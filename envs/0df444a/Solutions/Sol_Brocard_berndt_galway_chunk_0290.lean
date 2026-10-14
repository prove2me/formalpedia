-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:59:50.874791+00:00
-- url     : https://prove2.me/submissions/7e5be30d-7d05-4b12-b8c6-18ddd8491f41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51978421 ≤ n < 52158277 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51979671 1250 51978421 51978427
    0x70e040b0406030b1014060a120207050106030309050109090908031b040314030d05151008180610090c05030709031b031a040501060501021b0906010306030c061d09090c010804110402 80
    0x101384081c0014042e41c0c100c0302081000400030f4580002129011074044c0180f40034070742440a41c00f2190644800c200c000c405500b0450100010b0091080f030303000354400c0e2580c01c2c6a03842d04001401401c003540c0012034030390402c3c1d0080b001a50030720440c1d520144c03038494000d00c0360a051041d4001d00a80d0401011512a2203040b4003024002029048034160010b00b4882c51b92401e074170307404801660690a4104601c5500782001c3d50056001582c000c11044407020711601d82019507242440c143c8a02800e030182540070302c00482c07140034074003070f81c802030411501c0e60500080050100c0454400507101001c1c7c81409096484000080c0000f1a0800c408404125411080840c61002610100c4040d8602200010154004074908052102881d001020780c2c41c00c40500c8413446008040d04e040654858000c07001074400d0080d90040d14695503a010250450240d90a1000b88000746a12a80071081005181000000c14110315a428a00b8072155119071401a5041014a0120354001d0000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51980921 1250 51979671 51979673
    0x2060f15030d0e090105010c0209040f030315181103060307032402040e090f060106020d0309020f060a02031b060408030106030c0e130b0301060905011d07020f1b0108070e09070e040b040603 83
    0x4070603c08807500084400c0306241e40d079080107403240000c10100075000b5440200060106440414504015002c0d0070042038000340c0031030003100100c0642140c0010b4010452803100c9003068450590030080307055040385141000e0f00020380d5820b0511000f4039071040c50800a082c883c07008005211a510018190f407a1616003007080e401540464041240740315035042914a11400a4150b04a80382d90700030f030903000c5017144100c024214030300080c0d2300300300b1184120016454003401450400b00395400356840d24080280e00484200f85240c50020b98002c8040c840800c1007101141c0c119043d5040014120200c0d030416036154410361403039580200e000c95100fa501c0c0c02d5801109071400d084008108135a00c0f00792800486100303009541c0202c18080d401210101c0c3c00034002d0b006009801100d090700d030072640082c5403a42d1254214107101c51446908051358200d04082e400c5180380c184190103803522004a00d542100505220400c0084031103c0d01903203941e4002903000202a105000c0740342c0f2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51982171 1250 51980921 51980927
    0xf0605010f03110405010308091005040b070b01180b0105190c0614100803120601110f010c0c060c030c0e040c0e03060a0e12030c0d0b0103142a0a02060f15030d 70
    0x60b100941d04400882401d5010b80760070f22485040e81d5211081504200f03405051106000150090b482445001c01c004503034002c110014021181c8265515001d03981000c00341581003003100c0d5084401401d105c01d03903003960b07002015210071942c240c602c001684442c0c1e0044505007a640b2000d40610318051030300041c0000025210710038000c0b80449146503a41d0140f06650f4807a007076250703a596185030080341d050342c491400108940c1e1080200c032049c00c4200c000500b11454041e42101042081c24410200b0aa502030f004100800e810200300c0c50709030320406808691741c8078049115603503030110542518081d01581c00b09040c0a0202ca01310300d0114500070007441074400003003071341c0305101c41140b1882511044920402c920100c13a400c2050840300c00c070141c42c40d180c0070f40c1419210440007004c1243d41210078032a07070f5500798900301c40c100b40003040700c8003090100c1c03105120b0041000440b500d8000445039081300070302800d201e460b5234500e840c02069012078a0a5414040e110301c40c01501d81c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51983421 1250 51982171 51982199
    0x1b0309030b090712020d0c030b0a1a0a0b03040201030e030c10091103060403050a03020d06050603042009060a05190506030702030a02060f04020907050a090b0409020d0f0e0c06070f060501 82
    0x1200320307001003581e00d8614200d66184024403d8512080060035654010b05000d5000340c0003510613102803c416849655a1b04c4c460310403180440115501c506204d09400d00550b4482030074401e17541d00c81414181302c2c4108552000420107410b140c1c03103501c00e000c102c0c8200104c032210764003003003512000100383d071408000d840008004e80f52082014031400d8141780100702c05000c0c55254803000d00d0020001000e401035040f4030790510029588940010b903a0303d0346002580300d00d00c0354070584034245809421a0301c01d11811105030180303004030100007498403072500140660b60100c4000d0100c2e50400c8030001c200704583c0145030000c40100034000f007a500000507107040380c05a029141180e480c0c94102680301802ca501030741c02251000403d01d028044d50003440700555030f182203000f00340c4901082c12039502951007a24825400038110081c91240d106840b80040c0000d014842022162203040c0d4030901e00c0d2103580319140001e154000c00c0080091981a03d60040003030201c0d40e55141c1d08011a2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51984671 1250 51983421 51983423
    0x4150e0f040c03091536050a0309030213051b09040b0604030b06150a0f08150a030b0703060b0c0a02040b030a1a040309050301090b0a0513140f070f15050306011b030903 74
    0x208450701d4040d0740d003441e401b40b00e9518001a00c0c2812a009001540e4595400300501c5d4016540550026011a0041c4031903d643c074083e4841e20411031841c414030040503060155201010724000c1807120b2a4190f462000455101d032900988600d600c100003801082c141030120b900c084002000401c00c044500c0061203070030100d61a4006141000030520306100383c980000000d1800300000260768014411650052201510221003880780004140c82c1d0f25660810740300300704120104030005905000b84070140541d200194205040b1010807a40d40c03480440080c402d030380740e40021034903880030012801015085045491855019008800c5032842614207400040001e0170100e040d0805000f0120426803020f000061a030fa54501c0308000c00d00034018000ca06400c41ca21030210341c200a43d4204140020040c040070900103541030f291400e40d5002e0a40c442030302d44204202e41411001c0180f2a0f00d6081c203555035680c01004940c0003c80c44100310383c4e103807580c2c5424103041e40403c0440503a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51985921 1250 51984671 51984683
    0x903120216080a02180907050603040f0b07030e010e070b0301090f0b0303130602010b15070b04020a0909060204230a060302162109050108090703171902060907060504150e0f040c0309 80
    0x1c0540c0703c00d0511045c10450340e00c0440ea018101c100070504242c8015580309000d042c60a02c015070035603800d0003070101915403500190b00c03030342c03072002e010401e210b41c0181c40e90400c010821541380500100c41404148210310186982d024551502032098000144824004054030364810340355111b021309070303020301400340158600310050b01e032400e1240346102ca00c02454951820301130259100740341000010000c9802003a000f90000b1500c00b04d005103400244103020140e107483c00c00328101e030f081100428807800884070364400441900d03281c044200b6a8078504d03016a031014a411003442c0c01d0781c42e40f001402e03020000f80030b0b200c0c0a22443d010903120030755502d00300a2781d60354004642c03404040c0e4004803a9080320500300000740c4034031902900c6402410781d09082c6007034807466540307000c991690900940c20840800c24180f0041c8402c4010b803181d41402800e16081250b82d06d24000d481052100303010305d031020400103560701203e00c2e8031140010070a001030001014010302410422a0440b90 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51987171 1250 51985921 51985939
    0x2102090a150906020102030708041101271d070c02010c05070b0a050c0105060f030c0103020a14040e1608041109040f0c03030201020c0c0402040e04030c0804080607050405090c0a0903120216080a02 86
    0x90588103001f100c4c058070301c554410306251202c0d150081c04140d40400981809602c2c00200c8602124940a20020b4109403220078483d20749200410501e24032000e148480b54a6404c02810642140d40141c905030213181102c00310401e480c0c141e10b041001c1e00311844c0d00001044404030558008000d28501c0d0403d0020b000d03d03294181030040c1e440c103648240360701da00012648035071035211b42e01a00c00200d207450142e8800c4a01e5141584651140d0000100402d0800030070500410294000010b0000e07440e00e6403562601f5290403000241072024613109517804030200c0c1c180000c203559100c1882d042011100c81e01c2c1c3d80d207800790007540889400003407070043c00703205561481c0c180b0955007288c403500004400c0313584946d000c4600003035419003121860350910000c01c00d0581004102e20801044d00c541e0b6a682c100020040707101401081d03a10310700b104112181a080d4024808412260b2001485100841515059060500b05000c000d402d2480b02400206042c000545400d980d00903982048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51988421 1250 51987171 51987179
    0x20f030118080d0204050901120b010e070801030f03030608060a0f0501060f140306060c120d051308190e0d0501090c060903031b0302010b0d11120705012102090a1509 73
    0x109032105101c04a400c074540c81080400300d0a00c0e40104903815a0100c014502504c41d000926165030a070014881d05907041075081c00c00c074160080501400c5095000110f82c580003900400366041404024042091307001821304150203504004003800c5401e0070782e10f65142125405004203c0304400e03500302404e241c0001609030050300681c00d541040d9030790886442903891240b09646c0050b12068001004015441c203140042c401d2644008802d40841d54602d45004c00100f5618007504241ea02e14024000c0c400103088101159400c0184190382c0c41d05094102061740c2c100a0b070007003241c0186640c2000310800c9010341c000c8032018819890800b65a4940a0403146051103010080210b41805c01d044c04a030029088040c80c02e12910020800804400c00314642082c8604103d403844080f401c0c0d8001171800014054040e0fa0041c0100041071401c00000e080c0211444901c642418950031800004030a070115140424003602150240381c2d510f800e140d00100c080c503154000703210440085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51989671 1250 51988421 51988423
    0x110c0607050405010215040507080304080a051006140405040c030b09030c150606030615041203090e060f060904110c0a0c051503060f0f0102030c1501060306090504260706090b04020f03 81
    0x14160f510603802800f0b0318403003615041012401901c00d517454407904000151140c8204000c10103010302501400c284800c82c80c1052401310754a001d03c1c0e000d41070201c140002036800c1004800c2800032200400d068555041c480d124141a40000c2c0c112a0b501c0300b000f511180c0003005150f440d840200701c0b500307100c886149038800c94082d00d24a034040800c0011482d24a0100403000e01c0c540d070318007402d1030700340d40d40000140c2d80400e403030480c0410880309d41002806103c0b00c0c0365900031801d07101c101d0500c02d80b800241c80c5200d045000341c41703035541e001924220500f40058815103403108007211045105420280d442c00400d02c41d1600c668503502401000b0b482031401d480c01004042c0c941c0b03074803010810811015201c0002c995045100070310a00b10020002c0007101103841d074030440c000c82d80d4141000141524a81c0e0001d0641d203040409000000e030309107068046803c1181410000c1d464400341c1080a03100d00440034040c01d0034880040203210500d54103a008902c2280c004204162400c285 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51990921 1250 51989671 51989677
    0xe1608251d030613080a051902010c030612050a0303021b0709020304111804060f0b040c0f02120708120702010603080a021605100509042a0c200d1103010f110c060705 73
    0xc0050701075450b45050004645c20040e002103070b80340c101795060480c11a1407a80356840680c0ca800180c0d101c110404803030380c01d44503020147c0742030458204500000d441e483e503240c04415000b0704040c1e00103810002500c401001508640241040e40c501716911065100a50002e4500340e8420b21084282503803480c00c20101081018111404641903a4079120b410041c60004200310043e0b48074900390703100b6601d61084072001c60050b1105100d249408c4002450158083c035204d0342d0140402422010941d4841075850400f03040d072140c03080d555025402c81c090300590740010302800c00442d6119400e03070041420340c43d82c0026855042003d42e604100100c403a5040000c1010560801440c4130604154010400c1d4a83c17411a140907000400c8251045802d80c00e141d00010340700403051010000b03511f0403140400540d0070440b52140409000030312820100e040107140c2504d03200b9044c40d45e00c081d00486603032071610704104001d6025200e044100c4e4071000c0c000c0140d000b400d0015003114001c8003a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51992171 1250 51990921 51990931
    0x501140307060e06090916030c0e060412080702030f1e03040501050307030518060a0e060901090c0e10090501230111100209030309090403030b03070e1608251d0306 72
    0x524515150030b40503202d52201c2200306801c0501080741404580356014000e020304805001c14024400c00312000f800c986c1030302d4407401040081c40b071501b5190b51304e40030780701501d003000803041001000d890f0803000c0d4412002d00a405010b03091101485280c0482c24500d816000308400d02d0310b10402002940740d03c00e501030140424002c0c004241c0e1188a584056480400c4001d1070a4480c0149040b17860701d0740c102c60031443c0507141c42042900c407a040c000f0b190401440e00081c0000d110070f80d40d103214181103000703c013034581340000012410310943d0342c00802044200e804008958441c07100b00303050405446a6262060302c405226442d510500c074215800030300b6000780072b10130750303010203c4084e40c070803075000790705102c01d100020360350340c40180301409503101c1d8a000654141410034142803c61640c840782103240301c2c5c03080005074009030094801344156851700c1c0c00a590b50080c05550172080554103603104c1c1004c0440a41150408507084031090b075620400344256081c1c041643c2c860003155 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51993421 1250 51992171 51992173
    0xc150301061403130f050106060215090604020108040519120e06070506060906010903200114070b0105060d0603050607080901051008100c0516110406050402030f060d0201021c03020301080105011403 87
    0x64181800c030751018541110000d50b02c0b030a19131040d150300d0951907111000381c526035035840d81001002d40420000a0004241044510758901000c9054031590000d00103818040b42100040070098184114a0350f40810750190180c4030032824051005c9013070000000c0400c80720002c1e400a03150070000d40e103c0d00d074000001c082e690340c1c56041c05a075100c090001d078144001c0400100c0011048500c0c048000c0600f546414075440c020001000381221358001501010b041004501149c00403010b03a040d07640a4595554910249118130014102c580c0f000e0854003072103003403190042d0700064160003046c0030002400151180c0100801c01405446000c411f44e2010010b078400a03038a4011151803030042c1005820240b0300d100c0001f0500002000b260001d609a60700032a6144c903224800c083c100948045046107000c003607945e1130201c0948290302c105840d2060400316803080040c0301c11601074406480c00e01103a28000740103900207010b441101c0d4205400424007000c0130300700e0b000c0400014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51994671 1250 51993421 51993437
    0x1b03040f02040b01020c0a0801020d0501090b011209031b0f02010f03060f0302011b0b070203030a1802060714010b0604090b040e010b030a080c01060f03030903120c08041509030203010e0c15030106 86
    0x1500b000010401c0d01e0440d030641c0209031250300a5507840c1c213080300a03c2100000f41c1d44a0381e4400e01e004a58050300003231451803401d0340201031030740e20410516441c90a6000014100f0542c1425240100141910040e00c04a01040b00822010340c2d0b00703c0009100b0380f60950403200052080d0b05545490040c8000d0b441139400030405076120711001000304500703000501409110307480f90360308080300303c030b90341c001d40c2c800000d20001d07a2851084a040c005241495a01c102680c2e00096151244583c05460b0720700c05c0401c0f10210000b94002c1c440c0a5005081640d10384d40d030038200c2d01074003003c04511311481c078240c6002c600c01018000d01d203a80c00c0040203007221007030656483e96590811101d10b401903503100400704406500800c2400954081e072036810000d40345107014614400f0980210040080c421710590019002800f504c0580381c1c0301200031407036141000126070401142e071019605600300020490000c0000c100081d0010080e04c071000202400c07103a07806188420301c2481d0000b0815 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51995921 1250 51994671 51994673
    0xb0a020702040e01020c0d0206180309010809010b030609061503010603080403080a0507050601030503040f1d01060e030a0b130c06020604120c020d05030d060e06010c0c0b0d060f030b1b03040f 84
    0x6640280202480240009440d031105400142260005c0507041401d40c4149007640890382c04005884d400750300c0f8130801e8958400044066200d010301e10b02c0905100c1000c0206540d100207402484071b110010f0215841850b2200c9540c2e6144001d6440c883c0c0d10912040d20621403c041c0100c0041d01e41016180b807925245a8036000c041d804080150308000341480503400003507003400900c8c02540110001c50702d8508064441c4a221000ea01800c0c0c4080706800000751016004020390465900741000c86c02c1001c03030f5000c44c0c1440740400c0001c0c2604900b1003000f452441c05010089000d00450040f00f119031545070582e502c1a080d02c02428054076489075103211072090700903410107480035010540a010755614140b45030403010f03807144110f486040612a41d1100109283d2059003444c04c4e4400d0f00c019106c119807403e444c000d001084400145020100341250007000082884e0b298603441c00e656818843d00c0c1240958600320b5031750707181043c0a40003c0d0482524002c94000100040100316 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51997171 1250 51995921 51995941
    0x30212030703060e13020f010302090120030d020d050901060806010503060f0a090602030403080601180b160c0807120309080a11060c011b020c030c06070302030724150603050a090b 79
    0xc007034800b0107407500c0000c5202c510001d5480c0c003495400c02c0c1c00124007214810407c800b000c1c0d480c01ca0406d88180481403181e030f0701914488038401c20141040b01d95100060b62402c44c4158800e0403030090000a10f4504010f0300d074012032250140000801200d51074044864540000b0311a06a2540c040c2010070030460006040c03d4110303d0480c1c002800c1551665030005a03081120103030007003031201c03080240d1960403546030440c04410b006041100f0b810002d44081b40d01803056900b4220001b08590010000c101c04860094004801168180d607a5807000c100319101050b411400203080300000140720b00005416100160f02200140d10490740f881405016080058448090b649800220701100c130482000c070030b15003042d030260030410811018103182c11700c8010340e1800385400300807900c0429404400d40340f40d40c2c0d0160303001141c82c54050303c1c3d0302d132040240003200f0324a10702111400540032030901e03e4100c0b0520f89051110307a5880a03908100d17010610054120644540050b040a80c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51998421 1250 51997171 51997177
    0x13051c020c1504051309020405060a0e0c0c0a0606080f07090612022806080603010e0a1502030601180e01060e0607020112021c0905030a0e031212180a0b150d030212 72
    0x70002c1c4503003065660b00010704803103041d01d9070300512603a4002c40c0f429403e09010341603210340305552001c400362502c1c03100746401d04001c4c40101a88000302d84441c41c0202805800c001c1504550300380a1f00d500e910700d10ba00d42c0020030620f00c0b80d115a100016000d949805560115070143d4034021034689650244418481c10704014100c1001c94505c00305005488150500903141550710122280740c49000d15007150203500c2c149045074081c09807480080c0a41c0340428a080407190f0150b200c0d211000182c174403415104c1d41e01d2041c001d184020419042c3c404000341250201d41d21444c1d61544ca20038010640b054600290014191a1450904400c07903002004045540355002020780c2d003211039102192071244040354039810004a803402c0355841074400303503a04821000780c1412104450070b0b214034401c0f004042d0a8428000024203000c00b0070180d026001402401d83c0c3c5012101d03d85410740d00000ca620140e0405210006031560030248410100c0356451380051140044d90029510260 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51999671 1250 51998421 51998449
    0x1608070c080c010e010504030908120403060e21070c060906120e03190302070501050108010b0901090903030209120313410a32060d0507030902030613051c020c 70
    0x1020800c00008034404d20601a061002400000740d9040c2850000c1000d8a140c2c00417000358040071014116241c11000c0b5400c03240c1c004400640c81016003403050a100310012a0795112001200001c0a40d5410b001819514400e6454150b240d445410070303503008196000f000e0008176081585041c0072001d41c4003951300404101100c0c01d002c50142e0703040750301d802c0800c1e010000c7d401080c2d090130000d00740505400750103850002d0011082031800f150170300d481480f41000d07241d298491842032501950440d0100c0c4805420324015503141c0389210782d00d0f403210152003840c0c80038050000711041c0d00000300004514010b00c2c4000b0743e00e140b1051142e000c076180c0065a000d4042d50760400780e44d900c402400100101d0030307100c03081818411f00c46102d0070400c200450000d40d03003038a00c3c103e5030f9210072542d1018560800107041e0701d411200728014080c5a10094140c495a4148a8170243c544640c1442e1481402100c2c1d80703103403607140700403d6507662921401582c84442415203610b00021520300b18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52000921 1250 51999671 51999683
    0x15030e16050f01120c0e0a080606011e03060503030304111008040b0a02070201090f03030f08010911070f03030b0d140106140a1a0d090602040501121a10110604110301051608070c 78
    0x2040c490301842080b641922402008203d1b800301c1004d642c20003c0c03181e8010300c025400b80a942c50210006042c0c0a0310702c6200054034940754070804c40301d0281d4400009420041c1c1142d4591034685807600c0c01f4128840c3c80c0b0321a5843c40c01d141c4080d40b1a2415510460303000e988406035032500c0701d544029400043c0101d060105407200031030305141041c3ca450056000e540d13442000040304030302800760b95060700000d00c01428420ba1087c86e0424408442400d80c0c085002100c005c55824103d00600c204100e507a07000d112104610b090100c400c182d5140945418003c00c0b11175034440450400c61001d0110075040101044100720007490300010714400450103a010b450803208005441c12641d640b8012a5040c0e0b02050500440d40c7c03001900404410b181c07010080014065801e2858481c1800560310a031000280d84c0f1b2070701e00c01d01540d4505454002282e6050500c0d107083c480400030250300c54020b620b040c0010740e420352403510300d42c01d03007a05441d41501c68039503280407640c20b40018015115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52002171 1250 52000921 52000937
    0xf061e09031002070b0a0501051c02150408062401050a0801031401090b0403080a0b06030c0d0b0301020f0c0307050c0415210209040308070e0108090d0c0611030115030e16050f01 78
    0x1008a03600041210702c1c0725038405802460442d906c941124010b80005014140c64192240b0010701d124244445a4046591482000e080403040c0380c00d205a4226100602030002400b0002510a0100c41049140d62040305660310407801150140280011070000842550040011175140c06202c43c18541400010a03042d140e512010201720301500c0440c00180080c0403c43ca107800c91284d41e068a80c12902c903851800c1c0411607a40c54040c583e007000d0469590314030340c44555070035412a0849806da10030240c44001d1b0b10340da0340d01c0e6001100c040d1418000c54008049500c1c06100f504008581038a6403071205040030340b400c03d140140500740040440f01c50300740015079a00003401c1d124601c2503540d2451454101001485954002c0e0348a050040104c00c0c0a048400410400f5228000c0d103031810007160203041c14005442d09441a00f205100040003160140c030718607550285007076580b070038442c2c0143c000e5550f68900b0a031040051105800300c0502c59450324600180d04403005140a001d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52003421 1250 52002171 52002193
    0x14061e0403080a0507050c030c012c130903090902041203260a06090e0a02060a0f021905030c0607050903030a03110c01060602030901030e0f06040b06030307080c07050f061e0903 78
    0x84030742c803903048880440e80c0417411804001d01042200710007c01074015084c00c8403241c0001c2c00c5040800c500d914030700e80c0540c1705c41d058040d80140c0c1101c218001d10703182000305040c420b0300080a4800c0301f075001a20707101c4081045e401500840303040b20350310410130803401400c2d00d007180c0340d5079801a044101000030003102242c03119900b00d94041d0300c00c9040015145e18011404040b90b00886040c102c94108089002c00b5a03207040c1554102100b074245645045040b0388200e00300b019210240c40e1002003046014203004000000d0008045030310b084401c507880b01401920b143c09080b24417580f6900811080c00324600caa0080c81c1c0c0e414802e04c5190420051080180c01c0d601d09400c0200168404201440303c0c1d0fa0500072145280100c3c0d0162200e46020b01e0303815228400107002038640051580440e040392410811211042d800c1482d0303584840401c1d003420b0b00c0d2801403003030601c034980c0f220f405106440c0100495120065590600c06030501c0c2d08001501d81e044215850f07490300520181407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52004671 1250 52003421 52003433
    0x91504020715022101092901020a140609070f0803180619021005010909020906060306120f0d17090309091906120c0f08030f03060f04060b0a030614061e0403 69
    0x2492103078000c0d03841084a00500309400030130305920200c409402c00f4060f895821007034034011203604a440c05824112000030050f0b05c1c000010390000c0c20607407114000600604041609030142112005445890f9a1808072684030b03684d0b80200c240d0b5800806c8440c24600c0c0080d12115043d0f0040d00c124140540e6841e02088100f0800d00940946c000641c001a4641c0720702c200c40c00342030320301404c001d0102e4075008a24000c1c4004d1600d80512400004100c1960340c00011501c0c1084000494a00c21142c5603401d0701c0c0c1d0880c0540c0c00201d41003943c000b83d190001c4064621542d0560000c0d8100b2990508000007250040c14001e10114100890410034045026a034060242c1980101d40004245816013548004e0350200c44080707200007044c0300d8000048111081d40d8080c070500c0c4d48948a00300010325402c0d0700781c4880d03409482c001d400182004800003801080b8855101013208680c0d0b040e45408a00e808441c441d070007542000b03010512041c421600c98040d51044032207080ca030b1280d8a035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52005921 1250 52004671 52004677
    0x50f03150a08010507120203071d0301090209100e060d0f060504030e030102030c09120c0a05011d090403080a050f0f06190f0f030c08070b1b0c13020c0c09150402071502 74
    0x90281e40d443c0e901704100c694210320071504036400440704526602d0810401040e203080124070662541c0350403280e18040c3d0b401d4111200c003a4009001e07048505040e8991800962036205811280003840c0014015107400340741c2e01e85158008402100107041561a130006000040c411801d204094a10f54a02d0b282403000d58800c1484203002c3d80e07a00002c804000116445412450143d0301102d41521a921034944000031140203017040c0352b40c00d940c058840345c2e40342508811034020625200300300c240350307014103481d0040780304440030001c030344960301142054901140d000415031603900114400382403240f1800b002035040070740000000e03184d202c007072810401507001300340307503220a0303801d10600c800710030300b500200740240040c04007500d051b240962502919a521400881448641c00c181c1c900341301c43c0900f1304004040402d106c051450040c002c0d003254003010190b1265601102c40b60405001c50740c001c0b45644e032400d44510070401000081d600900003111105401c6000c00d04004a41c009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52007171 1250 52005921 52005929
    0x1b1603090512030301260f01020c06070305010e1501200609010b10111009020d080a0801321003140f01090c050f030601110111040308190f050f03150a 66
    0x1868450614181c104140d644816541d89603c0e001000100444001904001601080919206668104544114141501d410000749070b0750001810f00220303036000c180d90307109041c540c90410541e41c840e00d40860050040b01c544410300b01030303c800c2e182580101d10f09a00014941c101b0700801c0300d1307a00314030705114040d01c010a241c0e440d541032005c645400141c10001c15500c0ca00403a81041c0c029201e5a00c03551001001c43d641c1d92045002c040d5151100b811100c2a00400c18030341c0d07415001030007820704000340700c1c0c0801e10380840c01c10500e044c2c0c240120b40400344841240c003844400501000130f2990001d000c003040c9a60f50603043c5903842000c411600c00c03901e00d40c3c4810306600d409200c1d019034048001c4030342005402c001440080032108240c0360051800e03c2d02c080c00000381480180180002090680312450105000080141d003d00030107050071200b40c00242d01aa0304016a00800042c0400c00410014009001c1030080203001e10742c09800d560761240b220300303100d0100301681c1c00303500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52008421 1250 52007171 52007177
    0x3070f0b07020909060603030d150e0c1207050f0906030a02040807030803160906091e0905010b04180204030c051c020d080a0318030905060703020c030d050a1107030201081b1603 78
    0x181000c00d616140601641c001c44c00800f8045502c0c00d0b070000790700c0b44110a51604160b81d1b03042c13418003191414051001030040698004001c0c00c000010303440b582c1114128045902041c00041d41040c4502e00740e907a030400405806050076107032001c003c3c83c3c0c0c10040410038007950074400042d0090040150000450207100d0440d664208103114500080c0f2000406052240782a020080190b21100315411506205030f1000c04910160f012411101c840e0f2181c20600d00744000402d1500204008008a5080300c40011040e02264088000d0340180c0c44040d16030051008204000c0c10441c80110003072540b03004024612500303900081c2e200140130800c1e103804401140e56081c543e05482000f090107003400007005a40e2440e90300906406403070144500490012812400b014004c105203158250002e0941d0414101c028008100740c101c0d500001c00540709400c21001400081940f80030340343c06a5500b039255942076020300f980c20301c0010321005030b1810022031619840da80414141944269 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52009671 1250 52008421 52008427
    0x1e02030d0318080f120c0c0d05090d05060a050108070501080c03060d0309030501050403080105150705120c0115030803040b0705040e010504020f09040903030b030105010518060f0f031e01050a0c020a060b03070f0b 93
    0x200e000031a8900060000b070b45006d017000a4241a540010014200c0e02185070840e650f41c0c490020400311251410010060b1043c1130a0000b028507640145040e80c40306001c841009695000465444200b61080503035035108101003855030900030401c1d903681d8001e040152500d0758030358074582110302c200d405038001204840140300a01c0e14a6640fa005521248100d08001c902e8541d0b58442030801c0c0c1c00b820341180005c2542c1001c000303420840c0b5940b80100444030b42582c904084404c1e60003202c04032a0f01000100103860180280300343c2d015a100c00f603e03130245a080c10f044c030000b540560704001d40040c05111001c4517595038040e15040e603100b030398040340926440d410f050940c0d1041e00071910500700c030303207181e02d00182100c48103601880450f28950007075144d80c0400c01542e0703003200031030b01350180d241c914250310204403422400c196600000c021940c0e9400800d4100d50b41450b00d84c005030440d08a00001c900c0d96080204100c030014256101d45a0700d030300d1002580b0309a408031042d20004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52010921 1250 52009671 52009687
    0x2502030a080606120a0c18030602030105040b010801030c0e070203040b0c100b0420070f020604080313060c080702120c03010f0e06010f050f0907050403060203040b041e02030d0318080f 81
    0x820000e642010003030b1035190800799101401016440d008100641c0c00d0346e0790004212161107195030500805d131203c3c00440072a00c0e804c08002960003401958010350601c60880000c1d4465800c0c28101d84c0c10500c2503407028106007080201480103400c0c0c01c11440213000121b4100c03107280061103084a4400140072482c04d9071301f0301040c0c0341148a6030380728030b28150300700031600070ba5891000c501070100c4c035107039a82c8410b1418403100302d805400607400210200b00811207490001c0105002948481d070000c4c41ca5561038101c44c4100031880c0100b52100c144007400c018181205080010b501c031105a03080d42d03022101183c21140e02026a86002da15030104a03400c24052000350b0240003d04204007840d4106001f0504c040301804101c5c2c01906c0c41e00002d4101841841910b01842e4054401d43d41d07810582441001c02100359820b4800304e5501595030013880d0852000c20361940d01901510717030b00b0005d040640c020204000000c106e402c90100d0743d000180c03c0c800600390307800014200c0c0d8a81c00b40c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52012171 1250 52010921 52010927
    0xd081032061612020111030a111201080102030711120a0e0319050d09091a1203070501060902030f0112020d060203150a0306060806060d0302030d050c1b1c020d05040e2502030a 77
    0x103580741c83c00559140c400c4c140103084050f0100d0b6400720a800b808101104036900781011849140c90490103820050b00224282506400440c0155103d64403483c02c00001032210351210f000c1070030b8061041e0f0412414015600951100c6001840102030701c03490440607042051000740980b0466158002000405003582c121001402915110100f0810100306c1d2542004100524000c10311454039001d00050604040086a14841d804402072005590300c20449010750010b07114000d040b04007400100740a48807410210490350000e026804000090f1100ca00950010b4000c00604584807814420360f102c100c4144020b5103c0c82001a0311450301c034285003845809042c0c030707110300502d003650030119500200355040c404121200103001c1c0c46603407406c151442101d01c0080b0814110704600d24526000c141a40c500558000c001c2284000d0102241ca4003107115109001c82e0b400c0c481401603c8c4c110b05030560000300880451940d2940902d264210016000d0343c800682c00016001141c03a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52013421 1250 52012171 52012193
    0x2010c030c02010209090c0705011b0f090603020a050a0305040204020f0703111014160201021903150503160308032d0103060c08040f0b060d02060c0d0810320616 71
    0x18280b0085080101040020386460006040035040f44401f19060040c45020343c04100207100c1b0522804142038195006001401241121004180c40340000200b0034045e00884162684c96581d507231810044c1c4506030000d08016200f80d030420f0b03081c008100c2601644000f0050780e402510f82d007400b509515609490200c5100081201c02d041443c401546400c1d0002c40341c02410313242a800700c16a90300012802801285944010301c286005c400491503015404040c1040b01005421000c5071100c0a06507580642c5d4152003112500d040100041900035014507088200c124811f4854003500e800c02211101c01400c6d03110042d101001042084071074424801c0c0398805041a4506241540310201302c0e0002500150981c0030b0500001e40c0c40d035809003124002540285240d0f12400709066999484103c00c800c500803610981c045501da644242c000c40449101411a403460660280022501c043c0c49111840c040c1000105002c207580740c6003c0c084000500050f8030380901c69082000a1071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52014671 1250 52013421 52013441
    0xb040e030408060402060c161403010e0105010b09040c0e060403031107092703020114040813050915040c0c06020715050c07050c01030c020c09100609060207060203070209060a0305030a02010c03 85
    0xc0c0c020071040021100c04516580d026404481903501c455103c048207061900140e01c00c482219070342e9012541603884041e410490702d040d8000c202038541812043d088540030300071600040402c0c40400d40d68074060700a4400708440c0c0c039101c204000d00c880450840d4203d500201c011540c2c1c28060f0442180801218008082108040c844a504e04203000c00710401007170000004251317a02d000d4103150003504600c030b1894044080708840d1420b414010416007000c41582e00f611000c090000c0c031441e20f01801030103845c215101d0340c00c0054090800c03000b41044140e000034021080101d2010803000d01c080e000540c099008107010845044400e4112403004000d45d4070b0010074482c01c03020880014608104120a0a00040c6040d0ba03003420392401040c14292603000c60544104406844024503000442d204c5498a400d2241c540a00780c0e02c3e280c05000740c80050344103010038409860300100340c07500008046c0035160016242d888660075a4489010580541e4580d90080841c0f0386c10700c1954404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52015921 1250 52014671 52014673
    0x103120c21020f1603110607200a050a030804050d031704080702010314070503040b040c050607060603171912090602040b0702030705120a020103090503090910031a04110105030405010605060406030b040e 89
    0x420b0725410142d00c0340c14000a13005050b02d0b106c4100350b4031050100c50030141c000071410300401d40c20032800508105400090b01440c0d5200000610742081c04003801a45e03844517000d8141404c040074800003c0103503400b902086103c2c000511030a0300c0000140c00303140140003442d40c8200030b000140c240c510440742c03000640c250408003c10503521006580c0c000c1d600204000c00c41e03c0c2c5062440d900e01458001c0703a0300203000124a010080709911800469120380034400600300b11107941101400785c8608110310700b205030003609969210318030311848a0108500060415080d444030001c98001e500010a40003000408400358681040031074001c110849014014006020000e43c0300e0038030190090505883e07030b44090400c14280141d60106a018014140f1440c140b1688824511244800c4c1c8816406021040b50b1408003c241c5203d95000b00c0d81041d400403003030045030b9a80c001481035500d9580c50f0008205030f40c894004200419840d0740220701c50241d4010001258036590102d00c107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52017171 1250 52015921 52015933
    0x30c06010b031005010c170f0702042f0a031506030e1e10020702031f05040b010605090604060f020a0b040c05040f15050423090d0e03030c060103120c21020f 69
    0xf045680300480103a40e020301c0c01000d01600c0b807400180000c2483c03d40d0321030020101c0c6892040040b800a08441c0340201c80070b2041c0c000c1e45070410302c00b034070640105030784d9900000484002d10765100181611865454002203001210345140040121600307c1c4c4002034079500384446038107042042c408000c3e43c041c11a25000401c03041343d6518180c003174030b0740480d07034011a07030300190340d8140216165003081c16403028004000101070001032070100d4040752210340480c00880c01e0b41c407903000d0350301506018200d185458102070f82030351441024000d402c114400c02d8040c00001e041401264007561040c400815100e0500c4104015641080e0510100e203140130310003410210f03036202c05c404440c3c054600044818030800c0c140322801310f1955a4070020f60071700900c00d54003800500d0b000d031120b0720350b20312038070b842c001003019105d118240e4503c1103036000100510101d041e015580c0e00b10346207800c00c04580100381d629007506a20312001d071092000003840041415406100d903840c40381c035550280c09 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52018421 1250 52017171 52017181
    0x603051005013002040e0103050102040906080727060819060b030d09031e050d08010305121810020f24070503090d03050a06170303061906020706120605040e030c06010b03 75
    0x9914820103544282e90100c0d415040c0341010142d040324003a141c2c0711b1161545684a00703015020354814810f00350f1561030070b40000b80e403140201da440107841c140703c031a9544403a035820b141032000060340766400742030343d032000003e401c40204a803040d40f8094090208804100b410030504459920060710700a80040302c8400c1441d61112a40060341c0d480868090024035101001d0040302950800402c0c43c0b00f0500d040c0611500629203d0407284610308851030080c020204040900038185418551044a01070b0013080c60036156240654481e881100e618601c8086110f02d480041700d82180b4504400659a507070100380300d0096484003940c1001e500c8c5050080130380b55940510390382d4000b01070340c86000c13510124058204034014140c0341c4d103c4041c9921600000d44940c801e50303000c1d11030910200940711001380808a0703002c490642d00a45441c40c41c05100b42e90110310140f2a0358078aa58a10108080e0396034850504560204c1c0d0066071030740003100c1c1c581d240200c1a0442650a401071003004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52019671 1250 52018421 52018457
    0x90902090601020c22090203070303050d0f0b06070209060f130e070b070c060c050708060c0d0506010e01020706030b040b1207150905030604030522060f020c011806030506031501060305100501 84
    0x5a01d1610501200c0031103d00f95185c4c00402107080000e5060054038000000d0507804400350074001c2002e401000200340c480113480440b00c010950b0340d0001400c0c04044094642070090030303030180e0060680410503400000003090b4424240c00c1e42c1101d549c4121382000c5000411101000e80700380c0301442e24000c019140c650601110784110420818520518000c120b014001440104012002c403015410801113090454008904c9594607901d0480010103541c481d0301c031060007600c10f8014103144c0b81044021400b078500240056081612183d0480075511001c000015900101c1e0140140ca400e024030100039013a0b00e035510013040300f40d10003441355075404916281c2007581420080d60b01d08462524945000302d550003032480d060341800010700c40307801c2800e000c2c00041301d42c08e0724070100d5010010741c1c80e4504101584101d444041086c84410700a40c41560081e60040484030610110105000110000d8210701c0000351500241720b9408208681c2c08003030701e0242004034030944a44411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52020921 1250 52019671 52019689
    0x1081c021f0c1e020d030b10080a0b040902031203040b0c041805070e0d0f0201080c0a0504090b01140705010b0a0902030606090904140d0c020907030b01020d0309030201060e01090902090601020c 85
    0x5580095980d040c68000c1c540501c11041c04049551000f90041c0c0120354040d4541c6501c04138140403d003000c81d14156494030300c2a071080040191512419038868100050090684409154005949080388409a9030400c80d0900d07040701d08081942d03d12345071030400d40a0f030340a030500300c0c002001d010500c000d1540c00225aa8101c00044c0020940da900400b151a0a0798501c200d40088041100ca004d100840c100103117018000e0b2241034460700c17800712a030601c0c4600e824403000601d0501091000d030380075410094016a0515160941400c40c40449000303500404c401c8420b69503c455031042d07800c119900500a2440f10400c500310714200010500610807254101c2c40b4034110000501005075403035a00804903d80b5080b140382c1031040402400741101030344141d101340c41441c001031240d0722a00803030100308010703400340000d03900641c0300754080c1c2041c078022003d5540329000401d14400c110a890b008040c0642e010030401002e00501005010142146046400070090504542c551030b2030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52022171 1250 52020921 52020973
    0x5040f03081e0408090a0506130603050c0f0a090602010515100c02010c050316060b0d0c03020d060906020d1a010206061c1a070e090a140402060c0f0601081c02 70
    0x80c1142c1d510070400101d90491008400c800320600300344001d1200c414040c080506081c1c545010a50300c440804c07140740114031940e81548580c41051090768880e070003803a00607880c2c000181c00e040700c804250515070020041080022040c0104000c050340c240103198014095500d49a100894540428848040a00c0560601c05080221011a442641c10f10300740f1b82c001050320344032083d02c0c09401032035200c100107035441d0b402c00745d000c3c8680c0703483c415221242c2e600101c1e50880a155600344419640c401030b0581e08181d0b1352480c075010510900041020440d160340004103802d0038140390702c0304200c040f03010307045500000412080c1d86650280d0b826191102851b0344043d400d61801c48000304080c102003000005100034000c10030307000392210840040481c0c504807503030741d130400e840304a0b00003005024070180c000e070104000d4102200101000d0100e01d0944504a141e0380203145004801c3e80051010750203007824808181031504105038108181c4060519125008035414140e805665 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52023421 1250 52022171 52022177
    0x30201120b0303090301090602091009080a0f020d0c08070501092301031107050313050a0503031e070c1707030326043504080601050406030b0411012006040507050405040f03 76
    0x1207003a9541d010010380e80c0d0818024024041c03a00b05141820180d0424049070740200b1110034030100e500e02075020002a90140001041501d0311074030750f4503189500c040f059802624801107800440c46039107640001d000413000900c1520300d071400041c201802903011816400408103400c1850218954880e81c1e0380092802150310300c10002d10040314421000000e065200004561688040040341001102d030304032506c0050a59034801d150b200c3c82001d151207441584880c0e91103100d1754050250000d540910402c10b00c0585030700c1a0016051410140f074482c1d07001d245c0070402c0560142c8502002d0342803d400c882c0c80d1440381c40e00a007407800988020040c1c0d000f0041c03d034003010401c01650174140c00645c071b040c1c070601446904080394400d0091214a008100010a8500b4140a907a04584e4000c0b40054282d8581d110500a0444c224407941045400511010160598804880c41c00b49d40b002424441c102072a00710f2401b200ca5001a00030380c180001c005c04208040d840a500301d8040c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52024671 1250 52023421 52023431
    0x5060d0b0411031006090b0307030c031b0306052707080c150c01020f071101020c0d03120b0301020a11071d01030b0403020304050d0f03020d0c0b01050409050f10140f0103020112 78
    0x4903001020b02d08000402e078040c859001e20031503600503a00315100f1070b41003074010803032084c0b0b01c814035440321000d010141500807050000c0000841500c03482041814a84490b40141d40b40e0b640d07030707081d55016100c080410120b0002000c1400c800003201044500347c40060810394684401103482e82c400041c483c0c4110038429103102640c40441c201c0301e2001240000b10345d0f0b081e00d0010000560403503032058584101794048c0c03100d113500005611100341e074001c00051801d60300c1c4e64101d030b03001d030441d65041040351640d01880301d54078240064000480d046e118090812242e03180c09241a0060b4006813030f034260448210203220780d0012040c1981d4225601142569480c2002d034594441e541c00130b03400420003c5000107120100c1094440d0301c0c4a9425140c0c0b103103c4180417151011100805004c100c18100104524902540401025440342096444498425164500b07041c944a03d54003804c0d140c03003000043d0805202c42551007040c0011035041c550454000901060400c10103c02042d511 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52025921 1250 52024671 52024673
    0x10c0905030d0302210106090e09060103030e091e09060114150403060207051501080304090c0f02061611010203041b0611030904021308030307110d021b0907032003090c0405060d0b04 80
    0x8503403044030781c0c00805c61400841d6540c1e007005020200354481c14100101c017201007004c1d41400b26040e41202d8041d9100d1000070a8682009030f800700207400486600d10032010903d140b000c410001c4d114200d00d034060f00c0c5c40e6150015101000100481c1c00344a01203c514040c0c503694002c090f1001e60781c021000686400403890201d140201d62407441e410480c12000000c3c0b0040c0c000010001d40c0c441c80c1e41070000368014802620b840591000910141c3c1002c0001001e2103e4240440d0700c040d60307450709000317803440c1d0114182203a00c19030b0b007952103164601128034440c0b095605a4002c1c01c05160000c110b6290300d207580c2d124001e22140c00c0c460342d00000c580351106501002c98001d081d0755801d803907a90030450800b8007007035002c40401416000b20505a00c07030b940003194040384100040300700108140b0340d804120204000030080e030145950707007501400b501016010024400d44001c02c555503401d008500904e401c90007070005100d5824482042940d40b107050a2403c3c041e84145404c5860b112 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52027171 1250 52025921 52025947
    0x602012d0204080303041103120405010f210606080411010c2303070b010602010504030201050108121b100c052101060c02060702030a060e0726030418020702040c030e010c0905030d0302 81
    0x9107a00083c41c921020080c0014003c482075a44000c2d04200c04403852450404030f42e2840e40118032580c0d02150303030403602c00c1d004d42c00b4610417013075124151340c451410040c1e0790902044130b080e03800010001e5000010841040350054030030074518000d081c1002071181980d0344c4260003180740c0200e01084081c0c0c420540d86403081003036400d12070744140348991940e19040c0080c02481e04640c01d50042d824000005407116012030004e22174001350010a15082040030b6921101c0081c0040e00802d01c1020a0500080400c2c841d00368002d410382e0b0303041e0b07540102c0040420700302c051003102504001a83d00401040780c004220320300301607040d60b0b00b5032154042d0000905108031900d028190509268542110078000710741c240c10799802c0c40034206141422220302c40109800c0601244550003000240100f20b428099040b40401004025241c051150b010800741c85c803961800010a49460664210150138000d15062070703580d191010f4450303e410006030b642e60641d1410002d06170f00060441111b22 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52028421 1250 52027171 52027177
    0xa05032505010908030402010e04060503210c0601030804030b01090507050304060f020d150815060609090405120705010c12020717033106060b0a050304030e06040e16090602012d02 79
    0x90440700800c0001c41da814261001e6100b00c408034009010500040c1403850940304002c00e581c4050007c110101c80c19511100603070406400c440325050620000500e902e08001d020f001e90b110b01006030f1100e1451508080015068000c80c01041c103200070005c21650002c01d803980650030260115441c9203040e490f20003403140300ca042c5107440c10609039180400120034450110780310311040722155030880441072400801900d203e170380160100840c0d411072900c0303040b1750381080c0188240c0e144600b800b020b64003154450301040700c0c1c59444680160880b50800e07403141c600d0107203d60961a22407140e0380c081c44414001280001c44d0808004030300c0841c0e4050108203120f660203c003000789808094a004020360000341215481e00342070000c41d01103064002d4401f01c0d8060b440301030442e01c5586d0f0959034515074001080d04030009110025242c2103000400b03010380e03a100400500c110070ba50b001025081c45400070703001d5a0604d00c0e0700080b010020303010741403c0103880c18071001414800001c00648 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52029671 1250 52028421 52028423
    0x30417090a0e0a1a0a0e0a0e011d0604020307050a080303040b0a0b04020d090506070f0903120c170306030105010f0602070308131703120f0420010e040203010f03140a050325 76
    0x42c0000204003141c22198003803100520040702c19100481c4120800ca012691070060600d90208000070481c00d400903001980ba90403e44c00115911202017038410b6000c1d11540c0303c01700c40c0d101c0c805010a50a00340700c0900940025140f08035500e04200170251b8900c03000c1c000600f600540000122889103550000321035038001801903560340105c807140c070044e085c4250190749900440d00401e40090003588030150100c443e48480d01140d00c2c41d22426600820752000d0018020241030a00004205460504003d400319411a40f6030608000341421110140c0041750301c1101d40d20144100d54000400004590f0b02c0001c0d2580c1e00040050f2a2403200e0950202072500704003c0100300082c0007201500400c0c41d80c00d1080d206588603c141c152071241034401404515207200704031189100c4400d100b0b030000040c100301d04000c803450040f41c203c0c3d000f644400b102130501a800e00c10000b18480000101111000510303000d6031303039190641c45c2e100c0c0b9003541d8080320881500c800c01c041900e040c0300328a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52030921 1250 52029671 52029689
    0xb070e09070e0112050f0c0c0a02101e02120d02090f030f01230118020906070c08030a1202070b07230f03060906040c090b0310080a050c01020f03030417090a 69
    0x40c14940805800b50814030803160120f07a499401c0c1140054611400e07200c1c02449007242101d45400c1c141c640e032948042141035460250882030000350326009840403207041c2c15582c02c0c4100800c224048000050075286a003107410101c502c00c0e40034800c00c00e0b190486660000103a4504000c0f0008240081482e2059014001c40003c01170118040d0300140d078000103044c10080c20181c0070325001c07010300d0900650300c01400704400c20304619010b60240c1104034000e400540b80010645860036094459031010701e80398800102d04803c1544244800c031400c1d80e1501c250b0030701c1706599401c1100c0f00001c215000f00113905603010049010751581030082407035803810079034944180c641800141c1c401c544071030084041d1000315000c7d0070703d882102d41c0c1000c190f484020050806280d00700d6030744040d20741c6001456440c0b010510f00300510601c0c80300c912520040010112000001e03040c0540440175109581003401040003198442450200d10f0a00141c21503440c46000e000a124506d15000b04c030782 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52032171 1250 52030921 52030939
    0x60a0b13050406090504020f030a03020706050a0e0303132c0c030402040902060d02071b26030c070e040c090501150305070311030f0702071a0a0302090d0210090603060b04060c0b070e 80
    0x10200a66101c140543d00236503203195900e5065080c0360340c80310074080040c0180c0c00396070200030a921034030243c540700b48645003030941d14281c400080d00d107400991110104005441d41017180d00780e9501d0007030750160381d00c1c0c1c2c0800c1c85009440311240501c00404034604c00c0300003c0010110340c1c403070380003c000d03540c010240d503141d01102030290300a40085c2d000300c405600f118180200070b80803800d200d045a46840e0702d10351107540302e041d0f00e890107043e001d092501e22003840000c49010b0b040c05210060010215407a01a1a050a10317a0f6051034aa0101e03500901d04801400b214000c1e042c081105111400c01003410348842104400a0000041103020a0340c04000d20500e03854603a8907501a00c050390859184948454400c610440e070081c0c1407121200800040e41101c0c001e0700640400000101101800d2156401044982c081c140c019030020b49110000e00030940c16118010150000802140c200f60800c036010340310010921005d000c0344102070014401a200340030304504408003400d0080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52033421 1250 52032171 52032179
    0x20d0f02190305010b01020102120402011b080c03070620040e0705121312030c02031603020a0501060e010503060c04060207030204021c06030305040510020a05120a0903120f1106060a0b13050406 85
    0x5401c1895002c22140d650070100040c5513580705000303540a4441004550400da2596030054414081c41401c22902c00410750740c41c0c0202e80c0c40c9012340700c86003a0358003541c2e80312001d10717141c03084a400c0d00e030020004031085070429814800038140c03001d54440d854000320725241d000c0c0544140c001e0740720b60b1001403100401c011048a074001030350201e6214100c40f0803510024001501501c080c0038241005034018440261108440e84150740018001d0042d1145100c4d00c4d00c03110b09485641d040721001c030009500400040c10708000b51940b0901000400d420300c0e0030300c080251030318590f20010b8401e0380c0224401c0c582010000042d00040c2500604207c8681c1d28038014005410511038107209000001c01d01c00e140b40049400789002c1d52207400b070100c005051034070300c1282e04015489000c00c10307d0403010000800c150500491042e554032401c0c4500ca040b08020030645121510300650b420500502c520741e1034440d00c0005440a40303e00c0754550032500c0000381c0d8143d65510550f07005007805c0d030000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52034671 1250 52033421 52033459
    0x92a04031101081308090609090a06060806100f14160b040201080c041a03091e010509060c0703020d030c120213031104020301030f030c03050702040606170108120403020d0f02 77
    0x10080300e101d40d041459484039040151601c4404444206501c1120144980020300c00c01c02030980d104001d05e51810060b013030740403d1800400322402031a80703984980911a26400101803540420708440180a1030121000200300400c4102da01c014440d031036400560790a0244159a00c072010100145120070301400c141e081502d080e901a40450b4001d8007140f2401001404c880a8629008501582c13648006941089900091200c036260060150101c21011005150010366481d040003044500b0043c03d030030300304071001d0501c507040401080311500090b00840c0c5100003d500341030005810340c00300d81c250b80e4550b02d002c03a0410741c1d1000a0360b0010003410320000041d40e000c0c1c0d840c0300c180048841801b0032480f00780005031840c0d0b101d80565000034843c03000c0b0382c0910b00ca898824101000759002c00d081c1c1d2410b8102c1800b084d14030b09641c0c2d1b003100001740207004203006402840481e02414850341288100e000290058114030718000601001c40b0803507000e00d9014106654006900c6504 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52035921 1250 52034671 52034677
    0x31805100e010b0a0e0a0b0607120f02010c27151706060403170d0f05040807030e03070509061201060812040305120703091403010914030306040c030608060402092a 72
    0x309006490081810701000d41480b4940d00d01002828040c04070741403031010040d0352002085403006544803000041603440744009021060320603a2000d450303c10104018000e1983c91090408580c9040c01480246901111003411303000d40f0071282211070f1071a500031b0b108078150303000030a1070821700c0d8070325000c1c9521881c000c0346030000a002800a4590b001040390398800e030711000c0c14040d4001c001c9010226410010a05403010b004002800a1400e072040d041d270340210b8064941074004556181071540054425407489012405004542c0c101000a210050003510450050700440740c1030140903000d511100151551f082214140701d27031800070941681c0980021901401032449000c03100d174555042c5c640203540340c0c559600b49801c020090f10500f2500303003820350542d02e992100700480c081c2d09840301652008c07070185580f460500213110985d0f0103081e0641c10985861400c0200c4040072600f250000e50444207031200d42c9a4103292466001c03e03c0136006211050b184400e840d142d80c50007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52037171 1250 52035921 52035943
    0x5040b37020d09081e030c160302090f090604061a0409050105011401020d090e0606190905010e0a0509040b0601050919080114070f03090303020409020403030e150901050a05070201031805 82
    0xc0703030390345640500b046030302403402d10451801c1d902c081000003801d0780b0540541414241181100d0402c807040301000e26040c90701c218400c110403820014810740c28800c0b03400e40e0014848542e0346103428040b1100e03644100090019001d2980c7e4446521516146030316241045c00090003404503079090300b88140202020303c2000c4800c003000c2030799142940042041c280000c0d8540780e88222916020540070301004c000c040b180d010108003c07034501141460ba045540309003560314092403170704180000d0b01e100300c5421200d01c1024050780c100403035030390800125841a4005000c07c45511481c0c01a50035010341c50a859100440b8402e444100408507500070071562810001c0c00741e40e1107188400d030020000d0b100f103c002a0242c10f803114060107504411203081c407071b14005192a549140c000c049820503002100042d603400b000404070b14207143c3d032541c049a0494410b141524960010b0624403411008d5002d2000104000080da8029804100d00004e8540c000c244443c00d072529588030b07650460 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52038421 1250 52037171 52037173
    0x151e04050a1d0a0e0c0405040302010b10020111160807020616050c040504170c070803160611090607030c110a03060e010c08010f050d060b0411040501021c05040b3702 73
    0x110000b0702c40c8540b081e5420080b12051501d00e00c2d01c030b14400c0000340101c503000c040c491142208000c1365440d18070a541c4107034000c0d8000950b41c070740d500400c9a241d02401008046a0402c10350410a1803280101d80411101c18481c060180700c40c034003540180200b0501075030140d00803e102071042e201010711001140b092040d40c5240b408203041004403502030781c010b4440b01400602c5403901403560024005107480b0f10841d03c00740ea0b6000f5007880c41d4040e21242800302c42078007c24041084034002c0d01c040041440809003029080e20200d203440c010a5030160401c0541c904c64010310501d0191401c00481c007900c0b00c0d18460300c90401c1c0e0044c001c4c0001c0c01d040d540c0307004109402c6510401d9164180d421010310310072420718100400030b0720000c500e415036143c0e50b1211070007022b603500d1140318038541e094600181c0382d1386403a001a04017603840c031508141a2400c0040700d4a117500000b12015607408280c401d840750581d0680c003110090325801c0080380101c40c81c088400c00c01120b94002c5140c1564 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52039671 1250 52038421 52038439
    0x10807050705120a020109060e011a0301020414040c1106070f0e040b0f0103020d0e071d1006081612090c05090604060608040210020a0b010b03010f05010504050609151e0405 76
    0x18100315103a2103608000342c0700d500711200c0300300303101c10800040c0188801c51002248506142d11044103c54011801480303580d5141215481c483c240610161440411130086080c80d00c1d10041505018400303600f98400c51b6511607407003440f401148400d10b00c81c2e2050444144d4500351074041d149541081041010524048013554149030a00500c1c0b440300340034004c10111100413006501030b401c105d40250240761590120000c81c8020031401d00206502c0c03c03401c200904210140c8400724000d45000031020000d0340600000341c005d410583c1141400460614540ba1000102c03030b200c44403080728611504200303104050140086810040d45d8084031048542c0d103ca9040104807007480c03241c9004190404009000761403d2000f07415a90303102d0060328100c04040d59035002c1190709801684004c0e04c044018045004c0d0704e4a010702400c402c3c20900c1c41d281c1801d002030518040c5008080c469180383c1c07079800f443c083d103505642252209410385803100e40d840c6590942500240a0b9a000c0e0b0400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52040921 1250 52039671 52039681
    0x90f0118080d0c03020c0d0e04050a0603030818100606031a060a02250e1905060307030222060e01090605030f0a030507080f07051209031b06030c0a030b030102070606050108 76
    0x1485459031035940003422500d046500114140540f0380d01002d4801e056091100120300c83c000c1c4215203d01005590f910901070341c0500f08000c0780c6001e4141c42100e46000024070000b0741003010782c3e801c5030316820804403920450360224a400d4610444038a21781c100840011869016044488010402c2003010703080213440342032080314080d250090b801a44511140e81c000c001d900c1158405010f6802940c0e41c42c0c0c0c80701c50a00d5445001d40da08d524002d24504611841840d070710580340c0201044000d40b1413140f43d81c00058288900c0304100803410000031086800c1503082d4080002010100c1c42d0034819a03450b460900102124807e041c043e004035002c8100c1a800401e0072500c0d681c0c591660750418007962a406400c0d0403070b9107060b00c002d004010200c0800d60401c44020241c804c241460b65480c0014141030500001c44003800e11264a030312800b58543d1281e0942e40d010013201c400340c0c0c650f64080d80480c050000c0000c855010352000818030f05100700c5402403000c0d07a4081c0c8402900ea160 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52042171 1250 52040921 52040951
    0x302060f0709150210140609010801060b0f0a0302120907051005040b161b0323060702100e070b030103120f0503090c0907090504051503010b100206130305070b090f01 73
    0x42100c0c0d240000e03400c082c0030f014681e0300e4114052041c4582c41107610b2411110724201c201c1d24190515a0000c105c08200007580c544480c41c607015040500080c081d00303180004420b15400383d14050508501c0208201c031b001d510a43c145e4010511000300c000740e60030000c146a4442c005801810f010742000000301c417841e805181140c0c2190381c0b89680340e25000c08000e13039802601820700122a1b6001821140d1100b128070999200918055948280e44080482603000d500f018070001250300d8001c0030401c618140c0204010308161f2102d980884ca0750310030740c1d855042c020f07030b90007402002c80301000100c14807141240c140b00303030889516074104052003c0f4040e00e0a000440704821154002155441c1e1410800f4100350032100138102a50780546440002e000e942c801c40da02d00030b0705405111134000d45401d0003806004241541e10540060304044025200c60b0002c159158966204080c50704140c4a80116002117400c6250700c0d54601746844056168809444840200d6080034040b007420f0007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52043421 1250 52042171 52042201
    0x170a0504060f0b0915010201020c030c0105061003180327080c09072d03020d05010303050a090902090f060309030408120309010614060307030b04090606080709060909230309040f0603030206 83
    0x4010a4804250b80c4c0745e104100009005481e03c2c1195000c0c00500724620040010f0305c038a074258800820186012001e0200303401c400c03688001054201203001c50102070403c07501c4000c5400d450305004000700035800aa0b0888006000b002c4403042030f4000403980004110b03550040d100f11090000340d00c640c5000c480c075241c1c00703403103007480b118480c690b4002c0382600d036480c10802030310304000d4101200c0851a00860b04240c1c0243e004c80c1001402a810540c03015020f0042c08000304110300340100100410750620803295078a001d00c000001103509803104200340c400414102e421250424040d0740056410341050362444e20546c00c0c02d10202e8003045d0245a14244100074104034111340c1e03451800c0300501045503a454015603a6500c41c030100382103000303040c090030b000130080042c940340440e650119642a40520341c501c1c41c100d0700380c00040f03088a20b500b415400446441e0340702c0c402d800950540c40b034103402d2944649007005141070b030303101e5420000460380241c00b620f11650f10761140e046080c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52044671 1250 52043421 52043441
    0xb0604050108060907030e06190e060709060c0f050102070f17041505180907030623030c01080c040f0e0106030608010905071e0905151c030f050307170a0504060f 71
    0x102c0d148009503443c01c0141c02d071036000a10380f4010900040d03c0c65014104032003903403180c81d2980c000105040c03809503801050194100107004180310310300b9072401001c681c407034010001045010303204a4103021500c0c408415258000c8000c65480600c0c0c130b0a0114482d81c68022035444c100240e04880841101081e101214240c944442084058240c12104c2d0390000000000340c009007040c0d5a07030340d110810030b6446440140c034001a214181920f100c0450140c001e0031903206c2c1141e01c501c045450220b48030706628000e080001e40c4e0345801015921500840d00b05105484144034001000c1501d912064100c42241c1c40401185881d001070b6400c3c2e840c0c841d00602103601c01e120821601c0e451030154607001c5103a849000076251100185400d961094517400c1302c0f011003240e0062145030125a4683c03400300440f511078407102a0fa00030b41140c40340c10010091003004400120b107940200016245900300381201038081c64004aa10001e00d826581a11410701d413002c100d106200d035201d0b410090b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52045921 1250 52044671 52044677
    0x90608030406050d18080a0201090302100603050703020d050712060603170906031303020717010204050301060501090e01090f0902060705060411060f04030602090319120206090106031e0c050a0b09040b06040501 92
    0x9044440c0301d40185c010501101c1d4248280d1101030040b17210000540310000e01036001042174840c0c1c0c20004c1c03510303c5100b848041545024010400034100207145030850741e0581c2c04208500d9981401c5c0c3c1020740f00d50000380084a0f09030b4400c00c104090340440c041c1c9218428507200c202412140b200300e802580e0f0042d41210040012918080955101e000e01600c0b030700c1150100c40d01c0b80401400c0b186003003041500d503034000c142489549428007a45c00601020300c1c25018251401d001014105818810b60011035a50145141c0c108204d40040c00210307005400140e64401524200c1d9480100310b800350b80c5040c0010700607c241c07030400100c440f01d00300c01100e2400c00d07003952550b50095002c03182441e41403150f000304440030034035800340c00882e50203105201050401c4410190520f000101065007a074502482400016000603080395850354490f80940c1442c19441c1a03009103015800441d4850f0180710005010500c0c1c0b00180501d59041d14140301d03400380103051050070f0107a03000745404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52047171 1250 52045921 52045927
    0x7060c270e01140a15050c1b0102030702011b0803010b040e0702070b09010f020712050109020307060206040203070e040206070506010807260d03020f07140d200604080306040212090709060803040605 87
    0x80500503036443e000071400030502c1c0c84880c0c0d14204100c64880d4449080c010420105820903c20700600680d440880b205001d0700a1928000000b1744a108080c0001d06208030b03188010919405141c0d40215180e00c452819070743d585072503107224940c00a21580191540c40b50009a00c035101050207800c89214007a25414444480f0040d112502c0b0669041d0071446100000640301a400442050741c0317009100014012140c0c0c018107050014540284082d984468103000058400184010454260290640c032075222840052154414240d02400500c038150002c1100039000c01d4441c11155004000803c40100d180210a142412200c01c64550047c1a609035024065001000c0565071149501c0c078012450303481800050748800c2e45500fa40c440309888584070303048402140031000200081081d184000202c5660313000c001e0000304a08004404940c468945806850030706e028a0b26200d860304e412141c5650781d01080c400c40550f58104000040c5c604000300403a0b0540c2c0e01940c403289 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52048421 1250 52047171 52047179
    0x160b0106110d1d090c070203070b040303080604110c010f06050102190308040809060408070303050c0105010e01030f02010f020f0106080a0210090b030112021801030305120115120f0207060c270e01 86
    0x100200d4000c2450410012186100f03415507808000710f219120b094101511488036006145c90190745400800348075408104c14030100742c0140d88035030b00103011500820042c082075048180380c01006401070156090806904068020f60000d006a483c00e80c02c41c0c0084042400407075100700300810103004035800002007004034008030000c1c2071492000c0c08852805a41e504010302c0c1c02c0702e0303600550004502243d48011700c83e003801028010840c494940340154110340380c11440d500e020400070305204048030201586802849001030385007040c4000c000141e501c280d140e40798100000104d214142d04015021041e010b110001c0c140c64010740050700316800c000f90311488002000302640d014102d1212400c040e10280103c2d40a14841d94890b0b466085940c00300030f000340107030080b155060100c024070380a90b6104c054080e00d409070341e03404500c1540741caa80500034441d9103800380c0f44c14100000140100d4100e06200038104641d5511216000200301146490307920f401420382107115100104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52049671 1250 52048421 52048427
    0xd02030411090108030403122109020a0306150311040e060403080711060c09040b2d010c05010203010b0705100605090f0a15080c01091403100203040f050102160b0106110d 75
    0x180d10034415408a07640c00444000600d10744026403124040340e00004040c002c002600c1e0445040840c42d0900154203680e0710054001440c00f00c4e11101d040da41d820a00701550f55101d419802540c00c07000402c4080c800c0314600e625040c03140130036542e4240b50301c030b080c41a007440d01c500c04440c6141c034045d06080d2103540e000c8a443c0d8018161038200240850000681941440002e0041ca101400b2035511205903043c401a0f07554550150311840a91036807190040c2003400c43d100d009000e012121250031120f00581d50400f803200090a80d40c4003200110345e13240564020034919000310201c0c0e02c03101220751200c017640c07154002c00780c2110040001c41c04554402070711f10382203030616101091b2012004403071075280308582d0000103075034009102584156049200c0c3d001400e10054104151449140881c0d6580700c0c0408640c05194004009024000c06890070007500e54000001d641d1010a4010f5481340c2f0305c44441680d8032172003d000041c09030f008074003d02c48078034018080e000c80f2017007900c19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52050921 1250 52049671 52049677
    0x1812040f0e060111060c040e060108040510110c07090203090c19090209060903010c0206060108070903051e070506070303050609060406080c09070e10020a0606060801050321040506072306010501050d02 88
    0x481c103001c6003c8011041413800e0010512500000e40c215450307a15140d00016407600103010a41441041d006104c041240807910213251501d1400120f801001c00c41c0348216071080320000c8900e4050920040f07030b400b1403600118000d0103d03008580300f0860000c2004413000803805040460441c03a03108220450041d00580a10107004001c3d074201844400400d003581c940391582001030300050204401d0b9a00108015000003c501d040d00802c5e01b03580c3c0d0160b4038404800040300810b032290104200d00000c201d14006084003420f4141c403070546143c0640070381000d45945100710744460010b200381c1428800d41e01211f44031801484070401140c00d1080c0000050000340c20805002030707503000c5488200308008294090f07401805007003c0b0f803c02004480380307034201504100c00c580040100f50341c00560b02c00c0c820074024904a00e1440840000400d100356840190490303c04100316041c40000031404a501103480c5014540800070005140c44640902400c2e010840034850b0305100503681e400303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52052171 1250 52050921 52050931
    0x9111801050904021815030601020a020123070b0a362303040611010614010516170d140403080705130306050f0610030c0903060906141812040f0e 64
    0x10440c0b0788000c020118040c2d81c80b03624040e0141c41003a08210311380c00e248944968040305050114154148000001d403500c074800b1020741086154681d0060503d50881e07000891013801800c1c0396102010314005141400c22200c07015442c0c9041c0020200d0040200701103079201c842d28000b04101542d802003200044070000a40340b42e030300046941d1802c1103001e14115180fa45074000e40d10355181c0003004180d1000015a170540d0b90606c0c004020900420320004400d4109092003070b10f803010409825920f03051920b014040600c441e2800d0300d4506040c0003080c1c05584502d040c071840c0c060032680511008107840040c00144650002440726214001501c01d01c1c043c41214403000395a40c84440030b0760410b865440c0b161802c0300600840e031401d0085401c1121440c1018402d804d0303d01e0001d4201368003440080e260a803a40c20701010021198401429a011030090070550301744410342c84520000035580084070b12034803c014040400c0c10341a030b022a03000c034035405001c07800c08400001306000501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52053421 1250 52052171 52052177
    0x302100f0219020601080c041a04050402010c0812060907051c180503030910050f04080304061d1c0207090213030f03090803030112021e010c0308040c1203020601090609111801 77
    0x1000080c0e002c0710681203071412440d4000e15071541408640307420001d00c01c600912030703443c104d0a502d407102d44400c02c1000c410112800a400d99445c00162010394501c900101194030005010406e0500e10450b140261810b8401082aa0342d0480035195442620410080250410011401c0810390341080900d01a18800501c010b2031a0307550510b580c0095903a0003c94104080c3c4804070402c1c5d104059001d48040598103442c10151141602d5100c041d0018000719120307034102020190907035a034001030360444100c6400c01100c43c46100c0c51900303421100c0c018000d01d03100283c80345560081d00c1c0400c00c203141c0c46d20103620b103982d6007802c114000f00440501400c40000550040e040c030155008240080340c001307010781c0c10720401c00d00c8a40c110408120107400440a209660f0040b410314030150701d420101c0c06512542418064240c03036a02c10140c1c03075040700322101050342c0410320b0360488940080a1110548484001d402c0e80c40c0c2565200d45a4420711040e5021341d010900d03400c803600181 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52054671 1250 52053421 52053427
    0x40504110a0611161508100b1602030c0a060e010c020301060b1201090f05010e040201080604060506040605090a08010b06070822120510060e01141201050403090f0609030302100f02 79
    0x80302103015441194000804a44032031002c0800100a12115000c8405038100c4004542000d0341181d40080c451800c008111141d400580fa1541a01c450005000130f1014292200e51100c2129481c1a010000b00e01901a0198049240c00c1003908282951801d4840e601c0c440340c00710045030002c2c061402607034107640340e1100103404d00400004102940020065403d15810410361005840800c00801e040300d1810004000e0140401c0d00b00350020b0742403a00300b0300c544400000070081c3c007180c1c0049078091000180010308a80103002000e80d40b000390b5070100010b940e16002070072940401c0085403c600d0030403082d000101d1150041946952000e440c0606542c2c80c0c1f0242c00021441e0440d40c05a000c170070316242444010072000101824a44042c01070384d0522030140144401841000101a04002400881d903074196a9050200041008000ca07140a040003428880d0754864640031141888007c11814032442d1041c0680350542c0003000604e880218510007812005d0211420550034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52055921 1250 52054671 52054703
    0x61202070c0608010f0b0a050d051306050c180301020f040506090a080a05030a08010b030610140d11040e012108070c17070305060c072001020c150301031208070e040504 74
    0x1c0140740e80907000990341d044583d030415006440300000d50704002100714040c0b100c20b41581d400f404565a5441910011039a500c41078003452078001c80143c020002800c2200300507002c00d092001d8000a0140001841350f58985820302d4201c0c440c1ca0206540d03840100410310490800f54002c01090601a20f01d0304129683c420681c01c3c8540300c00300705c0303054000143d4695070a91203d401c030b000d4500d07821010f2a43c10700d140010101002100410148910201d200003240b440c0b1041e94010030203198144040348000b4000c24545d803241c0103e409807413468001050f02d030580346440e081c2440070003d07500c1082007502d6113030b0560049031040391416403500011454440d01a9070302110034910000f80b040505520b03082b400c03e80d0040002c00071050a0100c4c03c08030b5010b40c40180d049445030b0030a8800820380004030304003800713100ea050300b05440000864003071b14010001c6040b2401180c400c0d41903843c2c41d5040f0303044001901c2510002d85245030f600490b103070035030000d44c02034403404c106042a450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52057171 1250 52055921 52055933
    0xa1a04020f07080310030b0703063308101a0310090207030516050106090608060609010503160314100507050c0606040b0105121305010507020d080112080a110708031810110706120207 80
    0x10482d230358000652240e43c100720344d54011040658516000000728854003011007400c44542003040c800c010030000f00b0128000410314030440d4050920303484408400001c1c0d01c4010156070040d80e08038031400c1c3c40000000d11250034400e0300e04056050395500d14042c2403d10309441c7e0f00800f802907405560300e45002032185424810003008100181c040d20491400c0400c1083e6030b00140d206034002d80040303103001d441c0c660150440301a81d50004801d550484180b00b101e180600da10280c12405140109124000f071b04803015242c4003025108072246550b0740010b00c03050301c100d05002c81c04114288590b010b400c0160220590202481c8540142005607494450a44074191003030070140c1c04c010030403612640d0115880e4007414003043d640e505030700240d4942c0d5503842443c0c0c6c01d2081003802c44010941c64400c1c01038100610382b8004a17900c82e0081a152803101d4420b20391107103c0d0450b0f8018107c014041d4440300300c602012409080c003607207400001d4481d40c1c0ca80d00340b552140e500700080303400182c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52058421 1250 52057171 52057193
    0x1308031f0504050a0501090f0603030813060b150304020a080d08010501140c06010303031a03011a0123070501050a0b040b03070306020c0304090e010c02061f2102090a1a04020f0708031003 82
    0x200d1300d9404a074a514140b02541203502c810003243c18181805414400700390040c244079000340d000c400140000c031843c28004000c1c40f0080341c80354082104401d02030400011030180d4000c074021102c82c00201e0360b41071015a10b20048540780c0105003010b00410580d03000b0321540b04144200f68001f4940203000090301d00300300c401d81084001c25905d09000c62900400c40c048580c15105400800a080c00c01c5032500f00c14250314180ca0401480c9440d45030141c0340c804188088003c0c2d1040c0d035880c2e0545240540c017a040c1100c40f181070034a0701d061007045203064020b0303426415015002d0b10042d410354654801940c84000600f02c148402c00000900305020f1080810b0100200000500402449002403c100d800b5242e020988102ca03100229625403200d1403088401e00c1c00e0044030714541c0001c119400721070680c041d500020545c1041000302180e041410b044199038070303400642d441c06040004030b00840c0c807407180c0c0034000e015650024908100640d04454142640c840c4143d9903912118552 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52059671 1250 52058421 52058431
    0x2280308190f0e0d020d02030f09030115060809060f040305070b0901021c0618060609090504060f0e0d090807080d0e030a050706090905060d0803070302071103030a030c081308031f050405 82
    0x156a24924042184144130b112000d07125440501114040520003c0d80c078024003003180c0c0248400201d58002e40da007548100c00380c846440c0b007050681e5581c1c402415205007121007120a016810000d54002103c40e440342c400c513410384880b400c1500f280c079500c501c0003005126401540d4204404210810074202c1140e100c4030703181000c10500d051000303000464901e8000960f49c039080c00010302c01940c00241d9842036a100a01c0040d459441d42010700103880310b014080c10312803502420030007000012402c0120103500d9225180c283e69500b40d015a62a11841004101c2c0c200547d82c0200c41c3c4a1418610705100c000c0c1203030704110241d2196400c0400d43d81c4401d001c10120b02c41000b415400d405003550182d02140c040e00c81c1e00003500ca40382c007440024030002c00c0680c0011900c0c10040c1e1042c80110900000d01226204c500c034100150040c441200101c0c04220a44000303000710500225603400d1030350080c0303d2400c40c1c5903003c1079400c2442460a03020307100c4207160082810b84840c41102e101c0d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52060921 1250 52059671 52059701
    0xe07090303121517010f0204081f0f0f1a10080a090c030203120403050d020a0305070803040317010305010f110702060702010c0201110f0115080c030601050108060402040504090c060228030819 84
    0x14001324041ca08407145081c4601d5001d0041c841001142030100d080c0300303005542c00108035000d8205400034002c0c0541100301a019141804542400da0581c0c0201c0c40b00c04044004c1c16100310410404c400110f8000303200000440d440001080d0000e181c0252200b1032042c1581901691640c0c0000e0030042c0081c400382d80044081010001d00c0f40c00c010907441340c0c4060010780640441c80c1c90040041c8508000030f4052100003010508140c03140644940100c1e0381c4c000304009584034940940a0001c1c0043c0c149480d0618407a106a01d60340b5007214003040e80100744a250241640c01581c00c2c0c200c100040c1e0500052001c00b00301e84600b0b200400341d00044a00008031010160b80c007d1203803a02c0d4103c0d00669100010340019034400040460640d80d0900b019000e60351400005000b0380b00e5a08000e030010706000d482010031002c01c0e140000d44189030256101302440035480e0780011000c8241d02c802ca440c01c0c0082e400f0030300411403d604030038581c1400c0d200400485400042c0d41070854070310381c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52062171 1250 52060921 52060949
    0xa0203010923070e210a060b01110606091e040c0915051806040209060309011b0f020a14100204080f06061801060e01030207060905060402030705010306080c040e07050d0302030409060e070903031215 87
    0x8101f240c0c0b190b80c0114609003400c8c00540da260018583d40c500007000180100700380d0b404203c90140c010751250701a0b041030710407446890145400c0075044c81a200e5050300030b051524004040324840c5040094070000b40540050001304800858103400203015507804ca50300300001c1141340c690000641c4030392014000071904a124140440b180b0080d44c04040030400380803901c002d0580d022407105441500301c0c5c151408554035440c50760801c1115100c91002e5880001c000803444c1d4040344030200000c980d81900c42c241e50303640a000c0070a16900703161049400c1c64005001d82402020326000540e07040c034005042640399176404040b44d40203102601d050f40510204802c5142c00c0007081e020384004c2c40c0030300c0076624240c035070340e9941c10759002a0b124689582c0c414005000c200800c070000c00008007000340c0380b0b00c50300700a9120b60150107001819801c0c44030200c0c0400c0c4084a80d40540030701e0b40d8801c811840c5480440340c3e402105514141030340c5501150081100310103504014001150348070329 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52063421 1250 52062171 52062173
    0xd05070c06020a0209060d110303030106020a050c090601050a180509010906080606030c010912020d050604060b090702120405041a09070305010602010b0306040c030206030402180a0203010923070e210a 88
    0x342028541e8015021984070140500050b101c1d450f801c1c1d005034054944c0360030301025151411055080c1e0000680600c80800009021640041c42030b050710301800503908003c0108060114400c011541140824030030006150000d100b41d9209110f002040100102c0980700c20010329446002c1c0d10031041d4035210001071141d04014003205410103c02c400804224100e280040c00701c000502c244911800105940c01c15501c80c400340445e034a0b8094140c4006242903e44500180380a5041600410200d0001161280001040369511001000c2c19007054a040100000307400c1020038403181006054800c101c94a41c3c0316043e000f40c0303090300c0206080d8181103000b400c40300c1e000e41c0c09200342c0c020018040842d04a050007030039240c0544640c0d61b40da4850002c24000b50410491102e810041d9041040b2038603561302850580b46807080c1400131000d10413808010320a0356026020404080700411080da0168800c10310702d0707002524003e14800070b51032030005e040000f42d80d59229000081050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52064671 1250 52063421 52063433
    0x60308040501080109020703202e0b01080403020601031b09090b0403030f0b0603131406150102060c030c03060907090506040b1b01061a0f070611070501060803040503031c0e0d0507 79
    0x3d4054040e5030707800c60030a10a40c40040042001f040f0888103241c41003809480368809000c5086080581001e412240c0003151420000c9401251401d4120386003413400c0ea001d610406c0c8541c011a05075004019036400d41d00c1c0c6580c1c0100c43c2c110581841040c07100011007050030702030850124003038040034910f45060304000e41501c0400e20003942d007620b00718488030650b0b954000c1da40c00c05141d22240800c44002d1078402c065240d140c8180001c0d104103c1046114180070910508180080e0300707560b1141c4660800b0b581e070f40030543e548801c4070f03014000940103080a424440d44400585000031a69603034401181d107a900c0b54001001209000410b424500601c008038243d215914008012941c40c01f8544200729008000c458402c1d8030000b0010b006400c02002d440350141c0000040002e08000c103121354041d030064808807010350810b04000307003540340070095030300320348000d00510300e800c017000028008a00400c45148605903205200400d082040042c26a2402c0c1070319415a00c0407241040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52065921 1250 52064671 52064687
    0x30405060108070f090b0f0613030303140c042106060b040911040305030f0f1c0905010b0102010b0108060112110a09060210050103050309040504020301020c06091018020303160c0801060308040501 86
    0x1801c0c1580300c12400c106070880310000d0004c940c0a4000010a41c4071500090040840c500307c85c1d91280000c074482c88404036140b6a10101c6e407003502e0070084136817800c1c1c07140e0080500311804421302c2e4083c4000c1004090b080980c3c0c6200018010700c150100301581c86a046a80b19080208070210202c0c05021946c454821400900340c0038450314141440d5545043c1c0d2485600314282d01d84002140840c2084148016160a450f110083c0108500380c0c0703103420000c000f1104142c0f05503007001102d10380e13940107201d404180e10041c0d48440150303590000564104080c1c1901c0441150744403034100d41030303015102402a49041e41d580320340541c6440e20007890b01070415580c1c602d1038500707401000080c2e8004100c4402d40d40c25240800c031075603940006402402118500344cc2401094100078000380b01045031565105064000c1101d0b104010100c981d48204e044001d415134010006003c4450240c8403641001d4451034030b2910180e110701c1d425003914802e5200300c4000f1008101481590303005012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52067171 1250 52065921 52065929
    0x120406021203010302090a110d090305190e09060103051302040504110a15080f070306080303070905120109020a030807260904060e13030f02030409061814070c0b0721020304050601 79
    0x201600b55419a00060591280600740d400004d41d201076440326842c094060754a588043c2c0001c000d68941820054000d0788640444080b07400802c01203d20140100c103541400d8030003030001a003981e12500154000c100181a402c0d4440e6038900c80c0300141d5030313401194440c1d8400d03444440d0720a590810b001d04d841c03040e080b401001f5400002c00350b6942d8042141503000100c00302654558a500070150010161500001c03854000042003151894102100d074044030000d44d008402c45204411043c200e404248000f58801c1c940032041010698540182c4407050160060b00103800401d60303810f410b901c100c600c40110071400311f407035061072401c2d10501c401045d28004103002d40c509240b1501508180c1c810050511001006014000d482003040d40e005e0580301c83c0c10441140c0b6011088120142c3c0310290b000d00341880c00020102800b180d030b16018500380d0702d90f4079030301c40150340c1c2e110740c1c1030024040030403c6414043d40c0d82c071340790050700d074440c94840c0f82c00140e4900345401e0007402d01c84140c02c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52068421 1250 52067171 52067203
    0x14091e0a0e0402060a03180c09050708010803040b0702010c11060307120f020304170a1101020a050408210901050c0c03150601020c0d0b0703090809041125030e060708090312040602 79
    0x810040541c54010454007080c04c10b140005840b8101f10914880301c2c140d040203426020389100214003440c6950100d401030030a40c0700d1074411380c1c0e250102e40c0e59118600030085001d101b84001c4005500420302e034124144584007410b0400c1020000c190f241d00100d50340c60000d280361002c505418650310034281d28002102040d881c6107000d850300fa40d1200d00d86c90b138011b01c4800285000c3c00612900201c1003500c0780078000d642c0e03030714600c800410b04c0e041400341c45013500511990021030315032aa40c0340c003012100702c1c42c6403c014520700156901e030001039880285008100d00140c251380c0c2400031083c48602020f807290071782040c100091130510740c802d000e409219401511004616504001680001d00b0320300815215100c2c5824a1030380503e54142e41c000e82022503c19000b0130711000b0b0100032148000300c03a94117007c02020700c0f458a50101c003030f01082806c0260b101ca42450380040c50103078000c50f0b5003858564400003017450000c0780111600e5041c0082414480168107000c00c81d04045d00341c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52069671 1250 52068421 52068449
    0xc02091e0103030f030906060602280b0a0504050304080a060204030c0914060f0109030204091a10120215043501020408100506040e07030506010618080d14091e0a 71
    0x10840c0140e40018000641440030b07081002c140c05109030022060554042e0003400400ea45080103540c50310120489a440c092411406018400303014074841c03c41c0d00010403907044d80741c146512005200203001915540400c110204030b0400400200140368410300700141e07100e00c0c43c104051107000541084c1383e4142044641e0b8100e8030265540c60304004129a0700d40a0703110b000058402d01c90940c07000f50014100031a9405100888403800c1d90300e800410444c0740c0365108001082c0c0b45201e0b016005860b42ea1624010160030040030101403513100882003031800c0c0d113420300ca100c80042d020388490140d92240d00403038800c0c03107142d0901050340008002d509003030910400c00d0329020002000302074143d89500044186e6603070b40000364800380c124103071200d803134803801d001c0e071281c0b070074042c0c00041500d180214980b8650740810000b10b429003030240c0401110040103d401d068950956a80c0310700a100320a01507880810301501e1061400403104006001024401060a0b690081030401000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52070921 1250 52069671 52069711
    0x90f0105040608150111161403010b030d0f090b0c0c011205010803040b0304050109140d09050a15050a02010b060d0c080c070305030c0c01020d05040602040503011503020a0b0d0204090c0c0209 84
    0x100d82d454110000b05080e0001e8a40c8100481d482c468030618625580b02d146580c40c244401030347e18406a4841c10301884c20001101d0a2500341d80d42c40c1144e82d010383c0070001c030940300c61041e546441103250a150010300d40355078a280300f61980090800d10880d402840700d4040703668200601c084c00f03030042c3d801480b103580362013801602c900039842083c1c255003000001404003c42035125104069119140b80c007481612126181e54501c00d07034aaa000c01c68603807021485e89000f1440004450001480143c14600310504071560f40004000005540d26101130394183c0d07841d040504a2803000c0355000580940c49107009001c2076010705a14604482000000c010030361003030490364012071500000341d0320303038420702603a00900c201c0d2240300c03400745441c041c4030800c4150380082048900480017407100c00004660200051500d100080d40440003003c20030101140a024040036003102500605140c1d42c2c5240c84241c0d000113811000080d9001214000c51600900281c0c0041d901c00d4114005010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52072171 1250 52070921 52070927
    0x5071710090905072d0911030402041802030114070311120408071b03260c15060a0317030901060f0b0a080c07020409050c0306090309030604020d020613030503090f01050406 76
    0x2405484601d64450340d041c000e00c402006881d008159100411080c05260602d0b01420789100910101c80d80b0103010024006d0840d0141c0e10303a145420b4410341c40e50310381c0c1e400c100041a007558203180035410328200c0c0740036075003c0c030481619046c000703584a82031800078001001c550ba8101c6104031014140444d81c02c3c81540500c281e409984006295569031690401400500d190303048082c00d084850000300420001585103446000c0d50b00180c42030f0084101003407081d0148041ca90642d6000602003441104002a881e07004007000e000021059220b465070505014040c107045001c0c800042440a400000d1280300000c040c41004542c00301d050104030040d5215901544d020003801102040303030604000c040714074545d402002007043d120341d403034555102c41e03003040141d2007401b80400150361100080708907a20b100e402405003801d0707540e88d030030003601080b461006d80c1c202000f4000420604851001c507805103016030025900c9030010700170840c411040715116030400c0000c1c03004014a03a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52073421 1250 52072171 52072201
    0x30c05060730020c0304060c0c05120c090612010c02030306090604050601120504060f090f020901060203030709030609050c03010c05031605040513020306030109170c01060902041203140c01060603050717 89
    0x200b0540c0001107100990310305010303004107000c0b103080c3e010028001912079002519100309602c90303c828503103169510204804044001c402e030315290000004c0003014a0900ca800f944205c3c0100b501c070003004821182c500f100c54220100025030b0000042c4900c518200403074a501c503004440602140c40d0107030008100708025100d0789000d9845401141c00c008450b003090060102540003006039440c241802c00c030707640c41e55800380e018508a200205a251000c01100c0c40b8243c0c50325820740607807856940304020810f000c405d40f07a80c06400b0001c41555030a0007400000d00a9980b40c0380c0724202a01029690902c8250030802c0c0a800c1204002d00c0d182c202400989030101c1c000161203503184400b19001d04400200204400d02d10850491881110000b52103082c2c14000204051921017103120100d108a000303090904c211900300c0000284207000c544c45801e00a21918100f051301d800301e0782903c203903030008000300f40c40d00c04200407140e0041035844507440d02854900d081c11310203201c6000b40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52074671 1250 52073421 52073477
    0x903020a0b161d060912152508060319030507020603070503100608010e131a040c0603060504061d040503070f0503040306110a090314070b070c06020118030207060e0f0607030c050607 80
    0x108488504c06c81c14801400714819418600d00141c0c401d1030100d404101c41c1ca00201d038002c40500c1081c030b08813018070074004603208510180c014102c0003e454000000720400000c124100728003001454010f03121000518040c6046407201500c03420892106505401a604240c00300b0458000401101404032140c031b0300540003801d03c3c10741101d18140006038214140001400280803014003042091120803203017102e1090b47c0402c40307a0b46440400043c0c0c1c070300d445000d18001031102c4484552201d42015034105115000b140c2c503040e03040c0e407208051680700300280c60360b0f00080740070028030105009841d880c12916400781d1904040742400381551340c0b81c2c08043c02c0e440f2410740840300b145040040b180903051258040f0f860382042d01e42504003034028000e060045d401d01d070040485681403500300d9000c660640203040c0f91410004110b91003500c800c015640000131041c0d407402a111280144001170003903440c00e20303414a030f050003850414058202c0041050310011015805140c8603240880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52075921 1250 52074671 52074679
    0xe030c031c0204090207140f0c01080a020a0e031b030c0a030b0f0c09120105060307060504050603220f0614061c0f02130c110c030303010e01090903020a0b161d0609 72
    0x5000241c005030081c06030780c010703072a00742c8005245014040445030b0510f48900d2503007200d9090a108080b55100d4119404480c04160340b080459140a09a0094044000d480c0790901070700c0d841000080c6406943d02c1d0300c0354030800041156509040c18031074000c4222080c3c401000080c03460b03403960848200200200d00c0201c0240100c3c40048460007110080e9400a0840700740c0c0c0244041d2a00030042503501a129200c0c0880c00150140580150342c100d0318010552401c5035120b00c0d803002241036112071000c08105a10082c4001a0b011a0400005015600021390000143d1644d08201c0c00603259511800016004038100701c545d6020070b004d2544080c8046424410b48049134441e101100382000250130484030156a40d07015034042e03000310b40c00c0300b1507819030f20302810f040d101d10080c0118a00d640b100070050101075030366040b0301c101a2091046134101041034640c01a03045003502c0301003805000241380da6003613038400b107103591649800e6059650242c119001030510700c10240c0c0c160107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52077171 1250 52075921 52075957
    0x5070203010603050d030f060504060812070318060c05010e070503073008030f0c09180601020a150204050f0301060b0a0c0305120703050402090a02070209010501050c030f040f0305010e030c03 84
    0x45440070b4000b000210390010440c0d200100080018000d420038221410341c070313031410710000361a24142c056902240c030b0120140070b07001c0040c02002002d900050080d800c1c00002c0540e65074280700300811500412481c0c2d6406d81605507460090300303494800d00310b090903901610061141e07580100308981140c1c0708052084000d0441907008548007490180c0040b4860354408200902200100440c851242c122004003a542c8000c4a200180100b0820580003e150580c80c40003d980704111900400c05004580905e0340c280e03204610850000c16483e209500480c00300641c0c20040c80440b08004128000d00c030881c10300b0f01d8840f2501412000d60100443d96151106140c02002201c000640c1200b1050040c9032254000d8042d003c01d80e0304034002d94180c800506800240d10130789103c90760040240d59203910300001141d064002030f0072001c41e808104000c14103899003000900c010a210784c6044c008500c0e5042c080d085480600040380f290300200100c0e10034074000f000312810800f0140c1407081d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52078421 1250 52077171 52077173
    0x30b061002160b0d060801051806060123090103060504230c070b0c0901090302031014010b0f0d0f0f0905150609040803010b0a0309081c0501240305060303090a15031b080103030507 79
    0x80a082c046d03200320301651078441070001c80741c1c682241041c140c0e401030884960f40c0b070380b0004544480d0442c990710030444807000c001c860041c241c00101082c0405260201d5065110000901215522001c10703c000507894401d008551520320b41650010f14003070b145041101c01e41354903d000340c000301089101d00000800300190707800f5501c030001554002e0103c95400403000c43d000c009044000000c4d80711410500001060a40001196010320035041010304007002c01c0840b03000340c80d00d10210481c0320f80b64840c00b0200861072080015140c00f03540107050030341000c0700200c079240003e000c1d10302640d82d1108105c00701d0f0000c411030f411200d44012490756008114070840040c880008000c142c2600041d60a82100b281a1510010b16040c8000c011f607907030302e007015003420f04e19641e820000051004d00030103540c0242c2c012a840003024068034600b01180c4001030058416401016185083c100b40c0503120394503101c0d801059018044c548010403883d02c0c080c0200c001484010200200026800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52079671 1250 52078421 52078447
    0x150815060a030f0503030415020a1403060a03290a05040c03121b111306080c010e040b36060a051309050d030219050f0304061d07030b061002160b 64
    0x7401180c102d1000080c1d0401c83c68800e80f80d03030060703a0645070b0b5a8410b40746071186846101b1076402c000384d40c032204000c1d0031510440b01b440d00b000341802c2d844580604004041010741a10132406000c9240c0f402c489040940c242030302d00c1c00540100c650a1801e010030000038126092103042e00d40000340ca640c000d2a5010445804c9203100403503004126940e402c401b0012428040b03080300c1030850300b907030300340f035080c0305040031220b2511403000c0365840554000c03081e50045100ca249090301400109242403050701040c21036001000c0300740011703a81104684201c003c41d0f680f5801d030401c00a01c2e6010300300f140c001200c0e24201d001e2907120b2900340707038020400306259011700c0c02e01d035000c000c1d038419011019001e0000d4000c2c20143d580d0443c00340d00c101330684110110fa12255058410904540b00c9072180c1004080b404600e5001d59804a55002140b20030040b6600030f5209041d03010103481d10100f401000b24401101c402076501042c0701031450042c824500c01175840d41080103459400b4841c41c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52080921 1250 52079671 52079689
    0x40306020c070b300709140111070b0309060106090305070308090f030a03030501060906090e010b0c152a090108070c02010315060203090a0b13120201120513050115081506 75
    0x3181450300021002c2c4e5000a00c0c22000d841e01044880c040755092480070f540c00303440308a40c2640001d02a40c4180000c4400c4c0190030706036401032600e0180380750301481041c03821f05c994100c958554804000c0200c00c0c042006850b01511061500d0420107107541d84050f1b40b40700c5400014240480490851203a8440c00f000c00d50002c00101200d034100250b0030050014203080c00b4400000380d000c1e401045072030160b440001151300c41a07911056a203840d01c0000c0641283e40302c0c61b0316000d0003901e5404000d80041c0b80d4021803100440400e501050000b240d4102001502c107c0e4000b0180503000c0039a800c120703400d9001d03d030390405010b030001502c01240106081c0b00302d8031840d00c040c0c43c00309110784e0000180c0b012840035501007450f03e80302c0182c1c10460003025006114000d08100c2403103100664405400e4041c41810710400340c1d030400d10030100b40c481c21034048040c1d400c0c401903801404024001e07030f00030101c1c110404284600300001562901c0081103107e94605000d000f140d80340d1604440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52082171 1250 52080921 52080929
    0x6061d0d020402030a020a030605031212041502030702030310050109031713171e030405030a0f0501020c01020a050a1b05030406030e07090f020903150f0610021c090503010f02040b040306020c07 85
    0x440da01d1410043d00303002500480b10041c0001c0ca000300c0840c0c3c4d4140001c100050880515410b42091f02103180c2202ca5070b00143b00b00c440c2d05001e20f2003a542c1119001450254202e5005543c981c40d1010203040340c02e130f40c0c0e440310b4104810400e0400110741d0301c0e81c0824503100401300d4181d55100d011681081c0c0f0703045030b00015034102070049074100c0300d90100f071850002013240350140718900140030031640c901481c01402d40c1900842c0030940050300345040b00309240d20500000d4188280c51240500b2604100450b0011a000082d008282544654241c0900d04a10012840301c2c0d119201c9950301c0c0220700804c01455940d40c1d80070840c01c410082580100780410f82800549038514940b0041d410590549000b4482c03012104080005449440d02c58004650300d08d0440d51000d040120b07006d5088480f40070750140354158411642c1d41008030100384681d840b107910303403403500081c1400c5464900c1002c0c02d091050009220360006003007201c00b00d0350040310150700c41120b81d0546081030020341c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52083421 1250 52082171 52082179
    0x21090918050f011b030501030b010e190c090608010501020a050d0806180c0403110306040308070c021f1718120706020405130f1107051e0c1201090501050601020106061d0d02 76
    0x28002c0071424054001224005800300b070565240c80c80b074415025142d081c0001820000e2200040c00303c6080740d00700c1c0e548203c004c2c200010480040c03146504443c04000e0a400180f0301c4c0c1c0080c0121a044107410340140310a1004080c1e1004940721242c030760900300640010002c0303036000f0540755078440104204503403d0150103586030801c060045101c1d8850b10044400400342040040d141c5400314100344180c3c0c1503168400c0039a88c40c036003140d1465500f40101e0303116119848bd0700819484440c2d0601c40714644d2a80d2410304c141e032180f40f400b1007006141d81c0c0c00d0f10540048080300000403950b04000d88a1545031519044a4035055000c0e01540e0440c0d80c01c01011800b40812640940000b040004807542c108031071034002011203010301c103085010782a9130104641ea0f128001400c0715030b0080b484841501e050a0406001030b1080c07206441002c4203039128214402400802c0c85519006031003400204070607407920328003615174034420b011130071094101c06600b06580c41d001403c000c4598004c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52084671 1250 52083421 52083433
    0x9290c0f16050708010e030415050901020d0302090a0e070f0e09060d0305030c040b120a0608030315060c210c0c10080105010c03030f05270703030504051003020f0c0a2109091805 78
    0x7040c0340c0d1f5290814888c804001d000e039104e1070f030010b000300116008410103a0140c1242da40044c001e501a41c005070f103040d0804078001c8000f503070308158140e06009045c203175074110780060280001003000001401c2188140151001d100b080d55a103039851205691600701030391a6034545035580e071640074035841880b4042d4001040350120040481441c0b0030100a10300f0810741e40c03200700d82071362404210b4542506250b450305031422880c0c25030203441030b9250001210745400070000d041820b4003181010510a45007c112924240c0e01448034044182d401e4420720802001c0c2c800c0109129418483c80c2c1c107101010300b032031040c140b00340c00c0000900d42301c1c50180641d0a01b019000c02605600c0c1c40c40003c04002d0400100b4400045401d10450786c05030b4903942003504020030001d090100c4000e00c0c040c181e0810182c0c002425050251403c60340e114082c2c107080d44503003400c41030f001054107a088154190041d0840e80368121042000741e074000030b40092240000c41810442d106042409843c0f48644 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52085921 1250 52084671 52084691
    0xf0d0c081f050403020705090c0c0a0302061504050405070605030c07051518030c0a020f0103060509150a06090e13111306090605040204030804030b0a09290c0f1605070801 75
    0x66001529242071401e0900700005041d4101160300554000780141c01a05040006103088030b101504044080320703041c508070405c038860340b41c0700c000c900480143c0c010070104460700030141030356590b880040e107003440340c0c0c6440c0e61515125481d83c02213109010000c00030a080002074416900c90941c454103c035100494007107a049c0301d4804032091507480030069a1844800f02c088180c2d500344411000030030003000035070708104006c0c000804e2141099a81d11000a0640c1e690030054010502c640104420064140601141d4101c0b500030b0b009200e0b81e184200885001c002c002a4020840030361103100d0081407814288a07420810741c2035000c0000d1b100541d0165507513100904032100d8442c2080455903480500040c2d010358070020b848183d007444204041400c982049a111069800002d6940d1855503802c8404030b401c02d18001c0c80c0710001d04010004801d001c844e82201d40e20a0345814842c0a1072824082c0c071660f005084551203450011040001c104000c00c06000b10b080240013071550313 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52087171 1250 52085921 52085923
    0x2060f0706150609030b0703060e060d020619050711060c03120a021606050a060f050a0302040e1504050703030806030c1509131802031b090c0309070f0303110120090f0d0c08 76
    0x59005c142c0d0b02c2420b000200c0c1089010f84501c10854202040b02c00c2c0c030341d440c00c04002002807046c400380c1e00084200a09a80c000e03199402c185080075503242e0f19203840c19400c1c094900c001100c42030b800f8034810800c802c2c4101d40003058660041d0000714400443e59403d100601900804244110007401e0751082d40400059410451083e0201c45040080c241d40c1c5820081c910305d00e05c21103800486140c03043c030141c2010b0304581c04208462044a5034400414020400080c0885007900c09800003d0305100301135214201c0b030341180d0704078002d03c224191000020580b4803944109140007000007141c42c1c95440303541d020240c03081e45007000c0240c001401000503070580704c130204a2080c010549103110062901900903d03000014107005102d6a641907110032540c805001d0030824031a1070000507000c000300a1a0010350f10aa8070101e550744021840c034207490303070704002901c02c2401d280d9044101c040c61081c1e641c0100c086440e0525035030301743c2c0407a17180490210007400043d6020340c0407924400c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52088421 1250 52087171 52087187
    0x102030709090f05220201020313030309030510060f0b2217010605060f07110a030803010b07031e020c010503070e04110702090105030a050d0e01110a150e0a02060f07061506 76
    0xb40b610b9083c4440c8103191002021244100c03120a01081c82040f4008a0005202c12030301241c418012285800d4a41c481078282900640c801ca0018103080d009100b044024481050100c10841d410f020050515608202001e03a038003034a00d43c0740b404240d103100d000d201000c1e007000b0b00f00c1105059081383c8602041c0500c10300401c40c00000c0d0300304500000e083c113080d421240702407000305401d03040040942d80c098641c40b440000903401121010003102050881000f94001c284031806140c0d224007e1501420554030f15150f5500131360740000c0301d0002c54010603841c400031024a0560b50341c3e620b4000a4840040c4140d640b0b03005413601c0c44010050385401d00408082c2d008031940c2605a0f80c901c02c05070784100d003c400400ea60000a401c2180038010012181c4441c01410301591410003510854941004c084003960703954084260b800072205d0b60700c030b0703101c10042d01000303440c01d02140c2e0081034107803043c80c41e4001d0403c0006200000d00c034455101c0c9102014000804003d0382c0e580c100104025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52089671 1250 52088421 52088429
    0xc2a060901030f0c23040e0606030402040e0708010f0b0f0303090d0303180302010e1605010516060b09090c0103050f07050a120e070b04060f03020301050a03060b120d0323070e0d060207050102030709 87
    0x403000a40681c40e00b1080d8082e2021130f1040c14100820f88e5070a403e2003002d403c0540304980042e10b44101b50010341d0140310150207031200b080001601e1450310090004e03100c003200c01354042d4210382c6000079136440c00320444112040943d07641d01400520b00c0d046001300706000a00c07000101440c070400406d507064000740103014056003244e40545410f440c15421004500c42c0c0350100d041005041e0f03101d403a01e0b42c07246066005000c002801c605560221f440b0001c200c3c0c250301d11380c00c0300390948141d40e0948580307504502c12608108051404140c050064850380c903c1e50140a80307042e1500c140c1d0f11540114545400080c20340d0401c41da030700840c811640260281a01041600c65a40010b910910950b07040310720080140c3c041900d5070304e445004080c1e2824590300451340e001020486801003004800f4078119a400080b12144d0302d034925050128669072854180340681030001440e8000382d0034140300c0d001c40e880307000c045451400400a11440c44002c00c1c550000c400c01c094140c000c910b5404031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52090921 1250 52089671 52089707
    0x30a0c0f0e090d08130302010b040908070210110303060103090507051009170303091002070503090a0b0307020f0111070303050907030f05070f080f070e07031509020c2a060901030f0c 80
    0xb501e500c441c8a49401d0342040c107400107050000003551901c603084922048034000d000026021090b60042001e40306000025506008001410021801d0503210078081c2c9000d440c060540c510146203140e12488042d22590405172595841000d010040c40608010400286002c5226404003005130500da240d20900d000c1c0c4948200c80e170100240801123902c43c04070300303015002600c94900507400039009514141c0f80e510080c00380b03c8068030b642d100c0401030200c0780c1d8a16200e1504c100c0c000c0c0340c100e01d4074400603564107000c2c011100d02c019400340c805e041d42c036040108d06c507030303c17480716a1419006500240040241c1103511042c000f000c00c0002c15190030a0b0300e44200e903100d400940d40c400041d07a8407035459001c548104070300c3c104640000d41004041c40d01007558141002e00c20b40ba08040d40203818075550020348171000315810402c551600607260507a11038840c81740c641e803903440c0c03140c50b85900034040004d007100980c0c4648e000d5910340701800000c0112524140c4000c0281da4000690416 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52092171 1250 52090921 52090949
    0xf01171501080d02010b1c1511070507050f0105090f06031305030f0720091f08070f0e0105010e060301060311090901030f0507050a14041508010c0206070e0f09010302010e030a0c0f 79
    0x1081c10024062000d04001d0a81408910300c01d583c4c8045600c900f07040340e10050740c3c0f00d100c01e656206580c01404407901603801802c5407400c0c601004106000c031050b93f418841c1c1007148611a07240c4a4802480c04401c90b902603c0b9030b40c0241182e000811084024024000084e030f018040c00454090320810b0700612801c0d441480c4442e40090030145550324990001000001450041e40d0541c420703160f0320394298a200403035584403980e00d004002d410005102d400c828050101c0c03480703030b6035050040409103400c54102c960840444d0306840103004040405445110b0b600d03008890318125070000c9006040000c0355a541d0800340641e0301c1c440d034200c031180141000040d845c6401d48070b90054482c00000d11084400038800c0000422850710103160140d16240c00103241e003401e2281100b400300a40180c4450314142c000104145118100300d48103486040c41c5042a0700ca840a050540b84c0c20700f083c1b990030b010303d8002440d027001030b403000b04400f0719041c020030300c1c1160f4801102199022980b03460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52093421 1250 52092171 52092191
    0x4050d050403030e090a06030503040b041805070c020d0611160501050609040c090c0903050a050715020a1104050408070f03200601080606010806121501050a050303030f01171501080d0201 82
    0x94501c5648009030001c0c03030324040e00c040c1c0c3c506203c1c1d145c2c0003100c120000a407255250303200c0c0c0c1544c0003076011042d040c8011804212a802842043c903c3c540794520030071451424240242204200c2140070b80034000e80000d0304100045a808010140e01c00e9410701e8032109501ba843d00006a000000c85155090501040803030900300d06a41c0110b03800010b005010f81401e44090062000e5000c4508005031680000003040c01402070f1030030280108068640241401c1426007030389200c03461041103602c002010800b0840d862a81e05601400720f80200c1d0706c0d1074a04001d070103402144009043d011260080c2010180c1107000346200e60207528821805000708543c0d69110142440b51014941005000034104e620440c00300350f02047c010721500d5940321050a140c904420306201117000e88054005020078641100330b6030052501318001c40c40e6240072000f611021806100d8142204a0004040c041d650144086c0c010000910010708031036035030f40307140d40e9600d110b280b4010140d440e00c0441c2e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52094671 1250 52093421 52093427
    0x9010b01110d0c06110702090901060602120708040b0313080c010e0d090806040206250303060303120207051e01062102091003080f030601030f050103030807110105011206020c030c030301060804050d 87
    0x40c00242c94400ca00900b6481d4000035005101145c0408081008040016520040031a008035002000001c20754108100030b860840a01d03801d5540101c20300002000410701000c5a0550300e109a10381d480e42c4039002d45035445096840010100b150101d501d20309a80f055003c454800c0b0310400300c0704240b1890900b81c0c2d402d8030b580180115500400005405410000000c00000b84045091000c0e026a1080120564406c030411400613490720010014503901901c20300c001040100c1c02c600d0072504bd0307200c4e41d4400c2c0000d20b40704c2d4020f1091884903400003c0d0300a02c02030070b008801c202102128400c080340010008c1d41244034480312000304021b07940c1d00308101d040da5444407240e840d00c0044510709190b500010022410143c40c0c0007a200a040070740030f10b5009500c08e8030b45c040c0604003080c020b0030b00d0540c41244842caa01d040d004000c2444022010783c4115008100140c4e142603003801c00b81075109480011110f4070000000107482a07110003070511440c000c2054441c250009a011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52095921 1250 52094671 52094683
    0x10f05011a040308094203060d031d130b09010f030b0106080a020403020d03050d0506100f0c020d08040618080a0203030a030e010b1e0a0501090302030a060e030c030309010b0111 78
    0xe40e07994003070005000042c2c4032001010704030002813030105401c0308403032007100200b00a81c206440c0e42c403500d00c2070034030002010849141001d10142508501d898400f048440409101c00340030403407810070080c047e440a0764600c0401c0b001620b002c0d95082e030b41610070060403081012901401c000c2c0b0002814485a04500084d40c0c1d010406400c9640781440480700010054111070005508000c0000103940f200c862911480c0300f501c9040e103030150800054200c1c3c0340200480d00590001c1c0c458100c0711f0380403142e1304003c490342c00c100c50f40314864000700d0311010004000610082d0000380c04a03850360051492020304044001c0608400c1c7c07981d407200d44505440030003d4065200f03011003440103009401a01e00f090103000001058170b09c503c0010104601c1d11031140240440c1c0b44245200d08103140c0200c090103080c2418400ca80c03441e40441c0d81d40518a42c0504003982d02d0101a040c040144210343c424503452003143d40302d0400c120340ca8001d0071510240c0b40403808401c8616060b480200d44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52097171 1250 52095921 52095959
    0x510090509010905100b0a0806090a02070c0b0a020a06050906220308010e061f0324050901091a0d030f020d211a0a14030106080304030215070309050a08010f0501 71
    0x21541d050b92030480154003504028007144012035404001189500041002c0c2c0700508860307a40c1122800c00d602806040000030b017080342c0c100c1c010000c06010031200c240f1241203070009904240d0314040d0581c120b041c03030010000103004030f04010134010314000001d500b50055079260b07100440d01d84207100c285480300900c2401404117158034010000c042042e903102e5400f50010300200c0e00100020401c83d2140000c0624201007580c407408894070301d42e2813041b00e08080da81411041c1140c10307d000552140c50500c103da42c025155130042c41c0d041900d04030841d00101c040c2c00702e540c90000b403a024224115100d00c01c00103100340555210f0807842030104041051950074072341050518000620041c0c03806446038500c101050071248420740300c450401000b0030f1841c00c2d601c80200200200750035652290720551803a4000e01c411f10140ea1a000c04142000324070f10301d40d94940b481e01d01075600351016444981d02880c0010700040e4550103403c07070703000144009001c0200340c2c2c9510a507001d0704460b0321 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52098421 1250 52097171 52097179
    0x103091505070905060a080a05090c0f040b060702040606020303041a04110603040201020111040f08100606020309011b0c06080702060906010605030109020c1006080114070e010c0209070c0f050705100905 89
    0xe205010140c1507070086800004515104207841d8490340820001d074802c006050008640d502044840c1c080d0344681900085d500c009021180c0c0581d0000e082004006202da224680d07a481c08005070795040201e580003507001c1c10900c135540d91214082d41b01e8104417820780e5a4a0fa4804c224192030520145510969100d02c0d44003403185c0050a012450b0002030049040d0341d60f9044200760710241d00060320082441e041c0c150314903410284a1414158040d82520400d401c1200038008580c000c806d5a10300000ac0c0380c4880000350001860102104081000c0c00e9048442c401040c140d60014103540303d004103800301c0300d041d10750b0035501d0741d500c0003441100001142400180414800364000b407004240c43c10032952400d90b500060000c842c3d659200c504140c0d174a004a0640200c1002c035250700ca0140d083c4401c480c102d24002070a0b0901407e0700a01c51450100040c010a001e41e4400f1201908210030307840c102c40f03170725007966205001e024040c03103902101605c4040c588544502b809440001e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52099671 1250 52098421 52098443
    0x807090810020901020309130617032a070905090a06050619090e071703030f0f01120206091201021b060a060605120402030c0d031e050702010e090a0b060d0504050606010309 76
    0x481080c002d42040c3c03001c904600041000039110350b60075019420b141e440a00c00106130b85040102c0b010400c4488842e8074980047c4004840440940750b10f082d2800d80d50308010b5054001740c4a00e0410405030020480503241609019840741c000030210900e52084c0c8042225031500700c10040c1d02d1155848006c110022001c05101400c1b194105032107401e001811102c0503a142d58120341608160903005940b47d00100400c5070005880c08819080501002034804a50424001001c1d80800c000082d000c1d031400101c803035058450601d000d01d441c801100841d00d9200c4107025410403190444094464450003001c07d884102a10035a0212040c1d07486072441e000005415906090005106030f90601070300304403003681c1e00d5464040c01054441d960300d0f0100007040c6842d0054144485511003040000c0c480303000180d80244035400075031000c940c0c6036501d03070303a9050707901c041d00c1604411a04250301260072089010550070140c000c1348503800b61107443d40c03400011005c8803811100541114800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 52100921 1250 52099671 52099693
    0x120b030a21090504022704060b0c0c030d0f090e0415021c0b01050405030a0f0804030210080f0708100b070c08030a020307031403040308040807060b030a030507031b03050a1407050f0a0308070908 85
    0x64040a40c001b24050004541287d955007840029003002080781d00340e4100380050981440e0034070074154981714505010b000c03283c41d074000402e140711074012440886944004103050080304c0c80200c1109045580a544d141103002006280341070300300030328151740d041005d03085040d8003440030307102170301c8001d0000d041340c62145d10b9501c008074921405a91416007007101001684840b5900801110942c64030755503410a03010701c119120000b072084007084100028480280d544c00c840740d08481320310f00455200c81090070301c80d000c80fa00da4003200c030511001402c0261590048064040540a0340352255601d14540c840b01480c401100c00030300140c0c8240000d4001140c010107004950f001d100700080703040c00000400d10f08a000d1400750045079002c100001010741c051401700038010385001c800800c206031ba4000d400c9000c0d2003101c0f02400f00754540c1c03200e07403a030100648000720f81000c1111610b083d00c2440301c1d15803040384030540006206000040ca035900507041041164440402000300d0111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 52102171 1250 52100921 52100977
    0x807020f030307030c0302300112031b06020c010c081803030636040f0209090a020906040203090c0a0308070303060509040503160c030b090c01110d120b030a2109050402 74
    0x38030b0700005c14150309100c501d2a54205686404847c102d115160341c5036003000b81c00030340400059214911182c246030800c0700080c3d202c1580c5441950300c50001c5010b207403910346080070b03004800e02c03c03045603c1c0101b40c1882c07581c000e49860285010740d103001507800c5d000c1d940a880344401c841807500001e602100e4940d042c8940011580030b503203400013503085078160008165214007514140c908901c0a50704030154074128274144d07000502c06000340100c64190f80801d0380c10070300500da288110340c003200040d8541402e00092810302c20085c4607092a5807685007031101c0c0c0d00440b0003036000901e0300300d010803a030602948560160390420002c2d820035025488002141c0e02910084601d00344d004000070003d25820503c40c02a10048090b1980161045c0010082c4003242031200b039603400841e40c40210307504000038400603040c40002040e02e80400e070100f858100c10400c010301702407103199900e01015030800c000c290b100c0c0aa0328240f013107964030304010aa000700800c011050aa0107072209032044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 52103421 1250 52102171 52102181
    0xb100306030b06150705060c030703060501031803030b0a1d0f130c1e092309030306131d060718080a0c0e07020109051002120612120d1401060e010807020f03030703 72
    0x9000705543d1030245c040d0303129800c08400741c591900e4241e0110600140903058002d2034050582842c003003140c001c50328004a51001260400703414150380794000c0b1401d0301d81c424484054100403207801d000e0300d1200280541044200c1d8035082d40140c100c0400c034001405400700e44001c0d040180c07044c2060912600c149201e0505426144171150702d9400a59580140107400742041c401022215283d180300c403000303503050000c1c261010f07508100100310090b558401d01d1201185204d20016a4050803040c040e41200340e02d10040c4c80788103800800c891158402d00d8240c1416002e001d80072002c0d030b0b888080c0c0d078071103514200030007021502c1170a02c02030032400c00950b4050307600e100200b00e005064a0329800c2c2544040801c810315000240b4003041414078800f1904000300362502c04605070404003982d1144400e01c1c150318039030000600225543e100d900700d4203520b0b0203001c03800c0c101d50350b803400a01140b81031000c5602150100d40020380f110b0002c07443c021824000d1020751314660b586d00007100180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 52104671 1250 52103421 52103449
    0x30c0705150d110306092503020c07030b0a05010302030f0a02060711030a14010609181205070201051201081f05100302010f09090203010b13150c060515060d0b100306030b06 76
    0x2940520984000c00d825001e12440d19580105590b500d003003070010302010503c007d0180251403d034206103601a403104c0401c07146803030706140060b1140741101d0214101211507101402140c004014420998020f40c0414100c034400c5003129004076070700c1c5499846008403400654045403c1c0056804190311031101e40b40140c0c003c0903142c149085980d4017090080030410100140e540303100502401140d44245040d6030304988118071071807580d07503800032070160a2002000300300700450003104590140d415a890107200c005298015070b120081e05507078410301900c0003030307240d5100308407070078004140b1429000d003110202100c10581950010340300500c50340304860802140180010308100c461010318044d1680d0b2a4441e0380303800500e241c50b81e00b0710641003a410a82c21200303c506c11078124401110050348468045075640d030b0402c80d2080c0501c4200380d9a046000020205071100c040d600c02003003004d040313407490120000751008034210740e0f8501004000c200303440c002c100c01c0e02d0266500b000c50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 52105921 1250 52104671 52104709
    0x2010e01021e0c031c211404110405060411070210211a0406180914010c020714010f0c030e030c0a0902031b030c09010e13090b01060e01031104090209310509030c0705 73
    0x2102c080687c0301c0700d10380f00b01e400b81d038251012078501d00c20b46018052070303801030802c580174000212f80c4006010b80c2e1046c5a0000d1003096881c146281c03103801005090380440502000b0952a020351000b04054060301928059020690907204041d240034842c0c0b006544580c010003440140d10302e80e00340101401107040c1e03049844c55031410700c01102400744006e81442980501405c070701d0300c043c60f00c4640c01c455803541800840400a0442a0712070480c113042501441c1102d91681d112000ca81065500180a41c00c00c00c3c0e10303404140e00e5141c0d00114000c440f50301e094801e0a0702e4000200c218001561221031030b80b02000198103942c0300301b60b80090300100505d010a20440c4101c20403c1702d000442c01c0b01d01c2500040100314054201d907890602800038242031155500c04148500d080c4642d020305070301074bc4e000c074822440340c65403c078000c10800c505205191000f40500c1e0840c41004600c1006241d509080000e81440000700a6076041070040b8020110242054108040100420700c11002c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 52107171 1250 52105921 52105931
    0x90209040e070b04080f0106030201050a180302060f07050c01020a030f0c1a01090b21062d0703051b07020306070f051207050301051e0d02010e01021e0c031c21 70
    0x1004405104031801444507903c4250345615041c07a040c00d014502c9442240fa924110081016036006000c65801c44601d290403c0406840e850007a01c144194201035000840880e021821050040050940c640140c0c1110308503228003004999505c100c5100800252481008240441c01103c000c100e581c4210484082c00600709649400d941c800da2124484039211a4007040314140304442c108842c0c5c2c203030074580782815030074010390781c803200904921030000740d03228008410000c05c2c89402070003013050b549038102e08000704001d000d00419100c040e1601c07e0302c80e002c8101c040e0003040f1902d20750b0240251010b0351321584140ea044090908840601104020681d0510f25075800320b40710b0321a0f51102512035061406102c082078000c00b021550050440006010f0b03075411201035290303a82440d00800000508004078200419a002000801c000c01c10101e03c2060100340b060220005a085614040301d46038041d00039103202000c800440c0c2d0310b140d0b182e11006151202209030703d000e240411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 52108421 1250 52107171 52107191
    0x9150909030c0b1e040f03081e0c03100905090c0906030f0601091518020a020c090402030a0213020c010608070305120f030703020c0304030209040b0f0903040b0421020409080304150c05030109020904 87
    0xa008134200c80c121141001e2603d00320070507400c19081c1d40c200007a100603d885c1281e80c6035841000c0405844410540e6000c80041e884200d1640000060070180c0000c0c0402d040640003d0f540e5000320454520540040001802600f400540c480c0c420705082d0017001c940e468442401d00800343c0248045c0103210019010a48031f800000180e400030b210f076001a900c2d880818002d0030000c040050500c5010400b0500015941c00074000390703d01d0f0100c41c030b244504a0142031301c1c000c2c03142d840e04028950034298002182c02c00800c140c3d044a010700181c0c0c5c014020710701e80300100e1142e407444002c1c200f810300102d03005511036400b505020804a0403286084e480c0e40009000500c111000c943e405e02c1c640c100400040030702001070700729210000440c1000d007001182c040502950141b10100100110300310882250344001e4404950042c0c0304000d42e40703a6007407103000d0341c0c03040b607050326808208503001c1c10303c0c000f074070460303510f50680c0e542e050847e401c0842c0540650707c4146120b5200e034950900341c4d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 52109671 1250 52108421 52108471
    0xb01270f0b030616020c01050316030b0406050a0f03050f030c0604030f050f030a0e0f0c01050a0c0606090905060702120301060f050304020301141f0f0b0f031f09150909030c0b 77
    0x80c082c41e0b5507101c4d40c0080490300c000900d80090642c083e410014184107100c1960801b56100400031028100070516403001e01c0800d00419180e030010394080465040010810101d09100f015240541b0654200c8a44600001da40e4854801050440c2d03029200181c0441d21805440741211414034000e0315005002103521020740003561b41c4d0b0812666401c3c64402030008100843c1080c0340b40010b003000000800001c0c1460040300004420b01140100701403c00c1042ea02001c080d0903610800c000c071106a04016a41d044101c0d0a24054804c003013034040102051401d40b4102c5805903aa006030000d2990304488a80019200b00d81541d2250440c0090f041c2c424007892040c0700c00440742d000c0082e01800d0700101052a40600150f0241820902900700c140c1c0403219481a00d001d40380c0d07a03417140c0300d00200380303001410380e070600400340034000c500c0341c00c65080400589003c0d552444426210600203080741c8114400402251007080414001440b800a05501510b4500d04002d4445000504 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 52110921 1250 52109671 52109683
    0x909130b041a01050102060405070e190608010c2705060f1603020c0a050625080c0f06070801050a06080703090302160803190302030919020303190c0b01270f0b03 71
    0x301c03905040107440980d1085611002c9006103001d00c010940c82c2040d8070b80c6a210340312406280014154840000e4a2442001c1c0c2d58845085010b001c20099542d05140c600a1520158040c0003c00d103109456a07902d080050401000700354980c2c40120b4944010020ba50740481c1e20b02c0e824000500019001042203064581142d010f50090244a000e00d400c11801c0401070b001182f040c1e40a108680410fa103030446220030705420b0076072015440e0281802c0700f250090048545107480350205820b010980031500c82d004504640710b020b603590b241c004001d090f5041d070080780d000509a400040405201c1d8000032045e0f07001c2d0055030030b02000a02d00705812240d030f40003074110b54000100030301120f05c00301e20b40010380224031b811415800c101e0741c900d844865002700a11180100100b600c01c1d9601801100c0361610798002d0f1441200941c04090402c000c10541910001a07040c000200078151303401c4240104221140c0b501c1400c6078080b140020b00d8069052280981e45803901901c0351010044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 52112171 1250 52110921 52110923
    0x30203101805060f04110405010e060c010501030302030a08072105130803070f02060c04080a0b1b040e0402031e0303010603020c0709230703060b04030b0c0910030c09060e060909130b04 81
    0xc1810320f00f600a00050010400744940106d01d0b146081003102d01301800d80d41034030001d11702413142280309000128540542d088600095103000000410990000300034008102107494085503a900c0070f60a689215681c20f41e81482501ea4107441070445641e40059400b00c0741c041c90fa0318003011074444514541080350428042405c0072101000c16404005280e4003520b0b441001d458030b8207080f506901d42c1024a00204009801c2c00800c02c00103494803240b944522070382045840c0e643d2455803c038034480698042e0b0183c0900e000d0381c5111914081000301c24a0104021807640e441c1c00411070007580407540e0150980030300100802c0010b020b0081c540144c0441c10119100e807140b001c40c2031803450281c440424540707484020004500e5100c192011283c01c054500059901d1416200b43c61040b008690382c081100c2c2103c500203a0180d02041000806955854109444610960343d140003084860b40c03100c07062100030003d02e0114980d9070b0040503d0503100d1946000d42da0000b85640c1a58 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 52113421 1250 52112171 52112219
    0x812040308070312020712080a0b0604050a0314120c0c0a051206150315040f031b05060f040812040c0602120c070b0703090f18050c03041a07020c06070303150e060a0603020310 77
    0x1c240888270440380a030212071030040300d03800d1401d45868001a2052901d2100a0141402d003c2d960807903102031165184440396480f0341c6c1ea40f905034549103900d8200226189101e03141c4244c02080350b081c0000032518a02c00d050041485483c2d100c6030313407064041d601c0c550b0350610490b400139520911000d0722030f0056100e940c0840c101c4800c1e01e0090700c00c40f00d51030511040c014800528012030780029846400c06100346405803036441d1401c243c1d442c3e01c07500840000c0c4905410a1004014112401004440d803550a0715210340e02d14401070035510030341c0300f42102d40c0d0140d0010b0018401500051031020720034104860b2050781d44080c0c0100025540c0b08960303004204040e2495150580592680450b0520a20b89580303860f5403001c0010311042c9000c4110580c410000d511a80208404c8491840c0100304179207500d2a494020060444001c0c4000c4030f03a031000d070000c2d1341014000c2241c007401c0001c052228503418841c0460094100500c042801e000e60780e80054040c44a425206042011003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 52114671 1250 52113421 52113437
    0x9030703031205070c0302070e071701060806030c27061305070203030103110a1a1e0f0c010e0d020a0f03020309060708070b060a0501050415110f0105010812040308070312020712 78
    0x242d110320494074001c184c1c005115442040a00107079000c80e00c04140c1d014a148500d254503001411510408060300b84801081c0d880008640540c1220225100d95411021600f2032a02030080c0b286034045074404007800324403110003403006000c00f0031841e400800070300301c00141e61a1034080f4007512019201c90300513800001c0107005100d40c80c0341820a901080d42c084848074070b010011440c07500030a80344042800301040002170f0b420001d14107220054105126520342c1c4201407082001c2e8483d607035451440d072810b10740034a01d150204074200c0c0c8c60120380151509180070785901003801007480d812030450008001d2800c96940e00c1003e4a259030140b60030545407403c3d07140c0580c1002c00644060701caa00f51010412642e0790000444090f10050000510f100c00070301c0301961041c0c2400050041400b074440342c0348015005506c4141200c2c042030495843c54110003401206208a0002501c3c40f0780810240010038000d084616141c1e040c50401880e2052a4960070390811030340a400c00020070f42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 52115921 1250 52114671 52114697
    0x1502040314070801020315040c0e0301110901110703050c0d080409060e01060f030b03070501110a150203040b240907210c09080c03031617070807050105010902070f02150903070303 79
    0x104001d40103048900005c42c03541c103007032524518801010441500c00c54072101c40144491044a21810300b06001d0f009103c000d40c80091001c0a03080702d004107001604090741c4a03c0c1242c000752007400c6a4021010340032481881e402d0050010041d00d080c4c0d01e4000421000460034100d10a40008042c5041007016035410007000408030304c0c0c40a401810103080c0207408496030f8001c69400201c6000f404c00c64916808044060304100c64000c002d010020508602085083c468004522892240e420780e641d0b0f81e914000b0205110104814145905801c82d2406042c2494491140c000c074031414400240404a9804906110780d1640c00880c03503103801e84c2000c2c040e04510707003002410403031b0042d001d00307695500403d80c2c2e8080e050440001400380b6021300140903141200150f94190b045245a468102d0709040c851070b4040700c000c6410358680070001507140780500c2626221540200014024070060b000c00a1800465003400c1080508102c2c8080c942e030200020300040d407207601c3d1503100e0080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 52117171 1250 52115921 52115923
    0x602040314100b120c0108070306171b0904050303010306050a1d030d0b090c0f07060605060a170702030702090606071104020a120b0a0602070b030c0c03070804080105060d0512071502040314 83
    0x324a60b00d0740242003107403a0007003500000c1641170000000786000c280b903550b040b00880140050b075100d0b80c58010b0300e084410146901160906d81e002c5501605000c01251000388024660100c4001c0d10681043c80188000380241d01300980145a1000100d03000846100c1c0c1c50517010440c02901c40c66000184250400075a4010f080c1c40440c22103141103d843c6c80b081500790b611810121b0300e0350740b030b0004610081250a03404180980b0010346070684034a9424406004804288150368060740e80c28001156076200008031003190764040d140b910551110300602ca09a0004001207521810500b14030042c0d89541c805082020725650f0340c1c48070440100c4140c0c003120401c0118900402c10104117100c0340d50001040d40460b281042025038076a40c154100101d8081d681c022034071808006170070000c1c08079110240c41502c040c01d00802141c0c0b940d10800c00070030413099000344035130803070545001c0350390041000e400e106003d803074290600c82c1e580d0706a2040b40c1c0190021602042c060050004c141e00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 52118421 1250 52117171 52117181
    0x6080a112b0e07060e010c053903030901110114070305060a0602010203090c06090d0c180615020709050c0409151505030c07060b010504030605160f0c0c0b07060204031410 75
    0x103400750402ca000c03418030801d611040d80c1c0c05040c0510101d0000701c0340c0761b4444c2c48402d83e803e41180c151602c00032924401a607a5150200d00304203085103200c00c2c64074002c6540a031004810003001140703410034503401500c00c0c10303228554815230b56039070894880d07510b02070b280f0920614003654001154605a000c001440382950000300031a0320600030808018000910010405404c40d05a0b4445403070034002440041b0805004101c501c0f01503001418511060010b0000508000b0a002d0b49403910345100350b000e14421740c1c10059201400030041890194082c90300242d40c0c0203600c3c581038403026018280ea959441c561f4030000e0ba1481004010321130280690058200d1500030300e1800c180e010009140180750003c3c0600d541d8185414681e0300441c210b40003541d12850600c0785107444c130142d48008200d00180800321b601e03400d000e25401c0c1b00e14105c0011541c0002480e20039070030207800542c190881c04d4212401a420000480840c089404c1000c0b42c140c040010044c881100d003040080e00c0f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 52119671 1250 52118421 52118497
    0x9060504030c030204020d020714030a030b040b100f030605040c02030d05091203010b0c150703020c0f0d0903140304030c1509050d020904030f031508071d0f0106080a11 74
    0x40824042031000410750b4208100b100d8040701d02580380c0b4244500e0000921031a28000c2a814a1180e407042c030000102c064040303480191000c00c0144042018002500e10456020340d01041d5085030b45d045601642d1000c00f05015494001180f41d242c4c004201110210081c01d0050380c0040740751550714290b0300415910a506002500d00f0366030881c13084489001c1070003002e0185c0380c04980340004500030003004035485191181c2980605000102400940c002c18200e2517901400c3e9072040c000301d000589191034a0180d860001039403540d11a0003000745078000148480c00100300c00404140e20044000103408003107450752401c0c0c0705540140006c3c0181c5e104074010f40540e60340c0009a61074401203a072290309410440030f440c0f9021000c40060a844642c15000200740304041030200300012241c0a482c42d040c40204030000001c80081206412621650701c08001350042c8000e034421059250408240d00c8003040e0b80354810303007200054201d0404d40101c00d0131003129105220b480e4044144030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 52120921 1250 52119671 52119677
    0x1005092505010e0d03141201090b0901050306061306050d08030106200a06090317151201020c030307030b030a051f05011512020f0c1006050907050309070e06060408100506010906 78
    0x9034500740018100ca6940000a0f102d910a04500d00906008040d00f0010f1500711080590310342e107841c1c01044c1c0301c800f07000b9075040600d000d09081e0f644c2002c0f007506058030001001030149079144020018514500e400b440080c42d128000010203481704260303002090711031a50a40c0342d60400e4001000c045a1000e5014400c1d00030301c15403084280420fa100e13026030000030128000803541070646c1c5901c40c0541c4c0081d14207003101008407228010303005103420b21084480300d5a501921a33154241d001d040015107098100f040400e10302d600952081100312400342c15250102401e80340d16052143c0f145070301e00d09041c0031600d03a0001003544101405403005888210f030031981c1070320080850210741e003c0320100340c0c002400f060503060b8030180c43c0c4410003034044640c0d90f25425400c0015024a1107413a01994001d404030b404075000d20705582c070500f1900b005000d080d02d040b9140c4403043c0c01500d1590095410840403840d110140194a08032842c04008107950514030001418901d16611100c20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 52122171 1250 52120921 52120993
    0x102040e0609130807020402070602161a0703060e060603060a0b030c030604050c0703020a12021204090b040b0402040803031504020d020d0e0d05040605040b0304081201030b07110118060e100509 85
    0x103121407051742c03510364054074010b0305c0d080301d840e201d0003d120302c1d00d642408544201c3c03c1800c014403080200044d40f0744081d00041307900d0b80e800c150244c400b1130040f4075068140100003011414224043c5501100040500c40e501c0d0303680d080d1424641c4103484419031084000200402400d1600407190032907455007000c1c3c42c1442d00d4800948038402c2c090010009034150501451a500c00c002c03101c4a14060440f00c2d41d640d40d02e941d03040050001c4030f00d603400f442c10455000c1c81e40c6481d1081d40d0481d42c5540c040c6140d0743cac680d50401c01c0c1000d84066264010350038010046680d490b4400b40c0100c120031200028130148280340d41e4640000d15138120304215080006029403544030b0162002c07504450b650b913489032940e1400c16001c2c0500001b240444540c00000030030300c0080d034500c900869003512035844591b000042a402d03908140c0b1100030305912020b01c28001a1942d22400118410714241c0300013444441004058400554656000e540300f14140c55442105441c0d5071310102540c030200403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 52123421 1250 52122171 52122173
    0x30a0c050a0e040f0e070b0c0c030721050a0b0a05010509090607090501110f0d031508030f090d0807020d0b15031b010c0f0b090a03030f0209090a0b030703050102040e060913 76
    0x803403114096689070140c2e843c1e011011002e000d6030403407171502280200352540c29855582008450b0000d12070b00c40395104a042d00b024906010881d6002c0c0c034110164102c5004400b0111243e22a500800325100d1041c8084a404155a41d0286000d00c1e01042d000c03c10b545400200441e01901a02da0382d0306400482c1440301540d00f1120a41c1254020300b8040c4c0c852809551403410035029214150140c00380c41210b04002e0743c035030f005031001800052040d0b011a00c42030059528000c111005c6803d0004211268240ca85180c0d184091031041804c903190003060b5011408010801c181180e90305401c5c028003007009200311881040d02c6040c3d005160103130209442d8a800290403510906000d80c2004007000e00caa840340007074245412415420481c02d0030b04800da502c03076565500b6000603281c07001c0080e15110034002c6034aa4080201980c08a4684201e544000c0010452040d490304c280400007002031401e0001d000103181c52891211140f4000c824801810340040c8140d0805002151000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 52124671 1250 52123421 52123427
    0x50f2802011a040519150603140f220210030507020105010923130203031204020a0e0405031819030309030605011d0c0310030c030506160201020a020a03030b0301060506030408030a0c050a 82
    0x1040b004011280810151180a00c0d5511003550f1001000c4003400c106114210104d0840500c0407111141d40c10070503c842d421148800c4030b400d0302c1c80c039228401940070880e500d00c1400d01599400d1039240641600308207a001510710401d0380c001101094076076007000312a036020b2142c10300401603a4814032008241101da84441c0c00a60300030900342c9100000709004925409000f000345034050116aa01c14417542489081c00044804074030030303c00e96601149103a40713280b0070360003a50300200031400c00b01000070225001c1d1074141d0007034204034488007400c4484006c2941c50300860081c2c0310050520708608040c426100e05030000c0c128003841102807a1040c1c12011810380c1300480d804165202c0e03c0f2148550071089180c2d10150400c000020088180040820340e140180402c4c440701031000b40841c070980c243d000e6902d1100158000340c0c03031040400e0081d0424100c1c8030001703000180c11178403440081c1041e0000c1d80c0503154031101100300f00f03c500903072195031404859401d1003070929110300307001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 52125921 1250 52124671 52124711
    0x1090606050f250c030507060e1008071206060924021c03060503030a0306080d0c02010807050a030f0c05090a0e0903030103080711040516030b0d0c0e0403050f280201 73
    0x2180c800001040c6050f03801c00058441c10032040c41c1040c20a910720304203108085035a00081d2482d004540700040c07483d0090300340c504003120107803010300c003103c8030081a605d40d07500415030400d0044001c40340c000a0100d1240d0070182402c1d440360960503041000800d114010303004403c122001c888400450140c00103803c0341300380f00c0d1148000c041801100103e0113858158042901440003186c0e202c800c0d905908200c00740c8100c2400c07221415110f035130468807001080d0020340031968040208500a03c04c80013001a000369007008203600400003d40c03000c44100301c170300f5400220003080c2c1e9143e07488c10440810050480c80c00140740340c02c000d06043c3d120320040c807008000c8240050100f08220031850002d5001c40d00600410036498030580e103034000950070486800003881c1c54900e402d60702c1d200400183c100e404c04c0b141c2000327034149624801c40350b070044c00030b400b84034003031001c0d1284280220060100620801080b01070100c000000d09403c40712994080559040501000d501000e003800b0f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 52127171 1250 52125921 52125937
    0x3060604091e020403030f0e06130e06030c0616030801080601080606090601030b03060702010b0415060c06020a030905160503070b03010b09190801181b0303020a0807020f06030109140109060605 85
    0x340d000b49500c036050300d9244071250380d0105001180000c03c0c1078001c04240f401d6401358540415030030386c020800c4520f03c2480051900754440520034032205890910306a84640d01070300b2034403440c0311000081c0f00c903000555000129801c0c0c44410080650014900c0d0062412800420b09035040a20850316904024412401003000600003142a0310a4008200343c0001406171051401c0120000b1b01805428112a004500380300d106c50f4100312120b102402c0b00c1940d074070242a503070315079200e0010354030110018007010345401c054400300d00306010b06000c41001c0c1c429448014a0182131505045495014180b0441c0038401000101d081000311141d204013110890a070b0000710006003c0d5115039003240603151b103000401c000b0360b8034180c92010402d0003000d4501d20001c0101e840d09100c03c040c0402001a0002200710001420501c080e11308948010000410701c20aa00491441c0e0400d0b40400315454581400042604a0300000c5c6c0c050304064106115040c2070000250a0f4490864 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 52128421 1250 52127171 52127189
    0x20117070504030209071805010e062a0105010b040303110606010807110f01020a030e0106090b010c1b0504020307030203160c0503041a04050306011202010f02030a081602030c0a050f011103060604 86
    0x80000d54191080d0200d8010316401080c0c1c40b00da0401c2d00009003007503100c514890500044407004203d640c0107041e02800c800004140900e400e01410301010035805070028220103d1000a04442d403080a005040c06004200400c40d140c070300e5801c0040031500c03100851031094006030180305260360710070015030740801c8608201542018254107140340500708103036170205510220701010038682c940c006491041c5100f0080c00700d541c07106d09003402c50341003440c500c1c0482c1c070410784a000a24422110009104910030020f004c030782d203402143c140c0e842152a035000960000801900c480b5102843d02c3c02c01e010b00d0300186c600415582c1075500c0c4214024001901551020003901343e4000003250301500001e02a0744855a5842901200c5103070075004a02045c1c4510084104070310010654007000300c10340c0e4825483c2c41e10b05d080741070401d41c002045c04502003003101d06402e0300100216100b60344038200400104440c5102c4501b1940c52400c1505d600b00100140a51a56501e09807401c1d200560 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 52129671 1250 52128421 52128467
    0xa0c08060f0a0b031b18010303030516020102180103050702030c0111030708090d0e040b030c030f0c040c050f2a0102130905010f05150c0f07060c0309140105161e061d0a0201 76
    0x400003600e400c1d0042e401c046c03151400000402010790507004640203425004401c0551007000c002a801c0c0d020721204488590500b0a004400751311036042207030031038a2401038a14105441c9851402d4414400c0340d21020107000092045440d800b420055015040c24094a040840304200401d00c1d8251070019200e19111001c980d4166070505c4442d031091001000c60340340aa08120f81525201c4180e00c2e613203d00c0c07500e07078101c0307003180600100d03038003402800200d03072900100c08843c0c0d14011003456644c03000c100c21003205020010920082040b004111032720102180b03000c6440040d41d01c141c000a180410000c0f082061b902c882e1030040c054042e841c81c8688928a004941c2d240c1040c030015448984910340300011402e0304101c081076082d0007651804001c40c5c40f00e14610501b4140c030656400588208010041074600484c481c1050b03105491011445003042d91681081e086a078080d1a00c40c0c0d202d02100c2401d140d0581c00c2e04915810010304820001d940020745004881c2040101501c0e44e6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 52130921 1250 52129671 52129723
    0x80a03080c090a08010906050c03090715020109060203070507060c030e120c150f0405010605010c020a050d060f1b030b0f0f0909070b0a030203070e0a1a0c0a0c08060f0a0b03 76
    0xc08251002c180c805403150300c12956414500d40600f81c885026115145040e02090012460780d003142d106000300700080959610b0b1812001180642480402c01c65699480704c80c0000c095000a5000b200503944564031013005040403001c07a085030841c3e00a2500d800038090440340c0c003151600802070100580c50b154040520703120700b001d80c3c000000344418150010000c94040e01405075010314000d030005c0203c1c80d103032401914103505841000e5030000b0040070810251a01b10007071011241300d030780041417000350b80d2015422f070740c0c25690180031261010742003000180c0c144100042d2500480b00f82d048440c00d0341c041130380c480400c0d0300350f40580b400e6000075140300820000170b001400311103103503a650700090b00000d000390000e881c1c440001c2d8400020401d146440d401207402d4a45940c464005c140f69012800c0721a03001d0340500f000790085207424070200358003103c5d80004094903c050005440d0a420520003c40010b290101e1945800b16a903c503407400121001d280102411880c00d0b0f0b151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 52132171 1250 52130921 52130941
    0x70c170f090910170d230903010606051e030c07020d0212060c0304062a1211040b03010905010f290403060e010b010e0105090f0d021810060e0109080a0308 68
    0x100110746411100e403109010100703c00000c880215903000410121403800c881500307842d078074680f4519001a0140c0041c06c0c0c2401e00f500c1c401007501c8564542071400303c05002103800d4580300d038000000b046021030901c4007462986462035440e40120741152461a10401d400b0140c0242c46000c2e014151000c141403c544900201442e000706041c00ca0380b2510302010780c0d000d2a0310440302261901c7c108440c8242124034006240c82c050980061400d070112210412145000d500d1440e126540c2c550340303940615a40600104043c050384128642e0341e40c1001440c00980c1c074180e100032503040c10ba12040000412100c84000c0302c01c840d81c240c113100400401108540e00841e040a0031603441c00360780300c5450798154400c82e281c0c0c42c280c132111540388003080151564001c212440f0340000904825030414949001550001840140410009210200c50129080c1e00b151031100e14012014180f000c1600080070034070034102440d00c0a07060341800ca0054403000450002405e001d00d1030046005098 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 52133421 1250 52132171 52132177
    0x1b0608041101170a0501060f05090d02010305060319030206060307081207030f122306190b091201020a090e061c060f09060c090e0a021207050c010e06130b070c170f 72
    0x2070f04248881e0385081c8000302e400201800e220b007030302040074071119105041c00b44003031b19a111001444e0340c0456019400550141c00028200c0f985030060055a582420745412441c21040c041da00808a92130584281868407685812a1407154004941500f0024184049691107941442d12215107810b18805451012070010b003509107900b0f0003610120380400d22003e080740c83e500c0c04002c607075031140814058410400b0f00b045c1542c0c000c048003030041400c510014900048003626040e510282500c0250882e00805050400102410070402110660004050b041602101c1c4096007061040030303902c02c128400c41c000c2401c0d07201c648244030000143d005280090308940306119045503000000d051400310f00403001c0310000b8030042490100e6034402c1d43c1203251600c04d1021244c03070f88074095410b5084400080d0b40c0b507403200d400c0b45100c0c03000d00c0000d0203078100c8198100f181040f481c0840c40010020701503010480f51906000c003144900303c0039011302c400b10152507a1104010300b0b5540d030b44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 52134671 1250 52133421 52133447
    0x924030121020a0b0d050709050109060309030507021c051002090f01080402030c0a150207080f101e0f020901030b0102030304051b011215050f06040b09010e0103020c0a030801031b0608041101 84
    0x450110b0340040c04070400f0004004008100600f00100d544d0a01f060301c000c10140100340c0002c01c0c004092007030314000e5014460190080c2011800c1000e0307a070000c0c100da20700e0061450f03445ca01e11200d000300b04042042c0c244109100e0390550801410314040b130140314581c0300c42e9041200b002d01080c15900c007841107030f100b41c0c1c0140850040c03a03107410104100a69181105005109003040000c8018003c070310290040265000b8060074011444824040d011885240c80317454506403580c2c0400441c5d1240100c010901d041c056290724500c0e0000d421940b20100030b50641d0420000c0000080f0041000000c528800115080d08220a001210340c0c0c00d60100f002c0e00107291046200000c002d8136603400445100720790b0521225070302c5041c003400e80601d100b108003064040c44103856a6002e42c446100031030062400604040070310150380d1410107407000917070102c4c810070014401d001c615403d0031940c2c000039404400b19407518900800c0e000c8004c0c0017030440c00c2031300180c1403582e1203180091005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 52135921 1250 52134671 52134679
    0x30c0c1507082a121008010c050f0f040b0c0a030f03050601050d0509070b0c100507022b020c1309030e060f0a0c020301090204050f091504080d150302030d0203092403012102 76
    0x18003407030740813411408030a44008411140207000001c02c0c5405000c0d420044000e40e0703a50f82000c0020020003804d070803406809a400b03000b1710011412880d1013000c0e04803400801c1c001d18200c3e0302c1d404e0240808200104000401d030400d01000310998020007240c2120300105000107440c1d45451150b41016000d8118411021001441c65480080043c002c1001380c0ea50004000c241c0354420281ea035114001b0b13200c8111050700400200004c025224085041c69900540b04414802000100c24003000701103c0345c62a500c010010600d40d0040b0154003010098a00c0f45c582050410309680a0244580e0241080070040c0240d045417000c0d00002c024aa0290050040e400d000b00c008541e0a8200c51080b0148110082c10402c0c40030b803000180940d400c000200c2c23901d08031200100107002420109221482e54100000050710100444040c0746c406502454443c140401000a9050480c0e103004140005039140314003900808200e0b41103a4800440c001d28895140802094030040031001e540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 52137171 1250 52135921 52135927
    0x903010906020a030b12010e0c0d0519060e06070309051018080c070e0714090f03030c070e16020f07060503040f0b0a0203040b060103090b0c130b030c0c1507082a 71
    0x80780d4140d0010f172401c0c141103030303400d4400316070426490803180d600d02c040f0720590002e040101c1f5030404035001c4400c0e0b4014000d8582da24841e04100c28101034002c400c5a0700d039501c01c0845030030001030108075002002e83c5014402c0558507216035541e10b040d0403084207450f6036003408070003600f07143c40303490003407580401b009844240ca140c082d0b03201c0d0741c139109a0461140c00300c0043c00d800e00c11001c2d40348503003401e420603042684050034800c6420032203000c20b42610080100200003481080801d0003004603807403800d22440c08a48064080008060307020965219811103020f804003c40e03080140c4850749001500d0380e5940c1400d82e9070b01c60100014005446800c00d0202487c0aa0002c5108a0143c1c5a503406612500b004404450030040017414000342080460040d00e0080000c1c00c140e59000c0140701410740302d80e00202c581e40151174040b03603420b000481902652060050520030080d605401115280404e40139040d45030003800e05011052068100e01d99090151921407801008915907807 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 52138421 1250 52137171 52137187
    0x71d090903040e070203070c0909060905030c0c0a050a05090f070903140601050f010c05031207030b040606080108100608070902030703140a051b03060d24050c030a0e060705040308090301090602 85
    0x240720b0780301d0302401854240f5a000034801500000c11102050351081d50320075000d00d4941240e0092440107001c4403d1038030341d04100c01151040015181541039840a0700aa4a800382004101101603010314040c0551010402059464640c59039228410100614a0b999040b9040340d00c80d541d030700010a00300da043e054010500001036182c0c10b8540603150300740d500c0b001c1001511940e8580380d0080907176108001c0070781c40d4541c0c07043e215000b45039403e002c5207200211001406868103504140c0015103c0001049040020007413043c0d500c21000b420810142401c031410b4030380f0944c0c000c8524064000001c01e484d14807035403007220004a4003a410300c0c4c50601600c030801605050710007a42d161840a01e80f1a00090581140d000341c1004203d10503c504a5680c0d144200190030004400800400c100c0c80c0f01d00e45002e010301c030f1020100f1a5030341e441e2001410048960700f03245200540d06c00f10800c45c00e5a0040115815642c2100742c017920b8091581c006805030008680040103030b800410414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 52139671 1250 52138421 52138423
    0x203070308061504080f07090501050a05130b0405090a020901090e03040521010c030506030d1707030f02070203010204080a02090c19120f0608010b010f05030405060604111e18010206070206071d0909 87
    0xc1003040001c0a59a01f159030304a0901035030001e0190395440207070094204032910b8075400384082c01e046540085001c0d500071000900304c90040354070747e880d60881c01d054001c41c0f411844283c050405035004120940326503241c603036a40204d00031180618801e11541c0307601032811480b54540c070035206c003d00c05c421a40d9402405172500b5901207010b44a0b049100e0041809000342d03002c24000002c44240c2d551714550304030041d1051030081004c02c1c1c0c1c02c200e50000341e10280000c2c005804a0402040110745038070502c24007841c000c1242c0359401043c44540038075a003000076004266018a010030f4840325000444004045102d281c2041030b24005c000500140d041d0000014100241c0b42c110341f1541016054655120884000f040368001c440020043d16155004810720381c6849501800c00440c14400c401c0c00360360000c460020341002c10a000034440a0070a03807101102840904040d003041c3e240650b03145006811038081c042c5003401d6401909410807070866031403004226500605150303c0c12 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 52140921 1250 52139671 52139683
    0x15040809090c03070804062004030b09060105010c0b04020f06090d050d120218090c0403020604060c290a0e030c011104080708280503130603021206090601020307030806150408 77
    0x85000d010241d000500703030422030040d24807851003621060415601c981d01d101c003c1c00b0f801c1c001c80095801420000c3c410183c000074002441c400c03025500c1e907050207412280352250590007a410418920840d10000348846a01500268107132421109100d000c00003440038020003a12603009030b081218642401400a840401007a540d140c0041e0b486d07403900170005074400c2204880b02d05a60b0552221141840405c450780545600350b5641060303260740c00184960f2190340810005164040341f142842903011800419900081c1800c130003040b00340b446c5ca00100000c05012402c0e0382c4003c84a00c4480c1401200d03d0407201030020804d21001c3c580f15543e42c0c01a000d006101c1c410b009002c05c500500181c80e030045200310303140070340004540082c1003049150000c21a0180030501c003040703030103112081c0007000e0f14603900c0258072480c2c050b150f00340c4640020991032054107003400b48041c598001c41101c00140c0c140c0b401da04240d40384004902615143c240f82c889031040014005650000421a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 52142171 1250 52140921 52140937
    0xc1505040515030a0e01230c0415020d020f03040e0103080d0603050d2003030603120c010e07060305061c120c020604080d030c08010609050f09250306050102070501090f0e0702150408 80
    0x810084180c805d12a08030b40d41611302d20707541d41000100790f00b43c0d141c410082d940501070b241c0840c6441c0d244d40030361901040148451002d40e0100902f03080d070035014420140e44039198002941001e02d0801030b0b041c4802c043c03101600f40b070700c0015680000b2a180d00510040e60f0030030200ca4100c6503200c002086500035600307250030040004000c0c40d08103800710459014000090046c407000c60780c04500f20b0140e00010742c10301a596a10b0064451410500428000344066100042e503440d20005000342c4818101c1c00b543c1d20122628000c0005106803c1a8080c0e81d0768500f0221140c0e051010461a2003550844181c2d441921210f48006501d0341160002145596441c07015980e80e01d001c1d00e890000740981c40d404100d070701482000c0c1c200360480039404461401c034004014601c5501c8a4048110039000c000030b9180c520601041d6010400c0400801080c81e05030000f42c03802084028954440c0281130a078401c0c4404265483d10800c580940c2039443c02154110381001e00d800d58040c0d2000c80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 52143421 1250 52142171 52142191
    0x20d0c1809150209031f051b0a080705130b180114030c0904090602121305010e0705030304090c0c0804061d010302070525171e0304030c150504051503 66
    0x994020408902440d038400d94070198010b10410b4540c044406504502040e035018441d000b02e40003540d503e840e82c0c40302d0710401000002e0780d0621507403a0340002281c81c2019031280d81040100c9995600001c803a9210f012482e02c1c1781c860600d034a2140300701126500c08a5030002c08a2246001032805011035010003090300c9400001d401000303008000c0c001210060ac040f801484034400504054006618140c4154001031030700d48803841104a0130002c0e02da440c1c0021780140b00c48200402441407081899020004200a51802c00060780e1b0340f1490140c41a004d0305c4076284003005004000303040110750300c000c04a0310395444520007403910346580702e00e00290659010032030855009208640080e0b40000c003400e40080d18a1501c03841c2074038500c0311800b030420118000707400401c511001c0c00ca840340303d006e0310b4bc0c40389480143c00242005406004030360001c00081000401c3c4903002012248000003000d6004009141905e85004a90080e904001920400c8001d03100c0c03140114403d60040e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 52144671 1250 52143421 52143449
    0x3020303061207031703070c06020a021e0105130f020402070c0b0a02010f05010303050409020702031e010906050604141b0909010303030b01030e0a0b01090f0e03070c0e010e060901060f030207020d0c 87
    0x561800d079110b10500c0041c00d1041c0205d03042900f00d050400441d405030321410100051540707540e4030310484e4082c0b144e000050b040302880038448204c0c0703018001c402032084003d103c241003641117088118040c0000034803903d00c0d030300136808545031a0180c4001c55008100c00b4a080d40e5100c4800c403550080f81000015440c014066183c01014402e036810381c1c0d05562504d00700350810858900a50051f00160390620500311030307000311070150072034503194610301001041c80d400c0307031800c601a940d0103020140701b40e040c01038052410000c1c280455000c40000c203901c1107845448481c4510340b1481c0700c010342010002d030020051540640168628a0742a6070800c002d1101c3d030035840e100c0210710002000004d94100400407504c50b604440d8a0440e40c4800040790100c6407600e40c510780c050403003114140e02d007a07020030144c0c401d441c080b401801d216842c040e9a151520005072001d40c140103400034030160030101944a88a5070583c0c611070303070142034400f0305c080710304000903500407510805007520481 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 52145921 1250 52144671 52144699
    0x201110106030b1914071d150909190912081e0105010f0203091903050c090106020303070507030c120926070506070302120d0504020f100f0309030203160302030306 72
    0x140300744011a5040b05032404541c640d0860013040b05480401d5103103458650192441c0d4a540c02840c90203000382d52118498a00090443d120b14401c1ca80064410804486a1380c0b0441c40f81e800c550410704202d030800b40c9030780e96441d0288038a1107074241e100f01e145024401d40070004903c140b8401100d4944500d8403560f10f00b0a1100c150a403008034030640800d1800410441d401041300042d968140d005507030a00c600e81021a8041801104d02201c010300004100103000e0184440d03107484405480f07500c01503042c810040d590b071002034508810020700082f40f509061107402c2d81c00c05d041c3d10144d0580c141d04a01c2c2d0007400c0075640d001d1072050706905081000030300d5030301c0001201d0949100142c108185000c00304012030300054000d40650150f8aa450202040c8000528080101003400201030410f0300600a00c01014030b0b100740984500d5801001c551b4120801d4040c00702c042c034003c030761003506140480c20340c0281c1d4131040d40085941c0e10b4408064000c40076600c51402520712044400b55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 52147171 1250 52145921 52145923
    0x9090a09020f12030d020c0714090403080c0c0102040b070614011e0512010b090c070b10050901030b04060902060a02030406020c060f0406081003120503060f04200702010201090209040609020111 85
    0xd04029440440203400001d82e042c4801c41070146081441a02e00b41101032040100360313800320386031180b5074009031818400020003041c003078204071080d5150306891611b0750300074080d0807000c1c0540c0e074540c40109082d0100c41c425011034001d07001e6000b510751600c900346450340150400901740300042c500c260020900401e20003802944039000000c2003c03444c0740800384109200f080801001139501d075908000e068540c405c6c2c0c2d43c000d00740000880c0d5501c101d41401c050302c441c00303002c1c4034004020920400c0b059884c4507040b415a504900154840d0300c40e4a0a540104000c690082d00030340042044150a40c0110207001180d50a40a540410702c081c410803200d8481c03403000341540d0b4010b00c024001d043c0701c3e80005034403c01207031302c0180c0c00ba22a102c2594440324003118900041c80002004120b00300f0700c82403a0180020f480903c40550001d1607030f0103001070075452000000700885c80070309581c401d401c145e5209030058004c40d81c1b07090504025001d800311a00c1a8042039404103410302c1024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 52148421 1250 52147171 52147181
    0x11010506030706140903070b0c0f0609060406021b070306020408071410030b0102120705010504150c020c10090f12020306071103220e1005010e0f06040e10150509090a 73
    0x2401030280940e181086070030b980030752130a1030703541d12000140400803294130b08000c014050841360000648032001c60b0341440c54908642003811003078220009001c9000c4000608a070800d9000f40c1c0503031a104180079800c031215040c0c80d48a00341c402c1010006c1801019402401603641792402d50b0b20342074a81e10101010500a00c0c400d4001c0c2a0310800038000c0e20a50045101400501c150b46941c43d0130385a161a581002105803600c3c0d5598090108100e070030010f00d50200e94409091201201401c0040c1d00d987c0504003090180c40032800c914150b61041c98000c000e000280346080c640e82c0c5450240c800c10b254000b04034024411500031520150040c4800c81003400800000c1d03140111000b080d60b80d0221142c02a4550b2403040d0300802c01c140c5510080e0710074001c21100383d0b5142c0c03811000604840550078058022001d07440e20004e991104400c03281529030300b001d0751a090300c44c410240c8a03910154001429903d0384103403041c0c501c0e0300c40001c00d10030750204d65000c1a0389505d0810b45c2125 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 52149671 1250 52148421 52148431
    0x212150a0501020a0803130807061e090201020a12090f090e010b09010e15030a0803070509010201141006201603060605060f04060c020117160801081b0603040501020d020415110105 79
    0xc1e03c1208a01e0004141d00c00455000e01c1f0065030f1340c103d87c0280d5072401160050328048404c2622908200042106001100c0e00240d400390244030340c3e1540d80010303444000c1d400c00940501c246805203150f05000700109001000700e0036201e940700e99141091401020125074128182d401c019542d01c01d440c1504401d03040c0c810790402ca5100d0f845005800306c400100744042d54143c00350003904408101410080c5100300085d0b19031076270b14103050000a003140c0101036000788005529080c040c205034000390004c1503402d6420500030400740d0611040e08041081015119031141c03084403044007035400213400c202d80c030449090050075191801c11076640103500000c001c80c0401d02080060070320941c42003032440d006051507007030920f500340340440c1c200045a510407080040028034010300e510004643c01000f10030013410809000e000515240820044250300c04c1c00048042024000c1c00e5040302e6029058010855450350f850b00a040d03840080d040c9840030136203170310506240d410b042c05158821 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 52150921 1250 52149671 52149673
    0x1502060105011808070605070506070f05090d03030b03030408010213090b0f04051e09030901140708040e070210050f0a0b0301140a0f150801050615070308070c0609060212150a050102 80
    0x581e00308001115041d9019000c20f001d0b1031507010000701c1c039000380596000f034103095841c6952400603082c03c2d89001e5000c1c062004003c082505410078540c05002e840800c441102c09950303006540c02e08030084c20024820541c9800002800103a4880c154020325a40250885212106a9030040042115041c8040942003c41d412302c2c0e01032854164007640d4402d0684045009c148038210303480c902e45004031104030041c0d0000660078071a40e00320740a4050b03008400021890000350359907294903030185128802c0364000f840c0219400c1030003032103180c3c021020701c0010003030743c170b4124144000c5100c2510100452407400c2004100b43c20103020b02c08103502d16082111090b1240c0c3c0c10f110080018420f900641a5260380300000c007000c010700c4100a040d02c0002040314100380007049072403034800700d800e0904074003085031000094100001d543d200312607050140d12542c2606000e0058031000b84001d0442e4070005003040c03d43c040200b0f150003800c0c409030201c0c6a43c80d40040c000c0e5140c05008040c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 52152171 1250 52150921 52150933
    0x206090a030305042a140f1c0501020405030f07050906010503040f110609030727050402090a05040204021309090c080111090411190210050603010b010507080904060f0605040f1502 79
    0x402d0080e00160303081403041002c1c40a48040140e0030064924001000c01c20705e1110f0010054515000407950322040304a40046d4000203990004440030400f200d05003850b500c2c040c02c1c41c180b00d002e606680040074042c094030100207040540d00d8841146010340e601c0351a08001041d4154440e4080e684030f20341c0000b5042a1070b1854807902404405040072552002041207038110640302401900c00402a59042481401107030385c250440e00c0c415101c03008524900010031016030348241c40141c000528200014584d195070000c20007030f01c00c035014140b8044814200045d54441a846a0103040c0600c410310480fa40758282d59003a11070042ca4011081800d1181d2001441c10703900000d08042025022460b07e084c054602c2115030444800902503006542181e1000b125802a035a2110b0300318000c100c04121000040c226010b9800040c003903400104240b40c40d900d490784203c019021454440e219680d4401c4001c006a1180c0030b0801c035209141000034a11028400e10340c0780315440e80117450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 52153421 1250 52152171 52152173
    0x1080604020309070302030d020d031a0114030c120f041109101707030221061008071202011b050f15090c19090c02070f0501170f060f0303030f07020105070206090a 72
    0x180d0400f8002c094680244d03600040140c0e01000001500040c81d0003401c64241804d40140c112810001c44003c500b000032002045aa400015148802c0f880c200081d04c0751140b1104124034014030f9040381c0b4201064080c04180c0300b240c100ca604c600d1081d100907511440c14018000b0001066030342e41e1a03010000000d0060701070421044d0714105036081140c0c8020b85e203030002208010f11030701a2150112000d5215601c281c240480c55004031001c0b0004142443c0440465031904603210313036250b001440740030408580c0708000c0342c0100003443c105804180450304005840784e05010072051107100701c03100e0150001d0b200314030510030880d0360043c3c00b81d852203c0602c0485104045501c0c001c1003103000c08038002d43d1900c05c04241d12000e5004000a90502ca10514105595000309043c01100c5030b0341c6400c0d01900041941c8010303107104801242c0c035500c01165411102d0542c040d4140004800c0180440d031640f01140709000303940c001c4c05103407912a016a1614020341c0c900829802c076400c0c1c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 52154671 1250 52153421 52153429
    0x4030507021c0b01140d0209040602130f030302070603020f400324150609150305010e070c02130c080f100605041202030703020a0b09030d141c1104180e010605010806 73
    0x400e00c080203451b003114200b01c1c1e40090180c038000c60303003152100c1c0e001c070346000019404503e03100500101d6041448150454030302942c3d81c8564030030981016000600c1c01c0100026505803a1018841c850504034070f4000c00c50188940c1c00701076458201650a8890046413000d88002411603411521403503502c00c0d02e000b82d510480b03051003141c0c511511240f1f11909122403c5d5010000c10481d9180c3c4140f03810483e10f400c5820040c640e6404040c1003100510981e20720007040c5410100e00d0030004030fa41d101c1e00c0420415545810340c0022985415005094103401ca40c185106090201681d0b1059403404d41c03018915040703006050025000703010504c40b20040b04000b800003400101103802c0d1035626400a81d00780e0044e0041110880049200c0343e40d030808100ca08651517041c14510558070704500011880e00680c05070310502248100c00c210320030900d5100c0201c1413045011207582e142c850f4402000b008010114100141c80d065990000c4032042c4210700030744005956425054850307001704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 52155921 1250 52154671 52154699
    0xb031204170106051801091103040b01050d020d02030d03020901030e0715080705040e0115030c0207080c060a0314070206061c0b0106050d0b0409050d021009120311040e04030507021c0b01 82
    0x10004540d6144804961a41d0740303e1039140702201e03451080302d10742c108001d00050380c10b00c23481d07400802410300622000030380241c54141541c209644030401c0c80700500000d60b20f07102c4410040d415016400342c00c40b0707165040c3c004064021080e241400b4900600d80002c0c1c0e03400040c0302c0c0d41540c10040100b500c0182c0708144030303a0458078030300d003c60420751903000b41a040802030384482300c00b0f12072200b401e002603054010940c188500d8006444218540081075840c6c0c180343c0c8800e440362100050b440083da002c0c8d405940a4161600154030700e28100034041e554030701c1616150b2041035a6010002c80d0040c484030321200700e511251360031042c0d180c01400c0c2c9032a003290003079401030340c1c03110403400c03490315548100800c4500540003040c03403001004019003002401015618020b0034180c1c803002007140301080350300d1120b061400241c0320545026511250080c0d070842211000c0c003105020902d0340c0503001c0d04101d0f000301c42d07000304072890007111801d0550781036009016640040c0100850003a141c08 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 52157171 1250 52155921 52155959
    0x12060621020a140d0504060c0e03121e03040c1a1c0f020c0f0604030305060402070b01051003092405010e070804020103090201020c030a0804090f02070203060c0711060403080d0b031204 81
    0x12801003e000c40c0c03180c8116812000d00114500d07540d20420007440018001e605898881d1701300821103060150204e41c4480b82d10054050f010000a5081c80007101501c1480600308002100ca84038105072030401c031035101c07034400e0306513840300030000900c514000c60407184403903038038520040036007e02c80b2031030080c3c40f9036000803d45940c240201007040b0300600480c0c03000c040c10005060949024038000e011582e0203050a4020703441032110f00000b548484011341501c05c02c954440040107442d40c1100030740101c0c0ba00034440d0408d411403024005e408941a9418a02100140560703a02e40c030b951030350040212410070000760b0030000314000d54041d80c0a109064010320507070f52042d80041c007192400720910030448510200280410000707042c6e128010381d03608454000c0d89807020076000030303964080203002c022800400081c1c000030015109824051030310b0280800d41c60f90760342c4c240300c0d01d150410280d034451203040140481540c80e010800701d4405445e0a44141042d080a000ba0264008014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 52158277 1106 52157171 52157177
    0x30d020f0a02042a020304030302010c020a02010f110a0606060207050307091407120204090f0b1c02010f12021b0d14130509041104090312060621020a 66
    0x5400000950101c60224020294180d884200400c011003d0400319010300d0003818a17130007101a1085034002c1c1c008020701000340109903161214800001d000807038044003003841c180111040103103009a002102e0024860780e031010b04581c01c603008a009684400c404000c07914082001c9400f6140c5000144140000301054809828000d40984140300440f58119200c0444e80e069400500700450140700c0b034041c041001c401001c04088450041101095550301e50451680c0b00401503030680d01c488865a21000440d004507101c400c10000c25000c00031511900c04130f03480d074148020981302420720541c1812000c4c0034221417000c1008201c01c148051018012415001c50407030b84142d5120040d0350ba0351528042c02c00d04960055482890180d119050651020011000264005040144a84500302603400c200000410500600142c003204595800c40e0040d000c04e0301141 = true := by decide +kernel

theorem cover : BRFrame.Cov 51978421 52158277 := by
  have h0 := BRFrame.cov_init 51978421
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51978421 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51978421 ≤ n) (h2 : n < 52158277) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
