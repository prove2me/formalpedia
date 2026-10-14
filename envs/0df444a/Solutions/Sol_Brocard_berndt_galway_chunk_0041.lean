-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0041
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:31:17.20589+00:00
-- url     : https://prove2.me/submissions/3bef8fa7-7ef7-446f-984e-9ac2ff6229fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7194252 ≤ n < 7374108 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7195502 1250 7194252 7194269
    0x60a03020301062309040b0d06090c06020f060c07030305070507050601030b0105010f0e0d0303051b040e06011103040807120201050409020a08040c050d0b0604020c010b060406120612110d0303021b030408120304030c08090a 97
    0x40145081c800045040000c8a620b80c0c01c4032200400706001d10b440e443f007910100b040103c1403040a0000e03001c3e40006900c16000e251050a00780c241c0c8502d89820b5003a8070942e0064039110050043e542e00c0b6811005e404e0803800d06071050300c1c144004c658a004150b1000c1d00b0190b1300d5000c81c0681d1407202048000030804100d0035161600d448400300b0740842610450b0104401e0071088034150300100950701140c40c070714080d041d80c915000ac03240302da842012040781086400c000100b41520a4400350804c0140341d91a803829180525002c1c100c5103094000c070b0712440d2100240c0c0e001640592a06a010405542c05031301d41005950407409000344180341c9a1000c004240891016071024000c105031540000510099950b100c4481d280c017800b4030007500d5103084072824255410601c5060160764440c0c6001441c0441c40b00140c1100f074680d208900250b007001608000c41d003800c0000b1511056001005451410560303000f03000046401d000926945e4081460a203070303502c505010b0020a40304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7196752 1250 7195502 7195511
    0x621070b070b0f150303030103060207060b040e060411010519120204030209010602030703030f05040305090907020709050c0406140c0601060f020705030d05190c08090f030c060a03020301062309040b0d06 89
    0x40c030b811894040c04840700c000c1040030074001080c0010303000c0d0030030404c100907014502d140d0071612070708080c0d4441d24041c2c0311192160744c011003c0c0c56030302c0743d12000078000024202d141807600d00080780c410707030712142410018140190181340d005a841010503002c1c500307040c078010010304100000b90043d41d2029501c031070b15900000301190040020000f10303200740d9041085203107043d5010100c901c191805400030300705000d40e64150610004107a0440301c580110b8009540d2750480c1801d941080f19258a0860702042c1040b82036004012101ca2201380c05043c1d007030000e04150250345180c14440e41080041c019101e91070903000344400b20182070007405032a03400f0741e4180054a1540950049902250040460a5818810f42c010140030b940040d89514012003c010801c03150079441c282c80d030600038150040c025640c2c190040c602e02404c0d4402680308d40c0340541c00b0b40400c828019041007012000c040490075240901159451038088a00141e010001c0700420008c070345402d03000f8010740c9070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7198002 1250 7196752 7196767
    0x105040c050d030c020d12080c0403080706090305070c03050106140301180f17030906070e0105071203020c0106090203011202120706020c100306230406060306050906040504020409021305100605030621070b 90
    0x6003062904987d5196501d013900e590340c03070f10100e01c210300c0b0190200c582400440000f6030aa0040042a8007078940142004195122403c050300b95034001c594581d0f540d1010804090708500007040b40101710020003149d00c00303100c0030300920614840101040c5a1400620421060340302004202c01070b051040d80b2032500380850b940c0c0340d10907644000820084e40c10880380b588124126145c6c6540041c00850701051040140c1c06504500001da002355220720000c03800d082c191020b9030003041a2100d54840c088940140004512051780b01406904100424420303c2c0e0000341302c5258a00540e02c0f501e6440c180c410841c01402c680d0003a846284942d40c2c0d44100c8821809000c1074a4402c40f420801c10780e8403034080e01260b08034032819800c00482800034940d442d0540c00310303a019002800c081081181d5a001039207000c1c0d0024038403440381d500d40500000c2040100c101c0c000d00f0030340c14824a5801c224000910003000ba840c0008804036540c043e0340d10480030321001000309000281e46d61500c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7199252 1250 7198002 7198013
    0x21c0201150b0705030a11010209060703030605040501050609031b01050702101101060806190e010b0d0b0406060504050408071401110c010911030703170a03020f070c06030b030105040c050d030c020d 87
    0x1e00300040880c0c200030312408a9401c5145080b9080d46038460015890810654025160012054030018180d582809104842d413a84001406064881d5a0020f141400c0000b040101c90741a00454040c1006003c42c691540300000c3c8001d9401d400301c49006007042080040b0f40f82c1c450100c0c02500705080e000ba140f4469001208103410703540401c001d001d078a4544444a503036540842e0b03503444500c504074558814042a6210101541d51a00041214411140401ea020f2044081162041004800c0100b44003151080801800e001c98013400b4500381900e40011602452801402c250042e2090207074a003000d5004200400c41d09010359210040500f000b4000d1102d00300a0703c0d41c280c031151041c2d0614011a044050700e40c40741000f11140e51405020580d6040240b1200a00d0350801100944141e000003a1140e144121060113426040030717002000c0d1100200d400d030007681000705100005010031039040c00d40d4401e95800071801120b0a00308c03084403401d0f5020750041d06500d4070340140032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7200502 1250 7199252 7199261
    0x60907080115080705190503010f0203090607080411060a11030307020d02070806010302010203030406020f0706050a020c0706020a081912050114040b0d020114090105040b03090109020a080304030c06030b0604260105010501030209030303010510021c0201 110
    0x1c43e9093b02c1c0e440e980c8800586e01d00000701c0c0c005201108042940b015072500c0c1c8050050100d03140b03084840c0c11000d00c1c00c1840d40c0d106662540161744401c45084210350304214450250400e0303c050800365242d81e0020355207000280000f40001c0c0c012904014180011041d1042d4580050f4240294104a440d20f0002c4d804a04c50700300c81e0041e0304001c50f00f9400040c03003081940d440300e1501d1410805c4c28000c405600c2c0c0c034658100b00014900e04410701034440c02101e002c1d10020103c1c40c00911a10100310854201001850140810384c40070340241c0e80001d1000040f9910815550ba620513600040391a48199003144482e00000f10510078000c005610061216100345c804005d0366881d250221342d00e0040d03100062100b07585090600040d40b0a030446406080c020305094103007030703d40c21001c1d80b100c82d10f10250440707443d420050110315000d00038540102001e08045140c600c00c00040fa4030ba100500a03607006841400c0c545504520070081140444c40e41c0041c038001d440700e080000d0192 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7201752 1250 7200502 7200511
    0x10504110415050105070b06010201061203020d020610150e01022103160509060d020d0b1002030c070501030e07060318061107050705010e1305041103060907080115080705190503010f0203 82
    0x12494407070351a160602e40d000750400c2d10416107942e810700031295141018408010004c5046549640780041c00804021210041c40e1080d0040c2c1100c00d0865070007464514020a110480300c180c90301041100d81220540d52401c1440c60100200c0030b4070740c0140c1c90a2031070240c894a904a02c20324440b010702402c050350041e00d07070041050601000c010700f148c0900428455070740c03000d010400c1e080d1000d01907000705040b8100034804918514038600041c2d001d0311900c1140056080060525a0640d06200032001791009080410a900780b0041d41d40d82c44445000387d400f030540d030325550700408203041c4519520560241c0700380440307a1034447c408007942050000b101c5a100398140460307250700a46030032032600c4000e003035441c0c0721410123060805032101030819514a00311518614980d00c00f84030030751041031a00b0041c05070a01c0c1441b02c41c2124030340c2c102800b152458003828070048802160120032150100d401c02c2a40300f0803030016198212a90207184c5c0356203841100707400360280d60040c6126 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7203002 1250 7201752 7201759
    0x901090c090207120c11040216051516030905070504050106030b0109091812030212070206100501140706020919090c0e09060a03080a02010f02070605010305070b04180203070c0501050411 82
    0x40d03903481d48842603000f2440c1c01460a0403151000100510503842d403101240210200e00c844131140d0040380490303002c0200741e90b008699640c00001d0180030400c03181d0400b034202100315a4604a204001040b94501e40c0f41c041684418441c0284401004140c01810000b401004039580d244009001014035020340c502003602100005100c50051141e5002024008048000c2e80490307500c03c00314102034144c3c24240340c2c1c284149034142092100c914821501500188070904203c1510a00e400d240d0340120f04101d0b810240140d010340d503206540705558464809070700d5480c0b5000041400201c0a1030b031503240380c10741c0f001582c0a00c0342c201515800381c1da00ca5110044a800c2800210401103c6054214425401c208000356506008040c8250300c1e2000080f100501440d10701031b0b92101d80c4c16542240c5544c014414400103001c20001000d0002c0040d14080c50040d1405601803e10211800315074044001003500d4041e8540c138841c0ca9004000b0440c070f00c0c091425007410140a5540c601 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7204252 1250 7203002 7203023
    0x1a0316050301051e04020d08070503070c090509010902030c090603010608060702010c030614010e0d021504030809100201020705150903040306050103030f02010b01030b060702040b0d020d08030103031103120118060806090109 98
    0x12104801644c01e0703110350960f018207a96036413a000d000e141c00d0520000c881d0800104603402c0811014005030030154418030103004540c0c81c140404081c0d4802802c0e8a40c90f0345015042e10040e5800213000440718405c1d43c41580d15551140064010704082e03000d80280e008a404101c3c8599040d030092001c02c1481c0c03010400140c0f545c07030700543c08c22a020010302107903a01c12080207500d4112102c80c007180c4010407d40e00c030003800c00804110340260707108072056031011420396078500e040050900c00310114802181084000d4440540c0c500160b24030341c550710300d003c001c107840610610031580a5a0880c7c2c0901282d40d6034500240b6a040981008006510708038150000b503119000780c1040c0d4200030585030411aa940801004000140003542e01880c082110001611168846508070740950140d98903585541070240994103404000900750300f0030883c03910105110750055054803403201c0d40a01446080604800402440c1c105031064850b10003000f0618005400048032548541045030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7205502 1250 7204252 7204261
    0x105070c03080c1b0d050403020103061e030f05070302040218040c090e01150513030b01030b0f0103020901030605040503090a0311012601050f061204030203030f16020a061a031605030105 82
    0x4034030000302140140000c0c00c50300465110f00d0322001409400c40c10f0300c4070040088485548038a0a400350b90701901240e00031804009547e0140b20300b80040c4a05d04001900b40615081d080c1c1c2403440f404001e20101460039008140f0000b0400b07203001c8c2da030240045549007400b1907020a0198022903c910840c01c003010010300600c00d41125084a56000180c80070307034248140000e2017042034240c101000380034005001e1039425007146d200218001d09010b419075065083c20039200328024002c9034900b2000380100300580310069214112034101074000303206d48440c0b8000d401d520681c0002c42d80800c0180c000300c04d00c0076000342c011449000b40c1b100c2011909401c26032080f5a02d46c2000318015019070700411150400b000051800d2000500c1d0520f401c0c91001000d2841c041510160016440802003040c1c200785030400580000914841e0380b0075448440e002503440d0701414000302120b490322400c144619850809504405004098030121911070010500c0c518041c030410340b09600305030114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7206752 1250 7205502 7205507
    0x15010c020112020a0e09010b070611030405030412020a03060e0610060c0503090f0607050a03031e02090303161118040b06090915040c03080d0504051c0f0806150c03030702010507 78
    0x1002459042e100c98014014403071800000350081440706040c0481c030604043d080d0360b079182850280942c1c10f580740d20303880c1e0344c00c206040b1400d99800d003004100030420b210100d01d0000560707040712800e80c14501d1041861012914042d42548028403043c07c2040e00180d1583c00f10784c0d64411a09103095031502075803140c085030721541600014003503410811038881a41081c9250305121003000e041c19280000a0703860619000f601b00d02500020b50302d4095000c051050b80c4000008200b654041d0306002d000d00c002900c07413003030651203407065007005414000c2100c07127040c83c6180b0070024000b030f81d20001d96000d41c548107022030741107464585080004600c0d2070300101c41c80c001c564400c0104214510b500c00d03100c40c0c2038050702c142e40c4919404400000945010018224484d1808000c200c80c180f030f1a05602d0401c84072912903201c0359446041e82100d900c4030401e2000900c1c0d2812050944079a00400c0e0203407a1005049603030740002918415113500007006600408190f4000c000399560001c04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7208002 1250 7206752 7206767
    0x60b04141f050f130509040305030f010f0e01060e0a0801020a0302040806010b121909061b080907060806040f0219020303010315050103050303061203090a0303020705040c080105030c01051e030a02031501 89
    0x41c50040b500c2440082c0400380b1034000391400d00c2e03400501601e10713620754002948a4104070b50403070010b40c1c000104400090756580460060100c0c20005070b5050400d41d0f202c3c50008140214010015030407001c01c41d55564a1048009085140085685146192000b40070b0340c01030081002c10701c210800012a42c0c4c48130b04035007181c1ca0012200c4507586600205500800d603201880d08003a4a804d9003c1c0898043c0c4903040a03000780941c0d0640300024184090007540c1300420a18490300011300030448a50031000c20355104d00103c8000800754200c0079030700c00338068951441111551414036034812a000001181a240236010160b003420301d01c15900c00741c031000d00004096070400c2c40486c101e402c4c034039504034000d40024145d904164600c0d01042d014881a4401da0059000180030041828688a1851841340500c4d02584035070411003c03a641c0c0c4d244640325410484d00150000e40822102110703036030042c070203070034a40d039040542c0e00d00082d40058442400c00c800d8684a403a03950b009510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7209252 1250 7208002 7208059
    0x1211030606040302090606040b120105091e0a0e030d050c04050306010510050a0e0a030f0303060311030d0206040f02060c0601060801080c0f030c040906020f0a08240a0905070201060b0414 82
    0x4002d00d014150790910043c514050034403504202c09020101d2000d00c808054543c44003020040261580350800b08004281c0c06060709a400003031413200700d02c0c000c881d219141c0c4425200b4010074080303c540809031946c411140e0b8500b0151400c014050444841802030084500450854646036220700810a2503455005401c001c40d004001203002d087c081c0e03100701c4142e480203003844607143d41ca0b222031a0700d00c800c410071030000c1d80d0384206004103d1180803820500384241d000b040c4241d8003440184d0b683c00050300c05089610034100103401c66444100f16030299440c1c0c4184c480d1540c0d95180902071110a01a00086008052280856040189442400c020010014114800f040d0b05000040c6201c8000380c034904c0c1c0801c01c548012010700000d110701c0c4020341e030b03152162030549140740d42080a0100485140912036401c8000c0d0354030300d071410560700d903c0e0000a503500d5200045e401070000d640201105100818001a2401000110700103d0f005032000252030140401000c42e050344c520 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7210502 1250 7209252 7209259
    0x5060606041d0702010906090f06060605040b0a050903030f0a0917031c0903030f1b0e0f0603040b07020f06010b0a030e070503030a03020c0106051305010305100c0503060603130b010612110306 84
    0x49000a815200300ba25034000115000020b51055181c9485090f070b10728a20035211000849031190800120b44205c1c401811913240c154285800c2a410054521070525071004000000c540d04a241d41d00707100b11418084205035840d6584260400a010b01002d44130380780d1030ba1844e400d89400401d020041380d01e100150407814521a85c101080030044c4103000c019800c041d0703248034100d1450064407880800d10b000c0b282c40f0300c213011080d500400d002030440c4046c1c010490900741034209d4441000b6280c109a100c7c1ca0311401e43c0c1c0c2c41d40124a0111600c48912191141034000110303020214005c1c5032500140c1e0f01232046c5606401c0b01c546d9040c80344200b64141e4010000c501c0c4545c465805007401108440c004584a40d4440c0014020701c40018010040c0740d030340f801001009020080700d0894001031800340000158101d015100d40401410341d8001c940020000e507210401c200b074500c400d50f015030b070000c030b035619500028202e03400c0300780b041c440518151403031180d80340400035240b040c0b074003c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7211752 1250 7210502 7210529
    0x21201090b04060c0219050105011403010b10050304020d1209180203040506040209070302070606090f0c020d080105060706090f03080601030b030703020f04020a21020d0b010306030206090907020c1206040506060604 94
    0x240d8506004041d180c11840031406075403203841d03506d081074443d10720b901d018400105407941400b02030000c4103248140c2170301c2607240ad00d001c075aa0311060500c0c4512000350401d1901d030b60300d030f002003185821411b40c01091554007460f6212a5504595001c00741d403007440b0f4107070458040d005140104d04c0192800381c0703540c2c03102c8006401442c090700100d600c01c00c00d15004d810201a9030324881619007d40100c1442c41d00c1e900c10f42843c04032846940c00c1101c17603100a091116060300080c3c01d039041801417a018990000d005414000550041c00e0020f0b4001c145164400050400402c8590103403100c0c0d00290420100d4481842c3c00521003003566001405809104c0700c1c902040020340c0b0244a40040c0208400510181c0400d0300c820070342c0700058a400741c1c0d600344403110401100c1d0360391005414149444014400341e210308080d00c2240205490507415901d94480c280c0c03601425040503913000c1a080c00070503e00d1800f0405038041c5114408440007038840c441009018015809184070341d8802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7213002 1250 7211752 7211761
    0xe06060d0203010e0d09030b060901031203090201050f030108150c130b0d0b03070602032d0403020103090609020411070203070e01080a0206250b0114030109081c06050a03050109021201090b 83
    0x2051031052200d10040c00098034082c060240c904141d0030400300004941149030400900080f04021f684c8205d04903044405581035030b5984c0e40d03016211303044004260796010810216401501118400000b01400711b80300e42e0760f4034031140d803900841255450446254049407081a0b035005071080c12842c04281030f0303800e003051108841e42e0014860440041e850703d0810711140ca051041e403018015660165984866140710001c403405508080c0058800d024034003c002801070702528103aa9091a000c0b41c8100f80d801c20314094500028045d501030715000c035541241e5814030081c1210f601c240d040da9a500c4c0c1c0c1d1442c1c0550004248207442c01d5400c00540100185020300042121119449422020b20110f000030828489107100845038070a0303c00041c0000341300c10740c03a01070170103003203001b401004240d80d42c1c0040c0e4064942038141810603000e4440a03c8495048000071b80406440040382a03034074180345000c1c1680620507170240c0b40701c0c140b4044010042c010f0865007900010380c20f0b0b140d240c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7214252 1250 7213002 7213009
    0x2030705061e030403020609060f0112020f01022b09080312010501030b1305010902130509070e0909010f02030405011b0503010e16031404030c020102060601020f07030b0c040f03050d03050105040e0606 88
    0x4a1a500c03010a0751102e64202c1e035030640005940150300035402442d480c6443c40380d036864170f0000b5060400d0021110010000a034041d2403070035500d40d041e10034080315418900180c0c94552490000c01d260103848d21051403a40c1c0a41d00c01c2d04400d00f0341d40305480c4507600e0015907124460100a5040c20b001c1c0001407010394041e40028568a002034200d4035064901c01864007107840030b8102000140c0c00182d0076494460382c0b00c0850103050101d401c291103083c2071001400900078480454000e032074460010390101006c1d40400382d80a0000000d658070314017440d00301c2c02024044030401784903080b03c5510200d9407081c0305a906a0b40000f40444c1350340c0340c0c0c00c0a141c0e4140500e101310700b01519248410346101c81d034101c1c1c6000b81c0c400d0b01e4400c0075644910019050001c01005581194070000708001f0180e0001808004c481d0000c8841c05184c4a02c2165602481650021180d2601400c000810013000084688140503c0d950800050340c991041006440c50398800c0e00301d0740d02001c04600c2c81d03c4d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7215502 1250 7214252 7214257
    0x21516020316020a0b03010602030403061b0c0b09031306020304050a06110303011a040315020306030c04020f0f070501091a09010c0f17070306030b130b010b030403021c05070c030804170a0203070506 87
    0x140010132115090782c2d40c00d01840e042d8406d8000000682000c2410030030006a4040d8200704140800d000207000c110b62402480d4040e1070b4070180038440c0420100303910360800d00c00c0b1109100d192800f4450291104000b070756a501030f07c1654050f42980c500000c40724031428810010742c0d0408041d5195074070b0480110144299030601003554641008000005031406035148203046042d01c015072a407510f4002c03d070403c3d8000c9401c82c0501e004205100368074020b070f8100e402582c2c0c440c80ca00d80f941d03007501b0000e006003600c942c001e042d4604000c0d14100d040d14500c1c502e22400ca00340c028000c040110344105c84840c140e280380804614064000e1a03400c1a44480c82d41c0000c091400107191a9603446030810b04e507050fa4856845481101210103200a840d081d030301610580b44c02d90300e9400c0c69980203640b40240c0800481c0144001002c0c02514490750407641e246820010000c042a12800c2600c1e455000c0d01c60f60012550b01680d510301c1003030128010449540040c06050f441d45400c00303012407503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7216752 1250 7215502 7215547
    0x2040f05151201060c031103030a090302010e010902060406050c030c03070b09070801090f03050304110405070f030e07030c03020405061305090106060e0f090a0b0406030c1401030507090f050f06090405070215160203 94
    0x40050542d47c1c4c0320715020800742d4400c5010401c08a0003803120304000e07085881c0580d055405904028050000d6140c070411036048030769a00e401a6194281d10702c0340e0860041081d03201d020701000034100e040c090540500b60080c0c4505d01035a02c0390780d827041340908803140d180000b0060b41540c18202c020034000c0d005181d10900600318140c0b45080c3da80000c08483e821500d180101d2402c2071009891135141c0b0403081520080d07001410303041c3c00c60b120920340c034078148002880342d80c40d03c00140d2a43c680014820021510b54814452800c04031845806031a4a004600001d26946000340e524a0702420129080102610749001e07906c40c02c4104021300045154280c0203500c031600000000c044501540017017040500154440d48003100060a481c3c0c040c03c0d2608121503a9810710010941c030f1242011140119060f01c581341c1d000c000b09400d8007614003081d900510700805c00c04001e402042804810703d6850b152102c554800300b0b000084110922a00e00581c82840b605102e0a00304040e1000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7218002 1250 7216752 7216757
    0x130c03020f1c0506010f08030c100c03020702060403030806030d0806010e090406060503030f310605130f08150106080709030b0c04050607150506060712050304031202040f05151201060c03 82
    0x40c50040d00780842c002440071002c84060340010010000901ca4103540b10203469004095454250100300c4944d40e0705404c202a00e109990b0103952200500030b03070403034089941c00f1700407940f100d9490601400500c4215031042c004c0c002c041400e903055104841e214440d5505841d000001c1e000ca40600030b903400e00801c2160319a40d074420209071584c081025000800c45007805581c2c13203000301007840450040080100c001c1b001451044601009040d4036004d50311986070454803030100344000c64108404e81d0082061407100040840c5006000c503005011105d800524440b41e40c0e200070031600d04408403942c80c0004c0d94050300303100040300120b485802210801449003001d40f40c000280880c0d2010500300c2e0165841c941d000d110100381d00480741d000b441140c52038180400c54590800002c180c1c5446020840f001002604050180d01120f1a040507000c08645581c1c03a15a4581d13400030b030f0300941e4403074003420f0b801d5070b03030000038000722090642d05100e2022141d181800644400711548011403d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7219252 1250 7218002 7218019
    0x903050a0c050a060e25030209010e041a01030305070201020d09050604050f030709020c01020903070e04080a080606070c09020405040b0d0c05060306030f03030a0b0907031505060a03060503060109090209130c03020f 94
    0xc13610740d0240484480185002c0c0100160b0744241030b41500000810120311000b0307000c10000350b0789038250343e03044410220b40e0741c000d96074619201000c2c080c800c03040540b001b240c80000c014181e004003c0c1c402c49200386c00700e03a85001c01103400e0b601541e540c4038165105d00104010f00c0f090404c0031080199060190440311140d85900d00d684c1a13030030003503024042e81e60101c1d80611707915042002c0030013800c2d01d0304c0e019460304041d120f0150921418818105100700c210220348242c45407021104413a40040d004910f1503210b45504020303603c14802d051045082c4403002002d032038a40900c054860740500ca0104807850300c0248001c60300000c3c0100e031325005060180300580e500307100a603c1040011400514000d901e420000b0051004d0252001c152412000140200400072050180c4608540d107940381d00c0e60030000c40c064601c5420803030b05400b400c00000b44844080d0481c440c01c83c030846071500980d1b5044c4018002550801001d40003c5a0110800250600028090441c00090600381 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7220502 1250 7219252 7219273
    0x19050f0402060d060b03040f05010c050c03030c18120106060306090c0507020904050102091c030f0c050c0d050c04060801050f160801060c080702040914151302060c0715120f0903050a0c05 82
    0xc045c0d03042224140c448040e140201d00811400380300c1c9440000060518030b0504000400b020780c4e07804001d140800ba034070000350418480071103002c454003031a0014403c0302359040e0405c0e014081d28481c0704070313400b00b420b148000c03c060101d40a20071103640c0c2c2d0f503a110f04111a82e000c000102c070300a0025142035508000c040d0316610341400c0c0a681d020a1402c80401204502d00180030719521700250080201101d00e06002238408a0044107680c0110b0f103c120804442c02c1150800b004214466400342c6003600000e05000190469031150301e0383c001512003035458505150754048003090440016072408014000e04d0701075034012718480c0c043d5090905000440d40414101e800c2501c1c01c0d100c04030301c44c205401080c1c0030031200780000d220220f0810141004041c01080c2e4101d80c0c0c009100325400324180080e41010446c0d00c00070031805403203098400300030001401f01c20f070000800d40307168104a2004010640d40c015090466403668469150018010341159602003040e000c40b52405402000c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7221752 1250 7220502 7220519
    0x100506040303020d090e06090105040b01090b0c0705150405180903071703010305010b01031a0d0203010207060f06050112020a020709020c0a060c030c090e09070e07020708010504080319050f0402060d06 88
    0x820141d44a90000e240018150344060010115a4080c2980e072604d01d04100042d15449416411110203860110b0501400001a1080d0046410a0052650220359001c0403400000c00078101e40c001d690b0700304003451840c100042442607004041d0085200349580840d018810f80a03684401258140c4c1d0510103541d075150b101111060b41c2d02c070b02640120041c01072000a04c80e481d203005003402d0401400d40004d0500c070b01102d41e05951440361b641c004c28401551030a40440b1000c691141e400c0050380074103190341004280500409000410300301c80300342180e03a00e208444410200c0e400400300b5603e40015480a9030000b0b42c0c541c144e00071040c0c1c2e4400115980a100d0390b00100f6240455842c24400e0300401c4504543c0c86511221640790900521000100d0010291055103a9a04441d520007201760300e060030301d92100043d51f103803004010610100d8805540145903480c40325030800001015801911390544803400c41024101c08100149002d04c018039102c410980c02013900f9a49031100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7223002 1250 7221752 7221757
    0x210110703080d051501030e1b0d0606090504030e031207060908070209090105010510050403200118030602070b0f061e0a0801020c0a0203010b0103020c0a030305060409080304080a03140105060909100506 89
    0x202604e44003406841c0c2c3c90240a034907120000c0c0303420000924035000c41c130395600e0b01c03103016115144804101d034180d40b01d01140030039198101c4000d02c051030303407035100030020030080314103400245007800c240c251460b01040b88103450320525229420b001c2a0f4940310010001900f0407aa5210100990b00060311069003092003401c0fa0000000c01e50303d818140a09401002f070072104005c0308000500010f20180a601103540c0e0910083c510895550b006989101c4281410540f241c22802d00004000c0203800800e059031059451101646a04034099658030090740d6a41c0c1c0921203800b400d6080503144611a00884020007507651583c2d54074a4900726800800710362125001a000b490560400f401401c3c4104003e203000c51501c95082a80d58550860640080405841d0300c0400c545994940002144540013000303183c0e07070f040c145015802c0341c2c0b0019408010909040100988000500c0301034100c9101a024601d450048410022008001004c10075000a06040441c01da100c0d04007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7224252 1250 7223002 7223017
    0xf0b040f090605070810030602030604020408160f090b090a05070215090c01080903030705030105010503090c0603070903140601030302070b07080c0d18170a12030902090a020301050406080307021011070308 90
    0x40c00a90000a41407180558000400000c148100b04003400141707403078031001004403a04123900503181d403104800100648541d81c880f2440e40304510fa02c2301c049440801030002c64034450f00c40341c92a5a2440d00d035050703c40001040b50b00182980000d840380c1c5a5410159020020f40b0641701641420a03c90440341d40685030005603600080c5c144145582104421380c205200c0e5000f9402c5203000760000f4864481402601c0c10001c0201c00b20350780707060800c00c0c44600a80106445d8070792a104100800e000c825104c2591018025940c00d90000f40200e00c40741171304d805134040d1a019040c40300716580380d48031850403104404100145215140e0502802000168950301c040140080c40d030b403504110b1150f04442a09203120003102400c0348009800c0002660190715014100b400100a80050003443c034080c1d007200c802010400c006840d640154141c03803003200d04200a80e160081c0326524021280000c0d00808841c00704048a40919602d0000c000c0c08400c035482d09131070341c0d244402c2e90040303403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7225502 1250 7224252 7224281
    0x516030902040f05090c0102070e0606070f05070b0c0c01030f0c0c02061605100b030c010207061e03020706150f0807120605041106040801020307030f050c0a030f020903070f03050106060305060604090f0b04 90
    0x34501b07190f5a41071000c0001046640420403580c1440f10000b0707024400c1003402090189140303901d60030070405000e550020709601c4050342d25607020300b807403689543c01e40c03c10381d00191801405658008241c890003d82c800ca0b070751380c1d0700001c442da0300b80440ca034442e0204500d003409482022001400401071003c0f00c00c03007040085103680e581424140f418407030118085c10b5402090080c0a02a4000070300c481b4840044000d072000b4040c920142c2c024894440040d140a050040c2c020360700c210924403c4c00c84a504941c0310010795035400d102d85031245801400c0d84418400c0c024408280150415a0418000c007c8a040c0b101c1070000210039500991240c000c41e50007100f04a141c1e5007500c2001c3c062600c1400a1010385014080342c4030a205078158501415a2031285001c2034000394103407a1341c0d000c058111070f0b4058403045424070100c007a10045910790b091040c086038540c8207005503070245501408690401c1e08211820380a8400322400340080780da2401d0340707070003036581e4051003981101c0e19 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7226752 1250 7225502 7225513
    0x30124030615030b040b0402060f07030215010504050c0a05031905010303080406140601140d06030c1202040509010209010f0f0507080301030609110d080306040207050111040806010f06030516030902040f0509 91
    0x140380100030364894101a0b000d071060038a040000c102d044400b160b0040d802801c036040c5548510005000b805802202040714001154075000c141d00041d4003241002c10645189071680d0f990100400e481040724100c00c190010700c0f031102c400d40283c02942d000511503080e032080c112811140805c8480036070041d400a5010424401444810b00c140c006018106810750404d1500e00006030426030700680c0c410320010000340d02c40000c4e0710341c1c0c0600003442d03000306082d038a96074805448605241400099200360301d49000b01d04010014402c64442c030710180c49036030007a091401c080c1c074140340c0d0083c4901480070400c0484000381d1201c0007180610300c20080002c072801d16050a038040c24003c032007a40106c403890390b608003068990041ea90f02000032103000d42d9174000784c6003203805020407219034070708a040805c1c049049240414098141c0340c1c401d0600c3e02395175440e02c00b202900c1c000e0300c03181d40d5121010525900f0741c5c03003030700311a4000f070001e000494500c6504809804030b84044079a5502d03500702 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7228002 1250 7226752 7226759
    0x40e1e06160201020705031903020912030306010215060901030f02063a0203072102040f080c01110d080601120b09070f0f030209130c030e030703030b0306010506040320030124 77
    0x40300d04051845507148002c501301503c0b0b540b640d42c0d900c19500d02c00700a84884181031003151107501201d031401c0300070b03006034140311412450b544d43c1d820660f00c20b8050b008681440400c2e10540c08410720400b8010807203400d81e4038540714012641d00d408005c1e80c101e5405c20034401150301016600704404a1500a41c2c0c0f17008402c044005103042070000310101c0c9004005024a440c0e0180e0740303110050b00b541a848610b407010b500140240319691000d444042540e000082081000c604c40500803c05e0701c90b0f112614030b661105480710407020b001070206070001c5c082921540710b0350f0006069061000005403041c0a0400500d0000d000c80d4610009440032441040c1e0907444060b8413101441c0c2d040a604043c4c0e40d0000a02c0300e152070050700c0b10195950342480443c0c1c840d4200b00744149426003643e80d5140c4604004001d8803200074000c0c02485060300006060500c030048504590f049402d02c501543d20040e24400014020b00712503141d07403180d524030510b110340ca080b40144080000c100700c0341ca24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7229252 1250 7228002 7228021
    0x7120801140a0b03180102041a04050a090501030209010e0402030a0209010308030412030b03070b070206070204050c030a06050907050a0c03090803030c070308060301091a22080403030305090f0309040e1e06 90
    0x1840c2296030084030b80200412500740003c00f9642c1291041200031051441080310703500a000740d5000e40150800744410004c84038043c0f00a105588041d54210070040d2030341069015641c0a11000390800e00d0f60004204015200022035001341c801016141020036503000034046031002e0b0410b4404000000078841001181001c0b018031100e9401d082c4010030288000035262120761140c2680d00100164060441d603a078800c4800240c0d00410401c020308080c3d9140803290800c81d00b00c6045441d2540100b120b14219016610400040c0c1d5981d140121040c8121010380c2d031003600310300b0f100001e400802c40d004140091813044000301d10190300c4444500300140301031000b900e003e0180e4940500c14000c5400403a800800022805a00c8100d4565020450416451032000e00403101c402444804100408008100700e0f4060355080c042512400c2c0e00e69200d041a000c840c5640d4802c00c103102150030150485404007042405541100501141d840d1203114140f2a4010a810181c00c1000d0b088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7230502 1250 7229252 7229279
    0x50415050f014a04020a0b1305040b0d050d03050603100504050a1b080105010f060f051602090a09060e01020a1808030301090506130912020705040b150f07120801 71
    0x30300d401821859490300b2075240254035004441c0d159007840d00c1d8201140405043d035421400b100e030070110201001d01144422885041c2d41c1203100d01080f5100040319603080c0203485ca103120302010016000e2602003000014840e44c00095082400144800040340e8288481008041c080d200801c82c0c0c82d14600301400c0c801c0c86905048003034508800d010100da000581001401c0d4010105060ba40101200003ca5240741c0d0102c41c0c190b081000118044021742000421581e4980742c407106a008114151298000ca910224488503002d0100000d850400e01840d04071700580c1e00000c2c54440340d110803060351410190b401080e900040d041c0b00c45540228480a4022012403002c1e80d6400d014000d40c80c1d20041c0301d402c034081c0e2900089603150f503405c1a0150700b481103100400ca1f0700614a480c00000c80e016030860094040c02c240012075040031b004910001700c000380541c100040c01c4241c1046904050586000c21409101c1800010512520081c0201c00e9807a07030a4035601d0034150b442181c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7231752 1250 7230502 7230511
    0x604030305010902131403030c0d0c0c0b12070e0f0d030e12070509040b070e09010303020a03030501060516080309010204030b0f090709140601030c140a0306090b040c020a02010f030f05041505 84
    0x41344104070050010242411542c295000c1600071350700072540030001791450161240d2041c2600961800c03034034954104080c51042e600c41c011036000030750707190105001030040100f1041504101d80024407000c1c4914111218008010720f40c5c800d1207c0d0f24081454807201d030f6802c502281841c2d08a0009240400c0d065544c410118003c000040c20200844c0200d10003510050480070b08202054100340100c410740115038014203400c81c90340e500d080095035145109000d90100b403030440041025031207035040352075851481700d0310380e811075266440d1003450340010700d0f40c12a95428007010000469110306140100c2c96640395a0443c2450140c0e2400c002d40c0d0343c0a005010b240c0450003464103200c44005a2007002424002000080c5100a890301790301d000e036455030741400050f540112601903000c0025100500c1c1c00704007070411042404119840300c00a500941c0c848207103000158401d060040007a102e500c0d02243c4911603400c118140e88083d6002c17182c01d05d1280c0d00c03043c814818440e69510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7233002 1250 7231752 7231769
    0x30b0109090504170f040503010207110f0103060509010b0c031201030305040602150402090103080c19050609010b0303070b28060305010209130207151a0315040308010501020307120c020409020909060403030501 92
    0x20f8203281d6030310280d55180d01e048001d00b1001255214400442809840092034054008d66440f40a403030100c42c0c20541000841c0300782949124182994401c2c81444103850010b464040140d080001140c0b454103d01c2c0c0c030501906c410000c130619003100c02c4040c0c2c002d500c43c1c3c441940340c500723252000c0c3c10a00032400d0111044540010440507a84e40403500341144d800c071514942d00e48000c2009404c1482d4000c807095103000c4612031b40c040004c002081c81c030460151000300b1031140d1200405899104540c5c01815050000c0301003036503072003184404402007071100000f40c44945d0f0b10864105440709a0f20070780d072a0354089024042d0381400d548001080b01d000c00118542552907071056807504030300c1c00c100325869070b505d8604405c03410742c065160f550500500f200c038000400c140c03060703d07d18112802c400040c01d24000007495400081650603056220b1414110789000304022103250903806001d0382d00a44482204000d41c650100d84c42c05000041c001e092546020304000e01900c4060703010161 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7234252 1250 7233002 7233011
    0x60e010302030717100f0204050301050f09010b031f050604091406010303020601140112090309050604080105040c0603020a0507110f090c0315010906050a031104090606020307030e061204020f12010606030b010909 93
    0x1c441004a034800c3d121200c170000182840d010320700f46001b409a80c04c03203134040d031a15090242102c801400f0f203104000c80740007408291496400d144d21031404052141c180c118807071801110780c0c3c40c0e0b00081d0744240d000d000020355020585400314002c03440ca0f0311a030b16401004c01801490780c113110580c054240340340e44001e0000c1c0c480000301258040c809121032140d49215030010103100e4144100181801440079407a2074580700380b40e0013030405a86c00c990108889400240081c040d000356001001c4a490781c43c101140d648500061031010b80f50560301c14500581515683d55034242640039140844113140c89182180c41040805400d4047c9410f1180c0c488080103003643c01011101824600d29021980320425848a400390103241c00c001d5269041c1500031800590000141054500903070300c0c060003418102c18062036103c0c20190a254152030b500080140c24141410040c4e4034015200c080300304d0000d01030ba03017100c445420071400a80c440704050440d603400034100000d000050b40800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7235502 1250 7234252 7234289
    0x20a080702011d12100501080c090103120e0301050705071a0f1f0b0706050714130302010305070210050907050307080105010e070c02060415030c030e01020307020a1104020d060e0103020307 83
    0x154000e106000b030400007460842d46806102100d4102004400b80543e580d070201148003548903214a041700b885985003400005003a0400a81d5651843d0050091491a420368071355241e00d6000746800c00c1031207030781c1c40350700e6075503c4c00d2080c148100340300d030b5445032214600c1c50720a07484a80c1c030046d61401802c1c2c400307000c26040b80107500c5411018051030310312500301c80040c11008482c2d44d03001540c60300c0c002c140d1400b8460190050340c800d101d00e554020f800c0c109030443c440103004d072091808040042050030300040d4025444070f034005020340100c0c0c0040034840c0480c011b94804550490264012078400c00c0b4900703042101501400249000780555030501c2583c000d11000203114400b000281c59104d015503e800040f500a00a00150a09903014000c0d014014020701e00c09000042c2c50a601021403950600c01d0701d0203000581d0152919854940740c0c14042d601d6400c44541c065420004500000e070140700b0780300241546e10181e00c6940c55801050f050030200da02001c018443d00328500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7236752 1250 7235502 7235513
    0x501060c03140307020a140d27050d0206160606030507090207050606040504020a0e090303010602100e06270f0105090c01020102042106090b070507060b03030f040e040f050d08040b07020a 82
    0x301482c1c0000014584964454501300d10b044aa05000313015048114010b204010000ca04460101078030346803c1d0030102014054805280078501721000001038000901c210314168500c000c14a000078060350804101b100c20101e90a8001411540c070307a42c0f800200100042070181c04001d00c01450210305085140c0c503240d072107200040950344034950310320000701155521000b003809441c0d01081e1075454680350340681c0e5254420300402c40944240d4200c2d540c000d0b018080c4000803a40580070f049139481e425458003480e00400140c4801c000d143d401094000c0d010848015082284000031600381010243e01c1d09001c410182941103900422060004110b40500ca02061400b04514045d800060030400c1c01082007050007807003034498505000a9550000207000001d01411041005003125401c26030380781b00c0e6140580180000b40020401500c84040156019025070400e2031f2283c000d03924641465440720a040c00f0440540c1030005100711505401c0d0300c800c85000412001c111521503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7238002 1250 7236752 7236767
    0x901080a020907081b0904061a0c1207020112020a020705030d0c060b09060f060304030c02030a03030606021006060e010c0203010e010207030903031407050709050402010c05010c0509040c02150601051303080d0b040501060c03 98
    0x103c5c0c61644002420405602e6551282000701105500c3c900074652415140406601100300784030700d44580b4092140308640c110883c0c620660503101c1201529a54000030040d4001003505801d40c0a1500006020348080c0000e00c3e000360281c0d103010768045580381c40c03000c4800e200c00c42802a40342d1010030540c0e40343c880d0b00510440d41102c082c0d403a50381e0303407030b040360103d581d50750094050003a045080c080580541014050381e18035000da0f400007105a924030304542c941c0c4102c4000600503a10411070394020500d41a134240003130000309810502c41d000c242682d0002030304a00103410448108181544008901889411109182d192a038039858681e5070320f0540c080c0c103da09540b0304c00700c1d04680c040c3e03000d00900c0c1c0c0d00070000e00c49074a486902a06c203400c03c030401e0340075034205031038210340038070200784c04c07202c040d156404072030700c7d107400c4011211500310300c070000e16400410030088085030300300703010341118100c0a0700030603201c0078002170009842d81170303120700103020f68401d00e0b00010350400907 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7239252 1250 7238002 7238041
    0xf0309021309170705030702040b01030e0607030510080304080607080106090810020f070506091005090c030a110604030b0c040602121809060301020d061202030c011e080c090901080a02090708 84
    0x11640314201c0c182468071541038042c0c0c14043d24000b0b200002c0001c040041d18080d40216020401c5000490040d0103030360306880310042c5d42d0002d800240c0c066010303600c241d8100706000c80c0d8846c610744401944d440e6520513004a070081c1d001804101650303a10400184c0904954500040300a29140c01150303104100d83e0715202c0300b50081100d0000010080c2038428568101d8111012401e0081c99036440707034980100c840c445230909000801c2d00710002038520324188040c008012004c03613501d4000702180c0700881154070803010000000030030548807449004400500f07290381d9851038110041c1c608a114200c25000620610a101d0041020000210058400c1d504001c9aa0724800040c1c0284604000c181003d4680003010684082c2c54940c42c641c58400e4040f284420094001034a207400c203450380540d02c10501c40c461000d103105041035070300110030b0a0300a0070440c002e4001000030400342c00c18103455105081d0b4000350702e001744029400804505204805040c440441070749400200c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7240502 1250 7239252 7239289
    0x3030207050c030a020901031511040e0405060a0e07050405060d05011407020d020703080406030902030f010f0b0913020307060c0303020408240f010e0c0702031c030207020a0902090105090d0f020901090c0f030902 93
    0x420380104280345d400c4024040cac140e0440981c1c0d1a01e4805555048206450546041c130030f28000404500091103603654111180c2c00401d5540d18180800000d09401800281c002c8000c02041000030720034080c000031103030060203491300c030310f450b810084c9010b4400d0030620031507100d0300c400c101082607002201e00b40e401c10b1401040390841c41c00404e180c60901c000c0303072201d903103015924040b400717590b0300c044c3d58244101e810b0441510b425085030032221030b10b0006035242d00051010003000b4000c4003541c1010b40b283c2405401e2a6954140b6070410036910000e0840340c100c00565245a0034192140707900042541d4a010194104003480d000d020004040b044c0001c1c001454406554003080300d01550424600800e090094111300100650001d41049001c1c40c00700c07201180411650003a1400e042040e900c2c0c0b800c00503082c003003003418460740d0f20603192030344441c4010025842c1c005001d4040c0620750004603044660180090100e00c02c1010f0708105441e04200000582e44d14080030003921840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7241752 1250 7240502 7240523
    0x4062f0d0903020a0b010e070f02031201060807090308030a06030303180f03050f0d0501080319090303021002030a09050a050606010909091a0703020408070303030f0606090e04060e0309030a03030207050c030a02090103 95
    0xb440c0c142d142050b41d5101400d030702d0661000050f10f55451544501c140005d0b541c0d4004417140c00b005a83d02c3c082e41c1c4003428000c600c080140f01161280c0b8820307920a0451803c0036046603039445040c5039074001e64141d0040b544900061040c5501805815003040c0b28592800102c8042c1d1038040994140e40002020440c001489034a0008000c099410400b03000390100560350303598203427030f41e681d00003d25000c40200c048060b44d0003038000c8042e2403c59406401800d0750405243d0030400940c07000b4003106003c0d0743c1300c0f4608040b440400840c0c6415114500800d594100300001500c050398560180c00c0803401d0200c141c0c0000c1d81417a5165101005416121582e11000c03002ea001c1d00864010741c0342072003808000010301d94944c00800345010304040030021180c54000c100c2d082034207030084010800c40b580101d030008004d42d01c031805001000f01030b04c0c1000c44401c0080d0034402c540c00241c001a8004c150403040c000c1c02d01c424858000308400170014403902e0390204111071814800601600d005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7243002 1250 7241752 7241771
    0x9012c07030b060a021c0c0503041205150702030a0e03060603030a0804020a090e060f010b03010f050d020a050402040b12060603040f0b100302030a06050708060307030809060904021204062f0d 84
    0x180d0810030b04072034024601c035152003048000950b20311010946034030141c5034001ca000d0940c0070f851030b10403468000b0080c6191500f0321001791000c0130000412140e501c5150031207580d0114400f0050b0181c80c5550280d0340e6031504182c020100d01d440910741c3c0c800d8004009118595a0000c00c452104c009420005000d0b512400024841602c42d400710160311308002190402c0c49012035060305c00c407045c5079041880d903203801d0600c40d90f008c02d02904280301c035031103c180510314109080c42c442e98401440c0341c90341500c2c0c0340850140c1e04294400c201d00702001c102c0d81061415644401e0344200107450380d0382103290540714000074150344074019004159000218030341c80110000c100c0074580190440d0307868003461901078020f12007112504002400a00490b101d80b502049240480c0e80002c0c0d040d040900034410040325a0241ca612a0700550070000c80c0d03020440369860768450703800b410700094111607105885861119401602180426868484158481c1c2e0016101c00240c11440010603454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7244252 1250 7243002 7243007
    0x902060705150103020909010507090501050c030d0e0706090603020c060105010302030606190503040b0a05070c03120216050c090105010f05030109050a06030204020315150406050301170c0d05030909012c07 90
    0x8444001e041c50103920401118440185003050407244203a40202d615136407006100d0882d00140c42d0702c800100729441c10001584900094a07034403040d113041d00e00e4070310042513000c200d03526085003940d26003141c0c004000c0b0030307042031100300280014101940fa040000d10210385911050082c541450780c007001056254990f003080d260b01c1d11543d400d07902e80f8000a0710262a80d04100c804861010b600c00000d041d0300d07001d0180030f0140c0c1080e116254001072940c0d0543d20409120360450420341e09000b07100c4039604445580006a0181000e085a20a420280300f140360301600303c141030140c5000284484c90344202140d0440d0307801d1100052588960044030040c200d42d80c07010358403900104c148440e0740800401d221101c0c4045541159000f00b0002039100b0740110f1180001156041c401088100c150308040106940c5071004e0300c2e14000301c0c80001e07000c40d0701041c00369066400811100f1040c21309803525405030807460007a1008090f0000d41e0403050003101e00000d002e00304100070803229070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7245502 1250 7244252 7244257
    0x106030210030b0f1206041203020c0a0308010f0608070c081c061409011401020d03200412050601080303040f03050a12020d0b04060506090904031d0301020f04050306070201140a090206 81
    0x164001e103030394660208030000030301501050700c840d485912039142031196407030205440c5d00d00ca64040050442c41e902d5482d0f2042c503c22901840041c16020050105440010700841081034400c2d100c1c0001c650500583c5400300c2901d030841810f2214141c00c3c006c0e525008039041c0f00c038541c800042076484002801c00300f1038400094500d00142e0400402040380e510b03c1c000940c0031102510040f9003a81d9a110804001d008240c882c1e0144e009146c0190358140710f40c108a80c04400e0340c85101c0c04c108600060210b551003603002d030941c00030f0f208000080290502055005220940c0103608509007a00e5800c01558040b00c0101840f4001400300001c5005680741040d0307500b29501151901e0070041d50001a1100708802e0b440303240b8288001c42c03140f420b84d095400c0040041d0042c2e140d0703903450f80c058600072a8240010030446c40c680c000c6400c0c7e502400100003840d00d1050a82d140c600c0e00e0249850040080d0140b410b590601120070140c0b20400c08880e071080182c0c00200306441030b400403c4003071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7246752 1250 7245502 7245509
    0x30c060a020c0a021c050d05030603010c020a11190308070506090f0d050a050a020f0a030e0f03070b07060203060a03050f010605090618150402040302120102030103110a0b04050904020f03010c031a12060a09050106 93
    0x6001c7c07004004507850f0000095440385806400a002207009840c3c12038036800305000092001c0b43c0100792410604010745140020180c1010b8040781c1030316901c1e0404581c008410031170f032543c13181d010003020324824070008030404e400c400140a0f6448451380502a4060900c840302000760100e48212800d03c200b000034000c82c0c4882c15502d2441c01030074000e01e515409403c941c054103190349816903a0074001084002c0b5019401050309019140d078802020354405400c0c03070b81c410045a40480481c400740547d02c2086146000000d40a19041c04d00000c0e030f000030f00b0740d0b1082803003083d0313098040702110240d6442101d0301150000c40c3d8000b00050000c1c003984e08040e410030304403852121400340543c011811781e80a0b40c070041094110b1010014046402e000304a10903000307010402040c146500156003051005042c0303203116001030003081c2190a074440580010380c9491184e0482160410b01d8100480142c50040180002e54100da9881f04003403c6140742136039400c2d802d001d201c0298001c4014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7248002 1250 7246752 7246763
    0xc03030c020f120601080d0f0813022704060506010801060c0b060312040303030203040512090d060f0204030803040609030f0201050601050403030c110a0b1201050604060c060507030b090108030c060a020c0a021c 92
    0x24140c81a03084c0d6141024020001140f003007055295566004000c2d4001584003507803844810369440038102000c44c00ca1008a81040c51107034806140041100314500100b80d40c0095025803506003070110948002404a6040c46110f000610201341c0c03094000440c01d030001d402000646840c00800e1600703003000c200d05010038001c01c1c04020541c7c1500118022030069040712410f050640c980c0e812072050307880c525400300c03081e41c00500040c1581c2001c00040d000c44c0380142080d50741d80303c1d01c07115402203a040780c029a81e1003503082056085001c598500a5038402000249403100000c0c1441c0b00c2c41c08040c0602c981040c1d0001005581807965807440780203040d5481e0f0555540400403940c00600300055444415800800c003402e204003541c08413205a52040441c0305180c8458008100c090503d00406490f0301d40a82da84e2944a5414000e003101001542e0b5000720303181c42400c0401c060074010805004008240400f03c2c0040c02c0d00f01c95804450200c010710004225110442000500508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7249252 1250 7248002 7248019
    0x180b07050705010e150609070201150902040603050709051c0618060e15060105040b0f070512030106030f1107030e061603030b0109080a0302070b0d09020303030901060618030c03030c020f 82
    0x940039848800303041c60900c10300003070100084150025880d0b40c1c00c540e07103411220708003001071098a041e1500542020403800009007800410010a40c0e41056400c03101301c0f9600010200a030640c544100c40c3c0c42405440d01c10a40c504117000121801303659500e86004444d04003501052021340d61058100d1410000e00e046c5205240ca801d4020b05164500c40007280240c050515440c0202101140b0400d4141d440506c2d00d81061300300019038200045148401c8000d00c55070001580800101080d0840500b041e91290b03d061002030945aa555072a0001800c004120b00b50089150540e180b0076414188081c0144e00783d00810000c5c060584002060784809480a09041c1c15520288280500b81d030b51a140300d41300d48120350384d466500e1300240168015202000901c0030136000e840900b1381c1d03c2020680c0c87e007503000245181c00550703150391140d55a170010411a500178a20324070400d41c62404429880c50f681f5180840034084c0b001805205c0398040724400c40d41da580c4400d0704610020069003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7250502 1250 7249252 7249261
    0xf13110409051f0305030304020d0c080d020105090c010306050604030b13020a0f0503010c03020307080a0903050409020408030d050121080702010504170307060e0601080a020607050109050d08070e010504050a03020103180b 97
    0x1809400142d803545030300c1c3c003a01d08001d104400c4441d86425282c10000651841e1590b0f400c0c004000b0750940700380c0d221445000d01080000c1c05100286074040345038000f20f140d060101907542480809408141410f07d041010802c644481d0203840c1160307049408a042d80e951074016610040080400951160b569000410740b00c5000c50748509a07803054008004048119400361f04034482926a0000308001c1c000083c030003612a00012103962003840c01a084c03d944142c40e40980e0400c1c0c004005071380010408040130241441a140101a4401c13118007e00c1c0440060740145200c14010701079403c005454419640584100c6000f03101c00c090300780085140f80da25507101d03082000d040b5880e500b0410700000404000800794141d80482025000d00c1c482da0342008015131040f2001c580035520707100c03542c02062052051000c40606511034224514200d60300801c7e0b0f070013800e061414800c041c04244070302d45a000c400c1d4140da40c21300300002c01140701c2481501c1c51480d003000a003420500e03000c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7251752 1250 7250502 7250519
    0x2070510050103080c010501050301051b0a090b0a0e0312032a0405130204060201150f06030b0f06071a0a060308030a0c18090c09080109020310050709150503040b01140f131104 77
    0x10800c000c140c0001f08860b9132140101420b94001781c50071118840342240ea6000785030800300804200440b4182a40b138150b0702c58441d0445c0c0c1200c240240460f03a10300c01c500041c2028040e428240501c01c3d0590320b545440d40c001d04e80c0561500781c5000d030340840840c480350000085d0407034001d444010b1802c01c002c0d443c107200c00007030750050180707000650070490788148001c403000703404050314100000e110341182040021030081200d01a9a0340c09400d1690544198170303920010120503000c0d80c0904c00d40c10108046500761000582891002887c00c0410408030b1095016070360070522078040851038801d2502c1c11118841c2400e55019500c03443c0d03000040c0381c006a031241100e0902512005845641e4541440c02c0340c0501d5000781d01500500b580780f0380341d0500c0d441658400c90a050034000c0c40c0e03c5004040c0c4510a81e100c840204900100b80310a05c1406144240142114031b00034169589802c04200c1244030022414000d24145511041d51401a00210f41003d600c90f82c081e02c40303607501c0c9107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7253002 1250 7251752 7251757
    0xd05120409060602030a0e010e060f0f0309061320060408010c030f060f05010206011202060f030108060405120c19080f0a030609200708030a02040b0403050606010306050a06020d030207051005010308 87
    0x110721200d46403000016015001005a90170b5a05c651200c4e0b2068150354015540ca00b000b044003031b4068010054002d181c8aa00c0103402501c406c02021070312854460801450000c0180c14501d511489080110008411216070090004c41140340241c5282d59408034000c0c0c001e98201005550030203141100741580b40c0d1041c81c01c5649608140131a59840c800303034200c41251300400f40180c03c0300005208140300f060300021a640301820f032078907061501042d109c0350780080e00600c001e03030440c005110038440b0400c11010385212542a0707602e0500b07190f131210307922081400c2c4000c0315071a10300c0042c01d101051068076024412540c000e5595038131000010020441da000380c1c00054504240000c01e011280e81c4c4032411180340d04201c0c42d002d45500e603128590402040c200d106502000301041c0e000b201400f800041d0700c43c03c000d10136410624005030a80e512600194041e1495007420001550f0000d019031005405041c0107995501e5428040d09002a001019118500704000001040b070305400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7254252 1250 7253002 7253009
    0x30702060d0b18060307030311030409020a020d02010f05150108070c02030601090c02070f0602190602040f0605030114030615010309030c0204050709050a06030b060702040e0f011e06050102030f070807020d051204 93
    0x281101a442c0f01c98081d21021010358000d0f030190b1100a007440001e0083c900101c0c050b0b41c41c4100c2e410240d403001c42c0d04c02d9074800e940b07500040e0031410080300420f40902070003a800035100000e0100c2c0c9401503019000404211043d41000f440d00042a64136005a40d004007464000c1c00b9038401d980c588400d01c0217062400114401441601000194000e0364201c903000d070b0344a580500010007445204030206011101300b507514a07800c00c8002102c0200000890040c0303105d440d45a26507140481c261401e6000030030107400b03900501d0400c00148480c00c003d250414007404d000a82c52503500301110381810050707000b900b1903d40820711a0036034211000c14101c95044458a180c0b036140d0304210240c0b0f610340c1400381c000005100b143d00514090304520000c0c8071102c111803d6613100c504007425a0a07014400c00444003502e0055216145d902510018107003c0c001140381800c4901047c00e288503541c1c4c040c05416000c6800400c564a14094100d40d54000d021181d1620420103c420f69900910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7255502 1250 7254252 7254259
    0x30628080705010507020319171c110703080a050703090203010f0902090601050703080105010c032a03030c05161506030c080c031603020108040b0703060b041202090f010b0403110102030702060d0b 86
    0xe40001d540d880b80080310300e1240d010f00034004a2143c05a1825040909503084890421244042c00145141c001a0096041102c84103070b8605c2004802b0741101e210203500b1219140800003603000c2034000c2d240c940c004424010000719a6034000341100200450000203515500301000313503030000c1c01c80d0800794035180201c40c1e00702c3c240c40780001500e0903c07802c000107011400010040146600680e001e01449019080c00d140e0030361000310403001e8a9801503a0800c40c5036410070241415454800d803e0300c500c060812515000b00d103852209041c400002c0185180c0307520b020075003c540a0340206006560104a490f00a6120350ba400d88481c0e1b80c03603010740a4441c8070120b0300c0140242c1c07002da081300c1d010f07141c012a9840d9a1540740f42003600408039803e0644644c000102e40c402c11b17000b00018000c407404203200c0c10f560301c10084101005403504002c0084800140840c84200f0201c40440ba0b10503108920640704e01d005074210701840307402a61001010505035041c0350b4641110f1072021003107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7256752 1250 7255502 7255513
    0x1b0b1206040f02090d060c0e0603010801051503010204080330040c0303080a050c0d02031302030f0a0201030e01060501140a020c03070905150409080a030c09080a030c030206010806150603062808 85
    0xc0c2c454100301d01a40302c034640e10090066600c0040b440c42d501020016800d8079004a80010b1030000c030392240d1003a0300c00d461a0b0b40d01c40400c0b2510f4207070780310000d14003804c800a40c42d02c0c0c541580c0070342d2405400f40b0703105d071040c00742203086007102501e00c80c880b2201c42102d001110720b4071303080124081c0d616100903000300f0103900c002440d01ca2184112403081100c0034403282002e0040c45124020b420040030791a41c1100d0302d1100c005654100620750305002840010100040944001010340b80342503a4080f0301e82c1810400e01c1280c4c2c0112a181580c658241241c2c4c549120500492801600c5105683c15002d5028045240c03041a00124801c0b24000707845104a01240244001c5425803000540521010f0115106c0d00c0e119810020100d040c03858034504603622010f403203003414142801103000c9035510740440c04254051011500601d0034001901c040e06d85100c00340c03a5101002041403080c8400000546542d070781e501e00c040c130b02480e590700112544d440c910250b00a0103034051054144200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7258002 1250 7256752 7256771
    0x2070e07030615030f02070f0501020408010b0108040c0509060114040f1a0306030c01050d0b0310050604060e130609060e030307180b0901050f030403020f0307030206011a12041b0b120604 82
    0xd020702d20403a040007424070303d05200c26804500818001c48a6207030340c0c1d000c2007251302151071140d40c0d00c02c2c80d014400040c1d80d50703c0c01c01410300b11402040f0032380c180042c8408101c007050201410b07804940056030114800d0783e600340100d91484864050781610100442d02103481c0100d022014180c40400340300e040150904140c48000d40130894145030315a010468090582d413061024106845415a000c14004151320000741869140f0006140c0325641c0e40411480d0714045c0151002440040704c03180071810210103e8400003e09032000e08156110002d031400c00c51f03140c0c02818805030385070940c1d8417800d00c40001407800c840e40b8601700401038003d90100b0003040820440b5410141611003034507010113268491100e401c020820390550092a034590102e94041c0000d0260a204e42d01a03c4a0342c1800d00d0104c2d0078000381441c4e0070007501440017038a003485603401c41e038116411840391102d1010f680d00b54441e040458018108803000030950860341c0701241060382c0229070884062124802 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7259252 1250 7258002 7258007
    0xa0e010906320f0a0806040605090708040f030203070b0c070303050c030c091203131206050a18061a100203041802030c070f050106030b0f09100c09140a080601030302070e07 76
    0xc01c030860341d1500c09020311000c0380505036200600d042d8008078942000342655a0301003c2d00503140d07442c04180d52030200a0b49140c41c6c410b0303a010f070108881c984158108044c00134a0709100500040400c0c1d42d5441c05070030f040c02001902c1c606a8000225401d40ca007410000390700350000403003140460f003000302080868050b0400c2d0b0b403080340403410072802c0008041c1040703054820750365150034900007000003100c600c80304403085014141c40d4180d0600c055441c680541104e070004d040f03500d8186040d9142d030440c1c034100740700713820785401040102d550b07030703142c4440c2500e00c0c5640381e15a03001e400c0d625111955600400540100c6412051402c3e07010b80c004508400d1b0b10003161001111002000b0041c00503038135000c80a01d160007071000056080d103c3e600c0660090081d0703040d0303102020240800c80307130b500100002006002e00e038805000b00b241c1c44401030142d220724090058000d0100b88031744036641380c80141f000105030100c01c443c0d61b075969082c0a9100c0d01d20713004102080303c1d0407001031a00da0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7260502 1250 7259252 7259267
    0x203010b04050912070204020d020c010b0109080303070203041404020903010518070f0302060405090408040b03130c05010e0901050f0301090f0602070302010b061303060c11030c07060801060c020306040818060a0e010906 96
    0x3c01c0302800d010980203002c078550307a1022038200c2e4041c3e400d0100e4401c040540c4094040c41000d0000003800c402010005070051510394880740540d8820000c2101e61580481075408907400c0070903406009035843d0028029002c0c5100140e0550310304000c006142c81341d0103d403241105c3c0e01c000c0e100c030300d52a6001603452941d40e0001035005002040104400c0c03c24101455005002d0000e2604250b21020381c54900e90082da42c85c00c02d130003505c60100510007415a610020710b4242031180804020401203414448144120752040c215011b184403035440a400c54041d1552103241c000386c2080c2860103000941200000340c00641ca44940d034152400c080c4111456044030030080c44a061660340c84001800070b4210700e40400005910300c0017000740800203804418104000351584506102c1c00030000d05050f8400c208000206403070b907026813004140203400c650026142e80d41c945c0d403034110300790b14410702442c281c2209002511452055001c544c1c0800c41c00242e8955403003d555010440c1c424 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7261752 1250 7260502 7260511
    0x806030a030504140406030506070507030f080f04060e010b0402070f0605060604060c0b040204140c0a020d022103040203010b060c150109140f060a08010c03020a0e0a03050303010b1803010510030203010b0405 91
    0xb00204414081114100841076042d4402040850141d40300e55400d42450400c0c1d8180c004a80c0109004003019000505140c0c40c1102d840e141c2401e1800030010780c6003441c0034001400690390343c031000aa038071080d08207045582d800341c0203540c0c40c00540342540c0c0e200340c60300302aa48640b07000085045850141c0c115001c95001e40d881049100c02900d843d4a6040080d004980c000d54512040c0440c003211003806100342c003250022070700e03104401c201070300340a0321140b544110341088000a0506112400d80b81c00a0741c3d4000094a079511b82c40801d0042503240c10480e800071b000710b044580c0040014201003482c8100200c014240d03a5510504203846c080090380c0030030b8070000002100c112510501d203a200070003c10031110316136140b1b03c00f400c454800c0c0100d0000b90b00091010342c1550880a0608540019210b0b41141c0340746031a07803901d901060107210510500014854880d9581005003104158002d00801450400010080000312103101c101d000c0d509049002c0b5031440c11703121f039078400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7263002 1250 7261752 7261757
    0x3010203091e030403050709090605070206010b1608040515040503070f03030e1201090609050303010807051f051303060f02071505090c090712050a06080c090103050705060306130c0309030806030a03 87
    0x14011801d05801e14002ca069151101d4801400000040350080044c04001d00b00118005282c500e1f50078504c080d40c0b0000c10303590942d40030f00c0c010003036010f0403012070340d105030404a0341c1c01c00207140c5810729103441072303601150f401002e0a500380c1600303d07608010422502c0031011030707540c181e4402503610104c4052002401044040110081c2820200d0720507204807980710000565904550b01c400c11100080c0c01954141d001100600c40004108a25405030004990342e07041c9505015000b281c05a2280c0b00004000011408854070421005040041c60f880142400340140201c1454000c0d0480c6034140e90b0302c890003d00b25840d4485100f100d010f0700840c8040c1000603104804d102c246040a44590100600c3d40c0041090046c0e6110b007034082d00d46880042001880e15038550b14183c4d407201c40a125103900001080090000940c00b4110340301520013075141e40d80c0350005003135180c0350001c00354514144271044041640c9030740010f8503540300c0c0c1c50344140c5450311418150b0319010750000401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7264252 1250 7263002 7263013
    0x61015050f0a03090203060f0a05150d110307030503040308030708070c02010e040b0303130902180102120403060902030a02040e0f0d020c0a0501030504080705010207030504030317070c03110109080a021b0301020309 94
    0x207001800000c250030185401c000ca09000c03036601081c40c0c81e400f02c1d4072003c2d00d4101418880c03200d050780502a000034844569002c50703070108001403040e000c0c4040040031016844000000c548050010500a5800400b030742e886a9a9080c850b2030303940f0403a201c400141030300000038105809604c4c007000294060b50741c213182da164081403100420302181d24681c1032006010004a50a4040703825001d401088000768582903a501e07400b03588020042171606541040c0c10080f6a14402170598080700c0e00244003007000c103454004242840c0541101a41280c280345101051a20015011455000007000c0314400004030900b00d07181c1c42007255603540b0a40942c020040c1e0341c4207800c166049030280101c1480c0c00200d40d15503003203074881d840880124001060070814942c22030050000744015100503040c4e45880d190041044141d28030003000c2c080585100d000942095000506071540040c0442c1e441d00b01c2c9101a503034070440c155000e1030b4480000c40000c6d904041c001d8a0081d42500018003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7265502 1250 7264252 7264267
    0x60903020108092e05010b04030206070803100306020307091401080c0316050c030703030e0d050c07090f0905010501060e0a060203130e04030c0602030103030c0b090105062d03010501030506101505 86
    0x6502d4400580421114401c0312100b14011080403114542c0014500c0820441c08030038602e8015541305070b0119801100030b00003040907031101e108803085180d000919690b01e64400360000f070300401581014141520110800040d244c0080c00d01e03040d17130034a10710340c4105030f4244011101d04904a0303d42941420a10114210501b02110180c86120a007002c030300f084241c41e1064a1500031105c01c0e400a03031a10f0f01c050b03090f01c2c1441225101802464103e10b030983c3e0250b2a5a142998403883c00860f507650340da9031000f12141c1c0b04000703a6034007000034049035030f64800040004152501c03162040101d010005901d50001085908409154491a8040380b070507110725240d14005005600380003000c002c801c00518944021400707140320f500c03251080c3d04281001d24100c0d100a088002c10703890907040c440030390395071800303c801143c40340041540310140300000a03480c1480d4442c5030300f560030800003104200e13010174a0352044a275150310000d03c617680c010910032011680c48000110301c08101c0340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7266752 1250 7265502 7265507
    0xf08090406050303160b07090302060c06041a161809050a050108060106021b12070512010e010c0509030c0f040b0301020a08060906030105040f080306060f0a0c030e09010f09020313020904050a05160609030201 91
    0x1547e20620394180b5244265994000c10404e074400400602d07590072140420007086200702002001e001c1c0003105c80c80b185041c40b44119a4240000180b050048090b100e00681c008904000301602d10004240050f0800241000c00b40400380103504c0740b80596800490418400036400c08030107080403070031203030003105414418800840d103007002481c0074040c00807943e5240e082061180a03034041c000100210310180c95030031641703203281c050704005040019021036600090300200e4858200d881000c401e11070000100106000301c0b43c180c15500205110810640018910f4442c1c03000340e1b0032118030788c0d80380704041c200c2c1d508603030042c00314420f0303010301d000301e8604409194042005411146862102d15401110b9001300c6441c0c8009408041300004241e0b100c2d060f03555044081d50f04020719418901c4100341b43c2c8090103035000c06a40400013400ea8128007600040040d00039040c03180500b0035092058680160b488159040e10489606000c07651003809140129075090307449000060456004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7268002 1250 7266752 7266773
    0x703150b07060f0e030a0306060e090a0c0908070b180f060304080304060b0a090603110102010504080306040e0717031308070501020a06050405030c010507050405040608010204050f1009030f0809040605030316 91
    0x50ba4100d40d243e4107500409081e00c0350102c40d205680c003c5880b0301c001d00e001000e075803540e00000e0800610405264480d201c2c8900650400c3c03000c4004922400d02540c00c560426103984400a5440b900f140001c20310f0040004000603484800d001c4004810041400b64075000c0c2003071960806020000200499041400346421901c0b4070f030f000c80c500e199440028a8401d1503085228840d1340c4003002c00130004000080381800100380001d00152401d911014a140002440307180555140d0401c020360344810300525000c2d040103000d110fa003419807028244d0741d40014600a141011081d0041880da0002a1510031540160f004103e508903076a19100035140140c41100c1d64803040c4450307110040d0a0007028840ca04955440e0f0700c42c1c0c81c0c04100019a00503601c8070009910401051110342c0320a0460340c04801c0990380801591810501254086540d81c009010b8004404c1c808041142120007444860000c60301404115112020117840e8440c69002c0120780992074143c40016999494 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7269252 1250 7268002 7268017
    0x702041104030c030b0708060102160509090a0804090501080f0a0b0c0f04080a030e01020d0c1a0414060702010501080c060f07060906060810020903010c0f1b06150305010b01080703150b 81
    0xc00d08140d03499030380c6003100096800440e1510288030400c000c0e160301490041d0300100910040c2200c01c0941d07100001c40c2130314020b641c0281030a00004410402c1040150031090344514419a102d0780e503031811000349000e00642030341d405190341c040c00078400010b0300d0300450340000951aa940b10700a80f110b00d640030b013880c111044001d000c00108040140b08002941d0302a0700c80c1245481c00800090515000340381c940180300d50364800f5004234001f10325408071086a40040309241e2a5400d0078180940240002a46842580204881c0c83c0c0d041d0001030488480404448040802c2c108000682c01000f40710401000300340312510129049030400c044041c0a000e00095050f1100b0105041c0510304407521403040e00021284641c3c02c0910541c0306107502842e00c041c0124010303500030101110102c40300100066610608180441e55104255846081c02a80700709130b030300d00e0a6400b904903201980d000c00c0940740015011406401100107078203082109801e800d01348141207055410081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7270502 1250 7269252 7269281
    0x30a0e010c060c03020d050a060f0308091504032004050c0a030b040f020d0b090a0603020604120c080d080906090d02070b0706020c010f05060a0f0501080a02030a0b21010c14070204 79
    0x1009407011403240e218602c036880c66a6005641c40c82e03581d1006d006c0d190041e0002d0003140c5072074810421540031045003022360f0350100c80c4d00d0b6503d07028800030b0020704a01e0048031807040e0005000040180c80385034070103005282030742c2d1140d907904842004200c2d2400c48903814007040802c110b00041e84207512a03120020020000614200001115802c80e005403100c0d40030103980302c5691000b4035004400070341c05502e4000600249045a0214686004500c0361482d15080841c4040800110092540140c049103085406801640360014500d0700c058924921078080c803404105080c601148084180702c1c0d036001010081e1610700c0904442d0300c1204180c641c0740d401d00c07030542204400e00075030520144510020441d82005002c1140c20100d070750100c24040070643d030130840c80e40c100c00c095034410200300c80140caa695411070fa4005e04103040080e40d1001c0d8201d449140e008261000c40001400300000300090f9a8481080d41c4817040c1940c03e44d0301c3c4006120800052800d80c100c1e009500940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7271752 1250 7270502 7270517
    0xc02090f04031704110307090b060405040209060705010504050102070201200d21021303120206040b0403140c011b0f0903030203091002010608060a06060206060402090d0609060e0f0106030b06090603030a0e01 91
    0xa03603400740070f000b050314200c519040b82c1603484203618080061030040d2a00d110208008119003001840c18401d501c80d46010707940105140c1c0445c0d0f00c02c0c064400e031315007200007840070746451b150950003540104d10882c0450010100c150540c041c10b00c02c1c65007050344e01e0040600305440c400c2580c0d160b5002000c00c4801044640003140030b80c950000d0030390305041458514000e803c5181814402c00a0540e520840d0b20100400010541c0d43d1000f07500300d901810b00e40d0040d44140e44c2c40b00c1c40d10820111040e02c1d820044201c402d1942d018100089014a5881e40d400100c0920100e900001031b00c03024006030300030b02600c0c26615007609640030074446400001010b83d0780701c0c1040c0c24020111841454155145002c000d481c0d018803001d50301c00f2045038214a415034074800610040428017018110701d5641541d14108586a801130380010400c908a81c1e10f242500c1c101070281100c0c0c00304441c9104410086031160615000250040d000240514103006418204440f6080c1c0d1405075070400128 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7273002 1250 7271752 7271777
    0x2040b03100f0e0709020a02070e04020a03020406060807080c03010501020706030213030609030f0801080115060302091203030c09120d0e01050d06030b0103030305011d01051509010504030c0902030708070c02090f0403 95
    0x184200d842c00c80d0000004a0500000080c0301d0418440754070100c1c2c100e004114141c0c0441c3c0c0400c1c1d9000b9119401d180c0ca10b6529a0f0012484c15441908002c2d042072500d88045501070300988940d01c50b0f02c99a446070b00565801c4408440e03400207100e0f660260344465807d00c40140a500035041440d00740100554640c0d403a22140d003078601400040d000b01d03911500181c0c000d0392020300103000d4280c9100a0140f260310320841d24200800e8410a81090742c046004403c940e40c04e0800303041d461000c0d04994a0341042d4660400320384c805242c20b8072820252940055034100441c0403413400d2074035240c8030365810041c001035526a211a00947d41c076540c586000c800552405402070195010b0303a80082d181d0f06100c080c03007500c0e05e40c49c000065a03011400400440c1ea802d101c2c2d000d840d881c6200036446110400c016600350183d504000c2002102c0c0d800440c490015a001e58410195a5240300194a070310034207070b6104882e0034010307400120100000340c01c0d980c81c11049411600c00d19002122164 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7274252 1250 7273002 7273033
    0xb0306130b07020106030c060503070309051b0102010f050c0304061d070603050f0612060a0e010b03030409020712090b090402071109090706020d0e03070311040213060509041a060702040b03 83
    0x1100c40300d02030303450030403000d050020010301d441c1e00c00c006000801043c3e04644500c0c00503811403180c0c00030400b0000020b0300741c62007070b004540110f07804401c07a00018035440e6903513203101040c0d100e54010f40c0381003031300b560807a10b40c015180200f803511070007891619580c1741c2c107000d045d21f010f040c121110803401418130728804008210041150360303000542c905050325110a1448042c001611951880c5079041e2080d00100f80d1642014010200141d0042e59404ea640984620302985074035000c0810005201030240d0014413801d44140ca0074003e0380d0110906846000042c0036070f051a91081c0710502542c1041e500034a120750180c011980302d94443c1d000500e101800321030741540354010719410441584c042007a0f840c1000c15003002ca410b141e41d5008a50b644025100c00f4203207152548050072140c85541c110398405080590784031505848000142169200e031031180e0190f0b1914606000c40c40840c0c2e149904140014200c83c9011142e408200c050410382941980c140101c010f00c806480c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7275502 1250 7274252 7274263
    0x90406090209040305040e0a020c03030601080414010e0a0c0603020301060203030a23071d0103020316031d03040b19080105061801030617010605130b0d030c0c0506030a0203090105090d05030106120b03 88
    0x10304c2a5603a5984a04188104480310070180000030480c0c0184601c02e0104404406d403030307010100780303000062517071030342402211820002c0c0001025407034005030005c03030840803940203480b90098400c00d0b942d0742d407030710110202e1000b40300c1c00340103070001c1c0007140744664942c0005544110b09015158401d20382a2907000079142511098089642240340201c1c0c03118020580070140001d00f011400c500c4c010000c0c0600750b034080402c0041640e50707408262070100000204800d10a0345040f81d1305e4a4445616032035640c094840143c40e21242408107020071f1040001c1070503500c004e40301c10308048100000c980f55142050425051503202c8034007082408a00a490b0601d2010b600080760b100d00e8407003441410710140300ba03d40f4103030400c49030f03c03015110740e02149412607142c0362203481c0b4001400c1206400f4030f1078104640c820400024441c000310300350003035405a50148000c02182c1c4440d1106940e035101101035030042030062004000b03050003140c44210510b203420000c10480034400c002811311 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7276752 1250 7275502 7275511
    0xc1002031003030e1f030b0613151704080702010c030509030d021b010318020d020604031202010b0108090a020907030c0201020c0307060e07060c050601120206070203060403111204030b0105090406090209 89
    0x7410402c20305070320005089240b1001e507000d1041c030404502503488101101804411b140d00c40030b030301c1c0300c0703844400444004042031410f0441080d107c0191403515810303000c005001803130628502d041520140714a500541d48489040e261500700e03030042d61010928102902400f0003840161010b440610188001080903030150842484141021888ea01c2c1d001c0c849042500d4000c100100d420040f41c1140c0480c1c04540d040000100d510004a603840717280c000806484c4880e184094140d015045205032140980364040340d5603400075001e40d1400343c164007030f42c85407900010450140c025030009074003261300e1001625042c06240c0052950f4031401040391029521b4442241068042c004a4003805943c13401e0345001480352074a030340c0c81d030040c0607040d006440c0f0601c203c1196a40402c4603107080d400b50a80e40c25181c1400d014003526001a000a80c43c000c3c0b500c0000c0729002c14046030306403680314000b140c05034240400c0c8090a04000c108035a00b45da07035000c07003001da6103030503415114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7278002 1250 7276752 7276771
    0x403060507080403030e03090a05040906020705190b010b030402100309020103060b0406020a0c060201060807091815050a050601030209030726010603120315030804031203060b040b0d0e030405010c02060c100203 92
    0x3e003810f00d40101155062102c429464105000151090341e07000480d40c11610121030200d030580715803c080000b4464160000d05038440d5040f24141840850a8410400e000e54002603060307903070391104280c0d884111030080d4010301e404010400c141c000d0307001140c0c560043c0340c00181103407140742d140c6407580150450170241c1d10800028041112400034800905964070080c850140740a4071103661714818040c2000a07a100c64005150510000382454403d4000b10440101c01c464036a400051070700b0f80356504001e041c680001c806500a0007142d01c0044060003c108140c5000c04d60520a5150414524500c0d0f04425004a01c03009006001c05180207a19030b44c501d101d292005800c8540503004d140d419041c006003000807810441c1078904030fa41091a030000403020f14000c60040802d07410143c2001c0c00800c0110300c0c1c800d50006031400c04809441008860000c9500f6540c90040d44a507500262464280500504201c03010b80b40303141407401159513059002945005030381044920401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7279252 1250 7278002 7278017
    0xc040e030702040501090606050a1419030209011115010510110d05030601080906010317031f0602010b0102070608040803071b1a070905010f02250302030105010f051503090d12020403060507 83
    0x70342c90f2910480c0e0041811000c00c116503450b2540152190046c500c0700c80500032905802c26180f0084001c940030806264071421208401403030150081d0040300d041800122084c200d0b001c80b0348000b0304000c1032480c54042c40b401e03a10b010308220340c28442202520030000e110800540051040114680b000015100d080c0c403450100001401481d0081814082d81d02c13103001080030130201c2000c254000c0d1005a0241c2c0d81c2c0d201a2103181d6082018554507445200c80000241c499066015125140c0b00341d003503030a00350307032014220f0340e0302d40c10740d0060f05a090400101d0240d0f03002e20b02d03030f00304580c01201c2610380540c2030321690800e003c258440c078079100c2404100483d1550004403031000d000242407140010310020802599452482104052007081c5504581688100700410000b143c7c0200248501d42c0c4805110251001601c9824001c2d0840040303d140b21160800b41c2c1c1c801d4a4503401044801c01003142266110190341140d00429030801000c0701280841c040c451240707503151603151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7280502 1250 7279252 7279267
    0x9050405060f160c021809060108010608210711060408060103021305040b06010806030c0411090f0a060219020d02130209130c0e06090301060b040e040309050405100509090c040e03 79
    0x81c20000d0041c040a00b01150384204000c400440300811140001803074140e00003002840440c10f940c20312040c0e8840707000d4020801428000010b592810707601c81c80001d00401d5954284d00b913440788110010321200d000840e40c01c12045c0008013504896006003c6a21420303664030201c0c080e41c0c800d4001d038803a500301c04c0042c01503080c201400200c4c0c01c1d800c2401c1041c0e103491f40365159095806840300e410020864003003600b95808001000b2042001081000803c20a00543c40706070f1188a401d8000c41c0241c6c00d0b40442c1c41c110144000300d40a64002d810781c40c5441800c520013008084003240e1210b100c101601c00358640d900791241440070000d00595808502e030400140d80101810120700c1070500c0002010994410140c00800009644150310340d91510f000070301400154200c00c07601d41e801715000039010220401c10b40140d009031641201952100244000e4600450300307004504864001007025041400645034002c0c151002d490490402d20001015035444114200e400d40c000325624 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 7281752 1250 7280502 7280513
    0x705190807030806010e010e0d020a150f090b0f070308071101181a0603030a030209030a0b0720030406170a091401050712050603100b01120c05030f070810030602090307050307090504 80
    0x1581007102400d0003a117011181b0b0000302a4491500100d00810300c070301c0341c0021910f501015002030060103801400390300c8240002400c03500121440c800040250800080018076142213401070070325074901e203141c0b902640701501c0350700025094408020380c0d400c0c9162400c0d0280b0421040b5250a0743c070106030501810511202c0300c14140c43d0600c10613501c00d0050300d40d000022560101d4440c1809030b107a82c00d0b00002800c00003c2280607100707458400070032200a41c45000c2c1410511f450154143c58036942c6e40302c41d030324080c1d8001c050102d000c0c81c5080e140c480500c00400e50140c0401c2000c80e121a81c3d5984860780c9244484c09002c5a4660303050009403074103e02d881a001107070500c200305500d00b9000080e92200306000f81c0c81e150341c3d034201c00111a442810407030101001e0203800c0c040718800120040666200f21400d20010100c0c40125172018840d01146000d14058141106102c0c1107880360002944207840761641032155010010702a1002c1c00041c00428445000245134680390070301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 7283002 1250 7281752 7281767
    0x30a08030f1501081302120a0f050604020301050705030405071e0902120109050106020c0609060307030902120607030c030e0c090604020415020f070602010b01020706050c030f04080d0f02010b01020a020402070519080703 96
    0x40303d05100e0700702c040028000e0004403144000380c045403100390020105404504107948928050810000b00300f0340410312200003400d40c01180b00b6802000555a40402241c43e0b00080d1801815170b006028104513520400b0410b40007211442e9021109640c0e5540c2401264010549101561000c07401000b040c00301d482000e00409550000d05150280400041c5081c8070303c3e146a07110f108040081400070b07100e6800310340c0855000d000b014103100c0c415140c9540c1c0100f2100c40340080d040c007040d482518400d00408002601d103030f00504030440914204040d40314020645a0400d0342030000041840d170384580050000f0b103d401400c10066044200c0341440b9480d0880000c1d607050030010321103664000f5944e01100d002e40b8000f501c0322440205241540304100c0e000e9118880401c02141c44400402c015450700056111040d000c400071345c040e8280c41c01d03420345c140946c0103c003040015003441d0300141805c0d80305805441c03020346800c0041c03001200306802664400c101042d0b03401050f400c4043e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 7284252 1250 7283002 7283041
    0xd18110102060603030a0503100906031416030c051201090204060909050c030d0504060804030309020406031101030e0a0804050f01020a1b0602060703020301181107020409080d06170c040506030a08030f 88
    0x181070b0520b40352011a540384216200d01c402c020b800000107000d0f100d00503006020f0075070a8003c0c4482903580c00c010803407009150010495010311066031030403480c00c00e843c03c1100d42c0490740d50800ca180030100941c124204411804c555210b503220f074010381d240d12400b0041c00054100140008050810074078080a074580d2030f0195012007003442120b5000403c1e81e04840491500315110b0351280b03012400303000c040600a4005041040201c01c1069041c0440034130380081c4d804025030500a981199165450400074219503403c200074404d40c1041111410b0840041c01121500419569103c0410500c0171003195038425000c0c050000b25410302085400c0140c0307280540c02c6504050000d1006150541d01100c0d0b01d5440c0e03200e1800c200024261646190020820080c400260400d0340166000c0c00c0c01810903460041e0104070352301180d83d0b00c5011401034008002c5444450140402498040c2ca0213a144c8103005400f000a21140001c43c82021000c601002506001000c070050750345156 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 7285502 1250 7284252 7284257
    0x6050603090a0b0601110102070c051c030c030302090a1a0403030e09070915030e010e01150b04080a060203060f0a1e1401080403181203030b030f0a0b0103060c03020d181101 76
    0x78000c198a0000300011101c0d040910054a5101c240060318000c281d11141d13201940042011410b0005295124040742c405a94500d0802e41240045024181100c4003d011070001e21030307040882d2203680544000705010705501c40c95a260700100102114104071800100e00000b8140b04055000c16202111802900c00040c071382021040500640070500484000c601c840f1a10400310b0f1082c0c2000c03e014030500000c00054000c2c02416003e00041119101384122621002500c1d40d84001194211403841c0d018180748043d95948501941c8040c00c260342c0141464103c00c1d15581e00c01c080402428220b09803219015000d055a02ea00000e52280c0364100c0398021545050b41c00502480d4800d616142551080e1705034604030100310015000b02594010b6411124205030305680b151641c02c100f20101e60840103130b0040d040c1e0781c1402e01e0000708110740890041000071420f030080b9401030000d00b03000d4100b1399581320400071101c9a88842803c0a5016101000d0110786104104210b00a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 7286752 1250 7285502 7285507
    0x60902030c012303060102011e092112020711060406020709060b040e0712090c0b040801060b030105030304170a0b0708041b06020303060f01030b030d080907060206040309090906090605160201060506 87
    0x61155003076040c4081c0f01a09440d20002c0010400da00c01e50014400c4580c0d0244d2104640f4064610001000000e0040350000341c100402d1800700c14905906030b1a81c100d51312442e9000d0582180c40181d000405e00b181c03001c46041080c20640c1d03900c4003800151000d64024a0300515041c085403d07501244e0100721001c104220600c28dc2d02c02c007002c10303407055081c18900020a00f400350a17000f803902e1035000d040f405003487c0108401d40c07004006d2007291091002484296103909104005220070310846516a0042004021038100b00d00c1a007038404801069545a02440d00c90004040b000c40b01000020b10705410803041120701600c42d041c2e01a01c8108070340a41c01d10001a58a10003c1d10503403040f0300c0c8001c01c020580c804d030401c405602d406001d4a00c101d44903c0c003d030107500c040d1181580c80c000e001010407541d20000d103044c41150140d464000092400300400001c026544050ba09036489203d024040756050084502503850b10070212080710301014000d00b140d505800051145004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 7288002 1250 7286752 7286777
    0x9080304020d030e04061404110910080405030c0105070f090605030f0103060218030a08030702190803010b0315040216020906031f0c0203070b07020304050108060a03080d110f0403060902030c01 85
    0x29664466410385030190010b9103401c0695070300103030010095009003495801703d0903446204016801c03100584045c03040010014400d042130140380380c925000001004040d802901c503440341a000380c0500282c0b80340c0282c03900c00318251030045481e030300460160100d500d000c030350001d0408010280c6180c40380c1142000104100342c0701042c4405400c3c00d402141c0f60f14140c100842484241a008044132080d488901d410869600100e1f4107201502407880741182038582c040c0186081e0340c0c02807056203980e0808402c8541908003600f4225105480f800c082502e403524802400c0302140a82003140420044c8100410b810000f032459010307400a1181d9040615a1509074000f480c0900c804034034000ca4020480c5140103501010f4520000041405500b540210060054450a99400d5160340c1c8220070b20222030100d1000600900007000903c80d002c01d03a030701448000a40e9105da0703203405150a8442842d8216800580b09195035483c00411071400f0401071201035000e080c5581001070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 7289252 1250 7288002 7288013
    0xb010602120301140904051213050a080102030705030408070507050a08030909070e030a02011b020307060804060f05010302010f0305040309030b07030609050604060302030c0112020405040f0c02011409100902010e030601031406010909 102
    0x75204c1945020310f84501c00308007081024400c504680c4100c1c1d50443d00d0780c8003d00420000142031081a002d10710450010802100600869101da5119114180346031180d03640d5181d81d0340070b080c044c0d43c80c0c0208100880c0305d50701c42e903507840102500001503440b94000004c104c0c4c80800603101109004507034410702c403035840100752051101c0c1c09081c40c3c4070541180e402060903000c1c0c8a002903040c015a000410401d403c08a428000c40c040c1d601040403114aa401004031102030002078080791180e540030001600c65042140c0c4144640740a080441d601d07334070b0009840040d111000401d8071140c0c1072001c010144070b15940700e034040704c0030312003540341d80c001c2511804a818514100180b061840d200a98650100c070000d00010f0401c0101c94003024000d40140b0b444080751006500307042c82c8868038000303520384900400002c0c002d440c988040c1107c041c0103220b041e500b03c0c14016262504c00203176409220480c004d6004200c2c02c41d45009000d41e1a051000503005034116500c1e180644000c900c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 7290502 1250 7289252 7289279
    0x10504020102061503071701050106020706020109030509091314010221010f060809031204030e13020319020a09031401020d0501080a030903031206030206160606060e060904020717070b010602120301 87
    0x2000e0184e0240b031000644082410300342c0d0b6030085801b0580312002c200c0c0000d415400236041703580c15403e4442484c0c1b1400308078241e8210780000b034005041846854070300c3c0750401801c0c3c2c20059649050350074004603030390745040744c50084610f1040d0354041500d0000b50000100e911407019003500c07880c409d40c14850407040a1445025110812842c00009a0104000c00444544c4a12071217006802c5c607081c5001003030810b181580a00a8107480c10911007000d060003035034094008c0003190804820406151002504254044d400b041100c1d1000408601005d201d0f5414024881c0096030310303a041441401502c0b410b0b0700c549055400400d00c600481d80c404041030950754036203005a003c6035980050405040c2c160006580403200089035050301c1241a05260030a1140505001240d03036004141c440e00c160005441d0045003c07c180c1c9818a800e41c010311407280304148400c2ca448180300101c09980220604442ea03591100c0140580741e0100070181e01012101c0d045880d5606040d060100309 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 7291752 1250 7290502 7290511
    0x61401050316170307050f0a06060603020a050a0e0609060406050903061602030f030603150106030c030c05090a030204050406090c08100506040b011b050a051006050f06040e0c031305010515100201050402010206 92
    0x4101d000ca0f140310406000721580d03603800c8400c54406104041c0c105484814402c0f00311a614074200d00005e00034000e00076500682d566841d800c0c1001c42d40c2c2000c0da050102d8050195020350204124900b558481020b0070142c122940c85c19101c00240091618180700500301428184a040e113007000554000208c421908003400019100c0e200c010100341b41c82d03c0051480c5581058800110b2229807542c40348049094070755007032000c4800c001094a142c805d401120f41c008503a0b84041c07000d405c003a08a5600103200c3e041c005214405900ca1038400320131a0805089a004060221840549030042c607070003c00c101e4040200c213120400282448041d140030f0359542150850800500c442402007420468100c010380d0800702140d4180001000f4a0280c2d0b48500b8011816041d2401c001d070650301a20203450250300d003500d400030700c41043d40004020300c1070b0b81000210b00c00080c20070301800c4e000c0d180550011091044040820031055580c1d42640210781c901802c01c00541c2c2e0009026420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 7293002 1250 7291752 7291769
    0x3010204120f06061208180108060108010b0a05040e010b07030908011e05040510050406020306180c030a0b03120d020403030806010503090a030e12030304050a0203060108060f01050f040204080109061401050316 92
    0x216074a40b182c050180b56000980c0e02c0e0317114001d0814000c105004020902c1c00c00360801034501c9540040d41c8414003555106e000030840401030100d920341d0b00080c45020002d0504a04260f90b403070400d403800e10b098100200544000c0380c40310415800503040b001800b0034100074410340ba0100640c11006083d83da0150503e91980081410b00c0424446101c84a07030600090045280908080d000b0f94401c0d074007240640401d1220074050310ba078503030141c01802d0300b542142c550341b24420800e020344402c1180983c103019501e040b00801080c0300003806240c0d1810005030316a0b146040107801c01d04018030a80c103102c01002003f10301ca43c0481c80703020b03283d0705043c003840342003c040c04129044a590784482e11032000205110a2060004210143d280308500301c0d6a1681c1391066503486244c10798040d0403441d0f003200140418a440031f00a00111406040181410f64584c042401d41c0c0307110f04141d691980e6141c00744940b9180014403805488117600400314000690705d040100301c9a4842d0900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 7294252 1250 7293002 7293023
    0x120606081b060f0c06040c030b060103020a02340305010e0606040204050d060c2016060c02060403060902060f03010b0c070603020a05070201030b0a050301090803071205070c080901090b22050301020412 88
    0x700b08440605031342c403002c140400c95040b440c091500144508090205940c0201e520002503c150310a0084400c621504c1c0c0c054100c00d0000d0200c2e601003c01d001c240044100000c403021251603440034142c0065015a0010841e1030825206c40d04240c8082d0202d0b000e28010042409035803184d918000f80c09900500c001190110000101c0780c00490f00e40300d41c1043c220805518618100141500c44010030440310008656154410f84104190240007034104109000801c0400d1069100013030443c0003801191402001118940b6079030b100360002c4060241c00b080c001208482004003e014060a007400c610308100b1080140c41d42c010b029001341015141c00c50011036881e160035810040030040c00030300902555140c01c10050300201ca10300001062502c0806201209024143c001d036059268901c1541450321051555800300075024144885c100000500e40c1200009000b428880d0200304810303602c902e2460703401c40d61680058480d030f00500c03090000113034443c2142031082d4131150020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 7295502 1250 7294252 7294267
    0x50603042301051f0801021e070804120606030501050711060a0c02010b03030708071b030f080c010b1306080d0c05060105010503040f050708010c0306082a031006120606081b06 77
    0x41640d400740d100e1a0350b03509080078003002821100221311403114041c9060142501e4200c000e08034000c1c43c19031910070b020814142c3c01c040d181d43c010000303079000b40881c0303140a840b503001944c2c5047c20541200d84a2f1303260410001e10200384034403a005581d0b0b1030011300c0491001d07001681e580e005170100100540d00d03960340b85c415000b5444281c81000c00750950b52200c12508044c4260b812039101640d06031481ca035400c01c0700700d140c51150305032640500003c1070410310391500d504940200c10206403640d6591410b081d965118103101e001111070180101e40305040c02055410240070020110900c09032201d4080041c40c00b194043c19942d080c686a034699031103007090f401c001c1000c1d0001c2c203140110000070a400e03c064020041030741e0992420310009036902e203055031381c80000e4140100f0101c0c042e5003100041d184440242203080041c12a903050f1403c8540b80100d50340c540c0561003a012100c03010f0100003c88c02401c00401844000d00400e9209a520b1103813a8402948148107040003d5040f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 7296752 1250 7295502 7295543
    0x5070c0b070201090213020309010b0307060c0605070509040e0105100b0703020c190e01031109010b0c030307031104080102040e0103060c0201050601020a0f05011d0a03020c0303090102070e04020a05030607050d051005060304 98
    0x4d40d600e030000e02d045807a80c018100c90300294410346805400f0b5003002c030105818200020702400301c3e0b444c0c2d030ba00105461561103810043c0000762908003004000c2000401c40d070f13074a00456100d40c800350300019084c2000a80c0f0901003008e64407083d8428800e11800001c2a0041503d40d201d40040c0c03600c004104404007000028403a58003c03805120500d07001106000724240c818007071502c00d48480f0901e90702c03800282d840f4041c1c4820a43c00d6801000082c000500c2600300c9201c0351106070010341416141d4200c00e007640c2003a0000350075503900713130300400500409020320302803000c2c0e0340020456810050700007074980c081c150001c0e00c2a28054600810008254080408101e881c1d51010254110300003441d12440c5d2141c0a50052062405201c2c051601000b2203122407016002003144502d856450885054000c2c81a80d0018042c1c00c0000d240d02c050250350f10800d46541d90a543c0c0c614203440c54100c8401401104081896183c1800789445042c100c13070f009500a030390141c0c912080c1000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 7298002 1250 7296752 7296761
    0x30c0616050405150c0a03020f01050c03010b0307050c0c040e03120f060a06050c0a060203012303010c020c040c0917060f0a09050303150418030203040504140903160203070306020a05120106020105070c0b070201 92
    0x4503124440c85140301e052540c0440d4619272185110000d0003143c40314881c81000340400e0140c103289400c20004244c0d5640110b0061074103441440960312500e1002c80000c040f500741c0d051100c031a400000346015141e003140d0526070300003941403404a04d03041a1000c140c15a03498040c84050160000c1c400c00301403000c1008540155100d84203660720f40e1280e107804001c2d0008501c4841c40c1080501c648480c3c601030141204440c00c1d50b0043c100c07480000300308030240c904407a200061208803100412804003040c503d1296101c0d8100901450810110400b1130200c02007085001504d0485c030480014408400c50f038020200424182810860700300140052080c4000500c0e840982100c400070150080060300c21660f003141c003080700b50300c2449551040c138400c64054050703030420003880c01641500aa44c43c2c40d00c0c00902120300040d204d030346203000c80e40020071010100c3c0f00410340d0300880c04054070840c003600852000b446142001403015014802c0044010304040c1010001410240700350700 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 7299252 1250 7298002 7298017
    0x4150e1302070804030c080604050a0209060f0409060605090705040e010303030c0905060c1f0b0a1208040b0307032a020307020d0501020f0403030315080d0818010b0402030702030c061605040515 85
    0x3011035503501d0503c1c2a81e010341c014403049884a1185000060188010034024480d580002c041e05910242d503081081c0b500004041c0d6511201030104c180c45602c2d18403801001c40c1c403618002829030b0a00c420446400b1000744081c1c1048410803040c000101c2e40412541100c1d89801c1c0031505000780c940503903050645400c0990005400300300704402510000e0040b42150038400d40d441e080b00c854044070300791844141c0481e004080c0200030000601c2c0e08905a12540c000e0b8400c40c14681c4820b88106140d0043d01c94600090b10b03002d01001d034500d107491403c0746008030100126101c0280b0000303526805a540c000e03214811601180c1d0901c0800c0d0100c038400e02e02449426501c0d034481c50050000c0c04121240824944c040102096112001a2031003c413542601c40040c0d030340d1000304030160000c000c3c0a14095540b0340040100c181c4030f0340041d60103012145c001e141c0390b08078111000e10340310000b0060811400744850758410180c000d012101a2030083d207280c0c41000404803020410301c101c16 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 7300502 1250 7299252 7299289
    0x30b030703120302090103050c0405100509030f010c08090609030a08011203090f0f030311011401050607080921010c0306051e010207081504120507030e010e030c030d03020a1404150e 80
    0xb000501a1a0316034001d202c030300c5007620200000c0d141c0d18003c3d011405a4025541c000400800c403c2e01340380a1400341050040080844421901c1e444405003076942906490780030030401c005004100700d0600c0415070140c2141c0c011418054550380003031480c14188a41f00016081c24082030a0500c03940d5240c000c0c01c103607030301c280003a41d8900406841d40018842540011071505910380750410600405010300d04418001640d0707400d10040101c103034404803003110003160030061180e041e1241002456200c000c07072042d000c41c210327a0744a14207451444941c4810580707401401c1c0682c1d1780c2e21102e801501e103c80c8680c00c45c0d50303038900140d01c1e2a4140e00b10f1413640c40303040c601c40c6003006a641e5851066100700b0446040f031b400408203840a0040d0351008000c5090300400160b1135200703410300a003a0714020225120384030f0003070100c4d06002096072800002500000e000c1d845540007000754900c0510304019502e000c0c0380c0300705018020a02c0d00d29100b00440040050b52555414075060380510380308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 7301752 1250 7300502 7300523
    0x90507020a0f05030406090b1204060c050c010c0903030e010215040b060a0305060906060411040e060607020a0b03041203051003150507021609140f06091801270c05090115030b030703 80
    0xd0520f9a6a500301d44210350000e00c0d131420120f01941b01100342c50009442e040d400d206625183c0d9550041c01c450310701c400c1041414040c0780c003c0c100074040c2518498032905d81c0c0382284c0c2181801030221341c490501340c3c1951b0044105800d8001c407154810b03071050704041012200e840e0780380001c000e155150301c00b41c41d80c801d2200b4029040c102003955801070904490800844948020300c0000340201e1040040982c203400008225041110091025034402000602115100d440f02c54a42d0020388066a13043c149030705590351550548106070308218404250030040703143d41d45d0442c40c0b403d0469258070254582d004140594002c0010300d42c0c42c05802c4c140b040980e20f9112a4009104080c04401e01e05621400300d518002c403402e10b58000c14014100c480b240c1e5404161000b08550451600724665845135403540c95a11242201010110030612a030b030b0b202181043d8058010503042648900080d400400c120704910140c03d014801c9411302103201803003200002d00304455903201030002e0180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 7303002 1250 7301752 7301783
    0x3010f0e1e01050106080f1302120102030403030605040b0d03050d060503060106020f160b07030507210e0906030102030f06091b040e011502010b10050c0705040f090201020d021501090507020a 84
    0x490340e90110340e1000c290324452610034403002e0aa4100703106520100d151130340440c2441e0f80c100c542640c4044000116a0808a0ba42c082a0140403c1000450b10b0350b01000744000c050b0f060003014000d003001c075410f02080d039101000803a5034031118401000c0c442d0004100d0104c40264000d440281001000d540c115a03480341c01135105c0140d429043c240380220391680501031400d140304420340341d10003c85810f104030340c2d0302074800f5802110207036400c110b43c02c03850220200c00c401502003940c16035035215440c0710321001e21080a034007400040c4240d00500400c032411f0b80e4030009940c00b00086075035460136221a8442c0302c07910112810000121350008000c107281c4290300c1c20307078121200600004640d010044d403ca00721800000059402004d24062000c07280c4168090002460200700b6580ca0a070348100040c1111020f65072407444c50b072103840300020f568050002354450320190000d0100c142a2203001110300030305000710a04265500b01040c221442000b511202980c44010f45101614 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 7304252 1250 7303002 7303031
    0x1090902040b2505070506030403050d0c020115080106030b04020904020a0e090a020f030d090506030a020c06091e0303070e040906090605090a110604051302030612100f0b040203040206030a0b03010f 87
    0x200d00c0c00510101030660f0014850001c18101610080c2c01c0b202901505040c142084030780d60020b0400d03410024240070101d41c4112520030420003e11a400010351010440c090a0f8130402c0e95000810507450070404001150b403c0c0c5105502c503074100d8001c00710741d031180700054191f00690005009100c40000f04a500341c00091200d00300340c02210020340c000c07071000800d9591201032a80c4800101071005c100100c0c00c0280103560030040c00c800c05030800c030890015500d855005c49808001d54020b4003480c03455581c800032061003150000256103140b41c01c4c40054242040c19924174040c03940d5204040500003203a02004000b98400002c5c8514145168100d594040140d030954200c1d00d10041d4a51600d4038404540484070b001c1d000c429900010004003000303410082c992a0480311000f50381443ca6001e00c11140d52402c5031000241031400d0202820499844004440c0940c0c410010f008c0540e844a09496100349002c0d0042083e07060240880e002d0080901981103a60411014201c000b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 7305502 1250 7304252 7304257
    0x1020301050f0604060c02010c020102010e0a0803040c0e010b1c200c0606010318020405040c0f0308040e07081012020a05060301090608100903051905161101020610030201020c010c0201090902040b 86
    0x1c104652040c0090840d10401805100e18400d08001c06e0420441d40015405200204405401400001241070750044031070704290410f60300f15640740b07000041100700074042e2141000b400c0c0707801e8039100560610095115610810b0780b4020000c0543d030b14803d07400200d4214036a0a07004401310310500c01100c0d41e0702499080f54150000c80c1c0510360020301c05522074031a014491610047d0300c02907140d581c080c0b00c0101005001542d03180720103113000c15403983c400d030030800640c42403141d075941d10300d002410f11610308098404010403145406100702000d50160320070503520b01305145c40320300b03129100180f01e044095011b90381040010000061135020742d8460703405c6520110a854031540707140c01d040f0860340c04c000c000300854020f024030003050544c480c003525090701e5810101e150580702004c101c0d4620808400715440c64440c0c0a9040c15681441110b4100c100c240d40304945508646c0040d40b611401d9240c0c504010884114406582c0326510b0140100721101086650703d8070781c1c80c0422150b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 7306752 1250 7305502 7305509
    0x2040b04090515090606040918020a0b07050610050918150403020c01090801110f070302030f0d0b040c02060603120307090f120b0f1006050a030e03030a0c080907030302030d0203070201060b0c01020301 88
    0x40354550000c0030030b410135240d19880761078001d010b14a4603043c0a15200244401d455201d5845100707009000143c03201d0b12000c0280c16403410881d01c4a0b4146040380c503080300280440c010440d00c0c803040000e40c461481041d040010382603481c03050000b5046040c0b5100d0f0058070030400c0c003040020720042c0358000c91499035054080e6150352080d92100d40b610300340c0380d980320f61400001040110600302d201c06005446810300c0f91054900d03100c41c1820b114159000700140382c007900c2c0e44080030182482e02c1c0c46442189201030000d000306103007e100183d03c9407941e06032000001d00000008000e20321440c420b8014004a5518500040c0c49908a4100200c030101c11181e514141001c03c048481d4121482d00c11001d804031007400c42c1c10500122910380081044a00345521002000403244080c80554860b58081c48006038840c100d4034020039914001d0102c0d5465004503d00748007007540801140c102c2000c10001680d640c64241c82217005140d07603071003542e10380c40220700401141c1064001354104c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 7308002 1250 7306752 7306771
    0x8180d0806030607090e0105100c0203030409020301080d030b0306061207050d03030e060a020304080f070309090609050403020c0f030703020d110a030302071518050d0611030108030a030e010b0904030c0602040b040905 95
    0x180c0d413504000e440310240c5009841203219403500403c4140341c10504131480b8203451402008034a00742d804a451f54226030404110160044010700001c902009051040842890140300000f400f5001c240ca40c1030103405140210103022048480000c200303c41d0005000140c41c5500e20806810300800401030303c100141c050103060b0110f900511b503402074034000c6070000420751802008044100d00380e4040c2e6811010301a10f59000540d400c0a032241000034415003802040c0ca140611700242840c0c0600e07c501c0c8141d41c10f54140740e20703440010743c43c820b51303a05079840744101030075081c280165001075403d140d005248841c04420168003240e1901102c43c801c1c40711027102d615560545201c58006103804242c01c2c924020881407409249110105000c2c800005800741070501144190340300b6089070900d540002404202503500d441100d032140240f000070024401c070303240000e0307201801400260400c115003400005000b001e034115801403a112031040d91f1156180d1040c0c0203003000702c807041803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 7309252 1250 7308002 7308013
    0x703020909060d0201050a080403020106080102130e060901030b01090209040b0303072604030b040308060d02030703060b030709050903041710090506060111011407050c0102090a03050102030109181208180d080603 93
    0x8541000c03c8042d5010341c1c140c58850030009800d40841321010002d00680456407610780000f01d556080c8003c02c01c03408800d80b42c0828608180e40d01c3c440210107002c80b4050580c80e00100041403190301301d0b6040d074125240c096580e410100000b0007400c0c0321030030030740d25010008021081040e05402028141e413029100402c0c84107402151826004921015010032040c400007800644100143c55000030003c01c41c03c2d00d000981c021034038001050308126007030383d600c000300e060504d410800b50300108026001031103a443d1560840d078890260348580b041d00050140d01c4a01d0700020300910f40c3d0141078003810820a901402d01903550407041e10311134007090700354041940c50b0006000b5802d500d2020000300c0310507100e20b41c0c101c40c140d202c00101d0002e554280312240c1c55a0340e80da020070003140100d0000d03031a5410800c11000b241d035031401d00301da00442444000d000401031640580c0c41400c03070502d018540e4079040300d050b15400d448034603c528003506c41e500c01c0d00350300810300b03501411060b011901c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 7310502 1250 7309252 7309261
    0x70e041101080103080a0305060103061701140612030f0708040b030c071208040f0201080c1b060906060109080d030507120203090d17060109140613330c0609020d0b0703020909 77
    0x1502c030742c404e0101400c4c190701000000800e41c00382e00119045041072500041041e520110245402501c80a4244070b945605100e950b009510301102e410801c2111307558115854180000c0c3d8a101d050b804244400c00801c00c141130004940a8600600303000400c43e13038a00d081c503510b440d9940424021581048055041d400051280502621840c1d00016420a5491540066036410b000500060a1440c20441c61641082c500909021292084014101810b086940d103050030b20081c522410486192030070030102c4800909503060200740d040c0020680c9070008110360b1202d141c0342e0100c040e4000004c0c080b81840000b200b40341e040c1d644e6190740052185590b030504100069401c54001500840240705d600e10320144101034241c02003c13240b81031845041180b203881294843d1030110400c80c4500070041c0c41c00c6800031501e455007e1442045806180034007007130a810f00181c20310f50348a820f00119194143c0300b180f46504001000841c1c41d200c503000303010b9030080242c1409058080c0108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 7311752 1250 7310502 7310507
    0x30316050c0a030507030309150e040b03072103022b0f020709090f050c01030603050d0e030f060106180b0301030b16030f09060b130209030c060304080412050a0314030f0a0c030905070e041101 84
    0x32740000c1c0b25aa1408101c20740d0004002c00307001181000365050003403c81c0025540c9400885015920602610310884069402d0103400c2c1b04494131980e25128010103107281031070011080a4400003e030515916408000908a00d0408903801807414546424504400e1041001c001c1417864401c0048880c218001e0300118142d03140c44c8001401c5500880e00051036a00a06601240c01000742c112641070300c0c0b0108c410b18005083e80034001080c0c00d40c072040d407006402000c1c20040c09805c0d46031461945035503241942c4080c0248006400040c6050a485541c0300f0341004c026213800c482305204441e03ca0508500514900c008c040c4181070101c5410145451070007600d507141d03401006403040c07040d40c4c014002264002001102c045034108400308000c41c00b0641015844d0080c001012850700c18a80a01b90381c0118a05400905081c0704000070101c110300c81075440312840f8004200380250500590250141e114020101e00800c0ca001c2041031002103038170701ca24001d60000c1003103400c82005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 7313002 1250 7311752 7311779
    0x90a080c0a050f0a21090504020c0a021503010905061e01031a0306150301180b0a05070c020a08060106080606031513020d020c03031b030702060103030c02060405040c0c03081005030316050c0a030507030309 90
    0x500400c803050b008022070308d8607038080c090700e80030803080d03658004507540010402c0b4108000c003101d01d40048010f10110040740f0410b0b501c01d80580d0240100e400b84101403440102030340b0391504164854144090421800f891000d002c0c8000d402c603117550510785400081c1c4a17075585c0aa001c1c0d031070181072001c80ca41c0d014a40d14690340040b1414015140d0000401c05800c3c01420b41042c4020f08454400503181c00b03401c80700400e80440a41025410550020502c0001401e05c61040101b0300900c0075140c80340c2c00c000007843e01194001f0dc1e9010724400c5402902036030407254491031001c5030000051790b021004500c2980041c1e114070b01030418a40c45204c0340000d581440c0143d00150040c07000038000c00078119120300041440307050565480002c2c09480b09140b0380d50000b40e02100e818105a04404255001100c07130000a42060825010941d60301401c0142e00c1d00000007a4907006015080c41458079208024188001003900e905015995494034403084002600184002440a5041d450f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 7314252 1250 7313002 7313063
    0x30702160f0b03090a050a03050d0b0103020f1b010e01180b0603030406020705100207050a0b070b06090408031603090f0516060201060506030402041d0d030f0b09090a080c0a050f0a 79
    0x1041408a418061082e01c141c0008000704041d04c03ca035280b002148040020072051031081e039a195882e814400d1203400d0307440066000c0c0c140360041c064040b02d9500702d803d40d002c41c21084168915880c0768070155001d0407043c1d292000b59403800e040701c1d02e000d00151160114500901191209440342c0d0141aa40e1003244a4400160440001800145084440940905001e01c11100d410b5111400a4140134450384807103114480055140e040240104040350b02084c2191100d009107041e840d001e6003440010130030340c011011014010301d101c6c0a5400200055000700e030001180d4894940716641c2e04ea08007640c68000c81c804000038203036105005010954001604160031600d4035030902012b42100e041c0f400040c402000501c2c03003240200305180203050329507008503002d110184040210b071142441540145098010080180c0000400c40c034240e5114944941c2c41c80301603911340c101008900014014080c40500801203000000c41940150041d014601303004450003080c1403180c002c90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 7315502 1250 7314252 7314269
    0x3050d0501090b040e160501080402060d020a0306060e030a02130b0a030503130e180d140705010e01050402040b04020a0203030112050a05060117010612020904020907030605060a05070b01051c06050a0212040803070216 95
    0x300a07c010751007602130302c1d003080c405170144d4109060324209005a8005049000c0040e6036900c003002003d900c180300c16500710095014001145d500c0d00803840811560b80240b4459131900c01c41032040d103d400c00000119040010740341c4442080104c1d6100b14901c0c443c54008503101004681b051350105418000c41d203010005100e46404420b0503150a11581001090580c0c140321880c040b4400703008108480b6600d200002d085c0c03400d031042001b01d6000e900101e0149105101428100d900007040300d0550314900203001112886180c400d1800245507801805802a0000000c0c417440d1080c1c0070b4500d00c082d100038403143e500c4000102c2401d0203290003030f42c8036010401282c058205182016000102464003040b495152004100d96504c00b10b20140051400a0765905101344a1545805800c04480d400610b03079014000000310070920b6005821665600081407044002d6411201d0401524134405504c0c5040c2c00c121714a03400c2166200b000d0701070102800244442e1007140f8054a507200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 7316752 1250 7315502 7315543
    0x8010f02030f070309020402070f030807080901020a05040e04020d050106030308011409060f06090102010e060108030705060c0c060105060f120106030204090509060105090a09030c0203070801020712050406140703050d0501090b040e 101
    0x1107080b4085c0034070820503600140c0c01c20507100400d09002560130307018000d403201c3d80241000c0e080244400f6009040901991050004000c001e074090202c03004c0361003044030b03c103040c0c9990000804003818984010800d61804000000700768100039070034120340481180c41c414040000034020311903400c840d031a910102c2101c24090314039102000d4402c141042c800041c1c000301c140042450102c2c282c0103402c4a920100381c079010890204000c950160001007068200b0039078000c46da13528903060083c80d10030034010a400804071155015190b0001d001c003590421395030740744d002400a500500624078007a007040005616a02c0004210f03040b5100907180c0d01060303a41060703000c000c14448104a080003180841440035960401c44c1c140588410000184c1d141142d00d40500100c140c008902c041c05002c0c04200101da400a00d0303240c1c2c0e204144130180e943c06c00da18045071039210300c00708041c0541ca048000b103203604851b40440281c55040c0c4040010b5800e40081d02d03a908614000c4034400c9403030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 7318002 1250 7316752 7316761
    0x70302101107090f0b0406030c06050319060f090606050306010f050c030c030304050319020d05030a0c09170f19080403020409020406030503030903070501061a030a050601050408030703050408010f02030f 89
    0x9184891554926290503100c64420604603410a0043d5100d49403494072010940c10b440564442c031080608100c8080020b2407842d550300301c60484911412040c400d0100000e07442c41900b01c0481d00d100c001c01010062030352078280d04c0591510300d00441c4c2c03a261507e0404500303140604200c03806118140c4541400d0480e2250807034030fa0344041c000040c68002070001c22000c2d42c0810140d802144580d0180d0b4551160a520641c11a84103000300115807006204d805015044801c0340c0e000002003401080903050640240c0d00c1112a60050804c80a4880429110724000c5080c454010b1000199200c0c588444d440896a003c0c5071000b070401c0368204030410061605500c1000c485102900100b4115640d0300c2d8503003150406c0301c04075440d0b000010458104034081c0304250103001403111043c1c030080c41d01c4081a803800010000c84102e581e94000c42e2441e80281c090302d008101050807a0341d540b581d8640180f01d0342040c8070301c00d055802d1100900c00840307036000352071290030042d01d003503410381d40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 7319252 1250 7318002 7318009
    0x519060b12040203030408010e1b0a0501080403080c070c03030c06050108070b091212040609030515190207061d0703050715020c10090905010b03010501020f010c1d0f1e030d030b0102070302 83
    0x40940200d0713162104220000b8952428080d184000d034860000c1c00254281ca29040d044030302c80305116209100020040c800d40e038006a1141d009609031500c0046683c8009038443c144c031a0f0b80c000350607008800c4001042540c001748601c0e078984500400e00c43d40c1d90340c0c0c42540c4d403010680140800c400e0f091091620b20300380044141101c000b0442201c815030443c0da016215a80b003600140c000602c0341106200380241000ba541c03d40c4c075003c1e185046460001412003003004d8111744003e440e07400013015070601202c2d8004103060710740b0b41d0700c0340303850f40e504a08a503580510344821581ca009040c00000d15414440080000c01519000790407c101c0e00400c21813410702d01d1528806009040d08007050b286018850b0b24080d241401d4500c4c0d0320b505207000680307402d0000020000caa070402030600340c000d90003400c1002c60441c4004940f035104040700024188015040701c1500a1200e8410f95200100c1d092108499a4280c054401c0f5841d01c8400b10103480c2c650712080c1c09070b48904010001403d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 7320502 1250 7319252 7319287
    0x1206070c030c060507090503160602030a031a09010e06010e1203030109050403050d020304060c080c0310090506010203041d0105120307050714010c05010c080604050a0b0d02060f160302010519060b 86
    0x284603181c00b1a9268003603894038200c8a00791916000190601801d008505040200b1100300285040380790381c913464154000c2d500d204e070404400400d61915404250800070342211030b24100d004207001e440c1e684031000a031905008884c1e041c001020300d000d410f20b46c188084100700e00700000b0095451a800d011808000c0c2c00e000c0c0c021002c1050800901c64040520700c041c5002d01c0c400c001c00310303405001e09401882d8500251038a08000410000d03c10307004001c540f04c00407a20180030101d0181d030f03a080140c3c00c0d4001c65010035044000308040510117486504800e040c0c450850301250b13a082c080003525541d0045800007016540001c8050100360009075500b10404030500d881446102c1550342e0324203440070203600c400400c40c07003824002c0910703140c000c2079481130061004000041c02d400c0002d17000401d100000c0c2c0142400113441e1840d80385a4202c0e03004074002c0841400368a154503000380201811a40c480800303030310005c8140c5e030750050301a0004440310036001a06029142405003000e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 7321752 1250 7320502 7320527
    0x4080c10020c0a0303050c011103011215060b13080106140310021315050d050601050306030a0602090301020403060504050a060c02030702090105041d0f0d020105060607050706080a020906070807030e120607 90
    0x51142c1d0b401500c0c10f40e11080b5600185110780d440039202e10b5031780425805d60f0482020506801018030050104410b005080403031795420001c01e10741c48000d03440807801000d581c0c0000c50040710008a055852a80c601c2d1030084402c1c83e0001c00c000c070340e2000202d0301c1d51112000c4c998103070002501888081e0b00d5401403e82000c1001d81304050039600d60002110300103038400f00c0045034010400050303840e918810036030300020a0170b22502c1c42c5848000039444e0b11514100618050307021034501804c0e00c0950548028542c03204042205081500b0310554074030802000b20380ca10f00f454005134a05101100b958409540a0807400282c1d00303250400c005031423014070243c2c00000c0c2115503000c0c110100301d03101c1003098102c007500c108544d095000342515001060140600c500704040030004800189135011525203251403102030b103c044c0c801010388203500080e0303400000820f06905000303004c0020586544130740c84d0188850354040078411000a0700348004020303088400000e80e42e90042142d540030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 7323002 1250 7321752 7321757
    0x304030318121410090f03030507020109110105070305090d051e01020403150203090c0405070305101a0f03061315050f04050906010311030a08030108011401120512090d080712080c04080c10 83
    0x100401d0400301117441c80b11003500c004010480c481c09054240c1325040d04050f183c4001c1c48418100e8482030f0400001e4500d081c100400040d149040c144218180c40344010000c2c2102d0f07070300840b03003040340d0340e07241d4113039540b03c00400c031242000300d00814400c0340c080340d510514030b180210054003082700a40004182ca03009020b8402891881c3d41e030352081600ca5040754400152034240020660f2030304c1c2070340e0068021250031450b035404100014050340c4000d002c5508540d50780e075881c00890b00080c00401c4807a44a410310302000194400c2080c0e9505035070040d1010300801245408001c2924070981e40c1c140c039908560014004a008030200c40402c42000e401c4807880c68071503071140308550003640901d0850350f545101e01c0380380b00c030800814010180e0125450b540251900e4464440754069029003410800051b4000103441d0342d2a801c01d001d412030382d0702d40c982101c2e041a081c0002010038000c0001d40b07000001300107003480d4050320241d6194000802500e00c200060043c0c400c5c086559a05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 7324252 1250 7323002 7323013
    0xc0312020f071a130b040b040212030703050a0f0302030601120b010306170703050d020123070c1502030709060207060903020f0a0b03070504030b0601020c0f0f0d0b010803040303181214 81
    0x20650000801414030900c910304180c281c1c146001d03c00c0541102070a5407100d10042108100031840304c55416401076000241020541c403203100007000c40740b0b60321100c07030140404a8040281508880905210700043c0c481c0305082c40810310440491008580c21804190444070284480c100c0c0c1c0d100c0d42003001c041c14001283c1c5d40300c142200030300945a2400074980c0c0905c00a00400900344101404032101380020720481000940c0c440c1c4070b4070741c0519080122501e50000e2260f40c42060f42005003500483d0a5a5903d60300318104042e5004a40d8207001c5140800d00191044c4001198421109140e4404140034110350070844100c6079084a1548804034100114030220120004c50240d2010b0b01c500760b0705d525524007507004101c0244490b041d50003d44a0340c2403078039500d10329414183c08480701c1496045080020345413034005280a0003100b01c00d0008030f001c10b8004010b03c03d0700d029845225491103000c0c20745d842d05555000c4e00c08280e58505810002940861081091039080e034103075070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 7325502 1250 7324252 7324267
    0x140f0705010b03060901060501020f010204120b04061404030c02040b09100b090a0f080c1e0303030105040f0e010c020607090803030103050d030207150510030308010504050609070f0504050406080303040b010b0301060c031202 98
    0xb8a40380003660741302c4881c0d42d5060204409c0da010040c030b04016003818025800c2510700302a42b00030790b0b14044054000400ca80002d8104411070b403005480c6031304550b02890b00d0070103045c01042d001322898100d0180e45040100341c44c82c0350901409210319a5003c0b1101e00c41c1c00c2c00c040c07440941068a400e038010030801c001003005a060000c4a02826610b0000c0074041950000c100014400b1001410352040582c81201c00b600c020003120f0542d8016200803581c1d100755807003280280050003501807103510b080ba02018072603000c540c0d14025aa5591110541c50302d40c5005c580700d00c0280f00061003540002d0712000a14040e402071704c4c105003c0d00c01c1c19541411451540240e800860b95400611054030080c000c050300811041e0242500351810080c5203444000714688140180040c000c5c00b81c89032040701e41d07920440c109c40141c000178209200c0300395a25400b0b5600e42059500721200c81d020400403607940b101e0f000381d038121a100d0b990251034040a803800c2c1e03812401d022121074015000c002c200c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 7326752 1250 7325502 7325509
    0x604032703050105040b0f1501050711061207030c030e0309041515030203060907050412030c080910030902040c030b010f05090105130608160f020309060310030f0506090c01140f0705010b 82
    0x21802140200b0020481c0d280c01d142502c0d40e0600100b0030f119500c664824040700300b83d10ba900c2c3c20034001c20708109540790000e04000c1c0c01800003c85065003c44001000c4e40320f008030030001d6004031141e440c01e000f0103031800c1003a8107480c0e1104502c0c0c000e0788140001200740c076240c1c0200688001034501c010b41d950b218480680c40010049008012a40010078028141000071109521a4440c13030080d040031b017000070840000c10450400f03410441d00c0300c80324081c4452401143c0300344000401458103a110400d0241c080d000a80047e03128601d0000f02d10b580a010340501c8280c03020503520281d002c1581c4a007940c0c0c0350422400d2030f0400ca030510103490b0300c004080780000544540e44842c0e049280400920410324607910800d070401c0001901d0240d1a03800100340c880301c01c000c0b6401903c0360340304001350009601e55400a011504889004400c0c041c010034501c1c01035000c9019103c51021040040d9161995001c800c40207040400c0806451036022015055542c0300b03400115041c800380000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 7328002 1250 7326752 7326827
    0x3010513030207080606060a030507021f0603060f06030203070b0f07050109060e0f011509020a050702030d030c090b090906040209040e011506030608120703030b060f120406050601020f060403 84
    0x30101524400000c95007403580410440c0c0051a496004001902d031a501140c600d025419000041c142c554010910f405c2c0284840f0010400d007440c4000e01c1f0b076141c4506400341c04184010f9800300e01c0c044014082c02500d0140700240c03500500104405450540700381290742c41705610f5180c07400c05100d2000058401c0c003d004c8180d00500e408121100c0220f81c0c0343c00d00b020f000701c4c3c2030745030702d0090709002c0004c44020a50071513024810050b01e402105d82e055440d403141c00402903040c01180d008120b0180c040c7e11254001145a427900200380e15848111003a115101606600c9000c200000d40c1a182603001003943c100040c10120f00b040304d0031392041c20b480710520400c108809022040c01075641c544165030050103401d00030700d02985c0b44440c0c0070181c17041e404040e04051302e600d10f641d0316803107040c01c990f1140040c0c002280e4403c0e0b54540c0c142c0070300060f00e0484059041c00003044c0c0562002500070800c0314500041c1034680c40341d550039541000c1c04503080400c80c01c42c5a8807215030079405507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 7329252 1250 7328002 7328011
    0x4060203060a0b030402010206060405060102030c070e091c020601120204061203030507030b0102010902010e0d0c0b0d06091406090a05090f010204030506090c0301090f0f050705040f020a08060907140d0902030105 93
    0x140940c50342004000c000c081c44030b54002c2080620280b0800025030b900081c030540001050700d000405d5196900100d00b9849410401d81240c441c03004009805200c0005517881703419241c0980c0d0a81d29225595081c00b240620002d0040e40a000180701e0012050f0a20089600c0148002170701740d9100d07011800d11464100980100360b440041050207500b600a80c0c00c504424402000752078000d60018000d45001202180503d0354040c1c0b080800c08001d00c51009002d00078251501c95103007c0e03000c0040e0109026210085003001c209040b103828580041e4040c00008102d80740350b99501e2035480c01401c0040809200703118002c10140702c00c1080c40100302460259000d403516141400700380d0f240a810b010107900a81c58514110049402030640490042d400b40d07240c0380d054418100340e1724014080e0012076005281008681c8a461654010601d030445901e0b01507196544408001070180201c8002d1b0201e044160500d40e0f141820008240b07044010b4000152900c2e80c5d000300c2d084aa0894 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 7330502 1250 7329252 7329263
    0x4060e0406090c0804060507091809051e070f0909080f0304030210020a1701050604030c0605030c1317010510080606040906060312080103140a030e1c0f061a0102160314120304 77
    0x80c4420f000d954007c1ca0b40c420782904100004514054214003c41003500d4580340c0155213a4034001009401d005404031001100d4641c100d00300c0c038401242d00d070641c80c442c40341410000c4c940000c0361071842c0078401d0200d400c4041c00341401301c40d8010030181d92004004400318041c81107549a0000305102400128115555090181020fa074000d0369001e81a00601c3c0f02d288244002c100148032002c09806445407890400d4a0343c4540c1c0390071515004421046180f440c4825007c01e01c0c400c06c180140c2c590b50b1520091140c0d4440180d2005500307441d01840200b40c20180028100f0300b030a4012001031486a0300004040d076903901c5040514185454240005242800420500450200c2503100b4012000a442c0700c03a0590303005002c00c0c9407404118080c09010b9164120b4074030007030707204a60b55008812920400c86625090004181516100c5411814001c0f001d146501c002180c1c0e80c420076004a000c1c0f03850868031001c0c0044142c903a2000d136442000040e42001a6903000342d4015840b07013 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 7331752 1250 7330502 7330517
    0x8150d0c090515040b030d05070312050901020a0e040b010c0308090a0501020c03040807050316060c0c030203030a120e0c03030403060509190501090204061a0318010e030f0304050c01110304060e0406090c 89
    0x2d1081050f080c240b2043e125609126a943c00d55802150307946c84200300f41007181d0354013468541610207561161a0020262510080000c5080d042d0000c0400320341c150f449010088410082204681150890500294507021034600003401000307841e400083c01000c8900c501034543d40d00d800da0b404020030304150b4101003000c004103c410011500901011006880f41c50001840d900500100d485400204045608440180015a020a00516009801d1b00d5a40700301000103000e5030850760150390b8079407070110016001c1c1e40109401020300d1004010f9840c07d032030364035042c000e058041c10f60401405007035240e02c0d034010091042c02100d4418000402e82d65030a004005c01c070345080d800a081241442d120341909160082241d0384419800019034600f1050040c2500500d48203041149038400020311708500e80b060800386100b113101d04203c5804c13001080044076040003e00080c64154010b1009201c12402044000342e046000b03080000c220755140c3e0300038282da102c98980808210701 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 7333002 1250 7331752 7331761
    0x303020f060a0603030215070507080d05100e090a03081009060e09010609050f0103081b030301060e030606040b0306061018030602030a0f050411011404030b010f17010b0108150d0c0905 81
    0x60200c168032004a0500700003ca10750389020f900c0c0c0c0c0701d20110320404d140b0f1600089609020b102610030168200c000366840f076101c802514001c0001b0741e0003a004402e401000a40d081d004402540308087d42005400100010b680948a4280103444500500310000002ca52240e107889031300010602c51101590728104810341c030382114400d4005041e9203040004000050404400706411642d01400d55a5507401c5081c60300c2e482140130891716401e002c008000035043d0340c400c588580000741103065074500c1d00c0301310401084440d0b0242468041c0c21110004035103140c0710342d0341c0b1b81e1082035040c50181012020000c03c038a0006030403c0303400c035a0200070f00484506034851a030950301c48050400450800340c58424a40c8000c501c42c6040000c0441c0d40100351040030181d8004560280501c0079950b140c00c034541c8000700b10302402803441c29804506000d071805005040351020107031940d10503911101c9070303041840003030140c003034020140c005003c00142c0c07003148400c000c00d5411800100d60030b1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 7334252 1250 7333002 7333033
    0x1050715020702190609050907050d0609020405040c020c0a090e1005040f0b15090a050c040b0f0c060606030c030a150302030a0b0601020d02030901050d0203090c0d0302060a0b1203090f130204030302 87
    0x200c10030043e0030701308000040c442c090300404000169001100e0b1048142d6401e0f8084641d445107a02020180f8100780740055002051303000b800644104850030b05c4500c1c1e945e00c003207a485940c0610785d50b101c05100c0082200c4180c6500480c2000841801c0d07404442c00804000f05440b801c0c0c4049903d5032040310014107200800a42a4000c0000800c0c0418040280005600301c04050310700b94840303070b507103010810346000345086400400c41e00d61031903110100042850065001054411154007584002031407034505101161322401c4032402072030654941d00c0280c0c00802e50407081420008103580003001507038003001030740f58052164000e6030462078008002403c101c441541401598000e02a007021a0b030050700780c1e00b03032600803900142c480d55400916480c1c0002401074a411851105405040c5540803a40c94420100c241b02030080d06106010b1081c10419170940c0c05007034000340807592061a02d000e031809084d0000300504000302c080e141910499100c0d90045015a100c000e54800540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 7335502 1250 7334252 7334269
    0x9020a03050303041703070e0906010207050d05060609010801020a050409020c07091d0106050901060e0f2b0b06030303060607020d060603020909010605010e03030c06010e070908061017010c020309010c0201050715020702 96
    0x30031505d0a80c00c2d07040c64000505500112041d191143c000300c80060b0b0345910800200c0b0040c90000d0a0415043c00c42c03d1184d00e0b6171050700c005000703800000020600035414002c48200703440e15550706252510f050b0807a00290440c04c072915150107844000900001280a00e65100181a407600e960455030081c5a007101e03126405140110102001001b9694000301f241c203a102d82034441c0700e44c0806890009100040101004075404034144042420684401e030301244980f2881c4415600d442d44000c160fa2800121440740e400070040000c0d40050501c0b40c0d15614035441004003050098883e400150314040071503106203170b41e6441c0020040b075a4490000354070140b09030040c2d40380c00c040b1001b15440d49414090390201e0050b400101e07251601c5200c4c41c40c024141c0d1b030151880e5090011800c081140280b0581e4100c0d401030000e00c0400d00d043c800e910080040f40c00451800064030300564408215600a13410b2180510007000491241c80c0c140c0c51010100b040140d031138400340b04000054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 7336752 1250 7335502 7335533
    0x70f0b0406030b0d0201080604020d020c030703030c081008100c050c010908090a0b090604050631150e010206011401140705010203060102010507051606090f05031204050c01030905030301090c020109020a0305030304 94
    0x1350030949104001d1b0741c001c40300e071760007000c1507501580d200040d082c080081d105100c0c03204194400010b4007818540d160f80010704442040d503c42083c0e45071400304a552081341c0c000c820182e0820024000b10400c264081c1e183c61301a030401506044640d10304608603070260300141c685107000160b046291901604030000391044000c1a8140a21031002c2a014007450182c1c5024000c0040c0c48051030341000c100245101568980720002805000000c440036494405c40d101c0c0d020110141038184d00991f9800c4171854180e0003882c69070700c1c107403c00894241000c1d0311410b0020000700c90f12803110b000e0040840398051800565a41800d200090071103200074004d504125060100c422503c0610003c1d41d41c650308024042000040c90528030404411900c0040c12403000207800080030340701004a921481c000d0007580c401404050054080e05d9000307000070055001000144001c01e07143d0b1203001012040e01c00010740c080ea0f0703408079140d00100c0d04207a40702c2d4008810042001448400101c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 7338002 1250 7336752 7336759
    0x801080609010c020c0f0a0f090902040b09010605090d0309050303070605042001170603030f041403100c09030318051503221703061206010b0403140f06010e09070f0b0406030b 77
    0x96a043d208029141c0c00105610b038481c0340d4062086115039111042940680b0b4440b807290801580ca081c0403004101020080307005a0500a44821070300e000e5030140e04840440d11110f1034081c80c24100302c0c403015992011018402400300110fa40d450801c058452030f031064100081c40e00301424107a408645070900c1c5180f1030b05101181c011a40c0c000d41902c40145194120881603d460340001d042d40a101120740300d102d808a400114881c200c0040d03480e080e410740075141e0650001404c0000e441e0381d08154004140f00800800c0060301ca110498030140b1b1180c01c03103107195107480005045201010201800c9a008001d01042d030700e40c9040720481950310b2414000300a0713199078000484002c040e0340c400c1d110f4080002001511340080c81c9002d5140d090585142c1d40e115110400d0a0308140070588540c0c812180c0c8600039840000c05007041c403a194010011a0700c0c220540040c600d005140c001c480c0a10f40c0001101c0c0b500044d0b00c4003400300907184a40300c506050b00241141c0501074501d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 7339252 1250 7338002 7338011
    0x219020307060c050c040519050f0103081e120c030601080114030a03050f130f180603020619120507021f14060103020c120301030c030b0c030f16090510080108060901 73
    0x595000070380004407159801c04901d0703070405040071803d03c509441d9031500a410b00040204c682200200010b407030305054001c10881d16589031100300810709010080c0b2a1004000200604502030804807040e03036810301c418500b0380c5035031190030141d4081c2c40d031401000e804802c0c00b16968108a80300c0c094102d440d40200d86460040009036140300c4040040c0500c50005680d09480311a04202c5060651b85490010300b11741d01d4820084895191040551520308400140580c1c0f1081c000d070411a40c00a00715810002050401002d00103501000410702545103030810144090340141c0c1d00c243c200d900905110300f0030765084845045104c0399114038600d005012161031507100407458020f4000e28005850380c040c81c049500c1c05400801a11350500c000c0000001c101c100c2410100b030b41d110300c0c0040c1c982d84403400310803000e000541d007627081001c1c031a000070001c11003400d1100200d00d5919016108a907140b000c1506502a00d402d000064046801800490420480326400c000000000c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 7340502 1250 7339252 7339303
    0x403060f05060f01051620120a030e06040501020c06090102010216080403030e01080906130c05040f021e0f04060302070f06060305010b041b1706030a0606080f010b0105040b070602030402040905010e0a020102 91
    0x50520b2010003c047d5012680000180881c0074188002400d01400c80d01c81403607075500c016035a001c440002c4001035011035080100e81403240c25501200c1d8107070014000451020100009901b001c2c65181c1159403c0c070428a000852002d000d0000d0b0195145680e242e05601303008004036080700e501414003110100740b01d1040000990240c2c88aa00540c00c030041d00c443c900041810401c2e40728aa0180c10f041040d80a061594000c1040301e0107600b11a0302e4155260701c0b010302c1c0c0980280f95032003607414801007241e203019400a0060320710554003800000340c556101c10444159810655080c0c0d9508811103030f505251241c1100649030012802090000c018010513071118030880b2003188500c078001c100c0a07101009040e402542c8200301f4460941c4900d501c07075482c1d42800c0030b4038482d030030501b401d8090350049046500ba100b500944a01d040b5094031220060741c4060400c98005a8078202000030480a100714052031000d0000380000d80c905000091800200640e1110303511744005805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 7341752 1250 7340502 7340527
    0x70f080f0105012708030a0906170601090b0c010e0102040308071a01051c1703070e0114040303080c0a02030c07030b1906050f04050402010c050a050c1206070207030311030403060f05060f0105 84
    0x140c0780036188000b00e15440c14190342c2c0c0d00c4c90a503001441c5440b020860000013900038020305c01381c0322695100342504002da24540c1c0c6000d010740341907003c2035141005004842c2001c005100d0140001c3c00824001c1c020040503089030b1081d80156982d55002c5066010413000080c60002c810a0311500c0c4141d5050000049201030903c40c28040107062a401508200c908a5403911618202078100e0301da140070384010f080da101c2000701070300217040310403540c5201150400783c40540b0b40503500e0f420191b0715200105800da00000c0c01a05500c02801a01210542004000c0140d4418001c05400d41045149060f0041c0c0640701100ac8a05081c0c00b40010340711602a4140380c00c0031a404102030715a400145e51000a5400141042c0280744941041c410001140741c40c5550694624507201080c030800e54980f002680c24030010381103c201000800d1260340e07038151020314502501d1803d80d50341d882208503040184140e02c2d9a031201c0c200710369803a1245003664005000c1c240507207841c02104d0358 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 7343002 1250 7341752 7341767
    0x18020a110105070207151b0503070c0501020303070504060f0e0d0507080f0f0a110607050303090303010501080a06080c0d060f020d050414010504030203071403040302060307050309010c0207050d06020f090405070f080f010501 98
    0x40403d11a0f4000c030340d01106104039645c00c030104c051f1604003540c17413207418000c0d1250b01c0801c0556031040044400a6103510020031603104603070300d03601d80e41450f00384042101d840c0700800d90f071030402c20b48003a010781d07583c0c42d1003410030001d10890003819036516044005003010001a030344041a04644401101c3e6600481d0410302c0b240d00c84150001c2856000002d249400f4680303024125110200401a002000000460603100241c86100d00c66580e050000709441c03d6000d106001d8102802000d91405c048281070360f5148950001306064040d00c0750b030001c0780c00600701c190b2500d0712602400280300400340c40700002000d02c0001d00c024a060b0310042d54a00c12a40700a00c41d20038211590499803049c025a07001c1d580c020036040d070380e00749204003c190f500241e40200c070315440d004007103001500001d03007541203a50117004400c5803c1c1607200c00c0020341140c180c4003480d0000700900403a642d80c0340304552060711580c48102140850b21002804d0800082c0342101c0d64001a0041c0010380e0400031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 7344252 1250 7343002 7343009
    0x603030a090603020c0f160e280f0f0203090115080f0d051c0f02090906040905120906160813090b0a030f0203010b0d061d0a0807030c050718020a110105070207 70
    0x300507030344003080400245010b55203021b0103d02d01481c0b0103103044086d6a0740707900440d0210744490034551141c6000d070713000c0c08028503c24102800000e0310100422280c00c8100303c107a4071000011b2072526001707188141d03402220b0950380e9035581e2483c4e19072005144440d0014007050b8008165071303003003000000e644400c451180401e210010070f40c0f11604c000407441c00c402c2c034000e800601510b2803407030146010b500540400c61281c41c110340080c001c3c0c01c0610460b081183c02400070080d0500c140c881c40090b61001105680011040211000c100e45200820044510490040d83c1c2c480b905850388103802d101c1e40149505a04060308075000b81d6682a564060b00c3d0080c0c80302da0000318030f00c0040d0040c02d80040c925040700c00c4403c00700902010350312074882c4540c0071901d00400701c0c4401c0341a4503032950b01c10003070040c002031081c580480c0c0328401c209007042c461012105800e0702c541c5449807031b1003444d1300348414980009180090079401030102803001c102100901c418240090041d445508070301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 7345502 1250 7344252 7344257
    0xa1d100809030403050109051e0d0801030b0a0b030a050601050411030403020a030e01050403060c0804030210181407050303041502010b09040f02010c0305130308070506010b0708030f060a05060f0901080603030a0906 94
    0x4010580019082c000c50780110f601100170000c0c14a545851a1102c16244080151200d42d076031a90070240080f6040e422181d0301c0c0d40d401c6040c1c3c210f41d2002d01122016003024003080c0e403240d01a0441c0c90030000c00040d01d00031001401e4561614081006651043c401000880030030b2060000090700000d005101d29807500300802d8101d0504012034060080c0d52020f0165030602031103948650b04043c2c000d00440c02507080e070700c2c2203c00700134500c281c6040140c0140d020f0841011000032680017444050008488429903607541d0b60b8400181c03858005400c1044c2c801c04001410144a80910414000040541d030010203850603032120305600c0d818040c040e06108064030003204242c4541d0489003210020280c07507210680720f0400b10609d82100c88106e0f000d00c6a1000810062a001c00307071030400b5849405185196200710f03044005100203004249c001603194400b02e0380d907aa0901421001200511094030340840800050000c04003420441c000d4004101d550321881d80084140240d560b00d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 7346752 1250 7345502 7345517
    0x51005040305030f031b0403031106070221030a021905042c0c03040f0b160201050109020301080303040807030201020c06012d0602030a030b0a0b03011203080903090109060806130f020a1d10 83
    0x1c0b111130801d01b04d8100240d0300840b00041c04020075400c6100400c5d00c0000b9000c8501950340c2c00010780c0e44c0c071601119440d411240001c1e00411204000003558849908400503062401e5958201180c51b500000c21010440c085814400c40d4101080d4130b02c5200b07001ca010003544035403055010400009010440105400400141030003403000d007030301e003440c1c0c812170160480c03401c130303402203403480980300300b81c005500f00000015158050300980f4140d80295011b1031a40e01c41da9100a043e03440f1020442c250f540078403201e6009030b01803141900030076400e0310181d4103000441c00c445a28486000030b0038245159075050029590000580b11625500c1c20001600f03203103d4006143c0420079440365002d44400000410521074800349a04803a04c240c0b642c080d00d03101e400019840380282d0001da40001c030400010004648103001d03c40d048072010303010b41184003805942030140c944001901429a4002035170b0402c40b0790000b00500c0d001160703084c03102000b680c0300c0055025403480d2000d07803c20611 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 7348002 1250 7346752 7346761
    0xb040303090c0303020f010f050f0727090b150a0801050913020d060207060c09060f080a0617150603010603020a030206090301020405030a03110706052a010b0604060306051005040305030f03 83
    0x180d440810469007000464003040d81e04e20b4029603401d1002c04180c01542091101903d482d0280585409240c540c000d254466072120401c55a4010440351364180030000c0945524294108140d00003500c05228042140702684082c030180c9035210f583c541c21007804100078407000c0d40c8003240a040d50800c654403000c507168172124000350b50315201c002c1d500200c4508903204024566000b010003d11440003804820301c40c19040c0c1e5002c149201382c10219480f000103144941c802d40005d03611150741e801c0043c43d40d0700c0f85210724403241381100704034040d0b204c1030200340c034104a9500c050b4011f004030000c0c80542d095070702003010700525200080c000c1e080400c4041940da402c3d0161009000c021f02121014240f03800e000f003202680425520345801800b02c0402c02d10b01c90000c03124150101d103004486095880103840101d4134940d00030000d956103031000c602995901000304018849a038001c246103080000300080400041c0c500020720004000400c0081c80c04030958802210004c4040c3d1039544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 7349252 1250 7348002 7348007
    0xa0c0609080624031504060506040902090f060105040909080d050901050601050711030a0807031206060305070e0108060102010905030a09090f0204050a0b0c03040b0403060203010e1302090105040e030d0203010602010606080c0a0c0b0403 103
    0x2e0b0540d559250013003001d41000741c08190500ba11540c02100144001d0301c2728021710089512910303002c0c0d00300e41180c0c0020308603c0400320242d088501850310501e41030fa2a540c5a0803550078080440c7d00d84400144001001c0040c096550003400e10b40080080381040000a882440303a640001c0130070703200015824865800340205040e9941054040d5a84c1c00645001003031000310000e2850708925141011851921034860307a1302c1803200f034403400c516290030030064130ba0301401400c460456403140d5482d80012401d0000d44041e04541c0c45200d1080d042000d00390070313625000001d0407a18414001041550340d650080c2e4102d56040f20038558a00440b031541c0e0651180e03070090881d8420004001081145c0355008604980142082c10b1650700c034035a03200c0382046c4a1034082c0d88030148500600c281d140541c48140b01e642158101e91500c00071303c0d1144141e8100742c1c40000941d665607010001140c100380980e07404807421000901c4c040a19001401c0b2070340360b0001410780c82c0c0940c005000c150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 7350502 1250 7349252 7349311
    0xc0302070806070906020706030e0604140a06090312061208040308030709090612060b030c0112020307020723041805030d0c050d020d0501230303070602070302011d0a0c06090806 78
    0x2120090302c0c1d01c0d15040c0c00280c80e100d4544580340052040a500280d4039110748074010049451601801050701e440e00c9260600140324000700040c00f400481500090540c42140d012900c203450b410380a240100340b42d0111451980143d200d807200c004018002100d030811035040e23a45c0f10740030540700c0d119518219035521181c0c004c0c0d0107441c42c1440c08128804080449000350744503420610403d51070000b07044d02c50a1101c8001d001c01d00c40c64408001a00355006542d002c0024811070f206595195030fa042c82100d07205d08404815140801c20034141441c0c061312003411184420b4074140f440c41d80d10a596880f445031440c103240c0d51130340310000300342c4103104444e10b0b901c0d44034041d925000d80341d00c00300c002c1c0710a20a0740384001050392944440e8440a940010421004000c3c504020803615990065440b900088003155a5004100ca01c03582050400110a00704c100400a8010324a404807440c8001c4d00500144413000030204040c50000a100d640000901249084440300400e05000c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 7351752 1250 7350502 7350509
    0x3070b01030809040615050901030902130915060b04060c030309020307030f12020610050105090d080d0203010305030403140118121808030a08060a050901032306070c0605060414070c030207 83
    0x1444000800d10501e50b019110441c4200c4041003a542d81c0d5640741203114001010001003181030000c42200c1d03000760301189035180041d200c10340e05844900640e00b103c1c485c0b102120007400601d6149030f40c1c6d01c01e20822000c1c0c101601110326141c10b10344060019829000e0080400da2554410400c54809020070320081d0740c000f0030404234402d185040d00c42025110603c10040c402c2100051104803407860440c1110313410b031074a41c40e20303242c5018003c1c401c1107020180d0700e0100400c070aa41003041840114000c500620185882d02d06525006041503044913020403981e050203081c45c3c050120303070f590400386a4410092104100ea00c04141d0b07100c4030690754004000c01d64040024241070201c000c00e030101301a41c455255540c0d400400078240280d01800ba089a00c0e0030040c80040c07210010025601417400c050442c210705454450700e403400480308030300056031618800041001a008003500944100e40600601005c048680d500441c0101000c08200144101c07105040c024404035018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 7353002 1250 7351752 7351763
    0x51909020406050705010b03070e0612030405030d09051203030f06040b01030b0907030c090608090607050306010c0c080703060b06070b0a1109130501060905030604080901050f090303070f021c0309030803090307 92
    0x1102e5542c00b0180840d041508141c54039420180e001070f2903e800300324103059400c01054080103403214414800905540b4201245030302c000c1201080581d030400c072005001d01a9900c880d4154141018081002c1e0a040740f82202e91050050219064407003000300d0303008106603000950005101c00480181803154407030303500000600c05204149074141c0242140f41c00341d49170884001d50301c10040351080011620b80001d9013002012480d901d01c918000c5402c45414900b4852008050b03c403400164081e40c0044102c1e4054101041004660701984421900071540e640c10304c840e0b9204d40004880050151442e03da55111421141058200340c82c05850082e0800085410b40a862401481d080c05904046050581e00007102c0c40c00090040c82140c1c401011820011001c00554007034028440070702c10040140090900c85e00c080000e007564501910f1482c1c1390810500500042480c3c4d004007610620041c1021030201b904200c0003021a544005015941d5a403103102905500510b10000c19 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 7354252 1250 7353002 7353007
    0x4020304060b09010b04030803040b0a0605030f03030109140103051506041509051509240a090e060a060807060f080a020904090309060210061401080603010905010e070f09020702060405190902 84
    0x60100310b520060410000355150030440c0d89844220b5014000c1f0320004200c040200001340019624103000d40c0c21040c100380c045400c0b511040040c0c100a0300056140311780d48003000400598110b4025411150111480e1001550450311110313115500500e00d400c0c200302d410042590b5460f258801c610003400601c1031202585c5800c4400302400f401d64160458000300041c0c0360183c42c08880302800741000851640141e213032044100422000ba166896105180280c00a01800540030710407941d84c18001030070440c07414034003d208445042c0c000c030385280d104200901500707400075130300b800c00c0c00d09060005013580c40138480e001038811003804907002400e10b954131003015000b07000c1800b42c9400d9001d48401c81e0f541031204c81190041c0c0315078138141d0000031001700c465000e0260f041e0000700103070011035500303029214203003903545030380304007005501c0040100444146050300c10040c000e140003c1d4640421070b0002000d80c042c40c02910b20070f032499085e9a19070b042c2c0421010007400303103560031f54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 7355502 1250 7354252 7354261
    0x702030901110303071b0809030303040b0402030f06040308010605090301181b0b030f0411010203070506040302061602010203100504230106090302040b190b090a030501110703021c050f0901090302040203 89
    0xa480360856040140070555152030111a000c0c08000d40e481074025070f03030f141c6001409500c0100d080c19400c0c0192a00d00e41040344007103540b8184021440b1728090b60001c002d0741414818945010802003550740d07250400340a0100099020780600d0444103646051500c80702080000790050290000c280c0340c5c41410003a0300208031900002020341110f070b8052558030750b80e41c64444100c0c801214005070031183c800000700050504802c1c10030104040c4110307410006555601407500b03009031020744c0540c4c0003a04100c0b140351101c02c0d001c010410742c4001d500394245065a04101c82150140c02d20954460705070f40d00144050381c0001d0b035a04400a900da140d60740b4031002d40344000030700040c1d01032418911070941504044c4200c5901c18680300c0b080c03105031710300701c411500d1350010b06003160b02903918500000410303801d010b9500c40c0418000103942d078017440e1401034035220386007180c2ca484c24045942e009486130804d05a5040c0031703140005070760311145c00004030356452850700000e520620100500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 7356752 1250 7355502 7355507
    0xc060c0705030304090f0605010504150c061e050a050601020c0102030d050601021203181207020303160204150f050306060102010b0108040b0601141204050d030213140402090d0f0c060309020109050405040c080607 93
    0xf041c1b070290465040010903101e0700110349601c41d60245030414800c000c66030030921711070248112040d004046c00260481c1042c13841000005c54050600c0d526141c0042c80140c40f03181c496140c003e00240014880d102c07a00001070b440c1e001d514810b441070f0381e40d0000a000d80c1d0003400700844843c0480d1200f5130304d14201181c2e8945c00d040558803455882503903200500520582c2c1154400341d0024020340c1040795100c480601004c0388401240c119450b0f5074030031584000d20b104d40e00544124400318120238200010326140c180300070082e42c11a03051216030b15150340c0200c40541c05c207401c041c000341181e0382c0d58016034007914001b0701602e02440015044003041da90904a90055109409030b44941c40e03100800c8041e07020707000c0009840c20b4441c40c10070904042d080c80d400c0c02c200151015041c02c101500207045007488400517104100c5042c5a2000c0002031450034024208500b4100104542d5400083c000c401c1070048901039980c0d4001b14041c01030700c4903084000c2106908840d2a0300d880c1100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 7358002 1250 7356752 7356761
    0x7080a05040807080c0d0b06040e010204090b090c0909040209040303090209100617010f1202010c060203040f0317010609150c0204090507150809030a051b01020301060c0b0109020c0c060c070503030409 88
    0x692100e070143c610081580003000c1446241d00317900402a61203c100364641501305400604010741c415661103c8107600c90b0203001807c010300001000180e00d4046a0501400c2d4900401446a48004003d829440ea88248655410680581e00a0407a64492500350300800c20108069800f040000c10041640c1051031540140c1d5010344d14114002500f1540403050707034003809407203080c14070010306214a4404065288400707005161402e0021440d80300c400413030740166000c0c3c804120007403c2406064005007076440c00d040081001d01c1541c507015005283d144d190103000c038000d458100841449100350001c07000150020000c000c40e00c5180b500a50307030b180b14407510003881c0e51020880009402144617600c909107540143d0319003852410101d806500880c03006842280341082600701007402d202443c041e1034280c4034a40315680c0750803d01205e990580c07145519a00400175240701d260b012541d450840400e43c3e54a40313490340b000659040c0141508a1505031102040001c0c1c0d1a446411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 7359252 1250 7358002 7358009
    0x60e0a170a140307090306051e0408120903040602060109051308030703050411270408070c0b03070e092202030c041109040b0306040201020618010204050909010c0306060912080306040207080a0504 86
    0x6840b4007a01655906204600007140c001c00800c08504040001c10303e550440303940546480080e44008a1700344844d0340f00714058400307690480010031034440401009107410b070480e400c40011800d0900e0b00c08025030313980c0140504403689490342d0100341e01c40c102e082440d038031a0380024181e44900d002c500080003040106c90503102c0d0310fa103c10741c82c0030b81001503d207445a1540101100480304105850314081000b0784112500c0381d08120b02c80104128650103809045a081707202d03640d0800000081606062004251190401d40300340000b00603902c0c42e0b40c3c03082086581c5401655102d00019080c9061000304541103410465280841c804840081a0b200800c40d03003003041d031600c10141a0350f6841100c000780540c3c04000401c440503450000c0b58916248280094034040e00d030408140d01c040306450050081e910b462035904080c1e014001e09000d440e9914250700c2d82c900d4502c48400b4180175102c0988140000400308041d9103454040707548564015181580d503000030240140141c3c000d21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7360502 1250 7359252 7359257
    0x302180906060105030105181807151106010e06120705060309010903030e1207170405040c05070311010b060301090c02010f020714060903040b0a030f14010611010c0509060403060e0a170a 82
    0xc0042c000e9030180e42500e068031b5020b0044a00f50003824080462084007412407443e0b101c060280021106080044502800c892050500c8240d80880d001c2c103100085101c5000e603410a40040c4060341d018a00c81740c0c01182200c000d030171030054441c02070a000d155005950840000020400c1c501c10541001d010702e80300365000c200074001542419280d0081d92021050003400f0486800072a02c200046100c9c03d624140e100e240c20360b0780000a0850b00c600105074085200402d241c42070682005082040403400d0009001151482c0700103a110b00c41406030110459482c001e14203503034400d500001003005500d1046503200000d0418481d0320a01c0020889035105940000c1e100f904080f00340c4003261810703201c071804d003c17048500b079000c5c106515802002a5031030304404480049071900500801c0e543d01d80c0414007240c000c085080d503542100e010706004080244041e2074170f807481120102c0ba04940001280c0b881034503c1c90038220807000181410740303d0310080381c0c1c8a10003002044121000d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7361752 1250 7360502 7360513
    0x15090108011a030114010b03060a08030406170708070212030a0204030503040902040302100908030a0509040e030307030506030601170601030f03090803070302030a08070c0b0a05040206160302060105030705090103260403021809 99
    0x30000c140c00d031017030340c00030042c01d031200001000782c0c0700c003080510740000c8024403c540d1141c48149582c03a50f08640d000000140300282003242003c40e03401c0441d0401420b14100e81145050b03000651384010300241c40541550000003e07000034090390645007c2c503402004c4da50748541d103ca5a070080e41050005a110301d00c03541c0102c401a00504c68003040352888000703582041e070b200c20180c0d4142c0007030303140720303002610784444200500c41880114032644e4141c900044509002c010b262a08034160401d500307000712032940888821300020564116580005020040e02d51445c007182d02c150030341c0c0404d440d031002007000000c240d0044060401d46401703603940003166607040001c5600b80720403000580a8600d0f070300802c106c03080c0764000a50150014001c549001c0008c842d0150030036003010140e0050300070000600580c0780c00c0c801c0c400109000c84180504d035045d500c078030040b940c10390313400004014001c136041c4a080e15082039030015900148005e02c045500000414000012210b0030018081d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7363002 1250 7361752 7361801
    0x106050f03030a12090305070b160914011b06150305030a020d0504050915010c05030a05040905090a1109040303090f0317180d14040504050406060302090702010b030d03051509010801 80
    0x1042e01c40e030498a59503200d05814204281c00108100e4400307901f040420040300c030100b600b200c1c006004134a50642e201f1b165409002c010241e031001d030070070028981c224445541e941c0e030100003200c849010f8440c43d51041900c1c42d0060040181d801364904030703080031200100780407000c400340c8071000340c80d002c0c2d40343d9552580307080354580f1490140035484102140031031805c1d604c1c0f0608005200b410b06050540181c41e458840c5583c100003145c0e400200006414007810f5900d000d45504010b4001c020b08481500c0e2f519080b2001d48003402902455030000000c040c14400d4005807417085e00700210340442401d03420002c200804034a91040808101400300300404400300265480020800107410720749090b103001c4032552814114034417010341c11b1001140c10392795446024040c03480350340000752181c50351040c4820003200419840559140c5400308003d40c0300420b1081032522a40380004040d03a50441d076090620310340f104650440506400405e00702ea0540c04045c05001c6211101040d505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7364252 1250 7363002 7363009
    0x90b0f0d060b030402031e0727050907060207050603040503070303091a0109020a1b050705040e01020409020c0106031106040f05210d0c02030105010f030807080f0405060d1505010503090303041419050106050f 91
    0x180311f0b8144d1101c1d40701d4002007041c01d42c00c121b20529503403034100c0c9005264941402d50140c0300305654940d940c4d0414203041000c07580401051000700020b440322415441c1640301c085c5ca9001d408006802d15841c0c1c0c500e80700304404000c15070080c41c08469524102d58482112000a4000d007140c2da0101e80000380d0a00400b600d08103041c4220343c042c000b808854104411300018081d00540b91190790340911012400021900107419a004807a000090300c41c07460070f1914002800030b4055004580410051100058041501d41907403415140b0b05d41d401101c461201d00c00400319074802d038a00032181211241940b00e1210003a10340220000d10540c0d032100c2c5206d07044203140c4401440014100304100020700100003401500b5100c0c1350483c14283d462011524580c004030802c401c0340c0d030780d400c28000040101d1219014010a203843c0b400c500e0083d4156139240700290010f001124a0848801040c004014048005050b0000c10340c1141843c03034118042d10741400381f1803203165043c050140604 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7365502 1250 7364252 7364293
    0x30e0f03030d0902040609060b03090d0306050303040b21040609020306012102010e0a030803040c080709061d1504020c1006080102030403080708090c030607051206040c090b0f0d060b03040203 84
    0x10001000756103015a207030a4200281540e6000b02e8000e516050001400c003400d1003514000d0128881266907450404541800c11030390790260401c0c140751403028071480e00c002003a102a1410002142e07a11000c409a18401a190200c841c10b8174541030204001c11585400c0442c20520a804031050f598036403110404040b0144d14a07600c50800190803c003540c0304440e1502c41c00e0b0090103180d07107035440e6151002d50fa40210b60a44920300c2800c030400102d40708200c84001407480c0202001254201020b50240250f40d00700d0601100e04813002c520382e4030780058206035160000700115980d1090540c015103074880942d40702c0340b181c0307070000c0051001010b0013141d1040781e0556400301c1641c0d900c6015150780202401814062144080c20149900c0801c05503000d4001a1902d40d15441c001524094501c401072259000b1410000c4907000150040510f60584a00030b003000e80312745d05d48000b1000c0340200c4c010740c50503a0901d5000545124564011b6004e140241e050b12200c031024906c001001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7366752 1250 7365502 7365529
    0x10e0a0503100908090909060403020607020a0b010b0a03020c1b010207050406050f0405090304120309031103030c070e0601020a050a0c03020901050a0f0e0c07050a060c0813080f03060105160807030e 87
    0x150488904031a8402d080d40c80419003602c0350b0121810881c07030700b01240c030291040710141302c9903100e0400d0105240d0100b00e00350744621184002c01c1d101820342e03038100d9810410302c80c00d950514082205020580030303170103a1305150038920440781060106401603250b0320078074034800c0c0540594440811f00781428051801a00c07405130511809014003001d0200402000b421410070340014031001c2410b0015041ca421510f000b0303074610039514154141805444c104100d1345200768810003c85844c17600c041246400c650000e011045107a03103010060781403040c00d9500400361701171264a20200440b002150083c0c038025240e62110380c0e242c0003404126002c6000312150740c0050ba008102007810f040341980d000303811030f04c0f290074064150344603482c00300038680490708203807900800e2080d29071101545500480c800e8403c00d1800480e1124240c6100324045003c0240c2c000001030404c0c1d01803011a040300c00d1410740048801c2003400e06041c00c0c2c11110044000501c0f90701d4842181ca13001240c0c1451 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7368002 1250 7366752 7366759
    0x112020a0207050609040209090c19080402010e090403270f0603060b1c02070c0305010207031202030c0901030914030a020d0807050703080604380102010506030105010e0103020d050307050d0c02010e0a05 89
    0x20b28206010042150000c00b4a19030140d0204045440c54039081c469a014403c0c0c0079120380c580240d08046008000400345040800542504000c051b070707880380480d041c080f810345000402ea20f40f401c0840380100381d50ba2070005194000c581c1c00001035943c44c0351048418040c001407003e43c42d40350407029030f811486400b06c41ca1040c091035a8560303030301040031a0b0140712000103152203850b55890031504029401954903942c0400c010040c940c2100104210b0101c1190840c51440c1240080c4058040c2e0b1600710304141d5500d4072907003040301890120041000c4c0d982140e491300d22602009540d104034151040004aa8038042443e6a01a00580310956455141c9003255600c20007400300800075070f8080d80900f1503807810010005490210345000800d010700c64004545444000790030341e5009003842c8e000b0783c0740100400039074a202d21000e0641c2c0e0b040b191390310008c5083c108030785507000d00d00340a4154003404c0007101205400880300b88040e407003038803125100382d8401d0400c101500d140c4241c0342c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7369252 1250 7368002 7368013
    0xb040509030301050105031503060a090302010b0108040b130501110c0609070f03030203030408030a0216030801050a0f030b01030b09100c0806100309051b010507080705060601031103070207061815020604020112020a02 95
    0x4c558043d4002d10750003503000c102c2c600000311180009203010403d0300c41c05085986c980380350051503828040d5102c1d0b0b680a00f480005400c0c10790310840100801000900e00c40020b8150340c0800c0800e4003d1b162045c04240d8542d124140c140320f140c3c40e203505031740c01c2d1238921410380001001d14042d03c007401200d030141c02031800e6560f0758480c05101ea10041551125650800040c00b02c200004d4200d6001da0083d1741d180015070500c0288141240c003a0440780031074444000c00c1001030480c0e01800c1c1036981c410400c81c1c01d81c0750f0701801c9180520500c0a40080c0d820f01c222082c240394007080d00c6101d840d04444007266a45401402c0c1c0c01c565900300080c0868000000190f640c0010054401c0300080c18900b0a20b001d000340c680b4001c40e00450001c4442e030f0000403e00c9090340c3c0c14001d103100f524a088207d840c5003403821001e90b03500010701c14101404400041544c4260240c080b10004104a400c2c0202d011144000291181d8048a04030b01044031100a01d400481920235110b050b21940c00808 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7370502 1250 7369252 7369259
    0x8040f080a050c01081806070c060605030f0a060b040b06070f06050c03040b070e010e0d06050604050105120703110414130204140603070b0304020325090605150a05030a0b06180102010b040509030301 87
    0x114107850061070301c1da100c240b1b40589500381c00100000d07071040310156540c5e21140000e04e044d000781c0d10340b58080c91003503100c03e500251040300031a80030030745940072000080051744000414044c008000c0215406a00410f01c501484005400055180d101d0241089036590f070300c0111120303010658000e0302c00400740002600c0e6038000c485201034500305050040e80c583ca20800541c40014025085605035214010b005690409001d22809010121541d811591140407901d545901520010701b028000b02c60011050f00c0303603403008203002c04000f0410210701e05000520203804030802d04030b00907403814240650048604da2a1409408001c024000b103914101c002286c581003d0010399240c098003400c9104011710704d40103e19801207403c141c480929001b0100101c83d91076210600030034a0101d401c000c0c070910317030813030b4086e03010b44c1401c5440c1d813220320700d50005020b84604c0b035030400c000041c6001604880440300c14214400da000740030501c0850180000d82c1d0b03094805c1c00d0554014070051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7371752 1250 7370502 7370507
    0x70305070b040501110c0a0201020105130206031f09110304030e0901180f1104060f020d020a0302030a03050408120c09121f09020303070c0b120a0b01080624030408040f080a050c01 79
    0x64206010f4400804e07484804071188036180c1c403c0c103041c41d091307211034036a408550302130181903401601c2025030060104250003203212880001e0038103c8a290042c003007103090a407869082c000e0700d407100c0108100c001400d2511010351054505802041404201074207501d00849403505848412503e0000785010241c1c00c1c004c0c15510703204081030303a150480400c0941950740980024003540c5d0340c40354401c1c403003003010b8180009408202c045400204184003c82d07000011580110080d01d0001481d0f941c0e428524040d010351190002c1804c2400188003c01d000c05000d4004001c00b180c0c62a420103a030101d00f41e544018180544106502001c2e81d414100c0d681d20880c040c50000e41642d2914001e950307020300e50850360300032601e07003400070905814030890603001c40c0e841a000c4004000c12481040080c01011000342403e00c20000c00c01a030f0340044085000e8119044003200c225101c0c201840d110540d40c010b4003880f050140c84407000951403100007902020140c11401803d160307071105004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7373002 1250 7371752 7371773
    0x8030702030d02070506011a030c2a101b0905030709050a090f0c06031104050915061308010914010605010f0c0204020f0304050c030d0e0a0b07060e0609070f06030207030507 76
    0x1110a6000910a80c2d40e006198001003064a224002505440d8108281c10491040c1d03104000010b9030180308001c6205101000c850004200c4822405692000640b24181540703814480286016581030b20021004d43d402140c0311000f114911240b0381402da5088800000314401c06074164004802045000305a501603900303d0540c1002040b08032290b229a0400010303004111000f0782c0c1000200103080c0d1510611358040e81d00c5480c107191038503040000d41900f002800150003000104100300711541c40070111954491540c680d45c9160780e85801c800d0003054500740903207001c0194118100c2e448410b214034015118161151440c51110150498245880071402ca07000741e03007003110250109260010b14440c41c03150008109000024061505181081c0305100600100000c02c6926070b40b503401301c60a480c0885049074540c017031428141d024105840e0503100c2c50040310b0501030b49840c081000000d40c3c0c000096131003101d58400c001c40881c0700c1c220b006000140240451400250741d0403c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7374108 1106 7373002 7373011
    0x30201050c1603050c0a0203010606021e010509030f030a09080301090b0f040515040906020403020406030c03030807020601050a0501121506030f0b030309090403030207020d0b0709030c0b07020109030803 89
    0x12040346540b81c81038001c09000001c58000b0030340e08100440d80d003140d0014000d00525590f03080203034844040a12109a15241b40040817482405019090082000c2c2c0d0085141400d841e140b492650000780048011684480d00f0102003003a610145029200c1a0400601c070f400301001c0121013580d80708054000d9003000100a542c05618803410394510040e6008078070f140305460158000d1240d60002580f05d85883c03404000d02c049441c0c0035041d03d10039100c001d41034440b0303001603940301c00034803505501c406a14818845540b04004203a103607804403d0101d20a1006031200084030b101c0c0c0c1103e00005e40e1000c1d902d1400119004140b51590180c01942c80c00c4030344408038016440082025083c550001610801c54640552400c0c03540c0c0c02005500c0c0c1401d004100500d182554801501c111460b103102095145104084800d85a8140c640d803021a00d107a9614165400003030 = true := by decide +kernel

theorem cover : BRFrame.Cov 7194252 7374108 := by
  have h0 := BRFrame.cov_init 7194252
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7194252 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7194252 ≤ n) (h2 : n < 7374108) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
