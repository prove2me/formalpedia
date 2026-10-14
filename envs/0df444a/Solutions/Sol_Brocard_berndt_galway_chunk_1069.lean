-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:06:17.154197+00:00
-- url     : https://prove2.me/submissions/0139b28c-29a4-463d-9528-ebb7ab482f92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 192086330 ≤ n < 192266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 192087580 1250 192086330 192086369
    0x506090a2a230406080a060b1e0103090804090218030106082b09050918010b0d0203210f0408060402040e030406090605030c0910050a08060108070c0807140a0503070606 74
    0x400d8042886002c50101c1280642034582903509000c51008000500611000c0d8598407482e0b00c031803104e20102d40303907468030109107054102491a45c078000804a0b821121101d90700c019030290280660483d0209400c00001c1001c140c00c0c0b014003010302100c828841c10402c0d201c14982104d8843e00182d0441e403011601074a000c1820032480d0060700b2250440c04006002e500588940b03120380c008691008000d020011f0100000040042c010408402488500c0c03a1405001100a043d074010303426030046150500c03641e0700300001003640180c1c5035010b86003000300301c8074070b1003508140c00148154112005010039460180291681101000301a614051515402a0050b24244104010700c0300100c00104924400000e85001400c045d010300c00050308564000c1c41a4013022a200125070598042503aa52003401940e1080c101600d50714400e006903102c1c4cc0850700f00103821582c651800e18004941d010610a603020703d88502c00540e00c66100b80b6100099981c141c1080741840000039070804c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 192088830 1250 192087580 192087653
    0x1d07030c0c062304060b0a060e03070306021b0109050f0606060909010e250f0809030f09100c0c0b07022d0f030708070305070602100c020a03030f022215020102041401030c0c0506090a 80
    0x1181c0e8801e40050f0b80e4128400c0c1d553f01c0d4040003681045035403034032110b0400d1000c0410421002031994040c0c81d100e60b2031000300070050044207101c036003185883c8010b11841d600d26403031a4112881480102e0340c0d4124071107041010204108450000d0f62084103801459040700140307401c92142405103040101c9200218070703034010184010b01c9150642085106c01d8000c4448108441c4c000a000d607405ea201c8292041940c0508400ca0103800310300540303110b00c0d182804461615107000c103100c1c3e48203041005c1205031240040443d9160081010014904100708100401107210700c0152025502c0c1250280c100611511420202d500340381c156040940d000c21200216a413500f8002800303d80481202c0081c05040e400320f62080c04400c0a90990325007602d03050440e55000a891001e07812031b0012800d0380100e00c60f52541d4101130500d13141b290b0080d000320040848074a00100c0c4a03c050f00c50030319021080e10244800d03040740c049081402803102c580705048050030149070715032460050700d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 192090080 1250 192088830 192088843
    0x60b0903030d0504030c0501021815161101090503070e0901050f010621020f220506160b090a020306070c061a0102100e0c06041d07030c0c062304060b0a060e03 70
    0x42e446a950000601090700441c5012406c07900a00210749417840790244a10201030a800c40744100100b06d18600380e40181012030308082d6421601000c1d400259681801032055146014140b00008c040451075860800c2000010b0120f400c04030400d0038004442c0d402c50384050800c580100c40103005110540d007051700b44042100306174292182c0010b81103c2c03802405219030800c2c4500e40000c3e00201d03009118105283c1980000075100b4244d0b42d401080b40c2440b030845140066504928690003103140c00c3c011990103c03003401036130a51001540042e05095007158030b840842c1000c6001c00900c61240318501d1203203140c007031441d441c84033070780040d43d907400c0e80c0e03024107500740c880c104002140c4042c0316104031070201405180e11207403203101070308014560006e201030407000c08000882e030f40d1083c0180a454841601c03884000e40319038840700050040400c125060004140c00d0003070240c0c1c55114140f003940140e600148448003081003105038520b0358840700800200611107030b99a6404a0340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 192091330 1250 192090080 192090097
    0x10e01090b0d0b0a021204050d020601090501080d0503180304031b090c050f09010306080601080c01111501060c03020a02060d09051e03090d260403140f120a030906051801060b090303 80
    0x4061544c0d030b00c00c0c0d1140130b44580c2d00e00000c0c1c03006080500041203000100600703603401c00e07000e07a0103c0ea00c900740d08044500901ca880c0d040d80c440b1503c8020342c3d01460003550000e0f490b080d08405500fa003040781d40355238030503030044503c810b00c4c400e504000140003098202410303403020184940d0a0000009100d402400310285a01c2c8c0d0000303c101c101d80c0242d014400508004080d91525030351015415202c4904030106070208003008189004840c1c045040071201450780540c00c40c990070554212039800d00c134501281540301c1d2401e8900507030350300c1015003c2c40e01c6240000c60401d842d0320b4070500b04941280c0340c41564800307a22081d04460044140c0704c00e400c0946490514121509054207004540010080c584142d0700400400c0b690500040040d80d014042c0320031542140c030010f903503c0175404004456600160442d032401489c5a000300800301c0c0a00d0042038060603621071008a45003903e080e442c1031640d046009605800303000303a5000306100c1c0a4a406c0480e0303880841d071a4440e2400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 192092580 1250 192091330 192091343
    0x20a090f0207060504031d04021930020406090b12010e1f1202031603030903030c061b03060f0801140f090a12030b030c0a12150f0212010e01090b0d 65
    0x46401a00344580d05807040b075900b02005004906007804c1c05000d050000820521048a10300300078010b00b018003c8890051b9001d1407400150800d11003101c00700e111000300290f03010740c19055089103c2c0004800c40012400c88010790791494004040c00b0a10290b000b40b03c01c02c030a2080c440d01e402c03410201030440e41c030070548a4817566440308088041040c400c0320303000103403603420104208018039400c260062080c0d0031100161400e809031008000244402000100c0c07400040c030000740300d01d2500020501c1418041208500034482c058141d901c1325542000035504c5c082008104595034181004201100081200c0c0100c030300b80c1d08403000d0003410010988010341c0400d42c40070040040100c1103401190704418440c2c800c0d002030190400580091007403145903440003491822a412000715698070060102043d074541e100440303890043c03c00f050031680c0d1500c3c40d0380780d00e00e4002000b49408001000080c0d60500c4400350300c6034811b030000f2103541d207821403080b5540c0740c882c1480c401541109 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 192093830 1250 192092580 192092591
    0x1140d090503040506130e090705100509030c150d051807090b0307030203030a050d20090f04060e07030905010513020d0b0c040306060311131e0b01020a2306010909020a09 75
    0x184585584203da0040e50040f9000940f01c608800000c0c210043d030729440c0c0741d000161078184d0f16a07589d4a050050642c0314000c7d440c0d0786402da0091005144a61000e000d0b04c0490b40200700044c0b02c1907200c441a42810000164070301104018841c0315407081c0800c0207101c0445414a40d2590340a2500410f40880d59a041c0d0051030b59040100100440c1d0040c00c413917507040d42640042c0241c100d1850510228141180c14170796035044400c040650003a500881d09000808007040000c1c8089400d01d900142d0b1640e01203480725164081034418241a100404c5a20440c5081800c5a0b0002c1405007204c0002c580302d0010398440503c802480e4020292000035101c40c051659140324540c00185a0313850f100c0000100b10010840d034200103011540d809440c2e480c0140c0301d060743e41c0f000c1814660720a00a040d00d002d405035200b0355400806204544d0345807003580d55510b0520013243c040c0d02071014480f5030500c021040000c2c50140c01056424801c250306e035804145011032074000c0405c20b41e25407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 192095080 1250 192093830 192093833
    0x6010215151807030b150c1f290f0f0306041704080a031d060306220216060e010606050c0604030e120d0c030201050c0f030f040f210e01140d09 63
    0x1d81540b400c1c0380403000c05104500701120050004c200310403c0e64000c03000072402d52980000390040d5048021503001809044e10000e008040e00e0344910042c013070140da10100c1c00d81d29048602a80d00454080210b03104e4200da0008001d465003041c580b1900c01c1c4170079030726855641c801007043ca402a91004104006294260b80210700b07000c0c98008940c603106894900051503840040701028541e030201c1d0001c1070b0001c10a020320351000700ca19640010b0386000c0540310759541c03549c001c100c11055000604107003807801c2150b058001000152100f94a0b01d02c81e990140b000e10641c80200710701d0034003038a03102e5085000341e1240d4004001a0500c4001050340c1002e171035001c040445a003071201075895003600c20340f000e004606819400c0d0019860305000412a14010048954007001210568150359880c1030890009900420488450f54601000000039644040e030400c1600268050314200801110040c040e40700f1030205810054500000c1c448481c3c0d8000300c0d000c0441c1c4140100302a40d69 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 192096330 1250 192095080 192095089
    0x8160c0f020a0e040318060807050a0e120709060806060901080d0806150304030201050a050f01050a0314150108060109050c0304020d14070312020f1903020c0915040908070303050601021515 83
    0x1143d01a4414151403401c000c10035038482c42c101041034400b0340018a01d904c4402c22103000307404550a10100700c007008100c81e40f0b4003d0030410040c03003005000c0380785542c124a0032420030710b80740e1200100e1521103200740710702a410301040380e1091064503400015890070003455a10710642d00d541d42404100000304090340c481889042030750380709124440d52800d09140080c001d00c2300f10f1b9030054440c42e04020990049580307240c581201c02c0200b011106508586508000315650f03032f5801c549120301c92701d0080d0790300482d04843c02014100b000e8442580b60480c103000340d8500030f01ca458081070400811005980c0d5070840012260090110303844018400c0d5400c2c9400425007021749402c0c40540501d00ba29400103100d4401c1c11003c040d21010310002540d000d100d00510390040141e040301040b1b00041c01c103401305642c0440d880c01c1c920394100c100302c04901150742000c0190b448a2000481c0c03814103415000b4180c01c030701e081c4001c0030025800c2104000b6a01d000e01121120004a801900103a42d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 192097580 1250 192096330 192096349
    0x120c09040804080109120e010c022110050c0a11012a0e09090102131706010b1c020d022703060106140c010f0501050f03070b090f0105072108160c0f02 66
    0x3e14074001c100b40981400c1540c207011050140d140020140e4610b09000e512450025003459805003507030709000000b0b21420030b03124503840048054400d08008945400490007076038013030f44421586c0d07683c410524100410001124808200903030511007640c2110700d00715080d494240000c913005204c0c03281c0c01c0341120f285000e94079140d0b002c40c0b03820038070001384410740c010300904060f6600e9401095807080c1c80203011081c144202000c0e044a001000114040d20040c81c071848019117222103945012000340c04c0307070031604001c42c62170380c0030544d42c102c000708c40c1303451041c040700e00d12840345006200d00080d0390b01c0050080004202c004502d0041d0213142c3c80658140a00041c000d02452001007140d8000300b509200d03c521500484940809600703010035040e05485140708110b00e0416010b084c0704405604d581b85504201c810003a48011864840d541f240f21850062503040e26072888800070714602e00540030944010107090001e41d49500132400740362541c1e01c081c0c2400c00c0c0c0e0245c00050907064 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 192098830 1250 192097580 192097589
    0x70c062d0e0607020c030a0206030a1104080a030e12101e090b040213050603030307030513020d0312151503090602040e04080a03050f22020a080d0e0f120c09040804 72
    0x200d1460000e40000095000a84051100d5040395455600c019040341e603007181d0401c460301504000c5880015040c80c0c801903031302844c006008640c40f481e01000c21460751090740800c986410030b50703031700003003580c4000003903040b0100b02c9102d0103040c0a80030302c035183c0540514140c14903982d46d00303a408206c0030b000040b040148011040100d600300b2f050204c1810b41c02c5404a105100c20000b0310002400340c800d540c0529406801141990343d800c03800e400501028100c180300d184000380d00c80059580c1d11086101c140b0a42da160704c0141013018500569144111007040b9903c9440188003602480080d60119070b8a45070104085000b030404900030304c2030740c00c4102100352035000c000030f02207040004d005c0e2041566041085540303080c96048081416102c0200141c00c98520f041505202c11a0070503050004007007944d6650f807640907914101007001c0c61804103616160348001883c05801e002c0c07060f41e0a8540791803454840040c9511081007014185c0b040c404a4003240900003200306480140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 192100080 1250 192098830 192098891
    0xf01090504060605041118040c0801030f03020316060b01110d08070f05040b0d091502041508040201120c180f1412150c070b01120c0512030705151e070c06 68
    0x81c2c0c5086c0408199482101301104500c2c03841c9000045090604c43d141c90b944003036862a03032076401c5994260484890100603811448188106c03004c5c03200618050b40020300c103010001c2c001d080d0000162045546004a12650f00110200010182c01004032355220750140f512210b130031300101c0c05980314069a041481e401901080c0f501b000a00380e03011150540c000e03480210140f264074049420b80c803550107224a000c0082811a1000f4080ca0302150014030504000203903001260b1010112222102c441c80098040078108500714205502d0340007800c481001400441d060141c05606d0240904039103000c1c458980d080703005050140540500800c551074940f00f5400c0c4108149403d801410303040c0e915040d00400020318106c054a03410365135600540d82a0802c1c41c2804008000b009006085510700082003c81b002079001d001d6000003940c20f20250150782007401803502c0458410444032010f8005d04213105103290050644400140d00c124040751007181000383c4041c00700031803507440a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 192101330 1250 192100080 192100091
    0x150709080a0b0703050c03070e10030b06030406051602010b010206061c0b04120f0905090708100b0d06140d033c200c0d06091703070809070602060f0109050406060504 73
    0x1005410400b02d4050f28403a40c0a0025440700e8501080d184410b541280202d020b20581c2c02e02c0d414414a189124010307401c000545c1d820740c2000c902c6503801100c003229819540d0b4200012486451003001e01e2081c903100070880b944111001071b58504014101522981241119940b0b100c002c03040000c20a0340040c0e0012035003058905250366500581e00740000c59a00300304030140c1c51080301e1050031510001c0c410000390321110b8094036006d9000c2d02c00c040c2748102a034007103000078070304004107110042c0600c001011442c0003148440350304800d81c1d6901c03074072404050501082d40070320100382a564110103c0c0740d503034029100c069002009010903051400090340404116040890300c503490460130100000810b24840042d01e480941682580c0b041d00d160201002c903020341c1c400a00d1901c91800110b10500c0c0c1006d0384480c0d003088a01d007000581e001e08001c6c00c1d20045c00070f01d00910b150700040c5404d0810408812400d401400340c500361959070b400003030a205240d00302100030306018200300903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 192102580 1250 192101330 192101333
    0x6090411040306060608040f0b070207081902190f0509090114040b04030e0d12030e010204090e0c120c0d080702042301050414240307081609110705150709080a 70
    0x4032a0440e200c1624000c0c80d00c82d00140f0140900740d5a841240d01c06155021813a842e45d4021190b84d02400c10821071060311400700c1c96138001c100090205004c1c0c00c0b1034004081c03910420440e06021703007200c6810401c850007048428114164101900c1c0b044a501895a5a5001e2907006007c020482007008101c142032000380440303450140e001300e0003a0350b90500b101d02d620074001303900100e5030001e01c10361030031040c00b0302144244c0c00b009078005003900151403d65110404003c0da4020034800e4010b40010a04d0310141ca000c04d07003041c0e01c0102d03030060000c0351780b400000f844940745000d014140501c00034540c4215503507684611507041c280c2c9000303c010307009100520b080401c240602c2e0300452030070901401502c046455180300e445581c501c0540c810300565181c1c0c441c00c6141c103403901807103490300c00b10340200305208441ca4400400d524050045c681540101a1400b001420907029000c00441d400307c0c0c0e0101d81581110200c080858468807031200480d080550f0341d010300ba9501420040c01c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 192103830 1250 192102580 192102611
    0x206070201082d0a0f0b030a12020304050303030103060b0918070e15060a020d0f0e03340e060a06030e0a02010e06040801060e040b06121c1206060c050609030f040302060306060904 79
    0x50146130441c4040210a440b50004800c42c2d02e000805603040d072140200c6800510130031380380c0301e482407a44180c82c02e26940b0f0000c249182c000783c001b2070f5000d494010004a9040019005038020b0b80700350501d00300d076803c2900d20388504480c05549550415800041c03540c0b010f09425032031544d800781055035203212941d0700070344600140351510000b40100c0c2088103003a20034000380b09020701c010064070f00c46030110142515200186042c00504030110010b500310300c0c41d8002c000061103031008807541450b0000411410107041d41000d4181440c042c4c05510b07002000600400c1150b0a00340f01a1035440180010468000d50780411580e44c207001c3e0119444080318895405a44181000b0700551a00c0c01080840444121007284d03076442810380340c182d2003001c1001040d044040c1000c80d818811620040140c2e0710541001000c105102007145c200b200c2041f00541c003880250165003040300400360400c892099100182c0b00f00f074040007144842c4d0b1400103c1700050341c02801004030144081924 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 192105080 1250 192103830 192103921
    0xc0615050a06020309131109090402150a08180102250212010213180207050d140c0114160801150f03060503060a0603021809060406090f02030d03020d0605010507020607020108 77
    0xb6400380386c4103024140680424043e00000ca00302d540c5a50410050074244a8000380081c0180d074000000340f00401c40d110000e006050141017a51140014a0081b5a4500030325054030038003803d070b1041203888160388800000701c1c00c0120012203180d0014090000402d180e4a01d080400304d94800a0042074901c0009c92800c1224a0601800141075541c03075402c04074010000082d0641c0c024040c1c072844da900c21302240301800c0c50071a03842d082031440e407911400c550b20001103031801c41c0680140400340141c003800a0f005800c501e4804985c0d8100741003100d1b0401e0024085081c01307504850101d4031402178000c3d00280c4800f070103c461f14a040c0310a1340192040784030990150158943c04803070880c18035490303442907020000404454443c2c0d61010000d01d00d41906440007008410080b0041e601440402c051541c2c42c4d50260326551910682c508075045a88424184803040254000680b600015641e500c0c1d02428001d01d180c0c5e444404012601da49443c2034908070700681c81440441c060343d0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 192106330 1250 192105080 192105097
    0x10605090f1503010303180306020c010911060a0f050901301803050711150c0c01081005090c130f1e0509060603130c0504110c06060f010c0615050a060203 68
    0x40c107000380340c5071091000b4464107507440c1c2c100d240204014000320340540c26205c00c4036407080391100320a980c0c1e00d6181c12a0054094480c06035180c02a60090103802c40200c04030707140c122541464074403882005407004410100d84402e1010128031908280c1c0201040300006c1d11004010070b20810112046013080d541601b1700803440e15080841004c40015204450b05030340c592100303440c11087d6150044003808561905034480f11902880b5506103201010b00f020440306001004003602010025080c81402449074201c00e80700c0300c0c20040ca0307841501494200c108481150366407030b0100040da281c0b182d180c110307001d20003074940300051450000c12440c00956081d58138415258403602000142241a21036651085050021076844003185007000600f074403070441c01e9415541c170000704050392030b104640701f54804003013100d06060b50305000d480d80c440070440c0d544c0311b9a0041d10001e80980540e01002c0c080c2c030740e904080202c110605801e9009044000c00442d0000d43e500c034000d5580d40190b54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 192107580 1250 192106330 192106339
    0xa0e011d15010b040e070815060a03020a0815030a0201180905040302030c010507051e0a2f0606090c0f0a0e060301030c081501050109090e010f09050f2406010e0f0901060509 76
    0x4180002d03c1c1500c09503048a00c0c3d18405448104003151086130143c0304044001c3d481024658076501d040081c5070088858901603182c03400450054903128004100d4940c940d078ac100002d000e82d40200b00113140540c242130090b00f0342e001800f0080718034081d42211a42600c1d1000740030526800001619103d0a124000c0c007207a0780d02a012900b900481c81c0300f5072504081d42c440004100d10402800e198000e42c50020300614091441464054422044040000024003956030207241030010300e074008001d80e16800c031800e0408207040d0920a001801126040c04200c00d02c80a00c03507030406041e0b40000340059100e503100e00f080311074054117210b60145485084000540107004d2400b02e8100c07201610341562203841c03c818140603007404840a401e40d561740d0181d445000d82486040d030300750300500080249011f441d40c22450220315600e070640c1865980b5080710b04e0820814960b0b4882c500b841c0c200d15641850002c1921010800c00c4c20781c0c000307060400801c106501a0183c00000012203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 192108830 1250 192107580 192107623
    0x50702030d090501080c0a0507211b0503121009090605070806040b09040b0a06050406030c1518050618030318010315060c0b07020a0503270103020c060a0e011d 70
    0x24000c1d01d00b40c0c4180301d03807404240c54000140c9441c0c22003000d003940c0039441c20042c1c988421661a0540c80d0f0030184200108000d801d072811140c4e6003e40008c0c0140c184080c265540b80050310388981e13034025000100d5030860000001001034191400c52001040f042100784003180e05403a182015103000c442200028050100140740d41c038003402060004040030f070103891141c0361a00c4103c00c181e00286520000354075030303100243ea074039980704142c000c601410207031a11a00380f0b1500560b2040118003401004420009080e031040d880c03100d0b000303da4007111030a03a1003c80c03010100c50440304400170390b49070002003060000b244e1040c0410307000f01c2099904002008107003402c040d00040a0041000054600d106c0e20300042d072442806410039604e004139034008210350340300d52460703110a01e4180c4036184005003010340d030b0356403241d10541c49003406c041d07040a00080f05c85555580041c1030701b500c0c94130381042c918481c82c2035000d100b50500c9451503003903510341c4c2c02c2a16600c618581807201c1e0103601d0b4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 192110080 1250 192108830 192108853
    0x2030a0e1806010807110a080309100501050a15020732010203041401050304020d02090c21040206250b010f0311030a0203030703141917061002070504020f04030501090305070203 78
    0xa004280140e8964403000030242c495100446021200030564030070701c00c0c19241c41ea0000010007a03071003440d126100083ea0382c07500301440c41c14100002e90041d009401c081c01401aa9281c0c00c0350015140d03a22080b1111001c0001d00b21300e01001b99004000c007508903081ca0303c0052481244441c1c040ca800c03115207026401c0f03401245d49101e07070300c500c0b60b101e08101c5c00080e40d9031084005540140c0028481600d84000c2e40008010b540c00f925100d0780036a000801200c81140301143c06040d0310101c0e20201c0501d01600418500c1c400e12807400e5a14803005800341c41d64090450b8801c2d0140c01ca0021116903848484025401e96240001d540000782a20003803d9450002070140003954054040c0d410000301317503020380e0400c00782041d564840e1f03414840e011030f0684c240300480d548100b5540700d112610308211400c2e0404030280085005404000940311100d070000342d04002c569040d980140d403059180345200381c501035034000614950806c0402800c0c158000054400ca038002c50607145021603030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 192111330 1250 192110080 192110089
    0x90306020f03010312091a07020d060c080919050718020c01050705090a050910030b07050f0c0a21080411210105101e03030c030507122d090e070306120302030a0e 71
    0x2e52159850303641c02c00b407060f540c110947e0301034484c1d6440500f500d108120701390349180a84911108250006600b4010000714070360070006400b9203016001c601c40d50036900d444181d11100640210404c0100c20f07002c9015081159044546501d901c200804ca5414202c0b0002c005a0100107011b2040e502c4413808110b0385440091107000e548814030004a4602d50b580d035004820000705001c0c144003091240204440c1c000008000403860b1f1805043c1403540341c940710100d00d08140068070f03a6401005043d0320a50040c801c2078109400c410740d00c0180080c640007941d03c0c403000d8843c40c14122501030a1032408815040039005000b802d901160841d00d9060042140d840010145044004d544c0c040001c20f010f05c0245507030130700030703e031039032038a401c03512034482800c2ca0740b03c0b0400040c0703d1220440d480301a881380900316000d0007000a1f1900c111030000f00842c8031402603000c2c0da80040081418a030090303003c000108443d0801c4c004003c82420043d4894210b20400c0020404070300f8069a40d01c0c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 192112580 1250 192111330 192111347
    0x1003031107081905030405030601170d05070f030804050f030708040f15050f0306030a06020705030d060905090a17161b081501180b0319020f03060114010c03090306020f03010312 78
    0x14102c02084807480302c0021600000d514039099806000800c03010446442c00d001103400303840800749803900308500b0307030400740741500c4450705d6001c02400344910000614040d00207000381d6094130b40280a52907504200c0c0c1003883c035407084141817000141000c2000686000740c400c4401901200c60965900d03421500ca01d240c100c4c0420000704100103008000c201c4202841d04050081c0480301a165903950300d41c101ea00030003041d1155480803400101500441c05001d01a00d03141c44184071a04003c0005035880c0e51990b001451100405c5500310481c5196043d9070071031826460040b1288110b05002403654030081801d480c48000503c0401c00c407400090709104071044411016140c2e20f8440c090804040441e094058280c07901d5064050781d40030000c0009d40c0150b0301c50756000c9009881003119501019411034046e0304004c00400a20840b1900e54400d03080a0a100040c42080c1c81c0c01c4940c103e103a040100786a20120380403000748050405507058a1042911001004860405440300fa4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 192113830 1250 192112580 192112589
    0x60f0905071a040503031b0610030c050409020102010e030a030203040302150402060301140f0307030c14180a09050312040b070e09190f090c030b040b1003030c0611121003031107 78
    0x3072124408110109100503510301c03102410700300c10b091544950000b400c6070f216103400d4422481503e00089214024020203410124003165002c1c40f6107191b8a8403000c481e01d00c10301b03220701d6680d43c1900c00d690003900441044074204060ba5174641c00d0301e80250003908117135030540041c403582d68a48a401d5660900b00e000355001000340e402c580ca410380b03007039075007012001082d080b40d250302e03000807181c504101020155119415512800c2e041070b40d4171203090105400248034051803200c201d080064103108a400c0320401030042050000e82c02c1c00780c03031441503610481504840c1c034100020b115101601c9401030f0103a503602d229203000902045101c120136120035050b1040140488456610b940c0114099400d01b503002c43c85203903988417503603600e000d030b071040d507840b1840c000304410094050704040d8840e510108002240342035481c0100506c034607000041c6901d80d80c0e6401000035941c1c0341030345d01d08203040d84151220300e411002c8071402c0c11244400c402040030f0540141c00c4200118000003580c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 192115080 1250 192113830 192113833
    0x1050604080c0609120f0709050702010c09050f03070f15030c031e0507021903020f060603030f0429040b180907170604110a0207061b0b0c0c1612060f0905 68
    0x6503441040007803d903c4012825441170b100b07481400c00c61030500c0011103d541e8480a4400207160040d8a010b640e40100020116450720b591100741c2604000104c05175441601c0514480480402103843c0c401682c1041c0683e0840b000006100c40c01c14202100c81d48080d5418407518004850580c180d070030340981c4000c3c10b14a604010114029580140d41c8180940f0442d42c03404060f040c402c03640d1402450940058200300710183c101e010402007507401207020740c0107501e060781c840e0f4102554082ca000d8422103144081c18403150351201207000d01400d202041c0c0c16569a61140c10112a0b80007403d55200c010300121544a180780042c0d00720321501994483e01c00d03242d02110011050140141400d502ca07580c0d060f9034030503560040242c41d2001084d00100b100c20b00f00749021b40355854203100b11580000f055441400034612802468001e106a04981e841d031244000c000d003031200101c1c480d2400c00450800094005003000c000024500a00f0100450403030083c510050324204040506a07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 192116330 1250 192115080 192115093
    0x5070b040509010b030714130e061005040e0c04031e02040c0c0c180906060603060e0109060b121e0a0510080109020d08030c2b061401021f060e0c03040b0105060408 72
    0x1d50781c2c1380c0110380c88001403810684442c1d10210701a000d821400340380e07800c4103180c0c40602c00d02801a06540d003040d81221120100e9000b00700081440c0b0039806547c042141800c0468a2440c201050ba0051035001c280c5150b49032807010100c0f0051810380d0140d1081d070078212081d4020740981440c54017950030103585800d00741410590041020307038017042302103560b80d10410800700f0842e100b0f81020301400c0d0b80210703041f860601c2500741c040040c1c0101201e01d00d040d008010007110031007154010301480c507404800d80d40791024144040324032500074000e0000c52041068a0304194050343c4a241c002003d03801407030f10744601c6800c0310110f5070001d4100e040d00d503100e408600258065a44071901030380040ca0906014101c403c00252200720280300e981403131801c509000c00c2e009040107040080c00d03813540c0c1401400000c3d62564448050308406c000d032400c083c01031159400610160481220008483c246000d07a283c0070303407045600f85d03112040c081c000300b0305103840000c641c200c4900384002c00c0c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 192117580 1250 192116330 192116339
    0x20c04020903120d06090b01050c03040909030e0303070303050603060c0c060a0f150b0d0f05061c0314040611010c05190806190305010f1d150a0b09010b0705070b04050901 75
    0xe40c003544040d80c2c140319682030200c08000503030040c104050304801c0841d203d440e00748600240c51940007401d06000047c410070502003000003d070303402c0301c0c0c00c47e00114016185060681c0c559415081c526054040042c60070149038050708040e018007800da040b20b026594001610105000c2e40d0300c003a9607034122401042074200039411440d0b480348421000110141009150714411321150322298603014081074800b004001c6114242d00e45298000602a41c900310001804280b0300e00390645442007946107000c01d240c400c2c0784003695080c410220603980c40d26410080c041c82002c2c480002c156003000c00396409a4481c4040e90214200d0a0f080418100c881e403055030715000007009035400c521074000e00540c07448021901d00c0254002e500001d04491020071140985c2d03013440d844030078558103c075003442000c4000350100404545543ea00a00c2e110102600081d0a0688070150321501034000410306820010050000e00e1062040312241c6690b6450f2070030078000c0b8466260f01c000c06000410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 192118830 1250 192117580 192117589
    0x8030307120e030d0e06010303020d0903020f09091005102909010f0302090901090203041506050105181305090303060a09050906040201030209031005010b04081605060d0c1b0303140a0507020c 84
    0x81c090700c54034043da410809585100011a4020100307541c841c1d0200004000340341d010301201c2c00100142c036088040341c1c21500411010007400c00308070700072400c5000052840381c0902190004441e131120a00140c1420070403141003c25074010401089040815488400c400c0710180c40031201501405082c0f045800041d03030210f2008003080103140d004c108235025540c6031a00305010307050000c00144c8034103090801c0031080c2890b40d1242d0460340b42c0007060205030313085001d98003810420b000c68182000b164020031110304110300d81e22640d6003400203106480c40044082d600c1010141c40f06200c00f80e84400cac0000392902980e03006144d4028402007809940b21303400074042c211001d402c0700c40800d4020544411070b1002d0f4000c00c8070030408203082c4840d40091010800448103500040100e50411001644038420b05140807406503503401040c0b41140503182440e40110050480403050300541070180160020000c500600510301000a0b45c030503440c40742d00d0003401e1079401401e40080a90611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 192120080 1250 192118830 192118841
    0x6080d08040c0e091207061a0f0a050919060e011d0f132f100c0804050f030f06070f0906090303021509070b042306040308120714070f0c0803030712 65
    0x4c21244c0209102d601450300c2d0000204482c510036900041c10071119082007802e0040d541c3e48034404c041c440301c460300e03076507035001c2c0c50301601e008a91b040b00c1600c51054916001300542c1414800c10300705040080c9003031403205024101d0f89030b841001e0380120840c01d8006034a000315480c110b000c48810114084081c1001007868241c41240c03040c040c80380180701080d0000005144002d40b42204405008904002000c2c0094801d5401c081800d40001c2e03030340185038000e81c025240100c400c0303504170f4043c2c2c1e0104448904040302c8801e54004c0d040c441c800420326900c07900e50b800070aa620100080b070a01c90400360301100c1d019070142640c201450b00001d26450007401d00400703889805030215130051040e004000a0a0b001840000d0349010956101041180d0070054400d0390184420400315030030108440d8200e03849081d040d0240d0f601ca00c242d8001981e0480d54410360400700e600c4040181c031b8148043c505004142c03140081d80d032007608554a00c41110504005500054640c0401c10360f90000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 192121330 1250 192120080 192120091
    0x601030b091218010e040c0e01030b030304050907121b0c02040207030908010501120c0b180d0627060b030c0f010c03200a030f090f033306080d08040c0e 67
    0x10754074824209090300b88540c0210841a40200c146003943e03100e50380155003c10307442d805071400d2040c0d008540000e02141d20300c0340340a051603220302c290b0030a0390f0b041c800c8030042c14006110104505007010003e00200140c0340142c01e90b450704240040540d00c08c03000c03040305d104640d5404150f0714190b0902c0069040301a040701806400d00d00415030100a000d9240a0040903010100c00e580b6030500d14409032903680060cc00d0785003040001c0d4030803510f00001d010031000360340781e0310304082c01d25081d002081c2400b01c0b092880008408402c00306101e030b103900e07022801000700303004041c00b000806407145403c0c98050362028681310342740c115500444400700c000d4081c0c203181200a00190036091503500700303d480d5050340c201d911150308040d042001240c010b5030b41c2c5031000d896030625880f400c810500740800740803200e031518010400740742201c00741c801e201504154a0966203c581c41c2c0003070110703401401c0c0c1c54000e46003103412592283d62658032494018180c11309240c80c2646204121001400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 192122580 1250 192121330 192121333
    0x402090609030109470903070503040b04090c081311030a0512220303080403030f020417070e07030b09011a04050d030512060105032e05130f050a0b030601030b09 71
    0x3a569070340d602845909241401100b8510b2111030805180c80c3e44014014403001c079a440080e40c601c3da800c0c210400d0010601110a6026034892003444c0b403440c00f81d40700c000c000d40300010707001c158000c1007030180003112418a4148041d28007400181c2e1054030485003a140c24150913440c07070210300c02c04d0508150f2580541641e02c1400141c4409040c0383c0302c018004204ca40c00680d12a4590300c1c804044a52060703918182078480c2156001041d101000e400a003c15440e92407507c070486407030707040710014000450403080c48808a41001e80741e80152185005082c500000510050b01a016082065500902c0451143e003050580d05c503624a01c039171907442041c00e21000c103403502c81d00070b01c0000c58000c0d06ca2940380e005000c48011070792001030071b041c100b1106000348401640d00004450b4a02820004100404184e100c00360014030a50300c5207a004181d410302c5514691310381d10028052059140c1444130317130344241c82e02d01030700e01d01400035416600090042000c00c0e450030a4a801c41c40308030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 192123830 1250 192122580 192122587
    0xb04081c0e030109030921080f030a1409161a04210c0b03010e070f0e0f220f14040305072904150509010902010207060e0a0314060610020309030304030204020906 71
    0x21a0031184c90480c00c40108051450602c882240c1000403142400e5808542d03a025007660b0769110140a4010070340c9004002001140a81507079801c02202e01c540321054150703a207081c82000c0ea540c260740855810081d500d40300031545182d2250080410b940780e00d04980346c0361030a6003910142c01040101c07040d64200e02110400903410308a01d80003401d49580c16034580d4141b4440200031000034203008144000840280500d5030810980f6a400342c0131542e00301340034a00c00c0810140080d440b100850444501124040407400d40d20200b00030780b820004100b261a010348480c02c1c94030075500a40070840920102000501c0c20424140c090317494410810402c07021404090082000c1d9030454141807990171403c4003001c58030442e6484161031001380660f0081c0d80001c0e4988401d40140c0341082400009045203803601d2196900450740680f160000f1095120401d49480b000d680e4240300300e81c4001d9004c00180300005403450f401004000c2c0d0f1800d45160308010095000e0390459801ca042132 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 192125080 1250 192123830 192123857
    0xb0904110609190b0705100b010804150b0307061e02010506030613050f0307301e20061005030304062a02030a0c03030921080c19050a0c0b04081c 64
    0x20381500005002ca0b0103c0c40e145c00030391429608110f044001181024680000c44209a0713000800b66009504000d008144400c071070212805800f4003201940c240c8038241000902607400880b00d420710f01c1c400480e444a1000e10720481c2a500140ca800e6816031080012500840c3c299008000c40744c8200103d4090703d501e13021660035504101800c5d41d401c0c050061102000300a50b41c0800c100121144943d031441e9401c402801110800c500030460030010814005124015002c8100c1c00c45048505541c6100d1905480c1e0390300400c03505036407038141e0480d00003038a0600205490a4882c0d58550008004448004030019031814441c03898200000300f07420056103051001b40d64007402841228009070071410007800350500741e4001401240b040c3c00e9900386455060251503030a92210403255100854840b551422600c0900f81420041030f1021208200c1d00145120301240304101c80c070343c85540d604981000d8011407080c55030030307000100300c11a1b11071a1100164880800e041001d4444580c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 192126330 1250 192125080 192125119
    0x812090703120804061a01020a0f03111b0f06030603060c070614010803030a1406011706030102040306061d07020109030804031b06050115020708010209181b070b010302040b0904110609 81
    0x300141c41001c80c0c10b203c10f000501c050f9004401814018401c04c2c40740a8403540000e5403011007010290130600c864044001701032181585000610350300d4100d490f02503407048070b0541482907a90b034078421944442040d220341003050a491180c1401405004150758001042c2a00d0b8040402294940c0e569010700403080d07040b025103400380c01c01500841d200d180c0008004100c1c4c41d43c0c03400180003050318080011583c0d10004050450101d090904200c0d240c107008a40a402246c0005081c10704048011440040408503100701042e00c5149105a84613658184d00300c6041c200302034001883d0600003404280100414910800c80926200d9202010385618040f00c60a800c02c2c00c2174000c0c0d0080e120101d43c10402c03200a03080f0140214501810400007d00740150003880c1900032042100041134013503600c0414422f05880074800d6a0303a91a841d01200854003404124450380c604007041155003802c40e510742c4116806441d400c1d00c5020320080013219000003400e540c0c800c208071848a1203104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 192127580 1250 192126330 192126353
    0x11202130312080603060f01150908100e210702040506031c021011130632122a091201020d14060105130501030510030204020307090e090304030812090703 68
    0x30b03000715442d40300d480c034018205030000d840c5074800e604c403c0c14081030349600c1c2c5e41c01d41101c0d0b01143c45402a40c1d443d1082e40c000ac5a688106c40c9800341410006418029030081c0c0302050756a420b2391406c10144150900c1c1041c034040642c4c003c034041c8000070041c10981c1c4081d81100d0010b0403034120144010104d0030600c15030543c0300060704a400000c0203800d4500031054641804a0070030b0810480a40c0d02c42c80200d144614010446144c00b05030f520403152010702c071461000078401159044040d810f01d21680f18191601c41510160005001d10401030400000713070303d8410b280410f034603054070600c166070407a14400350300580d03540c01316003081e800344010008548010b002140043c03c085a0642d18413009154506112b02040306200912840c0c0c2c03000b00ba5007003402e0004464607540040d03038200510b41c02c029001440003041c0441b003500501524202c2d10951041012540c0d0041c8141e100c2c011840300904001c02440b02c8548a0b2000310780c40da01404103422185980e03540d4403000302214 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 192128830 1250 192127580 192127583
    0x605040311010c1b0b060f0901230609031b040605180a0c051c1a04020304030e0f04060602030708030a020937050906010f0c06020a03061701060f03020112021303 71
    0x5081a2950070728181c2801920743c15902400c00c0104003940b540810044611501d008000c0140d407400a0919034407001030360103115010303107440415a1500740107103101840c4030024584d40c81c80a43d500311440c00c0c0044070a0074001502074506501c00f4400e00c0c40c2501d01324181c503400740c2c89490104494a0f90340c44246040380302c43c0c12500900300580300f0000c40300c440c1c0004041007010003828400050485201d40340106d504c100250981d8203020702c0014408181034203900c54000801c1c0018507501c50100207003080201d80070a42e080d050802c000c102c84541c4101005a00b061040b100894460760180d80c2c0880c08000c0907103018404800912031020340340040c02c0c2d511020001d402d81c400e4510000c21401d034150022043c403400c19001800e0b90308014192070421203c0c00784001c1d501e200b030040340d140784da01440c01c0d510342900c0710001d005070540303000750141d90080c45210700074100c0500400c4229040c02e81481c281c02d0a540044482c50180f003150341005408115030b01e655884003d1090096 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 192130080 1250 192128830 192128837
    0x909010605041103060603040803071101110a08150102100209011407050d020d1106060904030e04140105030d143a02071a0702060106030c0e03060117010c08090307061806050403 78
    0x2401d041c1000304880c51082e03440444502030082045544803081283c0d009904003030080c2d00e90ba20401e048800f4841801403000550802d1400d0810102000c00340840d13809580f40e040c0f4030b644421200c0e070704072142101c490069110b0740c8800c1074407069500800c00759006251550048144a4814205901c000350131242e41d4040c0e541c444000383d0600c143d4040841503d0b0020701c01011180c3c02d5036801000c0c21f26440390a0741c40102d001c260207200103e21500c005070042c00301216041c40920030101c2442a80c1c0207024084154041c0c40c89a60b40301e0f01c1c074035011601c5007068040c0150b0460107016030340001039940100b4160f000100c540780c1259107920380200140c2e9400d41c0345014400091591a42508003403070380705002c4203603004030b200c505543c481d250005190f80700540072541e03804450b264a406000310303800402c0c11036030304141a2030540c6a134028400c250a02c0d9040300c032014110b81d1000107810a00c03a00002030819040081e2010340888182000013141e155103084078001d80301200131 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 192131330 1250 192130080 192130091
    0x6040e01080105011a0703211d010e030703020a0b060109050a08010204051507050a261803010c050406081902122502070b07060b04151206060f06050d020c0705090901 73
    0x9141c2401410702409842d02c40002c0e07002441c03a070f000341e8080c0b07920081c2484101000110710b0084582e80032610752a0300801c0c0300002c0c000c003521004000060b8142142d5003002182549650008103d51b5004d5040d4000c0041d102107464074038003060003a00450411812038000212903403100003207030161805800040c0e8807890700082000084942201c01081ca500b4405070010441c00b25400441079082505012100d40c1d40318078100e1280301a00502c0b910001052840040240003880c0340c4140050b4020408031580c00310555003401544214000512850000341301030010401072192a104010b0140c106400c20700391085021701100c0d150041514050000442c21080b4071044034040180040d00905042010b81e560600c00d54402802483d10703101100b00f1034556034040f40c075820b000b4140304500d07501c903005102840700c03e51003a80c405003007050100780a00c0072442042210300c0b9450300b903d031800465a50740a50085428940c0900403d400002c1e03540321241c15034868100c200c0005031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 192132580 1250 192131330 192131339
    0x40602010e07030c090b0a15020f210712020102250308060909190f05030301090903080a1b080405030904050c0405100e0a0603020705160906150509092406040e01 71
    0x71150180c07540801a489000c2c10000700782e000010000b035501d60780c3d02056240040703001c11204c0d0785981c004070050314a013010000c000c1d804940c01c0a0302d0281c9042d6200e03412044403a00301404894080c80032100700300104c0f0700144102c10101c0f1015018000503051250700701c01c20a010801200201411400c410b00004040e40400600d6002c80100c400c0c0c0b00030b040c03040250b69180300344040742d07600d030030b2044200080c4100301c7d0004c80703003641c44812030b03aa03580c464441070040c000b807000403808244810080303110300005005040201f103407007040c8810f00c01518011102c8001c06030007609d40c0c0c0010007201e0f1803521a4010544680e0034034601c0c03590b413450b140900818004903109401003104020b1181c2282e40c0781110316003290190f242c05130302c800035801c19509100e00340b07008182031a81054005120149500500212400840c800d412084da200301901c0c3c61080581c400d512108000c006564500c074208110555030b000c04145480170241c1011561503403080e08000d50110001d1700410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 192133830 1250 192132580 192132583
    0x9040c0e0903250b04120504030f0507080105011203020c0d0f05030313050c01030e2d06010602060402040b040603080d15050a0608150d020d150212040f0308011a1e0d050903040602 79
    0x2078503200c5601603c04804000d4a4444800c1c4014200406052240b411a43d02d00d21650580d40035542054925800742803501e0416a5000c00b80300c1d50415508200001074050751100d0340c040b80e650150040c00005800c4070800050b0395040c0d01c226892020303540d440c0d0106004001441c440c41014221005240203030070494a04141c0c844410704060030107604401c1410085180700c0b10880124100ec140d06804a400700c1000401f01c0e100b00d544620000040c00c0d035030029005000310300981d010480583d005003408140c8001e8000a0500c080810140d4000a440d6010340d1040c000d03c0d070002c03c080c0e12800082e0000d980d07540003070000f03210402481003134400352803201c459041c1101c01071054861903011500000405034081d004490f1620303c103d20443d960100c0741c1052082401205528141c581458211100c00003a400139001c240085041000c0c070840c501100160445c1d142041e103042180142d022074040805141942480718400d521124014213000f2120307100a591580d0070058007d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 192135080 1250 192133830 192133867
    0x20040b0c0622080c030702030f07030b09070f0b0a03090203011e05060a030f140f0105010609061d0622051c02030d020c0d030318050604031e030902030c09040c0e0903 73
    0x120001041000b001015040c0202401c944907803100c00d01d602e80f0710940d5614290b001d188800307500350180720b1140c2100c0c1400304d184c0b000c0c1c9110750100315075600c0b05d841103552401280541903040d0300101c0180720300c1c1e60000141c001a50186004502034031140c0c0170a0955044003031215007818079402001c1c25002a0144070303807100040e03840027003c2d440c40c5c80301c034244907802d6005030800f05081c030202144135041c401e030548030007428000c1c071540d603592000900090300c5100c0ca800140c0c004200740680c42140341111111000104620f060101400500c0303607001010703482c040034034044080002c030394503441c140501c1d000b8003000c5c15020307140d907005050402001c41500c1e8115000b401900409a495000810f81c0c10380500c1c00150048108101d04a492101c0c40003030105d1141c44104010143d00c840902101c51040c10f403041c4102d40c0d076a060301500c600181c003e50542101b03048500c9403c055100c04d42c450300401c040944c880da54500a42840020b4900400d40c5e003000507850f01d5200c006544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 192136330 1250 192135080 192135091
    0x421806091f09060309080d110d020327010902090f090f1b10091805061c0516060f020303010b0d0605190e0714031501030e010f0504051507020d0320040b0c06 69
    0x17400002084d03915120544141d6500c49013555440c0383e0801403000c0002501d1314114940d00c01c65032400c00180781c8050799601040c90381c0c94400800140f4191a040c088d100f0306c242d001d021454140c03655010700220303450013820524907118400d260786419208000b101103800840c14140e00c400900710600c221400c0124403001440f0910004011141510540d003840b000e5101e000035840d00c4203c0002c044900c80d0503c20b801d1480b101c0503900340040402c000401104101380001c10550300c4009451900e011341c001009604140010840d0100d081f0090440002006000030b2040d22000014049440310304e0040111241c68401c1c024420310b0b40845800c08510b04090b40440413054254015101c0100011568540c808088407940d0013900281004100e240c0207001039080f0143e5400285030495040da0944640d8181100d04580e03081c0e03007401540158040d040300c0c0c48032030059028050740d001c10007140d1001c814018003014488041c00140c09440f82050361502d200c071030903203044000f600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 192137580 1250 192136330 192136337
    0xc0f05030115060302070204290a0509061302090307031a0106080f0f04080c07210507150c0209100b03040321110a110c421806091f0906 60
    0xa03900c04540008031040103c1d5458500503030380f10305910120b000b420540500b50000b0b290000111808050142030880c075500a94030000810340d035004100d070718101640d01503000603050713000010410261700181100080a01210101642e95a031504a035907003484104042e07a030440180308480d8001261398000f11000c1c0401103030f0819080131913180d60050700c01400950009020240b07000c00344041c01c0240342c41c0034082002c40c406c1030380100c20b00781080111510b0003850004900310b400c074083ea54030900e140d038a0341440c010a50070300c100f2640c050101040c1e0740c00520002415180f00008610903880307680c44802c0c4510305e14000d80030581c048548217005090200040c0c5105407903054510110540c80c00e400000c010a001ca41800020810160030160300714002401c80408104a100400c0c41c45405000d1440c0d524000048203c05000007000d01c01080404c0791a0b48940b101100d1760130003420249403888810014000341c0a0348180144010406035550801d41c001e18414000c056504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 192138830 1250 192137580 192137591
    0x403080f0f01060e1002010e060108060a0e28080f0a050a0e10080a020a1b0c14032a0f1e011407022101090f0b060a09140411040f0204030c0f050301 65
    0x4006424500c913500ba15002d500406010013078240f00350401c2583c00010300036240a540c60301245a25000d084504030f0002e0309100c3c964903940c00016844031a214110052a0b0380c003800318625641284103c01034a2021080c807020b8070101c5d00d80c0c020011503034161501c0f03540e10350031040502804020340540d132198460761550307e44581c2060000358041510702c030050b5101c520740d00503600095150780703680440060941100030002e945502c0015900305004400c001c00c003000401d81e40340010b04540b4400d1000f56a0558941d100c101583c914200c004c2a9203442c4006c0b0f00401d000741d066000d00d001e82c81e0000c83c0719415580095080d4200d444102c500381c60004250080b619072502d0141e040d501c008000c604441d103120a501c00424681d00c00c110401d00e003c2c41c1007280c0e0b40b0380c09460442c441c240d60a800140755159215040d806075540c07015102c595141d17103035040740c3c948150006401c541c0720442040303d12030743d01c0100003651150009098960a0250461059040d50019800381e80340c42c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 192140080 1250 192138830 192138839
    0x61404030b190609090c03020a080c10031a061c0e0c01320f030708070c1104050615130602011b080f0c16030f1101090c050d06140403080f0f01 63
    0x1c03085140d00030400380049907050b5101c02ca50700200303c00e070b0082d04614605a100b8041040300c0c00f011003228004c54604a17a25221550940c440c0700c0d2140280e407154441a95100c1d9030b000e600070500014101003280c132401d0115002c03444943c070405086008000e480c0e10100e22084500c02c1a045090303034001000d035102004000b9250203040c40d410050103404025621480c103640d45144010342c903c0500c59200d90300d8484101407900203036000004101d101d400518080d1090342314201c02604040c00c05403c0d455507050100a00002d4181e03500001c130100031a050b9038050005000460003d01c980d0041c0e03150140003400c464034407010040001c203003000501c00540c00104517810200500241c105602e03440c000c80303c0c034440c0c0a01e00c0c1d6009070303441c900d006140d00440c5101e1024199100c441c1015214410300c3e0807169040e800514410040b0750520903410810490b0852034441e100019010192046034003029508440031000140703920b04204069034004006500000941030120316035060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 192141330 1250 192140080 192140093
    0x50903161d0c1312050f01360f030215010e0402030703030309051903091406030c19050d0c0e09090307030804030503060d0614090c1206061005091309020a0501022d0c091006140403 79
    0x2401050280341081c1003070039821100c08082000040d8001c50b502e003c229689400f0b034035800d400300e03a80c200585d21330000481c1c4000b01c800f148186c0c0d009000d0b2140c40d0071942c0942c0200740e9070000340c50034416040e05194242210103000345150103521440107043c9000c510600c40071903a46614001c6400740b00f0700111f958010151040458110100c040d0040034500031100b60203100b0980c12140d050072440c002c4c0c030750886c1c40b642d0304500c1038414801c0c60703643c881c490f50350340f003103050050014000e5070024000c20b02c90700c0910740003600181000681e035030301e4030b510b400d480206143e004c409031b494080c48180b9a04211403204804151500e0410001c40e0300b0b065203e0038000c0c40140071700e03440d0040301390342c61046045444e0701e8401450303000e80d41a150364000050004000407130180001d104041544c3d0f00010758040c1c2c185000c142c01070307580848617503100455104641e5081904c505a020403017941d80c2860548555078428901c1d500514000d801401c1c020410f07901c4481c0b0343c04010a1001c982c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 192142580 1250 192141330 192141371
    0x9070e0306090c0607110609030304030602030103051203090a0f02031e030d0605030607120b0f0411070b010e0c180d050304060503070e0105071502030403120c050903161d0c1312050f01 81
    0x3c10008101b010400600410300034481c2403001a41400001408420494240c0c0510b050768090000c403460075001e03405c3d0740c445200603901e00107507a0047c52103400190030140280d4000e0707c007405941c0c0e0b600380581d40c40708140750701510310081d41001c80c8207150706a541c130412008050481c010025030a01c0c0c0d5000d44001c003110748099006486403403040e0551118000d10091040c054800c00041c07070340a00c403001641240a003250800320791000001d12500f4404083e006804900e041e0f4942001000c1c2c400780807080034001c2da0000508003068001c40c40c00d1010f00002c20175919180ea032807405000050042c420380100380c0c18440c0070311072100498200181161000042c02c80180c2c1e0b611603040c2641c0e10600304c0030030032070541890202d02120b03a01c08060444000c003030301200d02004050101d0380240c03209000d070084441c440b8100310b410340d00300c40b0425044080740c0c4000b445e0034101003001c111283d4542204c00d006103118023920800004001800d00010750304001c001e0010600e003010907244 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 192143830 1250 192142580 192142583
    0x20c030702011227050c0a0609031506030b0c0a03060b2805030c04171606032c0c0103180b04050d0e06071713050904110f0306011503050c070209070e0306090c0607 72
    0x50003058514208102046011004c95000b1f02d031000d083c2d030f620b800404400140c04120341d04c1801c8007005000c00e031f6a008101c10b403070780b08010b0511a41c426034550282d40000104004168603240c0010701d120a11000703041400c0f816000b502080d0750038488140f99142d00c6014800c0000400c08c20075006200c000342d40590384e40310074112030a2030034041989044464a501c07180030301841b10010344507416501c00c9640c40121a11305846521046d00c02c0110b40c0201200070b075507000000c0b42d00d40c07980309034030447d41700d10b13068954a503086080e184c04400100403101101c0302d5101421001d003982d08000d103001d5100f000c440180c60304182e5591000003207200305180702c040030081505004031101004a501400016111203000e00e080d05200110440c0d448101d07004501d011070502040c00c0100711103050f81e020407c0154508078943e0128001c107002001e46801e10310510155005a40d014201d83c01120f6544c0c94140b0710740740904040c10000c3c0604101c007a83d0004421400c103880f000103079158103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 192145080 1250 192143830 192143891
    0x10b031306140906010905070e0a03170417030408100c020c0d080c0f0714010f020615210c040c0206011409060307030501020f0307170105060d0915020c0307020112 72
    0xe400524004014191403a841d000a002d401c0c01c10030303840c00000e449812a9011901030115850b0040c041c0c035610585142c680c0c00005030042070010a41c103413119160b007107000710824503081d0768000007020400a94120b0b92560030005003003241e01c104026441c400d8191082c100020350840ca000303966503c0103101c0a02a402c414129014040031101351000364901e0000d031074203815a40100c0e6154034060103a00003032505001100000d5102c0c1c03240310f40141c0107400038010b5031203d4031071424001e0141c20b082d500840003e500000031a2304ca00c1708204040080080c48144056000c1105880e0040c248404550007240100010383c03052496102c2080140c8604a0176101e51000c603007003842e00c0d08003038101c0d0b000181c5102020361100046108400c2503454101c400441c60b1036520100f402c1c85101e40c040d00600c104415144680d0009000f548642e080d158040702091024041c0e800c031204450454101080074415035030000000d40d03030721400e0001000a40069070980c84c0c09403002240a400c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 192146330 1250 192145080 192145111
    0x21501090b01030b09090a0201142a010605060d09060c140a030f0e06041101020f030705060f0903160501020306010e0d120503060109082e0e07060f230306030c0306010b03 75
    0x1c907406640310340c05459000d0244603c3d850300000b61030b070f01d542600040340081c0f0a040b95000e075a4500b405e0712603040d03210701e940c002030b005034410f058205040701842c09555a41d0b2000a515540c0000800a150305401c020803211940c1c00c0070002c6520407414002070080d12495649403030403940c11100c0d007100d24200041e20310444184c400042203800f1203202c03d40300c0d1400340024007010090745c0040c440e0907400c846810242000781d031780724001c1080042c081da1083d0003203150b041d0440c0c45564001480001caa0405881200110000140303941c02d6420b65800028030034156800b480700e070401c8000381c0c1c0c40344190505580e1121010407010400d0100032000c4042110760f072286058000429100341180c242406080c040c5040980c0d105002030204561024410b900c1c82a01a1107418030004015250507403a124040d101035840012900811480e40c221040d5000d40310682d07821120124903803502d0707203869800d00d440c20381c001711085c0c882e50061004006107608241260b07030028007451010301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 192147580 1250 192146330 192146351
    0x2030c1f0207020901080f0708300721121a0603070903140c01030b040c0c02150f0d09050106050d080a0e0402040e0a1a090907050103110d09120f02150109 68
    0x80c0a80c100081d0f00001300760000402a40000d528a582005507050b40e11030b83d620042c05681d0460300c4000e0500f41c1c0d030403005100b04400c428156807200b8043d589103181100d07669920101d110300c1142d20851454072410314034150342c820b101c134158004091303003000001d4480810b04285100246c040b4440d4100100140100b0311464641c0001e5612450000f0310360140400c0703949480c3c20000139800607151602d1010289000d004072041540c8903250000d040030389409014048074105145880f480042000101003071185005111100748440c00240314225443e0075425144180d000d58030580b81808000040f03006035040300c680c1601410101e0200035140302003006409550300c100c00b600c00d0035007042001402900910410225800b4202e010740c40041040b0b030418081c6c0b48a246940326903014010f0f5400f81e4004a00002e500702801c0c28500e0508c3c900782a40c140d22003c07100030944403619002160404c541c0c1641041900150030503100303c600b84680c1560501c6030381186500c03948240c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 192148830 1250 192147580 192147643
    0x50a0c061d07170d03020306060409020313210206130b010512010608070b03220c1a0c07030f0b07031a1c0b070323010506030f090f030301090504060b0102030c 70
    0x1107200d8032020a8840c015514100020800a441c014808078002c020070201140c2c806e03c2204d1150710001c24041c00c260400c1f000300c000b904014007400510b1a11616100420b0300c0c807611054101d005030f90030a00c0042d0640080c10b003400a410040c012180141c11400a00c0c40a8014152001540c6640301c1c104000b178031074050400b60740101420300400002040362101c42000b18810714807911069241039003600d11101c4204503040103401c0c0d581d00b081c03d00c04c50307841041c4001c2040116210a0503e038603120300c142010b4140d403003200e540301d40d500f00d042000586450250310020609003005a0b103524000031090003200c5800310302c0340442940500c0c8000e94004e0700c60a02e40c0100000c40d4500c1d04040c041c00500307104482c14140e20080b440c0304d612400060141c0c0c1a1103000d0b06843c2503894245214042201c064403e07685400751030b41a201c54842000618024420202d001c01d141c02d05060010440f84942e154038110340080144484403680001c500030914480080810b01d41422102c89 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 192150080 1250 192148830 192148871
    0x30307030c02100e0705010e1c150608190201030c0c050c09060423010501120e0c0603061f050304031b0506070f02030f0c0109021c0201140d0f0c03020a0f050a0c06 72
    0xa203401c41c03034503c2443c6130800014a882c1551003c0c0c9415440c0b8100c1d000300403c0c2050a0b080350a06402140b641c000109810603e03000013405060100c0c0054841d50070505004841d0340c0345001c030124400e020199a454003a04980035000d0411001d02081d031b440c0c1d6601d450040c100103018540d0040440c00e6611254031210300c54040c0a80e00000c0c504003000c8030518a000e2181c1030005e907400200d20391048041c1b01c0c80480f0f8990f10000c103420903680040c42640e41004000035070004038100c518441c200402520030b05580e590303a03459584e142901c0d01510010340102c107500702c50149400040040d03400a6160740100250072b000e020320424007030480ca0b600c907100700c07020400e0f004650b12103903603015001940381d64401c031403810307000100c0f800104010450200290000f0b002150101c007942a980044c00c1650034860b022501100031541641a518039801a0000a5000461000e0643d100c44000034498281c50014580b5030141c41c02080c1138a1100003a0115644200f184c2c0c410f417800810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 192151330 1250 192150080 192150103
    0x210020307030902090703050919210207030309080d080c0c0c15040302040e01020a0c02190308040f050909010c080c1809010902070314030123180405071d0603030307030c02 76
    0x5640c0da240c400801006803041d100102d000313074416000310f0306490003400f87c14850640d80c1d00410311010b01e600018113072015107500307403840c000f802146410034501c100195001840754008000191461400400c202101e80c02505150800780384250190350244500e03820450000036161074440303c41546041c040c01d56400c0d503002c01c0c203030381003e5008c4443e001713441200d000301c3d0104989001400998240d109041d03404c0005802144144014030f040c299811316440c08203486203250b074403a0b03100c151a60140e0400d00c261310200400f01316070b261078607030f240d8424038910003400710f80040c01d4060520240034000c51010040454080c03050f401e8542240415000100303066041e507503c0e81da0030000c0d404402c1c107400190100c41120303071b0000120100d0b4101e41d00507407200080f4010b8000c03050001c40a11149522290703100c0701003410b0162074050703401240650003800c9094980070300860300c4d03c6d0091110345d40258000402450b982e0110980307a0203c164200400c2c200b080180490410160041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 192152580 1250 192151330 192151363
    0x6160e06030c090310050a2301150c06061202120a110f040906061409061804020402031b07060b10021504021002010912031a063c04030503031f0308031602 68
    0x103010782800d850300003600540c9804803c0001c000800180a200e0312960f01c8c0c600e0840b01440100100380900c00740321590100f6240c0401e00c060a652846c00365182e03039225a0101e005481c1001c15441d05041c01202e102c102402031144901c01d580310341030031284003500343c03098048070192800c0351100d8006241301580008100266511682182036603040d8101d080c0c041c10f20100061503906020425090100c0c0d01d01c821301d403541d926820000a50720040c1105000030b810500d49100f00000000b034a0014407400011607640d0008080c0a04115105484000c550025026101040e200f04006400c1074050301c960444075000002640500321900c0300910400080c11080c40300d640c5a4040c142c0141c01446144007074a0600c200003050207103001c06050408c0c42d9504520034121414440d440b440c41c0e2013212400b4032051026071041c0c00a601c140e81c035410010800c03903ca0008040c0e030854500704055244c415096444015090000501c03580c1d40240520020400c87d0080141d400c04000400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 192153830 1250 192152580 192152593
    0x5030c01020c03180a03080f07030905040e0f121306050c0a02030336010f0302030402012106060801090203070903030c060f05010311011e080a0b010507020a0e060306160e06030c0903 80
    0x50245a0ba54029060b841413656100c0d044010f034030f4070314661800c51760482c035010f080404043c03801c034040c1d100c4402142400303040d11001446440d980294036000740b148000c0c01c003911220704101e04118801034221a24003081181c0410060740000c003109941c1a441c1258640021115842c80c02d0308400c8046d525110205001c1d000520903450170001c201c80412850701c00220280010005002c0b4840502042407000440281d910075401380d5406401490200c049009208400420400c41c81d0603c0c042c1d0b88a440030b12030250005030749801012240e00c00c6240d85080c4900406071101404028104840040007130305220301900080e015441c049000c00481d6524902075811a500315400da0118540303401c207000d4406100c140420083e1a62182d80701540c524400b80018140f00369124103009060040402580b680d02c1d848019108201c0c0e0403243d0700701407040500d0904000c1240752243c0d1440b40b201c010560002e000d0240100660381d03980c0b00c0c3c540d000010454011071440c9a09032007086c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 192155080 1250 192153830 192153847
    0x108120a03020f030f16030203010f030b040501090212011b140d241202040c08190c0203040803070c030309080f150a020c030d05040c17030403110d0b07020d0e010507030206060d05030c0102 83
    0x20185c3c03a01a80d02d003054071410140046040c1c0c141d01027441502c000035031030300c0b040002c524010502c0d5446445070000040301c1c0003e500180e444502d0b0101c1400984d5a001a6103e4008c07804105401341447e080c4080418400d04042c0518865802c03007503c41d030b442d03081000000300e914103c0309110000702c25200040303440344180b5040c1d0340c50b80e005a10071800c200051a80c6401101108d00455461075040b11071800009990082c103403100c544001c44c4010000001c41c1c210902c00340282d98422000802a68076504004020b146d254001e40f40c2504010064100c4100001c1c0c45034603885156100c070800d030740700500300740207010f40b0407114400c3c0400219051428819402144910312074189601c031107444c0c1c182d070420505650424119644104801d2000c10600300c00790302010f000030040c0e0001441713541c036019200401e0b9081c00260740320039200803205802001400c100c0e403007072038860705054090f10002d50b10800940500e00030300900c0c580c102446400d0046600c1c15180c03500035503550100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 192156330 1250 192155080 192155101
    0xe03071509140d170c0f090114040b0703030b030601090c0203031503070512010e1501050a0311150c150105010f0503011e081606020f0a0c0e07091505040e0a050108120a03020f03 78
    0x2032410b039441d810b56610010340c500d05c5620544110f444144461410050139400548610300201441c800c8010203120001d41c0f80c5400000300102880b903540880e01100380424146012010f802110280742481c245e0070350707a81d0000540f40d00801c12005408100c0100c404681082c0307464101c160021203107103440864402c150400160042d2220461b4100e49488003000400c100a00840350b100351042c1003040403ca40080130644044020f00b0400841d0300700c0664078a070f40c002105010582c01038900d80c00100c43c1d851216004200070b0800d006000c10102009015110502076060003500b0200212403510303040e0340c00300190000e4000c5801d1140c03284000e020100180c0700f9140103200320004c07050007943c0412000d94440c2d000850241150501d02d10040c0b00c03200070030440070041303010000100c400c90400040b1f0200b031540c0f01e06540304e0800013580d41003000144610b52310342c01c140040080e1100051b12403614118442c126440d03000044040740a07100c1c01e054040030300804400d00040114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 192157580 1250 192156330 192156347
    0x220203100515010c02100c0309050402130302030609120f030c0c01111b120d0b031612020f040203090c0f0d05030301090e060106080903180111060f0402040e03071509140d 75
    0x142d184410024a0390001128424500390300250000d164950908034140100040611503100341490b885d907944030700108003242c1080080588075000001d08005509050007141e4200003040003074000d42880c0e40072014903114547c4403030300481d000800100d1903100501541c403099204d800900607800030211685180e001001d00b4415003240f50800320801e0400949540074164011360182024409180000200000c412468150240100413003001c04004880005060f491188040c01101e500500c1039103085040740901aa104106000004800054280d01e5139000c4542c0041c80c0080b0002c64100d40c2d031210000c0252002000100b101440e9810111100b00c48008688061382d072104119113407002503a04181d150070801070724111a07c400351011000206052811800701c240c1109481c0582c01c03241c1180220b040d10521046140a00612441480f814011405c00b505603c81130400c880b8883c0000702d01f65610080010440c00e061096981070328101626003840b007400c4060701c45c0c4c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 192158830 1250 192157580 192157591
    0x4050414160e010c021e03060a060810020901020a1101140d141b030f0c0712020318010203041d10030501020c0a050d080f070c03090f140103150b032202031005 70
    0x71038044031035840621550b070424591405035a22403040c2c01d10380a01909503c4101040c58040b201c04080300f10341c034100f061500a0750580c6000840720f00d00801181070000c45c3c004640b109004000c0065180c1e400a42c1d00300003a00428a4a180824000181c2e48080c428403110048900824142c400010701d034012540b440e140e2501fa003d590303900440740c182201800348003603154424008592061811040340c2d9201421021031480e0a0403a00c81c0079102c82c425825000581c00003540c0b444904031002c145016080a000440c207003401d0000c440d0780724030400c8001c03006421440005013042c0071307403800800442d00305000710340d12602e803051503455014010090301d2510554400c7c4110910645c00e05105800210043d115521440c1c402c56011181050542c20031161150120700d0058070310050004085401c62890749010344000903045c1ca0030301c00d12083c0c07062048020040b0b406008101c82d03100c0340002605400c214101101030400d201035401941502c9400c0d030501c1581c105074002400384 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 192160080 1250 192158830 192158851
    0x5090703020a0206010e01030201090b070809040513110316090c0e060a03090c0e04050a0308090f06090d12020408060a02030c120a050411030a02131806090812010815070507030504050414 82
    0x586e01c0d12414080300d4003e100082c0041d50b810402c00c43c82d80e104000d0301d03029104152071403608080800260607a0000d0380c400600400382c000c20b4080050030400300d080941c05501070710820044d56003580c0110021721a081501c1c0e10b490100c3d0a451260525200071800208a01d8030f68207407000040c01402a4030301100c04c0140e010012500e41c03002003100b4490307030340071004056020b00c1d582c086418440107055124180300b0214819100341c0203100d1103205035415001421803600206004021000402580d80780510403c000d21400d6000314a00b948611070040151392034a5440031402140300314203100c113100c000c3c0018880c5104540e0403460065001e5101c46c115074000000f09601c0c1c00c840030707000758040d4070100b901181083c40e800028480140008a151000d41503d585040d1505c0d00402c6620b070400140b407061005801e03041c1c0c0c2c05082d082e801480292842510f00700340110152544017030000108510382054411422280501006041408450082c2e0341050b2920000d55006901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 192161330 1250 192160080 192160093
    0x60204030b01080307210e091603060518041217090708060a1109040906060b0c01060e0a0e061305031308060601031d070513060306060e04050609060c0901050c010605090703020a02 79
    0x1143c10002c1640c1c185500007410b5042c120742030254001040c0b8000a1400340001c0404800c0d03550f0f1000b04039480717a8200c48039480c0341800b00c800182164041c0d0040351180d8858242d9120030021072079515405640003011401c011884e0308191000c0700c0031b00e40248500f289200b00960244003065046c210354294040f20880c1d101c5c08900e005035a04d002110155107024032180e8114505a00b000f0355143c02040e0003d0180e07201c005034a10b9a00078920081c42ea1f440c2c2c3c004021003c2203107080c1d9800565036508000040e01000003030b495000261480c0c0401d00c01074151014080140101d805501c20442e000e4012955010f607652100c40464280e40801c2c0f42c40c1c01321000c1010b1280240d031071803400c005410003d040004100c403103040441c1608074240d44600103c0002c3d00c2c0e1040c8806000308102d000c04030301c0c02346040f0f0300d4410020401c001c01d80200342884032071003445081c0d850052003404c00039225203001c808203006052650100d82d2101810050082094159004000000156003507502 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 192162580 1250 192161330 192161339
    0x9030b060a030f0305031305030c01090515010f0b0a050d0f06080f0607090510120911090a0603020102070302060306040e0703030905040c050f0306040207030c17040f060c031d030c0a03060204030b01 87
    0x340026101c0600110f1001001c81e0000e03105100850b40300c1106148000d8110444c2c40d0300340355030001c20040a003030395190f1041c024450304000c01c0c000320113031000109141d0b040c00c1d92489042024850751508500100e00300c00c0481c0280709448645c034212408200e01e80000129001910b03252141407a070b8019142e4210b504000825001d01c10181c035100c01190a10341824411010f22116030031081201d40700d1924a4050540140b5100c5802031800011018101d0100003684502a100314161813820707a0400050360041514801c50307404848a03030301c9a4030400803401401c150010000940120b40e4080101500608a80203640080c0c404100b00207110360152210700c40e9048510f01407105000203611442e00350020b1280c1e130302c01d24100411184503980c2d00c502c0485001c01240340300002c6014820144554030802c000c102d079280c0070f1041c01d51510081c0048182103030799002c500c9500841c20706520104196900f01c0700241c100c4074461b41d2410a64000e400c00c0c0011185080c40c8000040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 192163830 1250 192162580 192162589
    0x703090b160b06150d14090a0b04020105071a041a090118080904110f030403020c0108160311090d05060609060a061b0606050a0321140d020c030c06040309030b06 71
    0xc2454944265041d411100ca40b42c55035080002080355a000d002401001610302081003c2c2801c800c03040c0b00815140c200003603142017580020000310055024071b4901001c00d04a11a0b650055020b00b0880d0759400b040c10440c54840c020300403405481240c0c2c0500c0208a402003090400f190b0311562403000351948407096099800500d1a075130b0040d1168108408502c3c4e0000422400c0002880020030044c282c1440246d0340200d44001500c2c1004820081419014407030895402000d103094a030501d0400b03189070b00a00714601c10b00802d907503441e031003811040350380842c3e180f40c90041003000360184034600b040c2c1c4c840c000c5441d10701400e0000013081c0c00b0304202480720183c07009615043c0d080031816264804405448130180c1c1e40c113440d4440020aa01c5405c4090003850050a04056140c10b008001200d14a244005020001121552101120084140d071040c140501002d40d64401540c521441c41c000c03100c1c080c006005000c00d0000305600101e0b0b100c201ca100d203a041209640d001d0400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 192165080 1250 192163830 192163837
    0x30c010b09011203030209060909042103020304030815040608121b0106050607030f05070b0f040b1b030c0c0a02041a1002070b030f04031809150b0c0c0105030903070602030a020703090b 81
    0x2026640f8081c0c0400028081c0d009010100005403029003010405800585464410f5409072100d002102e1201e0100306440400c1c0c40c07031141400c0551a6040ca564014581640144400100e1004007150411655103811900c014041041141c885406161310200c440d440504080741303150141c1c0d0794010110b818040c0101315140202254101002c60710150b6a0440c4200090200a0100f0031500054a00c41c0250301440c81c1070b5280742180b8041c17800d02035494001d440c4020fa03082810410307514959041c06c40740d009600440303031611214002580ea107000e03511140250f015040c42c000ca084820304007507001c40e080080302c0d0884442101c1100b6a26421140100040d4a00070000a160100001c54007034219210785041d01d9000e04803010300360200042d4000c0c06c0c40e03d03101e80031a2000003412142e90003401c1c58690543c940b03541c1c04825a6031b54900342c5258144500480020602101032041e20100f94010400391b541e8601820307050000e50242804a0100d0410706010034020341342d5064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 192166330 1250 192165080 192165089
    0x52b060801022d070201030b0a030b0108030403110f090103020f01140f0315060703050f0f0c0d08160207261204030305122809060e0d0903050d05070503040603020f09040905030c010b0901 82
    0x40e03d240113003540044000c0c0c04100785603500854501e00000000700c0b040c0c00280204005000703151540d007140380150340740b160b0300f051500c034a15030b5015001640d0b4441c095030440f5070403035001c0444000880180c0e0201c01c0d11a032010070301030100781c3d458400d914800440c865840f60701814000b076112801c1014600403410080c000603001d0150711185180e11004241c045040c6000c1400c1c0b044000000d850070151000a0000417036010034080e00c040d10400c112400001382c00a440d880d07042040011400d11100c41100c0c151119040c94448294180002c04c09860480c5506030f54589030704024150358000e81d00148051922000110004850000500d510004640c8030501080d96040301c3c002d4441d0804c140c8501c1c2ea54100700d074100c0030800100c5200c00c21a250070206074a5800d003281882690b140300001c1c800c0030808000010004403c80e820396040d0f050060b15402c034181a08034a000304552140c000c3c0c640450281801800000f600b019061000240701c02801901400342c2c0c10400e116 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 192167580 1250 192166330 192166417
    0x160f08070302030c0708030103080a08011a1204060608070605040e01061d01120f061214061b0a090f03060e06100b04061d0406030c051002010c052b06080102 69
    0x49400d240c881d800440c0c208070700b0443c45050152a4907407016680c02a4022145800c000501c203a4454100e6011401013400e0741075400e090000e031404103503900c6410980c454120078000041c0030001c02c6c2c0e2001028102801c12106e4480d1100c1020782680c0c414012001e861454400000d103a41c401ea110001209520041310b440c0c015407001502e81020201c000210305031248000d001c00e4000e4414800102410804894148424100700c001a0201c1e940c0d2400742e0481d03003c001c41c0118034005004c0110b64900100d54072070074864225100c9805800880171901c0041000003849000e40101c0043c0c1040c2c41a13030300c0c0e0b843d000d08403940c0b1010340c4104810100248001c2221500400044454200350009128100c3d81c840008040313481c150021584c0340602c01c0140011700700721608000d4900c850000300080b030080b40c8003030207034006d03440d0b20100d00201c02440404048960b002200f031a1241100b40811621140f040307020390020040001007001a99488400c10402c1030700328031400d000c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 192168830 1250 192167580 192167597
    0x120506100c0f1b05011706030d0c05070305010e0606010906020d02060a0f020409050112050c01140d15030f0b04020306060a030b0f18070803040602060601030b031504060e03070506160f 81
    0x103040d9a80d9548000c1034400c0c081528400d00071441c58042d022400700d45140e5070788210304110014081d1003000d0494104518904101300043c3c41c0040c404820b5445070405d80081001441c05906d400400d42008045508180f0420307140301e00003c1c82070050100b41c1b00c1034801074490708201e030784810300e20310100142d100d500804c85520069011448450180f9005498540c5651910040d1130080e4803000743d000ca21a0140300303010007071103004007640017403031720740303014591240c06174484d024032541e011190f5980c3d201c680e140c2040b80030000c010b540c070001400c0041e405003410700c1142c1084600341e02a006050004846180c844040b4007540e510004d500c1040c1c03100f0100a0001c50000c10409a0080c100f5080c3c80d0910104100401840050000c2d5a02d604151000382031240141156041c5400d101f403802c156178003c07a511000c1d001401ca181a20755503414a8009012641180c5105000000d000e00501c407000c108a8400c0e04103001400d003600031158100c4254008001c1180060a072a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 192170080 1250 192168830 192168859
    0x614090c090402040605150c100b0a1502012009180903070816050312010801060f120b062809050f07090303110c030111030916080c150c060412120506 66
    0x181c032007a402500240c00000e610781c540700402c42018101a42c80d0300380102280303a025900041090794014074103550140311100d8102d012a54072811401503030a00c01c01c1c4200418414803d501c0b500100c1c507486010081c006101003404480c3d8040945c00e07004a0061000040244103107120a0148071464000c5141c0305054a60019a4000f81c5500a00c1c480c03c1c48a100424800c0020300441d41c0340f140200e80035494400120f003100d18a40c0f091401e01504802003082041010b5001140c0b07070000880009940c03034000040600f8000051006c1125000b9480d004a001d40f200c004150f49494104124940b1214510301c4041400c440702e40000d01c0402e014800244145c401c101074018820850306607401d0741000900f554043ca034903071080da401008102d80080d081020400080661a004641d00c3c1422642e54449120101c0d40c3e014004c801c0104507101400e808030b4011085403001e0714024201440c1c03409034913140a080200164207001c0c540c0c0b900e9002d00c00d20303024400c0182480c2000c07150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 192171330 1250 192170080 192170089
    0x30207060f06051014040803032d06060318010f0507030b030c04091e0203030d020c1b10020a0b09100e0c030114010e071209060c02010c11031c02070f0f0602070614090c 74
    0xd801c2ca080301740c0010300001074008000c2003c0e600841e15498160010410b0400c8411a07a0211141441c201c980d8024002c15464030401c032908501c0407070b030a080c0d141c0d440241034090281484903c0ca11440d0900704082c243d03069010018500c5c048050326490025601000142d41030100090184160064200100b0700c013001c080745038610180989043c42400f80e800400c076040100500f1464004207060302d42c3c600a03549500f4203041c1100c07040d14400c1e114100950750300260308010448040d90300410340f050f00c01c0200c40c0d00b41034039010070b22195912a00c115150342024500c180a9800c01800586000b6210003680c1a510040184502c903542c000041f60310303403400d00181e1031140e45c981c2c0c1d01d4081900d074058200308540b56000820703c02d801d500000c200000250f01226117420500001142c01e500200ca441c500903400805a1640c02c80d00b80049920a10346000300400e888110400c03c11050303401800701607010703417010801c800d00504600c002d14012100b00c2841c2d00081001012880d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 192172580 1250 192171330 192171347
    0x10b070204110403060207060b040218040c03270b15130c03060302131406011407060b0307050301021b010c0c080d0515030d050d0b03030c070605030702011506030207060f060510 78
    0x81021951400111010b0440c1d80140c01c00d0b0b600e03580000f00c04052200d41e005484d030080d0181c80452801003803c01d1035080c02001001e00d4415910360644070401e6100342c0056171550b0780d1201c41042d180ca0000343c0101d00307948410407034400302ca060024401601c010201038070f541010b00111105001c14880300001d184900d01c100038075030740c2c80003c809a195100b07940c0d0300942281c40068104180c002c0c0142e42300d8000c0c0b07064100300030400002c1d6060801d4080da140309a0002021501d8412280001d09154964005a4141d0b00c003080700c074003440b200306104400c4218a8000c05c0851a0315604480c010020a40902070820800c484c0c0c8014100e40c1c442640b0419003c10a280c640e40400000e0a00350200e060b000003400100380014907c40502c21040d00040440045182c040c1000d40f09072100b00e90311800f000d005012000944490003900840c3c1c01a00700908020015102c400180094010f14401d44003940b0f80a080c8034bd201c00c1c2c0c45140b0598000504040032203405620417a003408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 192173830 1250 192172580 192172583
    0x10f0f170f061e090601030804090b0d060912080903043c090507020d030605030706030506030f030d060e0109150504020c010f0e0304090e060c040b0a0e09040302060702070605040e010b07 82
    0x30481c0100c41180d07000740042805541119100605050311025558501d0000b41812a16802000040001031800400c541c00c40340c2400e0041501d403001e8001a540344a41c55000e88880e003842044c034108031149820201c410180d841c4c1d80c00503101d14400704d0b601d01441c02800c0c0f2050071b4280d0303c00300301c00d2501c0e0100c1c075449818140b40c0d14030011400d841200120f0b0f00081c07100361504180283c20f601407040c060000351500d000c2040341e2404000035920529485401e06260745d6901164080d2014031041040b142c030401181d50301e02c00c00511900611451042c00e01d03010b805800401c02112500545c9080c4051165019042d804d0008210095000a0204072190350369800320503004500e000301150041102c0196458a207000084025217041d80104451307a040107003001006810b440940d415621301c0c50102d621a81c5c488003e6903008840111158000303103050403c4105540080c0c450b20a21503603091b642c070700760342d654241e409001d20b010780a0504c0c0088014400802c001d409048490f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 192175080 1250 192173830 192173833
    0x218040c26060a031e03030501090e1203090a0f0f021309030e0f0a08150a05090307030516080d060909110906030a02010516120203070302070b040f03020909070b0c1005010f0f17 78
    0x140d0b25580c90322006a00040800720102d0200c1c110145038052140b2340c0100341a0006000c100d01e598441d03a100da1148604105184012011480c204420040c143c1c50306c1d881100c4616000280c1072244050300000b000300d125015180f01c0304005662030140070102503061f10f5100c0c8007580e00c020030114280c409400d07504140e000000061081c01044031032400310400c0441e1100342400080c80e0156900242904025803042000000180c1d0010440d41c02c58000000342034482140d10f80038170319108049071040c0740c1c1e0030034002141da100c059104555a502c610502080f0008038424030032481c004070b074415455085030301c1060140d405100208110b0f0802c01c14164004802c1c1e40c0e0800b0780b02101c0c03002e00140d0011030005c081640410005016000c1a0442402d19140004c559150703207041c04001c0c003a191401c0070a0610404008050280c1040f10f00302d51030301d01c590307407481e640c69407a20f41c03010460401000046109145415206403001441000d4506003803101002080486403c1c02d0f545 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 192176330 1250 192175080 192175099
    0x2403090c1701090b1f0506070c0315020708070308150f100c110d03020c01020f01020301080309121006032405060f280608010e010902090901030311100218040c2606 72
    0x1e981a401d542c0703d800e210780321400e0300c00c0e202e00d032910b40303070780d50301b01c80c0c01070900300000d00c0030400031102c50040329404024002c482142d400e41e9000303402001c1e801040b144010454104154004c101f0078464003c021001e010144554100071220036900500c540091140707841141c0701e84664410110345018800d000c000c0403485002c40c50b03200c10840c042d070042c0c20000b000455983e05001c4900103d51600c000c0d030655052000032501da1284050040c0b0034074040e81c001c520844c0a000c10f4062030b5803540100000f6070b0702d04200704c01c0e0603408150f80c480383da0051080c90038581e5204d5503014010103010310f0810080c10701408800165598000021441320002500f20340449401002801003aa107009440d4500030b400d50703480340706030420b484c080d0040c40090081d41300d40d000e490441e601441c04071142000c1c4501541050540200190710b0780c00019884440401070f000e803c84040c05403010850359103020421960503102d80f00c40420040106600580c0e02c070324030301954010300010507200750f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 192177580 1250 192176330 192176333
    0x120934051207050f18060409020f130501061806020a17070b040c060212190e01050d1404050706020606060301090f0204090207060f050a05070c0f0507050a2403090c170109 75
    0x1c41550000c0c41010780c4410014001d9090105240411440994003000c00c0d200c010010951150014880c600969540030500e040d55240d0300031400a4070060000c0815404407500a030181c04c0034018000414440310b403004034801d41541080c1100c00302d50182c03c100d0007580d105510004401d07842c2c400030505010050105010145941c040c41c4501c0e9042c40e100c1c0303040b1700a0304000e003626002e11404018400d4085c0e00f100e01c104034101c4103051400d40c0d40140d6440040e107031402108600c1e689a40741c48094040d03441c00c1e42d0818001d40c000c07022203188603569841281c2c0c4400072203e032900420140700400c0944800e0704103649180c000c4078054142525035103d034040f41c02004040e10a44d40310398600e81107011910885411000301c030818001441c1a8001511415000b60000e01198040b0360040900205029060203460001c00003482c983d0384940e054220024900400001e01100c0c6008401303c0c020b1040380c58096000702207244a504d49102c11030485180005501c203552031340b10110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 192178830 1250 192177580 192177589
    0x40605120612120c060c0f040504020306010c08191101020c03120a140a05071709061501030204080105070801150207080705120f0d120612050c060703021c0512093405 73
    0x40b145156810f01503103c48181030790b149400005011680482001c1000425040c8110b084406540702034030050398075122640101c4001c0040d8802900d00d402c08146000782d860425014405000316907260300011181d04142401c1b4801d414101030035620410461234404584002194442d0031a24000341d00011110048141e560803105640f0495903402000107242d00710700c07007005a0413500c4801c2c41515184859035524030000e4007070f104c140fa000d5100f0020360b21070307011603000c0c1590800034012802c00c244050021102802000101050f0700040d21440d440080d54100304ca8084001b403601c1803901050040048143d281140c0318002c90383d07020040300302006680c018440b00d0ba00d904420402c030710300b482181d102e03821030340f002120141414041000024280720080c2c08550f61130303075641e003450180c0c03601c6446010003c884c140280550505500140500702c482e02e105140c410325580c9081d0142c40d10328140c489080c50b294106075001502d00c0f00f80141c0c2e0381c403100b10354014068481c40002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192180080 1250 192178830 192178843
    0x305040e070905100c030207030308150307120308090f150a0e030c070504181104020c010207020a140a05010e060703080a0e1b1206060d0f06020f0c1e03040605120612 73
    0x41c0041902507004120905110b09411160001803400540d042510381c0c00a495560500c00503007004210360200d441a910100991100d1b076004007122082a82c0744040d406840c1c408030203501048204002a41c508004a144e030320708004003003c4c00940e442c10302c00c44503061b406081c0c8a10503650304008910b2080c100020008400d080c80108601840d0404010680300304d00c0800380c2944d80740b01c0420010f07922010140100310111070140c3c640001c401440e00a0040a00c06036000060403030000c0c1c10100010710002101c01035401418240d1548019111201c1540360540c0100c001c01a51000c171344280341c41038105e4107203036011a8040400c41c203546082d03604582c003595828419070b40007880c50200d86107002c1c44910300140c180d62801d41c001403004040c1c1d001c06400740303226050350000c10042e54111015520019062901c3d405104922a69449a00c4000783d00680d401c000d51924800001510100c2d040c0d603642c10320380007860500c29130b4034001410007a0040720102d8151440f441c2881013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192181330 1250 192180080 192180091
    0x30c0b040b04050f1204140f0d08030406050609040c0312020f070b1b0616050f070206040e09010e070302090a020a09030f0506040308070309080d180b040b06040f0203060a060c0305040e 81
    0x901c88908050400c542030413000026202c140c1e0101200036040448241a9411180340b1020014031080540201f0803c0309446640f9510100600c0424204154840074500890241c3c01c01c020680d035070f80500060034429203001e84592501801040010410281c420030001603106480382c04400f41c0c015881c211441d0000204600c01140056191403e04000801c040b80c0c200208024144441409030130411241c51608010300020110301d452244000c4404099010348620341d00d41e542e000c1350420050580d54140154240f140f01c203c2440001415029290010040142074942c00c0000c8002d42c85080c0403030600c811004004003050030b8400007000d03140203401178104d45c601440c0040002000400c0f440c2458684005480860350900c00c0c3c0f00c8800a03104000380c5806081c0320400c4111034988010085c0b542c9800b0042003010803041107002e0b0074107850034440c210b01035070490180c1c0003c50306145c12032100c1317404001852040010048050003800c1403460162540500890305104070f81 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192182580 1250 192181330 192181343
    0x2101e030507020d02010203010e0609091203090d091d010e0a060305060901020702100f08161103030a0f0c030b0f0d0807050d05120f040f060f020d090b010806010b09030a030804030c0b04 82
    0x2c0000041e01807010a0b00c080443c40214030b03541c100038101c4100c40b00030741450700070340e2010b001620700c08042103032040d030303240464101c1d03102d281840101d43e45101610384031000810004001a6441071520329030b101c80302031b0f040307641960708258902140c900018549a4201d444240c00408030300c050081c180111040700000daa01c0708540180030148509005000410001144120300c40e6480031541d80c01140040030351010f40100081290b06581b00054118903020000a001c800c00450f80701265803031301c2d09018404242c1c40c0600f80c1c21608001c100982102012080020340c2c5401098600395a01c01c0050368200712041d01c0307041c64091a94030200119500041100f8581c01402c0c0b400d52168080071818030311f182071350307d1010329200101c0080199846801c644041c0200b030301501c0403a42241c03010000708600d030901c0d240c2c600c020f1041c3d885500407040041404000581110a5040081c0017020070850568084640d603000420540821040025080015080401e0726004600888 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192183830 1250 192182580 192182591
    0xb13110a1110090c0905100b07060504030203130608060109080304120f0c0b0f070b0a051905061f0f030605030105060102150403020307020618100f1b020a0504050907171902101e03 79
    0x841030012220302404007c0d20301d40d000d004014881823482101d4200f6400a80801c0e6919103182c1070f8990300400d050009403401018001c6201ca40c00b6444031300c0f4080c02d80c1d50f654078540c0c03032510903100d00c564020349803c2680c056900c0d000c05c25403590811310a00c0340200d000a940c0d200c4004140b501308055a0b00c030202d000503080700380008005901d0b004401c8100400c80d80c144440d5400c003030040490200c00c0c09446000043c2c03181d031a5402c0028a6101e000d0480c007802030100024010b0b04c42a20703150100b4502880450745040510425100f14410380040003148203241c840011250011702c2103003103100070000e042c01621290050b0840940c07038488680d12181000400003427400324031010080140840841c0100c03540000c4010b6221260440825030800600200d4502c1070550420390b0000d0a0006100f01c5203c002007003030071505d00368684904c0c090103007141a03e964070b54030382400010f010030176403015113040d041c201101c0c00345040154103000c44dd81c1140401040612610110f44e840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192185080 1250 192183830 192183839
    0x20109180510080c03071202030c0d06020309190807032001230115121503050109050309030c010903050601140d021002010f05010501031806050604020f0d0b13110a1110090c 76
    0x41003101800c40d076406840000d4110001c40d40d0342c0001e10034005169603240c00c7c0c6095460a10041d0030307030040a80090070003c118103000d0003070351061380e13204441c1c40b80407010110020181144840160f109080514081140d1811620310560000c4000301e000080340050000301c0034420744101c280b0a00e1454042d0381180c100d0015404140e00c1814601c2c0103c290301450b1381e0003290420f4100b0103990001381510b4050002018007001d8000501c01c0d07280607160000d015000003c3c100c0603904a0440e0840c480a10044440b4503051000400c15030000005105030106c050010038046c4002d05004107000c110f80024601115460041003d40d64540800012810500030300780903000a0a05201c4620420142c0301400c03103021000e440542d231000801d03070300da8aa40413101c240c0c5840c51880e494000402080c0001c043c840c1e03211b8801e04a114201e0208142c2e80601142080d0a40a40381070942440080d03445401c0b40c00d890311140924840740d50014032030702c1748065640c042d40066010a091 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192186330 1250 192185080 192185101
    0x5033d06030507091202010f110d120c03020a02060420090c030403090506040807030602030c12160801050102190b061504090b010207120f0f031b080c0c010810060c0201091805 77
    0x3030030f035a0400c040321209215480408281d8400d02d5030a1800d42408944044d0458101c3d802d646241998090201ea03542e549500c814030360088055454100f00c00c41d11070701c05508070701c2001101c1d005600500001008610003006034055690b11140b03100a4201034800241550f00031100d03940356a00100600c410f16620481800c080c00c01520306916041c1440002c96175030b115444001c01c800e800200090000300c01800740d6032070418620b0541d9007410080704464110038401440340000e02803c0c00081c00f5031002508000201442c103c100c0107a1607610342440e10b0b20700401050b0880300c5840441c800c5140b05004100905203994005104e1190800090070021580d1001400c0890000c0310000304009048a8441c954060840509c402d81850280c45c1c100c40d468428441003040d0700200d040c400160700074003c901c0350000b5603e210560b24015900c2072401c2d682100030004401007840207a0052500d02011030050411015499442203100081b078010000780c02c0c0b080d110010701450340407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192187580 1250 192186330 192186341
    0x210d05040807030f11060118020c07030f0218041e02060c060705040611060609073c080c03040c03021c020927031e0d0608060708061f05033d0603 64
    0x700e03031402e02140c5d0300110059035074483c10700880081804401c400551450f10340e04580c220148041034130045036480c103041081c080504000d1f4000c2071644a101d01e00d80000310064481e43d840303a030403030314150741c044220400c950300340c0200e8100a00b0400609945010402d152150307109a54980e540c2e03091250040000e05000c45107031a0768040c4050040551b034041c1100c2d84080d42d07107008280c1d0805407c0c44540c00c3c000300d83c0b4524641d03003078920b20b6010020001188400901e62103040f0943ca54044031075103448200ea018040b0705012400348014a0500b01584000300e80c19040c032000c500c0364000a10103001a40c0340c2203900e401a104007031401040c040b07110000003c0d40a50b041480c0480c1400035800c60562404c041c000003d50b00c00002c40b00d034403003406001c202084448900d0b0206024241d03c1d82a24020302c01d024100d040d080c603903001d07041482858110b984450031600ca400100301da203c24922000c42100442034001507080301e80c0300d02803030080b10141c1d0803400d174a0030101030210742 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192188830 1250 192187580 192187607
    0x13120c080303130c05010c030530090102130f050f1302090414010302090c070305160804030f0602090108060411090103150504050903031602030405150715050117010f020c210d0504080703 82
    0x1049002ca00800d07080012b541d28000c414210070032140d00c031080742c0e15103071600c0d01c0c000300e689801e41403004900c03056018003914502d01a624100940342e030b02d01e0030404030740d00c00d0950045d109a00003880382814480702c4000600d021001d802d1402620000b0241c0d007140c052501c9442041c40104254a82060060340085200304901e2030040d0944000703000380310703040d0012402c45452402c0020450f609080f01d000319000b020440b84440c3d185802c6010b90f100c80007060004259501141180c601071041c100c0e46042007038440d00e40401e08006601502c840007100304891101032000030152503502502e80300b074003d40c002c3c6a0301e160842c0714090b48000b80c030080301158001c4c8000d100031744034000400403195204120341c0d1240e06034a0000b4118005000c0040c03151304003000041d40c412182458907004550800a01100d19004401380c02c034011214580c0469010740812940740303001c010038000c2e124000c4103a43c60400002000e81c00c0c1ca40540341215040f600007000824141d000c0c00e15030050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192190080 1250 192188830 192188837
    0x30903071d0412140304060603030806010e0618010c1b0e0c0708030615190e0102070914070806120105010b0a080c031603020901090305060405071a13120c080303130c0501 75
    0x8429826000c00c07018005100a0140030b03400d490707a800c98080d6500d610540f54109045076645080d161041c068921440110b0105040d600483c04941c090700c003488000b82c002d40003c0c00d2040500110b503081c010700c9005030602102e1850240400c6049a0542d64545040080342c180d92800103011400440142000e41d0b03440c0a202d4400020503e40490341c122004444030395030407280c162500001c0c482d0040540c0c1449540e640c1c4034006410507201044c12800b40c09445080c2ea0303d031080b50035a8a140f01441048401d0707000036282900400207181c100802500644481e40710903802421105c00381c000300c44d1240081060400ca992088074998070002d00d16101d815828400403160101800c0d481c00790a00d5000300300400c0030b0b4400c01320700d0000c582040031164141098105151074a0450203201c0510386e81c00d241c0400e0428685c101c1e1551602500c20300c090310b1605100b0f410307800b100b40b011905803150040002d00e14404001440c01010080c0640d56500081c0c5400c507002c40c13282e40b2a0381030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192191330 1250 192190080 192190109
    0xa050a06120c06080127050c120a0e0615010206040605070905090403180f0e0403120b0301020f0c0607020106050a030b070c14010f0b0108070c0b04080c010203040302060907051504090e010b040e03090307 89
    0x300c09015144148a0102840c0407d4a480710745c0030b44554000c0720f40070750700803601e50100b005215842e00800d44c5241148203070b82003621086011070711902101082030259002c980440c00090065100c20750000c15071801c0d0000f1622440000d100b07210035901034000800d003010600c02c8088809021008140c0f040d0084000742c0740a1401080c00d00c0144044e060164100320401054403640144081d03070341c020001c540d00c3d5041100c1401941090388804881d1241d00e0000b0304880c0140700c0d50054404c020000d0604600d1992000384441d0000c1c0b0075000c0280403100f82740052903c15400c3c4001510200100704400c038104200d0450f52054500d03410062160700788041e564010a210012a4100510a50035501c81c20464071900c21914905050b40c030010800c000c0c598040740e1030380076107a000c0944005a50300c6c000c0090400b040c00c100740700420100801c0081031074942c801a01c070441080049042d0340004002000c44060840450f0701350000030390a8150301c0c090113114090095131113510b08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192192580 1250 192191330 192191369
    0x16050d02190309090f09060221010909111005090d0f020f010c03090506090d020307091e1a01030f0e01090309150305150f012307150203040b0a050a06120c060801 71
    0xb0402070f41c03148540c41c0e0703528071054000c0d40c05508400441904900c5c1075554110030000c103901c015050209a000305000c00003c1140c0c0600d00a86e0141500a506840118150010131036181090100344040c0700382048250b1040e100d1805d01e040541c000e042c0317901c4100f10350061000e000744d601c40f00303030400c007641d40128006500914202e041e0f9405030b50040c1c8582d0120b010450420a80304069032603c9002070000d03000e0001e03049a00540300705001520301111003401ca0055400b07c624068881c583c0342050810342d44686d000824402c1c1d00301010030358495188049003119103952080c1c000501d44c02d024040c0c0141e00140421144581c0b904000c0d81c54024800c43e80381045000300e5100d82c0140143d8112030388904502190302c00b524180e00d4110450480c8074010350f200e0030303045a0803e0302c1909010b40103018400c3d2403142e50030280c150303400d9a0f1500800000c110003003880480f240d64641c0803400414200f044e060303040c49402c045560340e090400203041808140d100da0b11019030341c0f04008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192193830 1250 192192580 192192587
    0xc0503040507090518030c06010501021e031e0d0e0606100504060e100504150504030c09060e040b09030c0f0a02190b040303032d020715020a1706040216050d021903 72
    0x125101c14030001220384440007517050080d19400740196520000c5484102c41e400030a0b02c6048030340036001c0b0741005000900030060010b4205484d0303031a400c2884200c001203010700580300230401129041c0c1ca0507840a00650803102a0b030004600c0398088001c000b61401c08520722030303104149080040c03e05261a00c02409115400c888501402070010007280d100e0049054501070011031460025105400800902a401520040d11107648071038000964a19902c07400098413034a6a155485a940e501c1d00c03c5521005815440c0500c4100004541e0040c1800480c004080002c0503003100c01d054010000c1c0d007410404014055050741c1802c000c42c0c0c900000701c804896040c140824021020441c126443c801403001169034844500705040803115a401440c400c1c1c800c040d060050100341e00c03480c080b801000380b07800200d100311150b0440410340000c0d56500c0000200050701d0b101036000220110b0341c200604480d03e50180441003040d54045c81042e4801e0019802090304001544004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192195080 1250 192193830 192193843
    0x203150f1005070609020604060c1e0804062d0c02090105040b06122521150b0903030705010c1e050c0c06090f0d05030309070801020313021009120c0501030c05030405 73
    0x2060000000f10700b4204100c58002054141c0c0040429454640c1c03184040d24580700c41d4422204941e00303061910112091240c444102c03604140521b00f440d08002c0c046c2e4801034104c110000e042045038030100c2c6011100c0c03250242c2c000c9580c5102c0d94500074410300001590681149110310704000401c4281d448801c00c2d12140340c0b10b034441c14019154150b0a0302c2c804101400790300c915030803034143c55003d500290020310740c1020080c44891345400c20800d0045600840340e5030300c3e0ba41e10060400180580c0400780c964610b004041d40e00c1c103240c0c0d65807a8210f4101821600104680001c00c181000141d44241e442c00801c1c00d095113400da46807034254480e000f0a000358410030001c240c0c140c594488440c0d070000b4030300251900000d001d4900300a80e8a0300b04944420300307071144640c0030078200d0040c02a84d00800c1072640e0924101c205600304100010004000c01c1048080b9000107000310341d9401140c2e14901070000109681c0c201400103050307604440c3c0500901104000b1b100000b175000509 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192196330 1250 192195080 192195109
    0x101a0c03030a0b01051306020a1a060a151202180102070e0106020a03120b0d0f0209010807030b0610140706020d0501050405010303120f1b0e0a170303010303030e071502010203150f 79
    0x1002a10f074001602d49016075880b00107801c403041004618160001125042a4040d81d03440c04110304e58444d00103081811184503070403500c85603017008141000841034801c114070741844841c00c1c291540c07038405c98014440f041d0032924441d031001803a58052000742d0240030350180074040c540c103000c0081d42d10044440000c040055100701d070f20f419016640543c1e620400140010a4240c2071b041222100400c8103051744070b000d214000180c82c150000d00c40003183c0d409450780210381d0b11181000310035240500c050040c004907890b6142403100c940000d05080b8441d56006889403e0311802600700c80301600001c0c041c6180c000103201080d0005030700c0344005c0340700307102007200c40350440c00304054901d218102001c983d0010103014642c3d040204003d1465040e2103c88420340c0c6e80002d482e03020107401e50030806401c20001800801d02c40d40103007942030180030890f00340980d90801080400c1c03442502c100140d60120511510519681e4002d06002c000c65540040f40101d03c00107071100e42a000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192197580 1250 192196330 192196351
    0xf15010824060a0308181806100503040f0204050c0c0d05030105131d01060b0714210c070b120103050d0e0a0909020d1b050a0b030c120405030c0105101a0c0303 70
    0x560b9035507840700724601031a4011620741e1110807510444140c402511080342c400e03420001159100d400035144280b00b00002003590500d44100d413010b6440b0342c0003503c2a68a031845070440000f50b03e483c01140c1c002c0d407400d2902941d0b658089961800c045419580a0801c00f003080100066580c4070089001d11203003020000700c6405402e4580d11944150000305250b50034000002080e0700b124000c0c203007442c041c1d031103860007108080c100c540725210b9070707a603440c0103500031140084d100e00c0601804140c0040c504440c5100d03200c2c605d0051a4008018014440c841360006004001c070621484505c1c1e40d160401c604190502c0001070300c142041d0203401c811560340c52428055680d8001089180c036008045070742003000c0c01100406140a030302660b8015686510001210000b00d400c90381b140450a0200d8100076182002c1c0292003000740c030980d0725210a2042c10f040740d0081c42664010381ca01c884d0008094a001464805030ad035503c165003180380c05011144460101100316a40904135a5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192198830 1250 192197580 192197653
    0x2070e090a12030501090e0316060b0604030c08010515030a02090402060307140301080307031e050f03060402090301020c01200405033706050108060c03040203031801030e0f150108 79
    0x106a0307103006082800a4510540000d0520b030090305a0702150603074090030000d00c9400382c1d80014580c0c03481203e00c2201701c021044501000315085600800a02c80018102464181ea80c0c860f000803100a070462491030755285c040c0503070454195151640c0e40c100390081c1c9000c032a90740014144210090000e4024280000040c0019100d0f5401245403101d81c01210703160b5031100301032550b0f50048001200400c0c03500c84110b8100c3e2241000c11882011991a07520f070400c038a00c510745541000c0d10003500b16800f40300f5442a80d50a0011744000c0b031021000061003030710103e8061a03080025190040044204002e001c07941340030401c001107188010841c00040100c1c08900d03031030100000342d151042c00040b120703001c019090b004181251140d2080303c0694032910354261061006580081d85507204112480c05480f508100800f98001414001a100d80072100c2c6820301150110645094220300d0000d1041510280c81c6805003c40400030840d500d18244010304042e83c500214003680b0405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192200080 1250 192198830 192198841
    0x30a0b0a060f0e0736030c0f0503070306090f0c1d0c0a050706091a040c0e0603010b0f010f030b060c0c041404050c090c1c020901030506100e060706060f0803071505040302070e 77
    0x11706032203810b9585510a03140e00e06070381e41179040c0c8800314001180c08420090001526640c51417009044e170b60010082c0000c1880c41d5150300003402582c4048410b4104521607501140d080d842c100010100038008440b0041c0321038001304400710050003d01c03858000d0204100c8590301c03506803445140d0003800001c41c04858149004101000da114003d81e101c001c08000030007080302d5022046400005400c84261244802c2500307071360b078226a00d90800d480c8840b6601640c80341488002404403810300003520155074010843c07980c081240390a40b58007081039800f05040a10130807000c02081700c600041420311b6a1601c0d201c84844080501c90895500811041c11505d81107444080204c1881521607064400c0c640103034002e014464007007840d1000195007801d1503844844030b50119601d1180c04040e007020013013181c02c80182540d40d1030f603400005c12f0fa1990300840c200a0280e0f0341c029030b120300580c50442d002070341515400700c0481c02c20051000181d0006000340a81e1004081c20485540e003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192201330 1250 192200080 192200117
    0xc0c050705060c0f0a110a1505030c07030e031b0a050402070c290a02060105040c0e030a0b07091a03010e0106110304060e0d060f0e0c0303071509050c030a0b0a060f0e07 74
    0x100c0c100c10503174000c0c8200802001a50b030030445002c00140c075000050340d580ca0000045641c4081e030f683c0800c2c0d040000610401c0184010401580b00342004990245010086803500c10303148464600c90b1801c0307215a0181ca41031071a280100b40845056148c04615910748000130b5003442840203a454042400c1d012130303208081803d8118488120310703103d65069034002d5403401c0a01c10603025505e06110311251600c00c4090055020b4054011310460084d0345e00e0b1000703144c0c0103050701e041007038102001c074828580c96424000f0901042503d500d0354100b02c00013003520742c1a0b100c1c00500c40a0110390003100004009d65080311120b04080c0440301c110303004584030300c0d0200b0006024a150000801884020394082c1004000b080c003100c1044051030207255880c4500040078045800100c0c2070301840703045800c00200b60f48250309a425154080300031a160098401080b501c03892184e00300081e102c490b105441c0200070070400c00c0403092031302210040c0e0351400b802010412a001c1d4101480c140c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192202580 1250 192201330 192201343
    0xa29060c0c0d0c030b07090305030a0c050715080f0906061c020f0d05211c05061206040302030c0d090605180a031403070218040201090b030703060306020409020d0c0c050705060c 78
    0x2d4402550450b440ca0025000c03a41d502089078070110010200d40102c0c843e10403482544e5000c40198501020600c041d01d400c0c0032107804650504c00e040c00402e889040c0c6244409044003500e030044241080824614000c400610720019030740003900f0003e003603803100c1244d201e211100c080307a04903c4060000c50040024082c4007074002c1902c0c00b04600b0080b00181d0031040c1c1040d0400011042c402c803450720058400d011140c0c4004900c151000c80660495001e541c22202c0107095004503110101c40742d040a03001c80702940981c01c04100356101c02402d00c000d01c1490b6062a04148003400d10f40041d0007070048d610920002c90404084c400c0c541c4408d079150000e56002842d0300312025140c0d600c0340d960380c400b850032401600c0418101c01c0f1440c3c0340103040d000f260305843d140341450402c110240250030081202007010346440002000c100c030fa200501c064503400e1809a5141c0e001d00680b0140c5440d180304400300044070078904042040460300d203094403000c98031169507585020806240c0344 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192203830 1250 192202580 192202603
    0x301020a11061627051c110102060f01170f1204030b070e130c020f0703050c0307060305061021060e01030201111b040c03110d050106170106020705090a0f140a29060c 73
    0x5844140306140c1c1000000f10500c02c1f841901d0403001c8080c000f00498450300c1c15264100d0418205005210340c14202c140031000b090188111852000c000c00c103035250403800b05d907402404100203000d00511096178445540300030355040070700042d0000c4010030b2502003541c0ca0020025912545217039024030078400c50a40140030012190041e8503414800d031180e180c583c3d080c0c400c2c8103100000422030b0007405101e01c0384000500c00c00c083c2d81c07504029907000100848203003070400201072499204d82940f150401408200c0301038061581035200142131070702e010a21141540c4411110b801d8017034101800e2502120940e00449d03810a800b00941c00381525481c440413036030002c100340300c00c5000c40d440541292400e9440c01d02c0d01c80d04000c00a1f086a085c0103000068001d21002e0206041c441c013201d8100c1e00a00000800100c0498000d0443e1a6019290b8a9802400600600d040c590207407d46211548000714a807078441164001881e0340b1300102c80c0030b0b400c0400d0702e403080607052000c0036044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192205080 1250 192203830 192203839
    0x302090f03240907050a180b06040b070213050903190504090905060a110403020907234501140c191202010501030305040306020d09020301020a1106162705 68
    0x280250440b00302000480c0c02c20034510202000000d082210005142c4112040900340804050810054801c2600003c191252103515100520010344556000b800203003042450303241c440319079104201182c4003a400c3c00e802142040706105203881c012080b030301504550522170402384070300b107400e039910b010701d03401004d00c01d1600240c5030038004049081c601c02c4c80081c4007000312111300800c0641d28022800060b401c401403400090049001d211502d5005086803450510440341442c0a0fa1544c0300c45004a4400d031000380480414100d140b041166007248071265030320300d001603680c2c800181c0180800e81000300160203c000c038000d21007151072107442242034480c06a1282c0c4030758040c050844084428441c400c008907041407040c03180034180d079815034138580b4051441c0c41c0c0c000a9004850542c16441d640c3c1003140040c2d0b07003407005140e0304140f6143d000110142c05106801c04500a246401c030071400c07a164004030350311441004840034034045400c44180c00f002c0e64904240103812440c0c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192206330 1250 192205080 192205093
    0x102010905010c120e030304080406052b0b040f05011a1b0d02010b10030509030306060705030d050106200705030703020603071215052b06020a030b0d080d0b100f0302090f03 76
    0x181540050380c01051110000244017103001680c26664030702c0300321800b03044d041d02070109001c01751091000b0225010b80064240400d82079100d01d44070344601319058900160b80740c07007081142c1014040c0da06500040c8100f04015850081f03d48190116003404441401300040c10200c960f000d840d00250001c9200d00b2100c11070460000640244841040a0301c1141035140c01e03a05240700e400b40c07d101d10f16840c003440c11070b201d80c000e01042e500800c50440c0c03a8082030281c004814413074491117000b840203a69540300c0d100c0308c2c20082c241500a0307a174207007107421a8006028a4500185203c01c40340d066035007507070301c0d55040f40803038684001c4030720700c12045d0400025400b2114800f020f0400d941044488810040070140303100314460108070300c00d200d10441d00207940482c0207607014140d452614200858400da015001803000e02011200721600e1401184480d41001ca600c5400c0f4946015908040c0da117001e403202400da8418480b100c8105900001c2c09103090301c8440119401c070720f02804a801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192207580 1250 192206330 192206351
    0x111302030f0708011203090504090c0e04061b05070503030f0601051308100f060608131b0602160b070c0b0f0712030e100b0a09021b03071208071d0609010201090501 72
    0x100003090300c40d440003d400381c0c00030039841e400441c2c0c1842268140c0701d0601445c40d080a100107014034020a581c611403801c00000d4096011807503e1240f84034407000141120310007811805030b10703e500c0b0001008800d00010000910000480e6000707044803452005075950580100c0ba07038480c0600c0c6004c6642203980009108800141c5980f189021000500c12106028500c034212a614420500094642000300f1080e810000b0200b00c0d550103408201a03103543d1480328045401c06911000042e071040d044282c034103039000b4020002d808100d28440c6001081c0d140c15406020364090b140c1c4516000030110f10180700c050031103103103944c41440d40300319003400d40c4003600030484460703100100d01450408095542c80c6119000750300300c0060440010900341112034000750415526901e040440c1107440b1102032040010b40a0759100e00d003000c1d000d0311148402000000060448001e00640380500200c00d1486404692065000da8031316850355620380040740034003403242e006002035180c034002c0306 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192208830 1250 192207580 192207601
    0x11070b0a050304061a0a0b0702041d241501120e060a0209091f0b07060e0f0c0102160b030105010c03030207020d140f070503060703181403040905060f030a11130203 72
    0x511440c000d031400c205c03824414140e13031529680845101d501440300f040511003228083e024101c085d0005c0c2000403044aa907100403c10f2a011169248650142c413900481c2c042112107019a09030901d82c100990603e80301c54980340d512148100d0520001c01821342941d9030301c4e4041898000040304588150801030340080c000d40c0306a014a001d04442000100d010450741c0180c100c0007903524503c0c90103440c0074641c1099030031034503040300c81a80356248102c000305d0811400e02c031b455030440a000b03142443d0001a25180a040702d2818961a40401700101d0039203a0640381100d0003800c1c05001b0380000e01c0e08a00034461480c00940c4000044a007070b081c44035440141c4683d046103000ca4550380d80118010346e40e401c8912440b40d05510403000508101d1081d000a44030301c0704c4440c0990021400d0750340d8584884404001035040c1d2010030108514603d9000d500e810002c00c0e034900805a040d4004030b07880d5000d02ca000390103412032905000e0261210b240c0d4901e5100350140454032400c0442040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192210080 1250 192208830 192208837
    0x110c0616030b010e10030203130209040602040501030b09040c0e0a02040801020a110d17040f020a05030703081207030c0806090c0f0f04050f03011122120302010207021f02070611070b0a05 82
    0xd4000a02c0c003040c0c0316543d40584806210060000c00c26140040c1c01d00040700654402080c1f10456085510010016150603882600441c420f040260710745080c803000400700d501d020f2410307200702c1124061101140d440103c01c01510f0b807c5510040c50b6a50034090f0001e40309640c00081d03a5840051010605580098100d403a0007070301007503038131601c10b03682c0c12180000e5211416210000c0314011400280071a80819402d61000c0d140c1d1074119035900000f410040564020b98036108002960364030002c44580003a840511400c0030480082c0c034010040c84440d00038950f034060072210300421154005c84096500c6003501781466036580c14030306030280349600300740305082c054140d407140f07444030b8941070042550144102800c0c82c1048c5403040200b100e503810f54403588041b0500c40012400703441c0e00128080403802a000907980303010b28814042030b420802009210303151000145608680e000c10817004580136440c042c3c1554410425060800d10ba81e800b40000c400300141103c00300707410074040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192211330 1250 192210080 192210121
    0x30a0b091f0504020c07051306030803010b04140301110306012607050a230712030609091a1501020d031d070611060a020f0901080a09061509060b0c10110c06 69
    0x408100c0d0750b60b401071105078050600d2080503074103c0c1100340040c0c146080c45644402c0d900c030303010405036074070746a0f0040c50348280c01c200c458480c0000e0034003145044a20b605880901680208030010502101640034007014240703604012201c80f425001c1403003180004040000668420000c2c2084030014090f0380c032182840f408610a80c04000701c003001c05180b150110b8900400b1031a00403980d5070403d508035550840c00903d503840c00086651009403240032b4500384500c00074000921007940540e10000000d00c000f40c1c0000c446207554050741e0118100c007400c0c0f0203003804034001251501407404070310110322040880c41480400a402da902c081010b0001121a06581040e15403442c00000e80c030840c400801042010006251194441e032a40740d07000c0031203040054860f007140c0e19141510814020002c140d82098000d004e031110358416040100960b8512038a42814000e01a03103504140040cac8001e265114a81121010103404075001f0b1188102650300318500700c4441e8003c0e4101000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192212580 1250 192211330 192211381
    0x8070e01210e19020d08070c0f0e0105040f091205090310110901080f0f0f1024020c03070608060d0c0b03191824020c0102040305060a0b0103060e070302030a0b09 71
    0x50022103c450072050704150b90003400710100100c0645a140003070380251021914401038010004000050246001c050f04020340550582e51501c0104419904da030803100140501e003100d0380c80003c01500c0314805686003410301a481381c54440019052912003a04070958034144200740da00038498000421701030f442604d500010f620340f4100d00707854900031910004c003003040b440400c1010300282544c0e58016000034610342c02e59100c81c4000c58041e03120701c50304030203070000c4c0750b40660940502049951900950040107410328080004220075809000f15018082d0643d80000b8005810b1008021f8542e81403215a00c1c1400145481080041a01c0105080c64160111018680f541c10403160030f40101d041d444104e908a0001c00310383c6118865101d86508000b10020003400780040c1c0b0007540110701900711450050300140640b40c14030041c2e030416181071024440a50354004080e00010203140068880d580c0060000090000c040081d03031010800d003c01c0030204581200f0000d4a202d4032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192213830 1250 192212580 192212593
    0xc0504050c0c0d0e04020d06060203090a0b090f151603090819030c11030a050712050c04050c04061d0414010518040b13210e09070f08070e01210e 64
    0x70800a854003a410036407690f508040100c4021600c00e441c4800c074410000d100510f45480000e800d0101e0303040d584060017582000c41e21480918102d20140700401c40c4010941c07078010316030005008400d0715451184141d021103c0e150340440c1800036903000c414108901f03280c07204c02e801d0103884040359105840b00e61140301300048030303485a041c00c141d80c00c0e81501c2e000b00d600150703555100c4880b41d0416a503098424500f031000030a0041101100801e00b4610108003a11a42001400c101075003484a01803405c003c01d12840b59401d0045400316190f40ca4030040100c00342c0c140290070380c0c4205480c0d5009050004540c902c0d01110481c50413200c00311a00071940403042c08a034801c00080b80d018092200c2c48001810400041c15650a11481031306005102e50607401040c0c0c117803211881610000c3e603036840402240c00e021b01e613140c001034281090080c42040950060003660018018001c0215003581c140407a409103550960000b200c207000710000140c0305240008000c030f19040c0d0064400c45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192215080 1250 192213830 192213841
    0x20307080a0302060a0207021306090218030a0f0807050f0d02070e0a0921050403140106030201110304030503040308090112090302160512060c0f0c0d09080c0907050307030b15070c050405 82
    0x5407a03903000e941500503196950390810b1400082d0000202070340c0242a0241c11001c0c6104da100e0100500001c642c01a140d5459a400007107070361004c400b080c000e40c004410800458480d014440005502070901941c5a00b94038220b401c160b000000d294a81c81000349025049801094030003d0790000441c104c0141e403603007000070a0300c2203400060f01000c0b80450fa20100603032401000080812400c2c07562a10b90799540d026245280c050071583c030f0381d548490500466030300c0030300583c032480e00c140110b007080d00355160300d078aa1191388001044c8080016800e407d603401450410000c0902c7c00082100c43d55508029444410381211641083c021900126040c41d12000031494101c50000424181d540c140c00d8144aa000f8007150350501014003048441070003c01014003200da00da030b11000164030300406149060000c6506074801d00d4941c00304031109030300034103070b075402106031030046074200801d0080385c03940c2c280b1841c590041400213652400d00610850340004c030740055508215a6491 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192216330 1250 192215080 192215083
    0x509040503120a0c1d010201060f0b07050f0601030b0a020a020a020d03020105040507050a080d0c11060304080a020601080c0906010807121a011b0c0b0a03060b030103030e130501030203060621010212010302030708 93
    0x11200d913400414505991508000a819070803003a42c10103000001d1078a848003e40c00c61220141d202213124800012044100103007400606001d480b001d004281da541540d46a045158005025103052540403a0b00514030380b0801c8840351580c1c0161a1408200760b500b4001d01a180844003a00c4c1882262800503160401881c80390407181c000c0d0240002c4100400c040300c40c1042c01400b42d1780036085e0348060500d641c2d1107001390f0041740710b018081da941c500d03540007a042100590001ca501e400c000000841c5880340d420309640f21a0928000f11541da8000c0280d9020b4100f502c5400c0f024030b01480f1080a2604440c40405544240c860100360088001c1804601d507088800500130f4440000800030302038400d010307002c8408a0305000c10805d403260751030600758000f680181c1c0000c0a1040c21081810300341c40d000c03804400403205202660550b000301c2d9854101a111602460080054140f600e82100610051740a0040203541d6801c8540c0c100811003020300059200340255000014001d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192217580 1250 192216330 192216341
    0xb0f0a0b01020a0c0b070303060b04140109060206070c0f1e1518020a1401050c1f060b12060f0301020904020d0c0906020d080106030b0d0204090b0a180201090e0606040509040503120a 80
    0x9000168189045c2803100c0f2900c1c58100718412414135840d1900419003c3c1044080d0025040500e4040441e40c4904001400003000b54401d10071340d00020280b007036180c1d00040740294150051207070708404286241c43c4650104c1c4030005469040072054650800a07803000656000c0d00b003400500c581c014140b8034800901c00ca80c0e000b9804a580c680c100b00001c214501d400902d241410700a0030613100350252400c210144451070404407079040507455400307a51103144041d102984680d4180055104440080a00603140c14860940031401c00340030381d030035011583c004502400540d110a140a00000030b4213003001900f0101741c0011012070128400101000d0300783d6540e5078028030b80d1030840158010400b00140d1500b01d20160207200c096203480c002daa040520903c803001c81351405d221100121100785107291400c80c08585200050307a0f0182c89402034a0381100324142c661141030018801d0310882d0300c52500706031601f00b00414004040050298110310395000b010b10307580c00b00024112503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192218830 1250 192217580 192217583
    0x61c12030504260316020a02090403110105010605040302030a020415091401031101020c0a030f03021204170d2105060a090504080703020c0307150f03140c071a2806030b0f0a0b01020a 80
    0x1d4044c13001440f0004940c103401160785090044c5e84040351542c020660302102283e00b40c000c83c0801140d407031000024030401340141340c0c51034000c1c249402c0d980040d403a500b0300d8002074411a1103024452101c0301e0b480c0c441000303041c05076041251400c20390500c1034104003448161070200400c80302c18001c0d400416000c00c031400080040c000e06040d951490f040d80c05180341a000c46c810f41c500704058501c50402807000d07106141801c100800d00d0600306150004200c211010004901e0940002490407050348030248004000482d20350340710070100b410700601c0d90000a80900301011300043c0100b00c0000c02007180264241d0740441c1b0f00c0c01c141591840d40e445540e8292482e680c160850354490121002c8201e8140340c00326202c2d90905159541000690350161206c000040040401c5240c008400314000d00e464100d6091822140c42125600703144561085594a01148000344840364404c1015503885031881c03102c1e00b00342a41820441044440e0961146480d44d0200f55600005401e41100d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192220080 1250 192218830 192218903
    0x1080c040f150e0c0d02030703061e06200f03040f1d04020306011809120801050a0603051e040311030301080c120102130312090509090609061b03061c12030504 70
    0xa80c81d0240d406603d800003040042e4801090108401040c00750000b98015810340d50042005804c1c90b1201c0c20340d0764500c000c1c0002c810880f80401c80c0641000d002c860310802d09025504c10941c4015030b03800d10b00420071829542c080000d001c110800121803113815140180300341e5040c0201c034400d076090300c2000d85020f541036003e48010040c0c205001c14018011905120101e607043e09070f81d0f000003800420004001241c200700042c4403031309081a1040040042e80744c01e20507828652101c01280103680c4580703c1c0c6101d0000000d09050044000302c200d0b00c444130440c1d81e20341e5143c4500b0380320200c00b00780c9803280c0c201d00c3c141e0b502d4040500a07145088500940c1d544194a544e0750b20f55450940e1103600e042c410900c0c4002081d0381c03600c140500c24040440907040710701d0103e62050030010b005103584e8020500300c07010580d00e5400010759074070150a40300c4401c0010a850704410100e1803000090504083e4803507000c406600d0303000035008600c91442030711681109007144c00300c28980814612003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192221330 1250 192220080 192220121
    0xc03190f0606030219050112140103141c05030105031b010f031d0a030302041505190c080d0204290a0e0103020d1512111e060307110601080c040f 64
    0x114801250181035107101d00307030004250b5034070703804606101000c1ca11135401003101e03242041596000841c0c1d00d515034000350100080031070303904100e24090701808013401c02d41d00c0c00d440004181c82003200e0b0445202e0078000444c250980b64000302294000d01030240640a0545841c1e00074600d800c04950f4804161598020f05801c14800c400a0051003e01d0351841c0348941d8000d00c40d4418808108158000d540141c0d4807400e04031084803501a4101e54404c2240c104006c4907011800d0f9424082c003001440c001300b810700310b41800560ba005010040c8134452000500040c00b0754010a8560360ba000d440c59140d100c0b0070415011800d000c1d90703410714042200b5540050856101e5030007421030b041307082c5002a504000425100800080e900031001e0b08406401d1007082c00800841001c02e41400c481400030240e01d070094400302104458503074001e400200c08208101e010340c1c1c22805543c181c0003110a9517035036000740303581ea4240307041c0540502d15000c03603010481318a002d000c000900c035030b600680c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192222580 1250 192221330 192221333
    0x705101505130c090306020406030e01140132030303010f0e091c0e0102010603060f050414060601020c040b030a060e0d1814010e01050f071a070e0f040c020c0d080c0c0319 75
    0x505885403030b0008000300c0500c08400181b141c409000a44041d50700003501680105100382110303840f0058400408000d0300410416443c11544808003c548800c126001115901070461210318100b95615010200010550182c955201011152000d44040c26a02c91505685c2c4a1500c05005e80040110303144c010078446c024054000c05410620001415903966119134040b00d0f032000c031050a0540394001c1c001400803590b114104040c0c100041d085500f03201c0c0010750340d0050003410b5070080b81c489181000301d580c20f100e10305080e40c008070240021000f501d03445403200340c00016400030410461039040c01e2581d504806082d0750511544040804c2c1143c01515805198000359040007020130515590052042c00313004014420080524100c400c031000940c144e20040c040820440d110382e002d5416a43d00424000705c0800340c500165407030056404a0030300028020f0301e0341080358901d40300d0402c00142c0c01003a1420a41d025511484514001c150721204401800f000e8030708a100c01c0380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192223830 1250 192222580 192222619
    0x201c030e091003050a05010e0d0f0206041707080706050402130207240204080d020c0a06141804110c0f21031b09040501030503090108092409010906020705101505 71
    0xc0e080801c80b5851210103075259281850441c803000c0844030340c0d450b01c8802805500400880d5118442c500307100c0485903850500070355904000b84041c1401c07a01c05c81004810299000300c1d500941c000c2c80c0e442d80c4250170309000014040070390b800ca010740d0b100190b0500a010398401d0f42c41c1d06600121035521801d140c01205130806401400d10f00311682003000003250001040010001180750700500b004e00900c0040204400203a03000d4414061442500447e0417005800c4890179205120801e0140782400040340c01048100454a0b0404000540030902d0344009054001880c03d05d044488101c08024501e040601c0f03040380026800d824004140c0703a400031b1001c030640c1e0300c42100c110f003003203159400102694021b0f0b0040d2615000009e0518a03035074048c02a9900000e101c0c010048101c443c0303007a44414500082c9513440c4003501011488868081d00401580c82c1c12a00541d250600c500344140c5400b0000141590030f0b2600102d0707140013400c0b1300700000300c9100801d00002010b0040300d82 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192225080 1250 192223830 192223849
    0x90108071b030c05030c03030103050a05100203010608011205010b03030d0b040f020705151e0f0601030f0e03041401051201030b100f0503102307050d140c160807201c030e 75
    0x101d8045c08140011820508100081c0d80290f014500400c6d01d141ea60400c5030502050b080c42c417056500400050200307a4200e01d003070b411640b4030013031000c80a0143c103015005200d03404e080341e418000044c0103807000031141c00c88504044101e030b00300190540c0303104c084102c0c410702600401d26002103825050304154454280e41c091221a000d00300c545070340c0082c41e85200110f41030903891079400e0520400f964148910312110b1881c1508010290405043ca5602e008511824000d102c4003c00c00314641d00c190181c40001304911404002d0756100d02d8a0300c0052011590f0078801300c100f8500248804002c0d48032011605c0250207000c10882000c440b0001e044080c420300c0c0040001050780d041500c1d031305c140520400c0031381d40d240c0e01c2d000604280740030380c5c48424424910301440800e00501c1d6100394120758046461400401d03580e4114540102c2d0340c0603c0c0d5002e400d0000e950031120b6913030324100341100004012191140c60b80350002ca045e0900c0e82813039020b0006202c0d0503000890f814003040c1e2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192226330 1250 192225080 192225083
    0x603070c050601080312060909070e0703110409051803130905100e070e010905040608031209121c1b051801050904150e092a06040b0d02090108071b030c 67
    0x8211040c4894403450310b0070b403013079011074070941c000102d044c1071003155003500e078100c101140c645840b401d107001515500c414a005e40300f40425080081410742c2d019074010700c45121041407007521581d0780d401c510020101291b1801d141d0200c0703041391321810b03404400c580e00010018401043c0d02c0c10004813200030000101800361442c0d80104c04541c610250541d10304c52941e41c0c0c0c883c000400b119000400c1001ca90780454041c1d800c01c1030500c08040b010003a5007918020000482065032103240c1113151170b8288a070364400d58400500030051022402e004001150340441c00d0026200200d042946544900b0070b01001590a010340c40200110300410100c00d8014500306090104400002d4101c40c440c40001c07400c03015100d01004100c00e03148160751300c61140d0000d04245015034110000301842805145500c0903c01c4008030b103036403004151005003400c0448280c440c2d0003050010004d500052000740411941800a0452849032001640c0700e96208075081e01078803696401c0d0340c04001e1740c20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192227580 1250 192226330 192226337
    0x90c0a081503010b150721020304031e0f1527030c0f060c050c2112101511060f070e010c060f0e03031b03090d143a09020d02060307 58
    0x41c010983d02e101e201d0141c010b02c1d1440c0e81d6909440c1c94043c2c1e0034864503145100d0190302180e074040c0f954010003a2421680c00020411011500e0300603d40041c103204401080e85240c00004402e00646012075090520441302c2003f040601c00d8000302c406401c1108404611740c501e519800003480341d4100340d800b5200345001c142d54076580d6600815500300d000b40b200000e201180e82044800c0c02c0000b55801c07645207010359207041852482403114400d001100c4150070004000c916075484000e03900008088900d0071820054a08200501c0130601d10220f16081c8030b0200441d84008031040360394010f081035103c08520709102c10054441e904040b030186c2d01e081e03a0360308681d150314043c0030701000d0104c00d1000d16a2850441c00308103041000c11216000544140200200c400d40052400e180300d6031130414080c0100201c200c1d181c540319007802d511a0001c45c503d40c1030314903c48181d032890360100c0c840740074200c09140080411074046000180d401002041c860016003032a17402550004100d14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192228830 1250 192227580 192227591
    0x10051303110f06090c010306050d0231020c030a09060e03070303080702070b0304050703030816080606160f0b0402010806060906041712180102060c16030e040b030a060b090c0a08150301 81
    0x7203007401c1c0542110900da59802000b00d0b0741d00c40d039148c419080a410100d44c07085074205a500882d200489c01c00c00b09046603194040401000700b1110703084080c00341040d05540d6000b01c40b0131680c690300914055404101c0b4071001041c00e41c01988500030416001c0c0c0109012451518100c0d03020502400440030350107100c1010804e20300d00c90087d07100d40d00440007059842e140d0f140003040d0b80c000034001880084010000944564811030b041c1d00004201c440702d494045400e50f01d60106680d9a0007041010512481001c106801c1c9a2a100b0b0f4001d8940c00b00e25030301c2c030741481818483c41100c5c6912000400c01440703100301e00113240c011103e080d001c655091600303c001032200d5028101c0c0d10044201c001c07055800350b070704118065201500306c0130541171040030000b04000030440755005045c020703054086504e0f6103840e404607450400c000c0840e515860141000d100030800d83c40b040e170146035904005401c1030010004c4400d58a22566840315582e1007802c84d00b1021184007403070b9071654840713 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192230080 1250 192228830 192228853
    0x6060325201f060f0b0a0210051503060610050d0f060b0708041403030f0d02221401030605030a0201020606090702071a0a0f0201090213020f0f040e0106021005130311 73
    0x4040c40003152104400409150105054007440b0aa008601440e01e030b0901c50f042c0500040c12261104440111140a481d05001c5405070300b090b19103a10f070500a89450100000ca81c24041004034010341039050f103002c0d0b01da410901103190144106600810400c105981e2404469030020380305801000d030008a107502c0e40f00300925980b180d4411340f030840b07010500f48035120210f250520000000c500440c40c12403503a41c030084c90300130a4652002c0c0c40e030220341907010500000c6c4d031840b0809440340100c246501e444250b9000507600000f00d00081c5000d4000c112414001841b07808250140c0061030303207940303050401000c400000d26039000c60050003000140c0c4c109504459a401001201c1e190b16400401401004000030305055030031a81040d90701c2d80035844608090700c503003840b140051782d00c08680200c0310b114070812a8038180280005400a041c1c1c000140e003a050b55040d50076120410701c0400f00e00141d90007600c42c04000d8100160060000340a1000c0625003002c0c00c2c280e0783c512406 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192231330 1250 192230080 192230117
    0x50a0206030411011206030b010b030702030c010f020a0905030106121b0306050408030f1f060509060403080403080304050717030f090d0807060b1f020304090504140a08040e06060325 80
    0x9407800c03143c03410b422000501540e0400480c1c441e201c582d4000f00800d0b4610744810040020610650f07203d06000004510030314400d2003100e00300320f64100240060406121190025482000104001000d045011a040c038040c01200304568607520740d00012000360300d0b524400c80504015900322400c520f0000700091450007620302ca9070150410130348a20f04810180c0d0b01080003440c00b80b1103003034200c80c9420220626112002d440061414030340f20509480824014881c45d00041d05125000c9400401c2000761002548a13030311401c160740c07249641e00742c00030761100b580d03261210303a800500c1034042c4101d041c0c0c0901591000200101d90385421038403080515171207a103017640e265854010100c028100740101c0400d0030000500d148000c00e0020f4025140c0c0644c1c05580c15030b5488801080a005c14032a40140c01030f03003482a12071a85152800005961044c0f14145002c01148002400e07441e100c41520300ca034450301c1c0c1180c000907001c0d14401304451300742d0314032050050702000001402c29 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192232580 1250 192231330 192231337
    0x911070809040b0a1818050604060e19060504060b06131e03060501030f0201021209101409061911011103010605090a03120e01030e0106120b18060a0507030b03060609060d050a0206 79
    0x10f40502c450171089080a800070340f4070700c2c510004c4041c0304010110000f000058041d40c05500040000ba8002c1d08034180e606045c0700b103a941b60100c10465600c8140300c2c441e881503004d24410f0004000b072200c0c0400780100c0e8002c8503400f0b00c030264003241c10845032250b004900e040030125a050b4040f03585a59441e4100c42081c0c0065038085203a02e08038045580411100481036081c5401d0b608021942000645c12000404c005082198080429403108001e0066604100780144159119883c040c50038003241c1c00320400c500055240150b40c0801c002c184200121485c000140e80d00e940c1c00e00b00240c07555409500703419000044c0c41800404207100c149000801c10a030340d984115034400300c00043c2a598040c140d50308907403622104100e82850010b82d0382035154040d401c0c141961790440132081c802c02501c50710710680103510410024181952040d481101241c504000500b4010140f40c0d441200f241c440340c1180203940460b2107442e142016402d482e2081c0d080b10356800c0e80354081074440c1c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192233830 1250 192232580 192232589
    0x414030d0212150f040b0310020f0c1204230111010f150905090a0210110601030f020a0e0f01060809031303050304032f0d03170f040605010911070809040b0a 69
    0x1a400310300d081800c00e1080009400c8018010018000d107011800144c03954850b100107031013240c1e11910004543c0b424489200108014141152101c685400c074902c03c0d400a20400c1043c0240c003560784030704410000307490503102c4007054010b0780e029403480700001da400d01e03202c2410b1281802211902e65024055040c60002404d40841c2102c00c294104400203020b8100c100c443d030a080800c03400d00300003d9103840c041c0d011225060000c5022000b90303407811080d074520005028410000c410711220190355000c4602c2034622411440d900c64607080024010b562840e072000c400801008235030301c1a065260024080c1c4166030ad03000d40a226400c40d504141d00c119941c0d0008a03003001445016051f00310405a41c25200100080e421030103c0c1c00740f20306220344d2060080c900da82040c14842c1c505001080414950325089060605086141c00702c2180c0c1119000d080078000700b505a10340c00346510400000700020309000700350b5a8482a40c000e258041c2d001a5168401c20560350340e100130304001e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192235080 1250 192233830 192233857
    0x21110f040605060a020a0309062c0d0f120e060f160804080a0302010e010c03111e0d0504060906050601050412020105090402191116030206030402011101140702010e070f050108040803041403 83
    0x50809150151085070180d209e0010f014580fa50540c02d0b40303a10348044002c19101103a607010141b12000100811203a00c00a04a125404042d0040056200e41d44074031080c2c07615a0030540307407500c013003080c98450581c00140421040c0040317101000ca1024240e038017071282945d02d040a44030101c0300e14000000d1820307030040c1c0d1030b41d4029540400030f2081a40c0c0d47c08501e014415034400c002590540d01c00d10940c0c1c81c1d0381100340580d6010140c0081618001580d00304280722505041c1400d60291254080c242c43d03003450040424915030051044504580302010000b08115a0350015070301608040401604640c00b0806460a0205402c4c503030220480344d1243e10161000c01a01307850310000950010403219a0b60301400981d8481d002d8036446035092800403c41100c42502d1405448031000030740c5031400754001e2040c400d406400413414a03094600321100c03155150514584c4400c144102030125042501027004500c9800080d54000e001e9207101450800c0701d005036140d44d10a21410244 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192236330 1250 192235080 192235093
    0x106050d15060b032a09010f050c0307020406060c03020d0e1e0d140706020601060903150207050a0b0a0f0b0405010b0a030509030c1b041d1c0207080709020421110f040605060a02 78
    0x645d00c1065401e0a000410404d0400714080006440fa200403180c3c0024000c0c04142c15000c90320070403c507044698050000d1000f01d5450744082c211901c0703e40c0440140c0203070030403000241d124100b002e0748401d0042a2005180d102801eaa540c0381c0e1040041e5080f40c02d107861540403035451030003065812000d4008151041c0f42001c02800c0c4201138114900f0801201c4081002c140c0e00b508148001503010001030b170740e80b01440d0181c40c1c4449001c00400384e000c10406c015820a4642c00740141d4105140203010400300b034001c2100303d0f40240a1880004018445a0a120310036440700c0d501441500c1180e01e0881158042c5203808060480703054000c007584100b03d014180f43c020000c051901031780785000f1031038055400ba225a00e0000c08a0482d0440c05250415031080000000901002042c8c6016585030f0365030001070340c024003441c86011041052400900d000d15118045140c104400d1410b1092080800c840945c0309072045034015210f45011509940c0c00000301001d04564004001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192237580 1250 192236330 192236371
    0x4050c0306010501170103110d061e050a06050a0b07290109110301080604030c02130f09061b050427051609060201050702030a082a13080106050d15060b03 68
    0x1400748160030150420106403103d00700b440640c88001d0640fa44101103022001041005c50790070031408401811450408924074013919142011019046c59482c082c00181da45020183c01d03507070b15109007074110500f030804100c0f45c28084d0260070001d01c52040250740011100d05100100f1141d480b0b0264058011300403c0806018880d902d050390007010401e003150f01d0310107400d80301c500003800681032080e0703800c1100c00c543c1c4600c1d001154a510020030444103804071090b07002440c000408aa03a14a00300503000e01d14021500c01000c4034440e52410f01e803504200303040c040d00021901a12030055501c005004c68000c6004180c0b0400003625805144440ca401c01084c0c584a0381c051015a4945001e20801c00c1e40482155040101c03070a158007261281040d040040c9094014140152242e08101d900302a462000308000011404c20300f00503a246c0d50039500302c510b58800e90707070b0141100c138400002820301070345000310070007228000035400d0381c468181c03500342e104031420383e20b40a460680c440d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192238830 1250 192237580 192237583
    0x120d0507080f21160903110d02030f030c1b030604050d0f0e04180b1302090105060a050409060605031806070206130302030d0f051e0f041b15090311011107030206030a06090504050c03 80
    0xc103104091170613083e018610380710406840c0d240003c05000300c82c0c02c1565019500d08126600d584401c80088036034a1170074400d101d8071805580c41e40a07414030150480929483d0005000d4000c4e40c024015104103852500d0556188290410318018044107800c0130805580310b106400031010f880d410081c0045c0320f0300c0c100c0035034140100351007540c1d5a080030785030250b10b0750120301d815200283c401070355490010f01d050b01c0301d020b55031100c10814140703d0046201d40d40a400b80d03010b0103001702016160620010b149489000807a24280143e001c2d600180301c0c80102c00f54800c4881c001d006407031410200814500c01c4e18401d80d405000745440d50309000c1403c604510554119031009903001032030411012088804101420191030340a290210402c42e0800c440740c407005180e03c503082e20000b035410b20041c10b070401c140710590348000faa0b880b240c0d40307501036003010b02c403582418040e10307880e81960700300f007a145c001078001c40000f036550b800490708200512809004901481c0100040116641010b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192240080 1250 192238830 192238861
    0x10060e060907020d0807080705040305030c07030b070f0806060f0c16140102030c0309040506150703030903031404052d0f0c0a080304050d06020f070818120d0507080f21 74
    0x560840d07018660708411386138800e03500c9410505a180c10702d21619401c100f210140520340015105001c0010101502c500c006030a208607841030300445825031b1907500980d10a545400d8510100c0c1696001900c185484e074010024022507450481c182500707402c4070341ca025080140700180e010b501da001e00c16280e04d107a1504011800341300951500c0b140c8294517440b801614080c42c0910f4444002c182e10b992180b240030b80c811080560180c4642980c2401000740400100c2680800e14082080641110110025204607001401844010040c840c01e603800864002c5039406a001140d59465804e020b2080801000c4414002c00c90a02c000f403c00140f05c074940c1c0000541e500400040007951107003001c0600d90f40e00220010f0310350006406103c0e25100384200148040800280024240564008900c1003881602d11401c0510242e03211540c409200003c030300030031170600c118000202c3e030b4001081c4201520202c142060410741c074506100000340e6641e01a0b80410080004520522996 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192241330 1250 192240080 192240091
    0xc040e0a1805011e0e12210c210f1f050405070c05160f050d1505010306050109050a090b160908060106020d080a060302060909060d0c0807090c050c060a0e10060e0609 73
    0x800051a218030700c55a44d0354402201c840340b00300490804d800e40c02191f00140041c890481d03520403031030b00302d848004a40c42419103081415002041d152145411481507106102828074041d4507103503004581c540480b8401c4400e481481010b01259645860091ba40503a130187c549040c002e5145c54080d00301100a00340b44a5035012450401c0540a09050201140d20546140000501d9410b0204241c001541840c800b00e040200000400035150310540c120707a1b02030010081a294880301d0310a46850b000050141018000403c10100c2551850031900c0e05034100342d1246540d810480c3d081190990180c005a0455000c90341807a8110005513848010440b042054134190b5001035010f00035000c1d190301682e68103001507150f4032005c80d110f11441c1c2007140c581800ea5181000740c3d45113200d020f0098610304066040c5080b500503010f540e00c032403c03000502180e1362100461002401c0ea2401d4a0345881903002000f9004001d214440150880e541a6081c0c0c1c5401c6040c0b15100d42c01612 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192242580 1250 192241330 192241391
    0xb0a0c020a020f060306031213090b100e01121503050105042d030c060e0a140c031b062a0106030303060b07080a272c0c040e0a180501 59
    0x45000698909a40340c0b180f02080720700703903200c0c0c0b24040824508003480880c09100c640000d00d015425415085410840303d0a180078450300d0076010502004194440030320740815100f2403204030380e40c0101903900813103032060400076017540c101190000c212002c2d481601c00fa59144280320602c00000441519540c200803022126004403043c0304036812031003000750401200c80b5507041004641e401c08034941c1800411101460041e06101c400b42c14140303e01c524038400e00420401e1414041400e00081780c2d80d003000c1c044400c021043c0f01940e44218510540c14090b5210300e04074040c02102c04441444c09000001c045065160180c2201c01c950004508801d041c40701e40c00007003080e030842c0c20b07041c901d01c3d041c604032490050311040440e026407848504240fa20001c2850044c0202d182082c0560a500c001c18500e0b00020a15101c015910a94076041c104402e00084405100c8160032100c0c81d079002419000066100c030784010403c2e002c0350945d465940c408502a507142c1c030807118204049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192243830 1250 192242580 192242593
    0x60f130504021c0e0c0406260f0309010c061404150e0a1203020a0c0213140f01050303070b0405031c0507020d0e031e0312010f05030d0203040605030403081f030b0a0c02 74
    0x5030210ba240314160710786034a041d200d00c43c44c2284d240a0082c40300c140b00c06030040c405c0c1d584804032050300e207000e58420060031000f6184107100c07101c00200c04281000c20340c05940b5262080d001140e000e041d15a00391040c5031078640810440010008040c4140c3c003da24203030b40c0030a034201c0312040d904250b07901c1d6120b911801c3c2240120b44030001845503500941401603071800108025a8286042000a54400550089242903500c207070040000511002c441c0c4d1219512000f205000075001c4c000d568140d0320034408c500006030210316481d00907010301d040b03a0800410010100d00c20964100d91030503151568117000c0d110340c0403c00604554804e04010801c412036002207a518401b90701016404100d02e007860010300300a2085038951080b5280107906507031541c02d81c500846c1d003407203500c0c000e10940d00c1c2000342510100540d000e0b1007080d590645117488544045480e804083d040c84900c45441860440d40142070311088000c51040d0700350405c9151182d000c1084480043e4448107641200c1e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192245080 1250 192243830 192243847
    0x9230405030a05031314031b0109210516030306050a050919020a0306030605040501020c06070f0c08030c0c1c1b0b010e070e101106060103090305180f060f13050402 72
    0x100a03280301e82c4a40c0351842c0c4a980e091003503104194400c0b00608440e0902c0d58565080801200070618a6040d000d0000f0560814130711a080300d0407007001404200300c40c46040001c600b4074800e8180000240341107414200c84400c1c490516003d81d00442c0480d50741c000400071030909611030b00003804120340b81d11203440c0c19151302d4110103c2448000055038001000180e0034002d070b0228010307641040c003c124a10713140c41c0a5000750712032904848a8800c120004034a00d20546200d10508960399810109111903510150142c0000d090700c4042c1c9070610560080b01400c00c5020142007141e04460806941c404004c0d0120302030040c0c0b12800c00c03408002801280c0e000048904648240041e05596070303e0900032030341160b00703501c80356004400c842c0c074401141c3d110341c4101a083c403090940301075855070710042d41210007524004022490500200c090031004c1103107900c07603070000341c8100c100f0401340001440603403010f51140e4014501081c403502d000d105c04400c0c0e007d17001c10f480852420655 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192246330 1250 192245080 192245083
    0x140c090f01061d0105040b0403033903080a091a070f0906050a050c12070b0411100c0b13060e150901020f040b0307030e0304230a24020f0709230405 65
    0x40d00341c00310103490f1070304980f41030f034420390466005011580b00c454965459240042c403104442e50380c41d200d0380940940c1140000c01064542d0321400143d040404a4079690b410340b07910000030840d01d1401d6503001c218012403586c104800440c02013850036a80e610b84a07201030300704030101c40007030100704401e50309100c01038002d81100d140c4109401c4c90b644a4003501255485e05410300402d06107450b0100d0108100010039407564010b0b442205845584a421824882d40041c04900407000420102580e00800c2c90014125044241034003046900341403510340d0401c2d0385030041283c2c001d52181d403034850f91090141140d6009a03180c8025407504107400e04000a5001d540118042d40030f0010205011034000e60002504d0345110341501d840e580e864400c04c4141c4055141d0781c8038442c951a0061083c80d05600801c1a1407a0800c101c1c8510741c2c240e00900445941a0713280d06501c2020f090808100c001c0118000400e4500000f08100e03e01c03610b00c803108202c0301d400c4a00310102c2810b01000500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192247580 1250 192246330 192246347
    0x206070f080a09140106140109060c0312020f07020306090304080d050c1c02101104030b1e0a0f020d02160c05090f0118020409020705010f0b0a0803070605090109140c090f0106 77
    0x411410200d02006182414002e1100c45203002444d5807a011000a0030000f01c828040180e41c241c803045111582c561701640c2c043c00140c8014006581c150305141e03041ea4036809000f0174064008104d0400d007035640803a00e425000c3e038055146e5070010500f00103142d01008980c10b00311031464414100603503501120350f41d681e040803261640000c3c030007116031503100700001c402241c00c00300284080284118000a5a03009000650340a0040b0700002c1070298502c602c1d03121000c2c1d04c2c070041e040c3d81d12030990200030f018513100408056001c00408540d00e2082c000f0784110044680201c6418a0a28048001c184075500560195070080d0804c061a8520b44209045600c00118040001e0141201400a1249030014100c16101260440074000e0550224a1902c042c03201000444480010003001154070303c2001c1c20340c0d004000c070f440040e8007070700a9904000d0740800451000c000f80d0b03e075545081001400d00580c0d02c150343e2641c05141c990206a082103410b8181251541481d100030403036803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192248830 1250 192247580 192247591
    0x1b01050108070311040209120d03020301091409030d1509140612150726010905070806041a2b080319090209011205070305030408030a0909051006110109061109010206070f08 76
    0x55000c502c8104503158102103030740710000007056901da49c2c8001d40c0603000790007c0c015040410f2812121a013086a00c200407401016088015404d000036580c055003d40740c50030b030407400101c120600241c181c01718001c0c007000300e03502c0c0144c0d500313494050b050100c0035601d0022051680d0090301d80861861144211540200c0c2c5450900340011200c009010301d0302c801c028408000c02c1d5080001241400f45e404107004500382ea81c0d04145444100400041d1003c07945142060007411030501d100c1e01d00341c00070701464150004580c0b850141100f58412161304200b055481382c90000820140e40180300b000800c208800c0b4042241c4c40345a0081a4412814003032181c16007040a002024010100300550046034004c0844c2d81e00e030384030ba000741d8076074110754110303004036081407000724020040e07011f15407207090020090000c0c01d1600d4000c888200c0311060030300f2155070310000d41010a03a60f01803182c1040b90344141545d600a850b000a1604000038415000c11540c140001a0254441c07030158000307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192250080 1250 192248830 192248839
    0x50d08070507030b040c0602160501020d05090d050f060f011706130602070b0411010e010804080d020a1e0509010e09060306041203022502010206010f0e160507081b01050108070311 79
    0xc8505160031464981c05402c06050003e00030108070801c010f4400c2d4400ba90082d6007039515450150f81940c4401016004150141e0020124020309a115001412141a00500958800000d0303100c1c1803d0102d40e0b040c00d02180c000ea02086183d00c210010b02e4014242608065400303000070074520b0711604003620140b810580244540144007041d01500c40b41a0000d07040805030400f890302e032001c203650494203400f0407d182d070780016079030007113000c20b1003140c00402c0c0c0c030f20341000d400c0c19000943c0100c91940a105989080714800c160040c2252580c0310f45488550380c403500c01002400d0210404e81c024171803061a8100851a200460744540055201c400746100c00300c1c0035000c1e000383c01495005008840034100c1c1d0b40380d41c00e100703020b80b0300300703000b0b0b0280c48040e40c135002c908070248030030b00450000c1c61082010900000301c0b40b41d519407080d954a041828441c032903035010748036400114111001446454070702d409007028800c03240100404002840a40d280d5a217121a10464500503440f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192251330 1250 192250080 192250087
    0x50702010c03170a15121a0709080709020c1905030a0f05091509040509060f0c0901020106091103060f030f0c13060503030c0f100603031b050708011d0105090601050d08 74
    0x301800b46142ca1003c40e0a01c0d02080c05103498410034005051000c09052114038109000600380700b003e51030860a03030056400c041c2d01c2c00305065507004050142c000360802400400c001060b01c2c0a10200300584845400940c1d1040038009192603c2d208030400d46107183e519034400c0020b82c0000480e0040855420144543c4080590642d007900a10000c2908090210f40036032000100d00001e001403001250200102d44401600385c1da80c8004561140d101110080030070f84800d11503000d040000c00503c008030b409a1228100401c1c0c956a0052200c120004401d10184d464004c00c02144200e0540081030b90007103100710a0755a0540d0040c0a014455050250075100c0260304840040c001c0582143d81d10804a20448d40d1075056140083c0d0321b00441c10f8044114005003e2081100d40564a4101030381c012100c0240e000c52015089603a4031414800003601d04080c0140c0e24407004030005d000b440394480e44030b131f030954000610700d445a8002c1401030000340d0b100340b916491607811050703160300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192252580 1250 192251330 192251333
    0x140916030510050301060902041802071a0c0c0109060501080d18050f041401030f0b151807050c0106060807180e010603020f0c250603050403120c030b0612011a0307050702010c 77
    0x21400e2600a544c055007800c002040701e0600e034000303100300c407400000400c8a5555540703001c120301030114001c008520b440341c503003440041d4130700060b00300202c101024078000808101900f119080502140c0c03286d200e400420201c2e505100840e2218001d0504040182c1001b803c81d510700e4042c0202071052800d54230740e00540d100da900c07041c0c0004d110108520300d5612810f11003064050040c041b5203812880e400102c1c41d061090320176200041c080d09042c0f0f409410543c43c1e4000303000904481c10410103004005a1040034041d0b40010503480e1900c0906040102c001014181e95007040300321411121010044070b0380c056200e03811200c85107401600e035602d04808140c184100800d8a880d445161035105209618500c1c44014043c1031252102140d60b401e400d6003903d8085078098045000e64044200d448040e40040d004000c2d54a4005508101d00d8006001a00100036100d000054800180100000d0900158020b49000365017400c510380104001c1051080303020003410000f03805003000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192253830 1250 192252580 192252601
    0x10516081b0d020306100c0503030708070c080a0c1104020a1b06090507060216061b03031a03010207030c05070e061011071203020a06150f0306111209071409160305 72
    0x1c000c03042038800740b580c2e00c2000c0c86510194000751449032242c071aa148026205020b1241d80c0d010030b40c844051400d56894503019965848005c204505000d038182180000848510040140000607101c211214003f8185001c0910344c030076000d4081c0d80f040041c42884c3d038009442d001848941040f00f5140016480c1c100040c020310707400101b807842421008a0b400d500440c4481c01d880480c1900c0d842580d5407402210070410b40c0418a442281100030240428801c0d00004141540700501d000d405400700c01203402ca0380414001d500203900249140d01300300f07051210b4401444050248100340c180390300059440d501d500c6191091002c049845002180d051100c1c000a000000c0380210049441c10f010303454042d020382c1180d1813440d003001840d044603001c5884043c1c81c14611104c07442403c65a442009248506a207541514248010b03511480038001c0e20707104500003406044071038070f002c50b1185215a401012440b402d000c100b0080c0350070301c1401e40250756149140c081b4940d210740c03030b000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192255080 1250 192253830 192253861
    0x3040602090a0602070e07090b0307260a0f06081b0d030314040c030212010c09170708030a1e02070803180d02030a060204060e01020a05030901030e03040e01080d1101051608 76
    0x2540c02c81c2001000051264011402804a03054400003d21a0f904c41c1d4088030501039501500d11214828000300e40d85034402c00950050f08407401003144419004c5c428540d0460088800084180e1104244000c201c45800b07500c3c02052800c00914451030b074510040078031100000034500542c0c400018400b8917120341c000600a81101d1840d00c1581401d0401c0c8203c0d0000d4041a4081c101020384032064100c14860311103095800c0d070b580000d290404500b000c440c0c0c0d0812000105100d000d001292001c002d000038502e00104e5120700070030751409900f0680e020884a202d1082d90005502000240404000c5981c4402d110300d116045880b14030020704a1060440003035013510911001200300003180e401807080d6285a1254102a0031031001213070350b81001c450081240d04140320790070a035402500850810882241528103003501d03403210b5410300700260302043d510303030103081012030050b00070103200e01d50f0000c00020701042c41c211020101c04120410140104070110303001803400000c3d440203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192256330 1250 192255080 192255097
    0x1170304211506030602030f060d020a0501050d020715020307170106050702010c0f05150405100606140c031b0102070b2212050c010f0b1801050a09020a02070506070302030304050c010905060f03040602 88
    0x4012003611390801000a410846007060fa8007034080104409107000210b2500c0161b008064062140c2030400444c0c1c2500001041c0140c190240b0400c00014407401d1a111a41c2c2204c0c0010380340d262025006081840110504448901000042c0079666000c4116203072140c0a003400d540c45840e510f0302c0310303ca030070000000d0020f01407008103c200e1070040080c00d028030b01034011503000c01d140d4210b0604480061141e8008515000500c03010107514801611800c950501920b0a2a440300c0450309841035400310312020343d40c0050711108110b032503584541c02203aa00d550808105408800204051003040c000e092501281c0940310f01504c214116034401c1c000f03078020300524841d00d80240c05850b0030760b03080e4440c10380135141c003030420401e0350118102e9800400a078201803614015600941c011004402107004046d00410191910340081c07028600c0b9500456403880c0506095051100168a0303d04121030410100296942e042c143c80d50b80909102c1c035560381e01c0e00d00c0c0c060028801d1160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192257580 1250 192256330 192256373
    0x3081b0709140f010e07020c040b060c0d090e0702150105040209150a17151c140601031a0603010e07050f01020c0d08130801020f070b1503060a02030117030421 70
    0x3001c600b40021100300300d0007000c40e020058016600c5229014440804803900340050b401603030040e91600c0c0c50780103101c644102501281c5003142075031106040c41c0000d01c0090101d040d4410800800103101c90441e48007e2a1020f0410443c1414482041e42d0341886541c0c4159000325001c045552084448400000b250001c5a6528590b443c0a0859291001180150603502d400502c2e140c80451008805d090000c110002d403100000000e032402c04081c1301611a00c0c1c101d41503c0c10080c0801095000e14012500c00f000010030b41d07408110400010000c3d23000e641040d00c802c0c101600020010305540c0225070240110040500407850082c0311094030b41d0048409000c40107002c0044001d040841c0040c80940c7c890f900c0d43e20150a038451408001e80b0300c041000800b000c80e612122098010304428a22007420001200180c60b00038180c070320400d0349500000400c0815000034141902c1c0084c440a11308051601d1070410b040c549144d1100880c5103452030721010001b5a20000c00b04149000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192258830 1250 192257580 192257591
    0x3030d15090c0305010b0a180312032a09030b18010204150810061b0311060f0a060f05090a0e03040b040e1e06030a231510050a03081b0709 61
    0x40c103081500c0c10034465088500d182a1080d00a188640207260685020342a003d00d0040c9090f4200c4005a0381c40565600401c0d42da808000100112100316207500395035000b0407021680d10b100710000340302035841481480c40741ea50036565a0400b040c2000c072508130600700700d940c2c1c910f0204d0420040c01403901d012548001000b282c3c1c05880e412a2800503110b03614401644d40d4030aa0741462110340c0a0f0ba40482d4400c0310780d5140071622400e08049510a1a004407600d42221501d403600c00280d0350034901c45a20800c202599200703101e050010203081143c074212602c2c0c140404c1c50032101401c4110b407151500f210400c002c01c10002c68009014000c11507030780d9540d8a203045000701d01543c2801a681e4480e00600c4416080805140118002000741210b08100e0ba18044040b0010942140c15071030003440803500c0c1c1003804480c440c0c4c043d40a1000c40c40ca44241066074030a800e4101d41d200d08000f201c28808a80c240c41a00c0344900200d10500040d074070000780c50b2506919521110282d0b0420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192260080 1250 192258830 192258851
    0x230f0a080f0618150a0207050a080a03090b0a200d0603020604080a03030506010201020310060e011709010605040e15061e0a03080c060a06050618041e1d0c150903030d 73
    0x19010300c6081511440f082844044443d42d4480b11a00076000c403d600b50000301c3d4000361203a00600c103462143c1d048030032403080c40c3d0301e880c1c054002a0307910001c07944d55900c450074803050095541e44240511000c22409081e801e84040c000c00110308028901008909150030000319400300000d55002400c658030383e99103070343c002e41e80c004a000460001c2e0503d004282c10b54014026240030f03503800c0d280410f100e81003a00444240034400d90403410442c610014203050034581d180680100a45000802d0042c106401c0c001507a440341e44090150744146103884007004c0090213103030007080c200c0300c41c103c5814400c1d01001441400d401c640d80130420420010801150b000100354100007003090f0340f19507543c85032031011201907102d01a0441d0080001c01003c0205840003564284001d0000590f00d030755003980318603604070030900300040340d4070504c1074115661041241240e446071001403001c040c2c024046103844080140c00d800d44d0901184101705640c0034000d031002070f00e2810b030420168180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192261330 1250 192260080 192260083
    0x1905011d06190e060712150f0f06090e040f03110319030e0f0601150207080109050f0705060c100c031b0f080a0908090d0f020306040c03020a230f0a080f 67
    0x1d845110a2410712200310108806030702562400600f0700003e080b4658902c0800d079121080c0900c20b8403081c0c0c2d0380001440741304002d07145402901611251010603424541d048141200c17941105040c440108030802c40d0819800500b40d1081d80003010310f204a00ca840e080e1000380590100302104d000c013054000c00180c8003000005400c000795401d1140212071000f880c1c961038111404000d9401c21300051060203000714555021b15035620464542d1030356480352a0848a8115084034503801820625070307604001c102501c0500400c4520514084010509a544464828518000f507447d50380250b1424041d500800f14030001c580070440350203c0c820010450f110206010010480d80c40c04a000c8800511404240a03070144140d440d141d548410003020320000e66040f50029220504c0d5001610b05000c21809503218403001d1850310700358410003041e11401e401103001890a10800c0901c45c00d626228241c0c0d04068402c10031400c140c2000c1214910707603402c160804e2081c9446110300110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192262580 1250 192261330 192261343
    0x1302120411030606040603080a030b031608150f130605040305040504110d0e030a0509010e031c02100b010f0923190303120603050c060d02120c0306010f0305091905011d 74
    0xb102600c031035944410800044074064040500302507824008030b450603000340e10281050b4801400c4800312a01034441040c81c520316004295035800c0603c0c4004038603081e60605420810000000d8054070f49800e0313915109001c21005442d080c0c40e00082018907024004980103404090401d1020007034140820b05c0c140c1c400d0f074940300c840e45009055190020f006c01a526110050780d141ca00d0b05600b02c004603888001c5101480d41030184c1d1500d981d10100400e88841e1101e40764020b4441800c8103141003049030b80007407640c1d0520800d801d00c55903203540222542c054804c03c941c1080103010386007000803144605592281c000c10020400141b05080244040c201c91099032460211910980400c050b41c283c0d02c0b00500c0b69000c0e2200340300914184010745030700009080010706201a00d0410300c80c12030b0503201d10345e070021300000344010741d41e00c8200d1041181c0c4a003400d00c03c0b8240158200d540d003c126560030201d2240e089800c0c1080b20a400180481c803050f4003000c04114800e01440d107408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192263830 1250 192262580 192262613
    0x1e0804060806091005130f1805070b040501081909021005030613110301090929040c05030a05120f130b04060e0a0e0402010507081b070305060a060e01030213021204 72
    0x5100703000040d5646032003444284181d210300c0000003003510b004140302061001c000081d09468540702030805c00f06a83c030070a0549824064042d841c10f84074144141481200d80104141145c20071081c011a60450075a0345c00142c07264010030301d5070301c8641010050107800c034000c0d030001d0000d0160002c280d000c0060342c060101110a1400007c4001c3c850045949220b1480781a040c140b0042040ca4581d502054070540074528912a40c400102d0340440c00c4681001490141903000510040c84540702d251809400d0503001061200c070f194a41a6407240321b4024001c2007100090410040c00010f019190006e4030382200000322034513039900c041241c01502503500001e03860540104c10b4500380e40b44100b2034581c0300049003036071100e03001154207901080003960500c0c003c00668401000800b20702c43c914500b80040c0041a0840c41c080d0b080c00008bc000030420707818007105110004400b01c820341108d50440d800e01c0340424903200355010b40554601200b01c6030440041009100c0115a90321009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192265080 1250 192263830 192263837
    0x150d03080a1116060b060f03040c090b0d02090402121c0306090c0203160b04020402070f24151202030a06050c04090c030c05030f042d05060109091e1e080406 69
    0x50000d00a00ca40394043c110001422644031850000490f509a10a000707180024114034034050305400c0100c501c3d48169803c03680111a0b550400c5200031501c82c00601d4030b000c440c1205044141d40004e6031601020380042d01c181a4400c14020300b11040000100e290208800b0f40310018080c00084d005080505c2884803581c207101c1c03405940c601c04030458580010500d200101810076840d1460203080c01030041760095030802500e400308a4010b600b80302e151013910880140190190b20114161441e000311072030904000c5002065920800d489050701c043c0a5a9460340c80140002440d04451620151410b4608414019820140001030082d0742548209010a100205049046480c0010068001201400414801c94040c0b400d207400500940104a9900000382038840f0788404101c1000500c404c042c501c010001c05209160041010090402200c10a41c0328020b00100c061000381801c0f404070701c09410001645800040e080c80e04000c0325400000e0310300024603034400c6c050380020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192266187 1107 192265080 192265091
    0x601031407030f0f030e010c0210050f070c1e0b191b02040e060105270103030c0507120305120c090a0902090609030a0b1e04110603150d03080a 63
    0x403e070b0040c2980b9003404082c2c80c01a2541d5007070f9000070f050103162102c030030140e502d801850031144200d05180d0b41d1120091010b0b0007070310a44100a210207080e04011541480c101c50211034560143c0c00011400e468910202440c06060015607120302580d41c04c43c0348901c9000042441c031544005100c500c540d542c009401e40d44d84040301070160340004c004100a25002c585450070f01c00201c1d001060351040c4418035010001400301501303001d00c021040c4100b00d810080340d0002e01c0540e0501854024902e801420341e032005d040401110000c0c40898808070320101160001200203003070310302c4c482c9040c45c0040a03400c00a0300941c4081700384442c20007a14103029844c0c11601c107258410b280d21700078403000c407030034840b100103034a41100904000c001020000c07d44181c900440303140703071696105481c00e0842041300c040b498001d20414100c13001c1580005490340949101c0106000 = true := by decide +kernel

theorem cover : BRFrame.Cov 192086330 192266187 := by
  have h0 := BRFrame.cov_init 192086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 192086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 192086330 ≤ n) (h2 : n < 192266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
