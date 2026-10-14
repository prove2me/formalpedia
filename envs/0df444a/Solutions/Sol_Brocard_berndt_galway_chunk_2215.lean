-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2215
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:51.91195+00:00
-- url     : https://prove2.me/submissions/ad20afbf-e5ba-4e1e-ab91-01f584af7d87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398201438 ≤ n < 398381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398202688 1250 398201438 398201497
    0x3020111030a0207032705120a0b0a02070b0a110d0e100e0d20070608040c08060703050a0e0c030601060806150d0501080d0512010b090a03060e061f0602030906 70
    0x50380c400c42043c2e808200e22003010b0304907884450801501400240302c01522460380e4503c007040c01039038012601d42c0d10203c0c90703540410001c0f4000e580205808080e19102c10711030000d400584042d80d0384c1d04c945c0041408020b40b4803d01c509442400105441e1240740c4c0c0c240c0010385581d00d1415410b00c1102e41100c2491058844c009410b230100e0041c101c00c1c110000010411400358190140c50000d122001503065000101301080710454280942565280e0070108041e0764a6401a11240600b10400c4035860345a44118070490003418104591220300c42001e0b5a0580b030720885816500c61401406030030300508071198000402402c050546c0700d81003489040342c0080d0100040581c80d80e0041c007206405002ca080000d0a51070705d03600f0418000e4411080bc071042c480c0140c644400106500707a5222080ca00000d035410541c18840d0030030b2280c0d41c541e070300d104036110b142040da1114020b00000b40d02080100311074180d401942030552407000c00015500c90b0001c5900b0703039400c01e50100895203d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398203938 1250 398202688 398202691
    0x614031b1b0c121207060f090813030c17100e0c0d03030b120f030d0c14070821010530071806080c1309020a080106090204090605030a0f0f0302011103 66
    0x3201c0500399800004050001154840c5010310194001c07041c0c0b050784c1100d103000d40d41e9242e004900407030b0200c480540c01004100084e0043c2a100c000614820340d0260780a9803030840744501c0300008030a079529107020384d102075a201c80096400c0f8407510200741d03000b80c00007650241090252050030b2408400503248000c1d000c011808070341c58a00c00380c0140307003103205a681d55a02c80003034040202601d041c26242d1045a401c9480c85a03580300c01e6020b68802c000300c00311840fa014516071b4030402401d0032501504001b00701c3d448441038101c446410b40140100da81229805010703003901d480380c0c3d00d03840010035030203803408514940d0101044d020b003030400c18a00180703000b19410b2401d40304038000d003003a81c40c540c010052a5200755003c0010b91220300d000280b5a030580d8001810310080c3c07001504801c60344e8040324456003840004200350b00e96900074070441309505420440c8554070414140c556494040240140c25000d800c5070200f28580c0032042c060b03100e48000a041d02480c030361800c05810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398205188 1250 398203938 398203987
    0x40c0216080114011d010314030909150907030902031002070f0204020403030e030610120201050a02010e011b02010b0301091527030c0201030e0114060402130801091101090614031b 79
    0x111503e410b10f5040c0640111805002d00c0c260118460840c1c4448a45114041c0303c02008130844000003025910140b060300c20f000710086c140801400e008281c1010400c2d1040c000e40318900d141d001c600c81e039009101e03850b880340d800b601608206513501060402174205030825901d00484800d50b4005a98905c002e001075071280d1289044480f000003850700d0071b070000300324098100900b0303800d0100c45407a1000104090382403070116911410441c00724050030003240c40d104250700340341c40680741803a00d441ca90b00d524490741c000c0048a00d1b17a8205030030394540d16000341a0b202d00101034001607845030000b6036403071050051303503d01007a440300d101003c1d11400410f40004030115400421907034140181c01c40f0520400c02804900c2102440c0c07001001c2c003400c113a00c95070340052103809000110328884001c12038000200490940750604900d48840d00481c0360000c0c0718a00c01180c030b1070283c42241058030302041e0035410740e510450178100503090049200710ba10300600c9000840003134a00c01d80c15414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398206438 1250 398205188 398205191
    0x5370902160501060b0f0f0a030f0f0b121f05070c02150414060f0901080405072d06080708011202011e1e030507050a0503062403040506060a0f05040c02160801 70
    0x7260400320708441c0145c1000050003001c0001201c4200d141040e941900300c2c0e070500c01c2d962401c0c14801d400620422840600660a1943c0789000c2e0303000c0d0780121016134041da01500840003004080380c076070701445150100d071191505041e40c1c1076402da0140798800942d042c9001228042d07000101411420420ba10300030030000b40500c02c4001086c803001e042ea40584880b810319014005102e55802001480340c1041014030005050103c104007003030040601500300003100902c4412982004500b80c1e000c14030407602d01001a0051007010302500c00c0d9144c2c0d4846c0d580364281001042c8174084a90182d041024054074248207003205000c812014003180ca4003c5aa149120f500300040c61411110040c0341c601420400460780040c1100c070710500320328000359a84d81d81e00c0061850b40c1344010782c0484942c0f448108801c1a1070b8001107004a0103403040703803001d82c0c50108000c164801805264107050385408100900d050540210141da41e2500640b8078095071185882c2c0b640e585a480190710740e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398207688 1250 398206438 398206477
    0x102310302090f090d091503050a090606122a05011b0b07030504030f1e0c05150a1508060105030c060d0209040c270b03040f03020304120302060f0105370902 69
    0x400301005500c5c0c078100c03c0d06004035401c1c0307000034031807640003d00c0c40c0b041416201d00000d03800072040d606c41089594000750801080b03890741800a00980743d400b00315210360031002d0f54100c00c9424900d00022030800b16500d00c0e02800c0c20011204030345a02044070840704501c402c0c00024101c00e04480c865200d60380c0000d441c1c0707041e01b0010002d00100003d801480003000381010034440703050580794550503504003103d200c40180303025441c11001a065071901d40c80c21040c8880011180c206613025a8030403500d408003500c0e602400c0d1642800e21590343c2c5544100012034150901d10007410318140b0030040181403885070008902a01d80c2c01c0300071800036000140c969211815001a41902401d1003101e21515080c4904800184405003002d8071a0b00c1c6c0080c0d01080502c01c004950207866040c0c142541d001151402a64a0728143c4141599040c0b40d40045401d08066050041c03d548030400d84440703d0030b26103001c101075a21100c08800780c00c400ca011030515043d000074030526402c0307080940003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398208938 1250 398207688 398207701
    0x4030303050f070f170702030d050c0406201902061b0a02130b03030d09020d1203050f0a090503090d14030f0d06080304030c09020d060e0c0c0c030102310302090f 71
    0xc0c102c0040100040c420910109440310758800c1008444c4668010a02c40680f20081d060b0301d0350095804a80c1c0403410b0504100b8844c03044d40180040300c07007a4481a1002265100c21205200740c2079550fa00755202c2d01440103210002d0705010b040c6400a084180b41070204814034203000300c441c0750500c0e1030f44002e0b840b80031802c2407141c1c1103001042040411115603a900029282d00c2544084030240da25281e503c03056654991902008a41c089610303111a4058080680907000c04c6400c0c44032017a4031000038482c0c10080c0100c840e100c0d8004013441c0340c90440410401b0101003400140c81000e801e503681c1a090100f00001c4c518000704050300e540b184ca00020704401e45505403c00f1100f6001880204000348261324803000b81d64025101589649103076414500800e81d0380c0c80101250508010310292038084c0000389698905c41065600d245100b9045c5420b030f00c80c070a229844040c4080d802021240d202c62958100f2144031a41c4844690fa0303000a040c91000303840800e101d103140004d2025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398210188 1250 398208938 398208961
    0x13120201080c1312080408071712180103150b0c01020903012306012a03120b09070813020103020408030a05121008070b0c1006060518011706060c0a080403030305 71
    0x24442c106204040c41c0010404000c95410030341c0c41410141101801c00c00c0400c040602510054a815400c0700d03545541c4242c100e03d0400c650024902502982a112040c52800401c885031100e0740c10b00c2d540e55001400044005001c404090b00d000201e1503070103d5681d000318000c0442070b90f40000942c0b00c078901e1040500710b0f8045400420074511924035800384c180100326181d4048424200341c01031080c1021001540b0107508020801c40090001d41010144c00007001c940c1211000c0c0d08000701183c0d0400d1160603401034400301d001c0b446402c0024114070054002d41c21051040c94094201035035918441d256811800c0c800000c07a02c0410f00100f6440d48a54065000ca550034920780c9551a080141c4d441e8140e5010740e8015400002e45240b003000200010700a004001d1810811265540310060240e0084100481540080c080b0020551321030745100854814040e001d07030082d1120340c10001942d1010414079442d004e508014400305514101910041d406920082160700d0034441901 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398211438 1250 398210188 398210191
    0x7021306050a12020906091f080a140118020411090310020304121d010302070201030e030c06150406061710120b0708070503160806030c040c02010b0a210b0c1312020108 74
    0x1031007510f5042e8290150713031820703900b40c0c100e10203542074190340c1c5640d800c00819401c020081e03001c90b07906a200083c0030f1000524032a855000320001c0c0b1440b5105440e20342a0b4507801c5021b41c10b944c41c05c01b4800036240c0703603010351010303a1171410f01c4d4075001286021900f0804441c945604c01c40e4044100014000c8825260b600ca11184c548001d0394865203048041e4040781406036410581e02098480840e4040d0f4043c0c10520a0300b811262512940c001c1143d03a01401c44400740400c41700070f0440000e00300f0303025101c143d80c3c0a0320742048505502c03d000111420082000e01101c820490028141c1201c6180a0025015000307940d0035103401d00d4080c000400180840007048800c0040001902420003000c0c0f045001d490118083c1d19540c00081c44c05081c140d1003a0311500d490a481c0e01c05405500c0562000001d0360000d0f60300d96500303241d40c0350f960100414070025007014420380000d0b844d104a00e60100c181c103a0300d410040101203081d900d031010b0304003004041002d003402c0705641c0c2000310716 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398212688 1250 398211438 398211449
    0x50c0f0601090b09010308030a020903120417100c0509150d0203010b07030206100b03010e040c0504020c030403021f050f0c0f010906020309010f051015020109050a05011509020708030c03060607021306050a 90
    0x8505506d1542d0b04080e51000411000103594003080480040d03905003d0b20310f040c4500100700b03450326161707107104200401c82c04c00010325214200c0503201e171040f03e0142d03c00050b1a5100c00d4184104e81d801e00c880c54400025000349800204040075911251f0320145018040c07211810f5260560342c41c000c0d140c5040980980088040300204011841c0b80c00103c074103407a00044010000c0c0c0355460808400c080781e07048641d01a0000c5510f01c203404002002c0d10840740211001460742d248001d03200312050302a507080001502c01c2100400340501c14000b4425105054201c4220401e1051407500712640c0e110304584103500001489482e180c02d0050724400303280e580d070800c228145191401802110381c4990030409031048800315a4030300030b600040180d9040401d0711020741c0e1764a8014020440c00b0340344840707002c03680d8001c5a0484a44250307002107074087d0809145031103c00100300c25400044c11140d10034020894040141c8454403c450156110100810364506141c1004088031b041d4115 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398213938 1250 398212688 398212699
    0x90d121412130501090209040308152d0a0803030a150e09070e061c12080c481b1008010902030a110712031b0c12050c0f0601090b 57
    0x15404400203021029000715202c1e120300c0d40c400041c6000b80c01350082c400c000c2c0d800351015003000309050b00052543d1150344080318401e03030b12011404001030b403030300c0b421086021070300940d000741c500d095411001036a80780140002e99181c1e841a695107036500403516031103015181c51000200000702c1c000f800c09400030400302c5006203000c58440b5a281203e00c518405011880041138881c1c40d041e0400d07101d08000e00c05881203401c3c0d420b1003850380044a00c081c000409a20005c1c5503103100200ba20240a00400d510803904003c14000c00021580400301e800f06591900a2110303c1c4240c01c08220f00300c0c0200a0407a00e0804034046542c108142c034034a000b031022141c0c0c0540d540d401000c0d5815111052801603c03500c1d215800d0008001d45402200042d00c0001c1e120144941821406172440c02994103100c00c0e01d00c01c102080d0340d035105240c03070046504c2001c42030008001000001d420f01161a099040000c041e44081ca00382420510009907080000184580710041c054811100f070140d50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398215188 1250 398213938 398213947
    0x70c1205060a0504060204050310090c05060429040504020c0a120e010c0311030904090c151803120c2a1203051207050f0703080a140103050601060309050102090d1214 73
    0x240c00c0d031108802802c5106a40c0e0710400038040060581c1510041e11026086481062382510303107a0090021010690707001c5d090940008652901c8400ca400382e400c0c0e04814542c2a5020014800c0c1d09500b404084403841c09000120340e07511389d4405420303281d604070020000c1c641103060034460450250000b10402805156030401c0340d070051a2090100e13070500d0461070350309031a0070107400d43c040c903001550f0040c00c00c1c4403c018000c49102030b0055a0351030058002c003042210040ea010200e2400a074102d107030b00c0d041080030075540101c05428050b58203200c0d038091000c5c0d4810004021010701010794a0311901c6020310b022807031801401810030b03c141240003000f0350710044c092380146107c1400b0b100ba103070300160350380c1d21410a8925108003044c140307031a400e5038074006e843c503141110000f003607902e84500d1500c0c0400303001c0d449048940020160210740d003092421000f8203d42c01d004d13180c5640802101d4400c3e200c00c0820b003002c0340908405652400d03c404000c1c09641040b81c0900050380510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398216438 1250 398215188 398215193
    0xe040f05330f0d052409010519090213060b041502030f190210050f060153040b06031606080601050d0e030a020706091a1c090b01030503070c12 63
    0x250008594400b01d803442c0046485000052802100010062040c020a540208103070a099031268506418114091041d42e0b01428242200e80844e60303090003074207150081e01032a0b44e03507108161090028291000e0006800080c4095031400d030700000c454440000c04106507106c091510b894030000e407010310300e465041e4900312140c1c000c40110312807503060503480c0700145008000d6050645190b003000d10262800ea018210003240849906012030540000c518601441580044107000214001001a086840740d40030042080c0e54011958001c0103441c1c06800400c01118800ca1043c001c0c001a8034040003410300745504d50307850b40c0d00664180b009104007a0404086030f4010000e180c040c0c0c5490121040e000508840030360f01406000c00226800c2c100c3d8003169400a903012a111540b03042e55400760100d00048035285403030040410b04c80074684507134107031100300224481c4402140d0b4114a0b102c1c01c494810a078030468085d40300045840812480704007200003002c0030b0200c1611900c154 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398217688 1250 398216438 398216521
    0x315040e1225050a060f0b01090501080f100b04030c08011107050304171207030320030709061409100c0308010e01050d030302091224091b010f0e040f05 67
    0x101c4044000c82d8a5141c0400401007524040c8440d030030030300721400407550f07007044401803140c0350120440e1410040042441d50280d202c510459806a5500002d56500e4500e91072007500074001c42d988030907074540040c0d84040440600301031401041045406441c1c00302c2c0c3d41c2100e200b0381c10440118414045400801c0780402238408413200c2c2c000d01c000c941120142c10781010001d01c030582c843c1c18003013600c80034194035078059941c40c0f14088030400180ca00200d4041a030104455903c0040c3c904002407250310310801e4524550100c090483d401e2082200001e905103072611202130009150344c005800f40751340110301c10700410212203030040ba0b5041a02092034078002e0200a001c3c1900024030746500c4c1c44591255000c0000c080a40740a40310122003200c0342100202c5801c04550f10101140d0502c1c00424681151b00544c1010b50041c4030303000c01507854228003d260b905015000d42c0c00c0c081619640100c44500c1000f020001c1d06140045062040714032181030f07a048003000140c00c20b061480c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398218938 1250 398217688 398217697
    0xb060a0f031a0a0506070c030204021207110615361b0a140f2b0c11211308010b1315050f03010204030212030705070e0f04020d030e03030315040e12 65
    0x26119179503030b5002401e240800b1007003588020b401901c0010840031401d61110800e0040311075556000c1ca00208528150356444207590040071101c2080b0527000e1440c00e00340b082640c001c05089246c91123039011880e001515406803c0c1014044481000005032a03d42c80300100308103421068100121821300074040b0844d039990701c0d00068001000700d040ea0100013030f6144c40c184080d2105450759000c030081130410b450b0000e14070050401e60300c1050301e070241d440844a00340c1030008260604a0250001c0102040e221444c400b900407c00502e6500707515000f81d020f00038100c0041000c400038002d101403981103005a407001d80c03030421000f40401c00ca500305801c945084418403000410040000d0081c403803644000d52081c0383c01c28040c4c0c0000080003401c3c0701130043c03003590307803440d50307200b800b9040e600c22140e11080c006403100041c010300c0c1000c00038105501030b10b45917042c41c1614001c00d15540c0700795a804214a48a00c6a01282c60310b4000c096801c0410030203068000b40340c00ea0410180603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398220188 1250 398218938 398218949
    0x2120601050102060129092e09090e0303060d02120a0b041707120806030102090406030f14010c05070803090703060501080c031e030a11031306080406050105040c0c0602030702010b060a0f031a0a 85
    0x145114950396482e0307403035010100b4103038108440c6912032040a0070030008e40311001081c100500040e0001d824850010307410f40707080203949150b81d03010401c545091003c100700c0e4800c641d48a4048140b000700140805540326000c2d510031420300e410b10149a1082924003486440c0400607400010340030480c0750320705423a41c01c101202e48c4808000030b02900902000076040791504c0c0f03000040c00449518086000d01540c40b05078000700d6006c002d030030b850241c0b40e00c0300810002c025000c00a002c080041d607104155505407096244c49594880c151035080e481040d0942c001180d89080b440d05000c0305050883c0800ba08480706c2c460300d2800d46a01032124042c090000504040840120510840302440c802080304030304140c9400300500f2141e82a14140d440520300800402d183c2007030712400b20202c616031502c80b80000300d956020003035480140090215500c518413216540c4401000e00400c0b102c0751030341403500707e2400c4010200c54804194142d1008d10256080c3c040d16100f070340b08207985 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398221438 1250 398220188 398220269
    0x7080a0e010c05010c050a030b0303090307050904030306030203070b0405030c0108012105010207080d0c0f050708030103061802100525020d030f021c030c090b090109140d021206010501020601 84
    0x12803520042c0e485500101002c0c0c2694280710401051580c00070003004025683d48003001080600e40926a03070f40948428140c055101107424809803410401c50b9034454400d24000c00d90355140da0201c1d04000617a130003104103002c00300d01400585820b0245c00d015503403e02e07140129615201800c80c400c3c81030400038035500d0301a13030344c0e105103e02074040703030402604074091541d21003001c6c65150060084122400000b00d110010b480e04621a41c215a5000d0300136042e030703040d42d00350380310300000307000c1e01140322400d55805c3d80c1d40c401030f04c604120103028600340e00e82d641c940401d040c8150041110500c4400b01c20000c0d041c18006130340f81685000d0840d01480c010740c2900d80d428041e8034103e03014014110000b003544600c2e00c25517058118900c6e8414607554010603655803518a9038038002c070303400c443c081107001505000004102c1c200901813180109064410b40702c0c0c0d001701d121200d0162050002e60081030051009523010000c290040c000394180070f1080c01c05417080e41c8118801042c1c1c09480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398222688 1250 398221438 398221457
    0x191803050a0e04061706070206040308070806041404111f020703060c0c0c1518051035040614060607060b03010b12010f0c050408120d09080c0706020c0607080a 70
    0x42c4101511502540050400c0107800e40b203686140098807085031144c1c0621584002860700740c80400c02a00a82c1d041d10740c5400c5880344541500c40c07410080031141c0040e0b4400c0c80131040c1100d0201140200d01450843c01000700c1070b014003114401c4000c002040c40140001543c00076400924542200d030400b00000354600c3c1030307070110381c04114040054502002d40741c0200c1c145040101c600d06a0840343c8500040d91001116048141780e0344c841d641d03000c014011844c0c0103900a0403c2c100c1202e500c0799940042801011140203102111813404030312065004120030410035101d0b029030006015490011840c200300025440c0c4075506000300380703944600f00c00c0f0b2107441c250448280c290000b001d200746c02e088045030b24000d0441103003a500d1142004508540c05000784110707401c0c1c07040c03000588115100c6040052244d0301404a01908030b07a200181ca001c21540000f82c0030406568020300074075441d00000a00d800e05400109226450030802a000520792104841c0003104a0500342c001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398223938 1250 398222688 398222707
    0x5012309040b030a05060f16080408090d0c080102040302180f01061d03010f0f050703090506180309040c09060906031a04180515060a1d01031b090c0201020319180305 73
    0xb500744240003035098407603280c000041010100c5ca80d44503039004c42c090316480c0e48211415000104800140000c50750320070104001c110048000c1c80908000b0f840c1d038415040940c0c3d00180c000b81548042e2a5035404030b4244110718000b82c000b10095007942801e0349030f06121b4010844d50304188208428000d102d080b020f40003c548042c6521303804014001c1185110070101180501884150301100c107241500051005000c0c0c414404001e42060041c04141c0c0c51142da40c800000990350b804284c0300034410300c55a9900c81c003400150b1071540c6c1d2600d80182c030300440504131032103c1e0440c07400d060810450101070002c8a07602e58110408840c0407903006007215450046100340b4002420038003c0e01b82201c0d4a03104100e030240200c505071002e1000c50ba880ca80c03c9104070501d40601624400b610041001c030b4103022446a00301d401084424135160f0b140b6400041750342814104000d42d40104c1000b00920780c0142c10401c900d003110041c450903203070603003002c601e10710f4a6009046c080080303000c600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398225188 1250 398223938 398223941
    0xd020a03141e03070b0414070801090f0b010e0c07170c06041a0c0901120e07120b040c0b180121090b191515140319060501230904 57
    0x858120040d010440c0700700c075035991036001c0d01d544000502c185100032582400300000301c1c0d403200d0b00918006419140caa031410207481e1540c5000005204080d40032030021401e1040c0c680e1240b058036640d4400601d441e05005d501d0059000fa00fa400505041103d18110142210b90f801d5015500e03030743c400008103085e001801040d00007401449100108000c00460b1469100e8005103854646055554060540068400c0680b032a00080d980c2e0880c81084c150f61f00281800c41400d03007545c1e040d54580181c021001c00c1c18109440c10314480090100b4800d00424040181c40d0036614146048100581d04881c00003a588160400c00c00708450003000a108440310b01c444011a020300c8140094205403851900540398948500419030003450303000b5081c49510601c03204100980902454032444040307085450380e0b100b0510840304407200c00c0400c4c9800941c400d0241e50105005110035601e0311040715416040141401040e01401c41b41c00300c180400d02011241d155101c2e81d03005a00e01060 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398226438 1250 398225188 398225209
    0xa06030b0112030c08030f09010b060f040e0a09060509060703050a0c0504060815030618070506070c0e040f020301020307030507030b0a1a0a0e040207030c3302071a090c01120504110d02 81
    0x746081000b0040c8080c0203c4291f0b45401002c0c054004c2c02221503074810400c00e0f11641d000b01410020401c01001260360201d030362a440700c01c0702c8000071268119102d15095880c00c031380310080c9410500410031307a107425100322070304000c135075508001e0300c0d0b042500a4481c1c407840c05030005002d21600041c40300f46501020490300e1030043d00751101410090041e85030a000200032003180e00900e0000318850130039800780c54880b0380013610201c041d03141c942d0303011182c000680161007a250060038031015071024002140108000c6ea0000342d9890041e50040884e118408828812040b2040811506500d41c0d107500705c3c800c5090503da80c0303000e0141c09032034441581d00c05c00d40140c008201802403503040072a07043c0e0140584088003020100d98405111f0110300da903440b001c446030101c22401060b840c4e016107122445580411260001c090640403441c1d0203c843c00701c85d5002e00721a074503e50380514440c0f810040100148104e080568a6100006400700d110703004101e1420503500395507034440800c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398227688 1250 398226438 398226443
    0x60f060c03130e1b03060d020402160b040804030c05030a0209160e0d050a0b0c0c07090c0c0b0906070221121314012c0d0e01091511060a06030b0112030c 67
    0x200082c1e5602e0b0250740c0d00c0c2c1c90071524004000c0c410168440c030140c2c070804882c4035000050171030042c0f143c41d44c00c210003500851001c1703400031100c040d601e00140b10362303007600e02580c040c455490311103140d403515009900d01c0ea08218041c0e00310800031001a00c0f031428071900220480070946c0f1031080054201e808098448400d80c3c041c054041c1c1c2400d214002c030b540c2c15000d004950034141a13071000c00b1800c2c50b210720300100d40039034040e08080000d17180c00d0344420446007184c54200d200410603110104202d90a4401401542000c1d01384503c0c070b46c04201d02c8400300c05803181c442c9412a00c29a1240501520040100304001c1c03a0005294001800c101d9083e02d6000c0b4090f084c1680c1e030b8581e68000c0903135900250040d061030503c6403440b044000c150b2103240d4540000e08011032070304070858200b25480720041c1400111072010a1502100c0d40d0214036240907a107489501d403400c44010302d01240030b004503503064507103803050011601c15540e11381507800c0d4001101549215241c1120018102c070f002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398228938 1250 398227688 398227717
    0x7050c040e01180813050405060d031409040e0d0305090c010e0f04061a03010317090a03060c030b030709140109050c07120c020307150816050306041a0a030303020a17060f060c03 78
    0x6000412401602600c00d40017060b0041c451a926841840100ca10075a00c3c56844041075000400207441020024014211031780c0240c1001e004201003425075810504461140e04504924103032030350305110b8507500640500080020786d950000203480101d5991074240039803071052050030151110380202c00142841c0c4803000c2c1204403444907500380c0d0000c0c041214040350008820070450418000e55856000c000c00d06020180b8661b208030081508011b110305240e00c40d9008030b0595414403d030001841c4807035010605013035500415100a00503000364510618040906c40d882180307109441803198420108103132115201000d81e03940d0f0301400001d5041c49070250114806079500080a1415040d840340c15a82c0c440400c604c1c10541260300c0800025000d03c009442480c1c40d4100400703016801c080301c14203071801c2c000f180340b034207041e003040e000b1035000912680d2481e0310000c2801d101c4602000781e400d5042020001362085c00480d0854881d44001ca0b040c44040d205204685508000d00d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398230188 1250 398228938 398228981
    0x1b03150b0a090503100c0e01050d14010816060503090c06090a0909110a060f1d010c02040504060b0906060705030304081e120603010c03090209011509150207090f0207050c040e01 78
    0x1082c011003805418064000e14408a4901e502d6005040640166131101d82c000c050f003038011901500100110400d25444003880c22200001400c4070313000e02044009400c4164100d080030708000c959500003c03c00200304100942c02e203010038402649107085841f26901e4014a00184043c0d01903080220303440e14040100081208400813001d82c254243c0d10000c035503581b4441924040c0c0004401e10125141c0f40300450031034540c5908500c803a005041c041481216500030500305c0d04116411110a56650a6102186010340c0565400482180c4003482c20300941da071552240000780c4000c044500c0400d4021604000c1e10441081c00c45d0701d041141ca4903d400760240e002042a40c0607402946424a4030000510030300480e0402900604541466440e02d06045050034031a01c40c1d0f010400603240105030300c0b101491900c02c2e0911350b070062404da82840722000442d800640820b0750188100103038000118085203004400354211030000d00f100d100381e145801341084202200c8030004a01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398231438 1250 398230188 398230207
    0xc0b0301060e030c04020a1709030c1002030a11070201140c0102190206061e0a030b06030c03072301030621022209060e03040b090607151406040f1b03150b 68
    0xc4034540c1c2c202d030440c1200d10007010041408200c1c8600240030f4009500107118201e4690424412a0424108012a843e02038503144860428100030000700082d80c002007400b00d505000d000750a01d040705950b07014986090ad40c00602400c0e00c110b840345080e4000300c0e9800001070300394185d802c00409041100c4070a0790006000751580411508140301c2d07070103aa11441100e9504040c84c490310b001030070030900c00d801c54071403003410036008046580c184101048840c040d101800039a000700050000c8201c10150881004000c00b007401d115810146010300070088040384c010b500106009819984088480d1030001c82d10f48504600188005820301e2000403a01c0440d138064007245026071820407031140c08a64a036224843c91150800f2400180070f045464542040100000d911591142090740003442c000c9096414012100000c0103000c0208515410103004120b00c5800450042110240e441e0441c501d0f040c01107411000c15903151003100c2d00002100c054070180803c4000c0d5511240e120 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398232688 1250 398231438 398231447
    0x403020a05120408010509011e1a1c150504050607030903110d2a0c0621090f02010f0509150a09030b1602212203080304121d13090c0b030106 62
    0xd04c2050040e40c070b4000000d1382c01d0818886d80c0d602c3ca048104548180c5021003524000d00b001e200809541ca001c8503c1c558180d8031100b002d8050140100f50885c400d04a0800c0e08041d1084508005440d08000c2080000b90002c945035034000030508000641c240503042c21104003149500c490b540384522a242a01d144c4c000301c800c592a18183c0e000c8c2c1c050444114a2851400801801030143e901420103120032802480c882c2071540d8003120650704070a025981409a50441406842440c0d051840c2400d550b482040076200034241d080103451b024850300800c414584c4001e4000081c140400d0402c02c07a8850800700005540004480e1218144070002c80c801d0b105244810307015100d1807010b5006003e148541d00f50006803100101d052003c21101c03069040c65000c2180d040781d87d107500120003c1d9281e000385018078000c50f9a602c0c0c5102644025040980d91580b2042a0341d85141c01c00980e07494100011002541d9200440e035a0042d1900803d4058140c2040e840c510000c80041030f9150b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398233938 1250 398232688 398232697
    0x1204050708070f0602100e03160804030507050f0f01121d01051005010c08030c03101d060a080303090c060d090501060b030702010621081606050c0705010b0307050907080403020a0512 80
    0xc0c8410b507040c5660750020b803c422006407190402680180e1100740382031941c0da2114041c7c91030f0409503031030309581201040246003458001c40c1e141c07034040b8050040c000100002000b81000b03890700031f141402c4000107016445003006003810480d5072403003040c2c00c07034080c0c001c90280103941207503056241c5c951103414007814045074a44680c001c0c2200004980d0b2080080120182c1c1144034649182c41d9020880c496034001041811a10280e01c000100d5200714858628012a1030403440d403079007403c1d420400b00128075440502203600078403e00c03208803408100c55014090840d0840c1e5103001c0b051424000d8902804080e01552a054000880c0281d1360006c6104040740d031700030010580c0710042d91140d012040420340002c03002d500c071100081c5011005280500c00542d0328141c1210603640e01080d900200c07101541000086407440801400340901d0220610441c080c1503140d00700f101003001107500404900c00c1100e88004102410700030b000385000e9035000030a4680e0080c0404210780303030b81e01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398235188 1250 398233938 398233949
    0x813050112020a0504031209050901090c031d1b0f041103180613080306040219090801060f1d040c03060c020307110405070906050f0d1506020d023012040507 69
    0xc040712000640300703241c401c036400281c041c1c882c079041a0841e20f40d40307403001400c0700140a0214020000c241036030f40e942220300818000c4000704a15800da20002e040d5a64101742802254142e5804502400e001c52001c14221682c0e0112801d43c52510002d180b03400035849140d00f19181040d001c0c010742d5003100541c4100c51050720f8401c40200820070680d903900894400c1c0d0420040c58a60780019421001990440380090016007081902c101c1e00c0324030349241580c0004a28190000c110540d4280180780050954a00761740385240303840e90b20b0131040e40003a40e0a402041c10302c002010841c40001e00740c003030754101b141006491840080039680c0d42c42080c041e00e1011840c5074440042c903103801190310918080d55400c525038078140040d02e10350083c4900c210b00b22000c0c07022441048551044070b028032010174840b91342500d0810080d0502c002c0aa1840c11500241201305c101e042a007081102003060020380301c1c00300101c07102d22145005030100440c590303c0ca0070601c018000002882d805565 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398236438 1250 398235188 398235197
    0x3200d050709200a12020c01020c161a030a0207020d0503040b0702010815010e211f0c0f0516030c02090f090c0405090d1107030807030c120206071d030a08130501 71
    0x3c3c0c80912448554000407800c042c0c0480801030314214611070303e00d1214000c00041d000d400c1400c03142d1201d00366040721a5802050f0702031000728600d260f00c6030301800241340f040084121074800d0b9560b440d0a100050184410382e4000801c0300c215251550310340300194200c0c09a039103030740c0c07100801040c9038000c0000360700007081c410106030704481d01c0c1100b03a5001ca0513107450074240c0300001032048041ca00102c0c0038139030102c4140710180c204140051306130316420131005410fa41d40351030f207581140c0585849204000320340f50f10301c00f0b0942043c00c4910b0031034034821141e00c02e28680790403200c54481103002034020400c0c02c14003e060288194a5008a072020305540000740b04c1000d110841c2c1e000c603403e1006600034981d03500410301a420701c0d0f1020b015482900c1d8155184e840e41078942d8825482140010f00c082170f00c5060044404907480b0801c3d140c07002d0680c82c00c10150041420040400101c3c4166841c00041000d54081042c2584250f104c040f0350740b43c031301e180101c00d4a0311442c4940303404074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398237688 1250 398236438 398236451
    0x3020904080a11010b0a0e040c0306110715090b0402011101060f1410020c061b0304121b1401121d060403050a030c0504030f0816060509010c260103200d050709 70
    0x283d41800781d42e14a0742c01820703041c40e80e40b5044208103d90390181041d60200d40700d10001c000f080584c020300e00c0c0d415805036510ba860800340340c0110b1800108400b040541e1401507102d00095020750003a401503024030704400d06060f07040c0030030300424043e840900c14804060b000074070000031200e000040d1400721203010300200041000c0c1d8881c031803802c00591000080041401d500840841d115040001c40b0403030b41401c1d1107400b1a032000704414010303610100340c81044001600840b60b00c1c00503004074400080d842c0c021030000b0382500401580d02c11881c1d110108580f600b110304215201000c07840d000c6500343d08080c04d0150050f4030402c105000030f410000ca505a80d4081c00407501201d501204c60200b00380151181010358025001802041e5503c3c40d02c0d4001ca80a40070300740c01000102c00005070440601c202804500c06a40d95440d090300424203207010718007501d0b15a0450760050f15820304410402c0315a1429503003100800d510210300b421920900c00002903c00030b0f01c01d1114100100d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398238938 1250 398237688 398237717
    0xf0a0b010509100b0d090507090609200a050702010c06140103170f0f1b0a0c050f0d2102010b0d0f1b0521100603210807020312060a03020904080a 64
    0x110000300d0b440c1c3c800107600c0c00d080000c01030031001031840c694110b00015a44d0059641c290900d1030503406000030585038082031141b044140704030049001c0c624284003090b04207052280190007080c00c07060502c84007003034040944e4000c07a418010740d80c0c005c40c104030004a1402d1075080c1c1c242800140d4141d00c110708011281402030b801c607900d5148045001e81060a00c556891250b40550700705002814404001003840d0000c1103010b04041c42801e480d140e5a0501c014080c20341d90907015207200f08169002200452101002448084201990600f106207020f81c1a8050011030740700a81004902800c1380501091443c1060007901c07428034030081c59000b4001090944130750140313640c481d400b08010200070f002070300b1109041080f907080d00c249140d9403428404540e0142e109540e1548004191406407a50007074135130340484c0a003000000303820880740c000d55034002c003038400324410340d00340200301c1c9507451824000040d0750040102601e4030300361520f440e41c1e0300588198030220729017101400c003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398240188 1250 398238938 398238949
    0x2b090509091510050109031b080f060a0c020304030308010501051b120a080906070e060703030609050408070b070207260a050d2a030c03120b040c050301050a09020309060a02030403110f0a0b0105 85
    0x44900507911b180300c180c00e40e11034850200401409006a17061640002070707016051200c9c80035407840c1405061289400b03a40c00050701c07035401d1000b045400030001030000a40104945040d180c1c00e28000d0b8840401c179005c6001c629010090041c1c61107a070000c129a400000e00400c0042c103140d681090702c1d16018a000c2e55640c0643d0070b000801d0301c03480075803c81d003420b40251003d1800307850040f4005580300c079440d00306c80080e20241ea24800c0010b400091000300481c1d50b0b00424988014150340d0700c0c207103810111b8501028140d11201c440318200360704840c01c1101140072034002c41502c1da0351401001c042c080c130728125461003004410401070b4845102c1c0c400000f88094064860380c0941440d580c048035240034a40707210942d01e64541901000e81ca80d48a0380c4032008043d101c0f580e603541070404000314868580d1264014600400410040000203d0380700d401c4010103001584a4940b442c0940b42c1640304404c005440c410020000e0b0350320300000c1c0300c210090040c180d681c0d003030b40c83d42c00703000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398241438 1250 398240188 398240221
    0xf020c15340b07020709050708071d0904060245010207081506120a0605040b13020303070b04030233060402030402010c0f08040f031a092b0905090915 66
    0x300c80c5034000800700200d0562210540e00c181284180e400058035985558115081607805d070380003903054404c00003501e4010401128199808a03840300c0c151214000036032000009000500840e00880c0b5541511801c03409944c0410650452604105002d803002d0041c1104111080000074200854101e9500225009042e80c0c6480094034070f910841d250320114901c003911458000122101c2403196030350a11510b0390380c83c4a10004155070070030381014207443c0400303040346803400d5a1003035601c0140d40c008119081e003640106159059901da09060341040224203002041d5404240207900c0c1d030b8560103004c82042d44104954a9584581082c0400c030302040754003d0102e2030882c44c81c0089450100d50f0701c00300344554040c600e01078031036602060300c02840c0d104455650f0480080d81c440040c90070344035031110041c1c00a200e0303001400c140005c00800c5042c2d1100c94088e0101c0d01420602c19501c0202800c00603150b403142c0d05050301031603603600c0d4400d80c800100301d804000c524203090700480341 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398242688 1250 398241438 398241517
    0x10209310b03030f030703020d0c0f020d081b040807080f010c09030605100b0a0e01030e1207170c01090c211112030706050103060507090801050f070f020c15 69
    0x4100c080d8100035003000a002245070303507a140c401841a40000c0c003908004502c900140c0c1e801603200e900d17495158081c5c0c0c03452050760090100c40b58401e41901d5000a203500510b090789003240c001c0d00c5450504946101d8024892440300700001e001c039460000140c0001147c10600c1141e145010003500709003201c40822109000555040c001c00114002d070708407030707001141c030801c900c88941c0d98140301a0960290705880c002c01c0301710788800320541e0588030b20302e038845e848400f801e05600c1c4250726180d140b00f025401070283c004005048950500301c002d07245001401d1008102c0d0031254188040c0c140064071803822030303102e8400b5126440281419250149034060540403014031010100819580c202e40809440e00c400e00500c40490030030300845000b180983d2000825040440005242800641018140b0f1b03051809014081c15a00010350b4004060f15084414a1484030224104600307482c03110740c010b5001200308a002401c90082c004000424003d804040070040310285444448012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398243938 1250 398242688 398242759
    0xb22030227010f051c061401030308060a0902043005060403020a15020933190801060f080f061206091f060b07230d030207060b040203040f1209090c02010209 69
    0x202c05483e817210f1300040325110710b602003029032100c010307000d605400368010f03000183c0318403d1005070700300400020040c1000c031a096207420b00305250103041902c080c8403000e0160440110344203c01000550007109076201c002d4800f43d040c90b040c02951403980040a0b51641d54a240300004804030303108440c15003402030250402500303802d05540721101803880d110591000c204c11540c0000c03103240100302025601c1607914050800010090000c074050f00708405001c01d07000081c0d6282d4100070030a500c400300291800140d179884001c0b070402c0148c520009568030512091080514010490b955800b4411100062010211a4040030344079944103501202008005001c080f96042e40500144407143c154440600307407201d07145207440d403c070007c5400254045101001c00565000f6982401e0007120258254103054840d00c641e81ea420a0040448400c00f000b08803141c0118400d20042529400401c01c4044040c8040c0c082e500441c1c82600c200c00e410818440034080305c2491140c208180c14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398245188 1250 398243938 398243959
    0xd0b04060f0b060f0c0f01060f0905040503041a0702030d080601121503020d052107230f0f0d0206090d0806010f0302090907091e0b22030227010f05 65
    0x40d008000d2003001058201075468090049440d201c41008049607984811016640c0000f04030741c0c0d007807200b01000304040e6418848108600200220014142d03000c480002a60307840e1450130138038512655000c1442d00b00b44d8803607480b400c19020b01826400340241c0c00e4a001142c1b5441c1164000022180035000c03034440160700311641119407010b9950721a0928994000e41c4940000c3d503414107158040314150b1041140000380040700031416030044072081c2031428401c0c41d0f80d5280c001001c0c0d07600c0c40b01211076400c2210108004202501d041014142955552011603c0440c2c4a0190012200152282101041d0081e81c00203210510103110391700e000603512154011168006a100110308068081c4004011a41c5520000e070240074507480e1074203c90b250405d52009808030004050707640207012030070059450b240381217842010488040882006200e103035861a03000c5900042e40107140c803803000c00300001b214100000031034400c26071441c6030303a41c000a40c0d19034118000c03560460242c82 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398246438 1250 398245188 398245193
    0x90d0f0201090c0609141f0c050a0b0405070f06050712030e0313080706020c0603090d080c0403050304060807030501060507030906120e06101d1501050306040e0d020604172b020f0309030c06060d0b04 87
    0x201e001a40c0c0740309e2404e48001a4a58a90b0b10810748181c40a03105030300a08810000119045242d2000744a2800c0c0503080c80003d8035020b81800c0b200c0d01c00001c0c980c407000030b050359207003d2044510500c080c2d24192521070310350842a5490025000707101c00761280400900d802d10341907058a00c504140802042a008804000c80d002c013400781c40205142414480800010418400350000d0201542c076000545068000281038480c103a02200074024100942d80c04a030348820750000b62922414422001900810404014400d003900641075004032802d0081421621844504890481e4548403a0341401c00000e80c8086096401d80d01c0c60345170100300905940980007841e4030000040002131110342d071284071070422000d5032200005812800410040240b14407451044c0003410020608203403501ca0031080143d20400f20310510701d0101c41c481030710344407a01224801d4042c0181c06480b41000e1310082d40c0c0783c1003001e6000c0580102000241c0909018120f0795100f90060814005a01c0c0e94 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398247688 1250 398246438 398246447
    0x110f0304060902060723060c0307080411120106060c0210030501050306040b1306020712110706090e100503150f09012304030207030b0c040e0a05090d0f0201090c0609141f 75
    0xb04a8000c1410b00a0b0401705a40130300d08a4080f96040100c0c41034440c1000c49070a2643c000d01800c044003080c801d00c2490750303203c400f80d42e03c00e0f4000e44143d03060310b03000d0004440c3c4c404100021402e60801d5004034409a001005c440128401d64044030700c144150810744c15107100b4002c450f017503400340002a0102e840414066004040c10940000d030003050380311001a0b030f2180109a482c03104091062944c241e10202c841000d0795040068480315003066030003004c210303152007114080303402503001c034401b000f20000200c01040300070308031494020701c0c5c00c01c4032418604132509203411660303800144000006008458030501045000f480c1006a6005800c0d03410000e8002e5045108015000c03000a50700c0c81380900484d030b1540c146071038519000e954001c00f0002019045a141042c0500201030400101c0c4011081c01e800d15045036040380d44100d0040860720000b51204d0120100082d078a5000f60411094410082501001c50050030a016141202c2ea0070140440180d540403080a440b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398248938 1250 398247688 398247701
    0x412080a0512040c180b0a091d07030302061906060e100e04111c0920060f120103150c0804030503060a080709050601021e060105060d02040e090a06110f030406 70
    0xd509019003000d56442a02e40203020803141242c0395504104280728240030000b01c2104541d01d20070900c00380308480d011440e03280b880c2c814a40c645807291503540c1034042c0c2018202c00d0360b41c0c0740d040340c0200d036032803c00942d41c0780103640034071040c16286d0540c3c00d403000d54042c460039a52140c80e546c00c50854001400001c145040c40d03d0100139400c03500d04426a242d00500243c8080303082103580700c002110084030b1007400310b50400340892030306034031000040075045e01ea900360030000d4003619040e003001c010500a1040c3c500c0311022200000b00000e03900404411a4180d9008440580b120603042890000700c4005003402004508010b0010700000d01c9800111303400781015010540c0203546130117407840c0c03082603081a5842500e03a0200b1056507410403840c64a10340341221040b5408410101517100c4006015945c0240e200080c25041d400c5c29404490080c00030065042c26441c140c071070641c40b25030492040340c0d0703d81004503d500210004090701c442d403560300c01c4d8074a0758441d9500d52005242 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398250188 1250 398248938 398248957
    0xf060c0813030e060705100507020c0607020d0b04081b070f052b05011503030e13020301150c0609140606090124110f01061d01050402030c0910020c06040b0406080606041208 76
    0x1041000c500050010707c0a0b074194031907040301280b20704100c0310181c2401c0c4900c150500076201031007000d0240c0c3c7c0e41c08280c50b00d99001001c8000c59201e070b09000fa040e02c1100340001300003801c6c102682d09842c0000d4a0011150500080380010b5129070400c080324820f8844600c80625003c1012088050907245d07012a5100b0800062211011040c02d680c4400c158400c0c0c0100f680c101c078418031810b048110344c0c200252036000710302c0d56060600c000c42030080c4420310030422000c03040754020055580c0c086d601068024120042501d26603100690302d0100719030660084040c0d000004031102543d003180b6a2a40300103102c0306208510104552038106841100007511846400c5881840f082c800c48002e8241e401500e000c4243c1000300d00d00c032344810307844980902e204108018224041000340c03000030b1800c441d4071101c0c1303095840c120300c0c01c0d101c800d05680c041c50001c0c000848584080003082160101c1d03e83c40740301e585503070400c0a507020b80d1040050400820600c0c5000420b1710008115400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398251438 1250 398250188 398250199
    0xb130608070905090603070302042405040b1008040311030315120703020319030207030b090102070219051804020607020901170115050303030a020307050f04060e0a08010c1e03090803040f060c0813030e 88
    0x3070781d0b600001c0a0302d00061019140c201e00004c2102f56060003002d08016180540c0c05000c03d04c10640406c80d000441d1100e0780030400c180b400310701014401c86200501c0d4003140201c07034076410b1004405440000201d00184036020784102890781020114052003280c0c0c0007806003441900c0c1d00b088040405100c08104c04601940f2400300010311084c198a0040d10700000041e110120703481840458082c10581a8075101b80560801c40741e9501c03848288907028440c40c500d0147c540c1c1c40840c0c00d034022118000e600440b600004200702c080e85400356220700d0400004c1c080c00741e5101c3c1e140b154030600c0c0181c0341c058000b0030001c0e0110089030002d5800600500d0060318240403406207c1891300181c12242c0002c12010084e8224076041c8442c9003e4a503840003049003098110000e1b1145a1005140c40f000c1c61a2021b210418002d80c0041100d40d000511a550391400703180900c20b100b0390117800c440b01d924101c203007900b261141411a04c07031640c00705125801c40d941d0710255102412962203e5001c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398252688 1250 398251438 398251453
    0x5070b0d06060e30030d0504140312010506070303180b0a1802010e0402090a050d0302030a141206150405130f0e01020c120309011d0f0106140d2603010b130608070905090603 76
    0x4c0400b0802007248075849200010942018a80810503004032001c60131268001d000003c5e09400440c14241101c004440c0d50303980300b0a625040d00580103040e0741f4505a030210a01c0c00a1294030100d03507100b4030101808010b1064404002c403a030130301c261400b0780041c08841d8030180c1800c055004208641c1c00a00c4500900e54070000a800c1c0940030130304034016000410201e800c1a005001d4070f0f001464148018180346040d10625041140203011a01c84c1e078a0180074110385500307504950160101401d816242c900f009008005400e407007401d044034501d002c0300540114018800d0710014240c4402034550700c1c840d4030030f410042d00045d003903000170b543ea40360452001c50403242d01003201c0b400c174000d0b21020200301403103401c45079a81d0041c000000081c0305614a50340b42d043d8403000d00d41c008c484040d0510300661113040d100f01c00f1003800a00030004000b01d040c0020402400b41d07520345042c1b04030542c1d15510126810035080d40c0c03e0010406074481840245012100d1692210707001e17041780c881 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398253938 1250 398252688 398252779
    0xa0503032a0303071d0103060e0115120501140d0c05041806050721020a020f060702070305060109020a08180f150a0621080a05040305070b0d06060e 65
    0x15075208504680301d0409030101d140c42034000150030030201c00100c0285045180007000900041d00c14480d8a43c1111407101060b091b80c001d034040c201030209250040055a1140c4080c1c03484442c03451100c0209459042e1300600c03500501800707050303600141e1000c45031807441c020b228141000745411514071125200101d140c0e1a6131291401c51302802000b001401e5180c00d1036412640041c10381010010903299140007000c400c030b13101c02410f0706501c0044e070f100440c640880c00d012091b9034603500d5004000a020079141c1c0002c000703041d2070086056941d00e998894885040344180c4841c03201090100700025a50840340305406d44142030b51081d0384050148400040c10304d07000c045a170707a804922106000769100e880c03140c40098152100342400d101d000101d4510031981220008090400c00104881006d10510596008561200440c0e806584540601610350007101d2882005850801d001507940d11030290300b2900071001e0000c94403100c95a40c51f45076200700e41c5c1c20f501c00d01a1403844640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398255188 1250 398253938 398253943
    0x150c0e0a081c030b010c0b10230d02091008060c310603110702031e4e04030b0a18081206010e1207050406060c02101b08120a0506010906050a0503060a0503 68
    0x30441a090380321148c1424a03000840c0795144c42803044900040720851041f0317441e04442c000c030303160b011140c03568250340e442d8040200d4030300b0b074015290a0051606105202e00c0c4440076003c007240010702103281035450703c0744550340c862500c500390081d10b85035010001c07540680c0c0840100790100b41c8103443c2060700d0300801d1802d03011003801c0f001102a0042e0705101c180900181003107104400300c1c6001e150005803089001070215950390020300011045804006000201a0141200741700c01c680315642ea0030107400384030342292041c61503820003c1c201900d07103d49004054580d07101e441c00b82081009242051078183c000c0416062050140c00c42040785c4d100400c018a500d82c00005241d0030b8184030602c0203407a0180d100805024600e080d80c0c0c010790f03910303c80324800540c03803801d5101c2c4440704469580807100080c002c2d2070304100003407041006444e6040c0612486190704c0a10154582400459007400d1030700c683e0300055130921156102c28403c000560300198003e201802c0583c45400003030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398256438 1250 398255188 398255191
    0x1903030c0602040b0a08100b1c02131203020f070f0e010b0c010f0203090a030210020708030c0304030c0609060b03010506031203010b0a020c0312251707150c0e0a081c030b010c0b 78
    0x1006c203220700308001410003088446400b8020039400d075420038443c640800780e41d505000c0031081c819004a911081c120445a075200244000f5203060384003900e6041c041d4554032606200941806415400314041c180c1e00c404c54101c070304040c0358011b41d81ca00301c4000e0507508500300451183d502d13070003020361400b0140043c50140c001400070b44a462118034010349000c19195400700a1070040c04071a0201e802402920341c00301c20500710355a20b03590ba10382200e100c0309020300180075034604141038061002940c400e6803400d009130000c02c0507884010801d6500c0204d26581c501e40c100030401840ba101c2080040d10203012640110f400307020301d18002904000415054807e2140045285602c4070a611004c41e42e522090207010600c108030746880d140000c247d580030400010020780002006100341051007194041d580801411b030400e6402040c0b0f90b40b050406208490044020960481c0840c182c1c15001800c1c0b61040e5000310608180d01422142404c07905011851841802292201070041d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398257688 1250 398256438 398256457
    0x120a0b0103080306030f0601120201050a0c0813090b01050c0a11011103031812030403050d1104180c0f02150411370f050904061104080d08060306061903030c0602040b 73
    0x143c892800030103042ca005034142c0b8259841d4441030040190300444da12040ca01502883c0c42a5140310822042d1061800c601f0010300c082c3c4000b890040c02c058443d64882601c000f03250501c0350060500045032640105000502160851940c500000307011100102d4210b6042c10500f0491120441990842c1c0088402c602d01450300700c2d01a03040c440901496880e00d005801d21811420b0540300282076000d0b0f02d07426000245e440454159600403842a50010240c1c0c1c602c00691100c0400c0e1729010b05601c07a040b074081440c1032035840e503c900100d5120811401105074444e070740d4458403585003400003c0040c0780c0180420500e0505280040c0e403441d0744a00428190f56000d01041400c228001c1541c06500d0750303010080c06002c15079a031402580c1203504610085a014441510100355110f90382c4841103e1064003000701c0c0440c0c120111910902c021002d80d48d0b00c1d5248000d100486a018076110044401202d01b480080d0160101d5602c013802221b0050400e1b032200980b0303100b40d0040512 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398258938 1250 398257688 398257703
    0x90d17040b030402121c030c21020a0801090b010c080f0f030c031b040e190605040204060e04050a0605031515042a020a03050306100e0306010b030403091a0306120a0b0103 75
    0x200804e40c240611000c0300030004000a05c00040c0b69200c1d000310903100c01e4541e08141d03e506480c1050352055444a986140c114030100744844481104d4000b540840099000710f1900c00002a84400342d00c00c42074031601c10384802d10090384035036540d00756a001c580003518203581030000e03a59543c07507200136600c10840500b20030380d80d0900071155010b66003511034408115404010a000311200d0000964102c0c1c2400d5000300318035901d42d881005440c06030003030be402030710100d00098140d40c0000010f02000094404020a40b279078100b0f0004c0d502c10f1301410360903910400c1e1034a8202042142a54003030042a0030202083d92000080c0c00d1f105650700160b461824545101803001c490480500720071298002800221880e075006412408024005440707600c039201d00d40c4e0710030300405140844040003002d6980543e110f8000724115041a2019000160004404500a03100c0d101c004d400d0030081c007109041d030b912801001810300c00c00380b1006440c01105026400a0320300c6502a0180d8464a203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398260188 1250 398258938 398258941
    0x70f050303040303140c07150509011e020301180e0309062215030b030d0c170c03120f010b0f070b04020f0d0f050c01020307030815010c052a06030c090d17040b03 71
    0x90f42c0c105c107019015128804042100d1000240006149a4202a041c1300403480c1d9499003941c41c010701030021000d060f0301c5121083c00100910350300450695185421544414203450602401c45140804e14203a55004002510483c6401c4c009003a8a003103501140e0451654020114020f54940d44035a04016006100462250b00340c002d640e00908241d00400c401c95000c44010048405141d000c0c004119080c11070f03107003440120480b1041e000c1c050131250703102e030807060304000d85200b1a0101c009441c2c4400100f9428048011241815001c0c461141401d44a4545155186000d8000c0703a10080c1040c56004030f40b00c10741d1003030030715025041c40011040541480d41c00e11200b4100a4110b400400c5003c0000760000001504146614194030691840c080180c40003100c4d20700290240c403d0125804050f04032015110f403d2800600d4100c1c0c103a5031405000041c08156100e0210b00014840100b190400810f103a80e0240900b418400d411040c3d4105540b66206400c40e01c00c0110000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398261438 1250 398260188 398260211
    0x605100309060f1e1e090f06060e0403020604110103150b0d050f27010b0303032a07151a12070611070e071215151e050d02070f050303040303 62
    0x851030000207400b2005000d403e138803000d452503039034484440001c0c1641e2400700c05401020400c410348000503480f01004400c0075400c0013407403a00c20300d1003240c80364181400403e0032030303026440500070b541c1900140642d4507195607110410f031a60f0320302c4d410141d0701c680c869172103458105808001d00d04071002503511a070807540c0d5030564500508207043e1100c0441808400510000c00d082002140d494200c9800781d00c01c0c4146c090004050041d600d031001100f1b108200c11545d0140071760f414046807880e983d80082083d4886030017020005407e00410010b054003411168105c2e40c1d40300301000d80c20402c1560a030020f006c40a04090101682d40a8a004d01446070822184900c6c1249140100340b01e6141c404484a00c2c00018092030400c140201012032904141d0012a4844001c80800503440d4803030746c00182e820f2503860fa0200103050009960302c41098410000c204602559507985000d030a2000c10300030354882d001c111800600852098041031091010f540101e00c244d40c00702d0280d1186 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398262688 1250 398261438 398261441
    0xa1b1a07080604060b0f0c03040e1015030c050301061b050109060e0d1107031704090515090a05040f14030c0f012a0c0209060a05060c1c1103040315060510030906 71
    0x80c1414042ca141001c1401400305d400305980504900d00c9000c1e0792440c2403a0342030f046014551003583e82c14502018040044030095800b410390300c110003000c0001704145c500b2010358070003e06080c081a0b08100610180d482054906018111001130100c0f00501d42e40e0503085a00d001030949280d50b49820031020700038180f119030096440340c078041d0049002480030035140c1c0321921004200150712408a0140c00d4008252001846040350800540c54100d195004003200034950034400d990100024003101c6440c859503000e1904078140c80c00c0c89156590700d00c40d5200b4005400118441400302c0015484100700e98400e0704445400860304140b1f1120360040c526042d40c440d0129551500f2403e4090341c440d41007440281c0484560f00180c8036840402c0d8000410340050b0f0704090002090804050300050703c00701c00303150b094409940c11007a2011200003000b003071003050b030350410003040010500000000c00088010600018400d40ea20300048000b07900031003090101b51100000030901546 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398263938 1250 398262688 398262691
    0xf0a0c02090405160503030903061501020a050d030906050c1206040902030c1c1205030138040303020c01140c070512030d051f08030307090303180519030b010f0b0a1b1a0708 76
    0x15401103048c640c0c09000248c0b1201d0080920702d0b01c109258442000e68420042494100d400805451100e015800d0040240c82e01c844240c800724188408601d42100700c004469150400c0c1d5500a007070345039541080301034040c50405a9041c4100700d00d80445a0740d1308032620300b06000740e521880d0b02902c0d192440684031f1680a8105001c81071004004016003c100844619845071048078501200030760140350102d208160b9041c200003003130100401d500000c03688110307502600c40f02100c01c94060a619107203e0103c004207103821012040009050040c99080409040e000350390801031491088012941c04480704e40a032040741071000c036952203480d1100301411320507001e91b28603e00010058401c203841d100c02410040d100100300c0840380d0030303410940a424002d01c24a019030030781c07210304511101c40c002a42e641c3c4990000266141c11210391384112040c10802d28108001d45c0c8060b110741e034401c00941500441d100b0301c080000e0720411201c8222a141001c0006820951002041e1b178a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398265188 1250 398263938 398263949
    0x140d21030e0d0c021c05010c0e01021621030908062a0a0f0807051c060504110304020901050409021503010b03040b0109050411100e060c0d020f0a080f0a0c0209040516 73
    0x100c00b0700b4400081e4012400d0421030340550700b181c001c0080100c58031140400e0100a0160752070045001e10301580b1503080a003100c8260300312941846284841c08c0801014456041e0700d508580c4e408401c412240c070405401e034040d040108020345d176013804070b061600c201c0768042000b00706000c0c1d0028542c00d0780c0b0091403030000000c00e8100a617501016246080c680e44100521914000248425100e1741c129080641a2200c240c1059460a500070192809016092045060880c01c002c42c0d04450241c0f1303c074540040412800340d10b4441407000030214030b401681c00c41600d0700d0000140301548000d500030f0501c0a48140e51f17181504000c18031a0040e003080304d081e4100014403010a0f002e40c9081c542d000d045850303000404221806803018a01c060660703400c0103002c585101d12031804a0f091003150465000e440d1810002001c00e034562007803040042c418101130004ea1040008040506040841070400c8080e00b002e0780c0000300821360440d01201d191340a005001e00074440184100b00800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398266438 1250 398265188 398265193
    0x30501140f010b0a0c08090d230a03090b03090321041e03020a0201030b01020f01090f0515010503071404020906072009010b0702040203040c0509070f0801060903030504140d21030e 79
    0x5040002c140320b40e00c0303031080300310030040501080305c2030180400455405000041005003400740324a400708403451401d010f00c54621110345181d40240d804100002c2e1141c2c15515044401e092403110f030780c250005042c101c0c2034402444102c0c065401451b6110458a0394084d0b00000e142034641085856462403044801c0783c00c610304440040d400084041007181d0900b00400c98400560040f80f0342043c00e16000c0c071541c2440f1f0803034140400852480c1e1805d002d6815210040d40140115445107000c2c030030700f41c055001c80c0007006100d015012030300020710001c1001d0310300702c00600041c01c00c0c0c0080c001a15030340084150b142c01d010102c9018110a81d09840440d520340c503204410311a8041c01c280a03004c1d0303400200003010064040c40c80b0026010080c05c045481c00c1c9680001c00140b40441a8000300e212000045802d6019420a10850782e06d0307540e00d841d20341480d000d184d202c01801030a98026560549010024080c00c840c10780500d4a660701d41140050420003c05540307100c1035050654 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398267688 1250 398266438 398266441
    0x3110d09030f081e0d020405090a0c09030f050f0313230901050f13021204020a060e0a03020409053a051c2003070302030f06030d0f0311090604030501140f 68
    0xc001d80001003401d81c0100f092610750740c00c5080b0070030818a030318144030311980c0010324400d030000c44c1d40500250b480c156802d00c03440d80c800ca07505c0d040302d50303095410f00811114070307042000903411564080b84610078130a5801d946812400c05146070481c04003983c1d4900000d20501c0f03860780d500d0300480c0408190003800c02c010300c11008074442020600502e40901d4020f1074000e1641c9600c078402d901d40d410507000b10750741c5c039018034003100880c01990100e2248800036000600207201e122902c003926001416001c0140c075507402c0000801080d10100c0b214060094070101c0d4025030742030325004c61010b202c500c2150300c2200440006a904100100900006003e564000c041030300a20840100b00f0070001860a48002d400da800c0840740e02d541400e500000030450700075819000b42d4092410b0481d0344100d5201c0d07004064403801c4e074810b240005000b00c20307070001403403081e00508030020000322501e2a0004074004a031a42e030140c0c1050342c460b0745030b42d022221280400d0304a07501150248a01545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398268938 1250 398267688 398267693
    0xb0106081e0c090a0b03041203140702060a09030c051c021e10020d02121504050f0c070210091223030309032b061508090f0706141603110d0903 63
    0x784a4090074505030b4400c0861141807a4480d000007038042e2440c0f060041d01d0340360600e4208144912851890b00090804508242d440b003501050340c0550304940140015170b9a0220f80001085550340540c100700c010201d250210b04144250500c005600c440d20703048218210020307252084854002c2641210b5000c91400e45c0ca02044050100c07404032009a60f5203c1c011808010703004080310141100da04105000d40e4071442050010345180540b018080c0350742d4000300c07100054003203522602003e0100306d414018030300070081c902140c245041008405403552040c00d0308607a00e00c0c0448842143c403880032403107420110400300004003200118658940701c202039481b401034040d88030402e8901001603c0d501c0c140722404510340200b09040041c1035075682100300380e68001c0e5811001c24010350120700e10050100d6441c01c2e00c00c0b4200280300840c500003040b20f803810b112a00d8121940c003400000c014010280190076054000c1e52940b07400c0e40301c3c9104c4c50403c41103030054020302690310002c100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398270188 1250 398268938 398268991
    0x20a0b0603071d100f06020a050c15040b03180d0201091a13030c05030d110405010e032109030124030507170604080906070507030c1a0301030f0b071107030b010608 72
    0x80140b82c01001c94241d4031341c80901072000855400c1042050701c0d41707102050040e400105005054080e004413840c4100807410b12865450390301211444007410041800361103020401142c2140c201c4140c0141180080e205030708200171080b02c000141d4441c2411414404440035440c104104c20444070240d0409007207502c1d0406190100809002c01d44148070241300c0705000361115008190018444408000c8400031590710a01409021034141041e0010078200000d42d8400c02c0c40b4000415800700744003802400540010914647c15034881000c0c03483c1341420540758095855803211011900d045240540c1404866080710040440c83e11600071035031400260306401c19040800580d644074003034041140c6105084001c1d10034802c0340030000400003c0282042190301654150303078441d4500c0c0d02000644020303c000b07000d01c20000b00441c0812220301106800a410b03080044409416140c1c0500307203055070f80191120120350004100c541d401004140c0e228400c02e05002401041c030340e100341c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398271438 1250 398270188 398270219
    0x12060b04030b09100c050403021806130b0f040f0b0f0102061303031a090717070230041a19111509101103010f0501020d09060e010c02040606020a0b060307 68
    0x1d001c2031040000c41c001e0f2409010054410704241014006455501c101400c50340c0688001c070b020f09c9900240f034001c106012135190086000400d41c0401508101c01c01c07000e010701080340355001148009000d030ad41e840e80709504544414400125540c0d0b80001085174100d420318001d03040d03421000400141d101d03440c112241c0310b84e042c240011015030307076030460014034019000c01c0e4201580c4130034002c4072904407086108207071550b80c0350041781da6042c00c12610365280c000c100c030340d600c1c940d05451190909011031000380801042e0b850306055860000151452141c044c0800800c0300180401100340304051061040156040a00300a078006121554810030344203c000d00020840100300388500902400f2880060388005004800344045580f080e41d00c20f10900400c54a81400010954004600400b10102503100c0c0c800c003e10b00fa009441c401c580040581c10403e00e01034a8005985c1c600ca0310000e070015500400041d074251500066910014262a200394040102049031b080f4165111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398272688 1250 398271438 398271443
    0xa12060e0309090a0f0501080f0304060c050f06180706020309010e09060111060c0c071226160803070f09030b0c0d0207020904050a021305010b0d020f070c08060712060b0403 76
    0x203100d440c090381490940c040da03811240d1100601040c802a1100350b0803000c01081017030f00401550340e0312903007684e9480c0f0b600385c1035a032034100348130410506001d0049100d100d402a000d803492030010544050505604483c05900e02125290b5800031010401c481e20182c812800154a4041250000385c1181140e603003485c40340c4008000071345c06920602003001009070340001c079400c9003442840d80030503800c0046844100d00c22407400003041340039075000b15000e80c1c100c481848200c408451542c0728a00c214074110700e8007001c00801001c04a49a03400011901446600b034881c140010000c001c2540c074102c003030800030083d0003400442d220f0b00030b05801464080880e07540d440404201c07400307070081c118069805907400003000248080030035040007461080360318101800601d0300a6040f01c2003030250109170308051281203402c2c0515401044000d05040b07a05042107401d42ea41e044100780398004040981048091080251300030000b80d011280b13540041c080c850600042e915240a40e1101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398273938 1250 398272688 398272691
    0xd0807080109020a050c060403050d11040b0d020307090f0f03060e3904110306011b0b040209060a030b07020f12090f0622030501020c06060a06020a11031c08150a1206 73
    0x320b1350305500820845d050310501005660042c505410042c0c500d42019032131004550620303060b0031000d5200c030304603016101e0000055003007801480300d402c02500018400414481404ac0c0403d0800500341080010711240300c410030383e542145000070550f41c0344c1c10398004650104400480282007091400940394900b40c518030038406000d104001d2100b01949250000e16005c80f196902190000440c0304041c01e0b261020010094446c240e0600e0900c9405000000d031040440c00600e40780c03541503005040140540c20060310303034503400981c04040d14410b01581c4041c4222481d03039030900032465206c58050040d4203020030750b808200c00c0e840f140180d83c400c03000020b8001d11440911864640d0426180728032521684034035180c0d00039031080c072103403403644030320b0001421030720b481e080300e0702652020390141c01d804200b81d40e03045080306000442e1b9498081c116400d00105040141c4906038601070341e030903015013440a14814104411320016000d400100010700a030f00880d03010f4015190700000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398275188 1250 398273938 398273947
    0x90a0803190e010c12050d0f140f01060c0f05010207170903070b0903070608060a0b0a0c060b0924031509070302150f041502010b040515181611100c020f0d080708010902 74
    0x170225050310030202c4072072000e85004100e040038859603006400d001907400394001291918901907800340003d100d20000501442c3c025400107040c140042d49007440743c0009402e10b151a518116500e543c0c00300d1180d41403000c41c6075052840c017081168000e02d203030b685451810b5902c801098440b021400303014280031924011a0850f101c6c200ca040050140c0c10500782c440740070400003001100411810b81d00d050602e055040203280541000780504414a0041d00c625456680c0602c01292400040d51600852290000c001c00100b0b0040c8241541406003003038500750b20400482c041a05540c4510070404c0c0302e070a401c08070381000c50b019201ca101c400c02882500f42c8049000d00910036030360313070094240b0341030100c1e65078224642480e082c0202c80403d1020040801301c07035120300840c1c040031048842c074120030182e8001e08080401c1c0c100b080a48800951642004040c4c1d1180c2c6001e00040c2d0103803103007860115060086084004640c502110320741881140206424418001c0004641e400034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398276438 1250 398275188 398275223
    0x10528050408070905150d02270108010c0c0c05010c051f0f0612240b0a2d0e061003020c1b030d0905030a0b0c090a0803190e010c 57
    0x1100000549010004600005008010001d811601c15004144a84500807035040118040c00303201e07419444d140150580d0a604010205003a54426a04017019054015102c034080040354003080201581500f00c0d4034049505007100e44e070782642000c01107500c46600000d09900300c2103040301d80034684011100110b0030691308004420303025070782015000700078880c4c80c9580d13005017500001c62201001015619024008964001c03c80201009503044032222101c0700d040040803100d4401c98009605901c1d00d010401500e100c1d00030039146681e044400c45a1402103419914820341c07190100400c501d050040c28035480003426103885a2040444030040074800d40c180c48211000d0001c44550006002c0340c03058503010300c0019800ba00581c00703147c030500d005152483c106e03071011740141080030082c1c0722000c0810002e4071401b90a0402c0081e050740d42c4d035208044001e008020b018603038483c1010822014140407414000600600b55104803082c3c0e0800c1c40580c4580c0c02250815819a001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398277688 1250 398276438 398276467
    0x1020405060318160509040b07110d03050109050a09080d05090102250302100e0c0d1104091217011404050a0621020301050a0209030a03051e07030c0219140105 70
    0x54200c141c2200001c020000d4851144441100c50703408003065a801c0c1e66140b014401c400c8180c091a070b00440c1d80004a4006a001c40d06603a0265882c03821450112070003241504007803103000a140040e4842c2e005001000c400d210341a005042c13801c040000c0c0c11a0303a28800e55014140031044140d903244c0009016070000c0d012140750b140015410310000001c50196450b2400200c030607001885540f030010320b1001d0510074000c080e85484001c1854124070401c21032030540400c01200e8400886111448a80300d5000e2407a0f00f40c484c03107036043c80c0c04221000428504250010054400860004114801100c41321240300d11041d17501240d00c0d80c40811050140c6400c0d0b000000015202003980705040b00130106c142d01c94400c800900280d00e4011008059004070215660302d6002018200e001030301410040000e130f0f01d0511122202c03950008201681d41050b102940410032035203a80e021840d080c0340303003c2d1260755002c06420081c1009460769801718441072050512600141301403028400e0b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398278938 1250 398277688 398277697
    0x20c090709050a0902030a0b010c0230060a020a080a0b1804060b093c070e010c12020304090e0d021002090604030212010c0e01080f0a050414061003050d05041211030102 74
    0x503040c00f50059459164000035030040303a498007094602144450175610415400c0c41d2150010004549804500085074506135024241c030103600c5000d6540031311503800d2000a00c0f45100584c0141c88803010740003d4041d090040034038400034079044a00c5070302e40c2e84182050040107102010f103119541d034a00f04004008080c900343d4446a40001c00107240e90000c0030200c039118800c0d0031030100b03115091409034204014407030469169101300181c0202d125170348854400034145817100e032480c0d440d00c038118030f00c1c0d41412480050b080001e05014504260080c1c126501c4090003e00601980250080d2110300003440e10308420380000d80801c0942d80d1509803009150028602c000172211400224001e050369032042000c1003948030f03840d40039070207219980d21440259181803015034071072802c03500030000100f0890b10884882c80c4101c3e1101c003040143d1199544400c1141c0707a5045040451800711117141c00e008201b4100030520403901042e8a68900b6980a805c02d418030200e0700009019019 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398280188 1250 398278938 398278949
    0xf030423030d0905102921060417040b180f04060b03190605010504030308072a020a1a0f0f0c03070807211e18080304031110020c090709 60
    0x1194031a140c4105a1091140f0303441041218801c070390202108003031b548a03558408600e0040403003203144079000026802c200303500412505034594180c83c3e140b0b5180c001d01d180340603035200404110802440700441c06172441c1340c044480c14586400718a00070f1340b040744210300c00859000c0e80c401a58031045628041e0107801001030044a45030050100d854000300c0e03030000c141604a200c08070365405445008261030040c4e462501e86402c5850642d001c004c043e01920402105d088090910710030401104403800f039a07110398082c02010300400c40240000d82041c80c0188814401c81c02030328044085a1320380041a481644030086540311a06600070700c0311030310503404002008010400c40000401a0030300c1030020304060384040070540400200b03d4600030102c1e19400ca003080d0762064400a0007858002c0c03400d0740c1800c40a03140c0703c960340c1c05544413012650000c81c0500c10040c042c07d4080f00c81da420740d500001d400000388009c0d51220242c042ca4001d00380c0801140074107104450319000f0f402c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 398281438 1250 398280188 398280193
    0x10608011a01030902010908010c0e040b04060311060f0409020f0702040e0c030615010224010602100203070c060b0324060130051f0609180209010c11030705040f06090509030f030423 80
    0x805030200bc0e001120502c9520303c1030307290121900345494035204160a07a80c225040007034604a03501400f5040e480064003801501c0107000010303400da502d00081c50208200242c264a8049070701c144010f86030300c0c008170001030b00403144542c51501c0016500754800c0410203442c942c01704001c0180e040c0118400720035108508941045c002e90740c10040b45040b00c801e1f07400c40710fa04284540010403400281d501c0c500003204141c41e5070216409030000c40007418020180c034602d89a1b9038004440040c0385a500071031000640c1044101e60b040701d10720080d5140d140740842d114130740b040c02d806444a50b41140d0651541d41c000b0408407000c030810060703001403200708140043d1700d400c0e0140444040e8460000c0d5070030b40c19078000c950142d5000740e03809010103854501500c42d2598505007001412411540c0601c42c000c070009256440307006028003490071b540c00240d2a410400070301c083e03d0703005040c0c0e0015031041000b100400c6561080f01d9107e500308099148060917072101c100c00d503d0004014080740f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 398282688 1250 398281438 398281451
    0x703020d02090415030201170c0a0c02040609020d09020405091207080d0603020a0b040905150f0f04020d090b06040c030212070305100312050a0f020d02030f030402030307140a0302010608011a0103090201090801 92
    0x8004d6861002d013524002d80350311142c00001a031091120300c007240c034848400400e0042c000c1044c020b030112645c8a10040c03002c06e12076100d05140c812a0843c044617041503454902c0700c02542006d101d05c07500003814030007034800a120712041010034424010014056540041c0c501e00325840360303109402966005180461060350f5001404241c0c02038040c17416401e2401000c0380860f030601402041c1c0e05009031085403042001c00405c80705050030312407590020740810003c90005894822800000e2003609150124100f400c02d01044841b886855010302d44108a04120300d00c404141c1071b130000151401281039640c1c0700d01c0d2109034040368002400444070013000c0051540000103064541c3d41950b44036280303200c150b000c9942d0111201a41c0140e00100305802d000d00580e03004540c024006003c6070b1170500c1a0ba030318410001e0120400c0da003a0043c82c006800c069084c0141c80060524500900081641040b940958070a1401103818581d58100700021079029224020081030000020080b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 398283938 1250 398282688 398282711
    0xa063605041505060a03020108061c0501050c07030e040c080c03090106121a0a0501350d0e1201050105010905101709011b02060c0316090f030c050103110c060703020d020904 76
    0x1020080a4100c4459040800003001340c141546000101d9405940c6e11000f9210002071200da203030840401044280a1000700c1e0220b2024090780d800b0703070000540340380c2d030300f01078140180200081d428442c800da0501c90110306045e0700000441c0c010001606640c3c0d42c1d101e411240b401800c007507018203260306280c01039405000195010784003015022860007580ea85846500080318424000d103034064905401e03040d0800510056900303a50400591007039400070030366800c2e280103289003159000691039060180315042030030340c88400c258000020b00065041030b001070325002e03a500034a0f0040141c01d00720104c5c54400c4040d012400100031466030a401e10802d000e003e4140c4c4858204444051000741d26054070000d5071507ca0820450258155220038038600d01034001080c1c400c041048250700851840c658820b0b180041d0702c18034030345901700d140c84000750030303500c41150510313420b0000d1025914030040850650303030081136860700580e01c0e00140840002030003420480d0b500203181c002411503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 398285188 1250 398283938 398283953
    0x313060909050603010e1509030c07151806020a0f02010e1309020a0512100b121213050904020f010e04240801050c070507030f0309031401050a050a06360504 69
    0x281c4070400030030300c107070b03540c050a060a039141d81a2034000b6a0103503010362901d82d441c600d040d40045140003528a4104400c5185291680d6500901d09280c486c24500c042030750003c40e481b2452114100b0400c24074070703080c0f0280d1034409500000e4404419481c0311000c581c4903984600c0715401c0200340440000003114840002c20100504a008442204010400c2d18200103800d80101d10640280744541042c17542902a1103c161029082542c100301d0048043c7e0034441c5070560700e807180760541c45804102a100380d21580e540918042e8401030103110250300c1e10f1000c050040c400382480f01c41001071501080041500b51700c3c802c0301c44584c5980360a00d54560200e80308480d084002485142c0b210301d031405031403244040042040e44102000c10010343c2085044016a00a0070b003000d600da901c0d03c0e4540c40c42000a1104802d0759920108002170040b0320172180c1200f00d90004002e0075042026402c1030a02c81d040540107441500548203417800007050300051503c2c4400700780000e0915141452 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 398286438 1250 398285188 398285207
    0x21090201030b01030213050d06060302151305010306150807021501121b05091b0405060a0809160503100e0304051003050105031e070b032212200304090b03031306 71
    0xd001a09145444040e5803090003541c1045140100004521b4076183c20400301c041400d42c2180d0558a4410010241c0c5e1110410b044499051803065500c843c08408140000d2007a00721a042c1441c220703050258080d00c40c020705588006080192035612041000d074a415813001000f501c03401c03050000b082c0420428540013a50303106803429182c1499140101030f0b20305590082c107810070800030000700703d807180a14228070803220070320492515441c1e501080071507005e00343d5800468821014001207150070001c5090301140b80192030301c11800d103030001c0d0701d40f08640b42c00f6000c0713900c2d031111041b4100e007442164001e010040104101005520380640681024843c4a202e4010510601c0e6059114590814590100400740c074500327040c48400c102540025223103031819209015804d0b01c241032a102000001e000d1090703d01160ba120000078141d0400c03007000d500c844000d059444c2d40d80e900000783ca058038100000030038020600404a480c5005806805031410201d2100240c00f036000701800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 398287688 1250 398286438 398286443
    0x2010c061a10020606060d151203030515031b01081f0305070e06090c1e07060e010b1c05060a180f030302040603150e15040e1b03061005090f06012109 66
    0x1a81c02e1048804280d80791001269041e80000081006881c00030b450351014605d00c13030b8404a0024030f030b181e01c0c10180410445000b10082903541060004100d0364004003445502c0031801048070701940310504080308c1010b0001d0381440000e6010500e02d50b0440c503e00544503c1000f81681240d0b00e0034402e6840c1030a108001c0801d003210045041820300c0044188a816000e281c5444c1020160400b80c00c0500c4203400c10780104207014142c001071450182558200c516000031595180303140c10060344040030744114079030310003245000d00011030102e045a445514100c0004d80314502000390f05401c2c2d041c003001480c0c100b281010900305600f5902400a464541d642040381c829800d48080d580c502c1400303032101e02125032001034a0395014011012505c140540046516910520994603000ca501c91220700c2d640a0745ca420401d003010004a61311921180c0403900c400d240a0108050007070103003a940e41d1801010008000da4091880c02d0b0b00c4030b440f6444d60710100d5562140c44000e00b0f0b0781604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 398288938 1250 398287688 398287699
    0x912081821150906010f030f0809090106210b18040f060926070312020a0207050a06020a02090606070c0e0406090b0a0e060a060b0a12060803040801050402090115020709020702010c061a 81
    0x42103039000f0000d09581a10070104280300518255101d40102e0301314500200c1341c06c1c00400050441c0c1d11847c0c00280280f95941740c1a0011940180400003500784414074410145415800c801d01e0740c40000c40c4001c00880f00c1204402e494508190b07481c5c00103040c0c007400107418100d4440401c441d61200e4860084907083c04505c410704940603180510541001600180311992900c44120141d402801812028011105a59034030b82c0490001c181c25805480035811002c450780c00d6040051005a0102084407000e01d028010b9664444005e034a00074442c1300040c0e500020b04015880e80800f40304c4d508005161030900d011200f101c050b000ea06d001200074041c03900403171400400fa0086809032540c80080a040a41c009811200668098a02c007652a12803800184a900c2807004102501010b00045040e203464010311640b1001a030000d41e5508a003d0400d04043c2d0200301c0100383c42502c6030259a505140c0012509140b00f034001410b15441c10251144081980d80388120400c001d848 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 398290188 1250 398288938 398288941
    0x50c1c091203021606270810180f0b34080903040e01030b010306110c060a05100b0d05010f170604080d06170a030f0f0801140301060b0c03030403091208182115 70
    0x417000700079a078030030120603500900840c0141d80141d000075000004c030027010030f12900c1c56281e040d903420080d03030203850147d0300c80c090100e985200003c0065041c102400c0c45600c4213001c5c600300c0707600740c9483c00100b0044603e01080c09400c0034000c0310000c00c0a0750303091144d940c50b814a61260300c000c1c4000c540c0b441c07502c1ca2140b030b4899040161380d840c1040740007070300e0359075988141c40c00070340b000410f2450350306101c2070045100004c05c800f504414040c8000001d9540c14001c008003480056001440c4402d030321612280100000900c040d8010350084803503031580a0300c18054054065a0892240d68074900340c0ea201c001c5c4005540a480ca01036598110350743c0070aa403c2e0f44030f94002270b140340003810000c0140301c003030bc00ca0001c203109540580000f0f0031568580d0403001940020070750001c0798000005004c04d041c3e03c015040040c10b842c0040c0042130b041703079441c40c240784070761000c100e29240914016922951b480f6000e1005881808000b54284045445a511000340d51110b810146400c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 398291438 1250 398290188 398290247
    0xc07081014010f060e0405040c12030306080c0f03030403060b04110705030304030e010e131107121e08010e0a09020307030203010c090e0f010501080c030c0405040c050c1c091203021606 81
    0x1020f40c0111201c41d11002024110501031001130040140103840d0940310140014041000042d6111464000d641c002021805d12815904209402e00c00710f03c55460920b405072030f5a004412141240c0c1e010344005003080b401408103000c0d02420328201c1c0300381c20100e804d1007030120200055105921940d2100c1c4962007000c010b44103100301d0740305190030100c081ca000c14070701c4041e03200c00760001c040010039041000c03a54803905920988001036000500302044018547c0003c185071030280303000d0402d403101e50b041508500c0c940030020031010703042e0749803100729081d074805203d20405142c000e03000740b00e0049400c030041d10001c034071b10400941d690716400040300004101e0284d03050b144140d5806130543c44550002d4400d4201821400302d00c1001c200016050380c841c41116646202d0743c03a201c0d1503000070507800f42400e40001c040c60090015030b80c1001c055034404400400d44121401041149096080880c40e048001c03a56511948030300e00d02040c20390300101c40605110101007001581c0c0d0412 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 398292688 1250 398291438 398291459
    0x180b1c0c08102304090809120613171c150b07020a0302010503041b152703150e03030f01030c06020304180b13050a0c0e0a0311060c0708101401 63
    0x40302c1d22020008400418026801c1c0d80d68201d140024200d0903e410380c61020016003280d05240b41211960f100003024191030411941c607204903895a4064030031840e04800c90590083c80c00002804c040528031652400841d210558240318107800107101007590b50203070600100340e04001c2c8595400b280300300203955801007088465155000d061305844601d142c0c01595190006002126480c0c0d191900c0c25014040c4110b07000105181442e110b04003600313840207000204251011001c041011a049000d0503c414100302203981c0320380400901400c0c400144020080b0615540c2140000000c1c841188807044480381a2405150305c5011940e85800c20303a541e203d588640100781040202c14514580c950b80601103105d0054200f200c000394403411003045131400c44284510681e5040a07030b00a5600000a1541300c0f41550030242c09401c540b1610004980300010610440000444900c584001d2203083d0044c41504111002c80144039071a001074030382c0d580103600c03500c0c4240001612101c1e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 398293938 1250 398292688 398292691
    0xb01030e0a21200127020d12110a051c0302030906240603040f03030f1107080c1005010e0106080c03061302070507080d091701020a080601180b1c0c08 66
    0x30480c1c0c2c0c180d510802e28046652502c040c0b14006025400d41e011a012014043c10031102030414000140a1140190715941084944850f6580385d190083c0c0c0c00180c135090301000e00070b0742005040440b186a4801201c2411807017010303940c00c0c0079090b6083d0411200040718803c400c0039005000c504400c54400310205d01007120148510f9000101082c1c90060000314a034003500a400038040e200701c22404101c01e64001c0d5004c8a071040d41c0f4115105041c0d16102d8818030fa21a801d01340428441440c1707901e114080da00014002ea00e000403402240c410400c5154401404c1200921075507944486541c801082446424007291141000a1000002c407044038030650009001c40da004800320340240082d040414100e511703104810010942540400050084010a40d03451801500340300d9400d143c030f81000702000c002e030700510207840c0240d0080a803550000c002e18180e1001192000e880090050139401820341901c000340403504648521080904130004600511400c001c0e214229981c1d0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 398295188 1250 398293938 398293943
    0xe0f09130302030906042d030503030115051b010204060f03050912070f15060906050a0302030303043002010b0f0306150112020d020f04091b0c0b060a0801050a0b01030e0a 75
    0x420005000040d180980c00042406441224100318064000c903c251b40540c21060850000420038030503a02c140c40103000050800c03400324103251555903110341e02e00042c090381d08403503001002202400c0c4140141d80510030ba48c004252030001c0f2a4105000350b00c14010100014072303d14141600307501078041d01d03000f800e40c3c02c000d145520340d080c81000150012a41210100715180d0342d2004a12082c0d0302d0404a104001e0001e0080d160025800450310f69038803003405601d50840800c0540e402000b90b9500940011031103450031003501910358803001c00f44420b5200250f142c8101d20709541540098a01d1200b036403640110b002000030076588000448401a0f044d00200c0382c000c1951042c901c001006031408405418031900640a40c1640c126200801d01d00380c0100341040352074120300400800c142003140e011140190010020110416500701400c6c0d80034842c08250741d5252101480c004008540080005040072400e07200606041004030340047d0508518018004002c26a6414640e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 398296438 1250 398295188 398295199
    0x1306020c220b010302090306070305010503060603210a1701080d2019050c1c0606060302090604140f1e030c090112020405040c15050a020f06070903031d0604150e0f 72
    0x101d200310000141902e80702d100d0400d0303000d00c00c2402c00d4034200b0526005021988010816604203030030701d031900e20000c14551195110110182c10040d5003004250304c40d0600314041e0b9511922101074a41105140c000103500740083c00002d455000460842000109030f40c58030700001039080700404002c02640301608682000c0e1086040c06600b2100c0e01ca16031142c42540c003100382d000300203030114880c00250030740142002c0202003000f1040c0304280c050011406e085042c03805140c0072810900440c080d40c521301705581d200702c40c1e66a400404407a1550300900f9280030910b40d95440e80c4021000346007a0003441405071a076514640409450305a6003031207030341300306c03586180c0812019080107041580c2c00740601501240000c2c0d83d1f00600c90340b8260740c0b074413a92000202002031400c00d041c0c0c40300b005500800c00307100d40f140e4804c030349404803505407070010000b9103101c2030703140140444550f0307950000307001900040d41204518110302c404826100c540307209070306070240040c9044000c0d1081d07012 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 398297688 1250 398296438 398296489
    0x60e0604090506040906050a0b330a0329040c0c05030f091206180d0c03080a09140d020d11010501030b04141f050a1b2c061306020c 58
    0x3401c0d5484158482001400801d61061680390b8004441c020790303007607048503104c00e8861501c0c1059154540c14003102c40b038841c100520441811168072100351740d2040700d000040c03424038082c400c0e000021413402c0000554502e0000c507c0c1310381d50a074680c01c014090b03803c0100e140e00c030602442c10300540d150800065841c020301650a07444a85c8a1f2002d40e903c1860b441210304804420011a031207801128580042c5600a40880d03107802c0361103103c4030800078038003602c100281c0e128407056040011150003103041a1140340a04040920004081e4507200786450700c0c0c0e48a40c0003c4151014015484101c500c1c652446282e0a0328002d0002502d4425101c01040004480720205600703a03540005580d80c44c0b0b024064035038800301c80c4414014094680d000d0000049040c851900b94200b551a0b1200400e5540005060b810485240c00b07543c0c08101280702c005070990b00c10107024003000300702d5540c42d00e1605c5da0700c43e480c0e01d81c045e036801885554140700032805c007003005000c510b001c4414000d60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 398298938 1250 398297688 398297699
    0x120302070b0a110a060606350c1902070303030e2107030903021008040203061e190b0a06020609070b13031203090803161d060405010e06130b040e01060e0604 69
    0xc941c00402c0c8081040a068160450040d041c0180c81c0454031804011030000c0c58032800502c40c000001c028031602802c11002c07000002400b6040c21745a80d0440c941d00142d4460b1140004d03809500d1007102005074540381049255404111801074038480e072810099034100600c0517075039a241c0803040e21808201480300404c4040e00001d0904188289031210929440344d0109054401c1003212501152580b0103000031442d041c840b5a60190000c04c201c01c1040c1c105554505030798001d0810030400f0a507841d00e280c120625000701001d42c1c8040c2110040c0e80d51480000d6441100300c410701c1407801042c0000c0340c6c0106520880e154040c00a0420003050b0858a817a043c0161400441c811305548903641000039007100c000e180300307e40c294041000030032110000361814001c1d00240310341c14003516006019544002c01e1340c060302e2003881d14291040042e000f080c902d2040130700074018030800312000580c0d4111100244181e031021a48444c01d40d0381d03440241c0d408045500b01c0e541c46101400103202 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 398300188 1250 398298938 398298959
    0x1e06090d141b1c02060402090402091503060c3705181c110102120f07030509060705010608190503070b0a020d09060f11040b09010f120e07050a12030207 67
    0x4040312403107800c0c1d18100301a500b5882c04044a030384244281c1140040784111104407804600018460019110910b083d41c00241810801030000f449581e1010109813a24010b00c0c0540190b10094119280e602300310180e00041c1c1c01200b02c50441c1c5ca60209813950a50503000c01c1d40551413954815920884090030599481d044070403202424140c044070380f007603039640c80140404034005100c14030030300450f82452000503400c0c201e01e40c1550300040010303203028031610448914100c040000c0c1d0f210035007860110f600e4400c03100403550005002c01c2e00350501406504c0603040380c00c0034048841d02c00140070001480c004603940640030380c2090200001103084441165800001100f00501d00441c0b090404d0846541640c01e5901b40d80e17603855500b0300d018510507120540c0000c4c02d02418075203041121441072080d001c00504209019010301c40080c0104500c1945880700401030200e0304140d00600d03500c3e91a841294400c106182d400903840348142000700d9010303090b501401c4014101b445803035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 398301438 1250 398300188 398300207
    0x509040201030518252301030c090305160f0e0906130c15020f060a1e09060209060f0304030f0c030f030905070f080601050405090d050a2601081e06090d 67
    0x1520404480b4001c100180107001e640205c160455480e14400c12820780019401140d8018014004054103079840d08030000703056800e03181e02483c0100b0017480c18141107a9602440d803008020344a40100700301210240182c10042e2542c14000114a40d69002480000300c025203180b62581c01c01000b103005070803078a0f16001d4147c0101060710300e465603a0369400032001003501c0540143c014041c9519481414020180c04ca00d52040c01d000b000710304483d40500300908840c10040950350801d0300c003000003c1e015110070000040ca065240d0000700000101c40d40b04a500310009504107101220f09402040902440e90b055520704c3d4035684680b00640042040510586403840388400c005250354041c141000540891006403403154034040a00042d120050070b03400c80d5410244024100d90307071003419103c2219452500303402110441402104515800e004000701e41108000840d503030340c00060500c01e42901c164408c0c409204402e440392503000586902140c4d40040070400701d1540315204c102d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 398302688 1250 398301438 398301451
    0x91a030c10270905060901080d0f0309061401030804060e0402030f0103120903080f041a0406050f03070509030d0903050c01110d050c01110705010606090f08030909090a050601230a05090402010305 86
    0x840e01110b840080e840d050309036a0002c01d03500d45940403c151800c1c602034007401015484020000201c40d584d0251803d007411201204041d980c22a44080c4101c641050240b60416071854585503101e08283c412903000380100e1002c10103c02010040d424184212807042c0e644207100400c0d6400d6648000c800c4550a09003020000668004400310342160024014400207100302550b6910384400e540d9214040e240400910380c0500040010300e41010441d105460011b105590704d5440c0002900c06014140483d40c15114150543d01c5441e080032404080e64002c104690710048070000449a1059039600008135410100030740b080c05010340060818410020300201e5100c0003408103e40310b40265000743d074241c0d10340c04100003141e0011031000240c007030301c0d51400704a070902d05040e56a11410600c0340c01800707500700241c084c100034010b2501082e03004080c7c0704030b965146c03002d050301081d4a85040100448000b040c0640c501818120111040030301020001d55075600103400400006003071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 398303938 1250 398302688 398302727
    0x60702121005010906060c02091305070f06021005060f0d120905270906041208060a0306020a0f030c020c030a0b15030d120c030507020c09040501060f091a030c10 71
    0x3040d00e1682401104404825800c00040661415a01c0d4090342c0403540000c0c2401030712440300300980c540c5242c0e01e50128040c07421003103200c0103242003460714803203a02c000c4504002400c0443d4299000c11b0320960b000a048052046448207010070184150a59199070322454058208000134000f4452440094240c1420308540d40e0340c0300403031403c03850104080701c18150318442075403000b130240409411004460003031050340b030596100360003a048a41c0365400d20903084001a06952240049000303940d220130190f4a034100030341c001e011080d0070201400400d0500e52501c2c01c3ca0b100240504130284000c008142c81801c5880e83e00010344050700800b007080c01811100c00b01e440410110a44085a07500c1e92051805034015000b140d034040c00e00d07001c050a080a1010280d8001600310b81888102c5020301203843e80e03c0c10500400c03c590025035819554400020302c41903903030081c0040b0081c0003911104107202d808042c5c0300d0400d165280c0e07001c10341d0340004c5410351182d8460680540f12004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 398305188 1250 398303938 398303959
    0x3071e0806011416030c020a120807080f090409060b0a0605030621030910170f01030b04080a0e0306070309020a050d1e110904120e0f0a1203030b151207020303090a02060702 76
    0x8400044c46104100b0360200302080d900304118209018000000c10074003841c909501401c2ea1128183e104043d0050b00704080400c4023208203c06c00c00311100140005c004008082d1185461005000c03261126441850858000a48140034070122403007400014902d110282d01c02101c00b03082c502240403510366100602001b007064541c407050000d80180c03600e42c44003645464051145540000300384155140d907100041001036120284141c1095000c41e0017a2541c2c5640d03000c4401c6900301248035894460f65003803000081e0141c0c440e0907145c0c0241d604a00694440c0c4c207120303507052092030091001d9510155036100f0540451981c04040c46400d00c41c1500c060700c0d0006540090544040d2a1140207502254010ba040b10300308483c4402510050b06001c1c45034009542d0030028807543c0d2032a15004c0841081520944c031034408003070010484501d20307090039044036141d0480d40c080701e042035854000c0b80d0708900002c1500c1c421038902e00209035030206a400d0001c1e58100e41001ca070002e80f01380 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 398306438 1250 398305188 398305207
    0x30b060409021c060b0403030507020303130e060411030412030c110a030215091614010c020307170f06010f1a07060e0c031b0603180715030203071e08060114 69
    0x10003480280311060300543c4400204000c078120440d5054000d60399442d040d070810400350410150340840c0d4241c18010b03221405c60022908510520046080f19003000502007080d20307010a80314024032041e10b00f00700c0542400401c80b42c9101c103072005000c4020640350305450920940003410340322803e03e0103801044034a400e55103820f1242c0011405a00070b82e00b1021040308109186030b02900c0342004117240b01e24400600c4071802c25014807000a14000b401c1145640101c070185540d0360301500701c85c0100d9407141c010032a2a010319005240d03009030003000404107400200305050303a141d602c4102c100343c64000740e00c0c000c100ca200e5075801518180084004100e6a114100201034220041e2012020000c100350400b40500e901c44009540b9205090683d02c80790141da6118071446881c1c040c9501a80c81203280c519251320520b003500303d02038040c4010b40e064018501a42a54644010300c0002100000741103071112445e8000030542c1d000a2443d601c40c01110605d8010020380c680703402c4040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 398307688 1250 398306438 398306449
    0x109020d050a0b06010e060307030b0303041e180504021e0d0803181c05040e0c0d05091f02190f0e1e0307140a18060803030f04350a030b 60
    0x89015075807a0000d1500ca42444245486268040c400740703000c60304c0050000010f00340d070102600c079204259885a00f02d610b031320200f0845015113030480070f51040b40460710380b28901c0445802088070700074032030180c100c3da16094001c45010310750091040080031003a070500c00140000c090020b6001d61841c1d803070004602c1e000000c0d801b4541b5516043c0c12800340e22050351070140345040d01c2a0030b00308503070724480e42d81c0c0c40010760b4113079001820f41c41b06035100d0001080366405804118081c0034500803c1c0501c2d91000103507006120250003140c03c03131150041c0e0080c2240115a440d52812801c2580491650710944180c0c0890000381000c5e200c850440d000305100010b03188403120a030000b401c0c0540c0d1071908104207c0100003641c40713400340301032180110b4640c0103240308060b50701c4024035950b043c00d15650001c5024002c484101c0e916454144808121000300351015603503540902800311802007101e03030440d40c850048002e014002c81202008005134495107401080507030381c0003400c031140d0741c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 398308938 1250 398307688 398307709
    0x30441070602120706060518070f0c1110050c060a020c06011202060d090206190302091c1e05150c0301060909050f0106050912010203180106060804030804061a03010f06090b01021b1002010902 84
    0x440506084ea06d80030401501da960b07844ac3c0c1100340310949041c04000340704000e07008501d100c10340b03040502c2a243d24041e100e07405049020070450040d0001c0121564076075001e4200d981c0b10600b02c580503640e900140b0407403140e010700030f17403c07510400070b521038104640c100c0641d1758405084a031401210b07092010040312080306020010341c001515003020702c1d01403c880f48031081340e50100c001100c0e0b5542c0c0e0080524220305100700fa504480d003a07081c050203109109800f198450548040e00d4000d01c0c0801b168403d00800e80801c01039040815803100e80c1c4a106c0c4250800300040360141d007007010079950390304440b4a81c2c1d403241151140d858803240a001660165209818030000400081061400d64501380c06c031030100100c200400000c6136014120540003500844c00103081160b50356401c52041c9542c15843e0150f08140784c10803d42c10b660b00260484000143c1003180308514401203895041030f40704440e0282d2042c0103404603242507080100c6504090000180143d156130114112064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 398310188 1250 398308938 398308969
    0x3030e220504020a05011b02090603030c0d030605090708010b09130e0102040f030606140d08160c080a1502090a03110432130b0c0304410706021207060605 68
    0x1100c0c0709010071801c0881c010300140c0003d00380780c400310103120403920854900c0d403006807103002c50300003040d1591800c1c0f04940c022082c010944d00d0b029503400c00a00030740641c6c851140120040c1c00010710051142200c203050b10aa00103651400d0000801c1014059403910320715040c940d0f6600c0300c003d0413024401003005000a42441050306e1840c102881120080e902000103098510030303a0740d2666500320850010740e480b43c03140392190102546c07000c3c019020030300140070300b41086c1c0108103e800017032100d00d01440307514002d9007602250288410b90140d0380015800040866041c80081d50502c61a0300f1090041c00000c2c0c0e01030b0784544000e15824185088a484584d2150301c600c940301c181c502c80e400960701c56880100460740d520b1808aa00c000c21000c81c1031004004101003200008100064040c0c000c1c2d2280030201d0325546414a00400310f0300d04071403d100e44c0104114130040780b41022503805401801140c403902d80c200310550b000503400c580703080c0e9030701000c0303000c3d0f0341d0b10802c000700e5a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 398311438 1250 398310188 398310191
    0x213020c0c1e0105120c040b03071218020f0d0201050d15050118050307060c08070b01180b0111070905040c0801022a01090f080a050f0c013303030e22 66
    0x4007a060102e009025030280380e00080400072220181d070007108541641006141001c1d4507560800d00903080e01070303a0050b0780070120010a10001550294142c403150905c00720800419102c04a5140764003041d0384025081a110998001703e4030700284400c8842d40181001403a0041c004616401c5803d0050700030500d844c0d0a40500195a0200150120308640c811800c032076420040060b503950068482c0c441000000955181084021029900d810781d11160310702c1c0658664400f403201c00b00b4100d00007103041ca042030944040d0300c80d0108020315102c1c80064410541030030002c102404000b03200750f5001c0d840e500009130260302403004184140a106848402e80e42001c0500343c810700f01d02c03d0000076070511000d00d000c10400d031060018541e01c980500d40d5103007000e0701a203482c007034003201880707aa1300441c0720400c10006401a5500503240e00c88104014003515509000c1c0d10f1140c503003c40c1c2d141c42c80301400020702401c4908900c00c8018a011300f0001040c403001c40e100c207a541c030201c01c00d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 398312688 1250 398311438 398311453
    0x9190f03261e220504050a060b040302060c030c2415010503073204030b0f07051206032b030c0203040503120304020d0b132a09090213020c 61
    0x703036500300102071900307045190201c0794021103507900078003803601d0303242003803008903010a5480342c070404685102c01d041d120072001824a010a652411540c80f8a5005a060200180c03251900b403040b84c05980324441340508090440e02403103015080311483c8010b03440100300d035242e00302c0700b0000e05902001c6100c82d503810390440f050414407220302070400f0100030510480740b00180e8210301620ba102c1100c0c9800c00c048132502110103141051316140c0206207117190a9011000c0c125002041604e01680c4041200e446510312081d03444c0b011202c41c0001a820f1041400a44001c4d5a654001b03c000741290ba03005d6000282036801036000e07000d4548440481c03a0322400c03e415004401d01040c450000e9400d00e1315050219480d80c0d880401580e09402c0000040c1c215514a02900110764101145000619000325054100703040c54a007038a070402c803c0031075804120300e40d02243d61000119203080c0e80902c0d1200b080042c0c42d01c4a0100c0c0d00007120052034041140900c0a004070040074401030144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 398313938 1250 398312688 398312693
    0x5060a08190914010f0203130308040215131a030402060403020909010b03010501060c0515070912031101020d0c02070e010302150a05160b0a060e010b0f09030a080a121107050a020609190f03 83
    0x2104d140504e05c1caa054018410881a40204441c0da0205501801c1070300140d0340c0c07480080c103440071340040c800345075030701240280d07906182b9201d403010b44100e1b007800070010300c014a43d41064042114000e43c4094108014070040c2005607555400002400c0046413224032500040e007074501c26005000000d40307d08900092040c1040240b01514400c0305500540c20900070040407248940a0341002103082c00d1500d0425100310340740c5005152082c001c41d15420500c0c0408c025242d084500e00051203502d801040041c2d514032621b04980d80103000042000c00b2001c064007981003048100c0a205050103001445041c00c051003140034400e0240e004145400c140c07420489595401c110210203120006007c81c610020480d61001d8240000c135480d81010400a03142810f0f44600034400701d00030a0745040d107600301066004030b0b600d08409102d502e0307039020484501e004202e00030303246a2044034a04050b04110009010703140d4064021b4500daa01022115803614503a48034140030348060404006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 398315188 1250 398313938 398313941
    0x3040519080a11090f04030923040e06040204110315040f02070206031302041a1507170d050109050a09030e0409020a051207031205070807120c12050309010e010605060a0819091401 79
    0x20b11848046030010541019180240408105e0142526044107001c4008244030740e04d4181d274414100500500103251200c1c0361a031143d5007500d0881c06182412030b101070b94450181901e20030040b84046461b2000b00f1030811000e40b6032886102c0384c650f4200074200168880340020340c4501110011480315080070700c188800c0320400890380810030503403400c42d08a0f03074403000340c0250030303186803c0c058503042d1604104040901001b50702c195064001400e03402e2031880d030406e9040303900c1503108000a0381d591407020300f55180d04900900060901d0070804281c50268080040f080c000390240030040d8881c000b2030300c220200c81002c07a450303108140820801a40020341355140e1a01d2800500306403555580302000d005404005082500300305403a0340d91442148074514441d009100c4108150840740c010706598004c0c0d50002c003035400c000340b10148040500800003141c1000d0310300d92a0007030b500c0f012a00050301405d10340c80c05030840c00e8943d078000540604000b4030b001c4c1c1882e4041c0d140c021007803030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 398316438 1250 398315188 398315191
    0x91107022e110f19141b091506131701060e040b070512040807110a081c03020405040f05090613080a03020703110f070510080903040519080a1109 64
    0x900d0107120301e8403214146150203501e07030714036003060701016440044040c10100b1060300c2c209640308150404500306804600da05015009004030000401c40c3c8101c1600c0d002e4044403864a0030b5150407040e100e00f040700c64a503001611444034012004418000780a030b50010569504240b082c0e0824000c542480d840c1581c096503040013003081a00e004e0356001c01c1c0c1402040030340548102e9001454460080c800c07107010700c6441c400c84480b4a03062901c0d400c1900564810b4400ca0b411800414860401d0705001c800c1c0c8103c4401001c081004120003402004804d0740c0d182050b4081c0400115511503008030380c188208040c0100e22032403d52081072801c0d03c024150710f00e0001c0b64140c1d5011903800800c5590f03601281c5800360741c0e05403d0030151459801c1000010b000e110300b04200c0c1340114082407240507030300c08503410200d8002802c42200d01d86401e8803c10040d41080204000c0b92800110401104070340c3c0d503401d07521039520003031541403940003d01540c410a078010302c800d00340307088940c16 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 398317688 1250 398316438 398316469
    0x7050d02010512091e0c03060c13080703060218061e030a0e0604150c0c0c120c030b1f09090201171b040803042c07030507110703110906030303061e060409110702 71
    0x1020102046c80c00207949070405020351041d003030001040655690203030380400c040e00d980c400715040a0354900d0030a00170b510040828800b590300400c012118030b0f1880489a006504a011020341840c0b1140c101480d400600060441070340d40181041c0d405050042c24031170f90050480c0c1131101116040b40c010b680c02100c5400c01c000074032402c000001c03240640c45041d5500491078948400c2103107005040c6160310380000c1c00200c0d04504205c51403203910f03e0480d8400680e9400c3c4101e40c1c0da105480c040d02c031b40d54030082c00b082d91a441ea0411182501708a54014110713290340d48016005c440c100322503407080d006060a6000001c00f4414914600d0100c402c0b51100221101030b41d030181c0007001032417405030407071040540b981c001c542c5ea94801d51602080c03400000546210b50f659242603203016060030301c00c41c0103481c4200041c249240100581c4d10440010f05042d203a4040003881040000c20301c82000c0c0e01070701c01c3c8008250b21100d803240c0103c100034001020741e102c1260042111549082491 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 398318938 1250 398317688 398317693
    0x6040f0b0102060c2a0c0301060f29070614100f0617090a020a060509040b0612060d0501110301120b18030d0f020d320103030207050d02010512091e 65
    0x30511107076400500c0c140d1210400c440d490311000c1170030a55075a1100c40070140c01620b00d450303400003520b00c0422240a00c0070201d0003080340c640c0e01d0ba03080801c0002c620944214081c400508006003845036280c040220208042518040c1c1aa940e01d00700c89448001248401c884420401c01d007942c04114005050000f00c8007290a20f0000014610759400d58a03852000f403800c0440e44440040120650a942c000c1c010401036071540d40007800c41d045810460311450400b28013802d5410002d0444036040300f200d507510320307542e149802c2c001e101c074138194211480e640e01e21091500c1c0c0c11800c059406411583c0c4003c841134680d00301545515409040c4000055402c2c0e2a09036002c03000003150328580c410003001c07400281c0302c08440300901070031500070005030924840c0100c8600400c0c074040810381301400e03811400d0807060b00d0020500309020040160b03010520a2065240101c4003c2101d8414540390b8a844500201003e100c07209982010a903403180510040500c4054081c03e00024031000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 398320188 1250 398318938 398318951
    0x2a05120109050609071d0a061e03020403050c0d260307081f061103070605040b100605070807060b0406031b24140705010608030423060405010203070201031a040e0606040f 75
    0x242075030006000e44040c0701c1949004400d0000701c804110010100910722081f4550f90ba0001e01060b04180307034014080103070860311000300d0091081e10305480d00b100082203440101d100707100101c2c9441c0d40a071411904901100b4400a01d4418200030074010303245c1c2034072820f00070070103460a480039010195809e0540e08070b0b117000e100c1b450280101c441038500010880a0524628154828031201801160a010800050200280145024101c0001301d5005140c0d200c900315103600030305100401390f51041240c400811038540004400c4070300140700041280d5a55642914602920004880401c01a00030086070140300d048018040c4046a0424901d2070400d004204540130301c5200c29000004c01c80c4414800258055005041d251084940c0d0340d0b00c0c3c200041070150303010480030020912143c006a1402c00105640071500181c00850900d9001d900540103000f4886803890190300110320303402543d86038001c22003c0c8000c40060051803e1584c10700098468031341d2210002800d069 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 398321438 1250 398320188 398320201
    0x10e1e010f0501120609020f030a06060e010506120c0904020f19080604020f1608160317070203072301090b0c0417030304021f02070f0608010504150807092a0512010905 74
    0x4803d213901a90100c80002e0401c5244000354240407500d079859014407855484030200030300c551107041a00d41c41045061640e90710010070140b0b00c01c6243c0f40c1040542e65010844244621015058080b0300074005804d080b000001282541c1001d544842981c0c9042d41c500b0401d80c01c000c205030000020b580651a10f00340403421612482800d050401d80c82483c4101d105004008065903145580c458580c4401011410700030025042ca1404103d64000000442e060301d00000803626600e41c001c005881091081d051002041c94480d80ca05580d525060941300140560481c1e40c0325030140c030002500c0f14184540302c055074440354204c9295030b10410611026940d6081b031002200f2402c0d6030b148100906030b03c02c900303100a503032104121920065000c52010707000715405040e104151401c00036405082c44d000d501680510444089400904062042050070382000884a4a80d20401c0310814281e01c0d04000107007601014000403004100f44404840c1462440d00510b8420014442c900346403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 398322688 1250 398321438 398321459
    0x3060f09050c0d06020708030c09130b03060403110c09010b03090c030102120408031018051503011505280f0303200d030b0f030a060f1518020705010e1e010f0501 71
    0x80e072820740f05000d10a000320401205404840310140d00442198813424041094401030300b0403102c2074440d41c00a008002c3c1c030f00c503912481811400041c010300782500c9546055521800480c00d0801324010101041d8058660170041c60082840280d4a80d6a180c81610709040041506070144264010003424201a58521426800513003020005e0b83d640c07520041e500e10800d65030b00210a80b003500d0211400c2d6011039012a10413a20507440f40c003429441d0040500301d41e052100c2d80b68480000c0000e00082c240301c4400300b80800a81115100e0b681d0000c8501483d40c1c0c036034842c90031007001c007106004265201100322040400c1e020346589610200032000d45030425900094201551030f10303026501d50701c014103134105440240a07140b10740c00509011002e01a55001c44d4410380c20006007450170b06c014100403045403c4050140d40716680344226001940c00b00009440741d42d01c4160b0007500d4141440001d15420701c00000012021903c000c803800d4400c1a2000702c0c803107107044010407440c10380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 398323938 1250 398322688 398322703
    0x504030c061815180c0b040503010b04060e1b0d14090c040c0f0c0c0509070302030402010e030f0a0303050603011d07030302060709050108040323030a02040e0105030705101b0b1003060f0905 83
    0xd5183c04540041403070380280c0320f544c4c2c404015012000e5100c000414082c050014000e4690582c000e00c60051004180030944000348145404c640501d0b0000c0c2c50312605180c001c291243c0e10307802c80c0c074003034128041400b61241045c910800c080c81d40c050040e045810040c1c603400c1300c002d4609004001c880d0101410818103000034105103d05020704038108000ca0390301070003800005000c3c1c440383c181100002c00940007260304a0204170710680803066450300003500394292840800401040006540807400381c00007404864040d07407111007444003028200115008804607074000e15030039246050007890b044016003000e052040c00541030104d13076880b51030303141d101ea014145402c41c4264602412000ca0604c42c2d221903201c0c011060000011139600200700302c421210409000741d88890030161280c00c0383c802c1d41d5000070400400c2075140d028583c5e40c1450402181c0c80340514400351141094008102c42101d03003103543d1b034024002c00c80d291003231003d001e100c0c07007040080360603d641d1305c0e0760b8044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 398325188 1250 398323938 398323973
    0x904230a0b0913111225061107030503033720070b0f1305100204080705042c030f03092812120e07030602040303090618050f01030f0504030c0618 64
    0x43d0f000c00c00d11502020050032110010042c2c0c40e41000384001e40310341c21540b8900070080000c8d04202203254011001130711200341c0750420003452443d102c28007034500350025074080800881d1810002c040c03a5030018101c91030b4400003200071400c00211600741c0c2e1048071540488800f910b01f8042100407456140d29640d1248018003401040c0d00c4088126001c2401940001c080b48111124101003000c950094011500e150381121501915901004103607a500c205103406400c881e400c074240c89030002d41440b0300e00e400c003003a82d20f0100010000402607200f02c941c9034070b40e40841062891840b039484012065040d030740401f00002d240e90740d6240c8ca10030552403d41004030221602d16003000a9008010045e040401c4602c0303542d80c1e19110003e034100e4481540440c0300c2c40d20001d40d29002e0f407000800d01c0300c80301400d6001400c1c0f03c10044130005e0200001d040550f6946d100409110a2003070314003883c020f44550780f6100f04da1170b10030203445c82d0300740b14200311203440d04400000348007181c03034264a05c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 398326438 1250 398325188 398325199
    0x3331a0702040f020702090a091203060e0c03060a08060406060f12020607020f01090909050606120f28060504030c05070614340f051507050904230a0b091311 69
    0x100074a0840c8064094124041e41c444880d02c24000208d225034421a50709100d031410f16a206403402c3e094040715418490075184e40121800502106084001568840001403595035078945508404d46402e100320b41c21509643e880c00148425640d44240a0040100645286d84000d840d404107400d07000d5180000d0040031144040042e980c081c0c0813010207817450304400c100c04a0b060800b42e036030b20004e451190203084001c0722011102c40c003050500545201c071000b40f000440c04900001580c1c6074009603540020512410b80010741103001c1c96000e00d00075a41d80042011508000d0305114a90b80464107100650905401540031442030360785179178091a4062000c00328410f07400340001c3e41c1217100c299100d0415208100055080200c40881c00752040340c94221201c2020048040190781c10400b084090109240c646802d0700b0100383c0c0c4809a443e000a03d035890748403804010280c0b0500b81da03503100c156140803801e18400282d4410741a01001d0098811034580d8403449003050b801e14002c030b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 398327688 1250 398326438 398326451
    0x2030118110432030d02030d1a0d082212030e030d140702120708030c06010f06050301121407030804090c0215220b09030d0c020a0b01140103331a070204 67
    0x1140c41d03d0102c003881c5809820344d80c40f090203e1000703440e0340c8107680c3d00800c249400c050745441e203071506510220303d5000d48041c64441803900ca00300d60b90050310400ca03280c4801d41c24007a08880740c44440c4000c107456418446000c96916011b401c6540e48110140264007280c0300c000301641c00100d240482c0c800455442e034407411030000c1421081400703107116241c42040c030001021200080189001034510058403030070398076081140d00c400d11700d06c10580069004e0006100c410720b0250710304000e500c14006002000f071000326003400c0100c0b691007904c041740f0104040150b9a400d0140c0981245544040c114070f240c12401030408800c00b13812184144040c85000643d0199001c1000c03174207420001401070ad207051030070566a54024141e00c4201410040001000d90001810720701940d401020b003501c0fa03091900d03a04101c0c002c1c03010030341015228041884071500061620000a100501d90031481401d0300a00c4c1e4200259813000c0e25940100b50389021101c808820760b00c01c16070407507010980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 398328938 1250 398327688 398327759
    0x4200c03040504090b06010912031409040209040c17010b09060d2d02180d08030a0b03250f06020d1223010e0a0f0c0f1809020301181104 60
    0xc60003241c0000ba0820301d00301182c41403100c099585072141d1300998600140c40d407030b03a01c400c0c0d5040c41140003e01040c07040400404459210000e020baa09000e413006040400200009040e05c88110540c07020a0800d404005007602400c0740602600868400500e484180c2c40131903601d10030039401500266036004460004640480d220356203000d06110b40312860100b88050000358050700480500f00c03400d01c02e10340c0b281844e14100c413006401c03000041c1547e48040c1c941018202c4103883d940e041c0100c0c0e0070940c028070030314001c0c00070416914000702c80070f051400d844501b90590f0401029540040100b03090203910029030010714801000116040c100100105130051710401c800780200341c50000440e00c038145420180c031403200114140100704100b1580c3c001c580c90300ea40c0c100081e500501c8488154058100e43c6408d131200d1203070070038503941c4030715030800c0741c10a030820300e42458001c05940001200d80903500d40451104461480c080c5040c6140d007400d84580d0003a00c0c50600f0100380c1c0003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 398330188 1250 398328938 398328943
    0x91d0901060e010602061008061902090a030203030c0c090a09021c03120c11193c0803040201020f0705060301031e050109291501140f04060c020f04200c 67
    0xc00c002e1584408558551101035241e0310200c0d810840b6084441c0f000480d1880040d500c0d000d00139402903d01c0c00144450f0643c0654041c00c0f81c0d0b600f202c144100000140c0b802c0004200741040d803009003420844010030000e0321800a0006c503003e6042c103081c000981d840c440350400a80340c0008a850307954040c50300b558641160040b06580c46c0c60555503030429600880e9115144025a05440500c10350092400003c0c0850002600c14981c5640015503804110600080f40c4d40a02c0c4480e03d8030034581010401002610084030fa001c1e002c801d120855030100030302e07606030310b440000d0101d05050001040d003600051001812050000c0805400f0340100024944c1c190740160003400400184d04000740c0c2d52101003174480741c880a6540b00c000c910110b561381c0d070142c0704c45070302d81c00044203031001150018a9420040354850080041e1040960320600400007048940c5928800441038010005101d4030881c0f02030003030381040e41034021040d012a031210402c0d031484045455107000e02d50540f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 398331438 1250 398330188 398330201
    0x1201021c0e15010e04140118030e0310060314010b03030408060403080403030b090921090114070606051c05060106030504050a020111030d110c011505090f0a02190c0201030c091d0901 80
    0x241030102c2e030310012420b4500e0701c2519100d030b0b0280c210b40d10f01220840b0400c1c00c0328100d14840e11003800c818440d4000910815009400000c0102140e100102050b50102110301c0750303000b111008100e83c0c5252445000703015110301e040e4101d01860030207151040c01a1a288020801400c11000500140c1014082da01c080090403016202c28500e01d00603040950302c60310603203414064540303401d903c100040d01400300c0c1ea409006948100058812940601b034540108a049405a880702404901a11400c1448413850382025151300981c031103080c03450400e403040e08820f08050800c0100400308000050465240d6420701c0c02c801700c2104180ca55065000e03045441c000541000e2010304a0188a400f420142c0c1000008001c450305000c1050450301c6688a0107411400020001e44500c417480c0109038025541440917203441071405a0440b18803a503101070000c5000544250190350703140c490401d41ca086401c203640094180855402a0400580010810a252400203c08003020340000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 398332688 1250 398331438 398331463
    0x30907030b010b0a020114130b150607052103061e04061e0e010e040f170705010903050a0f08040503031b09060c010e0607050415030e0c0a08010b1201021c0e 69
    0x55841e075844034218440ea42c0810115001503080036a007081d294020710060340100581c00c1400407102d00760f0ba408000110007003c3c8940d24103070780840f201c0364a620300101621441100603084448213038480610700c1103200a0000200e10500030000c203030307d03200c100018182000002c81c2080f40c800d000100607101341e40204020100740c405100008650400a1054524902e03008141e0703a01c81c1da0000029000b160090f0400f01d5607010040440c6008650b508152014640305207015080d4440c242076031200c4000701c00181c40010424000c079400007024903010f4691810420038142900c0d80365580c0005400002c40881d0201110200341c800002c44000480141155445651510680303000f04440d40a002c0c05000d1600041c4010303100d441100e05462a5220848030b81c05040011001403a02030180016482503145c94066591107441d000000d00130304001080e140840000d000107250041181030160b801071180c44040c030015810322002c050450070001e44504410304131482c12004045c031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 398333938 1250 398332688 398332703
    0x21c031a0409060b0f0103180809010c0b09030406090501020d09090c0504030b01030804150f05040320030a0506060103320403090e16030b0d0f0210141c0b040501030b01060503090703 80
    0x240800541341c11039800150300300e800c48156940400150151806803085041131024480c02e070b00040c40107009841104010300d044801e003040c0359903a844090050f105038140350320100d01080700c00d5000440d000600828070150041450340301d00541088000c1c01000c02085d122088107040e01c1c0300d0b8007510b00440d00944421410b5030350f800c02d00307899441ba0040449100280500ba40124007a45c468620325a503941c5283c40d00d0714548030311002510014180b0140d5541c3c280ca9a0a99002c0054600301c1c0d01502c007401403030a10f84005000c842c1c0c110f21440003100668210f1040a00d022018104089011001d0441c1d03034440c6412030380ba1805800030340c050f4140c2c1d401e1005404a00c800c0340c503580c1c000d48080000590243c01c1001040301c1483c001c0029540f84115001801e040f01d4070900c00301030f400d1101d105054440d10302c0f83ca4125800e001102c4400c10203446114425000c0d51036401c00c01d440407c900e50658603101c00a5405025100034403d000001c035040010411250b001150404039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 398335188 1250 398333938 398333951
    0xa02162c0a18060e070501020307080706051302040c0e012709200703020a1e0b16020c04061403070905041106030c04030602040f050f040c02031e0d050108030910021c031a04 76
    0xc089004102c141211003441c8290364000c0303047e50000007110112600a0803441c2002c6003079603505d020389001403881c42c8600700221404010b0301c850289484d100b049031580300070590520b0004202c0d8001c440005442c46107550000d90404aa01c1700d0710668510310408640d03e04985030b0922401032a81080c80014000150b4605040e404a142c0b080d8510a0840810104106080c000c11a02815014009208031808116582c1c0c3c80318480191415a006030352000550000090491701c0640c0083d000f40c081c8a00311404e03203824002e90307010340304c6443c04214034201516124010280340752203502609001022441180303810050b2002543d0000c000e41d915074889052458a03181849514043c5100305001c500918060181c112003c01c164015403d05074111814001040d6085900041034000c0081c0c01040394203016190180c40c001000b10f07503e081c3c200503c2103804c0311480400854101094100142110840304d01a600142c41c0201d90031012880702c4012008420344194000d01d0184c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 398336438 1250 398335188 398335193
    0x41e14060a2003010305032b1109014107060510050103062414090306010b04080f07080c101106070e040b010509090408030405120a02162c0a18 63
    0x410031191061062010302c8081028998010207000a000007007494100b484120800c00341c104c0c460300625684410950512036611071181154414101100d04100009400c501d65070044000c00140141e01141141085000701414200d01129244000200000d00c01c1c43c3c800020400d03610300c42e4000b241044242088405195070420522030180402d040c59000a0030b081c580d09813044105070070b42403403054039a00701c0454200041101040084500303110440e0f2030303102040601e0103072000c40c0229580700d08240e112803030041150300e1021070b50302412050040d10404188081d21003c15500c02501c1e40c401501030381c0840d04016902064481d4804110702103622007200c8c00303041d4042d102001820541c500440e100c0c4600700c03980c0c0c0c00c01c02c540041000170382d8000c02154001c3c0070b501a81c80314103440540c1c00c45940402d82143c0140e205000c1505c02d4480c9485c030314000c1c203840786041031201d81144001000d000c01106a0003210280001610b1403029070407605036030003c07040c542c10051180c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 398337688 1250 398336438 398336441
    0x1091a1507031e08040308090718060302031e030a03020d18051f11041e09020a0903060b0f0901331107090509120c0a0507090218010305041e14060a 65
    0x5120a800140c03204030381180c048070300224580c60348404e03929081c407991191419a4a60405070580c0b2081c8101240000d42c0d8000c00006070102a0100012071201e1650040516000d11110b180b000d1a8424400050840c070010803500a10824100941c407090030141f0715008140032203000c00c11001c802c183c0410410b022420096076403020791141c10312454100400c00311030b101c501c000c0612000300800d00c00b082c06200000087c00802007030340c4040b521280318a00341d0f0044e0f0020b8001c03550600c0d00b8001c20841e4044c1c041b104206841d10a10356500ba0700080c445076061040303207908034070750404071030080010301085c81100c1002c8104d078a00c820b000c402011440c03420441e80e698000c171040403174200a44d02442e8000d0ba907080003418240c5034103417010b07030640c8651348002c40c6116098950000400601c0303503000404903840b0050710780c000300100014071711540d60824101450002040b000511a1261140003c041600c0c007000407041e00e00000e00a140c500321a6061203068200640603045 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 398338938 1250 398337688 398337697
    0x50108390d06020d0c08070221090d12090b13150e030d1e020703120509010909060b130b12071211040306022508090112111801081e01091a15 62
    0xc5481006401d0f120f00d42100c0c411001e49407e001a000303810650114240d84001020000e00002280d20704420000058884081c1003411036011085901400856812800960082c00b1901d81d403464200b440100840719020790003410301103020035280c028468440c5000070b018480140c04c40301901002c850142c086103090f89500100d015200084054503c00b24140044991001040c03500030640403090b202604154450390401003080e00005050b0000d0050310006d00f090700e01d55680e02202040318110304215005241d18420030050901120304c84014035500001d00d107070150f204040340d401000604080395810241d8040446c002c420b01c100c0742d004001c414401b100e0303000841d0784901503140910301c4880203041041c05000b10040c80d4000c3c0004030a99102220024072010344400500c52500108045034904003400078401107541c01a0020342c000d0220950041190180c0c0b50081100030140515610261aa0851760841502d8460000d410400074417201d0b40b01143d02d40010701c0d411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 398340188 1250 398338938 398338957
    0x1911060c031f0b16150b0906040c050c0d0801051503071b03030605030a080310090b01081902090d111513030212010e07230901060e0f0a0503060a060306050108390d0602 74
    0x1044403103100e0090f490700c503201c1d101c00041d100d2001230b40c45200304001050359001442c01c1c000c041091018090003844150b00152598075404e10950401e07060251a80140d07408030082070040080c800b00f0361300401038860094160b401100303030b040d541c42c0c218043e02d540d60160340c25200c1c0d802d000c0c041000743d8003d5441007000d080b04c144a01e60700d514600c2561217070900540400d408002145a608425074040070103d120007016282005520204100702080602512800c25001c07218502e40b924030546080c280c03c544189045c554a08000e81002c04580301c028866650407444524030b1070290802c01d40c101e500000e980d0419500c0c20340110a1380a446907076000c043e20443c0c011586007070401913040c1d8055507a08500320074100c041c041c002c4400fa84499110b80481800205070341c0410606209848582000c5046491850213105481d41a00b00c0c40c007039081002c00484500d0b40340034803050340e03102d101100032040c05111041d210320015041c0d290070004e0a580c000a0040b9600106207014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 398341438 1250 398340188 398340203
    0x601120c0f030e03160305071a0403080a1d0d0c150203100302030d0c080d020c01020c010c05090a0504090203060f220606050a061b1101020705061911060c031f0b16 72
    0x20404001e40d0b842c0d201c1d940c40c5c040480300083c05080400d104030f029002c0184980d4a40c0341c002c0100c0c6000b415138504440440000d60f034a0304204952804d8010112400255042c0e13640005c00c1c0e060042c1c6541c80c8581c520200548888014288081e41c80e09407160040081d04654074104a40c14624189090000380d020b4400da81144400c5489440042010780c0c01907452418a07031510100d40c080e6111285440071990203022a1005800a128003010602140c0f40d00b80d880c61000309000055246a000301d1240b843c08034040017680f40821225488100c2c21450324042d81c50f4050416401b050380810321020301c08410900c10018070382d00c4001a03441c2254a407440d103a5400048650300782c0ca159100200340301080350000604080b262210058050060301d08490b00d5202040b0365401c001686424003611212002c03410307400c004804010220070703010303207040d10b800d560380e40c1319200140c490584458012604070303100c1c0d101070480d8090282d400c0740a0fa90300c001c22441c1c049500401054400e02c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 398342688 1250 398341438 398341451
    0xc0d0305090109140a031115010e06060c011506181d0a15150201061a09010e0111010911090901050105030a1b050901031505150d060207110402030c03010305210706050601120c0f03 79
    0x114000581004800072350740340c030f50141e003400080c041d002000780185401070303002c0c0b08001c0c07900070038082c0300c0c081ca03810700e0110300c50740c40d007040200464207503002d94800303e80d441001d100d55024200c0e080c80005043c04008101d4980210b283d0081003880e8054880300c12540010400322140c1d44c3c000381150030780d802800010f4488110b00302c1403d0354002d06002d000d04000442d500d5028204000702468141840d0107046004c6201e1401e41d03200c0d010803070b44410118100310240c90411502900810810000c20056050901107942c980e007000025214031070080540003183c0742c0c0a0920040c2402404021075940e603854007040103000404038258090901000074000c0c500c00f104840040c0004060b80d0454035182c40d04002540a0380096035440c0544c8603990140e20b0745d0000314051030110861659943c51410f109040889007022070010743c004c040c82000c1c00c1c030554142c0b64801e0300f041000400d500c0300401a0740c811003c410710701c565807c2003c2c00b000c2076000404007650000c140c41c00d2040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 398343938 1250 398342688 398342717
    0x2040602030a0f0f350a0c020106090212010b0d06180f0c020604020105090103020a03021b03090109060f120b03100504050c01090519090c140c06100b0c0d0305090109140a03 76
    0xe15135400300950000d503040c0f01900c2885880d400007029a040040224884010200c4060b034482c400c450244106444100020f41141d0900c2000010465541d04608011004c00741e030b10b00741010b115003950b108000c07548052083c040d0340058000d1054441203011940210445e078043d000c5c90303540506052400034051007450001c00c406d40710350b5059442d5450010420700541c000d41004007a9030406a0074001c008100580b090300c0090350070100021916070203540c000503c19a9070350010010085040b031183d00c4d2070b0308a002040f04403003c040102e0085581004203181c080f0300b0030030300c10183c00e01040c04284440420700510006007030780c800c0002c40c0c60300180403a10710300500081840500c41c1d010018441c4591000d0ba080b8000c1c6001d21808882c1ca11403411030f08584080d102c1c0c2d4000e0000e000c0702c40d80f0380b00400010318a001e545401c0c100400a0340762904800740c004020705445000085e40c0240031750010440a07404507224440d00c3c18030020303a6640042031421404288920008041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 398345188 1250 398343938 398343947
    0xa0b040209090615040914040605090d1e050702040c0822051504061416030522060c051e09130b0310150906140f060c0307020913050102040602030a0f 66
    0x101c032501034011129078441d03505100107407880910801c0c15500a2001088400543c004d89240020702081765409040a0030898121000600341d0422a8450038107804002e03080314002c2c0900e40880d4101440025842040e2428811010000c0d400391818050403103070350300044d1507070060380c07001920301503a0800c0c03800404a03644400007402c141c0c06240d003d00842e400b26010b0340c0c89072103008007240e590150404c1c0c0b6040c4406840303141400006590b03510750282e0510440340d10012039440d00d198007800e4605c6010607080c0c104050700641d140c4ca20700400501075000c03603000c004a5000ca80340208072840c20300d503542003501c149124800705a001d0b22400d0043c01044c00e08800100a031480c880c00c01b0040000307201061030030180c40b488a40c0003034410b00e01d10480c002044d1442c10220a010031200304550350500f590f21074842c1070203018211754031000105540741180d063b19104165100c124660307403035410f501c3d4003c182e580005008510568003201910307100c02640c84004240301030407810344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 398346438 1250 398345188 398345197
    0xf1407020a0609020a0e1e070926071a09040b0906150a0e060307030605040b030a03020319030b060706060e0c030103080f03041b0602010516081005012a0501050a0b0402 74
    0x1005a12842880780411469400441d9040c8001c2c11316031a9a9250b1488202010442d68010242c1c441040510340003071f818000d591004103031421803451030402501042d02d0707441c9240c043c951b00c462072103d1b2020301e04200920140015072800e64003000082c01c096003e41c41104030714001c1e81803250b04112802c01c08490740c0242c400522504040041400e41ea411b6040b4484403010440002e0b4030f0500b07511407200840c01400282c1c0c001c91114180010b000c02d60300c0b10201d46019502a5482d080801d501109490405e104c8400000e0b04048a450440c003809602d40444d070303c00000504401000110380c09407080b0340c11810842640d54032080b8440450209200c090402e0004200c070801c1c000c0c2682c02140d01c10b1241e590100d0b160041d01548426000ca0b40010025039522010700c44004039100c00d20f031070b089240c83c140d5154034140804901001c0144520744c10300c02c0500340703124030300a600c03030b100c18a14040c5000321b011034542c00c0c142d019120030355440111074944403501009003410700896 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 398347688 1250 398346438 398346451
    0x3021201060c050709091505071d06090301090b010e040308010611121c0203100f1e0909050c06031501090b07050c090c0c070e01140306090a110d0b0a0f14 68
    0x811a03292080684071400480011140e9005290340070079643c49900c940c10440c1c0c00f44241840004000029000701c820141c086c40c18040118180d96000c0401c80c003096079400141d414945034142600880e01404400d40d004040c481440004903404c2c0710706000901c114026500c6031034030303641c412007621301c0200305103c440070380c005040c20f010b08600d02c801802c0183c40030401e1440b6280b00148002240c0054581e8030407101030316400c0084410304011803002d041110321030500000228100da441001da48100f240958850341d085c010300106006028440502404c0320b03542e0300e0036400802640b0461000e89022407111071001c203072244020140c03100d13203a114004220f110103610401c05000c00040c524007a0030010050407400d50300c1841074100600b1881c10f480c46550400042e458030400c5544124000ea004000304034844400065000c11542c202d6480f03d001d9003004c000c60b03d040035580c00a000b0709201014060301c0d4415070f1000d8001d0705480001c102500f010050b402206806541c034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 398348938 1250 398347688 398347717
    0x6060405071b0807081e0a0e09060d060f020d0207030f14030f01030311070f0f08100203090307080d14040c031e0b0a1805070603060e0a0608120a0512100f060302 71
    0x40100181c540030040c0036650068001714200b40c102400e07a143d05400300300000000001081c09543c540d003044040076014411103180c82c45282c4403010440f900d00c401c0000c1d1100351181045003c00010368100c0d010325007014819581c45c4d00d981809030491b40d001312a48005010f0b88400704860041d801540d000d0156020200d03c16480c2da102121706002c6060b108006018a900c005821440700010f14024101e25110202e03141ca4024010708081804800650a034010810800ca825010040b2054a80c2c440b480d03d40324004d90340a2401014808403420b9080501c2c810721007030280c041000802c481c40748606030310642c003a41f0090000f400800c40200791546090101e00c2a104a40180d100c2c2040546182001c0b111910b8161511324140d00440109550300410711808091011090b4400945201800352519029249555546485402400c440e02060103c1060312410481e4034030030740d843d4134134602e0812460045a0421920440a01b04000200011098000d00a841007000020703074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 398350188 1250 398348938 398348987
    0x130e100308161b061d030703020a210b1005091815070e040203190c0512010e0c04150801050333061807080403020706080c0702150c0703050606040507 66
    0x1800348031410b82240031203c0e400710031850801d8000b006481c200905803640c0711142c0400701c18a45a0f42c03040310103128000e0300301c40410710141c2c4602031030720200c83c5170300d10040690042191528043c80d150760014410007102c0305100b02d0a100005803002c1e2041150398070400e44078900d805585080010b1001015049005484520350b840380140c8c0e40984a8101450148a0a0001801c907403040352483c100d10040980d100400d00280302e505c01011081c20440e24040350400d40000d1410b05214003c8000107440008820014250503a4018a08510040d144078408071018114031424040d8902030b00c41c400b031074100040090003019940300041c03c541c00300c2c481d002003c401418000c0045030000f0015216183d103140c0c0d410410700c200d0326545c65484a04207441c00074100300b103503402081001410301c2404190354002d0122455154100c0e1001a031030b0304500c00340120301030300c02c51012130300448200105001c2c000c0351152103500100e03000c01081e0f0f00e540094800d48007044609110721070031607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 398351438 1250 398350188 398350207
    0x60507122c0307120b16080705070611040f03050c01120b0d020111280b0609150616080d0c030b0301020c07051302070209100302030f0c060a03020a030b0402130e100308 74
    0x281d16807010001d03003520646600c488598101c0e15002c001115480001c5e400c00640281c40c4801620201c0c95180c41a0142841c0d00d0040050185400c00f60006139a101c0903d00c006c032100807180285004400f40380080e40d82e088c80e0740c5902010f040207012546100321103088030083d20800c5980100201410401c0b4165001103590300c0400411012500c140c0c002050b401020f01c0c100d40c00c213440100c04070354000341c030701e41005101c3c000381c0028003c0c0c01403418414044141084d035861403100ba106181c03139032410344c5004085081c0c2d07103010f4248800001d411000c01c0d400d402521070440d036030b01d0038088070810038141030803442403545001c0c0940000c582846180790030080c410803103e1082d805402d0504540025090751403e0b602c80c91b481c800c0100400c110f04051040310b08a1501001070212011342c1e00c08a11144940c5a0f65000c1540c001407500980d80642c1c41441c3c1c008000d8011505d8080e10000c4280c1c03451079026044101c9400f0b000204d100300395589144c203483d8400b08150030b00d0000c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 398352688 1250 398351438 398351507
    0xd030f030c02030d06031b060206071d030319090501020c0a35030412020909030a090b030705040e010801020301032d0b0a11190f02010902010917031306050712 70
    0x128040c0c001c500003042400404101170003008095805151080049090039910080000c403d0381b00200b9500328400b0002c0c92908060840701c1814140b00ca035031b481c080840068110b10454250402c074141c06402c641c00558081c0954064a070700b82c080b00c04034003c01341041140c00080c81802c0c003800c0615804005119003150129001440b06040d1461440e032000241c1035130001d130880301c0715a804a00080551803c5c0c4241504140250091458129100300c0200000070301c2c02400902400080490021032290702241c0040c0011029400156158683d40d4040d600030b1000751844e1050171000c6c4481403103d5915515070b00101140880c03c0705564440c424560020481045113079110f0f461080c500301c0c000142035030580300018040074a00480301800f0b11880d01599421a8501040900181d82104103202590003c4000c134a0210b04002e1b0240707148192190b1a00220a0040011710aa0040042c03e44680b03d04003004041010800444040d02e01d00c02c074800c5d40038145070014803010070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 398353938 1250 398352688 398352701
    0x5041e06050307270e100504030e0a050306180f01060e01030b010512150702120705010f1119110f0f031201150f0309020415060c02090a020a0804021c020d0b07020c0d030f03 76
    0x80e00c101040317281d00d00e2201401d01a200741408070710754842080008040d44004011001081290f240e8600303414000400d607900d800902201400e2001c00a242c8040c904200c0020310106180c002e00c10b56842d0804100134113003c0c8012980044190004603480c6024601c0132111f90110000707120b4240c400005082689001e00b11505500501d0640e280380001e183c000c12100e070090002141c21114000d15008880104450000c040800d00c0505400003c0c4195406c3c1d1045510300304c0000d0061094007400c0c070080d02601141d502c03514406500e8040040301400c40c2001c030542060880c0c1c0d8600e000fa103080e030400054400114081000440c443c001d030b1102d8007250014200080b00411881404290b0b000c540003003001c20544000b803030861600a603202c0e4070140504081d030500d001d00d42c01802d140e074003500081c842c000a9541c003010202a58055405580042040500322840c3c2480308000301c0a403821401805a040240f446052040c000007030a0342c03641d582d04040707007051400c40c0280030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 398355188 1250 398353938 398354009
    0x5060a020606150f07060605031e0606010c080d0f061d0112080c1e0106050a0f031a061807030218011d330c1c0918020405041e06050307 60
    0x101440240a00c4071440050a05e5610a040004c0c1c140c2c1442c0c01c05140c5655000c00d003980040d20078911008050120710160408001e0030211428002c51504030034600806240c030412614041409003104440c1c3c0100d03046564600d200f1180e0101c001009900c00000d00844161704003801080700069a2b02c8010050b55070b1000c151126910001000701c0178200c040f01440840e034550707034244480e29025080b00010000d000400b0400c0c2c1c5560780360300d24401c0340b018038040d1010a1001070506c0d12110421290080708145a402a113840c560180094101e50300700e09450382420070b51241940030701240c0080c000000340c1c0700303400020281042604412201032850320980a8800211158504000c04603888100d11107030b00c0b2032640d81d00340d00e8416015411001c001d070500b2444807481c0c10208180c240d07004d59401010394000070b8209001782c41640e0141360020318021403411501d04105402c8050b00b000d44081c011280c4d81c0b8101540c40005004452a00d040ca265640e08009040c0e100e140610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 398356438 1250 398355188 398355229
    0x30503040305070b0a050f090f0c0f0102010204050307062309090412050d060b030406050c270a05180a050c041401031a030d02030a0e010216031b030b010902090a05060a020606 77
    0x2da6543d4407102e144e001da440311420f41e161814410010031341032141d68400b4000300100391140e1100c2c00030b955020701740c0c4694020221196408590391003034044074058100030702200d02840e500d840061202c0848020550b0b04200c031246001074412150441e07d109000811145058481e03071078281c10701c580f499003507007070010411610109140318041c100081020300041c5031039180c0707801d011054030002003007403000c4032082224810f24500030300c03000c00c41c84281c0d041d261400c000c5400b1488070181c0b42c00065000c883d20038001049800600b00ca88554070300c400502483e00e9a0071014100e0255000d0b400240e000351070710b4041035129501c001030941305114000e40540c0140c02080c03c2c030090581d180016000001d851405c81e0b0407144000031000284010001003460210149001c40710f400000c01e4070805180f101007a026150003400915001040000c0d15655181c8101c02940030301c83d030a02031006000005124a848401c1e103644c00001e40141c0102d5a40341e040183e010116444020500c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 398357688 1250 398356438 398356447
    0x30513020901151e170c0c100b1806100509030c040c05121003020a051002010e0d050c010f060f05060a0233060f0d060b0a0305190b0f13030503040305 66
    0x40e80c403800d01030700030244410180c04050040c00c0041840103900e42c02c0a00114101d04c440c101c03644101c1d1540102c180192032105501d070302102000300e1090015042c201d11030411040b441c03c41d0381c1c0c001c41d62004100e4600c40500400a14002c0004084542591000240b071843d24100d004200410313544400409941810051032300040c211a0304440c980c000807408640c0200d084555080950000204541464207514642c0003501c05503850007881d019107841c00720039899034000d400551191604d02c05540075649028402055500405d0300b0031480d40c20801c1c0c1c045a1182c501c1014140c0e5201724003180650304010600255510240b248021071080d00b054040340e144071465455104420740400302d220780401650000d8040140220f842030b03160040c10708039566100c02450155501083c08179503200b1100000310b07552400c1e0710241041c0110038690301d442c0561681300e20207520a18510b40c03e61034044503443c1a04044403814450040340004c040030901410203103500510034500780b803a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 398358938 1250 398357688 398357693
    0x21b0d0c0b04032a0911070f0b0609010621090212030409060e010603111605010b060a020f0d02010c020d0509030106170105153a0803090601140105120601030513 71
    0x680d84990300884000401041c207108202000410f184038000b010208680020a11800c52070301c031043c8503402c029030350b48000409240000042e9642e40743c002ca180a8055140d05000b01004022244103204541c50b0001181c8240168070f00c2a03010314480756280e141c40d0381c0c0240c40c01842003600580c0c0c840070542d2181c2d0414020802003010300038039000803030441d00e084140350040344c060300a80180740c1845021001c22524206403686100e00101741c801091981c01e100e801041c050303d200c0c1d040a00000c1c40c2030707030176000110359003002044c004403900d185801034100d00301d82815140c0d4005070071a910144045220340301402c12803600500020302c80e55038800c070b000207109009090301d459440300c00300600000146c55401100000765200750050750b440090520fa80d00c0240d24511103840d100032408034036116001040c000d0390100d81d541d501c0c1403540220f59030352002d02c10f080c140c0c1c03229141e1803a00c1d4422020f0703840344443c00e0000501c2d610750344010360160400500380c0400c0d42400c0c101c40003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398360188 1250 398358938 398358953
    0x50115111606090f05030c010f0509040b060313050f0c0d0803150607060606110a1716060e0303060307080309060f0f0c0109140d030905030a0c0816061d0d021b0d 71
    0x420143d1109181c103460400f10042c2d8041c00c2c0c0c41030f80b0940000c480d01910340d81103100600c03040c007140340c425910000c40001400400711345080c01d400490200400109064520011102034007500c21291002801c40f1040d41c0c5070400d102c40e0707800c00712500c80704000070010000f0307503080a00310035503e600a000f20081804d94105120039103800c3d440d454204075945d080103070140e0f007403011809030040301c070140c81c1c24800c540e80411b080b040e141c0008041c1d03441d03071041c40e042c450a41d000030f041c82010050101180d40b07800c20b44280d846400303200310002d1900000000c86817081c00c081d00d240d041c08051400c842c581e40000311280c05a00d020010340c060040c0078801d14020b648100f0000c0c00034041030345024500007058080c2c41c107052a0804c81c0012617000410b0320001c41c2c142c60300c9950072400d403074a841a80115038413198200c200d4442c2c141001060380240c1e0160a00d110220403606011b045107982d41c1c0c0c1c0b40d20a40c0581c029400084e410b110101c3c400e84400000303000900007a40e280e40d60076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398361438 1250 398360188 398360233
    0x306021b0f0607030e0303060a0b0a0c02060f0301080d0503010806040210090e0907030b01090902030309120c0613060f0503060108040204090c180b1201020c060c03150406120b060405011511 83
    0x889542041040050783e94041c414001d28000300c50040d42145422000b140d2000c140780552250f0030b0740030411603d1030348641418110b55502401013516003031801003d020035082805016102d0003a14200590180300300180d0b4101e5140500520054503160240a050814443c80d14100440f2031000304101110034003035400355000720000c00d00c0303d19504181444440c1a080446800c2c2810385a20240e9000402d45884001c200c2d000310610342015056440d0495035400a50407440202c1c040404500c0d40321010200e5107180c030381d0094403902002c201c540c0d10041b5840c5000c6002a1301260150919601c450903440c89050500042c039150b88080440690f4070310f4404d1055240c2408815070704051050200c0f4881e000002d40c1840f200041860b201e0f28001c0c0081c40001c408000a190180341e020020400c0b04060710800941d80c55040c44198140380c003a088d203624807100040f61180c1000c2c0b0401d8100c0f031310b003045211280000b070340484000c0c2851006460911442c1074012083c860112010f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398362688 1250 398361438 398361463
    0x70c2c0412030b0a0b072a1d090c0d060b032503140604030903030f020a080d0b030d0c150b01020c03100501051011031602040f0f050a1d03040306021b 66
    0x80201c0040c840e004058810b890707032160207550500d404204684802e002c0d40c1c41b140c1d2013241e0f007030380c40c0300401041705403204800c400d4500a88800001100c3d8282d4600d41c030317041d0321101207400c1659092081660b0711203c110540e0400041c42200c008540a5444003404400040a80d028001c0481020741c024540780258001003c49000800812681049040e0b04010020180a6034070705910003404040e0305100140034850300d080f09031603a0b0320901000c541c00c0e41c05803142c1c2d2915480980070001b4030007007986502038411a819019014001e98510b50350550100390f0b02c1003a0015103220020700b0741039064906501c50100d4080380d40e40c0610082a181a074480c0000780c5600d07103010010054404280101400343e12503030844c8255000c001c4800401185514411410407480414020100304054800c058540b04050344c0f4407220b6001075000381241242031004902d0f950015018614490845220340c2c410081040000c5250b00685002d840041e0003600760140300c081682489224900e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398363938 1250 398362688 398362703
    0x910030609060807150e0a17060a0b0d0c051018120209070f050a030911090403081512070317091908060f070c150e01060b03040611070c2c04 62
    0xc0c4400752040c401c00e07000741070b14002480d0462400c0c002000f20074102d9580c008101d0f40200580485e00c0311901c0d40000c0c02c10a070440c003c0e03024100726948802043d1100c0d80407508142c0704210620308060407180b030700d03004101491700341c1ca40020030851110245040f8140185941789154200c03100071013200400c0201c44020b1401b5280c41003000e240c070700802c0b01040c4400c0445002e812584003040c0c9011051500300003034401c0350ba0400a601031310400655510031125030410040640c00a0454001c8241c294500d000c021386104100c0c420100600c00280d5a100d134004201155010b8500d50460a00701c00182ca4604000c000ca1181003484078440c00805010303a042041200401202d5444001c050240d851403d155170010100d00f021000540fa0548004840004040769400007007003103480340c000c1041c0d980d120099003980c0c100b1103003039519620b82510580446040c1048410086e070081c5000070560800d40d040303042212004501e07100d01c0d140729031412900c0781c601c0c0b40e40c0201e004202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398365188 1250 398363938 398363951
    0x20a02010209090c0403030512070c060203070c060b060a02151308130f0e040b0a0e101b1103040608011214070b03180a02011b080d05130302071a0708070206091003 72
    0x52090f00b120140c600000310604100402c0869030050a40d400c16486100c0300040340c4903400c04950000a0302009480c51340b00000713100c0765a030414100c640c3c05104080a012101d01c10302001564010f544016025070003410700400c9203000310300242e80c004503000b2001c034814402d1304c0302c40898124a110b01c420000e12241400b41035030031026007006100f9400c6c0e01a2900e0555a06803080350040c1c15001c1140d19800c28540b01b6105000100a0802060007000710291340ea004500c035030000c084810109885080c05c1142d460048101c1c1c0c00c0e00c5994485200740c0e483c086804a4a100000003a40c400a02020760000d400062140d00001c0800401da107440e0704201114510050b1180f01440544d800485c0d4800142d030400102000704506c43d2440400c04050300302034145114001021031010303c0c0000304041d5100c8000702c0700c48540071741e00b203c50035038440050741022030035441113600000c01400b8030000509010010708a442c409000641000384020105805660042d0300c0d0002c1794a604 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398366438 1250 398365188 398365207
    0x3050708070303170403120221090102190201022104151514190306050a090c0f031406070801030215070803180c150d090611120601030614010512100504020a020102 72
    0x5070500e1a813407043c02c9281c11130a00d5039010300110003050091464603004a0b135019620511030341440101c4034803404a9451400707644560003540302800388440f0384682c04444400502c144251150550303888a5218000c003600c0d4091007258000f0030465000c4007403904c0340710b4040a4001c00c0c03c0d69014110307425031a0b00b0b1820784161060303104e0605000701c600881c1c4050301c082602a90088036000300c0009200c2c0c40340c03004440500003483c80076180c0c0340d0800002441715000344032042124000d200380d40c0d0b501c20fa0b40c4030701e4488a040e02c02c0c00018803040300600c0585048001080c128039002e00311450941d85903104801d5400448d04810020001c41c7c0c4c04120301801e200c2a00ca0302c3d4100e40030264166800d81015250150032003c100560b40c81141d0002c102d81d13039009001b84242034100302d0300c03802501d17840d0000c00710480701140007034102a400903482c07041000c000d01e1154140c40d15414941c15980d00000140000c110040003c440d90300000c103502c0358801049185801e600240c0d0311103122 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398367688 1250 398366438 398366447
    0x61d0907050607150b030c0a12020a1d0406020c0a120e0a050405090717010b0402031006030f020a0c0212011b02030a090e0601091802071209050405240d0c03050708070303 75
    0x154041d80c014401004250300213081054a0040c1070441000044c1450007580030904d4009406010782c0c000e0900314000c0b450024241144680034401c45d503200c592900c0b00107029081d140901c0f0a0005104040802c2c0003840c560040c2c11000018000c894501c007040c4c46a80c1c4400410181201094039810510303a80c0c200811400c028150a66091050342003000c116642c0c0c14540c460003144190700f82d4110070850085d00400c44c0d100004005549a0801c0d814620140c440b0b40308010201e40390140825001d12903000703490410306a615103013051001e9809101d80260754005800d00d0303540e61301c494648070800030583d0b140d04009900a54880790310803000b40485010760804515a00020100a82c9030791028824081c2e40c00105c8061b800c4208807500c0002c1d00540400400901c56000542d0219601810007030031500125014401a15005807040340b160350403140b14a02c6c0e0140b1094822070620b461140982403144e000b181425550346c46980c00c100903134120542a4000c02003c0080c103511 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398368938 1250 398367688 398367703
    0x110d0f0b010504210c030b0f01150c06050c09040f0f0c0929040308040b07020f0d03080a0e03041208030402040e0d0804060f0f020a020a0c1d040b0a061d09 68
    0x50412105021030300203840380c06076224101c285075014101010b07144030b900403071521a5010b214010303030544918103a06091003c403209a240c2840000025559021340880c010019094641c01e00b0b020389a100e880180c00002e04442c0d52200802c11016241c80358440d01501c9600d200000416401c00c10003141640c890f480c0d07440801507048403d01503046d90300040e141241500310381420100c2e180500314500c0c080c560014103244004030b000a01740030070341c0c01403036054800c40301c100075444030004006503a0404003019001911910000b050032101c1d5005802a580150450b41041da9402852000b000544022079454002005000441c10300b070084803403171110701c0f0280481400107140201221130081c00500400e0710764102c1500c03000c10703500100b121403241105642d10350622101a5969135a40c40444101300010000a44104aa04d00f020a0b120b652103410998440d07480d084405103001d0301440c0b540780d23640d9001460034400d403c1c0d200c8008910440440c00d1815a0342c04d4240000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398370188 1250 398368938 398368961
    0x5010609060e010b180613030209010b0c0c0103050c04080d0c060f0b09131a0408030f07050a0f0e0307080610030516060c0204020a170c0c010612020a0b07060f110d 72
    0x202a82401142510280c19044d9665281041c0d01c55030100f18800c141e02c1c003c10b940d03401c400c0000d140c819001010075450285c074000e07104c3d082c0710703640c40803d4921881a25058103031a041540495940d40c801d410103500080038085250504d9100d107025070a21858100860208000000c3c0c04200261801840803803c0803210800006080202180c150000103004074012941c80c1c0385042007041240070b09080402d24503031070109240c50b141c11070040e44140c0d0800c011942d04400a404140320303000f02c1e0f0362040309545010b11003404180a0355032133186410a50305000342d2401195445040001c58443c0c0c0044440e004441d14504245040c07900346500d030036890f80454070503c60307a0307003024030354034003039030540d0016503038481320404840040990900c020b0300750104080c4100e000610b0044d0401c003803800300800031590369580c0c03c0300d10410450000c3d048914090100002300e0305101508500f4080c280c04103a50400d400d2240441d00406595800b05001141c000f054169611417100240e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398371438 1250 398370188 398370191
    0x20a0b13080c181803120f06040603110f0d060f0903170c1614070608070f0320031e01090914160902030604021e0d151d0c0f0c010905010609 62
    0x80114081800e00c0940c0070700e00c40400e030f014080f8019034103e18a00d82c0c40581141034075103a000d20105e0404c40601550165108800840400c0040c5014420340c800c5941c0035040340c6880100109002ca84600c0851441d80092003482d81c0000c1019400703202c1010a05060014138200b03246030160411700303134008212a007000a0100b1415078002ea00b150400b0340e401030042c0c03030800300d0321305010010031000c1180b085000c0c0e41d0000900703075040b0401c0740c003d8225840b90041000381c1001181281d51502d031b103021101c500f0003907943d120240c80c0250b8112120206039400307004018a03404c00c800081e4800750529940345040f5050050700c41c44040d01119500c0a0004070303405001001d41e8910b1802402d416540c00008210203035201d0781150400c05460400c04090308564407680780e6030b0440309001049072f05004c60040c40d40003680881040c0c41c03400c1610300d0017211440c044a80b95100800c1801444400c104010311404007102030002d10081a0020034a003a0f40c0ca040c5080d540385910012140c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398372688 1250 398371438 398371453
    0x8160b030f0105010806040e030d0609050108030705030403200a0314060a0506060306040b01030f0903050405100203090117070c020d150e0105070f080a0b090108160b1c090c03020a0b1308 82
    0x408440001c107046a600746486002510707142c0015009112007a1811202c2c400001d14170700308441600004211040744d07108025503a45d802e22691240f06013407000300b551300104001d00009800f0440345603180d009681441d0004014000710b150b108003034006031000c00703c42c03021083c2010200400b9501000804080c03045003048000f184d0740d40005400d8a12887d25440ca0a44a9100c3e511461800705503a0041c0068145030401030401ea0142c0940e41c011487c5601a2507514000001c80708008810382d81e83e4650000d10710042000b12000e401181000702c80c6109102503543d09520070311103400741d0301d406440f0131140e0782c4504503207085c0f00c0e095099052200300000207402a00c43c0440f409030b802c2440304c039907441c5d0030080189450040e407a80706140900210300d0b580300084011454489648803200d075500c81104c00842d00443c40005a801842c0d000079402d50515000601164130070015a800c640d2690b0024002d04c0051b044420501c0000c40c0c1d8071031041482010300001c2a8031006003c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398373938 1250 398372688 398372701
    0x50907090b0f2b120e01030b06040e01030f1103030a0f0806010206010e0601180509070903050d1403010302270c0903010b011e0f0c050106080c01271404020c010608160b03 75
    0x10f04200041c0000c91200101400b4410000202512880b940000d10130700c10403164102610802e000c5c19070311300003480e0031840c400f42d00303100d421a016550b1b61050481140c0c65503481414016003c0003c44000e220361a49010030b4034100b0103016402900e440f0031600c80024000100320250040000381150301c00f1b0010440c90b4604c0341002e410410a1038010302040642c00001e840307400642c00103800c0345250041124050344140f868003a00d202c2c0c025035128007201c15080714001e8001070300e842010b204000410052911220041f800d80c004911282410b8601c0921b003d039035801c5803010078800c40085d41c07107110301c0c0c01c0c03050f40b104840909103001038045d07210b002d09c1d90320112580101480344540c0c40301496406a66450604e0794440000c0c403015440e000320546403031440005034041401d800e2100e021040c0205212010f40318a907102c00d400c1d207010008410415041c1b11260002d500b002001483c000078021080540b100c04000d01d030007040700c1600e054450096000e4022000c050091200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398375188 1250 398373938 398373949
    0xf070317070e120a0203060c0409150e060f0103090803040308060411210403021e0d02011a06120c040b0d09051903050307081905150916050703050d0b0301050907090b0f 74
    0x1c0b455000d60701020485440740c0e90910b043c0200001940c140b03e054108000ea020502c003c106544004100f0301c542c4050000d411084a0741c4d02400149900d010300094140c1045c1c840040742d00c0c0140b40106900580e922862050760040c3d0301a000074018070100845402e06001d440c0094410b29041031511454a801c01a80c3c100d510b007000000c138041c404241414801c000b14003186442c5103100c2a10340440c8600c541ea40c100c01c800e04c000d5420b04c000800202d565043e68009854003401c414a041c5200c04010364292000740a403015503c21712000c21082401c0c0c01501b0b00c01828107001803e446d40d402c065180c00e48811210a21500b00074030200000e50060542c0c0d04801e05042c80900390b01d4001488542000c110b80541c02c03140341004000f020242030f13a41c4078000c1c0c000e035841c081c2602d0380440c3c40444c6e41c05242d03440c0450030802104001a11620080c40d17202d086990008006111000083c20f4520690380803096902c9070805000e50b001e24484d240210b0300884031250083d00344004280d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398376438 1250 398375188 398375207
    0x15010503030f07080f0a05070510090206030a020d20120f04030e06030a0e060c0d0e0a020919090501090b07020d050c07062106081c03062103050706020f07031707 71
    0x4a1050205803d8200911502650a1041d14907802900d681201c400100981c010410503203091050444005681d080e40c422403c1c00c5030003400e00c1c1d1459a443d1000e402a6101e04541c01802c0d5892180c5850594581807140700c0000002d0342d0740d40c070303400c0c5000841800c802410041e0321942c46004e22002a0300641200101141941c0711922650b6a0035103200500e80001404070a028110402000c02d40c0321009180c00030310f0700030070019500c2d440030342070703541d01166802074201000e2401320b0303641d02d250103820103404442c010205a50406540d481e0956a40c00400c50f04882d81100744203189405120f0030310601c00c0d45c5401400d1010000c40195600d610740b00704018440b0190070148056146c1d034000e02001150324045c41703420f5407082d41540e181d0004000f40315400d40d000d5841803051182c040c0008403415010f90700c02c001e000c1801503500924802c411001d001c8104440c900060950019007542000518210344452403402d001d445d400c0b112101001c0001c4a03010001213541014444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398377688 1250 398376438 398376457
    0x1403060d021504120605011706040302060a02031b0d0e07050316150e060c0703020405010504141f080706050a030510030209041104061a090f0a0f0b03060102010f020d09051501050303 80
    0x1d1a9403010b106a01400d8480c1c0c1c1c2082c01615072000c105018800c3c42c2d00030034100c0d910380f510445190340d10b1401c261101401d4800030016000000803600ca41c80d5a00919001065a07110b103440d000f11042e414019440040740498040c1c03641c08001603e2810300960006202c140c010f0310f0200402417507007500041e5400f0390749034840010240703a403151007a00203201c07280300a485140d803101c00010441d524072061104911490510380041990306250141c025500100705245446481d140b140d0340000c0700201000501078080240082c0341c040030494040101601d071079160b50740c44140300c01400e44400900c0d4041c01c4034464410401a101c441a8682c0240c0114141c2e048041d440000340c080c0c6001c2d0300259400510080040080024400405440b103040b940c440040c80d03500284064151039205031307803019651030820410b08818400650f817100d414400000d046c45000003201c03c907007222102c0007103580c1d940f08050402000f00105200c210078500e44012540c9001c1c0020343d28071902050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398378938 1250 398377688 398377699
    0x20a02030d020a02132301030f02040605030c0f0d0807022101051005060a120b030115080106050d0b180102220302180f1602011803020a0b010e070f05090f090103121403060d02 77
    0x1041b03551200d4045a110070580c6051341001c550752030603c200c425401c01c1041c0d11403031030f000000500f450002201540c1120251468088140d104100142c18081310000e545290342000113000594800030040200782010340c9490540c40c4080d00301c3e08441c0000c010022143c40800244069610b9000351021201c80b4506010301003140700a084c084d01c0d608034002e800d5800d2400b0f1200141c0c2d08401c5400f07490104008003d40755807802008403241160402409076142c03c0d01245681e000c02d1507429400a00c980050314140003c0301d80d08082031115a91900c41d0382c8881c082c001c61912401c020307500001c0c003c3e030a0180c20a215980c02c1040c001d0034040546400000400c0014000e40080c846440c4036007401c0007030660b80c1406901c641c2c1c01c0c0c2084808081860010030340050201d20503000f0341c8a90345050a02051041c00e445c1d81d4852044190301415004003403440e40e964000d0140694410b80042c103858841b800c01800580d0090a61071100009004020194842d40040d14070990101c45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398380188 1250 398378938 398378951
    0xc01020a060e150403050c0f01090c03031b08040f030c0b070c051002120706050106020706020d021b040b030a060e0f2407050f0a020105070e0d050309130e010606020a02030d020a0213 80
    0x8a0b0751400250054507481008103070108418150080d001d0642c03998020192094400c0400d00e0030308803000c0040045c401e40c0c01560610200e0b1040c1d54040e0b10b0381c0c403100110030240c80351712403084a8000d41d1150b400e8200d9804144204900e10509100804125000908240d4a030b07840281c3d820b100e00a0b680501e180382c007001e005c3c0e4802c010400140104014250340d80300582045006018240100000f61245250000b2054400a0005024403081c1d0250070b00c01c0f54038000113040319200c400d40d54480c1d2502d580074265581071002d0204140304500c006118210b0480c0b040c140f02c075151a450b141d8015041100c0d0a070300c821a0a8001c000d40c0382c1819482e662880151001d01881c41c0183c0c00c0c1c2c101003000c422060f015403200307004003660f03140c2000401818080281d400d09074800100302c0c2d0824400a0600d081240c4001a0014103141c0451002c0c203800d02070742112001c2e400703540141d0050807410300f941400e002c810310308402c9101800f840742d202e401091409040811044141d40e4492 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398381294 1106 398380188 398380211
    0x2120a0b090112060e0c040e0a0b07091406030604020d0501030c060908010501140409150e010b12070e1303020f01090b010e07090e010b090303041d0906090c01020a06 73
    0x4a420340d20440560344e5201038070201281804511681ca51558030740c0e038a00401e005052040300410142e80d00742450588807070054510001e024070800140003a030070f902c116402080c02910740c81e65a072540c0c80418000c1c030880d8943c40d44949450004820400c070903000408a40b01c40e512940d1103903c0e110424200c2c1d400b8850305481003840005d000700341c20140c011f60302c0c4034000e0782000da91448010411050b0303000b208400c94581d6451105241c50300c0c05050201b1075684240017001b81310b0400380500c07140803020b010503a2a02086c98018100b40c0300304006074541c10340348003d0080c2d09a6103403081102d80280034417031050802000165006110350342d80b804031082d006998406910b00078101c2c00c280e1155000300e130540010040400c1140e040c401c1801c1011001034062140d01d000f150365403d142c0302400340e02e0541c000342c0010445aa000924824840e0810000503c134803014 = true := by decide +kernel

theorem cover : BRFrame.Cov 398201438 398381294 := by
  have h0 := BRFrame.cov_init 398201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398201438 ≤ n) (h2 : n < 398381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
