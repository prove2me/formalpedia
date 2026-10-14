-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:05:57.780832+00:00
-- url     : https://prove2.me/submissions/fdf95843-933c-45f0-811d-b190072fa6fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191906474 ≤ n < 192086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191907724 1250 191906474 191906497
    0x10f0c061409010b06042103110a0c03060501081b130209040504050706140f0406030c09080303070305070f140d020706091703040204140114210f0a1a0601080f0a02 72
    0xe20305685044185025280b0950720f50800303111040b941855030540e01103403458216031102260084502c0041e601c1010140c0400c81d000707100c0000881c0c04c001e06031403207128010100520f4514140702045540c1a0060151a002000031500e0491140d40b40341c0104004c944a0012550b01d07142c1030000e22a60700078503040340c24042000180200400c0071400c4900035201d807080c03e02501d11030f5100340300c5c100c14141c45071014001071202030300c030b0352045580c2400350900088003a19108000c0c910740007180da0b080003d0301c0c0c0082052807984018424043e2605080c03c8114216100e0541d0150041741c0d405003910354041982820b02800c3d40001720f0468000a150040990161141c1550381c02103400703902960508201e81c03590302000011078100c52003013000750729480b0301c001002615036404080300311300300314440d00401d405018080c001e080d00301c0000412001109103042068401d1400151002c2d21903201045100d903048620654081200014108a981c40c21610302c000d000304100e544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191908974 1250 191907724 191907731
    0xc01140c0f0c0f0406030b041b050909211303030513051c060c050313020409030e030124050303070308011509030503041202040b030c06090d05010212130210020c0d02010f0c06 77
    0x452040c00864021804641903030b8100d60f44060781d090200340c036082e2000810452501000902140000b10011107099040c1d060002c0c1030350fa50700141070301c035090300d004c03100b600311074000d0002c411030700c0340100d217401050700b030a05220090190703003019081807001405218000880169039145401c0000c040c050003001c40c0c1500e8442d1171646031306010741900300c400a00e4641290720740d41c02101501e1085200243d84404041e00780c0c2800050a00c8000c00c80c18082d1007801031185a4003030082c2509407150019614a04078410403200c01110300c0d031700050094000304012030120f84d110238514191490007100c8020001c0c1d516044903420010760000e4034501011802160f40322800c00d0148807103008a4050021034040c004140d00c038440124080e500600400101c1400e00b04007510700b00d1540510f000508103000c18060415540d021103034005444116101c1c0000c41c5000319030b0400d003181e0340c401401e40010042c08201802d12044e0007a0600525100d4500c50340d00c540c50911000358029403d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191910224 1250 191908974 191908993
    0x100f0e060702010315350c06090315010b030901060504110a110f070305010c03051e01050103110d050405030909070203070507180603141609020903030301030816050a0b061c02030c01140c 82
    0x1368519003038403001d07090300445074508a0800400c05038441d0001b403100c007414041c01120200401da620035201300d9014040c4607083c200305100032401600030030200c110181d40c2d20384a0603032421035031180c10140c881c502e4420090044038022082d20b65040785400c1080d001d221020080385072600c55062800e2601c2005000700030440190003014000e0721a8400740300a031140c0043c0444240e101407800310400796540100322075840307a0800c04182000710359592400403142e208100b41c80301160305807500e5100140c8038119007442c000c0241e201140784055400d1041c1d075a101a00c44040f48907400301d01c0081d03411091601c515070300c200c0007560302500026403840500440c54543c4042c280a440d00108150006420180e034000c680200a004002d035145a013103682e03484543e00170102d035401040c400e0168100203082000b44070b00083c01340791818510302e021000c1028810410b200c8a008840070160140140c900240668243d8800d003025920000c41030b0032403481e801402508455031248003900d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191911474 1250 191910224 191910239
    0x23030408030702010905030f040509070e0d060b040b0406090905060601051201030303050c1c05090706020f19080d020c070f080c06030c0a020c030d0f1e140c070906060e100f0e060702010315 83
    0x10410ac80c400d0301e89406543d11840181d6041001c8020b090b08000c101c1c4c0c100002840070362001c90f41d204024800544c0001141c0400c08a48207030300555156a9102548001d0060800601d0750000e800d00c0e01c07924040c0e000074000e1842006104c020285520780300400c800c2d021403005e0790040b00c80c40019000c040300c5980f80a010b0001a24032303982900442001240080c0701003010411a11104002c0540d40c21280300c50207001c05070082903c42d501c042c000d10795103e40c58001480c00e000c2e850000c051135030400000c8007036200151702c2000389901c107100d11013860f01c500d000d40303a204641d6220b25440c2c0307050a00903030a0411203a03169505004400b0f504006a4111102c00c04004640c0d950380350603120303c1180e125684240455034049211000318048504070f0000030054405070405940810340e40b012030070180ea90681114000c50b02108448126080c10342c030071740280500340760040380c100810001403c1036083d4010b85025a000081000c01d59000340c0001d1280c070012807100500076560310701d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191912724 1250 191911474 191911477
    0x7c080708030f0601030b03030301170f060a0b0a0b090f040b0f030708031b01091106160503030f061302120105042f0a02011821090b07030f23030408030702010905030f 73
    0x2e000d054010032001081465129105000c160b040103030003103245034200003c03030751011001c44003d4114030603130300c03403448504052101034004d400c40000030888001c4030b0204001a0280d81040081c03130028002c2403100c1c2c6e107440c550701c01514260381c001201c40483d0045484030005614050b0548104540000e403240000020501407925207441050200311120301402c3c1c80401d0800f40026080d05408000307880e0250081000b06490b590310080c1c81b260b980d070241150001c81d04181018500010806030b41081404100c507616030040452900003491022101403806004d09400f4617a41d0100c1840b04085054400380210107003959110800b8a0529003510b0340008003100040d401d19121080303080c1444204080c00341c0c020040303207080d00b440810814500c80244030314108445100001841c1240300002d1050a009640780c144000000341f026003451510741032000c00240d82160040c1d92440340056a4200d079004901a40e41c0c0c445c0e07030089001d0701071520043c01e80e001c001040d000e450b00500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191913974 1250 191912724 191912731
    0x309050a0f03030605040b03070905090c0904060b030c0a030506150103271703060d0602030a06050a060519081b07020307031b140103060308030601087c08070803 71
    0x39814004c840d10f61040c00250f500d00408190164001201030009030001d8102e82c0d800700d00344040b07520150ac06000600d6103042500c003642c0b4269211104485410140100350981c10700751481c240d841d2640e80c42d9a0b840310007d204108000c02040c0720b11441e8843d030010b4064000480310044003141240a0405280e24203600b141c11100003440d1110118000b41640d203eaa8004d0283c52142e59076210345020758401043e0803c006d540b001e020801d552941880e502800039603880a844820800c40008402c0700780ea00701e401d101c0e11804200000c1e075032894108200c2a9040c2290700d640452012a10300032007604010807214100c0e0101c06070b0f140d0030051100b1240b001d460b0300880510200150211050381c00007808002c0d08000240e219400340c201160000c045000341070042e2444401345450391040030b103040700c021403a0400c0c0c5110421104024181c142c4c4080c540b0f0800e02030345022011000e29a0151000c1c500c410600060150364081040b019006041d582d5954464505001a507100f01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191915224 1250 191913974 191913977
    0x8100302040c2a21090b031303030c02070503060105060903100501120312020a0512250513060305010503070603050711070f09060905060108010b031305150a0605010c050601090b010309050a0f03 85
    0x443e240a80c000e001e041540690440348501d110302103140001c00915200a40314144528600b000034500844801940300f1040f0250174440f200081c94020150307240500c200c021580404414440e580c0c0c0801c0745411100c00b20389043d59403c5070340104e0300300300c10068150016032a1500000b00d4095407048441c495219503140134500390281c05180c00c038000c3c904505c001030418040d070301c00032405200e1590480011009845040c14141c40d2100920348641440c2c005800490f14400001d036941c0c1e500003030f00e007030304040c0040d40c10280440c1e030703500662080c00c04240d141c5009c100310500412b84011042d900c20b05860040f40c07160900611000944550449a49031541c0003070040054410140207500580d2010b060b64070305440f258080d040034100000000c0340500c0712300022002c011803451052036045001062410360400c2c012204241d00050511401070f0100000440c04030751217040d10102c1c1c4000030f0703603403100004074000c04e4005d8000346144587d03a044024814171008410041f44207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191916474 1250 191915224 191915267
    0x20a080a12050a080703050a180303090b0109060803031306090c060806180108030d2406030b040e0a0f08182206080708120306040b0406231f08100302040c 68
    0x2108899a21522840070f00184104c40440c114912070340159802800040c07000c902104810b41580c2d1074100703010200d000c00d680391000341c104401d4a1450740140450f200c100491441c00c1c500caa141c1c8001082d4241501c60302d440d40c401c1082c243e20110100d500074103450500754a0b2000a8031740c11059403503a11840d840c0c1c0341d9802c40301c9e03426401c2c5c0c1070f5802e05010f9030410f20120b0070076005c0d000d0010b0842c41c8603442013480b01111190010000204003a60b40424000040801d102c00c440c65114042120741009481001003400e00c0e08076101d9071790203c0201d40d104450054041e0a101c80d803103450344800001c20429041151090100070041099420807030706564404040e03443c0f840b8411012150002c2d4160ba4042e003860002d541c0c8910007400102e6180e514000143c2181c4041d08100c00f007a03000e208080190b4140c4211103014003066421842e16218002c1e400c1034100c4565285007001070f513030000342d482c21002203600c0007590301600500c07038240003884c054502c035543d56400040810 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191917724 1250 191916474 191916503
    0x50c0c0f07030b361f0f0b0d030906121103011401110a0c0b07060e0105010906030b09010c0912020609040e0616141206240304150506090c0c0a020a080a 67
    0x4030f07a551400885409504401c1c48902210001031102d0060b101d1004c1e0250b031580d510704440c0800e0103d1150801c4400040c0f00314081700b5001110462443c15004d1000e8500001c0080e402840d2003041d01e000303084c003400200404075404007802a2807030703003529024080000110741c1c0c5407280906106009032506080c0c08030060030b0030754079010000050058202800104015888070005181290107890b000c00c00380302000c005825590280d00500c080c9543e900f04200f48114420b601d83c204a41e000240304010750028001d064003c00e00030103107004c0c03c1c241c2c001c0c119a40d0f0400c54404841c00342040c070484000085403602d66104482c1501d503002e080244280c0b40d07105900d1b02440304c4007200560b09105a61204032504030005107904d4010428149040b050810103c0c580712542c15200b62030794070329044c80c003090b070201042c5240c0081810902405126954102440d50091868030300c00d0f101c280ca216424a815800c0038040c1d000000144c0214024201141400140b4000d03881d1124140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191918974 1250 191917724 191917741
    0xf07080c100615020d03051509010807080708070614130e0f04060b010509210a0c0e0a0b010903020f040b0102031e030108190507030609030203040302040c11061b0706050c0c0f07030b 80
    0x600f007030000c00682142840e440c0d214000da101d190048003034062800384200030804110032080a0b0080e500c0c1c2d500c80da8041000c0c901c1007044901500a02029201e540d05d004c0e8094881e141c54044140100c4011910070a500072140402d07008140301c0c00b0064990400b61080c1c28011401da4044d01c5a6050080000655015600b19440b10710301070440800c44080302250401c0c2d550340c40b440140ca008a410a20101d940c001c0b161024114034082580207003422401c07941203800c075400300d070f0502011010400150351107150080400d81c0a0310086850540140100e04610640c80c094001a102c140d807182c2803540780000e14142c80c1d00c071080f60f28008000310f44849004442c0c40c024800c1d8400e590030300c005115504040c2074103209004072070030641c44c2d90024007554140782620300000e1002c070a40c3d45d5507900b0400550071006250f003501804950944500b2103108041d0080c048544900110b5a44070355101102e603d0340004e07050341d580d01410b040480d05c5062a10040e82c81080140124a400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191920224 1250 191918974 191918999
    0x70c02040c1409011b0807080a032004031209180204050108061509060a09030812060918060c09060702040230060d0213150e07021e0705060f07080c1006 67
    0x184100c0450915040e41e004488140c041c45d402090040300700890713800124100090001940b203181401d45a414400b001421282e00100340f040303c804811041c0b80400c0184121004d90741c00c03240080550b40b5000040c0c900507440d6220f4076250803008506103201c402c543c040c101b950801d03600e241a0f511280e0401c401034501111109010104000c41a1145001402480c0303986840c10014242c52f0359890b15480c940040031404211110382e010420a880c042c1d1031765610090036940125140350200c0015610b0342c004101d0030180b40009600b480707550b550010340d42000c1d4010300c155a99070002c00c04280d002c0f814070303020148101c035001c81e20100c54800d00141c8a25005401840380511507000c01c0b08411502712110003090b43c0f4100701d6460346d000c4400001409804580b66814141000000d2030700c4007007145441c480c0c03a1040300c038850b40c1001c10f0070411540212103943c0c6884000710812200c0c450f18100034a0f0080005240c0c0700101b000c26168403070800810104040fa075141c02c042c440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191921474 1250 191920224 191920247
    0x1031112120d0f0516050a0903050a0c150c03140318030d06090c0f050a0302030a180605040b0610090509060f090403090e0112020607020d0c0b04170c03070f030308130b070c02040c 79
    0xb03c5c241041442d00c428400e901038520980b4500d04004015904d460341414101042e900791030034403020f075090021064507136000c8402ea561b840c016400d511103450013880f02c815039444071607546000022542c0030106880c80c406500340f05003540d503200a00c12010004200d02d1007424102800e103820034543e5070040b20b64162292582e2940c9140420584040b4025800200340d038282c140d50708828010026030000c01e02d502403082000040314100b60420f011038000041005209483c410703100700100d070380304400d402224016030380c0d501a0740340c80c0002142504910313031072a04902c40754100414968898031410841d2081034440000f03036201c01c031110251a444001a4000c01e00300244001414200d0b803c01055014000c4401c45c503440d10fa603503210385d000c1e1307200100006000c8401d4980314000c0c01101581c00c41240148dc200c0d140c00d00c20004041c6602c0040d0602c42140006240300010b01c40303282c18198400310f02c50040ca0201d0001d0200c030314440c03003030b8051072510b00d03240d011034050241c02d880c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191922724 1250 191921474 191921491
    0x10f0b09010810050712020d150e150d05010e03030403051801050f0f0903070302030f01060e01050d2414070c12090e13020a09050903030415060e01031112120d0f05 72
    0x80002040f070800203484081c041c02c0c03c003c0c215502c4450400c0314805003440c2c41e940c03a0b0201e814000710b81e40c0c003c4002e40fa04140c0c502180b01091001b070203d04034024603400c02c280c03242c1c0c1c0310034502c0c2040e600418603e802132038180000000c01082560003001440001d20039203401c0072040040b801121140a035650030365880004000380105100a180030300f036445c43c0182128502612030307001c2402c041d0000315422960391140e60521284024160f05405010160748040c0480000d44130140304140700007030401c0e00c1c10001000c600c10320703042d04410f09440070041c043c9403505025000514680714011701761f680c480c00c0e5041c0e01a5900c00d49031481110941d0901c02c503182c4070031f101c1880340040c4200490f40310102101c0000e0b40407250042905c500c0c0c4400217152685420f080800c0400300c01a01016841c0c076161040c032405600030300c0181942d400054040c1d00413030007030200d80c230031841207815041c074800c00081d101440140c0c1c00402034403404602c20b12012902c0e2000c2030a0f00c41c01d840c00c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191923974 1250 191922724 191922733
    0x607020303040f0809220f0c0318030e0307090203010e0a0b06181903060906020903060106090b040315110309010f2f030705040b0406050316080c030601120b030d02010f0b090108 78
    0x3c0101c0c1100000c0d20654400620301c1c0340c4034210034100c1840d10004844251910713200e62403051680854850084a00176900b0240400301e810020b072054034a160300000d0a11400d05c80440032500c00700f040358083c3c00c031203204560f6561160800f440c50302d01250701c890410300f0910341c0a82d0342011825188060010440322646032107600811910754216190308044441c14640040410030314010f10744003d0140d10016a0380c60844185800c01c50142c101c030f0280003d00307008201005d00407003142c04403504041f82c0f001008983d015100540f00c0007114014082010090054110341980101c5560700841c00070041c1d071035950802c01a01e841011215807540c000344510031440040c2c1c0003140d0240e81490500c2c83c140d150002241103400c40e811140000b00080100305a07290310300a032030810251421700304003514000c0099403203440b00030140c60400c4245290038000d81c4003508031a8100c08003c041d02d90a20300326500900034020b0200341403080e82000015021410804141416214018080c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191925224 1250 191923974 191924003
    0x1315090f020d03020c0303160204060510051209010b0a0621230c071211101a04150b030c090405060a05030a140a2108150a120c050604060c05060702030304 68
    0x6001c14403003060f0194021040c0c0c292140c0d07001c0c80144000b02c18844164200030070b60040c0811038205400050060b035140116180082e002400d03101803c5100301c400d440c6907640c402c041e000d000b03080d401a401c21000c2e50003065064201149076403091014465401c060f42c43d90840040d280c550f075500580b1003510301745c4220302c5a41103141d588a051845040c1c5002c13075503a9030b031000945420702600000c00c0500007500100003400340064040d1510f40c240454408580c0f0700340b12142c2140420710480e40c1d0096920840d034261002001806020b14160312480d041910701003a40c00b883c50315114600d0000000e07207a1814007044c0059903006001001681002c0d50766001c3c030003039a41201d1852090361108c07000103000030981032400e0001c540c0c1d0115800101005010000064061003101e00e10b42c884449a4172488039200454034a020400496442c0d07003080904140380f0b420454109000060215400e9000052034100e01e20500881f84641d0740d401049031a0f01007030314001c00da4078400b001d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191926474 1250 191925224 191925229
    0xc0e0105090d020a0e04080310090209011e0c060c03050901060902070c21170405090702010b15130306050c031e0702061b040506031312020a050703020904080f031315090f02 76
    0x142d14099101510f0400616115107600400380000c0340c084070440d500108214015007086560030050440c040d003036087c1052000040e00c500e580d0000e01c4091810482489251481103542210240d0007110400c1007a43c81e000003000303040c040703e91168640c00c05400140c508694030071500150b402040810310701d170901c542c4690040056007503c5100000401441c045004484600001384100300500d036180e11b010107204c1c001000501c03030000c3da458041e26620f0381d00c0c1d03045503070643c4400c4c42d00141d40f0141c0c43c0c84864003a4203604068607882c40c24040003904402c000003140540800c82100c982c1d2440f1011400308890212540c200607040440410303420180c0c1144480510316514039182401e454101003942d580080301c01c09405da0000080009205e6480c42514950703e19201405000110f5211103903200b00c10300c0b0007409010350400042c1802120400c2d0348041d458660301c19568205290050700c180c0c8040810381c2c00f0301001d2151540012144901c91130254060070040d010f81e5507808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191927724 1250 191926474 191926489
    0x20d080a031b020102040608010b030c191209050601140402042d12350a08060307030605010e0f010e010f03020121050a2426250602010c0e010509 64
    0x35030305068850044900500314480b01c0d6004040907030006884070300c2d0410052280ca41031744500c0c040c04040080c000401514030844014441c0c1c03501c00c0b146440d105502722586610b000110b01c0b0603241c032140000300b210100703505040b100c40c40c2024050384070060400c0220b00ca00d108800f910400d5118640311007504214042804000c083d03600a2196101c5581407100403501003103030192482d0884420004079050300e045e400c0a084580041040640c0708a0b040d44944070840301031100f0b900c009506a0390400a05020b180d0014041c8a40c2d41d42e1304031903a402c1000e0715241111000600040b030420300c3c00031070381e040f142508140c007040f500d50f400540d0301c40000007028940c40381119081525040a015003030040c503880b0000181011420280d400f05423040c10200100d10352114108119804040c001c5000740341d0013038200c001c81c50402002d180030403a1b1000e03c03052140015200081042140d1401240c805070020710a100308008222640030f0740110b12408180b00b0f00c01d103801750a2207031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191928974 1250 191927724 191927737
    0x20601120309050d12020f01060b0405010309020f030a03020c0102060c2a0f06070e1003090f020f060c070b07060c0c02013501030c0603060b071104050717091b030a020d08 75
    0xc0140d001d5440d100070600040013a0015036884210303482001c0c125904100075865070840e4002040f4080c181125400c06102e580b0802d810140c6130301d00c8409540d02c8003603031741c100900101120800d4609260194940311b001c0c103640c6c05030152400080b80203085504640340c12910515103820004228030b070b010303c0340700c070780304040b052240b0008244120001c001c2a0301030b09540d21915050103011040003441301d40c00e86001c0806040420140c0040c02c00c1020f41c034030a5044910a00b061100b40114005005001c10760450b0301c01d080000660040000082c10741314052581405400d03451601902c11000e0710b0002800a112a040c40329800954800581c110342000c0c4540d0031414401000c0a06180031f0b0001c2c1c690f125081001c01c142d50f0144600d01c0140184007815040074019200c04001d90458402180216211000243d0091250700110b0502001580c1c0d00c07602d0800d824200d07540d05480b40340039540d41484c189084549000a0b0941219070f0051204178907825a64405c519904100f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191930224 1250 191928974 191928977
    0xb1c0b0403140d141f0e1e070302090103060f0302031903050415051c0501080d0c05010b06030103030c020a0b09060d150536150415180603050c0f010206011203 70
    0xc0c4611284094040010f00c030800782031a000c00c8404005940300d58038000036040310304095464030345140324601102034404a503104120603c060755076031b41d4101e81c4d01c0c0c14500ba00d060307420141042003641d0075070701501c0f0340102aa4204031590311040c480c5a0f10840b8003010f589503014054120711281041420340d00c440c400d142007800d2581e50390004a0740c8800b88103450100d0400f0903081c0c0d130f115680b61414811a40141c092103594035240038031792138104440028040008240c945420301000350000ca43c0c40310003030b00082c0c1d03e40e9203040041c0206100d1404a108102400d00081c109400c0c409450690000a01c514a001e50244040c4001d040a49401050841002d40003503a0b0b07464240754070700448800042d840c0014580e14880c0441c101c9080000300e00c01f82400c0c400c888110701280681800d0a4800050b000c515596020a0a029500c030040c03c5440b0b80680c2d4215a0640100301101d105d0007c03681c82580c0c200c100001c1019013582c0c01c0c0181d02c104010031506450000b1708482c18040d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191931474 1250 191930224 191930237
    0x20304120b0612010f0207110415050909072103030b0103050f0127090605090d0f0e010c2a05100e1e0d080d1406090f070f02011d100b1c0b0403 63
    0x60407070890950303584807001075000d98042015820b200769868103c0c2c2c8002308840410005984428003032800f40d06010355070007815900005140311404020f420050107206255002d40c0d40d00c035103030386900703c4401000c900083c140000c2207202c0d4064014030703000e200f044010040300ea0801c0b6240c5c5104240712054603120b02c2062201100b9080e51007510070a5000d8100405c7c0c51074851540e903d083c41141e0142c04001040700b41d0050150320807003042e40f21000b440e044015103c0c50070103a1985c2d00501081604052072044d4440c100e4048d0b10030f90031134074207440a0003c2400c1c414165a100b00740285140c00048078000c104540c5039454080c242003000802e07484a0803030544800c00d5a402c07284541041701c2d6104250920f500d034070320005602c00b0003150100340c1072816a91032010760300003800490a0010018902014500039040389424a221300d1414152021001000c0ea0f00c41640340c3c4a62090f2421380d07142c07881c2c00c00d0400d075843e442000b902d40d81045030554441510100007001502000311 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191932724 1250 191931474 191931499
    0x40c03150f030c0f0b0301030b040f02030118021e030a060e0111040f050a0b0408100c0212070c090b0d0f08070303140115030b01110c01030e2509050601020304120b06 73
    0x4121400c8014092003050010790300d0861610b0b500401c1c00380c0045480c0c240300c0008211758621502100c1c19203511480c0302c119900c90b45424003403041c071404003e51550900c2c3d290800010003011030745425008507088055007456141c0d21603400790784800641c05400c50b01580d40840c405400003c10309400c4800003907035040c07800c150b481d10340054022400c040f42c003103420001447d0021424014000d1121107900e06480c02c01c0459550313005128040c10141c0b83d103448050640203005108a00344050042956521079180806840302c040c00b0304c49815141031250310250070140104603419070f04c109071020b01c02c082d0f29007000541010754210b00b050b4440020905034082a6807050080a8805d40c141380071800c100d001d410344400303000e510304005c860458449070020010700c9094200c002c2c240028041880e0b40000d040c4501c03011001e140d10003e811105030901c0f081400d0080381d01000041141e6212000120f03200e104510581a900d51444040d501140601000c59042540103108420001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191933974 1250 191932724 191932751
    0x10804050a0b13050c04020301060c0f021f0e0909060402010219050705040f0e0f06040c2105030703050403031103070201020304060813020307080f010c050f19180e040309081605040c03 81
    0x1d0046540c5a07624000d0036040041000410a17200b00c0d50084038250300350341c18440c0050a8400c440d034042c013100c1d0080c0488080d07407920404060b02081d100d00c010400100c0d0080030b09401103080d41240681503030300000b54a100b010640750b000740e505038043c0c003445407901e2000a94000c00715050781c441c0541003000070a686c0343c0c8103c1040c83c1c0302200c080340303100b80311034900e0031309c0e00070960f480d600d8000604200010b64440800c005841d00d1003201614102080c41da80106244800010302070320000030400c05254010740030b00101d911aa880710803d20006c1c03940350722030007032450080c0940c5c81840188003490060801c6640503032005034281280b4604e03000a0300d05031540c0d01200d0141c0080e5610112a4000c1c000d0000202403070410741d10b448804c00c9402800d20551101c01e000401e0700491100080c0b05600c587e52644042640600380d98842d229580700c0601514201e0128244410018071040d0225280e000da5084202e00304225140209010152910007540001c06548110440710349 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191935224 1250 191933974 191933993
    0x50a0f23060d150306050c030907030204110906070b0a05090d12020702120a0c060207061103090603072c040c0f1b0507090e03090a05040e03031915061d090106020c010804050a 77
    0x4060784103000e165155003018406ca801c09031982200400c10010408241000200c01c0c0403658140c80015a18141a020b210240034041a2a0744808001055000c3c0403682202c940200c1001108000035214040c80c00e6581400825440105800c2014100100119400751040c180043c14030608000b0300c042d1141001e01c52042214200741c1c0400a001c84c40d410002d103006000b003414242c03001c10032107a102e80c0c3d90180c109600d1298100000090059110303480701ca2404840a8541d40320140d445490406002c2c00b51016026601c0c100402d40d0540c8140d01480083c1401e4450380401c49030003211500015000c58141c0b218030603901c0004002506219038999091103001560300c41d5441d8003041304d1549a90b2000b4421810541112107540000c0100c0790404002c0400b00c40c5040a0b10700036014104d02008462003c1121f40b0004526401202c103101d042c1c41c08152030740b00d0400c001004183c0b4000c0c09a1300050780001c03104039045d40580c60641c1c025009008403000c11505980d6103400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191936474 1250 191935224 191935241
    0x70608040b0c3001050405090a060f0b090c0d15030f1b0810090b0105030303010503610b03161407050c030706021b09061810050a0f23060d 61
    0x201241d0000480703d41c1d000742c00d0300b4054031045406005500b445800700355038861480c800780c5005e940309044110341d0595070004442000140c0030449a282400160030144c20030a100080f20f1f082c07007401403207903018580000c11b42c0d50043c2d591100365950b4496010550041e0307502ca042003c11000403070134900401680fa01815645004036039840c0d585420801c07176078184e00c0203010398414401400155004079040b03655841203e07600c0140030302d501110301c418031240b810209002400040104030103103020000c0022103060403104d10366075820380802c41b800c124030911108040610104403800e5441404c03100c200e0b16071900c8100e00f240d5030040c0616601090086440398041c469040041c10240042030061546c3e0026200d51565622240c0341a2812141144504a07810008031140c3c4c3d540ca14680b06000580c1040d118541030840c0e80c181811030040d40c0c402e50f20013000041c521441300400c419240700c01c240d203011f0615102d44088a803c0300191603840a42841801c003404a9449000c64 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191937724 1250 191936474 191936527
    0x9060c1509101b05070c120305030406050610090302091f140907050c030702010e1302030f0702061f05040b0103090b070302090f04090201081f0f060806030f070608040b0c 75
    0x2504103040c1080c68140d000340c031038103060f00b404008010400d007818441c1000e1040c1c1001e903610103a0345041c1054590300d8003c405510703c40d81816052544c000701a5100300d100d00b008010948407601001a42407100c0c440c1c40014000e03660600c014201580c10a810140001c866883c102548a2116112029401c13040401502034008661450050030040c0c1105032070a104e40780600c0440d1a40d07c034412030401905008202c010850191102c80c030303448500c100ba07c011500ca041500341400600348c01d0342d04100522402000c10248100c0e91880c021500c0c1480f0000c041034500f0060201600200f42c1e280e0601d603032508a00085042514000d20038400c960300142e41b003010324100003041e80e111b209180903d2400d100000142d800801c0d80d034200c803071075418128000c605402d01c803030391030290061003607404142c800148442d000305400740914002c40c103a400a450400006503102030740d00c22003001a42c00008500824100e0340720715044102060786519144060282e07180714107142e4803050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191938974 1250 191937724 191937763
    0x1504050d0312051506040902030c12040305090a060203090109030618020402120712110a080604091b080708160e07020a060c08070e03070303080c0c15070804020102070602070e010b09060c 82
    0x4404285480350f03d03032020512030700712920360720301d400b04005020b240036120500e82d0010100d0880103000050390b40621454906a245180518008055400016031140035220700e00c030120f00280080140c1e040c480040e501c03005e405107140c40b801c1c083c10f440320782c1070351501d82d06a446025807502e0005003e11014041108400d04080d007000384100301080900344094076105101c07000b0941a0101c50348009103103424082525040001802031081e103800504074243d00e032107614050f2552109800b1510342d03805942469030382e504681c2c1c40304640c607001d08020755044400d01000c80013044098110040e4411240d4103401684d910040360103207001400440c001d00200f2502a0780000421038511040d4047c0114528650303001c3c0c5003000c06407240000c808c01007203000c00210300708180411901125008680340c28200000f41110b0819141640140241c42d40404c0c1c9074000101c41c0c049590300e40908030168078055201450783c000d45120b5034007140c00c1000c0c005002003000b003910814203044611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191940224 1250 191938974 191938997
    0xd09031e0f0807050403020117040302010b090906010f050108061c030c080a050d06080a0f0303050601050d0504110301050f0108070311010302070501020a021006080111041701060e0f0702010b090903091504050d03 93
    0x2400c520b50042c41c0c0030030441308220a00060340e02c81d4900c010300004030100718882c0ca4034034003603001d4400f65900035040740380e0000301b00d192000090081d04a07540d00c0d412a4031aa1035100455800300100c03140c9402c00c415810f00115201d45006041003640689405c1a543c06240e480c501e5940c040181800002d9021906044482591043c1c0004200440041030402c0311562015101e655001d805000c0c966100001111a406201241e00c2d002000c401000540b43c81c1c0f5011b611115a0141c1a000307628040001c0c01d17070030b200442c00d41a1016000204429486c42c1c0d58080180c030b130a80200e04050f02803220728000f813000d0000d80700d20b00c4180c01403c076001034036030322408544156220811f560304001031074031804000c1d03045405480c9500900c0e441401040c043c82e026244d660b10801e802d4403c1e80420010a4000300c000d0702800c583d90003486030022200c01c020070745005271101c1d0640c3e00200017110040c0781000340d0b400c28264900720305041959400001c1c1490203c3d640990103c0d0044808 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191941474 1250 191940224 191940227
    0x603090303040302071d040303050c0412032109170a02010207080705061506041412070302090403050d05010e06100c0203161d0f012702070b15100e060d09031e0f 71
    0x4640246c0038904004219455550320b00c8500b89000d8405820b15075107002060f4016201c100301d170050042003160096040f00352030001c1c0428116007081d078803c0d4010081004004c154050380c04d445412088450303641160032800402a444071008906540d803c0082000080e4800c01801d2024015006024646056501c56149080310320101703110b840c0420040c0041900b26542c01c6509006440d5600c241103001e5040303145c100e440c0c002035409014581007100b01a4410b00400c02044052005c2c0030350f980c0e80c00d4449841c041078070055485141c9502ca1401c140c4a044054080350006040358440100b9014801c0380c40b242d034010010801d005410286102440400d5907081100b02c9860301e250b62400981d0040c020965400c0d07050306440741f68000000e81e464040d40c0b00b007504800220032070b0502d4110500300780c00896500c0d0183c440344561a00c1c280c042c0042e24401c40300500352a280c541108070341401032548000032401e01001e04c01c801603480318a4000c1d01250002d032244102d400d00c0c1daa0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191942724 1250 191941474 191941483
    0xe0106020c0306160e0d02150a0906090506090904150e060a0b061611010c06060906140d02090601030203060a0815071701030f0303090809040507092903061306050603090303040302 79
    0x80c0d10301950124052184c40c03118102050414580791a00091a05013440041e2016000c002c010790300c10040d551200c0042d5500000b0300e00700d08039403150641c00b03a9900050300e00c4c501911415922450500c0400c0050500101c403da02904c02c1e40e801d08861041c0c50f80350211382c220b4001c11800e40c0a141002400d20487c0f080b01019178084800c1401c0450414001244030041c0303000501c0c1c1207840840c0d00c03a80c5d000e50703100c441e07950b0302c080c0a2180c01d40390001c0c0001030829208a42c108440050340c2161424520a84980c443e0040c1c1504c440d6900c0310015006507002a00440d040801107200281c1c107042030055840b58051080d8144032410441e10050100e40b503400034000c00d14440c2c00401c00110108850381c040c5074141000704440e80c0e50700340240304d40100d084807508981441c04211085501c02d643d20140c600d8070030018511903041800490324900c03107500b0306140804101154151600d0310340202845080d0707201266030f523116004038000d504151400c0d00c04d640003006100030941c0500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191943974 1250 191942724 191942743
    0xc0a0308040c050111060115021e0c01080703061d040809040905010209130c020303070e011e0215011403031c0902042901020606091302010903120203040e0609060102031c060f0e010602 81
    0x2034108201180b0103040c07602d91b2010f01c00c00382c210100c01602020306009110fa080700010700106609117558800c2503c0e25547c4440c0c00300e0000c0c1c41e031800174040500911030042910102e4403294a18012305184608820000d807043c3d070200c03002d00004419070303900e01442d40c0d454420000940c40b42c80280500075404402c00e2a000c00904010303000030029070001c150b9902c808545030881034000c212005843c1c00c101c10340b107010308514803400c140096800041140f80380c609000f18140b01d80e66020b038564071100983c0310f02c0c0e054204004d0325000c055206a0551f4054880340c0000d03501ea4654005411141b03044030520301c080c0200b101207a42110612110302014081c00604641d103040303800141e22020040096030040d918092120569120740c121401560f402141c24900680300c1901030760341d40061250400f60f4914400003011410540146030181ca010b8004508141005642041c036510040803650615070b105e00001e82061451003480040400c03043d100c02d25410110028100004c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191945224 1250 191943974 191943977
    0xa06020c1e0306040b0c040902040306090b06030f060619170c100c0b01030b13020a030b06030d030b030a0212030f030403050406030c020a0c0e060111101b0212030406110c0a0308040c0501 82
    0x80c0320101e5603807808580c981d0b01662100f20082d0b42d60300e11000b441140940e40140b0700042c40440e01004200f9260f01c65800f03a400b0b002c222401e43d8034901059980c00c4451440001904001c001c01d6040c140050b10842c80c18070014400c00302c039280d99900c0841d004041e5440d0b169406201c941c040c909228404d0580c001312450640244e01c81074076400d0310144103106c004c010700c4891002400152103440810010f5500604400f4040e03a40d0411010849090700c1d041d129024907846005070501902c80d0490000c400f4000d0101290030750208110045605852841030000300000f103140040a00103512441c4292115074841e414120b0090464025407550429984008584404a03842160b5003044900d48081041680d84d11001201c0249824901c121603110308040000704c41040c0e086010345044030710f0101241000110308a90b603041c034106131300f610242000464081340b106d0704034095050305a8030702840d1000c0c0076125840c0942c03180c0180e00107000d00301840f0420202d68038000080c0402d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191946474 1250 191945224 191945269
    0x50105030106020d051612170603030a02060105130b030a0c06170108100c050c03070b041407030f06020c120408150115090605070c12080d0b0d030504050d0c050a06020c 74
    0x42c560701a607100000001e40c801d0200214151007050300c0000520305032a030000080c40115038802d0302800b80d44010301d10980401e8044001003150030000b09690128106034002c2c0450b034600024000740390132130500035040395160030075040b140d01c0c100541190b06102d50000240a40f03001d1004084008400c01012200c121800400c008400028616280c0310f0424000407100d880c10000d42d00c0784500307440410355000c0400c00b5810300c8141715540784928080c843da01d10f852440103900da15a81c40d40001040700703448450b004081100c0303070301a1680d00c02c000100c0d00395000105004000c1c0d0010f90045015901244401f5010f80100e0a110700408100d5a100912005072201618180407400f4400c200301000c120b44040c801c0c004006001403000303204101480810707042100041c0c0c4445907008085040074500794040c1030503042d0f40c0d0280c0c4c15640c0d87e401d10f41884100424080031000c140c84503d00c0b18004a103543d5501600001840d04e41c0040074104c5082c000e12410346101500d140070a0707003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191947724 1250 191946474 191946479
    0x1110a0f03060e040209060406090e0c0a0b0c150a06090203010b07150e0d030e07051309021f050f09011e0504090c08010b0415050c010c050315060c0a0204050901091415010501050301 80
    0x40300f0500d80c2180c0c0c104c40a0040b40d41d5070010800420141d1b002103645402c01081c01030480020400c01c030242c41c299500410f090b00c0351040420340c86501c02804503540040a852600b1801c90380035508040c4090000c80c0c1d1641c0c9405c0303601685c1003030f0031040d40b03200e0000701c0004001102d424041d0b8114030f42002d01c030b55101d140c0c00c55107948003210080d040c941c8801d00c034035500009025110290600030480e135000c80f071b000507000003444d003280124065100d03001c00c004c070744840100c45660072405607207651411045817500421604125042c40c14051690251035500c0c41d00748000c01603000d03540d14203444a1400c80144191550780c44600c060041040c01031084404d4441214140d41c1c049603914510208035204407501d01c2000311404082d403a04003040c00302c5501c0f00045008400c0c0c8001c24400012000400c00c062081c800414640d43c0b080d51010014180758100503400101c07000001108a0700b902ca003c0e80c400d2440d0f4490766500030840c02d900c4200d03e40e441301d003d0300082c80c04e14155030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191948974 1250 191947724 191947739
    0xd02030f060301140105010f0207050a0e0703050f01120825111005070201050304080c0f0601030501140a06052d0607060204030b0f04021c0c050a08010209010930060b0301110a0f0306 80
    0x61301070164a040005170824844580e00801082d4020500a40038007035a0303540345903c0808041c20b6640000082c2050041103502c80f07500040750603100600c003402c500010690340c164082d400356402e8200c200400c0c03484000741034440c01c11a0b82c0742c010900800348a140004200000303440c0b840b224207104003400f0070300141c7da100c025254031541c0300c05029078681000005030b1a056079a0700c2c0002a02c992000402000019001625040b05501480000d615a001c1d500c05a03206801a00c1e0440c407111350404c00308001d41c011a8501d08410310100b40c0d10103a50124101c0d43c0115004d46841e60005010020007102600399548a80c3e5030ba040c410314281540010700400000a1891205008590071000d101061606400601c401010003e10355903501c0480d010307400007400035003c205c1e80c005c00282c107100804580d200211082c00317142c010000040d10500d1441d0f1003c2559415514419039600740c6003407142440c1c5400036200700d912841c2c0d08400401040e0784803a18410541170980c104200d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191950224 1250 191948974 191949011
    0x150117100306020c070b0417010e1c030207060e0601060908060901020906040308030c040902070b010302041b050d0e0c0a03030305040227060d08120403080907091a040c140d02030f060301 82
    0x882d8003a10140c0c0d100700c0d0f060901d241c1540740c1c1141e0000440050300044c41d8401c141d110f0099044600288035034030801c000b542d11004c4078a07680c0480d107449441d005102d4407940c0104015403060300300151260500e80e4086c030700f8074241c000b01c001c698480c40a100c0003c042204c20b5120810380000d502c1c100602010458a02a030720004150f16800310200f812078100030191005000801c4007191602c4050903c2a0014030038441640140e1500342c501706c003c00000b1101d48008466141c00b4641150840700b00c004000c2e094a40b0b82d10300800d01000510341c0c0d075540d260003c0d4007d40c0c0110303460038a40104125903040004180c12340c0040354402da00d107140d8070b00456005104a4007841c072148181041c216500c05d254004d0740a003048030403c001c040d08110140d014503001030842e42886c3c0c407200c0c2e40301200c08100000c40070f00c000c070b80e05003c00c0ca02074000005030003070341ca00114501e500483c510301540141401801150f0080101b04810070700d0701c0180d91100e4100c00a0002c1c41c0200d640c048034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191951474 1250 191950224 191950229
    0x2208010e1605240a0c020907050313080306040b09010801060602010c02070311041a0405090601080d1106061c0b0f2a030a09020a05061605190209010608130b15011710 73
    0x310481e6043d90b0340041c850281c0000d03030f940e61029695640d640c820003826200c1d0240228428400540861040c1d4401c0c03066078402c03444810740c0641c00b2415102c0b880c840c1c000421890b842034480d422011944c40c0c2e440e9441c001c14400d400031596908140005c0d003034030052400e50085520440c3c04101085102980d50103490301a04d002030007070004002c040b4020204290a0b0b0018200410722400701e42c002344d001e040701c0011040c1c44400c660504101c0e284010521869826030113a408580d503444c140981329102007103d10342a82c0c4188650740c50081200c2201d251482c0e80e5001d04128000c1c03080c0300d1803030b2001900e42e00c80d81d0180510461984c0d030301019202100d8280c0d82c480583c219281e4070035003009007100030105500c680381c8400307242d101c26a2607000c86d200c1c0105015402100001c10301e5091251340103015113416070070a901260311100081c80b1000850b250039030b080c0031500400c0045c0c0a214150340000c0d100d00c0420001d481100a0301e565241007212404000044c006a040d0344103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191952724 1250 191951474 191951479
    0x901091803120b0a0602030c0601080106260c0405090d1103030105010807210f060609050d080a1b0f0b04020f09010b0d0c022104050a09050c030c0703052208010e1605 73
    0x50b0014080711007001001d8000b101904881c2460b0080b40c010307000005001442501c10845046a80701c02c00d060170780c0d00302c1c4903c840030140c000317044107140707500c03468000359403a80c2e4210b801010706c2e000050144d500a0710405c050380c10014400b4490756000d10100d01000c4190011440c65140100081042c0001000f500401034250701119010500540003070740c03034511450078441103085001c003070b000380f15612a26010804840e0001040e041c036060642481e60007915041c20301c002028203448074041074100400c24041d5100580015217910f840014250040c40501c180785043e1040c0141c56280c220000d00c1022514010442c902d40e1008a50308c0e00c103100c4020070703080d406001c16031034440a6138000c2c46645105180c4180d17402d80b07002800840300c080b07619100a47da40e0801c2e10441e0740542c1c23400c280700001c10009102c0110708009103100c3d4800d18042c0e1500c040f030700440703003480c900d2200920080d685c07400c03c0051075000d00403800e8846040c000b4028000c102d9050350310039a0648607003030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191953974 1250 191952724 191952737
    0x12090d030c0f05161518030b1905040f1703090a1202070e04060509120705030405061305100e090c04080c0d0201180801053301080916030609020901091803 68
    0x2010452880c4102000b540d005089a841050107294000855154041c41c1540356501480c2c0074800e200e000e41d501e100035034810b100071141c190b448000040360014800c42c408081d10b00030304142c10803803080d588200d002d807003a50100c0010f45441d00014010381c403140c00200d42841401a100004901c400c0c0c00e60340010940d9001c00a64001e90625a2690105140d04000300800c0300b030040981040384a00c040105403443c241c0d842d0800500d034011504041e14540c028002031016040c198010018201d10b0b581114401d5034030030010301880940b4401300006100340700c0040c940d040018125030003405031200c2601749820503101036030f505104e19400d44a0b8020022070015039000c2c59004010300410341d042d0b0391036a100d00c0300b0341c007070a000d4581b81b85e29407150f0080e104c0064440005413421043d0903401450080310001111141c4010b01032046c0c40c021210312800304500800128000d510814000c02c5003045801000301100050b4000c2000504200348003c00407942c02082c51901d5050418a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191955224 1250 191953974 191953997
    0x30114041a1002011b0c050d0f09090c121a150f190801031110091203030e061e01050402030702150a060f0e060405100b09060d0b040f05010812090d03 66
    0x81c141c010301030904a4008500781007034080c090703040d00400c8240fa05090300b50120134007580211001001d18001920725002424800d4183d403055400740c0300b500e500c0c90700f00c0358240c035489900e04079a03211408401060b581d072002c6a8942d00c81c01900880d08446005002000c114004248441d8440c2c02d41c3e03144850002c3d029a1f04c0289a00352070388803c1c088110440902c210fa0064450700c001c0c0000e8800301c800d8074610340d881c900140c690380480300c1380d511400d1041c60400c6451140135050070440508d80c0341c0c42c0b4403240b43d104102882c400c0d803a1041030315034248594640d001000c01030704203602450040081103c41500052a1900a0340808103800315903207402c940d00090a00f50441150084403640000c0c40c4d580c0010705038001c41c411542089141c8442d071a04450740b401307116640d4a503509200c1030f0054a070000c082c0a400135402804640c2d0389200c00042c0c126111002144801076585006008000d410800c1c40915030345c0e803444070318004034500003c042c1c1810490040c204840c90140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191956474 1250 191955224 191955251
    0xe0307050411250201112814010c0e0a1a040510050408060403080a0b09042a03060203090d0e0d050c19030b0906070f0207210809030a03020307110603011404 69
    0x121102c281c040c02d414203c403500c2c802000c041c0c959034078040c0d0008064218090a6402c00b00301d18500d021691000d017090344d540700500c2010300c12850261007082080c0291810307034100b8010102d00006590315400c2070b001510030001d9080e02c60300800c2c15900c0f03580380401c005503401c0844098410440c0e200480d0007811070116428461a08040b440d03008940a100401da0030544681c0a40103031035050001800240900400c070400b2100600094120b0f0951000c005994100c1e0712810740c68848120003c0c6c9030307203030142664416560160580d020046600c40740746e0007513082e0381c4000120364007100344a80340c540e0b0795500c146a01c018490108910210940c803d002c03000030042d40d001060102c246400e401c03558541500703c55400c003140001603003100b13240c0b000c54210141c3e1840070f04080c51100c1e0728945070054080003030450f0301c080200200c200f550780c204080f948051081d40115611405840c1c9800681ea030084201d0040d40c0038001400b40d4001aa00141101e2003602c0004600011949 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191957724 1250 191956474 191956477
    0x50d0c1e0e0c0f070510020a02070506090603060f0102030d0e07030b010603050c030c0f04030212010906060918080d061d0405070b0a080c0d140703020912070302060912070e0f0411010e0307050411 86
    0x802480341c410051846d04000607070300580641d0820b41c0a550a1135924010310070b6601c12041e14a0b0f02c0141040026810314002607501100e00040c0b0440b0304150303880342d042040b21101b5100e1003e5a2018104004104800c00c0841c0505041c1c40d052104c2d007041d80b00100103000140500184142c00b0501e090300442d48410388000b1500106619070f5a5410090503000b0482d005080d9149810450b0100703440f0700d64002d5640070468928442c6603940f56417652030140c5c02c0504180601c0743c031214000303440c0c204e40246070840c6200c03140d62119030500d403521380c2c0380c1754950744078410100d001c0c0403803a503082d003003a07100d980014103154107580e60340b580d8000030040074030045910348490f0f01800e014400f07074564050019454280c0d00e015881c0307a01d03444103030760b599140300080d80010100000141401c254168600751100070086940e1152100041c2f94070b003104039040e0001c0d0580404000c00c2c00128a541ea04242e03082c280701e900b2181000c082900e44c2c2840c003d00c0d0095486241074000d00c0c20090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191958974 1250 191957724 191957737
    0x20d05100c0305150a0803040603020f09060c0d110705150901031d0d030b01030603020d06022505030306360c0906040b040602060105220f0204050d0c1e0e0c0f 70
    0x3003000304500303400c00600103007015280d620755005480e0440200e420442c0804069680200066041c1841d00c00120080d5200141d4020310b40d1042c03002c01d00c0c54a0380409000e420745070001400d940c000120300182090b00c0e0000910050f0301c445000c002c107440c2c0c0c410b45000d64400720400d0340d88400e804c0059024003002c105c849a81c10b00e0168010005c00d002c07078001c6800304250f0b01409a650300c1c40045059840c20701000c0d62060706030420724001a0203074001c00188440d0900c1c1d464044209004501c4c0c0c044034103056925030000401c10903030f4500300d00e580140700d4001d0303c821b03401003030f90161407080b05000300e050001181d40000b00d40030241d05402d03280d445100609199940d520b035a00c00c0680d400920800c000740c0314040001c40c16103444205c40304a4101c4101c0e22880013000c0b0340100143c0902810300640c2c660802021031241c650b00200a203080c040ca16007844a850030200391102c003200b8051040148a0100901080c0c82e034600054008040c40101c5894000240d07820740c0174070407070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191960224 1250 191958974 191959003
    0x15110c060702060402010810030b0f04031103070c0e010b07080a080606220302121234030c1103030a0e0f0f0a030f05060a02040302010f03020c2d190b0103020d05 71
    0x303204201410740d0000e500d900c928400e0b603456040e600d0741d04c0340c40c100b1015400028000802d6000048104440b0030245501501a1505006581604040900310341c0410310035078119860080c01c0c050860f52400c007070300504034251094685015600d5516040c0103801068041025000202e50b66640310810749181d00c035801300307170b00e0031480d07103030030045d1800c0e03244000c90080a501c54a810369441c0403588019003000c00200f24a0300c1c0035000d18011050580c0d44a098020036411141d000440001042c1074207446034a440c100550b070383c10a0702d1a684000744440c805c0d401041849910359100f16a00381500c0192484002c6507100800920074010240c0070030b8002e1100600001881458812081181c2c080c0003580c0940d219401010240e00c910b00001e400314a40d50310b425800e61280c0e000300300060400050b61181124284007104545140d280c0000c21040d0a1050b07104420a02401d42201070741000342c0241d200d07079138901c45c4a40d814800039114030300d600c45440502c06c041c00f62080b441c408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191961474 1250 191960224 191960233
    0xc061d01090308090105060922060c03090311010902010f030b0a12080304030908070e27060103080d06050402030f130804120605101514090a0b18011b15110c 69
    0x4010845008204a020a60000c0c9011002c24190881845105d01440f0040c0c070801d039030754841503010181c104000d00d880702005030203124000314205100d1080f100d4199500855034000c1800c3c0144140c00c1030f4000c050305d0345401040001030303030071074400e14030103400382004224100000b00280200da8103a2141c9100c121a60002081040100007144514030944850300020b031202000c42e582c0e041c90250940c0c48000d800070032a0070103608074510041d00c0d0401e0a90368000360380c4181e070801d00285d04c1100c3e0402c012401e942a030280340641c8000c0d24017900d00b1821880c000301d5100401d40e01811444026030045544400c0c17003040802c80c0e014003503d0081600420581c5031810040808079403504e6810100140801c404440c0d015040c40347c021651b407003055119030b001500f400d1740301d092060b034448010280012104046c0b0090240f803650000303005050030001e0001341041030300e00c40c03c030108250740401500140d40c43d002c01c11180390303020340043e500c036400614181c20712403c009501399104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191962724 1250 191961474 191961521
    0x190f03060b0c033402060310080d09090615050702040c090f0303050405030d0e0105180102160602010e0f0c0a030f020409060204030b1e06060412050304050901080d110703080a0c06 79
    0x50000090111302d80c44104140005080311070030405103031503511450b154807055113081c090f103041800303143c12011550100340301c6c0b0b07658401d4a1806240010314804140d10400420002c1c0023407048000030001c82040e03810741c14180c1d50082040c4030b60900244507540c0d403020314903400e10564000c40a01855590202003c4c0c490030003030943e8116100c1c1034420300c00d01902400082c80f94005090f140d0041e111305003004440e0103c0b44a002c0d003500f2480c11840380922403080390203400280002454960000a0444401403989003400010303101c03c0a03a40c070000101884d5111400403400b1240c000e04100e105501d54400503000e0410030713002905440c004900401400010320703070503004410001e09040000840540b08800c0d080440b0001d41c4060706010401107034034903050300b10250384107100740c2e4501519200002c0c65603401386c0040c00301c0e5010700328200225412032800913001c42000d00800f081440c41d0399400305071040006500401005c0c2014808000440e00328220700b2020700d155600052 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191963974 1250 191962724 191962747
    0x3020d031b200a080a121503080901051804020d0c090e01030210080a0f0501031103010e120301050f0303040302040c170c0f0a050a020c0d120e09010f06030902060f0a1e05190f03060b 80
    0x190340601d003c144c0d5141140e1000c4181c07a1141c0407089a600c00041070500c2ba01303000668058100c040c075407800000400041c15150b0342d9100408a40455503400240440303c900020004500c0741c002100c0e9295400c0184056a034508540c60b43c1c400c80d241040c0f2a90302c803a146c102808080345040303001d5050400120030802c0c0c0492140004906800030403041210048282d07441d10b4001007a00c800341308000500084c14050300c6003480050103421a80b60681c0c0368045011500310901e0740300068010784440203200a025003440d0080740300c088460421804440f064441e10802400b10309110700081c1c00b013a014001c0c081504010801020038003000c15a0621006201000768030400007400402520b006150207030b0b034a4140e0740000002070800b400c040080c3d0092288000a9030b0000003408044244910701c0300620355051030f5516140300e5145940c4155050b46e80810500c1400b0080c0303c0d00054020308064140c520030285800d40c40740380140350540042c8a283c11040c40000001100070310103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191965224 1250 191963974 191963987
    0x115110d0906030c081302040c18090204030615031106090d0b07030e0d02070f170312090319030b0d0605101203050405030606030c01080f06010512010303020d031b200a080a 76
    0x100c0b9036403000d002449004801310b4040d1002c80343d0759684071700c218898000d400c250b40b000c0903034441400c204852840e15104982240d1141c0e01018003103800040620811060f4020340d0035109400070361b08405804c540e1880e1428850000d418000d0300b022407402c0c2c669a0742d104000c65030340c201020100318105024000e01411540c00606030364031400004000b250300c0040c265003150842000811101d0501420140000301d0b000030391100e1100b403010516003035443d610140111032a06c0210b54520420300316400c0500c440c2c0202041c11f00d4500400d149440350340700710a001d13a00510000d45a41c80e021400140507494002540c0c84815130106030030035800c000100140c6004400702c03421a075440c2c041580d1a8680c280b82c60006007040085004243c242031200e8001c1e405040042c00c240039100400c000d00826401500103a010401e254041c50300342c400d420000c548803041c0901c0490304400039103651452494180c4915a01155112001091103110000d90780f1083c0076664070690326005012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191966474 1250 191965224 191965229
    0x303181504030509091522060e0907150903020d0b2701200403030903080a030207080708031e1026030307080612060709300305030a11120115110d09 65
    0x1e250050086800346d0451003000415010003000210311001d0094160304041028800b10b140d40d845041c0425105181c00310b451043d501003000348546843c0c40501003150308507604030424000b030fa40e028800350711181c0001021079045032201440fa150000d85800c0031035001c5610701d85000c580e20002d4003620640003c0d0407402018801d04401402040072507052259100040109107158410000265840c0c05054258500e0030b0050510500c0e032280d110700c1e030140008850820000007000a140d190319800000c645500c0c200b46114508400301a80080150141d949841c45c464403612102a601c00044035036110041965180d05002c44080d148941c241c0307a9a2044074149500327000702a0020300c480c403e001654a0380c0042346004c8440640c0520134808013a00d00021080100c003400125000b815070b40b1075914641c2d00d20b440041c0d141220400411500c43e41010400d034248800407440380e80c1500c0015558588210044406a664600307401d5070380c07028000c529822604907040440c0a04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191967724 1250 191966474 191966479
    0x19120606020105130201111c08070306080102030709050f030304050d05030405040507080411010e1302180f030109020109300c06170702060411012601150509030303181504030509 78
    0x94151034080690aa030310844814143da8024200c0c0405503205255039004682c100040c1e880d280c04084034075181c000d001000c1c038041164402403040880c0e2502c80c2170000e14880008508608040000030a080d2003407003124400d003180c2031b130031790310356001d2084600030a4002d210342092901840c00c0c41e12500300d80314440c860b03460000001da510f809900e120340310303a920526600c0503003011401034035204d05100b00d4a400c8201c84e0907001100f1881e20040c0940c80e01217141c000c1e41c0d20700c1010403c0c80400704c0480c6000c0e9041c1000310700180d8101c02e050041d50340000349800720000c0d20060f42c480703200d01002c008558080c00c60007406e20104281000640791682e40d0807003516103030b841007039000701c05940c00030040c0d02c8000010301203481c1d500d00001264051422003498100040340510014030300310000c0c2c0001da96001046910114000c902032130a85080060a0044040010b900c80c003000380200100800140b214011490502030351140340c00f1700480999034102818000c2c0180c00c8035a40d0b50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191968974 1250 191967724 191967731
    0x10623010212160507122003070b12060312130f0605030c0904200c16090c17130209040305041d0907090f14281509020702061912 57
    0x105500c003107880b841d60052001002d180c2040b400c00c005050101c076606803080e00413054017281d1420308a0f01c1003c00d0b0301a0318580f01401d8040c21000e060811240b180303100c0d5100c100104100d44045003510307880c07126042441107070f58506022030b0604c0c440d002e05a18102000401c00c4200081c400701e03905035a41c0c0c549065940d80c84060a5400d4031040e91941d600c26420b06c0341081c140351a42051040c0c0c2e905a20100b03050705034490308412a00400c541c840c2c90341007020160000d003510181203000f4184441c090181c01d0100a01400548020400d4401030300d20100280c441c2e40200c080003001a03001c0c242d600c641c585030030010015005030041c1030841c001e00d14605401d040c10f011031401a46200301400c4100d00c0c0454a800030064028403034002a1100e0f08050400d00f00400b4910032003100d90440622003404940d001d9105000d52050700741303843c0c91980f00301a04081c070310f0307426200104401030f511480c9000141c00e5000c2e0601d0200c0c00e4581000c003107072142d40110010190704450760b003032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191970224 1250 191968974 191969039
    0x120b1801060903050f0105090a0f02040b0411042c04030e0303041206020405010e0d15020901110102030109050f16020a030c02010527010201270b2d0906010923180106 73
    0xd0301f46c03071064852820079844914481d01058959a01403140e610080000a0080301007005c2000e86e2010416100ba081b8045020400091417503030003102c403210340c645081075101541c3e00c0c0304240710140002d4100302d102c40c001000354400b0401c460103801104041c1c01103003142d141103000796026014a500051004118881c0c0781000008203015035072100b0307044109036000800300b0003034002e00059810051207041c00b10300b0072002c3c4015800f030407102001290601e40a80d41c035080402c00340080c940000f0822091100681c00309240b066940d06152084011142e400101c485015150801d51000320110a80c04001d20415145804036000e8000340410302c01142ca504000b01c0c0585110300e1201103001c1000040c41d581d01d8640d000e603103a50030110300d604680c2e214031140d5000d059481421100b9092103070200c820407125004000c1400e0501c140694428940381103011010f00280030000c0d176012a220790540020005108044402080140d60ba000d15002c542c0000159140c1403c074501d51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191971474 1250 191970224 191970253
    0x20702060c010903030b270a060f060801080d110703061802041a150a0909020c0f0f060703050c0a0903020d030e12030a030e030414060d0605030d080a0c0807120b180106090305 77
    0x2507e0084040ba030403100144001c02440744044014034410313400b6518000403402c0c2024043d0038000c1d168560380e040c2d5542c189050103207003500403034007803003030040042c611001c5490001d903003020780341d0016021807213007448203844c002c0401d4070301c0080d442814402034180c0c51103003146000d1009000c4842d030701c001d070a042d0740d04104d2041d00c4580002450301c1005100f14045900107104610b800403c4032080360114104900382038412030220b069400400900c44025418000e06400105010504e89480000da0014107190300611000740110b440c2100f040500d800f554141660180c0542050080141681d81613200e80c062404080442e01d011249603028400000f65001d40321040e0700e1f0140049221704120382500040803d000c5103440b9480810310b038600380898205103c85444011060405c842104103454812241108124503201000031007688100700d0b5621818089001500c100c0c08800300d05088401c0101c13032940c1440100000703040342c2c0310301004202c2e40200306544c09423405025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191972724 1250 191971474 191971489
    0x70e01030c0e04150305120c10020c03090103050408090a0807090f1803110a050f010501031202030304030909241503230703051512010903080a0603020d06050703020702060c010903030b 81
    0xd41c80000c1d4801d42c02030070a003055840380344c07074580181000c4403507556980d826180124480070350030f88103400b04100120f00300401007814140154101542000d54002145580c0d009003480c030703410140c6a0f80840e044c40907140c12100003071030241c480c02200c0c4d12101510341d00c00c1d072841990f40d560f00e0015207094400c100e00c5940a103020600c00700c1f843d011940c50407182211000c0341c4007024040c60b07411900044040102484000e54100007080d10b6166041c1028600a003c0c10b0a081d500304004000000794402c018070280d5440040004140b11019910b00ea18220742c0e0720407003108407510000c41c0f81c8184900840c107a6509036001d10507004644d6102d901c0520000b200d0b540c00240001040c0c0d45802900b2040d403044e51210b40c01060381842c40083d0884045001c841440e9544024003800d02d5800079000754000752003201840190b1071940494441d40c045680139265503556401328560303500c41e03012140c000342c005020513250359642490900811020300200c011900e0010040c000d81441c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191973974 1250 191972724 191972741
    0x308010e061903230a06090b0609270709020a030506090105030312010b0903010f06150f11030403020d060204030204020708030121021807090b210109061521090b070e0103 75
    0x8040b0300089285a44203031142e40d0060071041c0c940c1aa50044016080400800d00018060b030404a004561800d280d001c030000985441e0003183c540301040f1100c95450039490f051001e0120390007807540070000d40c508016054024240450000444100590b4141c02490058000b1540c080890b644c0e81e00701039076442240071021a14000100420807005901c01405d6240c0000e00082284d51554076a0300c21a10690065520b6007800015807000c0d0f40d001e8030b88803280d80f0034102050412800001260360340903e100083c4a4086402000d080210a8058400450b80a0025921038260341b610270255002409440080d80000b501110814001c0314100301058010340589055079541c88000f80e03200c00204180c05100e0b03c054001881001c080040030120040c004d140e407080b400c0002d1002c06032040e0b00140c0b140c1c1c242103052103080e0210621846070012810b01762441032070341a400450444501c13200302d00500d410140420b10a4002c01c2c103105d1010380c0e44102060750420010b40444000c107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191975224 1250 191973974 191974009
    0x20f1b041a030d051602060703030c0305090c03061306090b09010c1704080703050309160b0318071406030403090b130509010e1009020a120908071103030301030f080913090308010e06 80
    0x10403c401030f0185004100751805240c000c0c0030001d0903008111140c0c410a011400039a4030061040f98640c140b1a60b42c014034848047c2c01c0035132002c000241e6440c0081c10f0084802c1c0452848420081d0f1540454441c640c0840f9003052803405005aa000700f180754464030120f9000010011031810400c03c00d0700c81c0b90301482c030600706082600d0449035500010540c002510555100d001800c214851050003015004900c48d80d0313192181103030340f00284005000c513a69001c8007090000c5400c00c4a2100c8a09041c0d40c103a0312507860341130840700c04000b54408444140300040c2d0300f0107200510628401e60380240c40e000e07920b980e00c0258a02d40001190000103d1000c8401403101a5507070b0000d01c094041c03490844035294030702a080301200c4050301d080b00c6c40c1e0700000d0403804214124104048064007100503500b0b640c034649070000700300030324000184000b900280b9040f55944075010000114500d14040140400903d000350040784280154032070400950f0000d81c00b85071542003211611006d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191976474 1250 191975224 191975233
    0x50a081204120c05040f1e020c0303010911090915010f0e01020c0d0c081207140f0a08030720010507030b090114061c11040e0a0504110d03020f1b041a03 67
    0x620440c40703460381c1c0c030b450200c0d440c00d04800001001e94450140695022803040e002801b50f80c1c0180d021000303000e915502148a006004c101041c02010050320b044403103520001c00e81c5130710150044aa80301d640020359000504001b440007490682d0001c4200c00400c1c0c817802d052041091003038034815064100da0740103078800460200c41d820015500319520780b24112a940701034075070407403a05005403540035500e1040f000c1155000e20100000a00c0340041d0301c400381c04112004658a03845102c043c070060300e070f81c1e40000440c00c0588520a1550361495850a10000e0342d03244c011540a00380696140c0d000900f089001c0286103000b071501812903903580c07001c16510018600344440c603081401e0745c4100103264414040700c6416030007680160134110088a13950303070821183c8c02c030450014006006c01ea04c1c0ca020000014410480c0707804401e0115000c1182d003000c2d103012454184050038401c5a40286504202103801c0c0304451055001c085406101070000c1e4048911040610b486440c1e15520 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191977724 1250 191976474 191976479
    0x1812020c030102040e0711100f020705210301050d110a090b0f030c0109060309110a0303091a040b031b1e0a0f0c020306070f05070c030317010504022118011401050a081204 75
    0xd007407443d5140304030100781c808081648d80e000c411100c0d1341009907482600022203400f044814403008041840e04a00b440410609000702e80403400305009190280b84800d0001c014440d1a40516042c82c10040164001ea621402e22001a0000c0c3c0c560a0140c08414501c0009140100d10041a07042c1a5603400c6100d107044e4084000e0142c03c0002c0d00c21040b05800140e171074480c40b41c1c91003d5402600c038420b5043c504000d4403424400c88000440004040c00148080e015001c12203420404c11407140d4030301900d60f40d01e20503e12601c90b50188400c02510900e03030900700c56026200d400c00c01d40701c040c64400c00e10001c8e100c28090000096040c1c1024000070010f40c021004286c3da4429403a2690500d16203a81e000c050b054070703406c2617002c41d0032115103201030540411098050039041e1025030030100e40f650350204071468031080041464a00b00014a076800008000b035900307504a00034010f5401c0310180c0c0c09451000c1c02138034080c94078021301103090301000844484c0c904d0a80440c518162 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191978974 1250 191977724 191977727
    0x4110103050703270c0b030910020a050d0510030203070603060803070b070c0b04062f0d0c1814030706020102070201120506011803060c030c1b11041812020c030102040e07 75
    0x2070000e04000030303d580e9900444c43e15266400c2d03900d152100800d51111807140b42000700c0210a554001d01c110b650810802804440c00b0559800c1914120700141e150300031250240c070180500c0740c144c0c160b140f8140410550000b50181d80c800c80b8000c6d4191112540c03030700012001d44d102c1e8041c0f40c0441e8002c210351800200f0070410035a0024240c5010303a60703e166561420016182176074141d070304075250309004c8414030705a0480c2c0b000c0000c802070000d0703852106242c81c2050149403000000e03680c1c2d036042284103601505c00c032031640300e40034a2000c1c507075140c3d5050103221410740c0800e40244150303800800c00368014402c54140e160140c440b198041940c8907030b50050f110041605d41000100003061183c0300c0001880400781d8480c140200740c41110600040484601d02441c50070403680f40380c02d414034140e4005000e074150700940d50456004640740810050b03c4442030603500c03a9045003c080500c10990549503012081e6030988100744c0400c0d040509034003950142d119460711031000300e49084d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191980224 1250 191978974 191978981
    0xd03080a020c010507050a030c03090b0106120b0307090f0506030a0b060d080403020306100305010e06192004030f021003020f0f0d09060e070512010203010f170304031b06030b040504110103 83
    0x5140e40d4009450036481c8024182511402d4030400c000c25130114000e50026018082c030940802c06180c20003c0300029182c00014040612036a01408850501b5021001081d00043c0940d4006412a50784a5813400c010004007849407680d10f45500e400041034042ca8046023001d10180c210704141c0e83c540381e107020040c15030054402150011010000040161400d001d131a10880818003540c0481e461410040d00303403012151492b825070461400c000513824070b01803170711390700d00d00080c0010700d00d40c811420458441035242c0284903c1010030700100b0040106c680a041b18402e403a085108829aa403c0d01640a01e1441c2e1050007810b1000550b06890240039041e41d80c1800340120703949040352500c00440300001b614803580d800190050109040100845148201c0c900c02149107600d4603c0201c07840074240511203144103944513102c2c041b4000c10a85010359080409400c007001000c1210000d51100e100b40340100b414145039225500c0c0502c590f0344202e070040900c3d08002c18050044004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191981474 1250 191980224 191980231
    0x3314092a150d060f05040b240901030902060c0a0507080d021002130321030509030a02060105040b03070e0a02031f0b12061302121504181502450d0308 66
    0x10501c10b12515400030100d0003450000e18446005500319800c140c184016030384c0b13441441d0300800c1400d007882c0035050481400c011140c03404002c0780e04d65898600403005029102c0020790300c440041060004140040382000c0721601c030b04105e6503010f54401805403500e000480381c0f40941c10610708150300d00c0d043c3d00200180d880d440442480d450f202c0d070b02e03640f04041c1d21a030000014403158141648541522030141c0014100c0021401e12410400095484905004079409180c0710b080c4c1004c0c1d91002c22185c0090074001501d8001450100f0f08003000f50011183d4000c0c408802c2c2c074418610031300b00c00d8041034800b20442c151401811907400602d0302c0c0d01801c1950401c01542540003020000d02c054214a03520980310700341030800022401272040c182800328032a41c6008080c41c0400c1500407000b010716486480d0384c0741c0c2114650604024000c2d00030f00c2c0e0300c11445250b0100840c0c011410148007004940180c80d0554241029401c145044034207079030801114000007000c2070007885155032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191982724 1250 191981474 191981509
    0x50f01150f0e0a080d02010c080112020409060b031906060509040b0f060d06020a09080111130e070219060b1f0906050c01090c0303030c1106043314092a 67
    0x54000e0380300491454102130340414080c0d00002402e143c0e4030760a01402e00c00c4a02c82c41c00e5103855040003407660f80722007001c0c0000c0c8a07965402980e07040000c260404090407100500341e40c2002d0104102d24070344420000200d80c000d1420b00007040c2e07803911500c95400303150440b5088180e81d5807078469000401c4061319846e4481051200000044c200703000920260a90360741c1c881c1c45520b84611103094514241c1c1c001c0340c0000501842008515444050040741d94a242c05403281c1c803084001d0741020740c5100e10328442c4418071025418820702c0c1d04051540030084c2c070700c001c40002e00091802d5a04080710b01000144180400b0004140308402030005130164800000f4540d069a0318031442c0407030365000320042511071208007007075600a0004400c0c080504042c05080c601551511160405188024441c0682d5440003c10040c05820000004440744003007154144240e4989210202111408004c0c861080030581101c0070000c52600031104040c07521941840c03508104500821064054 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191983974 1250 191982724 191982737
    0xc03021c050d06050f0d02091b12012c160e0604030b0901110a0215100b03040b011401020a0c05060d09120816090501050a080402060d0f0f050f01150f 66
    0x40415001030441014465140e45036103031180d1426a040c0d8000c0d900c0340d44a000344a0a0310340e1a00d8028103107501a80c11640c2141595801015113001004c108100740c6113030b80440c0c603080b031608001e021410f9440c0300b00000039008140205660751213290003414074041d0b000011800043c0c03403109648a00c0403909222030f0704048000410050381060380141d810f80e030075000348200d40000b849883d14040c0d041800c01d181903400c0c08040e41e111894104140c03000004c01c0080c0c00181981c010f8000b81c40100c402c181c0d030381000d041c0180440d40a0003860440303000e42c6109156580000750f0300009235404204054400c0c907050800007607400008401800c2070300e030800740b0b00148007006e09400c00303070040d00c9103446c0c2d0034281000300b0102030a9028100788039440d40b00703002683c1c02005480d40d0150030324112145036101d2004c14030600030000c03405911810f10340d230f106290001e6001500d1412040078100480e13526001c6d000d02c0e1180078400c800d0004030848058560511031003141920510500300035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191985224 1250 191983974 191983993
    0x3060f0f040f0908070b0f0403080f060102120f0d060f050f090a02160f03020705010206010b0f1b0d17100302090105132a02100c050318010e060f0f0a0c0c030c0302 72
    0x240549401181c04c0700c412000046080c03c01c4103c4410541107001e030703012990740e0300c4c2c035940240803a00c024040000403990a400103590341e100700149401400000c04060700c03400484c60480154001042c500d680b1070030400082448200b16040c3d004646009051283c0381c1c0541c0305000000350098040300c0000d80030403000c00c0c100031002403501807030b2289110050204d95410000c2c1040d400d90842303411900000010001010f0313130020703900100c60021103a5501d0465100345241418860050840b40c0600c038455002180c104c201c00c0681034100e44846119a101152510f004d000b41c000254415001c2c40184041d090040314100040968440061082242c00420100c3c20100064507600703c079284e840d03c5d509034140008012103810b000309003c410344034800a40140001806aa10034004039118504020309410000500c0401001d035801070030070580400d080b1108540300c141d20244500400d501000b1440f40780350050301c0d580c0e84114038120f5902180c4074400c2160030b400710310a0100c60f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191986474 1250 191985224 191985251
    0x1115091903090504050c09090708070e0f0d05070602030c0d030b1c0309080f07090c020307020f130f1104030201020f16090b181e06040c02031b120708040503070b03060f0f04 76
    0x1170301c1c01112107008590b2203d140e14100103c00074000d0201e010081c02c10280110186c0040e41c8040212044801041e072a43c440c0c080741c2a1082c01001412520030800b0000f11b10f41c000c0001c0450007038003400d41c0d1140c29103d00c15401e882c286e01e2550303001074140071f0441e00c20f84626012aa802d20a18020b0400c6507180f101500e030803289030342e58000350012a420419058140f01d240701d9000e0038000f440c241481c40e000a40112522403101d4022010310106c1450030314540c0c0503056883d0400c50421851414036a41080364205010883c058841c1c00d46445400301e00143c41d410031400804a032011a0420710b107580170f050070484081e0814085d00c50300108a8980000c00c3c86010700c1984000c07001c6824405400381000a00b03202e00851030320074080d03a490f60200c201c40f80241c804030030340c000c1c82ca1400014503042542d007840c08a048041000ba0410034414010021030381c0803000c0301c005a07150720200384e03075200c00d448041e0b0001d00085456a281001c7c0203101d04480c0082000540e400003110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191987724 1250 191986474 191986481
    0x905190302090c090a15090501080a0e06040b27010e0d031103011710050a0f0501141806130501081e010203010e2202040f0e012012100807061115091903090504 70
    0x1003000c0403a032280c1c81488a944e0212b11994072596058040c03084401c0500801d49a4002a0001c0c0669032180001540c401c01c18401c114142544030304441e000d0f108038000c0d4007c0c490405030180354000c0c000a040744070310034055554020165201c0604c0c4d81d203445241141858241da074600786018020071003003401064401c0500c103104414000c09c1e9010341e0068001180c0050701f2204a50050011103c41900d9042900c9030500c5c05040c1c1400c983c5a59001403074420410080d000110700300b000101d4a001d02145c49071003144600d90b040300d80c213242200c4034280c0c082400b80d60456a40600080c100015500808000c0610a01c801e00390080d2500032034159000250806109030f00c440c80141c0b456400d210320f4031800309c1099a1005031060031080b80301807040800e403c400301c0800000c50310554540007098020706496088440300c658a00019065454540844400b405108090040b88480c200c0300307480b440703820028154000b0020030f8080041c01f210b03000d13800c01c5030701000450aa1034520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191988974 1250 191987724 191987759
    0x501270f060f020d1b02011707030912020a0308070c021206010b031806010e0408070c0b07030e10080f04140c0411091219020d1109070905190302090c090a 68
    0x100503400480c28108090404648600c1c100210f40c8614000800298000403030311606441503800d0404c031005000481e880171541e0702c0307400384001040034041016007592007012118420f142d250740d504140c00c010390300c0d200400c030060003054050740061240342c89492640c008910041400c0c2d04200e001c0320081c0b6080e42600210301c80c3c8000400d0011141c8044c0304140003905890090400f036041c075840442c3d000000d1310040900320b0206a54003080000307070440c2c01a221200303440b621442c0341d040c010b122545902c0a18091030f020600300d5030a0f0300c1940c5032846100c1ea51400c402503200c90740d40b2103810401e181c09907010301524202d068195034a018128039142d0758021280c54242d0481040301d605000c004052840e0b104600d00c1540d94806803800b60501e404030b9400e24190803600308107443d1164010115403100d080c800b08202c90750480c0c0d24800303a840c00c1d60040070404041c0501c4c403800e9581d0001035442015400040c910001110040c01c0401016100c0d01ca00c0707940300380300c031003407800ca4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191990224 1250 191988974 191988989
    0xa051b0a0b090a03050d0506030106120501050f010f0302030c0f0a09240e01050a03030e01140304030305150a05060f0702120708100b03030310090906090c1502100c0801050127 77
    0x900c100300a01000c0745600d508160008064007030340e0500e0b030740580a0b10611034001ca500d51502d00040540c0d4080d03010000400000f484d002240700140742281c02400103e401c21402c03503900700007240405100303c180d4180d0341e0150090118404850801c41c002d13074401d8100340d100c01e9400c1c0110f10000319001700740540d031103092000c0c00d171001e61220751648180e0740c00c040c5420040b0001040169541c803c0001103d0f05400c150501d010b941c2c004070b80f4011101c0000318541000810320007003603850380c0300034810299a00010321b1845003900700b14044080d0310490740d1040c2d0034051450800d2203d00149000342c4001e02c2c5441c0340c1d0440c00341ea42030a016500a0b400303900b140000d90078580c40c90181000c4103404401440c518034201a06101002c021700900000607610049441008940d07801441e1446c3c1010454092950764501410f80c84601c04c0c0c4417005020707007110403802254038002c0d138680c24001c1e120703011076030301308001183c01d892045101c08207122240000c440400141d000c80002d000d05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191991474 1250 191990224 191990233
    0xe040f0f06060e09060d0506071b08040e04110901050a0b0d0e01061716030c0603050a020c0a120f05030f0408031e0a0507091e21020303120103021021020a051b 70
    0x180d001300802d06070000e02c841d009400180b002d4002503000f21768141e000d1254145803c81888140030b88601416501d00181140300020300402c1c9a036155400f5441540302d0321108100342c07040c030309001c00c00c03500384a6190000c4407410305110684603100600a1449032a4000541c1a0380ba40f1280c01c0d0354440d800161409440c0c1c0c0e12000c80603041c0060800b22000040c100d03c0d451860762a00720f076000f90310400d800c00d41e07940045214218180c0440d4503070b421103001c450504c6118100203038200c1c0b61701a030002081c84100c910b8242d0b8000d006480c4100e6010f0086111503880362502c0350503030b000604a1041103203181420302c1082d100e00c520b07401071750101c80c00a00ba1030250409003810703802d50041c0030340722051104207010400414040c1c0030741c1e0110100030800712440c51081c0044440c200d000307500d03000100da107074035081c01540f295048078003c4981d905940034640d401d0311510322004100f40c02d003003295030100c1e588174181c004121903952403a00d00d20f030611480b15030300041c110724031118841c1c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191992724 1250 191991474 191991497
    0x200d09150b150f0301030201120615080f09160b070c0f0b0c1504020306062806120506041104060813140604030f1d0405060d050d0f08070c030e040f0f0606 68
    0x40075810784484002c404101840e080c112080341c1124001407100904001c00f0240d01d099560181d00980010403041c640783d051255800805000c0075000c45108100e4640c141c0000d41d1041c001401d130075003503240f407038030b00440d0308100b2082103641c04030740251195105200300041c2c0000e40444000204040035507a910750890001081c1483e69031121801e01c803c02d40c0510016235404135916030480411186010b0030600c1e040303103443d000170045001084030245800041c0064100c0c3c3c1214100c60030000401080e0f445800704070454191701034281d5100f03014801401554001d0b049641c10206004000e015054107580b81d41500c41c4e407101c1ba00d00ca42108060104254000d105441c10301c00c5400c000b546c034030b5010130881c0380c03a0028500a01c2580c907040451030a40703825514003241504482922034201881c0405401d224041e114000021500000581c005200e12100031020350300d60b4580039541c0c0807404010182070344e0710804501c02e80c0c031450341c01c1a1800d031180c48000c00140e00c40044460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191993974 1250 191992724 191992729
    0x20307020a112706300106080c0a05010c0501060b0336120304140304142d0409081b030c06070c03020706080606090d030216060507080306120a0602130315200d09150b 73
    0xc800758031075040d55114a2141c061640c2cac010600060b07903c00e10703000c5043c042c6814024007600007a03005524401c8000107000b41802c1a01d4a4580307020080c40c010b6190305403e005010750b514036000080590040c40285c0e01c4000d05500541d040307400b6920400100c0000641f407401e50b4800c3d4040c502d0548000c0020390070342400810385048416a01140d40340802d0ba0203c118118084000d403413181ea80c038001c0c03908000040c000c1d140a24845a4501051410f1b14175255072503004d401c010314144a1600080c201501c9a404422842e0703043c0e01502c00246082000d03034881c0009442c40e64008400e0058041710b40301d0f0201d0051090007580185441d8144034098000c08100c0c3d0021401c1242c100641c00114240404480e00701006880c0000c48040f40700c03469050618000b0003e1000d8000106a06600407020000090301e0042510481383d2803001d40e14000c030303a00207680300c90324145038040507242c0008901500f003240c00c0e0280407400b1060380d9900a2081a01414802c426644007802402070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191995224 1250 191993974 191993981
    0x1509090f0b010e01030e030d050114030c03120a05030a0621030905030c010203070f0206040302090108010504020f1813050705060c060a05100602150a0f020307020a1127063001 77
    0x85014410070031a0541e1980003d14560b00c840c00103040c1601c81c5c8407020004c00400803107000008440c400c010b00c0d43c43d02c0b800d114120449001611070321030303400c0c9000e0514022035203074000054191401d107409840142a0354503000104a00c01a5a40d039900150001e140342c001862030750000207441e050f068510700030345066039640203540130342c1c41001100000c1c3d0300002111409600021582d18030025032000030124031070b9800080d04245000000078014805400841c000c44c4202c6035104014401c2d0180101c10300782100e0300d80740e50108008246003219200511508501170410b449000b510341d002300d0450ba03c20404120b26501c030008001e0001c03110701c00d250300600c00c132411640492501c08029070b00c0c800140b03543c2e241c0703803102d0110311017401c2d07a03000018080f03e007c070030754480c98110400307510b031700c0300d8039040e143c003610a400980c40f460960b0440c100100056004034001e0382403803942e40000e1004050907081a0880e5041d900c0340c0340110064460f004a860560401052030102401d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191996474 1250 191995224 191995241
    0x9010f030605061b012706060b0304020619030e030a0504031b0501090e070527010807080405060c0702030115080d020708120a0503060402090411040f0b0309120a0504150909 76
    0x309481e11006000c43d55039101241e14001d0001a01c084007101e91040e1401840362070980420070259110080035008030340e008401440c0035000c01c001c15a83c0d2641040944002c0b28000d610031010000500e01712204401c229105110b441c000401100c00700000d4a954130040040e00854000705040041120200707800002c0034030008c1001c801e610301000130b061031001d8042c01d619942e0400005007094454000e407405160076003402a08905140d00c0c5141081d035004500c2d00081420000804150140021a0281c1e0717028005040c1c80e980c45d01851101d40060302c040340d1654a40700b070600301e840900465009460000040d00104a103648080e2500d0b019034410308054114818008042c0150010366200105504220b552903845c00c0010307000388141e4840551152400902c4040040054007600c107503150040700b070003407a0301c03550714032854001100d4860059009040613031201c00800d001e4010f8100508107241082d44600c4405000e000381c0210600264002e5410402c40e643c900070800c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191997724 1250 191996474 191996477
    0xb0a06020a32030a2001051005040c030209041109010e18070309170706270c051e03031606050c07050d0804050f011a0a08011104090b0a05060403060209010f 69
    0x1021140e5991074501c9516030056540e90707038061a00e81150b6038a0246400d400c104016290f8800107000c000d043c0c5c403541d80d6111100031000001170700060051240a0040640006007014079140c41c003000301900e030382d01c80714007059000d201d00c2041e03449a009100650500000240d103840c015000146035040389826648101c0c40c100c411028413000180843d0401c4162a0101d01062142081c117078092102c01030040c0c825000802505114065101c200214440340ba240d200c0300000300c22840941d088840a000380100407403c0040e4074240d43d920000d8a4501280c004035401c41d0002030039500071001d854082001c03a0341d0741017002982c0c82203d07231011810071840c0c1404155260140c3e103400800d002014442103d01040a1140400180f522402c0110084c8050b000050b80f000c0c02e107260030b203003d000d41c120300340c040384283c410b01904040c0501c59482c1410a0f00c0c00c800f1201600e1008942034101b1241c01021505480e840010806540503050269840c0e0241000500300c0514244800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191998974 1250 191997724 191997733
    0x40c0f080a0c05040e040308041406011d0a0b060c030a02010f15060f11010c0201090b01051e15070b0c21040302060a02071401090b1b0a020705100309060c030b0a0602 73
    0x1802a04150390a0300310380c0d5044006010001d402c0161034a10883e0845440140f1071000c220415902010140c8113910410400580490980c521a96143c0038007500c2c03046240301d6100d201000064084950000f071010000c2005204000880c6456228100700c0c1116000010f90b02c9500d5024000d619000d24895010051080311221500d24203006015841c20414459041d8458600c03c2001d2000c1c003480c1d0000b08800340c501c10000c0d000340880030b800c0700c002c1044c0c0c1c000103952400304c524101036695004005004c416a00030840540c54601c1e41d0b0040d071105004001c04030300c105144074450307032a8040c0c00b80d5450000a11184071080d104060f82c80980250170080040e501040d03040c2c1141d00d140d400f6848480504c0c202055810f02c44003000d00d5840c00d020b1005001603524418062103110212880b410b0030007440341440e1090400600140e84119810000d83c18601904c03170b0070603860b280009002507941d41e441c0075603042c0000c103000251980140685403610b6140340001700035600051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 192000224 1250 191998974 191998997
    0x5040f0f0f060c0203011d0d0f021c0804080f0d0b0906060711060f0405040216030327030f0512070c030e030d1706030f060406090c150e091807060e040c 67
    0x492844803401004104140c2c000c03c401103450035080641c440c440508050404040b101c41e090f5030b05192041003002402c151601d03260035001061603406c01840c0d1072407107020b1229010a070342d403040c0070b0310464151004000e450312560610340980240d40310100702086094070b0408002d0501000740403d841851304110120008030a00302031b1043d503005070350140d21003007418035045213070280d80e2210342c001d8000a00c2d141720340c00d4002d000409174841e0b03c04010000341181101e040c610261004012400f03850000e82c0468000d01041e40000c42e81c0c9007207454088a0b130798030807580c0800e07500c00001c9490100d141c400c160700a019801500800d8000705001008240001c01c101040b0041180001107034000c50640d44080c01006c0400403a0b000b160070170305091400c2c10060841e03c9003610200360711080481c0d4200364094416450085640304900c2c00740c104100541c00a0240c40d5045c1c00341c0c0030200c4034026000703000040c0140820b441c3c000807441081c0500c016170f0048083e2004001000310710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 192001474 1250 192000224 192000239
    0xe0705030415110414031005091009020609130902100201050c0406050c01020408160905090a0b0c0d150b0901090b030709030305181302041409160c0203011b05040f0f 73
    0x40d60391080d08000d10300408869802400000c001280c1a038000810000700414040080815408030354010f40407980c04d42600c034802030803070300103407100350064000008003000904a60481c00004e8002449a072038a490b00e0005200c3c200c3c60110402c1d0349480d032044a040d0318040801000340f4145000074000b82c0b40c42028414544110f0161009103c0701080000302d28209605481c05020402c0c2121101080601c41e515030340910b2080707a44a50a00000400410001c69074114140c3d02c106190501e0f11961444041c903003045c2c00008100360f0b074224240211109245110050151a1810f60b0364000d440004084011681081c4209081001407100b007541c4901c4100c112034052810341d03121030036045610030b46030700d02c9100740e0701c13030807065804d10000150750080040ba032078144501040c000a1051101000d4201d03045c0300d11440040341080e01138021104a8802c1c0e2000b4000215072019081008a20100003800b800250020074240945240107903140003900a0500d01003095152100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 192002724 1250 192001474 192001477
    0x6091a19090f02130209032e051509040b1b030103020a05010e060f0a0e0f1012020903120c06060a06080108060106050d0e0d03150b1e07030905060705070806010e0705 73
    0x4400d041a541c03090030006019141908401055004001c1c09900e801da580100294119004161081c0074050b81044038066038101070902090b004084601d190710006580e0040000403c4000d8400c40d1802c0d44805503104c1e50701c01d00c42c6106030000000350030a82070246e0b20764800e8801c044179000410061005d41c0d100090712040340e04c240307419a09803548801083c002e028030b5011500118000c150004040e4200400e41048401950383c201d08071400704c1003041129801c0c0c40d550114a04030030032920307801a034004181180c80981115a000c07107074460420a5800343c0c1c8248400c0c1c104030300340a190701c0e2071010341006092600d060213032541481042504c451041c0308082c01d0010019440340b2011a40e00319104a010040c20399010050101000e03019141000480c250303000c40385000324600e0140c0042e1400740d100082240c0000c03da144541c0103a03407008a00f901408014100024195200c3d802800f040e07109002500c166450207011924005040c0c1110782325940c1c5404024841d0781c000b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 192003974 1250 192002724 192002761
    0xe0a05091306090f030f021005191d0f070e010f0602101503020d03020a21020a0311010b030106030c03061104140f01092c0c07172506091a 61
    0x1144003005900e04040140815100280100e807604144d00c00e15801030440c0c0c9a00c040c940941e610042c0041410044443c1110108448540ca001095580c42607134080038040c2c0d000e40156061142c44d40445282409078441501c8503131014400780503e042c0d41c080240109034018185641c00c2c2090030182d22040e0079014004140c0e0391b056a099030740c4048010900941e00603040c42440c0566050007501c450700d45d901940d1081e40f42080ca00e8480301e0010624400b4001d5024101c0e8000940d001ca0390050708d400710a100b50340320000400c2c295800e114090007188a0750001d14014a03524006040e10385004030310600c014180f008014840299404046c03291080380d645c04241d0005006032104009504074240040c1c100703610a0f14409248904035420010b0105103d00d07594030b400d040c1e8644100040142101040c0301080310b0810320002502c004440310700c020741840b108034464020315200600a40c0d14507196040b850038010760100d00c034031007996804d400c00e00345060031034240d056022a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 192005224 1250 192003974 192003991
    0xf090c09030b07090504050103080306030609070305070b0c16090c0207170303010e06060c0109080c160b0906030403050c19150c0c080906070206031e09071203030f0e011401060e0a0509 81
    0x41001543c550320441100e0060a4001c01c02c0040b543c40c0d04082c040c0ba00100c2c1c04a020744030700400300e800840000b0365007086aa1010003494081e0801890102981020300d011107188039001010710490910110000034140f20000000c688924100c002d1800165510860404100c0c1900307034815100402260b0548280d00d0f4282d2440d110a00420000e00c03422003200c00951a01c3d048204204820b4010104510364000b11743c1e20303038150a40002115002c3c440e51480031000c0228030284d007003050281d548103020b400d2071401d000707111040310708003d00c41c90410070414a40c80c0350010042d003048440c909004071182048030900312a0050030384905042c025002e0903001c125001c083e5075900441d465a540604600d8407402c00c482000224041540401408810000020070141c8000f035020200e074951140e0351030b51a6151410380c005c10400140e06509500c0340410ba150050034000d0408550012520b1100c80d8500700009005040180f1114802c01c000307003003044641c2d1421801900140754 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 192006474 1250 192005224 192005243
    0x10c14130620030d05070e040216021201180c060210020a0813080d060902040e06030f0607030509150c0c0105250305100f0b0c1b0603072012040f090c0903 68
    0x420141000300702003940000036444002113005060545801280c024100c5481e10300041c80c0c25810041640145880500f41001040e540030240c81c042d03114590008045000080701100e01c50704040e1452202015101411107107810001c00f80d04008505001c490540c2c2107003041d07000140109041c4011707100c070080110040c0c2d00401c5c1300306502242c021103414502041444d03a5a00b502c8041d4000b841245415280100080c4030f42c100421b1407014511100040d26081d50b074007000358003d21000e00f50704241e00c81d042c071488000c18800f003c180513403290300e841c40d291b0b0540c1150f94251035000b0b00100201481c007941100301d021040700c5070b9101079141008140d56403110310070b80440c001a0b000e10000c100d9400c00040d40035810005019107003060707065504080340100094a00c4003000991a0091400c00c0024180d500c140700c0b0761008100e0010209285100d891036505c2d00000070204100c212000400704107513100104074a0060494100034404540d00c0d0101a0404072a444041c241006c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 192007724 1250 192006474 192006497
    0xc0604031b17070c0e0907090605030105070807080c070602030703050f060406032f040504031e020d0504030602090d0210110f0a1205092215050d0f06020f0c03030405010c141306 78
    0x100c413807409000d0100c001030400540f600750309882c2e1743c0d552403240e5a016864010081164101802072512515154403102c016454010b011550914003c4c4070351840705050040100084660000398000c614030741d00460303141401d43c0d05007404c0c00050801846686840300c00c00000f0207807207c4403400740b12240c216007039100c544070024210750120174466000e454230041004258100c0c0c40d042031075003c4842e0344c0c09141440c906984c1c0d40360085c5e0070004180144810400901b41d50020403100e5006815085001ea076907010803600070513042c499020400700b240c880e41e1040104040800c4240180c000c00b40901340d134460034411003e00b0b810a0030004002107820381d03502c4e10000d045c2000c42001e0601021150300000400520014101c010a9952a00d00180c40c0c03400302d4400c01010780128010300d04c0d040e1665014000c1d0f20083c030440701c00d8811b001c2550004400d00140d80b00d02d01540003c034501e44608802001c03808074038890707a90140d0030311240c0001400c402000d0b040d0340c07070345c148401d0303585 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 192008974 1250 192007724 192007733
    0x50606040f080304030501060f0b03270a060e1204120f0203010b130c08070305091b0a050406080f190b13080d0c120f060b07081803030c0604031b1707 66
    0x3003250000e080e81c400410000070000341c0000104120f0340540700810945888416000491009202d210042c103000c2c80032800d043c6100704840c0d00c0c0540004541d4001d85929445800d014498038252000f540d158800342c3c405c082803189105140c03820700e501e4581814800c4140541c2d1408001034802c2650081e842c00b107403800d40c00310510100c01070082485100c0000a9400782c20301840c4440007684400c00306500c2c5001c0e0240c18010741c1540d000e084800c0c00c0007814400081001c1c0310070b60000d4113500000340c0703031620b00c5002e0181c10240041c000c443d02e15401c040c544004c3d604580a8204510005404031b01022170031604000c1c000901d12030340032642400212402040c0310104101c1c40d01d45200c00030340c1c000e1428014a00c104009128540c24545a0022120700344102100d000341001482c000a510100a00c0030500d0b030454103004019040c04a07107541c120418546042d404041800285500824052081500c003610602025204e075102d0b0788010040b1044c04c14414003049090422 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 192010224 1250 192008974 192008977
    0x6030a030c0c08030309060907050f090f07021e0f0c0f0108040f030201060302100c0605090706080714070c0308070327091e0905160911091c050106090203040308090f06060103050606 80
    0x609483c02182d0722401c003440c803d62030b0b18040c0e65070301d410320620100103a9030030001d0344221400710050a0221580c3c0d0759860303007285000100701104600540712840403007410a45403001c0c810b8000024007040000950a0780340c2000100d40c54070030108406501003d81c0d001c00c0b02ca501c6030340807010040c1c0c1025407901b82d01400c41504000d500501c04100f900000b544060011401c50145400340469143d1841442e205e003100e014480006041c81c000460250140042c0451042800e45507450410f080d2140c7c040203200d600105d40410000903404141580719201c0e000050712103010041030880040e500c0310f54201d521030051001d8842d00440f070400591024800080c00e8600b0900c00f94002d85040740d00c40700929102090108410004030340c0000c1485103504004030404458134040103001040412800c240d0017099070f0809030711040000e84c007070140710010081030201580f82e0825280141880700020701c1c0c01420742c031141d07481518410015682c1d400003c00c5c240003c20780c4030503021900b00d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 192011474 1250 192010224 192010229
    0x30706090321021201090203090606010e03070305070b0c0d1805100c08070c090f0b1c1b0305070e060619030f0b0a03031d0f150c07151809020306030a030c0c 69
    0x4a8540034400c81d02c11400d40c0061844281d207005400c0b10340e07240c045503070881c0000d0f50200741c141c4c0b010001820070b500401c042560030400408840e1f41c15680e030b803103e05d42160b0b600200c030902c0340032842c038803008010404400e420035103041100240d80184800040e000d130324401e05204003035044d00d0031046802801c9010346140c00c19240d036502c1c0c0d0903003803147d060400f0703109a20415181c003000f04600c5140748075031094698001d14140720045c0342d02c44640601c01d0503906440400302090140b22680111100c038000354441c0000d490068074080001ca040c0302e005050a000e50410000b05040c9149410788699030030050400190b4018400001c034020f00c20000415003101c603080c00031040c15000065203031a40d014103c60081a03101c00f0500007804142003a00ea003198210700321222100509002e4208120a8022260520740e0340808852091070340c0040c0c4007094034500c10507490211030900a028021500d0207501d1411304c0c00110380d56801d0010090108500860100204007a82208000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 192012724 1250 192011474 192011507
    0x5120f040909110a050901061403040c050301051014100f030f0b041a0316080a020123071109090111030c0d02040b0a020303071101110d180b0106110f07080307060903 73
    0x2c1e80c400b0b107001040ca008200c44280310702c1145100142915110003694103030380e0548e48541d292082c0d031180b80b40d0742c1c0024008581114206002142ca62024030506109035100c8a10300c804501d00143c0c2275101c00340d000326074020001d00e45155111504400095400d042c10719002034800c4001400758018030300404010b41c0b01d030038071b22400391a801d81e064071201104c081302602c60482d642cad445d40e44008054030449040307801911a04026600a04991018080c00d00b07010179a614807846542c1c0c1ca81c0300340c4080342e406600c05804001d40c100400100d91002c0d414000300140498075114110a0000420b02d80d891140058030016010a82e01a1401401d44840329901d031081440c000e501da40003203c0803030026183d0b9152400240c0140100381d034901d040c046075480c00c2940d024a8015241814036002400c1c219030401c030008070314022240c024882a036038400002c000d41203440c20160800d0181d112039000b10014000c20101008465803164084400600b00a0a280070780d0a018806200c3c1c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 192013974 1250 192012724 192012731
    0x606010507080309012a18031104090201090f0f1403060f012702340b060d140d031b0302070b0c072901050114030f0f0604020d020417061305120f0409 66
    0x548010001038041c06e0121a600c6010030721640280c2560710302c8580c880034054541000d101001c0f0709280d07120b0032220340103140c402e02e066111011f62f0700d0030b400d9900201c5070340c81408041040406501350545004022009840c280c108282d07001b0010906004000d51b143c0e001260003400c031200c80b54034102051600042d9125101095800c1c0045104101c20801c0d921100c001440c00c090b4598040800f44d00460b11940c50701c4e900e081c00400e0394500000c0320100c00c0e41c0d09418001c60100103202c0d6114480d94049205032080c000542c1c26000c5548100a050062000c1d1000440303071318007194000e5810904685641840c00c010a01404208120100342a524046040314006000b4541615002c1c0c03504581c1d400c64415001482c030040300d2003105011001d02081c0c00685200400750813907002000503040c92580c140c41c904983c09544a5000103c8030040800d240a05110050b8004020742440d450101d8944456884034081c9110342d01403000041e0340b01c1042d0100f02642c0c0030302070402040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 192015224 1250 192013974 192014021
    0x509100302210604050c030405030d150302040f050426070609020301020912060708240103050403020c120102090109290703020f0d0509031b100e01050403082802060601050708030901 80
    0xb200507003402e5500398040ca04050005200305101c00440b03000e2907100b4015460500c80c190b0000040146401c002c4140c01d25001c00400750742c490140380780100301c101e80005c0c0c80c1050b190100c403400308040380c1c0104515500307106902c00c0309401a42c9000360003601c00b0031b0007052407001078024400d0700041580600b4221006c01d160000042151180140b911200141e0720341802c1d6209641203d500030000b5044140d0b000550b510940045c0d4200d0310a0041750480b40c105400907401040000326010b40b6940851329050540c0e000208070024003802500941102030084010844420148074400303410002404008240c8200181d0a03440c0105055071000507810100800b03503440a13080611a03c221010074451940150b400700840400901d9000403030130012041e18100c4034030704d0140c14484188000008900c4641c02014020200b2035008011030340140d48180a5109101030b00031940502c2c01c10403266084011a41e80a07088002036850303546e1000400e001d018803080c0c044208030056650f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 192016474 1250 192015224 192015277
    0x71502040302090c0c0601060e1c030e01090512070e04031205071e08090705100311031617010f030f0204110a0e0301051303080a090305220303030605090103030509100302 75
    0x6403041d01e02c00c40d80c1c10720a440fa2851922103008000c0c0648141c1c0188004108160150703114825014002d03020302c0e004d5007030070540490303400301e10310540200741d5040400a280d0b074402818400340000b15054450700c280021050b940312041d0150106d000416800b10717040c90700800126039500307030500d002c0c070040c80c18000051125a4102010450904100501303c44038041c00c0305074461a020001881d0103440c3c4410001c924900a0b001006c1c143c0d03d0700003444c070842c0c0c00000e5100390240340c5090030321109054020702e0041009416411a285c680041c4881c218406010007220340000010750480c0141c000540142a41e800070484284c0008401c0a016007140d110300590204a000b0400ca07a035950760030340581c412282c01000a10000e001039100e202c3d9030300c1042c55074002d01d8980e0130810964011180e4200000c080300591a843c40104105a81802a4406004145e40e0210b00d0751541d6001780981c0554680b0700d104950030744820005901c40c1d07040c0d07404420b44070180401c034080d8584 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 192017724 1250 192016474 192016477
    0x1909090507090902030a12050c0a030e090c03011a2203122a060203041407060203040e0c0a05040302010f1809022a120c0f060a050a05090d0f050906071502 68
    0x20440d0540100e6000060b2034105116a899142e005000f4103c5140c070b0341e42c0c0320039881c44000c1030020700c5400c1c410070f4282d80040100d004081c0c030035101e0100c01510704041110990005118007800c01d402c0005000f08501c070740c4110480c080118106403641c40341c1151a400d01140025400e8518404500005120195803820344c2000d0340d85443c0c88101410f410790343c0c40d00c640316140d0f116040c14400132000848541c01150702601500c000c404841030107800a0801c105980b0960040e4400318044c02901c084000071a0428114120a442c100d5440310107485405507104c0681403086001a0208090182138260340280c01c50030044e01885d102d0031820000e412404506108040391808160308400074003100c090b4030402801000d480010201c10441c81c3d0005100114600501d2800d411307c3d20100304582c0035485c4d0361804903035880d00540c21407c96400070f00c0034407540c0c0300000146005401251061190350245000b42da0340300e449001c10028401c1e04e00080070b1201c04009603030004031660 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 192018974 1250 192017724 192017741
    0xc071205040b0d0f0f0c1e05040b070b091c0c0b040503071a2a0313140f2b200322060801060903151e09030e03010501050307180b1909 59
    0x4c07010170200f00300c40e200b032044410050581c0f0100742d815140055070680340c0b00c03c610780a00742c50250710f080d0302d46290200d10380200000b240d0700c4480d0414800c4d040d03c280040b861300043c81c00380b001c881403165802050038203039031400707001c0b0800c240115051100c00d00443d612103400c0000100c081300407000da60040300048a05103c10121110401c400c001d2000303040004454250354a0708640b00e58940343c010114019040720083c0f03002c4604005000203004444002810300c000c0d00488040b0f64144040d0f100c005c00d061145000c01c06451022500048054030a01c070040062680804a0900c1c518500c0307600759860009809035500031507002e090000c0401d4800641c4e039003909983e240c0099407090920300004000c01080d0580804000f036030741c00280f4130050a00495580c003001d40b04803040740c19001040d00000e8260360b035000d80e420309018060051005070010000c4926152189007444140038540814580310320f50100c0300d603114914541040316800381e010000c0d64a031156401400142d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 192020224 1250 192018974 192019001
    0x9220309030b06060c10181a041106040501020a230a080306030d0201052202031501090504020a06090b16060b12030a12051308030406060e0a0b030106080102030c071205040b0d 77
    0x2600041c08074200141580c1d15003c17800300a014040124503003901512a00a0013403081c90707803141c00008030762900d0020f02e40c003c17a4030b0b842d0b043e8100380c00c000392400e08110340103010f40c2041104000a9a0008100190300c0d0403000210600d454032410101d1070401e00d8561030248501c2007107405020242c0000c3d07000302811000c840b190040041c2c103078280c560444210f101580c24140e40c542e40e540441c080d0600d64401070031760300d24208451a080340454280c1000061a650b8000c110441c01c0540d0110058040e60400003101850148600403910a48010094003a0100c804c2e400b00302c1755401c040c2403450000c05208c0c0c1c0b041207505c040e0b529000740802000140e500d62100144c1030891054601442e0721000c0c14a807203215441d00d544560010340300302c803503903a50a40000c1d10380040d071503d07020302c529071004144058140c2c201420340303a09400010344d070b07441002803000c108010000c55450f01e81c0728040d0040c5841600d820784540c0500c0d0300130785201c1070004035008660300f070358000304000003072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 192021474 1250 192020224 192020243
    0x6090c030b0a0c020c1002070612140a0902030d020109200d02040203010b1210060507020d03050d0e031801020318120a0b0406020d0e0c090117100603080a020717060103020922030903 80
    0x5007006c100c0200c00a11800c005a00841000d100d1144a41400c501c684a40c4c0004a03c0742c46503840d41c2c9580608540010851369522000011403905010800700d910091009001c0107142e500c6a1a104100c2c0c0205981c100541180542c90303220307004c41045154000700110346a41e550350009000307070700001090026000880c0001c00f40306001c9209029240700790394441c2026680ea0a104040c40590707003d400b03102040c090703400e44800c00e008004100715a040a952030702d2080e01c101c2e010701460390b1900c0c19900144440e558003020a4140d20400300100c9061001c84030184055043c41040075000d04920140c0080209100c0d49400910341c42a841c9401c110180aa41c41e09407034490300011298003000d00700040144c8101c0c0c192b019040e80005040e61520103600c49040f0884000d075100702e8280300c0119182c03c00b03a405200840c0100610041540030b03070071043c0c1003a03d4040501000748103914079004100204118001851713045603100415a40f0b2009081c0a0080e410511040700d08041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 192022724 1250 192021474 192021493
    0x6162a12030507020d0c050d030e0103060b0a120f14070c0c0e04120c060e0a21050c0a0f0501060512030c07060f020c1e04020f0a0e0103090c0306090c030b0a0c02 71
    0x403049242400030341c069541c9810500c05a0800c070000c00c5c4010241d8403030003030795000b00b590f60300c0039400c0030030b42d1083e21141c13030110740c030400501603e01c141c1c80600d901c0d4007170080301d075040e0b000741c0345002070b00314003a0003c0c01e040d01e03040c3c403001410b50324030044045604100304585c07a900040181c08060150174444151640c4603081400d0440442e401400000c0b0120100d59890003070091112440c0700c1c00021400300352a403109490001001000d0301c10541d00660898100d60803403403024111107910744180340c01400c4130410340d11160300030001d112519030216441404070030f60003140505401040348900500301d0012076625004006101114010307080d000813064000d04034080c0c00e400c290054850b00d03198400300507543c890300081003e814426205070100c0d40d5548014050401041c0031680c5a081c0f0850040140e5442c50341c082c1414900090720001c10428400c0c5011250b00c10710100e600b900724078280c40c031589164001403400b44540d0a0107002241e0b5003020318110b4103035080712030810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 192023974 1250 192022724 192022739
    0xd14011518111b15160e030a0209040f1104020a090806070c03080c09030307060f0c090807031716050f0606040c05040f060503070c05030d050f0a0203100506162a 71
    0x3440411251070340790b0300700b020348038020400c0442401480380b0343c1950b00c0040914000e03154000c00f11000841c0403510480080034030340144d810100c0110a41c02041840202da020810b604c05c0900080c00706174486018a0400419150003000c030302c00580255180d000c1514040c00c2c2070005d0162011030300407a000103000c5803050342c5002040750143e54022007510b408088024960040c5142501400304209090202c0d07440e01a0b020380d0684078600081000d02842d0003000c1d80f002e40c110b00c006400c02d1038100007040c4050108101021507428140c0c0d0780c01100301c0c0301c000c0024000010010b0050340c0d50752981100100e40f581c81500283d030203022049440d90704803134500c183d02a030149900c0e60300302800324034411006990b2145280c240409205803588500e07141d9000500b07001c2c49a904c0c0e00070031100440e0700100c02e801c600241401d50031828141c0c4428200e694030300807503000e0240481c1d1400011110b120b5a01241c0e000f03044c40000d40c9801603070584072000c1612420900009880000f180b8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 192025224 1250 192023974 192023981
    0x4050a020903071a1608070204050f010b0307080a06031a010e07021f11042102040b010309260d0f1b0905010207290309010c1106060f0d14011518 64
    0x82100801a121440c103241c0540f0700c4520124102044c0507052040368401c0404c0c0d02a0b40925009007900c039110071840c4100429035100804203118a22000d00410510714070310b096030781001d22420042240d5032450092401001590f00180c02e110701c410340318865504805444d4140c611080c0005503079a1007060a070b070340300c2c40003003041440110ac101103000004160301140751040200c0440d4a1b00d640d540c815002844603400501e60030308a5044141140780c680301c1c500800d2021701307003808800b4441c2c680c50108030906210400400700a2402c01c140c0454400b07c0b0a400013400c401c11105207264042d2000b412075440440d224107009040d400168011244072048501c141c1c0201815402c00c1c0a80100c0d0340d07447d1442d542d02c080c1c03040029080c103040010307502c02c0000c0d200004c4c00d01c200b941c0c01041004c00c0c41100036280c000c082401820780391005403165001040e201c082440c081460411034000034011070305020351a040c1c0740c10422000d00da207001120400030241d0100d40e42000c881049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 192026474 1250 192025224 192025237
    0x1050601270506071b0f0308090d03140c0703030215010f260706111029180a0501030213020a1e05120901020d06080303090606040b03030408120904050a02 68
    0x480e03440c1c07890014588004841c0e001070140d824860070101c1d50b59022840c683c20140f01115452000d0701070b40042042d03035a03500300a03e640d42c0010300041c550f483e0b24180c0e01c502c207c0680078524044012007410301903451070b0720000ea42100d00b941c41d514450001d44511040c0800c8005024035425060403108803c0964180c4000a800b0b450403898824949400710000c1841d0314a0041609104038802060100d40300801072503c682d00c00d20f107070f03140e400e081c90065480800d540e4074049603820140c601719131945828044584040c0301c560101d001600c0010300c907070228481100a0200103142c001034100504a9209075440400401c4200008041c0c0c0606060f910006034503c0980300301d15001c1d17800c0040c0c5841400c040d0f00d0b000512082211615041f80c07956080e87d00051040610300c10740c8109002003c007400610308605110358813613214613011300340a10a070703140c1903c0d01031540c09008980060115408441c12020a82040680e41e0064140c00344918a81800240e1144c024021a161f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 192027724 1250 192026474 192026477
    0x1031b1a0a030b030f0706020105071119030807021f020a0e01021515060d020307030506030c0109060905130e060702070815010e061002011e0501031b0602120d0b10030b1201050601 79
    0x280090741004900401d089420749038107108405500140d6642400311002410660b8000700392031070b0203d4068041201c1080c1c01280e81d101c800c400100c06d0700242130102040d407629000c403207a1107045040f4a01155124245da144070304001104600a0540c002c00210300551101c0420429a0005a0300e5011041d000103000520000003075001515801400000000425a41c102000700303041c9000c03a0400c40d0000003103503680c014480140b504012030f40d560142441d2941c403050500000074070040551003600d01500105429040192064102e402030300501c40481c1e41624140d60001c1d642d079070318402e03143d03280200301c003040e4141c105440040c10384258410284458a901d414004208090a2050115542c179a4143c44080301c1c400030742c044035032041001c2100e50550401507201c001900000207501d484034420410a5008125240c401c0070a82810b8ac54a000100800240c0004944640c0c80401c500c8001407264166000c960942d02c10780304416011903001449080f545d003650020b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 192028974 1250 192027724 192027727
    0x102071401060617090106031722080d0302090301060819170405060708180a08010605030c0612010501050d090206040303030c1d06090d0203160e04020108070206010e0a0f02070b01031b1a 82
    0x10004c155042e081e000079410300005540746e0ba94660f11555460b401e8100c0101c01c0010f45c1e010524490003006210030380850310141e20900e4079904955460b100303407036007042c90340114103c1466582076000790000c01c0f05009a440740340c00780c40080d55050b0202c2d412a464404508006035524006054500780e41c03010300301600d0001961034040454011940382402c1220f1556004841c2d107440400300020404500040765090500702018140111601e00500404080c032071070300c0c1e00d094003140074112002800c2c866074a00c1c0302d00301078024100c5100042d403c0100001c3c00400c06506902948500f035003a51500390520f0549014500e121520200d941e00080501882d001d031f24140c0070240e032840c401011503118003140101001c4c6111181d1010034120340004c03c1005658111030280c0e4410154800303852158104610402da82802a0910980341c2d40d50010614540d035990441c4d05040c0c002607604025a52841c000c0c0c686210300c0360700f003076401d801d1078002003000c070002d90b0705c0ba031440001406 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 192030224 1250 192028974 192028997
    0x50601060801081e030d1419020c1b120106060806010f020102120f070309050a060204150c0b0c0a09030b0f01050f0a060804080903070b03090c0a060e092403010c0201020714010606 79
    0xc90244d0300705140b441900080000007103000d400e00c80c1c50014103a60703031580360358640310301c10ba12a04480d42031114a00e0040010000c0703054080b6500310350300e60030305075001c55035408804150b00c00040d2160034101c0d0300c1c182000c5101500301410307911900c400d036150305900d80c62a01c00c901780c0c000d101c2022000848000407801e80f0071078641e40ae511075810320703002608842c0d07501d85070f1811040c0c5806840c010350018050110300714032046182441d8007070600c0c120800e00c0d0b47c3d6075072030f02c0401020f41c50708510100740c4401d05d6108014840c01140c2200d03100c0d00600b04409102070031345081c81600d07c10913400909014500303004108004440c0151078040e525915900c60410580c000e00c0c001d9814003540034081030213903006c8069400745ca160f00c01000d940545506100624141d904048c05000c0d5410b004800b95032008040341c1d10112000007905d28600c0c40c0302904040c2c030089426541542050142400c0513415800360540030b0290001d40380e0a00302083c10350889465001d500001000c01c110f1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 192031474 1250 192030224 192030253
    0x10e0610150c120f3011041508070c0f032f030d0209060904090308180a0c0605090a05280b090105041502070902070b01030210031103070c0501090f06050405060106080108 75
    0x1102c070a80150502a0103444003641d84480305c119003080543c00c41c0c488020078010340851282030000c0702c3c4d22941c94500f0341004003090045031000d410b1020401e01030002981e00e03103c1c00c0400d040540c05000d44c00d40303650311314014000e900c0311101161000b00a02c60a1a01406540c6a0503001251009140340c219280740a0010303510a0072501d81141d410804c03505aa182e44c440c11008600130b41e1140301a0900810917642d090002c00c2d000065444080d07080041140780540608403246800d060f40d03101c0302800890502e4056510040e070040754485040d03514102582000c4811441140214103940ca8a0481600f40102601c1500180b42488144144401401420600a014012200742d15580d000000582e4450501118403602074030041045080c51840c80b2070700c02c4181001d1001c2c12114a6030062800300400c94030401c0441424501449800e5105200075500604807180b13280840c1895000307410b00359001c90301032081e1400005c1c40c5102e440e105041e03461890242004114a050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 192032724 1250 192031474 192031487
    0x20609010c03050910030e060106030221040f060c02010501060e0108100b03060a08120406031d0a06050c120109090c0515040306020f120a14090c0a03060e010e0610150c12 75
    0x508805000d000c1001d81c3c0c983e1765007408000d80c1d00c01c0d5507001c0f405160700342c3e00301d0030808181d1014041c98018003103012121030031050020000d078101a8242aa074550401068002144801a0045207403a607030a00c12a81034003c58142c0b003460707c1d038440b0091250011201680121001070040200450a21116100c9401507030071040040c50003200580320000b15040c12500c1b0080c00300d1072400101000f1080d05405044500b11540040c0800009031601440c0c80e600b600000030142a070740d000042010742403005a801d01c00010203900305c10368481102c90003d000c241c200780e51112003600d00050602d01b4800080c06440360683d802c0c1054550380d548030183d04801d0801740c03540001e010000100c05040711780c510481c6640f002240f0081c6652940c407140402a0098282e50010f40b488042620303040d1155044a40c8528002401404101a980140303c100050346481c040c107004d10a40150f28881d07442030741c408181b5085030034000403003a11800c070030801c003c140320b07540001000d0040c050305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 192033974 1250 192032724 192032747
    0x2d02010b03070f1509080c09060301020418050f0a02131401020a02040504030c170405011d0612100f080d122406110f06070509060a09030b190e010902060901 69
    0x1241401000000a05002d141e400485a0070184081044141c01c1000111202c80c918108000100d0410494517164540c2d9690607004282c5800030072940c3e1030941c104c90017091000000cd41011001202e000a40001d44004e015420303100c010a042c41618402c45000129030544041000d14000b0110701c110503c40040b070544c0500024140943c40f98051f861107144a82e60b038014500380e40c81d1540081201010b51000d50302c0a2009200a980021103100700d9601941000e2666000c40b002aa644c45000c40c801120b9100c407082c072610501c00b1880c00300355800d1803100d104054450740c005603581160704103038000030251402d400d040f1076651320062001e840a050031050030f00801c03c1410308a450751201380020300c21800019815004e01c00e02d070031078030b10388007030561810b001c04024524018081ca09219040010701d080d0300034040d010000c01036520020600b1507107041d50000c043c4071294000582414280992a02c04500c10321030b40000a5000f48002c2c01d0400e00707001150f10f4038850 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 192035224 1250 192033974 192033977
    0x80316030e06072901030210050c100f06031505060d020906040b0d080a0306060903080706150e010b0712170c03060f060d0b04060605120c0a09030819020d2d 69
    0x80c81c0c0325855107a4a004040395801414400c4034140c107095950b404290400c2c3c4600a0b60b5044014401640c0b0300f181c0c0c1d510002145801c94844c020220081d00341040c0110011000c0d25040074406071903220b0b001181101d0083c844914240315002c0020140c07038085840941c0160440d03584001072500d0540c06800c40b20190000900024580106003060051101940d4940d80824068043c2c1c0d1f042c000c0c20003800044c40d1001c101c51550b81c40c010240078450004010549810107503481d5000d400c0898000c0081d10b0782e6802a5235212007003412640801c0b000e0300d0200e0390074509091540035041d03001c03000002a20348e081c179559520b00c0d44c034242c002410842c1c0c0b10020700b084085507030320040500500c1446040008501c1c503800e080108549040d0300c0441400810b0040c0e02c0d01d00c180700c003d1075009125500560f924003000004030781100c15a040144840000b14103200c2092b0554102c4080280c140c0071240702c144070410039250849100ca034100509840c041188010104c41c05508599549 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 192036474 1250 192035224 192035237
    0x3010b030f0c0d0e1b04020408030f0c0a020901150807030608030a0c0201021908030f06041803050309070e280608030a140702090f040b060f180702070b04060914030708031603 77
    0xa2025203055a113922807803081984401030504403010304003000604050101c508614041c1342504407602c9000b40142428408004039845003094001e011500c91540c0c000d1140c0d101d07603101c050441a6080d45c2c1c1c01c440015000383d00083da000e0013032050405541d02000110b04260140c0d004a40307903100e940c022411801242307840c06610300001c3c80010350500c1036196a45a1521508151442500821661045081c09105100d1001a422038519180c26243c039a0f0780e6500c4240c1c69143c04450b6100340383c00c0c0040401c0202c045181801002c8a040c1784114084400910344184140c450718010f8051640040100c3e050341d6004034031919202c8aa0302070b0368100811600001e03104071044640010222494007044200041da1301820341c07000741260f500600d004580d0203d4602ca10b07020300d405458244c01d01180d8007034020441c1030010891300d6021a0b42c0c503200c01000300030030040d100e2440d158402802c60070181c50046201002d860040303000358244004190440302c0b00c041c034041501400740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 192037724 1250 192036474 192036487
    0xf120412020f2814030105010b16080c0a030809010b090106020c1908030a02030a021207030518010e28082113080a0506061c0203060a02221401021203010b030f0c 71
    0x10035040002c000d035042e5441e080c03d46800c0d0007640d5020035500c46482a45054010310070807500000f69034042d010b003040d401640b020392401e070496101b0b040484031203100320040c0b9400c1643c0701e0300c0b50388205003220003881050780007000c0c00141d04081c003440c00035810021850440c0d080c91107104800442c02c200e100650b540e03448229080d0740c80710085034010303080007c0641140d03404102003442e00c9015092186818a1a00e0040c80e1340114824148040030080c1c101c030741c1d40c0c403c0c0740080c0080701c010a8815448a9088640d40611002c22608a24a0409000100c000c804960845280821040250030240081c03148c1c010794072aa06040280001080200305248100441e0070034520550003041da0f801c24408000c000d80030108500040041e60110500588000c40c101e0b0300308501d81400b42e1541c0c0b0b26401007901400981c031341c42010502034400a004090500660003180c030030780030381c1c1e0500718145a21b036161009000304a0202c0040000c00c0203181c0000030316a100c0d402482c114200403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 192038974 1250 192037724 192037759
    0xb070b1504290d0b040f031404080309060703110303070c0b060a060c0f030c0f030504030323090108151201050402040606050c0316080403121101050709140613050a080f120412020f 79
    0x105079000e8a52081c440069407c0541000307040c0d20594030b1500d2a0b082610301144159a8400c00e034010b17010b044081581010140520140d1034079203500c00c20350f51a07182c016001021641c0c2c20100340e42a50424020600c00c0c203058101d00b040d43c26a81d600c41581019440d5030241c585441e000700e040040c0000d05201003044545408030140c0709070344040d82c3c2d03461420000c2c038410945800c1e001ca2000b20441d044008200d034100c83c0700420030b082c5a0042d40e1400a0f10901c241c250000365081800000712140f216419070050b4855031007154100030340c1d41ca400d030444083c01503818800040e88101f001e6200100841a800b0321684035400c00391a041c0c13603075143d11800385410030240210746003860241404000b03004180c1d00180303901d40745200501e030540865040c0844031a40e4000c94001030202001071a18881d40007402000d4581c1e041141e440d50926a1094014400d11160043c0740386080c800c4a0f0400700d800311545075441021141d055000c00008124400301117174042800200144881d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 192040224 1250 192038974 192038993
    0x20f0d0e0304260c0915130b03010e0d140301030209041e0813061d031b0d120f02070603180204020c10090507170313060e06040b070b1504290d 63
    0x103000d080c00000e41c001c200e5441610b005a141100b9202d885d902042041d010894044103501d06000c403003188800000e40c0180c402000c0c80601c041d0554245062203454a0000540022840e00c9966a0303c100342951001101e41c0020302000394050900804200400e50b003014210508040c040e483d2041e100c02e9407180303030030f43c82044034010343d103c00407080101740c0d000320920f400f541164060072600402000040e4568010300041d00c00c0b071100c1b030b007408101d8071340c0c1950a41c0c1c55406000e0094050001401418004040c003c0c10b0040c402c0f444041802d91107809001d00c07001c0700d42414031541c0801c1d0f0811001e50003c6248900700d21034a13040c00f000303008601079007d183c0d00500c050080c250420006d0300d1003020451035903905504c100a22030203c03400c1c04101c4220362036450720304004174014001034101d12403030303129400ca90004500c42c024015581400c03802070700c0d0011140004441c2e0380500040e640c007100c0324901040000f1520b048140c007940030080380d0300010503c6081d08020b50750114171 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 192041474 1250 192040224 192040259
    0xe03100b1906030617011407030c09080604140c031c0c030311030a090209011202091302030c0612010f06030603030503130222090501050601080609011406040b16020a0504020f0d0e0304 81
    0x681c44010402c6845008141c3c1714240e40050024800d5419040480b10681e0015040008041e0361b040346100b810710420740000580303154825529281014207010091501040500446000e198403603106880c00250700c288440300301038600781760402c141060743d2188501005800b4185c451040c0640d0128600086100e83d074030780800201403055006200031180141c008400c203008202c15500907a80b001112907114515003e869910201d5101207414581c105031500e4012001150840d440300c0490b034003505076020444401c00c203d580d28000c80641d086444090301182d02000842c140b020124190402907001416100c1c00d000c01c0852180350840d010701c10708240d40e41780600802c0000a0103550b400000c2407034a010a4100100010007144061141c0007484c00f040d145400c2d81c2c0c580301d0944000304001c3d5140f6072a202c0384c07542c00400c490b128400700d1143d80f00f2040810301b4a018805e4444400d0800c010754201442ca04161005104030702d804489032000f03100008800d40e903007910030759 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 192042724 1250 192041474 192041477
    0x5010b0a08010c14090d110d08030429060a181b0507020f12060f1918150903120b0d050124120b0403050a0e0a030309060f0e03100b1906 60
    0x90b03445146400801d840c640c084c01e030102c07074400c1103400480d903501e00c00d441c2d03425009440d4408880d0741100154500040c408000c0206001008100902c46505843c054941c40800400081d038a22131600b084104211041075001c00c2480051051641c000c41c0f01c81d0b03002181c2000075040c44d1b08000e14032804c01c41d0342c0c0c00e400101c00117420000c600700100e0700038410f0b60507500351005444040c0c4441e100c00d801020303015461400780001700d4200f805c0a070160786e284180707020081e9080349410780307012074400c07581682c0a214943c1d01c06134040c020310440c80711540541d9044c86600c001c081c00b40c040c5c4008040c1c15840000803c41c5000320300207204a00001290900741101320b08101e801c101c00704501e500404500c110714010001150031229915801581460601d41e110b5844406403403900c0c00d9045150480300e071040202c10580c114240c00300341e4400b81c6507c81d0400a0000c201c03007518504a4064040d0003440070f03928070710700981020910f41e5008144515090001110301401c890302c1c2d00280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 192043974 1250 192042724 192042731
    0x10803030a1d03040902030702031e0a080c0702032505130501090b22020904090b0703050103060b040c02070e04050120031504060302030c01080903040503030a031b0908061305010b0a0801 82
    0x3860705092182403203202d240a10744900500d60030010f500e034001d070302c03030010201c0c1c0020005805901c01d008444a169209410b0300441c840642170444070740001843c1d00c0424070303e07804078900d041c8030020f41c2c1000398000d0040c5880c0702416584c217403200c4421406201da0544620100d03140c0e54030b1410114040005100143c2c66143c29400d100351040148000c2c040c83e8554998001c40050f155450f0f031030800c4507009692248401c2c049002410030805c06040d02d01d0460900a41d26455048241200d0290380c09000703010310142003001b2035900484032009070b4400300c82041041d0340100c4081c3d02a01501c0001a2902c42c0c80c400e039084900f00e6080040903500000f002031602c0c19042c0d40218102c10344d0200401400c603800b10b03540d840d0058400e414000341100060400c00c041045401402000d0107903a00d5200301d88020700605003464818011a4141101240b968841e00901007240d012500911060311740d41361918a8214050081e5402e54852001d0021629030720f00c00c1005120610001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 192045224 1250 192043974 192043981
    0xd05030c1e0d0e010c0809060409020c0d02010c05090a09110c0303180715080105010302160c060c150506090105010c060605030a03080618071d03011e15080d1d011701080303 76
    0x1070b820714404690480500c40303030700c4a0074080e0f40d000c080c00004035032090701c9545e80e032014800075482c2d014680c03040804d00d00015001c01c070544081800340b04441d6903002400300ba4a0590190b406000d051105034006401000800150002d90881c00b1040c05d410403a9203014407603191142117034000c9a0a61f1068141048640e140300104201002041d643d02c4a8140144240d8002d00c2c4202c180324550400d60085060070500d9510040403a10a5114082c1c056144d940e24028051108120060760310311441d180c0001e51056500409104150007882c045280c4c5c2041c005640c881c092490690381196180000302d1542c808002503e2914083e0300c546155242460420240b10301c0314000361041042c00b01441089a00086d0303120220410701c00d0245001130380d070b0109005008481e00425280d81c0001c00d2013800c41c5036440105106222040d174252035885007089a0b41c2c07d074564011002541505007a007445000d903900175001901407501c8400086085a890101d20003a04052116000042030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 192046474 1250 192045224 192045283
    0x207020607061d0105070203070f0201210519090b040602070f0f0c030b0a09170c01020c1f060501050c0a110609100314090d081f0f03030c110a0e060d05030c 69
    0x1203d481c4200c010082c04076281c103020094403405010b0005126440c011050001c5a01a00640340742c0c48260703c0408042c6e15882c0008081c20094074290008140c0b00042c051048460240840d42e0b608040c280d001600c503983d81078000e500a24003a1880b160000740c05c0c0000b1004042d0b003480501403c001c80025055042008a015014100c815114905032420001900c104100001d004086000340d40340c040007001140a44034282d81c40f8a50f0043d05402c24503982203908440703284102c00c4c4100003094641c1c2c01990184a202d90242140e070226a4500015050700a1500e800c140900704034140301c0044085201ca04402d10014042521102c0b01d280011245400340c1c1e000803210018400c1549007800500014005804036011000c82401c4d903188030601e0510000074008010404d00c60b80c1d9a0400034208080704804070303040c003a0400d92a031146040c94500f82566603220804000c2e032a43c004000010340c0401e0100c03403900050107018901041800b42926042c840300101d9441d56172080f0f03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 192047724 1250 192046474 192046511
    0xe0a0306021903020403050a060906110c061005010f05120903090418110411070f050304120c090509010b060406030c1e260403020303070804111519110c060904020702060706 76
    0x5280b082520510080011450004000d4080c0340c01010000c0c1c00794807410140c01800c01041e0b40c0d00c06000000b0050b1000b00005070300c40c840e0a004024100c52901e4100460309c00d41014107074000110140a4a85c0422500d203409401601c140f0441c0c0c60b1a543c0c50209d000d0382c014602d540c948040c10303c50034051002c81c29504402a1048504001c0511244004105802002d4001e80740d040a4141102000b00800446000c0c10580c5010300520640d442c002500c1c40060142841190405010564420050184081c201d1008100342c1c2010b051520880080400b001d0103010400001140c50f990b01400c0b030172410001d1950f1ba01c109526000e03188144602c0d0702400d120f620070507402000042035010054a41000962a24204548403410080412030604107801e0703100502c12a81030009500d04010100756440c902410350391951302000b44c440710003104400c0c0c0560000a00b000491400000401c6043c400810041c10031281da008651705421404c01150440d9641d0460303841c00c005000f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 192048974 1250 192047724 192047767
    0x5120a0f030c1b0201050c2e0603030e060304050102070614060406050f15160507060201050f090c10030509030409020f07020405011e03020904020d0b04060b0909070602030f0a0e0a030602 82
    0x80901c407a15518400600d040b08000d290406041000b80d200c0031a03100d03104403120046c0c0102180c2e0482a6840754200202001038a09520340400c011b2348043c00190041c10708881d0035888080b10011a4814440f09900c010002c40f841c0d50700b0050640054800e10901090081e6034551014030324080080c0822124580c11452054071444241c040795602c2601c0180888621100c040c0c80320603805846181d000342d0100100180a0702501040c01d41d0b0540c4614481d4111003041c03c41c40c4ca8001006485e03e8001e2005034021940c0320783c0e100828000e030045608111301d8011649020707a9180580300b2600082c3e1000c4e800140041da0754103502c0c1500950380542007100c11710007200b09151130405034042c20b100090150f511701c0c00003001d540c0c0e2009040709080d0025800042441e0a14200c002084c0c0e1031005417081d541040412a0a0740c0098054247c50680c0c0045140c4281903038501c5583d0004a864000c01209080040041c0c4900d4a240d0042d4031400d405a2148030443d10ba040d40044030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 192050224 1250 192048974 192048977
    0x40c15090308160201110706050703030605120a200d03090806010801050f071107030614061203043f080301091b1209052a090a1503031b05120a0f 64
    0x2100a20100b00540c08a41090060240c440f410165600c01039520441c0105510703103a00801c40300041c0250014002c10f1124403964003006102d441d1390411154280c0c0001d600c0c0c03540e018010030780006000f0454400e06070078600060407e0800300c0002041d1290007141200041d0380403c041000c1d15003002200d01400720500203100d10300d0301403921101207900a008030200644400441d12004050191101841c6c1181c400d102d0300c105484942c0c140c4c84141c401901405038019090307810203012065a06550305440c0c81d08030581000041c0240d098001040000861307010840c0030341c1c1004c5c2d81d400a045100c0c0015607201d6242007030f1001210443d41d89586503054000c82000072503400800c80c0a0380c01894000109443e10b4240149007410b80c084d5044513030010a5001445c041800c0c19584203d8121802d1f602591100c090009039404041074001c5021401c1041c40041d00507514003c101c40100d038021a4a000c580f1040d10704100501c1000c41400b00045140100354889452a003c2016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 192051474 1250 192050224 192050237
    0x61e1409010506030c1306180207020f0301090c050f13061e0f0602030f0d1d0c040b0a0b0d050702030d0212071e021b040b03011103010f0e281103040c15 67
    0x40f000b00c1c0d100ca04844915100d0301d61070302c105022213410351085003d0300000b521404014510308454000354080581a403141c441d0400520507843d0500800460542c00762092070710514240510480c0118900110f50144146002c0180c001c03545c82048010240e0501c03071110f580c2c0d00da9083e66844e0303c941000401000150381072146c0c98002045800c1d035031032034010039512036098003541f000304090840c0d4070000605a05040303400c40c000441d5150608210b07820841040800108a04261180f040403054034051100b0b03861010300381c0c03109901c0f0a00d4015249041c0c0301341c1600d01240c0c0f00406107401c5020751018480860780c4000390303104161038a101040e84040600000e580ca11001000c008200c1c1010014552070312103800040e00280d000c0c0c001d11001c046c0f008204400d810034000c030b030120300c85080001020012101150700400d80c07220343c0c51040241850554030035240044440285803101d6000418480700c0c00114812400b030b401ca400c01d641441c2001e8090701215004608200b0b8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 192052724 1250 192051474 192051481
    0x2151504050c1315050919050d050606040e2803090302031005012303100e0712050f0c0109030c031104020708070f2a06260106020312070914010309061e14090105 71
    0x803c10112006e1a0084078100080580f900381c48004090756000160041071601c0101c0400c0400100540100f1080710180004003081040c1a0f41c7c40365100304403030000790300c002d038507002149811100ca4940a8501001d500c1c0c0c50b5004a481d1041c50310501104650340c10040040d07401000034a045541441910b080d43c21818000a50301c0728401d1840c46203a54400707990303a8803401004030200800900c4007048000540382040c40c4c5405150700c01d84550f00819442810b1588680310400540364440c510f100c0480c03c641b1003c0d51041503802054025a08000ba440400c104c0ca010703100051040c0c4a6001d55070b1076203408000a00c8540025009400308420400002c2900a1480580c0d816103000b203265288144170420001481c01ca80d400c0c0e4040704004034050394040700500a840c4e44e4003902d03078103172a0220125541003040c4145d81c03040310ae4190350401c41d07109802c0001c505010ba0004248550f48012b0514400d4803940685842991022800015214520f40c954010140d6008004a18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 192053974 1250 192052724 192052727
    0x10c030603020a230312090102010b041401030b180a0c03030e0306101a091002010501061b02150a050903100204050102210414150c0d110d02151504050c1315 69
    0x120b40584413441c030150782481c0401500014030030030500020300301da00304024815408041c1c3c0c07081c01d2682c015400d0101000c1a03007401e004c1c0701408a1161042c2d032040e03195449007100d42d03070050803081c1c002c400c4054034060100300b00f15214019024001c0c5819061031484c0103001c001e440d148031400b03600000200148151303201c85e814115401c0c0d03104070003c0f190843c611012845801502c1e13074031240a02005000a505600090581d003032502d900b00004502014141c0543c0d40c940000c1d8401e04480480020603101000391840d10202d04280741088074400009042c60702070729140c40210b9012034200310325a8100100385a1781c4404803107900307000a50200c17a58601c548e02030b511350500c1c8103483c445985c5032100b041c040d16140e150b840e0f80b00e8800e2264980c540ca0a4010440080d111324054928228042800d085400306900104140c040d800c00c0d0410900d4018540c00e0a403030100c1d820304080d281d601071148911200c50800c5c0d52032105c1502c1c0b4140c0032098000c8a8043da00e4103518000d0fa = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 192055224 1250 192053974 192053989
    0x91a2803030f03060302030a0606091d0c1c0b070f02060705090f0d08040e0c030108010606052d0c1203010810060b0f0d0b0402180f040b0a120f050105010e0405010c03060302 76
    0x1a030309071500034810800010b05801400240d0300c025050320850120f00280034480e8844019202c28002c180002014000110f41004046a01510030341100c11485400d00e04810741071000c1000e007803802c0f0005080d464900005004903a0b0130701242030300020788405507041c0200c541c044070a040090a0a03581c1010079036003070203401c0c00b0b0701440c0a000568117000e56441550000c04580358451940c1c41c18044149040c0c0088c411200c2c1c039824481e01041843c0650242c031302084458250095686480417042c6001681e145141d280304003c00c103c480d41101800303007800359103501000c5079507035240000319840e02425041164a5034a440c005205044120003202c4034480c030503010a8548240c41d02e8170004001c0c180745540d0084c070019254101d02c00180c62441208030440320b04084641c25400e000540301010720555108820031000d002c128840c2c04c0ba90700d4240116a0140031135525600c442c00c5440a81120b41c490124501b000100507003401800b0300183d0f10700d000c1c4015803079640031501c0c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 192056474 1250 192055224 192055229
    0x13020105180613081501030b0c0d060306020c0c1206040b040b07120603030905090601090b0f0c0a0c0305071511100c03150e1f150513091a28 62
    0x1003040025100d409404001100003804100800c5541e503210701210111002c52076109102980c01031240da13940700d28030100214100ea82014004505540d400b03100303038082c0c1c8116841a41540c0e2500048045903507403010300700070307a2450001c0248618000400c05c0c2c405900b02540120f501000422002403500030b00aa0410743c41880c012541c3c84603201618540c40030510303015041d10f8608000241a4040100000c4800507940d001c101d03103030000110b50f00d1503907000303400f4415400c2110658848030b4800901034000c040c0c1c06d0310b11489440c0d480c0c210542d5207910a0313030143c1c410141401882040030110544082c2400c200c052850a00f400c07985420300d2158202c0381c1d990707501891b411903000380c01000e10040b0b86c40c1900901c80e1900d1803415409001e80388515044100d22121f0b03c00c0c4a014151340a484070101038403e808d101c0070703089030349600410090007404610000010b900e40980181e07001d090b9002d5007101e0901043c0244540c0000700c54407130030481142001090401000700c07200b4103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 192057724 1250 192056474 192056477
    0x504050118022808150f030d081b03090313080316030e010512090d020706020c1807050c060403020c01080a18031103040b16020a1703040e091e01090204060608130201 73
    0x840d4448401c520300300c284060f00e4002d070303030440ea00891200ca901156441c031031600d020b0b004005613800e00501000a15001c4e00c1505a03211503155642640201c400b01c0c0c0c850f14006121000d00000e0741c10500a8005581c0c0c2c140a6002080d0000041c03900318115014000d03800085040c44000c07031034441c40c01e40d1400e016040c07202c1c40c110459a07905c124202d64640744c00b0b00c400000c9060160348242d580c114640078000500a00501007001c3d4804075601008802c01018a03202e920384c1d03d005503205001510307103414040708000542c1c03a21303802c1c0038892055009401410071541d09400261101e60003c0248070298901188420401c00700c0d03440a4540d605843d00044a00c04013400c0352462040d43c003c100040004109400f1008a60914085183c402e80340450340e2996100b400c3c01042c810003201d038160300240024000c00103144019032340301d4008002c44402c0c40e450011105015401214003c03d41d449080301004d50401e4010b20f4020712031403604e0700c1c580c80e10315100b440503125008002d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 192058974 1250 192057724 192057727
    0x8040e0718031709120c090c030714090f0a0f0603051f061b0b09010c0e0a060e06300a1802010806060c0f010606050403050f010c120e0a0c1806050405011802 69
    0x103120b00f900d4401c1d80d00d07041d40a0032680070350000c40c0301c80d540c600340c034a50070b031246403000c001034542c5014074144c0e401040365446018035952928900d60494009000b00ca41151224100081645c0e0780c5507502c00a00015907029501d90802c0c0c4000c05a4400030081c1c041020800d03041070391600c0554210701241d00518200e4600031500f518240c1d040c0e000355000d072100c0c1105060010844040d40034032a02c00d40c5032038a902c00392111091107586d40c040d2107484041401c40410200604019001304902d1380c3c1c0c0c400c600a0590224862051000c080c02850034200f4803504008104100307100722691a03850311340d01078600089500007040100000e1007a030042a0111341654025070030401c00ca515940c190007800b0682c0c6032800241a60840e00c01030701c091003035025030004100c042c41040c1504406549010041c151550448050495981040424851b01c1841c0000c5040d01d0940000f60840c04558103080244510040130344281e07030401e92040346000c00421082041c020783d20040354440748050f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 192060224 1250 192058974 192059003
    0x15020f1f0e160312020705030f06060d050f030d0f060815041205040317031506040e01060c0c0905090c191d0c040b040b0306011b05060612070b0708040e071803 70
    0x1d41c1400018035103980410704140c408020000444c2100d03807180f500b81d00b251030107036032002010344e60700c9200c0000782c1355000400490071034140f00160840c014042e80c100c4103134800d0402240c7c9194006d0541d45d040c2659000c1e081051345083c011760000b00b03030300001014601e2071300d031152450001c040e000410000071100c0e0301c080301c0d0042d010785004540001c51140e1a08040c00c8050340f5500484544a03040c0c45071409c4021441c1010548060f62803504105005a00303044090700d10220500b020f0741c514000310000503244055004c1c1c58840c0903000b01070140c111404013400302e4071050700883c4080b44440c110a06c01340110b200b150001c005400710101d041c0d2076664585a15200d60780207011903c03000200810518804d0b401140290002c1e80c2d09090401c24082046041303490050041298000d200400c3c01c51a048030340340d100611060580c3d034120303983c20841282e0b070f000315421500040046030030416000789120f0302e54070650a0400d160b641e9400b00001034004040e02000308a000e041d40d54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 192061474 1250 192060224 192060251
    0x2060708150a09020d053106020906160309060203031509040c090c02061e10120201090e011206060f0f06050a090e070e100c200d0c15020f1f 62
    0xc038070100700141c9910b41d095100c81c21807019510002c0c1e61103d550801020480100ea01c800711644848a843e80b9103031003030008034905508284c0c010035942d907602807080c01e810b030340e07500c000b40100d41905103884001d201c145405042e80d03a50f540700302c0541d0011300170001514040203500c1507141c02161680441d607a98035000c407a5444941100f41c1702840d041c200c044040e00020140d000b00a503c0001d01100601000700c62610012603911199003002d0758100000c0d03544034101207410748141414047ca94490325101c0e0545001d9103d22100e20344c2c1030b503200500c01140f0460019007003521301540c1e000e0030210305402000e600d03c104820000d002480c81c12040c4940c0e0071401901c6040005001d6040411006003940101000c4a200f4003096035100a03690040454441c41a4811412503002c041c07003540a01500713800d460140c00c08410709180f00080c0a181d080b1b4090b201c00c0041c14032000210707800030714002004916060a42c1b110300c25079110180008000b00750041e05001007a620100002e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 192062724 1250 192061474 192061501
    0xb0d05030c01022208070603090303020d0f050a0c090f030201050c07032109090905060105010e210d0201060e010f0302060a090801090c051c0c0b0706020405060a050405041107020102060708 83
    0x10054058040818480c50003101900206554021140e41c20b5001440c00b80d10101c440070b5202d0155180c5c0944001c20205000c0c0e089454418000c4c00d00500304040703110790100b07440703401d007070030f05038075074460411044810030f10500e012042580b400914807400c240c46002200082d0001034144800442c140b03004030800c00c200c01c091a4841030020900104180c100303202025002c0345400b0442804010581181c244a81a0180e030031400a005076403030103005488210984201c00c1d08403003240c5c1c9074100400382c1c240a00a5001040081c28085848180203003110055008443e10307074444801007020525010301d00c41035039011610b859513241443c0b41901c920f070440d84074404550800c0c1031102030021030340c00d0b0003ca88007514070038140c003182c284241c184204920020701e00c03030b003814043c0042000d0314084c0114610a0306c0040c81d281e00c840020701560403851501c000140001805d0205042a0090b6118140240251801c0c51035590020352264002804513003005280780015508030071841 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 192063974 1250 192062724 192062749
    0xf02210a09290105010804120809070f060c06060e04020a090c03200c0616050a0315120b0412020102070305090f01020c09070504030b0f101a09040f0606030b10050307030b 75
    0x84280c14002c40074a6a01c1200c03661602d0a03098840c0400000f03080d40075506192080380c1c002618592141124010344684901414091041c07140c5400412413040c000e642038050308040d1950108079486203030000903540542c0142c000340181c0020b003c0141c480c0004031056495a550116041c3c029020440080100404404403a8031060301852401c2405c1c004180340d0706c2d80429200345035100300b08000e482400c83c4d090000100100002e0f18258426840040d000010309000006036036100740d40d022600304505d00303584045919007070004001018a9001000d00540000d40c241130903600c1c050598090540c946000703180603119505960320a200480c60641c00074001061400c00140060098006010403902d52904c0e0002c50f600f206600011441450f948458035662420001e0400908542045c0d90241c0481480252243c1d6914020203480320f480b00070005000d45003000c002c003134070100c4001ca0f001d0307480001030941d0b0a0b4450201d0b0352056043c24089420780ca0380300030588145590 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 192065224 1250 192063974 192063983
    0x80f070314070c030210020604110f041d06010518010303050a0c08120c0d1a09070f0504080a06091106070218090c0301240b0f1e0403120903060f02210a09 68
    0x40c2d0001000300e03400c0c0340000d8034001e407080000b24103034201c16641d800041d60007910700b204081400090f4500302803503041500014101281100031900788510034820100c0c0401c43d030704004011f000780d0402035200042c0038126141800c8a51640e100900548600b802d90340401c0101030f21081400b40c1001103034601500806e051030f59190008400e40c0f2132700128051600c00341403c4d64103e00711440c021281400f00d00510740304a40d11640e0b0159500c16030050703c2c0050000500001901250a12401c6005070185a0124500f18585001c250305828507214a101b0780040c007840f40961104104020510b80c281c4400c0155255603025503c2c141c0b0100c14680e26608003030882c6014202d119680500740c0490302c1c1165101d449440b08007043c041c1940342e03411002c0c01e200c20304034440908c3c042e009414820040d01d2500b5201d4982003502c0440307402c41800b01d00030305800c20800c03400e4400c0f16100456044118104182c58010401110500014016203144500855a512640c1d802500c009510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 192066474 1250 192065224 192065227
    0x1e060807031116030309030905030106050102030d0506030109050d02070509070f1209080409060303110c0402090603150a030c03050d02072301050c0c0a030b0403021908071b0504050a1e09080f070314 87
    0x30f1300e0000c014158140b800c800080b0199030004580c01c050181c0410f0310016005181020818107046000313100c0200000c1c3c0c903648035414500460424010301a000750640d010742110b6040000380240510040c1c460003c12018500708043c86520003618490000b5180000c80d01880b2410424043d001d0381c0c102c240e11b14500b240020405402c01c0540c00c800040364156502d00e4401e0040100b00d009099140b07401450820000301c0d0413200359001e6004d20001040c1000e059101d03100c040701d443ca01e07003040318294070100103104529010071410380100b51084c0304585000c240e800807080c2c0c90f42c1802d81418098049a01d814140d000d1103d50700005018102e000d250f039580c14130104009003075405801500441d00340c030b107030140c10300c100407011500480c22601c0c0500680e100c26560a1251031000c000c0001c80010415940364001c0601035034840c00041003c604407211001c110483c03c2d02c20b52050f1925079003800240c10790043d5000b0500100314640c0f219074a0406071501508450601d200c00e40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 192067724 1250 192066474 192066517
    0xc0304030c0b16020c0d0c0e1f06050307081003050c010f090b0c0309150a09120201050c010e1011040f031103030d0204030b0f0c070b0a0c020c030a0605011e0608070311 74
    0x810b07480c1c24100b08076508445c0045003d40501c502e0400d81c00000c0c4c00210000000d1008055140307006070402010f1030300c1c00d080c0d02e485000011800e0181c000c2000070f0f00c000288882c1980c4880c149030131031a0503065511003480c550320959070310310400f1071138140640600c03030aa01038024105400240000c0500d19600d18074180b04948030386c00b9940091040724003546442d51801d182c400e032013a140d034030703110301c10174904100c044184441c90b88812410400100092514918280a4402121142c0c0c0052500030b100500c00c90644030b042c0000c60880300103000c20092410360703220200c2100e03001102110303d40ca9507030209040d88510f007040c2c40380f240006000030421011380189032040d200014840d50320b4860b00651480f40c440c900e005400e811a12000c590319000942c0840b1104980740110ac3c542013482001c2420030016200540f243c941d5000100000320204170450916152030182d01001800d04e0001f80c0fa0160141c21070703040640c1c0b5050b40300a000c202045401104000728104020354 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 192068974 1250 192067724 192067741
    0xe090c13030b070215010e13140a0c05040605030309150903070314160501081315020417031c0c05031513020711031e030a1b0c060203071106030105090c0304030c0b 72
    0x2202683d20310010b1003102d080030450710154400c14180c812002000c111070311260702c18010348201c40390964003109900d59002c0201810000280c4030b40c881c80e01500105e240c0001c20044039000d90105001c3d810800c0480344a60303845440c01c62800303035500f1030381d00e5003c1000803074601480ea03000108803801c2103083d40742010b0f00003a501d951410030002a0340c0152514011180c4d400d003600c1e240c115003844408080040c5200b404000449074980006003816500c0c04031461000c1c040c00b910304280c100040c0010134001c40c15074212015100c0714140b001140a0000825500c8000c04121600341342c94810441a514001404140c0c40c404006549600042c1086e018480c04241968030030b00c6045185c0071083d02400c0740041440d03030398014508005141c20241c4040c1c00120078001c030113081d844000c00044d200c0c0d0104010b00010f500440c3c03111551314000d0b81c3c4942c8480710502c614401d00c010401170340c030748081c0e130f60141c03083d4201030300c0c1d07119480c05850700b140d88030f802042285040e040003003c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 192070224 1250 192068974 192068993
    0x9040b0a05070905010c03081f120512040b030f0c04091a030d0f1d0a09150f1208030a0207020f042d0204030506011403070b0703020d140a0e090c1303 66
    0x10510550104030075110b6400599042009225541c085030781503115030301280c0600d00c0740394403007680e0241e0307000030507840c2040844000703540028205c07251081e550410300c48100400d01250450840c01c514160408507500c505001c01003240311809007040026030300300720003c181c03402010450702c1803050700100b41c0ca50f003038a01320140361070017803081c041c0358400c0e10310071000b035102600c2a440380e000d00d00e00c0f07001c407403542500d254040d80c0050103900000b031041c6aa114034840c8013000820041042c3c108268810403150581c001c102c414410003007400030440820459405c66605a00160703100128408124104501d2103070a5000303203450307107031440503011449070845a04a406c1d41c0e01101d02400f080f008034096808068420fa000000500a19800003c40c12070300c9402400c076a5000d41e40d1006400640c0010421030068004285030906160814448010000b82e103010a0508040b290000c0c900314580b640240b0034036070340d004680100500c90898903040c1802e202000796544074100310444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 192071474 1250 192070224 192070231
    0xa090614040b0103180312090804030501061502060c090108060f13060302100203070327050303040602011a06070201120b0118030305030414190f0c090e0a03270603090507030209040b 80
    0xc1e41c00d10300300c402c141d0710904c1502014641c2001030b03003101d021510212200c2c2481300807510b000e03507240d9180020843e0f030000780c0001d510130300020814609200c42601207159883c054403e5500c01c0781403100140380300064503036a200030704e4045030715659200001c0036050318015258101d8108050300031500000d400607400d8a000380d40110114162a030308a9492140d100c4c0034001070002a04000c1c0310324a4104a500c2180f21086400704a07111000a81140c0c0150b1010015030340d20226002080d800c5084e541c80e01d08112840382c201201c82d00080c1c010404054956202ea6881c50181000e070701900c420701c846a070f503a0100300341c80e850340380c0502540e000361016a01c2c000000000440403800040d0702e118003512792080d550028140d5100c81681210890448070300f401054042107200051107442c1802c0d000d14014130075500b441c1405440300b0480b40d000c404401c440082c0120429007040325000311819454000380b0700301c06040050400000341c00c02540100040700340300502c141561074600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 192072724 1250 192071474 192071479
    0x90201020f031e07080415050a02070b0f0406032004120b0105040207020d02010c1401020d0b130c051917090303011a0a0e0904080903060405030d0e120d09020a090614 73
    0x5401503074203515a540d0140c51070101d120300d9001c24802c4a0200c1c40050502c5503c0b0380c00da281003944488460302406d000448840000c0d1022601001c000c3d070401142c0010080f02082d6407811000010703c06544c4528040c0030249511140d40c2030340000503481d1941108445070a068545448444440e0a0841100e050b201090b520001280030320300f81c030031983d0090b4001c0002c030383e01102d54019561172100603030a6460a00225120072426002c0c0024000f2a000a40000e1045000020088150740380054642d2072840d000300284160f8020f01140e50601408007403012518a00e10110703001c1004085c034140c40c030f0181043c00304213140040554103075940d040c406d081461000700310107103a0081c510304000041c403108000001e41000809160010f01130320315545040c1c961008241ba2050503501200c9650000864042e040302c0c0748213486910309604050032800300c84640408441c054850700d007445a60750017040b41150380740c5005a0040403040c400303025807940c036510307048041e43c4481c2090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 192073974 1250 192072724 192072733
    0xa0f0804150921020a03061e0e0102030603070e090c060d050601091d150d230c040b01080402120319020a020a06110303040b0408040b07060e071208071212050a09020102 74
    0x80070740c000d080d00000c3c0da03140b41000000d074804102081440314070141c1079800c1160100d012000c652140500703103c104a00c6000166202038000c900100e0780a440415500d0744113100344142c0e0360300880d100f01283d144620741d40f290345a0028003402d20200703a003080d41c030410014582c140d000891300094402d00b0262a2030410a0b41c13003107071410000141d0342400c081c01d607100010700d003414a401421440b0001401d00c2c0042001d039a034005c55134000802c0846000942895000c0901003045940c40ca038070195001d000412482c0c1c0041d210708006003000f403003851502d1102c01f4044013041034441703131203154140c61080940c0e0507010f5103415031000241e0180304100c1d00440c000d8052100c0d107030464110070055107160754a895540418030007030300845850808000000310741d0381a0740a0800300b80550742c00141c0c1c6143c0001d0701e2a29000b50302500b42d040502d2064004507000b04103550903581c0284441084511014007143c00f1040c800ba001801844d01302805001c0c0c17195804200c0c442d01c02e03001c0340c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 192075224 1250 192073974 192074009
    0x209070804080a05030702160b090f04150303080603010e0304060c1e0803070c060f050106030f0b0a03080901050310090c080106020d170a021b03030705071704050f040b030a0f0804 79
    0x211140081100c01600402040100351403d034070403002154800100e00c1507e5016440c8460760100041d21740c0194070700640800d00c160b42c0c0c505601c8050038403004440800c500000150100c0545815110180600071038100240250f1020b400131440c1080a6003900e035102e80b00c01025103180c20060065503210001302c0d034220540c614004014025030001400c2d0b085035903241c0700701c03980104031004450040d12424010b0f00650180600c82c0a84002d4502140207200da01b120001c1b54000c01c1414031030201840100003140766041203400f050001c1c41d009503a562401c030b4200031080b440e0b011401c06850724407411529640840751505903482d60f400c1d03a0100f0010a01251584403921821840034010b8001c82c0d1403901c02d500612040c035121218a000c03022842f191421030f0030456006010602c006644030410080116003220301c0e120003541401d03d4204008510f90501001019015558a00b060026681c0800220039565488404c0301c00e446807034906601c00d0f0f0801e10034440d00c51040ca510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 192076474 1250 192075224 192075227
    0x8060709090207020904120e0916020f0a02060304080306150d020d0f050601020c130f020c0615030a1509060204030503071101110c06030c0a140c030a12051905070306120f020907 78
    0x2241c3c0e046400800390f0f5aa510b0703035103842041f03038400d554200501840059001082d101c5646a622400040c9010000e407034180303202030300b80340c5007000100c0c103038200100000060341e40000340c039049604120455180e40c1e5060210302c2c231845001c031403a4600804203a203150f05e810768008003404400c4d10802c1c08000c0354582c0035001d07600c0548003540507800800040b0b04a0038250f0304c1d01701c0d407040d2802c0456541001460b010403a401061288010b4010004100c070300c42c03120401d075005c0300080d0000c001096681d1120030040b8040c0c40044000c54552001805000140d010390300550380180580ea500c8455141c04429510304419040c0460b00a24410301d403801c000c264441d1040001d0000b0740b031583c400c0300c0c0e050580c0c801e000c0741c0144900071022520000202c4082c0c400200850010369640c03601c00c0340a04440b203582992150030307082104105505070b40e0440b59290000d440000b050741d4079070700410b5000d41241d40000611841c0380c0741d000140a514a04041058025070305a4023580300c0040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 192077724 1250 192076474 192076477
    0xf0c0402091309081314270112030917060703050a05060a17010f050709080f01020f0405010318050105271207021c0206030a020d0507090302130903031401080607090902 74
    0x48a582c0444031003000711941c0c03100e800041c1030ba84252207243c0780c10003a500400f4039086a800c8101c8441003456a075039039080030320070b4603074100840b5031030980c02500126405803180140910344984120400110416018bc0300c602d020381045500c4095888104e0b61b034980c0d0795030484081001a081001003018441603104280c000c0300094447c9840c07904200c5100002d160090300100251350364440040796030032510035940561611740c0d502d80018945400185000b0308800f460020b070344100104403204001c40112012140d0070b08010a00c2c5000300030610000301d41c82000341440d401c2504004c0360052003c0c0b00b0126000030710000605143c0409810360382d03508641c0c0761124a04c104014805446c046010400d6115a0020184031402590110398240c00654480607030303d03004a00e00308070100038060903600507a02d01d4031090052654000400e0484107074038650045d650344403006e01f45882504683d030a01e5081d11100c509580d61a081650380c64203d51810004501e00008580381c1c1e1a0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 192078974 1250 192077724 192077737
    0x20307030f2a1812060e0d0926010e01060603020a11160311060f0a03050601090503010e070e19091208060a0b0f030c190f0f09080a0b0601050702060c0f0c0402 70
    0x1c0d880381d00c650490b2000d4075100d129102c4201c02d050003010005130581c071002c28801c600d04c1403102284024113a03280380d25164000d2480f40030300401103014400d00c803d02100c40f0100c45480c03000520104404071882c014151420014410b50805001040c1c05800d0340003424620110f03a02c001303044071601e00c0c50761580f9000e030350101c900d401c000c42000456500002042c460b007000300b50503c0c050022503400308940c441c40104001c607845104102956820400c001c005000c00c0c2c00038000c17004820511500c80301c140c000d40494280c031401040c2d40b80091030508400b91141d030420046040b16081190808908041c550005010140005c6031814940d458604a400e0705900c3c174101610030b0410301c400c1c1c1004080003078210092040c910a01500102c240d48030b500b50300c3d44c512003140104018490120404100240803c141007003181000002c0c0f030310200b07604100b000d030b1151100303401200c15110b07205000e90f10010208081c0300b042408590401d0030b104510407140113041c80f1050009a00611 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 192080224 1250 192078974 192079031
    0x60903010905250f1a04081023060105120403030b0406080c0405090304050105030a0c1b030806040b0a080d05030a060314060702010612080f0a02010b0a1415030f0412020a06020307030f 81
    0x80d0301044030179620351544104210f4104078074103064440002e1443d0400250106041580780c5010600c0b411541001c0070700a9646802135010303141120000e0400c0c414880d62012603a019800141030601c030b6880000c441200920a200b0b46079100002d40d90b441c050500d651140d07242c280412414000001203404840060311820304503643c418000004004048001d401e01c985800d05801009258011804a52094541c0c8a5504190b428402150040c0d404180100030f05201845000c0d8006010130307100841d460301030356076560ba44004c0c2c050001355100500c00002c2600c4801038a00c0420b02510a20700366008000803680c62110f0003007080c0b604000b41401c1400c01213241c01c40503d030b00400d4444414000480e11150450200f291041c00b548042914643c00040e41403c1c42c00134480101c0c10f070500c08803810343c00c0002104605010160008220900c1040c1c07015409000780003010013590011000c41d03c07480c000101070301030483d5111844603d0303d0400c06200481714106000e24043c0310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 192081474 1250 192080224 192080249
    0x318010e03030f010e04080d060f030302161a07050106090e0a0302060a05040b010b180909010204080d141b121809070c030f03020a0c0c1203020c09190203040206090301090525 77
    0x2445c40c01c3c000e401003c0c0c0f0588501108200d04540321501c1c0c011781e8001c2000303002042e00070f460f40c10300908140e48204c61720080c0e03400b04030410071680014080042c4001f6044115640d041d507207411401003109030701542c1c010b42030804a07600510041110705425004c1e03020b440700341e5117025500f0121002110010030403010200180480c00c288005021000c01c103058081d41003202c0400140500b030201c40c010780c640c0d0001414480000203001c541c0300300980e41444100704000007882d422900440000424401040042c100e010104101c0c0c110740a80459603039a0320f40788407544200c4650360001c40b900400700d14002c2896248102d4944c0030980d01030351030840764403001d81c00314041e40c0040150800c1042a240103030100e0340d00b0310720030700900b1417102800d920307101d603c0c01034140082c1d4945544141002c00400044108510848000504401005940b995184001529405042003285e055841d00070600100f010001c0d008103041010950300c26401c000a002980c1d012442c042c04064801 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 192082724 1250 192081474 192081479
    0x140a020601120c03021804031413030f03091503050916050f040507021c030e010c030209100806010c08120708060405091018020414250c031808030318010e03030f01 72
    0xe4560b03079080014881d6084404075607494000460200c60f40401540504800702071004040d0000641ca106442415186040c002c62020007000b0071440e101c05050741241b0740c6d101041520440d40724001d80600c4105040c1c1c24200314000300105002c075107005403407041401c2c2c3c0d06188000c00310300b000c54000601c4500f246d0480000d10010f8240034107000c040d4861035441080e204d52584021050420564000a503601c00c1e030344203070035207030000d10100505104129400316500c2d40c060020310321989081c5580c01c2d492705401283c100c000300d00060030038400801c2c107820700d4900c03041f214001d22442c5d82d8021140c50b00c00800003290401d4625030025440b4030240030080f0000e17007006080c0c44080702140f11030222130f0080b0f01560500700c2003401130440c60080000c044103104d8429030304848900c28910302d02d0b03088005080e9548008000d024009030780081c010a81211006c5070140c240750301a680c1b01d062240903800d100140500300d600075420b00d1400c5400303000000c151703071164088140d412000c2e413 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 192083974 1250 192082724 192082739
    0x7140312070609050a0503030c0904050a09020a0b0c15010f0801050a1103012c0705030708070207030b04060f090f03030f110f040501081e010807030c060507050c060a030906050109060303140a020601 87
    0x90300d443c2c111414001d50368140080350060000d14420700c0916480c1d9510039594040100703c0d800105800119483c240388800541ca07054076440035550840d00b01c0c2e546140e00700c8500d02d00401c841d010600014118004540041d19108113400c40e90b000009100d04e841c0c0d10381007015207214013000003110505200410160f803481480300c214481e10f200d25440e409030700c1034007680384c0c10884810780403600000a100040303070b00201559205c1d480c4e01c0a001c040e421580d8a040918020b08041c0015407079461000350245640d02589003d0751040b40c25170b0a62003881e015011302041403810f4096890100034520250b1340724200d8200042e1515070078a4241818015a8101c40107003000445c0e18245511001c4004081400390103403080070000d214042c5140740100c0380b003000b9042101040420b000b5000010740003d86d400b140c00342122110388034644107400304c0050a030140040c2446040400014020542d030380102e0030b0380c0c061b903240448040781c10003101e030b2031013036842d40c0c00103170f00203030040242e017 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 192085224 1250 192083974 192083981
    0x90a181101030b1306050a21030507060b1f09080c0f0405091218040c1103090409141b040506060901080103110a090501060806010f030b01090302060f0c03040602071403120706 77
    0x1520141400035003d03d6040229510190803c0d07181c0125a503502d0a100601c2c244990350024130400920001e941040a100c21820701d2640c002010300001062a004100054000c140741040c050f1400c03100840b414941c001c0c03500185015400b0403000400401c1c010f1300414258a0624068460b0701103000020510000704002009c0e070001e40210310305403035048a004003c243c1e81e0202c1c0c0e65900030800c10820001180e4030541d10360240901e51400014254020080e01c0c0003c0c0c080700c00040b0b8001500b0004035900d422201440280203d03121400707a0141d4200f16000007000307403810032050740d8090a101d450310a40da03049007c40c1e215401040051000c00c03801100384005003801a4540c1d0b00c11031002a00c42c01c1e001140880d80174420014070b964481c03403a044401d00307442c050241c043d81c540040e080c8009400064010200007400900c480e00302c1e000c40d4041c40c048404c980d80c0e00d6566000945610490256202c038296880306100300d4a03002030060840a00c58140d07600e4130784181d5440c0000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 192086330 1106 192085224 192085253
    0x70606140a1202030f0607030207050705091e07050d02070311010f050408030c0c0111040323060f010b0705010b0915010306050303120c0a0527090a18 66
    0x2907403040000c00444409504900e00580140007003820014100b01036a1144101004e20209a40c5a0300a0030000e000c0e205842d01c1c0c5071644100560603034152118140d04940790f036190a051a0404046e8200540d810005d14000d18521480c050340c20141381640440e04074880c00110320002e01901d0b4000e0b142c40c0003008585083d41c1c8410080c000501400c0e240c0c8404189001905c50075401403c400f010b448115072900e41e6864200c000c1d034000710424222318016110310010000000b07140b401164004240c0c44643c1c00c20501c0700d481e07003002c00700742c820f5925203001000a0701c03000310181c010112440e14013000c850110014042e0f640d10fa000e6030180d4405c110311138124911980c02504618441102603640c008014126410300038804038048071046808244407100c01d0600301c41030000251101c42403591403881100440d0200418050340ca003500f510040040c2a020130303c2032 = true := by decide +kernel

theorem cover : BRFrame.Cov 191906474 192086330 := by
  have h0 := BRFrame.cov_init 191906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191906474 ≤ n) (h2 : n < 192086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
