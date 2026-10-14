-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2277
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:13:35.840351+00:00
-- url     : https://prove2.me/submissions/eb1317a3-3051-4f53-b544-6bb7258fd58b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 409352517 ≤ n < 409532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 409353767 1250 409352517 409352521
    0x5071707290403030c0f14060603070504110d051009020f07120c0305090607051c020f060606030402010f0f1206090204030308060d080f0f0c0d020f060a06030b0a0921090f1706 77
    0x42d1291403d51001c0b4070646802c4c042201c036440c2c8041c07851180185e60040d40c042c1040040c9d9007001e00441006050690b000e100c007446102040090703000300e2045002959441c000280125000303d8131030000c2c5800c5030210360700c99581480d00d449070b10458040c1c0da007240c00b00d1440b5815100c3c2c12801109905551014203100c8203004015040d8410601660b9910404184031034003c0c007050040d1036404140c00078a50385801b03015050411600400d442d100d454107008000141c0d800c01c50008040440d4a454458048140070039142c4400d10461180700e649402008034403174241c0d40c0100140c0b4020344800c41503644000400c0301e00148400024480c3d401440b60480e282c0c1d02c1d030090019004210135080c00c0070108000b007407502610300b084500590042e0300c004645d520a00209400c081100030600880307045484500001c180a00000451a50f420222052040d03810700c69950003c054255420610100c1008050041c0d0340034108010a001c60300241816807a030900443c1030341000500259 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 409355017 1250 409353767 409353773
    0x30b0619120f02040e010606051305040e100c18080d1e0e01110a0b0a0609051f05150c0d41091f0203030115080402091305071707290403 60
    0x5940c1c00c003400c036003154884401001c0c0321400c0c0207d4010303120f0ba50701c4a03190f100d03c41c03410f1100c0b182c50f88410301580c038003101c1003849100030030b480c0450380301950081040107100b5000c80300040b460300f5248500071140c001249440d03010411803d100d1065440c05048100710700014a141c4440d056400440c081e440003d540d940940441540240d91030103650054002e5100d41c1603403802154144a20703641c80c401440040094803d07560031025601744908403221856030289124420300805100301042406825000e5080e021551045400d4094901c1d010400c440038120107160742004407411940c400205041c60100c0f01c103041c541d1841d00d5144640c0c0d1100d021400365003c0fa1900e5004084c40d102540004001c50841c507241c681580107580d40d40c90310581e840d045c0030480102d01004000c00501000d039440c2944242c20007418010016100c04a01e00603152120550009120000300c0c8a03421f4107110202d08041182e80d441d101070b0340402102d41c1c244000d40356022062500348144828804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 409356267 1250 409355017 409355033
    0x1060c02010c14030d0b030f0304030b01091e180c080d090308090a030203030406021b0d0c0302090a0b0a12050709090507231302071e0b070f0c0c030b061912 69
    0x6030501444201c8003030942e0b04002c80c11544821190b00f042622186d000041c0e040400000c0340c0030082c2c0024600f0203041d59148100f0f6441031061032111038586104600c180d003064150300c003900400e58104007042240113501d0464021410548403001a81c1001407911070105045903c59980e980702d0340400d05680c2c42d0f1032560015200d19801030780080d404401031b201080280090406500103084500717151101e03c0a4408030080f00e40103030300003a0444c00107a08414000d0a0f60380c115442c0406d030350380101d400000c00c0c0035149954440000c01d0000750402c60680c00010160107107059a00280d1211070b00000d440500c1402041a4013212003007006601116603880c0720303080a000c9206083d007410028880202d03c100440c1c0b444c0d800100b490800a2962048010b1944480c100d9402042070720382500e8031000030308010901665030040580c103441031f209041302c103078040d503a031820b9900c03403c201c2e00c0c1c1c039411214030b030003a03406a180706007440042d42100112400464115910200c540e58001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 409357517 1250 409356267 409356287
    0x1060f120c0c06051018091403040b0318010903090e150d080315030123060d0b0c04060f020c0306011a0903070b0306010e06192f0c0a05010f0c020f2b0303050f01060c0201 75
    0x5510100d501c3d001505d48c00c01d10082c4020590a60f03035940341d080c01340c2244844a07a400c8007415aa261158100020780c00003003100450303100d031072041296900c004c0502460150101d11641c8404006035040405c2030300800b45004201d200107046640202109040c2203812000c036178424441d0a06008000c0042400c2840d488440513044a086500310b58481d1142c0e02c0580e0680d0b10000c010405001080d0300100101c00c07801240300802d110458180801c0d04d03004e06000c0c103d0442450012580382d40d84c0d80303040f42d0030024050308540c080c41d075a4140210710b800c160344060000b51140c030743c05401d140c41c00070307240b030b0607445440480c001c40341c81e000380c48082e80050f080c1906142c6c4200040b0102108019294460010000c1c0084580c3c10040100024181d0411810300010718140300c036940d4171120b042c0c140c590503100d100050707480c000050062041c0c41c421244c07154040303200328000c40491030b207242154070a880c06c0c040da4980d010418007041d0240641c0c00090003850040c4050742c4a0b40d240b031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 409358767 1250 409357517 409357523
    0xb13030e060a0801060201051e15040605030a0c0f0501090312210504050f0f0601150813020d1a06060f09010f03090605010b0406120605010801060f120c0c0605101809 73
    0xc003040e030494000c542a50044510a004945100010082d8540a00407542c2c4440e50710034a40c01c1c480401c84134000e00102620700801c068600c0300e104000e803107036480724001d000010102e4100700460310706000004d90600a1901c04546510b0002e11035004e40700c01e1090343c1c1d1003198440000e42842d000c1310410f403821001c2924a61411868000604030310419000e14081e07000340481c02c90340030a40e032034410340b2580009281d1200b401044500868020880a00b441d490480005e40700c8180c070b118041c2c0c00c1a4080c3d482900105090b041103030051808020030311341c0400840d03654802041000c2401202a0040c0d010b42c01c05c841c1d10a0f61294101c1c1000c03120340d040001d0035031000d4468404845090300248040c0b90000b0702804510f400440300c0014040c8220244280c504000000b0003000c1c041c8100024004030b4424900d40d54001d00c007c002015114070200010522102d0050070340000d400142c1d0514a0080451a06041d507442d40c81500d903800b0041c1c1d1005409000c060081c01001416 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 409360017 1250 409358767 409358777
    0x1050f181c0b0916050d0305070501051806010902040e190e060901020912010204050a06080601050f03090a020406050405101e21060c020a050d0f030608030307020a0506130b1303 78
    0x14035400d035240304500312500300039807a030030448031a807501e014001d0300a030060015501c000803080e40c10014003d51829103100342d6403800108110b20302510140a801300c0280f2a509110030441c0c0c1686000107418031450302000c1700c0040e40e0300c0d0040000c030300c00d0340075044a40c100f81c000140754068183e07585580403040c103400642a00d0141c0c045007040c10030764110640365000140110f0900d001c0c041040407485040003103203070925110005021040ea40300329403d0180314400541c00ba0f004005582d1403949a100321a0341e4500203807a903883d118901c008034031852410701c0c042820305007031140c14400c02c40042517811282c14500f02114003171044000030301140050b9004228103800125241030000061030080c42940b0a01d042e1043c3c498280c0304004640c05561480045140021144541c1381c0c03074101080320700c0d00076008074080c2a45410129071840000148500c042c2d0001c0d0400384c0a02450554040340c440d410340310030300d840000300542080c607003802041607902001e1a46080718481e01704 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 409361267 1250 409360017 409360057
    0x908070b0f0c0d020f010c0509030a060504110904060501211208180102040b03060f060f190509040509061803030702031c0b0d2603060105070b060a0f15110102070201050f 75
    0x200c1883c041981408000580040310100c04045090140341a000182d050550802a8542c04259030b040307e11806404103072110701003428010b00b5100900c00031000b400c96191442c0c00c1c20034202800c02131003030303508003036003801d0850942500800d0640000e91110351480d0900019400b11501c0703c001d82030045c80700c0007903007004503080e0920080c802407031020041c0c1d03200d281483c108040c01c0c0248042c6c40c0036860070000b12007909818000c03103060700312049502c04050b2004a04580314040d0311480343c1c219281c101481003600e000100c05200b4000800342c141e590b014100340e03035140e010035030702d15015038000e1101c1d400144800404207194210303c800007814051a200095101e42d07100703415100b4241c59014081d00c882e0241c91404415203644001d403450a101000070102c2c440c1000c0500040d2041e4081540f0703603108000f02c1c00a18000110142150b02d420b0040c480011280c441804604200300f501000f0b5010700a40341d49035016114142051022540c450282e800811002040440782e15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 409362517 1250 409361267 409361287
    0x1c0504170f030a180b130e0c07061a0405060406030b0105010e1f081006140306062203140c0102010e060604020c071205070302010305011202090a02090402070614160908070b0f 77
    0x1c0070f0141c822195840c4004035041d41d5103100d0b01c40380c0380c20007060110208200000c0382001d051950803181d9401c6c02c500b2075a01e105d200a141c0c022082e00038003c40c1484e2200440c3e48021000c070020b502d0445d410000764a0701001c06c011a0401c0c40000c02141c1c601c0010002507014040c21001150042c22403406102d1182c400003035040311821210200c3d0703004042c4039911502c00d00c0b00d80a2b28450500d14915903580c0d403c03003041d002c0200080e02c140070000d0b000c1400070760b40341c0601c654540c0341f080c0c20b01c40f03459150441c2c8086281340b1400311440f8030207440c042c07503105000340c00c810000580070300b00f65160f1509000280d402000c20101c00c0c4144030300003540c8040030758505074050143d40500310a500714400103081d03c0341a8490070342a102c10340c1c0c41c005641c03100c12064020610010040c0e640c4941001308020780610032014114914290a02d490185100030941c460181c00000341c5042880e91000da42c90031181c0104049a03101c00c1062000c4110040202f205c072000d41d08540c10300000706 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 409363767 1250 409362517 409362523
    0x10503090109020409260a3f0f0f11030f0628050a0b120604090c1503090512030c0a0806031c020a11030c030c0402070609060513051c0504170f 63
    0x403004803140e04818003031b071590803800d48609120041c040c443c64902082d54400900051419102c01a1965040700d00440407042d200d04101c2c40c0c140550080c280d1202e00c40250082086444161096003460303100c49540000d88612102061452065801c0d0341740c0022890f502e81008080e10780208140c0300003c5e018013180c0880030040b0342186502c01c410b080c81b0900034601145c0d0b0103040301c04003e00c4071010400e454154940d001c00150b034002960000b03810806102c41d0541c0c003008800048010701190f0701d0303040d00080c1134036001e141201c62401540c1c2d1406001d11044510401703c000601c00041254400c5041c140c11840c002d08864245111142625680240b0f50b02180503a0044940b002000f480030784840780c010080f005041c0820301c00300800d484270754461102c0e01c120b90000d00c070410409a54801c1180981180e0100880e140407101d00c07600c1031040d45c081c4c03980c0c4070b120380480d045091401406074800d85030b030301c43c0d0906141420810030b25015103034141150007940070f481d241040070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 409365017 1250 409363767 409363781
    0x40305070e01080c0a0f06050c070905010803130506030402090c130b032701050702120d140a0b0909010207020109031223030601030b01020a021f0c0507080303061c020d020105030901090204 83
    0x31800d007440e030754505480d691411039030248980c06440c020f003081001030204000038003111136078100965940c05107002c0030309000705908003d04035403401e00081101d20f8000003511401c005404460b40803a181c0c0d003000076a010803207000b5804528100050124801c2102500e00c00040e140c0e000700c03207525180d42c038003250011a100b40310710b0122920413803e8a80490022108030300c02008001e9420b000700025240c0500401411407980c0016002c0f41d6461650b0040d418500c40701c84074003050405e40741d003e020340740241002d4440e62100001ca5000041071085501242c1c0c140c4412401514547c0c9012610342c490440806002d284c80c61a800c51040c16000360040d454005120b649281082c000340c101c5104005a6045500259800005807030b0780c1c01460309800050840500c0e10501c40f4122581d82c41044010b049008600c800200c510000024502a00c1d0803901d075030380c00101e003140681c1c0000c0c00038081c3d44030380c80076940c3c1c0255004800850f0450711010011406441c550003290650b900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 409366267 1250 409365017 409365029
    0x150c05070602191716180e01031406070503012102012601030c0b210a0b0310020d05010504091110021e070305011107020901300302060a050601091d06040204030507 72
    0x10300c2c80b65510040d84002c80700c44e80398038800d509100d4240b9001c09501c0f892207041d558140485102c0b0050241640c0c50380308010b03e848003d1105a44e182d24000b1243c4000318003a10b503a02c14400400d01a03070240003603074144c5000300821101c52200c2c1c00b10300c003080305c068001e0313041c060300c580d42c000c0c00d50481401c40d851480c5001e400100b0352642c076050001c100300e0342c42031044c0c50061111450060340f05004030015080344040300b815440d00c00c1c40000a15403120303595498401c0d819418803640007600034000030303250351004200a0782c0c0c0d0405c0c80103851101d440180b144420159142a516146540d10b6844046104840c0b00c0d40105040110001c010190440103a00c11201003007048024019842d030018403d03c0c9505141090340812021700c0107020300c140a4880700c045041840018140d400510394240c0c2641104070705050107907d0341010398100030860308000c0050210350190244001704c90024985014940c06805041802100076110725407280c1c00300b0000012503000c111104c050b00c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 409367517 1250 409366267 409366297
    0x306050112030905040209060a12021308150604050402010e01050c011d030d06090b06070210120c0804030e15030a180c0f0e100b04060815211504150c05070602 70
    0x140e608002d0f00381651075112910030b5004000000c1c094442105488165507181001c4003c5d4030740c1c1a0003c007900820031a202c191905000000b6545000180d0800c90404c020340407403191580000d2000f901d0f001ca1740680821905510301500e075204c0c60050018148aa000140308040c44200c85800b1500c60b014004030fa00100300710308044981e1240f81c1c01412806820000255200046000781c003880c180a0f05c12400c43c1090f98500d0b01940c0404c004a6040c00200098901c0b5240907041d14015141600081d04802c140b07189805d045200c0d91151030f803020072605650704c0d940803002424011081c1a0101940070308200018103150020001c3d10f600e00e088200d0314200f20304018000c43c0100b0084002c05400010003400140e44216800e48001c1c0c50204225600c101c40a54980c001c01c1925401010f54882c03808041c1c101c400c9000d10300b4403081910301f00d09003082e9250602e9000d842c00b8080f400004c1705816a89600d51000c0365400b01c03418002d08201031925020f040780c015030307195a003050b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 409368767 1250 409367517 409367549
    0x803060303071a31030e011103030c0301150804170d060302030a0c03060c050307050a080a02040b0309011401120b1303090f0803090a38091203070510050103240603060501 75
    0x50810304c9030728202552501008614421064104003640a680d0140c103100d89140000d0b080e911030800160003000b10130071282e132420100000085070b0300911541c0c84858146410017540b900c5000c140e0301403600a104030f07441282a68400e8495441010700440c80703540c07403030000b006072410b00c40f1100650140c41c2560009185090a4003074400d038225040030007400300b0400c88440c0d00303c401d64010003040d180c1845243e5415016000901c540e03003103603030441c0c404400c06c000380702c054018400c0d84500020070a500d990340c80100b0747c01c20116500038040504040003070b129490074400122140e00074074200040c0d60382d40195608000b400d40180e40190000222504281001c5841e03030f0051901902c00c0307002c80c804502080640501d480394070030070720301183c01d55602c107aa84142d5014007030007050683d81d1810301c15487e941c0d5000c004115a80d004400c4000852207292084030f048940141d048000c2c005011106180050361642d00d801941d41c502d80031010850074400c45010b030825800700141c3c1c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 409370017 1250 409368767 409368781
    0x300f100504050601050306100303050f04120f02041a0f0f13020c03031506090d1119060e031002070f02120f030d0e0f01050118020a02150a0504140d020a0803060303071a 74
    0x480c3c416003049000e544800d0500040f1a60b42080c4c800303c94244c540306459807484801c0d441540324079484460700c0551240fa100c00d001c2c4a14058098520850301049170502d2103552580380c0795018001e5a1111040d000304602d81041c880440c004440200003074405148400081c1c22a08032031030402055001200304144000e0305031649141400468466007000b0095001036070610102d5002081036412340030302d00f180e413206660420041000070501c440103407606401085c5c841880703070191180c481e05585020b808440d1088480990308480c40d01281c18540d020f0000e00717440c3e074130400301d988600c105080742540188040c001c900c2c07501c1404107812040740c41c4a850301e070080f020850030340d140200400151154008003030f0040801c000c05030f252070803c01d080c6d04103003050046400580c149001c002d80020742e170b4041c5111303511070308a103040481d03584c0703580e9640c600c50001e03900541d02c00c021040100f00305101660344040f008044030320308411a83e030503c542c1242c0c903041c0940c00340e1a081c4100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 409371267 1250 409370017 409370023
    0xa09020d0203070e06100c170a0c0f1416261014160f020a0618141e0313061809090b0406052a0307020109081801030b300f10050405 58
    0x81820a1031f00c01442049615409058901c0700d0612410000c0003d03910307811030040c001102102d03008403107517010406a00b014031101c41201c4003020780340141514100e0b8110030040d903030b068802c0007480c840fa4840000c066a04e0907907044210006124510b6010100020340c052041c3c55064039407510901d040001140780c8101c103841140b4140f010070000035003e65400039075a00b1880c0c11410100d010048400c5c16080d122101c0800f414201d95070742c40001070100090301c0380d04218644501521107a00440c0c00e9140d000300d0071405051840c1d418200a0144502d40c1810b250b0b120340e001e10388c0301d50b99001810485404107030464022604a080200f07002da07510030350364480b541003148a4164980d080401c209403560107a41050040880440c101901c00d5100c003505990104090707540e11058003100c96842c40d80201140000e040040c41c4040e4200043c0001690719015030204203120880341e048400708072421511494404c4100541d2100310030032014020040ba81d400040a0800d400e265007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 409372517 1250 409371267 409371289
    0x3100207050105240405060406050d050a02190503060a2c06040302061b2505240105041109010f030905122109123610090e0a09020d0203070e06 63
    0x5031891206240c109130694504120090070210303000151599901c00150003003140742c20140d0400c0416000100b0858000b48501485000300c1d0300042098069002d00b562502074002c103905904100c010480d203c80301d8102a41c20315183c41c03544012180003001c0000742d1600030404a60781e022905200a250f0184150740d0494031107510314800d00740b5a0100c280d103200702d0031540b0140c0c4074202c1413015500b0380320500c84c8280d40001a50001120b200c01010050352485001e21846030800002075186080d10841c04070fa644208110304001c0740c0b800554182402c0c428510a26450f00031420000d882401000c45403984809510f44410450103108542c14804a80201481c514014000150000140095110760403141c80380d0321101030f41d060808091601c90110312288641d1036203040c207098004111b5842d0150352114003018002da080f41d000e445441071110402060020411104883e000140d1080c00a8540112800c1c1540400d20f424503540c0110303040c10702a001d000c4a8502201004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 409373767 1250 409372517 409372531
    0x20a020303030721060b04140103090b0406050108071e0e18150709080f032217070914070f0e031f0506150a09061d03010207060b210c04090c0503100207050105 70
    0x2c5d00e00300341909603140304a0184a10031510703010b01030380700d038440c2d001145480c0d404007249a042c2170074684000507100030b01850f03003d8060304030301060000c00fa01111001144c035031803e41d026450981040310044024005a0610810901c0c8541c0c0c0c400810204418040f1100b00c900203161032a40100654002d4200c0b80c4550091040c1d1228441e000060303a11090000c0f40c0903003665065600851003820035030110341c020040c0c03100c1a035141d0020511404582c1c03000e07014054005058400700003990b00311600004141c4907460410319a10903015000f40c600c01408540c0340c00c0c250740c8d4101101c2140070000000c15169401c0103824241100300030300e0700d40d200b12168103001040340040d00200c918000d100c104440c8090300007482207903190b2000b40b12406002107540d00201d0078004098880c0d1a002805072a0814401000b403107030b02c040354030380d1000a02805c10301d03003030800708400360030990b000350343c444100c21010600d640c00380480c03003282c0003000b00180d03205031900d80242902d000600407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 409375017 1250 409373767 409373771
    0xc140307020303120c04081b0418050303070c030302130806180604170c0a1a0a05010f0501020c0103110c070f0e0f0708010504090302250305120403170a020a020303030721 75
    0x300c40141c400109460940c141d400b405002580c07182d411600900540d17101e01c1480c802c410b07104964603180580da03405d0600c03d60301408013820090301010305114615004199920070030010390b060348a0303100591150302c00c0c60007500c0c0c0289036400003042900c5402c2101130b9041141449a501d100c0600c40400390341c0800079001034a81605d6007406c2945204030080343c9140011a1300260205014030504983d000462015100d150310030b007034491504a80540341c5601c0c08001140801c4003000401c1118816401460021607a000440107491002502d00c85c4c131009001c0d000c40311205018080207084040800000e8500d0305a00034410280035189109a5001800380b0880c590322900c0039044d1807090350041014501c0303140803842e1900c003481c0100c0c0780016043c003000c010001189401101c1c0074074201c42c00080948101001403107a4400100040d9035400d984080061000c06060865401e00643d01c0d07070000c070313004a0309680c0100c4418002660410403040414040d50b0180050300c410001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 409376267 1250 409375017 409375027
    0x1031e020d06091a1210090602090906030f0d05090a031202010b010f091203200d0203091003050c0d09020a09021602040f0509060406050a150b0a080f0c040302060310030807030c1403 80
    0x460b11850300c4c040d02950266000100d00304c00c90504014060f07001c0303001803041100e0b4030141061402908502c80d80b911410000c8041102803400103001c1c40c8113802c09020b0004c2c0bd2840b5819562030303200d024016040240c1c0040007003c0303008864034100c00f21454002040400d1280d000620400a46510ba414892608014800c14406c40c14001d1a994141025043c0300414035039400c5014401c8001c4090740701d50194168032a80c08009001203c00a80310003008403141c0c2c6059060310030444143e03411100510802001d512a0b4101c200c00b039002601140400792140f40110030ba90003180b11003e2121001c081d4411400c1030700c121f1214138100c0700d0402450400010140c0c4034140540701800341034032078020919481e07241c2c4c841c540d140190107502256a40d80c803061041a089062050080351080000500d9400407030403c2d4850594812190b01d417074215030800480e0381018142d1003108c9080680440024031600040041d1402600c170301025801600c0c02800c43c010315400d01000d6001400307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 409377517 1250 409376267 409376291
    0x60304050c060a05071b03051c050d090c0b12071d010818030c1f0c03050702030403061a0904030806120f0a14121c06051005040b0901031e020d0609 65
    0x169910241011501ca60340d41c141210129198002c41700054000c64280740401c05086069480e001203d108100f51a1484010100003d00308441a8032030701140c420402280e481003103030300200c08244107502903083c081d1120114103150b00210890000d8031000820702c08080d401c0035a0040d00c4c144144104603100fa442d0000b055148050080c0c0d06075041414910080306091003138072903080d010012201501010800c0c0d001c0d16580c5120340021614110701412024800e01a15106665540040d450302d4990703916440104440150241d44401010851030349560f01201c880c002c501a82d0780e181103052040402901102d8482c07032166661017110085602c0301c0c04900003c8103a000006144501440e40340300d4146280e07101ca540c1c95003000101d03468440c0f0f03500c0700300113028402d0314100f00742900c400501080200f51a01c24020031000d102c100524080c45004251801e4185800304002010860010b801090764082c80201c1e138002c0b078840b01254082c8a003000801c540d190501c5100c141203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 409378767 1250 409377517 409377523
    0x6011701091e0c090e010f0b060c061306110d05010305010e0c010e01110c030d020d0f020606060304080d0b0405040c090b09190b0105070506090303010303090b0909070f0c061a040b06030405 83
    0x2400030003403510b40e81040310074488050403640091030002400d00c007010864000600814001c2ca0588455240200c000380d903081100969402d007a6040c000c00c050313180e0141090500d0550031003214041c1d1603007402d070321354100c00010704020324640c01c01041c40d50551034000e003580e8800004102c90742c130030000c400090380e100803003501148081c01c21000c0d40f891000543e050a00590500d078242c480e06102c1b044066000583c4407e0344560f03626490040440641240c0b40c0005807101d5510410a001160109001000030702c840103041c00c00103007800440c1c0101c2c00340c1d0000c0710159a01c0c854030008010361520f9000d050454002150030700154604070582a030f180b8042000b0280742513443c880c554070784c3d006804441845030001c00b101d499103011600280e607984240412800108405000151148104251000000001d14444296480d4403040300c2c141c00200000042010040c0b410000c940184241111608000521034150381e04100380825151721142107401088100700300800320f0404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 409380017 1250 409378767 409378793
    0x3070b010b031003050703052103070c110a05040507110f07271104030f1b14010320070305040f0501020a02010c06050a1509020c121306030506210601170109 69
    0xa903142d4882e119105404849a450b0304001c040388900700e00031003400400100c00500a180e042d0040c0d0010400303484c8003072804151050f0300803c0030800304e140090044100f01c102100050890030066550b2000501551401d661501c080b076400c0c00d1700030b807a802c18404544e06148800c0203000c441c0c90001c035140601949241e8030785031281c4801a1542c2c3c10a80c00c103c02104c200700f4110744840d01c9003042c3c0001c8210361400c81d984180100c03c002c00c16002c01088041341c1069403090031004520005601801810b0078061550801078640c1d5401103184002c2c11016007c3e0b9501910f49003403038440384101c00c0301d403c0030741550b01c0302c010640140c1e40309220249950f400704000c9200e8817450074000c0030307045040140120b004a1800412000030550107080d0010b501011100010455122500d041c0309030790030600c406a401c0000c0c4100d9010350000340e00718070064200540d442081e8040820510f6840c0300880c26004074004000c1300860641810070511000001c00032002141d0b2881032321111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 409381267 1250 409380017 409380029
    0x905090606041a19030911010e180109140109050603060408070c1212030b040b0f0d110306070504051f02100c0e030a0501020408070e0f040215250b0903070b01 70
    0x11100000301191669415a801407040140440361108072a80c4400c1d55041404628020080305500a00b028400c5c00340d058206e4004c00001440f0740c50340e0044403281818000741d508100c2c0c240d400d158480c0e201420f46d00030b0115100c000380404537030303241c0280d4041c1a030010480030f05043c00d000040e80c002c200c3c1508142d01011460703962601e45012242c00703541c0ea02100558440dc4204414060562203c0c0070958240c0d8003007041404440c20230084800702c030b9032150012b041c440d20900ca42440041940064004c5420b00c2d44142c0020009242440c102d900d0000110007040030007040c10040d00107268640b082810041e07208000e207000396100c0e00311908203101e0f900c4101032120749000c1c60035156030501c050160f484600907401c26902030f41c464420543c991180480000c0c407051341c1c4142901035002d99489550070784440c0c081281001940c40c0c060003450041144041c58041800001045621480c00316100203450030f01c0f034460803008104803000c1d0010088900024000768405054030340c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 409382517 1250 409381267 409381279
    0x70809010c02010c06090b010f0b0c0c01110a1e02190605031f15031a011409151317070b03060303191101020d0f06060e010c080717040b07050c0102010c0905 69
    0x300360700049500240c284c2c0007520581c0360440c1001400082100716069030100c42010b00d800b03030b40341d0810805201e482c92240d07054000c90802c111943c410503d6011480f41d04045131007010242d2210b112089020348031110180404200e00b04500b004199010520031710075140802c0d03403800b54003500a2000030311202844c48000e000100300604500840054000c900100381602400f58000c1c0040480d00e00e0010227405680020407190700c1040400c001c113913014251418506001c0503c646116010141e07004e5030f2090000c2d22041d0107001d1404020034805d000c80c074410501c2656941000041e80000c0700c204030170400c20000791000411200400d012540c003804548a0240891300c20500c03101c500142d50001450345d060b0386441d08400070a035840901009a56a511000ea030720828941e0030501241d40f140e14840412501c6020b07142203030065092400c02d100b40c00c4907410a17481030304000699400400c110060004c10003007841102028002041201400c14002d0020300c1e87c0e100e524441c038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 409383767 1250 409382517 409382537
    0x601060c03050c030d020c01090c050a0513050c0c0d0210060501030c09050d0f12020304090b0a080a03050d2c01051f14010302070614040212010504150c03021210050a0b07080901 78
    0xc0040084481085c510041103407900360304a001d601902c45007a0654000c00c2c2e030007004c5520b1905a403118220782d00200b15080310310f0100c4800c0301601c1300800c0320303040fa681800b9010380c4000901401d003202c1840c0d40a8180f40c80218214021119903800281c10549404c1c4c08828440d00700c2c80030015107104548070310351003040e03191925200302035010081c18042012565030810741c0000c050f00030b0314483c0340144002711030f000c1880740c250320503ca180650b50104020a010074000c80042585034101c580c085071204280b28021500c2d0301c140b0712081aa00707903180c9414a02d00030b02c9030580040005021900208503005a840d41000d5806080d5900b40d60120b6085c141e800f9604480100c0c3d4449000e00c5001802040030800342c50840e400e83c05000401110700354004188100c91041d54440d40400c007031182c0c4100036000707000c2140000c2c1855800c0000c403040c7d0113240400b0344544100703030603010014101001e125101d80943d11000034813000b0300002c0b002450100c19580714640030320380085d40d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 409385017 1250 409383767 409383787
    0x61501020f01090c060f170c160204110d1404080d05040201090e040305031509091b0406050411090108010e090319110a050c01090815010306050a09020d1419110906011809051501020601060c0305 85
    0x1701003412720007980a807800e245205401407800c0509541d24098008214200c95012036502e074079001c0b540100301643c10040c0380c401c541e0310f601a0740c110f4011b01d401404a9242c02c04504280d03015682070b400300e1808000c03c580c40d081c003c2a4980c0110590710141d01b414220030701941d41042a00d0b403000c0101001c45a6107a840c0c541c001002020024418044040190327004403840e0b0005038034a0006d0342480000c1010052060041d015480e050000d501e440e42960203501111004070322402004264982840c1601d4200020a511401a0050001e540810780054960802980012040d810111540a1692405a1081c11039810032008a0b603903a07a00700e801c00070404410001e5108a01c003008405200c1808070040b1a003a1032011149034040a1280e9000700000b020000c007150841042c80b005810059512900000107042c8010140303004103c500c00c0b0f06660f00316540d0650742e001081440320161f04012070452003800130307150700e50405900501e1100d0052000c0d0600000094030354036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 409386267 1250 409385017 409385047
    0x200f010509210102160510090c0b07151103071e021b0310091b0b030c0904020a0e120a0512040308030c030403020304030f0b04020f040e061501020f01090c060f170c 72
    0x40d0702e0320703000210b507100040500880194107003002a121803003200c2c1c00d1b4441103c03510079002c0d4617070000d201a01440c5051524005a131150000b200c10300403014003581078500d00c0c02104d02300d44003004000d44a1602c2000104800c00d0048140701c0c20000b11400c5140e590007040c02c2c3d901120a070201e441c1da540340c80210b80b030021403030810000c80e40b03410100780074010310900e0410f000c0000c00980016075a07078440c50b55a40415035a640c0301c0441042f444156242c15801402c0440441c01d01082103c00d284c001072205c1005040003049401c900345440c00c021003403206054a9914010050a050851710b6103026400010303c0003071480000000b25003414020401d85000355072000d80440ca809030b40c0340403401c080d803d41b422401804041c50403402031a150243d00c0701d03000000000c22950b901d91032035604819903541440d055000b40003105030b1642c401e00034081150301402000c02c043d80f40c01c1c0c0090062243c00b540a041121040207061580d5001182c0b0b0b4110300310350b2541d501d8100c81d01c80140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 409387517 1250 409386267 409386319
    0xf06070203190c151d13090f080406030e060c0901030c050705030711090a090f02010518090108151608041106040b030703060302030d0f05041703070f200f010509 71
    0x40214603030303955420010510f1184007503554022040c004001580c4059818000140400c89039403040350100c546820302c01098410544c1070075022480c1101c41d1112008081c00b8502595a5140001c1c14010a5098040d00c5200418880100300030300d07001c1c914441170300030248030798101901e0360068138406110780241c803440f03034108050382d0b91090302d413030501822142103800c54010080cc0000400d43d6595200d00400366401502090041c40b15900446855000402444407028440d140c06501d8030f4030340140b40030300144030042c6100c4007030260500019000800003450340c4c1c0580020b446807030784017506a0f00903138845000030000011034005283d5000741d4100b40d403954008400c006840d40e141c0c004400b2a402501503e841030760048040755580005001c4d10082001004200080d803417071942a900560110103490810410703a071060309020803100b0549031148007031500d080d82280056040e264a01c100c44820b150080000043c102c0d0141402d140c0c883e012985055010707404220b030301a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 409388767 1250 409387517 409387543
    0x140309031b041428020d020a0206042307061d040c0c02091b04061d03070305030a0908011407050705330c030f13050c0a0b0702031603020f06070203 65
    0x50248a080006a221454240e44051040d400c10810004a005004050303004141c4212544c1002d1040c640341c0b10342c240c0d1440b5428010f9400c0140c1c3c03503035480902c042d003190240c0b070307010340000e0410341403440a40c0c4220091030030600c0342c803184155016000800004803030550501082645040c60307034520442140c3d030816042070a284466007131907448036940705800d200b1183c0d00902c1e1111424200219609d400b101c144506c10441407196034080c00b0f621a00c6000801014484480400441c2c100090b65000300c840741e00102303010504640006075100904070b01c200801282079042e00b440380e481c00c0504000140040020154240b11040c0700e14031019265101c402d140d01401010981c0300322100070795101d13031100349000c20303081304401301140d00944035100e02c0d04854455540042805802c81e1088920307100d00c046e00e00040c0c560b8a400d45c0146141c2038200e4440303a9034018076040c002c01d11068548000303401e41c00d03c016500c000d804416040c09a920350b0301c0320712501c04640f9003400d0321624 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 409390017 1250 409388767 409388773
    0x809070b12041a060105180f0301150f1403030304020108040618081c050609040308060a03050106301527061a01090e0a051012120e0a0b030414030903 66
    0x451491030750700000c5000e81c1c410441c0880001a44004031200303881503ca16000170400c01681c1d5014142e050f9002450a0041ca0f24001c0404840081e084480c0e401046031742d00c0d4010810020940203a0100c030007400c4400c5401800b000d50000280c03079200050009040c0300c1e07a10081000e0000b03540c000d50660110031420061020b140c180000b840c0c0251901c1a0307070b808922a01c0c00c060940740192070141d070b4054030030a429100e40d54190b904101c0144003d40049a143c4000081442400b4140040030921075681090304040703003129440d003025441c590864508a003240004900501c0e00c03000d40314048002400360340e809551074010320040360002c44440c0c441d020f601486120303807107030796504a0300d45400c0d0200b841c0c60056130f0a250714861182c4010700200000d22038800b0340c2116511009042c40724030850344650030041590030440c01a110441b40801141461750041d841c849110812a006500030b440c0c40d942c0e0041e407000400060804824641000707040c507003001920030100f801025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 409391267 1250 409390017 409390027
    0x19050705030a08040b010603180206071a040f120c110f040209040c030b1c0b04080a0e0a0b0702131503080702031c08090606060405100809071e0801050a02190809070b 73
    0xf4021003040d20281c0350150f000000251490003407082040004800010008072005030f001c00071690811a416601d0110341001c41007869140e05802d84a903200d011551a000d202e03082c90000039051608410511074403091b10710210301042d80e0740e112450700312800034003048640f020074041c0c024080f039141c00c1401c0191081071550503800c4111011425140381c160308828011454880b109000d0152080b4081400310700819540300003001d0f004007034100303000c603003002c04045100b5120b1790b40510130910002c00c1d0130b070440c9440014001756400e915001d1014201281020700b0301d00c3c42e840010600c17100080e0001c115142804031441303901c50510080c0f0041d00380c0001030702504007142c2d8040341d40501c400092007403074003205a50540e040074141c0c0d8412003000400b9140d540015102c05c0040c49400d4001809018001a0b48040c00110740021070f5030385000e03601820359070003a0203020041d0062101c03205600c1c808101000309117051400c0481600c030650b0b100c0c103020703068018034401070000131 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 409392517 1250 409391267 409391287
    0x71a040806131110090806010308030717010302010206070507050709180309090606090e041e031d03010504020d02041d0307030302090f0102030a170604020c031602100c03051905070503 81
    0x1500840351594192140c540e10450550b09044422000400403205070440c00c606040c841002c80303d45205041500c009601e45c03041c42e00d0702000740c3c0f04031200d10300001004030081d400088400c3c0703d44081041410703541542d0004c3e403141c2006203039004102000c80c04000f881001c000400081c00001400c01641080345086076140e01500c1c8207034089860350748005440d03001486102c0c11100b8a59076500355506250405080c0300001d0001d0310480d0f07164442c6002520104401d2250340c0c401e0320354051000c00e41d0760b002c0d13612000d0903c4600ca40d25240400c00542c803441038144080d45e0460f80014440c3e15209044a14140107484860354840400c0c40300030190544c2c01400c00143c12100d5007100c1940800480c0d0324861111039a00062419202d074082e00215211071750400801803000d41818000d9202a2070358010705d86510b0300c00103618045056007031030880011640da052400d50004406a1005800341c822194210914108516021460f81c400c0e0203541c072069001e02603076680c80e4114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 409393767 1250 409392517 409392569
    0x6060f05010e060a05180109171510081b0301180308041505061e0307180b0901080c03060c0a021f1e050709090203100b0304050706020f06040b160207 66
    0x80165404a0742a042c22031580c80d207841a103800c01e034595285843d0030000800e482a0f84114202141400f84e02940400c1812031107204a05510240008280d04110009440c416800285c101e0f262186622020302840101007015203807024003034103031160240d0400200e03005220140039820806071580070344080640c00704215020b04e00900d9024000c0010042400460f141a110998031040b0341d5107606040058026600c50310750002d080c3d50140369202110020041d0400c651141260782d03240b254010b203800303144a4050b000000040214043c0c84003c01d5440c04041c2050740100c4010030560415442040002d044031003c294128031800135600002c00b5110009074070b0301e072407140950384101d02100d10405101e200d056890103415440d005102c0b0003580b016200d182000c4581c840400e07800356110040d0700491007100200000e501d0800000c2c20424004620301c5690403140038003002c41c8403114170f40e030802407030807a00c208040b20700c0050b440e194003503000707854050b00c0f858202e007440e0300340c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 409395017 1250 409393767 409393769
    0x20a020d14090607140d080f190609061403070f080c121009030302093a05030d09081c0b060d0209010309061a0102160312050f0706140a14040203060a0b060706060f 72
    0x807800c80301c0958992000781c5481d103088807103101007180031000880d40350384006a09e001c8d4004141c0012440e0310b5032403410545601c0d40040c03001c4210a0080d10782c07400c041107010000c000400d0800d80003410007082d07503103070b41e52021254420030200b40140c00f1800188a281d51420f4031920403c5203810526001d0040d40001011921850800319180344084902c46150b15091140e95412214800b04501c01c91702448072380c007604c081c0300034445250f240c121403280e180e0150240c00001c7e181c0391452009014a914848603031880d40c2003121003041e40d05c90301d06442c0324010400b070251310343e441100124020078407034030050b000600304401d054403a107080341520300600d000e81c00d540c0041186010900d40c07003400c2c80300811010421102d221031912070070181c1028000304501910340166500d0740300a07642440104c017054950032003800040d8030b4520401e00003000345209400286410f800003a1940301c0100140001c5440d00f03004480d9a4919040318001c40d8070100c10000369844a50603030184220b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 409396267 1250 409395017 409395053
    0xc080a050709061203080601180f1d0108030f09060d02121e1e04020f04062615070507020405041112030c010605040209060a110a1401020a12020a020d14090607 70
    0xe0103038081a50103111113044401c03a0540c9130b0301c0b69500c50000445291441c140d80344030881c0804804182c0300b280480040081501d1103441061045c4c0089001e0a10300680c801d1410358002c01001a0408c5024103849089404645c45915000c0703005804001e0300c0350040503030702800030908101031104800c0d410b02d50318051098008542e952481060000c10f44401311040909194000400500d800010080402400340000c22280d5562014200c01380c3c081105009141071100c0a0b4280300040114460900421a40b90b00609246101030181c1c89221406070003643c1b1800000e0521021204040c1d2068000e88002c45c0414800100382c1c0f00d80092200b61074035400d0034000035161030240207440055030002c200300d140c2030101c01c0c1514400418500c2c49514082d9000d10b00c08101c0c2076370784440020b030b0000050781d62120088002e001c40d1a4149084001d0b1040c801c45a6007540019401e200c102c40d41425500389458100b42030240c086e8814166010034006441b0b010084040d1552580545d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 409397517 1250 409396267 409396271
    0x705071a031e06060d150e070c0b0601090b0405190b0409150e060906090a0b06180f100914030319051e03063a061a15040e040c080a050709 61
    0x1ca1048100400d21056600b0743c3e0100f005e02c42015602e00a500c03419003407024908680c101c607681c01220f440c9441c211a1a004212480348103824401c00b043c15650044091812800c010700704200c2200d24007844c0503c40c0900320050f10f9030316220707090000c10064100340c44801d03160395075400030364050030800c603042c000c05560400000d0075042c2d40e902c413405000024400c1500c0c3c0d4a00d4284943c0340c20003403501150a0700c400401c1100c1c1c580a00130010001484a500c41120ba8070b02400804480c4101e103501403080345480312010b80d404103010003903c48d180746414940f0741c003100007442c47c010198201c4910300c2040118170380c41c1c1c0120042042c0f00c5005010b0442c40f81d107031300c03042850004450450300032540c500107800c5c0e90549030840c4031240d4120504048480780c50f03000741d840002204100d03155070b50b9554480108081410001b90000c0c01c45581460180b4441105201d000d00c0c4a59a10100b451000c01c04201c4084400310107458100121000c00607a4186185d03150102d2154142d00740c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 409398767 1250 409397517 409397551
    0x30f0d0f030605060d022101140a06050711210304090e0d051303080d0f0e0705010206130f0605060303091302030f060d021e130905030301380705071a03 67
    0x103001e4000c8200300d0304024405410440701081c041c2c0a50301c80c0c40740388100018040404060007035404414064266900713040040c00c014001d10440e541190000740c24001c0c241311010000704074030401c0002e21000c0d01c07075000d543c80051481e075801c400c28640d8141030201207408600c0308400d80c0b00e40210310320b040850381000744403101926103118210a011240c1c0c00404240042000b2800502940042c0c0100003082d90300d1241501c12252074140924543d00142401c0205d9a03040001d0364014544041a8640260903921003107140740f540c00040030551a580082d0003540d041c425190f0001c80a0320b4000c0001036040004000c5d402102e00840b18090000403038a81d090180000e105141d020b000c5e4185081440740500c43c14044140e0b842d4404840a0481d40303075200c074014031101d1032040000390303180d50500e22a0300242c0c181e0000302e124030010248000c011048520030904215610007a40d03620101c5090035428810b01d03811010a441144085411041504006520034510040c0481c444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 409400017 1250 409398767 409398797
    0x420070c060c21051201090c0210062610092609130209040609110a0e0d02030307150905061003151515031b02010204180506060307110a02030f0d 64
    0x512141200a00420b2001440203204811050141c040ca075190070542d0030406091790014104500341c0215040a032039221160805404000110303413040c181c0418451a0f040800d00001c2d1080640080240e6100e85030500c162142070100b400394030005503042c0001030343c90803c2145a0080407400070b07550b07203071888070740f280100303204bd034400c008020030a08181c80100300c69400383d08848001a4020794518000407014258894481e85250402403145c50340c1d40ba01c0c0207030240707061202d17150041c0442458480140d9000c0201c1ea80558814038a00b42e030f45145075400000c00c03a07840d00409174030a55003404081030044c698002101e03c21155695494420300c0500240e0b9248518000d04207100542480768054020200c40c80880a05c2c2c0010481220124400b10700101706805002d43d500142c24814051701801004d81c01680440030703c207038207007003010401d584030040140701002031031072070340406070014491b00c0e44454004044403080b89000e41a9612980202c0c48000856403101d04170f500b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 409401267 1250 409400017 409400027
    0xf0d1508070f12080306030c130c0e010305090c15070837020a1205210105030c0307030f3801090c030b0d020d02060f0315040f090b150420070c06 64
    0x2580c10320b0003001603040141e0f9a1000d05e030800f4100662501a40751407000ca903d9110070301601301d0180c400400c840080c0748015040301882b08541c1e0405042c4420082882c1d0f000516440c0c01c0410b50f002040710341040702e003a125028400009000b080002944103080c070040c0c03000380c1c82007490450140c1010041044521080080c42c50b400135820074901c0310702048500700030030704510480c2012845c2c111103140103800c8010088072000c0c260781c0e80d4014072282c1400c00202c25503080550003402414255103903860107041d004001030540300300c000a079405070035102050006060060a103221500403070f4481c50502c1090181e142039a00d00106462414400e000c1d020f04080b01038901d4004101940070f103c0401c07411213003a07800280802c82e01c00e03000d0342400114410004c0e0790780b2100c0c050032030080000f0303120185511241c0300e0070b1098a2001c20b500c00f85454101e180c0c21454900c4040e8a408600a85141400314403180480d0310100050101c140c02040d40500c43da02c0d40e40b8180d1100802e540d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 409402517 1250 409401267 409401269
    0x60a020f06010f26070801110c06060a0b071b052707080c09040207051204120506060d030509060a0e040e01060314070602060c0a030b0306040c05240a03020f0d1508070f 74
    0x241620341c4c140d24500041060a131240a510b05010382c2e01c941e4807081d0030780c2507401c41d04084048410000c2c084496110520006801280444004410502e040095800c9010700030024281410315140741000b50100c00301e80008080241900c04480001103080c0c98600c1e4103250041e44a40c1e070000100f82d83d114005c02446440d500345183d041007500070500000790000c181c2284e49101e4141c45030040440700c80900010050041c0b040403450a0b498880e0420301c020300058001e443c9140c0210003c0c0c0c02c0002e440c03000009907070f4940c0310b80703170f580c0100d50024505040e560004e00e00454010081e0040d0001010b40c3e0046107038250500450b0041a90b0304803610a60b00103800c001d012407509820180203040e49030381480c0c04180e00c20450000b070705042c41940c080f0b0301c00d03a031840100102d0800307203007082c00e8505104400c5290f20a01c0c003444401d1083d111050105a40020f0310b003005001101500c2d81280803050802c881000d196154082c1002c0e03006180803445840700002d011040c40d12404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 409403767 1250 409402517 409402529
    0xe0f1005090c0a2316051504060209030d0323060f0a06020102220b120414031206010809010203060904030f0203041a04061107181508010f150f032f060a020f06010f 72
    0xa0302c0c205c3d01e84444525a21201c1003140e0b80d000382a60b010115105040440c0910302400c00140e64001510130140703011100300c0e000c4280350905000c5144040740c1c510b130050b030300856411000d45540381c50008241d1010100304039400444003d002c0f50b40d9505601900c445a402c80c3d01e480071110046401252044c0c9106e0f00c1e00030202007000750703403442c804a5000d0b001032241c00f0b11240e00303182c00c03031040c04c50f00403c0003141520407500070001c596a124200d0341e0004a00402140795017003a20209584010080025080c00300b103004801030f4600c01c100300c80040c80310740085440a1004145d00096038014824080010058101c55801000126200c0200d41c105440e10305010303042080140901582d045034600035040c0d0400040d9480c00313020303080900e0f8502c900051a404000c801080e8040150015185100a82ca003840040e003016038507004014190a07240c0c2032000c0da0100380251403060340090b0081e4000c90341010094000659101c00d4982c0025100c20780e0702c4811042100480c0e101d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 409405017 1250 409403767 409403837
    0xa1b0b090d060b03010b03031c0606050304052109040c080612030a080703090503090909030d06090c0f0e190602071d0c030705070c0902040f08160e0f1005090c0a 71
    0xa0001814503030000031000c0f0060001300e1000001400242180c00458804800080c021240c5449220300c2c480d00c0098039190506e1030031801e141d2105070303440352054011000c1d821040c0446d8000a070030003d031081c03150014401e0007900b151783d02c0204051003e07100e40e07000c0c6e2144003410301c45410100649d19091100d40d0742880e00d40d07505a0032009044c41d1501035400340420800c000d0152514006517202d6018000290351ba00504507022084030b0440d8042c801d447d26104240c08250340c0080c2514440c4190f181002c080e030032020004020703840c883c103040741c25403502c000010380d00e402103244000c032502024042c408440302c0e481d0300324002040300d03000a5100d04100140040d4020400717411124011030340259175648a5200200b01ea0054020b224404440b00e0204140c24040001c592a511090070081e0769601e0002c2e8510040b20180000001034841ca00069503c034000409000419006000358014103003201180f00c1a0b00049241e0006038903a00841a08125291810f03484240c2d1400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 409406267 1250 409405017 409405039
    0x603090a11040902030a02011805040906051f0f1509081009030807020c01090b0c0f100f0b0111030307051e0a0e0405070c050706083c07021f0f020702030a1b0b09 71
    0x4442c144505a03c1101501d0140d00200d85600c480c44ce060000d40f0410740040c00b0f00b01010344221604015504298107540403805021084460540310100e0700302c0f40c0e07103016945000c0f0054418180c5500401014070407114040110721640c3c0103062028000d17110a10a5121924100e80340c142199040340070842801c0104010f14080005281b030103846010b5450b0300d250455114100f01111011141c40380e250741d1991044182403140e2450f146003400e003045031318801d02c0002d85a0000400003018003c01066110401c01310a40c49000f41e04100c4801c1d503a031524200142080c8013482c000d50003240350100050000340030324150713004240c203c8001c040a62503c1e00c1101d84550081c01003050f07600d8482060b505c8401c494800c900d28103e01c90041c94034104400a00c1c448000038a008115845080800c541c0c00030080d004001c11442600401e511410354540c3c0064071a004000b509032141c0304540d8103020101d00c90120300e041d000407901400c3e42d101d1040001d4050322041607448582a61 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 409407517 1250 409406267 409406269
    0x60a061d040e03132c0604090203010c09050a080a1a06040e0613030e06040605030417040815180102043c170708071805040609020612010303030e0318010c020d020603090a11040902030a02 82
    0x81d9a1b90062005001051590f926404a0b0944000d0304075032020a2101000340428580701050001408503c0020a14034400762100f26101141d107946403040798001c00425415180ca8020014400e00c1c03200f102c07158107084032221514081c0b90703002d4001407000380f400b10451405070112411034030b80765540e50079521152100c41d02080d040000e150801e40401c000a4003000c01d01414080c44c0b4407071000d1b0100c1c80c04600ca10307080d04a038a219106d691040109100c8400040c0c0d0440c0041540d04032100041812030840c0341c0c880d03504100c001e03800481c0c40300080c030b1020780000d5000e030f60b004020396050303a0b038400d021a513611260040325600c115014851040c01141e0b40029070040c015080840d49503129004070b540d03035000c5548800840814001030080c1500350251280d4182040011883d0100e030311481c030000032a01c035034a0b0400c50405120130541d81c4980080b8602ca40040c8403e83c0c4e81001c81040b66203007000c080c12604001c3c862416020b9107000c1c8500e50b603542d0045e01504965007a64 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 409408767 1250 409407517 409407599
    0xc12070c0918060606020c1507020d0318181b020a0b150a0918051b0105040902370f0c080906030c0c0f060601090e060a061d040e0313 59
    0x1c00c42c1c00c42510303070745400b4040381d41c60040800800d11900038001128400c01844007580c3c04c4100e101510908001c04c0e00162070701c080d40d01501d0780600c0c00606022104200008034400c0d036020303500e410380002e20404842c126a020810541042e88a0488038541c8a000ea03221a4050009000f0388a00d00000d510703490880750700640184000c05c0e4041c0240c8401d500d400700d400e03039449035a92007403c82c2c100c010440c04208680f4200800c992035081051500c00007400d51140b80616400326401144400480d280d07170301019003081d0040c04501020035403001080d007112030304a140307000901103062483d0441c0510240300b10190410107080c40d1181c83e4061042540c8058156035441c4410014241030381014043c1d05840c15004024000d0b0742891030004141151982011400b920700800380801076654850003c00c6600900b440302c07084007a40e030250000c03035102c030b001034006040000408103400c002c8000d0400501105540000a0b190060402d5040c030b8001e101d00c6d050b04071800300003564640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 409410017 1250 409408767 409408781
    0x30f070512010902090906010314190f0602070605070f0f05040b071e050307140c090f04030c140a150608060408071412040e06041b0219080d0c050c12070c09 69
    0x46000851030403032071383c086920b0040845074100c0d01d41140b00140100041c0124101c0281d0064006229480b0120501c11032020f201b800100740224950906003000043e4068520041e000541082107141100d800703804038036040401c00c00107110303500200759140a54141e030b0a0f204001d00789800c040007503031062000008801c41b1960700420790b50400c00550100014489148190248208203140408040c41e1648071030030b071445030316007208020380c0c030090001155105d42c05207004900c1419504100c650341668201234030807400362062140900c10709044d2503c50f40245c01080040d103030b481184d5601c409098034000e101e40d8007044401c020401101e00c10300d000d440752044e01c50403044044200340681c406c0c2d001050f40492201080010f03e0184600703042c0038000c1c06134071344d5061100340003901c482c8200f03d03001c0741c18061002c140c184482002641c04150101408101c7d107000000d0107440c503044602100540d00c94800c00e4079120030381d007050303442e12540403114406040c00d0805800c0a04030b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 409411267 1250 409410017 409410049
    0x4020c0303130c05010e090403081008030a030b011701030203120a030f0c0c03030e010525030b060f070c06050a02070b18190801060e010305030d0203060d2f030f0705 73
    0xa11100a46000510040d4060340c652125144080c40924142110200d140c1c08241402921010a40941c480c100383d99801030740b52420004594880d84c060711100a1034104001a100108050300902d4041c1d001d000580000d03207a0506079402c009600600401c00d00000390150080803414181c44801c03c0600509000c030300b80414401e28290faa5001c451903030300c08900250245001d002456010310451468002c142e00071301203480d00400300a54200c82c411801c031140c8a0340709100125106c0d900112a841c0010403842c2d4401340030402140e1074000b000251002d03000380c40c000903014018002c840c030302c80d540d8001d090f00c50328011703040842d600701105200d1003a20048146256603921440d41c5881100070074409034040c284240c031821103009412100c0244491801400420f500009540d40f4201200025070b0300e030380d500c0c049a101c0f42141d0000309100900b00851a0003403880e83d039820790092021040340459502001c140d5210784921200005420008003486103090500b030010403a5a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 409412517 1250 409411267 409411271
    0x706020903071715090c0a05130e0118050f150c030709050612070e04090302070e040503040e0a050f06010f2c0a08071509062a080307020109020306061e01080604 71
    0x25581c8189030410603d403551510700e41020694228080c030802c801d40d0410341d12401409104a10340124050743e800c1e01a00c1d100701954280d05035040c1490b04a44440344c2000700074020b460a04074058a0144900822101ca01410070160a0030301c00041d000e000c25400d100b00d140540700c00940e420982d201600702c07400c00c504010046043d4039100c000f000c0c030b03002c100e0070058a442d01202c001c00c0c035000c01e000c0714400c42c2441251400320341d000800c0c20035280c100c004424241c6952600a01d948610340c040315030440d032035040210f08003040c0d00071803044072050f019400f84d9582c000110b80341c092518005011030f40086640424950782d00041c2540b030595a0041c60114035240020070b05401039204030f0702c40d40035400c18446000e000b45102603d108500306201d589082c642e000e80ae182c2102000d05030b1118070041c44290380b00c1c5007aa454403030341281101d42d0780d0600c0d40000303000e090011010383c002c0c40350a01203551814120603207905a19508407031817600540e2001180c0c0c0da08081c00c02c0754815 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 409413767 1250 409412517 409412519
    0x6050612040b060418110a0509071202280210050703090312050a0e030f1305030705030601031704030c0303110c09091b01020c1003061502010e030a030c050d05040c1e030206070602090307 82
    0x10f074917100181c1090740143e0000284c50101c500700311a225a079000030b8050b051513802d22105a40000d640600320b1501d990158a500114281c03141e00c8203844991128100c5c3d99140d901d2041d004508001010000740d4144800d070380e04002601507903043c0c00000c00084140d010b01e84103140c5640111340280e03543c003000c00c803103410488582ca582c21800b0100c0b00f4500c0012400c0c01015403e1803a0700603c0e042e0060200c0c03902d080c0010791950390501c0042c08540c4450304d002d03504542c00c01102d01540e8480d540c4520141c60f8103004021000003c0034461910403545106441d00d00001d480b4891704081d4002c0c9404104d00010001c10500d515280e0306502c500d07401030780243da80011103c06ea44071076078001000d900c2c2018203121000725426600a59260035145040d014010003169020205402e0100d010181c0403000c0380c0b640302d501701604c4584d1800050100f00040b450215003201d9802d00841071030784445d0400707032014095200c0254040e13010400c000c00254282c020b0458444006c3c182c3d4401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 409415017 1250 409413767 409413791
    0xc0102073809030d08010e1f1707030605070e100f020705091906060f050a0c0f080c0609100204080304180b091801110403120c080d0e0304080106050612040b0604 71
    0x3019a02086001d08041410180c1c0d00302005155140805850319110135450100c10071132419001e080c039820140824011200000c0000100b0300511703030060046c00481c3d240000035100c003440d003c1111164100310125a07031600c54a4a8295044020209800001d02d080141e4082c4101c0c43c3e00010340c0503003440040c03150355a02c1e513030b4464a9026200f03040150401442d00440300320740c1001080c0b110034009103180316800301c207465140a1074100740d000c10045041803600287d40d1680101031243c001080d441c118404640f05004403000000c0320341014001d140c3d101a40901c0c0070302040c0d6032050104000d14501600b0041800107929030004006403114040741400c03030201c030300c015141e241004441c00c03000244580d50040520a031906d04040c150381d240751114807000103140401908940d550123101c00b0400b12035901e443c0758820421088850040c9490b50403031710454810b5444e02c4000249401c101003140c1601800405080e8590b8441c1c1d44d198204c10003801d01c030b0f00070f0740d9049801c1d50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 409416267 1250 409415017 409415099
    0x5040b062d0403030903050d0302040612020f0d020304060b010807020c131d1203070216140907030b030f0a0312050708180a060609091e0c270c09030308090c010207 72
    0xa0750080e515170455030306504000f450304500c0701c03070f400425104100802007240d00c82540010603000b040b01607622502c003101520305000704140e2141c20ba2001041c00200728150f03100400e51042a2992507496965003001d90322081c00ca115190008444a00c1d0086c511003a40b0202d07071400c0b003900c0310300360b08085810f1074541000200c401c00e00c40380000600582ca50101700800e440311007000824083c42c03c1041b1103107507010159066010380707600d4002c110a14000d4010420720100a0110342c001203003030407110740e54070036090103801283c05a0070b0155440d142c0d000f1280700d058640c4030345040d501e8040019030140720682450200c0e00550f800c001c0054030354001c036401007043c0000412500c0d61420401040c1d070350b4a040b480080b640008250006807200f21120440b111240b182d1185641e991495004505584c10100d1991078003012080705a0442080c0059130300941c0c0f040c2c81d640d9002c2103541d0350f1000e80c03601800740c1d2041900b0042122084180041520b0100041c6c2d0080f00280d2031300c40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 409417517 1250 409416267 409416269
    0x110a1b0f0b09060f04231e060a0605030102030402062b14070905120d080a02121009050717010b0a121b031104060903230f1605040b062d04 61
    0x3000c0c1c800c0000e000c0c414500708181a0000d0b0051030014050a1a41e07402c50402005200000000000c1c081511203a505000044030042840400c0d01c41824a032401038642c141243d0000c0960301d084804a25400c0500c2524803030356002d4070319440c00c103044214600c840c00b040e01c0100b440310756440000400032680a440c2c03180101000035810303030a102c0c0024014034070355004070b402201842c054842184d000a20b00e81da14440c0d090040b00ea446001001001c3c6c4104102101143c2100d02488403410741c8265120499519000030071a9444880d011034901c0e080c21b1701440035080c07800061042455030001050300104a0401624480c0754018140c240d608050095107040c24040c501401160980100c181c450042d0000a181c6410984041d01d44241c81c000a040c0718034060000c6a2540d040c4400280b0303052070000c0f28240406944000c0e910103145107070b120b02e21080540040d0508003030003005500040142000d08040845450a01e02090703030fa59040d848403032004041100981e10001c1c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 409418767 1250 409417517 409417523
    0x910030f0605100f12020d0c0c02030d03090b0115020c040e060f0117031e040324140114090703090c170f1603020607080408030a05091003110a1b0f 65
    0x108000c0405600c030011a9001d40c00580640701e2144140c009680c09411000c450200b0b00740b80da240360b915140307000240140319402d101d40d0328002214103019040940c03c05003502c220111842c0244000c422001d039540c1110003010043d0310350061000d12007030a2548038000d02031044454407250000000e041d240d448102c2c080c0d175040007050041e1580c013910118050f00c210780541e8000701d02c2144051fa03902c283c4500d0380c00d804401c1c4101e20b8005207002245c0046030001914080d0190410b40e80a1114618007080403880c90024400d44a1011902450490300040f01c07640150040340144844014014064401c1551300c2c0b0920002904881004018143c084c00905c1030750590507050780b0781803102c9010803003a48460350b100044c000c0d09031402d0950f03038192002500c6200380d103000c401c50302954001e0086030101190200440d540320000e40540132080b210000c409a10010642c11541460b041d0b46410a0800c61041e005004034401c28101e084010605184290798480c80940a91007400b2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 409420017 1250 409418767 409418771
    0xa0c0b0f0a051602030301050f010903050601330c06051503060405010203061c0c0302060c031216090e0411011b140a060c02060907030b04210306180605090615091003 73
    0x80065544244202e40e0701041c1e5045019841894200180d41c03400144242c80c030403010100d210135140d10502142c0c0056501c00c08a80007561901e03134403840b441e001c00d98801c0aa45656405002a1100c4c415490b40345890f2a80041c01155468810192000070030759140700240740810202071b00c0070030000d441a4002c034001610b81c00e101e010082082285480301000f801d521030164007107a46070503407000301c1e0307411200d09a40e003c00703801450660007485807182e240b40005013002600300848903840c1c000d01140d40d0f115203640d200ca408507840745041d5009010346045240d41c021550144000004000c1824500b001c6003183d56210708110100d0f92001100d0740200c80900100005401401ca2100c0c0d2400505454540b14031207680c0ca4005100292081c10030f040810240601c0c464210303081c0c041c0d504642e0f6900c400705005000f0341a0b5104550350f0701411100d62501000724403400d42903030b2001306070954a80b5908200b00d6034080155448000c41400c0044c9840741d910b803c00b0000100c416100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 409421267 1250 409420017 409420021
    0x7060b28080c15120901110c0706020c0a153002120610021b0d020406081509030319090501020f13031202150a050403230426030f0a0c0b0f 61
    0x16900b0701c1d036421102401480c1c0d2443c3c003c10340002c1e1043c1d40c020540e80300b1010040d03480280803030140c00c1c03201c91408191800198a81c000e40701083d42020340e044da808944040c4808420320000154038890f490001c450303540902031892103004030544803511641560340c0d00042840d48080b50220099540c0f810364006110309100407002c0005510510032603002211085840020791920060710b009a01c0c004a5504c14003243e0322058a80325064028104020030364607240c000d0b503169218002e45c010b9a581c3d00014982c6030001044071b101d80c003040c4424104440300a4013801805182a007120a55028003138520b01d10000c03030181c20182c1c060801e8002617455410072001e5456100300c610115040003403490f00726004031001d1038001c0c405601c00900c50755682411580b1015218849400340f14482d00002800ba0307240141c020f59600e0601e03080e0b0781085100490681000f40310301d6080713030000c0c811102030800034405041505028100141c01400c03d81c4c55241d00041100c96507507111a00c81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 409422517 1250 409421267 409421279
    0x501060e03101a010c0813091a030a030f0e011416022403060607140d03020c07050f03060604090c0b030403090f0e060a05060d110309060604050f040807060b28 70
    0x201540100508110401c407583c0b5201c01200c81e04581c0340302c507051103c1e02d07070640c0420807640e04450010080400c00c501254407890701201030b140c100c0b02000c03402601e8607055900d180c00316045650607415217500e02c100240710801d442800034000900c2c180310741c640c91000f007980400001c21008008900b913031020505881003003504104250100c101e00c18450241c00714001c1c00301103981010084803500e807115128542980c210b001d01d40001c055000c1c0100320b04d0039603010b030060141e040c852416130740c85a4a0328184a4100240400039626a0003003001c00d1032420035030301080c0c400340500d401d105802e44508061f00c00d80e20aa500301c0016030f03005400c01a070341241e950381e405854100b02d404003904200300041d20384000c03409030b548075610005138218803005c15841120205160440c1c03e84034604045c40c2a00c03032600716450b034019410b010000b55045000c1c140a8842c0744d000b40b03550700b4813080e03489a400400c1281207203600720054007103119040480708100c10a120400346032440c001c1c1092 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 409423767 1250 409422517 409422523
    0x6040b0a1d070915030225120806030a170306030a0b130b01090605060702041d070306090605090d0f0f18080618030f0409090602040f0b0301031a0f0a0905100501060e03 74
    0x3006801044078040f0305200411000240d41400a840d18000d07845200010004400360700f61840d171110740c1030804c014010041c1c24001ca02d1125815103d10001d5694801810340b1044050001001101507401040c2841d0b021006940c2100014080351102e00c1603a55002c0760382c8040e1380805981a0510456013040490514107014100c0c80005203c00c1d4a0400454054041c4c0c42e40240b150b521600b51184286030198481d00f1138000001300c62041e541d0307040103001410781d1007080e07803030034101360009006500000301c40100801c580e542c0107600d1032400c01160240c032019465010400c44007131803501e40c400c0944d200080c0c42c550300a0185030a0606180c5941c0400f0385404245800a208007082a1900c47c00c1c0d60485a00c110045120402403812100901c02d6410000b0300d2461100041070740901c0102640c182d0307118000c080c0340c8030070380304d0160041141110000114440c440002d003c550302e47d0002d04000344500d0451b6a8a403203d410304060704e60982001c0005420310f03056224502d010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 409425017 1250 409423767 409423771
    0x120c05060c1f090f021315260a050607050f0f03041202010b121c0311072f09011214100203160504031505280b0a090b03070e06040b0a1d 60
    0xb24100b082880c00542c0d0300020011108000303485540000e00c06031032003100b03812400030310020080f000704694540c003200c0507010388610319020160030060303040c00d214030005003600742e150048010a1a40e075101400c51342a40001109640d01d9000e000340c2e124100888003543c0114030030120500e40c07845c85c02c0000d0855100c03140ba980314030800041d1001840c0d01060340c1d070f10345d90030348c1600c03211107056242a0003401c408800c803401c1480010b070203018440001e0b0020903940480d0390001c8016050502441034000c40c000e100c0d031005001d80104601c45c6502e451a410701e200381408000c5010300211182820354075800540f0858000040200d501e5000407450a403e0403801c2503403c0500307640303640c000c04000c0c0e140401410744e0350001c62004e00751aaa60f0204140034500d072154003051011003000350108125081c000c555425020032100b1b118062104071203005002000910303c0d1103c079000d808070180010341c00c00d980d205c0000c581e8542e0303803a800280c40e2004c030785440d074907024008044c0300d140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 409426267 1250 409425017 409425073
    0x70f02090a090c090e070e1302010f05040602070b1e070f0c050303280c2a210609020103060b0c010213060f0f0806031203010e0a0507090609120c05060c 67
    0x290a04550008801c001c4550548852020000301000201961841c2c046c0c160000d40c2d882d100002001540400401203000c0c0d503200b82d07104040403280707101c180d606008500400c809070f0040813052001c4460304001d005040740320b030084456450003200c0e64001c0d03030109106684000030f0200b09003c3c03000c0210401d005160550007186003140c0c802c3c524610312001d001c602e41d07001140600d440c68510030300c82c121900d82c00c030010046d020300c42e0780019400b407442c0e120091340c1f4102c000b00269040c00306800300181e030101400c03094140019902d4200170301d0200f8040303060654915020401592030b00282c008500b200700016500c100c22100b003401c009081c2d00160400040381d10541c06a503014141da00034640c50304081c1110748a10f00001d062201c0c100340f11120741d4000c800000c9000d84c0b14106070180c1040c0c5c0e0b0400054444ca0300880d0309030309174080d05000c030782443c03400c100c850035400c4208800d90054039010705180d1940009030440c1d000307400381c000aa1080640c1181900e000310080e8126017 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 409427517 1250 409426267 409426271
    0xc171b0a1208010f05010c0203010f051906091404260d0903090806040c030b0a090506040c090b03061611012309060f041203020702030102070b0906091204030b0c0304030507050102070f02090a 84
    0x7144c01c244001c00030560007420304002003650701d442152000d401c0302d41d042034110343c2484140381000095000301d09494a0040b10340c10304a00240c40c00c1c652080f40102103080050903142c1e96592503000601c3c0403801d4007580da88552000c03016040c1c444c00540708080041c03401141c0ea55542c1001807030304a05421800c081e030003010500000560124086003140c0e40701c0105012540d820000d24010181e03244007500901a10080100b006015448101074403028041004440c019000f410341c1c640c1c0444102c4045600d0104940241c0c0c0500c003803003d59410180007142d0500c0c02c445c958008589080c6800c001c0807920706101e00c001c828007940e903004e05d0540165000d450306413200714010044403e0703042403642c0011801c0643d1020b40484401c03c2e0000210202c030b00300a442c00b40d44100031140c80c1003501803c0e440f50483e040b50002c40302107903003062070700e8080c2d116502c0a100e41c0d44040c0049042c0b18042007150001042030010700340c07007401107040d015405014018090305001c02031192081034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 409428767 1250 409427517 409427519
    0x110a03050a17160c0c030b010e0f0a02030f31080a021e0c10030207062307170420090108100c050408030d1a1203071a070c171b0a120801 60
    0xb0007000345000303a800242c42c0c22051440e007400c00030005d104a03013000c2d0094031320300004102c01001041c014003440f01800c00c4181b5594034044a000c07400180c0c1d0a10482e010b0380e002c1603101285400b10b20005c240300c10450641166500b00c0b201010107000110f440c482d000c0740c0700c41071640610204001d00b00450080c9803520116001c6521868809641441181e4800d003001076140f29606988805500640801c07001b40030320541040460b504048401050381c80000406080c8211283c004c9001c10610012242c1c9441c2c0c0c2d4000203110804520030000c1c4030800c070038629034586481600030425000a00130312901c0031504020385203030440c80010b12000f04820820400000202d036202100507400040070b90b403144000000b05000b01d9a250312040855541020020100c000c1883e64400c80200c1400d40f9a41c01800030b21208640c4c07a03001c643c00004400c04110301c514100c0210349114011841c00008441010b4608040d001c201150761100d0900d000308642460880c0e0303200d4844c03c004042d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 409430017 1250 409428767 409428781
    0x1d070b0403030311090d03050705010c050a0c0f021206180115050901180b060a1824080c0d020703110c01080103111e04090302010b1e1c03110a03050a17 67
    0x248201c0c0300040c2019940c508814443d08120240d4400400081951240040500b0f009010303811502003650706501c0c140300d511001c0d000318107c43da010080c1d101e514066619454034044403082c81c0050740c020303840346004c110f1100184901d5220b106601848403154518102071802c544032580251000f002c0d0303103018070840c1c0d00c40c48001e0440c2c40301c4541c07030701c3e01d10607411803800b038050101003a402110105962400d83e401179203004002501d81c9014000d03650742c0c502204030454070401c400a0140e03086030003e280b441000c103164855040c80080346490007801a140890380050015000500301c0e04a81a0008003030004507410003003403a04402550468548800c034648004c0c02502c00c124941c402d03200a605080b2002c0c1100c001442009001000e0031b01034041c1c043d12091a2052110385030b080800d809020550042001c044c08a070b0215009091120300c418580c40141c0c01e00c00c4400c0e02074000c20080090048541c441e6032000c2c1c6494501d500035003403040d42078109075a00400c0c3c08102c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 409431267 1250 409430017 409430039
    0x50301020301170f0a1112011805060a0c020102030c04050d0302070e09010c0801090510060e150c0d0e010f0f120204051c02030f0f120918010b0309070e0112060509030f0d1d07 77
    0x228407022035480c001c0000088107d0300401400c12040d0310403200c0d0002c64103210002c40c0140c4144c05041e0b0910075410101c50032401c074481154980e004200a20080c0039134204410052a0103200f401125801a192a0400314902084800030090b039142d4080800b25507001c1c2001d40184006c040a10840c200078515195a200901a000c2080b4000e507101286650701550390700341c254188215580d07140d0128281e900d8003040c2c180d00010603c040546905548905c070944502142566075010700e11070404125202c09010400001283c2c0030310000c01c1c0c40e59258041e02884240c2001400445118814541003400c164040800c6401c0000785041aa10100343c0169001d01002c81c0c90351244903000047c164404d000040e429171038003600204100c1c1d00c0c040218001c0c5018411035600c1507583d015460298401d0107a28411310001c1400b8000a02035000709411182d42c10030f90703081c00c04108070b91810740c0005d0214901e1545039110440a0701c1c0c030171520301420001c400603082c020300302008a41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 409432517 1250 409431267 409431293
    0x9050c1918020406050742110c03030f31020901060305090307020f1305010806010303090906062a061a150f03041704031b0510030b03060105120304050301020301170f0a 74
    0x2180391f02e02c615407046041a11000b02c3c0003401080111030b83c049200b0352162403080c941c0205052841c0c03054205002180c0c0e4143d9003000d002000943c55a03807054440c88000318003801d0641c508046c1180301e458203490000e13030294846140e4480c00f05000c50300405c070f02e130b80060703002c001454076007001d0040307a207808001c861040344c0550350311015072040c034003080e01c03002002d0070001500e02e46400451040000700320030b0b049074042d9980030206a19039a0310000c440d40c40c03054401081c1101a1080640b1070b02ca6200c03c2204c400c41115400340c026158081079416103c050040352202d16140303582490110312030141a030201901500b058855009003009200c0580040c3c4a002c000d05c200e007600d14500100e801455111020600d00e000110851581885a0062610a44d10000c00e40799591007403246140d1201c00500074142070340781c0400e110b0115034020080303a040c0801c100105954909000560090500c5c8012036000f04c03010300094200341c054038174100341e0f401c6031148001080d0038101301e003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 409433767 1250 409432517 409432523
    0xd06140f1509061f0c0602071202100209010e04091e03030e0d050c060a0203130c06020714010201090b04020f0307270c1704020f0a0306181e0f0609050c19180204060507 74
    0x13809003040002900e20712801e0b030008112a00004900342000490746421a07007040316000c0f01c4d51040303100045001e07405803100590014030007180a000d18941034001050407402107551605002c1d0700c2e40340c1907840c54001000c0d00843d498070a40b5400040801c4120178001c2d05103041410300038055046500ca200182941e62490303004004101400403035040c8600729a80300c0c0d0035488140d92880c0280d1078082c0f0780318046090f00840b00c6190194010700034103003019400380302c044850303582e0307400c1251015801041c1c030380600c1200350202c0c007190b41c0a190100d402a0200383c5442d55040c100400c180c130408180c400400510041e98161005890312680d001541102c100b14004038a5010803986c1c043c2d1385c03019010724184946007400343d04000c7c0380641e9a0003048459403150400401d01542c103954603005003050b200d8170004021400e15400341054a101e1000c2d20369642c80d800c002520110780c812100d856011001c03080056040400d030700144510403100560a192400c3c40c041c083e40141c03400a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 409435017 1250 409433767 409433809
    0x50c060a111c060e0105060c0d080406020f16121707030e010f0603030f08010905010b1c0b120609011a21100507030f110304110d06140f150906 63
    0x2455010741c049003502c1120800d40d12901005140320b001002610340e5120341d8400e10700590001c035282c00e00200715402c04402d8002400c400841030811654428020016036059078240402d56201d5445c0000b8101c120b102041000d601109003050b1211200d038004ca8014441e040390036241d454036408003148d0100c4281800120042d1141c031841c0584100c120390f601d5a0f24102005c010107030800011b00e5400810354900c2020fa0b00c0b40620b108560081c0034484140100313200019410f4001100502043c40c500f50100f605080f29011404010f041c403180c1c00141c004400300031012009200d50240000104000c417080303104070700821440040c0c00808101300200341c200741410f0004121b800c3c0e10501002080001c0d10381004020014a861601c40200318200b0a070b0fa01108480e40c1a00e000350f4200f52002c4180d0f08440c1002000c40c42c4000807245c062303ca04240440ba00c040c80c20f11b200b000c2c0d24a04800c00d25200050000310700448002e43c0c410320303402c0240031198075811074440b000340d106202 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 409436267 1250 409435017 409435031
    0x10f02101506091d1314010603060e010507030b03030301050d0204060509010933060c0f1538060721050315030f0718060506030408041a030705090409030309051615050c060a 76
    0x1102401b0b05004d145080340f50b00706040041001902d9000803176119103000200440d1321961004c405407080401103961580c010300060250b4034080e090400380610051000030b245030b5900204822040c01da00c6160351300c0d40c804044140e41c1302005502a1003e03501d1b0000302d1020040c4e100d01403480d250141e18100703c01c00003d4420407419000b5030f1907068101c60724040080c1318840040150850310495a04070001d0301c1c02c0c2e20b0a0a410320500910744202d005520161020b100717125158100c2541981c01150b0145002c118042c202c0048100046c143c1d603807541c0c0c1c500b81c0951030204032840005802a80100a1041070b082c0114811040c2d94000720040144030503040200042c00c4030f900310300d80c00180081444100070900307000340101c1c1d1504001e01c171040081404541e850008517071600c00f040e400c02604c611442c080c2c0c0003049a41c0700e03050014070840280c45544c80d0421302805038445140d000420310070409640606041a13090780340551800e0b00c1204041e84904000e0251a00c25032140d00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 409437517 1250 409436267 409436273
    0xb0408030723060a0509120408060c0309120c03040e010b0f030a050901060f06120509010204061202090a12060e01050c0c101812050a1418010f02101506091d13 70
    0x30341c2c009101c000c03000b282c941d030401c07507402c000503e006c0d150114a841a0a05030311080b4622003507034100c55005014012a0762010a08043c03580000c0014201340a0301d480c0d018484228000303480b41041e0280210f0700e99040c14016124400f040e00001d107011001c1c40501c01c0f101500040720360110700194085076548603040e00a01401694201d8404180c44440110350554025400c1e2100000d1400038813940e240d401400c0c0c200c0c4207a0040800040f203204c1303955400701060300200000d000c05000e040031955902010818964100401c0300d140340c0328040007148031000d009143e00107400a0750b05186c000d0f407415055517a0508020702e00c4c507944400580c80150000049074007062341040703502031a065442c2000300540e110061507004203103609881c400038114001503071701e414540300740424158583c1c40107496400498401c03004501c9107d00200100ca014050488280d5500003001c50890410a000e05490100e40090400a070b003081d007090010140001140c010003000607070303002001641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 409438767 1250 409437517 409437563
    0x5060a0b2218020a03050a05040f080a05130902180406150c02040e010c030b13050606040e0c09040c0e0411030f01090b031c021005010501050306030709150503190204060b04080307 79
    0x282c0700c84015412090300c8041c0010070380040c50700c40e1541c0d0341001983d8036004084200ca03c140c5015041451414108000071130315401040440c04508080b070078219410110310681547c0e0b01320302c01d5203801241030200c08a20041030348290404984c00d00c4101c8c100f0603058040d90100d04000304001c00d4507120700664a07681e2040e0b03445a6008020b00140c02d10240c05401341c03c0c02a402c03400b500d41201050035003583d5106c0c5901508004140620741403404118003002e40c4040c0010029800800c4000c900395118415000301114070740b60102a00f000b0b50410080300c0c00c1000b2240c1000301001000020000184480d054404100c40050303040070445c00300380f60203884c44805c1540d100302410800140d0b0000303680d03048031008010520040c0e132104011550740c00165401c0c0d4050740141000d00c08082190055040000c00130744100c0b54582d20b20000c2d180c41c4148181b01c00004401c00710782d040d41018011300c0042d0010440c035500d8140307403560803592441844070107848007100f001040341e415244c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 409440017 1250 409438767 409438769
    0x92e060801050408070c120c060c02040f0515090a0b010c080a031503060e10020f090d11060a0c0b07090828141b1e040e0a2405060a0b22 60
    0x1100200003d15162074076100d00c2d44138190513140080003400010313000070380e2140301c40c145d5884079280c07121610300501919158000b400807070340107132104051160746100384142441010300091139400420b14105101200c2d00140400303800c1c5040130301001142c0d030480850003030154410440b5235a2918200103c0040400702031290800e143c0c03000001c140b00c81c60304001c1044020700165808c0105012604080303104080c90701c001c1344401d020420051901954681c078090042800640705416031001504a038810034040d000300d2482c280b480248040700c951503500600c5420070301607860400c992150340f20b8840415030f0204402c82841c0700304000010313403541c0903076011054403410301c00c0d60040d503280c40c560000b41e440041407800303070310280c646089034600a50183c8032501c4a004042e042c04043c10045907010230398403030268141c0c0090000000c046420624449414000301c1c90300540c0c050303406c042c16141c4283c61007982844000d80c003c1c11508000450507a61070711070310b07000441c40d5244407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 409441267 1250 409440017 409440029
    0x18121303080301150e190b0702041508010c08090d1e0e0d030908011a011209080421031704050d0e0f040c020714060f03060603040f080406090608092e06 67
    0x404000090900040d0b4001003c1c01003d071142d01e141c171051001d200080010001c0010640d551213001c00141c8040c10081503040d0007d04041071103030104240d8035500230700d0b900c601e09907035403000310100207680084d00382d0308480060058000c5101002000301036404000190042c91801660f0f0001e160240c840700c10f00c1840680104082c172251304020303107410094850b14041d942001e101070001c1e00007001d12807011405071190408a02c00310602e0000300704014003201e09090401000c41e40c0c3e210644942840081450b00b4100704449160080180317252072400000d4845d01030074000058808118103010248510b0007540111a01001800c90004178512030b80291506859449169010a00000b0382d59a440d1442e62141c400c82800f40ea4410580c5103031400c8014808282141f4000d4001c2d40c01c24018005405900050f0b221441180c0c001e034050300c00b103109050100000c94021030354a51041c8000d026216a924280004150300400181c1001160b018100310301190250340c080c0e0003810fa = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 409442517 1250 409441267 409441283
    0x90c0405070203131d2214030d02031f0807060509010509012d1b020a05040b040222210b0a0e030c030c010605041a0d080d110315010818121303 63
    0x160b184000c4c502c110f03800d0300050b01c0d11007079800540c2c0820000c0c10310001b07140000340c04407105001d880f1480d08110009000c42c0500040184200b841e049002450181885d042546e080e003080341c946801d240c5882d80002540d0b08890002c00c0345940001c2038408903002070800d25603801e400303001214900c00a00f007245580c001030007000366032070345034030341d50b200c10a151180c500da0110f1640c43c1c8014040381400a50042d58204244024105a000f505100c00c0150015081c240c4070a824030400c280c040e04c0d02c522901074941003200c2000745180700503649031403083d985100c010345c555015800c00101020203050701e0702c000c000d8080d4108111104034804101b900d850300c84190031507000c1e1540e03200301842103007014502d0041c00b6820004a0030700b131008201411804070303a44d54103456041101c075140500d0b601c0080e01c0c2c050381003400a510032070010594034524206480054078083c8007410041e0351041054050440d24070008016886240c1d800c0c0060b111083e01864400007001600000c01b220 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 409443767 1250 409442517 409442519
    0x203090a14010e0d0e060a050c0f030403050a05160620070e0a150b03061f030209041a100801050603191508010b1002030708031308070611180306090c040507020313 72
    0x86010f40c8080c03100300e02c50041d201000744441e822a4255019600c030755020340c00f0800c01c0400b40c0114014040080c014050701c0001c180360002e00c0c2907810a600c15141070300070510620070484107000014048215000c01c0803c2411710000500145d403c0c1c0c0071031000300e500314001c0c0c2c03500e504200d41001400124403101c4245407032070118000d89144422194402e0480001060095510b010350340f0900c0d01404150600f6001801c600b4a00004281311003450b9007048000001e480b11301a0390410051803101084010502c828466900b40c4180d8480030042c2c4c2a0050010b6981da008403a08030203ca605111180740c13581e07501c00103201c068003241c1c002d102200001108201034003c1c81400340e04984040407515800030a0740c03284075011005201c12020000a0802030010740c02c501414055444981092096a219822281503c100320820b45c0b000c42c828851140300e052a40303411304207402500319070610423903880c2c1d2007043e100000d00c101e0300d600024070003904c204152203600364880380c035020315 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 409445017 1250 409443767 409443803
    0x1180e010216030e131406010507031e03050403080f060a030308061c110f0603090706030c0e030a1104060515070f0609080f0309100513030e03071a0c1e100203090a 72
    0x80450600480d0182c0c990000c1d5502c8450648100c1d0800c1b141d003001c510301995030340011240785c1d00048088041c05803a2254501c0880f0414183c605081e0070345000465040c2070802400a40303004140c03102d45004001040607685070091550f080385d5250410308010703142d0300d00081800c2c0c26840c0700809102c9200078582448148121180580000d039030303100100e000841032080e684000c0310384602e44d5100900810400b4443e90040300348400914090005c1e062010009091803032140007a41d013800c160200034454542803290800030314040380c0040410001c0c00380c0a6a40c001d4050103080c641c00c85000780144809a001801840e070700c0482c4d00e940d07411820a07010ba54005481d0200a032040c241d8195000205228041c000c5114040103244844c03c0e07941100e046000d400c00d19054081c0560005902c0d6141004c2c000101300b40407410b86814842402034034080c00c010f0840112011078041c1030110501040d00e00c04503100c2c400250780c0313a0b240c2c1059450803580303080042c601c951410440c010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 409446267 1250 409445017 409445027
    0x130f0c05090a0f05011719140f1501140d020c0a050304030b070804020906040b030c03010e01450512070804050f090108070501030c09030609110a060801180e01021603 73
    0xa00c072000caa000e40b04a40701c000c0c542c440c40641c0515404a01c44035038544100040d030300c0f4543d02c541c0320030700e0f903a200294a40c00400d85101c413101c100390781603140c10310190780b1185440503805910364010340151040000004e065410f41001c200c0c2c8030380002248250b14a0300c1d0102da004109103400c441f40c3c01ca403454a503903258024071003512148081c60116280c40d00c03454030304e40a240c00810b40c141c00d03102c0303004000050075144640780d418402c502043ca10354500f8010140c035140500000034000310300c8100102d0780c0c0700c40d50310945a41c0c801003103010035200f00d5503108149010500d05002c41d0b045d03864158940316040b0154501d11300007007419010081504018010b0b02c80c2500c00f0021200c5078018880101000e0041e07600580060340140000d5100b030b030240c1c156120034030701000c2c600d03640d4546100312a2108401d03030307004240320a1007002c0c0c20000b2203180103081e1460107054561410700c81c040f00070041c8001d2038960361552580c00a209094064502d408000455580909a2454081c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 409447517 1250 409446267 409446277
    0x1203130c050901030b1e010501120216020d0c0602010c03020c030403061d03070c0513090b01050402160c0f0305060609010e0f07090308030f0109060609080a081e07061a040c0e130f0c05 81
    0x1040d11b64580003515000e19a5082904130344041e15240b042800d9150014060b410002402c58400707800380078400540c0c3d0323034614004000e0081018902044c100315009094810440181c0141401000f8040b40090000201c808884c1c10200016580000c0c6814640c10318500d50640c140b8071021850301706000c0200603030700854001f03c550484001c0140001000d42d4040c0b5000303451089000010401c03400c0c180c000300950864614608102117180d41c683c0380080503608032510306003078803900f801002401c0000c0c9030041c1c0129000348956150090000300c6250007480108000110030100c1d44090040014001840d405020b06442c1d2400343c0c07030194000d0091041050490410400082907030091f01490b00780c50384000603114080441d00d07410740d1940b00c210051484501e04110701a4038203040b000d4610300e44202e0340415190003591281d001d942800382e071180324510f003000c480d04481e00076410755074218040c3c40c80d270100114080808010121008825543c5081110503408242d020740181 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 409448767 1250 409447517 409447531
    0x170709082407030510050604140427080702130204030b070e06031b0f0412030f110606010903020f01170117010f27050c180f091203130c050901030b 65
    0x1041c65030285640d0307240c000a50300e0800340450070700120386039910a4011035131100d11007038030402d0f49581b103011407107a5000e43d00804400c5581103440c0280d2809014410f18010341180c1415a50242c2c4001141540c81150041071502e001a11808544803108401d00510341e48804540761135503410088058501200d00358000740c002e99801200c0d242c404241e038000d014500c13400c0607500000d101f01c02580d2000c881e805111300144030000301130b0810340800d6040c502c20782c0c4018941c0c1240b40c010b0030b205200c4030001060f810039401c01ca81079034010209002c0760307011115040051074400050341d4980c0c010b0b16036584030f0041000850502c41c4841c000000c0211a0001c10810110f040c003142210311100f0100f030030608950301016442204460008818080c0d01900c802007201800250340d07222501c0c51040125003541003103030802203120045d51103803120029004e000c0c0108030b000101d00c03000740040108000450003200380490004a00c02800018108441650716410114213102c011103800c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 409450017 1250 409448767 409448773
    0x1c0906112b0807031103160c0b0c040f0b09060f0304080c1e0f0309030a0f0213051501030606050306031e010f05091005071704120e060d0c0305090102070c0902090117070908 76
    0x220f41041e20a10801007519085403d40e400c585405051052641c150114001003101d1040300b000401c1030054031900480b041885503039210325241c214030b01c00c0c034103a10050660390240840c0440c3d860707600448000360b014514241e5682d0303552402000302e0041d4041d00c400e41c8100e00c800a10f03680d0186000743c07905492021507074a000700b4021a566885076482d8030744c25800c00a180700016944416030501584020308503151684c4601040b0b00301d400846002003241e401e4803455220703503014030545c400b804076807400900c1d41c030b0208007090f9a001c0701041e0003213041000b41d0b030042d8000700f03510140c2c01e00c03070081c41170100d42450010340f6940c003c103c031400a003038034003000f007201140100402c846085014013542e01c0d0340c1e0b807900c03a00000599000d03e541404501c00803d0a2580c54400800c02c101c81c0c0701000079800710702c1c0e00040449400a1240c869a80304001d0280800e0769403151400311204a1800342e568000300c40102c84074440c00c04c10301800020b4800340310f059600310350800282d88900c022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 409451267 1250 409450017 409450021
    0x318140c0901332028030509120c180613020c0d03020a02031326190f06060f061e030501140120031b1c0906112b08 51
    0x2c00b059510005101c0c4003043d4121412006808220700c90900c0408282010000ca51650b00c3c0c0040c1a20040c44c0442075400900c0c02c000c0203d10403003003407403480341050340000704010350f83d002c0c00c0d0f0312031800d285204604100b4070030200741040121000180001d4411010712400d00700005102c14250b499a1103808010f030b01d0f401e155010700c05d9800c2c106008000b0714031a06c4481c8260001c0d0700c4003004c5000c50104100b17544031584618181c0004043e403d48102c4020800002d11151004e2048101c00c141c210304508401180c040015520b40c68000c10119903191491800c4401000356030b008500310191004000360031a0010400c2c10441460703400c603da003a007400300c114202c4000340103c58928202c4018000207500c04e0810111003016520101c034210010740b60781745141c005000242c0140ba0058040d003914006016003404c803005041e0701b40d804800e045001d0544c001c1030140e54104a4001c2c51840c42c9082000f00751030380000c1c0c0100c2204140108007480404800703107007000101da13000b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 409452517 1250 409451267 409451279
    0x30e0703140709051308030402011202040510050d0506010e1012020c0d081006050307091a090a090e071202030706110313030f120c170a0e1f2d0318140c0901 69
    0x170155031516807040c202403941c0d5481c2c1c0152003407424030100c04107896003070001046580310b0901001c100151502c4d51616440d42d80054020f54800800c214104080c0070380001c41a200c00390b81041411044c201403240c08810054440203006007034083d0420321a4107944c21095070480d4516014100140414410a450704010384151106940c068009842c00c0c000b000501c0d407001d400c20401c0700144602d440c00a10200142207148250071203c8810f079221441074111004201d04401425107440d10140d04d942c2d0b80020345c85803818419002030100441a40905400c04d00450722042d001006c4601e00c1c944a081200685450003811181008541e0640c01c02e24007420442c5e078201c2e80f0190340303c40148807004407507054110328080800c1c404021054825076641d1180078002c00b9a41d5151480c5d50386081c4001c0c6003012600704000e06482485212540d40540010700003810145e003400b00704140d144105440031091000090070b0101103e0303810060920201e030003281c04200b01e410481d0399880341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 409453767 1250 409452517 409452541
    0x18290405060705090a0506030405010f0f0606020330130312052214011a2106040b04022e2a061a04020f0d0f0b060a030e070314070905 59
    0x1990103000c0d98420030000b24141c1c0700f240201884d54000d0410802a03135154041441ca4000b0f075012101d03139468020b192040348691080504034143c0001c1403080c03034604140a512442030b4006102840b505151901e8240c84c05d01500d4a1032148400b1504585003100503004281a102d0303080700013a010080350600c01285001d03883c02001c0820405500c54510000c1080842d0070398800c039869076404c4001d40c001e030028410100d100e104400c0701d44d030000100d0304115582c1000d0340701e02e1084030450076002201c00002070199016520204485030794440e0f0000172001c00090030002808009002917158100ba00c00c11021101965100e80c2412100c140c1100c0d40c007040401820300c609201010140440c10319000181a01e13030894107415030048420104080e83d11480d030f06103d00f4000125401249698407a402c00c80c03240000c01c000d448003d1000071341521170340c80c00300105601c1c0d07900d20b65020000c2c8410700055910014080b0303888005034200392550403a108801400c0d2400001860f154181 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 409455017 1250 409453767 409453771
    0x12030703120b1008060907030e0d020304030c08060408071e02090a0f0506120606151b0d090b0f04050609060d0507030b0315061003020a021c020106141909020a031829 73
    0x154503150016071700c58090142c5580c004200000305925032150801091051282c45412112079024658031030035410407032000d8069501c480c159502403401c002c0858a4141a41d80603a40000320b205007035400d4014411810303010303601035404404c15090203a41c01c0554040b00d0200030b40c1e0818481e5964000420002541400740e6841030b80020001030f40070300d0211071051300c44858815842c00c02203010b05004495440391001e400d035a202c40e820a030500d41081b11803004100f1086107600e84800304500c44803a026900c500d90240c03502203003840c072503555441034a6130004403c2c0104568034200e0b400030007a00e500302d08a07011303000f101051070200880b16205840b1700d00c0a0050003d020ba0004110000d40c0403413046000c41c01201c0340c065080049803004009000b4a40c0040703150340c140082800343e128106080c510908013a1451480106005503041c11200385880040e02c813403110304150044c10103280005401020100c0d0701c07003002044140045514442d900108080300c041d84907280031034003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 409456267 1250 409455017 409455049
    0x62102090310320601020f0601080a0f03051c0f0e0d0206190603020901030302010e060105040b0d0201080408040f091a0910030f110a030303020a030506011b02040b12030703120b 78
    0x40580d000e002c1c100c454100c2d800c3c141c3c469002000341070074a00c6031440b14200e800e900140e00d05031000d03c50103682c10414140c202c001c20000d400390b0351414102030340c0c0e2104032100900484212030454245801081074807a0610507404100403c4101c81100f0f00604140e0800f82103d13143c82c00c0424030041c0040d04c51580c007507507001040343e6110780105140d00d40c0642c1558100790348036100400141c490407060390080d8400d8001107001c1d00d000180c3c5081c0601604002d01580c9044100e081599401034018422038081c00c0992041e141c0d4106078140c6d1285030071012488035000d030000b0310011940c0c450701e00c5800b000c81044000200340e04001400030242c0307001c01507400900084c00803c00901900790700c2441451001c011801240100312080c9855000750003180d40481c2c0c410905070503004166100c41c091921030340c4455003512400d41100c08900203070040340d580440315469121450000021802801200c0e110611490300410710781c4122007080000d03040038410140c0781403032201400b034110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 409457517 1250 409456267 409456273
    0xa0312020102070614010501021f09021008070314060603040318081b03060115080c0a111c02010b010e01090b0a0201151401021009020603040605040218010f050a0b0304110114040b040621020903 85
    0x7170701d84141c05003005240700301c140c60f2f98042c50300042c0e07906c61896040e080d0320f8480132600c0c903000002508480410440348040801002005650b1355014110795000368942420008010b04c600320030301c466160b0300105224860841d40403c0c2d0039150b004603400e03840403821214641e88603424107400c42d611015050200d000c0c5004110011986005400750720303500e203880e00b904a000a5050701d050b407668120000781720b512244d140304a50a02032100c000d2028200402d9048084000070601c2c061445270740c0314000d02240350107240c0d100f03401c4000d41c070040e220505099502e42070b403080802031203816140944122032030740350400801e008541c8650b03001455182950340d175071520009400001c00403640300a1505429941c68040b00803035000e040d4010031101c1c01818201800003450f42c5401001c0ca00c2c005004000004808100e00710300d082d000e1030311b4501d180508448a6190142d9080720400c0718001c100414043d0380102983c15207080c0d0200d40305200584800b0f8001c81c4200c13580c00c1d400d50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 409458767 1250 409457517 409457533
    0x8070509070f0c05060f04150504030c080903010914010222060504060e210a02100201022d090604080d030c1b02010f0504091404290103110a031202010207061401050102 74
    0x2038040d4810784405842c80c107064442414030f40e542030404600302c0c1c0038512404814188400e2203c0100c4841c400307040c140d410001410301780c03070241c00c48034081c5008010600018100e4810b850a4110f580080d6100181c00110b00311a480307030703000c0d400100741041007100340309010034000210481c4108076081030300c841e03240c079051a8080f5840900a50002d40202e001c80b100002c4600010307800072708088030b1019024240175031040280c2a0900a400021a030043c00f03800d416501281000b541211224030103c03248104001030041d6000d000040d9a0000000c10001a041000300f4004d004c40c40d10b0342e080140002c200420744400d058a8010000035050003140c1d801540190611089030b00c4504001d81000d80d20070100080d111101c210000c0148032200b407000300701d2165002d1500c400e070002c41c0322070040714200980c40b0440500c0040c00006841c004080b89032241c14140e80555080580480c0c0b5445114019000c0e60003044100c2d80c03680791900e00c0c002d0200d40042c05043e268164090312040e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 409460017 1250 409458767 409458781
    0xa020417031209120d200301090f110f1c0906091211031e0d0605030d09030203120906072604030c06020606030604030f0c14012d0203040c0501050a0e0d1b08070509 72
    0x10215200c2c040c190046c0c10401e20350410316000618000e242c040703400309180400301154410796070b802020b182103050900851a06490b10004d840c071103894105d1302844c100c400140c240180418041c003030704a914203101181408a00e600d01d03e01948140c40d9580320056a980712580c030300c0f903242d02170b01c4503943c0302c105030003200c0c0000107008030f003121400450455141c10000381400f1f0140104804150181c90820031810180658103d078082052b0060500b1001004510340b407107041c0d0010600d60102080c070040d4204803101c4802c0748610100e407074a9640b2850555001c50150103608054420000014070364940000c1a5124542c5913607510140078140b102940d904d008080c04503076008040f810424018000d1151111224a07180c441000b480032021008106052200c01c00036507004104100120744078850100803107200f0310b0443c4c0d481019140407200c141c3c4440c0c2c2c60360b0100c0c841104c1170174801080b0094900f82c5030f643d0301d10709065840701035035039030740a901c00c81c0e8006080c10006010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 409461267 1250 409460017 409460021
    0xa0b0601030e0601081b0a230316030503120c0307020703120c080721050f0f0304021203030f1807060801051005190c1104090510050a020417031209120d 67
    0x60040c10081400e65500d0107407030038038600760414401540401c01a04c001031100924641600050b80c2c2c0044250421014100d2101c1802200042d100d03000528000c640301045000c640500200c0c0141003180c80740740c581d4695001c04001c10380c15003134a0102d0300100101c0116400fa102c0d0f42c00030700d43d141ca942c4c1d0321000016007072240001d00070810101d1002c10075401c02000c0c81c03071007254090040e502402140e4880100a0400703001c0140902c004078600700070104484951106040b480d880303030b44600c00651980c44404512299004c04024800141d19690b0507034000c3d0b88420060761840c400040c0c80b40d440219204820000d4882c1004010900384a850405005400c2c50070f2483c080e800503d0b041c513030806880704400208440c0082003800005004c110074142c045174103011030303203094480a594406003100d1000f266680c00101d030345040d4543c101c400400001409880c0d407504d41103003503182e400210760000c0701d22407000010310640b00400c802c440d45010179002401e00b0008122000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 409462517 1250 409461267 409461271
    0x10c09361806060e01150e1c0305091e0604260118031103040b0a0f020c090702010c170103020a1211150a03150e07030c090b0304062a020a0b 62
    0x20404152904000003500350303014101001c5070460740355480720744038600340c81103035003560010241342c841e800140445046c1050480c1841034030301c1c1134082c05c1140c80c000780a00c900c050002440d41e48403454001003507080000381c20010801c944000182800100410301c10160103620b036440b200800084c803440c0d1591442c20381c1d50a841d048d550903202401010703030844c0d412403800c844181e85208410100341e81300c1a40c103400000a00594100703480c000209503030340200710f90300007400340c1c0b200d0120309244200504079403014010f1000340daa08088402034000e08050f40048000b4803040e081d03c51101c01d16031158100e82d4043c00751f801c41840c2480c181002c4002400444443d4aa070070f80c1e00756540d50402000d00d040f0481c184030303940c03001040040d0803540180340425103c030850342c0811901d005090b49544c40541c40c00d0204525154100c1121030440316040500d142d00084240401d00045900c40c0c840c1404020001044507010400208041c0c1c0d48582e910060707000c0103900c00000c0785520116 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 409463767 1250 409462517 409462589
    0xe0309100513030605060a06050a12090201020c10080115020312150d051f0c02011505090c0d1506090501050c060703020723011509090b010509040c1a0705010c09 71
    0x42e00340b4569403581e071440b41081d4026982c2c80c0c1c840d4207224203807501010200c01001d05080c03803850001c1240002c4e244220141034200c01da6521340c0c00c002564003d120704241e40400034450600410518005050715a0071f00520340301c1507280c004003c40034000021520180340c104030350000d80e591045103141c0801e804d05a6600031540300c01c1a400a0340800c00d808108803013111b100c001c4008140a201103c3d0f0040000b011603040886007400460038103420000e80380309440b04940d550310b1440b00070003071099409180140d0b00c0c020941c0c41242c401c50312841601c10945c2d031444a6540c400044540d40501241c14005410003404540c04500a90040000c14400d4914003030028000499104520700e12684810300c0c2d440341903004d01560341000a50207054840c404100c008459180d900310080c05004440c010071400c00403600788502c0081100007820440320ba603524841e4410b00070390541222008550030740c01c021910f03d40c14051080142516180500c680280904411921420003001c0d121 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 409465017 1250 409463767 409463777
    0x405030304260a0503030106020c04060e0601030e0f030a030e160602031207021603030201020a030621020d06060f080d0909110306041e020d0914030705191719030f0e030910 76
    0x100d540b0460070f00196400e60b00800103141c8940c5000342c081d040c00300d410702442c440d42c50070700c090000b2080c400300c86801c0f020a1900041400048000d20b281c500a40b03003025840c8008078640c480141c0c1500b1508480a402017680d200402c11a0a03000c803c3ca14000c4070096041400200707038108a400f1503d2384407038907104581c0321032401c2800304018001d9403c1500181d40001d81c94101d25054000c1200a04031104042d42a0340d8020312220100100314000b403160207061800e13000e003c116082b2102904010480d160b13283d540d010a20758030300c40c00d0f088c640400e038560b4000940004512403a42c80380b100c21241451035480804120082c6514034100b80c800391001405104034140784060582145035100000d1600e00500305075000302c12035103c0300001c1d442000710800040c0cac08540300303142040090694145404600d0300d4aa9002c2e21030901407480c0d800315110602d511508456022000192000c02500034080080810380350038001c0744110340d108110740d980e00c0c10700300d41c030403103661035454a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 409466267 1250 409465017 409465079
    0x9010f02120307051801020a050309010302130f1d0903030f04080d0e060c03070e03031305010809030c010c0203071101080f0123090c040306050606070f02190e07020703170405030304 80
    0x41c90a05402c103460750f030009000420041c0d00c1201e051520644204d007400103090241003944c030150790b4880c0715003032410182c022540031006012000d080014008100005001c4c5464000c400100580001031205000110b00880c020800100c1224000c0c0d99190040d001550345845e81c680b164031801d000300c021603035020804000707102801303008e006603240704003550f80303042c86000240310582c13058034244a504104440e001146d961004107089070028248007aaa5079003107280f80c1036002e00040d1032061350034800d5500f513156000c002020104d214941c11403200030f20740c0045800410403140c15850b5040c0c00014081d17012031480c59055071b5035505034200c054400a01141103004143d07441069200c0105080c003c02143e8050180d1040080c1d030086d04000058032204000d590b9190045e0041c0020314100b142800404c5403c80903020b000402c994a09102c14001d60751201ca10066030301700407a816032010510140e04a4003240c0c401001513050a0400c600502504149001c0c500c0075004001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 409467517 1250 409466267 409466293
    0x3021803010504030908120a0516061413020a0906030503030a1a030f07030b090316120e09040f0b010602010204140405061f020a0b010e0714030a06181e05040809010f02 74
    0x482c0d2149109944501072603251030351861500381d002c1019500b40e04107101c0d9841c12980801a58a81031a4140041001c0c1d01c034100680100020603440c0b0000e0800b0080200c0140649000034042e4820b49000303e0300d80d40c03000c40104855550000900a40040001c20642c3e00c043c0c100082280b240d01c801c0d1103088080340001d14180b0480200001c1ea000703110108140010780d440d2030703400142900618a0481c40f028017600c2000c01c03480c001c0c1510084c07805802207900c20071040c0440d030006451388140b4206404d05503481904020101c82c00d690701800410503034418000c0d5421142143d22006090000b041000041d01e0018802c68201c00e51000041c0100642028003050301d9594000e800b440710f2500302600c0381c0205801030070051404800b40001c1581c0150031400c20700c42194419101c0e120011908040d084036400007003010311008100c00300741103650080205010100600c6440340c05100b02c002031f940200c901901144050214615550003041c8a0343c8441e21403040e1400d1683d661 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 409468767 1250 409467517 409467521
    0x3110f0406060c0b16090317040902030a0504140a0201020d110309060f0306180402010504050120010c0302090301061a040506090d1e0c060c0b160c1401151d06010302180301 76
    0x290149002031001c0842c0018062026031085e080f880840d03c540c01c031050310102a00b540f00c1c0f840000d041213290110403070b85003d00c10654014100b4400150f503a4101112140041c007000e60701503846440c1640041000c1c1c1d800a004040986c0c1a0041d01c080e024990061342c0c24003584942c00c00600007000000520b560384401003030001c00c80d014154490030b0440c1480002914510810180e4400c0414400981c2c0c000050301c0468500340384c154041d510544072074014840902015403e503090060341c502094040c1c020384050001503008110060341c03010618680550508031140d0150204801d21a60400074000c01962a0141c0380300100441030fa80c5048551400c410380010131781000c03e810403c203140c80c100b0300501051a140152407480c0c0c0300c5000000b409064540462105c034601c003c80c84c01020705c402460740018400301106842c42c035042c06000c0d1120300130101109800302007450702c254080c440b010013841c10418000c2e0360f8600150029404007100d0f122030f0040441c446000e5a0034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 409470017 1250 409468767 409468769
    0x1e06030209041805060a181106070c08011503060509030f04090c02010e06010e01260d0e0102010e12030a06090603080403060c090306020f0c1e030706092a080f0a0c03110f0406 77
    0xa072000300380603d000c121030401c070f410780c147ea8240106030901d280003142c03a80d45c011201440440341c1076514840c0b403a200014655640c0190515400c00e603c000f21503103554601c0086901800c02886541e803200d8070700e5280d1040d040c00d110f00d030406001c03d0141001c01d07402184050381034000098121669078a091500009912184c4400000401404604100241218001603a070700255104a0007600c0c42d03240c1d01400078071010080452900701850b031003508040030049102e03064809a0a11503c681c410341d00440f1408485810444001440c004d07901c51001200d822141d4941424210750f1240f014002d5900c02c003040040d059004400b040203072004210390a48550300507644e580c071254141c14090000e41324150181c14a0703840404540104c100c40100c0d500c00303800103c00c166880d25401c1c02c1c0c1603500d05840c1c219041c00401c00b0108a44ca6481505c00e140121410680c486002c603944d40301c601001460044000010070003d090360194118000c0c0042c50405072085080c0428100c501c0c2d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 409471267 1250 409470017 409470023
    0x80313050102131d0106200c0616030810120314090303270306010302090c0741070303120c1e180902030c0f03090a0506041b1e060302090418 62
    0x300c3d003006144004a4040d44440641400926070340c5415400380540308941e00c0220005402541401284010300140040800c001e00712500d6003014a10b048000301c07140400c5011421450101d88203613400e002c084101d031961006040c0c140381a41d005c030b074800700a480c1c12440320020b00072082d61340d03418005010100701c150741c28589010719420003ea101c0c660342541f4080e802490040c00941c88410041d984050300e0003100f5940c0405150400171105102c2c1d1100418100c02414440744104024282141090340c1c0c4981040714403c2040703440c0c4001340300090200e600b20800424a0429410400d40514641840c0240a010041d00d083e40b03500c4900710b10018051030980242c01503507041ca14003804048404500750719003401020312521407140d5161042c00c0c0480041d14100040011480b11580b10f01070b1880786c1000d10300005422802c0040444403040c2c3e00000c074000ca80c80003420725401395000850748842c03815009a00a41c800f80f000d50b0011f484041e10707420540c824071080141e40c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 409472517 1250 409471267 409471297
    0x7050702130c0e04150b0417070501020d0203030619031b03140a0309090b060915030108060a110a0c0206040503070e0603060a09030c11040f09051e030412080313050102 74
    0x12441008100c120550070610118680788480300c210340e02040c1040d000701d040c0c80c0005e9441d800450b1918240003940021007507280000c01040e1184140b032517203900703800c00049403000c585540041e6107800f5586010001039005200103036840c90a0b01e030b080d1002c14525a8144119269168032010b03c40c0c0d41d07400705140321a048100308010b503648482c0042c86820b0098450a8525940100b65801c18804d40c109107459243c01e20081d81e0f803000b1503813890002080c40582d4007070a4480503047d0024422425503019150000c1c40b80700e424042c04c18240c1240d0342840c40d14080e090705449141d8101810390300501c0074040401d00d51002c21841c0003600a2105114840c9085010585403240c010400e448480c10007a81d0340000c0d40200b010229540d01c000a41c4e00744e004000801d00820740c1d081034101d0242880da40d941030080c041129500c1c48600b031090582d403101507485e41d40c0c0344a50720500e040c5c50382d00c41c12000031400030b1700a5508161b445810003192002a151a42a600403203d510310b941 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 409473767 1250 409472517 409472527
    0x6040b060403061b140a0302030a1104060f030b04020a0e040207060e1b0a05100c030f0315060804020108070804150e030d090308011d040b01150507060609051b1204030c05070e0705 79
    0xd0141a01c4c803140c04001e1414040ca11040071110409001700e82a1009150300070010601484d02034004194482d00c09500607102c590b0f07008014650b4000c0140b00002c2032400401410740d0816000301e64541526484419403234034041c00388002540130320029105240e40d0b041600e4004014446918040504824543d1000440d010051405102c3e88071520503d407004444040c160030104035001c00350142041074600c0c60f00d1800781c0103049241d200841821070704001080064005450a010314002c1c0d8840382c1c950713598036043e0740104054030b01829101220300800240e151503041020075000c0d403000d680c18880c2d00f0818405a60310210210082605040144152074100c8540c0c0c2c2c5049a0a40c55401401e040d22131550b4400103000d09522070f620341c45500315107806481219a083e0384440c082195695030010007005000a46481c0c600045480f5249509600c0b542074559481400c1100e00d10f030f4407070350303030a40318071300308400803219400b45200c006213010f51085103a1080d0a1602d80c0c039910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 409475017 1250 409473767 409473791
    0x120c06110904060806060d2901060201020a09290a0507080c030301050f09040b0a050705041e05040606020102040b03190605030d0507060c2c01140d0608010b0619050306040b06040306 80
    0x280360103401c07044c101d42c030084c1040031a036a500f5501e1980307900a03844d07502800494020b02c401c03040200306401c50f204820000140658150f0051400b19501d07919980b00c56241c000c14001046100c009040034282c1c41066040000000001c2100c00fa85080c01490300c0c0d4503540350704098000c100380c15580d03007010004210074180409079858541d021100303400301e440c1580c0d4003080d282010b0b081000903691a400602014080c00849010346190107000c20010040e04071000039603514016035001d40d0030494006604c2d4014000e80d002d0310300c14400241503a41d000c00301d011609000400403c5c46855036030002d00c1ea2004d200408981e816541c40075552000341c1003110030340b2100321300402001201e14124034240300e60700e184104011080d891045104042004807203501004c000c0420341180047c2d1039542c0142d0360301c0007085404000080c49550f21900820965004516210700203100400009122510580045a01c50002400082c800d0400c00115156400a0f04110380c866510580c3d9040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 409476267 1250 409475017 409475021
    0x5011407050a05030408034c080d0e040f0e0f0d1806030b031609150806071e1106010f030218070e010c080d1b080702010e0a120c06110904 61
    0x11014031410000d01d0582100b400800511008001418042020021441c0c6020060006800203070008800c010040000d1022682801c0080d00c182c02c0710703500a42061225030309000004581003600038202c14400c5400c19500d0040499503564880d6840700071f0111032102d0320940d00310184c0d20340102800c0041d80304080c03030941d005414000b441103c0d0700802d00c80c4000100682a074403030380703000701d42480c0038004646801c40003901c1c090103502d4480082a020910392242c40b0030500a40e40c0511251350705006610307404142c8074940018103100f481081088400000003040041b45000e900020b0030007079450804400f0381020001082010042041d031801d408030005c80c00d0300c06920701c1ea50500300d60190000d0b01c0c7c00300c900d040c080c00e01004000d208442c5d060b5103070501001014490094101c034002c0340444102551b80114200002080c0381038414802c84801002401c000e0401c0f6100b9100d4500a2010b125002c00708051030a0940c00203240703005114109001d10502d80d11240d8002c20002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 409477517 1250 409476267 409476271
    0xa0305010303270303110a200a0605090d0f050a05030a081b1c0f0207081803190f0f0c1d01050a14010c060b0f0901030b07021603020d1209050d050114 66
    0x701d007090945005620f6015800780d00c0407a541410003401440b01941c2640c140071003070070302608103060164006004000720390040c2d81c81030115043c0d0781c0a46c8403481681e1a009403a2541d070070000c4180c510f40080c1048a00c4d001c81c50140e01110b82c010b00c2a6280ca00c0c5502191340380000030407103018040001488906a000405001c01c0c1c3c0d0b00744508900b104480078290742504205a4072030130320718100c114660444280941109645a84881c001d0480c4805003000004074040c2c450b030380c040340711890300080340855a50301070341c4241c00d0801601c462912501720502030b00c4034141c4500010f0b0b05190003c0820780000b03400d82c03c0b0115854081049582962944441c002407100a800d049031380e030107584404001d41c0034100164421000c03000c1109881080d0b5042c1c0c20151500000c03040c081050310892082e209179003100c0d1251b2130017a810707070740c0c1c29035200080d00400403440c140d001600356030720303118844a14501151410740c0c81c000200d40403054441503c2d56552584031100c2084207840c02d50f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 409478767 1250 409477517 409477547
    0x1060e07090e0f07120e060609101a030a0f02070302060910151e05221503150b0409060612021305060105030c0a09050303030106030608010513050318010e060a0305010303 75
    0x40d5540707002c980c400c900d0001450002e10070299000219082e000300349100110303009031010020644041c5020382d5440060703403124403410007180001e400840940c0d4180c1035a05e04484508000381e40d4404120942001e1701006070551110444002d1000c10702c05000805c0c045d42c010011410420642803c1101204d488010350f8141104c00241c111800000320446501103c6111a0544a00c0740e611919040e00482d9002e0940f0310401001c5031407440e5102440d54456040000c8034604010305014046480014040444d02000c8001040d0540c032a4081440143c408129641c03503580300000c0383c5090b0000300c0e2090350711118030300707505040c203140940711001e810030000e03400c0120010b40381d8007006241413031103200095000c04080c400c1c030071300004004c040e007140d8580d40c40d100081c0141c59a401860003d618060009148140441040b4800380d0400051441c110302c40312100c1c0308040c1e218a16050101813540054a0b440383d00081c040f40100d41d600043d0340d41140f5006140d842d00342c00348 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 409480017 1250 409478767 409478777
    0x15060a120611071a150f12030409020d0606021002070506070f050d060603020315030102040e0c03090a0c09020322021809010e0714010813030806012006070e04110a0c060905030f0c01060e07 83
    0x1400b100d480d1746c000e05078414001c660240703108140359549459841560044400d0070300200d8040708481003500a801512469002d031000743c0005ca128030103d018064025240ba80308401242c0704c030340202d407611039805251030410b14050306002d011059903615403244000aa0000801840740040728161101075011002903180500d840300130940e00202800c0c01120041c00001301d20384600030050001c849610814115090341c0c1c4414900c0290802c40f050600d40d417801100003102a40080700000c829070041c04041c401880149039610240000c101d071039199601c4000c9441c5800c10800d40b001007480320b10680c00088148001080d0100141071134864000c0700c1090700c0002d030845020340d80b000080c0b800e8062002e104507008800c000700362401c0360038018003080c44100355000301290680f11080d00d082c454030007070346c000d40304c036110341c0303403480001260603640c140080e950381c11044056005038112410002910941c06441c1c4c0004000750703807a9911003081151064120110341d020102c1d0901c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 409481267 1250 409480017 409480051
    0x507300c030224041101051b0a0201080105120615030c0d0c051e03100f02041215060806070207061805091017071a0c1c0903030215060a120611071a 65
    0x180e08050f014000410503070140e18844096407040e01038800490000f1607140c041c1c400070001d9506c2d90314952046e40080d1940002290900304000b05030801070040d8000c1c540d40d0384407000303081c01c0048a42495410300503c810b0380002c0e1303a5449400e0f001c5015201d00030a161a01041154200541c21402e403072540c0588610015540403a1011258039001c0001c00c808415000000007403065403c0074200c0405c01915005020120034030041500f04034204000d0191240d9960b69241c00450300c001c01a44030f20008d2142d1442060038030050703e82c000d50480d00ca51a03800246400c0002c581c2c0d03905007840702d01c04000300941407403546c1d42d850269003e03140c0c850410b40c1510350135805190741c4d010050300240e00f60a41d4010000e50203540d100c0844034100c030101100c000c0881c122840180c0040c840c4580221801d80c47c00ca03194000d0781d0041827440004e20f8079554002807210035205031000340e6130b01110991303a180c1c031008000c1c0c1440f030074842c504607006074990010310201900814103101c90f000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 409482517 1250 409481267 409481323
    0x40e1501140307030b130203090f1507050a09080304060c02100503010302010203040e0c0c0a03020105090c010e090112140708161203080402092a090f0108070507300c0302 75
    0x1d101e070700315000c0c4006160349548481c02074000c0c0c158102c0e4290001c41301030000075098901d0f4040e40c09150410300307a510080c441420303607543c2c081c940000c1d01c800c10081d01007907482d80900010082c2001e0b1f0304003d49451f90303a54445046401c1a0f0203103022510f00c8500070b0451400e0300000f04450407a0034194119415a00004e40e00c1c010303401000b1008079102c0c0400e1f5240140310030b0368440d055002c100c650312441440c000b806481c0a440e00050b91003035080c840d5881d80507041c100c0c03d1840140c85094107030700c1c3c44562078008000035000c1d6000917082601044110302031000c139019128001c010810320302000340101248501b0341c88000f542d00805280f200281d400b031060b94115170112402100b60302c90440c07445c2c0307892003d5002004103852400720742d600400d00f800352146060486d4420050003d00006540003035044880d031000440400c14080001d080210380d640045942d003040c5c03c0c408035103102080302d02210b81c1a801040c12102c1140c20180e0401441e0240304a080c40880966441301c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 409483767 1250 409482517 409482527
    0x501050c0c041107140a02040509070302180606070c0b0918090a06090c09060f0905100803070303050a140c03041202190314071b0f060e0a0312020a020303040605040e1501 75
    0x10080d80c0c410b648800951071800d11103000e40ea407607070304101811102c10004209039915410000100d02076400c01c0b0009400e03140100b610b004582c0c0107090040c9180641c1a64070141100900107544544c0c01e200304000300d40c5259110300a803803406c02e41c681c4c1e85442000c01a6000c33000042e10000d0403030f03400300103004402140c0008116440030780403580e103c503440c00140946942c0c1000f00c0481c9010000031714082c90385900790455090703090800403922480b2008000c01c4090040c00610380c81001000f0001e03100750f01050b80704e445d0010000d1010000300d00086003242c155050507400c0c03008011701c014007030114030103003812030079000404c070142c3c1480c560316203c00728840c05824400400d25280102810000300e6007c00d600c42d814981e03a07611418105170344080c5005011051030b04500c041550340c01005541d10440d801060511030b645556500051000c40784100400c50107001860070040e2000c0014001600703480c0c442c1038480741451600142602e000b0403c480c0c0101110902889176000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 409485017 1250 409483767 409483783
    0xf14090403091e08030a0f03063510020703030203090c0405090d140d11071b12120512070801050111060609011406130306020a091e091e0f06050a0501050c 68
    0x114540b03420a484110f10a10048160380440d80c6408001501007107103500003c1e10f0906a0b02d81c500b04030b0142c54180c1e00c58410130081038195100c000313401c0210070761855102c1400441c4c5200417580c129800788541801da80041f10121701194005c810310160920030310807140460001d8404002a25001d8a520740e12000038295500b031184841c181800e4601c1c03c1d049522036545080d0500580d0000303007a015032980901c4050301c4084107503030005542406884075108442d4500160351400c00c2c661283c8910401a411480a00404200080e00101503088441c07040d103641d1548082980f418002421010003003107040003540100b401c1140380d070764011a2905698140400d10641411640400c06a1187c0784000c248854080e10002c10000076030001d0a034032601d65912a592a80c3d4080050041c03101d110110507110100300601c200e03c3e441d4004030070728000c08030b90034141010b1031904003210f4076103120b4081c1c40c0e1a18803e12a90820464560003010f00303180444c6051103402a0b251240340c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 409486267 1250 409485017 409485029
    0x818030f150601021501080f07150203071709090f0f1e19060305030313061a0f1e040204092c03040608040320030c060c0a052b02040f1409040309 64
    0x7a0808501030380d02c02c003c181c1c8840a244001e615558445403065030725003000c2c20b08801c620504101045800d4856004482011a5001541448843d03a941000d600c8031280e410781d404070a100b6601780d641c0f5212841c3c0148100f1080440500f8548560f1544c900c0c01080e100f10380002000070001612801e00d131a038403140c101e0002c1036418030741d40341d00d002d0305059102402a21001c000d1250841004190411481c403810742080501c0d82011706e18000107504800503404a0f90811a07001c50074104207615140b03043d403812507c61080180014126006130f0022000103907580c04c9202420b0507000001c00d15107034825000c1c001409079042541da88150700500f410440c900011a0402d4010081042031208158400c0024003480495a9403030700003030345100051040704042241c3d2450035044500030f101a9403460310707001e030458051003011307202c9007403d43c0e0007036100b85a07440080c0381c030203040074000810051100310315003c0d070404003080c1d040030341d4031a030207071024400066003100641c022071b51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 409487517 1250 409486267 409486303
    0x306061b05011407050a170103030e0d050c04060902090306100b04030f0311150604050f10060513030c0602070e0c0301050a0e0a0906050a06080f0a081b03040b070818030f 75
    0x40c41e15007603015140c0341c0250b10b5034110708024042c190340c0140140040b4112681d42ca402000e6410f43d0808a03034080c44060b000c103409030849961420944c0e00790203464001c0d411210707000364041c0454200d91a5900076081990301003050340c940e18044c8007051304a00c29804030880300341018a030103094400d601c001004142031080b241c2c201406a69003140100541c000c0e140ca6400360004d10050005c210b803c1807083d86004001440484048645401005401c42c00c014441c11301a0a8800e9440035032840d9441405a1000000802c105640d40c082c103c03640c040d1107414505440e80310301c072402400031801007a090005202d42c1d141c0461160864000d14210100f41d00e40c4042d2200501811402a00c6541801c00b004032401541d0841c40480303110f0000ca555907040d80d004103840e02007510004000c690100b10440c1100880b507080003c3c0d507203001c00e4a240070354030403030089c80d98420041100c2182c0041a00c018000101003001a2440143c01030040c14030f0101125031110461400484814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 409488767 1250 409487517 409487567
    0x70303050a17060f01230f190804030f0e01090e090a0303050f01081c030605120619020c03070b15100e03010518060f07030e0a060509010b030a0201080c071506091a01030606 76
    0x603842100c84013042c0c000580b51b6558002480b40c81210f42d002d65000184204000410900b051041a20030f2046030580c6e034034030a01034101c030200d40001100541c603041200c900800300b090f080102c5140d005040d90340c000c240000d1907140c080c0517200c000388161610030740000108005c9002060400340c180c070f03051003c500380ca030301081600141aa40c1006420002c81401d120343c10b540002c0d942e000701203404070500250031008c0700100360702c114060a00c0980007404050b002441c046201c0d50484086265503030400524804182151003032141e80e0700041f41940c00d81c0382800d0a1080941021950201e0350301c608861020395690040a03028640a50003900042c449038401e9000d015091070341e41c181c80c0040510700301240503040c03e0350345201c2e5501c0c18544482c546000140f032000e5941c180c45a0142c1d41d0740d41c90140b116004410240d5244490082c810340b42641031041001414141345c0000e00c03010400c1c1c45415465881481314141480c08000b44100d03900034218101444450525102407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 409490017 1250 409488767 409488797
    0x3050f03090712060b0108061504170304120503070611040e0414010b3c0d0f05010902100c0302060703060303050904020915040e01170318040207080903070303050a17060f01 76
    0x903410394403030324000d0040d0f10070030b00f0010990410048a0002d0342c4803902915290100410284904c4046001003010441085910001002000700b081d42e0400e40c0e09080d920b40301601c2808941c170084030150030004040f8104041403044900b0300340c0304845141020b044c01101c01682e100604060141e06885042114005d825000b1815400d806070034990214001002040c20a044c2120045400d6030355102c01c501001e084114660748000070b0501062002a4a070801040d8904d001990035540740c007103c2016071a200100b440d81c03620340c3d548440030b01003414020300b0808042d01010405040c0602000400c0d030000c181d401050b402c490040c2e6650000000944e4a0300d00380c14002c0190b4046000160400d00c80c0c0194100c2d10102401c2203001110354180c0d407a407182c80c014818020301021007007a9030070240d010b0610507100302509407400d060500001d00e4180c0b25481140050800514541e10340c0d480400400c0354000b9406e00d1f0124240a800610060a1103106504110340c4440203840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 409491267 1250 409490017 409490023
    0x120b04061e0f140315060316060302130503030906071101021e0303040b010501080702151302031204050405130804090b040902030f070302010f0314040206070c0e070801031a01140909210c0d03060303050f0309 91
    0x9003042c108c08120166581d0000d0065001025203a1000601c0f8200089078200481112903d00c0c00400c3e5901d0211301ea82c0700a03004421103401e070304620590000d03a181290702202e280e145500c110040d51607207002d140071035012130142c001e241000001818455203e0300000c41004040078849004070790743d0790500020050071100c3c0f0180d458803a0002c203a8901c0d480350010300944206450030f200d19078031001030080c14246040c00034840401040108005400c0d80d200340603204000700301240c81d6a054000030b1400b503003250101c02c0c079003000008000310741c1c000b010904064000d0400f401044102242034615800040029008540010b804002c0000c226484009061845070b620001c2c140036800411501090004603140307031501d84051114100c45c00d400381202d581c1b4440440001014060245411014050760141c1c070030b52070a600400f081c48194819642d07030040d0a40c49041c80c4958524003210303001c1020900d4580070003400420351000c00c1354000e41038910b105540b900d036041e103645 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 409492517 1250 409491267 409491283
    0x140d0b0f0c192a0b040311030904060e0f011a0403020f0f060a180e0f010603200c010b010e0a0503031605070f06110616120b04061e0f1403150603 64
    0x45501e400b101c8035400e281d0000ba070582e5100c8841c00b0030505040e0007009a44203018400c3c081d00c2d041144d400500060701c1881c0c440200300062040d2030a00040d540402d0540741d4580107201c00300981d00070801b166854016013401090391019055000340c442d40150f5041c03040e400081c0c01740305040f5002a20f80c42e00440b540c100040a042c4507524400f598004166004240001101d14094070b80001c130004a80001c900074500f14020440c01d03403138040240d0060090700300c041f00c40203c0c12800c1030041782a41c003811824800c0b90006c12141400400100500c456488251051127840170500854070b001080c0c40322001e0300f480003504030480b41002c2d490400940e205c3d60120f94259000701c4d641e03600c40c02030070101100404649080d29026104800400c1c0c2509880000385e59611000c00120b4580005040b1040a0000100151181031076055081c4809807244041c1c224803041009040326580c1c40c0c0200016600b0b021010030f10f100080d1141c3c6000c002d005004a0800803c40b00d0350240300c0c0d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 409493767 1250 409492517 409492537
    0x31b0501090b01030b0414030f0a032a0206090f01110f1c05090c1806100807090812091005030c030426180f24070311060a0204140d0b0f0c 61
    0x100a43da0b5a10b080102d150046500b203c81200180160421000010030b40718140000090b66080400d4400110024507098103507030050040f44c200c003280c5c6002d001480359065a540d000d081185855a2050b10300210440c03211840d078035040141582d1000c0760161000441291245130f0391386080104602c41a40c082003211500c0d2428050005448000070b5401300c2d58401c0e5270205401c00c44014003004d06000316442c6800860703003103880d0541c622403080ca5034031005500b440140c00d0703200d4a8103032515070049041055004c00080146c07052a18031400482180381d841d0a03485c520b0301149071101d43c00b014200038464105c031030242c1c41c0e000380949542c80c8241c2002906848060f800b80c4034070f060882140b8640140341c51509030788a424220464411481e56141040502122250400e43c0b0b41c46603000b501040040c4400800c0361100b48020307400303812004405a245ca0412104400c00f844404546101c3d8201600b1900020300e0102025030060a201c43c07601d1507a40c814090b003c81c45000300e45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 409495017 1250 409493767 409493783
    0x1e0d1203050109050a0b0d06051b070f140303100e040203100e06070917150910060f081216030e1201060f090509060c091903050601030609061404031b050109 69
    0x100948561650015048405000381400f4907150703030141804441c0c6151406030817086d211064008110150080d0740c1080c00100e020041c035480142405090300115412034410350003400b00c0c0c003800300c4d401c0e001784409000b0000d14a54202a0980080f40441e84200340c000d121040002e425958140700407169901d46241c18012001c40710203294031013034102c0e60309000c91403802010800300c091811030130420319010001c0c01031400000100502c1200200344194a00c141c42c2440c0032401240500001808192040300400307040c04051800d0400c43c01000108520911001c266090001c03000c0d04a180c141c00c02a040800c0d01c00890385141c00788030741e40000e6092000c00559813900f241c45030100c83c0703034050802c02c685552600580318181510181d200ba001070003e03500074a40040000e5208400b001d076641ca155403a9130303650405000742c0c815070700307141d4400008052040c00d0244500c0c610154a4420961030f2035036000d04105608402000c3c40c6424600350001c0050940c0305001094000701070b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 409496267 1250 409495017 409495043
    0x130c1208030105010f0f090902070f080705030304050f060f040201050c10060f090e010e1e07090c0f030f2a0318051b22050604060e0711011a1e0d 64
    0x8140e510307074020310510b07001600420035120710b01d01c00c4040844001150340c8940216250880507406500801c0007501c12900710000000010500802008464424009542c6134074245c00e06900305030900062140c15081801000117880951a0f44c03903100350309083c289c4d201c0c409503030924078003614854030900701443c100d404a0301004204c2142e04880c00c1100511006444940180c00c2c2e52184c612003d0a42c411034a00740446c0c0d041c1d50190781c00010f502100c010a60b00ca0110040e10f14071007855001c9100f00710b0035880b980d8140104041350340b92030418042c54407140c20810302100046291840f04a25894210540340301c1c0d044002c1309402081030602420640c240603484040d5129280703a20984018620118100070001d0007502e540825100c040d031400b6074001003e00001403095500580d12100441d03401040440c041c0079403484da50b01c680c0c0c503080d4682d6608480000c852054403038120340707440d03c10b0740d13a02c001d544881c482c4000644015440340003041000c031090400400e51840380d41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 409497517 1250 409496267 409496273
    0x10f0f0506160f0c03050c0103021e09150a03020304020901090c0e130f0606080f010f0f12030306120605090c0a050f01051b0a03050a020d1b08070302150108100e0303060603130c12 79
    0xc4d0f0b54013640d0107201600d120303443c3e40d0010350403441145038100104110720f1050130000e805201400b48d404c00642107000c40100c040c8801d401d640844100c1e40420341c08000e02017507040c000911405484040810020200501c0d000341c440d0100031040c1d0700c00e001c2507888541c54030480e0403400e80c40a45076024041e16485034005401a182180c0f400d03852a4903100009010029181d14801c4465000c0b6041c65103040c80400c602120079420b0603000c2c1500ca038030005030000a08400a2101d00910f030000301420548450350804000c010410b01c241521501400183d4503040b00c1800c500c4242404c642d04d0039030060501c840c0b1089030401e600341c00345c080d9031020706802000821030340065a081d40c140600580007a509282c0f015201903054022104540000701d24100031300314580207004844c03d090080c2580c0351001c9090700301d01d8094100304c002c414180c1240c001e08a00324001c10145046203002e0011681c00d001c002c3c03444070207060f03100a003401d0124081150000d00b180e0b07079011a070300403581 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 409498767 1250 409497517 409497533
    0x12d2d060302041d06090c130b0a1d090405030306010c06110a031409070b0702090a0f090302010615320705010c08040314030723040b040905040506010f0f0506160f 72
    0x110030304a800780e008000041c5401180c204070705caa01c000f403c0041c1e90701d031900c002c003040e00960390402003520051000300703903d059000502080f24003a614040c00e0340c102100340484044280340c850060000e4401d0000191002c001c1d130764442c40a1916072814910703030503c68060103243d502400950302c0050100565a4103801580f00080d030400044041e898480805030369488620a00716595402d014003c01071500c00201381c2c1001c3c4900700070502d4055400030344111100c0319022000360395604020000382a907484619403141050034003c2180f00c20074000d9818580700c0119031001344d050358034449020000702c213072048150000020005031504800260405000380d9064012415146a000c0700541001c1140d10402c1f090f0307200700e051501c180c100301d2030721074641d01340340c14860034080420710050a501600040c5640314012400f81800d0421905162060f0410f02d500140101c0a00c60031800d145d6060840d0300c180e951596500b901586400070b40c0303a9001c01008012101d20b10001c0c44100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 409500017 1250 409498767 409498769
    0xb040801020a0801080a03090308090f120705120d0516060e1504021504061b02031f0207120302040803070f1b1710150302010305060d0218012d2d06030204 68
    0x54560f649140d0322403240c40e43d681c1c18090020001141e03030405100040c1d00002501c2c0c41c200280c07040b8150200d1000103040500f10a020340d115901588013049640340c41c11007014403400315009401000c1075000c000300244680525400320700c448644120400080c0d0b4080700c00c0200240c01e80e030007103005890062103d1000d440070b80c414102e0714088a540f0080c0005c44c1d0490311107840b05d841c1d643e900c0030200c2c200803944030181da1602885a06126408035002c00c0300c03409910b4500140d40d6065403a2250014540e1000f110070548144130500c00b00328004210342c0d2031500400070b0142d408031460000003101100c1c00e4080c0b10100380d50700013507100301d091183c1484118182a5154104403800003411641000900071408104141c1000994042e034843c0c0e410403000781098040810b1500407500c01c00e070070b80c004260703d255040100301c20001205a203881c901403000040c8003024a8880c00c8012006010311036850a45800311100d0899003202c070042c140d4020520840d2903039800c8050020f40017 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 409501267 1250 409500017 409500037
    0x4051204050d0308091e0303100501080717060a170a02091303170c13090b09090a0309170f060c0918040206040e1f0311130228142208030a0e10090b04080102 69
    0x2003401068542c083c001ccd00d44900c0d01a5941c00d2804d4607a2203101c4100c0d80030f006603070001c01060001c01c10a01c00756241e80c5030700c4088000e0401d0703142403040c05451a00180f014001000f548074107800280c4c490a400ba075401c4100305180c07a51601d0070b6580e003c0c80354049800c5900c650200004e1164007a0308000c0449404030f4400100344e40340001d027070715042c00110041c009800300da000d01807888000740c1d90450003c850105c6100c40070460109250140541d01e02e01c640601080e02d03880e03446c100c580c10035905201c04142c0b06509150340071035100d016501490b0f61888000c0006103210050700d10074034200007040010b00f50740c0c0c3e40381404070720400400b4985001d4694290380d8240c848240c0211120704198403c000000141c0740400000c3c11034400c4c0d1401002210301109451788680c2e00034108811092a60511100b4080840520204294000c0006800034804080030315000301c0e050706803510940301005000090541207518a0941d0040d028100020501040041c0150701130865a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 409502517 1250 409501267 409501291
    0xd050403200601090c080f06060d020f03040c08010c020f0d20030d091707050709020903120d050a0c08041101030c09050301150f120203071202180c0304051204050d0308091e0303 78
    0x20714070a044510580c211f404070031141480000c178129040960091604034228100182002c140f40d5014240c0e900030360f0141d8041d071050703d083c0280e20b8223220700401e03006180024803040e9280206151201031344c1001801b44054a00c00c5500000652341d2400b003520380d0819250f0307403449406d12500a0100b8802525602d040c000d160b00c440c2c5401c000ca6503015007000041c161685010418000b80d40a16100d5030540202c41c0d640003030160301009020141c509640100b003516100c01814100d818403c84401041948814030011a4a041c0a00c400140a28021400703c18040c010b40c1c107220994043d5030507618012064411a43c140b04182c20344241c60000b03201715564200018040c03440d00b0001e907042c1c0100c44104030203800b29811001c12032000c2c141119105204041e442403c03001c03274845007a81800420801046010f00000d601c4100701c0c2040da090030b05100120304003507a4070f1001001e102c003010100709100c00c10001c1600e0800c4071039800c1c00405105050949a81042d0345200a0351 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 409503767 1250 409502517 409502531
    0xa2c0109021306020d0e060309012d0c0810030b0403170a0c1403040803180f190201020d03060b0a0309020f06040f0e070201090816030c1a0106110a05030d05040320060109 75
    0xa1021501d46201726140c0d89000140325000208802981f000d00100030a642e950901e03481030009500d90100420084402c12001001c00141429a2900f00841003004035420810007011080307140c4200782c9802ca500b00926940340d00d01501d0202d40840c0821100d03c050082122410558209038181c00e113903901c407500750540c1801c03483e6900007503600510b884000d20004454000c2646404a0290014200da820503481c95940341002d9106d041d12109009002800c82996010066541560b45d286401c210441c50710360b0302c9040f030040346155010180c44090210540d40c40410029a200000303290603620b0703580310000c0e034401e40380348182410512042c0005a006006100303550200340c00c1142203241c0410085461150b4100080407000d11038281e4024021440d1240c0960740d03400098441c0c0c0244d41484406040213103a0050b01900f503010ba07254100160340407081d100b010708076440105042e2100d240c00c0c0c0c2c0b0a940c44190200ca07110001918080e2000041c80d2030480d0b1811404210071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 409505017 1250 409503767 409503779
    0xd0b0c04140f0d0803090a0f030801060305010b0304110603070909050c0903151e0c120403120608030406020a02101407030c030e040b030a0f2102010603020316050a2c01090213 77
    0x31101000308a603c0440480c942c0c01159443c80210391119544050710b40b0103004d0740d1029084020042c0030350002d082400140005a058031925000d01408d032145400d6141070303031300c010198001e06500d5024500101c08a00510f01501610700548030141e420b1045182282c282000ca400100342d8512038498000501003096803c2400f40c0220074450140d0400d450b0025004d400303a001a2071003a40380d0082240120714040c20f449140510320036a1350341808945c40003800150744080d042002190002c0001f044803a80000e030850709281c0c1030f42c0b14010104000010390f805075224564120340740c000110041055440b01010300141d2081c0c4407002c41d8000101808111022408003540541c0b040c59080045103090f140281400d124001800f0510f640000042942110444110140c0c4d100c00d028030031132a050118243c08540c1540c101045860b11001540a50076442489045180c8400c4052150004dc040007124641440c4426440d650f640c4018000d5001e80341b01c6810041d410404500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 409506267 1250 409505017 409505029
    0xb01060f05030114030703120e0306221b09020a020a170310060e041104060306030b010b0705030a12020f03010b0a03140105030d1d0306041208012907020d0b0c0414 72
    0x1031116941e803114216828001003143c002c4049428a03418440c110000001900d00804424110304e00d94518a9035441d44061500c0c3c9840034150a1b02002021407601c04681040103041e4100c0c0c02040100d0441e0402c00001d2002c4169000b84201600010700c160083ea00055480c0d1098811502c03102c6010308054141103038001914032142401c0161350410240d80f00f001d0000c56848000c00008100c08018480e091542c01a4015030210340c5484c01041809140184540101810701189103041d00c203503509522842109461010b0040e800848441400300f607041e52202042180350715640c0d41c458211b50200d420900300d0314002410f120030386c41c04d035046c2d8840c1c0d0304071038016004180124116005a8600641442900844420304a2140b86035400c06c5114042d50050580040c2c041450000030030304c480580200d00d055030000184107007a590650814203101034850110f0720b4011034030015040f5601144054079100d421000e006c64444144020402c4415601c41c509070f416040c014044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 409507517 1250 409506267 409506287
    0x812030f0112080a0e130603050c03070902030f1f0906061e110709050a020706020d0504290708041a1006020d0311030f0c0405030609060609011a09040c091a070b0106 73
    0x119003507013032003440e02450050303400c80180500204082c2c0d40300200903840045880c15071080c0c1c0c55901003500500d55003801d001441c094540a2419461071400707000c00611301c4c0018050f411702c403944400845a11128142d01800392680100c20300a01f552044000d210100c90010744042c40307840e9080d809003a000b500c420070300c00d400340040c048591620107060700401c0000d1045004039000c2040100150052004251020000000044500b0a402e000c030204075595a0804c400840b4000c1c80340045050307845a9108450f49806030040d503071840d000c2c00f543c55440c83c4445000b642e5043c4200003007199031444c2521919800c0b01d080218100701141512542144038000c45c80c104049400b85680901c591b6000f00d061186d1403420f60b403100424a0102c00301c07403002030b03a0000c80600c8414508041c1082c018010701542c1001e22034001c10303c0d00c60b4800c1d08a0548295622010030f031006000d0140500105030400e420401e00d821014440305036840310700d003151160f60281c00440c480e030041500d12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 409508767 1250 409507517 409507523
    0x30105010318150c021908040f0518130f0c060201090302060603031305120c0a03151a0603010902070609200301051608041b09021b06060f010206070e01090812030f0112 74
    0x100003c2e0740100060080014598503401c40c0a1407000503801500380c1d00a9040611030700c441c40da91031401b000c8011001d01904028851240e8068001403850901665904003055841a203240040c030724000c66500d01c201c800811310308850400285543e010360010050380d01a4090700c2d016038410f0105a100d2060b43c0d801c0510980003542400340b41481001740f400f0b020154101c070041584940000c01000301d0340c0c4100c80342d005441c018410001203008010b202c200704000000e080e2a0040041d1a41c0014040d1060041e4007040359400c3c8002030700840803c613040a02a40c2d01401c0c0c600403c948004070740c03140d0087d820900803604110a40001c072501b0703102c5589086083e1203c0e41c4651a5000841250a0a020034440031a0300d58040c4020a01e60012195515003052607258140c202000103000724400c0302c410101000c84d98011a0702030b8451400c2c039241001d00030440040e0380b07080d00d0b604600964425240000b001c03d44210046008980158003d43c10f80e030784014080c10403058030001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 409510017 1250 409508767 409508783
    0x13030609111008240f030f012705030703031107021305070314010312110a060606030f0b090712020309070b1606050f0c0924071518030e121e03030105010318 69
    0x325201d100904d080d000848000308051031012401000034540030040c00300c04240c0c0d549840c080503078500004041c1e04004007460707005840350240c80700c036106d0003451800340a243e1181c03a02a1071010000464083c107034000c0440751400d01c11350542006043c1141c135000401c4c5400f0602a100016140c0300e812203600544060445025100841c3c000c40103a403200e05500c203210ba0100094a1800381d400a400c0907030b4005604c40002680d1030036a40300701130050007007001c04207001685a100d00140e41940e40110056505d071034240701c244c074008580c1e1000e00080340c04a40c1c0c10540d4010054880c00034018207081c451500d0300400110030300d405072503001081030704202c002003900345001c2c1254050700001c29818000b00740041002d2a074007030741048074545c803031956100f00d803041d43c0700d900da820040001248002620b8ae03405000c80001d0030300244a0455505141d90030f8a040001e01c1142c28003051201320f4800c0301010300d0b80c0e80c00038081d0f00d0110341002c81d042c1d8080018410500515001518 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 409511267 1250 409510017 409510051
    0xc031407170a090f0b07111005010b0d0902012705181e09190506090d020309030c040902060f1605240c0a0207051903030305010806041713030609111008 67
    0x1500040a0211040f211000f84c0f20780da10110b01110460f500c242e1998441d200c901d200c0420850600c403d50301007907440c0d4548001442a105038800b40d0f0500400440c001605001500059814003490585180702015000d06034001d4500304c0007140c01c6500603292401104803000c0804028107040350032400c0c07010f004501c01c050049941070f043e0802e0086043d111103410b41080300d49112695002501d465004906101003d5400c02c000e10b80321040380301450a040918001a031940740c84203840d40314944508402c400c0d941c0380340c1140d0f50500d2020499a60340400c070311566040f05009001d445600540308043c0d0400003090304040d1101c0c0301030b1215401d60700c0c0c00500c03000fa0040183c000841c82161000304503a2a480f481150108c20050010301a91031854000c0580e80141c100d80c1e0b95401c18014030000403d149803401003070b0000f001c41d40c0c584c51280030300002280c250303101034100d60505218609122144220840c00403082d240c4408102e11900f0503105444141c480c036207100d1411203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 409512517 1250 409511267 409511281
    0x501020606060f0712120c03020304050609060702121e1204020102190305030a180c03110316080a020114121317070201080a0f0209130b03190812070306090c03140717 73
    0x1d03024180b0a250420b0017001d91124400c06c1150034003800d00c0080796002090106001040100d1540154101c0c0107080381e2810180084d01c80d141a032941440100228014101802c164680c0c030000c0766041c030254542c41d03074040e0030210010544050380903002d0114515107040c0b1500c0700701d48858060710381c580f03143c4451540078010b0071010312013610311120042c1200080c0510800b00d00941c05400c40c00340020811041605060048600f060004080c50b420421080c000c00c0c070300c030b1590302424002103000c1e002e02a00344910500300f10b0440d10104030308114980d40c480c0c1d00400700a01810f14440e403c40c0c00c00e0072004611070000044e0109845100043c8045415000a07004800c140380250070507822a01080010622075103440c1e805444400034070441c2005c1186c400a0715a0203c80306182500d611a9007141c42842110340b01e104440d000941c200c6d0003a00200020500000c08205001c040c090040051040b000006a2a1300503404500103610038040300c00311800c0a0300341c00f101d869a40b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 409513767 1250 409512517 409512533
    0x206160210090b0a0e0a0305060f040c120201020604080a09030c060c0c060e030309040e01061d010311040b0d120309080403051b040b06041e030f0b012c01060c0c05190501020606060f07 81
    0x12417141d00c26940d40c408400103d040c404075002d06000c02090507141000e00c0c0c03400340721619030401a600801015454050b0b03034002011504160403180c5281c1e6400181411103606110707400141403a4407014000030540e41c851f51003103200340112455182191181300c110f034040303045000643e26038003d0000c0380813440d0950014050b40b500c03070000078440c0d070341e10a14040310402580d042203401c0c0800c010020b02240c105000750710041210100840b0402c0000103241c2e294032603010707104100d601202c07070106000e80e201c554440d4200c100c0e280c030399540c2c5c0351241d078406d2040c050120303484503085075050720300302030140c0140e42e070b0010400c90401e4203091141c4003010460320718029540040200001194040404084844c003c0c10115035960410b0f509441c0a8000308410408000c545011011200c040b50703510f0564079586019100016a8241180d1030442c0b40c000341d9211207130745030107041150141d10300412900c00780c00741c4009580705810015030f0700074548010030164003000344e040010500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 409515017 1250 409513767 409513787
    0xc02240601020f060108070f1205070605070503120a1a0a0509060402131a19080411090601020a15020903010b031908090d150204091103062b0206160210090b0a 70
    0x103204903a80003c54000c0c051520100781c0c400d40c0c083d08001424010704c0071000518000d000c40014030040c0501030303503c240e0382d424144030719010440046094001c0000501c100d40408490b00c1700ba58041c100410100014001014003410085195507030700300303604007014800c04513030b0f0041040400390307140028400a5485403000e0020010000c0021400b1205074180c40d010308041d03c0b01c41d032682c1c0c400c08059000401c5503c1c08080c000c0c01400c010001e2404810b891054205803a60b00352034a41742c0042c0e16101070010000d282c0d00340d0507100c3c122020f49a02904220004074000d015910300c007018151184038030950900e84041014545010603407800080c6200740c0080c1c0f00e21102c0d56940c5504034202c0170403142030603141d00018108030002031070280050014110b0304051440c284403001030707032071107040c041c40c4465820480e840050054020300215100e40241c41c0c3c0b9a06c60b01040003042c3d842c1c031070600300e2103124030180d42d01606204440e00401e5690004689190981d00ca105940c01400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 409516267 1250 409515017 409515019
    0x60d020c070b03090d0815010309030905040c0e03010c0903020d0605040f0209010305010f05150f0f19180f050f010e0c0412080306010f030c12050406020904060602030a02010c022406 80
    0x20000880d04403010007940000703010745200300f40c0700c1c1080042c5a0030a08198240810000304405004015a800d081c0075603030030702400c000171600201d103815a1519000c0e40300c980d005207000151003080c1c4e0400e825140b0100203c000b0040c07110441802d5501c40d0342c03400042c0d0080b03462a040c0000030b0f49a480303582c0160041e01025080c041e203074005041c01e48240c100325a0340c3d4651582100720511030042c5a00007410142c0002c00d541100301245d68051740d8980305115014280c1ca108503034442124a0100003040740a440b003c64807404018020f80d0902072190a10b0310f0100c0c60300c55144503218150003120035803916503140c1d20700403081c0a295005007003041801410040003403058011009420418441d210703c0d500d919000b07001416890740c0105210601d030900d0a4500c2903903100321801009040580005603a03181e500700300000740641c107849500985050400314100c1c5e00000503116482503039000384840c00805c2012038507141d80c100c012a4019074041021071102c00c1c01202940110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 409517517 1250 409516267 409516271
    0xb03040c030c080d0905011e2303150f0603070903300909050f07020303190605060a02250317160f2003070b0f07170c01050106081311060d 61
    0x9180c0d20b03201c909001c2640668a581e1140c100c0c1004c00c1d4002070740702c0c0100000d080207000060700c20380c86000c200d9106828802c0003000c03c01160164161351200318500d800301d01c01138691809011009943c0850590244103030242c1c400c001a40c600302007100d100f60619650030340d180b851030f52050b0f40901a800e5030440c401e00d14002d00c0070f20762440303104500e69405d030392466000c40c82d1946060484402a1141014158000800c03640c1a00081201c1d0000d180507020340700d210401c0302c1c19004042d0b60b044158022000624011040d5000894194060039001881c0d85001d40c840300c0b0b80300441e04d21000301050410406064070000040150280c0c03001403040c4200400c030390307942002008001508444440f1840c9602c6c4a1f44402c02c80007230740d4201900103245007030505c11201d10030300604416041c0e06c600001d003502000f240302c01020000d050682580d4503800d00d58080d038043d04090080100040743c400004804244002d081e508094202045110130345249052151341d50098100804640d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 409518767 1250 409517517 409517519
    0x5060f130e0406020301210b070e04110c0631020603070903150501142b03020c0307060e130207030f080601030b060a0210140f011217040810061e0b03040c 68
    0x200c400001c661080c0d11603540140da030b42c107010052200c11480703152143c2c0c2100d82141000054014a00260400c0321814075543c9060060001000b60100803a201680140070442c2c4801d543d00042d403d0241400c600c4d03452017000080d0310f400100c241821a20801c414861450001d8240000116000a042d25290035820703225143c00c0307400400d240b41c010100c0d40d607200420500c0c512101000b604401200e00c01080c6e00300c1050a004400700000001c2445004882282058020031800355852000303010340d01c0d2142d681c000506074000000ca011b004150142c00401e44012501c2104c0d6503d50644804060409601c802c4980c0c0308002c2c100380c1410766400e446145507031584040c0c001c0036190b43c000d054008082c0030a0081d104101c15080b4458645800c2c80317a8054160b2a0a066421401441e08198650b00300030f8108440342c0c8586081d15000603000c140980003249032000007003a41000c0c0000d9a90324510000e903112214003841803401d09030140b2102821000654100380200802e108003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 409520017 1250 409518767 409518779
    0x90d050706060e15010915050d05090102070515040309060e1305092107052a01050705031303110f0a0f092c0a0201110718091a040b180705060f13 64
    0xd0000e035108813500c1d02d1007120142d1903038002e0f540c8000c3c0641012820020360b110703502900320b016582294000903160400180921000d41c181e51460390040304070340c144c00a4070b4800000c480300b61030035000034240c06004031b01c00d80142078079014454007502c000d49d94114040c81e00000c00014200010038020104200e10100d034181c400f802034846000596940c0c410340ca0701505c0e08010030002500c60007044002c490740d4545009a0035000320a0802d40ea4402d01880d0180c1503100b040c00a071940e461089002c818012a41e8103990902030540b400c0c4021604441001000d225900c1881642181141c0c103000003080794002c0221031250701050ba00c046c001c2c03180454100307070382e0f0b0210341c5035400194214259030f4401c01072401030b0140c0300600700b200e0400707004030703980c03882c8000e1480d070181c030b601e0322408215207000011540ca0558041c0813442c10b01d49044618180c043c1d803041013407a0a0409650140400f2444004a9000800182c80c2c40403100c3c6121460300484002034442440640c005a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 409521267 1250 409520017 409520039
    0x3040201110a03121401050303040504020a0c0b0405060403081e2202060d050604061502061b090405070c0b09012c030c0609010608012313140102040602010902030105060306090d05070606 82
    0x4403d100e0780700d0182011540354000c0442d00c1081c0345000910b1014010403281e00e011003103400b6244251005a51204644819581d007800c0c04c5009001c8665202000140310000c10b5041c0524401d5480150b20703203c044881401c1e141c84941101300c101c0d02c3c004a141c41a034105140e1509400359500b10034002b03d500050f12031b40040402d1840341e84c4810401002c1d28052040364043c3c08801b100e801d046e0302480d4025910f690080044681c144d00c01c0801d00302d02d00f210305490b42040300030018000c0b85068032008100c4041643c04440a0194501095a0001c18080e96000403000f400c00c2080c0c1c0b6204500303141e01d1725070f00c00e0600540000c009441c0307072400910485104100420010038186d00d0440440c2c05c40d0303044050011012440e40382020302075103510303020350000d810001101001c070b11400c2100a04e20800d40511480d031001a00088a03a0190031400d510b500807030080200323940d04002c0c1519100c08860f40000c0d9001080594030f1075004070b018058641c010f61002800d40c0c1c50700c41d1303400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 409522517 1250 409521267 409521283
    0x1234020601050f0904050307033e010c030e0a030e0d0c0e1006022a0a050301152c13080412080d0c021b060a020f070303030203041401140604020304020111 68
    0x1600040300501c441d0400c06694000f000c2d003610a07454038605030719402d80360300540900500f0401c403030058103525202400448814076200d440150b904420b044017659502a40324150703955420200680321041c024403c2e0400119400003410a8080c1c6580c211032120040300101d43c003a4451110001140b0340003074070301c0645002c42c0005141d04012100c00540c0059a114004541c00384070040c00410300e443c903c0007281028a4000d9844254031700203805005a03030066030301507180803215015444200c41c1d80c401c035854050001c00300d01202501c0b40301001d400da0f11404410b9140c0100d01c014800c80c0d5006100740c01494264102034a61500e850146501c410a841d0014003181a0516824610844000074280d0001b000c0b6680d0003062024207003c80c00903588100c03004105640014000d00400d003009203600240d800c01d40c0ca0385000780c029002503400303035100f03001c403152024880700520a01510034010940802e0302d41c0c0c3c0c20100406540020401c03410400c4001c0c5841c0201401c2003100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 409523767 1250 409522517 409522621
    0x3160503130305010207020a080309011d030a0b09100b0d0206040e0c04080114071d03070b1e0c0d0e0307180506040905100c030b03070605030615090a03050c040f0212 73
    0x941e686c29580100283c01c050b5400808d86600100322a94680e03800c07106682000c21503060201508204000181c201452000b000e0810089901008940800403641400407441003004100c00081e00040c84911008020020b400c82410030042c010703080d0410346280d000b03401011252034941c440e0003003825203082d00031861418010000b0300c4051500250f40c90513404003054003490401842000030364600003071081e0341211070000380500703040100c035a080140e003108000079541d4800d8612001c2c0e942c0c89034440080000c00040a00380c07146008035444044950108903c0c1c102e9000d071003c0001002c0182100e5030150391400f07040e0002d00d0070300081d1941242460005841c022049001d0107595078500124032039000b02109100c3c043d0000c0c16680c11070001d54400045442074502001548034100c525540020503103000401c0080018006134071001c15501444450350100300c0720b040c1d0060010414844001d5000101078114101a200181c00c0324130036a00d10654007844866040d580400740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 409525017 1250 409523767 409523771
    0x60803040308030a0c1103161b0e1803040303120e0a06060b0912010b010507060b030a0b040b07030e0304150c02010909050c1e0f09010c03030905061617090316050313030501 76
    0x101c1c1d000c00c00e21a14116200301c1c10b20405042c5030403100c981f80d1081080d219002000c40114105008041030820440e0004414101c0380a443d01c210f009910411508207010304028015001000c0c03001c07042e05d085987c140c44144443e030310310100c080038010035a45030f41c0600c101640b04000c82d40c0d40c0610001011080400d95a981100301030150940c1c607840b000102d0381c104000300302c840e42c7c01021500c2d1103421a40c00a062a07141c3d0000f0b0400c01c1880c000f40c03545001c90203010a220b840d0f5445030060380d40f030728204103428844221035164011481105450318280702d1b1820301d0b44c083d100c81c0100368414075041c216a9240e0300c0c1c4e07204580b0169410320040784080f8216031603082058241e0341e0340200c03a030038600304405503484021501c1001905810402540c1540741094020740142e1841c80c0d10009942c13107464041c4001c00b510403208940800514030100d10340c51801414402c038094030005001e14a03242891201c1820442408000c0794144410850110034098a500e40c50240d0310071000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 409526267 1250 409525017 409525021
    0xc1b21101a030d0906140901180f050924090a090c08011a01140403021207030639021c090504021b0c0901140f01090909030906090f0e04140106080304030803 69
    0x1803501e400072901d140402d001385140d05100300b903000200b5a49007894424490754411010004883d240e14481410324030358440c901c04150200d0150a400640c0c00030f4400488550b20401404960f95105481250803c181600c06030345003043c20341198400039030300b004901c1c14000da8078910684060b9100340d50701e0b551802049405405000103011001091130402c1c0c80000b11b0210380f110b441284402446606140340000b020f900c28001503000b0344d00940b080020010307401c0c01020010083c10085c0c8400c09440ea40030001d0518502c884050800703500900700011041c81103c03c1c9008202c00d58280001e20000240c0c543d00e0340010144c522118419840c030110103814189481c10300c0d841244528103103001444000d0420180c00100881100e503c415480c8400050b82d800020340c2045400754103100c4a80d0074940c10016000c106c40b45690b0350003c65030790b10500d04407a6a00e016005d51994140d0208001c20003a07592007940c04007003000003d11070750390524189141d00c40d6104a03001030380801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 409527517 1250 409526267 409526269
    0x50c1606090308010b120a0b010e030d0507150507050714010605030f0c0a090c02030a0309031707030212010e07121d0d0914010e0a0e0a090803010801020c1b21101a 72
    0x3c40c0d030041c03030304410041c1401c100500c4c403052220010802c1420700d40e10854548268821920304541c5000901038894941c40044001c0490340054000d0f01d60190710300e12200302480c2881507911400c000c2c3d03101810204980d4030740b02100003011034100c042d921040080b81507a400d12504000896020085c41d40d00800e03801e014200e000d5034031020f90a85020032a03074480d0740202c21111405181d180003c0d007a0141c0c07800795605113810f10385880f4075501c1700c00c0001d0160144c3c01401c1c9458518441c07813903aa40c1d901e4200c03812008503030a400242083c1034030300864055800070402e8050f4440384511403403025030720518121960f01258001018604200801c140819803512507810a02c0c01e100300e1a1100d010481c40e008511450716182103140000701e00600b5607000000069014000c0c56627540d5524000703000c0d4002d107414400c24020310000c1c41402c1039040e46903400902c080d14140740c290f19240b056040510201105095000364000320006075104d00c1450a1440c0d241c1c0014280683c00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 409528767 1250 409527517 409527527
    0x240e090303040c030206030a150b07020415031707080d11070312090308010b07051509030c10290111030c010c030c02031c020a050c10050a1104030c09050c16060903 72
    0x5001041190001c2082c4008502403074036490540ba015624180d407600c610700000c2c01020414040280003241500201d0800000d500400005000310703010300c02170f1007009000e06060f1991000404000581400240552103803014180305400b4040c0942400c618071034400559007005108400d030784001940c00b0415401654590780440c10190802072001305507005001100b043c0190b500080001c1441402c104040140c00308990719803444030311034203154002c00c0d0381c1d0300701c09a400004d020b284009010a801da10405204250207401c036280d05007520103102d5820350908115042180c90305407034090f014200300820302015540000030f06c0401d2600e0050440ea0012030140440d0400c0100240340301a40e0801400b110b043e510040ea5000ea406055a19116110300b200d654041d910540105ca84079500980c4100c10b204004d20103071903c101c0d50314a6202d54000180b0170b400c007a0b42803001c070080d9808180d200003220b0b407451030403d92480c2501d80b001c82800c1101d04a440320b0b044820140e00c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 409530017 1250 409528767 409528771
    0x90a050a0e031615090609230d140c070f06050301090b090702030a08220c0306060503010b031507021f021c05060102030a080405070e0711190312020a03240e 69
    0x101c000345040c0001c034400d104101c882c480c005014030b141440c0941c1c5044056004440290b4041c0c030800003c2c134241382940c2c6007462010b80d0500400e6400034401c0070302c00401c1d10701c81740515642d01051a03031030710500d031003a40164184001074403230404003042c680c0c84081c01002a00854a03000e40340c3d8034003244142503030340814645005e06001400e0180315900041503548030300090034502007555801e0120900301c803900c881d000007000201480014800c50340c2610090300c0c02070070280140b640382c0041c5402d80e802021050380640c0700c0700448001440c041113144c1c2003009441510310002028034101d810030703204c0c0b000d00000c81d400903e40c0c04a0029078955200158100b205005a2900c000040d440f03002e00c40d08070090001da0000a07040103014001c3e103020b004d00d0311403000b49083c50b440c024403807190f00990800c2c0307100c1c007207080e800307955002c0c0e008141e10381c1950b0b6001c00c80d04400c9a034010390860f400080c14036440e40520707411001400050380d0745100030000c503c101850192410100880 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 409531267 1250 409530017 409530041
    0x807050a0e06040b12030d0209030712020303070201080a1503120f030b0a1206021b0105040b07020609031813140603010b1509040506060f03010303021506013b090a050a 74
    0x401001001420140d01d1000c1d40300d041100c0c00186104440e0204d0b40300d906540c880f038610b000005003c004040903502070710122906400329240e068031010765240d126a810006980741c1d0090103880300540c851290303d0380c45a40e01070301090b801e000e190601d00701d20898000702d0f11610907484000c0082d5014805410644c85880e003840703041d403840040b0703800191500884e400340121061742010b00400e601114051090354107064440e20341d9800081c000c04007501c1c03c80d0240700c41e02c00f242605100003200f5000f0040381025524208140c9404045d0603007038a80d40d40c01032840d880da0012160940b09100106505849214192820008041c2110b4115210341d100e00d5203810403a490020000541d607840e50160b81c00609502c90000080c40b46c0105a10448240c4c0000b002004041e070200301c3c280c07140c3c2c50030392407402515424019560a2046054071207d0071300745205488006e0b614090010320416425070913400340340316002c98807083d030072202c00007141d4803031040c0500560148604000c21384 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 409532374 1107 409531267 409531279
    0x1106120f060a0f03120e120d08040302100c0c11010c0b040606060311090f241b0706050712050d06052205070813031b05030c030301080705 61
    0x300121507a0b80100c0e242c0307900007a2011202c0072241929400a070850b0510304994080751000380840c601580502c898041da95542410700c2403684c04801c43c1d45502d40c5141c14140a40b030400258800d4011524052401e08001d82c45010045c07a1a4807010320001c0e6210080100e401e041500c01c09041404280144020071915030300940450b03c46450a200710841c1c611f030b00400c2d000e24000b003030308120b80242009407481d2148420010301501c1495041c01340c13281e4002602600400e000b1103103a07030340c00050a074210081011400402040c0380c6103141c02c00f950b40b9003003000c0011881e0f07000e200c400714182503a0702068002d9005000042e005001e61100000440388103102980c1640140d440d14022030f0380c5d184103a04151207070301e03420740081c40c00d00713140d500300d4060441241a13400704454072907400019005000801340c0502e010000c680329414485020b042810950006110388 = true := by decide +kernel

theorem cover : BRFrame.Cov 409352517 409532374 := by
  have h0 := BRFrame.cov_init 409352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 409352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 409352517 ≤ n) (h2 : n < 409532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
