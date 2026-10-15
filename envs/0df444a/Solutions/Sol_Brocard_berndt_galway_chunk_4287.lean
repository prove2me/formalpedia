-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:49.220901+00:00
-- url     : https://prove2.me/submissions/72f7286d-ba61-4c65-8017-d4e69d2451ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 770863309 ≤ n < 771043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 770864559 1250 770863309 770863319
    0x209010909050312040218070503040b010b18041d1014070c0308040f1e0308040c0b160201030207050115080703110414072d090911090d0206071a10170d09 68
    0x4c006910600003404100d5021070501d421107100e0064968900243d4004100000e0089000200f07005010b242d43c003d25200c1d01111142d04500340c500c4651041d03032140d200c44d02c00c22500c0d007040c01c20701e5200207407038108041c0b40300100107028144a65070701e5651080010030380c0e03029a44e202d1405405451b154155030f100d42d142c241c045c182c118100d41c400d10905803001003030b420f50640c101c0c05209407500003143c01c02d81000b03c0040010703448100440001c100d0801c403614000903003c140360b030a0801607185c0f18645805e601514104d444210074485e81c10340011407141c00510102100d01a9640e15644450f60081c4004c0c0c404948914065501060204810612034204020207100c5210000c1c0100710349032003002c08003c5076010100060300071405208941c003501c181100301505003440352401d001e03000400e40c100700c0140040d1150b203010450000740464038205540c0c0c140048030041203442c090800c40d40c2d205031070144109442034131154807039620001800c100d145a1075240c6104c81c0b8600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 770865809 1250 770864559 770864587
    0x18031605190e1e0a0e030d0207050f0105040c150503010e130204020d1118030a122d120506010309111002030705101d2109060f0a0c02090109090503 65
    0x24080c020307a00035401001074581841c00079180100314009008040080941c2c914624010192240300c00c280791001c0c141100c0e000204944c4641c010a0015032140090f09200b4103022500b01d4840315035003041e040104001c41c17006d50400350b4074404044240341c250030360300703c0b944e0009002d00c1191440c0c500200308540001701d000008244000d0001d80383c403440682c5602500e0514204010800000c03075030500d001c41c5042807a02d64503083c0c0c01402800e81c1c54031806d42c1205541813410038070544000b8074079000355030030000107149091021000d44c8105490002e01300e048400c00c9600051805010a00d03035842801094040d54000c0041910b00300c002c810407085080c034100000940c403040010b00d0000740144000d0349840d8625000145108014040d00900d02e02c10f0010300080d081001c0c2681c203140c0f203112042c00c40348180005500c0320100000300d45d40f84181c0742c0324680a24049194106658003d09296490748280d031061456680c448d0440d0544800200040c000c1d041031080050305181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 770867059 1250 770865809 770865829
    0xc12010603021c1d010c0309021e190e040b0f010b071212090501050a0b01050304050a0f0305070602070602030a0c030e030f1809010e070f05130b070201090e0c18031605 74
    0x30307a1030b441c2030f0480c200c00c0c0c201d8480e13040d024015002441e10746102c49003031060740001c84c1c0d541010f015503111030740003070b0100354059981130642c40030700300e411000e40701c00404884e01c1000707583c005080b9031114030703044011500329011a000c010a4000071070030f110f4612101d0480e003450b4226400c01d02c05a0b03a03070400a020000359000c1000b1103214a03140109405000c1405d40907400014141c2403022001d4191081104003505014082040c0000550001103001c0c00079000003489030b4000c22442d00b103a8510801c0b070050042070020503450144403043d4021801000e03115010040302340503036400e40980c0c0072a001030b4865001400305890007070002d002041c4103400c420141414241080020300c030381c031080c3c000320f000c4004a010000610342003100040f820086084c8903040100d080f1000304541414001d80d5200400480c8a20841e40200300c14005007401c185030700f09900d80503005420603007200c40d80001454941e8078503030311800d01094a0b0100b044c0102e003405400c1c28207082c4200340718 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 770868309 1250 770867059 770867077
    0x80705060409051b0406030e0f0a0309050907090302030d050c010b1914040b06070507030c06051603050904141503100203160f0c0602070f032006270f030d050c1201060302 75
    0x401c90050007582134004010400780009803400140c00703040c000394602c1c011068003d006254000107a0a0200342c1102d1010215402280c0c0828183d50341c8100316030003c00c41d4802500f600c500802c3c41d5500d500a000b41031654500c40003002031840c03650410100c42005d0241010031b05181b14184008801d40361000b012800282c804a08030a4036004100a903101c0e040c01d40701908032482c248100f040340c2c10178100510b00e900d0401d0030240144c05585171209074900c003d041c8500010383e4130854840c4c3d000311980c40250309c610704080c071f09144d44040640c00c00f10082d1007805600440d030840112442a070380034400c03001c241d401e454001c04090b2541c040c5002d80206221820760454009034803800189401e5100386c00003d502c080b00d2502410801d902903400d00c90030307200300a0201141c000103086a2000c01203648080c44402108030b107030040c4054140c0002d9014900c83d118280000100600e070504150300100429500e0b8071050701d03107005002d4080e20854820004024840c4290040d1900345 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 770869559 1250 770868309 770868331
    0x150102030319150b0d06030606050105030705090405040317040b0103141f230a021c02250312020c0109150506211c03090303060812040e040606050607080d050108070506040905 77
    0x198490130540c00b2604504409600d40f900c0d05418020840e2600a08001744800c0c20214214148120003521a01601051500841d5144005010b141c4103c69800c42c00700c0300c0070949441d003000e08004401c503809000640340450b01580100314000c001400007000381595095107205503003c0920f1015110862804500000301603140542c410b4260000b40110740c07071b4800680d50204882c3c540c0940000c98440b40d0442d10600c2522840d0b14042c150004110040ba110303041e030805450182c8210f00c080c4403800c01c051010038100300011055001d1548140a0780c5100c0f50600080b51041c10780764122019074116500c001144000360b52414862109d444070400c3d60380d9a08420444041c0030141002c90740060703191400b203010308d80c05201d070702e0182402c1e4000c3c11102171020030f03c03403040c071691051031032143c40c100024080c00070540c4000c0c00303080c4c0200f40c1d560f69582824000d0017038202101c1600120b28201c00080e5200700000c0071012914043d12003802c2500e020b02c0c08005140c0101b40402d01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 770870809 1250 770869559 770869601
    0x10e062d0408010c050a080615030703020c0709150501021926070609060605011709070b0d02041e211505130f0311150f16020f0304030308150102030319 67
    0x450340030b000780400c00e04d455660640b01d140c42c4800030a078003005000d4a000d502c5100042070f4510401049981c0607090303040c05a40c0d00c25202d2003601e420b0f040c1e400f110b1064545118020700d20b1030505810308548090342100d42c1440040c2c0300a40c1d002600d2001001d22081944030000c3c000c6200260b4548013481c4099401d041054465406940500c2ca00311541036031450240000c1d0f8014803009043d640c4055041c06074641002040d588038074602540400b02c4010484502454850701140c001d0f040468550074080401c402c0c2c290014054091400031480d104882400d030340900c4840500e054028512605c15040d10f5645401071001a0003032054500d14284c16021500c800022940c4920079030700e0700307549280303400b2440c2000040584c2152058035030f024400c81090380004550001c805154615000250240036460501e034411144490b00001c10b000080c1508050009d10401010000d5000c0c1c024141c012a2240b104940008150054900c5a019107074940d00c541ca500012403041005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 770872059 1250 770870809 770870819
    0x60c080403060f0c030e06090726100506101701120309090c0804020306101211040e191221050405011d030d060504060501230412060b010e062d04 64
    0x39541c2c2c0811500c20140c0b03070456030040705e506220b080740c0c1400700c44c090803650070450380141d100c2203a84100c200d880c0c003613007a8907802880c48480c5001100d102d07040302d0001d500d402d14080a00000c542c49481074100b2082024114020300500311986003e10340d0a506030300300341002031400e81c800426810400b10400220702b80203030388a810314000c0306486401d1140307403d104052030180c0042103d0a010100503080059001c180e0311900c500b07a1249420740c0042041b0085001080125030300000d03840703040b00c6804641d9051184c1d0466901640f02016120031407a015180803a02c03480700040345c65281d03601c100200069201c41c0e0054801c40c00800d905c070f10f55101029508150b024503c0fa40c200144007580d122403481020000c3c0400d43e42031002e64034100010748220f0300c01c82c0d0139224080b1104a141c00d204554100c3c0c014040f46e00b040181411a81400c2000700305950304c840c08110310a0b0840180d150000c1500d21140c0300c00143c4218a50b007070440d00ca20f40315200d00d507002680c1032002042c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 770873309 1250 770872059 770872061
    0x30706080a0b0628090b04032003060708090f0a0b01060c1a0108070501080f040206030f0702150c04060f09080d0f1e03140a0207030e09270105070f03060f060c08040306 74
    0x5a01e11a031040002060f101e400c500e208081c071480e21300f09008200000b00007921102d07095904480c3c12100e000d09280e060890385022640005105505018002c10041159007107022280521070740e50071920343e618441c03081070f43e4103240c69001d07042c2c08811004000d1248158850307000d0601c10040d45540001140f04c9221a040a0304041c206800030300c014040b42d64031000b00c1d5030042e0035014140c9036090a8000c207540e4400503161103040e5105c680081c015030700030031403919100f120242d900420300c1c00011142c629045401154002860300c90745a1055104030303600070980d20000d002d810341802400060302d03c10030005104051060000e5118004645055440e507042100d4601041a820724141c4a0b011500100ba101400344140408000309506c012801072604080c0c8402c070301038807017840814403442908081007658240ea808801c0c4c1c07800c103402807409000e654071622203c400b02c900c15402d46a141c05a91981d0002101c1044290700c22042c600116021305540f6180603200e0319504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 770874559 1250 770873309 770873317
    0x1060b0901020c030a080301050108040804030c08100e0609150a0906020d0203100f080d05030c0705012a03060506030a09111915090303230c1f1a030706080a0b06 71
    0x4a195840031415101658041c0b1451040b03a004401802c2482030a949800340c50006019103810010440c001804001c0d85604903800745d6000100981025911071900303590301401c0b00010700a50400400e891448000910540142700c03200103003c620202080b401d5450000030488a01680c4500d030410108034580700400fa61842c1120142e03aa2a01a4107036060080710741c0203040c58004004100410103011445442d014200e1030025501e44550400081c24096808094610f519010000d0000420821003075840460350105d00c075010018078043c0e045580511400350440070400014450200c00e81c460300b1003521884007083d81d18007820103d51546c1505000401508005c0d0090284182821000c200812986405024682036580c024401807040002d100c4549001c40042c6000303d02e1400d80714003109031030403908240c00d00d4014242c540b00d09000d00210300d15044415103207009417904004a41d5025009228451a01e0003c680c0400010200b500c07407941c51214900760f544444c010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 770875809 1250 770874559 770874569
    0x1140a0801080d0503010e0a05041104021804060b091e030102070507030309080f010b0a090902040603021e040f0504020d020108072105011401090807120302250e0c030705040909140106 81
    0x640d110350704240449250140340450402403060900041240c40c00140a0070f901681c00d01010506031242d00c2d042003001c0210258941c40b50000c81c81105e154810649074081140886091003240da48551800161050001c2607030800c00c682d41900d06c0703405820403020b030a032010340014508036482d01c5813030410307019070000c80001e204100200103101041003140d030264580402001441c1c80b503000280076403002e01c1081311070780d101e04560065580c2c03540038000130358004d032000002d41c2c40003d0503a440703002c40140038815460000c00d83c3c1d00154500c18648600d41c0035100240d15102c6400544030040b00918130805c000742c1c0e0320402041d0080d81c4410f8500c0544c00000710b1254101501681001e4494601c5c40c10416400410481800300080180494902e03021340c041d10062401d00300c0c02d00d02c11100c0c40d0116042d420440b20002d10b8400001c044901c041a51120f5071500644003901e4071054401d8000030b481400309215041141d400405550701c582459100031040c2d16806095a5059000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 770877059 1250 770875809 770875817
    0x9050a0306061502010b031b030f071410090506030c091507061a042c0102220503060106081902090f1804060c090303020714061b010603060c050306030c040b01140a 72
    0x1c10081822886a03c1c0422103042c0001d100b80d02e00340002c41e648240c0c0240000400701d0301400340b0f005d514203102c05000013100c04282c0309895110780d012400d0a003a00510790003881404082505288100d008205031200200010318585900e0070070340082e00031440d2194041c0e03c0a100c3d8484025500040a0300b52080001213010101550889440c512484c401401070b03040c601d100781c91111041c800725100995840d1b0341403482ca015990760081c05008810030842010050101c1e9010f411180c90048410490456a1a03070300c030310003100e19940c1501c0e081181c1e4801544030b02822496009402e030079001510680d4040b828600017410030850303604004111001d00140420b000890180642d81290b0b8280700d40482d00e16175009594600c1c80c07260040d60b1203c06501e41159840004071a82110040d074010031003d080c600080c0200716a1004440b158646503200761028094070540340b10b441d005000e040491034400600c8042c1541c1c400c1e071307810043c1d05240c61920082d154041d00b50040a607031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 770878309 1250 770877059 770877071
    0x40b031c081302090a1109211006180908070b010b030613050601140306041d0d18050a0303050309161d0604090c060c03020a060f050610181509050a0306 67
    0x1902510303034000076181480c0b10440884400143e241d425980b0b402819134440040c42851081404205016903946680d101b086500c6030040348111103003000440d0420415529000c410180c07140895009200d0004800c00c610019200c00c5c0d1140c2c0942c0201e07001310165482c02c121583c2d8051010401d030001d8400350404010701ca0b10b8200180a2a00d440204034104040e08119002820364503000905d030200c02c0f800400114030b516160800018100004280d8501e25081c40415466411211244000808955801020007102048035044400c081c210104903411a10111183c0d070008205040511403032564120000c0c0e407400a00082054482e8159908030308050900280c0000d004a031095060101013004114448600b200700c8801e802e000c10802618034081e8101200d182d0098a0346142c55140300c403500d81900240d2042000700c1e44010360310f00b080d60540301c2d805010007801088100c0030703041c05449622126195000c0460a01030780d42a5078200180303c90708143c03c200d07a0355072941 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 770879559 1250 770878309 770878363
    0xf1707030606122d020409021801020d0c0b010506030403021e07090b03150c03040203120a0e010809030a0915020a0204150306110c0c1e06070f030e180a0209040b03 72
    0x294240c0340c405074590113101c12004602d90455800f2403500c032030710741c54810800211201559040703800030201005d05549506001b00c400c1e8500700103109480c054001c5074050030750244185000350100e64842500142642441d040c8102500020012425031003502204902072400002518268517500000c240d4142000880000c0d61449075001d4040e911500c001d00212900b100040e522014540003d6207170350395400000d28100110100c0400204005041c006040d40300c56540444602a211620140c6034107a51030350380e115080012000914548062215a41c030032105084440341d032040f10b66000c11500040d0480b030320945040c6000c0b4854100700100800307030052565459011224a04000c0030b11101d03a100c0305c0400e2403038480c40d11401543c00490038029100d050ba070010348540d45950742444c14046500c1c07070503c15008506050b10b01c0d4484e191044003038880260745a0b0206d8a40c503541030400107500f1800d05c9503400754803144490200e80342004491201514040822031301c00c218 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 770880809 1250 770879559 770879567
    0x201081f060c0c051825050706090501140c0904060b03090c010f031d030309060f07021c03020441060a031d0307230a0210080a09051902041104060801060f1707030606 73
    0x15246140b000140d504d8240701c503004819034000701c9d006070010407101c3c140d181050040141e030b400d10005004030030600517600b4a1801419000c101620308000903070300c4011003242d9000840d10022154040d1806c10741551140b83e400d0b03000c1606040100d000b1484000c0b00755001e0351121004070541c0f012041140100c3c0401082d40c0100c0380c12501603240c100354070006c2d200c0c2c2c1401c4c95100c4414100f202e81e07000034402d504031002801e20940d038100c40048901152240708400021404035050500185400310f10803442a200940050480c6d10700308510314260f02800000100070f00c400f8914580030380200c070500040010512403a0039210703146c014441c920003000403d4000107140d100580340d400585030200b00990690303040c10003400542d1030341c0300500130784140c40b0000c00030b010702240e9096292110f8203450625208450501605555030a03404485c0901c0c0b06031400a82220010461103001d2032003695450b0703040c076010f81d90411207501103041c0c0c80c00b07072150ba0010380d9401003046440da01c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 770882059 1250 770880809 770880841
    0x80709020c07050d0c06080c13030f1407060503060f040605030a030201020c0706020a0c17190809100503060d06181a010e01092f0c16030201081f060c0c0518 69
    0x44030300d04013002a5072500c42c004c20941c000c0c24148152200131400002d4604250f0702400c2e030300405240590303100d20301119040c2c010343c4104d60070344e10040079110782100031540d041036a0382a0343d0310381165244c00410a507658000781c0103803c2680c60304041070b1910140310741100a8025000503945a442035401c03861f142480c0c1c040c40c215000100705c00d0000d68800c1101003126450301410640a05125107a4106044200e030064041030710788200c410000c2c1d4402904442c181202c11102100903044191418403003151490b0348045510f440d1000120140d0040905050081841c0c021100555900d4001b40c49988014660962000104450014000d9090140804090610180701d400384002a0340421070905044840911040e0310702c0d003000c7d41a180f5a00c83c83d01111040000d011072a0380d40030b0781d404182c3c0041d00d080d00041121483e95981100d90038441c91b0a00c000d45412000ca07110004a20115180c5a00c00790008003940c4c1c101050303101d280ca0507901952401c02c01120714003055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 770883309 1250 770882059 770882069
    0xf0f070b011706090307080d0e15010603050903040305101518020c06060111060f040201112505190603110f1c0515030d050304150c0513210615080709020c07 69
    0x800f1100300301c0f00010220582e1412035001c41996101c1e04582080c1c1c1c00740c8558201c1d841244695090143d17004400d050040c122107482d207040003140c03074603400c041d00d80c403071804040c05a43c0b001e01007107507400c09503100090108041c020f4292041d00c0740c5001c2d0381414400350b14030041b500070600b0008041c041c000c840d004402400c080c16082d40c0611506d441f2040285940c4410001000142c2036902070101c00d42c0c0c02d1f0b00103094449000050100c4126211904120490410b0707031540411642022101c0803102240600800001480e0280480191a140d260080c40300c00c140102d03001f40c0c240102400d1440d020f5440070a4801c4d0b007107400400c5400080c80c182c2d58030102201c0000e1a2804690f1614040c0b107490219a2550340d030800104089070060002c207014030301a19100104c4c1d20201603e080c10350240d450752003659038121800c8001d0781c04c00a0845000805003d4006501c55010640c07090684a4845040382d503184107905180c0e40790b004030a083e07000100c010b0000424030051020305 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 770884559 1250 770883309 770883313
    0x130503061b07020103061809061109030703140a0606090606020105070305060a120f020604061806020a030e210105070509040f0e060604090c15120c08070c020103020f0f070b0117 78
    0x2190032203400e40c1141d41ea44404001c4100042c210055911a4125901810081240400c41c48000059800904032008240c640c1480e01d1141700101410808644c9030390f80040050054a0840d01c440c0000040c2c8503500e5158800e000c0108000b414501a4000030081100b00040c0c1c40d150100c06825950300818810030546010204070080d55104003960a039101c01403400c807480600e1a000c2d0721040d1412000e50700900101340000d0850348821aa00d1020004142ea90750568900c0d099980b54076204008011900e4652001d0160a2401560290b00b90100795005000b0300e05e4101c0d8219941514480000740d0700140c000e66505003400381888040415070204030b1102c802c0116034495101030800d074491911515903c0a0210607201500038000340c0315800740e21802c10034041c0c4100354440c0d01000090a1403002c0a042d80108441d900c074128644610b402d04485600441c002d611222031510301001c2800b807080540041005070482c50f01c600842a01135042c486444022000362840006907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 770885809 1250 770884559 770884561
    0x5040308060603131101180e01050f06030f040b060d060207060c08091204120f02030d2d020d11070819200a030b090309280501021b06031012030513050306 68
    0x4500041d4102c0c141504114011721a000000048407403000241c1050060502042c0104d659001c0060441c100d0b501107a54184200e280014811640001c0742c0740c4184061410001d40403440ea0000b01d81d000d10018541008a01c00755904000c98002980c1900c400f651800705c4079045405c5210250003050010080100150085542c102403080d4004c0050840540c1840001c00c46002401d46415500a06440001c54522030040c60f08580d021508044640c40051012103000c1101c500303450b00711580070b40900360715000c054501c0018080e55030300e2413182100010b6039105c140701c141640c00080404040ca541c460400ca0800400c00c04200758501c50030b2041c00c03090b6900326202044942c42f14005550381e03603000005d401c602031103110715009001c01d0101002d00c842005407808400c0c40381d204042c8541c44070b004a0342e5006005082d10a261800c491803c503241035006541e10201d904000000035490b1131080c9941c0c100345504070049038001c642c200ca01e0304060401c2010b0301040d1300030701003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 770887059 1250 770885809 770885821
    0x11b02160803092107030f0b100b090603270d0201091b0e060112021c0609240612020403140a0201020f010b090112110316080f0a0515100305060a05040308060603 71
    0x2590326100440710b00542070300003801013030600380031402c019034106000002c8030784035041c808840c803401c444a0480030503603c0c001c6001080002074500d8041c01801e0542169038038441101a4140e1408555812003940250304078020100f0228603180c01d240d001040903401d914000400c0481055614031069420605018004a0640c81544102c0903e85001004011003a8038024450720020740e00280c040c8001010301da1143c1c00c00b0080300c514540401c803101280c1c480c65403991f28480712800c110562034082248034840c1e076900100980341c0c41d005107460794035612074543c0d001d070382400c3c203261300901601001d540e0107120005018161200030700c6a920030600003080c0300814080c2c0c04105d85100020f0b0103019002c805828200000341c1110180c500300b030300d8002e0807102c5108814a80c031484000ca00040e0000c112051107581c0f04000b44680c0e0303510300505140b000001d04913002090901800800300ea003c202e1030740655801c110000d12401c160400400a0000604440c010305081080c801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 770888309 1250 770887059 770887069
    0x20303090103051b07061d0a0c05010e010306050901080a050c0a060c0b130803070915050c06060d020414040f0c06090e361006080105040c090e011b0216080309 70
    0x2605803091800166a40d50380c0c20700010102a50030710003416401050400070000300f40e00c40882e4003010119802c4081c0c00420556039442042c000a200d12201da100f00043c0d40600046400d10708141804200c143d110700224022403826030040259620005d002d03424404188400200041d090701c007100003034102807000e054034101c60300050030041c02000140341081030ba01e603602510303404203019a6030b0a01c803000074080c0181d4040c648505801680d00080140034000303c43e498031100000e014559214420400300a0640b101030381c1060f100e000c600300c1300c10070046580c460b40c8105170300c2881e07074028181460080c1071b68100405000700300c1030501030b0000012415500201d4015000c00410125119005046c0d10103240709240aa00c14903010040780481d414880b460455410045907a40c1e02106081c0d480940d005030180c07021407401e02030740c079842c1c0010100c1543d038000401c0c0400da50f9030320201006401c5010b80141c02400104440c1e42d07902e0b44c10001008148019401e244030040064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 770889559 1250 770888309 770888317
    0x80a05061b130e0a150909030905010f200c030a200d021c2604030506091203011701060f060302091809030f313b09010207020d051c0507020303 63
    0x720450403c2000078183d0341c1c9075003100040c0302e281807078850066070750358082018001c07000d411404034031040c202081c41d500c00d034444030f00c0820715624040345815062000c00132071081c00140f2030743d0088030320a4241742c03010443c4883c2e00e403003080c6600c2484100d036650004508181500e511940d9505107101c0503941c2c0408954405d010182c1d100000480c03444c000710b00c000c1568a1100349400c41d20346000c2c3c8440c00f0050011240200140d8505035035620115854021039150341042103c01d10040c0540540d5491043c80e10100000020392640c81381c040c025250801c4e4080710000307800281c410500d00b050b04510719441c032103054103400c81c2056102d5580300c1c000c50b00f0703299100e8804aa210900110071850115030140524120310000b04030f018200460b080e4001d1102c02e22136000b440f000d100c20200070980ca48200b5000296040ca05c169542c2d03905001780482c0d03803641d001c1c062000076948452880642601c504011704000341500360000740355509003203c0051000501c00b880150301d01208031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 770890809 1250 770889559 770889569
    0x2060712081b09030d1b02040501060e04110909040f050717010510060302071718060c03030a06080706050405101416020a05010309080f09010c0f05030d06050a1212020304080a05061b13 81
    0x103a80c1d91b070b18425441200300d00c0e01d02c0c041d6015040500000e0b2140d00070041a00442c0141d1781802215030059192100303100b50303070b202070b00b10a5500000c0c021480d032010180d10b0a1003602910f001544c1e40e852400c400166944400c5980d54690501001805030703104070008101504056082c140141c861529803840c10118003070b5070b07400090369040c2c0d202c40d070000200580000d000a485481005145540340c104840f031140d064542000800e14040016130001111020b503030301c84c41e090134001448181c2c801e4110345818042c1e000b240c3e203080c0e10104003034000c5400784a190140c1111500400c25400364603030001d41030614084142c00807540c44022210380c005003410842c0d4401c1d4210040f11440c0d40160050700c98240240d40e03c0401201100424600040c0f038003d1003015150410000d10350303c46e1107441203004100200320009085030b104440429858010740b401d10340c0d164580d5080c41000c401c1100e03250000c03001c2040c2003c40c180d43c5003109603540e02060520403d040c5003144840d941c090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 770892059 1250 770890809 770890817
    0x200f090103150528020d060f03120e0a030f14070e07050a0e27090d031803080601090e070f091505091c0c0e06100c1e02060712081b09030d 61
    0x6050340941001844c01c449440310040080ca240f0113904025001500c1d104074460400e20000351003405404407005a98000035100d50f144850402528409450907151b0b812001300900000415a07250550482c60300440044040c0301141c0b10b4070b82803002da03410000301d4068107000d011115030b000c0d05440480c0300500308040c45160100004201a48031500000b0320303020009000610746100b016a40560107450071955081d0300030805034151050304c1280c1303680e444814104000b0912802920360017041c107040180100d0703201d910341c0d0104501124004080750341c1107498a0b0385a07121509100a11012110f20000010341b50000c01c588500c440c5503105010402c601140300813050351100045922811844031b055403031000031070b00003003220180e210341c00840ca4100c016005091000c1503590000500c040c440b90040205100580b8250130313a00064140107810000300ea40c02d88100d203902945600d2098034100340c007602070280d1020740020700c54081c45a03914580300041d02d071031010b1060030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 770893309 1250 770892059 770892061
    0x190f050c0d054c081e01021204020d0609050a1101090909050a0303020c120412030809060601201f050603060610140d0b061201092706020901020307200f0901031505 72
    0x4414111a8a0001e43c8802c0780d000040010380ca101c00920107003084051803a04c561910081840d500b00e0140380c80403c646180d080001d40146091802c1224180c404d510000d007649294480303a00d4040c1c1e890741218800520701c090340d055a0842651001040102c0c4c0038888091942d40340c90711880b8010004041c03503004070320122056018410240604031003c0255110341c0e448203880009611843e0070303400f10705013a000c00e03000751020030300d207108031010b0b11400c000544074150040b858043d24004481d9004d81c0356010041000800740c6c0f0188884c0c5000801c00341414001c040c2820009807546210b0319001400025540e00300d0325030741c2076801558105481d400c2c403401d0740340540342002c602c1e540841e00145c07440048501015281c1603400d0502c08114100d0b40b80e6031220920040c102070080500100c1c9030309e000038404e800828500d481032068900b05041a62001c44801e0807224050060030400c110304060b080c410616440910104e410054079491501e44c1009118007810041c0040c0c2c440c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 770894559 1250 770893309 770893411
    0xf060b1002070306090201110d080406200901140c01060e1b0304020d080a090e0108060a20090f0a05150a020606030a08040608041106030915060f0603190f050c0d05 72
    0x42321070603011420f482c14401c00180041141a01300c4084a1481c80c001e41800f074070002400140e0f2001c0c0910600f4070f08540c9000555542003000303503000c440c020411903e18012703000e015800c0103001001c101046410034032155107250307003142e4892150070414001c001c0036996464140f9105a005140559100900390702114200c11a03000201031450850000550b2180012400e11455008800b00009988030801c0075540e0f0764a40001410702c814485150185807030b0800500182c0014081c0a1150340c2d40049040344c03143d6403207a80700d002c02240d01c50f003098062002503400075040340684034004c2d8540e40c0050501440c0100400c00415500080400580c0d00700c036641a0f41c018007241d143d10b0a103012981d00c040441c4106c61902c45003009ca41c2900300700780c0c4c0d0b07181090020400c80c250365603000c00c51901011408601901070b214088045c01c0b0406120740e5015a100604555440d01094071580c107644014015040da00500b2048103810135a5107404449540200c00d4094821000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 770895809 1250 770894559 770894567
    0xc0708060702060414070503070b070318060f21091208070e010909021b060f010f0533130305010f05070c05060c090301021201260303040b0c090117040f060b1002070306090201 77
    0x1b0381c2040e505403182c10300214010858030081d0444511903a581c240c0c008a954110f903025000388254000b2503240d2444003840c50181c0340f0110b03a0003040d2001c0e03174560f1164441000340c44100034195404103d4a0461440d154042640d50740040c0790304046002504080008045031901e100d03414a641c0c0c042410410a41c6c10b900c25040048101c04944941c14a60340d03000d0001d0b0b0078030412150041c103940008240c1841ca40f0b054107010004041c0c92100b500c0300c80100da103004016241100c070303401c1010000d031200480c441c901a600440000404003103007200c1e10111000500050144906040200c0018000141960344004460340658803032203140082030180c002c811400c00b042c0074010000c9580c0d00e04000342d80b00c412896002e000d40c174801203c100e449201c1550301401545440d4005103c480c8040001c0111500c1072509001d4503545e40503105030321200b514202c43d41c440c4115205c041c0001b901410800010032503102009001c0144003a50700c4401c0c1c480241115154842c02081d6802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 770897059 1250 770895809 770895823
    0x627121516170403031506091802160203070f06020c041a040e07210c120807141009081206031f0518071712040e180709060b0c0708060702060414 64
    0x701e200b100265042914002c0d0103070144401904043c00d00941c00501503209600701030441e0740804245821546a4950701d0207940020004000003100204410044c0c81c2000103100926004a1400465041090090402c05c280c00300301d20407810056000d02c40f0544090348401050120703000504407059003061414003003141d005c8001355800380c441c1c0e242060040340316a003892080b05912441600c0700310080c480ca00d45e11008d803400c0400d104801c0054841082c21015500a1017250050450440c0c144280c8050400480b600c40c00407070350015050441c82290741004049001d02201c004850f68032244440d0100364601140e101d2011a400e070301e002143c070048a2540e0280e9620311707111842051041c0321840701c002a0704c500031f01c0c5c04501e00200b090320145c480d420704401040c0c4034000c51850f2a4000c05140b10940510080002d00e01e8081c41594002d00700c03456982e445994901c101c070700b0104140e100c00302c25001201000181980840c12a600c00e6124100c07184c0c0c0c0c00440c0600e864644 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 770898309 1250 770897059 770897087
    0x3090803010e15040c020a02040e0303100506030a02041e140a080d1202070f080a02060f0f0a021b0601090516050f1b0a0503031f08010b0306040b060627121516 70
    0x21038003030701750280ca9022503443c01040c000c0d2010301103103082c2044155a4401110307401da181c010b1080c18041751500100464000c0c410800160406403995450700c1c50100c0c02c04051110001e400c0c2c01c1080308080d092062108008030b50f0320540e1490328590944030386a04a4803410810541801d040410907941507500302500410075125884131403402d21a41da022262040140c42510006104000e16601d55446041c40703031843c0405840f5002c000c40603401210074040d54060050440301041c40801c6124024091401e0100e000e0404c0360038828070103281840031007000010480c038000021118122900e805030719101d1040e10141015060504030307002401440c038040001400841100b65140e030983c4449200c10103106540c0c0d0034054221400880ba10350590040030007c0e01240e003950718994081c10151199290101c0c114419110111141d003150420080c51050130480c1041c001550f50400418010007141c0b0304021141800c9034014058580c0451030b219442c20103108035201d0340c40d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770899559 1250 770898309 770898311
    0xb180714130306050f070e010f2d0e06090a140609060406090f05010e10030c030e07030f0b070e03071a04030c06030504060b04061206021e1b010c03090803010e1504 72
    0x9101c05154001c8110500c019144241010040381a04800025260050f6141d80341c62412008000054078280310515840d4207200004440c045000c6c14800c0150807030040092014002c0d0b0081d40240205a0359001503015070070a00407801103441d488004800e4400303000b480c011500c88200082c03045d126200c0400e03003000d0040350004a80da000f12540d425102011600c18155482d0701c01152015040d0680e03d0703000302021901882140640e00015000380c0d140390100303000c1d03460b1909600d009003580c0102d54000d40550705800b40241c405495401107007510349a00c415101e9070000355201542d0040380d045950b8400e4641c840040d51007218003e41c1c0c030180e44405166203074006001070204903001c0c0c5500b41400c00000e1a49010310410302650050080214a4011a02c42038025003080b4541680d2007110350075910302c180d002002e041090a0011100b05181c050301c0c04500f0f440800c07040d10203050a00022100003503155090f40d0541d16039860b86001d80d81d441c50144941d480300c4640c1070b001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770900809 1250 770899559 770899567
    0x303040305250e0f0403080a0906022b0e0a0308090114070306031a0403020d030b01140d060303110c1806040f0606091703250201020a0c09051008010b180714 69
    0x1002c8844000951000450700c00b1007140e40d6403014186410040f1206070000c070800300060002405015001d03000300704041e0001e00d00030b603540e8440c201ea000d003000f50300404001071080e080d0b40c00b410f10451069910601449007400369600103503240340d8900020305000700c0d40c0009113416000d6101514020401007a805c450505032000b074001c01c107500040c5c41c0344030803a581103c1c40071f000c40c905000380d03859401844075418030031044000b0218a0304860410008152070750140c580c1001400400038500800500580b542c5000b03024140110b10545181d0851036503203076036036528001c4130501c4841ca0207401d007075560140051f0040c9502211980140e02c0c4c81000b00e2800d91210182c0c0907a85a160711507001c069014405a69000300010300100d03500003d44088518440c04c220180e03144180102c9003620441d1b512100410690341190b042d040d505c4040102400c40031400e04010a120002045000d01c14408200714007a09010030403802d2040c00030801e0700303215600e009140e8002d01146611 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770902059 1250 770900809 770900833
    0x8070201020a200909010213051207260d0f0509040f09020d03032c060c211501180e04020f030316060207020906040509031902120a03090b01320303040305 68
    0x1c400e03100c1c20f994002d890002c0001d603804814400c40350300f00400ca804141039803405040010004a140004c0e419000d5203000290500c0420a2103030450801d008405403002c4203404946007220b41e1046030100061250075034140c2e40c00404940d840308050f1804a055001c2120140250110010081d0003d96883c8041e05165040c0e02501480c41000b034141004489121820b01c0c144155411034110b0f007124002c6103400d102c00b4002e04c204046103a441625410b40c900101394140100c2d41114146404001c1e00310300c0d81d109115409503110584102c0d203542c1801e01794007a0001c000c2c0024090800c00181d55401c0d9800c00582d4017018900d09a11004810342ca4540043e400c060001c03406902e1040c04034445140030300502c1e200c0d1802000071820306581801020503060341a0110040d4000c0d00402e2100803456002480b46580c01c3e10086070078640c51400703407034882c0164880013176140014119400c80380103401061014041d000c21030080c85c1c0c1540064198425540000c2c10f0707120340f00b01c12003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770903309 1250 770902059 770902103
    0x4060c020a080a080702010f0605061b0a1407080d020303150118051003060518011d040c09060e092407181221031802101b060f0f09050a08070201020a 66
    0xc40703a42c03da4000d00c03000c07408421540039122740f4001d0b181e20127018091090440250503d0061000c2250111031002a064448066900c1750000580c2103411105060101d071030104014120300c1c2d0329100452440c40e02c1d0030101030040481d80303483e041040030010660010034079200400039080040041d04407000100015006090301d00c102d80c080c09001c18408d00b40068094017034102c4000d90203050030014054500007007101c0c024802c542c002d28141002c540078030703e40308120281c20041000c5c03102d800c00c20041403510050060070088140c0b05508400042f030016034007604186030381003c40301401c15681201e1030710300a400582541844103010802d0011150491001d20100e040c680300030300c200d500840a483d0050300d0340350a12007240d6040c006003000c6528400c030780203600d4090107403622000c1000741010f40c4070b0265603903a142e80300030702c030410b182c0325644410701140341c20030903500c2640d507190304c40a0801000d001208045180300942e4003e2040a0610b64040c4482c51112000a8116 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770904559 1250 770903309 770903311
    0x210b13060611010c050f2b050c040504050612071403030403150c0e150307140408030d0507111f020a140a051c0204050d0b063c09010e04060c020a080a08 67
    0x10b44070f42c00d00c4502500382e40104102d400d84110114000c0c54112050402019501c1080e0f0350701c1210008103030806900c0840c41841e004420000c07105c5c0d602d83c80c144c00c000a584000c0c0c110391080e140c1c1050640ca81c0c2c07002514404907000c40400301c0d015940100041d06600850340003a00d081c51102055440d41600c0d84107020000180d2a020000c48407082402000e01b1910b581c501600810001300707026034040c1030303000301c030f00e820484d107a00d41030321a12018210b410020406c001c0a48803004c4c41042c941100b07007103142121180041800d207008801c81b20380c140d410201245030b540d000420100981c4192a4004503000e03e040d01c40c1d07104d9080c1d10041039035000b10940c81900d00400300200e1075582d41d000b281c04842005101c0e41c003684060702c85a0b40c608000e448258008080c52446404800c41b00562007402c50101103e03000215a51032030311005090454148640305100040c0310f0720149481c04c94006800100010f011210010144d01c1d20480342c0d000360a114011841c82d00d902d40c41040380d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770905809 1250 770904559 770904587
    0x6060a1809140a14060c1903110403021201021308010c1403090106081f05010e012301030905100f0b121903031503120e01140a0c110a08010615210b130606 68
    0x41741c9039039516980c0540d0380181090711a9803680c0540710b6888501c00e130843c0303140d102d51490403403409649038002240950b40c020784254603500440c40007180c02c14104244024800c6100074003540e0200400101030000c5094040d84080b804000305000400075401500684180e40403208480060002c031a0205654403a09c51024105030000c02c0c2000c002c1d03a5a812510000c4001c1d04142d4010305840000c40948542e6041540d40c1c0a00f1002c140104005007440742104000951000c00304c45090a40724400013050080c414070813650102000000d00300c03840c607801b2904041c0000c0520341240035211640020755903d004860110500212900000d110b510b00e446441025040e08019203010a004211b411403200a00503041001d0203020104800c03031103441a8040c1c81c04550009901003c2d98000c111169500c5005000d001d001c1d01200050326554280699048203151080c0800d00189242008068480402103120780b90f0b40e0345d928005050b11014005030740c85000040c5048113540341 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770907059 1250 770905809 770905813
    0x60f060806090c18010c03110714030705030715030b030f07060206060f09040c1a1b030a110a331404030914090a05060111030d06050306060a1809140a14 67
    0x40760f00b02e5a0312084071324010109044610b00740702e00c40103460030240c4e8501503061280e803010560350300c8001d04c580000742080c410310303c038010149000d0501d812081e0700124026171090000703001d6080541e50340c2114440070f04d0041002c2d1120f0300801e04042c08802d03111503902c5080800704105070007040c9584a918150f5009030348500e52000c10503081c034299006450b02c0c0100341c0c14088003a03075641c07007112843e075207080314078020ba01000c501400c03c40d42c51000e0207410209122080c643c1c0010000583e5009030f00a1501c2c0b0110f896002e030204030f520410040e00041c228a0720101d018518420000403200313003c0151000c1c441e130340420044121030031400101c1820021031b00c4407002c1080c7c0c00103030b40507005e0f030402d907500c40381c0c02c000746006040135040c8040c2e0204204221002c200400c2c0302140c126010032103034a0311082c036140040140c025440b907048000c05011807600e506810781104c041c140c002c80c1d110b0407070914800d50b100035a4841c005010b4440700e0020300c40028410400d010600003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770908309 1250 770907059 770907061
    0x13b03130905061c2a1d0a020c060106260a0912111209030a0203060123151204020f0910030308010b0304030c24090311010b040614040f060f06080609 66
    0x404c1107030351422908100440c00030b55241c0b20205244400c0a52010544422410142c2603007188a01c4565280e001603c0f0440b00c0e4046400e001c03c0c3d6450a8004540c16025400c02d4000c00035140c0303640341401420104180048014130560740858808a0b00c40c40b440d490f504d038202000c0820143c00322440940c0c0c10000b00501c00d105034840c021400d001c01da0207000e0060100414440302c2940c4c0102d2100d40c3c90b2207085108005a6818840c0070b0007854512400380e403da4030303010400c9111a0b081c4c0064880c41c1c074800001404020b5004842003840c5e03409101a4581d00c910028141c140c6800419420408010030000503000e00844a0162070003916803002076070340c0c1c85200d512848115401800648122a4031000802c440780e00b00301d00c04811802c1c0c03080510341b018030044a240c04004d40000e6007114900104100c01e1140088070312050f41d05000d0b0f036003041c82d00960303040c1203035403180141d903a02e0190847e0000c070340c0040e029045061580ea4020740d40d0314000c1080c03106840b10b0303100b118010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770909559 1250 770908309 770908321
    0x111201060f0c1101050d0f0c111e031e0d0f021b010203010f0512070b0a0c02090f06090411131107020103060f031e030c0f2003013b03130905 62
    0x1039010140c00d54003250803860f018040c0c2c01143d8a0f000760f03581e540c21680700c600c51061403650f409144010707201a50750a0500390390071388043c40c00891a4141c0c0c207844443c2c40c0c0a451041c00300071502c41c00070391400d10300700c0e2001d44500d40c043d10540c81152034451900c1c00c222102c20aa400810b0b4100f4807046c40c1d1010049044400d08030700c0f0078030901e640f540247d02c0c10010b0b4208071580b0380caa100740000b95040305640d122600382c161f008034444e00008d0030500c044421440d140a0641d00540010604504c1d45002404160388000103040940703d500054001d0009944007050444001903500e0284841980c1c1c1c01b000145801c0f8123022070120781001004a005095507011400301c1e0f42000032015103c480c8811000d405201e45415010041d050101c00085100b8003440c00c1c0040c03107201d4405119100070103000302640b089543c20f200e03905000c201c0266404000b0b01454001110f4107000030034200045000042c228402888180e010102c5c4200100e031000c9515802c59034008802d0209550700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770910809 1250 770909559 770909567
    0x31106270a0f08101a1e040513050a06090516031518080403030309020f1509010206010e09030a0e240d0e010b01080705160b090309120d170901111201060f 68
    0x680503c14403648402da404840946640011000d15407503100d00c0490f0307000d20081040b00c06c0f90581d040c50961191203281c52410a4442d26500c42000c0503100d15841c031655945d0703204c0c80d141c03101429181e1103810040520130207000c02460100f0102050007407a80d00d2410035955510102610400f0303290500e1450b05200040a50a2059208540c00d19090a65505400400c1e0044099030080320100d40c80c28262900e44111010000712100140c94811b40c00c00245031420503042841c8071080881405480c1100100f41c9828010900b0302d4050600104041100000314802521015245c8501011260001001881007440559051060180c03032440301c1d00b40d444500034140050b80440c00981041e2088010b04551105a1000e6803401c00c6515034204005090f01c1802003a040010f01070041d107400d03d040b02e841d079880310180140351100d0f00003178064503281004507082001400060300b0848290700250303041ca41d40504985450815200302c2140c642409060003080c800045004c180c1d002d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770912059 1250 770910809 770910839
    0x501060e0f041b0c030203090303043003050405040902010c051501030507080c03060106030518010c03050910180f050f010204080d0909050906160c080c0d090519031106270a 76
    0x803a5031540070b48903003818100d6400010000585c118007081c45040342550741071009000605103425100c2da5000c04e0401c107000880c420030f90b98282d00440ca160400641c00600b51011601c0860300091140704e28001a129141030343d0004200c0e00400038109004491516002d058030302403402c0740c05c01ca40b620001d60341c54006034410f40d8194800001040302d944039410042d032045011462214500329649520f00b501d510b1900a80440d0b15030b0208880684200040c004580000c1814000c00003040e6411151a0306224042c03c06010303020b5603828410200010300280012400031552075a981da00380b520349000340c03488000154800c90010300d040a90241c58001c48204c5c02034181510b91a0301601980700441c1918144000c80c454207004c21002d00140014669560242000c03c18402c40100303240078640105100e00205540d00000500f94420081541e03800042d10401042d0300c000608070b4080d80c1360000740c4541031a03140c40090301000c51502c00c042e091b500000c801e0f03194070b00d40c000505c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770913309 1250 770912059 770912081
    0x70602030c100c17090a1e020112020d140f040614090c0f1207080625050715062408060a0614030a062610201b010501060e0f04 56
    0x1001540300380075003860364000019104503050501c13180301c10030038048110a00f00c1d004c0c081038204600322010b1009140c0c200850a40c0102001040d9a250740081d00d450002c00142d1149540469000d00d00c20302684004804201031401d03c5003841d0201c0c0ca01e20030281100c003154114100402100c40d0200302c2d022900400c01000902494105882448000410f0f000c1055011030702e09100c845045060001c9400741c00c010029143c5441d14071198034401048450001d0905802066070088551000680e03850503440312a0702d070700c0d150f07480301f00e405000107420403c2c1400c0002c0f0b420340c03100507526580a00030340503207d40d0071342e9035444200050104644102c4021421482d0300090146035100210341c000401c40700080c055458030011102e400e08041500c1000d11044100814910100100d10940035800401d00515031503040408400116902491054901280f4038400c140d580c81c00381c8441e0b091000822545d07071343d800001c246910425800703020b446420003208540c1030130701132102d11070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770914559 1250 770913309 770913313
    0x30311070308010b18060f0a030501080c01140d060918021e09011710020301080d110d051204031e02011a0315010e040311060103050a1505150f0d02060409020705070602030c 76
    0xe81390422914080e03000101c040c4000030301090241290f914038000e04002540351205989890340c1c00c1c3e02404541c0c040c0c02c10041036201500610302aa03000111107a4a4101d0a0749501d030400d80781e111001d005503810015a807418080500c007260307590005040d04500894009100f87d4080052004059180b90b006812150000050000c106030441500e0300e00240c030200da502e440c040c2c0e80d001c12038000ba0040900c0b608485151000c0e994403280c8100002c40c110040c1002c0446a0000740403445442c1c0705c01400b941140008042c540201c5014042501c00910181c0540705810000d00030f00321420f540403a00d29a0f4044000c509001603c4059580f10310b00d5251664201a05125070000041044041000040380c2444007401071000c50700a606c24402044201307031a1610030500220711140300320107840d15080003402d0000308240103e03e1010384035162a00041004224558001c1c000030350403801c0081d000490590680c000c0c00c0160241d015208aa40c031400100d840e44940c222249503a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770915809 1250 770914559 770914561
    0x20d1d01020d030510030605040b0103060605060c0604061a09040516090216020f0a271103060f13110c0f0d02010902030a060b1804030302070b0603011808030903090604030c03030311070308 83
    0x150180d4030145d085194804580c860603a240d54600903108202c0302101c0c55441c40004104008140c02000090719007154420b041c107600703071201da1351844010006800c0c0c1d51142a2010400b01d01d9050040500c4060200c0344030b8541401c02907a996540f801080a02980c2100000c3d03410051003501c0355160b459460680342d0a154080100e14403020f11140d46c402c44880002418181707080f002c901101400792103001c100203a0382c1c24011a400c1103a440c5610780e0030001c01042d5518008107407883e0a00710342c201d904c21300ca115070500601c40c020311002e02c3c0e00001540c1c1400d0400082908a84a82c0c03000c4071014441030310100c4c26100b6018000350150300061001c40042c102d5000400301c2d40d8050004079010610034000150210305507015004a94000b07145030a000c44d0400c440c0e40000c00341e0003401814064140491010803428001d420044003002280290805000326501085c006011a4840d501c0303003800741b42890ba82c4011400f203464021441c4501e02c1231400d89034800d4054803200340c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770917059 1250 770915809 770915833
    0x3030a050f0405280b040e010302120a14250605370302121e01050111101103090f0708030702010f0c230c03030f071b1203020d1d0102 59
    0xd00d4004800300010420240070109503522003e41c0c05400340d80840e1132050451010400c024054802d03045040081000c102c18881c21021940880c1141d50503100c1d1262488070202039820a084444010000302c03042400201c0d407000015802c201807a105c00070003107661114040684100725100b158085981030000c807807041c1c43c5601c2c14650042002040500e09542e0004031200f10407020080c0100381d0203da8041c0b8600740700c0c034095004c1c0d0034001072250340c5110750b20045035001c140300b00f5040000e91003607022565002e10a00103100d0180c0428000804040e50120b0541c2041b01c03c603445200e000700007400001d0011f0588200c3c4e0403040654a0a600b0f41c004644942c4c0e0b041100c4c083c00990711403000001c0040c1703c2c81c00d0101065000740304000034000c10b54284480100c03a01e101c1ea0083c03000402c9402c10400304c41c003950740246c02e0b008002d140800d014609030030784d0140d8000d0a0000d1030382c4c01d1680105540e019284261398040110400c440766034280e61842010034010ba00c0380903200d82c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770918309 1250 770917059 770917067
    0x3020309061317070b07090602011802270a0501030302062406030403091d0a0c050414120c030601030515130b0a15050d060213050612040b04150e0c09060306010503030a 74
    0x2c00501801550b903044a8080182c80550320240307048a03c0c1d030a1404000c0540d41c05054000585a640700a100711031100340d00d90050416400040d03c00c3c20741c14000342c04900c0195850005032914159038000380703404002417000306400d01c400e0303016006141c0018030345020380b95024811485c401040d80b01088040c03e0040e15040104100e060061441c0049031010840c034168034060001d1441c90242d1a1400b0104241c50b40801a42d041c0b200c144401d00080441c3c084a01c00f0510a44404120303814002c0800d283c9540842e5094040c001c04001200380900030900c20190040d82c0a03038516502e601807210000f80c0d1310003024000041c034002140010099810250719800180b4082c44040d03250700c005440072070940310031180190300180c00c03e1008250581140100400c0f20300508040c1c0b02c4044945945009000a04a0b403022001400b001a00d55220902403622842000b104500e00001b5903500341d4201040d100760358210000341140fa0014003c0c1c180c80340540034600700491520207035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770919559 1250 770918309 770918341
    0x501050604091a09150307150e04050912030403050a1409091807090e0d03050117071a0729060f06180d150c141801050a230406030b010302030906 64
    0x46461101e4005031145545044c2e50358000c142c4c141c0d03102401c14059007014580303c4160b01110700d000c0190034018040d03401104415032030b001510080341c2c6644032040a41001d07102c00d641100400b011003880207155024001c0d102c4080161615030780001c40810f04c0140f1f004451102e40d000c04c030140040c6541203514000390404611208039906030b500c1c0d821100c160b520498070b0044540c0890188141d25505000f458010b00d11000300d00e008600c50403615803213941d81e00030213849001040d1003003504a22141128992500045181c030019010a1103254044044440c4500c004d89000420200e14040032201c0d5400e1006098a1900d02d1628807485021401600c460f800405100c2c0180402c030340040c0c000c410820310b040040c503010200c10180490040d189920000c82c801e002c41c040303241146244100301d41090a1050316401d02c0d0508a5130342808810b5031004d036001c10404149c0400c81c40c0034105072455a103041c000040c00f074004501324042100c0c0d1001036481040444c41030b60071141d41c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770920809 1250 770919559 770919581
    0x3030b0112050c0903191a091c05040302040f020c070e0a1d06061009060e1509030102070c03050d050a12090503040503031c05100503030a0f180303031a04050105060409 74
    0x1c96039581d80815a1021103104884a14030318000040e44001c503e018030416614000d119040c280720445921100d5555803624412040006070402082040c0c004211804841c0d441401c841100000050010225042440201d00072410820383c2c5904140f20300949618014500081801c1498247c804c50300e900b0213008000c0c01507590111142000340c8002c90484100c209008140c80d080400901c418480e0104034041003113281603041c40440c2c0c0c0400007442d00c9404a89100030340c2e40004620446204103501644d056100099400410100544100407a40120140c81039809070140c2901e070f1703205141c40c03040082c01c150903030b00d03030004144d014580d0345010303104a82c10980c4030b1000ca49036512980c0000b115048070a214882143e050003000d40c0401003103441c0c6d502c2841c08003c0f84e0f072402003107007841c2444004071130b0b03429191260a010740c0220500005100b29680c07810090000c28100c001c00c40507031a6401009000d08041c003a190407100d000e446103141c5840c000040c80100310300301003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770922059 1250 770920809 770920817
    0xd0804081605031206040e060a0b011e0206091c0504060c1106030708040b0c2505160611060f040c0302090a0b0406090f2025020a03110a08030c0a03030b01 68
    0x7014080c1c060310110448142d00c00c0008560b15101031101c0030801c4001002e65109506016038800c00c2c61001c01c046401400717031900811030030203a0303006036612060f0b2480031000710381c400100c4000c0395000400320302400d010002d5840c000c4400307540d16002c1c420049444007184082104100c001d01c5408400c4490b8010f01594401032521000550a0382c815154580000c003030380180700520044520280e04084a60116071030101190f41c02c0324144804115003002001d28802c0006202040c400640e01d1040b540d00030060030307120070000d440c401d0b103218103038910b01c1881c00082081b20f10514450103140c10032500b55146140d5400c210201a00800c603a5140da110700d001c00e41034540b4042c2c640a80056600411550741c1c203803d503000c072590f0000104011070f04013841e5100031207520459035511960a01e1110003003c0c0071242900403141e401c001d400ca4002000042480b179a540703ca207650348225031821070541d4851400340c2d01d0150301c089a20039045500c0280c000ba0081c0e10208000b901810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770923309 1250 770922059 770922067
    0xf1909050d05130609050915041b030f0608070e280c091d0f0a05072304090605090c0d15170f01061a0403060c0c050a03020d080a0203090d080408 64
    0x9180350400601c07006040200e40c010800d41c60020030102c854000d000c142c81d00015540c40e081c009003030308101402c03021890207683c019075015200d81d0058218441c0302080101050600000203000b0801800c04560140ca420400305000c10049201800c403403842001d8071403502c5002030041044041c4100300da01e1030002e90030207104030702c6014418041c0c0041d243c40340c0c0785203411304503a441c9243c4000181d03d09003800400c00f03034a10025915801010300a0005400d92322441c05a40d01e240303503d41d2803c01050040080c41b0080a18002c1098409000d018081242e440080c07000d8000c040d0387e4841001028499101c3c82d007115401601c00c100310100511202c2d94411f10303c80918200ea0408503140c0101081110100d070034003516004107800300304030034240660154051140941d0000a00b204d894001e200075041c8146140c29006410600703030b46090001e072030061740d1a007003100c501000c10150000a0b540b480a44280d81c0f1031001d01c000340c00000c0381e842d03085880c4003008004569800e4180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770924559 1250 770923309 770923313
    0x6100e1c020d0b040b0c0a021903020709110903010e0102030402061c11030106031a03031305040519060e160e01080103030e0111010608030405150f040e0a0e0a060219080f1909 77
    0x85142d00200e003c0c0d442115a81814106090b264000810303040c041c44003080002c0246074005282a00110342586140001c20345240072814090a54014050b050929400345084115a0300401034000214002c2200c0c0c401e51420074203034001250041d41c000c01c18004038924082007000001e82c030114500009480c00e002c10700714810741003a009140007a5940d039000c1c440f140d18a910300d2a02c2411002141414510840d6036580d403850b00600740510340b904c010a0010074600d078038601c00c000c5075005005260300d40d2421240c81408844202405110045010425014034102110160b06941da20b40c96802d584054915005446000c0d040042070881014800e01c2841103030302a00a00740a107a8552810040200705658822941001a0308200500900d540c80003102c0840304a1240ca1003103680d82c062020003043c08550f0307a2194010040c054040110644c010b20f1607000b0a00145070310072903542c003100c0b02c1c4c00445503800310340300240209060300541c090030781c1d050760060030200345800d0716 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770925809 1250 770924559 770924569
    0x301170718020304030f09030804090e010b0418030f03060b1e07021207060323013803060a090902030a031d060c0c03061e130218090a0b06100e1c02 65
    0x807040041e0542d400b206200405500200e07110300891646841c81012341980c4840540d403055108081c1c0031591569185080c8000390811081681300034002c024848400784044030503c0c010030101c00040c00c1041d403150b290300911800040d610a144c0580c1820900341d00038540000c201d02c0340081c1902440100010f0780c545c11800103122110024052203842c04201030f00362614100315500220f0750a00038031103600e04003003007411140c60044d0308100d800c0c91150031129441c0c0380e0300000d1401c04440e0206040381240c0086001d80c03003d44994410650700c2c03e0000444039001c00003580750300262801e0300401d1181d0204000361022a882101c66121000000c0c129440481e0119043d00080c0c1039001c1803905202050340441c2210074a00c103410b444800c4046445c000307103079214040f0254120380564440e12111220482220300b040e100f070400001655651038820000c90728030035144005600d60600c07203010251480c0940302e80d6444910041002200700f45005201c990079070b8110108050f80e98 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770927059 1250 770925809 770925839
    0x20c01020714010e210702010908060109021201050103050108100b01260103140c131e050c03060901051c06020d090c120b0f040210052d0a090f0b03011707 68
    0x400c0030780d030844403841c000d40350a603891001e102c8000d0300701c00c3d282c6805c154410359072000a160b01c100195920044c0c030042c0c0c1c0f1141c080e00002910300c5194008076018801d5802852441c014107003400e1542e90f68401101514424000e140054001011451840c03401d5040a0300c095014100060402c0090601120b40d002e446020108a001580100b040c081400c5074540300c0701842d0042c1c150403c00d40003041d80c0180345000500303503035a210701d454244c1c01c1c81440d9851a80c0d0140c0c061005060403034180740aa08144e494074490000100000355600e03201007652416901490410021080e44e00c0d40002900a042c25000450311103008100180b441c00146001d8440705900c201c0380d41190801107030400d001400c00000789004400d0102583c1d5951f8801d1000b5500c1c6451580c070174460044181c100004400981303e0b6403544014a10a11040d010340503607d866542c0c201440d80d28118848460706506c50b00700e148a080005100703801c03040382e589840341103000803103400039614040d80c214854 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770928309 1250 770927059 770927063
    0x110904031e05072d14030904020d05090c0d0506011e120b07270b070203100c020c0f041406010e01090308210a0519180b040804050312180d0204020c010207 68
    0x4400100b5800b0045800101891410005403400c00030002d500d004e640203103d03100143c0003038080d00103049000010021680a000701800964413601205460006004242c502e18000d006540c441145c03810020b040104890304807005004a03441e00b09902e03c5500c403911061021280a0f0001c2180c200c18506040b1552044035141424a8000001407910242d5002020b100891507075402d2210350032001002510080e29045554400500c002031034015003c40391580700e41000707184444031f9008a0300105400c02503235855400711604c0f0401085412110000111029440204a0951140c085420b0000040c1030900c0ca9075126250700b45c00342c00c40890010840300303000007402c4840e10f24460303e4200034000010f000302d0410b8180c0400300ca91100c060f00f8140d41d210029014106202e11500c0b0340d03034002c03a6540843c14542040e502c9a441070180b14064400c007030081c000707039020a080315900c900091250039113240c0070381049010680300000340e0b4071a80900c00041806800e100a0503954 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770929559 1250 770928309 770928317
    0x307150807020a03090303031a1903030306050d080318030c030301081b011707031109061b010c1106192007061b050f07020303040f060507050f0703110904031e 70
    0x190a040000e00010006000070115006950b00754002900040701c80181e0b1341c1420045403c0e40d40c0382042541070b50381c9001543c043ca03103c03079401003000c00b0b00441096030b00a603010f110305a2141c0a2014203190382d48028450482080014184c0e05190038240d2113807203003402d6a19041c1c42c00000c52464001307030070402d9281c12003141e00e00030000d0425800e000720030a0034100c01ca10a1a44c522a50f000f005140d2000d06071901004448150310808540c0c0d4200020000c54a41c0c01326044003212a80c500d00620982d840d00c2c20019500b4000e415002810007032000921155540000209040540300b410b0501d0701c0d00c41c4200c5004007004a800030155a420302001d4640410707080c800b00350703031559000b800d450184c03195078144203610000f118081e0ba5a015095596103142c07001c42e10f10f01c100d91105218a00c0500c0200c1c0041e800802054528003410444100518072101207840d43e640d44401003001504400031841030074160740f044d40c0507000b81003c400042980c0d480456080c181580c0b00009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770930809 1250 770929559 770929589
    0x203030a09210c0603051302030f010e010614030d05180904060b1f0527030708070f150e040915060b0307030c05040b0904150f1409060d02012106050307 67
    0x8122202c00000c54100c80070500116002c1e114506540d240e401504105030302c4200081c400c00358400900c5c080f540c058100d075060541e1b07810450080850841d5103446500b807040015000c20103c9138114042d230700030050180506461020344e032943c00302001060403552045250b00564500c08003921480c05020040340c680e179000708025408075085488508000481102c00744c45a004080e540d02082031500a05100c1d20041e41d0b2141c4c52030701441035410311a0910200b1402e20200c2c620742220701000400701003544411482042c0400524a840045d030091044050392401d0303000f460b4241d000d21900394514800010f2002910390303581008500c1d0b8000018420110340c54450b02c04004101c2c900356040608020760158075100341c028803807040c3d80700c10703c0b10b01480b15050854028121401c50301d0560355140304130700030700b26a4000140715801980010b8000d00785000d00242281e030595a0951007003550610103101c61442105501c41566030740301103141c0d101040000060100903e010b008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770932059 1250 770930809 770930819
    0x30c121a0117040f140c0307030c140d15050a0b061201080f0318120f10060311040207020105030402131b12050106090e040803093a0306060c0f02030a0203030a09 71
    0x40030708805010144000410000401c0d07420b80b94101c40b960101d418a148618405d1390f1740742070046c030b00781ca900d4000d4080c00020480507061041c121510080042c550800710410000a40079140000e4080e00d08408240c08181e0b0070b43c0300c0c2e50303c0300340c0180004482070400d01140d0103070050055801170401c20001841821000c000e078400c025006001103280046001501c98030000301c0c100d280c0546c40c0c0401000a9903000d200660b515180c1720b0445440a03603102072038029100d1444162091000301d20380180c0343c24240229003140350103858035491601e0340e41c00d020030101074003482c600c400e07601d90000c01031184062041070620007655803041951014080d00c801c98006038002014440c1c9140c0070003007036249078102c0d94031039005441d107501d980d81c01c0c989c3e0b03092104a072400c01c021000320010490700414200510020305107440d1601c207005400c1402d404882c842c1c01102d0200e244c011004001540b101440c40d01188060140d480c00700e40da0303003c0380c510b80000034548003088103040d007408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770933309 1250 770932059 770932067
    0xa09200414010503030406030f0e01020324030109081b010b100207090b030105060a12050c09190e010c140a090f030c0810020a0c0b090109020d061d060105060406030c121a01 76
    0x2001c44444103640c425403504001aa80348613601c261310505032104d071095010403c550003a80f08003000d4000355502e182560019046045020340c5130805500d002003100b06040502c188401c0c0c6511030501031815028490103058035440e04004803040d903d4050314043c0d42c48488803101403450316001072062506183c0b00d9001d9a0702c2c031040c0c1c2c1c040c1c1c6c581010444207948001040d0100c507030401980c03032380c07007460306007541000d450320700346078001c100301c42803200c4044030704580440007170fa4040030010ac44d0148880350030ba40c024076800e400130380c1c00c10001d11491045401400701e100c2e14140b203805151380310202503420482c1e03401514901d072241d40c2005401c0d014020060030003040d240440c0380c50119000504aa0f540000c0500310420040c002101d001095000750380d09a0002e140300301c074084d2458448060001d5040d01d0381442c0a1003a03081c002e460028501c3c1c183c45000340350600306428050101c006142c03400b002d400300100c218001011540c144035103000310280b01940503540b100f030030001d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770934559 1250 770933309 770933321
    0xc02070512060105010c080d060803030411180103170d050c030a0c0801080d0c060b060c0f0c01170105040c0302040f06020d021c0e0927151e0403080a092004 69
    0x41c064100e4030906410600046002815a1400d0a1440b841c1145082400040c050711184c2e440c0710b07290500100e180c10000000c1d5100b288a0941da103502c000308401d10412422419040c210a03a03031000500002e0300800440c040000d2010350281003801440d0f103002915030030b481c11101c0040010500590040c2400360398010105410072441c0c035490902041d5551010350580da007007101d41500d039010403086800515402c14018042500d0314445035656807600c800043d03203001c0744108000c1070345039401102009289101c00c144e40314940e180c10203210141c04594840d81c200f5038208004918032101040c010050138050380202080d0350051030113817603c0c2c25400360a20400001c00c0ca028100e82c400c5021049070001e0305c0c0549c42d501c6264600300341040071002d01001d6015844090588a4001a070301826004209151010303240c01007501c6200321428038290041c2070410000d4003080c0108462174000300c55280001e007400c5c658035035030041c141c60b414106010103026100402807910740110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770935809 1250 770934559 770934569
    0xc11280806070906050915070303020d06050306070e0111010b09041505100e19060801020f0705060f01080307020d03021c200f100b04150b04030209150918031b010c0207 74
    0x6145a051844000d80000307498844c0108100d000241d12816480700b40c88469021040200d40f91a10b14515000c0c4c00394001c00e199000040c6060400a0743d407030001142801003000f41c4400c0148000384004540078070404024050940d264404892980c50341c1c03581c18883d034011814a00700c010804008415580041d00300c0711181803d980512031505404200c58001c08100d5006c00c1513008410614040c10440e8410150340d4404126488801720000080c0750040c441c0003a10102d58801c41d15044e100000e014441d8503510500c1080c005007400e020200f80c02e8060b004030307442c002c1e07082101c44400d80b00c40c2c072840010341e810720040c0b6030788401400d980c0c20f404108064041601401a0317a03a9038506840081e43c0741e9200c0c1050400354580364080100c40f60200396141da0b66440300e8111425500602c4100d0240e06440d000441c1501008408940c0120081109003a9102d00295042c8503110345480350300303030100b0802074200014005110368800b1149002044400709842c0c0a03040200c95882 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770937059 1250 770935809 770935813
    0x30f04030f0e0907050c15100f050603160311040305010606020a0c15020606040c03020f0d0e060601020325060e03030a0b030f03040f03081303020a080105040b1b07030c112808 77
    0x50789010f659510f0700d00380e02c80d00c41d00e005038036a9032503c03000303241c86181440341e0003007074a00041c003c1c8103115050354000e44050342084040c0c0d558800c1400303034503c030403201e031141c98003c0c4910480c2c551190304410865103900c0c0c1c8e001d0a03d80c50780c8400c1d00312850760b03010701c0240e072081092004004191100308000c05442e0fa901d12191101c490103501d0b00030060005119643d584074078a03510303000c4c0d8140c40ca01001010459242e040034280c030b00040001c84e4040030f4510407200014103542c0300000701c50760b1182008222980400001024010f0400403404949c000d44650f171201d8105c1c0b080020758030032402d034074000c140c08000c107090500b0403400f8004c451058104101c203220030818010f00b402141c0c0d001c80125a907501000b065019180030380c00003940100350b54400a201c110541000d0301030b03401402c0200240c1c690344040038601c900000040840c00013404000c011a000780044480c0303038040c845600e842e114417000035410200041c12805c1c894500c0380d1945024040110500180c410350740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770938309 1250 770937059 770937077
    0x306030b1b070b0a150e0906090106150c26030a0c03270203161701050f0103020a120203070e0903120108030f160c0b0a030c0e101b060e03030f04030f 66
    0x1035a501c1c82c416080b0207041140e8260100e10106003aa0183d1001e2a4910403000c09503101e5002512400007543d00d40c929214070302c0403501030074061180310200c84042e24040c0c600002a4401d07101c0d005580302c20348001008068100d07100b8500700150742c44945030042d0a41d40d02d80403a10004030340440c2c1e0290100352030007807a00120a0208400005980c0007e0304030039130f038003500c006407800300c00c4a120000000c5110b4000f98249a0030100c0303a030550181c000b44001d55840040f00081a400d100c0071350703c10726070001040703020009103c045d92140007605880005403280d07480c903140c071411342e00f002844d40001502311450824010386e44c050110500070b50701c2d110314180c00e8130300f9016680e101006000e20b0a001c5080110400004004040d442140c4ea01c40050307100c05030041408400349004900280500505480e000b02c0c0d8140722201916015120040514920003410026504032100342d510b6484000e40c00c0c1c2000618410003107110721020600c0e080c038000b003a50a000e14080280443c2d11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770939559 1250 770938309 770938351
    0x40b1b0d020c061c1116020108160e060a02011404080a09050a0f0306050606071202070518070c0b13050a0602130509010305030409270303050f18100902040204150306030b 75
    0x901103e400380880520013001060307440e041c00090920712905a40c0200c0018025095404541101e0301c85000340c85641e03580da507224280c1c940402e181c0c1104005500e1203c032244928102028010600040c070000030380048050712050025002c0d41c09035009031001c41e45000d40340d4001503100140400303542100202d4900341002091a01c217010090250340c445000441645540080d94101900010505610366030390602a483e421a40281c90058401c1c0b07242c14aa07003280e008190044c1245d030b03070385ea241c18480d417074080c6442c0b07001c2c023041a81842e0345111404204100546200c00d4042da50060f900c9501d0702c0c02c000d850000f0b0740b0150180c09000010004a580803007994100ca103a5070020804000c0c0306456000000c0070381500c42c030f203880040407400b41941a800b8a201c0c3c150602e42d04c0d030b02d80b20020443d040b2070484104000e41c0d407140380e050418504903081000141c2c400b80004d420192280022100035110014010000ea40d80404100f480036030100c80350441d10407590030105181d06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770940809 1250 770939559 770939569
    0x42102151b0702030d27081c23030f0a0905030a0e0103060905090f100203090d2105040b070201152301091503060e09070e010614040b1b0d020c 63
    0x1400c50441220540007404224481d1003203412443d4010b0984d003022002905c040d040740e000c189820018103040c8071600400f188454180280c540040083c80081009004242c0c00710301c5085003400c220f20448803c0011032490f44500d04980700001c0b0a03241d00d405005003021403001010020024100500040407a40c003204664030f091a9142c01401005480016405400140e20806003107280ca42000201d00380030842a420141c0c070b2042d223100800c050446003c1c6d010548511009030407072040308041c580504075030400703800c00042403518003480340b400404584048a05542c1d0785115020012a1982071151070031041e80002c4003900c407420b107544149400001e01d0703200c44603545014001000c6c3e00400a440c000c0884c094a94010145040f009005e8002485031450314117086020400407440890810700fa2803085090084581c40c100741264a0328048107001c0100c2d00410020605c81c112000401042c1909605111503d19903502c0b1031030310102c96107810846d044409044410355030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770942059 1250 770940809 770940811
    0x60308090d08131d061504091d0f010c110a0b01060809010f060902091503010e060405041e06060509090f1b0102100e0d03061703042c04210215 63
    0x1e4030742049030303240c1d032400b40c0070b03440350307590b4500c049002820000300680b0480750762003201e4202a0704030490f2945c4c0244140746902c0180180d045605100900074074499500c00c0344000f103030800850491000038805814000f00080082d4281d4452000940641c2c10002d60300d4003413a1480207007407410b25601e90058808040c081e95041190b0741c070204420704801d4000752216140c1e080c04120301c1e951080c0440003580700031000c03030044a10720082050f2499100651f4122201030401c0c41d0655502410800108001441241c20b081c120300b404001d05145280c000250340320380c0380010f0550400d401c00c01c0c00c5c000100070030b40e84c1d4445c078000302101c1c0d004101165080e03801b141942c0d242c02d954005030704000090003103e02a5251413989c9101490004688640552940741004240d0300d881440c0200c560080c0750402c3c03a401004100700307070ba00e000496108041064039a48072415200702f00203c403107080e079081e50400e40e980621107114041d2500650380e080725000810401c1a80001c0d00e0142c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770943309 1250 770942059 770942077
    0x504060512060a02030703060e16030b040b030a0209060a03080f130b0304050c01030c020304181a0d020306071b080706090215030105010f0e060d0213141503040602090f0a09090510060308 82
    0x44c0120109040034000d4004074060550141d00c25500d240000440300e03618100052200024107003281c4103100e0034940300d62817103207001401820786891181c0a10440f02d00c06014550080a00c602c008081a04000a003c48541c00e050f965550200c403c00702c504e40b0050b03040200c10401c10014400020800550b4a0340b5131070a0801040c040241c06007607045009030790180410f0765186016404141c042e80c4680a5802462481b00d41d80d8135103030900c611004024002034056102101042e81c0a00818440c060080c08044030b078007696a83e0b95030340598110800842c0c0c0f4a031600115811881c01d000651001036005801c0c1d8155031403d00000c280901541820701840041c1c00401100e40740c60040b980303e0203403070b042959264002c40d2101050300d858400d0a104ca940380c0c1c61003141d403234480c940144061406082c1c1d81580c680381c58040c002e50040440c6540086480c0d409402a01c0d51030040d0024416150000f491854070700300b05060003c0704140607405071410700240300181451090707580b412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770944559 1250 770943309 770943311
    0x708030d0c0e0d0b040c0e0c1b0a05070e0907081603020f010c050c01030b040207050f06010326090418150f0e0c09011203050c06190606050c0706030e070b0f040504060512060a 77
    0x2460306c1c18500d5514415421030030b041c100c140b00b00210a401c80c2c0060202d4820080f071b0440e050f04101503a07441b00c0f40c00700d00034025040f840f810001c4c83c42c01224030f40c000f0080010707511a250b80d90b1a003454811a002030100311004181c007001545054001200b00722000c0c00c2440080185a54180d1555510011541415580c10001c001038480351b058890042e0700108555100e0b050010641c3d65500921007202c020785a0404021810407100030040c1d0448242c0c6600d00742080041000f01824080c540c1040000d01c5680c0000824141e40030445000072034100000c01a921088900031784010103040e9829900c400504080d0740c54085106044a54400b8143c00b0320440345000c44984c0b0402009500c148a91001e222419409404001c99180c07000d40800150303944a00c207541038054002c4000c841c0d00068820081240a40c01194502108006540140383c40d062030b010150044445903812040c041018069400c182c401e0902522084175000340d002084d056050340c40d90020b20002840d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770945809 1250 770944559 770944561
    0x8010221090c040f0203040611070c2922090c0905040518030301300f03080924040c06051204031404051e040f06051507140708030d0c0e0d0b 62
    0x4a0002c1c84000104400108148040002c030000c01c0060b400075941980c05030314008000e0030009182d0212001c0e540d100d40301d9a10586030501c0950300c1c9604c40305145004401c01c0e01c003010081598000d06903001403d002000d00c0510401d07207142244c4940004025525204403140d400350030103404000c6031800c40d800b107510744c0c8030280507007221460018105184404400400c0c0517410100305d01d4820354501100c03d004030441c2040340c0000c1a442e000d005640802070360301c00b00f0321485c41c0c0c07903008105100700d032948412400c0c120080004050008013559082c024401007151007501d4070000d0402d460500c3c1007403900d80e141601e4100c0a00700409100154459400c0c004041c0c050300d0003030030010140d50b1041d5030050f41d43d18800400811074415884d02c4031074840e032242403144500341c400c0500140e44503c501501d541c069401480d0503220884850b0143c0340b140010050721003d0710f18540551307128200042032005903841c008101040c00412008840d641e150141c00c00b40d09604400c400c0c101e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770947059 1250 770945809 770945821
    0xa0308100b1c110a050406030b090f010303032409060f0803030405280b010b0304020414190f18050c09090c030613060f0c051c05060609040c021905010507030608010221 74
    0x5040c6420005483c0303602013030b03180b9400d030090042c00032201039480c04d221544580b01044540403046800e07407140d0b210b000050000c01d10903070010f1844034200e00406119515107130300c3c03245014594082c0701c21a46030740051100401840d04080184088002903003542015510180c5442e048040b0751450440c0c00b9845882211580002c60783c5500303e4444110355858002e501d915501c204c401340d002d10f080c140c5c980e1861030003038441886000343d4280b07500c0015400420001a01c0a0100400b5070703900c1e91030f9422501c0204140300380141c4183d004007241e02c0c02005201c040c04009064020903000ba40301040c5945010071481c6c3d0040202c003140c80305544900c1c01a00400300c1c00000000c05103411503134825190000020f000300d11401c1e0a0f02d08204911200a09451044500b65000701d0280803101d03803410150807600105181340140ca80a905d10b4806446d82c41e03c1c6a0295178030b81d1a030092000316034140c4100300203000e48070000d525085d0711114014902082d00786503056500e0100008407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770948309 1250 770947059 770947061
    0x1140103023115080c0112020d020d14090c06071205030406061706151e0d050705030a050c0406140102032208030c2803081b0415020a0308100b1c 64
    0x50203484015101c0c5001c16007042c640c000300143c1900204214200c840480c184500140d45803007524160b441180d0a05415040c201039040400000340480c3c080c003046034449080c1c0070300346007030300454801081480c00307042e541d02d425400f4540b070380101030802200c0c02240d49001c0f505090012410401c0d540e84861400c08020b0005074003915608440d00016614008049a414020400c0c008140e40c0d82500381d003040101495100781c0c0146010f0146907110034109942540c50942c040c006441c08181e44a002c203042144404048a940c1c1090784d00187c00c2ca824800c2d18041c3c090a000b07004800d46070300020350f580c81034030041c00207010700000c260b05203620050002c0207000071006803603c0c0e9801d00000d0350f40c0d000c18404d8440701c010018030750f00d40e400d4000350100400d4241d0758440c00c1d916480218110082810400195908200700215182072859403045007031034aa8000c1082560b182001032503040c0182940c11902082d180801402c1d024106640010340052441d001c001c4003501c0300c2c3c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770949559 1250 770948309 770948359
    0x10120b07110c06071109070f0912020f0301060602071802070c1223030403150b0d12050403080a050705150123011710030c0906050d1212050406020a020706020114010302 74
    0x1503480480010070314108000c09049076150705c0c06440f081c4c007640380c02c58241d40300072090501a0004840385020400302d000301c40054560380c000b0300304206100e0500042030a4502c01e40207140903901209007001109011b0440449001c500341d41141844802c0c0c0d142e440840440c40f5120020f225000098144040070005411142d00305524140740341e03103407110795241c3c0c10030b12007515624803240284552031010700400301c1d5031b60024050040c1c1c0300701d50340d035011f224000d04400080206c14080032000864410082402c00030588885880d0511132600741d141054541d01050745105110040000a4000726044002c02c10440e15072106005ca00048600600607402189410610001e11083c0003210b8031610a5a00071510360b040c0c0ca854a82840588003903203e030710380280390280c0c0640412091912081072002a10303180c5c0c05008182000c00075601d017540e0540d05503500040c082110b90b0100801802001c3d80c1c00284040350304807807501d084200c1480040c0c020024004003140c0803202c0c480e04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770950809 1250 770949559 770949583
    0x306011203050c1006090c020105091c050c01150317093007090c0206060d0809010c06061521180f0212061009110403240b0a0b0310120b0711 62
    0x100c605110089000000e817a161040c250100e04d0020b945009038418021a4403405580b0300502c040074032506080b1030314003000041010400148101c5018407828025141d0500d561a880c0b03003002d04508000118039150042d42e00000c008205542594480d00c811140c1c07030b031103143d01a076005403c2901c510074030300c0180d41c0b00f9180245c442c08108078403035502c031481900e241c1d82103461076520300c000c0c001400b11900c000b40181d1005d103e0301d680c940c402c1e44c00b801113920901c00031510b40d079540814480180c0581109010034004007503981c0001c0c2c002205400d440503003509202c1005018129559610400720141101c50111885810340d22091800400f1180810480c1c00c5450301c090301e2100100302d07000307501180d81041d000b0b030040f14034002540c0650b80c02c0143c99410458021188569083c810b2104034016107a4602403044c3c0d5a14803007400920300d1a10b265601d01d0012000460107246030400e00c136007280c0001e8000030031084040107038040f9041c00d200350800b49040b2514a006031100f04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770952059 1250 770950809 770950813
    0x2040303031d01050106020307120c06090f17090f0d210c050f0c060f0c07030203030a1d0604150f0201090b1501080a0c05030a0c0909021b06070504050306011203050c 73
    0x208056240c0e00c0341c44468611186148a2103103a549142604d1080c8601c100680c03040c000c01010a8044141031032040707541c20300303e0035480d450766290151000c81038140e6007500e0090305481030260b0312480070b4200b103d03004110b15101c100c4000030012171641b40403030f00890100c0c01020801441c0c103201c0341c00c580e40000c0483c070030751007420041204040e5581225640105403e14100017400211220400d00003850281455071042c0c020b0b51641200041c04164400c0000c0007000d61814401400c1c030168a5072618400300300c07801c071008000d408098031401110704110402c011107028000300360540c101e1515103507075403c103030040740074091041002d810902c031f1505001c0d5558940c1081d02d1501803c1e00e800790b29580c0d4a581404076a503040190010074410400101308425951060740170b41840c0c184501d6103611001c82100700d802188600d040900b1029040c0000b00d03040003030590003c1ca43c80c0281c82c082c2040c0101e03454810600c51001ea00786d00b003443c07808040c018002d48940d95440c2c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770953309 1250 770952059 770952067
    0xf030706202505031213050904061b030f06050109030b01030b09031308211804050c12100618032109030f0c05011b0c050609150c010b0f0603011503050705090402 71
    0x250b5121554054442e4a2080c4102c44050110f410740805031820390b181d0000d00c21500389010284204018000c0c400c4801d2270f641c40003051a2000c00180d130031204d1641d50b00162a071410004101200c50300d03000780d41440119241000050000101c4a0550341d01c6449001581c40b412002480c1d4007a6046840100e071450703c3c082021364001a00d0b604c2841103103c070b1009000681c1e0421968442d00f03030741d0310801500740008007507802c040e0402c40e00f019a155881e860214841041034176007409442c3e014108548650030030a5139407051411100311003a8110154451459480d141360030102e0b134881c4101c03150520603031402401022440011500032a480c4000030140ca42010b01054500505010510110708212194240c5c00c421314840d07030042121070190700b0141001140e401100c402c0c0d61083c000321410300d941d079125019210006a8400104130346c014081008450307200302950a00803841400104840e07407035003203658a6601c0a00740050945c0310340400722840c0c0f01c0c4000e8280c000780006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770954559 1250 770953309 770953363
    0xf0609061903060926120c030c09040b03071a0712020102120a0902150a02010207030809010203090a030302090402041205060f070329030a0c06120b190618081501050f03070620 77
    0x5e4000c203e00e01031108800380655031444070000f6800300761002101e110050140400c0360170541d0007480e68100060444600c01da40e1480446015100c00d00c508810b00080790701c0007000311f542c501d408458500d0009500f0040100800d988580f03000f007113164440e807101550010340d125140100080c1d01c8034940199100064640a4040d620407501100042c207a5000120315807410f00c29640500b02e90406410045125201103002e5002400c0722030380701d6420000059180f54003200010301d140310b0405815a840c00500c2c030000010b00811042c141402d0210581d4101003821003101008881034030030782c0044600c0d003c01c1c9800e51101005102c2d0520402c04641305810041c0480007540c552000e00140c9a280184600300c0c443c0c141040200e14110b4046c0043d50288000301d08041c11708442c0c0a06559a50040c0c0c5000b200a00d820301c2449024014465400c0003c1d044c2e44004003a00280502840d24000400c05694401203868009620b6a04040030000b0b200c0b02458110f460f003041d80380c203400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770955809 1250 770954559 770954633
    0x1b020301060b03040506130305040b0705010f050405010b01141201150e0d03020c0a0f051e130c0801090c170c03070e04020705150702070e0a18020303030f06090619030609 75
    0x25030b0b080d500d030306c0b07008005030345d0800760500001c015501d9502c450070549061800031050704a0401260b00e035403101400030340c1800620038584a030b4010300011881441c500005000c840c4540c1142c411501c0400900c1c40120b614080d860448201c0c0955441c5090742e044122011005016015400001c039600802415400268650104012a030300040240e960841c1c0007540c2d007612459070020310701210135440c580c401e4110f003e020809400d4420a8140824100c215444041c42d070b00401c011170700611007489a8420064004c8036402c2c2501000100210035100d0140101f031034520220000002d10021302c5000648220b038009070040d9118851890304030780300c10038100c041c1ca0103030b00c130000a030241c0c2c070024821003121b0074043c845d1104d0b101c2da42c2c100c000d801038840f0210b070300003548a84030051314200000c43c49101800003044070b506080c82000f0300e0b110041d2400344220003039454280045840489481280d6000070300249089281c1b80a141da0000410080403118099003801c00c20541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770957059 1250 770955809 770955811
    0x15150924100e040c0e0a08070819140a081c0533060f0d05070824010903020a0e06010f02070614070f02120a0b0c1e0c1005240406080309011b020301060b03 68
    0x311401c0d06d4050320395000503070b101d229215503102c0313901c115000d40c90080b02e50000421640980b8810080c2050a15680c0c80d00001c01c10484190500182a52010180c0480614051441034041c019070410301c000140b2501a5926041d00001c03182d4800490a10003060308081c0300c001d00703140d031038000080441100f90000d2080c008080c1c1007034000b50004c6e05c141d81c5035215000340d88005800480005052050700001003025041c803800c24004000340c0d82d203c00304170007441070a00159152502d00001130031f101141d00820250f40c00700d03005000c00b50304084241c400b991380300600f0391503031428107000c0301d00707075501001a4002404101c94403540300c01044007034030b080c01444681000e84416003090080d1007210402d010401403154a404180d0039000103019000403541121542803551031010100c81094808249181034404001c100c0ea1703a41054980813103044804010080c90021000d889102d0301d05503a042040e04100d8020811b0014203c0c0007498000d0001c010b80c0e03803110503240300703584 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770958309 1250 770957059 770957087
    0x50306060c010e01110912010506091303090306051003031805030601061107170102040302030610051012020909070216050301060e07080414030412020109170a021215150924100e040c 80
    0x28416811400001c0c0c1400b40c640204006003071003945030748040004cc0403002c164000c030208030390700500001280311030007094080c030030051402c0030151540c603001c0c20b50209a440704201d5200030808010554006c03880b18111542814030768400341e001807075107007455031580003078450074010402c0d803025000c1503003d44141d0b4826011600e280d29200c001a00b0386041d441440e92001c007201048404610855685500000d284d0016040507461000500309004c105c65040c0141e10031a202c0c00c0c0c90880c019508000c181c150000c020880c241982c01c02c00b00b9000704a5000e00082c0700100e010461016451180100f060056070f48503622106a00480700c1b81210590000c1d0500d040400c25888107484445c2410388031000f880060704035801d0012080c1c80031441d03c441d006002001307800c078112416682c410401c0c542009004101d05007005122a0040c0c645594a5908504001c07090200c0a400e1130283c0219940c05201d80080710464242840031045a0450304240701d94450a0300014441c808034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770959559 1250 770958309 770958319
    0x6030213061d13110309030318071a0706140f040203100b01080610050c070b12010b0f070b07110d030b03010c0e15070f081b011406210f060415060906030201050306060c010e011109 79
    0x580590301e2070340e030b010b550003802f010341c00d04140f00302c00780c01c0c42000b840784c948510b07070101d1415007401c40b040c0302250456040d00003034006410042185001c1c09940c0c62070780301c04002c2084942e00c20000f00754042c0208228010004a0308103040a4001d2080e219512044001c071680503440700c5c86903003580c020039001e8040e0300d030301030010600c149148103a0724030511401c103160810046466003180380720040e00c540306104c01500c550440c040c05202d440107407103164034046002e1016030181800c41d002408902d040001c4854400419031360003110012141c6c81004517070300c1c1d40d8142010703480403400c520010100400040c41402403410300c840d10312900c2c14107008001080001001200181301214003e40c00a01840541c0e05c5224180071110a05004002c031419800e03070440540c5460f005440c04e5506891001810101c040140185005003509200501141c1d03d56070002c3e1050201901d242d02c5208082800b1181e24002d42c0324038001c03114600280030381c0c0d90b6116a00c11035030280122070b000d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770960809 1250 770959559 770959591
    0x40504051c17010e0c2a010e0102070507140906010f020c041803080907031112100603030c021f020a080a05190f02011103060d02270106030213061d131103090303 71
    0x20821908138a88603005030442145840d9540b0100d2800f000d510075150100802c2448492605a091150511a000c01c00005035118110305020b0b1611100e940081080c140351002904030381c582400b1183c010300d082c00d0066907842e00f00760690070004c00f40b0119401910f009074031020110040340554081c1d001e5101d000403901d81c1003900340c8428050001a01444c1c5564a4202900708101c800310766000c001c09441c44c0012055849040e038417258019400540a140c103a015407a0440e918042803124880c4480319903c40e050103174071400070b41000781c03c14070302045030f0300c1d0a802141118071240244980311380d111400b55001c1e00001401307501000541c40c040101103818020411a0b0080ca0010103440c0b80300d96035800c0141801c01207510041d800072401000003101d00d003910746406088203840c0507032100000700f040702803000d036a48080c0401c05003141c0c0100b0000300390a01221980103a80c010b940040b50180310000c0c166182014411090000c104036503c007000c0042c50251000851200e04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770962059 1250 770960809 770960819
    0x150c04091b140307081803040801020301030804052d0f010c02130c0e0103090b060907030221150f0904020910121a0604050601170a0b090a0b0a06021b040504051c1701 73
    0xd580004c48088011074151000b181401240e5200380302d5055200c2c1c00c40f0700c0c00b902c074180142640c000380d1003161580004074043c0030b10720b0100e40a0ba041d8441036061103001d006901114446403601105a01400c889903202046034400c030400901c854000e030002500d206498800b800500c100b001600000d1101c40485c24258440d0050790724450700008083c2060b1201d20802500500180802d001e26500300103c400300c1003202d441d14182d400742c0f00121103900d4041c0101059210000020b407007519080038102c459034455440542290301941e85424580c6c91480030810001183c1114084e4440514000308200c09031051503c0c1c0c404940c0d03000c180d929110240005d0b50300a540aa0101e074082c0c001001141035203840d075510105500d00403844906000104100c0c071010794104480701d44402c009116130806540c050001c110f20303c01003e5000103158000b400b202001800c5205d10b4480c0e01190501808000050030014003100302c3c01c01d0902450040d000ca80814043c003290f8244a00000d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770963309 1250 770962059 770962097
    0xf08030a0c0914090916030308010305070504060b1206010201090533010503070b03090a0f03090e0709050604120f02040f022104030519110d020607030e030309150c04091b 75
    0x401c48004502400c8055803420822080040013401e0b54141d00c214400a41004c17480071206d8011800b80d25101819411814400c1c14085e0381d81140e0b000b00e003400703010005080618105c0e445c40e0f10031020455240c5030000100d000d0030705080b02400c1381c03040b40c84810010300e80c207548131001c840d26500c0c1c42420021b00f000c86070611003449031541c1030300410030800240342c0e0a001940e11040540560360891110f80e550701c0040405001680010302c500b4090155a280c80103c640000b01420010076130f41c9080002072042c4624000e500356900803001000410144843d20600f40364001e006001650801c041c0d01e00a411080da2a21040301c1c180c40040703c030f801c440c00b039070160750503a0b641ca00d13007441000031685a5500303408082c00c20100407010020601c042c00b0481c01e64115034050510b5040c000401425100c0744800740025070130030818040e0b40c0d40000b03140f8008224000e170702c203101e0b62943d0114110f4052035100c0c41c0780e2130400042804035440e04511944403000d507104c060040504411000f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770964559 1250 770963309 770963327
    0x120628050109050f1c03090b070309180203040f030e0301141819050a03080c071a2e03061a10090e07050a1706060d0c0203280207060315030f08030a0c 66
    0x40e410680300002e28a5041301c80c030401e074004d801b81c104451a207607103088041940c1d101c060281c0c00220f110074284030281c0c043d03801020a24090505505600303003603c0e0b1241d22141104014140890b03512a000711340c5082d000080c244182c49136419151909210000f0115a1605805030034003c0d80d010352082142503170500c00c81c0da00a801044281001d660a80780c4541c050300c00000300c1d40501c0014000745e07094031000d4400d00c40c0f4030009034505110060001c0f409039101105500000305000b40c00080001c200c4100b100e4000501082280c00b901e0038039000191036503141c0d045a10110355001064000703040404072809120344003201e81d1003400407242402181110000285510000c81c00c60308034058207900407100402c4117103000d181c0c80120003100e413007074001c4002d60004100290b201070080039400844010039601c0980c0c0c3c200c220001d41b20b513158092030040c5076842d03000350304140c4c218481a000e541d009071065020305d01c5050048161308111035020340542444d81c800d900b14400c100036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770965809 1250 770964559 770964589
    0x2460f0b0c032203060504050a0c0504020f0d0902040f050f010303080c09100c11100c0605010b19080a23041401060305120f0f07060914060c12062805010905 69
    0x140d410000f10104030114500c100c2d01c120101daa040001002044251003141d010b41c0c85071000341510403d51501a07404031555101034030691042c00a4030300c110707001c800c580b1030580080d000201501c06100240007880040c0303546040c04d01d031404000020040c410f03e641601d001e500c4040240c0d6400030b10480510660f00d01c1c50b0886100410580400c1c06403070000310b12407007542459004114400070602c010072055169001a804e6003030002841520304c21680500390354008140f40030880031540c0c07401250b103001e0400b004007000c009500d00c0c200d68011b070000b05032484005000c0b00703401c2c002c6a00c5101520300359446c4050f0428181504070510451302103a5100c000b420510110b00d511aa00c0e40181d100c860340008200b10744201180c0302001010210b00c541c50019800000f42020032000c01849411461751b4051400e01a048128900b44d030203280e800c0307903022125503400011a101402c00403003c040240c1c00c0401780700c904035034449c0505840081c4d0740d90140035510020400910040c0c203c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770967059 1250 770965809 770965813
    0xa120f0b150f12100c05030105040b030a050601030b180105010915060305040209160203040803070501060305070b0f0f09041409340b0306040914010209010207060c02460f0b0c 77
    0x1680500e401c1c50141c0c1c018020f086000d40e03200051994a003010389501800e4400094400001440b003841c0520032503c00301019001401010407036036900799118018003004c0c281d0f40301c4600146041c545001c6400c00008035000138401c95a44896001c00380580c05140e0002c001c0c613501c00718455100c2d20441707108640042c6100d9003611107056043c1142001583d110442c0001c0201080a110400003000f00314070440000944500e14180341d82496250b410021441c5420000c1481c0c000d500020790300c414609640c031540d11643c041c000b600408a030b580000002c5c1d858820080d0720380000c245060320090301c2e52002680c1d001454502d1500d80003008000c846240c0e840141b18485003030000d158071440c003800024886003c0d4455445103901c105440b85169000a03040780d070355a05001a40041000d8104101075002c40e6000585c1c2d0407042c400740b08400240c47e02c117210044007070b5154224503103200050080e640111107020a900d498020800c00440b4400c4c000703000068a0101c400340c441c0240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770968309 1250 770967059 770967079
    0x31603170a1118031c0809010e032b0204050a030f02030c01020c06180f06070b0403090e04030905060717040f05030c18010510020a0813090507030603030206150a120f0b15 75
    0x82002040c1c0b24056550103100701780b800501c21070102050082e1032031076160a41c00c2c3c41c01340c0a2609456008800d103c0c0f6810038000c0018410329030b08201c03101424050050090034152504030001d0080e5480144d200d50f0b00740000003489542c0c0720503c2c40354020760a441044811200580e81c3c0d22101c603515400550070404004c0c41c000c0e80030f450728070400040282c06140d2802c1e001800076081188140c1c5c070751501a051104060f040010280140a690b100521600c0c0c5901e020b0410307031a61150601506e0006200010014840c00305081c160601020310385441c2c942210705049c4c9030790b014080c060301c16016a00c00318585170b00d1020704215000c512400680c282401e0140e1443c001c4441400d52060700303115000121100080c150301c0d0250310000c400a890101500c0640300b0140004081c9441c1900a02c0429400314000e540038241106880e41501242c020500180d03480c1e01009418080d071000c1c80c20080241202c0313544a00904074a4500e0700c614502c03684d86880a030002e9840f0103444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770969559 1250 770968309 770968327
    0x50f0a20090f060423030f0c0102034602070506040b090409020d0503070516050f010c0816240c2615100305010510140f0c031603170a11 60
    0x5007102a240e00b01a045500b007076030790014002404a0414540721001100c03003251620300301004581140d03138049008000400350f03100040d4603841780700d200c2141e078030f42144003500160301c3d502d103e00c0d19080b0007841942c07100e1607441414036400c0451200018054140d00007803600d00001031320280c3c3c0a00e400c2c5450309690808200003410811001c0303030042e040c00d1005000c0f540c1403001d804142c2c0103901401c0d8090b0142c0400e8460b1180340c010701d200d151528465241664441040a40c29038018907003541e980f01d0201c1d940c0306c3c000390780004108600d03004c00c00040002045109401d0080c010007030100b0300d483d540a6403c4956040740340031403044e0800311202c2070303640d4100582188070200085016091030010032800d505056900d0301017033311200100500c0c00e20f0401c5800012051500d403461181e00c251089062240d50015125040040780400042806000710380c0c0e2958000881401c0d0507540c40d000d01134501040812414100d080c0c000351035140c00f4002c0080c440c0c2c401d244076140400350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770970809 1250 770969559 770969569
    0x90d02100902010c0c0303090e070801032a0b1b010f0b0d08090a0e1312030c0e0121060609150302070803040f0c050402181302070201020c0909010906050f0a2009 71
    0x1c00d40680c100070a040711180130030314440d48100518020303907503400c0d00da062181c40c441040000d0020b20403c801c0000400200c3d0100c4120f9921403030428014800c0440c0c084650300703038609600184041c0c4800290004115107010040104500c9080240078034141211940d0480c0d05541036541c0201c003042146000503409002401c101d94003c0c407409200345c0710b05050054610456000c07094140000c8807030184070600340f420700c081ca0381d86400d102803005010010400c00c601d0040300c4c140b20120114080d0340c491140307000c0100345a00b4041001c15524600100410030600c55444910f08071000f440050b4413a0086070740c1d42c0e0700440194074640351662615168030f204442a980c0b00d040c040080755550f9640014844000090780c490341c035201078000c12002c44102d1804150b031610411101c030041c1d801003000c602c418411a201240d40c0c0d503000045014000d8560010711a030300c4c00c020060340341c00e800c541ca030044200074420000390050395004d602a0032907480c01640410140402d460500d42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770972059 1250 770970809 770970821
    0x3070618350301150201050f01180e030c03070302061006080f04200a0b0307120608100203180102221203080109020f13030c090b10050403020618030a0b060405090d0210 74
    0x40605880701080ca09428420190020b8005010402c801a52202e64642c2400303425045204003295036150b526100500742c40058202c000e104c020345800c441c060754042841078900c000017a03c00e07250f4400341458020b44034081100d10001050b40d42d0004a21248600c900a01c103141505041c146600c40b5102e2482d2000706180c0e900b444400c013101010340d522210084801400c6000c04640c90b4107244a01512100034003608200c46864017030304120314140007407031441c00800d0322001a525100c4040170000180d03038030010081036000080340b01d900d10aa28050711280040742001005075104c0286081135120110041d0000d100d0380014002000b80380e0050240085840c44e10f4038100c03507035145642480b0107a10558000c0500d69041050240038080d0030746c0e000703040b5078030b803004031100d00054070758082c50001900074003000c01d98882d10000c9a04030f544920000b41140c5c0c0f240c06914202d40c1e0040b0440d145c034052800d02c004128201c0c070001c1c07044c160882d1a0054086403805201920040c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770973309 1250 770972059 770972123
    0x1204030e040905030705010e0741181006080712050c04080f0f0706050702090a020a0e0a0b07060c020f0a020d020a0e010e01080114040b040209040c09020c03070618 72
    0x181d900b2060000440030001014054490000418842e83e12000c2500b0000d20f50f1205445180c215420303002c0820380740b0340500d04002c0d2070b01c140c13004002c12105110707844003550300c60b04008000b41081904920001191054000d903525102c1c664854100b10b86041c070940711407010808400145d08030302c01e5508030981c4040140a038a04040e03035038420310724041c60585107162a401030000e81041c00b40a0101c5400380816042082c500a031980c0411601c0c00d00801d41880580d000c11480500740c07150081c2d40f140940103100684c5c1e20384903080d80703d896200700d41c04c4800f24503020340036450500215100f42c00b4850729016043d110459000d0101d01c150f002000c036400681c0a8001c2a0301a400e141c00d03000e0401840d40601030340c106089982150500f20120300b811190008200c002071400007069440356041d100c4000c40c0c0c44903d0710b61112242ca40065503140c1c0080b441042150b00080600902e0f80140014071401c0410f0500c2c444c0f50120006c040e0034042c2d200e046254112034072182a42d008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770974559 1250 770973309 770973311
    0x507060209012304170313031407051905030c150f0f0f030424090c1404181b09060807090b010203070b040b040204050c28030f0609140c1204030e04 65
    0x562030384055120340c00f001803082480b4002c1010700c580740e510100f0f8125840c1c910000c6282800345256122508624840240720306240e01c0c40302e01104c000c1c41508001c086c09800b0040c11039000b41613007000f481030300503a4007902c50b590807a1924a0850081c180064503c647c05250003038042031710300c02d54052100d810002c81c0c100141c841140c884070003544030328010341d040d004803a40c0b400c5101032040108114103041e42000360440100302c044500404491101c40d000c00000c04072004134000d0400301c1103524544482080c0d81083c0140001010144003c0b0005503451546078154001140c20a0154803126480b5080134040905141e0000c512030405004903400e1041c25036610000400031a405ca0f18941b0402c184021810b05000d00c40d041000c00202034100750b140c41ca00d154080010010354030b076407140d1341a40500e50080d4012044254042014011580c50f0012074002e452910300880070020a6000652074900103001d07180001c1014070303040c8049c4c07240e4074205d400011403002c0030792103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770975809 1250 770974559 770974577
    0x306011d0d021c0b010614090108150409030e010207090606050d0506010c08030a0f11030402011b020406081e0d0201061d04020a0f06081e0112030302030c0c0718061401050706020901 80
    0x360f5a060780d5040b030b0040a084500c041c900910300052040b0040c0c1c008803d02c6070090b0a40c5200e602e95068840070710007840c110500790703103411500303030802c03032a801003500720740f43c80800b6043c10b80c0034030207092000c02130702118066662682c40500700c845d184141800100c003030142900c41601a006160410700500d8112914189507c03241d000b98000d66482c2c420b01c0d0345840d210b50381c8041e13001d202c2c10a45010304050840c03074a500040d040c0320b8451012151030009a041000719550750703004002500301501141c855001116400c450382280c00c1302c0000c28842c1401541c40300b441400b03400140c917401081903007412140020081c9000700135104a80c000078058000c51480a4612150001d203960741d82d1680030f0400320240100d0440c071965618492402e803005000808502e0148100a5414a0010b980c1e59986049203030b28040d17078056044600800034000b66680440c00c0e842101074008008028280d80c8403e100041d400700c0f03e002d4089181440f403c0041542580904401300060409200e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770977059 1250 770975809 770975813
    0x60909050a0209180f010b03010b04120302120d1a030313150507060f06051c05031b0124030c171c030b041415090108030d15031a01030b06060306011d0d 67
    0xc0c01007501000308004204c02c10025a010504085070040440c008582e00d5941808510003403031085005505405034112201070030944200300c0e80224180010506444200d03130034000f40507091000300d00d030804072214481940c902d030120494a5000071749403e06002450501340f818191000d811510170b000060054401158080c021800c8500f15942c001485905100070000d5407221504490740c8401100b2403400082e50000c221049900300395145c802c03804003409014013400d0054800d10390881150690749617104804406404c0d00e110303003c0001c82e6a07d400340302001020154190310140d00100c5091591502900c401980b84003502e804a0b840168201060035103c5250202a404c46031004108100c0496840d03100301074011103005a5651501e02081d0b50b1340900729001800f16510559920301118082d52180210b6112410140341c2d0700e00e070704000c080103003440140c856021203070015600c1d00d001d00c1200e10610058584009152036414424001226000303000d800101045002d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770978309 1250 770977059 770977069
    0x501050117032701021c020607080a0b090411120102070605060306180a0f03170906061507150b030c09070f0207051503182a031b0a0b03090c0d030e030115060909050a0209 75
    0x900740d1b00980051900c0d042c40d000081071602c00512046000b881c0080b00702c543c4d80d42d0940e003034025070003504255010403030400040003007030944103421103517200040c001c0030010300d50041845002c04806880b2030b80e07911060b0411200054039160540c0d000905a18001600513460b108103a00070324101e020b108880005841000341610207400541c0300204001c280d03d8440484164140c0d15840f503402c0c12240d59a0100028480309d41c0c682d6180c07169001038158600700640315903510014071444032070030b110401800580c544141c020060182e07000100342c1c1e0404518104d400c0000088291566a49140414000c2669109401c0501902c404031342c00f1000d10303507003010070710011380c1070f605120202c02054900501106079a0087e25084094101569801100c6c1d046078145c40d202c655a0f600d40a40c1404d088948507078640c0965210b400c01305040c1d101480070704070441603000b08400e00480c080c1150360750307107441004005001810144181e0249800190304031a000c50003500741003c04000403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770979559 1250 770978309 770978353
    0x1502040e040c0b2b0f110d0614090703091b1e08010e06160309080d0519090209070e27070206100302010c061a0d050105011703270102 59
    0x2159060080061200b40450900ba52004181405002c2d181058450541035a1301001060011a401040e9450011480b40d017000400e180519420411110558000052a040441040580707807500001140340f03001d240090b00302c42d100802c2e80d0980d603100d5a0442c003a114014088814020f20441803103000201ca09040140c42c3d1440c41e9400d9803180100301c00343c84500d80c4000d070b5980c107007501d0310700b48072020860540218100f0300c2901c0403021500b05a02810f83e1040081c00305900180244075030510360f00036402992280704402001c80036502e008162146250065841000100410380e858060000d14004e013030050001111103060040000b040c0289150140c01099044100001558148801e0390300100c2c0d801403000d100d065400003011410841d0303004201c1c0381d840c1c80f44c01e210808003000350b050010040c1859a50081490a54003030002849101769000c00c0200100401c1004010740350300c0c01000c164841056450009100104212942c090540c0120a058514820800100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770980809 1250 770979559 770979569
    0xc0604060f0f05040b040215040308040801290108360109050105090a030801050d0809030303040303060f0b090f1908031204030215040b07031a270f04050304060c150204 74
    0x28207003504081c1d200954603511050a01146004100400503900c0d15580383c2180c2c0661700540c80203840170f000c3c80c141c032580d000501550300120700002c1c03503641504031003c01000c1d603484602002c8520720400000c1d0200801030702040200000446110f100545030007511801c4000c60342a00705044411071402103520b08000e641d46a4000c00c0900c08240642d45c1c03c508214020f0980550b580c0300102051010b004462040391056906014017022509070359884000034142ca58034142440e000e00205620f200d440030505a10000260402160003500d5000754040d00440502c002e030310800854140920301c1d4054000d04100c041441401040584002051010000105d0806080107031410040744045040301e04004100320000380e60600f444d8106115044c0801c44407020301e80c14298003500705803242c0148842041800d030a40114064400301c108041d000e0035512480d60f4403c2c0e82e08211006086c0d80e01c20403003000304a101e000700084da14000c480110f035034070700442000142c0c1e000e0303440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770982059 1250 770980809 770980811
    0x4120309110618210a030c0201020a0b01151d2b0c12060b150a05090d15020403030809060c090909160f0503010f0c120e12040b041e05010903080f0c060406 68
    0x10040c45007404c40c0341c07240441003035482c50700d0100441082075481d4410301c0003d042180124182e42164000c000d030106c026880840340c40190384a040341d8558041e02c0c040d44000038000000c4041004010354400d81d050340c0909441c20305a000f5103224122000ea00041005105402d843d00104108600880c040c0c4034000800c0c2024060b400c0510680d29820342581c41007264003412401c64440d4400c84400014034248240c880e0418400610007080030500a0040d803020101840c0c04945a4004c0041da4800d80350140b46440d4404143da880320222900f8104100c1001200d0342841c0500180e80d1003100101154802070000c011300d4600b502c0340d405022110301848081c4840c1c5000e014210703900c0c0c2491002c10400e009064010b00400180185070f4203940d641c0312000407801d00340700c044c04403205824030300e545035030303402c0071015941c418464009401d0301d000c01c02e0149014481841c0442c1d505a45028055096841d280365075071244440e00da001508000c0031080042c14004503100b24000c681c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770983309 1250 770982059 770982097
    0x1b010f18030b13020a0f12020d02060c0607050c071d0a1104120309051201021206130204091e110408030f180d030c0501180f0807020316090506010215041203091106 72
    0x305000210786940c01446c428280c06406210303800d90550001c0320180c0483c0c5000c003d20140c008a0454400c403140010280680700400c05001c0e0003030001d00085001d4811140e290340e8a680300035250300340d9585201c900501001154011100f50400d844a0b07410b207100902d041d9460001c1440100300d0305044000c5040c0d090f00f00054035196606801c440100b400030341c54460740d00c00d0030001e42c00c010495889007421000000050507180d050350080c1410361400c2062070002c240c6440d03803125903081c10581c5400d0004031010350500206480c115140b00d4011420801604601c4901e600106a200c0a400d00700764185803a54490030101e4001e4044e440c4d4001030059404c0060940300a0418424142c04154402c80010002c442c044501504104071903240e400c9480081c1c01d110340e2600c150030400000030f02040405190340001d001303100c01d0b000c13a0b00c509101940c1410001d41210082c1a201040e244404c03681c1c040c4d040324401e5032280740c188082d03c0f10744001400c1ea40124400421b080d075689 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770984559 1250 770983309 770983313
    0x212010b0c071518060f0e12190f0c090912050c19210f170604060504020721030c050327010606180503030f0301061b05030304080a021b010f18030b13 66
    0x9a030f0303001c5e00795840c0001608101c0c0b4005002a01d02d180c0f6540111072481f550341090300c051011007036400c0a1042c11040c240c1b541400d41500b0488801504c05103040e1000280d500214400c08490950154070741400420b80d90b000ea480d5049000c01c1c0402e405680c50f07003623981a0841011603270300d204160490100340c01c1500d8a04107001400800141b00500d181000c500b03800180351407074402803c0c5010345d070303070f0310f41001c1005440e06500c5260440d00108048040040d6070b20800080400790442c4510a01e9220040f02034804540c40200810701c20030204442e065a540408419900c5942c207000c20312401403000d007181c24640c083e00024080c0055820602001c483e404004d2134124015401c1642a1500c50306a00c0180b1442c0103104c2d4072106600b20f40c5a5050703200c42a0380180035292030745402d0503d610141d02c44030380b050040c080c0c001e07144050b80d21094014499401a0768270100020750400686202d114840e01281c5d00e041d912002000695800e00184124058403050490260718 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770985809 1250 770984559 770984597
    0x304150806220903120501240f0e060904020c0f01020309070b070b0f1306090f06051f03022701030c030201080601091802210f190212010b0c0715 64
    0x604180d21960000b0344603980034000d41424482034480c6000040c50912500d415201c0301c0c1103c81c0800e0070350904000090451040c07111140310612035240d44005844003108490b840d00078543c1c00301103441403100c4d884500707245018140410024200620f083c2100607003500d4003804500d9941c26a40020811002c0301040c0045030003018207603916030801c0200da80e114018000103220054052181001a070805c0103070703a200d2441d0b604144200160b8045040c07a03039010000d00c0003550007d09080105030b001d808008601441030031554a03c9200b402c41d800c0200c03041303510303801c2c840e03415000180c10028000d19480d01c1c004e601c43c103120038070146103100141208100608841c14404c4500c010004141641046064042d030711200503070340e51141d1101d1445103010604a824031502804000072640c0003e0364500619040b8070024030703a0400a1011700740d118540681c5d941103040401000b051020348082e242441000094800007601d0350110048040106060301c005140030182442c9824a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770987059 1250 770985809 770985811
    0x3093204020906090d02010201060506071b0609050d0311071e090b0d030c1b09090b0a110f090d02040b0306161e09260706020f12030708060603090c0303041508 70
    0x410365003581090803600024005008803610180912001c904d00011603100794004c4025160040410361580040c1c10b082003208041c0321104031240b5501000f081d800c0c0210041021507900420240c030340c1e0916031b011030f910a0311543c1008103200b0410003081c4062505416010404031082c108666850880183c094a4550389003a000700000942c000109900c2036561a449410034449031076040050420b14a6900c2a0f12414400d0301d4420600104611a01c030341d07016aa5084041c454a292807448000910a408580400007010050090380d81448030081500c5800204005213401000c0301190070004d00f00c5000000452401e03103681016040200c9a0100c002c0c94840344a081030fa090103061209240901e6a822000e400e1212590598001c10803070300d1901019109040d9407840060b507900d41001c0c000c4598040c001c280c01c58201c045064034854080b650f2110140d46465083c01080d80c0042c0004401b0300a4666030011034504100400090008409501e00740c050803030000c021443c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770988309 1250 770987059 770987159
    0x307020f06040e0f0c04081209091f140303090a030b06032a041d100c090b0f0f090112050c03040314030906042411030103020102150c04060c0309 64
    0x5101c14800303c00c0415a05502280242c80300340c0720f4a6242e0000458019980f05290034407800b404220900e650b10068542c00d0410707101403100351a030800810800308880c25040402e42032640400440113040d5040b00746c98405000d9078600301c61000805c4110f9041e800030364103160380c04c3c01d12001f41410080341418035611046065464001c0c02180c940305d042c41050745c032450302d40950070b614508240046680452110031942c0d00014007440340042c0504000c1c4001007101450000b8210842c3c00c00c03200003b541c031041c2803810488810340c80050304000d09843c1009030182c1003a01c66040d81c030440d401044015403003501c0e86482c0c0307401084440c0740c080c94460340d5410f0080c8903403944005400341c0c101c2d610100400b83c007060f424403070f101c28016000035010142004100c000c40443e14006505980c000e034280d030f040c80381c4103440c044020700a40711854114010402004154131070314114203010301c240790248045640b1944041072103244110305c01a01d8114a2200b524001c82c1c046900c1e0007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770989559 1250 770988309 770988319
    0x705010f0c03050a12140105010206060d02033304030302041412340303080f130b0c0304030309141605120d080408070507150e03010513081c0507020307020f 69
    0x21601900c0108001c010101c000c05000010483c545a1809801004c0340b2000308081044500305880b5854010702c020311030280540548800b207101800c000c0e21992600340c0160040071580c0d040340c1c000c25280780038920095a41c001c50b420301d4074107002001881c0258042e640141e201c900742020440042c10004083e40b00e5080016051b54140c404603254406400070703203402c000c440c441c06100c007841d01c070000c0c141c2c1c0d45010b40d0004802c041e0440074940c080c59003891503400c02d81e2240f00c0d8485515005401811825081d800900c00e2507440004541c03142c483d1401007060a4039580f012032440149042c4002500103000920f0022949034550b4014142120125403c0030410101a112905070114008100600380002c0910441d02c040755608d50b1b2200c00c9030540c0341e4820030303681c18280807039072500011035907146000c0e2441e0501969000c2c0100c40b20955100078156038a900740e5001c5110b000709000d21440c540741c00c508510410744102c065402550342c50410344100094100e075100782e94420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770990809 1250 770989559 770989577
    0x9060806040c0e09160f031707050a120c0203190b0f01140d05010e030408062e050103051801150f0e090c010e030a0c14040c020c090703022101090e070501 68
    0x401c0e9400e40d504103e0710a0340911240313880c1d1440c00350416803194400010220101030006c5e81040c0b00750310504590041c18062070004507400c048505202d01100039100354040c03150100880c5404581003001071450400f641400d413903502181c140b81d044019446034500040c84102440b011150459004468240304c95440d03050049100701e070810100b0040c090980c0c40288401c00609505c81e008142e900c4048030b0b1666130b05c04c8030603900c242c111621090000100c1207542d03488c2d802c1c440c00f000304403070041602c04281881c0044008000052102c206001240c14032900c203042881405118070304900d00291007801c0006100e1850210740c01981c243c0032600410413042d001084c501002d85092034559201340b181c80c00030785400b904000207000c4000c18100040c0300703201500044011241034400780f001140406059803a803044400030707904503101c900081c1084c0d100b94000d00c50003000c411803503481030040c01c40807000e100c240c00a4185941e030f0001c8400b522070820100f401480e0074a0407002c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770992059 1250 770990809 770990813
    0x4020906010206070c030e0d080c0c0312070308070305060103060905040b010e090c010c1101090308030109021e030112111f0e0901090501050109151707050703180f030b0a091a010906080604 83
    0x803000300701001501f0000d02d40c103004030580d0f8201040d01066046030790243c84208000d00d082e166056092018828844c00310342004180e290402d0350086034054881c07020566a51300c0a07000f0301001031010341095070300c0c400840c8540301441040c0c06a4002e49c0404003d42c182860050101c001500c12416503000c14034080003a0703806100b0228266101c1d090400c0480d058005a95080181d000240a104040008a0407001640c05043ca84001c02c13006142554035460b00300c1c5d184028010701000c29030501d00c08003c5580c2540c00c1d0030f0400050211a101102810f45c10a254001445100001c0c0c0c0c00c542c2c0c2045203001420b03103025281d4200c00f00415407500002804021403881440c007550b055481c3d454000707011740d0003415042125401000d161030511002841a44154411004250401c800c210480d6004540005842d907114401203030703d0641e201c1c400e1094000300b002600e80d4451a07041c1c00605d00c0c065503000300b414100c008890354108460807054459a402c180110341c041010880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770993309 1250 770992059 770992067
    0x40503030711030109020628050a0905041d0709090c0e150d05163209061302070204021b0609120a050306031908341217010902030402090601020607 65
    0x14442c1d84140308608074011440442d0250240010180d80040045092030840c0d60000074041c1e200700c440c412031085014a101507440780103462030540000e030301c000705000c5810316a000189041d81021400840882408442d01e010709036044103000c15141c680c0681080402800c50010b0006e06c03500603018501488031502d038010314902544914010300c5043c0c02d0150a202d14401c0302d90344001c1140361910751000c24602e00106414090502440014020ba40b81424105440e924014038240503070700c400c010004a150752444800d00d80d6030800101c001030b0756510041c40544a40420b4103003941c00e8003105420520006c00001494002c0f01443e4125000381d8101c4a01c40200e0500e03d0301c0351a8240070901d00002500003002c40001c80c2d0512003401040c034040c18521192042002c0c0400942e441c2846100190680d00c42c4907a4000400002035a000c400c0400150240b0307040c0301f000385080c131104c4081803c1e4401c14401d6400002d00040d82401090154811800c1c00206030034189590020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770994559 1250 770993309 770993317
    0x5090612061503010902580e070609080a030c02150c0613020907030b0607021e0319050c04110313050c131b080f010315060f08030a08060604050303 65
    0x10000e4620001400d540e8501c82c036920101140c0c820706407650385880000000f5440f5280311602044c40112a803140d0300d5240c1761400d038002d8180a04041200c01840c00203001841d00400c03198074005a507540360302c01030b21031309000c10448030044c00054a0100301030711001c0142c2100546400080c0d8540202c0e41200c1c000740040e6042d14060406004a40030410758000c6031107000342130141c5c4040c4400c4100c0398109507016070081b2040a41c40d110b40ea001e03011100c1314041c036a0800014400c404c09441c5c440061b08641c018030749503079012140400064100346030503042c43c1d0485c1c1221a03003400e104042100c0c20700844140c80c00c0184400f85444070120f40030050102c0300e024115150442001814040e51f04401d0380903001d11124a029010807000d0401c1400258050805400145019110f00c821500804040908a5590f42113803a0042040c40c0c04501c02d0300c20380c59003000202c418050648100900784203020b15145c03801104020517088001d02181d1044205201c00d12003660040111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770995809 1250 770994559 770994577
    0x101103040b0f071e20130509010f1b030c0f1e030608240f04230a0506012d060e0d030c06020c16090203070207060f170a0b010f050906 59
    0x110b5200c10128411641c68425410010842d80110582ca2044120045950328880c40390200c44140d02c28000c081001025490f100b940c0001e00c03481c048409181944415003100241002040688107842d000054640902c0c0c41c0c0000420340c44285981d0b68588a001d105500f0740c60002c0c11000342200040201e406a03d0740b00201511648a800a0707019900910050200a0070783e010100900c0c080381242e05000c0d010b001c444419000100e40849100519104560110344420140100314104240c1413a61500b640144102160200424000c000d10380c001d16a40281c608905100d00080100200204006952000c213040500c0140e41002d03002a20200950705101c00e00d80500302110030710349508028040510001d040b0211400100b034203c540c0c0038070111109003070b940b90980000ca1000303c44046c0141c101c85c0c42405190704c24140f9000c161070303620f00076070104580c01c100d5100c818140c5440340216514514100c255170400b5a82c80303418540e050460a003600b90000c6503c6101d44000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770997059 1250 770995809 770995829
    0x90e0901060312120f0f06051e0303040b030417120a1815050901021c02070c081f020d23090d0203070b01031106070c03080c070506161103030f130510110304 69
    0x1d1346407005101d80c002c11941865000611031071070820750315130060155000f1076004180381400d40c040d840710b440104070320940107001580751602e407400c0c2c01404e41014104441c014102c880c0c04001c025840e0180a03513280c0a0f01d42c00c1c0c80c3c10008a168200c400100541c010078460390040000300d062007030350782d4042007002d501040e0303540c880c07a8607402446620300c403151040c4504134003401d4589170303805020703654440c1d058205056200c40e482a60340700da80003144001070006842007510700300c0740c01402c4000e43e200404207503a41401e50004241c42007050680b040d00c00c0c44108450381d942044007001d440a00d0018519046013900c90360a50b040502000d412030598151441e80c50300c803036084650711390f085002c04003016100d103400c0107140d012411035811032155010101c1e19280c64011901c002c61031008082d841100b030340e50482010109050590301d80001c0c88000c08440303001c00181500390811407145040b0b82404200486401010000e400300090404119176141e4000103c4082e6032400c15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770998309 1250 770997059 770997077
    0x30f010905060607121e080402120613060c0c02040c0804050d090b090405090a021807020f0c011d010207050a0b07021302070803060d0f060f0204060e01020d0e0409080f0703090e0901060312 83
    0x802ea918014540c40110b0180b40322480c500415840030045005034030031a0341703080c5c0ad4140c204003565030000751a00348184071200b100314000381803036008000704400d50038a1072520206400160451300c18a40c5d81001c140b042040108006042c84024039901c01c03400c0c00401181800e0428050f40248801107004030b95a00c00301e280b801f020842600e420768001c0081c4a1060350100d10561604242c03080d0002d8030a40b2400c2c3c500480c00304800003030038410303550201c221031642c041807031030b0221032105410340c003c9910100303098030755620401c00f07014401ca640d5900c410b503105001a0a05e00f02141110500c144445400502141c041703e4010f04d0450351502088903500300070074680703810a8010003840c41c00300c010032040d4040c1c01030000c0703400b240c8580425501c070300300590700c0382080e00204000401403180d0380340d9460180e000340c159500400d421401d290100c0ba8510081c1e12a59007903000c19510003082041d091804039881d40b1110300c4000b4005140341d80d6410030342914440c80780c0103000200d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770999559 1250 770998309 770998343
    0xa0308130606120809120f0c011d030d09080d0302070c050f1305190b1915030216060b0901060c0507060804060b18010e060a06091502030c0f03030f010905060607 71
    0x14001d80054881c02941100c201c10925084d40f20760701c80031000d406003896880305d120380071002c1140c05a200101d0090308450800000441e610282140b4041420200d0000c038819910200100c900041141c0c440d0107045003000a0140703404070280303044081500400c03642c030001c1d65008490f012071b8401e941100444103c1d030700144d60110800e00d505005486c100402c40258540b091029000040c1c0c2001c010f2540c2c2141404003910100c2c1c81e03840f20300030241c0c04004074290340c41a0452900c070b9141c018280410315150030102004034800303075030054861090b890b0703d16081340700c079005114608021121418a03603445407258114420070040c40004400201030020340d4002e0b0400f83c0000b4075880c4544607041d092810030341d080c0100c0c03904c0301081340082c0c100d050460301e000644903540ca4440c030303480c64046030b040b81140300b403501c0045000510900c1102c840420940c186031410304040c5869107869480b80c0754a0005034041c6107494102418045140c96403070440700309541040851000651135 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771000809 1250 770999559 770999561
    0xd3f0c060e0102190305060a09090803040312110c0102040905010e01080d1101230901060806101703040e0c1b070501050f091f0c030e0a030507271415030a03081306 72
    0x16071a01c0f01d00080350007400c813540c16804a4815242158000c4816403286d401004980130b028008003425410008100424010303101901c41000c4e03d00c0204240324010580718032504010b014a0941c2c3d00441c0c00e007e014058001c1901420185000010540c074000360303136a5071584204c80c4010701620049000c014002900141900b601192010307035000c00001d6001c60b401030850b9094015403801002061504020800b2400741204061301007180f8100b402400003030034003200f00c500078030040000168607140c100d84d9034412404840c0054603548409415a080500b403200740d40c40703401181c01400700b40c1e08801540c0c51481440740154542e114500800c800c05010038060b0710304001300784190710325640007980180f00c0c1c0c0f00340d1b10000011201c0082c441020707840e003c000d1081d001248244100d00c40c0386407000d1403030304000b54a034600d2030100c511070480720340f41074002148603424108000c0c20190445841d00000503030003002d940e5280d80740108050405001c1044c0d203a02c1205810901c01c0b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771002059 1250 771000809 771000817
    0x441305030304030815060a0e0414040201091403010b120c030706050a051206270709090501050a0b0307170708220b0c031e0a020a0905060301120609020d3f0c060e0102 73
    0x10300f0311b0759035400c01c80300609000e40c22500588283e05140c0c0141c07d50011030700150285906841c0d5419042c10240e8030141c840354501d105426643c1c036001044155a02070784d51824583c0b440290201030340c40d10a0505205050f0000c005103e810031050402a61142c121400704e10480020484c0b501d0b05030008454001060717207241c13003d030b02070130303101d90b481c10071942501894103625901c2d0f443c0d903900c206100f40d4030248a4658407251000d01000201c00407401140d0221080c5081c000e140660000707095905402e480300c60006090600b0000c084804014003005440c109084400d04521941c5e04099440001c0c1703080507040c4088003242031070107200440d1504a0700198035499a20340301c02d241000390424009000091401103000441e400c0040850b0b05071041c00c840b85610801c0c2e5110880a031080510807a0082424544500854082110010000700c50f040d404195001407418154a455401c1c1c00c0d00c88900a0070010f000c0c7e078101102285555000764085420340340055440c3c02401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771003309 1250 771002059 771002101
    0x140d14060a06230a0909080f04030f020102010c0516060e190302010b090a0b1309020d0c14010f020102090d030e0a0906080f070f060504064413050303040308 69
    0x81400c00340114025a50842819603908440c038032446001c042c07025401d107840c1040b0f40e4200320084014413400140e50072503c0c40303901881800740740c032904540302507030f60b441580107440d02c907042c00c480021981d080c011290209641e241c03081c00d05400d0200e454a600244100810a999602910442c040cbc07d200d10800b107801c800d103403044041103050180c042c00000100c2c0d13206d101c03114009001c4803007600c2100e46c0100007500d6084240b0394080780b80d0040109483c2a41c1c0031043e0b10070840003804800110340a050300d90035041c2c0780c0300a5030014140710766502001e003d59006002007511303902e5446020021030b8147c40c0c00c3d1b200303210003000705454040b00e40005400c0c50031301030041002a000a54451040c9a140860304401e64407036102898144600520001420070032080010900c9103d000d000d030340c2100324800100c46604180d003054407440a0743c151202401d5405032207059800c01c5550700c10860342e04240c071104a07035900c43c0ca0380b1000340000d0511442002003803441041d00c0170070503681 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771004559 1250 771003309 771003313
    0x1b150610030b03011b030b0d0503190210020d020a26070e0d02100c020316180c0201182d0215031801050f1803091e060c100204050f010504140d14 64
    0x5c151400c0001c0006480344a10100f420320038010042d0400d11040f03503a06400c072010398101fa03010045502c003c00d08031206011482000401e0000080510003090011080d44005a450301c1000001c0c0020001d242410080c405280b801c002e0140300a0742154030500ca480e00c054044403100000703003659032050004e90405001c40c0c1e039511035900701a5014141e40200d04880d11040c007652006040b42441c060381080000c201000300d80101c00f0707040503041c044540000701c0c0603d4402416030340100200c1d01994801c10803802c6a80040c0d60a03518013074840040c1c0032801c4c034203041e000300741c01c003c0c04264021216400000501c805c418801c05401c0345111800900490402c440780e03130905c01081e200c8120314040980303452600c41d800002ca861100c8050800780708010412810350710b80e160141d29a810080400c051121403c040c003001c044e071480d0b0740005031660700300f0080c00b040e001205445414004200401d11207080c0c00003141e803001c50100e82001d00c9078003502c2c2894051005010500c814 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771005809 1250 771004559 771004571
    0x3030e1014010807051504120212060f0a0c18120f02120c01120e0c0d06020c030d0905010f0509031b01020f07150b01080114190512031b150610030b0301 67
    0x1001d8014025040303e01c103508550f6003a40724020090074904583c1c03130800c0c000082104100c55101e4a69201500d030008081d131154070441901681001000c0b90704d01e0411034038104201848480d842920315401951a181558003400b0155140c880d8050088844200388010030b003080140d00700315219600d83c05009455150000c1e5000e6a035178820011043c00f048080401d081001d0051007500400f001040042c803014000c8003e01504aa501d001030300c0d159000c00c00344501040400c01004c41e10f00e072a2000640c22440d06103d401c64081080030901d603800c14090121501000094510f00010410b0711001044800140c50091160b801010290000410307040c060115588071010070425003c420312228080c034004407140d01c424007401e060025014821221800c0c10450f00c3c1400490803c03400d1640d841381c000903814000c01c0007041c495440060081b111310b0350480000326024044005041c1c5088811200d20340101c01002c075406801125084000f252183d003050200f140f002d0001c0007030f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771007059 1250 771005809 771005831
    0x901020a17041d013f050c030106060207060e030102030f06010f03020717070213060b03070f09030f0b06030f01050106050304150f051f1d0f0622090b070c0c0303030e10 74
    0x8003210034401c862600300707001c0b1070500c030000d1060a20748000f05c04180f5107002c0d01c0120903d40034152800300341c4151113041c0c19140b00d074a092041c0c5020304000d400800000c0d00e440b0004001c08141c02d0f0b079900176401070050001034010b03503645641110090820341e1030003513880c004400074000c140c0040c20003510606613810705910034004101c0c0500a0718256401d600d4880c1c024190ba280c4d1150b50b802900401c0001c04842c0b084000c07812440035450310150b003507500d48940da07203c507038064195600790000080c0710480c50300f00580c6500c00002e6009020f150300d002e82c09046800024030107442600d4030080c52010008560184441b880480010849030504990b002540d0032140c520040000e00500040303801481c401000184501074107066415a4403c41004d030310f5180540309540208101c40e415182c0520554800b02c46420048005260411401c00c141007c8020303205105101d400400301001c07402d540406029250076080220340321203100e0885240480381400c200032549002e40702c0c030b5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771008309 1250 771007059 771007109
    0x105160c090c0c050a12120608030c0d08010807210b130203011109060409021b0a080c07060906050d050408040807090902040e0c0105040e041106070308100b0901020a1704 75
    0x2007681e60028003000050b802042c2582c0c032a40c2c180002e0001e5010140500002e20301961a220000c2c0910f090100510205200703419207205401c60701058001003000824610304000d810720f00210f03440c2202055140c18282516800c460040703014107103a010b650388010788485104824141d02a0351801c1914107807004103112508018100d10075402c0a850301040c445407400e54425601c0200241d24151419090b02d000394003108410741c20040487d00c03c41e0700c2400f07100c0100307031600602845540c0d001c1003a10a060900c16003000080c001d44240034051554400700f40d40d5103201680f80012a6105da00f002030301806617038010801480340502c082401030303079500b0410000d4401e840a014110074403140a444900314001c450024006010400c0b072402c1039040d031900070b402141c12481e2641143d004c1942c59101c41001d0700071580d000305015083c90341128000042c5401c1104074144003403000000d44644481c503000e402d01c01002080034440c9140b02c215401403942c0340610044150948040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771009559 1250 771008309 771008333
    0x6041b1115090a03120519050a0603022d10080a05040c0302040509150a06052d09070c020906100519090f06020106060f0e0f06030a0b152520010516 65
    0x100080d05e14500301c080380380c481c02403c2c0103c4000c80413034a14030b03070083e8107401444010802d210b03080d00c40302d000000d600c40319030043d694542c4c6c0540d0f402056120403c214045801d0f0354084c010b900b01c40446050a501c0440d803a000310a00300085203a0312181030007104006180c001a6000d8600401c1c007100b050006100102401c65602c000300c542d95601072002141d0184c40384640211103000c007203c0d191040c0b1003000705030300d0905811403141e0b0303c030001ca2540c1d542181c1c1140803503480d05180b019864000d1142c0d1f8882804c58072104201080c11009107030f4003840030a0f48035800c819081c2075550f0300854145000d803440901e501c3c07810382e031044024042c0400303115000100c0d10041412800307611884001a00740409410344421aa1810034040554801000c40ca03d050369541410b666070344180e8031880c00742041d000700d46c40780130220b400740b2250380881000030030089890b619030000d0f5800f100d5009030744c80907282003540c01024006a44600c0b0b5600c416400b885e00103200010043c0e07001c018 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771010809 1250 771009559 771009563
    0x1e050a0c0809070611030d050a09020406080604020328140d0314070804030c232112162102040602011503020105070605060303040906090b0906041b1115090a 69
    0x14805908040d405648512058581d0707440783e00801001e1100f140240c01e2500601e50000849103032802d0000303100c0c00c40703d0549444c001103460314180025403030207000e40c102070000d12003d042241000d9000aa50728400c0003440c11600413144803990199011401e203010303582001d05881010b15510382c150b26540b042900c1e50121380340c40a41c801210030442c0c02407040c24552659200c50b1a1520240d500700e0904000300c4180740301945d510b4070343d10042d80d81110001048014120088080c0c581c031142c04500d422484464001c0c0a006910f401171a00d03650030008801c40da840540d4002d00444607074280e070b8580010428030703901c1e95820650950040080703800590003040030245104a407400803c0501c0080e000542c01e11a000c0400c855502a9800c1040141141e01c1d259540180c40700740c42050f80308840c010381d64101440141840306079954003500032102000b01c2c4c15801041d18081c04041d0400302008080900322915280800c1a0080294000142440e9117099801b0981d10181c0003c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771012059 1250 771010809 771010811
    0x1020c030d051012080c07120f0605070201050702070b0c030408010c050301080f0d0e041d10020c01110405030703030513031707030f0311030a0c05071415090c0607060b041e050a 78
    0xd43d401003820382c00400d42e10880320282880720307143c88100e210f0300040100442c50140380d00003e0030301c400c1c0c040090358500c80c0c0d0019000034810305060080341c038000c0c840c030306590400c401c1011081d40450f0f90030944c1c0080c80580e442c1c0c0300041c0b19074036502030b580006046629080c000d41e01250040042d40c103c880c8801210780c1001605812500c03020416101400b280c5030790100215460701d600460221403110f885403c00c4041c01800502c0d081401d1907000600f44c1c002107800301070500b0300400131580c0c807000d002403400e4900004070380da500382823001030204040461f0050084484820282c011908408006002c1294100020080e071006004401280d00c118098500c14041e00072100f03d100f003080c49074150354408003814080c0821044020811404015400c000b8010302003801e440f4402000070000b0130342c010181e582075100600f00c0f0303810341d202c04140c1500f80d0341d0300100e0b502c1d164400c60210340096200041805028401220043e000340c1c90440d041845503a80a20301c41e00450348 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771013309 1250 771012059 771012061
    0x20301060e1302090102070303050313060f02130e1006031e020309071d1005060c120d02030702061003080324030f01150603090503090d021c140c0604060f080a020c01020c030d05 78
    0x21442d402c80c800d4584890150304400c8040001c01c0c000c03400345601540e0729440111107001b540d02c0390225451300340b000c2030407030340400c1c42111011000b031460b01410012404c1d003850300f01f203840050100f59038030852040589915850084402e9010f10b2204030ba0130207000d42d240d080c6115035075114001da00824120010030690340310103140c4113503458012081d160f440341940c3c0c108000d0045079440420b03802c2444c030900709a181046101e01c02400315a0020800603101c0c10b0a1030001d06088010381008141040454140f02181c071580840b600300511981e49544010341221b40e01a052502c0002580350042c5051000070401c10742024606075202d0304094241030300d848041d41141d14003d80640315501c14800c420181c184902a9100309000034249202c1c1328a03090f4000310f00040c1041100c510088268640300080304014031110040d08841c170383d040c641080c0e00280301000d4845c401e020401200003003440070119504894a880c03514001355a00c8880004081c2d60754030000d03103520118a414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771014559 1250 771013309 771013339
    0x190203010c142d040902031017031c1d01050a06060513060302030c0d1b110114040209060f1306060e0d03050a14090406030b0402040b0a0e2206020301060e 68
    0x20b07403100042000c0c160464200400904000400480c01c0c1d154408000d182e00b0090b86220311034060700044c1000000580d80b844c040044200d4036145032300a03c0c9018110004054140020003550f4104e20300f0a051080e150250315810f01514a015a04074850014180583d4004040d000140b0481c47e01d941400302a0b034a40f4101d840341315107000d417001041811000c0c80380034480e400075030b003041904103a0342c20b0078000d0030038004403441d01c0c8041215a5220113818081380d002240100604013a50003081484800b8164880d0601e00510007441021903030b000032000d940b00112030820010141400c1c0300324200a031403100030540340c05444082400d4421504051030031140804031940e055494600b003001c0303072200740d48420280f120b42e21440d20074030801c105501c0303e118010045000b114440c045060900501c0101e0306c400fa40340b805610b0004050021070030142c00f20350400800400e40e03d48250012582e000440042c600501b843c2c0004000180300d98008084030140f00102c500702d001d00080c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771015809 1250 771014559 771014567
    0x902041503020906040c1106130b01060c0f020f010c050f0c011106101e09110a120b0915010210090b15012c060705011e060f050109090902040e190203010c 68
    0x61100941c0f0a020800041490070310340c0014125012070300b04007146a4a000c045403e01030119403190304885110824802c0c00b1100c00d009005080340e04042c080b40249880320490344d0245a000780c05001007200d54007071039115601002d0b05582060642c0c2000b810318619503100d24402a800340040d00c02940c1d03c0c0e039080041019406a00b100d51028409840d11501d0051010949844d003d1020140b00000d00d00c20b1034003541e0b03800038811242555a295041019003480900420000400c3c82d00a421308551200501160410072681c1c0741507140040341c0040303242c010383c03001c02240c031402c01025804101500c0b40e002e015121103501501e0300c158010045400e043d20002c0f80d044a040b04a03d02d50788600131440728568007016060510344091921031602759841888072180080100700340c201038a03180c0c0700b581c01400601e803440f21414a4000003e00090301c42c05500e01140e030362001e0b2400c40d981e0340d00c035070100c08040d4184c4000030380031042204601101071080c2d020f5424100d000b0b021500c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771017059 1250 771015809 771015851
    0x4060e0d0b1504050937120503010612020426011d16080a0b07030b03030415020606030d031e050a060e0c0a120606090b220b0d0f05010302010c0213020f0409090204 72
    0x13011411501d1481e07a46d02c4580c00d031240d216070100f5140010f50040114450018982e42440c075900c6230782da25403400f60f00410140c4101070780d0300103507c1448180301a001c0f01402c000c07014104011019008d1303444405600601500250b0f4100e50b281c10071007050400046140c0e41582c08240704100c1082d51003818588910041000600e042172110002c3c1d601c500a0344501540030015040728242602c42c0300010b80c4541e0100d0fa00c0140c0d202404000d043d1a042100701650b20103480d051049601d81002c0380960448000c41c80c240d1604c9400182d044941c5901900050610280741011420000c8c1d400040e54010701c104400111029092403071030045000d20000c54100ea5201c20f605480c2013180980c0d500841510700c0c03a00103000c0c0302003581d603012940102a0440c0207020380e940f004400207008a9035001004c0c0c0704242030800410140c0e80007080c00c824650182c40121144101d1140580203120300d07401da558001010030045111071059002c400d18501c00c1da01000040c10900f22604d0600c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771018309 1250 771017059 771017083
    0xa26280c080d05030115090e0a06230102060a0b060705161509030206040509072705030d170a090203030c070306020304020f1c120507051e0d1404060e0d0b15040509 72
    0x24040004002d81c205206c403401c4041c0c01071401404880d200c3e90b1403410759000344c0d001c1e44503580b58441408000d61100000300d001403118400035401c220700d00040d49419000388415207290303880c1c0c7c071180d0355214802292401c1d5400415215826900301e80c0f8400c1014a004000d811520040c00c18800c1d4040c01609040d6900201002e08003403604e030800149002c0207000c0c00420450b100d004214140c0b8941003103a1054018440a8080c1440103141c6070003c0119090f0400129809400180301159041904403500c5200440c2e010300900100346540300752803201900348180c071400420f002187e40514001c500c02c03540c40d0070041c482010404c4000708140704ea8000b0030740c0500100095500d941c100b00c1c501d541d0410350705060103500d0300d0f8240758041c003240312001410724412a001c80280300128482c4030900b13103186601403007000b1440038082c1d4001c0c0402c0c80061071074181c4940c1e681d6040c0c07981c40e6000d03020035102d180143d0085150441145031602803400c5c100419000d500120724550012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771019559 1250 771018309 771018317
    0xc060c1809090a1103030703020a1b0e15040b0612060d0c0509040503030114101b034b021b0a0324140610211b0207050a26280c080d 58
    0x821a503c650b5610034041700340e0bc1c25072045d440700207010031040491030300c1900c1c0480d00511004101d81840207603046c1210b0b00744299810000d2044047c0440c14464004405a44c030040300c0e00c09240500c254102600072650002d03d803c00c006c1080400401135050f60b0741040c603005502110410b0244c1c1e00207011070340001c15203001e00110086061800c0d0602d00380289008403100c50002005005080107070341c40c619031107868151030004000510003109901c1140719120401941440c000c2d10b0355a04800c2120350405a000844143d40b050000c0000d1901f05040028100d000c083d8049651541180310041c142130400045612212140151140c3c1c40030b4080d01035100e60400445005400e9841007120310100119140c0b160050301c1800e1601c0c4003520b0020303105071170810180c5003003030039800640314030b641c20411300c44401c07040c1034043c040449014201010030032005043c02c2001803013001c1c070b80704541090041110360100081150380d0084041114494403521255114240300f10040041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771020809 1250 771019559 771019573
    0x314040804090c020c10020a0303150f032612010509070c12110703060f0c1206030305070201080402010c051b2d010e030f010614040e030c060c1809090a110303070302 73
    0x1880c9181c00c101d40e07560040c0305684a03943c08000013140c2c0303e83e4694000c0140d121201950070150180315000078603055032050008a433401c8281c40340c005450100625241141000000070a40b510f0281c0083e641414119201c19521710030382d410840034440e0f90f101c1c08038480805c035058092244402d200d50412001c2c180e075034142384c09076845900c82c400d42100d803140d0040040451502e105122a40600040120307400041a00040c00c00e1b04010015400b6450040100700280d0010201c590482d030a092401807075865000688107406003e0020781240640540b4600f4121203801501810301c0803900c20f0402107a0b0001c00740310780030042105c2858840d0210070120b641c080d0200d2556160f000301100c940e4910b90039079a0039240c0c142d01400d0910240c1c2d0b0600d2540c6040e0140c80c5c40021030310000c60409074882c08841da1864040c020040408000409860900301c14031004002c80340078040540c0c82c24095009655038800100585141d2126800000c0b2440d000c411144e09a401d030b4010a66 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771022059 1250 771020809 771020819
    0xe0c0d05060d02032805010603150c02120a080703020714070e0c0c0601050909071809030f080610110304091a03070f080703061109100f030506030c1c020f031c0314040804 75
    0x2200b80c01c0704110f01d105820341784c0000080090080c2c1c8095071084900d108004c62421400c800d44408080303900540d0410019103016081a4050301ca901050341303000d100382d444080059000384241e60000c2c000500c482e40b0302101c1c0c44005245012220621b11825072079540624407401c90042c0910b0440319000703880104244d207481801240c00204e12802d4440c61940e0701400d01d0415031080d0303595002c6440d040e617103040c9034002c2c906080e801c0150900444500e042000180019440e0b1031180503c800000c401400c0070701041610040c100c0c41e030382001500511240d140b220b40361103802a219104800d00412007607940304050741240c501c1c0c002400c81508541c0c0310b801030465203420050050702030114084945d40c00003210f000d9581c54417807000c3d0ba2104c20004080c0c0c2c4004200d28066403054202000c13607215038080c0281030040900803110151144005018001c07526089981031207652401e55140c2e401410482c0c42014030f803401c000c14008030a41d403107600401c40300600085018082000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771023309 1250 771022059 771022093
    0x30b180105221d0d0807050a050d02031807080307140706090e15100906030c211104330206070f050a0224070e0904020a0306150e0c0d05060d0203 64
    0x70010034000114000040003c10b51400041e0400d0381e4860344420b2421460726003051190b40c101d405850168a013800c6490050290311030b050110305460760003c0010898080400005e19020b201c03030035507101607542d40750741c0d5807900400e0080d00d1000d200301c5000b101c000d0004e51803040b20a16214606c1e11440d0003c041c0120100034240d8241c001000e0401c8803680e54104914001d2034244c50303002e483c81c100500181200e03c0305d8910018403843c1042c1d001488180071450206002000c00403441044480740000a030140e43d00001101503440b403540546c1038032052600c20039940508030400c600002404a03510101a1090004079014801c940300b00352040340289203100780e500444902003036072140c008000180340760030100c0140c1c40c02800b01c202e5100d200018030440490710304026040c1500010a00c007454440101480c1d5100078401f0816000c200d084000d00356840b214502d450103040c50321075507000440060380340c2c3c0350000150275480c14084c410001900640103140012840c01204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771024559 1250 771023309 771023359
    0x7021003091407090f0f09051b19080d0320090f0a0b030414100c0e060c011512050c0a0621020d090501060306050f06031209010e10030b180105 63
    0x144031908001540b002100c0e00300000001040610301c0007440182c5212820b080701c0c0b08160310f12500b400c3c0014900852400100402a9045001109482d0300b005000402c0c0c0c003202d014058021003001e60005c1d9512010561107602510760300c080c842003460310000394002602c040703d46451501401682807074100311000784034650014200d2040141c8807142130030f081c0c20031030342201d0400b65a00c094001650a012154410301c072030f401031180890700303036018020700525426180a8100841c1401100c2000d4216021200440242c002c41c2d41d100c01800034101c0380780c0419142c0b4800c8891400c414204481c190084404030b0703640343c00050082403400e01ca00342186820042c03980901801d800b00c01c0390700c141018240310301c00005031203140d03182c03c105440008046490844481e01080311940f07010034034100c029449605036130784541100050f10007815501540d5002214512981640c98050344064140c4800300c50f00354a4200d0a69012480741c800d01034190030001d040c400030104507240d4209 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771025809 1250 771024559 771024563
    0x5030705190905120c12030903030d02070804092307080f070c060b0616020a0e090307080c01060b07151d19021c05070303080106020309100807020a1709040b060702100309 75
    0x4400b0703880c2d407800010301c1d40900d00e215080940119407800100e182480300c0c5e64081e0441d8002e9030400312400002601d9014840d80e04446980018105c810090b40c4002c0701c016040c40700e010049040201e1035020300c00c1c2d80b09406600101624081061640208403042c46101b81000074010341e0303504181160f94100141c1c080356107940710210302e10a5503400015240071180c5030100000d28115004001d9500d074a0b038001250440100c00348880c4040100c00c07109078070f4224188907601c0003d0ba00d40c1c1d00501081d4031584482101151180400070030b40c0b1029040d40103200c0501c401035504050060400c804004d04140764026402c1e0801c9130701d913040510340f550004012130040b00000341010b038031100c1c03060100e8081d048400c0074010180c00038106809460144019810440b01501003040e00d2002c0e0200d01c10700c160070340060219403007040314030210b40c1d12a11030400881d0901c40d0344480d0300448045846941492640c06160600700e0585001c3c913001429042d42d40807540042c1c005104a00003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771027059 1250 771025809 771025817
    0x8160e01031202030d1d0706080112082226061e101e0f06050f1e07050f0601030c05030a03053411010905041404061d0f07080601060503070519 63
    0x40301107081800c0c4148180741c03901814464000010701d42050400c140703500000c0c10301200c6c100502c080c1d0040120700001d66440400103540758411143d0f1500740041c1ca04208dc1d0080050780440d503412980d150408107009090351000e6040d00c010f101382c80e10812150300420310820052004c082c4140c03c403080c0c20012155214041c2a21070141c000e0f6403c032010b4020741555032540030844d100040344107000030300d20b501e005400c2c00030351690401d01c2d125148000e07004101c81c0403d2801c00015504603440503a1020441d040c0703003101d04a0b81d4486100b440f099601c020f000c000090706050101315903064580c9965900d1504d401c981202121400c0c1c03e84112003a29444410811400c400404e1030303c042c090345c244039001e0000c20006140c60500e82045000e903060110b00c6404c81411200303150460f0703012030049481081088903000c03c100344004106a486090320300c408030341d004920801580e039100705442250380c0721203090f1070512054401c0d00000e2020444003040d0b2200080f2190304100d9450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771028309 1250 771027059 771027067
    0x50a031b0815060d0608060f090105010e010605131203030e0105010806070f18120b220c14040f05011733090304090f061e08030d0902150d02030108160e0103120203 72
    0x840341041720401c0c2c00882503a440041403200e0700700b14007003407035029031131100a004941c10850f030b0390202e030010702c0380b001171080110384800718180b11030044000d0403c2442c2110a5055410002c003d01074a0390025080d52030440040781c10000131507041d00c1a405d81d100c0d110240100c2e90300300c40c6500001052070041c040c6c0d07540440c400d88821b44820015009030241d003010b0800480c0711381a151280b5408204003401840c090008280302403100c00c48003004c8000007040014030216014040106a54045070700d02400400c009141c0d01c40d2902d010716840407110254600032074503d0120501c440070342141200707041440016210091141c0c41003140302502e00b0070b59641044402d40318044003000e107445d26040c06100c603030003070140e0a0843d032620b02c030140c6403440d201c07a4036128895454002110b0b5250f640b1030080d521803260100003003050f030388003030703910052003a484009400a0040320050b02030b16842c10721120140b3343c4141a60100700a1846a902e1507407200d419282e51664401913000c244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771029559 1250 771028309 771028327
    0x170c031b030a080f04020d0b04050c0d060213050a030209060405100b0705011406060909010e090109020a030606210c0b07060902091006020f0f070b070204020910050a031b081506 78
    0x110494030821401402542c07200014035010304998401803100c9151800101044051b903075000f11450500c1d0000c54610301c81c1c4a50074900e0810250746c103074a402084542d1070070100603035540108018943c0c40f0781d910302c0d41d031600100100b1142911010b51b00500303145c0403960a24280e40426080701c0399018000001e03544541c03e14264002183c195880e9555260a44000b18401c1c0400e5001300121869498108101c001400100060244007402020f0302e00040d4112801d601a08070950020f1041d0465643c2e0319000014101038010010001c090f25107248044102c00074400b4138513030043c0030f46152420203a0284640e000304034142c6801c1d449035003644c0561a000c44060003111440c03034501d0300e1820880d010b0f140038030b4881c41c808268030111120615040129461059808228030b1940c1d03941d180c00018040c0c02012141640440b41a0900090942040050001030000e403824414913112100c0781902c1503c444090b400311f03544600142e021207000703040d0403a81c00020400c5003819010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771030809 1250 771029559 771029587
    0x81b220b03070608011a09090a050403030b060d05101a12040f0605011806080c062205151c02090604050d03121b18080a120527040f09170c03 62
    0x96071241000c1a1108014810010500c81510017000c600e206c49180100304000b207102c604004016541d115922400315082502c2a0414102e498009003040d0b1102c4a040c003000040105a94009a09002c004002101c0b000f401d015900706000001003820b24845441c2100b401000400461b9000005881c0c00d000649504c5428068031094812807034440003003002e802203410740c0c0c2008846030311894024540382d03030700e1084444140810b0b44a462038a51015440c01a504940055610001241d201c10b0302d1200b5001400300e1084040148510b03c0340395a141c0201d01c40c402d0340640005c3c00308401c0c005414144038081d8403520a1502e500d0039081c40705900f00303c8117941d00c40085550100e8440d1744007648405900030342c48007407500c141c06528040005582d8030403580010400b0f1596820403030a20f000ea0305031200c3c2c03802e55001c0e8504080d540f040c40da112040e43d181034400c07840d040c0c0004000c80c8501c11481c156078400403400c0900081407690002d600085c04c080c0380c0c2e10042080252980712 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771032059 1250 771030809 771030823
    0x62106080d031a09101404020d05040f0b0c0f0a0e01050d0f0606020114090303040308061c121215050108060f1e150a0816121401081b220b03 62
    0x4a60342c00074040c242c5282d00540d000300c03690550b2040e40000144a039448010b030080e021291105c41c2c0c40c203921860000711b8060b0060000c880592440d1008000c284410900d110542c0d501c2000303000915900c0120024640c080d1052449012006000700b2040c0b0740906580d4007010380c1410850304150300e0ac4490b00a991580c140c44000c551a058100512902405803603100010813210651910b00844005d0766804010405010054080e01013075060b110b08030284003071580d110380b20040c0f8005041079104c800e00480d410b00003d4100b041546507081900c129402282c0d0b2036001c0340514507010044551003401307014103900801042d1038950684c2c8016500105031841003a040f0594411000c110307600c604410140c0c03c1081c20020101d505a01100c029402040440c40d0307030481b0a0048211640c40713400548031113403031814428040d00e04c1c0d07182c0b00c6c038120307100c04049404041103020000c540f1102c0e504c40ca50000380e1190325076480b080160510040c0003500b040000c018489400080c81c11907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771033309 1250 771032059 771032083
    0x6160e0f0607051b01110c060d09290109020a0818120703020127050a03050711091312020313030b2e14010e0d110f090703021201080706210608 63
    0x408403016000380b640044c0e03540d00428090034898244110301081c140c6500341000c126215910000303400d888046158080c001003600484172030304034014a40d05c0700102015505149400183c4400050074420b180215000000559035280d26912151703a1200f004507920b00590702d60040950000350702c00c0e40341c040c00c2a81e000c3d90001c0342604042c8980e44105840c070b05610090f100707210609002c0b42c8000342d0911811380c075140259540040381452490094000d0800e648803040c5010300180d00c10003c814914140101151001011146c1d0142c1e60713442962404203d504480d02c1c00c2010413100004076500205104110507448202208400240202c9016a440141202e414001c9441c2221400d081180a00303040c5c1c965401000010307034580200384002c0c14080c3c170ac0034001300c60b110114203185001003c2d01d049003d040115018006c1d4002143c540a2498000700000e2079030800200501100d0312a250501d41400210000a03038006115a440e411502d600c00010350f028104013070b0000d2a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771034559 1250 771033309 771033313
    0x161406030a0e1c0e0f010507032a030507061401030c17150f070210050403140315040609020d0e0106030b0a0b010c05070305161e06050a1101060e060901060206160e0f060705 76
    0x603d500f20003500d48101212a5401110070307000c0b5000740d0340c10504032001035400d07080003511203c4030200c1c1c001841640341c04000c0400c011400008068010001c2c1c0403a510900d4148018454107540d424002c03000d11015081d184074200800c600c01220041c1144009246d007900d1041003403600c40d02c180481541e0241025148408201030507606201503440c0b2002c08800303003c0c0e81010f490003801c800d2444150303801e415000010442d4088003e0070f00b00c1505014209120103aa2020104001e401c490603d402060404041140c0000103109040641c0d500020400f016100c404440f001041c4c24030b9814140590b103850382d001b28004204000c02144544010640350402c400d155140342c07002d600c0104122100500c1021312500b41143c00251909464031545a0703a07041411103140c40c1c0182441c40e0b951030a01d0111380782600c08100c500c01d110075940c00e642640d032005c00721fa8a41d01222403543c200481030b035080c2d0f454450207028070320f1070006009110290120700003c16982c0640011600c603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771035809 1250 771034559 771034603
    0x7140114030114150304081e0d0f0c0305150d060b040b060309060415021207080604110a0302030610050c06012c0106080405010e0615121606050a02161406030a0e 71
    0x3601d050143c2c50030022444d0f00c410b0860905503502c180c1070241010841411020030400544504001c0948030000c3d4080750900210021003000001059443c03008d00000e414403001a485005010352260480d01c090700d1700b01c2c1c0250544451004021100030b05034030503100e4409504075907610010354007501914000e008039007820710303005400c01c03003110300496044c0c014008801481480d1441550010b400d0400604641d11400042d000b80b80d40282030741800c1c070204454200c590706078046c41c4a15000c1d07448203003d070b40c0506c00340c034103018490403804142e0020005000d40146903444500c00d003e816030200000102580f0056201c030242c100400088041c010030050080c24000c07405405000301c003030702d002e040094040b9012007400e0001802071403a0550303d519a441000790307200380c0741d507489003280d040d44507a00200258050300c000b5005100f50030015050500120540044404228019648065140500181d600028168900d080d5039148888100304141310420311050159950606 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771037059 1250 771035809 771035849
    0x6090d1d1009081b101101240e0f010807051c0209163908070605071e0e030d0e01020319030f0e01060806040f1b0806190c02071401140301 61
    0x2410713110328001000d8600e190240c441039195084203590040c4245480030509441e440081c2c0988030030607800068610800300007003404c0e0303220050820b032540b404001c4c01548031007964254800c000c3c0500c0f80d294200d52010000c514082600794035403048100b00d644c1040e560340014100080440302d05c0465880c4c1c001003103400303500904038906014a55500034100311001c280e8441d020000401040381070049140724180f201840a80e032003107070f0226052080c1c0c581014000e0091b4190114400e4042440100441040c024040803d5021003c0c000b06811802030b00200e910740c0b050006541035000800c9030318451a602e16800d6650300c99910081168092a44868107c45852050303131041d91400e0402d21018401085441c0c1040d0800c01540c1100d906040c106881360790745018001c010080703000040d01d007038041000361141060f111a240c50646400d0b064007138484a424400050300312420034800458001194000720074103241c19044606602002c14103603000b80c000d101c47d1030b107903601514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771038309 1250 771037059 771037063
    0x180d0f03120b310e011d1c1d0d05030a020c031b010207030f1a0906060418051522060b0a050301060f03060902060f03130c0806090d1d100908 62
    0x45801e07000c1e0342c05480480903001042d022140f440c490118010040d900e41d440e58000c0d08003401c601e0f490070080150196614000702c402148042c24100360007007811103030302e0103105102080440b0464440381c00422955054401441c500e0020700d074059000b154140204508102030034000303070580c0080c411545a1010103241501c85d90035000300e03501006200f90140d84c08100d900803240d0140510144040f00c0c40c040c0b00345d801c1882403941c81c811080030400301c4280054414082c007000d8404210900d4040309511800340050000380c6079501000c0114005885450415806814450020b082801c2d000b50005a4102450f003541d00315210060300c402c0e841c0c074500a100404046001f04151458100444c0030140c491002400740c659690b440340540d00c030401110b084018545e0b41d1607880c60301e0049002d80da03154500c2a503103580803c20124080c40001102350040b10382000601c9514050301e0308a034242c54008180c10304205400044600b42c441a01c00e0408403840c3c0c850310100360138107080074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771039559 1250 771038309 771038321
    0xa14010e07020c0f0301060b030c310608070306051207081b0d1202100204060908210d09021f08010e0f190c0e090a0c030c030e03180d0f0312 62
    0x8100000c2242030103801c03a000150500d403190166407841c1c04c1801500081d004205642c003000190000100b0080c4940c0441c1c01048045072064096406103800c150000b00508802c25041d948003e82c90b09000c0240070380039403580a40c2c00e1a000c6103031030301d610110701b8140e061444d040d9260b00215040c046a50184000c2c110403d40303e1803c0c0c0703d00321540008a4495000308007078441d904404602c03038110b00c240a100d05c542c40d5000250b644030307079414005000c14264031031140c540c01403002c050409030254900562030340c8041d000905006980380c0500040c0b00c107500403a03204450b0703c02c100442d180c69801007402070843c2c440465030b614107941c201d030408000344000f82c80305500c000c024000c000414483c1c0180c1d14104005130207022203e003642e1840740000c41030380c8107115004005030001950861003003491f0695007400201c1301500c09078151503a420090304203070030034012041c40400c0d92106201c24040100f01181c07507a40c2c5d844580c02c54941880940000340300790305290071000180aa4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771040809 1250 771039559 771039569
    0x30c2d0a110111012310030c0b2a060c0c01090507081606140d110405190305070518040b07140705060a0501050925030605030106060c150b1507080f030a1401 69
    0x7409046000000806202c07074001d09409807140d00e0001c1b80f43e51070102c0f600c40141d07501000d03008000d915024a48502c0d0010a82c8240302c081554901a140425182c2c0855682900b8000c01081c5c550110201e4a0380003032003a1503096584550030f070701141040001d40001c00c00d0001170702c0514628001c10407100560b420220500c40c01284d07074403460607900700329888401d40c604c00040c00d44402c8031681c0240700b07551146501c14602e00e0680c05803a980306030b504c07c9a03c0f841c02c50b5010f955500c00d02402050380c24500d250060b40d440018081442c5201080d880103070341c608290840d51041005000350440c5109503245e6100320708000342d0380342c148121405080c0450307040d0090305c1c010988600a1280031146d82c40407214240c0c003c009400381d0009400350500038006c0c40b901d5241c0b4001402c12103d080305589100d9210441c1c5804200c40c41a5840840e0141004c24040b01c91502500c290340440012540716500b04222200301d2000c401940c0034802030540400d40d40c1440c4083c0381c90100c180c2017 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771042059 1250 771040809 771040811
    0x40b0606091507230c09070906020a020118080105040b010807060207031104020a0c0b010b120f060a060c050a06050a06060f0336020a090b12030c2d0a11011101 70
    0x140818942d20032911854225840c4031280e610b040902e020074003124508041301110414440c02801a500801d00902c1110240c0e8403c2140c0d8070360f00122007240c0613208807400f50300032100354000365110300c80d030300101c0b0140080010101d60350382c41e00303085803411602034500015002c010710100c0010300440004045500c020164a401e41c0c03208150f110390001424410340e400501ea4580038010483c0f45201500b000750740400b0340e5941075800081e400f548005052182a40c0040c04e0340d00c610240f58001c9038050b20209905050031030680d03808186110948062248003590000111203005181c420070501c034000c03501c42d1405101408032a0702031a01c070249030a00340d01c503010400303560340c9484800c810b074510a0b03102c4800a41200c0103540c15400b81d0043e0000602180d035450a4200958905c4181c070080251184500c3e0542c9034042c510003074115400c80074500c20712244c0c076450400c800440c0c07845483c83d80b010801540c40c03d120190220303008072912040b1000c940c0c020400c4c0c40500d00c0100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771043165 1106 771042059 771042067
    0x40e161d06090c0903011821030915020309030f1303020a12210504120b0709050d03021c030f020a080108120f031303020f03130f0b0c100c1115040b0606 67
    0x2c000b40445030720300c0340030401e1403003031041c0003826030020394a60bc03407084414590041e601c0a8444403d030302c000e01000302c0158049004100070300d036014500071440c0c59071041c040495090b40c0041c1060910000d02c1011544607a030050303d8040030780e01c204c80d000801700c5c00e42d558083c41d080411440c40400780201085040300120340151403d40341d00303030701c40e80c4c8104020001004160050041c0c0007000161191100807140c11400e0450f030802044400021030640c2c1203030403c200040006501a004000d8804180500c686098150308079529203400183d449405100240000e0b01ca140014010320915100748824856080000180c0380d590304114501e5940380348030302030b881c0000a05800000c612404d0800c85040008041c051700d102c030b540c410300100410300d6441103001e2003e55204040b10b518240f2541003040c4602c444038480d400e26080044200c100280f07582c0c006d4000704 = true := by decide +kernel

theorem cover : BRFrame.Cov 770863309 771043165 := by
  have h0 := BRFrame.cov_init 770863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 770863309 ≤ n) (h2 : n < 771043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
