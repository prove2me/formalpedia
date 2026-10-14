-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2756
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:58.073218+00:00
-- url     : https://prove2.me/submissions/4fba966b-ea7b-44ae-afbb-477726cd51c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 495503597 ≤ n < 495683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 495504847 1250 495503597 495503611
    0x305060f091b060a031b09061209020306071404090c120f090b0601140f0304120801081b010f030b030f030a020f0619270303061502031611030a1b0e 65
    0x404841ca0481d0301c00710b0401c880441d039001d4a400680c51045500940215400038060903000443c074410900c0141400c003140540400100101e03000c2030030407018080c2110507600180540b855884405054a412004c880320b401d848609200000e42d540e150b10420355007440d16280c10b400c0704072010140707080f45d54000201070780d00e01c0c20b5981004136104418950303200c1820f080c45100007150300801c040b1070003100903045099a00004220030407010360b01165200c041500c407500c042e40c0350b00c01c15480b20f50341703940c48600850b9215511501e610841d03020840c0c1d0071070705000442341c3e0000c5c046420010b00c05000c68441d4800118070400650420a80c10300c40c1c1c1c510041c22050601e510300b071408610854000c0d01d030b0f6440d906d000b2428050207210540c00034200c02e00e4489000303989030140192181e84552024000d19868104400d0700100840b0b51606100c3c1e400d80344951140d541c0d1883c0140f00c801c480e01481002d603100c0006554071000502c5075042060710710503901d484a04000391400030101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 495506097 1250 495504847 495504853
    0xc05030f100506010c060e1b03030c0a080d180b04020916050429032503050c030402040914030f180f01090b09040209040f02030609093909010305060f09 67
    0x16080d612404100100401c9031140301207020780b07803040101c403c401082c0c4003400451a1101207400010300180f1010894241a8400602c01c81c046c105030b128010307a200c003411a0802140c02001030f4022005064488000c000001c41c4c0d40c014070340d95030f0303d4011801116044e030035000740301c203514001031815400124a0050083c03180360f141c000b0038500682c800d198881001c0e40e001444115800210070b129410305851603124130b40707040c0c0b600014416000c0b8006000c0940b444168a6100e4080d0500c00c200b00c40c0900d10b0354a0790f600380700091003d0003042e1810440302c1d00c40d00c8541400e01c000c0040500e4416900d0f00d51000c0780c04140e401a41642c01c034440c001c6c3d925034002c1350340c015042d030341141c59040074140c41e10340d240c01281c0a44a03d050031640719180010810709400141e010314051401692081001d903107200e0f80a40c7e5504042c40b0380400030900c6100300c0e00007014000308405429260341c000103958440c020a07081003080e00115402e800040400a4206c040c00300141c8c80a00c030001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 495507347 1250 495506097 495506113
    0x51902060601120b030c0603100e07120b01090b030c160b090a03030b0409030f0c05100207030f0807020d200f1006080f0c010c1205070c0f05010212091f0c050d0801030c0503 76
    0x307507071500410104c6d802800040b000030001c42201036100000c001c02c04159004e854151401801032034240a410001450861094040e510808201095580342c000540c0f4540307030a40b003004039800400e000c40b0a4802c403034804000803080281039002c1c29920005080740c602c64900601030754038085880e8012860110620b0100340d20220359084007095060041c040c0a40b03046c07403414070110829801e18a400000c0b840c0405a10400b220780d189940c0c0e89650300794649a000b02d80324854881000b0000e264040b40d042d40000d0039501d02801d542d0a0b00b00c03451220382a04880c00c0c0a01440325010a556504041040f2141030007d90120001100940a00c04202001030a02410050064040e0400d0690b8040d854020381c1220034107a00201303600e40f45c03540d07072807030b24000307441c03401000e005001d42e04c98103602d01d081c801510f50611000301140807024140301104082010f8400314010802d40024035004900c0900c1642c2c0d0a000c00d0b500ca40c125810b6003080c1480c2e6101e0380c002800b0354400c9030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 495508597 1250 495507347 495507349
    0x11010504050a08031305010c0e1f0e0f0a120b06030d05071a0411030a121b031b03030b120714090405190203210d0f0207150c051902060601120b 63
    0x14000c08981d42c0565610303261340342c0a190360070785c40500340300501d41d40c80e0000c0c00105c0e80d0800c1041003050421600c0844d28851400250400d0054440c5c03200410380c1001c80303108074a018911489a40c2c0040d188846096407101c40440210821206850040d5000d0505c010f0303060501449054070725501301146031007881d07640d06417006a002d40c803000305040b44c40821308100b410b45a0010100e0002d049440c000400c1c10b0401c0c0d407404840702f040114600c061803250301c6401c00000100d442d011b0b102c00320000441c01036194010141042202095514a0000c000d0303070352080704424581d0030b44004c1000c981044c800c4054101d8a001c840c0c07042e0941801c00000490008222512501686003604005145c4c80402d2504070b09440584400380c20030145008840240040d0407125640c2209210780035950b550031040303102c0c0032409008405410909407046031284c004100c00031030303440c2c00d52601c041d4022a02648902c04000030058101c002444103540c1e04c90f041c5c01d07580c00b820070204940d440c900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 495509847 1250 495508597 495508603
    0xf07021f09060c0f02120c0405011703092b03020d030f0603080301120203011118030705103006060306050f0111030a0e010e0607030806130218150d06080d1101050405 73
    0x2c803a030000c10030040801410420341031140d91051364050401c2c00141440d200b45078aa485501e40c160040e494400002601e01301c00404001c1010110003440c54079549a09004629401c00381d1415401100c4100749014913003a9804c0c01e2590281c0d002c1c0243d00c0b001c041c010242e4400002c00c069042c00c0100c1030011403a00400c0b241102c1c2e007450480189c04043c400310b4050f0140e0030500301c0204000c114801c10380042d4184c1c8550140442c00c0c0c03000c02d9101c000700240e02500c0d948150005071800011081d1900101c14203807008607080f0030800d9a13644d500300c0d6055070019000400081e4841600700810701304007000e0628100b0909292800c2e54010142d0b6540c4d01a00507032008018a010344440f299000b103241d1814400080c3c0016900e610700d09024295800075691140510300d0b43d001c82091081600c00d40b900c3c001c0740701301442000310700b008200d0440c002c82142410070404003d2001140102d00c20b1600500c140806083c940c640c0850103015211200b084140690400c010040015404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 495511097 1250 495509847 495509849
    0x3070c06170a1a030105151207120f0302150420121c050f070506090706021b01082d070f09060c12050f03090124240201020d020f07021f09 61
    0x2c102c0004001c4001e030304180c819000c410704580c065203032809002c5000c6840a440d251100c05403625846100c800903500d980301c40500c204501c0b042075401540005d5842d003401d040303ca00910449111903149030944a82c0d01c016201116404098045600249920400740d1241c98080b95105511741c44100741f00d4881803d00400c0302580303407421800f9401809141a00d102c04102540c494940007103281c0700d6034681064420249505c60310100040e00b620024140103000c4c89006485070f9241900015580e14001501c40d25800c1041104698a061040010091800700610b050a2030616003c06040080603492500c1048944e0f2410302185401c9101c0240300f96020300d124005490407502241d160286030304119060400009101c060581501306011a041143c400c010b0011401ca80f54401d05079813140c1e80343c01c410006503940405100040c4c510f03c43c1d150001625000400b00910100d1303100e10400780343c801c001b1030340c0c000b541428400c1803003440496013031510750314281d003020b8900892 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 495512347 1250 495511097 495511111
    0x203010516080a0f11040f050306010801020f0f070f060c03090b0912040b0f070c0e011d06210c120a030806063c0d02120f0601080105010309030e030d0203070c0617 72
    0x26040b0f15200c14200e94072450b0301418000045031115207610304407c16040c82d2190502c01e109a0b400400c2180341803003101d41e6991b80e40121440d04c1450030b010315045e08407450681d14841e1002500000ca000e501811990b603140d50fa000440d148240342000d26600c0103401451690300c40d40d40e807442e0004510440d010740320403442d004d803944500c1c2d41c0c4030204d1040d200c00901013600c0e0400040c15103024650903059078508102e18611b1400d0141035013207075030100d40003540040b040f2030034014400c0305100d440d010540360081d1207520340e5030382c0840d884800c0b03030690207569404039040c8000c0c10b41c0402d0b0343c0d0300600112581450022062404407120451190164080501e0940461005a404105c00c00144080e9403070351590080d203184802904038807040144200b020000440c6a83c10000c0607200c3d0105840d1303804a6400d100045008124096040303041c0f0030322190f41030107581c080180c84421106540116514200c070324020845094075407100d82800b6501039144007040c0d4603410035038880300d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 495513597 1250 495512347 495512351
    0x1c14071e080f07050d09080c0604030206010e0601050906030a180c090b0306090d03050903042c0612071a04030f0609050115081b0604170601170a021503040c0302100c0203010516080a 80
    0x2000c85c0050141040052060a0010303060019000100d203540c400d41c040c3e001e4400d240e0f600c0c4c90144801740f045034042d001510400101c442032400e400515007040c150301c800981d60310700c0da040102150ba06541076800e40d064034001c11124001d4014610854000d1b0082e25a0b03081078460195200d848907942414192035100080100d4800c206480007048440b6111104a030302c1406a20f0300010303001c480001c940403034001902820000004418012020018618945001300d91540041425845000420b0800000000c03c500103003900405024a00c0003400c00083c0c5052801c603000805134241800b104241088180008210702d844610a80e0700c4460050011000075041d01c00c54002282c800040307155100549030009180d4140c64440c80000c60f50f0400c04100740c0c0d0b8159000009520058002141500490140c05507070000e100e15140c1e09015229400100052041d2400c2000150703116a920150314090080c5504504c0d5050090391001488000801c200da00514a40c0195 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 495514847 1250 495513597 495513607
    0xa091404080702060717030f010605030f19380405040f120c1203140a110f0d02090612070e1504030b070908070f06030f0b01051c14071e080f0705 64
    0x5140d103801c417a4095440210b0420030504c3c5c10303540a082d081519050035100c20700001240c010b01038400c80f0b000d080c2c0094003100070795810f003090050070001c00303a02c403603c0d071502c421030084c403003680382084022414003500d0150b582c003090901a9060b4081444d11031403c1405001c04039240520300d458041e04100407516a80403240240c03540100610001e1841e40c413051a80e05035689a4480d0380181c21516044405482d041490350903204441004407003424100008644445940700820400081720300260408207200c00281d81c1e900b20000f1240d50442071010840969400b0078282c6800301d084691903141203407081c0402c0f00703008502004090f6615000451101d6010b682c07006c0042c080a000c481941c1d40b10152555648003c2c070403503011a08102c01c07118041a02c0c0a04080c05806a4405080c5400b2482c00c7c105042d11400790a0780658170400c6141c942c0d200d1000601c140c035142c0320f030b603801c0d82455062060080300365401006c0044c0482805502106002c1e0940c0100242c5420343c4c80c1c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 495516097 1250 495514847 495514849
    0x90f12031112041707050d1a130b06010c020a0905040506061f020a200406150f0503091c21060f08010c0906110708240609090a231603020a091404080702 67
    0x31481b90480d543c41402c0c42c9285040051902c00074544111740c82c40040d864413a144c41c208010714404000b400e0410540014940e0f5110344881d04009000805071034080355500c0342d40007100c0040c0c0302078406820000410465090420500c140703c4806d0217003d4402d01884002900c50b2001800140800089108007242c2c0300039400c5c00c003442e00000d00411200d41e40b1040030103075600b800d140c440420030203030f80840b400b070142c011b40e8882ca131110054000002c1d0095201ca05d40048103001090061583c1c00b0048848270b82c00d0a007080c6007031080001d0540c00c00300c514100c0355059004800c02d81c140303940703101c1203a1300460000c1120303c0350030311200d4000824841c50805400b0f8100020501c02c1c00c0c4400051084805841e0181000020300c81694843c48140b0181d040101d8003094150700c0302c240c50b80082c10b45004400c4554007880e0a0714040c10032540365040110041519940c030f24031030006d00075441c04191000c0184004e0004000745601800402154000244003030501c1c10f002c2045019 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 495517347 1250 495516097 495516103
    0x30f22030923120105090c0f0a050607030c050624101d011e05030406140106020d050a02070906031a0c03060102070b0f0706020a0c2001051801090f120311120417 71
    0x8440101144060b03c880c10b6102d000b01000c5072031000364420a04a10f200c0d0030200c117401280000503200e1042c0307604250510045510400301141000841c0c3d00e0540468070030b100ba0350140c95038007080b0125030201e1020f10030060703506220350b104403002c92118089075040354007000003a81900016402c076540c0da00680d541d81240201c52554405caa0741c0001a9a201e0011486584141c404020001d81da015444003100c090042c08050782c40205140e138100d005030040c01c0c1400444c8100c542454031900100d054070616442181c041008081d42c030b20030954102140e6000c24405443d500790318000000030b50301d4500744141d40504400140d601491000740088170800c2d50030038025943c8070003c40340180304600f14401500e103414540701e4440070702203030750310b0100d030b900e0503540c141c10b124442050f03075038500d2032145041c1800691400040d03498a84031180e00203200038211524009818213020b0b080300990302c8948129000903020062000a002c1660261803000030942c54a110101816103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 495518597 1250 495517347 495517409
    0x31718011809050a0f0f0614062808150907091202210304080f0304030809010809100e030a030e01050c1603111006060905010804020919020f030f220309 67
    0x605062404020705000035030802c000c12081728200f041a48180b0b580b4104854407409050801d1104014a111902d840b80c0031300f1401d2006000c003005c110010702140540201030b00c803480440c1a01c820809408180010702030341c07034410f4518440d949850300c801802120340d4010010081074007001e100541d102c1003c440f502c8294458603a00380700c091144150740f07822a22034003141d8440d0200b100d40b004008010742d0202d0354040000c50403d80004015100d1410040c0484018441e085081d01055802d0041c0800444a4000f4568500700101e0083c251046c0c2020940d0300c0c0c0c1890f00f031214022600c41100ca490500007040320b4582d0062400300d450261520300c01d25644101c20616203c00120b601c034000b2124282c0b600b8211650326401900c1940c403c45019512080c5103000031203820031000e0120001c1544080140b42080a245c0440b03a80c1080d036190a00a4407a07003040250404150b60340c2d402603000c1c500d841c1c121940d9031300810181a6000302c8079222301004500c4d00b10310b13001020107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 495519847 1250 495518597 495518609
    0xb04080d0f02070b160c050705090a020903010f0f0609060302010207050d030516082d091002120406030b090105010903050a080904090b090f0d140d0e1e0303010317180118 75
    0x25607160001e0a2a9100c0d030070603607500502000c17002e180b82d03466005065001c0310680c0702014000c042d240504100310b0410080c00b03000011340801c54401c4683e0284142c1a001c441014009800c49030007100c00203c940e19003103201480d25284d13080c0302607030b00051100c0c101c590403105a40292081d14040700c0d24090f40c030403c0b41c0072600c00882c008100012001c0c14002041d40c56112001501c0d0660a0010051490850562130108012030a9040400c0d60040419075401294403950381410400c809500c00c2e17102000103580c0303591188103485d00b40c20b1140103040034a0002400ea045458068540e00211002010714800003883d200c60344071a0406a402c076000035004046180492030035858681414801c80f990240314004a0058094120394500070003820324142030240d0346012000820941107500f1307251140c03c940b2030903038004044224174100313044040d54036540b451402c200d408400c480b120700812801c2c4034101038444112500d1150040c240b0b071000280c8090019503080405c150049 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 495521097 1250 495519847 495519851
    0x603290f0603100504110301140103020310030327090b030106080601080c0d11030703060f0b032b091a040618060516020d020409080a11210f0d1a0901050d0b04080d0f 73
    0x119904006e00340903604071600e02c202ca240798849000110100d120407601c0310b10b002881c507802e2012921950200044102c801200000b002c415501c0310107801c00f0b5401415200d80310402e1030158202801000001c001d031000038445541050a103e842e58104400103005151082d0300e002403001e107500e007543c040c03c041c080e14840c9489007088406402d060803040c400ca4100740c000c941c20b041c00070b040201c3e56000d0003002d1009540c0b105042048003210a14410890800000710748c1c4d08110341d24040c07c10000d4525695940b40c0840075028600d0074005100103400b91808000442d040011a050810704041d0710150030000c1c03000607010180c003100a5000703881c2c18030711810420741800500c04104c068a801c0c07003500c0c1e0000c18a40d0341001036500c600100d51085440160b0348000003030032582808040c001c5c200040740b03560700e085802403034101d41c0c00410f521846039542000141c0301c0c0540800d07589403014503c0c54445c07034045240070744000c0c54824006009002e044184e803040f05403112044003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 495522347 1250 495521097 495521111
    0x3102180411120f0103060e0d0e09090a0c080312070f08150621012313152d05010c050316020301060b040308040509070509090a240603290f0603100504 66
    0x810031921005d00049600500c1c040100018520004480503110101d40ea20307840c100049040c0101150064102c0403640701c0e8845810000700041600005040c854000b9030300ca1882040c0c890300c1c0030b000b500350800c0c030009010341c0d0445648049400c0e849081041400e110304001d0020a41030302c9080c9603680010356604640300c0442088c00340d10304880b0301014201070250001200e550b0901905641075010711050034541c406c0710032b44c11600304004043c0f082142c1c40e5071100104141d00c01e00349403840406960030340d0303c4001c0d451101200900b9003071819004228040d99055560b125184800000c01140d1480d001155000d404c500050001030b041035484a56914047c1c00b01d07041409001d218080140000b0003d41c400d40035243d08010003020700c18180c4419444000030f040042c241e401ca800141140c05404415461020080030a6030780050218214806040000703c3d00c92011068081d0048200443c0c2d83c2001400040c10304441607a5079444070800c00030b070f0305510ba0001d0341280c14500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 495523597 1250 495522347 495522361
    0x606060201020d0c02030a020d0e04140c0a0f03050f04081b0d020106030501050a0203040c030807030504090c0806031e03030705130f03031106070c170f09310218041112 74
    0x20f4502940b014000348014003e002c0140d80300d000740507140006030f0080c140b00089034031564003080010406040001c0401117000c98410543c41241c1003146032000103215000c0583c08540d091031030391186410002e5007840304c80301c000840040d10103041c52101095403501c0c120709100400d80d0703120840440e01f0b01200240301a01a240310b1105030751651034407000403000f1200d8000c80f07218661040380d0181041c2582d0324002c0903000424260204501031102180b04409842104001102500c40054610b4844205440c1c1041410307820191418602c60380014140001625002555410215143c1d107540b04c0d1b405803110fa681c40f42d1152804802c0001c24140c00005030402414510b0507103c02d41d54062059401d4580184010401d610600384d0440c01505134000d000c1000030201024580200d120026054030300f0100c112368004034a452520780501c44503c00800e0500c8850700f9420480407030041e5008040c05143d10380117544aa16100c0040040c0e0120391040d10f80300590344590030900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 495524847 1250 495523597 495523601
    0x705030619060f1d0a05010302070c0e01090b0405090102090112051f0306020a14031005060306060f0c01050702013215031c02070518040f020a170a1b08070b070f0606060201 76
    0xc40c0c002003900c6403541c41e0b0034a00c84c61501c02c1c0c040301408040311036141000440c000c2d40421010350f08480344906c0840c5a0b00d15150140c020000d0820200d07029850008000484038040c284a096a104001c500d40c20b0340c000c2805624440400c10029440e99110945401070361811b0100100e004201d1020041260350b5001d05240c400b20340e0b49200342c40d4901000c078084d1000337540da1076100180034000c0249181441c01190701071005030441c3d0030903e80c90f06d40e060580068200c8200d6035100c10820a4542e424450030b42000c045030020f0202d580c840c042c2052443c94009070301d0003269000c00040c2d00c50a1060303800800c1c2c0e4068210b5400b041000c0102c0910b80000c64110010300910000241d145070005204803550700811081130692a540c0c0c4001c42800d54002c02ca0300185001e10020745101e08240d40280350190101030855083c1d5403a001c2018018680741820030541c000048c004040c0010701d0106075424229106c2d9603646504140b40ca901170501c00810050a00c031010403d0750307041d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 495526097 1250 495524847 495524867
    0x801020a030e01140103021f022a10090b0f031005030f10050709060f1101110f1201050607051903030e100621051218060d1401140603070503061906 65
    0xb84000308031114103401d00840e451000e00c4080e50010305c8030350f5840c014a03d00100c880081c95401121000101c020264544901000074400076409c1080b0600d62410008220301c0e0000e00c1d464400c47d50360601e130151556000b01241d00303d103c1c001200084486000c2e0200102901000b81200c2099003080600c40e641c0111110f030118550030320003c076540c140100c0d801d1060b101561136031074802d44510011118030b1001502c1080c259205c61204030544802c0000b010964245104244d4403c1e0a20100c080f0380d5041e07004602480d010000c0302c0c04988082100600c420907400c140064603240d0070300f01d01416030100035078204c0c080c0840b07640800302c1d40e070311074021904800c1a00c2b009581c6050851a23503045603601800c0c0307803c408041000f00c40030400070b01d0484464180790b845804280d021800640026a841c003d159a0700340d1000310110300c000d214018140e007034480c2c460740f1244010540358000540914240700020010030059036641004c004804224541e60490a03611780008100c0411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 495527347 1250 495526097 495526121
    0x605151504030302030901050c0a0f060516020a05070506091503150a15021b0d0c030627030c0f150c021c05070f0206090d1505071409010c0611040801020a03 69
    0x4034100045452101590201c0c1c1e05074020b90300309815003006440950145224806034040c88400000190075401c1e0b11203000e006050000745840d00207699840106580203c2d01554013010590300007032000030b4510180c6100762045500d611505d8007003407009038026181045600040b00304a1454091580c01308507030303812180b000d8800d9440082032041c4050080ca0401030b04102440510b80300458000f103110300c0b0190040b00d144280c4e0700d55074104c1d0350035001114442d4581500120100d2070010b2100a015a0050303030003014202c0ea00900380200d165802004804c850001d00b003805891341c100501044100d0f4244000180c0d48002034403001541c1c4c03407440d450350051400034054494001c0c1c80b90b882e030128485260719400d0302041041d0b00441022640500306218030300000c2c00003600072840402c19400842c19040c100070251029220703488050240c403081c040c1220703d87c1d10801c1301a8280d0011000141040c1030743e1003028030b20540c3c000111070341c0002003421201e03034154803004032102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 495528597 1250 495527347 495527359
    0xf07030f0203120f070b041e0b04060608060609070305070c06060909021e1309110307030f0c0b0712030207031211070b060405010b04270603030c12080903031302030a060515 76
    0x580100201c00c03402940695640803130180490310010311448a4180c0040c09200808112407514a24104100202104861b4411034100340810002a405003c010f450428054182d40c940a40440c2c1f9908008140c04100f40d1036202043c00301340186410f40c51780740c03c008144003541d145c01056003c0c04040d0f00c00c074041c480c180340401900c00303000c641101c0c890004040381342c4110f0b010560300151000072020f551407103030031645907420b0703808100c400011446003141145040140c02c0c400c5000303407580e000c0702c0319032400c005040c00141c8e254103030329081c0e015050050300c0e100340f4101160401102614004400c0c540845410648821800303000403e209015003030745555500240030a4030401e100741010390005001c18807a9200c81d40303950300000724840050f983d18400184c92016104581e0054022400700900142845440c00c00c104c0244e41d02e00309032903d030510a03581a0349104c0108070320585c010b281080411590f060003514070b0150068414041c0b0704103650801c20303191078940c9e0144146 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 495529847 1250 495528597 495528613
    0x14180a0608160905130207020f060309010605151c051e0709080c01050915070f0804030b150405040f080f07080f0d0605120615060c06070c050606030106030803180f07030f0203 77
    0x10f214103140340a548018107220344210401354000082e400800c4100d03444035070780d8110b0f0b00d030340c030b6280c00356128034031050020400500c0c010501420f070700040c40f01049088200021a08080c400341c02048541d040c800015442d80c84881c0080c83c40310310044103111110140c10301c0b4280c3e03070003075406054641110039200d0101c0b5020055600b4031070300c40c0590300542c0841c1ca20084908840140400c1d0b4080c4400100203000c1355038012043c0c1c0250030880700b028a10f41030141c00042050000d00c82607081c0e60802090400307031207814030700d90201001000003000064641c1d80c1d00c2c1840680e040c0d19408100c2540b40d005140d5807010366005035081d50380b540d1070014006002d24116013401010b0724801c01912264450b0b0000d1400f072100040b10f9600481c081140d9103d5003000c10025100d002e890b590590280c4c11803800f035042001c05091b01d44a80e042c4070046c0041654401102d80112001400220310b104003503000c1e080c4400c1126506050203040000400d0010603020b068845100300c05036101d90f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 495531097 1250 495529847 495529891
    0x2b060b04180512030c1c05041a0603030d0b150a030b0306060409170a050418050f060f0a0b03250801181e0b04111b010e070614180a0608 60
    0x54901c01c00341a43d400721403010311003000c6900a6400c00c3e40c0c0080c051030300340c01142d10313000c40705981c1264000c3c0da074440c00c12060003180422060b1000d155074010a407410654002546da000d00d0240f00c00c80703599010340101e10750741c0e400d10f40d140800300001540c80c0c0d504000050f000708440d115460180c01110001121407034584903040c22581e103c1e403190b00e0f0103190300d01e244c00da421402c816001d0104c10000410903070044041400b1020390602d004c00c0f103150007401d4a1409a005d04418060b00c482603003130071310340d46071488241903401c1001e400762a5540d00158800e0ba00c00101042181c2c040d0645c2d2803540d41d0b21581c1a410707101c0507540c0380c10400362014510704841e400c0035103400d818001c502c0004038090a420007020180003c2001ca005441000e42c0c036200d6008041c2000050400c8c0301d064000c00084c01405c604144c08006403880c14580035002d0309625160b0440d03900b020000130040000980703042035911002010348901242c075241c4a000d4801e21040e141c85081c06200702c004055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 495532347 1250 495531097 495531131
    0x109092f09011d0315180717241504060e131202030a0c020f040e071e0503070503030a050c16060507030314061f02010e06151207142b060b04 62
    0x3c1003c0c0900103000008080400f40e0703c006014000c03081c0c01c4401101d0740700e03429003001705001902600b5142c2800c01e15004030949403110300902d04119900c2001085400000080c58990181d4440041b03c0303100300010020f0300030320b6140c1000750062107250501415505008000741d84521800702d030b0400b0103a00030705907528011003980400207580800c0e014010704007021b5581000201520105600741d150941034249034080d08000c1340270700003010b80321701c12541b0148000100301c158042d02c1954101000b10b5142c2c442c0b01d180c0d178180080020743c1c059204040100f800101150712007442b40b961581e40052a982c00140203030000fa0904002602d440074210604e4003601004100d45401d510720ad030500075042000c40000255507031803c450700b0350309080c00214030801491035441c1100020000f045800503050381060074507405a0418403083d444e01d241c0b5002100e00701c4018503416640e03401402040c01091030803040e80e604107002740c10841c00b50072150f14194222018802c548000d020448 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 495533597 1250 495532347 495532397
    0x60301060608100b0a030f0e0a0b1308090616080d050a060b0301060f0305090304080d0806030114160e0f0a03060b040b10020a0615170d08010909020109092f0901 71
    0x20302201905810008803200d13200805100e9254100411a00a60708a09084881d5808820360039008641000100601000c0312030b8070044803520320500040e140c843c2c00c3c603070003120030681c0a0701e0001005034021161950840d21142d00141843d5280001c3c0219405420300782c3c0e007042c0c13140c1040c2d4007068409124003624140c0e001c40e650920b025542c13800450250401401076601c50100300702c04a0701100c203001b078800400d0b02ea150407030642003079400d060031038170819501d0340c0858004082c81030030309150449540030710003807804405840c0010001000810742d083d5081c0d020500d4a800010000139030041441c1070302c1103a04009500409084c010086502d8520a0040e0805e1085c500000c1c520752029039240002c040a9980640310010007503401090b240108840e4848154008440e40c02a840e5024240c885030920210074103600281001100d80070311000185c442c0d43e89040105a64146c15a60010203001c126910b80c0a074000306662024440ca4001030b1145a01007a411550031246 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 495534847 1250 495533597 495533611
    0x10612030f0810240806060304030e060703110106060801050f040903050406120207060c02010e0609011b050d02220f0e040c03120915020714221a06070b060301060608 73
    0x1d01462030014040340c0e0b2607801811034070900010a400314429032003244079007804070030030340b44a4444420310014000b500f00401c001c1c8584020130070400080d5200d60203512494080d0b603400d45076410741c5001c0c0e503c10502041c1c1304040d031a0101c0040c4c46075011180724100d034400d4800d00e624410403814001901c00d60702000e0b0104d070b000c00040108511032800000d100e82ca0040050400c2c81c0c030b966000940d250b00e0030010050b0346030300403170031000c0d0140005074120501c10020408102d110706402d203442e0984000c5001e00101096080388141d070380d01155124541d516000902500074843e071800314200e03000d518205940c100e400f0500883e0b109001e401ba94004509901c00c524640d1100fa02c3c5a4007842401041411070b400109074070b030304800e00c2140c03080350040c10100f03081844418486210811491244901f0710140d503014161441000d00300380014800300c0c001040e101c45510324401000c00e0754205500007410024043c503100031030b00038541203000380400c541d114801c40301e40350140c50503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 495536097 1250 495534847 495534857
    0x10230108011a09060604030209040b06092503270c170d0203030109020c03090306071211030408090120071211030105011a030a2702030705010809070e0402060c010507020304060201061203 82
    0x1244851401803c2d240d44840c008010f141307001c2e101c1d03000c12480c1a041e603040b501810300c4810f00207a854204145170f030094130300b4220118030140e080c1c801000541c482044c0240750740d40407910040c10302501c02e01c05810480800040c01c80c280d01c1c0a151010180c0714032200342501e51074041076104041060041c511142e401117081d41d082802c4140251702c12030308086140300c01c12281c0010f031401c0c854140308080700d80b01c8000068105003010203845104e40d020f00000e400b00200000505820142d40140c1002e01e030804821002007004013080c00340b010950b0b46840b42c03690016282c19090102212a886119410031000c0c1c002c041c103090350130a0168800b1a6800355101c242d00341050003466100c01c408401042a08003100c01c1c1600003603610090040d000c0c4101d606d07042d400c00f041307814024402072901c1403862602e5070303207552544c40714040c00c04803883c80380105082d940d038032042d5076050244c0ca0003082581001d02c0040e5881e4018400c1030055400c003d0009920800001017180c956096166 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 495537347 1250 495536097 495536141
    0xc0c0d0504230307090c2106051c060f1802040f090b0c130504020a0302220e06120102040e18071403060a0b0409050a060b01120b060a0f021023010801 66
    0x103440c08035001984142c1c044c403a41c50005505400f40c05041c03c224125100d6080ca0401850300808240b4040d40c3e591000d4100070341000540c0f01c0701003400301d4800c000780c8a041d080251400d07101034040280100600303400e28521002000030703181101911071080724100108102401c00302c040d6480040d0240c02c00c1c0c40c1d60001107448050100602c1c0c4030910005113035902ea1039000150403604000c03921000a980802d4580800404c100307101640084041d05004061418030b101003080c5006201c54015518604c18580710242501960302803d00030781003801030302c0c6c0b00c003050b2010301039003662400ba03210395080081c008500094200e000c4d100039020301625940caa03a40c40142c5200601a0340003a6602900c00100d00240040204584589000701e10715010700300043c420800c8840154045240404094260390384204541c10030010303003085104e092500f00e081c0e05028501d00160001400d042110165402455050400c01c0c030b001d100d40c41c140d0700c41812500300d036480c1c5221210302116001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 495538597 1250 495537347 495537389
    0x1506120b06060708070c032f10050903240603010c050408030909100302030a0f031107050a0e130b01030606050301060b0f1209190305091315030b1902030c0c0d0504 72
    0x80240f024500034061a403408696a90b025041c00c1e140d4000c0d40e11324003465080082c0f103081c1c9825030000f0801c50303c0700369446a020000f070032910103940724801d00030f000817092142c2d20180a41c0c2661420351205258483c560010001c080001300e8816119500c1e20b00e030498054000e00a403001c2e2034190380158103242810085c00248140542a2218024008400401640d00304180c2c048244500d0040d01344000e00d01d00540415220040f1034213541041c0014042510356080513402c851180c104402582c45039600719241a61080021705003078500030000c41070282680084040b28000e40080007640ea0f100d412441d9809508c2c0031280c2d00344104803c00114500725021900220b840b4140d40807820000c40b0b07040c11030000d52085010880c0400c5684692414546688404001035820301c42da0342e4104600b4403480c3e190000800c01034040000c182a01c5c0340c45519842600c250800310340e24200315a0040032a004040e03021a1351241c00c0350111203602c40e42c1964200d80c00d812100c00c000030801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 495539847 1250 495538597 495538609
    0x61505071704090c170603010506012c030109050a0302210306040b030c03010f060e0f011508070c0c0e0115030b060d020c010b03191a01060210090812041506120b06 72
    0x301510780780341020301001c07402043d640b0461048012580b5603c0d04034a1401c65a440e5800041103148203903d408200301b42a40c01c4404258080c0b150000302000c20003044203101d640002c001410b400d0340c0b03030600c43c004101e4002907180c07006d4029022a1a160701c00700080da00c41c2411022081c9800f01400401d80c142019000a082c40e00000c0aa464424501d401f0078211422410301c2e01480c2c0c0c0b40d40080010503550000f094100c1c610b9119800f407913052a0a18201c0440da029031010403101000260000b03114002d1100741950110081506070b60b203801c3e10f0a075481c00c2c0a900200c404100c0110400e6000b0b110341003040034060005400d01907203101c040000d400044030101d42d0354807040892410360701070001c0c43d406540c0104560b09440c2904101e602000040c680412410081e0014001c803500040e01e51301c6800403030302c04144545d186c682541c10340107520014801403407040038081004809019001054400a4100821640da4122156080c1a80c002900d141514000b1070036900b801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 495541097 1250 495539847 495539873
    0x70c080901030e0610210210051b0303040c0e0a020304020f010e04060f030503030a0605060f0702040c0c0f050729090d0611030903042309060111070f140406150507 72
    0x14140043c3d00300e401d16040e4101602111a444000c20241051102d041c01a1106944429840f00003031914140c0e80031038010301a54400e40203100010071145082c19070743c07242a00b210b541d0340962b5180d041c00d20b0400700e8018107014401940f80040e00080d401d105503c240c0c4d1242c0d400424100c2c0c100c0704034005656140c82100c507213070801d440c0c2a010071803100162404004500c2100115038078580455810110780164011038814401000342144008078002551085034041704c0001c0d100300c0e42842950407186001c4000e0241c0300500c01d0740d050100200ba0103007200d420a0301c03039140850500508085058141c04510043c0090100300c440e405c0005070039185a00c1000001429040200310b0100d9800441f0b44000300d44c0006002d1094035124070361804082d848043c0d80b280e0040c0000002d007031050042c05a4100111440b00c0c410b00b900400c9000f0080c400301d00c26880c0c0540302c10207401c2075034400c3c08070341c0140d04040c4000b031520041041c2c080f5401d4555190f40c1400744540d241128100c40d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 495542347 1250 495541097 495541099
    0x103050a0b04020a022b20030717212a040506040f031a150103020c2b0e0d08030726010e0103060506040614060c03160809010206010e070c0809 63
    0x510455461503460300c1c4000c2c07000940a400602c080d8503820b00800c440d030041d25101008030b40c4c42d021b80c08600d801c0301a528030b0904039046c0c0002c0c1e40015007624610f005420303000d004000040300d500100549040100040000c5c02d2003005000500801d9510801044e103c0141c4c0300b0a500c04100c00d5040c1c0b101d00204100300701c000c1c1e450155103000084081d007080d089209800340c01e2108004220348290010045008070f54049141d1810b620703660380003000e10f00007905064000070080c0030380105205a0248010000c041111459200e0340090030b014240c100c0740c042000444030a00745e152036500c076000d5582c8803055038035503075480c070044031440c01e10582c0741c0f02e041e0310191080c00c1041e0200d42501800600c0801e595541c51400c140741568400740590b801a0b140403824080c2ca80c220170710405070201941c1c62503944a8501d2414030398415000707506d002910300c062050803c5600d80013040c60b2038090b030031075050b030362542c1e000d08401c00140c0d401e84c0030a14404e11440010350035000342841140c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 495543597 1250 495542347 495542351
    0x90703090515040615150e15120a020d0b01030e07060c0831290f070c1202030f240403140c060405100e1b0d1208160c08090103050a 58
    0x8090a45012440b042d03400300d4203d0380703a440d24859980101c0c2240000c0c022022107460710200d46d003019103d41c4000300481d026403205444840701201640450f0155080104001030070b16215918030000d401c130118906140c0d007840781c000060340c072a0091404050454029211a600d40b080540d60345844100403200e56000380250034a0900f800350402d104540c2c11030058200c4100204449442078035000000b01008000e04844450030400c90141d6905151204d81d65416607502e1001080c0a00000100400c031030420102d000260b8030140700c4018400c0d07049640303102c44144000d846036068400c820190300603070f502d01c0b07a03081802045504a8041e003820013440c1500c045610356980442c800c000c6560240c4140010070030100800603926004000800c13210003070180d21380d103503035201403070b00c03540d03943d44140c0103441c0d440a651260b4107901040c401d110700303000c260180c1007071001c45001c180304016842042d0b00f40d01401e540540d040d41b008500d480c06043c1001540181800707441410419 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 495544847 1250 495543597 495543613
    0xf02040f0b031806130c050a060815010302040b0f070b060d080304080708212502071403072409080703080d1e0606020a020411040b19051908091501050907030905 71
    0x3e8820311849003e020307000440000010103040143c0303c0b090552009018904640341000402d51100341c50341c01c802080080740086880303400407806809144c0000b003603603000150300280708180600405030140309000c55907031036843d1400c002c00c0070600e910140808500308006000946d01000a0081501c03c0001c1800e10074100c1400c2d0040181c08608210903140c1c8051065403000c03401c40c0030402025690343c4221800c0745800030345448d605d2040d490f0803100086084c555035020310008020300381403a004072241e520380f44000140540d02a0140205282401c0403610102c007080031400c0d41e410031a464a020011102e0a005286500003141141000d08222094400d80e024500041c02940d0003800440d950740108022103020300d06921451000300010450185107400355030281c084003181d1122128003800a841c40e01c00c0c8030640301c3d010704080507105043c2c1c10049840c0110b208808032100a61309200b501aa03442c03c1c041c1d907500c1140c080005007081e100f078001014a52281c0c003901c40174 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 495546097 1250 495544847 495544891
    0xd20030a21050a06290405040b03070909031e09060f08150306040b09191e030c170301090f020c070902180307090b0306100e0f040602090907030e010f02040f0b03 71
    0xca9050f155000f20310707114a002c2140d034040c1d40c041070701c80301c806007242414800c4c140034900b580704611403c1d009944964078844959014841c10006181050051060894520300200391071108140c0f81d040b0103007241c03402c0c281c0c2c0c840c2c41518241c41e004d8440d0034001c5d040c50400c1d43d20900c02414244100000304c4080c031941c50900c51075001d05e114a040010909001403801c2c2003400b030404442515112088080215107100c106805400c0c1c045181036941740541402c861103041250090301242140c03c0100340d03c04510000d60480f22250b20030465140170102035820781c0f1403103d034040b46a02c091000c0c0800b10042c2d008008110040701c0c1c400c00a500c00c030100c0e060280690003e401c00c0d955051181160130309001050f4001021000490801d041840d040040c503005800d650314101244002010001e417903040b12580d0b100103210b00180c0c44d018034010050b040490f00d02c2c005500705038400308845181d00a4070203540000100b21905800d0041004998000802802c090f1012103042e40e03103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 495547347 1250 495546097 495546101
    0x307080d022d150f01060e06070b07051303051609420603050109150501020d1407020913061413021c020603040f0b090c0618041d0d20030a21 62
    0x200c40c2555094052131602d821030f10000c3c44160b000c00244203920704d210030341d41e6401c2c0071201c11035071090f0144460b48480500f1215800f618403101c0d018001e034200402840300c0045d8500c00d240b201d8806d01071140d04c0308450410384100c180508250440c040c031040342e0000c1810403114aa6419060f00c0590040305d1704d250044030194410301c0403e0790750005100408644c06544621601034184021803880c050000f5078810b03c804501c01040074103240c200c035000e0404200c410f00ea4004003ea441420240c0c80d8115070391600303004a45052414841d048048541c0703507281c1c86081601421805040d0075000c0c0080c41d8030f40e100050110700c2c1e2040100040c1c4c0d46a003d9400b907801400c03000c015401a10305078520110203006081c0941c84889a4200f80d41c1c0e03241100c4030440280540340d0791f0b04649000c94080d02c40300549030b00503654020b101d40c05420005410090010300c0da05c00d58200710b130b00584400590402502c0c0302607003003001a082441e004168020030070392501c40031a5680145003203001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 495548597 1250 495547347 495547363
    0x8070c15020a090911070c06050a1101060303030501081027020402040e01120c09090c120f060507020d121a01111c02030a0e0402090d0611040b030a0b0307080d022d 72
    0x890340b01a0f0901401070a4490044442c50700d0039a03c0c81c0082e1901c440e80000c03042d00c40d00007002030025464110600c100b040b1648a01640000c1c0302060b241d14020b00602800d02842c1d00b2840340984224001c0309600403c28281003011400d0350740c0500e0f540480f4010502c00c02aa0800d0302008005400001d00c0c540b0b030700a0001420040f81d060007480c040c0758400059004100340c0e403d14002c03c1c00304034403000c80c604844a01c0d601ca8417101061a04102c1071a40d684042e01061030402004545038010468030315a505a9031540d5220030315021101c00c4601042010005032040480c850b5a0b5000c1e9550801c020750103800c40d0b18116440c1000c1c410040e50300f40c2c500c0142c1000c80d02c00702164009c1201c9025a20445065042c1018100454851801d01364082d100c5601c1d01c1200d504480345008507006450850031190342c030b18101c5041000381c00d64042050091048030700002d07100700e0105042c103950100380d02502000e800f00c280040407450381503d01c00c500400240c078605801040103801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 495549847 1250 495548597 495548617
    0x91509061612110f0d03051018052512050604060f03050f0714031f020c070b0301080f0a03080406020306031c030c140f0d090515090307050f03090108070c1502 70
    0x106842c0e41a0200800c1007000e0801c03200c155000000c44e02401c040480c080300c904404c0e00d4009416a980c001c01c8000b0207003035001a010001607105007140e049160030451090b14045d00c501c946c44050458128000c0804240c1c034001007207010584110300030b6800080d0000401480400c65585034200301c480c20b0001e0740215010f500000c000c10107280c003400110010300503200d0441318003010030b02183d25500040c151800240d2540c020000001c480e07815660391552140450b00503584503580303419903034003e016080482c419040c010b03c0340380d000038141c0e050b1503056480003515103c650301c401c081e401c090003665050107405101450400075907403052149000d580d0100c0c10401a5402910001e40b600d09200881000c120361004015050110342503d1000c1c040042e42c00700504003a401c1108481040030140e124905211642d203000002e000410700801c1524039500740068016524494084440d005c100e01d07400140d006400391600d046000e004061801040811b607044900320b9020071041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 495551097 1250 495549847 495549863
    0x60d1b0903061a090c1b0d09080c0907020a020618041103070305060306090304060f2f120435010f0516110307080a2d140915090616 58
    0x1001440001d0003807540c3c80189044007110300000c1e80c00302e400d50703400901e07041441c07900040d8940c03101d200c1c03074660345022038180c292103854203c0700b00284640d105104010042c840c8580c00103051814000392806500150000c044002c2a82d083c000390760809510040d403491221845900368507107018480c0e03403c0f1421034040d0f0f245400c40001d030440303c01904040c000c1c1d005a082211141e0000100e0f4146ca1050800c450584001203040fa86c408011000c070b10315503032400a00e41c4503c15421407203004001c03442918441d01520f02405c403680101d00c10000c4c10030000d81d080319480030004409000d03180d92114486801c50700200c460035260300000030070500d81e4070400c01c920441109912003009110b8545881c1c2c24400314112507403405480005081603400160400d90701d80141c40c40072205405000d04440c51030401448014a1052030184003c9180042c0150003160340c0011143d950400804510300520002030010300f0b5088445041e400400410403204080c40c5030744030404080c410410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 495552347 1250 495551097 495551099
    0x190305030706050901020a0c0b06030124050307081c140d090b090f0a0f060b01020115060207080705010c1e020307050a08070510022d0c04060608062409060d1b09 71
    0x1c0b00003200e40080c4a41d080340d1041c090030b000b150340880c2c3d081583c0d070040c041c01803540b03540380000c0c010810f00c20b044d0b052030f050000c40324001c1280041d142c04c989044041d07800e03140c4c3e00c0310229101c0481940c0e2041d001e0280b01e01051041c000c203801100800c02d401c44904044100c4907a0080f00c0c08258151a21102c2d002003184452082002100001700c240c050b00340e04590356900800e40660010041c08507031945014000350b4802d51001444000114000010983e110f001940f903107054080e4180601541c00081002d5010f07915a9048030392010184080d001c401d1442500e03848140000c90340b41c002e0080008031655001300000c0070b00520f8002d051030340d01d040200503400e02980301c20f40c15500f008004000031002c4030030080425a40e501c504540d01070755070711035041000540c2c6c000e9106140601c0425070f9640424101c0c4996002e0f1031041c504c0c24030703402a080b1220709840000410300104030030022403c00341c016040c0142c502c94003240c88203410b0315a80c21a2080920200002e401c004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 495553597 1250 495552347 495552353
    0x1c05070e04060501090501090e040f0b070c03020601060305070504030f060f020a050a08090105043c06020c0f0a02210c060c03120109110901030b060904060602060603070b0f030a05061903050307 85
    0x210302c1008001c00d0803d190000d00c1c120010304051182d1140114203000d850000d401e203d80040f036001c0d820b5010781100e80320300d0f01490181c08001c0301c0c0701c2900148180800403c0c103a02921407940200e0940d1129410a4075555604a00c0030421400f00c40e029110900c001e00000700b1f0000d0314400c404d0341c41c1e65894254602005198403c000e0003240940e0508080c0300218182241d40e0322542001440d0701c086404480c01140200c51114119a194801101903010b01c2280c2e0f000c0c10411480d2015a40c00040146006980d0b0407481d4000c0e5008400394120200d02004c02c2c040d410230070b00705054800c246040000a40c0c560024042c0c190780d50000504039201c02c41444449002d02100201000800ba040020001c035001e000e143da070615a55140f440c2c1190340780c13400d072070703850a00500a021031502ca54000391203403000d842a6029118580022071381c6030340001502c44030a207107030500b41141d8400100b4005400064049504a40707104212880002601c1225001c1d5000310b00460b540c503102d00e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 495554847 1250 495553597 495553601
    0x5060a0b07051c320f070c030b04080316030207110907020f12070507150c02040218060d0c12020c10110c030d0c020601060e091906090c030f0b0102160b1c05070e04 72
    0xc000c0c4200c0f040e81c9034071030451401c80130540d201d95515122503034690031203240801f55040c0319000070300303500b08240420040015060003180b158503910300083c2200790b102e81c15002d902440030b005007849504002c3c4802e80c1040c60505a0002c46403044420b03c980004015052203502514420503c4c0001022818040200401c2c40203040015111904410814005081e0310402d0390080c884c0d84c000480318500100303c1007500c2000b4006151030799582d115601900180760000088010840c1115103410700c800c207200b641c4101c0c0f032001c0a850310319403184c050b100400940c00c02410062040c8000048440100040c080f80c80702100000f0f50000d403c00e010b440e100050f40b1150412400108201903502c0318040d058020001d410304d0050040c1c004078200180420340c0003659011f2401103401580b0b641900006040005224100034110080d00121707254554038074002010341c9100b4040000c40c403200014600341d505124980074074407551302c0420941d4010f40d16100061103114180c1d51500d054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 495556097 1250 495554847 495554897
    0x9062402070605120405030909070f022107020913080313110d0c06080a0603080c0d0e04060506120919110f0103050108073003090e090105060a0b07051c 67
    0x15000902007540b03040700c024040e00c1901c05201c1a108160046403c000040041e0340001c03034024820004c91514140007400d000d006028100107100e00d034040c408401400018110446403002c2840c45d1100b69003d0001a460140899801c410640164404244100041d5004a0560340c03050b56800b01c1d030801d001110105a0003d10801400540c000028156801002203411740d0404071045c0e511802500001c01301544007500c0c019000802004120010032400c0001465446612805451005000442d03202d4068141c0200d0100481c0c515190310305449035101d400c00c022140444030305007031419010040c183c2244e41031070944c103411003860400c080140480c028a01003200b50304d03184a0a0b0389000038407400d80e8070050354030421218030702441701041104402410250440300b900d0014a80c442e00d1040080c01d4481d0408208070101c1070060034040d00004040d07401e8141030121503400c950201d4422500391040e00e1842c02d80e8000109290341510300c9494841001000548002c0703410a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 495557347 1250 495556097 495556169
    0x10c050d0e090c090f120c0d05030a02010c05190c0206070c1d09010e06011e081605040617070b21090708061e010b0703110316200121060906 62
    0x60110700349a480c0c0464411741c003141110f5108201c56181c2c0071a0500d56a0501c441d0040300a14003a010f000000000300142000c1e507008112990303c4200468190080c000c200909010b0b400880c4a02ca03c03c02c100b0441e240000c0c00640340480035543c0d641c034a4500e0307000104030101130b44c10410744856800c481e50700031480c40081c0004034101e1004d41e209c0c00305006081c00c850869000840f4002d01601c80000740415004403440303104102c0003850101514807c031403049043c0032000c42d8080c01015000d040050403401048564104081c0c007286404c00c3c155010b2030060101e00c00410442200701038098940f88000d0407881e820492040d0070141c000b41150901c122020f10041e8a0315100845030444283c20f07161902c07807007e480c04469800325000d0310841c512001c158400030152a000c420203640c0704148241c200180900d607000c40c0b1079a819514089a14901980f046c1c40100001a560ba1414800001d050780c890310810300b2119140c100b100d04151207104c030a00c07a0070f9003007060b0a482e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 495558597 1250 495557347 495557371
    0x9060b0901030c182d18050a02030607020c130c030b060a0f031514060304110402190915050d0b030c0901080309121524040c120c09180902010c050d0e09 67
    0x8011181556480c0812440d101c220031508000c0b110160076404034116062440300c6c1c0c5200c1ca424284965240400c2c42c1c00d920a004400201d485103000040300b080180020348018904c411403400c00004100981900040c95203580b03094842e03599210003403404c0c0b05d95481e4140340046281004003142c26020780003949008180e4148004c0e00318201312903140d98100c0340c0c1175485d521403400c00c0e04034020211040d0841d002150300b1188246096008000040c580e8036034400d1551640c800346001c0c041074100380822020050085200c4440c5c200003004e55024049035a00c56060f400710340300034400d03070001720f00e60008151018145800041030b8207951540c4010710051080034924049070402070034242004200c2c80014183c5a181034544d88071590062080114400c00d031806002d001860f400c1c10205464819501083c5001726511019191f810400d24294401c644a4100611050074181d0510504400c00c100054041240c1208401c017a40e40740c09402a5a00b803028504002d0310300f2810170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 495559847 1250 495558597 495558611
    0x60e06060f0f12010f020d0617034305070513020c03250602030406051b0a080c03070302122514090f040f0e011b17040609060b0901030c18 61
    0x10341c4007611141103403802c403241500002074003c558014441010160000c600210300c04003407540a50110b0f04445c00c0c240314800600740f105921f41c8030f104104200720070b081000e000900700b007600b18214818892003003000c00d1585401d1070740142844802e200701d07081d5112030014001418541006008991111025030414030158041526400783e030b030401d0b26160b0344100c840318401c00b200800f1380300c035001035046540c0e042c10305110018107001c8070f06100d4261801c52402150140800300c1e0040a402d45d610300080d00c980c07802411950000d1f044904058091101c688a0108a4801c0313000e683e5000f803a46005080b030000c0d6a02081c03400a54082c8240c1408800d60306002d03a0880e40d411100304c412049010a00e40040e0041281c210006602450031814a030125815407107054020314001c03a0303c0f1180d140303607002c5888047c00c2400c2044042d003030020a001903a5a04010211480f8140125028500101103200070070240c0c0706640000c0081001c01c14060740110b4903c110b140c9581c140014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 495561097 1250 495559847 495559849
    0x812070203070e0a06180c03050f0f0a1d01020d230702100b03150106030b0a0e090a030e180723090a051e03060c0d05090c0306060d061404060e06060f 66
    0x1880e46102d0800300b030034840c0018860780c4e07103580410042c2614031910b040440008116000130081c200310080401d240c000440c4034a034042c041280300b04503450031111199120a020380291031074025511503007090001a40d4502d0080c00502603c441e074460000710480c0d010b103074900304001c079454480030214040900501c65404201c650402c03d80c038002040341c0303102c5000300e03241110348000d4550100c020701c00491042d6042e04801d010a104584403c1080d480300c444100c040401c1e101401d00364844521180001c0c00f0300e421b510310183c0105118440d000413030a01080740411101c11000404c2040b1410502c0c11011400c17810050006807075041200500c04241c14940b1402024811141c0304002500b5048412030700601c0107024040e10350505080307802401607040b1110b0010700b1814a00021482800050b100c610850018014000360f1146000e20022003481e000c04d0316981e80300d4440342c2c400c950f600d00042c0503902c941c200090b00c183c0b285403541010000f52603d841100190507036407071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 495562347 1250 495561097 495561103
    0x90a05060325020705031024060e0d0201090905130302250308070f15050a0c0e0603010b0c1002070b0406050106170c1b01050c04090b03030a0903111512010812070203 73
    0x901141d11500c10260044100700ba032a0204a905c103907858070a40400591861854000c8480c0c921080110290700403114950b401c030407814004d10000620491465005180c481c420b05031180c010706005034881c2e1101c205c0c1d8292032084815480d288c3d004504002019030410880610035a40f400c40c86036828100d000c03400c101d24611001d44251004921103060007185141955803a60001d8401179400310102c100d0094041142d08000f41480d0807440305c940d1303010304402c0008150041145142d6800d00d04c070700d031040e004011004c501d44140842290300704541d2000b040024010380c076510b12031806141c564192101601300f00108000c070104100d01c150942503464024140b001c6c1682c6803481500c2c100c00c0f440b000c42840d4500d600300342c2407240d1860140010b1080c0c4010400904c44580d0000074140d49100316491080014803035641003001c01c2084011911403400280024450b140c42c41c0c03403142607042200141c000100b440c0041009031000c0203481400c40601407024240601ea80000761 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 495563597 1250 495562347 495562381
    0xf0a1208040b0114150a0201090b060a060806100c0c08011e0204030f0b070e0d03080103020301050708061311040e0f060310060612050604060b0705030a0210090809010509030705060c0102090a050603 87
    0x810601400300ba401d56034940b00c5c080e102111400e11910f0390400700000780078014904080c0e40c110111000303e000c6042414905040d40d0301601c03410f590780c175200c2c00e11070000344201710101044480c010190002d16005449001403c10400106000945a1700420300c981c00507400000c1500c100001c000080c03a100c1c03e010300345e80112861206607644041500d0011117540090b621040e1501d80d101010b40000e29203041e24001d50007005207940c1e60328181c0c1d01e00c5c81558029403012012880c0000340d44a6044983c4030103560008608007540c418080140200070744441d50074090b00c804100003418204241400c1c90f030100b8061214916044018250158105141d00c0690301e48000803002e44468028600601c011400240da03141541825601da4010071581b82c01406011003c82c65108d0a00655214039044050240340024031030040d180c55000d00c41c540d406009000d80011655a00c0c0d0141c000c501100300050b03580e81c0c800b41000302441c4140c00071403007001c00b8014489030710f40441d0444 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 495564847 1250 495563597 495563609
    0x604060f2601120b09010603020d120908120a02010e011109040b1c050c090901050f0c03071107030c060e03011e050601090305100b01032a030f0e0f0a1208040b01 71
    0x4181840c40300400303030303040406092500660300403200000307102c02c0d112820300e5082e014004c0006682c88017408607007640c03110b20001e54008101ea2000707001c204500c030076812208a904003404900c0d51440c9241c01c11070500304444035400017040b0003a007a6020b001c2c00c0c0078101100003c00c11036480802e510554003460b03080900031941e6403400d404580b40e480802100c076918882c800d1200d201071400c1560781841e1422103000342280c2020904c14001405818098281c450342d5054540c1c0e030300c410b00501d41000308001c08021401d08206d40c45501400128083c5018a10385040039091900140c107006e0744121103030282c0c2c913000002119111160711032130a0400482c0100341c40d00e07840c0049803120600d070005071941c00f8403a2901c03150503040d41300b01c002003400c0c4c07428043c1e1070100751071901c0d500141c040d04100018100c52110554821351042c80004040f0400040042c86046468942644500c1d0040c13180e1110002d8814481c2c078007500000710a040c030f07041015180c681e03036a983e6a01c040c0310701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 495566097 1250 495564847 495564857
    0x10605130c140a020f070b030406180b0606091c0302060105011404060206010b070302010b060a0809060121060b04150b0301170109170d09020d1a010e15240708040906050604060f 78
    0x480910380c070a02c00408178001c0b0000301c07081d1a441c3c00a4036555030054908864403031812241448000c0c42c2e00300b0000382c9420440301100c40d5110300510505500600c0059030201c40c110700030a50242d4580d150ba00f00d802035004109642c189000941594150307a160308003040b09100401c00e142e40061078506461004405a40714107252406901405001d000741d44d00c14800304041c0021ba501c100311509ca079403550220340c4a80d90701d181c2c01200700700800341405125058280c290100c0c40700d40041d4106d40000e000024901c401e076020748400c101c10b420410400c4400401080708140d12902c4e0400c0c1350511008000c00c01140d500c3c00180c60070144030a005e200041070609001c0e01581c4214420f80d0068103000840c6081e2800440a000560329010103a2030400049001e170f643c01d01240c0706941c201c40b440c003141104020002881e520810342070044181c43c0c0ca440e002802078000e032426a1080c08001c0c1c032107045c00810710542e10704d5040140240d034217000030042240d02486903c1c03040300c68100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 495567347 1250 495566097 495566107
    0x50d0311030c01240509060901090203280c0810120b0c04080115080d0f050d02090616050a02210607080606090d08030a0612050318060c0a05010605130c14 68
    0xc64114015029655034552815018408481d4211031606075940000da00d001e08548800c1007120416094420b01e4104103800e0041c05111265070046400c01442c8030103a49003081000b0302e03a00588480e401440a40d25000000441a000100390340c11404060f00c0414032818140c010a4a003610700700074000c940d448010a45444810003118007138042c00000b40000414028140000b0140e40700d84103041c802c4260420f21640b05403407101c0c0904960b580d2030b29112032201c0708401781d08149202c540c0418100a0084824418500355401601c600060048034540d4010045071100e11149100300442c1c031666529015004203c0d20f91140c0c20b070a11804036100c1d003010070118000d0020705504030b0490b011807014030085070003840c443c4d405c19405109151b2540410440000d42484c0240b0310780c424480c030014001d0385000701c0107180c0040d1030542022000501030f4581036000000b50b9085c0d42d02c0500303200c1410070000400400c000c030f04050006112242008021802444014420040c080340b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 495568597 1250 495567347 495567377
    0x92105041703071713032303210106111906060506070b040c0909051f0b0a03060c0f14120606040f09050f15100c0c090911040f06050d03 60
    0x180c401030494185a40760381c05014208580e02ea20103074094416a110f00303881c07010307005201c007291003200524079040070403442c540d54a0040403034081024094400c142c0740594408041026100703c5040d000c0c00c100d102c81c904024040c482043c0c03ca14200141080d56040c080c00c0021449000d041c18240710040c0b083d1030600100402c655003000c0e922140011740035040c054215040342c0918014041400042d690701c641a0481c3c603c0c040080c46600b200f0078000446a1456441c10300d08420fa00110796490f4080000d10f840c2400e400803501d05030b031424429240e540c407a042d03064480c140d08060442150031030401c0018000c84014581c00b091860000340103440b00402e54000b0880f003541d11121f551911400e00180c403007140d2001e0341035000300002d5600d410311440c03103140000140003098142602c003400c031313030000b110401a10802038620300010300c400349120b60342442d03002e01085ca15a03800c1204000545580005025005081c09024415540c541c03540074035035075060400b2894488450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 495569847 1250 495568597 495568607
    0x210903030f0307030902130e0a03030e0f030c07031a010e010306050702120a0906021501032f1302090f0a03201305010303030504140706120207050307060e0d120921 72
    0x201c544412100110038040c2558040d0444801c440c0b003190707001c0400b80041d4004044030b10009100b41c1940c00741c205040864084c1e404100c2c5124204203030f801c524180011545076602100000040c3c2c1e002240800c18002c58650418204000c8001591203526050005902c214107000c09003500d9030b0b50780840c007071034020065440b11040440246407240383c07001c1c01502c1308813079100300c402502035064103049031480091114181ca40c0030b00031284412640c50b0003450300000344941e03e5006800481001156180d00c2d400c0c0a241944501581c2c07032541105000000c81c2d042113080c010302c6c4101081c00011032620041240f440f026100584052146000840714030348803034a55038035441e01e00048249549500001d100d00c1c09000b2100d0301607a41c2120075950300c20380c031908001603100c115400340280250010a44e40380100700320703420700071b541d1111070403100446c5506d60168004001c50b4120f1f41c0200c515403c20701e040004015410940e04c803c040c044003411080380b400329040c07036081868040c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 495571097 1250 495569847 495569857
    0x3020315040f0902150301051905030312041728230a02030d020c0f01060815060d03050d150504150612020306010504080a1203050609010302010e010e150a02011a0321090303 76
    0x280b5440d00107516003481700c0c071503201380282c82c001c0300740c02d81101c8803801c41842c1008403030004c0d00542c40d02050340e620030302c0e5140140040300c02170210007400b00c01c40440c03000f03450450204800c501d01406501a52109600040b120800344130b600e41a0300b61940301030341006001112000041d0b50340236054001c80c1544108003009081c4c40c4042030216605000054615144074404000c00030651a006025920400f2110740f00f240c404e000001200c50074080c10706040244070b030a009040041002d150f6068481d8020302010684912320200700c00d1030b00307000c0c030b04480c10420f030148095814260b000b01160b4482016541c120b40000214840d6446081240e0040404400703440504041d071500c51007000c418065a00024200b6011503550301d041c0b130500d81281e81c141c60b040041004c900040d1450031343c607030400354040c1d40c0c00d0011402c41080340082007c84020381c0000703031201070811100c0050700d0110140d40641d00c14106c1c0140c107200840080c06101c5100d000030344400300080000d145101d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 495572347 1250 495571097 495571099
    0x6050709060314132109030b010e010513020a020703240c320403061b030b04021602010309030c08130e01090912080910020426061006031116030f0f03020315040f0902 73
    0x703171084055015601041000076a4070a10f09040207903038480038446000801e02503940c0c821000c140c1c481c890030aa500403c0350b0310060060383c0c1103d980c0d4030b50301b884a03c0446241702c07840c45881545801c00c114407d104c14031030a070424075401c6900c0d00c0394000c020510302c19011440182c2d04004401c0500000303880055034011418400e02c103004026403042c81d69004040b02207810b041100c40985041c0c0259090880762511207160341d401034004402070701c0e682c507040d428000e0140d25a404034048000410206010000c801c440c0303032400800382c07180c5205034400700d0310914000c11113000031034000c4c04000a410501d0460f2251b111442280c1c24240c00f140282d503061302c0010002040543c81200d0f084858207091000761303894019090342d455200031541e507864801307846018401c5078041c2d03001440fa0503820300204c2c14841d4401c200b4440e41501c4800390040741418210b080c000e980141d00e00e079090010715055003035003032151a241c2c4441d8520619485151104903071043e40c0d00740d9004641482e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 495573597 1250 495572347 495572393
    0xa0c02030c10020a0b0c0f0f03130f0c230a26070609180c0f0810180605100c0c0e04022706040b0d03050301050f0a080a0605070906031413 61
    0xb1810000795580b004010101c030000380c000000b804a80b100c005031014031082c2c10611340707801803140b8150071031391000385800c0d204180100320201040c2440c0c3e4201929100302c03000e4000070308111002c9200400c130800798602414028030f0b520f2546600c3c0c070083c226442c214461070892840c01811501050301c1d41010010b01c50442c0025109512074110002c564003144140543c0703543c01c144209403283d66000b100441c1e030003100c0c02d10092180c070800e58019100780c0610a680e40b92855031a00e50203200c1c0c0600410346800040c002d514009008000410260504c1e58102c0d10310703614500300c5120707481071143d01400c40d000603055445140c3c450641210f80200480b0211440240350f10031103080d201e00d0f0040b46442c51840c100d0600e0812a880503405459550442e0300e001c0400c000300140d00d5005801442c00500002e030b04008100110500d0710903030300402c0515000500405162540e80060101410140e00044c2c0c0180141100e4001d94001c2206020191500740b00c21503c0343c596000040361 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 495574847 1250 495573597 495573619
    0x130b0d110a03060905010608060105030412120c110d180b090103020d0c1701060203210903070602030f0a0513080403080d06050a06180b0c03030606160b011403010c02010c050a0c02030c 81
    0x750b8142c3c8440e040e9155136000708041d90f01c404003200c420000301d91480c00b041080000c10040b42c00c1c0b000c2d0000d034600078a81103042c526015013842c152081c5900a9011807520b038400d84249400340042c0c488003801d460040d402101980224461000c80d10440108000c000307030542d46a4030070380454200c80c04040041c0b240ba480103000401c0288414240c4440002c03810001c40c240788080b00700c650f41203403400031660b4040040e9a40c014010040c0c15044144030401648000035010300256200740c0c2000d10055a9181480b01482a550000d110111800f017032584080010500c030240c8080c0c030380000301c1540b501041c072009402800c1d1034000c81e50004807020009800e940c002c48081090750a070401800d1a5510700c816001801401c4070380e90b160b00309200007500c5040c0000a405e00e1003400d50050035040701d0b03480d100d6040d0f0080e0809158003841c040145840e080902508217060034910003008034541c5800010b00d90f018940c00c17a010406007400e0a0295a0100071020f010b0200900b000406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 495576097 1250 495574847 495574867
    0x100b0f070203010c211503021519020d050a14090a15110106030b13050a060c0504140108100501030b2d01082d040602040e1003050601050303130b0d11 66
    0x20380c1019200301c0c800e60801900c20b0000d07106200e0345110350000700e10b5400d101000c030a05409083ca0541c002c1048041c15000005691106843d40140407410b864503a80c901c20901403050106d02e07481c01003950b01481c0f0340ca13012035201f8101c983c1c080c2c1c940703400c150b050385006840805208034a0340c1d81d48214003000110b0302c00080181c2a9801701191170300304405a82d4106142610218030000d0501c40002c070000d110542a100d1401c2554818015610f03091840d0759460f04951288041500048002c603091041d4440d090b8120b021312000d090403503030362800350800310070a141400303210b04064a460000c1260344a0b404018050300344210701002c1031011003900c1c0c0304510241c034020300154010002c00c8040020040a90113600c0c28038600c07200003c1c40c4084020418064011903500c0e90030040011001e0945220a00685900c54003c1d0384c0d510358207100e445c0c1101038118a11035001048014520b440103180c1c01c045501c8451183e4489008114020040106e842c00c0c00e000303c4000303200084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 495577347 1250 495576097 495576127
    0x6040b0c19110105060406030503090f19080105100f0e0604110c03160209060a120b040f020405040b09010f0e0d0c050111030c0c060f06062203140a06140402010c0b100b 74
    0x1040b220080204030655581c0100020340d2114800030703140e90010006510703103040c400d00d8085240006810100c1c0070780644101041801640e002e8004c503555101806942c0e41c1d680d0702400100075803201201c101e0308003601c4680d00580500b105120790707519030140d41c40038000004e641010700010b007a652650300c41c18119011521a0340c04911030380d83e9000045451819600507800c1d0341d00800d0506244144d0750310300c0385010018000b510884803a40c521801070b600c9001c3e1510540c85400600341c0d0342003000500d42526402c1801e921014204200b40780a144002000c802c1501a8a8540a1408503003042801000c3d02d1100d190300400020400c0302d0310b04040001c0916a03c10405c80e070440e601c85468083c80d00c402e4407200e40c403c07020029803c6015a141c41e0f80005080d50480b5041240e0701d581e501e11010200c140003800342c00c055040000c0c0304503445400030070701440c00145507510b0546d0000380840c41e1110010710030480320002c01d803a00e0340003090601500c401c1b02803d80c0c0780d05803030014030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 495578597 1250 495577347 495577367
    0x15200a02010c140a1713080d0605040f0c0e131515140702010905040f021c0f060e01080d1112160611120a0507031112041b0806040b0c19 60
    0x716500072004420180c071007040b1107072a5113a40e903881007035444241680160030090b2078083d264a5044400021440c02002400e40d03144100002a0701807601c4280400e58400071000d084081c50000c1d02942590048070a4000400854a04400c4d1500340000030060034146070f440340007140c500340810320724810251b0800d0f42d1030395190302c13500e0341400070801000e11071180000c0c0010318402c4104403034281500940c40400b2080000350520129074410031748641007400d0b5002150715035500c0f614034003a5214000190000ca0b80e110b00541c1400d66035981c4207a035031240c80403c0352007804a01019800d1080705503810802040f156903006001c2c820340c141020f100c054640314036020703c13010240e103440c00304c0321840c1c40708042026a03a12420741c0c42c0200700007842d0070705060310381981c04211070440005002c0d0822207484191305040a003005072181a50111a010030404c0031420b201038100002da45a005604c03038600c010594982d91034100f40d00641a40c0f419840d0148404080140c0005c1c440d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 495579847 1250 495578597 495578621
    0x30905010501080604050f1b04021608070f1b0b2a060c210105010e10110304091505030f120a09030c06020d0f02280606033c15200a0201 60
    0x1860090007064401e0b00c941d004400b4446d4002000340403508d0f410b00340c028110304c490b1410681104030072a1508660741c2c0c448402298155456030071281003040c2d121a0300c10100c40706091004807420f1900f02050380c0f1411000d00e501c140d800c4c0c038039841c240c801011009490031110540d20141441c0100404542140924410060130394101040902850005604840050750340d00600322500f4140400010031700e4540c401c100c582c81715101f00ca0006c200800c004d00e101c1f00700052044d411000d20049400743c3c2c000501c25041600c07011541d100010301c1000c080c1020360b02d5035036201071200a503450280e0ba4002002c1d6650075030700051403030700440c000b800d0703458540780c110408600100490f10317110b41d0106d142504040a0f82517120b001d54100c5640b45034407a07240010303242d072a5101c0d51b490002d003542c2c140304414130350107404ea441101c6162007415151034500f40451000d41d0303a80519600001c00d40214582e85580c2c0c2c80448015407024600c04040c0941c40e5900c45854000034040c0c0402d03220382d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 495581097 1250 495579847 495579853
    0x3020304060e18040320060106050405031005100b0c07050405040b09010b041401170717010c1e0507020d03051204082d03180a061b03110910050a03090501050108060405 74
    0xb05009060400829882e6044a52000400d1340c1e42d0343c00380d455145001000030503201401d16140700c08000c20145018000d55210381e901d40c0c4c41c1908140ca0b104d155075003907000d1410300040c03103040c6440810031025600d03a1950981c461104104031443d12089601c41540581443e00380410700c0120032845000e45100c400910420741040140016100a080103a40502642004000c240122002da0712085d072490192b549141c1c3e40e02c0492865a00703e5100c0002d6550340a258500c1c80d0804040e10034030192950040104900200117000380c01440c1d8040d00881440d0007000401d44610704445c1c0c3d10404208003401e506160800c0b03841c40d00900c602d109400c0307880032210f042c8012041c0c0d4040190f400c1000614503551010415811100c4041203a114810f0444940004010303002c2c1c0945240810707140000540314543c001c050303c000c038100800311403007000310309066141c0701e514441041881c144a951401c40b10401c400404010501424030f510744000418401c1d00030520324044c42c010011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 495582347 1250 495581097 495581117
    0x31c080a0f050402100f110109050d11120706150b0d060311011d04020d0b0303040b0d060906150f0210020c07050a0b0a170403120c02061906050a03020409140102070302030406 77
    0x40101e0b0000e55000e580118808031071044d00e07106281000100e05c031440c10f810860f211002d058250741e48003804a03041d812030071500140d6a400b4414000c20004a0014042e4441c070b400c103403109205170840941019262103112640b50040c0040704010040001c02542c0c2c2c0003c0d40c4824001c01080c00300b15000340c44003800c160f0701d6110b1102c0c5000703800d42c0244203e5a2280f01d0803c070083d441100306114498442881c200c1c1d555090015000405400302c5860380d840b1038000203411034000c0e400110f1f007103141c44028400c0c0900e103510040d002080d0308100000740d0300000242d1801c0e00846000035460300018280406100c085514030840d001a141026034540780c42c0700d114540165080500041c5105980c90003100d8001c0400703404c01d00a09100416007180d0303811500756040f0101e190701582c820800e21160310b581c40c40d030200d46180220204002414180060450701052102030300c40d54445000a0034000000d01a07603802801f407008656940b454070340030f0f48a030080e00c141008a01407100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 495583597 1250 495582347 495582371
    0x106180602010b06040605090d02041b0e01020a08030a050411040e010906060e0c090d0c030b0c07051504240f0608010603150b1011010b04060806010819080a0806031c080a 75
    0x603e614102d0003450b807420103040503004c4403160444640141d02600150056000d42c4070341c8104692401388507240404900c80360b001030b0542c00d5211080e4110740c000d51000340410f8206c0c007034039009080180e004c0b44a494500b1300c003481e1007800741e4403a0710074038148031380c4002841507002138130f9203201d400180719650b920000d400d945001280d808181340d004203d040307080c3c6881050381a28a22407031281001d035890351100c10340040104c465031080c000c0040c03c0014000104034030559500301c0305180c00207203001d0356050100d000c0d280d00a4420104114030444000f6a6007291080115090f010403005a80f90306c9503010b031800c1d203c2036a03900350070b0741c2c2555203cbd124013464030001030290165001064070002182c3c1c0c0a40e040026000e035696100c03141042c0d8580c0111402401000002d241c1c0c1d505040000e401c01105016084240ca040304000d80010000001d8030004000ca0400d2f20641c1d80c1c0701c000c01d0031b004078818004404094020384e5004540c0003034615004402d00c200030004166001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 495584847 1250 495583597 495583601
    0x15021513080a230310090c200c19090e030304080f07080f0c0c1e030a060c0512090102120109090302190c050a0608040203060609010e070807020312010618060201 71
    0x96200411114881000c40c04a40114000c0c0149011441c14000c40b440a141101c10240c51400791824a20008103100100b104003880d0005000031840c20000e5503c28400607104809119201121b24000415907042000601550842900240911890700000d242584600c02e90380954004145000104201c00d0400400d40b88169449030801d0324018040c0400c0202d90008030044035840010000e0f040080d02c0e03031001c1c1900340c82410091001c22052001c00c03401032034000034440c0e8003420035a40d441582c2d000a076542c08a8100e100092100c032000e50482d1a889031548070581110200180003001c00158018481c00b42120350b5104542d032645144010384041038409801644a05440b0b0202045e0380c008004e01c601c103d8001c246541c0e00e1011401c880b0b065030041002c12420001c12080d82018840c2d40d500c8441250900040c0d8101030192200e03100c05441042009070800018414600030807c88040061600310480c45680d035900003048070010044101108021490004280c0c0c014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 495586097 1250 495584847 495584851
    0x20903010e060a0f0b01080403030e010617010905010606180b030a090204020c07170c183304060e090a0f0503071b150809190206091008061e01090902030606070606150215 75
    0x5940300750035600c1c8d1380c4088014256141008400303540c0c032400040c048851541050041c941c0300c0c0041a00004c604203a800c48030702d64030810502c80400441e0f003140011395421001d035100c2c204502d4891b01c50201100003001402d600a410038400102080031240000d0768130221203860002c0340c4c03400d5840d540c003038a5109079400c85402409007804550780c0c01880cbc14856002c044c086401710186101c0b0b20407102d104141a9402280c071014801ca025420140540d0340540420002200507050130a68a076030f036aa00038000d020404000101d130308011007803003142d000641160012803070f48841c0070b10341e42d60000c0740709401103545015100501c1c1030055500511800302580648503400c5514000d200c50507600d0360490b0300c25020084580555642040e1248108440da14100985042424046c0055441c16051194a01940302c5c19043e03900201c280f05039204140c0c0546c0360b40f0f0700408541e840c010b600340100303030300c1c105000031a120072040760f0b00510803e60713400c403050102c0908503130076201c0b41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 495587347 1250 495586097 495586099
    0xc060306080d031d060115090e060319031b0b271c05040905180c01140a05070c1d0601030b040204031709030304030c2306031513020903010e060a0f0b 66
    0x4041c000b150708078060b50002c0c140e6403e85015800c070301c04098502e401c2050981203442034200b61801e0047d4290300600d018042c14260500001500301030002075610aa1031004245404e0a00f02010806104110030350900f03082d1045104801010f14200c81044801c4804080a8002169000941080d01e0240745401700e0b0902a0125072078804584100e168482002c0703050040c2000000743c8030b2000c0c45614401e1518000124003110088184c508120540300c80f45e0402210740808403200700c1d500c4c202c51300c1000c681842c2e540c50781c1c2460030004403059036100da0105607881410200790190a042c9070321074503090783c040140100c41c408100403405140000380400d11084059291000444002d00c5040c00040880b41050364941da0301b11880c2c4a07402c000403a0b201400e0000ca0a100421015050742044501ca030452038000c50001080d000712079098454584408141980c0c40140c3c1165040b2002800074001c0b120039000307081e41e607030042d07800841c1c0a24040003003a0182c5548285030000390 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 495588597 1250 495587347 495587353
    0x40f0330090201020102160303021b0d08012d0b0309070f08030904020702060909010f0305120403080f07020427150b060406110102160f03180605040603020d020c190c06030608 77
    0x40141040e801044620001c0b4103665081154059941004480d103c4540c420364001d070380e4a60006650181c2003901d000400e480d4040740d05198502c0c0c01c003582d1419208240485c8031290301590946460070304140390b051544084a2002c1500060324009611031440a81180d41c2c8a42d40d44508204030018480e01c6290740051118180078940340c1c00804010303000506003414034141c400003071640082a88200c4401c502c0350410400c1020902c0000d00015204507030a040c9482d549440c2550300c5480c0d841c919111000541608542e03455203c88800c0d04000d07004011034084080ca00406515064282c5943c4001d40c68591100b005020700f0349480c1c0b003e4612804d0500d000300c1a00e5181440409520702c0d5001d1100d1040c06030510401c0c030b0040d004a070b0182c00c400040c2405008a0040c2034075044440348020305110803900b107000c03103040318110724005a80c0c003c0550315800a000b0140b41002500610103005000d44c041d02c81c0520403030040503240880d80d5148015400c07240c2c40c2c4281c80080d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 495589847 1250 495588597 495588677
    0xf09050f010c020118090501031412030f19050a050603120702060d11071e020f01030b030a0b0709030c0f1a030f010308160602070b040605070c0503040e041109040f03 73
    0x540700c2c1c0440011148181091500362055005000d902405504402c103a81d42d52001001804540c2c0d030746034011011440501480504849203c03090301c0300611500c035046887d404030b03c89607038045e09400012080c090402c22400d14071200400f4150644a182c0300b4494864010300c03c101c40800c03512481c0e40108040d06d424043c1000c00082e00d8103501030140c12400348011004207210100350109098804480c603410300302e0384100600d10802d40e00c000d04152820340001403603100042d84003105604a407a64010b030740c0b8444111004105508001c08050724030a0021f03451107040004000e82c0c00032403d083c640c02d860042c0c0a080d000445011800d442807000400204000c50000d0000c08140e01701024000b045031070b450240c0c3d100c520100c6031041910100424095640b184036040046458142495061900c80c2507507405a80551418048010003140c100400100480388840c000f80000d01c443c50503040c0078043c1c00d02441c05030046058500030380721210310094918000c14507115008415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 495591097 1250 495589847 495589849
    0x10b0f1903061802030f0102040e0a0603020303030703050402060f0a02060f072a051903050a08010b0414190f0326030601200c0a17010b030105130201081506030c0a0f09050f 76
    0xa02440600300c000301c80d00039011000f60b2400d000e8070ba00f0031b42d11400036940e03a180543c09071200a0080c900d0340a585404424401a9004002c807a004500ea1802050315115030000071a03501c60540525810301001465a00107500441c0840c40741100780410324907651117041c01d03100304000f6100222420b803400800a44000120360401c0a04d01440445002c01785c3c803460388406a07901101a0041107000c1500280140e020420074003426040303130000d04ac03c0c50724043d100b0000e03004640c0c9219801d035400980044a54042c1c21000f08548500c8040544d07490034801030700508010b43c00c0040c0d1504c82d041100416060483c1c3c019031041e96030b0161244200d0a0604000e40080d40803d9402030700704402143e03071004d507103070301038030a10040300520036403402c000e401c6804030a5800c2c0240d041ca0100440d5440740402c2c0814580c0a00300009a5034403000e49615480b51201072980c00300d0040705000c1c80c001004040d240a540c075494201080740e8070441900c4440d241c1c800c2c5980080086890480307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 495592347 1250 495591097 495591101
    0x3030702063c03160e0a090c0c0606090c140405011706030102070c08160e160c050a1e12021b1203040b1b2806051308030702010b0f190306 61
    0x258480b180710340c1900340c849468030254a03a00c02c4219000d98003c414000001c0401102a401d84010b040c000d034003035600300c0031800d01102881100c050541e030385900105903001c0c1441c1c0c145554002c200b005529152030817a0010100c100c40000080d141c00d0050480d55541c100302d1702038138016141c5454807402920f11103c219001444207070555001c0c002603002071001209000504582d0010304012a03d40c4010381d00303030305194404c80450703020780288103440c402d92810910f00c0300a80f80c40352400c40e1a0802924000300850000c020440b010741c1e2084405001100070a014070409400040d891003c20490b52101c0c8881405213445250302c4c080e41e5071800c0708003980c50b4044042660b06181e41d0300c40d0b001082c0c03c4080c800c42003e100d0700c184540c0b03400030b01c045001424000d0300a100505041c0c2c5401c507d1410100041c085550340700820300c0c10901024100d00694021071956032490548030090103401645041070080511040c1d140a03450210000c400702180240d40e6100d081c035689076440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 495593597 1250 495592347 495592387
    0x906040f0303291306180c05040b040f03150228020f0111031006021504030513030b0a02070c050103050106020a081303120f020606060a050a0e13061202010306050303070206 76
    0x42c183c3e92003014056515003100030b11840443d14995164481060038012000140c9400c0c109240c0380a100307000d40c42d500c402a102c0001c0040f0002045003081e80180c3d05441160004004498003050000f150398401010303105692003508110f10040d010140b86041e1302601e4a1503900400088240182000e52240304000c21b07003510441c1c018a1050714010702b11010858005500c800000800c070035001d2001c902001859148020640390808648141600d03030041d0001301080750004141c100108071849120285070040700401c0c003820000c4007c0000e500134141102e00c00c0c01c0300c20001d03184d0700034450b190484040380c001d40403c41140e62805169409440500000d80d145240032010902c0c1c03054548050085e41c03220a29203038055006460300c0b1004103010312410702001690021580503041c4c0383c07003000c14200b0703203080701c9000002040c0100c03481e60808018038010300003880400034852400401d0003130701c0411400b074541c820306440c0d03c5810000303034102100b0003d40900d5034601c03003161 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 495594847 1250 495593597 495593603
    0x803040b09040b040f0f020c1605150304030201020d0204240c080313050708070801231b0c0c040507020c120a1e03090801021c060e07020721060207080403030212030906040f 76
    0x200e11094219117011203d006000c20180e55005c502d03910031050800074014055013130008620000d10302000034200312a4817920501d42032001c004101094000d4043d200c0d4001c1910080d034940344c03110868801c40c182008006070700c42c1c581100c1203065003c1d07a151070000c1e400c00e119600e075666544c03103913014124201003181e03540305084001641010a00044020340402070000c21109040303011151000095080c3d0258041c005051140b07246450032500300341c60b206030000d5140c4185c1040c80c1d00b41400006042e8003e4101420000200e174003140044616604942ea810310404405442c0d540301140c80d0001c0c50f65982103150b601207a105050161658424502054070640700c0020ba03007a6048011a072600c0e950312015090512410b01610000c0e00350380d03481c8681860892802542d0f010240701e592480c119500e4039002c03104420600c403507800e400c00c0c3d00355940c02c110320f4265000da100d8030003900140506a10304420b40c6814007280d01035041e4000900d40307070700c56480c0e1415445240b4412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 495596097 1250 495594847 495594851
    0x30c04050319020f0a0f060e1f0f0801061b200d030e090a0203070c032307140c0919050702150a02070210020303071209110d1b0803040b09040b04 64
    0x340030703681044021040c1d80300c8400c2002500c440d02c180240f219007040304500c1600301810030b0100701c6202d40600121105843d203d8502035440c4003048000c1005d00e4a240050040c1d10a02c4c80d45130800c80c420a104416980c04071581c0e03a802c0101c421100c5041002c12200c2181100341c003294280e80b0984110b00c48078403e148501601c0c0001da00c1c07201a900840c04241181c101c0c2c541448e0407000c980d4443d5001c801545180b400b10402450883d0321301000301070040081030118036003e00320364084071303c5010381401e68901c83d5090000303812202044956451280801503095410440e8142e4005c08466100a8110460105000c0a440018202c80451140804c013041403282c111034580100c641c960016134a4030503005010100402017042d1040d03600030010b10a126903c5006e04103410040440055400030501c1c1038064650f0a5800c2c682c007401e80b00b2000103200e41c0044181161015120280e655130f5243d00c900c0e224060303481781c2030385a0014003180600341802c1d000b10710860001080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 495597347 1250 495596097 495596099
    0x1107050d051908090f0319020c06043602040b0d0f0605030a1203140106030c030f0605091302060415080108060114030d121803030608011d0d050702060c071202090106180506030c04 79
    0xc0c4d1703461904020030700928001c88000c411043d64050149201ca860140c98031840c2c5410548040d03078071041c00d04802c8010b40904440f414903005c41d0752907010b80900440540d07813555501c0d40304040360810658240070f20301d00703962017150184510401080f1100680a0401c0725075a40740c614503070325004244414143c491404403000c2d500425403074041c080325100000d03803100048008046a03000795030018000d00d1300c0000d00442e41e030703000c41070340c455026a100c2e08000042e2000c24460300072980a80f5815413502c00c00168140c000300d003141682c800c88226102607a803000311072010081448001e0b0503801440c0c55070155885040c0070100a045081c01155070440b5485082c0e950310741160070380000ba540c04040c84000c2e42809208030b14800362000404d000d00c3e024003175443c0c0441220310000e00c0000034080085449000540c7e050440960549943c01d0340c0707031402c00c020004207004900c249620400450058020005031501078020a41a07064508000030b2040703540c00500f216412010900c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 495598597 1250 495597347 495597373
    0x1090b06010809070f081c02150118020c010f0b090702120f030a0b030a050a06050c04060504090e01090f06050714030c030718090617010f0b09040b07121107050d05190809 75
    0x30585c4001d0101c000100700d100040c04405503801e020210311070843d009a10201040402c01c08514199090b8291401c0060b1240d91804000d1140400d800229400c1c007040c07100e00e900350b51100f52290006e58804503555648a4201d88138141e6004030644103900384620340b041480f00002c2e580c404c1c020400080d41c030078204000382c03629846036001c550740c2e40540603030000c00007035000d015001402c3d48109030174142014400f4085010354060044065510100504100025040524065042041001c1181560412201a1000309c96800210300038400315001924031004580c07060245020060844d241c09104407050105140400e013940256200480d900310a4401c0d84002c080e02d2441c0c9080b01d214051460a50360840d88001149150503400360f80c64035900385041c1c0c0725900c1403007100c071503a030701c80f081d0340306648076841022040c6406034070f0703680c846040018050580540c00322040c00c110310790111a54416035120344114501d80da142c40c4400c1c05441c0c503581100c0080c041d1100500b0402d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 495599847 1250 495598597 495598619
    0x3020306041401080f070503010c0f1101181b0e010f182007110904030906140f070c050f0f2b020622060302070804060509012001061701090b0601080907 67
    0xb0304a0130143e0080c10034820300100c00c1081d080280300c16402400800e0a0701c0d4090100c80034010f0f000103216010048895aa02c01c0d40001c0c1c46442c2c0c070015580f0003400341480400d00b00e41a0724103000d43c402c6040441c04805c440d0900c0d040b92001500b50b0001e03800c0101d00454015450107032981c05440d01d42e500c0c000001503620000358441e0103449900c80e01d840c1070001c025080c2d00d03540c9020341c2ea010709000110b9400282c9a042d80e07440d0804205140300080d0310400d51148009020705c00708041591020020a0114001201c0c8125070384a90810144200800001c40b204100e41c800c100e41510070715200d403900700c203950b00d1015500c0010b013506600420340c1c40d4043d8131640c000c8170628502200321402c0f2890034000e001c02c0c0c07508500705440c03661034110314072581c0510380030300c171000c20a00c1d2241e00c0350203009441c0300124040103050143c54117440c040c01080c041c41c0c0400ba0500510120100148182c0c0d0b00300e9044212a80c0c0364590304015240c0400150001e02a80147c0102089650281d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 495601097 1250 495599847 495599849
    0x612020a091404060f02090a030b0613050f0a052d070816020a120507080f130e070905012d0201140606120a110c1608060f1e07110f010204080c060a090603020306041401 74
    0x190215410f01d0be040ba0810041019170007c8140039071828040c051500318412666900c0911b03444000741c661a024130080c4030741c0340321341c1444130080d4520710280321810140380d039030054507182c982000ba62203412200d4551300c44480e1380401a40301c01c0d813100102c1d04241000284040d5030034094036040c1c29444100e8641c0c0090350034150400b00007488000501c2c9801e03100010b0200440004050600722002084100f8902c21181088101c0540d2111422781480601d44a1020382c009845004180c0b40640a400307400c45a035150a04a0000348060074803008440d452100701c0c0b0f2078002c1d07541b131440e80c0b00148194145518417400501c4080c44212041203058403540107010082251031401655a24001c1e0003811310b124a1210313414050340003400c0d01c1b061968400e4804003600c90351031450440f51010103080c80c5042c1d110b16940c070500080103500603c2a12809011f0b6a40c444489050001d988521070b160000100226800c01c54948264065500420010804034507104100300ca09205102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 495602347 1250 495601097 495601103
    0x110304021e040e010e100c120b0f040207030f0e0619181203090807120f03050c0f06180c091e100305030a05030609100f06120f0612020a091404060f02090a03 69
    0x55903401140c8844100000581c0040e031206c103002d0094070110047c030582c9010300300300c40c1d01d07107071483d1070780a0361602108491404003810454a489913420024244006c0103001c2010842e1501a4240c40c24000d086800c04000070004805000700d4150441c0c0c55825240c035412413811800c000b062585440404d003d91600a031345003002c240c20541450306064039503200610540c022401000000c000280da008015058104035850305c8030768011038180401020134a03420301904041003d0a5901030340402007884682c04c0300d28184200040c491024804ea07180c261005502d550807001001d0f046080d9408407420034180001075507940c42c2407464200102d0a4046203000c001c000745814040450750344407411440d401121031801c2c101c88820354040c080c1c1c201b08107220ad000d840001040d003001c1c1c0b096051b079078201324450742d6050b0b0038180318803000100d00c14041c911000a23500d40314042c6808071081f80c2c02c540e105807500e6461100800303008082046141d02405074030384c3c5030756000083c3c00840c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 495603597 1250 495602347 495602351
    0x1090b03070f080109180602070206161202190c050f030a1514090a120f090b03151504080601050928060602010b03070b0d0e12070f020f04110304021e040e01 69
    0x100801d006480f604050b040b460302285441d00314180204140c5001c0500d98010200690740d10baa030002c94018461415603d50325880c3d41d0042c002c104018505025030a20380d0700f942c04015424034196031071246480050180c800d0040203100381e00d08074020220b2410028121001c1d1211075480660a5181d6550036581c03540d60071440308c42c03090300e89500e5841078580c00030b0145100b8503511032109841840d41c15081010321210184105d0041450740085d201912481e0b4807841c011002c480303003143d00100d2500510604240f045680385240585082d10003010140045a091100340143c001c3c000300694040b02c6580f001c1c90a400d007600919001c410003000102d401c50800c04040e00351402d11840900a074410241045604980002e98007080c07882e040c04514001c031070000303e1800704102c1c3c64800c4050001102020000049550307002a407007941d282852030400010041101c3e80c0888411100c2d80c10070000c0d0040c50701e000c0d05d402c521500d014150142110402184c00c8038040f060304031a5039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 495604847 1250 495603597 495603617
    0x607030506150c15060a17061504110a0f030b04060e06030c060c030915040b03011d0c0406080103080a02071a040306064a07030209090f06090c0901090b0307 69
    0xc00c10000c0c641003400b5500700302e0300e040160807500c0e03075510124030304032019002900401c2d85540e582d1152002403602c000740c101020040840a034540c035054444000ca406460050182402c06010740b000030b04a4260313135800c0c0101c07824182d50f02c0c80100e80400415954050204c81661184102c80c082c02c50303140c0324080380c64010185450044680c0842e403203440240040c20340c0000000480d10050740940b065204c070b01407041c0c000c1250069402c0303003491000120000c160a003101803140280706804c060704120b601e43e907070303a51090300c50780c0150f000080510006001003521074008140d00c5075148106d0300b0f155540c850342c00b00201ca9003920745d40f07000006410028019075001d600050a0450030300e18816071054017008030a6041000700401c60341c040c9040312020b0804840c074900000c54090b480c001c0c80c1401005009503ca00300b481d12036000c020218160004c102d009034800c04c0050010302e40e035101d05502c5540783d005001e0740781c104501c8440c0403c540c2c03c101c010f50300400ca1034031641040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 495606097 1250 495604847 495604849
    0x1a010302040b09150d03020a050a05010e1c0903060203251e020114010510090b0a0e130504050a08090d05031b011407090b0a0504050409150c021516020f0607030506 72
    0x1a425034140148210225000c1c42040710314004d00c072010101c210349070f041492542c6000d0b8281412214040c02c24095003140005100044d0020103c00101d1402c2c0c9a8031406140e000020913007500c141c10014121100600c00a4201c4c0d00450b000301102c580703e500704200c200321044903292140d504000644c9005078814102d00c4003004800000607000074041403102d440b004d00b05403414070600b4071408024845928641c05081010050200f05602d1591070a41150203400c0310104451280280400300082c101b05d1000d00c1154003e40c1c3c02005040359814903150f003600358201000e1141d200f109070f1045000942c041005000c9540300c010703000215503d00301402c0c21140110280b01c424294501007000e140d900c144040280c0d0b01c941c0d080c0f6182e1002090403a164051a08150780041c50701300c104c000d02c03049000180c02510000300c03d100c50001c180c0c040785ca54208410030700543e41140c010645804c1c00074840345914010707104460501c85d4600481b898804285c03034400c003081d07550080c0952 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 495607347 1250 495606097 495606101
    0x80a0f0c030c1418040903051c060501140307120e010b0307031532040f02041a0301060918080715060b040305010b0603010614090d0503132405040b0c03071a01030204 73
    0x1c1c560564200c0d0381804e94240f212901001c0c1c0c02aa1440385655100010425018800760340107062a000064050103a10070240014900f50041902081d220034000030b00d03100d0001117138030405603a6105161074040d030032464068a15207129048554071940c9000c5140c074100154801503003d100c40300c0c0d9006a1425410403134050800300201041400c00c0c2807503402a180d9002c901d41a81201caa10740d07525810700b20000c04032944003e601c81d00700780020141407050070160781c0d808002c030020080c00360380c3c42c11036046a01000003c02c150192446400108054402601a01340a00c480b400b0314403e00c0d00303c07000c9590703a810800c40ba0402103014014070409114840f0a41c1e401c1e1030291030355042810203440c1064600001c00b0040000883c1229501d03103c1402d10744e2a40181201d0300c03000e03a9880039000c101c1e540a03c02c80b015107000b8030104103a401c21900048901c940380e4031f01d0281410300500c01035014540c1030b00f43c0d104c100b1488000402403c2c1c10b4080082005003900e10b541507104202c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 495608597 1250 495607347 495607367
    0xc091a0312040f0803070201050a050703090815040b0601020109022b080307020619020901020c0904140a0b09010b010201060b0a03020c1609090201080a0218060c010b1201020a0207120302030a080a0f0c030c 90
    0x4c075540103000910050b60008100c2c0d8002c182d600384940c50b19044e1404890031b00b00c0d904410790728058000e2210820801e881814000c91040190703921301d03952000120700702e44a8190284d07101d0f2a05a100706040c803a84040c030f043c00b8407203440b1800c080503611100400d91080d2000e0707006900c200108a01064001c8146d03000704046102503150200000000b95a243e01c036003990303c1040c00c44013080411015900d00654110040306881d103c080394144090102d03011140f4590950a201e0740340c0640d84103100725415101320701c5c0540d0800c4a6a2411802074100380c9456905208010902c1d40c134980002c8100c0003003031403860100b02415584001050190042d042c0010f8500502030f000220803510b00c03120424500b500ca01e511140d09c00c40b81800b5219100c1e0994110303105241d40350070080190000e218251007073302190007681e519004984602c44029002c0d005030400e01000d01201d2080390240d07006168203a010601016000c2420100da5091f10075001081d6682d01132400c43d50000d03a101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 495609847 1250 495608597 495608609
    0x60105090103080415110d02061005180c070c030f0b0103060c05090f01030b131a030c03070b070b100312050a120614060702180f09070b070c091a0312040f 68
    0xd0459451940c540c0540d00442c01199890b00c1c0346418000034501c41c3c88440c2074541d0010841d500c1003643c80c00a500c0380f00070740c4d445084500b0104081114100303002c004c01c114094490290b2941d5401c0c0c002000b03070700241011140c2c04400000040424041c03805603070002c0c00381c3c41c900b605503d14980441190800c551200500101380940031981c0d480400a00c40c0f0402820041100f08482e07000800c141800515107403100d01d02040c10b03107010341c00301c1c1821b100041641143e15940da90001c00d0740c0c0c2c0342a4030440c08426400c00040340050b00b80c0c40940c0c4c01211031080d06041076180e5807000f070741c85441c0c2c0004c0d001500110f01030084130303408070100d0310b0f001c2c41d40400c115490a14028940fa0400c0802080c007502001540c0400c64613050209410f00d510185011407a083c00b014500c4243d0b000c0d640035060744a219030200301c01000000700c4e0385007907001212814440c5030204100240805482075030909808607425800c1d0348041c0022030b0b20010348007170345030344504040c10380741c1d0f0302025000380f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 495611097 1250 495609847 495609859
    0x10203092b080601180b0c0f1e0303070507080403060515040f0e030a05251209080105101205010b09040602090a17070905091905070302091e010308031b1209060105 72
    0x30703903803440c2c001d10740c250405002e10741410050030385000755000c0d540540c0950201031000030758030380c540300216402201c42e134078009030b850803105040549090f0111019580c00c6800800124182a0085000380a414030494620303050658a0300c805c021543d0860319450041c424030410038051909104031150300030720300d80c10400c01d132040c15601c3d928025074400e1400e2000c0041c4400c044150005810305019040340b00d05094400c1d403a00b00d03504154414984041a1410303c0842c900303406000d4148a907010140001301b5628292800b0210851000196201d5585055410b441e441d01146144101e0107001e000d42e5680c49581881001140741d805200a008080691100100c010503e5011500806400301d81ca0f1a06020b42e0b0400e040c56003060161111440031601f044030124540c03044078021a0440060341d20242c210145490704504184000f00040050000a5051010390b801000c7c072014141020303da1000c03500994000d840d424902180070b030422807501820060a0301501c3c050700c10b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 495612347 1250 495611097 495611173
    0x6060c101a0f19030201050f07020a0b12010614073e090c0c030d02030402040b03060925061e18030804030c1208121e0c0d0506010203090307030f060e01020309 70
    0x4190f07a0b800b0a404001e041040008500c121100114283d41985400810500240383e40380d010420950000c02210340040c03108000281150141c840c0700c03a00360b0f00f0b4041038034240403656060369107008000c11780c800d40c4c103429201a42242014211800c07051481c5001100390b011001c102e680d080041c0b4208500d030041140c41107008005c025502088102000983c0700d4945100050280c0310104400c2c0c0c15100f0641005140301c1c0010b0300c5c114142e400700301c100011481c3e0035030801c002000e004010100d00c0c2c00b0520710048a181c091400030310074600d042460310201004075040320b01c46034001e44812001140c20b000744040104050300038800300c094221019200d039111540c5001c0c80c0e42c17060040700e4900c00a80c105d03200306040110201103081d04089860400010701c0c40b0b8000c801c64502c0e42d483e02000a0300d650001080b94a00340c0020300412007a4550b58030702804a807034002c200c0f0103030307120709844403103e200f400914000d507003a1010f8061a8244014072450b403071416841c011050040d45 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 495613597 1250 495612347 495612379
    0x515060a0215180a03050a09050d0b010b070c08120a121812121b020c011110020903100f0603021e09010b16120305010f0f080606060c101a0f 62
    0x241070342c001d200600c1450140e82c1c1e0f00d6a0a1268000761111401c1c81c051404481c0400d0703400401488640c8007a10f90800305900d60003400f40f20252264002c1c0701d064410018047d2180d5038000e04800d074070541e015024a03444648440c1004000741040d0303c51a030100d1039001d0b0350b40040400c1400d52441904008502c400610318260a070511406001000a004420140c522681e206409a04469002d1002c011283d04020801d440c030390f01d03040140100d0030800c0166101d65082d81c95181a0740c010001018600b141d44000e52102e041d01d81d1520031a000401d08a12030700030040800340134400062854590300600c00000801d02c0f072004400003c80c0c941521785c1c1d4003021107040d1020041038170703200d060488060021030070422018100f4010a45805881c543c540c201da8103a480640702c008400d1380d1003c101e80004518041d00401e608100c0c00111242040005010003d11800458000041c0314040d1011a01c1c02080c040820301070210401441c00e000c001d034903090000740c42084149402d12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 495614847 1250 495613597 495613603
    0x3030306011412010b040f0617040201030b27040302070f080a0b04170c10060504020c0a110a0b0403050714010e030d120608010f06090e0a0f03050703030f0507030515060a02 76
    0x80815040c80b15148521042e8140c240c1030381c0b00e000d0b646050b44400e58407108401407a80082c0314944545c41d4038070000c00c00c40e1141c070340c011001c04050364044040d00d55500650241c4800755107a9003008007003d088202c0c40c001c1502c649018814032094072503061a040c02828448160045545440c1d54841046115000198584c4041d00018440c00d1501c0310315100e03c82a054018694441c9404070301841404404544504c00030b0620804000c62a91070003880142d000340b0081c4100303900080c07820780205a840d0341c01c50700340e44020424003200d6103070a04000c894210f40c000b034a542c4d100c680d0501241204c925608040c1d402420098144118400020f81e180306074042401000007011081c0b5170190f282c0c001c0f60103800010001c0c13003003401111f410700c002c191520038a602107080402c180018030340403402054043d0480c52035464031003152020b440a510425049040503a1824404070750b0419105a80c024581640c0105490400a0039500d141c0000d41040348187c40401519001302d17000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 495616097 1250 495614847 495614851
    0x2a080c160b041a0c0a18050603041a012306090d050a03020d1103270301150b210c07200303131e0b1603030209060a080f0c090108060d0807052b030506030303 69
    0x10b180aa103a1b2103c0c105240d0754600903888141c1000e0007005020030011088e10590140c1c42105008085a07030700e40300016891800413451906515200d24910718ec144030303004081c02d500c0a010194044e01a82e82c0f01d103050703000c02081e00180c00085c2c00a00050303000036282460f81d2240d00442c200840c089000c03020004807103444904640807504401c090302d003034004001c260310410b40c0060060b660090404548d0100034604800c4041c104c440403c401d080b0000c500854003803800d142029126600c06100040780c0061071100030b10810305028541d130800c002e10f040030484500b150403524080446000f000b40205000880340307070003028840d01d9110750540341101041400c4d580010b407a41026402440f401c2a4590002c40000d24900f0343e03908048480d0140549035401a01e5550b540c810110314002c0544880c0003c1885011480c186024552807048030300404419140611680d1028a400e4982618140d042144079000b078003140080015100c60141e07040504c8189040800a5128400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 495617347 1250 495616097 495616117
    0x3061906050d091a041b06050301081e0307080403050705120606010c11010e06131e1d0c09130902120102040f0513140c030a2a080c160b041a0c 63
    0xb0f02d0300c0840501000100100040341c00b11100c8000d41800e003010641c0d408200380600301c41701c1c05000012014032076802c59040300c0c011400b0303155407810810240e400112000481c003103440305001c03d03404030350030000030030045104200504c4d50a00d01801d00c40000f400d0f80040760070787c0143e000c004075660003d07404848c41e58401c54010740c1c0304500005843c15880052415009200401c4151a04c0d840e0807205081d81c203400c140400020150540055506c07407400740014428070522000c0d250701e0306a181c01d40040031080c1032818030100c0e0b0701190000c401c252024600c1502d890f04c480275401c0c0481002103802808001758945400c16070070200c410382c01d2107014001c802c100c0c5203003214400d03a0700c103103103040c0b026a201046041107443c0071a542c00070780311441039515101d0300e009440d1011070400581c2c5100c020b010071454a40c0800d55150000408020404008000ca00e0348800542d00460400b481141403d130b1904041c113020403403601c40c03142025035241d0102800403034a403034802e813800a18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 495618597 1250 495617347 495617351
    0x901060c0f1b180605120708070b09010c170d0b0103020f0a120207140a050610230a0f0603060914010e01030b040c21050f010c050f0c071a03061906050d 67
    0x8a0740304403602d0079100368040141c920540e00750345441c19481d04900100d034000c840c070b440603e20341c0c4181e5855040e5849178103195848000100300c8080c0b1500a440303048014140a10f14807031031b131111081082d4080805a821500140250540c5103034801c0c200526401c2c80e04604004414500d003d1500c14280008284078400a015195901d982c0446200d282e02451003200740011210007a590b5004400c12200c5000f1f0782e00185080c0b8450f2000c2040700c108482e00c0b000d6402000c00080c9c902d0365004026040120b0500205262041001d0f401c02000d00350340004146203402124021100e4081100c1c10303c14090004000c4d0080f4855403e0640350800d0700404113884074540651907030110b40c4002c1e120310040c110082c60244800744c1c02c07110750040003510301034501c1a40c41c500300c600071043c0d640414000d005420645a4080141100000002c1102c00741515103840304240300e0078019007400907800000300180750170001d01d8900015034161003408007504044002c2c00e940546100840a66 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 495619847 1250 495618597 495618623
    0x30c1b120a05161703061003050c0301050f0105090d03050c0c010309021509130e010b0103050708100e07022404030e0d0c0306020d02071a1501020703110d03090e090c0901060c0f 78
    0xd006680b403c4042a0b2007407911880c8100d618840090ba001261854400d9103001400f000c020300034011180b152484002c864596804c110410403038000003050581045424010013200340c54040d1407511850003625181e48076041103119900d801a2044201c3c10135042030703070302d8006071540486840c0c2106c1c240500c90300c0307840382e002140004601c0006050b03c00c1c10030917543e0740440c042d400409984030030f0342d0510140d40c0f6014155241002540c0c00480740c0c1520707408001521040410b41e030400c81070f10644070703400d610304d020018414148581e0b071120f81200040c00101a00182c054054443c01d40d9061064840c50303c03403040c80d803064031000e413131541c002490108075100707981200c016a07440340d02002800210080c4071308030882101c42039450190103034002d40030340c00010000212940008010068603228003071104d03492180d00110184007000d0000b20f41025040d001c6441150183e004000f944980c40c100120101c042c0c0c04001400b0a181c0e041e000b149100f0001c001140c0c00451281c028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 495621097 1250 495619847 495619867
    0xc010908041404050a02091e12031b0c030d080c090f060f03040b0606090a14040e12030901050703020a09060f0c0516032108040224030c1b120a05 64
    0x161080100003405800001804501c0000c040c1440075042c0c2d00356001c0000341c0d51818a84200e21680780c0d01640320711b51951150b0f04e00c0252400c040300c04006811181104001181c540c40c6402802ea1501c20b42403415050038182400c0184008440040700100b101944000002d00b04034406040846100c1000400052944030701921030000d55014100e503507110030a02c80001940c00a40b81203030755803070000206210340b0303259081e100c0d1158000d0400300b5441c5400c070542c1c40030b0845c0303ca5540064950700c9030000780d0024043c1c000c0f907900c0c0e501906e50300d1601c07120042c00c55400411207000d252041c026a0300e825444500c06007600c9040c20705c42000c00141106070b03502440300400030424442d103885100f041942071600400c42c0e118503000401060405000c0341c40f0560300c085034002800c0e910006015103400301d4500340d08501d2249000c490626a2681003407980101d5a00c140c0e8040000c06a81c01c0d686010175071204803134003015000b0141a03101c82407040c4034040060042003000318151b0340c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 495622347 1250 495621097 495621101
    0x705040509010608060907030b010e0f010909061202090a05240103020d0507020709140c0d0902121b010e031b0402031e090708210d0c052205040b0102030702090c0c01 73
    0xa0003000300050740350740c0c1d1101c0082030903200700da10780d00071242803000c201130601030300030381409082c16101e50820b054010148a40c001c1c02001c018100700400c40005441035130f03841034102034481d00020910300e03030140c0188005aa4040c0841c0541c030f180008208084c444603541030b00e00c41000a084500754070080040380640a4440d02241c2c540c034007002d000c1c45903000036000013140c1c9070220031f000c9803070a41d400840b0f0b094100c0307100c0c049203010088410300ca5801d03480b40000500c001d041048031060500000d01d0800e05250304040ca826100c1102c0e040d42c0c22440380b00f072902c01140240404a1000118405800b2201c040c901540d004008070340a10749416808900003000e800c200340c0e80c40d03c0c001042d80c9059520514501340a07800b400f2140d8808584603134540c0058130421403401203254031140091074001c41000410000344038540c001500c025895908003901420300e014503041c41c00304000c46600c2000541075500411180d0300503221880859440885200e05640314201104505c1c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 495623597 1250 495622347 495622349
    0xa15030b01090218060d0e0c04021305060d0216030e180603150606161b0b0a0917070510030b03010e1c0c11151201050d0812041a1501030b060f03010608070504 70
    0x1501010125501c1c400411541c44409542940408c8405e000f1903501400100d2003144040880110019828006810a20000c00710b28050079001484c094804200c59400d99030791130200e000406209050395146000503a110507110201d90294041c205200041e0707a074614500480080b1240d6000104075a8907502a68000203001d0301400c040c10080c94909980d104811408141c0c416012010410302c00d254195960b070122901e86001e12810180c1000c2c0408590a80035190321070100c0104241d03d424044d00d0b40e140e0180c40c0403d1021280d401c141c00d4801170318507008079a00c401195031800c00e40d0b9040740341444081c103040303020404034148488a81c1100d28100e4020380443c001000a4020390000e00b6207000940c94405540d032940d00b007100800300184040e09a18003804941074198150165942252141542c00c50b01503e5050081c0031800888003a000110701c24040b101c2c035601070003503e89601d012070340c003031604109040e0082240018041d420403c02c0e01000142e0080c01107080320 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 495624847 1250 495623597 495623599
    0x509011e031b0c0201082d090f01020f0304060f1a04020904060b0309031902150a0c031401030323031e090a1407060e01020d120b0a031502030a15030b01090218 70
    0x412a6a54602c05002c0341c0f000c480481c0000e850000045a40c50240e00f914102c104941070041072149440480801d5440600040c40d2406800c2100841c4d41091000702444c42000103070f980c903881c050408100720b5058400d0f00110b6170134091415100006150840f0200ca0100c40050f01d900014000c10000c1905400034801c0f0b48000091026040001002e0101180201c410855140700340030220384440349000514041e5107454003060742c1308003a4204c8013a17883c49243c0001d4801210780c0c1d07200b62410a81c4203401089481d2807440d0610103420f0203900320208031400c83d1071410120a00f507200910001a01d94101503440481c8a0103c1440390103099070300080585100681c08100d00d4035010103110304404140c801c004000994000310f4003503021412910b0b10320301d1030f1050001902502c45a4841a448543c3c1034001c0300080400d60800c500048100b001a124030b0120341c0001140c2c0402030101203105120010400030b4004c0020311b0550b5002c020143c2c84a269668496810a05c00710032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 495626097 1250 495624847 495624881
    0x1305060d0f0501030b0a1b020d03020d0902100c0b0c0f1803011401091a040527071d0a180804140103230f180304030f050a0c080708010c0509011e03 65
    0x10a11000e05c0056018100311441007241072140112402c043c00907641d03140140e0031540c0420701c1306002c0d601a100400d074599000c50440500d60002e09240807044918022400c9071140c9030903c2604404c0076030110301c3e414224a80490340c03000716024092070003c0c0d0040310aa82080e012034400390003a007400c14598524080d00d503103030600b40c0044c140c0c1d03880030710740142000c0300500c1c0c500d01402214090741c04600b40c20b50f02c21560700081c0b0f0728000609099210b2241038800209003503084041c502c01c40c00311844050504240306002e050390f10941201e20301410700700400011403207003001c0303504844ad14000b04204144141c0184c0140281102c070150790b644031300620050780525280d0912498070040d8590155540341310b41c00c07680c1e07a20030303584401d580b00384000e00000d90b00040001310309028400700c41070401259600c03140c0c0489030f007160b151908842000c1140180c01d0242604028072401c029023081401d074002001743c1a1001071220b144030083e0204099030090340300001ca07002c0e08480c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 495627347 1250 495626097 495626099
    0x7230d021e0336031c120b100528050909180a11030d0c08030a0e030408120c07061b120320130e0108060f1e0106170c1305060d0f0501 59
    0x580c205005000700400c0c00d80071000c5152604d4003290001c0490307161845489503080ca0402110220354508a1548940e6902900142d5030703203580991400814942e12240c0c0e80c070785a40b00d411503600390880012500c20008150001d26000700c01d42d200c2101c2078070002c90317a980c1c520800c8500c214103026500c1500600d030045040c40640703100303054244015811101c2420702d8030800c40d00d08038440030240101b001800852041149600000341c1e002c0c40c0421a410140c44003989130901da0601c0890640000c002107040b0201401c1c00002c0041840f410b00c80c0c60640580f0401c09541140c0ca0014400e40385680040f010310301075446000382803611070080340d415000a6061b409940920070301003c0e62800c020014003000c02103205410780710844040c00c0151580300048030031040290894074180c24202c00b0034040c945442d01e0030f0080c0b001d503580310801d00f40003001041c0450054030131030fa411800c00001011032104644003048078800c0e56415a5010f641794800014016041d121514030b06040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 495628597 1250 495627347 495627397
    0x3090c09060821090120030c030301090b0406060503040302030313020a03290a020a1d0303160b0709052b14010603050318030a021005030c040b07230d021e03 69
    0x20f001c0888001c030981c1e50124a0400389003c0d018040d844609001690100b2581842c0c0c003810325640140c58450212030502c00d000c0030711800c680003600103178001e42c1c0c0c0300c3c0c2c0d84000c2e14081c09070800070a101c1c1401480c501305520b0082d1203100040200b00d1a0708090168000c5484401600c00199007181c0105c80c085500000591810741911a000e158074401012840d4406039100f1207140140300d84a5210741034181d03040c0c80702002e01d414881d9060000f80529010011840c5056440c01e2145942d0401440c00340c0380a058102c0035007045001e00704000c000c8507400301d65078100c4641d252000b07410521910703c0c5407025036000400c5030390901c3c0d405c05c9000802c010000024208003140030b6031000d4a0113507181410342d10401c83c10040d40c00000d1003007d0140d5806007005580003244022158903181c0c45070300380302680e0301104040390741f1440c4642c2945d08480c0b4039041c40d800e0344440e000d400002a412130007584ea250100380d4008510141c10100d0010204008494050841c110401d42455a0003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 495629847 1250 495628597 495628603
    0xd500a1d0a031e11090108071a0d09120909020f0d09060b1c0201090b030603030f0c2407080f060321090a060305090f03071208070c061a041d0601030303090c090608 72
    0xf0004a880b100050000065803030a0610135059611240041102a280c01515100c1000e00f081c000c064140401019003064038a009002d0a1401040031079545420702c0c000401e0006107601c40070441d07205000b04000c03210220210380800000c0000444c0c1d503009418004024528481103650044905031000205115800c1c100300b164006d0303c0300c00300250381c0c484c0d1074582e100c112149541500200a00c0700380c40f4942c0c01901001c2142011540402c0d400071003011241d4003140e07031000062410082284082d4028841544180e048800d107100381095804aa5114000380c8170f061000305d5501d105074540141001e50701d80500c003c0460170f91680e103d402400520055071640554001d0403a4010240c60000403900c16a42c440c42e01c0045140304402242c086001034240b2041081c0703114501c02080c3d10340100080003107078810114441c01d8a030304000480b04044030300ba0102c1c9215000040d0200e011a4043c1100c0e00340c1004901c002040c601022400d03116084680154500000803034102800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 495631097 1250 495629847 495629903
    0xe030f1b120105041106030403021905060109050903070507030311030f030a0605090912070209062805010e040903020307120c120905040c030204080d500a1d0a03 71
    0x3030301c0412409a29101480c260b0750111406011038805110001c46800c0150040d80c0c070500900c1514000764580e010074003080c0f0b00043c05d0713800d54004001401441e045200d282d4001c4032481c010340c60b01c022039481684440d00c612002e000c0c041800c54190805000b803049420300264840c03015568680440300748028840c43c000d042c000c05003d400a00192400607800e82240c0c100340b11541421419400c01c000d4201c000c1400313804c2a44d202030781c582c3d00080c842e8003604a102da8600c007542c5040100060440303a400101074401c0d4105105140403039004022070384007542048030802102c020100586404160160040004410358803403444640d002c0020010382d54110b03800d001c6903000d0141202640070b06e0250a416820603002d1081180c0113400c0754060009072100010090404440c903006a48500b5a00c00c045000002000000001c3c20b07840ca80c080010b0b54583c01c1182008000b4845121301c50303c0005004840c11800c0541c0d00c113504d260085a201d03030382002000c002c020200b083d084d9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 495632347 1250 495631097 495631099
    0x7050a0b01090519050c0405090403020f011a01050706050a060314070905071d0907111c02101b0f030b090a022104030f0302091f0c0308010801021303030e030f1b 71
    0xd0300004a03409206004103409140d0b242040c141030402868a1002001d01078550b0343d0480d0204000201600c0f211901803069009801502030b0b08034020825007501c2145241600c031001c041d00030f10b00c83e0781081c01d0303905094000d60001100c0c2d49001c80706005219030b42014100341c2c10601c0c2005000340015001c82943e109070014411520340313503030039600005440c8070401407900c00c2440205a0811010003a0b0200007480d05c0814243e003235640c141842c842c6400d001110754009039843d142501007181c42d544400c00c074030070030201011003082500713101440d0700207040101c0d8001314030b42c90b84a41c101c5036800c170000b007d111260611120260007580010110103031000948400300200907101c8941d4800c68264403040d0003500c60303000843c0258440080e61307a01151080203048000e50925190400720a140c480b001d01e00318504001e000c0410590040f003240e8010800c4500d040c14101d800f0049a605003841007850f0b082d04002030034943e482000d00680d206021005800104440d0380110641c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 495633597 1250 495632347 495632363
    0x1501141e0c011d0d0e01080402010e0d2607080702041508010c020601053111042c090a0f03142101090f06230a05060c0303100f060e041d0307050a 64
    0x22006441130307107500b0b0302003101c0f001c954914100303006035001e09a000c3e4014070515010280b1505040051445c040000e01a5000780b1030200011a00c406001c0a0b204809101e0030346050403201d07a2100418840d04d48001c2c000d503225030391081c964803400c000700c000d400300c3c1c0d0081c8144150320000030758070f88003445064898140800b220003001021a641000080304401116074028040500c3e00681125421240110410080045c2d04205044103040c04500301003160038040304400c6104e1452405421684144c01c1207050300c0024210a03181000d2681c103060000212640320151401401254020120316200c000d0418224203e80300090607101100c0c4100043e102d0344610008480b042c2c0548240c03401c001e0040b00c4081004820300100303040c001c10b18034041d03441c0e401140d4107070402a1401500d0740044140003079a403455504001401c0140122001c0c245801c0000b8a600c0220b07100317074061607075100700070600114214207410500c1c9800c1200d60b1007499151555503040e000c001139440c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 495634847 1250 495633597 495633641
    0x3030219020f01150302090a0c0e0303040b0909010504060e1305030904050f040b0703060825031704090e0a0201120c030603060e0708061e0105130f060314061501141e0c01 75
    0x240c2c51030401c040c2c9401402c1030005550b408423100091440c1c0301e80f41c0c24001d00500c030180681c1c0800080c0003800400c1c45c956114001ea405000352040e0682101d80b0540c00c2000c24130110001c02d5905501c844644240003030710342281012030652060b00c07030041c3c100b0304040400004202c41c840c02c03400342d849910800a1607407010f1040f03084034410300412003681c00c10101f21900300e0041b041124448800c10306550510340d070b9032b6001c1031307240f07400160154080085002c203d40130b80392048043c0b606118010301000c0101d80d000800000a010035802c0b1a65a07003495184548a1f500540107583e2085041200140015411741c0c0c8881d5889a400d0500c1340c0350008203120101040e41b415250248034102c0aa401e0004101840d20654a00c4032510b030341e41004002c03407440d0f001e1800103602a070030707100074602c144440c1410320000a08690403903900400d071039540d03648609e442c20702c04002a1250b03125414030311a09010010b40e6411a56980c02240c1640d1185040d40304842a0811840065482d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 495636097 1250 495634847 495634871
    0x2042a0e06030714090301090605061302040308030106120b040c050d0c0315120314120412020a032c030a11010807020708030720040911120c09011203030219020f01 72
    0x10a200344581d04031000b07001040e91140504000e070f03032406454403024249164071012138210f031a030360801d0b00c14540303c5003840f1040c20104104500494121310079031500c0e00b95103e0340e613a84010f11880c820088802c910400c440301c0f0703900056012074014800c1c060800000401003a5800030503065000e240781c8580740100701d01a206040821b41d0403401d110b25a440c1c944c0c7c600d6440e084034410b03018003c2e00c01d104500c0d283c00d90300a202c00708011084584a080c01e00303024400480d031801c81e6066501120308140480d4000301032416a400d41420600710681c40481c20840c40c0309082d000f60188038075956141000440f24644141488c01c0e6590912035542e00000ca0703648010380300340080342e0800c10030040800c0e582504e5019244602c000010905000d4000c10116009102c040c2d03100ca004014480203440d05616102000380b107280100300c8004d10b00300240c540e110610400000c2034821540500b0140a6019102562032416101e41c1c07810301a0f0010307458504440c5142015480c1110030305107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 495637347 1250 495636097 495636107
    0x605010e0a0204031104090305071406160503070e21070602060604050907060c060c030b090114151309150306021b06010b041202011116091e05070e0d080702042a 71
    0x1240c0d000b065030721400c0103845c144030051100f00c40030f07010000704000c25008a0b1002e2100c4c00d00104040c0101303900c5c80c10050100002440d480301c407007004010414803000c0d5901042d030805101c0c04580c4001c6100801400c1c003d00c0c80301c0c440c5001503000701c240006107250007258081c402c07901910144855a40c1080c2152605600d003d01000f01d00d24440c01c04c04686c840c0e00c0010784001908000861030915030001c1d144540c02da106c081c1903040100200d95505104400150480805181c4e0741802c800540a00d030030354840c0140e80c5007540e030f4400049807070051100b4100645c1c00c140115070f545002e118600360a66170701100740240c414080002400d01202c801c0700c0440380e00f0040074040c04180c0d401190809600d54054070184a99060701a40b50b000703842181c02460540b000046c0105010323002c006580c00408081c40280c603040030401142d400c00c1c00003c80e480c04440d80c08582001d4900325099001e2043e001e03400038038080401d01001d00d103c200342e848805010041c00f40000b440c0007120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 495638597 1250 495637347 495637349
    0x130b0f041b032f030a1e0e0f0a0b1603150602030403050f06040f031b05061815090a0204200a021b03030703090302060307050403050312180f060c09010306080a0605010e0a0204 77
    0x1002000e03d12030030420b00c908001558101090302c0c00030032510b0518070300d5441100d14804500f4801d60302c80501c0c0388440104541f444107000312016101780c10340380e00e0b0302e5004d41008107800d05100e010940300d03415520a900804910b01c0740891340381c0780740d1101d50081d1750b90020b00040b00c151190364460350b4000c600250103032107240c0c84500002c69012a540c2100d00e209081c868a242d0041c0c6442800050341c240a994400c1e0079458039034003100044113800e464140d00e83c1c41c0c002c0d00f29103402803150040c000708441d0071007034040c3d40120300c040c0020113140d5007070311103039864400f0742d40131458204869011503d10380c0500d8545000d00b01a40a5040540740d00c20540000c010451000d030400050038420702456200b4100c7c00c060f07060540e04e031141403c550040c82086032004107042080107801804198040910700000100a03c229034100e0b40d40e00c41c4090401e1448800200d0310380b0b0036a1003608400d01030981c84040d110201075900d050401b4000038011149100d000306d00068001401d0301c2517030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 495639847 1250 495638597 495638651
    0x111b1504030b1f0f0506090103020409180c0909020f0d031704050705211e160b090405070f0f300903080f060d021302130b0a170402130b0f041b03 64
    0x142d078207841c140130090710703031f2005402505243d000c0c4070004002c0310302e100702403d11250a0280780050524540b001800120750400704981c0d1500c0c9041000d0b8072000004c0024901c01c2d81c0d200d40304401807e0548211240d00300840304945d50300c003003108128002c6002411038405071200c407924500c6480e4040007620030b00e0301e0b00e5660f0158000d80b00701c2c18450900c41d40317076540702e080c4e03000318441c5030f40d402240010f508003001d840d400180001160030316107c1d031940401036180c403100c01d12030854010803a0b010038ec1e519003003050042c5014204c2800c804080e0003c10b1020080510100504c408030140001c0103080e4046844400060601c5144078907c611a40e80141400d03803a1110346d0811440c400350941e1410529400d002c0940e644205102d80000760030280c0da05a101c0e244002c0060080043d9126103218070950300c18000180c641882c440c1c0c000d845035401044940350b000c0492a020800941c2a5100307080080091030950000d00e46a10061150f40a00240c081c0390b0500c0025000d1001d06 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 495641097 1250 495639847 495639869
    0x10b04080d0e090c070c030813081e070302061b06070f110a0203061f0e0103060e101802060f090d080a1b26130b19111b1504030b1f 58
    0x444d100d58074802460340510031703c1409043d0380c032500c0348102ea411200740581090200c800c11300806604010070542403c690788aa1110030740260015128074039071000a000d80000b1401601c00d00c03c143c15251456440310880311145080c21009024010710700304200480d5481c003101c1070801020030740038142e9402400400b01074862084624044900345517424140e680218042500c6000c144041e00030b5000d688041000120002d0003411310840500010200f4038012114650104c900130740c0c0b036556012100992601c45106540ba80d51003002c4855070f000109680d64070400c80b420014001d5501c059035000404030208000ca640c500d0b000310040c1030000c1800100a48100c0c051034032100b490b45000d56401c0c21006088e48506507030030340101110043c04960401004408004550205070528003002101c002c00151600c1e02440c0e4500d540c500c100750b405607026110002d0900704186109038080e601e0303a407424090b12800041c0e40b801c012a0798041e002c005100140c24040984a01c5014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 495642347 1250 495641097 495641101
    0x6080d02070b0306040b090c030115110d0f03231b04120f0f1407081c0c060b03070521012012090a1406160311040614070b010b04080d0e09 61
    0x542c540004002e140d226032070310b0070802140c4402d998076001d280e0048040e0b4803941495541d042143c1c40900c07843c1040b00d143c4840510003030010703440320450b000b81009084a001d5441c2200605542c01d00d04840d94030300c03c14001c0544640940038421881148240404a41c400c00d0000c2c40c85144180540390701c03002207210209580c0800c00d18601c0c810700109281c8070043e582d03c421408540c040714000e401c400400c121003070090000d00e00c141c1d10114040010001070700064103050074144041c00141c1e032604598400c0e102000002c010f45801024894000c04074814401555031503160483d1a50801010030041c40803d201a09502071081c003907070610142142148040000402030b400a100381c0d0f405d200800c0e1082d11902449585038043d0a8515041d0968000803005016003000c041c6400562042c0718254429182500e000d498005100c142c0c0b414080c1070360044000140c0350520310f0000040d4081035100030b004640522041c0d60910032000002d4030501c4c5000f44071a080514440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 495643597 1250 495642347 495642359
    0x140415050d0311030d0905030a0806101b110a0b0408120403030503040b0a090b040b01031202120d0f0608100b0a06030e07260d0807020f010e03090105030702120d0207030306080d0207 80
    0xc00900d80c0d440640844e8200b0400c4003134001500c48604041c1c41c190000100303051450761202d0119841501502c42024650301c5100003420044101720702c2854080084580040041c00d100b807410f200da00038941d01446454215440460b0711502c03d039825807181c2c41956224a81000540b801c40303030503486290071a92a52150214a2002011034194a503100d000f60700184c1800c6016006078082e140f20855581917203480f40400c440c0d6600d000c107640c81104561111110001140d6043c8403070a408103180d6070f0800c450024007001d1708405d10900036107400f0850700301c0e03070b6000764480d80080311f695204c40c0e42c031070781a0308403016407440c600541c2010100b07204030340d03680080902d1342138104540b8401c000541071444c201142c190a241c0000c02c62400d00211560400206071312100f000c001304040d0301500d0442d07a683c8248600d0398103200002c0000f0325454001e22030a0390314440e00c005941d46448000e01d2000940c080d403c1280404d1401c0c001040704c4c3d00024000d880600246c00034212181021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 495644847 1250 495643597 495643607
    0xf140106030b0109030f080403020a05012c1909020c07050616061109040f0c030518030316090b040e0703110702010206041b0f08060103350c03040f140415050d03 71
    0x2006043c140810410000002000780a4084842e0b00625005807103905610400035517000d15408181007010303402d103001403801000d0080e40c00303209914900c0030100c14400880c03401c07410f083c1c0040c0703000c40c244000140020150020700b541c1880d1300a80d05442d03250300c20051240580369410b008968031013000390002e441540000300c501040c0c0d05072410808075000003010baa030140802c8252a445604103644190103008072500300c11400c2c2d601e03c2400b51400c60580d6800010050503001c602014060701c404d0080d49000090803ca01c820360751151543d455180d00842603502800080c54003a50039516071740314064400c403543c168007500311602e81c4e0702c802010000e80740c00c0b4130b66441640000144d40400c0b4502c24004c0c00031002900140d859800c2c842d450742d60b0820045d0070004142c10f10165203600c0042c880336000307070102c119100d10744030300721506c2c40c062a041002e18618040001c00c1c0403461b140a00c030108000c940603c480f0381160041e0b1240015071161580100a031540003000034011713 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 495646097 1250 495644847 495644861
    0x11070e0702010b060301120203010c1d1905120d0207060e010906120e0706120f02090907110118061e090804060f0512151c0818190605030105040f14010603 68
    0x41c800400c3c0080d040d800038843e54001e900a0b40b120f400c0d2506001181000e000b65107043d0b1650030941d0320485559401714201d60710f4401a0f100d520381d01c54014a40c820400404060308001d0455a8001040c25400fa5200d007101e40110140c46050800110144174403040d031000a01a034031036140a16000e0306a8118038407045c0c240240b603c60342c200c0c3d5240820400d800080c2115601c51141038444c1d0307038507400c840c3d05624a8400d00d0041101c0c44c0141c96a00c100754110200d03150415401d80b40d0f030b202c68010004c05600c1c080c10584801c4180c20320410b03030004000114800c450002034940c120001084400c070707140c01001700b01d040c07004104003400b90b200d0350f0a003169030404a103050300000c85400b040004540102200440140c19483e03401d00c0b148405040e020140c5140c00b1200365290f501990043c0d032000c4c000005d8134100001151600400901811000c0c01801c103036517101d1401178960b820034007030f0601461404850300c1c440e4006000300a00742c41e4000811020740d081400c224080d000b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 495647347 1250 495646097 495646111
    0xf0a18050d1812030219062d0b0d02030a0201080c070c080607030b061303022701151107030c0e040201030207060f0605030f010b0f0904020d0b0a0204060e010504061b14150f060111070e 81
    0x540d02074400d4a4107221091246461142c010408588101f103018040312100b0004502038052b08034001f005890000f4802d1510f502400d01100694402803000386a2190500040500c0c00007000000ca1100004619006840c282c4003800340e20390010602c2400d015124400804c1c0344000b40c10000b5003481610b0807401900345010b01500713800c039401e80200e0b80c0b0a9001944541100040071402580003070303000a1030846501500341c003441c503120194080c5107402050b0700210303080045021603001c0d0341102c40c4140d0140301807051000742c0d0072641c024002171090502a001e50920341e40d220300103105010700740400400311404021240b083c080591402401240c0200721800c0d4400800e8190180c01d10514401c940560307140d050a1f0024072803100140e186040c0b000c117000502c0325623007148810403403050034070b0903408180290a00584021456004100f40c0c014204002380905140c11700034807030300071400704100940b947e800448010301c24000f00046074012000900884014040b16500410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 495648597 1250 495647347 495647351
    0x6180b0d060b28030c051c03050a09120303050708180a200307121703010b160203070f0f050a0b09090c030702010b100c0210080f0a18050d181203021906 67
    0x3080f501e0002d1009075070b0808407800c18044400c00400c0520010200941000e940d61070300d80310315405e030a103486403402d4000c050080200c4c2c46041e580c0301d800c0c060700410a60041d00c6054080d0300780076000309800d0319000001600c6000141c482c44904505c103940d02101c2c8014194011103880c1d05011074a00402d0b41d20905a20b00120700c582d50400c400b00c00f4020f250850070740141c59140c40c130361249190106820700395080c07004204c2c9000c0b1a06889061f400c5080c0004120b00902c0000e003890301d5038000e041e00c6101c00e40f01003106a58021210256030040c1c5200e10b08503110000c0c0780d0103000f4031554a500546000000b480b00a2803805580c0103403c1e4000491507081e5000002d40c480869141076002030100603940c0213519080b203003949008501e090000d258200088a044140401421684240d44030b842d050b002030300340c4105401940e000425a184144130b640003e20707505d000c0041b40131007454548046080d2110038191b0340c0c010390540090502a1202e18404c2c2162802070064170215 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 495649847 1250 495648597 495648619
    0xa110705060403050609070e0606040e0705120a02040f0603062315070b0a0c0e150913060b031515040302190504090308180f1e0313060306180b0d060b 66
    0x2807980d4010380003562245016203403900d0004130380c6140c020135074403100e01d1220100610a13281c4405040302e003030398840d0a1071078190781e0344942698584a09040500110704140410210200990250081d50140c0300130b0b03808a075540030120103076415802040c03048a5014a0280c0702200140480070b20b034800b4000c1c0d2403d00641111503150b8029010548030341203090200b160b2200513228810095100d400c1010760801d42c4030104011026040105908050004060202e03590380600d61820301c500301003e00000f81c46003d0761071781d500191050582250300310824070551078980c1c1114000c6000d800d2081c203081c5550200a001c1005a41c0d0240100c0d1011010420b0b8440e8001e0048603800380e15404068101030444440001c82040c0d0f00c0d465411024000d0201400032400f940c4220700c182c1000422640040300701d00b1072042d2104005a00d02200e0300041142d01130b00140d007120145401404030483c607881903800d0324020920203901005040c000340c0003549aa024121059014203415404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 495651097 1250 495649847 495649849
    0x901052508070f0c050a14010804050f0307050703050d0903050d03020906040b0301080a0b01091817090406080a03090b0301060c0f0c080303190e0109080712030e0307120f02010b01050a110705 84
    0x1903803242000f40c82c50492640100148080380401800400003603410135411864000c010040c5054004070604105110340880d0030700008115034984441007109032a6121a07a00d40a903840b400c83c0301c201c03070394000c4102d00d801a03030181c404da904481d0450301130145150000c0d000c400a41c0b10305040b59002e8404d2201090004401c005140600076180c01070101e00240e040420300190164810301c0c48900b0803602807494171900b9203124040351302a4800c020101e8202c3d01030402e0290349402c5812034030b02107001604100000780010018082d4481d04030240e181e62080086110074060300b00810b915000c01400540c91900800b0010300814140c110561038003102c0b8219881030301ca010704004400c40541c1240101d100da100468010340007004480d45981e5544440d006d81c0c030026000340311800c1854500b03070013038110120b0005404141da40d1041c8501d4030301c5038146900e82c40070014035401c13490584d10b4014460f104100c0c805840d81d9003440c6001a00f01ca000c0c03045c00201c01140500c0ca80040c00d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 495652347 1250 495651097 495651113
    0x408010507030606081f14040612030201020417010207020307051201090605010b0c0c03150106030e07080f01050f01050907210608010204030c17030f0306060304170a0c030f0509010525 81
    0x19200c42d940401e50503d4444020302c0005c0181407449540b030b00d415620381e604002c0740700c40e00302c1c0e00c80101c410034001400e001800804055001140c08035030301c4040c20070594198010400c0d6070391011405400741041c00d210f4201c3c0200070000350150700a8400344103501c0d003000c500c81602c803542d0000c60101095920401038400a91040740300c0080401d0811035100305118541124000760001e00e5032480080c07240700c0b02103040c803490003450395800d09070203001c500b80001000f400b0100304842c6209101110b5a0003000111800c0d40029502000403419181544001340a00345c2641c80c202c1481c01d03000d40c0841c48604003c0c0d400400d82d240c030300059505013030000d4401180a0340d04c0b40304440c80d03c040d5020702c0c00d00c01c04001407034004101d850038038041c800550303400103419503c0c0c0e5100c0c2e40c0c034901072009100202c01100c03c17400119a504840c0c1e488201c1340b084501c20790340c1090403141d40c841643c2038052100200d0115105000390741418048a010708484070300c8806c02c51112540ea215288 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 495653597 1250 495652347 495652351
    0x1020c0714010512010b030402010e120d17090a02010822030c020a090501050102030d0902041107060f060b04051012140c04061704020607060203040309050a0b130b0c0a1704080105 79
    0x2005410800c810049061001c1d80454001428240382e80b820440c12012004c15105001e0303145082400710215080d640714100240c45008084e02c4080c44002e0040701030754502d4456030840018007581e0001048000d9001e08a01031403040d0010030303400009500548940000405484003543d07508922059400750080c40007190b03000b40c46107144904940144508500c140c0c21144165051200422181c3d0b8008200c42001900382000a9000083e10004001e4401c4136440020040c000c26203c040c000c482c0e00c0388920200010041000c5591801020b1450086109244d40402066500215140106107801d0075a4200e000090016001d12020300ca0350402c0d980b007031440b00003150522100d03800104000000b940040c4043c42450194005040e40c4034a0320010701040c1c0103c080350401d8054464400540401030000075000d44600320038185400280080c482105001400528620000212207401040074007620941c0855282c1030310100030138060f100d0240041100058054080c8500d074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 495654847 1250 495653597 495653617
    0x150c030818070611161d0c0706111b0c06030a0e03070623010608090a080a0e03070b091509060711150a03060608090616080a020c0f0601062303060906120102 69
    0x70149182201605140903031103220390801502840080c0a0f041051030603551b0030052001210403a44d90040c0440c1c24005c4c0240107100e14100081c000008502c9400362294184558910381013800030b0201d0796441c0354481c1a150042402c00100307a5242003904103168240b035040c00c80746030a140e40e9904084031620a0440700781c032100c100d291000c295540603180101000c0c5854409810407800d2191034064000d00103202c1280001c880442da4010200203400440c010240d46859070b54031040a00d550210541c24400c038043e144042100203210192000f00501a201c9400c1412643c0c953310514a010b4a5591046c01c08907455518078107000186056101c0350b50205040d807074240040c042010190048103181c01101c1080001e000304102c01610201074a1300d24450340310758449600034410072441040c11b02620341c40411800d80000d425040b0350b890707541e0200648225402040e5001c04800481030404100041261803400300b0b00240c02038001040034111b0220001c0150032070340028000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 495656097 1250 495654847 495654857
    0xe101b05061b130b070c120b1b040602070506090a050d0825020d060b0a1d160306061209020a0e010915060809190f0b07090e01150c0308180706 63
    0x1804064600030030300c0059004075606101400202c0d41da00081ca000744d50000d200415008203100f0340306c013040004c12000d00c2070580c3c2c40c094100501480e40c01c590310700e609816040500070080340e502c21102203c4c2c6541c00344c21041d06010401170a23a01403204d15500003104000820140e0380ca22000d81742d00d1107509a5070f41c03000b500d51010840c8031403c14240035160f00301e11920158440c05030841c0b00c590b0100380045d40720008400901038a07111340020f1801c208105900106c0082c0b109107a001d190a00c06c1700c111400c0f015022801e80e1624007d0b500081c1d0300c032491145181154102a20b000d00c0103040c1c0342000c5e1a50800d603a042003d0748908606500d601c8a51040704d0b41340c0081001d004c0c0b0740342c030810500d08041d25a642d4008244d032811a01c69140b036810502845511000500d6405800e002035030901b200001c1803102140221000880f103080006601517401c50407c0c42c401c41612035080004841d201687c0d1448004c005000b085031488402102583c141301c51006014543c580d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 495657347 1250 495656097 495656101
    0x206010305010c08161206091e3207020106080307120807030504110d0201030204180504051608070303110309031204140a050d14030c0604230105070e101b0506 70
    0x50941c0d5400010800b03100d034a4040c0002042e5036603541034041c1c150308100381e0948042c020f620080c030807030b404508102e01d410701d6400b21180c0031509140714014613605201c20039403202400719041e5400d2106180040031540e500992b041c41400030307030100d0f4600000694070f554001d55401c2d40d020074401c0303a8008141226110042d0003200700c80e00558185010001440c06a03213401d40130510201035489034010021600442e8840d4048030060001110340001001c1e850414401424058404070f030f40d0301910f10080c550205072001c041c00c88803c0700c01400402e01e59141600c0e82801001081c0f0303240400c004030305864400308a20f2082c540c1c2c40500350340d524a01080c0704800c0b198030482c03034030038400345004010b10740c2c4040302c0000300f40d040104074048904044142d0700e5407145d86101d41283c000c03502003100740700380000784d4441d0030010101d109424258000c82c5080320704c200d400310085003444100e44094145240d540c45a44503904145208941241151420140e101d404903030390350103481 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 495658597 1250 495657347 495657353
    0xd0e03030d060b0306091e28020706020d1d30030403020715020d2a0b090609010f05090318060405150315060c0a060f0b040f050403110705010e0d150c02060103 70
    0x56040c0d440140d80505480ea4a840048021200c401402528001480140003008d21510300c40107406010b907040115074415852178840701a400040703115030303190b1800519500e18040b0645c0700c500c440e07000c000760052886094a0034207a03003422849250300302d00c201008045064050045004074004c0c2c0081420503d049030100000c90300558a4046421080150316003c0c0c20440d0302e01d16015481d11941c6901e80f000300740c8048000c5800c0a40086044000e00280d808081403050068480b100240242054244000140d8030151a4405160301c2000303615990256220515040c0f40010700c03440c9816516000506520002d000036541c48078000144000340480c07100c10044554240d621a080c20805800540c03aa0062440030341900d484d400880c44c0900c482d8000d001b468001407040081a6500b01d03007800810084604401155511004500d250f400088210840310160341e4900740c0415a0140018000d503800204c2d08070b501c003924442c81003031a001700310b5103000941c0100400d40c9942 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 495659847 1250 495658597 495658609
    0x70503040f2a0f0b120919030c0506070207140d02030a0b07020706080f01030507061d0d080706180221011103040b0709120b0f04050c0310020d0b0a080d0e03030d060b0306 75
    0x2a101c8400030040702400c201e13030034841c0141c42c4410211aa020390554602030079070304003082d0380318a4030200480c15007002015003120b45242528000c1c0100c2e0519030340c0c0c54069039107040c40e01034100c00e4140500e400c1218030f0b00c2e0340b80c10255440942a45c5504040f03070340354690303610240d981c240960030480040c8030f820341c8150800e50110b0390804a807095407664403032980b81d0701c050103100304119444848032041e40003050f03110484000a001041c64008a003482c04064010350030403900241801510007405030043c0c03111040755002400c4a20348a1800488a4658001c01403c42c66540300c03400c440103101890007461280c0d0003105109451b180c0040000c002c20b90703681007410140310182c1d01c100460400302030140c0c4100582c01d694941d444d242845403900c18041402a0705208a0380c4542e07a050301c0703130003515288240c84000d019200340c100810159098a00526004c1e52044501c601d8140c490070045082e4400a41505e141900b4890284103071401504207240c2c0e4003000080c00000e04000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 495661097 1250 495659847 495659849
    0x10c06050106120b06270102070314010f0f0b13020901030f02040f0503060609072c120d080603150615040506040b090f06071a0a020f0414041a0306070503040f2a 71
    0x1203402510301202d40c100e0540f08248100f0b28020706c01164000d4089034002c202c03180156800140b01c5048450b0041220b0103081000081d241250070319900700d844400038050660b8a04004000080300300e81244040c001390001134070213042544403d01006040010b100500203446035085490030241808189480c0c54000ba0500340296000800c1083e0564000503003000c41d44542d442025051fa0459454590421100c200303601522210070514184e0300061441c082c416203803512640c80d5100400c0544400d55101024070005004001a10f949054000040c01d12200c48001e810710341c49602158580d085a000350400c0301001078440c117146014032145064060032075000d4605070080e40e460400c240306c0040a2403020b650408129050030340d8040e07031030001d682c00d0700648590381e90046011100c0c25030382507030290380742c120750a207040b020282c550725080014004001c6511034020849d403540c401002625180941c1081e0400200804c40c21410406042c07603c0c00c80a4110030f0818445c682 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 495662347 1250 495661097 495661099
    0x806010b030709030f0501020d020309030c1b0105121003050f0d030f0203060a09020901030e0115030309050901030c0e04050304030503181801180b041d0706140a020604060902010c06050106120b 85
    0x5008002c0381560040120b000e803948010088178180c0d040c600326029000d1a9548808039002004015209c4d00c000b0160010743c01304802c65801c013800c18074034140c0407002d903590b5000510030010f17400418502d00125400440001180d03946a076680c03a00c500304030031221414441d0304140c95081541b0390601840b45076941c03c580451039801d00b06d0000c3c10b000240c0c406d6000c3c42d500030070555001d81c000d60000031110000b030001e02c1540303c0400f10800385103043c0012004200f81c850085814101000d00d54140c179030040300c4607072203401d25000800045006004071107610082001100180d024405080c1031400d090400e00c1c0050280304004c400203101110780801001a0f0040000c6001e08180c6408410502e000041c1c00145202003400f4100401d0500020042c1000f43c00081000081100032036415560310000c400400000c007456108003900000140d0120020802141140c0d02868009105040109803240e0b5039a401054800990008011a010b0b0b80c507480f141015010300300810704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 495663597 1250 495662347 495662369
    0xf07030f030216061d1801090c1b020f0d0c030f20040c020705040b06070203161d040308010302151b06070306060309020303040306020c011104080102130e040b0f0c1c06080601 77
    0x100b044001000d40d40c0c000345d0f042c00c031101ca04c1d00004589404141c6200b601e07131150b020701e9541e101c00009014001c2140c56400154100a806101d00400c0d50301c0d00f0066401410050340d0b0f620441007100e081c09822003035890100148000002540540450198a101e00c1c140c075031424551048980b40500e01341014042c0e07040c04041c1c40b07282e83c042423140907500b04a500151981101000c00e80c0307402201c00c025094440c00454000c208410758819044803119000800354003617040c1030303a086020985000340820f80320f00c0140300503c2c0c2141340304070010700c03003010340c2c1400d20004c012800e0101e00d40c001d98940d00b025007031003480d07940350061380c0180c02242400e010140340d41e4081380d40c81c840c034480600342c0ea07404102c039100c0030020341141c5940030903d07a10315104d81d101c2843d94002e600101b00d800c1405a0048d001032a82403000100c5c0c400c0390401500c2515a481e44104100240300800b40c610031034040008907076540400d66200d004e8045039100003560f50805901d5880d0a00c10380200d00c17540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 495664847 1250 495663597 495663599
    0x10050610020a060c050408100e12070507031101122c030c031606020d02070c092d0504061407091712041a09180f10080c120f07030f030216 61
    0x10380c000600c1d0b8001d543c04070001401407894607040b589800780d500f02400ca4068000c1d40042c040c50f42e04203842d036030910130030b8810b91022034441441500c103035440200541c0080c070301007000c9890081d49481440301030600a4403030940074080c4007150012030324004e64402c40b01071301919042d00d141030341c11003100400952618121413803103039036800b8645510180d038803450045400c100d0103405498a140c9086025501e6401e98600306e40341d0340460003460340103890702c203941405000417141c070414003902d2a1800d0070800070490303140c06040018820f0760542d440301000d02c1650424803c0510985443d511038001c0350401410903243c0440306803584441e8407040740460414440d0007210105c1d02d1014092030640c0489050450314003402d090640d00002224440d0010030b491407030948100c900c40310308a050750300c036845491510064015626140c0c82404a024681040d039148058141c4120071158405010001e542c80c1a0180c1c00413034001c1c1d0000c85110070903404021848913610030240042e225 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 495666097 1250 495664847 495664879
    0x4030606260615041a04140105100306060f200d030501080d08100608061807020c010f110a0221030d0e07050a0e0c1e16110102070b07020607030e12100506 68
    0x500c07103180d6140c2c481c43d5100034417002603194944448413140d01400920030714815103600b09003c4001d01c036950141c1c10700c04102d030300f5910a01c03030502910003546814000f207083da0000c42d22800c00324140d07450600205071035a48000204020500c03030000e030751701040942c1030103011410644001811018080720006010480640d201d401054600d80d00d441b0b0001e903274403000184069a44d030182600708400e036092040c0c4507401301c0d00d94188042a00e0300c16080003040001c496a54010404441c6504105806001450001c80981c50f2070000c80258445d03408001c80d03541598803038540204110b60701c00d21410b52100a2004100500e030848180210381e00c0d1030006440c88100820382c4000d400c1c00a0a020101c46801c01c4003d801c40c05080c25407110407032074550348481d4540c00c0c1511b04c0407100a03400c1803580700254000a0360750200300726042c11800e03401d00c03449400480703086050000340050303048079480e242c2000c0c400152401c01414042c859503035400c21640d0140c650303409820028420510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 495667347 1250 495666097 495666121
    0xe031216090308180f060a030b03070e0f13031404060e04050105030c0d1421071a01080d03090c080607090306050a060608040209041a0a0e07050406030c0e0c040306062606 75
    0x1015110441d030301044a0b4440001e0010304010344c681c1c6d0145d0081030031003819501d90310650768118194111100152210740c58003842c40700702c40048440c5480b5001589501007440f511a41c64840d080807403400d035401020b0106504260030071000680520814144c0b86054052540104020ba014248010802010802c000c04601001d40140414031142c06800700c104171200150001a038041030a116800c0c005102e60f1003094180c4225040d9020b60f920300b0203401581e412640f030000141100e01e91903030142c000c0d120207141138416510030300d0000342c0c0340703070501150b03100d0f0103141d440a007183c3c1107182010488201501181c0301c03610300740d41400341a41154038107412580440305e54055550310314105591420b01440c200703070144140180144035415400c010500048071095034002d50310780c818041115103510014200304188034003040054002034009802030180300d10546010384076252041a1089540400150b10050083d0200021014814803507001400054401802c003800e45541d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 495668597 1250 495667347 495667357
    0xa12020312030415090f0b06030705030601140a1a071403071505060f0d0b070201060e1003061113120309060f140c03040503190309051801060806040e031216090308 72
    0x1d00c1110000105040c000c2e2942c0b400546428010107101144840c580110400b607500c00071645611981c011842d18a40800d900054075006002441e00c0e03132038902c1d50071400d0420128a0b07040403038000085070020440b21000d11040010b000d003503903958640703402294008e28150140c46034006110314800984580302d044004529a000407442d41c45070300001d039011500b0b82d0030a503c01b0124925200304902e250100b48110002d8008001e8966203007010308900d04200c6000052184082040c400a034a07540414000002c40300481e007071070320504142c0040e00441e048046803040c3d84410001305513211023072001901a91405181e44601da400c09000c03e0026007000000302c0000c50380b0340d1415030030401e5030001d0100a0407650000701c0c500c90020b19982c0d50344154001001002c1c040b0700c60030400e031348060004174032503020901d078030340301d070071074150101406090740b141e1251401d01840004002914080070110580e21341400c03d00010029140040d582c0c0c014812000020004146a1401d0b20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 495669847 1250 495668597 495668623
    0x1005010806010908120306060c0a0b0711210f070f051c031406040c1211030108010f090b04030c0c120b1f0b0d090809120609150402100f0e0a140a120203 67
    0x503102c2d1640c07c00a0701c50f0242d0f01e0844218820400e1507001e001400c0d0500d4010003ca40302c90307240010b50018661a82440d0301c085c007403242e02c60500328007031500200820808100102007814960250380c6d504001110324019030b0300d40e002042001c985040c0c0c490b0740892076940e040400c41c04400d005000e030b1003d40107041c90320440d9030b107010090881c000c055210341280b90710000c0100109180991903250020b0003109203135031800707800900345186886640440da401c025200240d98969900300c80310607030305d102119218495180050b058400e401081d11a07449103d030102c40345840b051360503000907401d05140d08170242400801a014a840880c2c0026900c60b00102d105101c5040c000d0003841251080c43c0c11204214031030900350301c0407034803500401000080e80c2844078081808083d0030400c1d00c01a60140400b904070724424050f03030351a54407151500b0088201480440010741b01c0509520074030004504043e041c4040c03038240d4105016202c034160080ba441d0007600030a545182d060342d58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 495671097 1250 495669847 495669883
    0x61d030a320105010f031103011a06220e220c050d050114010803120a0b011e0c061401140d08070308060619030204181a061608031005010806010908 65
    0x1410005007028000078100c900316009000f256910089aa41000c9034801035800c4092180181900d1030103028400398056911140c000b841c00385c200b0043c55a01040c10301d4542c0940300c0c002c02144686074440d0008003001c0c10a1442403400342d8a040e642000c580481410003008030031200010843c0f581c0c1004d07034805860f07811100c1445d252880c0101445641c4001340500b1000000e980100040105079030f00381c1480c04c61080e1103005460043d100c20480381d5011664030b01d0024259020101c000c822220f240c6806a6280e01c00d0701c500c0c0c203c44001552210200720080144059040d0860031400c084041c0c4565903450307410b4540070348034026a41c005040203000c80100d039503a603842050390300341c4d12400d510072030310201508050020b61141c411807426400006eaa1440c0c090503110f00320644009a090103003404d80c110030081c076540f1a110034117508034100d0603040442c800502461192880041c0d0050742c0c0c4c1820000b400700c5400404e207a04016021100780010034021078a007034105000005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 495672347 1250 495671097 495671153
    0x6120c0a091a071a07021e0c040e0319080f15041e0b0406080a0818031e070e01050d02030c010f02190b040c0b0f1e070602071209081903080a1104061d030a 68
    0x21070a1030b0703032040705503271042c201203500001000200040042c00d101000c243c0c05040c1f00c41301030b5241101281c903031030baa15030300e000504510b42008201c0c20360000100001025841103107083c0c07040e00c101c403003076070401d9170b60042c00c840e810a407244d100501940401070511b0105552280080c2c420300c40702405564103007130580d02a440070001300c4100f008001c40640c1c81120788082542e50280d41c4141d00d1030326160000003400d07042012200a940350040e01401c21143e01d00b0040d20044230309191b650841c13150180b650801c0e0a0448046003807840781c14480c2440c105414400000901900400b140740000c100701048480d24000301c4503103002c0e009d2480341e40c00d42d0340c55400303541c01546009001540001904020400c0500070300d445c10380551180940d41e5220303892103030344507030ac06c3c0c1d902e40c00b8070304280e0765001c24001e940099000450400c08100012450744d446d1440d00a0b91180d00030510400011800c0094583d090b03070341d00405d80040182810355140d86203100b101a07410101c81c6aa208 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 495673597 1250 495672347 495672403
    0x70e0319060207110d0803070f09060905091e1f050406240302070501050f090115181a0d03020c0306010e09072d15020c06120c0a091a071a0702 63
    0x6041084c0c0d079002046800041c500e401d1a0019070310441d040030024404480e11b8074003a00a0254605442d0b0329038410031404c7c02d103000d20601d2407000d07200100464500c0c400001e40d902d1250f038541703d48040208001c0704203052154003000240750304907900c44d81c24042e09000c6414030f400d1500318a519102070004049011900354000c0c0300d0104054000e50911041014014030304405030b0007004c03c08001c010b9102d1010003a29544618001c0031071203107442d0310340e224030310740c54000c1000d4880c0920311810303d1302c141c800101c1c000740c150070031405078024413201c00e8245005d1010500604191186401b28034242d98455125240c500542c024078140a002c0c0c041c1000b82c414583c511040c148210680d9900c541000c82d0808050520200511511071002c5050030b003030f02507a2000d61041030044150300e40b490101c0b42c40e000810103c0400050303000002c2e0204440584881032962004080e986451900707001d001c0000d5111803d80d4042c1e40ac0c10300841540c00039413200c40c1d084011903c500f451042c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 495674847 1250 495673597 495673613
    0x90906060305090322030503030f150409020306040212010605030330040f1506090509010501080d02032730010501120305120703020408010f05010e0709080a080f04090f05070e0319060207 82
    0x140014140348002720811007039204080580323015690b001170521000c0900c2c0c0c100400d581b284e80c1d00a4068010501290040c1804401550000340820012070b0150300c0c1d070b0119207150006104018014841100e002010110103000c4222501400881110b4500b03501c9072616038010000080004400c2000f00e80301c00350f660b01c201c024154400050000e42080108140601404e018400d540e001e07811031400b400f400007044070a400b1084600c250700494601c120700300d09014030f90282c1c001c2c075079070003600c13090070107a6850401c3c003000d5141e01c00076907984610508450050304046c4c0444405540c0501089d0410b0076070780150001d0550504554809508801030700031607002112640c280380d8400c00084039500468142d40069075102c9103580d07615070488504125204041081c0c200c2c091100116000a008140343c250b124015858255104120340803900e90001181c4c1c031070356802c14403810700d92284400ca1440d004500405044100c0d20f07282031601603010300100900e07030002e998403c1101803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 495676097 1250 495674847 495674849
    0x305041103010b0603042a12060e071d041406040b0703200d0f090203010609090b060904082d1605060618070c050c1203040e1018090302010e010c090906060305090322 73
    0xb8460002d41f40c1da0740407640510074100904884513414016918050580042c0b150121044581441503a5071014007251040c0c101500c02d88544100303510031741e40d43d0810001d0500070380c07007401480389529103600001e0071101ca40c04001280d00010900054004040007a5a4a10f601ea080003c812941d044480300500f10100029055400c2410001e00c0803120b5012200403405608a440703030b69982d03002c001c03030481c007100d0081c21803109001144000c0c00d10082d4811180e010025604082c0e1412220320f5140c0082c2c280d0803c04000340d54000410100307009044e003010007a00d2101408000c1b6102507004130000f0011010003540300b0060090103030030054400d0503003002d03190580040d81c4420803030b102d91041c02000d824081ca40041100c02445207215000c54200340d0703451400c06d261020400c0030340b4a01c1d038140d00b159281c07006151031320004e115240d0007100c2d54481c2c0c2c05080c80d05010b2006c0c0c81c8558041024507141c80100144980d0100c2100e9080390070b0500c0c0d404800b03002e51521100c1c1d01c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 495677347 1250 495676097 495676163
    0x71205070f24110d0809010b040b030a0620030f042001091a31080d080103080310090f0b0316060206040803092a0414010303020a0213110a0305041103010b060304 71
    0x141040100c02c1174002c00081d000b456118028401c4490400500c400d4600d2040b40d69099031111503c0ea01284c6980d00c2454905412000c107500004d450f41c400400346c01c2a41d200080f00c2544060100b005441e44554004100850b0940251301c131000000c4c10804407489400040301d849107843c10407601d82c034103c40003140c945e000710b1081c15180203141c400b039404c47c0c00503101036614007010604140000d044d02150300c4a9440c10303001cae801c0d99182e01c6150000f80c070460101c900307903601041c1044280201e001385020204002103070210881098506401032a66040d0007900300414444180e000c0741803075000d41c03c00039150766900c0d140c80c0e00f4070b8580107070443c000d580800c4140e040c0521010701c0244003400211070a004001c000c000103040307110288401000759101c05002401803c09103040b036032f01c0a04c082c2c006042e402403008207401e5030080e9011800640d03140100020006403c049903a102d2040c0e0003040240c5400c8085402c5100280002d024042900e05000c2a8503010504801583e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 495678597 1250 495677347 495677353
    0x6090415090e070302040e0609100f0b0d0b060102010b0111030405060c0a060504200105040f090c020c03010204081e0d08011a0904061203020609120901050705030c071205070f2411 79
    0xe0442807458550243d0b0000701d01c1a4182100075040800025aa5004000e504d019020103c040b4020500a03c481032001160946501c20b400d0196104106601a240206c00840c00e910b030060009007101d120481041c18800042e034240d658030000000d942c2510020349640c0da907140309220740c40c40c21080541c0100101d08000402c410030069051000c103400a580c00e40e408501568015940e9004501502e6030f101d52110041004402d02e410201c0d01520f01d0060f80c84001080021909a0b4020f030041404d41e40010700d40c2d5600000100042000151500074124004903020000c15542041c81115800c0c0308042c8020307109525407080352141d100041080000c6517584100c2014410740440036805400b903680001c0030a0000700c1c6000c141c005001d012031030a008080150b589800840b03043d50140b10500201c01e45802c200b040308080c0000306840e24503503a0920308070345003803c19000502c90500c441ca0800c045031286503442006120704003c070400c07640d0340c0720860700784120380381280c4a44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 495679847 1250 495678597 495678611
    0x13033024140f121614010215150301090308070e0613060c1a040b060f060a080609131718060406080621011b18030f12020c121612020609041509 63
    0x18100013019100c1e000c0c00c21680c01040d94800403d080911180c603c1d9002d81c0102402e00c0e409921b0086065001c626898001c2070690380b4800310703084031032810b42180072403900c1c3d0502c02c40e2070304412032401c100400c072001481c0c1600118000d59000251260105200314104442c0130058410340354001e5203120070303001c0d0311850300e42810621030a050b40e40500a40e00391101104600741740741161008604c0f0788581c011034641c4c405000c2109001844140000801900d4000040c200343c614606c5980708070b02c0940f1a071070140d00e00704c50702c032400e64140310340c0007040208072441d0012106a4845001c840d810021300d4241031400030324169440d03117446035184c0300140034088181c9495204444440c0d44210050000d42003184804815000142c04010026101000108003040c850722121081c41915054403550020a00400b400740b040c03507840d0032620149c01c4014220b40308078024251391080025840294010805511403808054051901d0340d081d01380c0207490480c00c0d0000d1040b088204084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 495681097 1250 495679847 495679879
    0x50a0308070806121c02030d1a091e0f09070306020a080403080108010e0304210b0705032e0303030f14010902250b13033024140f 57
    0x400e208031521804220004081401c0d400c090788601441c07443c0d0b800401402104d0611502d003488401260811403008006141403404030713004044040c1c1103140e22040300c141040070440300d502c1c020300e581000c1281401c425218801c00309100d81103000507501f410390340c81d01c8803000d041002580000e815a800010050590b550001030184120f02035991700e00c0b1039803520041407e83d00418080031859005200c1401030b2591503090403400041d41c4501d02c102003040da40c2da101c02c40c048800d6004680040100840454890750920171080d054880204030100090043d4a0700c0c0355001c05420035603940200c490380c03003075944401403602c0d030803a0341c400c20360b904c0c81d03c80701940c4440c09410844007490915550512035524010207168811020221941c5002c1801c4020840800030f030204030560318012000400034010540d40242c1d80a08401400f20050140641c1c00c070b400c1072050304065480031424403142c42c00b0760003503640326001206081a80c4001905403040540d000354015032040c84803480e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 495682347 1250 495681097 495681107
    0x3020607110f010903050309060d481d06070b090705041113170a06021c061203020d0f0207080f010c0e010503240103141e010b070f0618050a03 63
    0x41c040807250200140c210600465081c0e1640c80020050b81c002e200c00031141c0741c2403014000281610800003051f040c154039450f4010b00944080d1412180e225100611081588030350070b02c441074003030545903400d01010080085500e010580c15040d000702d01e07602690344907000c440020f0307081003040646003014192030340c8880342c5201d818030603442c103841d0319254501706050b103a004d80301403070b004071031450218100155145030310302d04164020f01c1c4480e40081c03000d00c05001c03203407107031089070400203080030001003181c50b25008003001086050710030380004d50018040f1400c000b10b03d0702c4084c110711420141e2038260260414081405407254000c89a8015441a2100030050791006a092181c10054902d0f100a0707441d52488101d2812625206a1079000183e20070818500054405005840300b502d56200765403110300356800f81d050072141e41042680d1405031100d0b554140c41c0c9031146d03540004000354060004c03c00c0c0c2d00c803882c2000071500b0f41072100c903441e008400e07036445807100e01e0f001788 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 495683453 1106 495682347 495682373
    0x26090d090303090506180303040603150b1611210f120c060a1a10050d060b0c250308130906090b0a0b1303080c0102040608060d0305090d03050403020607 67
    0xf46d81e02d0420003440288443d60340061004404103040d0b40d52100c1d03034410130190809222040c50441007034800603e030f80c1d03c1384034003101181131804200e6852480c401c001c80c5044000d113010b104040440e500c0181203885050b20b506980c009205012030140c04210030959108900144803018140c0c40800d18995151801480e100d001000624109040000c2000207c01040d40c401071a03941c0150009891b2856006003800b049814107503548200308011440c801c1003c00402560f500501d410700555000b801c1a55120b40d43e10701c1e800d21415520424000328607103040060918118441c0d0f22451100030004d00d401444c00030303000e4098120580440c2d00b494031050000c001480100142103e410300d80016890340c0c034110002d003803c0001043c0c0c2c0d008241000c0800e0000350301204035942d04104585007030742022982401c6a0600464200a421140010380b0340144444014131031 = true := by decide +kernel

theorem cover : BRFrame.Cov 495503597 495683453 := by
  have h0 := BRFrame.cov_init 495503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 495503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 495503597 ≤ n) (h2 : n < 495683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
