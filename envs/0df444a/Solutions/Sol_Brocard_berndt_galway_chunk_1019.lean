-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:51:43.272695+00:00
-- url     : https://prove2.me/submissions/8dfaa1be-38b3-499e-9c41-3fc98cae414f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183093525 ≤ n < 183273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183094775 1250 183093525 183093629
    0x260a02040e010602011b030e0705120106090501150806040f110a02060f09030403030206181608100b01080f04170903030c0606040c020105010513090309050a181413080310 75
    0x440001d003201c1801138410a07400121305c2230f0840b0139099501815200e400f551a000618486400340101c001a511804100310f02500e40c801d4500520040048038040040c03c0401060304800078450307441940da4001c2c03481000d04552103141107050070b41095580d440c01d058043d60790103080750380e401c0b09005800043d01c8403501109480c01c503585a001404c90b51030311527a801c41c0040c4880014207900c038103e110f0303401c007607429042e070001d24282c00070700384400d6803401c446e081d546039462140c140316a840510101c2d100c40076109901a40080e0f102c20b0300b41c5101c0341b00b40c140c455101c981d0303454880820341075802640450300d14041d40085a0410010300181400e03426110300344125540312002c075101c5250303081d0b9034210300a281c0c42171400d05820b81c1c8401c0003c609500d51380041054581c0e01e00c0d0445400d9030343c032603100011640702d9080601d107080c54981c800520341543c0146480c90110228200d0000502d5a002900d400506801032010020f50b1006040f03681c004100360b1504204040122 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183096025 1250 183094775 183094781
    0x90a060906020d050604060f09020306130606110f0a0c0504020c0114090c0a0905061005180d0f020111010501080c1504091a19081018021305070e0102070f06260a02040e01060201 78
    0x2da144904008c0d5084c60701040d24001d4100800ca41c0e0007848590510011001e41d00c15900a00311a03200c0d401c0101c01410702c80c0c44c2011f00c440c282c2440e40000c96000100d402200b5400845008a40c0580d42d101040702080c09480040e00424007030300c043c0107002d80c40502060441540a007940c0304400c117a698049042900d070142c6120307810200c01c00c4000c40f1544664010032a030320881c6c00a141c251003150101c1d000c204200c90540340000110711550440d0b074000c50780301d5402c0000c0024451075051150700d44e04c4000344c0c045144910303540d0104540701103106003524003e0070310002c2048000c41d140c28200308000311328062481200640b820840e000404105841503594100c001e180c00b10520030284010018945122001003c0100b190016130310441011480c1802d0703100401c0a051201000d0040c00199002d80d0554110308820300294031448500400c071038581c0f41216040340c44140f00407904580601071038820100c0310400401a400780c000700121280384050086d0740c1e03a07a05080b422 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183097275 1250 183096025 183096029
    0x1060e040c26100f0e180a02150c0a0b010b030a0606050c03040501081005090403030c020c010306080309060a090f031202070b04050d1101031e060e010519030b090a060906020d05060406 81
    0x8036030715801020002c50780300103040c1e10100c08a607003e102034960000091040c0c41d503109502855203401040004058051040c48142a00000b000510100d60010300e400082c529401d41d0031a000c10101d018480400c51080855008050000c0a5071100c10b140030b940c2c401c90b07130b14000b1400c0a800080061040c812111007202e1500030b141040e0804004446004e009000008254040d03000454960303604602e075401180b10791800980000d903400041e04114842c22076a05052034840100250301c008001c850910710129600307030761071826860a9607122580e8100c05a4982010404800c100c0c0b240c0d40030340f101c0d0ba0743d02250492a80c8226140c06403103240106074100b58000030040c0016100c40d001c01c4072601c141008242d20307000c3e00c0c40d034003200e0b035030318114014503150b401c06c10068103103070f00c0325014043c107590b544440280000041c602000310712006101000500c002200c20100f400242a0103074003002c180414801414200065000842d03440c08140c0b5203004508549080c0c1b003140c1c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183098525 1250 183097275 183097307
    0x70210080402150d06033f02120f031e0106050d02030901091b081b06040b0a090302090a0b180906180a0210030203091009032a060e070f1e050405190501060e040c 71
    0x8101440400080711f4031218240042c25072080f07021000041241201801c00303a0007002e00e050316071500520342070300541820201c82541c0d40c01d100501400ba030000031100e507081a4000541c7e03e8981540351401011051000b41065141001c51550729000e01a090219158001140d00b40460500300001071460320400c04d82c000b40801c4100030410042000d08207425880c1401c003580350b07403a004120074200858480240b10b40d41c2c248082c10385800c581c1000d8030070641002031568075061060650b122000340a40e03225045c4e0780300610319101c0c20004254195409044090728070150310004c0c010790020745035000035002e80501140205200d00c07d07007100715050741d80d00103044004142000458800103000c400044410b90602c0800d034540250550940d0328401804502e1a061007180721041640040401c840c07202032309640e0500181401003038070f104841c0000c45841e0349800c0ca12001d190b180802d403071814800001145604001e1705404888107036801e2100840c16001240e500c030010303016070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183099775 1250 183098525 183098603
    0x6012607060e12060115140702130b150c0309180402010c02060c01020c061003051c08061327051c0507080a1b080a0f05070210080402150d0603 63
    0x810300388180e0000c100108007426140f400842c564003141004402d07003141e90100c502480031a030241d4018240c04508150010081c1040303460350000b08841074611814654030f071035507240400c90759801c080b100010082c4208960702c1202d103482949030b41004120521480d031424407507404013481c240c26032041354140d5031191498050f81c03c00007d90800c1d00c800703034199400e01000d4a880000c11180303005807014449900d02a02e14944107160003441c800700f070b400c045030582c8450000e0308840d8050b0004011106180302e030b400041c1c0342c0000c04100040451518541d10790384041e440640d500c1c400e4502950540b021441d82010250311105203981040000e030080000030301241030340000c2d104035481850034051103202e0104800500762022000d481081d070000d01c581c84181c0060050660021a003403190034a22030780c0000e01c40c5190940380384140046540000c0455841d0204d40744c082c0108101c035911070b40c0101c039541c020402c501003124140450f0303c96100030043c0044c001207100f0740c0020301e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 183101025 1250 183099775 183099779
    0x10050901030905010b0406080604050d0306060807030e0114040f0210030203010b07020105070f14031201050f06090d0c03020619080c25050c10120f0c0207150c0c060206012607 77
    0x4400074040b9042c19241d0795600e407201d24070b07640c440c000c1100400002c0024451802c00e0708240b810700b0741069a002c140f40c90501c041105a8019156a51100580c02c001a010140c1c1220034098044940c1e00c10f039441001c01008104a481540d8a60090003550f4000d2564000d01c8141c00700e10082c0100c1d000510f0030320400c4019841a001401403510424100c2c1e02c42807655205c0080140c900d800c820207410204c2c4c80d010034244440384900500c02240c9014180c2c1c200303000304445108192800780142c107803051b0300b0103103ea180c000c007000b1035014082503540c0c1c110f0b101c0b40445150b070516800010303031040e010030514131045040c0c4009907101004100740c44460700407109140d00d4040c04468500820026009a607104400c804151400f13854456031002d604201070201d440010b40c0c00581c0389003d41c3d15201582c0080c1300d401750b0341212000010000040025590501b11a000822000c0da0000c007054480d030102d4000d049543c0f04000040c40d08204140003407500a0035040c04042c7d1001c0c3c81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 183102275 1250 183101025 183101027
    0x80a1d0c13060e0703050601020f010b1f02031207181a030c0705071802070b0105090405060411030c210d050403050312070c050d0c020108100b030c180d150b10050901 73
    0x5254080e0315200000441d01c3e620785000d602d0510840c2d40002180d0f5980422a6a58062003100b050611b034500820000306e0313000c0014410302807640d00f003000d8600c0c4c003814580107000b041104e0014503028107840d030303500d00000020f00618100d03500c0341c2403143ca40400515007802c0e5409900364458881e60a08599640254204c16045a8000d031028440c0d03501c0011a10766181e02c001c441c0b101d002c005640c031107007400d000e050910180d000a02403800002000301092010440c3d54020303901510048500d4203440020340750420203440d450b4408a06411401c10a945100404019a480c1e0a84410555583c816560740c00f071880040d006400030800320800c0400ca111850340f0203424203103001e40c85842c0e00c0d01c078a030050001d502004110010100c01c1550b80100f42180c0c06100d501c00c0d03400107800c02480301043d000c06031864000d070402050b40b01528400c4001c4088020380980001a2000c4c6410200c60b014826047c402074245400090101c1c1d062154881e6250203c0d42c403024980461780d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 183103525 1250 183102275 183102289
    0x10021e07020402090a030309030b0c09010203090d0c1805040b09030a05120601050d0504050c030724140d2408120301060c2102010603030e040c09030b0403050712080a1d0c 75
    0x40c00c80e4016420440f41049680350040071002c0c500983d58100c0d66030039840d00420040e00035100740740b441c000f4041c0350550780c0c1c0041240d25030741007a00c0c440c407548404c1c0350540c464007054110408080500c0c04540c8922100e45c046403180d405000c8144860729124102616482280f10403c00640c041040256200754245556080f00e018034005141c4007203c1005021034406440c121031980140ca245203040c90f00f001501c001e041e241640900122a8400d0f80c2241040d0781d40346014402034041c489450300c001c070140c81e42c480e16120240712203000c20004040f01c09c0980300e41003181071400404556154001100341d00b05280d242150315503400e1030401e513158201002c0485510071188520b0002520500000d204130160342c002050440c01c3d8a802b170304048582c40540e00a600d003014000449610444181c2142c1d04500007070b1003a1102e0500300d46500c070341ca130050319680b04145020075943d4010b000c0c40c812404000104991080c40c000854044401100c100c07580e440f80c2100305092600e21 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 183104775 1250 183103525 183103537
    0x221b020a30030b030d030606080a09030903060e03040f0602030403080d0b19080304051e0307050f0102030d022208010207050601060813050f010204030606080304030b01120212160810021e 82
    0x40c4140c0d2014400d8a0842091080864401e00283c1c0718180c14416041c04c20103540907903241e080510100b410108020050000144100c00c0103031903043d42402d260240010101441d000b103401c0c4408401c80d040140d0b2580180300d0701d004025070003400100300b4800b0054a065981c840c0c01240f41403514003a40d0060032021034140e90110340450080a110b2415595800900024029644031403420080242c001c41503414000041c001044005441d81d02080703a406035801144c1500b07108112500407845d40c0100a2501c003030350310005802d088150030001130703020740c0322046d0200c4030241c540000318240e0203070040c01400390b40000d006114403801415415801000c2d9000d0000c0c0004503154140f40510811000c641a5400074003402805281d004042c081e0034200002c5262a00d03540e101c43c130803801407084031440c44a002d0410b003156182440d6104181d6900104c0788080c0c21b881d011207141e1218401e0007500e1042080030b01042000e8000c0c2c8002d4460010442c0580441d00103505c06a4001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 183106025 1250 183104775 183104813
    0x11010c051c111905010506120a08300a0b0607030e2e05030f01090608030f030a090602040311040c03050105010c02010c06020408060f071107050901050d020d02221b020a 74
    0x1040c50704050b0100144402d020301c2c14464010b003080c60030311a08480002e80103a01031000c0382c45540350303428005084201103600c00e006070390f55060541c1100141e02c01c120b01c044408181307003200345030000400000e40039204259082094500c0e4100300800d9105640c0010082103104920000500e000b4010900b10174000e4050356407010000d618036030000c000340140d004540040140282200c00021941c09040c6c11002001b031541040959030b5640581c680f04054800008000340c01c124294111540882e40f0242c2552103c0c4c0742e00c0c082205260846e00ca41c0282c4c50650b440d0120343c03183c0501e6040761700c180c40340801e20517a86c004680610b00b2440584505800304000210b82104102d994482e0401c0d0301c0030318480c00c001d500140015107101100c81c2507071003038400707200c0b981d0b0710b02c8054116202151881220807061011078841710603450065400151030701012070081c60301100795a000c510850400424503c1d00032417214140a44858005a100b03555420000740000c010486403551 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 183107275 1250 183106025 183106037
    0x12020414090405150901060654060e03101407030b060c0303070e010f08090705060c011503080a031404110d05030c0f070e010905070804030f0c080f0711010c051c 71
    0xa4210744113000026190024142e5681c0d104002c0b0945c4210318910380010708944c0603000112080315210b0b040301d880710f8020105035840c206840d425005441d101d000c7c5a0322880106e0b56140c10281c01c6013841d4842c24003a0143d01042c08250501344100c4402e5000f440b04840e942d100d08804400500200070710980010f03040114045609040001d5403103149144c0d19004c07010b50420004049600698002c424051010140850f078800400c1c500141c803000d50b00142c4907410000c8007805001003281754541c16148a4021090002c10340081000240c07549090140007074180c1400d0603110300715405050b0801d025241c10740e0385080856960342c1d0f8028811a800e080d03091007590300305041500403415030b9100a504000300e828607041030f80109941c0c1d2080010b4642000c029020342e100038001010407070b0f4045c1031059140151114000260499038490302d508481c0341e90038165001080603070362024000041e0519612586030421150b81c001d01400000c038100040030100224000304d8818041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 183108525 1250 183107275 183107293
    0x9060503041a27030d0b01050310150c1a10080a0308010b071b0b09010e120d0c021201020c010b04060902030105060f210f07080f09070e0a020409090c030312020414090405 75
    0x100400082c003d000c00000555500c1a00000c1d00d01194441d003451810320809208000c2c4140c04090301c81304807040c2e4000c000104034440c0040340c8904101d00001c00d541103140200b116500380800062040c4601100300341140c0d02d174400f4681d1021591001400590800c00610240a886001d0000c05214042090300f44442001e6882d00761295000b00c44000004180b00c112982d10040883c840101510740b1034415514610113625808a050740d00c043c01543c10416085445043c0c0d05060700c52498021900c80c1125a0301078041c1000d200b00500c40d5007410004500030880d0700c220b904a50004003880d250080303146c2d1590240d0000300041c00082440400400c0d4944242410f500c80c1201804d074805510f8680c9024204c40d0b4044c0941003408102d40800540c190002501400d4650a610022b5259214424400a032080750001c109182c00d001f00707141044812030310300d01660311a0b02c50200c8480002d10400c2203000314070841c48072600d162442c8006040990310550010700820030342c1c070115 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 183109775 1250 183108525 183108571
    0x7120305090418080c01050c0f07030c1a090f0f0706020309190b180108150102060a0f06090606081602060f010b0702030a120509041d0303041112061609060503041a 72
    0x1000318041603c10f03030400107003031045c400288102507002c2151104a800c0252084030b0300c070309009081c4000c080c4919000c410040c8440000040581c05c5c02d00e02c501c8852130090300e040d4a603400803000008078481e0303444415206601246a034240c0300698015814410644104100c0d14034400c84101c604450a03808105112240001c002d00c3c00344251280750f00700360380c000400111000b401304600d40d40b282c0c4d82d031449130313808503216800000c071401c0440c1c803500c4c0036620001400c0f1544181d0302185010b40020b611a04654450f01c14000062101c0c25441603050030ba0b100c0300c0859075407408240340740051040c1d00c1018050041c85002500300e0b0803d049684e10351242420409041c0c01084c40810742e071446140601844540e089001c1202e15400003c40d0407507a6404003800040c1a200d941c42d052280e5142c1905080b034881d4600308030380041c00c1504642c4001c00c404100c88001618040c004180940128100d030b0040e64481c208203025907030400c280c0c407002e901414400350b200403c0e07183c040361 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 183111025 1250 183109775 183109811
    0x913060f020307080121080a0e090a0603020f0a06020d0804060e030d06090c0e0d1412070605070305060108010b0a200327012604020103110f0a02010509071203050904 73
    0x2420031035005a59080100000d007a4820581c030003a00007401800201d8064039030000140540c1c0e00400302600e540058006640890400d10615003005a100800030007001582144040342c0c0256078015811005400307010151a00f40241d4001d640013100d900c0c4164861004141c0c0540160350008a520703030910302a0865101c04949014a40c54602c144850500c0b48141044503905080071904044107801160910802620150038000d040c0617100b0074210500840c0203000c040d08849a5450644c070301907004110a846c0440040d1070580017030044e50007803a0b414182e60940700741906100c2c480d071044034800c140c1d120355428001003c5540c81540d0040001e00741048034045104003034000e0032079000181103d0340542d030401c0b044100216a12019050b071021001c040c07a0b21100e95600d5000503405004c1d8150081c14100d000030310f106601c10310300c0140488044a5000703214540721094129603820707441c00f50f40700905001d00c40b5000240108000d042008010300b02007801c0501e002d000d222 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 183112275 1250 183111025 183111041
    0x304031509022809020a02070b09030c0d0b100b03190915150303033c0605100e0f03060f130204061a030414030304111003090605011e050d11091306 65
    0x100303d61084002040d41d00b00000b10190080a80c11401e00b4250300c4000d607105418817584441c48000545030010b074805000d1031050000180c00c00e42ca10b9504e00e000740e486d9508442800010a01c48800b2540c520700c0f0007100c1c01841035140e0300c511896400d202c0001012609822101c0d00030311021001074183d207000390103010810311202e0035101c0c0346003030207000e99a4900c814400408640da024100805007000c40c3c4031000c6c55000841e40591596000d40204142d42001c0e50000b024072545903401d034059029604250107841d10607410144d10f00341942c0701070a0f80c0d4410707203483c0325002030810707400b0280d0400380c14001040418001d076902805d5907034a518545600ca0403400000708820f106180c0c40e040141a04440114550716103500c480b4600d96201003410700c03860b1107038600d2003020321070382081e148203401030420030107035944126070b502889404410b403000364034020340005d183c40c0441c03004501325004607000d000b5070030702c50801040070310045c045d6000000c942c8441010818511401d04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 183113525 1250 183112275 183112309
    0x3020c0a060609110415111213090e010903090902130302090108030a08090d0504030615171006050f090406021312140601050d021305190e0604150b03030403150902 72
    0x740281043c0e05501500e41d220240003101100700002c010103250301d00300681200803442d00050440900c0d00f01424400403001c41c002d080d00206240d0341c2c81c00490200412664000380410a141c5085c00103800c0c5c2d0000d4502074086007420740200310030050380d0000c1184401c102c10241116803654001a00030000f80c200140640c00806e06c0315240343c02c030a00582080d81c1400407c442107121000426030321450000a00681e141c490a103580d020380e140c2180130f40058274690039421002809a0b031764008941c140ca041c00d0400a0009050800c6480c1601031390002d005e89115a4441e11880c0103940940704481052091060001c1c00c0020160610314036482600c034030804c40120006145004011307040f4521500324001c03c0c00042c0d5954181d118005c1e41e1700d0021580342e95148210074419182d44041580c1070030b0021104800001040300d034410340c070880080c9508005030282c0c0c0115010441c600d5095071003044148080780807509024880c0f07081610215084600750b010800514503614410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 183114775 1250 183113525 183113531
    0x60602061902030609070e0612150306100f170a02030703150b100f0309110306090a0302100207020a05011d060d020403050105160e0f03030d05010f05010212160b0703020c0a06 77
    0x441d800007525941162804112801d60a5007840b9000a14540020b040f407014400a09041d600c80c0d10b4842c25a1280c40004145070100c0ca400b81d0f11010351140b004160744030740030310130006170511846e2100d03005480e6482c01599189042c4801d54a440c0406461160135100740400400103a9040142002440c8a64088804111001c901d03005a40e51840614810401e059065030381d00d40c005100c400d1940c4074600404e0b080b845042400d05e854440d1040c0e80c15025040400100150014051110a109a0071255992039a008100c01c902400f44001d42c80501e60408021640c0b190700503105103800305008501c12003102001850740d510543c001a04941c002c6002c000707004081c130400c2e601c0f04000b000d0b0091248041402040300200d614403500c503c0800045020a4408101741c80c0010030717a00d820002c81d6111000400440d226204040c0180b10305688400002d800d5415121400808400d441910310142e48040700c0681c02031a03c0f0800d9424410882d40740401c1114481c15030280b1400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 183116025 1250 183114775 183114781
    0x90d050d060b0d0e160509040303021803010606020c01022401260106080a0c0905060109030206031e09030309010e0a0b0a021602181006050c031204020d020909061e07051b0106050406060206 83
    0x10506204a00d0317020540740c04800c04c00c1101d80c0b140c048503640a541490010b07640d01c032a041c1c0c0044416500d01d040d07015840c20b0710100e800c2c0e030001900515844240c00711452016611000014041c816459004210480d00100002000d0803110560004405c14032083c0951400c1780500311a0145d1040c2010b5102c4103058040c032181803041e80242101d50001c0c00107103040f0001a00e0001c20303200c0240907903400030014440d0b4801c140d04505047c1c50200c40b403c9824110b01c03031980c982040e118101e45510b405e02c44c0f5526400080c4400e10141d00412484030b5681e13041494009401035031304106080e0650310581c0c0144d4800080318200f041c0b0798161212400d02d01020307400c00025410038410300c1403c20913079050f0304001061b50302ca000c1030701900b0314550311840031660041d02c1c2c0c54025003141c030340e10500160680100d40c1c1403250a99180c00750001890304009010b0380415904500446d07802c00482c10368600c40700382824030700e06680010030038969902c0400c04548c05940504016008071040c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 183117275 1250 183116025 183116051
    0x702191526061011010e0a0f140c10111e16060f0e09040c1710181208040c1a0406090506090a05131b030506090906090d050d060b0d 58
    0x10541e600101100180061800d80003041c416524250201c084c002c01800352944000250843c014045c841b90640310761540d1450500110201400c00b00c0d10303501c401c84032042c004400601410610f80050031881501c920f000b00b43c800f10030805044031113000c0ea4a004079201b03609484419030383c45100080146503c0c80c504001318030095040f010410107403918506060f5400340410441d043d00301d90b12986038559180c013024140b600da010080d000c46180090f075500d1030200d0342eaa801c508070001030005001c0c0304803602c90203600070310061101c1e203d007400044c3c50f849203001c2a840f911449111803610b031604050424404c503110030084a120000f001d1107803941c0603017500000c041c1601c2c5d103400d20442c1c0c80082c1c20220f4600490380101d408203601d151603d2140c00540b1221440903030101e02c64141000100945401c0f40d4032401181180041090010001035151103004050050321071540c5c51507040700e81d5405401c0b5243c25907100e480100c1c0d944061002171070050000d01c070004101d402c43d54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 183118525 1250 183117275 183117317
    0x91209140f011710052e171b0d0c0c0c0b3402090f0a060605040b03040602130b0a050d230c0a0512010905010617071e03060e0f010e010503010207030507021915 70
    0x4031a410000754a6088031f40100c0f42904a03001111102d5a011103c42848046628042d258201c54801e040c4034040e02d00301c2d0000c00084e46d040c040c0c6038240314a900c0c0c4a0000d03c44c03096000c032441c0c402c0203c10b51415017104042a01112030f058035291440021a00002c8801009449607003410101c03605004400003588920b0008102c1400c0c503608107850200c900c45c150000a1014110640004100d00400070042c92000038040070084162185608031005009411019403000304a190400c0c420040d9800d0402c4903181e000d00340d808800d80d40d070004c2e07101e8503004414244c0c02d010301400485555500804191302a1075610000030769503140800040c04080d6000844460810650500840603408084524101d2204407000c50130155280f044005001a134000101c854000c420310554180040d030542c12680441e40c003211690b00e810800d400c03071240b9200140810350810140c001410700b60840900400c0c01c0c450141400e940c1d030018925551011070030b0000601300750702492541c195078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 183119775 1250 183118525 183118609
    0x1104090f1505030d0c02060a03060b07080d0b04020c0a0f08040906090e01050a02070503220b07080a0906020c0f090c04030512031602010c0e0603040501091209140f01171005 76
    0x600602511400d858003170169450503030040c0c0620310010780c0c202d106010782c01c604001e02041d03003069a91101030a1110f00303900b0030000c500c0c0240c1411006559850140240c59042c00d1940160002410f82c0c0d407100c00219110b142103501820034000007e10481c00d104000060411183c042442c80c01840703442d00b1a5801040c0c0c0710400e1040c0b041c071000c9240001a00d5824550a00700711448003031807015100615a94030020200f02c000032080200700100001d4580a041500c903c954192a1030707082e40c823001a41f04440d00101310000750011807404000d003c0d0482041c2004511701926070721503c0c2005011801c0f81d01340080041801100000c503d06418840107a00c000c016020540b1402401402e9581c1c04610840c00400400e050000039488140b5190740003152400c40d00307440c180509111041d109000c0742e10210150201182400b428014542c0700580d200140707078503401b00140794000e0140c040034441000c944041034940300c0c044c41600b480c140302441205005100d09106c1d40105107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 183121025 1250 183119775 183119779
    0x4080c03030f0f0703031404030903050c01020d1409010e06070f0506010902090d0b0406020d14010807051e09040804080d1d0f030601030215071a0103030809150106031104090f1505 79
    0x1c000b074041207801d01060b00e0b0070b80740010380305940d03410a0030210050a6400d1304103680f100c0c85414002050780042640e41103d110700240c4440388002001607860b40c80314221100801c4401c0c0c1c540c44106400300003030903803110504282800c0c82c1c8440210b0310b90f401026044805600b00711b442d105011040203031038018032420704150714000315400810300a40305520014680f80104021a04001007a01950715819103810b007044540200042c01602080c02e1190b078289004800012803c1e04006942440c00d118400c4e1480c0c1151900301070020300c1c00020010f5850a8041c0f20100d540706050100301c0b81003410f580d81ca6040d60000c034408419041081c00103221310341110281c4900e8501281d0141103a404460540400c0300705045006e0754416404000d2412209030085040508002003041c142c80c00780e620243c06540d072030116070743e42401e20360640392818890010400c0e20f00c20340002c40c503100c0c01003c084c10f00f55601032003000c0d9000c1c0c0b1f82401840d0340380d0a807201c0400341d2502442c010700d07003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 183122275 1250 183121025 183121027
    0xb010f03080706050a020f0c010b040501080102090f0d020f1002070e0115080f04020f0d05010f0f0207050a1203060312032415140405030601031208090a1a25030204080c0303 76
    0xa107a440d80801d10030900000c000320344400010300d00603995030603200300c40544509103545010540034240207280080301e507031042d072804001082e50f0005109440c1c8100b0040c2054180501c048200260031500c400126882005011041100e4584105822034190b20b80c00a2480c00c2c00d1221a00700e180c8140c00c0101030b030412140c04141150302200d0301d45c103c99240300c40300c0c082c2c45038000304a48131509803106821081c0c40304031404104056005400041140208000c1207041650803810381c49010400b0303005502008450300402c40400340c0c0300c00c030021400c000400994030303510b02548001c44005000426030f214285105a00c03405010555486804100750040d800c10a6065074403070140709030400c01464005441840c1c1c0101d044030060403005040340c00d0f9603540d10313203a4000311014200100007004040400d40f1420001038010896901122031803407281004101d081e2201e00400302d400b0910002d044010a5080c1e11000c1081d0280d56405a5500c0c10f04102071700c0d20341001000380c002d40c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 183123525 1250 183122275 183122279
    0x70206010602162106150602060109140105060a02010212040b0405060a0624030609050a0b0117060d121209031e05040b0919081902040e0a0308060108090f16030b010f 73
    0x85818000310944140ea00c00c542c0030b081490703240c4c0307004005807401003005140c483c0d900050001c100046080390419030840d60140e032616001025520180d43c2c1d5070310030107000010301c032510b050005040c124000b817000505000d9600d50780701e82a401510190f60300da0043e0306010510a0500c15641d12580581c0103011592401b007035045c01c10701c81541c1192080c825040115054401d8000340014910010305014038105401d01100802c00c0f10034103804240c108600344c4c2420766241504e84a040300406406e804040c540361140ca207414090488100003880440401c001694414020301602036651501d42d20081c010b00d00c24800180154010711006000802c110a040001c1321030f00c00c0c042d14034900003807000341038200d110500d411006c4140540d0b5000b1420711407018035050200e008642c14030049a4606c0b03900d88524030000c0c044e0004500400241d42c0394010030042d90080c0d6598102e0385480e203035021403801e01e99502d20188401058400404c14440d44a5180340074180804041032414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 183124775 1250 183123525 183123553
    0x1030c030311150f130b10050103050112080a030b1c0507140303160f050109050d05090112020910080415060314060f01060203040e070203090d060f050906150f0f100503070206010602 80
    0x10764000c2580081c81d055200081754a804500c09200d40c0d0f501020200c202d00f0240e580c41d0b0007821b68052180000e1800e4000548101d81c2e00d050301c41c5580026405107413500b410b0045016110064401341c000d03081c1a0f6050603012030103107204005002d2030241420909100c1049004034034029014481c0d03009100d00c5400c2d442e80b0f00703400009580203200000c0340080789400e43c003409801d500a41180211100300104640200040c403c034032090303075000e00c4c507200605050300320b025480703400f60408100c40301c2c124554000c1440a0b0072902400c1000d102c00c6a90b842c070415220313503400c101c851180d1031607000700910b1b082018940040803481c00103410341c1020303030003540c1740200e01c10303000c644c0340c0c42010407080ca00a00403550180c3c00074041843d442d94078140300c405880764104182d040791070000002c0080c040810b80600030100b0040410007071402c9820090481d032a0610190300c091031650741207203076888080250b40000710ba01e82d25207078500528083c1c01d00c01c05138462010754000181d020031764 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 183126025 1250 183124775 183124813
    0x106090608030f03090f1911010305010608060402160803010f030b01150206070c060608060705210c0a0e120a0b041b0509040209091c09300f051501030c030311 70
    0x80c80c00892034a903031352002801d240411020f030240160048480020381216400e00c2c0090380c600030300d4442108e030149401141261700903c0303020f0000c2c2c0c2c10303808904039280c80c1d001800d5a00b541c20100c4200b1400d03840745032682c0e00030703407046030105d5600310104100705504402c0ca004005900074283d0309070344c500c0e001c1d481e100010184000c1192102d034010070080d140e40904060207641d4112180b9280c400d4000d8040d5205002c252400e007404000e0000c1500074440051180c00300c0802d07181003070640c0da014ed4446483c0c0340c1705940424007e5085a507050f040100481c0203020344003491242c1414248000c0c04003001d80322007081034034110240701079210084e60641103035055808502c66680c0f00041c90070228824000304100403005a94460140c0c00b102031020780c0c4510178001c24031203020b0041c41c80900000a443c21101e02d402880c1c01140e186200f000d00d00b8060b070b054500765500f03403c0502c01140d00760400c89050071202c4090050652207440f42109003c07060042990300c0100b5902022 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 183127275 1250 183126025 183126037
    0x109020d03030b0a1a0d0b12120a05120a09030f1b0206070f06050403020c0307091517070b0f040e070923031c0e1c0804090f06030206040314010609060803 68
    0x180340c0c03191207806071a119591a41300030420002004c0c0502d02c085140341203a4400940b101e155030800c0801d0400b490201c09462128255078004c0c0003a1010f0b07410b106068021241d0402804428000c1326248640406118828011450300003024400703882c0140a042a5039540802c10084250840f201c0003441d00c42c06c2d917180c040710440d8454802c1d29040c00461881c901c010301d21420003042c0010980c0003e988103102c00102c041c0c500454449407608110b854810510340210103880d0204400e01007142902490b18041d02078852441e221009620164810100d488600400060421403c058038811070380007501c07032074606400b626107051424216151a800003e0200c1108140c0c6295002c000c016003643d145206000b81e8082c005c40a481c1e102b00054482c003a07d00001d0000e10b0422b2002091650b9606c1104181080e0500714034000401c030a08915184542c0c03401c001c80540d40d4400504010351045403e01700c00b14003201c40b142511116846507811394200b040074007120070080700b6180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 183128525 1250 183127275 183127277
    0xf0801061b1a0402091b04170102070c06080a0e010b1003020901030e061503010b180f041a01090c110105040c050114090a03050102030612030a0203030126070e090d020109020d03 78
    0x846075410641d0100c424122040080100c03407404010180401c4a0a4a900ca01c0c0202d401e100035980700080c1c40d0300340190f0b081c054a07201c02000244004690142050b010048442c001030410303140d0768802044481c5900403401040400b03040008664141c003500e0460404c042c001d0041c0311882c4041200984030044040616401103282e1a007070340300e540100c10441c2d40c40111525030804840d104042104812614025401d18007041402e051000d01c0074060a100c66140019907a00e01c43c60040e90f03000381080b0f80020010a10b00118900c412102c2e001e40700c0b115000540030942e00001d000e985136180b14542d5070f4103140401010413810300415080780c0c001e0810b0192243e00c0d0452401c0c2d44103030000071b03900101960001c4103200341540910b10030704081d51015840207819070392075543d000d000d040c0300c0140d000b080140f01e0b8441d01210a10b58488c580d502080040300d0001803418480303141c0000c1e140c1c0030300000300200042c040040c58104034107400204201041078012603814a00310a0143c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 183129775 1250 183128525 183128537
    0x613020105190801060201060b030f01210503042c04151a040e0109060c0810121a070201090c0506040806010e0c0f0a020a0c06030e032703030703020f07060f080106 72
    0x100559009030201c8401ca5110740303900680b89040c0402411907902800741c0c400540c645000807449a0040c01140d008030056840d242c201d030f1900c026040503605030b03071701141896103c41c1d0900020344100050405070030203000581c01781c800315922040d00d00c40b101060b0352602e071035014131000c10703080c5114940388550b207000840c0500300031201c81e406001c0c05582c00c1e00b00e4540040300004681c10740c4203404147c400c45d028440d424948008030754410703090300e841c005040070240170030401d0450b001002c100b6100d1200210203c1c02c2d80801d2005031021960100544d444103c0300080045100c2250041d080840d40241014100310b0081ea0b242030500500e000b0001d01c00101e0440401d020070b440c100c00b54a03c0d10760f510003000600940302d860389801110b00694218021131018040d0044122942c0044000c5052a155000ca0100c900040c2408021030140e542c00083c180c50600080000302c0c020307001010f8140c1e0415642e807600c00c1030ba100c0000c0000313820b0b004100f960b001c10b00504417010f9103003003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 183131025 1250 183129775 183129811
    0x501140a17060f0d05030d1a09130501060e04060b0a05060a0e12150903071103010902010c0f1a0c091c050a02010809030c060708071b0203030307050a030905070924050306 75
    0x81021a1101030380305601540000018042040002c007c1c032000d05524004c1c4110312800031085802c20f0402c103101e0f0322240350000201c1c441c003042107443c0300300e00034000461041d44d20509008078880a0b5820b641982c1c48202a001c503003000b1b04440b0080000740d03000b61a185030072070000c1c9125034410a03648200880360005410240030000302e0740e02c260381402448107040200d103a59403503004000494500a40c0e4510100a140601c01d500801b41c040e181c20181c400143d0f900c0310303c0086048210381c0301481c04403a01400c8640022103104140c0080c07a07554403c0c2140c10465600e541c00c4040c0785403183c402c12540010300224654451a90a0034081c001d6191008054118091310601019038803540e41041501640301d511540078049903100d1320724001a46003030034195628608060b405230b004102190403a4814401085810003903d80054a9a0a951680d0501c000c0da80842a40d649030031500d40c410114070388403a1015072000e00d503075485191501103a100c550040c0000c1c0411012584 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 183132275 1250 183131025 183131029
    0x512160204021917010e181c030b030c19140102100207200906030d0f02030412060c0314040c0504020a0e03030a02070314120909060d0203030c0105010501140a1706 72
    0x8219146a00820954440b0100c440e002601040482c49000080450304408001c900e001604c0f810b03180d0600c181c128980d40c902804502d1708405080d104540724100441b61340c1c0260140001c49481180c0d0003040803002e0400b01440d0a82c40ca21840c842c840103160612852140d10040c809c644800d070303103803481c101104c006034140452140c4107040c7c5400040da4604200e60b900d0b840c4030b0700480d0b15010035403042c00414020001c00403119a07426601900740c6000031801124600125141b51048a00d09a21448100300603404106c08869090b15404943c40080d014040c84007070400001400b50315242c07640314000c007484c0600c5940e01883d0300203460000d191050034028002c08011b001c4170b070745092509009548400d45c0c44180d48200c815049a03440b40350200d40300500c2c07060b211300b01c5d050002d01802c00c6000304010389a5a80514040c000c0001a10144060300120321207200004407503140c90000f400c02034500604c105403402c1000024180c607008803505501403410000280d013030351a900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 183133525 1250 183132275 183132307
    0x101d011206110a0806040c0503090a1b05032b081e0702032107080c1603110304030b09071701110a0c030e0301180312060302010e09041502030c0c0c0d0512 68
    0x302c00e0310703003440012030300c0c96075801c510f400b80110b000355400c00c1441004882100c1c0780c0002d603118001500800c040d50040740012542c2c0d06002d0303101c0b0a42c482d0a658900092806103a08024400a5216004110b000e40c0c0031181c52001e1145046c03000c00303403030152600120703551400c045e00343c0d00d030203c0c0200306468400c0007520b002041c401c405481004054405c054483c1044070781600269203a80050183c0045500359040d02007121070007039204800b903800340d400c121900388034031040c401480300001250b620100743d0b0160000e0b9002d443c403681800d0f0789101c00b428004945116a0600070301003681e1300302d0011140740c542c8500d0220000b051600d421500390701e41da01050f5142d82410144440403288000100400f4469210381207003815044440d800d41d500ea10019000c80c060020740e0384503040504d103290f48540f040e80d02032904641c0c040a203003241c0042d0740ad00080e500100fa8030402c00001c2006104910b81210305991030403c2d42c0d101e5903610f0b50010000d09044005c240a80820211b02c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 183134775 1250 183133525 183133541
    0x50309010b0d0804080c030d0e06180904061407020d0807080621031812030405010f020a0c0609030b01050414010b0a0c05010e010b0418050604060207080702090906101d011206 77
    0x34600035681c9030500f0080c3c52034106000301009800707503202c034602034900090606004071039030312203401c40907000302040041e4120083c0c842c0b814010701c1784010195036001c00c0b5440381c0c3c498880040c06496a540713214a00d6401480c14003075501802c040c0c0003068005000c240e0291083c50440c04583c3c030703003000c40d0710210b14111164061855242003601500080043d00c0c050307101d034000d04290600c0c0401c000b030984048501030f240350810801404a54404e2480002d00c40043c011604040d00383e564940c102001d5500c02e0b000500000010320401c0807040c1c81d14018103086a00303000004400d00c01001501040c42860f07140c07980040c021041034020b6003100046500400200203040000303803040c0c080c258002c1c01c140f00d82c3c03801c9014403200070072040405009030800020302040d9502d507903c41c000c0d4041c0c0c41c1690400b5040c0100e0006030f4038a4041440b03619008007500560400304441020000d0300c2c1c2111040d007410f01c807800d12030342c00c50940d1811181c04003803200b80c80d90383e402d240340145440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 183136025 1250 183134775 183134779
    0x1203090506040614060303040b0f030919050309030c06030f0a0902010908150f010605190309020d06051305060708091b040204240e01051306030207020f0a06030b04050a09020a0303050309010b 84
    0x801c100700601545a02130580c0b100b005142408036518403080540701c0c030036401800030184c818003450748099481005545e0007002c0108030385407400030b0036502000c0031a00740d0882c0c06030310000c0c5e10310550406000c865050041070b40c803a419400c0110144103010030050180e0002959500c0490642e0710803018400144030700001d4950582200040001c00c1600303c0c0c050b5019141d50300000741d2540b00310106c60b8404517406200164604184045002e000502416a840054014050041901441840d00030b0650102c4002e08100b9803620038200700d0000c00300c00502c007200d0104100110041107803041d0b8068036048401d940c190713100190080c040d0b9004500300003030840310186822151f203030a00c0d0354141034580701c3c510200d26004441903c00c03881c07100f40303034604402304020841c000d402600c0442c0c0f0040078110181c510300007044600b0030341e07400a40000e0703c0340380380c00303907818588034181d004441c0c6401400b030204590003040091060744001010040c0000014186100c203501c41d0142c5440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 183137275 1250 183136025 183136033
    0x41802060a09060816050a12060f0e0a0b0909211b06100b131502240a180f0318080106030807060f0218040c05092e09080a12030905 58
    0x10592009145154078043c000204500901140a24216604906442100c0c0d03070741624043d00315208403a040c0100c5126488141c0f40d5034003068407114400404007400c01211000428a05504003d040d41c500c00d1615001c1d0411b0130500ca0401400f10340d1b25842a0300c840d00094105101e0b0420b40349220300d01d250306c0b804091411078880c001e00404e02e680500c00d04807410f019151100b250304441d04c503140e4070140740b119000c020028290040308080031703da1180151452172580a1521450024080c2840401604001001401141441303441820b10200140031146801a502c403442824540c0003d000d000c0441d8908680307030592036951005c0c103c10340080c40510b58038500602c5c240c024103030444500d410800c2500d4602c0d510300c242c82c0149200d001407012883c1c60401d010042214140d040200030b820440c0c2e40b626220b25050080c400c034440c403041d0b4031644003d41c0354110003000c6410820803490711030410100800003610504030f604540c640700c0c10310b641311040d401440c1c1c28400805a001e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 183138525 1250 183137275 183137287
    0x60d020a09020a08061005120415020a0207180c051e09130506040507080402031906200d0b0f01170603010615030b01020606030d09170709020f0c010c0309020f04180206 74
    0x2000ba000351000c1d100c0e030740350445140c4034802048003200d18a1306a400144045c07100000c1c2032010320909401c140903410f040088214403a000d407c0e0381c84004400c3c05640f2408e400c118100010b0900408100050400c0200c0200301000418500c2445200300b1047d41412000032803c40c4001268050a0010442c071b084854140225018140031148544142c1c5800d00042516004041c0e10b44196030003000391a02c902d48440e40a524007440101b55415903951001100c1b0a100882c01400f80d03a0306a505c5c1d4a0300b103026000b00c1a40c82010074540140c4080c0c003d4080350360050800b070700c110f40540c4100816500c1d100440d00410b8168855403032041c40c50318042c4481c6d0103911001446c402039094882d5030359400285562400300b040c6103000550225410000c40c44c14041074201110b5800c151910581d840d010325007641c000e940c21028106000a80281c140824883d03407808490314201444070030600c0d000600c0845404405500940d25a5680c2d9407a46001802c0b203005035008001e180c642d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 183139775 1250 183138525 183138539
    0x1a04090213030c241112030901060509092b0309020402070f0311061b090a05120f0607030b0604061101090b0a0e0106050a18022802061509100905060d020a 68
    0x8007244070640e01c0741d010307803004140b010508250040c4110700416040302144440011188041e00395102d807018050901400085c05545e0000d5004020440021619509040403c0481c0f1005441c0d1046076001d401a4000d50201d0120301c0b126141380940224074149190003079002d000c02c030b10029445031002900710300b00401c2e07a0300b0401003070103559408580700c0c840010303954540b41a80c3ca5144030104940e040c0d0008005d4004285608010b030081154540d940c020469401d070010b03501416800140d50701000d107030100802c0e617000405180501200060381c000c03409500c5640202420007504402405103444250468031810b5840300d060755103860030001440042c000d0f010012001c2d400d0000004031841e11400d001c0c180c1c2d241c11400502010800801d03402075100050b0316043e4502005103c1c090355900c00d0b034640401c2c1c5500070b40f41610340119500120142c400d10103105000ba00148104c403030080041c5402c0c5c418000c0c00265039103440000864800c546140250b00002d000c0d004a900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 183141025 1250 183139775 183139807
    0xa0b0a03050a1a010e040b0d080304051e280c03120c15020a051c11030f150d03021c0201020c0d050903060601020105010324060911030f01050108010f1a040902 70
    0x6080c600700402c1071882203030703d140500800861050001e035580c0880307045494550310080c49100c0051034818040c1c0f01d955485000d4108035070a42e0550009100c00400c05401c2c01c03031401e078619940240c000741c0000d6078402c024003548a0b010010401c1d5183e80b0b4100300c0700001c0c440207160800100e11248400100040900102d030000700d9400d642d140301c00e00c410312103000307443c4400259111039003021108a41190340da25181d4090300701c00d4503902c1c00c0c2c800c110b600000350302079000c010700381d4003600d000c50000500c04000901070b0700804880c000c130404250f02040307d4803108040d0115284520148000701c1c064050034a030f0038034600524400c29505a00300e40104604081603041d94815a2040d006a0072035500348000341a03106880c4080184080b440108445000d01030b100042094480361034000321119075030701120090000044c0100514814283ca00512091904901540c107107880b004403004240705072110010045800e5515041020030f64020300303810345046403911355861300c2d6455 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 183142275 1250 183141025 183141031
    0x4081309050403110f070b03130c0303050307081308090d050a02040e03040612060b0318030717030405190305160f0b0a02040f080106080c010e010314011401020c0405040b04020405060a0b0a0305 85
    0x108070707a410015054840071403090345c442c1c0c0c41405400c03120b1421a045110340e100070541e4441c1d80c803001c9480001090b07a1084005035001c1d03907031561280b0b170058001e05030020142c90241444201901720000070300c038030201c3c0d1008800790f034018440c55051510a160070008007000394400c1c1802e01820380071000101030800c44040742c0d1800600b040b5003600c081207807020b001302c88a1110400004038103000030020f01d400810144212440c000e4291a030b51000800d150072001000000410300050100030442c441000045088002d0108850307a0054147e1080c48030003100385941c0010f12090201000d82090a80e4000281100078034101040c1002540140140100c00300c07668800b1403214814410a000e680c2540c0c014030b04500c40758015500141000c000301e04243d03c4000d2013100e2079010940b45d00a048040e0302c000045d0446001900f0107180c0182c4a020303d01c0c2c01c007040b01189200440c60341080d0155800602c580380c00c0c0210700b4040464015912036031001038844007480d4550701241c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 183143525 1250 183142275 183142277
    0xe0a06050a290d020d050706090612020a0c0314040302031203040302071a0301050d060e0d0c03030c140d0209010905060307020703030e060304021e030f0703030c051204120b04081309050403 83
    0x2000742d940b003035040100d0003254000c0188001d10a481207107414001d14078201c59000500c9050b241c82c541d40c65510344031b000d800403000502050300030004250820540596055245400d6051103502440100710f158068805020424501c10400500580c5070807200034503000750680e140603590180b014000e0384140e8045005215030900050344004e0b05400101c401d54810721540303164a08010055940403051044e40c1e555910080500055420420903080340e8440c0c6407502c0e001d5160501804480b4a941c41c1760500c2600c50b040022075280d981140e21009100c040180c40c0d0148034012250240e19800050f0085000003d211916400143c5041203e101c1e03900c08100018103c24488035000503540290041c070070380580400e19101000108000602504440d9500340f40c1700c070301d4501841d641c001e40c04503044150311030074404107200c4001d682d0035010b9000e2030640380c069200c011340701600c005001c0b1250400401e00304085101103400310440c1c080d101420310745a11000c0300501c01610110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 183144775 1250 183143525 183143531
    0xf020a050a060815040f14090706030e0a060f02040e07090f0801090b15010c02031c08090a0203190f0609060509010f050c0307110f010603050309031002040302060f0d0e0a06050a 78
    0x3a840c6401d210794010b03036801d551503070b40c1c0d03486044c0529050700705001e549a029850311a0801059aa403140802111003a034541a00341000c0f0501c1d8100b030411303000402050f040c20280b070102000098244569a07100d40b00154041015103000020700858126440c120044410f018455030f1100e0407100b5150380320107803180c49030368140c182e00b21021a48010300e12400040001c00341c3c502c0c450082a44181810064003025095002a0610304284400c000c0c0d01d110003058240b0590240703c1b554401e188100400250441d500000c0e92030a004036040c0d140503401c92032804002c4140b100a00d03641d4483d1060060702068540034014040c1154079221540c6803003a00c4d00c00f0b80050144902581c80e1400607491512810320407a01c2111000c0b40381d249200c0c0080800001009110340700045000e5006141c5810342c0b0010181889856142003a0b8980144400e1002d48d170b5410898100d00f11042040e581d880001c1486000340200c684e0b041407a002c1c40081105107c2e81e90400d40c4142541c907420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 183146025 1250 183144775 183144779
    0x612010e0d03050910051b1b0f030d0608190b04081c0204210b0402060901020a080c0303150a1a090a080f101104030b06130b060a020a051908090907050f070f020a 71
    0x241c42210002c07101d244807c101c502078501d025140400030000c60071042c00d820a660381c900c00135031800171701807040b400a5000240e10201c0c65040d1203100060522000a49040b05504c1c907141c0318030240307560240206103220302003004c00c0015170895034810340c100f40c07001308003120f02c0b0558020741252140507400c000404202c9190300d00316440d1a09154440c4102031591620703028050380d5003240c031610741584616200080801e0041015001d482019801950349141c8940411042100110000c1c0101c0c00b6220030300620304500102c110f40b08000a1046d1034080d09400520f090080ba4000ea601d801050fa07078030b00002012800c0c584424035501e0030b003c5044805015a42442244006803d03203136490042052490070707849080d031a500c459004030302d0a01240009a05a10a11048026070b0000d0b4000003040400d200c100789504d600ca04801c1101145e440705500c611802030700a104004080000381068041c1040d5410080203c000f90349401d02c1c0d28007402201d40d045000d901c150520000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 183147275 1250 183146025 183146053
    0x3180b0403120b030604060b01090f03061a0307051507020102011b050d0501050913030309050c040510032f091e0703020406030605120a0b15060a1707030905060612010e0d030509 78
    0x355103d208005401081c00c0c1d5603d45840004103022083c090401c080340c6c0e400a9128400601c0d10081c50240800185c80c200301300604c4070512302265604c4c042c0c0c020510070842d41c0e0b101d08100408040c1815519550072046c40102d004083d40c00082400c5c0800341030140f1810b038001d01410200c5104202040b1070f0342c880b070402541c1c10080300d0b28002c0d07002c84a1903200003031003500300128003407103082210092480000010140d501c01c4503036210810758400104180090b00212090803143e4402d014008503c6e1004001c0c001c042044203800ba0b6018000300c2d034490100703601c0b2090358503c41d00c2c3c80d00c1c0303003011100200030390722512450000070708000001c105440c180f9005240d0214030001000d422603180d03034001c0d0800c002030000258121244500350700d611154010201d12040ba13a51102c2e02c106071144180044002c0e00700020145403a02c0400080e0002500c80c3d0080801c0343e0826039854084202c5014000802e54285940502003000c526a50940c100c0c500406001e8281c0700f80004e9100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 183148525 1250 183147275 183147281
    0x2060c0d110f0903012f0a11010c05210c07350c011119030c14070606061710060e13020c010b0a12080f0f041d0105150a0e060a03180b040312 62
    0x108000c40c03a201071b43c0b0724034003801003030090003801e0310750510500302d000b1421032600315100d0810321400304400041c1403002c403c080340401104c11080004108504140c0c446081502828000600c40e803424804403020240001e01e10100f40d4052558100c0c45450b000705048c1c51f004943c60702e44a60900f402000080e5064081c2d68200720301d0f03c00800903502100088000c1c00b080b0010405220442205070681e47c0f0b00b9004040c071038080c807030200f4043e00d8840007c0c0001c40c0c0c4480d4000c00030031102401040942d50104500f00c801c5442c6c8203000014400020f00a00352044035030041030310020310003842080641000032802d00c201c071103a2030a039484038000c04d080e1007020b00404c4441d0800c00c100c4d084054101400322a0030301100e103410b254841c0004901c6002c80e015401c1d1500d40100104074074504698003a44104502c18004d0800e40e01d014080e1801c82121400c40c461345001c2a003440c1030344240c0c498a1124204450850408042d0421045061041d10103a000030f03100e9007500c2c070300c5600e40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 183149775 1250 183148525 183148571
    0x4031e05010b0d111c0209010f08100c0f1404120b041e0201170c090a0303021b1504090216020409031106130f030c031107060f020f0d02060c0d110f090301 68
    0xc0001c402100039420484221500410a006076178410b1420700541c664007030722400703000c2070300c4580d8900f424500d12a15007992495080e1741c1d181400510200c0d244d1114203c090003000c0d01b0030340f0140c1000b040309466801175400040c540001021028140520081240e02980c02a0306011180e1048080c8140170040c1e004060b012030801842010010407940c0110b522218004010b4201440b02c0300040115281d603006400607030180e201443c800d502400c1310940c80c201240e2901241e5200c0c610001580514444e5085036030340070130880e030030f40d480e104107043d69540103004000030030b035034900600502002900103c81c0d208070300c00204030030110308020410680091440038581d40550f0102c4100740d0744075088003081031680e95103089883c20481e03203002c1d14103921074010004031341c1c0c00207243c800860400d44482d8040040741c50344d50340204e07840b034124480c504026528140d4003601c3c005010342c443d02038030b100c80010b1000402d50660015207180d03c0110000c3c01500c01c0207014100d200d0f460 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 183151025 1250 183149775 183149783
    0x12070506031b07050a030503070e1f050d02040803160c09090206040302040b0609042906040b0d1d0a060507120b090105040c0201090c080d080f0c030109020f04031e05010b0d 76
    0x70008505894001410059180c6518090070b140503070341d0351414104500004220045100071040c4a9110703008050714007220000e860444d00608420225800c111413540f581c0203020000540f183c00014540460700900700840132a559a84103000d000c010042404080c0c840043d044800320f81c0030040c1c050128100e400429040c1090700f10740030080101170700034825500c804200a858020b842e24080d901e080b109411810481c025107449500320b10702c180783c03807074030038507040006100030a00f55056a00c0c0045000c400641c1f2040308400b502a80800b400d80b032441d200300c0f00c040081014942280348180c4803075a41013800107000346001c041c5c2d1b90350f1149a03070007a4500010f011509090388001d81021052002184180b4941c0b14440d1102d4503400000302074100450b06002e80c0c0d00118100d811040314110040189040251031032980410b0040c0303500035400181204000a0a400303030f9000c0c40c0c00401c400401c5050440005a104100c0703021502c0d5401d1840b1042e0a15203140220940c50308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 183152275 1250 183151025 183151027
    0x7020309090c0417010e1b0a03062301030c1e030b0703050c0f0a0809010b0a06081605120a0b03070e100513110403030c050601080601030215181203040512070506 71
    0x2600080048180c1c004040c07030300000d0140000188010300e4001301940c2d0149500014a043c00c03820030b00d050a240304542507410410080c00007081d10f58003510b9003141c0d0085000910b9040f2407040c5a024842e501e2480e10f5210180008024003c541c110281290400741103528070800009032007001c440640310103410403405000040819000381c100d00e50108210102030303d010120000d8810542000720303914001944a4100940c040d424401c0105640080743d4905100b49006402810f910004003000701203e0000ca0800300107015030240c84280c1c6104020440d2441c1035015100101013480c10035102e0b00c14400000741040300070701c00602648040095142490134002800700c808241c065804c80555100d03001018406050050b1014612959a8030551200d82c2011032600c07006030008034064000000400060b0303651511040c81120440b01a81c403004002003000090340701c81003003500140680d80d00c03860000c2c084000c3c000c1c0c8100704e950b0104e0300081c20100d0754a1506000f50381d000070b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 183153525 1250 183152275 183152287
    0x2070507062601030b07031512060506190303051b01021602190602030412050708030f0703092304091b03080306040623120f1b09010509040f121107240206070203 71
    0xa40c00743c6050703011185040c041690880201c207002800080d0b840b080139010111464000c104074be010301a00024100d038440700e086d05035142d030618040288401424094006181012a80207007202d0300503c0604000715210702c44000380f446644c0241004034031076540034041c1003030300c100d004001381540d1407a4010b50500d828491030b042e24403803c02d07040d6103e00c610100000d21800c00c10007040903001103080b07191200440c0c900604110410340211000c01c0c0e0201010301d2980726800d0007128528210707400309000303419041450004c420303140c1c441d1150101d010003109100d001401103010720303825901040210364459448400c02244030040d13203800200c440584641c50451082e184020510381a135020003c1d85022520341480302e00640300310190380c0325503141440d02200440c0103010030380c2c61141c0707440c10741d44e110b00c142d1443e00300a01c030001680361145682c0c412102c61024410001c12100540d40315540d1125183c4403091160603006203061110046101180141c0112030341d400035805c0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 183154775 1250 183153525 183153533
    0xa050108150109110405060301080304050f0a150315350c010819020c030d0609060501050306060304060905010605120a0b01051503040609050319110c0a0506120402130207050706260103 81
    0x602040c0401d840074045c0001308280c0e441c038008500074004a8000e5555518041c107001e0350701219440c5a10400c110101040100c01000501400d8142c0f440c001980700190b00a100a64005400c25400c00141142c13070100c8588480310017241e005d0032070368411b030642d4480e02641e0320091001c240d40015849400b04903200000804000d00c0c1603004805424405025041d61441c1c00c00888503c00580300c640411007041c0318801c4c02c01408080c43d140c2d156241c0f00b030102d126444064002001c2a54488070f41062045c00c0d8420000703400000e110f0403161510fa1006566200f43c4002510248100800001c00745446800c40711b00500008000741181d4894a54900510340004140e0f514002002900c1c04492000040d81c107100d00d58444500498031041498030301a00079200c18040c0d64903150a11085d5100c40540e40c10115107045503a0303a5807148003080605034001c0b48100c55500100e4080108040802d018050f02d540360f0710345403012540004943d06c2039804070340e41f4902101c00d0040c0041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 183156025 1250 183154775 183154781
    0x2040f0303110307051c0806060a0f05071104022110080604030f1e0f08092a0a0e011d0f071209060b090109020a0329280902030a050108150109 63
    0x202e0001581d0610300c0c15102c0d1402e081076054010040481c02c4022214503400c00031550300200280c1d4098104025050b01420303802100400b84140030001c80c031501040543d8504541040015006540303809003210540030440e03c80050320306c4459081c0001c3d0340070301030f0f46a42c0c04844921005140c1c0c0d803603a850595085015940480030005240b45c1c5090750150720641984c480340c0c603565100382c602000e10050940c80003510b403135456005404105550100c04441a54800040c2c82140d21160f1001c0011030048940d488002204c01c031000004040850401220010111400c0d10a844d9295a0300d811040d0f000c41d5640c0100d090303030703c04200038082940034a100c1c503c100c40020710350740914001042d0386c0b802d0744641081c640018402c801f0ba5454001c2800001649022803015101d081c1500c440c003d026120074040c20310700c0c80ea03001002c0150410145080c9441440c0c207141d403204c28081c0650b0089403080301d003500308000090b1803100043c00107104207200d80e0034000c90b400c000b140b03406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 183157275 1250 183156025 183156047
    0x1d010e0118030309050108060105090312160c09050405010b0102060f010e0a090f11010e040e25120609060c0804030e040905030c03160b060a050d0b091903050306040b0402040f0303 79
    0x10840001295203807101000644006140240c0b50144038a1801c4001800c4007001010300d810000284045100b41c1c030b0020301080c80144410000c4d4a9032602c0f241c12069107280d5802401c400c03801c840c0010030b20880d0344000e014501940c0240f054101c0d403401680e5440b4142c5007080b17260b81c0c030001005040b9030102c01540003881c2220114030900c05888003c000010784400f03a40806a084e208101c940e0881c241002d088002d0301d00b84010602a40d0a91301d6803044403d1000207241c418450025544060000f4058500100c00071104545814840e005150088044034580d18041e01140d150340035075042803140d94541e980c201031040f54818030001d84543ea500b26010301c418007580e942a1000e1000d812503900b2400e812900f81809d04200c1e5034802d0180038280140e40340704091001751201d015000d4225040081d14159840d840400c620f030044a1042060714003605d0401001c0690010095004140c00c032000d03c00c40c651141040101d100e1031180c600d110f6158101000001e01035511151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 183158525 1250 183157275 183157277
    0x10807180f02030a020d140903071502070b040309061d060409150b04060c0611090d0b041109010b04241e030b090c0307020d020303040b150303091306050f011d010e01 73
    0x80c400d441c03949007100ba038000303030b50350070b199030700405c1300c01080c1894825513046c1100190400c4180c00c1901c00c00d44c59105900c03001e00b0030181c00107128007455035501110900e41d440000340308a482c05090042004002e070140d44001180b6000b4411b201c0b00501514154800c02804907240c20f140c802e02c54014500c200031140084900640021080751100240c40281955164010304450300c0c03504000300c8400e1254280d90318014070001c0c3c01c076203d00d00c00c0b4480e030f0350101c8854102e85a9042c4403400c18500c040840e480104c0e01e0000c01d0100c5010040c004985095031024203851001c045907014005800d80310340000c170181c100743c1021400e52041190300000303007800250754007000f000c200c890300704449002d11048000148240070340e040082841e40b00071803001d14198201540c1d054940c4001600c0c2c004410040084000c107030383d05008580c05090010042c4240b01c040000600280c40d1510800c0d10a5070080e00400095002d03503803094031040c110802151038145034005607406100120a14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 183159775 1250 183158525 183158531
    0xf0507050a060e030408070902120105190f03060b040e01091703270106050a0605070b060f040e0f0d02061b031b04050a0314010c05070b070e01030e010c030605030d0801080718 77
    0x2280b59403162a4000e0044005940e0b114242024145008801c0e84100e03449481081058000e41c985000d45064880071283c40c102ca0151102010407131030780c3c2c1c01144443d40d0221001040100c641d010031907402c0162001e2041c0e0f141c844107542200c2901e03c01622807800452002c003890200320045a12a16001c1180810ba0b40f800c680607a603824107000c0030640c3c0d90342c8024001071030244503010007481c0c54541140740c41c44c1540c5240803410050031242c011005040b0320095640d840c1c2146280c424030b11708440001d0301d941a86a0740c0c009200c04d2102500401300810a680040c1c9411641c00071042d40309032450300d602000c118841c000c1c01c03a60000303060610010800b5540c1c90182c0e0015400384024004071300107007259030708441c20500c0175014000200b00120010382e079542120381c00016070038490000144100140c01030b055000d0710802c69460100140425a050341c09141030f65019070850b0f060259a40c0e0640c2d082c002805191156071003440104081ea603010080800b00000300004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 183161025 1250 183159775 183159793
    0x11e051614160f05070f081c05040504020313060b0109050105341b050915040203071218030305130305160804050406090506030c1e010f0c020603070503040302060f04030f050705 78
    0x2c050341d26014030031108100d0b00c0c588a418001c04215000280c21200e01241060b840c01042a1b03035080d0801340101c49208400d41d244003280034006031402084098001d65a0b841c140280701c1001c810b9080483c0e05620b4000c030031405500c1030b40c41c5800e8130010784800b80b804070f094280c11004201224a91080c9964809008440d04020100c041d02c0c2d118040741c6000d000c04070500c1d4002e00070307604843c2c022641c040070003485e50910746080c415120192801641c0780ca842000b25085030454034a000c3c2c0604140b00c60694810b08092410b05070b010b43d0b010441078540d00c800131040201c22402400040b014448002e00d03003401c2035200c070103a118000c034500c1c00b43d680001c00c09446c0305034002e8040c16920380c2013000505051011154000d4101e40a0400029010b08101500110003410f0304210301c41c070401c442d407802040102ca5541e0010440b03a101c2c501941c0c020216482110200c006004640100e841522580e0215008030713419147e504803456405411121500300d1b800541c2c10b44101452 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 183162275 1250 183161025 183161047
    0x1701020d020c2d0a0f1407150e0603010b0d110c0d08070f0e030607120902060c030a0e010912020d06110c0a020a060c0510020a050405090702011e051614 67
    0x2c10340000c0071000340c0000c002ca101e80b100b440304034031081c0c042c494840240000701403020034001c0816070311103551040c200d124203101205203482082429980b00b548400300c2c0d09000512400101d2400b0b6031014005510102480058007003881441c0d00c0c100d0500484500c0f4803145c000b000c621402d03040703841c142030415001d1807034411030030781c0400400d1800044c41038007907000380c603910900f19504044a081c0d0102c40400e545140c002d10101c1001000c003c0760108034103035040380301c8c2d080d0000c0030251201d41400c0c440ba125402078007410040345580c64041c9195002c1c0b40210203c0d6100354801d1901d00894080c0b00804241038412a1032642d102c0074002030142d00d101406003145180028602c0810728030520600840c0398200400f4031088001b03110000f40001800041e600c0306410141c1c81d540348010a0f03640380250b40040e9488150709080112041d07055000079801c07849a00c03428041f254506a18084030416214030004501804809600e180070300c1c4400e91040d00704410602e49401c80c0303c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 183163525 1250 183162275 183162277
    0x15070501110a030b040b153103030201060f0603060810091a0a0b010f0e060d09110d0302060a0f02070b0f0613060f0e1015180b130819020108011701020d02 68
    0x22440700480d43e20b007201341940c100380c400c6a0f00c0101c10b4400705440060a03203184440e00031041200134034500812003e6010741d2031000010110b000406a40c8103c0c0c0324036010b0302030b2000d400748220607210381d080010b00c0d52090217454222405030700500f00c030302d914400c00300141140200c00da4a08491101c1c803110208400d4801d4414018514006000f00a00c4001040c5480821100c1c00300b12170070300281d05540d2040e040390901c1810000019a100c52031034407404c903940000429070300c049070440740c101385600414000d216801c401020848110303a0320003102280100c04000c1c0044882c100000c600c620035031034071038000400a20203d5407204407444041924525080072805aa00f81800c00c061031005851980000c88610310b00d08003420181d9a010201e90010001d040004410101309850041d0a4403805440c503800900da03500c10503000119590840e2140305e5680c81480100740f6281552042042c10a40c165140705031646881591100d100c401c05800c40a55800c200652030f040040c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 183164775 1250 183163525 183163537
    0x190e160b07060e060106110c031209040f0b06071118090a03032a050406031409060411060c0d09050108130b150307080a20060310060309230c0a141507050111 69
    0x61f685079912607072028030900f0100641145c9002e45c2c02003007400c08505046090303a80061040d240018020607100b8400068000c440c1c40e40d412045c00500320b400e006101112120050301a02e0031580d0b0402c0d8440d8a1907140d08981444013900b0603040c3c800041d200360005035040030302081c942c001c1804c1034060001c0002005412001c50300010301042044c1d0503005404240c101195034605628050b10004e454400061004084401c0101c9030b411540d0789005581c080c02403803007100c0b4201c0c40504040c2020016000e501d02080310540003510b001c124809054400703900080040454171018107200156000b101002e41c103000b04800401c404008101e03400160b80103611021004c4412040c4d00c2c202d9000030702c0030f40504402c004100820000002da00111006460005240304160801c040c440c1e01603003000c12740710303541c1070403608405e40050040c425201c2258160007265884503403801d0b0140407109640c00282040f000c40d02003400b040030b001020f01a000120f154841c17941040d13160b0b8061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 183166025 1250 183164775 183164777
    0x20a0318080d18090207080706090515010b0a03050a051e06030715020c09010602030c03030c0304030302040b07030309050d020105061516050105090604031806050f09030a0605190e160b07060e060106 87
    0x103000342c2600a48010f58000213240b01c4408502e05600368170303401c12501c0344400142c100340c1c5800e510302c1000008c203d000d82c5540d04018031009035840d1003580c401c0394004010100000d040801103800200c091045900031814100041d60715155000d00c00d0240c18010031103a80344c041c2100015005542c00d0100c0c407034500700e5014040c18941d000812a12315010b80042d0219881404290404140007080744e40005034211515225515840e04502a100c0c58000e40d041d6030022416604058041c1c2002c81620310940965041e0b80c1c002b0002c900700e58007100c04a501c5880040280c01e2164000d00400c031041115007080801070f201d07216903094074030555280c56a07a00503070420050550009104c1d891107581c4040044440c90070000601030300901406403001000003d02c6040395a08121200525034041000c1c003141c90601e041c192100911690402c4150808600008407c8080340c403686460110b2448810241000c1c0f49482c160000102150465900c1b1090781411100300036840c002c04803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 183167275 1250 183166025 183166037
    0x130f1116060e0606030604150902220f2a02010905070608040308011d070503060d0209010602030a0e03010b03060403050c1509101b020c1017040f0209010510020a0318080d 75
    0xa49044001c079100c1d40442e01c1550070402c140005a5404a00282c10a40010340380070742241e030440000007400308420080d484002d0480386825081741d01595030282005001c00c01007583d504800d4005e03900040103100f0800d01403480180c10b800d003070b48048600c078094400000c0c00001c964030030345003a005401200208031900d00300001c16a0000525024115420800c9485203d6490b0f80f1a802006000340c0188240480020705a4071032021400e0b1031500140355075900d59640c600079480f5440309090600040d5040c0703001c0040d0505005481140340060020519540d50340c90868064110040c1580c182c041c44040600094204040c180510001005040c3d803e2020800e00700316284d800c00390fa104007140c5c030381e00106a001306846100e620b05440c0f54036500b000d80300c00c80c1c5011182e005403010000ac4d03800d0005200070165a15000387c42914240401e1743ca4104028414820b0310b408001070748488440c1c0300103841003130f41d001071b81c0c1e5a0b403030003035441e4030fa80409003000107602c441e9002801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 183168525 1250 183167275 183167317
    0x3040602070b0615160305071a0108010e01020c070504110418020315010806031f1518060602010608060103031128150c050901140c01020403080a0206090c130f11 71
    0x14526402c2504444121400c1d020143e690403090100d0043c803100503881c1e0b000c075500d03400780b501910031982c6007648448007074010354045600e074070040320a01890303246610300303d1010410f6505108490340b88140200500000386080208000b8154a000d004241030045c4000030702c01c07180520400740e0862000c03001d41c0307901d0205801055000b04c44501070400c544241070007010303240802c81d207414042ca00f0f6094504100b03865000b01803c1601008514844c90380030003d0102c900c1a5a45055082c0c50401c0c00381a6486904034260761582c0160401c0d030708801c0c01000001d000da090401582940000d8900c8580101200005490030440e0b00c00244800f80f40d000c100701c800f05d2164200845044100603101d644040200507000710b0030b01ca4144011341800d0b203040c0700c0075030580702c202d503006000f5503070703a0388a1a10540700e402038030610015226050110343c202501281e900b44034000130302400c110020102d02000605224042d0034040c9503030305644005002d5000091080e04064071004011113 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 183169775 1250 183168525 183168533
    0x30c010c080115090b0304060507021204080109020a050d080306090a11040311190305070b0a11010507020d080c04080307020409080702030a0303051023010323090601140102010209030a020919020304060207 90
    0x4040300b032440f810490007140c24001c61640310b0541e5006034028200185d80e07640ea0b8820303881c0800c00c481c984462036001c0350015402605400c1016841d10030303280c50100584c0d41e01800010004c11800a282003024400204207081112029503c104e6421000c50004400e880341c4d846070f44103800546e00340c20803400886039410034030700c100c005050300b5882c0c804a910355110700b9111407142c0541b100404001900822003807040803142e4503141440000c0115041a01001c0d41d5001d6808000003c00d000100184a0000724003d81d4200c50003407000d10710788041507082000605d00c4400803125a5814405400543c4040000c003601920940340012603092941c28042000103503413104200041d00070301816402188120305c8020700e402c0c200401e02c80512200b011001204040c1062101c941204010b2031103000510b060403110166403034483c10307591100480c00e074840c1c1e54005070903134010f0382440b006042180049500c00400c00320708011218200ca00401e0b81d00994091fa603180e00070411100344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 183171025 1250 183169775 183169799
    0x1509010519090506040e0f030a0f0207030c0303050a03021b1e03040302010917010603020d08090f12030316050c01090c0509060402090d0b040804050d050d020c01020c0607080903030c010c0801 84
    0x540022648141c0014140048031100312540c0036000760b058485000c00e040351502d030003c3ca04800c400058441042508000e40d0345d0350820000c040000b004580302d089880e00226009080d6904a06000400d6081d03490680d0075078003190401c410181c0c2000300b1101d010b500c69001c046001d010001d0060480b00011000c4503040804107400700750000c004c1000141e0b0017124507801c0f01c0088000190240b5000c4030603004000d182e20180d00000c0c42e15880f010400a01c1c010300b9200c80c104d0349048141d0384917060144e18401e4203580310b2154020400f14024840d081c00954856100746022440e010803c040d0b04d0035034203480380484014003504003e2126281040f001a800300e0250f400310b0030040c010001558114454801414414020700400c09029048080b80c001d0600135020705440f95441c5803140c0e880170a111000014050301a80d0740c1c40d07605c0410208500b1030001c0860342483c1c0340d616895a81e50100340495814401000307043c440c1002805000101c200b10384507000d41c1c5d85441c40e1a007035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 183172275 1250 183171025 183171029
    0xc030c0d0911010e0604080c0904080903070b0a09140906060d0b03160314060702062703070c03020414010302030618070f030f05070603020f3001080c010201200405040c09030b150901 80
    0x402d175014403081c81515000901c90540800888486046032601d0410070928458015000d82500a48401007a110030110040c80d002400c0e903503121406540d403110b2190b10420030301d000c2c3e01c030855601140b000d1610101501100e030180300002002032542000a1a01e0f100482000000f21044020030a106a00b19411402080d0002600c001e160001d0000d440342d1004005080c5040c43c001c84e4802450140a00e0b48116404401c0301c0e07540046080c64100d404440c40202e1103141403c521180320b09140b440a070480c1d50140080c6556110284402c02102a9416a207054031036640006640d00c2e0f4049201c0040d4080d084861141c051403d085042c001240c101c801410300400034810243c000308104e964050504c08000309080340040e903a43c000c0490321328420501e018000100e1034031804640450303025402d0300200114071805040c1800540801801020340c4010f02c07040140b0700380b50300042c10b9101e40e03207000a01240c4075038230301d010030360260f4015000410306602020582010b401c6140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 183173525 1250 183172275 183172279
    0xe1005250c080f15011a0c01050906060f030f0c130f0f0b0306060901030c0506130e0702101a010903021903080c030307030c090b031906050411090a0b070b0c030c0d0911010e 76
    0x44c5070314251200c2461604103105240e01035a10040682034031013050244e442100810b0020f0101d810300740c406c1944e40c081030350194070030110010052541e00c0c0000b1b1180142e8688005440081151420060012011a202400291160082c602c2100c09100e002100c44104030001a0210290241407801d90000e09180c0580b00d030f20700501c0030802c82901c24080f2501251803954032103c114444512495036801540d611b04598141302c1d074140c000c1500844400c2c3d03813200b0020200c1450104840c0d002002109000c281104824409400c0001e6040507a41542d0f00840985550380e541880b60751080c103070079245800c08000d0040c40b690501130f0001a0f030580c07801305201414802c0c9406030384005041e81455040700300c8050148822500004003d2400500800c40e40d203248003a031101e540700e828201d104e00b40a040c0820400549030540b40000d4021603c0a185d070341c1e00d400c0c1800c1d41c5c0003504080150f0000c0c400c0000e115120701030244c1140c492172108242e03402000000d0301c400d0300d20344664 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 183174775 1250 183173525 183173533
    0x180102030609010e040c03060c0809060f2403031e0d0e060105100c1403040b040311030601030f080a0903080d0204060206280902011707020102190e1005250c080f 71
    0xd41c0d691103a01c0d081c19200030b039290401549552400200c50596a0b0004050740c1c2081d00d00070384141c211100b940303d080d200054500f1a5078060151055031402c030340407054041c2148940264025000412841d403202078105e03454030108503038030141d0340516010104600c0001030310030781c4480079005000c41c0742c0c40c0c80000e14581d41004001484428681c1060082000108a030030a0245403101d1094141600058940e01e035129080124240e00601060303a106411704c1e0100064200011404d048030b400117413941c0200c109076600121030b440744119108200d180303a000300100b040c8500600c0c5c0c1541f000d40060f6224902440a400e00b00300800c0000d81345100000c403416108900140c0111903102c45000400800c00e1005035080440c820008600b0074204c42007240d41074055000b0701e0354034885103040e101d5808540d070440e000307004040195000007203821080c0806009034040c0602c400f01e02c0101181c0f00181e02321500b40c2107510030076500e6002a003002c000d21401804003a1449038444050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 183176025 1250 183174775 183174781
    0x503150105031f1811040b010206090a0602070302070803040f06030605030c1e03031213030809030c07090c050f0a0f030c030204120210210e0706110d08070302040510020618010203 79
    0x948903d84540385107403201d41c10076904a848103590019090243c1980b460f0865001820318100401d0b04c0c0058074051841c0240040705036000040c818401c145410040c2402d1100d07941c0c4078040c0d001482c08906510456038040f40380801030001c1c002800d038003400030700712a01c0c0410041c1510202d510041c000c2e0058000e5075016150046203104400c0741180c3c0160054204010919503c1742c500f032210150400403e01c03d55a0078412825505400703982c2c4c2003015154800515182e01c40c0031915141984000010040030f60507405c100c16513650350424a04054010002419507405201c0135400030700d400c21011482c40e09842440b4258006240443c18581400b103580015440c9410180c0700b400104880c510040c0b058802c3c002104a044400300b8840400c0c0805001e03180300c20380d000c0c4a014444010031040d2003281c0081d4496034800c01820031115107a01540c0a80014042e1020140c0030400401d0316200c990f204a4074920640c000c0079140b51003641000c0584400c00640341690040043c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 183177275 1250 183176025 183176029
    0x5070e01050d1505040c0905040e030a0203031602010603141608060601090314010209120f100507080a0c0c1709040f0c020a0201050307170c12090604020916050c0114010503150105 79
    0x82d81c0115250403400590700d030403030459012600e0030307500c01d691150401d02010f0b001c6030700c2941841200e60596040c0000101000303120340f00d0080340d030b00303000580c81400000d806428403a440300c03001d40c660000040e07003030722504d075507041c2d86e0744500c1c6008030b0b80311652030380500e40c1580c800b400a24114025000c0c41c200100004e1028400b48000f07051040c6040784504000003c3d8115000304d40004c0880c0c0400c80d400c14020b0300d03074030491b441c0c8140703008100300c9030007020881c0501403160442e0782d03c000306175443c4501c280050104003019410003400c502030800184500401000c45801c0001864842e410030040100383c0f21002c504101c0107052140304c0d007040c0c1e0001468400d065090800707a1f103941d82c088040300c0c940001102d0307104129245050100036403442000f07154056008401e800c8982c0c440308a107039204015100203403c03854030000070304108410400140d42131110301d0301a1802420340082429204006920040b080071031004001d140750410040700301c868582a18442989040c0c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 183178525 1250 183177275 183177277
    0x61409091513061503111c02090a05070201020702041104140307180e032101030b011202030706080a0b04021306090812030601030906020403120c0201030e033402030601120605070e0105 81
    0x40d80064012810300b58041100a400c080d40d01e00c103158900041139541c2c1000c40075500b5054515014002d00050181480c01c440001140c017a009004c01e110368407070309051002010020308040031075500784004c200594032400f5540504e82e41010140c1c59a00308905407406101c400c050500c2903100030000c000500318010131075002d130505840002c52010383c0c61400e0652243c84503100c4061f202d11503d40384108500d1105050b00e0085030281c2460303803140074406880285000c080c2d0b25902c83d0b80100701c500d100700c4450303610040b0000042003d8aa810100f8280e030420f0700051400500e1400501c441a44041090300801d803440c000c1040b42d410300f4011829100103030072039042680b44c0d8094401e000366034049800030340c0d1040c80e1010304807140900030071501050b101207000031b0400d1a0115405000403c2da80d00d00c4021406680055020441021081051401c10301d90b4002ca072501c0c001d80e40078084a4020900041e9060340d010051038200200c0d0001001c040921a500c8a04102a68000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 183179775 1250 183178525 183178531
    0x4021309150924050405070e0402060d0c030605120a110f010503040f02010903150f0507020c1302130531020a08011e0806070518040515060d0204090614090915 70
    0x40c000a0010043d040c003120b000500b0801e00b28241054081c0c84000103140c1c04284520b000710180c0c0d070215221000201d043c4415103010754071071400d20032800484800d40c0314601c0e28540d418001082c0b9581e8020800e400e00e890142012500000010704c24440c10640131410503000f242c090070180001070018040703001c00352000d40300d800400c0c010421640034071b00d0800a19040711015a446030b15000395005130861358145039410381004049031065000045005030101c2c01440030050300003100300d19009401405031482d075030307500000003d1180c80714a0108846900840301c803d40449034162a002440595101c0880070f104004071440c456201004a054030f14011411503140110760120104420541010f100f9000b00028080401d40000050094900c0035401800c984054401c00044910840d000700040c04001c2c05000c06d890040b00400b90720314102001401c140d203031940c00c002c0310f4042c0c00c91141b9100702c1070514140d24081170100d81c80520b400041c005003800b0100ea203c203200103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183181025 1250 183179775 183179813
    0x10e030f12070509041104080d020c0603150609060f03010501022103040204020a020a060c030519060e0c09031c0504030614040f0215070f11091006020601030201051312060504021309 80
    0x440101e50214814400c41310034107801003003400903c00c003400488195000f403140559030301c60080c9407504940041442065000010714190641d519980d40c0340764299401e40c070541c021410056220f1f1941d91034007510003c4200049076407658108800a445d212842103c07480ca080b02c4641c1020b0200e014040700d61080d0f040d01d016840f41300e03e031410392510000f0b800040c240350511014000040d8164026403040d220a0740e0502c40807040c0c441d000c12a45a03004e007800c03514165001a40c220300c441e004040358500502111071300d2060111088103022103154403000900001000c00c00c3c4101800f910b05070f03a0034150b6440c0b55080965408401021003100207000d03804604440301c0d030002c440c060342c0c24a50040c0d40141e51590a00e404110000b501d80d58602ca404400c010458054114bc07100c001c1c1c4080303800604603a400c0d90015121500b100000044801400c500403e04a1440041d0480c440c4a0407020450742090b104000003010b80c2002c44882d82e282c0400c8502051a09805c03c040400d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183182275 1250 183181025 183181057
    0xe010b04030510090f0f1a0a0c0207030b07020a02030a0605270d0804140313090e0c150306041512050d05031e09010e01090503120a0b13020c1c030905010e030f 70
    0x3172400e190b8135800400050051441c802a10003444284c4414103005000c51804158555031030603d08200d5104941c028010703401003801380000f804c50004c1070342042050049800d4000168000b900d401d100b00c50031903940b5142c0b001c0c0140740e002807240d9440c0c0c400802c62400d0542240c4c2e205035a6000494404d003c020445002c54184042d480e03884031250352103810749994007032020f81502d51041324802c1c0001a4948003102c0074095000c103120400c14001001058601c94042c080f000d182c00c0501001c2d8400ea40e10b0001420320b104107840300060405042400c540221401d0181c104611100b02000b884401c001304200726031000300b00903d0522450f25484680c50300d8501600402c06405c1594140d86040580070030f001c4004084c2226640fa1400c03401d03940c0d40c503141c1c5025124007490a40c1c0050b2004000014003125402130411006204112007505400c034031140b8200801201040c00b2a94405400301400801c0c02244002100080118608500c80780f0340b048603c103001c03a411801e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183183525 1250 183182275 183182291
    0x201110a05191e030b0a0e06030712110a060c1a0906070c030201020d061d0c07020f01030b010e03010908090a060e0904031407060f1505010c0b0703050a0608030708040e010b04030510 80
    0x3016524440700c680f00c0852410f680c0c41520340c0680184040d40d0102d100300404440054600701050078640b04402c040d01400b840d83c503103154400306107101d4404a03040c0c00800c4291b495030b1a01c4500000818990307844070151410b908042180c401140c0c081403022034801c042050440b00003c100d500b1451628028803541280e0074204d009002e00301c49508041c0c01c002002841044044560f6051010295100b00c10744a43c0e044203040d100d03150300203400030460100121151700a0b0301c1140050300c1810035004683c0150006821100211011202030703502142e400300358204002c852025002d242819241082408001780340c40000810040c20041241918100411007201f541d81c120b07030082c0306004220814000401416131030466040030340d00c0b0180040e19601c0780b010007214541010b05100c2503165a0382c00c0780a064002d21101e060b540740c03c0001650601000102002d81c000d100d11074a450a0100b82c250403641030f80403608280b8240b10901c042403010400b00304803c809000010044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183184775 1250 183183525 183183527
    0xc140f1e0102030c0a060506270f0601090306090609120315140402041e0501020c040b30070801020c0f0606010f0f0212040603020c01050c04060c0803090309030d020d0201110a0519 79
    0x84550000500302d030081e031245d1810001c96070401401083c08482c0c12001c0144c1c52080c004a0456608a6829002c9140816030603218582e80f640c10a1040c0b4019213500c0d1a0744a94054a070068004c0f141c2d9030f9282d8a400600080d0141800c0054a51030b09000e00c0e2101490313400c21944501610303903002c0c2d215140c0d6000e0fa4581c0d0480f40140008884507403002258030742400c2d0b0460520560b0b02501a85004456a06e840c2c070a64191101c014815501c688460b0a0031a50400d982e00401d05101c441c000d00030400c0c030400550000300549400560740320090016581001c850700d0300d01b510707684000103001482e0382001c0000c0d050001d0340f5004002c040e40b00c02c00c0380713021035540e100c01116030001000314040d549500100340c030740d030104020b110944030950240c2d01ca10aa05c01c07800082c45440080c000110884c00030b5030045c12860850342010111000681068200c40205000d44d00194021049903028055628660341c40d828031424018201806030480c40303102d80e0308040203001c0c045040c3c51 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183186025 1250 183184775 183184777
    0x60405120c030a0302070315090b0c07051e010b011101050106020607080726060306250c020d15060302030601060f020c060901031503052109030a030305130b040c140f1e010203 77
    0xc01d8010121070030800d80d0b0034080e48525280c04240c1e07400c181d401c5040740004060081c00840c0f0780c80801d049143c0d541524040c1c403904440421581d42c021240c03100c030070321140b03280117100c03844010000410000380000909405181001c11520313034185001002002c4c0c01090342c2d070f4000c150b0305110005c0d80d5070141c1280c01c4011000e6140b844060018050a404590400d451040009a003101c4580d1140790340b05040b0544d400c01c15030036410050281c032101d03101d001442c00d2240f01030402c00c0341c003440359540d480c03407851103511350300300c1c1c1d5504410001d6103810041c06005007810b08002403580c050000080d03e840248104078010480011045016407007a8001c4544008005014000507220301d003668541c0d080448000410b10400060004a44800202e03201c0aa0003402000800702caa13805501410000702031043e45464100030700d0106421a03092072040d44a03115100d000d5041080080712403074484a01401403240e0710a0030101c0e241c1d02038246102446081c0400c0c0203000d00b00403032039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183187275 1250 183186025 183186043
    0x3040605030c07140105070833010c0519110d0c0509100e04030c060b01030b220612080a021002030106170402030f0f030403020f060307120c02120c0607170606040512 73
    0x15030110394103100c40700c4c0042d4020b0380188559038500b4529114141c14180c58159002c17000c0300404800390003103c402200c050040c8911703040c10441019103c03030300c416003072420b5404500490030460012104200c41c4284031400d802003154112003804c0f954030b910811610343d00606018818000110f200b0000500249000b400d1440c40c0d444c1038076040c070b001030a05030254000c95440b42480c040349240e41c0603004074403401e0400f40c55100740312403408a403080040c21019000019607139500109081901c2101842458003980003a9943c1403145002840c1c4001d1391442000d844c0305000512102d42d010890b00e03036402954045079000d0b202d03400028180009100101140c0c820100f08514031503000c0301403c200e82c000c030b4030404503401500174402c0501c022500000001d0302c480081a22000c25440601c0b0628284103d07903d0310701340850744d5013980c0403690150b03680d80300000300b04440740c0c00740075039003c0c124068070703007801d42801d401141c9503001d40d0080303034424044400c1c60300c3c07188d00800540385 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183188525 1250 183187275 183187283
    0x150b040819111003140a020306060d090804080a1226040818040f06091b0c0201080a18061b0c021e1c060519050408030106030903301a0303040605030c07 67
    0x3140403d0014040d00a09144410b2503100700c10740d002540001707a41c400c3d42d210707030005172915150901d01e00070100200300150302150040700c18040400c2c024401c118640c4011301c41c010785030000100c03d40140c80410084004c060b101c10310a80300c25800f00c1c2a158a4001350300408041e1104280c0140e066004440f000094025281c41c0c2080d56194058020800300c90018008001220000f058800d85e25001c405840128079814510780055110302035569001e418001c00040d681c9203940d00c034428000e90542034642e540c0301e148a90307007403802c1880d1044401c128244000301075120b80c00324030140c04084440418890300700500d0b040b42c0310407c000800700e01119a15003018910303c1d00d1801800d00b034038101c01c080050707c202c840100e100d220b1706006940100c80142503a10b0650124044d05101d00204c04000400710226480d072521b4910300c820009a00c201065011541e6445007103c8010041c0240030f1000200b41109440c040300b2641951400c1c40c182c0c4c3c1d40e99030000284542e21130340d0301c010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183189775 1250 183188525 183188539
    0x20111010e0a0f03121b1b050303070e030a0f060209040c0c0b060907030b03100204080d14070b0c0705030d060305060c0f070605061f0c050c010e0f010c11040e01150b04081911 77
    0x7010300e403140480d841e0009a40c61f0440882030005110482410648008010350b00030004102801d0003101c00344e8468100404a034070a2001b540e81c5000c9a0220008a44a50b000700742003d0a00e041c1c01810418080c62400010040141c0c032030b5000076070058942405145d604022400c001c0c07081c2c0002c0c4044c440503003280d00420300c440e54240294041c1c07041c1403c500921010090a0340700e80c0304d040414030050000760a000702512203c002c102d024003a8034509108111000000b001407000c0c0403100c41d1003400141683ca50f09117203007451002480c02140040412402203000782040c161815140c00074800955595041c0220300c0503802084040320a0200c94034000a0301d80c091a08151b151060050750035078078080e001540c076408124180f41d40001c0071002030202c2c1d4491080c0b849568095001030440350300c0c100110b401c8410f91a101b0071503944402c102c004c0c0301c6088c02607030018003410040515151501c10859100d00c9170010f0004500e54660f512018081c1041d0003c07080380b001044030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183191025 1250 183189775 183189791
    0x2040c03150e0f01090b09011a07020d080d0c0306050612040c050d08030709050f0a090506040b1509120d0503160225050111010606080a0f180f020111010e0a0f0312 72
    0x511444141103c011810100080001c50324100a0207080042c660181c107000c032603400c0880135410000b204800418003d010300c10b00d8090b9035880c81c40e460380303402507400d10395880140301d54000b503071440300d0044289420503030b0802644d12600104c40170492038100c028100c3e101c038a8490420b60150307210710750200e8110008001c0c8010f0b00000c5000d034070f035a118688050741d2031050200480440359142c0e80021460b0040210400c40d030019075010000900004900c205940007400802c1207000410480201003800c5a40e411301c21852424200c1c0d0100400105110b400c00030850f01c07000b4000000007004402820300c0a008110b03e401d01080101030000c1090101c003208010f030b00314890b59000510850f00300b5030742e840600c1010259001070761640c1041d5100840f150141548480328641c1c590340d05d80d1821711800d160070450707200b84200c0c0703050046403032800010803503442d0400c4c00d1203e0b45400000100c00200190346803080b6840400e848046460b420280c500f030349009410b00c0307218181004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183192275 1250 183191025 183191039
    0x1209030503090d0c083403030c060203281508031218030c01020a1e0807080c0c0a02030a0f05060c0f04030f0618050703030212120f0c04170303040309090b03060402040c0315 76
    0x104215224218400642c00200b944204094000b00c4c4000750103c0c15270414200418580c1c2c009560006181c00e004100500411407044158800f01e003840c0a05d6036038406180c0b2000b6011603c0003080310200850806021103865880c40002419500307401240440d800990301c000e10a488101c80403100071900c4000c070712005481d44441280c50300c440f071001e6000c101d0f59409045100e01030b041e6036481c4511580c1d0402c1c0250fa55110b41c0e140403081c45242014801a6070800c044000c2a210700300f0507001d0403040c90454907000015124aa04d00c6041c402001c012241c001a070b0120b0f0b4018211010396412810100c00034603003100c100750340e200400141e4041c48400581c880c102c0c2c0c071a83c2118810703640704400c0030319802583e1071040d501400c1d801050440c40710700c01050b0014004543d2034500381c2c3d1481c440c032003e540c5400030701d100d410110401c8103158010403054002c240111090000380c0c0d10b036002a46907800280020311130750b900c44040b41118843d0b88102100d0100400d030060054031404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183193525 1250 183192275 183192313
    0x31a0118050403081501020c21010b06040b0711040908030a0b0108090c06090909070e040c230108040609030c0804231e09090a150501031209030503090d0c08 69
    0x262900c64865003100d50000140d4801e45200310b80550700e00c0840d442d14590300f2080040e001d2560304600c6412002c003002c2d40d034804145000d828151051070100084a070280c2035500040700b403440340c0001e0200b04040030610007243ca465521404c1040340e903001100150003401d200301d0207004008003008022144085512600e0040426201c6000540d20202c10070b03a50041b1020503604504140f01e109041c0c07d017010190703042070410b01a105aa0380351011852a00c0e811038007030358441491031082200c2e00c2c2c0380c10300c402c8086845008001c4d149104002824170003016000810180d80e03400e030f1000b8036120300c45138042658041c9170103640d5640ca03070300704c690b1414400c071030b146031f8200814608103460203030700003504000c00400e0004564604010041840320080c02070b690b500540c41e10100140901070306010131840804006265410350805900c2510031140703801c1440321051050010034400016a196203200300c5805103402001d140104201c001e581c00380620388a1015400e0181c119a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183194775 1250 183193525 183193529
    0x1203040f030f03171504020a05040801050f06090c0304020303040605180406060201061802090f0904150903030515030a0c0b0f04051903060e0616052a06060406080111030c070c031a01 80
    0x6502c0c030342111000707043c201c0c1400c0e042d11003e2401042c040d10700146e0400c0d80150081d6042802e106051075aa010054291103086618210b41e451100401403985042116242c0008207042102e0951400c1ea021036a288a81e008103001d00c0b4001c540028515901020074100c844040d0040c08400c4c3d403048041c1c0038048900448401c2c00c914a100c070003080151080d902c0050004102001102100f802c5c444403a10203042926a80c0f090603084402044030f010308081d0a02c00ea0300081c181c50300c07a0764092810458103043d486900288207000c0401d00085810040d514074a02c9250340c0c000716441c81003503104690040d0340100d00c0c084002e000014454200f4100c902900090144800a02c812522528111810651503040741d0a808041d442403000e007080d1001d00412864116003500050034448102c04014038580c4003408112103800c050060000500030700000f800500201303e500f02c8a0700004000b110088c80200d29807080c17200103c900c400a40d0042c40d03014207043e954070314440c0002c0c24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183196025 1250 183194775 183194777
    0x1a01120312050411220b0103020a0e04020d060f0f050301050705070f03110c0a0e0f0c0403030c062d1a01020303070207060503060d0b0c041a04060f080a141302090112050c1203040f030f03 82
    0x84002006c2d500a0003120a03083c1550b0b200d990341c50300d0b581040001d4000c1810030401c00d642c3c82010817a0004400401d0240071300d2074080161901d014201800e584008042c00201310301072200f00c00003038100e50629940783d4581009902c020080403941d28200303540702120b0780302248240c001001e44184400354011803d000d4045041d03504c10020501c140b1940c480100080c0010513800d0100c0c2d42a0b014100800d5000c1685602c0314000c6000e80c142044001e00b49041a0f803882009804090b01ba490100e4410038000340d8211314101e04003a4071460544900400e0200c000b0000700745503900341611211503401400b0900c01d05004450055a030003601603441d43c4071109205a140c05018010b440450745140d603a58407801ca4850101d601d514090050100d0340c0d20380000e4219003020088132071040700420310050f100710250041080340c80c03042c2d02c1111800300c44ca001402140020a801c101c0c2641990b0248901c240880c50a03d1407060390b10141106001643c04002c014014514481c1a400703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183197275 1250 183196025 183196031
    0xa05090301060b0903031b2514010804020609060a14030a090b010e1501030c02010219030b1306050603010905130501110a080106030506010906140c07031a0112031205041122 76
    0x5030307602c150040c07142c800455856842804a003200031082c52401d10102d0600d400c0d5113080b80c8c0d0070402180c0e010b813043c041d1100c2204140a01c206202d4001154103ca801d00c0e040340c0d0f600341600070400c035200c0c40740040e0041a000400c48100c9000d00c00785804240d43d02075403a500d2601e201100e0003406a86801c40f01441030000025030340c2082c208080c0299443c400202611000720019402014100e98000555400f40b11621312543e8000d400361100e0016140480c05155400c00c010848a90b9000c900c0d510f842c02100b401203448120550b410f581044900180c0d940310009441e010503441a0020015030a0004c044907060174500900780c52151900c50040e2079803606c10030f030300b82c85040310070500241e0039403401c200c2c00384030b020b00641806d1050a01840e100080c140e9504042140e0819030b50340c3c900609003002002d100b0095030060848480001500c0039030f6170000d02e2881e040e840300161980b9003020405000302c0d40e20b00d0a1851008040c211042740b4a4101f00002c83c0d50403010171201c2c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183198525 1250 183197275 183197279
    0x2a0a030806150406031526071703030f0601050c0304090b091302090f040c0b0d0213080307051218040f0b040c080702120d1104030503070c05010203070b1306110a0509030106 76
    0x300070652018200044400303d05150411600310000c0c040040d0001000404500014010403c0460744c1888803005100504128140b400c051801c0e12940c0b0156402c49a0350a0095600012007178940001284071038920310303203c2000481d007030701500d05a4001c1e4000002d00140011050f40007142c407600960b800241e40d9151a00714600c074030714203070194116030040002204000ca000c0b06075071052240030b02c0c401803916600c044056800140d140c4081d16800100c0e035122100144060008003038035030085140040d103641e003c0c0c8a070b503550300400282c200481d0f0641424100e0041d4200703003002410030005401241807180140100c4ea80d800d001c0c62a24140a80c601d20506419101d071100d5001001144140340801041d60300110003c1c61040e91b4041034181d04010b80020f02c0214000d2000b0f54803104203082202c0c40c0301d410350005040d9070041081d48001a4890034444d0312100403507002502e80300e80d040901c06081e854002c078000c0d000c000f0740c01c0c15490708113002d407010324020780080091503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183199775 1250 183198525 183198529
    0x51908070617040303020304240902090a0c0f0c05010209030604080901110f07051c170a090e160f020c13060f080102071110170f04030809010203070909022a0a030806 73
    0x500b046001c020b601800c0c400140407034003d4009503001380c810000d46041840010711010700303400080c02da10100d0b445541e11025880d1000e6600d8000821035001c00c03640054010103401d008000041034248507410340b100c0b042c09401c0d410345083c88409000e40e2030502e000c1c41c0480c12603012400c4140819564041d0046101c0700141d110000c8119200410500d030602c000c00202018502e243d43d000034402000320700042240300750090303280c0ea940b4030948407401d48078050b04140558103c444403004d50820032140c0c801d40290380444a105081040c2e04c4243d1100417828036082c20300c01900310740303107403910542c03034213103a0107030084a054408003501c560725030303041509070b20902002420b42c00039a8040d58007490715050203600d034900d600b8081d000b060f010140c0000c001080740c104a42e403606a0410040c550400035403580016101c0c000c40c6075160450303001d04403484a000701d54040740d012554054038540000001403180e42d20040510b542905a081d80d941e000d2210100c00140d5150045071540c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183201025 1250 183199775 183199787
    0xa030615050a0e15070f0b0114090f0f07050d0219090b16061802120609010b0901060c060c12090c051203030103020a17031605010f0605090601090b0d060519080706 72
    0x40b00d00d580e28200c110300c102c1005043c9024500e0410424810010301e00000d41458588903030318454002c0300035941c98141000211034441d07110382d001e03645980801000c085468091a8011101c500a400c6500c0e40401100c05004500d5036042003440084d0455401d5540001e4100540ca40d44d03441c1c0d8110740340c00d004046130190f850703022500300c0d0543c0d01500180d0a034101202e0040d58045986280b0036580015981d074000500c4442c4603048101800040d000070b008902c110300003591811101d51404c14005d10449040301c3c003400b0180e941c20005d6000e4803803100380c0b141a82c0c0800038003640c20f0500303069600314210b00c2003900c90710110f041c4840f066804070070b40b4104e907001488144224902410b038001c0e00135445001500380020000b00d03241a01002d43c800341c07180144000140420030700c85c524125003154029901c40c0302c24004001c0345a0b405804e140560f10b582c11000c0d00c9100c0f0405c1a80034040640001e5802030a6040708502d001d9590a611700b121042000c80e5401c42d524003041d81c1d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183202275 1250 183201025 183201037
    0x30305072f13150501030e12040b0a12090201080105011101060f06090602060901050f13060b06030708010302101d0d0c0302060d14010e09070e07170f1006032f0c01020a03061505 78
    0x243c1c0690102c10800f66000f50700030500b0034450803d8482000701452100c10b95071260b00b1440d141800400e840e4512076115003103200e0215000c3d070410105416030000b0380513050501c1307000d040065154580307480d00403c1d0041c0c00103241055600d20017a880301c1c00a81103441c14050701d00180718080001320302c10340501a45015200810300441e40362249044440a2000c43c103003a2003440d03c0c0c2d0280c48071078441300025889940140e41d000d16a506501c1000384000310207400c501045001c103501408200740c0390303122400010441e03812002a8035458452548080346d40042e51044010501510117561a0842c9840840840703541c1c1c1203030317200d020a8007088029075140c02c0c550321030038017840040c8940d041d0380c0d00140e280c1000144000c1035003c01c400014115607900200b61800240403280012350390070000303040c0d01e0a05110031080082c4d1001500c100451250700a40341ca01441070708890841210200c40b0524000d56550070140030140250100b441110402c0410414060fa07d521800a81d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183203525 1250 183202275 183202301
    0x70501110c16150c140706080105041109030706080604180f05070e251103070c060f0c020f150c0a0f020a0b0a050a1101020c01140103020907090b04030305072f13 71
    0xd85a001500880d00c02c24410b13800c0740d4481c056005d8401d068010003811000782041c1d52100712540c1040d0a11042d64042c049a05444006004c610b445980220300001505c241d89400a80303070307a40c08006800380001c2202042840c1c08a0303010414801050380c4040d80c18000d408440c00140d4520340c60202000442d502e1418040440350b06141c8504c0000354003007070b4a940340c02e81100b541e000307031039085900000040320702d59181d0794104040b0750045a104104c600e02d0a0022015455401041e11408000300062082c25466142110380100905030f071007400d50130381110107800c1d4034902004d8036520540140e2098036050400520b0050460840d02601d40c1e41d500c1070b06114080302d00b076860f2540d4000c036003c03c3d5006d21190101070002d1043e81d103500d4507415595000d500d140140b0440305001707406d050411001e00f5041c01103110003012101100d41c149401036866100782004800c20340c0c0d0034101200201000004644000ca60312140407406044175044500340d0260720010882e140000c10b92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183204775 1250 183203525 183203549
    0x1051201091b2a0c0b070f11120319090e010602060403020f0607020309041806050c131212030c0306210311030309071809060f0618050421050903160f38070501110c16 73
    0xc880e81d5943d4920010581d800e033420480c2907100d070021005141b0076041200183e1041042209040d410800510160125009440103003480b41000351030f031041e04041360283e03498850401003d412119003103405a0406000c01140c00d240610741ba25500c0710f442907001481460b40824161060b8086001c01c1e94009601024a51400d0058000c0c21605051030103055176500009080b541c503044240c1c0c28040b0f480754420b607448ad49401750500701002e10041040d402481044060b200000d600020f40f0001204038880c010000c101d98050300c0300305030090065051114204500b242500610196407041e903801000b0040b0100d0b03402180c0085074041c2040c20080c81c10040d4151182007568848a545001450541e2a01c08a840c0c042000000c92070039800100810003c9000d50084001d0310019880e040035030041503ca21107100f00006c1c3c1e2070400700c0c00011003280700e41e540132202681d5000c2c000f404046610820074240790000840a0b13600d004040385c0d80f0f1200d90ba0003201082d501045100303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183206025 1250 183204775 183204787
    0x1e020303011d130c030602092b0602072607030f020c0f120a06050420010c080307201603050c06072001051201091b2a0c0b070f111203 59
    0x14a100b00c20161041c80b0920076014000003103007544041a0156004200c0503a80e141c001090020281d42c1c1c1c42c0e031024079500d0302850b03880c2c80311100511340426040080584c035140c0600305981d2801e00e490303142c1d0900709086680c800c20034414020309005400303500c030088400707409402070341c80d0840511241d0f4010030344d0b168181075181824001208074000703401c80320a208155200000c50308203070b8050b5aa9070344150741c00d2603039001d503100c16242d802c01c0c41c10003003440c4c82c0c0d6504d05060001500880138440112418008031103000d01a240d00344400045402da0225911b4000100300640020b82d40c41c0500d41c0d0744030030b0703083c59011580001d83c8482000380c6040d07100380041000c010b514007241001720030081440f01109070818075020300070b20600015900303295440312450624688a46c0103008404c24404a000c149104481805440440c030840700301851611400d00d41d075540180000c200085104414001e039081038464440c800c070400c0011201007010001e0f81c1080040c1e644883d4810064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183207275 1250 183206025 183206069
    0x302090607020409080d0603060b100306050102030a030b1801120302010c0302090a06050904320609040206180f040608070501020610080a1709040507050c0c040c0f200106061e02030301 81
    0x2d2007005d010b010b03920300385807800d43d0381d0b400e8134555441610121b45500b542c254030b2070f20a020801c002480e0400304000b46c40c00001039164000d0142c2031050507030352044600540c45680d0030184007164442d0091243d80c603000500d268201d10a4180c00540c64540d030070450b24001d00c200e560018000b00f45044103841c18004a60583c011500340d600b1030780380da038920311046c55250180a40041c0c00b001001c048500314030500c0010008190358410741c1c00d0424400982c40b600104c444003c1800342103840301c4800c1d00420782462903400541e4003e0315004001800d084042034450a880090782618002d8603100490440344800e4081d020741500078207001c0c0b0001d40211080004804440d40d6541440c4a040018049030011030300c00d400308400041c15007606100784140c0084038001c80e0100904071840c07400404a07810300c6022414004030103036006150105024528240090300001e2040700c1d16500000e00303803d900e010b00680c0030f10b440c030042c1e1002e0010042e44e060350300e00000c0482c04802211 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183208525 1250 183207275 183207281
    0x9050916020c031209130207033504030503010f08030903031b0a140d03050109091a06010c2a050108010810360b1f03020d031e020a1203020906070204 66
    0xe140056124504007294140c800744090080001ea03980600c0d100d01c1c10b1002d10903132040360301090080c01e00c100990b400081d0881d01944000e0540e82c80000103c4c40800307090380b1003442aa0300343d60807004004120400d070f4408002c5050ba800d2155019016039a04040343d66402a480c00d9a81900140540b5401406a81c548240d075100d030000c481101c2c3d07036600e41107811010b0404840051300140071401c41c154250051500400384208100410615600d80030306013501c860103002010310010104440b42e102d048039030141c5401c100c91020500c0300400c129030032440c918410f01062020480012958081c0103454101d40c1441d004c1c0920100300c400d11402410080b1842c55088503050a2643c1a803a0301c009180305850030312040c20041c2d19003445c601d0510011f001ca5100c07840c000203000715465182505040320b505440481c6002c0071450103640028003e03205030130b01013584050f80b507a594000b40060003c0d004114400c01d211b04850103c003680328040c0704d20380001e000c010800c0107003000e80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183209775 1250 183208525 183208561
    0x20d12020721032a02040b013b1009060c05070906170c030313030204051308070b150102070e070c0302100501061d120703020909010b040f0219090509 66
    0x44140c070021030302c90000c07000e40803030403542c0100c42e4003031062101090341010f503003002c3c0c084c4290003480c1580c4034004500c11a0424000900482d129205005030380d0044c0301001c0d41034001d039480680421590405030702d03c0c40040d5900c082c20005900041e480c209501c044c1812140360790f07a403003c9410508180c91140f1010400c44080c801e600c400580c0c406030744100c102500046458080d2298809030b85072410301c81c1701c0d106100b50003c100028a0013032542090045940c1032318041003d80d624901100c48ac03100c0c3c40c000e8140b010004210341080001900c41b40f0803120741e01e14038129100c10004a0b071b40c982a000b00d00303902c2440c102040d1817502600720b070603a0501c02d10449100703a1404140e4000c4d202c00780d101d00e0102d44100c4861040981d1078000d0300c0307500000c0d030300c5050344269000296920700c514440607025248003004503c00240c05e4102454022024006200d681d142458500007544070790390414040403d00940c3c3e4000b48545651001c443c001006102561145206c1846111410f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183211025 1250 183209775 183209777
    0x5071a0717041a10231f0201090210031b0302041a0d020c1005160212030604090807051209090610020703060e0c180105010807090602120d1806060f05030a020d12 71
    0x914900c01d01e26120f501e1882c4100c141e02c0c0c014402c035241000e540002101450032440e00d504000e0170600a444404d4140d861b402c40e0483c0e0681020b071054180c1c018411050082c1d009100003040180c0715406410107684203540d0b41c030f0b2001848142c3d00450032401680240805452509030070000c5106040141254100c00040140740c02c032504202d500d1b010741005d40d1400540c88408022144040c00c07141c2c40d00f44001c0c0041e00082030018501882840f0040c0b80ca48500d968a040405000c21802a512031582c07141c11941102410000c070f40c000e8104202003482001c0900001d55035090a100000403800c1540092444600315500c0a001d0005000d885141c0d00c40d02800341c0803903881d03124207400c081c140200b002040d418a00014260b80004014005010002c9400c2003d20760005002c031001d03500600454031050385400c40e4024103943c20901e106a08086002428001140d11600860f030b040c0d1817480b1065039402c141030301e03540d5402c07000c1e40c4a41c00307414200102c1c401d511003484403022 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183212275 1250 183211025 183211043
    0x7020a0b07050c0306090a0506010e091207031101060902160f0303020c1005010521070e370b0301061a090f0a120b0703050c03040818060a05071a071704 67
    0x1291036411498110901c103407456800701c036024900342418017403280c0003201d907000340c54001e07000d0311a6907803401d042c850040e080c107140c0009810300c2e20510241e001d400c00e5070b041550303508031401c005100100000ca0701180f075103040c030005003000f110310072543e2140300c5c01d285aa080c03072151620560350038000e0090f4140f603020010b18140c1c0300103200e100c60740d102d140740018003541810180800c21a8101e044001a404c02e44070410b0311000250032811507050840c0e4400b1655820405850701092100b090300303168540c0c1c1ba03008081d800f42c0301501d00b00c0940d28200807140c1040704260a841c460302c99202078a40071840c04858403183d8004103910707400a804040e000f01c525000c66001d815907400900c1d0314100308103810402461681803078200d03103185424080747c205094146158030001c0c1000300719038000994840380d405100810701d0440070007000c0c240c0314030314810080d0007039014001c200c5050a21244503080e0a00d0302d40810b0241842b41c0c0d4039800c405e0340c0880c50034032001c040c0050b0360b5624 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183213525 1250 183212275 183212279
    0xa0f060b010311040801020c10060b0301030b090c0310090b07031109010e0a050a090501050910050f062d0a03110f0307030209010c0c0902090a050301051e13020904050a0507051c060207020a 83
    0x4083d0000e20040000300300045c2c2e900340c40c2c401c590924841c00c2500941608003981041070688610079641903a4000408828030344410100900e040b244401f00d9425000f600300034200b10f51a6444400000e0042c418601103a40f070071011021540c03100c0c0300d04202281401040e03104c2d48100c141848034440500441c05258843c400942110348540c05101d1598485005202504005d81e44075007003d0304c010202500ca040000080741e030741c8418406405803c011540c005283d0902207a02102400d01c189000b9004080c441070059603c000001c002280c245062007903296846001c0f00c1c00700084000d41400d588580404801a40c03296208904010b0280114000700307610010107030040000d4803005a540740541c050000d8207103294070130f41c40790349402c04110429003403114620104040400d00c410642d101d440082e903880184101a410403c4607040004003d00001c0d419000f0b130069084a43d00c0d80d6a004002c840c13010300c2004180e070018055428002a440c2c0c001d0200302c1d1000780740c08801380d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183214775 1250 183213525 183213551
    0xa0c1d061c02031b070f060c0c02040e15070504030209060d0203070f0b070309240305091612060605030f030a0f0306050904060b040605190e0405101d01060501020a0f060b0103 77
    0x1c18040c24480c482c0d0000c240001440c002e401030008202c00c1c0d80c03140c200112904c91404a05110102030700194031046800780d41c600c5a40d0b81021103a004001b0804e6501c3c17003d42076a50384121510001c0c4049810100b03401134000c3c0b0a41c0c0c21243e00801d6812070f551050180241d20911800483c3c051140f030301c0200e00714560920142c00740071080d00503500d4003400d080c001c00c41466070744080f00b10a10401c01c00442e0f01581600c0301151014100495217407a06c842c00c0d0b282800f2800c400c085404030320340200d55280301c048581a282c1c0100000e004554075042099145d07488004a03003015401003003510030060080c1c100104404180c1000101250399030045903052a08581c01c54059640b00350480f468500b52040101030907056580d8403e04040d4500c000501c0d0144c001d00503030036444800201004420041d1601d40079184409102e04280c002e07440e1007a40da2480030060035420104007041d65413000030301c1c10f0307100e800c010f40361002e2105880e0f403c01020102103c030304141d11600e5008100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183216025 1250 183214775 183214807
    0x203030c0124060503040c050402070507030b070917010209091303090807060f020615010212090f0d1b08010c021216021203031f1a03091603050709050a0c1d06 70
    0x82e01c06089122000c405840201102d1541900700009005007072040c400441e1240703400400392003003580c0c016600c0489040040c58181c15500050560070200c0c00c2201003035101d1071480854070000001c5068903036040c2d401c0d0a034041d42514507080b90620300081e02d50805811000c8025019090526030745484442c0541095425084500071401070310000b03052683c10070a084d44090200c0c0091882d501d0b1800007034541a4880200041040206104c05182d81d038610422003082d00420705d00e042c203c90710b0f14580c43d80240300c124010b1155084000746140040c0110300e406a6103502805800c18040100c80e840d810030070880c0030b640c4181d01c0120040e1951907a0a0304c8440041c0115101d2a040c42d41003201504200283c0801403440e10801c48404036048461201152101e142d480e690765030081850f2543c50940225010316041e800001e000003c1650000e0f117405020a0009950724003141055802c2140300000003410048408040d83d40d0015072038a032880141054500700c9925141280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183217275 1250 183216025 183216041
    0x603101a03010e07020613080903240108010b03070e06010c0606030501020705102927070c02010f0305010b0714120a030b1c05070b13030c060f0909050118090203030c01 74
    0x3484008010f0141010440c40c0c0c50f882644c0f40300801c41498185201685a500307048014029140402c0b04e01300c3da030381803013407504c2041c00c0c022200d00b001c0740903d00d503040003080c85500241d51805110703002c103040206005041e01c25011105001c0d85420004560302c42640f1410358805541d8140400081d00030700080800c2c0d4020401000510043c48035441183d8445d01c4a241e04050342000c500003032018003010514410440c1d90800706403103e2100180f240e80e079010041c8501d006000c104515821400307400710745001ba40d540030264103121040d401c417a0b087c0a2054045130074030ac200c0000300d000980403407004043c419a108242241c1000c54239801c541410b03800700c2c2e02c2e03104201c503e0404180a0b9100b680720014040c8000d01503c03900c0e11000c45001d0707408549800500b0710400342072481308000440e4040520702c6500c0c0da6110042014800114450008003100d00002d0028000c1c0903c50685101000074035040540c0d030345044c02400741070000c98050209000e140d554031028440c081c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183218525 1250 183217275 183217319
    0xb0304050313080c01020c0609030a02040c020f010f05070914040b1c02090604020f0a120612123903020109150c08070f080406180209010306020a2c060310 68
    0x2e00c4040a0040c070014040c03680000c1c1c22a440f0000401c210f83c0d00050410050313905030740c41652119250046801e00b4178101020b500282444040d4a40541c0098644500c010040080040c4c042c205841c07000e4a000b52104c8000a00b001d2090002078101005402c0d100401400001c150050300003165a6142c5a1354500b200c4248145200c20b6042400348140d02580866046160104c5182003403098000c0314060301c20000c51482052903820701d6032011000c0c03e4030941400c4940c5861600040702c0820b2038034000002c1d505640116081d08125504e40070303900030011104010302209120300c078415545401c1d4115922240e1500c0071403003107030841d0005034142c1c80100300c40c1e203040300240030568007800703c01c2013001c0c6142c110300c4d40d58050034407600903910084c0441c10010a040b20680d00750900e001942c01640c140c00001040107550092040c0c0c034554643d07150202d81c3c070552921809040100c01e00c508001e500411441c0391800085501a46616a6101040c2c5070031b007182500001ca10040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183219775 1250 183218525 183218527
    0x6030b030d02010603080304172502130c020705060c03120a0605010908031e091f03090201110d08010e070c0c0b04080106141c06020d092004050408220b03040503 71
    0x14202803000e040300c000c070307030000b403080900e07580d07910340d0350310005002403e0b5511688492040c0c03010340046a02d1403424900d110903c07190844e40d584820b0200008910550308c035000c2107283c00b0b03e8011180525040c2d0080e01056207450309104180e80302440b00c0ca00d40c003041040c8413a070300300e0700d00d154000c030079403040000e0041c1441c0c000b402c03001041d00000710310761003030100d00503506000e480700881000032004d0a454101f644089681030380040d21782109402080144007001d503040d0b01180890b0300036a1200d040190084c000c544550301220341e480007801c00b1006210450301c00c4040d80c3c22502c02d18100d440891282c964031a01c641c80e401400280c000041d0400c03203107000340a90005884000800030304100110006203007403009154940901241400b0f15040c44810790564038024aa000c0c14088000d99290038100316400b940b44104d100720549554516080a12a1a00c40c03980410303140e1501c043c00e00389130300c0300703000c218030900038945020080741003400c0304055400b1710311a10040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183221025 1250 183219775 183219791
    0x10c03030b12160510080907120c0b030c03040b0601091208070f02060f030108071e050108040c05120a032007061b051c0e010201090302071e0f06091703090102070b090d0605010603 79
    0x170603040d916080107010041e50702c0a0003a10b12001c41c104d0125180441000ca6202040ca09103102010650200d1b80300f500200400c1014a2460002c42c49180715244c48112551541c1c015600c401c084d000c0d044180c80c141070031400040c0980001c0584d1405803000f40310080180d030003d40d0b04e03445070a074660141c2012004000d1540200000e50140008040044416203049145000c050141c4112810401d071040400c0c1031102d1a05450302800000d014200810211128180c1d0344074511000c80024030704c11900f03c00c0c94115031040c5410319810010b407805c1c2703151190031a40440d100b504852854000109000081d400300603c00303440f0b06941c48030a803e00941c00c080e156100d0790601d6819641005550070020741d01081c0307041900e0380c041020f04500300c20310301440c8000c0c107a0890260240f0101010640340d0700310820500321440520004541c4042180498603400f82d460598050392001c24140003404402e0050a64110050300c0d0300d0b514000c41d141c178412382d8005c0c0e1005010941c7c1d0441c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183222275 1250 183221025 183221029
    0x9150f0609320708070f030b0a0f050f01170103080a0207081f050106020303130b0703020c01020c06040b070c050a020103050a02091c0c0b04081203060109080303070e091302010c03030b121605 84
    0x440c808900051004824030700e003c0d240600465002000001080031121903640c0c081c0c081e40c00a180304501500d0203a0b55505d5800a103801c21050040c940f007207840c5c0400400c01d61040b2480c004103a1441c8c0d0301d00d560707441e559581250760401030a203000d5028021001c82d95210400940d5a101240300803101c400280301004800c0f84d4068215004640040081051003014150b40900f66640300f80d00d88807940c0c404030b08a009000310b42034850700303500000e0702040c1c8901c00030f100c3d4001d038051507480d4204c2d25019000d07500745012803402080754010b00200e401540c001e6001c40c0e0300c824166800340c58440b104001032290109800c200040100c100e814038140110030007140050000188450310789400d00c0c0c88681d48844002c0140112400080043e01c2c07644105404e0b001400c0140c126512814041000382500c0300d5113a510380680d4200c40000d800c401005a00d00781c040d0183c540c2441120251012000b8007040d0280940100c0490000c07401d50710100484002000d00342d0f411200e460078901 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183223525 1250 183222275 183222341
    0xc12062f0702010e011e081501020f10050c0d020c01050405120903070509090c040e0303010602010c0509060f03070314070c03020105090705010e13140a1d0109150f0609 74
    0x340046051004848405040d110841107424464090a0003180c1141220040326603920000d010011441281d07114050140c000e500701c1e0081c0309103a034000c170200b501001240c0d00c03481500c181d00560f201d1705010b8180c2c00107901180d00564001031062a0200c8180800d080c3c0e0f11803096160180c3d03644080006002080c010780341c0d04100702d80c6d03182c503010748000003d6a900b4580a03e504c682c0150300810391888003002000c80202d4060000d21200185c2140703241c4a8000740704103005542400442c00030544034008413500c03018018952401c000d007202c0341400c2e9410042c980740505075184102d90400108d45c0c082c610908c3d140d5105213003000946002429a280900400701c3d90b40620b0741440140e0f0486a50345c0c40c034809a07924141c11400760b10320000b8043c54024a552401400240300c00f500190b0042900e07441340c809200b9007011040e0703a00f422207801d1031000e0f001400b140c07120b0343c940c081904102c0090310324000209030b0381d85a1000c1011900903011074440c01d01400340f12980821141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183224775 1250 183223525 183223571
    0x30f07140f1f0b03010e0a0b0402011103040b0703030522060501060e091b0a180608040215031e0a0e0708100e030325121404060f060503190c1206 64
    0x440034204051480342c040c11511000340d04011815203400c14081aa2400d51081d42e28100300011555003044a0a00c1e0151000c00e40b0300b82d0005001e03180c900032512000003181d04842c0149182842c015407a00c08400610002d00320303420520054141120480d60074601c00b039107500840e40020070354500003024000c402c22010f410f000740700300c0c010080220450784200c0110054042025521114550100e504580c0043c4155400021004c08510258010746091046200395485c14007a80c8042c2200708078001100c03242ca503180114010350994550001280d0171442100d00820b024003a00c444030b04040e480d030440e0756a03501a800c80300e446035040c00303500c280c0d0300090084c5145041c800468034034040d01ca038200303071940c1a00d1254218140300301020401403119841c00c01c001d0007116003081000308169015600c03d414030380c1006c0d00002d14441c52040302e400400608050102501c1c1c8000f0320700f4590f00751540b40183c840026264503850002e00c5481c411680046c4100d4250401caa04110785 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183226025 1250 183224775 183224803
    0x150304061b0e03070920042301171f09060902030a0605010e01020d0309031808010f050f010f030b1e0f041203050103110103021305120c0102010506030c010203040b0705030f0714 78
    0x401d82002c99140030440c1002d0f0b4050440c0420082140703402c100000f82c0d0840720160385680094001030540c602040000302e103810058281c42803107808011600c0d01c88158000000c56204004600a60101c01620394044c2c0840400c0902c0d580c0c2d20840002c07200d559011180e42038001003048918500e130310850b0080d06003403c0c1060a4101e000000f503032030880c40004000c0c180d48061030300525001e081002d4045520b52440b241140e01e402c0c10302e018017003020098200f03d0806000c189011341d8600058141c42950850058591840d00c2e112055440540f09505907030203900c608035082003141e400e61290540c480d000320141040c0c54241001030600844c8400c051074100140006441c5030548000c141c024078026894400701d026400200301c89500c125440040021680c0109401198001a840e401d8000300001c0d90303004185502d032010411110b00580041000380112460203001c0c1c211540250112410002c0204640419510201090700c281201881c00a541941009880e002000c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183227275 1250 183226025 183226037
    0x504051614160803100302060d06031b0b03070318050a051507030903080a020c010e07081011031003022205011e060201140c1b03041403010510061d150304061b 70
    0x203080d42d03488040e0b0402002c0f40d03000000725604418201c1d07080007941e0003d1246541d05295240e45004041c07500c0304903040201401003000281c03444000b101119402030a603803031030b56510002c50041100d209145804c00030b8000c1000803507420002c21214500c0380e07005005c2424042d049400071034004200c0b01c101030400c0703c81000203170310852698115414000160701c80d1004408207001d800c9000b1401b07054860a0000101d0f001c0c0003c0010301812100030400454469402140301c0340320490b1801090901c0b41c00810050900c99003101a0301a03140c0d00545605500101106441d020f074090025882c03d14442c140700c851046490f001801540020409440a0481c0c04040b40c8014107e1444c00700c0401c212350016405468000c00c0c40e00d0305e06590f941c640700c108501e9000f11111881d4029031030980001d010902c441c0030030701541e215032074003442c1c240a0701201060b85403007544140c20025480c00c483c40782c40301401941c000c41c4550408620300c15020b0001c810410f58403046810096 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183228525 1250 183227275 183227287
    0x20414090d0305060f0910050a0914010b130320041802032113170118020a0e13080a05221503152106050f011410090504051614 56
    0x180a0720700d01d4042c2404503081d5039103400a9241040c2c809100d411050100070440752050500324501551001c48031207040b02c7d16004040c04440d00301450500d0204c00c04018000310300c1c003901604c4480905000040d140e51030380e5641440020716150080c01c105200c040900c07a151900804900940701c01c0034454502072a00001c0e03681500d425004000c0d586070040601e40c03181c0f81308403804e680d2003580b040c00340b5684801d125884104554440119441c0070301c010218007c4000400c103841c0c00030180c8540c02e090050300f2aa00b1409060a219006802c0090300010720305c01c0548500852071b2038082d101c18405248102030020005021900004584144050043c035120741e11040d00501c0c0008800078240503041100c002c0d500300e41406100c10000d00075a00c041d90030504007502c26034040c001c6032035601c0c0c1c08030700801c00c0c050b81012505a1354105d0803402c042c0e03032402da00c50940c902100625512004075041f00e034140c1d82c54110462901401e404c003508030783d0380140b58846400da945811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183229775 1250 183228525 183228541
    0x1f170c010c020604151812140a03170c13030f021908031b0307050a050c1003060b04180207120818030702030a032f01061409090d0f0504120609020414 66
    0x4031460060014400c0017441002d809445026510801000b003410550707180d444e0045c242c6803507010030303040f01c2100801442c0c1d241e5607030118112030300340d40c1521120b442f425007070b01e0718201c074200800c2294020028000000c002610100e0030b401107020302000813011105006002e14074001d00780c54400b2898401e0108440d0400200312540540a881c0c108641728000400c41e040d441401c1d0040d0542c41041001024041d0100d05d488000804850781c942e20302110905800740c50b0503205000c21404180b20400000c28441c4020b03160b45032400c00103190100a541d40e0790150084803011000521580030407180c100c880e00e08440d46511000214200740440d03001036a180d000c2100140bc10040d80b075080448205065038100803049c2c62800074041403481060750007001c0c0c1c1e20541940e2103030302c041e41c3c200b400c1001c102d03805540c803c009080346c60350000095031602a03d50780001001401c20000a002e05c81440c400d01e010f1003a81c4c04910001c41c2d0040106030f0341400101100c1040910a020305a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183231025 1250 183229775 183229777
    0x5120a05060f18070b040801051303080726180f07030f060b040207080307022404050d140d020c03090a0e130b09011d03030a0e0607090303081f170c010c0206 69
    0x440e14124444003142e403012103c03030000640c04009041c620406402049201000001d801501d04036402045203540b819050750f000c00d540038020b004940084003090401d0711400c280e5070301d100ca9042c28001220704540441c0e82680403150200a21444001c0c44140e007424402c112405018034010b220103425501c601c07080b4100054014241070703813502983c1a903207403078056840706500320043d540c0340d182c012400f81d15080d2140b180b103c0e47c8100d00c1d031082201e46003e42613001e56004030003044140c000c0328042d80c0c2d010825142403a007940c10301901100301d4150000303008448410300a19100c200100c188044601207400c20301100504034104101082c043c07130b0f00b40c0f2040d0001c6e01a00c0d20344442004c0341c01030042400d00e20f4900c0e0b408404000c41c45000000f14002c42050b0030400403040f901c03004a0710760405903002000205900810070109200d00c4100e50440494030740607828410361046441280d00a520030800321940c13401c4144240c0040c049070050749000e0070003c4c60100198005115 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183232275 1250 183231025 183231031
    0x606190b0d02090301090803040c17070b0d0c090816170d0c0201050d060914010e1003151a0901090c110c01120c0e090a0b120a02061603121505120a0506 67
    0x19031a800b240b9070740303030750313025045914000d40188120380c6c1c0e030a00b8180103500c85d109000c1c880f52072140054400c1c42420002d408400c80b40b003083d003241081c0d0503007071030b40c007410824200c0010401000d1012a8640c4240301e0380c420340b40c001c6c900641003072170001c00d40e00f80c00301003130b9501898020003e10403119030442019810558246405a903c0441c450224000c155a030440c040041c42d00c070040c6016500c0e10200750694041c00721252a60341d414414000c0b01d0803600004200b0389203032503600c900808681046104800001d01011441042c0340880c010710401d80c000590035481d540c078012203d070018419002d00d603c120292200004902c0044c1103001d424803554270301c41d030340c0d503002000710302c6400d1401002800811607101400c0000140c0d01915550314110b208905508109120010014070032071010380c080c00b00e070700302481c2c0748030303209071203004442902405160403a000d4800c02c14407640c60f51a1911409502c0c99041c2002e0004540d8840000c1000c0d511002511700401ca001400b2a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183233525 1250 183232275 183232297
    0x10120602390f06161107030b0c070c050405130813090e011b0f02070e0709080115140301020702150307031808030106030c080609041101120212090c0a120618140606190b 74
    0x4000310750051220f1800051f507101808100440c014401c407030003001c0050150501404045078065161400c00044903000e8130381035050300c1603911035800034403003001410900c0e20300e2030f28450080d600e07000401038030300c00c60841040f65550083c1d00c1e00c2505c00b0209401d8a20149807081403080309a602a5841c4240d02405040300e002d02c00003410300d0f2048440304d01800881d8024070850764800001c441902d007074000e02c03140345802845815241014400d0b02c00c9a50000c201c3c0d80c01d06541c50a1407110760001d40054101360300c404089081802c55111085d4071481901402d03500e41c5031500c003c0842d6003001c0104100001d140600c91203549004490780c20581041251a101724003900507140d0341c00a0540414050020501040d0101c500f000035200c0c1c05035500350742224440a041001c1c105181c050b840d080f111410345070001c94400c0d4414006140b00055444a500c03040c2c5a41302d10100d010640043d69200104000342418414081c0141c2d0450003009502907040c0711901c0114018080d00071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183234775 1250 183233525 183233537
    0x5010f050708071403090405070201021603050c07030c0b0c060f070e01082701020a02010f1b1b0804091a0f030d0309030509101710120602390f0616 65
    0x341c1804090012614015400011103600260200d03910341c0b00c0d040403680520032807030034000880d080d0040c003c441944400c0c414074542540340e5030703058810f5084121042080d00c25100c002c400101000e2080000c2c10462055036120041041440e19100c002012030310b92401100604c6103607900000030000159090070240000d503034441152200f20307842841075014440c0803688140700c5206600818204142c1d82c021b0018860075111003003035551200004000320350103000400c94038812405620500343c080141c6020f864141c880e6891504076070000c0d40c3c8650340d11426285401d4050b980c1c4010b8070142c52829031200c03042c001a031030b01d10901d034020501d0b407548010b03c1018451422101e411400500400c90ba1184090042c408206540b0010503c102140819a081d00111a00045950130381010b92001000d6a511010790000320400d00010f00103248a84030340000302400380415000541000341030384002d000f5140032143d1a220301180c110380d0030300c03504400110002048a45505000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183236025 1250 183234775 183234787
    0x28020c07170102310807080703022b0312061523040321030509030310090c03020d0207030809010b06131a0906040806040317150108070311120f1005010f05 68
    0x40380a84200325915805081362103650402c8412411681a11402e8030251129282c0f50501c2a0b0750701868080c1d9015603200d03900c10001032070b00130302c21100c203002680c41d902d08107110580c0e45010201c545081300400d802440403803078005a44642001000300382c80720503d40a865502400080500800310842007000100060204100040700e00079540300c98549203030b40c07040521041d4107000045c25000039007000c0208555110020235240500301001540c1541d502d8001190018031080030a0018581c00b070064804000a92004d0810350303000c0d40b60503a0350302e0031501890071101006001849403109101c000404481c1c80c0c900740c00c0e600c00c41c0c241503d21a24554021040c06181070059009100041c04a8083c80c00700e0741d907004601c29110061750143e0020366100c564000c446d1100411001609100990300c50b000d030a820941500340020500b501c2c1122940c40d0384040d49a810f003140c054140f0620a0401c9000c40e803005401c1018402503040030002011640070481d5441081004108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183237275 1250 183236025 183236069
    0xb1603030b0a09020909090a20030a020a0303110c060c0a0206070807080304080d0c05090609040903180f05030c03011802060706060e100e0f012601020705030328020c07 74
    0x610703001031000345480b800326680d03800078010350300c0740d03109600a02612000c58507291303001481e010210703401030608020602d9020f06003100e001b0b000d0104da051049000f02c0e8003507140c1c802d894014602035910f0b01816003c540e4a10310b05117581c8260f5001c1e072410003580305010000f04940031803a034100c0300550340b0030b01c42c18580072901401d10064481c100000a04c801c0000c41401040394070540f0005100d0382200320010f44a83c0a41e41d03015802280800080d141440c02d54440b0107194841d080501d41c1445044014000b48030382c0e00902003c11002009000074901000011000301040f0000e01944440303c0280301f0404440310000e00658000c0740903000c200c05500b01d00040c14501c1106801c62814545050a41440384165484a0001c101081044403030f2041e26041e1244131031240c0c1a203e00c041c028880d62034505003071003e5542031160000081c1c00341f00039800342045804d401c040c03400da00842c3d60810f101c6410000359510402000345d0044000c20b4400880b00d0b1554405090074000305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183238525 1250 183237275 183237281
    0x2041b090b0f0c07060f02061003030504091e0c390311100903020c0f0945010c0e0612070e01030f0509010c08160203090d050c09070c05010f060b160303 67
    0x105100f49024000d4003044441e407002d10598a070241d58210ba540c1d071160f440c41c114182280c0406000600108000d1100f1055900000e100310102060700a80340c440c00e0b410b404a03490018018005180d188001c8554400c4419298080b9128090a00ea40c44001007a041140090000605000c1282c2200042c01c01c1406a09801e00740c040003400a8007042c503009403100b0084010501c41da0300d120101c002e03418a000494800d04c44805c0c100d001c0b001c01150b404102e003d00c0403402c83d1682c0d483d103031072004201e910b22441ca0000c14002181516172060f010302010552402140a54420310002040c0035800d01d00c03d0300b119290805014294080d00101c01404500c3c4c15014034034104001d001c1e40e1041544a18241500d555803209681ca4200300c10035002a07400341e0780d006a000348040151452715652444025100343d0848144400040105040c50000ca803140302285444c121501804002c0c020721000f451001000c100c4142045402111070040c0919000180c00e20403004003090702984c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183239775 1250 183238525 183238537
    0x20a060b0102010b0a09022106030307142103060a090b0306130206090d08130501030b0105072a061106070309030801030f020a03080f0d0e07030201140309150103060902041b090b0f 79
    0x2800070181c1548406c0f903440a0341c420b4400240462440555010707071160200b000e802020001d010750b2801d0450344445940c2540f01c52584c0c00c90213080c104184164003484095101081c07003001680301d151078410000032034500d5118288160a05100c00b055030f4000c11556401b507880d04072003d244c2581d0020070858024000440e0f00115114201c109001c800800341814075a10801640480d0719040110180d44a10388110b011490600a980c0011100308a441020070f4039000e111a0010500510b501025940e1000d0003081c0e40c105044c005200a00005910103e14203003403101c0d0340305590082600c101480007511008610400c5411944c800100340b00964000244545881c0801481c81d80703507024540150100d490805c508440b070780e000c24070030110b0360141c565030041495a1700d400400da0000700740c0300032030103048490091072820039070980c003075401140002021345c194410f1204441d0300225511124081d56840d8201d04d40c042c2c850720903500d410380702c651140142d54409040717000310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183241025 1250 183239775 183239779
    0x1200705060d1a0d02210a020d0602130f0b0313020d02041427070b070c030503070804060e090906010501050d2304020a0611060a02090a03051501050a15020a060b0102010b 75
    0x102c9401407105a0440714120400c0c0c501408100010420090350081031200250001d044681d071416090560140740600000b0101381c855010060b400610014200c000032a8059800714511543da83d0154503c009030140b505090b40d16824001c01d000d0a0100a10b10a602c0c0d4482021404548408035000f00c0390b0380c05402404034081d0640740d0031041c00704513130b8603004611030400030910004c00212031050418270000b0780103981c102040c4c0a00c9a20040381031320350b5104031000100244041000b402014000e40045484904040000780840d910b4000240701700000b409001c240728011649504584003400c0c2961303107010349190351002d4050644910305803c440c100700c001402190550600c10341c401c450f26405a521502c042e5a500c903200813014072a40f00e0000540050705980c001d0105940051440e0081c0765655100d901e0303c40d01c11034148a20086000405c81420700418050203000403410b400740d01e20000b58003e5440c203c80c003024107400d46039002d0441c503034000c0d070141d9100440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183242275 1250 183241025 183241027
    0x6150b0705010b12030a170c120103030f18060516111017060613030b070504090f020702030d03050603190204060e0c0307020708071203080703110301081b09060120070506 75
    0x101e0400e9402490307281e010500845100e41e85000190004c411103c0f200c89546401e031a0303840c03a00c85d08011080081c448810440304110100b40d1034000315070640250310a6980c11004100094003c00c440140584003802208c0d01c1024000c05801005940d2602140c0385080e113001c9042c180200c42c0341061030718039008001c0d14030070004580d000200c81690040c0100707030746864860301d040c40b2135446019404148114561010b100260402144e030360807004a02d407290400b07441e480340c04201c444120300300400c183d0003d0304400b14142030200607482500d60804000d140342210100303440700d001c03040c80041102020b644104550741c9900003405420308040c502c030f003854550001303110342e8000e07102076001d4030640c2c00004520000291070019a042c0399600d40741504159230507954120007408000c140760722481071802d00005200654000d103031440c01055050f00610b820f041d10015082950701400c00300d810042c0c0351340c01c0001041f582e0ba2295aa01d0700e04445802c1c2401c0949607000107502542c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183243525 1250 183242275 183242287
    0x9050a180617030307120e010c0f0e15180d0605040b100902040503030403110d020916200d0e011106070314010602010b0d030e030a150c080f100306150b 67
    0x149284080949440d68008100e0140c03100e84074102d42254200e80005607000b0400120724610074029803400921240c0086900340100b07600b04e01b900c5070351071448001022804000010356010003944c5a4141c1690703003d51642000001c8080c81c0705a100000300050303451041c644540300e074102502000d4200c642049942000e01d018085044185c98400100c0c20081000c5030f0703240766108481c00c480b0010000c510b4603181d1703610814101916626542d11161205d86040961580040c0a20440100b200c030900744510500180101d842d5902030103c0280540c031001c18840d00281940000c009400d000d0034192524004032203038550380d101e140c0d07540a10700510200c9a0540c00c000d8041c92100c200e884140e032a003178120300700c820001e2480c0d4042c108c6010032010a0150800d034403890409415249089090f8940008000c1c040b01b07652a20350392140141d41d0b495001182580082016020154078100080f0303001002a80f40800343c85940d41707040100c4803500c0518030400030b10104454549487c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183244775 1250 183243525 183243539
    0x120e010204080601080d1b15090b01031502040806010302060c0f100509070b030609042406080a060b0102120d0f15060509030c010822080c01050415060b0304120f09050a 74
    0x740041c800c02140384100030003c502d162000c2542100f003006696050050b04460000c40c1490f00000400e03103220540c01c1c41c07070f4121007181c00741406076400394000b6049545903183c200780e482d210803a00100c10f407042c07005201d9041e001c1134140c11260116941d60b103a18500446038103040f9014080d54045c440c4811196190350300d0b0300300c3d0b440364201400359105c0607550700800d42c9030b00c0229192039201c05048000f80014040e020568101c0c210401082c00c442c100654040c00c40d115608481541d501c06903040e820004180a070401c00781f420320207010302001c112640d10315405041ea2104207280c40c1c0f107040d41c14058a5000c1c4c82c1c00303100921550515903484101900d00d501c5180e80354024042c0c0102ca010179401080414018040004049104000c400b02000004241441280c0c1d40004101d503110b021400d01507a07008602440d1800241c62081580309c0c101e804075400b140b480c2c2030500410001c00d040c00c0e44800c1c00e6069080c50340d9502c104200403035943c10a6000142c0c8403103800e801065034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183246025 1250 183244775 183244777
    0x140f010507180915170c03070b0409060816170f010507170a141302060702060a05030105030f0a050a02010c110d050304080c0108060a030318090218041107020a0510120e0102 76
    0x40c038031003040b03103030340342d1841a05070f070b418262108102200f20010800c5145020100008010a00590b808000030b200068102823044d4011a07501310702140611402c0d100e0b1084000809102000385000c2c0200d51071111608181e108520301028070116514004030103101700d00e02c0c181400d000300024500742c0c9001d000007060144590300e05c402c0000140b00810b0341d03c141d11703101b04040c01c60086c40e42c810030a02450f1041c1d050498010f1028080c83c0c006854540c00703020f2443c9a615199165030621060620744200350848400740c0c4d0000962a000c18804201240043d40a1a003078501002c9030400c182201442d00303059800103d50010302040c480c0110260060313035419415035400c440144011100305800740c540c81da001040032002c0002901403600503540901c03123030101855a076580350130310032078105103c509510f1101410007030343c624080c420b03059440c0a4079070060501c0e003640c000c20000d15080c06103601414240d0b0324121004c0c09806042d0809070503050520003440403070403403070203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183247275 1250 183246025 183246047
    0x1309050708010e160c0809060d02130302041407050d02090d0503031e090a0503030a050a1404120206240f0307050409050a02030c100503042a15080105010503060d140f010507 76
    0x20000c1c803c000c541075003986040c4041d140e1a568841d51250700548a2031042e504c503411580c2d0003c5c08200e621000f03c0240080c060481c4d5040780100f00c0d80c03960060100351074040700c404444012250030001c41d0381e00002a2503100340d001304010703200c0d9141c0f000f261501e1821040030306548008000c000040c103060510205004000341d0f420820380b101d45a90348c2d0368805000c000c049070014400101003400c15400b0030b510804440000c00c3c0c8110b071059501845409a400b0350b2041d1a0040b98005503804004003030308061000200c880c0072884d01c0840803421f0b030343c503000781c8201d13644021840b4aa504101180160400070001c101c40941c601e8181d642d15005103089000c1d01618102e075805141c940c0300e40d140d011054a44914659565907080000d44900218a00811210324450b41103281c00303031200003a0806010100070314403480005005800d051740039a04101040003080840e031640c642507207a103a0b0040c001c540c07040c0941c0103181030100034200200d103586003501b00b108007030f070207110707040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183248525 1250 183247275 183247289
    0x16050106030816030e0301020c0312101e1d0c03070c170f090301050a0e0a020603040c03080a2a0c0b1606091b06080f0f06060c0a05101a0312130905070801 68
    0x4607003805d082418241c0c0205150307004190030600003100011a10b20460b0b5000300071090301001e0300e44840f000484407841500310290614481028450003100c0d546a95050b242c69442d8003151800b503503d504c00f0700c801410320f0100070b520540b84003040301811180b0143e00100002d2a01d030704620407825030035086491140d22035801e24001c0340c4009846c0c8142820282004080c02840000350240101948064800c44000160300400400303c2d000350040e12440c0c00300d07a2558855200030344020031009407207500c17230100498a01d00d480010b00c0c0040420465403c0d40d0541d48682c0e114004d001605441e050140c40642008142c0b000c0000890501014400303000e801c2c05c49540744c000895103e4011155000989002004a40c2010001c60000c0d030040b00105264641504804607504000b4280c03001c8800f0381c40303000310100040c031301d0080b4070403030102c0c4031003d0540c0101710000303170348170025004042450000140340c1465154201d9102c050003030034400384214180b40d4001412050709100f542 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183249775 1250 183248525 183248537
    0x11120c0114012304050907050103111201320d12090e04050304090e030301030c1404020903030d06090e0307020604090f0e0a0b061003020c0307020405060102100f0e0607020708031605010603081603 86
    0x443c80d1816204882c01003251400030a142400c2c40010350041100d800f084803103c00900ca8403c01c803c0805015000c2c2c0041d0f40044598044041d181410018010f1207681d030300300103040724040341c0b0fa61100c155400c0d085042d00b50901c0c241d4406807146074a0780c021019010048d020481400000801002150482402044519070107212580c0300e000c00e000c0101000b0a5003010400400282c8803c122644c004000600d0510120300082c03031644184c00780f869007510340b03004000d1100c0718464411681003101c09946444840d07400619a403003240a040404e6507603070300007004888564000007050010100725070f62050b50382000c44010801300c44051041c404880e0f6851154803038002c1d00d540b4290744005608043e1240c1c2004090000103104604507c42c509a03040350200c280070324003ca540114000540503028000c0e2410500003d01e10810355000c032030100641c49002085a20301d5240884600c1d02c094071f4039010713016124660020303110480101c2c04070481c5002240344504c4600c03c1d1610 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183251025 1250 183249775 183249839
    0x40b030a0c0f060305010501051b15041a07091a0309010608070b1e0a050a03091b0f0e06060f03010302011809050c04080606010c08090409020415090b1011120c011401 73
    0x444c00e9403002d0050380e0000b14180054030228031044120700000004400780c0b4518084480d4400140004407401e07503120406030200c60403c820124026000400380c0381007011581070070008200c4a50051050420103400000100c807082d0a60050025040360015502880c1ea1880b100319150043d5600003c1c40d08401c001c1d1070150807003400c0756112125078903a40d081a22102c4154010400d0500030344090251003c5140c0900280103000e0141c100052840e85aa052480c0a0b0400000038985805600b0421101d102507846000b680d045950920f02401d0841c102011821068131650255504c01e080c001485890060340c0c01400580d003110781101c0f09a5264801100c98509003400904411300800200328681456045502c006002805c089110186103d07000102d07910741c0c1c400c000c031036a6807082055518121800981ca00381914113000c42d95401301990340c440d0700c190460305000000003000d4104890a401030030180c003140100a00940c1c4d135104041000e42c20007a546240fa03811408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183252275 1250 183251025 183251027
    0x807030b0d0204050405030d05070216090b060906090d0f030302031626060103060503150603060705031b07150504030f02101103191407021b1005070f02040b030a0c0f06 74
    0x56191501002001e4007404406a02030100401e00034000b540d9a01040001c454044414040d460144015600074040c1129030300721034540d40b046400a40c001802c00c40c003444c883d130b1503606840700301008440e416618a4013000060000d480a80028200c036041c000003014140c00d0b0b07016500c07412140b050703848900b10301c405c12120315048410b44c9a414240c1503481a440503a4860650f0101060600061160f01e90f000249000e02000003858000701c0030040001504050254a0f00320705c6034107000c1d00f0360034841c41c1c00382c0000c19822a000488000300790380d0305101c0d01c03044444540015140c02c00150400e07040092142e030466080030054070416200000e06241880f80e40320381e010f2582c0c0e1300e0644c0c83e41c54058888410015a4040701502c444810071810700e00321045000780c0203500100780c60314900b9146070713504141840c05071042641c5000000e66607008000c5451165201140850441941c4005002021191800354240c4100201c0c0410031843c00d4100081d1000c14940c08640759581360 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183253525 1250 183252275 183252281
    0xf0605040e06181801060b040e0103050c06030c070b0705070c140307080c0d110a0807061d0f1003021b0601080f01110405010906080405010603060f0209042f090d0605090102030601080703 82
    0xc0c03e40c0c000c0442000810200b40591160110810f40c0300214405990710706060041d0402c0d0801c205210401c0c00400030008100060f4051401c00d5030400e0451400d4518181180511180507108a814100140050340702d5000c80e49240e5000c03036a4100c0c0c03a02e030030f903010003098200c1740607000703204544011810b5440007407212501000186180482080d50752001c10048041031003681050007450049903580040c480750707001e402c5550710000c035141c1258200c141c1600404956020300d48070244000f040e00e81e000d5010350b40f015810b0160362220111a03080364601a024400300c1805001e00100d00070001103003220440c0010700090020000111444c9818801c0d0303c185400304807581000c100090060041c160b00502803800014016a01d45039103007a914907064007a007071a8005000001da1a1a10414681504a00300d490000501c2880088009a241c1c80e50307480b19001304904900b69a00c000040185a021006010509012462a010750416983c0c14040303140d01c0f0020307507518801c1c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183254775 1250 183253525 183253549
    0x30b0409020f0607110d080702010f050405100f02190c051306080a0230150108010c080601030e16080d0801081605040c0c02030d11060903040f03110102070f0605040e06 74
    0x80074031001e00a941c04104003640400011035145d186100901815541c0c0c203902d4490a014491043d03945840e407000400e41d412480780201400300900c014855600e0391005110b20f020a801d0981c02e4411000c42070f40340081c41842410000e03008114401080601e840308422200151041c209800c4d10b042e0880c142c6107036000700c00844c0e0107400c804003d440d00114070035882c656019100d10102c802039011f06592041e1349180d04590010340b5240c204089030b40032a0041404c94020000a80242801014040e02818090400d070300d070b4044030b0b281101405600400c80c14401141c800030740c0c0d01c0c1e400e03407502c14500d80741c00401c6064000103204040030898680c07141c0031480000d0501c0c100400c1100501c01a6030141c00c103c180005500140c504100c483c50204440d1240c0b88030301c1300d103840c4500e0f245008280c3c075016041484100014080011440f05490780f00703880e2130114945000403460142998851a056540658001030503900400280180c4404010410155841e0010b02c00300d1700c060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183256025 1250 183254775 183254779
    0x305070602070201050714031c0e06060405090c040606030608060a110f03070c0804060225050a29030708090d030c05030105060912010507031508060106081f0f03060c030b040902 78
    0x810081000455980c01810810703c1418014102001d545030303030980700344140c4004401c1e40f0000e050100018546030080010080000c24048010a901d400d0f8451700c024100c00e014503200d4001c1000320a0900012440b00c4015104200c070560351440200545031610560340c1500489020030103001c424002c010180ca11766000916100b010310b0600c02550000780001c0800504001840020300c03c07200820060100d6801414450405100101e200c00c0c04501a040c0001001040005488070b124450840341010384001c001d4800d40b44000e0000c040d00d1100039940c9001040211050700300c21528050489901118180b0701c18040640840d41d009400c0408100240b004024a1801d4401018402c40141503c20540030130b0f20400d080d00d000303890701c2d40840e4550440b80e01d665a00506580100f200400616480d45400c00c00fa189840140010440c1200761528100c0060b4408480b0020540440d0a62103207070349091050061000503807600004e03041c105803450074a8540200d41c4042c1d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183257275 1250 183256025 183256027
    0x81204031b05041505090708100b0906092e0f0e120a05070b03070e0303031006030518060403091a1e1813020304020306010b0a05070b1b0a090e060a030305 68
    0x940d16088010612100521030080240c240441c2d151034a004582d14001d20b05040f0002074100b0b810440728410040c159401c000c011010000410303c80d80d52242254200704540d80c3c4c0d43c5825003c2030b06441070500e000d8108440581d00c1600190001c141e00f550328030f410342008924060001200e65a8611050f000003400d9131410407108e00e00101d44dc0e03962041007080b2094045ca60b6a030600b00310865110284c4440d01004004103950052446c25468004502031495494a00d0301c000840c80d581c000c0e0400c059940300062030075804280c1703100020303031075038200c0f0460324080c50700804a80042c05582c4480f250714110840b03850040060724594100f05c04c05800e00c401c0140340c0225500402c00c40100c203185103c9100352920381212008116a61410260f520701d000d005141c48c1000c1031340400381a01d4200004a5009c1d0303c04256640680d00c1030030410251155100500b0605081d400103400c1000011001300c0c0e203800c0303820032044400d0401190055900c400810030140505d00c005000301d60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183258525 1250 183257275 183257279
    0x91f03060e0408091c0b0708060f0f0d2604170d0306050f150d110403170a050d1104030819080105030c10121b020304090506031f1812030213081204 65
    0x9028883c0c840710350f40c0d800d03010711500141d81b1500108013054805c0c00201c0c004105200950030421420f201001c01a29041003c0c10910080340440b201800d018041585e06c2400090380044880d80009101b10550b189889645a81d0743c11142c0050000541140c400c41c11040c8800d0302a002c1e40c0c0460318020300040361000841c09112003824210141e00f129141000260703191035143c4070b106401d0280007841501d403400d510f41340c117030380f00340d0b00404203101010f0051504a541c040d045681f00344504202041c0b00c1d05070b02940c03079140603a030030040c4a0400810310398280400800a03110b0580c5c21796900003943d9136001415107510b1030400c07050300044241c566004c0c1c0b07070180d03081c40010f01590500140311407d084282107250681e88081c40142c00024041041306841c1c050a03030401000c80103490301d4404200c1c0d000c030b400715030300d0000ca5454032850003920146500500d81c00031a00010304e4a84c00c180e210000b0f0095100e4000b0400b419010b4401184515000548150440102400c1c4e86454 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183259775 1250 183258525 183258529
    0x706140f1302090a2d0c0834020a02031203060915060409110d050c070506180309040f0212010b040f120206180d050a08180619030c05091f03060e040809 67
    0xc904045d052104510029014905c1c03041250703080e4105112000502e075030340030002004450090f00c4510100c40341d44100b1810f84580003010304600d000000010304954114040c0e00344035113000d0182d4140200d0b802c180c24940004002c0d40f0449044500c44c0e10755944064003441c1001c540f41e46904080280401e01c507000309a0300803005110619146810664070721400c00507550229030a904000d000303e19401040004c00116030450145482020780b0130340c201c50b90359240100890280f1481e10744d0581c15103d44c06504850402d2840c1c0c3c9441140d41c3c542031740e0b4510758450320070311010320301e0040c00103407003e9826074401c03038507500406103881c009000003618290a0b18142c0c9a03032228074106810001b80c010442c1189481c425040c146c1c844180c004803580304c014848501d40551401c000ca60000106001c2650002d140f80c18000340c084286c14040701c183c003c2c4006a0703000783d032100e41508520740792400701030b0032081641c1c28029a916620b01054050781503400510304001417110100754 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183261025 1250 183259775 183259781
    0x20703020108071101020309010e010b03060f04030807120510080c0105040b0d0213050d050d1205060d03080702070909060b030c0415030f02011e0e03060601020705150f0706140f1302090a 82
    0x407070b80f54600700c20784030f038150100341c220f030300603628010241e64682c580e41c1c10f1402030041c81c2d441c1000b02d0180015152910040204100041c00141040400000244960700801002e50310b1030078100d040107a86084d82e00b241400d806c6008455040c4120054100c10f580b00e0800c5030142c903101e0a5403802c0c02c00c0a101300005e50071201c6104617020b41100045400d498140c0380c0e1403554000e0004041c1d0740906600606032066140783c0e00089424070f401c000c4113448180e43c64030000c0c0d0500d0803e82d03e50360141c0c124103200c80c07074200322051420700d0240c0c0203004450300310074031502c0103d007520004440d075030420086440d20b0068070110724074050200045070342c0d60200340c1a28010b0508041d20780442c98801d4a01d07100c0c00f134140c0400c501c105006210b040c10090300e54401020300003801780904003000903802c490a2010422902000a80320010023501415200305035403014052100c1080000c0d4010b02d104201c484a220034100d00c0007440c14418061b44075015500a85034071415141d414120000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183262275 1250 183261025 183261031
    0x60e0103090203033f01030c0501110a050105010605070204150501271203050301170109020f10031506020a14010902010507030804110910091d07170a1a19020a020703020108 76
    0x1141c003003405010042000b490b0f00c10120038584030404051030142c1742200340444400048142c2c0781c1003200500010b0540e002100588400742010f00c0c01e16000c00b219441c003060040000e11550800000103005038100002d09480d83c8219800d00121814000d4224840594440c3c4d50005490100d24000740d0981060401a01e80d42c8500c0803406440345080041503100d844100c0010f04008010002000e40107010820f21000c100240010822500094904030030420344d00c0c400c0800300c43d1044038600a0340b00c90710410364000b004100d184c0d00c00010b5100c460244083e50b050704900111452264180b0032740c83c40e140d050711001e00f8280c4980302281c0c0c1d01e900900499010050204510301ca90718441294416100c40a00200780b90811169070150382810410403a0040340802005030484080f070320350140e90300c10340ca0007084800e40c0d807070a02d08011f40c007026118403038040d00b400b94068422001442130007480d11800411030003042050803803244190201c016001490280019841242ea03250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183263525 1250 183262275 183262279
    0x17130b090f0f0303100e10061101061206050a050106021c0c080409090507180b01090b0705030f1201140f0108191506020a12090302060403080f160308041a01060e01030902 75
    0x5141c2980000145052641a00344540703074408402c2150102c02104903502804c003245a402c01e5042c41e40300c3c18848841401140c05000c0360a04e001c10401d003d41c000f500401c03410440b001440d11506068009090946214840900340b00001c2240c0b400041d1105403628140220000c1300c444680031a161070005e00308440c4200d0800000445030158000c900c0f80c1c0d409000a07003641807030260061901c402001480c03071a1410181210170680e04408454110743c28031001e01d07526000b61514a007544984024a025250081682507540f01104103490681d50307442c245400341511076040042c1507010700400e03400a503050000030fa00300c04003800b2401120501102103600302c000600c01100b004d40d42c21200040c1d2045008a090204614041000740b03154180608800d0450b00480d096109a0201902c4240005207451002841008464040c8007c0d15200044841807070005e00e642402e89054903546043c0c00d091411b03985001c00d16048030410f4981c49001064000150050181684103076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183264775 1250 183263525 183263533
    0x71202070b010b032a161104050c0301080708010513080d0624080604051003080304032d08060102010c020304090e0703120f020d0309050a0b0a02090406060f17130b09 73
    0x5850744074454060302110790a15100c1c80d11041418443c2074072100c205000300141d40f110124210141103a8400c1510b980d41a4400c200d0f017080400f4601c110b00081c3c02502d840100040c00c294540614142d42030303c0142c8842c56501c0c1045401d940d003e640c0c84404452302c00c0380380c0002d0921002480b001402400c0400e86c260f90710304285082e0128000261556800071031007060302d034004038095011100301c03002c0000f4242494039135000c2c0800d0000512410b400404601070600800040049030344040c02021400100039118507203c001005080204032100003092080d030040c050f2000c1c21000d0741c02141001d01d40323a001070207051500300d917150500a0368400b00108113149210450391805889006407039226202c001d00c0c100025103404101850003403800002840451403a859070b8103c07a800d0340320307241d0300d03080300007403140c0891a0350080c2b61580001d030a0b6046050083c1d040b070f150326080c3d02840d11642e0707003540f42070803200003002c1c074003142030354001545000c075068000390200122 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183266025 1250 183264775 183264787
    0x905010309020315041104180c0b0717070302010b010f0305150603060406050301050a05041101232a0a020102010b010c1109070c020d0308040b061002030d32010512030f03071202 78
    0x1480c10110aa600f075481e404000d46c03100362424180102d4901c0c20f8940c209481c1c1c1c040b50f48072901000110b0041c40c190381d00028212003400664017032200440c001048d003964660319071034041c1c028000352920b0340c01309071180d041400840c001c0c81a03030700c00d002d07800c014400c400d6003c040001641c801420f060b8000d0ba41d00010480d51403d01c2074510480000d04005298207203410513506018a25052034100120000140013115042d56010140ca502204040e01da002c400101d00c60420321000c00300150851181400400d1000100c10318154000e170000c002c0450b0003c01142d08582c1032202030842e04601000175818140111035550210540c5025200303507030b2550000301007a0270310300b060700010307141c034203000611583c036040541101c4101c80f0f242d070502200b07102075124001d050031700c0402c580c1c1d40c0071100f01d031440545001c005e2290301c21104030800703102c0d52000f00180a001e00c0c0c1c003c0c0c040c600c0c0f291010070004212200b1500083c041c0342551b4070310070200c9015441c01a11003000d0303001d1000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183267275 1250 183266025 183266053
    0x1b030c190b131a070f06020a0c08160308010915060806060906130f050126040c091e0509030a210207060903030914160501050c01111602010207060e0109050103090203 73
    0x34064900442c0d20780074100e03107000c5032440e04031520f500b1010700c10390401c2010000741d10412a448540d038406005070300c2c6c03034850350181c85410b401d000252216100050451035100c0c400c084408203071094680300c40300e9888154003002c1b1900e09200e82e48001d42050280901c0b4094101154070a030000c0901c1c2c90880d00c400450041d82242040b03140b00102900305101c0c0040040400c0c02500c0b080c41c1204000400c040c884940e48900318250045181c07803004a400d000c0d10511000244c038482e81c0502c07504404503d1104907444840300c200a00e450600801c00940002c1704a0f55910b50f00d0348c410121035903040a8203100c0090720000d558a6030308000650004800e8040c244084d4000d840004105805017443d121142c03800300009030b55000140703d4040c1c201170140a03015144286803454541c685800703980d0042c60940701c1d14000e101c011817100d40b40c0209030110b401a510070b030f0039141241d503200c4003500c846651012090102c0c41c881e1041c001544a540200102030000301240d4110b150016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183268525 1250 183267275 183267277
    0x8030f1b070803090a0e070927050c0c1e030316020f0d0216060302091807020307061508150907090207020a05130501050f030a080d05060604081203091b030c190b 71
    0x8000340390b80e040422042d0980c585071030040700820003e4604411071038103500040c219001401900b00043c0c0302e1165000c2d1001c808100424000003190820550400074040125508541300d106000c2c810040b540540e640705030814034208007440020350a51b00c4000480c02c040303500c039140304214494006041d6924100308089040d440349900608070222a6007410400f29100740c00960515004004819581e11520f46c40b10329443c0301824000756440d1004224110300c078240b0090502c90074105c4504c02001d0394801d5108035592103040399800c240c112548000c08508955055040e0403001b41003002d41504c0d0003d080280c4002c04d0343d50265254000911035490400042c0d034050350703c1005000508144a1140d40701404070300501c01c110260b43c50141501c030b840d280c002c1141d201c10208119450310025240500600400e45102c0300c0da0601a08958100322800c42c0f16102d0b42c0301c0c04c85441d100101711020080c0c084c0180102c010003d092000010042046080c640c84045001504c40700d240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183269775 1250 183268525 183268529
    0x81602011b030203010e1819030203130803190806330301091e29180117010506040b0a1e091803030f110301180f0c0f0f020708030f1b07 60
    0x28600603125410b00051004c106c41c0100724450402c44074000805040c070004201300380c0000c1b6000040c1d546c002d40380481c154000e2549859076405000c00c08140300c800032000d0680001c413840c4039003030100442f00072500d180c010b43c0d07640d401c40c4242c036455105a05440090041300b103820814041ea544074141211540c2c4241d1007442030035518001e03100c003890000385580036281403040c14170000444400040351f1540381ca440d408900c1c2001003080303240e200c1032860302698120214140041d80e48051000e22050209400c1d003c0794a000e0001d070492405114811001c1d4000e00014500d508142e1004c0c0d51051543e6030f1b20341d04501c80400a00840140905032186806810034a010401403a0150507244044004108a03041c1505102079070340c2c94050780e04480ca0001039520911540400304004c00d58140035960382424107802410264000c80415003144180d92200b02c29182c0b0303241281c030340c680c0303000300070050700204800c4651034141c0003d410340800c0d0b60301040c03000181d1a42c052802e2581e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183271025 1250 183269775 183269777
    0xb04061112090f0705060d1e060801020903242409010602010b0f0303030f06010c020111010c0e0a0b0310051504120f140303090604020418020402030a15050d0201081602011b 76
    0x30004111502005100b441445001c8000400c580c45c01c110010f0018040d40780c0118001c5c0c6d682504151924820f50b0461026000c0c11003002040c0c2c6640c503440c041d611280d031281c064842d0700200d92248850b006054203026598075908155200d1588207a000c0240380c000401c0e10030081258642951503018060083c50300c0e03000050400030745400e0200c107800600405210b50030610810001c140501c14469200802b483c004003040310134801a6440b102200a6044540c6400740340c248642c0c21000315141000c3c22103070201d603580d031010a8805880200c0744642c0b01c2244007020000c9062400300800c40030042035115040540718003200610505a03107080d110400d805030240e06015801a02c210040000b401941c6989000e03e1090750305c1c800a04028080c55441004071000082c0c0c0c030741c1d45510ba07030040040d5903e0034a4540c50010300030048640101985007080001c1e81d1402a0200039415810f13122250240e0721041403140341c0407034551a000b1355403140c00d040d02c0c20205042d4510303070041c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183272275 1250 183271025 183271057
    0x60e010c06090b0f09120a020307060917130509060607050a06090606091515030203010e1602030409020a0507060c022d07091b03060821070302010b0a0602010c030f0b0d0b040611 78
    0x445d078162070110322650007088a0b80c20448111125808411200c2d1981c12090218480f0041c1c0b8182d10700d03450b440310209440e0004100781713469661b0f408050044840803148a40103031039480410019203d035802c01000c41c0d00a0021000040d40c82e0084203445004d81000a10160b4a81690054603003918044019829030039042c4140e40c40110302d0181124986002c50642d810003921a610901c0642900305824200c10b2500354a03108104903009000102e07801e54682d041c014010f840d0740c20501c022a101400c3c400c082c0d41c1c103440000c4514050a240300e46901d41170560450555a0617100c0007821140035a800100c1da212290080c07643c020007401d64165802d80701d010060480f00a40c0002c2c140360000d0140c030201d9403201054a02c1c2050003201150303500420324080c1e0041174200d40720b030303005034440d0300c0040e03815019841038505003007688080c40b00460300311005040310002e41c2d030154000814020075000c50507054000da8001d01c40d040004280000d1074152140b60894100380880d012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183273381 1106 183272275 183272281
    0x12080c0f1b0f0a0506070c02040209090106020601030b010b0702030c010509010c240f06050a21080f190804150216020901080a0c080304060e010c06090b0f 68
    0x603040504960300c1c04604100c1040c0324045100710389030302512000c0c240d000c0c00861a83c00c029844400741c030555440d0308003510320a8207942d040c0e820680c05d100700b4110791183e03d10b59000e8191a0000c1c000c6600d5460410219881604283c20300c20041c071003000143c9001400d81d18a990909045480f034200701c0040702e05407031072140030302000da01c0d0490982d071442460700d50500300303401a000c0c40f0340006001e010095801601c030b59508105e404c8001c1090414030044040c0c04184c0d4100c0910400f03082c1c8034038445420080a40b1014800040c8003c003542d03c4400c880e002ca03407503040c40d4005240c207485100c240c5450002c1103002c03a400141c44da5080c1512000c80110f168001c0c2540c010396181c0c44020341e0340741c00f242c04440500356100003041c0381c0b400105440880d81c940d03407030460b000e180c0001180c00c007541207000c890107a02e0b500c900b800910404007092155002003412a944c0c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 183093525 183273381 := by
  have h0 := BRFrame.cov_init 183093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183093525 ≤ n) (h2 : n < 183273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
