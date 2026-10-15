-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:24.949171+00:00
-- url     : https://prove2.me/submissions/48666909-2b01-406c-8113-47a71497f7a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 770503597 ≤ n < 770683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 770504847 1250 770503597 770503609
    0xc11070303110709140103060b040e0615040b060c150c03040804051302070609030e01080108071802090103020426100c0c0f0204060b0403061401151202070512160501140105 76
    0xc440501007002c065020504000248100c0700103040480013081a40c16450300b0242da02000d10080d54198a0302010b00241d0504c1e0261080c01c004200107000e25590f861403a803942c299481a03240c0040c1e49040608040e200d0200918899690200400d0240700303001191040200040000c01c40550034000d00c40011092003c0e1030a41d00100d59603004800c056280320001d008210307001d41800d080400070300506800c812130140441c8283e03960006680c944401c0c640d18141885003407800c0030b0410314480c018100d6409083ca070b5005140240c0382c242d4542c0314214007610500c280c0721110b40d5000c0703444180420400100f0526084c042400b11440e4500c0282503012007a0000d00900e041743c144d2011540c0e07582c0414003904003072400c6512541c980c1403440c010040c00d50f1071000c0f082d80b00000b040c080000d09902e407469406980d00c1c910f00a03080360220203900312100484061150301c010080d00350305138002c0c182040d10010144030a07942070510070700f5a05a50030740f40000420800500490301c0701d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 770506097 1250 770504847 770504849
    0x10f05030f0903070f030e19050d080d021209060702010f0c0f110a080406030903110105040b13061803030b1f020c01050a11070305150717040f03030b220c1107 70
    0x4041d92a0310b82c0c85150329815845803074801040402041d03188410143c010520031500720003582d40c081047c04540100031454460b0141c6076008425070140400987c503c030040000400d10107000d820400b01c0c18450a00c080b059403c04900e07040300703081206050782440354141030802064140000703900210301408410284800d01c0130001c406201c0406c0440421259207101e520402d9182c2e52036a402e8000c00a0907550f2084001031041c00310002501014062a4080c2c1d4020681c90002d480b494240201c0c451641400c0300c82c03944440261180328800491284061300988010401c1d50146040012440c076a000c0b01d951518003110100ca403e0f4005900740c510301303007803c00c1e6541d180440015100040050300710074242c45910340c0030007080400301c0d01c0f28540e40e07c0d02d0440031648940d50195204080d003520703281c5c0c10303020800040120329001d0108a036135001e170900181e905c0c6520041244901c11000b076402c460002000200c0c43c0e00648505002001d992034140741041c0d9103880c0d29120310351 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 770507347 1250 770506097 770506111
    0x13020d020603070e10030501080d0c150507020a0f060501050406270e0a0f110301200702150d050a0b100306050d0b060a0f0609030b060103020721023306010f0503 71
    0x804000680c0f2140502009400700d0801040842c2003014144010003414090084680390302880d0440c41905000b000d03000e002961110100b42c528031440c140d1802058000c11034000c40c840c400c0b0b400302080400e45031044031806501c001c259981088103220554905604c60541034078041c40742d00b00242280807c101d5818a07038030203d50354150100bc20328142c125017014049464001840042144640307008000e01416002440b001c0000f00711042203000d01c3c1c001059a8004020b07120040c40c00101c4450301e007503001070103030511080078240402c5a038122003150013039903070700342400305403030b06454984016100340f409100e103d0520003c1003c802c10078000804202c18140440c0c1645e0320000040d001d800c844114680990342c40c2402006540e4900c410348007110706201045095100e40225404035030424003c0b15074140c2104101c00e2000704603204021070045050202c00d220b04078400200803105a84000d505240e4082c0000100c40e0190086040c0481d40e0401c0300c0150304881540c0e80241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 770508597 1250 770507347 770507359
    0x90b070f030311270f0a0611151f1a04090b04020f1908130c061206050301050c0c07210b040302030c19030314060a14033313020d02 58
    0x803526068015040c00c0b800c00c111110081a403010b800704201804102c03003100f0551003420001d99080c8049040f81c2d051441d04650110000d00020b4060b154042c0c08880c4442100c8800c01702110752038a5180680346410307031001c808401580924429585005420350814400c911300251614140c148554401c4441094680c0c0d5090300d280ea07590706881d440c008038a0155903902480c20300301c0f0031418100301180850510800320f541c01c2000c201110105038000301c0791a00340c4c02c0103405d45984141100c4a0943c0d40c42e0700c008251500c0a00440c0e0080d500740d00b00310340311181070043d107003005260340081d144082d070b042000801032251001d1140072608509070300343d03540303490070101c1c1540304284d41135426216a0b001007480403160003d0080141c02a0b5040000081a51030350011074000e40d851030b8001407280d002d0141600f0004d001000481c001d0460f07854150714007055050000c0082100f0f212082a210700e94660714000e0203640c088072200214000d01003079400102040380396200603018407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 770509847 1250 770508597 770508623
    0x70e032e0609020328050601020c04020c03090a03030509032503020f0105041211100305061503060d050a0605041109011d04081605210c030316091d06030d090b07 71
    0x80154031000140038503030415543c0b8a007004071401d400500f03a803503040141700fa40c04030844135072500c42c0c0d038042d0905a001e4590591890308000c06908807071501307541800200000402640c4003450140218400d407a81c5484081003400c142c10641400a440001d400c490007206244288803012010342c1d90465040c032412844200403181c0c3d0040780c101c10f01d040c4070403a260083c42010580a003c2d003174103c0e1030100d41c07403441c101182900e20075905150404928500030550000d00000303554804005000c0824048858640350328144041b40d09070399460b50f0b0b01c18401885a40c032018030760200182d4866482d949400500c1c00300d0500800030f000021071360000700c0c08201e03a0b10304580755291400c1a001e2001a5401c00c292100c640350300c821102c504240343c1a84a0840c502560a0040304070051401c0d607507004c04450052000b10394800c100b082d85800400c0d150801340a1442070f07010b88224003602d00d44034048c14508103415a944040c01000307541040306c14540011180d11592142c8201000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 770511097 1250 770509847 770509933
    0xd0e060d150b0903012a120b0406030b0405011503030807051809011e0806062101090f080c0706023d0f091b0302060301120f0f0b070e03 60
    0x3003503042411005051014400110180c0d542c000c1c0c035101c182140200401d08a0026020880020200204c0940d000500c610115030041d21241c0c0a0710070070201060707402020000030110b40e40c9400454188009605001c181b080c24480c1c2120b00000340d401c174154a0a60703c001d4020b00006003000c08100c400102c4030b4403a0407200d4650541100031300502d0b21540c550602c00c043e16450034800c0c2c0c1041c0100c0c40002c41040c001211802010003030b1543d04604822040040d24560f0b0603588040745d0b40302d82c405000030b1882880500080d0044a005844094149040d414540154400404c40d407040400c144c4143c003091051000c16444008124800040d06000515000c41c0b403288909905d40b41140102040503000104500d200f000700c40d082e0426000c120719800795178040690050010300042c80341150081e00300181e140210040409840d1a50392030000040d22101141c0d518403407000d0151094001c1280c85c0750180c202c001d0440100602480661079682e01e00780121a0020881180a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 770512347 1250 770511097 770511101
    0x51c020f01050106050304150519020904020f040306050f18100e01140106050301080c03010e070306092f0a0503152a0304120e10232a0105090d0e060d 66
    0x100d5204100207000a40c0d40b00405042c1d50011a070540715034801c640c40032582c115501c100c034804c42501c5480008124150740c403000a4120781002c0360416820406004016080070141004500c206c2d03012816107401c0c070030900e0810001d0004041d1001d9030146a0714810086240300581c207021100250b46048030010a016000e4001080300206443c000455116408401141620102030403a44203003106000c0c9400c98440441851140d0804038052002503450b400c0401e04500602c010030510440c0002e94000c10711112400200c3e4a031102d8200190901c02c80010043c88103c000d06000b80b074004044014560003440d07003200e41c1c0c80c01c00f0700c00c10f08021000e106d031042452840a07100d2070180380103100404650b0101010440680d1400341c2446c11440e2041416201e80e01e16200c000580b1400c0004804c01e680201c44e64014054421000d81c001d4401501c0e41d030131001008484071500e00d050845001400c51201034105085045c0b109400145403400710005440065940104004400c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 770513597 1250 770512347 770512363
    0x907050702130204240306080d080c0f040b0a02010b180c07060e010609020a0e090615120601090302060705060718051c110d0b07020c0a0608010b090a091b09090603051c02 75
    0x500460010a040e1203041703850343c00c0300308250b58030104111521100349650f50b01d00c080c410800200c8040000324034440c15005405680364250741e160a00307496418601d060b4015121820043c0e40d00c5407030b0300c40387c40c20f0b000104100b02a80f0140c0400d0609000c080704070311a18102034074058650702c6103440c1c50310035030000d0024224564115261661002d0050204005c0120319205016000c0800e03120301c1d2141c255034601c82d41407901450590505440180b0f0300e0010601814040001c03000005038a40703074000c0c040d06104a007e4030080c6880000500490301c4c05044001c2d11682420a000c0d58841080c80170b0f6001c03080039a41e03076407840780c5840c848004c51001095000f41e03008426004018051000318010316040d0240e5141c038030540181300560520b80701e810000f50801004001d800481030003002c000c80003405407045143c50704089400d4074a084001050b00b107191001d0340701103520084940141c80c940138180105442c40d00c40382e58070b54080421a0084260280d0003030000e000300500c107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 770514847 1250 770513597 770513609
    0x130302030613020f0f010507031b0f030f120e07091505040f0b15070f060c0e090c042c07032a090e0a02070c0b0903150a1a0907050702130204 62
    0x904a882d141100103046100b20004a02816070000d003070f907441ca440c00c001c583c1d400381039681900f00603942d10202c0e035140c081901c50b00002c61308031016000c9500d54440500117402a1510140212a010000c080c08240956402d000b0300c3d0200e5882c0c1550081003003400c40380b10039404140c0e04182c6002411019969105a41c454a0311080e101200e0050f0070031405c4c84411102907200d2044406404550310500500a00030307840032910000040407680409036019040c038040c4108010034001c5080384005403600c0103c090042030400c5103000649100d4400f03c886501000c0c00000381313244030400b1034050007d200740360b1074059952042940040e0b00100c0b018000d40300300d90b4017643c030020700b07107182a004000150f43c000000808412440c000c48244603400f80301c074000d05280400c01c40e0075800c20725080340c0c0360144104000e034142c0d021106074000c0e2903a500001d41c026116822540f01048a0f01e0180140c01400403c6141038002081d1407100750141c540d10007811070300d03403d40c0003845560802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 770516097 1250 770514847 770514853
    0x7050922060c0f050a14031902030411040c0c050303040b07271e0503060402040c0e0a0906080609010e0303010909020103060306140a0e0303060a050607050705120f010507031103010b13030203 84
    0xe420700c01c0907045421001040d0f01d81d070142c510048011100e80c03155083c0710000c10780c404104085a02454000c40c0e01658004a00c1c8449607590075410aa91064809a4400344400b003d8403c42c60944566500d103042070416428441060341c401e03840f40030080000d0244a443d0700001d00d1280070307030038068003e4440c40904814008025660340c032140203010300c5420100c101d000000f50b4459102c01e00688100500602d102c3c1d0b250307420803020300081d1300c10030100242c00d01034040c01d0301c1d03d104010103061800c0011410509200c0390350700e0900020203180b0560b0600c820240340110220499065072400040490289040d00068001d451203500c0100650315090340c240d2009400c2102c14042d114504c014408203461001c526920301042e1142a8480c1401c60100042d1909030003d1000d07500ca00d05031803103d039031035000803017003090101058510380094020124101080c03050340c0d03212a8504040000086d24580e40c40280014001c034005e80341d00080020b100d07100c041201009660080031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 770517347 1250 770516097 770516161
    0x702100342080304090c0206060a05130609020309010f0e15040221070f140f06030a0f06030f05010207170a080c2a2401080303041b0b0a0216080609070509 68
    0x2d0076565481889600040d03460104000f05180c40171620a0182070018443c1c0710080c00c0c0000c100c0507040b40030b1580c03c0c41d80e441e1800074009840f400a50b101d2001c0c4400015114000034031502a52a000c013000502c0d004030f410214502c1c40c6282a0760040d40644d011000380c3c1101091505200703803500880300501caa5880003441c2558070b00180151084042c0520200d40f010082c00000040445944d40c009010300005480c0741c429031000344542c0d6441c0002c900303c1d559403144099918004020380e1b0b1a50001090014011740d106100c6004014911803840c0546c0c2800040c5040c0024041b40100580003d0034844d250040412002c400441943c52600503030700d0300c20a43d200703504002141a0308100010110034110f45034000e040700c1c0313280d000e146182d4556603680520302c804c412000d800c0c7c0100c040800c0c03904140018100f41c03d2590010508007020108810400c240c07644480070740c0d0310803c01c00c4a540f501003406400c903502902c5a012544541410342e5510304c1d4281508050174588003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 770518597 1250 770517347 770517359
    0xb0d060b011b230c03100506060412050706080705180d0f0203100605130603030203091002120a020c0901170d11280b09060112030c0203070f06050702100342 69
    0xb03000361420080c3d0200b11000c011041c1ca03070b46030401c2148895054020b803070041d01460241c0c0000d54803440050440d4905a02c034008007498007541101a00c641e4004001480b010340c02003905c941041c00c1d41085420460110001e00500b1031401104d070094614600340400c01121510744403100b640103080d1740305000c0600a5000424003481031911034410a0000043c1140904c5a541a41d8159001d1850030711441e041c0b01d030040305001c00e24214814030084555000404014002c4015250301401d24580d80004003e0250810780000e141c2c221015036001051600040da4038a02000307003440e8040d85d4981000b241030140c54107d020340000c0c81d106000c10b000c1034015003204141f040c0d00e00c50558030b07011005942d0302d50902a00c034101e05640300c00c4000c0380c09801d210075844c0c4014200c0e00f4061320703500c0c0c4e0755441989502c620003081010920b10b04500d0004048000780c0030300d240400151041102c0ba1812000710003048402500e2030f0b48420340c8070754400c000e092a007903e40200c016541e80720 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 770519847 1250 770518597 770518613
    0x1b120b070f1b06090804030204060810110406051611060a0903060e010506150717040909060c14251a070207060c0203030a140c12091002010b0d060b011b 67
    0x85420001804201071075400c40d018a4400030601400901c44002e81d03100d50b0761000602513164281c507903403800e100000042e6102d003e07004c080c0c58124081c200c04644100024283c0780483c00c2c5000300082031000748403150340401a100c07900759841d001020925035041c020340021141c10851340010b00013994490454000c42807004030307031040c4820001d5812055a680c22510251006130740300300c3d000c0034002c1458618018000d01402001c0c134201d4104180c4c2c0c4254076a0142d03004c0044a07844080c280c041c410703036100701c02900e0024181500100454900d940f0309100307d54513010442c0c400c04600040030044003604182981c0880c844031803024681d207145511500721031100051080c0080414a00c5c41440303d041d901c1d501800075824110321050030b41d000d1120954001d40d429003807118801c050350410242c405070a080800030390b03170083c45003400b5003c0c0850840e00305580c108110388400c0e460320946018010341201c40007843d28030399001250103007560082040002000040d81c82442030304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 770521097 1250 770519847 770519851
    0x3030e2512122d080912030405070302060304031206060305070f181703090a0306150f0e340c0b100e0c090d1208090114070c12021905030301090c020313031b120b 71
    0x1c01704a4205541c528003a0800f448115001440307030300703c0001007006080170700c05103401c01e01c00d040c1002880411400b00045599980c080700000b6165014041a40c1e00240040c10180c0d0600d071900040344042203250343c18500d480741d640001c2d1480650206440c050040e1142144000c003e00c0001d030380c2c2e0402800cc0d000351200c64802c42c014200c005010303090140540211a0b0f107131038505042c0d48444402c40c0650500380c0c8800d020710380408141c61000c043e4203c0f4003648407900d0b000842c803080d090150110b0320013040c054035103000303c00034402c00208814080d403080c0329a1600f540e910201000c20544071003010024400394009811011181d00900d60600c200c208a0082014400001c40c0c41001d07041680e030103000c2a00b10350344001142110300781d03c00c0340c4041d00464450440c5003141041000e00000180c41c550000f100600c00070485024211405074288015401d051007040701c81080030701da2200030b001c80b08210360f04101040c1300346071900420b0001c5080d40c0780580d6051446400c401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 770522347 1250 770521097 770521111
    0x1d091b0c2409070e01090b040908042c1b030a02220305210a050d060b0a05090103050627101e050f0a1a0703030e2512122d08 55
    0x780d40c0010065040003c030f80c02124a013088529050b460080201d004140c025801c50b00151550000004140210000e06c000d00750801c682c01c018000802e03024102c803001064400025950050040420748003805005130141c6510302960b0340c0f01d2404890091045070f5445103507003520b03881e40d10301e100400c4004007182e000d4820b603005503030701c05011403005034218081ea0712890184400300301e19118401402959140f03c0c2d000030780380d0312070107030100d203812074501040020000a4040380c60359040c00f5180d0456019903981c1d0061a01103081c03100510440207003c00e030807800740010424040d04d4000b00003800c80442d03909070b1168201745820030301514014980515010384440e10142000b040440c00c480300d02146020f1004151480c004541c0305850590406485403015503241c8000e00464079800c0b81070056a0700008071041c44a003031207981d40b140c0c3d803891f65402541b012a10740380e001d100001052510200f1322002d850031406d10030301c42080f0003a00c81c44902c82e14500307400000d0a03000f121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 770523597 1250 770522347 770522413
    0xc0c0901030c0e0928030314010305010218191208070b15040c0216091a03120304021903050d181206050a0f02070c05060d1d010c1d091b0c 61
    0x16504d60055a20a03151100b001c1c84550866100f0280c0c1420b20403208a500c00c1c078022901300d00805403891442c0b401c0e001a075981c0d60000705250035140c0040c6080340c030001030b240310303401110203070340e007903140c21030344280c1d12101c004031418400c0103a040102e607a680e40c01840e0344005d003440340c000100c8440c0c3c41225801149010020350480303000085055050300c3c14442c210719642011040b2020b071400c03940c44000c80040c1420038000b582c003840001201860441c0c002e0320307458a401042140d444c144940c103003215101200b4000708501050300c0481d0382407400c3c0401010700e525400c0c1c030800455132100c10401650081242040421740106002d01c200d40c000384115804421270701d0403446030030401050b011007050104098203242000d820702090f03403400010340410036074101440400e441c0d4800d41903552440c0e00034060307811003403c030b5006050100036030380c0301e8030680422a10070300600308d0340300c5410f008184100e510003101168146010401500c8400d2092207922a844c5034044100c5002c83c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 770524847 1250 770523597 770523601
    0x307080f0103020d0201230d0203090727020c0a0605180114070507060509070e1e0703150e2a040501350705040515030121170c0c0901030c0e 62
    0x4809802524182c81c0c004100305010b60040c0c0c015101ca00d00817100380c070050103c0c040c0b180d902c40b030072001c1e0419400805025a0340d103032801d0040c0c200340007a0490314041046406000620808001c1c505408050b10001692070040e000b0030b0789000080b0320010030003400c210402c5200c0c400a00c5910b0903081c450001c3c0500c0c0074a600b8101103c4045603000700103071b400e100d0b020102d0303240d0300540d410640060a8900c2e0540314109003504000480707460310184a07640180030380e80d0314004160b5104a951608224030b0549901c030900b051036500c15441c24041c0034020510b1901c200070102c0e800f4011b10481460131841c00c800b030b0b140f50068400c1c14045000b00e0784030302d400e070008044280b047d85010f890700d049405440c09440000005004c0008010080c400450345403201c211207040130301602c480b540c4941c5401d1003220201c801000c00300301c2042c00c510316000902c02101840320120164491a01e6000b0702000da40341c25056940d00380d00c521001d000105003c1c00740220ba09440c04881e000742c40d6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 770526097 1250 770524847 770524861
    0x1060512090d210207050d08040c1a070201050c0c0301050106120e01050c072a09051005120c130b060f0706060501140a0e060408030315010e0328020105070b0103030203030708 77
    0x2c0d181c104a420003164056480a8400c9120701d40305002c4580550010b00f0f003662078403440e107000c04058020300401c50507402d10040c01241c05001c401000d814503170328419910041019881d0017006002418080080742903d80008240070ba21145400540200003075a0349400080c0780d0a4001c0c07010030104d18248000b0714502c0c0600906203c0d85035298209d1820b0710503568005207418004650204021440020445068174007424000f011040000701d11410320741c1072081400d509500580c41141d4100d0b88038901003000c6400c0c1c4c14a10300711254400080048880000350003008180c640c401c100003500f003006445100506041400344004100c050349403c015070f029020b211103000321500a00c48103042a2040c000d28440d00300180c041d50038030780d032400418a180c10580d9000b4080070f90900c07603901c0f541c3c0521501e80320720044004055141d13602e07401c8038546081e020700c1c1da00b600001a8000a690141c001c6461003580465240d983d90307075a05000f912504181e548200040d4588041240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 770527347 1250 770526097 770526103
    0xd022a030a08030c070b150a090608060610030609021c0c030b180601031b0e01170709090e0304080d090f050103060e06010818030c1e0303010e0129030106051209 71
    0x85194040e0040c090120291a00d14031074000821340300001008000d5503000810500b8500c2c0241e440d004440245004881040449402a000888081e28004040000601c00100640c1120055a600842c19101881180500741ca50401660705000040c007070a041c00707140e0301490030090200100101005814124180c0d8400140181d00c40e480305502c81c0b40d4a0241c072099004181410001460301a0203010701c0000088120f8402260795101400300035600311514000d40001c1c04036aa2803441d1150020b0090141c501841d0001a82d5610140d100801003046130090075034641160000c045402d001048541140100307544c80c2c000d03400010703c0d54080d02500c000d9130124051844c0a56515004440002c0004c0940301496400900100104000d0004066109181c0c010b069006840d48003600f138180c2c500e01c0c10b0240ea204200412100ba010320010341034a0800d0f010500030703041100620000da2100742d0070040c08100100000b00c02c0e4000005048503000c65580c2c01282d91800c4965407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 770528597 1250 770527347 770527423
    0xe010b091e031e0109020306040b060315061e1504030b010611030708070b070e040e072303060403031e11030106030605060909010e070c0807050106061106070c0206090109080d02 78
    0x14040e809a0f81c00820352212000c007104846400000140c0f11039250002031414000303880c01d854041e2801c05000c5c080c10140544c1340f40c3c490280e02400306061040c00301c0c0340e00c03401d00340800050300303000102122980c03002040320321000040c1c1056150350700e0b414403e0100300e080c400d074808075030748100b01c1001c1d503400b0080d1680180c01102171410500c40e5203400071141e42c0200484200400c0340a00200d136900e81c46a170004c44062401800340c030342007207260440c0e040c180d00f160714441040000c600b0300b640c0005500d54800d50500d008a091403040001c150219100e1040003040d44c1422500e4400701503810185040b152079a0303090241300e0380c51041c0030141c41045200c0c3d40003c2c103078005001c8240724524858005c01103182484101c0c0c2c058130b40c407035103400480e070840b00d0781d44030785c020058150312840f0100401c0034100640883d00706950017520543e05060000d004a5000c80c04040503030045c0c40450042c6003040c180d5210284e4004000d49030160a0f40d4904019a07410348240c9045400c00c0b070403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 770529847 1250 770528597 770528599
    0xf060307031203091a0a060f0501030902060313260702011403160e0102031c0b03010f0506101202071a07080c0a1715040c051b030304021f090e010b091e 67
    0xa0084010803c0340548054142074410045e401d08242e205d501040510303110b41004000090b01d40d0420031040c414907034980c4558105410440c1c01e902507500c03401181e4000c405000303111200c5029181c031b42032601035140b03848011048410318030300c42102c070700007008075070700c01d80c1e84241580400354540c1003804159040345407020160381105140d0f000746d0a10003142d00500403241403400300c040c00e4a40d07074102c00144000380d1b290348202e007240c00c00b4055450301410498050015140c903201044030826044101d0040040881d88140c0f02182a41103646003130700058103070b1031b58444001a03050300030192000e9000440d03c00026114150000035102c4942c2150b49510046050030000e00c1c1604000d885107500d22100d1341131850a81d114895240342c19440d0701c070a074403003447c2030010420618000290b4413139002002084016982c0d980c00e40144060b0f04146107039000006000c55204d0301ca604551540034041c2d0020400e1030a14002d0410100708941c565243d24410880845411b252001c503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 770531097 1250 770529847 770529863
    0xb0301170709092001020703080d200c030f0a1809050727050f03100c020d020d030605151812031b030702030c091305011503022707080a02040305150f06030703 70
    0x2894508020503400301c4c84c07500501c1200d4102c3c1d120386484940344d11100d41030740d41d5562585880080d90130400c0d040b86110005003198200700f440350500e0744034402c004400c1030700c40002859618060240000c031629850902285030b20340e8503440a513008003000d0359002c01007840d04401c03100140009a0001e1030703a403554510b00380c4a1410060050701035041403410380c035004280b100020b0048503c51218a0724059004202d40b440c4420040d040110741a900c1080500f08402030000e601c818186403400d079a60400d007a5140f11000ca2000852040584c540d84113001080b03200507000c000001d0f01c0c40310f61a040715403510308800c842a680380302e442e100941503044085580c025103002c01c40d1542c41070050003a000307525890754425003110b058050300152180c4c42c110900650034440c800300300d692034901501010065411440c603848900030000400c020300c10002502d41a0b035601958019035010007101c580300b6884003c111550000ca488041826076540055004e1400081c100c0840c0d80003020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 770532347 1250 770531097 770531123
    0xe0405130f060203060a0b0c03130512060103120c02040c080105010e04090b130512071b06050301081e2104050f090c03040303020d021920030915090a0b030117070909 73
    0xb0000650001045141c1c0480f11180010341d1441c0c25005010181c441c03c0035603070310a4075241c848110041758000c10700504080070110001c91000500505503170300101c000401407102c2e401101c412240c0c4030000c8d0003e040010413000d2540268555045e9402600d5130b00c440000c2e8803d1004450500301d01078813004007034001c190040c030440c0002c1903c5000c4e0003074442818020455240e541c2c4807036421240d4032900c0c41180301d0403110510340d00142002d0715100b8170310b524204503980d90b0390450840300c8030b4040c40f50a592078183c041180d84e80492403201940310324a00340c82001c076a038001d845041e0007001e00c8000c003a40b6262480f603c0d48500310071140c02e801e60b03d994400301c2c000c4d0001c1c0003c4e0521036003041018102e1080b03880324002100c503a0303513101c07124941c40902444103100180e47d001c5503106204142e40b40c2c1d180c1c1c0340390305a001428100b40e200d041000009942c811942d020060101c8000001f04407581d4001c01f03440020340700c2c4202c1b030303030641c0c1d903212071040b640001000340104452101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 770533597 1250 770532347 770532353
    0x20d030203060a1a0304060c080f041202070e011815060f0810081005010503010c02062401020307060e030712080115030f090c06020607030e1f020a090e04030e0405130f 74
    0x30140d90403100142c92603500036211641c10034000000e4140110400d400710401007040524010b0080742c541d03034075108025050010482c0752100c40540010014601c006200e64007920800442004201080481600c2e50303489003060f902402407210902c120f41001d8105105440d50004074080300c040b560303509050904040115101c56020b130001d1720100410800081c074203010440c0e40c1c0c1101001c400050a545010109800c540350b070741c01c0c0020754100d50100010515803020162007443c2800c0720424400c240350041b030941c1309584000b4183c81c5000389030a81c080c40000a85042403044041040318110742405850041307091040707080c0860084966402d680c030a030000350226941134008601c200060707aa0641d058a10b41018006074800c104010045505014084814041c07202520304010310b56110303a16045440d0802282135000030308034443c1407041e00c108000b0030f40140070b80d00e07e0816103002042c0c0d034009000141b14038201004070300840500c040e803140f02640240c40302115141a5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 770534847 1250 770533597 770533601
    0x3030a0506030f0106060503070e1c02040c03090c080c190b0301180605040f140a0b180601020a02091905010b0a1e140708070c12080a0302031f0e04050d0f020d03 71
    0x101015014041d072141d00040540134003c020150030140c89640d100d00d0000c2c0012b00c0c0003400c1912a11a02c00c000380066446120300c8102c03603084c1c0544000c00c0410259006034040d110740b036401058a0f813004000a80100d0109100d4060724040301c0443c000c080c00c0c40000000d405500400200110030001081101c8c0c2c10044030b042c0f2100e82d4004621345545200103800c03a48540200715486445036910043c5904d0b480e101d030b900c40b41800080081c0b20002c004106c20003a1200c92960450800c004101c1c540c1c020040c1002555008015003124680340c0d41816402c910250401140c0d403d000c004940044000140d5a040c4040c3c0c0d00ca1001c650098042a01032494041140a0000400c0c07415010408403004000050042941c29a80c03001454018404041b982c0710340c18031031004a08100140c168021601e4011482c0703009a101d856104a2061a0103031840c03804d20074011200014040d9009184c40748100d000300c081e20340014000740d050b55400b0f260400b10005800503501045424040d07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 770536097 1250 770534847 770534851
    0xf08010905041e120809010c022a0604060903050610060f050702130507030e10110702060c0106090c030e01140702070b0f0912030405130213090902030a0209100603110c03030a05 78
    0x44143d03401d03d02a600d22840c0030b081c0c486090f0391404080e2949180071740c1004686810111240c002c01080c0c240c01c0d0001d445c0c540c0110346d41c005c0c0120b9400c0c51400000483c2102c034508004015039a43e90790380802511020207480101d84500907180080d025200c0f0f143c02808031007007502d4009900d0b4188400300c900f68003480003240d10a00d801c2003031542224902c12076206191503100001c2c0800b080404914140740c001f82241d5246c00c001203006110484401d4803107080d41074680030345a044c11041d046c050062a00702e000681d20f807180c0ca1490b0390303160b0013000c542da440c10f00821150605c90000c015000c0308582c60710150344001c50411445409078000d00907604107192980c14aa00c04002420071303140b5199131844e81c0c1c00400e050100d0b190910f84540810070040003140360802c520103003284081da501c507140b2490740d00c11074403055440c10b0010410b425070090000f07100b0b141c007100705460765100d401100300203840c2c0140b190082400b0001c440a41302d400e001541981d45054a0101030140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 770537347 1250 770536097 770536103
    0x1505040c03090510091a0a1418070807030809041d030705070e150306060f01050d1e0606050a091203031107030309050c010e0306060d170d06060f2606030102040b0403140d0f0801090504 81
    0x14030901208c107800c0700200319016070f041074003010043c81b9414001e0b03d4264950400c030b0740c940103110200002000c9500715880d10310140c0b00481c5442d1401442c6441d009800c07081c40850000144030001c104020520100f80ea0001c4036810190b210301200d207010000385000079070141e10100228001d880c058030708006020051410b5071030508400c0c222001c0c2c841c412001d401c0e0a00b4905220300241d410700038003014115920340719041c0030404000a0000800d4400c4ca01201c5800348241d0516203c2e4021084c4407494241a03a40c9a4035850001d00800c0045410707200740c001d00c0c2e45035030598440e01d0000c21103070000b4010455a110001006200e81d9101c90888215007480b512103500e42c10703000039002800030a00000b070710501c0c10b0700190000d980c80e42680f040010100c2c01441001001d0740048041c13080417a003158989c2d03403501103802449140c128104404011400004000e6001d8900c1a0341c07032840c4c147c616104541400b41c49420318004480c1c04503205a0041c85004820340c041a80540 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 770538597 1250 770537347 770537351
    0x6120a020d06170f0309010c03050903070e01060e03100e0a031431090b0105070609060b061911060408030f07030f020a05030a05060d05060a1505040c03090510091a0a 73
    0x118280d8040101c405550000703541c4045850070743c0c0c61031010f015030351024482c9409185030540100000b03000d0054500d0040502002141e08c02c0c242d00e00f00a1840500126010140b055841c0e02c000fa042c2c240440010784684078402502041c1c1078540904459040403c004149030310150740c0c140c904006900210200c5071050100350301440703400d10300401a800c4c0c1842041c0340907441c5075010b41444181c10141185041031100110382c0d90040c04c0710303810b60308201c0c0019005034038946034015043c0d40250311b900850100d010304a002ca070304070040c0031070a29102c19400e060980034841d1542001c84020381184001c4c00040d001400c07064940f5070060b0146000594420030303c07504002c0703070440031541c40050b002108110071003440748903c5400c1081158411b52180040e602c01390740e000000c0c040e071042e507102e222040100f07945004690103400000c0092048102000004005010801c0151424842c2020040c60458180305d0f4184172904035031951585829089101030090001d4603c0a9240e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770539847 1250 770538597 770538607
    0x4141603020712090608090a030804030503090f07030c09061403100b0a08101b05071101031d1f140c0a0f050d1508010605011805150405150901080a090206120a02 71
    0xc3c803400c80f0100300d40707040e8558104180c10030303800812009008024802c07580c414001180400d070003080d8150302c40d0741407800d1541c0b595000b00560500c0c03407000049042d445400808020417582003a94019184100e0f020820290340e2510f520404003041482900754001040044200f90550000c8481e014080d2074072030100e5480b05032510348001d449604a50a0703a0314480c000383e0306466012200c1c00fa82d8070f80340c0e04000f501c1e20f50392a03001110071818145035a40e0f0024010360034040f07060728514110700c29905207040c1520450030001c0742840b036181c10b80ca0042c0d000b0003004503401d014001c04406901d5400e201003510160355203c1c0f0201c00c0302c1844000d008440303403191940596908030704903145482c400707071400110509680050308224144941c45c0000300720903020907032040c200c40040f1b5414101d001d0030205071041e440ba03038001540102483e0ba82c14100300c2120020540d05100780d0b141c0443c3d5440c601d000040354480074000754050010440d83e0040c00000c4450b40c0c10805200d4010b00d08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770541097 1250 770539847 770539853
    0x1b06130e07090803032e06081f05040e0303090c01080f07050c07050d080901120c210e06160e0f0a140a09020c0a060501120221100c110606041416030207 67
    0x107410032141b50a00002400340c07066010030302c0c0501c0b0f1803500f60505e03c0e02c11340d0030044007611444004000c680e078905107004051101031002c40c010f0080c50050400c02c03400d081c066040351260300841c4c10300480d1092090140b4903500c1200418440c0200c80c204008980f10518100c130342c0da100810210b41c0c0d128200300403e4a80c4c0b04910414014882d0915507a100c5100001411940d0201d0f0006606840c06039039040301c0f07420400340e5a21170703003111840d180ba5084158000041005101c0300010b031103008200322078410a1803034900000d10307507150058a01e4540303082000102c00542d071700c0c0e0895410b401c02c2250600041341407501c005e004080b082119107032500359080341c01295507115940d0080e003250b42445060702c9480c0c00340c913a00400c4100070031a81c0114406440f10328441c0403070341a1094620150304c080c401522401c18244c1e0503c000c03102c0c0d800007010310702d8100c1410800e000d4140414040d18040c42030b480070001045651500d0740d1070071289048404807040c43c100307142e002c00100d400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770542347 1250 770541097 770541103
    0x706110604112106011202090f01080d1218030302090a0f030203100f1e0c110a080909100e15040b09250c0c0305011b02030c0718090203030c1b06130e070908 69
    0x1805484407412003406d02401040400b0340060b20416803501d210740103010031540403074407180b08601da00301510400440e50000c001410240c051405020020310020300301581600140400c1c5021503480301307015140c02c1201c174036a0355407000951581c041c41c0742002c0303404a608a00102c0c0e1018000107002201f45850400f2440184608204107599201c181c41d5160894001c40320104944c000309003200c000c0d980d03039050b8402d4402444c480c1d806c00707000551a0b4140d080e0680070b4621031748104600d081c5400d2140702c0d4042c010200e8031881c10a903444a00f420409550b0b84191000d1880d40c0d07080b00620308106c805a4084610800c0149055109001c00d604400e0000214420800048d404445480308101e01e43d00d441600c0445d0020483c031f030300003007000032039006403514000c0404410f058003603200010103070f850001f5050700001c01c04544614010031000c401140340200c1000d01c07881d8070208680e500c503405118600107180402449100c420407109075100c0c22900b0702d0000e41e6102c00f200c9207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770543597 1250 770542347 770542349
    0x9080c010e010b01031506022109061b060115050d1a06070c05040c0203090a170316110307140a090518011418060f070507030e1002070611060411210601 67
    0x2515a443d807103410000d5074140304610b5160700c411101c50125042840081d12610002003000300c0f03151910b0400e051103110421210f81400041c00a9030741d012000c3c0d40d03812601c6083c100e00b84c03401081c00001d00c1269440300810449020b40c0d03520302d41962040b40800822180d001035880c900701d000d4203c40e44e00e0320001010540e0050002c404483d01d048204810703101560f1008046400500203e607054480201c440c05540341d1602d1101d005810780162881d600840210036502011000c506d028001340342040140c04105906a50030f540d11610072120002075011016040301601c902002145440e07400240c10040010741881103480c4050200c0c290f6400543e029030040328030007444101c410310408241111250070142c090340c6408065025042c60041c100414081c0000301601014490040b4010b0317648010300d00d04480d070311918000d541c0c020b06c0c042c040100b84102111151a01c0002d64180703d19030119080d00340341e0175401403104090340c0c0c034003942203054141440b20313040106000c2c040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770544847 1250 770543597 770543621
    0x402060c0a0204180b0105120309100e03030f04080c030c1c0501060b030c0a020d0309020f0405041a0f0114040911040903050415021c180e0c040b0f0901030e0303010b0d09080c01 78
    0x60304d002c3c24a90781014069204521a0351100701e40c1d460600084181c881040c030440b100048001541400c0e103060200d00c000300d90501000521a104600b03c40c040d0050314192070407209400e20100c1415580e540c6111b55560040002403c90304403240301d0401c007012440340c00081000340d81da81d1252916003050324a040308100c00b14400c83c1c0f09604100000c192620781c541480150b0081d00424107110203101c1e078501480e207401c001070900c4680303030321441d4100b20361100aa1a1030420412519907200f030041404012615800a100d40303003e0140c00c022540200c2c80b60061400360041000401ca41c081c1241408800c0c040040c840f6800400710922500e942c0244c503d0194151084580b604681040000d2003004040c007903810802800c100c0548640001c0600941c40e0154091518011948070005901c0c0010303c0701c15402000e00501801c1c1001c3e20240710b2580c0b042d1b030a9440380024010684140000c0c400c5003c03c030b51507041101114000c100c3c09103000441500c03542561a0700000d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770546097 1250 770544847 770544881
    0x30903120e1504030204050f010308090d030c29090c0919060f090902030106050a03150506150c0f070609210c050406091406040c020d050f12040507081b01080402060c0a0204 76
    0x13001582030a000c0c0d56404094418014425030455540031003a010b034103500c0703020394a04c56001040500540707020300340b0794028466010310304400608031002d800c0c1111814506ca03481c0b0124111a00002c0c041002c0c450041c10131040f5618150400880b4107400c400000442d05d4200004d10030700400c010340090000e424000c1501d01c4c49005040c02d440316540814020b100845d400c10114142482c0c10895030140c0c00c0104198580c20001610004045040035441c0d40000d0841141940094610010043c6205803202142e542009070740f03d480c030344190041500051005543c0200035070300024641c0c41501d94004d416104d50104007150001d800501c0000e503500703240d107814000b24a01c07a074080c400301c3d0180b11b07040007400001d40326621352091006103d00480c50940c4a00741109841c5885680320806d550b1b49094140030b030b964160362041c10194021006c6140074410f1000d1110f48000301a100ca09641c0c4031075080c404994041c501086550003003442070070040e5038034060084001041000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770547347 1250 770546097 770546099
    0x60403020105012304020d09150e060c03091509030c030403141911060f0405040c1e05091f050d0c0201020315060717070222090618030903120e1504 65
    0x202030300715101a00b200b07003150380c0f48680c0248400119100300c84c0090940d00582c0312032110802901074510007900806001000c2c0d0000c5160b0910751040400443d6102112440d4590038010126403005482001994025040940c1280041581541c22540b06011207280002401c415810340d0455002161a0382c200880400120002c10480c05050445644421040a1544c0321030b200501b40030f030035029000120710006502d5120058500a22000c0d000384649519510020000d2240050f441c829000c0010310711012031040701551030300003010300002a56001b41c0c1e18004000044c14070003040140411110404800a01503200314488680000d40c403802c000c42c0d841c17041100c0a42450081a05012002c04240369070000e455110b03181450340c0c3e54005900200d0001c0085010702d100040c402d180000d40018103a000c0c010241c01070390204420840220340d052442100200600003540014003800415407540d8000800034160030460000b8030b0010118411800e410310021195002040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770548597 1250 770547347 770547353
    0xc01020d0e030c07060f020a050f1005010f0305062a072006070803010b070524060406051e040507090801110702240f0901090e010b0315030303062206170604 69
    0x1c507101c04030001c01031410301e1044400d07650380b000e482c8a4107040102041c0c0b61200075001740096400150048242d403018015081f0243e961503200e01c0e03420781c0500e000c00018409540f410701900380c0c0c0c0d010b00035240e180c449500b0611400d99070418a04880c164140651800108100500c48288143d5803031800c9040c00900604107441c1c581034501814040184c040010100001c690540345d800c03c2e0151111120704047e031401d009510002c51050440800003a1451080b04072442503000715002e1054a403658140426150b04007145411443d0009c050309139486c1c1900010741c00451450503070002d9039030b0302d5220300b540c10313902d0480100070340060f005041d410000124055a07142d18840c4424a001c007003004042d120382080541d16038000f24141c1030b568030401161000303111080c180050f13541c4904003c1c4d41c540c01a60042464022a00008018100481500e104181c0200788416242c4501786111141c030141407040c2c200d40c4e40d0880468208032089400b00303003900e1840107001781d1800746 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770549847 1250 770548597 770548601
    0x50c0a0918021e04020c030c0106060c08070201031a0405130326040f0609060f0228090b0906390609100c020114010315270f0510020c01020d 62
    0x140000c04960709100206100412040189403615810b41d2040040000242081c05220f03031650150b41c014000681403c900300d001002d007207004c40107002000011b640e00790981c1d00d0703030003e00010182d110034490040035600a0384491030100e40c4c40b00100c0c5011205c0001400c072041242c6049501d800080030300181640000701128000004504d0000e084011100c040d8080c0d0041004040d000d030441d01c5070800c052a0042c049499000006011000c00241194003941105288030f0312500d45444280c40b00c400701d081c900103400c45440320318908d030800005619540c02090380c9900b01504012150700100349141016020002008500040844407000c007000049005a00c1183d40070303600b400054070340410b1020780400c3e0a000014412010541a40503000c0310781c44040280041c8000424040700f040c1d030050b0400c000b001081501c0e441044610b280428114400c0c101c407500c521040001c0c1e200e01c41d144010b00603c03ca0b0301306006082c0d084241c1e4072243c16620036940108942c05680418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770551097 1250 770549847 770549849
    0x3190f27060215010e0417070b04050703020f06130506031f0306090201080c0a1407020409020306040506061201200c0f0a08040801180503180f0a24050301051f02010b060403050c0a 79
    0x104071449280d45002003829245c10060805071040c4103014104002a9002c0300b12044141e00c1190504149000e003002078941126100030b82c0681081041c5a409107810070071103070700c8680d20341d000100c0c904003004d20000d03420041515480074280c1d04032001c50072192114800440c450340740414158014800104106409002101c451200340220000c0a8110728004800c54101e466181c40d0340c15030000078090002c81002039010702a41c010b0005010001c19064458842981c00c2d0521144004415080b101c566580010240001e801e03030740290316180042c81085040700440d070402d0b45030202c07581403060f454000c580d129000202000264828010301c0c40d004c0c0c4008101010310016114142c985c8141345088030b101d0800e90420301c07190381c0d988003039445490141c40740d80181c0c0c60384450b146051603190036990040806000c80340700da1096003100d0680c1c00150010030f95402e00075101c4600b0118a040800390354a81d81640515110340c809480218000d1000780216035900041c003d002c006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770552347 1250 770551097 770551123
    0x15060902040f060807090e0c0307030e2103100906080d020d17010b1c02180307050d03050a08071209080403061b0e0d050c120105010f0803190f270602 66
    0x50100b00500c19004401d4002ca600e5810300e612280e80d0010704903060480c035013144003203201001c00d1082c004e100c3c0c0040d500c14503181d1020011490403042850750f940e41c903100c286856048030623408402d1100c60207150010380c2015104242902c1c0ca00c1c49003914000d81107500e00e5030058854032090707a41040710141d6400d060900040d0128142449401c0341e40c140281d01c240d6100003aa042850340d504038480002103501d104640740c865400e10034405040b020f602032f1180c85140750115591074024101c0340b03c5685502c44a01e00b41c10305000b6250500700130566400d012504150355130b144550302902c0304940c8500e01e910741d140d0441c5446c0c4200c070f480302c2c02c243d401d503199904800040c1d0414010000000b08507a0b120302002507140c028030b40001d902030b540d0428210141c900044405420481c142c502c18008006881e48440f00f85980e030007184501c16444030030101c049003c9005000c0d403484481070303280c901501d00300d04416044030306805212070003060305460704001107039061260b8040b580b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770553597 1250 770552347 770552351
    0x10e06013302100b06070b0c030109060f0e070e03030c0a0305130b032a0c150103120c0b0601120b18040b0903090105070b0c070b090304031a060904030e03100207150609 74
    0x78080002581c601e1101c94002c01a60b0350200714295944070401e4550060784001d510250f1300d044004844160030070710500c0025810044003041c120018041e00e0165180044440c45680d140c04d4211604469008002d030140020480090b55400502203001501c0c040d460f01030361100d000700700c840d0000c01640000c1a605c800c4c400c0c482c0d00c4610704054100413030304002d09080d42c130003074100c040b0901c01c02c01c0d04803982c400c080c00d10410f8502100c403c2d04a9015400e500e14110b0003038400d4403600d07504a030041504024000080896000d5080d0b010051a4040005550842d1101040092481c0340004070f4080105c010031042004641030700c0d41c000c40d4a4051401c21450b000068040c0c0104580104803035061000a1340c9942c0740010307140016044003c80c0d0036401c0001c001900d03517000740410b84070141c0e6900100c003003005404447d8050032019025500a54607910704803050320461440d180d1501580402c0104e03030009001400c40700f030050b0307030000c821413804048004580c801c2d8044048a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770554847 1250 770553597 770553689
    0xe1c0b011512141501030f0c021c020715080c0409020c1b150d091b15080a27020312030a14061002120c0a0213050105010e040b0a1403010e0601 63
    0x43d05078140344c01902d1100341003449008040180c000e810062405c2d0010b0340341203966a40e0560000750310b502d14402c84032102e21510304020403a1900c8980c003070a0310823540c0c0240c007001d0354803420308154803d2a824440b810542c54050080903a40025024840ca034050845c0c1202004a000c40039046c075011190b405e0362081001c00b00e0701c4c82c050a12100d4031300b0341d1040214140300c1e25035400300102003000100c1003201d4841c00e00d50207190220102c01c002038100300008001c0303145482079410342c1d603620100c8101038000b0740a020910703040d100101d0b00740c000c100e0400d203460002e40246000302e200b90404981da500c08180d035036445100610142c07181a00d112660441500030400f800c00034901d00ca504d94641c0103140c460b142121a075802034010880920341200341c9507590216068072000d9940300c654900349010801a03640002c0c1e00c83d0301184011003003045094030f4500c1c22031390302d0280001c03400d00021000e480c10030209074000220125001000d000c0014201950901c1403c0590058000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770556097 1250 770554847 770554871
    0x30a17060306063a03020312010e0108060406020c010f050103030e1e3703120e0f031b01031404060204030c051e0108070c06090c081603030e1c0b011512 67
    0x80102d104d40d40a006600a0300410907115200c03e81d00c034101803130700032401100c1d10718000b50f41b83e100d10341a02180145400101c2c03000a00c070b00140c12a0728100082c10a911662104c40082d40072102c65071040d036a465640005030300602985000358000d481d01d50028150b6030500c00c1c0e44844900c0c0060340084036011048540d150143c0c070600341c56200c1d02c80c002080c03010010b00801031405130a004d0100100700002004000c20035410400741c140d844100d804050030a2005083c180384081f58136412038404071000c00200002d03255844c0c014500817070104800001040b080c04151010b9801c1d54000605006214214010000400c020b503806c0f21640346002d042490b140e20580c02504020701d4001280940340b154404260300d81d00b00204200340c0030b07946050401e0300002d11030881940a100c5001c1e1510003545c00107002c4a40540b01e40c1d28950100c0100080f186c2d44c14000e449180d800051000891150202280a0250401c1c0b412000002400190180014414215141c1e050902542003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770557347 1250 770556097 770556109
    0x3060a030b1f080d1b050c0319023d02010b1309021e0a0b0901230a0806031f05060303040911030a24170c060a091404112208030a1706030606 62
    0x1004e026840445c0041045c0381c52400c003401440c6842d850311803088115410502c080d550000c02d8421100210001c0144030282100d500703900308500341c15240c17000c035170a140905080d210b0f07400c840d01c000a40b444c00d000006d0070344510050348880c40da075038039442021820908842d05912511028081004003075500060864119024a0b806400046403e4556902941b01c9a514401c07541075400522015400c0342c581e034009034500700000b40c0000110350281404540c200000b810700f41e5401910190080751809420040d00703054041c80100400241820345115204030500703000006076403030410910b80004d6448100d00004103038020715840f0010810707a02c0890031210101049040b9200e010055410250140c1e00a0342007000012081c0b0919171010206058441c04401c10f20b20740e084a06100803222104078004801d0000c100c200c6202041040c44060060080c3d403690006d40c0ba07216250460304080c0d4043e000c280012180840031401644603a8054416002031241d442c0c503600250b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770558597 1250 770557347 770557367
    0xc050d2417122d0403050105010308120f04080f070c050901090c170606070609081c050106030e030705280f06020406030614090703050c040807081b2403060a030b1f080d 74
    0x1c1c14006400480d903c03a00800942d001181c100c0000c200329a5a800c01c0a0705d9480340c00e001007070700c140340001a5480b12441e02c80380140d80041003103040601c0e01142a00e15804200c096030310300080c0d080042c003581c0e00c81c18903010703240502011a028401c4034000d02801d0496460550f4054805c0c00c10030251124415161103d070094404503142109040c902114498102400d0400d0080700d8580c01000241d08124100c46413035400f00320b6035000e0f03c811512800741d04402000c0e0781100045a02000626038100c102e0340c0b444201803150320041c0d4500713013080211003084440c5500400c003001029003502c1100700900342c0380000b042d4034082000061207020000c1c90107041c0759894010800014101c02a05d01400c000c208031460561541c4103103a8400600448440106980701c045225082640b00d10103500f0940001a80c800003856812034950401481d860300071040c100000003040501d40028051882d4076a10140766458600b40c2641201507000240700d40c0c003504020210b0365020311462 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770559847 1250 770558597 770558647
    0x5060f0c012d0c09090903110706020a0215030408190207080601142103130303030219050c0a0b151807120203011a030a0207020409080a120c050d241712 67
    0x20a1894a0710544148620740c02108017a481e25492404040e0400c2041d40011038132011141607543c0d032030040780e80341c110b09002500196583c808200204001000d140c01c540300f036941c42e09214a81440c000400c140c411480700683c0a41402c000520081c0091405000506031000b0a40380190204803642e003c41024891100600c40702e0a0340340060050795071002890490300301d45c030350328140140a50021354000301420340d069124807910b40154212907500d80f1101c00382880c5080d5890b42d40c4401c500501c002c602d05000e00b05190750b9074600c800d002054210501c507845a050914000340f500681d81c981c44101881003006001c1d480002c81d02c0c17034001c030b19610116030382d40c3c40001da84040e00030300350000e420900f005196000c018003c000b900c04e440081d51040d2424506015100966080c1004035002c90001c00ca881c003503203201c0d0403400c1c54030078607c00c0042c403503c16004d01c0d5141d209a409814244100b0f2000c802a4100f071000c100c030b1442c00c2c49001d0405104848441882150b12954 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770561097 1250 770559847 770559851
    0x5060f120711030a090e0c04080a0b091002072001020d120b030c030f0304081c050702060d2405040f0e070b1b1516020a0506190605060f0c012d 63
    0x100100e1007840802d1805401005881c0c4902c2c903180042c0054015000c3e501048a002000034550074a01d0261400c60745208010401419140c41e40b000c0800c0290101c081e0b4000d01041c216442c07024002889041c0c401c2c0c0400c481811844c4590320600c2c10b6030f4032141150480140002440e0303120151700022513401e000020400b0103040024039240a00c2035441c1c140c01f441c0b031040107404000c0080d02c201c4108400341c403108241440d6250b0158000c80c56038002c07407000e01c10900581400b5002d03108050406000082c000303410401d80070710040803920348510b580408007d01c66824240141903d04641840c00d00214100c0c0344243c1d00c90190740030304101e4590201c0c0000c100100103107200341c500002800d417613031a405482240801c2d80c0c1100d401904020220901c05100c1c80082c041d00c00a070440c1c050300c910340701d03030180d084c0b440701c4641000951a1100804212a901c01000b00311300c442c0c00f031900b5074405041031308900303651903c00d0219160740c1d0301802d003115007080c02441c0d001036581000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770562347 1250 770561097 770561101
    0xc13021b06040c0314030406080712091e02040b04060b041802070206041e1a0a0e0f031902090105120a030810030b0702150108070b2502030a150605060f12 68
    0x50000100451804030149204020500090102c46003001003031340e00401002c0c2402d5600d110041e542d210342d03c0364600207420310000030700c0c40703210b48201d4100c1c19030040042502c124503143c030100701e030400e41c8442c600e40c502851101146001e20980d107403108182c41c140502842e116180700640070314810300d04010043d41c00b0907800c64441d0304840340c45074010880ca850720f4889480031504000342c0700e2600c2015a040c00455145600f0b1004488203100204441c41c0c65031400f0129224039288a0894000624072182d859907581440340c440c0c00d15400d540004c5e1403405004004a0300d2040e8421405031560f2602e01c0800800411484503854050410410f00d485809001d0b401d408264405840c41e114030042c0600a03502180031005034016021100722030362682c01726610350026110311440c00ca41000a08010200004100c2c600801804269910700315030b00803e08205070808210346280a0b095031072038403500f612a020103400d050386c4040c01c082c410700ca0340321148100070a0049034601d03000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770563597 1250 770562347 770562367
    0xd02070c0911180607020a0303031d060a0213090e060f04081204030e0907090f050d060e01020f090a0b0c030322020a090c11060606040306020703050d0c0e120c1302 72
    0x80c01005001120701009910340050050309240c02403d0422011551041d00c3c914500c0c06030b082d12400e07600201909030340351031036400703030003e00b140050034041400609a640c2c40c4035060040c644604500d042c050f030b6030200c1810060f25928650018150b003890415110780005d40001c0d01584001d5010031307403206031541c3c02c10780c016010b58854030601400004c204010182e20840c0000c3e20340040e201e00315581c031030100603203050520f03009a0040f900b80c10001c01091601d10b05200995001e403d00040c2c810050b10a9070a9a124507402d8860403c0051684028206200564010403030402c146062502c2c0e20041601e900c000340c03651502c0504d0096100402c0284070704200140d60040004140750799800404d00038154451040f0301040300c404a88084120200d11144034440007080c0038a8281990341307038402500001030075000c0010610480c4540071441c03140214007070340d1f41c44d150b06582429081000c204200c4141e149a0303003040009100c0d80c3c84032110180c1f500f49502000d40ca81180d51 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770564847 1250 770563597 770563613
    0xd031d090f070e030f0703060c1b02220f050a060305070f1809020f0d0f030e19050913050708100f0b060910140a0e09090303010e070305060d0f080c0c10050d0207 71
    0x2080c1285000b0086d00004022459001980301ca14036240c54956500f08844c4910f80540041c01a401000070360024039450340da254411040ba41c0180c0c0026082c2041c04201c08070781c0201d41200d01247e64001c2402400300c108250b000525036020000862030a0103084a00d003c804c9401207034092b00c0d1b02000d803c650b00d446034400c020300050b28807104101d2509080302900d030f21690a4002c40c9503001d00d0651420310120010340c0c907182c0f4103a81e440034030744000d02c041020010241b414004480ea54070307001510034011003004203002002031a10361559100f060072220500840841507250011680540d1150703c19209124421aa680031502e400c40050319040103800480600c0000040c1400300107070404082c10008400b501c8100e400e55071154459602d10003030050031115a000c10000b22401e00c260072140c3d0003000906a150814620f0b40c45010420003000e00320758165000c82e0380303114400b08010095244004503000c10108101d2070014001d446410082d81a054000442c0c00912401d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770566097 1250 770564847 770564863
    0x7020a090c0516150e120a14040f0f151d0d03110105010f0f12230c10120509121b0f030f09090702010207230a020d031d090f070e03 58
    0xd16200c1040d80501c2c6044071307442d145100c444000310f180840c0001408000501102d085c200b05954a292500722a0241c8680c042c42217005000f4104000118103440f032303401960010701e1194074000c040c5060200803410511040d01c26810000b440b0151124140000b00004014109030303a00b04080c0090b040c2141c04d0700310494200155070030325000184003d000c1008034200c03115000888a5a600d9544031060980501405401400c504e41d41d03031004030f500b98001d440001c1c41c0341180c03080c103d823602140400d04401450f81c04245540c80240c82c0b501c0500231982e01001200c0030b4a13600c06c20400c0700c0c40d41d010350483c06d068005c00480d01240f90704200059941c00a0580840c0d85608000c1c0d04000709030311002c1f145004589050204809500500a44044683c8400707241c114540c00400036019101c594140e40240c0300e060320010240c0c070f5020203003036028042e0b03a400407080b45450b5041c20794400d404c0501d001c0c04400c0308216850a11004158121030b080c0780245d5041940d5000918050a07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770567347 1250 770566097 770566117
    0x10020c0c0f1903110111210306061201030303060e34031512140d0f2a0308090c010903030c0b10080d1e030b21010f06090905060c07020a090c05 63
    0x50840110501841c0c00c004d07400c24209070b8500d07190404140c1c03200d481d1041003418009025668104030150f100d5200610761159010b048682014210a0b0802c0d00d24802e034010742c0408d82ea03020620400f107040c2d8099900240c07182034802256640a84540340c030401d41c0d03101c0c4c4441e1044000d5606280f00380c110f0b40c4410040c1e00300b92210b64075048c04a5010304174990881d419005001c0d412240200451101810007a5403142c030070040034a48142c0e0f040640b919941c21550552405140313200d07080f0b000011070390090b80c0d0062145071031090700341f60240441d0f0140c14029680010400207074031642c044c0c07042c1d510010002680c0c503542c960484440a5400102c9580600307840a01d200e5842100742d07000c040c0c41000c1600d040302c03506040d02102d8014016a81200700400c0c5825000c65a040b407031034000c00c5600004422a4501c050011184960084141c81ea100c040780350030f104007000100e402042d0141902c0c5050040c0d400154007031340074840c0503521a02d680050681c580074000341c41010388 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770568597 1250 770567347 770567389
    0xe040e0d05041805060a0e04031e02010b010f080c0403030e04090b04030f0e0415051002120d02040501080f0121080d090b06011e090918050115060210020c0c0f 70
    0xc85854050440d4100707000c0d410704002032400319902c01034070f40900c1d80580000f6000c540301d90304080b00071850390b800030020340c240b01800e46503100d43e200342007030410607034003e5000045100c503000c001041e40e010036442c007042140b5001440446502c950490f0b045a5250504825401b070f03203000304c1c000c2e0814510103007030030050300204400d140c1c11806050b0a24881d82d604082004ea1303c040200302d0310310011400282c004041c052080f400d0513090191110840c1c0100e4880034200400c407201c40d4040500b0142d21600450100840c3d60007000c010b80181884800d8541581002e18071168010b038031160b901d005100c2040d410500c034500e0120b4100c07003001d00040c006280a4100000034160944500380094000c0c4400c5403100030300780c0f0300f10481d0b02507543ca2003682e00d0014044064400d80c481c581c401a11002e07080b00060091191804101104424003032030380c9003010282c24080f07502080f90900d4010003220449280c00708404141140489826480d203a8120104100483c44070001d5030400d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770569847 1250 770568597 770568613
    0xd120605090114151e18040509030904200901270f052704031d09270a030903021c1406090c04020a02030d05060117040303020301091a030604030e040e 66
    0x1410f81480845043c01902c000020000c41020809a44a803540700c100c219030320740213480100c95290091901da041e4142400005549400140843c1c600340e4a140d21036100081000d42801c10380a4440d000000d030030f00000d0001008424111403007480d00d0300d410821610284901d030310384011040013100d02c2c0350500c40ba441c0c03070b040c0d07803880300c040e500815104500c48290049040000503074088203010341c1c2e03107584c92610b03250f505849042000704149001900c0d042c06a42d90b85072119550b01c17031400b021002c201c282104800310003815000c0350040071500b14407000c01c04250410017520840303906540002101209007a203100d226031441c0c1c02401c101c00380346168192040003a6180c05401c81d0303401da0300210f0400042100300c5c41554203d41c0035030814406440340c0b03940b590180743d2018060400500c800d0f001e00c8040c4072440105e40c00c50102e81e010005200b807050921a0081c208101c141e4071350038442900001343da40300b00800090421a0b140b441122945554001c01c03803c2d031040301103a000e6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770571097 1250 770569847 770569859
    0xa0312080105040f0e1b0a05120319020d080f0a0209090a0902040e16090b03031e0403030207081522020a0807030b1302060a232809080d1206050901 65
    0x305a0038818075100d00e0601d000f640d1034001900c00c404840c1100001840b000c0c1200c55140c601005d00b40001d50720212030b07000020b1a8403502e4441c45c0c6216842d014550315161003a92401114103035a01508541c0102e403050070745034002150a4220b9000c0042d004256600e2034228040d210b0f00c440503402203030400500020038026044019000d00c2100c09200c8e404411850507540c0400d10458058120041c0c2c1c2003110740c041da80003505840001e82641d1a098004900b40c00941035500c440c01c12010003d020414945e041c440d1401418540025080301e040c03400009103a60409044040300e410b00b80150001c60b501d401201c80700503805041c1a200a07074640e031090311108148001d40311554254001540101c41c20440141103900500141c02c0403219a022111488003002c20007a4501c0089140d2040c00580d000c1c01182ca4215040305102c607019243c1c603415544464030070280094458240b100c400c02040d21050b1403020703e030a07140043c9440e4121b01819007544034680100f078860000c900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770572347 1250 770571097 770571107
    0xa030c0f1a09370206071b0503120a0c110d0c0e10060309020d0f0305130f140603101a0405150307110d080406020a0e09070201050a0b1c020f0a0312 65
    0x46040c02d54107443c190080c0b22043c0d0744041485040252826840062001240107800300d05491030001d001c09003000580c0c0d492005178441c102c621014001c01341070422013841d04001392204418402c0701142404000040903017802c048610080001c4076941130b00100307441d5000e4021613140c02c50790402d8507607036410030201400da0a0780c0c00030501003c4100801c4d224041d029070440030b540944110050302040e01c60054885007036400703d0400004108074400d43c000c00f030980020f13100441609840510305445054410205420b0a00610051040183c9251101152800c4030480d9255420b401c000e80b8010400c1d2042e0740005a0004645c22404921301e42c082c0594402d884a0f141c0411a05090105542d10050844094001403c0700009000a16a900500410481801e10b1210b4084003000180444011905138005030b64480800403820954010f00ca6103c1c016500b411400808031103204980b20b160001a014080d100c0084600d40c944940e030a00940d0400c1d0012207540750100000c1c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770573597 1250 770572347 770572351
    0x18022b05071b020d022b14011820150a05030a1a100f03060902040303120f02040b090d17210105030607050313021f0309061a030a030c0f1a 61
    0x2d2800b881051040c1e4160b490760700301507001412000c540301a035003001510321030f060414440549224580d01402c130803440584901d8803c0060401c4400c0c201c01050071140d1243c851501c030800038101e100400d4180c7c5800141c41c01807400c01030404001404549420b0500b074407001003072400116041c0040c2c0c03180155000b00c113403003814001c5111078812045141ca1507011194850050159050f00a000350b4604880d0380752403c011903c15070740e400c1d21040b600164810740108482c00e0303071643c031250248a02070020550300000c50805040ca000715069000b8850118011440c5615501c140311100704101544174045071b409940d4404000d120f2101c18422461010900b40341c40089400c0c500421054401c4e5456a9814211359500407103104409010400f80c0e0418a00c031032403442c0b499010135140342c1c4082500c0200e6089080c2c500041120103508941100300c0555030040116074002c102c00d101c550300b518080308550710f141007a40d85a02d284078000c2552a4048203018105015507000d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770574847 1250 770573597 770573611
    0x2809030309171e0403030f110a02030d0804031707090501050a0c0b09010608100e060f0c07060e5a03070f120309020a03171e07061518022b05 62
    0x3541510911183da050241c0d0000501040d54811001c40e40751044800880d003c40d28401c4415007001134011908000c9042400e00026400504100a040d08641070300c209a8102c1c1180099183c02c040080541041d4001c441c108000000e00741151403003000c03181d1409410400ca0503c500300900b656000f01003510a0748801d000d07516401e0030f0300005100d0700702420000000f50240e40c0c2d407900c4102c404040100040c014a00600c0403a0219441d4444c1c25407103540d0800502c4d0240b00c2d190072098100214001c400c590500852401c0d80d00184080ea2a100246142d24400d000a480c3c00d14006200154160414400030907401c050205c00c1210019803401031088840c0d13401e070110301b14180d50b110480a0b41203030801d1400c00c0002c2540942c8841c4d104c82c081072302d080000c1072802c104d2a1060030700417604500045464011b00805114280e02140900c080089491038101150414041e42a141c003803948e010404800341d021300c40c3c0d030315401210b0b20304401084415114010041006607851 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770576097 1250 770574847 770574877
    0xf03030212030705160303020409090309170f0a06150503030d09060609020c03030f09160909050f03030906070f180306051015020a020603180105040317280903030917 73
    0x151071030800710403240988103542d20940b90a010140060f201c03581500b0803000c26601700030000e0350134402e11401c1500c40c42a03644041c05441c4c90a00309ca0440c41000a113043d40043c07604000002001a861249036840100880c1c0580b4212000f002040a6480550140400150360b0314005103070744070241c00d91003404c0c1040713107946030041076049020340c11300382c0e6680d40100041804800400200b5a0041c000e0b021611004d040c03084840040d00c284d4003030f005140d125000ba00400100f441240000940c0000460440c504034011a540b0740700a0480001d00c901142c0306541070340f190080358000042c0c002c40c4400d15981e441c1441c010401110144085088910080b07584201d54545000c161402d600404691409408110059001a1610300114420045021810020300034030344218040d032681d100e0f036204240c241401c80c0005000c4014144480200f407183c18124010f80382e07464650100040900c818038007a0001c006076400580f101c02c000b80c03602401d01010004222440a000721 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770577347 1250 770576097 770576113
    0xb0301060c05151303050702032508011d031b0c0604141207030c140f0306010b070302190308182103071808102d140f040c090e010e06010f030302 64
    0x38040c42c070f803030a85203001d10011100003903000c00d125002804200b40020b0a0300ca81c8940c0c10b0544803c14107883c4203005a00d6802c40c2005000303c20311520901c4401c04100c0c0a0318103010b24400d40b24410f00090003140280e4022240300284100114511058050011955075445031389641f20700d50382c0521544507407203240d0034001d001d801103007160490740d01980f1401d4040c24060300280c1a40150101038000c2080825100f55540c2000004d0007000401e10f46a41d90740503003002810682d500725040c0000e0b0300c155500303000a03801103005511961041d508907944540303440c074505040c01198010040e1800d01004034480e0400d034025800384859499200f013201c0008211036001810f0f10480c00305402c050350f400c2000c4015004180b400c0a241d02c004c01c40203c074000d140c0ca41c0481c01018040580d1005d0102e548204485510b401c405501c080443c0c038901030303039a0400c0306003501403540c200d91a4140800241800d4200d00803600c0070105a9a140da19501c0d80c0d41c5e030000f00d2009034014450848 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770578597 1250 770577347 770577373
    0x6070309120308240d03051b19020f09040b01061409040f0608071d01090c020c090103030302071707111915051306030e071a04090c0503040c0f06170603070b0301060c05 74
    0x34000b04c000c0c0030b490064051400e8030309030b80e10342001c248411502281083c40f400800c0c2404510a003a4442405021704c1d180c40c014841e42c116540c01550103940c0200600002c1083c0004a504443d110715251440754180c5a90300e10500a120030590824109480c4051401c0c3d60340200095078841005c49056642e140031200103441c1039103081c2001941000184201c1c0c400b900400c1d009280c41c0110f5a08104040200c2d40c1da0b1000d9000385d00195000c039550b806c001e4118603500e91044484c1540342000071688030306510f0310010101c2c0348181008045d82110501c100024001020041c080042c80b20100f0760241c040d500c041c001c0602c410501e800850454042e100e0390300c02c000d04100034030903641800445241d0034240c0c0302c0d421a405041c000041c091404e4000d482803c2141d658458807400c042c45c000300051080d810142e45440c14039028043c1651040703c10300404000c5154540c0c84c0c41d99401310b42003038516000300c089104000f0003c204e03580c0140082c10114480cdc1c0c01c41300860000311b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770579847 1250 770578597 770578651
    0x30102090d02041a09070801081b01090909030e060a050a0210020705190804081b0f010f0206150f03060a1b0c0f080d021216030e1b06070309120308 65
    0x5116198040311010704640542803650080c3d452054103045151120941d0b00001c542002c100c0d42c180c0040c2d5032030014495801c09118800c0303031072031408200e914020440c1c0007a0409001703000b981c044566a2210006241c8a0101d520b020900a4030030365035807841e00c1c2d00515a5110310120400342c4502d144601500e01c02d8030032905100c1e0800d0182c4841d40c0c0e0001401d0045081e034400b03460307021043c800441c005900344026003841649007044070b9840c81000501c408600c0003000181402000d010704200c098003c40c40707a40c002c82c605250401c0b1101d1100003945a07131880c2242c0d4051040340100034404030b59502200152240d110a20110b0340c1d815011034a1000e590401031441b4804042440000da0420142000700111500542840f10502071503035100e00490b001c40002403400b080140f256018428085551059000f81c040a0220641031080340d40c0a450180070710000120001814495544c1c1400b40c4102710780001c4e540d80c1810001c04880003560b07400d00d0820750340d002c1000c0540e18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770581097 1250 770579847 770579857
    0xa080d023a111908040b1c2d0e120a05070b09061008030a02070b130305151618030807210c05010c0804021c170c03180d08072004090501050a0b030102 66
    0x1d130146103843e05014814020750490440d4001c81040c000c224114802d0710300542c258401c0c02d00c4410310b5140c92880266000e01003011041d03640785881390030481e9640c0802c1d050b40011844131540c0e0b0b585184e150441e5144375030640505034a4540050180b0041e0100c0c01c903016440002c0c483e000c041d122843d4079240c3c8507504a40c0056400010200b2083d001d880140014000e00e800010307844d0b960f502c94070300340314101c0340b2491071b4040e5500b00306480d108209001c2d0f2a00f900d207001c1030071200844207180050b0150102400000010442c0400c0007400d001c0307450504951041043e90300c101c008041d140400d0134000b1140755081c01c145c840900c3c03040d60050700c0340d60001c0001c000c030180200000110f01d80c0610598030042000712001c80242e100d00100040d1180000541c0e8812854440b9044030428400181c42008170482c0d00000c80c4d0701c041600c49035508480468007103100e02240d029a040e951101e40e41041c2030800300c07401d019040d40003520403d0101410b200c0c0b40e0360134003014203d00c61 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770582347 1250 770581097 770581103
    0x100f14011401052b18120f0903031b081c0b1005040303032a120b0a0305070501050f0c0106060504060f03111b01020d05090109020a080d023a1119 64
    0xa00400340d00f0300e8a1240c18224101410300c00f82070300755011241040c0d80112807610751a0a28001741e0301008510100e1940440c0140b500003150300165000800310381d001c0c032014080005080c200040c1441c0b100107a04c5856000300055610300c20358008880c0c00510440003110341e407900803050142d0414103440c0807104201c1c0c2e034143c9070a003103641c241d00514400b800c0c5c5211040c0c040c120040125901001c13000b4650640ba115540300006004405a03200170f240c050140c000c400702040011070000740103050302c0c02401c00ca9260b4000010200c054040c0c035400a9582d8241600050324542050091060703441c1c503a20342c1d1203026042c0081e0140d694800203000c00707000030842110017001180104450a09180025180440c4e1480210550384241c031403070142c0c2d5441d00310034110300d40030045da0001d0006d5005000a00030035000a51688542c004e1071404001c1980030042600e111120070142ca954900071801c0c3c200034500041058100a00c1d0088910411a0800d0071420110f80301c241c6540c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770583597 1250 770582347 770582357
    0xf0106141e16020904060518070509040206071407180509010b0d0210030f020d0e070f0b030c070c0e10060906090b16051e0604051504020607030f02100f14011401 71
    0xa2060740329045540070785054400c412940c001d240c01a41d0703501055000300d0061034042428100b04040607541c0341880c1d068000c5902142d800c1140352a64480e055000340c040b01c0e560349a104605110b030002141044441c280c1c01807500100e80b40082c540160301c000034264041080350b40e504001401c955a01c1604d90b40f10311541c0040c401450814a0500550614580400c03030147c02c804820590300300c018283c41d11a1280c05804490808000020040c070300d01d115182d441d442c110740802c03d1700c80500b604070091400208a000e00134550458801800302e6a500545450000c4000c0401c01080c003a02000604400c400150f051148060303d0588a1039000c1e0761801d069141800404542c5180450b07060141102d010411030003000c0b210040800704024100700d140602c0c200d401e00224206514101280e9403d20025803240001c2c0c07082c80707500d0b0400842c4660204401e82ca42408458048202802e1403540b400454082c0c211192040c05180350003901e9884028140c0c82412070120315000076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770584847 1250 770583597 770583637
    0x318030e12030c03040e0103120c030c0609050c1815040533090709090f052404290f0a030515150a0e0702100b03070605070303020c01050f010614 64
    0x200d00110010607030070003007086a20f01032100d15103900399006039000050071104c04004005002214504a0000c905403410300440c1c0d8a030b64000e03002c0c0685000140105a541e02200100320040001070f42001c402020313043c1c5c01c0440c0c08480c4140b8811070b0740210a404140040100782010700885004500000c490403850020816030301c1d160002c042c01105818140b1403452542d203030f04103007030300403121961100c181d1814800c5840c10344056003111040d141c03174403041003810398040c1c414540f000c034505426250310b50400c0c00070380945040340c1e025440031240000f061a4034901644034030b0310001900ca131070002850104000996445c0e21001c0d0040d08120412041649034140c855481003081102c43e541441c8207000c2768403c1c0154000d400b01c40c82c2c407014000841d030100f1190b49100441101400300b02c407000c001c04d88520191103688140800800c55100b054001d4068034440c0060380001c010a00d8008821041e15000380310b00c1002c54441c0084d4403251040f2002c0321001c0d102032000004034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770586097 1250 770584847 770584849
    0x40c05180f1306090b07050714030f0a030207110a090e0d0206040506060d17040f0306050a05060d02040209040612060c0801150509010e0a080d020105090105130201020a0206220305010504030318030e 87
    0x10b6a0003010480725580c0e145002e4002903044e04a481c00b0b0a559502d45442c1c0d4010b282c0160588000840003003250b1003882820071070362242044803992019882d025807100064600070002e20b0411508075070181510318003103103910103544111404103402c0c0071a000400070050585c2c8070181980c0c0a016a000400001d18600340301130764032411446029403c400784d05180851410780c0094000903440c60022108109108950158680003044200108554207000001072020401d10390000d008903004940b0700700e1075555600071001010394803a10318452070381d403521b0741c01490b07800310345c00104081c1c000224030383c40300d142e09040c0c40049440b80c3e171410f9160710054488540305e00c0d255070f20040740380011644003800e200a02c1d9034901600046824144500381d00d080d900000c1c4103460304200c40c1c80c0c1c6005071ba800603c0c481182c0c2c040e5056955400c01c40070800c1c440280c511640a81c0b02520000020400154009403080c0d020766820818003e0144000d040410341485c0600000ca10343c55501c42 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770587347 1250 770586097 770586121
    0x709021c11090604030503030402180c03160e0406081005070903030504090209040f020c0a050c030d0203040603182406050d1a1321020708030f03011707050603040c05180f 75
    0x2100e194000d51070b0a00020100040d451352003a001100d99400106c1404214180304038291001c036003a840c007200e07030315204180810394080241401c820b01c04441c064580580565465081810058402c0c001d00c0e865102203a43c8000c9229100841481c0c08000b4038a2407280c600380e0b0030381e603040c3d076810b1500386040380380d1019401444d4043e81c0595136103041240341605200811000e902600545451116820024101007950603494080c1c0c00041a0014655000c0100c506444c2c4a0078009600c0d032407801e5001211608110061001142014203c000903091064106d48030031078905000040c3c8400510006079050740c8010040051110110840b4004200203a800810f611880300207040c151a0100400740c056440d17100f0a0200e08030f00c481c0c40e0305108a501a01038030b4003c510307092204842a02134401480380603209041002c1510700c503513041c0602402041c004210a4490501d0b00702910585014032846225103140c4200c00710030240900058800c0d400546c01c0400b5030381d240b2200e03503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770588597 1250 770587347 770587361
    0x1807030311030918091605030c04020a2f160b0a0509061201031103010605121905100e011508010e1b0103090803130302060c0c070311010519110709021c 67
    0x20781c00140405816901c81354008400324510b2081c0d0940d50400c171003c181460307540c64051301200d80034841800325031000202401c158005842c010b0f5149540407040750440701004001d980016547c0ca03844030400b426400125005d40c503800d0381c40c2c1703450700c01103103114881520a0158600e400e06c508031229001c2c80c0502410407014000600c0c00310405501540304c1400d80080382c9603810494130380740500b824400c0002801c0e069620070303150090701002603170711850325034001c41c40c0003454012400c102051181c0c0c070070b518402c0414003583c501e4007130b01400707840002d00c80c030424000d156002a004505003e40342032200020003600c040017000922154070658a00c155042c1500d0f80041c0c000075000400451040200c000001d40d81c055a29009041007409000b50000c24001d00c01c0c916244800701d94041166444075502c00c012900400680c3c0c1b5000307041c1c59206140184600c80003090304143c0103d00a002081650885900c4401d800102e0048030100389003000c4480003411864600c1e413102c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770589847 1250 770588597 770588627
    0x313030801150c0305131215050912040902090d05030a05071208160e03120406020102090f011e1b0606080c0a151d040906090f170307080601050a1808070e18070303 72
    0x41c1c1071521001007c04d90048040c01305c6071300600c400001d403c05020320505800444e0b0b03101400d0690401c01044002e0f006501501040d01d07800100100159104851090000d0703001e0107036511400030700b10290080d08604002d46403030445103908150144a8134440c0e11441e0150410091080c20300703811540c01600035a2942c140c41a2144c01c60101c551901800050000d54000340c3d03180c41050a010f00b62038880486414080303804401d031401e10181100c0d8480890078030300220400700d07441036501303209440d40c00540001d140034004201c912010413204e030944800c2d50103440d03281e034400705800b00701065500c10b400221081d11440d0180600c2a0b0807003115001003006c281200c03240c882c042140e020100480f0400d105103c40400c00c19049000d003c0c60444849646c01d40c988075130003504007080244054100040060031503135140c0109a048040d64514141560311a107900b4040d0b502c00940c01140c0d61110500006001c4070100c4050544801c207640140030164610f5030300341e862010022a00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770591097 1250 770589847 770589877
    0x40309030b010f061710060513120c090509150a0908040f080c0109060f1b020d140f0f010510030f0c08010c120605040504020906010809010f020313030801150c0305 72
    0x1001c00c1c00340340120301a20700e02114454080c0340c80400360061002011549900b0f03186410000100d024401000403100c0d0303418040d541e41212500e42c00c000503a40c2080e040d0600c00c2510505129207204010141d54003e603007003055032100c140695841d444a1520300180d0608000610000307040d402159086116104850a060b19200d400e8681000b94105206d5940480400d107410360b4072065003402840305007071034000074050750303c0207002c48a0640140c0314500741902500464450241903045103411517031804d00707001c0410485403034140318100355120340310340100703100d02c50410722641c1c0c0581459401d401e812881c41d42c8458045100d00d9083d00e800c0402600080c5001c0d081c0128900d50305141c0d00d2240320003a070003441d07044410581055024a203070408200060b00d40f4020980c214009082c090303819914007403e20b001d400d200c002c51441600100c00e11001ca01200d529500840c0320f0b03220410030780c1c3c85e60080030880c4500d091072030007d8140070541000c42d0041c00100b0b004041c902031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770592347 1250 770591097 770591099
    0x1022a10050a050702060c0f0a030216080703020f0601050f0a0504051b07060c090e01080c2b060b13020c06040605071b1103070801050907061107050a0b032a0f03040309 74
    0x1200441d4001c494414059407954200910242d05004242d80700140084483c108524041e0910060003214000340915600082c604040c15400c5c0c03c000c4000c1c0d2180d80340b0b94a803035503d4002d41310050ba003401d0240348540000811145011103544142910182a0105181c984801c00c00034081c0600012035160580d150b14803045400001040d02d01d002d10750201c1ca00600b108000c01c075917a1b5900c0388801e0078040c00144500d0354007042e13100d00440100c6078624001000c031508007020403400300c0c80eaa0100f81a10b00c7d020044143c02c107504603641250341900a0000d514420140d204900e000480b80d08500c0010340012007991005410480b0303407070644c1040084920b80080c40f04404806c0d212810f03001103406051a0811518010700510002031141e401c080785641d07070341c03038481c0541030902c03d4980d801110a001004007a0007070100614800006540e008a481c15900c2921010010170900341c00f00380d424802c0b016544164100c000091400624210048544d040500210104445060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770593597 1250 770592347 770592373
    0x30e010506030a0303090f0c0f140906060711150c151806010e0c04030605040812061e060c030d0515030d050c120702030a0b0403110c0a03020f010c05030f0d0207060e01022a 76
    0x14000c800b030046278403c007981030309000f9030f1244e03030b00030444030741c0304201940802040c0d0702d07103030180d0341001c0d848894541500f41c240c00050401340c4c03d03085900c218900ac03440c05400d000c006008d8100c0c221401a0072859200c1007020301034544d01c0c00c540c001c958401401040100203a01e441e81c0c0c40304000382010b05240e01d82e50340c0c02c10f60720182d509880076071012403485d81c0c0c00d40c10303102550024002c0314034202070210024a08001095a08094480d5101040400101d001030040700c00c1241240001c105615080940110545081480c1c0c0e000e40310317644100300e40300e002d04201c4d84001891070003040702c0801202074000940c085481242c25000e041c0480000840c16140b00e80194400d4551140301841c2c034107207602c1c2440424001c0c1c490034110300100b000d0b81701c20f802504601710a2034051801038060404070b145101750040c4108142002401040d450610380c0900403c51003a4002d000c80b44811003900e00303034090000c003213040c65070f03080c8004036501084c840c1282a80b20081130f5030304049851 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770594847 1250 770593597 770593613
    0x60f1e050306121f05070c0203060115030e010e21030408032d13140c0f1507021e040c030509060601110f030a05031f08030304140c06030a0c030e010506030a0303090f 73
    0x22030080f500740380a100d0414a6401e003d003503401072481c0382803c821f9502e43c0029680721410f110703905092900c105010700581c032075001031800a2184009100d20070950550664904140e142140200580e00c442c0daa02c2480f541203d0013140c109406600f580c803039009000b104818040b012201004000303080072615441440c061140041c0c51005803080028205010240221101e000c2e06400180c9184000d030345014812030358560550710348030449401c400525440c80f99020180d13115045044075000c0c41d82d8800c805c0000340043d1400d000040511405a041e1501581c1c0c0e900700c2e400400006100354030525955107095824411540040078810a007401d41d1b020390300d65400a4000010088515a104030414040d08034040f0340558516256031207459001c081e00082c0880b03c00b030f0140c1c84d04841048075510410300181203582d00d040c03902c1148001d04a02c04680c0110f820441003025402c0107104061081c48080c0182c003d034001940c04a005020001c011a44650700c100000c1c0890005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770596097 1250 770594847 770594863
    0x8150708010338060f0103110d11090301060e0106030b0109060c0803190c11120705060c223002090723040f0f0b030403090e060105070f0b01060f1e05030612 69
    0x3c0710092240c100b810500254840d922600f41c185401d00044144481e1108102c5e5444079030020b000078000c046c200c0a0449100d1030840c507900d5070a104002c51101c03111740d4141e0486510792410000f0601e600019100a2518400c40022800b55800e0401064222004582c04906201e041520305c2c60304d01c5010480e600b4104420014000307004800c02381104210012000c00170200312401d010441d9038140d40c480c0014a83c5d6521200131803200000d0480f4490824120801110492860307110300b0401a04201200c11105060101145000e190729402d20103084a401a0215800d9640c146094510160190301c00541001440e40320401102c284050320280c101c07084040104c91030040c11580310451500305411983c020000c1c04002500400350000310341d0a12010640d0384c6d076682c0141c030140500000940281e01e131202540c1000b144104560584695444640c046801400c0848868442e4162040100240161036000f18095000f442d407140006186006007004141b08038208041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770597347 1250 770596097 770596193
    0xf080609220b0709140a0b0f09031501030302010b0a24030b031905060105010f08070207180605040f0e01110a021b04180b04051c020c12010f021201081507080103 71
    0x30880050001c00c00c805d950071031442c011542c00311b80c141040790b06003192007800c2d09114021000140c10500b600d007845482000140d00e1400c400355a900d0030301034041d25010104510828a080011074001c812010b00240003110745a81556030301903000c164020440a6241c2c1d50511078040504106080c1c20090510b0b54441c10150446515140c00907180001d40c10000c014030000f03c0800c503055a0004003d422104c40c65a001c0f400803030717592654018041c80c1c00c0f090b001420500198220710981d00700c40d00012040008200441d0112140c080b00c0c01292440d00060308003040c00e541c0c882c1ca01d4500381c51120010000204900a01c0183d01844260b40085130003660390401c0006000303003441a0203c204a00f040480e800d02d4041000b52258641d04030503100740d0715501c5020802c10300354000d41c840d0041101c219650745004030036030b4651009201d8002d4902c030700e462018484803002400d900031401c98440c41510703421039903151002d40710300480c803040103c1207001e0120719045440d0b004440321 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770598597 1250 770597347 770597357
    0xc031b03050d0e07030f0b040c1a03100e010501140702040f06030302100b1009090c0e030304060e0a050301020403030804020603091f021908010803030109110408030d0c0f080609220b07 81
    0x71035100a40640f0316400541d012a0402842080410941951000703d20b51045008403280d8907458072a2105101d50052007080c035a280700000002010f50046005140303001406942d1079560301c601c041904240690303400203030f20b00101c01c13507110424064003550f40700410126143e1581155141258103a600580059010f41005032400019100390010854288d665000b6600800340141500900d8402e0801081c2d5450702805a20304c40c421911841070020162030b6119940c1000a059180c561041032045150400c00a400c0c070741482110100d13607040d201c880c0341d69225020040e0b00d03000140814000c1c018003540303607410092000c49070184036000a005071240144120b004046492042c1582070100b00e000603c00007800000b520704540410382c0104018465040000b40c50003141c1c441402444003007031142c5519440c5d0081e6001140c1039655443e0294aa00300711048041500c01a4110300404040354610400307200d4001109008504480c07100c0e480d5883c005510304c11902c0d500091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770599847 1250 770598597 770598607
    0x1021606020a120902010e090a0b03010c050a171b160506040c0e0a0905060408250c06030513030e1311031f080c06091c2906040c050306010c031b0305 66
    0x3d410282c0d807240700d2900e4604120300300341e035400030f080d5600752030300c06100302d4a440000345010100c2c3c00c2100c1010020300288011044000044c04a030040036500011a004080c03079100000300d03140c990f101d810900381c5940100c410351607410b0103521144004c0a41c10314400c014000c90010804580604d02c82c3d00110130301d6180c85c410900700c1d030015240b222444c0c240004c26002c03c40c0020060741054010121503030301d00d0035840c0b1a035000d61010b640f031a8001592140d8080c807124140020489000703440520181c0d83c2c1002c4405880d0711210018003059140800118608000ca500c0c0e624444201c00010040e40700340051915420403201c2002d4800f0700c148036010140c041c5410301c014001c80c2c3c024600e25030040700148003400783c880c074a4003940080d00200f44a0956800b038600310354100c02c1c4244014001030700c0c14503100c0c079241c000c505050110003281042c1494400d4811000c00c943d5080d0075606e400d03004680c0f5080310700c010b03420000243d401041c1202c4036480d512070796100f070315500d40e14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770601097 1250 770599847 770599867
    0x50705070e0a140702030a03050c0c010905060f18030f0309100207080a09080d2001140405060a11121f030503130302190f0501050c0f010524030601081902030102160602 74
    0x1440005001408111070030741441840c40c0c000047d500aa042c606000c545540c49800c03640c42c60052032a03004c559802e00d0b41c04410310002160440c007071b0204114011303540c3d4414416111100444c15515030380e03030081001165a070840405113411520a80588a000380310000400903601305800550f002c0200141d03d040103604980c4500041c06614081c00f101041c1e810042c080050150180310045411101080040c10031740c040d00c0107003001456807070a4181801c045a42e01030489011034080d160054040004120380240ea50710400c40400d945a03948000000d81e2041408049071480079003902d01000190702800642101e44031000149105032842c010440390075201c0300e00f50701c0c80c100a102400704180705501c07203056940c2801c4c85a0390345800032040386421a0a021244654039010034001076080c0d54803261180184e50b01568040c0c0000820191101c0e002c0c4211001c40c0e11440c64010b1800070b030002928600d0000300014104410311081942c42180b40000721003956001800b6904 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770602347 1250 770601097 770601101
    0x11401060e2107050d0c080607170f01121211120a030c0c05070e0c0714070320030606040c2304080118050303064b01020a0b01050d03050705070e0a 65
    0x4100b503407424020008018801c854645045003e1507024007045a866418881800d0851000f003480134111940da1034012030082a007280b5800d04e035401403021000c14101c4180c0200c0328140c45110011501d00a410780e22010b2488965100c1c40a010b280c1101c440514002d004400c0380010305100d1655840c0305072001400c0707942083c410300902082092410114030001110004d0f200344100540c0180c480c100180712030f0090100c02000d11040028080e044030b004201c130000c4034402c5604004440340304500010b1052140d2071030350980c0c004000140d003482d1680107038001110310b041c40e1080313a51108040740319030101c88170340c01d4200000070300b0816103034240b0503a0121140a00c010f0808841d940c0c2395a00c81c4030140503244a00c1c40d401c5214220042c07101c0c140140035010041c0e1884500001038070a042c41c080400040c100c0301c0c040c540403d9400460340f84c1031543d010b205240030342e013801d08112907054040401d404004050103a400010030800030100903240c004081d4802c0e141c00400700007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770603597 1250 770602347 770602369
    0x1107031806022d1218090c03012102060d0f02030103050f0a0503070b06190909021003050105031002032e08100c140d0f0c05070c080a0206040314011401060e 69
    0x2158050000d8050031003004440078074000c6600c40c003a0351643d070034421502d010728081030381c03510600011708000c017922075000c0c1804e540e0064421242c030b5903800754021382d13074002480b4500f030301d020f1044480c0f1400c4814469101e440d10052405040001e009204000c030782181b51141202c41e4000014402c0c02420880304550b154040d000f040b240c9940d070b83e166101d0040000081800c9604804104143d480c48018400c8411310025001801c2e941d90b9482c020344500343c030680c0039010300c040c0588600e10234050141600d00c041c0080c0284030001d14000c009500c02000c20350000e02ca100200c12024441f1a0130951016200f110781c070107810003400c01e02305241a00d0a8204610300002440d50719000520f440360035030500155038072110f180811802070700450640c2401c940c5000c1d0800f5607150410050002180a850005149a11040b48070b54910000d00d010758030480600c010000030300d04406180d000d41e001c20002c100300140b0020b00d6a488404c0c0c1100c40030540003581c1c084141007441101d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770604847 1250 770603597 770603609
    0x9060e1005060a0f1e03270519080405092a160204050402030a060f0c090f08250f080a12021b10230301090c020d091811070318 56
    0x300c1503840c1500281582c0b00b8202004280188402c0d5044a03500440c00f440020b0b0008501d40c0510442440080090490a42d9074540c40c4880082850030714000385040c4070a54402c00a041c21100310b05500c40200950001312126503040202145540340d04031641d004482e1103010002c8903c1070000b2a91040c0f400b4604900c0007018000c5084008103000030303800c0c6a4050b14000780c9038940d0300129082a0007150090034441c10614441c0a0104681c0251160b81150f902c100d459610b42409120180c002d100303200c115030091800701040410061054040c1d244410302820440d0350ba460101e01100551000d209a001000071800780300021071070419060941c4060070281f4158410130342c0151400c5005402040380480c1458450701901e4500034034030013002c58503004040340941c03460903031090146d004514205a603000c0401c0c00003600803010784564403007070500c6007801c669030241e40e10043c44a07211512440110380e8901c2490051807120300a940e03c907035807000c0c00200705500e00194414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770606097 1250 770604847 770604871
    0x60103111b0f190b0f1b070f0b060105040506120a02090d08090405180604110112020c01090203160317090a18151502030406050c03040302031509070605030c0a0e0d06050109060e 78
    0x64400142d01900455000b036600303d0760080d6841c0c04141b84140d140c0ca891460103e44d00203000c80904c21207650403050f29102d040110150f6a40c50011540d6009510030b145d00a01c091001140883d00302c60095800103115400508000c1c80b000040c011801c030300420354580b500052014402d0404d4020b040d403000c00c118010350342903005082c0640e1400b00400150031358240045200090b0701c1403134550801c070f400c80c006545030301000001e64028400b04500300d10078803c9100800700c0e0082142e4003011240c200104200c1c5901c0d40450720603d90110b004258840f41c0700c9800f08090b210000c51b5501c00400c814000340501c00f000c180c0d11240c086400110700015081200b03503105a0000444003519102d1901d80d80b90fa8555541c10310714000c0f508025414029041c3d000c001100c2c4102ca80d10426400045402156980d0001e43d103d10050390144141c090030442070002c10b000348400e005441000c0c00780d40500c040f039202c440444000381c00666202e40c86220030041d0b140d00c04001e0b40c02400801074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770607347 1250 770606097 770606143
    0x109020a090905011508030c06014103010507031d0a021302070201031509022505342301090b0306040b031c082d060103111b0f 56
    0x2a2410040c1c0c421800c289403154030301c40c20410290005150031003441c104040098403400c01e5500e940001080c1340d020300c00d02000203a000c03000043d45020040600d107070034032104010940c14000000846058850700ca50a40c04c0789500e00f4400c2600c2a1095580050300080c0303441e0074041c8140941c0007224a034001c0303028902503500d0b1510141a06909170005030758820510059006d007100e0b10300c6000c0100d07042e030005481c84107500141004031658003900d4484507507542c12060340c04118000351082d8092a0026070200c0e120b816040100420700341c3c003140c2c26503501c51616040b490381103189011107101840500f000355952040c104039003400c04810380342c1029500d50030390100500b054480c035160a4000241d8038140000e0710035401c00040d018144040713141c040c1c00e00b82c040c0c2c4e928100c0b94003824040b81c020703014031001d0b0740c068a4540c60101910f0b64001103015000500d62418841802c11100c0c0414110b005020000d81e6241c02524641e1407880710581408400b0308000003a201c9001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770608597 1250 770607347 770607349
    0xc030402090c1305120706032412152a050f0306130905030c15011d04110a1502070801050108060702190309030b070c020406050f01020a11030f1507020f010902 70
    0x80c042c1c0c0408601401529120828600098041c032980b00075000b080122482c14512004284401680c8061b10244003142c04603040c2c120003180d1096501003000307520403c0c0b10079250075020310f8101d03008091201d06a010100e80343c0c00c46a80240b030501d0880070540e00ca40c1512401202001d921050409904080220001e03078024400184054420088048074800724100d81c0c0c00b65162640100c1283c0d209c0d101c2d0074920369034484131089000b8071a40c03d40006034881802d142030485400509480702c690f29141c0e2441c0517029021020f40d0301400561001c01c80742e964034040390b41078410383c3c0240181d51509070a40d08450041e000f12615400450400c000036400244c1c1590000c00f0151028a40f80d4a08080300d0300000c941000346405814400e0101c00340d40100ca0344c48040c001c4404102d102d645d001000400d5080601880c096008041c508001c503040340300c0c0390f4030518040c044d101c1d82d8148029140c10000303c956004410300200e014003035110350401000780da9890f4100200002043e0350 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770609847 1250 770608597 770608609
    0x1d06070606140f040c021e0a0b0702030307080907050f091506030c071a0105010c0f05070f06050309100e12130e040503121311210d09060e030105190203040f21080c030402 75
    0x1a2000c2c0649030441c404a484001003000c810840c0d0000200b042d27508100400a444e030f841030300c0f0040054454400b06d004000b000c202c100849200402a0060810344828061020801421350b041c101400b071184101c0d4603400e00540c41007482440392940c5100f146045001c207181c000d0b0401d5031000039030061029036004882002c40d42d8000c800401450140c0ca4850f10b0100c00e0f03006504c2640000d0320028043e508040914001c00c0040c05031041d401c035240200046440f074082200b4690710014156051030340300d0008059400d2070702000d6410a48071101410041c0c0e0a413230071100b643c00081d199030009919610680c05c0f801d00130780c5940d50006601c403902010b0441681e94800c10074000304488000d01c0c1481100c001c44130031309039403c00075075040143c1020401d228110114145014003541450103200f140c1c40f4a10302d25020706001e00b11410b01009402c010811200d0741131090340ca502080f07401d61001408130244c410150306480b1a24000c265610140c0700c0d054111040c4103010069a41d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770611097 1250 770609847 770609863
    0x50702030a030c080c150f0106020d090e0a0605090c040314070312050307171302152503051c051f0803160539010f1d06070606140f040c02 61
    0x14900a520f004031414040c0c82c2d40704182c3c0b41102032240e4260300c09001c000e464140c0c405c000300302408076140c4c0c4c4c480050741c0b2186c445501c600001e040e00420300030450700d001143e4000750012800200b040e100e801140242c28141d078019011407002c41c04004001114105008080303074940585040c0d481c5075240c0c28006100d072010717070078840007100160341180b19624981e0340c044158a030403464107090348c034682c4601030300b14107a00400100022001c900307a52800c0b103003691002c0703d00800b04000324407070490090040d0f07401c0301000f1080020503141e12130f47c0301c80700c2100f0700c0c02c030005030a0600003d0361b2907030200d8480401c50303000604010854102c0200540750414103008000b0301c000483d03c2c1403424104124030341d840842c03280920701c01c0c0e41422480d040242c006090850103d207122801902c4d00e107005420040001c100640f4288081c0760720310160003a40d405481681032580c3c55039031b0001d4440300d400c1902101c09041c1415014a0100e9884002e00000d84c2c0821101c190703c04025210084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770612347 1250 770611097 770611103
    0x40e030c060a0c031413020103050c0c0a020108060d050106180f140103060b0a17030c0601080105250e06030a0903031a060301150c080a0906090b040501020717010b19060906050702030a 81
    0x920f480003035190b80641c02a152441c1541000303802e620f0080304044000d0600417060b40002d10307001c0041e0324892080c00b2a0b1010b00c0e507000802c001d091644c01111624001840306402c40c40003143c004c0022424051030014003002c00ca00003c508605840008442008440f40e1126080460340d000d0000201d4815043d01d0700b240e4041103015496011030b0b22140580c4c0f2922101c22904c001d15400392012015020038001c050035181c1e03507681c6011150a0300c0c0c1c10f50300c031400b005900c41d0030f855016950901d115222142c0c01c0c003454030454000043c4c19508100ea186180d0354482d1261400c00d80e042c0703d21211880300444102d651483c1c0808154103000500a0501607103194468803d000d000f190700c01410b070703406402240c0c0d80c000b0003001445003481c1d200c2e07940840d65060300421950404001d076802d646044e401000c1d02c1d03180548405080d0101c0c42042c404c0c1d5600d50940010703844041842d080c415080c07640c00c000500e4958020719151407544141d04000b402c2c000d001c0181e81c00300300e108920390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770613597 1250 770612347 770612351
    0x20f070f0c1706010312030b061e0a110c090a0507021e060f0906070c200d0f060605270711100c0f050f040528032d031e09050a080705040e030c060a 65
    0x15410f80071580c1c5105590303001c159150202a00c402d092458002440c54400b2335503001518610207031070381e590f0f6004844955024259070700144c0507c1560340aa0352118030307841140d440714451124540850349c0201890010340154081000c100940d82c0c48a400c6804580186100c0c900068000d001242c600c0740180740b150702e4014850420f03140c280d0040b000300020840c0048407924036120b51951655141200d05500b00079000034186010580180300e100780384004440950500300780710080c4801441c8a0074081c18a2403130340658405c1000440030748071003400040d0061f00143c0030304481d903421411810403c1c00c02180f40051508015901154010b1b16281040f480102011112100c911800040c03915690000020b1101d1103404840034000c00d0480e0040540c403806103c6445904000074001c292002c424601c0c1b2001600c1c103d000e819589009c0800680b50700005071000f4140e0b10000c041d40c00f004040c001d038603040c4a00d4214072a044010361030003034105030342500d42d08000d000c0d43e2155 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770614847 1250 770613597 770613611
    0x4060f0f03020c031c0b0105070201020d180306050406150e100b0c030d0504030203040312090e0606030a2c01060b2811120304030e090118020f070f0c170601031203 72
    0x150090b01960303600800003041c0c0c0c0c0c640d0b440501d0300e5501c80141650044550400342c0b00045540188101c8410b40e806034058082d81104d05003c1d10700881c0c2290003552044e20b0a000400310b0312500c02d02e40128030480001c101d07000380c0a00715240c2c0d030036900802c0c001445442445103056288402808858405517515111034841c13011609500481355a00380160400d020042050fa010000b44292403203075080181f00d072440902219502d000c7e000c1e01500c000c5460104085181500c061544032001e424007103400034155206000d214048151080c101201c011035007800d101c20b00441d0301400d00d9000c5c0328141013051a800c02d01da0048001001500c03a051801e000c600d110301010b5a41c4a540030488100702d160711007020241e401140e09400203400d054803108245000d410042c100d40c66420084540305038945000b00a5100d080028500e000c100f00f14400550446040301c01c9a00800c3c05802c124545102883c0e140c0644504240c02d0f0807802c0140005081e2003000c2060302d03c82d1500048007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770616097 1250 770614847 770614877
    0x21050708012d0e090706140306040f09050d050c0c0f0907031d06130b0609040c061d0a08010212061207090b0a181b05070209060d0f080304050a1704060f 67
    0x640b50242c0500d0401100b2004600c5100c00300f0001e000d000400e0440719a10f40d100b10882c1d0034840d06103e0914a442003010680c0c03490144c00180601c20340200028041c00d180d90303017a180000019981d004507401003070140340e5000a00075140001825504000303503000c1c0390005800031100601c100181aa900c050483c4c01c061101c1170108102c0d64030403200c5c2420100100c40c14815814800c0343c0840d84000082e4082c20420300d10b40c0951741c0105810700c0c1c681050001d443d0144c195a20910410459240c1e0b4803566500681c01d009145203000160350380012202074000722070041159000340350142c0201c00311800025460100c40b01090b0002e003002ea80340020704840820350010452034001014a00398003180e40c07010f040c070740c07154010b00b000c10301154066509025014001e948160900c0024895050001c1882c408522442405e0340d03500643e601c100c410b4100350390030354440d8011031b0340c2e1080009031410702e14014074082c9200e06182c503100b4000e000c00e0460380072004011541c41d820040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770617347 1250 770616097 770616149
    0xb0a050903120901050619031e060f061d0606090612190203070e0f0a050d060509030c010903021605010806060d02070213020415022b0503070c02030105072105070801 73
    0x2030618034180364082c6040c03412005000c2c0405440540c0b185a01170107581500120f420000222a4001b002a6103100000040d00c0c4480354000705844d01500e50154124182061181c4006008402c42c0c200700205003021178480400014160384c001e00b4100404010b55451009682c500d0ba06022a22040d03074441440c0010342d013107030380100c0e104c90000c0148000c69820260111028000f0303503e00c10b8800c4008200601010140329040e0403455805907903000c100590041d603842030404003282e14000b05410210f0849243c0f48059006030061400c14442070044032545000f40424a04072172241422800941103220305c4080d46051540082c04004540f100f400c160514102c2a20454581d969409002062800400540018040e2440d07400c002d448030100e04e800030f800300b0070b127002c0c032400f501c0d06a40a0340b0242003c0d003400041d804d0200140d800740100792180c403003540c0b000ca9511164840303c00c040504070062801d01e040c0b20410840702c2c3e0244401e41150101d0f00c07100e6400a04c1d0703003e002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770618597 1250 770617347 770617357
    0x10e0309031e0c040c0c0b06042703090e01080a050607030903020c06071509081809130201030c11010504061505060c0a1707140c0f09010f03031206180b03190b0a050903 74
    0x1d000350904e05d8081c0039980000741e54401038000c960b03c3c8500e40e11042040100ca20007040500c1c40c41034420068070b444d1442044240081c401d0515441e0242c1392000c24040349400d0b44941a942c1c000100401000402d0106581202c00c030700703040c08200303410355029445082c0d60071520301500f80071402074203024406002c0ca041d200050030410254001d820700050640c441e103142864042d20010410a40c24100b140c140701e00002003520b8017002a6a0046001d066900d2810b401c1082d04012104c20b45800c0c85002e000311303c07884001070b07010701609400c02d0340d0707499510603441494240203035200007401003105c0310082e502002c03070614103864020a00c8540241a00602480c02c143c1c0168042c1200050302d03224400c00315025030039a15007008004121909005070f0207486003605080002900400140d03070010000c24020070603540300c050b5141041c1d01c06101d861070544480000d007003801c0078480c990050208414059840030a41c554014910020f040024601d613034000040c180035060095038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770619847 1250 770618597 770618599
    0x80708180d05010c080709030f0b06060705060a0506100c150c1b050709111e0c01020904090b060f010f0e1302130b030a06091e0b04060812040305010e0309031e0c 71
    0x701290014204035008040c1c4641d5040414405004154440d0160b590324040325844020401c500220742e8800c900840094a03464002c6801c4c40341d07000082c41401103a10070881407a00054034a0302c081080606030074079008405000d4410300f004042401c0e0100c40d201c0d00040100811070054100003190fa059108681624005020f404d0404104c4085419821030b0601d403c184a500d803603402c0c01c00c148c0b240d417003d4a008405a43c40204e0a8825009411a0b581900005060850f8030011406a42c510f220454a0020b032504102151a0201e03240140705020300c1c0c25040c0265504001c1c2800011200b12803098007007024800c41c2c07002d590100d607156094684040305e401d5940d0b203225001d400a60b0074040c002c1c10b01b000400c81c0891380c4030300d481e0101400c0c10582c6100342000e080009000780303009941c003e92560000b2500310b90030000841604681c01e034072682c440c0785080982c02c50b0100030000025400c108a010fa44d40d5000820301c030303c0015503001c81401050b1040c240c6c5400f602550b05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770621097 1250 770619847 770619859
    0x40f02060a0203220b04150504031b052107060c02060d0e0d20060604050a0f05090d3c120c030f0b01210e010204090e0d0f02060408070818 61
    0x1801d4610b9020024200012041e2080d50078075110022036000910180181008498140f1003006030380c40c407040000790f09000c1d04040d403425445e40c50300760814014811700400c580246070104403a081c0280d280140c0c082d241e4894441c0105e101c0400e4807801188201c0b001c208803401948255545e150807110b22000103c803c200140102058a45440c00d0030104800300f4041072444c103015068910703030420302c0c50201c0a40b07400d81e0303803600700802020040d29101c400c940d1012082950f048034400c6074002e402c150000c201c5203840f200c005002090081180180111607111800351194105045500100152602d80c903528840d504440306910070103104269802c0c5800d58484941642c00100e20309404002402109100c2c0015240b00303961450480c0c03203c11101d07204001400640c0400c203140d405500241c5000d5688840c0020303a2010032031001290040c0400c541c41d103801c0300364000e00342d0407030018111910f4a40ca5124030385c040c0d80e2000d03000a000291220007078600c40300403043c0e40001851 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770622347 1250 770621097 770621107
    0x30405010b010e01050301030803070513080d031b031103040f1a010303030501051828020f0f220305120306010302090a08060414070821090a18060b160b040f0206 71
    0x2240a860000d50710341c00308001c515026140d5101d842101d060343c2d001012686142c4070000d088a07558061070700a0b00c10b0482d01004504034100f031014000742c1029980c04612050320520211070000001d90f01010f15142044c02d41c00202c004040c5d036480b580001400c40b0840710350629a100640048140181003e1071002108054055011768160b80e019603500b004141003104141c0c00b00000e680c181d024650706100519100c03401d8003000484401100003505041003a42141040d0700044079403012490041203040c0407000041c05413a21120307403c40c400705285191111501c480d0400c40640b40620004000340059001c0d4040343d6140d800a403007195415528001c45485202c161000c44101000300b4013030780d4044c1c0c0003d01030107030344406010b420740c0b11000d071304d15050545030702985280c0f41060001c00700566402c032079000105603200c00f030000c1c0101c0021030400c071040e0381c0004a10070410310a020541e4a40c83c4880d103441e51000340d0404544850404648803d4503080003940001c00080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770623597 1250 770622347 770622353
    0x1c021c060f1503023105060d0b03251e0e0109050103050c03012007031205011401120203090307081b0601031b090603020310022107020d09080a0b0402100908030304 72
    0x1107000101d448020801125038542c036412003e071310610001c0c0041c0d110000c08040c50014001205c143c04025007100d1035450707039070f00c0404d06c0d03508440041881290f90b10099035960809000c80e080c916a4142c09600d00b514961402101400d40c3c024040b81c0d08485440c0b21841a00303d0400c0c014011640300c0d0241981d4078442c200c003816090008aa05000380c0071061028141401038014405414184145004d4105844985d07a001541c09500f0482900070f0007a26600501c1000d002c1d020941c0303417040042c035180001d441c41c140340b0915072409204104021000e01e022041d503c0360f0741e0088500b075407016400f4004d0100310407540d8500450045200010800c10491444850000554000b1201c2a03460780010700b110b520313220182d0542c005180c074968400659005003a170f07243c2284a00c80c1e0690541000904110450302e400251384a4403806104582018840008100703039801045a05400d40d5505201c0700c025000031301485800400c034805502400c03807240a003681c441140c5d140e2410381 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770624847 1250 770623597 770623619
    0xf05450402011d0f0123070c03050c121002090105070605072007080c040b2b02031209031b01050d14040c0807030512090109030222050c1c021c06 64
    0x1440403800f0a20408040003201003140410008190092112042942080040d600c225a14011540c402d005a084106580401019018a5005441c015065415460101d2800c11000540d40c80752002103410403c64000280194800185c0040941c4440c2910b0042c0c4150184420091809041c401003003511540402608103080242900302c56190342c00c100d0a86904c528050700181e0b030403419802d1a103040503003103038070290320150441012085c440e00c1d4100c0d9030301c0640d031660000901029142035141c1080043d1061600c031140c546031020341c03000617030303903031030494502640c0004c051402155a0080d400e85800f81005641441103001c0c10401d0301e200c4000700e5085036018402200400c5a440000e4000d003540e600100800303c41c0030100c8a04c00d103801039010030307041044940010005172101c0500294480d03000015640c8a00c5c0030f1600002e41d9001002b01131411001d00254603032507007204121002d0414520300507a54090590044500c14241e0034441d0560b0801e5400540c0e803c49e8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770626097 1250 770624847 770624851
    0x6180c06020d0e2b0f02030d021f06050a060c030215150a090204050607030c0503040f0e0402040c020a080901050a0e0d030f090608010f0e0c091203030604060f0545 72
    0x80d50f83c0c44094a0441d04003d4030003210360302030301054080403e002110111803200c4504031700070081c8400071031013980040d20340841a108180142c11980000c03402c0300d190000b0b59402440804203211003420b21003c68054940d40c41003004100c4104280e03814140280300d101000c0d02480c240314004c0c541040780c03201125a001d1601d000c1c141d040c0000403411030a109580a8401c010003042c6002e1458504070740b1b030007070b0395015103150000f008002054034015407018000e0051020300403c601d49401000200c8406c80310381c206540000c6c9400703002030211300442e401a042401d00c6a16404035030001c0761005010102607800581d040540801e040e001146580ea0468070381d101008551101004c03201c0e00d03000c1c85a08621809410b013800034540c18111640d015003066100d07070625802c400019140d10382d80030034840d6900b0010901000b4181805601c001e0803000d25035076401803400c000b2030744609003006030090741003044401d12a412000760040220102c00360040f418482c0d041400c00c4d841c1c400f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770627347 1250 770626097 770626123
    0x9050129120403081e0108031e040803040305070501080a02280c0c03150615021f0e1509010b040b090a0f090b070f02070f03020d06050702031c06030b010503030702030a06180c0602 79
    0x103500d090710f0103282e0005d100c034180c400c902c0145051032000b80f01c2c00c04242c4100c2c46150511014880031690700802c001070801035000c0c10092204034a040005000200302500c0b1300300040c010450780c4440003500881901007124404d0029038614400d0048980c45a12980282a90b2810500006100084241c40303a0314995410422140b6510702c41e40c400ca894a14001003d40c210031a05116160380d61031000c0b060344003402c007041840d0003503e4141080c00d51b04082200301090020b20030313060000d202c1c01010140c1075904000429607140083d003400d10007000d442c195600c8170192000912150440d2003410780c401703160081030800740030141000c5000c001601c01441083c000203882102074082400303da4020b490908002c0f195191000070f40401002030702540700801c80796840d10901d040710108425511000070702a401c41c90003010804040e448548139078410300000d4090790300850403920040d807000d0001800c160030740c1d0554101c81102c0c8003034440303c6a0100001c4848d000b041e11040007031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770628597 1250 770627347 770627371
    0x5040506070504060206010b0706150608100b03011a03151f1b0317040c0e010b0a180b040b07050109150e06070c050d0f02030706020f130905012912040308 68
    0x81e070381a0440b614000d81c428200182d001c1e0004014081d40c00380200a0203001c0c4101090700380d60304a210346d01001a5002200081c050406c01035810780c82c2c0207110181100a1a20b0720b103500d8602116208040c4078880101083d0001c0441c05240080480c098140c5020300100303061007050040300d00030f650b00140d07040440d40b40d20120403607210000301c08100961549844d000b07442d038408103072a000c0d8002c2046031017404c10180442c003c1d00004415000380424100c0b40e5850a0002c4001e2003818004c4040813007179510601070026512100549090318802140581c07103004d1401c10302e014007400c60015180c011089806d40f501505078200c1380040c0c00110489400c3d460312202110202030a14018109400992282550038418403900641c480c503881100d00300409501d82d003003264040260302041040006045110b1459646407000a001d0704108000d990b1424890300c003089010342c464401072219800c00040c041030481921b1041d12040c02c4070441e868285005880c2e6901900e490360300744 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770629847 1250 770628597 770628601
    0x120510050108090a0c03120309050708030301060906030204050907030e070e0c0301050a06110d0e040908040906090e0f03070b06062a0f010207021f0912030f030507052506021b0105040506 82
    0x340000341995406a2141c1c1d00c1780c042d89152181e01c0d070001300400c540105602ca80041d07010034410440c1002800080010b0741c0d99526056010745002095031004d020b141c01404204843c0d6218820a503103d000d905020884e206207074051814228107410040c07078240c40c9418000d04000ca0000385040e40d00035101134007507948445d415107584118510b84104c1c1c0d400250503803800c620513803481c614600c0140c00411100c02941e154049a0001e420054239140c5c0d6070000c0015480c07a0141003603070007482010f800c0c1c4145040c0d0b020b0312403103458409002d64140e18003180035507c0345012560040c4c2c03500b0401c03802115161400050701c0105d4820f10b064851101c071000144410302c03c03034081b160b008280d2a02e0b114070340444403910b03010b000c0c40001e01010171000a13082c242c1e40c0b810b094980c402d54820040600829014003102c1002c1c0c8403800300078082c421003400c180041000700da00c2c0c45100741040500071340c0c40c1c110041c0c81000c0c0e0801e98112301402c0e0810713810054014500440c03090055860b20b07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770631097 1250 770629847 770629861
    0x5122a01020a0f0813061a060414031501080d0f020705090c0c0715090e04020406030b070c0501060803120109021803030c0f150f181614030c0409030e010f120510050108 74
    0x200070245c40c05030300c08541805150009480d030744016107241440c1461003240c8425800101a0782140d480300314110301d0b42c80719a40d9440c06104040c1010002c0301074032555410604040d0b659108240004103000b07a16008400315402004418014003004001c0d07459864125910851a0801c480075200c51050f07a03004100780c0e400504800c41e4034002e80d507094005260599140d88460094800da8216a86d010003001145111482e148a21010b40320008850380300e14019086809503070020525400a20500890002c0c00e101c0c1d40c1102c0c40fa840140c2c0b5582d038840e02030b06018682d6550355152000088880e407801380401c0340c001290340d20041d0f030034541468000d107100c01c00454850145061010008031600d613001e958a91400c45502241c3c0345d40310301b54614101c0700c91604607241004c440140c082c0140b40c10048036003450f00c03c0e28148507d200d2940c001e401400d0030000c2a0602401e00140030a6038450400583e03109225002803109080008080b515060310340100750025250400052003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770632347 1250 770631097 770631107
    0x1104080f010b030d0e040b0904060203010e070801050112050703180b011406041d13200f01020123070c0b0c0405040c0c03021009170a0e010e0d05122a01020a0f 70
    0x42030001034082c0130b00d2007140710b040311105980c41e0144da2055451003500c0158036410f007041c0c07044d441507070010781d65410031001c4114903800404000030060b072140180030740d90b840130085035034501501011071207440303070102600500207843d0280c000c20f032007036910028070207400c03141412290714840020080f0412018000c0302d00c12802000c0b40e8581e1106030704890380c5c403500420b83c0030303002c03003102e541603203403540c5004000da4480031a1008420590f1494a1407900d10610010080240000c108142c07004180f000c0703180284440c940142d00110008110f80c1c051020f241e20241d018419143c0c034503109a540405030000d00541d402540f91511207100d4601031100c01c1c0c00b45401d90001c00c0c01401204a20014140c030f90405c0300d03003001c0300745d056007103505c0c1201400c1110300949900c0c8030001d2030400103014004990000c2e10903004502480302050010401c1140301c4c00e40700360b155603200001c0c0070b0150000c0c20f40040308100080b80300f0b05440a01940504060b1300300d0745d0b0301e08940703000e0402122 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770633597 1250 770632347 770632361
    0x3031c05060a2603090a08070302040605041e0b061e040311030706051806041205030702090705090a090b0d1e0b0c0319020a020f0304060f030b1206060d030903061104080f01 76
    0x40201e00107410124100743c440860340c0712501c84045034602040100031403024089035001c0e00c419480351409008505d000d015210280006507000c0104050409070004141d800300150300032290f0303801d0718445c00d4682c032044031194817a1410940d0101400e0b4031500660703202d44015a02e0030811b01882043e0320700450b0b0081240c442d5643e180c1440078200320a0156001480600e605ca4800c21001400104411090038403074012005107484003e0b070b005000c3e40043c02010b050400104002c42e0303560340d44000090080e0780c090364000030501c00e40304c08500607603040318018113000494040c0c0c2030a02d0a584018942d02e100391380c041329a0311442c142d00410700064860712101d6490301240c0d40c120344c056000e4241100a0720450340314001c00c00546080d540550451400603000f5003c550352680c140c0200141810240e90002d8103944825095031509005000b035440ba195007039646060512451500340595045a030402c4180c004109001d119440382c171914459014541803143c0142061103001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770634847 1250 770633597 770633609
    0xc0e0126070b0a200703240608030414040603140105040c0902030c030f061906180b0f070f15020c010903080604020a021b04140903210106021213030203031c05060a 72
    0x2d03061003075980d810794034501c009000201e801440b0070140ca070b5000402200e8000c6004580101a15240c0c6141824640400b0044181d140c20801c0400c0b40100000c12a4210341044402c00c0301c2d030034004000380241c421139002030916044407090300301004066004600551086045140303140c1e694010509a0008131102800305a0900001c0c0c03c11103007a8985600030b2008021200811010920601254454128030000360500501c00c1c10501015415405414004040350a00c50101480c502a1140800081001c0c0184e80f102081002d1010715541d42c40d0056000c1d0340395410031a04600a12120f4415000a100071b00440c52604152003101e0540d1348a074041c1c100301f44a07604100014080981094000b542d45804500e00411040031500446000c4050b594420031400b40d4003d40000302050350f000a10240100304aa40004c1c21030214441d001c14a44c03105281180c1281492603603101035098000051004100001e51442d0b04020f4031440781009507403140710602007941d035940070344 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770636097 1250 770634847 770634869
    0x8330102240a0504060e06040f0308012909060f0406020c0406050a120f08190c1a0c03070c0309050d05060a15060e0f03100c020307030f080f0604090c0e012607 70
    0x1184290350b00b5042594041e000f41030106c0c25880140102c0d2400f00129416203101c40c0c400648420503a20010f0701e8018032445500c0d20012f0b101c102c4110940d9480390414550060010780030a10361910310545d40c40b001400700e0507442d299a001e0107901c80210750030442c4940d2500101007058540040800d055942001c4200340045060350740344040700010300251002c4a0502c100d241005400014030610b9000e9519a460a040317031900c491400289120401c041040c5000c000072180f10780103586d0b019603e03140000e06c007115070800383c52910709500650f4202000751030301000c1c4540051044c0c010281c000f030030401007149142c1c00345900154000c0a0002e1190415480342c3c0c80c21900400c1481001001d0f0303078078140d07450003030300443d00720204000146e0004070b440f0307041c141c019660710144450344c2002d0595140c5900c44141c60708006151520684e5910740e07050501003c089444003905c04860b001300380e961130b2042d621800c00006110812040341c02d80c48418190040784010449140d6040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770637347 1250 770636097 770636101
    0x60f13081615020d1e030603060e0c0306010b03070e0d151a0913051b150d090515040b04030c0311010e0f010b0105090603072007330f0833010224 64
    0x40c9405c21640c1c01d80c080603103c0170f02101040851040450039049280101101c101d80401c0c0341c1030070416030040d4410003080c41045070319904052182000c10045880920b408103501d072204502942111402000d45048802101505075a541d4040c08408888500c46a50360503c1406056001c84005102c1c0c1c11aa15051510208000300240b14000510582c1c8010800e00151071940002c000d0084958076a0340074018040140000f003910301c100190150289030a49543c082c803440644018100070540c540384003818401c443e42c07041403d64000030300c28000581c1d601c079a6803186007035142c425480c00303840250315030145c4110781d1400c0010309890b096a60342402544c00420200c80c4100100e40c2020032819100180700b0140989060034440152031904000219a0040d44001c43c0c83e0300250030a0600c21500071004814141c0750313280c900c0448c3d83c0d5081440111218031000583e168410b03202c0c101980d840303924002080e0081c0e0031541800111010000010b03000c1d20805071a03080e43c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770638597 1250 770637347 770637377
    0x5010509101a010207060815040f090c0506040e06010806150703030506010906030e060c070807050a15050a060b0d0e010b0409050303011e150f020111030103150c03020306060f13081615020d 83
    0x401d80d23200613072401b01001810407001007010b40355881c050541e0550b46428420421101c405000b000d042c1c00d03a0614241400c001001e90b4a94003c3d240f1418800c982d800030301a90784590302150154099200140c4558880c5005000b41405a035100d01080c00c506012030340303c2c030a10079000c040b0251001464240c40b40300c1e400c1915403001405507112002002141d001c9142008042c5c2d07282c1c4600041d081c4800801144000c96001074400244a800d000e82089204030b141c0958105a0b16224005800315038440c8260041c0650301c1c0d0142c0007400c0008100500002002450403581c0c0c003a5801c000d0f095070f0760040a400d0080c000c1c039440b0305002e110b80e01c00621429000d01040950300002800310000c240c3c1c205a90004d900c102c1d0810031000d0803031092901750180020000d00c45c141903041d820000000360460058018900c011030b0301103485130490403080d041a0041c403901c2d007501e01c40c0d00d41e0100001201d01074001d0b075090111042981002030b10000c1c035403070b1004082d41d0f0b840c01100010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770639847 1250 770638597 770638607
    0x10c0f09090e2b030f0c08160c240f150b03180102031023010212210406291c0813180e010204030f0f020a0305010509101a01020706 58
    0x782800c01c2d103120340310580d0038440d040c02c03150350060a1940740003c10350304800b0040c2529820b08494207250f08020061504a4010034569006184080001c07031095103a18100c48448140c24050607941c8881c40c1ca2030046180400c1c0c4511014034441404504500395040e4191003460b215580c80b4041c0c000c04000380c0141c50050341e0440104080c94001c440410661404e980041d209009030814000c0c00b002024070465290b070900c00d8181c0c070b001a034095440044d445240704005c2003c218000110135029041909844010070300082042d4400d02f841e00b00304005080040350800c841001c40762080c419491413103240758990006003181245000410728850304c0b91f2141c42121808001c0c02220040298104c0702000b030001d0004603860b040405124200f541d4030022192030591040005002007152407107651807507504803121000c100080e2011800e9000d5540c800341c0b06506c1d01c024041d20b0352020641c0d07007000541c0c50701800986041d141102403081000100c5016910000003000054099 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 770641097 1250 770639847 770639861
    0x150903070920070f08132d0902160c14090c0c0c01050f0405180a05010b0a12090302120a031a011115100b0f2110030b0a0f09050d02010c0f0909 63
    0x16206140c50304c041030b5140841a0008101c1e04104042050203210244a02c107100d00c1c03c20317a560842115010140ea0041c600b80d2901801244d140c0008441988610011441c03d0560744084019440c0355a01c02c1da56590352900d800520408141d00825610751690042d204040040c00140c00007071220401502e0b0743c1e100d0401400004014080090150340c1c032807031749102004401d040c900b1858030200c0300044410507008016104000e00c1010090f036030145211000c40205980000c904441e400c040c0d2411500071103d2000d1500010082203065240d00009142001c240c1109030951042c070064450b08098901d03100103900003901200e1002d4140780c016004002c03110080c214039141c849910290340301c241030810804002484562030392400c0801c40da2030b00d190081c81034a06000101c003201541b41c0c070015140c2141c0e2004281d004040b580220b05a000481c0e0810050005260440e1140c404403004400342d40b809800c0300301030740111032a81c840c036900e40e5140202802c000c1403000600f01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 770642347 1250 770641097 770641103
    0x503060a0302090702010203070809030c0a030c0831050a0b1213050f01020a0810030b0c07030201020c0a03090503010c03050402060306150903102a0503070509040b15090307092007 79
    0x40c80e800201688803c0400781c0540c3c00b5a0015907a8600000060070048001c1d001d04940e078010810841124408948414001d91501d00704522090a0030000d07203500403030030016994840300c406c3c9402142e031040d12825040b03600518526540c1c1c2c80d820428811080d01c01c240b5a100d0410484042c128102140c45c0c0c4000b07440715113002c008043c1c03181440d00280510600c0f0030781d030000e0002c00540d00704401c00d80c0400203085102c030740e500319582c00c0c050360300c05041c0840125003c190001014000c1d016158030001120443d0b02e010100d08005041480c28401c0c2030081d440c00c036446200d14468080d05108a030083d01191542d01d6000a03c40e0400c4e0005119000d2001405814400d64052120030802268420f0118084140300360007080c20000c0521643c888075808081c40303550360402c007070300e5200541d030030500d4640b1581008140904128180c03140e100c050f58400700c004814490140030401019000c5804481e207401804045a162042d49980480b4842e40c2c0c94458007580024240c1c00c0c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 770643597 1250 770642347 770642359
    0x80d0f050c060129091e270103021201020306030a03050a231201060f0c02060a0e0306100305160f090e0c0a0e01141e122d010608011b050306 62
    0x29440101da8100b41007030708079440c1080030300b840b0049590904041c0090a081400c1030b40f40011402c002514482d40215000034000c0c1c090342018241d54914003074043c4030082074400c00e00c0540128614046100340030403449401640c03a03000f4070240c14030036031380304400280c000d002c481d1490310207607529001156200c003044580301d5205480d000110b600c140d06d484039105c140c4c4607904620307810003202050300302c0350030088103040b0301c2503065001200500440e01038440a95860148208a5811851507100c580620800f4180003942840320052002c60340510b095400c00201080c0042c1d246405104850306810039400130300c5110020b42c04244448030200442d600d400f81100410822030003540f0044426010a00411141901c208034003400f4000321103810300c60270394007040c0030828001400d99000d102c501c1c0891030381610800402d407000d200d1391144c0e40790000c024804c0a0490510103500595400c100001074140b005009003071b000250021031094050103408100c40c9604020841c5a00c51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 770644847 1250 770643597 770643607
    0x311010e190611151902070c030c26070b1b010608011b02010606020c090a050709030204050a0606090f0b0418020f040b070b06090c030a0f020705100b0a090204080d0f05 74
    0x168101000700425040d191a40380241840880d400d1218000000781825100010004c4501c81406140d0ba45881950010303214503090a0049a04071160070090020040a1011810801300026565107541381c40d00c844c3e0a0302c1c10b01c10241c40e08154402d014502c8001e200c80080d194000040740c18110f40d031000040c905030785001d51800e460700c0540361401c12054611030f1030180c0c0e0a0246001030802400200480034507240840c4070100000c1400300d0081e03650001c0342016200d80b240707a00031a0018028481400c1c54050342c0003c044d944100340100d1095940011001131800107041282d603200b00b41c45c10a40340c90100301da4400740825001202d41c1c00c0151405100c44c40b00600003810b9607405058a5a04074a40681b0a04000d41418450203458003003250782c84400045a600c4a1070440100c1c404642c05800c1c006809050801007560041000700109003d1035481006818400c0310203814441d550035070202240700f00d00440700190000c0040342c4a00b030054000c25007500381031822078500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 770646097 1250 770644847 770644879
    0xf090f03050a08090d05041202030a200f010c050604030507050a0f0506040b090c0a092f091c03080708070c140609010b0613050d030507050f0106050306100311010e 72
    0x101110a011004a08007081000025500c03200c11540181ea400082590660400d0090f101340914414615113682500c074010454809000100d0010346c0010103904940c29494100d41301c41d054251540038034201e41c41c00b02e0a6200e100c10034140ca420401426041e1281d4400310390980c0040415500c501c1903140010005003501010051035000704041c1c4220300349490b014086903009001c3c001e056202100304c0c4083c1ea5005903083c200c0d02c1d444d2000404480403050040e2000c3c0c5214040c98140b0240c0018407002e40180052203049800c50b51502c1d104c80802c0720001c2d0011040d00540050503400001e20a0307402012a0342d002085424000307100907841c1e86044001381441d0303032944260000c03418082c039004240642140154111004c0c0e040c01c20840600490901034450140b00d03d1b801050441418090000c4481007030300302c000d0310600d51075403081d240600010300c156400307840750000041480c0a050341103001d50750f00039662000044600d004407040221400490380c0030016441c20404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 770647347 1250 770646097 770646113
    0x3020913210c020f0d05031b0106050301020a020f0601090c05040909020a2102100e03100f020f0f0408060601090b040e0403110105071808240403140706020418110d0f09 74
    0x1d501196550b05480036030b88103008500c401e940a883c05480d407101d44800003000441603c030460f101c038151030240c0c14415499405000140e0105401d944001824404154080340312172841c2c4801e0f084558a980e1040c0c40c00480b0713120310070800011801e006c00d20640070342c0d810210099000424080711241c55004004000c540c3d40c4c1c00ca01185a01c1c0c13801401c42c18030a03e28800d1a4650500040940b80000800c0d1541150a080030038107940703a11000000d496039042c1d03501c5003000e00c5201d07200d000c0d030043c0500c01e5000e070250f00104c0c8a160b00040840d803081514005546001411505140c5030011040321154082d01c11030500c00c50468560711100709101d09485510f440d500d01c21000c003118081c1c40e100d0401d40142445400c0002c41403c00c4030b16020303010896018030b54074151070340c40e0304003280d9160111480046031400010389030244800764024200350345008400c06d0100d00300700f02100481e03428949000700e00c0000c0c04a0801c495040e4802042c1518115000c1488000c0380d4a000c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 770648597 1250 770647347 770647403
    0xf0501050a0203120a1d0c01080c09190308130b090102030702130b04090b06180606120405030d091101080702010207200a0b0f0301060e060a020c061b101d030403020913 74
    0x3a00035070300c0f207601c003203c2d086240c3c1c14013106c3c1104c040d0010405040000348007000c001e140720420140042c51000030307152590424220b045480f501c12019403240782c01040c543c080340d01c1c0d01d80007503280004100402c840c02100c00c0c0d1013058000714a40585642402411107041540c51a0395541e0b1640da4880e44803400340c01115885410036090740d240c540100300601990300d00c13002ca144416400c1000989458013102e5100c0c42c0f080a0307034215619480c0c6540b56206440301c00320803504081d5840104501101320460404098072850741a9480316412404c0340504140581080e07503c00c0109200c4004401103201401c0c054242c5040540340c800b032981070b80c810f685c848d08540000004020031030b4050b1400d40c082a080300c0c0180b0f040c1d880c800003513941221000f444d118243c0016504400440f2690341b81c089401c5500f40d601c0c4c041030060080c000d140103048402c020345d01648802c5904800300480d400d5a40c000d1445020f80c07103001010940780c6110308200c5d1201c040900d038580d1040c8012910b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 770649847 1250 770648597 770648611
    0x1090f0b04020c160b070b010306090507210507063e070b070203010b010804121b0606030b06010e0a06051b0106090504050a0c09061511070f1d0f010f0501050a020312 73
    0x1304111550004a0042103941c4000e005181c14429880050808503030981180d400c01c4010a901e0350300d0030420b003400c4030742d88a8000001a040001c43e440d07401015044030b94019420344800d640e072414242e5420340e045111100c6940444070006400410442d80c0a02e00c040184001d20b042c400e4070060f16108050b0401c00c280000441c4990031413400740544000388000f86000b01d524202665100c40300000000843d046c8034012003014440750040490306d4089410070824040700344d030f13030030035400d02602500d400b4000740c0d461654080500b09404070100702c43e00c07640c0703641c60b000180e01d260202d070391b11022011140d52a4900003e00941a00807240590b0146018004040103403502d0003605921b41c3c030144255080910070044002c10081b2141d01500318180b1149200004902c103052580c42e4106c1c50b8a00c800880219501e41c4402140781420104603c040854864800300140744000748030f0901403c0404a01307104551007100600030f4020030380122814030001020f80b0145003021034000f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 770651097 1250 770649847 770649853
    0x14060c070b010909210e040207141e03091009050603010906080f0f030a1409091501020d05030f1b0c06070f0f050a120b130501090e070e010e01090f0b04020c 69
    0x1401d011407066128010100040c040150801075a81c0405030000300450403d045041c44007086000d0090394041c0e540c007802401150307500c03002e281c80c400c0e425181071500094801c0c003040c2c105440301d2404e004160b540c820021800e106000c41001a8035850003501010000802c100149548509002d140642110800807820605028091b4078203061b6094041103980035680e0303020708040c080200d4206080d1817034000001c10b040c0100010b54410391407031039000304910b420040f030400c000b40108000c050036400d82c0d0035156400c100300e440703000958241658444d0100824644071100124898003485050400c0c1400d903181d40b02070405500f02e03083c80100e0b9080d146040007a0780f04100d4004c400306828060300300855110001d0002500744491204281c1c1c0d0900100b690399400c030f04800c0e89804081c140032a41c0c50b0026400030341150001141c440c810b125000c5038030340c41c944100d41079610f940c0301e6007801e03881d043e12800580b44c03c440c00700110382d0725040d1910703d48890008184107c000401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 770652347 1250 770651097 770651107
    0x7081b09040e01020f0d0b0612011404060b07060506011d03070506090d1a1501090e0a09030504380408150c0706140709090c02100e0309093c0402040914060c 69
    0x4260107640c0c07150512231040804002140305007280b501303d10f0554100d10b4031031164032100c00109008002980021902000109100c0d007001407940049102e007000381d9a040008405032510301410071028502c0d54540c114100a1041e41040c2000d001c4800005040190014164a6a80449400406244508094400300450100c0c42008211499800c0c600703086014a8024030b0601400044d1100340310307030307110f4850805161064081d680605080080000001040361004200914428001d60145c11001c1080e0041209005841c1150300803000792491501c0300d80e910040c0b210052a0805003070b420b01c40d48000c03030311903c90403485a14841c4c40b04000c0c10002d070082c0120031182d103d00c460604103510711003c69808501c40908910140c80850300c807800d4004a0b00f503016003004d1b140c104014500300000001c5040c0860002500456400811031040b042d4000002c1d42e00c15203021007030a900031a0041c00d00354000070199000f820b95000d07a880c0d4425003410840150303004070959030082a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 770653597 1250 770652347 770652367
    0x333030b07020a0c03030c0201141b061b0f0a0309081603110721140609010203190c0f111603061b02011802091b03071707081b09040e01020f 62
    0xc52980250103800100515241079580d00c0a00095000040821001156100841e4004c44c000001560400e40007078440c45142081941c1000384a0b04040c80d105090200305141c5101111000504400c0566481e01441c441b8020742c070761010041c50101691140000c010071031090140400111480b140c00b03440205042c01812500002c0006820346c02c014400c1008d20105c0c0c01c0200344040400040441c0312040c00c00114404034040c81800601410041102e0420103500461041c10b09440402d040e000305098881142c9071110200b01007400020842d05690103000c4204410403071038110340442e40b03080c0840340c1c80e10803680119000e540b914141c680d41c40940d10040c078010b600780300030010300340a0691014a0385000e400039024980c0d013004a032890100050800980c080c0100d00380c5d0780e00382003a0040007407002c04003a100360800c1c10080b6802c40e1060f4030141c0140c000c00c150b544000d5940c4480155a40130188031076102d56907142003000394000380080c152000c00c03550410746a039505c2e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 770654847 1250 770653597 770653613
    0x203071d0a05010e01140309010c02070611100f0b0d0302060402011103120103060b06040e041b0b04050d1401150314100203060d0f0501090b04060207110103050705040303033303 78
    0x15400c060344031600c40d1280c0c0c558a09180881da000d28102079000c02000068468a1701c2080894802c5000810007901e044150882c14000d0001d13070803a411641d842e4803c403000d11484990b040307582c00444003403080500e141c100c0303181103a102c0e20028080c0303070203c00540c001070500411000768002204110642da08404070b468010366010285103800521650003200c5001400010951552030106200a840e00c1003a0703409400a03888088941c00c05083c081000d007000070a041c80103601070b0300402d130741c810202034030105c03000600b10a042001c40e0755416048500c1d14a8940159622401000000004810742c0010f5010381300c031a020507001098142041c140c5040f190340180100140304083d285c40130768404480d00408401d040700000e2810328090b14a002c2d01401c1001100144001c0c02a01e90060040c2889000c1038190106140015400c1e103a0407034022010031420b000030008203010b03411101e041010b42c520001e03500705000c0401e80c1c00d10a00c4444030080c0662000717100b0080d581c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 770656097 1250 770654847 770654867
    0xd032a02010b100f050a05031009060b040905150915041b050c01150503153408060108060a12030908010c0908070806150d080d05040305190503040f08220801020307 72
    0x80d2801c0004c803003071501c1c0074200740304d0405180d0800c1000070010318001070b450060740c05048060424000d260351350080402a401c54040c5012003440c06000ca981d105100c1011000c3c1130026141001035a5400f031a08400c07007540340c800741c22a0b1640f4604054014111a089003208580c0302c245d141d07120071000354211412086005181034441a080c4460703078001461650b0201050000d04c0d950f5507920501c1403495405002200310040d4900380c0920744101c04880c84141d6156030344034020380c3e52000441e0040000d4801c1c0da04040401400c1c040745611500100b20b9030300074100740f0034040c0e88010203401c5949da584000c0008000c2e51003405403000910852000300707003180c01030850b421700700811a0040d07120a9114490f606406480c002c02004101b601d00d249a105800c0080c0d142c20f00340504150302c030040c00c1c1c4480a1031032812116a000f4415a0700407604440c1e403900110305683d401a00e588020958000080ca141c030009005c50081000c00203065000009030702d07030070036100c082c00300212 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 770657347 1250 770656097 770656129
    0x807020a0c06090620190213050403020604030305130c0311191206240b2b060911040b030408031e010305030711090606070b1519080708010e0d032a02010b 68
    0x4080040141e40308006040f6090504146031891b0840306880020781300d04410309007089142c01c0404100901d030f0007150540c482d90094800b07104660b2007010700c1000303022041004181b030322009130910224110500018020b1809002d110080b03c54001c40400781c031445d03101307411381900082c0500801419024025801072500d0401c5040c1c030648a054010200038007502039034007030114042510492804460008102e00c1c0c0c0f400c54a410302445040c0a403645020342d80340303d03080100445480380010211400c452051142ca421620b03a85e860f02711961028100040e150031882030391000d885800c101c140214468001156900b1051500340711000c010082c81e840fa44002c02001041c0c0c98450498400c10b610200b26038440ea030704da811100c0540103c4915070484500d821282d807c2140d9180305003514040c2d0100d40d1b01e107651f0182c840c01d03503108141d01c2c40c95400100d005142140a50407912038041c3d46400030000341140c540c120050103800c00c01e0f000503034480c0850070381d03400e05444030340c1d10703445c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 770658597 1250 770657347 770657387
    0x90f060e0a170a022b030b060f040501050c0a05010e2b0905040509210405040b031b1311070804030204051f180b06070501060608250807020a0c060906 66
    0x101c1074888000180424038980902c00b400038030341800701d10902060300403e0101903c52210505142080450304294240c400801c0c54030300040303160306e03100041d41d00385454005407610340f03400c041c01143c450b0401c020041003072060032120b500058080c090410307455840e01c020000051200d4120007001d552000a00500c040002e0300e4840583c0f01d5849015500203640c04502610b4503401e5524089414824480d60960381d032641c07100d45070400051085030001c46080c010f015122003019201e0a07607220700d64126403a03686100d030300d042110360a411001c02e68070000f0351400c072109400d1280c1c0124421100080002800e1007185424801e403034000308403001c504244c00d00313441c200d50044140d0144c2d041e039188001c85403038140c603260000140f1080c040e00a64a0310a14940980601000d0060a020501c9100000c88195050301d00c0030710142c881042504040800c8070a40751510b02404501c1140034094100000c40c040c00134620003841550380e01c28a00380b0300480207005001281c15540c0300702e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 770659847 1250 770658597 770658613
    0x1902070305070206090d050a030225050f0d05030f040e19090218150607060204170307030518010905062206030207020123070c061e030204030b0a11090301090f060e 72
    0x3039100068a4205505075130540d518500c02000401d01082e405000b442d500c5802d03805010103901041c1c1c40c40d40141a810642c5090f00c01403441c502105900030190000000601030402d480c210f00032a50a9000b01c059900d0080444911a811352042e0840783c034507048031052082140071035280c1d15042c101110304001d18503450b40000c880c0b29564a560a5584400c4081107620340e885405006a6400030034140c1d4510301c0d4941200a50014031a8400c0c82c414101003480e10300000c07088615907075041c4d42c0c09181407400d0301100d8901d14042000c50401c241c5c0764002c03c1640710360b00106503440307001e43d035107000341c143c0700c1002c8064040760000010140188242401030741c20009544c1c1050120080f409090100c2100d074007175008100c2e0150104602c807600040c22078111152845801241d483d10081c020681e0054050344114070006041c0b600f207200081031421298490742c21f081495901915181c16900000c0c00d50f111200242c80d580500c000000812a0b28451094507081c00c6003d09a60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 770661097 1250 770659847 770659853
    0x30c010f0203030f04050f1005100839040c031b050921010f05040807110f06030103030503070e04020a0e0102010f15030f24140f10090b04110c0303190207 68
    0x3901002d085403000c2c0c43c4c100d012400300715092155100c0c00b0990011200c6c4240d24402d450054902135481600c0e03c20040800b080451004c41c94031250740c45004092481889684229405054869070179111070310300b050105180d0712400703503c0581100303507000301e03444145a5681e080f403d01001b0046c01d012003000380c1021922000c81520300090000e104030849401d034200c0d1409006071801d02c0d49454034103800c0000f0401070902900900e401400d000c903c003c8898180045401032544e0305510000500c010000644140001c1d50302403a503250421003c068400428240d80004410300085940300c3c900712900d59091041141d0501402c174184400d22100742106c1d200780f100c0c00060302d40f1034195944814010703040150740c40e4000c805c005100704441e034a107210081414420380c0c410700c0f1792400424a2807201d0800207000f00e040c6902c0345031441c6402002e800a0900e00103164100c2c0d00c41b10030b10144d0340640003410300000c07002c010f50703685d00e40031012000000321071100c00b81d580d01c1404a0008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 770662347 1250 770661097 770661103
    0x20f010605090a20030f010810020a0e0d02030f1c030c02160501030c1701090510080a0308060418020d14060c0f04031e050d0906030b030705010c080702180a0902030c010f02 76
    0x10403030f00ca40000b003c0500030602e4400b0896a420008007410000610000034a01440a4100c40c0e0540c1a14140303d03070815400306922032298900005205009040d070140340c88010006a0780c8010704550201040751011030415255404403800342c0c00d0500740c2c102a54040c0501c000881151000d4070742d440d90295400035206060081c9410503035215481c28500d1300842104400d000501d55001302580c5d40c0a0080140030101d46281d5142c1e08064001001c5100158110804d58552102d000c02c0c4e849600340310040c4107800c0303082408510807180901503150560341190040c06403101d292003e850341c40395890040c01409010b50090108109a41c0c6c1400310113850640c0e91045246003054100c3c44140c00c0c024007410042c00c1c42c00f0b04d000d111001500202800d0469809850a02c004440c0008141c0c4404042c030030640400c220000034000505184014007920388000c00d01e40180e50111451100410200d407e0450907940d40c01c0d078815880d0070851050307040002d19000580c00004040252 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 770663597 1250 770662347 770662351
    0x1b0d0f080a0b0a170c09130201030b0d0221390d0201080a020a020304050604060507020915030c01080612150f01121205031017030703120605011407030504050d08070201020f01060509 80
    0x8030800a0415500c1c0321030b045c00f40c5114448000c1c008036040c01c01a50207444400d807488200c3c0405d19000c18100182050312140c81c0f1503030000c1c9440400390914a01c11294207200b10140014060022006e101420170701ca0000c98102015084a081207820458581c1ea240360183c00c1c0729850034503060740140c3e0321044030755100010703220151b00c844035610160700d0343c0101d411036640140086800300d02035a00c40050b01c8a1402250b5035185c980354034030500c804035445140c40b6096001060350010310750080740700c1070304540c0241c14107603402d0b051001c0e5402d11992110004551951906221a81d80340c2018540035260070481c0c40302e1206503503182036001e00d503058000180440800003840ea01084200c0000800e2410004502d401411003070640302e074000c000c11800301d103d1041c012258649445003005888040e118060070001100c858401504030950482c1000000c00c4081204e441d121401860644956100303626214584000b80c00e0684030710311081280e242a0b01000365a0b076142c0155 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 770664847 1250 770663597 770663609
    0x30606030304081c0905060d0e063d09050109020318060606070b06120709020417030c0c010c021c0501090308061c080c010e030c1b01080405030d021b0d0f080a0b0a 72
    0x1000c2c0c40384e21034183e0f1160851350105a10010115405038620855002300d402c0044120035900b45690b100022003104a0402c6800c03415402c019502c40c0c0d42c40781031081c1100031198121101155502c4031081c06560003600302240c0c40350040705020107000c0e0280071030110500b80001e00035514020b40880c1c014050f125018048a500001141880e01c1d0b140307001c0b8043c02c5000c1075458a07a00d407800341010317500901c20010342c0d844525480450000200644c0d40c1076007208040d110400d4600011030b41ca041d40201a640070540340402000c4005440a40300c43e140300f240003240b80309650a0140c41200c005100c0b074000c0c011501c3c410010038055a101516a901071451078031003882d0f0141e18010310440d82e5041c2144000244008012400100021443d01703150b1000044002c05004603450303c01130380d0090880c0d03c2808080303080c8050307030050030204410340c611904035040c4503901da28100d5140054004500140300401e4140e6014082540c4045686002e000003ca0000400c10100d0f40703120305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 770666097 1250 770664847 770664883
    0x3051e0703151109040c020c01020c0a030201050415030213080c090a0207051c0324050a06020f07380307080a051512010b0925180b0a0c1704030203060603030408 71
    0x40d8801401c0c42a203030203080c003038403c000100b13600074084c1da48c589540f0800d02600c22850748042c80d01e000300804051300d90694a00b814249070086000310310b0945082ca505158090268840e184800d04544005200703d03002040b100c02c039030040c0218006c0140601d10300600400110021400c0080da0091080c441c45002584121100d0b0031401007400244122a0f011406400070300d200400d41c858055a104645420085c0c0c4c0e5000c0c260ba640f28a01d2921001e600b26000800c040d2002e0440d13600329114846c041710381d10205440c511510b4104e100c0440d20b800d0007000380a0144c1c1e000416981c080d081e40b504000c1b608009420f802d148400700c00451003010990b40c8050318010070341060f00c1c515000f819806403801d01c0d5028907422004280c2d034038248440c9030700030b1100503c100700c04444120410444141325050400d8082d071031b84104000d1b01400080400f501c0018a590480040d0038400315089480f181944101420100301500c078510940c4184420b000d0f80703002040c41d0441461080c18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 770667347 1250 770666097 770666111
    0x10f0b0a0c050a06110c01231305031c052202010e0f010311040b1b01090314090301021308160f03020f09040219080c1c030c0308180703051e070315 65
    0x2d40f510411040061115040c0b40150f071502e88194042e06414900c0e030300a00203003e031010504001039040c0b066a241c68603140101e0a04142c400d4081c0b071890151781500d1500c0360300d03040031aa00c07050070408001955104100171210340180b0880e0040064010000c0c0c00030045d4000a10440000440a206040307000401c002e5038001d6212031400b1906840894803156030755a0700f142c90300480034040034110305007004e039400d61044c0724004a10341c0c50380700d94100312074001040d40e01380c02070360500c1c2d0159804c00646001d5a85032903644000d14684000b0400c018030040d660811a0080d8040240464544420320043c1d407680b0b80d02602c4441620401d005540350b000055818030b00e00e0307209648400124001ca420341c00403510319501c1e00191060314812035802035035441c0b412000d0001d4002001564404000781c814142290844901800140100141a03a25090020f2607000301ca081e8014041d108040140c80031064070030000201503e0302a1464136510100d009400044c2411a40c07004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 770668597 1250 770667347 770667353
    0x3120509031c0c020312220f141507050a02030f28030201090f060624021b270f010e060108010b090102012003060406050616020d05070803070b010e010f0b0a0c 70
    0xf0b05101c203d03002021244a207505540c0c200341d5034404a5114145a4042400c90003041c2190601b0200c81c4091031340c281441c0f42c11025925680400442079206070941c9a100c07241c4485405040a58010009003a070468588109840c0c00500e8040b007083d500180220004641000340c40440d60600200c890103150341da282c1203005018100c002408203860400c100180501c90780b0180940e1003108100224405107110418400000940040168810414650802c014484444a6031000750580a803002a00c40e080714800241e01c4000640b0500400c11200444101071a80103241650001d446400c0c00300000308400d20500179821700700e8001400241d641d1003540507188403802c02182030210080b003074400074903a100381c032518425410407101103603910344801280e41c003110301c001c15540044c031542840942e038185201603e560158401c0040c51603070602c0100112807107000707400312640c14018019003404041e0055007102c0725000c000d10004030544100c1e00c28450600301055152814130f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 770669847 1250 770668597 770668607
    0x8090a020a08030d060f0e0a090c0e010611010f09050d0c14120301030302010f0506090a0905010204030209040503250c1a0904060906140312070b0c0403080a02060103120509031c 78
    0x11800035041074600c5400038094002001414034401c008805000c6140c2d58a001b40c600c50a40c01b8009a5a558102082e88043d5030342c04442240d12070036403248020380e9441032101c0e00c3d40136131000300030074403441030015084820f11454080c52180706041104200f9522010303540d045034042c2006100180f03000b0345c01d000a0000a0f140340c141d18003264170f009100c1603d8031032074100f0b01c011800340d82020140ea210325030901845110780006080c108070ba41d1210342c01c8000d045607490030764095500300804005611101c689510035400352000790f9903039440480000d0b00004c544040c1890007100161200024a4829075a0885403401c885400e0004040c4907807a181c071a481d1480d42c49841e0a200103a0241d10380c1042c3d080b10a43e4250030310404008041c15140c00d14031030703144020b000c10004400004e00001c2e495410418101045040c0768881d501c0070300c141d20400d110030160384454010420444140051400c04029140c10b904081d1a50080b07039903000c00039a41c2120541049214510522030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 770671097 1250 770669847 770669863
    0x1b13021204060c02030d151a18060f0c06040c170610050d0c120f02090108010b061b030c06070518040908181215190905190c0513020d27030809 63
    0x160604007d400e9400c0c0898800e0310082c4141241103810314150340004405006840020010483c00707041c400c40e503406c12100e98040302e551b081c50740c3c041c040420104420004148514820100c03182441d0901c07200183c6901410300b4594076900000410500c8241010a1700c102c4078155010200385502c1c1c0f500400d50740302d98110b5240c6c0022011020309006000380401707409802520801102d0f41c0b82c002007401e880c000003545070004000c01c9443e28040560640300d1980d0110340540b82006007541003070742000350565000c40058004a146d000c1c20302c0d05100303030018010032101002030340c0c43e82e41c81014034014040c0310341d00000c2807034507403185440784401e0b08045c030a00070540714459030100351401500801d80c0c0c8400743d400b032000d4061000c0396070f03c50781503803e410000034000f00329117100f1014400790030741003203a82040740d0030700007016100c00305c48101c02246c009002d40c0f1410486083d40c21038186035a0881d200400017a1500c544000e2045240442e403d40781070003003035566151003407a003102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 770672347 1250 770671097 770671117
    0xf0a0f12030f050702010b040c0305090c06031009020f1c02030f041b03050706023003061e0d060b01020d0207031104020d0216081b0c010f201b13021204060c0203 71
    0x822013008843c2d541940855002c1404a504002d51503c800d0214102c5000310386107259944450f8280140b03180c100091a072000c29090229440d64581213501c081c0d0304a2000050003040c0880c203501c1400c0c0c3c54005000c0e00c141d107401141145002c00c0c1e589081580540050801d08002103134120300c01d84170003200040c0d074211b0201c502c101e6a43c034000799038001c4403c0007032a08142030055041004030980b4500e440c5503203040b05086480c0c0f01c0c10800d8101204842180140102480d505162545503c6614850142c5000111307115404c00281c18040c0121644d000c5402c50716082c4001104420615030a00c0c0030356006884400e0500200001d00c40e40304a18140e00b9503071096410000801d0041c440421002d600d07403158003c000c0d00d00e594610789601e0a012070312240c00b41500512441da400c98640d00179001101c1000c0c9204070900302071011a00e0403002c5008507400c2c00608108140350000c50400070110f2814111ba007203052440c1001d0401000b00381c8840050620320300c20000d403819146 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 770673597 1250 770672347 770672351
    0x5071a09010b09150a120f08160c180e0129010e090c030610050c0c091e09070905010f03030212180901180b04050f040f02060408030406050c0f0a0f12030f 68
    0x80071000b4542e0810520f840d10f1180c0c1517000b010500c03120144009081c01d42c444402c00055019540c0d00303520350400e050030019008144c1105000c24003000b0082c00400072038907c0b54214103214801425a051004150802c1e03060407a040c064810304542c02225079a0325650080000b0601c004030740d14540001801d41c00200301e0140000807410000450060904607034840325541100410342c1d00d4010768411104a4000d1146040e95003440701007564070901000a1755450410040241e5254000340c0d84401c45601000e41401030622034440d15002d000c41800098503a85160740095503000694034840f8080c8003c55002c0c0804951003d0320840c2d000102140700940c0c5418203070301910790690455000f030703042258452003810103100303850044403c6900e251003a41c858485084c078207440802260001d10400c40020aa40280080c0c0701410807030341c1d0640c0c0c41c482c2c4141c1d240b03401d5041c0382030360003a0040c9d4280c6000030399060285d601980c0c0310a201201c1c0300d00100550092000100f0000c0d443c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 770674847 1250 770673597 770673601
    0x30e10050105040f060515030603070b0c010b1201060f1e0909210311030a0e070e0a0204030309081903140408120a120614040b06070c03030306031205071a09010b09 72
    0x200058110a040c0c0b07405850030010003078200c00d0b0b031094488034070506420080c55071070200d000740004004c40d400742c1302401f11418140d80f410561450740c4001a0b2103120b9550320201d01140ca08100c000c2100c40b1030b00002c0c0f112504003044520704031200d04c280211001d03051010300d605580c501d0020020441d40c142000b02c540d907420015481c203140c0b421035006d005040491006103009105202c1c045060600346402c654403281c2c100c0090200000c40381c01d9115200700014000c1c0142580c0388109804540541c07205d10b946006010b001468004207440c0d0420000c030368090a2a070050021031b601494546000240c48450082c40d1190742c000c5100c81c02142000b4031642608401008411800c0c0d8907210039190780303004074085445602440c0020f0f0040508d2089601c0c0c184c10600e903103c1c00409a900e480080d80d0b411050f00500d60044000c0b035180c1000b0414044028615910320f05030742801440c1030807d80d50390310300d030050103a102888488200800d5502e00254031408041c000a1700b0701c0c03454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 770676097 1250 770674847 770674873
    0x901030b12061317031303030b131a03010b120312060120010c090504051006050a020c131401061e080705090301091b0f0b0d2a09080105060603060916030e 68
    0x401c10300400d44a8010090713100f24030342406402c84c1d10400f6450000b620340201650120050b00050038815846a02440d00304c02600d07851140082508100c200311004414200c00e250035140d1940c9124401d10386901c010144280110840704075600112580c511941d8880c0180da0350021a0200080303260880121070b00600c056210740e9001c101516003a100701e90700c030100000d9441c222036aa00505030706004102250044019005c80ca4442c0103940410b480392011881400e02000840c0d640340d100d4181044058a030280d450140c1900c1c42c003414008949803603000e074070351b64440070b0080011090008051030703c9135080da004640d004000b030016001c030b402c20f444500c80444845819407400031001030010403540d519012108481802401c0c440030030046002003074001d4820b802e0125554825100782030060441c55103a0315500e07540314113800c1c01800c40c21620000c06035805070400704284030f8541e40340e000031a440012a511441c401464174002ca0240040a040d2015481107403424609 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 770677347 1250 770676097 770676121
    0xa0804020306220303090305190917070f030809012f060f060102070b0d110415030c05130b03040609020604170f0303010b0a27030c090e010606050901030b1206 70
    0x1140200c080b108551550020354625507000340e001c980341d0b41032080c00d00c0024080d41203107603058000c2c2400f901384050101d4103002590740c0b0034240000b400003007042c040b0050f404041c14100c0325000003001e080741003002855090b8182c0c00b0141108401003a1032849a119280c104d02a940b000c0c0300c00c104c680c005940c5500c41d00c42ca06c6100072030080310000b94081d0310008402c0d01c60b02e0140c0c01040c2003860720034030070110303808038900c1001c4a84400b00d02d040340301020300800c010302240d440b491400e070103280014200c2d04032103000c604201d0b04000038114a0485401d070000e407070348440c5040d500c2c0c80d140340000041c0641c04000f5040304010400140c030060040b250030b48002c0140940710340d0360704c15030780644904c000d02918035081c0007400202c9075a1302c107038031219101c54001c7c1007070b9600200e44803103807921758990302c101c80e50740b88246e060113a10898011402301e44213110080c001d80d030600801502500840c241681099540c100c800040d50300c0084c41c68407800c1c082c00350741445c1041924040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 770678597 1250 770677347 770677351
    0x2131e0b04090501033f030b030703050d09090603111005310605070c120804270c0302070c140609090a051f0e04023703121b1103030f0a08 61
    0x30242c0041c46c440c91300400c0c06061141c0c1100300c149140865034402400708140c0c884000c403404251396004000350301d8600f0000d48014601507001007188000900c0010040c9045400c00d0030071504100080000803103200356101d158504441c06542d4a0f11440111480c0c09941c130780c81e40507190b903048a124410100100c3e00d10b03c1811020a000c1a180c9005031260310820344001c058080d900301c100b1030014802e0440101d18401c60310716140690300e18141c1c0f85040700794010f140616580325400303018074151240182e1a040c604003542804c003152110200941d480c4128003651105040c01101d6135640c104035201c2c1c603002000415070782080000c803401031408961203400ca402140c0c9100c00c3d0b80340041840c2c111100f80d5591011a40c8030b42c2444118a680c1c07450a1001c5041420241903c00118105804410601000d014a031540c10680910440c02c0c44080034044201c22401d80e05d01e00402c22144540c00082d0a2000400b42001c01e14500c5a41d80c401c242d00004510407400c5175001030840c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 770679847 1250 770678597 770678603
    0x7111606031a0f060703020c1306080c0108070f08070909020f0c010c0c0b07031e021b0601090c0f2007060210060e130b04020d051e0f0102131e0b0409050103 69
    0x9a6000960b604000c1c0c1a899101540001c1c0b15100e12050f00d402e00061a40b6440782c0306503507403201594041068090047c2d12140c099440b000e046c04000c400b0030101c4038407042441c00305101e08140d0f034058104980f40f04040200b0010f840040e45460041d1302c410700800101c40110b69500011940c0f0501e074000320202065942024540e030a40307803099541100c80c94024038603501640781d00c0c0c0150010481200001c4c044003120440303000c03404052001d000041c00403450400798000740c800090522034141c0100c540300345444d08015410303038883c1004040b8581c0d402c04e2041d0b45000e20a0050843c5403c050302c4081c454401f001c6030b450750106406c1001002800140501911113107041c0e10709104645408080fa96800c4a01c0864098450305421a002600501640c3d0301a00c807603007011440c2c005802425103000c5100801c1c80308200500782c4898003402142443d01305a454826179a243c49060032140701d000c2003140540710500001c0007007505101007981d03540e0701c220185c05440709100c15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 770681097 1250 770679847 770679851
    0x60e01080f0f0d0203040e1302060708030a0506010c081e0c010c020730020d1e0819360801020408010b01090b0307081f080618012d02030711160603 65
    0x400b00c1e2010009000034401010707009181040d06000c81c00c000e1240040041c001c7d01c10314201040981c440e44000c10065000703001040d924508855110161000a000341d8104040d401c80f41012501c10000c5d00c581d00b80800e10850000e41c0c100c44488140079070000702800794039001c0b01490f5107400140d100115544580d803403440e0040030b1018907078007100c460048231a801c40c070b1241005142070400ca080080c424a04403800301026400001038241c030000c11551220005072310f151190f140400e09410070b600f80b40803404004031980e40008460400260200301c005105880989500701ba0401c010300203050085490b1540c0f4292103001e084070039a0180071480d50200030407208011070440e482060241c40e0891180c49128400318121035110600903207030742d8420042520141440f02c0c034020f240c4d408010b10000c100312802400c640c0c042c1e6082600d2803680d51800d0030300410440d4500d00c207041100041e220364400c1c00a5400800441d1a0130041c0200d00118040300200c04941c800c1d00e00315a01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 770682347 1250 770681097 770681113
    0x9010e010206130b0601050c1014150a03020d0807020907031a040603031d0102010f1a150a0c031b0f0f03030c0504050a17032a160303051c060e01080f 66
    0x5a0b100c82e02660952a40c080444003a000f04520200440e041901894000d14002c00b42c584641020030320b010f210b4245881d84650801d500c04c09080d01c1c0c20204041c103015801d81c12400250621240e480006c1c040e08803900200280019082a110040e802602601880c540b44000170001c0c0800c8401d1035002d00005d01100e0281818814103050307907031684504c00c880703007040012403009540494642c115902c40e500c03a040e620290280ca446007a980c024241e0030200d2008107e000409619140501041030040d51010303a0322002d24080741e50541880304440b8a030071031400e0048827445000c1c183c80b20580e0042c041065200042c01c1303041c0280c1c1c0c104041215500125014401d40c45079561004183ca406e2200a40d0743e100c003513110010302c1c00c0720300d0302292086940c1c2600c181e0384400354240340b0142c0036090820602481d182c2205601920642506555018100e4002c401c080c48141b01c0c440034901c00c2c040c07a644200041c25401d840c41d41075607943c1031140c0d80c6141020b0014003d0040c1c0c20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 770683453 1106 770682347 770682349
    0x12060915041b031a030607140d02030c03040302102c0f0d03150e06030613080c0a06020c0706030e030417030f04080c09060d0312050606040305011109010e 68
    0x11880580c1c81c1e546201030200c1e149220103880130244510740101e00e41e030100309603074442a6414140c0340401c601c1e034194464080c9001080c22140f0000502c19662840406544034034880c0d0300310740c40380030b1302d0414209840c1e00d100b1002000300720a8890042800f2a0230704144100064126040031194084281c035121a0899103030102e9628500f00e005100107100c418043c0420500b02407a0f0f05043c404240e82e100010b00d148200945280743c4010006204101d070000301404d001c5844030728041c1441002940003001c002943d1040d1800050014003d0080c0f1601100440185040c10714200e00c0044280f8101d92400c01400200a0341401410813800790000c0c00842e0020000c100d101c2d410701c92800d1020742080d10440320080247d0001e030f400f85a681142c81100400b080c81c1c0c540342c0119005000701e41000780994280840d0a4030941c42001510f0810400d0ba500311401040394 = true := by decide +kernel

theorem cover : BRFrame.Cov 770503597 770683453 := by
  have h0 := BRFrame.cov_init 770503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 770503597 ≤ n) (h2 : n < 770683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
