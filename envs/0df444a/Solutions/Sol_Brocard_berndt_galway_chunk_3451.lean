-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3451
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:10.851781+00:00
-- url     : https://prove2.me/submissions/3c87922b-fe02-4da8-ada0-e6a39d3b4491

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 620503597 ≤ n < 620683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 620504847 1250 620503597 620503607
    0x3070f0c0b07050c04111605010c0e03070e060108040606030609030807180b03040f0c03140703120e011b0203120f03421c14010e070506040e0402060d090c06 69
    0x1030068842008244919400b2902c0084c00307414080b01958002101c1c00300c650744401030700551030b410b61494090007aa1007040f006401c0365801c150315840d1100728050684c201a1501c0c09402011b1030080300350005202d6603c45ca42464009000b01000a5440d07280c0e220102990380c00e4809502103460070060003d5075621844040462b40d0111148004604040b1a00c24600c005000502641c500f040d061003840f510700094001103070301c0103004141c041d246001c0c83d11181b551105444040403a030a00cac20f264001e81201105140503580e60b402c9000d8001c6134400c2110348d200a03a014424004501002c0b840803000307018550000b0450751f1a440c10b90700d5128500076000345850b400e0f000603001c1c800c642030005034460b131500c01c0c401c0b03250407028080824a15050410020010000c40e0314034018098010b25200c00080004001e01c07003204820312042e507954551144940089080004102d126000388260ba000f0384024980c5180c0741000d500c000c1502e10002c1702303440503020882d04009a94001c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 620506097 1250 620504847 620504849
    0x131401061107060315080f0723090c2d1305030a02220f1407020f060103050c010f0e030a1109100f03080c01140403030606031d071e0803070f0c 63
    0x1e01d4545481081503206075103901c0341d80305490a00d62261800007211040c402e405001c5d00001c400c640ca0321800e0010f0681d45c3c91141f00303d81118a0068400a450480c00224401e1580181c001d03c080e032241c1401c03c0c1c030340d4010448007201004000e581140001600d00e070f070112514080c1e031030f621090f06c1e121485c2c0140705a889030740310350b001c0c0011070700580f0341c018002240841c440e0380740d03552090140903401501d034001d1540304070307440c228003c3c01084d010007045010702801d80c01c44c0c0000d000041000c0d0703500c200f80800740040e44801070010312588031300000c44070b0342030600d002c1403e4446040420301c0e00c03145440c1119000200c1e85680d03101e007001e039501580a0385860064055038607010010b2040d0320030380406880c11900052090040d1401d4210880c259044110391050b45003c2c10300030024140b034054840001c0c10070740d80e1603070301c0320800340c40b010003070300c24050190585000140d40d00201040000314a400004400050000c2d0a04c00b400e5890b008004070741c40c0e40c8151034400c1340c003d11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 620507347 1250 620506097 620506109
    0x50105070c0e0c0408060103050d140a09170102040807120209070f0503160302041508041506240905060f0316050301210204180c05041802100806010509131401 70
    0x5114403030100d10340205070740c101c0c2d100c1d100310b8101d501c8500c0050500e100f603030409400351050000010130040005043e404c070017150368506124940d081100b0729103110385d42105c000130720459014441e040340e01a0008580d1140c0c0d00041c5403d40e6a40500d05001700341c0c0c40b50040c06826140d0100f50300740840d006600121a2409100e000e001940291803808064100c072220121480c03910b0320580aa030489015000c02c48056a2002c6c41881c010295681103034101c1d26500c2e503d03200c4d07d0b180042d024a80590b42441807102c5180241d45150840c10400d16045040151102e0009040d84507400101182246000e0081d900c0c50b0000c044521030076014502c00c10171004100421030f4240d5450070f016503d28071840306608001500000340507203091818103d1192000e416442000a15002e000071980203a909200d8601110308001c4d42107520350002c0d4000c50403071b0741c9003400c1b4411812154403100505110741004421800b14040d002c0c03812410b08001e560700000c940f6003805904203801440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 620508597 1250 620507347 620507357
    0x1b030301150e010306090f0203060a0902090d0602130918050f162303011d070f14130609142205030a0302090d1a01030c0905090a020d0302030904050708060a0501 71
    0x11500c601040d203a4141c01c0c9034010400b000e5820465070380709400080050607100424840981c1d500304401c020360003030b189140726510314940014812910f00982e81c01c01401814100c24001e5034a43c400650b2207000d600c0c08444882c81c01040e02600d0388075104541810140d501c1100c01d00c1d141107031030000c09080807003041d80326000c2000e100600321040030954803490912042d85003004220100060315400c0c40d503065081c240c3d40e907107000c00c1411600b08107610384201d940180ea1a416240c0d5100c0b00c0c002c031034054440c01c2104000f401e2030842c00717034145041c1134005422a81e07203a844044641d00311901445040140510070400100d11140024010004516984501c00d03550241d80303124031502a010f05401040740302c0b540d52900c03441400e142d0084005040505100d0141201400901081300c4000c0d0000300031072420094420903124112400080c01e505450780c007003080100c0012421001c52104224108a81c0c0300d5025450103103500c3d03100c19886041100820034411115001541081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 620509847 1250 620508597 620508599
    0x9160909140105060c03090a0608061908031608071e02120319081302060f040e09071203080a0603060e010504030e0d0503030411011b0308010f050a080604151e021b030301 75
    0x244020a41ca04489044421036518075110410605500034000115880000d890001580982110300c840c410103085a1802d40070f01150782c003440d03544607801488450f91060204424000c0300c248142e48141c0602c8040c3c2c2080ca0030782d07980d005018141c8441c20680e00601e40241141000040001207050400103076061103480507141d031541d2800107800080202a401084d00c001c0d01c3c7d055503500503005003019550b026980101c014543c080d104001c03c007070200c0001029908049401c10a56103400306107083c0f014161400c480d031840151002c03180c1580d035000080080d000d8490051290901e40000c15540707444c0c2800b0b0403503641040c10500801c00c2000f4400081c001200b00e9034800c2d8044100c0c082605000c00407030b12407141a10910711803403000a001d0a064008509504860800c41c10314100c1d5155403e00ca05111075101d1000f40b0f6000030046000a000a812000480801440003c50001e80154082140c200c00700601250f0350018000f2202c41501c600810008143e000030340c599 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 620511097 1250 620509847 620509871
    0xb0c10061508072f0109020f030a2102030d0501080c030111031b0c0309060a080906092409010b0406120201080c041d220b062716050909160909 63
    0x7840380142003000b00070a1241c04500804c3c0c1c11241a4a01161900340500c190785011007170080c01152401ea01c100c0344111070303020b82d03c0c000842d0103a96500c103011401e4121102c10b4100221051680001580400d2003400e401ca141d40c4a81d5000b07011801c01040e0b12940042410308503170380e409003c08400710800410001c24440d1040f0941002070001c0d240c1e461aa0340d004e00d043d030040404032640701d07100080c46895a0b510440690061081d03900b0742e613440d204c42420320340d503444c01400303171030701e00e884807041071404610040566002c3c61510000c41e90761001c6d0b001a084402039080349582c8048503210f90103559000807426440700150322014a00750900350b1002d220741c60020315580c4902c035074001501448440c004052011801c11000b940c134059890003408020044800d18000c1c0703100b2108002e0000d1883c000980180c1d4a440c03c0e0040d03c800c00c800034480540b20761681407100410069030540c0f07417480040d01c10200c400d01e4403039140701c2c105d004000f81944e910000c101410400c44481c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 620512347 1250 620511097 620511107
    0xc0210110309190e25091a03040f050f010e0d1803020d17040f03110906180c040e040506011403030403080d2003040b0f0a0905120d02040b0c100615 65
    0x120300802c4600c0c4400c0021400d140001071210b40088880301c04c00424820100410782c07070a01e015510300ca503030160481c4104200c440121a100c1c807201603813104900407411111308003c60300175015024451945460b0746403140b41402c3c030011f00010f69501d0840707064691341408070001104c034501e4106407030548450305180b04011408060301c0341c8a00b07170010b402c1241100382403000198441100c3d4841e0355a503084110f0f24200d10007504c951980003072303d800519013404514891000103000880103003500801071030b200c800800300d80000404020204030308080008040c89548640010b11031581444103c800e96104100b5443c0603034810f00c4244000798440068400741610340b10002005500310311212510a000e0f54074080240300001804144081c001d00b06103d10b00808091419464444122003100c407000d1001c0d1140c3c01200403070001702c204600910380c8402c03490002d424130f0744800314a451544000c0d0f035850f89521014946101e41000d016000052001a82e01110301d44481d0018103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 620513597 1250 620512347 620512357
    0x601150804080a0e0a03030306030b1605120414100b0a0e01121106090406031101020d051908040503090a06020f06090a030f11010f0e070302180c2b0c0c02101103 71
    0x704011881150144c866414600c203a40c1c0101807059403990790078050020007860000b07813080509280041e030700e000c0c0003400020b06002c684e9910b00d041100d8250903032044000d401200c03402001c1c0c0d80304101039070802140b907003a0054040000d01c1011402003007104c030700603400103a100b059400100441c0c0d0345190001030040d00054442c11401c03450b00050740c640300d092000c50344180740810100510000c100e40200c0d0200c20b800300d81741c20164080c00d542a01030120600c010301d034220441c2c20144d100d9100075030400d03c65001c81c3d04041040c4005802103586400400059110a8210100300c0c0e08200894020f00c40c4005403d60172040e880c01000c803180400d800c424403035000115606c0890940c4680381581c4840c0007000381200e41401d00f521119541b0040c0d2040100000744c0d04028016103e1f82c1c0504032100d822403501004071000030a4a0801404220f8006000e0b00101c01c00c80502030000032000513070340c940100d11a40f04001c0c02d194010800d10800852680200d1450701c00000c5031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 620514847 1250 620513597 620513603
    0x801060b031f080601180b010c150e0a06020d0915050402030703020d021306060504080705010512010e0402060f0406020604021c0b0601122d1404050c300d020601150804 74
    0x400102503144000603414000e0f030241c0c445104d08000040d40c08442c00312a0b40546080034140310002a10004507003030030850780064031402c0c0c81c1042070079500650f4000241110600300f582c41464940e256074080ba0005035102c030340142c80b40b041c03608000527640c2141c0610101c0200700700034249600803c1d42c4076000d000080c01958201f13107072010341da20310543c0e40700a0540703030061001c1360322203100a15640140c41600d45d148500c1d60b01195940c00b8000b030720714060191642000d01e80c60184ca880800501034001d0380c001e001045038070014000c000003007000e0030841d0003c002c141050b1050000c00c0c441d940c0b8405500c00f03080c200000182403800d0860304190309107001070010b202105010300910480347d02419a501031b6032b030322140050183c0d881b541c0d5803d400c01001040c020a403002441841103070010801e03006103140b0005031400b0b424241d403c071440a450740040c40e040302c14a00002603044804466480407090088031503040022a000d000c0321500710000e1441c0d0b40f005440110090401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 620516097 1250 620514847 620514871
    0x24020a0309091a030d120605060720061c060609090608030315030f031218010501081c03021b060421051e070b01030305070506100e152d09010801060b03 67
    0x24404203079030788482d054900c00509079417011a1051002e40003500210106022a0602c0d900182030328103101034540c80303908188031403880207041034003c00c0342c5865807a15038012803d01124000c4100040700c0051554100700005485003041000780c103885c3c803580324000c460f0600c4001c0c0901030022095903003200c400e40e0722485050615000a041901c3c00904014a110100e404225a0600300929010b401d43d92203008078258480c01460903500300340039100280d0320640c2b00c007140002800c074450303a01d1070900d001030500c800b00d0444580c02048801003242507015505110611100384031000e181719403405036903089844148050f006e409803010101802900b281c5400f03030383c9110000c50321043c1e44103141c800e41c0d603128680901a43c101a4040c0c40030700c80d2030300213a041c154a0071200c041d142c40c80084107041c0e4980b407414000c048000090340c1c00a0380046281b24a520300012403540100d6044031541505041741030018103181640310301456814401c0c20003141c148201269040460301c008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 620517347 1250 620516097 620516111
    0xb04030f060f1a09060f240f030f010924050607030c0503210f0709051c0b250512040308090703080a03050f180618120424020a030909 59
    0x4050028a038020701c2c0800725091030718200c22400c404900e141d00c0c1d242181c0324201521201c0a0141000310354004581050510f01481c0c01030540c2052400041da080803550b24008000f002c40e80e041e003094a00c641401c1328440180446085402011103004c041325010b00c00000400c040c4840c4030309842401c3c024a4001003a9080c1449204140420754220703003120380e100e0301c002091249a149140001c5020428800b00b0581084032408d04d0040c030450392564196410b020400c48642c2c902141681d90b49107a12030600006c0b11000f200b44a2501d41500681e009e035070107080b6080d0b40704a20800e04100c800c2240d800721200c91481d842d0841d4240c500784000f603640c5005a45840040e40002c2c1c10302101158807803080d5070503040075104051031031050340f840d114111505241c82000908407125003008000400c1894480882500030000c2001c5580a0040c03003403007035150788503820407110702000a4408281265441403a25041d415100900c80007083e174034001d03c10404e0740074001072280c0740d001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 620518597 1250 620517347 620517353
    0x403030213031b050906190302040f0207050f0715020304030804090504061e0606030b090613050406151d010f0b0307030f14011202100f0225030b070c03030e03040b04030f 75
    0x10701c64002e164400e0f600d5404407880b81c12002409128455680b06084400c00035816007006142e03c41001074841c17411800e80d0440c0e00300300142000199040405a00b8088400800c1041010010720045a406088010b0410100402911101d20f07400c00b590b004110810000d00310303404940c2258196040001c49845c2e0b8036102e80900360340b13410821070341e03d030142c4140070110581c462001c4134803603203040090300c1d90307002030081840040320907541c80701c2e800c036058200142d541c00c080d42c002e01c250400200604003030703006169500c1c607410a0b650071a121855686101c010882940540344c2c0303014208955180ca581940a132000901030003c16464018400d0300055035000360a50951004041c41290384480c0140304601005005074800d2b000840044403583c040c120780b0313603250704690203013080c03209541ca0103201c644000581041003502810000c04110340c8040940113003015a81c0c0542e008041c1401025103000129030001c541041004100711507070b9104550461364000030000030401581 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 620519847 1250 620518597 620518627
    0x10021e070b030f0f06040b0904260a0e0f04020403050c0d03030e030d020c0d0e0a0b1b0109060506030d09050102030415050909010305100e0c060d020310080a080304210804030302 78
    0x80c0c030000200a000c014000e0070fa64030b20415124100c0f00c2034143c1c180e40d44100700810358240715103640d04004180080703004070752a03800240c0c0003d070038046010070b040b110280480d20b0303104c02c00041c00074811000003400c41ca0b00142002c00040221019400c00b8156202c40d51540025900180300e5030300c0f9880b140800d4025002404000341600c1074035180c28a107003024020354424840c0d96014015441c000070bc0318002c0300c00030031a02000c0c00500f0070505007551080c2c144d200f40d6074284510401c444410803484240584a1094481c58000c40e0a0400c01c050519101d404400c407801d000300c5140a002c0d699000044e1411a840c00b85003804032000c500003130743d461003000e680c6030b0410001d40022043c010001000591056446010000102404e29494652038801c4d06036038042030030015140781c2060b43d00990340082240260072034441c3e40d00305080c60a40440003c8441d01d60100c100000d005076222012100410a84020480010948000c100190081004080c541e000c03c0c0c00c106c3d04603030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 620521097 1250 620519847 620519849
    0x60615030506130c1115150103021801030f02091512011d0609060d0f0b0613020a050f0a031b09030209010e07271715070e010c0f02060d0204090c03060510021e07 71
    0x121090300d0410a402800d0b0410390b00889801c14540401f000b241c2d2071307511920031109207080d03250803200d0300010140110040d254030320407000c10741d4091090544d0380c0d075481c082009000d1004081640c0d0740112908002145059010783c2980d9803409001d61a100e92180c1507502101c2202c001c0003070380d11440004c0007401310301406401d040220386040108044816068042c8a08540841c501051811200b05078480c18000e1000101d0600046000140b050041e180d42200b034100486d0b032007000040300c005c8070b400b09a80c000280400c01c040040d420724010003409040080003c00c02442c2075440039240d0700c202c100d24522007411230000406107000b103184c58083d06601241e0380c22184202a00f99072050201e03455540d0920038400300716000d00415025000210607107a4030501c0040c1d445001007152000300aa811590821810200800030f01c008c1001c0d01c402280000c0034101644005c040318056001140500c1181d100c40000980000d003002c4002c8001ca0240480742070200018101006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 620522347 1250 620521097 620521127
    0x51c0204030f020915030c2116090e01090221210a0909050f010302090a0212070507060e0c06030a020901140304050c010f230c011503060615030506130c 67
    0x10119000c010048110b8624a01e0390003190308a18546424a00700400d03840d17204a65816840346e070700403801c1c0c2080b4800c1440321003100445014a40d0b5110300b20f003480c5040880c89105501c00005000380c0c03401d0300c2044419180300000b006042440e41c0480d16a0480d103d417440d140b00142480da44010041000880140c5c5840c1075041e10f024812040009401441a1901180340f10201003200c248610916114140b610030140d916440c0d80c0910015000140a95078059006c0001c00700200d840d641c5140034101c0c0c1c0d42d4450f0364030f00604000e011202742204958076500481d400c01c1596542e402030300d40107a41918016a90010381d00183c400030740340300410340d00c210003104000a114000c6081040c280c400e880e044011041104c04660b100b00e032034000c01d11102d041090503441090440501a0a0030020000038120408000003601e9041648111107241e05da00051090a0320200031032441d186504081c003885c2000c3c1c000030100881d45101d1041c0c0c9954081440e007880c80f50a4126042d05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 620523597 1250 620522347 620522351
    0x8160807061103100b0f0307030c180b120f0f010603110403150605041401061e140304060e011524020a0b010b09091e0406050408041503150501030c0f051c 68
    0x855402d040d81d00707810440e0b140303540b0100f10000140342c3c0c1021084401502c0d00c03840c103914650720f42c0000d41c01411450319140400c11584600d03180311040b4400c04001d010040e20361034440300000c0016054103c02001510740300c040800380550f0030140050356064a44504010a12010620b04400c10340100e40c4050400312017001c041d03014144a52105054620551301407000c9808050842041c41c421700c12a00003444604040540102c2440c5100600f030103454124050060700c00040d8241c1c000b920180c8880e42d07598242c03080030801348038241c042c4150003010985d161600845881c403a81440001c24030501c508030305440c251003809045400c1d94815424130b01c5503141c018506e055081340d500c003030080d6114000b080340b03889460f0703410003521004210120240c0e01ca0391444041c0002601c1101c00071018070003c5000010310108e280903400c20b58000480051283c0084048500c69100d1810f040c54280c0150580350301403030401c8101c04c5402c2255942945101e52109414040c08108040e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 620524847 1250 620523597 620523611
    0x203190801031e0f0b06131b020c03060105010c0204152607050a0e1302120303090f1605090c0a0e060a03020a0e19060c0201050c0109030c02031501030816080706 71
    0x254204190506990140043c24a02c2000ca10034280b002022030000e40044403164141340000c10410919900031409040b0403101c440c0c40b10303041c003958a9900010303031040d4640940e090007581040104030183d0220028001945484c00280c41414040d00c080d014984488484408a84503000840240600303030305c035441540312840e01e02031001c044030f40881c2c5016810001842e890401c6656007541c0c2644050390154491064688141050a5040340c001e02519145402c40400f44061449190544040c001c000c400400b06820720079002c201d14100420000184400c1d15001415a440408042c000ba03079210040300a83c0c0e069800d00d41c0d1130b0700c1400010104844c90781500a0b015a00c855110060320a90322010001e903c5803110300d01001003502c02c020050309108103000040c0d58010306002e494403000340340c103a007510b00510f03013030703001c0f881158640c011810704124841d548450103488030314a504540c0d6840a500c034400c1300c1030011610819400c1400744e54000c0742e0078030394455000c000312 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 620526097 1250 620524847 620524897
    0x1c090506041b0602010219030e0c0904030801290a0309050a0503040f0e0601030b0d1502040b0f1b15040b041e0507171207170408060403020c0306070306060c11010203 73
    0x10580103903841c1200c40da40c1c00280f00c0b0300500903241d0707131030320450054084509148218001c180704c0c11a4003142c032400c00c4100064560040450040b402552401407541c18a03408000c10849c2054086406014000194503180700000341c0b00364552034903012968403410f09210340707400e1032403070080c200e40000a030010f1a00c459854420880300004c48040ca207070744e01c2006504940c05c1641042e00114000700c0c1d100003610b4000500a04080031100505281e04d400140a054100d011082a07007140026056540d1101e141350904444a5100801403020b201d00c0040c800240640010030f404100d601140400c00101f10100d1400703100a4076610018041c104980c0d900d015129440341c60001ca855554140c0b008504c4034001c4040000c82803030b003001982c03140101596962455001d07072050001042c2c40406100441c000d030700030790003011900038210805040844c05496607050520303042c010404150002043c50800d030700418081134100c2c00900607825485000000c42d20701c0940650341d03a036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 620527347 1250 620526097 620526113
    0x2f06010b030f060418032f0c190b0715060b0c01140702070b040b180301061e0e0402090105040b0d05072903010f0b0319020703210b01051c09050604 65
    0x8602c0c0e10101141d030036101c0c20144000c607911032000311035844004010601182c0680032820b60700300c0608006995040c0c0007100d0780422a5650f01c0c1c441c41d084880303010558545040700e01761510a0590590160f072811117000d5107403003001e000419a0001d604441c041c403a0139031140740201441e030200f541e03809000b038419008081502c86501c14216031404602c0f507901c002842026925400b092528003030400d10340354003d40200140406500c0f4405000711a5182802403000030b01481600c6c80380521210b0222400580c1504820130f1024a6420800961384923a5002e045402c20b03100050f0340080f0402046410131850400b500d28070845a0000f0060f00300201c000891100300180f50003150b014802d030b05c1c588000e208009122030074050074440e00c0d540d10300031500090b400820100f8409503e032000e040e0380000000350080b4650300c51038407039241209103c00d1610070602d0700b00000b6540d00e001800500900700a031401032646400700c05d235400158490180c10750040e0885009240c2840d1000c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 620528597 1250 620527347 620527351
    0x7030603021008070f180308360310050c070c0b04060905060306030307020f01021c0504060e06070b0a0f090606170115120f080712020d0219032f06010b03 68
    0xc080d402c8a0034000d222880384003030038014005645c6901c01081518402c981c000c1d448101860080032801c0008000b8114000800c4052814a0544d91a9003d583e003071406640304100b200035010440c80b2900e45540c04500e0250490b17104000003460749440308502c144d8042c00d00c1c014602d4084c4038010412071500c001810440702c0d80d54907100e1300358441e01441400e0200341c078243d030594000d0042d8401803410b0055000c00c2c0c1c2c010300c119443e0803450500c1ea022081411660004124000b80901203180e1011b1012800034055900c40c0c58080540e41d1427520b40c1006006030002e59860041c42c041541a800c2044080e81007182070000b280c030703010070315030300041800c96007d550719100302080003540c4402c0c0c0d502100d410a194003046100b03505d8403076401d111000121440e0204000d0680011496204140b5000455004203401060840040d140503948140b01d140c0514211080000a0348584103087e14008502042182025501d10780340e00f480c03143c006919802910000300b41b181d1100090742c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 620529847 1250 620528597 620528599
    0xf0203010e0a080405040902010c0b070507020102010b09010501080a05070912050f10140c0a021f0515010305190e071d040303140705040303081009051006021510051003020706050703060302 83
    0x1000c1c0081d071446036600c40d0385000038035610041c4020400d03490590302c044407550040c10040500c10b8540e0340c1c3c06941d0400c480d040c0c089100071440c2402d5503070920507422540d1095406500c103504040020303024680c0101540680394071030340050400c51045003040e008090282c80c1d02c0304010140303046520b662410143c0c020900c00d0b040c4c1e061240b5041d00800c01c3c400c0307540c8a204961b03140c0e909a044544c0c03001c18680c007135100d071800e800030b04030702100e42020180720f40340000b40c5420b200c0342e4505444450950181018109000c2c001e8070286500c54060324454008006101c440030980c6504210140d80310740a601c56010300881c0c114202d160841c0b2452095030304010604a10740c1815000100b82c2d510030009409200501c00a40150340ca10b420104044c07500701642d42d210144800e9030342c101e4410340e103040c400300e0070004c040e010403092290842242d42d210440c1f030300040303082c2007014602ca0244203600c509102c0c02603a009504545045800c110700b40500d1a1074240034002d051544022 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 620531097 1250 620529847 620529851
    0x3150a0b0a021002040b1228020c0d030902010801051215090303090d1701090b011b05010204050f01091a03270703110409231e01140f0f07050d06050d0f020301 70
    0x3100c030441c04d10031078094881c1c1ca6441410190f8484449080e070780700070301790440c2171499892820b03100300c0210744051000c0305030405a030310400c0c0108141020410b0005405040c200745c2c2500050780c00c80c40306410341e40251161103403030320900303442460010103010384120803036170105004000c18040000c5200740200030440d0f000400c01c11084540145402d21003e41c461998018410500f40d84c0003000c0070300d01498184410411245d64880300d1003c42803c450f103030740c00507081206040c00c030000c0b04001002d090070070740c152611140b0941d44d82001d440301c0980c800000021180034510440406500c070b0540080f18500030008030315034640050000395140e00c10245408454035190144001300ca030301c44500b41182c220f100c01342101704c07030500c031030b40d1a0b01034500c14070044005000c02814040380240003189101c400094281c4c0c10f8000f811003403543c06040100f1160410031450203400c0315a80c038160350703196003040042005100720f40000c1d6101001d02c0c0c5c80c000f403150403013412a42038022002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 620532347 1250 620531097 620531113
    0x1403160b06131508010b19030b3601110c0a0b09030c07141c210302090d060605090619030308090316050a03020f1b010522030c0e0a1a040203150a0b0a02 67
    0x400c4440f020004503007c0f0601c40c3c60301440010b442107910703600104000a0a40841c0041d11402d038080b40255010b1302440c038452481d038505000b4020b240d00058059005480c120300118100e44034022010050102c511450200d265000b00304201c45800125400b510180e42c1c9856a190805449000591043c074545544041c0e01c403981c1c1c025080d1552103003811130b048071813000c0608004192045141416424400c124123030b08c0704c2071508246441203e0000311617041c2010041058400360840303018240142c1540b1145400c0c2039144252a05410601002da07100c5940d07516603c1103d1008000c1d8041040a0040140000f610100180701e07400741c0b01880c40041c00266200c0c008034652041451030107140400354020001400c01680800c0c100d07404620205d401040345240c1d178400c37128a12401010080303005010f01d01600071160000a010000d005c0110340c0003c4803800405110307582c008045203102802c4090340c40aa800035001f40c03c2903546000d128200e803c1020050054018040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 620533597 1250 620532347 620532349
    0x60f120921031e1608100b03070e010315060203040e15130902120c150f19020723180a020c060a050a0612020604120c0f121403160b06131508010b 64
    0x403400e03c619920002c020942c138003044112418140600044524006d400c000704402c40504001c2d841020070b41c4801310461108400101210500013400c0300c0481080c506205032030340413045800f2210307a90300031041c03506c4074011500205c0060350f03456807001c65010001d109012640114a072280229008644c280500c10115110304172101c207070382d0048201042e03d1292000f100a0000e100b8600d060720b05203a0a901c01030214001e10040300056806244104144141001304840810500001503c295040000b084400b082c4a02003154000030300002400000c1341d50548170010228011115503080c0719074811700510058803201c00c2203040100c0030450102502001e403156501604203480e2614002102d10710100c0180200d8844030743c00e10004800e82250b0301c69002d090282e212015500803440c00003000760100311003800c1c1c1d0304180810703180302c0c040407100b4036580d8001c07181503c143c0da4600001e25816000c0c2002800920702604ac00320348140d0004142624003100c002c000004a8034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 620534847 1250 620533597 620533651
    0x6030f02130b0a180e04020901150509060a0c02041404020f03070806010302040203060a0f06050d0f0b011211190801030209010f050607060c0318030302070501050105060f12092103 79
    0x16804858070a0045820466180e2400040c00d101d807240c07828824281c00240c0010550f08241e01081048410034280800d5103082006140141176110200000e150000310140040c040c5003851381c4100b81c003040074000e107402030240110740c0340d000300100325844094000020008007901c00780d0003004841a0403009040c001a14010707120380c03000812140e880d59013040041d5000030031054201d202001c001980761956100d010143c002519905e4566140140c010308a80c4070002e45250035040802000659030000b854000d9481e41032000b00d0b0f010f42c49407840c100c51040e60031b82c0c45002030710100b0192a60303111250303138103136842100c4c5026240d070f0700d042d40c148040131402441c1d8407040400414001810f1035000c00c05040741400d0114481e03841034060007240b602c41200364003003500010054100b040070703c14a405860212122800c00c2d403132015032482801500b401c40302c448100000300d56141000c100c4040a801031040303031114441d281c0360954441d042239070a810014094020400c03581801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 620536097 1250 620534847 620534857
    0xb16120e030d050c0c030904050402120f1506040522020a08061305011d06010608370f1109040e030408030703091d04080d05040201030b0301090303061703070210051e1306030f02 78
    0x101700550034060108101710003003201410807a4030000001d640c2c022840e0a00c40550181e1400000d0401d10148210460104070010649071040785070504124212502ca1548950708580d4012882803500c1e80c400301e04000c2d000e400c648114810342040150502006102680103031045c4000e01a40190185201605040f5007001e09a90060310040c4070041c4651995a48210500300c55140d0b0b4030500ea510401d030070030024010314401c101c075412030314011500440f40040e03015941004084000701007066a07006401c88248103588403424140c1c8400108281c40180040328150380c1c0e519110301c2e001d80600240d1280000c01b04c410a07040c2800300300504480c0c40703180c100281d03d250903000c0001800070140204100c1c117050392508a101035850034881c45000c1440f03510001030342e07810200d0100c8032003644682262144e0080003000f0042e1100c49051400240605109444010709070b00301100404629440000c4403001c24208903c900701d40d950022641661801c20851100c14a80002d038494 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 620537347 1250 620536097 620536117
    0x503040b0609091c08100b090307150e120a032006010b0d0e0313080c030a080f1b061f0e160f12020f180d0b16120e030d050c 55
    0x2004000600c2410b00002ea50707031100302031013070301c1407a44c039640095511003a000310000013885010410070302c03205040e0342c20007030101301c0e007654180f03400c090020365108494001c142500900301c0c05c10000313030300521421000f07200041005400802411003540e482c41e00400540000307a0700038003121040485224589041a244050302c11130382041d81150041d8401c14203440151358541c00b08000000902c0070707210407000a540f200d086c0e864840c1c454506800802510b20a8004910000025408200b155040300084002039100d051070310001c20b04160305000c2c109540a00c004008060790040e1184140c0401c0c112046c22040c4c4075000c124018504641c44910b080c010103400890324020300d024a4100020302d00f22240d520303490181c005903040019075003100e0f0808591a0840561541e520b26015401d40d049140035210b910307800d002c108080c011900940100700000030310343c4210508038a024250b03a0030700c4035444d6a4159a81c0345d01420703401201900d04070110b40c445c1c00003000c6480c8250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 620538597 1250 620537347 620537363
    0x20414010f1403100e1f020406051b07050402070f060f060b070201031d010608010911060315120309100c120207030c180e011113060309080d090816140706050304 71
    0x1c18030142c081d020b00d0b640c0045605214055100003138080c90300503003100c5048100039000010308179a48013040b8482440107a420360040c0701c10300c00d1039409000c0d82c410040c07061030a0083c10242039510700341100d90300050b070042c0c0009000800d01800c1e42c4900c000d507201c1c0500300300408840d401401201c4a078060100300750301c10020000507601c00e4010700100404107818209145c1c3c105040c90865003a5401b01d0402d0b5140e08030b00007406030100054900300c40944120b865132900c8110300310f4040c0c54841d81d5110740d6a010a1015501003002510f009184c042d2541054260204000c3c01c00e1685600484050900344981444107101007042e0040741d030302843c229820382c01d14456050b000744070540590403540d20040200300c90024010814a600601c0a1568034503c00d488844020460380201040c142801400c60009281404444600c00484800900c1701e00074070301075031035104e1454503c582d004c0f691900003d00400c8040111111001c4084070b042c2580c804058039540022240034104070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620539847 1250 620538597 620538599
    0x912010501230402220801140907090e10020307030207111c02210303010315110c0318060405062113030801120f050304030b010e0a09050309010c0602091002010504020414010f 77
    0x2c1c074001c4012800a00041c00035040504155540c55241407828204402095101d0700304680c0c04280300d40c000400001040d051039282c60180300d690340c2013600c1207007056640c510408a000c07200740b01d101740341c2c42521019513813801e0507600180a0340002c601a00c0300d2000a0300802c9a107003034a00502418000c401e00045c468194003048814070f00b076400c04420314104600181c42c0f8605000560203144140c0741800c0c4402d000c2d580d081211006c003034a2020090800c07580c0340c410030001c1a02c10701c0d10000c0e00e150190500601003070f100c1c01f07150b0040307801203800b040824541452140e000390f881d40b910507450380703540c1e41c03603109c2d40030045040d0140100e02031500500481200b4244800150301031200008840b085581d80f80c5540c1c41544142c901d00b40c06401441703688110365015801501207441030140c041152500e80d141d11800c513110341840241c602050410016805a0b2200304004200d03045c15080800d02a02800701110304a10030351900c10480c41d04000f100b8080c0c143d1b85101400c4090b0303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620541097 1250 620539847 620539889
    0x7050303010f0f050d051509030405061215010c080708031b030c0a081012021309170c01060f1805100503010c020a02040b3f0a03090302010e0a210201120608030912010501 75
    0x4218080c0508c00305000070800800c00b512070000038555400c1d4009011010310b003440ca1003400240e100c801904001c0600200c1002c19001030946494540101d81140d9a848003071198011210a800c0288112004000c1003a0010187d026121081490322500c4040c4d132000040045000c0b54011828941d81100024001d800e10800c80c040c40d100140c1c0001c0d070340e070a1391500c1e80400200d81048100010001d002071210201780240c100070800e200001c505503041038054140c000003a000d45811a80d00c1d00091030b2a141c20301403100070701c400b8000700718030007600038000d4548148a20a9020710b04000781d580c41d44c24404246080c0d0544024400c44c0002520304104d40305000c4102c0b0420a40c0c0601640040c1e001440290041d52003900c5000c1010b04d50710000d480d501c091000d0f14407500303c40e1010000c0380c0c81002c01e9044c2c80c0310b0742c0748510000368520058555400c0c0c1402a580186410707404180c4000c000018484614112074400300c4a401d10b1350705003070740c10034050602840d410300b40b0f101c85 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620542347 1250 620541097 620541133
    0x120f12020c0f1b1009050108150d0c060302040618050d0204240801141f03030f021006170c15070b04080d0524040c1409040207050303010f0f050d05 65
    0x44041082500c1d040c0040e01d045601e810050302400c00e09082c0c00e201200f60b45003807081d000e0382403d0340c146005007615000010745120340060580079103020702803011b03101d0781c2c90b60440c00441d41c0c445005000552101d4005009410074000c410220b900f174035a0904058080e43d1402c00c030380c0001c0628889803599408d000203822071803d180c1c07294588140c54600200703840e0001001d040c0748000014403541d20304113040008009801400a150000fa001c192a03541c4d81c081001c1c0c0343c06091854001641c03107800c074985041d80503c5500b41e4034182010500400d40103444a030410744c04c0c1224014201402000b0b0718800125500c485045c08000010018029259032507005008445541c01c1070b021a80702000c0d1481220301c0c0070206001401e0210100c044000d01d140500b003030320f04004440d9a00009482d150128410380e40728040454024440c1e80c842c0c041b188404e41c00001d503912541c1d03989040c1038800d01805010302d4000141c8010a15045c083d00a085181e0054010990041c510322030083c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620543597 1250 620542347 620542357
    0x1217100e040821041101031107150c0509040c080a0605010f0807120b040e0d02150907122d03080105060a1b02040b03191509030e090c09030106060c120f1202 69
    0x82000d1240003d0801c440c0c0d007010074429401004280c0b0340141a00006084607122400420102c1051040780c002c00d581d510680414070000c980050b101d442e0000a071454014080e2099011381841381d02c1d03038013070f511030320681c0107021a00c0c0502c51251180d0064a0f451280c1c221480044e601c0310000790b100b8491901c80701f0744403682c1d07000244800414041416034860000b241c0f000d51092640c0540310303030304000300700142c0c411121107111402d1214280383c681c61148104009a201141401c0074081103001044c8805452103000790b400000b050200c0019000100940c0403d2503c4000210f03400c28000b210724a00360b40d034030075455003a80102ca10040207089002d98215540740900d2010b61420001c441e85c40c001d0001e180f28200861501c10030320610650a018568202505040040d800c210150807141d0219241800c6544142454040d402480c4c8129410b60810fa0300242064000d0ba203518100c1c0a6070f14040d4024075401c1c287d458034012015040001c4034046170866000c0035901402c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620544847 1250 620543597 620543617
    0xc03070213090c0b030708070e1003021e070c150f022815020c011d300304030509090f06180a060b0c0309010314090601090906091217100e0408 63
    0xd0356801e9407140044103c040e0060414184004180030061390003038202d50344281180780070032003104040c000c2510341000091040501d6000305440700e001c0c10b19144030b403075284484201601c580c11402d00071419081c0b4411000690070080c143d900251068044440742c94590700100209200b41c03030302d6560000f1020400c880d414116114500080c1c010744e0405c02081030810160300c50340800ca0030b03400c4480a108440e51450b903210343d094203010100e10030840e518111400b0280130702d4050522606442050000c80705e0000104000c105504400078100c1548142d80d09034084d9203e112522008034203a640c01e0b4411814003420503420200501e07181d000c40141d002140c0f003955040561141e801950b10111a1f81000c25410803550741341c40f030440500c800c9140d14029003000021592070740b8040c000c100c18a1748032003c100a010064014190f1280d116a03c81d5140c3c208c45402400380301e148068003020804040496410200c00d040358044e980d44101e03401341c686030307581c40c0e0b241d43e4408003101d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620546097 1250 620544847 620544851
    0x1303110d080d06031209050102070b0c030c0a0305030f060a1202040b01050903010e06090f060f070309030e12060f0105030d0f0c020f03060f041202011e1802040f09050f030c03070213 80
    0x900300195081d00500429441c40c2d2002c078225085250521000035a40e44076420040c207120200034070380e40002e01c5000c4070760350071845640e6101112414110300c1000c4880415208800d544410558000021072188507480b41082080e1101400c01001049034413542908107005086d00001d40b820303034070420581405062061a00310f0203000b2a0a551a8040007100e03500f00c02c0030071110403003c0c0402c1c82108441c074080c2003945040e2400184c040f80241c0b10300105a52244103004040c01500c01c102002c1b0000d0088110030707003041e21070390341d10000ca4240e00a07501400000800341400140301c00c0c8034886450340030b81012a8030301128156400d41007664400481054003850303031000e10055008003c1c15403140001d00c0d150030691105070110800c2d07002c680c904400444030869070500940141400c03072003c21203807112042d01014017001503010354014032b004c1e85a603014007540d100705102d500c59004d542c8840c0c1d090600580303901800500700b095402c10071030300d80180303462500188001480c0d00c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620547347 1250 620546097 620546119
    0x215030f04050c0607030f270f0503010509030f03071b0f0606051309080409090303150f030302060903070308130203100f020c0d0e06030705030405070803030106030212090607020a080f04080a0c03020103050c130311 94
    0x242320041301e1300780d002c004a050000000e00c074505080c028203500c0408580114900340f200d24101800e4440100343c8400c0001e01681070800e0303800c42502c8041d9a40103003400c140402c16082c084009d049501c141c6200316403d81c01324040255a00480000b25040394055040a283c80c8105001e40909102201050b42c1d920302c0c00c0194404211090190680005010f0f070a401d6240c0a0f10340100500080c1050f030040c0b0290002a40c801080c46c3c0c0a000407104441031503180c0301003440c01d40f1542440030124100340383c4013000c40650780503160f002d042108072000c00c02042c2065a030f03e001c02c25125080001000021a024040c0c2e0040d41c03c14440c2080340c01040d034800e502c4e82141c000b078010100003500000e04010041d01302000c1da4100c5907400c00303040207040103200655a81c0641100800c09200458541000008041981e00802c0c0704801e0701d0306104a847d203180d0b00344c41c5000485c086860100070990034110704081c5c401d0594010089642a4107607120b2001031141400400c1c2d00100807a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620548597 1250 620547347 620547407
    0x16170603010f1404060b0105040b0405062115131415010c1403070c0b09010c06050406150806090f160b070507030f081e03130f0215030f04050c0607030f 67
    0x304403c01c00d0700421008915052528140382a11008004603040010a000501142c184407084900f140d6040b40d034169280400c01080200b50901c8912502c084602020070800310516614100c0040044681201c0c1d600b018030f4403c00c940040c40c1032640c00e900341e800142c150700001b52582c0c200710141040304081c2104d607100d20201e4060100d5010540012412320100400300e015000a4042d6800c06420036440c800000d22030000120041c1401c0c2c0c82d0f101040610200d5404041040e046800c02e9950302d4a0700c5400b9544c00c3c00350788c0d46000d881110079115804101003540c8142a00c0781e80c014001e00c0c5800f000800710703084034070155414007840200100049944150350308503403184100075140e450040b0036581708103540d242d104e0540c1c6c0c00c004110b0000941003060f005560b202d06890050102400840c0a0140084030071101720030002c00d200d00000340c1191140304038412011104280548014024180500040140420460311000c9071050050b000510a8010701900e00d16a41150f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620549847 1250 620548597 620548601
    0x280b0103051509011b05180402191206051c1a0112110d110d051e06040203060a0902010512090f0109120e031203040b040c031703010e16170603010f 65
    0x2910840306030b031201c1400b284404403003110310741c401c011500070400040420b1922084c1103544003004104103000515400342140c00c0740c0001e03042c50161046441c3d00301002e0703940418080c52004004038490000c035001080d098083c0350196440a000c52413500c07174010f000102c4d501020001c44103100311040300300301041070f01d10003030003026215000400701c0c50900f0444040218408003502507056100c507840421417940c2400300f5058140c407020316028942c14100d04142030390928090600e405030015a02000014600e40506e0084007510282c4e21050301101c119907510100034040b420510448250510070714000d42d102214000395032030070014805040c21a0071031038040f02c040140e80348150f143e50340034040c100078030b800b54024404000404070401c018007000f4402040c607019000041c007003000940a02c402540d02040228040e82e00320801c2601c2e400034061040314a804000081c5494001e003404803000442d07448000c5580801c0140b0500c20308001d006079010340d00e40511444000140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620551097 1250 620549847 620549849
    0x3100c0c0506090c010f020d020c1504030c0305031e0711040b0d06140714120a09050102040b1b12040e15040605060d0f060909021008070309021302090f01030c02280b01 74
    0xc00302424901c130318035002412601e10118024115400f0283d80c40d0820340018090110f08000c441e8101400460002c03d90360380300f1504010543c3e142c80e10000304100d4000003605d245010420038851071884188001801e002d240d20107001d00110031410001070401e80d1010852940150000d41d0380d410380d4483d2000c3e1040b04e11141d00303064105081000c003640c814030342984804010303081447d00c001099190405900070f0b0114009070760359043c580c100b210942c11203008000456440351606a10001b0400045440340c01400d80d0040114a070300f4000f10381c00b101d05175491400c0030321141d10b41d64000a0030105404a0940050791100301081659908015003014202c5078000f0a100c0840c208050543d1403942c4000b07140c0e030130f0000c0b560050342c4507064007800226030714200c1c281c7d81e0340c3c030407c5002c2c00a40310040e401518a60000c94641f8240d0024103210b03000740e55020035000204011401c4400d03004901d401031700f011608840320104082c0340d0304a03521100203403240071010b413990f09501e042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620552347 1250 620551097 620551111
    0x130806150616240c212904140f0108010b0301140a0f090611180409111002010b040c0302070501051006050d0c0c1b061112032701090501021e0903100c0c0506 69
    0x2141d4030f2112030049030340c5e082d0481040c904051203444400c0b1a01640c1c49081e40c60703080c92519488100c1c00640303440d030142c440011101d40c1c81c45282481040011640400e0007803c01c15402d0074110001400c05001e8881800c510901000d003941e642c0441000070305804440c243c0c00703610351944c100492014041c200c403214502d012030b544e44485508101d84e0740000740c13104c0c2c00b4034201039180e0042907080c1c014088218068541180b810102d900c00c900505000d804681d2180c5080280e00b501a03140c0d001c0d10100344030320000c111a80760003071b0541030014140300d504005070381044005010032954210424001060404d4040c229495549400c0c2885090340d0341d40c06060400104981030f072103d9031644020104003c4c3c06089142a4000b00a2200800b42400c0f09090040500d001900c0000d65a032001300038001c00080c450341c41e00d40e020754010034044c10404200104078400d100380f80101c07920300400800806072094004a07030400317850355060044c00d00008400c44404141c0074007103248113040e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620553597 1250 620552347 620552357
    0xb0a050c0a02090c0a030b270705120f0403030608010203090c01180515030f06060403120f0915090303030b010f091401020114041407140105091203130806150616240c 73
    0x21005001b001c91b40031084480c851031010074401641031078600c3d102084030240300c40d0041544c6125050b1070301d20884291005c0c1e1107001042007058030f90700810a00480c800d0790180001d6a0311000035080c0e02068448202d142c10441c5200c03040d6000307208a004850b4000c0200080617a03074000508044a920502c10a81c5400410040225600c1d8111544001c00300d501c0c80c14282107486031412407400034032a00600c08165680100d03075008440c0314005050030600c1e02076014544e03e00a09094070351004a012a0410303003071416070760095021208c4146580d0f510b03180b080c980700c0700e840c0c54402e0009a906656840c254079000600d00c90201d44198080d050040ea00380402501d10b2401d1441ea100b2480c1a480740d044100e50780e0301c201240d03d81d100440760300207501c00c09022a8154455054050761406412400041602e8081b074481e00c6014a405030040c01c03a055424014184558801d03400c610f000354824a000404c0c0808005552184020807000661001208001c0340c0740844d0f28800302e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620554847 1250 620553597 620553607
    0x60b07020f0102120d05190609150510051c0e01090503070b060901063515040b030a0c03170708040905191401120611070303060e070203040b0a050c0a02090c 69
    0x1040000c028000c07031100780b00400112200b4030345071945004955030703094240d8941d80411808400407100a040303840403032003040301e640d66030400c070000c00003850886d410040640001407030745050800102028a141c69072850146842440610000ea103400500d0302c4e0b507a071100b4411070500344210014507114500071640d880c91814140340c0d000c0e00800b040d206d40c0300b51006003d80c0c0d034441c40503604c84a510b1501d5855040520b9203c020100c4c10164540002010013008035482d50721040262060060b1020032a2000050505881d01d0f241c6601508041d034021040000400345202c0581d600c0702d4200c03150800140380d543c401c25a0050b03206074000c6450301c0501070141c0008010061580300e4110401c00f05400b46018202c0240c144544803420341d041e50300c0400d10580360070140c241c5119001284c2c1e01c40d000e00d000b600519041c041c14001800d0400000c00c420300020448044c0c400014004c0d013024100c0804980c1940300c503210004c5800380b04081c0c1c2c01030710b91480303450040c41d101c01505e07150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620556097 1250 620554847 620554849
    0x405070803030c0d0c0c050a030818071211240d0f0b0a030602030916030b042a050d0809042a1407060506040e030406093f030210060b0702 61
    0x1118403034000e805181c00c100144407041c9416401c60b009122030000220311540d1080701950040e00006d00a4840d0190717180d0201055405020035100380c2211008603100310b41241a95aa000980503c10800c40b4000d040408a0442c80940b580c0000040140e0400101c0010312400e00f5544916481701980100d010405602e141c002c000380702030104000c000f5184120006411103141e072102524043e400804210b2254061050790010880700f410141100d03900d00e000c4141c0c10044030b084d073701740c1148500707403140c05401c02c0000e040d140d84a04030840d080c101301c00c1184d10b0000c00f404552060f010800d22003a41ca40d80200d14038601e042e510504049800130103043c060780d030380f12400104003448403112940300c08081540c0c030203034000c840000c4a50302d41000c1401003c25100d550400c0c44046400642c0903440480384043d508061110154071640a20701c602e00112030754800008000c03002510090a1a05140f5102034000e10403151400c1101e040c90f03080701c1c0581c00054106500017851025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620557347 1250 620556097 620556103
    0x15020a0506130b0f07120204030302030d0c050a0903080c0118050c0f010e0d030305090c030a291909061d0a05120a09060503090c030102130303030b0a0b03060f040906140405 76
    0x40305030000b02c64107025095a5600103040f00041c203042d080704c0e00c5004181d000d4410820110100d98910046541366220301b4065a40c0d0090186078168909040c80c0102da0380c864000c6c0d94144010b612107003815800e40e03075001c026402c0469110511f41d81c8032a40f80d01c41c1202c40000c468180103c01400304154088140601079199500710f5050100c009600322094859500454a094240c900000d041d11000611410001d190780c490351306108110102003804118052803410700c00b84001c00182082074082144200e40c2110325451a140110b000319050049030011040d0901c20400000c10318002603641c0010300c0107002d018010303441805c01404110301081070b00c00d48102002c485084c56601c500c01017217100740d405030004104001c0041003000b0010020a800f0001c0140255100e46520343d960840f020380340b0064001078103203a44040242808211042070780d203411a080d155030f940078140040700d04060034117070f0040c0d0382e64182c602188072803142c8119100c52242c0124503003454206186 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620558597 1250 620557347 620557351
    0x708160809040e060c091e06032e030206070b1e0903040504110306030303062b03050306010813020d020910050904050d08060a0807032913060606020a03120b0a15020a0506 75
    0x10f100da20150500504d82d612009030b402c3c864013250105100e0301c4042441c0a100303640a1015000750001c0180280c1200020003000450103642c10207290355030b070450440e1051642d100182d0040010400e907800b1800c2210940d5000c10183c0c0a00000075a85115548001086520750780741e4001140c1400645040c0c0200240c00c84544122429401c000000985911004d04400e1054090f201c80750045000d4042c00200900985e40d00a9850814100030340103a10441c2c4c52400038681500244004006003034101ca01034000d040c90320009819400e00a102001030b064000076403107400e00280566a180e440b1b44182c1c89440680744422155074003522401c0050000c1c1d1003400c1140d000c0c00203050005240003229000750b01241034100e1240340c1c0700d0010320300e41d105d644485c080d002c02c120090303074500c0e105001e48500d20400030142d4401c0c04a07141e1109040003000210824070140a01c50b4a400018044200805840c001d941e60030707610754100d80368402c1d1005604022407140900200b842116 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620559847 1250 620558597 620558621
    0x3070e100306051c0b060f0409020d06091703040b0f0c0412050106050906090606030c0f09060d2c072c01031a010f06080c07050f061816050a0605070816080904 70
    0x4c07200c1103a540b07100381000d006004501401144032005e1079595544c10a40e50a0340140400045401d0303401c141c006450342c084150791001200781c0f41d010440e40c0004481c802e5810200407807003510f802040c3c1c2148100600b44210400050002140381c51030245c0d5541c00c0b03071040000140c1c4e5441e0006000d40000002c0043d84100010004c101c41a00c60300c0899501c43c0143c0300c11a52a0001c2d43c5824607405441c5000c1d4101802161840321200e903948982400c2506455600d1000309040c4e04015420740d000c500000f0b03800c2000200b0119012500544564010286c10496824071458141014409900540e04c900c41c1590070911005c03070940403800750040a000300f034403506056014001640103040d07d84840e40014060003403100c00d0001c0e0380030071850300c1521110f0400703203600c40041040310340c035070b001e40590800c46a03420a48940c034400c4a0003c1c000c884a246803400a8071140c024010a48036100c04200340642210340d044103916091252001a0701c81c5900000e210403034103c1e401c0301d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620561097 1250 620559847 620559889
    0x2281b0213091211010b0a1d0a14190b220b0604030b0915010f1508130b04031d091b0714010510090c050702130f020c03031302120a0b0c03070e10030605 67
    0x42c00000e15202801d203c0b0007400c0b582e000b80d0340360304400200902e51a1150200d0ada541001e001c9081c601201902100303000340c0040c40001940010800d5411313140d840c12002d0034a1701a1b01d06007046031703001a844001d004103098241075690701c40ca01c98420440305001960000e004a50b0340c3d18510340d207280940040e508150a05007488021000d2500d84402d00341440754100004581c017040d000305120865115004805600f42860060103002c0c1c1005026107500c5280e280b11031b1420300c0429184907419000810031307140f007e80d12111310f542c04140c0a031101010340712241c1100c902401034134041c088500d110299680b5080d103050032aa000c40609040100401403070015907645201c3c2049200c01d034800280b00200721032410000d1080c00000c6005000200030440d1041005a829900074000d452100116442c91030581c1c842013070b600000c0c40034107280c002c034882c0140c66020310361241719811300e90641501c010000324062107078400c020009480e03410274405428503a440f441025900e04036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620562347 1250 620561097 620561099
    0x60f0e090a0303020f07150e010c03020f030f0a0b060c1b0409030503401505010b0f0a02010b040e06060102010609270c0902281b0213091211010b0a 65
    0x1265103810070584050708254001c195080c0c0b01402c8021225620341c0a903002d05126241da0000e005028860307000314265280041c6005003601030f0088a00404c24404441d01d1584e0340c908840b070841d0090300c82d0011070341d00c0c0c100540b0b9850700c00050040050000090038101ca00a81c40e800d88681441c406000360b041000c1800040d4110080e40c1d04504114034100b601c450303100d44100055180e950900c41c00140b4010304d448551144080e0f51510300468102c045041084400703416600d080c4103007031040008000e00e404c11041d11024007600b505620011490f50501400241591f01c1005ca070b528941042d0300b0700c83d680d07030244109002422000c03828025400d406c60a08440086001c000c980280020f007264100301c20480002d020b0111120115160400c00040d040d9249101b00c003c200401b40f01400e403036440c0540100900080300c8012040300010039800d0126008840700c010940300d0306c400c100300000f81002002e54044035595100c0d42485040c840380e41c2540c44544d41b0310300620401078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620563597 1250 620562347 620562361
    0x5220e0109060816090509121305090105030109030e010f0504080d03020c010b0409050d0c140f0d021b0901091a04110910170a1d010501031a01060813060b06070213060f0e 75
    0x1d8070855018585c005103560350700107074904024240d14603914421000914200c2080100703481815a081511484031030307030b00d0786c0615080b83d117100009004180c0e169640000d661007a10308040078501d5140a904061356806240c1ca45a00856001d002c0b80d00810040780e004d40c244909100214115001d000d80300064803943d0702d414108004c01d007000894412841840742d5001d520402010f0350701101c1c1c182050146c0140c0303a880ba43c400e200103005861034541d01007000168101c505000070300c1c0d940b00740d10340714140005250014032403503200d082c00054061031352076110b103a00c0381245400c4250740d61586020800003000c84021201807100e043c03070341028480020754903a4800c0400800090080400042c07030209405005818143e601b0038002204004117402d804140a607a108045500d0b42c98031410389003e0030854101e0810f03550f034a08000814050b40102e1a200409059a4a803408a401103509c00184030041900c06444140400c2032807404a4080700400c03819400c0409801d00c92 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620564847 1250 620563597 620563633
    0xb040209060d020d0204020d0908130305121c051b18040f020f03012112051207050a0f2003121b0a1b020406260609160605220e01090608 60
    0x42001780c0100d6000c915240c0d2080325a000722400c80d0010b0407a5143d04142c010319040c03080c00e000854030b40c05444650f04c0300d1045501610006c0300b8166001c0c01c218411142c2000a000003041c40414803040100b2505141403040240100c03540505840c080c0c2c60090244400c0da00e6620140c2c0c4090b01c10881d0440c0d030201201560b0640d0500e48044892140107400820511614075015104240705818440e150390000c0042410003400491102c41d0303501c0c070000340d541d402a5403000020801120128420500c208411100f108040d02942c02081a5110480c038640218903e42c2c1400e041d102440124003805400f240c0c1a80c2c0001042d05d444011b120042c95044888180d20b1220706581c944401c640d25030300548060509440b126110580c541d0b03029102904031921020320340140e201041e01e17181c0c08140b408000c0e80c69040300e10480d18121003101c0a500c101050360317000400c0203c844216a50019103401401d030302d020030f001d0f03504024012080f2102c55100142540c031075101c0700005c03240c80b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620566097 1250 620564847 620564869
    0xc030516050a150c06140c180a0e0105060c07080609030c10110403030810090c0f0806030f210d0e0c0a0e0f010509040f05330613110d090b040209060d02 67
    0x3c0d1500740351440300d034900000646800c01c1d1465400c00f10100300081c80da103001c00780c040c5502c05180c109403d08110280001564203000e030038102400ca80041c45107080007002815880703422400c461a003540d8074030ba2414000140c03a10321310b640002412a640ca40c0c20014207c00e0b10080c64200f10303104541420300514815840b00906010410303000803141e002e0317005402c0083c2840078081c401c8903400d02e001003541090409a4010407044804a1700750300340024a0352010072008010b00750034081f51030500c1b0742001540700c000040d00c1084840f00200040c0a031100034510400281a0b11480804000a6605030703045065054000d00800040c04c0040c42100e0448a051300c1d03000c030584076401e0231800300000800140c02031203190f0740d00c080000f400803001d0a04440e0704406091078107114103408812000d591903503100070080078080754441541e00c0741054400d4091090300e081c030340009090985600c13050076070301d5010f48000c002c1036003860a1102d5011804130707480040d040c0745500140e840001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620567347 1250 620566097 620566139
    0x1b080f0c040e12030c0405010305130c0303030513060905070f0b030709120c08031b01050105060c1b1f03091a06060a080c1608090f01020d091a070c030516050a 70
    0x1c0d0700b015400032405203d00807808001100c0d281e52032408207030001a944c000d00c66176001a20300340c0020105507404080d04101c960000e28541c0b45c41c5140c42c00c03009004081e1410a070304010500e84c2c40014014481c0c541000e00c41e801801000f40b82420780010360915a00802c2c0b00442041001051341d842071101d402c1e038102868152104040c1e007801940c110081d00022160320002565134008100306001007291502030000740b14a030307221400c0c0482402b5012401017564060b43e00d06015454610704d2a038010406080b0a5004d50254401d003030581c017072410b56001c29951002801440f05071030400c00c03510041c04000e1142c0c00c000c0c0214060f845030403007000c2044000f501080080f400c074000c0316100f21444481c1d1008260909003c5031641c40b500b0802e108070440481d071140b95002140c040189d2025456007460b0f207182410740b01514a0744141e043d1070050421000e00003500902108000d1401080100543d01380b400322559101c01c541c112920404914104200c9074052580c02c03149654 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620568597 1250 620567347 620567351
    0x52a03070201021c090c230d020f060a08041118040326090c09010e0f04240f0c081806150a080a060c140708030f071107031b080f0c04 59
    0x980d000301280203000e44500f1400042640c002c1c003e64100d5500168001030050b0038140340f6a58444131900f00030001c40c21042d8022034240000e1403481c1194aa030103040c00989420000b40c180d270005442e6500010f50b2101140102085c032043c0800050700c486040425240311602010380c4031015520f40740104010100003d01c2440c581c0d080307102c100c44038030781da021070003844504118440c1500ca452102c211030040140c900005112058000030740e0180c120305102902540305d43e121070100302d0b02c07852403500c0400720300c40403182c1c0c81c0b241c07040d40d40e440b0403100c0015000540300001480f036000600130140d00e086080300684044404100c06800c81a01220b149103d58810701040020280d94000a92805500441418883c6940054007080d0581c0d8850040100c09c000c10b40c3ea500400310041c290031824400114501000d00400e60070469034105500d4200061f0881460412185c104684d11400060705505a600010006000e030101402501c400c1c206042619580c0c120340c2e058a00c900d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620569847 1250 620568597 620568601
    0x6060909020f070b01030305040612060510140f0d02030114010e030c10181707060203072f060d0f0b03030705100b010e0306040b15010f020c04050703230a052a03 71
    0x108480440c1c0143c1c0d4080d0400d00a0340e9281000340c0355030814882c030b001183e1040d035508540e0300d0520400095481c01080c09029040c4064115101212514080400365013044540040e440242c0074003982c01c40c5200160ba250b0502060540e4074021258007418000510306003000780d03401140d51401c010301030740c000c02c14102680c012250031580c2c0b0b207840030034061050080380003400203070f0044428164a08441480307594550499513881098006050152100409103921209808840e900c0000d001180014000d50001500b180c2c00b4145082040c0c0d9a01c45460000c2d58a00a201020108a026505080564980c3d60715424018441c40403143d690840c407c641c3c2c090303495400511009421560715290515005015090948202403200311001200d140c941c8100002c0800c00c40c10b5014000c0701e007240092002500c8081c096809140c1c80b403207102e0490f202d03400c003c1090300b02c00303408001500340007803c00b0850b000907100280d400c000e19140c8145000380a401500300b10341d80011303552070b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620571097 1250 620569847 620569867
    0x6040b06040f0306020304052817040b0f0702010e030d0e06030c0705150702060f040305070b09010f0c020109150203010e011208070209041a0603070807050d05010b0402030103060213090606090902 86
    0xa1007030350400902d00d03000b51004028031805038041c0d440350b0321400445040600300312050a05980b4402141d21701283c090321400090080c1701e0214501104200702800c0c107484207001c03181030b04009044060102c0200e8040199039001c40343d8218241c064014050f88100588000c203a4031140504501440000000c5944462881c080b00c10383c9411506440071080364002d904000c0700b060300d1041c01446000c2c0850040410707089514040d50f410f0b198180750002544d02d0b01c0103114014101c440744c1d5642c1d4400301490245029802d451160b56000164010b0320340790404070b400082d070703003018502d1040c0b0060014050f20501c0741d040d10003c50f1340c0304101c21107151101c580c0c8500a03000f900504524140001c2100d42d01d0743c00006000101005460788d201f1080c19070f14034091003000f4003036110032402c008600b04105640421409900041184600e07107000c10180d81c42030b40f040765101d50000300e0a6860100755030800207080f03400781c1404190714020000303008000a000e6404810b03800920b00d40c0c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620572347 1250 620571097 620571109
    0xc08070f051804111e03070c151527020f0702150417100f0b0a0501031e23130507150923090c0405151e030112150c0806040b 55
    0x110704000740140000901000301d21250340003141c0940d14007108501e1707170400b03001400c04d4920600050f510914102ea403515190140000150f41d2240141d4449800132a41411030b007810140c1402601e40300a40d850442c10000320041e80d0704540060720501000030685d0b540d9003141d290a404440c00706801c00c941c0c030482d03403074843c079070050010420015241c121004003145101509807031450400401540100d04010b6400c02c03840e03a0342c840001041401198020b6002c00c840714400400d42c2e0303040c0001408042101c40908045030021a115551041a401103100c198804514581c800c0c181040e56a4596607000c0d6000d000291420780d45900c01103442000d10074000e14a0f5114051040d21480c003500c040c40f4a1002130340101203501c00134a110f80750300220f9040703071005810500c8103207101c0000b01503a0010584850079211403070400901c0d0f0280d5003e54040c00002030300349480001407070b00b02403074030390a000c40d0303582030624040b030305e10a40000803668845400d6401041c200c19802c0042e50f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620573597 1250 620572347 620572387
    0x604031b0b0a050a021308010b09070311032811071b030302030711010309080f0705070b031005091b040e070810030309060c050f01050108030d150f210203060103150c08070f05 77
    0xa071b030703a070710390000b4503c0015004034031000d0040e100d0b40556216100c2c2141610041d202649882504201042540349244203100c1c0c0d0710762040b0a02881d09000340000d090361407580322404a4540421721409200d03800454403500b4600070310840c007407440c654019459000c5c1520160244246d403820591a0b4001c1e00421070440d8000c1d0340507942c1c09e1840f030f44281600050b0703080c2c46a10a101c00801c890b80240110390062a800c40d00b9400349291904004140c0d00040c1080b000c40d0b050250000c80c400e800010340054645408005c041d03180a180050112a0060645611400f050b104002190700042160705640c20b40c0f916021548803400c06a1600100c3c07192901c1a40c03803c400024060b50200140158000b5500180002c03801d222000c003402c2e400b40205407030200c00e41000c000c2c0e80c00c0414100205030b4041e400700c8501b44c66800180c01d04109074002da07200061204d08060480c03945c0705144c02510141000340150804081c0207102c0381c107407a020303c10311000040070116600748240c16a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620574847 1250 620573597 620573617
    0x30f040b090c1306060e040903051b01090f080306030607030209010c060506120703030906020705030f07060c021206010305030711030a030816051b0a020a06140306040522050604031b0b0a050a02 85
    0x143c80e110004550b075006001520036400010101d68494906150500803189120341580e6400e003403d0000f140706004003443c2d51280420365075486603800080d41e5108100d140782c0100b11090700c91038494181402e2407401030002003010f2040190801aa8001c00014a01500a10002615035650020554481c9440c0c440c0d102d910a02100008050b801103454054928950136542403943d40c0d014507648025000e001251908181414051603120780540000140001c00845000d9804103002c1d003800b10030b030000e607030603000002c20505001d00e9448152044400350000c0810181644005100f1030b4044c0c1098000c40301c28241c035040910807015100c2e042c0c14415050000304001030030f20342d90182000b04a00406d040d11000403400d00520000d20595851010541356549074010000108001001510000c1424400c148140c0243d50b8110300d00b48180000d11403402e0605018206180344e1010b00c03400d802c101600f00001d41241180303500211480c10206280e281c80750f20300081d004800c0c0781 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620576097 1250 620574847 620574859
    0x90204020c0a0b0907050a0308030a20130f050a050906041d0709050f0105010201020f040909051c1d1c1b0909081c0b0d03180e0705070215030f040b090c 67
    0x72401d002082003c58000c0e08140c0440d0400c65480090161810041c4005003050344140006401540305170440139038100c04501e180d40f10010360220200741c0c0c00001d0054441703540318030280444281c03031070740e8006040100c0308440558a018000355007480b00800c1180525180c203826136005802c600607101c0c0406000a98600545403080c10009000446031ba40f12000e0a1000041d154010b04c01c440e41140000d42aa140c03500b4030380e00601403c9410412181403203241c80b8000e000101c510942c0d00d45445540e91285200e240f4404004541c0340d40b0114400c0241d040481042c0306140220a512070340070a4484854400095a990668080d807040040c01c1c01c0c0018071007003003e4180104075440001460110302009421a0400c68019011150f008400f9a12103030100b40200807170003800e80ca9150b141441c0d62110807129022805a44900210b4004030741c5404503c1c00040d0040d5a0071913031211803e51034204d040c40c4a184002d0009082e0303081c03200206d0354040007405035440c0440c002d441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620577347 1250 620576097 620576113
    0x604081603020c0901090207020108060612010e040507030b07030506040c090609050121060306050106020f1513140d090801111204080c07120503030610021603080a030e1b040506060a090306090204020c 88
    0x406c40196110000c02c038002340d4440300061a41c0780c103400762007080c031202081c09500d0b0309088600008100180c02501c452056800000004512a280078440c0c91745950100d900c3c14990b06120584400030704150520001c1e0742d05000081d40846144112170003440c046103040605a40c6c4490b0346803111801e081d450620902009020454105038125801b546c211840e1554503000c0700d4503807030540001c0f0500340c1c03a040482d04428210700f01101c5580140381240e080c0f0003d00c8128036106980304007001082c0209410040030000b031040125000c80600403514100e00c031000c000c80c500c0b004000030400140030408802080f010800e101c00b03004c04d914412075000301400c0c0710703590f81c104894651042c0c0c04421468410791001c25070131041c207180308002c503105003160340c0c0794180c0d04281030200401d0fa4980c10b170141440c08000030394505981100300c0c8100341c0890103001c00e4030342c01031a050082e07101300b201d203009541c402c4128040b00d400c030f000010203c01c0380c030000c0c1c040d101c0c40302403117503600c91088 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620578597 1250 620577347 620577359
    0x50d0501023703090305161103060105040e030f0d090813050906040b0f01030506062203060e03040609170309060406030506030f1b0f150c0a12020604081603020c0901 73
    0x10040030400e5034800c0e0501280c08000c6554000740001c1e00b500280c42d084a0b4005055001ea041200011311074106036050508056101540c2035030994140d44801c28054070350280c0c1424070600380501030070b9a0500841501400c00d41d40d81c418400e912204030400602144820100d40c0031080403540580696a201d031241c00300e02848100e4024984203e04907030210741c241c50103105108a048003c0c1c840e4019030121401900102001070080390446020480d1990580540401494504e288c10300c1e44086030943c18040110791800e031906002c1d83c41080240f01564002040c40100c03016540c401c138984541181840c190b00174a4041504044d01141c0440e1054050300001d00c07940003034049812160441180a03940e04900c00c02c803021a04186075241a41817000c036004c51040040c0040e101018140c0001107181e000b9124071701c09400400208040000060703084c001c0c1c07034480c8010300d024281a2265400742c811102e060031041851006602014024040c00118030001412100c5075030750707a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620579847 1250 620578597 620578601
    0xb0a080906070201360516090e01050f0f07090801050114190311010c050c0612040b0f07020331260601032102030c060c0712210209040204050d0501 65
    0x34494200500880303000a5000f841480f81c42800304000075007030400008081d202017850110004846405800644800030a4040020019201d500ea0090304c0c40ca00c0c00309401c04852005401c001564100303018001207141605030690003100211400000e51034240081d51501c1c01540500e5041d402d041c00062880100207400b0302001c0162410302e840040b82410003119400d9010003810009880b01e180c48a521850f82211401e00c1002140e402d0041c0d07500041803a007110040c4013500c841001000301304000010b8140e0045003d07002082c050615060180d141d019031a5060352280140317403010600840601442030300c08a000d0300407042500e481030250740c10202610710f0b450401e47c1c0c401d001541000210715040341d412500707590003580645010a102070804540c0d008511041c4101902c1e4101880603901411803089451356a90340b0345002d0000804100016040c40074a0060102000c400d103081929005102c40c0140d071604160f00150090241e500100c0d0020401650841000015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620581097 1250 620579847 620579851
    0xd0501060e100e10170c04050a051e0403021b0a1e080111090607120c170712080903070201121b05040e0f010b0d020d2910050c0c12070b0a08 62
    0x9545190b415100c214000300c0a400743d0b1410842c61040508119445407944e0010340b4031808000e40c0c1c00e807038504000030f054441c143c2d001da0565644105000204a480c03081c00000014031140308601d25140d180130351107061072642440710410341d004101e00303913460501e010050164604070600f1060035150a101b0104540141c001d250301e4100c0403240f804500c8185c4c1d40d640d1005089034544241075807004074880d4900090b80500c4201101d010018041561002a440c1061502c0340c5078595030a1100c1c0c81e045005410043c072600c1c1c02030010541020040360000354080c04e240100c004400621001098920301d040c082141100226034080c0e0700100410846a000c1c4007136240c1e440707110050002c0c000a1040f850341c0f010030001c200d01400e164014004604090b00c0001d05419003c4d52025040c80c1d05c2c02d01e146840390880040005d00d42407054010f04215850806d007004041e00010395660440c40d421032003603828482c607207400c0c50304000c01c0c0f0150441c3e043d50380d11040f0404000d8070645003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620582347 1250 620581097 620581111
    0x405040f030e061e07051e0d02070f0f060e030a0816060605100503180102120703020403030305070305220c05120604030207080a030804060222060206070212041d060d0501060e 77
    0x34640c1c010120300e080c0f001d075940200002d40c8418000e10480c1c05200030360002c0011a0b140c006c200380f2080c429101d110404401c440000038080a100850303000f801c06205400884250204000c1400000550340b04e840640e03005003443e034119514000082d10f44a5809001000c03804006070842055000c4071080b000d030b6208280c1441441d49450800841d10f84200014000501c184001015001c2c0107258054640d1242c00061400b03040701c88140303100104480c8040802c1d0005410800c0540c903108241d4090910b10f420882810b108402000f070700c03161701c40c0c0c06241074180c00f40014002000a004d004080091607030050402c1c5d81c0090b0f032980300480d000e40c00360040311400a12000c0c007142440c0f0355541951180121f0340c450340c4080003900210000c3c0040d10562400c11400d10344c810440010b45820703001045c4500e002000240740c06003a40a085940005100c200f20040c8410358000c2d0540841084400c1e65540c64081560401010b40151056081400004070810110742a03805056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620583597 1250 620582347 620582357
    0x302010b04052802030f0705031801060303020c090a021305043c20090418050303090a0507060507031706010c0c09050a0b010e01080a0c051b03030f09010b01080708150405040f03 78
    0xc0f001c03140c00102d0208070784031194524004005484240f05900665120458420881c00741c800d00158a08507403968104a0269211103906035041c41c0411680f40e0001c08a00154581140c181e254010b4000c24841d050049131104d814080c03001000c040c60700c42c03109900740002014844142603514900b111450030380c81d450184604c3c4034800c4100b1605800c10f00301030080c680700740c0c00705200050003a07103000ca06180d1021907040001d40c05100640c09101000b0040864680600308903050241650080d020302c1405c0105000003a003105000303810707103821303007040c0d03c140d40d8040141c0b42d80c070ba5044001c01c0451801c8021902d040190f1000d800340308010010000d1f0104400150b520030710320590203020841800014800003802d4110b10007110b4903140090826420b00084c01903600c00403949440da80012081051121a5406940d0301c840c14030000c1c8450403d01001800703103a00507003400e0410a0502c0026032544480d00141d41034800038104120601c3c050505024130858150110b000a07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620584847 1250 620583597 620583661
    0x604020c0d0e041104210204200a030c080907030b1005040e07031704210510020f0909060609150d020c0d0806012304140d06150510080f0705070302010b0405 69
    0x40140015541170f0b40c1b240c54248841042c3d4880d14000d40c400201c220fa1040d01e4603034810803000083e110040c0002030820580d00c5074942c80000e030943d0848610442041207480402c03d0b282000929002203a80200e5811042d0315006101c0c0000405034001607005410022200c100d400c0025188080724080d4462a245040c1c6e00446401c034400c504c01d0205040c14040c40558102251300c404000d1b078030881c1221589a40b8488003c00e0380c0100c4115021003801044004540c01e022001c268010811070308240341c1060940000c003800200300420603002c1c2c0200d146206090250304880c9400d050030201d815074600c0380c40041060713204860361400603138003140104500b01d0369100060182500c520035400c00f424100b4850340f09031045a0a070780705020542d14400305255209484a540f07119000c00311036801d1406200c40040c92080389801c0201c40420800750b0700c800c44550b900b003103003841c0035a542d07011402c040b8050401d082c41e43c1c1c0c1c4540340206000016100406031501081c8540103d02c82ca = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620586097 1250 620584847 620584871
    0x315021206040c03330603020705030f0c07031401060f0902031312020c090a0c110f060f1504021803070b0711100315090504020906090402180604020c0d0e04 69
    0x180c0038003030400400080950200d4428902078220030f510800600e00040d41012a030060f8140040038449051100c0c1c0500d80d14030b591001d81d10700c8010344080d00381545880c80320f9958954034030402c4c50386001300300046046418000c041c40703224011070f0004040c00300c81e980c03081943d00814551081e041c02e51040749c0006075000c900d0003504d1084840c1c3d42c0d030411b0980c0c1341c1c49902c404048000480c0c11401503007112461952a441c21602482c40c95000180d8101183c0003d03011080e4021030071354030750040c0e0400c00501c20001d4081d500c581c0d4035907580d44030f448218110b613054420300303050b0f94820700105000720100032201f4400b60b1044210105d611003507444421040131b11404d4005445031050410752641c3e030a108001d00c954880d41e150000300254129141c01d0449816040380020380d03190000d0109524005011a41051003142c4006540c113085e800507001042000091020001580c00500140d446905503254080150155425465034100050a51940250380c511541ca0b003401e407250 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620587347 1250 620586097 620586101
    0x411070807022d03071401020604061d010e0c03011103131b0b0d0e0105011a040308091314100b120a05040f29010807140108041401090f0b0f070815030a17040315 71
    0x10034010b23005415140c07101d8075480003808101d14403184060010380b8407101c0c2e810074403550400f0411344c0702405518480c20304040c2500c8241220102044003402800241e03000c84039601c04195000500f5031400c42021480241c04001d0b5101c0c101c9001c000c1003c110034501c642000d0501c0d501c0b00000c00190380c8034000b59000f2043d540d100c6152400520082c00011101001041d0381407000b03000d03111229404070140240c92803c44e100c0001d280c541e0910048a864000c0c000140134000c40403030406030220204840d02c03034010001080562103102080510030030204030000c4540145405401d42d0071f011590005528200000c2c0d0741840701c07400040c400c1008034901c130a44807030440758181012260300440d0620070141054514009080c070b000c5807013509100d0a0740340f034403500e203010202c001414413800c5014000c003c560700542d59800c00c15003542c003a40030b42e84002c14440311000d50102801007440c2a1104000070240044205030303810449202c2e014008491042000d840324281c9841c842d81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620588597 1250 620587347 620587379
    0x60e0c0c06330f06040b0403140606061c091a1608090c010825021e03070308010b031308270604061d01030e01050a0902010e0411070807022d0307 64
    0x128000300c1c0c41c0d05007802c10b01c140300400b80702c020000c40d0801410400600385a10590001c122001c000030100700b005049070070103120842c0303207020f056180740510100781e15105001703205d14282020601058800d510b0fa100242054012099511035083c1845085501c0300035914a081d5006854192071100e100d813901074840c0c105134005c0c0c10362103d80320040d00c20040c050310f20010b900307800f0700410a000c0c1d200030070042407840e1b5005204504180c840300305101e00c80808035075990410082200802d42191950f0304403030550f0061740d56036032901030781c82e08088240030081c0300000000c0d4168184150f07001c8074004003041c0c1000c40020802c9010401c0520541c45480041407800101301402d14514240d20003981060402240400041e0f00541c2110b81c2182d6105e015913460080d5029941c1c45806400c0c60b1030300366001c00400c0301d900b46409283c024820010700c80103000070004115211002d540d02011039000007a041c80b0440303000b0f54482c51a0301310050191098107030000781d018801103045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620589847 1250 620588597 620588641
    0x90e03090604051020010c09050f0d0312061a0d050a0b0319020d0f061a0402041d0915090a17090109090203060109080d0c02241c060e0c0c06 62
    0x741c58140b41c107062020354206040c010051042c0301d048180040840d9010156001910000142101e0003039006840b80e0140c0d000580030751102c82144003551aa07801c08166103070107040035002e402442c0c07141005450a07801041c80301c89903c1400450854180261201d100144020300c11592060580c40803140308143c50f03940355001c0795041d2040402802c00c011a0790015044401c065169120f00000b1b000e21141200c81d07950f20018122428824034102d8100601200c0540c5000d00d1b1504054524044a04401c5980105008a4a104005c0003010000c034940c1011700268074010802d280c0718202c4c0341d010744141d82501b8400c01c2d000002c404031a600101610394031551420404030100039000282124144211101c000c81d43c148104074003a0081107569402a4800c040e1042c04201c8042440a040c605000c1c600c5800c42201c0d1000e44001030301c1500108001c0817070b88404d001030b000303a52202121200140501001c511a24020403e1110031400c54405444108002a042d02018000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620591097 1250 620589847 620589859
    0x406170f0405030909041502040f0e0a0b0a060e19091e0903020d080a090204060b0a020114060915011e050301061d01091a0d02190f02060f0402010c060e03070c090e0309 74
    0x3071121885c1401c041c94200d8000c062100841880d2408001240e00640003d1114400041c042140c4010000d405902004204e010701041c0007100204102520340c0c010355044c40814200340f54a603e6881500401517903d41e9030680450b59040a14024403100c0c95907149000007401c1d1000d0700e0160300070224090740c141d005144103103012000302c98111018000200c82c40e00d4241050142c0d860740144070142034000b0030260b0b2280301c100040d00711481c0d6440b1051a0f0302c02c0781003041540d141c080c1c031940503440c04008541c0b07400a40040380c0e19484038102c210348001c10681c820003258004055416108282c4942c182e007074040e1858445906402100c60008405039828030058101c58007854080034500882c0b401c001700081da40060f60404030004104445040e0843c540c01d90100c00c00e4003a0b40140051301d10b40c00c1682034040f01000040010341486000c5401504202180d88a050b52640c100280c0ba03c1d03154620382541c60382807510a40c44410b041181107410042c0100880b01042001042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620592347 1250 620591097 620591107
    0xa0903152a02120a05070602090f120d0f0c02090c030612160315050420040b0a06030b1c05060703020a0e300f0304030303090203160315050c160221030406170f040503 73
    0x347c0c0c2e02039440301c01d810350006000104250513803100b000c9183d0320106180584a2030303250081c020610802400b03c0703801c0046102541c000368075a01c910913005407803030500350f13601e40e1020301044680e43c141c1d02421991152804810007000440c589a099910881c682060340d0b030b147e00c802c02615025140a000c1104107800c22240444800207508040c0e005403000c102841030000013103003403006134040c00109440352500c3c403113072500480417014101740210f01c9241c001180c9a680d42d4503030050510b002d15900103901304840d4044c01041001000040c0441803070004e081010381c103924400302140d40560242e040c0c80320000302196594803081400019401e0500d0354804030080e260b4660142e0f014060000c200400301007a19142000e07502130749d4030745100b0494120420441d940102600c45440c070a000340c1031140854580c40c2c10680d011504220111140184a120303659140e0030040309110000f000180282c21260011094544c03035441899541c42034580300e42d641080b6401402031700200301d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620593597 1250 620592347 620592353
    0xb04150e061918020919050108011b1202040b1303051621020607080d0203100f03021809100c030b0315010b030403050c0f03030403021b060a0903152a02120a0507 71
    0x3c09541045a1181e094a1149181d000310304400303000c1e01da403180301c0805036084000c201140a81c3e8010a0004002c000d10086c0c899502804142c3c04104000c1200d90307c0f100c0f0b03400f0303410340507034001d4006000f00603550700b003030b03049a0007034611761100311511300a003602003c81011014814040710075136012002644503080612711407400100040360300c0b040a00c12400030030710100142102c6002ca4800503500d050800c01600c030810250300c0400482c02c40c0a0a00040e2941001140d01000c030714101c2049444d0302d0141802c00d0600d080310303507200d80784c043c14480d419899000780c410a501a010303120540f12107618450100000d0184071903410041000c00c00180c86a0010880012501d080c0e40961050b0356055007150300a44065005a2040c881d007000e680e040341640f4903100c02191000c0c600342014101418000c600e10010304070018004d22030071449495044208211507004002e6002c0200a241905400100003048014810500030b880094801c60072111821016258141013001d266 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620594847 1250 620593597 620593601
    0xa0206030a1d07030c0f1401050304020604080609011e02040302010e1215070203040e010e061c020312040b0d0507020d05121b040303081504150b0c0304030b04150e0619 74
    0x1515010409541e244002024502d02250b0715500a161000d0900f003883c1d4180010241a90741021600349084042000700c501c0381545011080000c0c00c100c7d440b5681c81c00000d20074003440e8000030303150265404000d0051341c198842010303096140b040e03603002d48501405d0000c0b40143d0000078081640e60304001101c0c5485035085000201400403200796095100d4008142141954540d016900105003400032031648a422400762141d10500c40c80d510341000002c841110080711500c0d140e00c180805403e545050040c400c25908010043d5a2560f0360683e50446500080c1004034041c6070001107103116101140b180e125400550340c0604040194155541c2010064440d400c0c03180401003201211b030410020780000c500a89030a003807480c104008000403c111010584035a180004034549000390001c42c0060303ca240c0403840c0c0781c04802030403038554403843d0000b03021a80301c00c04001c10400503003100340c0d010f80c1402c010b200403e010300c132142d981c80094603924101c00000c031325181e111040e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620596097 1250 620594847 620594851
    0x120a11090a0504021c230702011a06130f0b040807050a0f0b0d0207060504030f02010b0a052d03010608010903020f0304060905060f190503160203030907030b130c0b09011b050a020603 80
    0xc5e507440c41c092200403070030b0301c03c40d1100940c01181c65203201c03202e4030044d846441994048020f0000380107000480c0d104483c2e500da55030606204110104205a6407548030094001078001401600c40094880c1814070464100741f080d0040c1d4403c0c5c4001281600301182100c007103c80c00002d41103072608210b109034140e04800301d00c4581503428015240820960f000700f50040e070180d154003e40004c5024020300f9a20302081c487c0c01040020010080303501c1e501e0403840e07504801050b03071f6040c0c280b44401c0c0303010070f80341d441e1958990709001012809840c19440309090600c2a007ca80500000584640e00c0380554804c07031f0040703518940100502d0030030b4070042c0a4400403060b80b0345004c1e04c1e001e880041c2c410030b14014000441c00700c2003007400b035890800391054410310f0009600303600e0034642e0a42d0300c203006e01000f0100802035000c0ba54000b42e0720310040071340364000d584210f41c0791982e000c485660411240c203030014140001e44e001c01d840068420100d2034019002d0300c2000d4140d02800441c1e480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620597347 1250 620596097 620596117
    0x141504093311030609090a03020d0503091504080d060806070212130306051e0a0603052d031c0617030a080601120914010e011104030609020d08120a11090a050402 71
    0x2001d020710000e5126200b2164081d182504942d2241000418012806002020713581c0c264410165000407940000f2401c241049914049603039070346541446003010f1503102c0c9180218080004d1004200303914000d03098001030300c0d0301040b0301d07982c03000708554520051b00c03607502580001c07240f40d401a480200400d001c41d0030500340000c160345c80c3d60704011203800302d078110b206402401d107035400c01c1e000b80c0046030080c103c01820704c050342c1191510364030740c1c2d815480d0b450081c034440c840c10400d0490042d03620000300610242d0b51503a24040d004005204040728140100745480f001040d843c4000d10f1071340030342d08007034021030404339003403401e6503c0c80c0060540d44c1170059040e60300210b0803080c0580d0700900c0c480d0080403540114501e00509446401c84500b00b80d90404060045841001c01030b00c080f07d0b04814040f074800220700102e091500c8051015046440010715058500c181100103801010021400c000385d650111032003005029101c2929886a2002c00802c100c1c44c05402a1000350380d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620598597 1250 620597347 620597423
    0x1909050115030924021306050a0e01030b010f3e0609060c03040b1008010e0309030601151b03030e0d08010509150603270d1707050322031214150409 65
    0x2d44940e4016010031b10343c0c045000a400082c600060642c44440012000310a0800317000200329034002805071498698940c0800130a151803401d01424080b141c448084840d060180380c18070f842d01d0b8101005001c0e0f40d0040392040720302066a04500044440c86440a03942090540d144d60b0303284441010054403003590b00e090504089441e50081c45800c40d1704410f070008550700c4c03055900341414508140c7c001e410040050b0401e0a8198000040c20b0400980358005a140303409480c0036001031990003140d00c2203105041008020540162859043e0350049505140b1a40c03040041020443d02464540e0801c40606c0400c412600520b0b00e15082007000c0050800246800d400c0c0e450b054170007082c6800989407040d1840554140030007a60441c1c07c80c0740c41340c9103103862901d03160f404021030303e0050344500c29210038081c507105860f00024444a101300707010740400344c0c0119a040c0002d43d00480010441c0c604240f00d480c00d40719014185601c101e0b010b0010140760468160b8803080790425030166 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620599847 1250 620598597 620598607
    0x90b010203130e091e0c040207020109030b1e010909021003020310080f07061710030f02040209180103060513020a03023001020a090f081b190905011503092402 70
    0x2409560360100a8008100e070748000d441c1001130b1525100b00740303c607410030100d603c0030310150403c00703d890f48400000343d40240e915105480100c6100115900241582450b030041c01100840036800400070799210a92a5440c2d0722203500f50100e502d051030095202260030140700c03080340680c000c2c56008007000f0326664061f1380c1d141103e0510100243c0340125400400040c08029004000300d0013080c45515000d4a81c60480e07090000c985240c0806803440201035051000c540e980c0c6c046405100014000246100040c106c80321004020300049601038144070004146482d094040310899800400d00800e4a01c4c64081c000c458002101c0948007460300308460b10300c124502c02d04000c0e40c1e400000160740d4a031303d0000400f05a1250000388521b00000410000c80800240c0a40c0405200a02420121860002130002c0c10010407803910b00c1001c020000f002c800b00e601c1281280e9804900425911110070203c003100c00c4c0305001050f076070215058020080c20620105146112301000510304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620601097 1250 620599847 620599867
    0x4120f0215150a090219021f020d020421021305070c1707050f0d080f04320f0703030315080a032006040c14120d0e1809030406091e090b010203 63
    0x142c3d031680104802c40e80000d1040c100f42c0b40404000c140307007a10b1026001e00c056406d40d000c101c004c503500203400c0c6c58011034102c00c0050654102e0340144040d40000c641c098003005080130008600c00142d200c0c44110103615100444d0b802107521800d041c0d500c16a900005035100f440700030196041c01588901408940b0001d2402c02c8204152980c0000030800d0840e800720040c41d541d0700410b030100041d150f2043c0701c00100d003041c02900c14204115880c11001c0c01c480850411035030401c001500f80328044588141c000c01003020810b4034002e503000d10002c60f400c0705c0100900356038814602d4903441040e40e000440c5c03080d0300e1051789407420465402e80d0485800070524201e4141c40030340780c540205200704009890015000021003054949600c217124030302d801030304d078445580b203032081c00004036282c01741c1e50701d0204540100116042c80007490902640c050f0307981d00540070b8600810306440000c280c02c48a107160022a82401c4003d00d02541450101c40141c600301d0455415440184010249 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620602347 1250 620601097 620601109
    0x4212031704060203041e0b0a0902030114010f06180f0501081b030a05013b1003080706050907050d08030a09060207080a031418120a18080604120f021515 67
    0x6600842c4050703102e082508000c00364100006541210711031121b11400001c0c14000c403a41d001c00c1032070001859000c103002003800f40010070300c0848185541c400214110620b14488402c0c0c2c0c000748e1358075103030000900045c00b800046011b001d050080000003004158801c111107a440725102816140000410407403040c00d8100b1b4034042c81503030300d8000600c0250303e65044503500d880385103201a0b5082c00525030700c3c079041c610780213072000000d9440090b00d01e01412035030710000c640c40802c5559540f40341c1415402010284da1a000500403501c0001d8030740340404800895a8000d500140f4581301c01c800200103001d0280100c0b031594003404440c0c0464254400341c190040381341c8003c01c000c48801d550030003800d0004c0011481b99044a58a996043c001444406802003040700c1c0369a64010701c021380350709060302c000b2890341901d05404a011040031843c42d00803445602e00c1540701e610780406840c4180705481d60001a0310100c41081860840c100290b0420b06407900848110141700120f12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620603597 1250 620602347 620602351
    0x301030303061a030f04060b031e060a06080607020d0f210e061b070204111909030b160f210f02091c02180c0c0142120317 54
    0xc0070940c0d80d58100680d01200030707403040010500880c20f18510f00541051071203140607001400c42c3da910b1340324a145d40c50801c44955010401810381aa01e03141000280e03864008844803607045090000000f0b28190001d00746004003d650041c045812440d1811248000011011b0042007c5180b0140059811040d060030600044101290012000e201c003480e00d0005400115901c10203080440d52007580d0003504c81d80d070ba0440740459081440c2002170114001d0b0ba100c0c2c0342820b400e441005899401c90541021603128192410307080c5e40380c2240c01c0708038020421900201e41403209006049200f6030044010308445007129004010002c4101c04403149242044640341d40042d41010f1460700d141010300300710707041200c0c014200c07990740801c1110124000300440250540d001c1288024105c059800844004000308187e003a441c0300303801c1c0d8003000664803040c1004104400e05180359400e280801541407040307100f1261030036a0141c0552840c005c143c04102e00024440510440c0d00d00303080c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620604847 1250 620603597 620603603
    0x2010e06181c03030b01020606060d1e050a090c0806070f030504051006080c19080a02040b0a0e0405101416200313090e0607090302090406110a030c03050601020714060a02070b030103 80
    0x80b40390070140307000780c101c8902c0f0840505540c0410100b06d519914402155400c800022000c20403050b4030303100d640c1e401c0007500200101c5d410403003002041080c960018661074000c06844481954415886031500b0040e606500041c0e522890125028001e400c920781051269007201e4220100714118011202260013101150300410000001480c102d060020ba030b00c0131107407d85090345480b0f40d01d03903241200703030b4000c0c082c5484050003520f560301d44188500070503541814070031a18043c50720039110444214480600c078508114099048000301559100f502d0200b0f00c0903014000c01410b0326140f450640760070390150183c0c41e500f0140340c11f201800002001500d4181014108880c0d817054448044000d942c6d0b9000c0c0c8104044142d1122884044903010740d100d103180d4807141011406003100e82e104110040001400d110541d5044e880698114241e60341040300d51241001262609a00e11a40e00c1c130302d42c19000d0707401c40d2922100500d40340c0001e0040f14000c50361080c11003140c1d04240c0c026 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620606097 1250 620604847 620604889
    0x30204020c0d1404260c180f130f021e0612010e06010c050d0f09230f150a1b0b0903070c06050a091e0915050a08060402010e0618 57
    0x252890704040303002c0c4568100f8200a00305800c0c400146001c6039150703c000541503a0004101035104240200c0c0c03000c40c40909484c1c21402541251125188140e40405561000c00001151003052180100f16150300031043c0b07811340101c2c1c003000712032448400020003000b010800c81c0281d40e80c1c000105403107264000d00744901c2d0325019801510043c02801941440704148207000040d50200344d03801381c500d0a003061500d81d51342a0040740e0b0740140760084e80c800f07400c01c03007203c8200d412416000c0f0403000c12282100310301404000d008140c41012101c4010300c0c400d010100100d0701550520039400c800325142c42c1c044081da25403c4005100b84c503942041e41000400038140040804900c000d031025007001407030945944c0c00104050001d10800007a540440c80b40103007521610440001400240400d000e045403902080c5a020002c2c82070368400d5102c044c00040715040420120300c5550161642d40318484060127005440e806005200e8400d0440c0742807020350740e60540060b803440c00031864 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620607347 1250 620606097 620606113
    0x816030e120a140303040b01061d040c031d0c0109260303010f060f0201140f0a020d05190e28020a090606120501060e0a060518061914030f0112020a030204020c 70
    0x3000c0840b50038107001c06680e820801c108404917426111f00c50440394035142000011486010b6620345041c05050907a005040c00d0507403944640c544c000c40050302c1e201c0b403000d440c40d400c0d200941d69211081c0446010903030000c41009000b0030300389000c1c615410300340414808510344040c103007158800d0700f2054100f4903506050090f0340c3e002405880e440e0850008100030760034589178200301d00c80140a89035400210000800c0c00000d5015a548416240c80134031082c02d00060003240c5007603d1018103056807074222201044640010402d80355005500da144855045600002c1d000308100c10a03030b0080a264800030388044540726400c024501030362034281e80c03005041c01000b134407810b9018104001c03404a1071406035481940c4a0202c800034145541c0d250600030317503000c80c6070394164501d034408400b1814424485010340b40d15405507031603440c06200201d5542c88800ca010a907019074466200000601800c0000d50981c02c915000400e1154441d070740340c0c009002e0344e110b41420381c102d4120f00c030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620608597 1250 620607347 620607353
    0xf1e0c130b0d0606091a0306150c0105150103140c0d0914070609050a03020303090108040c0f0605030103052815181b05030c012106051005070302070f030816030e120a 73
    0x21a0101500440c17500100b65450701311440c801649240c17812241c0314002001c078006644000c1542c02c5041b01c080c1e5141c40c1c02055004900030901210b000448801120130940650320900c204218400466104241034171030480441c070035049407408401c42030396000040080b0f0846444d05215103416002403608030308001c5c0050114640f548001d00401c226001800180e90102c00e440c1651801c0c68404404d58940c01d101520188551091403261654140030074825445001541070b42d01981c11601410210b0a0204150803c40e100303201140742e0250300c6000900303180c28141030440d01d003008240f4651000242d421029400c2040b11150b120810709925250544100c000801044000e01004001840081d140d0310786080d2600328203903e1701904018007025407040c40a0310000c0c0c0b00283d03002c64100090f007903602c1264240c001d0b01c00d90600140c1028000707000000d480d44001d809083c040107807292603181b00f841174203c00f80b2041c2000301e01d5544440d07903450401e5803404c2c0100103070a00c41c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620609847 1250 620608597 620608601
    0x1c05212e090b030c0a06050a140c0c0f0604150516241a010f030b06131511070305070b0f0d0527490c02090f1e0c130b0d 53
    0x20340360ba00981080d6801c030710564546400c142152681d04120355100741000c0205d0f50175000000021811002103105000741400099010040d041943c03240082d5011030100f01d0207006900c19401050301c410112842580b00d0000303032261074490a0380307401003c010ba94a000c400441074800040c58043c0b810003038104060301810141040420f0112070304030500000801890360040782c1004d1540f1482d60b010541c449408541d984941822180702c0c0f261540380001d06107140209200002d4043e105150725850045151400c980d405001008800d282c40c0c20218940c106204807090f42c00305104110745c02d0702c0c600465228811010b0302480c045540610100c1d03003400380c1014006a401201c80c80d4045500d40f001903682170001120105c0c240c4d40c842d0725104842c0e501d0a110b48042d02c0c100c1003546580140b85800024401c0b2072809195440040d8002000e83c100c503146021a8101550b05010842c0161107030400d03a003c400307502d846800aa6000b40a0007940100200b92001070343e042901898 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620611097 1250 620609847 620609861
    0x140c01290402070302062802030a0203040209010f12060b0f091008060106090b0d0b0429032b08040302010e120c07060305040203030409020c010f0e1c05212e09 70
    0x1c540450401100740c80c02982d81d10010f00442004400c107a003136582d480100f5540c8800c26840391305640d00c4c90001e514002070341050781c0407801024407800104d5050003142d218010f0711181e001440100c2c0340b946419024001e503821183c3c103c204206105902d883e2406460710a4000310110b246242c0741a850790700c2c010701688030100700a003416041c8240c0b44603c084400200c910080400c08001c040002401002d000c1c8000f140c40c10f07901c0c81100d441ca01868403100c42d8208501340c8000c504400f0000110008800c0100c803000c5445002d501002d000b0310089400ca03020b88000103c0d200c0040e01c6a2030000b2a040c1021206004100e030030b01c008041103100003418840c501441603080650100b6500c3c001c60181e03040e103e0b0042052852030000b507006140c0079090a00900000102c550f000e912940c0c0c01000d80102c040e0b400b00c00240b030780100220f9801201d00340100e0703040500c03001d00d5441c0c00001342c00c080c0181c00110a4401280040000790642041208409441e40c5409007410032506a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620612347 1250 620611097 620611099
    0x302032101080a080702030f03030f0106030c180611100c180504140105060f0c011104050102010b010306030201090b0a05070537020d030f0c051006091a10140c0129 72
    0x803000051042c034401148082040340d210241d01e403180d95501c002410500c860b80b035403c00f844044104158402d410502a0480d50207072001c200500c036001d000c581403a0041e1159070705010502040207400d20031282c119040e08460706172038403803c0c41c40c5203c003981c4001da2160001462007a43d054250440590640200740844003001000401130640c84824014810f4920521011070007102c848004400c5a494418600c005c000d02d0301e954407140390790741040c003400b40107619100c550141c039400f9100c3c0e5400c3e02d0301619102c001a260845020701540140f50800030401d05004440c0090790400281c5001104401c00140b030a10a030a210050760404000307001c1c01c03aa18800314050b031039103c405905190140340c13071501d0001d480000e0b108111984001042803040c01e0103005101d596902c03403011795103852014090001c0c408100400c1c64400c00802c3c1e88405c01c8050741c0404d42c0280e072404035402000701c4042c24040745ea1081d90841716421065050101007081c80c0205043c4c2e280e070040340d400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620613597 1250 620612347 620612407
    0xe010306120b0109090201020a1202031b06060d0204180f110415060c0b040f050d020f0c0609030c04050a0908040e01030201120216030305061333080a0609020406030807030203 77
    0x2a03034507110120a41031113004003040d43d0314424000c0d0391081c03001000040c0c2041c004030f10225034807002176880c5d2004c1e1031400c24000320b6040f0b03800b40c100401d0040c041c3c17000410950100b0010340821004101810ba04441c02e428044013100240e28409901c181a02030542d40341c04140d01c105000544641015000c1c00490740081030000540007007245000d1504604400341a6503646000c0c8139941001c0400f0342280b01e00ca01a00b84070340e000a05c64201038520066658019484040c0100340c052200c115a041d08408508412801c0546c07046038402007500f0045a02081d9459020040c4d025030800103d00c0300000040c001d558100394400c145022a100c00c503e0b03d01c0d0b0080214100840c40c074005c041645034800b051080d912050b44000c500b845920030804500c021101005501d00d084210701280c0e8002c019015921801c092141101e03d184040d049150781591203e000303285090f412a80329a0780c1c40c012000c108820040c064541c402d030000c60f42d8085004403a51010091513242c04098 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620614847 1250 620613597 620613629
    0x1091a1e040503100218060d0c2d0327030c110d0b010e270c1504050102031e040b180f0f030d0f0c0213050402091821190e010306 57
    0xc0c50018000c81001e04c8a030006131a444440140c180800200729450750160010648454480301351b0f0090182940340c3d1180b0f03a007406521100c4014504012030380b8851440c6143c0c155000303001341c00040e1440c0c000000d9001c4e84920382c940c801d021140c8281640006c1e08135040d6800c0240141d416802000c0850324120b11408580e10b42180d034105000702d0507640503c201050010300d105548151400058405405106000308070503518550400040d00c540566400e030940346003c1c00446040d504107a0103185404003140302c500c910001c41d002100501401c00001400d484244054130341110402980340d050b0a1003010000701010104c40303103104030246c00144100396400540140d5010b46820070382030b0711440f2542601d00c44040c0308080d4000121090240c1c0300c0404e584070b148501e10071038030b40502e0746a1030058558040c150111440070b60001d0740314441c568110b80117490180a402c0c256286c4010500c2c094603280f010b52074003000c0f0710780e8803900c022582c04d4060100503140300010a1119 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620616097 1250 620614847 620614849
    0x203060a0510030201110a0c0311040b0616080903190803012409051210050a020903120a121d030a020706120e1f021e040801050610020c010e01091a1e0405 68
    0x4040c0503c0f0003070510041c55802c00d82c8031000e010750a545900196503865807545c034203103a01040f002c4031140c0e10031071500010740f0051a02e48150742c0c03c1408403070a640302107401d650b541c801e0380c020800d880d454460256004042600580601080342c803660030347d512949001d900001c940229884052101e00700010251404d91081d03100c01201c0040318450243e0f4080009207042200e0005202000380c00c101c2001010000c40e0014014210141d00300c40c1d1901c16014560b80c24010a141e50340000c41d05400d04011444581022401004401e8000c0b02d070510f0388022440c5600032500d0001503000544104002c6c0e03041a16800c0c5803da1007000c0c040c0c01540e0454580700c0510303c5100304014002059519003c0a590507140580d410540134018284911903005450708140f0486d402923003004000341c95030030034180184080c881c1c0d40041950401e050010760704200c058004904012825100041e10344000da4400d90300c03e0214188c0d83d465815006410010034000d02c40030045100700010005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620617347 1250 620616097 620616121
    0x9010204270522031d04090f020909061315020d020a020f01050c0f1b1006032a030c0e090c0a09090b0906010305030906071a0103031d150315030a050d0c0203060a05 72
    0x10050340341c9800c201c1c0e41725403041d441040003e40324151b000f601c1e0040400070040c001c0b25940c911802282e004107942d40d21401d01b40d44400c11221341c40954140b1000320001601d002c001060901000310250a00c4100707502c0c01d040740c10403090480180d2001007180ca40c05400c0c41610340040e0800c04131483d00414440e40c940c00c4c41404d00000c0404034104000c40301840c184003c0c41c03031142215044c4807069603424500b441d62003e40050141c1041485040c0d41d500c0312900140449130310104441c4003034503004c40c05072051002070003510385001c0d401251025581d4120042c2c00f0300085080020f0b10300c4503080c030602c1c110004029a032150710103070060011541c004252506880112000c03642c81501e8a0312021054842c002c158440c290400040101600131000c003a1400051001901c41c0c5012020040320009902801e00380341c0d000c2011442502c1c411021044035a406011240c1c2e04000d9658945801c003c1440103000600b080d605404601d000d0040300d41022641109000b541400344e66902 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620618597 1250 620617347 620617411
    0xf040902061b0f070e040b070807090504020d0212090105090d0c0503160804080115051003140106140f03010308040302010e010809060c0723070521030304060203090102042705 77
    0x1080002c03105140c10301c10204194541c00e00b500c001d64806a94a4041c081e08510990702200d0450303400000a486610461081c0c0c03103003007070350b8465201d1458142030200941c094140c5888442d000c111500c034840c0410070640c040e140703800000809140c052046130422203150041820400901c08010200e4000801d80b5094000140344904001e520300d04900b16100e550301542155090070090a01c0f40d0100e200e03482280d00584d45003c03840300d480c200710101c542e54400e05040229460060142c640b103100d00b51900d40f07000c14114a403450341d074500652500242c2c000c82c2c08080018051045590015000103000b90070f00304130315581480030b0030a0312000028031018a10401007445400e00c80c006900703103410030031048900c424154040b1f403280c603018540030b540d00a48580306650240c03215444a03415400464018604545595460710060b41c00548a116250b400f4800844e00b00080b898451a6000c01c0410803100403149070000f040d90401040301c1210342d00e0140340c00180c0c0d543e00100d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620619847 1250 620618597 620618617
    0xd030c120201060312051312020d110303250510060b0307080c1612090e0106320f1b010b0105030c03040c0306180201030f0e030901180503011404020f04090206 70
    0x384415020100300d004100590001d482600740245501c0f1458002c401801090305039820640c0180e1100c030000701d03c1200c950029003203441d84000201103012004c0e2070040e06001000d40e4a880128100b20401c00500d50311000081240600c1004202d420441400c10010800b428001d42e4602504041c3d1400010b000d1001c0c85200c1e000511500d104401b2144100078420080f0721141e032600703242c1e03000a1286009400701380e007034001160840485010f00e049030a640d842d801d1900055106044511404a035009203504820545000f81c1c01c11018000140403056066101d02a03d03803001d44400017640c461078181d1410f840c0b08040d9074000104c80e0300158401d18280e50783c5451170170902c0d8606c60750020307000c01e00c4d200ca11210000d0034400703042c0c014000d0f80c0c04e01c0744505958140c41151510302108402da40704020051055001d9510b081c5540700c0794501c104031503500c001082c00c1d1007049611803c9541800f08000031450a060703000045001500c04003c191580d0340445c209114400c480 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620621097 1250 620619847 620619863
    0xf07050418390302042a0e0a1d07020d0903020f0d03050c0d2309090402010c0f06020c070603060b0a080c180d080706140c040b21090a0506060d030c 65
    0x410240016105903000c103100044400300d441c86540180007030b070007040c0000c0344243e04000c04042c0c4069641c85420100f20084241041c000030603c1c1910707004480c02c0c0050b0003002038940020b207451540d0300c180340c000752011018580e00d0031a1000741011001e140400601c20f0000741407000d40c0b82d203523a03010010340c151124101c90805040584072030046001c254464840e0071803c9512641c003910b48000700c0c0750302000c644600240042c0c40309900902e150942c1007000000001c3c0036602c1603010041640c003515803400c451802c1d4440d882030380e00030a6580c41d160300162041040c04e525114040c000e20224400609000940c000100142405805411080c1d0301040f420f0b00c1941c02d21014070403190007000c014400c0c0d0245011030058200c80c00a40d1564944200c0e2080891190041131041c4000070041b40380034100303d401c41440e00200460314440e841d4400c0750031311070b000e04a0079000f580400c00030012000c0928003549080d0000b80114054103c0022500010382c01080c103900d40e0354803000b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620622347 1250 620621097 620621123
    0x203010b010504150518061801020c0105120a0f0b0d12090605030c0307030f0b031006030b1003050613051c05190212040b180a1d0618070305060d020901080f07050418 73
    0x90a06c0404182c00c09621100c001001503101d50104c03c01c031102c050070307000c0c1c50810004400541d914010b09080ca122000030100148920642d07074041840c0c10342c011000100940c3c9003012545481da59601142c1560212a0104c407007600420228000c0c50f2380d01d006865450a80e500d075445000242c40c4606154662018940f888120b030012a0f55000180403285640c40b44440c03503002e049030307100540702c0c175003581d011a80301c00307902d1843e00680350010300500c8251030b140c5041120103245281654140140d02c03002810100f4000110703014046a916281c94228130104110591110152101554010034001c0e140b03d100030141d4046a0039043c05a49a042c0d940a07901602c60303007400c0640c880481c0c48003081814940c400c03482c030414164070030482c940d078000a200300c04610070090a60b9a140400140102e4070a412140d4000805041048044929400b084440c4000c0e080700f100c0d0713004190300569400081140c0401408116424424030700005102e079480c107080780015100e0b13604108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620623597 1250 620622347 620622367
    0x2b090306051306150f080d170c0d020406050414041407050901050c030a0224060901180b300601030807142b030c05090a141309050a0203010b0105041505 67
    0x441c2d0002641242c01400440f01c000c039a002c651a13680280d51a60b022000046514440020319042c400a075440c2d03d081009042c00011000400030079850304000208203220400e4402d0000c1d0004042c80c0d210b142e103c80c00d190301080309000e65004a03005516215030720318034034140701d0784980111450800c07641c0d03072907000012030f4144034101703402c04148400122103611030f5002618400d9408075841d203809041d60121200d03c410f40603104564000e18550061100101401031440001a100740010b04c00180c0404a10704400396041103444c100904c000c820b000a1414500700030b81400b40c046c107807542c11642c0701c078101d010307507000540328410038068588400f40401141240e0441401080d050300d09156441a04550400c5007000290801c40d11000761406130090b141c004000510b40b50009090400c20300e50070350201c4070907601180f040c8207401c0d212520b00c03a046040c0e024001900451701340380140350035200e01001e21810001c003040104100071410003010f0401c4aa442d0080c0d558580710 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620624847 1250 620623597 620623621
    0x809011811011b050607050307110a0605071d130e0102040f030c051e0918010f020a031a090708040816170c0c040c170606070606082b09030605 63
    0x1610218225024105038207120115141800040d0260303160305294003000c0500180b5090641d008146a0007140810003060080d40607503481802c5107031840b000d0382c80c0200245841030300300042c0c81485d6990140031b9980d80c0114088000941e44c5203c2c040f25803c0c40100360154461600d1100140e910020b10f44103600a4044400a00b000e5400200c0316440e410058000a440d00c10648189c1c050a0180c180b004066a2148030f12401080c03085981d6a01007885201c0d0307420791603801195a54103032811406490710103048164910351700001c003080030704800d00c94620742000a52103085004100070f88141e100034411b41c443e0340495140d4499503403030409a042c6a0000d8002c00d10000618030082403900c103c0900200e100b00c0d07040700c10503140542400101c91081048100066588001007450094403c0b56600b200c0090b2042c0d250184036100e1400711489e90b00f1102d000e802202100d0601454500c03c4440142c034840320166402d4440e101415000d000e102c000c1070300b51280e0000b44031440039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620626097 1250 620624847 620624861
    0xb090d2003120c01150e07110f010501080c12010e0a03050c07230f190b07140706031b02010b011b0f1a0108011409120906160606180516080901 63
    0x1d4100c84140b5018411002c40d50415224400690319280c455020801501401011950310314070300040307034507001400c0300c038411200e080d0103040c8505201000000c0003489034500a284900c0a4606040000f0820250b601000300c0c8020a070b04080d5590310f1540003141201e0850780c5400c00c42d5941c05040903190500410313034006c074188008100c02c06000b010102c0d0903054200100c40107a01070300c0104c20081c000640510240c42c9004e601d6041c40090310303510007000e54034060418002080400301083d4941141500418002600e0304502d40880040c1481001c400c0c0c141c0c00240601d91004000810b1007100d0303041d42c1442c44004003001e007404410700c06000c145411020095503460032043d0840078400070721030284c4961804034041e00300a25921520f00030200078010700250040218103150356084556510307032142040065403100f14505010030f80440c420080420443c1c07501584580041d40c5c524000034446c1800108201c0310081d0380c0c980c07400d807500e01301000161603800800d0b00419507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620627347 1250 620626097 620626099
    0x9020d0b040c140910092c2d1b01140a08010f080a030203070f051e070f0f0311100513080f101b0f120615090b090d20 52
    0xa00824042482120240c4200783c0f51a0391802540820344024030a803900101c965401d80001d1040a00102201c0d13089180000d074444140c0600c1580034001001d105548203564247d81c0c4800301c0400e281403007140510202c81c9001e0b8000000c1c0b205121580c8501c0521540c6d4a10740856009099a0307028000d024049100d0381c05058a40c0d61040340a08800310030300403c280c44402c240c00107100480010341c0025250701d5405542001300c10341e10401080d41c4001f0464141c01040e20001c210401c16100c110071421074002005a03034a0000360f00600483d540050901000d66602840443e40a2444188044080d0340b00c05035260000400c4a984c0100482c410f00d2030300f580000643c5401c0060148600041c1d1800c3e41c0c03140c040d021040c030468006500d200500d800344001d58000c03e01551b160b8103403840030309264202911401e00b2404940c19608a440041c1502d0302824202e6440749102d00038004403168a840d10941c04009511540c40f0f0b540100403c0070050000d803089510b4010102043c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620628597 1250 620627347 620627363
    0xa050417010906060e060a12080702030d0f030e01050601300f0204090b0607020d020607060204080d08220b01091e06080d120b100516051606020d0903120309020d 71
    0x88194403003400b0346407009041d01e0040c203012001c141d00114031040360017440002c0c000b003d00c605d45100300d65251100f14040c1d80c1c0c034a0901415001d42c809000c0906c052210341c3c6d40c0c8511078001c1e107025080324020b040c40041d9a140804104031070341c002c0c10891503c2d034004203007001c3c04000035410f09a600e610610102440c00c143c414140a096030b00a4025210b12280c01c1c000c0750480b1050160381c0c00380340e10180d0b02c10760131007130100541481c02c008d100d6103005210261902c1d4668110f1890b24440381c900c0c50000ea290f80820086100d0780484850b200c003004c3c064100341195844400c0c0582041c006c0041956036813134107504072101120b07000d800d1020400c05100c5141e07214001d60301d940300c01102d000801c040e60007a10302030075a44180940c2d001c0007003104954403c90042145d0300d41003540c144025082c5800c10380003040e81004890b00d0340ca0030340e08410841d414004024140903000c3c01800500440190900002d11510841d031012040c6190020300c480207030001800003e14200b000c0e156071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620629847 1250 620628597 620628629
    0x10e010c020606180c03041205041505040f080a02030c1215130b070c171e190306080102070f0f0203070b0c0114130f02091b0c07080f0106050306010b0a0504 69
    0x75008a541403003400115405000c003680c102e00403110807021030b03100010031402c00c0014002903186417074030440001440c10380d0502e0b455140d034034040d4000303050040c007252000c6020003090208800290280c184040a00700144191780883d584207800007415100d040120581c12004c4410441c88070301d00f0391a00100390700c1c04d1010000b00c0b40050703030605a032000b4110000400b1715009040041009174002c1c601034650307902540c41090394004075034444c3c10744010444100072540b61005070044c20400f24a112090b031b001f20010b4126240c50740b250807240d006004901c085044608482c250542003103180102e14000d00c0002c0c20b02d4000e4220020403213000c5014504000c055000380d095407020724083c000c0382c95072904400800c1d42c07410001c2140c034081c0300d58130060901c2072110b034000140340c00e0000c030403030b42c0c0004003d581c0055045042d07641c01000c08104880e8108050403895000f00000c00c09181403901003529000140a5480c0c3c1800011755610111300c5130080b1802840308005681d410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620631097 1250 620629847 620629871
    0x13060e1005060906010c03020706050703052704050f07050418060b03040f03030608070506041e03050111120f040816030e041401080c01080702030912100903051b0309010c14010e01 79
    0x40c9000c2e5030441c0030300c10641c0026a40d500039103400c00b03581d402d034000705011868500116183d6010074411020800301740121428200c1d000c000d142e803038200e40c0036581b00030f408406100c201c801c02000b244104101509114890390000121016200d5010780e00100b102d034956100040d112541c0050745000d000003c20013030011080d060180d4900ca540c00303205040d0349060a0350b446515009040c2d12100801081141d444c0b0784540d07601121400c107481400e95500c2d1146421600003c81c0024419030026509254480c000100d0764060420300034004071b81080d844002d03843c000d241418500c014951480d109140c0035007880003040b00c009000384000e011401503040703120700a115510140c40307040307c404819070264000c00e114524a6005504000b9800200610034482043e502e00368002c3d0b194000300c072407980c022007078014040d445180e030f84c2c4a0b03404148920002c007101100780f50003e00402c4040e170f80c000406d48040da0040e015002010f880000b40c4e0051942607107100442d0310b441c81031601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620632347 1250 620631097 620631101
    0x30a02091f0b03010e07081e180c010306080d030207032a0b0a0902300a0602190f0c080906090409030f031b140c0a0b010b03010f1d13060e10 62
    0xc8404038440350801d19a00e42102280e40004c2c05900e10590f040700000b00303400d100d002ca45074005007a44a10700094014028502140e8003580c0100b440407494030f13100b0f002001000049160f083c01e180c01c200c1e0034035054081d9159800c2540304400c15400089000606201c1c05912400710f20320103440a20b11128401500d01d0400400111901e42d440800030308661181e2184240803134003c1c10b401440012104001c2d5048034084025220200340480c0070308090081110382c90341446040010fa030750f01c0401c0d00101002c40e070740659080090800d10400c5490740804e0524100e41e002c0e02d1292180b10b81c00000303a5600a143c58250402d28100c0c0c2c20041c190701c5805003440c0040d980782040002307a00c580080d086019023103001c000ca55a01001d942010f8508c009040310000103041e9880c807403003540d4043d102103080e8003400b0807400210040c090704008116000c018148511650104c989006101000400082c114409152546401018071210350032826004006505035107100c8440629400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620633597 1250 620632347 620632381
    0x30703020c1006050f121f0b0315091b01121419021e0c030c072c011511010b03100c1205060603061909180614060618030a0209 56
    0x4542c0b0500c00c0c500d03065211807040e1010340300041c04019a405800303061050548250075174203010f01c07514080780745801d070054201c00d40c40740690700402c0040c100c070109840c014100d441360700c2c0301c0300540034071030781942c0040c1c1d6080078580c01c17442c031058800c03503801038900c4410708410819007428a2100e4127005c400e10600361061100400303803c03148000000c540b0480c083c0c0c149000b82401038005014411100e1006021a80700d4201101e1610a1715201203080000c16440780a00d040c0500012050384810a8030b48015171111034002c19640c034003160350480b841d0340000030782803110038845a101c031842900812034540000e411035500885100d1004014081d5036003a000007240380d42c21000d141107078050301d40902d500034011030075911194100401900c407e40605900b403c5501c0004642c90240240e43c41c8401d0713082e03602e60324102400d00c00c081d180c500c1d152448900400003000202e0b55600103440032030b0400c52800103c90502030101e85041c8807104040d41c00403503101048903500d5810a424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620634847 1250 620633597 620633617
    0xe03190302060a09150e0106050d050a0b130c0e130501060305030c0d0201090b0a150e010801060e150d0b100906240206010e1302130e01051f0803040504110f03070302 73
    0x55040e9a80c0380d010f00c121084244002c16181001c400340c030340c001c0315811a907000e8404000000d4016905d00000b0500c1000c010b00700d64a802c905081e00602018040099000041101c83d2035074076102d40d41c1c100e80500e5400f81c15088002900030841d10005c0c0c194400019510800801520f03480341015982c9801502c9101503920070f1901d0183c0d241d206002c1c1d0615a17600c0f03503448030a44c5820401901a000300c07030300d2003110401441c0001d0046d05c2c0c504502e000b008503500000d0700d2800e103140403242c0d02c1e0041c01c10184201d14210703c1d80b03588035483c03c4c414a68000004544a48a0711042c10201420741d028684841c1046e03004038920b000040b040030200204170800b000301c00c00c10030a0303071518800d1080b03024041114001404115000709820304031440105042c40e880d02900c000800c80f074140c3c09461850703641d00100302621140e02407450303000001e43c204006145ca02864a0741c1c0344a580180c50180342c80c0c140d074070300307003001b12080ea50503030100c4203915240d203805040200250040c0740e8031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620636097 1250 620634847 620634853
    0x13050414011a0c0616032702010e04020903031204050c030a06060807090629090d0b0604050901051b0c03190819061226030c04171b100e03190302 64
    0x52003450007014212020b14404001510645d03545640a90303031180c400c0d1280092503100d00786103a010310004224050183e80050080603007600340001804d01014000da1801144104501203407a500001030300d98008040da001401961103207015030501e4408000107416200e100456410021250032520580f02c0c01030071685540e940b600340c2419500380380300395648104200c010340790802d5030446150344043c60200c0d09140480c43c00104d20086070240d42a1580100d12062101525040c080c29410114250007408a410a40e40264100101c00c0d90181c1450f00090b1918440d84203105403040268400311100c2e580007200300c00750081a00311403403c901d118030321410100c0c83c21481080141e07401d014203000341e881159107050020744005400d10710001c1100111030001e541030700035482644004069500d0f41d14221464028604014641e951500b0600340c12000342c04400303161000c003800700c64803040031154250940c4d00f03600340406282c0601801401e001712018012200b00c00901c260f0071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620637347 1250 620636097 620636129
    0x30712050a1a150a1805100306050301051f05061606060605120a05150f0613061e020f03160c030b160825080a0f060909060c020d050f1305041401 64
    0x410049090500d0b10000c40c2005010b000700710380c82003100c42014150014661245911b03140080c035034044a85115001070380b40c803800d1000e400c080c081d80d60802020019002840407041d1012044101c0c1d00805020741b102250010500c80d5141c80180c101d40c004408000341a00d03401c0061066010b561201c1e4100007200c04a0382440c0c080c80350a11640180050041744e500d0030003000036a090721414168421020700400d0b20010b59107003083d00402046e10381c03011182224044540c88942414150305640000080c1c40743c2c41d0002c02120b0446060004060700e910300c03440c1107100d511681c2c0002e44450f0748402002216410f0343c02e882a469000c0d20340782a02e0b81e400c685108003d00c000320101111000c3e20000c11014028020550080d005800201d880210040003408482c41580002007881d1600700b08000d0040d903202e1100710052900c003400d01c402c070421001e842c52068204030309801c10002401c41c884042c1e4200c035405440010000d00c03035820348094820000d030003809600c0b180152042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620638597 1250 620637347 620637349
    0x60b0f04020d0614120606090622090203190b0a020708040b07030306030b0c03041119051e10030e030324090103030309110402090f010813080417070801110f030712050a1a 75
    0x4580c000d4607005d0040c03006607030700341c103104036400003915264110b103003140460314489005600612885298000103078009403801014903100d91131441c0121031980c00d50a00100d41c10300c6070b49501801c026000341e556040f91402d1a002d1007a41d0041c01481e20100c0d00404140d4542c01c05002c580c01007800100c1030701e4400c145481072000342d030010074240d0a144910703003d040002e1080390365890000c1070307500580e88001142c00050400d40c0f42ca500d103100e0b4001d400030b1030000101b0818412a180c01c10503640e550a141d07640348009005940307044100c81a84500c290b10380d031040708420015060b04082d50352840d0143c0038041032141106c800d20001d043c4141e40c1094404d5401c074500051448861500050042d00d807a00003804401d044c100c01460603000c01c80f0000200000c1050340b1100010480030041181404c281e41c22108683c2d060401c1036205c404802c082c5c4148400c041000d1740d89880304801500d10804624181c180d40707080808105405015500c5450414070950060a10350603600c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620639847 1250 620638597 620638609
    0x507020102091f031d0102120f010530010f0c020c01030902030712020d080304050d18060203032409150a091515270f0806090703060b0f04020d0614 65
    0xc1c5504801030555008660f0b0700c001c1407094480607410005000d030410001c17180440d50111110680da90001004281d030f040704080580e001e0001200302c070b900d504100c0024031050b2400b40030880d845184d0710f880140102c05400101d00c002c140d0080050300c40007144a0050a0041210350260050711034140c10380d4001d00503001c510703900501a1031520304095090031103040050302684c214003840c503583c002440c907400546c010781c000c000400ca80c440b4120b0042c05040d8080308400e050101d85010040a44c0020980b900820007010380c488030020710a110b0b02070348403070906517403001d076001c01d000c00d110910328813004c1801c06445800c00d194540c50940d040d0341e060314092010f2130719a801009400c40040582000c50b5851401c0349070350704070402c045a403d4007030000808000208404004c0314008e40312000c010301809000c1c1c0a00c2c50480b4174036840d203980e8803003d810143c0701d02042041703a031034103080010140000c1003151140440d00e1080c000788031502a408a00103040000700305454a0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 620641097 1250 620639847 620639857
    0x190615080a0b0c0d0608070f030b0112121d0d0b160207050603060d0507050a0314070e2e080d03020c0c09060a090c02070314060a050109020c1b0d050313090507020102 73
    0x42d01c12201c039152449044041e6019000710b0000300d65546012401500c2407001c03800a01d29804041803003402c2d42402d412418040e0302940500c50402e00100009546051036140c00101d4146644210803004075022003d50301c4000d50b0f4808000d03000c3d0410441c9943c101070240514241d43e40d403180c0c1c000700c00e03640e0319894001c0c1580b154040c0300260403481c1120420301d440b03204000390342d1200e40d00c0003c00c15401c0242c202700c2d041d030507161140c421000c0801054000341840100000e440c01c2c0741040c00e45005900407250503c506203072805116040100141000300740701c8045419035014440c00800030340101c00c459070b0318029115007001c5840d00b81e030254041c4200a1540d850309160500303010013811041000415401054800000b141c012400c0749040070624014044621b8080c03114401ca07a0305801c0030107001d00c180080f6199040024129268184c1e03048200801d0b03000d8400540380c4040c0c100010418440064241c80201a0040c1c0c641150b2003101d0502050312601c1042c0d00380e000d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 620642347 1250 620641097 620641103
    0x191707020c0114130e0f0114090103031205091204080d080a05041220070303051c050403050d02131703120907080a061a10020c03070f0e0402010e03190615080a 70
    0x4189240b03a6895000c0e0014900546130411016500d80e569822140083c012101e821126200c0001002440d540c5040b0444039082283c0c04100e540c11540c014040140ca682e114800c40d90f1180002c4641000300190b42c8100c06048900ba02c40303130349240072a541d01c064200607001400180100303402d0940c40c0102030049070300203541c031440d88840d80200c604012540c440340b14440c94540e008403c010070700c01e035000395000b6620b031556041c035500b251000c1c40000c402403400c0d40c030309020880425888001e0343c03d850804100580e9030401650052180122504088008a1700c200c416105032000401004030b020f045070b02000710341ea440081610342985120300801a01b00188820000c1d200d944600d88a1014405141c042c0c100d0b2001705498a038145140d00140e48420030840c1c542c038080041d00c0c0140100112130b212581482050241a04050002410311003038207981880d5a4040c460075025001180401c00894800d05161014000222890340c00c10500140801c5104011603240403e40d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 620643597 1250 620642347 620642357
    0x17041809020d0f1a0112060c050307020a08130305030f0409140c0a2d09030c05040e03090607022407030807051611030c03100b0306071112070602191707020c01 70
    0x4540f6000c81091081e07800321a02441c1c1071441c052016003220340c2e03018104c2c2665600003d130fa1464824116038003d1080030902509004211555a00003103502185901400090f11690307080301100844959410041c00e901021512080840382e04014000320303650b403042404680401e110500d442801a51403401c0f000702000070040440c046c0f004503c1c00c80041072480f0301140f4840500707001d5402343d60201c00054200c04c081003401040854100035010444040141d80100303648666a4810026828002d0401041210540d9102d400382c00072201c8980410400807070b8070f000d04e031075079100200c202d000c902800080362400e48140103550020f00d04d0001c51100c00a280c4a02207082e16010710650306125807503d140f0300307807410b00840301c50381946200401c007600040c08141c204140200a6010400c800c00d0507404030380005031a009014010b1011650b41c40d06040c5030002e032054000001c07910032111003001d88142e00c10200079002d0b00610b05c1001c90b444c2c2d650100c0e00d40300c580c0d0403280040c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 620644847 1250 620643597 620643619
    0x9010b0103060f03060e07121a0603010b0f0909030d02070f122313091b090b1201060503130210080402030d030608060613091b060909051905070c1704180902 69
    0x61410750101b40b00144101c201c44200d0740c1e07540e030141501c02c0c105040319080003d1050010b003105080300306812060450090015070301c2580451400102c0300c1400344207003c400040340c0030300b41c14400c9070400100c122042d0340c1c03181c55007401e0620b100900740072074400c10020f4000d11104e04c20f8140300345008069182c1d1420302c50100035031078990410340705034001550071030002440000502c540b403080c0d1085140da0201e54104d00f0094900d1166900c504000d00e001c0190a251203107104100381500c46038101191640c60381260310f4002480c0c554001d42000c20b002c0710890442e003155409100b00d10860803030b03c2d0105010000ca084c0c5003284900600c5900c20008184140383c0042038031039404030311800040344102511401c00e40700c3e520044240131800142c007032010b503903c0f2040030090844d007041806a8209000c0850f20001d510b400707000c000380d5660124800d0f51148404500081c0c020340c0061000c0d001d60501d040f07542c00b81c8a03414549080b61842144104903004080001d0340040540e103880c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 620646097 1250 620644847 620644853
    0x41b0206011a0a0503070c08190e030712020609010c1a1312110a0b091f091403030c0d2c0f010605030d050313020d12021c0914010e03100c0809010b0103060f03 70
    0x2c0407c030101301d031400014070800c180c00c2da40190701d01466040d07903640c020045008040c9414140c05402109400320703140e2540000d41c03515401c480c0880c90078078042c200d0300361508105110301c080c000c25090424941c001d0007200c4061008400e44180100d03d0030384035810041d400e9404541c003104201e19504a40c451030040740f045001c40b940300035840207598984007114806031707021951031052580d0aa584c0311590501c208203000c103241c0d0000f0401549981045540034603580030f0003485420346134039914032000c0165004920516041405000c00f07010080a9955448802100c03120400b58a032074800261843c0002d1555000c070100d448907841c540b03481c00c0700c048445000f0401c0c0d0b002502401140d0001d84e5114813140b00c90301d80c0c0d0207050070180c903410401c9050403680b121030070002180e00521a5010007041000401001d081130003450b6216008a810030751080c0e13031101183e00e001c80c141c1c08203402220306072180712458002c10021061400640c02c0b40c0b164003e030712910104410134000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 620647347 1250 620646097 620646107
    0xb09040201022a21060c03040f061109040504060b010f0e01050d021308070b070516270f180302160806011224020702120715050702041b0206011a0a050307 68
    0x1000010f441241c80d1102900041400c00074031495a40150540e140140c48000050188035040741c100e5211030314600706034641d0800c015071820042c18407a41d5401074441c0603030350400c880203040c002c2c001388104e01d81810154000c048400c0014085080c142100e520244642c581003040c16058540c00d050500b05c0240d10003e41000b22240000c0c5031441c03012034000c01c1003019100500055211a5541c506403805a0800f000c40b01e445081c61b0712074105000a4408844409450740d00b01905940b140640e140c00300079200d000f400d0b807051440e01e85250301040c120610000c100707000790200c40050b01140605610003e903072080b02070540014006102900c54040846003290007147d440e4082c065403500901034001244030100c01e030341d00041501c04c5040c0200d20b0034250080c1e402420400780380005040250040005c410300300240012000119612030788450382c0c406d600340748044060013031030010356582020b000b80800b00401c0c400303813008070300000d0440b4000038041d503589041d42c65030403003590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 620648597 1250 620647347 620647393
    0x3120d02160c081e1603080c030d0501140102070608060d0f0c030512090a0b090906060906070f0507210309030b27010c0f0f081b0f0301030311010b0904020102 70
    0x300c48100c1c1902000b040641c56140d020302100005010303401c10044d00d28030030320084800c503043c90700324400e05d114202c1005d4070902104d800c0002941e0b1444a00100d600714031483c0c0c002015240b402d0000302d264625408011800c55080e02190021612010140d540f50b00884070300382d020354210100030010710480c03290546113104041025800b512962264202805110412a85000441c0040700d07850049180b0004241c0302549504c1c00c6550000b10340141c0c0c0040010703000b0f1034002156100b0352204021146070981001c44490524130170310b083c54440d4164450400c2c0401118500f1001015168849880c40d50640300c42d00054075543e10350707110800c010488044211940205051590030091a182080490f800002c02c0090340750701800005280c180c002c10001d43d10080c403251504084180d400814406581d80301c005000781c2c0d20161311498070680d0300040c0c08400041016040030346d445094407040b00034061074680401340400004100c90290059021109143d00313141e40000c644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 620649847 1250 620648597 620648617
    0xd090506090c1f0e030316060c1103030a050c0f12010504060501110706030b06090a080d081006020c041a0406030b010f150503010b070203010e07060e180106020c01110309130501031103120d02 84
    0x440e1013184d003c00a400c540003842d6580c0980e031700b030010004100712403188c0150704141d8100508101841c601050362404010015406241d403100420307000141c0a003078410401c0c484c80420707518044400000e807c50000e20801340a50b040c4000420550300882ca0304145026070001005602e160401c110302030120514041d4200004001d01185915403c5c0d1040181a03a000108000c02c041e0400400e6450001c0522003401e0741c030342040c003a50b940400d403220102c20072600840c1090103803051044200b01200031a034050f2808000208000300711102504031014650009899039a031021501100c00340d800f0403001035420001404032500c618040d11840d4006000001c49560f140c00481c03034007000d1713003180d0082480b19200003803520305940300700b9840848078580d44481d45811400795845200040d0603050040840c0374150f00041002580d03c7d04100400000021111003103240043c2001e000c1650385448581030201181000101501c1c5072a224600ba85010034042e1204020340000e4002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 620651097 1250 620649847 620649857
    0x21230105031f0f0207060b1807050a03200307180f05100c110a03050c12031312051606031e0207020a05040f09080304060b011116090504080f0d090506090c1f 69
    0x203e410390070584042c01d000340c401c00c800108100d4400400c4401200c0484252a8490300c00c02c002d55254001705846005925040c041020040e012220f040740351040506103034888080b08001542e644a45120000c04d002c950b00300c1055210750801142d00b0907405a00c0d0421009140c884065202c0e01107040b0701801a0400400e817180d02c00046d00101d119802603443e68009052000c0c10314180c0010004180d01000951502d245044203001e003101c203225800c440f29803c1c0300f84043c80824840282d10704a2580c071040484d881e840050300500b40c0341440d5102010003407030b01c82c4c0c180d05403003110701c015002052910118030303110410018203003c10800c050280c861808c2c5001803030b00d5014500461064102050f401040c5c80014035510100c11040b41c41c0d0f00a1400b02444030f800c034002d200799080302d040898940d0340c1e41410741c0d25114401503038403004c01c0000c422070780481c69880401d8607445001580d017141c4507110460790b0f5080c0e4a5800c1e90040300c00c4851400c07548a8205070b070007540c04d4144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 620652347 1250 620651097 620651111
    0x3170306060415410c0c060c0a052a0f0102030c03180909060c120a02090d0b0f0106050405010e040f141f0e07140a21230105031f 57
    0xe80074103079190348050004124441a8a6035282c0b2245001c0c802c240a44007402c02c84810743c035100e4141d003d80c1c0810445910000f901106200d00703206a28030800040c08240e43c0784446039480d270360794900c840281c0d0107000300c4103090380029001303548101804007a40800c010407820400c000722009840f1314181548801c20012075038403410b20280140307207880b48030500305030000018040b17003040042c44a09c5503008034003044800302d841c000b0340e0040f00c0002d88a24056841d000114001e118540009500c00008400b000402220000f42480380c000c011a0440303690380c40905039018002c50140d140400d40c21032004416081603401801201c10260011076504c0800c9050540c41e40c0540f12020303001c044007922090035191241c810002c01c00001d02c8540d501c0e04010091060300151403201d41c051001030420501c0d4442d01460b0030341e1072401003000b94001c408142e0002000c041c3c0e9040700c03070500a0801e041d041040c40c200b5040340d6001d0f02502203010524941c808601d110300c060710820342e1303e0b10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 620653597 1250 620652347 620652359
    0xf0702011805091005010212090604060807051201320108070f09030b010b0a020706091211120d1e09030210030507050d02072003031c0b010917070e010e01031703060604 74
    0x1d001c07400749036941c2e8100d02c04e509260009080c170100b01d000090440782003106082a071168012102101c50600c1c00c00303191b8581c1d01007100d06110b41c81e0090342448074840046115080d03003404281c030950a04840ba00725008004165503101002d805a0103e09000001100c290189a1128041f400c81c50300c958119240c1d0399014000c1000c0e004110313001c0c1e021802e40c04039901003012401401c09402c00c0184c0383d00d00782030798541c40c1c1c0c102c2000303041c140c1c8001c15101e01e44401050111451065040c3d42c41c00540701001031104070080142908061040c15041411380664820010781c2e801810540d074028680b6016009440090400020404100080111a038851014110b0700e4426004c1c0d09116540418107402107030301c5605a4801d420070403111440c10b0041c40c154640340c460002c01724550560100581d0843e04981c06030103078009e45013030f285071030001048031402d40b0003034044106280d885a1849448036003d01008292011101074542668211000b442d40140c2c01000107241c20740fa00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 620654847 1250 620653597 620653609
    0xd051b010501091d07030c210204050901092108060411120408030f0708010e0712270b010909020306070c050a02060c010f0605010305152b0b1504020f0702011805 71
    0x6401280f0069884101c08045056001d284c04e96440c504001c01c1d9650031034580b4890701e1a188240351104071250715210100d00032446080c640340e00103100304120701d403241c251400f9202c00042100c4000d501300c03110717141c602032041003907101d009070fa607400096507082c2c28800141400c0203410300040003442900c4101071008501c61240748981400c68490800201218203290090301030400d100490300140b1511110140c0d49a11880c00d1030480101d0108400600040600052092a0321a02590f090301b1001c0c0308517002400780f260710184081d83c0d80d044510b040320311810f002541a003280020581c010b1050b03401d012036501440580391050a00d5000542c04c0c0e1140d52002c000b03944803d1000144074061090000801c001c0c01c050117180782540a482c5040c00640c2c0c0c8a109100c140d103100005c451030321400613800680a040d401d4003605081c5143e82e900102c0300c010401403489060300c01802c141c020769081000440410307091140660064407807450755099140700f02d88000000805230b42d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 620656097 1250 620654847 620654849
    0xd02150a11060c18011b060c0c1b050603181c0305091c090533091003060b04120f0515060a050d020607030e150d06090c0806030d051b010501 62
    0x5500d80c90070541440d80100c0c10020020311540769100184807254101c00000e54034059000300b441c0078104920f00060039103080d900d07400003500092401c05403800c0303260010b90300c62860b8010205000411010079035040c4c07190450003800e420000600205000c43d6501c801020700c001c0701c9007641e12814a43d0306071424282034000c0c6600181d2203105100f0030f024180007400400740c1070080c9081914400710041c18420043c80350074000c071a0080c501d24a00e0408c4040383d07071400b05031005a8030308000c880c148a42d4002c014080c0c81404006815500075000c0d104210031511051381c882e01385850b0481b180e401d80503000050f00c5862000c5054000150103104c107000604109208800720b0078464140b00c00142c441d08000c0c0a11141075406026969180070b44031125410b24203402200348810119032601c110541903100390501043c01102510113820103403d0328100b01007040f01603507440d800c41e60320400f603a10680541102ca11042d031148103400501d501c2c6070317078041d40e160140f010560508592003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 620657347 1250 620656097 620656117
    0xc210c030f0909130b0402010f030209120a1703010e07051b03160c0503030703050f09010309150606020111030114091017030d0c0f02070905041104020a05130816050d0215 75
    0x200141041c02c1c0d1070a2000a500b20140c1440c09203403840c0359683d800c130b91901400180c184002490781003120313407003501243d60a0401401c1d030b04000482c0c06a66076610310281007100c503003441411030404800303024280c0c2d0403070311100038516403a00c9081042d10203500c0700410001d4541554001c3c041d03404100010501e030401c01ca04004025614205640c203445241c011610907081080300201195000056445500400d050a80d43d03403c2000142e0081c03042280092410703850000b82c04142c9401c1d40b001c0119805a0004d10810220ba0701f842c050384000d02444683c803080c07141025180c204100c82a91214071031200299490700c4c1c4454000008140c100d03000e080d032000a04103a814800e00800030842884d042905009140680207500c0b4100b034000c80c0740d02c81c2d6490001d42413164029030032032840001fa204555401102000804542c0712520100d03024501460004411400040322000316400c9a40c102c0e1450421042002900da511360a90307010f0150300e040038460340c841d40180040c0c55 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 620658597 1250 620657347 620657377
    0x813080c03030a0c02071a13050a0e09010b030604080409021e030c180301060b1215220c0804051b03011d0309090117031606021327020c210c03 63
    0x2428202443c16602c180941e40115003041e481003010108a400120184c080103c841c1d07114002c0541a0080144990140364448140b503000100d0320315510301d45001d441140f0007400030300e0707191062503911902964000c040940400080118140c2a405843c100001450550792081c2c0300c010200150400c0c1c80790044000f00082c07c1c403e02c030b01e11401044000c002d030003e000581c82c1070b403540194091140e4202460f24100700113542491a42000071350410014001c600b5070b92408040d503603807e07484034004e20f03181c54200800c040314090815a44940d0344240245412151441114010240400102e815640341c600b555891100d10341560341243c0d081c00259214003801081060304001a8270035a40c40550008144a4181c04012921421121100f010042c00f1918001c0000d00c04c441d40ba07564414603003404180760048106c0c01c0094045103d01030750201d035041c100c100324818800040c802c0c0d446a920701e401c0d1600702011100c014041101c0506214454030403604681c000685211021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 620659847 1250 620658597 620658601
    0x30e060106080a14010e061002031603030b040b0409050a030e0f031515010813030311120f01061412011415040608061c0b06010806040b040207050705030d030c020d0813080c0303 78
    0x28245108152200040403c4a804c1e5450003007070a1500f807028000d1070103000c40580441546008004644103045194913441407081e190034002c005041c61082d0600c00c1b0304143e10704400c0c1c9014007800f03100c039401902900f0050b2080d5015120005081c80c0740d5004114003a116445607011b20000038010700c003042a122910703002025003140400d404295050201400c14001161000c00c8640002076050030006036006000396402e010380120090fa45040780c05070b00b045240c074200360b0745034101e0720103495000e08181381640310709080c00781c0d92101445220f01401000500e00c401929030b0b0420028110045250312400c1880140d40305400c00800303e40c0d55414004a03040c41084a42242c1d41c088401c4070103a9683e41e85407203d58050001c904220040300403508075034499001a900c1c210041046690b00060314200c2e465040500c1914402d0040e0203a010750540240180c4150707290587c068220584850703401e5508440c0980075241d0907a02c3e1541600140a480040503a490300328001c3d902c0b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 620661097 1250 620659847 620659861
    0xe0303090139150c0207030323030702100b011d06030c0c0a0c140102030f040902090307050a17060f040507050907050d02450f010e031204061e1707030e06010608 71
    0x141ca280755040819150034404c038003281d800314071041521340c50b103404019444a841c641c2c0a9088608804410480c00800e200c1c1d000e40005002c001d1001188040c040250b258005489101740807901103905400e1440f80ca8552900e0401542c2c0400740c25001ca083c10340061080f45000e551080440301964500c03020301485d04031002c2e02140341e109200035880e044043d12000500e000d40d1080b809142d07004a9400b907030303035001c3c8038940207030201030202c20340c0319903419625450304901104890207000b40000324112a5280080c1403140c6d8104000f004a10b10309030a0160a440c010700d4401000f07130034041ca05a1001600003007010a00b0032108400c000200d82121704a07080c0d40c080b01400d00110040400c0d8840c5441c2c405c684101c04403900020308990b100143c6d1091b820b820031503810f000d802e030007080926010780600203071011603a5228140740c2c3e450071191105003c0d82c41e5408600c80301c000f2034600580307038a802e602454030b2402007002550304120034601982078012001140c244c10410002e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 620662347 1250 620661097 620661113
    0x91d07170601121a06010215070203190507020a0b090a0e0c0a0e010201051003022701030b07091703030f0a060506070c0509060d2109030b09030a0f0e0303090139 71
    0x1420000c20001124042c913610103a503400d2070070914071030740c3ca103000150b1141c0c000c0c0700d500070311220003205021703600d000c800007500c0760f00521880300072035a245030940c90b242c4281e05503031603242c1c040c040c03442c450b04003402041c0a40268030540c0d4404104140482d0320030107020918041c2c1c115001c540d840710209100544000e503200d82031350442e803410302040a40c0c0390058030101101d4045e25060710000d0507400d442c0a5068164040484850740c07400001000320302c003940b0f4030505c000d590f540c1e01180c5424082c008081c2445c0c4121440e4410b202190342040c06416113508400030034030014250740d581c0c01046d1950170022096505c81c100b10000c12141c1083c80050b035100400322600d4400250342c2d919031040d07a42c50348487d10307a06100c0420078080c5008416040c09135420003600c0003503180918040380c1e40d81c00280035400245820161903c6140100c1411100e40802400346091008000c0115401c05450700410b1038890a29145c003a0140101d025001c000007450102640c10414200064 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 620663597 1250 620662347 620662349
    0x17040602091e180402090a0c050903030f1216090b0f0d090b0402030c0a2105031620090f06061c060f030618020306010312230703080a0c0207091d07170601 68
    0x4510f410b01040000580c0d41c201410b034484080d28002520018803c002c81e620702500d01010380504c000510400c968900e08041c10300741c02d2400c0105419640d01d403944c4070f01c90403000c0308000b1444c506802d000481d8184003620703d00100c42b80e894100b101a00300342058031540003003034034180648414082541070038003c55521440603255001c2941c43c02d52a410031000342c0e645508403882c95043c4504010081c000c64801005130420403007403404509180003058914505030f483d000001c04043d01c10308014201c188142800703044605039030703100e00034040d6035403003034480054881c44419280c03980e440c52303c20031000c0c00300c1510307600206096251240c100d9a0148580c420b81100035001801650001402c1e81981c0d03201c15110824105181c1c151524001140288102044800c800504030001c6000e010b9090082d43c0d20f5880d520341c01c40010407242c031000b1400c0140c1042d00c0902c01c40303c0760707080915017004040e031900c45028551001c0c0e041807200d404c000ca183e0a06c1c003240030b0304103040161074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 620664847 1250 620663597 620663629
    0xa061406032b02070306020c1e0f0703030305060102240109060503071202010309150c020309040c030209010c080a0212030901060906050621131e120e0117040602091e 73
    0xc8082d840c41c01000c1c07100e180c0400e041d862095141d01074855109110704070056a10038030a40d00d40800b142a40d40f02c420b50300360072054600100d5429800c5a001540d42140f90441025101ca103003141c1341103026140044c181030551048110382043c0441c188070002a0039844171a03010294140101407056030160381c000e6200398080c00040c40321a1400d22403d052941c242400a0440050329201030754040c02d02114081c0d6180c0b144011515070040000d0005e20b4084508004c03c0c1030750241078040303010f804071590004601044141c00980b40b40001e16200b00301e801100c00040804001324031a41c01102c0003106a51160300411011030540100406014111855170410040309a044a46407000408103841d13054000401c00240d803000b035448200d0740006000c0000031070040451191581000115041104401111382041c411a15500c1c0701c24160b5801c1c840d00c5032081c000c03055401c0034200307a0b8855401c101001c01e5640d20842079481c180301d000007010786034483d0200f040c00b40d070004440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 620666097 1250 620664847 620664853
    0x32307060f14031305100e010501090e0d030b03011b02070e07020a1e0c050a0e04030e0a0518040c0906080d0207080c0609190e130605010504060b030c0304060e0a06140603 75
    0x40103016800c00344580612082407011600ca94411050780c450900184018029000380c0308000ba1440054014507407002c407c000030b001c82d0361707298100c034101c4200b1a41c0c003100ea001400070180c5240700b03070080740d01c90100400106111404406075101c80100785003d030050fa0100d1000c01c1184580400a40d0200850024110440700c1307440384030311000d04d01035413603412008008203003c0200e03100640001d46006080c1c200e00c0d58a410000f0020401035138140d0104d43d9240c9152010f01c0e1010806083d140302616011944d044001f12503d0404094400c8400b00c1c1401e030046402e100c24802ca000500d0041d000704007074501c4500180c100360658001d42e5054000401c0e0000e1a207644046501c44c03038040d41e224810155071008100481101e41100b01102c44881c01e012440154007811025030b80a10020400c0340d80e6402004102c40d0944540a513000b000d10005a10b410b00d0307009541d01074010308010942815212841d03080c00215241118000d81e00c1b550144100d882501d141d41c410810340003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 620667347 1250 620666097 620666117
    0x10e030604050d080702120304150b0f030d120f18140a020a12081902031306030509070b0f04030c09090b06180c0315150c0c060a09140a03230706 64
    0x60b8035102c14080540038180410000031070301d41e40c420009541002c044494082d00c9041502c6c120101510125290040c01e0070820010440c1c900502c01141d110780c020002d25003002c120005441c1503841d04a102102590340d03882c001c08007643c0c0101c2d00301c5a05a4001c000a0f130b81c5241185034128107066081581d0301c5160014016183d01103582c00781d0340f101c0146600c445c2d09240000c410f11500c1a90403002d10745c0710107061125000005080d0000360480c903401600d0b12400118200c40d81107800c1070465008100402800200300000d242314040001c07040e1805440c0d440305070b50700b00654000030ba52659005080d06110143c00d9598001c0c000316056009580340c40104100b210024050086e083c500001103610b1043c1d00c50300c20321900e00600101c00007007088006800a4000ca551000c3c540a00d40042c00d0030300e4003804540201400d5110110303198240b102d0441d50000c03039891141c0117130305840040301042c4201151405501c03541c0c0387c04107010912a0b0075040500507030001040c441c2c07a03c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 620668597 1250 620667347 620667353
    0x60f0801051803160f02031c08130c0b18101d0a0509040615080d050301030203060c090d150207081b0d0906051b070f15030b0f0120070b0f0702010e030604 68
    0x1c00c69004c0c07206001080713010805401e00d020155102c034802035052041c090b0b1200031902660810200c1d01e03103920f4210603070ba14001c22212200103890b0040c1078949041c4180043d055200280c0240c104a0381070400782c0308802c0c0481c0b0606550000ba00204084a95400099008152034002140c06a50007281103180c840800c00d58140074000820385030711031103103c0c3d1012130310000b20f00030280070080ba2611070342c0c080040c6c0f01d68800c0c04168044c0c01048000303004005124100c0d0345201001c1c20074944501c0301d0302e412403800512072402100175001c10100010400c3c60016041d583c0c02a44820070303410b01404200e141c511105401811312808280030443c217038120303050300e01c4d40d0300c4000d4101250450b90403940c140340c1d03e5004080c0c0b04034000ca010440340d4808c58404c404100503201008031060441c10070150000070b11842c4c0c0041c900383c0d1000c0143d00c540700d00b031201911210446160720b0700c0e2040900580c01001c040c1c1c6c80107101280d00d030306560b80302c3c0800400580030750260000b0f0030161 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 620669847 1250 620668597 620668603
    0x7170d0e01030b0111060112110306010509220b0c09030c04050c030703020706090204020c0609100506030303040210031811010e0411160f0b0403050301090606181512060f08010518 79
    0x5030081c14140d64911180f40e59005085400701050b034a820b0703a980e0b41c1c42d01000346000d8828207040c0da42a1088540c00382a0800044650503180000d04004060390b4004940400c4c0301101080301d440d2402c1210301000800310159503010b8904241c0c816182da556000b454940002c10503240c3c0f1841c2002c0c00c1c400440905c0080302c0c8c000321140b80241e030b40d03070807402d002006e803c0101c030080d00142f0000d18030421078000701c2c4081c06111083d060b105844020008070050745c209035100c0398903030000c002003401423070030f04130002625425003000311300800301c000b4001481034140d0b070a40302e42900803104181ea60b070149200b64409000ca4040000b840e83d0305203135002d405800d02108816070a800410b0910200003400071420750b012424201602d814900100560000e101d0078014908012003c01c0440c0540c02d111328020780a80314400047c84e05c0c0c0d0303004108016400c62028880c0c500c0315144850a00c6c0145006400c4030904090624640791119084541c0200a40c20060010714a002455004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 620671097 1250 620669847 620669867
    0x60106110d08191514011e09060e010e190f150c02130e0712170a17040c050307090509060105100c11060d09060b030d030203151c0606030507170d 64
    0xc4803d040c44070031060340c43c0014810401c290001c4403000e08002500d191940f644501790340300ba40c2d80e54840c41d0221543c1d401080465000e0080344d221841801154400c211141d054201450030701d034491856008115940c596108444280c2020001070120041c8414000c1c01044105801d400050081400501410400000034030030f4503a0b1085451103d1079422140d45000000c094951195459810407001c4012150440701b140c05106152410f10314a02564420422900d445d0b0259800706001008403a00500c21100805d0100000c1020740703007045014080c10804000145504040c07000e0340c41c0c044146d03c013500c25000c003c0700c034840c0d9611104e2403000e117038000b01d461071000007100011118003800340403006991030442c1074414084140c020501caa2825400e03180ba00044580480c1a8407040301d11500d00c03030716409a0b00241c280400c4404200001000d071526284c516500d21090725283da005a4549d0302c0700b84240209003500d9003450503240344d4002000358019180e030180220f00c0e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 620672347 1250 620671097 620671111
    0x605030a2a120207050303070903110612060402090a171006050427080c0115090e0a081603120212010602060705030f010611340b0405130207081b060106110d08 70
    0x74526010320b080203250103440e40554400140ca44a14100034003c04054181c8001da506000400d0400321030f017060422129003404076100041d46d070f030381c06061101941c013032020350b5088805400002885040d040041000d00c6441c8090040e503003070181c81e0f10a480340b91b00000e103d58a00f60660a102404100314580282e45244007101e4500360700304011140240305d25031038030f94203250b50000f503c4056500d04040d80c1c400c460410641d581079404e603584900c00c91004202610410140b0070102c007000003512410302c24a401846e005004030300c10281d810000305810080c0d100801403100940500c421944414036191990452401502000940c50180b180c24284400c41c0314280088405001c00604002e98030b5105141c0000005006001224441428000c1d08201030100d05100c1b00400c0741c00316000140890f80d84c1d03141e50209030096101c602d017122541010044220030740164000054016100b07006031640703600d07002004d441c030010b540140c072098000c0ca08200c80ca40e0046452600040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 620673597 1250 620672347 620672357
    0x7030302100e01060518130b0702030a030c0e03060a0b061e340209250815060a0e0f0109030c08030903060106030905030a18080f060a110702091506130605030a2a 71
    0x11401100070740800305d00c20103094008c0c180c040140c1c0e42c1e000001050900c0280e9030400402c803c0c0801181c40b013a000c11801e40c560821000300f42c00c0c100301e0b00103000000c1e000309501e142483c40840010b18038005400040a4200400c0022440020152404401004819140050119186c144850006100300031301c83c2d040c54000c50404c0c030300c0192042c00d141e4201205c41440e42a010060841003040743c5625020201c143c0400c0706003420300942c0c1d580101c0e40c850b0200804c110f020013140c881408901410000e01a100102264040f000600180b8090b0701441da5400394500345410700740e05811582c00c0c1818a58a1000240000304441600f100303403910058040110b00f8560f42c11019910400c011b01c2400a100d0328490701042190281c2c20b9413200708400d4400060241460051100c003a5001486d0b0002440c80000100c0042140000806030752a00e550900500601e0003580c0025002030b8011081119506041c890000f454500c8001c41c60f120180f007201e410344001031441841001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 620674847 1250 620673597 620673601
    0xa14100309060b1e030f010b0d060203040809030703120f05090a05060c01060e0711010e0606150c0a061503020f091b0912030a021507180603050606090307030302100e01060518 77
    0x5075540c81010f960000801500611400e002144100050491010b00c20f00400511200c4c00c0414840c801106030080e104600c00d90743c907120344c4001d4000030005d9568031030402020100742e605200d200c024501c200072200715542115801400301400e05288000d0007001c00c01518180d07281034030002100d43c1100c105a99880c0c00e401e2502608807030303102e01400d00c0190309200c84140c00058544003021214002c0086200524030a80c0c3c60b441661070a40040c04007200100502c6804001c000c20481c11040301c0c405441d030f59440d4200c036030b822010400301951040c140304520f0a405803403e010300484400385281002100b80040400b1105010a21300000030101c10540f13815800303141c22a40442642e80740d00c074146001c1d449003070034024851045004400603266030f002d0300602e095604800b0302e010300c0e18140401a80240300190205a03c05410700006c411030b03404003c0000a10300c0307680a000d03014040c040700020fa4800c080340000c0750b41030075000d0215485107103207081e107101503484000c119 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 620676097 1250 620674847 620674853
    0x50f0d03050708132a050f0409020603073203010f0905071d010c0204060902040608010509090a020d030c081c060801020a02150c09060a080108190f0f03030f06140a14100309 76
    0x400c0c079905e0401c0c440001c481e00703802c40002072410002c48030141c0d13210000078032030b0b41008122401840700070742c8080280041804e0b1442034200b8180c0b003000790b41001c94941314103c611070400c200e80c1d50912004001005001c0b4591407400480104140f500502c12810000300160111034079003003003141d1254001d2000a0381c1e00c0380000d5081d007500940200a401e440d200920007070f40c01801080040b8604800000c3c036420310300c003440e11919480000e411840ea0941c01c000c1c1d180040b00d000d80804c4161040f8030080f480c100d0040a01ca03440d104900000036801c1c03140300507201594048041c0da4814407500c42100e0b00800d4803401e8060484c0c0b0f1030130036620700301c02d2b040354000c0d0f80380c42c1d40201000c511884480d40141c901810b0f60f20708804c40702c00308022407e1105500c3c40150081000f0380c000b580c00c000540020314425103510a0802240e008403d00802007103800790380c0700346020030340403180a66a0800c0c0c20040003401c0d42c00740302c8100c121224003040c2541c3da1034000c4020036542c0d01080040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 620677347 1250 620676097 620676113
    0xe06061905100201020c0105160503040f060605040c080603160f26070807030506130f0305030a0f020c0a11040e061602070308040b0a2718090b04050f0d0305070813 72
    0x41c0000906180e1200e400740c400034000d402100c0b03004003542c038100204644001402c40c840780720000e039941074699940c5607203800350340d02c01c101d04551180d100e51020078641da45000b4125140460759854415141c26400c052070504010700c240110003c0503800d2001c80c1410b83d02d07c0c00d4408541e801e482031500200c605803030084001c0407100500031004041418a0b000c00c184c81102d0148080b00c0c034039156100d051b03002c41080040200145021954600080d004602465000c0100c950000b81e440120f500709041e60300082c1d60000e60b0f0041d4003810100584107010400342d0b8829113040000d96500d200f00d070b940b001c002e00110141d84c85082c0046801d482002400080c692100d2800c2e111135448240f03150f150407400d070b101c0200b0240c41c00c8507031644980c01a500d600c0d00d940c041140c0c0d01e1034800482032400055408500e469100c4500c400440c282203040d0f4000c5110b80c00400018412803071541c1440d41600c2030200b01801c02c404e200e0343d13a5000e40c00d180c0002d64074010002001c65840e08000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 620678597 1250 620677347 620677349
    0x9050f0402091503010b0a1805030d1215090c032304060b03030c03130515161709031603020f10020604020907120c0c030908160b071103120a0f030e060619 68
    0xb010000000425494540300140c221074009455405402d08822101c1180804900502d40c25601c070014003e11640700d00026507000900d500006218030401c003050b0f810709653b0304260752081d200c0120011003581841100007219000c80403403d01d400341803030000310300c1020f0400781071582c9602c0c00e809a41e50030301c00c44401c055804102c0e41c3d00c5426107034444020009104a03803003900480c51900902c1212412030762408000310414640103613595800c10040c10300d4100c855100010304c480c0f03900e51402c01074081c094941c07040a0072154034610401090034007840703209000d18800505050156000607c5907005681200e980c1401d99034040d0403146002e400326000c0c880d506100f04101c0c600e03000f0140119160103942d0f014165501c07158140d548542d030801c1c1050b0b402070b080c1d0400041d40031601030020b440c414104400080181e0340080d00d8490062100280c2c08030001f031040344250032840c40e208124080c241480391211080e1029203505000344503071b000d0b516801900c910b45852030760302c1c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 620679847 1250 620678597 620678629
    0x90f010201060e0f0405060c04051f030b060a08010906050d021008070e09040f0332030912071a100b090d050f01050702031c1404030f030e0102070609050d09050f040209 74
    0xd441c1c4e00d0108980700c0208416241680c0c40d00031480860900701c0c542003140c0503200007412181c074150442e21460f00301d0784035001100816035100c000060640e150030041c0034007407096a40b030146506003d40641124140e40c40980b04030072008601d0010b03160300c4080005180c035410510a66600c031f0750140d604080c1d40740e829621044074401c2004000340300326150003650003541e076481c522040c031000301203142890a04045140310700c00091441d0081d00021940162618142c2e403544c491451044400c0d002404200d50070120540b40141c803281d081d2205501001c2e00705111311031071909040410034452444014080c15040750144103110003000a0780a00e540300e00200064601220000c0d00c075000250300c0000840740b414401240140c0b0b01481e006d058400900c81d401d9129542c060320316001801250741031503100c080012503a942031024001c040d00501010030221000d00d0110b083c450b104000b201030048081d020b10103a00d83c04c3d501c00350760100303940040e600d04052001403000081d2659031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 620681097 1250 620679847 620679869
    0x30504050409141015050d14010509060910150303051602090114030c030f0c06160803010e10170c0103051005060d0902031c020a02091e0406060e011406090f01020106 73
    0x54040101941090343c005540d81d064414001104612005507107441d20812407002d243c3c10b050002d840d10000b1000e0b160310074140d40941d0800301d0070013401c2d100c00300c0304160140c1014040040354034080c4840700c85041c1c100b10810145120700091013901e1414000a400c0040100b01e0644241090705600c0c03040760010940c144543c1c3d1005810403080032012214001c3c016035035080c180d03040006000c07007075281213005400414545411300240b40c0080004980b03a01c1c0e20300325540410b980c440291b01034007641000102c1864403183c0039072124140e52080d40720600d406c0e4217018a0a0110310040c0c141e100740303408907c1e178442c0d5401c00650505074020310f0740128001460603c4001d83d90100210901c290700b078849100300b0305980c2c00d002d042c00c08400e015810990488005182421009070300c0a08112042c6c060205460b06210002c4120340c1105c1c442d070703100c6061000300d8048109038014904540d900d00c5800c24080403034014001c034503405004100c444c0f500c0e500f0745c0c002e400000240c80140d620f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 620682347 1250 620681097 620681111
    0x70e030a12090b0f041502150901060806070918050c090a060e041a01050d05060315070e01031109010c020607060209030a03050417072102040e03030112031d15070305040504 76
    0x461008214628000740219480c0940007030340b24080300640e00803d02c0006864185440d0041951140995541690842c0500c05000d07409650503140c2c0e5000c0d904180c000101c0b1400c04079a181341c044003500300418010814420810002d00f90910016030385210340110705612020300061450151001e4254446405030020800c41e912032015005003070b044a042c0811a041500000079101e83e145040c00140100042c1c000502d00b0342040d500000c016040303621a40e034000d284000d58200b6980300000a5000141d0409586e05020744024403183d10261444c2c4068000081c0201c0c890840c000d0045c41301040c80010301c4a540d050b03810300c001c00307400c2d07031220842450f0051043e406030089030210302e2914004142d220b4000f0340c041c29200701800180e003074640303c20b2105841c1c01c44801243d001e42c507100d0784080300790b0900c040c60080c0042d4030074902012491801a1440d004002c0d103901e014036a0079458201d03960080c1950ba0f418440d00481d83e42c1c051818126094807031a08144d030440e040c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 620683453 1106 620682347 620682353
    0x20709060303090323010609050a0b0901061d130c03200a02030a0c05011506110c01110a0f0c0b0408030403020414150f01020a171b0706020312070e030a 67
    0x1070b01c3c03021417020491036400d50304160050b00e80140c40d0000d2041c004060301030703900c01c910100c547e032400b5030400f0002000c280320350010144031020b40b0104605500d400743d1072101d022001c00d06100c045564800903001d0012003404501d1074517a10121a4400c05070015a192201d990f07010b9450701c88034540481d801c44180c017040d5002d550308c0032040800b07132200440130000c080607251420601511007006091220484c0c0d4241030044175112200c681034042400c0002940c0b016008461103014204040c440540e6004144000d10004000c200220004003900803244202c0d8144071402965a1044414209840c250304201c000b54103050b482c40d2121851158200c103104071800c000346611421601041040006510b00f800510140c4800c0a240b10352454400c1c0c1c1c0c000e203030091400750000d5882c80348040517100000000007040940b40f26115429032800000c048480320711b0203003 = true := by decide +kernel

theorem cover : BRFrame.Cov 620503597 620683453 := by
  have h0 := BRFrame.cov_init 620503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 620503597 ≤ n) (h2 : n < 620683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
