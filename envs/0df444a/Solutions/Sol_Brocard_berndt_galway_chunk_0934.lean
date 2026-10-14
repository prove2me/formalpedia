-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0934
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:05:04.238992+00:00
-- url     : https://prove2.me/submissions/4255eb32-3733-4e4a-a5b3-5910d2652a8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 167805755 ≤ n < 167985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 167807005 1250 167805755 167805761
    0x30f04080d0504181512050d0807020c0105070f030216060908010b010309020306040201140c100614030307120c0203100e0c0f090105010c0f110a120b060d030e0907140418 75
    0x90780030107102040c401001144102000005050321408000c01c1c200341000208000d9800b54015003145011041c0500501000060020548500b034488000d1500c40a00c00e0780e440d0b281c0364005001400c2007040500082d000d0340c1c1844003a00c640112180d1030040b608550b040c200d40d8000c5000034207901c50420801b0424000c0d50a04182800c0401c903a03c81a00441d8441c0c4009001034140302442d1002c0e00402803c40480d60b811300c45038152441e00c21071489c2d41c00502918840c41c00074140785040391126250101c210b41400d40d00500c44030b40402c10200c1500d03408440ea006a81c075000d0042c032690311110f00e000b02c07a1418100809004403010880422070142c4c14041064011940200180090398118605080d0307150000c00b480400300740c9190450310040c08002c0703141c01c110602c4002481c0c03035084141c003016501c02d40d14660f00c0c1e9136440601c00020300741301e005000142d00c40c00c2a0301904241c8030841d0001d6040c48c20014078070b004800040706a00c20b9000da031000c0303140003410203d010740384 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 167808255 1250 167807005 167807023
    0x7060605010c080f1e0c010b0f04060815090a050312010302031509030a0e060c0a03020601181103010302010f1101060b13060504052407150203040218190c0c05030f0408 74
    0x400c040801c2c1d996034860104901422014103c1200c001404580c04403201940e040d809401c40c98880d52551103e000b41e0107048a0b48a080c0590004a142c100902d0940562815245035600a1060000c1080311000101014003940424020540070700d001c5841400208500340302084030100c01c1d455807040c145464684a9004500c200071390901c075041d03101000300da030b40400d0741c9069207c0030541e0002489900c030311800880c05120342401d22003019008035890303040395040c040d1000341c1019162100f0543d2030b840201951580208014001503009201207100070740c2e80d2520001c80310340c01800b5802c540070360300400c0740500b010030003010340151400c200018241f54908141040d141001060590f0b4a8040c02400d12401e4024000305030094025170b401142c00440d00f0150104108034100258002c2d2801d90051404009501e010780f18506c00600510b103203020784804e0802c10003c1c500605030b4500c1316042064200c076160100d14100f0142c01800d2503640142d0340c8134500800c41d440d1140308 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 167809505 1250 167808255 167808257
    0x21608070804030b0a1d1b0907120518010c021207030f03060518040516030c0b03040215041215090b060f03120418050604140708090304050d080c010b06030c0906090a1a0706060501 79
    0x7943c0c03140c0040c13582c41c1f20b6810000659860384a5124081c0a85a1215001131135070b016281004015041c0c4036110310484d803803440fa00804c80030800c040c040b41c0707964109070031a0310105c040020900003442000c1e0050480e1103843d000a00c10703210000100760725000a0080061603e0344148820701c541800030360300129019000c000014555a100c0c00c405c42c0c54400c40da14200040002401c0d9100c1410b40c00c4c142c4000314440c2d50304c03500c038655440d4820407000207680040c130070a06505694054410800a85d4100d0882491541c03500b0401c0b280700d42d15400c0f907400d8011160820262250301010344040e000d44803900725404003031b903607800c00c1303c90080205218505080b03804030301111502605400c0032031450000c01944d0340140d0035266100702e80c04160070007130b003035144130131310500c040030781103000c0910000d02850740301c2001c01680e404181e83c1400004010032800304580361440003850003481c041c000000e01c2d5960030420b48158501c56101c106400d00044000030840c0f503205001c054142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 167810755 1250 167809505 167809513
    0x6050103020301050a12060b03030a0f0906020312060d03121b1107030c15020c090c04061805100c03030e0a032001020f090103020304030c05060a060f09021608070804030b0a1d 77
    0x140000050100d1002e210361904488203415446c00e119040d00000c10566014040f281e1747c030311144004281602c0e94668a000030f464039404100b96202104076007031144c03920070001d090307200e0408000ca0548285411010700444120300087c1c856503000d00100c07405240c0c1c540d1802c038140d001c05018402c1e041300a0078241c1100409200182c219115201030b21510710b0100780e040485c0e0000ea25054050b8041035003c418178040100e0000c05000800540d40c070b951b1040b15001141040c00c2e03403c05c1e00d002c0c4540c410102c0200d00b031032900c90f0031b070700c0000e5021f0b04d00808d144e4a01f0240a0030a0f03401daa040c0c0001c0c030041880c00005403100321400802c4800402146800d0480403929250f000e4500c0d541d040640000c040341c01d05d03208e000d4400495403c401903514901740740c0400303402072010f071045441c0a5000b8000290074585482034440e80d00003110040058912507a81800c50390101800322104001848040045002405041d20610001c8000202003c070307050180040c20403c0c90030320b03a6604c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 167812005 1250 167810755 167810759
    0x1e040b1e0a06090b0409080f030c0d020d1a06090a0501110114180c0a03051906140703090b07090b0f030a02041502010c090f0b160312090303020306040c1106041104020d0c020d0306050103020301 85
    0x1c02d0080b160012380c900507464070381d1215040360203107220700d04041c28564000700d030844940c040fa60200500460301c103159020710140354140704680c010480c079103500803500082080309500403241e101c071004070000001580d502450741c160640b003003500c05d4817804a548104bc80895001c00402100940c1251808892859036407510342d0350114104190410304054108010888137401106600c0b02d03074440782c4001c2c83c00041c010009c0103410402c1d24011528008030302c41500521101040d640240d8841d490b1000020000f00c940d4009095082d402e5420400000c662084c4010341c11001129030012440b10f12040c001400e40c41c407600040100501c175101001800305401c12030320704408054000250600904040d01c040c0000c0d4035581016040c10051010103925074021842008200c404001c5911079000445817041e2642820340e040d449000410701141c141842c440800d400200301514201c40354924030140c8202005100242c2e010100d9211580d03054051103001e02303c28070301181598 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 167813255 1250 167812005 167812013
    0x30105010e0a0902010507021806010e1f0c050f120a170606040512010e0106060e12060402030c06160507030c03060b030c0f040f062c1e040b1e0a06090b0409 69
    0x1200141c20141043d6943c40314070110790198082c2c43d400c40c0c00030300003070004520722200c800740345040751611f0018420001c004072501e070404000e1114208031140041d10b03108602c05440468019000b03561500c40c40d64440788801c800c11456500c0c004020519864148061b00036152079540740441c0d50714203c0070204952525010269800c8501c1107449815a0303c026a6160040c400c0800c1d180f590350030f01101040c02500641c480c807a070386050301d4030440c51403843c075829101e030002e4900030340c1900f01c19260031551901202a140010861071812180c62156030303018607010956004075403604401c0e4040050041d00d1041145034042074001e00511008200014034140308a0081442a55075460408134501c00381d04c604003900d600e00c07608504020003042c4007100c034403c0e415003510b682040001069024401a82002841c01108140441e110396070750380005ca100410700c0444621040700038036202d100c0089640560580c1d800000c80c40c0c2030000800a84108081c254021814103070340320001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 167814505 1250 167813255 167813279
    0x60a06081504060e06180f0109080d1d070602060402040501080619110f0c0a020405010b0a140901050702031e0607020d080109180503070b01050a1202091602010e0a06091103010501 79
    0x21940c0201c001405035507910b08203000349078040f404900303031107454208044605c1c80140c000c5040501c20442d10401c0c00c1c00d0b002c1c1e0903150401c50003005e1b000240048a00308459800c0b0106c5034100921030080d041c201c116440c5044056406040103a014100f80f10540c1820302c40c080c050502003000d001103251080303100e03400040c0380c0000c0c951966600054808141c02809071400240c4501001d0b59960052042c03554994525000764800d500d0000001032400d004e10403203114041640320400051002c0c01e0310030441d04a00002d5043c0078003002071000580c1c060004400300c40308100100b60003804004003d291040c0248030b0400d5601c83c5400700c030b001d40c1026145045a80071a40400c441c1c2c8090901c80c01c80000c403000a01500c4041580c1c0200040100214141c40054401a6055030340d14248144003040d080d0183d0013840c1d02010400b0040100c0500244032010700001c121036070075002d0f1600d001c884c0041901c1c4a940c0708800740030810708440001c0341000440082c40325504114400c446 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 167815755 1250 167814505 167814523
    0x120a020312040302150a0e1e18040501050a02040501090b09060f030c0304050106051005071104180507060e0f01050405190521010506150306010809121c0f09050705061303120201020a02060a0608 85
    0x8c42c847e60007240c0301002c1c108468154140025002410829050549002c3d0b00c5040c0c0301240c40317500702030000d2800340c00c0d8407e03981161030507550300350003502d0640440c0040d80300c11320054010008002c880705081c11200258065940c840d051903691500d41450342c2110025041240704921150901c0c0c022607101c0155100c054110919516107600c400005008201c060020101e01072021f40c060180907001c41c50f4411241c5944851844501503010007110010014180e408900d080c8800e2280f414803440d00080e4450f100b6040b0002600c0d500014000c2040801003000c1141002e800b0442540038040c0940051082d10400410011000c2404883c040100710b2410003151000040fa0340804202407400d5812007411259107010101409204c80c10682c442000d0078105440c0482d83c81441c4211071100f50080d0140c50940d042c98100541a4444c40c2c85c68001040c04c0d07008000b03d448014864101c550640006070b9032503180c0c03006401d00100902c803009561030301d41e041040560103d41c0d014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 167817005 1250 167815755 167815759
    0x2060406050c19030c0309080606030601090905010b0a0801060501030e0303151c0f0b01030c0b090a0b0a03020f0c03040905100e0a0c05120717060301020711120a020312040302150a0e 80
    0x915410050022460f04228040c03001e0b10f02e0500e4003040500d600690b40c0c0902c180240c6d03c1c08030356174403003c0040c2c0c0c480f01076880a4150744020010007120f62168040001944a000042400701c0840001201c1c069a50088919a551214100718035a0180710360746c1a8040c0c0700c065400e5180a85541d00c0000030205c203d402110000c5a50407040000348020b1491940000380f203401c1c664a0500300e201c41401d02080314074020900b404949144000c003607541c5100000c3c0601b92446c10132803844c10315000f843c0c020042c55000e03c444035102000c0400742055545070300003982c07514900601d000a4403c0540300d168031000e03004050243e1062141c41551040300c00d00c02160364960258101c03a01c0c46039812000024412005205540f40e00c0343d10240245014411081c55490b8807080500f00c0c0315000008040c44e40700404400c1909044403224481e544020641d1904005a004641003a04000c404a403c5c00000b9040c0110f10302803500680c0104803090950500001d018085d010401111401d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 167818255 1250 167817005 167817007
    0x31106070e0303300c071a1504150f0b0706060501080c16030c0c15030501091e05090a0b0118050703020418022a0f0c0402071a0c070b070503090c0301090206040605 72
    0x1000c41e9140003007091003507581203500131107142c584c0d2501c16682162800700c850f0b0304810344c003505510550708900d0280201c2520221560404001c00009208003260510b018480c000e00081c41a01d01404000810031000c20715660308581c5031101c200c2d00300c1d8221505000004060005a0701d86c68141ca501c014403035051155681ca5050581d9134000402d0001c0000041000114450382e51120f02803070010a502c062041e0798807103400038150b41c2900126210207000c00444c49180c5034680042c1d0f00211100b05403601e40c110b5444008040c00241c2000581c995481e14049000456214695001282e46001c50805041405080c01c00320100c0490303e01030380200300e0302e070b040401c01a0f080d45e010088600070320003111000384949070f454040d00c02016000d41020080281064021181c900d0751155425464000c1e195406042d1240608080302c80d031002c3c010540011901c03030415021b2451916040d498ac50312009191030004041c1d58a806a4103050241740142c84903400c2d14241c50003400c1003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 167819505 1250 167818255 167818297
    0xa06080403120e0304030c06021501180b0f040905010606020d0207050a06051c1410091a10110f07141909050a020f0409050a0605180703090f0b04031106070e0303 71
    0x440041c0c02e54030070f840d000b804001000800c1119016143d01160321680980700b50005242901c1030b40c07002440740e1040a400707405603c04500c41d5500803400c0d00401407941c20807100ba040810202c030a010001c440c80d85d901e2205000d0070383c04204481025036144010103d50742050f000c00d400610074401c1d10b044c0000400c3c00030054100c4291241d604d1444001000aa096a1043d0a44070b0041d0f48461303030181414000305101c1003e004040e19403004140c0c81c42c1c1a000c0c541401180c48103000c200c2d0811000c01d543d60190501840707045002d20317400c03000b0411907013008044018000103031303c481d02c904210260b0350450070300b06040340300f180c0c0b210b040004e2996a04034845c0c040d00c0340c00501d030004040040d000ca0785680d61b502c09800340d941c00b1410400c10362200e0611046468107850382502c2c0404100040d255031094000d00f100c1c0340304100484807100b080c0e5624451400644045000c83d038600031190f95510108075072940440c0a2030f201389840d04900109450b80b20354481c410103c0d1011400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 167820755 1250 167819505 167819537
    0x180d030902211509160e0a02040b030a0209100516030309171c0c0c0b0a05060a03080a05030f0c0301060c0807050102040f06081618090f090b1806060a06080403 70
    0x4503050703142c00744070320005a07802111841e03141c00303902c5040c103d2480c103c00403410f010400201d1514110700043c2c0d4042c4141402180c1246070f41c014407001415030204008240c4411800155014141012016854041a0003007100b511115201a8108181488403245000a21252001c1c250300341c200090450401c0c202000340c200003009080300780740c00041c800d155105000542049615a19040085103a0954100c03991050494060418190003000c5403500c0e0440d405580c0096004120041442d42c9984880b2540c0081c2c100b031000c100081f003003012180e03260b001581d115410200140c690360400c003010741090085075003d089404041014020020258100c0c0c014001c03072229210201c1e96070400500c41201158540b110400c40072600f0280d0f0702072030117604404950511001c40c24200031800e40103280014001408648620001010803282a0840c4c06101a8a0140007200d00c1c0d020701c9140100281001d4002c030b00280c1d08116441c0c0c4041920740086c2c0c18984450f002c134102207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 167822005 1250 167820755 167820769
    0x1605040911040c0e030615091605030708130c0b09030d090503070b0901110304090b0310020a020303010b07030e0d2d0807080c070305060f0f0114010c030e06070b010b0d05180d030902 80
    0x4c1c0c42c1c052080005100c052100e41000400702c090444000390541e03241301d08070040c1c0d541d00c00a0b00c0415414000300b400c0500515a541d41b00305008074802c0703020b0094451040c1800300b6401415011030014400015080501c21441c40c44894188240c615191502080c2da40c8006e224001c1c1c007180c0810040c0d5941e10869140355462503140490391501d485810038801000d15280c0144240314454080c41411614001d0301d1160019401850860780b80c440726071180d0b07100c840c0403420003180005036042e030ba40d0001090b040724004c100f0000c81d011905000b440803007080201d5000c400303002c45a0000202d07110111040503a01800940e01c44a00c0350009151941c1500b0082043c080c050800c5030b110348010402e032092241900041c41660385a07088034003a00d146651383d00060700390500c9004a0300030200044d000c88050000c074500021500c0d0843c0304403081e04545001e44002801303806442d185e010700742d007080f41e40310b9400c0e440702414500c560303c3e5400f100010a240c3c90750104425076803005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 167823255 1250 167822005 167822027
    0x1090905091203010902280807030506010903140705210703061d060103050a02011706091b221724090a06060303030504050708010501120303020c0705060c1605040911040c 75
    0x2d80041d03100d5842c0c0203000c029400611071600100481c2c0c5001407209052a4160017141c031940b0b503217440e921805011005410001d000c103040c4208900004005003210080ca2005014040178104041c00c10041020150003c608031098204091a40e280048003090550440e903000c10002080503109001041c03118507020818101d0066100000600c500460300000441c402d90ba4482000c2054403080c0c50060b0903240c0b603402041881c00994002e456040303c1c40c000644030342d1030742001e0b44109101401e001c0c1c3c0c0304c1d911007558405c04c10040050761026560052400300082c0452041800d003000200d4200819040e4640011010402d1507034184249000785410170024804140c032420b010300905000e4500315010701c41e404c0d000500030b8043c495503050b20a10751484406900b80d4600310084d4100c00c0c03802c1c034030f030003031003800a202e503103400003400e960702ca507409032440c400301d1040010442e209620040c0914101042d240024440c0c080350f4100030011900001d00001c01c0c103040720301001030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 167824505 1250 167823255 167823283
    0xb030c0a110f0d0903030e06030103080306010c02120f160905010e07050f09090a020901080603012c0c19030c0902030c0d020f09031501150203070f02040b120a03030c080f060109090509 81
    0x10700c40e090950300c4030102d000d1703034002c0d140c69440c504070500344210740c8402d100181621800740040b9140790301c50308a4208990000304400000301d089044d80b410180b2888201c0c4603503002c40b03031030300560100c910f0100003061039007010802c46d85080c882070f05034000201800100400055200d000044660560b0503000d0007034458441403030482c01e80d4000f548010b031710724081400301c4e0000c2d8845c0390502503d00104d410041440380d460031150081072405a903007940429005a140e242c05648070120040e8410783c4290944801501e0350400c05105c9241d6003240c0070140c010010012b441c4c0c2c09204459107001c03072102c010ba81d0103821084940c07501400c031500d81e05024803040c40b10300ca041070301c1c02816900d849103c501840104a170a03684c9200d520401041692000d200300054a0035600c40395034000d01500d900000b03c21080050b0030051800c1040300030942c1c9541d9455520b074001c0200b41d01200d12003640b400b03401c215002800343c0c5840c3c030511030400d848100041e4515010b001a403288260703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 167825755 1250 167824505 167824513
    0x2010e01090e0c040f15021c0c02090406060915080d0c030c3906080a0b06070506040b10121a040c050d03020705180402060d090302010209060c010203070305010b030c0a110f 76
    0x70103048603c0368424030a4000c00402450701142c810035004040013031b0302240c0c0040c40b24904054110141401e50440b0b0801d03c021504c00070301680306c040860348280c1c4140000600c95090003010310842d00188960b40700b420300288140031a60001031015803c20b031341d0800038002d400902d001c81d1007103101d0f40014804004032042c0c0c202c40320050b042c1250703070122040369910005007403c021701000741840381100140d100004910014119803001c0f54914003e4410741c50700d034650710380503e0071109483c11981110030900b085161545c00c0b003084050301002c0c100c01c648044903122043c040e04400b4406c84201c983e44e021030104a85120401c0050102800a0a291620313050283d100ca500f481001e024043e14400724120390000b02a041c07203941d00600d420f04014501c1c81440081452810440079507500304104c0110313035501005821140501000543e40c0c1c68540002819144180e214509a0809006000f41c0c400c8070800d407084440d0b503181100366810006121454445004e0305001d071802 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 167827005 1250 167825755 167825761
    0x6040e0a1d0d0905100f0c020303120c0a030e03040b030a0b0109030215040501030f1401030f080d0501090207060c02060417090a0b030702060702061f090b0102011e0c120b06040302010e01090e 84
    0x40120750b20078001c0103030b01c0d42100c041d50780c018422010100c4d2070140000c0c2c0c4001c0e6140324240581307a6400f07201d0010b01201d043c0440000107000e07000c81a61441460b0401040009405506000741028103c4581c0503504281ca4140025203a004c050100703c0000d440342981036071030f44a002d07000d0055400800001122030851003030200e6a006000d0386000a040001c500121805402204214052054040b00c582c0c0703107840c0e046292180d11011510050100f141c072029285e40c1c001d607400b03000036070780069a4500924150048580342c000c1c620640d0081c10800001c1a00356548200b041401216182c0d241c0e002400900f510b032868100300800d500101c00d0010750743c3d00145107071191129408858841c1c4481c07885581600200c20420110074a02c0c0091050310f810360001e4182002c180000326003422890740c9080510711172070010445940d101c0030a0040343e13008284094080c071281c010001a02c0d1500480e0381e6108a01019050010b9001e07500801d074440c1e0b2503c3c0041084070025030483c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 167828255 1250 167827005 167827061
    0x30403050904022b0c0e030d0c020310060807090f090f03080907090207060912140d020d0e100c1d01050f0702030f060702010905061b1801110115050315010506040e0a 73
    0x3460780c0c00307501102e40c903003545c1c5a81d05004400c01c2502c00d800400403c040d03100c80304116170580b41c101e000c0b0707014040c05421001502e054000d0502801c003240180c080786040c545004d044807440b05c40d1300c00242c14099494085417402120181180e0503107840003040e540c4a9000d440e040140e07012004040c400501d5006000b8540c2c000c4080074455446003980c101710b41c0c2c045071009030300c426455400104000c0310305198461f038010205181140301c00f044900c005003825003403121880207009a991074060b048905a441102c440340024401e8058aa540030341c80028024061403404405209000a80341d040d941c0c200050511450190b0881304140f900d440000e001e041c00381310403075151194402159040b80d00c040f2001107440050f01a900341100d40300800e5042040035803090600462008014500e84203000d9000580c0d1035101d01c04829207840149407504108400c88614000114014850f43d0b840300c08071812214425800042a2142d03940c0e040100000141c842542120034030008100e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 167829505 1250 167828255 167828317
    0xf0a180c0f08120a030203041a0106020c03011407140c0c10110d09030b06010e12060106230a0203090d08090405040b0105120c0a2c0c250803040305090402 68
    0x40e5500780165554241e444048503610f9040140320344512400b4460400504d220341d01030340d8014090711090200000e0b01890708082e071000c9c0c01042c01a000748003505618282401002512210800c2c1d0303294910788101c000b003005140c6070540300347e8603000400d40b6066004100caa52010340040c0a01140c0024400207041e2103510b841c01c060a004030900c00110500a484440c1281c0d0007400c203040c00c1d95003000443d005088013900c10351041c40c20402000c440b0041000714040e1646071983d22a074101224070058501c15400b42900c1c11004114010b140ca6000c0140c0c0c0d1000710680305140c4405052070b00101d01e01962180f01c0e045441c04007000140041241814121101a03035959001441d080790f503920340c180c2c440420340040c081c00c010802c00300c00702c54400800008400d0880d00080300141500280001e80c7c0d490515080803030380100e0740c03c900c2104690b51002260400511070f80d0b50f6004200d0000510280500001051043c256211501102d10160040613020914410710402c5c00c1c1c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 167830755 1250 167829505 167829509
    0x18090501110901090b180609130e0d0201060f150302030405030c0111040e092a030c120607020111033312010603050c1c020904020424031209030305030f0a180c 70
    0x209110381c00219415508101c0d91406c2c001800d10b10030004c408207008599100c84c64054112110360003501c511071441c4943d040518944000c2c0400d40e00140c8001d0039140c0316040b59051319640c03202008410076000c80200e0414107401c026072a6911404c04030300f5400b400c4540d244650a14080f44010f4411f80700900541c2d942c0c100356031700358688041c6103654807191060801d40d0340c2a910000701c3c403922841d2000d01d11f88020112a9141c06290114510315201000340c0c0082d800304082c00b100c140c0a0140e48405050804103c4c11840d08010200144200c650440c1500e55140280c2034a203003010007104c0c4d0220b0141a452200e8002505140203140364402070740e50380100000c503007440c45c00340300246001400c405501b8010140b5000c00c6aa013402070402c0303074016a59900b0340e03840c1e010581c001b00000100100340b04203600d1400c2407655402c1c05e60001c0100000083c040c400240c002059980001c000100e4921980e00c0220036002008259480c0002c0d502d03a043d1142040030304806001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 167832005 1250 167830755 167830757
    0x102709030504171609060602060402010e060c03070b0f06010201020c1c02120406080a0e19030e032b02070b120f060102070e0a0c02010e07050901030b0709050d0f030305060906010918090501110901 86
    0x1050030345d6012010101d0f03100d4003409006030030850201300990b10841e0034450b040c2c0d000340950300c0c0c01c0e420141c003481d5a000890840b0303415003410400010f0095000f100394410303420300003940390140715040700341c860f160368102d202110074240405580300d1081002d141010b660681060f5201c6d02c0d800068070040c421030f080d91086040032068180501e010483d02c403e1501800305201001060380e0075a0b00c81003c0304000c3e00344c03095900c00b60a402c0300e43c1c0d076a0300da884980454207500810b40310007030412101c1c0d08040c040d07150400c410f0701c030041c050200e0355010305511030320381c0c254541e40e004078107024040e407000c030654082400344908003003150710100181843e90002c2242c460405209901d039201c910542c2c0d403001e071170001000810b100001c40395000b1030519201c1074060315900000d1451460074025505441050195002c040c2c1502c41d1941009044070460341500c2c1a41c0000e01100081c01a81d405084940079140c500c901d035000084190f03885802803204550007454100641c2103c04624 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 167833255 1250 167832005 167832043
    0x3040605060312042d032a060503040209090c0907030623090109050712020408010b010f030e06042604030f020127090203040c03050102030f10270903050417 69
    0x81c20070b14002030a94004140209401d0400c3c0c500f52030303400340e28007801c1100400c498442d9403244030311060140304c010310b10030155404d0100420816820b2045e80002c15044600341d1072003070081c213030403200f900e034087c1d4100d480c5d98095488116640c1041880700c41e683d088841441403111494250b00160203a940010481e00402d04005038100101c0f11300b0041500182250018801c4a0568200682c400c140b42000d90600c408100347d40101c0c0c4c0140e018028a0b55154410540b560303211418080c01c80c000d00d028048440e410342900e0321b07464054002003d07000f02d01c107002c5d140c80301c400c18a40c0c0d00d0365510034a80c40c0c03556030410100085503204220b000500460300441940d02c502c0d44506010850350b013490045041c00c1c4500700075400580141c94007848100300000080e42400250300c20142070040300b5160800030300d0008070314035580009201042ea0070a1180300c1c07000f884400925280420049050206400c05032214410794024003441005418440550400050508429040e0325800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 167834505 1250 167833255 167833261
    0x6070b0f0705460c1205280926120a021e19081228090c03170301030308070504060c02010e1206010909051c210b0a06030203040605 58
    0x200c82c0e078411009200038070007428a500040d00403800b00c001c00c828400c81403524040454034002501d10107015484005801400450100502450030086601103400c0c110705181c2102c6418100340300700302a02c00d105050003942500b4910807440c02c40200000c4400703410448040300c02020060f40c518003e016441a059180400c101e00c0e021140400d0031580a0461128a0f6070120240082c2d482014810300c51180c202c0c10b99408560810849442020029540d1400c404003010112009041415900316090084281c00003102d10714406003005500048895440c0780052000019400107020881c000a8130703416907100100942c183d0b402078481a540f95140300d0b04680f140300318000d00000801c0d0032024401035000310480c500c003050052003160b890790a010800c3c5880001d038000c441c4952103030042801c1c800203100100129407a80c05649110141000c06000d07402848440b16100c1c1781c04c404882c41440380d0740400c0002400802041c3c0c03103651030200034080e40040d03a080d503500d4505004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 167835755 1250 167834505 167834507
    0xf0604050619091d040330020a110a05070e0c03090c060d0b100306150513050108040215070309030c09090c030201050f0d0905030a0f320906070b0f07 66
    0x1550115040108600c1c40c00c40c0d20300c0200008a4102c00003401d01440003004112440d980c01100d000e01c58803039003034410b4503103401d00405010500c049241c0039241c0301c02400090442018614042c50220400350340d0701488402152104d80c50b94034502076019000d08401008004102103040302c680080352001500c40c2d0515600030710043c0d4280595500920a00c0521304010004d85155240074600240708001400404c0400454281c12800295510003d001c154800c071141c0c044c0e0364040ca0002d0400100d102d952200b2501401006c0c184014072000400f15a40c000032100700000c204140c5449040c1c62170050004282400100c030b09100442022034030300820312a07540d1032a00403446d80400340c919001036983da80404820780b24a00200410324000b01d040c002c002784103108400540da64010071a0040c01d01207500d07552020498140e00e01d5003500313100b120002c3d8030300d03240c50b070100441d43c07813030141d07400f8410300c0905d540110b0042508000c1c080c6c030040c1c0310301c601f0550762880c19079518244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 167837005 1250 167835755 167835757
    0xe0f0c1918050a091a060408030702090a0b130f0c0e09220507080114060d0209061009050d0b090d032c16080303070f020607020d0c0204112209140c03070306051c020f06 74
    0x24130728540c0e006118ac8405482c2c0764072810740066083c03100041580011012405160b158441140c1c00794549200c900e02c19618802c0303a030191458a8081040160880000c108080c0542801c4424801403146a01c2929000010b44100d50100440c0d521a951380d8419010b8048888051014514840041d109040800d045440300c0ea0050901c05607680c1d1100704804801c9007500d010810640307000100d01c644900c40c0090b5030b1303805070304080003900d000140340703203480340b404070003020142442940006c0e0b80343c8184400c000c0000916810070750107a0504185060040403500e8410342c5d1090300007a010801000079401100c1e141d41d1000c0702c452810307050341c1d925000d4880d1001a03000d0101140c4c15449400783e07000c45c07031000700082140790700b00e210015079410640840202040707040c8442c192002004022000b0442010180402c100b200034020292800800c030300c01d0103400000260a0318804e03804003000e410024030b150038001c510b403034900d03044008500c12401400645000002c03803810740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 167838255 1250 167837005 167837009
    0xc030206010e0f0a0c11030d060305010b0f030304051e040203040b040201110d020d0c0303060503030a0302220f03020108060d1a18070506040b0c0a05070e0f0c1918050a091a0604 78
    0x1040050080d20743d441142c0003442c42145220820450034146d8002903020700c01003c0e1051516008600765065043c01802c480002c01260700c034808808400d402600d001c400c3c0d400f1184101c405d81024810100050711100035811440c1c0d00070300c00070401c002c010701085120301550007a03032018104049030025590f100e0703142d0a01409a4050611410070520548200380560f21a1402040c1c4035a1071000c00d156810a0140e07402182d004101804820500403020010220044a00100c80c1c40c00c451000043c407035003c064100545540021402d840746800c2c45102540140c8071a0540e0041010307048a00302560a0304440f100e81464054a020010382030f015518010300c40c501d85843c2c03a041c6081c41d4009005204d0500a1031402c101040042c82104010f04c1788004040340742c5030804003c800e1303800003025254044814810701d4405e90159034800c0c9610712a00300710320495000501304669590a600c1968804030f1b0450108042d01c01e60415905a20b0307480b8000c0c4094080000c1100718001d074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 167839505 1250 167838255 167838271
    0x70213050705040902070b01090b0a0e06040504060603021c02011805090606091512061f0e01030f15081b03060402031c03061703130803040f0306021b06070c030206010e 74
    0x540080010006580c440d581020031410028980740e076811111041c0c0c0c100c807005494100501c07004000c1d1441c50f010710b040c4100111071100d44076042421900a420b000b40040380a40c0d9100001020403007190311440266400074648028031031005600d04c44041288000c038002403201502c0000003004003e1030081d50030003803022202d41e54440c280803443c0c2000c0300c06e947c4950600c103880f45412060340180000011050f44103201e1038907006124601d00c510414920199030740b605040c400c1d91000003040c8001c001d2a0200d003000c460801c7d940a08490850f5a05820803160001031410000900d0403034a800d140c01d81c0394041980081503101c0c0d50413280070350960480a41118441c00b168215003a544007030800252440d1034012034594041100301180030755000040f180305c01103440d00700d00000c3c0381e890000c600e800c2c1404042c12045500c1e210007400e0580200d82403000074113900918411032025170440d2140d1801400052080407820425000340c09400004034458620310f000710f101d041e02c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 167840755 1250 167839505 167839519
    0x605120a030c150c080103110105031012051203070c0611070c05060a030f110306030f1b0f06070213050f0106050403081603180305060901141302010807120204080d080901020702 78
    0xa5181030341c115685002c1120711000025003070715185881d10842c07800c032070315507038080c102e60461420140740c503008201503060020920802940e0007200300c8060581d000121505403083e090f1400b1071400200f040355070240c800210070400c001da03011020103000390090100307000c0d4400004609502c1e1151840c0905503c1c6004010320641c02c1500003810180003903c1e0005044103854800e1045030802c2c03402107100b00000080c00010700d0f040201055800500c00a480400001c8072041801070201d9411402006c1c900c0c105022555290292180380745c02420440010207051541d0000f460708543d0303244203440960000c28028130440a4031f040d258085040b0b413038822203032002c1d0709143c9480811410000b0b05501c0d155400b4070307520280c0007944501d004060740e0600701c43e25400c0d50803502420301c0e032000f8a0200266481416000c8800640a080084954403507017002c440d10850003841d02592400003030700055030140022010849900d0742d4070001640c9551101500740d1085610103580050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 167842005 1250 167840755 167840773
    0x120215041113180f21030c0324140a0b03090105010504110304050a0b0406060506180103061a04050d050304122001050a20031c0504050609060402012a080c10060512 72
    0x5a259810140680600d102c04172581c080c918020001e62810190800079880b0041a60105d8042c080c1039042c059054450803100000041e0b40d80821141c800c00480c1c4104144020007616210000c8010344004032180e40d8a00d132008085020744028481c1902451814804014005448040e24000e41e481809407480b0003180c0c4030300e8103104020340142e501d290b81301000209555944001c2c1066a481001c0e90241c2501c90700140488090b0b80c089038154004420300681190b24200b242c056490450701500c0b09000b50811901d503020700d4100c20fca00b058a240d134402e0040b23114080c03103001c82458820b00300c002d041307004540b00c3c0102000100451034071a5000c25000d41d54102c0707500d28840000316800d060000388040716400000055032001603445040c40184541405050b60000000000300014241359000820201600c0d1b40310091b40c00c80014813024a0b100c64034002210b070040000b079141c1c101c1070452910342c0112264802c51610b440800903e506141e92101190350a8001406a0399 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 167843255 1250 167842005 167842013
    0x6012603030c1c0e06040c0905070e0603040c151806030b0105030c0a02011407091d07021903090f0906170f0705060f040b040e010f0b03040503040312021504111318 72
    0x508a044000400701000c0c0284031403030392500c90480740e1070340040140017a017484d04248070303642241e81103101d0850a1208000c41300c1d80003003d0920301c17041520030aa59680d98200601007040940100400603156000140d140d030740f1004041d039800c448044c0d2003101d507a400b402d03000c9449211255020500c2480001c440180700700180109444500000c98450403084c9013846411084035141d01013100c80405001161116005035004d09030704806003118141305101030b5840024014584102d0f403000c0c2030301d04242c8500500001000301c044641941903c80320100050004d9000b23030320920140d0040355407040380c0013030205841a00ca501801d07255042805200290b841520072602d40201084001000f046c410001c000901d110030302120381d541010514200c00315940e00c040340d04002402032001040303011040b01c0c100c036400368011116100300d20003641030010800000d1f2107001d1a808000c140103044040d0120354104440d8407541d140000130300402c44440c1d020050080503107004420000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 167844505 1250 167843255 167843257
    0x703020d081b1507020712080301120f05010606051801030515040e031210050102060112080f09010c120e030d0216031203060f08010b03210703030507050f040806012603030c 76
    0x620a1002c11444000c100140e00e20341002e200084990f1541081006000c5034117112050145c40b84250290125005071104141c40c0418054007000740e1407600c0c9101002025000e0181e1030313078008001d100c0b0075501c600242c01030f04592804071b04030b504c501c81071100b58802c2c4185882401740c000142410b01d41002440003c0043c009000e519110400040812036002003800e8850003e05540b0701c0c03040c2c01d2500080c06c1540681c80b0040d4a5890440000010200c10564010010000c02c4544483c0b44e00d004170761032040c800c4050014010702c0280300c0c5556108040d500d80c03e0050782120080900110101d03034881c0e0041d00742c1e03c00044100b06000040107400481501c6030305190115042d502c840c501d41c0e0007407280d886940b45039903942c099805800e0900c980d0803042c5403040075021071440c0e40c1140318544101c5200408050352200010b403c0d40c00b880070b540b140000034007035544841c1c032114096612036081c0640c84955440d00d94401c41d0400002c0640981000340000d1410b50315502001c0e030603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 167845755 1250 167844505 167844517
    0x6010608161b030e0d0c090f050603030a0315030f060b090601020d0228050706020d110a0f14070b040b1b0303150114120c09010815010801120f0507080a140703020d08 73
    0x80011446401d003056480400217891540614500e400103480c0104e050102c1d44a4840003100609010800c0f982d6038001c000d4655403c2c950402048100540000680010300345e08000c0c14601c44035014820720030194003d45906605580b0a046629104010399603926452140c4c0011303403001803c419040081c0c48030007400d0007401c20809181c1319550320a81040e10342d401c5800182d114003401d00c2c130b19034003500f1210720541000c00303000500c444d80c0345c00d00000c0300ca400c007400d10f0042524000750024204a09001820703c101508d0b103564442001e04102d501050000e40d0b0103441c013038002d80e0540d0100480e07018002c00c1645402220074a0010766160380d07880b0b1443d01c0f80304240015010a00c1d0080d05911590f05408520b50b542c07203002c0098801040034007460910060031100d040c0590700240020305492405540300562802880c0200c865034000500500c54040c020f000192044001594920984207403140c80c01a1000007060fa5a4019488007030f5022000400c800042078140d4010f0113 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 167847005 1250 167845755 167845757
    0xb030c09130e032115061b0604080a11060112060902011b0318080a0c09050901020702060f0c010605120d0e0f090f0118090309090e160806010608161b03 67
    0x240100359010104036080c05071208481e4100040000f0040119072a40600007021141204141000300c0b5580e4041c107841c29031400b40c440021f201d02030000e4a21212914030282d02152294a800e14040420740c01114405000c18241c0702d01090748540891203605a8400d0301700100c0603d10760702c070000501240c2c10241c0c140009904d1210245000009042c000c900940713440d0266a201c08051180380456031040c20ba0350400102407000030700d0081c80400303c030307100c103408126905c59408440c020311400500035444240007a403c0714202a01c0003402443c0001c500070884d0b1581c3e134040c02400b041d0011200e11542156020f851402d00030b00301c0702d1190a010305048003025122003c00c4107110190340c042141d6101c1c00041003440051165000e881e10b2000043c8180c071a00e990180902c00c2d00e00805800350b40798440c0b5047d00d0f5040104580c4000c01c2e5543c1400c0507961615076403221001c0c007032000001c09450000f450742c0c642c4e41d400303070303805a035941c540028115000c1c8000ca1114901400c0b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 167848255 1250 167847005 167847019
    0x6020c091b1c02120a09021f0e18010306150602031e0409090503030f0a1104290403150f020f07020108060109090c031d0c030c010810080303010909020f01090b030c09 73
    0x342c10001035020551920300150006035100d140c92041303030544400600301c409060501800e100103842c1c1481c04400a20003110f0380080f0300300400c0c151820b0304003401c810b8120514110300d640c40801034840d41d0403a03010b82420824602034100c0c001145500d4014800568810060301c01004003101c2c0e50010600c00c02e440c58201515070792610240c0d2510720094806600c0031052020880c00742c030f0030703d070420003008c4d0030800c030a060700464a544c083c034459142ca10450215040002c9207a00d1104d0582c40714414440d40d0725140d2618541c84081916403a1090b40781003070001880281d4801c0300e2008514506060419444d607004603403200000300110b04000803002e0000300d8400ca4020b103c402150f944010130866100148002401c42c00000050680d1005207074132000e071070200381c00c0403e0700b080ca0031303c40075920200b0700c2000782c11642c003c00c0b15103c0080001582e01d159403103031500a10851300c10301d01c07078501801110074200c140210540713090100302040551800c4001404d4070300c4050100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 167849505 1250 167848255 167848267
    0x11060f04120908030d1407090e060409020103020408010e0d0207060504121202010b0a030501020a27030b131416050303031501121e060f0e010f03020103020307030e0f0d0906020c091b 80
    0x60f0643d007020f090317101005c2d180e00c1d024034800b4904ea592548810f0a2801700c2e910340c07503e04040640e003400b80540c1e02890b41e8800741d0056901c00e40403a8040c103000f100910401c100c8007107041d9031b2807162400e8001401118808101c040c4114125011203800d80d902401e92522600d034a181580300c08001001e542d655180104036840d04100d04000358000d000068449000c100050700c1c404200d109e01000c050002740400303032811940c030b0000c1500e40001c01d0060a41c0c40452100040f544204042c0c0840f010709140c0661440016000b80244410f070721031003080380d440c028159680000e86860110b03003e011130703101503940301d095121980180e8400c04108400306e102101c5000c2d4103003602c0244192904002d014080c40d6100b444000d00d02016104100e600d00301800d205003c85000003070405400001288000384241c0000085558150030740303480c502800f2000390750718010344181010071100040090603900108200342e400c20f000d440d0003400d60b2400702c4042a0142d0b140c0300c0000310028000d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 167850755 1250 167849505 167849519
    0x10e010c1a010305060109020403170d06120c060306120b070e0f04060b120702030715051009110901021204060e12030c0102040e04111c06050a0b04020313020111060f041209 76
    0x150407600c000d0803020084650441c101142008030507000301001d5801080200f0005132801e1413a074100d04104012600c4886000001016141560104110307201e580c1041c010f0103801e01e001c500f1a00d4030744082028564948a0003c0c000384908081c124800050018012501480e400107001100811101100441c2d50000e0222009a042940c07100000304250000305031920415403c40650300086051500d2a5030b1900c0986107400d10681c4075071103e0201c3d000044007042c5202808103100d00b404110541c11617840c0075003007051b0035801032003136a512400108040c0c0486041c2ca4081c5d0315000300c00204018004443d0400500c000c45100400c0f9031100c421080c4040d201503c0366441800c030509060401039243e52031007e0352441900694a50740558011101d8624225801800461580d445c050801c004091500f1a5901300e4000010007042e010644c0301c4181035403007600e409071120706100141c0d5840e241110043d5448406a0106004c1032030a45c02c405000114036240c4006619428 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 167852005 1250 167850755 167850773
    0x1051c0b0a2702040b030f060412030207060906020306030c0d12110309180115020114010603091a07050406110313060c02061b101b080105060903070902030f0405061303020309010e010c 81
    0x101d0b0300300c00d4141c44500821803916000f001107a500860042aa9085046000c0d0716540050001000c0c0c004e5078500340b140031b01a40513512044e030401c00403c01c1d011681032000180d403049421520134002d440790364071149064100f110b011034101e80010748070501a04107452410946902e10000d100600034402955203500c1c0a2010405030010714000394504011a1451054000600107590402e0a85042118000d00c814110f9041e0300c1c0c04201c42056080c20000820b48502102d0440881390404c581d2a801ca1700910868070b2540d5000126090708004e00c1e201e0003008411500084142c00411100c0d01c82e10748000068001409a490002d40c0e100240c1901c038140d00d1003410360402c0500908014040c4100c01210240c11070b00300440b0800900140f4a5105020701c0d0f10452000c1a610001d4408210071009081101317021035480c180a03420b0050450125011652031050000188545003400200700340f850703068005500301201c107001075541282d200700701c03410440490101008507101003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 167853255 1250 167852005 167852051
    0x20307090e1608090d1b020604090c0206090606030102040b0d0504081207020708100204080d08070315060e0a060e030a0803091609090b1b07020910090c120501051c0b0a 74
    0x10300300d090500c2c0004030150030f00700010600441600241564141160000b4140d09040080c0040104c1189240b00044950085030840201e50b4901050310809980001e50a40240c01d4042152220f5603100b04050917841180200701d4500b00070300c0381881e0f40c1d100c1d400c101c0e08180302e01241810301000300e03207900160004171194801640107003410001c8007008d2040e600c840152850651a041c10080c3c2c0035030360524440000b04006035000011030ba180703342d0005400e01500c41443e064155140401001c50404183c41ca114504200700003607c240140d1b4030a40808c005070183c495010380f5100c0b40299080248105424080c2840e42141e994040c0380000c01b620f035100f07001501c8542c0c1d003018100900d00500004441294030300d401240003a4009035140b03640d04031070185c09503545448650f1749900c0c0768444072066003083c0320348407000d0300652214000b03140060100102da0740d50003000302e08145c51a40c54800c01c1101070040204600c05029903001c5240440810301000c5500d6002e8010891 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 167854505 1250 167853255 167853271
    0x409020a08070810030c0605071a010609050306250503070909050106030501060810061e0e0904030c021201020a1b020414070306050a080703020315070c050f101d0d03020307090e 78
    0x80810009070036000f103040794000c440e40c50441c180c24116078400c1403407020350003070b10140500482e00d1020810840c9696048c0008007a2482039541d46910182c9640c9903406090712038015000080c54091495928151403090420072002944160318250f070380b5230001c1c04000400098078070100c1c6413100c2e030040f80e008003019070380007407a0361405200800344030028000391074048100034104010390b4071a10280c02400c1e1083e00d8840c1444075107090361a440748404407034100c001e10b4200414550440f81441d4070b503000741c52407200d0040844004d8201d00c141c04001c40482c030b4070241c80b030503080a5980608814809032000822240c146050001d02c01f04a4071780c00042d4461005200904009107000000c5c001d038001010a0f0b030556001039201d94401c0c2d42c60901040302130005050510480402c0c4110b90024169100031001c00709643c2c503108c3d440801d151050030010703040d10144107805200304010b600c0300608042101020b0480c0a0b50028258808008082c100804c00b05030b50810030340a010380c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 167855755 1250 167854505 167854517
    0x4050a0f0b010f09090f0b18060a06060206100608010b090103140f01090615050403020603040203160e040c050108070f030c0e10120b060a05160204060902030708100f0810020c030409020a 82
    0x1510f5024610983d080e00403441441c10000e1000000e90508003521580b5481981d90545a035045100076440403188004c1e5980e1041d8000e000d61122a5031040c4181da6481d070940d14195164840c80c0003124440c8130307910004482400401c501c0c49100c01800031103805140c04100c040380c0304500e409505064910310705010780d150041007401100e01ca44001000c0c80c4035841e00c015501c1d0b01c007a15501551001a0040d080040000c0442d502881110b0600c2c11084010000d244c48a003525403801046508641802c854007002c5050f40c0140c074030030300c03034a40740d40c4d00d00305680d10fa0401c601411603c0b4404c410f21660178800382d811b9942001c10010003045940d150254a401c28219059400c0026541c0c005e95041000070301c0c0d00d500c1411680c040747c42301041e0015854501c0800c004000561001000c14800300a110500f82d0040080e8024118003144241150b00d81c1642c042e66585445485840d0307000b050180780581c895005000e07641350000980382855940d01d40d10050340c0c0440c00203000144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 167857005 1250 167855755 167855759
    0x1b0e010e010206090c010c0f0b04050703030305092d0a05073506060d1403030a1a0a0b0a0f020109170a0207090b0d03030203090c1905120f03070b04050a0f0b01 70
    0x19000c1458210040248014511801c1603889940c444195514580c10405c43c422420700b4405c03444521251030758420800342c072914203410100d8552071203005c128006803c20010030b0884000150000800c1400e40401804900d80c0e0350302d014840300a81038805034050b14802101045050003c54000c04c072039070464500c6000800c8140800a52100000f1000c19002000c1d880b9134000a80540c000d2043c1d58600a850030382c00d0015030711040715042030f050311002040000108098004541c820050426070341855454010040d00c0b51103030141200703249081c07040018241c825840d400c1d07000554000015078508070340301d00c2941010a40300032091200051600080740c0c2c104210401840395880402107111503d0010f0102550b86201504160300803001c100b64030b038180400d00c9040402440318075117019400d41d4221440261007071612071084c20151413404d120100300129840160700c051031819505507104190024045d0042c0e85a10070b003021131002071a404448090103015000c4195158 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 167858255 1250 167857005 167857007
    0x4030801050f060408060f09030c100c200c0402131701053102060d0204120302010c080106020d0c02090702120d20092d132415030f1b0e01 61
    0x12495240b642d0040714100000c200112010030302d0f80d0029011002ca50f06612621286495401500c45c26040750080c2405c0c2c105074046640070001411050b21281100c644514101c0b46c000383d02695820310350098010032415207001c2d4000c042108041c056400041d464504080324180f00269100f41c60790356200f84011040c2c82103600d074071301d5041040c0c01007404054401028001c0300f9003009000d20408600c0c1d824030714413a01078402400c800d80d0307500e42083c22810002e002e400045d00c004c0124019a002248452010400254590441d2540c0c82d0400c0c0c3c0d6401d000403020018154005c5000d890b01040080012200510009101c0b0a000ca00502030070100038104800c02c005244c101420401c82c82c00e6241c1000e9070003081543e0404cac40840310681081d03030804000c0c0e040c19034480c0075041403541022042d0700904040c100d8661040c00202048654240618140500110040d05070031050310319100b43c100040d01c0a140c400410611607a0302100d516000181480f804100224044a625 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 167859505 1250 167858255 167858269
    0x1502010b040e0604030507060509241b030603030703210204170111040e040f2103061e03030903021203040902070b0702010b01021222120308071e080c090d0204050403080105 76
    0x80440080a003042d420071740d070051b10070b100700000208100d03121340c005810b580062004055509010f00c01d202c401c420041004103010301203074030203803007041a0150050034800d001540d1059401800440c0703003028a4a0550305a0410030284250030010303500c42e0f10048260000d80000c0055160010a001d507100065003559401c0c0125116840c0c24001004001d420184907504030340c00108802e0908501e0501518015500064402041d450860100556855401801203807800e0b0344110180c8104140201e0551880c131001d0300040d000d500a0000d441d000020031a0080a48110707880c080d07491012406981000e8001e846405042081003010382d02806600d0120800f44081d00c4451071f10120307920f42d4040c01032240080b41100300244400e1541003604c402915950070309103580207482c1707001480c50310112450390009464042c0d00380c0b840e5429400310036105e4a42c641c000681d4941e01e0445050300000756655106100002e008050380b10381c407599010b64000d540d03c40881d81030106106138 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 167860755 1250 167859505 167859521
    0xf030c070b030c0a0804050a02030d0206070314011206020a051201150f030920030106090e0a060b0907020d08190f050109060506070803010e07050912150106051c151502010b04 77
    0x141d0201001007003030040c4003600b02c1d0310110242c00c110050340c0b41c5042c910310f00300018000a403d88510318034400174a800003400da02c82c500aa03410310992842041e4010092428403c102090030f01c000c05200007400d980180003a40c401c2c5c80c0003810105148840c10020b202a4840482070346250030b0340003d1075000441040c9a691410305020109080d074903414410006000ca4440707682e0100b910025a400f90000d000614500f1002e200b0281c05003001c1ea11007848500c01c803201840d01d14030680c41d00780840c0d0341c0c2c4180421b0300a0a0703100e081120584040c18018041d22a10546102003aaa09085c0c85413012807410280d00007100d43c105032014088501c95080b00707100d440244502c0307002400400c100ea0645640401000054407440c1040d103043c06040621036103e00d09800c10500e42c4000510070080b2540580c40350916603071440207075850301c5001d11188250400004494038117003c2d40001d0864480e0600c40c2c0c450913562620101d51402c21400000140d444842038807140c0381c10701a0140b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 167862005 1250 167860755 167860769
    0x4020108150618030304090f0204080714012703080d020a092304020702040b0a030807050606060901050904090f021201020d060f0605030f07090504020304030c1202060f0114120f030c07 81
    0x154003030041000890a0044203203c00e103418440b801c14485807000c0c41076400400c03035000284160303084410454080c3d009070282410380d04c2420f0000840c040c14a2515000c14010786501404102c2c000490940e05021103601d4080044084000000f900000041c0000a2103180068583c10200380c000c000d020107030311008031982c500e5484054000d440c603c4000b1060101e400582d562014804030f4081d01c1101c82603030f400000c841c1d0000034041c11000130300c4694816400d03103890ba5150710030801c807401101001c034000b80d001e1006202c0303410070758001446c403401120014a10200ba6001410060002c01c00c804980d4010504050030b40ca1405004081d042d04080720f0a0f0604282c00141240002000d0400b0700380f948010996440c01080d2043c0641000b42044d5500d18203400d0251440c1c0f1940302c1120384400e1115134070849440410800d010701c64501d2030004030307480d01840320140c803910310140e507002485600040b000c2ca402c21416500c40404405903841da80550300403410711b402980292 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 167863255 1250 167862005 167862031
    0xb03040f0203100e0616051603030b030a0302011508030310180f050c0a020705010e030d050a090906150801060e0d08091903060c0908060403120f0e01021606180506040803090c1804020108 82
    0x207046d50b9001000e4500220f4014000150500c00e81021000303014124465509806030308446014154190401120040442d0b201c010055a0b50412640ea11080340c0901c0c98280040701032003007515064181c4442d841240380442d0340044542e55008a0740b00355440154000c000540381c2c07980c0d40501400006060900f000b009610650740031a8542d51254810f1003000740c00030702e1490343e03030084100c1c2c40034200e00a070403c203c0ba150790318404034110010502021404107000001c51070b10410900d030260b00050132030248855070344d9035122582c100750200d80d840800d14045501545046851100950082c3e07000304804041c02c034080d185100d19000111907402030742c104408a50055100841014a8017000580d03c2c6003107010001046144c80a0325103500014003c2840c000355030400c10030b02e0180b00b041140c50703401500c10005154025006100d45c02c102e00041c003288512024541c80317611312041c0c0e00641100c0700000c0040262000407032008104400780f10a41d64041585540114840114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 167864505 1250 167863255 167863291
    0xc0218060f0f010e1018030309060e040527070914010f090b010503040b090309061911070f050f0402090406080708010b0103051510020109150f0e03070b010b03040f0203100e06 77
    0xd003605101810301740910591112081c1a43c4515616100030701d206454103000340d142d180080442000d44103d0002568145881025103400d209107402035100b820604841082c0301c0142541c04208514030065000d000800216848a4020000129400ca034040007540c10f100e85401d2601440e00b11142c4107261140010553360010100c9800c00e4001c0d0b6110308542d602c1407814590f200b07203035816030020000304045202c400c0c82c2840a084a8090f1500d151a040c003040f9244d0b5940144500c01e10001204010001410400334a8101e800e02a001616150f40c40d00810143e40c00381d403011000c2e0780904001c1100c0902842090f0b150142403a042c8180c0c10308414210400e80e262910700d01c107050389240c0c000c603e4000d40c054401c07142d1080f00c01f03403840c2120b10044000c1c500b807440964240d00b400c4c0d0740e0154500200031501c48a5020601c0a02642081c181d42d0311904001d00481e4007101000746c01015942c2080130034203101036848041071203c91001030718206040a0484800c070b0400c1c03944 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 167865755 1250 167864505 167864507
    0x20426160506160f030306090c0206040506010b3708010605090907050306040212090105070f09030803010e13050316020f0d050c0103050a060306051503160b09100c0218060f0f01 78
    0x35504a0700101c54041d1540d03540001100700c0078000c14010251130660200404040e016001941105d903070781000c000140718000240d854080c00c03503000744240c20402c01402060301100241169504080540c441d56440710066654a40ca000d801003001c81404203125071507034089032003405001a032810038188608100410001e000282400041c440044001680d58413a030381a80c0544912044081450a028200038004c0009031898030010303d007804024140340c018080101105d500404951442e0720301284c0b0303c643c003005446192043c0c03403d100d000219a003080030b0404511151100050300c26148108040c400310950102c2c02a82c1c124401408100c01060085403d1000c0c00c0219803503807030b86500b40c0180300710303000100b00c1c13072400707007449882e8192100c1c00850710002e504483c20b03000708568200c070110140c4561000001c0412040550f400c028006944031500c500b0b1001800e941a40040c0c3c030710410f0b01c40070080303000000801c0070514240d8140301c002441564941c02c04408030380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 167867005 1250 167865755 167865793
    0x80d0e160909030c0f11090c130909031115070201050a0c081314070b18010903051b04141302190807060e0f0a12030306050a0501050406030c1101020426 67
    0x20078000019036522501d414140282d40d03a40300c0650240e0711098108481c642045446141100c41307000e40f24480000b0740142d0aa41240c810a62401510070000e20703008402005d4502c0302800c070100483d03c52058a080010000a81c10701004201007199107000b0310000d0864400400c004030842c100088408003580040b0380c15088083c41c85014100c00860030010a00d1800c1884205c061066140c0060032000700d03400b6041014401c02c5540c0d144600200460300403140d0b0001501540008069241e4142205002600c810002e80007203108035960b005050003580889581e0800d00c1001003450031440d0510154001c546007407418510641400842981c0b01c44d5400703030b5414465030f07401580c2103170744d42404010302550081081840380c1c0c50390400052160050001c0300031a0805801081d286031182c2d1074800c0d2070040c0c0d60281041d00c0c011089018052524043d800d100c0c88410040034820207000a0002d04141c40260010f074a41d039600c4c101e01f203030b11161102590025241c10290510780d079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 167868255 1250 167867005 167867009
    0x406020f03070f031b021c020108060409050c0d1106030a0605031009030503061504080109081b01110a0311090405090c011103040b04050f19090f0501060e030c01080711030304080d0e16 81
    0x700d0080300c040202501c618000c00c000368007030742c401fa041d440d0610000f030004075406054401c1e600c3c9011303500d81406020503640b480000a281c3e41000d40100224140f8000c4135407080e000c1d800d102c4c2c8648125011500d0344c0c0c4142d41c0080d100d03031210420b11060030204040b0b01c9120440344200300f20101914018a03c0c0406000c1504c6224100007400903046404199800b40c0030403002089820890303d0048080e600411483c4003000501c0001200b01c0b0040c0308990041116080042c40d0004000c000c900421511000107900c040030b2000d40015140c070310526206511075401811404c8050f0000b515500d042500c509032540304000a0041c10341c10410344044a5040c0c0742034140390441d600280107a8801955230411140600e0700080c11805508000c5400006000412103039807100000c1f9a02114582d105030550300c00c49a8007050352203840e000c0c1d8016204e01c3c140d09510003010809055a00607078040c1c0e0001c0001c5009640c0c92070300d20030008404080030040070000ea00d0740442421840c14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 167869505 1250 167868255 167868257
    0x90f0f01050405101814010605070b07031e0e0c030c030d0914060708030f10050a03020d0308090304080a0807050c010305040b07081b040b0d050105150904020f0c120406020f03070f03 80
    0x2e01c012030201120f8685041c01742ca800c00c200204148400210720041c500500134400b401c0344c08000040710350052007200c24850f00030011025550b00d0b20f00590140a102c3d00212209080e0000d0221f01025032040c81001446500070780746001c002e40403d40b420a100e0445031007034105510807200a074000c400c0000300c90000360005581207000000402d10302406402a1490304000104552010315140d15486801103070400c0d02e9290301c940a006c0309012078000250401807052888011074041c650155110412104681c81c00351540d0440f4181280f80c001105c003480041000401c0044c14000f50fa0452405c1c641001180303440d0315040801d03c2d024101070284040708001c10034074009500e038004440400307021183d803113540b51402d41c0590b00461070580203920300750020401e45450741440301c440c4424401036043c220b03401c0c00c002c025070040742c80c103c1001c03040091088001040c0503d1042401c010b0046490300e20380300001c0c1c1000e0090045a943c0d400800c00c080000e80c48090300b507201509 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 167870755 1250 167869505 167869511
    0xf090b0a021f02090d02040506032401060807021b0405060f03070605040609050603071b06090539130b0105090306040606170606010f0c02040b0310050108010c02061003021005120405030702090f0f010504 89
    0x4003000309003032981e0850780741710581e1181a800070142f60040100d0488489555151059075282001ca031201c0c05450b0840d42480c2c80d130301a0b1071924090300101d40205004242004151804001910b410174039071100e804214046010046a030708001c2a40003007509542c02803a502d005013000300880d1100e40c3c0300e08110415011788040c0046a40907030035a941c01821602c819114040c1d515a50703a088003080303c12061000e025200088180521101800c09041828030003081d640f0714001d0905200f1441c108801444181156581080700701d0060380540800a1710f142494030064000240c4000d028140d8003010611050303981c03016050600c1182494280803040e8540f0000f0003070440c600b012380e407600c55000601d08812003940990704942c3d11800070020604410300030784e2200740c2250f000c52805003500c0c0400c054100703504c0c4644405403d1030401d140c07602c142c41025a00d0307000d07070b000c1e1215800400c040c0c0460410f81702c015003103041014142c0003032a0503180c0d4081d00505004482c05940c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 167872005 1250 167870755 167870761
    0x618021309020705030d1107030819090b150a05010203030106022a1e010e01020c030606101e05120618040210020102040503010e0604170412030f090b0a021f02090d020405 75
    0xc0320030020806031844100a65503030400e814407a40d01d8110850342084c0e140303403001030b10b00d00358581c00b02d50302c041d81515110074a5032124101d84950600800c9001c0564881200100088009070084d100340318080c19003143c058103401340a4082c1311504107030f0644d0700c02c000612032560005203900d0108803812100070f5900c880140744003100303184220035422646c4070700828070f40340748501b040241590a98900ba02060200012603503544420b480681540202c8046400e900b0301e1a44900e2030a402e0a22008002005400d0010500b00d0407001001440129041058540c484507450300700303034111114001040214416081d09030003810082c410009141002021070007034060f6001020000c00811180b814806003a440340c80481c0c0443e015020702803d04120305240c0d0594003a2120400d00040e40303800c42c0c1d0180c1d2950300f02c1c01d251080c031403a5500020080503540050403011407030780c003800451060080303000d1035088030500040b60500511462402c2e480317130703481040394940407500851151 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 167873255 1250 167872005 167872027
    0x151410090b0702010e0904050303060f09060f0f0402160305030f0106030203011404090c2114030a020606010c061107031205070c05031c15030501020316020609030316051902010e010f061802 83
    0x5d10304401154004e21200d0400c001e00001201a6101c0d0001343e6a84604101c00c2c010800703003c004a85640c0d0010001805051501b40703009803040150001e840185426a01001201003403031900d002c40003e1000401c00102180703c3d14050b00410b6241015802c42d41010481c002c05800440c015004540c1c921100c01400004070301100109994600400500000e0141c40300500702c0d048107a4418100903072000312a0400000c9a0700006a5409040301c0d45031040110b0f10701c05030000c00d4803403a0716440341d455086280d000620000e442900c5009103040d840c0010000e8401c010082400d01102c0b00c0c420002c15804402c942c0f0000d4800c1c20a1101c584017400c4e0001050f600d828001681007826010040000541c019030140c552000c0048020302044002ca90340e09045401000da5082440070895600703c1c00e0140c49101d115040c11418001c0c0c840c0e03c4488000c42200c40e0300140c1d110320b941640380ca000c2c03103102110408940144441820904400e510002e4841458100799000601517500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 167874505 1250 167873255 167873267
    0x305031e040302031c030f0c0306060201061d0414030c010f09030912020907140c070902041706010b07080702180a150b161211100603020a060c050a0f02030c0301151410090b070201 79
    0x1c40c44001008123107804d0324020010002401240c01540c6880c5012402c0d0034003c60340b0628608469144900ea5a166914882e0840500100240e0310082c410070003100c101380a4481e201d00310440c0040c01701032a040081501e00e456105d07580c40d01c2e245050f680580c48031041e890380701d89a03090141000c00c513032100d40007603c5a044010194002c40304041041c4520340c000f80100c488510401d5a0b86c0141c20b0070503120f001c28444c14159000402c251400290010060f262903800248005d14088030649004144082101d400110a646044e200d8020f04800030708c001400c1990803140c1484c800001e2070203041160117000d0030f40c02c44910500d0f145d034812114031410070725580590307403c00000804c1c20054503050008070303c40c1e80701c4a00070924900c80e0b0580704a040e0004014040c0b40003c0d10b80c00c06407516864184d0b010300485041200d1030320f003401400810641200d21410080c80c060b20301c101140318441003482821312029044000c2e92151480080e100011000c81d0360b0540c61005030b1360 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 167875755 1250 167874505 167874521
    0x161d01020304080a030c0c060305060a091e020301030303050f07080601021e070302030a08031005030a03050d020a120617010635101103070e040912140f040305031e040302031c03 78
    0x126100e9110f0030805c066200038001d0059100350406c600c0d46032038842c00c0d003d881040303403002c1c1c02450003c0108448071194101e0395541112018110100100310b400070282d0303000360010740100341c490b0240085111111001684240140f421040c54100000000d49419928240010b0704100441b001042001881448011640101107612440c1c05217007031800e41c4c10480314801300420144000500b8140811000e82969159036403074541841d0b11401d00c02900501298004c110001c0000342001d039003885448090304441d006000700b5481c000c1003500b503812030b400008a42c80401140d10700903841f080000f40111803448800842c0d81c01c10b08051602c2c1c1c15a40c4503001508008000c0c0c6c0004c83c5100460203071000741d0311031028075100001e00042c1c40f61b895000b42a00900307800c100341180b10340091901d49008081e001d25001c03001001280c150010b03082503890350400034a41101d90240c9070020300d90070700c41545908040c40c3da0006601c86454190009000415001c1114124031981c4206c407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 167877005 1250 167875755 167875769
    0x105070501020c010603050604051606170a0213030305041815140105070503070803060103060b0a080a1d0f060702010c09120201030203131a040201020c03011109100311030108010c08161d01020304 86
    0x89140d81f1305200c0c0e99250265025a4240982c0c1e41d4210362000802230001603c07403a844ea4102055141c0c3d5980d44004028002c0015a17402d0001100e800c1d07184481c0e4000318001d83d2040e440d60304019940f640d800c120501080382c0c0e0328100e94040100d100f52480b40c1212104a501455141c000006840610032940001c1c01404002202010400100c0c00f95000304003e076002c11105899103181c031564801c0004100c04502d40000142c0780d8040c50304190040e5915600c2c8410703910018440c18a4030000454a80b815003011040050f6180e091051495520040c40d000000c9468030601003022414144080d040540010002e240c2c403801c004802ca58070343c46580205030900310184c2000c0038206890890043c05050f030400e0061034140a800c03910303c42608002d00e45843c2c0c0c406c0200f450441d088080a1645403aa131001c604042000b45000740040c0c00003094035401c00303030300a00422006109458001d44e0f042c08964141d80003aa5442010810101c040084e40d1030006038614029948080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 167878255 1250 167877005 167877011
    0x90b090a0b0a050a18050c0304030c060902012609010b06250809060c0c041d15040f080c07150f08010303050306220b1507050d08100f0b03090c1005090105070501020c01 74
    0x3444850317103a00701c3c001c15150407040100c1c1d120403040c00150b200035034010300083d040e072600f00081000ca074488811907205040090340c0c05031401190314070111060000701c4401101c070400c200c0050a004002440da000c0b201540303090000c55209007400f842181d612400d60110000c0410080d100c4201c6103103110050400f52154003680e14103640310400450f00d03005138240845428403042452a0800114001002d0040c61890018100b0103d40c014000c0c0ca0010a05907107101050001008106221400005d0f007600c50500c0c2500c401d6104100d044020890007810b03040e141da034850015810741740d151500c44da6a84030680001d504c40c01602d01403003901e4a09503440340000340b40d48081081074050f140428101000ca100d551540a0120090050307006800d02c110542c0c070031032615034004400c5a07000d41c070a840d05031981034850b280d088131040110000030710100210030410300840300401c0f506080e0100360300800074018003503030103098180000880e4003030411100307405035000041440d00070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 167879505 1250 167878255 167878259
    0xc0106090603110108040201080c0702010e04021612050301060903110d05010609020903070b25030215090a020a050603040309141219140f12070606150206010e01090b090a0b0a050a 79
    0x90300040c0aa440111003010b400c0340030b9030a42d40a80e04c1c0e0381c4203940584480c10030765655408002c80f80d00c0458104d0400c0300c81103406a0590311480500350023703404e10a14401c9101c0d142c124140a000c10030341c1e06001040c001044415804080102601c1d8407000740c0e0550394400000c0307007007040291001040e03542011381c08a00e401040e80500b410220403021900c1141d41c601094115200c0c490304034a14104c03000c8076182c030200da1840c03c41100d02c284110b481a2800d41800d1003182426280b006e01c50304006590000e42c50a401a240604802c03903030a455400c2c2a0750250600301e0790310030b01d00055000b05060100e55245c41c6084080e0380769105070744140c4014407455685088070035003140da080980c00c030015000307030010310b080c03440c0408801401502c01c8032881c0065508400002c617000e5031a28001f080055a40c0954003000032941c00824155040552020b03030746074142c0111200a185c900b929600d6a07c451038650070905503903001a40903003500100d112b54480340c0001f80c03c02d0301c200700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 167880755 1250 167879505 167879519
    0x6171f0e1603050a0902010909050903090d0b0402090705031302040e030c0a050304050316030b041b09060e06120d0f212c010203040803040209090c130f060503010c0203120a020c0106 80
    0x7104111266020090359840c6200e50301192180a00640020f6100b8401e0040041660080d0b40bc4400c14040341c0c14104584000723204183d50b4601100e221514609102c1142400315002c4d40100b69420494210320703000740900741d00c011070320019216607140c0d42c400c00150002d204a0302c0c0c500a440643d40d5442a900300107035240c2c80b178482c3c039000f80b103010240e4641500907058071042d49d9114040800740d484540b61010300888c12400c503000340018170310000f42c242c220b03c180c0001b4240810f1007a01c5181640c1082502d21030070500070404e801c40c05501c40819484000d2024203100d900345840c8850300050f01c25510400301401032103047c9421910b544450081c4042040d500450058000d9110450015801d03400140c400400e0b0440a1001c1001031601c8002150b00441305401c5a0050160100044044410102c035100e403d40d02c8032326080b100350500079200a00020b0340248019401c0f00c000030340d00d2251094003d495544540410445521901151030082008000f848190b84481d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 167882005 1250 167880755 167880781
    0x507020c010810151428030f2d090204050f04050607031e0905030d09060204060e06130605090604030b0408120106021606121811030706171f0e 63
    0x106807408544000c0001e6940750385401410142d480130900340700280d0082000762100d0081c0500d854010106220880d003030742e60300d0803001c41a50303d400300414241410201604891608a00d04505402d15000c0c0d1554410f40d940380740240030350684840183c40400c01c0a004180d10600254841c0c1450306000b01300c4032060304140200d010fa401ea4169844040c026070450711400218400c2c048000041066009990320141c1c0d40c900070000d40e0724000d401e80f001c50480d20700d070b82d08441541c1d003c00c080c001345d5400b0103140408a0700390b4686140600c0c1400542514655201c1c0d5001c001000481a03001e4a680c4142c80042d50b00401c0c0c100541440c1c54080c90340e800c203010b0202d0620700b44000042c04c1d4400078008264035030074882040242d0424400312404580d0801c10340e025030b200c0084003000b081c0c08418401d17850082031204840300700c1130101428221941d01c210200500320800121211540b00e05a4200c0b280d05c8040420280d008101100c0d01d0465100746d91141e001d070100002e501800d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 167883255 1250 167882005 167882023
    0xa1401030b010f270b0d060c0f020c0117010e1003020d030206011517130212070b0c190825080d02130509090a061d03070311010c0c0305190e04050702 66
    0x1003407000c2419104c03002c114400c102050011950050303407107090307030b0900310b50b2050805e031074081c10140520920303440305400e9880d42c020400007d01d44d043d09004c001c0c0c0c103000800d940102483c0140342000700361422000c00b10103011f4a154181c11001260f0160302d90b602c0f100c010340e809400040c6182c0c403400c1c082c0d1114024810308015248810700944400e02c00c10007aa09810349500203440c544a20000d805e040071091002c981041083e200c039000840100141002007054407403030307a581c0c3c08c4c203400603041c202a80804114401c0c030252010000c3e21032402d42d203813012007a0a8031a641050700081c00c101494031800b4210050010750130b2140c8510780c0083c806000d9840500b803000e03a984042c84030080d01101c51001540194000800045868100c18001514081050001100c025803d400c60740700300d4003200440c1d502007042200c40400e0103400005c0200303052004201409440182a600c41d00c240c031002402100b80d0320790f03440d01401c10501c0c1c07000301810402c490301d003403040030f9a200440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 167884505 1250 167883255 167883269
    0x40902030a03081b1c020a0e0915030708010204031a0a111809060f01121a18010303090806101526090705040e0319020717011a0103020304020312030a1401030b01 71
    0x2514960b00310142d800d04a6005c07007010a6207401104c882c10f1090021740040910350100020700204818507541d2035101c6000f81c0381c07001030b00300d41c5403d80105450806980c1c00001e00c1d9006100410104e08016074004411600b623509a01d182d9440610000401d480d118181400c08042419001c24010740b12013522407205540c05600750320348404001224100c404d440d0b0004038144500e0411038281d801c5000c80e45005201322603814802000076092401c44103000c411541981c00420516a03c61045001460088041d04187c14440312482072031469000d90468140c8090b49444800c1c41012010400303000304030ba45a8103000c13501124004201a82c4004040c41202000f00b03081c41e16100314160400310320000c51134884180c51a0a1492031460030f1420350060b030400003961000518a107102840183c000100056260068512120407018050400d0310500c100030060300d0010340786421a800f176010755100c0d0340340000c55000c2c10029441e244a41c4c61880004104038490380440d05a80398 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 167885755 1250 167884505 167884531
    0x4060501020a2109081504061116020f0d0605160e030706021e010209030d030504151103040605090309280815040602030a020f0a0f020606060c0703060b040902030a0308 74
    0x2482004a9030790a2208001c0c0a0b010708800082e00f4007400401c1103101c4025040c40d900c401d0340c400126041c03414a254588014104004000c07c01c50b2070700c607140c20901d15400d000c1c180046075552141c02c0c0140d9100034003400c000050880d07a40c0d1a04211001942d21030701c18802840d03d46055401d2642030500c000109003005041889441c02207000030648909600600d00402099080c81590405d4115840c10795800c010b0f03402030703880c00d0026034503250741034030301150034102450220480c8803220000b142403032800f06201c2d0111a50780440b900146c00c00c002048a4440c0300c00541144900d140c3c45610020003c00c01c0740e001000700100803100c0792209103040c42c5946103046602d4803910f5001201400000c0005000070b1002d40c05544c011455000050509503042c01d40d402a038002c42c650350118903480030969080c1e038100001e66110b6410703998039040800c0c140c0f05d60b0390b400c1c090000900761901c8404443c00e90302c03654098056650001c080b68821402c901b0042c24808003560346030401c801e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 167887005 1250 167885755 167885759
    0x91b010e0d11180106170a090212030a090f0b07030807090f080a020109080601061e0908010603030905040c0f02100b01030912110d020712120215012c0c19120908090406 74
    0x880036149812544c483d1504050340303400742c2d0700d03022806c0010f11a20501d99180d00180240e02d514081c000307045c0105001b541e4851042d403000d0015000382d44910f400fa11540428000b45400e5400d40b0010b03a890300740004d040e220303040191400512071704a12092090110000b84006000484807102c900030380315070b001551a03c03465626288240142e201280440b2a078241c070140c0d1402003034a00b02c0d10316201209540f079034850380c252280c40c2d100394006196183d080c405880c2a100d000004051030030400404003000e60701a450700c8480400341455540d8105641e50369011b0f800c2040c0a6503c01a1080c1c0307400e02c09409007101e51016a080340c0361003171802e0451414000a0b50100b5244110701e0242994902c1ea100070a0343c240b0744c501c02c2140903039601020b00c88100c3d0307080d60113400e40100491405800481000f9071001d5011140c0300d40600c6c2042c13200c0644190200e81842d1202d080f030a1a0912100b42515165141990300007a9031400f003010040c00000d2000e040c4901782244d0601c1015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 167888255 1250 167887005 167887039
    0x6020f0c0609010b1002010216080a140a12060806070e060c0115180b090411090a02040909051513031409040e0307050601050f0f130b0a09020a05041d091b010e0d11 72
    0x2026410614270014078403c80d0318045000c0754003420740c0141701c0c6030004003a800602c0301c3c401904420344480220f1080034540311140c0e801d004070b4005e005408028209481e0200d0f00400d20000d02103410700505001422400700c500a402807005541100341c03202030a80c0e00c00094540c1c4c0958508281c14a180104006c014940596000d02030368100c60060038481d0305004004914002506200025508000c00201034515000b4550000d01a1019001519500e8100031303003000d008060222006105034090006500030400700d19440001c1d0390b454542520201050041020600324207040c40040390359002c00100042c65416030b6020b032a80762041d5000414403550705802c4054076806160741c4404812300b41d46600243d500c03c001061550440e68400440089a001c1d5400100082001905000490405480300040e4105041c08031440c500140115110b111400d40c40030001e00316030b05000141c1c468404912100d0f401481240b800302c5a18003e1904a440b18209020700500c0391142040d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 167889505 1250 167888255 167888257
    0xb032205030301030b070306030605010e0720030a0302130e010e0405070b0a140309010603020a0801061a0f072004050a020406030507181710020304030512100b040306020f0c0609010b10020102 84
    0x4954050011820340e4210369820398808001010042010307681c0d503001010803000d011f10340c0245242c01b8040d060741005a40200304a40c0720300740b0300840300d8010f00303811281c0c2c00008031114075185140042c2c560b500c0344d50018417095035501622000c0c0e800c01c0042608280c002d10b140c00381c2d210f40b00300d9003066580d10a0074554041c1000220109011002d03c05404403603400955006c40c0300d5000040f050386a42c00546040d02d503400c080c203207a5450700180300b46c0c85540c3c00d60308240c4201d10301c58101707030850984000903c1840001400b041540b45a80c4614401801c40b103110748004001788034501c1d08107503a00080d0000e100d080c000a0400d00414aa640598081c00e510700c0c0020f441400c1c80c2c02e103865184240030104070b1001038446d290b100d03c1e010309180302079801188641e540c1d036500c00326840c010400b0709000c0e06103410707181e82d59070400017400079008440459071700510258880c0700d04a04c0001a001e10351242c4014003d1408100e00300382c040d400007030807000885010300f16016009040b400c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 167890755 1250 167889505 167889571
    0x90501030803180a06060305100e06040f0219120303020915070c0306150306050a06060216081507050d18050106140f0609040209060a0f020706050304240f060b03 71
    0x4490010400f10314118000c20f01c800925080c20229410350800b50b803038500b25000fa0b8820b6426821040d1803500314140740c0501400070700200003e01050400d07032540c04012910040081c4070f288071580301e1240640580960005010b0210051447d1095080280c042c0d80f0005806100d550560145101c046040040d0740c038003504566183c10484c01c5a0f40c080c0140405c1020f070b14800a800c10010003e082401200c6c40344502c00c002040c0b05280043c040d24121756603030080010301e15420248001c2078005409545060180340901c2191200a41a00e581c800e5841051a042c01c0c61044420503018003c640c030540d100700000c100d010350301ca0700b0403144901e0010080c1d01041d008c00300744442c9040006000e09600050006140092850015100c1d9000e0b410b01c03001702d1001e00701c050301c00c1d0b0140440c0c4024480b50804a1030b610701030fa0b5500d0f0307540c601d03074840d42070a905400200148140c0ea026507074000250804100f00364580c10340c400d0355082218908801100c41300d002c62032560070002110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 167892005 1250 167890755 167890763
    0x221160e01180b030c0411070b07030c0206160315060c1203020315060310050a0e0a050601020d050403020907020c0603190b03031305090a020f0a09031b05011b030309051c0909050103 80
    0x34000000300790000342c03002810040c1d140c41029801c112550301c0c3d10820050030031101520303560b001e48c0d1038480310b00368000b03040744145480c0582c154000c6801140441c2e202080340c010320000544000141e00074010300c00c80160a40510030003081c013075000080170444901072000c041e04400e80707500071020f0b48007c4540140c100c0701407100900c02e003800c1c0701031034010400441c404401515000820803600960788100f5003a0b502c407046c026039518034880e03a41c010800b03101a200001e140200a441071180e448028090303849840020000b2f8802d01015098804c0103104550f80c1c20402c0c02401900f0008942c0000c0d40d191a0b40302c1c109140010441d1010701100b00d800510f0703441d15040000c00c000c002c02c050708050302042103070722200e03207000100030381c00d4503444682e4814118146210415139444011709805101c0506204d0740ea00001307500e401c81d20804a403c00540f0501c5d0031170244c10030300001000340c42283c030207100030014a41140e080300c01a03501c1840d6280d940a6200565030300b840094 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 167893255 1250 167892005 167892029
    0xd0602070b1608152d030109030f090f05010518040b191a090a0e0c041a1201060813120c06092a03080a12020c03160b060406031e0221160e01 62
    0x910001d0400d401700400d440102061042900203008203003540e404c07420860000f40710540384410303190424000e40c043c00400008200313207800c000000c1d20750300c690340a102c20340400d03142141d6956102e4201c0010b84001403d01c14062103003940311412403160f8000c1d0f03009250002e01540131940800c0a841070b21030024088000340c1d107048c1060100440152000380051410880807907500814031441d1101949a1a40e0756100240c401210040d02c060304007108101d01401401a28505032005210b280e80001c0320114200081c802511508648800107090a06241e603481c103000690403203480c0d180c801c0800ca089403030f48503010001410280001410350740c2c01d1060b0200c9034854401c031695410041c034010314000c031f100502450350308008007c2c103030070210220304405c11400381e400c0c0341c100e207003a2401c0c84424107558415601d9101c482d112212003011217075050555071050040c158102040f007203201c2e050794001c915611107892081240d03020702182d400080c4041901b02550403502240050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 167894505 1250 167893255 167893279
    0x5010b10080a0203061507030914041b030b01050405130603051005060306040b040f020a0305010213050609060708090a120317070c0314030a0e0105070315090504080301050d0602070b160815 83
    0xc42e000f500301602260300134408000784110700406000070600c00740a51111408c8500d402d41c0d00071840102a00c3c00d025605001580c1c61100c0c3d6480c642800800d18280450f1090086004036090b00950f8001540a60140e14a21200d1b90300d41c01041a0b0b8021016030740580b405030506019075809403412a095880b43d4000350104054041c0580c100d07200c2e801c0550510b041d5000682103000c40e1b0000d8680303941c00141d049400c03282c01c01d054010300007034441d503040120503000103099010302d00018203e2903001a0250541e6144003040000d010a4503404211140300d040041100441009034800c03500d040740805e123641e018152961240da4541d4030001c0c400c1c2d88a82840040d00058541902c85031035154941c9d07003000a01400e8400c00095074001043c000b1510005202c0300d140d403001e0380c2c0501d00818080400c069004072415601c06480f818201c08852034850001c2c851001d01038403100116060280c0c002c81407500c641802c640713585424036502e0f440000c6c0c207100b000c98113071070707100f403c02c420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 167895755 1250 167894505 167894521
    0x60612022b090b0f06040e06010803220504020c07050102250611010905060a0c09050105120a050403090305010219120c090303080601020c0d0b0603120309060411060d020703080405010b1008 83
    0x3880103505500314000c66190142d42c0c0b210003612080e5028100e0701310340c0040007254145031050320031222984000780100d5240c500030030b880c0d2290410040506240d1309108109203001452207000b00f5015104554440c103540100303807104803c0c0942801401103d0b8080c2c0d910520581d50000c42d5170300703070648030345a00e4481d003034546c9180f0710b840f03010715500c46607504045002440514890510900c000c80c5008080000800e0554176801c0383c2e062000500c901003101d1400c0c54600c0d880541100d000a40744c4a5003403c0d11205c005600040256000007450040c94a0385101a00300705c80039261442c1d0041c1c685034450a80340c68480207030004003940c40030404a44a4101c29402c9841030050f1101400803002055000034005415a51600c490092002d00d0030308010700080e081c090b80d03119045017022400240c580d000588080c24a000c41d0840552a0360340c40100d03040c18480d400c04558944035460003401c4103904503070035103403540b07040c2001d4428140031000030080340c465a200710850384e415031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 167897005 1250 167895755 167895817
    0x19030504020d020d06060501080112030e09040c050909010209011e0c020f0118030501020304110f10050c15180c010207080307080f04031707060e0a020906042d06061202 74
    0x402680d01403850000c2c40050b03240d513844040d8190141e040482d245080c400003400801c0183d110f02e007a50b40b85a40e14001c640d122481500480c0222111a880d40b1181000c0340c1020740781d0441544421404184612000154005c10b01c207a820703240d41c000c0301d001c00400e20325120b442d00000007180c0e501d050007006142503030f02881850014184910416420783c1c07400181c800540040380d450703500001340403c3c007105404654807102c0c1140c442c0c505000391804201203440034007012044c44004030703a00751406428003107011322103078409040b0840c1c0b400caa02d881845208281091060282030145800c80d44041500010354015000842c0790a0440c0c0d56000b40307612448403070404401c144800301c0041c0182081000c0a848144501d483e1601400c101040b030301d030403001c204503030702001070180140c41d480101540020300f10750004000080541c00e02c034092580244983c403180c072941949410901d41c0c00308068801c40c0c3e8840d03030b01d040c0350002c5004074881c190075640425607141c000c600e00f2070380c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 167898255 1250 167897005 167897011
    0x411040c0914090402150a300609200f09030313031401110307050c030904060303091d10030602220f06030c02120405150d11030f090a03170a0603140102070b010605190305 75
    0x403418442c0f0b148c0440c7c0450901d50842041c81c00c1d0300d411002e40604041c240200c4019040410b800c20405a14020316500646010b016040010300884c00800e1041540196a00710b28090140c9643d00040003552901c0d40c1e40c1d00003242c200c100c0b400116200c1d44144105080d0040e01c0072654510346480900743c0701900300000380c02ca05d10080042c544c454486000f044001e41c8661542c018143c14201d00c51f0600b460240c1c80340da80307a40d0000b0840300401840b034020440c0e403c004016030765081c10110104070020354404660b0409a90310000f000e406000e108030072106035a40401c42c02c2141e4004a88548a00d03140422010f42884140030320f241080b169600070060517070051070301810183d900c2c1581c00c242c00c0c003501d42e0404401c03c505400c42009003a8054200c0002c0c005100e40c0c1d070b6004e06299078842860016030300c60400101c40c801c00c0d5000001441e040350782801c81441a10711140070354454441200d1b1440301c0000041c0180c0908161362a00600e40c0340d4440000b11030303908600504c001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 167899505 1250 167898255 167898257
    0x20a0303110d0e0f2a040504030509090f070806010905180901150602030c010f060e27030c060415050c0d0f14130605060109050d0b0411040c0914090402150a 69
    0x2044482102e105900c41c0240303030a80240603180f41c06485a40303c1c18405100d40010500c03151240303654540004403070821600714219000507182c3c4031420200c0340c1c0d002d040141a0400035480501500c1035030070030014441c2c403442c2d0f5511004d50721540111380d080e5141c0f003000d412400011030316818400031030704164450005000040c601140c45512950003140341d120001680000a0852801400380104203070402600e1b01070001900e04294142040b40c01080506409280000f0402d6002122000980d00f00c580302100d80b506101c55981d03407070355401c0d68110b58000804d4051029800c3c03a009013403003180e5041000307042c1850031100401508240c1c020000842e40e822400c4402079540c500b5070300825059444041d0650246030120841d007014024505100c5a28400c02069a072814520640c5030b106c0c5c1c04001548940c648545031150910003154041d0800c441142d402c0c3d4440407035400c0703e0303050006810f5940340f80c040c000d8100040c5d4010350040040c0030f14071700842c41d1100400e400381c49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 167900755 1250 167899505 167899507
    0x306020d090807030c1106040e070c05100540080a0c230f0c0a05040207020103020f161a0f070516021203040807050411090108040804030c09090611030403020a030311 73
    0x71962010b0082d8011001180850084442c000511403510103030401042e09449062905090903001414035000400f403508100c0803a8411080183c00d000c207000c000c40d10803041c00319051903850900c2224100301c400c0301200240c210011001448003201070044000764001815100580301c4000f02e40c00070800109001c014840007001880304400302d10b07044040700040008510b2444150308040f400d00c0d00e94825404103207070b920729903a00718101c811954100c50050f03a4a0003480160040d006d010041082c9500c0410310b19603a000044803102c40d5031017141d400c0d81c072502001800c0c95106e000c2e50040c1d00000e5202c00220760714092402082003500c0754640702c5010080e92300007460040818010010f03a0808141007100c410108585400740004850511000c81403990600c2c1038086d10101030b04000d611008142882146422540910b410490601c0e8064503880640c4c06050054011146286001c4903000380e074001005890096a0641c09810b9000450f00c04a01401402030b4503001500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 167902005 1250 167900755 167900771
    0xc090c050c0d0207050103050f070818101803020c03060f070318080a2a0b0f18070b0a3902060d090320070501050703051c02180306011406040306020d 66
    0x1810094002c14880ca5401010424200000103050b2440038010380c00e60308041c1c05100b1a01d030811030b102e0380300d4240b400706502080700c4071050303151181d5030310160380c03d078034089500ea84056001080c0e8080c1d40640c085450070706483c828141d0364601140ca2898038041c2e240440e00440c40394100c20989401411502c84540c120b4a90714680e501070740d00d40c40491498680a07400800782c42e180290800c4d503892824004020341c56000c420a40240039110041a00002078900c04c0c0382c02da050300410760202160b54031915000320045a5029810140100759070607c1c420001d440d8800303c2c601e0382d4960342e0002071001c14501041c54000301c080c00720387c8030005010b40c0143d400c1600c07600c00f2481c00b0395100c00c14940d002c00c0b01c7c2070040b80c0580c41e81103600f10042c180704c00d0343c01c0310894200660500c0c1003607403103c1c665003217a00c5c0e800780c1c414016014000200d0700c5c004c480700c1c410068a850118103442c1180d82e580e4a9440c103140b00a686a000b0301c05100410105091341c1c00fa001a1000c40f0b80420400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 167903255 1250 167902005 167902027
    0xb1f050604080105070306140f011115072303060a1202030f010c0302070c09061d040606030b0c0406180602120a02031606060f0801051e040f05010c050d0c020106030c090c05 76
    0x81c11a0b002108240c2d5680308001c1040da0500480c0010410307005c84003c2c03507400c00007184481c040c62003601d0601594200d4055010401c025081d00d400c150a00c0b0142814180b9004000340f0000d500c2d102842200c06502c0743d24449001180d0041070010700248420f49030004031003200340d000006a9040c0141850500300705400e000701110b03400c081da001aa07480545c80d00300714080d420b811850009203019400e02c4041c000700000001c81e500340741c1015150b5510b203810006450707070750030061845900300c0901141c550b00320003800a4403000d84407514940c10000e45060404802e216040042e400000281c0d61020401c00500e40c2e2001803058034078205044490300c031115145a01100d12a969078010000e190400110380090b1002c60700900a80c1448030214442013072021000700403002d143c000c0340420080d202140b8100c0c3c0e1180c020f1110b25a916070141c2560020b4100443c07441c00d02541085191042c46244252030b88440c80b031500b1810603180b0802094002043c00a100e81045141010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 167904505 1250 167903255 167903257
    0xf06070b0901020310060207031208090304081b09130203071802040512030c01050f2806050d03030b012715111204030c0e01080c120c0604030c05030d0801030b1f0506 73
    0x8908203800540c2d41c2c1815081004005c4c16179000000f150030929080c070000d00756540d220004c094503e0b11107a241c13030303224003103056100399807020030030f8031410910069030030b0b031481008019007040b5400f10f00e82e80c03191440c4040d04601c1000039410f0300620000c0c865041c80100361590381001c0c0074014102078856000c00d489103111100010749030700110b0b400100407000d00416500c041080381a036542c1c242682e41c1c030a401c655807601e0362102c5810900203090b0500743d002200401c0d0052408054007081e040250080c00e503040c01500041c1c0c4000701c20300307030004a412035882e1050745510424003450480e04003400c0c2c17507049014042003508100080d00304401c11100300342e10304a15000c2e40d40d5140d89080003070450b2a0340485001d409040042113561390201e80c40e107080030143d40070701020801104050805036001041031f840500401c1c0070003401501ea441034144e0320305404039800703a46400070540d01d10009100c01401941c03844c0004445c4290a0740b000000c140005d141e40d8404d031250b00284031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 167905755 1250 167904505 167904511
    0x20c040606050d050c0f0d09061506030e0105070207050d03030906150305160504060315050709030c09020c06010902030c041a07020306010303050901020c040b060307031a0a0801020a0f0207060c020f06070b 90
    0x5000401c501a4030b8656109154028102401c82031412000c846e00740503c2c0070780b140c103074a001d40e24142d620610a40b600035403041d0080104456100b900d589014000f0074218090051030740c80c000004415600000c1c0c483c013500d2006103481c054206982e13040f0064035807800201c1d10b09880c0c1c0000254540000c0d104405075215134007904440506032902242405542d0100c0d1140d81400410000f041c6020303400c59410500b400c000ca80fa9903038090a44601056074001000e90084a80000340c43c203540d4081c04015482c4800d8481599851048400f030f07020586110a60050400042296201c0300c0c005808820340c0d20810360424000ea000242400c000360f1003540443c07000034004e00c02d582d040c00760b40d000b8681110108101d02000000c40c00c2030100030150018980e0350801180803a54042007c42810001402156410b4451100354040e40000b00c0da9008500d207100c00300b08960011032042d043e01e031682e56455068807140c00b0012090303000194182c000c00708100c1d0101080d02c40700320901c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 167907005 1250 167905755 167905757
    0x303010e0601120506060306060a230d0b01030203101203020709051611030c0a060f0216110f1c0206090d021e090105030f03121b1602010305010902030702030910020c040606 76
    0x314514040001400080080021041280c03a0004100b15507440c102540d8010000390703030554886195050a461000e012000d1600b0408000072895107980800018484686074245c244404048680103409134001035454200c0c0c4c4151003402d100562424182c20341d6103002c0e104480c0e44a6407207408008603102a0394207001c40600c031354004d501903001001c03000040502d000451070007524296240c0ca581038658001c040c41d4481652038040c0501e90143e806010601d0580300d507036910b0b4038020381700e0400484070a026401100740c50800e403034002c52840c624211000780310400100c81c0d0801445600c200a5540d0020350783c154600940c80d10106c1c0b00d201d002c20980007080b203400a04103c81d0740e03c160302c041e100354041c401000f07500f03001005a4000646113481c900c0c0e00e803070300a03034110722004070341c500c1410031408900581c03d10020328541c0000f40c000c1c1c8080081c0d903200c43c81c800c2648404c8403080090380c400c118005807410038117000c44810314544103a5501c0c40c0420001001e40d1599030000c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 167908255 1250 167907005 167907029
    0x120304080f090607061506090b0d050720010e0609010606020a080c0a0f050303090c0402030c0a0804050a06051e15010c020907110d020c090c0c0a080a050d060e160903151d030301 78
    0x508000703048649000074141c01d0800000040c64104a0180c038030a9040c2041d15507100e4010441541c0110030de1210302007d0242c440b00c0c803012100c2c40340200384d2140900342c1440740d40003041e0003050621a407000e440350b80c2d005e00549552a01d8841d0194000800d102841c410480c88101249240071040b102c2c1d445a8043e40d03582c144624418030703021401100c103204506c10020300441c105610708451115181d401d20440950740d6003000da08150180b5801b616540c01c02e0b08100f007030001801e05101d000498017103103125854034454034070482401d041c00b6010580904400b0094602251441c0e8007010038503100d0711901c0c1283c405414000146402c0026034400b0065821519101000703c0d40101206200381c05d0103480f20041d503440581c500050510400040d64010b03281c8120100d0b003818801c48400c0c4081c2e076540749460314502081362048043d00e5096a0740c0303021480784e40c0d10001caa03006038a0303012151187d5410802000f0040d04000304002c0e041816031400814405103009210000341c2c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 167909505 1250 167908255 167908271
    0xb0310080105070824180c0a0f02030c1002030a1b0e010e010503040b0402040209030a050601060c0213140c03150409060c0e0d0302030304031b0605090618120304080f09060706 77
    0x10a09441028003140c044c0709aa0042202c60089059150018401c0d8034160f098200f036100452415440030b410304d411900002c080145d91040c280041c804502c6941d40d4034008106034104136100d000340c0100d100b40c2c0c6c001103c0e440c20418550007954102043c0c1c040014407402e6524207008000c3d405400c04045840c4215010b0ba42d038200103c040004002e082c000d05c0c51501d640c17004125030008100a1040c2c1c9d002c14041c03002d8a041201c0d80c44e0503404401c80f4050b50f1198005402d41c2c1e02003100303d10900985d21103031001111030203050100e840036441500c06464041d401803860f040140301c0c044803c15101c1411140e61903010740c48009010f580c001414071110f1a000b0140303100c480c23043d4090303001043c0c058002940001180d6000f601860017030b220a1461441c2d400303491000201071f1000f070810050000550011554500030301600501c1210780c610445502d485003011800d810740d41d9024400a401300d6481300050082d00c412813242c030b1625920741e000600076002030800b44c54080d030740c4030303d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 167910755 1250 167909505 167909519
    0x8030a080a0b010e06040e2e0311040207110d03022401090510050a0303120b060f0a0809060126070314060403020f011401090b0f04020d0c080117071a040b0310 70
    0x144046202c080c640500c1101014011501e2485948241c840f0003c0400020750f1006520480c070184548040d080d43c102581c5000d4442c032000315000542e006a0035021980d0f041c54188200c440a41c2e001001c503969400510411441c0d51201400360300b0750042c100540050380c001008600d00d10300b1345a01950950520442808890700200780307400036003605609001a035544d41107503080342c0d498a0403c03608030016174070300003800307010490039046400401c0000e074110b40c000140c802c1c05110307170b502c89199540c00e03195640c43d0000c1c459010340c0a210344621040c2c18515061020748103010f411900c00b25a00e0383c0c2d491540d6a000320015040d080340c0d003840704161381032041d0990340c4480c50080c0300740040c14084031000d10040c4140c044842c0e44211580c403a8031000c040100900e4014801c545070120102458050001da580e58000100d0080010451400880080113154410401003038039500307044208500135045a4421a441401d00002a00102c00d1004500c90901101c2d49001e00340f82c814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 167912005 1250 167910755 167910761
    0x90c1707150908191a150a030f02040513210201140103030201092310020c0c040e1b0402044b091112270601030f12050f0304020d0c08030a080a 63
    0x40381044c4d03550341616a80c0440c5440307002000c0d00086800d0503109440e203040c401e4084c90300b1003420707030081688070f0004107101c04940b8024410740255814403880c3d07184003035207508040160000707051a0200e02d100c0b40c240080146c40c440211540000180d00000b90b85c4a18890b00903070040b80180e4451104034104440b51800502c2c4550000751500300880b03542d5040c1c1c46110704c912050526601240c1d900e1100010040c20780384100240c0100300c140302d80700030507880b890712210680c0000310701d0b45d50091a0800c4e2003104c0c00c075451016400c410030b0101240030692840b034600402c0860490411060004802c0c0c1c1480c00958030f800c0e020715140c90058040d00b500c00c4d5219210368100709001561407170640404039948400703a07030f501e030b106030704440c10491a0603030900c964000c07481600008401c2240c81149291898041c921402e0154100041190300d48034902c42a00318a9040c004203005003490004d8804180c1305010a40310240c0381d0842901e9038000c01c0f03282c030000c0c20443c18408420200c0c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 167913255 1250 167912005 167912023
    0x9030403111f0c21120e0a17090402070b011202030c0405012601020f0f2107090303080c0d020307030b090a0b010903030c11060a090f09090c1707150908 67
    0x107101841000c900502e40c818034050030303040a0a00c0a640003000800960906540035020200350f04041502e6074040103100a403540b980c01c0b038403442d0440c103036480400028005030140d40450403821407139159001856a070410b02021780c10540a00182000585002c0701502920708a0344440b202e450b54010185000441580d60707005a18000041c042c07846a83d8400d07060420710400440018503e5510b14024854140342d000c004402143c009001f007600c0004001d021030b0021003102c0340c0d40303c4201380c103410400d0300c2c00c2000c500d9400c81000002d01501490744c1c020302e009400c07800c18907003038046016030f0f0048802f43d00003591043c2d10702d41480d104040b660450032001c41005203085420020784a94202c2c0005024408000402c008016481c49000c002d6000031b082c45407901d15200000d051840c041c012460340801200c2c0c081403206c401d104203069541c11400d40391045243c070740c10010146030081d4240980c0190700c008101e5050602d05412003103d556240c0b16418500620b103410180e0303003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 167914505 1250 167913255 167913259
    0x106062a020f042a09061101020414010c050c1008060405090c01050307050c0304050406140109080f030d0f02090a0b190e030307021908101401060c020d0303020c1002030903040311 79
    0x8015a005a201c400101d10b8211094030000780c0c0c078004410320303030f20f0280d0b800050000d107281c24910381c0201d41c0001804100c480030b0304c40d82c80d000300d00440e081c2070340070381d0050390048201c00d81c080c0c0700c944c803e03418012503601900076154541e0807040403520440210b00f11b03101282c900418090641018810790740d00605681c040e040b100a4200002e21622010f03101908102c408200045a0308051044074001e2900910400000d0303030f2100c0b0495900f042c0c90354240864806000081d0140d80403801031000200c031000303180b500c3c0806840400400360b00e42a0b0710f0056007400304802c00c0d03d66803e0200540b4010040c00e0300d40858910741f0042c550210700070800c200400e01111039540340003080d5030314142e040340c801241440100041c0c25810b0f15138000d0443d8415040c40e81c0f40da18465108951004008143c2c210350380c0ca03544c00341c0e043c25005500940103003c0c1c104150100b44207a0180990304011415108441c83c68210758081c1d0b001650310b0103003500001010010440c0360800008202c1c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 167915755 1250 167914505 167914577
    0x602030c1203071101140610020604050a0b131b0503011d030304060506041401091505010e030a03030c050c01150503330709090504060203101e06050c0f010606 70
    0x5000000c0e1100c5003400c903408403010220124100c10b01613440c00c070b4004139001c000c015840800c02a031191000c02d403400f030700440240440c002200c0c80828068480d6070818010030140c2c0d416511070031554002880340c124810201100c00010320328042e82c1022440d0b0550800c001402e0204050031543c441d440ca0784045000380294401200120a40e50710a80100340000d1030ba944c0c502180290505964003280d4118a1001080c0b907886503010192404010f002500340d00e07100c030015101c0002c50600c0e241e0540c0302c0ba1502c00003034440d412280303e00742546030032070078129200300003820b41c1d030110403c00b10b0001c400803c1c4420706081003140000c00c1c0403010500c09506003400352881c0c4000803400c004207400c01c0c001543c0c079802440100002e045003401000300b0300c0d2a0400304020740040da69414a4201410000303196695035100c0a107142c84a019002010b01e07001c0c1c00d0362283c0c040858a00a8007400200722140d80c0c0030700c0781e20b005000c42e84a43c110301c11480c000e907041f81010b0318113555002c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 167917005 1250 167915755 167915767
    0xa02010e0406180504080408010603081e030c0409050411030616020f0c0d1401090503070b011d0712021b070303030c0207330c061104060306120b0601080712020a0f0801060203 77
    0x120303d2595902000104200041503180c41c11700e414a8880e60f000a10b8542c01c0c00000410002054003c2ca001880303032a850208400c1c0940200d1039110644400303c1e49042408107001c11b5403141e1085030858440c00003036080c1e103100c80c0420b052003000c603030aa000c085502d0b078039640a80c051061900314646007000e002c003100180009080c0b0031038240e01405404110130900800b040035401a02c82517000800c03203485001d245031010800e88c00f40201032070245151688074cd4030311000941801843c507616040c1c107280c0c0c031218001c000c0d04400301c0361800310b040d00c26028080c0024083c1c8000355000340da000c600841140e90281c644507281e400316082d42c0e0801d41310414100c208404d10301d103005008409996111495089488600c04000540f030345103490010300e03640314054000c108540c7e40d605d01f07000d000c1d1340b1900000024004a0f02400b20f0719200005001c540c4104002e5500607903904010800300880742c0c880040360441403800010504c48c00ca00d22881d40c11a00b00da0040c0b03210710065151030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 167918255 1250 167917005 167917019
    0x60607050715120204030f0308130b0c03190207030921081206011709060610030b04020c0f01050702030702010c020f0d05060411090f16030b0402040503160918050304060e010201020910020a02010e0406 88
    0x60034480236041200600208486611010040d016250003140c0000c850074840c240d213106034003d96041c5440705004030350010000041c02039807a555059200c002d40c007440c02c1c0c802180c0380c150f44d0076510302030b0400f580c0c440060b0349036024111801002146155030301d40500050f001481d0464109042c880c81c41c00c206d010348e000140c26038404000e0783c0303100580b9407040050f400360001c0031100394441e00200b020070030004002141a01c0e09040c000a000540b20004107a0700c920620340c010380050680b55907080941800051103c5010014007100c070524219164241440c200b40c0d42100c1103104904651804d203880e4940c0c0b0f4000000f60303107000c81414500030840d28200d46002d2401455241c42080d90345503156070580c0c0090101a044e5985058004107215a021003801080c2c1200c1c0b0700142014004211940e181745540c0c80802145001c0c2096000d591400300681954119034003000072103440d840b17401c05100c07000c0c91a0010702d00c0d03112610014259010b0750802d603016500c0c1400c200440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 167919505 1250 167918255 167918273
    0xd0221010f060b2a0a0c03050c01180f050607050a12081b03070822080c0a0c210321090f03080f061c0203070f031109010906080604060506060705071512020403 70
    0x3c1c00354200d0514032402c2c507444c0c81e0420300c10000c00352035892540c0e0004103001e00450100750462090381c400c1003290481143c0003070400c0078000d00d034040654249c01c0c003103824210300800390940114101d03204040c40c0e07900e82410102000c20900043c6503007041c4500058910501c081c0301040d000c002c2c0c218500342070b0090842000801b42d0003020350f1800202c08600150000d6440c80d0381002c0d0307540c0e4400000046669501035180c086404600d109400202002910440105c02c03048101102400750542c03021036104003e041030149420441045a06101c03841c8102d8484510441c030122900c412410050184800107181b186120100b104115140d80c8001903000310f1840070b280e10310940114000b0a01e0014650030406c110700900501005001c091810798807400021145200d0aa0302e9500150a031120b034400d070000d80c1e00c81c5011800003043c40e04259800000601220304240203621003514004a542c01502948088094482c20381e03407005280e1000142c1c250194582403550f5261080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 167920755 1250 167919505 167919547
    0x70303021906020d0e030901231204170a02010b010e0603100b03070c14010506030c060c06011404091208040c05040e031c1805060106200c0d0221010f060b 68
    0x5582070750900501003000e02d0b0306a84651000320010800e0300f010280442d076a60000a071180860000070341202040409074032a40c1400701000301506040080448156859000e881221888849110a0009075001c40035003c2c41406a00101d041103101001400805d03d0012003805610304000f0000007125480d64182180c99a0317035020b03a01d5070fa411701240d80342064000200703502c40b07035212003007402415004980540707021800c7d51042544242005890300c43c40300440c000f03401c0130f001002030340d0040801a0a085010f000070800007419526620101400f20800002c41e07070b44001d21003440445018880030f42410340b0100943c0780c0f100304407582c034004d0710280c080e1412001040c6c5912503043d0004240c55002a00b0802911034500c3c050703407660700c00d009400000c4d00a801c0140c00040d0303c09100c00148051000d800c501c0210414400c006001e0682039070028000440002d505034640c2c0544803038030f0108000215144034800031426500c0070b41c0034011a0405020a001900c1c00d6010010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 167922005 1250 167920755 167920783
    0x1608030f010609051f110a08040e010e0105150904061203020102070b09060c0906031024020d02010506010915181502010509070b0f160501060e181c0e06040906080304080f07030302 79
    0x703200845d901c01103483ca03020800c50001c500038851003108200b054009001034645010407140340380c0c0c0b00c201c0588003400034490305501103650000e8041b1004842d0040c41d4505010700081155074888442c40d00880e02010f040300103030f40c00200320040c0503820b03801c00d82007111b002c05883e04d403c140140580500882c0d0303900740304280000204a01340c0440856000030403400c3c0c00ca9450380a005a00180d52500540485c00f5008102d0b51085861040c42101d12424050311840000da041c1000c4195044103a9440000c2c412584802010080d40c0b5500200402d203034194101646074104009096a0300507000c0001d07588110000c0c802007000006494118901451aa4982c6110900b0604400814402501c29481e000000c1000601400490300c10b60a11030602d998140c0c10207001d1b41c8440f8544014000c070415081122028400e00d201d4022007001002281420b8036009120221440750344160501cbc0d0000404000c0346400f80950b0902620303d8000d0500945140c4001c1d40396101009040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 167923255 1250 167922005 167922049
    0x31505031c021e0a0c08030708031303032004060905010207080a1407120c150c02090402091b19021903120b1201020c06100503010b03120903031608030f01060905 71
    0x41d401d24401c121012503060006083d54000412003c03040d140c1d20880d005443d114529113012411400004c00c640456510404452070b6039580c44900c000301000344001c404041d21040990300c1040c1032106440d0b100140008555503074984440504000990b6000c2419034110f0f80d4100300c240303004602c8010003504820300c51400c40902d0019400d0215540140c01c419982c840351209000301c8030800e83c16101d10311103034444c503ca404000da03201d00758030f800254840c94400018005041036480c1ca50043c58a001544115036a03003940207441c1c200c041c2802e003503407405843d0284035904008407440c84100e8000c0208807102030314010031300840610148481d5448020101090f00d034100111554400d4070001c540b10400342035229101c910546040614010303c100110366450706106008214000500400c05580450040145a004481010390602050168040b1800700c07481034a00706100d43c02c0c071592881e003503007075404007a410380208041180302c07501032000d901c8640518052903102100c1e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 167924505 1250 167923255 167923303
    0x606020c0319020d0507060503040605070302040b09120102091c0203060a0e030d051b030a0f0c0e01020d0e0a0b03070f020f011b0c1b0b07050c040504050a031d04020a0f03150503 78
    0x1c18441c0d580703980005c25501c1035440c00518564050084c50007288628130074030030794031001c00c02c6007030340118051501d80c0c9408000d48401c900d070050010200c0500100054100b84044000401c5080600420044a0b01202840d021407606200c4141e21034000c04003000202c25031f0f107080e40d40340191503030103038a140ea03100030a505002000c0c2c83e0001040807902280d0724078083d40c840c0084c10740403507148403550809480c0030b0400e00a10f42445a44011381c02090558416081200c0c4000d9542c002c9400c140d44c07040100d40691071100071803040d500354851244090207040e00030b2070000303408200749250b407500c0d030000c00d0114240051021300000e0300d440129100e9a00701200020f078041c003000d040c440418400225444000b01030a1050b000740250740607040e82100303000a13035908480c02407107030304a031000303000090060400e904180d028030820000c4514090101d404c84e4002290701d4045400600c13802c0341302e5414041c55035048401000170224078500408a44d4803d500710030449544004840c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 167925755 1250 167924505 167924509
    0x70b0307030915110301050d030504050d060b030616020d0f09080f01140a0207020307050d02031f0b0a050102010e060109090f0c030308060a140f1309021512090601290903100b040606020c031902 85
    0x52f600504401090b142504802d440e2600091529840d528080e000c2c03600000e4414090342000c501290341078021b41082e81544404035906030701c80341200244401d1500110301108200428110340a04000000c0c0d100d000e0400b17008007000c02011115024010000280161404212402240d4055a03084680840d61000a040040711021507401c0c40c07541c0d031040308811807900107408039102610200318036134952004a00361600c40c02e40480d140c2c011801045004115446004031a0050104a00c248441e03900c224120409900c00e400140002051040c00d20300311035920300900f600000c8100c041507842c0840e00035025200c89611a80348841040b003885200d40102c500181c1c024002c42040e200c00050780281d0f004400c5890700708800c2d50005e55000c1d400a281411307030b41d00c0030405201d0940c02c2d004c05040c407032040c201007040c28180b20b120b010b601c0401190b1751480c041d4001150828000050100300c0e010740c3e00c4401190712071000d0300060f45001c5074214020007041103420b282446400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 167927005 1250 167925755 167925757
    0x130303090201140309060a0614011d030a02120d0806060901170a0f090305030a0b0303040609120201020a061b030c020303220c0e0f0906010503071a0309070b0307030915110301050d0305 81
    0xf03100c03201404000104400c0c040b02044080c81030008140801070f241d114514401d5015000c003006005c240b03820000c20b204103135030301e861850f0b0200074103ca1801009a000c512505103030b000304039459000e80d450426944d0080c0810b9404142503030068140402240024660703500e11104c002695002d402241c0202c00c1900034155154041509020282c070310f140c010440da10071100151480c0c03911400d2405c9160100486007118025a1007007442070910030924010651090124150b00c2201080d83c005000c40c01003040c201002c0e4200b41001c60750700006002c1c0c1e81101c000c81b045400c01c100b04140c481e1050040301d0f182250440c0740c0c400900c51310f0007034906a016003080034032045000810100b101c00741c80780b9100c3c030341010944800f070b6070b0396040c9a941c0200f805030136201c015107003000c9103203403111015552101d01801140c900541e1084181060b510036118000040d0b21031a41d0300c00d000e19204403003a00c41d08282e04000d10802e8082040341d034001801080c0c81018250000700a0600c540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 167928255 1250 167927005 167927027
    0x71b0305030a060b0408030d061a0304080c01090b0a050726190b090906040212010504120f1206083a2003270306070e1002010e070b040806060603130303090201 70
    0x2014255170f03548449455607640c014800703000155040810200303603840c640c00c8018800440c000300a086440b01d50b00c0000c190801c1c40620025940c0386c403070700080f0340c90803416402040680c03400036160920318030091075100c040c0d0000d42c04a609090070104031003d4010b07164001500b00c80440c080e0300f41da031448003500310b441e03006511071262000c0c0719680c80c0115245002e98801c4908079110001030604c0b0b1300713840084030054010010100b5008166000303070b030031000c50425403404030503900c0142201c41c11181a504100400e40c84000741e542c111200d40c0c102c0652030304141080403545042503030403592601c59060030003041010112000403800021100745852103030320540c1d4540f541c0b410702c1d40a0714140d03402e05c0300088084515007064117002c100c00e80205080e40d0b40c5805d070010720040c050b40441d08500c01d0304542d80d840391085542c1084c0540809000010170003a40d680c58108038500d0b01d040604030621a0104100380145c01c0a4105107030b02580e41801c0201d0300070b46600050746c50300156 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 167929505 1250 167928255 167928269
    0x206041b1a0408160602060c160206131401030209030c120109120519080c0a2001020c0604050d021f09061104030f03030c08150904060e01140708071b0305030a06 71
    0x5940400c0c00c0c001107202500c02d0742d5400c02181d03c0420603041e405006030662140c000503030000404260006200c0e00186080040380285400110b00c66000c01c2055101c048a0992510b2804050281d4101840d50110300042440c0075400c200e40760b80000d44600c0a205280e00c036012640b1044214613003908014a00b41d00b0002450364002614405021580f04502c0031900328444100d4004241c019418a4020544c010817182000c0c02203000f035451800505540c54507000d035a61802044100b4002068001d003540d01408545c05c2921304149040480100c10301507420040a9203402c401e56404210462881c1d04042030000382070510b40000c0c0003900d00081c007103030006808024003490b80d85139607069100f0303601080364920824088804c0c0c40c096444032908011445101c0e0b0030b1070203075000754000d4010070000405e201d01e6200b241c216079040c042090456001c4003000791154020042580c080681e04103482440e501070032113030003540548401401e03c80d000c8041014116a40d0020001e0940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 167930755 1250 167929505 167929529
    0xf0409020910030302060106261e190608030c06040f1e03111525020304090c1e0c03140c0a0f06020c0c030304080d0302220e010504060b0a0206041b 65
    0x2000d650001d022040c003040d800f6201b00c80001a506100764000f5007501500c494040d00b4080200d1300c407882c4c02014090800c0010304128058100700e022418a00407200003802075074100d04207032480140c50742a407200b03540340c00c24030841c40f20300e4011511580c01588203801402c14802e40c94180d0000502080860803170340c040c08800100741d008076900c80720f40038031001c894101400007a054000031040765848551070218030a2a20101c0b900c144241120310780c01507070704164980c2d01020031500108200d00000c0c801c0611203103407520060003d01e2580d6a45810030881400d901e024002d004450180d4081010000761100c01250038440f0740b0710594008403000ca40c25240c10000060f401a1810f9819400350361000308181c58004110340456004001078450490802c0c0217a000750026800c0000d20240401c1c03040020060341d078000b000c0c1446c0300060000c1c3d41083c040c401141e406030070841100c041000700c0e40c01250001034450b803207913210b14402c20340343d000c0140128040c01d6501007084104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 167932005 1250 167930755 167930761
    0x70f0c060f031a0f12070306020f090a080a050a1b170105040507050d030c060c170711060a0506060d0507020f031605010c090f03060506032a030114090304050f04090209 74
    0x180c498007a000c041c090740c0d01405010007241e811000614009502603008140c20206015030400941c0c0d01050629101905d96440d1741351100000e82e03002007001600c80c0800107c0caa860314200aa010182820000070f20301c0d40302d150340e01c030340c0d0301e0383c800015100e0f00c100442806a044410b4800c805050444542010740d82c1301400c0d28040c20040d80c0c00c4445024200010600c1d00303204002480003038041ea601c01d03071211951070300001099000c0070301041010f6903005090703800003107034201d011701c5040d030b42c95a000c074480d0380381130030483c000e0080c0070200d003810140003040daa4081a03078031201043c5000038084d117801070705030700d844502c001c0301d1110b01010030450075410b12010040d00980c0130300020b12003118961401c80d19440d95004903200c10710b916500780045000c1e6404298090f5002d8102d40078214490800c050fa0074a480304c2c803684840036800c1b0701003410280600000e1703d400c0c0b828140e46085c80d0001e2030700d0b0300807070140c14000e03080100ba025040d40e864000026103600a001c40800b42 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 167933255 1250 167932005 167932007
    0x3050105060a090219030213080109050607020f060c04140a08010f1a0406030b0712140412120504030f1b02120a0c1d040209040318080105010503010f0603020a0605070f0c06 76
    0xca021184a4800c810002d0009001e6199008031103900142e00c16860741d044006030294001e411a100e00452041000808110350303030240705c5d82061601802c002d20081c0340c00c0301c0003413900c0c421010120b2140c01c03680c01d1004500032042034030b007580c1310600f0101c0c100d107003440400d03b814240e0740311074065828085403803e003c0142c2d00c0101400841c2c407205074141d404c0020320054599511004040c050f941001402c0c5a21485403c0e01c403c60441c404180540d10407049040310304183c034113031102d40c115094903180b9904220300748920005507030705104901d429100607110400c1d140c1114103018031070111001220170803184462440e40100446120040018501c3e9120321520b002c49040c2070380c0c48040b8000704116141841d501b05c40c01200d02c41c3e6101e03401c0c4403800c00c0141c070480c00d015001590441071211403813041c0252403102c1c00003440d585804c04260959900001582510745044000c0c805625180000c100780e40540c101071f80d940f280c516100d4101040c07607001406142c2000c0c40402d42c9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 167934505 1250 167933255 167933261
    0xf050c070f0602010f020c03040308031009090b062d040e0c040504120305091603080f09100c0c1203050f0f040f060306052b030f0e0d050a0506090a0b011a13030501 72
    0x2070381c00c40d80204450105c9507143c008a12030341d9000d800c940d205200400015401c40c008641c0003203010100007030703e5a10700c420019121092011150b0341c03018410014a420816807000c3d8604610781c440300a00001003110b041903010f840e03070306e004075290075088440080412445905001c05001001240761a050045006011103613160002e8100004070704180800190b00c280c84014800501c1501d145644044403640b040301c00c58070162043c04225401c2ea2546c0c18409558840c0e1140448170506280c2200d40f4800340d0080c641101d00b0f9241c43e0003090f80041502c5907401551500d03641c42e4855404080d50340503540c009250400c0600c008107a01d030b890b4001000302d9409503070041400882586000c001c801400c0701540c0d24041d000e40f500802d00c550b450380d411182034104080341036944000f155500d506410280d507507611410341c8008100301040000c0d4049004006415401d00701e56174500088410300c00d003181c0d0f94060007043d950080100803514018009800c07488103556034507040c0d020b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 167935755 1250 167934505 167934509
    0x90a030305090a0b19050c0c0901030b090607020d020d0810030203030310030303050604020319021809010b0a0e06130302010f110a06050106020c0f06031603090f081210080d0f050c070f 81
    0xf1103182400240c1030001205483c404040c81a083c01020360150044034207400c1aa89110207208141840005494103402c19020718081c41a004091515006041c03500f03201511410031540030500d86403415034080b4400c804c0c0da0030b624017140310703480d1800710840c880c240e6000030754140000001d02c84400081e103444000c0f40e100303480500c451b41d60001004200d00040f1044a419030b141202201400070a500901442c01c44100300c10401c1075500108414078026040602100d01c0011951140d503040ba050101030281240c1c1c00d03181018244c081401901c2c907100081c1400000701c01d482d41c0318040d042c4910f4a607500011152801410b04185014000a00c5010301500607a6454052410300b0365680150314400340031246580c54604110f6003103000c0320549410140c1d02e4241000040b2440c3c460315005000c0d40c2e125440d8011460901100140a0400e600101807504108207540000c243c0004001041c00d10505818401d9010341c1c01c6c0c49080360b08501400741c0c0202060028190b160442 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 167937005 1250 167935755 167935759
    0x311070e010b18100c0308070c02060708071a0a06230604090b030a05030706061502060f0106200703050303060f060c07060f051204061d15011205010608030d0203150405010e040b060105090a03030509 87
    0x4000d44604d842512710300382e42440a50070480411034080030800010007048514800c1506e90110340781d07844402585041500c0340c0300702c070f621460308000b04038030a80034001c44503d03003010381d0384098001e000442074443ca00c40c0007112034880c80240b50941d824045060801e80003000c1d0303030351804540742842c0200518043d111118100750200a0320a1002482c00e21075240380000b42038a9081c0324003034a6019256a03a205e08945901284104440a2207008021889000116140d007814810004401304068085004180502c2036000f0340000003801c400f110201c2c10410040c42d1074000c00c035001c0c0314580d800c02c0140c1000c4180810882164444502942c81c110b4440900402c2c415142e1915022142c40740010340d160014444a0301c084544002107108400000d18999640d20050654011000170ba203260380c04020004001c0802482c188000000c890400c034540c14601d0181001d440600701500d10481c3e040000c00d81d03405001180c2d185200104501140395903860000c1040d480814054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 167938255 1250 167937005 167937017
    0x71e0236060310051f120b07050f07030804020a09050408070b060f011d130e030d05010501020a02010c120c0606090f0f0203011413060f0e01030311070e010b18100c03 73
    0x5451840c0e0140c9029036030090141070324891000f40c0901401d0050820445045a1010211880411070b1030b400240a140d00708100c0400714246041e01d008000c1c01c11b03050040070006941000e100b0030844003215031508024200d926180040764900803650004001c1d00e00e04800c0c0030500c407500f00079003502841500d1203885507440c03100780b1120803540780101d80401c3c0d41030f8900b0501c048030300e80c0342580c10025042c0d0804c95030391240a01030b205000340e80c4a03690000030300e0030880300c86030007100d025080030700081101807916400201b43d0041a030015161241418648442c030f8440ca030800c9802d5084a01880129142d441540041c108200c84114040c42e140d0b0100001d4080c0c0207417030480f6051054646100448000d0045030788041a004900c01c2c0c1d100000b00c0d1103045045080050001c0201e03405441d0b0540c50080d0000b00700c0c040c0140180d011090030400340180340c07070f43c9054541101c03190341c4505100740128142e40c040c4440b00d9002d40d2030700c0301c401100e41c441c025090450003a03443c0c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 167939505 1250 167938255 167938339
    0x40f0f050603070f05040c1b0b0403021203010b190e04110a0201060e0c0f07020d140105010609060302280905090930030f060d0b100305120c03071e02 66
    0x2503510b03d610b10503c514600440c9080189142a9101c2442c0082c18140284144481c01e584455482c02034012220840d0322401c0c8024558104a5204c0040c00785c8401c0c1d1030355041c116101c01600621380385a01c07810690580400c2a031003403400301850b0038041c00a101024140d0200710003a0041092440150b11308000010a0607151181500a10b0108512454500941c100e480f1a07400040141e8000c966401c590001440f20155010b00f07403a0f5800006c0c0e1941012002040800d40d94050003c060043c0048800840303408111524a90108401d0100c150720070002d4550410651106500008500412560000203c0c1521303c442000b0043c2403941c1021340e460129200b106070104086105000058903140690101500508010410010000195500281100d048800c402c2d125032145e02081005020001d8910f0ba8607404411801c12070100394140d90307030090701000ba20101e025010308a002804200d05540c85e50040d040c00d0301521891860040002408071006200d81030500c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 167940755 1250 167939505 167939509
    0x40b0d050429040b090d090b0f130906030302061302032a04020c01021e07050d1206030c03050a022d0f0d0507120515010308070209060a0b031f090608060c0c0c040f0f0506 75
    0x307001c806c0111621450845401c04e17101c1030282d0450600142a60010400754400758058404000101109100402e9030750452130020b0804001071300e81c4110811400d42d03040141c0d4086070305c503240c084091545034030101c00c007a0460110f00f2400c105400520018400c0c4082c54107400601068007900304442450601000001580c81040c00180c0250416904031010170b2203101000c650321710030b1202154294981d1516004c0781d999500031180c030b901c091003078803c604005030f590240d14400412070f07000e4070b50040c00c1c0e04034400e41c04006204241c8840514202d546d00380d0121800c035040012904800c1d1215185040340203142400d9882c2d00c560701d07540002c01240c10030b046c1aa90301440040c00c1c40c00c01d41c00e10042d0b41c03000e001d280d4400070000000c00c9108640000d14850003016402030804c4002012813580c1004a07000941042c0c1018024400810009005030f00f001d684084c2c0c66458080040302d038205245403a010398410708140020400601c6030b00003441c84803e0381002c20481d100c0d241 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 167942005 1250 167940755 167940763
    0xc0c02120604050616020f030f2a030a0c020111030703030608190809040b01030902130b01031a21240403140a0e0114130e1506040b0d050429040b09 65
    0xb4028444e0703001d200040d80c03104512494004125141c0100c8001c1c1d6405c400450640d0400f00f100e0a0220300451502c3d2000c8041d0305090110701707111919150003c04542d2182c4030b100f41d4100d5030501041714074410031a4860210515000c0021090701c1e158021844c0040142c400c1d482030b103d00e413042c61610400c0f00302d503003000801c0f140e000c0c40301031429050700144005466a248001d0505603116410400342c0c880550843c81c0104c01e050015411503181c3c005400c82e00c48011401c84884181104140703074940b0458807a0103190f5540c0080c1c00114a102c5920b00408020120020780100a104140d102c0800380f40740103e1003a180c03c40c0342c54280380320312100e015421801000441c44c241482041d40649a4002e030580b40e1003455107425003900040e01c0130413550b032003814030031007080c108400035000b0034440c0300708182124220b107041d02d0309424a500307000383e5001c00d0300303c0c1d034400208040100c3da810360759000100c2c030040200044000c400401507a0129016a404200380c0d0005842d01004a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 167943255 1250 167942005 167942011
    0x10b03010e060903040302100e03030a121104061d1c0c06020d0f020c0904030201061d16050a020607030b0625060c2a0c050a0b18010e011e090302040c0c021206 70
    0xf00a60400f03156408000802e00c43e40c60000601c0400186900940c0703007403005240d034070001e8460314000f0f451040381d1011205c6003001200c00400501091011030383c0300c181070900510703180b00360410308088800244488410811404011a403545400400610301c0050302112259001d880261040c60000d440b52170a080070324006822140c1c0f048041d190103e516600180284000203403140c48400c90107104007400711840d94141c640c001c0000ca48010480c0c8175542c1c000d481c146050640e0510003a548000c050030040c1416201c07007500545032140015540c0200105060040e0a103801d2100150040900030a80e40d0509140e00c030014139004003c0c1c4134a444442c402c1000d000d18a02d840e01120038003801c100c0d0721982c02070740056550b48501e10007004c1c012140300d299864103104003001400d00f031805124180491444503040c140e8000401891a00504040c0c915034012480308840100750b64000a50040c0f406400e60001c03544a039603003000d284284c40b1510402040d550340d40d9602c20803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 167944505 1250 167943255 167943271
    0x1050d08040e04111002070f0f0b030f0915070503010e180c040e030d050f0f01060905090402102303190608060c130b030403050304060b01050a0903171b010b03010e06 73
    0x1008108410060382d4200740c0c0c02405000c188000d2000d1800013044804940d01c1400142d000100610a0305900303880b02008100c9100c880890034a4403800641600009064400d41141440040d00c000800d001d80c00110704a200a0b00303d0f440d0038600940150400c0c081d140c144511a030015011500d01c016092003030400c800245101e20f844020800500100f0f880412180000d222490700c07540719001e07071400b801c4444401819840c050741c02d01c400c114140d000e40104580160104580e07260355054942098047c1c03041e000e00008800c06a0364072540d1101d10f000c0f1001421f1307888040d0541c0b030155005a08060089941c0501280c40c80d09a55180c010040c1a401410100c2c504c041050020090100350b440a200d00315600c400040d100d401c11103003500401c2e40002044200505442001c061150908165091082140d4014648086400f00801c0560520b480311100384019041d00c1c1c5040b0361110341000040303210103044c0030307046119900f4001d41c201140000800e6000c150280724442c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 167945755 1250 167944505 167944507
    0x90f080a0f0801321507050703020f0303250c0806090c010201152102040603050615010801050d0819021f0e01050c16060911040f0c0e060901020703080306040e1f0501050d08 76
    0x2182c038114103901c4503070003d0b1740282d40d580c00c0003041c40701e000540811030084c009002c00c0c5103180107000e110301707105480c141310381c00400403c000182a0f00b0702103014000c141c407003190300d0742915045401c4506504100d905100f07140030031a942400080c0702d40804c13000e078028041ca19403081c070622088242d0160307c100c9842a2500d0358100714400114240310b000070070110f1159a2a141c00341010001d031142c110312150800104102d50300300a403140140025500030501c0d50705610313003400c103000d000d1840c00c585455000ca440c1340f5100f001140f035007881e074256802c1111301c816454001046200d03585207841d420500059108000b020039070702114102d4002c1c030403c8207140d440d0300051907003400c110303490504990381c41404d4480e442413950b80041c02c000001e0304952510083c0c4540d40d40e5410324401c1e101040182c1ca0340c0d901095980c122a070102083d42c032074440c40d000801801c1c903040d4020441c0704a900030003911f0303c201e82c07000031102034050403c501e980341c2003803006100311014040c1030200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 167947005 1250 167945755 167945819
    0x609050103050c160b10080c0f0105070c090e0c01030501150206040f060e01090f110409020102100905121306090b030405120d291201021c090f080a0f0801 68
    0x1020380c10540d44070001c1d551081c40c241d58581250556213201c20143d0300b02041358104041810400c0d07841024100d070600800840460308005041d80c440050f03081d0402002140d82d0007001000b2900c0c1f0050503102c0800d028011010b680c40d5076907001c2450300f6000078242000000e10031141c0000d010000c0c000da000e80b480350385640b00d5031402c40c0007000c1100c640b40c0d26403010813088028416665a07512503e44208404894101705654450301ca001d40d12480c035210880c00143e80002c5c103000300c0068404046680581402e049007480a1180c0c101c51503000080d20094642503032070400141c0303020b922103129003a100d1041207014001190000d24a602103c82c0c03041d0307928440c000e4045030150034000f05401d1000e10300012044800d15000c5100108150070890b18a0098042d011b02c01e1000c000b1030525401d07803a1400e055a00901028031030369588440d00c244880740580710340c40364002030ba00da500c1c3c0840c1c600404e403010440c03044000541150000c1448000c04001a8000c0642d05820503440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 167948255 1250 167947005 167947007
    0x2121c2c0607031413090b0916031a04061212080705032410020a0b070201021305151b030301050405060109030f0b0601020316030201060e130f32160f06090501 70
    0x540441802c1c3c05000e403602402103040c030f03200001d011841048000001c1e00d03152200c01c1080e03580099015100b40c243c0c030100300c00e804542c0c0c1512802c07c40ca15001c03840311208801c3d500350038505520745400a09291001c00e207003041c003601c0c1c840103101b9440006581202c41e0700f01c45400c41a501400066070800c08141c44c0080510f4a400c0070740f8a00102c201c540c1c16400255841c0241c114403000b40c1c100180701010b01904a854030b90000c2c550000358a03001c60110300e94a10042401010702c145c200904034401580440309694990301010000314042260721800b640d2900700f40310703240c803a90a01f40003595551080d0320100450741c2c840b510700d1641301240c2d504070380f01c40c000b0203140c11488184244c83e14001040e000e00e190a01a80000400c2401d102c0950307112400203001c1c4a02c0203502d0201c10006d501003010318607980d004050340e4098110f0307000c0e4503070711003402981059034003e03103e800c0d200b11804030741080b135152b05045008109503280c030341e1407006400780706010114031280e508104035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 167949505 1250 167948255 167948257
    0x3f05120d020d0501062313060311070b0c0d0c090302100503091f02070b010801061208030c09060310051002010c020d0c080d06030c0501021213060c02121c2c06 70
    0x249010400140c00d00c02600482c10446809a0082c400100c1c0421744c811118107950000c048808280905860818a03410f481d042014503c111010980c0d6203584580d140d00ca03409407061180e2042d0f5082e070604200c2071801544c3c1041c4180940c4d90b1a241020601c0c9005892132022a0b601500017001002c0840f01503030701c1d0f0401841c0c040c16004a4032a074640d201c2e00e0341503000381d07101e6480040c1c43c2e9083d814400c84a20058021003010781c9041000e002200d2010b98644400d94000740d10b0b0354990368215802040e000e03901c0312503007111b00030007070015800440383c0b044182c4c2c4095a244561000300381c0e0032070913100d604182d040580c001250000c0690310a02c4c103803501c1401030745030600d0034981c5c0310104112082580240c80303030380c1b03841800c0c0003540c0d06018101e468210700d0703035160070a202c80100100142c094441d0806203e03880d01004211344940402014050807171003540c0480e060040c80d0080b04101e071044000240d00200001d205602c01c03800b4030701e40384001031001032090040040c080c00d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 167950755 1250 167949505 167949517
    0x905011d0915072a080f0a02031e0a030c03150b030a18050f010510030c15030603020319230303130302030c0604110315160e0a3f0512 59
    0x414061000e96003910301d90300a5440c0a545582e1300c00100e00048101d4065040c60007076080e40107500c0d80040340206820342d0aa58a0700c540c61100c90791524202002c0c0e00d5031140205c00302c81d2150a044854111b10408040d014081c10354400740702106400400b102110103400310841020140b9a05200c100002c070003465200400e07e000207508a100026040419001a002c0712030b98010404020140028020103420115042084406504690340c80100d50450b015280c0c20040600b4040c1b122442900000000c580290030746041030341144202d440e48100b03030801d8424068207110304034001001440d018800c201c0c08055800d680740c0c552507c4050501403015400c512040c0300003000003800384840c0d8042e40c0700d0306115045021900074103040440407040420143c0d001410400c20b510324088108011301980b034070007400410080000ca40c1e02d0705400200c80180480103a6041800803088485202ca803c80e40b01540e000d885200078000515100c001c21030380007801c0064800c43e605c0050a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 167952005 1250 167950755 167950771
    0x20301080a170c0304120c0609051e010c0803070201020d0e06071d1908030408010b010518011803050d02010c0e030109030504061b0602030f0f07020a0c0510030603050312100905011d 80
    0x103d0f10300d10400b01440c2d034010350488010000f40c2d0200d034080180c410405802000c141c14924603081c584000105400564281841020f06040e03201680703078410004800c4c0c00350b101000544034101014003d000790030010500848524190b102c07410790000140e041d00c1640c030303540c1380c00403c071041c581c8800321402c094503d6004401d2030680344403206554015001b50110b1b600441d00d90b403810303010b682914241c1c1e110032306100d010856100d1581c5205480e000300482070170702c0c5034405540c2007100c18a0050750300280050203110072145c80e45a044d042a031011020b90b4940140521180816003200c001402c01004101c04000c200001d6000304c410b4914030021015034000d0074411b884002c280e0380111040d03840800f0003001c02c58034101c04e01e01c950300546184010200c40c80a644d81c507000301c0701806001c0c490403100d400e500e00c8a10a800550207198424161703034840751040d107102c0c0c4035442500d00390300d00d00d220707a4040368403003083c0314581c12a0f48a04000441c868039100021265038080c120030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 167953255 1250 167952005 167952007
    0x30e0304080f010b0a0b120a020a1205190e06010e04170f070534030201080603010e0a0c06140a0f0e12030a0216080313030209150a0b0301030b010603020301080a17 72
    0x14807074009010128480e9418400442e5144a1008102e00340183d60806416101c00f40304000000c01c00d21380f51a845601440c0050391030800040640f140381c005130382445109e05107010420f60301080c3e414451400110a028001d051000503225140c0b04240a10030071000039a0015020840b04034030389401140e044241441c0043d1000e0300768150740545426070751a03000040301110030074007200b10100310049803c442040c9520a40c03811001905100113030402550f040451041e80c2e0a500095002c0180021030700c0c0d005091410b015007241d42d21800b008500c2107a1482c00d882040030486070741403210b81d50741141e04100032060b2050b45204003040e8100060750314203003090604000810f0088419001000005402e00b00003440d12040d030411b540d1a002440890311904408000c0c400352030b4101e40d0b64400f0350750844482000c01c0110b00d0107500000d40040010110042001941600d02401c1d0010440c0c1e00e820007a0280d00c0207128148881d805039000c980410702c18071008002014200c0a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 167954505 1250 167953255 167953259
    0x40506011b050318011b0f05010209041d010615090314071d090111090105040b070f020a03030c050c0402130b0901230c0c0f0108061302090406032a0b0a030e0304 71
    0xd030103001a603030000c689036440003e1060704e08800e6600454911800d1130076501c02114410103003c0e10f160114000e00841150300d00e00d0801c2401e406913249203601510421000440040c80202082d201041c100d0359440c00c4004030328034022440d80c640b0444141c44201c100c1d17107560b40d002241c1e1f80c003003a4503000380103098000c1030484050145104401c0f081511081e20b0030a4113003682103c0e40c018580c560344e4410441c2191302c0c0d8114007138504440d401c0c4072050326100d140c104200c3c1041d90644c001d5004084005c00300c101508442040b1440d0b004804685500b5068410f100891103905000707040f01e212041e00f00050110840200940788041c585007a0070f80015407250088684071080c028203140114048049100810801c450400201d41030780c03885d1151000a406054050308041c0607081d610242c1e080802d640d0103c2d0500036002d40300300074140d0f0301d00342050000c5890709500c0c180c0ca0300d50080021100c50211030741c2624900c01d000c0b460a907101c01e054000346001140c90501d80018000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 167955755 1250 167954505 167954537
    0xe03011817040b1c0b01020d140a02120a020a0b070504080705040506030a0b04030206090c030a1502030601110d0306030b01080a0b0114012604032705040207060b100903200f04050601 80
    0x6821280c03200722030284d0b0000980d94000c2650101c035041340c1194090795404103410b034021050504003c190107100e540e40109541203041c008044245000c40d440014110747d4243c0c001012040f860080300400660b46840c6001c44d01d910480c400c9103065480140d003840700380740c9a44020f8000b81c0003800c40e181c450b0966104414004104c50640c00350300309400304025042c05001607151000c00f10060080450280c0d01c0a0340018241642da217110b5001c07000540590152500403610396880c4119a8041103651005010745110f00044400350080b0000154000f40000c10f990919400f0b4203001c100e0b801c1c110324403a0171120100007070400c1100c03a800b4111070700b800f010752140c2100d002400024130b002e080c040d00d00d142d00c1c403d229540038601c05000010094007144010b444007103402580c1d610701030070700c540602044001d1690100c0880c2410031110f4000d1024411603118034030600000360a01ca4810005580003015034200d0768401000c8290303e01030303024941c0000d050420445640b1222a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 167957005 1250 167955755 167955757
    0xc050705011d041a1f0c060e070b0403060501061407020306060f0402090406061e05030103020d0b13060203070309020415080c090c16080d0f11120403020106080d020d0e03011817040b 80
    0x140080148130608212030381414141a0003c0d103500c0c04034081c0c0007012003c03000381062408200941201ea17603007644458403506102a1000381041445952110f0300c2e4246580101020302c5070001041c03003541800c502e01c04c4c40c00dd81c1d030880d030000d0281100341d407804180481c641c010000203a22075402c12048031142d5492080b000a044203540b1080d911800c1c0c41c1410020115080b1001805407d000400050f5200c00030040d01c00e50140000407291120350107407000221981000381301038008810000d0140d8076030722174421a4000c031010310503103164000e0001c00114a004510098000703114441c6c040c01d124616582103110703002002d1404039418800354185c2c066907011111514001080c0e00e10007203e00413500366060f8080c040000c4215211009210711840e81c91003424032410000609041c002e500000061000030f040e9209d0030800d00c1d000b52240010644d81300498425a0130148604051048035949892400420500c1242d40c45104041e10740520082c4032650800c40450051180c01c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 167958255 1250 167957005 167957021
    0x6090403170a06180e16080604080a021203071106072109030e060d061d01050105042d0305030c010c030209030c190f03151103040f0b07090b040806070f0c050705011d04 74
    0x1003800034043c1d10011600341001b0012406801910600c001401444004030b00c0310741156011101da41e4030111644103900b0f01d40294013068040002004000499804c00c210300201c40c8a81c058507104d0b660034009442100458242d852002500300042d02020314030b03031008842c03034003071304003201c0c1030034500001402648003426843d070503522500b0812007040d204510510300501d02224069540c10000000c0140c011340c445c0e0340021003500c180f5060350305804854100c650301e030f0500c255115141d0501561300e0b40b007000c005d5055842d1005100c18913205e4400d40c3c001030801006400102e1440c01084103c50041c551402c1982001c4400960182c003000d80c80006c5101d403401e99612811030303650104440300b20709100003c080030010400003415007074440c0c0c0010703402100b80400d521040f00840e04ca48140c7c001c03205460000901042401001a007207102da210780e6079814020380c114000b140c014103a500c1c0101158000d000a010070340c080c81c1c40074602a103100212a1103843c400004095840d19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 167959505 1250 167958255 167958299
    0x50115080d201e010f11070819030b041b02120a0c0b040309171c0f080612010e10020c0f010c0c030807020c060f070c0f1d0402120d08090606090403170a06 68
    0x8000042d061005805180b0200c06c0c1c0501c4541080086d0b141c0ba0818420702034804401481c030b844030080305010758405421054094400c200f81c2030351170344111000c2c420200070310141c4074000d10180b80f410808221130f10054a981c031081a10459070712a051400e01030004c4092000224002c00c04190596050310803c064000130314022a14003803641006510303524013420012140001100302e50001d80e5560402c40603564a07016a005031000742c014a040ca44034139080c05004088014090130350054003180c082e100944544034208000d141c2200d8800714a030300070450001d0388202080c0907a40c190350140d8140141c40d907440c02c070000501e142e4402e4600c0814a0380200380d0a05020b00749403010301410f0000412810345040c11810029085c2400c0e020f040002e92400040441d1145401441a00b28a000b01c030446100160041c100e0708040752890254881d03180090f0301c520381030044601458244e100c0705092801141100107038800200007170102501c50b07800080018000c00c1141d041ca200d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 167960755 1250 167959505 167959511
    0x5010507180503030406141602030102031005040605030f06040f080706090803043c030c1707050d0306030809010807020f060a1d0726070e04050115080d201e01 70
    0x1403105000316141e0355009180250300502c800e02c90290840c4010032151651503c040d00e0706001c0140344203400362807200035010350011052062480e201800102902c0c41250103100700c1c2e44503c00e065891140005026041d8400800300b03012850001c44200e0040c0039907039992810032203885081c259090a2021605090300004020a210070b4008000412140310421604040701018110071044400848440200038000b12010140210b0b03170b007810541d00075020032a80700d250351840c60a41094605403824042c28124041191180c0300d15801e4039845520182400c40c42d81c01180c80702d400621800641c03040d40d00d020b202a0041105a00c18082410041100120700103a210490110405458a80d01601007400345410010710303071034604d40034200b01441d0501c0c4820546400c006502c03868503c48030700c0621047c4a4103401107082948841084101c072036448540e00d40e2826483c00c05800111104500011111494403030503407940a40e0445444148240341d08403130203005592100183c0d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 167962005 1250 167960755 167960777
    0x20c1906180f0f06080f0628091b02120403050703061d0624030f0303010905070504050607030c1b050f360916030201020d08071b0b07031505130207060905010507 71
    0x3505c02d0036198881c001e501654820b051210220302407400d01caa212441d000400e0403010300c00200c4440d0401011190340620000c00000761500070516846a140014010181007615043c000d104840490794008003c14840d80b46888600c02003040b42003056284051900092160380c00b0410039002e10010403640300c01d00a040c81c1401454403584e981e9001750012406c032104c0d40c401005407811111b001d0303000f160658034154100d0b024030981d000154082c80115452041c1035000d858030b54150300c40e02e0f000b00d60501e4000013000021503403081ca80c0c441940700c40f9418509220400c6a4403054111040040d5041c0300145200143c0395016401787c032595004101040c582000041c0320030605016180340c590460300000d40f07908007050300005001079680455402845058021041d00d560b5200c0424448a407030f00014880d019079100000a06080c04100e840280200910403204004d1001280c9450040c840d0043d400080c4144c502a60300d01607040826000c0c055603100716030507035411a60b14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 167963255 1250 167962005 167962007
    0xa030605010626011a030606090d05060106032003010b090316060e03010f020301120318051003020309150114010c03020312010b0a111b0411090a030501020307020c1906180f0f06 78
    0x410114000c6544050070300420a05189180e07070105c2d014140405680e0751385e00f0001c83e045201e01210160000710800362401800301c08200715040e10300c40d80d010b20012281c0d0061080901c180741c054000180c0410041142d507004030010401440b02030190b8840603018122091800c606a102d14041480c485480c2c0312454284262154601c003038000718159418003407010480341c200300c4000c0c20300c400c48106024030b658054011004010045c010f10500031b804030010301030340056480351150b100d100000c8514110300b4035120305071007840306003404421402c8011103000d40d6100d01602540010420340a5441c9001881400780840340b407080d90359040301e0f0005160605c2456110015040307a4007020407011103038801340780c0000071600400c04007401d07901c0b404144210901d480d4801e14501e000070801c030040d00514820603468081d0b4090420f55802c0c0a0382c1040452a080001c101180501442c0e00031811a101c21740c0700070307410600b40e03110151170740da200560704060a95941440100119 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 167964505 1250 167963255 167963297
    0xf03090a05090906220501091104060503010c080a0c110610080706050f03040b0601030b0916081b0304060e031b07030b0a0608030703140f1602030705091e060a0306050106 75
    0x2041c0a0b5506040751812103056500d515029024014410390340d40510190313401981d85086654005001304400c401078642440310030004205103008505000c000141e9180c1841400e17600c800e5504c4461080e48c98104400c000c1683d00011014000c0c0702d41d00590032a400c0299501c510002000909041d0812401c5031414110354011820420208400360208003148140c17904a58400740c9445c00c0d0b00c403500141d015009954050360026000e50401040c0710300c40f40e55117223403280764480c0d103841d07103542855401c820151414071060700ea00300081000900c8982c0680f40d00007a01040e6402c0c025100c902034030700c3c41c0b01880745940368002d01d000e20501856003580e03604150311040401c8518078200b04c850312800782d124042c040c464586955100000320308101c0340703070408103842c1da40e85510481d5890b001c81400301083c0e000c0c2c81103c1c0c0108560529085590266111085a84000d07840c170f9a028103a0600034209038100c1110b01c030000028a81e801811302814450f1140c40c881c4210000c0b079459 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 167965755 1250 167964505 167964509
    0xc04090c180803031b0903101a10020105151e0909030301060906020304050109050f0307090204080d0809160e0c040f1706100317070609080c0d02060a05060906060304050a050f03090a 80
    0xa10f400400500c81c00d6142080e8009041c000909106d40325035503c40020f04000b281c0340c1c40d000060a100180c04400f0100c2c505c074999a43c11221040c0f080d4101008038200c403011a827589040038448607050891501040d00d021424501c140c0a5072a181c482c04a44d03103480a03280240c5503400800140f103065048050034020b068184010b40c101450400000c11400d090300c07031640580081001a03986850174030005000c2c1100080941d03035590345d0382c00700e1341d07661030001a0000601004040b4011417008035511030f2400b00400201c542e103041400c01700910601408800c0165010840001d8402030b071003859006040c600c40401c008040d04580ea030138030a00401440700010070010030300000d4603e003e000305070302c00c400484d5125060740c9005401001c001e02c0160101001082138a212200000c00c954070420560a842c503a40320104502c066480030f5801c0c0d9840781c0280b000071041d04102000d50f610074000c10484803030722000c1e1106801c1206815500c400c5400006500d1510f050200076000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 167967005 1250 167965755 167965769
    0x50a080f040209040303020f09090c09010306050f130e0f160302100c050d0318050304031101021207174b0c1002030a020f04060503150f13050c04090c18 67
    0x200e480c040d400109409802000202419030105103c90b502e01c115040da404a000a0064161801c01001401994008103000c6000be03007080700c00315103428a01d0084d045150060301c807030b0340b8290420441000c7d2031800c8414005103e6026814120b100420200c800c4c07403007110400d0001415401403290041903c080501030000b6014940700184000511100e2000c7c41d2a0000b00c0080400b84000800103041c4082d005110109001c0103010341c454090324440300903000c892280c410214110042d02840304051f02e64012841440c85640100b0001c040a0802c0d000400354681c0046514003203800d5440d1420760b040400420309080300b40165122500007224001e903080c0011410364a6072100302c00c5005038640d80200c0424850085501603882185501007030780d0329030703850b0343c3c005145400495158011a06c10380305800141401400380c081c844019102e40503802204201c400072380405495014407180421001030034034114424010f0320655035407181080505450196540341458001074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 167968255 1250 167967005 167967031
    0x908030c091906020a1b080a030302031006020c0312090105040b0301090213050306090c040e0a0609120e01092d0801050901020711030706091503060305030301090f0e06070503010611010912050a08 86
    0x1000745a00083c05e130780441e60240048901e071400d10a070017a8170b01150303c4120903104190038401051f4040d005180300b40d150942031003e9903519401280c1e1150000c41280c0c00d90810000204981141d030001c116140301814501d103000c1d40c1d1258196a54400d80c4625071a550100e442e40041c51207041c560001d00d01100241001c1c1000c1040d030307484803200ca1405108690398103001c0c40085080c40000200e80d0014410400e074101d904010b00c60040040c41d140018004018141d465030044c60300d081a201c0c90902e0a04070300d45010f01465241c01a030103802c5020054030000b070145000d000300e6224032040c0c800582c8440300d174646503075100424104036200ba005440c0c140001d507840061102140c0e079000f6800070700300d15540c058004001d142c00203810b07404008000303c2e910f6120f030803950074603490800800c685e45201703140c0c5841e41b40c02e0b19103400058080004000c0c140c8213081000c0c200a518000084102095a0301440d02e6041840907010030b401260f03901d10b69400900d6981e008804402c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 167969505 1250 167968255 167968259
    0x4060c0b0f1909021c031119030503160507150c02240615070f0b060a060302120106111204090903200303010b18280609080c040b03010908030c0919 65
    0x15a490707003407060710541c2c0b039540e0420b942990b031107541840d00d030b044641d420802500c9504008042c007502d010030607643d10401c0e00f192314240306241c1ca5909950550349903030460325000c4000020000005005040150511420001c1000804c04001c1100c0c01400080c00c00c0d030b103120180c200309a014042651045540744400444209841d65a0004040386d12854071181041002d00c81c3c040d80d5000380629010185a2040040511070030340a030004840202041e139851508130b007a031252003101c4500c1091200104007041c0209444012500204150b510050301040c5140c22600240d020842c0103456001001c00c0c07582003504500001c910a0310420101e400c1044207035284010f100c1e060400e200019010300d104401e48400380d9080d00106540090310f010241081c00040d4440380c440c1c201d104640010380b180c0501a0302d0100e500d4030026110b04840d5200700002060120704490b015501d4030010000522020700441c03007581650815510365102a041c40140203c50902c05991100c40c0ac1c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 167970755 1250 167969505 167969521
    0x307050102070e0603150405010f141510141c0506060a080114010309240509030c0703110d061503030e01030506011205100e07030f15030c050d03031104060c0b0f 71
    0x250700b040c3e50729200c056515466034004285403001c0c0071801140468082c0501040045c107410018005072000300070f01c003c00384185e59540070354060340c1010f1100d940500c49075090a005820250000c1c0505007045e540380000c0108156034440c0802d110000140f40c0d00c1c4015000e203104141e0403403420380d00c0d0760400c15405c0b0081c0c4404410700030403004842019082c00d03035030b10070342007906207560298001c503004101c01da00716040210508401074042c1420000341e1801e00002c1510700800d2014001e0092920355201e12a00200381a9001d0300408400003540104400f409040e500c0c00d42d0415070302c4824950f0900900012042240b070341050f0600003403246076a8000504112164806c40001d290f8603280295289140d5903031024094030440400c020b190354141d40040c400806a0381c0a01400c3c00361208042060707118000205907028220050105050140003c04218400e0800107040521040d0705100f90b0002e902000000740310041c2074041192041209400441503100e030103540c140185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 167972005 1250 167970755 167970763
    0x30c0e0603030f13092a030b0609060a031b0e010f02030301060207050f0f04050405010203153304030b040b0a0c0509010c14010b06040315051b03040305090406051306080c0307050102 80
    0x2403040f58001010603003511504102031003c000700348840003003161445500c00d001d0301e9559030704041d1102c00c80c41b5905010500070301440d004d5100091a8a162624100c200f1449400500c002000c040e0f942c1160300c0015801da0104030710420681b07411030054014000103000840414045085400c01d00040216540018402d41030300c504681d51a0f034100b10101040b00c0300c0b040350485a00500b00401d002c24001d040d4011030103500300703c1c90320141c18510401e1021544072041101c0303104030902c44954000c0d40412070702141007012908075181650701c0c5c5a4202400c41510182c50b5001f51805004103e00a44680c1e00d0070072080c144903081181d144000b810709150f44a000d0f05a00410f07801e0104a6020b40c41a40110f0b0001d04198a4035160704000c01c80f51650402500c505107410003007141000000c84181080703560001d000d24680da00d82d41140d2541100501540041d00c807203001c581582c55042e034821041c880440081c00e40c0c40c040c000c0f840d1070403920f540d80c0640c100020500250364007103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 167973255 1250 167972005 167972017
    0x10308030103060c2d05070b0f0a0f09080d0f0b030d0e0f01090e06090702070f06081902030c070f0203010b0607030f12150512031603090f0518060d0c0305030d06030c0e060303 77
    0x3d103c08024003c805c1070f5800d200b503e10080400c0001030400c00f030401e41c0c04896020305824002000300c000403120340703422910760f02d070b000d00400c0c0180408a5945d030300d03402c441101c0c080c3c40404075540074000040380c41d0001004925000c140440b1180d42c2d1820700e54038071141103e0901c3c0550034a840c3c074003d05420740015003040c0c002c160420008100038000c001d0f241c000e02e1403034840c20000c4c2e6640300c001e04828080da5501d90390b8101c030f180103150300110b0095a00610440e90300516201d8540c1d511031000c115480101d8140d500e81e17000c940c10356240e40241040354080d80360120502c1801d20000c01c040500e48403840124540a442c0c0d11a03111300d003032706050b294190f4101c027144035686282d40c0385024200c0400742d0303450918450420598042c550b40300719102c440040640c19103540412014400b440e0b01c1c4106948000300246140c0380c442c40ba000c0b001c2c0508000c0710006d0b01c075140c450855105028000c122511890108200074403a11000c0c002d00c0e10005954007810200002510391007030b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 167974505 1250 167973255 167973317
    0xb010501030905010e030c0a050709090c051011030711010315150507020310050c090a0f080a06020703051207030b1503090a0f1a0a060e060402161712010308030103060c 74
    0x42c0c030210200b0409500c02c440b255400d03002c41c2c0d21101100c0420b541c40805c10822a51401035450010300c0001c940200d00c0002da02c01d81f40d0748040c0c180310038400900d214220b00000c000800001110030501072005148160140c1603a00c0d0790302c04d10001400781c4a07610050000081419401c00002480503940c08070100245451a0b90340400d000091401d5012407a10f41c840749828244095100010010400c101040d1030481007169a02e180c1d0ce05050280f0070404950880c2c081c00b00041c000e81c0c01021414442d0520605012800c1d0b061242c0d22821102c11010070f0707640c85441c1d0325251000c40c002e00c42004811040c518030340000b40d26100c6030941e1004043e08101c242c40f4041010752503100c55100701c510a080030350b1800a0041024013041d114a008040107000807030654180360084800075074035140707042221384941c1e42c1c20721079100c01c810314080c1510030b0082801d406e2404d00303494003e50050083d551694103500302401143c1e0300f0701039401441500a040007a1543d00700c0d912018102c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 167975755 1250 167974505 167974511
    0x5190e0a170d0f0509040609020405040b09130b04020607050d0201050901061403070302120718381302130303030f0b0604050a0e0901020706020a0203181210020c0a060908030a180b01050103 83
    0x2007000259541d0045c008003590007810b018004ca14035290354043c000315030048806206039800c40080c040c000d841907500c41c0080c00b1919401d0085400200d0290b00f01e031000e13001d1440c1c80800d07201c95003402501c400c203200507510f90050106601090240201800c4a070512440c0500b01d40000b035911410352200034024001c0c001110443d01c0c00380910b0005001c410f41a050300c0301c1e0000544024500d850b00303040300c120001d2a28040c1d169580445070824400f425141d0b52041035420000b070b40c0401000792145640800100b6460304a88150703000071403182d10045251008612104141c1c0c0a00c5e1340340b0b0044009100400090b55000ca0110440c3c805c2c0b00c40c10b244d500c034108003d001e4468006c01401a600009000c070385070398000300500965a03c000310007035100c1d0b00781c10081c44500d4620660a55400300010490a4815600030008049600110303039001070303180e4402c029507a198109440e040400300811042200500400641640c1e5040c140041115682d0745040e64006003d1541003540d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 167977005 1250 167975755 167975777
    0xa08010608030a080c1b16080d0c03030b030f161d1012051612020f030a11011d09010b030103120302030603031209031201090c0306050102031201060e0105190e0a170d 73
    0x12030617080302c8500e00c40c01440c01000040404c580d540748007442809484c244106400550044041010171004056a440895840003624201c0c0602903550a10790326004601c1816070204040010031400740c100001c420ba1240303840c3d010104001525100e4000640e03e004002c80030711103103080c1c01a2401c0300c0780c4507d40d080c1d6043c043d1526109010311003545600f04030201d40784a1110400440510840311240c10020b04024151200c042c020020803070f6105407074212071580510350840002c0c1c20851880d00111040d00026a0142c0c280d21030000900d0010050040c00f0302c450b04a41c5e004503a090662450502e5000301e40d82c3d1040750f16842203141d10901103580c0d01014030413200785000c081c1001c40513586443d41c1030000c01c2c0d01203102c0040303072400300c00050550010099a80074200040e500342543e18020095070600341c51044c0e18104102000404c500036220725050350000b4490340c40c6c148000107081808540310894000d842c101c080705440780380180c070001e01140182d82a10301510415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 167978255 1250 167977005 167977021
    0x3020304080708060a0605030d0903030e040f020418051012030c1109040303060801060504060b0403110a050d06020403020109060509060a0e01050f0c01090203060a020c0607050702031005150a08010608030a08 91
    0x100564020103414000c03004002443c0f00005405401000c0c00b45013040456503417000c143e41c0b05600803000001c502024003c20109016081c01002c84101034004650354000e4100300d006c0b030b48203800c07104c400c440902c0350906100491207295071203c58184100700300c909100c2614440d810048000741008840c010000402102500920654a01802c105c40904152a018020301440d016004080d80382c10000a07003032425010750000c072014035851610300782c116140c02d2034220311078495075045440008002026141c0c0440703070f190309005c2c100c0107031544d0031480014100d1059602c128108181480b108080c0e6850380d003103030590740ca0380c100354128644220051740d0354025412500b54494011810b005400e8041d001400124400c405594499588d02c105000300d008055800c2c03225444800042d80700303802030000b803e0a6000030101e40d96074241c0464281a9a012a4050740070b079400c011803049800e1608400d03010f41142e900078071240381801c3c1c80a989000e80e603203c0040100312804502c00d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 167979505 1250 167978255 167978257
    0x3060102070f030b1e060d02011202070206070c0905070302030c030627100602011d030405060a03060306090609031d0102030d090f020402030403020708190c06031d0d02060108010f022104030203 85
    0x400d5030300a01d20840f650390400346401c41040b21000e20f40c400b404403d1600011803000c0e24070030030008207100c40c0d850803600116401000e4074140c21101d5420443e200c0540d4903c4003130101c842c4682d16400ca90303400e0900c1c81054078805032110080c50700500601402e1807213182501c0c2e00c6081650f04042d01088851100400c1e0814260205281845820710000d100c0707000c485401d840f0701da00244208143c5601002448e5402c02c0789000942040c4003e100e41e151040007450119a289400301c0c2464603034983d201200c01d1104201c4c0d603999030300c520004045e0046980a00d280c4a01d4400541040a00001c1d40b80c0c890400c0c2d103e81702c0d9640443c1c0041010352044400b08680190086480786003c0c41c0c007035945c1d010340c000e084140c030404040d88a0990420101e11400d680088800321451031302000741c014042d0000c1c0e501c400151400c80d1000c214003003160903140c6400e9402010a949080c5000b0700b100c81901d03564402a004002c0c0f889002925000e03080b425a1880c01501d41d03a40d00c0c1412819 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 167980755 1250 167979505 167979509
    0x206040b071b0b030919020a050103091505010603021803030a0905090603030708071a0c0a050403061109060d090b060d05070e04050f07080106080d09060f03090809040c09140a12080306010207 84
    0x28000781028041405090f05000d18462441001210f181d4880f10380d003c1610103400d54000c0d4810100c00041c40194441e4118024041c413942c403140d5488803541510040d218241c0001c00003d80c04100c160074540b01c0040001c9130030064010394600140c41c00c000380003c00c24010700d405414898003260180c0c40400860b1030964200c44203a848042a02e08418030703282c2c100390000380317449603c0421144507038039049515480c0700d5285c00f440c041c0b030f541d139401c0503101e00f8454200d10303a014440e034019600c441c2c00030039982590b6200002d40c5111031406c0301078400c001d044180a01495501d010010b400011104152040d800025041e642c8138074101e45012202c15000b900b500440a000030f8a41d81508030388143e6800c02c043c1c0d110603002d0070301199012010300c941400202c03421400b8048500075408105114028810a4502811400400c0565030740041079000504e03500810440140b6500f500c0440000843c5e100d840390b460070074680038074015800d01030f00090340003003c5007a982c02002501c0c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 167982005 1250 167980755 167980793
    0xd030c0206160e100504050a0608060d0b04030e0d060f150b0a030f06051207080c040506010c0201030c1205090c040f0209100f05040302030118050c010306080d050d060e09010504140a0206040b07 85
    0x1d80d442113070f0002000d41e003240c4942800340032112004102e09005168041c031900c4040c054108c3e061103a01c50f00007116000e00240c2c2403201c52030b100080c41d151250903954207409400041690701c0c400c2d420800302c2e00fa00d0040005034002c11000c0c880610144115800c540052401080e42000c00c0c103018010000383d8003850b800b40c2c1e401405103080320301180700c0c01119443e0081e100d916135110180001d962007221410b001030080b804581c0150302170380c0a075150100c20314103220624101041c040444005541219180e40107646045441c5898024a02c0044030800c0c01d41c10a11800085074403003d420800000740a11101ca004a09101c0d005940065800400900503a00480072000041c81c1030201503030706000d8551a20050350080c0071b1340c0c040700c130404d0003001c464403c000304a401d608009055000c440e102d44c1d0004011000032005405409510000125400d02d86001c0c00380107a89011803010790031030a400000744c1e9a00d0185c4049034100390100da0303074480707078500740b00903e001c40c80d210 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 167983255 1250 167982005 167982019
    0x60406030e03040b0a2003160803090f15010f061103030c0306031204030c05330306030c06181807140940060e0415020c0d02030a020d030c0206160e 65
    0x1221701d9200c5643e01c0424124003812202c1c80c811011103480344240c5d140f82440c03185900940e07001640000042d64407e0303824042e40d4484014014582c2032981c40c2c50202908026800103200912108a1010040800d418049007040300c070100e03203031280001404198110b00c007200060140e202442154852001c00c0b190540e40d6803685410200c2400754000e1500654014403041c040e00340c582c0507141710304800c901e01c01400c0b00d50500c0d01c183d0346c402031856401d401070004d1540b09440c2e2a01500c44032580b40300c0e0540c0e01e00c840060150200c20203942c0300380e081034442030102d0260440e503006018030903800311661f5000350341e010440c080c04442c87c10110385001202c0030140c8104400914500610a40700c3c1c0081309040200b0b000c0c3e6032903004a83c0c5205001000c900002c0a80340b100d10607580d005000350074500358030f942c6800d0a05c0d120251015801c006507100e007035a81803140b0035103054141010004401864402591100024a07845442c0c5c480803164821a004802a10702131400922003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 167984505 1250 167983255 167983267
    0x4180f1103100f090c020309090901020d0207060f0f050c0a030e030405100302120c1c1a030303010806040605130f0f0507031211070510050a05031504061212030506060406030e03040b 80
    0x4102480a104204a40341e58010101307022882d40100b2150034a00e80c0250304044054041204003030014000c0422590701301f08448400003903001505c2014010940000d140c103c41103d4000d9034004012042803624203820011454110000c1d601b00062920340042c02c400e07564010791541c03107680c000700d5000c0041440b140c50141d258004240119402d0b007000740640300c0050f090001d009200c181d014a482d0319000c44804901503012070340c541c2440300300840c0c408040001c282990b0080e041380205420450410090103e940141c0341c2021000020442916032515544056005000c00400c01c003102180d03c0e040c040d003001308902954020f42400705041d00703590007416042d045200b490182c003801c100020796107024021024902256119035150a40308070084510740d20040801c005a184200240c01d103890350f04c110383c00b070602c1c07004400582d18a03042110700c030380c80881a8070816092508115050311408255001c881842c1004a0881c101c1c050b403506600854100d11488000070401c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 167985611 1106 167984505 167984521
    0x20a03020405060c030304022e080402210c0a0806040804120203070801050a020a0305060d02030d0f030603020405090d0824060d06080a0f0506060604180f1103 70
    0x10062a01d03444200103032454100d002c0300b030180c0e44080100021802e05511590075990a903281d0169018a6500b0501c1903024000d01c20802a0f00d0b0301190840d20342d40300820b89a20900c2c502c009614038801c0342c3d551220903104191145424040008000780003191150146070030004480c0380c10301300030140460044c084422a01031180900010f80150b0a00c00c0900903030142070007503070b600110900181075820250403540714120305c06000c40140e0700043c50424880807030400c0320605020302c4090b001803000c0c0d44080d4006090104016035824041241c1c6061071403602c40d80ea80351201e400788032610000c820203011044003459980000d140c880e0103408007614001d404034034661640710440c00c000d9041003c407121420030707880c182080400c0c00f48035440a02501c81d60f05103458400c50305840642c2c0312905030301c9590b50022030984183c0e03411110340c161146419942c4c3c1d04101c05 = true := by decide +kernel

theorem cover : BRFrame.Cov 167805755 167985611 := by
  have h0 := BRFrame.cov_init 167805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 167805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 167805755 ≤ n) (h2 : n < 167985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
