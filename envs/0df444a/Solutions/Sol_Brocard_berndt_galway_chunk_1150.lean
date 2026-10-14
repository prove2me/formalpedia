-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:28:07.628736+00:00
-- url     : https://prove2.me/submissions/46ca5787-950d-4d3a-8f82-b458d4c3956a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 206654676 ≤ n < 206834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 206655926 1250 206654676 206654681
    0xa0f05040c0b0309030f03180d020304062304030501110a0809010606050901030906200403060e010203090604030c050102040308030c09190b0318010608071e080609030a031109090a1b03 81
    0x49001e804461411410b00440c400c10b00159040f912440460b4141003140f40c40301060740c0100c550150924482c50000c191020401c440c440c1918540055800c0c0b90420000500d075803540c205043c2d8600070098100e01403040d40045801440c0c211380240024415040c0985050340300c2d40c0c52500040b0540005107450300188038a50955215a80713140c036200c0c0501c0110041c0c8580c040070344085a803142d80740f212401281d000c40c103d804100c0320782d846520718104a402c9404074401c1c1c803143d074010010414031820100380f60383e209130725003000c024031445810958028040d82d000200142d10000070b02468510400141641d0a82282e03034600301000c06c6c1e13104103c50074600c1084150481480031071328038403134030840b00b0403580c240340001006540d50107072a26121859100301b1028040b800d10f030300c00300940764140b0058003000000f809a401c2c24080365680f0310455000d04201566200c14261154407141140c0308550003c114031480c0c00d04140c444005e000b41e0548110288414600315180d038000d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 206657176 1250 206655926 206655931
    0xf07030c0c020411090a030c05010f0c0c0b0a05070b0a15080c0a0b0c0c0d08071217060904060f0e0d090603090206180307030209150102060633130e0a0f05 68
    0x341c1c1c03200031005042d800e01c4003a0564001a0b4010501408800b400740c03250071801000707500810f94400c07900d00c1e0400151408901e40d440208201d00001002c01040c01005039100715503401c2180341c0e40b80c031055400c07a224052444002d2241c080c980500c0001c1125400210100b50310b400d0f8030040b255030b028a6940c410400c0c0c00107400c06a440e004004102c0603201500f40310742040c041d502c00c0c00b82a40003d4441140c0d0340100d442010100e240428020070105040020b50700c0e040c400c40083c07010190460710f880007005903100d0245100041c08018480d04a0a158194080c3c103100d008183c01c032103a10f624030f20032420006810f134200040c1c107511a02602c007019130007412443c0780100f4050f103048448102c0306d080303806114040c80000140c40700291548541c0c50001c040e014007007010002801c2c01406040140715a00b071411007964443c1804440f20501c682080c031914205111103140018041c0000740c2580380d104840000701403c7c80322029102c0d54516004202220408030b142007140c109 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 206658426 1250 206657176 206657201
    0x10b090604020c0d110c0a23060901080a0507090f030819050f071502090a06091e0e06010305130b1306060905040f12090b042304052406040302040e060f0703 69
    0x41404140d00d0380182140403000c940b60080e1510304001b200810540481c5512040829500359135449401e540d0b2100041d888008441d5103240c4481500001c01c0031038061b000e1252240d60310f0200e40d803503000d03e950300010b0070343c10070540c06507a8074208480079400041101e01d683c6120005c1c210144d00c9041111480e100000a550034441e5544844590b8014161214142c035800c2284441540c4c07000207140082065035541c03101c10b03080c41c0c1c2d124424449240300341b4420120101c284010380c0f05020303007a442442840c0004a513640c0350003c6180111404000c0d1040d2280002d000c07604109010030078205014120a001c4541c4d5510040304030303002141d0140112061002c020005502c2d01401c8407032061034034000050948074040641103a016600805858910340307400074420760803000000f0b503200300310340030000c0b850034a0740b01c0c03c0b500410f40c03010003a40ba0465010020743c0d5080a0b00c020315009001003168002e80014240d64000a03a01881c0800d407081c0044c0304240710f030240c481802c40c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 206659676 1250 206658426 206658433
    0x512090d08190204031b03020a090902220f060602030d0b0906060714030f0c010609060b070215090103020d021210050d0f1205041e090507170f061f02010b090604020c 73
    0x1c0350300210520384038102e014004140c01304000008a185010034205103046551060358180c40e51040101008059001001e018105002c038005030759a490b8100c00061552002034440120000c0c8100804a401c0d10511141c5031040120303400e41d0000281003920040c402c20000c040ca500d04111265030700b1a040c540c400310800030785000070304404649a200e0308080442e41000302c4560402c076150401c3c95000066951024204000040b40c0500720042101c10f03103c903c2c0c0006900414100c82d1401401c0184003000503581d0000e9210364112250303203205c40c0b030840d1640621540d0961803201582c07000c82c80640c08601040e01d10300100ca82001c2a44000030b20311190301c1c1d950302c00c402d07201e01c140941405428040082c2072524288041c04213094201d0015205040408050031a40040c211500304200c5c44120310955036007805054010350344200c27204196550000150303040846030200907100a25020341401903405402812203098112940c01080e96114140b03c03c070b003c1d100c14480c0f640d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 206660926 1250 206659676 206659681
    0x31208100302300a0f0611040e130201080c0c0a0201030b0604050613080c04020c06070e180901020307020607080709060c0503131205010606030212010608090a290901020906040b160209070512090d08 87
    0x1b0034030b51154041030500c0224a09144d51007070360301115481282d114110000000402c0e08540c2d1080d40280d002203c21145800d0000604000d40d8988407440001d0625aa81c4001180c0f42e81e1313041078500401c0d004207c55036904210704007034a410118480c00169205809100a15280500075501c44d240218002c0519a8480004480d406454810b00340c11062044040da524142d507100700d80b04540d601c2c0050703528208820b00070301c0d150000f03001004120448060205c2650f01400110864240745406040312046080041c207510954860400d132800c1640b00046000d40b03e003840424500600c005c10031580d80e240150181c1c03041660061091132100014480c450241500540000300324040300c0b500002c07507440d0102a4800f48800598160020f849088240107042e00341d880120000207500344807a00b0042500c40c045e5000310448545c0114030032100c81e0b50111610213854000300301c032409041c95003010302554440031204991303d0108001403024000024034000c90019a51007903001c1e03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 206662176 1250 206660926 206660933
    0x302090408070f0819170106080c070503090a0f0314060601080f090a050a0b270d050306060f1c050112201306080601081501031208100302300a0f 64
    0xd030300820080f140f00c00b003e0302e0040880c0b6004050040c05a003007104000100051a0140031094071050548100115400500c40301e580030921540100e007a40e0000d0f1181344a1078558110300800d02a19009041900c1c0021a0484e501207001142d003c2e141003112290500d011030b07182e440480300c2501244035280400c22280108405942c000c40010980c3c2c002802d907540e05091102002080d5500903042052002e000b400c807014072005010080c00481c03890403804e1075501c64950844110a20030048006409510f8850842e0302c2c1c5403544179843d540e040c25045d0313000d210b0f0304030354101d80e5540360000101d480301020b122030304a5a007154510f12041e900442510344548208a11600040c80d0f407030b000d038201d0090140101400c85400034006940c1001d02c0d052519114110b07201103000da200040004c1016030b074042c0c2490820b031400c0011969568a42c4106860301d600007908020041208118414282c104442d4403202000640c40f5061520141d43d0712102058003402c2e03510b4065040001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 206663426 1250 206662176 206662193
    0xc040f080d050414130903030504140703050c041d060106090f060804051009030536010206040b1807030222060515090609120303070c050c041503120207180608011503020904 76
    0x203c2c240184030030007017100302c12181c0c251400346800710042529101407004028a40003004080c0d00e82400130300d40c451440c0c4455550794044000113000b10355860000f500172205c05c1d2240d241c20f08460865405594400c00101156550701c50441c0d0b25019020109000f4401d01805d03000300c2d040340042c441c085406200000804203084100c0a000b020416240540922085040503030259280e00500100c2c4054403071900c1020303800d003811900312604000000d42d4554620b6007210b41014000780c079001d4100b8031468408a500080d602c6180c41d1803d01d03000080c4190f42c402542c50301c0041c0005640d61042c80303182d07040700343d040c1140c03d030038400c124550070010081c1200110045c03440401404520206056a00030384070b40300080c0f24440c0040c1408410082e142036810f05031000c00201400754a80b100f42c86507400000c00c000045800112200c2c130030000c070f201401078103060728030b080d0303014214000803d0302c0c4c0b0421040d542070400074034031022030b412000e0403650044c24146071075560f60303940101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 206664676 1250 206663426 206663459
    0x302011e20031e120f04030909090b220b010611011d060f07050c03030708060d0b01080606030d020616080c040308121b07050a060f020705060c040f080d0504 69
    0x4001030a078103092503038051103241001564080140d80d41e034008003410002c100c1124042da801c240100580d41e004a840703041c00c1c3d8402d0b440d520301500b035211854119101c10046d40b00003100341c100900c88040c802c1c1c00d10010300882c0121030208030b2010555002c41c0d020007070800600301445806c01080510b00540c0a05081c0503d040001000c40704810349500410116a1010981d400541080411080c400000f07802611a0404504080310b1084066892000500110400c00714070045180c0f5207031110048015035101550502c1907840785852560303885c1c00c441041c4244920a002844035002140c0d40d405069909005210848100c00a98072104040c00c01d003002c031420080000851084070203045c0c02c1140c198108860304044150b2000b9002602e01c0c2803542d20b003001500c0c00075200188503590558021008564910f43d5103022000703000b404030181980c062001002581d0494a0041042e1031200402c1c001071074440302d4540d5241e4000c1c45100208400304002c2c0310903400815040c0c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 206665926 1250 206664676 206664737
    0x40c021c201f0c201006050a0b0403120e04050a09030f05090d0f03051614011b02030d050a0b1306090c0c02242503030606081b030415020301030308090c0406030201 72
    0x9444c00002c007024100103489020076000800503041548481c0280002400d04840440c2020709200407442e8074401c51100400b0002c0c2440060815805909525060361000700b003081b8920300111401e006e0410b05804400260f110350210b60094050001ea81a90901a2040148081a58480200c445500300a4040c0301c0188070302e22100c00c0c640703481c000c564402e0b190a5a030303040548000742980d01c407180303510150303801000340c1040c039900100b62060024410008540ea0b01c0b00c046076001001d0000e20315070072504200704036808842c6070300704004656074960204041c06000d00d0071103144960305c10086d03010644a00300001e0740c0b03414078904014072034019100c0c90030310308580000c4140003042c008020048040e50082c181501441900d00611141c1002c80c40e80c40d281061408a180f1903d20020b0b2201c04400300742400716552500908800d803c100710b569503120300300035103042402c407003010341c07440f45082d025028102406000704582d41038540c000080b09426405421072120400e02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 206667176 1250 206665926 206665937
    0x609120302040b09040225081225230f0c060a0905060f0406020d020d06080d080c031f050a120b010b0c1b060702030724080c09040c021c201f0c 63
    0x440e0211440141003512a00c1000c0860343e5000c0210301c986032150052030410380000d01e4070481410000000003c005241501d807480310202d2181c00c450712f50940200f64050100c01041684c142075a0100400c458001d120487d08107985e120121820768070224001003e50f017100d0042a81c220780841e1150304544102740242c00d06481720484e02c101c0e0010703400340021980f00c410810000c1403d00409258155500e451400340c600291440624880544418208000d8850401d5408070801110f8054100240b0703c0061642d119400d03003042040d528180c51500340180000b07602c1505100321042601a400a010b000f402d40003040c454040516081c0d81011040040e4001030380c0a110b46400b07000b0284802c2d009955800c010302226036000c45000501180e2000d0200203954042520700240c01140c010130440d50400c000c03030900d60420001e4003000c1101c9650100740d034010623040340d00010b21300d150300d15600704920aa5180c181d40c280c01c03982503a46108448110444c0c218440110550902 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 206668426 1250 206667176 206667217
    0x1003020409230a02040e0a1109070908010908130b0a08061c020d1202060604020405010e12010603081216050f07030809120c010218010e01050a030c02100203040609120302040b090402 80
    0x24200103a008030900c210b00e402c80742e951000c51a041c401c1402c0500c080703004010480c00342d600d202c5a1804808404d01c50b002c4030001600c0700388030380310030805080700c400280045020381c5483d1b68903410041c11030401b080310b02c201040140000080d18106141d50307468611544442043c4035400e18191200400d44010090079009602d8184a400029105d4485d29028221031000281805c00240866219034010001000581c0c1e0000090000a904550a03081c0c0040c9041050042c082075000a004040104120203800c0f180881d0510480071060400207044014400300d40611030f0071014800d0700303002d200090100340320300b6049070301215003003c40d40c0404001010a200350001f42d4840d065030f40005441240508a240b0211910000c0c00c180c00d440e11b881001800038003801104804040c0c0e500e956010081c4204010001004405400c5580341028200358003d044901e90a950348402d40341b074a56514440d00c00c84040303d4041c41020f0401c52480c00b044080c0d0301081c021801f00450103803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 206669676 1250 206668426 206668463
    0xa2628020a080a0f030c0503010b1b1c1115042a080304180b03010c0819091209030201080f090d0309050f150f0907060e10020f0f01021b061003020409 66
    0x4010f03030b410b661600340001034508002000c0d541d18400d41e40c1080000d20042000304410070079918080040740861440c0d48650907041d10f045c03080c6000030f240c010010503864010b5044201450310300c680e030042d40e2000740340e4600348003031100940c0c0040c189128070401107500114080324030b10500f030400145c406280ea58100904d550816008024105104100703405195130078840c0c942c200c1400d0b4001e04c0100000640030f0720100008102000614410b003c4006034a029401030200f40d80c4103d035500104032180d401001006240012808610054042407a01c4075511401c4e2040307110500a08540301041e10440217440c034024110f503644100d801d9061281390902000c0b00d90540300003100b0161510302c00302615444041c0070011071b074000140500880340c0c0034420300200e4600b92026440054000003ca14210724060f15400d80e010700952441c0119040d001010b81000241d01d80e2034551602c0c0a55407180800c3c0c0b481016900414000c00040c02d0a400075211a0b0151030f603400900801d10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 206670926 1250 206669676 206669693
    0xf09150106030509010605040b030a080f0403060f02040603050f13020112060e010b0904180302210403020301020703031a0f180a020405090c0409060b09010e0910080a2628020a 77
    0xc0200002c40d44801c104a9541c0091217504001c043c201c80038499403180f440403070b494403449100503001d1a000075850002000c0700040306c0003183e200208010707601c55452190700a40040c003810001904010206800070f0442c42030381e01a00c1c0191030081c014030f0300d5005489103601411200c0031192280740025019101c003840074002c2035101051a901d001c154100700480e14010003074903080a1301c41c10000030076030002d11400a403940640200420580c80d102070014040c0d948000e5044d0700004004040542c950000c0101c88507010000c20400342542c10403807491011844a60000e820302208450f1400c000300e103d07000032140c4d200510740b54461001c940c0c2110121042040140001410404800c192180308020040b003180d44d0b04000d41440000d091364510080302c1d118101000115002103034001100b0003e00c0f020702283e890020394075000c080220860110040405690551010f0390004422190b1040700440194a001c4a81105046a881341c000d06402c43c481c001c1c14000052525 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 206672176 1250 206670926 206670929
    0xb0103110c0c0a050109080d0305040807021c030801090209010c02060904020c010608030c0d0305010608150a090513021305090607110111071518050c040e01200405031902090f091501 80
    0x3000c0d00140c0709000030b0008402550780501d04001c49400700b04846903002c88c003180b07102810b1030045440d48580c14080c03014016800042e500090130407090031103020150079207210754800d44a50200eaa41d030646e51003280034010707249010512854090005160420042030b121030300420050920000500b01421114250418a03041c0d00000316840071350341c1040409113010a900d014004c560401c44024100000903007035501c864032034409420a6500c021000307000d8070081a0030000da1800d040120b59500b104202a03000307290925001424100c00d0081603c1154210001d0003e038a513800304440200110b8000100323950303542c6480000b103940030003c0c20348a001f061050403001507040c602c4112140303200c229100c03a50011001000170004100000385041c01c9900086101c512041640504224101905d03d445036103140c44410043e031001d031090b600c096080701c404502a0ba50030b0658411900c01079402650310000980b17039450341001c1c0da4440c01c180309032900030307542407680030928800703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 206673426 1250 206672176 206672197
    0x9050307020114090f101112031602011404022403150112090b040605070e0607080406080906070815011407030305011505090d060209010504030507141305190b010311 73
    0x186080c15076a1080c000c1c1c182140442c0b24502d0300b0300c80c0c800250304610600c01c00340107291040c3c04034030f81c074066022048040500b4090701d038011a0760202100e41e40c0708441c0e0510b106120031658000910500c50190b030f00020460004082d195a000c020f020303a030b404c45600140d8404201c01180c4c1d078183c0040d50203010780000d07140c1d4030701030180054038150340d10f000750040710300d403007640000305031040c0c0c046801030b400410002c0c131500c44840455801e8455111303e900309000046000c00c0102c0d26000300308441155031141115145e44080e1600d8140655040700010035520120f45440441034202c01c00e0141410b04980d83d50390342d280c1d40c0030380e085201d00741d01003543d60340100030744501c1c40e045583c031040a1034001d1803c40782c00000391503201407c03c06040325a004c01c014900b64095021607000d1500704088400301c0ea40c42000e04202e46000441f24055400c0c0d0341d13100c108002c2401410700030320452140c1d0301d0b075200f018858001810045461410152036443c0f4507444611040240060a00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 206674676 1250 206673426 206673433
    0x1605030406230a110304050406030302030c15101502010204030204050f0f0c03010602030a050d0b030a05160605090a090f09020415060e0f011e1202121914130206040305010905 77
    0x548500646070522001100030450400990b000e003000c0c00b4401ca8000c9102404d0240c1d0254003180040d183d03000b01c3e000107800a1803d4408801d054001000c0c003c00303022a41100e038021000c1440354580321058494425885a0034070600c051503144025041080d040c0c0700040c00e0079075a4000409039041502c01042d01e030f26007014072090051590041398807170051a40c0918551400d88000d41d207220b010001c1c0300304140465200340440050b0891003001000904541c0301e480c0c542481ca80f03407188401600e1001000c1140007400c01e002c2d5003a00c41011000706104003c0b071508610384043c040704005480c500da0340d28081c0c401a501c070b1007590070b58143c2c20038648809052410180000d07500030507040c402c00040d05074400c0c07603921445284850f1900394031030300c40d00c0c900541a03c1048090030f14100c42400800e4010811400c40641c603c240c0c803006401c1107000c1104104000c0301e400c3c88460360401004800600300e60064108000d00910152281c0d18042e940e8851500b16148010100c1e120741 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 206675926 1250 206674676 206674679
    0x18020315361c050f0702030f0a0809010206011d040f11030607050901110307020607060b01110111131d0a0e031606060510090b070303200a020a3e040216050304 70
    0x1c80400900b150000e0505410500d98440300d400340c030382c1c010395040043da0440024840110b460900035031410360400b13000c648840c0c0e440c1c60300c0300040c1c00810000d4014440e10b0000180c07440b01c1c54450b07015020340d02c0c06070095280c544910441500e0b560080d9107180c00107503800b04a45081040621500060f554541c9441765400010156003041520720f4040e40180901e00140e40c070102211403155100c1c0c80040c000d40f0b06801038a0b032855189040d2143c3d4640710840400385031060092040d821014499601c1503202d11404540107180301c101d12404071054002000d0480381d500051000040b14122820280d0881051207484a449421219a6280c490420141c14400c4d4450400607440c101a50031038100f190402440c000e0710f07405410180c50b440260b6104a4011110800c0c00d080c113001943c070700c40302001030760715a00300c81c040394a046400c1a006503004480c3c103049556110342001e10012510000501c410f4004010707540d0700a50030070004034a41590001840340700c1c03141c1d01841e01c0d039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 206677176 1250 206675926 206676031
    0x30c0f1b06011a09030c04090501092019080a20060c030705060c0705030a030c0306170102030405060c0910030b06090a0305160801060b030c0a11070f03050118020315 73
    0x40085440100f000e00038080901e0740c2d900071440020380705041e10001080500da09125014140c0000c0140070b80c8051a0908118800350741c0c092095030b416a02400035174050b07010070b440d24010340f05d010110740215030010b0000340101080324128400c15118100c00880e074002642c59482896014000d50000030444204001402420351104400c4407071703418680580c03202078480c810500440105a40c42030000d5402c5c2c02584860060075611040002840c034000496000394001d84081c3d0f0715204000000340c0c0450b40310201c0b0000180500008544210540182c020345054516554422400d03c803000c8280c0780d11949034010b41c000c03030060000c10300c50b0a85040c0d04549400c0240c140c0d042100600000030740601b141d4101200114941d40c0d449101003c27180110850740b40506801130080c00102c010800d40c00d0030a4a0280d4004c01043e2448900da40d80907402010007901500100c01660400d103010100701d90004a50b0790b0300003820720f6140e000f00102a220b54540c40700d107100c6040e0809 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 206678426 1250 206677176 206677199
    0x409060e0a0516060504032405071715010912020102120a0207030b010f08030a0809030c011409070f050a05010c150e0607141e030601051201080c0123030c0f1b0601 72
    0x101c80011948070511403c12500800500c00e6000140c8001c03a2410303940040c0719003e07010030100300d26400c20030003420300f035034014203050003464bc00002c00c10394030108403a1040d0442104048030161220040e0500d400d035011110b40d860311090b8198002c9450001c4200c0ca84401448940c3e1590f01408115040d890000d00c0b841c0c06030450318511151410a12010000000715a4007408508100b0143c0e1f0b41e0120091540c8964514141c02e942401c2c0403168007800e64404600030602003081c1e8103001d468508418402003a40314455000307031900020440d95004043c0000183d0103824520b01140c15007000006503801c604801085030f014034200000c40b0b034441d070548403160720303503e00510303124161300441e103000c82c4821404032220000000c035581d43c2c01542110f441c2c4507a032062860740d6966007100c548031220240068042011200d619003c00072407805001c96240c1c00c0d610600b5920741044030881d5400110800d00740c00b904000d00d003450045c50302c80d5004500084020b094940c107004d0410070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 206679676 1250 206678426 206678443
    0x61303020307060c0503030604050a060b0a0c0c080a0807021014031302041803020a060525020615030a150c141b010b0306090a0201180e0709080d14070308060409060e0a05 75
    0x1080700100c81080005c0c4080f0440346c200100716008105900c0c2c4503c1c00d8020305666000250f140030000d01c0301202a000341001d00b04500401d03086000a5540c0b8105858811102c401010301604100020040c0b60100704141040c9440c1380c01001c5e0100c0c0788100c0350030b600544804401e000da50414004500d0076004144118071010003040e501100395070069914540994014400c0d034031140000c45c1c0050040b1240c0d01031410900600004080c10000f039110700080e00c2c0007003035070580356011036a8200003820b0404642d0042100f1201d009854840e0000d02e6542c8000d8100101e8207286681d4605520140403503061504034224001c94180d501401c441e90601d1090190b00280c080141590300492034480458080c200751b005e0842c10b03e41000c1c4494180c000341e0800c9041e00c280120035601040304015a5900000c41c2c0141908a1043c0c9a0740c04580040c98115400c0100c007000900c2000b01c540c20090161003c16480c3d1650744040a8802902803610a60b01c075088490600000b04000d44 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206680926 1250 206679676 206679689
    0x1060b0c10090803010e071715031b010503180f010906050106261501030b03030a09080d050c07060c0302010209030a0831090509030d0507020a020103060e06010804120509061303020307 81
    0x100d907401d2652203d8040c0414443c540d030742e00b08440000c683e80e000c2c1c07039030003002c07800c6140e4601a45000620383c001c05046042c028041e2160503110b5007144403800603001c1880058507074034110340d15425040d580d0343d0410144141402603000c07002c540e21007401144c085c6842601c3c04900f035814803000811080c11070010f02d6415050301c204178810520240d00640018101c065040c00c100c07200c005801810310b03030682c0c542520001035403860072a8032480b000181c620507015920381c9031303031500c0494150140c202c1c600d4054009010400c040c0d0700404541044500ca0300001d801d010402d1300090400d0303800c2000359101140054030210000100d01860350504234041c05101c942404035590b801c102e298014040005e603223101003441c00c61b0410950343d400c4034818043c40309150400e03000391030b0241044224082030508801050447d49425854031a41060b582c001c1d00c2c1d41d964940e4514446400100024032074204901e030403a854030001003101310f020420f0240018518411b00d80750102c41e51214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 206682176 1250 206680926 206680931
    0x181a1801020a17060f06040f030501050105010f020709150305060406060f0906060801030809010c080d1b031b080a020d0204060e100e060313020f0604080c0a09060513091401060b0c10 80
    0xd040d5030001420003d4801483c0515142c0c0c0d00c20003c83c1080320ba4804da158004170100e0b001410712006903503201a280b080d8028000c59a8031801074030340010144418000d40c0004106101c00c41c6140d04c001d10030f02503100c1c0001c81c16074a844850619505a9043d6500758864005010080003844c400780103160080081000e18680040200b10a906000043c032494002500d28000da1281d0b180700d0320365403c11405ca0f6600a000755445c020092007060f04800390304040741d4041a802403280345416000c24500166003070a460085610050040a403503041c0e5003400300344000161232002c1c00261100382c07900e840202c40c110130401503000c144401d04c00c110402081070070a40342c110a03281c0104502641400060350707480040c03100340206c0900c90300580f01290000d454a000515842440e1041e1001103200e0348981d21602507644c0c0b80140c0d9085088480b1461180c0d0307071944003408590080e4000c81e0090300c1003a81a0940301598030220b000c00010a840041020a0000c262421030b064000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 206683426 1250 206682176 206682187
    0x708032e060f0305151206040c05010507080d021e0406230f0f0307030b060f0333010c06090f030509120d08072a0b19020418181a180102 60
    0x50000790101c40d124105a01c42011690000414071112074a941c02804030b00d40d013013420203145c7e88460484080d00e000718211000070396540694112044d6a40000c841441c6c03514290b07442c800f87d4089a0445c0c0e0309800d05100000c0b060041c3c1c040c00c040c20040c0d5444440702102c0d08441e2500c003c042c1400e0380070317004201c03140f2002c5202c411900c60011401031541c490f510780c1001c0e001003810481c0d4a400910000d11030600c080d0241c02507214480803400e000b480446c111004480816480398464001000303489440c0960145007881d080350711a00011030030040c5a41c450420184003a000c0300424800300300030000389002c0450009000004004040b10f6007209402020080302500503000c0c400051a9200400c809414040b618520414403244175001e520b03007501e0b10328044402ca41207640b4040c80d041111100c1c001c6800b00c0d070441c248904d990084508940052030100d42c00134042c0442c024000c0058110040c03460f2444240509140c2c1d480c00180c20040c09010f1510810a40d104201307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 206684676 1250 206683426 206683439
    0x30a0e0c0901120c0b03040506060a06020a050d03022a06180f0d120e01020c0a03110c01080606090a03020307060201020a0801050406050d0b07050c010e0307022704060209060708032e 80
    0x704241141c00e03d280900500409081080e4115110b802c41d9a004000200708000d205001811030f020300b02c2501e0200001d640c40c10100c0e2141c0302402d00a00035000340c180d95174424070030f0b00074040d101080348000030036160003100d6039540c000e54148441190001c6040120001c001107580740001829400b502d0f642c0b1190319803940f203071407a090071000c1c411410b140d512401501e901c0301c40700300440b82c002c66640c1c5201c42e095a60341e99600080b0001200d0112190f040344012a0041074414181c40340400364448408111244d005001c3c4a60050f2066000102603a001c0003030703c009140580005070780e144460001400e00c54146c10040c044c5080c41d008202c0787e226800ca881c241c41d04440303c1840c0707459031071044030f092054411080c840d40c01c0c103021368401c80c0e002c4000c00c4801c0c0708845d0701080d0f8000f90000741448484207014140c4c7c0d040c840020300800c920b80c00030125444000c244a2501c4071590360f0340072035081541c14000e00410204840030452451806d018080c0312200c804000b5440c044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 206685926 1250 206684676 206684689
    0x30906052508070c0b0103111201060f05011b0b04030504031106040f060516060509150109060f15050405060403060b03010c0e031e01180b070206010e010b04170c090a02030a0e0c 78
    0x1002481000300220029140c14810488203c0031a44400c0c045c0d00da50f541d05005045958002c140c600c074000000e941802c14005200d090708481400399100101c51803d401991884100c41d26251901580d601110024019213410352080b4400d4035203640329400e5041104003003108000030b9000d60b004010070700100d1105c0b010310040b620685403003907545503014000c0703062910400c1d00800441c10242171240041000c0703000415890812a10784403a81e071107040ea000d6039003a1140c90580d4100c0c2e00c4c18000c981860454107044101400d1540c5050f540300b002c18440d43c0a070f4400d07074002d5520210b0020754a000e004c0d5101901c0a0724001c40740b4000580041e0710ac44940c48282a48003c83c0c1185213862829000041200006a11940011014140880f50b80011111000140640030004c00c5006210312421705135042190070b40d0501f8104800080c901805c01c00c1c298162040041204056a41c01000c52007801d1441e0056102c0c1071803d6030f4030a45144050811040d003002c407807200d054403402d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 206687176 1250 206685926 206685991
    0x3041a01080a02151602090711012a0c0c0305030309100b01020c010f11160e0702010c020f07030227190501050d020d110f12010c1805060d050606130603090605 70
    0x5100d42d642c3c8000c20f600003a217003050240001e410600b40c000300450b40d60011074040752506250003d001c0701c1508040c010240c0c6d01c14035003441c020500d00c44072042922a900d0058468410f140c542c82140d10b07520340703920315001250075210a502901c03052662a032140911140c400f001c0c002409042d0524001800c4060036a680904110803494041d601403c100721040d24500072a204030026921400402d4200d001100c22102540c200250950a10f00c00103103518903083d080c0141426a04503400c1002c510046400e070010001040c10f00c1030300d24802c0c40640e003c0c40400d82c0c00208048034950400c292001648414440e1103691a10000748c1c540050002030154012903801da480c00e01e00000d10101c43c409071054014124100401c007030a03055000d240ca207880c94403203d404403522001514400034500503650411418401d109000640ea0852030700404000d22082c20175248011a150300001c40d170001e40000d4946082d1402c1c0032881c45007903003102c081035000214074840e10f40046000c048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 206688426 1250 206687176 206687209
    0xb121e033a110a0f0e0a1217030c030f0402190b0702130606050f0d02070501380117042406030b0f01050a05010c08040b031306140f01050d03020c0603041a01080a02 72
    0x25014020302080c03040170508441c3c08000c02590025844584060071280400c401b1203503c004948030303e00801010050b6442081c0340c82c1160f10716070f500a00b0f0301c0b10b018081d02c108e801038030307130340c000380c0300d41c5000000c240134244403001c6c075444280a00401942c01a00008066041d190200a00245030b010044a5046072051141960f50b400004540b0082c03003544000b4041d9443d040d010180c004c0056000205000d004000034601d42443c2d000441021622041901254001c9130700303030141400300c504580c07080c0a01081c00d441110304c18120580c0441034040501341d542e41c1c80600409c01c402d00751640044902030308147d40d43c145404a032010440d409885d041c0b2454040700380c108000c9404032400350240305401034990909000c8880031140480c021908941850f450a00c0d8001a8412610800c0b8503001d242559107020148000c84401e440c0c10fa0443c02a2030b0b0040480d00c8403c025405148184200710f009000340720704042034901038200a50704d4010b0468980580c0d16020180e1700e0203130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 206689676 1250 206688426 206688437
    0x150403020c04061a0912010f06150518090402130905060a0c08010e0604021c0c120b0609090105060d06030615031b0b030703180203011d010b121e033a110a 68
    0x941c100003403034011b07812080081e01d60901c0d03c20000f800130380c0c0180084419104403401103800f010b0303043d00c1600402d95228031020405001c1d038403900c2c00c600b90a8102e40090148021099050340286c241c0e072000c0010350342e90f40818180809503002d2b103d41c06080c0107500e82207090303504160800c41c00d2440506800c0c4110340100300003104055540c1c0003032502d601c4907401c00c0080d0000601820400740e410f660b0340c1c05481c1a19190b04e50805508a030420724008285041c1c80e820b0400304920b6411124003001c7d150f0741d41d000480020894820084403802001c00d001c4030910714030300890702e4030058415030715006640b04200500e880c00400d4940180340f6040104461102d080d1801031406402c0c4080c0d815800c009101e44031070304e54504110343c0613440000f80b00f0140d07800140651001d1000700000b5591180100b080c1810120302c207104200b070b0a40559203012070480d03030814490f40162100c905155100e07480f401421440100f041141198801800007149030003000381c00c2d00278009208284071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 206690926 1250 206689676 206689687
    0x21020604261506190803030a11040b0d0222060203070818060d050a05090118020103020319021c0b030d2c3a020307210203150403020c04061a 62
    0x504640c0030755150308850032036000964080241c898154140c41c01070295001c560048504140313144500c050762501c0000f180b443e122089140020220745005400e0a1000e201c08240740b00300000138407c1e4103008130003603110329411024105801c0300000181e80e00070020710821403c0e40200540c0c021a8118581584492501110800310350f2401070455200c0b100103141d00c50080c45034001c0307000d112140000c014654425100d01e00301c03555288500c1c80c01501744216801503210790002e603402451081b41d4809809291500001e80c2c20520780d261100005140c81e0112003410300c100c0c413500c0d01c101d0003001041071070000502504100d403219002c0c0703a01c00c02d030158104e17510607610454401c0a09034410b5000303280c2d0910707041460150f400b40c990360b05255003650304002c820008a555001006010540e282941c40000b801041d00102c0d454035003901c0100c0542d03014484c1c13058484500d00110254542464020b04041c1c030505020b00c920324114041c0301c2c01c103022100016220108251907581c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 206692176 1250 206690926 206690969
    0xc0a140102040905190507020703050c1009080d050903060705070305120402040921020706021f1e110702090a05090c010f0e060403111c0819030902100921020604 71
    0x9100d02e410107089a42031800380103000c104401e401784c3d08001900208410786850008a0700c84c5407511000e0500c2c0d02040c4080c008c2e20303001050445440c42130601000c3e00782d4071020507041c00080500c110110f50007040d000c490b42814407040750702101e545040391400c80300da503000e0150b0080306d510191200e0390034001411526590f200d41c0301d00760040070766401c80015460650301140005641e200500a030300000940a00008001c4d00000c101c50b075210b5030115840c1084014076080500340b01c100d0410900706c240c04a640304a000203110461515929070550043c000c8800c0044c0503c48098a01020854008804600b69002c02c01c24070b0124090144107200f121401c001e4002c40c0d9001c00c0020700042000251f10006100500c2036820811441c60903220200f0000651000307810036600308040018000704505480034403415007030000e6201016000b04801e107042e210391030042280841d0a00c0100c002c8082e2014440c0b03a2200a01321104607030102d44a0301451185034042c4800d00b40c00c070641c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 206693426 1250 206692176 206692181
    0x301091b06091503270b0a0b060f071115040905070f09031e0503041a07020913020d111f050c01110c0d030b13020c0325020f09040606170f01110c0a1401 67
    0x14017605008541c02c0300414148900515416a041c09905141c0003101d091b40c00d0130015a0501c1d29210381c018140210303900c54030012410000030503880200c0d000c00e001030040b800c015101810706084001018984000e0203810303030980700828414000021410000160700c0002031a0410112811400000192a1480c518007503038000ca588503e18119010750090f0361070262a80f82d0007280d020105885459a902d81c2c1008100e000c6c3d04191010880c00107e84480c008500c010000b8080044410014042d2412202c06c4d0007100001440041c1030b400d411000d009843d01c03010501c0030a8038000307201c00c2080d41c0e00c00202610f418591140a904440e540d8400304062120216805550324240841c1d401c1d103903400034076800c05078003a00d08500a0318a60002c01801c095018040b503e4000d410303810846244030040c8200e899985610001c950001480c2d0702c010700c0c001c40300060000074a00822942582c842007680c001c2404203114440700e2101c00141200b0450f0011800998596092a002e01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 206694676 1250 206693426 206693471
    0x40614060916230c011b092108030403031b09050627030d0306050907050c060112050f07081b150405060304020324010611030a0f05030601030b0301091b06091503 71
    0x914000c1d003410480340c43d0000d008004014502d0020130980142c001c03603484c060307161100540020010310301409600340b0600d0500e000651400176580c2910310b80c0e038411496004a4046000944036421030b4034420b01803000c0fa0380403c19007405100b0a0501012134280d00031142400741d030094001400010310fa4182c8480b503107800240030344200010811001e006481c40744a81c40c00b45001100268203503120340c06440503070a490002e40b100744d00e030001c6141510703101034041d5042c0c0a20059600d10358010010107008200590283c1143c10016940003405507003c40400e006d0346010140f031381c0c2c140f58003080310181e07041124800e03240e440e01d0002c617140584040c40000f140c0444070004902801604044c0c1c12a100c0b0381d9964500e501c108441e41d201d004031f1070104003081c101c28044800702e0140000d158807410603d40090200d0140c00000d0940715110400e8480300030001820124408501581c005040913042000d070a40c03401c01c03e02c004005c0c0d041018101903450f2100c1c0d0612125448102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 206695926 1250 206694676 206694707
    0x1090213020a030914061e04120c02012c0102071e030f0f050f1606090303020303040209190c080402040b04022107020312150f0109080a031b05010e06040614060916 72
    0x703001700040d0b065644440903540600091540b131019201942510000b910a41e804880b0406a40b4032000503a5100c1c50408200d05101035151441001d0301c5d41198008c1043d005100f9841d885c007070780006420408a6085062000c01100b041040b241c600c29141e070440342d200107c44003c0d0441e0030403c501208007107006015010b150714901112100040d255000750894944c500d03003a40d24842590b0000703503440010007607002400041e004d0302d8030300d0080f64014012500c000d40c8010210501c82224400a454000718007040103000550900d4401c0040300e0703006580c11440c000c00410125901e10382c1e202e00c07800d4030070000002044a40709000f5100120842081c5e110541024400105404102e031368840c0200c0c040c048c1c0c000d16600c83c6104400b01d81c0c4510103086500c0c40c6032000ca900c9442c203c0150304905c003a040c0d150014800b4402c590040d01c108001e80401c3c02c15160031070a0340e50502440e1900c6104200307100309a6540200345400103a014004400c0c00c0302c101d4291b9440d03800640d2030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 206697176 1250 206695926 206695943
    0x90601180b0304060e0d021b03070509040305090d020301020a03020a0314060d08070305090406141305040c05060726040314160501121401031112150402010e061e040509060301090213020a0309 84
    0x1954001441c116640d10815804085071081020316542b4005403003100d07400008040864080707402600141002500035041140c0140150042404d980c000401c220010703034002500c24046601d40b0600800340e019004810361400c180d00041c080b9071080d41d001e05401c2c0e0010b0f1810815028400310f5440c07027030252041c07007000e40c0d55498444038411419001d000320183c850480c07e0904900c105881240c1c44003113026190304040c00e21070a80c106040c00c80e006094a83c0302403410046401c02203a440390351404070b075114150300d40072500030070170001d8040c43da01c168454540c40c0c01491032481910402e00c0c258083c10b0205030307100c000d82045140d282480849900200c10301882c582c591440340c0c02038503580c04031140e0094a0ba9034003d80c1783d044400b0020900400d00540c403800c0040780512004080da82040b54003a030898070300c10480d4222200d00c02c000390802c010f0615491099014800310000c2240c042141c01044040850a00301c6215503400941000340d64041e50001c41c4583d00003c85 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 206698426 1250 206697176 206697193
    0x41a01080712150f0504050907060e130f0507110f0a0b060d08121f08150709030c060203040303140f03040b0a06120f020406240536090601180b0304060e 67
    0x19800740d001d55041e01c20304d0b080101345800e142c06100c0c00348200b14000c1c00002d10340f500483d092010f0045090344044486114144103086021302c00c1c030000c490070002014249100c0140907401101030b5101d80b03402c00c44442c10b01da217001c0f03158030410390030140040c0d403552588006032807a01c01010040c1284408220082481e400e4081c40344201c0103000b60108400c0140346034402c01c0c3d0345108048040d401075100e42c41e101c035000b42e0317990895068140b828801d5140da4030040310282c1c41d0010710040c0d00108080050691000c18211440c00000703000707103403440c44421249a480000c002404108040d40841c3e00300c0c1095124170003c200c5440704880c0000300d4030b0418840e00c2d05000680c03246042010220304039000001c80c00d0700202c28000303000e840c0e0040106840a4001660340e00c512880080089451301c180b2451460800b03030405031110b000b02c58820080c2401001d81020f0421003e0800e180e0b480c0d00b558111016035000f540480e850740e880741b600340050007216400c0382e9680600500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 206699676 1250 206698426 206698451
    0xd06020a021906020304030207090e03040501050906070f030c0b060d080901210e210f09010c0311060408070302060f0c090d0807020604060306150c030e0d0519150b041a01080712 78
    0x145d07005912a40c00c3da81080e82c2c400c0b940003a07880c40754a06c0754030b0300208020010340d030240001b4442c4a20180100c3d08043d0151610100d5400c3d00c06c0c1500460080040e0308204480741c074546a0001040300d21102c00134003a03c40078401c2c041c520703080d0305002802e1032006001c0c0420040c196030310518402802802c502914050b21000b1401404c0315100082d01c05014030003e04040c0d5928654030031360070f402c100350303440111811550800260144200c0c2d00c80c0340c0c8499420b110052049000c1c2e011140e40d60500d2a00900c1c21000904a00002014405000520183ea802c40b14554000c45510340c1600c0300d410011a18800e05100941c025400900010907c1c2c142d0403034011250102d40202451840300030070740318100d0741c120080c0010107000380e90119160206101e00058040d8044994484c1c2405541503141107409064800d400742034003280800350b81e03000e07400c84401d0968082c0110342040c4c00109061000180c0e01d07040c022810001203100e803148040042c14094048280426020000f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 206700926 1250 206699676 206699681
    0x3050406020106080c03030d020a110601060512090d0903150f0e01050714030f040602130504090b18010e0604020405090f072d06050d1e0c110d0e0d06020a021906 71
    0x100d00c0000d542069800201103e000c00c1034004504040c2c003452420402c10400c0000351301444800042c0400c3e824980741d003500070800769000e440c02c2d80b951603940c50484246649801d005180002c1a440446001d40c603e900c506280101c0382d002c2c0031310160785010320380c0e00d002c0c002041c40000c1071440c041c101902a0815007040f801020192034907080c40d80c045004101c5480221132074245811044003180000d280740e0700411308072610424048000e80c07500c00150643c0d0038030200b40c0340c807000003051004044161003e003082c4000000200b00542100b0303003007a1189070080001c0d110720303612000102e60300820710018506040c103000f61f032092521910b25111000c5c51a0364088021103076400b05045018a004c0c010980344c0d143c51311410500c00003400744c0030b0000c1608a082104000c41d01c900c52a00b45c1c060b204841481743c0300c0c24000340c1d005240c640350401a401000c2000101070021205840300c3c1102c2c107989801c40c10141c0c2e0ba192034082680303801c4840381d034483c1c078904a551207014020307241d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 206702176 1250 206700926 206700929
    0xc01080a0f090c1a0301030302060c2208010203100e0712020f12010810140c0301050f04090204020f0915030c0f0d0e06100905100f0b070f08070c0f0909050c090c16030504 75
    0x200c03e00c4c5103010413049a00c0c01d800240001009030384590702080c458048580602031400e40e0f401196010202d010300303056000426444018242c0d008014010851000e00c8881c002d0f103040f8200111610b4100c500501c503400e5008128152a0b0000320b1104400402c07044070240010500110404e59450822641d21040303403880000840c5042c2d4504407182600010078044c003034290a1a00316400d040410050034000030301580e0151f980e0540b480141c507a80064001d03009030000d0786403200d5052080c0074012404100b42684541c0030000c002e2484201001d49500014400440c3c0d203455294480d4030080481c010712030703400d2045d00200840041d2034901b640c00d80b140420b003417105455100c0e9190b021680c03406402c8520482440a000205854003d0566103016414021002030103898000603503025104c240e0724242022810b1260540d280308403c010300c0a86802c1102d001a034688130748510380703031070030522441c0700401144018502d2010345a034030380c24500f055030f151086c0c5000f030a1503116 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 206703426 1250 206702176 206702189
    0x70203090102100c080106141b070f09060e01030b040c0e010b030a0b09040f0201110102040b13080105070c081207030b10020609061605030c091c0f0c050f030c01080a0f090c 76
    0x2461412003a0076a903000d46500003445441700300082c0d08007081501e510405403110443c0c8502070101c912540d4403008a10482460000030b00006030501c00e801c480d80c44035400c24100c16003031020070000c003904400701d1070440b500540d04640c1c41c1c8071494001406c8200303a0201c0858020000003040c003450100003035002d8403058604000454888003845007009003240c02901c2061081d140c1c20155000b281e0003022070050400052a007515000506419007200110001801c4513401c03d1040020034440c60350030405a040000c005441d540c0d40c0b034240c1c031410f900404d071503040c8030109000d6406600081c0d070a0074000c08048240008000c001d5035981c1c200c60311410b500c41c80d004a458480249da0b4070201c50180c0e500c0c2840d6582d02d0079042d4117503000c11640c6802000182d101d50750720610f0008a80308a21620603400c0544450400d041040c91a030040c501c07a22115000c021a41d07000112444c0c4a2820b0a0008071076a650901c84000d000340c1005c0c941c140d00f4003007050200500701d160300c400d4612 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 206704676 1250 206703426 206703433
    0x90501030b0f06090f0f0a030309090c0201050603070b0d060506030a2301050d0b1503060103080406120204150806210a0209010801020307050a082212110f030405060d020f03070203090102 82
    0x4950104018041c008031943c1c2c002d20108450640382c01d00c88605c1c00d2146000d4143c144c454221380108050b0a2180c2c01a80080d01e60103040c081c00130b8038095040140034510091055003040f800003038840f00755100703031840140000741c1c011002089810107002008009d0135203445c0d14115070b18a014001d40420020302160442505804d0f110041126040e143e010f070944400e1300c49980c030100d6100000d0f112074100e030702c2041603410680c0d040012038081c40c820081c240c5c4841c945031010380481e1541c19654442c47c014403050040d000300c8911a041c000325480c008090340c403040041086083d8400c1c034000818480c0c1e11540f80c40100080480440c1e1095451101c1030b0f1340c0385069400c0b800180c4d650400a90204a003141d80c0d48108807141c2c00c90381680602c1c000c8068640805140400b0038000c0b1007031000f0811000f104ca07000004110100c904001030b00c0981c21521400c3c0d2248581c1c0540780c81000041039190702600d040d8141c034620710050038039644e6801c02c4000a5640e4200c401864010320 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 206705926 1250 206704676 206704691
    0x2012161707110a03030e010c05010608030f0912060108030901030225050705010f080c0304020d080408010212010306060501081e090a0f1104060501110601030204020706020910170106091d0411030d09050103 90
    0x100f807001c50048039015038400e104000c0040044419420f98070060302d181d03484003000f15003d00d09000a00c400507145040c00e658013a01c03020b0103079101d890507c6030842e80144004000e004000300c12241303010000d05c1c1c01a524004200140303001880c515465146503d050400801c00070006402c4090310026201c00080050002c0100c8144000311003031581808140045001810015003d034032141c4039124642c101030302e45244508982284201c441c0c1003010742d0040051100503c00d01c0302404080c40d0080c414904084054034004001c0c054024840d07621001170b000050038002c50078155441041681080714600305124011701401400c0e102d03a18044c0300159940c040c3d4240c64031040c0718000b80c003847e07285408010094105c3c42d0305641e40c07502000540345545e81c000c003504581c4400d860b6407900070105150405c110b081600b040c001d20000030000d20200c0b20020403145581400009200da640d40c40c0b40c0f00c4904544030035925018424804161442600040d0782c0c410ba5201b070b40e0802856 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 206707176 1250 206705926 206705929
    0x807120207051e030a140309090408030f0a02040506030601112113080706410c0601091512020307030516091a010915090b0a02010c201216170711 64
    0xb00e40f1012166040c1c1c044030340000003944d101d070030000111000c0d00380d07030500c909900031603c40e032411603040781c010300e0001c00c220f09612040c00c00758005001c08000c608050406c4081141e500c00a0a41818085140d2010038128000c00c601040908100c0c464000414110355840c241d802c294448014902d45800c0411030940000e00c40d001c5a11960b210394900b244a00116481404480803c4c075460100415084464142d4048007184105070000340d030762902400e2081c145103041e04200e0042c0c0c20050f001081e00013042c44801503820304046c8010389050b500c0020b02d8110b081d84010102d028a1088080240018410200301c0c0e0070746500303219451280e03850280e01c0c0b880c9440b16010170841107041c007403d6260841c80717400c45181d0604516194441c092440e06401c240705a00050f07444140c03030f4124a0307028800e0505442048010b8440744442d1005907140e42d1001082c080703802002c01d40001c208428180e6241c4103401102020500c00c892840c80d02a520004c0165a05152214102c506 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 206708426 1250 206707176 206707219
    0x7050f010503270712120c0809060d06030203010f0501030c14010f081807030b0a060b070b0408090105120406090218070e120c120c010e031216080712020705 69
    0x16000140c0d55a4910354902012207954255210b03001c00945000481041c010001c00c510000b8103034100c002e040b03104651802e000c1180d4000d00510030424840610000194018141d54140908942c1e00f40c0b0b840d0001700d0180109010b0380302035030641c00d101442c0740d040070380d501031030580740919480c18074240c0ba844194a40c0303194460481c00a00c24004800c0014407481d00c01c2e4000030841900f00104a040349164500344e00703a003055909880740401d010f0007040b140303c4c1c50014880e6040312070803d80c0a84401090300740c018409400c03460005100a4a40c0c49041200c04141c848962110b04e8181400c250004041c0c240049000d4101c240001c0460318807034161a1040d041d40d40d6840344110108180903003540c41d95050a40362240312149e5009607101c0d10440b0550303d8030402070410b0402600010030103d4018400c0f80203800c4800031001c1d80c0c1810084510311424030407a0ba032600e006182032400d034070a40f01c000e4034910380e0401d4034550a0740418a4812503108a8040c44000f101100102c803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 206709676 1250 206708426 206708449
    0x5012402030412020d030905130e0c0d03020c10090b190e04020f07020d050f01020c100b01210903050708211036020307080414030f0405060705011d0a050705 69
    0x28001c0061450014a03205c8002180e0398420720b802d85540f942d1b44041512243c40d80d02810b40540c80f8000403482c840104030107400403004942d000b6400e207103a140a0345600e8520f200c0740c0a8201111003c0341280245c50b00780003413180720702c103d41d240310702d8450200150400280b00b0000340c1500052610b407501c0d0003070300c01210700ba681851400c101c50b401c124140d8903550003165a8010540d01c102d1400082c400b80000300029009440240540640a400c990280418505110101d03032111200300540d041202c0700100c864001039080464141602d040c015088014040000080c059260110b0500c0b8408511040800f010700c544643d200b1210418a90040d9084510950506400340d021000703a1007404103d1180341e460303c40d6150303040090703a202300d80c00008200040f061004006080b40000c0816074564059401d042e0840d04540d82d91269200303c43c420113002c81c0c44018850300f984003c1e48900d610390b2100c1200800316845441d6020008191414040c0c91000282070505600048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 206710926 1250 206709676 206709689
    0xc0a0909052e05090318040c0207030209071215060206040b09281104060e06010e06070c030b060306010f03031e030b0a0f140607080a0305040305040305010501080303010f1e05130b04050124020304 86
    0xa06e814110800d200060440512605c218441c4078800805a02c0d1189810700603035096035240c8112000100714802d40703440b0788401c0321544c2103c1c0204615980802c000d40c10992201d010010b58503810b40091900b0445c105500c4d0100402c1c0d012500181c00b49503048409114500d071183d10000e410411040302c0161107050503500b0071100007903056124102e074407284800104200c3c203042e032a44500c0c0e1340d10092307001150503000746014045245410810180140300d0200b43c040180d0031741c2e9008210200340d04001d80181c04059407507103010700030342104411040151001601d142d82c4c4840d540c005415100340480203240d03603400701d4541000012601410740001c410f40c500502400d04a005000082054040040078400480020028040c2600801c500402562654140740c0b48003d0350096520000c40701071581002c035128040a2440d00071a81c00b103170750706041d441082200001e00450001140d0051400001090000c8150300c00b0f100c00302403811a191802c100e40c02684d0f244942e0141c1c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 206712176 1250 206710926 206710957
    0x70306050604090602070f3008070e030f10180309210b010902030610030207030f081816080d0203040602190501020d0c020a11030c0a0909052e050903 66
    0x144042091500a5900180040e1000502c1d2005486150480e04003043c116044407051400c034040c81144d010703403d80c408158941d983c011792134132002c1e110310560245101c2886807400024000c507000340d0b040080c0c180003406441c1440120407100d5119001c03a000d44030114a004c010444d00b0240b540d5000c60181e240c1c0b40ea8110358200401001070f0301c05441841c0208c66414810030004031080413180c02010705250241e1a404c2143c108000980c100006408040c410311a610200e6400741c50103c1020180c10f100400e921058000d803031044c184402d01c511481050f000240c800c65011182e01207500580903141200210041203840e4800e910465005074426a0702402818001d416407440e540303c0c3e000103160020145500054440010442e005608010350a40c240110009103490a00044010b05900c3d245640080e10480c010300914012668440c0c103902000002c02c030060110354103008032004451100032403824031003950f41c41c2d0b40302030070003020a445200020543c0c03e54921065607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 206713426 1250 206712176 206712179
    0x80601170601021f090f030203070309050405060d06020a0311042c0709050112020c0a0812090a02010807050f1b160e09030702042318010614331909061107 68
    0xc2264001e6203944d0040115669000c040014801c0c200e0303600441c0c840d4001d0340c3c680140b81801f82516200350300c06801941010b04110f0641d41d009104010103501c02801038454070f0800c0200c0081c0010140075810300400100492076a000c01c821040741440904025421303401468a1000c9a10694000022584082d4188640d40c0a07008a0359105c8481c1c0d001800c2080c0e144004c1e1506000c00002d8814000000b400c50142c0300b98207010790b100c1c41c010014440c00d0b00a60000b0000030300208000c0030420b010808045101c03c11040f00d0b06c1a9001c070440c20884030324140b0369282c0c2201d0389482c0c100814440c002030b00108013100503202d070400401031400c0c10050380034003000d411890445624103654a900e8050806400c2c0c0c41030145481c101014029000c106416007110260b81114000c2c1000340d841e0ba8442d44c440300c1c0300310b61804455403200d0103c0b8684000b44049240c01c140341903a11702140032040f10a1140380012912000c0d964520400d0341d580341501c28400491200c0141d4001680 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 206714676 1250 206713426 206713453
    0x50f190b1011032701030b010302070b16090504050906010504050f010f1e0e0a0506040b0d0b0a020c070308220e0103030507030c080d020c07081c050d0905011b08060117060102 77
    0xd40701c004070001095a00c0c08a8414072070255984408030640c00140d400b11401c0517580c10710034072024007401e0904600d08225920388021009009194100030700341f0b4041ca8003200d01c201151401803030050001d00190030150400c64803640d0900070140550f18100c000f41c004201110746a041b01d503044c408012140c24030501c1d10048101e680800c00c49080907100041101540180030300c1020796502c005100d0402c40104019550b101240610071280000300d000403d42000c030064110180350001607850014075249801c1660560010703094080100d0318519903050403008500140d0b0202c030200546844404240c40810b00380000b5001403030511840300001d00485021241d10301515485040c02c110072140d00c1aa0b0003052048110341014104000780c0e4004c1100b0000c640034070422180c6c004907150014118090017100b0801d0a80307e0700b400e010300c0780079071111800040d0700d5600f0341101980400502114400d4a0503400180c00720301401c654200c8403c2c840c016481640509000c803c88103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 206715926 1250 206714676 206714687
    0x810020712030e01090f063c0b04060b030403090303171915030210020a030206090309031c03150906030209161b0309170a120203041d04060f050f190b10 67
    0x21040700f06590703160391081c0401c0c2c044500a032035500c2005c0c00319a6038140c4a90b22250a5403802c060500700b1508520070442d22000144c4a28000c0701030009042001480081c0140c402e07a80441c0c00030800000340801e06a001e041c0005a9000f03848021201c44005c410298004d402c441d4880c10030740c20290220351b0304d90364104184842002e4281092141c4980000d02d600b01d80c403040c400543d11001c180c0003016010f20400b44d020341250082d50401042d200402e4a4050501628005a8019a081b070200f4040e62101c5070b0031a02d42d4a0907030b075940792070800000b010301340010380c844c1c40a100003c02c0c201d041598000c0d141c0582c0c0c0c841d21106407080d51030391441c091007012018045421800302d142921071101c80c0d03002440d94000e02214440d4100120740c14841c0c3c101c042150010441488802454590f5241c00510784049110a59031810410010400104c9541216007003d003402610856003c010313002d03040881c5d840c2d00b8144040040002c595071084560b402450b5440419006400340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 206717176 1250 206715926 206715941
    0xc0b01030609060b03010c030204090e010b1503070207091803030b04020903071a07060f05041a041101050d02090409030e0307140f06070303020403020306041203060e0c07140705061201081002071203 87
    0xf8200842c101c4941c81c0020300b520b406c1e8102c00c0020b079000c502080158080e0040c40e0103504050300070440501c034840811042d0b0110a40e80300e94038000008514228401c00c10314005003149201000b481d2800c0c241d4138100c52014605400090900c40c02100c00c1c5481c0c400c5a120403c01001400036500d40890380c94420030411490466000a100c1140490307158000c03014550b460032400103003460305240620320a0035012085801e10201001c210006068401a41400100742041502d40460782c0d000b4020340320f0f851105801c141064201c03020903401c400b00d82000c05044040d920040d450300140c07152528070811a980c0303d41c1d59200b0b5111814868028402341d800381ca009441d090f100d0b00840e00d8518161400c407110803005541c80e00030359041c401c00d070241440309803092180c03c0101000e14213014405014245500ca01e80300140b10302c041194070011f01000c0c0405480700420402013204840034450380503940a1408004201002442186c25183d401300003000c1000002d00c2c00c40082c00903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 206718426 1250 206717176 206717183
    0x8010e15090402150a05070b0a05070f120204090e060609090607090603150305120705010e0d1205060315010f060e0a05060a051c05240108040308010933080d0c0b01030609 75
    0xc04a0f130900810315180100080030194490a640f6249498080110350009103903110301807814040c400c1707841d48040e250761120003a1809680003040503002c54001d03c540e07840080c0d100c0c0741ca07602e90301000c2c01245041c402c420032514840240d0342c1144160b201c92007100d44500144012209000d0b060290b800041202940e44003824100e0300e0b81e41d0a403920509004c14141510013040d4502008024020712807040204000740811440143c80580550030420201202c6622040062031680f010800d1156242c0701401c100c88a503501c0c012075144104501a03980040c1e01102e0301c0403d41171811460302110b001070211460080710460417102a002118608003040025012100c0e80c11a030140d14000c44205004401000005503086142c0354080b05103410301c842001000f0210342c204a091307044400210003c5000140400c10603600c035640524501818644981d4034002510000c000c4142c540510454800381c0c1c90b81c0d815071360301b075454900404040e0035000500010b907007900103025840c030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206719676 1250 206718426 206718439
    0x1f0f0e0108180106030b010602011b03020406020601061d0d120e010905100809030c01090302100608240a06080a06090507061103041509080d030e0c040e0a0b04020121090308010e15090402 82
    0x40300c1c0e403100b4036010203238841c0005070f440e06418001d5035480950b114040e201c0b0305045151030b1801d03c020313481301d03414464101400f0400e030404290b0182c00100202000300108000c0401d001854010040c03004800d000d000501c51301d6070030b202540100c90307140650380018500c0007006000c0700200c0d11044020180c0000d03000620800203191000d000d1100c01078441c1d000b402d42c05848600400031644540d000c60b43c5035010841364078100e125200300c11942e08482040104954413540e445000d810a07520881240c410461040d080c00f10315844019014840d4060310a182e0742c0d10811110550b10850711905d41d0410082042600d4541942001e4010142001000d00c1d03a1103501d9400c0190b05580d45c030202e0b4640300401d0b05031300140031800141400f241d041110f0001c0b40f200c4c950760301c00c0b514010103048140020030705580c010341610003036011600c0507012400c5921082c8002e082020400c5010658090000c07458611130030f100751050324200000100064007004200c108c040107807082e0380151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206720926 1250 206719676 206719679
    0x17060d0c0b0c150f040215120a2a03061d0c0f0904141312051c0504060603170705070801020f030a18050102041e14091609051f0f0e0108180106 63
    0xc100c0410984954200c00f04c4c00e0251030705005002d846200c0041c0e00d03914000c01c210b564031110400a070140c0013090082d0001700c0641c00d803540c100c104000b1000c40c0181d64214110401154190000ca0035601e000084110009409102c01c0391004145e406030344030281809000003044a031400740172090030041020404806103103042c45040c800b6a43d0140398080451964184400b1140508094445103002490044103404440c200ca01089d54008a249c43c0d10200d4240075594208030051904824100204000d070b00c6007643c4c85c0d010840c101c409004003280001c0812043c400c3d101d01c41075061034a40703141d4071062404000c1c00301812070459080c0140210010820074400340c0098000d030300c420b030302001e40d18203c60a5000c09034020365080030f156490301060740317840034580d0700512016590080180e44002c00e40d1002c0c095000380380c004500f203021194165061500b20540640d40e25190012004080100c46146ca2405010b02141030580400d900c8540c1c2c0d10000c0c000002c4d0800014450f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206722176 1250 206720926 206720953
    0x20a050909010b0d0b060906030d0e0d0302150c0c1513020402070501020d0c0504060908030c0307030503131202010204090506040b10050306040914060402010206010b0703140d020705030a17060d0c0b0c 88
    0xc250070304c41a11010520400c1200d182003045250f40c112070120018542d41144040040400c07820303264490003891400c0303160302014000c10800c00e00b00000d981c80031036840c0a024120080c1c024582c804c07054844d55041d00503a603040d03403040d801400118030845121100d034003800003940c4940c00407074641d0f600b001003181c2c02d022880745844101d0b8540c0c03800d6469282c00002000c0314010703007086c0d40c107410402031440070480010450f9503065050415984030740d0f48580304c42c2c48186104001c0c3c1625044109128030660650040090f18582d007400c000d0358844000b4002250038484400ba000700140d01140e04a5001d08040d5600020060000c188050719540354902400080c2b041c01039540190180008c642c0c05102103409001012180740c100a001c2d03c008007031952180c10010030b010006004800e4101a4044892050304081200d0b918110404010401c5143c01c10303d290075481e90000c54600e141c04c04104040607000043c6449940c1020b60092143e880350000780414480c200001080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206723426 1250 206722176 206722189
    0x20c0402070c12060f0b01030e1b030109080409050417030106020a03030f0605060c060f0a05060a0317040b040b0a020601080c030d18030f030221030714071506090f0e01020403020a050909010b 84
    0x643e40b0400d0042400752640c3d210b2000da403420b141c07141c141420300c1c00081a006000403030440142d84030100c280e201b40c40d580400d0042018941c0600501030004000c1150065600194000ca1107007035141c003040040045140c4901081c0216001a00540d0a03180864840d400c5001d0b11900c2c00400a616a9150001515075000041d1502c0e50b8000030104441c42c114200038942c45003000e5001e11441c60184009016100207010062003035840c281d2a803400c030329450641d000b5114014246941c0c0f0340340c01c1508060f8000384050401481400c0c000b192500020072078404019016000b40410a01c4190586030000300e85607080030301000003800070114003840c0e1040100c0d4025005020f03c2500b90341d00c15400111400c01e20184c800c10028004401c1c2d00c0000541c165004030f11203500e0300d0306c41c501031100005074903000c0140360902030003294061059104c82c0264044510400400002c0c107625403d0380100d1001950145042e04c040016040420030903a000e0750900000619121080c0010ba4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206724676 1250 206723426 206723459
    0x5010603090c050f060702210a03120515060d0b040f140f0705130611150f06031908040e100305070303050d1406090a0e0309030712031806020c0402070c 67
    0x94641ea18003052000095036103003e400b06650403054010440b0101d02c141c030902c10007d0042450b403a00314801d20806001e2804036000e801514980d440a0034010007110740c80c41000ea64a01e02004100d080d07180c0c3c169080400c00c060522401d00d4986c0e40d00800801c5e0100308a1b070006e40b5184c5495103600148034011690401d504000d0003410110028002d45034014642e2041c0328041000c2000041000d15900c2140c03020320307140c2540890068030904180442c4800c0d101075046405000400300d442c001107105405c1a0111800f0f01c408645c00412620a5503020f030000000b01310500c654074140e241140c0c030400144038041c4003a0340e5a00d2510340003496000740d001501c0411a038204200d9801883e84403140a040d00c80706042503000910f280c0400790444420956455a1a5841c1801c2c000d882c2c441e0002015640810394501c0100340092402c0c0e0200c000454201c080c000c40b00d0000d0401d000d440403503004082c00400003003407000a5100f00d005440035000400c0004036545c00d00030004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206725926 1250 206724676 206724689
    0x160c05060c0304050c01020609030708090f060304150c050a0815210601090f0207080a2106120b07030509070311031e100b1c02041107080f0c060a09080d0e0708010501 73
    0x90b520720f0a0300385141411610141d05045420407400d0100d0001e001040d6040030f500010090350300d550102c00109644c2d100011141c00540c080b080005124250410000c02c50345040c9c103010700f000d1204115141d01c80d9061841c0804d41140100304032002c10801f01c21318010140014148070b4102014440740c40c85d004c4c18130300c150310280061110742464064003203402c0503c3c2d025414100303569034200c064081d00348140200704644004191001c2c01a00c031000281100034204100340d2140702003a18140c4082c0b01359520803a03032002c185028070a203c3c05200e10445000341000505507940c1c102c103c0c860581c0e25516100e81d60429403040744883d00e10380100007000c020680c00c40003052040a6804200d1002e01c5070900403c1081c4a4596001d0304582e940d0484000981c0c0d868910741c00b080e0f006140c1c010340078640106003601000780160040c560718170300804454150361380e402c840069601c01d020040c0454402d100342c0f8030340d0f0840d40000e1700c0014400152142641c50f060002e0031903609a201c103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206727176 1250 206725926 206725951
    0x906010312020d17071404090c03060e010302060a0f030906050109060e0601110318010903060c0906080112051b06120c040f0f050a03110a0308040e060f0603040506160c0506 76
    0x108100888101080300061090010f01078007040100068500400652801d844009003000644101c4c842c06d00403454001c0544411b4481da20f85000c0001010011a00d102113454203030301041001c0c070b0444c414121380d4024003d5182c6050504211000d54298003020107068541005034002001805683e0107000f0680000400340d00d81840b10350302d8030b8054086814401166603c17440084044119126000b5012000002104400c0103c44070041a031018144502d03084e030700311265612050705021181c10781d95152040e6280c60342034207000ca1003403004001e0307805940d4061113010950a00b503a031070002481d00b8100008031b4166445040704407101b103030451001406202c062002e1640201038081c000e036070310b090303030400000c601a00083d0001800840d050b2110100d156034003580e030b10140d5800a9041e03140d680d59401c49191032420703608180b24400301c0e40046144c1c2007020540c5d1203070381c020000345620707110f01c24403010504201c51070340d00b0010100c501c4e00c0410010420240914140341a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206728426 1250 206727176 206727179
    0x613091a0108030d06170a020907051e0406090f0608060103090309090e0601030203010c0309030912080c0d050c011a090f040507082a0301050601020a0803100504050405030901110c13051e090601 85
    0x300c07000c917041c5400c05050b41400d0100075580107000070b5407082290381501c440220b520340744801d541601820003152180c94120042600c5200364101038412a1308a40b120200c0742d485010084800300c580c012b040c0003c1d200c0c00000d01c50742c425081f180d40e031070190803c019040d0300c400c801000c0c2c40301c40700111425400100100218102441000e00c51003881c50100403120b910b6400500001c1c5034800d004541d440404c01c5800c0c04080c80c1154800300c059400c6541c000016200a041e5400c038a00c88501c41d40b8100741c1d001643e1181c200644c90034001080c003645650b030151750b9100c2d680f02a0090341c0c0d51041910104224100700044954485040356000020505010030500c0d201548059406039050201b40040c2ea41c0000d5915034141c2e0242101c2d07200e64601e51403484070140380d4040b40c2e00c942414248010b10030080020150507000f1303681d2145804008480c165100320f5203603c107800c1506482102c0003403219900c51900200c400180c1c026110040c0700c9a2072a02c002d441110068204500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206729676 1250 206728426 206728447
    0x90a0b0703020f0d030209030c040207060e010903091401050a0e010302071718040e0d08010e0a0b0307060f0210060501140a0c08071b0911030a0203060d050706020f0f03030613091a010803 82
    0x135080740d001500d015840d046605001c0394540400440c400d0089401040150400c081e980001039881e0800d0020441e11495050040902c582d9110300d05004068100007440707540f0800c1100c0503041142c0380c1404c1d0448904c011802588070344c005503a0a03440d400c0b0100d1009115004086802002054803a54140c640420045482980d008406a4026101c5100258000800a0446010f000d994855130340e400c0e5030700080d1094100c4590316000d052408158142c100c5800c070040b0500d54200c40f0804140701c001001c40300c1c0e43c018180440d190443d80d40c103000c070b40350082c09018201e140c44400310317070a9998084150400041161442c86040981c0720903061540c4c4c960041030520004c0c4081c8001c2d0300c01c1c17000c6100c06028504c04a0b00000000c156403900001e015035a035020742200c2081e983c1f00e100035121182040369524034001d41d00350011040d070000603240114002003103407401c84903521041008004076030040301c45140b00803004004082d038544841c02840300102031039481c0e0a409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206730926 1250 206729676 206729683
    0x803030613021c0510090c0c030813020d08090102011e020405180106050f090a03081c1a01020c13140a0605010e0a0e06040c050c0a0f12020607080408090a0b0703020f 73
    0x603078140c1c0580c818401580300d03141d4003151550002c0c80f07800001c2c0350b403a07101c010051400305410284a15040c035900c80f4400c0d03404202207203401e0007984e0705812911511a688068030705400040c0d44080308190840c0440e941e030000f0800d001c0c0500002811070b6444407803800450940c20352052403607001c40d0400503414008244c059400b90b140700aa440e42c1004005011409001c01e10010100c01007210201601c2d1120543c015641124441d51101411008009040e1150070603070801030404804034030505a5000c465903101d0141c0103070042d0078800c01031010100e40040300c0c10201d40c403240a20141c5801704035941c0925100d5001061103400c050016100071004041d4030300800c4c02e0a002c00c6052507060f00716402c80701c21100440c842c80741440888407130141c0f800da5449070150050050030000d14220490000c2c0c4a500c01c1c0e40c1126241c0d5040e03072a18421500c2001040a590014001444040092643c044000d000c41d81c43d944030b22014500c4e4001e4102140036038000514070b04070070001c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206732176 1250 206730926 206730949
    0x708101e2703030624090b030405010204120b06130c0e0906040f06030b0708010e010e0613090605010603060f0e04051f141801050a090c05010e04090602071115121b0c0708030306 78
    0x9807810324a01c5d4520300c00501098080c8925114240c003c0007040400200790120380043c00d0085551824000030300304880c290800b40c0f07046110701c40340010794a44078540d006d441550000b64854901c100f0b104418050010801004654015a1b8030440260120f1601c1080040c40c0140c140380c02918180001421500c410303000310b12640c1c9083c0c0100b01880071f08007801d9004005640c540120303241c1c40e8400024065440004080c0ca0401f00007148480c0c1c941e0040040310300941005050590350480b1000080c0c2c00d981c00b420300e0b007000719090030018220b000c4510f21903540d01c0004901051000d1a00490303c01e88405040040312940c000c80102c09010740703074204194040c02c0201404a0b940d582940c2150310495043c000081162091540c9503800358001681000d000d40d950000341c40e009000c400411405031250b0301d1a06000001c6100405451a85a0200c0a26060b807101c07140c00001c00f240c0d0794510706042040122003007491042c0080e10003801d1030802192203042c103404001107455030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206733426 1250 206732176 206732219
    0x91503060312050306030d05090d2004060914060d02120709050a2405010f0201020d1109031225020d060c08060102190312021e0a020708101e27030306 66
    0x6005110086d6400b1030309481c0400c0c14104150707602410000f05100e503c0c0c0810280409c0d0940c0d901007202e03840c20901c088030003400c4904101580d103401c402000c803040042e0300d000d6032544000140c1103040281702020715500003014003840041c141030aa24000c41504590b840c2515034042c004060600c0c02544c1c1000e440b0014580741106060384c0031041c5c8101d101b0f0070f04014102e2181014a4000e5040351b406034000403003400402042030200c1d00315030242902901038403989011a10060400043e0386c4000a810b40072245c0c500c2070a5500051054458140e9014a4540700003000800c1440780c610f86101a4850029900c5d02d100064100040348180551b108600041a00040d60100f054420007180240058840b14070316058450448445d0b6210115080050b01a40c002e800066120132200d054044400c402c11480c0c0d08800d030340d14a440c42601d0201081464803c24603030700112128803a07042c001949180002c04291480c40b5498290042580d0f05c209105040841500c034000340e80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206734676 1250 206733426 206733437
    0xc0201091715070306091a0a06020d02030319020906042301080c0702040e12040806041709130b1516030e030303040f030819090b0603010b0a05060f070201091503060312 74
    0x441d1400a8481190001010b000a00c000000703031543c0c0203501c86005020410820080d61600106288440410950652140310040c0002801d9807001420300c200c8101940a50309640318404004a0b082c1e1402422044580a1043e85443d413140000350006049550003d0f0030041c5000390070b40f00c440300c46801410070103a0381c2041928001041203c0003140d0584001401180c220b582e0303400e200d41c900003602c07980e0000400184410300000c806028500580d10504452611140b001c490f02c0340c2c0c2c80283c1c1049496580154102c255403012000d070320040e05204071003280c03001c41041039004002c2c01510888035900501490b80c009140710641006a0065180d42030031384a50070314010380c100060411442c040002c0544c0d800c1c642610152008000905c550041d51400e074070707001d20440d50280a90b2801c0c0325420030f0700d805d07a1000308071103001e0300c6149481c014507122908c039406400141d05010820f03100282d51354401d4144000b10b9840d43d0300091040c1180382a1003031051080e40d8104110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206735926 1250 206734676 206734709
    0x1050f0f0d050117211605060a020306010f0206040c2309101502011e11160507051f090e070c021504090605060c0303010e13050a060507020607020318060306120d0c020109 75
    0x501401d0b96800c0d01107440c05c50345440300000300645600c10700c40c008085004401c00d00580b00172640145004440c00d132990406590b060b0710403651208200d40203000041007403410007820780000469402481c210380041003c80100f000f150b42070f0415100f4440740041c0030070811440d1111410827a101650b4402403100440c0101782d02c01035111208610300c96075540e50f804600c0301d20181103e040e021810201000100c1d241001030300c0303814503c070b014040d0300980000041c0082e40211600515160389480728160f04103001a84941c0006180400740540b2011441c05a80da040e061100170f000c0d0728959036560708114800d030a440003503000074041d41c410300082c5041d807404170949066410300910b1440566410724038101521140c0b0b400b5101e1b015982d8804c00384242c030b0300405c1c0300711102d03000c0b112103071180300c000ca07a00d2041c1c032014401e01c5620f91401016190660046400102c01041203e2000101e030450381048005107803d00072604040c003203801c40d41c0040b00c54004010785485070300c074807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206737176 1250 206735926 206735953
    0xf120203090307230a0b040806070f080f2d10090209030304030b04020109030b010306050604061a040302010e03030408010c020607020d1805091906180510030f0201050f0f0d050117 79
    0xf10114029008025412020040300901e007481030742c0070240c001c1c04d21010943e908011040c95020380914034181c02150005130010f8041d40c64001a940700e6074422003250340d44c5103480014a006840c0b80c14944160440d408840142c507140ca010103a0014a1003d50401d4110050040825406000380c98011320517007400c0d80d000700030b5400302ea80000b95020195128801280e0b070502c582c00040020900c0c20001c024030116034001445000180c40030000030352100c103948680e8001d038407955a1f0100400c01800194864000c014102034086d04a0303080c0303134884048a084d070f1805002d100050f4012410040d080d5810019a00c03882c0035810aa6820448201d0070f03560402c2c10700072140a03041c1c4202241000401300c0c04a1f010458034070f02000b10300d8407060184a01c4a40302001d1001e542448040380362072100c2e01120007120781c08004204502c01e10b0f801500ca9070400b2010701d5010000303004408402003180d008105640f50108005039542c104101132113a242200d00040440c1e1000c8134903c0d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206738426 1250 206737176 206737183
    0x30105010e010803120414060a020903010b010c200604030605041214091011100615020705150307080c0720120f060604021c1e0506060703020601031205160f1202030903 74
    0x1812420b82144109a855040083c4a040b07c0c0c80b00110074454541040260301c8164003030403810307400b10006e20804a08000444a0f001a420054a80b80e029403031078030105c2c017008000e403408901820307440c00c2079940d4450004841c4100ea00b51910304d40c84800d1410b05900c180c414000f40c5e0b41400c4641807905210202d4228a0a82000b5060004000044207448410881055401c401d40320900c452038036410b0b00c5010544008600016100b180c0700840c0c03500d040e07507503000031618450409046030348040040359019806400c00d09880003c005820100d0b00d80342d44490180c0710b201c000d180b903400407014401400f04d0180e4420440d080620b40401c1c1031000300ba00754111904407009601c41514022404c1404402c074943d81c00c6a2800302d88072064240080400031002d00000c08100d46d644040070702110344aa1200180160041d40040c000207008007e0303603945240034500242095242551304041202800d410344004901441140410560f0303003407202460312510143d410711100ca004660b8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206739676 1250 206738426 206738437
    0x6040f270506061e0d020a05130c0e060a020c06071b03080405090a02070506060405042414011502030406230a02010b030c01021c0e18180c0a03030f031a04020315030105010e010803 79
    0x420201c041c0c0d05d20a43d6070f29103804000d444024006444d000303442c120000109070b607114040100700002c03414000c44c50440c0560f26101c0c01c8e81c018220802091b0104041035000440032100c05012126400300098040010005148a0040c0b90354581c205000c00114a40084c48000041c0c010006840040c801240048c0c00003c140c8001c2050703125460400c2401a00750f841d01a05401d00c040c64440e815660030401c0140c11601151043da600c41c0f076204040c40006141c0809030384200810003130360b48114282101e100003155480300866280380c2c003010f20b6102111a000503034458404d11118901400042d0302c0000900042c144503400c00c03428401008680c14900c140020a002040c454807040020741d800c2c402040318002074580801d03141403c40754440764282070301ca074560181c0d045c01d081e02c440e029287c140c3c072003544600f038a0348214090514000e4030000032074480100301d0079450354000340d0300900082e03c007000380d42c09039000d00d03085a4050348810100b4400390010021100084115030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206740926 1250 206739676 206739679
    0x4020a0903020f12120d050603030f0307050a09050a1805061816030b0603160807030c080c09010c05060406020406030e010504020d030c05031605060703061d06040f270506061e 77
    0x382000307180000160441360350185070585009010307540d10510381c01e10080a0300800e82200700169182c01c400c1c507641e40202c1640000c00002040483c03030140c0550080e2202c03a50606c2c00d241d9168543c80807032101c85040e440301c4c00c2110041c404100354065030260070f0340000c05a0782840301c48003807190743d49445c0d00680401810703102c14414120082c800e8000000420000c2c01d43c0c0d59074100f440d0b612f100054071021480025500a0200b00554402d0092140c50003c60352064030741d0701c1e40c80c0f220310b566200000070340c1400001d44400d00041c5c403d0100c103100d140aa0001601c99280007005000d8540d2041d440f03055916003420000140d0b00c4081e079012054140c03a0010001ca028a4524958464985000141440350f01070104011002031000e2048046540501031550b443d014110f8440d880e18030807100302d0b1142c00090041c106030348030040380d0302d0151002c00d0440d60031802d0b43c5502003155042d41c07060300440c0c5410170b110f410000b0300d8001205555582d0b4003081c101c18900c100d0051000103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206742176 1250 206740926 206740939
    0x90515010903110301060e041a070c052a04050708070f05040308030f0414030c0a02031c020c010f12110315011b1502041a090a0501080601020a140106090615080604020a090302 77
    0x6040f07901c09500c19005006407113500a103900701810314069000001e842d840d003030790003500003d542601c20388060001ea40c0c00802801d29102c4501d00b00d54441e001100100e1840003c80100e81d16500d82c0111801078040e40c40f126107504140c0310040880740f901011805001c000c100800c0043c00b1403007282d901071050101100b46032600d25024541c1c08100c5040d000510000c41c01d50022503001c00c1c94601e0910841c1180c07030b004081c802c5880407060044042d4090b801a80d0b09680035401070303002d00500581031070003440d0404003034560001c0350001c00f114060710402000b00000e100000c00e01090340d01003424807110020300c4521240464000b0700c8024501c140300440380c07460060390b40517640503210a88000100000030031f0780d480c3c02e030441d0a0080c8070340140a000203481d40a020708900511040c1c0c040d000461803a2035a000307180c030b030b41e140c40d509660b9a400003c0319480d5103e060040c243c4070001040020600c3c40040c80a000580700622940c81000362854098020060030b003200e0381070307608 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206743426 1250 206742176 206742203
    0x708190503010602301b28060506010c021309030801081203180c030601150e040504200a030c06080103020907030b010f030c0c0f290103050a0807050a0507090204090515010903 77
    0x190a8100031030075101117000d4001c110000c442e181d4902a050701001042250020382d4000c8070388101c900400c2401c942480104507040c0403e030346811890744098103062402200c0126408901081d411300a805103c2d0b6803202264201540050410b005244110050210920201e40c441c168032006d4040119030b50400b4100071429001d1041002c00c140c02001c2d94400c0d85c1d19005040c514081c9134641002034018071803844180f45c40d03c0f03400d000c2e45c2c0021881d0381001a82e495440d0300d4031442c04056100107000b4000000410b00e5251001030000e5076101a51545184180004204080c0c080d40030715081c80c000d080180d91018510b0040900c6190101d80c0c2854050141c07504500d0300c03009020f0035a011011070502180303440080d00c10101c42d00c0c1e100710840032006c80020480a000041c91900600000c1010030b03942e00241203a240141c0c255130404460303645041c136040843c0c4c402803905401007001c000c00c0925101d5982d00c0b010003d9135002079580c01c000207040310414000240f006211400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206744676 1250 206743426 206743483
    0x20307061b05070602150109020a0206070e040b09040809030c01050c0c090c070501020307020c0a09020f03150402090913030206150f090c090a03080d0606051c0c050f0708190503010602 81
    0x1158402d40110036286210b403600402911140340303101c65100310300d2010000138000040e1007150004807d80d4060210780d11501021150505040d16555015483c0e442c0d95000d6500c111000d80114828003841d1340e100185814503080196814102e030602c0300510090648000219508049030800c03180100696174030369100141d4001c04002074503e600c044100004c440d000181e29034003a204540e01264139030f60380c604409a03c02da8206260740079040c00810640440903ca4461858004002505001a14000c00c205030b41c100c0e503040c040700501e801d11080c07640510040c0c2e007008405103101c8240400707501068202e107141d5403441c0607114a400107001c7c43c00703d109440010000a02d070100d807580d00d040c1100d03150080820000c8141c9092000030384680a102218000c45040d21000c070700e600500005802030081c401c0c01e00c10b1140410081c9a110218002081c520303201d80c0354a40c580e00c180d4410780e0903902003503000d420301000b040180b21664000031550b4800e807208070440700840c4c2a01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206745926 1250 206744676 206744717
    0x50607080604020d0207030206040c05091501120f02070503041d22050109170702040f060e0105060729011401030905300703050c100c0e091e0c040510030902030706 72
    0x4030807090548040b9801b03042590125400e40640e01881c9904083d50700d80d0300300202600242da40200f80f906400301d41203594029080303c4a52503d10344000756503200d03101c3c6a000e983c8920401c031103d03040080c0a1002c1c5010b0041c12100c00c10703401c0c0780845841e01d1041080980b60540c0340801c107074410044003080000941150700712075886407412100040e95001240700342c01c0080201e21076402c020b020040c240345445014103c9085850b0b030070700399207040d060012590150100703507031324110001c02c000c5128079843c000c031105110368000c0d01c1c0f030340c50000c0c1c103a0541c4100d18020b04140c1042204c00200d10001101181c80c100c4010070041c400302d14079019031a40ba906901480180c0106000043c581c1010140510690308000d0381d2049840055010460316403040c41c1c0003103032200c0c450700214245030609960104e5003070b501c0000c02003070042c80e181041d0102ea401000e8040003c3c18072445c281440c080c000c0241505091281c030038907034006612010140140000c00040c2e04c40304aa00705140b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206747176 1250 206745926 206745937
    0x709060f0e1f0b03011a070c06050a02030f0c060a0614090402060903070302150d0b0306040816082701020d020a0b040209060609120a060510150e01030608030a0e03061305060708060402 81
    0x8000e525002962041070012130380007480351000c22000d04000c2e105444650f800c4a11940d4002c9594056a040107402e5805402800d26007046100038000025003d644400404030001d9910040000e890103040c450151211b40d08442407958011000ba021a112500884c1c0c2282c0d0488503030f81c80d1380c444004a40b902c44668006540300311400c41d03524403000b01c2801070020100ea0b0000b0b1005030881c405050b0303900c80c1982e000b0301e5a00104881c0307080c02410290003000503c9450380c24030340108143c00350411844c451280d03071055649440700e0385543c3c0400403c00405214000303041201e5142d00c07500040440100081d014441c44400103505540300c600b00c91030407a0040c11000e441d1400d102c00381c0e503200002070444005103010f0106140c4500c2c4050182202c036a81c0c3c030307800c0c0d00c201e2400c2156001a1401542d050540301d060105020038140702130100c8000c40e56030030070043c0008040600c0c0c0035010342903260300785902e44c045d804030b072020684562046a80c00c20f001e43d600c80502140c000e1041c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206748426 1250 206747176 206747221
    0x809041103040605011202010503070507020a0e0f070f080c1608040305010203040f06050a020711010c05010b030d050a023f04050d060501080d0e01300606050c0709060f0e 75
    0x10a1108210100c410001e14007840c0586420000c680e00e4081715000e40720001e002a010840c184001090580b080f001005218409448105e0075030b0f640040d6100e10506803078040410248000b0031180a0740203030b1001d9590114501042d940c140084040700070b104a100040c070f032040e00c1981a06111101c0104d4005507400002156207141c18142800c80c8400344c0313422580c682c00c4c14003117101c0644500907250595009505c181202000780015194542210001c036540c5d500c80440d10b100760b90a1000d07240e00e40e40b5850b1950346c0e04040314020305010b10031100743d00390000d904002c459894050010380014211032841322280424282021a03030080354001a030001900c1015010003809400c614101c4120381d0446400d04509842510012208643c85000414039100d008650107000004403070700c910700c08502000c2c0c1c0900502029203441d81c02010201c1d1000509100c16801080014020000010100281c500f861501200301101d482081c54445401011801102d082d210213110149d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206749676 1250 206748426 206748431
    0x71b0b1801090b1005011236020d241a04020a200c090f1e070903170306030606010503010305150c0c0102070605070216080303010909050a050d1d0a150c080904 70
    0x91a658010b1004800d01840d40000c2001f0b225024034507050194803010030000c514480010003032a41d098211401144540015000700300c00d01c05601e038100a404e05502441c06e05880901401e81d01101c4c5001184d026401c510706850ba00102041140e40208104116405661080100400c48282d032540c0c4a80102e1090102211040400050f011320003040c01d0700d00b141155502404c00d110a4421101040f0b0302828404800441c80340004480d88181241411920325403661a1132548400100300d480325540c0c0041806680c3c501000804d6002d1800d1a06600d50b6055566650321a0b10a00441207a03101010110745000000802c1e280e003070075654001c545520190a01c03001824098412401600840702030042c01601c0c040c0c2201521541802107103944d1900349900d00403e000041615940600f90900d40010400e001008510b211561500d04515000c1b9204504480329002c540c86009000707410030000f00c0703003500d910800c1c110b82420420b0340b8550511520310310501a000794020b1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206750926 1250 206749676 206749681
    0xd020408120c0d0915270f08011406011409210d0e030615090405010b180115020615101806030e0c0301020406080c030a0f0204060305071b0b1801090b 66
    0x540340c20107080302d907180d00100c0d03055008020080c1e964420314050100008140d44086241501680203030b803150440c540c41c0b0030003081031404000350b072150703812002c02c0d10301902d020800344609000d90b80440300300b41a406014105040060301004080490030080200424441c0055541c5010900550380e4035a020381040407005444e074465090008503404604c5048150305181030000e506031040b00c0703c42a030000010081c0c00c00c26650701c024000c44666490307100041603030701d48102c000c0c00f0035620714103501ea55042148580403000e0054070441190702c8001048000071070300318078030b41080341665a11100703846e144c2c04540f0010341c00341c1c06490980c48440004da469055020100c0c1520394015603040c0104c1402301800cbc0d21845c4034003000590082c021840030b04800c0c0003550051200e580001d09144811407403000d80c7c0180d441780d400b003551101000030154102c601840d21109003080702d501c08003540d440300001340000d032040c1a401660f192040003010300b5030200031a150000810344562 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206752176 1250 206750926 206750953
    0x90f1005150307020f06010303080a020d0b0415060f050f0f0c010f111305010801030c03110604170c15070b070503060d080d0c020f03042702071407052103040302060d020408 76
    0x2e078800c3e01c80701c0c01481a800b04104c4001d01158040c10ba0f42e165131501455241e002c0400301030740003601c40d82041032360b60205c18620340e203921940303032820b44170011001e070300d8504807000d06103c4004052000b88003081194042c042240021030748050200d00c02c2d1501d410301d509035507004120300004a02e20074904452440c0c00c0341311001a112604000b2150314095498000446110300d0030700c4010880345102c24140000346011192003400c040240a05040c00ea440d2f80c5448c1001c0d00842219a50700108011500b80c00d01d0400044580c90b8108031070701d0a48266200444030f00c00805800800034007001065280d96500311641c5a1900180240c1c4c031205000801001425030368800c00140c8645043d04001c0c92000c0b00b95421541c0e540043c105001103590916840c1a0f10080510035550811550380020f0901a080c4050030248c40204852070410060100500c504602400b20801c5208245011000001207800b0360768151455600d03030307072500da4000180c001c030342085503130703001c7e030700101c07112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206753426 1250 206752176 206752219
    0x303030727091a04232404021c0b0402040506030c0a020f0307080301140409020d120306050a170c041b0807050909070305072a110a0f081f02030106140a200102040501090b09090f1005 80
    0x80500d90142003012b540320b0340030441284206d00c5801d412401c14400510500f002801901c00c1c4a25401901c03030303c164410701030342941c0c030109044800781400300041c006668041074100d00007000352020810451541c00040b140a424100100300c200b80c004110341c02846604000c2c0285005000a1600e54685140c0c40c20f244000340105441c0c071404100131000e1806006102c6082008120310041d40807540701124a204001d0050060100030420b05516889113118244030f80c0e095a400078142c1844000100350b08015540600c0c1324550410400f03450500743c8908880d594083d400c404510b0f002400714141000d079500c45401c1c0034200c0400a074441e004a10360151001045000100c0e054040ca03c100f207020138007440300014880d41500404a21078801000c10900c5410036020125141030000b441068520000c580d42c0d401003000c0205580181112024006012240d03040010398008191510b00c01802020791141c1c20700450704007051291580041c000142090f0389004c03010100400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206754676 1250 206753426 206753467
    0x150a090c02122b1a120304050d06050f060901080d050a090b1602090f1b0309011503030e13110909130f061a0303030727091a0423240402 60
    0x12400c0c50b03443e8200220205105039400381c07080700f0080324692131690502640c4803d0f01101d12040c4000c001c007280d29a01d04941140452058001040d90b19115051030802d90010b0100c40c05200700300d005020070640411459820320161400d1621a1024007045600300c000307a00100ac0404d0025168149040360a06c80340158004c0da50001e45450300b01500c01100700072217042440c03068004a20f18000c42c5003000f560004800c4001084000c2c0d0307140340d048140b080e030f40214041b40200b40d0b4604c09007400409101c50040c00401088040d0404144e41001e100d4a044284640748035030000390301101028107200d0141d0841c1401140f440b452401c0e00041c00e00260f07020440c1d410310100141803500100300d034440c148a6031500036000300f041c08503c04c0a940d40f03090320265484c100c0030400f50920b00c01c80c164980000c403035036141108903041c00100c4a0149010640c410000d4903841c800e1140e031041c941005500184212070400510000080d0500d010400e034844d00005140194103074000c030301207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206755926 1250 206754676 206754727
    0x30402010c020f0d1e06111804050c2b0b010302120414070f03080307090f0b0703140409021c0f0603021008040201020a080f0a030605032103090106030524150a090c0212 74
    0x221103259030603110141c8c000c5000c079845e5103815044580d144d043c550001d580006074841450709090302c1d00c0440d0704110480d410880441020b9034582c501d01070b1170103243d90340102820b0443c03030004464110404000028400740c4172031650081c00e103031305004000ca400141040c81003084c1060700d92500000d00d0f0710a4444800040e030390358001c2010000d031000070341207036400c510541c9480001c0d40c003541c00d02189081050b003a107060200190b085101d000510175208050358520302144806503083c1211684054111040d14054007800140c031211261002e0072120b0030031580580c3d5910041b4500800d41d40014210038021580590368500003018080035641038600f84070054a600901d03644003115203d01d07003560798403448a41540801e4005603001045c2d80004104503440e902c440d46042021041e5a40c100108000d101010095130100b50308111900702d81c1c04564400c000164031100c080c0111040a0381d50511040306c0c0703008100042e2500d0104e50b1030740d2550510a00410204180c03103024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206757176 1250 206755926 206755931
    0xb0907090c02120409050a0902100e04061205070e19090f020315040c1a0f030c0310091404020402090102010b0301110415030b030303040809270a060803030402010c020f0d1e06 77
    0x9800c90341c0041140144225220040c50903e0300c5c0c4440040030f0403014081054042d030355150034000da118045c1e1b1306861171560701da0400700a5204144000c5440715407043c0c600e8203903030544c10005100400e0b000100c90720750000303a100751034904c440310310541003080d03400040f840c07c1190410002c01c2c0028103503590084041d504a1403810f00d80401c1a07004407001031400719030040600c0804010f4095040303a01030540800e007408060080108158415100021050404001c2040e4007590034201c40103088446001d00c03001442000407603200b400a40000e02c1140c0101c0c00c079010303034801d40c000e4044000080090080e1080b855072510250f02501540f60710702d080010010503a8001e004c6c500c000e050203402185141d4490701c80c140d0540200084580c4001f520701e9031040002c040502084e0005151060001801e00f242030f0011a4400c3d440b60354103800600402c00941e030800e1502030100c0e016642c1400d000c042c00c00103a445642090014500c902c08102d4410b01080340c80881d03581c43c0700324401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206758426 1250 206757176 206757191
    0x1203050106030e1e03090d06060509090a030903060b060d14070201240506070c0f2c07020d1409040e010e0705041b0c0507051e01080c030c0f0c0a0b090709 68
    0x1141591101c2480c103400b90300810018000790134103220703140a80d0a40003681e0410300300000154802945020aa840750707282d0f0b10500c40b0303290080d02560015441e41c010003000d04903a60160034207d00e44070190803d0b944840b01034058030303040c00f00c03401c0c0078008c00d0800809007440d040324000743d8242d81d04c100561800c0f410043c040f440241c0e603400c1200d640d074940320003803030101004042c1d4001481144c10403900c500000d8000c1901c1014006441a0813640000c444901642c04061a9103901420300c0440c4009002400c0d4002c64156000c081c207140c07100f514508011004100d12071100350941041c603140e2030110080041d0300084244140800b03071003d00b40e0b100304001c2900c00003000000301d40c580d00020100140100b400031000780c420b10580f141969141d00181944201001c1c207405013012550701d410759a030203501940e200510f82006420350a0588805100d40141c091342016200c1c00110090040c500700a00d10020343c4c40030000103945481c8030030350785800c1d43c0d208003501d240c00c0524 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206759676 1250 206758426 206758439
    0x5010c0306050103150306050a0b0306070f0216030b0a0203100e01080d11010e030a11150c030106030e01050106080c0a0c0804090e0f19030c0201030902120105010f050405061509011b12030501 84
    0x4510541400c0e02101702184d056031590001060041e00d9080220390380c0301c5180042d00e05001d020712401c416129444891850103010341042e8003041c0d030421007101a01c0070700000d405003114a402210f1240010b8496641050707080b26801560003907401511000000115200d000480103414050f80d03407060300484c1c030302000c2421307540b51441c0c00c00180c105000ba84880c82c4221b5003540748076903807011681103801d40f424104414405075500381c41194000010300a45405020b070305041044580200242c1d0725000e8000c0072a0000b03440b03404034110000b00c444140384508143c11040e0f4202c0c601c2582d4a58405200d401040d1441c0004082e01400707039010500e10010681d5003054580416119800001c7d54044440540000741241416a40e038004000350b00c43c003c5204034140a03000001301c0703504022403840b00084e6640018071036428142040b8041e00d80140700d0303200a0a00d40b12941314540302005a0359905070014101464640600350024010160711010011041d41c80c10402662140c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206760926 1250 206759676 206759681
    0x120c07050a0c06141e0913150501030b0d0c0b0f040306060b0304140f0601062f011e0b0102030409110903030d020423062b0207060605090903070b180a02040905010c0306050103 77
    0x5042c1400c00d009030b11710702020325920300148500030b0300030002c03a034030300200d424042150000101140152507001c4203218550701031055010f0000129030840042129a0320b200a2000c1400780740d00d0b074000070400d100b0030316106090342c025584c0550305100c42030303c1c1c01520f009908101c50035036200d503454801000c4040042040d00c8107503a0350f0058021a07007060800d8400d1a01e00315620340c908200790295052040e440c007104942c15490002140350415112540c04440c100702e60040540c0c40e00083c0021a0b800008071401c5900d041c60100d8000c0880340011094019144440e8060100041812074180035500401c10360744644a07425503807100d407071185809194007450a40190041043c401e1450302c4d040103008081901240003180401c2030b5104c42030b81c200c5a8215000c03502d03800203200030701c0c15004c8240d000c1008001507050441d2a141ca99030550041d15601c031892020262500300c035000c0c060004440e030080d10600c0304c842c0034074041c0d000703014bd066403c0000b40b6040000c02d5079880f90 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206762176 1250 206760926 206760937
    0x20a030b1c0515090304090f0c03150f03030c23060702060c120a09020301060b040b0711040e0a02010c030e030a0c030506060f031c2c03071a120c07050a0c0614 70
    0x1000030502d04a0f405200160f40a01810760455480180000640c9445030300442807010805080450240e040c2000602621201000b10072900c010090030b01000d14204011011240c040c035100c100c0c14940c0c2010b40c801d400300f12002c04003203103d12041306441800680c450183e0002e600325041c40d0340721408102180170f07181d252801540d01002040240c06640c001050080c001400003824540e9403113001050b0784030798400d0038981e0740420726005110f048081003d240006440a110320a0303025102ea45480324047d009060100c0d1ba07c800061510038035800c15051409401c851071a012814054005446840105c50501c00c0310000340c1c4034240034550000b52030001c0c0081c034103140d410032802688003009201c402000b5030b1840303618a000401ca1341041105100d0600200480400281420400f85401c424011a82d100c80c860503120128111800701955200e614419120307d454500540300740e840142c00391080d0100c0900388003000a4050889109803554880441103400000042c09030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206763426 1250 206762176 206762183
    0x405100f1b0519020415090e0d020109050316080c060a29030c04050703020c12040314060c18010311130509060f06071209170708070f0b031305030d020a030b1c 70
    0x4610f81c451601011079000e5125100410104458401501ca40b0640125511013101603444041110b519481840b000d40d201c2000c0c40203200d4440d140e21010f030340b0b2151165411030b04150105001c240014103042c0e840801003101503542d01c0c20a40710f1080030f0404980084000c0d04840e15214594100b000407401100000d00500941c3c00d2400400009040003865001495002c01c12896511801d108006440061560060711141181130000c5640c03140705046080703500100a000c0540c000744141c61710f02c1e414482805040c0203081c0100c003d8901e1070070380f0410304030110f00f6a0081e640d19003041c00350f03841511213071a103988550411910301000f403c60364010034100044004a522a580103103c1621814a06109070f69256000b402c000350011505c110380003410180244042485682c3c0200380d4211910a41802c2900c041c0307a80c44007801030b441662810071410100501401504c00321028411300315114900d482c80503000d0301c0c00050031403051034007020091405100d4101014555007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206764676 1250 206763426 206763433
    0xf06100c0b040c080f060a05010f060203071403190305040506090303071b0c0f0b0a0305070309120e0a03170703020601120507060807020a29070f050a0509060405100f1b05 75
    0x803103449040d07494401510a6032924110540420755520800401c865005550002c2003185030004d0f9001c2251410f804c00070001400700c40030881d590f40001501c26140c4c2082400d41c100c402480001d1961080081d00c02c410481c1418807034075150107502c114400c6000c3d20545041d503448050ba0b03500da1004960b180007003900700d02034070040402841c0e06a14144241202d091194442407109003034941944810f6801e040000e90705030b01c40c0e141c010580c0010362070409110700c04a980c1c0d81052855001120420007c030b6034802e50130365499104450045810408c0b524402581c2014000c09500c40c0400343e0142c8190000018040c207c0c14410440e5a00140a8400030307040034021100518064140c0c01144100c0c4503050104055030380881c281124004000c4600c004403911440f1094010b1080d410b02841d104d1010440782c1110856060f440d8510f8041e59501101c0700107407103401590800b0b6001a000c10302140180d0f041003400804620b0394903800340a10341350490800740e0944241c000c3c0310381c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206765926 1250 206764676 206764697
    0x703060315050c0313060f09050303040c06090f03030507061506050a030b060f03011502071d07090b070201080414070f0b0706140c090409080d090317060109080c10030213030b0f0610 80
    0x5c10612100070203610548020907228840d48660007541c0c1d5030f9105680d030b40c00c00414002001200c052034001400c1718142021483c1c644a9282c00f98483e5100280074441e001503900204011a80044400441c110f140700d0341c140c480d64018015000044c4000200303141041806072440c010080e80c20345a942e40c0c81e586036a091602d0401425940701580c419442420404140c01002d0300d40d840c10b00000140550003403800e40002450f00d0095403150340800780c00c00c40080580d901040700b070340c001d070020700c2042e445c02c03201c0c0803030328003401075004502c500c074a0301d8082181080386000304413060107a0020301c400c0003a181812a09a001e40341c0f107401000402c0b00010302d04142d0020480e03140196002c50501a0098103003060b1022801c04a00081c10403c00307032502d01d01405920f070482020329060044c1403c113410386030340f00042041d2511403500440043c400c42e1094040342d5003800082410032480d542c0b031801d21301c100303001d94800d0b9442d103038200040c03150b051000c1d214070380760305550380c0541d001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206767176 1250 206765926 206765941
    0x30b15030715020a0b04030806130506090f0405070f0303200105060d06092607050f010b10030908040b0708040e01090c0804021c020312180909330703060315050c03 72
    0x390a842181c007540205413803035010407041001948254007a84a420040c9040c5040203032283c03440400500392032628083c4181a00c030318119030303802004c0403021091601c6606119150044c2c56218030070420b000500441010703401513941100c2082848a048212095081e4500762801254500d401200c1c400030200410010b07041200c01c00e000b8590380203451100c010806030100030044807000b0a10010b503017030400c1020003095481c050840000c002c0b0b1810300d0001050120003a112600309a1203110300d01c1130141d400215401030028000c40c0e40e6031061071402c5010368010f48502c030048100c950001038106514000c1d01840b0441d5039070800c0581c0c0b80d07800c125070400010a881c0c82c403000141c0640050b18200710381030044842074880c6490348a042680088900c011140c54081c0101c14103000001d00e0001d400d058501c4071250613441c1e090881192031000840d00070710901c81c0484000e001800e50103a01030030959002c0c511190b4101039031401103080e104c0690b42d280b00c80504100083c0318 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206768426 1250 206767176 206767199
    0x16020f1519022502120606010905060708090d0605011703070f080a0509150903100603020907050702060d0f0b0f0102150a020306010c0602030a05012d0501031109030610030b150307 79
    0x145221401d005080508425a1001042e0010710000e0180c20407030b840c90562810300140d0300601c00c40001400540b40c038a000804c0440c031071045074040c0c1008546031007009040b07400d4078289500079103582c0d03a03044c43c0e040070f0300604003c2c8241003140340c2d05440d02c2d014520100480352110b41042c80c0c1a281e5203541d54052480c2c1c4494252010400180701c4203056a07103ca42c99040c1c4049048030720307240e1039038030101414107140140e0031140038502181007006031141071903658031400504182c1d84030000e034004100e4030301c03c8110003030495144c140a131840760030076407190b008985c0948446080c1c10480700103980e262944031b1030030340341000400000c1c80c81d0500e8000716030114040c501a007224000d030f9920800da0308151362001e0f40b5030b21540140301c82c0c64a071104260070105030b90304502c407109142890f44031050310300891781019259915a01e01940e001c0c120b40005002804444207440d16500503070903404640401c8610454200200c2c1400881069031121400d0080142c0825850314031003050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206769676 1250 206768426 206768461
    0x240108010303020d1d03030307030e010e0c010c0b06010215100f0e04050c0d0201110a0c15050a0503010b0d06030f120e0906180a0609021b0c010c0c060e03100516020f15 74
    0x4171506400300d1081a920b060010714054039440e14041001d14268034002e095403c088900111030b4000f40140074261b07480310903040f14540085c1e1951030794580c500101e00340b09100183c1c4244149400034403800d104c064540c4000c40b400316812024003903c03540b29107040442a03d003e060745d40070840c00e19461410912500a03984141004011035048116082c20203010300c1081e2903283c3d011900300b009916006500c030040c0303024605030b031400c1d110100c003601c2400103010b03018a80d8400b0030b2410449049602140181d0b41141280121103281e10704006030101005010300020266101c080301c50030a441c607039001d944000c00900c1184c46102903400001c10040c0560449070300c4020000d2454407502c010701400140c0c01c100541c030a04038040528008400c0302490401901e003004002040625411400b5a071840c41c00d42070040300d0f00c0c0000c1c6041800e41c02c030b040340791404042c014001c1000c03c80c0c0504e0455602075034440c0b80042c12284e290324103240021217411400c400120a044140c25582 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206770926 1250 206769676 206769707
    0xc03031e0e1306051005070203070506040e0106050c010f0218010314040203030a0e0112050403022503030207121b081006080c0a0e180d02060a14070c0201030b0d0209240108010303020d 81
    0x29190b035181d00017030902c0e05a545031004514006062002d43c1003d1012502902c030a0711003030328280c9040c030700c5401040c051280504001012030000311540081d006100c0c0c0f4901c0d0f440941d01c0f84920744150181c00440748a440c003003403900c0f1920545603c1003115512541d0018040d5003440c0303030f007082611943c046014140c104002c0504414203002240301e00c5004a02907401050210b1a076009205d204098001500d42018811000c200180d4000740d9441511030b014011510401c03246041d003c0c800d81100c03203110302c890804001ca40e80300001080a0180301c0300200340a403d070b640070401d46901c22851002e0308181483d85c10700c1705c110313500c40700d6402150841e541c03014a12140281d6042440c08a0458010380041e4107120002d03c00b805101800d80140704d602c10a070421850182c07c180968100130305141d02c03800308400550b40d0f00301c5001c01c0380d0060070f00070003494038000c030142c00009009001c44d812141660341125501c124407880c144d0358107400819504a003a5815594800e200c00c261 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206772176 1250 206770926 206770931
    0x60806090c0f150d09020103230a0c05071a0f01331b0302030a021212060118150809120901050d0e011e0209010201051b07060f020d090c03031e0e13 65
    0x1c03000002ca10010710900400a13000110024284001001c0e42c0200781641855094002c44030440481843c9541d00020401c00001c3d00c1c1c02000010340c2c06001c0e032800904026040e000203c00d030344104070050720522880c18141e0444c0c4e280da4403d848007422001c9048119288108410801140214604940d4960501d01001701c00703a0744080d00901094022001608046005002143c0400c4801c40c902c680c054858241060101c1d901c9540c60024100780c10812092040400e00c0c40d00d2201780040c0c04426105802d203641d443d005406084250750300f8806205030355040f08004a4102a40c2140d80141e488503e0714201c0c1080c540035248008229950795a40c2100c040c1d02ca485d0a42c00c1400c404607140580c40d071450b00006401c55000801403113024413105002854803000358215003009920200008032388403480e410100901640f506650024a00002c030002e0080400481d0304491280d5a614400c0580600940004407500500d01c0452403080c0020481d2030481c0e0828003d44040800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206773426 1250 206772176 206772199
    0x90c03030f130e010302060f070201030e010c2d02060f0c0f0a08070e040516030c020f0601030c03120f050d09140703061e020304050c01260106030f060806090c0f 71
    0x80c1158060819061840d40015118241c040302180301c42c0107103400c0c802880c1d07540c55074000c6465407041d1004c003a59000002020700031a8040d5014901503401100200211181c1507000341480d000203a080359664030050704201c1031a5485502c00b44105640d001d0f24031615550400054440040c0510000d03c02c20f02a005005440102605d480000e43d91007112a062080000d05101411501d04d0701a030b042604201d040e401d140c03194445079583c4e290019042d100103104031300b401d408810110440c00340c10000030074000d00c07540d40d00580303026400305c04804050700001d4541c1c1c141c0030350304404150f0070302c81c00e00c51b019a6403081040d903004000345241000d00940040c207003902508212141036444041d251134100da03440c4c1c4640c0800e864070840c80e40c10643c859540d1aa41452103074100500c5441950340040142c1d20801c405085003110421561280b002801401c00004c0c074210480c6844800201d8002c00100d09001d0647c150140c0501210003052010350002206040e4201160303421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206774676 1250 206773426 206773429
    0xa21060c021c09230306150a030c0305070503120c0d05090a03150e07090908220302030f0a0317010b03040b041410020d15030c09020304061b020d0315061403090c 71
    0x2503045682525985099195040840e0741c81c04c0311080000c07280c486131500700459282c800007100780d00021002040e00c865044480007400c2d50405400c0107010242c0e0700b50000401c03200007002401d40340c045099803088940101d04900d907000d042c4c00c9105591185070146030041c000c0c0000c04080750060f125110341912615040080508812108040c030380e920b10803652880144460409084106004e11002109171503580560051141c20a991201c409050124001031300c2070b44015030380a001c2e620b0700d00c050000991240e106140680204000038a511403040944050b1416a14441111801c1d52115202d44202d2400103000300c83c00120100d0a40c118281000400c004008207c3c1c00350369050f801c104441980d08142090039500d0b80b441080c00010210304601c02a103108600040c0c0b80d0380c5a08188010704101c442c680710316003d401600c14507550209aa00f20801140c13014000008906941405e0138524440e120000c3e56540002c005290200b0003180c20410000450708204100030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206775926 1250 206774676 206774713
    0x201090c030b1605040f0e091615081003020a09050901090203063301050403080c1c17060102120a1b050609030307080c0a0f030f090c03060b0a21060c02 67
    0x10000c0d80d0b84a020400c00600c2e6190031000c1444200925082e428240b91400312100b50380b55000e040c0e0f104c9001000503407903070310400511003884a400d0246400980d1040480300c0750014100182c001015900000c541d40c0c818a480c4080f0b0380d02070140d1135098901642c402c002c200c0074102170569501c0b00003040159408000541c054000500c0000e4441c05441c5000d40360402c860410300390902d03403041c1c030f48240e8200d0150303030440c1e0300200900e940b452840e100906008420f408066036001b86001c640783c49503c40201214100c60000c00e02031a00c900c00160b0741c462103e091080d03024010018403901c0c510070607207080840c00c580c01400c2030091039921681400d07022036240055500110400c41e025034000030940c0c002c3c080d01580751034030745010b20051480030100c40704000d2503102c406000000480e40d100759802d80c2c01605080c405901c0e840d00c3d40140100b00b00302849900000310100d000d01c10825859003412800c681107400d00540c0e42e41c036014100c1032850800f0742c010b10a12000000905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206777176 1250 206775926 206775929
    0x30c050a11120a11120a1506050f0d0209060103020c0106030503030f10060908030d051005030f0f12120411120d020c09070e10120b0d0b06031209100e010201090c 71
    0x1503400784801000041808640310110a20002c29406100c09002181000400e050301e41004e9402d1300035181c20780902c034a05440d443c4001d021000f4100c4054402c03019500080a4400031156081102d400000f00315204d081e000c00607622002d10070104e0010340c0203a00500001e000103002094482d50303522414110341044031249242e40124041028601440980320301416050400b0544203080c284c1d503030754a0085000340707880aa034400110710002da41c0d01800000740702c010304a8480703070306e1009640d8641240f0306d200c40c5144601c3c1c3d0b04030507000c1d4103016034440c02c068038644c0240366110f468601180000303446080d0001210002c00c0084078090001c042030f1400350f001020001200300500001c0c1c10000e0608081100504002645603210f41c1c490114511030b2501c503425080410810000b0410b0b1050180c1c803003842011030f070070042903004851003000100c0c180c80481c002284000124460980d907164800003039250b400c0c40c0344c014003488220321010300c000034032240a42d450040701c4045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206778426 1250 206777176 206777183
    0x1302040b040608010b0a080703080301060f020709090f0510050601020a02010e0409050303040b011809110402130b0406020706080c0f04030206030907030c090207060f0b091501110d03020a020715020309010c030c050a 94
    0x40d80e5030320b08113080c81c8051b00010214030300101021450360304c0e2000709010601a000c01c1012080c1a80d00c10352082020781d01425500754104868030007458000c000c14519502182c040c0918880c0300020a00d03803145070720950060b000303070580b042281c0c0112000c146003400305500070317655116800411003c0028511491003030307c5c10030300f950400710320481b01c5e400040e0581d182810303c5c1a00d40021028401080015019500561210b6210180c001400903e40052888141c003240c0003c0303255000440008441654403420134a48030000d90102d5440f442e205203000380005c00003000103040040c01540d003c00c2c7d50042d00c3d042501e9a99440584403554000200e40340c0210704802030045ca445800d030783da0780e5013008004400f80c0d07101040407404020103004030030f14800655655640110442000d20b8064019110090702046000d40250004000c1d4001440f03820004500401040700c41c000d502400d0b0001c6082001110044030301c810117040072010004001c1f0b60f00f0000741e0800403882a03910 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206779676 1250 206778426 206778431
    0x605070201090e01270207260c060a05070e010206010302061615020706022107080a0e01020904090501020406110a080d02030a020910020a03022401030b0403050c070806060108061005031302040b04060801 89
    0x10384c100c0c00090217000703031a690381910403c0144006010f00d01551583c005001c010406c400c03150703101c3c0020707000d460031102c020b01540040003041c002580c09140704030003d845040311004214012a580ca07400d000c020340141042100541c0c24840800002a051060300c10042204082c18160180c2c0c200e008107c42c80352300030810360800395140c0b41c0100c80c0c05034000d200c8030324508480c00408040001c0c0c44e490407103a0fa10791011a9034000c0d011607417280b00141080c0550352040c41d0240c001c0d8401d102e140e000803403415605032007401c04102c0289054005141d0703804c015800c40c01d50001e41c0080c00c0c09000035400c100e141e900d0745507041c2c0701c1c650190980103401c1d00e8801d810044d0074180c000e48001911100103603481031899500035054152500452020101d580b54a001e94807071095112161051040300000a00950b00061040c0306920aa9030005a62a40e00c01d005181d9400091000860400c2c4001402c0fa10b60818401070b0500003400410390079802e1b00868100c070000e4200d01c0b030b180d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206780926 1250 206779676 206779709
    0x3050d030f0209010e011101110a0507050106090608030a050a0c0c030510050117031c060b190f080402091303090510090509010b04050a050108101a12100608010605070201090e01 78
    0x5416115200001c031115000b5841c1030412000284050355591000c3d060291850a0703e02080c002d5004040c030a2081610507581d002020001e0107030703001340d00229820340c03c000b00810401043e00811080b6070040000f1418021346000554658010701a200b041142d90751607140481c0320042c410008601400c0038040085d20b407005603040d590142c2091640c3d0050f642065441da20000440f40c540980e00741c0c0c0055408540099000703802c00d684240b0303034510702207143c021160244000030341020907504c07003001ca07109511050350b02c000102c0c0e01941c4102441c1c00508800003100e1107010b418803c1c40c01240d01504d41001030214010300400740001a80c802c002d00840c24100f10540c094001c484025040510f010005200c00d08507020700ca04003d450f5000c2041a000e900036480509109154251003800400100900343c00c440340c41130b10000300703c0105042020301100c3c0010b8503010368806005a08000301654039504c0108103d04004644600045101601101d58007820314100c82c0500903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206782176 1250 206780926 206780953
    0xf040e041a070c23030d020d06051e031603080d02030601020109210e090103020303040303030b12070803091534200307150f0822110405162c03070305 66
    0x2000c2884c06131032501c42e06060b41c0d0342070600005546010308000d502580c0c5000c1102c140c00500390030740c801600003529003000015000c103e440030b0b428034015000c40d60805082450004110914440030700011420084201c10012030340040d54807070340600001c504909560b88046020181c400d0400c50451a40e14401445522410024500c00f0803501d4612550442d00083d8880c8668030000b000e140d600c0c19444c00300d4603100b00320110340c0f001c07405940c04a80c1d281c120310307280c1d4401000e9034070402040c1800c20f40006800f013991000420000411008061450b01600341c0041c0303442200030300a0041201c0014150b401d901c400280c041c0c154160800e56142030600c0c196161b00809850352440380c0520781603510100704c1a21510310700c0c000d407043e11010b8484140240961103805c000d11504001000d121340580001e40100b02610704001d17651b103040f04585d440708606091800078000a5840c81030007108001c8003c000391b040310100e000c0c001a0002840c0000507401125150040d03203000250 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206783426 1250 206782176 206782193
    0x20d060e0705030c01080c030604090b0a060807050103020f09130f091109010b090d0f1b080d110c03070506030c0c0d02151005010c02010528051308030f040e041a070c 73
    0x401043c2c0081442001d03440020b000c4260043c844480500c020001801c2079030395800603c0f906402000da40150b00700b00355200090042c600904107184a80301d400100c55101e4801c030303481c80b03002040c2641000c141204200480050500b011445500c48031007281580541c0308250005100700070107841015120140094000c050b404180300c9102403200c0440c1d9156400700041d41a807003440f03000130900380d142c0802c032039880700109035a0280420012500c040000380c4404c2c0d500d89510791140450001250703503503450050407003135091b0708054020013032401c0c850003a580008020100b0340c240141c10140602c0d040e020305200c001030b40540f214a031031340c2d108908590001080c00000745402d081c5070018022404502000b810000c000400c81e0012903101c040c85100307622a0080681518007181c000c2981e000030b000c044440d80b2081c0000b521190010031504100002004c07071f42810315003205c6418480d00200103a82008030680c03007030000d805a0141a200d83d01d80c0d10b403c28541d01c0c17810f00381072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206784676 1250 206783426 206783429
    0xe15151c02042d030503070c09200406030e0f030c03090108070c1707020d0516060906050414010507031103030f0f0a1509050703060e04080d2a120603020d060e07 71
    0x14644100000c0c010a0b0083c000c8000b050000c3d414081d200020540c1d80080326910f40c4003510381e01000c54400104081d0008000448180074028003800c980f43d541e250200f03440741c4080d00c01210421007040b90f03501a070850803080c0702e00010303070b80c0302c0d10001c24003410750b0710005400c211038200040f204065030b0021002030b0080c4051401480400d05555484148004a44480c5100304007280c080c08641c0d6800303581400310340c090280c4041c505c0e5081e81600400440c0113a4000c80d07400c640100340540f2442c1a0340403075584140204030841504015281c51b80480c606400704442510040d5101d102013004502450b4105070120b45403078281c0360104249005481c80483c0d6042201c0d000004518a8040090740c0a000b80010507440daa08141c001b885107520500c07081006808110502201c0340180c60211004203052103410301005110300b60060280f02580c1005018a03180e012074481c801d807040c40d101018001507100c2d2640c0019003814440e6400301d52050300d503002e8020594041c800302d0b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206785926 1250 206784676 206784727
    0x2a0c02181b18042715050912030a09020d020a290406020a02042f0306091806150301111615020307020309091b070317010608100e1515 59
    0x7820250010503802d0054000869548900d8680c1c2096032200103042c0d5080300401e280b0f904028101d880e1070b06996180d040c0742d60308011441d12001810002d00883d080300390341a01d8802500e1960340d00c2c1010003c180b000c00598000203000010310040c1c6030590141c01030411300e03200c0c1c81d89203414240081e0001e14850b0a000500060001304065038002030711001d83c0f64115408141000e910003c00d0092181c0c400d20801c0c00f0105044000c440b414000950040c0820398071034040c4c0d520114105907132500d18030028411fa00c80d800040c030f034800e5440d406410400040000c03510703c4214006981130b4010b40385015034201a010031004000c095200c520803071407030741c0e0103600b145444c01c0041d407240501e0034080d001d4a50b600004950b02d10030501284140b2414011070385441c0c0302d0a0060208000c030f2a500510880c5000204900b80200d40c1140303d40c0030782e1444136569003804100b0b00302c40c0014100b503416400c400030806a6039107090700d10386d2644c03481c8045501c401c0380e01c00350004e0f2180303264003a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206787176 1250 206785926 206785981
    0x70501060803122e090606080c091f030902101d010c05030a11030702040c0f1704050d0c060216050f24061c170306040509012a0c0218 59
    0x482000e00340f2601698070003141d00e100d00601e015180c003072006030695090482c4070388500701d0101d84220380c1d621002c10b5941c1036035100d51984e54048001030a04c1128081a441071003084403040d120005000e104845000d45404103e9a00550103e40310416840182010400603c901c601028040c54204550402440e01204444c40e40e100e0b076031070380708040300b1804002c6a424038160b80c1780c1c00c1080300c10143c1e001d0710810000880d000010300b50740f100c4000703100040140e0150242454410f85090156400002a0a000794400350036200000c0d01d5108844182d020300550b18104204481041160b000d01c000d41601c0765400b0340700c2c0c10545058450042141d4000344407a17043c01155202d80e0002054581c51884194507480c241c608281000050000d075100006401c510354500195018500c15a0240815150034070001e00303807a43c9a01448107200c0080340600070f0b0450b23002c1c4070524402802e0081c02c1004903001325241141c0818074280324003881c2d0034001e41c0030900050151490303200341e25 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206788426 1250 206787176 206787187
    0xe060604050915010302010f140403050606040b0d031403061c11130905060f04060905030412110f01050a030506220212010608100b0708120108010903020606011805090a09050d05070501060803 84
    0x10801e0841800080d0422003000c2c123420314a806009040480c0c41803860f45600c0d250f0b240b5107141d4402c0d00301c50040c042c0d4240b41018295042034800041ba035581030b00c5070000b101c8048030040d840e80005010661000c40e6207060504c1c0500005041c0080703024a0400040c60100024480a03c49038040480f085140036058008100045001a0440008660030415031a0b03400d220f00078110f8000060254000050000b0b0034906a96200c115148039072420101501021304010380000e040c00d0707042c0806c204000050505202e5402241e10080040c41000e001012004822a6400c0d034010f0400d184d50000c0c2011409280411190040265140c0805a868254105249480d50b445002070603800400c044040000c0721702511a1054040d0b0520140d607500c04104e400380c4901441170b405809108003141d400d510880090800d898103600c484c0019180000b800b8889000610302c44c26580d03107900150024400b484640f030340b6895562440e44400b030301c3c2025402c64415510551203075108100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206789676 1250 206788426 206788453
    0x7111903020f0613080601081c050a030b030a0506070909050c0f0702091306090804030b2a1c02070b220b160201150b040f0f030807140a060e0606040509 67
    0xa40105680e41a00c1038191164020085103903400340030340c3e9011150340f508021401c2680080d0640c125100711044540901d0202d094400c0c20222505100000d8010000030304454069007203082c48500c090b00701e4114010b41d07142c140c20000240e401500081e1904010081c01803d4024507411000b440089441e001483c44001c92174070840c00020300541400e07001440c40050300900118064003c0400d008004c45854281c50b1544140400c84030300a60313802041c61420300d40b2000c94401c2840c55580ca6144080c44145025044101c0081844640b06099488441c00340040c00301c8903c2a00321101c1420642e0240e0042180740200255186d0214510030120303090307d0f6000e8014250b0322800401007007400040b4050a82c0e10010710031142d0198000030074070b81c040006c1080314190b4a84a001c1c0383c43c3c84543d0083d160910000e803501506010079400b050f2442000d40c0c09040b90400c80390255000d036161800d5032072081c0d4411b60f94004000708802810140030b041d40c4020508094035482e0201c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206790926 1250 206789676 206789719
    0x60f150906050f040c111c2a03050903031b01020a0201141608040c0e040f0201030b12031c02090306040c0510030c121104090207050705030d08060109030b07020102070f0303020711 79
    0x10502d0304c201e0301c410300810500e000d5036006064035a040e040c2d0321f030700c484e401c2c000103107100e40801880060140e14000080c1e10400c0c06064001541d51042c040d4442c254070126140c0e0445d04821b5898001040000c0c240003680c5003051044a49500140e141c80100f11b000c0c0c01c444101d010000d11076810303001c2020a0b68401040c285d1422503090006280c0c40300c0c108494101441e0300040d13141c2c7c058509010500880200004500c1d1003641c041c451040302009001c1d80d075844525a00d0107600c24031a6403001c004c00394101068040c0e4000060030002ea0200080c07408105840c02d4490f6036503001c0a000a080240c41402500c480c1c0c00e0500c526089038100425108420345180841c0740c1c0c2d01030a18180b800d81301220700504000d04255114107403030070400d8403030004ac41514801c0c0708000c0364503689401400e000348600c1e170507120122140e2954a4030200d410300200703090f0841d5402c000c441e002804a990b03d5003c207010b56401610f45002c0d180030701d490602f80240504c0b614452170004041c1c000350 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206792176 1250 206790926 206790949
    0x30503010e10050901090f0e010209030c1c020d0b0702010c050405010509060702011806030e21030613110307081801060503031606200702150c0703030c050a060f15090605 75
    0x5424004881e03460b031514000004143d00070560010701c000c000604100650401c64501c034507228100070005007944400e00300d108082c82960542c0043c03072012080d00e4025071203c852a81c104200f05880340c0d42e0300090341c002500c0300031a42d441c0e515090010325a42482507400b410101d04240b0719050030800060070364010041c00910410340000c440086912030750071082c500004648401100b6203410014020305419100d0140a03c61000400013080c5e1092f000398614a0050685143d91207110030f20200e264a1107503c00001d17200d681c1e01001c010007800542c4101c0c41c941d2102c04904140c80d8207106048140c4020001e40e0401e6814810303603601008803101040504451507042c41c02d031502101406070541140001002c40310106040600c001c02050b00c580b0803207032a8000c842c2040e5000d100c1c056000d00c0030680c2e1006a0038400079002c1e107554001a4050011240302c08000d81c2e0794029119940e2000003010303110b41c0055200c144a42204020307002e001000d01042d41824040750301c80000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206793426 1250 206792176 206792189
    0x8010603031404050a12150c0503090114010e15030f0d02100b090f06040e0c03010f2a0c150605100e09090304060804110109031a01030302150c1603020309030307110a060c03050301 79
    0x44c81c0607800c00c001441c07440c1040d41c7e800f906000b00b465080c0d000e0881c1d001180c84101950070055441a080b0285840d41e0581d0304a004060b0b0644401c0998150409050400b6415110743d07001990441010800724042400f554020070122030081209410384500b1501d86001e80395034810702001c2013201c01c501c0c0c2c2c0808255000214002c010180328500307860070310941e030103500e003c4005522880700d4002c00c1c000b22a400310442c0c0216104402800019040ba010001500887e80180010030034445005040d440c03180120b221922140018101146040710902140300c0748080b00181c100b00c1c101942c000c3c103c0015509086c03138043c024003130083c020001816885103490700c21441c3e0080c0c2d800000b41d80c11203085072840b034200c4080044014203000c281e01502c9000901d4030380070040207440c0c0c41103241d44034560514103070110b0300c56000c0c00c2d8002181540828040021103807400c101408807e03008280400c03403c0441400e000001600343c001104101501030300e40d0219412100310780c1103e07135 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206794676 1250 206793426 206793449
    0xb15090d03020102091002070806070206060d150f141824090109050706091e0f060302090d1e03030f02070305040512030702060304120315030c1203030b03060108010603031404050a 79
    0x141c5030490084c0300754500943d1012803c44009605a80040c62500380c82880040700e640307031141e040aa82d24201102c040358443c00e55201c41000400c074001564402c4890b04011a9048026540300e042d15140845e00c034038450400200320394212540b066040005016000d00065245000c003c070a040d00140c02d4103819200c10046a00d10100b580090303030700c48c0c00201b0396500c070b40c03102c000401d00d9489216030780003081e0350406080307070f1031050103c40200d55003070603042e58582c50041f055010350001d00c0d000d5444240c0c405140045002c1c00716206607541e007a80449074001d000e24000c0d0032141903c010100d140c0c03051241100107604202118180c0d00121503001407550104000c1d0f20314030413000000e40020001c810300040004a0255400b50543c07500d00344408166001e040c1d16524162001405141400740f080220088020626484900030700d4042a08625503011902d07100081c7d1010b801607542c0c110810074540c1c40840a014a800d00401030324052810300007030600d030807900400c554040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206795926 1250 206794676 206794699
    0xc03071b05030c03071b080c0114090d080c0d0509281a1306020604020a031e020406080d0e06030408030601140c01090c1e0b030f04080f04090209040b1509 68
    0x41540c600c20005a404021295600a103508407601e81d004458211400000c22899070000303400441e0b4a415a4400c100400840940700011500c000c0700380d00c1c1101c043d80821820029480e400120f090140c02010040e5498065881041c40c05c1034480c440300400009010010155a8004001c12800301031544c50941c0134400042d40401c403e29402102031140c1c040708807280140d100003030441040550081103107d551031205988948084034005d50103c5000030a00c001046215802022010480c0c4c40c00416940d81c0490708461450304010125070006040070011640440c9101d9801d805541040c00c500301a5900e241501020340824140502078807000c10380280c03c0103a94030500c415009000781c0c0240c6c100007121405901401a140c2e45040b4080728a921015103035040f250a81040c900d9075a030048030307600d03948003d4811100c415003003040160482c40702010780041c0c446034030010b03620b07100c030780410049441041d8000d005039400e40c5d4614080c0e580e00240da000300c10075900102241d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206797176 1250 206795926 206795957
    0xb0a020c1902060f1305030c1c141e070f0807060c0b1506040b07120f09120807020306090601060305130803040f1b0906030b060d0c0315020708120702150c0307 70
    0x5004903045208000744c08101d2405000095410000700d400c19400d40d1a01c6090031306008103130059540c0176901800607202c100009102c080e030800150090020f442c204200c0940e000c3c81000c014403c2c207090f41c0907810500c1401407518501004016620050100c04c0c500302c1c1c050241440e860b00548101c010900040f940f0301c214020142c82ca800800781941c3e2500c40003960030030b801003501550070344004003068015034003074918841030b000e00ea16102c486074546004a21481c1c500b171800c846000d014461000180c42c200030b418080c0b031440010f401e2a40c18440c008003101e1000300400c40c41d074440842080032078007202c101c1c1d0308950040c03a01908500e00b42800f01c040300c203d100103544140396400026819074940e1100d0300f5203104404c1041c3d19201c0c0b90801c088031241807009003090090040410019510b04050301c80c202c031860015080030015115036003142c00c402c8448050341801c2c000c000381950306002c3c580350307038925006e421b80780c1c02c282800840c0c5010091524091010340c0c400800342 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206798426 1250 206797176 206797189
    0xc030a0b150a0b04090f050f15060d020c1513030519031b1d0d05030405061c051003140312010b090105250c0e130308220c030b0a020c1902 61
    0x2000c09030081141d50f80d1010b2080c0c5a03485441280b032040d14003402c03042c3d459400e024450044010a0b40b43c0c02035124013a120f6100014120a035501c44410800c07424461858000b91860320880d102400c40707a10707155401e0344280070003003100d1803009205118200090304602601d44621440940420781d0590786010f0b401041c01039500c00202d03800a40446805030f1164000c01101c02c901048450f81134100107122200d409888014007580061005012034203000c000b03842c2c42c000802e10882e03200d0412108004072a0290340c2c02c002c50200c2e240038002c1c0520981c00031a8116084011131030030b0614500e6455140c418022540f0011000914984580c4180250b40551002d40c45000c008880c3c102500009a070854003180d00702c0030a500081e001c03148a00701446500c0c4a2000032201d603043e50201c4070344400600030316210f80204401312040d00800e807081c214a129103c00c451450440c245481c4650004106100590040110000900c0d0100d00d100d203013018580c0401e01141d184c800520f1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206799676 1250 206798426 206798461
    0x6070e0a0815071e05040308030a060302061809130201020303070c0206090406240507050319120c082e1a04030b070f090501090f0b030406060b0a020a02030f0c030a0b 73
    0x30700c1030755500c1841c030180c4081d80b40900c90503102c200c1000c00040440403a01342401c41e140100300c0038030080000c555004c0046501000b0321100103003040d2a0382c00200e058100c3c0c2c00740386a121001032194598201541429044400c2031242040c0000e075a000030741c3c0780301c014881340411850101c0d1008648a0b02c0031340c1c01000b030060062114dd42c5030410081d00032040112090f410894001c21149070f801641225032103500f2001070340c07409200883c00c50310a071203117201904200c0760008501d050044c500c603105d900c0c4845d039607400450804d102036000d0351360003100c0c1900d103950086101c0c030310b40c0b208000181104d01174220706881c3c0c0030f8003000700c3d0302d4042c41d030000d803410b4641d00402162651044140400f500705450303c01045865500444d540060390103031400e080154007062140d0340c0108095035016208448c0400c4c8151241441103c41c0c220a07400300240c0c5c0300d00d02c81c10452405001a882d818081801001c0c4e5000200001c0c0c3d13211518000035003015840d4022991280c0350b02101b45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206800926 1250 206799676 206799689
    0x161e05040f0b010e0609030d2703030815011815020c030708010501060206010f030312020c010e0d0201050a0f09051c09170a03030c0509030c0111010b04060902070c06050a0206070e0a 80
    0x400e1141c8050070a02400a002e0b8490024445020040709454050143d45c0026000790051008202d000d00070f4944c00b01100f104429103d1007130030400440300d07440c44103016520036650040c030360812440880d420a2030400700c0c0e06100a500fa00e9864015004020048030000300300a000d40d039080380140d00340001000129094020810081103a41054200b14101c032543c0d4226000b503030340e4400f201c841c80351a000c000c0c0098542d19106891502d180c01601c0e188101c0c900000340703403002810301381c5081d41d1407d103c00544d456404002050841c0d1080a034102110802480010a6030b0b0340d86413200300c2240d0284030a1015403442d42407910488089010b400f242065005000002491a46e1840c5000003200041d0511340c4601e4150701c1002a00c40c403a02c0500180101f06d0507600664a60030340d1141c0340380b50340d83c810f6508441c0d544d41c0030b00d00041c10b211200603039921003400c0200503178a241d080141809410421100c503241e00080c2294081c085140c00225181c4031000650440c00590180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206802176 1250 206800926 206800931
    0x3041703181c021801030b1311040b120312011806050102030306040c03020702090106051206010509010c0f080c100603020f041104121509080a022104030b09120c070611161e0504 78
    0xd03c4d00740301c0c0c58000307043e24010b0080c0710503aaa0242921200d58080384000d042c0007121012006900309a000050f20b150b00802e1404419403603105186190010b0001d40256601c2d40c0040100d03074505440d00c0440d1030503a90078400942031100107035480c880a040c150040b6a22014034910714031942c165000d1642c014003812981d60b44a0b001401600461641d40009410801240543d13020714112520883c2c1a1108144070071152200800313107501c0d000a40e80207030200b00d81807040509020712415030002c0f080014050b41503005000000c400480e4181c00349150196080c0e0409610341500d04850f030002c2c08036140d2a092504e00c0701994108214074007542400800c10800c91504041c0c032264102d6070850743f0300340c6114400c0c0c108204100030071a03042c100308020710110340c15900040c3d1209040c004c4500d03000c40c042022031241e008845280b055003202c5024044141c1c4180b48944090551008010301a501e100c41d50072640a44500351a200240301c031444001c2864400d10300508008204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206803426 1250 206802176 206802199
    0x170a0c08030c0d0516060509010906050117100905071701091505041a0f010902160c060512070806030303070c060b0a06110d2c0a0e01060203041703181c02 68
    0x60075074035000000411414090800e100004030311a07020380700c0e107844444100001010b60303103510008100182c81040c40d9501c4848000100c0d420b405205e0081c1403000d40440d039103000743d081c0350802c2800051a80d4203804e01d284600800e80001d1200c0654681d401c101c0595588098800e0040c01c140d00d006009603030008503c20a60f200ea4041d9125600502d039480c828031141448140035801158443c3d4848038900040c40460a01e43c0940f040450000c0c0d41206050f0729140c000b20103a29170320031400141d0026040030040400746029410072014101880c240c1000800a912804010315020400030302c1c01c4010284180c035001502c02e0b80c0040c160040a680311800108101c84081f10780b134451180410a440b060300c2601181040f10b030071080d00602740c2c08120b00d000900382c00700c0c01560000c454040803420a0300a0030890081c03220350000d40d40c0301e25140045246e460b11240c02d000542052150000301e4825014000c0241412034041040c5241c88018204903c0d8042011790050003040310b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206804676 1250 206803426 206803439
    0x221506060e030109050d030c18030f02030c0604030f08130e0a0b01020d02030c0619020705030a020c0301140705030403030522080706050a02040308041a040e040503120609010f170a0c 80
    0x10000596800e60303102109007004005060a842900d074008059038008090b41e003074907129a10800b80b02d5400c1ca001059545224203000605070350340c04c25202407600c40700340c20031450104600140c44005039035280c00c16107140c484811702680c85102400b1820001141c1a00c012007410180180c40ca40f41d84610a052450080f0020f004550210307000d841003a65460300140004241c9030110315040040101340d580d0b410310352141041300c4014030401d40a00c01e001c00180c052025003030011003903000700303442516102003500703603910281149403900c003031400e01c600194003034200c81e0b106400d0700f008140d68955401d203500c0c0c01c081c120807034043c104071180e0108000a440040070308501a00c0244040d484a08040040341b1451200810003101013000b00311030341c1d403d201c0000f080705145030030b81084e0b611400c64041c24011541180d058100045c500099440130001e180c07c02401d940c5048070358100b6540d5000012076029101c81003840b04a10a0103050400c40c000d4216801a04510019940c03030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206805926 1250 206804676 206804681
    0x3261312121e05070503070c06121103040f06020928091104050901290f03012303100b0312070f0311120f09010c060603051e01142215 59
    0x1007150008120300c004403505208a080d0390000e02c0c0e0307110340c40c02c0100c1c490b025910340d40005421180760200380a44000300b81100a0745005080c6611002c211030000e01420007154003007100d2500014082c03003400302140c5484080114240d21003c01652403500000180e6418000c032001802c0410340c11090100300c8820344100221082c0b0749007030104800c3c644038002c10340110700400d03811034032b13031001005090140e5180004102c02000300c01050382820508a036280c1c0315461240842038004010010100c1d814041c0c000d2844180800c2c80f200d98580000c0e444040000c40600c00340d4030b03000e5024456074188000b01c0310840401c515640c0320f555140460452088000540220f0095500c1603a6403001040d40d61803007c00d401818a00346050380d000d070039500301c941c40c0350401c0601d07506c2c48001901846603c9c055401032004050380260164800000c6c007151010651350790601200c01c0281a2a01e00b040d0080310740e545110103082710a294141034030128802606205800e00281907075072195 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206807176 1250 206805926 206805959
    0xe060702060c061005100203070f02090c130603050103031b0b07032c0105060f030a1502070312020a020a0507050a14040c0203072015030108031801020708070e060906010801032613 79
    0x1606d0103501186010400e0740c50340144003016141c2540300e0b60785d000600d80210290f6008a03481101400c1030640040b218584041d50488000710341c0e203000500616802981a242084440c13410348500b0340c0907510103143d0354000d4040c90a02d503c4007038403104038849500744403c500008141231440c0ea07041d06a14060001942c41c00c0c02115600091079107400e0200702e002180d501318907804c40c18085000050000d52019400341d0070414500b5044040d51640e000410301010305c5e80c028035001010782001828171050340d010741c0c400c89140758200120311121003007215110003200c3c00100c030b803c184001c2e0705510030403200500034400901d10010301000d50b003820780003d1050395180c1129503007a980d161070348403c0c003c554481d0301c04d0009091442c00030021400045041c4151503c85507078109141c900b0806030060951003d039841000314a040a0702c5540d4811000d00c0d094800e94903548a8292210400c00752480b0081c0c20401075007407581d41b000721508181604a4800b01715070302c000341981407520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206808426 1250 206807176 206807179
    0xa030c020909030301050d2009010303020a02131b0e0d020306180f010501121104060b0d061703180607030507150506040e010b1c0f05010906050708070c030e060702060c061005 77
    0x90115a100d14000240c0707041e218090000c1004102c01c2e11200c03023943c0140760465007000981101c0b143c1c1d840e4507020754001c51081c0c008100c520301c1841009109040400402c0c24146040300a902070b1b0715100408140f1180c80c10607918144d1007201088800ca00c0031006034161182505205007008a40850400c881c0000c06840f44219413113102ca003607820070700c6500581070101d841c4030041880890001100712000308006485075a401c0303120f040707800c90a030300ca01066076040100040b0300104c1495200080d51400b41d881c152600d1300d41010103d4080000d40101404101a02094080e8007141d50003600064003000c403a0f400232000014080072101d850041d820481d40c20ba25040500404034a202c009102c1100107001d9403882c0d080d200ca11000b80e4040c450306402d03002084081c82080c41003400f501d4007044510300490050180074010782600c0402a45000000201c0d5003d11800d100c1101200d209039101c2407400051030700d018550f940d00b080d018440501a82000c1022040100e030390 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206809676 1250 206808426 206808439
    0x6011509171513050f030309010f110a0809100207051b012102030601031103040b070801050a0608011a0403150c0206060415050904020114070b010e060d20060c0a030c02 74
    0x7294101400345010039401c001d2190301c0748500c0d0341002e03420040c1039400702040b1001102d00885894107450301416500201c910b410000502160140a00814024000c5404280842d1814031039040052240002d0300007040f1050022401d40501880014104000d00e0707015034a40c40c15007409500d600b403c201030510555503c42d604115400f07001d441c0d0034012103556000c20481740142d00c102950004200030304042d914010b040c86600144080d5002e14041e00c4518018504004090043c1e6010b070415445006031210030031800b07034002302e020f05407544001803402d02d0000780c1084002c2e0099420040040c4441800d401d9084800d512540d1010700030303802c4401a4803610305110480320003170307909800c100d1940004d0219050212003150040e01c10702d05585000c1500300302c2416904a83c2007221007000c1c24004100138181c0f11500c603002013040b43c102010015582c0c0d1080425040b8403042c40b4000e8800c500301d00b65441e002600c0442070b00728161545d4130094907004040703030005d0004900c10075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206810926 1250 206809676 206809679
    0x3170106030501061e020c0d0b0603010b06040509040f050a0b0a1a0a05010e091911280504061d0402030702030903120906070221030703200a0309050f030f06011509 72
    0x14440e001d414102d13161504c03802000e44201400c14054810040c2020541c410000480b120307803502081140c4060240303043d13000300d00b000d108250959103035010380c038804c54090009010540e5916409030b080f591004295100c0d00881c94103609100201d50041c0803211028100100d600a40e0400364048000810003101036000000300700041c1c1c0e19008060010300350a18a8800d030400c4940ca580090712030841508076107444201c40c054400152080d03030400004a42403802844403148070244025001190003948540c95009045018520541d020042640c2000507040810b10619198103c081c0c42503507245494038000c0d60340d52018001d90700034030030000c0c20420070101340261850808020701b5145442c80b07540811580d0f2215a0084007200000440c1d031150b81c008000801c0000e110b92201141e00286584103005070310300746910740c0d69420002d0901c0000f0742c004030a006444081343c03044c494440180102e0301d0444203040154451141c0000400d07079050350078110811042c1c6542d080b1005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206812176 1250 206810926 206810939
    0x80603010c030504080a0c060219050405030d02070e130201050909090f0c030c060a0e27070e041b03021c140f01170d080a0b0d1b080304030206030103020d030219031701 74
    0x8480484e4041e00d00741c1d0502980d070410f4451f01060315564000c0c00b003d810040c40b48441c0c401c4c0240c0d9211b03000422800a82003200d8101844001c0303415001c0e00192408600d852010090701030000c003000c10700c0490f0703500c01086a0040082d24038401002d014248940f170141d091558822000d2194400f51107081c0901c5680e180001302ea1042c1e4030080e00030303410700c03540722030584106084040803a404807004c503010b01001c021000024200170014001103031303810a8440038120683c2111024069420281c0301d0b80101c5121860241000a62600580d5181c901140b1040e105141c808140b44a00b02000490a04001c84500e405945000c14040450341da0f028100c28aa000ca0309014407500000100e904d07440c0180c11642d446039a00e24041140700c0e419002540c0040d49440454082004143c60700d26000c00d15124806041342070000c510303080c1141c0004180b400305200007031152445104503401c05100307120803404100c104200741020850352a0281200c15a00c04040910703444030000a00e070f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206813426 1250 206812176 206812181
    0x1f0b0406050f03090f0f0d090b040302060910030204090908030103050c091e070c0c030818030304050d0803061201090804170a02102303090f0f01050705090d060e010c080603010c03 79
    0x4480407500c6003441c110304110240580d40004040000301d02031828842210541131100c030440402c0b9401a181100f4060000341c50042c1c150018501158140010300040c1c239458112090000100d0b00e0b005070482c071410840180c41030360003003020507041c002c200e01001418000356058900c60b03001c0d914a00e0310007052246103442180e1815a00c0850400321804032030910206130854050300e002106181c8640710340084503c0e941c8104c42c0300200041071a1030901c41e403103594000000b10041c5140c1454240040d480a5440707001400201000006c07030643e560321803c486091881400902020000c1e0030440010b0700a445412140c240d46e8000e0102075101203005064103a00600310b01640d6803c11084600502c0c00e4105441400c0310074035060445070900c0614030a04841f00100040200030880700d007003840c14680717a4003680c144018090401c1e004015070308400c8007510841c00c2c1a00d14180000604070521010209501e040340001803503138400821846000194024041c810310640c00720304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206814676 1250 206813426 206813429
    0x15071a060a120501020405060a090608060306040b0a0e03270306100819020609040501030b090705010216090519020c0a021f020a02040b010c05240c030702100c171f0b04 74
    0x140540c1c000c40c140905140090708886281c0a64001401d081d21100030410580c0700d24106000304000440820006520001941d48040c003034001d88103500305955090854040035100a0a95456404e00d610a1404009440e006000d000c00805e89003001c0d41c9140c88036030072140741c81c007030700904002405903020402120106e40c0400b00070203190031003615210072881203090403039010004024990441e0390354000c007400395000f07510520240c280018054070f44511503201d6415034100c800b1901800720f400c02110101c0d46502008529a50307100c2c401d08000c0103440d0b41484403403001c113000c84c0d902c0c80000e103840c1d258801d031240c0301201842c0220545110b0103602181c01030340292408e100504140d008052026018100a204441c4c5980e0b20f50910300003421990440c244d0041d0035001700c2440c01141c1e04a51071480092840c00c0c0402d009440740386c824845400d00740c40d865170f404c140d88180d204101a070340303084820040341803c039004484044100e003003000c061561500850042903107401c440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206815926 1250 206814676 206814679
    0x80d05090d0c120606080d020f06130c080a080d05060a181a0a06110c0405040507030f020d081804060f060e040f0b0d08070b070f140c0c15071a06 64
    0x342800e80090411084003004002156404001070001820700503144401101c2480b403280851440e040950b01b52402420007201021135100142c10480d218002c034505820070190040d811514881d414040f840a040364850030080c0700d82c1000c0c209020b40703100500380206060100748295159002084003e00e031070b0003126410342d0030039140143ca980950181c1610702c5900590042c816280300054100d0217030742c0c04100030980814404d4100003041c0a10b64071118110340401840c241a00c0c1e060f80c078882400014000301c403602c060811742d65503000c0040010361020135943c0c7d94001011040d620440c2c0d03106907009500b81500800d003002d0800d0760320141c98582c1e490203084900300717080001420740e560310403010903501d00c080c4a59464221143c14107074002c4818039610112458681e41850b0010216410816095906100c103035101c440c298410103548090341d142d2071024000d40c203207002c00082541c0311078a020038041c0c14101d00094960704e80a50007003035138405020340941c1411030844089 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206817176 1250 206815926 206815937
    0x103050d0503011a0c120c070e011e03020607060b040204060e0f0102070305060a020d0917040f0e0f16170403080604060b09100507080c010501090911030c0114182206080d 75
    0x7840c0b0b00484c00c00780c031800040d0000c449445e18110304507990740d403140c0c00300c1015403c43c800030320981221082e818010310b400b0b03040c44442d000d60060030484a8082c04001e100e00000034024082c4151504074600a4400400442d5215902c02002d460240da01807194000d0201550f2030b0781960000c80c4072000c480d0440041c21300b60341d80d103418000940c41440707104003441d070300c030007101c0450386034024500d125103200380c039540d141c0c10312944d45402d2040794848181d0281032003c010184400d4280746400404000702d10982c05160a01a00c06205000001002d07682d030000b00828542d00c0504180911025a01000410b889054000380c41c49283c040c00d030048003001031064168428001001e50038020b810060401115000507429a1030070382c0404140c0751112b2044050180100e040f80ca002c5003180204525000314002a00a0340904040000341902064094050040003440f502c402e13030090201118845441c0a0020f42488100242560b403a00501040001002542200e440d000791240f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206818426 1250 206817176 206817209
    0x6040b090d1e021e010e010506030a1115090301020a0e1003020a020a3c03021506100309060b12010e06060a080a15110403050d020c0307140d0f080708030103050d050301 74
    0x2c81040030001040502180b04880400d1a15401c10102012010a0400110301041d074030816600f541c0024040314031035000440d58000040100351518048030301515451410b0103140b03212240b034045e80a9082e015400043c80041c45a844250307407070112412107584182c3c22032110110105c0c000d9010910142c0d104000800114000308100041c81e001c0c03c540c0b126415055600030041e203450402c10a030611522401403c240e01400300c509072603540400c0d64001e181c100001003c41c0c020421484c01d05a4480d00d840601c00d4035004041300d0b16010781450303d03091034500010300a0160b03c25a10741c1380071304000f00d00b035481c3c80540002250016001442540d240740c03901388500c4401e60303107008802d40e03500502909460b00405440194095005421104070220b40642880d02601c0241d1280d00518401d001302c0c2c0c3c120264000181007511648500b51061510508602404c5006001e103040815614104080ca0f130085060381d1081c02914515843e0480075504d9010078040c3c08000b00d03440d000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206819676 1250 206818426 206818457
    0x6060906180b0d050f06040c0603020f0406080603010e030f04030c0e060906060f090301050403050702030d0305010609090b010219060914010c020c06210a0516050408030403080f1b06040b090d 84
    0x100e5407020800408105428650340c0d01c4d10300e01000054100740c50b8000c0740c100014496600e20040052540c0d0400358a0440031180016451041d80a03800a000c20040442c5080d01c003503100103200100030782129234411039010301a055400500c401c60304000000d002040740e440e40096070303028540c064070410725034451800700000758110740003078a40b850042c070180c2e11030342d0240035040c011402521b0f15503403070b4884e005050800e40c840101c40285400d00c1d004010356544012030100300c404100c400070380c9002e0000101d0034040b580d94840c443c0d12804aa80d41070107100e030710a1400c81e200e9291248851a4000345500342d0341c40d00d00c201c0141e0804840345040d401c1a400900da140c404050401d0107045504046400e50020340301c522659503124100310010306c803480c1d110180e10300e501b0118105840c02208658910803400018500040031692030b010800d54030503070711041840269542509440b030032a6030760b908111016208032644001003950300741c01203149040400076039502101540e0b181c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 206820926 1250 206819676 206819681
    0x20c130605092a07030921050604121112090102160303020d052109060405010506040b09131a041506060518040c09080f070509011706041502041a070606090618 70
    0x720f00018810448042001040b40001e003046071003611921021800c2025680b18001e103000820030307003000c0c07008040c0032030f400181c8554040d80c00101481d58510300c0104490103030303101440c554144126044070b0142c034401c00140c42c0c502000e80c00c450310040403032041a1019610b00c005005070700802041c62140340704d800105200f481a0207445c500d4061050300341e01e661011507070b400d125000b071014001000003e0052603048241200c0500204003102c00094541201400500003080070303810349020000c03001450000e15030650f50440343c5152a0074100f50808109110481080c5080c102082c072500990903202101441600c010010b803040d010b0000400e4006ea050040c81007030000000c61080400c54882e0724a00724020b04516440e01d01401910701c03042e00300c4400900c04c115074050602000602950058010740502c10032441e60403040300134816a00203030800030601d030a07551014030110003006d115200320001c003da1039854501d00111202030281703100341c411032800749620b9881c4d40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 206822176 1250 206820926 206820961
    0x30c0a08041b030308180303100e060d05010c1205090d0e1c02060f0408011107120f2109120305062206120f020a060509060909090f0d020c13060509 65
    0x10090310082d80c1c4451864180521190300403000600c61004001d012507499034201c403014121703070080d415030901440781e40103104140100d0100245110004005540e0b04c1601000c00703404c0380c001c2056407041d54000300303000607880607001003d0804002c180c0803c400200c0883c003030f500b81e45604a1003280c60401c640082c05441c150303000d500400d40390003d40d4500c03008141b542d80700d070400ca56681c034010006095400d25a01c400d1710074030a11401000c908807805035070f10b240082c0341c0040312500182043e201c510106002541d43c1e5455031100d107c004141d842000780c6401040c5d0f103039050550200071019120201e940582141c010104236a070201199540c942010107000c0c04555680c4078004400c0c91842c0380da007558110426400c03442503003030203ca06800b900b454034000d4901b130301404c0403818a2090b1034589004840040c006400c09209111303010010036908261800da0350b80d403000964884a0324001480b40b69140312006034031560f8854401200c00c09801c5030483c0c2d407201442991200391 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 206823426 1250 206822176 206822183
    0x9030909060d0501020d0f0507090803070b010306090c030803010603140a09020a061d0402030406020414030a08040302100e060a0f260a050703110d0524030307241a030f0102030c0a0804 81
    0x240807010701c007406da000c0c580c01001c68102c0000d075442e1080005280529581c80500c658004118840101d811694040d0540350420380108210306c0600d00703881c8041555202900900001c00042182681900020350409641760b6400b1591100c40d9800c088a0040a0003035200d08050710400c00940030f10400401003400307803039180e0038296480120b01030340c1c400c8030201c031041d90000301400040c1000da0741180b03c0800b0340003440b03c03007080d40e02e00c04144181d000182c81070018a807120105c9110382d103040c8003008050300312070715448552070160481d0181c40421005c2440100130f41c451b610b0180c42c0c4405241b40c130a460880b5200c1548200c000c00c4050201d004041d22039007181c801c9031150000f0003074580111000141441d0403032100d11040e00403420340c001074110840c00001550000250356040b0340044003e061078024104248040c10f070004083d2469090030307200300349540f102c0e002408404055043c6e94400c3c014042c554202c0c03200701e903890f040800038050303003a4071803007802a658014070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 206824676 1250 206823426 206823431
    0x108070e1c080301050a0801140c09150406050306090610020a0609020411030115030e01050610260a02070b010801050c12040c03050709060501020c1203040b0a0509121509030909060d0501 82
    0x80d00204000c5410001c03100382c40000340000104600c2c14100c042d100100400d0b0004c1081a03000107a082c0745804c050844a246800855660290354031450052a90b008003104d2998560b40d808029066400480c1d9035881154004001091810203000807914101c66602030314010655990b10b2008003038106091384c02a6856002c201d04010103801503002e005007056051260f64100001415034000140301c1a03540d0400e41403002035110071010440c040c1e0541400780b55918481d18090301e40c030580c40400706d4503c3c1c0700b05011079540103038000c120b4140104840c070010303a00ca202c070038240c640c20340e07008002075010400000e271406050412a0824071850324031502070707500d4603801d142800f01c1d0400c0446139a1488100b2043d82c040001c021854410783d0007949103100521071a88074041d0b40709500800f040060030518561082080306d254190061140c20016102102c1d5a43c0394105009050140d00c0d56000c80c403452800010741d003041c0c0000f04a080c05680361001d11030109407004e400c603615034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 206825926 1250 206824676 206824699
    0x31b190906031112160302150919080c060301030c0302040b0105070f05010c17060112020a020705040212090601050108040b010b07032c030c1e0f0312070c06030501050f0108070e 78
    0x201030044000540c090000400c0100c1c2080030444413440781060b0100c00d0303010001a40c003150700c960b903003000c50345c04030340d407901000311030b2180a03041c801d41050590088120300c4500d0311503d20034a0f201500c1c2420101c403845510f41c0140122031000b80030107007600c2c80100c03080006182c542c019000012040c58200c1c1800319503910000d00c4012000126016515010b043c40110f503c50301188280f80c450b040d040c51410b01c01c0001e82440888040500440c0d000100e04c580c2078003c0101200400029104542c1c800010782040f4100c0d10075144001c040c0a000000180fa44c40748010300d0249401401904550346490034142c0b00d0381c0241e8040b0207020950003a2442c203c0801041c0c0f401c4400d03e40307100030350444a4101400c040b82100c031180b2070100c642c582da030194020381000c51072034010358681d0303001454100040c0c50400214540c000b440c10010315041001540d00005c01214090b85040c01180d0702c880400c921100d072a907035a0300080710b1000060351a445451058544a030280004a220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 206827176 1250 206825926 206825939
    0x1706190b0a0924061205130308061e13140603010b03120a020109020a08030c0105060103021606150305030307020d0806010903020d020405040303060302040e1f05160f030e030d0501090b031b19 84
    0xf00d480f6440000401c84105000702520124090b69034080c0100141c4c82400d90541d0300030702280d030080e181c0ca010f1020f5008401c00b000810407152008800281000020507400041c540517110404107080c0c441c0800012487c1070030140076140450074014007409400725803002a50301030b042a0901000c640d02c0d103485c200580c840e003203038001421841d0f000c2c5503550300d041c044500f5248040e26107810948108022812901003100c0c8106440c1c3c411000b04e0288198a00464225003c4c3c0000d44203000000602060756000100c0820b054210b131031300e20721640d40c1d8006488a80f058070010350400382094036200149020350017640c0c064482e0500160140c1c4a030082003c0300ca05c40b80305601e0741d0024210000343c8a0620310710004480e1078206000a03c0c019510741700300c211100d061070a200184240c1c51901740039030411a015044042204e032034161003002600608001c2c400ca071a83d91618181d540070342404100c0e46e0311a2501d81d040601d05c240300040c041002c8101c4525203400910000100d1070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 206828426 1250 206827176 206827241
    0x109030c2409030e03010b0307031104020912060a0b0a060f05070b07030914030c10051317070b040b011a130e060301091e060e2a04061706190b0a09 65
    0x2c80c0259680c0002d90344d040145400c583e41054103d101b40e1085500300002103422202d00c101900644015031034016072000719000100359984040030740500c030f00b003001600c0a6800407107074000458a01450641d03404054884485001461000500412078140454601408a40c0022241c80c0014000704251a034240b86610540c030030704950000540d4040d201d03000c0200b40d061594141080000d401c100661109500c0f000d80d0050100f204844040d14080303501056a0146800c05440c03200382c176080c500302c61a60000d00603180c9400307689040d04007030082c200540354000703103201e001509203040c141d420010460003000355626648a061401c00030300b024402003031041f03442e001d01c0c036800d0072407401c01c0a5490f8a03003041032980c404100c00f04c3e1003100712903140d82c1842800d03100a505100b440801c020349a43d82106031074001001e0358140009000174480c0c40340da0301e4529405131038440200401991103240743c0700e074484a40c402c1440f803030b20a07502c424940e00340a00040c6044403a581480030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 206829676 1250 206828426 206828441
    0x908010f0905010525052b050702011d03040e090106120c051305071b050c031006050a05011e21050411130b220f060803030109060b032e0801110a030e0109030c24 71
    0xc2e103540788c03014003481640900030301e0f80d40d100f185241c2d00c1400848001035a07070301641c4268284c3c4000c0d0340109040b19401c0d403000e4060f180d004003503034a4800a040c5958a04401d02c1000d0040e6225211409104c60b107104490080015580d094664400c0350000132600005440a0b01c2034050301c500d80c0302580d8208070305910945d0300d450104800e032800b410021003440c0c640c040f42c18031a00340210460903081c1c58481003181c82c1402d042c2c00803451320030542c1c00240b0303e45500c5003044c50a003c0c8400c1c0041c80c0c8030f0b05100390b012940c4840079144001d5140075a0180c0c4d54040d00081754158801d4619104049110382400e6000006a94001188003030144c85860b4070441d01508000018000b59846000b42d0b0041c00f0b072001440c1c5141042034440403032200740e40c0a1a4006d40001200000c0006803040b0307002040103000a005e80b0790214400013031944201802e01c0070030714004048a5180c4180a407002c0306070161a03c1c0060419a19420500c80070403011070a000c550280028002d54507126418 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 206830926 1250 206829676 206829757
    0x18060c030b040e070302010908150f0a0b0d030905190806070e0d0b0a05010609060807020303070c0f020a0609060e04060b160201020327090c1303120908010f090501052505 75
    0x4c240d155000140c1215810381040c066030b00409a44140f000190b14095005034419100309200d5480045003c000c0417407403076680d800601000f07107009040c3d1040c508003c0e40e07000c45912590f5000311101a0300b22003948103005264004d880020206805803000486408007c1c0540043c08003035030301d12044000c21506800525942c10050204603030201c111409001300341032120f51814441e0001e550703030000030308000c00c025611043c14100a44454480001a4040c02c06034045485010191201d86e413405030ba00019211121700c0300da460140103410846885100d26407400403003181c19810a1351007807059044d03120401c90314400741c10046144000c410383d80e05202c80d400309041080401d400c0601101007060003800503400d03045a00c848007084035800740c611514080f0800080c0d4400210b584068000d51030500031003a10f00982d000039a05501c0f0704020030490b81c1d0a06902e48444152415410a190003000e00101d540610010680c0e409004a00b81c03440f402e02481c1c0f00681210083e54 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 206832176 1250 206830926 206830933
    0x40905010f08010e0316020915090702010509010c0e010e090711070f2123011509050a0c080705040303050304080d02030a0c020715020c011d03010e030c0c010318060c030b040e 77
    0x401004000380b003205503400308131028510b4240f00104d03070309281c08032050191042150304041a4a0462a400204a0000985042032525011501074001c0100b03c82074a5030f54203100c0031035021071007409031815009050719040320302c00c050000d12211402c01440700301800811600c0c2c614070304c003c01c86c4400801250110392000740c206000f026039104000e2038021102c0031740c100c00000852070108130503402075190030364001515980405000d0300403588041d05590342402e01048490064020a2060410180c240701c16004000300b266003000440d80500052000d200c240006032148004540240c0a1400700342000300c42141017003264000e440c200d90041e61504ca50b80b1007074040c0001d034024044415651007000d0221f80203502d49500303c01c0141080b900104060803911601c480205841001d0300070004a84444401656680816585c4c1154824070095400300d62090042c0020340302c01460a044841c029a1400003a00102c6030f007505040d256a00f16041c0e8885200350f08283c19108003c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 206833426 1250 206832176 206832179
    0xd0509070b040305210405061b120c2103070e09040c0308040b0409050a0b0f04020f0d11030906010b0a090b07110301050c1312170c120f04060305010b0703120e03040905010f 76
    0x59003103178022492070b6000103030240810020340d0344a6054030450500c0ca01c1c51103801c200303042030a0402c0c3c2c41540901043d03c0c00304011000700c45c001001e40c0c010ba020b88040700e420400d0054448540022500c040c005034207000042c0103800c014007540e07003042c13045180c41c8000b5100d81d104000c980054000d81041c0310080350810841c50107000d1542c001004800c01c10090301207030041005d0307020001c0d00701d001e160006270440307020b512a03003291100c0d1f0f07509408204110b0103400311b09880e0300a6403c0700d80c901c9480c0c0082400b01102e070450b60300c01d1703441e1070b20014140751601100594001400a44242160140030310f01d948080c0190b07032080c0071114002d41c3e168001190f6500110803a00113204d000c00e451030b45400a500f17108408804d2102003c85619400041c004925003501340191804e003010100d06090f00c0d01210010b0400d50f80c1545040c040340c0c3e02d5000c4420700c1d020300c0300081c00164529000d00e039440f07041e601c0504c00490010a82c0d2800d03494040607020707030b9002c1e8084000c03034425010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 206834532 1106 206833426 206833453
    0x9060d020303130329062e0c060e070602060609180a0501050a05060103110a0f0e060a021e07060518130c080a051b0d0509070b040305 59
    0x84a90710703000070020f8140541c4070f2004a5811000c1c40e8591520040400b4100c5440c2180519a00300d590b00400c11440081c058000c035642c11400c2100480da520b0f500c403c11481c2c50b103450380c950300103007444e04100710750448100c015240c01000c0140051940840c24075004002100c03807400e25203a062468140400403c0c00c0219840303021403030300400c41c06410651040038030080c1001155070b0342c1d0041d030642e151201c1c00c02d900c5004020700d652607805404241c20040040c030348416603044403004540d01d03502441c0030340056402141044d406018072900e05035181c880102411409103020000780860281c18500c0000c0c10391066010b07106d851ba18050612034000100c10b1001484648000e4401c1000340d07a13410030b5504000000b0078507200b404080e1040e160940407241340858680c8800e0041c0005401c00c031141c09217043c0069101006c40103000654000c070090f1160041c00c0c01e = true := by decide +kernel

theorem cover : BRFrame.Cov 206654676 206834532 := by
  have h0 := BRFrame.cov_init 206654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 206654676 ≤ n) (h2 : n < 206834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
