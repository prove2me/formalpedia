-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:20:41.669101+00:00
-- url     : https://prove2.me/submissions/b0a64eb2-e467-4408-be4a-0d27286ce53e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 236690647 ≤ n < 236870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 236691897 1250 236690647 236690681
    0x801090f150605040614070c090e1c0801091a2103041802040515161410020706050103110919050c070605070905090a0b0906090703060f03140d0905031b0103 69
    0x1c6101940980208100c0c5c401c2d54480311161440f0580c3c22440c0701e641e500408020032800104500d0f2103d80102401c050018241d410007010006c40c603583d6580207022100003442800140841c908901c207461188615a0b95004180c40141c00318040c040c807662541c44200d0510945110103d003002100d018181000d1510020340e070f0b03501010040c0d0024058284101c0400c104004405c80403002d032020f000808001c2070310543d190b00c5080c4115043c40e014004c5006402d1501f003000120b00080041c41d00c076001c005aa50300d0360400c680c9134103415040728445e144400601030f14540600c0070003103103010101f001509448003030082c003040c80703410401000c0f141000200a504d6130400b2883c3c007150780aaa04099642c1c0d01068801202c014900c4664000c005402140c95802c0c1a090035921003030500f00010503a40740c07140c004111071242e204031101189400100712002013403066a081075514203005141504040010b925110450740070240e02d9210b541c1d00295a200381c11442d0040400c6900c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 236693147 1250 236691897 236691899
    0x60a02030301060f0c080d050703060506220846050105060109052d120601292a0114100302040e0d0e0d05030d0606050702011101050105010801090f15 66
    0x2a45a41091103a14040f500901d50080300a02550130714042a03442015a0300d04214010480001c1c440a4940001c0694031000425280c40d21401804161054541d4400c04045041e00701c50280c0590054040d0b60801e50710450034a440e0710500b15003d00d80400d1440fa07401540000410080300e0722414a82c01d40710000034180034066204031701490007a610b8075a426100e0051001040000b41c0d64945000342101f21040742065920318182c035400244418101c07000408020b28000e0207810403820b40304598070f440040041c291600d8030140c02c00c21203e040840b141d0348a01200d403201d2a4a05000d10354070103140382d5200303502c80060071801401c0310b581403e00859500c03c484d140d00089014a1601d000d19586040005903181141a41d80d1040000b03c40c00060040302c5200c14400c0b1410b100c140104d40c96010a030049001070700b034550344c140d195882400010100100703d0030600e16640340100500c0280d07440b104d143e0650302c0c00c010210304082100c2480b0010103160a90301860030080310 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 236694397 1250 236693147 236693167
    0x906020304060c0219020603160908011b0801060c020a0504050c090d0b070207081c0c1a0106120b0904030f030c181514040803090f131d0f0d02030909060d0206 70
    0x4071802c003c0d01d0f95401c607134071040d1403c040d00340b134410f051000c0c1d4415018400141601c00402803191034500529040081c9599180c0503825038044002e6000321518200e007038085254000f0045004048a28064061040f9a00491000c003602d014190265860381c00080d01c048540044915409011340504105000c07800c1401c0e1051094a0300c80c0107005d60000010401400074041c43e5144080c5002d030002d50708590141c40d070a01c040b030202e80036550140d00c0041e01c00451039090003440c203500c0707124640213400214030480e210140054443c111300340503c40400c1d48000e403260080c2150400044d490010402a180703e24031444007002c3c150308040c0404c000060108030429070340c050312074868007a440c0b5aa0240f07070066008514196005221820851034450008402403502521103e90300d00500c0101c4292083c112110450150b1440b082d200f4410030000d04034004c0c00075020301410081c2c072100030f407a8880d2440b014412011900442e940344e50300300c030300b90501d0760040c07400e07a45a400c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 236695647 1250 236694397 236694401
    0x150903030e0c06030a0507020a02190603060512060f190c050705010e0106062a0602280e061c11270906010c02060a020f030315040609020a0905060706090602030406 72
    0x14118002810080c4540e032140340041e100b502000c00030003190940d036034507a00300e000f040c000300000c046101d104119005038442c0050130441d0568410b0701e19881c0c1c00e0400150644110344d1049001d044c162144410202c000f0408035080603202200140c0d6850f124500007256800e03045c1103401c18a8107918a0340e43ea049401042c8062060009004090038011405d00300c0b00d01c1c1c070880000c0f03180300202c003c1c0c0e204200038482c00c0c101c41f21800c140d4001c85480b07810807a000403520003804501a10101c01040b040348000c80341c8003180c50865404240713140494018010014101c44909008101c150769158a810140c0360800780a00207444035541c610841d04103400840415120680d140346048904190a14a200d0041a15007841880d09a824081142e100c041000d04500801070101540c542c00c0c402940506042d401546060108034200001c81e8290784c4000f00e418410011035034000d40280801c0100d4000722000d545404080c00c000c000740607082c0b03006283c0c9100001b000100542c5d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 236696897 1250 236695647 236695661
    0x30106080a05120702180a1803170f040846170f15030a05060106020c12062205030d0203040609060b0618130e060a0203071b0c15050715 60
    0x21400c0b41c940b030420003d00040c1d846803903006900302c400e06d010b031410b684405000716044404030700c001400c1141104e0341c2c0c55500441100702c0000d040002200c0440c04103605003900102d6070b0048254a05203035649402900c1040d4204001c482c451700603c0c040b40f0345100e139003801c00006c142001d045044c2d610049210581c00310260101d15064074049403007074203124561251400c50030150054903158243da40f140d441903040782e410b12500701d801e00040d4040c01414003c00c1c003500245480c24001081201010410010b02d219900c10303030401c0380001404030700b8119141c0b000342908043e400341c10030310306510811426102d01400041070100b040b40c541d10098450380188d030b0412881429804000390791041118101410b0498402e030841d034a8910803041c9280201000001c074214000042414000304031001ea040c15404820002099004602c00c03a4090345001c4200071241c191f500d110684440303019650982141481100529020f0811a20404d4010751078651410031001c07888050401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 236698147 1250 236696897 236696903
    0x1817060115090303020a17070210090504050c0702090c0a090b0a0f03060e01030308041113060e2508070f05090a08030903070504230c040e04050724050f09040902030106080a 76
    0x4480e40c1407481ca40b10700e8074002540d6155015020a10654494405241c10509000c450390004c100c51801a44d1b540855084101e140d295036540b0352403c1c0c104411100018103c0c1401c0c43c003000504016500c040005601941001c00c03d900c8140109046810001c0c070740104606200000d451511171742c1100d00c44400444554003031114039203846083c2d0860358203101c01800706410704007003000200743c0a05026401c0001d0000c0b40c0151074021107400b581e040e580106036240390700081c000c200d0411070301d041d108848000065800056400000c19002c0024030801c20040e5006031034814a11580403035416410081100c0000f40d1964112912548541c20643c428482ca007000607560616019843e104030002d155605804000e49001070081c200600e0740805d0b4904000100307005104401c00c1c0c2c06140601c000307240c114100703d001c0c0c40c0302c100110f900320004021032240e03105c0c6502c1411200007214921019071540d003400003140c046d2199100c02981542841004078a4180c009840606a80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 236699397 1250 236698147 236698169
    0x12030403020f060108030a09050f0f040c12150b0703050c0102070f0b0a0e060f0c1b06042111060c0706090f030201020a030b0402090f0f130203100501080115080718170601 75
    0x199441c4070b15920f201f00c1c140d21020034525001000f040c9040d411102c0045005010036445c45000d000250803540c80301714a00c040784000040080c0d1068522440d141a00c100741810022030170002012028094082c0080c100100000e003c148032000b03405580480d03a00c484400c5070042145400b40701c5000890324040080d02d00a9003044810000440d140900b0540300007810940780c840044060380d100300e0740c0401c450005928844165802c1020503ca1805000040044c0c40c2c004406041c2a80850603c010020741c662200c4d800e042c04102c0b1508107000711401a41c07a002841d2a00141901d000f0142c011880c14000c0400e264040d00213145617155940c04104110410741000100d010b00300d2140d0300151031150344500750400010300540044010040c007000d04031803025005a07441102c501290182e80c07030b010030007540c000620340d0140c10041180b00446000d440003e10b0700c0c20040c961000c101014000c0601400c00d100710f07001030840408070090800090b10a103035070b1402803007042c010300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 236700647 1250 236699397 236699399
    0x6030b041101031505060c0109140307050d0908250306020711030d0914310917040608040b0709080a030c140613030e010509100c0507050a05150c12030403020f0601 72
    0x361091003a02042060b0b13910084d181390609061000a4020000c1140c4540d40e1351041c202003440b48080600c00d036514030003540d0310041440c2690030b0403403400c44002404902441030040090205030180c02c40e09074020f600c00c245804441100a21560340b015102c2c40c40001c102c0188103501c1850b042c1c0c0c2c5015811255441603900b0201c54207002da104007604d01d440400200c400c3c0c50b00c0d00300d001324003100d00c441c101e00044014040d91140520380507444950740e1b9420580030440251145504081d8688940c0e061524001020f04a410018001400c4d811000004ad030500e00440300403024010307071030846500344114034000d0407024080e50143d4510800000742c0381c15010008603148511181c596006200c1d400340d60030341d54110007c25850501c11700340030f480415210030300420304840b541c1e070310b0510700c80b00ca09003241013194940015014186004013030110351a86280d0115907410001001d42c0d5400300b200c114284a007043c0c42e100000d0300001030000781540000c1d0340843c1c8066400b41d9031030f6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 236701897 1250 236700647 236700649
    0x180b0f0a06020a080309010905010c050d1b0c030e030703050718050a020c1207030908030d020a1106042019030c150216050d1401111312050316021306030b0411 70
    0xa80c5807449a4001079211480c0e0000280c40b10010b10b0300840410f002007558000303561a0350a442603503800100003080400c044281d01c15074041c0320504242042c05044090030413000400c4079401c0403015040c01200c1050070f01c10b8a003082014011904070040d2101142c884800804601c46400030380d040c40d00b0080400c2000741c0740c0c8222035040a00c0d80c0105400120300000030f60b140c203c0901902400f0300c080000030301c180280002d2005807054640169a072006290140c02e000d0460700741c1003954002420000003035640c614125901c0c81c01c80806c441034403900d0000d911102004200030003414543c03800000c0009124004081c0c90403401480c04071101103104a0792000d0184880301230809400702003160382032070400c10101070300982803080c0c00100c002425080d51010b401d0386504a0300001c86040080c034859422001c0e020003401100442070300d8031160742e02c3c040c611484080d8020307400b560741196540c4007203c1c10f0000d039800a01c00d5513030300c1c00d244407100c0c011601070310300303400004840c0d00c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 236703147 1250 236701897 236701909
    0x140d321c030b0a0b0301080a03110f07030201030e01150b0c01051b040b07080903010c0815030304060203070b070903020d050102030103120804020d0b0a15080a140a03080115020304180b0f 82
    0x3418000c0c0c041992031820400440180c030800000c0c9800400d0710f040803d034840742100a50213804c9040c018042c0404a29008140c200b07102c0700713a00c0329001039108410503035000c5410300c120b07a024070307020179822285d001030b900411004000d00a26181940000741042001e00070340701c1510042d00030020f940da541010720f200f001d005410052020200001d02c0305201c400040e0034142c0c044c00d9200d0820000d000407c3c04c648001c84541d02296010080080c5143c0240016030789440940145040500e0280060758a0042140003003059541c2e100040b03806119507c0c0f8402150002c3c00038581d0310307171810441d001b94800c0c00705562071402504240501401020302c20700455001c6c18441002500d5100d8519031000602803001290f05c401a50b00030041c03035003006c0c2c0030700f9858003e08034001c210710f0000c03480e4242c6ea40c158903c1c0c00c0b240d11040070a4000d42c801d81120242040f00d0420f100f034001c02ca0071882103800907180b8400c041c03c52507a0039003542c0801c1034000140c88241040c0035120030085 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 236704397 1250 236703147 236703163
    0x12010506030303180331090e0d1b05060c040e070c030507141213080114040803010509130203031b0d1e03090804051c0302060f10140d32 60
    0x14050748200b000ca500c940d070a001090140084900b600c0c03c6c22540646019080b00c0410143d0b190350b2141072001c2c68109503a407001c0100b504200c00c000904081c0800c903103034407255a80406012080e001c0d400b0303001920005201a5074404160780ca907240c180e103003240542150060b0468410500300041d0001d00540c0c01014894164403401d0400c94243d0710b4130301142112040c204280030701c285060004001802524041c15102d4800076006d04002c009804c445141000752504c2c2c0f001428000899140002c036415a001600c000c04290b69201702c03007082d0034400341d000b5098800001c07100b4441c2007000c2220024410101070301c890600380030040b15480b00b8a105031400a40011903000298000d600c0700c254140700c0c00c480c40c20305a0b0382000940044600f0207a0401c1800749a079a410540c1c18000590310000304202c004d00d40c141005403296001d4580580c9031003a11000400c403031540d801c00da55200b958171100c1d203000c0c0a407001403900c200035032445005a80c0c007540071517002c090000c03504034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 236705647 1250 236704397 236704399
    0x210f0f03050a08130305120910060b18090f06060702010915020109060b060a0212130503070905010815010b0f0918160807020f0606090a1503030302090a05090f0a0c020f010905070512010506 83
    0x82c1440e07030100240c4401f42000d00000400e10540340300c8405010140200001000482c842d2600ca448159510b0348418a5000f068411140c034410040c4540c0180a40c60b000340040d610a5154a12840142d500d008250055810a0b00301c603030b40c59601d681500310221940c840c01080c40846492814402c1c07030700903800200003680000720400c840c0780c012805044901008a41d0a04407070b51100840d0505c1c1c526044481c45580702c400510a41c8003c00c40f6440c5c5043d00d0066881c3c41d894130403240290f0091312900b00400c030001134032450503640d00d600542d01d100c001c194103180b801c01000f02815803594141c18804a420b540004582e2400803550310410504d49001c1c0000d584c500c0100700b401d0724010888400075035201c130b03c6c2040c9003001c504640990300c240c034010b95a41180702049a5118540c0c0968452071804080141c0c140701555416000161110080782c1d94040001c242e0030180c4248401c0295840c20030759409104001482508840c016141076030a0500101010309075501181d581d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 236706897 1250 236705647 236705657
    0x803121902160632040b0601050c0a080d0f051f060e0d0201031e090b0714040b070807030306080f03120a021e07030504090f0209040e0601210f0f03050a081303 70
    0x100b808a080c079041444442107101c4400c04a806488039100041c0d545040213922551600400042110840c0c038580c004809007021400c040d00c4000466071564402002845044040b81c40744403400c05070040d450421000c9018440c524021004030b10110b43c0c545507074100b6041c1003002a490340102500c0700d085401402170032400b040e07500158060080c1c0c02c40c0c0f803c00002c0a4103603c01c05c500d0710850b50110700c148502013403410240c00040080001005e00d00000400704810800410340208a035806039106015075280c00c1d190070158000c009561001209000e54001740132106800b0ac020304120700005003402158440030400d904034021134039170002500060200003180c0c10620040c0601c24400d28041c0d2505403505056425108040350205e940c54012500340760902d040d0140800c85c41c000c40003801d480d890460003003807001110f54885000f0410070025010311056807203e0701070a80101002c1c0c60014240340082c2130b90300c040728081c00906044040b5000111107401c003190180c01d035444d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 236708147 1250 236706897 236706937
    0x1a0d08030115020c04140f0c090102150c0c070306020a090905040c120f1e0b010501030c08060f060f0f030402120f15070e030a050f0f010c1d0402040803121902 70
    0x21102d280c0c1d801039030100a511402d1903802040d40c603800f40c0040c105081a12141e070b07041002100c1245000a400c03403500309030510507a0100d90303000902e140480403070480035030703281c441d2a521803151080908008107400341d07000100500209030020f0012650694952010310303583d04c01300b000c50b5001d4038000d29400440d0810484880450502100740c0e00074403000c1ca0408007940c400e00300320002e9840b001c1341500080c95000b4000fa4540316401800b081c2003d00488245810040100c90000c0c031540c4111440c0c0f03081c81640c0c4482c0c1c291040e100c02800040c0c2d031540150b4400041c2d41045a08911840100d04d0500225a01050800c551a00c0c0700041035660083c0d00c400c50b1440740207040300c041182c180c1003504d40380e6003001f014020300e001d54040d180c0f19004a40705401c0c6036500e80c02c410079030304100301002340c10703403000016007699020950211201100300005010348500ea100c1c00107031001244544c1c8110746400b4440c082c1c0540c401521440c0341651040060b80221030600900204c9464 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 236709397 1250 236708147 236708159
    0x10080304030f02190e0103050d030908090907122a030e030304060c030b040501090e010c030608190212121b0d0503010b130509070c0519020303070f110409061a0d080301 74
    0x1c41c811582c0c4018110304101152840519a84c00c1d50362050020850300d000400c103001d000d109003000d2001519080c8444c4002e0b0710341801610441a84030b010340d14160020302811f1040c40c2510b2a503d07020028405102c491450300060140158004880c8a03029280200c490181c80340c034090482c0240990b0541e6590b03242c520052000030b446038241070302c81203020703966551442168042d00c1c40310702c0043c0d0013090032501d5003152075400c003600601d49001e4052284450004a091112081454030707007a550322480844d02828104203510310910581084510b02c0a00002810400c41c0d8200e2101c1d941400e030415a81e90b8001c02000008a0006c200600030064500c0040030f00402241c5d401c80116500d40110f08082d10480fa03100004060b000c15004104050110070031001008000510303549007a00000d8032445881002003c00c9030f9002c1c03600822001410181440700020b000f002071024604101020b0800035400c0c104045003005540c00714604052007600080c2c2001c030413130850f82401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 236710647 1250 236709397 236709413
    0x708010e1b0a0903050d03050903092412090610060e010305040201021c180e0906060904050a17030f0f07120b04090c1806060903030203030703051e130b1008030403 72
    0x50301c07207100118201115185240e41000620000b03015a0f100301065265052060030103000640f43e404050900c0c0500508840000644007100e10403105034030203880c460a0300b81d09c00305c84010341c40000004a000c459001c5480380c114400c0e11030340e050311015680c45800d1140c11f0442e02440000c104500b0311174055502c40d42c0040e40c0107106004a5407480f48a440f0300b195042c1403440b520014048106640406000320030310001032502601e104458144410070030340720a0300030310282c0180d002070009130600c4810440c1040054104184c50840a580f18520794aa8400c407841070349a00e840700440c802d4190300c068a4403854255945108940728070b4441c5028100300c40000ea803180c0c540c40c4032000f180100003200d0081001581c1d0000682d000c003e101d0a98a50f80e01130b90920008240803c0401d4000c02101d9000d0a18600007a1990312803c440b1407180e0707071107001c4081144401c200718090241c0c140b003d0310180942135000165840700e448140b014130764018078a0070307002800101300146c601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 236711897 1250 236710647 236710651
    0x9050601090e1e10080a0b09010c020708060a051e010806071701050d02120102210103020f010503270109082703061029070c0e0f100e0a0e060c0a030b090708010e 71
    0x34000c501505e036584640380c50318803440001e65801c40d542d01841440d5100b4407504124035414000f80c440185050034a0b038556900500802840792154005815084052042d800904202e25a00036550b11606000d64903081201c842c00824811407a8143c48413a4940450480308001d000301c01e9006580e080c0003c114014108003a199001e20920017003122a069421401210410407400e940c074500400c10080301200600b41130140810602c81d010408003840700446041c81130b8054100c0d071401449005210b40c90029080c030802251700b8126955400c5020008641d1503842c40c0408415000c01d80caa800a40d010703022500410b108000d45200c01c401c40b0307012a0200d001042906e41d5a41005641c0d120510445540602c04014040c030202600e0480d00550b070a80301e5050340c5040d000140941c0e2460040340c080b0000c0e100040c4c905442d40c0c010030a00c0351018151042da0500c1c114214440e0444000c05000c68249400e02440f4180003100a00c100e02a0b55403211a0b403810403c02c900c0350740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 236713147 1250 236711897 236711911
    0x190804030807030e0907030b1305010602060106080c070605010905060108160e1201060306230a060b07080705010216030305011818060203040f0f1a0901090309061d0a09050601090e1e 80
    0x13100a004625036546a0340034402c0e0b10a0301e000c591201210100700301c003c1004480c40c2c0345440c02005010381580011140e05640325400c0c104441e0b240d182243c507042c001c840000b07080505020000c15541c10940009000b403a00f81c81c0c0c1062901c8010105048180b02250700c000500c00c07526202c8146092510802003045001c00020f0700c0fa00e9403503000c10f845c14200454140c0a105071005440d80100c15184e0344502d04400070000981002060784480c81441c0026145280129030070b0144207003941201c03842c1d540c8920290b04080783e0325015015040920401d250503407000d00c1d0740b0000c60350b4000c0b0001e500052800030306000b47ca541c0e910094001501c19110010707804120f80003e128514004130060082c00c031404140b002d506465503640004044d5602a4101801070000a420034410000d80d03410f4100b0355088107404180e020180c002c00c076640d51181e041c0d20300080380e48059020740c1c0600e80030707a80d035500d2a4417096292501d03101611440161039038940010000004549002d1b08192 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 236714397 1250 236713147 236713157
    0x30604200306090309092215110309070602010b010c05060109020d0b03030d15060306050d060906020d0f0608010e150c0304170a0203030a1419020c03040f030c060219080403080703 79
    0x30560003007807820300c0c00c03620b8841580c00021118490b190510009500100c1c0760188400c142006c20b1a501c42d500510006104000c0044a0072098030550001014125000e200546901e000450301d50703200524811340c00594078004882c1c05951081050f24003030340e0044021710f410f07403900502100961083d044140d2550b69000d0041d0f00741c2e000e00081c416043c144001054a60b4450403040d0701780e4031903014000303261030800b0410039034807035170445482c0300e40280d00020484070302c0c2461006441400340e184010741c40c04141400d40780709503211a0070b032220003008100b908100103100daa541c01500d840079003440c030b07000000c41c101460002194070900c02ca1030091103000460410b0305c4d541000c181800503070404070030030004a1592050549114020140300221b007404c0c4202c1006042d03007840301c1a09500005c002c100c690081045a0007090020050b440c0c05550341408000070000e40500d42c010300801c00708840c1844182c040d2103906803c500400c2c649459030307490b22650b070720422080301401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 236715647 1250 236714397 236714453
    0x71d0d17030c0706060905040b190603060c020706110d210b03120d0e0d050d150b030f0115050306030c01030b032506020f12091c05010e011505030c030604 68
    0x394400059400b441c084039040741c59000b5071900009441d52504401c01031841e280410001c80c0810700c0841e00f04102804454002050903074400242c0300d42e810240445040807092000b50350f00089100c200c1d0f50a9998001d041249661241c90b00201c2021030005403074620030100c8a100c1080481c003c00120070000f604d2110307280406e0410341d000d10310046002e80800c103420801d2090045d414031110040141c8500b0444440142c4203000e90044503c20541e07600089440c0ca20600480001c0c000344590700e0f459141011071030705840c0d001d0240085070802ca0106901450094066a000e840c004001d844021300010044000703010480c1c5103545481250341403c03e40c030242b010144010000c001c1080c85a0401070040d20305001740e202c220450380543c0c074101411001006480c0444000c03691003001042d800a12040e585403154064143d500c1c099280c07008010541c4480551250ba0308000461359603034041540f564001060035425800181c0003070002410300c0ba0400c042818188060300e04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 236716897 1250 236715647 236715683
    0xf0617060a1a041703040311010c1a060d060501150221040501030207110402070507140109030c05040e0a05030c1c0903080307140f0a020601030b060a0b0d180f1208071d0d 75
    0x80c00c2003482c5213040e6040000d042c002d12401d0a901c140181081c2040100304c1080ea0703440110000c02400d91042d601508007040d002e0781c41c1002c1c0340b21160460020301030f03940c440100d0420f482c2c45032500405841103040502042020156031075007100920300d1f040c1010703c0c0000540c0a540014400c492540181d544200c0d25512440900103040c0034000801c4598103054004d00320724040d075109070500544903020000181c4480e0643d003610001d540119400700c245203001e10b42031080100415078000070400c42e20200001400c01d414a9000b140c000040388006d0f002d445540c41c41c04081d008000410024400e1802003011044620b1a840c0309850121400321307548490300030b008010300607000b0700010814013610800321074108400720313403150041c0e16010407003103148543c80828000c1d580310f64003184c2072007070b0012000220781c000c4c06101d4200c3d214900344801c140706130015804664144007248920b8403591b05030b80148844220341c008420400b0400c4980c405220f8110341d07041500d4484021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 236718147 1250 236716897 236716919
    0x2010c060504080a0206090102040f0308071707140705040203070c0b040f080313060605030115060c030912080d0509010504120e030c0a08030306010908150408031f0f0617060a1a04 79
    0x1c10b40c022056180c8036000e4210003400d2140141900c0950fa00500c800d2050900c04525201100d80c0408031940d101e42c5460545030b0340d0347c040b5048020b464042140000d00805196844012484800360b951603600e41e0308110803400140d42030310000310300c0440400010707040c0007410740050050880310003904c07031661454a40c1c2c1c022200b40d0072051301c110072075003000b440e4007030003015280c12802070042c81c95003941e000d00942d26110300c00070440c0c522681c1c0107050048288401070880740172299040d00250908200030f81c03201c9030340b1038120324100002e0810035041c810b9034040c980c840100145040b41581c116034010010700400c1c1d05000c0c6030010200c941d94200e206008002d040d010755101d1504000240205c2081e5102c1151038010003a003011100b014944958455404140d0a0300d0b600d410125607001c1d03030340703441303810f41380154080c08200018142070100c112080b03641e540d2100781900c1c010090312813080d034001c1c0e0401c807015402c1c045041c1d102a5010040807003207869007003640d10310898003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 236719397 1250 236718147 236718151
    0x20705100c020d180b0304080319020313020f010305060d061109031506010318030522030807050f16031518081201140a0e15031e1f0b0307030f02010c0605 68
    0x1c056400754243e00400c5803c000c0b4020302c8203540c40b1100c507480c0381c802003484922008200030301d1b28200100140411070394102c122000b407c2d14800b10348a141810080d030200e0801076041e44950110f00f0040d06a40c464000c2c0c501c07982001d4242a542d1400350b071904c000c0c10b80b0035012410340000f407014803c0d41e2801c01005000c00c85250325515503091020001d4100c56890102005210b214140fa40c00b00740c122044030440c0c182803a0783c80e045050a08101c07024015600002c22444c40003030302030706100c000980d258201980c4800e0328490800d0000e00051150180320050031440151066240c1407c1a402103e04050702904d82c0c94018081d5600d5105038011191180c804240d600180186070100100c108201c5040c3e5199100d942400178807040e2501c020540c80b405210b0b480d00e00c0f441c0e2028082102e00503400464407a07840a5455815240c0140740000301d81d07059000c80301c116807a40742c0507240e030924018000d84413003420354a440580d600310003001d0741401098448580003039054800c5038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236720647 1250 236719397 236719421
    0x190620090a0b0403021513050a0306021209030c0d0509190b0d1a0603150310060603060e0901020403020f0108071b0c050f01022a0109080d0503090715020d0302070510 73
    0x5a8a00340401049401005500040d980c640c0901c820310040e03d91032a04450a00c1d107228154030340720f4500000c80925042d802240e0010040c01001040241c981c02800f01e0003d480700344e8800e0340c0c8894029660b4000c0c400c041c40320340d20006105000c10301540061171411406041c200500c07000003800070504010354000048036800054001c41150750348940d100b000c40d80e0100c1c00f100c10000c40010000d001c003405498142c003d04054103050b580c02c200d440c0320501e101d14188903442d511038016000340f4092054650804da0200058070700750307041c4204c0d01a02d500514011002154500445882000034403007018007a91046c41c4072a690050980302c4214841e620b0f1482841c00d00042c0305040410410483c10340d40100d0301040130201500707600140002c0ca2030200401c051180c01202e0044946d4841c000c540509101c207001e842e031140007180300e5005c1a0840e0070481c2d90b1155030600b500c00040351801a0844008044440e201c1e030018442c50340a1070480e00700340501c0701c1020445e0484200c032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236721897 1250 236720647 236720711
    0xf020607080c0d1b180602150f0604021e0a0e060702060d050c0d0204091e05060d060c05090a0e0601080f04030801051009081605040e0109030c0204020a02190b1014031906 75
    0x4502c007509403405ca03a001d01800e2004e002c14594001002104140c013504800c044a058800583c16803078641c1920980a200c070914016488061114241980040d240b0301c0000c10010112019007041c40c101c5940e10313405000701c1c0c034019500500000405024043d020303546001c115004c40303940d07030340040d2000e040a80b4001840b0440301c20f050a0410401d240340e69010b0800d0200320b03641e0354000da404411034000101140c00020001708072414401e0b000c2c910303880700440901151000f00c2d03404262090500f0b888031111130300c401c0c1c8100e1480004076402000a11130f60014032090401e40880c1d5014509800c00965154460b45c1141c1042040d480c50a03903048042d104015600e000d00a5100228040c8001c1000078100e0f100100355040c48007010307025039000600c04240501c200995514040b88544200b0704c1901d80c0380240d400282600d0110400740b0348a40801c4144403000c1e15008928000e00501c41180b0024070f40c00c54071140340c01035941503514040d0b4055021208000c640c507030040010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236723147 1250 236721897 236721917
    0x603020d0c0806010c02010e030c06120105120102190e0117010e1b090a12020a050409030207031704150c0f081b100e0d0503041704150f020607080c0d1b 67
    0x24504541505500a0801c0b5001080c880180d801140c450000758088c0b070940c0003000740e440828540090444100d4100c18001010481110303900b502606984003204e16480c9030217000b078440d0a0b8003e003004511595481a140c1c2c80c21809040c0042240c0018103000080550010b200300e0024000da015640082000c020000b02407051000c6900180c0d4400105013407144000100e14422994002d003402c40201090310001e55803000142001044010030070720983c0303000c1c54002d4458086200443d0110382207031300c0d2003c504080c41070303505494902c0b00069100031855021a50799000d0101a51849402800280842d09060090100400c681103520190303105e0364a05140c200303c0b9040400442c0380070310040040101203915a5108070519060381c49884909000c03078402440ca080000c031000002e000a035110a2000c10307424010143ca529130031001c0181d09a88410f81110080d00003a41d0030b0001d0301b6800351401512510b242c1d14000136042d2850000d5502c3d003035051800c0c41c0400c1222075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236724397 1250 236723147 236723167
    0x17070e0c0c0606031f020d09020406030302010915020906092e18050301060f0b030907180c03050f151201020403021206060316080c011b0b130b070306060c0b0402041401060302 77
    0x400310f0340005041e001803002440808607100350b01800388040c64070707540000d115260078681c0d0300f00f10070044c2c005104100041e6030386000790081041c4401141c80c044840d030704014800d541d200f0380d8064040948402d141c08a9001041610f103043c11240030141850024407101c82c0409c08001101705880d202c4000a01030b0751815503a8900c1035011500c80c0c1c1c10078900303000e24910310b0f0781035084484801c0410788a454003143d03941040b030310341c01c80c940841c501c3c988512078021a4102800c05905074404022607201d00b03850440c4020b00b240e05808101d160780800c2d41c0c07401c1503c1d0500b1566100300005050a481c0d9000a140f118022071102041d84400c09100044c64144655100903900c00e00b47c044480c902412281ca03031400c0d140c01030601c0512004a4142c0c240315001c0040700307501600e0692035240c0004070704044811018107580c205241e4002981c1540030f0b200e441c05985041e00d95141e248000e40c0c401d0080000103004981040d1101c060701e441d80e02c8a80218040e00181d100984c680c2c40b00d030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236725647 1250 236724397 236724403
    0x9050a0216060b060415020102040f090c0c02010f0905030109050606031905060403080402010302040e0a0c200a110307030218040b0a150504020a0e03190c080304030c17070e0c0c 78
    0x180211464900c100194200300480d400c99400180e44004082543c440d06000184039000d9940302030140c643c1c074144880c01641c113500074000e032403150724209007290312150712404444c2028501000b2408051600002d5070003441050940f1420b840c111040f6038031100440d0a46103a4041114254400014402c030f41c070301840b02c1c00502810390100380980000740c0314943d554801500c0078042c400d0720008101964400d4049801619a01900b1f9020381820500e480042c8042d0030400d00060301164400c0500130700e1842201c40c0c0b0380e0803009241025441d29006001b8a10070016541482100000001070716900e501c4440c12144103d60300c2c1926207410072903000030f00140003c01e07035807421020050701016100d0303801c1a180d05070380c01620b410500074150381c50310364808403a80c10300c68064070f203100c20484925140d40c11301c1040070106a950712001942d890065010007007100c00c40d03001c02e003c000d4603003840462524241084403542c65441228648141099946040100c00080c010704108010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236726897 1250 236725647 236725651
    0x2030c040e07060c050109050607082a0a030209030312010801060f1703030708131a0a0606052508190e04060512100c0c2a1710050429010905 62
    0x555041c025582091074441c0c039140b25010369000e0200c402c3e00d01060000c05d41c00300306500d03400310413910281414040603100b01001c0718103108031103100c072200c401d81e0740f540341c40782000215010342030a2000410043d0b0280d00409150340c1c05103c03d105142c260b06c94140c1c3d8a00a0040030000074605d420010301c0d8a002d04141c0080c03d00b205800000d000038131001048951001d91403070034440ea51242240640f001107090702c05850100180321503c0c40352000c080040c00380050381c0007080100d50303d00082d00e8600500704c540d00b000801480481002c1100382d900c400c0385106800c1c2501c0d0281529035030b94a9202c10721103d0004403009070090701414030b40301e040003400f0101c1d00c8490007440c14a1165403103850b0307082c0c9200302d51101d91121000d8040d1300c00082e4030f544101e10350303404100103c82e030329030717407007009814402130442e840014045920b41184026499800003401d01c03280c06000a0000c0d100c050070488028410400035440c1810000600030007980350741c075100065140460101c291000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236728147 1250 236726897 236726899
    0x12030e030708090f04020c0105040b01090b0a0e22050d0503010518010506031321030509061003030c0303021c06030807142a030705150433120e011802030c 68
    0x200318540c08200b120054840c00b042c1111140640b10020021a01a000340c000740000e5600348024031041183c00b502c018161410901f04211200c801d2003042881d05840c410034441101c2400407640104010b5041e000c08000d1007803204000902e0780c1ca00c1d19228500b88800001000800140030b1807401c202c01e10b02540c170118110b50b55506110002e1010311010380001c2d840c0d0480319480c010015044080e0220070b41340212543c42d640103110160140501311100c02c0746001d4900020381c0c0e001c0c2a204801641d402d941da1501f8500e05650a60003540240448074038030030340d4020b00e040030307030b4900030320b40035510803807145840714802d160801c1d41c061034840d1840c454100702407200308001c7c1c0c11906409407013524000610500c5080c046402c140e00c1ea0444c4d604880c4506c0d408007a42c444100801c21120741041d1000b030300c1d000b89003000c24128098204040104049001c2d4560351080c4d004d03060b0108648070020341c10241c9007005084904000003450741c40440c41094096140a014441c00c00b10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236729397 1250 236728147 236728153
    0x3070e040506060a060e040906150f180e0705060f0d1b120b1f050c030d0b0a060309020609010c060b0d030f030c020319081b03010324020a1d120a12030e 67
    0x400c040e07000d07200c402e0107081c042c042c95450400100780100f5810488544900343c1c0001c2c041d03501c4805002201e112802950b40b10cc0102030141a0500244103454400041d80c01810702d860404080040036445071000d4102128144404680c0d00e5003880750f48444a070110440c452550b01820203408020380c2c03d142c0e8840c515181c010311080e12034000140825032080c000e00c21641e68488141c8083c007a000052143e0f01c00854100704090304c80e44035005100088a0103c01d003a80c9203001c07001d8400000009401030820302840240d54000c00c85440000d104031008180c4a0300c003004111042464401076002036a090840d4030034a4140c4900d854414492000e075240002c2c1501000070356445c440c8120400100c03200196810010b01c1e6030080d01044100b0361603503541c1d01c0c2814503208003038070701c08090b6050401220800a42c14401c80d0703181400f81d190324606042d68034145046a501c182c0003038001c480045483c043e9242070003820300003031040c00481d1002a484100030201c48e004030402000368 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236730647 1250 236729397 236729399
    0x10303110a020d030e040e03030c07020f19062102071505071107050d1b140102010501090204050f0907030e0f011a0901050901272d0b24070203070e040506060a 70
    0x41c40c0d404020f00c1168142c20030303800c500414404540100040250106107000100500140800203c0100010343c0211001031440040004005801801c0d041141ca0b0800c03080082085900500302c82c80e0f0300030310b160307445440080842ca80f001e80e448140112440d400c0b108090f04500d04511885800506514210b0500c901041d01181d0b941c883c0e004076031050313050030002d03002c209503170002c1d800a07800b0300c0c80f01070f5a83c0e07540340300481c1c1c055111045016500701800070803400c155109131421120010b00e500d41068084d400e0044810026200b4410941c0f90410480905820000060201001c0c0000034a0718006910b9015a940140d03109115219240040140755101c80c01c0d40c0c191003412403078100e10790045003001588a9074400e040140d0303003420700e00100034544942421000b40c44200f006078900d080010b24003240c10f140b01d0f00b548508581140700c09080510212a600700c03030b00106501d08070064000a01d03120981c1c0c46001c02031298020803003040814005a070304508241c98441840d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236731897 1250 236730647 236730649
    0x3050c0909010213060815100f030501090b0d080c010f0501170c0f030a0305180d0602070516061d0a0f0e04020a080102070c0e1e01060221120a2004060503010303110a02 74
    0xe44940320705c10801c881ca2001c070301d8651100b40c0002109600412544a0b03a22500c00078005160582020001c2843c2c503000042c52099805030000110b0002d01c1d440e10030007645c1e9040060742150700031490a66031106007030080b4082e841402d01a041d00d2001032100355081d1802407a014900a425000b00b40d1308031040c403680c0f80041c10018282d0306050150b2078051203002990941602c0300081da200b80e01840400610685500034040d49005a0a8607941d03050340c00184030803800d6205210018110391009024500350040f0011040002829140480e540d24500c1e503021140b50012042c91125405120031880c3c500455401080402d00940c04c00d4070720744803045404420320807009507001140000700e41888140040030a85001800b10b511540c4507403009607100045c02c070003a044944500b10a200300001016136181d040d80e82c410203400d80d81c516404010300807000c44181d000c0752814041d1a461403002c0508041c101c90307580c003600c2e0345c55801c1c01440314a802c1042d1300ba1307030040030448003d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236733147 1250 236731897 236731927
    0x41404020702030721060c0c0b0a1802060a03060515180d08160206070204141506070804031b032102070509090c01080415060603060f050102011e0b040b090103050c09090102 76
    0x1180c11040d09100103c01c00400902507616901c4006c115510b440c0b01ea0303c0b60b50300b080c410803071217000c0c041e008425074880448004540703100b00380183c2c0b0072020380e1000c01440c080b401081044441e140c0480c0060303a82c40071841c1d1620b440b0301c400501c50042112030f0f9400c1a00d11003900e4641c12540b4203642403081c0c0301c0610034400c80c01040c0d03800e0030110700b285c00c1d92a02012103090301d50280c0104814030401e000e01b40c41c0780003030b40d11190320002c0548410300b07841c03d18181c0c1e142c1500038152500c0d02c0c1c034640d00e100790800c004924140e02203080030008045201c150304c104e1906080c080d4040780d804c0d0001d009051010035040b40d445580c04d035060080c21700c000550056580c4080c00c0c0390f160f0b0307283c03418000001d40f15036084200c130a0502c80c000c19520760542282c0100c0d90500400300e8140d8603200160300742e030910407084010007040302050503070100a07002800c000d10b0207040081c08111140200d486090241c2058410707034450000c10480381400620b0590040000c0002c6003058803405500c18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236734397 1250 236733147 236733149
    0xe1e07081209010c14071802120a020a020c0112060b030f010e06240d060504021309050105090403022109030a0b0601180302010816090504090b04021207060c0f03050c01050109020414040207020307 86
    0xb0090030141003101d06120b081015201500e61840d4070044c002824030004040c0d40300032880c271840b6400001081c0340c4810340c001d0303558800042c3c002d0050300254400450f5011489070510a04d143c032580000361400c003600c0110b02400c01c282101e1410f604041480c000988068031490003000741601d81130b1249060381070341c000c0c60600301090b903848038070b1758118016017842d400465010b88001b41c114488422021680210ba009000c14012a079a404c00c1003c0b4140c121005800340c0c0000c182c0c0401c0c0388240701c038610805d40c854040390810304d48030b000c60720708100d441003202c80b1001d13801880710560b007058100316101c401600b42c1d030411f81564002062020007404414076488580c51844142d4060070030b4802800d0040c00c20800403d00f42000581a074007503405034042c421460311072502c00030115404050764025151685c0c1e0004c6541d5840e10700707071003090070740c20802c0a00c900f0094000a020315030003440100301c0984c0b00e23410850b1450b0140056010fa42c85988100703e540d0042c2c4012030420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236735647 1250 236734397 236734403
    0xd080c0409020d0e1605030d030b0d1407030f110a050904050d05030a0b120a17030417160803270307030801050f04020705030d0501140d05100e1e07081209010c 70
    0x25859010a0040c00040c254004c4030010a0050300510440070044400c0c0000301c0314114126100e43c02415000d030300311340ca030541443d0011140c01c07480010401402e1a000b01c40011421510722990340e40f50624051200f060807101048118440c54a624040896501a000072030b1106220700b030694550f59150318043d41070043c440c1c0072000078002d09681c1e00c005580c06000d03110081d2090408687c40c1c48220001d011039860002c1c04c4441d03909103070078007a00e105039404803400c1902412940740501a4004800191a980d00544204006074003180658040c046c2070780c041807000c0003280c462102191001d404000e5a20505c862004a43d000001c2411900d00765080481e05540c2c034003240103442112005415844002410000784031150301142c101d40c00c100180d80b402c048a0300700f1111400e0908003034460340c000709000b1000c81c2d4030703440700c1100c58036942145c0c02e4070003090041c0c0e0350100a42200d03145c1c1e00110001c00c1212410301450301c06607400345880d0300c9c004d00b03c000a044031032030700006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236736897 1250 236735647 236735651
    0x1a03030702090a0b060f03041502040b040e101a030411151209070b0304051b01020d080402041e050a0c03050f090a150f0f0207060b1f1202190c02030d080c0409 70
    0x8105800311644c40030b03400b1140903002039620401d1043c2006c50342d0054034212100e0381c031100050b51307064481c425542500c803440c0d405031602d85080c1d0000718001020b0040c0c20b018400007800a0108041d800181e01c800020031101e841e03140034100710301552240c10345103000d083c2c0c0d944e403e41200c542c0e008813409102e00d085200155119801e03400c2c9003100c03581182c05201c00c00002c1c0018010300184144c04480d0150340b40396040c2c500401240c6401518000b0408600381001180044c07505410500614481072001c1004141d4051200140c030404c2c0c1300780c60919550391100707449644c5409025488155050a030f090743c01d1403c09242d13601404180982948035040c00d02c044030640c0c0e00040d020918034101803016071000130f001c000961150300c0031540d1500d0442220814200a044c01441d080d40f07804100d0103500d200402d03919400003180c03e408495007000b0341914403070140751800c0c400440d070b0780c2c0c4488400e082c41803600d0910030f160400280002c00c420801c4001c6850308803802d83c1d07041000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236738147 1250 236736897 236736901
    0x90e0105060f04030609030c120c030c060b040f1508120c0706031d01090b0f0901090302060705030907030605040c0f051503060d0606121a0c090f0618060a080a1a0303070209 76
    0x15001c2c8a01441d0401032409040c080c510083c558400b29841c007890065086000c002c000c0c281c2999a204030036030050202d00040803480115085520013070301150007610114030058401c404c07100321080c80b4850a244080110305201d1110100310f5201c40320b528134002842c1c104050105555240c2511030f500815865070403900c1800300728000411180c034260024804403c861400d01c60344e000c1141d021280312000360001d2201e0300305009a0a416416030040e0200d601c40e10000c9940340d20003004404039110b03071100040003900030701c5654170650140781c2481000b424a000c000140415a001c54880c508072122400c00d100c0f40f1341140d4011100702c071640e800051526000c00031740503681c084507140b605460680c0600001d61042030940350820319403440c47d0f48180c440140760007001882d0750810040710510001e030030700100510420314001602020b82d8840070014516501428013000020990b20500901d819540940c0d0304615852120210300703020180840d5603030083e888041d01c94007076200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236739397 1250 236738147 236738167
    0x70309020a24030606091a03092d01050c030c0a0c0309050307030308090712120503060d021804050c0108090712050709020a050c010c0206010612022d0c0c030d08010e0403110a0606090c090e010506 86
    0x41031040312b00c43d001030480f0030301584200c0d0750030038402d06488440394200000903011520141c100c82c455032400c2505410b0404c202c0c0708440141d64030b1f10440501c40ba580020503540c2c0c042020074001c3d8881e980c1e91a0394500300c070707025003030890303039400842242c55080701307600042d462419004140380146810358580d603c400008070694640400a500214280d0b548256505540021841039020744111400400c040d00115264001122401ca5540060200b80540348102c407011009601801c1103030b003c02e03210840d0400b268080c2400e503002c1940003442c081040d9080c01428401d5145001501003503152040140400380c003070016084550740000da00c9210b0769502c040150341c4050280d001e0721400300051064403680700a5088155100e035481240c40c0340b80001304141108d8540ea6050b04613481e1440c1c1c1006000058002c40074448540d50812503100b08010110242e40522002309041d0300c0c100fa01012500c0b5a1a040e0410210380c405014011000340800d045031003c0d0b035461b0f50740c0036070b01c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236740647 1250 236739397 236739403
    0x1021b0a2706061220030c07150203010e16020d02030a1b0b091608010209030a03082a0d0606052802070b0d0203011715070309020a24030606091a0309 66
    0x656440c0354501d07250000c01c01c1c0351302500d150340b02d80382e00c0320410001842c0d01e2100c22103c03414141005480d82000020050a2048064001184540e80b200e4005008074800e0303085c1c7e00240c02c1001c0c811020410009650111321034144208040e001800450403a91130007905ea01c01e0380c00c12070602400641c800500b0444180c440b62460304040c000c0050705141c41c40584415007039002c80b603c6a0007590108805106200303c03103a00c14010001d000031001513505442030320004025404400c44900c0c14030350f00f200314440100a041c96001e1a40d2082400680782c01c0b103040d900100104402441210368104a00101507003511f80b030b0f00c00c000300614100e012403404c0300c10340041609402c0400c01030a1124290040c605840e00318501c5000e601d10362000702e9030340f061549404002101c101c081354002c0c0c0243c2c03040302464000b800c1500b4542c0c591603503a6902009090041b074150350b106440c207844ea407600c140d0014040500d0701812040c5030100034241a499806543e005c03000010206408220030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236741897 1250 236740647 236740709
    0x30c070b04230105010501080a1e05060d05160618030506040308062706040e01020c0a06020c0712030203030f01080d0207091113121502120103110a0302040e010b01021b0a 75
    0x38a40c401e00081051120b180603003000e2082c0c0340814003180c0404c514141ca17004442840c0c820048442c404e51a170f621034400f40c0700c06012250404500740c3d400d00452003d10101040f240800e41200d41035142010040a000b169541d254580ca40e03030905100182d00031620302d400607098070b011074241d2144000100c1034440c0701c0031660341440700e42030301d050104401c040501c5a44200da0801c03002c20406841d50a0303104100400d44a070700315881030b80005a81da4081c0042641403c05c544030070340c0b5001020b1498070498402d901681c0f0120811000e942c050104601610040d8090300d0f400805200c00703991000d03280180003481344c84145944260f107100082e200d01c5c1d030f40f184a95200980d41e803030421038a0010f55050380c0c0182e601292450480c110700842e0b0551543d4807203d04140e20b141c9900e00300d0804a1540d603800b402600001025036144c1c00780511303003810b5400000e900418140064a803150190040400c8440d9140b02401c40d03441424040441f64003c01e0720088000c2010f441c132030399140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236743147 1250 236741897 236741933
    0x12080313113604050d140c01050103030c140106050102030d0207440a0503010302011202070c030309170c0f010509011e09090b0f241201030506040204060b030c070b04 73
    0x6502c040148201d98001e103426200d01d448082440042140c52101400021207002e0700e190702408003245018420071450191a0f41c0c0346805080680245456094030340a038801c1d0005140180c0103003e100d5402410000c5443c40b4000704220b07407425001031f440f07020391644d558100c0c0c0c0c0030403008280b1002d0030300d04409101c469254120a00d59200c00240317450440550345640a100e514800207035484c40440d90740843c20384501b81180e10303543c011a174806d24903200c03040d0183c00b4440c000c0020810743d0328401442c0b00e034031541400c0d810480c0c3e00003401c01c40d070154181948020503030052505e0350000700200002c00e1a120795540341c0040169075001104d03402100c0c80c080d0b0300d900c41e00380d80d0043d100000c0e68010302c2c05121807498082001500380021a66941c00700012004041c0c4000b08900450301c0c10014240324180740344441c8014401000f40c0c0b01b5500c5401c500108011460705101e4400034001c805034140c113500b0081d54014030f90180e0100180051107010115051100f90140303c0440c0003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236744397 1250 236743147 236743159
    0x60a090c230c1e0d2307061b030b0301110901120f09021507030e0a030209070807032d0509030f030a0902030c090a09140706140904331208031311 64
    0xd000910b4050310070007078074010341c00341014000d80b082c428821740302c8440c0701c10791142c0341c02d0050760640c0c2035500851040b00d05a994490642c581000c08403980c0c2e03181850b03207001403100c8410b0189800e407841140140000d070000c02c44804c140ea0000500c000700702180000103102c46007000d030300000b01400c0101a5200c00c4800d60800d00701340000050011610a6031801c00d217180000c144034910800b40002076000981000180c3c0c001d101d001d007590301c20480e24000c41c10102180860a180c031900541541c1400860f680d24050400f0380525604090700c0002145040d280c00e0030fa43c00c0340400341401c2c00d0359480d01403031819584c0810142c0780c24500281840803606002e007001c002003e80034011140d03404440303a029140d00010420070201d5000303440b2050342c0c9403a0f0889607190b0303004850107944199103d11442c1581d54a050381500d010a40310100141070040950707903410301b2168041584564040003000004110400340d80e08485800410b45142000b89411b0020044030848250085 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236745647 1250 236744397 236744413
    0x7230d0b0c040303030612020105040b0304110a12020102070b0301150f0e270901110d09061103040506090f0a021521250329010203070c0e060a090c230c 67
    0x400703031100800c11640300351400c0003440d913030313020005090b401c407a0082e001c02c0042c00104400312000c0021345e071144c03150007000800600c80c8001b030360b1150a038000d07140716200c184000045580421090015240785403040b4219031600000810020700c1c43d8842e4200000207038034031841e078028030340c20107040f00042c00e9418101d5010700e030806180c850300310300c0e43c0303e0308000100300d031244113101c1d942c0c1060306143c40b2071404240b501000041c04030044100c0d4460b81d0340811664901041d8065401148140054921424486050f504e0002c000800c860b40d604440744100050340d800756a0950040302c088215109d00300f03000c0d11001d41d2403264142c0072418402c1304014000c2030900200084503950300c0061a0005030401c00c504481d1a44d0390209034041209072a05184e00d0304541071f1050b201441200e103846455901c0702c200c94926800795140c502c0d480b082c0132040c84c0101d001e4010300301e400c0080250b4251288024044c60030341d003c0355280d01c2d50f00490405104804201c800b54610702048034220 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236746897 1250 236745647 236745661
    0x1506090a0b2a010507030c0518040b0a0512060717010810050406060e041407090b13051b0a02010c08070804051e16030f060c050723010f0f0c020c0307230d0b 69
    0x680411120500003d16080302126031fa802358007660900703007124401040c0b01c1c142c1410300004081c03000c1e03110303030050024400140650b2030011700c83c208182c0f00b0240000e803c1c1100c0c007401c000200c103c0d814040c0e20b0b02d801407000d0702c00045c0e007588958031110082000c0c1c440e03051540040030b4503001500541e0314401013200340300f80090000c51700f230b80c0741f03040310071182c2e8072019201220162480035138842110084c420402c1c800380c220942044203a89414000102d038000700706541e00044100c03015035110014401010780110b12554049614241041d00d89007903130703900740c90fa03d0755140d0121100410b042c0c0b45808008100a4900c004400f04101e0741540381c3c20040000801060b00305c508604084803050034900c02d41c1520b00d01c03980001540b8175080c0500d400346035512007a480950710340d40c41140000d0340d80da90103400841d410b001000140016944002820445409000350103544003117810414010b500e0540d07035648021030010f29030203c0000c0000c10860100e140900300841b84403d06c494 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236748147 1250 236746897 236746901
    0x906060d080333030d030b0a050f120d1e0813150b0a090f0b031204031205130e06040c0f0f0c1104020c070611120f070602090d06051506090a0b2a01 65
    0x4070000842c100d170701e030031340090040f02078881c013448498101d034490b88204558209010400d0079004000c2410140a6141d8422440d00140340e180b100040d008a0754081c200418100c80214650503103050585c61070620031000380010090350081403444501381c031500d0003500d80c0c842c01a1407401414009002c1d91800300030003a00041139060500c07840d009002940703140004098a641d140d0300300d101d05103882d640b41c0780c00c05c012a442e031205004041061056041c41092004040c004032200e9014a080c204280300451340f00014180031700c80c41c6000103c4c4903400c00c6414202c10301034605804a102c0501d03000100c0103050103055001070011a0686c21000d021940300240c821540c2c842da180f40d11986074958445006019007410710040100f24046d0f060200213080560080030301620301010780c03011032404410f015043c1c1d28155100c2c18002c0441c4076942241c40b1540440392941001c20440015402529512840c0c0301c80b02d0005440c5c0c103071030a6150f10f050105e002d92081040150705000d10340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236749397 1250 236748147 236748241
    0x31503011406010e0a050f10140703020307140a150510030524072102030c04120614181f090b0114010e0105180909070f0303030209090906060d0803 65
    0x1003c284161380f84145802c043c110071007140c200600032500014001d05000c000010403401c14108081c0d80c4c07010f4214100040100b801c030344694000c5a41c0c0d00c0750300702105a03841044013001c1c203400000e5480d002c0307040b081c4008202004080001429202e01e000481c81014a80c4000c005000e9002c04150a100e004003d014842c0720740c0000e007180e40e440c00d0454010056508003c10950101c45131a1170503855409554442d150b034440619283e1030311798035440b185030351604586141c0c03a01d02c00481e001d8103014581e005a20038510080c41000b0034031494640030300d01010303090341c040341c0036040700728602e90002c0708460b07003014224001d544c40e00c017815050b050300314000b40031461048042d4500d51250301186c2060342001d1501013a030011408006c2c0300034004d800e4030100e00c10890b010803422307010f0003628011813298130300683e580307030f194188440351a0040040a140e04803900704a40342e240c0c0750360224090780c403246007070fa65614440c8118540040300c521606201900512481c01411206805 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236750647 1250 236749397 236749399
    0x13021c02041a0f0304030c03021e0a050c040203010f06030e010b041107110607021f120e1005010b0c211c0e010e1c120905010c0f20030f031503011406 66
    0x402401c0d410701c40320855104605103d09030031000c00000d400710380b00749400b82119101303106881e030200703040c50f132a8150504054000002c0d0001c1160008000041091b49110201500c065085d985085140da840c15000d203c1e2006260319822035200b010020342c001c4480e908014410021200c5c210807040d5260031009003298200c2d1040d00640f9107103041c13429a05400d40c010092042040055410840d0826034902c100030b00980c183ca01720b43c4485400b820800c0307c2880d0003000345d130b504402c0400950b00107910945c43c1000411120407005004200e11714040c04000307407600e801c00308003160304403407040955a01d0203a509000700840d41125400c0407461036242c1d030007800048102142c00740c41d5039522811010214072100300000c1d040c05011228600440100000784403005034a0b81425615030b100da8400240d40c41c0c1d84994055040190100c14180960540e100303100544002d40c2d0300e104004c20200702850102c0001c140c88044280c11181c141e0140003400501e000e500c0c2c010348101705850035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236751897 1250 236750647 236750669
    0xc0102030106200105060603010504020c010209030f1c05030402060307180b040801060501030c1d100c020d050a02030f0a0503040509060a090e06180307050312070201060807030b0108010f180213021c0204 89
    0x403c414800c14050030b4014000281325034a183d203400100002580808010300455400b40304000981c1d03030611501d9150710103c405804640f000c403543c04003420700d500000301071020034018400940c9500f07081c1c9901000728201200618400d940020019140303600107043c40400040c046101d917030640018089074800e0b00e060041c0e0314501019525810f00120300703000400210807900c0e051405114409003100c882c02c1c0094802c907650041a00008a018140d8560303200030148011420204204030b070300801c01d800b03410041c101d40d07202a228455481014401c502caa030108000360340b07110902000300728821040102e03081581e5501c1d00c03102d084030720300c02c8561003140b2040080c40100407144010750002c003640c9842c520f104007030241000641602d04542d07903440080307140c6504002101c0a94090405410070b585072101c01c070f0a403014404400ca40c10704221b01c00c007a40044c4114502d030700768100c0d5058510b000c1e10104900a001c1d884040105641c89405400300013000c0d4010800d0b40c0300e000301c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236753147 1250 236751897 236751947
    0x6060614030603190201120906021207050705060106030902032a010e06090a06120204031a3103210f0204031e0201051204110a140306060a05090a0f020c0102030106 72
    0x6000854070a5015001038100584c043da025405540441c0b050401e501d100c02c00b151047c00300c940100e002c491065000443d240c050f01020702095025a0030f01c0c01600e010036644c0d0313842c2c0303421042c801c1d0700615032501e92942c219517050001440014244074403150314400144001c004004640c00c10340070802581d0b0084181c100b05040300c20300c401c00b800d0300d42424507119044a581c95040d442581055080c003011000908005036294482047c0313002151500780711011001d00780420110450712100c810300c0031312002906200e900d80326014104580000a030301c150354030500066051004d514603040314500088070030740c060800e0b0390048468901801540c0c1031904501074501019010420504c0f074194009420101a68094481e5020555841640022450f00005034002c0901c951084000b003626040421895074448000c0328490314461509011980c441409060502d10980f60300d0f078070a404440d901140c1d046071005000b155690ba5034000101400f4001650052800d80071071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236754397 1250 236753147 236753177
    0x7030c02210303150310020c0102040e0a06121103010f05010e0114010203040807051005040b0a05120604050f06090705070b04150c020d0801060c110607200402070305092803060606 79
    0x41d4034140c08801002503180d0340721002d0803003520101521042e41842824481c2c550403c00d8005418508076003c009a140c50030128000765925008284180382c524164081044019485a220b81590001c2150040c0300c40b030b2002c40d01602510120a10080c244000060074a200d480064121086501600e92501d00c0304012610381c4034034886c0e000a039001890900041c1b4100031210810056428124509561095200c900b504265840700101d40082440c6840c0b140d07078200e103544503104813010002864820300d03a40420f50302a220502600100d00054001c070b010b00110b64850350418501c45640c5090f1600c03c0110350741c085101185030500d640404060b000041c000c0380a25151255a22a03003000f00890386c0d192081420303030b8032240c640c95141803030b100d02d030060801c503002d039a2000307210004900414038a4081e2200c24000da20400040e40801c2d071010a9a61149003201c8140c01c440080e0348e04a01070103201e82202810401840000402545604c070004a440741c2d207525440b050292 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236755647 1250 236754397 236754439
    0x60b06090307090c020307150e07090b0303031303120204032004061a0708040e070509040c0f0914030a050304080f0d0306030f12110d030903020c03030906041e0305010207030c02 78
    0xc5090368055018000c10321903815103403c441c8400040e1310440781003c426403512070310f0450203107540c081c031036403a00e02c80390700b0b4400e008803c064030706ca04084c8070704042d4401096681c0710061141e0f03c0740c01910744c01420107208031440394100c80640e5041d501c0725141d040900703622803e00d00c8086034a5980c5840d2060b420940902012100b0080d50003c2c40c969818054a55a00100c400c580b0729400f008081580412030520500402290742c40507150354544c800c0c4412140d40610300700502a00320054400301d50b0106500083ea0102e400742c41000c024280880d203003102c0c205004126010104ac0414421070001c1c1c0b403c41d91980004a80000b41c041d43c00398121506800b01518007200d064264006c20b014090070034180000345012050800708412080c24240c90419910000ba00e03900b2420134540c1c1045038514100341140590300c3e08142400248a520452080400140f00d05000088126103001c16000654112000755541c15035464020052141030100b20f1041c3c00c80b0b008888a81006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236756897 1250 236755647 236755657
    0x6180a1208070b090f03030a0e060709080735010b0a0e04020904020f01050c0a0b06011205010b091507080a230a0f0e030a050703080d140709120f140a060b06 69
    0x186a600d0b152003925074240c00c01000f040082248a1304411341d5414404100440c840e1098900009080d107244070b0482c10a0300c003a04c080200404071200340040c0704045004000c6030001890325202884a0f1481001a003910351b0b188008041c030030f0a09025101908600f0003d002120110001d03500c8404102c0e82e41020348000e5081642d8400240040c10a0f1a0000d000b600c14103049082501c1015800d25004c3d402c40d089078049201e100b400308558201043c001e00800c844d005111715810403551310b109000d810180c03441414211a2402c1da1401041251407a54011012a42d40c49494130040e240705040e0440b0b040c0c03010116010010305d1440c07400e4506030701c419590282c0301c400d0804215180301420f021a80c0c10700038000103c0c0021410441d980085102c3c59500342ca0343c90b80300c140001c07105120300b20312845804008008249078070505540035a504440c029090002a01340804400503014006008050504d0307a8800e400307000610720441486180d003881030820310300910200c1e000b8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236758147 1250 236756897 236756903
    0x10c030504060804030507050d02150703230705040f080606010917190602090303041e080616030c0509060a030f050108011808180409080406090803031e1506180a12 72
    0x401d1206100700d43c401c1c0700702900036010b4901103092901c2a100c25040115417501140507922680410b2840f0441c0b402083d440b0b012800c003009400d80c0e5403200d403c1d1000300300e4900030103c48000081d4006006a050f907024044480c51070220584402c1c150340d8500301680c1e150302044400200203205511142d4802604088001030f200852418200748280568450200c55154080c000300140707441c100b01900003007401c0510503e0aa0a0311808808181e55400c034a00c942c000f0410040c1d00b1201442c1d4945072000d030300d000592000c41c01e4040b1034600801510341da00c10800901d014489a140d0030403541001002c070100841d981c0c0701c24550884a030a40e04140c0b900309820400c0115000101802c140c0c500481c001c50200b00200008080b034030314420813200b00c1c0703001c05c00340b07d40b9500080c1d00c400f902d1040b00841c51401c14010b9100500004440070000010402c00a8000801c10840315001407000c1d200541791a04c0000c44544124000d0a41d0300410b0700356400150a41c2a80703120510f590 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236759397 1250 236758147 236758157
    0x60216150503040c0b130302040e01110a11030d05010e090d02010b280504061217180d020f1201020c15011202060309150108010506040b0909060f0709080f0d0e010c03 73
    0xe440109036125000204241c8003590545030004402c49484010800700600d035900c808030f90304600c100004c0320407548080b0880e03803501e00e105420702e50450484000d405603042c1381c20f20f016000d59041c910b10ed100c80d0345603c1c5082200020388900a010414014003581c81541c0701c400e1400401c030700321801550517075400065450f1781403018101b61a00d81201081c5501c11f51515210400310f01624030903031080c291600180c0580301404204480085248000d0403030b60300d4165245004204a02da0b4248a486121102d00702001c6584044800711034501c05082080c09540d4120b42c14000d402241c00d0b524140100007094110326407003003080d41079441042040b983c0900c0f5809001442c0c00040c0301c91443e20460300351190b04031000f40014000d14880c4c00205681c0782050900094440c1f4182c0030307001e01104002c1c440c8001010801560110003000c200305a80e44d03500084034451840d03403000e40349000d40d80c4503110602c1e0205500c02c1404047d1103110240700641d0044a2444000707a010380060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236760647 1250 236759397 236759429
    0x4051602120a02280c060c030c0204050c0d0f1a0102070b0f030a021308071a03061807030b1203030406060515040603020307050405060c010902090718050f0310060807060216 76
    0x90945000382c0039988952040328125260300b220b84615202c01e07041d030602d030481c1c008400108402100380101134109884d20302d49140456401411405202d07400070b10450300e40c40050b06446050043d00d045c081244814801131000c6800940207058070400844a0901034a01452a5000160041c11034a800100503c1c0c00a658500c140e0b541029000c41111a001c020000900f0741070030208000e000c40001070b0040720301d00000207070703101c0310311031a041c10500600030000140d44414841c0340c02800040b1011040e641d00c50110000c040003000c0a92004014480d11162640080558415407050750200715003078540080000c80340150810001c2204208800e009491003a0081d68008c502428002d007415100d4000810a070050540c0d248160f5580e1540000e5280801034240c110300b142c1044c031480f031241c00c06e0702030b946940d0084502840b400e0041c0162a2400c005212103204205803c006a94071100401e0700c8489034410300005118103c0589148100c11004a044490104101d841c0d8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236761897 1250 236760647 236760673
    0x30306180604180302031c0605010e0103021b0613020315160f0219060207031d061605030f0f03010e0f060105190e090f0916050307030f0f06020c030904051602 70
    0x245001044182c20549a5400151181c3c0300e680c05002203110f50003030340e242c544088106610f00110356070140c0150402c481000640d1304404403400e5584286005680c0d0204034030307201010600016146014030902c401c100503003410075030f152a014801c40540b040c503500440000045601a1881c142010421010304c46680c000d02c11a0b101101c81d0045c1d408075000602d401442e40c03155401a92540d400060500c05c00d603014040700b0702d855003c401c4924400b034420118019000e14001c2e240612126015141070060801c01d4519851807062590355800d100940844180c20170320403180001c1c4220301050520700181d804910440040c0d44203803c0441080405480c45540c1205d01c052000b45000e0b220b06031513031040c151160054040c5054103040c40109030b441c01801c0107001401c2c0000b500305104568000c2807030000c590b00700034000101041c0d82003c44041c02080c2008250910006c1c0c03007120a41e001c0064002da18045034100b1299440c006030400411600100400580103484c43d4089 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236763147 1250 236761897 236761939
    0x109060f1a09120a2d05070902030c04170106030203060702070b030c0d020c0a1b140d0b070207081902100912030c060b040c11061f060804020103090c0312090503030306 74
    0x9140005200c0720480d80003a0f00542024081e00050f0380b40c400c2c46403040c50b19000f010910032491204d1012040201560b03d03050744030103c2d400390400458001000c03414940400080c1c0380a084c0d402007118040030020740c1c4038001c0400c0d00c0200c3c000d004810000d5110341c0082a00c60807641004c001c10710b1699011444c4800340c0c0408108141240e00740b015070302100040202014052103011030030408503990703044009000955000c40848100c00310114038585489009510307555000ca49407400b502d84410603801d110050704802c0d0b05208046d00d203401c055281d0781c00512540295122540340100000840c1d100c0070902960040400c12140c142c0021302c202140d4005600800000441000680005050b102c80f0160f540c00a81c80302025407280c5414000b0726085000b45240440b5801d103000c1c03070101c4200030320420341400030303520001e030569000e074010001b03441c4d00580c3e008d02d035500c902d040120300103040400030000d859604081040d060000c2101d020f444001c1c00c21060310601d82107040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236764397 1250 236763147 236763157
    0x21207120f05030712050711220506041b020a0309091811240406030e06060a0302011d06070303020309011805070b0a030f0f0c1205040b070804030320030109060f1a 72
    0x4030b0b4803040141c0c3c0042a00c2c03801e2a0200c64055a0320350352071140307040111003480e2101860384181c0380103200c65110481440b40780000104160040f4050b070740c580001b002064581c620410403403600c03000702c0d400d95010a4504005c2d1103602c5464085484d569500c00b201c04070540e00345c288031119050380104000860050381c0420081a20103158007000320007c0741c407003120700c0d044492000301c2c1c2030003100e4150090850032100d4074010191b5280150020745014010310019041c400c095000c000291030000100c0032135a009080381d03560300001d02e4000c000390b0003200c200030554a0541d6040341c01c407028418000b0729402c20010310071346040c6012000181c0c00403a00400f0705603502d41c1e060715000e640c0600d00119914000010b0801c185440103400f04048520744842c00f85045e04000010f03101030401e0b0341003255850720b50800d564514007070380242403900303404408039944102c811543c542000254140c0340c0361241440b00310341d9840103000c0c0e141c55001c1c0c43d100e100c9800c0b00c08a00f41e04400500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236765647 1250 236764397 236764403
    0x1003091a090c0a090e010e0114010b0f0c01050c040501030b03030702012102091903020102010c0c0b0a09020105070506090604151109150405151e04050303180604081207021207120f 79
    0x81c0b110040714000341e0480d107582e0083e00302ca6144c00740120a03800030310440b0410b81c240c00c02840344041c0020f0103806030b04140035083d021704002c00c0c1c6d40c0c00a204403040d142030305074810080010b030030070100b0729099407c1849118000380c2450070031016401c021040d59980c0f94182c4a0f01c580100c1e1855411190601402c1841710039402d02603950999917866600078410b0880c441c40c070b46c45045d8000203081d02c0344074031b17404188401c401c05c4800260040e9440341c0d100512200019901550348012901d0703219107140a0000e10414081c00300e03e00d00407a00301d002c0da01c071300030021022900408030f209460103001070103c00b170340901c205d60041c108025900252155009003600d001e4403a0002420550039440080c941903000c01c41103d09a640380c5100c2c1c90041d60400b86050a1914001035560700c901109021040741300000c4a038a42c4641090310003810124041e12121400c0c0342a080d01034110042c140d110309440100c4d4004401c0c08100d00040e110310080001503482c0d140c46000101091032011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236766897 1250 236765647 236765653
    0xa0c170601020f0304091a0604080703080306010203090d1a1815040503040902031807050103150302040c090308030c0a080a0501030f080309070f170d0e0919150602010b1003091a09 79
    0x1c210024004d00c0208041c0c900701c04001030410540384a03800c24250f1101d8640910410813091021040c0042c0200403603034041d0600340d0340d6607200d004030b0960250702002504041d05150348800c0000341e24064003001c08043c1088969581c142d88800b84140110304288150407040c95001c9002a200410ba0701c1405070080720f02d405d98501d468012a40700326244c0401c00010440c809110744240b00b040c00400003403900b4060540d50140d400341030586888024415556a580c0d4040640100103402c019900507400d01e48a290648041c8901d501118000c0300003000c0c98001351802c1036074403880381030340e82140b503490121445556400702c9a0019045810b14841e0000004008400d1503144000d40f00e0981d162940d0764124003010b1911088410400c2413201c21044129652180d030400d40d031000c0c1c0c2a100101c2c110079180c01d07100400754518003400307000801201280094054000c2e01c0c0c04001620303862020040124100c080720204c2700300500d060b40040200c8000d15281c41403c0d080001c10f800c1e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236768147 1250 236766897 236766913
    0x1511161106030907080f0a0c06030b0d020409080904060b0301080307030c050f0f0a030806041b0e04090c1419180207080d0905060406050709080a12030e0d030506090a0c17060102 78
    0x48454100300e80802444d844088144082c040500c6074104201005000f002c4600c0d283d9500003c0990a000d041c0c10107660fa00b4100142d6242c2051f0801c141e0043c204000c1501142840441548038451480c040c900b055030003c1d40c20200d408490488000101039810408290f8003111902141002078416109800090800d0b040030f0010364024101ca00040801c10110b250141c24010001c005901c6140b90008040b1134107100c4440e424039850515160b4421160400058000d10805074050b101540c0c03510f000c200c50064a881c4e0070a8041102c40e071444000c58070701d46a6009890092080e07101258100170b6503603403250043e25145102e290710a00b072172201014031084941507601958103034012401c1c441840300c544a20398000c885886c1000b200c41c100005c0c19522010107000412a444204010781001d01ca98059601c0d6040270341a07940c1d03001c3c08600140a41401e403011441090803038086880c5600e903104222502c081604c5800021110807001d0b480c0d00c0c3c000340602d0650141c01c40e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236769397 1250 236768147 236768149
    0x40f09020702150d050a061a03040f0212030f0c10020f180f060c061803090f0d26070c0801020702090705030a0921090504060e0c0703030204080706030915111611 71
    0x50420204c42000001300c0d850b105003105c0a130f0f2181d52200101c00e40c1c0c0591000200140c0040703d510a0304603000c005841424030202d806e40c842d002510140b40004200384000008002c0104001d0031a1801c0b5206104c000041c00d040f842501c00d041c0307030380ba010410301d17401014440060041c240002c20480203544607402058890380104880c15054020340208030101075000311014184408800071400c0c210b40d02e0100d505e03082c00d1600288510050842d14007000000740c01c0f0074000303400000a803020704001603441c8603904091400c0303600c59140400400e405c04144256040036400030645c0709aa1200340c02030380e0545c4050290b15141f81c40303044c0d00b40802c0e8050344800c03101707110481001c860094543c000309683c040b40c01c098803980c1000d07070402203818240c1c2c8507900007400402070340e80c9a030503280c140e00070b100c0e81d40680560701a8190001c1c8035505948080942030044800714500102030100400704c940700407140b860711106015688036910301d98210810580310b01412101408444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236770647 1250 236769397 236769439
    0x90611031303080322120e03030c0a0c061e020309040b12120307120b090103021c0b100314010e07090f1104030b0108070e04171819030b0c040f09020702 67
    0x600b0a940742c0100100780300e1110f4599817114200d28420f1010160b0551940e54000c03034501c0c400d0b090341008008064002195010b00885440840c0032007180d031051401d00e81010362200c0380c821100131801401c3c0b142080740d0741510841c17103609258040d619003000c0d0f00404c001440401010740c0c212130081c9000400160802101c00807248500030b01ea10fa1900c610010013402840e90700b135642d90305040d84a00c01c1d03114200d140341500c3d811652507072100f4020701c1d0100390b101c0420020701206e5030b40b41030140da051507046031400d59000300750f00d80aa42c560640542a1045110322041d01e9100000030080402c8032b40c400303064000d0600c008070f0104400c0b80c081d500d036000303600180e446143c1c4c0d000400002c041046840c000709a83c44c1c00001078545600c83d00d0304c0071400c0c42c0315110340030000361007503114401100361b0889000c0180396468070082580b40b110042034500048400301002008151110907100503a0210358241c1d4008000508050030000030390041e0070101c1c0c22049112050102250031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236771897 1250 236770647 236770649
    0xf0e090f010e010614041211090c03060405150f101418040614010f0c05010912021501060810120602090607031713020a23031c0206160906110313 64
    0x403000d251103505003003038075001060692204d03082c006800d0703a19540b801840305407412600c0d02d5000c40b95480ca242040710012600c0681c00b584500d0340d070304008418101101a60181e002a5010040d95581440365141074807035106856001e510750b181c0040510b40441810302500da5403618080040100c070070715000e41c1107250140003c12403d6040d07101820f040c0715120052001d011401d9002c4040400030346081c09094030001008020112581481740135000544c40380d40c0721886074215200c510000b9140d4940d600100b62980d660030001501c10702c2007480f58020b1450106c2c0144441c90104121f010401582048441640034403c40c00c090b6510000341030214080e03154482050420040044071a800a19002812509290410150302c9a00500003500d0200101032000c5418a07038411034142c151805507131500c00c00e518480c0b403e100d410701d03124065154088840b25151440c158085489000080001030201c07501008113501c41c2e0030070504040510300356454901d2040c0c400f40c6040003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236773147 1250 236771897 236771911
    0x41103011d0f1212070c080408030d050f0a05040309120f051203040212010e10180b0109150501090b09010503070c0506100e0610021b13020409090c060215010302010f0e09 75
    0x104024005200d00140100340402094003843c0b071402c0510341d50444080c1d00a8451810044282c105108000c508021a0003400000088989440c1154140000307030030120380075614a00384901050089207140103a9001c1d6a254440543e01c40c18203032510024056443c042c1c0d45900b0321045000422014415000c2c5031441d80d034620703620324150061100c451400030203542d480e803610b02c51300140b540c04030319040c1c41e8a00d114007246400c9503950942045012070005861010080c0c00021810180d50106503010000000da202c0181e0f00c500540c0d4107032a0340b046400001040022080641c8258011a44140d4509200121148075101e20b45488811900140c804050030000c0c01142c030300321103041c0d1000007100c0d100c025510040c0300035268004910400c80714603c030b910411403580c81c0c0c17599078214928900c0840d200e40c0d5078101c860240000b0181980c1482c0400d10100f40d80f407001c50040304406101c0c0407231402d6440d60380111044508d2080e204100420186070328a89d540c3e022005024842c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236774397 1250 236773147 236773153
    0x3140405010b01110303070215040f061b020c10050702060331210522080a031e030b01090b0304080f1c1a0a030b090304030507080a0b0609040803041103011d 69
    0x2c0000009025103502036409000d41d84244200701c03820f0740c000b400340028900d8102c0706596403681e280c105191400c5c5840201101e05103040010b100030040c011807100700a9038200c07924089494148544020bc00c00f010000660030841d04d0003504100f001150054402c1a5008141c41d07034858100f9403403105180220760840c0d0688130400c1c015180a41600214015800c41d0403081141700a0002d108281c0c114079002800c2c03c0380740c410003580c42d00d0002060180b040d00c1900081d490001c0494000b04501e003055624501d040709900c1c800e104002c450740781030f11400302c1d00381803d03410380300380d0001001180c01c003004004221623480050b0150240341038481a0b0745c2c200204a00200c199a05000c01c1501105d802c00850095625005840c0459400410105540e255040c000e42540309c1d68002900c3da00c1010b50000305460000340e8a4440e60055800078804d4070f80e1800c000a02e401510042e00e6a0320074070210700490604101010703941c1004000003480c2407495403c66159420101d4000c40790 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236775647 1250 236774397 236774411
    0x71415010306110412020f01020c0406080304091d0309120c0d111305090d0e040b100203070c0602010509030d05070c0c180e0a0803040605040201110703081801050a0215070314040501 80
    0x1a41d00880c0081500f00051900b0b203404d01c1100317071040d42042c601921031070602d40c0e84061a40240300d81c00a4020103801409055100c81c4c41e5996a849845400c3c4110301d084030303001100103104061007117040c620014519104101c810481e40710610f002c003d616001e048d41d0494240e03100c1d0b41514117184212080e588000c0300504111007007400300044002141800100003106070046400e185046090500d070460840e140046070040a0302050a50030251403410014010740002c05000540d10580d0000802502c0380300403800ea8005031005140d41d4800c2c4044403c00506402c282e5001030706103020b82d0061b02039142c2800300002c40d8807140b040c02154589002c01001800340d400e0a90156005003015082a0388903280c1e44001040a003d0550f6030020408582c0f241d004103880901c514102d40c2c29507100c2c100744117035500254284030782c4100c915401907a54020170039a1406451500500700240f01a658078039041c00081c07540c4101692103201c060790403c0c0000d05401113004074000203243c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236776897 1250 236775647 236775653
    0xc090609080d02060105011101020c01020d0f0b0a030809040203070e04050a0c120603031b170a11070501090605030a0b06040801020f041508160f12050702061902031603020714150103 80
    0x1204007a0040980e0b9000018100307401500002d07082c0c111741e420b20f440304603980400030a900a0203800d00010031035000154402202c1c11540020b1440c5a07864420030020b002d00341080440ca2252000504110b824490000e891510b81d022351740c840c202d401e00403034422060700000d0446800b12020300c01c0340e40e255544401c00380c3c0031039550350b6415940070070401c250854a01070400d081c01c248452002503a00090010044152104114040c0c2e03d014507840da03101a202520140400440c45054401c003c030000d40c0f0340c45003840d002190303800d0b00c0c3d692654445039070a6024040071104640c00250400c400500100300f44000c04038003229001d2240c96904104c001214105800c03000010803071502d060001003071041460400c4501d542c00e110604501605040d1041c84510420202a51400e000c01c0015a0080350041c4280080a000030070544c055016100300d000613500c034400341c0c0c0150350081e10b05000b0341c018a00d541c0618402c60700716a0440d2040d01e030035011420070075001003d000400130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236778147 1250 236776897 236776907
    0x4050403120f05010501020c040b0a08071805060d0221010929010503010228030b0a15080708070801260f01020405030f0703170706150b190329130c0906 67
    0x74441807220038041945045d0000707540c0c0d54090005449141e442c0c144410075520220000020100d410a60b0b0354240d41f035400400c0400400f20030761482d42410001401403a00f0385404116030b500900d40c0300c00309080c5030780220030366034404490920365030751812101140f40d00304580364920b943e2a91000c540e4040c1640c0350590b20680c40b441c02a801840b14800c84c0c291000c040d01040e00c15908900f051804a00072005011380c020f0144c0c102c0c0110401180b0b01048403039030307603612545440780041a15940004c450842040f103101c40050002030052200708607000d03c040450420003c08070717a0076000d0300240c3c00c0c14148402c0325100d03940080c1c2001641000e0050022051407040130344041c41c9540c4400b0a1740203081480c058034000043e0030703400c0200c180d01c0050460718030098080215140c01400e0750540c800c40364400c1949d081464820210f12038052003c00d10140321340880001000c130b04010340e40b0200c030205584042d0903240320075400254032900d081d0748020307565100260316040b80901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236779397 1250 236778147 236778161
    0x11d010c11210412080a0806010518060a050702030303090106090501050604081c091203030c080a0908090609040225030f050c0316030203160309051509010c08070201030b0405040312 80
    0x748821842034108090010030051420100c801c0c032205510104103501e619441a5041807820001490b280421721001d1006450055916114216141c441c1030054445010b410000108000c005507190405d040c0030015054441030350800b45d00b0149960300003819600701300c5504100340c0d9148010000d1103c20302803035004160a0311130504d0181004446501e0f070704a03a8440d88009401401001c1c560f1083c030700c1d03400030004011860100101498010064502d0142000014001a000c03400003c2a4401da41a4550103403101f441c000b0018180460b0741c208842295101d0380c02e001c040d420454100d170401404c107020310b140503200060300e009022056884046010132200703100b032164485c1c00004642ca408441c3c045170008510300d1904071316520503a039912925800300b00c00c0d00e08040c1c11a50030819500c0484100c0c44085d06100c2c005124042c48c0b1250f400240358208940101e145a00180402e0f0700602d07000c50305c00004070116084d240c081c0c034110009622058003c080c01c0c10f51207151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236780647 1250 236779397 236779421
    0xb030a0f02070b07181a0a020f012904060e040803160507020a050d020a0503030d06080f0d08220503041211040b150a0306150509010f03020903070605031503011d01 72
    0x50030a019520f0f41e4a10810003040202070001d14013154010030f2a00010300c008146851500c0900c1c50544496405038102d00e82c41c0015100b1803111040c40d92040c0a000041c0d0301856101c141d010310007000000282c0040c06858100e640e803540428244040400c0034480c90007142c00554904000c00c00caa901134110368980704210041c07103550010790350b6110716011603408036504001c501150002034120340c80d59000f00d03850711001600308400f100a40051040390b0103807058561800c91820b207281c4075069a650f610010308041d00180703003001c041c601c00d01981c51003481000555400e5645074a540c0c401e400000d02c1100b2000c00b02d040058188492212580549090000d2650107021030007034645414107048400e40071402d480114400c0d8000802001e00c141643c1d5008824440039040764041d16100340007500c01421001c586000b4002c5602107200540201001e5241c0002190b0700d03040640340c030900071032b034200070071301030354240035800718203004060266010116282403030858000311048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236781897 1250 236780647 236780651
    0xe0c0d06080d0924051804240503011109100503091606050306092d06060c010204030f02180c0904110405030f070f0909030203030a05071e02070302030d09151202130b030a0f 76
    0x21210045d400029140c60000300c0176012980640000050b01070010040750804a605201c0c00c00301d84178442d80c0b041d00700c070410740c020000c41140d02d184100900c140219182c1048415607181c250500c40d10055500c04030020968881c40310031200c05003100c1082e8807c2f000500040107101c501c0c41c2100c1229081540c50420031001c0c2030148114500802c404c2c14403105a80031f40000381d45d40c8440d01201d85003080c2c2c070300866440e502c83c5040801d03800340d5502a8040c0d178a01c00c01ca0708401c000000c1600444905107c03030f00341b070780d8903003080050064502c03a03200145c01488005402c1e1000c10100400640400280c03c1c0b40f8202a8041545600c5a100400c0d940c103003940e503c0469008000c4942062081c0d00108150380d501d60103031080c044d100c0701444000c04071107681210560100d440020340c2e108500f81c1d17510b030b40c2c51501242c1d14291401b4125180c51f002a203d03100c1401912021694049500c0c058207201281c01741310041500755002e141d80d554000100008c81070584540e0400003800802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236783147 1250 236781897 236781959
    0x3050703110d050c130b0607140708030306060d0c090504020c061918080717030c040303080c030402180604110a020321130803040f0b0a020a180e0c0d06080d09 70
    0xb03050741e512130ba621803501501144040100c00140c5801401c2c44110140800d42d581c49245091102400381032058481400384203808215458040121390003640018401d13070416a881a080c0b008080c0c00740020144021400d002550f038a50f030000e804448404400741055207449096090303490362800703010f4947d516006160741013156140c02e0080c0703160820421500c0c1d8800703180400840100050b42c0d600520080200300c207902c040001030003078030f00c0380e9101503d984840082e080c181c081510001c1d40901900b10a0800c40d9941400c0c0342e000d0b50081c070205440c5041080d412072540503450340700041e040041c8040c00707501007522141101c3c1140b203401c48149800e0200841c40845058014242c0c50000b0108060140c1343c50044044c1d60080c19400032410030110800003980260f0003c0c011591452040c014503506002c4182180c1c01c004183c1000c2c0d484921100c84ca40c81402803100442d0340f0703d40440d5807801001500b00c50f0701c01d1b4a40091603801c0045000300040c854200c03110040e00c0500d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236784397 1250 236783147 236783153
    0xb01020604030f11010f0e060115030b0307090b030114040c0501090602070e0612031306020303060906040b0307060302030a0213030503030702010e0f190f060c030f06050a05030606060904060f03050703110d 90
    0x810b0380000700710b072601c060ba104800341e0b44d0740500007484082d840b031030610403040500e140c0420014103c4020400c0f07042582c0d402c0c0c80a800f91690512040d0741604805d00420802c07800e90000000380340b00400000348480741e840040d84800f802d44040c0c80d100060281070109507046034201014082030300040c071000d882d03d0080745201400401d650b00032200c074100394000c500108280e030150400c01b824081d140c0c0e01ca01000307507241c00865102e031255847c440403d0213810130f80b050481c04200a07020b4800c00e4100791050300a980094280e21300a80d0800a5489042c140c8107a030001e035208001455407030400210080c01d6510420143c40c450304009110070b084400040c1d04180010a02a503203540d8000d801c0c001d50007015080050151400c0180c410a1554942e000400c9091074101c100100ca0712241800000245801550f405a00410106e1000d00e04200602420840200301040c0a40c8840d56004001c003203620450701a840110288204100180c0c04465624183c1c1c00c0074034841e03661 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236785647 1250 236784397 236784407
    0xc0302090310090c0503070303030c09090905060f180d0522080d300509011d0d0509060f07080a090e070503010e0405071a0a0306050a1a0a0528030b0102060403 70
    0x500740058640e075030f405040030804032510304401820010103035503010355641806009407503240c01131400621310600200307052a592252500050f0020300401440d916403c0080401e02c000d070002d8046004003980101510040102d07640324440c2e6529141c98440f95a0010304840c2c2c54020600b0706090203030144185000001c03040f0070611a89030100c0c41906d101045007040c032020024650086c69000300303c03551926a0081c0d80a10241d5000300481c2c0e01c5900c2802382c00d407000c680801c19030400010f0414440c89013010342056000107082c107240851116078080c150b440104119400c0c070001c0b4820300e143d03400020b0704008001c481400902d500e40b550008106220500502005458100c041010301804008032006803060408aa8880f041c11942c401c01f40c1200341b000000034280f07813021455041030700440086403d60070307040d2080c0c08403000c698415003004011000700b280900194014035081a40703070b0300344844010740c2140a1311880d0000c0540709074242103419544040700741300001303902c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236786897 1250 236785647 236785663
    0x10b03150618030a030926192306010e01151b030e0d21170a020703020a120302040f050904031e170f070306050901080a020609060912010f0c03020903 66
    0x4550050b40c40015a80e0510442441e19402d501481940010380030150040815415940740d0502007000f0080da0f030f015440000c0c008034100c0250008030101c41d4007109480300175085482425405004000880300d038120003a072502030281030380a40c004100f041100c1030140d0240404200504249034210000b80151845600110018020134401380034988a00d400000c0c10800034540d51866100e81000c6038804448400e80d2107541d41540590882c50203030804030369201c011450300e40d165a4002c0a00000e401400c0d040d401e50007140c119200003181d17a140c000c000c003240c0d1001615282810000d0720225107641005e4001c80c426014000443d40000001d0404c03c690515842700400c51001182d00d2101e40f606403020720841001d120410380010056880b55181e81e40401c07a4550312400c106400d1001c1c800d65045811001c02407002d030500100400e031082c0041e14140c513002540000c101914101c1e918100d071650b6494032049120f9460007120076483d0107250a609100c003600000b5210028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236788147 1250 236786897 236786899
    0x50705060601200a030f0e010f0c0212030f0408010203010f09060305100f0e0304030803060306060306100608040302160b0d0c080c1204020d0b0907080105090607080408031b040b07020306010b0315 86
    0x10249402800d0072001c4400d09040f0314980540d013110486240280501c1400c0c0b0400e0042248070310446099441104140d403460134030b42ea1717130040c403515400307002d86050107002c2c0c502e050004005051180031080010001008020b0005a60707603d06010f00c048060750b90040b075280d50800030108003003500001c2c2c0700800902564001407100300c100165000b8a4514000c6201c0e0002103000002d2054020242d8400c010035405d407001a9507100406807903032002c0f141c82e80103800c0100f00340b00d664030406040b50700c54402c1c01298005902e100d40800e901400c2e0344580d24440e4001017622106940340203003a500032035418054803500b80b1180ca0352030380c00744228819000f0540380004065580e11904000345d150004040542030800105403900d030324441c00781850541c285400b040101d0000500c20744924401da850b080d40781c80e00d43e1140300d19880034014040f46c00c04048122116400e0380021300080911207151540e606241c41814180740c0c0581c03010351496018000c0010303081401010a803100c8d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236789397 1250 236788147 236788157
    0x804120807020c0411070b0c09010801151106180d080606040506091507030804050d050f3001080f0106050a08071a07211d0a05091009022107050705060601 68
    0x340c1c1540407450526040050303035000b400c29804240e101c81200052459600590005000c2ea44880004180e0703c521804940010074982c0108060200d441e003580708821a40760035a05800020380281c0340070425a06591405210442140300390400c02042400103602d0038842e080e4030348100098200e000381e218260058500003050300ca550b8442821600095200401d2900c42440d4100245032080071501180c191151843c0d010b000c40c060360a40710030303501045079645042688402032081a001200040b100c80d050055002004000c03101d1134041c01c003400051420b0a40100c0f81401d565541c0d104034040d10000800b0f2208000125000c1d050311015419100c24001c00304d9405900e01c507402d4007604070603a0403131079041c040d19a021065030b10304030713a00c0c1c9176100c072801c038005184000003c040c0d9110b0b0304041c042006042841c40d9690200284d000060180d50b01d02840040e139020b0032481180b80010039946450b4580003030400d801c00d816141450410020307580b0259142d0018260b1410302c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236790647 1250 236789397 236789401
    0x3060102070b0408030703020f070b04330f030c0f140714061311040b0607110411120a050115080a020c0304030c090203070905040e07050f1302190f08041208 69
    0x80d000304414001005000c01c01c0d07507a5507542c0c40c01a10f80c1c010150440050083d008100c0f1219400030b0400183c8014114040c5410f10701000d076205004510040d1842c2c0706128610709900103500d00a15414140b900c0d0b01810008440b07004045801e1405810103004509180040ca07039400122035025541c1c0511040c0d85694904101e210114008029002840f80ca0108414480901030b200002c17440380e500501415012400c12090716051503001c0e8101a0a000390404034a00380c110400254002e040043e40c66000002d00e1541d034400c510118009901d8005d0124007091842403500400b681507090b45440c0d42e1200c000c1043c44050324036541e564010a01c104922410700850f801541c1c401c1c02c1c2c4032040d80e5002504065001140c000010031203e040020301c505190003404240503510000c1c01625013064100b141e0040e5081181c0d400090f2800c00885440180c4000d15900303480303115a6001e010815070090070200341c400d840c42008101814030000900c4010103600519041c1000e034099 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236791897 1250 236790647 236790649
    0xa1503030e030124090e1506060a0c050709060e06030a080a11012c010e0a0201050d0f15080604150c0509012006070e04200904110705010509060117010c0903080306 72
    0x507003203030711140362004c3d8a1000032150b0742d1034100c0c0a0072102c01c91030a120b1101200d0110b81c90365400d080810080c02c04100041c03051900c00f0040c51201124180f42c0885003d60f10b40c1c03031a1002c070350084001c26036030382014004800000400341d442075044004245060a030760340d0a0f007030300910a07176009200d207603480700740c42c02001c1d000f8990a031186850000f41382d80d4550301103041e444507031641c1700c03a501e048000f6071b09800200c1e451044940684805240c0510503100f14018888080c03071102050740c6102488207400542001c000610110001307040c0d41c01c090900109200440b4443e1002c2c1d841c0101c4680a1508441503a00040703003420302c0e1521180d001108514040d19501414050150804014204d50842200d802c3d03040166000c2040920b031020800c0c0d0342440c01003807044058140724212161401e45c10031980704016000060618113203035100750948809031405500c6400080c018891100c05a0000b0303543d02140c4003c0c84520081c40c005170400c009400040e10840b0004005442c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236793147 1250 236791897 236791901
    0x30109260f0706090201030501090e0a0201081005040911010f0503240109030212100b030a051002030a0204240e0108150d060e0f0c030c01020f0d0c170408010c080a1503030e0301 78
    0x558401e00300d000340c2d0703500207103094001414481e800f01c2c00710303191100125450084d4071514214801c26401400254201d800664400c0801840c0d5403050a20810102d07a680720b5008040301d440c801d002041a89480e07200142c0400a0804907404010b0240b08002032070005915280301210001d41c40194003c04100481d1104600e400c003035000003003900c0883c800ca0000032840c81e02041d0700b0b41044003101c01010552a481100710107007003640240110241c580c0c2540c0190313000300c1c12030401440d050b40c0e40c100c0b4541e07480a200007c0300382c1e500da010700f502c5900445540200c05091900030b010b80341414011a5044080400601a2121f038580000b00006980400c4040302d600701102c20b8450700006595480440c40300640c02409040304480b0309500000d42601d010f08244054007031590104001c84624841d250b0944250001c4080b0002041d2002c005001401d510000800d00300440f52001d84125000341c039104850f46005459111343c60210806001c1d41d52524020768a09040000280 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236794397 1250 236793147 236793157
    0x20901090e04080c010e030316050d0b030613060f0c09090c03060906140a081212070c0602040e070201051510050d060f0f03020907020f070b0f130612060503010926 72
    0x882124402e000034064060043d240c0c0383e0101e0001d000403981075404645a020030760b80b00015030241c1c13100740c0c5000e000d84082e154480021400050801d150000603203040c10544a103952800b01504101c240039143c0140c0c0d400c4041301205100c414000100240100c0c51407280d07060b0941d8a42e400f1a020f0700c2038000390300074170808109000f555240d80410118141f041c0c45140318004600e4002004400071890822034029000310508107215604403507043c6000604410420414201c9a00052414030103040038007120f0030411914a03164801908444d070240c8100024680b585080c096a61440411004407065240c03007038403001c5006140001d0450390300003850701c4402010104800c6142020b607411603000b11135a580940700c1040c1640c564894500e00c1155270090a000c0c008207a07010004e001d642110503078546821b003c0c001e51020101140c11131000106e00302640102c106840c00b502000d88011002003003560b08560783e86e2080501e0184d18044d2901a20701030350f103961070301c050320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236795647 1250 236794397 236794409
    0x70807020c060a052703010b09010e011203110114040b071e110a060e01141e22120c170f120601030e060103062a02060402010309050f0a0302033103030302090109 71
    0x1000004414400040d9484042c5e8590181d8139180100b80c7c2881c101e00c9041c100c6524440e010146e03400c0440841d101c4200b1002a001c0c401201d0240c041d41409200d440d90140786540c0302c100c0781c200b0380341501228034041c060004101c1c21212042070343e103902090f100d2805080c107000b000500410b2180d4240380c4460b601400b684d20701803140009103c19004103140310302d04040382c0010381c0d40010070072040c4001d0351a10002e0b104200043d43d02581c5101c600041e082d0718035200c01901d00c550360703143d03441124022500024150640c0008011041410340072a0714024601c078186030501144d00c01900910280078201203a10300890001c1c0d00039441449d4518116060b1103040da101d08051019240140740840d03a0507005407040a094503400315010800b07036580c007500c2c25407100e4004401420f040c140c151414003802070603a0b401201080710503102480380e00550b0b11260700002d40103510030101507000401040340700c0f41d1100b0011000795425a549410010784801503040100da090759990000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236796897 1250 236795647 236795677
    0x4090201140c03041e060f1b0204020705100b120d0305060a050406080d020c0411070b06010917010b090a020712080c04090c0e0f01020a030504300303020a08070807020c060a05 77
    0x1400b0041400300051007529100262100c0c03002d0980c071003008036000d80c4590030000381100c20301e41781303144078141072407500780e040c071525500340400d8000404a80c0405000c42d000d40c842484000300c00f180c1e006521b002030b412950350b81c44030000d000d8035884022a03c1e00310b00701503071000040d055603a9500075002402c03004c0c0040004c0d0f43c8400341c081d40c90060045010262117800c50540241c5018050551408603481105081620342e94a101c2d040b800030b81040d0512000001c04211b280e81050741a032800920b0001003050044017091000b4001c0c050101f89605004100000201d40f0a0b01220f068421606e03100c500c940d04e0030b1819019000b943c01500d0458280310010858075440344042c05030743d000303e524180d1a141c0030010b913030f00d4030694802000718109000802c04000114886850001c4c000081021414401948001d10344030590440100b6030128040c6045035000c591340741e02502c03030304008805080404002c4d50b40c001040109105986c0006d80c003050700c1c840e00548841c0c00b070440f00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236798147 1250 236796897 236796907
    0x60f0c090a180504231209041b0e010306060903051e0f010911120d1215090203010902031f030803340f030e0c150c03090303030f0a1404020603060409020114 69
    0xc100041c04003034909943c0c411024440c1d110043d0500c1742d4a180100c18030041c001180c03010024901303a00400840d80d070150b52410103000c483c0b14240c40f0248050181d483e419400401c4001508403007203500503904001e24800d00380001a00040d1191205010440c00340c0541d03c0d80010305d2a01c0c8000d465042e10354207048030700302000038851010480820458078003c0c0710807071a00e92035445440003007440c001603e2007491000c5000305d40c080c03a08510107007121007a2a495038500340c181e074400c2e40701b1040c0507400401c0000f00300d400204e903212200790174500940189180c40311689404040c0c80317441e0481521660096101d001600441c45091000b80d80c103802c0510b14020b06064461811b5201090030000e08046410300425503005015004241c0154080c56480800b1590002c240202d568481040b000186a0f0104050740c8544101c0c1c01ca0b55852500110728010f039185541c401c40c44490f9202400b0041c0d5910042c0e0390f001c401a180090044407500040358503803103542910802100002d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236799397 1250 236798147 236798189
    0x150b0f12030702090708240f0402040305031c11030106121d0312061c080f0c0708060712020a09180908041509140d12050d050705070311060f0c090a 65
    0x805800b0141c000c4511102c03582c1c07250001d07184a1012a40c49040101408004052003540ca00283c00300034090b12040d00110400045403c0f0303030154009650340e901c041015404c5007503480700720140b124101810b2000c41c50900e81f00f01c0c2400180102004d200383c1d41d0340c03041e0183c1075074081e0381c0221414041c1c04200e0000002e02d03440354031105d03020302c1c01d850a00002d007081c205a01c03100c0800b80e10900d07640094102e07454000c00c64002581c544095681007004408000f410026400581400d40c082c0000d41000d090150032000e210700d4006881c0d0040c0000381c010b1303410411090071500404400c3c1324032900030503050300415480100801400010402041500f01340f00042400507464a030326400540b1903042051039100701d03038205d610461003061007000804030402e403014007000e42084d5081042d034025000c00d5641c11101790b070004502040c03803000d242c1d01814081980c1100f001410311030034880d8503c00081401046003810103000560380031107894044582e4003c0019107030316240c40030003075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236800647 1250 236799397 236799403
    0xf030216080a0f03060308030106031112011707060309081204142a04050f0a181e0605070e0306180c0904150c08070203030604090f12090e01080307150b0f12 69
    0x4100b010008800c1206200c0480c000d214410a0760303041003800741544e19140d0104d010703060105c07408012023410b12190849079910a5081d01800030009004a1001d565401034078220b0320b17600000425003080b07106070110380c034201201c80251909104610070b42c0e0314140b0504600390110040e1040c0304103403d940084111480e0303000148040f90044003550600b07010441034810a0300c09070a2100c103000860301c500100c3e40245004000c981550101c000c16860760b00c2070340740c2d1503003441c0e009880c103030b5507070030400c3c544a02c5500003400e04000c0195005840840e0f03030703a64010b000284620071030200c80400b0804003c4190300c071000030710302c2500d4606480c06009484101152940d00c6082c08601c041c0c0d03500841710a03204040650045003035980d20f50801000d410035280c20380341c40c0d04481080001c5041c9004440302e181d103640314000000d03e8004400d000d41e005030712920b00c076001401030f680080c2d00300e80b03411b1070284050300210700700702081e000030b40780f031105000107500685460044142c84004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236801897 1250 236800647 236800657
    0x20601050307120c050f0409050a030801090b0603010608070e01090915050a0b0702010c110a030b1e06041107080d020c0613050705090403051903090503030705090a21030f03021608 79
    0x1503098520082d5681c80c3c1000b60340c1d4800d8020b0890b51411800e21950403d62566503901c1c60041001c90707840881d0700c5440c00e20160100540000e03d01c00018030030b003512802100714920301518010325545c50448001d1440101038010b00800c182c1481c019a80d80c41003802c0800b4040c109030030400805403a401000ca400319110740c50242000310300c0090310144c0c00c0c003926219030301a194104a1181a0f8464143d18001c24050354041d44480011010a8040c2c104c01d116040c080010514a142c074000d5030706100c1e0080030f40d44105e040c443c170200103849240c2135408250b80014680d03120000d9040000c080e0144908002040c4101810098a000d20800700108180102c3c1074941c655110f4081c08003c2c00202c6010300403c10800240520f00254840026500124a00050481125918107085502c103a44036000100c0c086902040f41c03030401035010051000104a40501c50301e640440303114075400c10080e05200f210840107041a0190b0111100c0043c5280b103015600341030710b0800300303a03080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236803147 1250 236801897 236801899
    0x70309110306071b0c09060306050420131a100c0b0c03150f01120f02040f050d0b04020d1a010b36040e011d030a080606121b0c060702060105 62
    0x100034a1410241000702e15140240c01590b14040240840b9441e080c080b0480d810840f000e441c1140000b840c030b403161159a01a511442d03020a04d03040c6828880da00d070f2000c0100c28100c12001ca12891107580f02c103020340c50303040c203c0c20210750003d00341e03030b03d50312204120042e40e00462008020600340794481d25071180e46220f82030700c107150b44407074803040d845002c12a030182504041807828407942c906200e44101514052408082d000440841d81c42941d404881141d100c54010400340300c080b182800d001e02030f2600342d900d0400340d01c003901c3d00c402c00100500702a0262080c0e54040c000d001e40c1c0501d0f9002070951088900c15540d490414000650140d21280081c0524a1404d040e429600003402c0120b28100e81c0c0d20280030440341003000a1400701c0301c5501541d0b8624011031844405c0d01c080307100c0326404025646408119001424440f0000c00151040004004602e00c0c0207840b807441c8e401051a108181040180c00816485413150f036428a540744030380c1003040400d5030b00040130b9041e070b03030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236804397 1250 236803147 236803163
    0x717040f0326041707060f05070f0e06040512010209090c0703121107023309090903120c030705040e09010b0a050102121210050a0e010f05010e090f090a0803070309 72
    0x2c2d2940c2e05041c41640c0c012200601c541ca00701140104050b400084c031038142e8001d42c2881c00d08a43d031600201c68040001ca2889516032040101c0310350080c410301c605075041c0c103100407044106000518607109038001c0600c20807800810111101095040e140f100700c0c05840c201050605c01c042c20016004400210700156080408000858840c00790040d441d840c101180e040c6440c5a081214042c60301100d424406c002c4000500901160450a030a40ba40706110740c0d80c0b00a5181440802d0200500c090343c0c43d4010440c4e2034800e0800c589803a403100500ca17055803292502c4108039000c0c420b0b5481185400005070500c110400306600c49200e481084600c40d10042d507401c010390301c0e0071000d410030321440c506012a001d0f038080c0324111548198a802248400342d11600052448410340c4c02c00e0050010910041c0a0703000004c04040c0034282c242440c2c404c3b11030904c00110000d80080c0703050074a42c2c0c900701045a01d24200640a07100394840d817502d40302d241102e0001c006001c0c072041a200c80b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236805647 1250 236804397 236804417
    0x307051222051f020a140c0f0111040501081605040b0a0e090406021c06030506060111010e0a0501020c0613120e0f0a0306050702190206120402060d0504080310060518090717040f03 79
    0xc610b0348201c41584005c0d4480d1019003aa0b540d240085070404403480e140f03030068401620000b83c0c00e10540306204070b02d42401c2e8880b8100000102200c00081c584030101540b424116000c80d0420b041d141128012925607030307035604540c0c04641107514042d001d90001000c0341400200101600541000340348081c0d09400407011548050980710540f001800781c0c1c02c40f1001c41d50552140081202080303c0c0400400e880d0f072141545031910407210001c1e14642d60100d41e00d0603001c0203100e0550008105006101c4440ba151126561203c0480400060020320b40c2c504c480c80e10703480790a003d900c1d8014007583c00786540b401e0280280c90101c1d80800140203040040d480ca03240781083e00c5c107240d00541070fa4204140b041241d040a40c001e042a43e0080040c001c0303003034200310382c02810720951003290050788a08200310502190074042e003281c000c3c400c00f840040078611000740c150700507080840b04019503465116081e00c04044003115130019130300b8941044284010408034903555407003965006014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236806897 1250 236805647 236805703
    0xf0b030102160b090a0c030b041a010b0a030f2703140a0804060b030f1603021806010f0f0e040e0601030c09060308030a050405330705030705122205 65
    0xd100301080641585042c14450300469a40b03d51142c1c001014000c0340d07070540164880c41c024084590003151130084400c02c1100700851079a40b0001e03c00200203001312541002c02034102030040c03000c00b6080680ea00b50030b20342002281c0202d03103030310b10407242403916200b10101540016102c030401d8000c5540b01d03600d2051601303850102c892039609550b9680030b50316543c1e80c103009001a05682c1d64544184400792b070f40d22105100303150413420310703000040710949148184101502004100c014250340d00042180690f040a4000301d141e050380380c50340621640401c00e481030b600d902d0718950010720f0413075004d626a00c00100d50341640c0c0500701c1240900d41d40d00c2468180e440500005001d81e00070300c04200242d840d134000030f401a11a02c00e442c180c01080d40c007008402c1c80120808014011000d02c03640c6d2a044108190708411036281191039464020000382a5128007017190f0080c00b08400004d91400c0700d4400480f0035a80301c180c400104509041140c0d5943d1040e40c0300e1500b04082c1102c80071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236808147 1250 236806897 236806901
    0xb0a050a1203091e180b0402030c0d060e070c03200601090204091b23040e0c45011e2a0b040204020901030b040501080f0c0306091b1f030f0b0301 64
    0x2409498004034000f07142448100d8286401000070155000d4581001c0a06d9603924005184202442204952925400540d20701a80d01c144d0010303065544410a0000bc0c56122000c00d180c950107080101c05d03101a072a2401a0761141d40446c58a0700030880045000e1000d038000380200c030041402441607414100740e4a0741d803140c000101021413090b101075514072010b4003c40c45500503242555040035034a0f1000d107104e00040303524602449000546091440040c10044a200381c2c00c051481c18440b080804400f140900c000101e0142000c011106168400c1d1426030000200b144d032040602030310703400600b0381c2d101510052100d58407800e1003030340040700c40090086c01c0d81081c451602c0d5282c54092000940c04000302d00d040507240c090286480c1c41c0da0040d98024040d8000410410565903c9a1304280703e08041510907004202031120400c00010751540c5025022200321142d1358a50019200d01d1a034081380020b1100144003805250305a030100800030711604003809000440010982 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236809397 1250 236808147 236808179
    0x7050d0b010908190515070302120c07020f220905010c020f0d090306020d0e0d0804150204080304050609030a0f0c061223040c050a090203060406080d120b0a050a120309 74
    0x3da6840340401600c0d5004c1002001c008030b0240c416074003417180c04801082e4100e81103680e072010a030001406c07080003d100fa06158844110300e4107600300212580000c800c0823802584038480c10b656540d0819500b481c44026840c0300000c1c4041120f03043ea0301d452406000028101805802409440c12000c0c40104852124100b26a41e42c0446410b5030340d480025005407004041481d80c0e1448280380f0442080341a104c00d82588882040e45011b00d071010111044c94501d004d0940140030030080c4410010540d41a10740441c2c480b5180d00000010a2429030071040203480c002004a100d01841042241e00c001c3d034a65698903034610000e61140c4003910380d45000b000352002610410301d0b11182c503000a9070440e100720020119140d5690000303401c0301c820340006503016800401d02405280c544101001001e130b1074003905a201103a000a4002d440c600b010022454a030180502155104003a070400b0b0f080c020200603165460302241c800142c0344640c118081860301d00d0108038040c450188807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236810647 1250 236809397 236809409
    0x501060c0605040c0302060c0a060c0e01140d0b09010e0403090902190c020102210405091f05100c0f030f030b2b0302070f0e07021603030e0915030607050d0b0109 71
    0xc24600d03199900c000040c1002081510804003d42c1d010005994040040ca8a42a60001440b68881e2404c240d411102030326200d0003400003410f90900c0a0341c001100008000c108a03955481d0407001091101514110b440300b40d2080481c4000308500c0f00e41c00b0307650302850003951442a400c0e00d440d002d000703d101d244600840208410914151180310300310910110340b06106071652110018042c8518181480d4406c10f80c13007002c18240040c0c20710804c4250b10400d0410359480c40051203154000240c12405010302030540d40104003c11070050200741d2940e58410075001481c00309e418000c00e20170314070b65031400090410800300f8441c035005481d600c1c101c020164003091180d40d00900a12440404403c5080d0302503550001000c4402180480082c041208420b00380c0c580380c074000b8204183c13030b4003981000782001002d002280e8842840101440181d403d210113448818004007407101556000340d2500c141c5040040d20799202c40982000c007032409051040a9900005442a8925018207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236811897 1250 236810647 236810657
    0x31208010f06170403030207021005090f01021f020c0a080406020604020a050d050606040f0905030d0b09180d030902010504180618090b1308071a09070e010b1b0309040903031a04050106 81
    0xd0f03106011039404003a00f26201c2e0500500c0c0880d40e03404128820f28100358040880c0002c02c01d44000d0510b5900e808007004244041c01808080d556150b0154000c0d21600c0000ca030302207030034080c00310100a5008200e03005a4200e88a607034402c0020350f640d40845080b40100c840000004039410a804481d9038154800098541966610184801440302e014108202e58540c0c5107172010401c148024011031145d0704010030184901f800307000009101904140102901a1039125180400b01c2d01889580c028503003c50402510700040350503000d182c2040c7c10328040381500e00602a041e502078800c81e40d0b010f0b5000256807001d0204403c44580030005010051000c0004401c11b8211001680c4280b10340b201505100d62a1191401d800342c0b243c901b070fa90400803081c40200d0b181080508000c3c0514050f00c0e4003503040506000c40382c010701146003843d600311812442410024030030354414500c051f00070480c00e10142030003000350490142c0d0081040c41d202100000b0b040c54003401d4145c803890303111 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236813147 1250 236811897 236811917
    0x3030f050103151517010204030209090a0308041106040504020d0b01080702070b25050109050f06090106350f010207060b0406030201050f0715060b1207020a020102060711010e0304031208010f06 85
    0x83c4040c002070000301c035840543d0a400300e00012038100403101c0c140384900061300d5504501c1401290f010280404103c0d602130612200026400b800c84c61384103500c10748095009805034041213450090341c01055000c0d0000c40c1c950710481c030980c0300c0c0c110280b09076920806500c41c1401640c44000d6401810700c141400c111601c640d03540701c0441d4000701a0501d0a035482442c03511000e003141d80c0d41001b15603d81110b503020b20491020046250070041000007088164901040302c414410007540b030005840d0b52081c0240d004102903c1400121045e03410380c1e090340311042410f4000d41c0440f404580c80b034544116030314581071500c40d6100362903040e117450745094030814800405400081d0212081d040b0303d040c88003440a40e02a4000a0011211b8561564070f00d07a009815880700405400031580194003210140c0c0e40055026085400c90816403814072200390a1805031031942c541e01e066100000e0000f080011100003040102202c0d030f07900300d8698803441d50756240341b01e52140b600007540c1d001c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236814397 1250 236813147 236813183
    0x6092406040f08010e070603050f070c020d0b0702071a03090601050d08040b07080d0f0504030c02060a03020c0a080a14031303030c05120f010f05041e022a070303030f050103 76
    0x80042a0000080000e41007995a421612207861203400c5007090f6510341920210024040140401070000f9040910081c036000900100c5100c0003031452042200703d0820030b00b503455151560a10035040a0784040615240601039980c100510404001940c100140d0010401800c19603009016200103051549d01e4801080110040091b080e10381280c100300008041407607400426000b4842e41249895039024036003041100c00c0c2030342c1081201d00f850100000264030040303130042c8950454002d51605005901207000f4004e22104035114882c40303200c182803040103c040c00160440d82e840c0c55004502c1002c1d50680d000079500c084200c0030001803c0006170094104010708502c51921900700556003d00030400c60080d241d915100b60100018051b4403001203131038004e001d0a40e030a100c0718940740121100400903014172005154049010b103a0030384030f8092510070030b80490044403507030601070245490b88010310088003c2490001c290b0765050480c01514120394025400180043d0455 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236815647 1250 236814397 236814451
    0x801031202150405010c02070909050a1b0803040b0409360f12080603070501030507020a030c0212070b12070306030c03140c04020a09060206061504050d051c080f0609 73
    0x8010301940a01001001122600c000b0035220754002c1c0c0011488845e05030300a4200b03001030b0015410345041c00c03019000b0810014040c070101d544804002400c84440340c0c141400c1e00e964000505030b0000140c0010500904d201420603100022410451040c6800790f145140f000d42684540d039071041444000c0e050707020000c101049000d81d03a41056402c45a4480000c010350210302000300c0c51000a0041b0380c24204180c1c00540408c1c01c0030860790a02100103561644148001000c10890440900c115110140c907001d0824070030088170a5907031038a2000c0c0807038000f0f06c2c84100200c0d1010000e42c1241c2300e0b004d800e00312a00060118815411501d95101201c43c41e40d07034504a01c900310b51f40342140c44034801806411120394468000301d081140003420300c500907002d1071041c0e4241c10000700e186000340c101e4048034030071252808035482d5807610500704803031060840b2107207540d244c000c0081500310107401d01c500d4500703501c80a20307604c03801040703115201551041266420303214400d448031b41103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236816897 1250 236815647 236815673
    0x509060d121e0908100c080109020c030c010908071b0303050f031e15010f02160519090c0513091a061b0f0703060501061d151b0c1e01080103 62
    0x918001d01c0c5100b10300011405614070111081c00260b801c2010403c0e40420700010032042c0040d0390511402208180040a000341806244000d50380000d4070301c407242003081221408041c020085c4401d40035410b111006810001c0700ba281980100c406003c0c08000c4080a000d40341c0c9a00c505003850010b240801050300010121010410b16080160f40d806c03940c103030103100320300d116892803039101c41e5000100000d0140381d15070150360159451801d5945e91358585001d4410a9607006291403481c01048680c81060340509000f074036180b05100b525034044d004000e48005100801d1000d0390300c1107520200c0c5c0046140319500680101c8451103882c005c2c1c01843c03806c4108120082c1d084c02c0440d150300b084140160b150065000c81d40030070400c203490098500404403800e00ca481c094903090202a46400c5c0c48045215440604200a802184105131031403115409001c120314082c0b40c0e1810342d9002e0322801d2500c11061f03001d040840d50003000130350303060321010394484080e0303443c594507400144d101d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236818147 1250 236816897 236816933
    0x30303090c08032d0c0703020f0103020403170702030d050408060f0405070f080105160206191e020d0212090303011d060a05030a030f030b0306060a061d0406060f090509060d 76
    0x100180c0014030840410103408451a881c50518402c109060f041a13070034650402c02006070414041d0001d08540070a054040340d0b0142c0c0c400f01e410f11640c00480080c441c41d040288941c0a50300394891404d1001302404200d031003941121180c00182000350b80e02d010f1031285d070415074840000581103406034007d0f02d401600c20011036501c07070385459031003903020542c0e0040d150030b03959541040810b034015148011540c4490014181c582055a03400c05a910031003034941071aa1210591241460640e9095043e124805000c54a0b0202d0500c01d1019602400702e540360300c3d03041e0b404039a00d0640441101e04072060000c0040c641d80744400300700e00e040740061045500601172540096203480c1485011003261003641c445c43e01c48038118010302260b440b003110a009a000384104900f0380c84416200c01a154142007421403035002440100c81c20b20950451a0001c2c10f0180008026801000c0c603038080030203881e18072a19850b4130034800101801c41d4001e50004079007041001040f10070390420002c43e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236819397 1250 236818147 236818163
    0x50415030b01060e1305010302061213020409030e0102060907080705100c1b08100b1305090a05070e0106031d030f0a0909180b130201020c01030c110f010c0207060504060903030309 79
    0x2503a521049500a0268866004a190000c442019203095100703c2c01c2c1d96840b0b01c0402084d415030300418224002c0d00131560b501c44d5207101050701d600504540701e005503802407062200307400c2440c008105880c61038100b8058440c120210300002d4005c156441034801d084020070300186490104000b042410b0040310070b02a01103801c0005c03a04031800981c1e00d003540302080407410318010300280b81c109110000c0954528160300000c0c1d50b602c0f4a00840030f603200f440041000d40340c08100a082c030704d519000078102d01ca0054000303808004651000e040780c940c0d8608200740911700b049400c0300c0314041d416501d960400c002003c0c2c0840ca440c05401e000351035140c034906641c1c40351000c904855400c1808202a15112483c6003002100c00346980d000b401c008500007008481e50010307585080c40d00a0a05054498082d04442d0b0302c070340a0503001140840803500b80c181d104041134020144000306500601403010b0119055000d242201e003250b101c1d6880303c052900d1074408030000d0065030012181c442e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 236820647 1250 236819397 236819399
    0x1005030703090c080105100f0308040b03270604020310090309051e100203040305060601030207020d021516031e0504081c050f040b1c05091e01020903070e01030b0c0403080301050415 80
    0x31140034154003c0c2c013641d400003503242051000c682183c04581e0250f01c049070b2865040c00011041e2081d6021103206144850700d03501c07808160032043e8900c08a02c01c100500e1840000000c4c00022500c0c0078a000360141c1d1001520b08078120301390782107200050041804100104650b042002c01c242441c03090121007644405090700141026000c0d050038001a48040b606006104041c030031150002c800742400c51800c08c01c0e0303002c5506640c2c50362000e0312400f0203520803280c0c05210b2085620410414100900100a51030050b2000c0004941104a000d00383d4648800c103001d481154190380c83c8500034052a840218424440c1d80c480c2c80507010081c0500c128100194004040c202400484009039140c0041c3c25004c0c000b22a64030320019064180320030f10018030004a007441c0c400c021200c04601e1120b400455a0180c8501c0c60b00301d4051080b030a0005000000e10000e0303059030701c16407058045454030f040a171300354000c3c0c3c0400707400c0c4101003004203c60301d0581d00a01710450b1000c9441030003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 236821897 1250 236820647 236820653
    0xb090a120203100507020d020d02030405011e03110d0e0105010f03210905090a0204090b010f1b02151224010503151306090204060221070f0c09020d02210402100503070309 75
    0x92082078606170050b0340110309408401d03130144000040040d19100a50070249024002800c4104c81d201802d4004c88200552030004e10a401c54024086017500182e96012040d0900c0004e200400302d052155190500218000c00d11207400400c5a801022003000c10300c03008885920b81d102a0084424841c801a00040a480d594400761280070500313030050700d80d840e003081001a100b003484050704102c0c0c40c0c0d0103010031f42d800911003030a00c0080020400100c1e40b620108400482d80f41c4062013048003c6a9035404005011100b4850102e048280d04054058851030711001071890b0f4190200d501440010380c4111540c14141680ca00140403049440d1001001c0c0203c454540055001540000f02849010303010486845243d14100c80580b41418005030340d0018010220000d2121100007070006c00d101e06072007004080c1c0800c1600715076512a81c540f4030020b41c000592460b944c4180b001030170518501030046407007150090f10b030400104007080c0807192139000030700000c00c0c15070b030b41c001e5004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 236823147 1250 236821897 236821901
    0x20319050406091a0708012702070c0503070f06140a09050d0501091202070803030c0904110a0c26090d05100204060809070b0408030a050319050a0203060a0b090a12020310 75
    0x255000d0b460001e50b0149038209030070080660000c2e529020310030310070700c4101907000c0c0242d070440f0390b8041c13038074507001d40c111402c0079042290065802d0f0a0010a100e03003400020103811044030422000c4030412946d840001004c079469100f090b011841c0d4241c80e0040e0800c80c070041801c001c4c03d107400000d02d5101c00000d0201c4858113000d032030981d511741c4500200080c03403401e140a4511400200350662401d24425582d10004100a80420703001c1607069440c1c0fa1608141c01000b0091819502c0e24080e92000740b004040c441c3c1580c4030040384079a252205000c1c198418031100b20721156142011039018469203660060b400c035518802c01400e018040000d1001d4130240101d40e45100c50390401c40403061500c160354100e41e044c3c034010002009451000411a503d850590a0250b103075651450144045440c0b0810011014100b0080003a980800d170700031481440304a13040c0c4004c90720761441c1c2e4228000e81c1d0b003403604011119424485000d294010002062005040b07800b408035072804101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 236824397 1250 236823147 236823151
    0xf09030806090c030114061605072c01050f04020306030705060d020702030111030c030402011b0b01061e110709021e2124010f05120906190b06070602031905 69
    0x800240031406010709490b11444940d0400250340700d076410340d41441d4144012100d10400d0500c148400102c4200c00441c0d1914056050342000640e00955507803420070240e1254a50200040d030707032030410380f190315941c501a90b050702c6c0040d013a200444403e4040c00020b610141c000d070b0749403241110009256403107600030864032442c110b0160f200e002e6403040c03509440700c556a070741c9150414420030502d000345400f80d960294092074100b008841140401801c081c40c6100a803a83c040c401c000326100d0307001900c01c500501451081c528154032342000701d0303030141f04039040e01c1580c01c80c950420103002e80b600031344030584034605c4010054a2045038080e032a480950054041e05144128201840800c05410340c0000025403030320351407400b40c11014407049070150380d6062104c0956034803880c61107201540c0d400c0d5820a110811420820600d990340d460444000c1504541a0046243c0021a020b090f0300428081d100605040840d500d15001c1d40009100300301003441c2c41c0341841c911a0300e02440d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 236825647 1250 236824397 236824403
    0x5041506081609050103020d171908040b0c030702060703150503100e19080406030c03020c010e010605030c101b08071505040611030708150102010608070e0105040501080c010203041205010f09 84
    0x1200c0440003030001d590500440c0d0140c0314413860200100096180c41141002c1310390b02c80e070b0024004001e08245401030007100350003192410a204401c0c019a000180705000d03602800302030b071981d61080148800340c4800c80b14000140c20403004141c840d8020741016103140c6030030300313010350268640c00800c1c517003031a07502ca0000c0c07aa01d5641081403500b05021101d0303880300700180005040e4460322104442e01c9680304440415943e420304007150341c0320742d05694039070207074600a02822090014050207004c190182c02d100b8001c00701c00d980f440c94068030354868280c0980f40c440243d2000b40400500301d030b4102c0d00f40c84a40080016100060a0012071126030043c1d0100103000e00781420450129a054102614020400c00500c0a115003003002070b03900510510079410010b02ca400101e026007150707808441240709011000c984140040305041c10b03181c0a5504002503a44c40652030355801c08102000c5c003603002008103001c80212200d643c04030901450006c5480701050008a0480303008201c00d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 236826897 1250 236825647 236825653
    0x18210307150605030a030e0d1a0f1f030b0c0408061806090d0e0607020d0c06050901020c040b0906060a1e03050403020114010608010b0d0e010c0509090a18060504150608 74
    0x44204181000c04008003101c07103604100c11420305012a0740c81030700c40405001d0242d0000210307402d96940203500b0070349620612040076a1125201000c045109949548501502c000000e44817032019681c07030000440494004801da01c1c50711125600540a41031450400c5d04006c0030403c59000c0101501402119240c44252030100343e1080c20810040c091070030795000f180d091070740c4580c480000041414100c440994179070040c4002008000e84400003001030028001c000703400e075004405410020000c0e000e40e0720118400003000304450401c92001d0f8054014070200b00c5e039042a001400c43c01c0c0182c2400340b9001d40c00082890869242020306002a445500308002c2660a0003100500f0107420b01449055050041c00f4102c59014041d5440141e40840e940100c0b41068200e1003602d5107c0008205d01009440001d00c907620110f86140128080f00100d8007160a80c07050201c000c00b01c2e14200f01450041d994140035020140c815500c00e0705000401e1080c1100307100b9840208200c0d402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 236828147 1250 236826897 236826907
    0x120f0705060705030106171909050c010e0a03051b1c0f0c050d0c06080705090d060b010905060309030d0506120d0906030507030c05030a0209041107080d0f090305182103 74
    0x324a08040189680300700041400108201d83d008044407842c101219070849070380e036400207640150303000001c040c000d1030709000c144001c1c13050220b0040c1007403100382d1720380c1e40e401c80020a0089200c45440b00414560100c0345000420f031203000100085c3c10000c0040c105c201c103641021a01c000c02d21030030b40781d5506140c0c1c140704016000c452803009200594111089842c01d484540b240c10880c801c1c502030061000000d01a54801c43c01c03102020720050280f00401040d0811000400f2003640017400301da00c003c0c000c101482c007407007964400d21000000354a850540344107040640f102030560740d04809951084810a8824000d007980c000d01641c982082610340b01000b0f080e104040c0681050628000450a0701d551190490340d0080c0420300144c1d41d1102c50002c90300410829200f20549036000c1078480402500e82c004140034003c100d01440800c40d1005028204c88603603000901240041281162410b040500c0d0072208500602401e46080c0c0c0301241702036041c44461003003681d080010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 236829397 1250 236828147 236828153
    0x90a170d080405060a0b060f0c0601091a13090804051003020d0f0b012a21121802010e030106230111070f0e09070f03030e01020c0301050408030612120f07 68
    0x800e91611280a1404110a00303007500c681303890b41c002401c6030b10681c0c0c03109010b00107a00c2d41011150f102014242807a91521100c140d00c0e100d880a0180003107007070601c50319421011000782401440b1000400e030104003d002e4086c2001803d0500040ba5250814040010580d5440240400310760301928090780d5160181902812a82041071308e62425144c10703140c5900b81d03406506400320042035154103200103180003001c2211150040014121050107d0f210106100101d0040500c00c0d43d4481d190118103961520f000d840ca035001c900300c503049a41d1810701662040e109040036000103000014072030b48542d030540850342030f542c00c910003c0448012102039617004d05c5504c252800752019104041c213000c50440000b14500c10003946440b01408606a0103040c0005401081d91158a400d29030f07903450050411000840b880340980540f00305000d03a414180078503882550f01c01140c500d9a62040d04100400811100c20fa400313200b1101506210781c1790100809000c049066101e484410b60305d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 236830647 1250 236829397 236829403
    0x60915080c041a04020a051c090c0608070f050702041509021806180405070207080a260c0c1309170c07050a08060a090f0210120c0509130c05090a17 65
    0x1000311800340340f0b49000c0148540c01100d0001454a04640160b40c5050000044505d40103207103003c1102c9900c00c001240041c030a50000c641d05114100f4902200d43d52281036840c0c000881e10140881e031400540303a0001d10030001840d076184001c100196070080741501450508080d007082d01100c0c3d001908100c1c05200c081c1c42114020102d0b44145000c1c0020b5a42e10100e50044405009076244c001140e0800e000740300060247c440d0f0f0041f00d08090b55030510104030307158142c903c5060900700300798043c045a00011200d03601d25034001003840c210650148900f1001ca21a02004666904180c80000b060746401541031840411129101c1103604541801c0410719805103109040300755040000980104a141d80480c0e012f5001517200881e06004040d00080ca070300945c070419454030006041e0b0080c1a2250541100d101042504006a019075961040842066100b40302c2926054074956a4005902c0b500c01c6142450516848001180c7ca480068200417245c07a1007541a101c0c2c0a020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 236831897 1250 236830647 236830663
    0xf070c1e0c06020c040b0a03020d030e0d0602040608070504062102040b040e090c0303030f130809060a02060403090f050f040905250608060d0c0308070f350c0d080a06091508 76
    0x440302000300142d50000180d40d607440c2e2000a02501c3e50b0504ac0060501408241c0360ba40030103403120806481500e0828003e40c07181c000e51011511130ba01081c181445401075606907007064950035a002c1360181070100600380400000750f03154082201086503600d10007c1c20081501c18035080c2d035810b00307140842c24240100030881c041d900500070010701c000c070314011b203801019040103429240407a041090091040c05507084e0003200004601c0844e682c00100c5030300c16402942c1c2d5a011903201e040f12150900207101e41a80004244034117840d500e416404900d00a04c2082128541705000c901040052840810115198030280c010460369401a45203513120400310386a200c028034540d55040445400e00002c1d100032004540b031800c00c40101100d00419411200c90a5221903065101d00c121005200c3c0c800c04016070303d1400da600341400c0a030756086502002406a18403041030131520000010510b114090721008001114503040c03160007181f45200b2401001c032814210240e10704100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 236833147 1250 236831897 236831899
    0x9031104020a0203042306040b04030b090d050d020a0507050a050d0f0e0a1a0903060f010f170c09040309030b0405100b0618041109040204080d08010503060f070c1e0c06020c 76
    0x4002c8015031075804000c0354156019070050454032010a807103201c0000c0704448840c0c0020000501242d411040f1020708101c9100d856811070603179071507410640314098070f541c2c5008a0404d10103000411695009008070a41d145001c90070a40d040e26554600307c20300d8010344142e000b030130880e20f04560185207101503001a050441c0807514403004a41c0c01d000794490801c0a003079801c46480c01e0526007081b600c007407400070100c4401742882d00868004940a01c182036400c00c0c02c10001070041010310b0701d2444014040080c22003c59980c050224140d4028011000c2002807503001c000509103401c01400390380280c0080130701014003800401214460001c480c80380d001401400802d0f81d040c0c039104120761061700c0100345440800c0c0c51003c240900b001480d40035001143c0400c101c400000c05480d542034940c0c90f1580e90341d076401410b031140000d403101c507100b03c02e507800030b0411070185140c03008141c4500520202c1c1c1300c07410f074240b01d1a6840300007100d05016403c810003209a04000716104208 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 236834397 1250 236833147 236833151
    0x3050c030609191a10091514190e07080403020601060908030a20010908091c0305030f060607020607060b01020d020610030b0901060306020403080c0610050a033009031104 75
    0xc124250954418014400c1000c400702c5050032420441c4c0b200c00b04026102c4035400300c40900b00f05100c60038122050003500c3d801890120070942000498415000700c0e0000390405000c0001602800719840d82120010880758a452001034600c1e070070b82010344291207e545140441c02c080c0f50003400c008040e40040c042046000d801d0010f2800401200e072004101d04200440f0103800940407619010040003840079480e04140c0700030b2201450040034414404c03100340c86a15184040507000080c80103025001030390510002e101c10b03061010761a00072100605072803c2c41d10702d50004103143d0010310100c80c41038450000b4002540c0404c0b03800404070141c0082c02d80761800d40aa000424000d11010346602000e2001c0f4105443c01e500c200b002c0c580002081d0368031916810155855849201105090b1207900e00080906d1019881d1400b5a0001001c400e8203030306d95114580c07020700040a183d01440410044c5101c4d82d41d0301c9039401820700c15213840ba059891400c0c5502030110640800d40158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 236835647 1250 236834397 236834401
    0xc040314030322050114010f0f09110a1b02150408010e0a031d0118060306061103070c060e01030f05153d12020705010b040c020a120e190f03050c0306 66
    0xc010600304800010ba43c841510002d202e080080c09807460218444074840c01e1000450026031041c3d0000076a00e20305003d070030040e56000c0c018121411a8403045142500b40315944942e807050b468030648031603180500000124540004004107940100c20800c500c0001d0100825030082c002c601140074400c0103004580c1c00d60301d026089062014000f6100e42303108141412903800380003d5040590f040b51815503094641d04060001d20307184c040c8902065825400085400000007221985d99101c1000541c01e481d081081c2c403071a66801f400d44c1407645444011102800d28402c541c822402803210020214495052009106401000074201c5c10034400312aa100c2c21007941422003034003c600c0c0d40c1e07849811701c3c0440e5030350045809038a569000007442414420150000c0c1ea180d041128108103541036000e09913501c0c0f035050310081c031210101c4481c0d5040c0303015001501489401406440400820520144001c0040d421900c0e00904a007014420302008001c502100d002c154008d01c424 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 236836897 1250 236835647 236835661
    0x209152403101508040215120109020d180510050703022503080702030717090102150f100609050d110f030d090f0605030c070b0402030a1401090b060a0b040501080a140c0403140303 79
    0x204c2001007001e4062451f1b0700259148482c03490071902c000c00840030388862943c5400441c1e000c3e5001c8070b0740148071414030509080c0c1c1c00014649848243e4450010003c0100d80200000500700c0102004140b690034004811455022a541142c1c0405560700010b0310b81c10340742c040e1003064040d00c9402150b0091040000040c2110629a0308003e0720400f161a05140702c0100d181203a468a81201074143e0414000282ca44c3c1d10401e0003440c0d8016959201c0383c642e5412901c1c1a924440d0b01da00206114411010510401d07040c03680e0030001c0d0460030040700e810040380c9000c82503981c3c0710000345019410000c90300740001e0320f400741900345001803560400c03040f400c143d40100b60010702003401480c0800c04540e000c07c40207a000350b208030442290107044101c18001c0c0032018040e00d1403081c03500090050b203056981007040e40c11010183c0d003024146001182d0b1307440c2c010840d1113150350366070144a4101a4581d07051080030355001e203955550951030203103c03800b09807450245590040c4180082 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 236838147 1250 236836897 236836907
    0x71d06030f010e0c1207032907030902090c03040c0b0c100b190e090106030c090605010e01030b093706081b0907080717090123010302091524031015 65
    0x1340c42001c50b8000c030140d000e0200306090203016880100741030f2154800034080c84402c8180c032240c204041c0380d810503070341c0c16100b50140e40c1d109000942c04000302e40094485100e8501440d0018000d200d1100c01c030b80c59601d0340943d641b128001040b203501c5042041950340080c0101044404252284108002c1503c0c0c40001541d090144089105c22100001e490407003d40c05040159081206000e00a9130f948d2108020211405824001180040c4106165002e80181004c0f000041c09025040e40c41c500640c100e4510030344803804110580741c001440440702d00000803154460000011038529000c0100e1400c080103001044c103c00004002c07001f80c4e6038140c0564050041d0030078071900d68400b8001c680c001c8445e2080560040c90f4002e1000e5203805520480324010a07607002c01d5502c07400b240010ac00c407004d04c4000d5000c1068000100d900201000742c05422078040d01b40c05008002c01e00c40440c244c410000360581100100030003e00014184180b00203003034042c0014500842c83c040280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 236839397 1250 236838147 236838163
    0x403030302070512030705040302092215021204050706080112030203030c090a080307060605090705090a0314030903070303030c08061008060405041502040303080f061909090302071d06030f010e 85
    0x1040c198042044014002d06010101c45040b6140b03050303560389405c04000d0042d401a0000380d0140d294040002c0296000c0c607001499696550384546840c1100d41d03403400c1810016110484180d000e11590a80c11102c081c5140509d00c140050321000e800d0150081640d50143d02074a2a80c00018840010030780210840350080c40030b01c400c550790010704001c24032010a40c3d0110155120004480d41401895407010064031000c49405c1400d8551b660115898000e1a003400e40c0f0000040c0c0420001d0769a14050f076400c074851044e80e0408150b80f000a0928102d03900a41c0440e4a90310341702607042e07000307540c07680c050f5080740c1241c450240718400401c042030091001740120350350300104040c024110b0850201850712036082d5a11038903071800a101d203005a90b02901060900040f60492400464409a2122140e4182c098500d407543e03030f00107004a42030680560040030004120388402d042c2c030b800000d60708013041215040c07500030b1510b0240c09401c1c0c010182d141400c081c071800c40c0420401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 236840647 1250 236839397 236839403
    0x501060816030b0604081b012a0c030b13060c0807090608041a010b0a0e0a030206030402091008010207210f020c012d08041509020901030204091a0f090f120403 70
    0x3495444a00710640080c07481400a690207440490f00040302d00e0005040b201085400500c1906509180015211910308050800741d1302d009001e80828014052040d5040d80d00404005081d250340342c0303600006010540b182501000d490701c08406000c1c048c06104480d40107450080c819240c2010000c03d001143d014040412643c0c102280c2400800030050041803409852a00256500c660030f03825540321054110219a5803c0c000400d4a002401c120490342c024090030310317655a940c200000900010300c1210800500d1034040b60040b0244080d2028500c80e0706868a41d255030050040603401d00018181005940e0140c0300070142d020540075140002820040003420710311003800d030080ca10999200d605120001c107001d406071b0100c40c2a000741d001c2c0400541d2604450050b50a403203490b0301c081e4018550100400050500d0303130010f800d050044806407408a60790640d07816404080d964010540403500030700c0207482d024050a03070150081c00080c2000c40d0201909100380c0100c0c4409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 236841897 1250 236840647 236840671
    0x501080115050c1606020c120a0809030a0f05031e03060a0501081302040f05010e06030a030207060f12020d060f050f03060c0c190b040501270f060f0204090e0d0305010608 75
    0x9002260184050312050803105084c0c0340448071803e0440c80c4202030b4894071005104010146105041c600c000c0000d941e5610081c21006100340c60309090b0ba484102e202d501813241401c04404100004003410003503114002441d80c951600a040700c800c0c03940a51240c8021080040c45102d644140104044800a08086400c2d654600c03500c084100214006034100e814103c030711801c11515405181628030364401300d402c0d42c90351000d16950391074203180103000d644844030620650b40220f4200600c8111890840304003c0d96a201000f680c03c01011146000d484100c00d000201540d0b050070041d081c10384554114407000e1000039900c0c60080c00d0340039a168009501090240700740481c0008039980d08424041081d113140980d00c05004071811780c0c0951a11452000c2c0b03084070420035103e0440d151001080c82c4030764444020401280500701c4900d41e442105203800901030000d04014103a900380003c062085402e80c500300080b0341103417030815140600512046800060080d0001a01c2c401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 236843147 1250 236841897 236841929
    0x1060f080c0405040207080912030705071a04051003020c010501050613091107020d0b0103060c02010c090519090501060309140601032307090f1d0706020c01030e100203090c150405010801 82
    0x54051284038503000b0b507404c1400010290240715008004080b2001c043d02c007074403e1818404526124001d1850041064101c03140c20090301d6030004c1c80014810720001020329003607460000441640310f0416003400700e500450314160000081c0329aa00600e8252416446c080c01d1011440c01841c0074024059496a074600503010007907c06c06482c04258040c140050f000b029080c215082e1000340310841d01c180c14001d10103001032040c050801424843e880780d4a041c6e0400c01048041e920303000d0103900300b28940314000b40600301da0080600a06554600040c0d03a201400d03d8100c40e11046401c00081e44890300400c0040d4040303107203032040141c40aa102a0f88c40302c203142070600c1002d5000c2d00f0303100d080c82002c11501c2c8040d4003e0510440d06c44c50a40309c5410884010788400f564800e00c000b507007100f80d0b1021780354040e4000742c02c030001031802d496586086c4030a06080f0f030001d613003404050703200d005041d407a4101100b80d0611641402e103c9814076107400002022200140a0740d032104480480c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 236844397 1250 236843147 236843161
    0x5040b0103200619110f0115140f0607020d0c060e0321031b07080a050a0905100f080702030c070803030a0e150610030b032413050c040c02070321090e01060f08 70
    0x81c1e01c58032440781c009442c00c2ca02c14243ca64048d2002140070900c00c000d242e00001c260071404070110b0a6840648540450110b500c100301085d08134403c03d90b0040009140180007c40e03006011014080d991207546241c0106414140b8003643c141122203200d000c034440007000d1880c2019030354811083ca001c40710310001c4141181a03030243e000020848200829003064080e08000030740342c1c101d40b941d07a1500d20781d0707944208200502403074041000301c2c0b44501e110740c5491140c002158814002e004072450404d09680042c5029070b1039102d2141070300048180000c84e1081d02652101007042001080d21048410100421483c050800f52042800140c3d26011134080d4000c0d20704408000c05035525000c82c03030324103440c01700e200c0748034051103124000103002d0130001181d0031400354000c8000c064508824041c04010a100f07400f850551103150030003c00a20700c0020154000741081210182c01c0c03842c0c2c0081c00352212600036603032017250369005000b01e91b031050a265141d41c8514182c425500c400b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 236845647 1250 236844397 236844407
    0xc040c0203220602010f29010302160803060906060301031a091c080402031e0a0f050c10020a2006030a020310090203010f0501080a0c08060d030207080105040b0103200619 75
    0x880c41c00a107095680c11800b50868504441d41140d030250020b001d00d103404604c1c0300c121080c0304424035440603002050b407a0448035826514041c04103041c01072419044100312484c0742d1007a0300855050030000104034040c1070100704180c000105075001801d65045507100c0610b0044426900807040d41d05000845144080101e039030074942c849151110082e14180003451000d040320183d003e03110b00094100382c214644c0407441034150f4600940074150180c0c4e1841c081c000401c500784c650f0720075941110341c60340c1c401c0c070355540b02e5065400600046100307190030200c0c6143c40c282c3c000c1c122582a40c140443d211907048940c030a80072940160b403a682c0c2c1c070f14600140b80681040422510110010410b0445480b0540079034800b40c950041e95a210b0031208152078180502c040000c61510214003641000c602c11131109100703006850900351030324025801c4a001320740940e9800c45c1d1200400a0145da03061104901d0a40c03190030000ca4410b10100d1018802c4004600403900c4031106405228814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 236846897 1250 236845647 236845657
    0x19170f040f080f280f02210927130203060c03040303090b01060207091a0a03030323190e0319110a08032a13060f050d180b07050a020c040c0203 63
    0x40c204840e03e0f20f0080e0035611034440c04015030303061030861310070400a941c0558507952401344160b0052802c2c98410f6003003880b81c11403211a440390f41040c0540c41c421f41e1703690030320100c0814451100d82080341ca215080c1020b8809030410003d0421740d000c40f00962408034040d40e00201003171501740c0ea6240d03803070120000c000444020704030204400c0046500c0d9030100d18182118a01c2d80103214401c2c60441024002d034684080e143d12800000040000038000e420903070182c2405000790440781c41c96907a4002000040b00c0c15640c01c03030301ca545060078040324864052503503400d500640c18600003440c4601e81c4042d4841d040c040c0300900d582c022007403004100003c0d015030f1281102e501d9003003040200c0c40d00c060259201380c02c8a032000c079440554818500b2348000b001d044290151043c179119069407174100303580000e410000200046030418640c0d0007081504440d6003150180110315003019080c18201820420401000704800981c0c0b550024050a45510440d00002c28101c0c08005030315510078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 236848147 1250 236846897 236846917
    0x301030f020114030901050105150a02150402040e060a0e12040302100e21010504020a0501020115150504150c0203010b0301061d090c10050a0e240c0c0619170f040f08 73
    0x800410026585c5040d0851412504241c0e8000c240303200744100c2070100d01660300601d0050b40b11003040c22030b00810200d40c9400c1070010304001000c001d80e072045410600c0440d07a401e0655260211243c1504080004078000b09903c0080d07070406080d84e000840800304d0910b81410409007641b010541c5c0c5d036030803100b00c0d0341504040210386952403400302c078064013040f074080e0b209400d0648005120b50060103010f1b54259066100d440389414201d91680322010341c40841c007081020f000104800b258626a00740402d00b030749407548141d00600c101760940300c03113a45180c02641009000c0110707900080d000c400420405034081020b507250301c100c0e440c100e00c18155903800280d002e1103401d0305410000424090015507110566011004244001401d60010314146c80500c0c01c0c0002405150303401403d40150410709841e050307540b1000190164000081542c9440c0d240102c1d415415004010301240c00703214502a840c1d4070704080c41d0b07000354000500140c1001d250300005410810b040c402c54040c055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 236849397 1250 236848147 236848187
    0x1203090c0504180b09030a080103030f12050f0906281e020409061502120f030411030a03050406030c020609030f0702130603060605040617061b1c0509160303050301030f0201 76
    0x40c954084003c40d0284980c2550410f0703c25000c9030004001000712906e01c0e4840e110009203910715035044a54105110f18002040002181c4080d08055809502c1c01a541d04d03160038502c0c10410019801c1000180054141d0081c04202d00203801d0245038811042030512000a41a010690103000c40103401a00c1e503281403001038003140a80ca03591080e000e0780c28a501501c0300d0031801c00240ea40344060301d2144541c1d5401e019200700814420300540c6e00c07034400c000e1440c07901c0604001c2441c0c49801d02044002c100040b80600c002da038035204200d4200320510041980d800d245131001e44070712a101a00340e10320360006400042d502d400d4401002100e1450040000a5a81c180f60740205106d008140c40350741030090000d50007001c40850005001660b0240001362194040b062064078100d541d8400b041c8140542420f04000b1081e0340c02058220b0004101c03494040b0032682080c2000585000c403010312002400866844801c1e02d040d2030380582c0c040f10403031b080c3c00180d0310444807002504c1d00031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 236850647 1250 236849397 236849411
    0x3060e010e011a0a050306060706060503060906090123011503021b0307030e040b130506010207151101050f0f011703070c030f060506091b030a150303080708010905041203090c0504 79
    0x1101c0403419812074064070b40c404120542102003c90b203108400310b1000082d030501c0441c1062800c3e600400d91188154400036619680300c0c00b00782090000c40e880d81003604440104003080c1400c0c0100c400350703144041482c01d5500301031754000c141c10040c00b03409101c20700d04020203402d0703010f503049561603042080d0384074840c9440004107a0b207500441d408c40004100c0100c0385082d05041c0113614282000411025640d4210147c400040000510607811880f400c00c001a10029412a03401c4054a80d6500c0100768040c0c60014259003001d0020385006400b07008011036424100001415180581c084132003418a0081c010701e1802186005000e10803400c400000f000040c81311240070706d01c14081482665120802c21840100880d000c15407015002e1081210b05010b800640c5e202c410118000b072007070b43c1c5005040051480d41c10171008640300c80c0030301c00f1072a04034044a0040400d44024480e61030940d4820041c502e542c0c044806243e00d80e840c0e0000c03c00d808140d040034050140c8100111 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 236851897 1250 236850647 236850659
    0x1e050601030c17010501140f010c0c12170301151d03120c01150308040623030f060a15020a0209070e09040602040501030c170c1b0f060a0c0c2103060e01 67
    0x700304a100f00b1901d1603065401c40903080042c02068122070418600140341e020b12402c0c040900541089a410071036886100c070002007030750386982c0262500c2e60681056000a103404208441c1405038115140c0e01400104108604142e00f045004002c1c81c0080ba1035014500d80c0d100d2041c00380d401d542c107019031110b003800d00001c82d015022103480318000f4810f180c0079110750110698140401791410404000521400707005120344c280100440c02171a00140c92842111415042a00e2071000c6c60f02e10030074003d2914020b40080040d10048110303c3d0035000c1c6038400780d40e440d16030344000d008000d0100002c801900400c201c8a00c8400903002003060701d00b83c40c00b44000d50103070103140d010910308516680c5e058811143d9400c13005400001c6005a202e22500304002c0d01b040303403e075415032600890704840c10400d20941c0c0300364107a00003c141c0781c240400040c007515444100c0c4020404810032140118145000c802c000740c080800000a010320791000310040c15181e080150304d58940000004c0d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 236853147 1250 236851897 236851913
    0x1110307120902010e060f0f03190b18010311040f0219020f0705061c150f0f05060c0d08090309210c06070803010915090504050a0c0803090a031e05060103 68
    0x3140c04207a640849141ca0140741400320703909808003030300280c080900345140f400c048006007003c6006044031400e0500d401e043c0d01056104607240006d40e550000211450102402000304804080361880d8044180074203225090005100c007030024900902c0b000c009841d19444982e13141c0c0b030000c083d075a492004200c403203458076040024006100307681c01c0002d85c88011682c102a00c4000340032618000700c6848100920840c54030700c80c1844d176964094410a274034014460000d11002d030400c45001d26201ca9015013040c2580405d000d00390402c8000ca00c150302284000d5880c0040c00c10900540740e14906500d5401902c00c890b4011200030208105105071718031020820102c40d0488210543e408144640c502904400411001051005201d54241a004041c0641c0d403403180e19244e40d41c4ac8a80815148141d0b8299680c2c0c105c0d5440205115008030135070f0140003a000103614014062000c102e01d848a48000b510030f03082c407080803070a4980034075411700d0590844102c4009584900740501c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 236854397 1250 236853147 236853151
    0x703020d0638030106050d0e0f0f1609060b0a0c0302210c240105012a1109100302031f06090603051f18030c0201030207121d030a080d0b0d05011103 65
    0x82c1850070101902034075070300c1180d05944890307030703400d00709000c003880030018240c50402400345001d40b0004454a039020020480f01551860080a0640d141f004c40042e02600340c02040860342000020b00c42104040200c80b071080311840d04009800e41810124103005800484188122100c200c1d1148940481c2c00307041e0308100b107000c2d204503112464804006044901c2180440845840100107540c001e4a0400b200901c000c44207600000c0006000c003410300f140d10880e0b00c04c0141c1c0000040e0b01303000700001e40c0140400d90380400f590441d00065070ba40c90f01441d00c1c4071001d00301554070202c4d801b034010400030070b48110240201900d130314040e41c444034140504196017211250400c071001340da001d4001140c1e02a0603460380c40303086032800c89013000c8a4a007070b418182c00304000c400054007000b0080f00f150b456a121142c40c10000202c14202101d505200c0c426404001140003282668080b600da940804400180241c45000890b608a01042c80500203500c0c00600300c0e040103124000318 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 236855647 1250 236854397 236854469
    0x4030c080d240602010207230321180a0b010308090d080c010b101b02040f021204030e1207060806060d060308300c090f0406090c020a200105030703020d06 68
    0x9050b142d00d480301203080380181107000e040603040781e10302c808215a411140d4202c4030382d0f00a0742d00d03001e040349281000c001c44184444406940e40c0c100705000160044484146000d60080e2030307094210307200e0942c0603c2c103003c007520a0200140740344850f668100d100300a075034402d00f42910717550100841c2e4000d00c0c6c24400c942c05005031002c4106107500c40c4070416480400350701880f21640641d0240704c018200c031496101034070303030070080804100b04c0400a148180c3c070035130350600100040c4081c02041d042403c40300f0000d52105038140060340d003049032070b5480311082c2c40e2140c44054690001300038086a074006404200001800c06041907040a1f48981c00b4650013280400c8899500801d06508100e503403100050003070003c5241d61074070041241101c00000c00c0030402c103880f41008412500700018401c09a8802c0d041c100c200920400942c0c100c0c0c5d010081e0648e500300420010b00244401049081059400160201888259840703900600f00e860080d03200703040b1244035103010700c006c21611 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 236856897 1250 236855647 236855711
    0x31a0d060e060a05090d030507090b0f1c05090a020423010b0309010605031c1d030d11120310050904031101020f220f0b0c2a010f030501050904030c080d 67
    0xb885002060044034001c17500c81e0b009080101c0610801c03070041801414240c00c00040c4000055180100d201406202246150483c0e4824894000000f040761400394910490f08140401140207404100c4551894055402003a02c40a01740a000685c5950540010b0030100200214960281601035846420391000810146031500105652000861010508600ca204d80042c145200b6000405040040710249081614500000f4200b1000c002440002000200ca0481d5444100320b269220341440c5980e910358200940d00a1a81440340191801514884080340030148594107030001083d42c00c00864032181e007181000c3d41c0b41c0c0000c03200c0e0003001030f01040c2c101100b944c0f8043c2c0b00f210000c0c20103100c11440d05082042c2500034100a09070340c040c4407480d510344640751405c281e01c05c2082c2e5142d98081910300000d0040c401405a1908041c40d040051240e40c603402d40d101d4216401d42065900c51045250000242c4200f0070000701680c1404900880c2c40303e10300c42c2c443c65010030a10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 236858147 1250 236856897 236856901
    0x5060403090b043f080903120c0303040f020d050f160602062a070602040803041a04030f20100810061107120f0b0705091e0102030a031a0d060e06 64
    0x2d8400340c01140a40e0280000b42090611503943d003440034841d032100158840203c40c40b403640c60307044c0c60361240140c54130040028150781625040c0130060380040740c0c120040c103144503500e03002da13640801400100700507207000c0320350107650795016424165580701d03040b94140c81d0440d40254540c0400d1440e40d4001400420118110303002040715480741c1c0c03070070410740ca4071110542c4114032014140c00140106104220b5035011a00500080c0040c0c00403200459640f4a0302d50800c1160062a8800d01e4450040c08144009040c0480441d01260485206d0040d100c044007040000c03940e45000f03a500a60292207818503503000301501c3c2c07140c1900084000c240340c0d2000241c0c0c140b40c1c900b0301510103401c055000c3c405241005100081075000c0c0d112201070790400d980300f500480c000e40b0034901103900400d100546140c036030001e680d494401ea071070141404810300040d45e40e000745007414007803541792601c0321007410134680c1c25a03112600600790300d00b0303820b42d080200090014401e4135170140201c00c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 236859397 1250 236858147 236858159
    0x8010b010c12320405030c030c180c1201060201090209060a060c080f0d0203010e0114010c0c06031e0609140a0504020d1202010e120d05060a05060301090c09030b040506040309 77
    0x2882101c07668214054032600e04680038201c9981d00342501198020108142d0901140d00180384400b40b0f040c40801196a50700b00b1040615194440c101c03d803195000d00250121601c2e50f124480c450700090403020641d8a03450360411084c060b0400c0c081001190200000d44590305400c803041071402607032246c209071206410321003450064000c5001003800c99030082c0020f6412402003c1d1040300d6045503060001c80b0345840305990083c1c3c400551003201c0401405940070410400a2100e405d003003040507081c403607850710780412040c41170380b041c507079542c81b4181c103041001d030040a807402e6044104079094966288034010180c440070105407100300d20005041050611800703020702d400409402220045a0301d000104d001c0c0c00d0408115500c0c1c40031001c2445080295290a03d44200c000f902c44000d921000103c0780002d01c0342c4c1c403070070f8201c0e4100800d4441208aa05694810b00d001c64041003003101507d6084035544010801e0a1401c108014000041501b41c041c0b4404d5a0702840d0542d43c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 236860647 1250 236859397 236859407
    0xd120e0a1217061e0411030405010e060a090302070902070204020c0709050712021608070203030c01060303050a0f02160317070203070308040302031203041505060d020d0b07080108070b04031e0b0c0408010b01 91
    0x320300e0307604400a0a02d84e0340764801c0c0d50b83c00a00600082c000308500c0c50981995065030019201110603a4545c00c02d10821801400381d41e40c07184610300100100d101944000707503030705042d1041c11601a0f0014a2000755216501200c80c080780e00b008484009a031400d4407801014111080400145138415040c02d2540a00842d11801c81035090280f04070a142c5070032910790700400c401c0f40e040c8010403480d21070803401e004070340045020b41c86440d112000040040c020295015810045422001c4421800f00d49800ca0000342c070740085030071200340840da4014007079106031900a0740c10b00c5402c04c000100b241e004010f0096034825070603921122001c0c40e0750881c9000a4a000f080c60840010300328490032141d20903503009000801e41d454461003031b0041845d010340e0240545c0d49118030410170401c0c581040001d80100300941c01003015500e08074002c0c1d014000c1d80401800f41c040d02054100e0040840d00482e400c94200c0365040490500e10000c903c01d0f4010b2080c01019420715403110400d601074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 236861897 1250 236860647 236860651
    0x1803051e0d2606120a030206091203041a180f030912030319020c01020906043203031b101107030206060a030320011e020c010e0307050d120e0a1217 65
    0x3001c0305042181942e00b441000b0001001107412007507018505024910800c0044203c5000c3d4015004900301401d072035061008100c044540d4030400c00510001541e007118030581c183c4c00815061403900c40780901111200501030018091250707401901e0702c04008001040c2080003119030100c00010a50030a0b100d000c101c0d9031084110500d02e00f903094403210340080034140b41b0b0b100014645001100007800c00e4010381c00c1610f0b611181c4408140702c100708031684606031b445800425440050313100095580c40365210031403c0c4085c2584d40d841c0307007800300100d015030a05c0303680500c0b41601c84400b5820b2900803800550040c400c11000c1005170038100d002c801641d400d0382d2120403c00310a80105440c0c0304903403d500896595100d503c1000c00c0012a12031404120744015076101d80442000e030039034000245a99503904104900b00000ea8000340010f02d804080c180141c01e0088000740c08000c1120040800980c01510303104400c102d0a08600e030504039080e10b0380c1100380c1e0031030888090000c0c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 236863147 1250 236861897 236861927
    0x6020d120e0c06070f12080402090907031e0c0905090c0a090c05071415010e270a1211030a0504031a04050703081602060408060a0608060708071803051e0d 68
    0x180d411145803d102c1c0084c08042d00514900d04200c0195480c0f80e0310050240c040c000140807807090100b146000a00c41f0340203011100104030650541c0c80d80c0311490150451070444038540a0210100035100759910000c00ba41c40c404c01c118945a019680c0b988001c01540388210400b44010824445612130200c40250f145e0b80d45007071050b5035603003a88803a4400010003030351141c60740c0800202141054240a4054850706660506140d0b11248840320300084142c1c000346030310303200c900b40030001454070341054000610300141d1040040a030784080c2c1e03080c40040c081c04009515100d4542210040003241d1140c40c10100c0c40d00062150404204143c030020819007264001308081220500540010f18010b214640000460f0380000d90b680d0050b40002090340044081142400062041c04d0050403da40904074518183d40010b087c0d010042c40c0ba0103108500c00284e075031a00202942c005140d00c00d044400c51450000403031840f501040d0406014866501e5501c0c6440c824800da01100031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 236864397 1250 236863147 236863153
    0x80601050609040e06090d0f020102040b160804030b011e12020102030306090c0f0a0309060606030b1c060b0d03020c0f10020a080d0209061b0105060a05060405040b1906020d120e 78
    0x400c140400c101c5038400c510180e4450b8891540d544400028881580284641c4d4010706800010302c030043c1401031916818000d591040c00b00b00482c0040b41d040312005685041380c2d481c0c0182c2031034404501e0040d5040030f0814010400003040c1910032480d42002c540031200060491503440c000740c00401004200240141c00c14170100d401802c011000a40200c560b02c461400c0c480012510100781e0801d42d10980002d8a444d039030740c00c2c49058800d20001c3d00041c0b4003032001c100f1180100d44202c800084954001213040695818800141d200d070900d010000c100415001150170025695502d0075400d40c4070b204000f08210144c90104842100440c251300640123a80480d103d125440e00904103225026400304141d5405550b020b0091496851044500003009010b0001e142140c1009050f80c2c06100001c10500141d581c1100f9101203c4013101c021030054804000300d03514510300d41200c000c0800c50103001ca41c0030780100b00c1c1c0361500590741c2c0d000700e200421080f07031003690020740700205560 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 236865647 1250 236864397 236864399
    0x501090e07110d021e0601060e0d031e0806040e01060302100315050a030506010e010f0b070f0615081e060402060712110303070306060906030c020c0918100c0f0504080601 75
    0x2a00825880d94010003038203014030748608040002d402c02c6404160b860050b0041d0040040d0340150480350281d0006440040038035605004014019030050350002c2d2050300e041400a040520a900400a4402504c10300c0010740301100046c3c418070301501c519208a00704010070241410500c603607801c4039002010310b400307070b005400300764001d145903c2c030040050b180707460128040c0c90300140c040c0214800e10060007690705d4803090f0380340c440040c0c112280104074103404120b0b004c086800d07070b9999500044c404100d0000f82c940000108644200c040e0a042e18100009480d0008159400030341c0090143c20b010f42a210000d0380c6030101100c00940c800e6092008101107030038415100800392050805100d00350b015021140f968004540600010386c45290500c049030303100da1104002c1c0341c1d034203013800100000903001c0d448103d501c4006028100c0e01000402e44400c43c80002c25240c100d205846d6170504640d5024044c01c001c21081d80450b1501e100c88071124030070702c00c443c120380c1c5100140804c0e17 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 236866897 1250 236865647 236865659
    0x1204030503060f040e0609010c080108070e07050904090c1703070c14030705150d0b06091806040f020a0c020a050f060304110103140f0f102106060308070302100510050109 75
    0x154001404083d00310200a079940c065440e00c1c40380040c0d148154000f13110501d0715940392425600e1100c0c260f810040b80c1030040108a10000350750064800c40002c3e442555036054080b40d113030049050b150343c41414120244184120300c065001514485103900507140c4400111680c1c03885402da0042a010150404005203c001c021704640d0300001816100c03082c2d61040050801901070850702d8824500191000c2e05031100d2080a10014082d0f64041c2440c81400001f4810181c18010740041c001d4440007490036900d50380803604658140c103045448104001e0020590503601c401280a48100e4101041d0b52404905106045200800080c5180d0311a522031017452032515003103051580740c0b025039500d0000c04002611030202885c0401e040d00e030807050040d000c88041c04500312251858001e002500841280410141041d4040c170304000b0309140500c001e080c80d0b800581070b00c0340402c1c03440803d640840c104165180280084c8400e0320b48044a042e039101c0c61103680d001c03481d40c00c810462 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 236868147 1250 236866897 236866907
    0x50f010c0e01030e071d0f060102010b06270a0f03030e060c19060b060315100314131109011401020d031802100e09090105090f0c090c07021306060f0311120403 70
    0x322103c03c2050300c00c6151b840c02003050281c15001e83d00d000010036410028410300402c13516500c031000b48000d000c80321126005c180300b88107580110340944810544041e443c2e40100e60312544030000303403d14003038030781d0b0300c41d801040c0708035001c2200043c00000c1c141020b4078003041515403440c0d11501824565120406001509000a00455450742c03116900c0925a0300e10028500c187c0581c032005881d9100328003000440c10106420005140ca401c07904a6010b0a80c010960301800d249003000340001d040c2400b482c1e024010003c0b5511622070000483e42604404449204901c00c3e02141c2240d03600d090b055042c2c0d0300c6221040042c0c5110741d00d1070050303d00001c0b5810243c400d4207102811019010204071100001c0300c030f08a1a80d1264244107011208120300c0703500004010151222502050000700480b401410981c16004003007103070015555808a045080d2400400401c0038030359803480500f003d0910f03281c140120740340913000e00c5400040b00440d541c5034110504190143c0c2d603a80d098034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 236869397 1250 236868147 236868161
    0x501030c02190309050108010905100b030603070b030405010212090a050615040b040f05060a17030f180a080a030f0906170411031b2e050901030b0a060c050f010c0e0103 74
    0x10031880349500c2c0045801d80c01e000c0c126010f00035a54036031143d04040014051003010b82c0f01e40c1840d4604000c010130003a10358600420344000b4583d00783d485d15120b0010b490841c5030380055007459400010b10081140c1503000340403040c030001c405412641c0d9850031a488038480750020303150350802c0c0b0004420001054018000e010700801c0092900000d1000c5411152800110b00c0303414ae8402c244201451f2009079680100401e03100c01e940010720042c21500d0740a08466900200800b156544001071100d02c5101c1010003c0e00b04640d0603910b1202c10381d6810b07850380581c0450f400a00c0500c1281c4240003c4040d141c09803540006400c000c0c9200100c4c04000f13009542c8611502c010460301e0b035003403000e490511104e0955403185a4400308200400c07072040718613024800c20250711003200030140c02c000712403403480c200b650300c0e54803040068001d0214580746641c002c0e140c500c040f80445d040710034603001c0e03402681210304c0c0d0120325420500300c588600b108004189070540e100340640c800d8011003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 236870503 1106 236869397 236869421
    0x501050411030c06070803060301021b150603060f160903021f020c04021201050d1a160807031428020f0301061814040b03190605150901050a050103 65
    0x144c41407091907401080b014000c0005036042c1c0d0294140d50b103400320307131400c0801250714408240e03c2d10001110b00ca1004d140501185050a00203155071050031195a0400161500200881502080c20310380c2c0c1000000000800140c4035140c5800c0c001980704180d01c880317110f188001c0e081140c80c1d6285c82c0030701c2c0b042c84914215855548601e044650980c2c0181c0761004509200500b0741400002e08000b001c86024030071003c910710400040e4019650b00c1c01c03010344035644214141e40917400301140708600384010400448d10b5000302021402200008030461140548507800d90300024842991703a107001c001000420f81021100c0141d028010990200501b0200140c10f001c808292090007183e0762514540507031010090415151840d6210504070451490102c01038503007115410102041054068004d0411100d054140c40c0018401984582848011001000401c50790 = true := by decide +kernel

theorem cover : BRFrame.Cov 236690647 236870503 := by
  have h0 := BRFrame.cov_init 236690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 236690647 ≤ n) (h2 : n < 236870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
