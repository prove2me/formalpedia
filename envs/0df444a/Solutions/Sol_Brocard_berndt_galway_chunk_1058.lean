-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:03:05.419666+00:00
-- url     : https://prove2.me/submissions/8739e8ef-ea4c-4a21-a283-9ec07e1ab30e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 190107913 ≤ n < 190287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 190109163 1250 190107913 190107917
    0x90f15020c1005060402090a1512020702220f05070513080111160f020a0e0103022409190803030903030f0f0402030a0f03020c040504151409060f090a0c030c0f1401 72
    0x5102510b1a00c00001c10004000d01e80040d0200402e41850380c800e25100050a4080d42c0703441d0004201c0c6000b055508001081550b130761042185070050380e07031880d03015002540b2003800c50324030f0140d02c0c007078014201110750341c082c260605080c000d50a41043c05800c0301000015400c0990703035101b0001d42079460041101c501c1d10010002c00300e01046000d40301803940d019020543d070341ca01c194045403c2c081c0a130312851010400398014070441c0b41500c52084d0040c092202d40319001c0c500404007080d403280101070b82c8100b0f120b071640025104440c0c1501c005009080c2603070348070703d000903900c1c0c0c07241d00c200e441016049108000800300c4131101c22890045802038010f0904a28513035410f5002000050240c0035445004c0070b1140796070700c0307004052080d4403030484108001301025440054072030b28823015070035030007480070031800c56800501c150707100c0d4007a49070241c03a0300d03485d20550a10032103840103040700341d90384004001d21101050050031a50b10f2001c2416503a07444903000f01000d061801240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 190110413 1250 190109163 190109173
    0x91005041a07021e030301090f02091315050607111f020706140f1801110d050306100e0d0503042102010807030c020f0a0b16090b070b19090f15020c 65
    0x1885070080e0041540c000381a0044580110407035000d00740c2a0701600101c1e21581c00003005202c01c2142c0e01501e007540d00c500d042541014060000102d0240b46c4e9503899510325510044400d10703101c030105031300003460080e00321980d444503410000d184441c101e00c2540200025480c40b000d0352142c407147c0355802011b6025144150524400721051036044140061480050003a189000100c0c401003222629500c44200b0b01d0304184000361109040500104450300198a41d0400681160031030b80e100c1001c80b080d010380b12044105881c0002d06c6111580c0100799100c031170041250020040040d580705203280c81c9003102c4050381e00c04110040710002d000803046030108901d0ba000390810086441a40151080c1d5280416120b1524810030001d4800e0308000040c091500030007000c8290740c0e4140e01d04400c0070303410301960401610a24000030400208000061110f202c801315903001801c3d00001840608103504003204000f801800550b03208540e600c1c0320301610360700c0c0b003152007482100010301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 190111663 1250 190110413 190110443
    0x70503040308130e010815181b04060f0e010305011a0f040504260409060e010803040b032d010e0601020d0915020c030f0105090f07060c0b04110307090509100504 71
    0x5016500400c1c150a0a82842c00011500105402803a40a841010b000b001201c410344a9032400007c06461b0300f0107440300490b000aa000003044080c1c0608000250740d244950f40e1010038000d00065000140c070451540022501d00d400c0015141200d00031002404421806120703410000c1c011280300b40d001e444544402030f1802c10360800e6600a0107a00e803501c058200150001c00e48400801c44814210b000034207201c6001507110300c102800c655400a00c05604101742c4e00d6592286000d5071250a40100004070000c1c1f0b1100705460741c69229129456a613290089100148401e00808000410044c0050159440040d039002d00165a07660384018520308120361220301503014280c011401184143c9800c0e84040143c5120301c0c045400028141c035062455a013084208000e10060303401c88101000f034554170840c41405290002645000c9445914040038001003005040d9010700800341d000602c1c0455502c524466120001a105c0507048a00c2c0d000c2140e2086030300500c1c400102e0205 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 190112913 1250 190111663 190111673
    0x209010207051e0a06051b070f121704090b010e0303030f01180207061b02011404050a0b0a02041806141c26030f011401050403050c0928060e09030705030403 69
    0x50200091000e0348048407544001080c8130039001d80040e00410740004244185a20310391800030440c849001901e012820503081d14809130461141044581d168201c01c001c0c005442949094482105c2d4802e9442e65107a03188400703019114a0f0070b022138107036400c0c61070904001c000c6030300c12415040f0300d80f241da007411382e400c254801d0000c428486503030900900d40020403a10501c6592869491080308501c4910402400e44041072046030088803254241301c0015000114840ea4036844414001c040da01ca500c0f880c024000d0b81c1c480c000c00144031100705180007d607030015040e01c0488040750340b201c2e0300f1380511040d40c4003031420141385134210741c4450120700a400950740d505103519165440e02000c1c9282c514903007040e81c00c190000780c0000108448249040300010100081c20000c2c146860350310781c40c2e100c0d030381030401074000c01d21031000400e072000d43c042c00c0b1300d042e00c3c21817600d840b00d061503c100c0040004d405009909070141c004541e080761700106456040b03600900540c42c260a550760 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 190114163 1250 190112913 190112929
    0x4060e010c03050f040902040801060803120a050402180106050c011b0e06160f0b09060703090305030f06010903050d02011508011406101124071706220c0207080f01020901020705 78
    0x8141c08010084c84030048903070a000041000386103694000da00c840c00c00300d405003100c18941c0940c01c0355004109464524000a031440d41c00722101a000941d0ba03580c0c0080382e260000080903030b0750040390300c00110390701c0e4001c0050003000352140001c0141040b10010600a0170b01c0003401400701d0110011201c1c02c1c0352003401054031481d96644122151116580c191079089030301000c4441300d07100c0b810000f02005c01c110141c0d12003c1c81c5418050700c0751a1310064854400034000900941480f800207040d82d0140c006000159800011211491408403000703000b46055940d1403040d001c420b0000552390302c14081d05031a00f00b5414400320781d03120fa800700400a085440e401d001e020030184013188044c000d208084148446030f40c94069001010400c0048001c001d0041042c0040c0303640540501060b480600e43c4580e00391240002e0080460900b000c03140c40d101000b840b141000581c0141950210302d0303c04442c020800c030f618031900000054207074025103620342c2c0160f005141c00c10061800c120 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 190115413 1250 190114163 190114187
    0x720060612010e030307050403050d090b0706020c1507020304090b09060915030a080406080f070302070c050907030e0102070614060901031203270615080705010210050702240901050c04060e01 84
    0x1c000074001155411060a54004942c00000f061005c942003061040070f0003202c0600601d45030080e076580c100394803e02c86001e082000341005501065102c9400c8080000c144c3c00da210f0154800c03240341001c0c000350380e03a03c9809044201410001000202e0410141c55802014003e01041170360352034030b02c2da40d43d44c1884a41140e140c8540c400f01c1d004108a1070044c0041c108a81c1c2c4c0c0e030140d1802170308000110300080c14000c2094030410149010134044c01540e81940d400b21480401519080400c80180024413119200313940300180e50020024030364400e140310074600381000c1041c0d40d004100400ea040920002d0400d244e580c00a45189110390300c8810003255030590b03c901003e008541c2101c0512161781215070503520248009024030076440c0e07100910310500103100c19810400001c0d2122048000c01038155201c001080802c1e00a1042c1c00c0f00d0280640e040d40043c140180c44e40c054403082d01e442e03546500c2c00020a00e080c41c00c0041307800780c0319191649901c0b080380d140119400b64840c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 190116663 1250 190115413 190115449
    0x6030515040309031b1d06030a020111010b120616020105070c06052a0306040f02041a072901090c02010c0c02130603060612060e0604020a031401020403081207200606 73
    0x81001c000103034000708005d001520344219810396828642d4211114a01c0c844891005402408000c096a000034071440f8503642841c0c4250200440072903103001d0407000302c2003913110b28400070a401c08240054014841c0001920100d140d0b20800d10036422502d09030344800014191051540116072903400007078000d40c19240c0d900c0d40c1c8090011f42c0720110f46c006000001e101c000401d000d1985001d000d88029000c00c2101189001e06c0c02c0c5800c030340c819200904007407504000c6042e20a11012160f00e10310b150350b0806414410200030b81d07100c0e503034100f40200d804c1c241ca0440c0e5101c0c10303881403140e05c04410864031400c084429903020040000c40545070081040d845030703030210000d061400741ca4018500c0b002d2890482d846494007105030740c00030804599981c0000100800740c0e0b07403000100c040383d8002841da640c20f68544030b0140607115a400191070100c0000380c00c50340c46409000e075841803c56544214034206c62003001c0160035604580428030390300c03a1010840b1480c0600840c50805421 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 190117913 1250 190116663 190116677
    0x120c03060f3705030115060f030e030c100203060a0b070503030708150a06021b180f040c090903080601110a15180b09070e0711070303122d0f060305150403 68
    0x501e81ca0381c070010750b1048841d4101c50b8003404200340e0900b4080c0400003044c05200e09011801d00c40c000784072444191600c01015202c01c2c02003880c10b4140220b4160050031401e03108a03400207803903140030f9482500d0325401006505d40002c2d030840303404191400a0703404001b8600c0c58940314411280c8441c00741005180d101e6000380656540c3e1403000801c002e210980180003c82245090364170440900c2c42c5490240901000c1000e2011804021541c0004200c107240410f45903030400242048480c0c120740d01c410b1410b02e40f803052680121500b40718040036a24468410910001551181d14100004000c0304c40300c036000d080790445801200b8103034030b40da007072099605c8661180e030003142080c1e40352280e80d0015a820b01c070300c84401000c2e50384138036141041c07400707030708410203c0d0f55844851002800b001030052521900c1e002a411203921b83d01c8891f503022800c8c030310344080f001c1c80c0e601201c1601c0b200d103040e1442040c810742e030040408403500100904543d0706600404681c0c0100100220100102 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 190119163 1250 190117913 190117969
    0xf0605040f0603030e0414010306110f180405010b07050a06091104020409020910030203070804080306061215041b021504020a0f0e07081005150d14090102120c03060f 73
    0x55205084020032501c5020030418518207014050440400c4500d02642c10600003000c071507400d00c05181120b80c0305800040b04084090310322914060664804261900040c240d01c3e140108820900c413034004860800444e40c0c3c46c1042e07901849401310050454106002c114040b8817a030f40810701050296403014803c640c010000703401c82c0d2203a0420b004a55000c5080302070340c102440c5810000714981800c44c42c5040602018040c41002080200044000000103403681c4403802074450000100b0140340c4941072001d010240010245071082c0142c0c030304003081d209036007a028000300c04400f41d00500070010034040007490755100108140d8010142c2c820020311107904070701034001010140f00c00071042c201010f004052010247c800d001c078140e00e403000d100d660389004011203465140c4014684e80c28030803a07100050070714a40c12803020302c2c5a034204404020107400502e000981c1240340c034007a5030380c500101550f00090b207d803a00300e21342c1402caa4143c140390700c1e10b05681c4003040a5009040e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 190120413 1250 190119163 190119169
    0x102012c1b15030c07020a141311030105010c06090203030403060207140d39030801081203010e0606070305040902030106091a190f140403050d0e1903060f0605 70
    0x1824540d042010460061040d03500006104454088204000300c0c2404008440022030710320102c030504488403000070128080403403113002c40765803540c0580102c00096441050110b40c19076652020701a0307180c111070100581d22442141c120013081c1188508503400d02c40112462180c100003140c1c440d9480d004900507a03003c10141c40210f126030800740e03a44849142138020480c09200c901c120707a1007030b034a414038103401001c4500a200302c0440e0352812029900ca4121203c00e00211814041c101c80b11002455800780c080d9050fa41e540c1c1c212890007071741c2c60900c40a840244122020080100c0101c2c08518019000345081402413a0040c2840c0e12454140101e074401c1e8130400200c0d491810801a50012a040e0317174544001c0c0c0078580c2048010421544c6c0380403a00c80d501c0810901500a100300d0340907140107007000c20074000351a103482d2039240c25039484140c112003801069080810f080d080c03900a4441c1103104243c6040c492031407455590401901b8040d0041000b5915101c0104081d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 190121663 1250 190120413 190120451
    0xf120207080a0c1a0712050706142403070509040b06010203040807060804170304110108040203030c010905010f0e07030206040306090816080712020c0a3c0303082211010201 76
    0x3d004900300d1220364601983d0380c000381500d52090304a0001071002d00c000ca51040c6071003007801054100750795205028030345880200406044080c1a204040900c801c1c00ca0a500280c0394041c9201e90f811107141d071600b015500c110510032254441030583c00200040d600c503c1d040d1b0000c0040c01124101500c0c0c0c0d0203541004042c1e001180083c13000010001881400070b148000ca00e55001490311794181038a426000c00c4d81d81d5503260502420401250444d1010030803a5654403141008012201130ba2404a020b0030102e82d40600250400f031058030764000100c2da4030103c3c0d5004082918051850781e60f28081c0c01117940959200100707000c010b0090a60108800006125120b910b80d00c40c0c00c3d1520320403969804401008541c8020b01d58411626083d01e401c00b40c82c40400101000c083c02d0840c1c1e00780c1162440c10720706111079520700ea01210400e42006041e64401d0720754480d9071f62041003140c0c3c0040710034451a940760914514002148005c80e4039031801c441072002185010020503084421 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 190122913 1250 190121663 190121683
    0xb030c0f1912150207210e060a0f11061510021c0e0118260f0a11030708030a05032706010e070905010309020a1512050a06050405130f12020708 63
    0x5226140d8584204207240381c402000c0d072443e14086042007426151402c00c44651704044113005e0580e0501d40e8894003802ca184080d00000f0311a943eaa040c2480061400d0000003005000c94010303800d8022665000c04c9007485408221440c8401c4039506013003141c0c140ca0802003100303500844c2800d15a10241582c4c2c2400901d45803140c41d0440c038600001003030540001e90309681940241b23000d000d002d24505407102d8440842c0305004440c81d510044070305040d0a40341d00c1405110b01c0900d00204845010002e031030200450503180065900c80740f00fa10383c400c3d4220640001c40800006680d0108094080f10b08285810a800400b4008649601d080e4003a003280000d0031f5800100f0103603981c07007a400c0303010381000c0c641441003402e80d5020540701ca4182c0100d8030f8520309a1407851007148114030101030070300155018446420000fa5000c01006d40d80078440c00786081100003000c0c1e20300b0001a032102c6612000515400e00241c680101d01021248035034218042c00e0b400040e80309041045080e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 190124163 1250 190122913 190122929
    0x509150a0e01120b0609100303260108061015020a1502040b030906180a050307080307180b070c0e0105010c35130e01060504090c0201090f03020604060b01030b030c0f19 74
    0x41660075003425114000c00601c2c17644946005001c000021826201e84c00440b549400c10002686100f81e000608c05020200d8409910402000103580c001c00140c55000d40013000404803159111044407031000c0680c2420009680700d11b55000009152200d04aa4900011401802c1c10340303031000700340d40da401a100e043d107540c0000b0034801160400410084c2d40001c04006041e001400d07a03030740d038984c0902c4402505402001c00002d0b580c07801040b00010b01111101003401d11502c03189442c0b960341101000b61403010040401085800304495914107840b4140c440b41c2508440395100200310b04240c0c204169011098800c0514501e003900d6101800720348466581c031620b00a905500c0080564002c4141e80c017400b004114042e04402110305075800400d011402d81c01002080e070142c0f210500003401c580c0400c5244086c158003082e001c0c0154483c140c140125290000111b0559122400341c550540222110038098034011442c4c5000080c050000004180c1e4000700c2d41180c40302c2e50101003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 190125413 1250 190124163 190124189
    0x20a06110d0501050301061a030603010f060e010e1f0504090f0602030709232b08070b181204050409050a150605120a08070204240602070603150509150a0e01 69
    0x70700020140140c0d40900401d800810102c0e241054820070071614041e101e400e17080000c0411a20348081d08681c501041283c02400a169502c45c9401040c0d42485000641c400300e1020030170807504101ca15020200c82000100464200b00c00c02009101040044032008246401480040e6460014620034a0203840315079100c1c1c03130110440c00c601200c840540301414194400402540c901d00c0c03681c4c01890620219a00c501d04944002044517501320140c42950b020402404000d40058554440d86a840080c080c9006280030555161141040c090300030100740b0041c001800c02da8001c4148030700900440c1d20520203500c694003188804855020340944505003408941418412402c0c00d0701a6401407814951170748a1090601a084c0d000380b08503100d070301285c401078007503414480b008080720401c841c080c2d541c44065a41c640300e1140501007414441d4044c00e0340d403241d820b08119007001e041088203566002c05010b40360204045d250b4060342c0c1407004550150620951400303400088036000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 190126663 1250 190125413 190125427
    0x1060b09030f010e0604060b03030d02031320030d181e031b060801030204090201030605030d08010306270605100b07080919270e0f0105010f05040228020a0611 70
    0x242c1005881d5071162a03c2c0c2c10701c02c00d800000da00044103640181c009100144030030002000070308610860713519400c130354008401d001103481542c10314503046209280500070320b2019844003800500811401d54580c022141c914007060040100c0105980030803901040e05031a0002c0c2c2c0020090100e110031046500301c07080c010042c0302c000003181480c1118103804042c1ca002002420060305020082c0203a4540c0d081204590098110317501800004050340c0e100540d0b08802000080e00b44800e03280300d400d0407100c02c0d1140341e03440000e03000c0c644460b070351813030440c50303200c205c06030a010300400039510090400082c0035100001521b100c071320401c0d02c140c0c1c8600302410000000790401c0240d4400360141d1040011403500c0035402c4039842401c1d46080351101c005140c10013031690700e024400e40d0198142e41c468400d810342c041816180c420351141107440c2c9070001d0104038080c82c05441c20903404001800703030f0002c1880b20480200d59920440751480207039581c04041d10304110400040c1c83c008501c2c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 190127913 1250 190126663 190126669
    0x9060324060f060e01051213050c010806060702040506031e06040506010f050105120702100501140102120a02030a081003060f022502010203031308070503030c07170403171b01060b09 80
    0x40300300e1210520512580707051006202500c900d600c075410521810103036029880c0d000d8410364010880881401d1014503100d134046e54050444842103e8030302420400e801258042e1700028040d0340081c00d1542451039036820702c001400058241c9a00d031180d4264541a0321013182d2020b8007289000c041c21450070a480c2481c5000d5040c1c200c0b50a01d14500c0c01031003140da20a0940d406002902040e12150316803810036814075061903029999542040c0002c2564030008030403000880d000c0e03088078a5040e540d00d1099981c0941d069020060f0010040c0500c050701c20000c1c150000a00c8402d0314005599a5680d81200ca020f020340304c8494001c98031000c1d2103007d107409490141c03a002460511199940001d4682c44002c0000140701c00b090000c40a12a40030255954941c4c04002c80b81d8904142c0c0e54240300f5000090304844084190402401c501809000c2c0c1e0100c950003030250350300c8240411b0030080d940014642e0741c0c450145800d038006120007400342c88001c120307400403030f41d84030b0200c0f041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 190129163 1250 190127913 190127963
    0x207020415080a1a0603060f0c0d06170c01021605040914030c0109020909060907030803130507031a0606160222020a0305070e01020d021c05070c060305061309050d1404090603 77
    0x500824500c04c0c404000c5941c41c04151940e1114100008443d10354406601e40b02d1401349290a8030b80718a030410100e41c50b600e4000120006072448121050005032600481c0e403034803180e40d4802d000c036600c04204624141038100e1003407548a00c442c454210003590000340356800001d85c072b42c03440c0c0d1201e00480c15400d102d0082500708c2e401390003030701140c9810700100b0307511039951100500314040000000c081c2480c0300d07007a001503030b881003d8801e034540d41d08040c610f00341c0c00c01034546100800c001045a070702e01201158001c4425010039200c050f0769400b0000c81d9000010b81500e800f5144010fa44d03100050301c001c10343c1c2d000035100001c4a00b80064010a40c81d5082542c9056621020003203080640008220f2500c0320601805104c05218650072503c50107039482c0108200560380d4046006500b60300440d2003500240c426000304a5582091410303203211040140c0607402000664803401e214180038054102041489450035907204107883c101c0350241d10645422040882e0f50011220f8110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 190130413 1250 190129163 190129193
    0x70c090b010c121d1002030c060c0301080d0309050118060f0b09060102100b0a0806010e07020d020a020607020f01170903090108060619050703021c0c030f02070b04090207020415080a 80
    0x180104500320ba55541d01e07106071071454100e091040c142000340c188010b000000101c40f034050a080070a083c1030402179940e40190701107149078000c51001404111150090f03a040302e0752000281103002c41b199060700100004001500d50f0754890140440340fa0007960748020061043c01e00044d144044560b4038102c64402000f40d105034041c0050103026a4001104004d440c04510700082d0114543e000681d0800380398031200c594021400001a19008002040c0c0300e0030031a020340d280c01403026000c03600c07408a140005e40c4004c05203c16405418481c00810105006052416461aa06509599400c011144d0040795400012180780d1542e01100d459000340b825070360a41440c040001401c40b48801d11030f01010400c01054100505200b00140100300d1050092a90346120211005150349080b0006402207040031600002861000460360203c1b68408912428a801c24280074040d500c101802da0707000741c4481d030610010300a290010014054000102100301882c5000d0000b065400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 190131663 1250 190130413 190130417
    0x10305070f090b0f160812011223010914030a0e01080907050f150a0201061a0a020d050a0302041e05010809070311130e0f1609060f05040c05040308070c090b01 70
    0x1081c0e042606811040103026107501a070969141c9046503841000d42c09482c00ea00d80034842042c40300184032241000341102c607116620465542c1e242c860068003024a408018901c2e80580c420707d4109003148010010050058004600d901c0140c555400c090028280307a0829000002c7d004003854010a1030080d035403003800e0800c40761400c00000350f201c441a100385801810104910f004603920010010745c0030f0f0000c0d10701603c07039040030301c020700800d150b0280d10000ba8101c100c403e0070701405800d950300340c281c0c4d90081901504140d4219082d400c0b000d240028180c00303100200c4e2051304644140c100035101286018918a0000014481080900246030b00c0e0001034007840810f940d140c1c0751102c81c1c425140c0e903c020300c011884100802010340130070614060f0495450b40d540c00803882402032154000141245500d03000c044040b0742651241c550074000441c020071150a0540207100206104c2c07c04c141410307039980310085190f010503011034854445c05014050f2520ba482040c09040080c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 190132913 1250 190131663 190131677
    0xf0b0a0c020c01090506180402090d06090b0a052211060a050306030c041104090207022403070e09090d0e18010e010906080307030f0c02030a05011e0f050c0f0a0509031b01030507 78
    0x11201181b0280f141c0349421300b58884103214003185d5180c9404035002000040d0120400c2c6806003081170080000320360840d00700c0a0701d000300380c3c100c01ca405464020725203491102d0303003d4500768020009c002e44810499901c001c2c18180075031035a45030b01070b0104070b074181c440390b549140030400c250a240d524022944900e2802c1d070240d0306030007040c06032001c1d02c5d8140380051340c0d0342d400d000041d80c802c00c0280f9079030071a00140c0151007455004010b50b01540c02c6480380150800d0384c030100311041c28102c44a2015920000c00001c100d4400e036401100000042c088d224480c403101d4415102040076000105406141d07801004030b9030172445101c0003804da443c082c60402c2c09a9800410404802403050308201003004240d044d55010311450700c0d4103600000070860003d4082400901d0700300d6074829810076203040300080c141402d6010305413182c80060140d602e4011003c03040183c1da08020f22040801106002e440c000b03450401c004882d154501186507013868906000406075180100700004001035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 190134163 1250 190132913 190132919
    0x105060304171b0712120c110d1103030a0e190e0604050402040e010e1605030304080601061103070c0b0d0608030a0c0201031e020d020304020306100b0d090f0b0a0c020c0109 76
    0xa024004034410301e035510300b540c501030000c1c03c2c0c0011495050021a034090040b000171005a52540f200805200d0345580a03103001501d01541d185c5500c42e0b024115180303c02d042406840c01c5507800e0400c9201d40504216016400c002c00e20756004078a884002c00c4013419408814a0903910041e07110054001c00824242070034145ca03140074002e060340d4005c9440e6800310341196503e801114455005500801c1810b1028580079524141580341e4140006070075000b0400c3c0c2404811581500d43d901d00802150b442c0c408115615588150103041501003400180300084498040e8001401c0003070021380c448501c1c150100454200342d2180159900130018580a81c0e0458203228401c1e1702400c0c00502800c018903500d05004118452a861a10002e103080b0401d805d9070146005070300a030100d40f415030302c0c29684100e40f40719000d03281700d0000a101d0999542c0254210760801c0c1e00c1400c8120309a4030580c0c402c1040b0000751203083d2610748904d02e142a45074100408241305000340380015031549 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 190135413 1250 190134163 190134173
    0xb010806090615040c260601030b01020102120105090604060315090b180c011215230d02130e010605060403050606040506040c0f080405070b07120332090a020312070204050105060304 80
    0x40030040f540101d44aa031041c4d100d80c001c0030407200040184010701c800d0011840c000601402c1240d20034080307031800c00282c00c40e520520984461500e905480b0006909000800c4480e40f0002d124543c01030300c8480200002e002c0801d1180301c9608420b000c030760001b0303520340040d0b8281c1c028200c00b00b039400c1c0343d02345110b00400035221034100301c01c0c2881c04203188541c00d80405000c200000065036885000001191221511031440a40781c41802084140540d4108110f502600034080d511480d5074240d42c4010300036034480595595087c2c000140305907030b0350219078250000c2d401540d2903004030081003181e04050290305c1d88101d045408100e01c00300b11102600c20700e59043e111003000034600018080001c100310280107003010112407521900c451403da00010700720a1900000382c101030b0745040c034142174814075000744000c01555444218607404004440401400b00e6407902c102c580c4200907031030030b0004074804004d05000326620016801030100742c80060744810700402c002c108001c0418 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 190136663 1250 190135413 190135441
    0x2071809112107080717060912030705090a0609031e021c050106030606120317070c03121e05060f010c050d0503061203040f03060b03010515090619030b0108060906 72
    0x1803811600740e4401c440c2c1d590703001c0002c860700c0c0d401040352107441d0010420340340004602c01110140740500d181c40e10140103440e25035400b1341c5c41442a5024102100351211003401844e480340441c070b030075420301074094006481c0c100217900030008030303c0c19103041c000d0040012403210091031400f000355803102c10707901007480545a00000d50307000d0070a070510400c01c40700390007001c015500a03900340890b80c1c80d0222000e29038110740303045020400b041018600101e0300d03c00c00d07200b04031b25240e0000e400c1c802d40701952081010100b034180071f66140b101154050080c109401c2d4145444400900c034a40802131260911054951070b0501c0081001000020320005400c00d400c2c1d0703185004ea48940340c48000c2800c542c0042442c1041d80000304011980d400c40c00418000c603801004240408540801850308807030040c2c0301140d040904c5c41441c2d141d402d0406d64039801c000e014050601014850300c0007081021030350070403101c42414000401001d5400c001c7c0c80e4121484d940504860304203105111008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 190137913 1250 190136663 190136693
    0x90a0c0e090703090602040b0909090703051b0d0602130305070b180d1103060906040203010c08010506030402190f08150108070501080a09080d020c2a06041a0d020a02071809 76
    0x141c0e40c0000095407140300740c1140e0b10702ea502410641d01c2d242c9803e00c2c1d007955003150075064011108500010351070400060100700b2260810b020b4030420794070040c00e144003044d0a80003a0445590001c6200044d0184001c04038820313000d8910302d01a08524084d420080d403a802421810000d0245c00303e050b00c060283c41040c00100c0d982d000c81c01e194a0400c4104400c40040359240c0105010840010008500980b14510860080000035076046c1e066400c40030071700403150400010320000e00107007041e02c003040281350650400f01840ea034a421241116155400c040e843e40c1204d10030b51030310103420520706c4c00f402e003607c081e000b990f040c4030000341500401803d44aa8a448203502d40c1800500012160b8960220038159a0b0324840303201c0d10f95a0b00940d1018100cbc01d1f141104403900014081801c0c030905004003110b1406140c00240d13100035201c00c444141c0f90f142000030103042035041c401495820090b4010384440c0f0718ac02c004040c061840481c5200c0a4200034801001409040b540161 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 190139163 1250 190137913 190137919
    0x150604141306080f06010612060e010504021303140d020f0d0c1b0515041e05030c0609040e1005070807020703030504060c150501030501050a0612112b0b06090a0c0e 72
    0x541e0690004400b0780302962102e45a03002d2801e46000700840866054143c13162078132901c01c1d551031100051704807212403040311600400d903401030010f442c013600100f4040480d002d003680555240c1d140c1d0f42c00d2040d02e2011107001e90004040c0000c841c0c043c030592860004c1a809801d601030f400101034114409410014401c040b00420641e89090f4210a9809042c0140181c01a0480403c1c2078006500c180121520101d031101c08200281e0f00c00510400d456010707000c1c2200210701c40510026412030030405502c01c0e2910000d800340c0404000c074106a0740707040300c0420203007044c2c40040d01110000c0d0070082190082401407002c01d4000044504880d01341c80c185c5000d5809062140050180b9000c0134551402d0100000501c2015001350307010b80d001c03103000c00c615035445445500800c01300340b0042051107140d00b0a00c60f8074103080d08000d07854100d40320958101e0008003080b043c4026040403500d8134140c2080c080325041010f03002e41d01c1384c2c10880801040b900301c14040c0c0610006654148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 190140413 1250 190139163 190139179
    0x8060a060e0a0317031509160e03070504020c030d0608060702070605072a091107020d0605090307050613060b01080705181306080f0c0a1805070e090f15060414 70
    0x100caa2958042c8070b00641c1c0000307031030300f0b10f42c40b110054180c1e41c4281c5044652150510b0300407428039203440260300074480c405130404440c00503c0262414480411803030352500034428000348076104ca0000b400c0450900d000303103681c1c15401c030013501119001c0c1c0201565620000400a00613000111441515420b06000c0d4030b6005a03c0c140002910884a80c021019000300400e6100314545800080d1091064280b04401085114801314081e02c0c40180d0b0007280b0700004030100750340e0b0b405590020160010382e40703420040e4403440d2810310b0603140c142c858290308540318188800b40c41032f5050360310b0900c2c1041460501000040031800750300340f05100b20400c20b2443c0081d9443c0100a980c8400e182401d004241d9956551501c1d620f15480282060084902020452500201c041b007502c40043e50440350b110140000f100415004104c035083c040c0000603074130715a5403512090320800c0d001220741d04610742a0000111450f04641880c00341c1814007040c8030304e84a03422448500441905c8081d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 190141663 1250 190140413 190140437
    0xa060506040e04051911031002090102250e04030809070503030405010e061b0601090e100b0102120d0b1906032009040b011803121419050708070203070602011a0108060a06 75
    0x360610a02040ba03540031981320800e803040042120418800040447c03d03242c01e00300c0d00179002c040e44264501140160010070301c805850040c1900c0c0d010031080f241a29407295110124211034400694080d8040340340d900402040a4082041e8409803106030083d60030b1500c0c10340007801c0e840d00440c10b184a4040031403080403206100514455070340001d03080310955651a20100c00070403910f115410b00b40030303080e40c08140030350386c0c01040240c10040e4020800a40010082e032056080304c0440881c1d65240d10303001b803c0b5030703480c5981100044000d8002c00ba1615007180a401c80d0102c160000600845001000c2c0008087d020750310b104909403808035038a401400101c1d040705100000c1000441c0740301c4044140064440281d12040894460542c2c1c00e000c1c0c412811303140140c2c0c407103c1d03414240d00035014955200d24040d0641c40d01c9410483d09200c0305a0002c2d0400405801c4000141e6549908611440703450003c3c050f01e00702800c0c04841e504045000c92100c070190b01408042c090b02c0c1d2000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 190142913 1250 190141663 190141673
    0x61f0608192a031808040e0405160612050a05070e09070509040f09030311070c0915090207060b01140403081803150108010c020d0f0e01030c030f0e03030105090a060506040e04 77
    0x26503840ca1690560000c203541042d410741d03001d41080c2002c0002407030822110304440d040d0444a91031600503000e075080518000d0f01d041da03100010030444640c0588550303c41088003102c0701901911190301e03900c078070903444400d1008031744004217401c1d440c40c00c0c2000d1001268001702d00000c42402074a24040d95615001d00b40d5a42c03280500301c6421914121a00ea5424200c1d840302134064801e44d030521036054038002c1000076000c1c0b04409011a40c201000b00304071013182d0300103055940b20b6013800401c15a074200703c0c0100c3c1c1001030705451080d1034040c1001a0f69212f44580f50031580c5401e02401c06007180c43c0da02007405200040d1040c8a80200d82070403559040000e84000321707801e02e40c2039031580c4452030240600b500d15008009440342030510305055014005040030441c45550384034145e000c50b001140a000001c0d080e10615031f035171152102c50b008c2c500031001d82d640448001c0d6941d5140c1428000503010041424003034629081c1c080c00942d0310360303044400310b41600042c1d8a050f102c41c05c203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 190144163 1250 190142913 190142921
    0x604031706010c03030902221d010507020d0c031707030e0f0f100b0409060204030f0506090102090112090c080d021b031203010510120513061508120703120c02061f060819 75
    0x12502d23048501c000300c01403d0b4150b17044500c40c0b00354000300e200b083c24015440b47c01d072801601e0b5030000d80c001001c1c1d004054401c004003c0d8160082c0707015210300c01c504002c1180c008050790b141c0c00280d2510100d1401540c01c01003020320a00f0303900108a280803110400c2c1d1030f0003040e0003003603060351148000c1d883c0c0c1c4d9954005020007138002e4411541c035540e07460306292811411004852038040c0c100020301e842c0d03041c801c3d40d0742140182c450b06020044001828020080c10700c08907000071441501141220042000d44e06020711500100451070007d02c5094202c19195065032003a8098413080c1e00b016400c4050701c1c1164400c5d00c182009072860b01c81524003030549050003207114504800c20204c080300c1d1026140640c0610410449185403c03c92400c0350454060007406034040400120303c80164001004003d00900d07185a604102f484540c041d0703100d800340301c00141c0c0f00b501408004115088203100511001004500b85d0786001005440440700511520819141c04042e1036142c2803600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 190145413 1250 190144163 190144189
    0x5030a1509061403070e0c070b0603010e01051617100639030306060503090a1203020f0301121403130608180312040b1812030402030106030c080604031706010c03030902 74
    0x100034800340c1e450b03062070026025080b0010b4131030700c5040e900003031001030070065a00902c5100c500c18901440e0f41c54a004801c000740100740c1540d626164901084402c0c8034840c098401c04802c0e00c2e220b010424010100561010000454038503101442201031448003a9003c030750301c0b42030402040c040700c3c1c3d200c200c05071020701d203a9441c04a802c84c241001c40501030500780d41d1107a1010000140c85030011074950100f1640315955a0003850340001060281541103d05092440c01615110000050160541080c3c0c1301020a1000080000402003e200760340304904a032270041d81449004c1b0b0080484881e50b109040600803940c010910003060044504400f02055007103994542d45100d808109080031601034401070107060114507200c03119011304850081e15070003464a0011007446081991001e001243d056580c0c080000000c4c8011030008000c201038005400c1c540b6040c24060310760110382049424940e264410070046d80e800401300c907000b640502d03002840c20028400700d5142d60b4850 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 190146663 1250 190145413 190145429
    0xc09090c060a03060602011416141c0905060a090c060e0a170309030609070f091e060602030705101b050d0f021603090b0c0309090a02040b030a020a0806030a0305030a15 74
    0x2880d01c00c5160160070a1044810b00e6008001023142c0c0c05c400b0049003002da83c019001c682d21b200b4005860304c6480181a05080c4000c000d20701220170b80c19100800107086401001600d4414140a012047c071100d60b000404200600000c00310b551010341d1840580102d400740181c1501c1d440668448200c17030000390415000e1200d111000d145042d5490b000030b0500c80c482c0c840d0742e00240b004c031000704098040b030782540e1034902a03500f060860406400309081554603014404503007c00340540740a420010301894000d96030301c42c1d09090581c2400d014800b1500c01ca4148802041560b5040c2e01001c5601131501e44281c94a48079486d0401030202002401c802a00120b841d444155140100c41c0c0e52521079181c1441d003c1e81c81c40500d030b1600807582444003540041c40f22000e41c1c1000c0c1c95107940b1243e0900300602e001d031500711240d5660020b44a034081603501091102c2a035070055182c6800000450040c040d4003e60749c0c000302180b0004200000b00e42e1180c5080e00101d1342c1d06c614001400c1f0712 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 190147913 1250 190146663 190146667
    0x30a0b04020d0203010509090c0a06050a0507061404051504050715020a050a0c060e0102120a0807050c030d061a13031101020703021804030306150509010507080f121f06020c09090c06 80
    0xb000032000650801e008551092030f4200c04140742400014036481c0d81100500352200c03503498448141c9a0340c205403a0203003404001c21204000130000d2080c03003040001030585074001d05090401c0b628040c0d1003007104104074030220602c00072030000512041180d1083c407050152043d030140490501d912100018002c0c400c00801104110402c0f0b1444240e400a07a59150750300e00d46401240d8818908c8003c5414234001c015582c0204c1c443c41000e51b22031800e05003240351220362180315203181c1c40b220012507025601d007410710500c01d220b1b0003c8040c2481070059800c00d042200c0700c1c14100c1a51000820302a05050503003c1640240400401180c0052a1211202000109400d0750004803412000a4588500030a200d03e800d070144003203000035580d07141882041c00041d107841d40305420030b0307400003010302c0960382c81d103007100040014500b4407100141d18200b94008420701001180801c40b0011080000d000e80381d4001481407000004540303400007516101d074040c0c2000392907142190030000c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 190149163 1250 190147913 190147927
    0x11a041415071a0a1103060d0c0305030c0c03010f06050f040c030b12060105041119050a0c150c172809061803020d030902010f0f0201140115080a180206030a0b0402 72
    0x8940919a40c1e03c00c1c0b03841e2519903a074120005044407080c484580c01c00720240013099075410010740d62001184609190780e646502e0340c450901c0c503002034103001100d9000c084844d62a0500380034101002590342d2040c40201d0521000035330407100c402c103a601030340c3e8405c0d05911052080d0010a041240542081e49401d080108192561400d0051a000710f06007038181c860243c115040310101e0681c0846003568018114084460358071480821042125500c00c500210f4800003604140c1d5160b0705001a003425020300213020509491b070014462010102041346051102a680302035480b215124095480718030042d2005289107070000c0d01c00c40c580a00f002941910703460061303480e40603408a43e01d1400d1200d044041c0d62080c04003e000a104e444021480d9010310113007014410540008569820308143c040790081c4264040c411001a44100c0d105e080d800000c080d800c0155103909001005d0b600601010002d90140024020400000051542c00d01c1c2d5024140b204001001035644c4c0007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 190150413 1250 190149163 190149173
    0x207050a1401140301050a060f050c070e06030c0d0b0a0b060d020c07031401020a0c03120905010c0224090a021210060b070209070507020906010302130518090105011a04141507 77
    0x84040490b01054034000300400d041241001c2e0f074101c1d06c0c000c0901111030705114044410142c40320080c1c05100341072000d0a0307051001c1c0308190260410b04285941352601c2d10825192034030803c0ca032401043c2424900340410300141010354800200d580220342c4045403404a00244200387c0785040c094408038034580e1902e80401d60400f264060302e03000308900340818080d0301702c2c4140076078400460b05004659000a00940803e0342c014249503001440f000310b5200c0324251a0064440f1005170041c0c042c6540c0c8890340ca0000a160103602062021441d00300030302d5696140f4208007900c01c480b01c0740d851000c1001080b50002c481c042560a100c401d60700da505000f10782025900b28425a12003000031903c80c880d80545200e1b0740c0090440c0c5035a1110300054000b5402441c88948041d1a07080c0402d1136254208562445442190724981510346848041c5c01c42d501a007103c207501c042c81c00c84c0107000d082c1e0f8099505540c000c407031010384003000740c00140f80c080d030301d0700030100c1440c01180d0710083c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 190151663 1250 190150413 190150439
    0x10170706200a050601080d0512150103110304060c1103090306150301240812030c0901110106080a290903030106080c27040e070f090203040c170d0906020a020a0608070207050a 77
    0xc20510440c3d003101c100c080c041c0e07954013580000c4034409c00b901000a5481038100181a9a444181800501c0301e880765031000c415070044a0580312951030342c1d81000010b5010f5040000001800e020703500b004400d000090711a6006000c0c041401c903002e4400300c090b034083d40000500d0380c4a6400000800c2280c070203184c0171600b8880c0c1c00090141071001c0030f19194810440e441243c01d0300c0f90b00d01c0d10413700015600400c850000c100341c1e40d46c1d1080400d00100422420304424094920f01400d840b84041d00031141c900ca03100c41511240c840103115818000000b600e040d03c0050900c45610b42e900c00580000d4000c40403a105034651030602c0d1800e10041d85654407100d04103031000d11112a4000707400d0344e900d41030321490a41c00341c9203900b04140c00741a03001e1034101c1d01c203201d04200c1560340c195800084200d80d1b0341c40b055802901c0c20820b050b40000300c61000701a580041e1104941039000038034a8003060bc248401d0003540000980024030078400e000c00307040010100d090054894040c04244 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 190152913 1250 190151663 190151669
    0x4b022419090614091b01031b210e0309210c0114070b072606061b030409050c190905010c020609010215041202010609020f1818010e10170706200a050601 67
    0x12910302c51503941c954130a0140c1400d040070300c040323120f00059000084400720220440c5003e0201803d855a0788009030b401480c11000b1700c20011034440800b201084200b40c200c1580e0320708a01209041420414046421420400242054001c80c070700101004194807889800400e010b0703400c0b00704141c40d9084086402c1505a40720540c240d541c44902c04100940c0903201c007a400801400035225144510440100b0f604e5079400b034a040a40d1010041309171230303041c2c42c44400104c020400311b426040c5051002c00300f82003440c20076111842c2c040044d168295000b406405a0400240c030b0409900800c141d460000740361a4a0386546482d007818415081d000f10608010350804c200040c0b5815540203580580c419030003843c1c0750100c04100b61780144400c60b40c1507000780c25414030415403504140002d00070081080c9100d418903020481151000443c0c000c900d1788030040c801f4021100c00040c00f80103588490030205003c192a0304400c480300d0b2500500c222034072920090b0b400300f0102082c81c4d030403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 190154163 1250 190152913 190152943
    0x9031202011d0c0901180609021215010503100902280f09060905150c01140103080a1206060e0405040201030f0906020d0b014b02241909061409 63
    0x200d8114a0b2801d445104083c001c07030b40800c1c503000500001512001060842010641c0003c0300740d55042904243c3e00174114642e100c810f01c40030001503211303684280302d0307092091811514500e01022000300301b2280703001d0190f4055010948150b111421201074201046208a2402c0d468401c440144000c9451055100050780c0d0000054041d00521b4200d080d681c1c02040894410903074030310040369400c40c001062030ba64031a10703410200030f000c0f403036a8003a41c090301c0c000d952004000c002903c14120742203075950042c901002000020b900507802d40c21101c04440100755501c403400124042d007292098059030300d01e08440e807820001c00c0e0b03009140300c46280c030060000c01074250040da0444020301c5286501840d2030700ba00140710b0010b406144003440302c004c1322181650100040150fa55501d044400740e4408202c1050700c201100680e500b6141c81010208036180586035009005c514414001205459042c0d04040100d02c6c1c001c02d0b20000c0b1003001c140d162801e011141e0781e602204c690000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 190155413 1250 190154163 190154201
    0x4090e100605060301050604060c0c0906060f0314060907051e030c0414060705030a050c0f06011203120b0f0d1e1b0e060a1203020a0605160306060215010306020a0903120201 76
    0x542c50410340140c0781241e1340113054030304082c0742c48403d071400c2402e04800c40b1560f41080d03010818900e10b02c204009401c49a5070203800c500070040141c07c80340e002c450301001c0c44213081000f210341ea1f160301c80360744000075241541d12103001d041100c030f01080000b00a424840f001c0700300304410000c0c0020b40206c540b081920303950001e081c024003040e03214004e40a01240c02c200b00310340034580203500034141248000100c803907080010b0842410310100780c10411b0310301403040408080c580d00200034620a01c0c105020010044080009200714511008090007110740454410600c0400c1d0700894050310b0300404400811010b1034541c10a044c9102c000400180b00e0070301141701c0e0355001000d84950009010700b010031381071006440c4508000041202144100000c041c0055442d000b900d00608800440400c0085041e82c05810303911a40c0011f1304551155100b1010752906510003070461742c02c00320059842054800031120308816070005014140c215000310b250301c0c0d0542c0101d22060388526180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 190156663 1250 190155413 190155419
    0x261f0b04020301150302031003080403030c060e0c0307090c030f02030c220303051602220b0906100212090f0a0f08150c1b10090303050f06040c0503011a04090e1006 72
    0xc224042806101808071592141c285198003035401940c001d0b446594164040d59203075505200d030b0b400b6400480010315807015071002c0044600441141c400035002410f804441d220100396070780d20174403d115559450322054210b03a07010394800b4072581c0c0341d16825580c6e454460010034082e070101e80600c1d0101407a40f00c00481d2840d244851050700c1d8103580342e03403504011790703c05080325041074002c0e40c3c000e24021107050100c84410385400c1c0755400400c041410328068040214800000b0322081c069503009681d1540645d003c1a81d2480210030025952206150000b181c6030f0031031070000c01c0d0803038050f0001040000203192580200e81c1c0709803c81e004050b80340e101210082c41a11400020782081c015500702c5086984a1040910580304079500380001414040590f10307000000d5010075552014403c0f0951912401030b409030055806001c1c1d2001190010440d1005100701f149030161205002c01c200e0041d400c840003004040820707c03464049040003074450601d20012202545040400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 190157913 1250 190156663 190156669
    0x5030d0b0609100c05101803050f0f0403060506030d0311070303150e1305060a0207020f090a0f0501090b0f09160c030e030303100503060a09150f06050d03020705120a050601261f0b 79
    0xa84524405800c0c7d0b9122484155020b40b8150000031307003501c031154284a141c07841062603010b80000c5008020119250509005150400d000e410441007010f0401c240c2c200e02240b01c004594980c0d83c180390000302c000004a203001d121b0480c1d007045001012034418403600070311450b01c02486501450544419484030b008020407480355060094012043e981040200d2034030a01c2c0e940e00000f00e55001c01c00b0200d820070b01c400c44070240c005e0885140d07542100c400c1410800c84040364800c00703594616003400c144200109101011003040200b1907001102c00401d03114051801140c400a01203d850b82068440119080228003810b40a48035040020700c803014a4020100e00c940c200680d030305014941440c2102421084540042003a03c07540005010b0b150010f458010710701039400b501c001401c100c1042210314051003a40720961000b1415404503402155560440705040361504052015694000010004090701001401422003412038541e008841c1c4c0301e02c2820210401410080c0d17030030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 190159163 1250 190157913 190157921
    0x304030f020d0305150d031b03031a04050105061b0f0f1b0f180c1b03090f1e040c0c120c050c01020312010e06010c1e060b04060305030d0b0609100c0510 67
    0x760b400046117018400d202d030a04004c618900c038040d107070400c490340d81403403041034080841000310b000950740c08561040d5440382c261400c54841c1110b09000c0d070751506c2c000038498042d01c3c181c81300030580e0b40700303c88100008002e40c07184248180203847c0800e00120210781c0b207982d4000c50120b018070b4500c014041d481e1110b0400d00440d0000e02d0f90308051101c015841002e00d004200001030032040000106481d040d030a06542e0a014200540d0b580907a0801c4c0003445481520340b80c002c416010515034071244841c07994603041c1c002d07a00042c0e6005103010031180008041006059400c151341200041607100d1020072245000340100c0e860071080200480e500e10504041a101029840051101c1e01d03100202580240d01450610001c58007900ca801c10f05100424000e218294481d00f07108000d050b0086400c1000200d0f03041205600c1d5813261601e9103d010303521705400d56100d1030b01410b9901c842c252110b0b024040d0940c0112107a0702c8028011070351140b03054601344190000c48a8412050007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 190160413 1250 190159163 190159171
    0xb010608040812060a05031009050c120a06050604090b01030503070c0602120a1b082205040902060d02090a03050706030603110a06170406020706050709091406100e0a05060304030f020d0305 83
    0x445038035015001c4003549100714094040b0751703c000c12110001c0d20340d4080007814010030f210600000d22900340d2508a207850004e91400740540d800d410004407803030004c07449000c030796046407000c20a99220740004000309000b400c01441051410f00100c1070280000c081c0c501d1600c11030400d04010340b900b0081e652955881c00103100201d04101d0341030114030039550503141002042c10407005c240c250741c0d43c070821341100b4420211100c140c10802c18203400280d08000a045c00d803801c00c1303401890740101c2d625101d0b2516100c0712076000507040490791107403504d49006603044403d503400b003074903a10001c018142c107200c1510400300080724001c061524252080448210b0b4582005c0003411241c00010403000601c10b6070255400c0c0044004079100740901885520180d035444042418142c40100301c40500b0250603500c0300f5501089119168071101c4540c0119504065103400724040004110707850701d422007600b044c008010320040580190842615003800e03002d0700c3c031480e80c480c4c0407400c1300c508403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 190161663 1250 190160413 190160423
    0x2007050d02121e070b090c01081608010e15280501080c1801020a0f0b01050a0e040309090b060d02040807030606120c031e061506030e030f031603180f0b01060804 71
    0x85a502c0d80340f40e00d440082e00f40700d01d01d000d50070000c103501c8442c0c43d04021207030204070350005008221190f90110807140e01611421013600903601c0c0c2000100b40810500600248000c03103004107203102481d08407c44c046000404880490b100c00708440341031998144000e6003411081000715540d8050a1418030569440003480c3c00c2503201c2c185d500e01d4803000d91250381907010742d21046004c5a00403000e00404c2d130007203c843d2210f501d40814030111884950004584254200501000a0340720303074800201ca08000c400f0410b000f040340090214401e0f1210120171900c00a00080d410a001c40d50104403801240c0c02c00006603907c002da8000c0400400c01014a288500180001061410000081f00c6008010705440195035a5641100c0c280305044c811640d020400300030180c1c1c103000d01150050006d0146007060402150f030034903800041c00c108408101d400442910034860740c801c1c00308003041203901541c030070141010340e40703000c03144010348502d84110008103e81e80141170345d5004541c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 190162913 1250 190161663 190161667
    0xf1c050a0512101a0304020102070605091c0213020a030f11040513020a03020f04030311010c03180f1a0c041d01030209010603020705010b090115081b0703080a2007050d0212 76
    0x580460b07000140001c011401d41000e44001140f0792102e00e8140090341c4072094400e0703036801c0c60300019150000781d07884181003003000c119244450303c0390313052031116503401c90304080d01d804644000742c0000d904e242c0c44d54403544041804142c16a260300400c0301501234078002c00014044000803040c505c5280241604104441c207d426400216801400c3c400080e00e0018100900e00402d204164000da005400080c800300805104290070b1180c400400c182e0700b01080828200150701c0c4141b50101c0c00176180640056149043c440d0700700b114640d441d00f2040c03861240c644110b29038610b4026008070104039418503018580c150781e12500c64180d1307130001c11882c84d5a00e0460201c002e0351000002300c81554032500d2050040d00c484c400e860280c0120740b420f05504805410041c01c0040041c082e6295188010360001e0b00344164003260500c03074162400400b1a0780e18070b0101c018003c50080e0310544030592070324070901c2e003003003028180d00381c414400c0d10449403804070102e0f81c3c0d64061402488200c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 190164163 1250 190162913 190162927
    0xa02280b040b0a1b03050a1401080705011409030601120b070f050f210103050106170a0f06050c46090b091206010b031b03070206060402030601110f1c050a05 69
    0xb00c03002142c0c003034200140402c42c2000b429218030311315101c0d160400800d880b00f0070f10541c102a409001009100003075a811030b50700d060601035852280f88203e81c1032002c10b140c0c008041c0e120b20212041c844c005001c6401e9035070b556000d1010032a00880664070769841340d0108442c148101000307080d0703600b940d40303060506c42c2c44007807a0344591000441450903000983c1200304006941c070640d000b54001c10000440c2403408040c0700301507034417948080b01500b10781031042c0000d03070b446400301216070040c00000d4540d40d82a203403c040d124400a04050009c0e001b41040000303000303400e44100c1c0d2988080c3ca0000b652410344100907041c3c0342c0040e004160301361000c0c02811180e002800170303200300074601c4c2c40e00d1118100c4a4101002a000903040032000020014607403070b80300036580c0581202c1c203a50b2540c03401e00002500e555000d00014400c40c0c0003c0451041d81c882d4841d00c810408070000e0390321511316512080d594002403102401c200f1030841c0108143c6005005a0b04410100c1c2c88852030048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 190165413 1250 190164163 190164173
    0xa030e101d13091104050a140a0209010905191404020901020a0b090319020a110306040507170a02060307051201090c0509010c08041a0703030501080601240e04020a02280b04 76
    0xc1e040000790400c401e0345032180001e560740a00000b20b4000d91001d01c0038115035003400b0590b403008014103a020b0074980070f01000154588072591107000d0040050f2100102c000480d07000e0342e03951045038001002143e41d2548004286404211008811a1000d42c406081031200340d01542a00c0c1e405070308029502d4000c15044800c850f4800785443c1a60b142c184000100d03001280e80c0c000346130041e44070301c49900821001c11f02400d0710880880092026141c1607445a07aa00254003d2004e900e11400740600107103000c1259020103640204800d80303070f244c100801000c503080501100c0d4180c0d02c03d00000348103c41d40c41220003001c03003581d44034500f0b526040151500c54400c0c90813619480304000000b0441118050b4195200c07050014555070801400e008055a406803c80c000e00e802030001003243e0404a607110301006580031890610241444044d0b404440f81e034412034016000203480401d2650101704492203800498000c2116108100e0b10756100c1e0701207100030040342e00b110110300410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 190166663 1250 190165413 190165457
    0xa0203040f0534150f03060f03080a180303051608130608070212041511030c0109080903070b03240a0f0801020304060507020f0c0112020403080c0a030e10 68
    0x180c02a00780541400e80c50b5125031400070391071004640500150104168021031070720303855030010081c10b12101141000442070840001c010100700f03014084680340d49090203504100001c050592400a4030390766400c010800d0b500844a240016905003a51804508241e480d841580e4140d81c0349800c01c4201c4100040e12a0314540c10381c0d0804052164001c0228109251800b600490340c50414600342400042d01e000c4500b1040c00000109200522100c44030300345841c17450f4201c0c80d00c00560303021010060708510500d0060302c400c1d42450031070300c20b104a44000f440c1c8064164111084190b07504602e440a010540f10004190020083d100e420644040641001c800003441100b4496a40c890364005a0440d400a0601d0350003001300400d100592082c50350002c018006080c03211070060721251100c16a8900c64107004124403170056407000c0d0342c1910099a80f00c05200d503165401d1100c0d81e82c4120350b0300e04800080912120880608200486400707002c00c2d525414809030b1118101d107181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 190167913 1250 190166663 190166671
    0x120108150610030e06040f0b0c1e2a0a110301021309093e0d030206130510020d060911090108010e0601140d05040c210b090a060c110106050a05090a0203 67
    0x6488100481c00100103000d1740b40118400d410036035841c810783c60106041c050050400031803d01c1480b81c46101d6102d290044248070007041002d640750800410710802028003031907803100d801000ca00a410200002d4020751440c05215510900d11501e400c0600741d00c640e071040b10700318580c000c08111900306500010081e03845814048501c0341c100400e0318a68107280007000c100320031604031102441061841c07881c105401c0c1c981349100b4010380c802035920080a820001170301c070780e403a8002c2031210910203840004d2000c0029559040f4440040020300805e0040c11b40643c603082003a03107551403400c22511065410b842e20300c45d6070700e07220741c1142090340240103c0c103102c80c08111591425002e00103007900da0b500c420002d054206810100948860707900030324a00800600b5140c00340481441040009078440310f001c801e965004141c60070980b0b10b000c000c0845040643c207900f040d40285071580016000002000b08030f03965010801d0b050f00504c0f4480d0042c162001281c2d44145da90029540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 190169163 1250 190167913 190167917
    0x270501020903030c0312010b03100501110c03010c05040602010e06010e0103140a020a06030615020d120c0207030b070306030b091b01030b01020102071a01050f0108150f1504030305120108150610 85
    0x10a041c40c00441d0840d80080d1000d80907030000558000c010041803a464051702c403180c0c0950552612040d000c00300780950040f20b045c4511040c4411010804104501c40500e019000384500b01d903100c0090860380243c02454055401c10880f040120400180213040703c010008401040c2d20315194554190070b0b00302500c2013070040710f10078030141c1c88039040d5400422680d98005403141c580364220441144d100b595200b10740000d2059400254081300d00c031400c0c200d007400014011800c250503440c10359160b0004101080440c1049003054240d8003440440f8000c41c005c1c0303141c0e80c44100f615150500318440441011041b42001041c8d4030a80c068601c002c010b0000524041d11a200d44054100d00119a100d80d0840d4005011314104401c104100c2c03502800d007048035090100c020142c400807242c64901a4100c040400d080341c3d02c05405811030074402c1411b9541d140c803401c004045500c1440c0300f40c40c0515a0300001000c0e0000514600c281600c01c41886840c1c9801040000ba00b2505c04e071001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 190170413 1250 190169163 190169167
    0x10c0203071205070f0f03120c02010c1e0203010617190b011e170a1205070b040b0a0216111c02060a120f060f080c04021c050402061308010902011227050102 69
    0x26917400e035440644080c00c0c50b401201070051943c6092100001c8403000c2508100003120f0120040c4d801418500340154820020310a0442162003695100643d0b00d002e0360560800070009050180107001411400251090340c4180380c2c043c440100c8004096001010007580900400103820320901d1108a103401c8200c41c503010b5580c0300403e19045881907005825045203501c2010080b00946000b0034455a007001d9081201a80302d8142000000b000074003001003050004400c001154100c030800542004807105c411194100702c441001114407a0340a0520747c210300d01c440da00d82c0c13041611181d000b02054a4044200c408032070003501810700c0600c9584405d10804100c41c0c600842000d030020104d03a246040c5000149071812400110f0940218070402800361054110300c6a1104604e101d900400e0349d40754ad00c00301e031480c8244001015500c20303454002c1200701e01900400310850007640d56107800d40c4100422821558100e107039064604010b004e0200040c1c3c040a444515401640018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 190171663 1250 190170413 190170419
    0x306020f04050a06080601080f0118092a0e10150309030309080412110406060c0321050a0e010507030b0105030601030902060f04081c0f36080105060f010c020307120507 74
    0x240c10f8036084d00040b01088042c0104412941d02103641580000074004001c8607500d0081c8024804c0c00309000e402d005034440c4158420301c080c5110250001e0f803400300b5100e040d11202c00b14500c0c240c1600403030b840200312801185403130030381041c0c100980e4103041109041c495110400ea00070015001c0131000c0c1910b40c00c141000c03400e1800a80b0041420903840c00c081074141ca0001303084803036402c0e620701c602d1600c03005012030fa6000000c0300c2c90b40e034142002101008280340c61f10700d580b07000302c4442820b414907081111954190300505d0b91441494005d00158071901403c2d81500c04400c82c00d0700055050001414941c8031307800032403034180050101c17484c011103403280080590164001e125a58000c5ca1000e0201d02d0120810b020314025103041007401800c280010310040070300314100b4001c480d0304103290703079040054400d59004814003001d002ea6544d0717010040c080c040c2118018071482820041c12817a50107072a00002c04e82c1c1c01005001524101003070144048441041a1618400c80c4004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 190172913 1250 190171663 190171669
    0x3021c0510060915120b07031d0303010801020a0809150a110f07110907170c0a12020d0605010306050f060f07170d05090c060f1209010f0606050909010902040503070306020f0405 78
    0x4001d040e088102151400d07507540d0710740d400c544e55440800c40c14128800701d40400c0703441d14000c1d00801149404144880b1801d010451607403102c440001c0ea010000c000180540158003e118102c400d80391881c0940d2000074031512805442132041c080480c401c00503846002d10f60118600540000a480c28004d803665a0714850b0000c91045980311488803100d02d40780303001030080b07600821a1030502000c0e46001000c500c0f4080181c5204a20440421801a414041c1c502540c146001450464a461001c89140003401c40340c03040c18042450a0030128080c104a203045295402c00b4200d607140840403500f905a590008900752101c1d0140d0150800d502c036600014054503050010115950404d00311460038960100c02542c8983c2d4100040e10b0400070321020740305803280803418021265902030150340505030416001c01902d241110204140b600007028103610302c0291014030150380c84441c10000c0f48580d000d001c0c0c3c15408904100700041d0a600200610160f010081e41032907560004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 190174163 1250 190172913 190172921
    0x70f1b030c0b0114030d111504081306030e0312060607020402030c032203080f070207050301020c030c0115050303090d06090f03030b0f0a06140c03130e090f060103021c0510 76
    0x100300c00181d000500c2005124040340403501401d00e0350400a014040c110000c0d0b0758905a1a00109100020788818141801409200e11803001c0d60107280301c9160503e010340d080e92204240c00e035040200300000c541c4900c20b100301280940d1880c0150710f0710902c64404070240030b0042200c2d5201200704000401038072180041c0d806000c000d91540e85a092021a2110f40484140c01503010f6110b580300c03c02080e4040841900603d500381da6000caa11500d604a05208050308200d40540c000100d0101401b4004010154005071000070000090031045c11000800c03d071090310740c140d0042c40444000d280219220701d18034494040014100c80715910801045480541a0040b0303a40c0e0104030303000e0800305007211015208941500619042c4903001e00325441800c40714900c5400802d074001c1803401001158198030482004001c41a0b98990076218000200c1d600070450161442c000401800001c4041c180c2e40c5c0144140b00384000d41070045408560180260340394031400203801101c0c0320a00c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 190175413 1250 190174163 190174217
    0x1c080405121609060e0f100b0c030c060f070314010e01091d0d020604020a12020a0e0702010e0106030f110102030304030207050f13090507140d11330705070906050306070f 75
    0x480401c0041c501101c1e000c4900000b000d9800032100f1b6401c1101e142d00300403409050300d41045806847c0d0703078110b20107441d60140c5681600340e8818101804544c00c0c5101c16648500403d0b513080c001e05d0510b00388082416802e110703200120034032000610044503107410440664181c00c0f0b451626201000d01949801d10380e5600c01e000d40c20080a110650800d014000054041c90054043c268800d502240d0801c00034403401d4207071045000440d5283e40700b0342000d041c0c100184000d0000c2c54403400c000f40b4078410f090701228444400741c0540700c0c950010003540e00c551340640240000e58a00b02c24004420f88001c100d650110b0244505c4444218610451310035502075001130044c1070502034502d020303030321500d079440c8107070b008030b001e9000a8103e0a1641e0380301000c1c2c610094a1501c00354129544a0a40f41902e03040440c0c41810714400004028041780c0d80560700700e072001d503624140c82c0e0440b81180a026019000303100002e0210740544084503c0c50301c945088402100f12022041c82e10440007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 190176663 1250 190175413 190175429
    0xd051905190f06181a04030302041d010518060307090b03100507020102120108011e0b0f040516030c1d0d0c150e150307091712040905061c0804051216 66
    0x521014007800d4454815000703820768019110381969200da42250340c21080e12100d05c200316000400709031094050314000e00350314040c0c1580020803650550303820001d00650b40540202f020018000706110413113030107014080c010380302c0f4500300304c0c0c42009400107400e0b0640502c625590101410030b41d114251084c28507900050702d03a404500b0001c409001a0f00084217607040c094a40c40101c1c590041488441403103600081988961011031031400360f00700d005a11a2a11007040b4040100154403400304491360b8081140b11030388201a268496100c1c114110495404010205810811041c0c12901c1c017682070703105003036502c06144c0b480d0848001054005944d42c0b0441c4410706104990300f040d4200306a00901714544804020940c01041c800d941544100000c40000240c09103c680789501c1080c8413260703642e4940301c51002508064500074090380b01a840f40480200d141074240b00268060a82454035103403d00308003c01c0903140601c0072301d01458105c1503000d11040b903da00142000703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 190177913 1250 190176663 190176683
    0xb0f04061e021c09080106270905070501030c0c02040905010636020307050c100b01092408150306041406010b0a1b0f0203010207200d05190519 63
    0x40400207141c2440c0861445000c0e080384148400c254002c07408200030a02c03042d488890030b2903050125100c045035440f02d1025440e280004ca100c240d10442c004d000791000c5e07500c944020700341041030304980c40c80d80007070000d8200b07400070701076913100f500440c000f2a01840d0400105200d500000c04484200c40210f455130741d148820042091000750052510003070541050f040d00b07409030081140c0c40c003041424a803a500000280c1e05a0040d0301350303122480790004036442901503104410091507034116003400304041c4080003e000c000702c42035510399100c6201c124a0742015100136a0a410003500401000300c1e018461402510308105081c8518010039000b8904854850500d09040c41a040f003403e8080c00c0003081011a0003074940118a403103083c0c10100810719041031401c41115420095065000042aa0030320075108083c40550030440700c0002100080c0081140f03d00e400d0703900405a4200c0704040141c40080c00028854074001c40c00e8441500d82c82e10780c003256050b0341d64129100c41032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 190179163 1250 190177913 190177919
    0xd0807050f0c0c0f03010c08161e050408060105061908040309150909140106090e04060912121b0e0409140d1101050a050f01090e070801060f03020f03010612020d0c0b0f04 75
    0x400d030084403140d00185e00800810041810050031560014055450203a82d440505c000c1e901c03c07110441d9011071110b007101c204001000c020859482441400d040b8402c01c8008621032400e1012240c0004d40542058540e0300c0a982c1550701c100001d00c150140070500e0400102d200b40140800c00820362562484034050600307007002e04489045660101d810076110040c0070540e048a2500305071b0349600400703042c50703803581b4141000d401c080340c006042d042c07052900c110290f00311140c003003a180590300c14081d01420b050729400080c1d00481400002d12646014141c40c1081d5100a101c00d00500e00e61071550a4400c00a00c0d0070a59001540002d10307404900c02c080000b0301c0340c0b41e0802060441030155081c100c4144002e050180600800329956a0480c85480710800c1404002c000c082c0c02030094950783c845100402c1c0951100f039015900c0380b11003040f50301c1d040c4218004d9402e543d030303442c1106a0035020300c010501040800c0300c030901400000b00d11506054003402a18403415174190b65241 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190180413 1250 190179163 190179169
    0x15030b1203041e0e0f04050c10090e090604030212160b0f010e0c0f0301180f110318071224050a0b0f090f0f06180924090d0807050f0c0c 60
    0x3030207480103009a00719110501080d0003503228540c11002d0400c880700151540d0824909025900d40308da640841d003038550103007203070b08411944120380a16034114403c1e910203100036101e171822600100160000f60790551031010b0100036041861407c84031025400807551800369807007096882a003a500004010803681e409003d0709503000301088a0141001381c82c44c2e44070854041070080c10f8001c0c1c40003410000c1104907500444440305184810701900d0150611802c03142d0081e40d07000c406030001c025040000c10700152401c1201c00c030071a00340c1c009602c2d4807880041e5401c00d02c41e01e80129aa07164001002241c061180174010f6584009203010065040004220308000550700442d1000100000c101c1da0190280d07001e103071380ea086400c540c0c9940c0003584035103140b000725100c1c585a000f4131440c1680000d2444011241901c1104141d00101c0368000c1d0312412102040d1a0b8072182540f941f5600c500171b503541020703160401c2070404003090a020050f40081d800007000d031340503220600300c0349 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190181663 1250 190180413 190180439
    0x718030c050910060906080c1204060509061008070e06041d0c01120605090a0518030a0e1804050a0305180406090e060709050f1e0603190608030a080115030b120304 72
    0x10301c0001da02c0f980507190603030142c60303907180784100700a10110720001101d81400d441120f074540400510941da03840c0038071f000c4000740410380d045119031240c00e001840f084200e1507510300750303001c80006103c0540380202d01440010300516441e002074a5000d1140560b07014004484543c01d442c000d4010309102030001031006103600805000c40e41404801c000d60303280c10820581106040d20085065a1054600c42c1c1c41e03d0921988526840001080f03824151701c1001c0380300d848400c4411800b15007890703584699140084d60041c0140d08004010340000c0c4c003aa00038401d9010411240d0101d08001d00002e04441140d030100c01d032580c03109a01100c00d00140729040e804001814000c0c0340b9800d14000c64480c1410b06d030341c00d000303c04d40b48905ca0035901d00441c0d8543d0440080000d031b528a48040451180f8483c07031100b0f04014101100880d072080044203403035a2048513076900c1810ba00e060580181c10b8101e101004c1855a1154000b40300d03207030110b07a0003408089000941c5e0707452810385510424 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190182913 1250 190181663 190181671
    0x702030f1606081e070e030a0516030b160816030b041409011d10090302150703021909080d030203070c0f080c150c1926010914070e090718030c0509 65
    0x190085403034014014003221405d40050841c60100601044803000c20b1402c3c1440c0400342c8a48100d083d44d01401000400e1102a60b10031500007609131902c05182c0c01c0381d400070500c40080b50001000403604601c98142d0310f040c0c2071901d000309204174600d011800310380303245510050407141c0504001a1b03d40034001c02014186850b500d025024910011a84500780c1001d8201c4458a4044003001d00d03200300b1010348034180d4001413403414140140c010f0000c0d800140c2c4240a6002d8089000c0690300034114002150002c8c07005d1b0100790100c0b40120700079840100b2840a000006407164003144a45941105036407041e900103541d40310500d0321034500390440110002c00380b48802044501c842c2d08096420104003e14401030100c00760105540d01880d21018141c642e4040c100d115840c0c0c0461003083c102c50f4446010810340f010910051040c0400b25400c0303000c10120820080d180c10080d0007550700c0107440c40c11030703c000500e41e0740305451515623005489689900328140911301e4408803060304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190184163 1250 190182913 190182931
    0x30b070c06050601080906150604170703050d110729070311010e0a050309041104050d0609020108060a03080306100e1201020d050c030709030b0603030409020a0c06060e0c040504020702030f160608 86
    0x9989095140c047d40c0e480000c240e0000e2100c1840046a56101c85040e103021309410174100c08416480450071760740746003e11040d102c921840e852800690301038403d482c2501c464401604211342400c000b2000001c1007400d035164400420701e801000c085400107010030b54802c3d07640d4184021001c580900795030946040b1811904443d2003d400104000101e1b148520152000714140c0c2c0090601c0e44503009651240f904520404040170802c1107a61203002c4c0e15100340c0703c2c40c000703440f070030188103004146001c010640001007001c10180d190001b43c2a420010b02e00e0807101841020000c81d060007802c900044007a90003245d482e0460f4a58010154400504c400d1641503140c07940c001401445d0910004c2c1110a2075800b003041510280122400341514200030b56070340c4900b58000304402c2005109541d0369241100c046903079550001c14601a01e0b01090079800d181c00c1004220013540002c034206d9151007080000c03090842c060250b148201c0824100c00aa1803a0039409445034000400c5030103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190185413 1250 190184163 190184177
    0x3021c1403040f06030b062512080105010e060904060302061308070801090f2a030807050c011814030109060614150703020a12020c090a020406020f1204030318030b070c06050601 78
    0x10400c48008041012100e05107401b141c0402804041003461003020142c00403217215100b60783e84c441500010742c1101384070b11060402c01e481c0c19000c8602002c03c0c068280001c60707032131400405281150140076007010040c4009116590780d800100b8650080d036030b0a030504007010713041014075020703c0202e00a000b880c00920910032540e07613807451031007611300050813150003074002c05007420b0140c4065040c2c0c144400070480039071281019819034001070300840303603403186002c40800b40d40704030011912070b507050208003202410504030548207000c0c28181500756580f8211000400c0c45801042c0c001d003800102803003194064002e10600000c04400310001c0302c804c000420000ea800906040c5464200422040c5401c00000803030078541c0d0030384200d9011001c4018813040c1301f103e07801001114110f400300e8000d0007098a1580c4c40b10b031b04001d042c92000042c0401c001107401000c04140c55111802c0c0e15007215106e070344031604424166446000940000400000c112540c8115a00a0b0090800071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190186663 1250 190185413 190185419
    0x506040308030c0309030705030a12050a0b0a031203020f070c05040e150109050c040503010c0e03070503070501050403080a030b120d03051e04030e210c0312030c04090902030703021c140304 83
    0x2485600c0043c010580b038a03c000005440c405c000d0007a254003940c40801d40355210428130004200800f4509814501450040494214101403141d05901c400c0500701c04546840d60311040712070f80124003a001070540030081050254081c5004000d050711032081c03c3c454500703002c24407085480004980c070395a4449240d502c0e94045115020b41101c98948001c500e0b607450b03214508090140794000360b055801c0820201c40103801c045801c2c2c183c0000d40c115860140e0350000c050303407042ca40c0b00780e60120f0410072090010400d000c0060408407102d0801084200c01440410071100400e424902c01d0b4102c00d011001881d458050f494000e0000c0c43c80035401c94209808021303584000c0c200401344400414100c03000d455030411038010b00805e21072003920300e40544215454000241e042e920900402008607070108243c0141c1e801108202030342030401d401c0c900341c24020301c810171090b6031602c525080080140d49401e445414041c1040002a40402d01d00d4205c003070107184a000380381600103201c00c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190187913 1250 190186663 190186673
    0x8010c03020322060906020414030f0601060c021924020d05041a031f17120703020a0215040506040f060f0e150d061d040b0c0a0206060f031e1605060403 67
    0x1440380f0700f404a1040c180d00380c01e46000401040d000b80d000f4074140c0003150000f8409000e0700d030002c001e5000d03015141307140b9003000001d0301d44c0c03401d024000200c4c904030740c004050f050410a038020b866850f004425000c0e2600420b03c0c0c1188022000244001a0640c0310b9085a06009100f0b50360054103000b41040d080400400d080d808920115040403004000078507010380c510060440c1101002e010007455481d5a0641c0103034850920443c2d286c86402c0c0c16600700c0d0944401c41d00c4154042d0b02402c00c2080075400c0095080d611b1101104d0350f40d0500000c5050350f00c900090009003600b042e01c0000358074146014010400d826048418002c0345c41e070524064454540e540b2001400d000c81035924421250003000410168101e92100d0ba195401c0b4400400c02690041c000c0d801040001c15170354560780c0201580c4600b0610800507000180442d44a0070420028814028028150b0304050040c8171180240e1a9044a4512942c0041044000102ca8125040280006545c500e24144c2541c5407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190189163 1250 190187913 190187941
    0x709060e07120216030e1002190609050a0501150e091606030509030d06030b0a050105120a02090a11070c0303080106030e121602060307020a021e01120b0105090409030908010c030203 80
    0x200e00e0030702c44100c54a0758010241d904890074542400240d1115840300e0030010f003075821800f00785003d2840745400c035400d0b6000180600c1c41d0740742150703c48480911a541d40d8040e000881003150b1600c45d03da507890000b5404c0c001c01e80c1d14843c0070241c400c030610300b25200c42e000e40b01070f000540751b03009084055036101c0b40c0c40307481e4213031003241c100130882c0c0d19200d5401e45075102e10400860298507141020040024408516004584c140410300043e6213440810640b0400151000440d900003612603005080c441210b9a2156042c807000544c403482c080c02200c2c90380240c900b10f400e801402e900b8005c00d9001420340d4054112840d0030060945020303007099a030040b58400305403440010584160210740d9034090069158041c1c042740d02c030b0501d160060b503900e520000881c0720346607020281d0440c003001000740c40e40c404140d41c1c0c08800c454088185d0028141c060420707040040c20000e01c0d00c00c1e150343c0160700c48a480f030354405541034a07006c1c4040c2112020005007003014010030900071102c500c0d0700c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190190413 1250 190189163 190189171
    0x50f0d03080907050612100902030c040306110d020d0905120306061b0708070e16020102071e0f0602030c0a02011a0f060c031c0f0b120607050d02070c170709060e 71
    0x34941d403152548107845142040d80d9109680c03000c0001000c01d400354034003821a024032142d40b17a0b0404c582d00d40741c2000990004a40074400c0040c1400200041885508000d038440721710324481c2e00e0442c0768500c00d800d03070340105040c4141d2520b2740209030400c83e041040380c10424408084505504000d40080c06920542d02410180f62800310401c0040b0400d11400008040500480e080d407981c0300c40400801c80210703aa0015144a04501e40c115401070084981d4107130700c000c42c110600c82c0b0002c01070030702119580946400c2040010071002034158401940600c400300c11094030340c0e110f0240207003503802d101c1c84030702c440c1d440400200186d20f0b000359400030a60221886501d0b1003000440c5843c0d8007842010001c81c841000e00ca5010350056071040301c0250600009000d996440014012101681080798225034043c00c0010211407240f000b4008580c4031401c0589031000940b9014004407080d0460103501008203024010402c0070000c540c01054a59008d0044600d030442403410150020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190191663 1250 190190413 190190417
    0x60a0915030507091401020309040c020705030f070e2412011a06040b12040305070f030801050a170c0909101406011701030f0f1406090a1b080606060f040b0d0510050f0d03 75
    0x10301011240c2c000d1045c0d5029000c0072b8410020140300040003540c44515104590003030242400c1a0190b81c0d020418138150b601610040541791641448101c4c2d50400702603410703140e006c92640b04801c0da038034070f0b0124200003c400003160503615203c7c14200d40c003010026510540d4208000c001c42d500d6001a02c00b500300d50301180140703941d00e080039221071092040060802c0030144c000c600309a0041100c81c1078a40984901d20210f485007040d00084c072420601000d10b0344a0320307050701744d440c0c808009540824408103950340c414040030302c80c0940d980700301c000740030400c5c00302000106c3d640140d00c80030346540503030308401c0740d45140c40740c040c41d8101041c050301c003100507480d40045c0507095850203035030660030048030058541800c44580b52003500c002265007a00640b00501c15140340b0f13094a060f95a90b101070005515590108440744c0c1c010511142c903440306000003e01c00c2c900c04060f11503a00d098201090074500024040b000000d40c0e00300f107120350340c5805c0300c9142e030721001a8840d115507d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190192913 1250 190191663 190191689
    0xc030a080c030f0409020403110618040908190504090e0706080408030c12071d01020303010f0501081306050903070501060501031e0506150c0307020f030a120804030509060a091503050709 82
    0x62084030b095202d000100c003004000060001030640c070503401042200d00481010104e40c1c154020004188200505214505039600a000c282e2406d0342c0036080e6540f195500f246400c030102070b000d80c0f450400c3e0000c00030450115082040c01c29034003c0003907418001001e850050300b00310380a045044042d1001e4860071000c00080e40c861107a000f00e901d1000520b00c1101240782140000b031021095185038041c4412501803440c41c1d500000c15241a50328000781d8245090610004640d8104001d24000c488031036544100c004c200d0901c2850b0146000c280076503516031aa04140f425544180e0200e410140340c030000d403808014840d5248005180e8003404101030711020005039500e440458010191040001d007022441d0002000b800310f9407003690010000520383c001c02d901d4450303a040250400b030180480301d107035500c15040e05912a1080c2409801c1c800703414003080c01c40d00035121301c4004c64085d403000e00860350080401c1803480714a15003400030f854501c0d13005003d815580b0030314190b5144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190194163 1250 190192913 190192927
    0xb0f130503070e0702010f1506140f0c07050307060203030c120a0b0a080c0414011a130f0f170c0f10051c0f0510150c030306080303040303140106020c030a08 69
    0x49148010040200030101d800641d16144078403508030040d03a040b0099032800564440358655400f81c80280d401e8007800005040c9440c109941c950486181001000010400388510b142e2041c09440c0540c00000101049400d040506140103d07a82018055500c24001c00007452000c1d01103881d441c0804800c000c960f112401440c014008142c1490350000f00c2e0240030910b6070001550748040a4100d0f406d220b044200e8101c1d410110082c0180005815a161110940b408610050105002c41240440500e07907482c01c411980d0225080503107440c40700403041120007428803840051160361130203070801070270000010301c07958007040c03031036018480c0e000341400014001c00c10f0711392000e1403110280b0340862404460004200728000c1c000b00c1481d00011131100801065000c05a400740485038001c110a44404d035108c008000049040640f5070b070300810044002e001850049200391400b003003070040700005a205140503045201154840c0b4000285950001055500b242d042001166103d030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190195413 1250 190194163 190194187
    0x61504051e0402030403030e0c0a0602030f07020d0c08010506030d050a080402010f1101021612051c09021c03080411010305070504440c0904020906060309010e1603060509070b0f 78
    0x440d403107141c2d4014804000c2109240d055003181d51071201080035103c0004680c010041034070694025a03005a0003441015a141007003401041440e0005060038800301d12591004080701003904103954994641c018010b4500703081200e072140042c0707818010305200b5500e900401c8070300c0062002e8100141036840040103030091544023a81180d440003550303502204040b8550b1104003490850b0291045180c10748054800c45c195603070b03a04a906c2e04d520009000c0c103144050b101c048030607a8003e01074200c1da004103485012905080b0712a03121003c03e46002e0a0010740c8611601046041c50b081c0020008180d610200b100c1c2a50408290150b8400000c0e80c5492081c8080703101c0410f5a100c8150000907450042c001e441c4003940c10100d03262000c443c03041c00100b00098400a4000f29010301189682c50888051640321100100000b640501002c07800d207030128104811101100b4100d00f030052044501808ea407140a000080011500d0640e02080c03500c5500d500300b80c85d4101042c1845004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190196663 1250 190195413 190195459
    0x60312071b050103060b07062a0315050d0b0c07050c0303070c090b191806150203040806250e0315070306080c06041226030c190f0c06020a090f0e04020906150405 71
    0x10102c549060807419400402b8005069464505141451001c070019030391400040c821940d0740d10889004030354458820392001500f0460f01110340780149000e001c6140c5040002d8000c02e400703500d142e220503113002c2803002141c41840909009290021000d840104c105c840326088450700c1030b0b0020804084101e180041413560450404024000018220a0707400005001618450020744455440d00e884103443c1c1c1c070208100c0d1509040060960300103602030003411000030805000e9410b680c10051240c0050700040301d245012a994080900c00302804100300aa0100141c1e82e5502c0c2c2030502000300c0b090006110000c2400b400000409128051840c000c400241011102503d0b41071141e0034000740c0e0000d81c0441034030b000b21000c440107144141506052a0356907115028144203a0b00e90030041e6000e640164240980440000741c2c4000c1d111210005001460b4420180d050134030400030f0542014000d184903104132041d1008000f001c204540c2102d80c102c558240101e03041101031403035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190197913 1250 190196663 190196711
    0x7050d0e010905040615030b19031b0306150f0f03020105070204050c090607060b10140a0c05010b0a03050109020301050a0510120f020616030e060310030308060312071b050103060b0706 81
    0x40d0400e178002071040003402c5844520415030320305000c8072080d1403e01c042410245400d4408446603a020030220703c0d807088028104510342c04a1003142d460b5100c0d00196844204103810f50514814104070003049411701c0e4000e041004c105810742032468000906500400002901c12a40c55000c02c0b03a04c10200c00302c076240200542490384500c403a0816074014108100e00b103000d800b058481032407171441442e5a030446044c0c03030b0340181014400c060841d0744030321400d0100d50325075031034052801c82d5881c5e64244004500c00c80c00400e81031100d00c1818250307a00036120300c000e1070802052040c02d05a10300100242c48604c90303540580009414a45104c225208000e9004240010b140000e070b14140081e404282c040d40320a42c20301c40110502040b0b22048408056000c0c0d1090300380000f0b8860240175400450007011500c41201e00d46042e6041d50046204807508a5100c0040f10401b1000010b10010035090a00300150303858581140c0d0103125014006003007558880d0384103500700590f2011035034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190199163 1250 190197913 190197919
    0xa081b0a03061b09050a0b040902090a0e130203120412031215060509030f060405060c0901020115062106030c05040507180b040f080a050d0f051e03150607050d0e010905 74
    0x4a00c2d00c0f0b02c0d070100d800d05051100000904800021640d418030050f084c1c2155601c81d40545013a140000b000c0c02504000d03111a400084020006002214034001b24010b82000c0ca41240d4014a0320416180140c1450841d080350b030240001c00100c03030110000c08800d80c240c20240d2245048050301001400c46104580540c4d009040116134107a0107005040b41503170a800b202c8110304042c0d01995540700855000341540d00200010340402c40d00000b0f030100a4044c00042805100f80c02240402d40c420707080100010303034002092085589601c42402101858039003000a903045403a1801c16480a0190b240141d85590205c1d450501c6001c00c079010751080c14410700c1250715145c2c214111352081c0310f89c414103031442c0c10216039000c000c0303480d000c0d19038403000506104a404030151a116070560078102031190501810507600440780501c1c81601940591030303641c0c5040e090880f0100c280200c1c1a004501c140101c40c00101c0002d0080605240d07030038116603981071400121141011a08aa60 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190200413 1250 190199163 190199171
    0xa0201051b030310060306060206130204023004020118080d140f07060e060108070605071101090305030c0604020306070c200a080d03060e1e0c0304020d021008040309050a081b0a0306 80
    0x4625007504c1d8501c06540c10f039581445480da4501d8205c3e527640701583c0385055200980103074001841d0540c0102415000010182920001c0719404d01040d1081e07407108101d204048100400c56901008000c0c85214081a079039040f4241102c0d0741e526210003403070b81c0c1449841610403402d2403a4506441e00ca00c40340403115aa10340c3c0b80307884400b0b8880752510311024402c003000407609036030120310301d4182c0b4450755540d800c10201d52290381c103151190030581c0c10300010032800300105070144028016055402e004200504180c41850b00d00700d00200280704000340c07401c224002855401c1da5522180c0c006c207003014086000d8000803002d40d1140c3c03190324a031050480144410b0b0f01500b1000407240b5842041002d6a41c0880341d21804010115442071aa03030301c00040d0190501001071500b080c005014820130000c15804690b031459681100004207030424200401c00d0f61150710000600400d443d491031161401e076001d51b0740d200f40c41983c0b00f0600d006055650540318619090001d6412900c144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190201663 1250 190200413 190200421
    0xd050c130315060b03011203030f09020a030803010e161413081f110304080714150406050103151a0f030c030106031202100c020d08070509090106021c08090a0201051b0303 75
    0x440e88400482d000305110b070508000149081c2028250384c100c5451245920345100c51f6501103008103500015049015913408402c0702607240c5004400c05188148240baa50354142005110342400007050400d80310b44041f441c01d40d481d48020412a00d081c00b20410b0380f179000f0300326440300c00700c11604542901c0c450107042122058502d942c000ea1002d0211007000030501c503003500c0025200840b030203840024208000b6000a42c807001c81c04641050a00b610846581e1101d010703000c04c400d5400703070b4401751240014028066054003d06201030322610030822450150640d00070b40160040c41407150291455564264a003401401c420b842d0090007000800d03102e10700200740b510300850080040c810529000401000c80c4500c00b5590384036001411520400081143d00c590300030014410040b0500c0240142c0d200c0380d0400e4060103080d0050718200c1180300c007002104d005944600704100300c80d4207000b800314012a02a0300c0f96020729209a81e8498240d0300105103e5145843d0906d120001c200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190202913 1250 190201663 190201673
    0x10902040903020102090f0f0303090603100b07050d0801060c020109140d150f050708090709021b03120f0c0f040e070c0b090a150614040c140703020a060b12030d050c1303 75
    0x3440b825004640d0b1f4166500d03001c00b8041b00007442a40716402d0382c0f00300700c002424078250002c2e583c420590182450b815131540381902464018400031903031940044518111190041800703400343c020761410412840882c0c000819444840c481d11a80d5024424049159226280c51841c8071341c00003400000d105060701d82c80020600d008091050910340804206540d00c101440e50107200003000400f440c1d0700709600358000354048110030b03c0c07400c070210480400720800e0000d0080002c1c0ca0710b0100c0e181c0703041c0c0c0d1080d8801c2001003c0314001c140030441d68090074000420b540644100440100080d07a4554054038501040341025051500040c100903142c0b800041090700305104040d5034120f041e02405550550f00c035400f41c50b0318414058050300d0542132a500c821070001303da250a00c2549455031703031002240d220010950068005480890074850203015031070f0300317072010748070903482c085031102d0240c80b4080e80283c60b02094460300415080d83c0d448080c0c4040c00ea40c0300400012554910302 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190204163 1250 190202913 190202917
    0x2b122301090b1804062703110609070807030b150913050106080c0a05014406030a080403080d020f040906090e070e01050607050a050106080309150c0a1103010902040903020102 77
    0x2844101420242000000e042c6442500f0003030860b1040d0040a880d25550740c4007a02009800607401e1000c420f410780c0110705001d4015200b070003034035407002c0340882034806410840b0040404101d42e001c3e040c100300c0400001801b00c222a000007407106c0035254455400c64000c070fa05646640300011405204030701051085031414248200002c101c003aa40d041055155003910214951182642d282000294011001c10420a88d8000d0a9850384681c18449140d1581d101c2401080640c0c00150307200f80000c1394a56400c0f500c00c80c02032692112a50314404035101c2e5000c000c18402d008502246c0851054040d17803101200c4080342e0b9110360315007036007400806451240c554154105030000340030700000719400d000c5d03543c0c0c0100d0896503824802030024070707445001e04480b144a00401c1b00d010400030f11502d80a006c0d030101860b039a014610030040041d502c02243c0041001c200300c441041e00d00010b200000603402000c0b0441d800c55000040c0c01000340d180041d4002e0b0904141030201075040d40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190205413 1250 190204163 190204169
    0x20706020d0204090c0f0e010503180c0405190b240a0c0f0b0613090b0103230106080f070f060807120905030307030b13060b0306060f19050406022b122301 68
    0x80d45440780c142404044503040c0340d000347c02e0b02041c410001310707040502d0214500700103244001181d9640d900100890111801152843e1400034015410401e041280c040c00203d4002100c0703450301812045e11005018000c540302c4403c10000203200803004e8003030b540000480d50441420807180e101402c002d03078450710807140144185005522103001021070b2080c10030003600512180e0703140e800d44e911601610313546c92050070f00c000540c4040395070354024003a2401400c445400b902c9a1800d1085251030803080d40c020001d82072240d823003844001d501645250380101d4601e0050301d407994001c0e803070009004800c8050901c4c00004204046641c041e000117101300740950300441001d40754070410045443e9402000002241000403850030318000c80906036240c051020315192031101240700341502d0114200d04003050000c00d04201c40ca80610a4060508469000034a0304038009000080402c1101d20303e01480407002c5103001098040d80f00f581c10411600200da0701d1401ea021000348080244 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190206663 1250 190205413 190205417
    0xe010e06011b06050a020423090108010b180c120403080603070503010e070e041419110904020d1b080102181c0b040f1104060b07020102060703090b0a020706020d0204090c 75
    0x5012900c03a520803001c400d00c20042000051441d1901c0e96481c000c3c22010b4058013081d80c0900c00814051b070328407072017440c540031701d2140c02c41c0340c80742400d1101c0f0080503031124207164500b110540342034462540e03003100103402142d080b42e5035441c03240616481c080c0050401c6802d009400300001c01d0b40200101e4003d02d0110100c5008a0f620403c25081e188007032a41c0f0b002d5044030740d04000c420303030401515400500c2406e0000f441081c58507001c1c03504800c89070200303500030300010010034881103400700000060181c0714503d0a28094010a50849241000400e9440c406800c20154815103d03544068403021000759550284e807040c20711946811a90b980c494124010000700344110480c40404c4540e0000c540040d0b0b5569855680315650703412420f5540e0080d040c2c000e9150f40e182e03c035040c060006024116161420360000a203084801450441418503290300034012074104945298800310f00c550144c1c1e034103030901d8480083c3c0250b10210049600220700070a040905030000c04400340c41d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190207913 1250 190206663 190206689
    0x609030302041706100b090102010e030c01050f0109090503070b0a0b0d0c0612020414040506060f04090c0e0d0b0c0a05070b0f011706010e0403050a0306051e0405010906080613050a0b010e01 83
    0x20514403500e44401740c43c2c1a600c19503214003000245c07801405881d000c0380500000802c809151905811a8840c2440300043e075540d00820800031842e600701d071f025002500f020080150183e941a036203100b0000058481b140503000104000190b801c0f0035182d001c06009a440d1841314503201244040758024000031a51407084003403804050b00c00c1d5030480d01c5034112440d01c0d5240000744001010060718031078010382d040203c002c5078140140184010403040c0000248019030210040041540d4440103100c0d41492981501080b040c0d650780b604441003c41269440c2502c41d0107807103603c903903240242030304d25400c09c201b20b41804580c200d0403107140c10388540c84003001a82e041d80380c0f0401d00901003a07d100201140c0400d01c902d000c0c201c1d1a08a080000f003403616000000c4680f1107100c0102c41c5400581403003155803d240c080c0e40c2c010705952805000703490409401a0f20782030010f24840702c0701003510440051240401030710307070306503085180002c255031140c0d0f0f01e298408007401414550250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190209163 1250 190207913 190207949
    0x120313020d1b0b121308070206040b030907050a060509210a03020a150501031e0213060b090a05151e040e01120c060206060a030605070e032409071a0d09060903030204 73
    0x850211042d065240800200d60f507a0310400326012158084180c980d01b00038084000181c0b02c4000074409070140103061030f142d20313008142600d00b00d00c3d41c016a0180c032144c10f081008a8000c0261803003c070003102c0c0e10751120041030500303401400c1003038140824400e1662400900d40c010541c403180c41d010b44000c45200868000e03140a5136400c1c803000707010300c84600003041c0890680c000480014401400c074400e0a1a02c98584103444550304001204200050034104e05d05d01510840010002642c8034901c0c00100c40107500d0070f00440c4410346952030060341030032140e01745500700c3d800381604000151055840d8190084072501d01101200c902200e958041402c500010710075120720b070000c01100ba614150b91300e140c0641000752280c014040e0b02c11031341806a07428826095040078202035204844400701041d050041d010b4000a069044003c00b40200c40c0000c144544040b0303400d001395590f0510341075480c010306c0c52820150502d482d1022070010154590001e2048480d520140c80c4a005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190210413 1250 190209163 190209179
    0xb041a070c030b1e01030c060e041407030915090605010501110705091b0d050408090a0611100b060d05070315060509030a111c05010609110408120313020d1b 69
    0x82030040291104000c05400c0000034260070791540e004090003d58088502c80390341c0c0001119080c1c1084074a1400b88034140f1910f070780240d03070010329441103a09124112001c55280000140a40003500301a01e4001e010b003030164400d442002e0a8162204200c1c2c4046030401400605013809440d000035001101c13541c17001c000040e403070300f030343d400801d031440c540c030b4130400c010042034103054000d2013420602005104a0262140c244114021102a42d5a007124400c01500703500a800000a0000c1c101c80d4402c9610001610041062140310019400b400c21001039094041c00824030009410103040185c00c86e40754201070588444100195440340e00d80c9801d580c1030154020039034250340020000700200f55121290448018080c0007510919003c1c100c100581489080a94075a03468604c10001e82c5900d100c0c0518555011801c2401e050030310300d503551622640d20480900130b0000c4003147e400071070071900141d20369004080d40500a414580755081900008400f051041c1824000600030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190211663 1250 190210413 190210417
    0x306090601020a200f100903030e240307140a030c0318121202040513090c081903030c030b090a14010b031909060e030a120b0d020109180f060b041a 65
    0x50350007000740701e159101000700c000f045513030144154000404110005940c40f0424040840c000e55521840301e00d0550401410030350040d40e059000350300d070101e4500c90300c612418080c0d800040b803054517035070b88529100311058611f10490400c034840c0002c04800c001d4165200c0101c810480c0c07021b00048004007411203ca40d4183d2001d8110040920103c502c0c0d8410000e601c4400c44000c0d0043c10103840301d0204c1c40940750085c0c01003003e59901603000c240509040580000e08881c0020318007511400c00e50725807845d07910703002005d1544481c0d08501c4180650006011401d001d0000070042ca084c0c070881000e0101c05000e01141a008000800d9500c03507141140c5c811454103a0084903591803c5030f4000911b520907050741c0940da01c45605003030b23034400e00051403100b08581d1018900181c26400342b08032200d50340c0d80d51052403110300e0070006076000f001d840120f40310300d444045030202c2e011103500948108032485c1a07103844c041c1d0125290350080c01030019a02c00d4282c2025030000030401e44c03114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190212913 1250 190211663 190211683
    0x60f0810110f030a06090e0a1502030c120a0905010c0c03030c111c050403170c061e0609060409140616031a04020a0c140a17180f03030f0f030609060102 67
    0x416003001000c0140042c01d00441d0001360541c400640d49990340c040f00304a42d01d0109140168005d05444000d02200030011005015000340c00c510b50704220790b110b260303032181407040b404036591680020302c140740c80e074071401210fa00f02000744891081c0500081c00c0900341b02044000ca49056001010070f8810340d009691442c06000400000042c050045078015103011070a04200c01000b020000603a10a480719001070020461512416410242818043c000300b96a451b4080e00000035000c19920351543d421003803d444200312610742c0000728000e440c01c04005000d80c07031403643c00c0f40c4050000500d603128581058601c070f00c0d49801c04048081d81c01c0e04c50840c14804c07021200641d249016030080906c40c4280c1091a00780409a89000501c1201c04905c034282c1c01c001403010034170003485030302c01c1110000145a40750034460389000c45150707101081c3c180200d030862140c0101e51010022a1103000000c0000307900e0324042c45d0081103a92044a003180600c40190204005500009414600e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190214163 1250 190212913 190212941
    0x60e010c0c1103030408010f09060605090403020c011812050c0f01020a020306010b0f090a0b041a0f190201020f0c01150501020f1002090604050a0305030d0506010801231201060f0810 80
    0x84000152201580160940c2c0c4043e4140020440060280024421180818030b8030802089441c42d501340002110b0603540100c0c000c0103800104000203a0100b15500309040900b07098042c051480380080104225400200c10308161017085410711a0018008800090031924010003048401c012038031101200310081d099031000c0d00507c01c000302032015122650f0f6003840e507414600b00c43d0020781070003e243d01c54201110000b6003070002d036030130316000b80906c0c6d0800b0f040c0c0d207080e0000401807864443c910801741680e40801900604920030b4045035240040c5082054840c1180d03851580200700e5030200c0308044090b113800040f95400400c0d91008405c48c0005480c160b404070080ca4069446984100c3d400001044040380c6990b41c00481c5014500503001141c07148090602c107012900e0141504e03041c0f1021400402c0084291080a280b1190000900280b2907080b00840c1d580a440e1498a01e154280300f404900b030021110200121614402151000c5c0e00340c507004012100700d040d901d50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190215413 1250 190214163 190214177
    0x906050c040807060c05010e0109030c06050c0301050f1c0606180e0123090111030f0a0b0d050c06161e03080f060105040905090319091e050f09130b0106080103060e010c 74
    0x1650140c03004205c1300d4040c01c000f0030140d5207890294216000494210049502c89101109018444c45020350254040d42c03054515410721340015160001d108806118111100464482503401e101840641d54882e01c140300180d211040010088441402d0120f41883c2040e00c509183c0c0500a0244225051020160182403040c1e94440d0300001400c44483d90b4891a2040030b1004090083d442404601401005401c0c20810002a941c1c80c001c0720b41b14101d09500c08000c41c501003030180e035924048400c1c980e0342401c201c1c040000b07000e100001e40124490760204803003031001c00c01c401c1c4161099468040076507405450210b01704087e50500c1c0050302c00c0c4000d0101030303030690007180c0002280c0200d904000383e0007015a030311b0b0040b0703000b07000042c001c8408100c41e03014002a0340490002800c4080b00d0b80c103020214a01039060a00503100c3c1d55a04049801c06081800e6449026082001642c0c151384500014040134800e00c4101ca0003490a08551000c0c0c10602c100d80d001c0c400c640c0e80d45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190216663 1250 190215413 190215419
    0x4051c0803150607050a060b12011406060a0e03030304120e031204090f0209040c020106050319051513020d08040501021504080a0804030210230108060405030f0f1207030906050c040807 81
    0x20091010350081d4001d801040f80b200803d008203d0170310042d1147c1c03c04a40011518107004035507018500010107681009007100c1003184a940ca240d10110954180d0784420b003041f0122113805443d080c45400d40130000511040c003000b0b106007540700c0290f48440080401c42d4060590301d1000e00015100144140001d10200b4855000008a4040202d01505000341600010203c50030201d0400141c6c0d50f8140030000da08082c00604400c0d50500d801c81c4046160f52181a1169020540c00840090160010704501c4407400312900d4690003601d4409843c0083c909083d45900c13a00900d40580700359260b0100c0382c05183c50f4603100745c1e40030340081c1c01c3c007000d600260394008019000b00e003903004011300d00b541c9154a03c1a801c4400301d0020400d00304000d074410b420400c0341070300107401c150805401c00000c548000103c525840e0444101031b681c104040b045031850103a80c2c0c284070480529410321000940c513070040d0382003038000d680070030103601c44052202c401d104620035042603400c5a0010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190217913 1250 190216663 190216681
    0x807050a020c0604060503060306090613020105070c0b0406180e0712181b1a090319050723030f070311150706060603020301030b0702010605090609040f050f0304051c0803 75
    0x19100c5152240100d40315421020b00045680d0480e40280c00094004802c0100501c0c0401505410007134040140c11182018140a800924500b4000e8140140003e000040201c4102c5200080460241e200d8480344c4601c00104000440301800703100004551010035941240c800c003d003d0103003610f500400740c00048408001c0c201803100c8655003070b0880040408a0044541c41100404054070401c100d414420032041d03c00d09115500074a00e002d200960b180c2c1c400148440d01c52000741031080d01a0284d151203480c1c030120750002d13840d010406840003a1203482c02c18a4107080340440030f641401901c407020540e103400c1c6202c003900700d298110040a1070b080400b070010b00f1045552880313282000701e458920a49060707522440c00258004010024055004030254000c3c030f035480240011884d05000030700b510340107400300d8441c1400314049410026400d840f01450b076070080031f036013141c0c00e0507101d99240d40051040b41e024100c5065000348800f618407080042c07950010041c1e0441d1100502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190219163 1250 190217913 190217917
    0x10806010309080931020f030127090b07030606050309060106080a060f0b0d110c030708090d02030a060e060903070309120c1d071701121403090a080a061506080705 72
    0x2c142c9102000f04201146900c3c0c225900342c02c903840c040d0040020380c0d8010800f48160000c01c41d00c80340342c41401510a00c031800710440c1e0448941c1c9428541c1c440d00a80751904018400904207441403608000004000318180117900c070310328544003001500d43d500700c180d0350742c40200e0759018580c01c040c0052108900074001c85401a0700355400003481030704e41e40d1401807001c0c190844e502980300856440c103c003e01c1c0c0910701c40602c600c01501e003806410714051356079000d41d110003820f01d00d003c100382410703032100881c2c0744040d0340007000c0b5050b80d10581810402801043d00c0400180116000603002c45000402c42d80c03e158103aa6000d20301c0e25210307141e259008248800c8501e000144800265a005480031600702c1011400c40d4402e07061051020708240d07001500e040c544001c0d40010480c1c80c01d0540c681c19540d030416031205103088407100040c15440380240465111076107140c08a400e680024002c03600603c101c1d41000300340364200c0c141034032403a603128007800207081400180c4414032030b00c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190220413 1250 190219163 190219181
    0x327090709060806011805030307050615120a140c04140603010e0d0203090108090a080403081201050114040e0a060e01060905130504020f010f092102130b010f0309020d150504031d0108060103 84
    0x194046c40d0340c85000190a580c80200292100d07840f076000c1c0300d00c081009002602401080742c544400d02032000e60340b80c6450b002100600130140311003030900d03c603a040c0320f1801d010704c00900400002d03607003d807103444050055440d94065840d01000d00312600300003520b0804008650000e500f020281401103030403040c02000d5040600846562034005044407025002a62045842d280c40380c2030401c40e11032401c0c050b030101e4100010030310180c00500d05801190251501c604905515a450320040e2001e0720b140e500a0501c849a0b000014604e980425041e042d98811924038022030454080d140680d2020758019502903c2c10150300095070140000911503c010f0504005d0303103a4840c144205a55494849040420b508201104601c0c0c00404014544201070781084007441080000300a6452030500c1014036a0710301d0a030f000d5580e01029000e040d42d0141003506021320034814038024000c1034404030302041d150303500d1020b040800c048a002908040c8c2d1035128560740c0030f00460181c9003e00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190221663 1250 190220413 190220447
    0x2120f090f12070302010f050418112b0f02070c05040b1903030e090a090b0a150806100303080c04030506041704051e1212030105040c02032709070906080601 69
    0x109000a1611982c0000784444100400340c42c0007480c40c0005010426180c0b00c00c4d0800c60100b0041c402c140324000702c101c2c090580507001500080c0c940038218140701d28500007003d03a07642ea405142c52030544400c8032000c08002804c0c4512100c065011041c3d0040400092641c64900000e1105040541c40988540401400fa4200400b40d4074200081c10150300300394002000060416402c0c1400b500d4681c00841d880701c20004270300641c0b41c0c2e0071228005040c0381c049580300c8030300d44254480003110102501c401000e4898604003c840c13a01c4da0005031004901088900f400070700000000d5080e1021690040301401003942e0b5599076590f0303814207070b20300c03104020301344404903141e02d4035084040c45141c98000c20250765031400801058104a40b079400c49a4804c0013420134202032003003076a044613002c3e20042a030300003030740e01a070450255119a00c0e010f030504038690f500107140c280720500c215054604008545800c402100d00c001c0c01c2c00740300085403c0a0108000e5441900a040915045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190222913 1250 190221663 190221679
    0x5011d011413060905012a0804090e10050709050a0e1b07050c01030b04060815090f060c0d0b01020118030810031202011a0405060904080a02030c071205060702120f09 73
    0x2410014050300582d10044441c6054a024025541c001000303402400d02401d1140100850740b1894600543c200d03404080010204101d104000ca1003041c2c401400181c00244003e2503440003090340c0c0c1d900c0c1c0c450380030206e05040c08104424040c0d034144069030310190110308410304010b00240e0340f41d07024011440c280c40b904169030030b00c0c0d5041e003c3c1408610510240c00c2454141c5d000600766220002c0c402d01c91850950100140d8800103485030a2210040c0011510307038a0748107082c01c0036040c40e5540041d000c0c0c402045a83c00b80800102201c01400310708220a110f404012402c860500b01021883c02c460b03405a80800d005881d0301d0352000411034005149500e1303550f0901620311050407080540c2d1141424002c400c040708100018440070b640800040c900400040c130b8600010708007814646d4006000305c5824800d10441782c4a1203c40201d81080e5525804070300500b400e04403e403200c0c003c003004228a5440401d00820b0000c0322a050b505010000300041016400007096990080740 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190224163 1250 190222913 190222937
    0x4170d1103040210030e0c01030c0513060215100f050607080910023f0a020a0f0b1e060d1506030204050f0907050303030417160b100f0602030405011d01 67
    0x214040d00905503020001103880c0d0509106001c51001458003010615003400e00d099010000080c4140c0400da0900e40809d40030701010003512144070301201c9038554488848080b8146c1d0b000540e42c04d4038100701c148a401c665482600e401208841d0007602560040d9800402c02442c012024240060040e8030091800c1c1d80c25000410b21424080c051002d078015506440d0b480200c0c40f52880c847c3e206400000d03041c241c0e00c001c0c1078203a10401a0402c2030f4000318010b84020301c2007041c480003641c040c0020614003a42c0c20700c1c9007024000c130303503505080141c4c0340d41c000c0891105210a01a000181210080c641156071b610f4825229060100c000c030703912040080542d40c0c41c090781e40640058070725148941041100c050910141d5044913000c2c0d401007080c00002401c04c2e52040300c2014091109445440200c0c140e80c000c440c01d90043d046144a81c1031001d04480074085a08442410040d68042aa912010f903124011441145d0114038690184c04510304014024402000149040603003915 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190225413 1250 190224163 190224187
    0x120b070f0e220507020a05100c05040e0403020c031b09060f1302040b130506040b040b03090715020d08010515120c0903070b07030e04150302120a12022808030417 71
    0x81040c110307007481d5140c007281c000802c45114103a0002c0c0300784090809010f40e40ca86903036030090403d0500d010fa58441c803001030780d441101074070701926100820450f01d042c41d09009550700007140400b4800c1c014602040210240001062000c4a02500d02451603803000200030f180000010031a0304024801083e0610490510080000c2c19244810301d0b200c2d8014021148009001c0d00901e000e610204810301807a6030030020340d000c132500d030240303651742c1d64403a001c06003000c1c8a9030001d22001640c4041c10300180c0c000c180403019520555541c2c2c0070340e90b07902c1080912441400c00700180601000b07080803200c4044011503100c00c5640b9024500122840030034580744031544164001d00c800301c2c2e071070100365200d95410074110b011101840070413941030b5180070f030105510009202d46c0c0b00c0c00c401681d000c02400340008458000420020b40401d401002c1d4131002189840e030300d21007100365600712020030380700000d0459411049880c1199100d0f5203202d40b584c1c24101d41d50a000e0b00b4030034114a80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190226663 1250 190225413 190225429
    0x60f0902070515010f080606181303030204050414150307061407050c03060f0108060106020105070206072d2a050303070c1a010303020d0f2d09030f0f0b01120b070f0e 73
    0x100c07100b01142c5d46649060394850a00e4001340126204140442c1c400300700c90215113450ba002895158083d00800b040c0c07906400034441e6601a50300f140c00e10050f0440c030151113840d207124803050515542c0c030300801c00405440383e0703480c020b0340040f44000075005229600c50b406810440d100e401107136020307a50301d4002854100c007141d0441c000300749103006002011051020750300400346400244818288248040c1d1100c0d4020b08540c1080f2180112800d044545003400d64040e42034060000210a4403400801c070302203582c850401c00c404102110309858103a4944420103230840c02450071616400403c86040d80e201005480c900c0b00501201e0260035080b440d140214820780042100b070344070a0000c0c0c40c00c0340c002d0b0400b0601104c08000e1100030041d11034655640c8014000114201801b001518030449c02d80014007540303040701c803070000c01c6044452000c20300d01030030005409aa0302d126000760700c4102d07000145414040c0c000700c3d14050040320011f4241c1e40b04d040c425036804c0c5640100f0006c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190227913 1250 190226663 190226669
    0x308060d15060302030d0c0309061202120f0114150d0e0a05030c0c10090e0a0504150609150b0403080412060b0d05010903090803090315130203010212010810060f090207051501 77
    0x40380c2d0300c0008000714502001428003a00780c605149088043c692000703040c090740c5110708000e0000300e18403801501e1f09a8122203800e000000082e020b401c0c4070340300342000b60090003035041d001e107009041d659074a00f2802c13035001e1014040405150151741e882d880040c00018584490a100e03c50320640040e605001402506a000f8004c0816000440c01c004111040000c003101b030241d400028040280c10440d4994803034000c030004103131601d692a0030901c45c400b020649000d01d151090204540c4030b10741042142c414a080e01700f045540340c0c2220030580c4150700c00200342042c00c00080145012003032411851900408002905c24a031001240402d41200e1048800b80d648100507030806810004510140c00303200c00460404054001095548070f5070b02140345400800303000921150803405400d00e00c958041c0080d074036010000e03a940e848070001e02900040d03000d1071101c010000d181c4c0c4510011a607540b40c10301c00e9640340005000083d4402041956140619031a03803a90003802c10b1002d0003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190229163 1250 190227913 190227953
    0xf02090307120605010b030f07080601020a05060106050a17090a14010608071205061509060427030315090b100507080720120a051b060c0f03030106030c0e0d0308060d 73
    0x144641d1803400b5411130b0016004400c40900602c2801120400c500070141d108400d42088042d5403200c1c40180e107031254030342008040d4450301c000400d0141d07125010b84000c411503140c980800411094440300c0e03d80880308050298061080400820300007458001d08981190000542c6511605114104001904800500203142c8006401c0081c01c001d403da0040018004e49000000d0f80300080500350040c00c100c0c0308946800c0501d4116104505500c1410910180500d840000b841c0190150403544040c112000900358002024402401114080e9070010954003840c000e41d5020b841c0d81d0400002070360200c1c000d11180d80040c0711013004090810100a4078950b8a000c0820045070020f002c114481c150484504000007900c0061041c1c1142241400310303184502c200302051082c090380000d60800c1c030904984510f1504080000c40c140d03009940c1c14005250009030a681c1840303203030141a0041030880c41003020a11a80300720727800910080c805545020381c0d0302ca5003503c144901003408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190230413 1250 190229163 190229189
    0x203030106260601051c0501030f0204051308160c090509070f080a080d0b1203130608060f01021f0e0d02030c1b0d03050307030f020c0f0d140a030f02090307 69
    0x312294201c810076808a1450325115000340340042c0715016400081c050b94148032001c90100310500f44490350001c2d50550700ca04001c0343d80d607400e00800d07001061b94240e01035071620002c5214802148140461560020780302c42c07900d04441004950080b2440c81900d82c43c5010b81c020900c090b05006082c040c0302148020a03046060801c189408030782c03940400c400b584040400b0002800782400c0d9a0f0708001440000390b0b40d2205008940301203008408814607010008a40c10008040a0401d083d50155039940000703550304004d221800320034190943c05a40000d48806405242500080ca00150b5620104100c08a44099072070105410f18000241e000445d801240c4481002050803001c1e00c0110008401c0600000c903510714a40c01e00641001000800a00700c03500039080004407403210700302103648205001a4580f02d000314034078410140650424000d0262040c0c0c1440d081c40c0d4600d016a1521b001200158001d06044a121a40741c0d000c0c07200001a0380c00f4007007d0020074801000407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190231663 1250 190230413 190230419
    0xb0f04050d0f020909010e0c01180e190c020307030c06050601030e030c0d02190323040b0d020d0c080606030a0c090308180910080a0b0402010c05010501230105070b040b2502030301 79
    0xc03007540390090160345d440c3e2402150300c00d0944d001a004400380002e007405014a010f00460002c2c4100c0d68101e681d58030420809d000203148051102001d00d010700300c3c20026900403020498582c400c0b190040e00241d43d80c0381500100c1c0c1e00c2c2e440550050014140004d00f5020300202c0c81c1107402021110b00d942d00301e00703c0001c00e10380500245100d0000e0901b41ca01a9003650b50150920011086c02446511400da152070310002c43c0080341c01800c00d6110046d182c0b520b0352a88006548840780440580b41002a04052140540740090082c10001c12603400c3d0ba030741241d003000924020081c0c2080242076407000010030f00c40401007150410002c20551950044000c1c41003401c40907000306011058003004102c200c0f80030036140c4156902048190b40c0d9252400101c5181c4810f040c00780140d442c0c0400010076030480c0c2c840c400b41c0c081004e00c0c60b21403841140150f03000d00030704402800c05100d01c030025000610b94001c0390f034080d41c10441d20300030850401003028803140201c00701015900020041c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190232913 1250 190231663 190231669
    0x307080c0c10150801060e010308030405070e1609050303091e0f04020d020304020f01050a0f050310081005040201020106052e02030c060702160e1905090c04090f02120d05040b0f04050d0f02 83
    0x40f60180040b88024042c080c0380558030394806405210203043e03241c021002c40d04014044c0056002072504035580f03801820194a81c400d01c00800c40c00002003918100d0010702d5007004800c2d80c4d0f0154000f803115204e900c0b105580007807800c2008802e580080002d01a80c02540c8500c060043c2900f141801a242d14084c4180710300e602085001ca410311006201d16079405501444a0040842601d003144d2252076020003000080d030305400a1145004039425945011466407090384118001da0080c4a02ca07600d01c01c0c00240b03071051114908481d08482d2451403245009440341ca5055103204680c1307408403416030350303081ca40240c90030b00058000700e010544034140902c01340040c0001c06060416410000c0c4103d008242201c40c400c02c0707a40b58400211240b009024030710040070080e1048c4120001841c1140404040c00c500303d125400f043d200304e04510001a61040500c626151503140c10b04020b00000310743c000c01001650300c1c500f004080b500c0d45a201d020384c8402e00ca1000b080c2c11030464410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190234163 1250 190232913 190232951
    0x1020703030e0d032a090302060a0305100b0c0c1e0418030906020c06030f070909020c250503120d0b0312120a0e0c010c060f0e0d11010b060307080c0c10 67
    0x65104041c10000c1001c17000d14241001403174038450810140000249a0007914103045551010f58040310210f410900190180c02451043c9015070050f8511615005d0302000350185902150855001126181d0681856424ac40c0b070303800da006d0b1042280300410300107020b8035460f801890380104021508420560801d000d40c0c0544007600142c81c042261901051b0207010003070010f05080342c20408103034900c0c080d125180103409041006c0d075580202d01034680c0d85084811400c000c80006240394010302c803000045000359100240500345202c070200702802c1640054040c18900b6039107840300d00141e5810014440100072038140240c0310001a403000092480081049084500340204130780300507000316000f241200c090030b040d00d110045052100081070082220300b940ba2501c400e8501d4030750700060f031200c4038607203a07100741440880521075403c1e82d04c41d1307010a8000200303002050106010713004981c1d02c1016101d000e410050441e020318a06071101143d680140d82c3c43c103000150700c1d84810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190235413 1250 190234163 190234183
    0xb1b10230f0c09060f1b030a021203041709061c0b041113060f020a050f06160c05030913091b05130b091b072301050f22060e01020703030e 61
    0x58150340342d160407840720041d8819065190310594000620340700040c506030a072441c2044d143d10b0700001610040c030183e92503000060300e00251003540c3c40c00101c0d0b049041224803c6502c4410341722980750480911030550491101c080d880301c0705004001c82e0f0008600b1020002e206841c012464031800b000303020031150400c9607001d18800030402802030035010300b083d0381141c0f201e00d031007a840c5003152012403c0a011240c0100140140111411110400241d0354001d81e0b0b140c0d200c0d400c0d40c141c948152018002000c4c014602e40040c03005c00c02500d020005800c030300c55601804911014156548031600030010010320307100402d030038107200d107003072400800101c20700300c01b0100510120640050740895000b0b288250940c404442e0141e0441c03140c3c06d039808503030700c15149192200c02103c0b10482130790708031040240e58a0000050320140c00c4003085ca0162010318110b0075180400d002d07200d00010040f4042e1001d0f40c9403404a020800240300800c1e10702d0180c0d90004805500390301450500b4081d00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190236663 1250 190235413 190235431
    0x20a03030f02090319030203090406031a0108030a08041e080408060a1a0f0d0c05041104180507170a06150201090203070f060206011217070308040506100b1b1023 71
    0x40f10000160b01c0000e40c0e80013540a10000d6007111149140407451442103464060b089418003800008000099001c00b0107035010003105495a82c8541c030150b40d90040203d000c00060050000c5008101401c822045010110030003040448240d00c03207030107e5005911901c1283c4c0310f8401c20240c41c40ca44158900d22401606542121854000141c0001000d81c5043e100e02d902d00540c1040241d0451a440180700141003440b28031007031102c20101c2e400ca4070400500c2070042d195208465105d1140b5032007a04551240200d01d585503090101400004010b68030040d5510408a0039102c002118103200174654000f103000d031100c2c8141402d040c610b52200c0941e80c9000000c0c0081900401c4403419140100c8d0410003c80e42400c0581c2c01200044455001c070000007036880c14540d019a40501c50b81c040c800726a41c5480d201c0a0010001c540c0c072030a083c440c01405001850900540502c03898217903c0100c0d001807825604501c100c0e025211111a0741540d051400c210500c00c0e0403a80d8411503407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190237913 1250 190236663 190236667
    0x601030510061d0f030d170112020a0312110f010501080d02032a07030c080c0a050f180603012310080d0c0312020d05070c0c05120c040902150a020a03030f02 69
    0x7240a810740c5002c40046543d000c045510360041d803542d0256540c941c00090460383e44203402e14010b031100c0000ca00011480581d14004146041021074001c16507038040e00c2d4080061a50712020080001c01d5201e40c10810f142c0b1003d9400c08003006488041a40f1030000544c82d40740510092030b01c60f01411301c0055400c01e009800e104040400c0302008200c82009a06000c800030b500d2504280c4150402002c040266001040d075450000e8485d900c0c59003510380f00009505d0710700300412182160302e99940400920341424424030389208a581000001e0000b00390021090140b0030120746007840c00381d40100c800100300f442003c0c4803e0342c0003000c104010b0b02e0b00403148480203103074124407040a411700229100c41c00384441554111030303c0e41902403003007105041110340280b13440c64000342528150503211000c9180d241c0030700300c498400c03204001450841001c1051001030700c0c1d9140141d074403449004c942814040110000d000c4510503501811403040303580f40180403140013081c017488142c81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190239163 1250 190237913 190237919
    0x6030a0201200a0203030d0204060906050f0d09031b150b0406080607050310030b240a2702190f0809060601080103020402131a090a090b2d0301020708030601030510 72
    0x1004004501d6a050300345000d00e0b240010707181c603044200500a41600c8006038003c0c0b40380b074a0780030340103607415a030700c0a0b0310301c1d5212412203590180c48070ba0356020320100301e0005201400ea10159025100f400c04090200e5104104000c03107903403002c1500c44214801a21000c50307031900c80c2c0b45100c04112020860b09082c21003031a52010000c020b001400000004602400d122070807181c01103034824500203003072038000c00040b02d108404001ca814035505480114080c90480d11180070346d0062501c04240404003d20004c000c1c0724480d4041d203040e0700700104060b0304a0720203000341c181e05a8840302c9242c0d0007840000e144080050a000d0310f60040018801e190380d1080285045a404540c0580c1360342c04c5521803115080503030302c01d9503c1d0508078042c1d2800c010b00c03c00f8103d1842c084819001c490399500802040d207049100289d840384146116901c02c982c40c4102c110907002d2404101c0100c0103520200382242d10510090700c0e40c1074080304000031580d15010745907011910784108011146 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190240413 1250 190239163 190239167
    0x1504061403040b1801020c030a0c290a02070312050106090f080c030303040803092406040e03030c030105060f0408100218010f020a032006011203081303020c04020906091306080606030a0201 83
    0x161100440940404c803001800e00c0075010f4401c6214220143d80d40c0d02441000500800059207080718030010010b22001c9101e185002c0b90807401d11442c1045480d610b00301243d00035400078904500340140c00425002941c5980300d51030103030200340c581c0169103081100b0380b040119294880031040e80312000c180160b8601205403078015034012403603070322074032070a00041c00c0c151216100c0c4035a5402c40c11041e0f00c000280e640034003440c8182c0d0304010101c403a030000e689a1004442032000074408200401003030800310014010400804942e505050b00c0d0900755003044161001030041070307008111002c07560520b0307007400700c0040242010340000000c51b4000c1e48960100801505110340c82200040301d00c0c0010245800301490403c3d20460740e1038104e0b01c00c202c0c144036000c0c0c00203201d100c00143c0824081d0110110690103030001d0080d001c0210801c00a51701049102e84c0200b000e03c008040c1d42c82c2d8a166001c42c5a5283c00803035810b051000f440d190100c001d109a20a80c44002c012015036 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190241663 1250 190240413 190240433
    0x110703090501051b0a030819020c0c06090429040f0209010806130b040c0507210801120c050406080d120b18060609060313170301060504090b010e150406140304 70
    0x1501c01e00b081c984843e00d0f44108842c1904c2c20314400000d00520310074900b00b43c2e0080220703104810a02d0501c44500e002c1c240d55049001e810000d0440e03520015000005143c00d1000e8081404002c0010480419403070b6003040c3c2c0310008060b60048484c02254501500d0310f17000d0041011183c0104508100c10100002d0441c40d015103c1401074203170060b030f442d0207495a001200101e030050024002c03c0400c00004160f5400410152961742c5040003000d04d0100c5d601402811034200e640781d4007107900b070018101400044881c00c40d4216140b01e80010396441e1030295500074007640d40501009075098401500307000071504120000c03481d2284a114944d00c003005003104e03804030070300080d0560b10f18010441c6881144200d682c01600402040028661a43c024020510034500314011a1442c8001300c003034002030044801013101404240f00042d07080e40703e050202070500d00b002400300d01501248106403407029032103030020002024040300381c2183d50820303030524180f809451441c2507190301a0070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190242913 1250 190241663 190241669
    0x20607080c0c010f0c0504050405010902131505070f0308040213050705040b0a020c040f02041d0f0613240816030c060f050403080c03091f08071808061911070309 71
    0xa1808600141004002d52103c031403804c203020100203028028070301030030345d4000f8414903200340d052800108004a0301e000762410b5000311000d9600c020b080c4901c05542868110849040000c14414400441c65074807110700c2d4a0f01036112402039043c58010310104015148a40000c1810f00052190442c0c1c4401201c0c100c4030b08103041d6440c0c006d0ba4404a081c03e40091445038000d042900b0841c40d0b10469008004451b1600b820340002c0c40e692404600c1c0300000c6030240074001214001a0315030400080d8280405000c0ca80050120301c1440599504c03000e410401498064001c002c1c04807520030440e44003144111801c02d1080d500d0340d078030503040c0c0388140665410480100399051f0b0690094058030040c540c403c0d416270f210701e140749021341c0d00c7d00300c400e1462041d000d00d218844580f0343c1900c1c42844a000766108852581c4888094842c05003000c40030441110310100003a40e500140710103400303910158200305c0741040c0100002c0598000203004040020304100c0d607400250485200011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190244163 1250 190242913 190242931
    0x5060d08090607050102030109020a0905010815190905040f020a21021003060b03040302011a0f180601020319020609010b010f020a14010b06070620030c07060f020f04030507060207050102060708 85
    0x9641c403060042800c40c000c40000070070a60002c400030416040310340151010000c01c0c2d40340026695100700458682800b5241c2c030748444107565803410b0500f01030700c9115071030004105040240743e40d2400b0000f10b58081354190b404140901c0c4c6041140b1b00324400c40000d100f4480002584954088240685601d150009100b40c0046801c604287d00035006900208041c884907500ca02d014200680a049003609082907010720f008044d01c249000c100320003a00e003010303224010800714100709040045001c4e00250540c8002d0003500e0078152305481140600c40c49501402840c10219102405d4906421070b142c180515001e9907e8901e60001d880100c29822a48134240e010440044900400b01c880380a134100d02f0010b505018002181c1200010095404010b10a5030340701442035802e0009645001c80c02c80d04102c1c40c2c0200e00103410000313082203454001454107100d1019020b240e441980100d038540c004e04010041160140a950001d1800f80094041c41c5054400141142e00050450365 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190245413 1250 190244163 190244167
    0x120702030106031b08060c1201150c02040f0e151b0304140604060207140706050412020a0915050102150603030d1d06150a090b0f0607080c0625020105060d08 69
    0x106640d400d4000d40000c64100d60f0810001c501c04078507401d9a050b80c01201c2c1c01d4030409001c036603056880c00880d0f13030322400303003d6104681e42132105d0b80d004092415a00400c0001004440c40580d8541c0311b1006401c0107800006140100561003030304101421780b00c0c1142c07a004030304000000c0d868180402d003000120a142350f40b03940f546800038500d44542089405885003000700010802c1581c000c1c007409000d200361040b00001e44103090360350b4280e8092074002075002c0c0020004000e04060b090f0900344014401c0440580344c40a0390201d80703c907074510341c0400100340200480d5805015040b00c4800ca40c030100c000d480c4c402d02103a078174424468400b0086954103021451021001e000c0c0c0c00e00c0c0c04010984510341007040d21913070261b988440d503501c0f600c0003100000e4807034840d00c100b01039400041d14071240040602c0c100800c0d604105070075664000100003281c070881040c8441813041d419500140c1d2000445108842d15105401c00f8105586c507040901c902591a510307085000742d841000702c0c2d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190246663 1250 190245413 190245427
    0x9050a090b0607031817100b22050a0e0a080406030e0a0c05100309080a03050601090b1201031209031704030b0618061e06070f02120a170d110301090506090a0e12 71
    0x19200749503a1b8000035031480c543c2c00d500284140030508003140c51658000b400280001030410061008041c45003001d07851a04500450b00541d0300003e510800c040030000b2007081003d441c60504500150850381000002410710203142c1601c00d06182c908141c006089070f0a90340c0d1401414248d41c002c7d14416514100801c16640c070a41195040a600c819141c1d19010300700c0015020306002d0314901d02095112401050110020051b115070072401d0750204407991071511042c00180321644007104009200ca00440032031207541c451802858504001555a0300d98103101030000009071016104020300072100c640440403003411504401e04683d41c0c100030790042c142e030000743c01c4e03410b8040e08904041070040030710942520030220030f0300036282d03541540040032003952100540d40c070003092520003008540100e004d400181c050903410007000034036510280c0001d9801e800036072002c03c0b4246c90388104403032410681e14458200c0f030983c02c28001c40a040d442c150303c40003c0c803414409400d01045003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190247913 1250 190246663 190246697
    0x2120903010f0207080712020d1b0606030b010b0c06070903031d010e0909010603110409020d030807020a0b0a0e251e0e07030c0f05090a0b0304150c09050a090b060703 73
    0xb640354082454085503289407602e010039541e00049425903002008081c0c00c0c0603140045500c0384d40c104a41d841040c8175000d02d00f1030000e16100b20301540c0c4190384000120004581001190282040705002a01c0700f04200ca103c0c40c040b0010030200c10031481443c20400660846449001421642c402c801c24007120001282c0300b000c0001c030700f0b03407103002e03c2c051054022042d408441580c0c010903003106010080402e01c03056030002c00e0b000350040d10782c02031040424841c900f510380090040c415601201019104c2444005090360f0001c01c480e41d03420707000000c910070854007111018110654910340712031503d401c54509207100e924010040c1c40001001c1841c59140c010140482d210501c10301d061540d0000c00030130400d0000700225024854440c041c0d4000c00954450b10b0000b0f1500e000703982441c015075101d4001400445941100c418464002c10b000c0c05003115013070243d036032540010318100810000581d140e004030300c40c6107003419170740710346d01e071031044884103501803c2a0111915198907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190249163 1250 190247913 190247921
    0xb0105040e01021c020a0e0901050f0d14030a081512150a021b010b0907080114010e040b030a0506070801060504060e0411040e09010b01030605150d0f0209120303040b070e010212090301 81
    0x10740d04031038000c074038182d010103a4086c009400560340c848540550717000c103020340c04100380038890f4030002d1810512080d1420504611000d031295950750900d42c9400706141c0707940c21980741000841d41001c01c1002c0320341980c035101c02c000c03c121420ba00030340954444071384800390181c0301503c00100c1c50004c1c41c016800e404a491001c40751900d000354a24001485008201c2041e0b01032013003411501044481d48288407641c161a246990564011440001561901300e4180750035007080c0c0300e82e9800c5041e0380038040468400c0c0030b48003412891030300c003000034401d1030305070000024032105000c140105648110b080b114a5002e4400040d041c144030700402d05c9010341d912240508000c0350810401c08419080110044000e0324144255511181000b112000c800d000d000b6808007070002e42e1000d030082d00b110504028114005140c1101c000c0401c071180700036103000615500000070b000030007000d40039082d406a090328065801041001c0000c1d00e03890b550010411004021841d0390303540e903081d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190250413 1250 190249163 190249177
    0x110c0d0803060f0f190e01080606030d0302070213090f0201020d08092a03160f0503030901050702040207150c03020408060c120718150f020d030603120309060b04060902070b0a06030b0105040e0102 86
    0xc01c2da070385e00c074041d110041d80104038083e10b17034104200000000c01c10f0000902500980c1c00034043c0c003821141545c110025000164180e921a00c400c02e2180d20401034410209250700800c007026800b0303507034000a85840c851600301001c014581c81008000e090100e01c69601140c054101402000712314800c101d4403007480c0409515000d8041c004071000c0e03064211030202d40680100c03804c0203540b5000c05480780030307529219020650801c5802c005181503801012003901c166840c00d03102c51510440750441d00d07030303004503008241d00007024006418104500780e84041005400c91900d2401456001031100c0542001c7c01d02498040b44c00e1480380764030090b00a400080c800c2140a105140c004001d1414031407202c01600852410400c103e1090141c60256604540c41414480e1344400440051101c0441644c0312655401161030996960003140010442d21001603107541983c1440c40d070110307001c0c0064909601c1c200041000841900c09141141c100b1900010580c035060001406882104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190251663 1250 190250413 190250419
    0xd020403050607080f0106020708030a0509030f0a0b01060e0906030705040e100c0801030b0705070302061f170a230604060f14070f201e0102040803040303110c0d0803060f0f 76
    0x10403010303a6108013864071403007542c0d1000041e84d903104810313030b1581900d00618403582c00400001d03010500540040807064405000c490440d03184145c1d05044c544800307821500c64801c07200421a0f154404d1960103406ca00b11242c90260500c0000a69900910300c9150700035a140c0e00084403400e014031107040c0350300b407074101409941c900e040000e0220306d00740400c070341d1b1340100b1011401c440d10070002e846049a140c2c00074900743d02e4680704880e0443c0c80c00da01d9051070900c1f1401042070a030121007102d40302c81c0c5070000c1024442c2c130b1074208204d9400520030227030a0322400c4649000440002c11541042c1c1102c000581c0c0a022010080030340070280307601c0c0503030340e94500f8043e866601c4914a40f42c0002030791081c0e40c1440382010a8023358440031004041e0340822144000c5080302520714100703002090005241031b507200c0400d400c44c0c1046e44180c000c102e508112039542ea2045c0183c0310340e03900c111001e60751014641e9031890740d404054605801286201c540c00d440c3d48a81d42c070440050741c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190252913 1250 190251663 190251673
    0x42001050913320106120207030807031e0f02120112020907080c0f032505031519170d0314010e0c0c01090618060b0301060b030412090e01060306060e0a0e0105060d02040305 76
    0x3480035258001c1017803080d1030000b803a001450003605401d01c260f410955140d0f444000f10b80304c0b200308502511242400300b40d0b03400901440022804144505011000d074511f0140e121719802c03200301c0d400c0c40140c1c44811660f0209258200507030b1a4650103521036000d08000445031038460036680980201071007810f0038640042804414110381d5400b602c02519809170328507070254140111440c0c082500c440b402004000c085004a107081204001750f030501c4c040105610759103a094801d512405841030b00e444d0812007145030303040e606008001c1c8200c3c1102802560354503004000d0440c0360020070005d0004800700d80310b00c0c3c801080d000607102c1070f007028003070204040d02038268502010f00e100803103075586003107000715460034180203505c2200c6118491030309583c0c03161501c0c000815454151810040c24180c0411000303400003255003e4000c0d5a8001002810003901500c17681801c0d04541c80f60380100740400407190031001880c1541c206451040e01d83c085075a07c80040d009a4000400c0341c024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190254163 1250 190252913 190252991
    0x604030818030414241602010c0206030a1d0a03050901140d0905031b06040b07030203250210050a0525050702041a0906100807030203060a030b042001050913 69
    0x440181d4503254401250300d0500f02c2d00f031710704130902940705c3d4400d01d81001c82403080c20801003242e04040c40f018010706000c51403500c1079001511070b5104460700c003041582c4958400710340400d481020003000304031000b403000450644001e0101e014038055030781000071403291514101d02a90540d00d02070003d070001e1100c4010741c5030140d00c0b900402001c0320700080c4d1501289407284005112070203260003445e80b50182d103400c103044000e54001847e007040e51564584112001c146c0447d81c10070492544c0c0542464000100d03000241c0300301401c400316280c142024440b0001442c100702d158841004000d40d6244103800d0162800d000350b0703c003e0b500c1468120359501c02c0f981a070742240318420417283d07402d6590f10302c001c00c50740c1107120041500269080c2c0006070b2480c002c2c1c1c01103400071401080044216525614078240c03404c1150f04448090001e1038500c500d907003d10071740300d507810242010f501705079001001c40d1440300162041c00030251101301343d5503040b000c81c1e4240884034071540c0102120003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190255413 1250 190254163 190254179
    0x604080a05010f11120c0f07050706051210060f0e19081c020105010e041b090e0a0b0114062b051810110405090601120e070906050603010806040308180304 68
    0x40344607011140d03410303c000d0a0198900d82c1c12200d0308882c07040d480b521611b4800ca0103415030030400381071400c40320800260000c5034003080528010162507440a5a42215801d0241e4004020708103a00364041c00a050181940200104d00c0651907450100266455940024141c41708000c0482c6040d1001a0110303565002140c0c3c2510444140c0c80400201c0c1c0440c0c04901b260780034132030b944040da40e202c040750000c0c1e0207a030030368201224445442c4c64161105211400c40703a4064500103030360300104080003001103010455004011540c03680d880404807030042242d6100303038004461311404800104404048801340d0300c0e20169100404c01841c500841100c1c8405a80d820080440c1714940d51740301101d206010340300c0201c0e21076070464100b0b490f080c140113907400050034446c1801085006000c03403002620070b07818014801001805001d01e000325200484004d41c001500070a02000140080540064640e030007540c0740c0350002c07040e5550244858000e40c0e140407030200d80400240003800e90303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190256663 1250 190255413 190255421
    0x20d020406090b122404060b0616020108061009090f0204080f0601050108012306160b0a0b130506031c1b03020607030507050309120a030f0207080d0b09090304050f0604080a0501 78
    0x14400391404e241440803802016503c6050300940d039502d00c2d040c0341d54065140c40e4108036030403034440e0b05c2c007241c1005408005105508408140303200c007051340c4081c00c259a4015507451300030174240c5601c3d400490a000c0204090f48600032954081d80328404560b00031015411280184562025a41140b9414150a032122400c0c8240e600040d170b04000410006140a504002ca010390900140c0d041c001900344211a00300e41031184500020100c0ba1020440381c00020744035899030000060700c0c0300c80c0c8017013010311008030404400561600c02082030a44000640403600044070301010484a4a13403800c840e05000001e801102a201c0b81814003090f8000441c0d500400c402c0d10700b03200980d2003810486190004640d80f15280d4040d0100d2030703c0b1031a0000500710803005140c003040c2020207400c02c1d02039031701080089481c4240018902000c5840d03205440d2144421101d41100f0b040c4a8403590740d13809680106807080390501d91420a507541c1c84100c4001f84004c0040d1003040c100b03410041c0c024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190257913 1250 190256663 190256681
    0x9060212060a060915110f0616020309090a0f060308040e0f0109051501030504051204140306060a032105070f0302060603070e0106050d050606090d0c031a10050d020d02040609 77
    0x140e80c20408500107240405041041e90b45030b6840701d566500c0c280041586501000c41c0c42d00340022419030030b1b0302c2401400030015081c03640009048030708000b4450a10f4180d0101c0080454105000907913003aa50005142c0d003014410401081c60b222407004000202025031004000103000507002035075040e0014185d105241581140c2c22603a1303100030302d400f519002c54049981b80c1a4810503c510340c001e50010307412900420842d203c0b991410181c3c1810360154001c0f4000030340c1402081034510b003c010a59101c03100352404000c0f180b81d5510b07400c1030300d94251006812004105804403103480746040c2e608840d001140088102650f08000c0c2d2190400d6034524028000c42c0800305080f4802000c1da41203c40039602d452500d01703402c20540c003d00010701296448102048050181e40d50000822841800351110260091641c40c00c4480700e14284d0040d00d00d2504641007280e10b482c004018070842d0340503100003805401d2031002480c80c94442d04001d522500c0d0240110307403a94280d10590350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190259163 1250 190257913 190257937
    0xe0604050d091208040308031906080c030f030901020304060c0521040504150e0a090204060b070b191a0d03022d0c060304021c020a0b0307050307030501050d05120f0904090602 77
    0x741034035403a6200e01400f1120024212410411003000001c06400081d036010640e41500e0500540614965080d982075510110b0709a1041c401c08009250a101840340280324200440c40c00d05001c0020f0b40701e02031442800c081c4030081c242a000d000003030000081c800c00403020348a4620010101c038482d03801500965018502c0c110621300b03030501d40c2030f400003602d2071541d080496a542d03118480140442090898010384c580b0070005140700d907103010f05003c600c10192684d640c80c00301b010041c03500b80c03241048400da0030847c00d002007071030270b2000d22081c3c0c005462050054100d170030240c7c60244141e00008810a001c42d24424408000200c075402d035450005854280007544104041c90005640283d449940c10600351201200c00000c60341d0303988050303c4400300a503250b000031810f4204607001000b280303001007040a803c1e030601c00c45002d4082202c0000c2644966140c0303c0e40c611032071020030860800007500060b040300c20340a480c04154000d000f44541d41040c80c1c483c0c042d403c84804241 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190260413 1250 190259163 190259177
    0x1030303060b0315040e160e0403020c011b022e0201060504051003080d0203070311030a06030b1602060f0601050c1b130902030d08150a1508090d05090609040e0604050d 74
    0x103420b0145030b007103900a11003000d524020030a1a02040010040e07a80d200d03460344907003600603110541490b14000144841c00d0712109620385420003a0604106045942c10880c001a5080501101243d8404202d80607981d12041c140a50f01101d007007601c0d074000700c428100403016031000c1d075030541005041d52001d07a000d00c01070b00e805803a106611078600004042d810240302c005008103842c1e0103154064814600456030345a54840304440340c0c000d03a078040078903840340010700500c40c94466072031b009900c0c419038120010220900a4a9000180501d0900950351000c84c0d1a40c0c4900c0645a80b4017011040d10094801841054103e040900640b400740d5410510312020140c0da108a0121a0f0013a016206030307002507000701c810b08030007003810400085000f424109512080f0448001d81100300c04c1c01d40c400134014000d005440c0c000d120b104a6844000d11401e0b003a07010301600d01040c000c5d074a00f030311035071500002006040081d141222500c1f0301400c04c0f0601900048001d80c280c8180c1b1248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190261663 1250 190260413 190260419
    0x8041704050915010201290d0c0e071e02120a0305180601180e0307080a0503040c03060f0e100b01050a030903110124120c120206130b0c2401030f030216080102030103030306 76
    0x72001a100e400110220003064401c042103051554008e0710030f2344645d5161300e01980b01e6094004101c415030b203440004d03801c41c2401c080c0501d5070062614090307440c001001040c0c00c85040010354440d00a0038010182c60310085141c1c0d40c80d0000040e034444c0f01205070340c49580c6034050203040818508400181c2c60420041e0399a010011007240c0480e034100210701d181803c407090035503c0b07900181c070484003403112080c0000070465622076403404003542000030550081130920140303032034401d4035038109092500b25800d8280c0e03004001c5903505521401e0200d02024681403e6400c4200406912025400e00341d01c3c640200343c10303820811200d29195010042915840746104041420900501040032010140038041c00f10040c03011491008101514142c5070040391644100c959000c00e580d6500480c6200f089482400f441100e410501d030016100310f00c01f241c0320740c40c0d5010300c8042c083ea880d04213604113040c4207201910550f000c1000414810f40e031109618002d51092109400187c03501c40c000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190262913 1250 190261663 190261691
    0x2030910050606070803090708010f09020a09181106040e090307021903170313020d0308091921022b12050906151f051308070608041704050915010201 66
    0x654010b00b80034200030b08112003541c0340e008070b0348068500d440030f104003400003d807410309000d003c0c29000c00000c04504d0310040d10520915042c42c2c0c0160515034145031029128481800c828031441d0b402551a004c0501d504012408900c02c076004021004a0301c4100405040c001004003034003803090302c0301701000780b130003490100302c007003500000f0010036981402d045000100009590020b005201031550a082640090310500c00004102d0205550608110034800e061001c204074000310036001301460710655880000c1070b82d2450350743c0451118070100b1a900e01c00c00029035409440c1d2001001c0d560900e0081000004080082c0c0010f000070202810f020a103001300c90290b046440100700c10b0b00d9000340c0300069001c0003640c54201485d8113a10707564243c9001210603161140e26520382e502c520690802d81c10010b9001036440e076000789010407400e5800004075a00c81e801000041c06d00a07aa00d08001621481d071003030703900c540d4960900801d08040b403112903016500b42c00801450b510140c032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190264163 1250 190262913 190262921
    0x40806090a02060304031211040e09010501060f0c020d08120c0304060c050a050313110405010b090a05040204050609060a090e0103030815040b0a051201060314031e03060f010309060b0a0902030910 86
    0x4020340003c014800b003000240100205000250344e220040340c0d203c5410301e05101c540041d440b00703080f9400a8188001c00f00e0a100c0e29016050f18509040602010301015107912410a0000d0103000348901c81d000740143e24007582c82c040c0c01602840e042d07040079190021a604240e50556810385000301900b00c01c0e000c0c000f16101403206864250071a51019015604a6845401540d1094040315103004654076803040300d01a01240c100152030340c01c0c0310140042000e03117800ca00c1c0658030400040c0529562031090b80e46020044501554030808000200e84031801c1d640590705411f1100c002108054100030b00c14880c40c08400b0540702070b00c0403820003050324500034040b81c2007206002c00703008604200940f00741c10214580049100344d603c0d600c1c80b80c2e441400c021103d00390404107022402d44a030501ca002400c0b060f113440c6003141032003000612504a000c00c1c00341415503500354501002120b0300450038140c001050101507558441c00880698800c4403408814001c51400350708546040c86 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190265413 1250 190264163 190264183
    0x11d070803041d18060a05070917061513090303020a121503060e0a020901090b03070b0a020705040504060f0c030f0b0a1410110a1a0c092d0d060204080609 68
    0x307640c00c2000160000d102548002034040c4c807640d008030100d448851000c00030140944e000c110300140034544900c00824801e1140c000e581d211401c2d98200080020002c1c040c0c1e004021210305c1030510904100007051f00480214150300d01c2c2c2020f00210030b05406902500f043c0c1000e44900b1000d400707c04a40c0d044805652a03151a40c0d9100d00074008180650721070794078494a03604440405070282c001601c1f02c07009030b0004104545950000e41c017401c0900c4070100407c002748003513050400d42000a500c03503030940604c900682d5624001006e102803900714050001316070000300901d6509800003000b5050544071070900c1814004d03000b649062012101d8100c1d83d03510780c1d035005c8180a6080050141c2c8542461040000c0c0700d214142d0604180304c909801e2b48a08900000130f000050780800318035005001c0c4404210512810480f5164004400140b400b010351007400d5120700134082c04410301c403003103564101500c0841c0f441003007c103900400903203121000310343c4282c0c4c801c0941c0381e454200603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190266663 1250 190265413 190265429
    0x1401020a060b210304150f05180307090603030305070305160e0918031c0e070e0705030405072313050403050a0c05030c01140601030c02010905060610030e011d07080304 74
    0x400c440100e0869440141e024000403c401101d920409001c6115800b8050003e00d6403c00502003086807403040c08281543d03858200a0510080514040d00310b004074460b1000111500082407025076041c40030710040d1182c4007040050030b440e410003d004140480d41d00b004030746000c0c0070814045001c81d20054208490b910381d0340030304d02a81403000348034002e0031902c401c038401da018800546003400902005c0e000401000d00c80d002030602401030340c03a10701c899446508160014450000a082555884001c50400301d58036215803805900d00011617000c83c01d00710044d510703000c0d10640200d01941c1c1c90801c0f03802c0c68842150001d41d00c2240c0050741d0040c0480e0081103801062400307800000300301401041030780e0510242100140c00d541c3d40145040c3c940f40000704100702c0d9a054801d81000f090503100030070600d103065640659a410103000c591096500d402600c48461107900b00b129000c141100a01840d2008660408407460101540c201801034840105811000000b40c5086a09032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190267913 1250 190266663 190266673
    0x2030618061e0d0f080c0601090219050a02030c011409070509010f14030304080d0e040e0d17100f0b0a080c0c0a1101031b0e131a0402030703200c0601140102 69
    0x400306000d6a0b08464049034100c0240d105180c0800c0220050502c024020014150b45401102e212400c20070b050300003100301c03407060140001110140700305604201d41c6040c1942c0d5040742c400280e00c0c41c000e20400d02401d60070b01c4039000c000c0c10000c0149006010182c00c0351a03064440040043c0f4510034010240c80c05610003080151000003a07034105084405010380340341c01e4903034100a003801c10a80202001c558030380e200c1401c0b4102403141e2540c9480314405015400c000d40070081807510001c210108080000022903005800c1c0d40740c010041c01c1c034841c3d26a005a0361240e44401d900011850804940d100d4001240b0840031021502400d4624000d090324680c02d94440c0d142d01308110003d81010b40e0f41e490340540300b4584507803144030030a50710b5a0840301d14103006c00584440010300c80d40d44508059449081091012a030411010110307009038403540e908400310700a10506007003104403006508808990054140103082c0d00c0c0c072200c2551656a02c8903c004007132038100d25003e00503440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190269163 1250 190267913 190267939
    0x503030a02211b010c0f0e0f01080402040f0f09050c0301090b07110a14011a04060602030a030506120712030806010816030504050c03030a05041d0408070f15050a0203061806 76
    0x410440c9070400040506020b00f001e0012800ea445041e1008900d4a269564003044039134540010740c4d901403501510303140f01c424064101081c410064440420b051001c08000b0030210b554507001050701c003100c00410003010401284460140c0711303182c001d07591f41c05024520b99050a06000350507841e50003c804e441c032a00c070620119402c1c100c60581d04039901541a001002034084940f0285c220248070001c1902c032844600070b100d00b05000e65091040d1310740b030710400c403054001c13095520026a6060000f903d59599010620300903689070f501d100d6000740940810720089090b00d900c400341c02070b9201080c3c3d581d00001511500c0c4140c520302c5005d880000741f00000e0b0310075080070b44e006101c1d82c203440329034001030301181c99500185502000301c1c101050901c0466050859401c10200b00c0241e00e58600301500c0d01c62452007040c401416102840c2c55040034000c5426030b140c506141d2031030812044c5006c0c1040c50080d0403d070b460a100d01050810f42e00300c8490304829074007480000303040c2909494 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190270413 1250 190269163 190269193
    0x9050f03060f07020307020402040905010513060f180e070312080a0b0d08030402011704080d0e01060f0b0915040915140f043603200a15091b030c0503030a02 69
    0x401003c8104501c81005507400688940c00a04003c05c044800420301d035042008208000f595031641e1010039240c86010403202d00740c0341c1003000b00c1d0500120880c1c00081d00200c10050035070080741c4840c07442600e000008002014810300240103caa50b55541d81d290041010199000600c0003a400078000480c5c1d00401c218100944d006441410000390305401c280411070f110804440950381100081103828490415000e0b22a5502400000700441801c10011518026050203040486000440c4a40c0c480c0c0b51011a440462143c5d1000d0751103650f24810305000c0c1c01103000940500000080010701941c80426a042c0b0100042c0041c1c10b0440b00b20a000041502810701134080420610800700821403404c00c6400c0d01c02c101d01d01058012500340030700003e1503c546494405078068907282c2a40d400315100250726445080505c1868031204401d000d000d00c0e0002806282d00d0101c0281110b075210b00c1001124464807101d8001640c1c1c07001c2507164081e0100403c09600702002450300b501c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190271663 1250 190270413 190270441
    0x106030e160b0f1b0c041802030a0b06030a051f11040b1608130608040c0e01082a0405070509030f070501050708031306050708010819030f0e01020106170d09050f0306 73
    0x1032403070f440300b0341814500308422060018004076400b064200c3c2590048a04042c0a01c8200f00e44000011000c14030642c04a03540f41181403014005201150220f5040d0382c041c0400300c4002d411000b10fa41c14900c859266082540c00c0115410700e500c0c11a030540c0c0340e04440305941c2103803072400045044c405442e000d410000842d000450f0810300410881c4610b40382400544081d00240e9105600c0c0d14042c60241c442d03140c9508030320004841d103001003041c80e0001650107109a5150329440c0c001d083d0108103404002d9035010150720130708000400c402d4590110181806980840071148006495240e5a4445841c0d0281038006401009410007140c504c10081d0b410003842c076101e0b4007030704140e10380c00d0840e0f00c19182400003941000040010000400c00580113850203282007802c2c1100b680d015018000031280c48c010b00c83c12000700100d0341c2c001c0d13020500900c00709001d481c03140c0c903480700d0507150071030000094080b410b0517101082d242402074440d80d800c44082d00402403a11114440c0d8006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190272913 1250 190271663 190271677
    0x3140307021626030717070614011d0f01180b0d0204090b0402150c0309010c03020c0d0501020a03060b0c0a0f170408012a020a030e03070b120106030e160b 68
    0x140c0700b00180201440c40e40c0d442c00004100c00341d0956040b40340e21040035a0000f009121a50b180d10500c00704000c2081c07001c02822440c070b1105601ea642d805490103101801c03003142c14000d00b40c0c07140000a40c00601d4450348080920041000c08070740da030341040c0c800b0b100c030a01075200032855186641aa54809074401c0e41e8481008260708488901d80e4001010f0300c41b614001c0310207072140d4060004504185001044201d00d1407102030509038002c80e060381d207000b02d03002d00b410403080c41d0f00041414028810f9034900c800103040c14a403955181400e07400303903100d0262000002c6c13034007800090307044517141601d0040601c403000c0d221203442c5483c0c0c440c600d45400c1041d1090001c2054000e082650200100010b103000d41c004900030400200c81e8803040c084482e10802841818201d00f500fa90200324100520340c1030518203601c00c13882010901e0100b176504a605030007000a404003103c241413244c80d040794a50303a0244100c1c40c4d406c19803138440c0124038001c070801901620034451503260002070b04070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190274163 1250 190272913 190272917
    0x180f020105090303040b04150207080f100203041406040f05100c120f02040b0c2a010c12030605031504020301050702030c1c050702040906050702120408151e04051606020a03140307 79
    0x40584800c0741407400c1e441548234030000004901207920080c0c052022800400940d4050002032080c3d685458a03070124201840c0ca8580c0000080d00708000c0707030040c0f005410b400c402c0350000d25140c80d12003030103907940106458a11855000c07288044490080060541072a580c80c1400e2914411a0024244060940407010b0b000e00007c222000b0b01c00107044500d83d400020701100c1c40c00001030074240c40e0100d41c0e0404842080445500380d81200417100181e50210259410040c2150100e0090046410003a458003540840c66248820b070b03030b211802a40200c000300402e07129079900303994a2141c21680c0440f90400314405a4449e102c3c0c1802e400c51405003407180ca00b40300ca0380081d040324078103130044a01680d5202445500c5504101d00341e0b0090348034404a01c2d00703082100c06a0340c0e8544440c0024004424070000d084090091582041038003041c001f12203030b04042c0340c00b90715604a906903108411506100081b4144001503100c0300c0d90f0035444410f00b0880c0940404070a034001003080c42 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190275413 1250 190274163 190274167
    0x1104050906041410091a0604120201110105070c170a020c060c0c19080c1504051201063308040b04020d0515040c06020c030309030606060304020a030f0510180f020105090303 76
    0x50056040700f0142c490503240c0400813a040c1044002000c44001c0045d040042050003946d441c1629201d00b200c050390304101e81e0000341e42103880100c035002c88000d15000c86500380014080303d150025100f180c00d52080b0600045094010340020041c000d84110400680c0002c0c203042d0141004001000040204015500c849644601051320700e4038240107240800907140c010000c0c41e400707000c155920380044071903c100b001140c0c0c3c540c205005a0042910440401c0030000340000250b0202c0c00030401c640c425030f0741c1070305400382d02494a0390440385c1d00d544140d4005400c142c1d2007030189510540c1e000a98000c1c0e900c40e40c0a0021485038002d0854151056000c2100100070070340c0028030441c0f01c2c60f40c540f44942426002070501ca80c3d00e140308c0c06680305208582c0c0c80e03038001c102142d001406843c010744903a10f078000198501050b62015101c044403482e11001d00c000031a51380188003ca031300c20301103c0c5050066407000550400003601c02e288110300200150300c14070040c460540c005045034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190276663 1250 190275413 190275431
    0xe03070b010311040e06250216030f02040b1507080703030902031608070b07080d050a021c020702090717060d030315120209010803030f0c03071b1a0a110405090604 72
    0x25040d03080c0c1042d180c00040d86040142072416011741410001004081c00e0380341030044181e101d040c007440300e84065402d40f42d28500c619200308411440817400c00798683e4001e030f483c20041d86401d034554003603025909190300c1c4a15800d013501c0215400749a5000c081c83e0813001c0c0c070f40c0065500843c500b101016101c030690b102503502080403641d039441585550281500e0441d0940ca013a495620400c4004410300200021542c02800e844a078942a07001040d255a03040b00040203124401030214203842400c40c1d040121000d5001d0b100c0d00e48240d8000e402c5487d018003c1d60300070074683c5038100d040761352000201c440c1800c10b4892400392182c00c0105c3c6242013501030003150b4105400600c03000e202051510154070b09810300d82d0040214002651443c1400143c07100e44401c01001c41420003000800b041d8074611030383c080701c8001600284030310912920304d07080e00180601e02005074100c0c61140840e00c0c0b18014490031440c11089001c1c1413420b403074201880700e0030100401541d8800d5a0304500c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190277913 1250 190276663 190276673
    0x311090901180509010b10050c0f06040305070b070c08250b010920070503070f08040305060c220602030412060e070803030708090a020a0e04150c02010b0a05030c060d0e0307 76
    0xc034080d10020b20702c2807080c9500c2c01c2920032614010010020ba81c10720303401445c0c0e5103a00e066205071000c030389400b690f07030300e501d810443c030380404d00071041d9a6125140410043c5980600507141c2c0780d00c518110490303038031110012030b0311b60007540300a400010b04221409000d112030f40c8684101400400b2013055401c10303100c11802c010240c3c800e401886e110544400102c0c00680340940da603a030808580d08000c40707601c07070b02d41d43d00a4201c001d00070300000291070103002d8900140e9008507405070880c1d0baa46081c00d5481141d40009a1100c0007240100e6420124002100c6480642c2c40c2a4002c40c182480c2916040d00703880005810b5454668420003d41501070502084002d04114002180d5900303003401d005001000081c81c0c00c1450704814241c2006954a603111401ca445020020040303480d0b80c141000726140ca0260803034000e1900d5100e0a40ca501074205040c601c0080303820101c050750b66814191203da00c0d1309816441001040000c02a000f150b2045025803160001ca070700702882c80c2d80e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190279163 1250 190277913 190277929
    0x350406121d0106170303130602070203070902130510020c150d0b04020c150c07051c050f12070207050406032109081510050d030c2d0803160f0f031109 66
    0x2039980d00341d443d0314090001095080c401158031250300010f600d107184c00c80c141510342c01c64403001440243c00043c00c005554041010001a116296046542c1c5510044c002030f000001c5c402c4501420f61040c5590701c032800498441291480540032a54420301c0101c441c0103680002c60002c0000d65a980d040601d40307961003d0b00c201290303080100801024940f10300901c0c00000c1010384411010800200018804603011b20041428064800d1104600760107648070b0041042c02104144d002c14840b00004c1040d4119000d01e116400b561001500c5a0501040d90780e0b500015103100d08502e180d00ca00e405801c1103104052041c50101146500c030000e050600c90200418410081643c05000d8241e9800b00c02e0002040c04540c1380c50290b00c01d9038060080741000701c0151903094401d04c143c6a4003114061051706010500d0350045802907413030407140070380082e514105c0c00b5070b03018a1042c03914000e41c2590710710001505e51003d0041000807c038040c003180c4054251075441405050004d46403001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190280413 1250 190279163 190279211
    0x4050402040e07030c180e030d020d02040b160b090f0a140a0203011e0605041b030b010309021906140403030c1502040312090302130501052101020903030735040612 72
    0x10310280246c1c0b60613072480e201135010b404110704c02d24005882940c07201c0002100d050a0080301e0140c0c40790300c0740c504100207002d141c0c04900c90210000c0c143d006410882c5142103013501c912074101c000e0700d1362400607585403807008090000d0744c4084070a901050001000e0002045200100c6008105940c04a8251141014184401d43c0b65120301035a40724030340540805040d055404221040180ca251741406010a810f00141070351030300d181e00d0740e91090300000d00143d009055176400d08006c1402c1a80d0020502c508030008202541d100011a105800c0f10100ea806030390f031910904054480c82c0740329400800a888640e82000000001440c18021030032601070f0f511070745155441d50040c0012a624915080350b101d140c0710044c8159951081c1c8840c489a44201c5151040c008000050091140e156110360500c03000c90030804100000709100c18440fa500c0b821191141500742a94160380405026010280305000500c079103480303061180908440c207e070200348010400d90100656001c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 190281663 1250 190280413 190280423
    0xa090906050103050d020f060103060b06270a0b04081018050a050105040209070c051b010203040302180604230402060f04031b050901151d030c0918070b071104050402040e0703 77
    0x44010400d104045c41014000e401d1400a000608007800d003e0384c541c901400014a490390b41c0e40f90b110a900c2c2e0400781c85041010001228015240b110400b00482d802a0500d01c50445a0004125101201d01395421514400000c001c14810001e4020190156050306207403c1c3d4004074100c0404c4003044007072f4005001e840001440d06150041c41400f030b8004000c8818018040c03011300001da800203911142200018101040d0240000101e0451140d03600282d801060101d145503803e1718200b209000d80030440d0100b003003035036218014078541c001c82ca48800b0090b00c50700083c0981803407801001c03008904c2c040e1a103801e0700c035950f655070314459030400b543c2444a000d080c801400c043d58410f016085840ea0216410407441d0001e00581122294003042f0680d01107065403610204a450308210004290803402c0c603204810349020600062110010f11483d0310004010071043c0c11140415000b8a40d0241c1c103549800384405404003070f01c120b801550340c02c008a1082c8041c0960005188a9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 190282913 1250 190281663 190281671
    0x90d0c0510111c0e1305060307090e1207020112060e060f06090307050d080d020f031b04060c0b0405122101082814030a03060302010201050a051b07020a090906 70
    0x500021406603010300041c824000102c03003008000061076810821001d0304401d0840b2016400c503071025252a48035000183c01c0b21003d40c0420740d030440c030320a20081d41100c100765901d1a000f400d94660200f1589550001c4080018030070100004144040c010b05107181c00040c10300103881102c41d184c3c0b01240a920700018004585840914000c0500d012190719061030542c4c0c0002c0c0d00c420541c41034a00c5140c4204502040080b210180e0703c0358105944119250f0009071800d02d030b141d10072160311120015940514403003c084a041e1829a60142d85103c00c2e6141640c40d9040420044c0003915180305024808030001d0500009080c07005042c0c141c22010103250010088495060308071010350f40008566010081e2004a4240d07206281000d01c0802012030501010480801a80345801d000000340010b11940540100003144d10070b0b4000c1100b0381c0c0e01c04c1e9110444405850007014980340703d400000302d00400020340320300d60004000c8101706c1d6031105180d00b2240f0100d0101d5003581c035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 190284163 1250 190282913 190282919
    0xc060d0b1906090e0a110d0e0c01080405030306061602180103021f050a050d090c0b041d010b0702060a0504080a2603100302041a04020418051018180209070201140105010c0206040b030408090d0c 85
    0x24007849c020100d00703080c14215400d00b680e80d0758480c00020708040c000d01c00400c841c03c44c10f503015217500209401030b24200e010311000040025010b000d00003603008907801c0302c020100c00c00e9a50500b03919580c540c0c8160409848030781c100d0300b076800003186944541d21820f400011856102c0303608000c144008100395120320f801d020240e83e00050301809414039032200104503554010b42240e11140d411281c0a6860b060942c040d80c45010715081100c9e83c0c41040540010480c2428208085040064040000c4601ca003507103507107840101c0e40015502100d031020801400c041d0401d001007503840250388002e0b00f20300046812a0003a0b4040b4040e41100c1c030080141e02d08510440c1e420020015148002d0303400c01100302090000c1e00d0501e03440c256105502c81c007d2018000c101c030130139070013000300e84030713040124000b401380914040d5020001303040000001da641c001c4103903045290707000d01400d091074030f44000302400d41c100510941d1428001c0040380d000b90341e00300418100b944501840c045581c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 190285413 1250 190284163 190284191
    0x3050109050a06030f060c05040f03061406040c0f3203042d0b0c1306050909070801050d02133210030305030a0e0c060d0b1906090e0a110d 61
    0x1c068031550100746400401d10208201e001a18170a6410030804108007074202000c891511503544401100c0d4400640481000703066041070b6000c40e04c0050101d01d0352500703805c00c012103410035281c5001c078900241142c44c0b203001e00210400540b0510103440b580ca0110322050300701d12201c49003001080000100010004040c03a5100c07600d05c81e41101400c0c2a0550b40a803a1000f0103401a14810300c200c0080c01034030036042154950056a40c102d5a5169a031201034108d401600e107040c462000400004c04007841034680c40d040f203000074070140800e0304030380910107044442c06185020340c0e00e07111803010b072545149039002e0500740400020880c45103c00c00d4030307034120003030320780211510040f6041010030f901000362504944680030008080c0c00101a50303280a40401c0415006140402c10402101040c7d2100700d1a52050f203005000c00b400480041c8140c116025a00100304a4030007840042004101e1ba903101c503074090300040c1901d00401840c400e8001002200d440f0382c0701e0001c050440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 190286663 1250 190285413 190285421
    0x30403261305101a09040807170417010b1e030102190207260715020c030106030b0910060302030a0f03020f030301080703140606010c020111010f05090a0201110a0f0605100b0a03050109 81
    0x20400c00700300301441310780e00e1451680c04c2c0780d41c079a03100300c504201040503c03098008461032140d20015005003040d034407030890384982151140e4030090240c0c120304044001d042c000e50032200300003820600038101c20002e1403800003d41c1c410302c0e0950742c244407070740300390385110300b002e0700340704190000c4c0140e52900c2052500d090702c00707070708034980758800c50101040d110024601040c0c42c2e41d01510101021000030480c0f801545132241c0b507156007002400003d0120400d1001d0180b050a010703100080104d00030740081da211480001c0d055400016800c0110300081c2e00c03080054401d20650381654101d620f40c9107150001e8210510540002c80108104201340c00c082c1d9140304044040c0c2403074a41800040d103002c803038420180c140280e020130a66070140a61101d0b1508802000410090a103966281d42e5489411800c9000c1895662410702000001464010a035800700c0e000c1c01100309903541034003416028044420320b0803004004a18886c190010303040721300450740e0000d800e600d00700c651010b43d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 190287769 1106 190286663 190286683
    0x2303010e012105061315181b0602121b031b010b0108060105091003020c0d020a06050703021608090303070f0807061505030a0602090d05070602030d0c090506030403261305 75
    0xc84a0071f44108200340141102e9a46a0405040786c000700c0941c0075041c0960b00040766001400b190900501c41003c44210701c4600320a90b031400342c0b450304414a104105001010186005902486a11071501003440c4c03114050030007800107442031040181080c0900210039000c0303c502c0c001c0d01114030400300c030821100440c2c0c41c488025204c1130406001c0340c1280c1003102007106c03640b0a009131000072842c140c13201400c00940c2d440008540c45040c025425000504c40f00011074001b59803035071040e0080320401e6661001c4d2410000f195440070441c0b03000c50244001780310f142c034000f90311882c081c1d103d1401a07035424050300080e00703803440e210014000d10841a012803801d030302101034084d400c031000c41031200d0002c0900034ac8042205004803a000f1009000040200303120700103080580c000b403064600044450756204490400490305c01c45401c40301140c00e0104a4100301d00468 = true := by decide +kernel

theorem cover : BRFrame.Cov 190107913 190287769 := by
  have h0 := BRFrame.cov_init 190107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 190107913 ≤ n) (h2 : n < 190287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
