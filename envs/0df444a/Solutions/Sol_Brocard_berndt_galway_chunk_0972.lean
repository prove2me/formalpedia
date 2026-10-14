-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0972
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:35:04.728925+00:00
-- url     : https://prove2.me/submissions/a55e5de1-e99e-4f29-bb55-78e1a7182125

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 174640287 ≤ n < 174820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 174641537 1250 174640287 174640307
    0x10903030c0f0c050d06020903120307090b03060402040b221d0411130c0201060303021c020601050d03110d050405130e0d0c03200d090803120c0c01140c031605040302090a0507 77
    0x1740b54034110305503420410000d42c410b01449200c0d1242d8142c5801c1000c0076000d4078840c03403807500c440d10b04a14100801215510040a1560155003040040b034880803800280010b20340301c5010003000031050918180075803003900401821601c401e000041124035025844d4041e622402031501400c280340855429080d8400b60700d040740c03c24110345082c5905500c50811a4041d50856000f0901160144910390502540400581203040184220305040e007404040500c2803800d41c4c031207002001d4050500ca803034910b520008500207020030030340c51302e020702110300c0010070410080c420703c052070950f40740740440b10714091201610104050500a09807c2d01c501d0200d000603206548500702103441c0e0580e8a0100b011510b0000e003c51400e000009540d0f8030480501c1b400643d03128140c002420b030f080325403e40015900c440744205005021050503002e40780021030b4039101e052203c20030703907556004d410703074010070400b4403080000d039a40d070200c9504401c40400c00030300d580b1120011034589290b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 174642787 1250 174641537 174641539
    0x403020d110a0b0c070509060a140319030906030c0513030210211d03040807050609121903030e1f0f1b02060603060f010e061519020705090105010903030c0f0c05 71
    0xc0190002a02e0701080000d1141352504010740d488107840d14100009280281e8a003a002910321005004075000011040c80d07902c0c005048460080c4030000d000803a0002c0b480c1280024101503080003019018001c00170a60000d0030000e042c50700000384a0886002884064403950b142002e03040b045004d1603440c1c0100340081040041e000c1490f00d40702c00761181911846041419400020010f4808030565060740d901d000504847e5240404203c1c407504940780d400e512171010030001c03055900c1000340502c1c03030680303070040560070481d07060240454403031503040740c00e070307041801a9200003200003c0380d40101c02485000507442510f00001000700501010045505030071a4a98072894002407618410711049040361003658812071208112807003803040c0c00c091510007020403080d00e010300051015000b03000c0040c1c00c18588068003954820704640c4100582c0200358244201c1c1000d00c00580504028241000c0316490355400602c4000041d0016205849003103000c001c11269034200c90081034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 174644037 1250 174642787 174642799
    0xf03060b0d0212010603050c040b0d0212152806030f02070506090a0605160f0c050a0b0c12180705010530010e09010504051c021507020d08070201110403020d11 70
    0x1040c1e51910002d40c070000b40c0d105551040d0000003074880c46801040c0c420315018124501302803404412042507003184080c0c0000d075409001107289032400340400c6100361094075104000100b40c005020100b0000781b051400681c0c03816010000800c00e601e11004c80f02e180c41c000942e646c01c1d96540009000d030490003400d0780580e50030f101b802c00d00011050001d9016100400c0036490340c0c0940075490010403141c0d4089035400403001080c500440c1c004010724050b070280c0d003040c1566500c07100141c40807201c0385500c81d4003282c003100d0313011034034071803544803078141000303c15034240a07901d550b95240c0303104986c1005800540a044002d00103c00c01d171080c00c1c0e20307410101243c180c00900c0441c00034003603090211060710006104280c14003c280c000d030303088005089090280a22089444010700e445815032081c555113181040008000620402aa90140510750300c030074001403000601510220441e8140165403c813152038404480c00c0320f50450306121540602c1c41c00440d896905104254488 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 174645287 1250 174644037 174644047
    0x3090911040503190b01030321060306050910020304050a020f190e0a0c051206062a0a05070f03030219031116030b010f0303080a02030a020c0d020c010228030f03060b 73
    0x406006041541c50803410fa0b400784d50a001114a0840c0c0c004000d400256101c0042011038000c1c5140b003006c902e03090303050402c84e140413048000da83c07030703548105c0e8465950002c008000c0340c244524510301e4070f486410351071418952919075454000000191042c443d199200c00303280d60b400401d084500300a6a00780110f5910214240001030450314503413010f080080c0000300a10030011140b02c101013030040d091580300d0409000c01038206c000280000404402c11041034545540e07100680c480340ea00500c0d107403216240403824501107500070208203030103120610001390040742016640503405054240041d06060455008041c1454035880780a4141140020f003003451024003a44d0240c001d03584680d07178800796440483c40c0c900c0044c002410700001b048900845800940c1c1102c02480051f0900704800c84540c00c041103c51b00130090b034862400d80791556011300c100c8a0180e010b0501040c406c04107600c0c6540c603054043c6c014100000b108090400c24000c0e4013070000342002e01c0c5415120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 174646537 1250 174645287 174645311
    0x1230a17010920100305240f12071a03090a031d1c031d0114070f0203060f191802010806011404060203040602010b030304051c061e060e0a05060109060c030909 70
    0x540490500a001310741411803000c81501070701486000701c44140c010b080300080040f03081c141e0707507038040143da00460002c005d081e641d0711615054496400314010b000c9480c03404640c0303120558000c83c1d0031003645040c401c024a481010540201d41c035014240b05009000ca0b80415104000f1074a00355072046040c48100b80c5404d1440c1d076a0b500c80d20135107610b0010803601c14500d1005100d01c460900103600f40c60848a40381c1c0c60809483c915100b04036444071031400780d0010b414080c00300c61004010303030a0400c02511400c0c09503400c080d444205000c02032142e01c140801382030141c04030040d060045a90101d01107074415070440003240b035150302e1291075a8076040025100e6100b072003a2401582403030b80b52003e0b0319001c401c6a0403608002c2c200c61408100601c07500c0311140d12001615065500c600300c0c0d4040015600c508408250940c00043d00c0303080990b1038101c8030014008896151403c010402d890f6002400070080d9a62400c10001407840c2e49001c4480c4042600007102c1c0343d040200e00041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 174647787 1250 174646537 174646583
    0x10912080405031c110606090105120f010c050304021309020328020a030b07020705030f0c102d1205040209040215090613031208040503030403050a091d01230a170109 73
    0x103e2800e68071071784040e001c07910150b96100250b40581d40300f4030600042149290800480703003102c0202082d51442c4602d01e00700360858140e0011000450f2000042204600d802c80c020541002441c2c7c040001501d10380129940703800300408012440c021490000303c8034410380c0300c1d40800c1c1d4010013070141182c0364984030380c60920a6442c080940b0800c0d030080b4a40c680410081442140360307004000c007010203020412078110000f080030a206d01c00904180210b284900f001c4456003580c00402c0c41008410010302904440d8146a20b8514100c10f00005070b440b444030325046038041316013400100350707040d5a0310b8070f109d0310100b5a804200025654140c50040310480101d074003912611140b01c013075a4060720000402c9800801c681c20400001d0b00081c0500007516601d1140d10b0240304142d100d44000c0c080f1402c03110052100380d00940104410704004226040c400340c1c1100c1da03409556500003044003544d0601900022180385c512000035404250b204016590700709944042510170b40010801c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 174649037 1250 174647787 174647833
    0xd05040f0303060b0405010806060f190e1512161b06090501050f09060a051b120a0507110709050a090c23100903120e091509010f0501091208040503 65
    0x701190400d000012403410040548040b0380c010f85803401d081e510391040044940c0070b506910030000c1c040c0041c0050740e510104005d10510b03140c40b6201d2520b0040d04000d16080000410148804100003443c01501c4014580c1c1d00140140081c400142c4844415960180d00c1d0303400c1940768910b0511b910500c40c00d0380000d940c0a004400821440e1915498010514422604150780d58007041c089a40c0100690080b42d0201d480d050031840302002940c003003078690001100c0740408060006000404c1e28070f20400d50000010f080850036800c407003050540b0307a400c1d03100300882e4969800000c0e01900c5150450b61509038080030306010705889031611482607503038080b030303070b2090302404035003d03084c20102e5962001142c103490302e481442c590303034170f202c030400b1135800407400c2050703444d40300120f5101d2428560241e040075840c044040407003400d1002c2c2c4030050780008408a0307081810400d030f0b600002204155103204e11000d00400303107820f0015240c4182d511082d00f610982e03042c0507505040301000c036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 174650287 1250 174649037 174649043
    0x90603060803070206030f0406061a18030c0a060507050708062806051318050f0c01020f0a0206040e070207120602030a060608040203070b0c160905010e010e0405150c0d05040f 77
    0x2200c6616103429036660700414000941040040010556100300341e4551035025110781c4000c604144c84060300901d44510a00300700b50910041444039014030300002400101800f98000d041202c00e407400101803000d14800e50080c0000084c080301407003014030070940503042c41000c0390f0440c24500c620000c444007880300d18080b5280d401503400f1005460140c88110342c0300070020308054071f6810b200402810700990880000d07449050303030000550203104030301009079401d01410035000e00740006810710446201100007500311102e14030040c1ea0310810744050740c040046d4612035603950b040603440c10b0f400c7c0e00081044a440c00c610b10410280da001144a20320f4100240540e5549410035581700c40e09a50003945600301c0101840f60300500800380010300b0864080340c011b202141c407405085409500000e540d10b44800048c1301c00100c814816004007812814807016190544485885c1c049000c00c45000101c2c50010806110f80311b27058507000131145408100c94101881c103076a4158006c5021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 174651537 1250 174650287 174650291
    0xc091f1410140304080a09030b0f0a0c0507080f0a020109051e0114090a0204050a0f1802040b0303030405191109010b09040b0a06050f211006080c031b07020d06020307090603 76
    0x6151454465918002c0b45002240d00c40c1c11074885a9030586560001c007294410006030388000000309819503d21809455020107520315802c181b00078005544a600d00c4009000c0204041c5000450070760840d03542c54500328103180c442080ba5003c03805040c12020250242c49022054005024680c201115580e0110000c01011012115031013031560116604201a0460307030a01016080542160394032004015002500c0b000c0310600c042101c47d4110690043c90040c080c04085081602c101c01c04d070700045000b0b500f540351640c0c4030381ea2881c40a03d51000342640c2c2285404109175164200f00803c0000c100b05290b42c0c40d00355a001e2a00800c0e43e25204904100442ca528101039111905850444d0707640c03403500501a90700061079014015071600e225800d11801d40a01030360a00500078203900111070400d61904400070f04628019000b5070f0b100d01c00704140040300e40c1041c0070307115900711413003003c0d1566098000500c0c040780c440d02c00b80005c1d00020822140340e42c02035100d02900e81769203003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 174652787 1250 174651537 174651559
    0x40204061205070e01080403030c1103030a06032603060d03020a080d020306040c0f050d0b010507060603080304121e0305090307060609050907170606041d010e070509010509090c091f14 81
    0x1103e5801540c070507a4007141b034000102d00400c0c80f940000310300821a00f4860707900002c840c100351950780102c0384200810381d1390f80300707104011440340c42010808900c074840b044001880c40c01416444040c140340d1251a00c000c0200070103000f402500c0207035800808198496130b1512120020f584100c540d188039519040e1001212030064440e200c0100c1640e03134031803c1c113602c542000010a8589811414030405102c060000381c0680141005103103c0d00c03460303449090501d00f0b042c045a01c0091142400355400b42e05c0c100124000042c807045085107000708594440e189454110f1040805c042d0115043c014041122081ca4000c0e900528801040303400042d65010303808600c2003424103212281d080180030864501c5c0a4100405810009070421411074005002c0c9085621064140d1451780101804001034900303030100303a0040809842da0001e500d8400301d41134407103500c100e41c0d40c811002100031444c034410303030030044074118051440d8055050b00c4191032001002c080d16860f21803400951 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 174654037 1250 174652787 174652801
    0x602040e0a0b10080711010b03190b01050604030302150c04031a01150509030319020705031f0c3e0a0b04060e0a05060f04030527130b0604050609030309040204061205 73
    0x94102d6903400a0b94a134619500d0380302c02141c410341c16600800f415925107004035400e54040c0b1090161b81c3c034001041d00c40b901c0c6071070000303085001688090310800c02400b040022076000301e860031841c058004a004160b80340d40100c0e14900840d04003410168545200310301c0920b0f4003001c2c9050718494a034002d06122489070491315449140265901504144240c0e05220305140391070800c441c1d140195a00b1940b0340700031070707d0000c80301c41718040c10b80144498207111000c0e218041c210740310340c549282b07100740420902c000d20701c42c82c41e0b840362200d4801c81889a1180c144240f410140d2150552354440c807641800602c4100644050b6409884c0055000001200084001c40e881d40325019140c00d40d20b5403121201e120004000b90140203041001c0340b88082140429851548040d01d010200900c1384240304220440222028000c0d20f405144100e41c2c0d20f120558003103c00c00c07079820b0390741c000e00700109056024003d1015082800072901107541500225440c841481140040140b540c90391 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 174655287 1250 174654037 174654049
    0xa020a050307050a1202030c060c1c0903080f030601020109060e0f120c2e2a0815130603061802011d09061005070209010b19020c100c020d0602040e0a0b 67
    0x1100f81c0c1d81c00203e00b00200030142080160240c85800203081d030341c001c00d0610204501c2d40c40b072803400c4d113580c1119080022821050a009400030464038003510014150f070b640c81c0d2a4810b609001c2150300c40480010742d142e200f5040200b40c01c4e4002024821140c0700032155554010855156103507000d190340740d1050141c040d00303592680340d10400030100821844c2c1c0c082c551403502100302626208103121500b604c04680101c1000d9407413250402e00052084005125280c0074103240c40c20800c1e020b05118044040c0d000310014000c00301d80c6140c40303040105080004044543c80203002034204039542821b4500341c000044d10324000c8e21048401001502d41c500340c003080402c4d00340d128492034003060319400c1c620842c00b240212414090710708180b540005040d810244e0006c0c1c2d12500000704041c400001600e103400d2591075000420700e19800c400043e8010034000c4841c004c12900250401c150756a812520302c500f500b002007155200d4880f944440081c0e011101802498100f10a601c1e81d8103043c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 174656537 1250 174655287 174655289
    0x2041802070807030c080f0304080d0e030c0601260a080d060b1c05060a0506161707030912210c03030b010e0303072004020c030327030706050a0216050a020a050307 72
    0x210018507243d0140d5003658049a50501914120783c1404070382a002d00c2c500c0150300560062841c1d50320740c025540b65070140c0ea100e00051031190014010034900390f00004542d0f06491802c01015040a01b22008081c003404081d08964a48101200d420038462200020060008800418410f041d12034030100003071304c1600400201162000b00790014103d295122640018001300260810744c0d589002881942017444e414064460350485082080804204803410803140000b4505003401510050030036205d84c8603601c08940b10318014420410324000e03000c000e06a5502e581409041040c00401c0314081d800100c012078070700b078001440d41d03018260580003084000c3c001c0d864550142e4410310800709000002ca07980d40c04507044110f543e598005880000b45070002541c580c0340440d031000e260200908202c03034a525501c01005a464044111480b03580c0054000ca496218803154000034803440708904045a0388400040070402d0104070002201d000301d41c0e695082c0c1c1c641003010789804071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 174657787 1250 174656537 174656543
    0xb0112050a1104020403170310091104030204021b0304081507020304032a18020d06170303040b04030c051207061b080a090201050c031b0706030b030a080d1803030204180207 76
    0x71450480000407035000000b03010b68800380000d0f0806070b41e43c4c0c40c0c90340c0d103030481d960404a28020042003060b40c0d00c9a186801041130b00024010600c2c03d8058410900c940d0001a00440d00050855007151135080580c100d80a4081107907920344e0b40710061900e84420b90380d60164030302e0303800120348a0b900c0042518152500b0082c41041c070104240b268100740d0100c00107001015141400160404454002c14150320001c4000f40e84c0e0461a105101103400b0b981001d8190b801000300d400c1d0116000066940c016404681490b890315a42401c0d1000c16295000410502c43d42640004004000028281131407060800f440b048000700603980c500000b2107840f0001451250000705840d40c2c5070800b080c894010304101749801d00340c0032010309540c048101e00070b0b003c0d5441240070340a50304000c11001805c03185405c004c503e400c8030001e6114841c011000e0034003c40881c54a18001290b0701140c0d0074800f05010908010a624000d00039402511580b150403803003052400e408100c0380211a40598 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 174659037 1250 174657787 174657793
    0x30b1501020d03090b180a120306151b030503180f071401033b060a060623030106080a110a03051f03020d0b0a0b0622090c200f190b011205 61
    0xe6844001c84540002184000f002e2041030882d50201d922041891405122a913000c580c02f41403400d180c2c1c1c501030301c044400800000c00b0b01a60400c403030000c00703002a40c5c17628065940b81c6900f105009500408107482c6458094440b544141a00015444048405070311070503420f9800310006504499410072042458100550041e41a103120140000c02d46401e011740d01e400040c2c80c140c0c500d444001c440109010f41d0780d007024041c41d500040803440f07441c0c16000c0c603011103240400408032400107220758828800320102180180c4015000148070803481c0404544502d0803000c004c0151406440c0c49410524010200540d03001c507101000640e40c020308009032010055484002001c1c0091032070b042956a00403141d2203599100003010b041911171102d008401001c42c582d040c035096030780b00039002450a0302d4195800d4000c40c1d843c0e6550340c0040210001e240f260441424000c0140a803002d600510654510700454600c070002e8050240b010001c140ea2030b000601030414071040045d02982c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 174660287 1250 174659037 174659041
    0xf0518090601021c0809060609251e050a08090304080d0c080702030105040813090204140d03021f0207110405040f02060705160b031501030912031104030b1501020d03090b 75
    0x82800d1101070780011061048448842e541c000606041c55004154800500c041c0140401104100059a04244100d95402c01400c20040e441c40002080c3d101c0c58014510716482c0a103140500c62411070248580b507031165600005000a081d5446100a4004030306280b0102e9440d03240042034800741c800800c02000760018526082c3c47d4545080700407903000900b0008840140c4082c0a00c5006510440e8102e841321000101c25003480100e42020040510610042100c505c0c0040c00c106121403d565140240ca000d06040303041141e541000d00c0e00d182248801c020140b0341e035005180c02e038050203443c07107447e1080f810803003943c400b9500540300707441d0b12441001602c0c203078000706440707803142c02200d0b861020724000289003080707603004100c401c20200c2040820b4240e40075903480c0e01d07024070381003205504ca59106c4c9602d05100c6012010960741e01c01d81c1410b0710205089074081d68219280450300d207132018040342c9184032243c1e0b190041c05601c0030145164040c2c06407000701584040ba62044c0e07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 174661537 1250 174660287 174660289
    0x610090f12080403020406080d080a020309060609070201020717030a150506041707090509100501090b0916050c0303040f02030c0d0b0103120306090207140f0c012c0a0e06010f0518 79
    0x8460700700340c0d61074104000000040c0d07100d20034000101800b801424a03070402ca80050246a8014400e00b4254010000c0000b00340001c1404c44d03000d40100d0b11540c00d5140c50a04a009000740900100328100803100c21070700d010844085c0d403140c034942105000b03a841b2480a0f880b034100c0707423082a40200c01800140700169000741d40c141040980d000302c454071b50f43e4a1044c002c0c1c503030503554800070b50460302c00038260041c94090746002d001e0410045c800016014045000c2000041034400c110002c9039000011510034000c848070f00e10450300726030703d1781410704240721a00e0810f803040b8400d110740e164002e0b5504014040c9101d4a8000c16122140da06e152204050007405a88000030540d4868003c51208a244050700d030041c008e01e004489002800c2420b0b01d4131000c1c5819504680c014140e03180560f901049404d040740744040304440f06914040d4643c0d400034496410b60340072050810120356580d4041a0354401e01c4d017641d92581c440c0702000d0999140c49034001c1021002c41e04802d601203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 174662787 1250 174661537 174661559
    0x70c0b09010629040509040f020a0f140f1f030204090905340308090d0807080c010605090c071103010905030f03071202090612070207030b090d0e060307020705091b040303080610090f 80
    0x4014052282204013823041d9000400504140e045040788136008501802650462088881c1b661416995500001c0070783d40054401c4003041007202004860088801116219405580081401c070500340141380031413a040d074541d0303001021210b90b84980d0072080d150501d02c2003e103403c40c40540c000e030421401d41d01c540b001e90740290005a0002c9429516000040c001001400308074080c515254607040700d002190300f594026130085225145d800d0034044080c0317540007102c85a036882001c1c81d540000c20303004a400340c0000b0f44040d0507408081049402e003407407040191320601c0c0b00d0380c48190300340d104075841d402c0380034a007845900002c0510101841c020f1510020307411020b40d0044814180e66903a5000484200315503c8d1155009a600300020a411141c946070402088444034114900500b00a645a0261060500c20052a03011820003044003403c40b101c0565501c031035035075a84a080140c600394003620214000c602d0800e503058200e04c20300880044d228603d1410074490f16107060400c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 174664037 1250 174662787 174662791
    0x15060d0b090721120f0210020d060302030a03050715060b072d0503040501030b010203090d080703051b0c120331090609090501061d060405070c0b09010629040509 71
    0x40c20b4440c00c000400d01c501c6640c0d200200744041da504055207016494808002100303000d4401c203211003500d0710340c0000c1d00418010703080340f2105001a01c40007240d4800c00541115072002e9018040c202c05d071010325600800030314099010715085801c000f9015024001c440240c0300703000e034451051200308002442e1610442d1102900d00391061180d4446e007440c55403051b4014102d40651002904006c8c075600350090000034002400510309081140020540000c041603004100000c00209181010f000c0d00030b55885c90030384880018030f00a07440e441c1d03688031305502c5020310401c042190000c46e01c0c400070403030f15000d60300d4040c0030341500706074400361103844404e10780c4038404215400410100030350300c207031b60007400707298008200040719050160841d035598128204861383c14050001d8004034040701034004805a8001a103075072081003c580d46403c442c802000b105850061200c450b9054200320281c405a042100d4611407540f4540c1002c3c3c0111403c95501e00c060004200034980824855 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 174665287 1250 174664037 174664051
    0x207050d0312140103060c030b01080a240f08160501020c011107051c172b020d1103100b090d111c051e070e06040f0b09090a02010215060d0b 62
    0x700c0440c1e0180c0030b07055840001c00803681400390401081400900e0080c1d81e440740c203a040801c0300e42202c0700000d0803648010840341e1400c0e15207110346111096040c00f4807951802201d218404d071b403280070310b03226940207201d0721005208001070420345910303040381081101e00507001007242205403001528181c5104102c070200d801120400905500c0e14240704140907220301600400d041586001c20001e010701020300c0740c1410038030141c14074010b603080100c91310384c02c2d12001203003c03020303d00e180c017a10074802c04449141c01c280c0402c00b004401c0740038600035222810002c001586034405400700e801001c0d500c42d8000d10003d211000304d860080340b0024074001078002c084080744601c50841d50b21801d002150f140d4030900e082c02e5071404100d05914400420400703403110600d040342c00c04101401a1803248500d030380e01600c6424404a51000700c241c440682000094a00f404446495409804059000d40178003070070342c0c10b1121404c83d050700c100c000030160310907002c05445081900000402032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 174666537 1250 174665287 174665297
    0x8100618030b18060f0103020303040b0d15090218030c0105030604020903030f0316090807050109030b0a09060c030b030c0108100b0702063a0212160224070318030207050d03 76
    0x70000c620219456441010701100c10152410080f03282841e1801c010050102070030118014001030b40c0100c102d0702110604203141d5255990501020002d0600031a00484400103450000b10346003960060040034041086810905202c0b2050517120040302c210180094030400c0020400d00d01130340908445c41c7c0c0541200d0800106007400c0c180f59200f03032407000721841c0900d81c5000e80c1d5440a541c40260002001406015180074006401a506404018511406d40c0700040c5c0701c0060754042548160000c90920144d81c002002030001c00624032241e010303019820340c1051f154000c0d803804c1d000d1540c104850350001d260903203680c01074212100c201c0c0d209404024406400381c0f0028062600410709135040e103015078802c02d0507008019000c0052445005001c10170950007200c1155612400081480035413052241c03040b403c22108244000048103003600c1d0400c481c00302054288a0034894400708610016580c03216098810007030010016800101c060000342014180c60044600c01d0400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 174667787 1250 174666537 174666539
    0xa2a06050d150b090301050705041215140a060303030c02030a020304031202010204030b0a020a0306090e0c040b0a0f0618050319060c0c1a04052a0913050d080109060608100618 77
    0x2d0031080303070100d40c0403140e005000b044d000a00d280a214450b0414120300349a4589490003460b0848102804005082603a00125034000c500d8103800001d400d0a40c003c8452251411a6826004014a000c03d400003407400c0800e0070200d00000840d1244203850700114182444c50303591036500301c4d0100701c2d401155020b000001c0080e41200d0501c0c005c20001c2409a1119020b010003811502181d01003403285080c0000d014031004089041c4840d20b5068a02064494544001c2811a5850b80c032900300c0c0c509040e00054403d0340314010301e5425010381c555454403946d07070040658944207510241c00e02e4003514401070000300243e11040d800101c5040c5960354140544035480d001e41c540c10460030007208070b0100000c101041c080c64101351481d1007032061503003500403403840e0801c40c00a47c6000e204020b001c5890f0408640d08110826400030844101e000780c0c1100601c0d060081c412100325904040010403007502840301c940c403609680d283c00301590302d02141101e03401c0015000880c00210b50320 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 174669037 1250 174667787 174667811
    0xa05180307200409140f0102040f050439090e040503031609090c0804330f090203010603050c0a0b0a0f1409030f010515030a021804080c010c020a2a06050d 68
    0x5484c80d040d01070204100c0004a01c98031600b0b00c9155661105103910410050045005001405041d01ca0940340020004903881d4003440a20b81400710043c41641072810814074803001c00b00306542540c503075500c082c203035031071058444d443c4086e64010081d8009000040b45518100b545e2502c207826881c00304c01455848084104480c110445040003e005500308001d0041140103043c0e9200d003c0c4003041d040b91a6028000f0102307d03490506500c41e110305c1c1400c600489a080f412a080c0c0080013013008950781d250907a52115103801840c0552079480c0000b0340e0b80140300540b10702840710344039481c24800d407000448413400d002040d000303800414010242551002c009007091150300400000303150400000e00c5d1140040c1d50034451180c2d021145003801138a819035043c52641070080980b08a0720f662600307200d075005d021092820380d868144100201a40000e480c1d287c80d0182e070003c00c03a104510b40c0800d0416805402114400000100304810703842000108151200c00740002064480e41c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 174670287 1250 174669037 174669041
    0xc080f03041401053a0c0503150906130e0304060e03030c07120f2310110409050703110a080105090717060f01020102040b040e010503160e070c0c0312080a051803072004 74
    0x2405c0c0400c0a01c484030030002608252040441110fa41c0c00d00301c1c118070306a1305606d510480d0b00c440600907503036200070800070b07260441c1084182c0725011092104801c00a900c0d5a86e402c1031050900060100040744218100807080320000710040001d088103e04044890060100e0501c040b6612040b0296260214540c02101c0c14000802c480c080c03e99102002150b2910014400d140041c51070042110350001c03800c03048504582074244042010341e07811341d007900281142422541080000a901c085080d40044420b060380c000300c0d00d00c0440d0b2290b403c1102d0000409034000c1e00d201d02d44020802c0344ca031100c2082e044c1c0070144005450243c48040c551615000b81d40302c161350400080050003580340038450002d20391100e11500c018185811500d9607030241c00b0f0030170401e00400c040b015084c86105001076005d148c006400d04a406502c4030005d0100c403084480e0070303001d4a00302c0454480c5005a60301900c0411a2005600740700e0301e42c82d500300040d080d45144180f54100e1030080c3e160381781e40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 174671537 1250 174670287 174670357
    0x1a220c20010903110712150216052401051005090f06130f080f06071206091103010302040e011a130b09070206010806221416030c080f0304140105 64
    0x39500104601c00903180142004049083c144959004110f05111544003264440c400c10780040500c11035802c0300b030300800288a81c0c10006070b5900100b02007000c1c030000240060800300700041e510b4030f81c4c80b101034500403010f0078018142e03c1422030325181c040034400c102900c030300540100710603022940c400006100e07174421070010041c502025000c12802602c120381d0001012458090b14005900c0c2c003645454102c01010a1309000c0003810401c001030481e4488005010510010001c642907407148052a4209220803840389040c69082012140d06001d011002071020300b2820340e90300b585040180c1400d8a041e4410070f15034445820015941c0c89001501036612a00034104070750601c00054206003009040351180070341c0d140c1001041400310042850250000880b2080c068008009420124907006100e1402e40121b00401403000364882d00e421241d04204030f13400301000664543e201d01403440346151113188400154900d500403c005e04495005c00758410115451a019410480385 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 174672787 1250 174671537 174671597
    0x10b03070e040e16031209091505091b03090c1309030c060c05070515040516030b130f05060f06040c021b04050c0702090a0207030801050d0b070315080106091a220c 72
    0x541d8040e40c0c009400521f445c020b080e03540fa00b40404540c1d82d0000c400c140143c810701e4011518000000c1d0402050542c4210404440701c1c0e02d40d0345c0c1000c40446686100c00010380c0c1c800d107418a648036060074584203404401d075141d00c90309103c004a890f07500c018020b003000c10003804010070500340042c0f010f00c22a40c038040c035040245414205820102d15100382041d00d40c00340c108106081c00400d802c129a03075441f09080310844440c0c0d0191603d04020928107400501314801c80090180c442007070841907100b00c0381903604000c1c584440c1c0080b40d0f52507041400d003107118141110340040c0e0409030402d99110485440786460061030340d000c201d01203030480c0c402013160381c080b92000401d503100b510540103000480311482c11301e11035281d484004001405180500d43c1d00d0904e201c8007400314254000424a520017003140b20754459412b03024014016001c0d190b24091201070002c0c0c9081c1001d00300d203240d0040480c114210940008006100e20300f026003c0c000801a45d5844544444209d003403006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 174674037 1250 174672787 174672803
    0x10b0a080a05070f0e040f020d0f0b04051515040509030705060c0403061107030e09100302210609071a0c0709060f03050607140a0f09030218010806010b03070e040e1603 74
    0x108030b041c0141440d0590700314440d100a011402c1103800d10790241d050300140c205000416010040c4005031000300c0640f0002c0070ba5814101d24030a204803094021712490050702624080c0b02c40515258a0040031191810b94209c4516240c003103081c81d5104aa104400c11f0480c0d01d4411141c43d19440d000040b98000c140c03480028003407040148600a005d00401e00402c000d04000d82c40d40c01500e40c3d81c18075840f0380215004c0c0d00103550402e211810100840c0c000d41a5191188110403a00064012104085113842100045000b40d400081d041c802c58284040756600c0d03650512404030954000e140c0310031607101d2508003040e000480d11452008020310b920302c000661440c40c20070b09046000b0844c000f8010010f00204a0301045822681000000d00d0640200710b00e10f601912114072641000c0d401419141084403035000940c0c0307480c10383e114201155540c3c0c0c0d0341c911008092000b1900c440002c5c0c82391681c0201410550082c1c0c1d4120290801d0b0b403002c41c0180700994141410340e00036110b0403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 174675287 1250 174674037 174674053
    0x708040b0408121306030b220609140103020d110102100c02030406030f0507081b0f04080a0c210314040801020a0e090c1303020607020303190203030714030112060e010b0a08 76
    0x740401000307503c40d000d19040303030a02e0400d45030000c0c401a03a00c60301040c151660a0001350b5503400e500030300c600300410002c07441505007003001001801e8600800715101d15103417080003050100c2d503800c0d049a50003030030f090861199076030307800310072603070b036007141e041d441001c403103408468190085000b0309800d0f9005507105c5242210040c162072420a0100b041807800c1c0500c0415607001c503029521008510809040740220000e400320303885101407a43c0118408600410f011070040740e5018800d011300c542e040c119480315180c607510300224100c103510b0500e060500740081d0050703151402d50000c410f8030358201541d4840c02400e91b40120741b070b180000c1c4207401c44802031800e0801c060300701c00d860201905041842410204401060001034030030300340410b61808564040003110ba6519000b00490b1810601d001c010756603400544012000c101c00c0003103411942401025a03040b1008812060340320790240e200c540017800d900c2d072450199501d070160341a0743d03114000ea00c0002d1005000500840c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 174676537 1250 174675287 174675299
    0x304060e0a091413050c0a0b040f091119031d03030a0f0203070509060913090305040f080319081509010b040306060b0405010e10030f0f0501090b03010e030d0c02030708040b04 77
    0x4051542040c01918542a0803203c1285002d40c180d40c05128405020007900032410441c0c07914000740025035002c01c0700d50020511040c144040d0046880403803840c03601a071151840015103c400700c00b012a0203007807100c0017100e1010350110400c440e8034100055821825501000f021860320704280140d0700c000b0910480803828441c0d03a001c00000c00c1c0c214154180b8290040c1240704038030b030440c07103100045844180b9588a15101c00d11103040380c41001501d132186805003040c2c01c02d01c034410303400003507140003d141c003804411603075504070701010212120340000c01030394481000b515601c0c50b0203d000c069401d6440381c40d07181e8040d02d000d080c401c2d02c86203545007070404d40d511038209601c54501800200841c0e40c0041415400c0c190444a01c140c0c00b400360300c00c5000740748101c0c5c0d0303407401070805014070304002c40703a4040d9040e43c1a1030703014401c50074910181400d0343e032074508021140d8000c000c1c2e8102c7c41c0345a442002c000429206484c905805501e588041c0e802541290020040001c4d04001d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 174677787 1250 174676537 174676549
    0x10b0a0b16111c1110020d11010f150807080106030f06020c0c030a030e030705041406010302070302030d0c120506040504020112020c03160b07180b030426120603070504090c180e0304060e 82
    0x21213001114201d00b0649408030094a40c25009205420700c07000c0d4018014254007908001041c08280c442008ac4501605030503500e4102881120f100b0301620002080e40c11042c002c003000d80f60050171180b50070100380d403400000d600110034004980120341c9902c443d6034090140702c010600a5450443c0e40aa2408250410780c83d5803040d4869443d16000900e105189030785a548a002400c0050301c0b8029418180c0c114030641e540c84d0300443c41d00c0c40310041183c014402ca0009807559174100990b42e2104103201c1203600954020b400f1800a680f100780a00303140d0010301d0f4003105002600d0500014a00040c0d0800d401c04084a80007130b44010032511300d5005848e4000c503402e0181030b441181c83c1001c40c64003444050005030a1030f4070000300c40100c1003100380040d00f441c0400000381da01c83d001c0261081041090311450300ca40a4200001810710301401040d1586400c66188842d1600d001c040c18181c0a01c4e89528020300c2d02d44c0242d0210000034405000100a26120703107180112003400c0143d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 174679037 1250 174677787 174677813
    0xd051902011803050c040b010c0c0f090f0507081906091d0609010b061206030a0209012c0601090b03040f02180403170c0a1d060d060503010b0a0b16111c 67
    0x24865000d11000c00201310300007006020720009540004803400182c004075100e01c2d6042000d0b241200e02c1c0e40004102031140400750444504030420484106842c1442042e01c00a0300c0041c0041c490304081a84d00301220b112296001034000006501c0b6aa44409015150084a03004004501040314010020f0a00070680d00480c031030700802200038941d0019409000b4045410508210380f400500b00d51000c003d43e5002503002042280203694031960f12182c200c14400d4500c0c064500510200100c41d0201582d00800c0161154034099040101080203500001d00955170740721a60407110240e102d030f0260130f890a40499017210707039242908003d0403844031220308a84420f584401c03c08060303400000d032000921149806002090f00c503104607a0a0f07001d52401d60700900000340404c0d0504581d10034000c840b01540248a6a110f9104022048086200d003803140d1404010500000389200e14103941180729580c94040c00d8000c00100702c8407014080040103400e06903c20806110452800baa = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 174680287 1250 174679037 174679067
    0x904140901060f09060503061803070506130204230105240d0605031603111c02040507110f06040b0f180304030303051b0c1002030c07020d0c06080112110603060d05190201 75
    0x8400c0c1491b00010a40c0c1e158014503e204920860500b41c11000041c01104d40c400e400008441e118140000d40f03811408040303500300d00c2580341110111945108072881381189403800c20484440e031804040c0070f21349642c990100750b000c00c0406030081e80388021001e8104610740c03000c0003440c5414031060601c1c1011030f40540b4104003441038204001081a41c01c210042c1042e40e48056070414405020f03141401001c0082d40035007810100400c460303000601c040302011001c02c4a0300c641e21480c045440780d20a4401514081086002490341904200c0359604104008503202000b0446050141941c1181d001180026121410b02074030007400d880d2070790350181d21003100c3c1c03921080c05815962031401e01c00c4041482c0d00400080c1041d0640002d807842550041c0c41a241007400e4501403000703079603034000d42c004101c3d14000425040194030b510040664000d00031250710901004103c81c2e5080203244c1640300a400c0d0002c400103c0c10b01070b40d0748204004581c040404102e1001614090400c0588 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 174681537 1250 174680287 174680291
    0xc010612060608070f18060b12160c0201020606060304020d050601150905150712120f0204031a040f060908040f0602030d050612070b03150a0305030406030e070303080402060904140901060f09 84
    0xb03000800345110308904441c541c50b0401351100040c40d1030303406821503030300114044ea17022509c296a10001070300e03144500480f18400001c80d81109090f120403400305c001a00690003000001e800c0d081034402140c216000405807100101c141d03803030f00c4ca00300e0700343c00100c0e0041c4240580060282c03c54040700107001e0403618528107d180b601c0d4111103001e245005003c0080103d042c9445a004003008485690106000e215200d14a141c0c0741c043c2d8014402210403043d41031401004068080d100750043c2d42c00020001c0c0400395840d4840900128441a0351441c000c200005142960b600108000c14280e006035880f84c0c065a1814102c41c00200524051148000800d1a81002080c0c1c00c0560300240c04003522130b02d80043c5405004000f500c082d82101c2110804000d0180c0003001d0001c480c4150303014086080c50100032502c810756480003c001c5030540d800300d001480e01c01302901e010300c1701520000312a044005042e14001c0180c6071841c0d00cbe59180d2045c0001402c4203104400741c8050841 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 174682787 1250 174681537 174681539
    0x21005060103050412180b21010510050403080d060b0d090506070e030706030c03180506160c050303010e07020a0501090c05010207060203030910020304212a110405060103020c01061206060807 84
    0x100400c401d540c0c44620104020442291b42c41d1501d151844007804400d02d0440d22808204850348006d4150180c1c00030700d500d8003000103864580501580707198182552340c1407c251655032986600d4000612a5180325154800840e460300100c01030009201c030040c011a001c02142081c0b8108900600048108510a08203074481d0b2400100034085544601c0e00040d084803403441100102103029080c1d4a0294811003034080c0140020018040d01e807002c00c20124007540402580d403442d001c440100303a80c00a20040000100c8940c926034452242e0041d1401c010300d9030758684c21118207c5d02141c40b24503040c070a01955a041240b0005001240007d51450519207842a982c118102da820031090300000004c1c2004030500c5040001e00700794030f1109440030000c4010380405444546900c01d2a10b108a80750481040d01101400070b0300120400c042601020600005c1e01005100074103041c2c00701704c8044860424404c040003002071000c0702c402c0f60350502d0040d00303a40041d400210550311030340c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 174684037 1250 174682787 174682793
    0x50f160b0f15012120040f06020f1207080904020c0a0501060506090a0312020f0601030305091003180308041b030f0b0a020c1c0c0606090905010b0109060e040906090606060210050601030504 83
    0x8001c181002610702c2240244c0d0083c0c50344001d082c00c001d1080c42810f554000c021942100c00160095612513815a031130f69880342012681c646010807083c445900c0046100e0840d02c828004128403400740400304d103440c0b02c88020805036445040c510a483e400103c440003801001c0c4103600c05040704855a41c5000200c4001a50086041c0005062201404801011140200840c84410302d80c44d0980b1403940c1d49060240c2144c010210003400b070000d00f0251451148603100c4e6208949142c0300c514001a9241c80894080304000c0c4110360801114a460213941421070368072000f181301d86a9100c1e0b0090a142c1804600380142c203400100c0c2c01440000e0740140041049141c41c001d18140b05080c2d110f90700d04481c1500b5004018007041e00d48000454800c02a0b001a0381d2580144024400c41a14170011102d0b01000e210300c100140c410440240185403d410003000d80f03020f15004100c0c00030640f038600483d055030388000c0150b0301c0041240c42c0c5114900a8070390011007404d0400561401c4d032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 174685287 1250 174684037 174684047
    0x70503100e060d12080103050601050603060a090209030f070b040504061e180b180105010e100e010c0807050102041e09050708040b04020118260c030706050f160b0f1501 74
    0x2004850205400d440011015283d8007521008150410b440c107440c080c00701006045108280016a09400748000224503801d280040300d02800001e000c010341249002d142c1d80c000c3d00000b82d29a40340c00ba40703000b10b40c001000c0044001030070418a0459841e0f2900c810002181e44c1039000c840c0b072420450140c00a690740890342d80841d10a14000c01403140303202d4407a4020503440030703032a07031200d10203c4580d07900900c600d140f41a544c0a8a812a80ca40701e6400c12440c04882810b41000440c0024000490f5201da2a0f561803644034240241c1480c80641e0395a003640c0007904111009000025580740000b1a05040001416480c03410040d50902c002d005100d080000c00245c44001c80501040443e4440c074018105a03a803648603070502911164601c100d02d202c249009014080c0480ca144402c60200b50811100c10040007070100741d25142043c0c400d500f0600c1c10300c4460400b481800c3c500501c0d468007546862142c80c0d1622645401c0303008040f41070007c1e140e06003403101c040408045036040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 174686537 1250 174685287 174685289
    0x3180d05071703160b0105010f1e0f02240a05010f0e0c070f080d09050c010207050a0e2805011503020c0d03051b0f1c140109020708191707050310 64
    0x1c4074060b840660500c69041c5584503078040700508607040f41100c410b01100d6544141602d2099848446010440a08440c3c41c9040d007800c1c0c0c00703900e0000c89044001c3c061292840041c44500584130340881c4c0025480f511220017a0410844850404000a4403214803815014104501c1045009400e0401107150510010010700d445403001402c03405000048048440040e40611410b0b40c0b1586010113034060010018212001e101c0e162860707805600100f01078041c0c1e17102609000d101032409e0b260050313418019144041d84a07a2805e01d4003440e010880d4660180326090002c2404e502d000e0210820000c000401001c142c4180101514488081100b8101021901e008502a10741049200300c0440da6010300031074a200194610f0340c21070100c094088014005c208840f150751030040b203001ea07260206500034413199100180042c0d4030582c0a0040b03c0d00075480c2c0c50518a0060001491050030234813640403602070101140840d07002ca2001d5131200c03444c1360407411418040e03841100c440d12 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 174687787 1250 174686537 174686549
    0x3160303021e0c0109020f040219121b081501030614120f0303091501090203010f030b07022d0607031a0f010c021e090108010513110d1403180d0507 65
    0x101da0510380c2020510ba80069400511541e030703528a00d50150081c904040128043c01031900744900d245800d00c291040480364442c1ca440002645074204c5580e040050700750b128980c0c448035110364034040842002c1c520029291441182050200d42031501407501040c3c0c105030a110043c0203440003100c8140d003800f800e8415045035403407183d1090a000407030400540310321004c000c00c803c40c1c03c009071000a07003052146c1c185480c2d0b01c0f03001d2007080e44001d000314101855637480400000d1504201d03240d20032007501c15101d26070101b4002c41c006c0c0140700300034007a4205041002c000f440c010b202454202e1118241004a95240c8810900c1841d000c001d03140b2618506496403600c0e40a1005c6c403da10b54028401400c10300b2500d180351132005000c1e10b141c022010701e80041399841c0c0501c21b07140116810090209180d90503550020a10848007403681c11100c0700100400007a440300312040d1444811000c0d648428101041c0b018407a030411f883c5114000804120010490111f501010b80301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 174689037 1250 174687787 174687791
    0x9020a0e0c07060c020307050a03030b041a0609150f0301032003030306100f050c0f07060f0906170a0212180f0109032003131401080a021206041505040c02010203010302090903160303 80
    0x40c86040a1b4158028000003804902481030700c9400c05500d40e1002e02e1002045400700711000c000e050204684460317043e0183c2080c400c20908145242c002c9804091404070b01a16140c0218044030030160341080c1d10488203603801c4180f05001d01c1450007019100700342035000b1400c0d460302200040c68028032030310b01402d01180a8036489075512942c1160b80300c903034040031204c03101c82c855122661680c043c80b41d440000c160858551402c8c0c0f0a050040403109182d0702d5400210360170707140900d100d2016004040d09503081102c0201903c0000c5154803d07030104a01d0342d02490041184c40c14140d28644054050740b4043c41c400000307030807280c104144030323400481e101c3c4c0e4015103110500d07522800c0e000c80070700c3e0500800020404100c58103800f07600000c9e6129400c640307450180ba0203038041c0764000d0210020381c2d0005210345c181603220586400701c094000400c0d03a80d0b83d000c03030100d071440065500181d40000050044d42020b1740c8898000b0101d200451a018601c180285040070000c402000c00da = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 174690287 1250 174689037 174689051
    0xc0303040609060b031e1603080307050a02070906080309040b100212070218040f061406010e0105071b0b1305062a070302030d0f080f100603020d020d05010909020a0e0c0706 76
    0x41243d80c0113101d84900902103401c41414183c45040440208182101c10710030041d503800700a600c0b140300300072294400740080c2141c0f0360800607101500b10704108403c40c4130f0100700145042c101e010301801400108007070b5035201c66100c20b1000307440340c40ca0400d0041c50345800602655900198170021407680c1003103140c50700040d10000c0c101e4a0880021541c00110340306001c2402440305001910500ca0300013005520f910012281c0381020442d40e06020400110100c4095405900242900752007100200e540882d0290744401c51021600300e00203209010420707070300d4000c84c601132102908007101c406007040075400c00006c1a803401401001420344400c07601c000250104200409142e00030300b078807a00301c000c11009003400008203c0b03500245d40e52001ca09981c20071400c0c1d50180c0254a02208401e0400f0001c0d000380d80a40b1507101c01035400c00200307000302c3d801d00c0b17003501800d01d0341000300e4030301064010000e00c00e0342c40d00241d26001e0344a090100720310108007119600740e4825000325202d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 174691537 1250 174690287 174690293
    0x6030b150616030e010f08160804260301050a060e030c1210020307031e0506090703020f160c0302150a091a0f0c06010f0f0b04140f0a03050607030f020c0303040609 72
    0x98054407052502d12040900a0010150010f141c007025102c03c1e41c0d0315510700841c00d070860b00b4102c2a00c50701d50450460043c5e6001c94825644560b120707018903040c0e002c10408844900c017108178481c5030020b0681c048010308c06c1d071801214100040c80c0500c0d101240081d4000001d44400183d1b400c3c1e8451081c40321680034142d01441074840144c8100c0e0119103d14100c03001401900e400c150400c2284160035403030340a1041849554081e900c007034210301c003a5490701000d8000354010624100212000d000c0c807108020000580e8000e00d206602400406166204ac813401c3d840c60740729401d030080e0611042d1003090748030b118081110650f40007510244c21074603c454583c41102140c910b210030002d220480c03c14002000390480d2450001c0c01d215a0b40d41c1c1d074401c20454140201c0e2026007041104215070300c83d203010708103100c40c024440001d4900310300c00034005000c241d1040300c00d60050004c1107601c5401d8840c20600c08a030740410342c90a403003841d0180e100d11000f0401026183e8412342d182c18 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 174692787 1250 174691537 174691549
    0x200901140d06090501090e030304030c061b120e06130303090201030204090f1a030c030c06030a14070c030f0c1106070314040b07110f01170c0c030706020901030f06030b15 75
    0x8000300c40c911003681c07203400c0908540942600c0c06080105400e00000050f005450310800055100c0c030005503041d6156030b80c1c121050650380900b542c1d16501c4400c0e0604010b900702990301168010344400103a0b0600300d04140c00e079000502c4049483d0454401c002d1120703c580518240c0c03d92602d80020f08815520040e0028050754010700c0d83c540ca40004032114040c0f50b03210360a2050f01c0003c50000ca102e6208241e070f9003082c88142c68241d04101d032940c10700e0900300061604800080c1c40400c000c442404e9040505070103c50400c0007540011207102850341000072000c08207058900b0404650785902c2c4c0c08058055014070901072600000c0103028588200c201c404628824901142e0f1142c3c0c6840c680000d401501c400c1c3d5a951684002c0f02d02440e0802d804a20500103856000500380754030b0003014424001450030051020402c1010b4000b05e0600051800c3c40c45400010784075910107000404840d01c0c000c0304001c2507d00b64003480442c60b601d40780d0b0343c80002c0d046141a041940008510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 174694037 1250 174692787 174692807
    0x2060c03040c081c1808100f0b030a0506160305010305030901050c030d1d0d0806090604110f0c070905010e060307031209091503030e01090321140304050706080604200901 75
    0xd06406420400d000d401c250354080c94039564565031380c90032179400302c050780d082408900c20100254010307103140600018a03000b04200c2e40c52180001801810380700824200a031056003104c0c160012020094501c004034035880d0801400d00d001c01c25036056642c0e099032885020340203814407101082c0301c1c0b4494410030480744105028a02400004820003c065a003944901220880d008002802841a03c10340d800c5100d110010814011501c0d18024403000b02000040001c090004001030419004440000c01e1080300441c000c0012602d421030500807103006070482403882c1e0a510070300c0030030345c0c2c0007502c6810f80f600825040e400324000c400603034400c20550b0000710103500300420714124822078407070300301124025111070003480c418000440741d000301404014016000e004110915150689801895032602c3c11704900c1140010107030440d07078100700e600301c0700c60744590014898142d00c8942150400ba0503601444000e420303104c4545252108890b0040b0141c0124400126a100c1e460080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 174695287 1250 174694037 174694049
    0x109050c18150c0f06040201110118060c110d08010905160f0305060f10090810020a0504031104020412050a0c0905070507172b0c170105091906060306091b02060c03040c 74
    0x1918280e048058503445030300445080e40800c0309ea827840c00010106010721604101100f04110805501e9958040108010110081001106031a0801580003040081600700d030946030808198540940c00041c0e6200406440d1040401049400c9464201550280c007014a00b000316031665503c005c2680100141d180300d034001175002c400b5902a4002072000103039105003066400702400011210280c0c455001d500c0c0028000b080b0800205d80175001e010f0070071000503c09031810381e90f024054002c0d50030070015903d5802c107c054408101134030410300020404102e00f44103524081ca00603290307001d03922029000c5203800c90840c02c4442c0f24400c94104030389010000d00c0c0c1d42001444110000c8100311814071803460f040c0d01292640c052810320607003e1000d00810100da083c241848030600c409400c0c2c84000c40030714504c034410101030166001800d580e50700081da4610b4804134606039200008200410a5403501314813100c0c0e40411450b40c41035801128a94175119490082442c07032596000c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 174696537 1250 174695287 174695293
    0xc06040e041a130c0920070c050d060605191a0a030219030c09080a120e060c1b0a090504050a03030207170301031109180d030b040906050a050109050c18150c 69
    0x40501c1404000c201041c50180f90f03411003203603da411031707011617070404509444100d000c40f104c030440d80f0082c01011518403541e03981401c103039110003280040c02400e00440d00c2c5a1100c4050116080c4921070742c1c41c010014000d9150700d440c041c0020b1030661a02c1c42400921070005a00e99403901a4040f2070801c0b008000c01c4000b054540c50080040110b4600c400000d48551030020700000c001844d8106141c020700d807400c802c036102c4000d8a411582c0921250080000c3c491200580c5c001d00070f007030b9421860165552411014000c0140c2000e20f40c00507000e841c034142c14400480c500240ca40c1d2032550500f8010780d00d0b00c0a04144050408854074401211400800407040042d929001c0c45140170a5544100c162038621036404245840122008641d002c0c89444c000340784603400000c2e4a03040039100240d072402a40300d60042e18001c4800c422615180c400402241c0d09a105003075001c0c0110392070505012042c111700403808180358042e4821050843c03003c4403003144074100e840342c40e50b680807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 174697787 1250 174696537 174696541
    0x902090a080a11030d09060e0118170607300213030c0b0406090909051009031215081606080c030415091a06092703040e070207170c06040e041a 63
    0xb045041c414110000e0285c000c0300304c40456607000c1d0309404169031054690b000841401d40046500120030481800c08030200d01700012032113121840040da12181d14068616890410f00c080c04a08468800800c04056990b035440700da20f03070044130b030329070740400d200560f80740c00d0f0320f207100780c1c2071415080607107903d51100b8000b8000f01603000400032505c15490f0300e80e44030f9441542c501180c001c4200680103800170420301e18200300748c3d844529050720900381000c007108000f400c0f104443d038107807201400303032030506003480020010004418600c2c88510b0f507030800e5040440c010411040030705666442200800810300300070150448814400302d0340010003099130075042c07a000b00901d01001c030300f0580c83c080c04200241804803400e0310500c9021240300005a0300d60540005040700340c030b9105207010500020403481130b80c150030b5015056a500509609007443c1558080116101405540d6072008090444907241c02c0705440454400c1105161944e0303032402c02d00d8400b5013440c8103442d03803504041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 174699037 1250 174697787 174697793
    0x501031e052707060c0605070324060207050d030203040b0c030409090303050a0b0114090f031203010e0115020f060f090a0c081b030718020307090317091e09010902090a080a 76
    0xa441a0041d120901080c01005003907a441d00c0f02900c4c01250002015040b021010404640081d0b40140440c9800164140f8040422000030750090103d0b100c80c040b0141040304560400090010308002c458540101c0085d0703030080e60f070b480380e403003141c0d07401c500440e1381c84014500344103550081c582c03c0b10a100128281c81d005006040440300c60b810355150829075011548070701d100c0710400d0040c6010501d001e030220100b20750314002030801ca9140c030030044c8102c800100d050255000701130042c81c0d46120350420342c05a600d10000c02e488400c40d40f2821485200c82030005600b900030b54007401d02e2a058890035041820701c0000c000c0901201c500c86000580f0040c00203019410300078810700021100000010552161080d2090940b03035100000402c451070b03080d500440c2c0101030360500f8070703505a0f00d5991441c800006641040c05400200d038103007541c20700e00344ca00c00680072680c42c807901c20142000190203200c10301450081c0303580898407000302e0712000070780c0c400360108a0440b450204680703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 174700287 1250 174699037 174699061
    0x40e070e011419090b0702030c01032c01020702010e1504050904020105070209180709020408060103111807020703050d0c02011706010320040906050d08120423010203040b07020c0a0501031e05 84
    0x140340c03100044c050040004190041078241d4440d55401409400b02c1a14640114080c0c0290207840b50301c01c120011204550010b81c80d08141e001c00c0b03600240c1c90b040a0b00002d4442111316114a000724a440c8548440310070300411101039480490701e03000d0507251400101d515018000300250020810001d00003440c41c051980c0103680000390441d4100b540743c04080b01a4040c901c03416015902010060000031201c4000b00320348003000c3d050010464120a6107001c0a2090310102c0150300080030500507c0001d215081021002d801c10b980003808950000313040340d100c040c21082e00302c803074008112560304c203400c0280104044542c071000d1808441c0207101a07400380c030400f100d0318070704000080c0c9801d051603c01092a0000302c541d040a84049880c0c070660780c01071040b60a0360101c9030f400c600c264020740060440c20100c0005880e498103182611448030080c06060541d40901594235a42d60b400c03040400396207007032801103003500c0780e10900039038205103021003209241030000b0270400c2c3e5914 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 174701537 1250 174700287 174700327
    0x80f0c060f0709050607300504090c0309240e1b180106020304150e09040303050402011d0907120f090f0201121107060207080c30040e070e0114 63
    0x340801007515140e82100755182140c600c21a80c101205000318000301c0d501841007841e0100d10040c80d580050961040320140c03600c1c41200c0007007400401c0c14440041544244005082142410410078a2a489013041c14a040c1b00300c04040345000a4000f0070806900007540c404078860859104d03003044c0034800c0481f503840c1100c501658055110a18240202e01e156040f10f4164001d145081d0802e40d0484101144000e08020b105243d000c1e50000c0c2c07940d051189c41180642da00003281c0c1098400140050210120007440c800807075460a4140c2c1c818040c81e42101041c20494407107114250303464050100c10104c0504c0300d1400200d241405485040703400350714401d98134800700010451842e0f0031107a0304014081c24031414090740000031131075402491031901809045051207100d410b0b40c0d05e070206c803507402400c4d10031f405811941400036110048448081d540500e04043c284840d10384800341c014078a50030007041121b01451a4010498140c1e0141c281d180640d03501c402c9000c281400c619 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 174702787 1250 174701537 174701551
    0x506091b062a1c0815010f02120c15010801090c051c0f140c0d050d14041e03031b0b040213060b0301090902030c0f2211070c1404050402010801030609080f0c06 70
    0x3168490062203061384c580b290f046900422946400780300110340c00d13441e204c8441706621484540e00c03020040300c0040d206021865000703100018103903075102030608042e03100c0e80e040c2e0304215410300084c0d131441c25101074440954444115140900c924000165a00c1000e00020f07c0c1d03040f40001c1c0103010461740e0118281c02e0031115030f1040d1800348040c40c50740c40310140c1035400603004914454802c03441c0405284642c6400c80c10903803100c4250020081d00c06907580c100310070500030820560004900c03070400070b12031181c3c00f4034001615400e40d9100002d000a2240e1590303803001d01c40040750742c401170140c6101c40e00b02d038413503840300d034248003c0c25400300c10ba00c2841541c090400300d1070f044240501007040a884102c2001441c100001c1d5500e00c0e50118041c1a1500b140c0700a0b545810041e019450040c00b8501c0d411380b4191049034017a003005100c42c05141020100000360b600003001504407644040d001070410010f080800950007940380c40d084d950000601311055a00009005005d4030f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 174704037 1250 174702787 174702823
    0x7050412052103060a120303022104050f120a0c02030106030602130e061e010e0112150306060906050a1e0e0403090302032b030e070b0a0302070506091b062a 69
    0x71502c4601c4203000484001d80d205c451280107000802600d000401002c0c4641400b500381007501403265030742424550200c5010240034204024000d0030401c0801c2030105c1c0015220f41048100448590311030012201c090002080b542403c41d00d096102c84020b41d00710100b191070b00100842c0e422040c0d003c1c4540c5c4110580ca078003003a12071518600c0a100c0850000b0a09480e660303450044d41c40040341c2c02c6041c1407110482c02c0c1b80c60950315000746401c096420303041400e841d00b1071902008440d03064110351501031400c0001c0c0100d440c0d0406100951701d0942d81060248500140e1308040d24494002c54000070700740d0700b40010150411a041e05980c0b00310300b95520340b5111444201070900076200111411240301008441d80d020354031410402203440c0c10b4403452903c5c0c04481841d94054031001c00081d40c001500c800b031041c11300015810601d500d0242c05280884507059242c039958607015445000002040d841c80c21661101507248410400c3d04400f5541c542c802d180c85e4815140110300d51340f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 174705287 1250 174704037 174704083
    0xc0109060b120714090601050909010b0324030a030507170c0102030105010318050601061d041107060608060403050306041d010509010b1c0b18030708070b0702010c0c08030f0705041205 81
    0x700103e2074109440510084040c40d00c42e071800c1041005000d0580c4d81400010010072005484e1240301501a10809102560fa4109244058200d1414400b10f0704003c1c07044039641a070355000b041400c619034051810b03507100e000c181001d0030340c410190240307400c5000c0003c0024042c1019000707141200d0091300c04105828000e0365a00850589080c0205a6000301c0c005009050280740340c10000c200404c160f050501d080704c0410708444022115503c012070100b14030081014600031031014001600291405040c5030368060200d01015100c24800d0351070317801a05082c080030025440542c6503000a000320f04210013800d001f4924240c14601a482e543e040c0c00d178090140d400520410b50006038150281d9400308002c04529000300d4018040c00108900004507081038060030816010302c040c104242050b0b4000303802c5482e5410f40c6428072000c0052a4007059500c0305681d0f202d000040c52012a0f603030802c007214180302c1c540044400f6040748440758140000003034001c0c1c000c2da944008216507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 174706537 1250 174705287 174705319
    0x30c0303040c0807270c112d0c18040f060c050a030509031e090402160c0f0515030703020912060702010903030b06250f0609140c0d20060c0109060b 65
    0xd0030745c1000402c00568a80440040c26046038003210300c2000e40c2c5000402c0c98511007009050403442818294004002643c0d0b01614030075665000705450200e00400d03e44902d440400e813890b60104a1804409819000070244601d400d0b040c14080c0d03121008116490b070000002d041303600142200400070f894000012184240017040340c0001c2c0000e0000d11070f010601c00003445550010f040180c00030703001d226491410f4040c01c0160713103140c0b08090f95030107181030562091a59980d07921282c8036110f1000036100048044003140d4002c00c0e10324016036501c214101140c5012046008000140302e100c0c10040d030180c1c19400a803080f882581c09200f1030030b12608001c2c86014a02d021040d078845200d582c070001d00e108139920703a80c2d4400c00103120605070a1300d0340c404444e1202010b48041400c0b604507a03d600b001e00c800000c00408840040301d94440e5115096020b08420000324404aa04540403043d5182000c3d110600030620003480701c4400741c0340205c0906080000fa0f4080c071380b16020b045403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 174707787 1250 174706537 174706559
    0x80f0a020c011d120a060f0615020106050f04180b0a0510050d020f0405280b01090902211005040f020a080601021c030506210706080703020c03070803040302030c0303040c0807 77
    0x100900b2040010b050410004204a805050046903130610070124240e0004109019130744201c2141100041d10301e1600a0790640c86124806c01011039240c0001840b0030f6803a03000c0150004c40075200003075003400001944401c483c5286000d81500704120402191002c140c110328440d09810f0074031802c5a84e15420f210082c1e036005c10003584000d02d124406180d00b000c0d401140d0041561544034055003c104901c6502c10b1070790b4500100a8030791098039815608242180c004004901d4111f2401c3c48040180c414101151940c3c601c021700300005c41c0c191800003610b0405404010420014110240404002035001b000c0f0080800e0440000910940c004075800c07405044020551490740341443c000c030014040201041d5011805000e04004102d0310700c800d8850240c064028040b403805c3c184040c02c90b010080c040c5042500400810800b12070200a507448a980300004940b60b40b10f6142c160300f94003998500055510000c030420003403004500d80b820450b48140155a1681e4a1b1156002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 174709037 1250 174707787 174707807
    0x61504080304030602030601020304030f0c032f040902060903030a1d010c080a030504171c060807050a051c0206030f0a05060402070308061009030203010507021015060e09040807080f0a020c01 84
    0x9140c205002c00c00c00b140c200e800841d0310150500c1540d1815449503144c1d00c80480c0303c1001d131000500400705108004450200802c1079004e940503a00605d0b140d00385c0c01e44900b1580b1618012074950b1802c030b045483d4001651583c0c4001000d8176101d1614038401022850884041c05140828821500465000341d0400307010b60f40020395645021614072068001c1d05001e0b0003203400c40410000032500940c400c0180029681035552044141c000408207403d40f41341d07800078602c0da000f1001c204100d079a0a01e00700200c600903101c042c00343c84d031070040203603030700381c1040194004034000100b241d20464185554412848d0110400c1039443d07c1c81403100300d015980000b00442d0454002c199140307042c000c462640c00c050304d040540309441c0d901003808c0d40c3c2c0943d811400b41e8000c200b664442e84a5001b5240ea0074907498034900c0b0907140c03e070010b050020005400e0b010300c00100218003404414412a008243c204056a9540703d04001d001300303580c40303005144010b00030345421030f83c99881a40321903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 174710287 1250 174709037 174709049
    0x20c09040b010303080c040e131101020c01050912010608030706020c0727090609060f050703140c04060302090a12030e090609091002030919061b09081915050a05061504 74
    0x80c41d280e0075960309a40c500406019849260404d000016080301600c2d01180f194000304804030440c0054074141c410700400401c940e0540d08002030214041c1d03840403ea86404030111041e2101102a81590b4014034141d0000001800005400018014030390010aa020030080031640000d940d00312260345040c11050b80d0110395a0380d021100c5045454104952080c040c0b100001d076404207988050444443c101c015550740d4581042020340354062140e49185204409140344038540307400d18500038400e40c042c01e81410fa02013410b410540341c0316030b840702500640201c001c1041041c00c1c040c1000f1001200c4520070190500002d5242c100007031a1806074103090002c2111541d0050010301940004100412520880958000140c802c619008c0c0d180c1c00303468001448454142d0111700100c03540000030601103100002c0081c000001841c0c0c00040404000d16140e81c040d25001041e200203002c0c4808040c100703414400001d031182c0c411802600d00302c540745050341000341c0c03100850089100f54 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 174711537 1250 174710287 174710303
    0x81308030c03030601210c080a060b070314070c0f12110604180e030f0409020c0c01110307030e01020319030b0316080a020f04110a02100509010501050a0b09030a0b0a090201020c0904 80
    0x11034400c0d4082c2c2c0401c4c1601b45e082e82c002c41130100d0003e0f01c00449091981500006404805029490101e48103000c090158900759528003009a10080c04c184500030010308000360006c4d2036000c0c0846010220b010380f5030703120140701c02541d8031019000c482c0748020a8640916500a60802d440d1140c2160f007191131000c10a2032031000041e9000040148160488890100f000a50341001c402e5001b800941403a6a0050322015000303001d5203845500540b032818007025135101d500f803410000a13540455850f08e400c0f440740c0c5004004030b0035806030481141407071400c501041c0455070190000303400e0701410340448003550600076862420035080d200d4240c4a410540d400740140c24548502c030b14142001d0008216080d1700d0700007a106078481421200182c0082031004401e01e0207025240d04202550003d0005505040004140d010907100303c8403916030008802d5201e0320141301c60a402ca0f040030040c4a00c1c50420500d0001e001c030301e10124014012074016600500e08640050300864000350a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 174712787 1250 174711537 174711541
    0x105010e060105072d030801080307021f110316020108130803070e0a0807030501020c0d090b0306040b190e090d05041d0402011106070c03090902030f0c160c03081308030c0303 77
    0x64403240c4c000c0344251850407403d030000c0315a428079011100c40f14070b1040916801000d84c20300a00f03240040c0c008030480d070010042d40000d42d556032503030050503411442d1a02d114410102c207a030703402d06e82c1010b82c0703090001160348004070442d100d05e80c0b081c40c000e0301c40c42d0080c4e8a0124150b8801e6402d04c000b0414602440400d41640c03248820307406440001d01552501510f40640381d2601045074001c031401ea40000d03450710035400600020b165041c15040054805007052a400281e0000525407801240e5590220409039034441c00c0c08a070070340d4000c05512003500c900307402d010054100c40501c4548918405401c0941c455801c8030201c8610101d04100d130401e01450340c51040002c1c1c001c6e8100300c6614000c1d01c1c04403003400b1850103041a1b40b2000191401840c000d00201295441198554414010001a0f86144c499103070b1002001d80c10325a180da001c0c4010380001c298410181c5405a031103c00300400144000814100a202501c540d980340d80b80c40c0781d0b580b8490320407000c1481e001400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 174714037 1250 174712787 174712789
    0x6120c021516020c03030408160b0c0d0f030b0612040b0c071109100b040b090102060610080f1902040b030603010f050103030f0c081c09030e04061a03040807050609060f090105010e06 80
    0xb541d040002618410340c3d800c0d0030080002869504150000e0240e0b4000031425001110b018080c280149160400d035400c1c460104503160322502c0d400ca0b06403d0208415501e04282d200358040c1d500c2d05070040103907454240c03031856005e0070311084508841d803520707407030200c1e401c01ca84200355011a80e0014180a1200540062240c4800c01800b04000c171140b0302e07008104c0390500750184c405822813040060325183d01a00091500401034405401116840320000ea2594491a0241d00800c81d08a144180c1c803019460001003100300c034000f030524404100828510b0a00c001140128002c40081c000711140350074800884000303100040100e0118202e0070340c038a000e402e0201005004480c440d0900400e030000000181070b8000034100b090f0b940ca000780404d41c00c0b0104a0748182d050700d0400c40301e4144208404242c0741820300682d00c000100000d800c01c01808125142d02e5031020595025042103000d0695500c003da0b00c2a80011440c40040c95003001449024101c0716101020240f54851354 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 174715287 1250 174714037 174714061
    0x10605031915030f0b09010b010c020a061808011e050109050130020901030c031509030503060f03010b031002271807050c01090302060601020d08090703060b0102030c010606120c0215 80
    0x36540700182c4200b481e00001180039042200c1c48680110803c40d1140b4284050a0864040440640c103106480344044056201c0a404030180c9205050082500c401d4800641640c0c0b0aa0322244e0a036007400411649140d0200c400101e01000030b0007070140c0c1c0d8031142000c065800900541040028105100d005040d12480094401c0e02c48612500100c0c4c0640200300c02460981068480803a82c100410810070841c4081210444c0f00800708144a10703542c0c014500c0c07001401c1e031032050501e80f03400d403030580c1e0070751001c480490003c1c1102c01007810030410001a4009011405450001a40103409412190394004282da4010008100910300200c0300307801081c0a0b2081d42081030078080780302d07401000d22501d140c0703d0294000701030928088000918210b02228881c041120050500c943d002d07000500b40c05680c0e000c10302149050044004038910300503940c1d1b8281c0c0398241040044c13259000443c081090746c80110501510b000400c080c1e0f600c01c01802204803045014000a038048104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 174716537 1250 174715287 174715301
    0xc06160b040309090612020909030304020904021e1e03010518070501080a1811030606010c0f0209091612020f040e150408040803040306020903190203031903200a080106050319 77
    0xb8200b0030344013500d641d41081101c299822091082c0e40021155080d0700e4050441a80000c0c2e060041d840e52a0a80c0403070440c1074060002401405060100c5145e03000400030107101241c090460205522108101030400c030904010740d02071352914003c1160400c05815162076288000f00502105241ca00115409400180325000760790361681d69a10180d0048240b0074054041c1100001e079000d11001c05043c0580580001d050014020300360000440c2840810071454040320224071664803116140d080060150302d0400b40401d5a601181d01145210311f520001e000344c440c59030341401002484101c844100043d02140e004039500a54900c894001c55401481800310a080c103580301059807464110703070801c985075a004660801d460400b001488848281000801440901900425240d220720040015005074214403002940d00940005000b459003000701101c558026110500ca50811001000011600400052600d1040064070301030f4801c0f103500182d0f0065812003400400b64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 174717787 1250 174716537 174716543
    0xe0f0d0e01020109150c1d0a120f0b0f070e0d0b0a05130501020a0e01030b0a03170c01021201060824011202070f0b131704060516061515020c06160b04 66
    0xc840d010b0000030411502442e105c40d826901080c0802400300180440b0341c0c4403040808240208840003403552084200c004844040d4a60a000c240506002c004c071101500c010b0001c00180c020310420b800303507400340c501c40c12040d80c0d01c103c10700701c0314100003a8200c58000a405054600003041c100f0700705a10490300910118400c084846040c0ea0311401e91f08100c400002041c002d509a0a071540c0602407012000da003200c210b2191400c2d5541c1070408400d10f4442080c8050100da82c1d1101d00e02581142d00b855510030044001e9030307650400510703c2c042200d4200301b0f4095640c0d03003100380070361031240890340105131501c07540c422441610071300a4010000c00d4408080b001c074242e010a0000c00054000c86070000c0c204e4285440c3d0400d038100100580300c0c01d0501c4020801044010703403200a55080c011489986082403409042242c0038040395211070011100d03502c0c0005404541c0e507410540600c442d0240c4041d040100204000c07401099140220140d01800c0280003925212101c0e40c0588 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 174719037 1250 174717787 174717791
    0x8070c02040e06090d0323100b0c03071202011a010f091a030405010c080910021b060a05070e0d02010903060f060b04080307060b0907120506060405041a040e0f0d0e010201 75
    0x1503400040580d0342910150341941c010300305222100c14188000e2010081a0400b4810143d401c0459a05255004034469800c6008000704801901800c41d11005050f00c1c1e140381e81300d12140310f1268480c0d0150004552010a00d40c42980150040c05a9070007003031030b03030314003600c80d040c5100544403076100d010300340300b040480000401c6070000c5a983c6240c1030303400b92043d9128a01032603d5030841d4003088100003846104420410341b41300000d1180d5140c1031031180940c59021074062289910b0008005115502505007007081000d2164030243c0304d580b580c1d0724500416820703005d02ca0a400d0312100030740001d800341030a00200e207085c0c104d903c010091810003c1e403e0354901c9103000f01d800c0768103d09026000043c289043c402503000f046502c15046032008194103085a01a19100c880c8211100aa0300c0304000303155a40e0310816500203210181050000c200c1055042ca00c038060540701e1442030703182440b621003003400000d12004006409006083c0c40350301072070981c0c690074040000b030304541d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174720287 1250 174719037 174719057
    0xd05030c010609050f0a02070510022203030509190b0a050309030706050702150a02091011010905120702093709150504060b09041119030206180328030807 68
    0x8409102d540e0080034416000286402c01d1000481d003800090b040c20801030040c0702c55808a4804140825102402d139401a602c4131440f0002f0045d0680003150140001000000018160018014540c5844c1150030160003014080c8400c450300c0d01c1c6c0540a0400c00070300807500044d0054005507004900e5400320707410181d1980d5140b0640b0380456060006802030341c0c1e402035121186c8202500004140b0056082c601414049800180c188003640d04003e0b490800c441140401e42c040c120140d04542901c90140d40856030040702d5106103812405216008001007002c0c0348a085204070400741508020a43c000c4000d01c01401e41d0382100101071550740380303824001034100c644191503642102011500e45413604041c1c0403030b03155004c464040c1c540f5504000006d131a03000c204500401c116000481108042c8100310754801c150002504000d0014074a0100f07a92034002441a00d400c904440b402c1030344a400c48410300300111684c943d0844282d02400107801100401c1d80008146405409a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174721537 1250 174720287 174720307
    0x301050d06020c06100816050f060a0c05010c02030a0e04022106061201090506090708060d03030c2c0406050316030818090703050a061205102a0503071d0603060d0503 73
    0x30ba0039203402c41485d000c1700b000c000c4a40c06119070b80071003900000f801c4c18246000082803a198444080034443e00d00010b45004141c000c0e0410b03070405410a008200c0f0200c401c0c0301941e07a13801103c843d00403500d13524003511640340a000321044641c1603041294010003180c2416085000601525032000c0700340452208040c80180d005e00a005070134000c211418058140001342d070001c0e2000082114079030030000241c46003109205480d9040c80c0014141c02401c0b400c0300c03c0301c4100c24101c4d2801d041441840625a00300d0690000c04040350700b00000781c1d841e001c152342c6495400e0034500750314042d02d003003002c035644801428420480c81403012031007804034001401c485084902e080440d0703640d814041005500d2060002070a83c480306480c2e682d0b42a00c1c2c0d1940c8954448002c03031000d40301d60614560108101c50038016a00c85264408011150034000c0c105800072070301e001c00111401514541ca04615074108010900a07001d68a0b54844e04144520301c800d8803001d030b4051004002840380 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174722787 1250 174721537 174721543
    0x170319020c0d15060e01060813021306060c1505191802040501090e3c0c0307081b0d1a06030c06180f1504060c050f0616120608030301050d06020c 64
    0xc07103202e0030542c0500f45103030030500c045a1054200d101840000704c01800065004540326403c441c054032540b045c10403910003d007a510f001c480e8440c100e41000340c0020120380108002804520405008150b03054651100c8210b4030200da0070b171201604248583c0301411143d0180884410502005a15941caa0042000e0390020703403200340750030f5640c802c6400443c000c0c4085031841c100c44295402d05901c1d588501804554120031049084410741c0043c0074103001c02085280020181c02d032000705644961254884c827407401201030a60000f072181d501c5141c000c22401d090760f03200b040720030075003202010100c40c10302c010460307031301803207602649806903071401d014003490170f0704003102d00024440c4424052005c003000c0907039001b400300b8a0742880551000e0207550070b6800d28a0306024000560511624185040740441c0c0390707012308010321418a00d45015100400300c140c545c0302030540000400011200540b040c0442d0360401d00050025180c0030030010521401000b015080c20960682141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174724037 1250 174722787 174722809
    0x90c0d060608060f090123030f01110a0207060807020a08070809040905031801030203010b07022704030306060e030a24060f0801140f04050304030305070303090803070903020a170319020c 82
    0xc1030302c003402c00000d46000142c00f600c22200356209205949010709820062101e1074072082c0401c0351035405030301e136103081046410f500302090091002003010700d52940e15603c0040b0b9600140a070000114016016400081c01401198028000321609480385941500400c0003100c003100100301100c10f540d01d0b8011011203500070b80c0030f076989098150158440f1440d070714855040c5030042c0010400350802c8402d640046805480c1440d440c00c1602c8143d180e0b80c500e5551050301e05500c8140428503034154020300c15540c09485001182c0c6034401015501d14034510b0040801d8500c2404002c5070445045180401c00740b076402040c1291074042d140e1190350640c01c0581e1580d55540c101d464000c1c1c0b0300500380c12200130304185000b410684c843c0781d01c1c0d100d83c0c0006403d00100144c0d80081511a80c414510395400621043c0c4a05003c480100219001c3c44180e00c80c0040c0c2102081c100420040d0019804451005615261203001e0030203140001c40895000c2d030080030020062921400b154803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174725287 1250 174724037 174724049
    0x30905010e0f0d1701090f060302090408030906070507080d411510050705190f05060705030601020304090b0f0a170f0307020604060302030a0b040f0204050418030905090c0d06 77
    0x141101c0c218000c0d4076080c6443c0070030007045a03460000c252403030250740355410342c0c1301c2c0030740840d9140c003008136030700540500c1d400213400002031000c200603c01c0c06000745004a0600060320003948810404580500030100050135002082015150080b510b0748001c0256400071440a044035840d9001c110740c60140e4401044240a40408084801800c1c040366110f8030310841c0a01140802010459a04141c442102170100008107078040c00400c001e00d1100c001c04407031700b40980c0031500e42011410b90800c0d080382c091003000c01080c409030080c070680e4812503042e4019070520f444e0032040c0c0040c1c41c600710b4050b0403409003441d080594807410b45e65030280c0072041710b0314a103151b15074406203001803601e00c0078500d8005000300c0005039151340445084414034a0050303165220007505100906003950f503e5841072402c0d50071203c050881d00030f4001c0b5070084500700083d1900c0311107640c1c81401154000c000030b07041e040c180114a05160040d40000c041840c2c0741c1005490100502241c150b50844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174726537 1250 174725287 174725293
    0x6060f0e0a0812070b060909030702060c03042c0a05010e0c18031203040b010b040303020601031101050c07060207060f0302030115050c120a0207030c0b07050c040c02010f020313020f0603070207090c030905010e 92
    0x680c0c00d000303e0043c8690841d40580c0d41030315078a0100c141d2307034a03800b0b441c200071b101c1d00c1e0010355040003545c02c201392000340c181c1490241e42c6c421b102005a504504c0340440b01c46070384a060010707550342000e00c81c80b412200f100c0802a4580e562018280040d880b070048000c0369034500d28225000e80f810400a40202d490040c0191b607410581410303462400c4c141c1c8160f450500401013440080e07030110300181140c1d8000d180d030f100c0c44410001030711140130310b0684a04074415880300050f0075500160800855001c0d0720b03440205c0d9806c42d011005d9200c00d000340c5664a6041c040b458005200b40001c00e50750000d2015240940350b02c03004200c0740d070312502000d001a481864103206008151190301c3c001c00207861120314104c1c140da00c041e1280b2801c0007062146568114440b5200e0013904610b4040048032404c555070310708041013807061024050180d02580740c11030102c2d1541801001ca038002c082903001010042e20b00b80300c21000d40585c03200d841c1019150070303094001a009020301c102c560411006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174727787 1250 174726537 174726547
    0xc0106030f0218091906090b09010606030e01022a011d01021c0e0c01031a0d050105160e030303040b04020a050a090b040b010e0d1704031406100906060f0e0a0812 71
    0x400c08285948180b20104403081401c0c40590500000d072901d484c10300102c5d0300c0c4001090305141e002003581c15400f03841c01100748208a055103041d4800d1094036201d41f404c01c400444e50004900300d028400c0c020160403030300c41d60105031240710400740001d40915400862440154480d2203940600d145070341e1803580d000b01d00385075006080c03000c1101e01400d14008100906211064940d1529168403ca040c155500d4005907400941085c030191003034068a000c0d540740040c68401c0c02014100c8480e544200401004000644682001200403d00a000718196243c1d500c51a600002c090b02c12030b4800440440024140c941c640c1a0000f0f10f41060002004030300e100502042e01d000c0b12243d810491031214250702e9030344034814200c03210b4010066031074203800b040b00b2348410321a41c1c0010f024900b030031110840304100050b80301d110310b0800d013103404040ea851480d0301c25514140210b0001c540542c0321928142e219642c00c0782003040080c28860860ba840542da0305121072268003041c0c100001803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174729037 1250 174727787 174727789
    0xf060b0301180606060503070c060b150a0c050606090603061801022104150b06040b0a11010603110a0602030307020d03050606090d050c0109050d020f06130f0b0304061a240c0106030f02 81
    0x704140003814203081c407d00d10314100600400c503003d02d00d0020861a038459500c500c58868407403002884504280c82c590b155060701015001085da00310441d0188600400602d031818003c010f18050070001c0d0043c2155150514000030300840080039042e40c1d035003407180441c401081c17403031446c148110102641c190300b810f05104071140d400340c001205043c10004d22610f00e4541a0840e0100d0740e4100882c1e0701c03142c68040441e8940943e9003c1e00c02c41d03007041d00104c05d005601040c504806001c031840250590742c0d4000366200d000407101d603c05070704521519141640241c0201d603018000410365442c00100c0d10001d900e07208804810f8420390300002201405581110070300d40600012914551907952036400900036140c14840c060080c0004180c510020a200021101800a600b102c26070a62611005001600100c40649901c5c1c1014000000401c1202000250f480050310155034108101d07007000d59032800c5400d46002c40801c00100e02079180a200d90006140f04030303050164004070380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174730287 1250 174729037 174729041
    0xa050114010206040f0308070203070b0109050109062301032a0e0411040f1e0e0702010c020c01030203010503060610110d020304031104060602031b0304030812060103270f060b03011806 81
    0x100c0c400d070640d8000030901010840c1442141c032038551600c0d2603a00d503039490904a0035800b0300540200500d210200129842c00140c01481c140d4000ca441000520398502c4c00100740c0e40d101d171852280e00003801c41500194442d801c00e8007003808088101c0c02180303000054880c442d860314050400030760210251015882d050080071001d1000d41d15480c141401c0c4400d4a10a0156102c3d15800005a0541c5110441c01024030300c018070407106261305500c3d01480180c083c04032420710b1801401007000c1d01c14250b00a01c242d0b170683d20082c0c010241982c0d000284a22021085041000d01190075600b44019034100702120305003a41c0d502440e03c451452410900c01c0c564408401d10807030410205000301e9a00200791507826103000b004105210703903084400d0a61103036400207495020009400c081c4d4500da40d0885000300c0d42a6810080e042103078031800c41040d5003103514010302d00403001c000c0100e01d501c2d00b100c0d034144c019100000c0c4c8509020020f42101d080c04506044003030040f41c40c005006041c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174731537 1250 174730287 174730319
    0x140a02070308010602031c0506190f140a030b0a0c0e03030301090b01020f070b1911160303080f09060c13090c0801030201120507090b0c0a02040903110f0c0d06180b0a0501 75
    0x3d00086d424442c2c41540c203a005036450305418146a03031500082d031643d441c00600c00f0200022520801510b440e0315401140403554007451201410380642083c00307080c01440c4404980e0803807400301c0c0c0c0342c640301c9003400031345541e41504c010000400b2481d989594180010340c000c01407200c1c001380c407148480000e03040c102800c0711000c0640068034100722041c600d5084801e080702050341090441a4090103542d00c1031b82400c4072007148140803550844154500202081d6070007034030748001da9540d96400a9210fa0304907001d00301604481c01107040c084202015240700b080c000c4545500b030b80c55034590701c200c1d18000520000110550010010b55800007007070032004100c0d0390140642d1a1070340f0040d0140003684100d0b03180d60703400540e0980e00d140c03d0288218a60b8020003d201c0c0089905000780741c211b100e60040540e02501c0e0034001451400603c6102c584009000b540d5006035644440000b0000c00c00c03a5645200301410300300000c1d8585e0b84082c450807900c000019554108a1115858818 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174732787 1250 174731537 174731549
    0x90109050904020303090d03020f01020d05151207060f0e0603090a060c02070806070c03050f1305150c1b040b090109090c0e0f0a0c0e060417060f06060706050604140a0207030801 78
    0x401c1c0300340409a1004402c5407100c400945000a22100601c0d01324586164010107140c10352010801c614041ca99402080c040c0306d590700415500c2446004100d81143c82402410465010b6401040047d018100059940c2c2a40c2415650040c0400c080782ca9580b040380c0c1000e40740c00900710340e41040628403401c4c2d0342011174402090100d04004030300c1d0b9a02405043c0005121025020302d0800d0302c1582190030242c0b0213202d02c1e8075414140e5083e5880501402020b20481601752070154151074a4151110740c1400030080c425a14868115440c1c002000c40c401d410030303203607001c8180c6500ca2100490080113024000201c0c0c0d00c081c00c0110000c0c80780d8000d15404c141600030300c00c0750300c6051800342c0c020403129000a04420082026180d04124010480c0c210501160018084100340d009050aa0401050380c06554401c8040c00100034101c42c6113070f0216060103281d002c90800c0d0300440d440840504009a110303451000002140d01c01c80c0c030f052a442d0001407540800d03034410142401455 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174734037 1250 174732787 174732799
    0x20f06100f0303030b19030f020111060705300903070b0a06060503010504020307032918101e030501020d0f15180c030b060a030203011509260c04050c09010905 70
    0x106080c8020703180700407844050100354885100d841240d5511400351604d800100d11700011543e2494076115400c0a5402a400b10712014000707400317007030301090180c820451541c0302480d0140825541d00c0034a07202003508510120303880f4140e0042c88120006009680c81c038011a02c0c0e8006240c03005030400300070f061011117801c1ca40c0811100307403c841524150b0304200c60140c0c50313943d100d004038000d10140b8004080704c41c0301200a04004071954440114200558104000e60910110f19524480c10b40d002d03030561041c100200001400c518031503c9100420401c80079055894075054266084404804601aa2018000030050407441595075580c640e65100c141c451038442c6145505550140b102943ca88490000d51001d200c0c0d401413818800c020030013034844805403c0140290800d009102005614071000c002070b6000e48584404c440d001840c0940407405030960420700c154035003031a030b00b07440703451003104150b44c403405440d101d40540494180c0754400b041c001458001c0e00e50116009803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174735287 1250 174734037 174734039
    0x1f020901020c060a030b03060a0209030d05040320060c030423030d140c0115030809030115030c05060a2a0507060311040905181b03011d1f021603020f0610 68
    0x1036004140500c104904940c00c0f5100c411a1310240e0140442441c0e82e80c3c11701900e0104044181d0607070281004041c10b0b030460321500c54180003910035104600025068400302d01c4184030060340e0032058421800f000d400705003848101c007071710b51079a00984c000310f003621603e4100001003c621518118485801c0f001005900c555001c01b03003521040e000c00e03a0702d034076000810104883c82500800241044050b01c02c80c0c0e140d50342800100b64024460b02d0307119508100100c0c003059043c1c9041d1003a40c1c1c014100110440c1b0f48020840143d0003180c002d800c0c44100b0100c3e01c055400c031003040d0f00141d1220502c10710000c607403410604055075a00030f882403603d4100c2e00001920001d042e04d040e111010800100c603192400182c82508280e00380402c06d11882e102046110000700380540c60a50a40c000d0181150415201c1401d0b0920041c402d10359010600241215061104d1400c980001c2500145440215208030103095003681c82a40940c1c0010580341c82d24508114895200340300105404440d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174736537 1250 174735287 174735289
    0x101415030708040618030504030b0c070b0c0310051512090f07060c06090b0124020a0206031609080d090602060105030a08091513090e25060309050a0c0303021f0209 72
    0x250001401000400507a40300003800c0241c1d582c080c1c035030014940f0030080750f4025460003d2055000d80001c49085524801046041c0580010359216981c0031542c8601d9070b5580d04c182d4851741009040082d0080500c40000b11500d0311801d021300709001c810f61035070310f41d448003040603030780310160420342c2030b5102ea00c4406900c3d401040c0724003030381d02070720300b401161520b03040204c00350060030b00113042e00c058a0000100c18000104401007001c0e80f0400003241100c20a003680c641201d110b001c2d400050400009060f40d40a020490488400f420006a41c540315034010b13182070a030016540206a205105122182e010094140102811001055003408d55943c900381c0b4010703c00550b01800c50303000c107080d40082080507107804250000d04010743325601d0714003138041c00c0d0708520940d107801040c4483d55110590512111551009201303069030514180c2c00710018000c400060f84d80d4003401d10114006a480c42d0001e00440c000ea00520f82c601d402d1480382e03a00d800c41440083d00703601c10442d80c002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174737787 1250 174736537 174736579
    0x40606111507270306020309161509060305060d0506070f020c040908040e100812120a0203040f110f0402070b0f0115080c090a030f050115050406080a0210171014 71
    0x43d42d500b848010309401e242585003d40c01d109038000420090020040002c40c400005801c6014040400c030300400580c1c9074510300f1101c0d48500081d000a440400c14000c003406500003d4104038040d08030154135800b602e401d410014142d4005c80003402000515050540c104510b00c4591001c43e400c00540c1240e03510240b280c411441003031030480e80800040c0084000b6014400140850703420351303560601d5035420000799408000091914100c440c08144825094400e03240f0481d030141d881042c0c44071544400c00d2030550f204000750b105148100c0c404154a441c00034000c5540300d10000185800c1080203c80c034408140c204c0c0101010310f4030200c091580c8070480c0c0340c2100c98030310b2055581c0b1101c80072400c01100c0f0340002c2c0136610f13110400020800d0551054209030074a40cd4840d401c1c1c3ca480c1000305840c0c0c039100702123550703201d90404000f518100c1355400903150301d0309044104001c40542060354000c101d990031b0103041207000800031481070345405d0b002c1c00401c44404000c802c40c1c1c00d4001e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174739037 1250 174737787 174737807
    0x302070f3e0d06090f1a01030c061106240a03080c01050a0908070813260105071e08060423010603050a11071e02060d0204143c040606111507 62
    0x1040d01e480310204d5090119218a803640c507904524a09804e4842c5807002499070400e1000b201e208038448000070301c03144a4240746000c500c0305d03409003e0b2030b21204c01d000c986009159040d03480241030810368240c1d540f09002c0e03600442c825000c003601c07224858030342400c44100030031100e5032a0510b5511000200032104646003641e0101010b5291401243c41ca10130713035501e402601c1440d0354141e0346400340825154810860070248024000b41d5a800303004c4402d82c3d079482020800040c022180d480180c0100c140c7c59000b0300151000a221115020710b02c460040346180782107107000c0d0310046c040d040d81030040395130110010600b404040110001c4850520501002030a80010b42c100c4219681441d032500c81407980040650751140c843c0c10301c810013984544110b01c1c140e8000ba1b070b51245420110200d1070010303c0070140041c85a07012409003d03032a61601e081c03522803440c1c00d50707840a503a035124003c0039003010b03550706241c154070f03038000c92510400e400721411007104101000201944081002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174740287 1250 174739037 174739043
    0x10060303020c150403020409150e010b010203030a0908090a060c02090a020403030509040207080705010e06061002070503100b06071b030b0a0203190b040b060c01050601170c030105010302070f3e0d 86
    0xf071008440d50f92000d07010300a582000350700c0b0782414020801d1015503030080308111001041002201e2581641600300c8820151750382c0503800030700020304e003d91190b004002c15401615403074179203218407001420341411340d041400400c803001420800d41c10805416039000500c0c2204500e02411500c010f4000d020b803a0100740f04580001c0d4440c1046034940980303207403a600200a0011075052450035840700011100f45000c3e48005454a070410b100142013411038201501900200d184e980c0c0b02809030144401494001000b00f0024000a04e01501c0030300a114000044001c141186403001c440b001c05040030300c0050050042c011501724000c8000300107406201c00044001d00040850090058044030b6a480300c000325004100e4101904081d10500090341c0305020701d08030703da00760780014003a05d0910001030180300500c11540280e00602016024074008640c10790035940c0c5512080d1070040703084c82c4147c050074110f01d0001010080007102070782905c410451501d0804684505d07e0b008000e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174741537 1250 174740287 174740299
    0x5030721081501090e0411030d0c1106090324090d090305100b0415090e070602010e07030308130803090c04060506090f010315090c110f030304030c02060913020c0a020310060303020c 80
    0x925460313015512040c0180140a01001e8900c3e2504140d43c01002c61051580a0301500b500a40c0861041403501c0381c46500180c640c055240301300601c4440e8020b2420f9540600c150300701d03c0300d102820465a03030f50000c6900c00000d58949605002d06001d482d4190000384a06c006041c0002b400c0800c9984418140040003d043c0308280005400340c003481c00364240d011182000803c203940160082540300c007942e800c9130305042c2c1e543d5040f82216030440800085030001041480000c0c03207000d103982c04c84c003000b105a200c6050740e02d40780100d9005444201c1c0703507484400c007403015042601138680240000c84855080c90040c0c4041813000012142d128109659409142c03242c01c41065000050020080c0c100038202c4030207009000403c82125460700c0d0320600e044a0f441c1200003040701e10840c1e140d80c400700303290602d50910456030002885940c1c4081d203003001c1114818544040c1c510501c40ca401001c60750503a005050622003160600b010035820040705001007500040c440910741342c140e980d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174742787 1250 174741537 174741571
    0x601050705070902130e0c210a0e06070e100804031e0311120712020403150504150e16060203070b01140316060206060a0e07080403051b0a0503072108 66
    0x82641440b4035038210400702403000c1a0703210300e903660781500401e4980140307050141d6101e02004034001c1c00ba0030720402017041641070304500c030102e480c1019044240c160001c140c2440d00d015540c24014121000d00015050b14034110f80ba05e418607135402c4082850a11544074205514000c040c418200d24842900303007440f10f8030759218801c6d84518400c401904541d9141c0d2556502c03504504020389140c800112603075a40b11a4001c40e100301c070100c2ea03104528202c18540801e50b90081d0400802c1034800c081204080d00145205015403a503180510001d40700444000d401c1d02d0304e034047c039000307082198000d1201400041250041e02d065070910710701c9683e100f5030440024500880303107242844004c0c041500080030b6400182490281c0c04c01c40300d404a2940b03500e50619840340072514500012048000708021a018000404040c205003030001401c00c6411003080c50b040d00080c00301c071640e000003000303018032540c3d400c2c00d504109000c68410040b041070400801040024005c1c0204140d0115 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174744037 1250 174742787 174742793
    0x21201060e0f060c0705090c0c0f0706051e040b070605060a080d170c0c03130806070c030e01030902040225021302070b181c020609011103060319060902030f0a0c0909020906010507 79
    0xa8010540201401c03528501074031108c1894002c0340321540248242e00404400398004911b54061b20102c0d40c0349410140b1101d00070101d080d41900114a40804101c04120880b80c00011304900e8055080400d190408a0900001e42003d45c0b005941ea04080d01d8003941c5030303100395a8000641c80ca810456251255414540c4034401c28550101c144400202c507010503516501c0f00c0100c480700c10a41e0803607543c01e00d0513103444515600c000c0001d0300300760003040250300940c0200d040500140006082542c00060600c071030340b103510841d00380f049002c40041185001852030b0b40e0401c0c40b010079801c0c40c100e603440000840010b0054600345064072882503195908001310041ea2240302c820001d91032041c14042c0d02c3e82420b5820310440c2d4205410310800c0c4449004581c01008040c0041103070128505040603810104c00b412114903807102d122102607a000c0120625011501014142031802881c000b19a141a60710820803035041c108280090707034520700c01550014007030030038175a031700028a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174745287 1250 174744037 174744043
    0x71701150c060f06080d270f0608130203010f06053f0321090606180109020a090f0e0708010e040201020d030c0e040908031f0b090d0201120f021201060e0f060c 70
    0x500b215900344180e2002103201d5074071040560b8026801f4003510302200e40d042c900484240e0501400405100059007005542d02c12005a40d0000f1580003400c90790007103600103400d5980c0d0054500c20142c9441080c00b00e841c02c0000240c00e2207220045901107400c00c0d14000150b200140d0440051508005844900c07006204407281502e00c990174401c40b00240a4240d5440000d449417045446000c00041d0181408a0343c00d00801001340d02403001d84c40c05040074040e500240e043c2c4208a07007180009611a9030780480d9028001d400f404590b1440d101c80d00810041d0142d006090442c1081c080c000941d8020030388040c88502c918010502d10060103041e81c07460300c0e00101c0c9400500d4094420305000c0c1e448045c501808040fc41c80903a9402410803c1150300207001c1c290310860100000c100601c0d1102d601c040c410301c103052030301d22003040c10308070011500f80a0418080c281c00086881c002014038680c28054903040c1030414519001e580492489032101c600300c0d028141c0040d4600b83e48000b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174746537 1250 174745287 174745289
    0xe13020904020d0807060207060507050c0703020f0105070605250f050a030203060604050316030b07050901090e10030b07030f0b01031a2101021c0b010c021f1403071701150c060f06 79
    0x12007a130540e50101c5152a800941c00403900f47e60341c61501c1c000c01c041038800e40442d203503040b24200402d4902e007541c007001200c0c1000100c8030306105041010000040702809041e200c2c4841d0283c00722804503d4610403d217a40000025042010103407034104450341100035201e2100703c41c07a005031280e5903000851503c0c030841d000b0f10380c5485800101c04040c0040030030041640d20500d0410b0654507100d100f6241307070081a4040380880d84403241880283c00c260407040c0d003e00d2052000b40441e40c0d9868540990a06940190000761141c2400d5a203a000b4003519480b402c0a1a0410038502e8203101100501c40c0d844209225001c1030042c01202c00c0441c1640c41c1e1801c9400c021590360140300440301d026003072210b620842504040a00340d0541c042c105503088a9001f60284030500c814059201032213450241900503c02c880400030318905d00070002e903125108a8880c3c0b813000c0c44150a005060005902a0405080c1e07d030305590f20380e031f200c1c0034a0140b50f480500400c15202081c003072800744c021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174747787 1250 174746537 174746543
    0x2090925050f070611130b0f04030f05120c160506120f25090f0b0a020601170106030b0709030302010e01060510140d050c040302090901050402210c10050a03060e13020904020d 77
    0x500105c08481d00c0e00a00502e8803030107a01b1518201540c402e81d1300102e00810170803215040080c0001c00100300d00c050007168051090050b00d60116a00310002560b030080e02d0003017280e900c80407410405106844540010b804100d900906050483e0000f820f50361004110520045240c00414070008651007107602400341003000c3c4000c800d40b100028100c1d0010b01c00d00c0c90541c1240d80001d030003a441c01c12070300342c1201c07980640b100380e0a040e040d040d1300152100c092804e40d83c0d01c10000101d500020094010b03400c60380d0340780c4024610b080090a5401400e840e00340313a40342170001c0110b50344455040c80440c8050138400b00292130300d550712500d4019626500c00c418101410003030400340e44170041c029203108880000c40c684540318281d08a4008440c02034000b0311008404070031100c821840240b1008042c101c504501c041000715180030282c03100b11011400c082002e646003600342c0110340141406510314109072915245420150400f0b4401a0040407407102050542d01e8004203240001c3d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174749037 1250 174747787 174747791
    0x30c100c0e031002131406031323060103020906060a0906140d0510031211070306020706091a090d0e0a0b0a031401030807050615090f0a060510020102090925050f0706 73
    0xc80800244085d40c800005034890b4503440b10081450074074059040c00111010b802d00d81143c2d106043c104000d000d40b0800d03192320001410482c143c0c0000b4086400c08919003028154951461050085010340a007100d40314040510403071005951001415088480b40c0c5001e0340410f46104078864a8414010014a40340c10301c0c04021509030506d00c080101c3c0e01c60011241181031610741144c0c1031503071100c088a01d4004140410106102d50040c00e4000d000e8100003440800e0307540d40c640045011040c81c00c2140c900d00030445890800d0010344030b048410704210541d106030600280c0401604d010b1b0110400300441e40541940c425844001480085400760149503180e0502e01a1500080c004880b10300c240d1002a141c62105003c0201c3c64a01410303404007511403d602c1d0304450401402c00006030703660480040c41d592500f0704d295210034203400050346c0c0c0601d08144028040e000b080c51010301025116010720b00040f00c89081180c005280c0a0b40310501d5a850074a0340c0710390400075003194 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174750287 1250 174749037 174749053
    0x31c0f020c1c030603030f03150b07050a0606210602030910050903130801020415030f0905190203070e06090601080403090e16020609070302060f0c16080303070f02030c100c0e03 78
    0x144006401222000b12105018080002c1e000440a40ea09800b00400190f180729039404118081c2d08442c803407221080c402c1800d10344450021800f034100d00d2099821744d1183c0314000610419100d108085c00003580241c008000071405496100c2d0701c0c0030b0080005500200140c5c1120050050581c0c544081c1400c2c4801d051064140da620b41210682d81c00f0600070f04800102c4080520842d000c036003100a114035201c0540c0804e900401304078108441c12610f800310100020002d0000b0300c19110428600801222140145460484503400442c1140b280c4d4081c4800b0f6a03540790450340c000001d00e0016460ba0b07852504440000565002020a191800501401841380403460714000c03a650308032801c540d02c00300c2c0d0a50341d440c28440607400800c20020240b08008042c010188400d4010440c0d2240c44008005003100c1c031a5071192810390030200900c07100d1640984130114060540c8021741c02d122248120945806409091005c490b40d680a03c030011405030100c2c9920801c01802d9480c48 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174751537 1250 174750287 174750307
    0x20d0e0102070b0709080c010e03010e0601090f0e120f03040f080304060902040b180a05150a08070807081209220e0c0109050102070e0f0a020705030c0a02090601050408031c0f02 78
    0xc1e400040040f1054080b11001034485032061080300c00303d80381c441c000e140b500455001582e0316103203900030542554980c910b0b0443c50340200130300c1d1b00804160500191820803c94158211148e400400d5050740180c0702082141024200f510044403020410a40c1c81d220791030010386480da88d400040c05a84007104200a10900340c3c0103040c13150080d03405024403541103007000380c801c8102090381140b1403160301040640384150701c80b035032045520903001010000c040c000740c40e00780350f13070701260141d40000000e2085203004e12910000f06074000040a40502d6506540b105000381202c0c117000b5440100f0108090300030140d18162490030711010400068000462a101e01c4c500109901107003c3e004001450751000031448110740710b682e0002c400d5100e42503622001c10380a89001e54181c0c00384541c90220382c080c0000c0450640440c002d000000c050300c1404486c0100402440c1801010300041098001c08001c031240041856980980a1250380d0700c94003c0004100600980c0e1000c00d00780b03a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174752787 1250 174751537 174751541
    0x12f1c08070833060d06030f15110403110411040308090405010e0118090f0c0b0309010e010207020f13060324060510090e09030c150105120a0203071404020d0e01 71
    0x50a0740e9803600d0040d620302c504003403010081000c02c464402030450005080c180c2480e00f0b10740c000002c1a06150009202014090386c0094109070341c40c1030741448102c108200070240a019202c40b25080c0640031464171942014041e610002e4070184142c0c640da691682c840d03120128241d40502c40b10348950300c90400502c20f4100344507a5004518007800400d2110241c00228100e0780c0150b04052404000103000b00503110404046501804406409001900454802020b003849002c081e48a14001009900391500c410500060b40d01c100202c0e4056141d80f41000c1c4081010344507490380100d01a109401003480c2c3d4000340c01c0d02e00c080342001c9940500c2086c1c07080c1041d20b000c1440110f0b10b0700d041180d582d640110790004941740140800c400a4005005503100c19500c046da4103100c644100242040154100051b10740ea00c4001400185400c86550149601d03401c01007583c1495a40070030b0fa0740409020b0710540c65155804240c40741d4907a011035a003c8801402070060002030518180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174754037 1250 174752787 174752791
    0x1020403152403111306030501021207090f0f030b0405101104061d0a050f01120c020c04060602030307020a0803150307030b0f180714040b04091a06012f1c08 69
    0x1000c2a071031514490b41c0c184200d048000e80c0e4001954465184044003084071142e0440c2c103c1d1003058450b48008081030083c80a003180000c1c00101c0c00107803400400040003c2060303003280c2c18200039804244040c0c90504602811b81c2c2e403020041805860300d0a1503481c2004960300d081a0030304240002d0021385d0010007034000c45485469aa60300b03091540c180040b5070a40c1c48981c0c02840e5442d04110380d1402140600e42ca01040c10403440d522100d007426420f481d8004207010240e4400364040403141040c0c442e03070004107024406135085040c400402900c41400c59000f81c000c2c80003001289680140c0400304245410080440ea25146e232460411139810381107d04030400e4444100003071141c03800141041c0c80c01c134040040c1440504000c21000001540c140664100c0d944001492040e00c40e80b243c000010b004041036602c490585000440724680100701c14100202d00300c1c90b48510303000c00c1a6018144070340460f00030040310132800500d0140400c500500d104400711401070032903045230710340d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174755287 1250 174754037 174754061
    0x61204110907030614041d0304030b041a01080303040209060a080d03150f1508040f0602070b040b09190b190c050c071211060a0c02040606020f060f01080a080c0102040315 75
    0x1401950380c0d110990440300a4400c4542e00b41c5500170503c0c8a14095028080318900b1040051040c86001a100c0c6540c00a40007103070416054818002803004141360342810011001c400401c5604000c1a56100c4c0400740c00240030f4402c44010912075076504d280d100262600ba4101d032044c0c5120a4010081c0407444070b14003410011450101d00488180619400e6440f440354004507070349803240803241110002c0c4180e50300c96101d0000c900189090006200843c052170608107541072a080c00c10305400d01803c45040b59010507940c280007d22102000c044541002d14800203a4540903500c2c0314511045490640c2840c0c0011540c070f0030340050181c60301c0070321761781200c2010380c607515000480e04200c40e001c2c0c400300c0ca000f624499403a1040092a41c0c4029180000180060742c0c00318050f24072581040000da00580d07040160711500f000701c180d0001d0350502c1030700e40d545400305158541d05103c074050101000002d40da0b00900c1c09404031801180d1144100e445162102c034810f0080c03600314258 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174756537 1250 174755287 174755299
    0xc05031221090d05030703060b070624261f02031b1e03090316050c010212030c04030609020612150f060a0f03020903010f02040f03030311040b1806120411 68
    0xc4480c508410807881c42814010024000d245010100ba199074000821200030981c4070f05000c600c2105c6000036001e240e03c11f81c0089445442c10030301a0013403149104031155049038160030000d04800c5c0b0155890317005042612003a0003480c0354002d0030700c08088183c40d5110011384031324888007055401113206041c00310301243c008082c00d5841215101d2101c6044202e2402d0140900510000c0b0045800c0026202100d26141d03a070000e00c0002040d0f8402560300703400c544003803200355130103000c405003040c2121806440c0d40b420310f104001c1c2c1d000314000601559034a41031282113440d408202e641620000b0401122072400c020041801848070f0030b01030103a1184440d440050030803100f035902c0800261690614803c00d00e50803070081d04036000d1560700d5900ca03101004940f401c0c0c4004c101810031903030316403182411402c016050301c51564050310ba50900700710070880028090150365651000035500c207201100b40c0c2c00160345004140342440c901296005101c00c001d6084d000070304542041d164 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174757787 1250 174756537 174756577
    0x6060e1501091d060d15090b18070306090201180b0a030605011d120309042a0c050d050901090f060e090a0203061507050703050607021b0303130b070c050312 69
    0x1114a20410710451000d2910058150f00c66522203441e194041c802070005800c00b2210b031034200b060200c5202d84001c080c0c0d180051020300c01c0e118000c580c0300c2c01c2e040c0d40640121410301c160b6550000c0348009401103903038880ca2021a0300c240c00c113018130708140007145a010b80301d240da54083d611423400240882d10b13140c00081d00d940910000952510704c07041895031989500f0600c01917500401d80a20203000810401444e6a258032130030744003808240e00102450310f01c003185503890a00861401c1844000b803030f008001400041d08540f0344042c1c1c980152242c0340b51005230f48110503070301710f6010003000702e40100e2029800341050940150880f1207140a883e4844050101d100a640054020740c4a50283c1c0310880890002c000e100d1003102159a803a41c1c9440325810510165400310058006071907925415150b40040d00c0003d804501540ca40140660040d044003c0fa1103071200081c1c0210313400f024048411511002480c01800b65103a00851064090066002d00003076204030f20304e021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174759037 1250 174757787 174757789
    0x60102160302061e03090d110f0a140721110d0503030705090114070605010e0a06060207060806010c0203010603060b04180b0c13030512130b0a020606040e030706060e15 74
    0x1000003484030100c20180d40309041d9020f0220a6104408043e450158981c0100000000d02e005620071000074000e08050782c11003000410740445040c507611954884460b080c0e4580d8003081c44215290310a603446102400404200e0070102036030301c11285011440080b5025440b206105ca8151348120011404107446000304a180c200300d40f400f5080d640207100003600540108014224040141000300c401403810b0385070b1003694000d4030100d41c40707030b21030b070042207821004000703582c00150b00d0b107041c000c0c0350070542e0096030365103d40b040e0720800030020003094031640201e102c41c41c00c6801070b00074402035889003000c1d40030b02a80d28110707000700c0c5044101603000304001e011001103940f08180c0007a07a12051380589030341d00700041c0344c030344511140301c000005401080b51402031042e08502d203840d1400040d8980c94201e0070782c800307442c0c0c4604100c20221a079003c20b08a610550440740050a8a000d42c80d0524600070540010207a07407a11101140d010a0481424030030040141c0b0034000354040d030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174760287 1250 174759037 174759043
    0x30309120c050114090a090f0507020a031205070e030f0105090601050f01140f0f040801141e0402131b02010614060a0207061409040c0c030f0807050405150f130e060102 74
    0x2060182240c081c000c824030203036116400000050814101503800c00c03203401c00141c0030115991050107900c3d941d101d8944d03280407501425030301c4503040c00900a8101152005400000741c081d030144425500c034005a280d60250080301d40f00000601251038013402543d51358001e140aa50315130f4284038030000080d8510b41102150400b80b4185c4d80c5800280c050391007407450390842c140072250b14005201d40255800800082c000804980740041900d0240003440100721401418070250030154801219031008215042d0b0f40095040e904603580c1c01d80b007024070009200103c041d041d03040c118148408040c5d815003000c01526a46c80c45030b0146048801048000c1c801c80c2c4e041c20158001c01004c126003402408200d043c030041000d06803410300783c6030004007101c0990f96030202150401074188145030384520712645552090404095a0411903000f900d24000c034891a4440c0300c0e41c5000b20629901541a1160312004c9100652101c500e1400040181054021003008800d801d000440541c400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174761537 1250 174760287 174760319
    0x90109051606022d01020c07061404030f080a020a0804150809010203220c05040510170f030d150e040311060a060b04031205191107050102061605031806010609030309 73
    0x10f40c00a0000194402e00944590b691010380c07503403500d407000210101c050a000400c0c201000b01c001e080d03002c0c1082c8001d0400703c00100310602c820014070080c0000303004820791a00b49500301900c9516001604422490003039175003c001c0c203d0502080000380c01840c01ca110781038500a8039003082503981c2a100c00d00306d020403501900000c4000300000c00b1143c43c0040900001d0044c0e1310071240540310404181507400556080950310601c00c01005040c042100001c821440d0a001c3c1441c18000c2406031703624054800d4100306642c0d12601da0302030303503010100440204520031071078880749011704010f00381c1d540300817a00b4200d0040e8000100120400c1c0300e200192040c1c281194149030a5481c4d000803802106181001e04c6010001550300d41c00e2080c0c0380e0f07200d5440c0e80d190f1038490300008100e82410b80591040d81552301200910200c080282140f100000840c90016125034401c1a011180c00c6140d65601d080c0c01154008030340076511681784410b50b40603480d80c801d4a6650f10216440c038010b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174762787 1250 174761537 174761549
    0x6031b090601031806060b0d05160c030f030905010905011a1c12211a0d05030702060702030703080a080f070801050603160908010c020c0a0f05150901090b030901090516 74
    0x5100000707a00c80d0b000358070900c064580407030070340075100c0c260fa141d0040302c3c0e49805c013030000c5001140d4469241080c2c0100d56010821071a249038014411002610f500458080201405545802d03028468400d0b0312042616401c103009120318211030a05034000c1103e40d490991158010601305c249040c03d0320840030812030000c40c101e00b4041b030b4031054a07220711561040c1c1000100000140d8031021150000d2941c004d49000048203c2c010040d511100c098145507400760070741988000c00716401200b59549a070301500c00030355843d000d100207402c0c1207850700000c09280d40403075501007080d0700840301442001440620441c03900c41d0b620548000100748074680c1d02c4a81000081e52901003500c005400c070f02039081c250300d25920740144a0175500499245001684000c80140340380c034221882d04002e10035104860070480c02c103c0400c08845c0d405920848003840001d9501081c0d00c00d00000d070092001030f01c126102c1c02e107104030902800903800c042e5003d00c1100070b54950b40040005110403150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174764037 1250 174762787 174762799
    0x2040302030c2b1112010e060708070f0e03010f180b100f030204090203011d1510080712050c03011e05090c010e01030e070503030a08070f0c05030403020111030d1406031b 75
    0x9006844985903c00010f400c49686038032070b07484440c640390f141c810a004a03010300007040f00da041042181c030303100d030003021982040801d0041c407009a400c0402240c410689142c152007002e580300220f40906800c400709081145014008007182005000e01d0301d01e24414041202c00b070707c4180c00e032592101c0038061464a0342c0d80510401c01850190b00c5101c0d05032000c0e0001c10b041ca01c280b20f03007080380c610b01c0081909800c040b491000c40315030002605d500480c0c0080c80203085050000150783c400c424028030b26550302c601190303400d112040003011209540100240455000122000c400d080004030b2289030f9801d007008a400b00c1c0c804a0b04c0031071000184d41d80000464140d004402030691020415418010b0600103c0c1e1614140300034800d200403a00c0b80500c0307060880b4001c0003071901c0384810080112040c00400040c44c04000c031000c0305d40900e418030b110080c200c019815441602001c401d0303586402c81c2e20010018964409120b50ba0840642d8041300301020a03e40810b0442d80b5075034407070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174765287 1250 174764037 174764089
    0x31b1219090209071b140c15251b080708010c1106070c05030f1602010e030303060310150e0c09120a05060406020a050c0d110607020d05190504080a0c09061d0a0e010e07030602040302030c 82
    0x7100c2100c080704280d011301200494607c51506e50344856100790803000d444c2d008020703703010740d41003401400e40c406154540300a050040c42003e0341c403584040c101c07004118040003a1824803404000303490b0b41040a20840366200108400075102d2040f540c401c90200c0d104001c20741403440c020096030720440d0058007602c03c03d010782108200410302102000c021160300a00882c0700081c8907604c03445000b8004403190b8400d440402c102348452141600489030b800700d5552000940007041c61a0020342c4a0409a2100c90f1681d003511640105102002144130706180c0d08070f01e6a1082c5070100c603403000c00c20b41d4480d8440e0380b000c9841e2004400000b0103e5010806420884851001000b989109192075401d082e128200541499803400c000c0d298036001c0300301800640501d11416008008081c031464403a03011005110b810080184440c82441d6220402a2049001c4d000300d42031005520503a04025181d24040c80203400c81d0005900070720802000c0c0c40b00c1c1c00d160300c0c2445007203004044082e2b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174766537 1250 174765287 174765337
    0xf051005071e0516030303060311040506060f030603030403060c020a021009080c0f0a030506040807141504080703020f070609090609020a0212031b1219090209071b140c15 75
    0x40c2d0304904089449114641e151512011640f4155015510a9401203061071031030030013014050303008400d9842a40f0f0142445142d0340c41c82d0440f80c030203c01c5441584c5954503040024194011030307101510301c2e41005282188680d01195410629100f152000740c0302c00084011602c0304250301030240981e000c1aa20750300f44c45c2500c014621a840141502c20542e100c0c0d80f002c3c10054240c0c2c00f154090030214440080121550540403115144d800802d00407280d0540d00102c008041c1015000810024a10003414424086054907514500031500e50544d11400108615264801d88840b50f18002001c41c10102034021900707050030035070041000155004d002441903202030050104012640b11045240911002420411580100908075843e144812058600810007e035464504e000c9120005070307100c08900340c0041540c40c1545440d0709000760320840040c150000340c01450506400190607500040c9146131481c01d8031000c0e048071035460858094050120070800d000015501c40b616 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174767787 1250 174766537 174766583
    0x6090305091c020a05011b0c0f031401021905030603011407020d0e03010b0904030f020f070b04060305070e1503070201242c040b191d0105061c02040504080708040f05100507 76
    0x70307103904140e0101000005a64980411219072700000e0f81102196003003090040306480980120100030007546031210b55003003503070049a00039103942442808400300b905a20254004112a144a541c10601d821309a101a680b40c121049210000b1214261000b060030180030f00d43d8580d00160400f000ca4480e941c058610072800c0480c8821485000045040c0135420045207004103c500516940e0b1400c103a001000ea8000400c81400d100c9100b904540c01d4032220390a8541e64440c00780c07640c8035100c0702c004901410121030680074640342d01d01c021811422109d144011196486100011041c9042e0821041820030fa8420a6604c1001c0007030003003146610701503440313030400740d081c4051102c1c0704448040ba904100c00c4162074444200c2106203c1c802d00c18603402c01821216844ca0480c1c2d0321412007040100748000b401161180003180401403da41a52603940c0c0c00050703113032142c0c1c5518000d02401018403c1910074013581b1829104c0c80e008004035000700b83c009040d20809055007524120f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174769037 1250 174767787 174767807
    0x11407020d170304060f0e0a0f0206040504020a08150a0b03160e0a1205010f02180f0a05150a081501080a0c02070e0c0c0609160509040f06090305091c020a0501 70
    0x1030421005100ca00004545040b055071041400607140c2e2241020308110040301d40d204100b554251600040b180b4011000070902040b590007510741c0030308035051008c0759941c0210307804150058000b00f000c0b41c030130380c00080700c0e4030940301c0d5000312649499400402204002c40e01c600309000c44e003003001c05c080389207202400da401d9602d414501400c1c2884404900c0552440c0d12003d008034181c88135008010081c0900d2807501400e60741982042070081c04440003428141c80148140301c1c00301450f0194640900540c02040f0042c4100c40e641104a5401a554056610840043c80070350000c1d52540b01c02c0c2c0110045a01a51181e9140c2c2d0f030b1142110040005040340000c0d40b06071080000c0e00300c00b00c00282d100e060030b040201c0e240c10105000c6840e02d407001d010308010342c01200140303400c0302c1c011001c0c90848400f29450381094445060882c613081e01c0040c09070100741440c070204140b580242c02000e40ca081541c0c80f080c01e0301032a1040e8160403112038025840002c07c1c00c02c00140d0710a10540d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174770287 1250 174769037 174769039
    0xf0b0901110706050a05060a0806451504030504090b0303091002030d06080c090a02090a030512030709170a0602030a020c0115051c0305090d0c0302130617030901140702 74
    0x6000000901e0304050740e04268002c42c2d842d503c840c10403400d403040303004032a04050181d60b01c003003481c00c080e035613502c9010090001c83d01d501c000d07103100e80342007003141c480302290f11038a080c4045040326440c0300b0350405a00c420540d90710901e200401009095050240300710380680d2068105401c1050182c09000040c0c82c682d8103202c18007140c1311603650039003070170707034030300c0c10741c000b10760380c9440d4100d400a5980d80e40c082c01e440d070031550f00c148281e26403207080c0f0341c000a000b10060369020242c0000e40c0d855401d81010b4014450300d400d041d24072100c0d100650044800e0744842401c5a518100c40481442c140302200041d00001044000105260003958200340a000c000d07080020b207401c0136013150611254402c0e8241988810030003800c194a40c8400d102c0701000c40c401c00003407914083c1061095100e118058a1800401c00034407444022080255078010070f5045c07203042c140031100141c0642c0c040c1c140300705442914440848000000c030742c4103d9041e1640e028503d03506c070141a02d0b4010410503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174771537 1250 174770287 174770291
    0x30f0105010e0f060d090219050306040f0204090c06090e1008030a0c030201060b0c01061a0c03040e04020a03081210050109050d03080a0212040f0b310312060b09040b0402070f0b0901 80
    0x30404070ba13070301005042141c44618000441d19030324010044c03d09090752440c2d0414501e5003041c03045403800b0a04651203900080e003d2504c44540c0701050060110410103000100f99000c04200c031584410a0b4040f00d401d110f1704240d54440403030b0701044078458030504250b40c1c81004601203980c05040c0c3c03034680c03d000340000101151707500201c081c0f940c4226440c4103d6555564240b0801c0c2c0751040c4100d0540f01c1d01c010314101142c3c440301690368400c42c020034131200706180c0050f04541d52348100380007846d88001c00c039483d012522600c0c083c46d501692060010750107007001045e254401c5c03042c0d80440d4402000ba40b4014466102559800c01c05080091030a80800c903450202c20784148060040380728500c124807100d03090818599600001e052420800303c10510302c801c003841d50f402003020304941c0550050103501c17482e0a440c860b4910000003080c074144440001d030b1000b01c5000d8a10240c042c1d41c148101080101003008a210750301e4003c0010b5010007111011491a80000358028415000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174772787 1250 174771537 174771559
    0x60f0905040e0705240313111005071110080a0b01050409090b06010f080609010b0d0207020a080c01140408120a0903050609010c090b07030801090e0a061b090605030f0105010e 77
    0x1c1000d5800c0e00d80c01e484141d0150400304800c0c1403801d0703010461001c441d6038490a1134051000f5200b072001412010154006542410500034102104c404001e001000c0c42040308541d2000b070103540001005954050030781c2000c01d214145003042d031104130495940d05646e0f0b075520b250900189410008a070401c01c0c00e20000c01e100f0034a10075429498001c0402d907001d440c1170000101007a00800d1504100140f400900c803290725040d407240d055608a01c005502c0f540d071184014000d0103882c8010b58058000b1800165404010070700c960382400030b980b40a50800e451007502494401c9120710b040560180360542c580543d504080d03e0108800c0c03828202c06a503d4484a20309a0183d80c1c4814596690125170741098214540380001d00303041d042d140c18039080b910041d020840510544042d20b88688400660010a0204036800c40d4082810012184002c1c410804034441d800041c0110720f00300c0002c114203001d4030560740714184c02440000301c0c1c0e0038a0011a4003031030200c0074580103e0a00c107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174774037 1250 174772787 174772789
    0xc080403060e0c060a0909050703090602120405010c0201020c1914150105030606010e0618150f0408060a0204081b03071508060109061107030209130512180910060f0905 74
    0x4020002140035900100b000c02480740018285611843c0141c440c80080000362101030304510460100e81d103905000405566a64040e0044d00c0340c103000034500b501c0090714114041748400010b002d03500401c02041041d24228099080740315500b42d08006a01145c241200c80d0100c810f845100c91288080d600b4a0119180701481e143e5458450003184200100600c4541001c10010381c1c480402d18100c000c10140d600452510b1007040050031f58001d241d02c1d0b82546841c0c402080c40d074115000f0581e40d50381312500820503550028001c100984c080c030f40224107102003038020b03541030703403100c40141204402c0c108101c00e14142c1d00c1ea07156003600890300001213602d0340e0503214030607020750b071600207261404c02c0006240003111380140050280011010780102c0002400506032641500e0f6108291035001c88919007845a5500922a105940d0140810000c8002070320110301000000c0b400890b01e04104209036070116030384a0705c55145031080100922440f04d201540e5004e04140070783c0d9442d94 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174775287 1250 174774037 174774053
    0x616020d1403040303080c120a1505150403150501050901060f020a081b1c080a0b010212071211010c050f090402130605090a06031a100519090e0c160b070c 68
    0x1551026003070b080440c3c00c005061700b100803e81c1c400c52819009103017600c9212403134084500502141840e80c1e440101c2c0031007200941c88080078080082c49004844420b4442ca0311542c0b00340070485088800f2404103070849494043d2074182c400007446080301703a0034600c04507030301c08100d610441140310f1804480042402500184101464282e00700701c0a1008040d0038038010301003032410305095400c00740805282e800310149400c0190180081504095440106c1c42d020720444102105800003132420108004d404100300414a2601c5e0b80301d00c0580120340c18220794103540400c000c00c0023042405100141c540c002d010701c00d4000e2006041c030028001603c010700540d04581c0126000003030703564051804200560041c042460103206c405145a540700c61281515000c0e40103a8551000da0845070244059400c00050b564080f1341420072a40d0040051095100300704005200300003041e544254641280c861400b007520035050f25103a41d403a0f566104004020304108900c1e08181c200041c44030b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174776537 1250 174775287 174775313
    0xd020705070b0409090605010e07080103060b0d0b090f01060816121a0a0c110c180403090e090a060c030506010e0d39081c08100504050c0d06050604050616020d 70
    0x50040005d0000355403404504566044c1c2080030402014010007141542c400140c0341500d41c842008218001c051002c00c80070410084024089918030040110346000021000c009407829002801255600c3c00c0154603200d040566100300d40380e8410900400c00807100e804021840b8203140d204680e62101111041c404c265543c1d1151501d0780840840c0715800703003039011130010141c0540511620f400c0000c00400f24500a40025020000010141409040e04100405121410103a035203001048103840d0312400004481c10340c81c0c207442c08103980c428810030f481180180c4540d071315800200c04010007441e480300304880c0074a5101c101d8164400183c0c40301c0c40548021820346104400100c402c03040840d41c0c00240c0d80741d00c40a01c81003d004840841400c010700750400d070301140c0b20040c074801028210342085030058144001d00003011203c0000b85401461000304201080c0c85100300401480750344291640210140300750f4004482d1400468061840100800700c00304813030340c80e1880c416207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174777787 1250 174776537 174776549
    0x7090207060b040b0109080a0b04021807020a03090f03030503010b03250504061115010302060f04030501092a0609062601090509071202010f050a180308030709090506060d020705070b04 81
    0x40e0102c051281c1400d006555811100f42481d41c4264200043c166880c5441c0310050407201c1c00c54042015500d590414040c0e4642e02507442107146007840300a95582c00340322049001a5004034000382c2d04e050414030b4000d507a89507a44500d9646041242c0001d50000392040c011541c0b0684500c1e5404c107410100c82014819448480d12030f4a4540d000e01880c010010003030158100003900c07003507902100301c5107040d17039411604640c407500c0d900803000e07041c001c6c0d0b00024455813800c2c90034420300402100803000e03003100c80703104440d450760b000507c040c0291b14452500030800c3e52034203000e29400780301d500b45064155040c0b95110019000d001ea4080d40030303401a050944c2d248280000070006004030303000ba2802d41400d40081c1c8540d03000030070000005002d0010000045010190a44560b0b070406507880c501c1d0801e14060f4681c14000700b25070080d10801c0104020b80c10014184850780500c1d486584024041410560040010b202940c4184030440385800341103404a600ca02a070098005041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174779037 1250 174777787 174777791
    0x403170108071401050c0c0d080705010e101b020a110429010315030c0e060f03010507030b0405060301060b0403060f140103200405060d060b0402161b050607030c060c020709020706 79
    0x1c903143c00b040880310800c9506040207410051042e000c900010b03400384c1800b090320200724610b124240b9000034026000c00038003550800d406041c0c0b00d4400500c80780740000e02e036401c01961200034104801d0b107440481420250b08072513400404250032603c20350081502a00104018004030f00c5486000d04855803245000c0c0b6400c0316080550341440f909840200304107a01003410300719164107410006074405c0d48046404d08000501940350724440815442c00903000f4046405e1442029000e0a0710040482c080c03442d0000080e541d1805000f61422902c0b42004186002d0540e25154054500014049003040d1210000c0800071440051180214041c0004c040c41c190480c09030458403402c0105288038504020500c40c06690725901524419800f250010321030a444c0c0216000c0d0248428038a400c000005813002030060031200480d03109980800c0d10921515601000114015420050002108801a84005020381c3c2c041f41d48424540100c0746440e50300c079101c4007a43d20054044501d19 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174780287 1250 174779037 174779039
    0x2190c050601060c0503040905090102040306020c0102031519060507021c05060702010e0304051f090513090c080109171b0304170c10021c14030906010617040305070b040317010807 79
    0x110600090b0302400862500b42004140f40d185c05a0701d009500035403890303da54401041c071041b4258100c40c01550300c02800d54892a031000d005000790411035180c02a00c440a41061117840d0080da0743c00f60700b0001c03012a5199041c0042203906800c441401c07600292006054694120801c5d0000300c214841c4d00181010b1800f182c001342916007008202e4029801403005100b136695011614491007a141091440c07035544000480f9a50075580c042a004a003401d0290207680c5560030100c440d600400c1070101c4155640c00141c22100d000b5009804000c000c9402c11020f25031030000c100000510381e116104641600708107003160701c55804040f02502408101c2c3c4003101c28030081642c0b0030111005120882c0443c40a500d50400d1400c240002c41044048070000e4020003007802c0d600200c0d400f0b103442c0c2c64800303070080e1788203401c0c061000421580003e158001130302104161150b0350540c0c859007070091aa6800c00071900152040341030140341340040601c0d00980b140b0034002c01c03900d00145059 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174781537 1250 174780287 174780293
    0x2030d0306050a060e011e051809060904020d02031204151115071202160f0204060506030103032a02030a12030509030901081503070506070f120c020f040f02190c 71
    0x620408500810305040070000c10141d83c0e000400c108071001070500714040410000100c410004402d40b40b6100b40401d20782e4202254080d011300380c0045481f01c0c070302501100d80100001c005040f28080d5000a86000180040c00c154041001d6940301038100c440c04000c0e01c1d02810280c004c0e030001c4100310b0904c0c07894400954081d00000e420401ca4006d8252100c10003030f0616401d400401510038452021905032000381664111084140f00003070219080d07070140b41104410044500583c451030508201050138940754044030304807981501c800941006442242c002c0900707510817050341903c861604005602c09200100300c0c0f6100b40320b0221645526480a803c45001909205081c0d0080c0400f48260342c11a0308550400e003000600c0485590000001e0301c0e01c1e131f10743c0126401c00808111401001a1281c2d0400d1092040201807501d00c0c154601b203400340541c08010358006005203000c03000307003410303030000b44480780042002d850000544000b42c1c92184e18a20f100c0011051524a014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174782787 1250 174781537 174781543
    0x4150f08060907051b070f0e1806091c020703080a05190e06091309020d050d030b0f0f010c02040f05130b091903140403020904030801051f141e07080301030203 70
    0x1002600b2102002181810000200a0302170941690451502d6484403c04240c04000060050050b51001c03d070044d110340b020b41d0941800c0d00c0d1007102e200c1c4030404140076280404d2140c414840da60042056208650052820340c05480149003540501440400412045130081520f50501e0f140c007599804200c005041d4030a504004000300f240c400d45962003551107904640301a03000b00c0e02200d03440703242d0006c44002c01c0b480d04000d500480c5c0c070794244108880414941e024101c90b46080040d0608001800520120060103e5124451001001e0a9070207a4001117416001a04c0060388441e20380c12074040f40d6059505100c2841103200c0102000b26040340e4550108195000d4820070090851000042840403070040900401d90342c40b18226503200b040e81e0085800500c5c00d05141805e0402402904082c09070600070310422101d0010040c818041c0c0d960000299038010001c034142340d00104a4000040e0340c0c00340042c0c43da0101a18040e04080d04055010f4a51550b5030351551041500e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174784037 1250 174782787 174782791
    0x312140a0204051311030105150d0c0f0207090b0d02060c0c0406030309050f0607021e1c0615171c0c02060706020d0501060801030c05040921080403020d0201060b030a09050304150f08 80
    0x41c21901344505c041750400c901003a24115002034403083c040c0300900401044500035000700c440c3d10751525800e40c002940c4841c1c651510740030b5409a402803a29001c02c1c1e010350300c0c5022480d400050132400c803001401c04600404050324a4410f880c2c16204200028064403900d510036800114204400d11a5250551810040400450704249000815030101d2407540d40a8403840c00c0c07500110b200c1c01c3d2a02c032808042d502c07007440c1940031009600e0b450600e008052071902ea411030900c0303941c08030354500c2c00c1c5401c0840484410080400710081074000c25050282400401004004204603005803108005030000314400d501c003580310b00340c0b8244042202c1059100104008440004001054550100c06d055884c1590003084518203418404080016200c84a6220325001d085401143d4400b9141d401f42e80309600740e40603600c21103412802c0e1000d50240014409081002ca5001d1106a00100680f4401d03801e0302d080960320074611500c0b0308407242c00800b2621103102d1207512588115095 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174785287 1250 174784037 174784069
    0x20a0302010c020d080c0c0309060f0c0c220c02011e05090607020303010f03060504050c0901090f060503060c0d0b030c0316180207030903060203060d02150418090b040312140a020405 80
    0x110303203003034010001801700384080e00e544924031000810080f8007005204540706504007500d06039541115581c0c0914039407020003081403d0290002107401460903401414122501c007859501d80021084050000e04120501e10b040d5980c5000d030f0040b061481803090540341c1560350004e480c0c81c00307119650600c000100080b0440d0810401409504508041a0150f0f50004000125680c551501307034901800f010105600c41007141c00080c5002c4260801c00160358074010500986a07107a0a00d5600d250948a90f0740d550802d0125001208a5611404410600908990052605034003090170309083d40000044a4600042031194642c100040e803e480180d0300c046180c61081d840091a040f480c0c00010403160300080441c05581e01d504c0c000300c001d0b400401c2014480d5040145440c242d20503c588031840c0e400c5046002c9a80551241e00d00b00ba4001c0c103007c2140ea42c030340e000c68070081810b60510000d40c0d0f595001c070283e500158114820007031441c00507a01d50918040281e0a00045810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174786537 1250 174785287 174785293
    0xa0e010b031f08010204030f11010201111804090212010501030b070203043014010f060b0c030307080c16030903021206150f0109240e0a0e040f0c080d020a0302010c02 73
    0x10010441100c08599100c8030000b040c0078541c200b003880350480031007035000101c65800440e022013400440343c0142841d92050b030500c0c0c44121a1001a801d942c6003980f0300c0f849141c144550041c03c5069000c00071035020040c0300095054041c0e000808903003110100d2410f42c0e54880050040002082c11f6035048005070005505003880d00d102d4400320946980102c02c07514501c0d4841c03200c10000340302e8001541c2c0c000e59801d45095982082c1e8000e003500c000c0198130318104080011074120000403640b42855007409140b860342c0d00b10003942c600801800c80c0e602e0030402c00c00d0034980e51040401e40d200038401e584032601c3c149140100704030082c5035003810210b42c10207001c0c0021580700f68008010048240c03501d907030b01c0603020010f80b154601613001100c2ca8080c0401c42d06290340030101c0d0901850300e5100c209901c00d03800c050081c03000c0c5500070b400007070500c6030114010465000e079007800c140c842c802c1c0103503003501c2e2031041c1e06202d003000441d00942d026003075102c00c054080c050030034104990303c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174787787 1250 174786537 174786539
    0xa0e0408092b081809041a01060c260715021801030506030607200109080d0c18030807060b1e01122903070f080303190c08040803060a030611090a0e01 66
    0x22010404010302c00400c030880008100f00156001049030618420040c141301481c6014200824221804814000302040601c004500d05014440c800d403c0b642140c9444400c40481d0303e003071704450b03c3d44002a1000350521407500020740380d039410410700a03586c001503100c000c0c0004111043e1214807845040c5810001000541d40300080c505078411918076104a02c1c0c0c0d10b1000c3d0b0070209091509111055007454014014881e034031005000243c0302a104010844981c1006c50301041011008060030541c01d204202082d8240080c00b40a805004001411b2103408000b9108003419908051520400e0010844035a0007161802c076507a1840000d10a420924980b111000e80b41c040b1145005040c885040030b0343c40810500000d84002c481c0c0c0b4a00a84621100d5030342e4000310340700c1040c0902c4120028522030a03015080c00d052082e02c2d42c5105480d03656842032030b0b0700018680c47d0880d440090020210f0480c0c0074565120340d0020400783d03588100340a01c10049559000005462a0140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174789037 1250 174787787 174787849
    0x17090d0302030c0705010e1e010c0206030a06050f0f0303030c18030d0305070e04060f05040c050c100603140f06070509040f05101a03060a030305030403090f0e07090914150a0e040809 80
    0x8401036000282c03000c00c0c403207010231400580e82a103400402a40002d00030040000b103216651248081d900f003240c140c100d42044504004040c007683c590190960018030120349591003400144c4000350300303501d0918040c10b03084e002c01e26000700c0c20002000039480d0411300c040c00c1d4101c09021024101030358107101c21804d00b000380703d014669100c3c031802130b603980d401e94421510500c1952401402e00b1300341c0d001c0820076036080000d4009400255600070200507150300340c000c00150658091107540180110ba518401c080d501034000301100fa42140e16071100210704005071103a03d1007005446c1e1142d0081707042080c40c00050412203400c3d4203c007420000d1107034603540c011070201169890b151140e501e83e1107103400c41e0346490f19030014800352240e5901003843d00140b40d2035442285543d03642e0800700d07230f00c4800c00305481078805107025940340500030420001d4400c180610a44000e4030948039265105111200004201e0701a2241c00d00442c042c04245011085081010310140c200d50f00001015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174790287 1250 174789037 174789049
    0x131a070605010b0c07031101030603150b010f02030703080a05180a031e020309180c0f0409050a0f02180111010618020c0c04050603070e0415090506040c0e011217090d0302030c0705010e 81
    0x10001607c144400c409400d0b6030380c829040040507661000c2608000501500404080d100488403680450180a24841154070010a844206070540d591480b151205c80e440401084040c24040c1044008482a03140c410f04101c0003081c14442e03a40c20b099401c800f105007404000c403003615011500204583c171070507560300414000c0b5502c8400b000e2030f10f46821440940c80d00c62528410b01c54280460300080402440c1c0c06948a81d403142014001c4a00c0c0d1400c1000324812000034020321080e28641c01f20552203071000980b031a80f1000005452600c0d44040c0503050380062410040c140c0000320200e0814080c000340242c1c0c1c1060b035007441281484030000740c071240c26010b509102c4034190700140a2240150f0080c03a08020281e04200540c0f440c2080c3c0e454010482d0309407455003c200e400501c4010b00140c0c030b4102c6800c11505106881e5698468581d142006103590040c04280400700040d0348002080e82c03114481d0700217569501600300c51a0602c04a43e20103410b01080030b0858a00362544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174791537 1250 174790287 174790289
    0x3140a02030f0d17090a02040606090e1b0a030911131e09050c01081e0c03010314070302030705010f030e010c050c060a0b010e0d1a010605030915010803090105131a070605010b0c07 79
    0x60703040750941d0356852100f4601019901c010f54009d082c8600051140e82141400050b660640156040d5944525014030f20100f03428140400c540c04120040c1c030188680e000e40d402c4ea10940365813134408040000120b0003c02505404070131079031041c1170300000d69065a82141d04400d42c82c24825002d507600c5035611914481021814052040002140c030a01c00c000001c403060110714820280c2001007200d29650824002112001c1c7c141001d0245a2000070b00c001c1100d5009005280050805004480d12504092014149601c1d8403c20072964030030b00440504905590b945902c61460b00f004a14001004e058114003a01d003455564040e60b1081d5103d14443c0b0948a10f90340c8d90715464950f9000c003407900d40c281c0d02d1a01d18008121700d41d02500031402003005504913140650805480340e0000c20030303c58a01690b0081051031441d502503800b50407102d0240c0706030440c1940c0c0d05d050210707107d03119849150408002881b601005031502c20980501030098019041c07c035a110420307070710607403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174792787 1250 174791537 174791567
    0x180a02030a17070606031a090c0d11060f0c0a0b070f1d180a0e0d0509010e0915032b0f080a0e01020d0c0c0209060603070903060c020703140a02030f0d 66
    0x34240d60610000341000880d6043c40d480b00c3c00b001007564a085c08020000c03800d59107021040b14a000c903400050010b81150035020040401c4940105a5120b8105056141d10b00c3d13000075051115052500410029100110040000d401c0c01c0c0b001346021006001d00030a0705003031000f0713480301c502c1d195031004210325050894100600e044684034005180c0d0b090341c616035103140c0721150811800b080d03190004480100b15808075062032103115401d80d400c0c001c03001e002d4009000b00540760454030700070a5544e00440280700004000c4004400319041001c0400e80000034554a0035a41c03072006101c801036060080c42c41c0810302000c1d1450f00a05805002d00010803468480094411444003907040f580c1d40b01e5440402c04c403154107550054175003d50080280d2003010030341c0020300541007070001c4a10804580e078803031100f18216030b2000010880390741c20404611901401000241161101400030700300356004003010f0384203104040c07608458820040325a081464541c10b0950000001c1c400600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174794037 1250 174792787 174792803
    0x301030f06090f06091209140913020a06091d0609070302030403021c020c04050109020a05070212030d1a0f040b1302070215040b031b030118050a23180a02030a 70
    0x34103420035001400c0d9440020b4000e1074210300030410001a688400104c902c90742c1e49142c5145d0000b015101d00841f40310f40510301c02023a00c031680e50302e042c074040f66004090404000b01810a6004205030003110381040010420b00070050180c9003803e0004c549262450303681040b03906e02100807446c0e014000d00074809254021000c1002c15000303100084040b19181b500c0544032120b0a4000c1d9180601e0301c0441c02035160600115062469000312101c1e0161621014a08a10765003404811025510b00d6102c0e0b000c107002e034416101b15400340c628021001c0c0015a1805030410400801004403414035109030700c1d2000540300e50f290300300007402c101d060110060301c908282c00822400305120a64060040001801281c0341842c08040c40c0981d03800220300c2090108511301c50098030080c040c0008030070f01c2c6101d88603806016003001da404440104013107030b0903030000c102120b005961070a10240b04086810402450500b0b07071041c10711003400c0001e06030041c198000c41e80b1419544006042a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174795287 1250 174794037 174794063
    0x16090b07210309050d05030703110c06060105071a0a06050f0d0b0103061109060318061305060a05190203100303020f070605040b09060c100204050f090405030a0809010b060a03052a030103 82
    0xc1c000c2c3d00800780c041e000020b0740c03000251410000c12540c021a51240480d10345000c0d0b1400030b5500003039452132030609008291580710302c1e0066074503070414082203ca120303c030141190740710080300c0d10500a4104440c0480c1942c1440100440e030b10252120034040c088441c103d0010641020850741165000000043d0503144540750f070202d07100d107402060300090008244201c05e81000000030560f4015026140d05446110514907130f40003005014020360300000110b0413601091384001d400c107040c1c90540711080f02022440741660811214200344100340311003001410b40502c41d020300214040d010300700d0316041a90141040c080c5005042c54001c000c15054241c1e229401201d80850000e0300b1259003200d010200c1c0040c1d8040d00070f02d8065624503040101c1d9007000c0780843d005070f03032000146062401c00311301203039209401800d042e515034880750382d5542d58131044d00038000054540d40202d0545060342c2503011550200e600101c3c0703440707d908030804038880d06041e24107481e84812502851 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174796537 1250 174795287 174795353
    0x303021e0c0d060e01110d140405060a05060a05101e030c021e030c19111f0315030b0109140c03130308040309090212010e06090f06120f0616090b07 65
    0x2070841403608021503280c0b4440046d041d803128043c6c0a12024000140005050b4140c901050b0405480007040365112030041100c0c00c0030b0b134002540c008000341018aa5559820005041961040345400810000c1000f059280d0100e01310820030442da082c180401c1c2e8124034001d50b07650310f44102c208200c081c0603245a07000c80a000b21000070342d144027211407004948002550b003c071600303401c680703007104045000e4007400c000c000c15011400500101282903558a015405011306611058204a01da1804800152120021030103401780e4407000070528164109600d0b010f001620301c040d0654203204000c003140c2442d04000c031042d89440c24000c9601c0d01d2605035140c030965000024074500103e6000790b94588030003581c4c12244140e001e180d10352101018041c503440180c9405078240c1185000508504001c1d0094030044203003800c031510183c0c079455890070184244c420b0384d081880c0160000d4119844000d0401a010740141d440c502081c555403030900c1e1403040002401c031020741c0560190 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174797787 1250 174796537 174796541
    0x3020c060703090f080708100b0a05010c021c0b070e12060c07150207080d0f0c08010b0a020c2e02070e072a1208010609260a1203060303021e0c0d06 65
    0x20700802d0700880c00651590111038031046d6074000d1895034418004480c405034036a00501c00701b618003510456420f1300f01401110100454141a030704908880103501848403020030121185000d01e0190800d8100120700414141e8500300041c4500010030108609900124056801a25411903965102c81c00d150800000c488038103049402803001c01c0c0001172015140c000c0c03040c42405441001030880504400085031010540e00b0700042c0000010b100c0c1c020400c0090405220b44c0c012105030a1320000021030a01040c89a1501201071103541c030040c00c50b2400b41c840b221f8540c0003404040e0b06110945014000050840e010400c0d15410646240c1411601180d011048800000f4060590800a00d162240700045001512450000034528030800040741a40c0c0001d000c222880b000e4005c100502400002000309400b0b0401103500080401e59036003500c00c82a28049480c0e461750801a007407050501c5940e400408454620042e090003040c050340ca50303030846401140130034070705110340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174799037 1250 174797787 174797789
    0x501090b0d090b070503090105240f01050f0f0c010507081b0702010c0b010806040b060a0b070201080402030106090e0708061f06030e1f0623010203040b03180601031406070c03020c06070309 83
    0xf2000c00e6003d0242c241e501400851042c0e9818009020b43d031110900c80c0d454500d0883c81080c0301c9414000d4813154030740b01035040c1a00c2c00500d04182444c5100c00d00461641c4604060109844005014400c4240c05c2c081c40d540403072a410811485c0c40c1507240303030171141428136140c000c8041c00540c03403045a0141c98071480054000c2d603580c00a41e155418a0307130313603041600c003601c034500e02c0c60020300286041404942a290408806400d0825560042d102c0000c058803c80e415502d48102148480c0d062051201e2000420300030040940703080e1340c140c24040044c04400d01c4801054a0301c1e60380c40010005411203a030307450002564240700d01e4036030400c1d020403080c02c0383c2500b2450003000c204441e0403d800f6100121503000c1800f40d00d80c441810011220361a5000d40c1080c001000300380c080201030344d4400c6034800000032000d05130007410f041c80b6090300304135102e08150a180c16190820009954401032a06181a45000c55240a90f0705c030340040c00716204003800103545007050311a0b213080c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174800287 1250 174799037 174799043
    0x302060f0f030c0a0305160906031a090c120c0702220f05040302010b041a0a140a1203020732040b04090501021803060708011d1b070507030c0f0501090b0d09 69
    0x10b44a05180c40910b0a5a12050000c40003904140100f40500840d140040c001181916441e82041c0340c81c2c0146c01400304070040058007220a20418810b4485000b414880c40040ca2019030f906116a0b4015510901030482c80510b5410b110031300c016200c850000e80007114407111a000303001c1c07910701c0720058280540800d84140c10101808101034054100034100001280c0c2400803048840c84441d4404800740415400742103002304000d40481011692101c0704041c1000341807645420801c5944200f4a9080300187d04c800001c004004188104420520ba00e094041c1031440568141c810551140c840a21482e59181c0362a2659110346c483e5003042e6010000b9925040c2c0490360016440008052078003e0042c00c1c00910994850344140703040e14043d16030074800380e60320014185684c000424003030290782800d55503207281c4402c5010b82000c44c0b01e01d0041c00100e0642c174128080280a520540c40365407004014841a82c0241c061400c1e01c10080c0a42d455200e05824071014000e01600a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174801537 1250 174800287 174800317
    0x103200a03051b070305030f06041107030203030f16020307021e0a0b091002060403020604060b010c06140601030e0123100f06051b0627010f112a070302060f 69
    0x84250740540060f88036403507450f010041201c0d10500006030788120200107001440400002c0c013641c003022020b542018000c6c10008220440001000d42640440015405a4070200400171058002c58103164041000c2c1b01e400507800803240044c4d030741e0144160007032141c00d0714400000b4031108003207400b809000041a1040090381d40b9000c0001e940b20f0b4448a00a0161a0030528140d00001b807540c0141c0c8e040d80209599a16034942e00c009240e001d4958ac100302c1e10300350580c08250240078072500300d800c11501c0e91341030400c40009022071300842c08041c110390400d643da81c01c01d42541d8201c2c0180b03184607400d5000e5601e82c021003103250026046003884401000020a00c0b0381d1000140a200c01c1c001c0340c0206040c00f501120742e0710481140d400d01380d00110358a5a20342d00c030010036655044484000072036207151000904d0182c401103034179041210310101c0c00d20303195842101d040310a05c00031400b40d28000182c0c40c0c010784a0400d400044e016807000036000030040183c9007203607180001100703e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174802787 1250 174801537 174801547
    0x307030b36010518040f120302090316030803010612090f05031c0204030f030f0c02031e0c09090d2303042006090d021009091406030f070b030105010320 67
    0x96407240c1c1c1d08840c0c0c420381541141e407000c0314240c103200c141e4140c0d18000d040c803014841d0300582c0318920000400440398080000d210780d000541e0125407405284054030056261010328041c14070304a1042c40d4074071030030642c400c20804100360000f1070303041d504149880e50795000c550341504080c10b04000004d042c08a1070400348280a000310240078290346031001021102d0340d14034004164012404068030510303c503840b150000307002c0c0307170006a04111410a070841103c503400003410103241c204c0341034144081f0f044010b005501885007462240003124101d40c24101a12660340d14200b43d1203080600400b030b51340d03000c0150300110300c1941000b00c241c5240e41e0f18003482c1010340c03104482c00390402c5800c0c04003800390350728082003501c000d40030240c4800746007031564003000310f0f8850400303510040c800c40a00c04584851540110150fa200c01884a240c80c1007c4091500e444008107120506030480c080034881100810f0480381154424680400c1c50314510301141c174030b40c03030290a5460307494000503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174804037 1250 174802787 174802819
    0x11190501050103110607050714042c010b0d150513080f04060801050f030c0409020f0301020d021809010806070e010228060608030f0904050c191106070c0c03080307030b 74
    0x3055050b648039010803071031130003c101802118001c480d001002070300105002e20141c80040c40ca80032503c4010b00200e06100125026000c0c2c4180c2c4119569032006000c044034080d01c00d0140c3c803100c0800b40c401c01c000c0c031080d1300c400d005152a81ca8041c01c00341c03a880410b0b160b01805554141d11500010f143e999844620744240f03459100384208000708010f440000741510b40048045a003c0d0090042c1402e1086d05080100400350b8903022a44418600392480a0f40c509201504a42124840040c4e4079403900f0301c6c0240300389083d1440ca00c542c039424018003001d0400f084281d001507417070901c0c29001080c000103034282030f410f1009070005192680c0e101d0034140c182d410300421070f014500400040e900c3d0366600341c0300d1090554200300300904200e000c0003402c040d88000d5100040d1040c040c10300c034003c08450580b8030914058000a001c8204101800e0b01c1800314540002040c14031005200c026640c0e03040e00640d610014100e160040000303040d240c000c0d08600200c2100900409480807025 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174805287 1250 174804037 174804041
    0xa0306060e131d030c03030f0f010e0411130c0201020d05060906030d0f0309080706060510030905060c07030e13020913151404140103081b01021c0207140a08030a05090d080711190501 80
    0x2241903d0040c01744007c5050b8261400c03005060300c0b00c1d03038900b055a33a201e4036a064007548145009030040e020440e54681050b0512560030084520340c00541e80303000c0718890383d09035400078007410b100b5a00c0501340002c940d000207003014604000c0c104440d06000414040e0010105800050446400041c0d6501004201d40c4242c00703a800440e200000c0e4510403104400711351000303100070510740c00340001c608428500301c044c001081c464640301800507440c03408160728410010ba2510030701d4012a20a4541c9803c0d4a82034100708003038810808640a02c0380c1660040c0e040c424010115210007141400352103a8100071300c8910b2880403041c50f540e403803501440f90b030701c503201c05110f18508034250100314030103000710345c2c00145048131129840300038806d0318000d60050303078221b0b0a0301c1c00c1c102520103080107003d502e0021340107444607034580c503241c11040155500181250301c03035040382d201041c505410181458214010f850300000043c191860b4510b45846080c41390344059000c0c1c40d52007000015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174806537 1250 174805287 174805291
    0x20612130b0a0203072304120b15190501030f0207050d08040209060a050d080d060305070602060a060b041805060609030703080304060b04050603030f0c10020307050a0306060e131d030c0303 83
    0x60107425250342c0c81d19614001c9020aa0380100024846540e20176000d084614005482001094203450299114510181031040c04021211007010700300304041080007010003a1001d40c1607888511440c2c00e4080d9208201041c05680d05040c6d881d449101c44d03101a80c140d80349141e1010031510390504000c005002190120760481c403407030341800083c41349d05003159400111040034001c240301843e545d1b280107040d008a044809111340d10100003000c51070801c140300041c20140c01030802402e0030300c4541c040c2e500582100b910440100010000e0100000d101c240524031108001815148c0400003a090b00c652503006a2605c40d5030701c08014001c007400114001d034030605041001c00210b5044c03209070742c0200c50340340d0325800a000d1200c0302d44500b8000c2030519402d01c107070f40c41405032907810001c170780003036400000080d030200c2c100d1000c0e900b520800307002e441c003400c18030607c1c5040c0c400101c0302d03058000e42140050b1107085c1c03440c00001c01a41180d845808030283e0303460350200083c09580c0c4d041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174807787 1250 174806537 174806543
    0xf0a091712150d060e010e060f07110304030c1e05032a0d02100c03030e16031a1005042a05070b0106050408120304030c05070e150306061c02061213 65
    0x34004a0b6280e84401000803001901419480c1001d200c1e481d5500140801020400c0e81e5482d24203080c0144030134411140309402d07a00056005041c12000201007002c0d041000781c80d58000c10003030002c0392a082c0400e0482c0d480490032141c44015900c21400d8440b00ea0065030548110b401e5411800900c1400321030822814492180d4486000d0030080415160702c5e02130340000441e0040101d42d8807441ca101141402410040b880303001018141e89400c0b1285144003100040040c18820050b14910040410799508140e43c0e80742001441c01e81d42c080035200c3c0b1032240b581c4075101c0700900520611f00100044060301c405255444c180080d010758409002216020302403000410014099800d4406071250350004203901c100301e0001c90b0290744040d0054085c00000d0ba080e0002601c10042c40000d0300c6050031142c245c1c1442002a1401d04414220b68440e401c181c0030001c054441900808150040380c83c2c0610401340c50001c9241c2d40b09080300308110030b402c0da08020514580032020048144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174809037 1250 174807787 174807817
    0x503030f062d040f18060228051c050f0c1b030f041e030804030f020406090c030b0a06030c0816110307080901090609060e0f010e1206090106050a030b0f0a0917 70
    0x585101c070041780c070800310302c4611001100300c0d4008601d40364084d10002040c28011002a05105468451352020741c0d4584000340700090000150080805280401c0e240c12006000c18144a03000c0803101030300a101d00b05210303011410036100d00c2040d86ca14808c0303003010290707aa40c0e80c201e0200096603205000e1151506482c03414160b5041103204c0b08006c0b03d8100c207007141058107603501c50a9640d41003400360f0b401501c4d9400030503213200700c0c0701e2114404103d0301c0002d10090098140b00c03040c49164420418145005201c045103508016030701d501c0403803003030402440d0701d5074030b02518981c1c082946210144400b103240000c00c01d0181c000c0818401c2600d40400c6c840d902c0c202101c016003240210b80010319400901c081b142403444210410301414140078a41e607032510007044003001d60b04011503060b8032a00038482e0740d020030310840d805020159502d0713142c2800d549920504440190115254003d100001548003015600400011798001c0501003c2600b001e00b084141d0410411105000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174810287 1250 174809037 174809051
    0xa0323030f0d020309010f060e040209150109060309080415050403030207080613080a03110a0c060b030303060d0f110316141009060e0a240f0c0503030f062d04 70
    0x6890700340d080c021156190052418001020b5080a8101e5840d5901d486103907a0000d014000d000c060405c288210703172545405d00400800360006482c0b018140d9a4905403251030340e100c2520000d03164581404190f0101c1131070075854510865001361500c141300d010b605881c03130f40080104101c0b4000e60031a4201d5444200040d1901d6080d00e060f00c00490380d030b11030b0000a442501500c0c0031181d41c1000140040441c8079070002e688100e40b2034000540d140354140401c4501e2080c400000000d80040d1700b140790000109612010f0700d01c020300407071829010702c3d0400511401c1800320400103020b41f40008050f0683c013840781254080c02141401c20980d009090402c802100b44a5032a542e8410f00c031460004203441110460009941010849002243e11502e0340d019141c400c003140c101500304400d801d40109088066030b031310001c210301c502818000c10000026650441c842e400480131a44442002072602c00c2d024030f410007540722180c4108601c00d100c401000803014141c030241301503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174811537 1250 174810287 174810353
    0xe0904030c170a2001090b090c010906080910110721030c110a02040e0c06030c0a030506010c08030f100302030f0601090e0a08070b0a0612110f0604120b04110a03 71
    0xa802841d440c8000501c000d40481e07800303500801084e0080307916800010b4010283e03110764030300c010100c909503403030b6103ea680000303a0b50307003d144500203001d10324203007919042090382c8944a0511784000068903403612800c400c0f1203602022125000e90060280b01340c1041c0406010110080310b05440c0440d1801c18030a00480c01002c1440382e85140801601c105000b079400c000041522030240038092240602440321a11141d00550084030301c0211245c443e00416001000c4e154000c01807070400010f950b8a00010b2500001c1c0d82d0080c094007800e981d80e80d241c2d4803124017001141d10280d80342c422213090142519000c03400f2030507a15155828010401c2d11218290384140103030004120303000400038500400c011010140d00302020a1011800036907803031071081640030051040c0c1e0046040c0960ba08141341c06150303541c0e40390064a030f0b10704092401401c008150050040506900c08100008080110400030b20301c400d400185100c0d126600e905000645882001c2036030100301c4600210741e21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174812787 1250 174811537 174811583
    0x1215020c28020f150d0e030412080403050f010b01021b1503041406070305090d080402040e0d090e0127020913050117010608030f0301060f0e04050a1b0e0f04020a0e0904030c 76
    0x801a880100c9180ca0020145d032001002442c001d120f407804188404198080f14400c035500c154090002240c541e4210300300641094881662050a80e1501200c108aa600070814400c212075aa543d00d003448078190100300390309101034000e20028000000c000420680340f04444440071801c0031035850b5912450190100d45099400b00100e911502080d80c8552040003603650041c4003400114a0910303292002d07142600c902851400300e034551034140100101c144140740107001000c07104041c0c0110075121102c0718003030044c1d0b503801500010b00e03110f6070b1914458000d5041c00c0c19801c204640e543d24809228a03425451001207508101001a40582c00029103000e8842480d8561460b4a80031054441c00c00900c40030051040c000040c075456903c0b44505803007007034044000b08152401080d200d030150842810384091101000250405450300d036014102d21009550040c2e658043d0390007510412003c1d10f10540c00f40c113050410003059888040c0e803c1c081d20038108102207520011080003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174814037 1250 174812787 174812809
    0xd0e0f01110f090d12020607170402060301050d21030204050a08060c0d050414120304030e060a020a11060c01180209060a0e0a050c0d02070303060f1215020c28020f 72
    0x14880a00c829084050401d0042407542401044c0342c00d4100560740d510321840520400d2009a0000d02c20440c0d0142c20100b00d1420303550800789044c042c601680010154041802094000e46c0c441b00707100b0800110b06c400c0c2c0341c0840e443c000060300711800b841c0180650b0060284a0059403000c1002580d00800204180500008a0700d9401e02c01011a90401054002c000391380c02030001ea465040a442071020350500c03101e00303401c6a520320f0700b8140544518030380e921490080701d04100d070925040e400300341c2036410340d0704c040c82016801003440040c1c0b1601814003602004d519090030900e006582400d0b0801440c03003964444550780d01c501c00c01503904594828221881440c03c0003034001c424581c009544900856840c60904501c02d6009040760440441100402d544140a001c4941029045001002a071140c1d1400c4122951002d040d01840391740c60007080d4000c80e8090b1100c20521103400c4401e940c040641550403c00c0d9604034104900b01b00360701901e411401c655040c1070030040c0f0300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174815287 1250 174814037 174814061
    0x1c11070b0304121719060e04030e0409030915120609020301080a03030b06040f121a060d060b0a1502060f01080114041b031202010207150e0d050c01060305030d0e0f01 73
    0x3908590320740d00c84010044400400200b00035245068401005409600710b000c0c2c00c040150a2080d18410810401c8a03940d40281c20700c0d07400385c410800000d0f07000d0760303840b900d180035079000c611051244ac00340c0d070a10247c3c100790100b8a80c4000d00110301d41c80808076040034ad2894003801010380d01c4090000703e100a003d10015504103411440c0031034040d40000d010708038050601c81c6020f507200e4101b41c811490350040d144000340640c001c2c5c2030051400c0400451150142420350b28102500040d030701c0c203505c520080c05241c480506461540d2040440c00041101c0c21014100b120302c144000c0d02c07200c040351200c10300000c800010404841c148940c0301c280e28410142c01560304c49484d110325142c03c03044155a54400088044000380a0718081d5001801c0d070740001da00c4510f68a0a0aa0001d00c00c421000d81b6141a041d1759001000050400069005050207507032180007856aa001d8044e03504084d00905c80020b0706500e0f44007a0f48402d0141041c0d40980f1107040d0554003550076200010088 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174816537 1250 174815287 174815309
    0x90a090501140d1a0406020d0c0806060301140f130c020f0705030d0806130e070510140406030207291608041101030507260117060c0708090a081c1107 66
    0x401c80b50404014081c02c2502a1101140d0b00c12803021449515030115012180f00e60042508440d0840500031900c0880a500700344107540341841c00b041440c041485942d01600d00301c12048501d4403401d000b8a0a0b45010f01302c0c00c0f0141810451402414418042100622807010600076401c404100382c3e00340c0e41d000380500b5014442c0c10040b511081c004d0038042c1e001013500785583c1000704e540300340c0c601c00c0c43d0303003015040786441c08041110328070010710b0006c2408140c1d41c0481d84e0360803c03421681507070b505043c01030b2034001301c0c10054031b500c442141004143e5000c8441016801c903511401d48189070400100300e4041c0b0a0b40119210401aa001011106041322011080d0f0003600120740c0041d0790b1034018090604ca1421042d040c20700c0400035081d9410704010300c0324450a18002d5010281400100f8803030a1980d4078008a21030311502401c508000701380c10f081552041040e000800c440004c55107000300c0344240242d250308070310580d80400c000d02e04078401c0f904042a50000c0703034040e4500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174817787 1250 174816537 174816569
    0x20604050a060f0e0d09140f0117070e06031f06050a0509150d060f0807050103020405010914010306051201020a0305060906010c030503061201020a050a0e030106031e020d0c0b090a090501 82
    0xa0800a4545850442202c42d11060f07144d900c108104182c500c4548240c5d102541c051908182c03c1000c0480c0e80124043c45807001c0a60113642c00c460100240c09412501c20443d030b41d840c0c41124542c10321540079a00003000030030300c044da8449d414181e25004440c6040341550366149403d40c2d1621410300340740080303002401041d2862901d0060302c0f14003440c500c5207614145002d44c005040750095003010102d0448803400b40b00c0e8032002c22020000d40b03400e007821440c150038500080c0482c000c0f48150200f042401f9281c6d01281d11942100c03000703040191060b82260030940240b400303034016030001d6000034038000000d502071405d0a0750fa4015101a1210504000c954804555030b510044c44a50005141d407030302100e0f410244002c0c20390120070f9070703600c1e00da000d8004014820118410700c03334400d81c1030034010b101141140d65000000e40c910f6409110184030361000c181c009a08a001034400c00c000341c40001c0721119000208035100080301c0d000c9480d91141c0080040f1107080c0202d03a072010314450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174819037 1250 174817787 174817793
    0xe01050402220e0303090a0303050105031519060b120103030f030908191403070c030801150203030c1602120705150f07061d070f030b1e150a0b131401020604050a 71
    0x480442ea805440c001c501e40341000619072942e031040d01c1d52800c9910a5001d00c0078140d140c03080502400c0c007100078020342217502500c0e8041c11009081402c2e5200e251892121504050384510b004089103041561200100d0400410540003480f01313401040ba500c001004d904d20900c5880100b59002150b1800c0103070207429900d103042d69201ca8802d10003405110810725500a029600c03980c7c0503541c10700c4101051900500440060b401b0554003100c100072440029008819203070300004a0a50503290145e4011802010610f040c020350400c040a1082d0301904001c100842a103e0994400c009240030f1044e41a191180c034a4101c000c0005209a6001500d103403c07000389180e052400400ca40401d003140e908047ca03d50100720500d9052408108012b00c556416501190300403160a1124410f141c08582e038100428401d00400608004100c42d5650000360001c1d10b12030411903216000012002240308590050b440c4130b81d0b1900c003412241d03200260040c0b280798800c015246101c4995 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 174820143 1106 174819037 174819079
    0x7060b0307061b1e060504060e0c0a030206030c030408071a060906041b0f050409020c01090c050f0a120204020d05040609060b0a0b04060c170f0d0e01050402 69
    0x900000490f07410729401c400300781c0180744010308895508160700500d420100003800039281000b03002c24042103501103205804000c0c11101c1480003d02002003c0300c55120003544040d00f040080d01000110020316001032042d08820306058080e40c0f001d00845515401040d41000701003004400e02d0090460743d002601950100071312101c14038904542602c00384190207101c03c10468080c110312803c200e40041c02051344c119202d613001c07030001c0d01800b040401503075851003021010400e4034020a0141300c5900003002e4111031898000303000074080c40e881c0113903417160f0b090007050140403c40c000d1030b00c258825000028203805600e819412a104040700700d016060b50130040c0301c000030000c11a000d03141d150500c1002c2220614100703440c00c4466000c02c99044001c01c0707610020040002400c500f020106007440b509927a28159422070764201e0380a540400c1005503842408008 = true := by decide +kernel

theorem cover : BRFrame.Cov 174640287 174820143 := by
  have h0 := BRFrame.cov_init 174640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 174640287 ≤ n) (h2 : n < 174820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
