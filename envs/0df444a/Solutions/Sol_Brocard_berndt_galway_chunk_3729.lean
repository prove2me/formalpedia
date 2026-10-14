-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3729
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:44.680277+00:00
-- url     : https://prove2.me/submissions/95bb5be4-b11c-427c-9a43-e2311a8c2f01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 670503597 ≤ n < 670683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 670504847 1250 670503597 670503607
    0x3030b0d05100b0405060603091c11060109090201020f030c101e1401091a010c08030601051e09130c0f0e01051c060e01050102030a021c0e0904050d020d11120f0f 71
    0x207009a0850f01c40e40f8001d4034180055101c5004201490100715904a5141d10124a010001e02c904540c0c000f8203400e4181298800310702c11202e0704101098208904880c1c41c2e4a404045590421017a002e05003160040c1d0b00b020a07540c029600e4041c00c40b003100f03025443e06260600c07aa903016048000950040c010031008442078aa165000d400744900030a580c030b00194802d95641d00d41d030f611814507050b0744540c00c01110340e44030780c03198001070501e904019082c0302841036038070300100d20161100020011511112035004126400d115003122260b4107051003102222290001701c602e103920614180360036250011740c0129200e0103154007a000300444029840c8900b145680070030282c88845031040d0980c0e80f40e00042e66248a00300c45640180d00c08554090700d011760086409210030b680c5410100a0300980020300b140405840070380700b50b0041643c044a541d0100081403030040c60381804a0704c0880c03100640d0b04e5010811200a401c5000a401490300c141030088840080340d1011103074441e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 670506097 1250 670504847 670504873
    0x50906151c29060f01031a041503060e030705010f0204030b07050a17010f091d0618071a0a02100501030201082a0f090108090a0b0109090204140901020c0d14040303030b0d05 76
    0xc420b0a0300c1c07142c001c0d9100c244007480c2d94401e02802100840050841d01090031030383c08d01c4001d10315100c000007061071150010000a07105d0080d42d004001c0d08006585960081c2429421107000e050304043d024810013003080010003a464a507031090352070a140792540300707800040d507802000c181010f00d01c4075400004581034403400030034001d13a40e04c0300d420401c0074a003942d115040c0c00504d03051152603100310001400c0c4410780060001045942d002d0b50398540c3e49050300c50740184444542620001c0c003055501d001c9078100700c0308a128404a0f4244115450b40d0000791100d8806807000c945c00749940c00e800d5092806a0340d825000300c002d54080e0380c48282c0314030039643c0c2d0800d101d843d002400312000b1420035070b400500840302a4225002d0711059203460184002410b02008c1260420345410103821440d8241d91600d00c102a004009603880d440c03142e03141d05007640c002e0340405110941283d14510712003813042d0b80581c6e505040001e0b03881c00a90020703c2540c81c00c10010035604c514a08a160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 670507347 1250 670506097 670506173
    0xd05060901061a030903041e0308120103060b0612060609040213030506010501091703040b0d0605061b01050106050a021b04060806180d030903020312150a030501050906151c 76
    0x4840415140705020165029074040d0f40c402983c2461650344180701c03d012020790340c04200c482c05190b4140380300055a964560240d9040198046a1451948010070901c1018016940c03804405c469545c0b525a01c0d020003100003001070130b4980030700c10104540d207640e100d07a4100d82146415502d5000780079900d10708540d6916003401800d00242403c54001200706640d900b000019002102950901e0b05180c0358103c01d40221003081d40807030311100c1c0025a503d50400a10306024814503451080d04110445401e581040c0e21001c200a03003008984009a07011901e030101280200c4040b01d005150400039014241c1900729401c980141400e0064441c0f040e100c55041c03000c0b0000b51900485400015000c0740c0080350050701580040244101840c1c00359172081d40800f074803101c2c0105209500100750500b21a4104803002c0c4e40d071b038090040340b0000308a195400030311210f48000110f808008600c01202c00321040840102c1c854018080000310700c5500a290701c0d819020102c40c0d052041284 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 670508597 1250 670507347 670507349
    0x203031215061c0e07050a0b09011814010e0114070201030509030904110d0c0c0f020603090f03130806010e10180b030312011e060906050c0a140303010f0b0c07050f0d0506090106 78
    0x140a601d001088105000302141704002c0310b400820704a0303803501d0400135902c1030340a0780da040d04200300c0c02c540d885120b84d5050502c000d00344841810401403075034000034200001c034081180c103204030001c0040001c2000350031904019428603011a0a86400f0350325459806101c001c550f109060224048404d20319074050420b441507090284a004803580050b120707680f004002400c6010319541000c05814110019504501d141d0100c403507140700031000d5420360300441000758860303086030010400d01100300011405070a5007100000d440c1098868403501080b28031403820b031640e4601d0311b00501c800a0740442c070f0401c8041d0035242d440c40700030a1180d490200340501c803010040360500e001c40307502141c403480070b40d184d0380c03103100a035810a0025922500711002c410011310030290740f20300281d4003003c58405104420025a00da50401e01800c03100111a040490864028040e4400001c0c0008050080f107006a034248901c126580224025101940b0080c20f40c0c0706280a1103000c00055025030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 670509847 1250 670508597 670508647
    0x9102703090308030c070c0b04050a050906011b050f010c2a03050d18060e06041703150a0f0326160f14210f03010510021504060c1b020303121506 64
    0x11240c680701c9048840901850080e20303042442c2e0307079040c001401d120dd203090f000a0141005040c4041e00e00e0711440725040030004642a0300308800000be894003d0081d92000c0c01e03607007000702c600f40b200b81c82981351345000e4014101c0203107400382c840c1c18107025608840c90131148000078011040b819070580f2502c110b07044101d6040b45031400b109a111004101d0900803684000314002e901d2118041a8440d0000342c003810402c01c401038030382c603240d0f50488030a00070400c0341c00c202c84551440c10049000c0c0c1410b050f241860800441d00e4901c0c580040c00c0f070341d094241000a01c0b41c884a41040580354010040c01451441084a2140741c14000074186840d880c070741c00034203000300c1804048990760143c01081c400304101840140b000703203082040c07a40299482e10455129030342207951004000c1055506680940c0e88021203d22141e1200d0041203c00004220040c200e03d5640400e079a1700c07a104640009a0003040400d000c081d00d031a0f00ca010351401420203445190700e43c608030506206400c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 670511097 1250 670509847 670509863
    0x40b0612250909030206040303150f0602060901050609010b0f0f0f0d02180307060c02090a2a270b0325031e0e071203170f09102703090308030c07 64
    0x42d003000b103400b54035155a4194090010394555030750035009040f190028002c580e0000300d02040108076440c03440c00a15007580100382c80c2c10f140c0e040c603086400c0941804d001c0c030b21043c01442600c076520210341008101c40b1110b80ea40440a80d1240305004092403500e240500140c0c24428883d6030300540903a41002d0038007092041c81c5e40403d40e4441541c440c520102d203040840b0405844c117200800d5104a0a200c00f040c116141080e40340c416401107003114058001a0003000052361152424001c50650707580302e001c0c4072161841d00b411841344d00c643c9810030304c0000010544c00d03028900310f01da081d1050b009042804440c5018020700b0407148203408609000d180e42e420803941d4050312021900000150807082e003401140c0e20050074820303095050100c01d9510584050031170389218440c1c0d02c03060600c41c55040c1009603c3c1008031010444444909141c98850301180da011400350705601c0941c0300041e407440c1d1800f568030350606c0d031025008200100402284014500041250360310610306 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 670512347 1250 670511097 670511099
    0x70311030d0c1e2c01050d020304030c0b0106050406140a0c0507270b0a090c090b160b0604020715051812040f05030a030e0f12060426040509040b061225 67
    0x112502c0fa84a140c00c2c1480c8144000c005450704c0b0300d5801040000185882440e0105106031041070341d1003a6070850015000f084208148800140041c0c090241d514140b41350510b420401801d480b06000350060b000e1001400758201e500840e4100c1c0e903194030909a800c45580c541ca03001c407400030440c40c42c6240180030740004001940d0701c502d44200e80010014040b150402c0250801001c03586440030603c040703080e000c0f8809403004045e0859078004c0d64a500c0701c40182c41e09116040c00500480d008500502c58500000da006803550083c45c40c0d000d00261540d10002861402c10107404c100d40d80d030042d00d10b004a905072410040c401c0d189401425a04a0f03070310340c14590340d5081a6400750008070260515451440c0c40145800050030040041c01c5089071158518180502500e0841d51410181209d928004074500d51950062241e40c1c003508061520b804252502d8005100803c2010a100060316503501c60740c3c0d510040401004551107c3e4000034290110402104200c411004c4244 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 670513597 1250 670512347 670512407
    0x150b03010f0b190e133002070b180d0309090e16050907080712021b0c03060a020f0717070807051506190501050a0c02030f0304060e03010e03070311030d0c 68
    0xf0303001003102e03581c0c80c08050543d035407901c43d060781d510100e0450f101c1100020b107104040c48128255405c1302400c054501741e00c0e56120103890005142d0046010503001e11042d803525401c824042143c0000703a40702c0b154101d480c036040b10801c10340c0c1c0220b00707041c0c0350101c1c5001d00d640000b0764102152991420f5504103032036400b08405088200c85d5034000503800c1c1d000410540c0b05822201144081031009410f04410210b00c2440c0301c05101b48400c070394082e415004041c60104050780c2c02c5400802c0852030502840011502031003110b00151540750020288009400000100c43d000c64010740784589813800c600d042525074040711305400008002d000030526510700814a05501c84c1c951985244061034070006464036084074082c00c091240c010414005a101817291080e00042000615a5281041405040507200c048514020381c90030031001d00d407020000855842c203805051141c007000e52000b40924610614800d04903081c28080c0042004d50058510f1070341e090304004900d0310800f003013 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 670514847 1250 670513597 670513639
    0x6050d0b06060c07081509060a052202180c0705150609010e150d1115090310020f040f060206010501120912140705120706180f150b03010f0b 62
    0x51018012040c880049001441c0940040104400310390943d0303001d070b036607039242401c101c6040c5046528490b8202004905002803004035407040310007070100054140500c81c03407086a50340d141c0c02200f4000c0000b11055542d00c0250b1100c10075440d500c5c8040d03181410081040303400c000000c6460781316201990740303201c20340c0c00e03451f2007114017500c1c22016a00c0d00342c040328141d2b40a0701c505100e1800300c0803c84240c84080f48201014011400c4502001c581c0c0140418000c0700301c005004821300f4044540c0c141c0c3c01003030b400014079000708003603180d140c00c02400725588510b0303200000b41205400300040035900841c040d81202c0b4241c0f01d603e070803a0b00825810a840c031000c2c1c0101072514401a080301180a0810011078000b280395032818041c0e942c0d241847c0140e12030455001001c0880c14404221181c0945001000c1c40b204129440d00e2644d214800302140c500000c0110b01c0c030800380c8001d150a5402942e5040f0020001d000300c0043d0030281c0014441d41c0c94441c090301d220362040301180a04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 670516097 1250 670514847 670514869
    0xb07031109041d01290f010c0501020d1a0303160b06030f030d0e120909040b0a11120f0903070506010608040302120301140111010b1012180506090105222405070908010605 75
    0x28078a6800d9282d00d2010000c000103001b007010305000e891204000440d900744050074031030004000c00110180b80d880504001b003480e002040c4a58000c200e168142d00c00040c060280540c0841031051381c1e26610001f0717090001003c0440914800410510101c000540005480003100c10580b001c659031029944028070a240040b90000400c4020a00103003c40c29800c0e41301601840000d0400b0019807401d48580c40380d182c3d240100d8904052010542c14402c201c1d401c8142200154508250364ad585030321500b052050800b4032441030001030a241c0240200c0034050840c1c0e00982e6a5a114200d41140800c0c10140a00081c10802c60340e070000e5051083d000080c5000300700c031000103215041151000841c09040d040d13242c503040070711b1504c01041c059160161196010b84110316145d680242192801050804408079001d2a40c6081003074031189650660080c0d00004810400c00d03240b051036001c00c8084c0d0a040c94001000010340e4001c4104043d10001d02c002c1c03041c641c1d50010070200303110f2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 670517347 1250 670516097 670516151
    0x80a05210a0905090a06090501080102090324132414061005031603020c06040302010204060f0c0c0e130c080304090608010506031005270604060e0a0b07031109041d01 73
    0x4012003d10180c40c008801c117502030503000300828080d032102413030000d9a0080e40990324507900841c0d449058030b0706000d0111450f00d0420110007104100c10002500307040501560070080584ca0003000384103019503481c8881c054140344185000e81032800d10020450610170003101200e03003020640a01d404011104010300580c0d4240c2503480d440705e2101d04207010b43d01d010602d035080012645511042c86a01e00c640d0094000680f540e141c90409041054110003580401c041c103840705001880d40c3c3c1e1420144d43c0c0700301c100e040d80d6503807a16030700500400301c0000d00601c0f850301c40014039031300010003442515000402403000325601c412907800ea5000350307480341e4580c001c840d800d40000041e034000799100c460400c0e50203480030382c401009555602c1c54a000210b0300610108070901840340200d8840d0f02c600c200504450403030b42c85000840744050890001c040c1ca070240d04460f4444c9500b550001c0380010803c205648540403240441681c07100154015402d0001c501c4030301c1400c01d40000c0c44c9074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 670518597 1250 670517347 670517357
    0x9081e0306130b0111150403020c0a031509021c111906093b040303140403020d0e0a05190f09020f03011a251506081002090406080a05210a 61
    0x8102c18604010307168030801c0da410041d4007521046101c03010040a00c03804c00344030501196041c9400c000f07051052020070070340240c201407030400c0020000003000c132195000c2038000402c01c00c50720000300401820460102c0c28861520004144000e103050603031044402c98000b01074408404070120b40c4907180c4510340c007089501c0000c11248c52850010000b41246c0c40b04203d407040c5030b0b01c200c0548201224140d180304e05080400003090f4161240001078401248040900d2403d5600250b4a01c400302c0c051007041000d04c646411611810300c8080a000e0052075411039101010017910044440d200b040404101440002011300c264800c0302d040d110300308585483c5a003040c038565200c00ca81c184c005c0d5021810072081400243c401c030f444506403a00c0a803001c0b1010b250406940d45120081a4205a8600300c000c0220070700000d0302c0b07100b11014080c0940c0340c640e0100002d00500140c2e106030a2401003408480c1007003404034401490326400920f2801d6211103030340d01e110368080c111449011030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 670519847 1250 670518597 670518619
    0x13140105030f2a0603090f010c0302040b0405041a030d0c1703040b07050c070803040902040302030c1801350f21030402040906200a0905040b150f0c0109081e0306 71
    0x1511100c800b183c80d4454100c5004004680000c92400d80c800c654030401504140d0b950183c1c0b590038084d825016a6505c0d0541c2003508081c0c21078007070301c00c03032044512480c3e032054400c541c4090024101802d00f0001c007601c0e140207030a0310240c080b0b002c0000480712205007002182a100902050703c0c0140e8100c180c4400075900d80000340c072075900422441540d8030401200044041040000b40b0160150000250700e4903d980306052078071103010040c03445450783c50806010b5822828105044400380074894060f1440781038030300442c42542e400d09001d60000a5403039901c401c0012043e08000300c002c1180c07104c107840c001134100c0325608011603107804400c0000ca40544ac241d086002131501840d4001461540d0354100c4004034441100640484000308a0340c062681141d1100d005140645003804003003e054005941c070303409804a07581111010524440c6814450261100140346030002c0040c0001800d10700c0481d0081421071007900d0100420748480104001036901500018002501c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 670521097 1250 670519847 670519873
    0x17010303051608031f2414121005090117030405090a06120b04060c021203011809020a0603091e02060a030911150c0d090803120603030913140105030f 66
    0x954042c101c11462400c003507080c0300118402000850050800b41c48424076100d04440b00002e940c040c0e44001c1d2840345800781442000c4406c10440d42051151400c00c4540000d1741d1411800d00510364030440306c09000040059044440c0d01c4034065500132941001c550b0b9958406840760304c2d200c250400903030020302c010445418030f9028241c1000900b00e000c10750a44411454402d0030304188140c03030814420f003d00050101903c14100c110040d440030b002141940300b00340740c2503c41031090743c14580e02e03011144203231400c5900c91245194002c0000c411290780b5440140038105145042d2410b071103440001ca50262040d420a00e10f070f0b40a003e460070b05000041c25401030007118420ba030401d105107010001507130f440c80399051020064880c00d03103803060385244a142c109080c001405001c00440240048200042a01d00e060302c880c00da403400741d40d05000b180c02d6000ba2011640c0002c03840312011607480032500030030803685040050024aa13030300c004050b5120310042c641c0042d43c004007000010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 670522347 1250 670521097 670521107
    0x303040807140a0e0a02030609090304050a0b09030f1501210c0b0d0e0d0f0801080105010b09090403090909060204050f0103060e01170109020d1214040b12420117010303 74
    0x1030312004064654144d0b440301c030900c006108460300ca144030b50000412981e450720203502a0091448002035040ca4141b6002c40c44034001da024800b2011303008a60901c060b0340030058120038140000c1500c92804420031320f80c0a1290a000d4083c060506030010000708140d03858038803100c0e0708a070f00c1d02d40d1103150603100e11a503800011407400350343d1258860841c1340f100300040d65800500b43c3d1090480000c0c8940200203200603040318503264100300c010011005403000b0780308411021508081251030700e14080e01c0705000795009408003401c2c01c4140041c80003d50250027100d6055442c040c0303403039402c0011401c9844602076907100628000040c41001c01e80b1515415074400c550001034002003680004604e50480c9030100d8a400c1006d00d2320620303a07804001099140c004031183c50800341081d010032654000c04148090861140c000204007084541c03200c10f0302c240c81c0c08651882d645040000c1c0d0340c0744501b41140480070a2101255465100d48060481c0c90861068030400342d08540e0704a907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 670523597 1250 670522347 670522379
    0xb0f04050c0301060305030406200d030e0a0b010b0403170307020d180e0f0402101d010e04090f0309060207060905130506010201240f05010507050d0e130908090f0303040807 76
    0x40c803445012188120340c0c80920404015600070b60013075490380d02d8503000030034500d40c2c14580e0b108003072078080d2981c9020002401fa454441d0608000c208440c41110079440d040c49035502030700f604005400060101101c00040084e203008091049158042c00c030748aa0900c41a40d1200050b404100032203071552041150f080b2040407101001300710b43d6111b804d514a900c0a60305030176050b000f102030004603c1d02c00c0b80b015102140d402e00780c65441c40b83c801c0354210302c0c4050809040c07003200b41c80c00b423099803582c2c40364444030f510200c450700130846810020250aa6800307010007501c02c0c03200116255005620140807074000801100d4403002c4041100060302014000c541950740b5400c12100c11080c1c603130b5484818204203500300711103140100004500c40c2d40d50145041c480f08004e41c03800b103480400c0041c1d900300d8a00f08104d4142c6c80c1808594141a802e1080ba0003a180020740700412001d10010010321078201c6800300c03003405c000201a1644254405c0b005183d0082508201c09482d02c6008a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 670524847 1250 670523597 670523603
    0x11d0a11030124050f0108010509040b0901090b09010218010810032907180909021e13020313140607080f0a0f0204060801180e0d051602060a0e09070206040b0f04 71
    0x80f80c203020382d10b11151642c005003000700312444821018443d50900341640c119881003480e2401c200c0d407407d00410b000701d1014102030300503408107002440c1c0703d100750041180c0340c9c0d00a014207607030319004919034001e401c03030707911081003a0503d9071410140d840b03801098011115090000d075018650b541d9201880f1030011001441d40490806211001210200350300c00d0240341c0782c07050b0701030380d4001c841784e440c100d900702200381440c061649002da00c0300389011131250790400046800e010032900042100d80d020b050001c800c2d000104001c10b112002000400d03141c8501c1c3d080030b007121170201c0c8503290b075021035003000042e25150000b0000e60040030880d4203d0050383c0c0010b1001c01d1128808203991182d000100414055801080550020059408104085d55003000008040012079495400d52040a4100f1801244000149d080840100b400c0383d0b00524850340d0311119030000d007045000410540c802c1c1c5442c0c00045c910707030000c02d0061240e03501c2100c03000310360795403c420804000050429 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 670526097 1250 670524847 670524851
    0xc0501050a110d0c03140307050708090415140a06020a15051b030c1201080c0a060e0604210203010b09040b070c080d090332040506070f080a03020a02011d0a110301 72
    0xc0341c1402e00a0049071000300d042c0d43d441c0300d0080c00341006807942c08070300e0b842620207a0420411110941c081c0c1540d140030780c05844960307140d0040000a000c1c2c40500070f007600314194601e00045800307024411229207001520001e0050b5038807081030780c0300c8804d0007016016415074040035501ca400c43d40116480b000c42c000410744003106d40303580600d50b001101c100414a100003203e2000c19944820107004251078402401001c007184049440080207100f12405c1c41001103200030681d13203150546000c1c02c1d0903001e400c8426030750b46a5282c000074054060b4000c5d460314101030160304003404103610858108031452541c0e11415011150011004030a0380ca00308180440c2c0e44030b02a40c0100d20301c01340070350341d03074100e4045230584020522a003007050a01d2403034203503030359007984668030680d401c443c01280e11036211001c50500d4402c0245034040200700f82d0b00040c4407910326405a02416030b550940d4000c00c503080002e258005034041c58040c2003820340c403800d03040340010603507180c1c4001040c0c05000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 670527347 1250 670526097 670526117
    0x118090b04050309010e150909151201020d140106081b19050a08071107030611040909120306050901120b09010b0a14030f0102030106091a0f030a0b1c0c0501050a 71
    0xd150122101035404403141c0d040043c100d119580e002da5664a06003003150811102c0302411201e1510f03204044e00d00c2c0c0039841120018030302005c030701c0b0b4180b8540310241003800142b4038a201c0c14002c2d8450380c05a42010b10705890802d841d80d203402030905031a210303141c100194035507081302c0c0c1c001541c030940341d09400c1e0200300c0f0b80384007101007851100d98066070325819221300107480d000c1c20300080144404200081040560240c00000520340d040303a030031000000d03015445482a4520b80308640120041e41e040a02110812502101d64102c011b8a41c0d410448240c4800070003034482000e01c81d1114040c04015500f0100d07808494164012448400001d440e01e400404150014695448120341826402d520380f2103080a0001000060800c0021445d640c14080042d02da0045405030103211421550044100110901120b980e066a125450b032645002000c44000c5c2c007242801e5801245001d19024000100b506010102a444914070700d40908103c01120190405410501008082d0103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 670528597 1250 670527347 670527353
    0xe19180e1225060204050f180711012406080a05010b1e1b0106090f02030c030720030c060105040f021809190615140408071a04030803090616020a0b011809 68
    0x10b035125052040c40056100e03840d0200304850496420385c050302072807140038181c02e02145410b8040c0c0c802c249003003803c10181038080139801880890401c50848101d8542d20300f00420107070b030710800c0341c0c6e003940c84803e581c3e1103071442e0082c1c5e40b0030320624000030b00500130400840c10901034100d2985001f260b0754244801c280c65a00c80c903880d55060034140e5541e03c2c05000c1841303103010310603003440700c0710055140d800d22584860540c44000c000c10b04210b81c00100ba03600d01d82000214880300303502c00c00c40c0d03100c80003100c00688428003031054921542c50010043c1d00c00c9130174000e0700c03c02c01020601d00a0a040758051041c03440b0010405072403030341c440c44504440d0501e4401c040280280c600c0309103690306101e0001d080c0e400d603100680440d0000344001c000d00080025018143c1d100100303c0341d0140c808142652103802190401050b000c0048204444500002201482540342059a42903043c0702a020f80e220100002d014110b000c11130010702a14100d0021011441c282c204000358249080d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 670529847 1250 670528597 670528657
    0x6020d020706031a0d0f1401110d05060d0b0c0309010501060f021b010908011a0307060507150f090b0a0b01021507120e1015030c08030301060801050f010e19180e12 72
    0x2050485a8003003e001082c18031142d87c0c00007041303010500c0200544111b15149a5041c002c405405d80000c3c1c07110009596a203d0001115605074051170494060804030078100300c03500212921041586044000103441344100180b02c0c07800b4007a00985107103221055029003201c041d281d542d0512508a8000407244000d102c1c15201d0100a102254411240c0c42018107100c4035510034020804184001000314041000d0750303440c1e044150b00001c0c1c0c01010700c03078003000c0d007a041e1000d060000483c0070021a034184e500720404ca131300d09078261080440c5003614948205010b550b0a400039400b100110600c202a90122200b680c000040352001c1c101d814410082d60541c8100140a00590f081002041941000000944a07013400340d4107560608070005c0400b00148030311403140a034000e0681250b4003401201c43d131144043d01a004082c103074585901d0303007441842030b010008522441c036110318003980f04140310200410060200c5880c24001b52210381c00854040503a80e40144801859103014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 670531097 1250 670529847 670529869
    0x702010e090c041809050309120118081c111911030706020421050604031407060c2307021c1401050921070c0612020c0102030901140106020d020706031a 67
    0x100521079542e40c2400002e800607044c1040ba001c03c02e0030240110001080070040d11030610b02035907030103041340b260810b803405031010f0701d61081c0c00b0344403e80080500450360002c00764400c0d078034440310001040095407401c682407a03848068125061100d140003403141503026600048a26140c0090805400c0d51802d6a2001c1000c5984507800103003046440e041c11a2080d01c0d00c111100d004001841340c0310540c0300c6030020402000c0182c01c1e50566100f540ca2f0040d05d02e047d0708040c2c1040076044806001d0460401010740d03080d508406494408404804011a00d00395806085207041040300c40014074000c2207064119400d81c11f081220502980c00d10815100d42c2c900401010310000540d0030a01e112102e005031700300400c0400000c4081205070500c502180c180d840c2a00f00101c422040c08002c0c00b464003200301550002040c030000000540008403107225841828800c1d90b40e0707031b0f002daa4a030300084002d005a00f21a034200049070080d48040e1490000c1c2c01075100d1012002c1c0003500000305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 670532347 1250 670531097 670531111
    0x50715020c010c0903030f031104150e0109120507210b1005100903080a0809010605060d0515090f040f0203011404150e033f0c1e1e0702010e09 63
    0x80403809201c241030074065162882603070b0801c0c442460039910020040c40c0c0d0405240f080c1034031068611495481501242e0082100c294000d010641c081c100428045502e14400d0001e519600301203100305400c10f1080c0c9865000c00100a0246080d00010000524500001040b084002d0324404140c0c48408144640a900110101c150404c020032644036070100c1c4c4102081080b0300c0c20f20000b514182160303440146820400b01e40d5903007850179805802036401158202d080850311724820700b140c1c0c00032800b0b024882811640c40b4040c2c400d000740e6030011140141060310030004500801c125906803010b83d0f00150020507003c124686103944a0030030703241140d145129248a1041c0d00b000d03c02c04d0f540c5401003007d1454460f043c2d100746100100710115022145410b204441c803450015100da013038800304802c402251501c20715146054011442031510000d90b141c0d0400040030388812261069020742400001010310f0198008a8000e40d60480c18440d405d540b1084a5031440034003071046d25 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 670533597 1250 670532347 670532351
    0x20a08070f0b0a1b0c08100e01051302060a2111071a0709050f0a0f0f03051203060306041514040803060f04140a02030405070b0a09032a0312050715 65
    0x11900d510814076a0066128500403081449201010b0b54046101c1250360080303444604064540d00740724400c0452a44400802e1040101d070500b018000d8102c0400c03049130b0310081000e41e50300140700003801d14003040254081c00420004003528010710705c5203000314900d40008401595014103104031042410400481200411080300b000040090420100760074510014181442e1902403e030b4400c0d4058107104081000b00000e01341c980c118201e005051080700d610040380c1e181b203046c48000b8079001c161024001c0050051000c20a031040364090304000d03000b03010310f6450b84c07034000e11070040d014250800e039181c4500d010760100d02105140100c3c0544000d83d07032030400d04100101c0150105015002d54100000080402d44000701d8a5004880c40c0700540d903035440745859814201e00d500803000d036070b1011408407420f6500907050015640711745481c4500c40115654408047d6407814500e0708513446070f1040c0002550b1071000401042c0c03e00b41035041007080e988260400348001d071401040e03a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 670534847 1250 670533597 670533599
    0x1403030a180305070602280203070311121005011e03030f0804060905011e0501050f030a08034b1302150405031009051506090f04031b031215080c0d060207020a0807 72
    0x12401d050300300003102000501d02810500d40c04607450341100c2c400901813800a0a911030cc070740341e10804000c2018500141c42040000c2d40e0b2060040c0b8080c01440c1d207541003c040402040080303150710080ea40c00d03403204031580108500c101d82c2c1c444018400c0303034091780700c26503c00012002d0040002d00340c20001c0c16041900c1940d03c0c4030032510142c1c8028400d24100c41500546e880c0821512038007500980c40564039943c0c80e069044074001d006005042d4480d070003040c81545068881c9510050040081c00c000e81d45445400351542ea056860030f071840e04c5024000018a41007a40b005644880d41d611400c080d503603030000303051003140c1001c1c1e01c1c82500d801076201084800d01070b010015810490a0860341003d00100742100001000d10101c1120000071400303040c018141c0564000303041180d90403564080c41c0007028000480110040c00d8140600d020014006000407020380761058003c2ca2064040c104101030000302c0d480956086500300925000758a4a1800c24098090840144002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 670536097 1250 670534847 670534873
    0xf0415020a020124060516020f10020307050610030309051c080d0903030b03070f030209090313090e0c0a1811090405130210030c0e09040618030210061403030a180305070602 76
    0x2d00e94051303102060030318260188200d513044800c2d144046038644003100d4031030b2244041003484600e0101c003540b100c0d404e490202100e50010041006a02c82c82c19940c0d030742c480844030860782d006400020082440385a0030f001c90309103408a5007000c074110300340041d00080e40e1913040656000b020820115078072840040c00303140d014010007000b0030040e00100307440c0c0e1505a20b10580305090000a116a41d00c0002c2104070f00c080085c0e030000015224100d60300c950b00d081300300c01840a0721014450f400740c0c81e05c0c1e4030a4507203280801c013207032821101040041d03500442c2200a20f15580d0703a0b400c1c88424071210f01035481d0f41c420a44159055140c050040c1c407140108521040c17240190b00c101030410780c042c610103920011511081c90140c40100c144e494a140c40c002414202420030406519040a4000d069000443d030816000305001048075a0b00c41c003048419000c9102010341552042004c40b90042c85926280440100e07907080c81595900da948044c00c0078003941c400701c0103a00007221040a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 670537347 1250 670536097 670536131
    0x11805061006090f05040506061210060e030d0c06020d14040c0e01240c080918040b0106020307020616030201060b0c010219260c0d060905040c15080f0415020a0201 72
    0xc0c26103070a100100a01e131815180960035580200c030700a540310004506161034107000d80c0d46071094400004440d10305404c0c0e0f40303401c00a5108400000b440705d014502c03142408100000300c15615504c10001c0200c1c0e4460b90007941c0f20350361014032180d85841401055050048250140c1e1003424030304050391820500e41003004043c0c1106c2a1903e000c100201004a0580e8804e82d81d0840d0412000ca40038904061055000349148540c10074800400c020808404203a40c03803003a4802d000c5040142d88031a02283d403400707010402500240c0801904175503942040100303002c10301c00c0c800070604036202c040f0200517400c822280e07500c9a40109220000340c01c00410454000f015280c903141d503696050102840391512034103070a0906d6a100404d541c0b2401404450820b6100c00c400d0000704da171007100d900102012242a80c842980d428045607015054503401c00c4266680d031860413a485a5525a807078440203001220411181d0398820070b840080d0001d03103c2100709400005072510101d500d17480b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 670538597 1250 670537347 670537349
    0x1d030f09030114011d09010603061119090501120203060d020303040b070c1d061e03070602100608010c140d020d050a050105091501120b010e18070f0c0507050d03020118050610 77
    0x43d890748200140807490784409411200e40380240b84d4402611140c0550f4010070013074001600260030f04092450307a200c0000141400a1400c0319108400711115003210702803aa40111400a215807641a03a02c003c642c01545c2c10600082c001c8211007040c2d80000d24550281e402501a0000401ca060521000510500040c021910b040d801a12b194504035101e0308020151440344d50b405a4016180c003500c0d00f0302c004400040d08450289482e50006983c3e031042050341606107003020f50119031810107004000d117000141c1ca410b49031004001030000d0a410040c100000aa801d00c00d0710b00360310440c001d040c011503420b8000941d1b941458148203840300024038400000d040300074541c440da60710445202d424036840f0000140c20703501e2001215100590094035911094007041d82c0b0981121030700f45401000d02c6e0b1100d1061011115044e1202205043d000c0d240360082401000641014803404900b64801d01c0001001001e0742d40c0d11020321500070f02076801d90301040c10002c4c1c005910341014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670539847 1250 670538597 670538621
    0x11806050f1002010b33040b09040209010c0609030314091f02090d020d120e0a0f0b032d010e010501031118060c0f0312100b0306041d030f090301 64
    0x20000506160208445507809024280601031141112900c076100790310402c0d0a11000305030900380e100d48010000b542019030841746005c0e00c001030522610400d2011a400c403400b0a0b82e0074100101c070400c120081d0005a01d240c18803d0210320000052954860303542c01c035110f524002042a074601d8428038804005084400f941d00c210311081211a030442e140141401d100c00141e59400710b40045191007901c0c0400039084030500d1072010070880c0910308078012800030303078070380420b0304248081008615241c4140510301c82402018022555a06d0040d6440201c60380d040a946143c410f2207030000c10480321001480e0340711710050100d40301e05104180180402d1809100d00c2518401d0b030b0400d032040720010f80709031105038445803843d00d075001910202207580c001c3d510b80350f1401007487c0e02d951113250790004501d984400518413060317928490342590103141c21142107582c0d40082c08028200000a85401d000c0785d00d003003020250810080c0b010308c1c0c0c001200391303c2d41051010f05094540d00300c140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670541097 1250 670539847 670539851
    0x7020a120302011d2a0d060e0705030d030b03010f0b060a080a11031906080718150302060a0f0305130b0403050a020a2406121a04080f0a0e19030309060c031b06050118 73
    0x82c03581d070b580310134046d04917035041400003400c52241c04900389130490b0b070303400160075004070401e4010f6183c040d40070710354082c42607000b07004003070b46c10304c0440071a0303443c04906500c00c030144121201144600c0e46140e200208680024010f807142e04030740c0a5801c211001e02d0155420902c0d1125200b02d802290020306141d00240851401c003a10001354401d4000e0300308e44c030365440c02030582500950501000454001c4c3c0305541d50103400c00300074440c2541c00c0d00b40c004a402c10340460a0071040280034580380b50001101711052b1101e5608803460740c05204928118030aa2405001184c42314030320740b203174806000e01e0801000401c0c07541002d90b8141d0707001c92500c51003141000c000c41d0a104d1103595039060030562114541c0c03546000c1c0351301d00402c04044504e002c0442d441100c47c1e0810f00b0700d0326130001151482000e00c0c451203002d020380301900005000404084081141c980240900e01882c1d102c0e0408101261403d0301692500465030f400351401510303070b0010000b0f000b00c5110740c00703105508442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670542347 1250 670541097 670541173
    0x50105030712020a1802030612120a12150e07020c03030c3d020901140a0e09070509060708040509100b0a05030408070209090a061107020a120302011d 66
    0x1c0c1c450300c00d4030820488402c8040b01d0b804642d506070303000d00508214003409500801c841e07500b100a42045610500400d00415200702c16100022043c00c60303242c646030280b401900000413229072241260104c815501c031450044480050404c002c041d217660f030503114491034012070007407400c84040e10702806a017041001200941e8080f0f202c1400c0c1a42c9900007074400c000000d00c00c0504007840d039491120007880403128043c0015001001d0140b0242d80d14003030103e8020f5450024421991142d01003001c60248210600b00b22505552080241c2062424211104003203080e42c2d000741e90446004100141c284107034a40000410341000940080051050821000441c0341c8501210401440f40c0400000c0400c610741045402141d4003400d0b0500c0c90400c20150f60352008540c4089403130354181b40d0003840b441c0317a040980d10307099001016100500c1c82c200d28075101408500f01581195268114618403200d03c80c0040c02030714111005000401079100ca0040c40c2a100f0032200181c824005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670543597 1250 670542347 670542349
    0x6030118050c0d110a080d0e060f031501030b0607050601030c0f06020d1b060c170606090f010809010207060501030c03030f021b090603071e050f03070e010e04110d0b01080d03050105 80
    0x1c092142c00c400341e902da02c1c040994101030500d900e116001d04e81c8404c0801020841880228007041e001c02c9607250445100040c0c81048264000d150000800210030b10008455008002940034940418140000d04543c9440812031a90001805540980c4403100410411000c4240040188003040b6242d850740e0038190029122243d03000c808003000340ba48448180900c18a4020410325132122003000342c144c200310050300b0142c4442009802205660001d42d080c2030a6084070420003000b80107000130140342c1d0040d11408400390120003259428420000024081c1c0b141a002e14050341102c8141441c2d40f500816140e10f5015550031500248000f59908922005000211004683e6109665141c00201c0c0c0343c0300565202100b042c003251020144d1120700d40034031040d1042522215240c2c20341c0410305644120390711940c101c0288aa00400824030206800c50f081840f4000c1a1070100c040c0740000c0d1421881035080da1160a04c00041100a50400905210a91030705040c0300541c5010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670544847 1250 670543597 670543603
    0xb12010f06031104142a03010e150307060519140d0510090b03030406030c020c130c0f09050603131703040c0608070305040507051210020d09050f160b09040e150603011805 75
    0x282842c1c0c0c81810340c5042041910f1202c2108542a43c54400907487e9a5100842c40490701d050700e04056001e0070350095600c5042c08034080c02941c035240c444506e07115901e44400e06a5050314030380001c20a03038a4000c0301d482c1000d8010500c4840324040030803d401c101e859141400c81c2584580c00107850300c144080b1503280841620308491081c240010005291035003a800c242e500303020168480d00b0f900e00e80148070384a50100c2d014201c50740c2c03510a0342560301c40036110303d4442c0c0039181d40000c040c000940c001101c014403441c100c0c403e840c10811546840310007800c13504140c1e003c44056030780e00814400c440c0d208580640c8051185000c2c40b85040546403203403684140d02805000e50540301210300c80940400c03009080b030000400856450241040351001490010301c06c80c1d103406030180490b101000011400b03ca0102000e0000c1c503540f03482100700c0c1a6020854035500035844141c0c15004003c02d119000c0004c0b202c2180d8182c0d4a444400c050131034480e2400c020307842d0030301c6402d400410307000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670546097 1250 670544847 670544851
    0x150e100801063b130204020d0f050a0606050f0409180f05100f0216030c06110c06100902040e01090b041d0c0a300c0302090c0a080901110d0b12010f0603110414 70
    0x861310302100490300b400400d02904c10b564411306110f080950050324003000c0c0c0e100758410750f1034070020018a0749446003100d03544507400600601003024442804295020341c8104030380000e12440107010205d039610a860000c01c48001e0756140c105100b004a0b0303d44c140034110030030031a003004610f003038403d558a00c034900d0030301005030070041c600000c6800c0008562240007a413080074a0603480e5a0101d441c1907031004d080740d607038140031146c000c000b90340d8280c1d0081c0e0f07090318140c5000410076807e048944000b4400300c0001d69125032110a03920240040c0b80c221036014200300054490504410180510014540e00c14405410b800885105d5084800100e40082d00e4819a00c1701b0b46505041040400071180c0000e50b01c00075080601c1003240c1d082c4000c1000104586500c02581e4800f070505089070384c5030101000b25801044404000c103110ba0000341d070048010030b108600c03003d404d8010f0031a1101d01d501d0f0361850340c0341801e009000404c0d48130100c1c21001c0342d0600c22400303020f40380400d01d000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670547347 1250 670546097 670546111
    0x906060406030f0b04020f04230901032d0606050108240d15020a051c0608120306032a120105090d080c040306020d020a090603150e100801063b 63
    0x526005000241072035048040d003240014015911b48081041402c10748e40300744280e403d20806d0114940c40303c01d1201c1100340510005050740703020381c650340f070702c1a00e4005500d2809180c80004103107503261035508500f66585010740400103d0324240f200142c0300000260948500c55492009401e051000f00115840020145c0d161001407805103014104181130500c1c8240090000c541c1444959204001d40302c480070012503450343c5c26001020204543c01c5000f0310b40c41da000703045c00880708400c8078020f50b008800941100d00c00925003002c10140ca0403401500031254080b07000c804240741115202400c0720f5610020001070400d41e40469076140301c2c11340401400109070002c1c103035090480c203503401160403203411f5654401c2480310200943c0041c510b080801c0761450049001740c80380c407900d2003042d080320085001071708040c412907131400010414001d40403c81004a0b10100c280a1600100f10140b5800c1c00c05110443ea810040d600ccd410b4032124009400c450704401c03001604260700041c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670548597 1250 670547347 670547351
    0xc1506030a230f0a0f030f090b04050f01140c1f0e031206010219060501050a09090b150406080d091502120f092d040b09091002090a0806180705090606040603 69
    0x40072107034190a00325126503403c1540206004807044c4080c0c0b584417141c3c0f81c800c2d950502500e090b981b041e180741495005054010200740028000703401c101000d50040541410b08080055144085d074141c1c0d8090700b0f40076181c0c3c02c01d1103034200b550a007090072144e581140f9030610424880b02400c0781c0e80e0040001ca440281003490104185d0f074020b108211300d681044050b150b44544506100340900028450f0502900c2d1002d40015114080d210f50324a240c0c1c000e20300501500c07819160142401002c4505901540d1400c00003040c0000300164021041640c403004070141c54070b03800401e00004900c041040d074105c080a06003084140341210403034808440055101d42628002c1000150765000c01c0aa00407200fa020100789074201c140140400203c074244031600c0c00c60148044100706440c0110f540d40704003540c440110242c0c01420380c80d000030382044802a500c1c44501c0c80c00d1429240b01e40800c903020000e40d03506c081408944050b040941c1e10f0074190801c00c011032080c0c49980f03c1c031f0301015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670549847 1250 670548597 670548653
    0x5010b0f011d060409050709060206070201090c06030207020a0509100503010b0402070c180f0c080a1515110f061e010905070c061a0907050a020c01020109150509030f0c1506030a 78
    0x3d5111019500944542d0404205600d00030b01c015200590300d0041ca00176114803c001402c661050080c01030042e8007855136483e2a2500c1d00c103401a4000d030004a9200d515600040f0b41d40d2160b402c618400c1006c5071000951500d01020b140c21583c440b80f910740510300402181000c05d400c1c10002c0f04a80142c100c1041010501d02908010036482c01c0e02c0c03032098248040c4a0041d50311148a5004403001c3d807041005940200c1c1c208139403010303031003500c1642030390180c0340442a02901400c2116620101030381d21000c9131031007181c10540c00310390ba0b4a26100102840484a4100c03000c01d0150203507441c10401c0e4140000082c1c14106503100060040d0340b680c611840d000b5402d803070428035000c05001081d09007842d50010b030007508401e02100062013000c3e070081241d071050040100d000d4210021100f507401d801501030227410010202d24440c0300c200b0800030080090401085080742c0d0300046d118032010030814110440005d80218402d91003403140c90003003008407121120302185514445148 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670551097 1250 670549847 670549849
    0x9060609060702180406060f090507120c12050c03010e09071406091c12110d0c120918090215040608180c15040806090109050316020f130905010b0f011d 67
    0x100804c41429014140030b00180004c014107504220203940f0144e454403092503c2d1801c01088440c215030140028070364017050000e1400942c0800307413410b558640980e1007207080c82d44000780d50058484020b5410b0002c010001c0ca21611882904180c0d50000b40000f145400c100a040183c2d107000e507446010300182d64040baa5680740c1000710329183c4111941c0226244c206501074106124180000c00c11020280c0302e40c08000c51302e40302e00c510b551030303200400881c1c1c0c9940d40c0107861580c64a003444000703080030460036419071030402001d44020b404107240d40b039881030041e5030086846070111100284002d01c1096001603466900180300070000400b03c400ca001585801d44113240e403500009035040b8440040d28610080080c1d481c08030440d03245846511102c1c1c00c81c0c83c01d40020f00190410f01101d4003544814441e6070000b400244048d8902c0c09000c0020190b14410300286850b030f94030703040d00c0c1c04c0100138004c0c4002e01c00b084412441d001000350001c0c1c903441c20f840d6182c124419230070981c281d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670552347 1250 670551097 670551109
    0x60b12071409100806040b010e011d0415180609050c070f050709110c06010509010b0405010807120c0309020909120f070503160503070c0e070507060209010203160605070e09060609060702 82
    0x3202d00b0003404020114070b068400f8018000070f468103805030f1304000b0300590715405140013001c1c20006965a6035101c00b42078946851072240a082503100e5184c10128112904150721900a450500b00070040a510381e40b01d60b080710056800a46100d040c00b003000344410b118001d0302d04551300300c1c2d030001405801d894440d0604205030081d0450f5403400200704074903000003002d4201d40402c50308550559032103800b0030640f420240310318071a4800400041c00194450424907400010343d06080c20700d000301078000c106544a0340c51140009907280744400135494400c090540000802c07000e480c03540301a200b400027510403004c5401000030009100020130030704004440000880c1812500c11141510b81180c0b241c0c4008401c3d100304103003403000306020781d281d1034041c00788030152219840c00d14290342d03a07000703034000410b803905501003407040020403104485210000e07881400009464500341002a0403089540c040728014101813042110548038101118022074040740c86075210b040910000310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670553597 1250 670552347 670552357
    0x6070c020f09090105100b040807060f110706050702012601050f0a0503010609140f010e060405040215070c0602160323011e021201060c050309150c0f0c0301060b120714 74
    0x7030461214401c03c0071955040d44aa4001e55042400344d400c80d56410884146001d1400350011940001c40c08210a50082201c80842255030501c82d1204108040751030400250746d001402085000032580210341c1d00109a032701d280842e04a541d4207101d950040418544140100c41c0580d11800d81c00c08107070743d107070b10440007480010000d12080381c80f9031b01d10006e881e107011452404982c401c085840240ea01844034141d800300492030459546080801010f00070190090341c211103101e00050a125000c1c2c0180703241d034001c10304644102e240180080c98039030342175000c85208048420500014408100030501d200200309007811111950405e030740108020100340200f07100c1d4009410058403541c01030503c8a5502688401aaa9030601642d107182c100310010a01d0b0420041082c0c94078148010b0315501480e13140ca641440b01c1140e0662402d900e070342c80180b00da07101416500d098039090040710081c0609860f00b034240a000c90401035643d90242c00030301071184800c43d0385d10010500d41a10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670554847 1250 670553597 670553599
    0x6030510020a080f1f1415030c0d0f02040b0403321906020904061205010608150112030e03100207050115061e0210020a08060405070c1203091a2502010e06070c020f 72
    0x803400e80c0d41d07078114030b110401c0340807007d00401c91002c1290710b103007045082d6441003403203581c43c03131400141c98074030401000e680e03003807244040c1d003072001041903020a0302500295220300c040c0340c0100301c00000c105109480042d0b1000c86480e1661101d0030707140124410007540400b03103080d4406049841d000000e0301846200036041890920009900307151a41200001c5000380002c00c80691a070b011551249028004195500b54940041040803a100006040540246802c03002d00c00c65000081c02e0613020041124070b190041a0364040c0f00083c4200013400f0008550184034501e005130140065540c04003000080201004031000b40e0f00070312814000e0924070074219660240340d60060032050085d11002e028615000009003100d025050f05008150012440c102c0341c0700c112401c6015140c0c003202150442400c1070b045600e864584002400345400c2c618400c6a12602e800c440c4483c0c03000c0030740b2002c40e07040007051918141c001c5819030700a2858900000c16503602c0c00800c2c03071396103003146031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670556097 1250 670554847 670554901
    0xc0614150d060609240e07050405150c0a1419020d11030a050609060f15030a0204020a050d1803111603110109120605060f0f130203070e09070306030510020a080f 71
    0x9040081d0f1100d514001c00003000c040311054030b071900c4c54581b0032402129072401040c02048140641c3c03a010340b0164515420400705844c080b81d1651340e50034182c010b072082720040400307100a4449103007403201441d41d1000001c02c502000300307a00010581580c10030017405070107030f0900d01c941e00d03202801001d51940d00001143c00c2820045030b0389941b00030480f2012641081c0401203014218000d401c1500035200030014010440a5020400207612080c4d400d414400b0401c00c46050350b0700340c0a080d0310821050303c005621541400e026205000301c520400303603034001401f102101125200100e003038a41100c00760b15200401c50041e205c48015400100207000411a0803080011640109208070030544421482011140c01d000598211070280d641c49285e906080100c3c12859014592100c071707610f07003041c0441154010a0300030005959540c00030b900d0350030030300500200704448489044003420852501d2942100244825000b400e4000034402503404110400c0d1241c01403031440c1800420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670557347 1250 670556097 670556111
    0xa060809061005010e12011b09081c120e07030b041110020f0d030b15040b0310060c080a0c050a020907180b03010b0307210c0c0614150d060609 63
    0x10140294108844104080c0714150000301880600c5100104a03201a19910b002002c0e10041021064809451040310340da2481c4405012200004184c841a12500c580ca00700707003407803500d600b070030001e001c44001c41e154441a000040c0e8400c0400943c2114004006003403001c1d004a2410010a580050212012507060205020500c10b4440b00614111031646441e0b000460a070380701e01c9051500c030981c2e0007981c000003609002c0c2e0803801c4141801400f40c40c40011038082c10304141c0294000342c84154002c020860710905603050103010384114100001103680c0c985c0c407040c7e507103d1400803c0401c04a07000d840204030302000f074111401c1d401800ea403407074a003410000b01101140640701c1c0c0c01c0c84440a00040c010a40c83c1200d060b282c1a250240c038642d40d540040d03845110b8041070400000b00c1c0015584951315605c908801c81c1c11176500d201c00020300d410427109694840c028414000501424050115401000340e89030b14001e4541b01c0f07500c44035040040041a42d0742c4506041070070070305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670558597 1250 670557347 670557359
    0x60f09060606070f061e15050319060605100314092a010c3804020607060e03040e0406020a031a101407080f070501230708060607080c0c010306080a030e1903020a 71
    0xc6c0d09030b0810250901080403c80c1300e040707461007825500c0381075007681220b506403483e241c0c00005000d406008031004a801c503075400104040d92818402c980003c0d5692501e070084152035940d068000201f2001401d1034141642c18a00b040615401d0884c07402c1c1e40180c45801d039009080040c01d031070700140042030300e4070442010280711200c206420b219038100208400660104005540555005081e03242080a01c0c0c1c0e80400034402000b8031400c40c4401d2200240a03d40128910700c600d1003520056140c2580c010b014040d40c1c410100c52941420303038081100c40d07440c3c1d840026100b0788a480c10110120403001a585284130307141019000c94070018425140000650040580c10300c00d400070440b20740207100102001002d0092034201d4000440818000c44c42441c4c00c607000000104a40d02c0e1400e0b0380d5030120b2170381c8080404c0016800c00d40300d0328206d40e01881400000c040401c00341505000507a002001849030f1501d4a108045039485c4150120170ba0026001669003d0011414140c41c0c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670559847 1250 670558597 670558631
    0xd110318010b04091709040209030f0c011709030a23040602031e0301030209040f062912030c2515090f050a0f0909060e0d11060f09060606070f06 64
    0x4a0304505540c01c1c60500b0645041c144200740c1c845800240d81c102d95001d1004007031484d4815050b4a40c0250244143c000350b81e0144420300113000c00c032000302513000350007001405c07881e13000108160f035541e00c404204140d14048100c4402a5035850040b007000315010000f070300c16030741445154070f5802c003050209420790008000c04a80903c0b065428a440d15188401001d2109000003500900a680401c000170a01c0c400380700340c203118640101e4140c2549100c5004560030000400c0c489007041e000381c09078102091055128411500914985451042d46070b07500d84800c20500301080e40c4400040350035806800401c090301c500219070119038a0302c0700c02410024207019402c1a5051007400003898a882134a01c0201c5600841d80e208032031625418900400680f141550b2068842c0750010003400b05108a9061045a407203c108010390b03400c00300e2070018018481d0907940c0500040c050041c00c0014401d0b030100088440c95a141c4180c64050081003c6903401480e0710700b41030840554040352 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670561097 1250 670559847 670559881
    0x63102180301020703020c01180519061205040201201906060e130b04080a170a020307020c030109020901051903080412020f0d020108060103021608040b03100e040302060c0d1103 78
    0x5200c2060144038031040608030310615000030050390040348001115400f41e0b12016000c3c20b2049001c1080744d8a00104490313440401c002091104004428003035a900a4980300c1e0001284100700418035081e400a4200500c1c41078488501e940c8003400c580300380041003400c070b40140740c24041d50f10001e81d03e4103030080d0059008a07020007107400d00040c00528401220308035682c224081004036182c545415070b0643c0941c07049000c01c4200380000554196446109009000482005030703a441c040000a0030a1a0b200320148030340d0400c0308120250b43c03a0b4001905443c1b0844445074243e02c08110044200641c4d44020f09244001c0f034002021907000c030200c04e2860094560400341c2c0d406d54108100000c0d0302000034080303035854010565652003640a01840d600b050010a040314041c3c80b40d081c0740d0041d5000b0b03010100c0c0007003048460102100210010000101c1c0750b84c05040640d00a034a40c00005c0c502c44c0c01841c04501080458821b8100045a24a41600750f07031700c0c00c00c445010030003092 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670562347 1250 670561097 670561117
    0x3071d0405010e060408190c20090a02090a090c051303030c02090a050f160e030a0c051302030405030409020c030d0516090602030406020706031d0d050c0123063102 72
    0x604640d180f01c1d1040450706038400d0342c3c0920240d2400800c2c081c20054521621960b41c200990b001c40c010000d810b0014813441448850001d14412040c1b07001c014000c1c02c02490b650b0b0b0300e0300501c10f00d1419294400300c031058560b55240801e120f03424100445c4c071400340303401032429141c1d1000000203260f0041d4117916020300940340d1a100f42d51b1039400b80300742c400c284c0d02c40c20601c81a00c00280d003100d4403821100d12a04034034000078130441880000e80382610b9a101a0780daa40c04110800952914412a42419485203025411031415480d405c1d220b01680c420511540c0d000251340b8182e610510481b0740c8240c10002c1007000303080031000360301e000703070f8044c1c0d102e004c10100380000c102d641c00001503d003150307000e40c01402c030141440b8045016000502c039520b094011814080900c0b1000d000c0c0c000d405c00f00303585507074844c01020a51030a541d100d10540e01c03161a000004c41c12b0001d0072101c154002c1050b03c1280391103100c400c0300d4202c0340e4000d040480841e0604410011031059400810b40455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670563597 1250 670562347 670562351
    0xb0a030b160503160c05070806070f03150605030c0a050d09030c1407080c01120f05090a02010f09030f020d14060c03060a14030304030204110c100c1202030f1503071d040501 76
    0x4203441a02c2ca440141c4180145801940b80490424844c02c2c1e141c0140d4410700c29102855a5221040d26101e4240c5002e00403c8804155074038030766151294050109004007000380e0903203081c5014001c3d200103440810030fa907002a40e902070300c0c0590103c46c1140c080c8003003009201c0e06402e0042c440d42402c141112400000c5000d80c106040002d25141900d81e00e0001e0920700800800540b0341e10104001680015241c0d0703004441c104d668480d152140303020f00003410030309460740b0004001c00600848401800503540050010802002c0030655030ba0b810340350440120704504007400003080c604010001031280000704500c40300e1500203140609002d03030340ca440c1039403141200e81d0161602c4d004150140d006000410241c0b40c26080301e0206200310780d4040c034000d0701d00b4003142010180c141154031144c0304c481450256a0154880c05840224841113045061000c40c0c9003c1c1940500744104141c900ca0401156580a201d40d200901001e0303a140202030704851750340ca603071004603010b032800c2d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670564847 1250 670563597 670563631
    0x504060905061807021f090c1a030a020a170a2c0604110a03170408070906050603070f02010221010302091608040b0403260906160e06030a0b0a030b 65
    0x48038001c1501034400144080c0181020024000d0703040002000c6400f14403031002c0c3c1014905612685c541c094086d048003080f5030301c45040030880e002503a0710410586015880302d98031040c0860980390011030440c409607551688440031101c8004d40c8242001042411050002490381c1b41d021502c4ca10418003000389288005461a0545e0400043c07101d07660044400500040d030b2030032a1046c01100144030110858880d103501a09485000b01d08482c03840c0010180034000d02048444020408544184103840c10702c0301180960001400c0c2c0400e00100080004940e8002e40581d100e00340c01400f80a0302f80034401040c0300c00320003803200780d000d0003100d404944050007502038101d00346111749030388103262242c0d0789440030140b0040c070903002c1041c00c0040729090380c0080b900100280510010310b00303030704046841034146000a41902c0518400001c40910250809012101a44101d030710035280d40e25600300401814180d900c2e20352101440344007104018000d90090300030680d082c1088050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670566097 1250 670564847 670564859
    0x903140d05071d01051c0f020703080a0f021305090a060806151f020706080408071e060b040c02071a090306010605070302060a0908040b030c0c010c0302030105011107050d1e1704050406 81
    0x83d141c0e00e28071400100108841c4d004030720707108000c581005401000040c0c12040c4c80c4c1e500f08a0300f2484084000410400038001040c40034090340303441c03100040e01180b4250f10a010f805c2c18103441d100c0d0a0058507040001407140b44d0030b9109200030510340c1d058072a02d00c2c052454030b80b404a0381441d03e00c201c00c440380b100d4400014540d038198203003498005000040c2805020354003404000d108841101040085500082d0304040c03490040080798005441c0074200c8c58010155103031207096500540c0382044c07071441c140c0c0c0000ea240494030102d4103080c94144107901c2c078600c0d104200b200c0340c052141c13600014880b9401030041c08894003e82c00d44400762225032900c2d013681d561400c00b13800228144801d20080884030000c1d9046036141011303c0c0f03060101d402d11800e40d03a00c030400b8800310b980800100309a50b0800000c02d00a00d03410003400110342440c001807141042c80b14042c003641101d948000341d10400300b00c0800c445030800c1481d21042040c4032407420b00d0b8068050326020700e0520000042d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670567347 1250 670566097 670566137
    0x20307030b010807381306081e06210106090e0c150429070501090b010503010c0e03120a03180c0614040513090510020f03250903060903140d0507 64
    0xc40f18494148050007544c603d00320101742c820b820715403510241000750318520004890408028440760300d40380500e01e020414001084502c000c20071400c00301c4e004000c5035a484211310507504549441d8461030100c2905202e0040c640c6402289800f4500344c4901030603000081c603001c5208040b14220801070249150312400c0c041c51003544490303101c0d6a16000c800c56100503200246112034141801c1c0103a503100c5600f500e80c03120060350b62940d11070040c4800d0800f13000c4d0004d40030b6981028031041d40900042075544da81c0d40c40090f0072140c049210300c01c140c800e401140042d6885901a0398024081c10a28a030700c1c640d21410b40402c840740c0d05240b40c8039255060301e0840d08001c000c0c24410300c8014500d001b400d804039007200e5a000d2040000c07502c0ca214406030024614028840e501c0c2d00d000728802c081d0f1449114100d0303a4a00115005540c5507002820005403035200d440800c001246250030b60f4030000706880c0071a082c202042c02c0c81000181d0317001d18400c044556890001c602c070340101d603a07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670568597 1250 670567347 670567379
    0x518070f03031b0b07050307020708071503050a06051f030e0a03050702010c1a01080a05010f090f02060c01060306021b0d0c02150901090801020c0105010e100806010501030b0607020307030b010807 86
    0x600d035800c8041002c02e00a89095410708107410400c0c00000c40c0e07640c1d8070341300c076402c85000000c04c0c004018041c8040d4104031120180444000801c6410f040c461003600d0011132804000401d900c07040042d210a0550f001200203200c00740c282094164580d450030400841c2c0c280780b00000c1c0c6400100d40302e901c000104815225019103589250a8807600111a400b5440f0b80984840c5102c00c0507120350703045070001900030007481c0d0207030802c51190b1401b203096856941a0118440c1032003404404510100000107149a0440b0060790b0350400e00d030310a014010070f5201800580c40800c052a864006110001200000c28151044525018000d4030003008011010b508050072880c0c0802c49050440149034208e03050410071a000e5640201e1030a9a001c52903440007a510740f80104901c8080f030034140d4000016000a2051604240c0d01d166240b10510850b4105500c0707504042c41915580101c030041b9801800b5240201c1d1641401d0600130003e20a0000307070311840710005461001c081c4888 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670569847 1250 670568597 670568609
    0x111908130803060f0609120d14121f08060c0d0c17180118060c11031c0b0a050d0c03050613050703020904050f06041202010c09140103110c0d0201051807 67
    0x82e00b9600d5903014000042500321441e5003008081003085040e60722010726800541c0c24800411814440100017010400142c0c60340d00f0b02c08090200f4510940c00801c1e15078484400490890740e004108a1520418900c0e800074180b030140c41c06222500d000034005010b8038074605010300c4200c0d1800c90880c3c1410901d9a84a0004107110200300188218404a10841d60000022682d404c101244e240110001d99040394080c1d9203114804100c3c1d0041042b00c0644c5961000e1400c083c001c10f03c200c00c3c1540e8203400f681895440040d000e03980da8618400019043c0900b5022041006141440f030488003400300b40c0f07135032148100240342d8001031004c0e0001c01e54818007a140c1c451841c0d080c041000d4010340b0458546c0211420300e00d6004d020003505100b10702482031090b0345401c05030080d007120b20100d4842e04124000c4420311102005c040c41c1c0c109104280f070000766013000e88009500d11300501d0a04030b8640608a5042c508960541102d800384180c24214404502200e504030798646c801d20900d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670571097 1250 670569847 670569863
    0x6011d01050a0305041110020c040c0806031f060b07050d03060b0301050d02061c0212150306040215030a0b0a090213050d021008071101050103030807020609060f13050111190813 78
    0x282c0d1458800d42055800074440c000d204104419800001c4600c100c03000c4080040c0e0144a07000c24600c1e20380184044003c1500b0001d11a050481c0480c0e02d45150400b60f21100102c0007881e030b02001154014030040c01008070f103c1e16805140380c034a484541140300880085e007064004200c80d00d43c24212412654000c00111802d04658280852604540021001d44005c584510820101800102104280341e00300e600640b034604c41d000310813280940f01c5406540500200801a01c51803051880c08000b0f90340561640d54005c5c281003d4810000050703040241040002000401d41d0017410081e010138810040c00d40e110001c2c010b507003100b840040c0d0f00910394101001101c2c01400542e4001102d4030b803840e80240c8039400603007990320a900031400a06a441040701d0564180300d05504000350702c0c0030780314604006d003030b55070601c03c06012015400241481101000001d42c0f0000e00c0a14492a031511642200070307141480c03000854007000310703486500041020311a420342565643c0c0c00000d0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670572347 1250 670571097 670571107
    0x5071a011815052e080402010215131703010f0504021305090601050417060604050a05101a0903011a040b0a03050d030f020403140601081902011403061f020606011d0105 74
    0xc0d00141c902032048644440d02418045400d44a07200015425401d08000c80d4140f880a03809084c03000155010000300700e0050700303000050780d010401d1040c41814900070b804d1031f01d800804005801130890000c1002c003805404c001d010003c040698100d40e00c10601016a90f600c00911061780708614010810660300f4070107100c0d600e4148a5a0380021041c50300342e040940304c444204181e90604242841940000100045481c1c180141c0364000118002402607050210310396072820300c039004041000c0403020b002c6440807c0d200a546134010b00a0007485044002c0308050320001c50008564051420051200c071b03281000e05050040b02c0d880001031042805084044000342040464950b0f116020040040031941c100d01846241c5500c2000e0001c651404129a2400b07010052200c26035800145100141c0c5e000320301d010302d4a0210310b1041d502d070784d840002158464044071481c80c0302100d0707599107440342e80042c44070b10174031003038a030000140c0050307805082d118034218000b4001502000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670573597 1250 670572347 670572389
    0x20a0312110702060a1701030c09050a0204051f0e1507060b03120406080a0603080d0c09230103020304021305040f0b0901060b0301090e0114071701151b0c030c030305071a01 76
    0x14520145c0614004105051001c408141039200ba40700382c4901d01034220501c00040d851240a402c0740030001d04602d0240740c040031800700c40fa28820924a048080e8041c680e039030103034400c02c0e404a0014000c0850394021001290343d40c00049066074400d0ad0111071075003600380060b40c261032616213041641070074a0450221014a801000210300d586c540e000040080e0305080609481c5160403804181a243c124004000000e01e038003014105002d01c00003000c5e02d1440740f020b20000f40038030340580e0325901c3d800400c0f00962100c029164940c5003c08210038400440000c40605218492513481c907290310780128240c41c0180140c24000d0ba01300010004070307040360b010040098a0000100307001404a50009084400700c40e8000400c0c1010f280615030110042024094000c0e81001615240b1162000742043c5655051003000e0744500c0c001024000018688001989e2101a031030103140c0305c1c5802006600040e4044031618803490858054110004085040e0750394109a905082d103109 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670574847 1250 670573597 670573609
    0xa050303090910030f03081503010507120b04150f1508070e040b0f0409140d03020c1b130906020d0506030303072f01150609120b0c1e0703020a0312110702 68
    0x503148060f000c65003500040019181040c0e00001030081d180c0107218503140841c0303541440201d01c0303544aa403400d420405501d070448480350512049034000200c038424400424010003101c4113020b6603881e410b83c0043c0ca0403801c02c4180507601c0340344a14198181d4004140c038046002d584450106005d04007002c003504080c1d2000b00b1800000b01400920307240200030808498020500380e80c801101320f0200c030461000c2008001c0060300d842e0131413900e00a102c2d05034a5115034440c01001d11a0030014400755134520110703000c0303903511200400050394989051002503001181d180c850307905082c0007840c80d00e070100a9a100d6141c0d03888098240010a035105410f40d20a1001340c28104d00460303203003c0007402d1254801040e85400c0000d1450300f02030018207500c0036a840005014504aa0040052202c2e09425080315504440a480b0042061010104c009809039007100e81800b250400a042c0e000a2140c0500d000f600c414041c00304504010099420b0850b003501e19180c10450000142444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670576097 1250 670574847 670574851
    0x30a03050d1e0c0806102c041d0106091d0c240d0617011e02070201091205031222020105030c130305030c15160c111c060b0a0503030909 60
    0xb05036003440a04140300d4008031080d41007044000340c3d18800700a020f01701000202d1a00049003042c1c07040c2000516000c03201c01e40501c1c0300c44210f0040c044501c040d00c403a0400310209681c4075202c10002c0001d00494003c00e0b0b640b0030081c40c1c07400c0030745003c011240b220390b807403410b8800c102070b0070500021414055080300045400362421725140e451620818a20080c0c03246400a21020840900d0035250b07200c21814841031039400c2e45800310030b004001d42454203805034003d0080142e240c0405000503911601954017400802400c0000c01d810010040003d010304684401d841d5082d84604403e041003441c0c00c64443c40100c000380c0345001540c0150045c5070300203081d004c1c0c146015001040d01c0f00030041a40704491030303800330035601e136005018049038400e10300c0300c0c030421018075100310740412070381700c0303260300024811100400780074008610544031200034050302e500104500318582c141490310520f810f5822a20f040081400b900d40828030b4070480b0030060095042c45002c2003000909040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670577347 1250 670576097 670576121
    0x50a0503040f0c141302160b1003020310061701060e010501030b0402091f111c08040f0506070e0a080105060a0501110304150f030f0e0a1403040e090c040b030a03050d 73
    0x200500460018510b40740743c1015006480030300341202c480b0410302c100c04440d600302e200b09500501000c60322044282400b031a0f40c0d0000d440c85002d803074282600a0204841c0c00294043c005e05064040f881c000d6040300701140c829010380d04007910004240760888a0314000c0d00400504000100038a6209402150700602c00400040c5001ca0140014401081d110b06003100300d03650241912800e504466a5000e40c003c40000d003200b59004440429074a41141c05001482031000115046c01082000c03000c00c01d0340301040310001d0401d0600500074005121100f4890520202e011481202c180103090040030302611100000d42084011b44410071000980300452006000010303503c8007214030404c41e0011174940c1f10031204200343c020240c800182d004858903060075407545070880005040440389402c104003c4c118050740f192141580701c0c1da130164500e500b080e07052110b00c0c00080b42000a51000311003c1040200031011315880b14400280500456020311102c0401c145541003000c42c4c0038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670578597 1250 670577347 670577363
    0x40b0a020d02220504060f0e04060f09080d1506020f06010b03091203150901050d050d0c020102010617060a140c0a050a1403011805100b180d05060103051f0204030201050a050304 78
    0x32400501800b240b450a916500466030f0711000c01c41400c081c481c16015150545e0386111060400108030031402003d0002880b080d03030f0300c51965000341e00e0b902c91080207034000b8000c0e949021121100c0013808031003003d40c2892403030302c10000d00c0c24000100303e8842140c150141500b41e2030400d82c1000740d080242080d40e18000c540c2c0c41c20680a181c40210321800303010f07103a03034603200c0c10105001407402d05800003800381c00f007042c066002c180002550a4244150b152071400e1424074070040b030140909078040c1d041018103420100600c02c1c049400c40c881d10906e00d0800000c00c0702c03000d44521f40d0056034005200402003000003980d612400c01003060640b01e04000d5a2035090024000d000d610903440b8000703280e098140040381007528081c00da0441280d032005400607041c8044815184a01c12030034104c011640100141502e485a032403007002d4104013500d1207036070340b0300300252119407410200e1400f000f0504c2043e591403c91017580d06482e0181d60703041c100014950103860a51014209464940c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670579847 1250 670578597 670578607
    0xc0a03081003081b1c05040b03060d020a1409060d0210080c0c100e1606020c01030b1302040305060612120904020a030e0a05101104140603040c120305071208040b0a020d02 75
    0x30350880c001d1615034950506484c0211821381410700300b08000c10700c880c41c10490204205005e030b01c82c0c295015542544412552038440c07030005030601101d03200003508909558000035500040024a035107000e410b8801c1d07501661014108809203071100c5001798404206c00003e9192842800c0c0356074044284265580341034580e90444d1f24141c00c031076842d00c10756155092154a148180310000841e6074007002d0352001400c00601039111196502c1c900d040668555040d0700d1680c92900d40517145020000844d5142c5e107030b040498072404103c80641c01400d0342236000250b0342d0001019900d034001d0446250070000110100b002a6000202c4001055150305910361005000d02c1060b0699104030700400381030508100341d2003a01c902c1011140304120900c0100079036900c62040d80655101102c02c0d0b0341d2a5110701d41442290100c0c1c2003420b441c0302042130042010382210007003244030302810500602c218803840032a03107041304880080c46140c0c50300c003140e4001d503190081c000480e0010000343c00c007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670581097 1250 670579847 670579853
    0x50f04030606030c0519050603090309090103050c120303070806091306140402040c09060909020a03111201140d050c121e1507030b180601090506030124050c0a03081003 74
    0x5504980c005a401c0d03540e50750200200f0042c0c1201c000144425a00925112840906043e114900d803113040d004a10000000c0d040c2801403046072090540141000f00c25612820501d994000f4a040c0e6405042d0204038015000d200105a900c541c88540d60010250fa80c001403000d142400303051003800d115154000c07000100c1a000e49408945000013003003040c6000c1c0100030940300c011080506000b01c1078000d001560b40140e5a074144d070510900540e039804114001c50050072501c0780982e001e00701141c0491849d40e412440c0f4100c4000d0340301140c0348103940c001c20814182070000101554806102c03030250b4100006a44038004440c82a61074040043e605c2c208100409410040c2e6500700c2c02545080c0c992141f0015040301403132a0030002c0070004008141068007005880c680007e9900010790180c1c410000b100240c640980103503100d580d1848040110400030b2054005409145544a009407040d001d850f81e554100b0024103005c28079880a507240300b0040c000c1240101201004004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670582347 1250 670581097 670581127
    0x4030b01090209040f020a0f080402210a030207150818070e090d080f040302300a0c0618110d02010908250f0503060f090a050d020d0f05130b0a05 64
    0xc100d01c007809030342e8401c1d410070070040f65410500705040502c14002002415400711107240440001c1c02e0284003a1200d000003020705108103602540300c0490485070340708a00c08036546102030303c2a0203c2c0c07016500d40c01144c408902c1e80d180503000600342000074800790803003c401da2240603801c0583d042141ca94444c102c40e80303012950100c0310342c0310054400b08286d000001c2d070383c0040745940c2d022081c00d25a070002c0d16081c01035040090914491403404250fa2515003042ca88000b51450a955003600a0094005190140e003550424a40500001d40c450ba070185860340a13848048200d080c03860f05e04002d91030014030310982c10041d00060205041c0c0d82002603500204a00f5108000b080344000b042c90079685a400042c404d014101040001c9d440000b202c1d50007400306c81242d0b1041e542c4506152504412030700c040c00920400d240420070540224214070f895400b07545018290b40d580303000780d5840c40b6000e8901c104d81661042081540410b1003d0700480c0c4903441c015182c20041c1408080c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670583597 1250 670582347 670582349
    0x8030a032706061a13150519080f0c132c10050a06021b010c021c0b0106090b09011b021507050c011b03052b2f040e130804030b01 57
    0x58440d83c0303190501030003e50001218a007285000014504042074454009410080c812024140041201c07004644e0084003995208140c0c20100040c80c40b00c41e0340142010020f0711044040110100030a5010412404886c0c0072807900700d000c1d1142d8078000e503020f00d40d9100e07840300c025200f102001c406000c01c1e8866590080c0c0d600e0a404400714248400c2000003200d0b035000c082558003000d00e4840b0600c8900700640300d22001d0821140c20140e85c0045513440418403400300031180ca900300b40040004803160b07241614010758072108950384602c0070441c1c62144900032030126011070951a181d2140002e1951440c2c8060525624400301c0c040781116034219440840b2617412030f2500c408156803018070403160401c240411042c018080c0c40c003401610905000c580d0f05440c00081003030350764201c100004680e900c40001c02007d400f4070f0f81e180030403015034052525040e8107010018082c5000c4190740030703698896148206603d0b4040c0b0100d1040041c041101c58047c00d200000120350f21050300b40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670584847 1250 670583597 670583603
    0x1d0904020f040e010c120e240a0f020d0c030b010f02100e010e0a03110c090f04020f01140d02090a331e2109080a0f030e060403020c0a0b030108030a0327 67
    0xa4006c24400c0340120981d00b13000105d15865000f010205082c1c01c08018100406030034929000c0e054075401960f9010f0310404005501c16400011125080c0102c0c0c4d0007004c2810032030354200060a695001161001461100b00e401039111003108079101c1460b510070b18a68040200014001015241d120304003107a6240a82c00310340c0341d50074600e080700103010441121034205c07081c2219182460f03254040d00c07000360019000eaa0035015208071640602e4000e1880e8103840f00b00c80c0c85881001e00c0802070340c0b1003100c19010301c280407000902d00c200068a001d0440c0440c00c802d520758a100618031001905403000c40800c03070303100711080d001441300e8801d0911005650320242c3c401d5070340e10441110110325914210303013454180c0c9500881e051030203036094602140f034100f00700e5504000407000382280e00b220584d240518420304c0101174000400580340001030b00c620a4850352550001d680c1c2c00b09106200b203079001003240c94511886540300c503005034075840c0300c1c0c2c00713440301c6031094401b28484040817 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670586097 1250 670584847 670584857
    0x90f0c1305031c140c060106030e3a050f0906130b0a0201060e01060e010e01030c02030d020415020607110c011b201c0305040e0c07050a0501020a1d0904020f040e010c 73
    0x84603c0c0d0702103180b0550018040c605451310fa46400d1300341d17407444140704000806a9407501e00640b08400c1c41a050400325902c95101100030702041070145007050110510b01d50a103640740c000c81c40c010003c0d5001e5149121780c0c1800e0000030414444958000314403030b6104241c02c540400c045080c400031740400c2c0c00950001401c0e508201c1e55103501030040e001a001d02c404e1003003080781c5a0b407022040a0003c0b0038640030406040c0c403d01030749107004007100010050300100e00402d0710341040d40c0001c0041499400c8407240c0e00c0d908400d0f01c0900c4101a0710407950007a08030840d00754012304640c5503102040d010340f5540403040d15074402e00030703002c43c803c441d07404001002ca07120700d002c413503411010340d0030207000030b040803035035009881c0744241e12480a04034003200024410100c0c0d00c0a0301e240c00c0e04041984c0416003945070650003980091110801710f6141c5c07030106030561341094421060040035003010074640b119000c01c0410380307015060300e034000e8442521a082882c20300500f2048101c8e0340310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670587347 1250 670586097 670586143
    0x5030a0f080114041a0d03120b040c1202030709051012060e090a030305100306020a0504030614061e220b0307050607051f0e070f06030506090f0c130503 67
    0x1001400089008001c00c0105001803218125001d246001140c044600042c4804160013100d440c0240b032034800d070304c6184905804149a0001002c1d50421091042005289920700400003100d070420b844000280d44180001d0315128584c1c001c42d00a01c80c0c0c1080360702e440d81c800015042000101c4a83e0005040300441074540d07519000b1a00601011409590b8516103000000d5588400c0300b070284c10192268080741802c105108400b014582205e01503503110150f140182841e4860b1008a0b0994604600442e03c1008004014040d00000303100008410708240444001d85048000c10382c010705d003a070f400c8a16106000c00e07001c01c050005011450300c040c1401c241c00c141c159444035000e502c007041120000f840c0405c240d0b050b441d2940114814231043e2036244020500340602801c40d100d0480046020054401c4003406c9031501c0d0380601807603032100d05000084000f03403003440210f080000410520661107001c0c11400240d0107a014500d6625000079160036210b4956290303034900902 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670588597 1250 670587347 670587367
    0x4150c0c0303090518090c100e060307020609060a060f0308070204140f1611030a0305041a0403170606160308060114040e011707060249180605040302120312040503 72
    0x7901c9003451603501711194a24044044544495500c0305083c03084118000d10a0894061003a005c0d440c2ca01400c565140d01d451a0007a607140825035204500b4880c410006540840030b004040503107407161a40354015186945000c202e4005420899100e40c40d0b002150003440d42e450880c3c0f240d000705619003e54200b07944038106e50700700354150a007040080c5c80d585021141c0001243e803c0a1a0f01e80002e00f55220300f0402c0458442281e1030a8000034030052106150348000100c0d4a1081603055000b2500c81070304018080c824000c034120f5400d65992002e010a009600c683d82c004010706141101c80d1070591071000c5540142c1101483d10071160060040034007800c440c0003e061908000c004907404d00e600a55505803c118460482c3c442104882041c150041c050206401151034640f054824031101c00054944010390000903046105c40040f86481840540c2220401d4842d81d2606003160240241e01d103512102d201948410422084028a4a26171500c9680a08060f5480f030303c00c18 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670589847 1250 670588597 670588609
    0x4090822030c050618130902031203040c0611061506090d150f0209060d05091507030b122d0109080a090612150501051605010618050a0501080304150c0c03030905 71
    0x180145025440c10f021080f01e000c1103100a00c0c0d04141110340900038040f61b8050f4018154641c6c000350107004010055610311191009140940c0c45460072212042d158402200ca81d503071444484d203d6484913020a90501d002501004120009403586141a8202c0b02180c540e030b900d4a400c6803409051003094200808510404440881d407100c1075140a802d18000b40707503801407941c5101d8165942020401200d020414565440701c200c014030420b2a12400290041c260742d1b520602400301c00749106503806012950364510703013101311b94000039403000c00c0e441390780410024541c62030b41d0307244454400f160544015140d50000c0e130f6030714950b10703003040300c000e15410912148503075031303400c0ca40e07001d010020b41070030f4800741c510a2078019102e1054040c03411410700e01c181d010706a035181c0403010403814580141d481024a282800f032007203440351110380003162400d01c1192020f030001d100901154510640c00700e00f03200c003447c09225000c0b181c1ca0381081e007200e07a03000301c1c04074070808400c20071400c1c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670591097 1250 670589847 670589849
    0x80307150203060d03111f020c010b0d08181201020c03091f0c0b06041805060108010b030303060306041202030c10150509100b0c070806010806041b03030e04090822030c 74
    0x31025411800c200001c0b42c04500b8491004040c000700f4201242551030070410341c0c1d4240c2c048442c1c05c0341200011500c4009600441440da80365007845074120980c00c1002c0c140d20186d900100191401403c035809210758150300b0905070b40414107070300400340d40c0000d002902c281c11568015607070310001d901c02c2001c80a0968503156841e18240041038080d90000066448242c1203400c1c502c082e51002c00150081002d0991004520f24840c659401c2c02000601c5605030b800e01d0700200900c41102c400c142d0b0380d000440f000b031f40c582d00c010001030001d00d070b032a45a01881c141d801120b0900c188000c1280c246180e0301d03061308c503e40d1b80300b2594a900e10ba1207c48001010242c8001505003005040c1c5214500c0c24000c588030f0312000a00081c2c0141c00304042c00040440710241c42441d40c4440600d915510b0980341500e2482c016071082c0c0924000480510840f540754903924480d01c1c0c0c800c20301c005060701207c2a00c074044103110a80c2010300c6903901048038a06c8400c02d060041c1145070200c03030101c803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670592347 1250 670591097 670591133
    0xc080610030b0703050c04031a0105090109090b190b09090a0b130b060910050307090917030c0a12141312020105010b0d090f0602071b0803070803060418020a080307 72
    0x41940304001142d6078900b507641002c1c281c0780c0032400b6610219429503501c01c2d44d2004003002103003c180400143c00c04241d5060350021607225400f07981e5641c190040d14126131000e455880c1c520007141d12900007a0351134104000c07d1a021414001e40c100042c1160b904484030030454215001c50000c204210f41e006600078440c40c0e40c1001c80301c1c80c1e111a40303e500010101c0b070185102c100400c000e6401110207034004c000040480d610b0984541e200406840b400070111031910545805581d060483d50a4030303c00c00004840d81d0420312030880440e04062401f83e140c0c0304a555811503143d40e80000005446984d03141c613400703500d0600d0702d411102d03416440906811a49010018048a139003201200d0314030440c0200400e00e80d00905100307900e03c2a0280003000360380300040c0d000030031004030760384001600480c0c1c07940902551100312a0300c1c1e01c80d102c401002d132601000043e40510b415408032074403284051404a16242d9540850309544294200c0c0265a1003c10a01d08100c4010b4410103003083e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670593597 1250 670592347 670592371
    0x30a08070215060904031403010906091812050d0e0a110906010c0c06112517010506011b083a061503270602040302100201091113020909040c0806 64
    0x114035000c41d41d20010b0b03d124800d95001012406040c0305011101e0089807034004240d40c0d5039560390300d0004050500c542200070b03003800d040e48241070489031050f8400381c10114542c0d2488250000722207941c0003180900c88541d94441d604100030080190b40d808038070968140c80812191000c0003480d00004100b2410400b52000c0d01c4002407000402c1c004903440c030b080960f0502800881c160400405841d00030b42440513100c2c5c61a54080d03940107104440445500360500c1040341481401c5e0f4401b00d448a000c1404494034507040070144541070302541c01038403900c0c10b241e03292040c215502c0000c0c90030901106070a81c0c141229200a1080604c40400c04042010340c1c58a0300489001c4601c800c00d000f415070315600b07412100c80714a60185500c0c01781c0325600341c0560341e14050000303401c07034007003030340074040304544061454014810382100f90b40001014030825110b40410a074218060054146150244420a15a203860348410f014603c201050406542006e140e1403038220001c0003a65519 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670594847 1250 670593597 670593613
    0x1021206010305180a0809040f0203090601032603060d03090306090507051504050d1103070302031207051606050d110c100b120303040f03031a0d0308040c14011b020a17030a080702 79
    0x241c800604105e844c0d40c800a882e4882d2003032000980140281030300c841c811800001040003140c004294181038a100f01c46241c00704122101622000c040b54000d801c03200010404905207241c81481c40b4081842071916406045c0c032a56400300791070034000212003d80c800ca005014914000d081d2560000050303c0c030300c2c285441c0c14002880700d964a071018120b031002c0c044081581c1c40c14000131000c5d6030050201c83d404182d44487e0745da660b0055009403103501421140b043d107258421640021907207e44da607503040c1000441c180c03005040c0d020b0402d10312101007104080540b420300286000f010a03000c0051001800824030540c4038603844c541c0001c3c3c00400c204400620100c0111090700d80601e000243c90200c242e00442da00c80315004107510040d070544003020907910100440c800c3d48118600000680d4072100540140407e0032802d02040b844501d40000d441c20344404406180014000040b00c0d5503980c00c0b032010151041c805800d82c0000071510704441d000710103103030446507600c01000c0c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670596097 1250 670594847 670594891
    0x24140109050f1c02180705041409070c021909050106110115030f0318050604090b01031b2111040f0f060503060a09020a0c060c1206060e0306150d0501021206010305 72
    0x1030030078620441c0c0c10400c0c200c40c0800b076440c0d03440c5410aa4020b4880502d03c0e04006c1000303062904030348180e03001d030000300e03408202e641800703c0840d0240c41c40c0d07101c8660083d481e508028000d502484103a00c0300f0b0f462600043d44011500449008104540f11a03442c0c440b400c18003829921803041d080d00c03c3c45c06210400004460b01c1a076105640c142c6041200080c80c52041c843c4d0603079a81c090340d4001d00202d000f241040e4143a0201c9144c19003620f040180785010000d40319002c1740484110045581990514000071040101881c0303190144000100f9044030506103200c0e410580042000306046003080c0084468101e10704c0150500d4140f280c2145071030300002d503803420240946840742d900840e00360344840c050320400d401151700c07020500c81c20700c800b40001d002e00342d000c142005040c10034030001000e90142c2900014807101070040c19056403002e110130007221081c04c43e90f802041c400c41c83e80104000388041d000d40c40c040c14502900d820444001400e480020700b440c0d104400440d280069 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670597347 1250 670596097 670596109
    0x1302040b0a0c0201110f0303180a110f0102030d0608030403051515131b171803030f060111060103030c060b0a05030a033902030708010e03040924140109050f 69
    0xc5a415140c2402c1102c03251004842c400710040c0c002c21584980b00041d40095000310185204074010048034100043c1c4c0c0c407031107690b0903c022026014a065211420031814206545a071020040c0100ea00d4a03800400c15400c03105103600142494002240500c10080280700c4c071100c1c0e0003030320450115810900707040c11145d09132288091103a400b408c80f601407281c141d000144120b6540d4424400c4114500001e00b414004429901180070840e0010718a00024102c001c0c044900c5001903040d5030395041c803961f41e10000307040c081c11700c6445440c48200010400015003c0c0d03120740d4403241c1102841c80c00c401528201c15440b0712034000c044080c0129100011482e28842d0545020680030050000d403100c0441091059100c1040b01c2d110060246900c140d480d0205100f035046508890f50382000034201c3d40d038600b0380c003e21380080104003d0310070075801c100484020304022100d0700b03001c07010f401411400c0b9844104118008901c0012540e00300c1102d00c010541a40c0c1c4c501155690000030304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670598597 1250 670597347 670597357
    0x607030c08130c240e120a0f1518050c0a0b0a1d1003020417060c0301051002010b091303020c0306071416020a120506011d01060e06120f061302040b 65
    0x1059204008a682840903050300e00f0000d00700c085508115000003031500d07440e02200c4014901180446041800e0740c180411594013280841010f84907a0580da502c07444500107412050365590b2248020040c038048a20520403440c06100f020541041645002402c0c0407000f10b15070310038a07030f804080000000e850111041c519051620400301e0350301030796035803400c502030814035009400d0404044026415034000d101703845e440c0500112f00305901c141d0940d2f40200700c524801d1400c06200400c8541000340075101074080c18000403403402001004038916100449002c24000480c2d00d1400a058044c0643c4040e407000360003030003062034030310341c041d200c0c0c2880411080041c40020b440603904034480740303da4405500400c0004c840d031b0303203509414205644900580e00c40c003881d8000500410b0503114040014003c64407042207a1030f01c8420703558480552541500300c1400c120381130356103a00c00b0b080303485100b00d09078a03016030900d1424004403c801c080c0c0e40c0600d520400040c031811200e202514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670599847 1250 670598597 670598611
    0x60f050f16021209040216052d0a12090e040303060e15030a02010518030a051014071d01030612060c030f0e06040209100b0f1c0204060806100908031b0607030c08 71
    0x19511a0b41e240420020700c01e007c950500a500ba88080080040104d84140100c504052103205032034164403e83c16031010105501741170340080420030008045642100403694141040041144d03151450a0301c401c00302c1d401c88c0000e035603040602c44500500c0c1420740042d2407480c0344080136071000201e5034800758040040e05000c00854400c80c103e007400342d1100311400c0501500d654442c5803900302c0d911940994441201400c29211840b440c880c0b440c4540314000ba5516546c1c503281d00194180801c00e46207041d81010f0300d40b0f801180004810781440d192900c1080c2c0001d20b143d00100050454001c22030002c941c0341071040c0345900900000d1410b4000307070100c0d02d804441d10303121650b04507241550b0040d2540400405d00e0151000d944c4041e00500703060700c0d00003201a0f96482e04000300d00c100d010b803038046071040002c02c0203402d140076003500e09421418400401d640f291402031443e0000c58480000c0d071807503c05180b100c14144200e94100015050074010040c82c52806001c80800408403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670601097 1250 670599847 670599883
    0x1051b0a0806150409090b0f0105030f03220e01030f030807020c0f1c020909071e0b0a03020c070305030c210c03070209150901060305060f10050d0b0607060f050f1602 73
    0x84456152503d0485006108800081020001c6403410f100005000c443d80310440d103081000090500380480c040a101c10031401440c0390240c03401004061901104e41c5030716004070210049003c606030350307500340070714003d101a1801402520780109100c00082080d001c5400c20821000203440c0c0741b8100e000d11600315002c881c0e11000b030740c86070031380090600c01030760144826060005244000c01d0107001da070480001e18160810701c80810760000c1c0e16211311000c02000700054000540700354060994079000c00c055844590b62511180d2540d049401d00030031581080c0c0c01031040d504800700000600100b10801424001d144884640fa8011048041d0143c212040003544d16881c230742c0300c1e40d010000241103440c1540c407481c0060040508407607050085004416108035803500c0c0455241401d040e44ea20341c40c0241c0c888011700900000650b40340c01450501080000800c94014131641d03000e40400003d492030130402c0550780600141128000c240441b04c1a200a64085410800e841510303800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670602347 1250 670601097 670601119
    0x90e010c0801121506240f0804030e030f0616030b0901030f02010c15051312051602040b0f03060406022a0d030b0604270f0e19020301060806070201051b0a0806 70
    0x40341c03201c400e80b0401c0755151a01001103a98011004032180c20340345106c4070004107801c4e0406a824040100c0c180c07010070310707a40c001000a4850103600c01403a201409440c1d070344440021040c5480702c1a9030007a03144221004541003558184115110903030102d983c02019403540d200c2d48210034071064003a04000c0410801c100f07116904040320b08098000300e08106a142811000d506000402d00895104075424a5003000c2449841641d032000091041c90302040d00a03800c03c8010304d030500a21b600b1007183c56884e61990f90a01290348140e00907000036980c0d1b5045050801541c10680c282c110441c1e401c0e04083c2e41620000b15103014800c64240041c002031440c000641e10300941e800411000a11601c5203110b00184030140340c0b2004904044c050508032a0005090791007403400070000c0d52003a401d88074040e0f0740b0f0302e00d0150b6030b001400014010340c0f00c40d030031410304070300301c0d040c401507034507601801142d000c04000d540c10009015000d5050174075081c001011400c0160005101f44140c0b00d07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670603597 1250 670602347 670602353
    0x405130204050a030c0303020c0d200321070b010f062c1e0a050402030915041104020a110706090b45011106040c030f0602190504090e010c080112 64
    0xc11200a040000c0c205501182d0724900810a1405800210014010300c4408405428003004003241036900c07000c02880300706103e13a4005800c40f1070702800e83c1072003250003203d066501161441d003e6400d0071841951513103a42032131200900107a00c00c0c010880d4003c002c0260660002c000224032600030107100030201c691060090180e120340c405035104034050341d00041001107420090f0360b0b6400780c5840b04404e0b075802c208001c80c0400c0300c1d50740f040d40120160759486070204103160340c0301c1e11960750b0240c1c00b01001e0218040760804c10a00010076004001690700041c2084010010400c03450010486800c212045606004105001521503810101c201e00c80d04003460a680c410b0038080c1500e44281404080341c01c41d0003a00d80c40303010441084040000001c0400d10500c01c0340c005954504252451303452001d180400441607480036070a00080c6502000314440005d03000c60b665600380c40f9810041d000c0121002a002e5409681c58401282071641c1c20081c002c0c112104c0b900598030600c6542 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670604847 1250 670603597 670603601
    0xb060a26070503030a030903110a0201020c04110d05011d0f06030d030908091216140901050603060114030c0304030e0301050403140306030703150510050904080f070f02040c110c0411040513 83
    0x1802c0305605000104a80f031000b907140c2d0006100c40c0c041da0303440001500b9450410f4075110442400384c010303040030103000c400d8106900002221000140d0407403420440a890608481080c6c100882083d280e4141c404200341c44c2d50300f20b0f000707031b0f01c02c82c01806428858002551440c42e8940351050548405c0b07205c0030f01581c0400c0c2d40749a134010301a03951500d86505100d4075041104404001507140020110b1058055244203803210000703000c911780c5908200c100002c0e03400041c40c06041020218100b4840003442014600420709865100c1c0c4034201494058450418105001d00aa14060401000c01c0d84881342d1081a284d03950002c0d0307240c5404000c28100500c50f0405055007502968240b201c2d002c550205100754140c003411080309440c3c800b045100101034034007414210301806040e51081c80540240a890311803103120b06c6079403c940c041410381e09200140301c0400d015484c000c41124003489980907603c0101d078200a05054241c005407180034034002c44e8011192000c1c11200740c0c00070313 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670606097 1250 670604847 670604849
    0x212a05070b130b0f091603080f0f1b06010609090516030c0e03070e180a030f050d0f050a09140106050112051e0412030f0218060c0c0603130b060a2607 66
    0x210700d1540280ca011381c4106070602c016555411030307101d0040b080841d0240c4a840b0f00030351b548050194a001c01d14210003030940c000080c1200040010054608880c44005410200b032100c130000d000258075142003d4900413503a4031041c0400d04102c2008001009040080c81c80300c0a42000100c3d26a055012109920b04149850705841081404251000c8064182e803080b000a000341c13290b0043c1682464561000d40d00040c041505081d040070380c90700441c00307450f0308000040001001c2c0e42164031401a29020340f208035885654100c9001446008103006c0082450300000b84070084ca8580024075542c80020750110769179442c00480c0701044030100c84080d0300240581518681800c0c241a40c270603000d201c084012914044251000616070f00075500e491500000307840c840c800080601c05907600c01c0c803081441c4e004608101c8450341e202c00c051409410102120111441c07a032070301d01984500035092900c11145801c003040349802d40100215030100500300784800c01080003000c0d14041d16 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670607347 1250 670606097 670606103
    0x807020a02090a0e010e0a0305070f050a240e010c0207140d06020c030408190c0302062101180b01030203090a111201020c060a0c030b0306010b0a212a05070b13 70
    0x50341c002d004043c056600984d00100000b0001c014802c202080199a0703008100000d01240d0300b846410302090034950546070b418001c00c2524500340036541c40c0070280d6a0349000016940401e1400e10701d4002a2054880004440d8000c004485207014065a664002d1040c008903041403036690f891a03c0c0c0d00102581140e07c1401952203d600c440700b20384a03001806145924490130002c100904c2d41c203ca203030580ca4020703e07105011819034080c480381e54484035842d400118600d82001c14901e0a0110324000c0040061414080905007541c1054030804d50300c1034101801481448100680443c070900001d40c004c001d100d01904003004210b01d405150761448480d4070220700c40308172110203d001c0c3c5c803400090204203d817031145082a4201c032446001190580c1c0400c00502006032802c0c01001c0207040d13800c1081c400495400080c14284030280a40d14060712181c01c18210058851411038001445450706070150342600010580d02403003c014005a400354007080d80d0114a040508801e90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670608597 1250 670607347 670607359
    0x705070305030904051f0e07210e070b0c1203060d05070902090406050d11010c1509030c0501060828032309090a02030118020912030403121407030f0807020a02 70
    0x103928100940c80350404240c0034020703424000051819050b003c244400c01da041311501601c00e0515100002e5080010180b000b8010b0764200c1c400d803402c1401600000e01c0b92800c01003002840a46018200401544881d0540c00c0034008006100c20110300524070b51440705010b0344a90b00c182c001610501d20520162084c01226004961514550020114520700707413800d210071070380c6e10107000400610300c402502c9210308030f0850074551710405440c1c0403180200466101c022a1081c66011102d030800c080300030030301d81c29084017040820301454000b00202e602510355410548070991401d0410b001e1941d00b00003814040040500401801c9904101084200301d95682220144082e1380501d03038441c03054641100044800816008680c141c880300c1502c6100328240c0010704010350041b40e05540d0081c00c102000c3c08241041016000450050f528414960b140502c042d041074101c0d185500724400030401100481c0e080b092610050301e42e80f6015009640e641400c83c00d04007050302c000e41c091 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670609847 1250 670608597 670608599
    0x181119030302162705040c031502210114060705071d0121030509061305130b0a0806151002010e0d021b0405040c17070b03092103041511070507 63
    0x140d03002442070107002090301070a1031030b6107904601450510118a40c40280541400c0c01e00380001908406d030801e115007580303800c1503207a558612504c0801c0000041559001c5401508080c0700514003a0b80300185070088080d50401006040c800e02c1c14400314094800090f00c4000c005040100000600c15600b0000c00f0003005009600c2184080c815011889500180b5071440702081110800e02c9516468280c5003440210030303c22036401c45c0e840101c031000b540c0c4000485403104d41d400c0c038001864190015511848004000c0a09400e0701306814030741c00b480400140310080c00d08114682c00c1210075503800c1108180485c054890f65001c9401070040880c03d281254000944001840412021000580000301032200702c2c0d9003120041d1407090b80340c40820143c11000d0304100b030300155205680c0140d44660303c10505620a03a0705a00e5548040e40081c404500e0f5001c0314030510000c2035440c61410652109120540c1400200c1c0a203541d035030400c0141614182182d0f152507001c01500d40311 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670611097 1250 670609847 670609853
    0x140a061401050a0b1206040b0102070e0903070204110a02070504020f1b07180c121d030a0e10030b01080a0506030f0a080d050601090b040b16080315040e0118111903 72
    0x16402c1c81424000d002c0e40c1004640c180054095809810404000d4426a65400f040101600d02c42d1602070540c010a04040b0700c039070075211a10b22900100d0002c5585002500c14401107800c9045104c1e458581802198201640462120119a001c64026031940d0000703500764490302c00d100c41c0c00d100580058042c080d010010980a04031030100783d1441c1d1003040c804004042d56851031400000912201d000d11410300181d020110341880200070200481c0418441891640b2281e002d03c04920513250ba280245811504046600c40c0d0b490203000607c140d000182c8141400303402c241c071242e115400220036403001c2050000348441c8608035451004181004003a9a10405180c50070509100008801c0e500881d030440444900901142c0340c030386800240c0603103070800c102d61468030045001810100d202e08002d54012000031103d1740d880440c1a08200c200c803803811704040c981e41489484400301802852062000c1d400c100c002c040c9034040700000359000b8500c1011180e09018000c04414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670612347 1250 670611097 670611131
    0x2250b070f030201050a0b0a05120307080406051306020c09150d2003300307050903030301031a070e012c030102030f07080709050a030311010b370b07140a06 69
    0x707000d0107078008011a4070380384c0c012800d48001ca1020764002001c0c01c01000607041421030749040c1c50301d03581030340e04001c403d43d02d4403800d030300c00c0c2d100074009040803854450702c02445105e00700a0445000030002d110440307021030700202e401086962140c1c0d8005103900c1c1c81e00c4616541d01c000e640600e81600e071004c048030101c0220042614580688101c01d9200030144241655984c00c04003601d011501d016102d40c1c3e04216400180300104105060107981c03116201000514040c5102e0540b200070303520400411000a10010150410007444085040459801110302020080c0e220b08400300c03082c0c240c02e141400456403c00b07a8043d031000041010303040080c40118014605a03070303a1181038030b44500440d0104058080ca07070348904011010030009000e52200000d0000c0c44002148034040c13000003800162001041442c0e001c0400e05184284204d140794501003181c9204100ca00750a100820906020303026006040c2e0011b88004651020304000598001d540f02e001031040c842c0c3c00c100000c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670613597 1250 670612347 670612373
    0x120f02040903090f12081206131803030f0218060f07052a01020304271407091a1602130207021302090108070e010815010e100302031609050102250b07 66
    0x21130024445000c10520b04070a0b640da61a50000916410300c80d0307400360503e800e40042d08a0354400754000000c149a100342c014001c04200e009840c0240c0740d9a428007405544001e01078124141c8104040d00c182c160340382245604000680740f446d140d154541e0b125009118400014015101c0c1e1340301c0d0240040c0c2300d5140e07959030804511800c904007900c401a40d690140303003d2004004640b804804540400d41c81280740a01090404901d024044a8000307115074241c4048000400f100c40501003c011041c00030b1303680c50200c3d81035207891600300c62542c0c80148264020311480d00b80c14400c00e10900340d0155502c1540081100034804500c0c04024000d5012000150100d5001c1001a1034035010700c480242114040c0c4400d1000e0323503000e601030203078018640a075050040101c4290b60135255484040c424070030544006a036402c0251000c1c2c000000c0800d180100403440703a041c00140d07404540c5104403010345900c0740303108100c01c1c0c2110000000743c200e1a4004404118202402043c11000d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670614847 1250 670613597 670613609
    0x1b121203010f05060a0503070509040216050a110102060c0d020f04080d2303270114100807080d090605371704020603070e0105130e09060f10120f0204090309 69
    0x20b03020380d03514103111441c045d40f41000c0c04508180006a4a140101c2c000c0404040060005280800e2400c130101c4840400d0340565040e0f11108001d0104800d140720b40705400c409000400d504d1406000100d20380c07040f540c0400b80f81d41c001c100b540080794000150340140c4118000c0d1140140018001000d0500d4004500468010140d10250078601402280c3c05201094481c00c20300301525102001c450095000c48501d6503245088480d0300d000700c2c403150284a9184800b0f103503924001c005850050705030001d40e81504901154244260014a0507048074858180940c486400740000000030183c1c5024903200e01044240740301c816204144828940503607104e40c50340500c0c45c0d05403800000101c44c029040030041011440c203500507100d051075048140350661404101400c0010844c10640c450141800c4410a12030041d81c1405081d90003914030721400b0031b80c5000400c245031003400f4030031098401181036002d001e00109000e060210347c1c0192007885182b40390325008102c2d004500c100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670616097 1250 670614847 670614869
    0xa0f08030c0601231e09070504080d0504080d180f030521030709060e04110705060402030105090303041101030903142802030f04140a0816060f09081b12120301 70
    0x11a00d18100d5000c800385403804402d0f41d55021325981031000000c00b07101403c015414403209801d055454010041c803510840d52219110341c5051961482c1c0a008055081802400e20090040040005031101d0802d0540f404c41d842d000d844140c080c010900b508403204914200d80c0200912800040103d0400d24180c41012090b0901000e0000c03030109480304000641044000c000d214800c2d20300d1110724800510008400c2c42c0c044403a5201d500041c3c0c103c48a4008000f00000e6140078860154000c1c00b0601452841c5401c1d03030b031024540b084507075407414136985208a005140c8a0040494900c1d10100129135070a030324140c04d146103a103d13104000c202030b405403000e101c0c1c5c8084240d8480e80c1070b070910b041c04d080c01d00d0202d002c00a0301027440c07904a01035901c00103a042040100d640700d0014420345018003806c0c0400104000c840c03040c5042407098454003005240c03030024041020f0700d006420082c281d514540042c03015400d083d0080240c0c070880c5401a030414180c40194100c0301e4030008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670617347 1250 670616097 670616099
    0x304081e181002030306040e010b0406090b13110f0715020304051b0f131a03010603120306060e10030f0905030c07060e0a0e060904060e0a0b180f06150a0f08030c0601 73
    0x10040c1c10b2019082c1240103800500200d100c0b41015005002120500c0b00003248100d0000c021404580035035002d07031006500d85440c04040d041c103480c54110f044003002c0c140314404814005802034801d20000740e00304040043c40c0001d018003140d2011011043d10415592414541404c591303800822a0032084860001e03e00c2d4180d10344041400341000c405002d2003140d00031404228020041d2202c50110542105000d20300c5179020312400020310302c41c111307201d070f0390500f404000c044030829006101070242e0603008400541d110300950400701018500840c50382d02e0748008501034555807070700a2032440041489460400041100f0099521581d9089404d54000040142c0100107110b40462035a90001140450610ba4a01680103000e1400810406c0394038042d5841e02d49040c02c00e69444144100b44494071050340b225228001c800e000a05400e008801020344880380901003100ca610482c0845410761101d80c0480d004009007101401d086903920380760ba07141d900c00c4003044d80c1c500400740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670618597 1250 670617347 670617349
    0x8100623131d10140f0d0215031906141c150b10020a2303070b1009050612070506091804060207021f020d0f11010e010b030f0c0607080304081e18 64
    0x54100884801840c2107034480441c00a00c081703040544440382c0c00002014490015031210f1500600400c14440c0d2a0361b07a01e040070060070f00d003034030071601614a81000b008100140d0b601803034484009086a500c0c011500c052490314103001020760090500c1e0b0b266600c2184101554000c070240403050322981d20b8a8408003040b84c56260f90360740146001d50110100500901d41394001d948104414226403408400d40c8807120b42642c22250110103844450701406800300c5030082c0c9030444000d8500d0607003121540101c07601c6842c1401541d006900200f400145944e84c55020004091a21644640c50034541010701c00b07940b01030000da00441d003078104205200345040092414521035030241020b402c1d60602100d031311841c55059401c0190b41051150850380a100b858001a0140c00000c0d1905949003810300340300d00c0d5070544805800a400c4040306803103450449509540c4880c0b005d581c0e60b141c0c903012085004a10359508841d466000e20351240e14024002e00203080c1840001c807010035000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670619847 1250 670618597 670618621
    0x2030c161a1f1502010e06240f010507030e011b0c03060c050702060706050406020d020c1509070b040e10150f111f05191107020108100623131d 63
    0x702c840000911280c0d8100107038860b08420304032088241c4000b003860122034090928000f0145c803007280400042c06800f84010715070010890249041c1c580302c04d125000c0c00007a1580c0075242d07000d006d10082451802c401d83c0b04940340e84464460700c0d101c0c903aa51403410700600c98260f070b0100707c1d06c06251451628001d40183d003039a40380c82c1e00824082c6040a940d98a4028050141084030781d9502404684003004a41c0040c00c4418050401024812a004180328080da4060280c12650300071900c18029800401c00305c0e020b84500983d035021035110804450001c1c4610340c050071400030400066000301d1b50244600e100c9050640c1c48400840032030501507210b106031101c00b44c0300b0105906021541580341c001c1540504912030f205118689215000b06603405100302c408120300015503001150b0300840000d4211100b070000310509400c240780a0000110804541141c000440704848482e02c00021124504507801110528694400b0a6503103540001006901c1c0c603200400121448848 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670621097 1250 670619847 670619881
    0x60d1b02010213120c170c0a0e0411011403060111030c061510020304060c110d170a03140103020f09131e1e0c1a070b0903070204050f0c0d02030c161a 66
    0x500c0030b680301c0c0c6001d02200448880d220920482d0160b00b561070410b070b88d00e00c41f5000804043e150340d02180f42615000100110030390744241804043d80c80402000c8101c010303607900040a08119090b0b44800d95210b246004d00140009688074140400000400c42d100840d24258140c0d2280e06107002e0307440503a140c0c0218042c030b07800180160f00b8540424403104074004e0741c02000d4641e001030011303500d6916045011105140303507148001581c0071315542c148214208482c2c1051400d46c95410f583c00501c842c218000030324454140b50010806c051900c0c0c407006c002c01d903c4189440c41da10312080f40456049208002e0324004080c2502500300e602400b8201640f80c0e020b42c8090344241010540b2302c4141c0754031402400c01c0b20030302c4860002101500e030540980300728801540c4035200c500c108030686600400710700481e40300c4e109000100c0c024006a64030701d03103030b0b4001584a68850151070450300a0304494200d51050f02e06010900920030800860301140642d01d03141fa903540300740c0401070012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670622347 1250 670621097 670621103
    0x2120301080a030f1e0c0b01120b180f030d05060906060403260f040806100b0f070b190504080306040c111902060f070b090c0d020f060d1b0201021312 66
    0x1c42c051082c0000c0c89607104144428550a20011640101c1d08800c0303c1c0742c24098103004592650750304000d0040c8965128010300304403030140c070a140503a603808000315016014030004006800e001803040c0c3c0902447d1407001d00e440407a81c607810103a071000044c01d000d039030b0240164401c0c030204181d81010300c219019aa0403950054846003104030000c510107010070751000300c20083c8031010410001c400203200800c4d4190003056030b410301d00c0f0031104000c0b107507100040c3d610040200d20140c0c8402416190025009030410509a550081942a410070650442a024680000c01041052490255000700010f41e400c05c42000b91860035500c000000800000c035602001c2210340030200c901c2c04241c620f10181035a0b0a00901414600700c42d04281c030704981d0526000100b1440c004100224450030008540d003a0700310031a500840c031082880400a40600350001e1315504c0b85030b0780c1e0020311640042c5982c1003131596030424028002d41051000d141007031400030b07002540a040d0342c005052550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670623597 1250 670622347 670622353
    0x1060b1c05152b020a090c140a080402010c1b0608011e0e060d021203030901020304030f02010b090c07140a03050918060a0b03090712030c1505040b0103060b0103090213020a0212030108 81
    0x2010125a0a814400c150f000220038128580500140c946680303800040201240110300c01300b0740300d0041c2445401c1c109180b08518180840003015030b001990540041c7c080c00c0001c682d01d41c50405e004810003030f00490103804200400040c4065011898034103d903140080c82ca0840004110441000182d1260307448900c44072011440510b0007561001205200070300002000c01c4c8001250300b10b80046a004015940c04800c200905070400d260080418041c802080704201200014088280c085c128000c2410041808020030004a107206182140503085602c640350f5440e00502543c400b284490050118600440c101d40081621901541c0010704015500d4185170b1000c3d003940004040c130105119007480041d0809124195104490290b954451485c47c01c0c102444981c28254408544501c1c00c010400400c0b1410141419640d0010b00440c8030801d01004901901030741402943c840c01c2c3c1c0c08282a004400d81c01403540403019000c2e540030746420000c000c942e010034030560074250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670624847 1250 670623597 670623619
    0xd0606090608011205070306020309030c190b061f1b05030d1e020708030a050702030909010b0901020618030315011812020306010906080604080717030c0a020c100906080901060b1c0515 81
    0x40c8d880d402641d4403020f1081182d003400320143c03800d81390107203060807a4001180c602c0c0c40020b002d440b22102e948644240c941e1429420115910985840c2440c1ba0303004100449460030b494070480a17100c003d1603000004c0303c5e2070320b005131480002054040240c10760045450440c2c1003004450090b83c0e440e40d00403031158216921085060080c0030010520307421400104000a003540c0c6001c9000d002e42038208045440380c2c8031100180c0781c204081c06080203c1841c6111820814001040360f5011510142401c0312104000042e51101007680030a409041000c03004951404079482041070340f4022011502036907a07454100048840c9030284017495040382002402040140000307011481c07060060440300940d00100c00e036250404d5401080c079030000a1a464803aa0402c440040d220048500131200c000c0054081c03c003a4403842444280110300d030006442144c00c2d03002e0401414102c0e40c056031140e440200403198003201000300b440e945018042540c2c4048410124880c81001d043e51440d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670626097 1250 670624847 670624853
    0x30f1e120504020a051011281209080106080309030c10080609040f08030f0718050919020418060509160e090402061611330309030d06060906080112050703 68
    0x14141c0100260b0b04010501c40000701a103c0070100b200e45205035680c034003131300312007031907181050b00400e109218a42d580d103407504a00080154804a542d0011008105040c40c0b2000e82d0070150175071021206528010300091104000b00042601c404114191107081d6196410000f690030f05900d00c04c0002e448000240e05418110402d942081c080c800d4001949605e40c2c81070700541c03084414400700646282441022600001c0840c110010305040012031800c203400b1689410000b030410b52854407250406044034607560450303010b8500d400c140a090700d03612104101074a00d0380309160160390702da070005801140170000c60714161010790302c84200880c00d6080091061000e0030a0342e2000c070402070780314038501c015401d600d00c41c490280313140c00d0890039080060030200070002440060300151480c91045108102201d0140c07820300f00f5849841d110744035441d5000362200d0150641c909080411103541021107402201c541d5554590f0503a00ea083c0da0b00e55100c5031000814540c0941014000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670627347 1250 670626097 670626101
    0x506070c080f0406120b06280c050712140706120c030f020307080405061305150403021509100b060c0c040f021c060f060e0315060303070b04030f1e12 66
    0xd25001c0c0c0080d03820700c40e200d0760016203684a40d00103000b14100c2070b16450b08189a0040d40d0368a06d04070758090070030702c40386000c0e00d40107004006803403034035990080c20490a0148240003c11074018045806c0e80e0303141c418410704404040c1c82074171401c147c8071125040c03a0300050080142c0e551603890071a814815510b20014200c12003203641415100c00781c5007095482440694401d01c3d491740e4801050410f42007072420594080c000d1200b90107481d00b80d1010031000544090584a0001018800d03621418202d0030903040c101241e03480c601c190305010008400242e507034540603a01804211009809003001424850200418050b07007001c55100e01074581070340302e42546802040c0241c07400c0440c000541c2c0c2501c010540a010558030001801881d0f03c1114241c060007050400900c40404200000d84c0c90040c40301c106403240040c0d0000310251800e00998000d150301c810b001469080c1850f0140c01e01c0c2c50300240034001005912a2a0280e040e03c900c032401007081e440303048024443c0b080c0e00380 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670628597 1250 670627347 670627367
    0x90a0b012109120f03061a07170c03040b030f0f041203020309100e0109061401032d08130e0907060807050d06050d0807020315063006010306050105010f0903050607 72
    0x1481652014803102181003043c164440e241c00d541c07800c0412111010103004c9400703d4210154039031680403540040c0c80d000d01102c030b10340e800c0500d001c0c104820318901901c520070324000510601010500280c4122403002842c003660f000e6600c12100d0b40e03034503c507585d200b41c2260040c0c18600c04100303501c1403502aa00464010404e1800e4075120b9041107044020b4403500ca00c9042c050b0740d1400c020046c0070f4103104d20200c102c5259113003503555140d6200c801c42401e40341d1520b021b401c0008862a41c4150f50220b00120030b83c061005078685840104c0d200d1262038502ca160000e014000000e401001c1c040b9119040c1c4049499071345080d210144121043c0c1c2085c00f141000c1603031464007188964503a1039248503107200e108419070b16151841414102540a100030483c45021410301003240da82c582590004001d04501881c01d69110580900c0e806c400d540000490246d40c00110a0260a0f04024180d402c00e0300c8048001c1c410306811540c0907030a00c005000c6403c003e02150800b03100c0c0320f41e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670629847 1250 670628597 670628657
    0x5121b01150b09180f0610080c0304020f010c120903020a0b2b11030109050106110f0d0c030e120a0506010b070b160507141b040216112b02090a0b01 65
    0x3455180072840344c801c2c0600c05503445042d003038101c3e082204514264040d92055013003407520441074209606c3d200e1440c000a0002441382030900480c1d00580d210340b40300c00f5101d410203d00044010380c1030010740381c000f00d4081607000e050034520110b07402894a00b101d5000d219000445005540450b0003078014001c2d141c10401d50b074880030290f29203010100030314060580f59070002074951402ca005850b03a00c00c442050080d230411690380301032010101e0044c002880c07034140030040502600d82100c010451424155000900b1100c840700180c00088501216200c0c5044461503620fa4820948a0081c0c907401000c2440c0c80000940c15004035001422041c05030800d0382c1411815928009000700c48800304005501070700007020845601d403086079218400b07850031031510131030221407a5074010001000e0103003070056078400801e40780e15161113801c07905003018101c0c8080b01c48070000e25602c0214140e10a2006c40003140d23200d4124450544038640507103803030004c441001401d03030801c02501845 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670631097 1250 670629847 670629859
    0x40506060d0c0503030417241303030b09041104110f09060702030f0a08130506040608180a050d120b3f011419110d021605121b01150b09 60
    0x3072070b6201017024001130200c600300340c2901182c190a00746411492656100140b55103140d84d00004d0703010007030681111a485980d180c210310b81c10243c01400002c141d450f000f800304000c1000340080d40c42c58003c2000c04039010b0181c000642240402da00919003110151002000520317918907020004142851003c1e080c0d07805485403424035410441d90000c00c1d02c0240001a020051094076840540500350403103a890a00d801c10600810002000342400002c4503c088103e1245400304807480405902204640c600003807404c00a0142001c034a04010f110304020b59802580b61403c494200c030b078040f55a14a003c12400703c03484016280444850241d0f001c41601800c44c4800c0c000d16034010b00c0450040c0c241d00305544d40400d206100844041c01e1481e0403400031082e8020421910025150b40000da15580d658610b91024003665000500354030500e0039102c10420180050000c6d825075624909030b40781d50710105802c4e503110b540c00141c1255030000034064031600790080c0c4680755000d884 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670632347 1250 670631097 670631099
    0x3020a1e030204031a04080d0209190605040f0f0503120310030f060515030d0207050108060a23100f0210020d0207080c0c040f0225051c0305040515040506060d0c 71
    0x1000321242200440500000d40010301801072200444d02400545980d1071310002503e445c0e15100d8107809180584100150006034410055541c01e0342051001c0c85125001e1695543d260007074440d611901c10080d00280d40000014150316180340703c0103c0314082c0140640d401104403c0c0b078a6072005040030784540200c0400700204240d01c04007847c403441500009500c1c204076159000e00010305158511075402811088141d41c0c1c081021022104203080c45031403a1150400500f1807000754001c40d24481903e0784003e1041c41c400c040e03121104040d00e103100000704e110400c0ba10380c1d403c82d4a07480981d01c4050b407003040911a600800400a5582006042011300d544265507540a81c3c150140c4d0b40c40f00905030b5551415225580e82c000d14400b08600d0244050002c01045107401034141c17004410001d1001804824803482c1d000000580c541038401c4448680236000b800c0903901900c0d648207500e444038600e10840c9035507000d19000300080c19242e5501d42000000c841d4150b08132800a45404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670633597 1250 670632347 670632377
    0x30c0618150606030c1e040906090605061801140d0f060803211f170705010e0a06200610030b161b02030c040501060302070215030f1924030b2503020a 66
    0x44481c03072903086d0300810741d1740d9450f081d005010b84486400000a0318a0301d0010031140c0c0c0c56500703c0c0d40d0340d010349150540720510580141c5200704c40100f075017226100060030b10350285865110b940300a0f62940d04014054950050f15982d0045040440384180300c02144980b0300405010701ea800b1041814040150340155007440b0310300d1540d8048200c408010001394040c11003840503601030002072800000000000c40000c101202c1403082c00f040c040c00110700e40c2c043c04461404c00b036140ea0790088800c0c5040c5500d0210782500b49120540390b0000e41030203e440400c001000340301d010f0990303949030b011194010321043c0440c0e416a040381d06101f40c00005e000d5803658017486008200c0754800585a02c003a0041c4000c0c00b91940f8502401c0e1002c004004010301c180f0505900500c030940f40150081c2118031420040550099001d840c010440400200ea2100c101c0790040d01d1052020014684079650103803e60900c0500c2c4050030002c1c12600d9500c10302ca64042c1c69204842c1c5000d0348205001c030303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670634847 1250 670633597 670633627
    0xa0e030715050612072c040b04030f0e0603011a07140606030c040b090a0b011103040b04061713030e03070b0c0a1b150c02040e030c0618150606030c 65
    0x40d5046580c110000700410104030244105a40301c40b00b82e8007401d42090620101e03482d80214000c00c00c2d000141450140513040400449980d140c0000c140113a03400d15081074215900201d44c2280010401c0d0424000544a120b1a200208000d440c4604690070500002040b0f03807850950f00410106010b60740c0810001c0e04070329001c40c81c040103081141808801d03d424101d00341c803d103000e2800c0c10071044550300d402d841140d0008000f4070004600c0004801250099001c9181039050701c80801c002c210400304d2001030080342d00544030107608001e062180c04442e50b0403030b590101c140504101602003406071070008044507006013518011a111501d40c08144c000c128034545070b42c4035110400c100201350004805800075281480c050320310f840184400c010345110180d04004040c1c0128046455642003c030700c41200e281900d440303014441841f0364401044400714180b402d010f481010b07610700410040c1c0b0785410100080c200fa500c41e01846816440174003044201da408000c401c1201d9a15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670636097 1250 670634847 670634857
    0xe0c030601050c030a0e0f1c060e0304170f0d111f021c0902090c040810020904060902070302012f0a050313050a0804080601060e0a06030b0a0b030727120201080a0e03 73
    0x680c0b01d00e0a030600c10781c00d1001c010b0800c7c0070f581c02240c10001507011410750b141004c50a65020002045803030500d8040741c00c40c0169407099244440118031000901c001158030301008400d902210b500002c840001c68400f5115038400c40150404040c00001d0100c041c2c21000490143c0000741c689401881e256203484001d200e426103190b59110304c1c03000c6150003025079030090301c00c45840c1d0130b15051046032074842c260f808948589560000e280d5442d034443d80c010030001e00d8151011500c132461418040d010384a049140d22011a402c00190703405440b2800f410040b0f15181c41303060401128038026507169001a2061151143d0380e20104c0015000300b1041d83c01c94480c810580d1103a1900c0106458080e040e0810821300c280320010949a4403000966401c903451450b000c20344041e9840411010441c40d003181e95401000420013400e42d410802c090312211000700d1003683c150300c4003400074410b1103500616840b584071403402c1000d51310808a054101f40080800200d48100c1100c40d8599404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670637347 1250 670636097 670636117
    0xa02060f090a0537050409080901180b04060c060e0307050a02030f010c0c030806062205030c03010b131d1b040b18010e09150a090b100e0c030601050c03 67
    0x800541e080d11401d00061240080c0402d584c854100c000e0007940385048180000d00c02c40c1c5400c1c42c0c1070342c88800240c00c131410061102a0042100c98104e040c624226400480103502003690010345615094504980c0b0701107458802e0b1403810103041c03a104a034581801c01042d00c542ea111003498013250403c2c030040c036100348244020030700e85a540c41407508184000d03810740c0459240400c028120b43c0c1003050280e0050307041c03600340c0440d6518030000e815801060741d5101114012200c0600c0e003094910420141d8a00700c0813580039044000c101401d940750b44421640115030303e64520040700f17041e000750b044107106800d0204034803800a00310b880d22611000c0802c5580003010b490900e402d25101d11142c9601c10f99801c01030004400c085920400c06200308586110000700040184606110f01c10140807201807003d40d40c10212083c002038402c021054641038070000100d14005070490796103003120710f80da6284502d0b556182c01c40300c00e40c00c024112814060108060003104005200030324282c42c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670638597 1250 670637347 670637377
    0x11040e011e0501120b010e0a18050c010809160515120c030403030b0a0819050304080a1407290c0102120a0207060c080702120702180108071d060a05120a0206 69
    0x10707201c40c140c4150780c2d060f480204143c0190390b040010410300340c0c9407070645500d0300700300c20142c60743c40c03142005281c860b03070310b400d200c2c8100e0f0030784204000441c0e00d4024a8090fa610085a1103a90700d0300c0d12006880d03800f54503c0c07401c400c01c210504110940002e400c0042c1406810001300082c440750448045400303a251150000802080540500c10308040580945031154034904069040f90b665a4109800b40d4420440e0407400802038204220380240c80c1031b0060b40c2c1030b00300c13518001441d030710000c842d01224020b40c10b02051040c4a081d50068003030301001300240f10b2201c0c00203101036038003070312185800b035400708440348120721001c20b900d001d2034000e000140e985001d420300004460040101d2801c00c107401d01403161451b8000388410078002c00905141d910921440003d200161000f01032282da80104000988448045255021100c0d00c02c1038003484241d40c0c500e40c406c2d00d800ca44250340a01808828402410201000780442c41e00404030b4078502001d030001074031074100301d2a940d8900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670639847 1250 670638597 670638641
    0xe101b020909030406031104140d020f031e15090705010810240f0f0917100e0102030f1803070b190e0f0d1b0b040c03060e061e1311040e01 61
    0x170f07501d071151220040500d184142000c2c00d208903941c0d800038412000e88203d190100750001c1d591008451201140000d003164115409000c00501e512803003800034901e800340098501c02d920016901c0d40c800e0700c2c2100038107070721800e180065a110320080d150b0202c1c0103000e9030114140e400d104066072031086290320803070b07d04048980101800b50701c00d00f80080001c0c02021740311098110308000140d8031505c11641207001d41c0d0842a103884224548140e0850604002c0202c402065005500031200d143d0a084580c3d1002110b101009044801d662145d000708030400c0498500140b0350f400254804085a8043d24500c00c0c20548606203482d44194024000c05500c0c180304010580c12100d80e4241464115200340c0d039081a03045068000d011041d90b140060b041001001801001e1940b000c1c003007180e03200a80800707a4812044804001d080f01c00d4042d9050786158503206817180381488009030301680d0a0740c5268601c00d0343c00c8032582054451041160081c02070007400041c1c40e81c2c1030451454 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 670641097 1250 670639847 670639859
    0xa090b0a090308180a06090803040b0612030901031104120c0e18100b030c220b040e030d0e070b0a03020c010507030e0712111512070e101b0209090304 66
    0x84100500060310840ca07010120000030b40100a655002011605200b2080c00581c2101c0c2048060705004008615245032a020410710802035406203003e429100410742e10f22042c804600c082009058030365006214449141d0b00c030703400580c02d4083d441021400c0a80d03501e00f1058010031070008071001151203a0510515246030070b2242e10822071078800604207507a66820303484040384102e0001da40e031164a481f50684080020079400c4c44054132120b54032022107844407000f44c003c600c4018860130402c04118619042c005c4940d051030040c06907141076a080c0d141001815040e1007040c42e030050140006000307100703001404610003a40c0b805a55031142515490031140d0040609060515000c00d00100c03040000300c00c1d00740c0f41c644c03603245200c2019003000d00d5001c8031a01300903800042049080b024121100140c540b0190a80c0d5804094540d80c00c15551018101d0708290402222490041c00f0341c0300380b40d030301030402289080c85030062a54004c101510f8045440507507a5100240030004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 670642347 1250 670641097 670641113
    0x80a05030a0f0209010c08031305070e1b030601050a110c040c02010903090e010305030304020d2a14010f0522050405070c03080106020604030203030c0c031c06051314070c080c060a09 80
    0x200b980100462414030f406001a00e6880c5055000c0c01b265008030000b0841d08125000c04041034100c411503800c16907402c131100d54074404851006070941c5041c809811064080b050368010041616220308101c40c55908480042801e4000500c03032040703c20b030300f2040c1c451b482200644803917a8008210f88000e401c0203012031502da8050311402810000400101c2c0d0040152074000d981200e03200d2100ba154144042d07003510154100c0e19224212541d0003601c04a0240e000c211007103028a952641c80d480011350f59008011030900110f14204926018010030340c44c4010328040550451000b642c5410201d4100d60f0101d42403404114181c0b010014181c10003681d500401143c40141303140d00d45a41c0c025204d000140442503094004500006038080510980300c603c1d120804041d0349506c280c2c0d4090184c8007070710030303140140c440002c40102d405090003905d440c1454003ca50407241c803142001c0341c29203060003090f11400340c01e02030184104001d11000740140c28108001c58101014208118 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 670643597 1250 670642347 670642361
    0x3020319030f0b1c020609180f06040f022a0f03040e391602030f1f0b1e030a170306100e0d03030b150a090f09060302010c0b0a09080a05030a 62
    0x101c901844160090070419003c00291303120342c1aa00c082c3c0314903c01c0080382024041c461001443c3c40f0900170480305400c2000c02c5807240d00115070500c8030005c42c0045004901c110f82c0010001d0b140c2924a0f08104d00d21424040752505000032922103010b00c0d00300c3c1c0d0864002e900401d2a003a80c3c042070282d61324414280160300c2460080040103ca04800303030040041b03640f5040007540c80041a580b035a0310502414004042e006404c0e1400003d0b42c9106545582c0141c0703003e661040210f5021607881d41c41d04c40e40399410006040e58040c14104002d0460b00c0c0751038132202d94117200d40d110b580c002420b0f5904210203100c07510301481d1a400c11f05d04002400644481c4801006242d45072030003e65075000c1081c900d143c25003000960003d003180483c281a04102607114081000120240300f91351002080c2c040768a83c01202140035103030700360714065980c24803002c0d0000700401d032418007150308186000c0d042805540c0004900f40e080e07803111038a8000c070011002041d000f004006590365607001e415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 670644847 1250 670643597 670643599
    0x4020f01050901020307060b0607140102070303050f07020c011d1906080615030105040c03060510020c09010b0910050a0e0a0f0602010b010c02210307081206100c110d03020319030f0b 80
    0xa418103030b01c40300003940ca006020001c0c1401d919070740503d2a50721210b0469502ca07170040e0102081e204602580340c040d50000500701d0019150000041a0380c0344480d80c5070080c0a1907000d810720600c040011214030b1100707011500f084109a030710402c59540c61860640c0b0640882400c1641803402c1c6026140c0c481c0248528016102d043c503100003103c060007207a0641e44200c0740003800a11104088000b8829a00129001450035000303420b51038000600308540c0804440c144060b0780c03913071030b140c203140246c61015030840140310f030f2004510701034009844600d00d907140a20f809204580069011000e41d4828951158210001c1c070015a0a00500807840d17802c1c20100b01c0040141d02144459a1503203400c0341d600c94002c0e5080c040b9905000315090250800c0015841da0302d000d100546000040e140d8521442185100300e1140b0b0003a41e42030103090700300160111102d0a00c041c0002000d02c104101c08500042100d0405103104c9101d4100001880c0d03000076001d804000f416085901a44141d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 670646097 1250 670644847 670644857
    0x1b101b0c0e0a110304140f06150a140310022b1b02010c021f0605060c011d0f061315020c01240b030604020a03021603020303190912080907180504020f01 67
    0x3203600f00042030071a50060340c021040f000b4045840104d60520200b000241d040340215030610007050219040428070440841d440d150b810341d24115100c20b505c0d400710041e090b8008240c070270300d160b00a074081c041e0602ca00c9201d400120514151105404800004031070076950b03038000c2a0300c84c0301c41020080b5043e4034002003140b111160800b03562400c0c0340c500c1c102c50158289106500155070707000709d80103200141000ba11011070340e807058081d05000e09400036003961422134083c4514000f41c448803004021010700a40d480d8200030408101051303105603907a014005940400350102d01c0281310114054000144800081c500e500f1180440c0248542c1d075684104207001490a46048035080f2800700c43c01640c030292118207030041d004624405005420f070310701510505070003200031441014908000a84420320407892812141e488074080c19880500000200040c046d00c120341e0020a81400c079904155200002020344021002401507581c90300180021810300c4805555030100034245 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 670647347 1250 670646097 670646111
    0x30a0c1d06010e012709061805060105070309031202031605030a0201110a090b0d181a070512060603060112060602150606030f060d110604030c050108091b101b0c0e0a 73
    0x30500302032400100b146171401110700c032036041072071a000d00030040d80f901400281e81d11902d00c0d5072880c60131804540b007810710340041c13404d41c4140d007254503c41c0e0603183d4500e814116160340c4561009000c0540039403208003e215030100c8440101e4166910803401107580700204072000742036030038070f9000c0d440500084c40300150030398025929000755040341400700d84a2030030007050b00141030a40340410b540c0c442d40c2468414440d482c5a030903050442840b101c03000d42c44a0740125000e104840d0010704800c0d40001003141752404030003c3d500000145085100c040e602012141281d40302c0d88148050303401203100c0105c0d00382003400e156018904851090071490402c00c14407000c1030080c0b006224800041901e010455480c11800054101602d17042c2c0703c548924003014044114001d040c0480c03280e4002070710b910700000b0600f0221b416680d2001000402209210417205104200350a21001540c2020341c80400f2028102090048a29401c11490710294184d1964054104007225083c03540f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 670648597 1250 670647347 670647349
    0x503010e0d200109141c080105060703030c03090c0b0d0f0506030a060b010519050d0e01090f1104020405090901091a01062312090f07090920030a0c1d06010e 69
    0x200200540c148601c0307848092103900c5940340108440e14000740741e0000380c0d0051220050006d117a14444048600c112410b0401c144140c981d004240700340c541c85501007104178000b920903007200900b054141800700b0303e99082d0b0354044030244550444091080c01142c4001804401d0040c204445221b0508000a050076004252030702556403000c1c04858480180d6080350340304004840104e131401891031100c003040d000081c1640c0c440034040f071501e810054803000b110303818460103044540c4482e142041c0c0e040c0e0340d9610140d459146030181d00c03650900001505071226068a4031508040380004ed110640340740980b00117003000e1140503100100d030f00600100f504001e41c98203070008054002500c2c483c542c3c1c81c00326403081810413480702107580180701e2106000200344c1e142113440c40548aa0507160004201159843d18020b0152074144442020403885042000311000014007038030000d902e5526113049450b0700e07602000102245112440151145001e0660801c40929000e10300c030742d0400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 670649847 1250 670648597 670648607
    0xc0f10050301050f01020f0f0601081506011707030605060a0e090106030501030c06031e0204173007020d0b04030804060b040603150c0309120e1207050307121401150503010e0d 77
    0x1000385801410213480790755642e8020040c682c406094941120144101909042c1c0c56085c28403c80c021031180302080c0742c0001540000500c1f0b5401a5140311001980f51194180d03c04003500113010301d0b80c1e9806c0440d640c2c03a00c100405c0c0c000c2c401d44408040030082c50030702038a04e80590000040600e000c0041c0000b8001c20584000c4030305501e004107883d0502a0071141a1101403019241548001800204402c0c0300d19811410041c107004c3e10304401c002007402c0c40455880c010585046101c6c0c0840b0149410b05000c1d04503140050410082e40d40070341c3d02d002d20382c101a18154080307020390041104011460049100c80c403000c2e94140015413850b80d440648230401001c0c51b4965464010b071503801813107548000c1c400d80d0001000030200c0009600078009000210089000b000740c00045180c0744c10014000d011100080d0003000224034090300d2794600c001c104070860b099140c005030391a90017400d00801c00403124400041102d0b51a142c10076084400f15084c0103a16000301205400154000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 670651097 1250 670649847 670649849
    0xa0506190f0f0b0a1e03020421060f0e0c041e0908040503160e06101707050c0f070e161e030c1106040c060305060f03070b090102010507090312050f09120c0f10050301 73
    0x3001e200d00511707411601540a07001e15004804600040075694915808600c555903059000b20000c0002e01082e140c20300c02e55039a602c0c41d95403030340300c0c0d280c410988c00c160f8451171242c003030802c40d0b16a44020074080e00c2900c50b100800c0d1105003000c00c0500031854284400c00e00a10880743d003400f00b51070312042c02c80c10000100300502c6000c0d994600c4d103600e0301624074404d00114a0503c420103140052010740300d9006400074a01d0b07441010745c0ca40d14000d0005c1d00400740c80d0140304150040c1d4918103181110344031105104200088902e080340315076801200910141700f50745000c10348100101004206a10040320000c896010100b48400b040024118100703403102440e0200f4182d4038040031840f0590b00c094025058843c80d28000341c02411640605400c0c1003d900900103911005801c030383c0c01d1040c0c00068000040c0d001a500c40c140524000c01c0302c2c0c450b408800d400c1c403e807200024880307060a0940405500142200c84031458641d44288802c00100d8500d01c25604e0fa2000400c0d80c001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 670652347 1250 670651097 670651127
    0x807030506010e0a06050616031b080708031b0408010b1305010b1e130b0409150f060e0a0314150708091f06120f050c0f01080a0506190f0f0b0a 63
    0x1954013140f0510060340003900644000f130281daa030b400f41c464a00715109406101500000c4401e0030808944c0000003c001c00c01d90010281030415100ea10740540c41c2d0300141800180c946811352401e0301220603406440200140320001402c004003034244005528040c00401c0c1d02440c20005000310b03012201540c415504210044948002000d40c0502d188108030641d040c102c100c4a0004000c0c030040300820036181205010301c00308049040003081a07a440c0100d810082059038140084c074881c9600d01c068102c000c01e030051441e82d0351941a0780b00c104030040c035001e41018101c601600700700070b80c80c1d0300040c207450654858602000d2003502c0303407408141c14512002410040d0380304419034002c440640214902072282030030744d2404240788003d4040481d124019198001280d2400001d1200c0a40041c2c50346041582c5802171381000b040014102c40e4020342040507080303840d1902c1070503006401c00450820220381011454010441ca07580305017003180701040b02c88100c65000d01d000300c0c1014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 670653597 1250 670652347 670652369
    0x91a0f0f01120c09151a0703140d090b041a060f010816110105090f0d051204020409020301020d060b0c0f06090705061c020307020a14061510030b040e0703020406080703050601 77
    0x3843c0c9440e07243c0d20800d83c0f00403003130b50803c00c01c1030190841201c584110781804112140ba03103a0709800d0343e694011034074060702066410143e140480d44c0b1314000d01c1d030007096880015003914541e8506010000590f010b64030720148460141400d0507606110360810f0048910070000d9082d0000240391395002000000c0903800d0501d4084141e00030080c00ca00c21016074020310551400c4001c559032010004944100e40c071034403034404115030107041110140e5550340d900c20060342d00c1d5020f00003e0210510300326010f40d1b0810503000c150816100340d00140140c0c01030a40d40d01c01c411042450b0a804041d0059140c00c01014020800750000d022411900103440311600d481150f401c1e454030101c3d9003c942e004900000810002650102d2600440351064280d001c81c0ca00301c00086030b440100b180c101d180421801c00010051800c280ca09094550360710340030070302c001c01d840440c00391440001c04e20001e5103c05000d20840c0b0b071034005e43e0007400148008250151440e00d030f03995610018812492504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 670654847 1250 670653597 670653629
    0x1709030706030e0f100912050a020c0d0206070503030f04030e0a06020c09060f0a06020c1008070c03120e0706030902130513030e0f0a030f0b010b03010f0306020903030409091a0f0f01 80
    0x142c0f051107600103001075035068403402021001c60401410091000b103622100c951081c0548600440070388a800459500400c044042e800a01140e41400b46040c3c0e4480c000b88154000640c08100039442648480001031507070509107000761408140b415100e220301e2a24406000c5a0341c0011040c20422040358504015107604000c920b45a089e01059a00001030b0480458041c0d00041c001d07440000c140c448101844181400b1502690190750040c0080c0701f006078030300440e126840300c241c05c03014848002508a0001606440c0120f0f6602c00d10110751501001030551800c000c14054400100710103004515000420b01d02c828280007008061000070401d024291f00c1d150030840800b50054520690103880c5d0808000601622008842c4003032064000b2078041245020f8a0499219400f41e08410742180d441502039000100c1442d01480103000c0010421003038041c0c80d440030f0081140d00301a5810706842034500308001e0030a044034418070f05020301c2045c0000041d045507000d4170991910 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 670656097 1250 670654847 670654871
    0x1171b04060902030f091506100f181502150115050c010204030206030421030902150c0c030102130303080705030f0a0e0109020904061a0315040b13060603080403170903070603 77
    0x80074103401c0441e1803031001c03041002145140c9522030150341c0703820445031030b00742c03602045000d040100c0303015401001000841441e0744c00748500d20001e150a09001d1402a203000034a0120607143d13001d40020700702440c402000540501920301d05109203017941000e58102250f10951525886800b0100000050010700060007075041d14041c5a004100c10360340d003032600345124105490040d14040030301c0d034526245c0c894000d2060511040d4060b0100780c00400d0754003000040d80040d100c03c0a14064028407408a0740e0038402400c0b0030012400380300300135045040003008020f0051030001031007401c00501c940110302100040c0c1c406540580481c0004610045502420380124000e401155150500c02000f41513040f210b4549020140414404449410195101500043d1f40c51820f0b2102c0402e01041201900c2a404608050780000a4610313a542604540041e03000313490046c2d0216061082000c5d240011485a807550307407040c01c1000c00304c0025102c0c080740c400c50050641e60000c0c8641 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 670657347 1250 670656097 670656101
    0x91209150507120f09030c03050c0f270a06030c12050d0504231302070606171506090a06030b0907030c05060f091315030b0a0509030a02060412090e091501171b04 71
    0x1b86611583d030b050496500c0c0360803075450540710b1400384510510f070b82c49139490928842006010161126043d511004103903031003400350020b0310716a0345984a0b84080301142074031601d4002072a90750490352011000d030902070304000280c0d203003a0821100b004100129085171000c02d03c1a2403148038034001d40c001e600024041210040503802c0b09001263f42d100303000c05680528203c80c034400b20001c04d0303e01c021049494407004100348000100c000c0c081050b60401401c03080d031001c0704c1d040c00aa103d40720f03125800110000c554074a9540d100240600070007009281c044000e01042c0d13181410b103000b5001c55061809605c0020340246000f501c8450740340b055401c98286118904070302c10805890781440d100c070407070448500f0081c40c1400c02244500030f002089070385030340d01540036007169202c541c0d0300040040300e44c00c600301300f00c60550301241506540c0d00090185503500000c08a03128070b001d02c03252040f0140d103da10410560b0101441c4003201090a20040f407880d680f0180115200c000180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 670658597 1250 670657347 670657349
    0x5040b040326070e030d09050d1704050303070b07020d0e01090302040504050c15040603050c030121031202121e0402030d03020c120c010b09150d020f04091209150507120f09 76
    0x200b08102c5041c0702800341c001004000143d800d406446254080c0101030b503102c415440741ca80c000714400041008118202c0302c040c0201c5c01e1024891519645a001030300d50f410200041d18010742c1c52042c000c0301070701080b10486c01462400e000c10314610140020b850f004013031201a018640710301c009010400d00b0707c4584807510700100710003401982c0002c2860f85400c64000c0c070011074580008145640812030a4a040300e40a440c4602c84041c80e841d052300d5014400e0b0200c060010040071a600031036140060314a281c0c218101242c1480d11b02c020250304402e188264000d1f81d02c41042c0805a10042486541781d202800c000d80d07a90403204505140054601c111003211001040c80c15000d04190443c4ea0701510072a41c104030703074445000b03a00c00d0100c019a800ea001381480c0403080181480c2250400d41c980c020000030f6192515181c1c054004001e45044001562a0b1414000003c0c00700c14507140d5800d82c035146040102e00c0d501c4920040c00b807014032090044030750074180d6003031086d0b0540f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 670659847 1250 670658597 670658657
    0x50702040f0518100e030f07020a0312081603020702030c10020a020901030b150603070e010806010e0405250f08150607051e07060314161119120305040b0403 69
    0x1280c0b4000074146a04060f041a451241c0100c0c941840b09902a018400700c4a4540010714030b0941d82120f00c07442940004400c86e00205400c0000010074600810304200c0c0400d43c0720030060f458405540c034014890082c0000038103105208010250301e0000d814800c00d601038626a503226072405069180101c1098000d40c00902c0304004801c104149034518010103416048100c0650401c0401038580000c0310a840090b080c5000c000c1d00d50720a450403034000c070041c18500c1350311044001007001e45200f11101e40382c001118200131022300741c034000034003009501d10340052010380c8244001c0501c48041c0c02c3c541e508440601e540c0b0385540d4241100d84166000044034036400030001c0401c03041018007205802e40c0660307500001c44074020b002e1244c0500f0b01c54841e21450361107400e480780d07802c4990410702c1000700d01e481d0480c0000c410070035070400c4c001100c08124542507502d41700c04d4910401402004250400051100140c0000c1c2059041076040c101030350301109c0703404511303201e08040c05d000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 670661097 1250 670659847 670659851
    0x13c020408100207050705040501031a07180303110c0a06090b030a022203050c0a060f0f02100608070521120a0203090604030c0302030c040e0c1002030c100b13050115050702040f 78
    0x1a0150070a5a8004c0103414402d0f001d581d001d560721410401118024403010300010003900031f080844608a906580c060150704003614084100b00442209031690f41044010500c00a4441c40a0b44208110b0f031001c0b0048840f21031160500d0300007040b10500384a041d0284e070700440450b40700c4000390103403004102056032a000c04404881c00c0010411a0b200c181d40b45e0041d0f101450f1582000894101a5000350310b45810f543c00c000400c85407006036850840850040d104007454140302d0b40034680040c041134000b0020756003840c00300103417000b103010408040041c4e2003020b075100c2004180b005d50b040c1050318035515041c0d6200164294424800010b9009400103004400c020306800c7d000c0a680c004d4044a00000c0b120040c04101c0d58402124403080e4441d0081070354514100d4204402400d0b5032060f00e00b0124000222444c1c0200c4441110805407101030526a1b810040e0000748083d0310302c0701c107000c10f500d003c421481440e400c10805007006000038a51055440d1a0010b110081303030360b00c0c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 670662347 1250 670661097 670661113
    0x50307300b030307170301050a060314070c02120a030f090501080105100e011b1505060405250e0a09060504051f090c050415021c0c020901120203210705013c020408 72
    0x9a0b00c50307a81b0900070b95100d070349030240129485100341300d18002d079890800e282c40b40762100082a2948060340804030b03403100400000105d120000d001d0304d2109032003912000e54101c0364400180400442c0d0700041d040204800042090396101ea080314000466414610030042036140101c0340c0701caa410f200c20516a88075090410840c00110765290001a2074040006032100f00802042c3ca40581c0c10324a0b009180c81c0c90380e014200d110310700c0c11410240c2010742c52410b03514042022100b0590020320420f58071002040242414000c140d40322042d4070214040c0c02d2011420200c1d14a9802196441555045401425070066003101e01030080e4100c40785009204d40310080d0799042c010714004040240001c11f4001500403c060a01c150f4001d050502c61386c04c240f410020000380700c2c000c0c1c0c0e0505c90b200440e0310f01e20100e0207840c00b00102d104d082d5601c4070242040ba0950f008850382c1c0010390703c05101d403881b450140708107649030308031101c4501c440742c60408154080d00480e00003c8107030107465a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 670663597 1250 670662347 670662383
    0x603040c27060608131b050301090b1509010303120c0309060e011b090f090504050109020d0318060212090f01090302040509032109190f0c06050307300b030307 70
    0x1268140c000405241481030544071807040301d01c4c607001e40d083c048a030b408802040018101070a1028981d1005a4110380240d50304000780c2501d00015094840380040402c1c0035800828846540e0342c100c00343e4500d081c0d54955030b002002d0320381103215252110703a104218092107100b174007e0120143c11503010712071214074000340da00038240c807040908140560390540000ba03010b1f00b03a20013202d600301807070000917203031007030f010003402c0d008200702c4044d5a070b100250b00503038400e803601180b280a5986c0d2101c40707620f500030f55440340460308a0000e65204802800540f0300c042c0454141c030806641d06620203030885c0c01a00d01c0003660f00029401801e1504100c2c50200000141c24010f8414502400c590140c1c00301c1882c20405030742814543d001001c9240c0e00e54a010a5038400368490012110068403940310706040210580003c40020320000901c01d10a41c000d4544424842200380ca901d0020388100503482800c1060042c0440c03a00c0d00d600501700d42d414070907100f0b16900103005240716250f000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 670664847 1250 670663597 670663649
    0x20a0611060a050408090f03070f030804050918030d0e1005010825030c0302011b0f05010c200706120609050f07022e05040f021c05010c1d0603040c 65
    0x5008400c20700c40c110010725401c4542c040c060180e90400d06480c94a441c0c035051000d14128a0513491305840344007400501c0c0015918072400950042e50059211814403007000340305100500001c848030103150081040103000300031508000c508000c001002c07100f411095041600791000e0394011484e05000080034500410420411600c80d914100ba007032003820f00c8060034015000281c00c1c04e814400510055000d02c05c0d03400303103c01d06608100e034114241d8907150112075002003216140d4440c0c10000d081b582060245080481040210540c05009003100e580c82d041ca2082008200490603040901c060540c40300d03018160019042c0319074506030005003404001074035503100510480e50081c0500d40c003c021003055690b04030201000e82d1540d6200780103010080c01c10f644050754003440034010b903517424074a412211001c00389444c1c0c01a5081075400c480904103180284281c8440010740c00c80b03510810f1080e020100c03200742d00c0303480c0ea08208010100d0794100301c3c10581000c4102507007400b10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 670666097 1250 670664847 670664867
    0x1030308061908190c0b0a080a11091f03050a0209060913020c0318090603030309060114062b0509032a01060f0b030103061a010504090e390603010e22020a06 69
    0x15111003040031ba841104040ca4410070800e00d00040c0300c1c201003038111586402002009400241043c10501035000107010103211000140c142c4540c100045001070705802266800041d04504600345102c2902181310340c07081080241c0714070300440140ea100402c0d5410340d1070303402c03415003141d840780c501e4100d0944a040c110640c0d8401d0011200007001440c001003228070601c0170b4030150005918000b85041780c81003c003102507001034140103480300c0803944410003288840c1c4054618654103013509240482d078001d000c42e946034000b0014056540c6214107622402c0e040808207000700100022203a0050100b5003010700c107400c00c0b00740000ca04490202450680f802000c00300002000d0000c886405c86201e401c40b400b2460070301c0100114822039002142070b20404098170800c400051090341d54840141003a1000c40080b80c0120594200d40395050010030241d034944d241d94140901d00d01410002000e0448818028424000302e19801110032483d6031302504000314561100d001038000220 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 670667347 1250 670666097 670666103
    0xc070f080a020405061e09090c18160905090718050d060b010f08070206040209060d050f211c02031b040b0702360c04080f0304090608060103030806190819 68
    0x184004a007882ca80508500346c00c003001c1710304200c144c02c040103001c031600c40200074a0035405500c3c001d80342c0c2c2e1a12104041f40c1f190803040c1c0c0781549031501074040c00c080040000010001c2c0c244040c40103440b9000181e800c0003040c14407690050120b03020300c2c98503d1a80241d5000700d08000344400b000401c0d0805c28031540241c8400143c03c09285c811610801c0496209005038001703030204001d8142580e01c00d80004024120f24145162900c4040c503101c8032101803045a400902144e03200020880141d034505400f51040346271800c4241e4008180450491103496a580000400c030791030039011a224242d03407044102d5485a9942450b000103400c00d4101340d0283c01c0c0d07443c6998240841120744001c5541c503c080c000d0452030500c0000c0c020400510248150b14208000300b0415810080810f0b42d21000c00119521030410306000f058520703641c01102ca5502c290010f00009801140d0f05910034030582d240c941d60400c0c0e0f840c100a0450300c0e8030801d41c0f0300039110912514600080c070241000c1c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 670668597 1250 670667347 670667351
    0x102d0f08070e13110411030403080609160e151b03090118030b0403080405480d110d020607110406060912151d0f0601060201060b0f0c070f080a0204 65
    0x40e0715002a200c980045840c02c0a2101c070600303c1000400b0b4078144164036401a0000801c0c0401516019460b88103483c180c010801410801c842c40c07400e6030003103070b024000039410700c54980f40344c3d0080c014024188600c0c3c446d512250003a48ca9903030200076078540c0d00c1c40c41d0002c2c3c4010391140781641c61754000c00e0602d00040c54040b000d02c040313001c003c588045a41c405594600c45d69070f030b1000c40e01014050f00889280c040d5002c1400d059845000314290006d884c90740c4103500000c0440d00c0818070145c400d0010500b5004a40b90303c4e0740c2d60031707045150355401c13074804c0b07203c540c030000010078108170b040c00203500031004180b0406205401c0404103510b87c05850401696880780825101e800d21481500301301a02d05810000080e46214000c0c41407403c0e41d800b01d6462040000380c84810b81420312040c0640c043d24940d14400c0f002c1011034011300b480e0000b00041410101080d449201d0030101000400c400205000c640100700300c1c41008100c0e85146051698941084036142c0410b10026881a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 670669847 1250 670668597 670668599
    0xd21031b0c1b050415170a0f0b040305040b0d020306030d0201050c030c0d022502030709200c03090a080c030c010513050918100902090708102d0f0807 66
    0x2440c4440810009125616071103052003866030b0b14030205560b9004411005000d90000619440354003401e0f03450900c4695501406042030450080441780140c69010383c1d103c4034040d07001c2591b640044440c83c0d005414070070f40343e0700d5080580c0c036445a5401a4084000010041110f00705680594002c003412400e80362100811a000c9003600d50560340004a54810404600402d02c0d40c8000d2100003020000903040c2001c00c2004840c0c11020340d180e0038011b140350800340451405006080107001000001c01040702c0116600b0081d112002d0307a0100020001200035a0382c108000341d60b43c03140001c04000102d5100d440d002c0d162400c54413030b54040e110f494000328066001d501900d0030311a035030410181d121315150801030104030240081e20404c6920808030b284046c02d00c00c0c000d400b4100140070a5200a510500c50459001899603080185007805d028410b4030b0203907940200e82041155090300380b403403260020091618000424146602d0b040014601c03440640f180403180d807407007511992 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 670671097 1250 670669847 670669871
    0x140610060c0b0c0307030617010f14220212060411010212090d02100c080a18060c020f040c090503030c1006061e051e1b0106061103180d2103 62
    0x515005004204a5a070400680c508043c0409103600942924021445960f5083d00b604040782d000b8803a2503e94580301450f450340094001d48820000e01c85444a0030301d08141d0003201c05c51a009a10315294006403032000f95034658140405003407041040c1c6046080500c0c0c45401e009401486901600456904440a0b00a0320554501d000d01810010441c202642008503045d02c0034903d20500051842002c041605000903207048030720b54880e801580309901e140c1c031004583e5170000c0c0810000310354920050303d40403c3c00d1300209050340d001c91900c044400685002200c2d81065815100c081104407218000181b401d02141710082c04110f010380b284d900316443c0001c034021500b04000710035403014a612400080c414800004080d07120445210b86042c034030f86c809080880c0c400305001100d8000d100070310075100100a90f007085601074002c508601d0720390213504030707508500300d2011800909848019050748050350080004403942e0000748047d078032405040c400c4000901c0c140c800750b80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 670672347 1250 670671097 670671107
    0x20a18051014010c0501020f0a05030153060705070303060906050603060d03030204180605040b01170114010207053a2409021f02101506031814061006 66
    0x240e441001e54801d25a52800064501340091542299659404c01129843c0c4036148050000c28050741d4643e56203516102c10743c1c19800500710329640380c0c1d010400556000400c18030000600307144543c420460404a00b0b51034800c2900140310300240900e03002c1080305588500103140040c401e8804101041d128100d040856040b03005858210380300f08007050785c47c0b07002e448017201544a807502500d844c0d00e5001080500c01c1006129111704e80340d00d021700491405026003070b00410281303850340302003404040d42c205140041c8140d91403c4000c00c40107555901c28030420000e4180504400240d0104513807100c661403c00c01c441540846e021600c680c0325403042c10082d1500d800c4000b1000b4000c41c412600070015582a0800009544101400068a465100e291414207440307900315843d80612001c1e0a084404c3d440304113162410301480c98843e00c841c4030702c05441d09490001580c840701324408a0501c40660054401e401c204042421454005800c7d0701c20304800098007051940c0c2c1c403041c2e41e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 670673597 1250 670672347 670672349
    0x51302190206071b050a1b0f33080103080d020903060c19050c0d081312080f0106030b0d1b1a0403050c04020316030b06090d1104110702100c0f020a180510 68
    0x360f0b03041b0403100e4011480707203d035240c2d80d0316984c0a00c005040e0b40e0b240303c40494401c1c1d03000a000c100040324a00300320585a00c2e81c60384505940e800c00701c08126000c01410b01a0500000f0600400801d522120700c5840d415115048405030480c0c00c182410442070031503401c070612030f1f00b03002c00072841c02c0c42c1c0310720503010303141c4a0306040d004018001400005507100200189541d40d1400d219107c2d2b0041074410311309182a8000c0c2e11203141a0410f90401d00041105800007002d143c100400040e140d2601d80c0241841900440b00c007180704080e8252802401060740070842411225071254140359241004000b03c034400c100b2520b04000020620042e800100d52488200c601c01d10602d24550280d00160300291000780007510f001c002500042c1a16150402a20500d8100f05010307401d00b020301c6000483c1c0b02c4068810704240c40d65000800f5050314080400822075201980e104029070629091551a4003e000e104000c2e200c0540008410f026001e03d00003506102c00320340b92080d800341c500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 670674847 1250 670673597 670673603
    0x10b0102030f09240a090f051804060f060617161b050a05010234050703030f09030816060b0a0e0c340302101104051302190206071b 58
    0x18100440c4003030302d12994000800c0e4503000089155052500c0352880c1941c15601000807000380c6641c40180c00078580c241c590416a4059010001800581e4803150b03c158401012000c442c120796451401c08040c2c40b8407101030007011309200c070104201da000301c0d180920604602032020f0b2903440468020000100740c00500216008030751801408600401540b141d0340103030201c400c102c1d1603036103550032a030142e10f48105d00c400c042d01808918030740d4000701031400c10a451140174800c0689805071506100d01c00141440004000e240c50079004200b0320006507040f42400f526000004100220b14660340e10484a241c50b01c09101c650745809080303075081d1140c041103681c190b592074000480030750000d4071440390140c5221480c200906243c041c45910003510003000400940b514020380350154031024500a2401c00d61445042694482990304840049848070300200080883c40005d100d048005680100040100104581c00203641c8d400b6101c0c40c1c3e6a846120385038049155101d10b02c000003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 670676097 1250 670674847 670674853
    0x30b09010501110a170d0c020109050c01030203091f020414060c0d0509031e03090901051c031b20210304090903110d0309110109050315041506060c02040608010b0102 73
    0x40c40154420030f5082c1c0004101821680381c200316413074501e220744070100c00d1a50140006a2202520464000c1c0503600c41540000d0000d00c3c80c40d900c40e9210078824130714504060b8084001140490708000c405002030850080051541c0c4019200000c1e40c00341c01100141c04600c51070300c10314108034040769031020000700603100e080d00307003d011200ca500250102da41449062800e800c003400c4a8909644602010025651600c034001409140d802c164003903071150700c0d6007208460081e40c0f4401c00303d07015811301d002d0125030103500110188114070300010341941c405040e01120305d59058841c60380c1700c40c11107140c40e04652035811880321140d00380138494a9081800308102690a640002607501d1203030074040801d9080c8984189000682e108050000707803519035042c00d000c0300e524090002c81084c03800703136030250810780800e5030303034403505c81014030904d5090000b410b014002035000580107194200380300c07803075544000501ea603807203043c01c1e0303c82d07440c011001505400c1480f0b1000c1c24001a005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 670677347 1250 670676097 670676099
    0x3052812080a06171b01030903170c07060f0207060b030d050703030213210b1015080915181005010e010611010e060c04091506092d1202010f030b0901 66
    0x200d400000150425400d0740d182e02c030220f044010b40b04554811410280240591620301d06000030300c00c800d03021071b8103051a110721000400e60000e010941c410a0400c2048241c0b0b07071040203100c51184810160143c0e107032843e2100300d071401e27800902d81103003d04418469410888205030700c940d0792110034804078804001003400680207802501424010b8000c40400c2562034445522034000080c0d0907142030000f000250800050310007098000300c0a01901e410141011020184010305000e050103100c09180010741c0700300108021a00f4503a100d0a441c224184698400d90f85881e40003010500d00400742c203084842c4a03803003270704e048506142035003c0b035034644441503d00300c090480001d099500c500794540e443d2400c10015000e084820b500c141e41ea4904900c1c101200c4503402488507010441801f040f0056100c0d00703880903195180761008080c5110000250304c901c010b1410a41102c54400005002e003440e01c1d018080743c000c2e03c035034200e07003403c07070f4100d040f1801e240384150321800300c00c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 670678597 1250 670677347 670677383
    0xc061508031b0a0c030b01061b030c080c0115030507060e0d02030615060d050f0a0507050c060a240f0812070c1412150601020f0309030a0807061401030528 68
    0x4a2403450b1400030644800c0b0300301d51a031540c1990103401c00d031074803d03401004000ca2036110390400b00d94092400c508000002565000b07000000110700a0b00111004c214440310722000e40c0140d03074004481400d104100c0e175a240c60383d2140140c2c0324550115041c03407035044d03d90400b2000d0301d424940c010050b0800d5034801e42d20070090300c41845459003000b01030150b01d814120ba0301c40c0a01420141c041074801e8a8010402000d03a0001403114007003104c14000c60049460016500343c000d1055a004035114081d031003c02410941d80b1003155401414500000302568105800f1080c1c48950080e2880d00c4c41144800340349124007070300101100c81d004001c0200d000e0b1940b1007002c11100030b1a450501e5014000140340004a0460940a940c3c03103040c0040c1d50303010845003290242140140d8200355908000945901003194085c00b041c0d00000c2e418204000d507404500c400084403a95040340d42c40342002c95035605500d001503441144003507401403004050000c0146243d000c1240000f14034062 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 670679847 1250 670678597 670678627
    0x138010c17270a1212020705090709050427030807110703260721030f02042402061504021e03010f0e010506250f120c1502131203120504030c06150803 66
    0x345139201b14050740002003482e98a801107a40218400e640d0059154103082c108021154011181c3d50800c10740c90110001d49410000380031500e4242c10804072a983d114400e8a60344041c800b503a680c0e0152200220801c088030131402c0d0b900019003001d8070050105d21041426114100b8003800b0340340c140c04800c0d01100281400d407542105444c010074000760001104050340c001c1c2e0000c1303034000501d40c80019810044002400e801d600d6100038011030810f20242c1e041410941c80460196400080f00b020005d105482151a41000035500d5076a60351451070704020a0280503020140036150000980d91920a050301d01c001811181d04d000301c4045d690142001c80d000400315000381e40500580007086020341c02c4003e51069841c1c1c115101c6440c904980740200791108600f01c2031041c0708a108034950303048200160f41c0c190714503442207069400d0560b204110049202e01340e606020800040581c030020200150b84204000d104400700040d900100010901641c01d040d4801d0003918a19030400d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 670681097 1250 670679847 670679873
    0x70b04051f031428050c2a060c03180a0206161416090c0302040e01120201050f0d090311150a111b0138010c17270a12 52
    0x81d040005030050101c0d030560b10b42c9003c4594148030390540034812440807140000c00c130942070035030082029240c89500d1400600580307a141007445499510541c114242802042c2c0c60141c03c000c4440920f0722610002c8154070403584022491022580c2604060740000d07400c0034992300400840c140858100b0b60f010006a0310410b80f8003008840000c82101c80038040c40944403e4203910488450504040105551a20203280200f600c100000c01c10401000192070560b00c04d07484400c441d0b0034600040318070b40a042c601c400084030000e240c2d00d13103008642c000b074030141c442d440d9404091082122181c466200301c5851001c04843d000165003610207522903480d808031500340c40d0506c81c40152400c0200150040705880b80c0d5120b41982105207030707240141590b018441c0108440c64408488414908459130b45818041440c0500c000c0018440c901c2c034001d0114841c65444240c595030400c503001220f801c8078486113960005900314103044410a042d204082c00c803070b8609565a903030305200401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 670682347 1250 670681097 670681159
    0x2120a120507120e06091b0a030b060f0613030b07030603150518030403060212060907020d0f0905150310060f0c08070809090c0408010608030313031d030709020c070b0405 75
    0x18200c0f03509007030740e641d10030407004d0483d401c020121890907000d4507241c2818a9400061122610700305101e60b0346d0240c00c4000e6981c04944a24545c4a000108240c0e1901d02c1c820b0758484004264050310328603014041c01100d00a0450402c41d441c0c4550540482d503070f0b400098881c04501410f02c070f829950b500a42c0e0004940c610142c40d44001030081030440e00280c0007180c1550300040c1110001c80d60301401508244200d80c8202c2134182044060340e03a5074440801d401307100342400c0d8101c1c4a80103101d40c0000b0715001d840c042d40c28103a07451880e183e510481d00342400050010010500510415a12030f40d8085515100034104d80c035213071502e0542190000319580c030030401c031803403440e2103000040c1e004151090240c6d0300c0368203251000c3d0958031075070407800459005004203c1070161071031041070030941504208040300398001071409500654540d907a01803107001e9000403411500e40c001d0440c83c16450983d0035180c3c8440c4405850b12942c4540c03a4042c0d030341c0c4004440b0300d0034041c0c41c2ca035100c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 670683453 1106 670682347 670682357
    0x4140415060f050910080405010507030506090c13081e2a01080c0c0a080c0c03060108060406230901091709010804150e01110a02120a120507 62
    0x101886110208030081003001c2e2000d00800c01c5620280c0060301242885003068005851074500756012142d41d841c0000049401e03200e4440d9038050140100040403d8403074132100200c64204c0200d84454909a54002421810401101015201303440080304040000c206850901d00c0311070f0203880745a0b00345800c0e00b528a038044020180002400c2c4841c01d0b40796a000d0080c14001c03c1c1132803203107100f03210300201030003e02005400580044011144d80500c0b00c4203054550008ac420040c85511840104000a0f05904420103a00340c0017000201310130030303005100f030f641e4098982140c2655a120602c00348401d0101c0c080c0c01440710b8004600d07020b41c0c1c000003000e40000400241c810032842c51010405015a04030800b450f400100901046070740710031040f020b90120003070f078000d8031581c00c518451006220544171414a00e46410b0303039205a100502014140040036007041207 = true := by decide +kernel

theorem cover : BRFrame.Cov 670503597 670683453 := by
  have h0 := BRFrame.cov_init 670503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 670503597 ≤ n) (h2 : n < 670683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
