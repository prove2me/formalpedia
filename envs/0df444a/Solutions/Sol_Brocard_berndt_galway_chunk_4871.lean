-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4871
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:00:40.348917+00:00
-- url     : https://prove2.me/submissions/18ddf964-5015-4884-a989-36544f1289d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875899280 ≤ n < 876079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875900530 1250 875899280 875899301
    0x20f0c010b06180118170c0405010b04030503090d08071a07020d0302071a040203210d060603093f030506090109111b070f0807090b04020310050d02010210020319 71
    0xb12420203500c2007840c2982c448a0040c00d0401c000720401c0c110707990300804544c000e0300082c824522076a8042d454036036a18164403829005d5482d0400000da82120300c0285c4040d29401400346191000800c2001550b0740015130540e0143c0c000c020990000c1d0100c0b034440324518120b00c0240c00c6240c54034020303041040940031401072500401c07041e03001401c0000307444a8070100c218040002e45503400401e00e8401e4040354454010300c0c0d04200303010317158003802070041451107923400d12065440d207004406480b24060018000384001d58014061042c00b0b2101c07251f9035000c4403852034444038a403599a040c40c01d00341400800d94400034461242000a50140540142a424404040040e0010202c2d1044523a80d61142000101d0340e21502414050340c402030041d115800407040e224450192142c07590703c1103040e1f451802003040d080e414540240c0340306100364090324030418501400e004c11280307100c20490460098003088d42d261080c0c2e1020354001e80d02a506090398210743c034a01002c03110145007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875901780 1250 875900530 875900539
    0x6050109090b0a0c120203090c030f01060b2704050109020409150806070f050c0f06010503070e0c0702040c0c0b0103060f0c0206043c0302060a06050f03070303050c10020f0c010b 78
    0x7400e00105526684583d04809464400140d20000080880304403800059040d01603000200380400d420b800541003810450440641d104100340881341801c85600d441030a6840c42c061080715881900e00d6100c0c1c628104912800d0020410103000908a4800740c02100c403865020805000f07200b41342c41180141c030003d100034680c140c1454115a641e4030020594001c003c90913003002001807044064030f503134401c4082200c143d130090f04803640e26103500740500c500078810f030400000e40c241c58103400f5000700d2618140700d2825580e07030284000f400c0480e95070010b100b180c648400000ea0003a00c820300950284600041404c0c00e98555404e4820b6a002e40085501420510000c5040e5400c0e0140b0b1809a52103041003035a68800790f00d02010611703a800784124130000e07000c2416004260540f24403907000e020482c09031030764100a8820011400c1d00e800d0307480140188000f0380600c006001d2443d800080310000301c0b00d40310403016a409811100c4940b800820b00c424141001d00030b07a90000012035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875903030 1250 875901780 875901791
    0xa0513020a0e0c04121136060117090610061416060b0904050604020a0f18090c0f140906030307080304120309080c010207031d2409190306050109 64
    0x800046003010a805005000000400402c001c50b0260b01120b0040505140044082e085e90070626401c2c3c800c4022a4050071000e52010300c1c1c400c50101c03c543d8071802c08520030040750080201011070300c008081505000320100c5054140c200482200c1c420042c500090820f8074102c0c04445480c0140d9224070b060041441e10034800f403400310141c5910100340440001e80c0c0045041410103004d8055899070000c200388140018014041203d80c4500d00070344191003090b6560900b5440d6002a1180380300c08981c1c001000c40707050241d040700c04e509024581141c452601d030b9250610300d00d0a0350020901003800f4481d507a0728285800460f43c00f0000b2406503041401540360b008913488014401081c08420222000c0d00a00036809812002d4000130303419200d04510384c40034000e5100d8507058011a40002c040e01c010441071000c03411401002e0010700c8482040d600320802c0c1c0248810743d0341081d80610800003252106409000c85030b50807100f030480399156003440001c580042c4c104420003070524 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875904280 1250 875903030 875903033
    0x1d06151c051305070509090c04050a0924151802031906080309040e0d0e010507140601120213060b0d090c0515031803090a06050d200a09060c0b0106141c050a0513 71
    0x422960080201509d0214095841c044501c000309511310005044200d00c0710f2400c1c001425800e51542030512060410031010398a003020000071891044a108155110004000e07681540155400a60300d00382c10007420030184120081d60060f0300008080d910200b00e04107035203000e008601c0da6031581000740001400c0e444004040e104042c8400341400000560b0804210a480b00300d03044140310010780e012540c60380f05540019841c0c0e0403d9201d20300004143c400841c56124000860b01000030300b62030014990945405480704200941e1a81603490300060562200c980382000002d1804d007240c7e480c5800303041611141424400341d86140c1c400e219404aa445041120f01540c0741ea08000f519961f601201401510391010a51743c000c8080c0b014119036800e08002e0070030948a91103c41d805600e640c4200d0f1900030546000c0d10102423580100002800366044034040c0980c9a12907250030340854002400403104104003403065503440030401b8081c010b11540d5000501c40d02da1030040c8145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875905530 1250 875904280 875904283
    0x141005160809190f080c030406090509161103040e1e100b121012030306030605060433030203150106020105060d0b19060906030803011d06151c05130507050909 70
    0x8010012101c02c000d206040c203001039104c0e04d811040c1e111450b070355507881c0c8030091900e81d042440b0710400300d0300130704020405250141c01039101e104e240c48807183c046001d000071215000310211581881c001044007249140040186520a400c003071047c5031007904a0b0031203c02140d009203040c2e0440e000300d1051040c504c0000440e44800800e0030301e04040e80303541b804204803100a0380718a582058501030340c1d04140d010b41011003124040c0c0747c1040917545a2052000350340303151a01030120318549240480c1002400202e043c080607500e45400070036140d90100349021b120310aa000005c22034801045241d41c24014258003078802e441c24182c1c00e0182da5a81c23840750f0064100100542a45103031030090750264403074801032020344000e000950b603d052144140d4020b000d041e81201c0c000c40c892000c003625243e0a4091200608070310310304214071060404e207811040a100c0841d941c4031000a05031541d0040a010740940407a641482c042c92030171078504200c81e44003d014480c55400c00c482d8510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875906780 1250 875905530 875905543
    0xa1401060b0a0c0c0e010e19061208070501020d0203010b0c120f090120120d0e010603020a0e0705120a02030a0b01030506010203091516050607020d020106051c141005160809 76
    0x124202403c030110640340c01c035000341043d04100e50144024000007108044070100a00521540307a1542d043c0d060041804141c50b014014690b090501001040c000b58641e002080102e0007400010304201e04e0302d00f0a07050764001c0e80207850a010100c4d469030340b100140040070b112284200c805240082d26074100304540a0150840d0520150000c0580341c2c40c0c40c07165000a000d820400d4540524120340000b00c140c0002e440d50440500c1c0c00d90725200c1c2c450510525050b42d400600c2414180d240441190910100031306840400109120700c40207070060072512030158601100c09070301c03442c00c200794804403440140352604050801082c48030991f0040b04032a0034020503200d10303c1200030440b400c0a6885814100b441940001aa00040c0240880d48900681d296800c5d10950303040400c0490903110a4014241e0004409440d0422620740d074945d51000d5100e1001d0814170340d4803d40041c1801404040c9106044c0c4450400401910320703000c001051602d030414056038180844039903901d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875908030 1250 875906780 875906797
    0x30507090e011d01050717010302091605121302011403060112020901020a20030c10091e080d030911010309110d06020f0d09051009030e130f020c0a1401060b 69
    0x690760404440310301030030b42181c0d81d0303448100500076528a4481d00180200ba007104c4d00000142c1e441070001e07400d909458140c0c120b9800030144491a00c03a114a50040b20380300d4181e8041c004200220b0207004048503d0b42d11552003560301100c1294140009058905480c000103c0441c040040081a070b8100d001d0369856008900c005031107a000c80e005030700e014039940014150f5030420201c9030b0155102605414281c50503400d60310124094020b00042d040e0fa2401d64022841f0b810081c0030460f5025085101d640d90402e081010a42d1202400d003082601d401d031100082c1c0f617540c030405000c002804101d02800c00e2a040004895a45401000c0e002801c0d00350301c04d04070f030348968003401000c1e01a2100c0c0c8810342c003200d40e102c07006043d100049c246a2403c9400b8001c0141919440000b8071402c003055402d900c9140202084c2c0f0104040105403840f24560b859403001c0340c1c00b0700081480503101242c10400202101c000a0801ca0318400c108114000d45a042070b005000c285400d100b5a00500d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875909280 1250 875908030 875908049
    0xa0507030c050f01150f0e01050d110102070b0c0a060b090112023604031b0f02040c02160f050a0b040803070807140d0c0303050a05090606370501090f030507 69
    0x30320501d09507041c252000203420f000d42c02e104103a105041c4000c008012144136445c2183c009940300c1d5185404202440703a1b581c00410481988040749228040e00312607003052041d21402a2a00e20001454001040080955000408443c00c00c596031090340000c03141181d48130482d602d0a07907950210b07061010021301424500400d0b00c8080c19172416901480e40d980909584250710392001c00031301c0800c54040c5c0004011221007100041501d003108000f58004140c42c0c10301196800b444083c11000c0003180451190402c1c1c0354031368500d03880d400c0c0541242d0312980740d505d151504000c121102c2d5000b2546070002040108030018000045550a580c4071040a4842c2c0702800d000000010a00300301046010b000c902203030b500c2d03004464400881c8240c40800941e02d803042c440044070320440e004001e9600c2400410814940703803100f40c1072095038842d00700c0f03a024041c17040c100000240800620484400205004644e000400b5102620110361500b1031640fa6442d580c0d522801442014941e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875910530 1250 875909280 875909297
    0x2010e1501170f190c0e010f090506030a02090702011b090e01090c020a050319030c050c060420060c010b0102190b0a050601110d0e0f0301090312050c2104170a050703 73
    0x580d02e042c031000201d11186415503051581040000000300301d040000c0710030480c940c1d00032940c89920b1040324140c50f0106038024103207007081758940c0100006031409030308d4807a403003440c001039881280f894424045a400400c44a480318000d440d40d5900d50304100502c280e0043c2408128254031140d4119003c504000c2101d450714a0180e0600581d10005000d6000000c0c9010792025400356200c6005a56a010040c0300300c0350394200c42500400c0d0710505070360030030004100810b041d0b01c1110215200c0b8001c5120362800440011441e0340300604100d056510392240320195a018050215002c0c0d062100d40b800740a1aa1150452031000741040c207110769410102d241640b1800d00d9910300d01192048030780101c44050080e24821905203900e100f400342e400c06190605045c0290320300c103a4562158880c0800b4a0614409000020b1a40301403103410b0140d1000702c0c1803008080004005400707000d909003050700b00740c1c003a80098600d200c1641d82c100080c00c84981d0007030031503645640601d0a02c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875911780 1250 875910530 875910569
    0x1f0203150a0905010e0601050a12090c0f09061706070c0609230619021305040504081908010914160539010f09050705010c0f020a1502010e1501 63
    0x12500da18a4240c0e800078245000071901038101e82c4602e05a8200400040003980c40100454080c441e02c01401c00040e4860000305c0d407080300d500070725001c03446101c2080c030707542c1c55440b16148142640e02096510752100700401c403170004848050314106210010302401d00c0c00c4030b0042c200f48043c210042046a6131400e039002d1011400a00359039080241c440c4000c0b101c1d00854540e0391005440741d025003003901c5040180140d461007159020b410a80406000d1440c201c1040014503004009490f07404013040007079594000603016007054405516800d07419414035040d1400ca8407142e031180385524410003440a40c020110f417008111100e850201c1ea61588034683c00e0780f044090f840b27400d5101001c41031200b5000610700d0341044034203a000801800c05881c0710030058400002d0701800d079401804051010394458a030507103807640200d000340d0740340210b0340c00708000741d8040d44403031540480e03100c0004201d6828011a10b12440680080400b00380b41c401041c40000103118404810300d0f002c0b00142d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875913030 1250 875911780 875911801
    0x708040e070e04051e06031c050d021c06030b0705040b072010021b06180904030207030b0702151e0f0702250303020d02150c07020a08030703031a031f0203 68
    0x1109a9001d40f0074031490030a00403905603805000807624005d0103881c0001c0b400d003400500d0210001c00c051549800b6904004281ea02e43d001c089030214a680030005101c03882b240c00528980c0b41001342c00080d540b4a03604004854101c0540103504224080000700180002041a00d80ca00e400c0303400d55010320425008400300c20100380c1450780006241715001003990f0040b44020025841199a082100c024020010540301d00b4008480145003090821401c4c1020010298014480c0c011209400e45980703a01800071800c07507142c401644200c05016800c2e01ea001d0007500007400c00030b60a40e0b501e1006070f9005c5400c00400c11301d014280d2200040c6510700c20084a0307100804c02e13001c403000c1c1015201d08800e9411740d00080c0c01502c42c0310b543c10000e0b440003c00016100612070841495120008081407e0f400a40d003079901215141c0c4c0422401c00c1480200281cac1e22030344002951200e84205484410611402039200b034009c2c00c3c0c40440f9002240c141c0031902e03020040182d40766612510003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875914280 1250 875913030 875913047
    0x180b100617012313051314011e050601111006050a12050307020108040c0519030b0c12011203090f08031903051302060d14040506071701060c0b10050301240b0708040e07 74
    0xd01300e1400e090522441841c84001c83c60032601460400e031030b0501d120343e03080c00d03116615030540c94800f0045001084401640c4003e401440500d04600046010782c0b1640ca800d1408080b0000345a071f41c807041010f454841c1d8039500074424603c400c00382080d01c0c4c44140e228001c0a9020341480841c0001070100540000c80e03001909004010341c0f411403124400403503035941800104d070400c1c6000d010038004070a50095402141c044942c80340c080e82840540c4842c0e0413018011800d00011410120341002d20684650182c141c0c40300131a114182c040c03442d0356401080e2400e00c10305250405009005c0e08220300c00c0c5100e40c054940c01d981b40c100036861001412482c40d02000016460305000811501181c400d0142c2c900c2c7d5903a0541c44011241e4950f030040a10890b07010958460301d20340040e0010101d980e001070000d10300310341203940b000444c0c25141c0240c0c51035260409003203201e100403003003203c0790050321000907200d0074040240d0303075514144640c0c09280d5520200700002501c651040b03803203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875915530 1250 875914280 875914309
    0xa020a050f070620060c0c190317070305150f0109090e010507080f0609010302100c02030a0b06121b0103021c0614090c070f06180b1006170123 63
    0x40360012408015107945565990144200149640b1300c00030405141d00400803030b80b03034148080c0c035207070700d425000311541d0380443e141808900544104440c1854014401d595182c0a80c490715a800c045009400007560020b14250a140ca44818040880681c0d0911242d01800f41d590a201006c8407005036008506031f809600b0315414100da00d00030080c1904080d0180d05281c07980580c50f155404918403401c0100c50164100d04000010405460858911081e2903254100441d0905264010a051802610341940d80d0900c110500280f0705088200e900d4203819840501101001c08900da0b000911004070769041540220b0204194012180c980d2418501d0f480202b01e0107580e2500ba12a8403083c00c4103c0c0701d10401000600a03483c018100c4800f01c1c0e02400030010300c4002c0e556a0018031010b0f241c405e01c1c211202c040d0f0001140b0303c01e0240181c0949001c035403d14a86900285440348030801e2403820301d040001003010680e502d603121340040c0e02c3c40f243d81410f030084012403038541c2030311103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875916780 1250 875915530 875915533
    0x1f1e030c080d020708070303020d12020702120a150b0904080903011d0a060b10050706152606091216060b0409142a040b030a050610060f0e0a0b0a020a05 67
    0x2000210700400040e403500b115665000c1c0c80120f50703110701481d01c4640c1c1c0c2c0300250160300407803404154944107008040780c244144100509142c140e03008264196503152400d00558081580c0300705000d80003080c0d00140c6810401031141c4c071840d101003542c01038081c03c000c1245102086082503558290810b04181d4504501c410b20024000c42055440d1822038081e50383e1440d1192031491030812042460300540c00f80c455500d81b283c16940c6800030442200c02030101505ea180100b6203921440200c642c03090503003901c0d0f120004d14101c0e01c3c2880700240106950394042d0340381c48610580300098554042c0403042e116940107490520300080e000754010954841d00e02400d45081084407210b417041802000d003180c0680e8200301c003001c82960b40f64118144400309500d209500c1c5040e420154032508050141d606003100b5981c3c65240c00d20648020400038030040041c00300c01e500901e0620544071514264400000e14070228a030609140281c1c4200400005d10807803050007004240d00042d1b0100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875918030 1250 875916780 875916803
    0x9091903021507030204210c030803072304080a1e17040806070201060602031b03070206070305031e0c1c090210180f0807051c0605040f0204051f1e03 66
    0x36009450740111852030b6030203544480400c00c224071910a45060b1501404000c00c1c0f8000c00d1003040714240421011901590504404400078a150000d18059041c41d00c0e4400c41c586a0b00d0208501c1e01c80c41a44100518144403c2010400004014002680185401c0c00103035000c120301908000c045c0020b00450f50004074019503800501c002d0048440410070b032500b586860404038203a40145c440c04005030700c1801034203030f6100707a0424003c0e8103e0000440c0d2801c1080d40c003080090b0040b0380d00303a022403004000c100c503025400414120000c2d038911100303039610f44010008018018159108c4070304007003101a5101c5400b0741d00221080340c00600402d0b81c03980c1d85500400b21440403003056a450011540010b840c00c001c4020303016554420054901e16040a040c08903e403490030f058600b507110005a000825101e2003070b140158000c070405100d500050041c841a90405010254151003840c403204401c1c0175400400c00340c804010b000840c803441c041904c2c550741007940006e05403031400e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875919280 1250 875918030 875918033
    0x140409050112021807020703082b05040204061205250305010212090705010207030302070b13050a06020d0201050c091c050f0d1805060a300f0c080f011202090919 71
    0x82a411020314030899a403008900071240c001c0000e08140c2e001700c05640b0181c0180009820304000c1c002e000031400d040e80203640d21891160300d0b090b2400c001409036a6400a20044d810b060280e44054031541d1803c18181c25540d5402d0342d142c00e00341c14181c004440c0e410061000001c034000c0d1000355040402992a086002c920559014080d20350b000a841054000100c42d400480c0030780c100d0313406401404205140807804403141e0b00c030f15800c00130f008490310080303580d68800021074007a21640c0c0c010020264025006800c40758082c3c8800012642849440c400d41d441c1c02e008a582032500b00d001003510924036000380f61181c40308600806003d0030041c2c03501075600401c42d40328001104580311490b5900e2080c40802c0c4281c0c4101350014008450315108601100495070900740302802450503c103e42d01e91070121500003006225451300d1f07010044801341e101da011034000300300005400581d49011000340720501e110100034040d140392000252604400d002070b1680c01c1c2591101c0f500c0a01c3ca = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875920530 1250 875919280 875919299
    0x11030a0b1e060906160210050d11031005010c05070e070e040b06090303030402100e180a2d0c0216091d06041e02030a02040e1018080306011404090501 66
    0x40c082240508401c10000d590100000810104a0409004249072524541c00d115056022604840100c0340968500340141c0701c503010114020503681e1503d46414203844048155200503000b541c00d040240280b10640c105290040211002420116007116152030401c1c01d0500d56488400b10200c0401048510380d004142002c240b5000c8504008508002040003000c0c0200007280360554401d20000d001403c1c01d4519001400c0c02d8109086864403100008150034002420754400380b0029050011070b000d1030203100c0140026000e42140f50001480b21b10303a540002e04031600c07003078641150001c1d06000380441100701c80004031403042c0f2070f101c41504000d41500b03a0710052240d111070b1015041c4601144540c0a2940320308107524402040a0f08501403020340d4050f40d06000d01c42886006903198401d1030f40711600103010340060b5001317540c18000c641184a11074541e0040342103890024450381c0c121ba601882c2405d04c00c221514803441c0160700d02481d0404040c0c10320304000851a200e6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875921780 1250 875920530 875920541
    0x4030e100201091502030907051807180305011a091e04020411160f0b1b04030b100801090302150108070f0b0c0a0c18050c07080a0e0616060e070605280311030a 70
    0x140c002329641c450307490342401034020f0a0b000361030a041c554004103038aa4030801d803400e4904c00c85100390a07100c1e00e079142e582c2190103010000030145100c1024407518201411204d5016900c0990b202da0744078020201c02450400a00003882503642e05445121400b45209803400705074032210042001a041c5004c0044010103002680e288038000005203880910307912142c281801c510360b65048c0707032071913407888000341019105494441102101140500c0e0074420001294002d5006003600b221054086d00412010303044107059402c03d41c41441030146081f075100c00c49070301840203695010401c0c1650304000e00301100404c06119010006400d090f488400d2b58190141c1d801041b09443c0e40140f0780303082c0304800e0300400d40345091180e882028042d00c0d001c402d6200c0a006140b409440c9228519040d4140703400300e400c9982d8021030001d1039010030480025010034248903252116142c0105010b131811015411420031086400701030030700c40c0d040801501052000781c0d440342800c0340307050040c02c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875923030 1250 875921780 875921791
    0x220503010f0b061602030c04090807020a050a0501170603150414012d0e160f030309050607081218070f090e0c091603140a061d04030e10020109150203 66
    0x10300304030610014407564400d1580112000b80010f280c04803448014a640c036483c103050780d050040c4003000e80c56841d14060311036030038400d950060340c5e601c4a204100c0c14101c80d40100d07000c0e001098040c015079800c06150b9448203281d40f480c80071a503800001074940707078901d40c04204203041e050a0ec010444119400380300610540300034481c1e0814501500c904118600c00c0e030f9083d20855241c1000d82500398400d0580320707198002d8030310b4901c156003252445d180950004d040c1381e010300003c205245d8010b44540c040c0404640345807500300561609400c900450125100180844000c185026684100300d003454410400744e0309495a1a04644140d00782e51007580c0704e03d1f0404561382c0304d03c0000314008805100c0108010351541f182003264101140c40390380f01c014956140004410115075680b587c1c4181001d0002049580c100240c10200d02101c082180d00b40b8141c5051000083c2c10500107540244241ca500d0301d0341d10280d00403070250034a0705025204503010426104c0c4002c02c0c1e00107521a8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875924280 1250 875923030 875923033
    0x30209120a12120c08060904050f120a0306050f0a0905281b021606050a02010213031b060801031505070c0b130b0105150f0c030f03092b1d0402220503 66
    0x42d02d0080f80d0409030340840c1900c5002a0900c40015806c0c90701c3c5000d250030a00440441d482c0c84000d0001c5864004240c8240d48800400700d112044142e01d4003800b4094441990034401e0520382c940843c4840c0d0940c009c0c01c0c1030325100c800103044200300c002e4403004441d81016440a11110705908030003002c2204c00390849103580689000180d000080405a52000c840d09070119440c2c500c0485450300710a80e50b80c1103540070010800d0045907500090f002e540651060502a120800003401c0118941d00c03000c00d200d0224010070102d8100680b00e80400c1c111030000c034890b85d0381801201c005040700401084000c400c420f01000030440340205406501c10700310803072266292020442040704c21400120400790401071748031200410409024440e240400312402c0058100f00403416810031201e11280d035102c00d4141e05600b2604180b54a0b031180703c002c18801902682e002041e2454600010541a22454011100323881755030440312145001c00c1ea80e54010704504001210103807032b218246c0f1a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875925530 1250 875924280 875924297
    0x15110f04050a12150b0f060c06010e090708030f031012080711060306030a021e060a020f06070302040303050a03020a0903080d1d0f0a030804030908060106050d2a030209120a12 77
    0x10f2200301500d20380110740101441d00703a00521007180c07002d45030781550705070800d0416071280ca680e19501c005e08551000303030780504210342c1010b000342c91441000380160380c1e90f0310200c01001501c10200840701c3d20791002441ca607072035451640c07051103280194032800f4020211081d25090010190140020500c5102c0075101d400304d040400103c0d01050712880d0b0705402510000c0014500940c08917528a00a48803094007043e950014655800919610300542c10440c940d12440c0070500205501c401d80307050460510342113440c01465400342180c035406042c1d0008503074198034050518800103607030107034100d540c07092817035111009081c4601c59040316486000c141116000301054188000c02184000c01c4401001d44007246d51220140c0181c0c2403050641000c03c81803170500109002e40700702e444160f9984405005202212455010301001d8151030210841800c400100309005241529015841c2c1141c0310014900e141c0c4034010301101d00c078843c0000c00704800ca01e6001115125174032036002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875926780 1250 875925530 875925539
    0x1a09060f25030909180506070302090a1208041503090f05070501090f05030a0605060d0b0420100905150d02070c030b09060403020a060203070905030d0e0405011706010315110f04050a 80
    0x101020400004011440030030084c0404502540440c282000945149240c0a200e48620342001019141940000c0c0c000070342001504000441000a14141c0400c1c1c2d600072a94468001c00e00450103003445d60646100c400a22a10179001003412070340101e005650740303c661074007940e200024818140030510b0010b0000321828040d0f122000c0310340c091702508007918030f0794403100100340c010051644003460f10140d0001c103407010015841a48240f8010668010300900c50001400c3d55007070600c580e0748140c50b40c20044c0d1001840085880507110b119005810480c1c1060901614110007a050304c04148041030041845220003100e005400742003071130300c465802d41d03102e1400f02c40150260348005110b45c0002d030345500555002180b80b41004c84a900d070000a802c240e5031a601c20b00040e044082c80140307241621642d801042c4200c5c0c511010320200d106103480b08014800079140380030010032007150300c24941061400100e5041e0842d074070f104c1c40d4a802a2600580552402080090004074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875928030 1250 875926780 875926837
    0x111040305070302040c03022101050102120a0e0120101b030e060f060612010305030c010b0604150c05120406050315040209220b04020d02072009011a09060f 69
    0x202038941100107071400381e09503000c3c08042c1124061640805031f007004051300c2d01d0040d0020950381180075040003c1540b4020009280c08491644e070f8040328002c02c00c441000382c12040c007200b80c040a084c860031120103410640c00c08150040d814400e07005007041c40c515608181c0c0807190526003030303c03107060b10802e00d0b42c114211680d90b0689030b0b181d40210302040018102c61300c2581c0c000b00c000c0032180360861200d020f80b8040000c4e401168036503c01b081d11140c1076020b0040360300468003942d403141418503008101d01000c034420082d10511032071265260030321034144a0461090491070b0085d80c0d8076500ca00040c820b83c07044812000b0384a000e40ca600e00b40ca064000c81e2440d0500a20312460704400c10201c90342400840e450507449903a41c00c04000d00d0300c5500142061840c10400181c440805040042600000c11214412100c00c01001c2c1d070303656989045141566034110804020301d0010400c0d40c101d210342c80c50164008800b24040c0c101030100c10003045016101082c0e044900032100b1580b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875929280 1250 875928030 875928037
    0x206010b07034103040605060f060f0d020c0304030f02030f060f15030a020d0323090a030305091809030307090b0c060406320619030f08090a1d01080111 67
    0x82c0095007070710f03151000303410288580d100e684600b2034074401e40800395566042019040d5031598001408001c0005100991248641c80a01651641801059071000a050303104003e8941098440450740d075444058590503548040c0b91041140d036901c0e1a03080403100302c8000c680413840b0b8452041c403034039460004038445004a1500445800c3d40c0c80e00790101c0a40e85d1154401030701441703010100005a03941181c950320341d034042c2d240d0080c0003c0b05030304400e551001c20309041110500300844070b02c03625074449200480717030185800782c0c480500b800000e2540001c26240c4901c01c0d44030052050040c80440114002c0d107558541c4038000742c2d0382110080320b00411000c01c1c920b400c28400900030400b15082203505080e1541c0ca2400065400854a000c042211424024007a0003081012a04000e10303410b141410740c00880303615034910754032041c920308148001042e001d40852105c5664850360700c044050507400d05081049100da000c1c50046220900c03540499609165032030110b00c20f002c084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875930530 1250 875929280 875929283
    0xb03060913080306010309030e041b09080a0c0521030307031a1c0201120f0f0204090b0406080a1502040b0a121409070b1e040b1c0c1704061d0705010206010b07 70
    0x40c1513946160054000304507404042d4217100c40d4020440142e40c80d172240412032134040d00d03d115109044080241a8007168008015a62100c01c6250101c1c041c82e010204565044900d000c00c0c050603001c000c0c07030f405c00c5181e603980c511010051000e00d9800d03801007058070340061400c003001c483c800c003040400a004120002c21068021002015511540c0b070444000c0c041071000c125105c820b0004403c90300804254856183d001c1021302400506010328540d607901101c02f0303c8207904049820f07407907c180c604000c1c607512a001d00b103a180d039520780540d80205642000551500c0b044c00026021140f8024005001464900311003145034005822034000e00d070f400011b094080c01c00c3c0e8216010f0748082e22690300044201c007401101c050440003030018003c0d5124103620f40442074030b40c4040d00c0d022511022680e05164034440c010741d1161450f004542030030b4602d82075807543d0524400503c02484095185c0382016581450010300058800c2118401e82c01c6990507070b41c5001045150150140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875931780 1250 875930530 875930543
    0x81f030201080403110d0306030218040b1f090203190e0f030301060c05011409030a0909020328090510020318030c1e150f15040c140f040f0b03060913 66
    0x40a1000d54824480b641d4890321908181c0700541803a06014a0001c54000c0c00000075140d007424021820205460a220f14003400c20030f1300f9080c01d07901d03001401c00082c0150501b1051801c030700d645e00030441c0001c0c0140400001190b0341d040c00900d0303003401003032520500e800a041810086003c10001480c04180d80100080c2d4156403c0c000f00300d40c040c0c4101815900d030743d201c408601180c4503082c074450081c501400115035420348040080d03c802480c2d4071213101c062042c0704100100c0f418014080c0c030680c040c480ca403a00d5581c3c1008200500b40000081c040f8452400030340c1400403650700950084152400c42c3c028420b06e00e0130b8907660311031400c01c2640e6170802685401020740f000110705100c0200425182d48600c01c00240d20301c9039044907000d060b60003040034810404080e201580405100780c600380b146004501d00500703520003850050281c0d980c0015030391921000d48087d0b8000e0000d047c44e004825075242c214100d640c01c01c0d55928490005031004c40c4c0b088600350400d04100e9030295 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875933030 1250 875931780 875931841
    0x20307050a0803060f12061e15010e0105190f0212090d080c03090d05160509090c0108090f01090311010c0903030c0f060219170105030c0a0b03060a090e070608 70
    0xd480280396000076202d50f40107a40c2d04400f03d0140e603100c01c252142012400241f18514020942c880290011484034844114000c10710003e0804070001b000c90714402c0c00d01d034103140040c0b00100d40c688104c8060415490142e04d1400095a00c0b181214024441d45e00303d40b0f0020050820700200c0c401c020807168001240c01c44c00c0001500c2c44007401c103461421003681d060031140004900c100580300c1048645401200c0a1034003c40340c0c004510144c0f5080c0c44000c030702d1505030441c958440c071210702d07035050155100c005504c5680400c2603c1801540900900125100d0b15008d403a00112a40c100055401c10303100b41407040c0300394107100490342c040c2d480c002c003007400d521100308040c0f20398420303120107400304440d01d09103c48908003901c942c1e655407034886d0750744480442035503040f06130082032291b000203040f900c4d6980c80c1001c00003038031f044081880d946d880e690002400c02d5099803240040d107040c0032000003182800705007a811140c003500e5440e21940c0e0b003000cac89482050500071007624072244 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875934280 1250 875933030 875933033
    0x10b0a030b0f0904050304171218130c091a03070e010c0311060f010801050907270b0a0602010e2b0309051e0708070b070c0312090e010e0115020307050a 67
    0x2600071a8803880098810741c4815100404528040c034225400d480d50303031001404000c0c040302c985800014928040240445140c4040840454400c410f91900800d122049210349591001070300011980b0b80300d803c2290181026000e4001c0805104802c100020050401881e441001c100d034071448440e40c464815440d540015a200f00021005404000c400384144114007001c00c100303409000c4c3d403044c0c0040d80d0700d804d6455081d02c2d0024020383d441c1c0c00c400000c116a409001c08030314096001103880c0d101d075032a081c0c280000c0c0342039050613501c840080000118146c041d802080003069100644055407080b084805c124222880d034900081480901d1100544c82684000320b0588a601035071211140d001452014641b403903480c40d1960031040701042585400c000d07003401041c1c051440c50422106842c2c04801f001c451001904c04848075005542c0c0e60711844c0400040c010003c4100030301c3d6116003180c05007d40034011040741c00441110400d80758000426035403a140e00200030441070056 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875935530 1250 875934280 875934287
    0xc09031a1e010e101401020c01120b0303030c03060301200304121407120305090a021c050c1c02010f05040308190e0301090f0501110f0d110d0903080601080f010b0a 72
    0x100592101c0c1c1da0315030207194089855a03214001d080c101000029418001c1800e04004c100380d0040c5203c225030025000c090342c010442401480090a12120a0341c1c1140c1010103420402c03c031a40c1400000200582d464020b4003a501a00059000704034500291144117040c051602104c154940c09100043c0014411041d050b2070022900d0007821980b46080c502c440e1740c02c400c5089441020b0440701e080500d5140c460b40b940b02030303003074000c250024080c0c0107c0c2c070690b4501c2c080c0304c22059140b042424400104040500300c1409042c080140d180000603c02c0002002d83c00c0b0b000410059400c00014403610a49041d03d8022280a1601030034642c0300f4088503c031780f480014804512096402c9070341c20b104e00d14010b40035a005000c45490340c90010f084940d0003568000c050310500a59141c000d00c3c9055850041003102c000a0000c3c400c501c400303090042001000c1c1c2d281c01e0210000400d80d01c40703049030080100f030f00d41c03040c59101e070030001c81400d03824002e100c0108811710118807500e10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875936780 1250 875935530 875935583
    0x10b150c0114010b03040516181508120c240a09060e0d2d140a02032a060a090528050d05030f101404270b0a0c0903 51
    0x10080001601c0c0c1d002141c51050702c607090f030040010a102108000500c8820300103c81643c1040001102c0c3e43c1c240300b24126aa000e41c0070442201c0e43d14680d0780d070482034005480c0702418504003110744040350a80c03141300741d50000703030800c100b030060300c581405444202c00511190014541e000d452540ca0500e604020450706000b603c101e07460b0f2150b04007000050003007080c0f01c0110b036213040a04001c40c04501605034000e03030507000c1e03402003d0324265507a03010350142c1070f681d01000d5080c0ea031050030100302d00e54001c8c01044103003902220518008202c0601d0b520401403e03940c01d4500d240e580e044100c08698810782c02500b590850b040035213110720031a0b003000748002407000b00d5140d10f8254640705d2410421805160100e0702c0001440040d407d0540c0241c2d020b0200540916a14140500f412120401005550017542c5441c615407403d0602042c081810180071250b00c201c040d6420310882030b0005403804080c1e40c0c9486d52418020748035441c2c0c00c09481c1c01071035820380ca00d0320bd5940e450702030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875938030 1250 875936780 875936797
    0xd02100b06030f1f08060601030c0c0b0c1b0f0c010f171b0f130e060306130b0a0b060c0601032a0b0d0915090507171e030c07180e010b15 60
    0x4c3c002d0214180e59200700785070409003c80400404851814900160803541c4500104040c4410f2400b5107000a1740232190543c4512195001074642c44080c00b58440d800b4139101a890500501d0001d82c5031110020302011309800980c1c880301001049d07002070301c2c201c0000411b5901d0900100014010b0404500d030b00b048410148249031078200641890001e40c0c0094819030001c51008208200007440900c25580280c411000740c0503d040000c42480b0103169104000c0111441e02c0005000c2e070803942c0030f401610000350145a983c4103035504140c84030b00034003048801c0c0313000118060000e1a680e00841c64205c0014071044028100300d8239480701d400c07030410041003036290803c0000041c01d5a05980e2081411140840c0004136890318504104d9207400c20b2040044407140052804000150750860100985000082ca2000d422103421442480d054000c0b82c81020030004480390b50b0f004844032000810820003103442542c04e02030030f03030700c1c0c0c1c0e20890f500c00020205074440107030020060000c0f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875939280 1250 875938030 875938051
    0x8030a1a01050a0c0c090204030609170903030a2f011e060b070201080606090a080f010f09020a050f0d2405090304060806060a030902090103030c050c0405040b1b0d020c0d02100b06030f 81
    0x44d071b07031440410141da205420403180c003504c8203120010408088680c0c81244c2c00c810b407841c20031b09000b010a95034080d50300580f040180b00c1c1c415010925404405094204d10600350b84c0d450840111000d01920300f98441c51589819031948120010b0188143d03425a01d4905059182c101d01e43c004568a10002d00380c00d50203081081011596a503511050300100807450142a10b5103040100500b103e00781006444000d041106003001a500c0040e0301c0e082d40d5003203c9001c100c0071081e01181f03800c80e040c04000c044641808141129028440142c41044003003c0184010b5a41050b160f0300e9000310300c95640441c0c000d4022034041d180440c05420301c3c0c081ca00d400583e0a405400099000b00203901c16030203d292056514140300050022401c05807081c4c074140b00728100703541c4281c0c06481c000c25aa00208401012030300c5502c6c040c04980300c400210006548550f1064046911000c452001201600c10030b0b554662060241c0104810070b4401052141150f407048142c030028640203002d00da88 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875940530 1250 875939280 875939303
    0x303070522080a020a0b090105070f060b03010906052a0d0506120106140a0b160204020a0c150605121506010c03030e010212150a030512090a08070308030a1a01050a0c 73
    0x1101c07410394418001e000c0d1030010605031a242c01840803880c3e164200c450241d9082007a5156660080300322160305070f001c90300e5214040c1c01e06210008150170043c86900d5402c0940780810b10155030002401507500814066003a1002496030025180d58540303458800024041452100082e50006904c4003019110010340c22100e12070342e003115200d41007090b0591a0002c0041d550038200103200241444140e241e140103400410a6610070b031031600244140d8001038030f00480d603c114030617501250b0002202c42824080c030614406011540a00782c00b51410118401c007845002440084e10141c59600c03400946035000111400c6010400070b800b0700d5290001c1d1440701034244001e0400d410300c00c0e4121481c0c01c12420390309907008040b01151148442080500100303070b02050140d808003010782070981d602214800b041c0507501e00e80c002150342c0075070f040000901001c1001544507000842c02000884030b64206000ca150f0304001190005a0500150300340c80e0156800c652105d000f424041036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875941780 1250 875940530 875940577
    0x70513020703090f06091d1e0901150e0405010f090812040c1a1206150f070c15080103062702010e18090a06150b0304241107110a0803030705 62
    0x80484d5158081d00002e00c0e0749604000040841889010b0b481a4405220803400d04560310484400010250010201e602000c22a51402540a000c9883d02160005040d5550302e000440c00d0300d00719810b54081d4200b0803100d00040c00c0c3e10502d9045584040514100086000003400c01c410040080b540e00040c90710100700b2031060701c10301000d01c0503036007440d41e00d03c4000e00d500c030030076000b802c6940140546068540310179a80c00c281c80440c40040c000e40d44480103410203003000d884e00d40c46010860003030b1010000055000c852141038038012030042c030201141c1080e80201d8000403010600074042c9202000066205450301d00700d081008182038401d13070110a0640320400180d5500c0a02d611818800041003000d015108040101e2941c000b203051501d05003000901c0020001006441144044e1031510104561070006040e03801c810400c101440c078501c000340e8025601504c0184c0e20002c0302c911490042003840507500c00e032001d1800c1d07884550b4123851503040b0105414141610456065 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875943030 1250 875941780 875941799
    0x1503360f1103010921020a030503011701062129270d0e0316030c090e030c060705040302090a0203061e060417031233012c1207051302070309 62
    0x100e0b5180a041c00d1700e001102d00b03803070000c1090110b45560540d08103800c0c0c0030100f0341000c00c1e6411141200d03801e00e242c24803031002500502968108001400c0c1000e8810400f9590400d20221984924514a1a18101c41e0b502c03007002c0e804450842c007140c0c004005020016400d03810000c0115000300ca180c500c2e0005880c074100b07108091200c0005d035104940344128a0104011001c03400c00d051940350040c1192103140c05030645000b55183c036a145c10580300c1401081084411000d01c41040c3c40315410181c0303001f0540d510510040c0e02c51817225010400c3c603c45482100e0140320014841c035240d414941d0b80104111402d580c5c240d2007c0305010000d220f000c081603403001094200044e5070f840c3d031441620452404007400501d000051545644200a20700441c1e00c40c2d6080440241c050b40140300041362004260b10400701c0c01006e4021150402000a1a80310b0b42e04e800c40d582401070308103200c0156500d0051103000d91040910f4210803c10303150b40d00901d451070080c6881c0030010740380c96804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875944280 1250 875943030 875943041
    0xa060c030e0f0c011d060711090105040e030414120a051f18020f0103110a031b02010606140c0304180b0a05060c070b07020315010602151003080a11071503360f110301 73
    0xe548e40c1c0d01001c034105240c40d05000f580d0141000b21010403130024849080c940d07074091030142e044d00c00d4038002640190342d50804602c4104800300e088890300582894001c2d1604d152602c2c644518400000091041c2114094042c495035545035204c40041c1d20703000c00403c8519042554107241da9050020483d0103a80300500c1d4a0303603551404105401d000c3c00e510b2480c3c2d0070030501001c41e4549034007840401c0e8407201032a01d0400c0070403810344441c250b000c2182140b0503540111032000c0e8010804c52171180d640c00c9500d400c4000c640b82030110b80e0712010301200b8030a40f030401c801508942014072002c44080c025200d0309001a04075000380750410b40d1244054000c2e00083c001d6406400c05903c044000417800790b1022250001004003491940c1d402d0031400707107089003814450300309141a0a45c008001c040c0c018450350a43c41000101b42d48090028002c0381090790f182c14400c0c2e40040101401c0140c00c1c0c22040c47c4d41065a102c80584406040340030140089800303810034822454295424003c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875945530 1250 875944280 875944283
    0x10120f05330708011a0a032c070e06151809010f080d0f1b05011b02061807120201030c030f2c060903090d0302030c3c0a0201030c0e030a060c030e0f0c011d0607 70
    0x221031030058888c80038503118083c2d200c110300803000f000700291a2281c00c03840c8034404501e80c8261702c07920345900100101710480003068102c0c50709000010a2503140411a088895040503102c0c4e08541100444410041028010120b01c5580301c2c114109050068882d0286c002d00000400010f5200d03071002e00000c0600f600d00613448030003807008104107416200c1a641860004043c0c0c94900040c1ea20401c074a03040203030500d690380c02d8846000340607030440600f5000d000800c10400102110744141d0b040707e180c98424018015441807101200002d1440c09000a4030056044c03a01110420011540c2c5000c00c50840c08140b00b080b80b40d2404000915001e420344141108503003d1051000500d0105421401d020390000e04200d5034280c0800c050030800c0e0203103404544a0300342c04064880b501c1c11000320341c040c0f01c1d1030002418002a940880d0361520195028002c0310500298941c0d0f594031000c0645098011b40120a007035801041500c1c4406519180f81c00240004400039005400c035240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875946780 1250 875945530 875945591
    0xa051303200f1005010b13140a030605070f0305070201020702010e060310030c0602062202090613020408030a03090b06040501150c1104060b1210120f05330708011a0a03 74
    0x410f08114060781c0a441e0141021500340da040c00491030140d074824040e44242c40141400b48400d00c03968540241d010003070b6410030004d0005080c841801800d60300e1b20780c0f00200092034000810401d07807040c02100c0f45160143e58000c131460078001042140d9001902202804d82e013908000f000588050480008180302d0f0041c001502c1c0015681111320806054441d404100b0059940180d90301c58480c1d03000507080e1900d101140c2e0b10b091110003841143c2280303503d4440400c1d102d030b5030b0794150024120507100d66501c003015210300c81400250f410a00441031007840f401c68843c03505100300da0b0f903038420780030700c000f10607103003104012408507807850f00040c0303114400090100d0400350380d48803540c0007080d003000c0b91051454210100e00c1c4118085000340341001c9545601d09001c0104000e0f035103072450a075030b404d4113100e4080c0070440321980c2c80c040e440c1420020002d4040c0b03000d07281c01c90407030304d864109500d04107000f001c0c00344540c054079904081c166640301c0d0720400107598078a44a088010701 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875948030 1250 875946780 875946793
    0xd1401030b09060103080414041d1609060501020d0507050106031a090d210b010e091003020a08030c030a0f020f070f061106040f03051e0f0904050a051303200f 70
    0xa0484071820001c040201d5a44103030b004100084804044070119074821030194100c0203481d00080c0500f40000c81440114800c005c501403228011882c12031450603442c90301e070065681d1200d0310a41c0c040d0301c903c601603040144207043c050701600041420700e02c11f6000103100d50701ca60701c001c4568503111156085101c40800c002a184003001428142c81703031410168100015802c0c1b0240411a48680c2c4d507406844000c4030010344d00030031809400d92401400c2040300d00c0d00240d0085010018401030703100781c4c007000000031640000701c100d82c010300c01c0101440c5031119101c01990350750b0b20980d62100314451a0049003450409001200241003000c1183d1800c0e498084002c00d903c1071803014a0403900701000348000a04068010000b466040c00c1a079205e140d10300e486a52003610310131180c69510000380401080c0ca14000074450618101c40c01c001036102c59401c1c500b00d50b800c4840002660412a554020034002c0059a42c00f0440802100f010300c00382080c941802101c403031141960344502c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875949280 1250 875948030 875948033
    0x40f0314030408091302190e030703060513020406060906050d2720030d08060d0314040b071a060904140102040b0c06010914070c110a03061415010e03070612020d140103 74
    0x700c1c0c80c010145c011841581803180303905144030020710719441c94041c041a01001c49060b10248440030046400200800031403920141d01159154900c0c0124415440e0010210b8914014103090080e0341881d41c070582000181038401c0000c00760f03051400940c8018a03489075081401200040801d40306076011b40ae10201c00c0110300342c5004441c180340c4260040402812083e070311018007544408201e51f1000000b0b45400c06840310b800110301802c3c200c02c005030110342840346000070502c25201d0500e60406001001780403250f0f203015500d00d80d10080c801c000c01c000c030321141c401d000811103203000103161036601c0084200399400183c03102c03200d40020300108030300f1030103200b160103c0a00c40104e10040c076007142d00400042c0248802400c0340e469000c0066242c0300c0c0d94520000d0f55006408121a4a910129100740300c0111080c95200c0c0440810071015440f4108030102e2120150050040c0ca007000d405403901c442e44103203501501c0d420701c105424490140500c031103900c2100f00012265045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875950530 1250 875949280 875949289
    0x2150105061e0f0d0c0c03020f030f030a091a01090f050f07020c010c050c1c1401060b0a03110708300c03040209070e090708060f0f0603040f031403040809 68
    0x59000038801ca50a002403010341810b00201c1c80188404821107580301501c26603801e1601850100aa04510300442109030036041201c01d0b03e450300076021681d0040042c00c00503960f1040e0048840c03100c07002c1c0003007001c0f4680364103d0714599201c2d4501f51101242c0c021310031b104c424243c1c41280c0710360300c036059441003c2c62032048603000002c1c5088107280b8948404080d607190810503074281085a902104030a0003801d010062500300c0041c90000d82a0340447c01080d541040da1091f110390144030900b0040036414440c03442280c0034803500c1401d0051031001640203148501c8410340c2c4e15002c0204600143c07100e401082a2040c032100d1541c03005102c40c40000c400084e03010a500141a1400e0010300e01d6014292507215504840c0c00035555500c04089811a08418056410200d45400d004000342c2001c0b40300e02c50441900d40c0110035140d542041200d100300c61034140c001c10100082400300d481f00c0014207401d800303801c1110720404103483d444041c0c0d200b00c170107880480010a0040045c40c1c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875951780 1250 875950530 875950573
    0x1030b15090418050d1710030206490204050f0d0f06020d0912110d110f031605070f0b070f020a120c0509060d150b01030213090b03010609050c1614070305011508150a11070b0702 78
    0xbc10410440c1002c4c28007000c603006600400c0002d1003001101062010001c3e480382c50000ca551043c02551902d5101c1d110300042c0c03180b02c404680404607a0003c000c0903202e0750320311840100c0c02c030041c000d958400400351509111040e403180240214580d003018008108020184000800c1c61030b104500a4142541006e1050304180c00c80140180104081003040080d5407200e908136846a000403014400640d0344a0550310241840f05800a03210601c44140c60003401c0318130a82d0555420b41ea55410003094803005c05005140000c5100c007548044099400340303000c00c00c1030400510b00b100403a40203034006480c1e4420403610783c49900b081480d04081c01340030020694040d0a210b03605284020111078003501407000109641d15030100c0900050580544d040490a0256807515440341010b03400b03000329500c01407c8864980c0d0019050f40001990500f17007280c2d0312400c1840d105c85c042c0d4800340c14907020044500301c0901c40300010585c03194070b40d4011800360b00100b001d01c4d140c0d240c04242c002d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875953030 1250 875951780 875951917
    0x30506070806010203040b0f130315141b0c0106210606060504031707020a032307080c0102190c05060f0a02060601030b15090418050d1710030206 64
    0x1215051107000d980002c146d4040d203d41040701d5071030702030400c070b800d1040c028404030300c0380303500e0480700002804041c440e03a81da100341c811401c0c42405504002d4462108080c0c0741d0048441c05d0307103441a525450388001e05001090600003040f100d9407a0714440120500100c20600ba5021800070010400340b881040014482414141c1c20245152501200300c894001c1007a2021000203054007150303505c1d107a04000d581d2005e060005030381ca442c101003004a1071040f8a020f846a60404a510344001510582c4964143e0080c15030207868400002c640b60505400c60f41501c81c0040800c85948180290012403844440d00380c0702c44121000a10704603010300301c20706061130845003000076210300c1c282e6940c84a1032910543c1c2c405299004c100200200c0000d00309a66030a55080304010010801459290082c1e135400c05202705041c043c2d40700801030340d4040c02590720641c1003006044ca0780c0a4100150b0f480f00d5400d0b98010000c1e15111000d103c8581e81000c540c4522000081035030400506500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875954280 1250 875953030 875953037
    0x7210302031e0103051f150303020d03150e161419081e0123120a02040c170105010320160c090c1d15040b03040209010e040b06010e01230403050607 65
    0x55146885181d200d5001c40300044031402c115103030310070031b89294201c020b000d0000550900c40c19904d0400079120603c2188140009040910300e40d1800e000b200002c06440a00104841644903038210010301119000d0304014401c82c80c202c2218880704c0d030046e001e21404100342d40c40c400005040140603501c01130007070300b13400308101c02980c1260b4540343c0c05040d0382d002e103900054a140c0c140030030700c11a801c5060302c1d4040004415042d0010010078071080700e42c0f0a607020f0080400c42c04059802000070500d580c5c1030204180104510740c404d80000d0b0511244250511001a8003401e4585650102d20140c5401d03a01d0181d038010044034a02600c0145503138003007000649454100100b1044c090002300071505c610195003000b0359901150010442c07040c920031130761070341c0d111030f43c010640080320203900c03840140000003250b610071074041d4441e950007440c01d000e680e1030900650f500c0c800018141c2c100888002113180640e161043c0c120642c2141c0070258a841c9107142103490600000c1148040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875955530 1250 875954280 875954341
    0x1031101080f0a0e1618050a05060616021c0f0c060e0a09051b070c0812120a02130f12140c0306010506030903120a0519050118020721030203 62
    0x8044000b0380d040e401c540040d2011407042160388100c3d1419070003c40344840c0c40080c80300051011500c0001c6662a183c1030400d0003c3c2c2e8034400c0c14070480c0c0b0102c07031036508524100400f0340240d400307400001d402880104070b40c012610b0403001c041d02c1950400e017150104400340f03000d0144002c0b00e11031401070850b403500800700d00845000c1500c0004d548101110355407644081072200300e0b00360901c5031809000d004151500040d08003498400118452120340e4050007290b0010181031008484003604400c2191b1a45e0b00c4a0000500039484460809241e1020940226120b400c403404072000305960429080d03007209038200943e913001d02e2506038a0321380c0b00d0315040345030762004540740341100c00403100e0302d0300c0366144e246036410361092000900c03482402000300006401242d012030b000d16000a5403840401816002c001210002e02984203072811281c0700c0103100c0140d40080501c648101c8403890b01d05039814402125690400c0510042500032041044000c10f85540459441c445c81c041c144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875956780 1250 875955530 875955541
    0x3110703030608160b18040605030d02250602061618060530070c031b031d09090c0f0a08120711240a0504030f1110032d14010e0103110108 61
    0xf1180f00722604206c0c43e0441c906404601d40e25580040020f140c040c0640d5041c40318413400a40743c05404043c80d950b04100c01c5000c41d5011402141d20503200c0c2c9800810058440380100020711445545010400c00c00b5111020412303201302d0624000c060b0381c1c03121a15031416114002260074200080b42c48091485403280d0b01c95080890550400c0303850402c07142041243c1411590f901c540340c00c036401184007000d0b040070554015280c0c510600740244400c0004418020811485000d40e40d14600f0b60120070601e41c0c4d45400c06210b6030fa08002440151072503980c0c000c490608020307a500450189003c1745e2101840700c0c3d51700d00e41c0c01100494043d09020700f6007c48204c141003004500305291000701e9682c44d02401441100c1c0955040144940707090802d18000c0e04604120f0b01050043d145410000c071440d02900440f4040d2548100c0403510407804091503180c40a601c907030765080e0340c0f140c01d040254264014501d000c0c040b0000d07034010079030450401c20040c142402c10a0304004a0104000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875958030 1250 875956780 875956799
    0x915070f12210e0c220c0c1110180902040e0a11030712110c0d0e100f080c0d05012d0308090105031308030901142508070311070303060816 61
    0x4190341c00000001480810f1400c15071038040c0c084699500010104600940c003001d129102e2013102c4909130030700007030000800480c1c082413401e01c01001e01e45d004d091310605280011500e032204c545450f10550107491403503200300b0380300c0c25484051072aa0000d02480b1403160205090f901c0400303048144401d0301064040c1c211444020440f4041010180440c0075003405604440d0401801e240340b075443e44407000d40d079034985035a40b002c2d0f00820040443e51050381810b21410340d87d1b00141e140ca0351000d1280b0b40070354401c1d000425040e0808070400c14242c0d00400e40c824036020b0881c1d10302c001240b14051100c00c45040070b4a441c0d508a4000e07030801c100094100c01200c2145400703207045a00c0c0c0e20b4ad40e05100c001c000000b801052400c0c04410410310036415481042e0036119000750b40555207503220300c00b070009102840909000440c034110f940307450050841c0c6411001a00c0c00240420391f010401c030750740d00b00c0002100003075120a810445050204285168000c86549094156141c0b03170030351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875959280 1250 875958030 875958077
    0x10c080a12060e06041a0a0614220611120d0c0c02030a112d0603130605011202040e01140417070203101401060203070f06020915070f12 60
    0x2401210002200c04a041c410006a00903008111040c44100d84881c00c000c5445401c9901c0da0060385088040c000350070843d03029521926010340090000c81c10b00204940d030164810f031400c4855010004541aa14603461100380c402807004900310384c81c1048001000c1221890b40760400d540700603140480e2500030405c940403820031000004101c1d8032800c0540b00302c4080c810181d032500514000005020a401c5402d18824044442c03441400c0000b44100c101e1510040e4115220fa50906041c11820004001d52308852840800c40720031005585820640e5802d07040846039203010703904c460840c00c2a000760300c10b4510710743c001d011a00c0c540c9040201070400800144c41c0800704180b000c590201c0c07001311440303e50060b00342c0f40205141220700c8040c25a0304541c1501e14000d20001844900c00f2003034420b456804042c1d50f010390495143c10000c4e40104400320350080b02111203644010950703004150042c441c4015030650f02040c100400403402c601285010302102c8404580c2c90401c0c000f5a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875960530 1250 875959280 875959283
    0x3080706020c0106060f2a1406090f07060c0204021b1002042112230c03032e0b13050d05010b010f02061b030a02090901031b050f0108010b070510021306031109010c 72
    0x10242d07c024505c1c80c00da41c0c8001003018107003220240201c500884007103a81880b64414104950042210006072a0381d41414454800022031f208858001032921b50020f02003c002c0032019403064901100280c14140000c04d001c100c10f600103000c00111203041c0c03441001518042d620743c0840c8443c0c440b1580c202400c042c0000b00052410a5a8180a00e440c06a50b540710403054941720780030941a603951f40c0c003d0350240c561890000c2c94a40c1e1502c1107003c00c40e0079407100d0789000007511700390a0b2111a0040690b075207407420307403c00c08280c42e100c3c902c0c910041805500041281000c480001d020344d0354480140046400c5401000b6079452003600507080c81008164455a0b03951380807851009029803104180d0004c60707440000240b20106851a041944104020051a0f80d507820412400007003d141030204000c1401005441c88150103000000d01903003d40b0718403181d1603004003ca07030188002d0700e106400c508050000d19414030464030035051403050300385070000c040006400344019050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875961780 1250 875960530 875960567
    0x3020f030403081308130617010311090c04150914181302030109021008070206093c070e010f170c0f03070f0e15061305041503080706020c0106060f 65
    0x11540f192415541c04051517081100c0d42c0d00e0b4400844d40c5680c04401d1310408000541e240140350b51200d580c0c600a0481ea802042a82540049014071240c108028545d08400c0c0051100003815600c0b0f14811035010310542e5183d45072410b050700c0701da8032682e00c5100ba000303043c4603464140042d800d904943d001000c00d01303451040c50300c07480081e001d0500d002c2d0003900822100740b00420140c00035550350144985809555440d901d0800c00d40c6c0d1016400c1040c0c0381090202840c07201d180180d107a0100d0744a10b25190780e081a10912030f1072411400e40d0114811442100c01013103840300c00000740e000303403034030004c10b0b0a5014003c2c015591000011703000c91243c40303205105800c84c0e030200500c40060104825070f00030596650f102c3e2801c107100310b8003400c1c01c00c2480d0385141946027140c1203628510000442e903c096080500380401024170300d146822802c000c2c4408400704000d4809401900e01c54071015940383e003207803442030940c0e586a0009040c01210341401008075004941016107034080c09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875963030 1250 875961780 875961797
    0x1612030210021806070807030f110615040f2405030313050f0f0a09020d140f04060c02010b0607051c0302121b041a0d0c050405210c03190b060103020f030403 69
    0x16250504203800c1c3c4220b648400c000904508002d65840034010b414066145e00407400d00d500340c01c0c0c0e4240740a04448469402070000907120304d2450305030b0711420401034000124181c9000030341c0100e03200b1580c80300c201412a585129903400c0009410007030001a005542444402c1c440780d004d201040c021280300b54002100e9030303820b8440503403070a5145001048292010759414100b0001d61200320040740c40e84c1414176100120355500e40c00e43c0244800d428070211030f5983d0f00c2d040010074103c40c50f0300442d503c5108142c42c69448001404503140120301500d05400c15840c904200c480c1603010380d0034140140325032814102c6048005d603004050400800080d0140c034150b14052056400c0310000c0c00c003c107490200003119201800040000341c1003080903c0c1e01900c02c0e1120f020300d00c40d50b5400341007400d540011410202400190030201012100b4843c09017000070700327041075180c0624120700001529802d1129910607030350040344c28202189045140076003900d06200060002e0184440c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875964280 1250 875963030 875963047
    0x1c021018060e0f060f030406230403032f0408100507050712030e0307060b030c01110c040e010603150e0d090617041b090b040605041811130608161203021002 69
    0x142e07410f81250081c030217651202001c296071440d810039141992000e00d050812460f003850b000484400140000400c10165181e95044024101003c00e46504000c220003072000c0d91500d84c200030020f0f00d86070083c0e46950030100341c0b07803920f00031007c0a0b107014200340502c0004e5401008403208941c00c500070907200c0082d22000e0340600240c9001d00078a120014856050010b42c1d03018401008049094900c40c40ba00001140d884c410b040c400d032000e40044000091514065018903081c1281e00001700c0c150340c1e02c3e00c81d00401c4140900041025898001c00d0124044c00d122903161302c4038074245058075506040c030041040d615507031a41c5101c0030300004542802503182009802d242628a103c8405407102c0b84140075007181d0b0441e5010314200540455145454043c0d880c1d060708402140b1000c404035104d005004552010098025600408104410205018440c00380620400904100c0c80482180d0a000c01c1d0354002140002c1407072a5900096005c60240c0f101d0081e004090707221030b800c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875965530 1250 875964280 875964289
    0x11040c02061b161e1e05061503120403150606080106020a020105030c090907031a010207140f060c0a12080c03060d061a030706030911091006110a021c021018060e 71
    0x90000b07410444100783c01080310099100001201d0312071701d052410101d118040c955085000c20008240303400c1300700090b48203008440c51031019a4002d08442161414000a0419510a800940f104658507000c980b801449004e1300c0018010b81c580003100e0b40c0f40810094030b600b858075000b0704105e00003000c100f08207225029107112080081440c105410700f000c01a0003006455030a0203002040c1c64a41515800481c402084981d0030404124040700c01c0100329a800c041440d540d4010014090240408030802040c9822442003240a0b049652040007810480c401040c0128004080041140c10340315895014002c1d940a000420060600a1070700041681d2083c003d415201e1444001101e81d41a0040c660240c050b0503a4041c001044080c03040c4450100c03545031803894210410458507106030b030300d5100c510000301540c444040c0c0d81d001580c407200c0f00e01c01c0f000c00c286850302d51003949000c00b02d00f06038205a081082030504420a80e08000103d48124814030a0301c072001c106035186d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875966780 1250 875965530 875965567
    0x6120302060c0706060f080c0a17031e07061d060a0c0c02060a02070333060501050a110106030b0a060612051501200a050304060f03090c0510110a11040c02061b 70
    0x41d41030380c80d0070391695541503a44001098151040300c1e8070600243d54540c0e2b0716440c0066034480c014601c0c01c07201d0410100403074445156030110310410444200800d03418401d540440c804041d4182000c21507529251900e0006050610202e140c04002c0c0e8210760000003800c07060390705071415501c40790280307802e03030400d48a03500281c0040080380c003041400f00214002d40c102d55080b20403d00d07988120724403400f182d043c2e0240c1d03030102d04100300c06551103000314900d40500340780c20008140c9581380da60f450030403081610101100f50729400140113103600410001061131154004225625100714100101000e0600690500c00c030400c00c244403010110101081000f000b0842700f0310140752a00c1d951341d80c094490040040c6401440025092080c0074000e02e0582241e02000c07164144400c00c01d400000050000c00c0c09074013020380c2c3c41e40405008400c40d00c0d0042e40d00112100014007448103a9002c046070340308540100d8104123000d8408000300e018128000d030415101e0050380c400441009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875968030 1250 875966780 875966789
    0x1051305091009020d3008040506060d080409020c071401020312010504020c0708010203042a0b03150d020d06050f01120507090b04110339090d03120f09020406120302060c070606 78
    0x80100344070315031054040286c61000e6800150380c0798940800ca0f1641000daa0081030350300a840403480c1441c05e811690300e490300541c4030b240f6003640e424031981240d102029103103194009030310400914041280b14005007000b030000c1c518218001c101009808014007600d40702d66400700e02c1c04020a000c109180103080d04900840d40e9051904107510407000201c7c107280592505040d269040c86078601240844090030003a84c21910354a60001c484038016801035000740760640c080700540c0c0da0406140c90240130b04000280d908107008901020241600801c041c0c2c80c1083c03440700007030400541d020854900810002d1f080200800240140c0440c0300d00000d01240032043c01300200300c4000c1420255804034016041c900e400a4204640ca038281034816003203c14400d03500f003814100b06081445100b071510024000c0d40340380180803562a0b2034a00e6890341d5651a000450401c1c1c07007503402a1031801b2682d62900c00a55000355034001c001d01e440009113001c5090400c1000e01e030481e40151 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875969280 1250 875968030 875968043
    0x160b0d1a04060f08070524090d0b07120c020f03040b090402160b07081311010f09080609030c06011d0705180d030503070e101b21020601051305091009020d 68
    0x542d1482020340000050242c1308036401000d00005091902e070300c188100f03803050b00c1c0b40c02c19501c0c1c00003080d2080d0014604540c000d4208443c03280003408050744d40f4402c403015298880740820303000121080310400c2000e101554410320b110117000800000b5103080343d0009942581c2c40e51480041806030081d45035042050050000c0841007000a4030424031611081d0f48640c1300f9510200b000c0c081c0740090002410b0780840341314050482d485030107000310302021418100c50780c0c1d90342d1107003034502031302111071401907000410a5020780200388251401885800a0510002d03280d019a521407003015184000340880000c1000103580c1004850040d44c00003810844541010700740a05070354012039401c3c000400074103204c0701c0c070b141040c043d00c05400c0d03e07941d4400711070080603510811560300800b56088001a00c1c01499480450144070701c24059030b024100c503501d000c0a0101841d031416030358005d10f0522041042d85038000501804401d1040000f00700d041d101e001050b0080030203000540300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875970530 1250 875969280 875969291
    0x60912100609020901080c09060906030727061103030405030307360315140a0515040603120e01020318010f0c140d0912020307151e11160b0d1a04 64
    0x40382c030a94084c0c40349072403c0e00e80503042d82d600075000049100e9840daa9a01c90000d00c14a5501d0038032402566005440b4200208150f1407414a9400310441c10b5403070041040803a402e10115500c40c3c1c3d81a05030709040000e5041d8101580c840e07403640001090341c81000b554401415081c02030007100503007081180c01141181c8500f072032610070303007006000c15504180b592034045032a803028861440c0c84041040741e031149459594403840513002c0501b4844a401ca0b18440624075941c1c0e1003507100443c4111019042119410b03405000c0244844955040d5003050119427207403501300c5a02144d9001c240f8000c07106200d600c1d41a0f400c000304ac2c5000c1c04000c500d882c80b4071169400202c100c000007640d11a40c050640d10400005001c0b00c13000c0003505034010220030003805000e0481d0301d21003021420011005c080703260404521050040404000a2140512003401c02090201148508500c503580509a0801000910700d2107001d0582c0034555880952801c0451009524003011200600c14002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875971780 1250 875970530 875970539
    0x90804030305030f0f13020162010e090a0812060a09020a0c020f040e0d020a0b060f0915040f0c091e0501020a0b0c04051809011a0609121006 62
    0x11035001156420300c0c3d5081140418a90356180d40c0c407510071415610080c02806c22a401116410900141d510a01c100200002c0b13038005108a40c290581480700d00d6055998000c01800c1811011004400d0900031010b140c3e4030303441c490001d00d0640d0014520250700d03459403814103150503007940001d46403000c0071034900004145030410030b015210440710f0220031516164200202d102d00d80c1047c0115101e084000010708101080003943c00780200005110720883c030466040c50303840c118000058110829580800819409064200b041a28030703070b002c62101008943c4050001c0c2c83c01000700360072100c0e071a660b070340c0350082c912005024a06118061602d00d01506c1302000780154115400d4030300390b102e104c0202c0d10944045070b8050b4020454060aa100d407500b03440301821460781d224041002060580716444850b000081d81039001c5014506032046c00e085a031302c14848881c1f43d01c0e04801207155a5081c01b0364000401c01c0700e05c4c14040c100000d61920305201c800322003480601303000f000a03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875973030 1250 875971780 875971787
    0x7080102030c0d0b0108060604150207170f1510060804020d0219060e060c150403020a06060e01050f030d0f0f091e090c0809060a0902040207061e0608030708120a0908040303 76
    0x1403243c4002010320100c58440c0054800050403500f480e00000d05201c00c00841d03120030481c81d0741c1c0f80140160b6084988591401d100004445180c88040d48280c00622100b0f07000c200208040869601c1e0b0b240da070900065900c00e085503441108100203408000c01c05542c1d5001c41d90003803560043c40d44170409030000f4071100260851251a01043c52415aa906800e021045420001400020305240305041f00341a0640101401c2503085118001741080028402d1241a0141090b15000c160320762501d41041501003100804500a80240182c0340e1256001081107907040010308080280060000c4116454441030b407205a2401030a01d201040f2920781000009441c0203003010300000384001c0c03061729819402c0e074114269600c40340018a0004080e40b010755403a20007400903103491130a4441308151504400031741c035010080012082c4100c0d140c8609030007400000c0103903003400540d0310b500e0742e28007404100003845030b41c000000e09403501039440400102e41c00b440c0346440725141d04008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875974280 1250 875973030 875973037
    0xb06030906090714010503040b1003052401050a051804080f07030305010311030705090c0d1b120e0c061c09170d0501080c06030402060a121b1205151207080102030c 72
    0x742c0c0a0089060101e482c2c4285003c03048402c0e81a150680f03107803100c1e41c075041c44400040000c2e549081601011001070300a01c060341c01401c8542c0004031446c034030882e049440006070301c414800c038980c5504000c2034a03180064a02d200c0c0d81c10030045681e80d2400c00002c18840c0510310000c0000015004003010340652229041c0d0b802a04c03c2030b030015625007490382e45c01c210700806038040c0002c40080c0842c41d22000074180c10288250115666240311800d8501d06445150300c808a0405520400b00304000d2048120345e4941c50000c0c0322281090b0701049081c401c02101d04403c001d401802800300c2d0480e0421060b580c0e0007005283c40c0c00200c0b0805105400c644a8200391f9405e000000501c0c10700080d28110ba148020803440c42c54503140c2c200051544a039400005001c482000207890205506c0740b0000d4256115401d25010f0348554014102264403801c0d000140ca00402e201c020b20b498500c241c1d0391310341590141c4034446200340740751400510780d02c00c0c12a5030000080040c95075600016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875975530 1250 875974280 875974291
    0x24020a06060f031703041a090c0406060f0e0d110d08130914160212090f0d080a11011e020f04030f1a01080c0907050a21050915040f030509040b06030906 67
    0x32131908990b001050b91407440103480c040c09400090300e030343d0340c1250740d90002034102080908460000c0003c0d070120b070580382240d103c00003007681c10105600240c0c0002b00c4000c01d00382116030907402e408998031b1541e41c808041c0340c1d134001c02181041a04010010301120804e054030600b002803280c1d112505030180c0110b0450f00c8100c00518080384c03031110303c020240240315480d00030340813041840c8030300b0b12960045c0203480e03032046c1d401d680652541c640ca014881002e0050720100c1d40c804142901400c0380c011400101c510340c0c0740540303030319506002e14070180001311601009a40c94014001c1c07804240140e40016100f00280045841002440c407240d5880004c42480c0490030782c0c0e5680750325114100e4030b2490790820307201d0700041c2c0100c2c0725900030010300c015410304841038400215100620615841704003042951a4140016460304000c6006060140304003103101f490580d440c0120744007a01c1c4018140030740442d8038881c6644542001e45442c4016100646074a450006580d856209440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875976780 1250 875975530 875975543
    0x1920061017030705060109050a021902010c020d05180d051e010207020102011512060b1210151a040909060f020a050a030e0c2206051809010501050a24020a06060f03 72
    0x540d60000403002c01512896900880500362503860900b2042c05044020f101c41c000720345c01c21162860b8042d0303800c2c0c401e9000a036400003d0040c24040064035021000c2103800a01005002070003203440800c15445070f040007074401c0c5803074004c5490f2030740c5022600d040c0c10700c04c0c07950711541a010240540c0174005080c000d078001c0c00121174030080d006402e0841d008842608403a05160030200340c4940051070400070280c040907030101c01e4141241802010391100c03c48645480c919012035024031100c1c0003400108000060501c0c84070204c41c09441a84103032000240c680300f1603024083d00f07a12034010324000d01c070255a544000c1030300030308a5010b4145413012a290a0800d98041000940040c0014001c1c040407411502038480302e000108000510000e40c0d110000030510303880b00c01c0300007106c050707401c940308490030041c0215094074016049180070300060003040000d1461140c0d442e14400c8090300001410001d61400c90409074030a001420150900100107051980f00501c0c00840f0301420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875978030 1250 875976780 875976809
    0x9030c0c0f0e011401170a020406080c09210703020a0605070308150a05190503251203080c070f1719030509030909060d0605090105060901090219200610 67
    0x3030310705610311514065a040b4564480c01030040c0b1406403024001070328141060902001801510180a10102c495a03070305a0003180030001d0a0b0400032a0760416070300f005070703410800060049405140c032100f40781903143c000094088001c000f44003910140d90041c0624103070701d448800103402d643c4004021000134000078001982c924000d0540e4440140080c00140c02c0b519060801242c0000407004501c440105c00c0009100c2da010402100d03d0b90415440500c00084281443c51500141d80705045070b0080c03003000d9000950020115520002d1156540d03190000790402d8243d018030204010808605521561030801c0c059001e020304284424184e02d0241c0410401ca00b03444041c0c50f103c4113035009006d5145c19143c02c0c101151b00c06c2003e4131000d40fa90041d1502c00030745105030b4080c58107942d1007007480420308101803110302403d015041945807001550700c056496240c110f00c0c004200c000101c801021490716100c401e0b5a9001040750303418140103030100c0d0f92074520300c40c00c2c01114408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875979280 1250 875978030 875978039
    0x3061d06012c0117270f030310030c080607050724020d0e012f07080c060a020702030c0406051c0c050d080903011a090103031202190c020a090b060a2109030c0c 70
    0x80850300c100d0a1410070190030102c6105c01c1041c0e0110b84504c20980116200c01c95118402c00155205102c01410300702020715600700451220300c6034000d910700c0d8000204015060350401c1c01c0310501a485081105840c0640546800302155082c3e44451a400020f100b060031101c0e8204010000c2c08000810000c410342e482040424020449444421454900d10380404055000f40c03604038041ca01103840c1c1080040201d003454400c4400c1944d40c1d40c00b03d940002e604040001d04880c3d00152803c0081d9418100007a034910710940190984c0c5040c0c09011003044030100d80c2e1402080041d0109400d007015103041030b100d800c4071005a000e50300e07201c02e422401000340c040710303440e58003d000100c030769003151000c0307449070b00c984280c0c03810b075400304801c0e00e00820014481800d500181e0720788604110610400c00c804041c3c0d4007844210b4188186901c40e035039050704030341c2400001d061100e0600400380c94040d501018001c0c80c3c800e24a0031403414181030b00070707000301c0c0301c40d10a82c041074525850303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875980530 1250 875979280 875979317
    0x1060b030708070203390313090b210601060f0318020409051203130204050a020306090408160b04030504080105090601240e06211e010509060f030706050c070603061d06012c01 77
    0x9485041050728400b600420070411107900ac404548005840303006c001001154580110801c0140f8000580c0300600400016130f2100c0c1c1800b241d402c0b450248106140741c16003801e07899444030040e01c215681c0c1441d90400c01c4c100444840e0800c0b040b280c03a121301c1c2a903c200407801c200801030b8040d50401c0f000a1015a032071003102e00c2108000e0000c8010b4849444040030f40d08152400c10341d061414100502040004030810b01c280d00c26a0f0f080d50f500d0034800c0c00d6080d03c0d80a40402c40303d500002c01803120f03000044070301442903c058034038806441c0b00101118049505240160042c0b40080d49440780c0f40400d05140391807100601c6400c0300d881e41582c00c0241801c0340d491042118000c4018010b9182c40405c140d00003e0040c1a51040742e0040002410030840b81e000d4800714000280c2c6a052400c207120307560003001c2d582002c11007245062581c18810020032a680d006e68003c81c000354450b070240301d100264020768585c412500822400c002420300c0d119a4881c0495003402060329800a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875981780 1250 875980530 875980537
    0xe0d090f0e07050f12010e0a06212a170d08010317070f060c02010c020712030203041806030510020403150509032a2a0301060b0307080702033903 64
    0x8903008141a0b42d50301c2d0000ca85030740141180305001801081800d40c0c050907010300c54041e140303400f5030000b06d0510508030021201507900c001070060301c003500c0e102c075080316a440800c05604031880724068081401d10b643c3e102c000b51030303508901e00b610402044012881c1c500d03810003440041180c84981c020081038a0b060024800201030040c0c5050002ca0341c1d1302e000c00341146920034891003c0c550b083c1d90300c1400791100100e150703005039561900340345500d40c10000c02c001446c00f180c402c42100b400d07813402516440340c0d0041e18001000e8040c011203122080e48180300544d006400c1e41c04407002d0701c081c080030b50f004c3d10066940c1e110030402c1011a00c91031103824001e000c000004c40c40c10768041c102000d013004100c4284003005a1404401d82c800e001d1045c02001203407134041451443d0088518040b001745600750303a001e44e15001050010002c0c03a0200c9400640608140d4026030f1030388422851441100042c042d8450b4185a01c462440c03104040c0c1e40c9034000c003e4404038000c810400c11382e80e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875983030 1250 875981780 875981789
    0xb03090d020118030f170a0212181e0a02210c042a092403060b031618050a03081206010215060609040f060807080f010606020d0f020f010e0d090f 64
    0x1031030f800c1c00b00c002402000780c80484050f81c2040076000c60300d8882d2614000085600e214100d80004d102d00c1c001c513038002602e502404110180f400480044813156450035486070500d04030074110b040e0b00e1400c404100512a039540240740940502c40c100001082c0c50108042e604240b10b6952100110b18050085582c001c011a5200e50503403003400c04072800700c25254880007070002c50f000224035070300c00c2c018440701d0040301070700b540540c2c140e000000e04942c0c86500090741c1e0082881070160642000d0b40d110f174058007c4c90f28140018280d111210400000d51000754441030b003960003c10003080402604411212280c0701500307a88074001aa2282501070000e942c00e034100001030082c1c134040000d880050000f0740300282d00d54104140c81c4c1224001e8102d081c40e82d00158041182ca00b00f0000b880b00300441d40001d12403546450b602a5480a4016001040c420408900c108582c400c11511500804410003030000356030001c0020f1711002c043c0060310020f50074071800704004910004090898 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875984280 1250 875983030 875983061
    0x1504031709190e04080d0f0e011b0804080d020915130603050106020a0209180106080109050f060c0c07050f0409021905090a02040602072108040f06080a05070807030e010b0a0b03090d0201 82
    0x5680c4c550b41c4a5066004000404d8502e60f5012565190388291107485085003000d800012800070700b04c0314116040243c0c520b182048003180401c4000f444150543d0303006054048090f848944003000149606940c68194585407004034092268130b84010307000007200c400344c500708004d0343c0b40e000070be0700c59460b2000079400003209408640d59107005041146030381c511100005a25840d00d80850940782e49020544683c0c0c00780000d80c0752043c007030003815082502c013040b980c0b07850040485e00d5201c0089202d024840e025000030900c0380e8981d600455000340e80288a00050300e2100c0981202c500c59000d414003035032078080020502d1090b40f085030107650ac03540081200a10b451481100c2c1c1070040c0c1c00f49150150240d1400c0040c01c000098005455542c82085040d070400a00401070003005000f80321503420181802803043c1c211380b1558000b80c0c24503011a5800c4035044c0310b07014028400d510f980060b1194400100f540c052030146001e03010040540c2d414203a882001c03400d940329918100c501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875985530 1250 875984280 875984309
    0x506040e0309010f091a1210150807120203011e1a09150705010501030c0e0705040f140406050a0603090b15010912150501090204090c0f080105150403170919 69
    0x1c0b98011000140c40c0300075480c1c02d00c8015100c2e0940030780502071b602001c10a0b400495620050510a02410780c42031607010705608a6191110142c80d200b050848007084c010000b000c034010520400301e0b91244c0400242c250750341e50b500c0b02030a0501048821520041e4101000841d0001c0c5e40e80c20302ca0b2441c0c0010901d818503010400300301ca190014103003050607010401c40308000030000c1c02442c0c001d502501414400518105a0000c03600b00105600100b1a013004213102a504458440040e00c0ca25101c0000128960011800a000581249130320180c0c030040066a194580c1050255500c60110b5000130b8403400d400d00940a8414500350120f011031b9018822050703003481e26081203025401090100940d5158941100e00a0300040c00b80ba0300000c040c4507801d100d00508888900794a04414641c41022004064040601410380300e4840c00340c0300d515022818055401654214019454032150407140c14a2680680c80040c000d21209010b80a2029035500013000c550024103243c51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875986780 1250 875985530 875985547
    0xf0c06030a022d0a090b0c0d11010209031002030604060f030f0222020c0d1b030e190f1514070503040e220507050915030a1707020607150506040e03 65
    0x10f900000c40d9101410500b601c01c005030f00d41c0c2c2501507800d124010303680b55075005040c40201080380b2030b0455151a4010419800801c500003030301000c1441500d05641440c0080701000c0c0a071160600ba950f05203d91500c070342d840070040c4c8c01036020f80f5046030b003041560f45e54000342c0d00b90b404a1102500401a400c1c03840c0240c01c1078009071a2841c0249000110141040c3c030620881c0c10007142c0f02e1040e8402c0409802454100340e9210b032075080b0341c0300801d5040f00d51b5001001c0c0c03500c0b1407a2030300036199528070031030b80414841c190b805009024801c0365003e0700c4003081c1c10443e101c1074402e4002011421707030100201800d03003203c55503500b02014500d8603083c03103c2c0c0082078401504021001003c00528107005031150500b0b86060b120b040a000043e14220400480c200060980712000c024000800602e41d400240320040345e51140b84203040c1c2c4d00701c0c000d444080c000c0e25006504208002411401c0001c1c40d1588104000400c1c4104113944402051208484d02c0c1c0b11440c1503070707004200301503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875988030 1250 875986780 875986801
    0x602030d05070c17041401080c0706090302100204080c10090e0a0b01091a0a030b010503070c030804080d11070303200703031a040e030c060108010c1b082502030f0c0603 74
    0x2540b0150078180200e0301030203596a19192000da14002515510215083c8020307222001c02140f4a03009103805019801e100d1602450745c0304500b0000d001d261703105050b10406009200c42007040807200d030215162a91021607a40701c00c40c54038204d03c194030700100352102c42d0082c0c4c0824180d648641c0701c07001c8c50b03854942d5000100035003205d40d41400000c0100060940c90703e000b80e0b1610309024441d50325540c4480028040e10292085a41408428400c00180d9503002da14803514503054942a600741d00c2d0760400c2c0c001d51103a803030240c0081d030500315812910180600207011891296404014180d000c84050f400c0e9000600c080610340700403c1182e0111f0321a401420120317190151001030b07050b01c400018100d910b040410300040e000410b1200c031216081c00135a0051495000030700c903d00c03003070000506c081d405010680a0103040300030716081c4910303132059400c96003400b4142154a030740700000003c0c003410080102d11a10030144070715903058003c03c1e4004402c80140c117183c03c50301c41800341c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875989280 1250 875988030 875988041
    0x3030b1f050c190809040c171504110406200a200612040308011e030c031b030524161d010e0d06020d110a1d040902130608160602030d 59
    0x4440c911440f502062540051008495001c2c400d195181d941c0805605000c16100740d48909410700100001448000d207100c8445540708480a4000310b16880d000000340003030400c0d4084800d1100041000714009410282c03080360241c0071010b0b03403443c080c86150f241e59040059401046003075101b07038243c0c03000c40d0310300355080e907420003088582044440b0201034192801181c095000414a10040190760b010000d1414204140195006524150388403812000d0036844020904900d9050800c030000352411101c000d075910200b56207030402078040314080a5a4180360a600c0440303500481c42e006100040d00d46681c101d9160306890800b8151074503180741655440d5414401c0c00c5100d490160b440300c1034000b4240c4280d10050b210f00102020300107e650402440ea5488401c000422a064200a203100d0302400e11036450905545c43d00481c0c042d0a01d108020b42007025846e8004201055811000c203480480d0129200250014000c1c05000307414842c800160300100708818041110350011b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875990530 1250 875989280 875989297
    0x1b0816060f0c120f08150109050904060b0d080408120415080901060801020c03190c0c121506080a03080a0501060c02062d0a030c051c09030908061303030b1f05 70
    0x79100d01c07102070700d650320f01c2d034104582c403000203030314045407005030390404201500f0001c1c1030081c0082e8601d4030000b0380308450074025a80702e5180c00000404205158000c04080403002c1c2481402e242c152038508003030f41080c000c0111601540400400180d0428180d40484520f000610301c940d00e0321200303484268010380048225500c510003c600d40c5800d000a241c40411000191381e1541130791505540d01242c0040041040300214009002c1042c600d03a09040d80c83e0104482584200ea20300745001055440c050802e450412400240a403008600480c0c0e45000b500c071480d0310781d5030903214005c452090265001103540002c1d0400541012009880e44a0604000782b04d03403440c1542800c0425101c034611010854002025644280d0600402e0080710860400500f00001b116911021441100e0000856552400204207261107400d03400e00408484043c0c94603800d1030f030b981c40d6100080360025000300707041c41980304440c1002c410b0318003100c4100042c100e440306d403550111481d41c4480348 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875991780 1250 875990530 875990537
    0x806040515060a0b070318081f1b0f0909050420041b1107080a08130902040513090602120f0907080c0325081006090e0a020d0204271b0816060f 63
    0x503002e80000821804005803d450740200703018418400070751681c86a81f04800a1142407843c5050001f1540c0c0c100142034ac040c1c1060408140802400c45040c3c0d05540400c0c078141c100000d11050002440720001807004d04140c8000e00c41d41c0030140000e480303a00110310100d401d0900304c80b941900c40c030310313102c2031810f80780c00e5900c61a80c4468580c07804220b00c038140c1d04400b000900103181c1c8006800403004004203401503091520308000074121408905e01224040d450304164410400c040c0d046620000c80e000429106080a03402100d40301d804450b130103882c0c4503000001c502104001425284a00c000b001440d0381d1138940f02e40300d60684018582c1c4045021440c0100d04240b0074070031001100c82c00100000c030f061400c0e040c1c00030754002511070400350700070212000c00758a90040781d24502d42c0544000ca5202500d4041c0c42d400781480281210800b101c0200310104140f0140603c90000c0c0c004806c1c04c1c0c183c55a8001c0c0d128000c0d581080310f9102010401c02c0568050100589131080604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875993030 1250 875991780 875991797
    0xf140903010f020c25060e13050f0108010c050705031b01060308030403020a051b03030a0809030906070302010b0f18040b0603070308030411031516050318070806040515060a0b0703 79
    0x1804039003542e425003602100c00d9004070701c0303001280007081a240100781901e11441074001c043c1d4030b80741202d030500460042101d01c8003a00101d85075002410000080700d80c0810040c50030040e00b4415403400c0c007c6800550034240c0504106100d0b074265008203400c003001c0c500e0409040030b4224000302d6190080c48a540791400013003c00c940101035032040b8025000b4140d004200c1c07074154180004030a043d541c50b090308445010076140001503800140031410024021f0f01c90031201e5155028032480c2c10303404400094140100740d810f401c52030100c00300360f07081c80a103805c24003009140c2144285400354460710500140118090f1440180c1003c00034050b162401d40340c0c1c03242c07041c562040f18151012700030100260814201003051522422021001f482113007440042c044481440210b048104803020010884600344481499040c01b0700350211400c0b1343e950108644c48d10421a4180c0f00b600900d090039003a00060358034144141c0d4001c110112142c14640304140e25000302006a08126090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875994280 1250 875993030 875993047
    0x16051e0301061508060a0f0e090c0a080c0307080607050715020706090606140108160c03020f03030a06170f0a03140d0f1a0301090209040b1906030c0e160f14 69
    0x20322520001d08103901810004943c0104003504071a03014010500980e40c00004020500340e40880c0010340d032801401d602140c44040003d860f0504206801e0f80c403082030a0b0018010000040580c2040c005500703454038282e94a0b81d00352556411107020000c55420000031000680c4503201103100c004642005082000c00d880d281c0899042d001d048490540d110024000208241070700900543c2c00d01e8188010310748554000143c0e5080c403545020b03c04008912030400d4024003419464144103421203480385050b070100c001070166072260740407003910001c0c2414040c2010561004000040009101e0000d140d64219071900148802040f000c4c01400810314052050051707101c2d403800c00202082901404403400c80008400461500c00da1400207240c006848022400394407681001d0303500032a603a50504280102582151b98010500d00078020007040340447d80803081d10f03072540d060040750b40c4500a1000d0b401450b8542000706403000c0700b03d10414403030a000b031000706441040d241441c004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875995530 1250 875994280 875994283
    0x3020915030a1203090606050409022b20010e0a030b070c0606050904051018020f31090308070e01050d0f021318050c19030b011704030201050402090916051e03 70
    0x61034090f6001075140e00c03207032007401424010704000d01000c503801c010040c01507000a021700b00c644007040c1c0441c2c8141c18010340c80d408601c200201c0d500061040e80d07900c800d504620200c210807640c0c0d070100302d0713400480100c0e040800c0300106485e44041d589880752034908082c1c54003500c40408985032038072030b0030115080e22881c803444e0103644680d004000c17800c080504035003500c01800c4071103003480c0c10720325000160341c2d00b4100c040d0240040d14204410f00c0d081d41800340640d12450100603094818a00c031885c0c824980c409485180260303160b401503183c4000888614004504d9540010424410142c03c100d066200280b81440400014900020b580c13200a10490541c0b00c00ea130b0500012100303140d18010b00030154802c403041419407403c1482051310410b0130810307102d5420950b4074003a2181d81d0f4000c1c103c40c40e84482003142e0740414541450001c1c041c00d07080350200e0003804140013180c14001e0004004400c11485d0030386188003400c3c030041c004089030120300d0307a0481042c5030102c40b03e502c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875996780 1250 875995530 875995553
    0x307021e01021c020d0c020d02090705040e071d120124030c0906151b080721030c230d090308010e010b0720040b03010e0d031503020915030a 62
    0x444814031810340e000000190034000442580003144111002c0450659804208030a000000b4241540110018004680500946032009401c80000028007400540242c082c00484040100c84c04480d521003000b1909a0710b602944079580351152200d0f845480e00c03e0700c502d1030464031000000c11107442000080e031303001c10000210072035150807014400c0c0101d52900d81c020f0110510700703000307483c5080c035503a00309508a4038030070803c03034080c18440710f111964031940c0c0c009800803150350310362050341882c2c0300e140c0b009441138840f05003400b0030100d010301034003a072100e442c1203888442c00c50203a42d0410988a8110b043c18017816420030a18a918486200712010341e8000e50b14221250304150480d0712956042e009090226004d06c00c5000151080c503880b492028a0019100600512008217000e088070b110225031650905840b090511800180c2da52800300954091001c00a0b0b45c0815494901f540030181d0420b2a0000080070403080c900c00703007110600034003241d01c20030b2680c881b182c1700030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875998030 1250 875996780 875996809
    0x31f0e010915060906030b0604050712020d1a042f090d0b150111070b0901050712031b0e0d0206070201021e07150f0e10030f0e06041403030601051b030702 68
    0x80403100b10501400c61446581d000d0310a0403820040305040d5100c220110000412a91143e9201e01c002130b680f40c490b9001d228140030801c4159111048245504045c2c11022072502c1d03006181c1c480c2544514190003032500c41d9502c08000600da0407842c0b280d82030410711400d0500704000412400c2a1521441450703c440c9000e6083ba5001c0d00700290741c665402e01c49000c8070304000e05a00c0c0036494180100f2a0021151a0041e05968405810041e66103014000c805001c03050b000181583c00e0381c268200210b07041e06191810021144078809403001c1414504947d000040264a0801400c10800801041d401401110500281e90b102d010a050361404514803a41183d80c1c10020850642220b040103d0b4070f00703140901f01105800184a0341441031024890342e141580300c001c1c180690b11980c052071b41d1803024800e00708680c0c04159500c0040e40c08a03840194081035079407888000c8280c1f4044d140c1650780501e031030400c103002420101c44103504032507408200400030041c4e03a021114081c1d007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875999280 1250 875998030 875998043
    0xd0902032418010603121d151305040203090a0b0411060301240c0210080411120706091a1c0204121a0603010614010c0302160b1b010209031f0e0109 65
    0x280b404400d104096298502142c0c5030b6810014103100141a0780683d00c02d10388035190004000006031042c0c011645610f038500c5e04220707010221300c0c0e0b210081009000c3c08140201240b2481ea0341c500b07010032031000701d6078071b00385400243c181400105c10011007508180030b2401c006150b894078001500a90080c0d1042506c0780246807000c4039054648584040d501d114189100101c14a4010945500540c01040100083e200c0090100040188054482400a003028400d0414190000c2c1d480e441409180003007646c84100203501c40b0702d4440d00030348451045030541000000c10850314098004800e0a0450760280f0010031403024044d2030200302d502840408403641c2c0e500b000459050b8024058178001c2c1d040840a01407000c100d40c054490800a1809503c81d0680341400c0781842d201c0000202c2501500100041d0136603c6000f41410325040119503050380309a0002500300e22a002d00e075501500060405400407140410a444403802e0383d10115040045001312400c440a444040300c41 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876000530 1250 875999280 875999353
    0x11010219230406050306040f020c1b120f07170f121806030907030311030f04030b090f1f0b01200718061404020a0302070b07051c0b01050d090203 64
    0x184540429280e031589107074048078903050600740c0041591000030310032400380e078848008040180043d8100d0300360041e41c0040d10700b480e420245d030240c450b00181c00030340301e200c2124a00300580800300e80c4a050455443c010b2a00624190006902110018080c049401000c40b161060102440f8400803401c2680385075540d8994220206100c0c41c0f1030800c503018200c24010020051000280da0080e80d0b014180328169828846c165483e6101e0307180e03540b0003030b08003081c00801c002c1c4040c217640c091706400e003d488549030607204182d6a4007071840e154080c0480007400c00041c90599010050003041850401e0812410010340e08500071a4110841183d000d28020841d1101c066a01d11460340c01d820b043c0074061602c02400c00c0502c0361030100303201d00d9002039501645802070781118075490740142510081d1420342030181c0b094104021a480c01c0f000c0710004807070320b8150701c501700392110161201c038186884070902c030b07004001d0000c040360144524806014420300c8803080d1240c405250f00100351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876001780 1250 876000530 876000557
    0xc0d020d1b0608040b0c03060f151e0309010b0d02030a060e0c04020a02150907050321041706220c030b07020f0601090e0c030d051e0d060e09010e0d09050111010219 72
    0x10340c805d00928002c04050705006202c016070301c12504c00700302901210510b0104c100e4004000f00b92007407035a0300843c020302c074000c1419441000c001c0d5200b01c580c4ca00030051801d14406000482d969200c000358035402000001000134a03990000c18054980e1044482d45001c40001c182282c0c04800075102682c0300b8031007041100101540c055210030b14002900405152002080d902c0d112405100c021881126503e82004017100c281c40003480c201c09499130000641182d01e03181c12098640c8801956000030341c5103d858000d40c20032010780e00c0720004034904d165890702005140c0241803002103010300808032441c090b0030404140680f03024500040c40d80039200715a403604c01c4512607580039070490140303101016000380c1a20030303071031014044080c0d803c0020b0a403c0786205805910300110315003680890b51031900ca1020f031050301c40300020014030320752030405592402200c0d09000041c0d10300500740300651144040c0c6001d42000030000d4203000118121240003850008104000340e510b101108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876003030 1250 876001780 876001793
    0x60a0509032104090c050f0f04051801030f0b041b03050105150d0c090203130f0803061507120f0201061a030403080c0a080c0708040504050a06170c0d020d1b060804 72
    0x2c1e0b1915a803007003104075080034040816000e503105015440d9525800e18004500440c00c40c1c02c00d5400380402946e8003e58145a455604603008a0b4001c076100304e003030000c040300488018180c80d00800752106087c01030b91b500e41c00b518020002c0700c0c040c41e92805040c225883c0c001010107544108004141464240d00400820100303038409031040b81000d24400c0030030441200b64040e102000c0300565030307035943c00002c1811410180000c14400307011884409006888001d94040c480854107101040c0c54a0400e559034055a1320207004a8180740c1d51107030f0503014403000100c0340094000410071540c1c409161400d20352850720b600d40c0c45030000c208401c1542c403600a552094010445078100101001c0c021302c042c00050441100440001d40d400510149006440c02091f00420601c49884e04240201c050001d61294031003040307140f000004000c1c0d000c100642c0d03d0744041c0c0309003071943e002d40030407880505043d4203035200e03104840d06035a41858007240c03034058802d40e140c00c0c5c0242400c2c502035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876004280 1250 876003030 876003043
    0x90a1a010e0a032003030f091e06030622020a110f07030b040816122d021504020a030605010e10080a0c03230102040603060302121204030f030e060a050903 68
    0x2030400210100040c85640ca0028000a494110701c0a00710304d0300308841e403a1850886048180e0510020850210740301d0300c1001091404801c5d0703241c00d020325080703040f0a0010b4018103440e600000a1001515509101090700800c8045041044090f15194001d5040303074030803080300b03002030b1030400289014403041000554071075000f0020480b203841d60304ca0451840001e40001d02e240c00005004d0101481003001c8107a45403c00d506001e070103211030000d0a1602891501194661090400204d2114034001c0185448854000d4062100071039114005608018401c0781d020f000c803440403011a00301d10a01e07010340f07008034142015091285e8031050b14040d580c41000184c0c883e4180000003690740081004980c0d00101200180a8090061040a64060701400b5a40c804600011102e030301d0b40014048900913604200d83c412840602c546070501e0307060900403098100420000075241150b03134100c050080c504450075145120020704107501161010b800140c021a44c414140b070b0034021b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876005530 1250 876004280 876004331
    0x2215090611040e16050c0d03050910060806060d020103020f2b090c170c09040c0504110c1b01110303040609060c0e010e101106010e0103050d05130510050405090a 71
    0x1420705103443d1a41064184400910b0007004100c1580c41c9458135002d807081d1070f10030441c03000303841489160050040050408444aa001e81719226040c6510401446541c0940e00c45102502140c0d45400500940c0083c00e00304904041d420083c08611044c100d000c0d019109038114021186865450300200030801d10320a080e41500c0c04d4000400a60440441c2d4115842c0000740e542c191450710f82d0070f0a000400342003e810500d05010030041210b50003090040c1c2d901111704008852500004641c070b030240002c43c503a554030107405c030902c0c60410301009213448414500528104070b8030780410700355042614221100d0b0f40380c80002c4100640b500440b001c003841c601c0d1080c41c43e088000000d01440c90310020354054034880c2496540103104000e103241d400c2d161411035100356034440d40c141c00b001091005407107074002c107a0803800ba284500c084400c012209040010b29900f0103040103d4620309405010a00104000014043c3c9902103220f102c2c20340a071002486440c40344041101d40d191400303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876006780 1250 876005530 876005561
    0x50f010b030618060f04060f020706060e101412070312051c0207080304140c030304060e0f010810030821090a021201050c0d0f1d0714031522150906 65
    0x1540340940343c0000303102d41d110b031000d07605604544960070034034020820f203a0780340905400094140c00380201c9800c41303011034840c046203483d1940d9240040700221018003840260810035860600da0349001c1c4100000302d00d0a6064a026031759a944400c03801c10080b090601280000c69503c0344284407140c241940707030745010294604021a034640c101880010f20050034581d400b040034503945020042c6000c40c12019003180d43d0760742c8418010742005001c9105510030300240230000101d501c6590450b02484d010022008001e0940d62204119004502850703180000c0314040400c45c2d407100340050184516034041c00411815006104003a004400308900aa0415050108181d460821681011220301b4001a80c644140310140600100c981b42d5480000740064594488804110030080f11841550700c1100c4000e501810344421040100641490041e0000f44042c1281051110102c000c81142c18190505a50382e00a200114203044020742c0d84031071109c1080111310510036600c881c401c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876008030 1250 876006780 876006811
    0x1206041209091e050a200702091e041211012d051006030c120603030905030709051603090f0f0302060106030b1518031f0b0a0605090d11010c050f010b0306 68
    0xc000d11502c030030030383c03201c07452030780e40c40000e40d1640740d40e11034180c0e2a019a8058540201140160720f1074004a60070791250340c48602040324000d544039040d803040410011109107540d203071150351111100e85400c0091060107415400030f510700b072040c026010303040110350242d8190000a003451605a20543d040d5a203068140708658035000480ea00b04c42c4645800b048c0300f00000d00450f1105404207040a00c1400c0004c08030406800010034000d032a01a01190b2296503140c40a2003620b4085e00c546842c00303040c80c043c030421440798102c600c10501440c48441c100e90f03507a0312040404107520f4240c005800203401445420b40c10300a052500008851580000a4503003451601d17100b8070a0611001d11048040710302510184920040c665540d4810041e05030049440c0d0007424104d0041482400e0803640810550702420030b40f16403030806481e01011452561318080100c420040300e0b410f000001c9500c000144c0c0030003205002441d60000400c500c07051606052410901910410b030910400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876009280 1250 876008030 876008051
    0x105090a080310030b10030201030e07030f1709060d27030e10020c030a05010603060f02121305030903010207030203040e060303190f1b0f03200a030509120604120909 73
    0x40c0145120707048034449990340c84002d0801c030280215400241066030b40000c1001000b0f000d1800001c6038000e8030b090010407440039450391036007481c0c00000d0010300d505141c0004a100707001d48401b01100319031694508070030700c400a004e6070440c01c54521041d407900c80e48902c490074140071300300001042c62501100c04d0a0343d00a482100c902c040a801800744d1521050243d00c200b200e030340e0341b40700502900c030b00d1840c50030964042c01541c001610081e00b0003008613607121282c400c517041900705442200d101e448aa010f0766030500c12200903580d40c481400303a44615178080c4014101c8c00e20070b400940ea00c074604200e481359110020500c6200c0c1d00240b000000c096a6122500b030481060310740042031130b0701d114003038403005400d2030f02e00300681100920001b0400000b0a09801034082c0d180c3c0244820450301609907400031203410036158010801040c002800b4002400115400808011940904090003482d001d42203806550000207542112210380e0002c5488004d4100c0081c140140b0100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876010530 1250 876009280 876009283
    0xd0b240307050f0628110601050f100201060b0a050405090112030233181605100c0203010f0e0c010f050304050a17070b10050a0b07020a0e040f0b0c030f0603010509 72
    0x2030b2049a00402002100c10140c0d50f40c10202c400700780c809411485014030208241c01900300c40030440c004107040c6191966400400180c207030481d640180703000411749841c0d041c407103e128100101000d541d00c80301c01041d0b6050440240100c642da954031291a04c0c41c210410a1100041e070002c00a100349580800101e41d000c03c1074108021001c40c0011660b07000a203101180c0d2001c02d201c0c02460322102406142c0e082c029122440f06400300031555184441012a1100381c540d202d0a40e00400c41c844d20a0858002c14041802c41c1c0000c0001501161125501064450118500c45a500519444c84180da008003414019031042d152141c1513247c10ba444030381d103441e000c03005003441841142c2c240240700c4060488800e164401101901800c20900c0c802c180719a5004141c410340d0120300100d01e101895098848017a0020641501617150901c60200c3c0d2030082c0080e10003103259916040400d05411141d4001ca12400040b580c2c2e24103090907100f8000047d1030fa0744030341d040905001507010f0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876011780 1250 876010530 876010543
    0x60b180609060705011e06050108131211070306060501030c05161707050316060e030a0903201f080c070b061027150305070f030504020303090d0b2403 66
    0x419503140755141181000a240ca008101c0018241e6080c103032200b101c0c14100100c0b0001500c1060f050080b141c4400040d07405c05403ca4180744c544e6102c0320341c0000316540062440004581d030810381c12a509103031a0b170b410054142c2050b509035403156002c11807540e140c41784075454506881e040b400e100100003560b10b03070050101c016007258030507150102613084a4080300c1003258070008980ea11442c980301d11720381400d001c209881203840c0035215480344202000300c4e15070f4950b540c6c0e02d0540d0f074119aa64607401900f524002c50f1003810b00c0c02c0d801c0a0300c0e081c00030803c080c2d031410903080c4031030509001403243e04010101d400e011414400a0b0014107204055500010f003203071509084000e5600c2281c250304421014804045030400e070504c200c44040e0f824082c0d41d062031105155000c1c40a0942c2078401c140e407103200180150101f46801480707640840e4100380b00030241c0340b43c0204400090001101c041c001e84180c0039120500c001c0500c0c4402c009030002139101c00c1802c07203500e0070000e40c4030308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876013030 1250 876011780 876011827
    0x2090a2706270204050918100203070c230f07030b060607080702060d0b0613030323040e070207050301050f090f0714061b01020d0209190e04080a03151404060b 70
    0x140c16040300d10300d0507490f0140c070090030000d40800d009160900c060100500301d003520324124080d402e80c03a52903c20074021a407252416803980d00202e0300d00d58036008013030b901da06294104a0300c0e0481090031070b801c0c00a00001c0aa4100400b903460443c28003010620026280314440d00c0c0800c10100000c040c03200b500d80710ba070102d600e00e46841c0d802e48408080c009200c4c2c00c6034448000901c8103180c0b80f82d01c824906880c004c1d0b81e0008101102c1c282c4031700c6001d6030540c080010205201c100280f01c4a0751902e54403100c2841900c500e0b80c1d407000413078251501941c08003085a06082040513001c41008044404138260000b841014a4a00305406840c0d1500e9a1382c040d040014802c2d0307400070101000d010040d1844021540c80740464843c60003500011001e82c421104840f2960441c010f40500300d0036141d40030074a1102e07880725613641c40070703a1281c0030044c01c1c182c8032128000e400c0707041c1d004940100000e01c00c0c4c260000f1008104422502c50f80c00c0320346011828080020f40c2c0b40c100d5400c0c40e510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876014280 1250 876013030 876013079
    0xc0d0f080a1e0e010c0e1903240e0309090708070903110d0807201504210206070302010c09080102120c03041a07050a09150203030a09030302090a2706 66
    0x4508a00184502e8415a40340c100342c2c0c240b260105034984154080c182c50b034000d65804400ca0080c1e410410400c02803035a44040c4050600d00b0700205420021403428004006c00105005050038175500a881440c02007044540002c108090a42464610030358000000c2c9010f40d42c91400050240c00c09865010103045187c52841c9081c1076219142000d840540207081300342c0794460391600741d110003070b0f244480f80050160b40001000f8248024440c2c44403200740f42080c1800d0030300c54000c4481810100407c9251850001c68001d03880d40802454601d000c0d90021541711415000540101c40c181d011a10b8bea104100f096041c060f450354850304aa00884034030360ba41c0780e0f07080200d48410710000c2d944d0554a90000c0c0104190010020120120701d034842d0080503940b8001c04903000140c0e9802e5000d60010000100443e1140d030041580c2031181c03d005081c00541004a00101e000d600241c0c030205400b1800d040d0400d04510300e0b610040241020700659007003031540143c1c15146150141c0d103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876015530 1250 876014280 876014291
    0x60106050a27081e0c0f0d0b1506030103060b0f0907051e0c0708060928020405180613060e0a110d05011e050103060e070e07050f04050301060602030c0d0f080a 70
    0x301150140e954006120314821100c80c0e07080d03c84041800211034000100b50700ca40300340d0300e055050101086c00b02c018000d140392840c14460316441141140101050402c00311040204031580d00c242c00366001e0360080600081e014030380d40500c92042c1561541511441c454410002819840001c81d1059400700050481c2441c5d030050265540c01440b0100c0c0c0a40900400801c44810000301c1d0361144001d0001c84140d4502c08003200035042070b0384425451500b601c00c2d040c001d41402c0c0c11040e0803d500c2c1038504810070050140c40c0c10710030700340c4401840070f0600011070140004c3c1d0240d02c60080b928800b40c5484600c96803454000c1039900c1041d03008d4440d40c086101400780a41c03042040402a00c55114500300e070740c0310a0000e000034003084a50601c1c223400300740c01000015081003651101020400035843e000c034203640ca608142c09440001008200202d01501c082c0290340041003160021a16401c168000300c1c10103404104440c03c21159214030465194050742580e000000548000b42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876016780 1250 876015530 876015587
    0x1a040c08061e010c140105071b0209070807020a020a150306050109080c012001020403060921090501110106081c0305011203020303010519031a0402041d030d020922020903060106050a 80
    0x11800d0180f04003604c0d49854180c00c4042c1711341034106a1181007a913882e824541c80c08003808180c02c90840001e50010701c02c0d00000d22050103a84003540140e00ca00441701c001d40d00f540007074040800c07504031001c1ea524881e4039247c13464240c000d0350050842420900010b900b0020140e83c1e03079100c1040141003011964141e5408059182080300306001240203554890b140d003000c2001d805099011184900782c451260192468405400d000d80c00c1903036a6000145000011907003421078041070180e075540d4100001f2428410001449010084030798a050b0310041e000290460700d050340800b010780034009101000030342c01b1044078155001102c0e00c200c008942e51a0040e8001e5a8000810110128440416581d414030202c0e20840c8200c0c0c040c01880d08062200c00802c0856154010035402031100200401c159005031000807000b9010715416142203140c0c2c4580e44191500b9031003030341e002400c8481400c042c04034901400302801c04501d08200c20000134a200c01311f6110340034411001030200b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876018030 1250 876016780 876016787
    0x5032e0c05180a1802070b0703020304031d1513051c080a080a140f060f01020c03151317030a2f070f02060a030b120607020a0b07020f011a040c08061e01 67
    0x10150138801c100c0c50101341440c803941e000b03601062082e03680340300e42c00004040e03901c00c0c002c4902c61b60b07250303890007070544a5030898409820840c8449520a88101c46c20701401d01580c041c042c4015403c50300c4410502e00005e1005061010082c000b0310003d400003400071400030000c40b61058041c0c07404210a6072580e0200c0d00a02000d051003080c541800140954031112258150041c1c40c00c492800712050100c5c016a80c8d100d501c01c3c41d0703405d0303001403491f80320f0710701e5040d410755000348003030388151000203642e80b42050310258080404020740b0100900074402c1c1d076481406c103812009074103054410340003d0348220504030340c0c81c40801281e0004043e400c000c601c0502250f07180d40a082e4a40301c00c2c2d8800098043c1110710941c600500c1040c0072162009000100f65008a0042e0007170300740c010341c6844401c12000014008000d500c92001c21162002092080d0900b0ba42014628403c400c0504200010b81d040e1180740c404110814040c0b10b0242d035150302c4103000d0604050144004044480140c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876019280 1250 876018030 876018049
    0x2030c1209121912091101080604200a0e0306040f050601091e0f14010b0a11280212070f03020406060e0a15020f0a0b0609010e012d05032e0c0518 64
    0x80a017801c0c0203940d020800f156541102420302629031400030390310b0300c0501c03089440c10340e0795246580b0701440c0014039981c00c0d0002c00e05a00c40340790440c401100c01d00424503088003510103c80305400240790b80d06120b0140443e80c00360280c12018044115034180200350604600c203500d403195602c0c04192890301071980414805000180703503c41540c0e40380340300302042d000207142c04049000000382c62000280410f4012624000c41a1116118945000203a0010b001c4d8422030b00825a10034014841c9000c1041000801840301c020090078154070500007500c4295101c0c1e418000c40079424030f1155034000105040e03480c01030306256412146a022482c3c007a8503410100640035030260300044c08041007038648140015140e03280c0c60303646c0754002c1c4580c4400740f04480c41c0c2c1414001207842c4041050440303007030802d4801609005521b0360300090400418560b0603001c44815102c0b02e078000401c801c0c2c2d404900030810301b00880d50040c1b4018080e40304a10341e060561171a6802a4855691008407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876020530 1250 876019280 876019307
    0x6010f08071d01170f07110a0209041106040e0c030703320405120c0616050301060210090507030c0b0a0e030705061e0f040609080105060904020d0f0309030602030c12091219 76
    0xc0c3c51315803c040e07801c00040c12055501d507000030340e20030b040c121151000800e89a01c0d94083c0000d21380f9945c544503514084030b040102c82d8401002c01001401130030b01c45016009020021106580f030900710400360803541036035200a80d200150116110400c4031000810880011400604580c0e503035180c444c2c18014150503503070081d00080f80c500c1e03511030005001486030307400b009044c91070301c41c0031002d80f0280030901c180b100682c8050009210000590403038000307144106d040303070750070354aa5443c6081100180c0000009400115442c9226640109031130b1f944081030f4040c2041d0350501c3c02003001c80c411359040404600418620410700a0310030211a2181c21205050741c407a030712000010502f001074802c880141d800d180c0440d0b114603102403900d0241c0d5004080d420b94036415550310031300303006d003101c19400e010400a0001c0410044e0004500c0340c56601c0ca003035030300c2c0c404084984080c80003030100d038440e501030a5030102c402d6a035002c03600e1000c003c0d075040d807a61124220485003801010344 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876021780 1250 876020530 876020567
    0x901050d0f06230c12061216030609150509061b19090302091b0a0e010c0f030305180708060c1b15040606050105030907031b05041406010f08071d01 65
    0x18800743c80040030084404076818084148040e4a600e03c00c03c9090050784000e0199245c3c0d40007059480c602150b4102000c0c050805540c02d002403600510100e1060f0390081d14842d40f81d4200c03c0070005490f1180000041411081000342003802e81c00b941e401000703100940c07110301e8101c0f14804060f004290364a01c0d403410468204400f5580009018416a100880c0902c2500d80815400b12095480389204510300c0341c01410561258003c40f00400c0c689012814002507006560100d802c03100700d844000e000740c40c003262909200c00101d070300b9001c10f8218511508511000e000d60b5101061154000240321115905d130b0050b00a0030110a580c42440c186034030901c0d445c0b00514402001c06446140a2002040820b40d9003005460520045420b14102d40114106000055081801c4804600b40301e01c4c100300380340c450001c42c08a544078049042e510303007183c04104180da4840301c00500c6444615028050b400c06d030b10702524031840e58041d44001c030f40c01589411240d10a01800070410400035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876023030 1250 876021780 876021791
    0x80403031d19030f0219030c0204063305090913080f0c0c0102010605040e0c01030e03040f14030c01020c060409020a020c0d08031005060405030d0809160f091a0901050d0f06 76
    0x61000001001c070400c1100810240c800358a103817400400d0000320441ea01551603014075007543d003102c18620300c401c101c1e48195110004a0031200741d5128071480005440c0307034a81d942c060541340c4c81d1000c050102c0c40c01c102c2c04001c001982d031280440550485070185d010380c4031128034900030000c1d0103822000440d070080403403c02d0b2210000108140ba1440a800030401c091311141400140c070996030394403101e680140300c9000c465100394010f103101e00b000b8056034140303030301c0342c0300d030270074040b1650001c40e255442907409011440c1c01d00c000c44251800340004c10b12030303c003c008030b6840c0c05548184000c0c0b40c0d0201c2c03050100d030b009000012011200616078114506545415a000c0d001611400c20b42c820500000c1000e04024045a0a940c402401400a1500038000302c8072444000c00f401c981c4e018210182d102a6201c00700c01016044400e640840142484420001c68160b6071243c40c44003a000a020304a0300c40c0310001c1d05480085d01c0754921420700f82440031010300e480c7c000a00861819 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876024280 1250 876023030 876023053
    0xc0d0e0d080f1e0406050315010c0209090a0611030f06101403240a050627100f1d01142d040911030907090e07080f030a1e080403031d 59
    0x1c070300a0052085402040050024248201c00b0f41d0150740680d001140041001c40c40a20710414820003d01c0c0500d003080d5088a160b0100d100c51401751080d076059070021141c1c070204401401002e402a042c6280a402c518200704007507003008003d80b03098012071044451226403442001812401131001c0310040c0d50b81050411400d00c044c500d129103c02c4a6403604080312850044004022114010182800c00480d508014180041550f84590701035900b002d4408589031f05002d20403140c1152070b1200000d58100e00940050481c7d0003645400e881d40301a083c0780d03a0000c40f181c0d07843c81340d0b2a0003511180c28055201e060320704800500b115217840e5441c0250100343d42c1c001e005a84c01c2d800140710124509034030707950900090311105029004801c0500011016a03c4081c0c5541d213a01143c040c540e8070030207036042004410307000015400000c4c02500350ba410201400080d4108098042c44070400c96000740811400f030402010981c94130106008542000d0800203e114510103841124440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876025530 1250 876024280 876024307
    0x503030c0417011a091f0b0a0e030d080406020f1b0c1906050405120726010516051218030a0309050607080405100207020d080a08100b0c0d0e0d08 64
    0x6803207400200c0003405682e02d803401040c060780c180d036001d240129642d44000c104021204038020641c00d04a490040300102c0c0c848180c001800a01200c540695115600a4018402025410070a01039888448410b507a103034000707442c0ea8040e40050300103850300d04c8100100c1c5070b4400c541c07030303183d4000003c0c98554003070f140400d05040d04d05046030702c01d4284060300024440b01d852440350002144040c00100031508102d9054200b41140d03600b030304c3c0312a48400070f10f49600c1010b0020012001d0b0348036074080c110790034411740d5007004002400b800c00386086403009006100314001e140b4085034110200e0101810072546105110020301501c0c1c5544c0c0c00d040c000c0c002c1200344008c1da25071160001040003580039002e49030055030804083e0020307000b0050614084e5000c40402c98218518030302110204074050040d000b600020380c0d5141e00d9052501c41d03010884129001060380b803408010000c0313541c400282440766505142015001340340c130440045c520003d420000b41012600090361050502d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876026780 1250 876025530 876025537
    0x304031202180a1d01060206010b042102040203040b1801020910110a020a06020a170910081509040b06131104091503060906020c060c04050303091e1914030a1e0f0503030c 75
    0x1c101c0000b00c0c2581c0c6e1004100d07503c1100703119000d0382c0034007003006100620507070f07030030201c510615850520131302d909501140c01c9074400c50301503d503005000144241c2800d841c076001e461030800c2000b0b5040c640303010000b990024a2230107904c24040000400110840c007400110040c81c3c00030301c00c40119540d00ca01030f440e00f83c400303400c071103045c0c3c0429000c40009003079040d10708a85014000900350a5050001d0314103480183c45507242c0a50300d0200c0c0001da0700d550175184214801e2144c6110380c24520184103c0b541481038003801c1c0e0342882140514012403100f61000c070f414040300803a0320040030201001c2c07800290401713040706007802060800d11000d0b40081c0908100c40d07003240c02964503800c5803c014003503401000d6254000b08103030905840c011414a400b0500243c00140500c260030004604d9114001d40c080501d8803d501006650031921303104000000079000f511203020b00b540d60300b1013003c4075240d4002d00c0d0024083c640901c884a00030450b11a401821a41c0d41d04000000e04000e41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876028030 1250 876026780 876026819
    0xa020304240213060305040807060507111b011403041703071b08030708060901080a0809010e1e1003060b04230603010609050f150a030e0115030f020a05060304031202180a 75
    0x510040000850705c0c42845498420303504644203074200b02440d59a4800f50002410490801c4101e00284c11400030a01038100c403450400d01c091000f80511001610300785d52075014880d03060040c0104004a00c00f00d00b02e2400140310411a47d0325914a2420784140460343c002c502c0845501e9121010000d45c10f00079030107000c00340c850600c5c50361000d080021600c0240900301180d0445c01d000350000700f15a008e0000510b05041015601b940c481c0440d4404443c420410103070010b40e0384140441c01c3c50307400c0c902c9503d07841c41c0a22406d07090001200c2944240c1c448c40480707034400207980b4250860034010701002400208241c2e1b403540c0d04e02c002083e03100b40c0c3c000d681c8a8802c050441005242031014040320324a94003c0754144580130300240c0090402c1001c1185954a030b0a1484e00f0442480c3c0e80005075108443c800c124031051b005006038440150481800303014100140f10100b41c00c0a00c0b07401c14042c03c0c50159542c105800c3c0c00040032500da8450350811070122011418a40c0e203400f40c1d000c070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876029280 1250 876028030 876028057
    0x2160f05090f071202030601030b100513050306010b07021e19090506010305040f0201111e21090f09130c060503090c0f21010e03030a02031006020705010203030a0203042402 76
    0x252540450090a008103840358008a40c2d0030340405556201d030b8006e5a80030505040000b000000c12000c20114001d445000000450000d0310a1082420001c41c1d0080c050030341c0141040c0d030520300070315424440c004011b1310546a014a02e0900241d5007140c1035540b00c00f800080002d004101c102001c04454051104211300b403000041495110703204103485590004400d4407444019001941c103100c002c00b0009440c0030301c520150408184c2400c44201c0d113006401009038801c0c03503640c0002645402554104c071141080b1041041d658100c804a9509040390300c840c064031480952281000240002420052030f8040003a0268110000d14400c0d41084d0aa842ca041c0d05010000c40340401c0ca80103070702c4000558800000c020360102c1d07503207040504000003800845182d0551840c0c00803076040d00c104e0303000400c000c10b03d1250b508580040225000030b11040d420600081c2d140c0c00000c0000070425070200005040c468511078141c0070b248607408829000f02c0707042040d8040c7d0300c1800d660802 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876030530 1250 876029280 876029299
    0x3030c0a0c0b090a090b0f12030d271e15020a0f08041205030c0f07050a12021609270629180406021201060804051203131202160f05 58
    0x3a0011030200c3e1000c580007000d1281e52410208500000c20f0454940ca40000840d0003016068540040328082c00306c40c44000c58603a417072002401c042c2c80c40d0491201011405800030b101c0d01c18040c00240c03825034050404043c00d6500704005441181d5224082c1480312003201c0916001000c4e4001d00701401d030b0781c6c3d544d00340100b92002543c1000040c0c400130140c0508150a44c03401d40310383c0145130483e0400f030a091400400180ca04103540205009a441e03400c502c0010080120080c0e07400100c1c9000c5c00500050011701c1c000c2e10007030039144580301d1113549608080e046000d9800c8840d0188002c00b0a0841840243c24248001c10345080049080704500c404290100e00400c100b100d9080e0080004401d54039000040d84210303400b030700c22a81ca50f001c0c00864581220129100e000e4403441d5903148491034141841854000c41d0348034012140070030801c0c80b806980241e04001c031941c00a82c0c030428142551000c80c82c08060403e501104d0011600100d21840d44c003001900702d410849a6214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876031780 1250 876030530 876030539
    0x305032d072a11120c150310150c030f0e10081b040b04060e0a050a081f14010302060a1e02010f0f020307090e04080f0703170709030506071d03030c0a0c 67
    0x2e00b00c844038060b185803280c00d10100c2c03500e0940c014a260380d00520507903100016400c08944482c50560200b943c000d804020072001c20400c010074030003040c4c1c40c1602704880d149010007400c1140365920103010400f408900c00107003401800c0035050001c02502410b012004003a000344030070002c0d25195106481c111213054480400c1c000c1d030f02540c12516545140c1803404800340c6103921402c904a400480060001800d9580c610101c00248103220141818000310401981e00c000d50300d0b00201094505814420304140c0421000d064950548509035500e803c440c1c00d40d440121000c04841030828002401a030680c107401000360401903c1082c0034140031000382c1c0301680002c41d28100042c00107031080081c90287d41c10942c03c2401403200518148004030300c00550340c080c030700c250b0210f0030042c5416a05030000c81919808555460400440f90071595100d80750341000d00404100b0030f00d5115915001400e04007020a40401000c40b03030394500051a058441000b04030503500c2000b43c1c480042e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876033030 1250 876031780 876031847
    0x1a030109140c180a0f0b0c070608190507020307060603120e0607080a03150b0c0d081f05040203060a26011401080c060d06030f06060801180305032d07 66
    0x18002e0b10700e03011140c10308003144841448808804000c651042c8240b5001607040c100c010207001030300307080345072580c0d070180750360011314210082d0f00c030008000c469010050399000700800328000c0304521002013569118040224134500640c54040c103031038a455000810040c0041d41103805101d5078480840c2c401160040000c04d000d420000b801002081004103000c0c1e1180d40800e4000c03901500c0110700540b540c03070844054000c02e15803009507200c29044002d09402102c06070f4810500301c1d0428401c48410703680d0142d02803510426004d2178001c80030600710707500c0a003000c001e0140d0f62040e0801150310401c4400c0005050400d4800e035290006a402144484210505940c070802c002c0401c03605550520045510425a002c400b03036441c9000301c0020701140c40020410b00808010600a040c00007180c2110354240380e1070366000c084100b50303000039044000d4a40c4a148409400c140e50b119a04541a0401d000044001030111000304850a40c12030b201c803400f4040c101e001e4a0b00200440c414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876034280 1250 876033030 876033071
    0x601080a0f0f03170903090108150105071b0803210c07030c1e1401020310050406050a030308090f06091b09060d060e070b03100314011802120102041a030109 69
    0xc0c1101940c011a1030104a91141c810a0b092291a019070b0300400009240d1012a041e01c05103c285c00c0020b84065969005242d80d4100c07640c4602c5811811075500081c00ca449045001015201c207124011344082e28282200000d1503100d0581359142801045c43c01940c21013220454407407040c5010a8956860100380c6d00801d61548500e803040d540340e29080048914a0210b45540c101c48000800041e6031041020582241400260301c80c240320400c0b40c00d00f2800d8010074000c91610300b080007261b55040c0b80401f02c0c0c0d0541041412600d401c460380e4200b11400c52402c1c0f581c4039110500030b81c01c000080c0340396a00d261808184d03600d0101d401700b004080b001d8542641c00158003894002241540d4440039080c0404022a911156600080741c2345820031074649491030807655003002400407021402000a00c46802009600f00c15003000e00c45a140c5000680142448070303230316402c20401d5040701d0181c560059191500000050382124aa00c00d018480c255401c0c82e041842429221982 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876035530 1250 876034280 876034283
    0x180302030619090609060606080f04030f050a0203040e131707020904020f060c06040b010807091b051c020409020712050702030c0907090e01030f1101090b2b1404050601080a 76
    0x14203055240c00200c0d014000c981d090800303095036680c3c0704200181e058410300350881d04c18400425454903110010741175042c001e182e002c1c6200b0352000c00c07000a9001100860383c02d070a0402e66101c8040100881c5036000300e400a941d43d140c2641849a0610303c0507131501071510941480e0a40b55400c0c0d145140c5000320040203402107004008600185000c0801140c1614094070003810000b4550607645841401e482c1035850400b510b0044c80f4400c400d001c4d030000f4000303444060100070088042452070061004001080040118103044d4400c1002c1e040d000040428500f50f461342e0701c072500000298040340d01190000b50300e005407070005008105868000303400901428018000800384a4046002081d0904000e44844040380c00c0104500071400380d40102d40c140c0c0024414545482c085d044000218148034201e41d080142c1d450000c1140d2009100e14401010742c081c03a02d004015289485020300d1840c2030200704506180392210040c800c1d4015012a046079903168516a165040c4100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876036780 1250 876035530 876035533
    0x9010e120f0a27030302012418061e0f2c06210102071401060e0403030c0e1c020406060f1d030f1203041703070504210204020a0302040618030203 64
    0x31806800008060000c00c41642003039010301038014080903c2d001c00c540f00c0322070000141000d00a02d03909105500f500942d204039001000c400c402c009082480038803800515103061350303140001807460307041340c40108500032101c0a8466a003164039590b9095000c1c0205189401070300042c0414080400f03c03d00d0012010001000781c1000c0d00801640001c04044c1c00001e48000540180c0c220b015181161045034001622900d0a1401221040c00185a880c0a0381000001d0281070001e2800039001036140c140000c01400081d41a0341100103111111381c015031940c2d001402c000c014048132801d41c800c9a0420000c1e4030303140309481412011101e503000403080018440345049087c84011548401000c445190005100107880c1140c070400d0180d0701c000c04018001000005c2d0303440c04c00d10100052881c150f20701940d000308940070300e100d06040001c1070515a10501c3c561480b0924598015100b176541d00313000e68018001c0d620a00c0381d000000c1e52a08200b1404d00808091426258000c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876038030 1250 876036780 876036787
    0x1060503011806080f160b030c09010c030e0a0f09051b04330302040e09120a080711100501080712050c0607170301030507030b0c2a0f07080609010e12 66
    0x9072500322801c0070302603410405a483c2800301e44050104000410800400d0003884000240b80c4107402003485035001084030802401801521070342801543ca0300d600c286811500c4413001e00b4101c4400380c240c40b0058002951b0140840c1030030b180c0384404141d0b4040d800600081c2c45128803108400c450280c41c04a00b0310900c000e100740c60303d16000014401110704000d408800c1a4103061640c10b0701c82000700400da00050402c180f20f140c41d062a0300070910005491240341007901d03040070303100742403100e010071182000040580d40030302010601a510b00e021254403c031030301c40c00c0008150a010b5803807144580c11001400701044072480c542c5607480b5025180c07030a07880c000d00280f40c00c054421039044003203141c12070304842c0c088050b500071401200103102091440c01c1089a220b0701404a690307c003c100500700300007041080910103c0445525458000d40740d01d0f002d410401491700c01406401741050010f0540c00003d1058000c17007040000700013240007001e045540302c80201d1040c01c0c088090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876039280 1250 876038030 876038039
    0x30b011706010c08090312030a051b12041b120506060a090c020304090504060b060706020706060914280e01020909011202010206010b091c1b060513030602030604020f03040c18050106050301 83
    0x41c4c001d031804c10701c0030b021a003400d8284180007201c0c1d0000ca0f244040701740d494041040301f03030a03001da010b910314030340c4c1c0e07101c2c130380b0b01c460506030441040100040c00400086140c803640c41d031480c0c4081d00400f401482910104180d1a01c036890345c0c0191465441000200404170b444900f9105849907003807160000c0d07280030302c0c0001d68000b920b00144280c4001e075940c001c140c05034640300c00510619203d1040160f4901c2c4514010088810341e8101031809440c0c400181c012800188000b5004010130b01100d8801d029054840b021094468480355102d04161143c00d406905401074105c880b0112603003110b41c0c0c1c0340e61800c17400c05000080030740143c0c001c600410086907900b004001c031400c050000315030242d400800e407010401c0701408584690103c0ca201c000908003c0450340940120315102e0325012600c4040c0b250600b4a01007e03056a5000000c2a0f06030355a40c110b80026840d48100c2e0744910781418282c1540303119201e883c040400c2d07031842051f552071f0340c8140303816540180c403190704503401d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876040530 1250 876039280 876039293
    0x1b0305090705010f030b04090506070f032016060603020a0b040801060b030c12150306070c03081315111201030b0f090c0a141c05060105151608090a0f0303030b011706010c 75
    0x86d600c100d40c01c103640301200c4010600c207100191180b0400d40701e400061071a40b400508540303002800e4441c1208008503004014131490496181055a0000c10070031455400c0c164000c040c10341c0006e600000c803000010390400a50058022140d45000070440142e50710340075000d9120858010110010811000314a440d422b8200742d0031140c102143e981420100001c83c3ca4a041560b4000c040b9415191041c109a4044403103640281074680e00c03000009583e42e40403122000107010407007952101495800300f02c000f8151144040b4201000b0880d5a580c100030803103030705c161204040c44500400003030910100050000ea1440d020780041034051620840940c2c0d4103000b4042903022070b59080004440c40c00845550151780076001410441d45008108200d001c0e081401c01d40782a011310041122950384018100402e80040280d9559002000003916030075030f0380c0008145800c09030700401455810340c030007607600b882a01d0b01c405101941140da9640c0c14202c0f0325500041038a011800060b14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876041780 1250 876040530 876040541
    0x5030f010e04140307050c0406092a0e03060103140706050708030f0403050408011e0c11030d0b0301062402010b0a0e150103020d0f05100f0f0b03191b0305090705010f03 74
    0x2c40030681c0b0f80d204051010300b10741c082d02d000d840550200c3c611101c5460b240c0700d86001407040160401081d816034522422070050784a164901b5030220f101010490300464000c2d003554001010303a40a983c4a1034400500c180e5808540300e98851001e0203d240c5015104440d9800d80140607e821030b5114000b0480b0280024006c50400505210014440000b402b5086080300145200720070b4010701100c035000c485203100c3d510304103e075000f898114408007000711014a1013429001c54190103800120b4094200c0c1c2d03100803038940c3c21064161210b20620901c09240c0e102e0350090102c942c101c010080020624040d800703899aa0078080723189241c140b00809281070040c180542010981003241003111301e000c1c40d402581d502c40d020040c0d0742542c000000007070306d0303001c0401e0880c500b4040d04000303d052a010300d0350501000804164540358501c0084002214090180f251310040505d01c0038180140b42c0c00d501003814500071407a8181c0c0030510b501615410f80d22500c041e080004110b000e40f1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876043030 1250 876041780 876041783
    0x507080c09061611180c070803040c030b1905092a01030f0221180c120a1712070903030f03180606060207050102120301050a12140601090b040b0105030f010e04 70
    0x8080007420008031000118090190258904c2d1004411075801c0c04401807180f0311020b640c1d42002c04020955010760242d4a140f41c22840761a20303503885d85847c4400b00030399000546828094010000052842100c6030303c85000d440e0f0a0000e6210752740383d181d40343d59925200d0410310790104005001800c1b804623289401c070501d00481da00d0b240b405801c2c1281e024060603040d29015842e0740311a24454240c0a81081581300410500030301440d00c940c86c0d6540c0c580b900e226010303a5030f05070110030f01040020b54880d04020445044140c8900140040d8020a0450343d20343d840b1000807485406a0104000c0300c2d0103072144214120780200031001001301c680341026a044040b24074020480314442c000151035190002c05540b42040006403500d002c2013584a0710800810050015031600000380003160314006080c0c52241c4103283c0489607c0046960040703e20a960000030405005d0304000e004d6101550208414014000111214482110004140c181ea0801007181075201441d10754441d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876044280 1250 876043030 876043039
    0xf150903040b180904060c090503120708031e0f0a05070e030d080a2421050307060c0302091801060f0f091514040f1802090d0f02060c16080f010507080c09 68
    0x6070f580b0006000c040c000c0e603082d40c0141d554a2040401d03a0800024005400114014400d141c016507020714540300c1d0000080090790003002103040c10715000d0300181150194190200c0038a03002100b0f0b5090705044604200b00c2d0b040c013000c42c0c00640250401c030356441014018101d068804141036840c5240a000c2046240c1c5c2c40300b6018400020300d001c4007043c031a0707003003040d245440c5c5502c0850842c3c1502c444541c020a2080d8100010720000440d0080b40d4004000302c1d0342001503030150f00030b02420742d003160056005c1002c002c0ca51403158585040c1c854035141d6119401e40644111400c007102080f54002c1442401e0038440c1000300c88803070100480320300d021080b0710070090004850350055440a07108191003201070091440941d040300650300010350071420100c10400141c52003460307003806012450526021029074803890116006104401d00300d4114403099240d140b0592114882c1da4030f640a8081c00040280040c015540a60120350b106502611800a030704071f2a0300005869510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876045530 1250 876044280 876044317
    0x90702070b0703080414060907030f0f170d0608010b0102190804091b080a141302190f0e060d0f03050c030c010606030608010b1912050106030609050f150903040b 71
    0x100c000341d500a00c4510710940d580d080c0780c145858245985140c10314904480c3e0000000c1004111000030000100c03078000e40c00c020f02880500740000004c3e0044400392060103400810400400030701c0041100003482101048055a00c080c86800c035a00140518016003128000142940081d1590100c060103806450702d03196071140080300b1269080048170610f15100006000c0c2c64215800075400003520b80305000f10034901d031107051100c1c0000d2400301100003407a04442951102c00b990001c8040f80094103280c1034481c04142070b003140c64445d0020103001c075400520241010001400102d910500301244070708165000c0c0d03080d070072080d00d001052005100c1030b54500c10034015a8010a5151030000d00340c0e0074081880d0a40700b103c2a0103018001020000251412041c44c0a00300c400c040c01ca4002e103402c2c3e10b4106e0160071710340e00103040d040c100003441060041c041032101d44405100201c07090303004414020b80d101c04040700c500351190000e100030130094803488001d0141c4491503103098035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876046780 1250 876045530 876045539
    0x60406170a090b0606390601080d02120c19060f0f0902093c060907170106080903070f060507090f0303081b07140c0907110703140a0203070e0a1404080909070207 71
    0x4020003e1503503466009030106d80154603c2c0240b0846024000b03440291500301c64a9101960303805402c80204588480065002c24040c070038084424070310943c242c00c4c5c2100f0317942d041640117085c03080124400c0340e20b0440312000c0000644107407480198081d10503400c0342d4440098440348080c010442c402d049505e0f288040b844401c0c0d0240f841284191010380690404c00c00b4052000c50043c0080140540b840d00c00a8003001100c0e600e0440341c0a103082200c42e5030303012905045004584009080c0460400e0060070441545c010f103200c1c0d4003070381c3d9554586590b54107413584809144805804601c0c8200800c1c0380ca02403461f400d20244480408620744411651481581d0034002040051030708201100300035071820390321254004009103451080400348488454982d000e900c4020286000c61080ca05111420b0103603c003401e80080984852a80d520312410100d03070211132560f100c51420a540074481125900c260159400003805414001032070180100c00d140503005800b58410b5100004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876048030 1250 876046780 876046837
    0x1210327141c390810020c0a060504020a08010905070e0603010b0a09020f16150b0105340816030e01050a0c030c050c04050a0f05010e01030209160e060406170a090b0606 74
    0x1600c0c030b004030f0b1007601c07190f280c0030180b410160b2a036141d0002c5801049410045680040c61054079900184005503584841c40080d019032401c0e80b1543d00c075400c1031010014844041030040440d00300b9180b105482d03503800105400c0f0b440808103698001030380c800900144a1560181c084405048540d903c0d00144020007445030f8080601151404a44124040b1040f0240112540184207003003507030405501c0c10b035000c2c04c1c1e0003820230110300c020012110021181000c940804440d00b20303401030f54401c10402d030814200b403a07440640c041069550b080040d1f504c00c1044901d80e10103607454001d800500e980c1142c21300301e006c0042d16103106000c0040c0c0300d41e40340e10916024401e000c800040464440c1c210780c060311816071151400b241c442004001680302c2d0203c0310b52118800d100002100c500e11340c20384502450000c2940c03c194081000703d88a90410300d24076011640303251201046c1c4e42c082d0351000742c1c0c9007102c000327055051210101d14542056400740024044034402122091031460144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876049280 1250 876048030 876048113
    0xe030d051f0302030c011d0d03170c04080304050616052a030a020a0504021c0c020c131803030c050f0f0d0506030601210327141c 57
    0x54420039039032000e1010801a0100309800311070020302004903607285400080c0c8418900403003034107010511801d203003c04004007041c000480c00031310050b012911820000d104c04c20300c480900c0d00002c501c1c046041000b4020a50b001c40310078500a515250038074046c0401500020a00000c0d4080540c003c00061414083d00c1111059a03052000c5403d02013000d040100c00070b4034080c0641c000058890160300c03440f00800c140c0e42c00b49c0e00540c0d900480100020020360241c0b4070700c101441c004221102c0c65020407085460f10301114404c030231001580780c1030b040b02c01903181307182e0401460110b000007074000c1c0c120a5080e21142019400c25030b1018000f846079000c1c0740c1403103450b2030004130300c0f00d440034901c90250401c00a90003481990f041401c40d40703104ca0780234110129440081300341d5003050310611158000356120400260311841026064000c5030841c050f03a5071a54120f24625a542044040d07403120300e5032018000794205aa407508207012009001c02d40e020301000413015140012070307107203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876050530 1250 876049280 876049297
    0x80d02030f07030b042901180e0f0f07270f0609031406040803040312060902070807060c0f092904060513050a14120705122103010b030103150e03 64
    0x20702039482e29040c01822610740071022481540f418100146e00300c12206400001044108450b680e4820300d00161150301c600c00c3c0400c5004100314022914800d0380940502410490071007036131070345400c4000d07944403008940c0a400030b100082c10110404051400f0308010b408580c0c80f601c195101c1c41c5001a07928039812200c00300e158203c0030020007040b081010142c070810320142031f80f0b086c10b40c0c0d0008103110180014082007100200310510141c598005401840d01d1401107550307403440e1401d10641e4101c200207580d02450300b040e030704849000741700d15001c0314072035542c0a00c0c0701d050a46548c075054075030003003041c02c558104c2c10107a00c689400050010346101e441d49921140c1c031b007101c1d4681d0406500a94050842c01300104803c0c12501c1d000c0d1140030084506055034075169425910b01f01041d8061a80100c42c01c2801c05d90700d1010880012075440005681103031500c000a9030040d101c00c0c0304070745542400b00700400104144145d18a03549001c400c0114031024015038041c60340e00712061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876051780 1250 876050530 876050551
    0x602031006020c040204030c170f0a0b40030201060f0b09120d0909021b062d0f130201110607120b010219020f0a0e190c020313050d080d0203 62
    0x101404070035010003251503007000c201e81c1546024110f58840c5083c0140e803003206040b801030209601441d5041c4500c5140b46c4017981202c2d461511400c0c1424210340c16241ca0030b601300303003c0f08243c003218620500b82000040142101c00480c84403144030050080c16003d6086550718400800d00a0705ca0740050010505192400c4e00c03240488100100c40c8140b24445115070700c1281900300c481e030420014030484540d05401600c0704480c2c0c1d8100704100e02c0000305c0310b20b8050b10b020091840c0c2c1045c81e03283c140112016000d094030001400d2100c07140c1c2034032110a211a4400003451210802420500062040c03401e21309428502d0512890480c00b510510f0104030401e0402140320068414225800800d100904500c90501010310316444c5260020f030280844003003a000544441d200e0700b0040c2030842da100c10921b0300c2802d25480b120b42c1e00342e954242d0708003483d40004910000c1034a80340700079041e56084651502c1c080041d0346c1101001110701750b0081c00b552400c01342d01c0c4050b508c00c0c041d145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876053030 1250 876051780 876051811
    0x300e0708010b060403170703140327070b070b0a090804060e030d03061215060b07032006100b0a0e1c02040605060c150615070507140105030f0705070f060203 69
    0x1003880307082d62060b0214500401e0180710130400320b01c04980031140c07802400b02031a07845400b41001c03140080003c1c3d8601a8507000800c2c403858080715a270907990042619070840c1b01724111000980c680c40144101e0501200c140019000309500b544041e400201e404400100450700d0b03500d8002580296000f40301080003c10716145900b424003041c08400c135146804c01c003417414a07000038085d0591990147c80560040d09013844000a40d00c1031015020036040b40b40c503041c803490f008010100c0070100384100003401030301103a221781c0010400d010f601d03c1101342c140e803810b0004004103504240c01500c2003104c041800380d2641c5030710000300a4083d140002c0d06008a95005100545403542c0c4524000d0908002d03060b201e40001c628510f110031810681c1013141c07641000070340c80c00403445005a41c4070700000c084040001c00240b07401207070303c5131106180103c0e03070900640d4a800200c40300c1d8841940ba200107407640d40b0900003031034854820b23200d0240410003074907810220b070421070b41440e8141d5000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876054280 1250 876053030 876053039
    0x903010b03070b120609040c14010e090c041721070f080f0d1b02191103060709150c02060405040f021b0d1101090221030705060a05071b03300e07 64
    0x10f003c4e883d0f0186080da900c00c0036041c241d0316518000d0b4103118009644051403d2044503a114034a64510540c0c0201198503a00744520101041d42c0700d40305021290000381c0050300c2100e004100b44000202e030103181a056002820300005a0340642c8048505c091034404442c0051042c0001d00329400700074601585503c8851051005c4a01081c0d501003030b4401c020300e15103642d40c0000c0000003c080b40301c0c4040044054603283c0b0040d2041b040c504ea05010f21020032104036445010320080300e07c0c0701c0315a0380c40464140156502200ca250294220000b007000780042d041c0b6820140841a07400701c010310703006400361500381c181010380703071005203400c420101c1c14a241c1c4540e60796070342c8240e44001c019940f0168000380364007950a20410603655180a40f81e5400700c00d00076540c10710703009400d4030a03d00c1d1050300000203120807110700d401f155a042c10100701ca2055030070582c409905803540b442d54889030304000b0155107204c0b03140100d101c081031340c0031030724103940507030159810400d00500c1c0b000d0a2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876055530 1250 876054280 876054307
    0xd0e010c090e1513021317060f0c0a1d040903020c190e1f170c01090b0903031e0906070c03051e0a080708070b01170607050f04050103020903010b03070b 67
    0x450384642d54403010101400390444110400e510f03845000c81d100d6416030001100103020b4020803c02d1555003505100016841c00c040315201d807401002c0043e580030350b0314500020700c100e4041c0c40000c0e030080c05011051f0444e0150b41c1403030b03006e50881c641164102c80307800010140d4205440440050300b00714182111400d001c80e500a0070072888407082c901cad506081c0c20040080c0001d00c4c1002d03412641034024515050700d040301c030190060510307003c1e40c00020390ba401d58a4070300606450010b80780100014007400d5003010341300980802400b551800c1c02c415100ca0620000c0c030850300c005101000810050f0b9611001850703158481c41c08090151b1450500310308081b4842c030702c01c505516040c003801c800c11010500c6118150300c20b00d000d4035010142091080307070049110090a01c401300d00040b41c030610603a0700c10710411030981201c1c11995030620032281401a0b481146101da800d00060015602a802425454002400000341010904002880c2405135840007048004c0041e289000300c40c6c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876056780 1250 876055530 876055547
    0xe0901090b0f130204120b09060a0b100c03021e01060602060108070b0a0f03140112121418151209070603022b14091f05040b04080901050d0e010c 64
    0x1840d1404110711090100840c00e4081a603200d503110300c5100c185900368611980c15900074040248940c48202443c0c5071a02d8400402d40c0d104000344103000c0051b40c1d0303551900550030340c16000b4200c0e10721103e4541041c1c82c14a01e41408a0a50040400c000328210405140303c1c500e102c00300010420a28190019003030441c10b030400802500125001d208008040c01142c040980030b1506000b6000101d40441c0181500f4961925142c0d80740b00000f041d045800d0509541c6005a145524030620a002a200d10491407612004000d040c08203401070048403d1001c001e0307002030310030800b094181c0559051580320f9030390740d4503d070142814065021000c00603c80903000c1b90400f140380c50b168440f041c0d40400440c080c01d01d5919003100e14004498140c0211502503000e0404280038146275240c6500c030a0402e0319820b005420060155044040c0d00603a8016078000150b2245921039403202c40f107980c842d20142e8144003040014030f100038403034450900188400b0340001002480542d00030b00702803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876058030 1250 876056780 876056789
    0x30a150c0e01020f0a0321090606061103070f06110c03030a0228080417070210031b18090e1e070302030d03050f190f020406050714150c0a020106090c0e0901 69
    0x40c0104e032107001c0803d0002c3c0f40c4c410282c040c104803c88801e11a100400c01c900081040c0400341000c18243c01c005c125042401602cbc166222490421308607403035180ea038054403402502144102d00d0300700226403543c0c440300c000014021528605a43d1030f00b61031a640c02501c05440712507002a00c8803640e010b080c0702901100804080c022040c403000801060000040e0024190b40c0c041180c0d4541303410b6600c02c0b91441c580c00f80500d05015014600a0000c0000c4166240101460050030301054405c002035407000307002c9181300e00200d0820500344000c05000106296a10510301800d20b2040103070344000c2200010f00080904508610505080000d0b12009006150501003442000707a06215402d40c418180d100c002402007036115071402070100084030543e000d20011703010a41c250322400078422540248074640045100c8095169a150854079440c100c80a00000c10b01c080841e1000b840941c0300ca10000c03503c25100e20440c0304440d814104400800c1071070008280d281040609a801030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876059280 1250 876058030 876058033
    0x50102070e040803060a0e0a0207140f121c020c060103050f060f0a090f06020d0c03270813030b0a0603051e120a09030b0a05190209060414030a150c0e0102 68
    0x241c41c010300c00300540070181c402004503401100041c11a107034016aa00101600c182d021050f01b0881c04170700082d40000710544000d4800102201e14103030010340100b1402100d40180420b0600c1c41e5420182d810201886104180c0e602c0061040d1803e0300281c0030400840003e0502540f5519006150040300a0b0342480ca410140412032a01c490a4100e075204e01311407404120480c0034a0410884214050014134051010030100b2401c820b0350300c89000300c242514200810031064001a41d104503560b003201c0c41c0410b03803095000082c1140c01518002e01e004886c268103d850343c2c0c1d001a400340841d0214509a0b8803c41003091103c20000f8000002c854440594400c800c4040c03940c50340d4540400a480e20340000d20020041d22039417600d002541c11040040300350400040b101d014202c01e403190b14056118468942a2030003e108480d03403603d00401192a0614202a0107040401d40804544c14022000100c0216840c40c1144400c40300c001c0c4002080c3d84115409041d00c145280c006046 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876060530 1250 876059280 876059293
    0xe091c0c02130f200a0e01090509010b090109170619021603080601170f100e0106021b0a0b2109010209011413031b0501030f0219030c02030c0a110a050102 68
    0x2507264400d0b01400740384900320100d00c0d40f0000c262000a050b19045085040200301003404408a8020250010b8201550381d528001c0b801d10046030715070898064640d000d404034004000340b1003500000d200461041c14090b02040e07072031416000d000e10741c07035054005403c42d4040000d091a6004c5804a01d1030a100071410040000101d00704044184401000d00400f0390102d4800c0e8042c1032070480d048072641619107280f81c16840502d502d11705503900719040d141c1030f40100c0c3c4e001403003a912741690801d900a0601100d08071104060011258409421114032140411950807180c0184916548000b1310602c000a04945400e5680300412030506030b44180086482a030b800950340d44c41201d1072544c00c2d104c034400b0400864501103030340001c00043c044060294006c09240c0c2e4401222400d0300d0400040300313409071080581c0300302103240e00c0c1400d000b81d103008218000d900c00e111014061048034100510454417500c2c050110307009840c24402c41c90040d48a10340703603e0071009000c0030700c041c042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876061780 1250 876060530 876060533
    0x6171b0a03092f010c050c0d110406061b0f0812160905010e030d0c1b080708010b030601030f0206030403021002040902040911041409280b03150106050405040e01060e091c0c 76
    0x100c00350010f80843c1000f05521801051190030004c22400001c002d0442c0b800000c14a00141d6900c1c9000d2094012402e0290025149006107000c00500109103411700b440212552940010395160104481d4460180803114000d106c8050340d500c90703d01e10b030b120701a02207400000390840d82185d00142c100f200301a0740300039580700401d8410307110f006801d0210302e030905d07458024140e9410f0030850841c0b1000c2030001800b180006507260484244038020807446200c42e00345500d89070240800703400240088503040c010f0400314011a44940070344103890528540d980b45100783d078060340c000c00c69286c01041c14840b802052203400001c3c414101c906141c07920b0302802d070721440414501144500c501c00005405501c0e4800303100b40d00c4480042c088001481146000c004060700241a4040c0c40390a8002241c2894070300218141d411a403030b80d5080c92300d401d04100107007012040c0d261881d500d42c54000307500c903c081030f050302919089000d060030100b03c211142c0392400c100d03e08000c000010344040e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876063030 1250 876061780 876061853
    0x1208070812011d070f031d0f060f010905040f02010507060209120d140301030b160908030409050a11120604110903062d0f1303030209100309170406171b0a0309 70
    0x2000d01100d41001f03d0b00c130440f038284d000d40030840899010079004401da4943c000e503002c5541d61203414400d0b0380c01c015980380d41c2c408085960407100240281210400c00d0050b6000301d000e0301d003a62040801601d403c0c03100b0301144071203001403008000ca034004030350ba0b011107800ca038003411055448045141150f00d5611004092030f0094250348261010180d80080c0d640704951600c0a003104500302c0b6a21640c0e4000b0a0061404944191981b868542642c0aa41c406801c841e405c42803c4034410060b00c0300004c103c01001c00c6090940c0307180042041c2141d03074500b404000d114818040900340480c003440c10711900f002a980150600f03010f00c0c002c0003041071203020016001000c805052015a240385410340c000e01c01c50100c1c80c0d2180001700c50b0042c5aa064200d00940b51240319080e54204000b41010514006d901515000c140560817000014200803401d5600c20048050000740740c007030b21082022030f8414004c180c000f0342c075010704a09002d8400a849000841a402e50400980058620 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876064280 1250 876063030 876063047
    0x80d082d09010e1f1515020606030c040227040618021207081608060d060218030d03110d020304020a0f18060f1d041403030c070b0105040501030206041208070812011d07 74
    0x300c549645d6503240740100b20183d0303d0400361040003013080140c00301c02c90103952484100c42841c8640310709110707102d5508041c000c1c0c03000319500f01c07405021091000101083c4101070fa190701c1d0040e5950300006840c01c120b540d2000746d41402203005a844a41c0c019801020000a0103501071000010900019081d22018481242030a02c0c0a03031071074540900040c02145c2c0c1d50006000e440c0007044004203c80c56140c80d1310000c004500b141c00717142c0d81070030135015201c2500000086035400e11890f0400d002d1034000316071140c40100180c4205444101140560140380c00641c0d10300f0103180e07a48401085886200c1c00382c5403500e12004698503009211903c5010071108440d0030119901160801800411206109041034103a030780301e18080080c8500d81c0c2203000240c40f111402c0c1d000084608140c81a14180c81d0050540c625290410784100d100c11500e11080391521410042540810300c10009410508104801507641d0f500d030078464020710081d40d2480755a4450307207040c045103941203c0f01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876065530 1250 876064280 876064333
    0xd05091905061921060510170114030709020d0617011107030309080d06080f1e0613032604020a270c03060810090516080d082d09010e 59
    0x4403c000510b40c81140c2d10f84824003984900c8045118021401303440350030950903100c05807031120913488000421180d80300103440320081c2500000c0144090503904010030304111000e001c41d40016a2001d0260899106488084140b6510b400511082d20b02c0c80c036030004441c0c0380c0c000f88a001c1c1ca2034120785c00340c071400000809150751044007008201d884010b59041c500008400c1004546c3c070b0f250031303460702e0b60129480620300902074881c04100461660700e0041c2c410000a208607a0303a0880c00e180c070000780b2820760038801e01c184d04100b81040d8040411411041500320b04c010304061043c00214401500202401085c4202140c1d080c1404100404003110769000403030f8913001c0c41e209038000d0203117400024003402000d0a807018120203803c0500302d54400c03021140d111802d01c3c0391345404c0b0700c0760069030100d80040645090451254002d10341018078044030b0004080100100600400c00008401c61141c08a00300552483c1c284a071003081502003003d45920701030154105468030b41000c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876066780 1250 876065530 876065557
    0x14031903120504150c020c041b09170f030c030a09050a060e04050a270c1401050a0c0804053006011d0411040e07210819110d0509190506 60
    0x14050018207162404e0036544108104004080c80398000d403507804440207140500c1c00e24240e00c5121601c103d404400e100c00769214400301d424050003c240540e440c00100e11440340c451018401c02090004101c6200a0fa008560711542c402d000342100080703a118604c41c0d1304001c0100032150f0041d8100300b251108943c005015a203140701d03400103182400a6140507190400d080c084810320581c1d1000460042030102d148a696007824210208102403560000c0c800f40716204c00d00c0d0280d80e402c0b90749841020700e41e0505403900041603010b03000d404207e03078013200500c44660301c5402c10315a00039003000303030068282903060140b020001046200180d28440c00f2100240c2440803851014074407441c000c1c01841036240806806948a200d4010002c03106a8904141c10703260060000407006603012070030a0600c07222159031000c1890440441040c007541c3d5003600b26500c4140003241440d642a1242c507200c10403042801421032040000104a004c030490500542d80c40310241c03804040c1100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876068030 1250 876066780 876066791
    0x7140d0216060915020f190312020403081222240e070b0c030409230709060206060f012303090c04060812030603150405010c2a030e0109080303011403190312 69
    0x984c120301d040c4c5040041540c501460320910241407444800c00780e01400b0b55070b01d040c2e00e004441c01038100d114a210040943e070f02040b6900c00544c07002000c5601401c8903400d00c542c0465103800c0b42151024540850780c1c45420141d207400c008498840b01c040e611591000c104001c040a401a84e442c020700484048500100b00c03511100d03020011100070701080f95040c080d0f80c03152190780c2282c0c040300607041d05243e911701c00100624480e404000c116130542c0c1c010109610b4410510100450400000341044007801b80e0242c016800c5017400480a42d5100c41c1d42c2d1703450301c640f459040c08404560340d48030b40d040107030400c1030003030004040442c1e000f20082c0558984403113000a1620145120100d11007243c4410041401419070040320344645907140e4600103604404200885400900001007259043c0040d0000c01d1007a5041d6015040c103040222519172500da03c07920f190003d03400840e010250115070091814140020b004201e4140c4803103680c3c0003241d5010780104180c1074280780059854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876069280 1250 876068030 876068069
    0x1704020a050111250501020f122d0c1606020109030e100203120c070c050a0302011719092d021e010e0a0b0309060c030c0a1407140d02160609 62
    0x6005074004c00d2400e18102e41c0410f980504210941c0440c0300d210301500070421820000b210114076041a000c81c003050510300a0a5030207540e422200040e507031015a0440d40400d0300c080c6800c018901304100300010003180300d9540f81240e418681d07811074001c5904042c0d0040000790411078003030461804440c04410f18004a50032031540c0981608903e8055284060103582a440707002817014500079104104456103c0040c4800c208840c80024000740f00d5000c0220002a20386009400023200050603000301140ca6140c02652908403041d40c0c0c9000b00d4003d43c0a0b8015070000454104902c5d00d42ca2401d00030f90000f5074080001d4146007112065802e403810581e11a0f40303023000440c0d009101189050f241c2498040329041102c120042e40701f100049101140380c00240c03842201d140108520388448944101e03a0140700072005980c0c0305d800d10079240020f0040d0001c00c20038002000901050a05080c0245011001080303c02c103101c0301642400750030390055000e07007a50384080c1c0109420102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876070530 1250 876069280 876069283
    0x9061b140c0a15020d3c021209010e040b0406030c180b0414061c02030d1d092a0d020408010212070f021b1809030d0b1206040b2502010b011704020a050111 68
    0x3212980d055080401c5c81b4103868156541c454801c400c50f0b0072076182c0700704c2e4141c441442c4507800740c0e0390120b0340d9400740c000320b0328050b000305440540152012881e5a92a581c4501c81501d0382c010f551910a0503c108007101100d104d1901c0000d4126004d02c0040015400c2006000d03000d40814021920104540e582d100002035425001d50301904a811100001c3c1c0e0050800300c5981440071450328200a103222480e00c000650b02440411401030101814002008500d10740c1d01c1c2000c0d404a41030144c0d10b5807403c503201400060101600142c0e650400c05020390a07000020108428003400d010845c0c4215400581060300074840c07240e40500680740c100040440052003540350381402c1800800142c444044094080009410000c0c880082c4582c00c01c901180400700c02085544100c0004003c5000468540d401015800300f12402e908040800d80819843d18050380141c1e4507035140d0b864070350b401414414559500800f4500782e051690004401c00481d205140c104140d401342210180b20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876071780 1250 876070530 876070577
    0x6031107050d021b0907120509161d130f08070f120c0b010812190c05030c030705070f0e041203020c030d1e0c09061b140c0a15020d 58
    0xc2203812541d007202d03642c200950740c0d1a451450740300e6801d04080c4c68020b04161080314003a0710b0545484051071060552040201402003d00c4418840c1c1141e9002c031710b40560083e00030309100004001503d0303440d0310015041c64060907030102000031040b400b001c11444140f80385080c2d0312084041d5503510701d0070110340551440c100075014080403550b0300b14075604010074880e0244a262455103981e616401c0396114081410042c0035032004011f49005c0d03844102900d102c0c1100e46c2898580c8a019859181c555000204031003070642c40011944103210003042018002d0011315a20700b5810f0502042d00c060b0721001c1c000030311841c12f90914003100d41c060b4041d12a070480394022261103002c0704c16180c001e04902c400c1603011740c090450003889080b107070045180c05422912080b80244c80c042e800c480810910205a03994071101c2503400009002290340d88a2985610050100070622820000104005d600540d2000304006102c00511f801140500c1001514180b114012072200900c205615 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876073030 1250 876071780 876071783
    0x50d030e03070b03070c02030105010e0c0f0904060305030f04030b010812180f09150f0603060d030c080403020405101e06120915050a02041d06180604090b15040b04110406031107 78
    0x60f80401080282a4000f00ca6491a030003180281b1003642d81d00510108400151584418030b40104001045039100d03400070010f41c0300c0a400001c90f00d07aa6110b080c10350f085079041c0108403200050800030b00c0603004201e40940707103080240c00f2500007201e40400d80e10842d6165005000034051009140c1e4420610600414010703001d07400501c1d18420010001c0c201c03a0440341300d510320761210740050030400d05803841080c0c064200c0303c20140c1d584054500341e1074078504aa9802c41040040300584031401103500941010011a010f2303820034483d5140d100c2000c089401129841c2400c00c0241d60010940c00840510b6a0010311201c0c20305040b1406400202c051465034281424800608612343c02802250840c0034040240040b500e00010301c03076010340b0340590000e501a15070322201459110f00390081e44c020300024a1100d507540c1c126410740101d5a0144030011b5001c1160313103003030a008a40036000b0440d030800c10a00504448000e070300890246508055403001400c801104002c12940c585 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876074280 1250 876073030 876073049
    0x112d04110c0607020c010f02010501052107080d020a110609011715150d0627110c060916050103330812040617061315051203030406060f050d030e0307 66
    0x40c640440f02075500c07032100700110f000500c524841150701d441882418140c0740300420f1006220f047c0700800a09280b2400c0c80c440c03601650b000010f06641c1003101404009054001d40504c2d80141400b46036024801314090051030100210300290ba4000c0071640142100c804400f06502c0f000c400307140380e00c810300115400808046c07030340c9004130254010b003001c0302103030000f1f2003c107442e4031540011420b02c684012108984100c07018188090f13400421001810500d50360816580c040303054504801a00c40c06c8050300120003c10900e8100381c020000b5140a007000d0041d03e00f4000a21842c010441c5038440d5200003600704039160010441c69801031010000300e8800c0d41282c620344007141d00ca403084030080740c00210390072114410b40060070b22484005100900454110203c40c025000c802001050031151010103d12551403030011841c020400d0000c64072403a03d46001c804a5a0710307002540f0710707001c020b02084265502e030200e000250345403600483c10f00f58000424681642c03504000003a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876075530 1250 876074280 876074293
    0xb190b0a08070906080d170a090c0e1905090307031d04060305100f1b051305060f09090c090f01050f1c023105270103112d04110c 57
    0xc207000001c03540151070350b451082080e0b030707075504a2030f50307a00018490002013a9200000503031a400c00c0c10840d441201110007103031443c0c0540c0d0342c480702c6499810002e00e01d12041c00380400301c1100090340001c580803c00400076070800741c2415640e40100b06004040020426140b00300400080880c0c01c44840504140000c548924141e0345a802a0220300074980c5083c9081c0c407401c800d4042c44d068408002c04a800300c4503014000c942640c01540384808102c9001d0000071251036440c01004000b1152040d1521000300c481000301c400c4018002a44041c4140588900303035545060100e841242401d12517602c0007140b21501c1c1074040c1311129000003081009101c0c403075207640c000f00b007124540201c690040c1c40500c4a01e1040c40d180800e5040d42c007803c48180520301f031412400324212136001c1c1400010012a110034000300003604100d501000001c1040b001c0d00305070702c5050304d101000c070442109444404202c91100340340d40750144102d484d540c030356048003540800c5688030704510081c0d580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876076780 1250 876075530 876075539
    0x1e0903050f0c10052a130e181c030f140a0203041401020705070f06050307080c090a050a030f21120c03061203080103051b220e03040e060901120b190b0a 67
    0x4041520b2241c10742c4c041341028142044480e044500000c1080c1c01b174a211400d00c2c90302d05e4409401420102c1c040304203981c0c1200007500b0003440c0003c40211000103030404002c007008003680c09a912212059060416030b810501e41e07800000e5201c00041c400507140d43e11030400c0206a11001e0005046510014040046c4600480e442040c3d519080b041d41519a42c2c21048a8500c022103a502c005811600414800740100005156100b0010b00b43c080c050307100c00025554030250341c0100d5101800314441d0f4200080101c401040e22044001030314651580c1001a14900b005e2400c080e00d40d0f5140c12803d10203010383d00520161070483d01202850520740750181c01c10382c003070001340c66a110701e1000b0400f10785c0e846506503848801406143d080100080300b0510781540c1203a94001c0c68842580c003031280000c20283c001001c4040d28100281441802e10180c0e40c0185c01035954200e60ba0011070104856104264000c0c510314001c18458181891040c000c00303403014003a40c00350b8107100005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876078030 1250 876076780 876076801
    0x90604112403090a0b151f121505040f0e0706030c0f123b030901140d140903220f0e04060b0a080c010e0f090402150904050a1e0903050f0c1005 63
    0xc90300740042d6100c50640000307101035254075080c54180d000281c1c1c231501d607515a04040c2c101c1d1306d00d1220045104202600d032400a005e450340e1040340421155140300d18134881c281003100c40c0086c400c40c10108601d800d0080010010740d546110381062082c2c0380c19221036140c090b440401c02412500c1d40f001010b01141d0440e00400400800040f03000340440d13a9208000c01008036485014141c542840c0d40b100c4030400a169001884540c14107503070313000203e00c3c0503d94610140b049003803201550740c6204400810746414500341800210700c0000c035042c0308420340c128a000584038a200c111040b50390341d1030f044024014140105800100c00c61001076044d2001a40f207100140036281c5109400400c03042c046075514200c0e51a901486070000b00380541032038800c18000101c0700141030f24000910300418180e502c00e0303e6a50310941da4000c3d1001c1d070020305090036203048207401300340040a03154030000c00c0d81c011120007507020007000402c0c25590800700145401c0c0040b409040c03003c1d180001024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876079136 1106 876078030 876078061
    0x90b0f100e011e03090c091b052226010e06160c060c020a03030c0503060907181d060a15020303070e0414090604112403090a0b 56
    0x11400b00100c4030042c140981551000724860003c0d24080410041d547d0040d580c0c1c0d46400d105000c000210f012040b9102607600d40307162102c2c0200c40d20740b2000700f41d841da4404204030a01c0050308010714502c10034000040480c000f805180c00d44110300780c84050b10103400b00c1e0880320024802511041c42c4401070780c000d20301841c01003c1a65444120399001844e000961300410b070080c10942d00d4003564108030605d02e0040d0441c1040303c08110f43e518064402030030700240038006441020700021901c000c080c104240303821115032100031042560142ca5103401400c0320f41020816004803109000b61400030f070b00862441e80c2e26034044550400c1c2c1400503501030749407209001c2c10a0b854003081e00400542002d00440d041c10304c0e0000c2c9840c002e60540b80505a0710810b00d040365600800711154400c100752560341d075664201c00324100400c400b0014268503482e03061114009031f800d5070 = true := by decide +kernel

theorem cover : BRFrame.Cov 875899280 876079136 := by
  have h0 := BRFrame.cov_init 875899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875899280 ≤ n) (h2 : n < 876079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
