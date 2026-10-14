-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:02:53.712248+00:00
-- url     : https://prove2.me/submissions/50caf842-34d2-4c36-b39a-880c0cd2cbd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53417269 ≤ n < 53597126 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53418519 1250 53417269 53417279
    0x4150507020a06081f0e0f07030e060703050c1b1b1206010504051003021c0606170304090b24090306070e010804030e0307080706170a020a020307060203070915080709 73
    0x1000340c44540758003038549003a20381091402e0790624002800704086032104001c9140d101d900e44619001001403a1810f1850f05201c6c14807441c01400810801c28582002005101003500058842e40050503190002c0c1f6070300c40700a20034031441105000c0c0e80f0700701500810f0303000c00320200c1c4146010462003c00342c40d503070398002440b42c4400d034052030a0058118500401450415400466100285c440c51440680e22680001c1030350701a2038013071318948424045107040004d00d01c0780c10090901001d0125160182d800103540c0c921950045000707503a1680019241c0e9200c0c003603000054100080c200b5903d541e460b511704150340181b4a224030911034640440c86040c02030141d207840d0001a5139069040c0e490f83c9096510703c20780020160544600c150000c1d80c090140301c5900a170040e81d4480806002d001c00303000c2c0c8181e014142d00c1c0b80b503104100710480d0f00d40000031603100130f0384134002586a56401d24213550803402948402440c0c140c8810824809502002c400d114094036101c4201c055250 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53419769 1250 53418519 53418527
    0x30614010602010e030414060708030106021f18020d0204090c0e0a1107020a051915050c010b0a080717030702060406050901021603020906010c050304090603050c09010902030f060d05030714030415 86
    0x2410304c4603125001000240a50040500c00316214880a0001c0303291424540d1681030907032099005a0060300409c42c81140d00360400e88865581040b0349040c0600ca00d070301c0c468003201048010003440364010703040c100d0841d110754020058454010030aa01c01c1569089685011001100e040c140d60b8038220400c10003407611010b50784c510350007030203240b840b509150a0081c0d00c1c0b001103a1000f0080c00071000107070a091020700c2e40d40142103030b681680b16010380740c10a0944004150951183d030340b0707200c20b000c0c0d0310000400e20201c4008042d024000e4441c010068214481c2403800794105100250100740190071900908240000381d00321210800c2602da410b00c60702c440e02000350b00c00701c401e020445942c031a2401c04202809001074901c5c250f074800381c200445000b43d004407103d401c03068410099290984910f0f0040810794015865460880e01c110000c120040056100e41111403c0405009080099400040d481144403a0103040d21000694070f8006210f061180450010056041445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53421019 1250 53419769 53419781
    0xa0b030919021810060e030f030901030903090f030506061c110402091201090507030b0906010608010612021c09060b010504030201051b011b05070c0f140906041503061401060201 78
    0x241014049003034088001040c1d4000c03810301668005940403594141200001016010f030310a40040c0040c2c51070030700e010b840c40d00c1070b003c150301c25003040b174800c2840c41012044940410091070000781e04180c9140a0712094020780091f000021500c10100030854001030140c041c140c100c8104030004190074104003220101d010041200f41c4640850020b81001e8014211480c40205800c0c050000c8501c1c4508484108200b0f4a0342d070b000d40000c206012032428140d0b0001d2558001d04910343c1001d001a01d101410300c07400c1d04106a0ba09018002545641130b604e940082000d00c0c0c1400d00c1d0031000b40090443c078602030740d0fa00c1c545040602c00798050011502240d90603100c043c04d00480c0141403964020041c1340104da95280c0d02da480c000c29400c41040c0c00c8640b20b44405499002c50708062020248940040415440010701413101a1040c488044014012560501603a41da04040741c00b410141d0401c03004008144070110800485402c410342c2d03c079120399004040c0ea610f000881c00c2e00c01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53422269 1250 53421019 53421031
    0x607080703030515040c170711010906140702070e010b0c10020d020705070501021603230102071b05010c0804030609050f030a0c0510150b0313051b01020f06010f1401020c03030f090a0b03 82
    0x2101944c401000d01f840c07550744d0050607030801d80c10110b0344002c0c0380e09503a282d03042102c4840c1d445000c41200012400000e4004205200901070b1a0800e40c8074001d03076506008180120030302007140801944100440880012100401d6440300f080351510806900302e0320044400707000d80c007408600d0b94030001ea401415840c2003030304071440b4656140c94451040040c481010304c6004000101c80c403009000614030b07035100301c8022010009030828800b01c0d14441d042281001840440d0001007491402a80e00b03aa81041000510380c03810710b40b081c90a500d950a0042601000c138520b810710344c01c04001c40c80140554151096201e45211031006c5aa80f601070003d8500c1e80079003440b40803034038000b4581c032042e0000d41210b44001078441c1490b0020310383c020240140f081c41e01d40c00e0380d64180302d40e070102c80910000703081c503506181e02815030f0b200c1e038001c65601940500c02a50b550303108120040900703002506503a5145048226868140c0c0598800c0c0d0080010342000102d84110341c0840744201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53423519 1250 53422269 53422277
    0x8040804060c0204291201060b07140f0604050c010207090b0d060c050c060109020310060c021e0a0b03040b0703051609030f08120a0f06080c1e0607080703030515040c 73
    0x54240720081e10126000340c4140d03080b0751380b541054148011550480d4207004104120220400c01e02c00300081e10000481111a81e414840308200d10390051080e40d02181c2d0201505140602c0810740c9031500e030b180842d041c850311032a4140b005005011032613881c021000ea0070b0b00e10a94485800b141a0394212000075005a103d08940340031400d503520005201860f0303e4900c2c81c00000c0c09400340307481000e030172000c070056000043c410f00000070342403074008000741d0810f0201410141c00241c101d542c1030111400d415001c11000500755180041803002c2c0002c0c585141c3c8078203040c104032020180031a626808249004042030304410125400a16815a07030b5429080604603650a160001030350380480e0071040c04d11010743c0e0100801c40d403901ca5901d01c54005441700031050740a00360b03403d65002d4403882e040720400400a07190b074801c5041e0304400c4480c0c1d8518100c0700002c6460b0740b1804001030062000410038008041d410b0700550b0051100000420440c405041044221500c1c40a428041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53424769 1250 53423519 53423527
    0x10204050d020d02030f0303090f0706030c0512060a05060c0604050d020c060406120f020414040b01050a0e0910170a0c0b031014010e10050703080112020f011d03010f06030b07080408 80
    0x18030f06555000d5030680f002d002d0b500d51030070210741c0c80e1440c0c00540d6071100d140c102083c003c10006040020308000c22003460b00340010340b6130500c0034080d4815000c1210318107038820001805c940344c040448000342400381669940d03100c01d828880c3c40740c1c410799040b607a50054038240600f0510000d5280c0c143c03035004008514207444d101e800e81ea403000c1c0381c2903043c12035102e1014022003d05031010704024207066610000e03a44180007044115180f954542d8107204090048004880c0e09c2100c215012070190b40b0f8002036218101c030603100800c1c507413004521103c1d4404104081c200841c08200740307449204a001c10342d466140c03000560004035500343c0304c0c8881800410444a00c031102098030001070403c2035010942001141c88148480110b20204c5d030700040d007000301980a103055005000400080c0040c0c0702c154002081c58842d110050304121f110072042000424074803500c610007500400170841680b400e25100090005440240c0d40100c8000003d0b008500a80d5614030480e071040010b854 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53426019 1250 53424769 53424773
    0x501052b060902100906020d02010e03030a020a0e190305100c0c08030604090c0609060e04060503120a02250e070305040b010302040509030702090408041401090e1506090409030306090509010204050d 87
    0x1554841a2099480940724410b0501507200c03050340141c204d185a072000c502904020019140140300d10010046a1401a1201005c3c6002c0306030794110003c42c00142c5e5812400c403084030b080c04403424007607024010030340c010f000000d10b00300d000889100384282c0e400d1507105914001180d10800c1d168000c034101a0f0000005811840110713400f400060001035841d40750346800e4410042c582110010440390881449196080010159080710450b82804807e080001080e1920040c0c081058140e2010900c9071042c1d000b030081008080302c5a410080480100050150f1760b0300500c2403084512030040440c0c0f00d0f610a00416210f00d40002405655901c0e5a00303201c002e1400a2200d04da87c00180450030041c1d440380416401140202c012a0302c031814440c621405c01d221240b0107040c0000040100004045040500e501090310581c441500c2814008038445200b02c107a015800362a0605100c2016050340c409000d58000c910104030a07a01d03a00ca0303070700700e10071401020382c805031540350000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53427269 1250 53426019 53426089
    0x8040204090c0b03070c05010b0a080a0803040c0b0c0d26040f05070b0705010504050f06070c1202010207020414040b070905060904050c0c030301030b04030f17130f0c060201020409050105 82
    0x40340074414070560342d00542c1c9038081c5055400035960704000403001c0c164172007441002d010b2003042c0c050413210040141e1a080c28107503501c1040e000103140c070340080300060a02a248407100002e01b46060001d6641743c14400c0b00e074968400c0003081d0007044c4840b07001c0120001150945072840c8a0060813460394540d45c0f00d08c6a801c0140310211454821440045401e002660181502501c0740c2e00119540c00d0500c0c085061003100307801c501381c039031100040207060390784851066601500001e03030580701000303c1c000300c2c0a44950754020b500181000c10203038145010070f0076640b18a016248829054907035a10072140c815140c42031907800304d802c1c804280d052a16030f120a42249014403124900881c85059504540090b801500d41990b5039040009144d0003662204581c001351170400074884000c40c10b82e40fa580c002d481c0450310458090b8480800c003e08000303060f05500b12203505c003d10381d02c0d68001d010754403d00407052054180b80c00040c807800d04400d840d00c1c4111100002240c0707012505514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53428519 1250 53427269 53427281
    0x1030204021b12040f120201050702131103130b0a2f120a02031902070b1305150108030306190509060405040c0306050903091e030619110408070f080d08040204 70
    0xb0089007049403440d08031403420420511410050490280c495140c03160304080c2c2034141d408a45011032402d285070060703912000f2218040e82c11100440c8881c803042c240310003481b0600c030885a00e100041071020f101c08510564a00911901e00c2003d240d40e042c1410090381d10065612103000d201c0c3c030b4019055040d0556401c01000000c06143c1011880e50401091010035580d091009074000240190600c10032020000c5401c420000e40c0340c950980e4030582484002401a00c1120482d45100100101805070490540461484100950b15410056105d03441961000c0c80b66070182c0c41501002a2a19201d0485070300a05201c2d45035248003d100103030070002d00880362109103000220000d00544540340c06a840d8000a640f03a84040080c41510b421256000180501c00c1011566550300001d1a41d0301100130420921042440c50303100015050407200c0107211a8007040104289400003290340071209546080a911960740010340d40341c44420891000103410040001c01500b00781d0400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53429769 1250 53428519 53428537
    0x1050103020c1504150b100e090703020c03190e0d0b0417090a060e04050a06080a02040b19090911120601060503060612010603140105030c1e0301060801090b090d03020901080103020402 81
    0xe511418800386030404443ea044038112005034801c04042c1030106544510060000142c652198414148401a12040e81146002d11413110310000495562098040d58520303026001220703152002e554011200700343c150b56160006268032210000c62030800c2c5840b40c4940c021112000580b25619600404900e18030524040c2c141048450190740f104000e140041107565030b000c80c158040700c01c03c41503c00c0030704050311090501d2010b110281001c2100380d640c5134100c800050956403100841c101805504a00050300d4020b140001c5508442d08100c0c06584104000319040701c0f1102000100d418102c0d6200d0903602100c01032141e64000d900550f00880b0007020507061960030403940b44226005d03000b21001940311a0704100c040b00640025024050880182108400200100d00302c2c40c0030031100c5200c1c0d1010301c00c0c01c0c005c0c7c0342940990b024010b810b000340024007903030602065003201901c03141c019103d200c0100400600c24403ea4140a40507902c8410b182d203542c0810000e0f40007072030340f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53431019 1250 53429769 53429773
    0x7050f16060b090106080709061d01030507020a0204020d02070201080105061204020118030203120d0c0e100509041104060e09070302030f061003020c011409010b010206060a06081008070b09100f0801050103020c 92
    0x10075580d503407800c924000c0491b90703501c14035803900c400c0041250390a6030003103091061040101803025940072b100105031b0000e18002a41d961030300b400700c0c905245140041d400c80e100081d4042d00310340e2500103001e400c0c000e0701c2e1011a0307641c401c103003c0ea500c5002101d01204030000c0210b801503208020362094030040103480700016403039030000390810342040303050081c0c1c85000034015001b00050084548021660410314102c015030070104213444007c03044001040b000040c11803690350365500105606408101660f16184c440d00301815405508000c0740c4a4034080000070740440c440e0084900c201c1007224010801c0d00c4507418454000c3c00d00034a0b0090540038400b000040700240309480a03070b0940072304140181480b500242c00c4804210689045402000421a003511841e942d601140d00a147c00413240d5600504000a13200301d805c10350680c040c0d40c00015070003282d60041d0034580e03402c4038550000c1d05440c0f03098404a03448182d41303011440d00b0004001d80d40c0280d0281c4200c03441982 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53432269 1250 53431019 53431031
    0x90f0b0304080c10060504050c07030f0e010201020c01060e06150f04061209020d0b070e0301230a060807080321010501120905010209040e0a0c1a190207121a07050f1606 74
    0x140035402c00a2850f2558103142c1d41740c00801140c40d0a018960f0442c1e50000d450340740c40310689004001c00e200c20104024002c0076031010085900c01d604071840b00480b1030003040202d84850700450800425240a440342080f1415440e40055000c00c0b01c96000c42c2038240d0f481c203858a4810b4902424844404a0b500c0e1740b41d54203000350f240e1104504c800d9204141a4030603141c280000f03441b54003c0c00c0201c0c060fa00d1700d041e8200103801911b441c601c1e80742d0320442c45282ea0303861004030050040c1e034001190a000f00300d0000740020000000d440c4603100f52280710384603c0c1c0c4107060420504244070303050014185004072a030311065688803e108601a1001600c1d010f00b200c0071600340d801e05402003e4542c0300401c14000d000351909000081c1c605400042511a00c0c019582224002d4034400340a904000100a8015000304840740050400b1040300e05614940d0900e051301d80321000a010020100d00300003113002d4890001c8031146441c0340006030034690a1603645004161300b01e0200c92040e5030b14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53433519 1250 53432269 53432287
    0x5060402040906030b100602030c0a0b060f0402130e1f09020a1404060c140f15090a06060b09040f05060109120206130b13080115050112021201060e10090f0b030408 72
    0x3025003c00b03035004804075070190a205084c07000741c0605921007000c64200303000904009501003200080590000d15001558407424009620204244044c80d407062001503c0d02e409614141d070740d030032a4981d0040b1082a9540c1c03500502041017202c0c00700f109011810144076412003580a006980194a020600e880a0741071540d00c80e03100b03403ca2400f0030103041d2614200b08103030301c1505028444e034000d8915607241d4440b0ba60394055001001d0f441c039102c100010302d0f500080194003451508041e00b40402d43d0743d060010841c1c0c0c080f02e040380c004c80c01c0c0203215680f0149401514003802c0d041e5592281c2602e0004165100706402004981c000003c10a9a091141e400800c03c050100c0619007507607101003502500e140043e81c0d101c28016418510070000040041c0005800c0794020b080000500d0a2541d2410003031003400d030030003003592843c4004500c0651000102e804440f041e20b0a10441d510101c0a85180c0c5440c0300f1801c113034652440501111000c60b0240d504144282c00850900c0300c64 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53434769 1250 53433519 53433521
    0x60a120f0e060105040605040908070809150313210f0806010201090212070e0f01120b0601050412120f020c030303010306020a05251101050306060702040b0a0b07030c060c0f12050604020409 83
    0xc0c0c0081103600102c0148030b10f00c2c0c18820000100b0003141c00300241c21441c0d1700c07001daa00071408054051030010825804546642c58036400352003c4103080c594a1401f240301c0071003a0310f400d0003541d000721880d022400c004040d80c241d90542d001526252010340c1e48480454a5142c02040d42b411075480301c00c440016202c030030100f41c0c0e01701000c01a100f920b003071691030b0701450320080c240c031102c550220040040f4058030407140d4240350070200044a5980700c40050311503101d80e60108085004241d00c039000c2c02071002e06400080300c2076458001040105004a80c0c2d0348d20350115903030681081004000040031a4000c080c591076500b001c6003040c00c03a404210344511500071020350410100c84120401c0782e0b04810303a0a070003007402c0060650500d20045540b80c006d241e0000d011790398900038000c0340e540c1e2804540081443e20340043d521f00092a004202c000309510486070b007828034000c0040c241c041c2c581d010748040c6a51711004c12881a508902c041d00b4003805003904203500f08804544183c071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53436019 1250 53434769 53434781
    0x1e22090302010203090c0d0b07120204030206030f090606041b08090f0609070f0909030f0806030c040507021f0501050d0b1f0b0403031b1113020906191706060a120f 72
    0x41d800058980c6855062541418a0508510321444108140200180b403501071030340c100c001480e00c02c05803844540c00f08028070498201a522201c04020050544140103816110b13030b00260540382c0b1a1600c5080c0015241000c51620b002841c4407112a030441c031400b0b140b9030103190041241d00c549005100c0d07030304200c3c041d20150380b1500603020030700c210703020215000001c101c85001044140d5268500400c031000348210b4000b0041c0304004600c0507601001340812802c401041004207090094000e9501d25042c407801c5010282260000c69040151083d541201c1c8058280d2121912030354031041041d0002702b440c020904d4568400c13594120000305100984400c040c0c10355aa030841c05d01401c02038080c40905014a05441c00310001601f40a040c0980481a5894000784d610880440060300880414a13080240821150103a81c0000d03a0b041c1c060000b40c8641c044440015074216030400f044442541121003044a40483c07441410040d0f42a00a014001401c10b5058000d00507180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53437269 1250 53436019 53436023
    0x30e0f0312160602070311070b1c0908120a0203060a0b070b0703050c0712020321070e12010b15030103020a080d0c290406050108121303080c030f040909030801051e2209 74
    0x74031400d00e0786010390108003800140411000c058208a0912003c1d07400761107500c00030f041591580bd0b801c04000115041d0b03540c1312040e28402030b55180003107601c0c000f5003088945e0b074402e00307010070009503140b0508202d801c51a00520b03400d00580e500c2d40150b01130a80540701683e004010032401d030115950318401041c01506602441d40d078107540500d00045211152744400f03c1c1502c3d030500107180e4010145244c49001598480e0340003510710110f9004040145803560403101055480c01c204000300b0055060b64402c0ba08440000c0d261840d1a035205607281030340000c42c05d412860000f0800c040200451107404031641403036080c1c441c0100ca405081603504540340ca0700c07036005000080c02441141041100088442e00f004d082801000d04082503100c00f609000300068000d060120034030850300c07000010084203030b81d50755901c0d4000080080503001c1d0001000f9000101d44c0d45040188210302d06208000985079001180401c4844200f18403a000e8600d446140424007050f80c0c02201d1041e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53438519 1250 53437269 53437277
    0x13080403080301050f09090a0b0c040906090b0414041e02060f0c0109060b010e10030e1c020d02010605010e0a090f0b040516140901090b0a090305030412030e0f03121606020703 77
    0x751504c01800940c01086410b144102c010004105c0b18100000d0341e01c00954110a88490980301ca180141062090f60000030911b418a140440c18203500d4210020180c07054808001d1200310200c00614890309171401031000c000e2410f0862a010a800750003c02e40c001404585022002401400743c0d62003400010160794551800009220b007030310034103440c0f082c00e0a001d92000d030039100044400c40b030a0340001c14960b442c4c0d41440d0740b01040121103401c2c0c0c1c51061100860300d4a640281d0b40b2540c08030303980019800c1c140085060b5208242d611050384001d0b145205450030030f1130120191446110241046a0b0782a2650b0f89554601407075001d0002c10a80340360000050302c00520048408107204441d007800c0000c20400d0340c2c0800d01000f2240d070100c0e184e4540c20140401c07503c01040380d0000c2c1c018032000c9000306502100fa005030710f0b5140308c1e032038000c1c4500c110814450261014800c0a50582001c4040caa020003800010210440504000c2c8070764030b802c0da1910101d0b004490203900103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53439769 1250 53438519 53438521
    0x5090a0c08090106050a170a0b070c020310060b0702040c0c020a0b0306040f0603020315070903050f0105010e010608060a0302060a02120315010305060108041e1113240608010e130804030803 83
    0x2858010506641140c0000b00902145041c640400c03640c4059201e955034940c80308810603001003050000203402e96001e141d00380141000ca40c0284040301c1c0341e030264803901a400a003540e00d80c06110314401c41381120481424140940c08000003003140c2d12003081408086149000140e551441d00070140c41043c00b415180d0a00ca01400200c0342e140c0d204000161030300b541400982d50006014400c403d40400305072841e0344464007101d000c8025440200103100d0100101c01c07640064004074140c41000f4107041050307907200403c98170113400340c07106034100803252b00600141c18031078020030300c07808180101c0d06050381c00076121145900440386810428007101c8003003800d60341401500c0e0801b5003441e2034169800c05840d201c0194800307922624807034242062080400241050a00300c514000b42100b4496101c43c4919004e0b1501c0840b4804129600000c8403266086051640030b94180b90b8514000c2e82c01d280180c5150030b03000c0c241d89801d5078062802000181304100401c082d503c10b803403550316 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53441019 1250 53439769 53439791
    0x8030f010320060414030c0a23090403050912030405060a0c02120a150c03110705010b03011b230f0705030c07120b0a1e0606020a021306060813050705090a 68
    0x810b00807819040c2031600511460300303581c5510a990039903031003034800344074412008006440c090a411105411420065000032921408520034141a07000d00c4100090002d03001000704040048030010081501400009a103040070f140700701168208004591030b0a842c2d500041440c1c000404160000366002d00b02d40c118108040c60b0000c41848100501600445698a10203900103510880d2240da4980706902d202c0d1107a00701c8030020f9a2000381d903544004500f0018007a208100b0110300035802c2c2902600045100340b51546007402d165101858a0510440804281c0c9015440f40703108200384080c1e15100701d020010038540c0c0c4550025039807106094100360030054254045105564003401e0103021403a00742051360700c5002d84d600010820030025407042140c01c0c01c07070002c0e0081d190500c04a012a0002a900c240a0089418a540f90805d606000136100c2d1030044600050501300840d440303a22301211030085910983c1642d80c05510744000c140c0181d801c5496000c01900c6084507a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53442269 1250 53441019 53441033
    0xd06082e0c02030301051c060204122001140d060f091515020c011b171e030603031801020a0807030e040b0303070c030b0a020405040905010e0123010303050d020708030f0103 76
    0xc0394195a0000344903a0008150294036400305125940c010590000a80a41c002106202e0790f00c40c1c2c4250110f441e95103407207400c2c840092440080b00d01c00124000f880c080c11a5051004412070141d46824845414044a5903a500645c2e210302d81c0545600001c159282001c110390003412000b040000e07540c0b04a003041c2e00d41c00b29070380811700c0444609008101d4503800b00321580852400c0c20400b00007c81c1a02e08441d11404a001a1840b5000d281540d4101c0d4030000131700540c184050a103401d04520020f803070603840142ca64640c1940100802e15150450300e00110b21040b050040c0c0b400407000351180c4510394000c000450005502d6181c040842c60303d8400c4089800055004500303000c1295102c03061018540401b82c000c11900c80000c1740000540c040703a0140c1006001448400402e24041d4007074602d2800b2400e995081018541c01004a4101c0d5000f01140d8225400580d00e552016201a40410f00340700070341d41c0800008000c0341d6107100a601484140500000c55031542c140f078a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53443519 1250 53442269 53442343
    0x109030f080106020d210e010c030c02030f09090a200901180302032505040608010b031018030503060d02060c1e0723120703150b0301020403030507080d0608 69
    0x205100341e14005104041d4002400110300c00c1c14200300c0203100020016100f0040b0210050074401e00701081d0303401484040d0495079032281d150300d050105d0b10108034180e0300ca009410740401c1500c03050040543c0b91401c54040c541100140000182e412201d00c405801c01072a0341c1c0c112104400043d6103c25540c0c41002440c0440b40c06544040503429580040d45a19808410229485600e12294505202c1202100003020010010080a0303680e00c07281d400303884401c0d2400e21034001d10000d440004903c0c010403c1e00c00406031003640800c032665094070a504080c203465000194042d405005880365002082c07000011002005094402e540c4090300c13000010820900d034014840400a5491404c040c1542050380c98200c00700004140106070002d0701c00b01e21a400e481840000402d10101e014058120101e41e18140718401c0498185800e03442030b07210080008104008000c0416040f102400710740032940c101155a030790b59110246059000d69202d460540ca0940162140c2c003242021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53444769 1250 53443519 53443547
    0x5120c06090c01270b0408070603050105090405070303050706061208070212010b10030905030909010f0501020601080309090109090206120127090c050909071a03070905061903020c07030204060305010903 89
    0x2c064111980d00001c0c40e40900c15400c403c0a400d01085a0042c82800c02070030240200d038181c661111358a024203595044548030703143c0403916110003c1854242100da103442250070000178031520b403a56501303d4555114407001e40b610b0b0394446001c42d0041030091030180240c00f645c0f0207031715030081d40104188214151030000e1a030785040c641c011341c4d80720890710b8100b051240c20300050b07602032411320500b9031150603095076003e1611070006c601c070207100744500145e1b1000e03030803544103a0320382c1061030b40c9200340109c207030303004c40d110004100241168005101051000e05510705202c2d0010102a05810a8108401c90b1204a443da1000c44603501e038140320302d40100e021b200d552000d40b280d04051900d8002c1600440c074800004074006030410164000304244948a448040043d0300c007143d035001500c0c00700024600c2071001581e440c00b8020b4901c1608017550319070718000c040c03105600030352040095500c28000d241d00080540d60381e102d401d000b140211b00220384e8199510300188401040440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53446019 1250 53444769 53444773
    0x7080a03140717100305010513060c11060a02130308070c03030e010c0215030714070b010612020301060e120709060b0301090b0402130314030d091401110309030f1605120c0609 77
    0x402101d140d00c407060030010511800c2d443c41503100c0c42144207020b580c1d500054095070800c2c05000e5080d11540c0b404401c18001d0104200401840d181160166102240b25078280e01410215541080c00da0041c01c41d00c043e0644a0907a07650f95913106102d13000030728140e60042c1030b81d40c10001c1c141c000c0a5000c481c002442e103004129082c1d400030381140404c000b515240d04c0044002400741d800343c262a14a219005680d0707440d00781a19101c2250340090048800003542c80304040b042080c980241c1e41a0f410b29140c1c03103160b2281d002400820140c0000040c41c0d03108484002a40b6000c506c40ca01c0903150b0f40c3c028079600d60401d844507060300c002c488414001c5104000182200c040c0d02d50490075650305c0040007440c0440d4000c441d1441c002e036111801c10720324203060b50007040a02e40030a0b82100000000748441e41d5031003e5075916010032103114890381c00800001e02c150f06900020185002070031601040101300d51074491500c00003201c42d40414170002140c4510003410014643e00140800c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53447269 1250 53446019 53446021
    0x20d080a140f070816020a03050f0c0603040807030309050c040f02090a05180f07030603120503060f01020601030c1202040e012d09020109030212011e0c320a110307080a0314 76
    0x190707107642c520030110301030300c0d403e40441e0941081d0100040c0c3c070031507500182000c4d40c0d1034403410056202c00140a081206200701c80c1c00f544a420700c0030036a803080350004402c0341452960b4400b54007500e0494801c84060081d1940c10f0702030b40d520f1240a9820507030b90401a207420450040c054010030343d410007842001700c04118010300542030580f5078003081380c003554022511940c509401410a50b000117010380502e0141e8102d080d4480060340c0f059104581c1a24110222801680c90b40800e0001414100c001c00060068011302d8250064180c4007420020314091805091401c41f419030038020400504207480502c205601011501d030803203108803c000114240e40080e0444819110080c012401d50780313080303c010821360241d8480c6442c03c0303420913000310910003e0300520701260b940011907a10b02c0400703075905e01c00240300b802c003508040d11100980c226803602065000700c0317040000c11003071003a0300d4513803030052001e40009486680d0300c0780c862240300d60160658208192040140d0f0b4024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53448519 1250 53447269 53447287
    0xc0a08030105040e16090209010903080a02031306031401030605092a09160e0d081204030c0605100612020310081605010206010b03160c0203010f021b0c0402030c0a0e0409020d080a14 80
    0x240000451b5003a01d001030f0348190031401030710b00301c0740303540098030400002c0b03602c8480640210041c40e0f00902e209042d40d50750340310b0380f054084440040040004040134801403001401c585c1c0706981120342034003150804032003140600180503c455012100340c103100c02c0003034107007418030342d854001048a00859131040c0300c4400401c442034811045110700d000f1040142440310308400c031aa280f030b200e10030001d646003c2c1030282c0907201004045840074030305400242c0c204500c52001055801542ea401c940c15000c9140201a400281ca00300303500b07180c16030020b00c1c5c0104001c1c4654054440070780100e81450640068100f800591141145000400803c805124450800c404900340ca0500c48005550350001c44c2c01401c1203d11454600d10020f074042c615100c030304100c0544441c0b03800300c50403c4c81a90600059020580e0114034510050040092150003080480910300000d007000509140d141c00054031515046019030388840006400b0002640c04040003495070ba0009409240c6035000f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53449769 1250 53448519 53448553
    0x10061401020303150a0e07050c1606140d021201032001030606080f0403090801060609050f0a050108040b0a0e03030c0910020706120e0f030d020406121104031104020c0a08030105040e 80
    0x42800034074082184e09500190740702e10300308014203080c00310499145044d00b00500183c0c4401d00410843c072882d540c12411602c803106038010303640140c1e04c41c102600c18802c00b404c1070f001049049881038090284802184000340c21a00a501420b1100b203c1000080910300040f007042220b4101802e000042c450640c005000369040342111251010964450608403440010781d0014006542040c4e40040c102e684141c8035410748104a0ba0a502886c0c2c100812490074054492140400c490100080205600320301490b84807a42e40c2d400311b0344c0720f030513071303e45086a004495504801c88080f40311070250800080c480c003858040d000525a003030900c013028208458000c401c4075403e444c1d818080840c0c0e024450001000c60703c0c1d040380c0e216160032880320040c2d005400ba0800180c0404403c080721101c074025080103a03016005d203450a421500d5064004403c00d9400d50455001c01c200f207400b40c0b0400000e000303680560391658807075040504000540381c0c54283c2c0d00060b0b0103068011241c01d40313 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53451019 1250 53449769 53449771
    0x40c0302010509010e0406060915020a0b15030304031401140a0e120c0102091203030f0c1905131508040209060f01120c030905100603060501060813060e010605040204030510061401020303 82
    0x900b4019140c2d40524012100802c0038202640c002d41041c80000c0c5541e008190030b005d440c1484400848101946801c903540c9240e01c00207045440c5005c04591000d0098509a0b04c5090240c25a840c11381c51352200d80daa00100b400501d00f80e95940040841404440d542071340164271880e050040404d0b90690683c0e411400710381c2650220002481c02800400358115060000040e00101078100c805040036100d4000b201d0306000b100305040050f0360000508200c6508a0002402040d0740c010418215400e8102c10380740021101e4051011a016034805c1c400c0c00d0800c56513035181c0091a1900c180170001c03502a003801e0003030b180e0904000450b030300203480346213000e00801c001070301c0e0b072441c030085029059800740503085000360300100e1012a00e90b0001001d0302d00950090205907a20307002102c1508040b01c0000710280c14209820008206402200ba1141100300116849840c0e5001908a0f030080c0d104485a600c10440d0403120817031030103a01c0080100304a00c202340c012950000c0d440e440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53452269 1250 53451019 53451023
    0xc0c060a05070504080109061b03020405030d0e040f050108010e010b04060b0f070204060b040305150702060f06041d0607030c0e030303040201050712050d020f09090f101503020915120f040c03 84
    0x24441c400620043e20403000e8500a00c1c28030000d00c8039008504214009011195544100b4030904c4082c0c0d50543c007c4c000c9070101d0f180a4000c0015803101d060803030f4442203580500f40c1c030940383c1007600e000d40d0203405640e01a207280b400010340380300c41120383e038211010241ea00e40158205041009071600d5241682d401503800604150b540e107135440040c0040c101500303d68000c2c00082408028424002400c01600d1002080c508594440030300c01c0e40c0d1681d084601785041e80e02c1d1000920581040d030004144c19000b10355038064000b05181d60303030170142c0031190540000d58030070400c214640e1200c0315590b15502600554034605060b00002e0480c461500c02414202a80d5140c081e005d01c10f06c100ea0910854a07011500c91000117100f07a010791114211610801020000c5034001d01000f20880c041d080000a04800501d08031038074110741440c404690505609100c051141c0e200e4144240710540140b50055440040d1940050002005010041ca82000f2420003001482442007281500d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53453519 1250 53452269 53452271
    0xc010c0206070b010821040f0302060a03180305091e03072c0c03100b21090f06100f12030e011202090d050d11010207020306011a040308030c0a0201050c0c060a 70
    0x445a001003003451262000080c441c081e60f100024920700d0126036070415074590310404600f0380c4020a9003026014074014100e403106000010001841c008008100c4505a424046404107191011113660300140c6415008140000740116542c5032441d0162880302c2c40c400300540561407400070969074142d602a50941c510b01c201c56600045403540101148807215140c903c041c6001844103082e41c00a03a9241f0003900d603d5801b00b40000e0781c1c0b0556880d12030403d0100c1d483c00100486858003540500261200e0080d00c02c400070034201440114816100e400070110700914090f60500130134131903400000380d2034406501d180000e13408004020f0b00c000c02d20b01207a001020701001402441103814080d88082c5510400f420810301003030044030304440f929501c1900e50900003003800d038413503602d0082d85504000014481e9440b400f03100c008c20000e00d1101414140c883e519460301d0361081d0f0f02906860004540c10f2456a424011b0660011038100030504001030140500e0355004042d02c801500b07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53454769 1250 53453519 53453537
    0xd020a08031e070201090c0b0a0507020d170d15050301050c1b1504030e100503010f050d050102070209040503070c050a0e0103150f18030914090105060a1205040606080c010804050c01 80
    0x840b21448100c0300480c03407840b00d40c25062640d0080c2c000c5c51300140407180d2903149030000031001d50802c10799050b44130743e13210185001401c3d03007001042c4441c0c500071140104507680c03102d80504c0301006408800c010b6071300041d0480310f03810315a00d900a01d500403407090b8144410849069140003c0d40c81c54454141078040302c4240204c003600341981400d5098103000200100404d16a2004007900300540507507009503e2034840004881520090040f4408504440800c0115040507090031000c58025000107040c118168006413034580d040d107056500c0d03400840c26000780311082c50070600800b0304903038418540e031902a085401d404140301c0a8403c00f05021a480800e440317411a2040d003024042c2006402440e80c00c807400c2d0443c00b0380583c002804550040f880d00745908410152000003000c480141c1e107403404100150b4024650002080402411305a41110382c4c010305024500c2040003003813103414601d41905c1c2008840440f41000304007010310000c502c0125007580212001e192414103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53456019 1250 53454769 53454781
    0x100609060312051b19061a1e011707090810050108060a050612060705041406030112122a06050610080a0c050403050601030c05190f0621050f040308090d020a0803 71
    0x300d010740142c030030700411701c1003654401e40040d42451148070b02030401c03890804504805070f0401054410b40c02c01a01a0000e410441c9144403100c100e20514001072080c60001102e0f80d915816600c1d0030214260341001d102003003043c0400c050300c1d0041c1104100642c500074486944020140c06d500c0c4090340c0e24040ba040c1d450300c0180303d0550041d10111440d50801010082c00d82d8424132500c200e4504220080101e483c0070421a07040720f0090940450644d09915401d03c1d50f91122200e8045c4a414901d40084103030001c2104209501d001048000035081d081c03400a07280d008280034890303649805041a8103820040305500079610f1030b80000c845032000340503511841150000750952040320300002c00c204c103403010117013604d6042c1c131342001160803511181c1502d8400c6c010518a2002c0c81024014188215542880e24060400d446211544501c101c821520156503a803100d10b4040308000a00d0f410000c684e81080c0342c1d5000b8162982d5103000251517050032132009051030b00010110305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53457269 1250 53456019 53456047
    0xb1b0f1f0b06070b06040b04060302031c05040f060302040602070e130f05070815061504030c0b0d150b0c1b030c04020313060c0f110604030813020d080c10060906031205 74
    0xc01010b800c15584040e0307400c1a080390310b01211064031641c1040c0001103142000e004000449078090001d10304c5c0c1403001c0c04020000c14000540003084014000002c11280c251111002460240c81c0140e0311402d0100081c03c2c012190003801580002d0340034480b012105200307903540e071074008480c020a0721080c0b518a041c00b8040e0300c50440c500c40d07007c9800c1195520407900d03001e20021140c0e00d03911007940d007540d0300e580100e200c0900300c0341c03441400b040340494940081005807a001c0001500e00002148492003010a410803003540c07202107881341c1c40181c01c01c409451800d4110300c8084064516000a54513040407000d203001d04c0d008000318003052080c0c0c120340c000d039510007020300c58a50071204c01404031020020b010001098681600400e5034040361103405150903558002d1156140e89640400d0031819030120380082441001c140410700140150050118041c0507000003801c0c4030f5003000f41d031101c0c1c0002030214a040d100704002251107000d1068030209050140e103035144809800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53458519 1250 53457269 53457281
    0xa050d1407030605090112050a0308090c0604090504060e0604080a030f060302040f02030702070b0a0f0807120e100c02030f0403030c021503070801030b0a020c06060906060f040b1b0f1f 81
    0x1240d11808031007030260700c541682090303007070740e200762a2090507030381c0c6010000d07640100440281070b0741c00070f02907100030902c1285420351014000d0200d030040700080d004100c1907840342d8042250281d540003408104189401000000207461000388010700702911200d9480c89003480308014195104240380900046400280007160001d0007000003c0b40344400a0180d4421200c130341c0180506c8202203030030003042d03013030381c00c01c513403c0e9a1100303000c2c00300100703441c4264041c02e00002d100c560b1038695071500c510300074400807040c0c5a002d0a02c0c00304405e400020b450380203e90005541062003190790300b150f008151421250585003928010600e4004520700581160206503482d4000080042d090b40118507517048038400c403203007481561108201000ca005034003550207240c000c900450010b1030005001c64020130001d00c0d561801101e54190312140d8096031001250120110740e40c80313440c1980c2d004040f8245c21902a01c2e004101c0403005d0703258a00446003000c007824610034003030304842d00d038428 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53459769 1250 53458519 53458541
    0x10f050d0e010e0115060203030c0301051c02191502030705100f0b030d02030304031b02100309051603050114060303030c030c0307020c1309020a080c03030d02220f1a040b0a050d 78
    0x8101807580c180e900790117400d18258004015110070000a0294070000440c1e100b1106210020b0450742400104900c40e50f5140c41084180041007100c400341e0759449880c882d0000c440c00c0907540c0b9141c80c2d52003402001e8807445500755007051081c0030100c2c002050b039040c0d1207620311000540c8060302e00c01710001d000c050180c83d00744c4034105800d04030507000001580070300e0090301c9496541030800c01c40700303003140c43c05002034000f8031150504055600a42220540c18070400981c1e0403a440100440700803201ba81c015516a0346a04c003481d150000042160740109040c0d02079032a615000130588004c1c800a00700951501d400400111410300c01d00012000030002800441c2c219000280d00000c4c200c01001a84542c40160700000c0c1d940300014170b40a1907402402071410600240c850300000c1d04040144c00c00c0d200d00494050030b403a01400c6000c06054090b0b015401c070b504000540d0030508400c143c0301c0300c282080200313016074030002040d5440302c2c4003413400641d241d001665050141010440d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 53461019 1250 53459769 53459771
    0x1512090d0e010c080904060b19020f0a08041203020705060c0c091b07241505010f03090228050301050c03041b080c0d1a0117010b150306011b0b130201110c010f050d0e01 74
    0x80e2403c6513910b144080d0101c907a58200c0f80d10140300bd008944507190380d6001446480100410091070103450060103d10f4028015a2003081e075803c04141160710410604010350424800300305c040c130749612015005030410b11070700b10480820010340058440c7c804080c00c5160300d194851000303140c580080350340400051080c0308100c4c0340425800c4c010038034000c19020031040300c007613800540b192051515041e00244001b24041318090008542c0f0b2510f04090f010528410012541e500c0074014107016000c0c004880d41e980c689800c2010000c1400c95441030800d02104042014106c0000c2074110300c401110303501a44089807500020400308807101c80410170002c0d000045c402104c80034000004450b4000f40000e101e94810406107155801e031000c0d084906201042c000d500c0350b00026041c1d42803d401078400000d52b00c81240e412012a42d64242004500240c021560f02c00c0c804410b4a03d12001401d00380c403100c002038401e8220303280403420090003264000d0000d405030041d040780c18541e40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 53462269 1250 53461019 53461027
    0x20030f100501051c02010c060c020705040608070807050d0b0601050f0702030105040507060908030a050301140d0807080304020a09020a0804030807090f12170c0a0f021512090d0e010c080904060b 85
    0xd140e5024010034070a080c451070708403a142560f0b403801c107100249260305a540c0b440c2c503800307a1b44402c002d0811031910002c61080c0f1202081079282c40c80b03080041c3c02c4042c0141846450844264035042850b04114003c0f401449900b00003a0740180071030304490f090900741d031104508118006507000b08440a54103609100a00051100100b001400d44145543c0c007104180c86000c1c0b5540c0703100d04108000001c40400042104144194828581d058000c2034401c2d440050348640b419500000425102190004180170862502c0545003004044c960815420420882d00150103407d00610103024814141d0014850ba880750043c20003a01c00381c40c42d18800c0c0e482e12840c2e03140c40e11a0780b0072120004d41a80406102001000313459004416100609402070666500005600d124000300d07040a00307081d000300804040c82c007a080b400c5c104201c0107001d107807504007a0b1429554039540402e000652074007480c5664000340300c08885410007480313a0350b82c900f4400b14000b4913481d4050f001c1440080303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 53463519 1250 53462269 53462293
    0x90312020342040b30030f0a0327031206151d090114010f020109080a0503060103151503090f021302072306010e0403050909010602010f110720030f 65
    0x40d040118110b012811401c19035041c1080c0004c0b03035424810182e002c030489101d0f41c0f0030600524403144820328112980307070101610306a5451500300f205019551030011078003c90310fa500d03100741d00514031841b001c00c101c0d0b10396890030000c4842200d400781c00c0107407170b0030f54a200d1706154010000801524040314882941000003c00880020b218018154240d0b008a5035500e8810010b5050310024194619811041d10054032041410960441035540f42d1200b000800c40f04000307084982a541c8400d82c0c2c901c0c2600004084405449000140c0c0b058084c0c1444554400c2011303d14101250034000358072042410a11041e0292450081d408070720482d400e541109036030080e0070b03400d10840320303008019202440c5500702290340c0c0010303a85610032001041810340343c0c3c04403a0024024101a49040c018a01043c0d4004007600b1050260b9114000d04444d800c25100b00b80224503100070321820300015581c4c440600004403801d50b00340940790031407541950117000d100b82102900045030b403d100b40c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 53464769 1250 53463519 53463601
    0x70c0e01080c060c03032a03070201060e07080906071404030209011206060e0c03070f031d1606050901020712020a0521010b0f0603060918030d060f06030903120203 72
    0x34081d0450070b002d02e01d01e80103a400c288080d01c10503c50040a0b5056a581c5030501040e0803031150010b046c907001c080d4560030450f40d40015030148101e5800415000d0900d250b41a000c0800381c50041007001d044200440a0b5000c91003035005229460128204000c2621520b00b50066402c0130f503200c140d50000141c0748504100b124041445130b50b007406115694003c541c1d500c6002c560040c02d01ca070030000503c40a00c07401181c4c10360680c1742000103654030781420034105120650104a010707070065500e0066503502d08001c100400f441e03d0700515004007000000d44510480c4180030518200d40300c0d004c119920300c01c540b00a8140604041a028640c0110400e145503010402c001540780c008892040d003000c01c9100340c805006011149103485100510100309130041c4165859400d00300d25080056040c030007070140d8400604049007940c00c224250004d5201c65003c00305152034664071000298102d8030500401c01220401600c95440e804c05901a0141c58120070315000c1d01d004401c0302c0014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 53466019 1250 53464769 53464771
    0x303050c04270b010e09010909260901020f0705010903030809210a0306060e0a030305030604090b070e040609060e01030b18010903120e0a030e060715090c0617040b07030b0303070c0e 80
    0x31030360180480d0b083c01e4015a511168030180c180c00045080041c400c1844c1c641041d0042c0b84181040c0b03c2d0010135240b03503089420b0b1021a80084000021407180350b682c10030606c0100101840070300032903481c24001800d03141c480d100003007c3c846210001206800f05100b0aa810b0320b0090342c1c0700c0d44010f6450320303491640c013540110003c41d1401202040f02885002c82c0000080d0242c07030501c20500351b840548035a080200369541c443d849544800004840c2c00c116030240c0215200d81e800e0003080000c00c41607822682119400500c3c0c03240800005880c038503040d0449800503295030383d0303031583c83e504007a40b0165440e2006560826007403a04040e48107802c0a462801030008002c0c08202c0072070f05440b034240c42c90240c0014010125404140383c014010705215204400481d0f18040080300318066070403480d420781d9142043c420403c6819000035108a807942020010302c51850f0a50352452a10b9025114400b015074442600030680c504104551909030072603070510510781c0d211900039a440c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 53467269 1250 53466019 53466089
    0x703020a03090f0609090207140f061b0304050c010e030f0610030b07020f0604080d06090f090b07020303040807030e0103090221161412010603140106080d08090a0303050c04 76
    0x30b1003460000d0301100c0b0880703860503a000e45d9900303104645803050410194002071350580c0c10760409980b0500d4032808100b48811b484801c006083c031841e1420210100d025190b41915451804104200009402144521440ca02401d0440b4109485000b09182200c0002e03008841d120354801e0010b4941d13820000701c222849402c80300c2c21503445a004a88504540c107880ca07499001c1c1c00410005a104006800c10314101100014140da481c90100c3c00e45892800d0001c156580c0ea00100034064440c0015a10007114002945182481da8a1904034842c0040c050100003002c091804180c1c480e4202c48260f5070020301120a01103103131002d030013041000707041d0003040c4201d90314130052002c0d1041107000c507181d00100c0c10400c0f030001e050105030310780c0036003d108075541d4040100008011410380140e1410850001484909109001e440e100c150840c1e002444080000c200d11010005052030030241d0601e00803074a03880ea03518801007805142c002034229850340b4040c030b496040c52461a140300c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 53468519 1250 53467269 53467277
    0x190512151c03020a02010c061104120204060603021219020f040e06010e1014030a0212090a0b0c1303020f01120c11060c030402030604081305100c02030d03140610050f0703020a03 78
    0x30040714008007184200c240d006025810030908000958040c0c1900c0c100140117100228650180078800c15041e445504201000d400d2011008154245880780802409050400b189050341c0c0512400d0103960003019640048903070600301c24001e0f00d6030103881140c0714802ca406c0d1501c1e1200d812604220341110310600090aa1801d00801d00e03010540c060540c03601c2d203034131240181d5010000345a91008011130f45040d001c001c1001080d000601e224131640800d006040c1d01c0000c2d150860039070130080c0044440000030321030b0050351444c0b180407800316941101e03c4e4582c5a85a00141c8400703010070300303c50900d131401c62000d20541e0001d45031120708800b00d0585000303944601c104000c5001c00d640103901a4030580004e0700286090b00204140440b103000d001400d80c0d2240010903c1002c1d840480004401d41040b4085080810008203000f00c1f0703041c20300032071701500280041680001e1600d44903031586241800d500b40500308841d0ad0225503402d59a440806040c080e64854028404070001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 53469769 1250 53468519 53468539
    0x801090303020403060e060c0d02130806090c030601062a02010c051e0f0f0312060a080f100b0102061e0604020f0403080304030e06070305070f022808070504060b19051215 75
    0xa44001c41c031f16115402c46408941455000840c01d0300a401040716515003011104c000b149940307082004074859a0041e00502a02d142d00c0701f40b608004060384020f050000300100c69010707070090310085041104155200c1d03101041800105c403442c2018030040d006004242c1e0701420102c000b50400f44c1404020115042080f0b555207050303a602e82c001800e16180c20500101c080481011040da0300920010007560315036481c0c450103400c003ca1110b0103401a0701840b11081c4046090285580b2a0400d0000e446503140c00704030b41d040c606000c0c12107614110b1500000b00d296496505603403080000c01d41c16a2119281d00c0c100340030380d00c00d540940108403210400000340c50000b040b12195540b640d83c6038142505a41d0b100c40c9140e900308101d900c102d00700054030382400c17099a242036001d102e4241035061840c241d1542e04150307681d04400d0180b814003406201c41d4a000c0212040c1612a15100014a85038001192280104540540f20250641c18000d44164020502c0c50b4880704884410388 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53471019 1250 53469769 53469791
    0x2010e0c061201050904080418050402130c050306100201110403080c070806131716080304060c0906020d050d091406040501050601030b0f040c020a0605090f0c0604081510080109030302040306 84
    0x718064002400a0001c21a0041c811418480344c04d9030820303c99110a030402d40c58100000003002c8914940c40c0140c1e0302c0040009510b451902c5980220107120100305030308407400004d200340f000a1803540104030400d804248580b007540500340404440e204c0b50384454480ca001101c46d4002d081c0d15902d84075000f4003080031200822401d0240c0760781d106820b010009541e505500c141000c02d5601074240038030814070055141520842003d00c40d04a80396245041d14040702142c400381c140104112760080d0a0021940028100071800614100301c1d407990030841c6090007038a21040c008206031001481f00d01e04200014209015604c550020301007941c07480011000c44181041c01c1c0d038480d2100c020841c0606286e03111107103505007841a035040c3c00c0d00e44c48050940780140d904071044ea0001c01c030120918030901c441c1074542c074101d540c246003d2904064903507544450000c80360b002011800301d84c50340e00248040d001004084002c2c0003e41c614140503009410620040c0c80043c2040d0710024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 53472269 1250 53471019 53471029
    0x90f02031b0a0f060507030c03020f06010e010503190803180c1c0b070e0604030206030c12150109060309020f01080c07120314010b07050715030e0a0c0611030301030c0608070903080a02010e0c 84
    0x3c00c2c1c40c00f940d105414101251000c8620408900094040d4010080c140840c26002d02181c0d01030032015024402d15403514007810b1400140421200c062036061020000191500003120780000e101c904c54451483d00d201241d081c52101007221364051b90110070070180d043c504402c3c8000d00c3c0902424030b5641c0d1420401c6e188130b4107a1900b1030b8401001c0000384010300d0b04001454001900280b42420002040400d81c1c4442c0b0030345005070310f00580710104a040d07a0000307240d80500040d03e420300c0505219800b081c040c45d1003021160502c884800003504080300c400c04e95000701d0304500d01d0080c0359120310000e402007149a000580d0204808000305192410808840f4410361100042c8034852034803901650440410038201d04240c3c88082d441d041d418108056070341c1c640100c2c0403c03020382c40d144015045c0d59030742c502c41e002a04140010000728402c10700c84400c84445007041111a42c0303400040707030102155000185004008035a00c65055415880088031868040849040c11400c400b080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 53473519 1250 53472269 53472299
    0x705090906070c080d02210108070506041202030118061407050909070e03070503030403030809012703030506031e010506090c041a0702040e0102030f0403090e1504090f02031b0a 78
    0x1205074001c1e03010075990340c8140d0281d83c0480c01004107a0400b8043c0266501b45e902180c4942801c44802e800c02c40983c050000e00c600520319180189a00d61901011030060b00031485880c01003d0b40c001040e0554a0a40144850400744c00400c2851121031801d071000740340d155410141701c5440c800140d2031501810458103a400c00405007a0507681c0d80d501103c031452010003564043c007502c003000070140c40c200040c1000d03501ca07482c0c84080b031070280703800e034216000e81c604e0481d140b0100c0e841009800ca00c0c05051025601403801254598a81c40031920b4201c2c150741d007200c1d80502d011300c414041010362015004020031500750a085e110903180c0c6a0602850003401c00030840310f444269005042d10003882e8141c4080e1010501101669045003243c0080310000503041400c400c00007050f600044e150003402400d00081d1550500c03904c021032224074200a603000e15520101a01071103100401030303000903801405c8902036240131881c1c0040c0c5c0c0c91001c1c41802417020100118803910b03859400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 53474769 1250 53473519 53473531
    0x708090d02011a06070201030605060c0a0302010b1005090d080403021302040312030506030c040e0f0109050616030912032309010204060e01050c0c01140d020309063c10080109060e070509 82
    0x380f031a001e04081040041d51001ca000c1b4180f42da0741d00c4c0010340392200001b40240e61000e0000d40504030007801e019003541c10a02c03101d072052503604040c04d10700d90010709444100341c007550251030340e48141c034101c4050310541c0c10103980306142141c00100560950000c0085c1c0c2d00c42c140032035505c0e00110341a81901d03002e40d04990f15401007584111740b410254005d1404c07e0010f012904220100c0601c2ca0840e00c0c050740590300c6030800c104010502c980d41c1510740c0ba446c480c0c541041008001e488403000d03180405940d43c20580c4403504090720843d101c100364900f030501103040d106400e01c6c0036114000d40c0039129180c081210502d03208030960190058036510b0008401410840901c074004407000d08a610b42c042d0462824001c41900010a20256100700402e000030b190038146a01080510102e803905041e464444e142e14519015084030000d00c2d50030000c041340904d03121200450001580340e0420300b480d40c030b0680002e06001c0260084000004047c081d20301c0d41d41c440061200c040401c80b60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 53476019 1250 53474769 53474801
    0xc09090b0109020a020304050d0f060608070b07110d05190209070513140427150204060f030506150706050f01050901050d030810120308270a03110c030102030708090d0201 75
    0x42002c0100c90b0003c201600e00c610580f46000c0d100e0f4000b8001e26a41ca0065444030f0101252100308500e62290801a01540c40180b0446241400b004080d204048004054034007062406d4050745580c80b000b107006a01c2426210700e903040003200c3c0c03e072003000e0b03138107170300c143c0320785c0301207842c40340100212030300492564140c5583d1402d005091070120f800311213140c0c00035030750100d002c900420524a904c0140c11260002c0c052040da0410b002059802002c1d0030501d841007008101041c1c1240d140c840c00809820301060f40da590b040040c0c80001d0104220100d51800038800f010480b042d4443c80c450030341c820250103241d80315010310290001c2402010340051720404180d011030702030403007182e019600e840140c160b80d0715209030301c20300c464411085002c520f1000903c020781240340e8003807d43c844640180810210030758000759440314500030113014811002c20081e0b410405002c0e14040d4000a4000c0d0355a0400c0400200343e1401110400342500400d0b13a0100c00500c18024034034558142c000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 53477269 1250 53476019 53476021
    0x3060509060f040b06040b2a01020315010305071817070b04080d0503040f080a09030b090615060c070f0b0316020609030d0b06190f09120c0e04031205090a0c09090b 72
    0x900c03000302011069607a01c110103010005801d440c450003440e140a00000a8023012460f040d80c172050924500c40f0b50159005008016220040ca016000008003d20b030215440d00d0390070b016140448040001001c88a0366100481c0000681a1004242503880e00302d03640c0030395a4000c40802c0c040c0313000b08029900208140003030315100350007540c0c1042c0114140c02c044001603503114450340c04400b450380410a04a0b0800c14001003101d0b0f00d81c0109040c0c041d20480c07420140c00201c649450115a03c1628049404881c074081085404007500041c0c00d0f115450352502c003000140e800c2215040a62949441c040c440980301003030060245100c44001e42c1407070768030000c0002800c031800405811034002d0140d02806e075440712201d0f4031600c0a4540300c9003401d007031600030000a0982c200402c0003094410171000600d0f4021094201d807002108241251540c0c9402c544805030400440e101ca4209001e006100d0303400301c0c3c1401c2443c4100d010850b00e681d22a03441017611150030019140d010204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 53478519 1250 53477269 53477299
    0xa0b18010b040e0613060e01300803070e03010608010b120a050c040c170a200913090804030c0602030405040c0305010503060403120b0301091109130b040f300306050906 74
    0x10300d60010b030000d0031102075940140b140c1702101d109a015040c2d07800720320010040f01c0350341da00b100003120241901d20a075120071494080080940080281000c1c0008001500a4030030f500b9128030010041c002e200660341c41841a020305919680f25110741070181c0d8240c40c00200090000c142948034010b01480018041000020044c00c0390036024002000082d0070308203900d000507841212256000079808203450361031a1900404107000c04000410000c01306140d07500c007003104981c02c1606011401003028600080300c0d0080b030f0b00003840c005a1314004114290044040c0040e80c070299810010507104040840680e0350030711a40d605a000310f00401c02091180740c1c00c3d0304103403603143c000c1482c00400d4040b0f400c540411809652820028130326454138681074a0064025190885401d800c40d12030f104c2006900340900010300c0504501a090b00300851180c1c132107040304240c442c1c030308281003807805450141c0403440380900007450503902154070300d080e05041d4003c100103001c00848030141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 53479769 1250 53478519 53478539
    0x6050603030708030702010c0908032d040305070f081002040f0510110609030717090a121109040b07030b0102070305030d1e0c020c130506060715140a0b18010b04 71
    0x6401190980402c000700804900000d000b0350080070705600000c0c0118203404010b040c40015000030b07200e9001000038032075042d954006090304c107605207114140303a107803c1404e000c5403007154401040b034011768a0004448000396239403004c9468050a50f0003071042011040124469030160180091440100380f049003454100903850300c0150400e04444190420384a00e40070085036000e109070320008130902089490504109029408201c1b00e080142c841c0c001040d405560151108510030390f2032003011710001e00d01c0d060a190006d1700e05d1156007450b091510640350102e684001280c01d1030859031142d440000d4450490381c122010314100001091150040c0250012072086602148200c50324048184103161151103c0c0d0010f2011101e4441802402d10741051030f84c0403c0d14120800c2291b44400c411186510351169026040b8140d810301c010050200612403158035a4404c10800d0142c400e62141c4403a450403240c030000d0364920b01a042d41e16100340248600c2490600042140c0801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 53481019 1250 53479769 53479771
    0x9210f0203012406020705011418150a020601060908030316030209130e0a030f0206090a1209120309050301180305091201090b0f04120c02060a0f020129091509040605 73
    0x80100007107480c409845429007084010f6081411a0125000c20011103030100035100c0101000e0070b0400c901401391910800c1c0c2d000e0340c8100300007a40e180150792480e40d600321031250401c3c0c54000c0207440303144512009544031401d0082030f01080003d10049000040042030784c0c4208000840715807441c441c100100c019400040c5201d8200104c40171000d10314459010b18440552040020321205100741402042c2089200c1b82d8820340d0803110a11001d50ba02140031520241c03c802070481220082804503118107860340070745040e86c400100042055400383c508812588110024032413600c10f49040c05050042e03402c01008184c0800c1440e5490a16000005400e001e50000042e1081b498032000300d500811104220246150005c120030070030001a1a0b150b194589040021400203501280b02c61052031a490107000084c502141c60a00c00d40003003180e40c4820300001311862502c0107820740042c50f1500c083c4905620b90009488216034200c002e803045006241c051103846d40d4032098000d01c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 53482269 1250 53481019 53481023
    0x311190302030d030f0b0a0611160303020d05070f0602040905160206060f0d1e0b090708060c03040b0a0b060a0504050f09041a180102070c050f0907020615010c1a0709210f 75
    0xd01c4046c4002d05584410a2130010040c0b80c4400171080c10a6800c9800d050040d409180300d1500740c00c052002c240e001800852120030f07404c1641e6251000d0400180380d01e205500103051900000c2c010420100c240c21060184a52004105034440400301c16610342804440e0507403c007007a05405c1c03c251604d031400c109228098400e0400414881c00300100003a2240c80648100c41400107020049500b0010034006040c544054000c40c06c0a5002d9a0b04d480080c4c0080c080d002e200000c00c014203000da0100006441c01007049948040035100641550001d11034184202046044c0284504245181c544540da21a01c01503091403c4c900c4c039030000e100904086416032034400055658502480200442e44c00b132407414051515010801548201c4c581507207002c1c501000520030495000a10345800461032001a200d020740000101c5800c50a80000b07002c0c243c40542d128221404401d0a40c065411969076a907944d8840942c80485004680300c41c3c000e0b4200e081d440d0114280d85a50040742e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 53483519 1250 53482269 53482271
    0x90204020c0303010326040e04110609090403270e0109020c0319030f06050103090f1421030405060906010b090108100905090708010506040c09031101180311190302030d030f 76
    0x141d01d01403a500e150800d070011a80b89039000c8204240c035091411505001d1480142e00345842e051408103205848003a00023410310718a131031850711a0365050203036884000c02400002c19807410f0f050050202c400c04002016609020386c11348401071b58038280e20140d4112410200507a460f0001d9400203510508c607100341d600050000702c5090481c010054030041c0710307580104440c000c451045046807000e42c0954181480d00c0800e40004c0c0c08400f4004403150400e02003200205100b1032503082041d400c3d03a40000c0d014481006007404040c401950081e4041c0040758038954450303007030303a40e198030a025024003c00107100308403223588a401c40b681e11003014419198604e80e12a262803c0d5141900c02d114150421802440100300900c100340c0c3c400c100719014819a98a402e000e882c00c0141e01010381480486691080517134044c41050601d029600071701119a5500e0038680068094070b08000c0c447c078841000c4000741600c0d10801c01c10369400070081e11502c003007540309500030243c030002c41c8841 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 53484769 1250 53483519 53483527
    0xe31020d05030f07020a050f090a0e010f020c060f01060c0804030605040c09020c010219091409041e050d090b040614030a06050a080d02060105040203040809090406020c0307030c1b061209020402 85
    0x8078280050010f14406078050b588601207841004416246500800d0180042072500c1d05107a480884154001407800d10025400c4031908005014181d05004450118000903050400da0b100194661180340000304060059886460442e92100d01800c060054041840140042502c0350300c0540c20502c81c101d200191a0394030b844400342d8006a00203580c40c2d50124803000014811040014200c44906e0000c61140c14666001c4a400160340c4060241c0f003603600080c1046268044509001c80000c030800f03642d4614a4615038031481e036151000001e210003000200c0c03201140a9405440041c1c50718207004400304803086c6941c00042800300c000342c075500002000c2d201c4104880141c0320300b00142c258420b40b1b540c040c1c0f03010340c183d04c1107005510400c1004042003d0b03c040e110030503811110b81c11541c41d5030074190040d0040c90b000401a020006042d401c1680000800581500c21000006940f016920348041c04946100e880301050b0781650107410030f901a4442120144010001030070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 53486019 1250 53484769 53484773
    0x2060304240603080334030e070305070b070c060503060319032607020d0c020d030804050a0605130312180b0711030f041e060207060f1101020a090e31020d 68
    0x60320b1090b401581c5284002051012800b00d0503031442441d40042d40c1760740010342c1e440da03540d040b0a89030141d030f08050351810f00e0110100140100380046400908460040d521104012280c0d44144d00807a540c0c1445500000c60303a0141c0180c038411280100078114112038403411920300301c0404400c80401c00610031110140c00070880c9040da8441c00b44c1e800e8864504000083d28014002207241c091003c8030550304c0050f50b03030881600f009507240c03500140c2500c4518003103180c141890401003d4900780b504000801d1740c00103c981c1200e00a84c0d07401410b0b900c00b52441c1c04c1701c044601e1440c0c2c4d6488a1100c001069514441c1600483c1c6440c02446161614a6450954220000510304410005400c0240450802c1840044100e071a00300b010305240000195561000748140c0b010301101d500f95181003805894401c02d4042035400966071009010b000426050480c0a00c140c0b0340090400301e800800120410081b002d014070044440f0f0f44403a2881241850320302c0103d80c0509442c0d50400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 53487269 1250 53486019 53486021
    0x515090403030504060605150702120c13020c010b22111b010608010501051503180307020402040308090a0e010807030f0503250b0703021806090a0905130605090a0206030424 76
    0x4440c0d0700075600020382d82494608502a01c0341544914403d01e03444100c06404498881114901070f0704449403007450801c4100641060413a011603a4807144040f607000c52f881c3e594004140344082080204041098682001884942003200e20100d03140d100301c81d0320300c2c61345500002d545003014003940d0800c1418040483c0707200c4008590603540e51544010403900e40300f4013031180986412517086a03004c421080016140c040100318048001140e03902c44a525001e1045483c0c1c0b5801410655880340c50b4141188680c0c17100200b203000780641480000c0001d001900c80381030f19004030140c40e05a1640c0c440f424202a1100f060320107000400405010b140c4038108482c6552892021650320f9020741091500141c00134010400e05004000450306210b414071124050703082191215150142c84001c981d91a803182c03c40c103201881c11050096070504055100c001174407d10050254bc0d0310991081e440e1404040d0085d0007040a1000c180066082c20350b2a1f410721804108440010a211300c40c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 53488519 1250 53487269 53487271
    0x60b0603010b0d0b030a020105030c03040c0b040905160c020f0d0201050f0409060326031308070b070315080c060d05181605011d010903030e0402042301020c0d0c09051509 75
    0xb140c2c400020080b80301c0e034490268004441045001d011003840300c1e000038005110060022420b00c5c00000014200505894240040c0c113500ca4540d03115500e45203c04c1c002d1900741c4092111029460b0361402240c42252064902640a03001051071044c260500440803142e890883c140002400100c0001000c0000f510040c10441404140b0fa4036600b00070400127844004210000d1541e034039204000003080c1100d0300302e43c1c2c050a0703104040c032034100316000340034031000203050805940a020040390b04d03070000400420301e800b0318060369586d0301b40181d40381c61082e001e41d04134506001590400480754091507000c900400300146142000e0720399410402c003103110003d0440207040034070041d40e110460b40344800d0040c00c450b40c0c52000c000060086500b9100081c20040c1c0166001c1c90703511b654046d54000c00044001444000381040c1a20f03440852110503401885616041030942c0392024800c2d002940125907a01c0090a0122030400b400c030092901c40054a14400400079403540301c992 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 53489769 1250 53488519 53488529
    0xa0b0607060605011e0503010e070908031908011710020901020124080c06040b030a0507050904060801061814010605090102120301030807020405060307080304120f0507060906140a050412060b060301 87
    0x1034101d040030f00161001031800c000e8001e2480304440e44500c0e0340c118084030f0641361f4016a290b19035032540412220603440342c01c8001d0a001c0810541150f440d442100c1407040f415842d0005c09a8070340f540e101441481c06411752017603020744100001500306034000c00ba500e2040c800800d41c1a00c111030451406800e000c2da800d69241c80138104403418046c44003100c000c1040300c080307191925241c440409804050b00c2c0210b200c2e9141c01050909024a003200e140410150041c003602c0c0d515911680205558403955041c0102203910070f58003c81c3e071262803002900456040e140f6400c022003114960080d8038014150700c030328168458100c0004014500035032044d6000d5039592154418082556000341100d030003580315900510000d130b40170054070103440503282e81c080080428104500951008000941b050056000c0403503d55403111600c02030725416100c110400001100d00c0846208581606000410900c0280004052030100802c0103010ba0004180912981c000480030751083c0c0c80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 53491019 1250 53489769 53489771
    0x303041e06021c0503090c220e0604021c0c0506070606150903050c01050a030209060313140304050a05010e01020a0c230102010513020103050c0705010501030f060528050a0b060706 79
    0x6041104120005400c040c2400b4409007041032007200b0940301c04140c400c0714600703100022001400600080044450441d00100207600d5809100d440710083c140d00003d5070869402d00079036400408c030010703d80b802103501800c1c030b4401e00c52002d005d40070030558170070482c0c03c001083d000242c2980c403880588030450254000103019454010b110419002c410b00c44801c1c40b0311a8030030030216801182203015554207081c80d0703664550a000440003403041e80300050340150040700b2308c418043e50201c0f48600c076100d010712038102107003004595a41e005a1203054be1000d21841d06016a510590000c01c0c00d00043c01120355101c0e65695001d0210b105400171a452072040e005244891810801a04101d00030700080001c1e090043d03645000300001d004c00380c14141c9030b034040b50103800d8071001c4400c01508040200451358580c680303c000040091002c2e10a14180400704450a01040d1b03048400d14040044210307042c03c40000c800070b010010524050f26030f81d001c442c00142c0711100240060751040f40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 53492269 1250 53491019 53491049
    0x405190c05030a1b2f0a05060106030b0604150c0609051504020109060c08180d120207030b010b0a05030a1a03160306050106031104090b0f04020f090f060a141602030304 74
    0x850340102c40804240340504072060201041250b007240601c00c6800c414200302600c10381081751442c072819880c00d130103854480c941c41d00c01030000202d0340038181c03182e070395061102200403002c205007800742d400b4103242130192012107210280103010a0103460311075100414a00001e0b10380c942003180e54040c07442c070001010704210440d0381c040d9074400030308a5030030133b102c80040c07640b1040d80d64010b9141c0e1054034480c040c504409a9100c1c2c5031902d000b54810402c0350040e0130300400a448565900c802c64103444c941001250f49106031040ea80020042d80d551419035a600f051040a440207440b412000007405007541c580f81c4080c48100c80210ba40c2100c0c0401a10350301d030881c1142c10503841002010319207020304596405c442c04480454180d80b82c04035100c800703400060740d084681600c040d80180b00161200e5003040b05000760400070011901c0b03010028201040c03000ba0304c01c4604900000740310700c680806044002001d403d10034204a440202c5a64580c003080c9564060341244081d012640d07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 53493519 1250 53492269 53492281
    0x20a030b0a0b0f010813030c170c070e070302071109061f030e06060d0302070512010f050f091c1209050304080304090b030f010b09071116150e01030510050405190c0503 74
    0x184020000082864104400e151206c0c030380300d420400100003810410140740c460144882c190010704201030404460740c0e5410020885039403080d15229601c03c0300322080c00580301901910994411503080148201400c3c806020451440300052916602c0701d24642c40440310032198041c0b50042c905501c000525501c464809850f00000815481c45189800401000030345d0200e40e04c07003182c0003540d10204801b00098500d0150011115030712100d46040f0400c510340c0003240042d0b0041c18150140c90012101d8594190b404408580120200b03242c5114a00226160b50150a0240c000c00a031781c10325440d10111404d613071080d84801d0300c10361141c02001c09882c00b03105998409418100802400080318042801c84070010300d07200601080030f104e00c140100905c540b1240c0740c0c0101e10908103d440e0705c8030b1800c040d241e510740b41c0020307600b9440e445594001d21603107016070980880400c55515000c2040043c0030010212202e54440368820b200116507401041a0340c40d50b6118140c076440c0403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 53494769 1250 53493519 53493529
    0xc060f02150105030d030b0105281b0b0705030601050409020d020d05090613030305060a050405130303050903040503120705120301030b0f100e040b070905030a08030a0b031606030207020a030b0a0b 86
    0x1825101c08060301d410010041ea940008550804501a08020424042590069400d801126109041a0095a400704d10001030703c84602030401903440d5828066444c140b2900e804110200081800008030302103600c06000d00e02956200005142c80c510307140d2100038400690b0001032640074490f4000c200c8500607001400350903801003180c002013503d0703d49080700c15685080160f014092540c3d600104815448804400001e0a80540144950f003008210080310104c540001d130006403510000c0b0b04c80c02004002c03101114001001800b0300504984070080683c00000e08a6240c802c0f40c20b15901c5600301c2001c0c50007540108400383c00b0303181c01294885c00b01401002a015401c28040034445181803500c01a04070342c1040d00ca41240c0c0d6240410344e200c1c00c240e0070590b8035101e03503d4000c1c1084030b01002584101c1d084901403100c081084141682c0d5409103c2840100c0307403c210034000c00303101307a000d044501c1c001810300401030790344d03250003400204c01e41d1b046000503190311135007100c0c0c103003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 53496019 1250 53494769 53494783
    0x71d0a0e150303091509010c020406060e120705150d06150f110303040b04080702150d0f0b040501030b0103030f02150106090e070207050625021504050a0b03060607080f070c060f02 79
    0x2d501851030300e200d1030000b03400c00c145841442008600400c0c8110030780d10901400c10119805401040000d448400140080364081d20051103504080384032900b103075000c00c40001710351f4051b114020351401e03800b0350701c2c1a800c1364003140052a078603c000509440105110340c040f00c869280d851515480c010020010148601c1d1441154010401e11000555504200781d10503000a540c545401c1e6601c001210b505080c081426845000300b80300119a41c1507101c040c0c1e031050000c080190405450078401942c030700344801350610400000420100f400b424040380710380c40170700c16900014200340440b03481490a03003210001451161050000c010714013000c0d80c101805000800d01d50f840c1100181561180b00c880700c1c24015820005074003045000c43d0003800a5008101403008115040058125085407085522440c1c2c84003001802602520031603000d5180902106e203006c0154503211250740c04540c17a0085014104001d0780442c0d00c4c00d1110001e0007096454020845100030000c1c80c1c008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 53497269 1250 53496019 53496061
    0x120317010f0902090105090d032016090203130c0b030604050108031e0a05040b030a050f01050d0f0204021b0d02010921020304050d060914010204080607031103071d0a0e 74
    0x1455000501140718525585011180e24a6015981c0e07003020300101c446003e03c44000f44c100d148200c2003003c16822410b03a4440210140d40d0507024040d0003400f41d03a64043d8950221045887c00c4240210340c0c16400440d80400100480144440c4680c1d50b14030070042036100b041603280c0402030010529041c00b810b40102441402141002c1e4a500c1103542404000032100800200203400b00c4480e0051046c0c6000303100324800c054403883e0102082e00940301c1155031a5440600d000003050614001c0407641d8000d4201d41c20701c1136a14542c1c01d10000b94450500301d2159011281014034401040201e500034107038590002c00c0040d0603142c148013441a003001230a00310f42d0440c880b0102039001003a2821184212041e504030b20140c100780000700303500038002c0e001200f0700054901e1814150001c104035412007040700c50079984c80408804680608a050852000400104010600c00c0b6054060710140414440a4a00090000b0882041035120a0284148070b003000038201040e042100440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 53498519 1250 53497269 53497307
    0x1e03061a0304031b0b06090403021e031801081b0313080703031407020d02030901120e0304030f0302060c07020a03120e03030a030b01110c0904030809190b0105130908090d03030e03041203 82
    0x50301c02e0307980202d014001041c447c0240c203a1400035043c5442040311800a06ca03855038003507040f18005c13250b5100d41c0f003991030071100d06410001c0100d652280c0c856170300c00c140b454054100710001c22102c2c54a42e00103400741a2803400300808102240341c0d0002001d1703087c0309803000160400240a80450401c00803c008155042945002079140d000700c11142145000d107440f00d10a01041c04040080c000c04584105a204c08240030040004001014603298040c0d000c0f80c031a07664041c10f280785841000e0b002500302c508403008000140030030868003c110940d0030408481d1603900c010074a5504441405000203442d1051001c2c1560090b0158108810b154050101c046c4010b010034118a0068030041c00c101c0c1620000340c1d2a0030a002c0800b5404151181c60300d0140716080c0703041c0c0010280034862080c0515010100f14408501c1103003c02d80e805142142400f4410003080744c460b580c0c800507400e160300c6203180c8500000a1000300b01400241121480380c50b0300381001880085802d200344650 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 53499769 1250 53498519 53498567
    0x150503330d05070e0403020d200a11040b1e0a0608090309011b0b04051c051905030c13030602030a050106080c1e0712030e010b030d1e03061a030403 65
    0xa4000c4214514144825a1520a0305950b8509103140c210039500486401c00321340c081c8010590f0200b25031082c1c21a6a543e04e03800348c02611900302d00030b046802176110f94450100840010f528a41001558100070070001e07000039540b01241c01002406a80c00c0d03000011401c42d14203240101c50940586000d24240655103803120030203541748a0105424144240406000984101d501100d465160710108000c41800c003482c0203a0758841032041d51012240e481e0504082034401c0040c4c1d002454217003141c0043c0c2c080d18105031100e60000c0d1010140e001c0070400a1080b032080051500110b1191400590303034501a0740100c00c583c01a080300040042c14001c0c0500f4030882e400350303840700b0a00d440051145001c4100a0f00c141300344800242101101e0700d504140740d42541c80342940b8000200240702000700c6104142c1c48400d4108081c01050240a5a0740f4981041046c010401002c0c10001202038441232a040504810b8515001100c4004200005c01d540f000102c0e100100400d1504c0320 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 53501019 1250 53499769 53499841
    0x807081305030106091a0411090a0e06010e010807021504030203040f0314010e030406080a020c010605040525111b0a0f0312120603080304110310050a0905120f0f0a020304150503 78
    0x1d4107586c8081c81140c0342e1080e140e98070822011244c0c0da0a00405d01e00c2c00c0c1d035070b07281e44403500d50381180c50034003003805000742800550080302d44502c5061140d02a00f44070307070041000f5644004c041c000381c085120074030000c1000150840c51001440c000d0b01c1d01c001e50380a1144032820343d0b880d6010095550024002002126006400a900100010b2001d615180900c943d40d00415080d03001c43d500609150902417a4052155900d6a200c0010010b002c501c207641d8058980324052401150243d00c40d41826207509285d15140d0f003006001450000141e0b03441c0c0130161040c20540054030500d44605660b0b030000d40001e0b1201151041c1c50080c01004e2458072500c03d0f601004001030403203249074440038030542e4148200d241d08103885a08012505244903c03000070601710004031614400c4040070f64a148001c003d50b2504100c0550340c40c501410304250340580d4000d04c403c002544000d12001c100c04280400c156101d600542d81c181d22454003001d040d803031018503003c164140b00001b6111074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 53502269 1250 53501019 53501051
    0x9070501020d12180303050105041a060307031805030408010e06010f05031b0303091207080c0103020906160f05010c0302180103150509061503010e040203010c08070c0b04080708130503010609 84
    0x24210b00380b03040240444050f0184030001d00b40c0810a0843c0000c09403110301019010780c480380c140d41c03080d03c040090110b0300c101d80d0540ca50380c459a66202c00184001500f00d4400e400a00c8207902d040c1d0b80444c41d000c250340b0b0910f1a00290040355469456440e20000703203d003000141d005241450700c008520f4500804a91079180056a2030305c40304e8210714501054608204441d0f860101800c0c0c030072410309040d0b62a86039440c900943c1c000b409040c1c1c0100f89580f0900030b84400a40040070140b07055119803035100300801c01282100e0340b82000c014100415402c2c072030090200340d9910050b070750b11035500b00c0ba4a2403401d0342445061601d04002850200012200303417082d01d1081d500c801c85611080002041e414003140d10580d800000000411102c0c0426083d500a6200fa03000b8050301c4503a031426104414100c40c4036000550035543e280119600d0280c41340c00500600c1c035245414142d8803004602c0c0d01c0009a101c00c5051224200401e0809200342402400b0161040020340107100d0805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 53503519 1250 53502269 53502283
    0xd050f25030204111204060608010f0c053702030307030b011115071404060302090f060702100503070c061a0901060201050c0a0503040510020c0610091104120609020411040801050907050102 83
    0x41c0c0651390740d00c0035040c00802d000c00c507020100c2c19040240c0c0c130b180a10301070024100350300515a00e542014044041c1c1c2801c4d0090f040c488880c0d44510341003420700c4451200f07020158959a509404001000030308000d8400b016500209541c055603230307450a00d50150558010707044040c1000f400380005481d815000c14440c002c040410006251922040c1d07003161009112680300c198100005000129150580c0c0100216401030b14105d444905070010480341d40500480a504401d42c0d0345003c0c1d1040c07041c0019a4010381d1814002c10707040d620f0f1110004c450183d00c13040d01401030410b03040c0c143d10707020301c0d540c0c01400140300a112910b0030304502c526501602c0c1281c3e051120200224041110501c45442c0c4100048000c42d250007040300307041d50314030050f10300c121090004d20006c100515540551455a01220105071500e494404c032846680e2030340d0400e440556032070300b04000503944c40c01901c03511581c200c043c40c1c445051880c010308581d0090440c5045902c0304008100c0369070082904 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 53504769 1250 53503519 53503523
    0xc1a0a0c0809150a09030510020703090b0a03020f160501050a290604360209010e09060402090409110f03010b280f0605071e030c080d0b0d050f2503 65
    0x441d15402030b034000c0b40c2150722981104045010104480c051180d214480d042124001c8046402c3c5860b55401034080b803017001809000640802c00a2040000750320040c02614503501c0d0041c0781607200e603034038400b507001607030800804c44800c0c0c0c0300340a1040901505420070001d48003005010510f840304c064800342e4800005803c5401400d0b10501c0c1c4e1203400340c03001401548101ca4a0b540c12400e144900d500300e20724502c1d10300305202c44610340610340c0b00b80c40b10104107850350f4006a100c1e604001d813015008103059400f076005c11151000703849078007500c1811486211460302119000c3d0801c03003110b503042550b0b8000d0b80341007014900f594a482032000b40b00120305501000345c503420355204e5542c4403074000340c1100038000b40000c0c2095220000b402940e0051040c0d82400200045190400c205120007800084260b07034400e0124144100910203800c1e840e900080c10384420011845561042d041a52660020320606111100a00274032130200101b400f014180c8612000b00c0e03540d800b6034000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 53506019 1250 53504769 53504783
    0x804110301020c010f02040608090303010303050711210a02010207050f150a0309020306070c030f09081b040e0a0b01090b04050408030109020304030e0a14031c0905040e01180c1a0a0c 80
    0x86811a2400c0d07044401e5107a02a00900800107002e90000203036100703108080002d6554800a0981039001c810b8034140c9500d59034803898078406440340c40c00200c20000c2541d1016101a01c031861103c194007001c3d6100c8008094a104003a0780000f9041a19941c0700c24090814045040a030b42e0305e0813007580030859140708003512503000680c120020070140b94001d405100d58402e20007150707004101e1289962007542d8602a000301e40030120303101141403041c45520f41c0302e0320b010070f29030044d10b82d40c004c0c607e80a400059010390f900099444c20040c40800d40b030300e00c049001404034040340d002e820308841c019201800542825a940360a40c4014480d005916a012000c07d00705445408070a00307840d4010003040556407118440324800740c6d1030145c2840307845054201003041d8484626020100100c2d20751034803940c503100501c4058110040701040c1950303185080020100401403481050b4084c1e400340d00c805040c90780140e14210400c032080a03074402400304140160f403080c03c1415041c0e003c03030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 53507269 1250 53506019 53506043
    0x20a0b0f06060901080c0d020403050601090f090b0136020c06090a02060306010c0c03170307020c0a03051b0a09020c01020703090b0403050c150c07060e100c23030c06011401120203070804 82
    0x384807100c82c00340302c50301f59015000280c008144100019158103803240e82030208030800c200e91245044684a010040c03500c002c19004101e001c201201c03802107142001c0e0a50700102c607600554030201e100b01e80044225501042d0f00060400c10025158882d0303140300204008180c13600081c0c014007005000301e042046c2c07000d10001b00043d48800400843e17104401c10301c40100b4000783d1140f80c10442c0c0c14401031050420048840ca0310318649000ca90700800074240c50481c03c20103280150144540c0c82d04400319120010300c96446100600b101d02e0500001600d030100e9180c0240310965070780c0003102a103c14002400481d10105207541090b00c03c0386c18a030780f200d4142c2c3d905024003600c10001c659000e01c03080040e031160001807045002c401103880d00095030706004103913803034403201070040c11072100c2a1181014403084036030b003190000c00900b206d05004000c4c6160345880d00c26004001491a0298080e86651300030703034401c0310000602030640c01c52400320401490782c2d4000f8000742001c000c1c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 53508519 1250 53507269 53507281
    0x60f010f0e010b04032a080a020108151005090402070b0f0603120a09090504020a050303070c0302010e03030708030109020703020304080a080a02060703110304021302041a07050708010c020d080a1b020a0b0f0606090108 95
    0x400c00b40d2520b001459002c840c00d541f0883e00781c46032640748044c1d003c10f6400c0006540003000d01c4646505020050807103065107ca081c0854464100301d1046402642c2004480f01159404056902c41c407801e0070129214030348a010301d800d100000f214015129000d0103c03c0e035370394100041c4020394001002c0010a652a8000100d0102940d40529054000040c09000b48540075240205580c000e1721800141410740c402e00d50350b0b01c661603010785121401d100500180d209900180b084078040c1c030459003055210b0303842c0d03410082e21030000c4452440000d10f20403501e030140919688551103040c1007059184036400e103140b6210042c0001d1140307141e0054105410b10a50644004d0600c14181c0b92109030681c41c810999413108205031990b100305480042c0c5000140512041856141d019210320300e92982e05480603540a070a07980b1094031844603500d00303c41080400c011a06036401455180824184030400c20340241c02c00001030f010908100d09601c9030011120300090a20f08040c0c682e90704 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 53509769 1250 53508519 53508563
    0x105070b0705120109150602070f0909060b090c040303030b0402090a05010e010309061a031002030919050a05030703030222051c060e0a0309051c15090201020a05060f010f0e010b0403 80
    0x580c10706003c48600c0c80001c1000c907800e50018401640c80e94860b20119106c0350145c0e40d50149104451344844582c00a100d00b0409030850500244105070114060103550001440100c007120041000b00e000b081c02c005050381809070952182050b5821031a01d003d400c081052003206008050501c81d00c0b05020100303074465840080e410f500844101b0000307400c1003c0f04400c00c0c0b5800e02d203200384a24019000b91922070300c202e07406190090300409038076542a0341800e4086000400740d460b80155258131001c11014001000002e10940c0d00590320343c60202d01e1001000c522500281d03411001c0d606001039158080403091030078204180800c14601464214040d16032640b10101500039409420109500940341d2400d0310070448142c1c09041422040000c00c40ca100304c040d02d1412841c280c40e28206855106501c42030061059a0603912547c0f1420300e400e8081c0e9620030341e18892030041140e00d01c544101170107061040b4038244c0a51600800003014055800040c0c00800c3c002000c12502c041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 53511019 1250 53509769 53509777
    0xf07060c0c0f060b0a090e060a0c020304030c0605040315050708070509030c0a151e08161101021c0509010c020c0f0f0307080f0c0a031e11060f0310060507020105070b0705 75
    0x4031002d000700c860340c5450050050300c100c400c00703070050781c083c08041055606406402e0020151340000c1005503074001140002d814409850310950008003c04404200c85100040c058030b250313220130b565071f881c520745035100f400b40b90b0001001c245804240200385e503010080c21f0b0401c0c114600713140c45050040009041c00c8a0224a642c80b0550400002d8480c484c81d28003c1090070030b845102d0100b40c01c100009600070101030400001e405007002130907c04001001c0050f4a2880c9005102c1030000f105031030880e400f24040000c0140b981d031001039008400c1c010303654010a40c0d402440004014000603565040036201c5502c54a007201ca05030a90315124003034a400030008080301c40469a54140b581caa000c0050f0001d0240901d4801e800d140c00c05000d40001c50f94040154603031040c0c0703481d07052208204604101e4051000075414010740d5100b40c0540703030b50724440e440c0c907a0701d04211504003841101039000c042403007014010b00c400b5070b0f000703c265a150340e0400382d806850354881d101101e4070703c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 53512269 1250 53511019 53511023
    0x21c09060f020d0902040509030306030d050703090f090e010b060901020d051605070605030f010e130318050a0b04050109050301090317041a150f01020624031c020a0312020f07060c0c 80
    0xb02c0410364198105031600f01c2102c20340296000c1000c2d40b00c0030340558403844111101038150740206420710240d4400c0d00207006190091410b20340f05622002c1101d41804254003000c030700346c0c9410805946030b00a209400f904d800480c2d5051038004910001b03922040d0f6800c0381c005100c0c021030006404e140d003201020780f40e0752010540d80c0040e15080c0180c50341e0001c1d19001503254001002103410400541d2660161080010f0842c006c81c5903507007100e1080c05480070544c0488113010006042d260390f4045030183c01038116654640707080070001803010301158000c501c41d80c107040341e8a000c40c2d004503240154050001aa0700302d0381d640c0c104480e00c80c0070300c81d170040e185401000304452520000b0f209900050f003281c40d440e9034211a4012070b91070006507054900c0c1984060705241d244c804070701980480c407001d0181c41c2d5000c2d00041d24201c02c21000d094001603089140200d040580c1301c0001d0a0400000c0c0c0c0840c03c0024101e1074450034011aa0000e004540d5401030350203da018005c00f03600e0503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 53513519 1250 53512269 53512271
    0x80a0c0323010e100501140703030906060f05040c0216030f24060f05060304030206060906010e060d0203150d15020f040b0c0a05010506040b09132909070504021c09060f 74
    0x314140607003004407609208a180c40e403030314400303d0b181c003004a0120045803816551b0081c920200309030f803090390307001e003404900345503442840c100000c0d46401100001d0240a021448041c607200a201c150b1303121610303613001c541140840390a09010158080103494002c1d440000b030081d14074040400c0000c07542d0000850034502d90740c1d4031301c03012500a00150355004505905040e81c0b61f0610401d03000a030b9008016800c010700003061410b100300c00035440503052409e410340945690206009030f100740055224550004100310603000107040318403c030ba4007074600c152003125030703100d007030b0240c40151003032242070b0300040c100740e90001e003c05503806490111041943c9402c0c40b000d090391180c00e000100c40719400d16000a2a515240c4151159080054040c5100b036880c49200c060700c40c00d591048400000c00030f00c0c0500d030380035800d80d42410301c0008980005410b1802001d840c01c0c135070b0b900092085004100b003181d41d80c80c1071104200d00c0078520707010443d940070303246c090082d00744182a0311039a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 53514769 1250 53513519 53513561
    0x18021308030a0306090606050a2a030c0506010608040804030f0809090c0d05010e011202090612010c02070602011127010234050a0506040e042103050124080a0c03 71
    0x389501100a141d810b03070700d8608002c1e090f603400040c0300340e074120301c04d10020801c00e210340501e80d4082c81c200110421001500c4030180b039110203464400541020942c009841104444204135041000703d0141c060350511058601e07165907080590720881c00001c04c0c500c1481c0108003004000020b5444c10440240036410a00d0401c403151241d07001140001c413010709040000500d00d090103500c6041e00c8414002014503151a000d0060358007001e03081d0b60304030071101d01e51440c0324130a10604080030794541c060407060f45815002070945403050141031080604010310180704880c2d8503001030460484d06080d031100e0b022030060b420128021050104514041c641015040f1a41083e0240424602c50b9041c03164484042c8043d203400e0340035068001030100024010340c0005010741d0390051080d609070100300c0050340c2c0d401c4e085c403100a8401c0480d49550050000b1450700e8000c0050700b02c04c40030180b0880c40c01d10003c1907041c004d1700081d125551004e0402e801c904c41c0d08070309102c60512140a0071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 53516019 1250 53514769 53514779
    0x160504030203060f0624030105040b030307050601090219091d06030c0d0501060609060903021003050c1c0b0f0d030f0305060d0204090c05040e0d0801030201050a050702120c030d0302070c180213 85
    0x40030f07011200130b4803910065500182061261b5244980200e180b00f941e030860782050f09220007402120f1010394503100c14030040e40051010800c00c0e002e002084409030f00d40395007a10035419000fa03020040140642c01c0703014030003413401025040406041e2480f082c03003900c9940103e41090120a1103035044103200101d42d00f80601500140c1c104c450b0390b990b05180950701d0808642c414031500009600c4002503200c1704102d07110360030070740e0451110900e192074403401a0a0183c00c0c110050036013103c0c3d403900d09144152800440d108402141624030050304400745d40d00920418889881005059589004c94081c3d101c40c00710144859014008101c0c204040c149200e4054482c42a207100700d040580006000c04085210b005448450303c51000c00d900355801034916801c04c007d440f04000c01449042c3c0943c0c1d40082007009011040b000d09068511701e011304d4205205d07060b00360b0615004001e0000050103451802c4200e95510a803070300c240e100030383c1d400080e105640c0a5800f151180100ac60 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 53517269 1250 53516019 53516041
    0xf060e0a0c080c030309060a050f0403140c0901030f0f050c0303120f0c040302090406020c0a0c0b0d060f0b0d11161407050102150f0402010306050a0602010f05011d16050403020306 79
    0x2580e038000e044180000d80e450460030f40d100461940a070305a0028007804001c0d05056000d0034280020b410081d08016040c1500380941d00154801d031042051004641400001840324012122064420010070340c1103494902c840c10407404000c140900e0107007001d044c003400b03204240041c1c20081c1981d5503021400c8190120324001d840114220610101080301490b0440889089030380c051f040c0a44c3c1c0e500d40c1c8601e8000d400c43c1d131844034180180017001c40094400c00141d005400c40c1c092058941d80303090340e1401140e40541015080e030242e00e00a02c960001a42500d0a0415505001c11701c3c44807540080300d41c0c0521100d00c480c02e2251411001080b1300c80c211506404111001c590390543e541d001280d40b00345600500180f00c80080101d50b4058070708001980c003070300606000c900383d9901c1c00400c0384048250f1100700141d40d64115030a04450718060f40d03005202100040d0f05c0302400c0b01000302c5050001e0110740449041c582e90000c1e1074000c00c25580203580080c183d918528040115103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 53518519 1250 53517269 53517283
    0xc13050907030207210e0d0f0f0c0801051006090b160b01140909010b06070609050309030607031a011812031701080319050a0c020f03010609050a090c0605030c09040203040f060e 78
    0x403880c05005e0301c00c080c24500074420005504207651101c441d00d2251007802130071181b048007510440c0381465440c0c003207001c0725885944c1c540b040c600046140d2070140c10508440010b0501c2002e0300c0d112008224090f806680710081c1d501d02c0158558500807443c12800c0060700b034000921020009000003160381d640035851007002010b50741103609541d002c5029080b91038800807286e1044c07042c4900d6010803840e60145084074800d0084074584286440040d207080d10407140e010009442d501c03403a904980d400c141c1c4500350030a090092100329070500c10002090369000d001d00c080035020307040c03040c9841403154071411280d41d020fa100d1941c40300d010540f20f038040d5000b04035807280d5503001d00d11184560112240c01c6129910103142c1c1c4020350800901042d03043c03441c0e60542d210000450354000a1043d1400703903002003c0094052a0380c680700490321150b03440401846401c0c0b0400419201c41411280c10b01c0048800690383c6d615032401c1a000313507007108050481803a107500f44041385d10015600b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 53519769 1250 53518519 53518523
    0x30509070801090f05070b0a05030a090c0302030604060605010e12030403110406180903080606030c0901081503071e0608010f17120a0206071d0a05060f04090c050403031101050f0c13050907030207 86
    0x605c80c6c0e5070315841500054820b08014074000b5108000180c0070315680e90050000c00c2c428986100d003103680303400292402500f9541610f1280d0f0301c0030b0420042d82c00c07080c00c0113903003425949003a58107030002da0303141c880c020391202401c0004240900304e40e42d40c42d0f034410000780c04582011384c866503010b000f940007041e2444088020503079803008a2503070700d011429a482408024082445d00905100445002c500908110703441002c064403007130305a6090001102414000210500c040e03240b548015240c85039a10140c20f05c801070006002034161901e040068904885c00c80003210368004009103000440898140091340101c2c05824943d40414554000c4a941c2c0c1d13107940c2e0804041401403a0b405042d2116846221444104061b060007000b811a41c000d5401883c10300c0d40e5101071009a490900f40100081c100003000c2c401c1642296604240c508c2c504000c105514100d8550460b0803006007112082003c040b03105148000d2481c803d0000d4000641486000d06240304060f019401800742 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 53521019 1250 53519769 53519773
    0xf080a110c030102040320010e04051810050609070c03050f0a09081e03030732040e0702011406061b0d03020d1103090a06050408040e0c090a080f060601030509070801090f05 76
    0x211201c0d19050003501c098941242e03903581c030000450a200a04847e100581341842a1451008603640d03461185034414540c800703038120004456504031342071444c028280c0c01080e1400c42880710585a048643d507000301d0701e050601032202e841c00d040d54a070103000c10410200800103500d005050b84040e07040100c5003000f089460708526002907034004101c1041c102c100d98010f00003e48001d2285a4060400d10708111545c2440e035080741d04e001d17075942c00782801d045880003c0c040201282d20a251984083c00348020006298081400a40e807040074101510502c2e001c0f80c4007800d0a030380722428030386410250403101d540d11100c00c0a40690001211031111525182281c09a1300442040701c2c032410080000d0b1940d41ca459079a40014800603100761010f00c3e00344000b19140e890403101500450102034059114a2908100080124541c000e8a65500714040d00400144002400f40c0c012009080218290f0383d07140321946400455800407071150b0074000100144110180500c224500a0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 53522269 1250 53521019 53521033
    0x190503090a061e0f2706020c0a030c050d110d06060305120a0203030c0a030e0703030201051f061b031209080c0106170307080c0a06112706160f080a11 66
    0x1d0580f0580b40c01040d00100252080300c2540310b5124690404100c0000c0c24400c28410400004140f540500324075040c1c00844c1040038480c00760100040d01000400302c030700d0101c060640ea1144010b4603207100b014041d4024881040c00c00140c40041021401c020f080d10b00d9008035402d2140251850b407200fa0790703500a080e08010348590090446000024940056181d500c1d404000391080d44001100000c05a070b420110061003024002480118043d60010a243c00d0a860b1b00311014103004891600c03600012003000196007100c00841c40310300103c0500c03e51942030400342d0707518126074068402c03940745c5030039403041100c648003804054070514001c022050700c41641d05482c041d1400096482c0e803091150b980012000c400400e04200035005840280c04070f551507406030756400c07507503070b0308403801040425982c861290103002d0300840e003034651264001a0041680b40c442c41c11189502d110a000d80c505000010704010b04590748140d1280d81c41114810003401c2c000001001c0740349005020b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 53523519 1250 53522269 53522279
    0x105030606180c0d060609150f1e0309050303100e06090f0105120f12040302040f05010f140f030d020d08010f06020c040f140103110f03071406070203190503090a 71
    0x261861064401428482c610002c2549102100b0001040c071000007804208075500c20300d45000f1200240700507100c0c10749803410185000800e208061411041101031980c202800354441040c140110f00080c03002502503140504501412018001a003035220001c24000110b80c4551413000700d0b0b0740300c8410300c5e1039241d000c01c119080509403400c0b140103441d01c00501c141c0c03030810088600e0280340002c407400460080b181ea800c11030030020036032a40f640458200b041d41014007402e038034011300c64010045903060108003c0c0d1203000d40600131200f4000320a9044507201c03c0c41103007e01a006048a00004000c4802540c4240b400d42880c009074125000040040050200d44250303140c40d00070b00441103409003400014241c203180500407a456000341611784d2203581c0301034040d6000d08490a610341c1c1d0f810600c181e80a4031034076035010354001c0d0400c11041c10803620b1f007000c24004449aa80c0c929075400087c0c900b4810000c00300c2c007484000d0300342041200000080040c00001d030f0302848450b50365 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 53524769 1250 53523519 53523523
    0x1903050103080406081305070e04021203030403021c0302040803040e01091b12051312080405010c0914040209010203040506030c030a180305090f01020f070b070b010806040309090e0a0206030405010b0108010503 92
    0xc0c84002c05440c1d09001c24001d540c080e80c45154401c0c0c5040c034100380f544098460031b14005603075011002c506208000e200035403c11850806580e400d40c4021440c0d801c1564000b0340d980c1414070742c035161055014989070020701c00d804a40042050710126030700c6580380e000301403541c0000c0c401c0c00346144c54402c401700601e8510000e10607030341d0701d034030340d41a561113010003580900380090100100600341c607603003400258a20001540c00c59581d9891403240344c54541282100c007182030003020300c4030310700041210715158075402c14292410796004d40c03a10000c4005034914007ca800055020401004010340313100c011002e548601e404100c20f100c81c0c02c83d41040600c1003036021010380003a404010558181c00d00c0442d18600e400706104a60b158140b2012242c1440416000700c040f0301c00024a0809101c0c4c5480014050400c60010b44510b0500742d4001e01692814465045c8868407034910034640340c02030001190306a00900090340d2843e0038038000d4000c021201409011480ca500040b4042c180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 53526019 1250 53524769 53524771
    0x30e1c050a08040809060d022101120f02060c07170c060307050f181c0501230103030809070b0f1209010902060d02090a030204090b060a1d0403050901110a0305190305 73
    0x14584460340360000741d490031621118020030603138000c0e00c200100301c600e0311000c0041100c0350381c00b0001038a41c000e85241a4240380b12200644040b803021006000c1402040020310781154401d454011201603840411181d00501011581e1030150501c0041c0030741d0340a40d1000c841800105035260442c08208000141c00b041d1140c0000400038030a040c0d100720000d000300440b01018501c10001155980099003e203100c41c4454024414803800c001004000d005004418104074040c0d141c4900700403c003100c008051001804003d8290f011842100c0700344640383c01780100b00c178420764840000c0500c00d610343c043c403901c22500043c8800115040010300c1142881035000f0807807441d000840c2c4044010f900040c0069a00c441022000030059442d8410920900e11400700f880300c1d445c0440070400d8000e200c1d07000a07100b1103412580e00484058042d16035015074141006611030b07002200403a418509035201707800342d111700b54101c018143c0100c050280c03415280d11034144060754103003c0b4180c4030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 53527269 1250 53526019 53526073
    0xc051603030509040e01090f11040f02041d0c0c0d020703021003050f0103110102010e0303152b15061203210e070b0a1b0804030203011103060d23030a030e 68
    0x12080c00f1200e441c0c90203421075007401c8003000c00031a80203425141c2002c90310158404680407a81c0d040c0303050392800d00d405002d558510340c690840c02d05207040640b4400d03250385402c00815848000000360941484411f40b010060038504036040c50f040101c01030b44d1100180010ba1051059031b860000b007501c00c2c01451f00c0340040320b5802c00142d203590b1f41d64170b401554540c5141503540700d101c480c4070414200051403151407182034807882c807018441840200303008114240c0200d4007405010318039003104055140c009521100403500c0f0842004000c4c002c01c0d0540000200300c800c0440d41c0c05042d40007800030340c10710301c032107642e042258500c1d4000b00310381d91700202c00000c1d0400c01040244800c810040d066600c541d08010000b85443c5440e0b880104540c28103c5104101003802e1080d410309104c1c17600d03201d041250085c40c5080020002e5080e140c0c43d58020b00c0001e00f400305441540d090312800900c0b818010840c1c1c1c440c2280388014018118041e1107000034030945040c0d201007201d81d4101e2603944 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 53528519 1250 53527269 53527277
    0x4050102030f0a050123032125120c11040e010902090906070905210109050a05011a060301151101180203060c0306060a0503070e03030d090201080618060103091104020301060c05160303 81
    0x42840500d01e05000c0f80300724525030500817a02c038012020949000c10204010300072406540e0390f08040d142031340500703c03c2c9500e4181d00e0b102827440054501d807600440c131a0f8a0428a8805000740307031a5290351180d03c58070340c01c2030070b10b00c2e410f4171070301c0540040702014400c5501482542e50303c1c990a03940c0b101161004001101e07040201712500340140ea8820b210681c400020948030300c0c2200d603080d210703032007800c07585a8040c9051000b0300400784112038240320603404264000c042c00c070008030716000602901200741a17031020760030307141c3c040c03688030000050321002401001712202850040c203080e007400741c0c02802214005041da0900c04112880780400a10b000e040c030103804030454490304024100414003191030340e121700903075082000c0d10710311107000300111ba41c070000d10004092000141c9114002c01004440c030213800a81c1d0500c03a8040c40a20f0002004911400c026040340d44075224180c0051000001207001a8000e0304200307141e0080f41140c9000c0c100d1b11001403001c049100241c009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 53529769 1250 53528519 53528549
    0x11030a0507120602090301050403050903150c1c0902030a08030912190507140f06011401030b130216020406030507150f0c03030c09091b0207080d050f16080304050102030f0a0501 78
    0x815082c40042007090f0080c50014103280380540401c1c00c5800c26501a00407170702c0480e1080d514a0108206401280050942c1c5c00608085000c8081401491881c1c480d140c01c05030741e01100761a075408585882c2d0020100c400342010390410800300d0384207481c005001c0c007a4a0501d589201e0b42e400312126038541c9003044032400d01801044400da00085c004803811a0030703800c0d000c1e6040c010131100c0000c038120b1000e007025515002d80644985d08101c2e0007418182000c5e00c01c1c1081da41d44000c58403100c071405015a03520864445495800c030805d074020b5010b40f40a0012041c00300c0028020261028000f040b000d4140c6184290b03180c0505200c0100015a4211100000380c441d8110024150150920001882d00c41151406988040241d0103900004807a04807043d035040104100400340e079000380c042d88400080080040c8148020341100c403600040e500703600d10754040415009a005001e503034984c2814500035010b5403060b00d00ca4030f000b0604000c1400c142a40c4213003070480e0802a040888 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 53531019 1250 53529769 53529779
    0xd141b0705030304020d1704060f0e0904050309010c1401020a121406090c0a05040902030a090b070f02031206030f1f050a1a040509101802030f01060609060809010608030d0203010311030a0507 84
    0x41c5003106d5000b203030219450349883d00714400f1940035002801d4540c8501081207408800102505035030b0a03528030514458051201240d0b0100407990905420302e00b01200001500f4004902c2107941c00c04c4140350b10000305580c465500030300c034600000600300e0500021168080c038000800054a0999014019801040c0780150100041c030401d40703036003030042c01e1a82e1a43c0c800100d800c11034503000415120100071080000005003158480c2d01414610401001600000d640340103030000d584020f4005004078000c0e0394100103a000000007601102c000302c03a0084d4224001c2c40803400300c8480360401000c140b40421134000d408101514110300c41c2c0e10402e400400003d4030b000b0340381080601030300c010b05649010798000d100311100801e800110901081c41070518040c02c40140714141d0b49008000d2000e60340c444002001c80b0807a00e089091510349e4001c0500501d640d511018040c800002c0c2001c0c00c03503440c0c0166040720700a04040c3c202c54841030070b01d070301e03618258030041c8160041082880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 53532269 1250 53531019 53531029
    0x109050c032d010b0309010f0e06060d020301060e0a020a200c010507020d0c091a030a0c0509040218010e060f0103090b0a020f0409060b090306070c0b060d0201050d141b070503030402 80
    0x3684800d0034042d001810308001c0e040002c6042a000021506070000c20010258402d019060202240010030840c1580e0031502c21348484020300494400c82c0c90b500a403007990740942180014002c080c514180310309012260720000e501010806010031110303c0035186641c2030004080d5101c81e880080c01d008290751004580e16400b01004903846225202c81401203518000b40201400d42c81d0b40c001608040380100e5146199260340d0141700b42d0008840b98000341c0741c80254070440d00107036145001600c0d00c0c0b000a01a2041076000000b021030302000180f444100003060340920000d5941503100005200110252200700d04040c009418036008940f21203030550003407206041c034410701401c294480f81e030034081e2440d90b805030780000d101084c9803042e41b4081c0400c580004150805600951407a5500c5a1001000300310031711030003198003a0000d590050703040710041d0088101c100106150800460742140d000c0d1381400d070700c2d44032003800160303203030b11200b10f840080d003280c001c505690321503007009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 53533519 1250 53532269 53532301
    0x1407060906060e07030603020f0a050a0b0703020109050604030c061103010b071b170c090a020c0d08060d0b04030f0f0f09090902060d05071d0301200919080f060109050c03 75
    0x19901541c03010300084100743c0c070600d58001c002d42d940214040340b46004001c2c03034400c890b01e954898500e02004000907640c280094088450300072a044c2c980d28681000c2e070044c101080040c082d4010901080f00701980403400c11003041c071900c2c1c10030102c15004101035140c0024003441c240c1c10303000c1004a01103000307a40540c0d10041034003640884175840b2001440400041c001c9a103a551000d4101c003450b01c0d003122501d501014280c001c60a0040700890550758014000341c900a008101c0003040c1591101e900c034040301908006010f0b203509145c607005001d80e0340103030888005802284a41ca01034402c0000e8098800103680303140f03000d030810200500804661004a90001081024021107603180c01043d1246407682c0312018ac4904c0201a0290070026003011403103649000c411005062800c0065280e071070444c624507850340c9184010603c1034482d4100600b030741c84070310000514403000203003102d6034686900688610788d98a100c1c007800d40e134060301c003110326010520000340c600c100f0081031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 53534769 1250 53533519 53533523
    0x1e081f05090a0c080a03030f050402060712020307020a0e0906070c050c010f170f090d030b060a050f270103240608041a07020703060b010806090105040e0c04060e040606050114070609 80
    0xb5a0351260603954481542c0c6070b40d40041190740011140009264152213841e80030000550103200f20f182caa4002032aa211b00703680140700000100100e40410310800699400c0c6601030030380c0310b03050785031000c2d101c4241084502d0001c0344104800103031030900c59400b01040740c0c0d02100070084035a0100064480311030b052031007003c110b4101315030b1082c00c1e44c107040300b4000c0000306281d0b8428200040c0440c1007119604e4000c080c1801c101c0c054100c0d480b801e007100c01140a51902c0c0303440300070441c0320814620405207040001c100003949008404034086c3c0c1076411b803100740c83c01c006d40d00c20b8451900c0c0c150b401010a100d803d00307482d030802c1018040c01d001580107208800d4050854250050030059410603200b0348016406410300784100140392245100608003400c1000342e80c43c10600003050020140580c0340955181c0c090144590410860f03540012802002801802e8542403107140680084034103582c060b08200700040d079540214034003500c041c1d41031070031340c80c0c01159103903000500501001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 53536019 1250 53534769 53534773
    0xc02010c081e07060207030e0a0b030f060a15020c0306010f030c05040b060c0a0b060307060512060f030f0106080c0f040501061e05090d030503040c090204050a05040e0102040f1e081f0509 82
    0x442c500c200720700020302c50079210303c3c2c0041e1141c0d41420020059002d061659000701c00d040001d11001d080901a40d0344002002c080310b203555240001709003060543d500c2074540c5a810307018079440c5500840d04410050040c0c08692080e030340d0740c000c1c02030b40c226840040c00703020140d5014070070341c201a00b140c615400c010300307050b00d8905d40c1b0355041c4c603204040302c1c15503a1078009018007005140c240a4075004040e90300c0c1082c1401032840324001101005055030303105480409080c80070380c9040c000b102680303440b03100810905030399800660b00c0301214006548503482d140c00f034007070b103180900c2541d042c0e6034940c6d034040c450040c4020100420074044d00c800140b00052086500d2960703181906844036105c0d503140c584a08003071a00d503089d2602900712030b26440c01888140700390f840b166005012140215800b05204140352800c1c0e00912485d000079015001421011a00d045d20001d0140c18a01d001140b40030071760386001c110f855107039200b4105020030b1003a06540b059411600025000208001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 53537269 1250 53536019 53536057
    0x5070f0e0d05030f070f0b070f0e1e150d050115080c07030513090c03140121080d0e010b0a150504090e0c0a0e2403030a0804081303050106050901060c02010c08 70
    0x5131510700f580045030211148103050849404001c400700c0c9154000e0110b003000d8802c1310060001815030300b00800b105009045142400303030b0b404100346420304c00502c06852821303004c0048155003003550100c0d9208903100c3c2030000024000e2003070488024003002030b50f44c0001e070303454601001029510030030081e01001414010401d01e840c0e00141c503402000d00e22800608402d0300f81d006015101c906280201e103404038001080520301a1400043d40e1000e440b407401d00c20014504180107010744c0242140300b500e004984048280c05502c0703254400b0040f14039110301ca5941c1c003150b499003180f5028000061040c40100700c031302040d4024001800d040402d445041001101040d0f04906941c065107841d043c1c2414800c00d109107071030101e0785c044588110543d2000242c040b07641c91142c1002e5104004c080000034007030003404000e4482c1c494080c1d09100690b40c1e6424451f020307254070b0203664440c24a07000001080c078000c0815004480d8181c5884620040a0b1202201ca4002ea10682c80c0301e54408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 53538519 1250 53537269 53537287
    0x30c0307091e05010905041b08060301090c0f0e010e0403120f06030501020a020717070f1206021912050705040e06190f1e050111060f071407060f05070f0e0d0503 71
    0x80d01d8842500c07090304030740c200341c0f904000600c0360f051580038500903450040641d0b071030002e080e03008101c00354070300307020700c013a1034010201307005004070000030b4290060940301045401607948540202c2d143d10140c840903036210f98032041d1640341641c0040c04030709401c10140d074a200c9a080035518402d41c0c10b000408aa0340d45640d8260391100031254016046550180503030b100200d40e00714180c1200d00101000d9003081052000181e81d402a0600003283d00901c50801ca019011901000184c0000d9038542010030000341040c0500c031a22150720381000005800c20b84910141c81c222568100304580035260403080c8a42c580309441048013003000601d01003151220f21100000600f101041d00d0010f21302c4890517183c0110759013000381007107004a10010042d200203003030303508298122908142031300d0b015019504001d21804000f42400c011038000244542507000a2030f0352410b030010300c219038038800203c80f031041c0c0c0100000803c0c0c03020803081c401d0401c03064100c0080e10440c01c580c58001c00c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53539769 1250 53538519 53538539
    0xd02150a18020406060509090901060609062304030317060f0d03051b0d0c0218101802120c09180108030307050d0b03060a150b04030f06091110020709061703030c030709 74
    0x4e90040d01c04500c00084441c41418000c0c2d02c0c6500c01202c40c000c000f15401c01c180208052058400c800030041201c83d501c082d8403500c58410820643c502c003803540c4558915000d41801e021103042200300c058000007030081d041c150035080da0088000c1000c2403c0040c1d940c152001c0d00035005600b4450f00b4020000f015400070090842c4214558076041c40a0103e441080074445090413040101901d910500c42001c01c2101e6100964401052401d0342280d203a1101d0000d0042c000b03001240920a0240304600341d447c0014201900195190f10641c1c10203c01c0781400c11302032041003041e6108100244080f0b00c10b201421050555584c003040c200804c1c070010345004821ba56074071b442030f03849500000c000e104d03d01c848010511240c00c0c41c10a031940d2a80152080310360b101074000350f1108014410410715058511107250001c01044110710361100007075542c0e00d10300071951210f182c00c4000c00c180d81c08607480c801400250b40114038507520b0381c0151400340c20282c0b503070050042002020034200e0003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53541019 1250 53539769 53539781
    0x8160e070509030a06020c0c280506070b06121005010e040303050a0c020a0305090a08010e06010806010e0708010501031d06040f0b06041103040204020a03110408030c01060906080c040507120609020403050d02150a180204 96
    0x400c1c104101289d07411203404400028691000d44204c808004d07240010304e00c1902640d01040460b01400c1503030f00d03090042d0802c0c103028000040ca928107000801c892401c481d4140c0583d0103564100300c155282d039003401c04c80c0c1560003541c02581c0055541c00000c5d10a40003480b0a840180a00301145d0350b0703401e00c0f800e4914172a511000d64101e0303401404a004100823060041c000c1020101c844c0c140300201818116040c015181050703144c002c0c180f4080000c2c241c524040744041308880c2240303020f082044007040384160496452040c203001c650145060300503070884498004c640c1d443c40d00c0b180d0820000358490185c403005e154903050285e01c5005140040c00041c0310f06009075944828458050f403c50f045500120708203071619905102516000410020072403007030310b000030251107900d170507540035240303a0113410882d0800b0b070b000c10b002c4200c4c0c0250041b64401c0c07040f01c140d03030f0103600141d807229200c444946da00179000c1c1c0090301040498202c1103901422000c51a1200501e801040944107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53542269 1250 53541019 53541049
    0x20c0f060408030a030b1201151502010204030b090a12020c100503060d0803010b03040605060307060f180902040906090b03030909040f140d0302041d04020307180608160e070509030a06020c0c 84
    0x180d1500105441e041082c4080c07c03080644008200e9001070902c050702e070002030f00400540d5030300c0c106640303903040c001d40c115806523400000502041c600076001a40e0340d545903a0407500b4900c240b40f00f031002070000071110fa250b0002002950241c83c008421602078100030311680c2d00c00810804840400d184100860103800b16000d095540d1030142040d40641d20081d10350340c0241d01010040101d0344d8040d1880710350341d2007850720420045005466400700081a000703a20b5913440003600040c18966984010200c03002e00c6010f00c0350b8503103542056280d0191000490704070f00f40e00300040005d0f55950400100510611015801d4481e01020900c0c010000710300b180803031313400074040c80030310ba40481410043c00d4032200c4a0141c60243e0210762a064940308980c10903498007070045440445401c243c0140140000310303980311410020050760100307a84a18074141c0042d1004c100700911850031111002030290051000c20500e0b0b45501c02584030741c001000d18050000040b035150b032010310840040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53543519 1250 53542269 53542271
    0x40512010c140702010801030206090607020a15030608010e0304050f0d0503030a090b09210a02120d06030b070504120b040201050d050a05060909010c0e100207050a0305011a01030c020c0f060408030a03 88
    0x1090100e01601e03280c00c20ba0190b000003014802c400c0142c0e482954541901c0d0f0588141d07469440340e20109429009082009502000084001c01c885d00d010b54104586c20850340e0074040f66030f50f040742900300c0c0c15841041e100c0d50401c00c401c3c011802c00c000b0002c0d44200190102403443c1c01510780034259082a0383c140f0456841e41400c90a220340c40f45082d4201040d44090081381c0d2003151503a04486014250868161000c100801494024021640700d001a0440c166a44c0351506120008154030b0108a610004501c04103101901c280d080c0d8064800844041150311801e842d400d8180c50010030403410404c003000200000c0316540110303405021003910203e182c1c01e04d1410454290401030486410fa89070040881c00c0e01c0d4009890000c1001c161803c02c4403942c410012401c040c006c3d013101c2d801000d00315000080120551245000200d8545e1040c419010030004400390f902d04807103580140e00058082846151034600181e000300000c05052a080e41c4054030307800c54200c0307800700c8042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53544769 1250 53543519 53543531
    0x606191e050f01050a1211160b190b030303010303030f0204180f0e0105070c080d060b0708040602010e0a0b0412020c040e0f06060406211b030605040201020d0201050c03010b0f04051201 81
    0x79050001c1004528082420f046080c030610138002804103d161030f013030b42100c2d16a000b1401c65904241103400031414101c500d11200c0580c14154601c0c0d409a54442c07210000d42d001e48a2901701d4401c04c0c80708800180139600d16441c6440440281c0160b6a072000c03580d6007004001040c0421001102d00301d0040c03040816140e01295075142154405840714182d41d0511080018096001441400c4254402c1405881d0034050244038001c2460741c00c0030031900300002e4031070107000c00b00001d042125855070092041503d6031480a44480807100020500340d02c20f000b0070005002d05071780d40c00c0724440c1e2048034042803104d4005829140307460300301500c54111441010041a041c0181580298103030b6051040504c5c18559004002500d01c404194040004010041100b6508800c40100407524660341040d12070a0040040000b80c40403800f502c80e00505081c070300c1c01070007654440c1c1c000700001030840e8600b240c0e00300d0300d6010484240c80c0300d804010100d4156110004c0d2048500b11000000301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53546019 1250 53544769 53544779
    0x140412120b0108130303091b15020c01050d021819060201060605041406070510020708040509010e040f060b12060c03090601060c05030403020f0f0d05010b030c010903050606191e 78
    0x10041000810411141441c440c00e400d640c00016079500512541c000080704916401e04400414010400900d1060241580910300160303041134410341d94640340c50f400c011a0303000142d907904814984140402e00606c00b01412190540c041d00020001c0d0091812000009000450048a61001042c80e480c088000c0c44502e90910800000d040303242006032400d030800e0700c0800d41c02410000d40b4410399000680e1001c00605001c0303d065424015000c0d5210000c1e1b28140165401a0007424003c02c920000061941104046140140d03000411101c046980d9202d6801a009110703416400118444e081143e90500b000828071680302801d800351a410010708150030003806921620410184441f4580070950100486084035811220403402c00320145c0880c030b484510040c1c207a030100300104401d007030060640001880940440c2a00c0c40d40411200640d400d40c541c0c00701078075640c0721b01c2c0051510306040d2100724010841000d4669941c1da66810b8400c2030705002040d0009421080003004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53547269 1250 53546019 53546027
    0xf04031805030d11160e010e1e040c0603050606030f0a0e0c060c0703110a0b03070f020a060e06040309061b0b04020409020405070908060601030c1d04241706090a15140412 75
    0x207040c038054440403007071444c002c260300e00050123001d64500540d903440490a9440e201104d031581c00c3c0001c0e28210700e851306080c010f0310800c0f030b44500c4000c6400c0c0000117603d480e18030f003264401c804400d00204551508890300f070041c0300c00d94028005100f85281d84000360313140c10241040044400c0100407035070a44ca030100001c1e05840b0700c54041c0c41412814001c0b50079210a99601c00914940340c0ca0341e0011400c201d281a00740d0030060030042c50802c80c400e04078408a8000d00c506d019440d801d45003695400c0c1190303000e95415040c1d900c400c40c0d40c0c80038002480c000581d90010700040001c02c1c9952260006421100d06507040b5010402d024010085d6a206000c19a0702c01c0090a003000305000310403010f8031201509404842001050100c5591580d8680c8010f2204200304c18418400c96043c240f00c40300303107880c040d220040100c881c0ba40c21b9140d002406902c11800740000c0e1414583c10b903902d05c030303900e402031045510b40c0d1101411030140003054015403155009620004c40c9070710240d0003130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53548519 1250 53547269 53547283
    0x91602101a03121e070303060e10091a0a060302090402040b04120308090f06070c0807061a041d0304090207080d0e0a02010e010c030804080d020705060a050414060f04031805030d11 79
    0x14a4680c05214941400804da100c000c456001034440d5076540c02c261170124002e12103034001c03101c1000d099040c49151451b81498506981c80b10740200610120448005414103289000c50307400751030060140a010300c0782d00a0304901502a00250805403501c900902540054004a0301117100041390003d1590054216400211000151041000f4030b020301da00c4500080000c024014000c07810020000000c04442000d50001c10422001c106890b80402004a22816074852810f0200380c10200f110300208c2a07000707000e01c00540ca06840d10407090302070b401c8807009031600c0c101402140250703072075030103480864400c0c0c002800114117188005480021a03c0010741080901c6540d000025042092940c200b40c100c400c09032144801800c0101a06c1035a00041040c01440c0920225503910f07004140940c1c403418046590b0300c070301d2844030b03520b030307030803501c00c126140007a0108022074029041c2545044014038481c0c615515903012a03d0140200320150002c0d081a05410400505000741d13 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53549769 1250 53548519 53548543
    0x50109020d0501120c0b1b06070c0c05030c01022a030f0609010c05040b03070c0819020705030606060f0d0911060403121805030a06020c0102070b0f01030b090c091602101a03 76
    0x59041d0700982e480c0e880e809026402111b1118000240c488841c0a43c1108a026030348640f0071039005141c845002400c0340c1281d4811584200c0c41e0304040345510300031078441e0010030182d0003883e004030b10860f04110054008032150700c10034024080c030b01a8601384044516000050700070445401c08410007402c43d040920309508220040c8424861001d9200c12250001d10500c0c001013852040e040024083c0b05280c0f101c101503114011241e0080c4e00490340c01304907075080b01525070072b603220814444144181005001001810402409801e51681c4103006e0352b400350403407042203456000030071900d90164000307507225a50b584bd40303004590310402d101481c5040c5200741c18418078100100383e0701c03a144030300200b5107a000b080b50448141c095040d80d2440d60090341008260801503010200c0050a02054a22408190000b003032030790001000080302d600605442c48940d580e0700c5500d904c4140400c01c44c210700036860b0480041c8524010606079062403219958610704220801d80341078010b041c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53551019 1250 53549769 53549789
    0x30b0a0203060a03020112060f0915080102030c070201140909010e0901050912180612040c15020706171306050f100501081b03090708030d0f180c0512070504050109020d0501 76
    0x10400c00b5114103d040c0c045a6080c20034044048202403128081d210715000700441c0c40c50445c0006171103020703412541c0014542c210700380c0566280c8100601380c0c801251006150380e02004203000551107071102d4124038554914203030501000e003000031a454804c0c4d10150030800c0440620026407000c0c0328064114003200c0050066200700c8103554444d02a158400b2500705d168001441c80d030f00d41804886c2000a05002c2100d10303c1d19203040c2404510601602000c1d80b000b803a004012800092400242c81c02c0d1349170100090040c000d80104240700501c2c10031380e08000c484c0180042c0050081c580036504a050348a02850040810941d902d119030000c2d040040e801c00784050a84100700030f00750241c1c244a51176499485843d40b500c0c1000c0f56012640d64400010312071610003040d401100000310104081c41118880100305840c145510000340c60450001e20070021860000c240d41c2928560b881500c14040e9610000f6044550076440005420380018817168401064801d943c007601500403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53552269 1250 53551019 53551021
    0x1401060509010210110c01090b0a0c05070f020607061d01060509090102040b040e060a120f111516030e040603111503010b0706020c0705061b070509090a030c060e1204030b0a0203 78
    0x1c0002e689800008055460541d1030600b00e510008540407601a5100c2c040240846522890f15007100c0400b2900c0b4100c051a1201c91900e0901c81e1080390f4140790822a482010000e5401f000141c2d440303010200c50003680d40150f00d1480c1c100c4410201c0313003044040006070962800b0180300b00070600400d90540783c0d20400c401e02102c0f1030701d410f690030740700c452001140c1039580d50003080c842ea0443e0003506020404141c80030800401030030f480c51082c845c8042d80c03002072544045c40407440e208050325030001c10621600b091119000480d5030410300a1802413200104007010508456103500242c0d0807070700c0b200d1403009608004098480440c04000f103c0e02d10b40c9444003814040c05880c10050885400007199490685c6c104201c00107004002d01072640c9591841860550768808040b80030a4081d000b8006800e24140c10424411458100038101c0040b866900712412000040211012941c034505030007114810840450f0103284114400d075600d04500f050000028000c11b00e042d4180100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53553519 1250 53552269 53552287
    0x12060c0e010f030504050a020d120315120201081b0a050717040e04330506040e0105011401030f060b030403080601021005060d03080c0d0f06051c020604032301050a14010605 76
    0x203090500c60002e8540026103840341e103011400e00c0003015005e036001a041062a040c81003006408640c0c094684041110b8000004110b160020a2168500300d03160007140c10b0255010f02c0710103610002400c07003004e4610000380c2228480d040010780000281d8082100020880d904c1c030015004910401c0141c01c00e4600400341e10311100003440140040d10305100172441503508688200000c1103241100c150a1b0142e810000400f02200c01038030943c18840300f0402058184030f414103a40802d100d00051883d00c10041d030141044c000c040d008640e881c000000c404a108001c0d5002d14840e0350341c0d40c1d01e4180300c0002031130710f0481081075521600c2c0c03a0600881d035803a103000c0220a64582801480e665034090000c009005000290404506020480080542552201c410b84804440c1180108138403c8003441443c4040d00007500101c04000600129940910254801345c010865200f101c001da1a600e09440017a5501074ec23940d220340040c0f0074400001d135458050491494070034107141c42c075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53554769 1250 53553519 53553527
    0xe06030705100210020c1b04091101050307090306060902040905010e070203070b04020a08060906040b0901200d0603080703030905120c061f0b0f070507060c051b04060302040612060c0e01 82
    0x3072259511600805012158050092251202d0800111021904c80c907642c1161074440d5900d401010402900680d801805e140c144900d0380020741005140c02111f46900054440d540050180d0301400414200040060010f00420300544800c180c0562564a001100001d841d81a08100d400e01311000030020081d1380041510202c50700451082c0c602d46460000c1580d03000301d9048940a0f008481c200001c54a000403010f0250b032103850701030065038038140f0b90b5007203800c4120440908101c2d8544c001280350303200040c06010801d542c0025400e503481d50f03642943e42c00715504401103030712540c080051100921450b03400c0d207a030850301c501d00355907600b4180e16040c009084410003a520b41c2c94080006076800d806025002403031401c0e03900c488095510015800011089a40b0701c608813001ca22144602890070015a014005000f400070501b440900c0140052010703170450f035501000000b40e941c078084c042c02041c555965007a50700e00e80c14117106840c1c0c807445280500120050500d416688 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53556019 1250 53554769 53554783
    0xf0302030303150a0b0c1b010201150e0c2b0b030105010b0708030901060b0309030c060a0c0203032e14010f023705011418070518071b030302040603060e0603 69
    0x303400404030381e0401d42030010f91044e40d25007042e0203004010400013080e95001031040704484847c60744040c0c020007440120700340e07810140318900082c80342c68100b0864442d4a403450b040388442c6070280c24060341d0746803c400c410008800704480c0c0195141a03260241c070b8030500fa80c01714150001e0200d903040c070170b00d03200d980308411000740307508000000520706007020750101d0040c000d01c00100765170b41407202982d0b0340c0340c000121480303540c0120808a2601b100c03611650b0070068903500030b03604641d42c401c803c15200f4104d0000e00c010195554194181d090380c0030709000038241080f0402d20200096000419010000d81700303c055500140c0002c025000c0369002c8038505141d42030034540e44003d50b005505140d500ba200030441d40c203112001888070110481184907040c84040040119001551240d0328186880b441e900714091440c0c0548401e4010000f45e0300040c80c2c2022048241d00b5405000c030507058941c15070000303a0104007800800c1c3d05024441c01000e07039903190303403c90400d0000a43c0b181a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53557269 1250 53556019 53556031
    0x131407050306010c05010608160909020901090c0216030c090501090b030a02060a0c080304060b04052d1305030a09060318020109090905010b12070303090518060910080321010f0302030303 82
    0x400042c009078031440191041e6540302d030083c000f8580d6400807030f1390f0303580d07401004134601604540844e0a11482c4a0381c0c544940040040403203902c3e04421a0003400e0381c40041046024000ca420b0805080580c08002988606040c448851401908000b101e0041e000084058202000c070222540c00003000504180c0480e841980c0741c1422005840720507004200500c800800320070081801115800040c0d500d0054405003c142c1c0c030680e03c0d244204160302903543c203100c026101500000481c01040e480711000940700d0b200380321074554070701d150070080113100040d14040c030074414260316005040404039003a506114503021540040c011080601a0304130203507a0b82040b0302070080942084108000103010621000e005c01c03191b9884a165000a4021076508440003400b8204450319030301c0c00046009070305c010784406080064124004c1c014000300840746401046000c2d00b84001c040b04140c600c02c004000d1101d4a070070b560918141c0c0003121000c2114801c0000d13880210031030307034491 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53558519 1250 53557269 53557277
    0x108062401210f0204210c06110c090a0902041406061b030f1306020f0a03140a02150c07050f0607090303080c190e0f0406180c0c0501020d05010302131407 68
    0x100040c1805012040b01e031900300740790750600c41c0031200d4585031380c014400d444e05192200394103072440300200c0d14801c0082000b005100c204008001061051000b20380198a0300d050700c07405031104001a080d001d0981d03d0300c200381c1d603c50405007146424890703c1c8030b072100d044500340e140c50450005103050046800c030703088045621005441d0b6500034001c03144c00d001d00100942c0c0b1040c0c0101692042d49503409144003500c40c50075a4913148500140189206506980d880d13443c0c0810b000d50215500f048802c4010340c40b6000c14003031072002080f1010301c107a18414403a81c985000e030904034980490880400603580080041c48151380e0b001030030b241642d406d8142800e0ba600e410052800f640315031188906001400c1c100c0000d144c0d0310200c400c29184003203400007803140e4440100811140301d4401d41300004001e0b6003800c181b2480b82c06c84000140c10703080240701a161900c4050980c0c2c0300301d01a8004980c6c0e0001402140303082c070f207c0030340c1c10042142040510799200c0c04482c1241f006c0d040c04240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53559769 1250 53558519 53558537
    0x6072f010e13060f0b090111070e07030902010c050607110d03020f070204050402031c020a140316020f040f06030f0209090f03030f040c030203030c0706090603020c07090c030b0303120108062401 85
    0x2d802c541c204400516664038100111503903407102c0d07103454024404a0f0f00040a91110f00c000c000300044840640d0b848102050a507110080107074000c00c10100124184040361005001054050120510410706911400099020030301024241204402000c0515105000c1c1045807580b01082d80c0d40598192400602926103000203803401c0d0607082261315085200800440003540401c1c540d00e80c0e4854141d0161142c02c8442c0d00b0388901807402d4416104030b020140001502d0b241c4607103030001d00301a0002a42800840a040640d403240d04280d40a43c0c107000007104506010803156401211030020b0b0500c045034580042d00c2c3e200c081d140015584000300403030244180314560310011a070043c01c032075a8201c80300c03240b40c840c18240304070800f282c0f5003500003480c64003d000f01e883d540b01d80c07005030420318103080b080c10003041e14000000401d55200380c0d244040e2820402042141c0c40f00000c0c00d9150301d4096440e2030044000e00d408481180d030811094003011710040c040511000f42010100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53561019 1250 53559769 53559799
    0x70801080c0a08150612030d020a020d1e03050a020405130915090309090506010e10030c031406010504032616060507170a020711040f0b1306031a07020304030206072f010e 75
    0x1008046c0603842e541c5000014214400d490654002c08070180b550b0207a4801200801c000d8452a841d155107080c48402080c2c040c480602c00e074403003a4004000e44c001030425403114082641032005102c20444540d96881030001e1012610b030440c0c807804030100a000c1300a90303940040c00c030760444c85110700103a290340c00309045a001d1440c6960192010700f40d000740444d0840d005000d402d001081c02c1c0801d103030070300c41200852041c0000c0d2041d5010785070285003a1542d134412120111110310400c0c15001e50310300d00140e00c2020004c000a11508000c0403c0e403080c2c2c2003900071100c02030910824054110101520100c0c0d03060b00f2584400362950068031000c0b64281101f0310301c6810f68070f950091403d1a15100311010307071f01c0114181d5058032411455038044140d50102c800c1400054002d410f46290b641c051070100e81055030000461060b20300f040d603207501003041074019140403034401180c9405486440d0030302040501d01c0a000e6118407114402c1e40000e0104c1c0221340741c04e400350300b800d070f50340c48 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53562269 1250 53561019 53561029
    0x20d05070306090308150a140105130b07050a17030402030c12011409030a0207140a170316030201020a1e120203060d1a0a0b010504030b060904150203070801080c0a081506 75
    0x401560000d6040c81003c419283c0201607020403642007050160314800819079041814640c0d06565030a1442113410b01440e005440c2c2d9001407200c4010480a00f0f001329a21040300f000d81406480340008100c1e403155842e114000c19103a0700440d1040e14103200f0840540d500140b1b200c845c400541d940142d000b0080300c80c50140c0030aa04d003918140d8101c06003c101580040180b00d001e074a5403e407001c1c82d80f100c41100c0123590540000703500c4900000207100b81c00b40c011000c201500458200d91900c00000024103030411003007402d80150f5030100d2810351298001680c254020b80118030304280502c1200098211201c0c864203030080399002c03000440c10303294504030b44030f01d5401000020010303040001e040320304042124100c40e07060500308201040d50040c803c2e07500392640b0a00e000541d5403014180b04050000130803c1d00d07100200400d68500a04500c0203600a030519030360301503203605191901e031601d101a03812a00808805ca020400740e000070901b1100300000d0001036101e6201c400001e0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53563519 1250 53562269 53562283
    0x51e010f0504052106130f110301090b100518010602030d0e0c13020304060f0b0d0b0a0902060a02060708090708030409020714010213060e0301050f0a02070201022506030e0303090a020d05 82
    0x16003115807a0448000d2201d1130900400032000001191700d50303541c4401e01c0e030038680351500c014452031001648000007010040011101340c0081d0001950223000d441d41642400181d131460004000100c0c103210500303000e2040840e07460785031150405549400e1000350340303228200351104415551a27032003202c1d03141407001c1c408049000348500c0c1410000710040000794003d4400311006440d0075902c2c1d454840602031515800802400900c07500c11a407980c00d0004c4005050111203540d80c01004010382d101005005411115070003410f00c2d10b48600042c1c00e00a0140901050390b000150801010310300008036810390301140b4000d40c44e4610792604c030b070703280d4040c401c02101540007013070140709034051400b6a401c603082d903540c04903001c0f244d009040c00c81e001a1412207508800d4000202c030231140382c00a01c00c0602c1032044441030000e1401d610b400b0180044c0384152500b03103000400020b9818080c3d80044c142c4900518a1801c02c160816918200c10b2000fe0141d6030a10340c2400344003041c4025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53564769 1250 53563519 53563529
    0x2010309021906030606080604060506040b030903041e1701050c0d09030e040204080f0613030504030303050c0d06080c1503060907081314100608032106040603061e06051e010f0504 79
    0x40b8150b03448050207405041c090044c01d00182e2901d00041040c41c1c58020103040311305c0680340a2900381081c40c1e0800c281e00003024030005200400c0001a0544c0722800c200508a88a1403c441542003400c80070b44181541c402d0220703a030504040c04a0a034505044905841c0400070028103c00c1501c1c065800001c0740c1849640301c3d10108000580010124420441d003201034196004d50303442000b03030070080c20005000780c0010307002d010034400240650b000c13513080184020074030300384200002450203481c020b40000c2c106401c03802c500b2809007440b500c8600560076000e9402d04610b0100080303070946030020014003c101600002c1140001010780038084c0c9600700d500c40d07240c2a400b6100542da44d40d12055003e485250090015a0143c0132040d50301c40c0100301784018513503808100100c240b0501030800c1e503000c5d59501d40080001c040340724031401c241031150800d24110901c40701d842101c1c0d03141d00060041528610244030300c0744210303000d44000000d0816801c01d108000d003c881c9400f580e049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53566019 1250 53564769 53564809
    0x91f020c06210603060c030c0a03020c010c032004081005070513060216061707120b030f0106030b010509040f03050d020706090308100f0602030d0207051006061d0604030b040201030902 81
    0x1e102c0b80225460b840405600c29281c070070303945840c07050660f500c8046440b802014814004540c0c18201c080082601070f00506e0301504260007010710f1402c590808148001103990f9812006140203a0342520103510103034410142880c1c948100345460f51070411000c1c500c03903035443c0010b000302d0141c4152519a0789940c156540541c44e0100a0366a080240311091101d101c40c200046245c89800d08c60024000700302040c4030398913030200c250780e0343c2c1805d400c40d4850fa440340c02c0185961002c1100d4a140331004001041503403440c2482200420180c1015019000180401c808101d0140c9074100c5268545405032352101080c40c000000d0140050040c01c007418024080c05050340101d0315070056002c031600c03000c5503603203801034840619140f00ba240940c1060061461409440c0d002e0141c00e8044e100361400e40c5000b41080701161215000100881ca149011300300101407208001c9140c00140c83e011714203821a150411325200080000b81016214120401152516104d1180010010032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53567269 1250 53566019 53566027
    0x705040b2404031109100909050a060c1d0406150503040807021c0614060a0b0c03040b0a110f0705090f09031b0c040c03050c070201051e0d02090a0902091f020c06 71
    0x4880304455105102c1556120003100c1c1500c01307407030070741d60300b50060340b81703280003424945400704420260800d03035819511802000700400106009004510b0090100d5684100300340308207c0700c0e20b9016004120030f005910b032174000d1117540c0c1510800003241280381407071510395075140740c444441d10031404000e411080700600c1483d0200c00e0000c030050584038071800c0c000d0009000750280030803011915990b0280c168030003009100016401001000300c944e00303a80c68241c40d0301450b206941300c040e642c07000a060613103034034100e4030074460f034007000400b6000b030000c8030715160004030152405019290024230b20404200804010002c960301d22030300b86034030092845000242900c41c2060022a070080d802d08081604187c860b20900b440740151a09031814041d00303400444554000058001c3c00607540a50b41145101d0480500b507042284880980c1e2100e01c01d05001040d8415170001c4500d80c01400300c4802c83e40c41c0e0102a441c401c459691440400b01716508a02d05545c115146400c210001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53568519 1250 53567269 53567329
    0x1f12050102070611090d0809041508060601080108161503180b0f010f050a0308070503041208090301060f060203090d03020120030a0e151306090803010608100503030901020705040b 79
    0x24002e441ca90303005070401c210104911072a504140304105d01a9030000c046030800000901e503074003400c4008001b400015191407001d5103004000640e0304143d0003580b1180c1000659a445a56140901489030142454504116602003030329a6401400c14207404c0641401c01641b0907441025060554100c4490146050504040c0340300252000c0740580480000403500135645c1c81e00d0011501c1c0a0801481103166484a05558000074412125030004201c0040c0e50445044400c03040d90040c0b070529a280c039102c04050844031154030030b050a0740040010000710b80c01005844a000e0161065054480a4601203005149131202041c1d0b64050a0b8480c480c050810040c620840c003441042004e150b040c0301d82e40d075030a08030700e10701418116a40003610800481c2070099015119010119810603944d42e01c4005410980201b40065039001c1000b1000b00c101504200600e420f0f006589007140150000751148120f0041a000d9900c0b00001c01c81a00d501c44c000403800c0c040f4181d004281e80003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53569769 1250 53568519 53568521
    0x406091b05040f090b15040608090114070e091305010f0b0a0902030c041206020d05070c02010305070e030606061c0603080a110106060912060b1807020d171f120501 72
    0x14080084900c100318100291180104121010340702200f202c09074107898510041c3c06408914140d40c6c00c020881c000e04140000c05c805440500300d6034449001c1031070002c0d005030846444595070303140c040203401480000e5810489074910343c0700135164038006945015510f0140d4002c400001c04561800c1c1d99560f10000682c000d41290030203c608202c52551034281c00300342c0c041910001210b4030100801c10000042405441c03800b4031070b92015051194040c802000c840d01150000042000c5c82a0f1100310341e4035200e0243d0106c500e04180000c00000b90100f645c420008007001d028030340000c2d03074580d00c10441030012882420000e040c80003503105d1414513038940000c050320010a0340d400500c0da14000600407001074400954602000c280f40c1189661100c40c12881035408941d251865130aa80700c0017050307422030001d02000b00c41c0d810009002840c22400351480c40420021800444c4201180d000c00e9030802a0043c40084009030100081c00914032030b8040084092561040401c100f01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53571019 1250 53569769 53569781
    0xf07030b06120109080d0c2307030e0402070c06030f020405031207020405070212090d061112010f05030f0303130201111e070f031101030507120e0604050c011b170702040609 76
    0x58442c618050807141c1403900707035641c40d400106491000d0040c0100c1d010241c0c0001c82e01c04852410342100b44c4e116030403c40030210f182090b20019000035805041c1904110b0500074041c003680c0031880d01c8000c1d142d91103502c0d03041c055103082580340c40c08140300095035010384002d00001026103100300400c44c0e20a0495000360012800345003081e0010301210700210314112700d501000c01c1c40d860803006000f001a449100003048a0160b5a85480314000c1e18802c0680310048400e000380b002541000300660b580b89081e407043c0d119030702c011004040d9080100681e9040418031401980c00341c424401031f40c2444e8032414442c4244940d28081743c1159070158403543c00e208060076940c40d1920789601400c20900c13404081d05a070b1280b02c0180143d44030350b004039030140140c605650091305064801381902c880d254408603542c8010280300074410240325020301e401c824284580304248020300d15542d160f180001030012030422078000d40380c0000c081165211a0b0003001003140750780340c5100c5030090030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53572269 1250 53571019 53571031
    0xc030105060306070f0e060d05131a06030304171005090a03120603020a0b0a090e0702030705060f10030b0c04090227010906051b030706090606081207230f07030b 71
    0x200301800718403141000b003025030050401c0d650304030070032140510544c0ea030104c0c070280c0d9411520400031480000114460140248030044412100440d20305101808601c108101d440700c1c400001440b40c1c9036000406c0b10226a4042108615000084803a50428005941000364030341800c040020b041d01c040340e0601a20f02c20f44402007107003450b0520804440e00c60000940110310300c10103104a1500402600c0c4820103803600c1d40f445515400c2c5911117403003d81e1a4005039102141c500c08004061003480d9020403c0103002c503540c42c00d2428200180c440e840301600ca45d44901c04034200e26621b408560140c8960301e001d40da02c201034450000b00445400390600364070406101c6102641c40b5030b00392001c44d0030541d1040d0428102c505000385008020802c0303510341c4010000d10002440d140503e030003460003034000150642c54000d200d400c0001e10010042100c80070015100001e502c0002e0203400400240c0f2400c0f0311000d07103c42ca1810752004404c0609105045000080026603200c00f4070a42d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53573519 1250 53572269 53572271
    0x204021815030112080304141c0201060e06060304110315010608041a060d0209090a0c030c06030b030703031202070c09090c030201020f0d201e010609110a050702150d0e0c0301 77
    0x5000301c0079080e9140400c0c0601070345030301c45018002c0850703281c03405140c05c180554000081400c070504004d107041c424141e506d404c1c000751451407400917020701c58000101381e00460f8180030b14003400000c0303062000030001010b0300310401455100c0c0d1010000a40c90001018208610f940c40e202e010340b522800f00c03011a01d001580d070308034820502081045010718009840c007010900e1030350800c442084020022101d500c610440c400100301440c070f807600254040d02100d400c1030f0510b08000c0c296541c0c1d15403107000383d004907c1000002d030f02520a11a0740c1e18210b005864200d58600a0004040c03039000c40c40c1641010142c005200204071040200c9200b41c00300c0b20f0b00c8041036180c40c3c850f204844c401010031a80c4000c001001d110340d5015003490100700595007030b40c0c5149000ca04100b42c04c0c0b44845a03a645003002e100500f074502c1030030b240201605505080020f42880108075104e146030007030003480740e160080c1c0b002d02c12a0507500c009180c0341081c025440341c1040281d40e21fa803410054403135 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53574769 1250 53573519 53573539
    0xb031f06050d0c030b090f090f030d05090f07030b0c1305130b030f011104050909010b060304030801090e03090d03050d06030501061d0c0304050c0105180a150f0f08190902040218 78
    0x503000307205c0c0703011488000d407080783e90341c0d2400118000e100d00144580300c0c41c05068005800d9020034401850428000300002909051101c40c813854140f003508070140d070b94402901400411082c5061691201c00c00c59603030354a80d10f24481c1130300000d00d640704640007a285403940d01c0c21085a08080c480c401d003036040b14421941e000d411400d807a4902d9400207088c0e0100428442070030500102a4814609800490008040c00205129070300c100c03000c0d40003074900c9005104100c124025060390390b91400c001c508200aa20010710078000300c8000405001c00000e076080482c105070001c0d0000e5070088000c1194507030311010700c4141c9444400c0055003240c13010005224400354002e40e80a40d070000b0003081c8040071000151803950051000009100c01e0f03102d40e40907950380c18491005021400e100c40c80107401100c020b40b9240203201c5510501c4021045074011660100c15560b00c1040120607a026103418401180101021070029400c1400021181420009070750060500c11040d1000401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53576019 1250 53574769 53574791
    0x80313020316030219140d0302010b13020909011a0a050702120609010515010201050c040b03090a0c080a030e04020702010f180f08070816060207030b07050f070b240a0b031f06050d 79
    0x9003000c1c5d03002d6504001050b40c024103283c10701d8594104030364442c1c000054021303581c000107600008a0800122110740008001c401428014603140c014001504191001102440003413058002e5007851020040007140000035540c0d1614003c2204020720180d640c90b040241c00d05010b04001c5601002c980ca40d0010b4441c0c0b94414844c5c288242050041d0340c0c207190614217002007591019201030480d10078401141d0106245040407002840072000a0848803218a000340c030f044480c006a40c032491043c400c6c140540d810101c950a01c110314602101c010314080340c0b10710341c20360b5600012118009040003043c01100010b20300295a040c60484501c804e0010680628403c1b80c002c0c640140c1203104c1c00c2001607083c0311100d404c2501e90403c1c07401d0000704025111283c00806050381c07131003030540030700c0707111540e00c0c00c0c000d41c0c07003404190a00741c43d6040e404110080810310070000e80c1c400c004000b94000780394101c00440043d002c4da522001c5d699451008215406c50081c00d1280c0d440c1c0411400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53577269 1250 53576019 53576059
    0xa1e020108040f030201020c030307230301030f1401020c0d02030c2518060b2b05130f051002030403080108070905040c1205100c020d03110703020a0803130203160302 73
    0x14059a0507910110207a84940c2e44a8860360014411010b40d9021720000d0501d01c0d040c00994811640740c1c0d0344403928219a00c0d1283d0030420f200701c13421034940401c01440070405845a091085800400c0b1901c1e100001c2c0c3c1d003e0080c8a901d248003158010300074801c003050b50100040c4804440380d812035072042a90303400d07190358214492810420b8410142d081081e0704540915038650342e00b8100005225941e0910000c00740d000400420b0906145121041c0141801c3c070340d61264100420708000d240b404100e05260028100001b802c1c04090800301010000304000202c004556040b05645a00f858617001c0e054107c00e0080c4d0b02035000d42840070070468030342d11805216035001184460040c1c54844074200b10902c44c0c3c41554903000e07009902801e17200c180644105046141d0081019090312800101201c600141c810030305c8400700405004658006141c81c074150304100896501d8803a08407440f4149010403009401d070003040d6403c603428800d06114011240259804009903498116a034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53578519 1250 53577269 53577323
    0x50d480506030f0901090807060507020607020601060504140a0504230106080c04091109120f010c0203130b0f0403050601080d030b09040b0c0313080d0609150803030105010e0a03060e0a 81
    0x254205605100248010f989001d00c00e070003402000c000141d0800c9070f168800554400700d4141c43d01c903121028003001c10390401c6031542c8007071036101408803541040c2e80100b0f1840750344500c0c4525050811020240e41d41e00030190001c0c10020801c01075100c0703060b094061540801d40c60300c1c08140c4c1e5000001c0090082083d5880340e00d0042c0518503050070700300c000c1d00030b06106c10700e1003400c1c4040c0800d008c40d40702d40c184541c0d000ca69078000c1081c00b010300410380c00d407988103801c6004c6400c00c0c0400b2182c503400c40382e000240c0b000c007500c280d1501220541680c86002d181d0003d8161b00c22070000007000c220114000440b807400e43d8050041c01c20200c01d00071001310640d00100a9840d21380020843d903070030405103400407030004008040ca0300c1519480e038180c000e07054032900e02e69250010040610584699800c03481c0d6880401d002e5494409025124001442072605001e151f80e070040b40d6941d0022100091139200c43c08010310000d0001d0140d640000d14001c840084940700019210312100c6240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53579769 1250 53578519 53578529
    0x16030501050105120118020c1506120316060b1f0504060206070809033103060b030d032304060f0501030b040204050604020903030f0c0a17070b0a0b0a050d48 69
    0x190020340d01e40344601c008499412814003100340d0900c400c2d181d11030188200002c1d27001391003042042c0c0c14254204039a2080b00c008800190f03000700440314014410713140b4000d8041d084000000c9070f484400200c1c1940c1c20003a4120038600b6050b60f000394041c1c010005e07105807a100da00b11a11a5070380705e0282e50014040e2001410341d030040c41f0440c0800361120340528406554041c1c01000001154100c1001e000303900101c031056200c0034603450302e007820480305642402c1403800b4051442c400360361860070314000b03050004100c0c8201c002401d018168000c002840c08641c0100906d696900b4034070616800ad64040380300c0d50400e00400c1c400e203014002d031100341000502442c6001520800c822455000c4040b120b100e0141c860b204010403110601c110584080551007030351010300f460540c6148100902e04d2600e01d01c1c1030b09003409034882c03e50513030540f0003e40b8100381046803424110201244030301d5103e60208078421108103141000c02d00c2092110024000d242000c0858054480d034900740a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53581019 1250 53579769 53579797
    0x61f090603030c1203060f1719021f090302130203150f10050a090801051003170313030c03021606020106050307050904020d0201080c040b040b03061809070b030703060b0316030501050105 82
    0xf810118881d00707500e2030038000608000a00039a244ca88401101455000d401c1390a20704214071021681030100a08020000340c1d1000c94070115400111000c2c80d58140312011440440b250200b80c1c0074202c000041e41c3c004082e10031810000d5100750107580126802d8445865141031201c0d1401c1c80b030058a0310301c0b401000903410b00007058044400780c0100d0030100411281040c005101c820038801c00c0d00a10110006040322415814991105000120f005003110800c104200c3c03880b000c403160311141c59040c035291300c10032601d040803440c214400119100120030740700c0c0044c41a405600c46d00c00c90340250182c55a2941c2d600802010718403c44011390070a000d100d52900540c0b04103074050744441c1601c48541004d8942c001042c068000d5045603411440003c2840040c4c0f50141d60310b48907016840c4012014644250000e07262916841549169240400441c40981c000d4000c0c10141c10015032460710391501582010b00c0d22401502d96010904e442d0011450b03500c99001c90b100804d00351a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53582269 1250 53581019 53581037
    0x20c0a0201111c0e03120c07030204180f060209061902011b030c05030c090103060b0408030a140405010527030a08040504110408120705010b09070519110a0f0c0305061f09060303 78
    0x70252140000b560f0f13504d516004924100c5001545030b0040c0500c1e2040388000d103400782c1144140f00460f44410940c000d1581c00d55003520009814001031028903501c6800541c03502260710100b4101c0c0a1f0700350034181d2100d0b05841140e50b950551000d032244124200f00700700075541c40780c103030215030003517107040009882080064581c00340e1754018803402406140000d030326941c80b89451859041504420f2443d0000296040c01c01d601a0004010401e405940d80c601480c007000a0428814a1072031200200c40b99800035a03135000349011601e4801c05002e964006c8000e262040c01584280505d501c6140f51802240f450950b0f0000d0750240d46070100201004d0030103403101c08090b040391504481c0d81d901d40d540c1c1e060700e4454046880c044c0069840e001c1d1641210f00020928015100720740e800c000e1000900c3c1490800001c4813450203030404031032a83ca160905001c03280070000d800240080c4100024001c0341c540c103205900d4222021402c0000d40c039200c19002068504d1440702034005080c40c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53583519 1250 53582269 53582323
    0x105060910090e12040b0c060601050a2c031605040e0109032f01020d02090f010f091205030c06040b06090703060305030f0c011506020102040828060c12020c0a020111 73
    0x6400364662401032404c4528a0550440007100c40d40720b50084141d921010504021504007000810381081e0242465030400209890040078481301e010076242d660840044090740f034000040504007900040d0076601030a11000300c4905082c141d1203910b0042d45048501205010306120700c1e40141c0c0c0c1540d5001844090b07040c90b4800901410030000a64070a40c41c25800440034402042140d066aa0140e1100c6400c410060303d034039213004041c14404d45c4030a540c40580e00030500b40c182c99480540180b035104604003c0c5c0f540c054902c14006501c41d5105200602c010000e1991043c10211307006074007950b5810007102600d074a440001d040d0350042c0040040811844050682079980400020780b5100a840029500050354091030150758002010b11900c0014070a08401d89008000c00c2061190758201a4107812000009049990749030030001c0858800e480c0941015220030342551640301e0400c815403207003040d02003203000c110101e20120000c203003c148502803001c2d82c140400b407581c0070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53584769 1250 53583519 53583521
    0x1020c0a08120702120a0b01050a09020c0d1d03010e1005061203090d1104091101030606030b0f0609010e090106050408070e01080a030e0103060b070c090b0f0303040b0d0216060e010506091009 84
    0x40c2800326030160340500d05d020f00e41d40802c00090101e0081549144951506003401242e0900d504405922070041002c3c840b10580010000300c41c52041c98151a0901c00400804010a4a40155906508183c2c2a80c14002e00103001250191030000800003611800200944070b02240f1418007150410701890101c2e16000705c2070524240030706d801e09805040f4070001021900a41c408481300500b400400c243c80d6418400d210203401303181400c00c90101b00c1000140c0c0b4500e03d10071a07100d42000a903080c0181d100c0d01511030340c2e1001801814003035840704d00141c02604a40142c5c0700900c02e142001440d610080c000c503040340e40702c4001d000380241586046446603442e0030103d0516171941c40000d9484096001815854022101e5800a030f0400798241c4c06d03203c240c1a240c0c41068070302008280b9a601104642c01c66102c052205d50790b650a80c2c614001c1e0040d078903054414204254003405202c120341000e154240c00200800c1140c2c0d48500300203540c41e080e00d0340040001c40b1403080c0002d9040e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53586019 1250 53584769 53584777
    0x50403020d111c030c050c1017040501061a180901030b2703030109020a0207090c0203040b130902030a0c08060a1a0702060f03090d110607141606060b03010501020c0a0812 75
    0xf500c2c01c803c451056414074000004140118001050b030310b0080709208050180448500b012607441100d16424000100010045071003000c0c0540e922011408004003544040010849081d510300503d240c841545c03015000304103c2d42c81181441c1d49081ea43c41c10805640c1640d034070424030001c0303890751103a200d40100031450443c2441d540071280c1d403000400304007650007000c4291015a0300d01080300000d0a00d102944503003581800c009845c2080c503008001c1d601500c20841805071240100210400d031901c17a80e000e682d0715440041071044011450b008070852894a031110819502c030101800f03041c05072880f0781d4504054408920b005200510014506079000529141c10125200e020741200e07401079803100e4072540680b505a10060b048480b401040b1004005000549448000a08503410002100100300c000242d202c580401d81c1d100c407250b03650030860800110361100c090756290780c42030007858058441d62888442e6407030600d40ca40c058070460005030984404a10100700c0c0303500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53587269 1250 53586019 53586053
    0x402040e0a1b0803131a12070e09070503070f0f0e0310091b180b0a0305030a080906130302120307020c0909030307030b04090506180309060705070f06050403020d 71
    0x1403a8040400044410006000001d0007840d20000b0303003182248041d840c440d10382c041d00540c0c00a0109601014100c07581c0001c603421448241a008000b101d02c684d03500c61b02195002407000501400110741e4006103241d0341c06010741c4c0403541600d5080c1c091780c081c001111600d0004015030b9214142038820460b010301107103036040100c1c199001e103000a05040401c06641540740d5a00d1100003804503152185611214115409035141d0515070044c500c4000510315149881e229840c00314541c94050200340110380090a5a40781c0c422100001d080050664020460b8452035010400341000303000c1e40081982d050b00103000b103842d440c1040c2215003004040100398052890316036a95181e00000b1807040e802040590b950b8a0f0080000d02101c10429503140034038035018007032002800010790143c210100c020b1a40741c400103240983e01d1841404400b9402400214104080040010f0f451050380c00d50000c101b045510361108440718010340c440690b0003210119280301140c110b0016020307400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53588519 1250 53587269 53587271
    0x2010f080103050607141e0705010f050105030303070c050c131415010c0f110406080307060e03040b0909060d1403091c12121b0c020103050601140301090b01020f0601060206090d030213090203040204 87
    0x1d01421051a1803503000030400d25524000908e04040007002e101d003440840c00c0c04820080ca5040101107641c034000242002d0501c5112070f01c040501c581000300016483e00241b00c8000c0c802000040c4020f07041d6592940801a402c0f00403502c600031480504900301410796030341100080e162240c3c0b01003905001c0594501c0c1100383e90085980707a5000310000f602c6558015940c8130000d10f0039404660341d0082c0324126420a0005100074540300382116481c031012200301449407100000a800c98103401070042a0000d808206012640c01101400e8003c8088801c15180102d030044207a0304640d07580010502082c0e0040b5441c624020705c2c031a41c1c11041c101c40064901b141807401c4c000c141000903038401040c200106801150b0f41405a103500101c02c2c84c00b11664011038440d04220b01040c01603402440c1c0b01c50600c001a4400c11054042100c2d81c0c01301d0f21296581d54019489038000d5a00d1340c1d05004046001115500a008a801e55840300c1e0b0418021460414440000d40002c0d200b26402 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53589769 1250 53588519 53588527
    0x30a050711040e070f0605120402010e01050c010906061401030e100225061401061b03080a0212010f0617071e110a06050a06060201090506060607030e1c02010f08010305060714 77
    0x20ba01c4078030444225201d200010100282810518501011168000e10400808001500105400b4000c841e0490350a0030640d501f2000c0c0d10042e901ca0040c451162a55071801c4030380d00a11201d604820b044a00d80c04a800032086100c0045099500c080085039065000c0400b2a1001400358009c1c03041d824442d43c1e20b407400946070300314041c40844807400d5442d00e48845402c401c144170111510b005183c0f500301103a100c00c2d9103e460304144248803000d000e10410500140601e002c41d0111380501f410700c03080d110b00f5038682010364048001030203071000188040300718805e0b0300105469640955a15182d00c0040c400028000d419103000c2d00c104001c12a0074112440700c49410031403424040e204080c085507610b0b28414400c02c0322801d9000d8421a81000c3d03004010580c0441e001341c015500395095550740000f070405451307080010b09010340048100307004149030003512600c04683d610036603c41112422250b400c4494800a00001e0002d41100000c100e4490141000c4c00c10418001040c2d030030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53591019 1250 53589769 53589803
    0x30715021309050402010306060f0f0c0c050604030305120c032a04090c0206070206071e030b030102090a03080d200415020c030115050909010203010303140a0c060504030c02180702030a0507 83
    0x810320158016190b107030301c6406000840d170705806450050012403500301443e00468000500725180c001c2d11a051020175000c0c80207200740002100090140a46101c0d41c03690b0742c1c600180f840d0302580d85281e0340350340c840c0070030060303082c1d0801c4901410014400701e29a0130001000c0041c0a4000440c44880c24204400142490940124070601c146900900620300d0a51000790404000400031000c1142410b0094030025100802150740c8499160000e1035404c0200424024858004610350182604030000100080d03c40104a05203a04900740b1491052441c0c0c3c08080003c440c04e1045150184824800340780d0309110706440d1616441165a01801100480d003100c10704001c91030040d000368810300c040d05000da409500b040c810802140b445d80f56850041c028000860408071310200040c02c44040e521540d140c0285035042a0100041d09041c500946055075150040b07000c7c2c1d01050500e0641b84045407001d112700225000395107411600041141c441d80208411980d20100202c0210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53592269 1250 53591019 53591047
    0x2120103060203060f0108071215030c0e0403020d02010b0f010503060f0a0f06030b120601120c0e160905010f0c060f0e011d0c1e0d0f0803090c0f01020c010203071502 73
    0x100039400381e800142d60b41003020510110340c003a05440c0d8140700c2d90034244808168410003424200c2e45050000401d00e0500750307284901c2d0900d50010300a078410b801c02003030400102181501443c4240c00310303503940c0003801003030742600c0d0008903041d0712401c0d031000c01c2c800e540a9401581d209000402c030042d11250540001d14102d21074200a040f84546401802155010300c04d041e03050204643c0c91101d450305030f1103c0e0751194140210000b00c8040341131102000304a2005001400b0001c1c440e00d954940314094003001890103001500150320b00000040c2540a0350780c403006035680e239651690344040e646991016002d044a50b61400b41d84101c840a0480203204001c20309104018100c1005541c845140c506405c8440e0a88500880300010082d8140d071502d80c2c21a4009456a150b90b1a440c1809543c8511480010f0b04101001080064088000c103030840f6592044076038584000e8100e00480e82c80d661200d86601580c0100041e00104400c44c10881c1121030005001d0f284c1113100c1d00e040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53593519 1250 53592269 53592271
    0x903032d0a060305010c0207050a0302040f090b090607081303020607080603030f07030512060103050c03011404110a02060910020406140c0f150708011409010b09010c0b010803070c0f080304180212 86
    0x700402d5588030140b041010a0041440002003440100078542c2001d000841402035844000e105030303541d1203000300e00c5015400101a094210000c240c0f00e1902e0900f130307500d070720301281c4900005010200040d11581030b0f0070f44003042c45c1c02d039004000d0707a030303030f003102500c0144000d4241c56142c4003c1c40307060f2411110500420204d44640d90f4240c4820700316104603c00718001e0301c500d05140c1060100103020703101100b501d0440d481c103c00703440101d0000020400030001900b9052869000040c40074403107800182031802400c50f001100c055a2550800744102d01890045400154a80c0c24880718104400040e007054a4403005440c92502005105458207800c0b1164040300e000740000c201099170001861401400c1701109144128190030004d811102c050082c0310b20301401240007411b99108800007100281d200070304407500e50f1503164156a0703401a8800711291082403901244c1c0c5400b02000e1000c8a107008000c5042904000c00071403002803d42200000076800d0004045001080c6089 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53594769 1250 53593519 53593531
    0x200304090e070e0105030a15060506040e01030506071403132103050603250b0703030212010e0114010903110609030a0506010e0601030b0f09010501030509100603290903032d 76
    0xa81c032414001140d080284942c08a540c03840000010817a46d00c01040365020294403107075a40e049089412110000d0550790001e0344c0005004c180440c5401c0c050380c425040c0ea000e030044032100c0e40c0e103a2048450440c1e036140c6c40c24984050010543e0000107001d030074151845041020000710340c000a1404203040c10800a002948940c184201c9003018844e040c41140a246081c8013902c07100c2407a403500f100b0f8413580105240c000b0f070107018188654141e5890903030b00448020300b541e4600b0450309416080c050801d81c5075080000c13850640c090071501307040300c0e0301c800000550410242041801d810803002d8075058014400b02c50001081441102e020309a41c240074260381c200310000508031303500c128843d03000740708102000070140d4034550241d046031024a40411141d640040e40703800e2091113004144041d04214001c410081c42c2e0080d02c0c1021408041c0418030301500410980b071450a50b4989003581080011642c0e140c40c41095030b281880c03071540c0003002d014110701c1e910080310031591 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53596019 1250 53594769 53594771
    0x8030a09030b100b190807050325051606060305100207020a0506030a0b0a0608040b3103120204030506040209160504030318030b01080f0f030310051c0203011104031a0408090120030409 81
    0x80c5c4951981294080760049054a0103604601c0c0c06c51040c002442807801030059101030340078110140380b1a90403074142c0802000800709400051805078040c102030302042340d55000d400014040180c40d4802d4030343c2160014000c10145280070140082540f000c0c1c00a8119038580f04401b8054072111300f52802848940e0ba8001c0d6440d240c240b0003025240a040c0c005190002c0d4aa201101d10381d60066030b07100424043c640060f1954941036990480141c0701040c0b01e80080750000c18000e010417070910850090301d6181165940034200203081414141c0400411014001400840d108010b443e00c10410100c1c081c1c801912610366584248099010040315400799181030040c00050002c1101031501c0700066056040071580300c5403841950003424000c140b030b1120340440b140990a041c1c05190003400800043d18144507140040d4440e00045d01c00501d060b81001034040c02e11440ba2081e81c00c6410b960500500000448030401010700c02e0580320402c80f51007070078210a00c0288000d21800700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53597126 1107 53596019 53596057
    0x10e0a090c050918070b0a030b030106120f06020403020d080405010318020a051c1b030203160602030a03051315050a0b040e070504021b0105010b090a08030a09030b100b 74
    0x1d80c407101403054200c00520781b10000010300114a10796014080c031041c50302418240e0b0454840c11400c03001609001c40858010340040d906031b849004007501d01540e070740000b030304000c526038107441e00b41d00007604100568041c4241d51001850803031240c1a84550f4002030300d800303014415540540d07400c032414488201070002e4150340703d0f402000c00c504c402006040d400d42c010140030880c024414442088a009202c50035041100c0b100e500852030f10030070090440c0513240141c400000c8090740d450708c80c005200400030902e01c000c2c520300040e46150481d00c10040d41c006204050245150000c551046000420207409561091342c2c0542e1b105503e101d41c1140c409001070695a55203004004224028035a000342086081114403500150f218500241c8900c030700d03004e400110300c90071010000101085401540221a2214824540d03a0740a60fa0003a5102e000b014000042100e = true := by decide +kernel

theorem cover : BRFrame.Cov 53417269 53597126 := by
  have h0 := BRFrame.cov_init 53417269
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53417269 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53417269 ≤ n) (h2 : n < 53597126) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
