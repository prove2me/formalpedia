-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:19:23.533862+00:00
-- url     : https://prove2.me/submissions/aaf46106-02d1-46aa-b353-74e5a7d2b789

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33093530 ≤ n < 33273386 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33094780 1250 33093530 33093539
    0xb010c020a030501240e0c031005030f0109050105070905011b0f080f070c0909051510080f060f070c0c030f0303061a09040c2f0a0b0405060109051b04031506030c 71
    0x203052101c00c04400c40c900c2c5c00d08450064001c3c51904150fa01000030604a40d9949080fa011580040d01032820b00d0340a010003d62903400300050701442400100120f19140a45420b43c02e480010341601d05200c1460000d01559034001c00c1c6007a02c00e04240410803090450900d028800b15540300901002400100d4401950a250040049601c540000103003181d8541040046441000c8002d010350402c6009105502d90140f020340c00c10b6034243c005018541d510212450550700320192a0250004d604114074280d005400a91045a07424010070948890356542c3c4070040314000148a100380d0b0741c5640034144254441405402c11000010f840c1c02c0e41641481c0d00c2d084010b980c0d200310f0400c07001c0100a8411101c000528030b80083c02d1a00342002e81c1290720400140d0358013a454841c1800103408100d8103810a4000d600541c0500010b506103c43c020a035800107000c46420380260002d001071041d039030111011660400d4128552a03003541d00304000d86542d0744080c1c41500314070000304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33096030 1250 33094780 33094783
    0x9100c080f0712020d1e031d0d0c02041a0303040614090d110405090c01021c17010f0509010b0906070305031f030c080c01110709050424020904141303030b010c020a0305 74
    0x49002c0b11940032118060b4540500702c410440000841c1340902000c40281200b90003500b0621001c1d804640b0303540080d481c00c2301d1900c0d2260382c1140b8400076507130706425015400c10340304182050849042c41c140640222020a07030300d100350310950003000f4800388041d000300c507503005840d0b131301800502401ca001242e0800b100242d0a00c8400303441a407800300400c8142d8800190f91000c3c0d007040e006130624403403926051a03c003258140c4c200071700c815001010204421417091501901f6000342c0ca808650070401400b5080c0c405030440848600304200b0410b40e0703520903099030306407580f600d403c503504d80d03c104030821030401c8211003146011b0b44500102c00c028500c1100400d6500d89412668540c144400458041840c0043d00e05550804101801804460b0700803652040c010132401915840850b40400b807403804842d031141c41680411030210620b41801001002c5840c0c5001400341e0506c03101101000c405503100500b4160785207030304821a4020302511450079001030110b41c0865036030504070f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33097280 1250 33096030 33096053
    0x408010c02010f0507030b03060402010509011119060b01110a020603060402040909140f1506040f061707030302010b011403060d02030f03070b040204060501020d0507150603140f06060609100c080f07 87
    0x75243d03038204400540380070b20a01c02c644228400070000e01c4a611150010b40f15503004070301c1141000248547c0889008d000c0000b0950845c0c040c3d071462500c80e244c10030398211091500c041d07040140c1050300341c040302400261802010780440d20140d1303980307800e40010001e10a0303501c440417042c1000422014010700440040340c0200002c1580c0c280b14694214644075240c20f10081035416000c0e020500d03906003944420400e41c1d495000140240d2942e443c4644e00c081d946005c1c1d03e680c00100700380101a820300a1520141080c00c1c0309200d01e41e096034864850000510203401545102e0341c00b0155982088401d15941400041d0b0790740b012103051400b2070714404c840a0b4001c80c00d120000605500c0000c20041c004400c1d6076003800e090042d070300d07040c07250080c098040380319407030b40c50100205034008407030140080e08500500091114143c0703203051050086c640c91203000c091000342c0c06a101d04202441c10001850400e04c4050300c0c5c50103070161301070f0781c804000321031010461031b0810800300c01c01e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33098530 1250 33097280 33097301
    0x309190807031202090a090f0b03011803031506050a1b17090909060603060403120603020603070302030f0702010b011d06040b0c030703080108121206010e100216060309051b060408010c0201 83
    0x400f842c0c44618406031003644501522160464051402004940b81550100e000005e501c00046840d14000001909445240a18510401c48071040d20200b41c4c261080b03200b038860040c8417800051038208068902c1c041c02d04107205100301c1403a140c400100e03082603190140d500103007030070306c442c6051301c003400070f4200c904c44030700604480c400320b800712400041c0e442c8900c130b00400030021640c85d55422515000c001d04142d400685940020006070340e940c02551040c1c810f80d4006880e40303050700d10204081c8001d40640c095924000d140310391640e100100f58408080e0501000b6421001004a1020301c00c991000a0307041022480000c4144080018480103000b55524a0142d882e030b48029101c4510520070407188004010743c28001d884181d281d58040014103021078030a06000100d62101585592000180c1014074017000108200242c00098001454100180d8071160340c1c0c5a5a060109180158222000e030806c4455a60b10102e40281000100901040f03000c442c0c0039003c1c0c0740c4180c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33099780 1250 33098530 33098537
    0xc010e061005061206010c0c090c05090406060c02030604120509031905010c090e13030302040503030c010905011a090c030c04030c1509050d080d0b010e03190c08030307080a02030919080703 83
    0x5030741c1c507200b001c4e00c4034060386103020051074032240c0054501d4403039418100c0c1c00803914880050448080d20621500c0b480c40d403103050703481210f01c04020480d405500180240041c00b640e40c0050703140014107642c485c2d03100310005c1400110203c1654540a0384910690511512002e2101d0307000025100450034401c80c0240840c140e00042a640044280121000c100e001c0000034411038400c07d5030725401e406803e00600e01911240031030f040d80e000110040342a9110312400b010003e091040b2009140c24920714080854014001080d4010282c002d401c80200400412903481226040ba0019640f091071400700c0d60b641d0540b04c0c03000403004a024040b842807200090542008c1702c4211120398440a25442d061458401000610b000780000c2d04002c1c0c821640b0714162070402420307200046440c40440c5a003085c0c0f85c2101600309030b0704522042e41061085c007503d680c11030400c0d600412140b5026880f41e41e2086501c4c6480f4110b405410018102a000002d02c0444002086d600d030003540c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 33101030 1250 33099780 33099811
    0x5041104080607050405130b01030b1e030f010605011704111807080c041802071505010f05030123010e0403020c0a032109150c020f060d05010618031e080c010e06 71
    0x1c3c161464003403445019007018201d0001d0b100d03101c0a0740840910303a0141000500c20041030007041039441c84080d130054100d02c1d10154016072404100341903c02202d40000d00000c0e013080e00003001c51081e4025841005a42c0e00030a08004a8826540c1820380c0a080c3c40344030300c00d144503880030340000d40740a004a1240004607071484007000842c1c003038030040900051030401824280e00254080320041e204914034a0460f03940100301c0c0141e134000d02907642c02c0c00c603481c1010101402c4600c140c0d0035030f0b0340c1d180c040301156050400c1038800341162400440e444ca07a5a881c10f099003055141c103186a480414000d010081086500300b20325840d81c8114613803c9030403641c0c0b094669a126001706c003102a0441034132421a8480da45100c038543c0301601c1c001d01001c803100482c28a4102001c125125074441006000c410381c003001d2030b506a03502c1c2540b48a001d285807035051090800007c074801e00380c812641401402980000c40c0d003980d403288000c000c1600c140e06040e0700c5100c1a11403258046541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 33102280 1250 33101030 33101041
    0x302071a131205121503070e01050a03060c02101401030c080604200a03020406120201020606091b03040609020607030804110d110f0301090b070206010e060901140405090304050411040806 82
    0x159001846400303000d06880d0000300d035403105408000081c0d0382400b0000d00700190404407401a4038680a000340d03600c84440c42d545c0c00101030901103140c21000c1c500482000400890341c0c1c1c0e2a0310b004480e001640042c0d00070901e0000c03401c192281900001540c1418407840300381100034000e5040740d02401c1e0b810b10f020b4070b503403a0507245d0109807000762100b47d442c0201500010240381c00010328030020402c00d00955203601103415184240e00210704948110700c14029135806200d881c0d44401e003142c03a0082c0780b0304a60a8103418810320300000c42084080006010494107a01103030304a500104183d88415103440c0041c80710b030003128211440440440c4d07444141c2064150581000c0e030160008408a108105005e1141e24400b0203590542d21006103c0110340e04480f030728001e00182d8041d02180d0304220b01c1005410003e08614040c043e01c00041005200000440c41c059030112000325454035192607541c0b55026981000e50312516145805c6000528030380140300b21003284040d2038a0740d849 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 33103530 1250 33102280 33102323
    0x306060509090d0e1f0203070501060803030402031507020a0206030c03090c0402090a05041e090305130501021204030308060d12020a030806041419021306030903110a050c0103090203030f0703030207 87
    0x140c403506155845140c000342114050fa5001045030720217403100d4145040c2d80240c10000c0144401907025030000500e10040c008280220405068000003c40c5035040c15400704e540e54040340343c44902c0da10440b000c0b4060902c240202c62019400502c0140c03a03003840d41e010485a4801d0310460910701c0341c8030051541d410240260381001500800980025150500f880003030050050388406081d020110300c224581c81344900400c0d24001c0e0344554484010b90b01064544c106508424190351081099a400081c0c4c00c0c1101d040e00d500d0b103800d500742d03150f030408148010860740c8010011076036060350003107942d40042d900b08030b1400b90751610303540d031101c2d01840300311501c0d5503400400589000003e8152955561031807201d06011100601d800045608512170b0015600040700190f2035209200526921040c07040b01c00b0044406001c10b0485682c546a0741c806140616042c542c0b02e11042041d5170701403055a00504030340480316560390452800030002c1d80107074004c440042d106421403e14845 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 33104780 1250 33103530 33103549
    0x4080f010501061202131205030910050309121b07080f011107050307080901020f0d0f0801060809060a0b011103070804030303060b07082208010e0706080a0b06180105040e010b030103060605 83
    0x2010b80391900c000f012034424130301039031145440b82032803150108001601210201c400c11154098005151100120820000d03014031040051082040034410700405c1c000100382c0e0076800e240c01c0d0199948050802e6180d910703a2000c076285280303000e1304100007a41803004c9000716615244c0c5008102104031000b40940038040c010024201e9030040c4600340008041c80014903882505004981c0140c060110807131034140744035142c00009810080b14060130760444040ba001d0841810b11a007189081c07103005550f1840208880f0070207860b0048103a059006031341e1600c41e0880541940ea0f10401ca0420741003962203440101c0000386083c000080140c1d1940954511710b51200c1441e00d84035400c250200000300541182401400203080050745100921683e100c2001400203001018070b002006049228002e00c3d50030203a044c81d4a001030b5680d00030880c1c990b01c0503926003071030304000c0b030300104c0f9a0301664000039811400c1030004192560a4809181200d01c81c803001d1045503205e10501c0803421 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 33106030 1250 33104780 33104789
    0x2040803040308030a110310060f0807020604030f05090414090709110703050a180e04020424050603130606060c050f010605010807030506030c22051b0318070b030c04080f010501 78
    0x80040c070082c400141d1900003140c00c07861222000c1307080109105080350b583d2040d103850401307001e403080070021182c001036121002003c1c1d052001a42c038003800080e403581001040181041207212051204c6c0740150151401038030080c0081041d18840c04194260780400d5600400074410140c00269400640c040c060b140c004540c0003504020031a50103803440d410280b031000c240814030040d030641503100c000400051055800e480403a04103401400212040f070845032440328842446108422030412030581207501c1030340d03110f682c6d580e9640c03000c81c10040240020f1009042c600002006988071620407030b4030380110152405864091b00841c221046441061302040c490000182c03528040c0d1312540d030022003d02501d900e00382040021384080343d424143d080004040640c54500d054601c515a03114a054103450200503a0501c031280d180001005020340102007100310241c08030510030311000301b140c40d2449440382000000d001903a0461b000e2013416101d00440300b03640380414000c160488 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 33107280 1250 33106030 33106033
    0x30218010815090102040b0d05190b060301170307050f0f06010618050405060607020301050a0c09050303070203101e050103080706111306030b0d0b01090515010c120305040609050a150c0201020408 86
    0x4402c1074511100b44008280307640d15503080c000005c407001c481c0014205680400c0001616240c00d10005c10300040014014860b01e2400701c0d4161141c56010489042d248504130301310080c51010034482c030303501c02c0c43c070b00901d1030284d80c0344883d040304001594800c0c0035440d8151600e50384c0b5004211804007400c91000c580e8030300b5070020003040c10036501c401d0304100041c02280c0f0f03054642e0046800c0d137800b034550348040b507036815a255200f83c1c80030558010303000460245150002a400080e520b405030303512070814950b80c0610070340055086040c281c0846510300240241d60b03580c107112640e80c0000b8000da070f1fa141048650480c00500720204c510210070205101602401c1038000c0b8020883c5541464200c41d0354241400420410f240b154001c19400c000882c0c607207440c86a003011901c00c1c415103414440301c100444001404141640700c0d50025240010b1550f540c0e040c5800070f01204070020f0514010460f200080c0301d800f207680c8101d129030f40014003400300b075034204900302d21480c031449034113 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 33108530 1250 33107280 33107293
    0x118050a020405190e070e01090603021e0f0307030b09010c03020403020d03080702070801020414040c0503060d03110a020d1203060e0601050d1a0a080703060b01020c0906090a060314070302180108 86
    0x14601030307221030f420013600c10001c5040002c2481d00c0e421a41c0d080e50225880c1d0001004201c01c0c050052482e026129209049c041c040c9194082120f40080103800500340c0b0345142c0001c0d041c0ca0717800b4503942d0141e0007400c0b40c3c195683c0e418a00700200e8280c98aa403a54240202c0c405150b001c0e00885084907030140c0b9070040006c01e61002c4a1459000d001c2c00d0446c014000c0001d0400e13824006080a490040361700200303412208100700c204c80c1e0720302c0b450703084c841d0074020807900369140f070070740702200340c0500f011222860052078060520940940086d4030076807504440d4140a00c01c0070441e408185034604000b11900c4064078042000704590250000340104001484110f00350050080d0b86401503003050030a003044c0019442041c16040698607a2210008206001660040e421086001c0c000b034814002030038085107925500a22240c02441080d001c01c0c12811250b100000864001500e4240000d0090960362641e825210581c482e442d80120060540700d01c0503254121020395006001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 33109780 1250 33108530 33108533
    0x8040b0a0c020a06051e01091505100203130b0405120c03100216020a03050c1f0801031202190819020f0307031b0b040303020712020606010e010815041a030118050a 72
    0x24021480482045000f030b00120300010f401e80c041c0900a241c1d800c2e94101c50382c008441c0c0240c0ca00140d118402c05801c040324421244904446d01c02600d070140c07034400e40c050300c8010036403551240400700c03252004508000a00c00d03584101500c140c5101f182c1ca21013080fa6011440d80e918001075100e40e0640001310031404804082d030003020040e45103903042ca03540c4000c4c2c001420708205036200740d8a540080b40c04481e24035004110005810309800111140318000d480280404c40500006051064540a82c84814000c00214010026001d0080140000c524240a080c0c12101a01d00e803020f00c0000384c0d860500115012a04840c0840114140b00b070644080b40c8a0802205064401c0248100e075404130f05030a44044c803070390190700c0c05642c800b50b5180007140c042d40d56603d8011900040c050000603a801003880a1240c402d10b01318145456100500d1749001c0d100d003002d54040d2070b1100f00c0008c00040c011440c500101100200310301c1e03c00101c3da00c000411004010584e8110340344d07000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 33111030 1250 33109780 33109801
    0xd0804030b01030506060111030711090709030c0308071101090e04150603060513020a06110a0219050303041508060103050103080a11030904020a020109021e09010e0702070e070c021002190308090f0d090806060108040b 95
    0x95002637146004105547d9a071101c0030880220b810030396064000041032828400d090300000c190300028030b80549a1403400008a13102d110141009141b01360885140c1010482030300104080c3d50000010451030400516689001d0381c0400128000c03088500c0004105000d0359181800081160280c1440911759080246410440020f0340d804088007002240315101040640050800c65002c0c00949140180c0a0030810300100103604150030403005100141c2008181c2d19207075020b0914100c400417140865040d8016020b5158201d4408034413603d47c1a41500861160740c0242c0c2e09036644171586020340c1e01807010b042100d07000034100004202d19605c0c400300550014091041d80d4480d900c91203102c45201c1c0a8130308034002001d41c0f80e240c05610300315441c0700c0c0300d20950004004810504580e60a15134003840d0140600c06813400280e8441e1081c401c40700071001c000162144030b008540d02500210b201d0007103405c07601c1503500182465000340b032680d00584e0441c40f60010380c3d031400e2521 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 33112280 1250 33111030 33111049
    0x603030418050c1902060a060503030a090603021303050d2c01020307080a02031c06090f05091e0c030d03020307020601060201050705090d11040501090509100b0603060d0804030b01030506060111030711 88
    0x78804001d0410071403081c01110744d903040c0348802a501600403410030142d4203007640e81c150485842908100b00c6000b401c0c2c0c1003540c48046482c00d050161f22000e280c0c00542d00c2c8440c1d64005003d034007810000c0300c100d55000c50601c012000c1e0060030043c0324000506003070307403600409000340540c1c01000700700003241e100005041c0c2c10174140b044928007400c0558141f00018404007100c1c00700c4e215001800080000d000d030008560314443c04004500e80444602c0ea9a1140994969038884110380700350044c0c414011238511600103030446041c01c00fa00d000400035401101c0d000014060100041a56031040c01141c0c00340a4550b0340030f04004680741041545006120100c80382d40580c5a0303441c0d20f413960301845000f4005088001404cbc5018411541024400b85882180c18500440000c143d0b03590002c0c0d9805c02c1d02038810603c5ca02c090b250030030390b520580d007000d000c000306000000304000c00000d4242c0304203400e07030710b003c110500b11000b155a402070710002010300c18240d2500b101c904116010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 33113530 1250 33112280 33112291
    0xc110601060c0215040f090c021b01030209030a060615020105070801080309090a020d051305010501050a0f03120203090d05060604060b21070909020a0809070e01030c060503040f140d08060303041805 87
    0x21381619a001d400f204100d80c03260b800800e070180d40713080400483d00c00c0e05c01c8080030581400034000003004001c41242082d150001d40b41030560220b040c101580b010081d00040c3d95000b80e04000f120f0300c40720114407050043c0c42441c0158201170000b03030b106205404d190704950035000203504194071101080f07040c0030010a00d00c4210381c03d2103080050f0460b402964024103d0b0b007401511100141417050950780705811903400b8a550f40010400d5010841c480400c80345c00c215681400d07001a04203c1c11403140040c119840581c2c4009402405004211070f030082404a80810590766a980340e2003ca020740901000c0410940b15454401c060302810a0780c06402460901249078a901d252002c0ba080214007200240b205000c01c604c0e01010807003500030380510790305245990324560b500452070700c10340908410800702102003000c01c081040310300340941c0c1c061509a0b400224102d0540e4400324071191200080304440456080d040201c2114240d4440e00f241d604000104800c50b409003101905 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 33114780 1250 33113530 33113539
    0x30b0933060d050f04050f010507050a030e01062c060f090a050601020c15040608010902090d17131203020105070c081b0307080c06061002070e0703090f0b01030c050102010c110601060c02 82
    0x2c0c6401c00b83d02c241446a136080d5659001c50030325080c518902140c0d01580420b0368035103803d100070190040e060b259007025031700e808554040071381e41c16405491550710198600d41c540c510030035250004811040903601c01c410b4104039a5801040200040703070030319003540250591001c04c248644039048141d2002060040390710214641010601140c4116076096103000f001c1014066140d0104466005014084042d81848d54039400240c0c500e0b1074100003044403000d10fa030412520f051009503005941200b5403004d500799942031030121000e14003001c0b0019403030000000c80380303802080154405c54018003460b081000c40c040032a440c4207003000714050752205001110002c5c903040020068003070000081c080d00d051450600c00111009501c60080d9000035000f030181c1c039600803009a00c08031503c1c000c1101c4006041078002001c520720040c0590303505800220034040b404558900b00e860a0b03008112455103034402f11400c02c1083d2039114541c018500410516204601900c4c05034002030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 33116030 1250 33114780 33114787
    0x10204031502220303030b1c050d08100b040f03021302120103060c110307050304030203060106110a060b0607050a0302060105150903030319110712180605121f06030b093306 76
    0xf800310942c42d583c0d00880000741c4407403104600d13003012110702c8030513801494103086800f070a5407416100c0b00b1503030440040110325000140c4034080d40d450000100829001d440c0c2d41c80e2580580320000400303000aa0181c4840e090409138203005100712108940b42880b42c81281e405c6070395080107800ca40b613103081084031004c0219540320040c40140000c4c0c1c80741000b15a25803031417041c5414484141d1040303081c070009030742601000001180c8805015031000c000240c01411000080c270b24000d411000d8250700c518000306040540000344181a6a0304580e0742c06000480c900c036603110301c603c8986c0ca030141c000b800400c04c00108461421410f05c407000000c078040c034680700b010100f604880c1e4180d41620118444907915604801454108030510300000030140c200b050141c1148100404001c403d0070400000320a050401c0f6130b511407002c00c080c5880720300d6a440000f009044420312540c4640502c01c0403400403130340c81610b9040345041c0809402c3c00c10021448a01010f030503072110340c002c80c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 33117280 1250 33116030 33116077
    0xa0f1110090605070908030d02031f092c0a02040b18330d02100e040c09060206060d0c05010503130b04030906020c030c0109051507080c0102030117010204031502 71
    0x380090100030315090030004048000303040010540d400548200103104010000340806070001c0110380000000410169494680f03c001012158145e40300b9544d2080980000c50712880f250800907821050b041d9a401d4140d0401030800100203a00c5c2118940d07228082500050070640c20185440c03900500880115052150604201204642c030045060100c0c24408605072000c0c038140b042d08080b07040e003a03080c00c6840421728506601801a10450344d0340101c4103040c2c42031a0000c40303400060b00901c0002e041c1c00e00980102072500031000980034a000150080c2840c40d80c805001e50071044900210345004015165680f005d0030307440040b0301e00c26141010602910105004601c40d6590b800700130303e092002828041002c050f10b119402052001c181603a1002c051400c1c0c4900325503101c4051028944c031000340c410000c0050402c2000b1804804071103040d0301550488220300200788800c4881d0540034202d03c182e01004102d07081100c3c0060419180f5405064030868071402000b600056 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 33118530 1250 33117280 33117283
    0x5070504050a0209120703020105070605040204180308100501081618080a0516051f0807120e0d0e03060103050303070c0602041e0303110304060504050d0204090b13061a03030a0f11 79
    0x1101c40d1482c09400191119483c2410900c00d19024076800180c03c0960455000070010300c1055000340900d916040031406542d11035004801003a58201c441c242782c001da18019002080444400646030080140010294003d44501d40f041410b15004a0f8080f01084161181c0009940e0502d82e28180c0308041070109007001001c8005015a0080a00045a00150034004442d03000140146c03804c04501c403d441101c0c0406091000300c1c02c0103107080c2c1d102c11080f103114150501e42e415040c201109a09202000300d8a0700801003180d80e07124401001c80103055480800703200040450b130040000410b8280f15181c0400c3c00c620480016191907690003410301265043e0005003450488a04104200340c0c00c03040e05d005c082500d038061820940362a40c0075109004510402d40070705801c0000b00119a6994003a80303000d584152001840d00305036420408613407410408403440c62500c0da4402162151704500c0f040c0b000028002d600d4031302016411140c08030100100ca00f800301d42da41c00450400b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 33119780 1250 33118530 33118541
    0x9130218061b0c120a11191202090f040b01031b09060b1215060d0f020706020c031801020106030209011401090f06050c070e06010f1407050a0305091f051605070504 72
    0x425072044041e1201544030070308181041e843d80d84113a0306035810700040800401d0304202550802a85814683c02102290321400b003140361031500000c00d01c000c90700909101c603400100b4025241000d040d5910f16003c681108240d501504200010004000045e010320002c41488102003e0841d240e50b5240b05e41d0640e04542c00c4610008408034600306c800785c0d2800d00c1d81c0c0c0000d010f008886c800c000d041c04200350384604290300d170b139003070302c8062480c0c1d1002c5030340498042e5688101c2c01c6503245400d81505445c0d8101e030f2184001005030b4040010598414002e0b002a030703400404074009039103001c0c82c0c110301205003050346040c46109400000c5031140301307000400814031901d64594606510440c3d03414481160884891040c0a0080c8107060740d0114141c0f003002d080341400f0070700d00c90717603080004c03203001d40380c0000d0040c414802d00108051340b10001c1c0ca0081c20540b8481402181c0504c40801c1c000f000c4d00c0c0c200015010712240304046000c401491000b0f02450540d4400c0746c466002c10240ca6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 33121030 1250 33119780 33119797
    0x70203120d0506030606060a03181403090a06030605031009140a11031002030c0f07020117010b1b0a0302100c0504050a0f0f0609080604020d0201110a0c03050c060913021806 76
    0x9002040300d8072145500d00480d42c2c0600b0840250445280c8040007684a005d529403e2080681c3e400c00c00c50b0b0710b00400c0955031000e406c070305c020101503040c41003a9030300d030f200e00c0d0440c0c001c9000c200c0002c2c100f40070307000e01d4003990340007000791a83c01c0d503400c0003c0c01030080b484140c961f01c0c10401181c4407800c092103d2034101c1c0c000c000b1007007460100c40031b02d0b1914800c0120301c1c21261042081004100004043d02d65450b050024581c0e1280302f4001251140340c0781d89280c1d50301b0000c00000940400c100001d20345a00012150320220280e285150348034024030b100600582c20109001e00700314a0b6070301460644a1600f04a410030362644081801d00341d0780c1c0c004005040d0100c0b0240801c46a00d10008020600c2e4a0022421800c2a401d55150a00500001d00449054000004580c081c0800345c0f55420204201c0c0c60701003882c1021f4031046001d200c1541c1501540d10885100d08040301111180c090150881401006134000b0b58000d50000c070340444114407116041c559aa9048010150b20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 33122280 1250 33121030 33121063
    0x150e040212150a06020309030705090405150c130504060311040c03020d110301081506010f050c100203090c180112080906040305030c03030f0a05070e040c030f0c11100501050906100203070203 84
    0x182818428448440b0f80d90300030005550051010382800c0e540040d164050380c1007915032030001e440368503000c1d181500303d560803544214410700700040a50241c01500c00d00720302100f00100f0590300c4081c0030483c1d005000c00361140c440002d010201e41841e402c0890703031060341d140c0180340c002c0390f0400e48215a105030004203440d00010040003000c0702007001c0c480d14001101c140d081410010006480d01007401010014400045024282108103010516088a1000301590740785070501c1181d03140e42d0b24a4145200710300401d105c51040103800c03101c80c143e17406041d0000e80804951a18206a0000d41d4241e50014003004040002002840640100145900156100d0800c0c541181c954000100381c41d60107072500041112103540000442c00300c900c103881c0000c0340740e0042d10880160100000401c2620f0905010400b000d910000844c0c3c2c078031034402991480d2104250344410b8450038868503910418150120380c031450140c032046c0484c10076004680c070b000c1c0142d0110b402c00c0400c034201d4100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 33123530 1250 33122280 33122311
    0x90f13090203010609020f0702130b0d0609020315070f050c190f0308091209060c0102070b0702030a03060603140c0f040e010609030209090a050d03020c0708030409020c01060f150e040212 82
    0x210300b07090045101a0910107070960420005c1900054180103c00010340b043e00e0f020801d504000440d800602070000290400b0a2440d0340d0030290081c01100c00202d0003889005100031540c41e211202e20700410709690f0306180c02141541c11203d036008540e030100c182c055040400d50f2044248a2244082c4c42204041b03c0c6c1901d505002d08548001440c3c05030b690000e0a807400c440d04c0f03000444001000807520b075900c030380c0541030090090180c4040100000103140c24401c0c00c0d13800102402005080e0358091082135241d030707821010380b801c050b000d40c42c16420701d012138000b0100c036002e0458030f10362400d110b04256450080305041402039001d503003c03480f0b10800f4029410036011059000c02800c00810540c1400d507546940d81c01e41f40031802c10940e01044a46c3c80403010710078540100075480c101c82c1c41d6510742c0d07107400095002000e503000540c602540003030702c072031490f80e404100e8815000f40d840c3c1c85120502039a100f0182e0a0066010382d0030400a00c26498640c41c05003d150099010170b031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 33124780 1250 33123530 33123533
    0xf0e090a06060e03030c030304060f0b040c0206010503100e0a120203250203070b03060105031305070b04080f10050f0c03090c04090303091103011104030f0c05060712020c0603010f0902090f1309 85
    0x800c01501c2e0107030301704002e400001e850000469400c954442c5000031048102d444040050582103003059015007450306841c00171380c6c00038600d81640c000710281c0b0b1040b0398030048402250f0700d160013448260001c08e44c1d000810a147d200340412091401030b41d00d8145645440030f040c04e05500c05c100760540c004080410f40c20b0801085000d02002000c007451030030101c1c006880c6000081c980e1074401504442c0c00100903003809920001c3c1580c07111a0780b076540b18200ea98480010b01d0f0030200d184501c0b1001c500140f014011a0300620340d134040c9200c5902c40008000341f5038402480070300640f052040515850b106c40c49078060b014003a40d00000c10ba000703442e00250030034070000d0085c0300c0d83c104040600700a50f40c0040f1760440f94810210002d4800518008103285010780c0041e0341f01c41c0200f00311081c0207401c225609500959425100240602002c200041c00700703028001c0301c122000741c1804036514650040005006c000c00a4468050620018030301d04403d401c2c07441c1c01c1c1d807546400750 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 33126030 1250 33124780 33124787
    0x4060e031201140d080904020c010905010f021b07050f09040302070f060c021207060e0f0a03020907030e0d0c03170901180c06030e0c0f060f04030b100e0603160302010f0e090a0606 79
    0xb0f0345407104981c24012003040380c481811a00030140141e1090b58001007291340b0035807d6015000703581c0e2241c001d00c1580041c55075400207400c031001042040f41504170005848c14040703000c606642c030062450700f00d1800c1c0c80610410000042c421015441541c1000c105840580c03076081c01400f2643d40c90180c6403003803042c40b042a6122074803558607482030f84103105041c0c1010003085880c1003a00c8158103107800300001407456149038000ba41041c0c1a6041c4031101e41d0682103807602c540e0141c1200c5007240c5542049900c0c0c00080c60280000e0500c600d007c5900750480c1109410141900010880341200c01410020a4960000f101c801e0001c01c0b041040e2a018000d0313400c03415510000d02240510070022603005606071104500c1000000f40085e104400d0205072009541c10241228442c030704070b0340a44420015000b844020098040064071624001074023070348c81c1c10069010b102d40c0d4590f82c01580d400610400f900e082c0251101d01244076203c0603c46032050a004031b01042c0d26182c4580503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33127280 1250 33126030 33126059
    0xf07080f04081e03130b0f0f0c0102030411030d050906070c05031509010b0109060e0907110708010204080c0604140d08041815120201020601060e03120706090b18100504060e031201 79
    0xc0000b03410034480845c4001284822004440441840f0b41d5581d00206030b01c6a1172148046130507628030041824403001405501452045104002d4001d124501d0000c0544c2d60745401d1003440003540400c030100da503043c55409446101c1c441c540400c00c03a6102c2000138106003246602c02840d403203400401011100900850705844428205002c1301c5061100081101485603200c80c001d0802c807000c034001a110304003d40c0ca02c3c6008082d07604890b100c0c452a800f0390f0081c8150040c5106026094103e498039008440480303601e660403400708a000010f0141074002103070142ca8020051100040360840d10180e0642d081c0820780004008072031040340318400040350070914a20105440b41030040c0d0f000192035041d2449420192000d14181307001038034105c42000c0c580414800415070f1010054550003414100340308001d100320750b82d44d076000c6107410120041020043c2d40b10b01b001d5110b244055001e00c1d0498003030280414617501a40c2441e24607403111440c0c00d0f542040e40010440fa06610208 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 33128530 1250 33127280 33127333
    0xd030f09060e0307150506030a060b0d0c080a120302030105010804241505030712020f06180a03200103050c040b0a0504030206030103050d02060c0a020a02010e12010912020c040207080f07080f0408 86
    0xc100785e047c440b020070b030b41c0c5080c660000d207400c0c0d890784165450303a100390b01c0340391a55201e10444801a1507a40303807500c4418048044400324444024810094000c0c0245c038107079001a5128810b41e0345030703111201c010300c2d007801c510035502071003101a420b10101d004012001960000e90001c0c103140000345890840e03a90302031810110781c2c80001e401603868241c1000109004c984107038950f0084d5038110f070800c80302e0b80847d9025040307030000001c024500c64034030814459070710008044a48900150140c500440340c055682d20100000e00410386040040c2903502d109190090402da165030114469034802e800540340740e400002c00341c1e2501c0d4100f01d55940321412410b62428102c0e6000d0281d903a5600c494028144590200d8042440e182c000d03c168011503100001d01c00180311b41403032100c811091520500501a1801c0c0d150141401e000320380966900c5424181b0317201110b81940c100741c0104c0340031200c0003801c02c9080441440384001d04003800640780649003640054000203c41080e0581 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 33129780 1250 33128530 33128573
    0x105010e04050103081204021c03021b040905070510030b13060e01081204150e06031603050601020a0305040306050a020408030a02010213060915030c050c010606110d08090d030f09060e0307 83
    0x10300000d41c40381c5c2580c16002e9299000030344c0c4d84940c0700007969490810304000c1c0c8030f4020312402e4141a8000b42c0b4241156680c13030840c00248510051000fa110032000141c02d42d4803603042044241880310700011858490300d800100510700380c0004240045205002c020951940401d0040078015861140188420001014810302c0e12118030301e24055480b45000b41d00140030700d001e6440c0646011814100020320590752071819a17510a149a0f0308140c1c000041d1403d40018a42e50000900400080d0562174003420645036565000181c44010005150107400f4000003d9210040001e482c1c039039025000940c68031881b100350301d010388181d40700500708030805008002201101491082c161035518000c99082104803090f1098132840c0603502c01986040ca0004035554450320400e50442c05800307550410a42c2d04013280c0064098440c1046904820500010103000f40d11454442c50130341c0001c150300410f512480d08984a5684400e91500000b4890080121850120954a001c510f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 33131030 1250 33129780 33129791
    0x20c15090a170d050a030b090703150803161401090206040303020601080c04020403020a0e0405010917040305011103040c05120a0f0303050a050702070305030301061d060403030302070212030c2e050a050105010e04 93
    0x10b90740d80d20385249200600100295030481903100c0d41001d4400c207405400c101c0c040c1480070000300240154207507103407100040c0c41d002c00d117402c0c04401c803100c440006111840100d4603499030041541c000103000c0c0f656680c2c17801840140c407810040d00040d0700070f40107803c0b658580800c19003802403000c0d0141c4910b204010600c0140d03202c00384001aa0404c880f1000140e84500e407040c01000f404902174040400c9103000116840481c0040c01500d200f04000c0c4404110404008520701065400600c118151a000d20042c20914603404d22842c1240460302e0340b1499869000140c4e6402000f0f800091300c0700c0400220b46121b0040c40c1e002a450310042c00c5c100d20310b403245c50722404103010b090200015005c01c403200e8412807803600b8000d540107050b44c1d5501c0e0341e8a4050025486900108d00803860041c806024500210503113020b4910b41001d007000011010450040003c042c0039000d140e8000380f11a0001503140c0701e11803240104820008540d418400054441d10440000c244a9070408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 33132280 1250 33131030 33131069
    0x8010b0105030f27010b18040f1101020a0b130303050601020a0c03060506060c010e0106050a0506030f01090b011106070216080d02071203200709140702060f040201020c15090a 77
    0x4036580100070800c603a960b61a0640e1134003c4101c04030741400b105600d0300d0030000c001c1040d800741840c007008980d040c0d9a08000101420b000310116000342242c0c2c0400c101c90003250706001028042071051043c0d4201d401c2d40c0da00e80010603c26251380910030840ba80701c20806405103d9590005402d000401d03800605540d01134003003115000090842c1d80f164003052142c0c513090b060f210129185c000901c01d080780c0e501040d008001c03038440c00344a02c2e45444005068103201040368004ea00300c18045509038245500c20001c3c00221240504100300003002906c0140b05029650080c3d40a03400381205140c0400d0382c0c20300700c4d00c5800520301900101110887d807600040d03203400701c444400541918102c00c1c2010fa48440b0303802605103906030382c1c0000032a1420040762074015140d06540400a69203101002c080c0054112258409039004601180b018010711210690051051044078013009007803000c6450001000da1802c1e02035401309a880031480d12411080141042c580746420340003c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 33133530 1250 33132280 33132287
    0x40203060c1204151e0e0601090b01140a050702060313063b0f0102191e0801060c02040e030c1b0f150d090813030302150906010611100c020d0908010b01 67
    0x83c00081c4440d1100602200c0701c14a5000724040e0202c801d10240c0036502c0301e00c650043c20518040b14142d0050074004500f4600700d210340301031000103a440b0205101d030f204401d6410f9000d00c4050040c441c0900c00d110050307442d800118400d07912000412401c00c00d9192550544481e02d02e188480585031150880700c0040401041e06003039503904d000003207002e10030550706001010014030b0282d40002070041c5400403800903a20102c400f41d59944090301c6600c0a0251075910603042400100040010441d081c8600ca050f04001c1c0001c000284103268444154a1903008071004030890b001000c84840c090010b100085851030103442e44181680d4500c0014005400c0450010a0303d80120303801040021550091510640c07110002c0c1d074401d00c0e0803115002054500c0201e0061107501a01c1c0c1e21450040b0070103024040c02070081c001642040340603280c1d010320480c005164852040c608800252601820f100020b10f0707005407415042d0303010014400318081d00b10000d82d070304001c400302441e60b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 33134780 1250 33133530 33133567
    0x1031a040f02040306020a0c0b13080409020903030c0f0d090509040b06120f01020406090f0b070c0e0a0b031006030b0603160b070c0518010501020105071106040215070b040b040203060c 81
    0x200e0300024074690400c9054000d024603040a00214800b14100b80000d802014041ca183d0091003083c50690b43d01c0d03040aa00c81b12058000c044240c00c1c8010003401c681500603154041c8000c5c181c0341000004400e1901d0708840007140f00d031a6229412061000c1d4001008070090a400c1d52403804a1516843d00c241030180603100c41c1c0900c0c40541d603060306a2051005591340e40b2030394001e40d0b5640e03545d54024210742041c002d15140c50107400c00040d0901d042d10403150826445a0700d499603d01d0072445146000340100b09000c043e0b101d2410384916230b400d00c501c00f41c86d40c036031034001007560450503d0380400c20010502c3d4085c2e880f0803242c840006c200d2040808441280141650342c0d03d152400d411900002d0340419013000184050101d551280013005061320800e0b03000f080b4503580d4010485112403529a1683d40350403103030119004d410b02140841800c0350b0503a0540c5811000e6075030100014041380d0903504056048103003c1189424080542c0240c80d00f20002c2c140045031381c103030f4034048 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 33136030 1250 33134780 33134831
    0x80a031d0c0a050d0501200702010906030207120f0e0409062c0303130204020d0c080906060102030310061407170304051009080d050406060305060a091401150b0d020c0a120e0103 78
    0x54084c140401c842504a44900100308819040060307050f80220915001010b040740070035152040420880d100344255803a941c0c214904070402041100152112240e0a01500401c624190100d01a48840c0a0701000c6441130700005401c403114545031940c034081e0100032050103192540c01031b82c4070000044d02e42002120819100324110791000500074851624a00c1c2c450b82840111818546c121001c00d200c0e0416105031041a90b607400126180c0c88201c4803084814040f403010302c090362040b8a01c50200c2c2d4280100740c03a00c8800e8070780c411101d1071141021000c41d0008204001c10000f80700180c2d108080100512510001f40c0c2c8035002c0340030302c228041050341d0ba00002000d028007900502e0045070808151561414111219809040c0107502610750307641004e02d02960791814400c2c0054090310b07a08089495040c058080b42d541c4c040500b4070603141c2c0a011100444100f8010402424840c1c0445041c2c0940c107070000d088920f91038111814189080484480750b18091a103182c4003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 33137280 1250 33136030 33136039
    0x1103070f050f0405040c09050108070903050d0509040905060901090c0806090706030f0f0509100b0603010b0702010302070201091e05040f020c07140409051e0c0603070c0b070c080a031d0c0a05 84
    0x280405040d40059000d141d100f260f0146c03c1040c003103042c3d500101c070501510420ba84245055490b141c00b034680583c42d110013003059011454070f0a0700303403099020349110038000f0000b00324141e4903220249003000640e035584490b59075940c44001c001c900042c040042040d14058441c91401041e603540340c43c02880b406080c1902e0320301e1010500740b40d510840324500403610070402814260300040d520581c4147c105800e5152403d00f8620b403808000b41da040b030300f0ba603072028a0a81c03035074011006900003240480c10f012555001181104140c0e1254201404010044207120300e01010001610401e21480070350038410890a0190f000109403c004c1c1c80c5c40030750381d40c0303004d0b40400402c0040c8200c0d600500ba60142c543c04900200c00c400e1b58000307407010b43c400c8035a10f0303210a040060511041d1034180c08240c007464850005041140c0260740031855092055042155072503c4465a0100c1201c1000a0388c641c441c02c80590740c01c903004021403464004008221041000c245c40b1003142c011180b24 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 33138530 1250 33137280 33137287
    0x21207030309021503070f090b27060c0d080f0a020316081008070b0306040b120a061a090a09020a210204020c0304050406060c05010b0603070c080715110d1103070f05 73
    0x15921040700f81079035010f2500720580e692606e02c1c0b0040034188900d002c0400a5140360000501300c040c601610f4a00c420103540b08956a40c81003044c42140c1000203840d00b1000a000001070f4000a000000850046868884007032038070400e44002c1e81001032440620034418803d01007000c0701c54012a0300c034801d6082c4000140c40d9402080325202e803030740c8030645c288644240860316201c0403029500401c0300b03440c10b0128414501c02c0007900c0b485074040420b01d601616051340440c40307e80003a40b0901a80c2d180054960b403034801b0802490040303840c8400c41d6107400781c80045003041d440c0d80000b444400b400e10700881d00703041010145000000040c0c401c0c1e030045210583c0c65030610807100203220003841004a141e031004082c100551011701a40d507546440422044d41c1000003c41e4414101c980d5180761030340441d9101c2403260020103047c3c0d040046c00e1001e04031283c00d0311a03900c0c0c044103054116142c14040e02e520f030548683d5032600700c420a0a02c140204990014158013005509003011900d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 33139780 1250 33138530 33138533
    0x80f0a05040f0c0602070302011b03020c13020c161403150604021309060f0e09010203010819080c010f06170708060a05060d0f030305070908010203100302040c020c060c011506021207030309 83
    0x302c9180d80350001d80f010040c0800012810740024090f0100c0e4400e1720b5034045055100d2000600800b503404c003a001d42c00c080204412898118020018075101941c01810030702003651842c40c18050000044040800107002c2c00103030b41c00780d000b50381c0c0300048004000d0401c602c4404105960f0107400107000d19004104400583c0700700042c68080c0900030000c100107541c44e076886c9a5184188100c03e00c0b05000301c0070660b050030600071a8161144c42c0c0080c003030b12a11820007140400504400e9507548002d1003d1196044203004d00300c010741c2c02140128000d800e0001d05454400250007a0f1003550050038200110320b0f0100d9040c1c2d0000b004000020144c0c1c5080c04201e201282c2103008100713064502c480020190554040e80c00790a007070351038441e901c0d05e5080b1103080703200940e0a2079219001036004c200501c0d0030f03002003001002510603a0180039440010610b1500700384a03c54903651525000c94404000904c040000c02140c40100740c9140c4030612410103104a040107020141c8400c000c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 33141030 1250 33139780 33139793
    0xa0c060506060c06040807060c090317070c0e15010f0e03120c0a14010504030e04050603060402040e0f030a09140402030c0d020703020a02060712020106080610060516020a06080f07080f0a0504 84
    0x4007401c03d4001070350350610f09441c160003a5440090116113a9140601a025003840381420400b583e42c8060b0b28002e80c01c64402503505030704034040c00c2710380e0100d0300070100d2078094104042e40100032500b62400b08d5081c1d20005003c0d0106610300404102d90001811b542c2e40c0c0c00a03a203115052404800c55507019005030b19070401c040304002621030b188500035a003441c2015803269105034020b0744c4042e0920a84003c210580300e040c4c5005505600aa0106025103000e0748544ca42d035100e4402c940c444580ce48943c0d04542103261400d010801142007000001c6810111000c03003034048500310320314078190100b4800c5000e80a400310342c2540c0420f8070420180200409410140c0081920f0b4454030286000311848000c00030280040d424004006141c1e000001c0c042c0c000c81b03a2140b0b00c070903035017060700c221000d4008580398491031004c01070030800368550f948040b019080960b9100f03003900c0c0540f0000280803000c0d0400e010018108100b000c0c01230910a86604207107011000309168a4600300740 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 33142280 1250 33141030 33141037
    0x81b0705011103041a070204021c0609050c0304080d330b030903030103030f0908010614040e0109050d03090516090e070b190509030a15020d060b1303021002030c0a050705150a0c06050606 82
    0xb90230510015103000320340740301c403900858512a0b040034044c5680311080201520f0068030064034585051022800042030203010301011101480000750181051854a807500d4520702100b0207407041c2900d060400b030503002860041d0078450000e80c43c509240780005d40e2407005200c050200001030380e52041841c41240b2840043c03416800a22180d40c4514003c00980e403c10784140c455460300d860825459010302509107015004070280580c841d04190a0303021b040740403c121882c0c0254024602c3d107962111110001d0040c41d40001020458040c03043d00c1c00c0d1580d0880200f610050282d000380c0c082c0354a010800c44540d140154a400300040401d04d85500c03040000d00002141000700d41c0c0050030f90140c5081031480b68280801652395100d05c81a1140c03920954041381500818005808e148600001911052040b68600203c1c09111401c01c0c010843c00c58994020080400091a00035a010300c42a0040c0d05030380350895024003c2d06514250038002e01c82038648000440301c1e81d034007069 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 33143530 1250 33142280 33142283
    0xb0105010c0203100608010b040605040506090a020d06081207050106080a08192c0306131a09030702090910050114060703140408010e06041b030c061b081b0705011103041a07 76
    0x2408161303140d1b54464041c00b07000080600951400d1800200c6180500409020700030180c10707040d05032550b00c8003030041d62043c02c2d084074694540000003540d501c20000344d801c601d0210342150b155541c501d00542500c3e132952240c011030740241000ba001c14041c90455000b100300c03000308959144114004d03141c007943c6c03000703010700c51083d03400d050702140380c0040c0329980f1003041b02030319055070710321402406518034a100900101c032240007948100b40c1040354240c000c50002d046034182001680041d8003420201c403042070a400c82d000c84031284046005490140488400640200340e0500c046283c60007113038405000c0004000b4031000a444110448001c0c10807840203200c40d6480c2981d80780c0d2050140e50481d11a04107404c00b02c13011168104a900780c80d40545100b0815181c41d01c00c941e0001c505029802d62070380c0140c404000345d0700e0002441f0018495252040d0000c07601c2005003480100c0d031165041c48501800504007040220440f8152840d03080c0c0c0100302c0311911820f00260140e52030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 33144780 1250 33143530 33143563
    0x5040618050a120c0605030c0702120705041e0506040522170c0706020f070b19030f0f050610021b040903090506040e0108070f060507030c02010507060f020307020f0a0b0105010c0203 80
    0x50200b929070396243c0405440b8051545011459914242280c0c248030031502c0b00003944081c044040145451908030101000d05800c0301c2215485100080403209071405592484106048454403ea41400f5040c0d002104443c100401e10700b40b00c4001c03408405c50501c07112507079113607941c008201c1350314081d049045614000c117071641c4000c00c00b55a64840ea01514001d8465100d075100d44034400030b00030040d9100e9146540c1450b207850220340d1849180c0c0304030814151207210a00b0300c14414454846c0d40e85040c90045000d040c44d07020300c03038510300b04003403c1c045401c51020070710b004544840c00210074409a4001a1203801420110303200b000e507420840c0d01102c001400200340c1030490b02c1c5416507402c01d0039205c000340d6850303000c2d18000262042401190051100c180428041c81c10200180c0c0181859868602d87d079803204201c5001c000011411940030050142c074580c10001d24411075414002844d03c80610303201e510040304144a468100003484460f0011502c0601200300b44400c2c0c01c6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 33146030 1250 33144780 33144799
    0x140a0f06020318010e0c060705030c0f1b01080615030702032115090702060403081503010c03061401030207110609010e030303070f08060105030115030507030209101d060a0504061805 80
    0x36151000c1c0d070050300d2089400320303801150303001c1c0c40062190150140f601001031911400714410720101b40c1103800180c1d41408144040c40d0906800e106103581100f103103020f4580c022409561801164440d94582e040060303140c1048400d4a43e0060804024034194090b42c5942e07400908070310350321840c84200c01213005540e02d24480d4441c120100d0144501c5003486031100c05041c14040705040072169480164000004500070a000345a07094000c018059506800748410000c44e082da042d59185d200002e130388440030451250100c99401d40c4800900e0103501d000a0b940381d0100081400c5030345403080340001500f5070305a0044004000400c405800d0701d483c1c2c81d20150280c010325044145101150150000414035171050003245d068542c070429802156a440c44102c0c0100344c014929000c0c135600b040101140e0780d581118140014059841044c1002c0c800d8041c070000c4080c12001d0b004090a000350200d0315000420344054a0f02c2c0d2038510440105600091103c4005500540c0c00c072800a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 33147280 1250 33146030 33146033
    0x402130e0a0501080c060313020a030f1208060406140402090a030c26011407180f080304180b06070b0a110313060b0306010e06100302070503030a021e09030604140a0f 73
    0x254001403088001c65020401070780c1e1100c0064a802861200c81d83c00031040002940b200c0c003042200500300e0000d0905d8041540b2607540802c0c06107482c2c003d0780c990580e441c0c04101280e1000b0300c02d0740264103450074042c20f440d04000300000300404400303c0c840c6802013407540041d207403c0910401940c0062a0403042c1d40d40344502c1c0e2001e10381c02150107030650b60300c600c8803010744d05010740100c40070740c250084115074a0002c101c0d645c0041c00c184440c074000108000a5159042049102600d484405559941e2070074400d000d010900d4803031410740c9420710403002c40341d03505ca1081e56a55a084001c81515070b45400760a0001c002c1c56401070750072100403040c440440500c2082031030013481010100708007500c4a042640c0c40c0310902c20a0075450741140090050304050b1500712104805007000b504000e5980d4460303055800c21100780c4915540807c00010490090001c040c140d9050004280341901c0c080102c1e4030f40380b005101410020b00c0100001e101c000802c214195075810044d2011544803a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 33148530 1250 33147280 33147299
    0x304030903020a0905010308030105060d1805030406090e01030506010e0c0c0109050105070305070c0f0618060501031a100305030d151502010b090a0b01080103141504080301030b070305060102100902040213 90
    0x181c04243d0149002c07040228889200e8403e45060340e812030b15180c20f5071320b00810804168089007203000d40390780700c0a030340a07408400b02300ca00c1803d10400c003950300c0e542030900050003c0d20700e510050700e03280f0700001040814408640c0b541502c05441c10b454060fa81c100880507644100c0100030300079031a1a54000a110301035110600560040d0b406102c680c0384d0101c00c540586201c400501340f051100020000120254010840c101e11280c003d0006155a26050200c503802da0041d034484503c140105a406240e00d04554804015107110213882e0854036025924041e412031800c04658031400f500e003080c8a1440c903001810604800d203150040d102c002406400c0c1204100d01a5118034040b806074030450091104110041c0d4406003136038078545603a032850001a0004009020b10002515403e050304111803241b4000e1881c1e0380c0c1d80d450751402c900d4428004244200705860030051254603a40460b9080d040400c40307501240c84800f90000400a100c0e01001d041811440c02c4c00240c161031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 33149780 1250 33148530 33148547
    0xa0504030b010509060105162604030b0109020f120c070b01030503090406091811040608060708040b090307120f020115090606090506181201110a030b03010b010e01090b0c0f03030403 80
    0x4a610001c06a0341d03a90140011880c05852880c0420420302040442c41034071003e00022601603000c5989025981315040c40c1c800c0b9039110074202c810001002d0050007500422a401410b07204400c520780300c0d003041e908045000348060b4480e454192000318181c1d1103180241d8240d103801500400e42560341e8074004c0d03500d500c03d80340e880c01107091510002e000d521620818081c41c1c1e41d80407618205e00d10340c0d80e1003180d605072690765074440c0c3d8a000200b500300c010400f140c0300740c1850703c034118541000c0c10500c2c0b007104014140c0301070344c3c0f007042813100003030011200c0b550703204841c2010140300c1d990240690142c44030802d141c1d05074031040c0300001d1808660704910200c46441d04d4002c5110b40b0703602402154400c001c4c0700306417030084c009407000908003240030003090744510f0000145007000b503070240c22a130b02410440300001d450340020415440d082c0301e0b40c07050700000d00b04070030300740c010780300181c05201742e03215841ca0610042030f030310b41c14003003480b501c15511090400da03a52894503140240c8240d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 33151030 1250 33149780 33149783
    0x302030c0a0605030109110c070e06130207080912010b040f0b0f040509120702061603200309030705040c120905060103030908030a050306040906090503030a0b0f030a1709010908030a050403 83
    0x8140314030312609040144007034060340c400b95a01c61441c1e08214122016000400c0d4030402540100002e421411042c0804c01c00741502c169078403c14107120040000a182c08401d0800b10b610403c082000503103603004031071300842d0644400071101d100c0880e241c01005448041d5800504050402c50610000e0b44801c001e40c408480c0408101340000c14881140c00455104440d0b50003203a440d05100001d501034414248003c0c041d5290400703032500350001916400c0e0840200c0c03d110300003202441c28506007800303c0d11000040d410400c0c0c0c0c20007e543ca5000b4411140140c0c0d9030007102d10043e02c2580c1c0d414502000000600020701e4038a8020381d81c0c1c400348025130004008550220f200398011084416000f656512030b41141c40308010000200190481141c0803a40c94515400007a001e102546c464814031800203210b80d21131060181c2d05c041c1c058400d2003600300402400024030862201011080c0c1c800d200c07926400e01c0c07401a034044070150031024061001241554040b03501c000200280d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 33152280 1250 33151030 33151033
    0x3020f0c0604061a0904140313060f0e1c06090204020c0106030f120302070507030b060d06050703091a01080a030302090406090203090a05070815072d02070e010807030201050301031b050301110301030203 89
    0x2079960650a102401c0000d40d0064000c400b04010a811102210240140138152071074050708518262714140c80350b0100d0081074151f10280240c035042080d080032100c003582e9040754900d865444080d643c003041801410250703100c3c1c040d0155240c6505881c81c03000c170b82000700009916030400f4205010040380c1201c160400c20f5940510074440c0c000d0304c1046034010b001b40005411036607807001900e4002c0c80c0e55001700c070800ca00e401042c1180241401902030b07403000280035145040000f5603440034829541000103150040102902c0010380045007034240c82c0c01a00d40d04000c00050140a099210246940c00070007801407503000800d1601c55107200306c2c202c504031a926070015858130800150070031a034410a0000e26028040c02d41e40c00d01c030b001d441d514511200c2701d400c1c1803290181c2c00008001070380b24900a01446624620950140c82c4910042403443d00c1c0d580000c12900c0140401001c2c09145046200c14014540c140800340038010024401d14071000c000105a03002440300364483e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 33153530 1250 33152280 33152291
    0xa0213090b060a0b0306120102070602030f15040c0504091505030f060619030f030809010902030618010e061b0a09030b010303120c0e10030e0c09190501050618010e0103020f0c060406 80
    0x61400d84400360484000182c6136043d0b41d500000c109000c1e100b032815030b0041d5001c000d85000120030344006d6101c0c442840100404e82050305502a242c0e5180300110702a5252142d000c072056000303801e4500711111440b011480f01e44e0902104600c1185600040c1c251040c40640c100c002c9010507030303e10580054400380042d00c1000780700301c01c41c505440090410081c41c0c0790704003c40d12070038819512070494070010550824a0740440d24000003200c003075030890201417120585180030b0042c1001503441c02d0040000e8201203450015100ba11101c82c1242800020740c0a601401155240002d5803c50310000351580c2d641006006020218000080703a40b5080080d00d02c0c0780228002e50180102030200d80ba051010f5001340d0060100d49641280d510800c3c5031803d4035034412217803d1040f009462440c85400d0758007401e209559042e04491310031403051042150680c407510801e242072400b46031401d207900030348006034028801d001941303484074000201c50071042000180c680c095407185000b04038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 33154780 1250 33153530 33153541
    0x160803090f0d080105090c160c140f03070e13080a0207080d0503010b03180c0301180204060602010903080a0c030b09070c0c0803090f04021b0114040501050114061b0a0213090b 77
    0x8852075410006030103e41e43c00014089420000c1c103c40d80011703040861403410456003000003007507080480449500700d480c44140103102500c002200c04042c11359420140300c40c0703800007a890350102c1c0a120205089070b8001003070b0505d84007100000035002010181d031030805120080d00c514240c0070b098810b11079071100c441c0e00c0f4071a03800c4074120350000c40845e095071540240403600a052261030b09803403066100c500943e42d000c2c0b03e900e5190b0000092030380318180380e00c140000e540c03d07030f44000e0035640350034030f00c402003a0001c4542d80e001a079008005011501480700390024110083e80b180c00c007040c9420001f42c2c50300000003030355040c051300080081c51343c1c403d441341e500d01c20043e0341a045a503100400b002c5041c550040e010780003c00c0c949210902d00d105502e400c5801e1103090059240d4094140401e1150a208003809040300880c00d04640102802003402445170580401414000c031035a0500c20074280070700f201c8203a0041840264583c032141d04005403c41c608203507603052281c2c0120f00e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 33156030 1250 33154780 33154783
    0xd060e090601080601140d060e07090b0108010f030b041e05011b02060f010f050103020705030412030504031403030705070f02010c0b07082e09020306031e0303011403030702091605160803090f 84
    0xc5c12540e04145020707601e2070a105024191102d000111802502e903100c041d9401c1d014440c010281c1080100003603900d0004c1c00041c10f4802c182d00901c42c07542c52085c00e1002c142c1503041a944540c01407051000640300010311b0005690070400600194a00b0900c803200205c0719000c16a200e03910f0b401c8601d140c440440301241d40f4820b1140f11307a50080d00303404000550194024150301c40c017520a82e82410b580c4c0401d2150502012811400a040000c0600c00c01915030043e032a010b580e50002c505528003040007915510882d1805840e1400c44180b10003107a128041011a26511041007036060412101c007600d060001c0e1400d5130000d445014004d010b00100c848050b0300707a510036080c0e00451400b14540000c2d80080e00c1646c1500503c80d041040c1c0e00c601e04403005c1034100d0001181e4a6141c248240003182d854000340f48071b900100020400340e5903e000300ba800c4604243c03040d200c198505801d5540d80316200c182d000b00d0440210f16014041c0c4900514441c0a0040030796042c00800d0400c02e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 33157280 1250 33156030 33156043
    0xc040c110a150e0f06040317010605030a0f060314010c0801080a110d030201180c14010e1e010e03100204050906010503060102030d0c020111160501060b031003080f0d060e09060108 79
    0xc44280c0d004100303031004a40390030408625400140000200518222281800c1c8264505102d0041e8080c0c4180410141d00039190244412000740742e14081d41030040c000d14510020300001251078035902415640c00d03080e0700110045611148040032440c9810318107010340506107060003c01c443c80300008000902040d203a01655002d004603075120141c008100d90501800b206900715940e54040c17840c0301210314070a1140310302580000d90f5551a09801400c05060010683d04110b89103c00e00c0a1313840394506907020950310600003031031007891300048401c0c2c014400c071154588105013015045034500d038010302c15a40190348961955030f40c03400560707891006540003030046e80f041086902c1c0c40352a07032180080c40c00e288000300b00540c00802c0e500d1075030402e0b0100398082c40318920b800108002403160f84020001030300c100781507180115400e40d15070b206110182001c00001184201c41c0c102c4c4007100d00ea10740507c0100b0940c1c0c0c9410101001203822210700c00c00748180c02c00410b070302500060382d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 33158530 1250 33157280 33157307
    0x10020304170115030804230a0909110901121a010e0708040317011502010507080c0f090f0a12030801080613021507020a0303050a020c01030905060c0703140a020c040c 73
    0x6518040c80d00c40100d14403800062040602c1d5601c088090015000d003203028004c5000d050619229424a00c0942d5000780d131000280301090414034240b40d03601e5060501080b0b8024800000780e0300d4050820051040000c00c4080e4050024000800c6541c9000341c2220903a010304109101c1d141c2580c00021615420301407202c10404440014a101d8400c0f0401d5500c0ba20a1404000c0b20407035144961030041f00b84c1181c60b83e00000d1a1401d03644d03030b0910480d0307070150b110300d417480441c03c2c02e07050202c207403241d8a010b1701030080006100c519511010841000c00d940134201d000c1550b81d980e042c2c2030311189004100c0001d2100b00001130120310000382c25021b0304981c02008600c22060b400c0046400c94650b103698160400e000402c0940d4600403038030700941c02515030590383c421030320000f4109145034040c181818901441040454400290941e105050800d0207a44040a00f0207450742c00b09a986020825000035008800c15800301c0e007001c4c0e040055400740005084d4020560718100d81d21036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 33159780 1250 33158530 33158533
    0x2208070e060307031b03150c030b09070c021306120602120f1504020a0c060504030309020118060518012106030b0a0905060a0b06090a060c110a030b0a05060301020d021210051002 78
    0xb0310118100c0081c85d480304440320f000000c029a60365429280342640c60034407a51035607030213102c20741c25018090304192040071104082d45180c0580d000d130032a01c82070030280c0034880c0c0d205104000b1807668001005040d0551820707000380c4140ca007800195200c079006c0d800c40c04001010a4609892114040c0100800c01c4d481c81c010f41c40d58140300c000e401c82e51200b402c10070020b007880003042d881d100300c9001d94001d070b4002c5085045030001403c3d180d04000100d912042c5040100f014680c4a81900c0b142041100740b52481c81c090300c0100c0323101214021051805080c098070000e8404185d000000b20b07803143c03040b00480d50301c8d403050604072803070028085c0c03d0340c000340c00090b186c40159001d51600200149181e06244a070004510300103000d811503c0450700c2c241410042c410030542d100340c0d050b8116803030382096056949040f14900040d080e0a14151100c0c049245c5582c290181c4454400c4814119101c034040340844d017800303509403072104040c4624500440d586c10044600441ca402940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 33161030 1250 33159780 33159793
    0xd0e100f0c1218080307081005030705060a050919080a1401060b090d030306030b10090f02070206120717040b010e060406030503030112060905030a02010b01020d090f0e04082208070e0603 82
    0x200300b00090050218071506000706a5400d4001902080295029081641c0e44040c03614151000300340884503034109034440c0d4440c9004220941d2200704035089420b141c588651101009000b04070200080c440d400f00820b4400d002180680c0000b42101b0340c14005d000301302081072580107003402c8581600604ca05030504011070700d5681002d14204110600c28540007401698075200c1100d4401d003076441c24070400040c10100700040305401210804a90404218641070341e55002680c28810000445000c0c0d04003c00120315502680700f2404480b11680032021510301481c0c078003403450090107404184c09103280859405d040620400060345d83c801c1c01185582d00780322240a0180c0908003c4034295111030081001038024405402e240c1c0c0590000701d040c0495400182c10040458040003c10071400c0c4e041003c500742814080484c1c140070180c1545440d1410070406d10b101c1c10f040200607484040540101d01d400c03101c0c142c1200c0c140004e5540890300e4154006108409803404c030340c0340d809103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 33162280 1250 33161030 33161057
    0x110606091e1009060503010212010509100b0d06030c0611060712020c01020c030d1d06040b060105070605040308090d0c0305040b090109050909030306040614010507060f020d0e100f0c 80
    0x40300d045410100c004100241400985600d0591000440e141161003411010400604615001d010301801c0114001d5081201d00f440700310340c0020510400b4400c1540101240c40010000004000b5211003136420f6a03a0a4680303150016085900c012aa1220f0409001445e203115840351401d403024040a0000394075039090490310191202840f90a10340d0030081040c2900d000d1006085e83d425210140d44c0f902c0c2d254004608842102c0400e003018a0a860f0040c1481e00c0400c04582c007e510410040c160b40307800c00104c40c207008200b0000d00c01490039050105140c1c0101d03885110b211950220340034482c928004445808c284400140403400600c0f0038881058170002038040420185010640a561440041c3d0b01c12003c0c1c41000280d00004103003c01802c0074000c0401178980a006000010a94bc000800a00c5810000352480c1c0d82c48002c40b0f100d0b4841e4046840303501e0411403d01c80e85507a65409601e5140f0340905071100751805002c040e880b04680103400c00c440b01501c0310611480314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 33163530 1250 33162280 33162289
    0x90515030906040609020a0b04030b0f0604020307050415051204081902010c050d1a09010e0702120909010501030c030b03010c02030901030b030703020108010501050a0201020f040f08100608030d0e0c0406061707110606 95
    0x5d140100c0e0700450203007010070038200080141000314010003403d825400c1401c101c0500d040c010780458002c42c0100204010240c1007411601100c480c0c058107c2c43c00400e0000b20b44a010b17241c80d05460104c2030741440306128070750000c1c059021088006902491980d603084e801c035451140100003041c9c090140c0c808141441e80180d40c29030301444080c038000d00e40e500040403407000340c01055604465906002d4282d074108900c00300b2024032f1040d01d03d0144903100245c8032010520615040680756030340d00750340c2846508024000c400c05002440000301d803500c040e48a0708040700307442c002844c0081b803640074070b800661001180d40684690090741d00b03000046540e58010310944043d50f40030005026003480c1e02008200509440010b8200c903400c00d212681000d01902030709680505000003881000c00200442340300d90391412000554080c44400c0d54280540313084c489601a10b41100041c031590001c030101c0c014030b04d9464542d40f07642d42c80000e8030341e00c800480e8504168071140014025080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 33164780 1250 33163530 33163541
    0x61005060d060506030403050307021605010206010e151206010510031125050604051b010206250c05010e06010e1305100b01270303020f03040503060a150f03030905150309060406 78
    0x446900400c0081d01c1e5004130300554420f460032000510004204a515603040c040141012840d03000302c04000d242000003569000c1c103000e50b650b80131648010604941d051240703152060000380010760b40c43c01030000e00c0d807110400d00c10680141025040a51214400c0c4544812030b0300440d14a03003001410815004640e8100e82e145080c0301c0c8112201c00855401c2001512891198004002c40e8018a40e504180480300c0306080c155803109041c08911514050714091056082600d0030b68580d03403c000f110805a0300720040e186500c0c01c03c808001d0880481d01b14140c4892106581c0541c50b01180c80308400da043c50050310540220608511a06075600440d84504e01450104a0000e03017205076030043d8402009451407000300042041015014010b0601c480003000155040c1840c100229490780d10003400b81c6e0040380d50f003100c410003054441500018002d0841d00c0b050032a244d00d0003405001c0f6034010315202d204040500c481c0c104d110000c0f01e105058510240c005501d0f90303034401d8040c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 33166030 1250 33164780 33164797
    0x120f0c03020a030605070f050304150902030723040b0a06050f03070512010b07030206060a061704080c060c03011404020708071407080d0e040516170406060503101a0306100506 77
    0x8019880000c096503814880802a6004030000640e505102c03402610303001c1403610901c240001401048082210455403c2040c24516004030349455180b00090408156070414001c08100042c9424040940048171400d0803046c0d80030000a085801000481d548a1081c0000140100300c0f40c0e00a404e041c000e150807210034149541425489000180309070026080310300c15440100d038500c10300d41c0c10891643c100c1e005440400c410f070704018004107240c40081d40803940d510300c3c00110301009540802c4400700c1082d0000e494150030b04a240c00c083c1d030300a11802e110144260700f0155546003e00c00c0b0340c01164001d80d0f00340f5000259036039502681c3c514050500c180076030703140000d100c1e0f024012032100c030744503a0320070050844031003c105c2160f4000d810035101c4140704154145241e041580104080c9241601540070351300c4e0301d801e001400043c0c10181e0940928a4110034000c8290003403480c115049541100c04268102819030300c00b0111010140100014030401290801c000100b150030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 33167280 1250 33166030 33166043
    0x60c0a030f03060f09020904050714040b071713030c08010c081909060504110a0807050d0b0c13030803010e07020c030c060c0a02030106030c0504050c07080a08070309141b0307120f 79
    0x190307903502e40100c1343c01c855403040c14480d400069401183c5043d01c6201d034440f445081c80d42d05400e031a005202c2c0c50269002d5503414000c0001c058044c81a6400c585a403c05440000380d07680d9012101c00003928000d00c000c03615001d0844001c40d0049040c0901045880281c0d1031110725601d2040603640b0091054220703511942d11400c0d100450300d5405500d100700e001c0d4500d5085c084802d414001d4601c595845082203400140081c072070303580c0d01c0b10807005498011211180d02d4441c1804007000c0e1007911032040200540c107500004000013a0003442c1210306682e481e01980e40c1d90001a030f200e1181520322039154000354081d03119417038078902503d140c0340c100c41280d084042c2c5c0c0d07011034215207051304103448850072100d0401c0949040d00405600c20300c100500d40c10728480f542c48416a001d00300d40c81c0203010302a000100d0152081d4446c0d4655904030000105003031568440640f40e900c080321003c442c3c1c148503100d8119040002d000b07000c0720b082c6509240074400719203440c0c0d00047d0b00c5004803200f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 33168530 1250 33167280 33167291
    0xb04030c12020c210a021504120b0a0c0c03021509100e030405030f0a02010c060504020d0611070b01060207060225080706020706080603060606070f020111010e0f010b060c0a030f03 79
    0x46440d4980a00701e14a0300e0b0024100c180c0100104500d406042c000300015450f035100040e0402c0000c64080303140e903070569080080b80d4802200710004e000f1500700c1351128890000181c01d0025042c82c80d805501071040400424131241c81c1203d8801ca454409400750f80a1424001c8584001c03c0066000304a50165080c00f03214006c0003065402c582d51140484c1e201090521003031405101a15428507040700804545c1c0a41c0c3c0040d21000d10048060241c039a104002030641d2200d11a0145c200c1d4840d00030070087c100002c000340650480c5400390f51071041c0303d002186403800051008107450040d0000d1008034140305200c140040c9807842d030f6124001c0034030005400701040100b031000e091560080c002060030080c0003090302000038090b83c4645c1c8200c3c2444000d48660080b1020141c0249840c03044180d0f90006035412802140900034079841c200c11030020042c0401e40e03030ba10044041c024801c031240710f000c00400740a01c2c05092110f410418110340040c1c007075208512409550f0402040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 33169780 1250 33168530 33168533
    0xc020406090605131b080403020709050a0203011706070207050d0501060e040515090304050d021018030b01170105010e060103020c160602010501091116021002030d020409020d0c02030a0503040b04030c 88
    0xe48200d40d00a401c03903a100d4500f03003d41c0c070b02403060418a0f000d03100c0c1002030210f11050b50404102801003003040c00486000706081c50702c24003e82c2c010780080320003072000381030003181c20b0020b500c01d00c180c0c544030b118003440054812001c01c0141c090038180d8000d000e024108410406032400101c0200c800e990307680c800107940c3e5805004603200b94041e20151002c10f0f48014441868180188045a90381003008180001d54401d04809406601501c1c01e02e140e08000000365000842241007111034240802e001080045208559050721510214a17008103040743c0c803942a210f003801003070b02200c01c1a00240c019442640940049080341c4200c42064400d01078007a1100466040714005075112401440069081d000706e2118400320720720703180b4007003c50890640d48000040024401d00d03d00c0c1032049054802c0080e940089907100046644a0341d40e00b0303620080d44900500415103040504502c9940e00220944009107081d4480a1541d80d0340d0360360300d00c00d031001001142031120480c200760 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 33171030 1250 33169780 33169789
    0x106110a030e01050417150709030b010b03060639010b0a1a04050604060201140618040212030c030a051308030921030d02070308060405060a050a0315180b010603180807030806010c02 80
    0x555070425a0041d00000000c0c140c900c00c6000010170048c10300c03e44007020030004a4070540c9a04480e01d00c05520f46036196100015114460001e50f10305000301e941b96522080ca01c0c603284041705000000a407807051044c0340450a0300c07645099a58002e0802e0f00800c192984848103810144520107810b14041c2c480b4000745254109030442001030b99200b003000761f01c20314016000d4222a080764011450201e81c3d03510100440000c0000b0f003e4100300100c0c2103404001c0054a001d40400343c103582c1c1707680704210002c20700d40012110003400c103c1483c0014510038040f08548100d24090038a1001104000d17860b0140708818002c400300340301c01c202c40c1c101c200302403016146040c030030340d03a80500b42082c80810096500107004d05101d0207640b20200085e0b41c442d6600011241d000c00c901c41c040f00038079a8500100700300c0e000c9100f40610b01181504102ca90000103050700c515417000c110394065101d07001c4510080110050050702d0811002020034025020700b0f13841101454102d400d00d4080d400700c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 33172280 1250 33171030 33171059
    0x105130f0b0d060b04050d080a090302030d0f030f020c1c0c0501110304060e06010e0a09170f070b010b0405011b06020d06030b1b09030a02010c021908150106110a030e010504 76
    0xc445055001c00c1d07150722400b2501030a4001c0607032403412810142002c0c0041e142d92445600203205e000005810203685010f21490f030000e68004054070643d00030f490002d4060140c0d10301d10800280303410409103941d03c0702c3c0700360b60f84082c50a00400b403480e45800504c0c0c141d10390ba040b58051111251500380090000d004842407a041149038035280d0400789011800e80e01074481050031a0008001440356100c40255103600503c0044d001c1903048090800085602021081e010b407004001416003013280004003c0c411036119600740304141ea69078101006074000d034081d01e40080c00009504181089001c100710700517006890040c54201184000405c440203644126180040e0504024100c1000c5090a02c1032071880040c42c80d013051800000d0b2140c0711a4002418011008008015901da4208154070400c070318006402c07840d2100f4900b0383c1c80340515040c0e2407080e017080022610601c1070302e00d01c49100d100340051119a1450b030301aa030000600441d241008024400040c5c10304032038100c2e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 33173530 1250 33172280 33172289
    0x40f06020412031130070206180a0806090a0813050d050a0302100b0604031e0209070809010b010e060304170f041202030c040509031b0c0603070315050109060e0105130f 74
    0x82c220311981c90f000e080d006103580000c241c2e03007140c226500d00d480c400200b80e12401429481058080003590f1907001da008460000e5002680480c850115040f0207080f1900070b0800c0b6050802d03255a9610795076144411100102c0c00d803c82103e0000182c0b1240161010b0a03c48403601c0c00152940e000c962101d120700c205541640c00300e02a1010f040d0144100c3c2c1400d054900140801c10304180460150f00c1a0322009103c1c08254586400443d205400d1030840e950050081e802e6040c491401010300c0c405070b071044003951030705050781000d6000707001e41d0312003040c042d100a0441d42d0300c0c2c84815200d01500340000040104101011003e5560801000503201d08680185c000c800d0313005161038903203016050303405a0310700024400200310003c166980700f100e02c4014038820340b0b170700d1402c4d0600d00508651600078001105000d107180e015003102841101e16100302100ca0360b035600450b01544284615000b003640c03903681c04015403151f401003580b410410040c034512561a881d020b18018250300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 33174780 1250 33173530 33173549
    0xf0901021e030d05010801180311010905011503050601080703020f090402040b220b120a1203140a090b0a05040201200f060703020406110a05030a030b040b03060a0501090c08010305060c03040f060204 87
    0xc0d1440c030703d5018810180501043e4000308081034410034480d68202d50f180018051200304814014011004d411204000e07a000000748145113480410800105440c00115018051000007180da51000101042205d80040803800d40065100a0004105000d481660090f403107000b461800e46607410441001244d000707400c454100d601c90640c040360480d521103032043ca200608039804000000f010410725030003802e5280d90703610400040e0028030701b0342018504000317100108142c0c04034541c0090300060051420504a9507095070f04401ca40f012280240840e00d8070240c64070303414680c507140e00e0b40b915140807140034403140200c092500c40c1c221810740000790000307018858030740d0001c0707240100c0340350328020300c140d4490b0317910a9128060703440605c04250744c4041d041d1a584d620340001d070701e0707410117070950b8010f041a039040340280409024203e1a2801c110b808841c45220b00d65a504036030708800070b88415202d05000050961024100351030694400d83d50402080781480244010400c215 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 33176030 1250 33174780 33174787
    0xd020f0414090d09030b010314030d09081e160b070908030309030304030207080708030418060902070308090d0c1e0f0206040e061003020703020c010804081303150605060901050f0901021e03 83
    0x75000d61803d01d41d06808000c02501040400001c0c0188422038107407540001140b12062203c007800b4a14014442444a56401e105034441032140c4500241034800100010b1400e01442d1600510300d486028084080d4803d50402c640105110000d595009030141c6400042d00da510074100d8070b140c00c180d601c0b5405030400401d1004050301040702c1c100a043d404044c2c00203900c0c007450750761203001d2031184110040000440c0c1030039803501d41c041000380c0400bc804548414840c00c0045c91210102c0b8040510310030302c504903502900a40c0a00d103c240d00000b56120040d0804404180b5640ca1900f21155030340b42c081c0d400183e8454028001401102140000916050082004c42d028050210f0189441009950301096010905030042132080c00c007031102e6220352130000340c0e500c00c08065201255482d00d000c410030100e404d4004044480080500034241c540c070401c8624400d1071a80f0740411010000320b00400c2c2c0c1c0e44040c002218050065441d0049a000c122242e1134009481d48050342000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 33177280 1250 33176030 33176041
    0xb040e0105030d1b0b090a1505180601050a0504090f0c1203091d0a0c0215010f1403010b0105041e12030306081006031709060706060f031e0804050d020f0414 69
    0x402903e003d52040d854007484540740681c1c00c1440000d40da6010b01540b091800161000508004134031400c1d500c400b40380d400786882c1500000801d070588190ba902203010191012400002072018140c440003404120585d207091700b00402002030700400c84400050005120108913520b4002d00201041c0440424a00d080e240062900c02d45400c171800410034148a409607114031400c4542c0b160304c2350750000305412451016450016007151500070000304100104d0381700c20304080201101c10380607892003207001c00c00415086c0c441000b03138580012001c0c401002800700081c06142d0361000640710034101e9480e440c2a4110609040e0b0540200f80c86880030041b50f40f00300009409604040350411000341940d407209031003d03070b01006002602011860804035500c110858916503400b07030701040560380e00c8200081418461106552100030407413152918014112004003403607024045900d05400c2404000b074045d50b00c1701c2680c0082032188546159200c5102d481012543c07090101114a880c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 33178530 1250 33177280 33177283
    0xc02060313052a100c150e030c10020d0605060702060304030f12020d090201090e0405120a02030c1b01020c010908032a060a14060f030303040204050901090b0705030601030f0501060c030e03070b040e010503 90
    0x11109000d04102502080c00c1c0494034507140c40900c01140b01c1b000c00c14134240001c061960007441c4141241d0301415220000341039043e4018204021200403d220281c0e4030404c121060041c4000603400660410000d00064400c3c0700c03c185880b0281003070441d05a04203100c0040340c00c04072418000541c0d425910040d981c001440c50014120300200800c175240a0303998035215075490b581e0300540280494002841e900900546202004100888101c0740ca11501120000e0403000b07140c1c003600407001c0101a0307511460030542076618400c01146800007400300501c04240004850300c1d0580198549844071105110750b03809155010b82c08101c000c0407034484a400d0b4409007400744610702207120754540d5140842541e51083d01100c00060a1f956100340501611741144002c0c00150780c6410811056009405140500c07004e07a030403c50796450803a41d1040300e800303000b4580420101c16103140024880c410030305d0220340c040c00765000c0b1950b59810101c1034005410030004440444010f0145050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 33179780 1250 33178530 33178549
    0x180706080916081b01050d020c010605040b0409050a0f0302100603050616050901020d18030506040803161d10030915060513090209010b0304060612030806100c02060313052a 76
    0x1104005a0310407481c1c00c07905507a40c00801c6485403881c460742034500e013580c0200c0070b607521032031360000665540c4c0c6035005040c000c0000d4010309104521b018144040303404c080c4039010360701d03500000034140e00c401d41d19081311054000004400710320130582c01d00c02c01207490080400551080d4000d21032414515110307994001d5041000c0304110080c420070380940e9000586400c418541c1c100f580f11141840d046890300001c52700040c025100380003e000c1040122001507200395421141c000702d648104200f1110f81141c0e081c0d006a184d500d0b610004545000ca0100010540504001503044581d80c1c841c520500c0060784804040e80d40c000400190030048032403080000c070250304000e81c43c01680011a43c081c180981c0c0c02000000c000242003208079413040c40604404026150400090702d03000300703102004c075885da0050500648401845010710341002c03030a0b500402007800c0d940c45010b40410803102308801d48107031080d2241169007003200f40400d50301009558000102d0311040051201406 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33181030 1250 33179780 33179803
    0x1803161101020c03030a0509010909060305030c06130c0e070e040c180503070b0f16050f0102030a111801030203060a0905010b090103111806070231060501020c03151807060809 77
    0x10445001e000450760080206c800c10350041c10000d032a079404400403684c0f0182904440c100600c1c00c0004410302a00002414401c4035040c00c442d0700f0358a070b403490680c0d80150a0001d180010750394050200c252148101c83c2c3c069580c0ca043d501e038091010008003a503c2e084110004500070700c8210b440c103040d110284c4041d210550061124a1400003481003e11407221325000300c11000c1350354443c100e81c895001a07255042411103212292210f5203d00030750003515031264151610341e280c144d140d1100207907151040035520b8000f01c0100040150060741c0300911450744940c16810110b8684054441c40d4045e01510815940f946503040014088520381c05404504c07041c1804451847d05004020148152050f5145516031540340b000c940c030b02d00300030299a0325204846204000c2e0030380e070341f0f14608100b42000a00c0788640e03034001a030b00d0305400b40115800d5008040d000d500c1001e40118030740c2101ea1041a40100d0002030101c03402c12105811280005041c1012700c20b00707003420003e414120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33182280 1250 33181030 33181033
    0x2070506070203060f0402011404030507060f1e0315080d050705060609060306150109150203070501060e09030702010804020a0f060203120a0c08040f03030e030301080a02030f01020306010e09180316110102 90
    0x4980d00001c4d6514030081200c941c0341c9003c00000d08591045002d45444a52401c078030b6240d13900c80c03500e0703600e8020700c0c09444001b59a240007a50054402c0c0c40041c80040700d26628049203c00000881c042c000903056103141c0340480320b001502e12010440e4142030402070b034411780c840b1040e28042d81004030191007207101307000c1002401103540e00410300036004103008154403a055250401610a911715602800007104200301581d1902e40100c020106248104020050107840307903201c0c8118803050710038101035413051044a0055004103e8160172030b00081501c0c41c69aa10004441c000c012070300070100680000c00d0000403100e0450300b65402ca403000c00207000e00385100d080103100c142c0007000070304100c628000700d0301414041d0340a41102d402d03d0055a0b82e030341e1581c9459540310746141c4124004d11804500c850310300c80c10b20999006071816985d904912090302c0800c00030a01c040c00703400c560200800001d0040c41c00b000140002518880c810700c6050310307420b0490300c2d0b41a001455055 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33183530 1250 33182280 33182287
    0xf0303031503050304180e01020301170c01110d03020904090b040f0c0b09010203070201081515090a0902040b040b0a0210050403030b1503130204230a05090c030d020709020d090605100602070506 85
    0x250f002c021368098840204001c007280c040081031501070100401d8811b1194400000403900580310000e04244071600c00c01c64490702d4142c0011079030a040181c515045800842c0e00d43c020b544250000c10030310300000d00114454400d5218500700d00c00545007180d0552800854008004521422034010f00040c130155060006050000c2d440b4490703c0002810841100c00060700700109507101c2a40d074038041c081400c02070f008203001c11540d03c5010082e204000c0e030580001d410340d080c001c0705d040c1c0740f81740c0c60242050300d000d50007515900010841010740c081d1441c501c00303050701403140034410317800b0f5600031451605580030b104001081451050351100304008010403080481d640c103a03080d0303044d1000915184554912201e00c8407030800128100380d184e09201030201c454000030b001d010404281c0c0d064103180323420143d94006c055814809600324070410000100ca66000c2c0444842403440822271402c2540c4002c11920100c580c0e00c0c0075010f04200780100c2c2c1d0304202a4000c0c20702644c2c000d16 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33184780 1250 33183530 33183533
    0xf080f0f060106030203040c080a2a0501140a091a030a110a0804020108061309030c0c0f06320d02180102071a090a031b0801050c03010605030f1f0f0303031503 70
    0xc450700140102e800341034001011908000000d0203580040c0721880549062400628020712411a00f44070007088418000305026003221103000101119016150028548400100c00702150030034000b103428410800d41c0092111289600d605103249004426592807610784110401c403007200c54801c124000c14001d500116810404444d0410780900b0b002c2840e03a2110006200e101e60058002c0c0c1c09403d12418408164100005201c4184601041060b4540b01ca002580407052840389000007042161510083c1403524900780060000c1c03040e4241d83c80da12000d21403154040710410058990003d106a102d402c21054003005090074806010900c3c0382ca05071502004107012a44080034000030001e50503514071052000640d800303441130288a0032510008240042440344642030350a10000650f050403950850381a511940c503400d00f144c55055055008140040040c3d0301c01d23034094002001509055a0b000c0200010158072200742e0452800805648442070590390700c03015941f0610 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33186030 1250 33184780 33184783
    0x706060807330305091e030405090a020f190c0204180212010b1003020a09051005040e13050a0b090f060a060f0501020109080702040507050403060203040c0302010f05030906010e0717010f080f0f 85
    0x20200a094603010078280c031174680322404c10350102640381d81e82c90343c0065040c0900300070024104030b8004442c440b6040d0340781d0345d14000b43c4c4100c18074218a03140404c0803140d10340c00030200c69030502544c5000c1d088401c460b4007050440e00742d0084c00b4012000f000920045243c400741d00802c4c1a0303050024002008000003040742c40003c0d600080902d5008204140d40714881c4405030b0052800038075100c0b0b4280100d402600c42d500500607990809100380c00a8201003000d03006000d5140d100005213013000e1940c54000d0a081c0150803100c036401208040c001d005020090f00d40107110030000010860b00c2e084e64803100c250349900032819a41400e45500c00301c3c1c5c0349002e982e107244e010744011520b950380c410200c9180c404c41c1c20080c03600e40302009120031301420050482c10359100ba04c2b03803017025694007401d8800380170403608003074140d01ca1001400701252410709140c00901504006100e00c0d1f40c010084070340d075000d8201003c1d1441b04a006c00c042c01041064201020181001d05105210194842e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33187280 1250 33186030 33186119
    0x5070e0a09030e0f0414010e070201110a0903020103020319020705010b1201060b03190608060403030b090f0105090613060b0d0203100b03090a03110a080a030c020606040506030c040504080706060807 87
    0x22031242221208640064030f56400511061b85100d100c007205603150404040717505425121100150b181c2900031020f2500c07203048032904c003443d44401d0301c10382c6144d0044029500042104010034000c403102d000c0480d01c0c2c0054100303984910004507410086d0402d0201c201c9140c000076280e44e04220f030401034410070342d00320303030300f18010000b0441c40a00901d1360360084c0400c0d6001690a101c0c0030200b01c241581035000c2d400d2542c049505803c55114410f03080060070b4203010703039640070000d007020900078500044003110304400c003070002c2541661040305564075000041c8100740690000101f180c942041ca45e20380c06001201035250640c14455030099449061050003404d00030b81000304019404c003008900345495002c100c446d5500c10028000340540304001001c2d016104040202e0000e00d410b0146034410030015000b84400c10802e03041002401000e4000d079164a010001c00000c11007500405028100d030300d005050080c80e00105806414120980c200103d20000341e0b542c802d070081a48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33188530 1250 33187280 33187307
    0x60903030507020a051c0309090b060f09040603060c0504080606030105010317031b07120f0f0e011d0a030f020307080303070801060c020118030b15030307081e0409050405070e0a0903 80
    0x120b071900054400b092000318560403942d84281c64a5080d40c42c02098905d80042d05d10031754a41caa1940c0e1014050160b400c0504900e511070010b21001da40004070b03201512212000400220302d9651342c0d15641c04403609050080000b0350006800c2c001301904010140d04150144c0081010b985952500202421000d08025121000001103100c3c0c10451880f0444400404181039865229240c10300c00004c0c2c00b000c0402150384c1c05803464a2030700840301d28503215101e440d07840d15441d00000450340c030070340e44614032800000a84002c80329100c980d03d003070140d80300345031003901d0030402e00425190800a80c45840954002c20030002d026512807100e81c1103541e2411b003900303004010b200582c1ca4040c050012182d21902071400401c4c849190f5440d0f000700c244180e980703600b4448200707140d102d2181e14405070445004200f020055400c41003040940c01c2071921340350410b074550b0342c2c03031042d1501640c045c1e4881d8400301c010f010500f004007000e030700001401030402a64646681c0504101416400b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33189780 1250 33188530 33188537
    0x6030a0b040f0506010b460203041a09010305061c0b0606091201060e01060c0302070b090a03020315010e0c07050c011d060c060f06090f160905040501060c15050106090303 75
    0xc00e0402121080400640c2d501401303540496031076515441454200703030304034500c001405000c20310f051002101e031040070034101061220b429544550309a8070f46601241d0003144410400000d06103503403203010310360604000805a56030502c070001419200c01400e820b100d5400014114448200440210f11080d4400c0020503641d075074000203003140c040c0f5005603030001ca4280801c07a02d002c0643c070541c00d072000134484d423440d82d883c2c1000300e4040d65220801805030b480302c64184240100b01c00a00040700c0000d14280203c0c0c2c03030343c1c042402d10340820500280c4100c600018481007207107600741503101d141c0e0305460341840041d40f120343e55668501d00b800d041c1b00101f07411400c0e904007200d10814564004e0000da550b4542c00b00200d5490304101e40b2110740d611540b0110741585401c40203103000c0c10401c550a01c0b80e4403a04030072900c007a10990b00b04184110000001120740321400340c203000b46544d8031285140841d40c00c2410004c880e042655403050300c0c103401880075030340242605003a01c1c0c1614 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33191030 1250 33189780 33189803
    0x8160c030c020a0e0402040507021b01030f1812020706020c0f01030e07171501090b010507032a1124040909020105070209010e06010f03090c030f030201090b0a02030601030e030306030a 81
    0x201558107440509010703400a603440320100741e0200d03144030fa40c0224030a07101000180c0e0748190407611109080031031016414000102c10856100b60824000100a49000101c840c000d82c0e44031041e4008007812228890f0080c3c3c0701c0d08060b0144801002040c09002510b04214890005103840082510890600d0307981c5e041e540b840103041290001074450b1950244030003e1102c4590fa551080c109030f00842600c41c000418031800901400040c070b034040e1510750414030790b07990a943c09404100c00303400f4400b40039202d56103180035a1602d0b440e1790003a0a920728800c080310602680012a442d80d8000808028a2120100207501164121100300b40c3c0010761900b030303100480e000e2081030b1019600409050000c95021840c0c0b8030b041c0604000d885024401c02418016001c1d9145402c014110b010080310400118002c0d14652000c2480713840000303015440c90380d8405016a0a83d003010b03202c1e501108012007940c140c890180c013a4203000003076045103000c40001e50354071403400c4000c00a0703031b181 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33192280 1250 33191030 33191033
    0x5160302030c130b0c010b0303280203070f030f03050106080f01030303050c0f0d0e060112080d02071a070206010e0907030b15030309180712050c0304020915030d0804050d08160c 78
    0x1082903c80c034840390511140c10a1340c03803400070382d142c00c2621400019440d0580c400140d10380002100d000880d080b0300001d1507510304c0848101d062031581d00d0000e6003c00c103c0480000c130400324046a49119440c0d400000626140040490358140c020400b40706c882018030050302c3c1c000c030081d03044030350514011800355282d8985000a02400c0b00e802101480440d4005420b4499040114081d250704122407a980c1d890410310176418100c0c0c0084d00d245010050072545d0720741500101105402120055130821510341c0700c40118608a541c100140c00c00401030040400322811507400100000c02000c00d9429034a9110001d000500443c4941c0520b015071105510b0900588809520081903115000341140315001907007012101c2c0400100580041500b0301d520b44922400f9001d4507500c0ca056568550074400790600141110301e01800962002c074042d0303420030038408070b05025541e503405030800d890460324100700ea24003401449500020011000c072004c0e0f0078550400d55290005000441c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33193530 1250 33192280 33192301
    0x305090904050123090105070f0903150b0a0306020306031b0a050405090a02030f070e060d030e04020304030905091311030c0d15020705030d091214030a0b1503090c010807030516030203 81
    0xc800300130808410525040505243c54007020384188201c900a20032035517400e204413480c54a058480000c03401700501800460205090503901d00c44e0a10300090200b840d90005510070031039401103850b02d800000b00a914101804050214010150414004529000081d508000314002e250180f69550000380c100710041068030038498001d000d907503050100b1000c860b181d54060054860380c0a03900041452801d022008429450709036641c0d02030450309200b0040651f00140040e401c11002e250080382a945860100c3c1c0100c2012801c400b504049190a800d51480408014803036080003d801031107486000c01c003619594481e056082a0003451800f034000d00824401600c140320200d9445100304031a4401c610060040941080004455a00b110390700d90940c01c41c0401ea0044c4080b50b80c0d04031b280c11259000400030588500507800004003022a00101c4507405690702240c0c1844295800c5202180c00c0066480c0070700844c50031644101021111070b480740c04059001000501103441c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33194780 1250 33193530 33193541
    0x81303021e0a02030d05070b07030513021e010f0e03070909050a060204031a0c0712080703090b09062502030702090403030e1905010f02040f05040908120f010e100303050909040501 79
    0x44198601c001180040101e507a100c0007a0000c038002d10860040894450040007a00c00550f40314100c10500d47c1c4090003140603200c042c0c1405c80010081c800c4000590343d05000c00040985c80e1354a1b103801710036500044c40c40005600d014148102c0465882841e1008980c000c1510307020344010448185a01c1c041c2c2c0391481c2240e0107801075201180100c00c00480b1841a202d00b0400060b404080d282d550b41450148903213400208448404056266031034000c0f1410341d0301054900b00014480503d0312a0095404100c490503190f80107401080400740520410500c00c0d0442c0807088820b03090301101079524440d801d00070348a40310f03610000d02054881c0e008440d100d5654003d0740d80380c40c01003009000d0281d90300c1045a01c0d50030988140340c0350900f88280d030111080d02400350390480c546010301c4002e0641e10340944100c1c008000241003050240c11943c042d405010b1035501d150f1400c00f545200c040007514101d00440c140c41d0410100b0745c490191106d0742c40c21210310519446900d0300d1401804c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33196030 1250 33194780 33194803
    0xb100c1b120c06031d0618070b04030303060e0a0b01020a0b1b0403030806040e010b0a05060d060e070c0c09020a0e01030510080d030209011e020d0c260705011b08130302 74
    0x20840d40301c1c00200309040d5a610100c4141e0740341441500307a051011040d0002115001c1510344c814000540d040989014690301ca4204034180c0c0c5a90b6240c400b0000c044d4459003040e00841d848560800c008004404101c0c1c0c024128882003015114007c0001e441c1c15260300007800302c020840102d0b8410310840c5050191008102c82e0641d61541d030719014081400031105144198900341c0000b80e4802d0601034103804020080c81c400080e8280300c100841508008200d0b64103a036681000b0848001c5000c901d40580102e444000c82e081641c50280d10f007000720340202d0305003801844003902c1290001141e0107140424200481e190b87c400c10652540d8945a0108545105401c0c18860490305a401800c2d244800e0b80e50344500080282421141042c111002e00180d01000f8004017440c4103107101e900ca5171040e25102204140310782003400c0940c0c0800d0800e2a04000510401080720074405c2e413040c0030300d820802a03010b090001c040c2c4004802040d220070021541e20b500c00f010702c02c1c002240041c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33197280 1250 33196030 33196049
    0x2010605030703140607030608070612110a020a0b0c041a0a030e0d18050303040b04060507030210050906060a0602010b030d0e0103090b0a05061005070807020118081c030b100c1b 78
    0x6642d81c10a81c40300c0c0c1844454450a02170340000c00c0b41248280504000e0340d42c840b000708181031030100d0445143c103107000702d020099611b41040640008200c0200807510041e4020402c0c041d0703d0814183d00180506012850f4804000070054005a90b20340e60403040d02000d803a441c0d034001c0c1d0041d000703000094408821030041c07120081407035810418a01d5243c0c00c2104181040c2d4580d03060560300c4c03050f4010030407c400248005c00c0154418002030203018460b1065035610300c00c0d185060186c820a99801195401080c200b0480d03080c85281c0800030503030b500c005d01c682880b46000c01e0322582000d81003820420300000000899010b030b0003030700303806a0002c191001031500c0070400006003019200350b0300c02c00d080d020701124648510156801c2d6608031100a140000319130054441d100b608503030100d484070170480010b00400c1803200c3c5849506000010b400031580000003070444201c002e0042c416001200c03c0d00d0103e5000101c2c00c10030f50700c400c800811018041c0c180744580c0d00c541c04400038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33198530 1250 33197280 33197293
    0x1150509061b0f010b010e040f0209061804050606120402010f020f0f0109060f06030201050412060612050102070510060b070b0907150906080115080a05040f0b13290403050a0201060503 81
    0xb00000d01c2c1d219601e40d005000d03070f903400c1282c40b0100e00b6030310300c0310405000a4250394581a28a06a0711a4206038a100d200618100c15000840d03c203410400000c00e004515184145680c03c1078096a9413006080307401d10314001340040d1a90300d40501030800380c10044c1d4051810202402004110b4074040107038101c0b6a0141c1010070140a44400c0700d0403694281040240c061007100d50180c0d00650fa4161640c50034981080180b02d0312a01d00b56060b0b07041a211900041c2c0317002c1d043c0300181d119008400140c4c2e140c4640c1400762074030100d0207070307111703017510b02002002030603c84070a81c0d4150703601030314460701c03515000d103110715000740d41e0400c4649074030485140004030307001300b00c5008a0780b00e034440e00300c0f07070b030340d41c405107950481103403003500810201c1000611210480d80166841407007440024190510b503141c8100ca4142154441c19101103070f921002800501054015042c1588002070700510010800603108280500000c0902c40e001c142c3c002070f94000c0d048500a0300c00070301160107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33199780 1250 33198530 33198547
    0x10e0a140a0b01142b11160317040f061404020f060a020309030106060905010801080105090303070c0807050a0303050a1a0607030e010903150507030509030c150901020d0914120307080115050906 85
    0x5002c0a14007021900c1ca0541410044416960080c1d4400019810742103051464a141c034447d4680c0c0c68070102c0400011100c03115003182e45601d07250246000b01950302007100e0514158085801044044405041031010000103035240c4400520716501950043d440340c0408d8400d070f10b98008c1c00d4900780d055080c4503020440b00e0344074940b00102d620980c0c1d6070b000303640d075841160701300c0c0c600761495400ca4004000280030b840c01030300c01e910628880c0d1055850030107680c88041c104030880350104c0000e5215000d2020031f041c01e004d050459003810000c2c941c200780f00d6000810a200e18030000f000e000801c0424003107a03029428080045820402640025103000030f1038009040480d0f44501281ca4200807038480a000400e03154010081001407100c18000344412000c0e8900a01c24001076408210103100800309001d0700700c03014130488541700743c0062a880349042511519400300448801d1081000866121000504542d000e100c22143d54801d80d20454041c0f1071248440c0c0c100d540081c1801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33201030 1250 33199780 33199807
    0x17011a060d110d0e0c010804051b06040806070306090614180901090b0903091f021005040c05060c1612080318010906020f0901020c0306090312061215010e0a140a0b0114 74
    0x802d000001c4c01d68840c00c01c12001503079a440d0036140500f9036071009513143c1c20f00c84100c200034650b4200610450078a540d801e0490309d0801c049585800007a15028108a03072020350140101610454074000c0059284a000c11130710090802c0b201d03c801030032000700744c01c01429442401015004000d40c0440c4c41c280c40c00c0c070380e2a4030902e25180a000d42c00c0c0441ca04541c0c605071941c08960355400f412211007000d050b000586000341041d05c01492041000425071340d50f40042c9115944c400c083c0014003503c502d91480c1000076401803d40b0040d041b07003140040c001100310b07a4040c3d1000383e00d181803450004102c1c010490140c00502d51072000424101c00810311000e001108026404c0b205a1100f2805154860005036284101a801801051481d5109031703c070700e83c481b102418103050b504005584034504004582e520110710030100042c0309113404040c80a50100202f207051003000c0e82038060303442d4020002c0c20f184d03100f507580c5c1382c00909a04c00c08102400702c1d9455402070702c0b0300c6111980d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33202280 1250 33201030 33201041
    0x909031701050303030105090a0b010315151403010f0b0717070b0108010b0102010603050c0f190b03090613050a020405040f0b100f06140a081008060108060117011a060d110d 76
    0x420000c00100002001d20300003086078140c0f9000340c010000b036124200c00c02c0107050500507203814151180110301ca10001150301d1387c0100155403044024a2148202411444c04450398880d50003041006000f545503501d4180116426005a655120007a00345800794140c8121054014400002d224003808101c81010b13046c1c808401c02000030810700e00040e400c9940c140304c02440f40d00301c010145200d2030b00700b41c401c03172100c0080d14008000c101c00800e50f140c180181c0180145c01404000c0c012120000c000c013031703440142a0620450101c103038035250365aa030401c000070b204a4440c8001410041482850040164400342e189202d0401011116071688540501e07143c1007691640012140c1c85400c401100d007440802c2a458041c2c3c4560456032580c00618103590703a200d030f02d030000b900001081080c1c000d05545020f8802c0794103002c5c2101101c3d05d05003603240c6581c140450f50101075014036044030840001c0f82c078690f0303a0b40c4510919001d0075550060481ca0314020659403020120364000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33203530 1250 33202280 33202307
    0x120d06060e0301090f080c030d02041805060d0b040f03090b03090d0f0201110301090c02030405060d1a010f1e02070512060402091b04030f06020f04031109010b0c030d02070c090903 79
    0x10300c0c100300030711400e050032540085806803091084000d800c012540440013885041900c000766490400d44c0355400090342d0059101c00349050b50340055840d030024a11900750058012982131709100d4507516034000103500030748041c202c4400d10703404000f0180601e00140050400700c250b141c8901d0040e5119131107a03084142d80000c1110001c1000f007807803040c8210404002808484d5007181d00b0101100c5c014420102c1c0c40055200c20040403509a440030040c10003501c84d40000300d940401c04401610040800303000c10b040c44502440590015000b610908615061103c20000004500412490482c5a50042e0b8010102e1400800104c03008100a03200f103000781d0703110340d8036200e421504100c110101d000c040e61840c18001400020560031914407124000d031005800d0040c6910003c64550040e841156020303800c1c910500c917410f000106c5030041142400190030300035401d2080b078a9105203c2901e15155002804201300010104514041c0c8940c1604104204481c0f070040d000d00380b0200c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33204780 1250 33203530 33203537
    0x1080a0b18071a071a01030501230a020304061103090d02070b03040807020d0620070203060f040507140a090c0201060807080705010f03020f071205091302040305060403080702120d0606 81
    0x381c0c0d04070001941c00725500e0751038018100302d40b4018100822211107503142e0500d0404010302404140312841c40903500d16002c0000840f54503500c0c0a03821103c1103465480141c02c040c01c8225a1000030401d60740c0078050b01005a9a503440749003240081000071410180a180031040c01a40c8100040100c8401a540c007101c103425294007490803d07000c202c8004040580400c03440006081ca80300c90140b9611510300402c00c1d07100901c0d80d20b0300c81129200d802d908074000c5a00300c10340c075042010940052004441c0c1c030290420340c54094840516000718280812260750702003094842c0c100940c0241510031b0104424884100028040d1085114089403803203001d0700460720f51004242c0400b15001610751606042000005031301139009448400466003090040c0d6011135000241c000d00c2440b2950b44503514904801000700b035a80d031741170130034200d441800107000040001842c9604141c00d424484410354a040c001c9103031503a80010a10f0401d800f16050102c00055001803054410544 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33206030 1250 33204780 33204803
    0x209090a1a0111070911130303021c05090d0204020315040e01090201111207110406090906060911130e04050307050a060e0d110c190506041202090606040f061206090501080a 76
    0x2070045925002c2103602d21100c0c2c005400800c8051030320f40c85000d51003400e0102c5414140c42c044119283c84a983c4240c0158000b5803401580c8000381000c40b403181743c24100581001c0500d004180b00c10700c1c0d680f000f8001c6500001041641030403003410b070503c00b4010000d00c95140400f0619010b40340c2140100d01040c43c1060000040ca408078140c1005078108012a0400d081d0381c544120041403d51929041030342c980d000b10381c08600c4d0081c6903005000c2c50000c9126440c1014500803104800c2004040800602c580817441c40710317241e00001c54082148003d003039116401c00d83c4c02c600c80d03200000c00078812714040100f00700380c0790046100414040306a03007140480751025105c84001c600c1d03001c1d080c3c01401a50066181800d0a11440c00d042c51b101c40f2404d80359030104d41c80b039101e5007041101c52461404081149801840240d00c81400d0301d4450405140c941a00c440015500804007402442c034403018040501d503000d071004001d131540a03c002d5030b40b4143c40391141c00215055844c1c003203c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33207280 1250 33206030 33206081
    0x301090222110309031b030a0f030b1503091b061305010305090c030d1205100308160f0209040305041d010503060c090d080316020d020109020d0b0a0209090a 69
    0x1841128a419005000041c0008544819507564140032050780d41c6195034200301201c0c20700c150003a40c442c003d100021a903844040b4900c94140421080d4280240d00070818004000d510500d0281c5c086040d040110360320701c1702800180c900d042e0548152004074048100060f1210000d198881c200c0b00c1a0030082141c69442440414030881080c0b041020145030108495442031707000641c864040c0090b607440104000010b0309200400002c04006210390355207035030f01c018501c1016000034070f05452500c21803465594030900c6c0282103088202420f441100401c1c0040c3c0c0042408091b130003040b6405074607181c83c02600c07541050052440c8103000c10044c2140c82e080018044c1601e4005008050940e62800303d11117a602640300d66801030000380c0a200000d0043c00911b0081d60028040804103103010700003460f1100c140408011a03051482c20009a118120758141a90f001842900c95070707240001c007402b901c10008130307030b402c51500e10400100d6603244d40319090741d1040844e007804c0580070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33208530 1250 33207280 33207283
    0x6050a0b040e04080a110105040602031e040b0103060506030708030a0203070c0915090b03010209030106030c080607091505090a0803120a0f0905030d0c180b0405240901030e01020d02040308070501060503 89
    0xc90080c40300c11040360003c40c0100345407070b024200404445c5000548441c40c001d1481c02d44a00340d5048512540110034000701940b00703100520b030011781490210701864907031a40d000350803041c88003900166540d00070840c44c3d10b090040402400f00d0404a80e07982028410081d17807a070061401340c03110b000c94180800c49511b280104100c0550715a0148280d40c28017100d10010005000c050364150b40c00c214801c002c5c0c4003801940700840c0507601e08081c907850415602c4c18140c006086908005c04603805110b00207242101e001c25420707915080f070310b541001c00400c13513498103038100e000c5602c00815130903101c804085501c0e00c5619010410721003000c03d485200107030341c0154001800c641091202038681c80003036000312600720305d91508108007a8440e48200d2020302981202da2810700004051001c1d080c03086507645200d024603040760044001c038030504030a001d0301d000310341015111500044600025016103910303c0500004640d11980d038a0607050551100b42c00b1100c07542095030020341d510f0f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33209780 1250 33208530 33208537
    0x807080f150906061c020702030d021f0e030d0e010e01060b0c0c0906040f090804080f0c0a030b0a0603050d021b04020c0304050d08040f06050307020f07030305041814070306050a0b 79
    0x140910455228400da0070449440c60062030690003410034841e040d010f9009505941307400e16060300041c7d4031002c030f006150601141e064040d044d9480b000c0103103009480c01648080388420702e000007540c0d0f0603c410702c4d4113520980c0c080c841c4090918074640f0080b113043d4010880644050001c02c070b101e5403001440b80c036000d990800300c0145c00400c1060351504085480c50342c8100010b000140b0310586d0401401200c4142ca0140c91030381002c101846a03010400c50007205802d0b84004018101882c00050850328190200030000341106011032050a059000071018503840300c1901c00c04000320174001d684000c03141040c05480300540c543e443d0360401d4821240c5a0320054091403800741440b040c06500600c01804840340c3c0810000010001c0081d0070310b0010f04600c2e030328a99642802580203142100301080d040707068000b10810400281c1203404c0340c003154204840c11981d459940143c1006000c1e07491028403991204c3e0401c0340c1198160320000c2600c0040310900000e54544050100d00d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33211030 1250 33209780 33209791
    0x120601030305030a0f0204050604120b010605070809010507020d02031c0e09010b090f0112051303090b09030c0103180b04050a050127240c2f100c0e030601060807080f 73
    0x550400116080000076007142617040031030000940782a0741d9401180c951741c4294018540d10492054080401411401060060400c1e00d442c6c0c0c1065480e46807010755100d40250795050100c0055204e045449960070318a0242d001404c6d520110446802070502c4820b11700d404002481610b070310841e0746030060b062416124406030103820240a84240210035440705031040c14021002149000d44103140540e0703200341d5400754404240702c0c2c81d15026244070204e070030a8003003010500003409107481c00541c0f140e81c0c040918006c24403004c440518a41114000e0000e449101008100400d01c0380002e006d1980c5480782c8001c00101041501a601e0b06150390000d60031521104212000314041c040f904460b4200819288142c035201040201184d80041031540825010442e2484000846041040e10001c0c0d00c0c3c0030140b100c2090700c145d100e81f49803441115290b1345000103001e0030b11450b41d5038a440c001404444965031940b0014000b10070440e1500005445100010900550300c044a030280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33212280 1250 33211030 33211037
    0x10f0207080d2415030506040902010503151201060803040e0a05060a060807020102040b0318010c110706080c090307030b0f01080a0b01030206220909030201050105030c0a050d0606080604111206010303 88
    0x94002d4000e40c007805454041c684491410042c0c1000003030180c41d01030013000010341d02024951001d03009020b90758010540c621852416600e080540d8100003200d40c80410302c0c41e40d0140d03141410003c0c40c039010340c03110b580c023030361070890041501e02d40040180103030340e06808520031b1980d80748451b00503240700b00c035000e030814900031041010034040c02c42c2030341004041c000542041d442e205d104015070000c9407007088039280e0040003072141d2403e1107254a010100e10740005082d45011240755038103803622641d81003110b0800000c00c098216429514880401000d88240c2683e80c20001044c0200b50350000d10698004000603e41c0c3c0001041124543d0060340041c00fa032039034081104542011242d07485e4000495186100c01d180c17140310002520507c900000c480e607032414002c1c2102e00580015019500c03400000388540c0c5c510b100c03842200d10440385560624840e2070030a000d01380641c003201081c802c1d001032100b04141c0a170041d14048007610110304480844800c4d0b45c0c1e82071700b8400613020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33213530 1250 33212280 33212287
    0xa050405090d0503040809100903110301050f070e0a09020307050304020a0e0709060e0f10090602012f09030f01020a0504031e0213020a0207030206070b01060905060a05040902091804060c02010f020708 88
    0x243c0108013441e401401082500d0a10700850f0120316044081420003001580d4400240100503852501803480e1005034000c0000f8600b0071102946440b01034081e60510400e0700091002e0f56602d0703902005060310b00006d545a00300f180740038000d90020b4a040b40f040c6090300020541d5811440320920a40b00303a620209104d140c25016140d00d05000328441d00494903101191158483c6010041001c003e503444be07000a01d00031000342164030980c03101740d00340e80c207511758844030300d0800c0e100e80c08a5105007025503826088000a16000400d0385c0c24450b0750000c6030104c00140c100d40600101c038040c010301c2540c0201c2c1c220070200b20303d00c00f40081d84101100c806c4000002035a01078a5850343ca401102c01c5941c590300007545035040040b0484d40e541d00e00d001405082d0b40031070080001d0000352541d034106200c1c2c940c0500903028a02807560351a0780400d07024159076414189840314954a4100240c3d820107041c80d201600440203a000958240403015074804985c0c0b0031641d0f01c607008040c4508 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33214780 1250 33213530 33213553
    0x5070b0a051b0c0418030818151501020d03060302030604140712050a020a060215010303120b0604060203180609060d090c03050d02030304050d02060103020607141c0c020a05040509 79
    0x100c0c0c202801080411205021015035800d81400e82500c2050940041002040e61420881502e480b82d2a4001c030000e0000d400002030f400100a90300710345280212140c042d8501d40c19460700323200e02c500384841c24501c130034071601e1024a070100250007000e0f800d881040246000c00d50540c1d60500c0025050351101000a01041101104440003d100400c0c0c0780c000e55a900341054146845009a82c1a08070101c1e04085107046070a80c40144500d0000d001c28280c000c1d000c0c0d100f130005100240502c8418260384080a0380c55001440c5004010211a201ea498110080d0b5070b4104d048620802980c0303a90049643c500401940d0b14520001c1c8103030b160070080100c201c003920480c40c04030340e40102c280c0301000107541841004444122980216282e1400c0e05206103018901c02032401035422507001800580c6416003141d4865412140c100300d00c002d42c1740302d180360850740b200710a184650714031240001603004c2e000243e154000c94141d11f0442e00c07041040212281903440010a500c42000c80b174 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33216030 1250 33214780 33214799
    0xe0705040b030907050307090b01030e0c010e0112090609030903151515020a050304090b1e0105031503150718050114121902120601080a09020109031b080a0501020d06120507 76
    0x103501c40c641c5019252055680c5c000300340b4050b030541141018a403034420b07001195905100382201c4000308002041c030b0390034020007c0e1180080ea6041070411017881d440350140002034000c00d0801d64415410040c0154500b4000d014064a000494015603c42d10085180c0c10764000c94055800c01d032607120f00d02d840d151000c1d4070301030810300601c00d50281c000c0e401c000c41c0e818009040141080500403400da500e1108212000c11200300c01440c4803102d84403008140da0240999a01469443c5401e403d509100006072070070382103441003404000210304000c01c0340d80c402c42e0b88614154010401e1005501e42005503507a88001764104a200014080c24108450500700d1641045001c4503c03900d08806003000c070242c3e80300c8090000c164003200c040c0b104550340701511680c008a610420402e00610740c1c0002d01202c0c1c5440090000e6918200c82403503401c03d009200014a15a03080710301000891070458040e400c5020309030841c0746011000903c1060800640c0416036205019013241d605000191 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33217280 1250 33216030 33216037
    0x7080a0c1109040525030602041e0506040614090607020d03020a020f030a0b0c031b03070f0816170402030f030d0911100804060f0b040e010504020a090605100311070c0f0f0e0705040b 80
    0x10589810005c4002000c60712520040025041e04000000c007042c12000188465003d036001e28000e80e0300700000c00880d54007107a80151150a8000709a680c0890000214035002c4d0880180d44040405428410150002a009801b40c0300351100e40004101504140d1685800e0300f000d8954421040020512901d090045a01c0301d0311144500400b500102400000c4e0000c030f031030743d020407050b00340c501c2c3e000d070030010301ea42c04144201007450100c2c0c4984002c240028140107040e409118a010400310340d018480300c20310840000c1165151000080c2a4005d000c052806840c6c41106841440142c24000611070600e01030381c880c0070807030301c84c5d40c0c0380c40c01000301d00103c140c0560f50341a003030a1544c66002e45c0304001c120320000308035400c00d030040000f00c2c042648030002140c40c04208200760386030610380803200003150500194002026240003a180b1502000520030380300c141012500c429400c07820402d603076155404101c92515140040c2509105454200205000340010003104051a005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33218530 1250 33217280 33217333
    0x50a030b0612062d1b180306130c09020301030b060d11031501061706010e10090b0c030a0906030209090a0b131401171c0305040807080a0c11090405 65
    0x4078440b10b5021030181040c10a03070b0025540e180d6690020182e4050409907500d007008880014141d04080290000c0079036011011550303c103005c5500710301030305c103074145800f0560003030141d074464a40440f809000380d186040803034042e00c42d01c001107210100740c400e80303059070b50101c100361050316014200104007501040481d60b009180845841c06d841c1845080f20700d152828061001e9414040c019066007011516031210b10582030421046a03031021b094102d03000309589000049064081c00c07030f0803440c03d400604056200003201d855240000004005840c40c40d40c7c1e00c8016607c0e00022000da01c202d528a660203104280414070312151948160a0303503030010090b2100042d003c040800307640b024104a000010075000400c9025005000010303048080e6000e400207a0a1122070f01c1e203420396800301401c16942e0070010f0100a8800110380c8038035041801140c03035101510004000c0b20300300c0b030112a00c04070320031001d1040c140310f0307400d90040c0c1d406400f4003101403d00c0c4900400d032442110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33219780 1250 33218530 33218539
    0x1050108041e0b0703050609091005150d050a110a030314090604090903020f010e0a0510110f040f06090905060310090204181a070c0302030d020304080910031e020301050a030b06 78
    0x3401c00b1034007006040210312481010401c8043c504810040c044400042046000705541c108000082c8000706d812029001c500c940020961554010a01a0010f500819070000611030020040c04000182000424401e40c0003610f18000d000c140840604284070040101e0503200d4004000c1c00000c0250201e0000549840c0c20103645180340300564400090075005a000034030540c0c8840c40078001c20508107483e800070100c50401c0c0e81c1c1e1036a20f1055400718070226a40341c04002d1496081c508030303100d40881c001c40d2611203480b1b10005070501e000e032042601040281d040001d841019000e40c5104003001005445060042461030000d00300d040d408a071b10a42c2c41300c188a20070044495074030b00d207001c1c003101e0340c9159140c9031409110340081c15403000d00c92403c8803000001e85c0001152030140c0141000350303e03a01d962403d11140e0280d0044030b640401032030000340026526178406d0034016015280780e01002103614000c81248020301071079401400c00c01041c00410050384200b40c00940280 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33221030 1250 33219780 33219803
    0x16060f0212040b04020f0a050d020d061814010507020c0a030b04030c020604090b0f03030c0c0d050f01020a03050703050a060f050609010909020a09030210020d091206090507080303060103180b0105010804 89
    0x340302040c000002c680484240149900f88025824002c032010020002922603071201030400b000146942032030b640c000d10a003801f1441d442009815004407682014002510095034101d02d0840b44c01000d10322110859880c00002984051000407007814810340645401845411920303604a6400c0051007a0b0910044150100047e02c0c1d00c1c0080004050301c1c8000030340d40625034200300c105e02d0501c054600c01d5100f80400706c60a00089249110040c0485d400710300840e03c2c0c47c0c07143c100300b120046071002d940f000c01c280c525150140c003c0e9228084a940c10080366507041081d03002c86505001d10b80b070301504030f1402c2c009800c084004001300c4005040180a5640e1044824140c0c1d0bc10b040220000b20305e00c0080007182050b4110183c4a155400644640f881c2088002c1082c90580305860307000070b42c20002d0007070000da03030301802056030454261814291242001da42c0c0ba841070b543d0a001900d000403240818034110041c0c407069501c05c0100d410350f46444011105c0d902c01410a5031201042c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33222280 1250 33221030 33221047
    0x8150306070207081005010b12090f0105071808030a21060302060c0a030f080c0d0504150e0c0306010602010c021b0a0e04060606090e04051e01061a030a050c16060f02 73
    0x2040964407410007a07005002150801c0300650801201100301e0354068103200c014040c041c0c8060035508035598032208903540707503a01500e0324035020101e55901c00e154600418840300c04d600c030614113010101814001101c59449103041e5907032203022a45000210310300040414a2480d1302a03404e1204148404100346483b074000a005900c50043c070742903a8440d00f01c07402019044400c0618071042820a00e256142c071000c0082140f10751651408442c0d079920004040007a6107254214042c1000c200300030758814000b010742d88441c4d042c01c561180c4a03c00001079200d20502806201d01e8141e4040e0120254240402c005a0a0070b805264068045c010108600001e20701680c801ca0181c8004211a840c21102400340302d030680151031804001d0007000089003000070421a00300810550604018496841e5030061200303070800c0304000c503041c0703048d007008800d00051402401c410304100b243d0344410180c1b413070610600300c8506003000d070000101c012075200e41c803200748051040805450004617 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33223530 1250 33222280 33222283
    0xe040218042103021b0606060703050a090911030402040516050405010c020f030607050d050702030403030903150908030c0702030c0a05150c0307060606050c15040b180c0d050a050d0c02010c03081503 87
    0x100c0b0800044c1e03020440c0c801880c00d050b21002e440000320701404460400c0004a516845543c0000e01446400600000e5035407040944000401132004200030180f050140044164002c0c2e90581c4034a05000101e0540400c4190345500443d0340d4441d240360900d003200568410002d0030082e64003040d210030070f41240e2070500c12284075074542d40c0c2d600c0c1e45070380c205c08210403104041c0c0300300c0842d802030209000003500305145400350380d040218801085d01200c02200a0300901100074000e40b00441806900c8140c036025100040c802c4040e16000c040c8003082c00605c020074400c0603404843e101d074801900c072440300104000400c1c1e905030780c41c0c10000d031604001e076281680003a002500000b101262110144070f10401d100f003480c2161b81c2c904040c1c503115100000a000d542c5140045201d042024104021aa5125001038000000f11009092a41d101c445649051b18103000d160342003404103202d005032455181d0b0584818600c92201d49003201e500200824407040c1031081c00745039501d070f0b90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33224780 1250 33223530 33223583
    0x40908040b030901050106021605030618190605010f0e1608090f0a050703030806060a170711160314120f09010e0409150e03040f0b0717030a020d05010e04021804 71
    0x1e9443c0007056552401a00910b4060b50551010040403190000c0c081f035075011030783c0d940200181c0d05040328107038400c280504140e110700403019a400d041c5c10f0201000480e4100504032081d012039072400a40e22025140c1844046131003622050b4500c54400d102c03401045d2460b008480c0c6011074000d42880a00c151500008140503245035201500c2007003019440580c0c50f5010380262005c1c0c0c00d00394045400b804071020000008a04552140028141d908c211103982c40441290100e4503111384036955074030040d0441c04107855040301c0c070503158182d510000d00c1000031810308981610302203044440e01c400e50004560750307041001c0f100080d2550340d224001d03034442c00d000c2d501044141040340300305c0d8111040110302c0100342e00181300410008980b000000308503400307200c0c029520481850600c0310b03d800340c007118111110102c10310015120325805407003902ca480c0d00c1040386989071031307546002510440d00291302541070704013001c1929000309036031340140c443c2c03807580e5411014000c01158403c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33226030 1250 33224780 33224791
    0x5100302090913120c05100c110a0602030f010603060b040b0d0f050f0a05070f0e0d0204110307021b0108040803010512010b040617010b04090320030c03040f0501080a0606050306040908040b03 84
    0x192030300c01e08107104030803800d1309195940d810b0505204419a4a4503250881d00c928641015030b903150148201d40118006a81401d81c1006e031100c0c0b0307103141342100003034005079281d0481c105020001700381e49001c1d1241006035400c2040c098141807401401520b594828200c1011180c0c46407505140c40704070303000e028090100101055054030b00704000104481d00100940700b0040050392003900ba640101e040c04001c10142d480030540180c9001080c050540c01c0f1080100c16000410000455400701d4240c801100307401c4a44d5020654200440300a801660054131a61003007004011500d059010501412400c2c0004141071350604001022247c0036400b042501120016403a8403410a106180040340c1c104c404110001c0f007070720b00a01ca1494080100030b1202c44a201507070701e0f0001c0040e581290001b01c2281d984544412695200c005907100b51400f08103084041403000d011070107000252205c641c1c0d168110340d5500100400b900095009448128040001003684c5000c940218402c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33227280 1250 33226030 33226051
    0x60a050405030615100c0f0803040f050609030a050904050402010315090203060a050604080d08040201020f06010308120f07080a02090402120103140607020316020f0a0b030403030905190804051003020909 89
    0xc600e0301007407500380040101095942848002260341c259915840d00800180c2c83c86c101d02105000c1c03814225160041a001d04017400200411042244240c0543c0140317104800b91107484c3ca030641166502d01861000b00d000c51000d010041c0c030b5007865808260320900525000c506c024142200e4042c800b000d822940a080e00001048020704141003030f84000d040a44140e464a403900c10039584401c5840d40ca5401c1000d800081000d5a10800c0030700c000001d0b00040d50401d50b0b603807406008540c400303800039020b10706030b500003140c482c10103100d14800c1d4015200e000b455500d40c030480000394407582e00564026801e00207041c05646a0f240076000c0c61240c0c0003021400d49040b200c0340b17040801000d140841d44104110900072243e051055200e5a05841c4014824107040000c0c40c0001640c1001c3d0354160088100400d240e415000591900c1c0544241c9101f001821085800d0300080d010150462000700001c1091b404d003c06800340c00241890300505040c000c0001a02e00f0383d00741d942e00c02c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33228530 1250 33227280 33227287
    0x60a03020d120e1203070204091a090304080c09090a030e0102071a041e03080d0905031605100b09060307060c05010b030703030c060b030a0b0103080705070509163c02010605060a05 79
    0x580d9005642d03820500c1c070445290100e500e92403503117552445a620b0080c020b54444d8646400c00441410850102040c645150709071b1804000130b0b41d49030070501c2100228400d05201d940c0508100510030700410b1624003502d05810079880558145038503402e00c9045101d03c0701c001414944546c01074102c0c01000c0c23441590707103180030000010b800c1c1009852035100425801003000442010071942082c0f1840301c0410600800c1c1402ca00754002e41210320680b891745110103041080204001000d524101d90400240380b101b03040c80010f08040f0b038041d4140d0300002080c0422401800519503982c81a0008100c1400d4003010a05101a07070f070046001c5001600c1d04010004280251007400f9400e4004058050044c4c8441c0c5140070184000303010b038100005e4080500c0030510651001c0c00014181c0081c50074400320340c100c280980412640080c3d0031103501110001d0355400350180d0300070751501e15161240b84070102c02284c2c1c0125003105565950b600001e080d103070394000e031031140040e0b12216103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33229780 1250 33228530 33228563
    0x3080a1806110f060c030118020403080414091005130216020a0314121206010509030a0c06050d0c0201050c0702090717090105070f030209030d05160615080106170c010305060a03020d 80
    0x1405640000d0f0301c50603040303281041150340400302030300d0450783c600074640000076402803080024850394001a04141c400038001c14803040c940c2c1206c05440b810758500b055560342002b5030742d000c24240a00d951050380d000700340685c4181c0741c005c0c0c916040104090003130300c0740b00e50001d206501107620844242e04c01c0e0f0000400160140300944e0410702d5840b01b94070b007050741411003464050082c02c01c0d0602c0004110081c182c0c42c100000501c55500000140c511619500050a542c0021450291850070620800029441802940d005000499240342011110303420450710900040c6050100000b16403074001030445030040d6401400402c00001d00b0b030411034802401e540c0c90800c045c040c1030040004002d03d0f10000340d10300c4039521901d4115125414509199241400304e003010b06417070300f040b821440b030794000c0c85118211800740008105065035001f020003030070380400320031140d50814081c8801030350107a0481d551006000741383d1080d1680300d90010350b02c50031020003a600d00d880440d5514 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33231030 1250 33229780 33229783
    0x1050102010c08100303080c0c010e06041101020a0b0c0c0102090904060f05060d020609010c03030618060e0703060b0417030d0903230f07171e03070305010b070c03080a180611 77
    0x10880d02c161602158030300c0d040e101c610101c480d1340310080800c041407000076032080400c015180400d18103002408190b45100c101580d5030026901500c003000c42811010307135580000b868003140c035804400c440305541c81d441021100c3d0801c40040314195002c0080c00d0003a0758810303e03e40b04a12070080051840394070106907048480081000e4000c40c00a003143e00582e544005688010800340380900c01c00910346001c0b809040d4550002041c0c003180c0942c2c034807001c0e141d08000c0568030501030072116a961440c0440c01d44a05106210884100b04424032103042100f5030401840b421004803460200e00d42901012100300290940000b992201803d450108401c181e00c00b00c00c000031014240480d0740000c031500d100e103d02c014085d0a620300507620601c03c00e401d0b284034a00301c00c00780e43c00040e02e407007046065200719048000640350100104204c003603201900c660580101d21115040e0a69840c108a03510004c50740c2c0134085100f5191000040c451a800043d0055517070701816200d5200307030103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33232280 1250 33231030 33231041
    0x902070b011a031b07050f01060b120f01050109030807061121060409150b0a151112131505070b0103050c0a080c0306070c0309180c080601020115050f010e0a0e0105010201 75
    0x1c0da5030000304144601c045000c84071341d21905040c00c1d20342d65404149001d5250040301d60b200052035003030020000700280f60002a00d0104d14115080c1d6103650740d0056204108403d02a40d4042440d4190500101d10381501078082a880780800250000d00b0b00204032150304041204100401c070400382d20a003d2120b5546030f048001035906002800e542d41c0c0314800f45545440405a1556403c100191540c489607807034010305107030304081c070500c6010800030002d9401c148044e00c2445100000b0550445050403a040c03003180341004800581032090b400a6416081b0208040040c00e0005c00003013040441082d00940c0b1800003040044600000e10805881640c0041010b8224294040e000d0700c001c10590f5100c619480c0c40c0c03106000f50710b030603a074001641d00f001c00008511000c4100862007540102c0c0700a0392500c5645282d84c1d100012400c3c2c40161101a588013110282001181400d06800700039507014181004007180150201d40e01c21039650014181801900040004c0d580a1098 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33233530 1250 33232280 33232319
    0x1a0c0703030c0c02030c1207030c0b090102060f0c090603040c0b0d0e061006050405060f0f0307090801110304050a0b060102070503030f0304060b09061507020103020f04030f020f040c0e090a060902070b01 89
    0x1031030603050b513900042e860300c42d04c50007240107a84a00300d50074101d0041c0103140145600517500c0d0b042e41e0722081840082c1d04400003179400361007200b0100703103e040c0e006c041520500807030107882e142542000034030200f9013004d441128401c030707180b2010903a204000040c2107102d46500c4006403168107000940d150650141005607107509900c41400816030181c200c1d0181c60050705ca00f5541c001404204280f07108040a17000540300c00300034041d885a001c000300b01150b00d900000e001852501e03c0d03100140c03105580003046076203e103140100007101d40306000c1d4020320500545170806e59031000300e800c66100311901078030b4010000c10441048850311454010440039034080c110f80c03606d18085201c1c007049000b0b91458000c0881c24074116031103034040380c0840c000030424644450b501c0c0340403040c0302c07414542284180f60700c1c0c0c134026076801d1903c01c445d030055895880120b61040304062042c840c074098954140b8a072201d00101d0480381c980002c0800901c56005552590b1600e6030355515801000036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33234780 1250 33233530 33233537
    0xb0915010b0a0e120a02180f070201020a0c030f1106090a05060f060d0f05010213090e060915011710020c030306190e07050a0c050a05010501060e03060105090103030c1a0c0703030c 79
    0x80841071907020000f40000c4500b90390400f0108070040c003440c94941840002540301143c6030f2040e1031180b51455503801090f951241d41c3c1c1c1a02c40d00c6c401d03800d0307000300f0500000185909060700c0c082441560710041c4209036040800181c2c1e040154a41400b070f040755800b129502034030350203007040303010041c1540c000290031703603890142421130001d070b1001c030710040142801b19803c010009005084d41152488044400f060101d50340e50410500a01204204400b01e4045c09000660010000c180b149059200b00c08003042d0760b0070010b140c022849182d455440074400c004502d49154030314070043c080400e000c0025903c0e803800f0000c009110240c2120b410050070480c004002e010640c501990f000152810490344079410b50ba011901c590550601500501c950400c5205010066204a0685003260340d251281d405040c00e06941e000d007840740e1781d04207a8540040010034400c01c0901c0100784541030802641844102d2102100d80541e41c034240440001441801c15402d889283c03001059400e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33236030 1250 33234780 33234787
    0x31b0c13050405070801020403030207061101050723070203100501090b1909021606021201081603050303060d0203010209130b0a06210b0609040606090306060b120a0b0301090b0915010b 81
    0x801040c625100030004501040e1100085010070409010326409498100002c541725036803814025940c0d4030034801d2901151401407920101f00c81801154800c40c00743d04c51004500381480d40144c01589d00118072480f00041c048040103039428049041c0d01d130500300000c035595060441002c120707066081800d200320b032105101e0728296041c43c103080444a4038040140c880900130241d0030301803020f0000424462002030082503d90010142a0507500b010007102e20002000c00741170b140000900000c0c14a500c2840050b00900e00440404070080c0702400141c1000c00c81808175540e0100840d50b207480c030f030720740401d10900c3c00c03c85007a4004000504d4141e4a015189134020103c11500b00515003860720344100c8001a204c140c1115240310003d4000c0207444c0e55510300405070b0031507000407207065003440d000248503080c0409541c0c03150010300c1d5500d45511b444000708024416280780c1380e05035490b000b4402c0403070310340940e0138481c54642000d40840c201c1c840700803c611405804c140301050303052 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33237280 1250 33236030 33236053
    0x9060b090310140f04020406031e0b070f02251d01150c02090402010e0f1504090b06040602060601050a0c02040c0908010c17132f131109040b180108031b 67
    0x500c1c150003413000884650262a203002140180c200c035000501903110418079414250b40009140a44500a102d200810b49511004503540c90711440a400140d1003000009402000c240c0d14600403040e07520040e510f65661944005103210800684221034030071401003012030520b4a8929480d02e80e40303081d039842010350b800910712420203840a4100840d40111600c01d40b0f40005074600b0340402410200980141c0348040c120350301070f00030100300604184441c01241450030039101540c48640180c0707450303a07a0400440789508014601405c012000d0300c0840980ca0b54400c00b14050326659600507080d0810305c009081d60b0716126968100003002100005450f5001c07561a089000f158102c4a00c9485040519481d19500940155662410309140e102c29510707207030b8009140e00342d0707542d018030a04903147d0301160404500c018020700700308041040c0e4542907000c4041c0e404001d1491a184c4c0c26040003c8080a0036040300149500000d05400a0040c1c60100388400900e80014a0b6048d0748 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33238530 1250 33237280 33237311
    0x80109060501050304080c030702030f0c010e0303070203031206030a120306030201081f030605060f0310050609010506040e01060813080c07090509070f050904020d050d02060103020a062c0a09060b090310 89
    0x2030000e0030704400402d1f2040070a86c140101d5440c5a0018202c40c180b036017660410740c69040d941d90b0796001c10f2a02d0210b11450901005a4140980090245040448075840c20240360f07002806950b150150300c1401000030407400781d00030202c0f8a9035000400600798070024100075000342c00c2e000c041c5107500b984103031202c01131411030030340e9800300021400d41ca9400101c0e50311001c61481941c180604500403a41c0581c47d4011031040500310b9620304035980c0c400c14000c6da8405c0d80148002c0c08072000050280600419060341c128250010306044c46101d81c031030072201d8020340903841c2250050305080001101d2800b9050f0404c1c0080d0280a10514029503124034500f81c0c070a2602609402c00013400399601e00700001881c80d0002d068801d04105408001e46030002400100e00c074604400010803c0762043c080d40152a83c80024280c1110110030003050740803003900f2040c0c1c04207607a20042810030b02c60085400030642c03080c1807074454008100b0103060107002c507000d00805140081d0307007601070b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33239780 1250 33238530 33238537
    0x30f060e130215211504020906120709050406150e03010b0d020d11060c03030a05091603082a011d0109020108010509090f03030f070210090c17030d09060b0108010906050105 76
    0x18100d90012084440f409159180c0c001d014140800001c1d0084014041d2030f11500e65118580880b0100009032161041100700d003e044482904040107210700c0ea02010f11240b09500120300b0704150380000d50314070004003078450307035002080030703082d02c882c0e80c201c580d00101141107444040700284400d03c03644000c00c040c9007a001003e40f0494040004074144000b148906000d510301800517951004c075010516502d034070513201170070000d00d020001001c212020a084030b000c4140c0320050140c0d890764540c1c01c000d400918180d240341402c005107044581031201c850300440943c00c0003050420f1254446c9100854150045d1007613414852054010b0380d010581c6815a881101d40c00e07a95281c0b84070940c5400908009040203100000c10310041508104c1c42c1441141a5405c0300e8200800701e540e0f0040e640d00c0c4400910141c80883d0030702c125401141c900c11201140c004807802e0401400e000313030565035586070548006550781a042050b50340302c0565400f411484605224a03460840020018030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33241030 1250 33239780 33239783
    0xf1e0b0909100b0105070203010c0207030b1003020603010509090316030f0e06070c060302030c0403050106030f150c021506010201090218060901060906020a02041508030711130b01080411030a020a06030f060e13 92
    0x3c1d40c0d039031040403580c0207105880280f60094001c011107220b01402035592002c1d0701054602004440c000340c04d14812595640560340d0107800d5130b06517440c00c02440203130f140203044100b0a02050280c188590021684d590009000f0385e1842300740041c428010742840d003102c03443c1380218020072820b0301281c03002c80c1040c00c55000c0d140c0143d50303a81d41c040141941c002c5410080040d42070950000a011010a00d001058000c1c1c614404038130003200040f085030b400a600802582102e520810140c40040c0c03119030020301800007148030915507002034107544c0344041c48220342a0240074007802d405c2c0008030f980503040302c0c00c01c8800c041c1040c401954600c40303404002d2245403501c50300c110515002c0b040000502e1070380e04603a1158072030f2814000c1040d05a850b1409000d0003d074030a01d454040c003d20b40303400300c1038581d140c00383c0780ca450720381ea48645649541d4142c03041803152001070b101c80260200030001e84d94001400c0c1c80352040d00c41076a4480d808070300502200028415000b525500c05e4030139a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33242280 1250 33241030 33241063
    0x10c020a030f11030601180501060e09070c02061308010501090e0a0203060c030a020403080a03090302121801030e0111030c1213030806130b0a0f0806060303040f030b09010f1e0b0909 80
    0x3082c040ca0108182c145040c44035400d40601400041d0a0501905540681c100c100781480980e8030355400700d071507844540741d180c0d0000462000c01e542501038a89804c645e40040d00f07071450b040c0c00c2511030f440030000d80c8c40700390302c2e81d034450040080142a01c5880e6011070160003400f244001900040d6803694050001c85101c003000000c0b401d46041703035040324000d50740316200c0383d107a01e020768000c0e0080000b43c03800d40c0036000f000c81c1c401da5094180119051018003540c5600302c22402001107004000d001180d5960b50341c0c887c0c00c1d49001491202440c810420796000a943da00781e0400035851704000341040b41400b1000d00a132000a400009240e440030302918098408031b0f6041d540c070b02900c01190155007002c2807e40111b001e04600c0c0092007031303448410031114a074841e03134140b680d2442284608040c6440740c8030300f40000750b5010600f07600f18107104004248000122548400c0b0345028030245681c4001c0032074661004203038010100107940403a4858044e19003003503540e440302100305204210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33243530 1250 33242280 33242303
    0x6010902072111060f0f09010603240e010203040c03020a0e07051e070605011503151212020a05010203010e15010c11011101061a0c011401150807030204051801030c05010c020a03 78
    0x40502c40c190804048034000c0c110790305030805d004481c4041100b9101008480050790000b90908014001d00040300c1c1d03c6580c00d82c00360b00d07407000345660211a01c3c1902c81c9546904071600c88100900146000d14094640c0074800c514510400000e42203583c806010044d0040c20412800d8010040d00c2049601c1c68510b480303000c110407085618851200e00a01071860f100002c580c40340079a00c01103181d801c039101044000c02c046c405207040c00c998442e80307040c442800030043c000740b090000010094100c3c011903a4216040c5d85443c01e9030400d030080f4989000060030000d0728000483d044c04410000c0c201460003464075112011004114000d450511000701480c20301410258400b00007060600000000c401410300700a5035588295400c280c40e60904039112100c80031040c490f0b040312004280c1c102d130b03445041019500300320010282018580d0030b020002d4a80c640800c00c6c601c0a40070740c044011136042d0f01d006052207859400540c100001c078202c60300141ca030304c03407a40181c2c0e40241c100400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33244780 1250 33243530 33243593
    0xb030d0c080f0d0f0903080c0414060f040e0906090c010509030d08040510020f0315010e010804030f05120717090613080702030c030f07090612020a090c020a02030d110601090207 78
    0x42c24802d0b4044401c2e524030f0040c80800e603001e103030700a00c00503119689180d00340e01c91811009150103540207403507091500c040a001d05207801d0740240001d855900314141019074454800c00c03800c10407146003150b90030400401c100100144152584003100342001c0341000c6214004c03a590389158031103c82807001c0c0f0008078081c484200511188540890401e40d59520002550b1000f40c0090760701c0540940c11224082041d8018080460040b5060759801c003a5070b41c4e40c43c01c8410749400c1c0000400d00508001c80c0280d280700301040d5104404c90348401c00015625140704451500003010b02c100e54101c90180910554560690b0042d980c0140400340c41c3d07105400000d06001b15201000c2c0c4c903101e10658501c1c000008105101181c54100c4100030703071680c84e0709440300c0000701180254070000d002e009100d9100d40383e0001500717940c80d104480b040070103640440e1030241842400d1002c0740503c845403c04000c00c1000d00e0140c121241c080d4246240c60356007560003211075002c03541c000c600220200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33246030 1250 33244780 33244807
    0xa1b0204090501021809010e0c1e0403020901030807020102160506160302010b03100b120a0209040201050307030b100503160302070f0224030103060516020d120507120203040b0105040b030d0c08 85
    0x6150716042002190f50340c1120800e00d89041111205e90300400c00ca000004080b6405400103109a8000035498608144d040c402c144031080320025035601607041c040400503031200d55440c2d02841c8204041640c400a41c00007a181108010000100a010001c28002a2034220949250022598815004070504c1c541039000d40b41141d915505803103000c21105140e00f40350041040300000341c2d20706039135040c40300d803068490b03100c3c03c0c020390810003e80c08500154480e10045501045138900001d0a10800b400100c10503001c40a050000c2d0002c0b0030b00508440c2c084080e0640740c0d282c10214504803451340c03801c44070700b04240007a2050082070592103084406c580700011040240c40165a40d40e12490490010407068449880f000c08482000c5150740c00002c05000c8035109803641403040240640c0c00019047c001e002e00e082002d08110007080b40c0031030002e18012807103042e844d000356041ca402c2c44110b4103c21a180d220307600c00f103040d110441d0410014599550889a000d80d180c4a101e00d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33247280 1250 33246030 33246041
    0x20d050901021515011b05060103150b030307030e010f030e06060d03031e06210201080a050a0204150c05010509060f04030305060613150807030209060405010507050f1617030a1b0204 80
    0x21407103c191002c011807504030b0b00413a00f400344240c07a0103946031141c040801c4d04aa100e01c00030280c3d440b010040c070200b4020020000c1441c01450081103160b15200400d0458201032002c0f004504c0c0045034181c40d42e013003407403580700354450304c0d0400115070141c80d150340e103400181c8681c2c0905100c400c1c44043c148260806a0302c010701007001c5d000c085450031014024120344c03181c400c00a80550120350301c43c541c840d03041c140d01d40503074440e585502c9181c07240004090113804454010381c20840080c0f1401c59200d4171a03044400d0319407900b841e085092490956100a002d0120b5802c00d100304008007020741c42d103541194151a000809035a610302040c020311400c500c90380c00c00d04001000170f00f1203d515040340708090076591a80c031525050030039401da00445074100e9200f2810300003480507500c14405841058003801c100c1b106007850380081d5041c18584644000b04408690050101d05807200c0f400201800c00b400641c40c0201c03005008007102c07060020041d420020111b0b4030159075503500301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33248530 1250 33247280 33247303
    0x60b030114040803010314010605131503061815020307080c07051612060e0f0705040e030702060403050705090108030a020703060c020f160f0501020f0a030309020109170318040903020d05090102 85
    0x1e544041c2041c0c102014035800921040710303a8000340700c004803448010702030081100e1000e403004941d211882040320181a40903060b41c5203202c02940080071030b10381d02800401c60b40c803801400c40c50046003410482c4010140707840034058010001c0c00421544401c440d035100681081440e00e5086501e04141032800c584000d6141c1100d41c9400302c0c0108200310b005501a22a500400c4800b80310000c0d40e4594588510400003500300c0c107402c0080381010380080c5410302221040d83d25150b025030010342c0c1500540c00c03d07030b41544048814000b82c2007404d4000e000d044d10100550428481d070b40700035692801800b0007418581c80345081119240200301c1744004241d40701c02d83d9841411242544c014881921508540c22060b5900203a01e5001117400b0300105100d101402d03a4140302e0300c09030050100c40f203040703041140d1000009100801c5001840c0e0001c4c2c0103010319540c400124603c0340e20038a10f5003003442285064825030000c0c0d00041c0c9441c09501030b080150701c0e415600e006070f040c9910310304d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33249780 1250 33248530 33248561
    0x105040e0312010905070305090604050703060f020912030a080906040b0402060702061b160515040e130c06020a05010b1f030c020c100305090f030415050304110402040905070e0f01020703060b0301 86
    0x41100d1203145c01c410720031000b0303560400481e0348200301c485c0c0d28a1b09550142094110a500307101013801c0340c0220b51056481c1e5405403402d10014003096450100742c0b54502c3c2600041346445101c0d500c046179a0b00880404020b142d941819116034800240c0604028803c06c000100c600c1151150b1041e50388206682d00011604045886099210300c4070f82c0402d5414141c640d0003103024a0950704481c0c0c4c0c0f1410868041c2001c4c1084003042c203800015000b92105050000c202c400503254404502c040d2109a028040b030004505c1e00c9425901d110301041d200f00400800d00503408501c00100c10341090320328020501d11080d0340309a04101c400f01c0503d80068045481d001d90a41540005000c2c4140904541c0c01511985080341c8a000700d00403122403160510140008c10301c0b45000e10740250040c0443e10f0003010000010b070032a409544541001501c0d5020054159004042440c45500603603e105a03020351000003502d5101900000340704070f03990b130301c0300e401501c0940c0400302500c500301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33251030 1250 33249780 33249817
    0x70c0302040903180b03070c02060d1416020d030b060906030a0915020a080903070309030f150213050112060b0d09080c0d0203040e070f020c01120f05010e01060f14030105040e03 78
    0x1c1c0100344401000e81c0055400034940001105c142100449100c1c000658405090313042d10303420811664441000d9490460710340a480051100c0d000c2014000d414020040ca001c2c40151806400c081c41e440302d01c070605d85008940b8159449070b004440344428125001940c9035a0030440700024242c1b244098102c00080c032008490031025030042c0205069621410390036030f03801c85001e40e02d10030044020002108068108001421500d0304503140744140c551000402070b00c0c540d08100d0300b00d607551030580390f4612002c0049503001310142e030101e0081442441014249110030780d1500c580705c0080314030f41d500c0c200395050181e6081582c0101401800361101441081002990384c1c03c030703002d1046a01c0c1510042255940109200740c4810b4507500640340302040c4c0740066807034042e00c141400d4480d45031706100000303181500c5024040c02031004c4108a950510000820b4101c04a03c5101800050b2011704014068501600c0c115030089402042540300700e202a8110701a00122003121001c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33252280 1250 33251030 33251033
    0xf0705010905010f1125120c03020906030f010207050c090c0313080c0102070812010503071d010504050c0702030610060f03020c0601090b0a0b03070c0303200a0f020f07030803060909010b0312070c03020409 90
    0x200006c100759100c030f03001692151201408502c000303540000a04043d66043e080005051200c0c24a500180003000d845a0441040b1100e09903800003c00302d5a03a0007070a0300709000e1800b40703401600311803c040064118902003460340d141640c10b500181c038810000c941d081d0008000d404480b821580310034100c0d203641043e0030000c00d80d0380c28040c0c0b0340b180c02206000b003003001c13100300070715400485411111030300c2c1d2800c41072100a00d805071a050140508000313101c0035880c1041254001d8200140340d990043c5403a1008088401c8031030100201801004070007804e0302d00040311419502c1e0110005008170001000070307002f101c0b40d40800107480e008000c11589582040100b46e045010f40c400b44080c0102a855140304404001071a000700802d11502c10064442d401e1a0f0590000b801150f00d011003450405252402541c412203070310f030b000002c000d09420000c0900c0d8010041000070311088400c031000a07101e8450303014080503620003068400901c01c081130503200643d0007030400c01174035209 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33253530 1250 33252280 33252313
    0xb060f0a120c0909050d0f090e091605010201020c03040302010806060706090318060e0d03050a0917011d06010806070c06110a090305010b03120a0c02040e06010b0a020f0705010905010f11 82
    0x1e0840c16210918980c100051198081c080c1c800c506510401800f00380481d1101070300d2286400e126403080080d480400f041d402d202010850081403444020642c1c8172245800303203240c807c99000300d811a401441581c141d001c1c00000e84058030390900f0001415a28036020460602803a200600f43c6403c00280c0820325070030018200008c2c84e4802c0054030503444180550f09003d9250226400001000ca114080381c8110044c11164420746804140199070b00985001a8000c1c007034103a00c1e0f503640101104440c0c0462100e424031021030040c0180d580340c00300c05912800c0007041c000c144940840000c00300080c980c020441400c92080403515400c55003c001c14111103408100ca5540c68031051141c54034001481403084014545020b151503006001210090016182240c10545071540c1102c940310030710003280a010341d0f140050300d07000c214200a16051015403982c0381c40d00203c500b404203990101100007034074400c1c00c06201d8041155012600c45401049000ca10300518204070540d125 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33254780 1250 33253530 33253559
    0x21606021303020a060e01050a080a02071a10050d0b0a0507120501091d0a0b06061b03040305030706050c040e04110105070609050c0109090204060e040c0e1801050405010614070b060f0a 81
    0xd44109081316224034040e1080c0b00c1e03043c191070105205000d5264182e01c1600c2c0e11f03900c50041e0801504101da02d5a0346032010f4102103402994007251010480000104001180145402c4428108601254583d17103c10403010b840c8009691301c86000440c1c45015546001481c00c042104224a6039549101e400a0003220000c1d5620002d0404030b410700038001a02c00c4100b5004184030b02c02c1c0d10740c00304000d066400599150300049640314070050125081c4040c000840c003910140d0f030744100a1818a0464100914108901348103000c1071101c03203d20200198015800701503074031050402c0d00180c1d00e501510340c0040c0524100494041040340100b100703e40389100b85c80710591592101208010f81c0104e00441c000618482031041940c40c007908491003000c0d280c02d2481e50790070076102144800c041d0075003968207004a04010080707170030184180b41c014501d514201100319494102d1441c1c0744514840502403420340004a045903a0f03c0102040005c402000f000390346980da11a45103440d07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33256030 1250 33254780 33254783
    0x180b01050103060b0307020c040903020f030409050901181212020904020406170a0605012708030406080702070906060c0807050c030d0c030305060d0206030f1504090305040302130902010e04021606021303 89
    0x3d00300350000403400001e00c141ca004500e1500680300490313902061000030802d00302d0076421441000200e5424003802e00050019200582d00032480340303030001000d030954458014603c40c025240a440f80411401c9034141025030941ca050414840b000740700d50b02034040d201c1c666502601c00200084d203150020805140c4200c1c6011001e403a950310000001202c80510420f408902d2840038101012507002c8980180c24009012104907625003804d00d1454205030480c40104000a007808502c030b40401014008100b00c1d00280051420b0a0000704a141c105000610003800803c044003000b00500042d00b1050000d81215408450b01b04001d001422488080c1e0100349014007041c89400c0c1841078120b40b43d0040e20262468a51b100341441044004100030844820441e07403901990317035401030500c818060368801e0344039030550041254002d040c41a9810940c90022940c0050760054850304185004640050300c1c1d003c0120f040c82110003902c0d0013406c3c40d02c0001c4003107890001c0500e0006aa = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33257280 1250 33256030 33256037
    0x22050301140405060601050f0f03130b010905100b0c0312070306061103090303030f04031209030504090e0c0f120c040f02071202060f04060507091d04060b010c02060f0c01180b010501 80
    0x34036211041d0700300c0081074401501c95040007000401c1c650180006100b200e03404c26280385415a03002030020150415038181034120010f070503900c2888500b021032402741c00c0300b2500304018245056905048841d0b40b040910007017000c40c500c00b0380750007401a1208845030700161040d600d4819001401001a0301a19000c94410f48585400c0c0d00b0010035102074100260045296440e11340442e40860710003001142041050071251007038045500451034400d20945803540c64600703080c00001990034200c2d20b2f94140e400300280109036030342c503040041a05019140c0c0030751a00c01200050402c104090f6240c3c1290030038004220302901039000740010b5004007099054140309035400c80c0c440c44152a242c0c1903a0005001c00d000c41c00aa103c650010940d05041f200e0030b9031000b5540c0c0f4604008440e03400d4410850400c03082c428140500000c4000910b00700a40841560000313001d40190710a5260402e03011030183c103400e2003588201e400010043c47c12181d110a40380650104200b4010766000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33258530 1250 33257280 33257291
    0xc0d0e0d08070912060f0603050307080c1c0206060d02031c0e0f010302030108030403110f040c03050a0501080f070b070c050616110103020319050403030605130b040e0a050d1422050301 81
    0x3910f10030801403050f02d0b0203034080c4030074141903255140640154a00410b446a44000020024100304010480d0721b20a0400caa11a070f03001e0f5580b414030780f4a0300c034080c086004040300208580c0c003040d4241c0c0b050088440c100085007500100b450000b0a9141003003490b10181c60500703050704000c05a620390011204e1500403581c40e4011000c2c0e010a120301d10075980140700038070009900907003120b451800507181ca0400325a000004042e00c01100f1084007195555081c8004802140606405004100010041c3c1e40390345003c5076075051b1501c6401031545011a940b410004100301c0709005141c020015900e585441c0c021050b032901c0c2404c00ca80140050042407455402802503c9c030501d81c1c05000d128400c48880c1c00d402070800207100303c040555840c408210340c1d0303821154051500380e458000801e04048800e0108a86000492506941c00402100001a80052802d008020341d103040f1740c0e4000060100c591030300440c26030220898440d03d541d0360000004001ca01100d1084000b07104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33259780 1250 33258530 33258541
    0x140a05030a05060106050a1b0309030212010c020d11030d0614010809070e0112030302120403120e0102070f020105070c031208040b010b1c05060a050405010803030103020103320c0d0e0d08 82
    0x381d4840c199001031182d04010010440c2c1760140016002039041420948000c000c1c0d03683e03040d0402c9503541704401044140f0428000c0d402d00544501002e2054030003089a64010f0802a54510302d1042d01d20800007105141e59440f603082c0b051398900070f40810240001c0d51a1003004104074200140c66001a500000042340d031800046e00303c040b50421142e8020720b07406d0a00d10814000c41810582c00d02d03070200b140402c00840c0c0184613200b00d0003030345c50014078405040030348207440048652705aa03070b006101c07250209a144169030621307942400d11703d0340c9a08914103c070b1755035105e50002d441105000e00d4109100d41020031140f00798490032444266a032558a10000d50103120540806981690341107810f25850340c2c030880d00b1000080c4076019050381c031000101034440981042c4915000440108119601800703118413150500a0365241d0108521403c04544280248004042c01560104030090200c070704454811384012400d0040311070484034569244040c804840018058900080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33261030 1250 33259780 33259783
    0x10091a0405040b0621070302040e070906140c06060d020a08070306051e040b07031a12030409060b04060507120311030f04020114130308030a02040f0303021b09060a0b22140a0503 78
    0x8801c5c001030f06040e640c0c1c2e80c0e0150011500da40040608061660800c00450b603160b004044512602003a62a020454107010009150600440000391040d106029400e640b120105806622110503105400214a0740c0002502028503600003103842c05003410100c240603141d00030501c1504d1030b242c1c0f01c034807185590002144800848000d411160f120000c0b03841c56200350045a80b00128840300342e40c0c11040700014000f103101c52001d07441d0b513000080422010185000f542d0041c41c503865141e00382450322102030b00f14130466800801031341860030360122140c0207610416070b8418101d800e94413031500040c0562040b50940b8180d01044003100115012411102240c451010850141d02d0051941c0c3d22001560805400071a071240c003840b001c5036901550034030384001e50181e0700524801c11b01800e800502c4421b070b105036028040150070004503481309c0210710225511070704600c0d614000c01035204020040c4401c084500841c0c00d000180c01c0388500404021442c0c103c40c6030484a070b9a00405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33262280 1250 33261030 33261037
    0xb0609010509010501030b0301140106020304030501060b0a02030301060f0203070501050a022805160f05030703020105010e0a2702010e0406080303010602010c0c02031b0a031713060201020a0e10091a0405040b06 92
    0x1c41d4024410b40050100d948a03400030180c80001400118411100e0b1001c0000102c0980050005900c0480c040042c030209000b083c0085c45410310301c030310380b42d11414025101d104c140070b4401030014440005400078030030011143e945402c41d00801080c00d1584141c0040d61140c44811600300f00381003c018110040101c4400182c9c0d552502e82c41c198a0310240300c601d0703000c4e034802c1e40c0319200509904040b510910041113928840e40c0001106d60410941c0310090a01030001521180340000e05100001040f10b1a21000d1000c240282c6403091840121030001c8840c415681050500800154994001003c0c40c1078403a250000c0c80360000c201001c80361601090006581a40300001700135442c181c030310070481c0307005025080c4145c2d9520b030388030074681000c000741075011070320005500c04030021440c4141c40038191910081d4601160681c0003081e03800701d0b0305154400d107007420f102d100403030169609000034000d03030211003c456406004858960400e119581c007071411305403000001e103009400c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33263530 1250 33262280 33262289
    0xe01021501030605060d050303130b0115050306010311040801091103060a1a0405040204020408030f07031412241302181504090b040f0603050109050f060c040b0304050703140a0b060901 81
    0x105100c1ea1860b118040901400750502d03400120450704800858800c0c00154401c1106008103112046149003200d6481c0d8142d00a00518114803d1051810f500000320398000b0030074170b004540c5a83c0d6010b86031091060f68000c240319880e100c41d00c0100008980d840403401070440c1942d0951f07070382142000c1620000003081c00000c1c140c41844a0390310f0640d020036046800a08014101529041060710b107038403440582c004c6240c0460020b08150380a41b1031b6000a605c00000c0781840c00030b28400114a20152000c035040d011b10000107009640e940c00c0a480c01c00c020075607460340100d1030a0720000e610001d018a20b10b84200444280c5060245030301c2110760203a00c10314640740c64465142d00900202c0c0b41c9660054403100c0c40300800c4000d004a102a500034000066a031a180c40c04030728006180741da410a51f0014401c0015050710a4280d0b0120784403410f0103507403603130f07185404c906000060b08000c0c03000200001815900340001013403c2850301c00c0100050701e4503031070204108040240718 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33264780 1250 33263530 33263563
    0x9050d1205060d0f0804050904080301140a03020105160302010e031b010b041a10020c0d060615080402030303071b08210a090816060902130b1306030b060f03031215010e0102 76
    0x4464002504e00c81075003c0144c06005043d0600d620b0b00d002492010342134900344d030420700100041c0501d24a480c030340a0f4000b41120703100e001901d10350005c1d250740191094815a807011850b11014503000b900075505403030b51041030f40d40d00c554000c2c0034829001950406070096103441956415801c25229450000030814981c9001d250381c1c504002c0940308c0031034214114007508011000a45030000c00c078012034071605020491500740120341003e5094940c000b420484820b0600016803004011a50070900514110142221401d0644500210090000c013807040004074501a03804214280104914940c10f80100703485d201e510358103071203544002903c111010000707420f100c205810a20512840f0707110105081089800040c0524120481c40740869201c082c4001545001a4502c0b44040c00d01c0d0100300c00303401c6032540e2881c04002090240281c01051004103503950400c1922425012440901c03643c0c6045885601ca520151a085020400030105040035600100f41c0d0100305402c1c5c42d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33266030 1250 33264780 33264799
    0x9020a0e18180f07060306030204050606030403091a1b071406121611010e0f070501110a0f020613091a0a06021b0609040906021b0604031d040b0409050d120506 70
    0x100003141c50380800b0300880b88110f041e1070b9580e030000c0c041800101407a4030700141c1980b5600500098400080030144108800c200b0000003980010726001600c4100e0420001d13410400443d0513540324040d10000740140d551143d2030103000c001100800c2d038406800c0ca224905000c0140301d4103004071014048140101800580300d52100390041c1d081048500d000c1241c102c0c49140a400c48aa805510780c40d5000b0003a1040b21810030000000200020300c2c1004019019130400e41d00e80700c86540052060310000b45e050190741e00c0d04161041c01c01050440204643d480b01c680303004003401d81005c604840f118102d041207180440f140c108840d6250017030903820340d28106140c80701d101810784948c000c9041c0030351045a11544500107000780704040040e9210385a203194800714031108902c40b8540c0c010420400041d504c540c44408504808000070070815007900004d000d0700351a81102c0d0010316041e200c800740b100000d0101004c07607494940d1103289801c06190303026128120741307164200c034149 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33267280 1250 33266030 33266041
    0x1109040b0a0e07050d06020d0501050f06070807080f03100305101811120102030a02040f050a03080a0c0804050301050f0a1401050f010509031612020109120309030206090402090a09020a0e18 83
    0x1a00203802d82250001034450440c0c80f4400125844610001900c0e655804250100b80c40224410b050260004440b52034200c01084001101441090001400343c10301140403030401100405642803030300e800303112a0700c0c0d15203044100e407049106d120640b5240700b4034a01030761a842d07500c150441030f5018545450914520740701d21805200443c080d6802407941182d00620f00802e01c0030314003400d402500507903039500e0b10050300040d05075504140e104811000003000000d0300001140c51b11112410b05082c440c2c0c140c1402300702030145501441d05542004d0802123002e0116404901c100200681004003e0f20074041500302a000d005190300102d00c29178060b42c540c014005000d02031801812039138450800b1400504a50940e0b00807034201c0c41d00040c00b411580c100204802034000c45515220f81c04891302c00074000055032002a01404c80004c0000d601c0d01d6a40484801200280034100c0e03207640ca50006000790320a014500c002940e01c000a0703414644908c0c8120390300c281a488500c6503c0f035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33268530 1250 33267280 33267301
    0x70e0408160f050f01050601030c090b030a051b07112707050d0e010905060103020315040302030d0b01051612120e060c0c01020702030d05040e0f07080a0903021f020301031109040b 79
    0x66180540b10244a142e00c440020002c0042c00380c03100c1c1c1c200010545007408000501074514100d8000e05108052400b4041400c4000549134403414000300407680d515407408100c403075100a10032040610001402506206900100d04031010041d41ca440c10081c0f001c01520052002c6161041d07002c0c0140007040340144100050300920f000d51400260029403072410901315a20400111420f402840042007986020b110030f0002e40007000d0315240d40d14141d94025101e208124144460a98424100150f41d1045003a60300d410b00d90004c0404a041504000301d0058050f45a500007805420901a2002c6140500c229040c0d00c00000d0640747ca408021084641001408048640d824031100c5c015940420402a60030010b4031000d994070b00303141034601108002028429204080740510440940c409290780c1d009410070000250040945000c84c107140c01c1c107841c0150140921001c0103144165030056049910400480001140000c03c0c041744c14011034001e070041c0c4087c070002c0c131605c94 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33269780 1250 33268530 33268567
    0x50327040b1c1b030609021005070b01090c020c09091b030c03101a06160314041d1f0b041403010501081f02040302100c05010b04110a050705010b090702030c070e0408 73
    0x426400c0d01e00c1401d4650341608003c01c6036000356455034079440e02505506208000e00a40702080c5400e920301141c0d602c9082580c1c2e410300c204100c09a607410b0004409200380025100484000c0c00060310341400985a9901c000219080c1080c2c203060040301e04130b1500080040c40c5000180c003620310550131059800080028000244450000b00d03c0c3d1001d59540000808090414200c09515103009090003441c0040510010040c40802c101c207000901c0300b100c0003103100c110300c51042c003155a514800b21480e9050f29140400c80d0a0720310209803641c00768068001e480040c0c52146100c4020f00416081e00c0f028456081150040141012a800c0c010444e82c2e003500780003030161a1036920740c0807945000211840710001980c1c0c1c882081004800e0040705e039101c0c2c085601340888002c044018007148908100d50342406000070b122020402d007034000c0c600310b44000349200114900311b000a51264440f40d21072030f403800348802c00b00b8072000c4e0804c40f500403504400828284001c030140002d1814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33271030 1250 33269780 33269783
    0x306070e06070609050d0210060302031002090301020d0e011e110a03020a09080a0b070306051e04020d060306090b060a0e09070605070215030a0b0907020a02030a02100c050327040b1c 80
    0x10340810803035010405500400701890712a10080500c0103203086c000b4109410000c12100c1c20341024030810140c2c0e00060b900c01e444501072801039660910100003402449954890300070142004800452450194001c2c444200700840346903610f1f6040080d103003110f00c0210424000c007414000002c00d94403070b0707014040800d16030909001e0301c1c0d11003011520784000d100c42200c5150545040041403507141c05150004d0030155641104c418085500c0280381070604187e60107154003141c10880380d149500048002c58210718200207801c0c041c01d000304144000c65145005030412017000136094681007996101d5030f00b941c080c02800f030074040202c565030311404069a02200c00c828410119442c04021350080c0c0c0b01c0000040e14400c0d54040c8600c0e854014009030664100c02c0b075520260f107001c02c101c40c885504131142090183c0c0840c003078500c04021180904079102c045a05150351100941160240e900c042c030450003400030034100801d41c1e01d088245a082142e4041c11001d0100e841840034001c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33272280 1250 33271030 33271039
    0x306051305151006030b0303030402090a23160c020109030b1b04271a01050c010f140a0b09013503030901020703170403090510030f050f070806030c0306070e 69
    0x100c0098840070302c0c25102d1144403501e12240000e110700d21512012040050401d0b040601c58496440e0000351a40001000a4050b40c906000103c0740005035020184841078003445405541c3c00c0c04116072010411641c10403e03440202d4195003c0f40901102c00310280d0595803a9401da065943c1c0325010440501b100302807201c0c071100b41282c071550001400150854004104600b01e4200c01c0001d0191150302942c10617141541c0c00c581020961643c2080c54400e0a01640d070344a02080c15004100d40f1303941203032243c500130b0000260323612700a41c5802001000000d000b40009902040600d50007031080404001d810708240b209042c40d42011040b42448000c4141c000307603040c0c1c050381143c0c011151144580d600003400010103070803862404500c0306c27003020b048051901d0760f0701400100f550702a840c810408044c0002003644650003405404007004418411420315400819181c01d007951114041001000092034600b00090840100d0300010020110758540000c140d480405070704500780c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33273386 1106 33272280 33272311
    0xe011b2606040b030705060708090a0b0309030909040219081f0b06041e0306020a03061517040201110f03031006080f040f030f030609050a050405120a09030605 70
    0x104005403400100c141c035840c00a0710382121644403a60101001a06504000510b402b17450030001c00d44011100c107841e44c40280e15400100c4500305154000e02c1a02c01a161006009421600103481e01410400c581c4981c04409682d0700903401a502c084840780e0f61440fa0b2a0010203007944c81400c001440410000845611507445500091500a404d5401c0c03a0242030000c0d00030355000504560307400380004040c001e002644a00c071311404c0d4130503c500d1054080c0210040c01790f11520b41e45a00e07540c0354010344007111003c9000e9141e114240ca128000002000154001c40c844500b1902d41131400d000282100c000400600004c5a1030041c80f0001d9151550b22581075410300b0100019601c03203000702d0080800d6845040140d0401082c0070204015600040c040e80c012400e9400c0442c29282107003140c8200140c2c4000605135801c208045441c40c1e20054019040340307804001d = true := by decide +kernel

theorem cover : BRFrame.Cov 33093530 33273386 := by
  have h0 := BRFrame.cov_init 33093530
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33093530 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33093530 ≤ n) (h2 : n < 33273386) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
