-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:48:55.228982+00:00
-- url     : https://prove2.me/submissions/f0fd9424-235f-473e-b447-f93fab981451

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16906481 ≤ n < 17086337 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16907731 1250 16906481 16906489
    0x22209020a020616050412050f010903020f0105010b030c0406030c020a02041a0114030103080703210203070c020f030105072a02040203010602010507141201180207050609030d0f0204050d02040e0304080318 90
    0x40503040c1410001303500f070034807040e0754008212010b688101648510001c01c91804a1a00080740c000c1c480d20b5280c01c811908041c3d02003000503103143c00500174461a62208513010491105890703010408008100800103640603030801ea000340c500340180c41e09034140341c02140a941025092110a1954290041e102d6821103001c61010440052490a560556a40200c03030700c55400060148000142028506441044c0702c40220100e12815522810142c90240c031400e00c0c07030801c0340b141c1c92003204070b0710b28201417282c103102e13801903510b0142c60301603100e01e11b410810070f0354000081c103005d45082c40580ca80b400118000c2205500000e0300f03280900c00200803c0d541c0e02103040458040240d24260003040028038191b0701000103e41c0050820a40c1c10024810010020510300038281003000000000c00a00404400c40314107001e089500403078a001c900c16400742c1070707100301c03521007850147c102a07209803007528001c022203240c541c640f00440d01e550800d545082c070a41040b14222810300f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16908981 1250 16907731 16907743
    0x1401090b0c1909050612040519050303060109080c0a050f0f04060e0708011a040603050705071e11040204030f0f0201021509010504020f06030f1506090a0b0909010f03030909022209020a02 82
    0x5040c2c03500c80f007211308080010380540b04001c41d01291040071070205082c8142803203000d0342a80000d0480c0202c0c0030724a8040d4903500f04a40d924003058064400045c5c1c4107000c5000c0032007180c0100b9510324a070510040102d81d030141c12545402400c420420750071031300c580c8500c2d00a0304503010310b07402d40d00e0406001403015030142c100c8000d81c844096001c180c4c0105406507020303204c95050210b910f50b1030502c100c51034000c4000103040726450120400740440c80007805011035000e07000102054180c42c040c0000d91046100c010404c805032180301c40401c500031014501d2134414815240324200d01100c601820f4015039007080d4a95407001480300714500140782c2c46481c0d03002d40b4410b0440c580005440747c04000104482c200c580020f00d445055980d4008907107415800801c4481899141c3e614601542c101c58003c50258822100120308500300380111000c5035895a034441d8490300f41002000030b0f4100310301e441c5010030301e40004003c0d01101c2403071901070b010140d070058641e400f40b40000d1420b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16910231 1250 16908981 16909027
    0x50105060703020604140a1703060907081005060f0c0102030709060f090e070e01030b03010203070c061406090106050c0a0b0103081c06060f0507050f0d0305061003181401090b0c 78
    0x5401004094002500072500f5680182c0000e0b031b411341035038512001420035801110082c02010000181c90381603034140065409520107480c914111f98030900150303001c4e41d080d504040c0f82100b0402c10480d501e08603004100201c10500390364100300d00d44007410b00ba41c0003956101c001c100c090500b0311050313030311034a001e6001348140b030142520f620340211100310940260000c07080001140301e500059001350456546014050021556440c0070b50b4028050090350200f1155036042520303030702301449040d6032240248401011020982d180000c2550746500c10107851890707001c0c0821100101d800c1c0784185000350301884a20b9650950268402c090710550070010581600c1c024040c031003203600484004103990141401039541d1464105189421024101c1074032a11485540410181d415040b45000c3c05040d20150032001281805600741c41800420a0340750740726664507000301e4944901d4410701b0503004000940d004081d1102d016a40c0d007140c968003108000103103208144103c0e640c082e149 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16911481 1250 16910231 16910239
    0x902090a0b0a031101051b0c03070501021c0c020a03060f09061103150f01030e031306031b050a050313020904050a152f0903100603030e0a0501080612030f0703080109050105 76
    0x7100c4080005010205a000107080a0341d001401c2078030764012003c031044035580039011280015a8451141d4440100d00c02502a004805001402e940009000341d901c07540e00c08100c80a0922030030440300d4009003078090703a100c0c410b2840040410400e1254408102a00c2c0c0c0c0440c024a250502c3e20130307188581d10001400c0e600b0400c1149a074001160700d0b900c1ca40072500302d01010040001240504000c18000c500760100080d40d00d000354095011208941c0140c41c14400460107540b856030070081685040c1c0818810411402c6192261000355400348240e45d4407003071400e00341c021449158040343d040380d855102041020600c41c14480c0d0b007005c18081003090200710001c0c030056801c2a0074490149a644050781d00312010b104450a651490201404071440e052400c804940074103e42c1c80103402184c44084070040905010f801036044d1801a12141405d850308400d0054024124a00c401d007400203100c580200da03001da004081450007aa41c5460380c1d410903aa04003281e1040c3d00052007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16912731 1250 16911481 16911491
    0x2060a060605070203060a05071404090b03120301030305041e0b0c060a0509030301050307062d020303010609080115050d02010309051902090a0606080f10050306040803070237020607060504060902090a 88
    0x160317400034200303030700c04140a0042280d890703243e4203450b6440d01c04504144903c000c900443c0003641d0350f1010270500b104030200c0e84c0c505032480f40f034000d5100c28040500051402c03c8107009841c8100c8005021034040d000780d20340d0640c1c0310040c01064102010740904c03500660f05209100019005441c0c103e5400f01c0618030703652400000035625040d51040005000a42c03d4140c88030880b00c1590b8035101c0104a00016540b4030f000080d203d6000b4012075003c00c0082c00c02044070f250511400514905103425030170360381e040200b00074000031245802ca0403d5110901070340040c6c0c060080c411a08180303420382d100802c080c81040008000200030314000761810f24100001607100b4680303074111064189820064581c80384041e80e011b17564200030340500c507041c02e1008000d0040001e5118a210340e00769200c0442201804800591200710038007000350841600e428203000b104105032030f500c0202490b02c2e0030300950f40e10058410494040d00c845650701a58030a5041a9609950090034100d003017103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16913981 1250 16912731 16912733
    0x3010603060801200d1104080f060610030903080408090316151b08160804030b070804060606080f0403080a0b0306040f030e06120a0903030204090213090c020f07211202060a06060507 80
    0x19181c0517500403042003e803200e031036021030a00101142c014000007015100103a026016141d81d920040e9181c4e401001003403240700d4014800e12640c451140d2503500c0465540366602c1d02441c40d00090f900a42c03500801034511000d41507002340f40000c0040340901ca017841d10580003d451000f4101301900c4880c41c1d12001030001c0ca214003214000589440c0614095580381480c0c440c0c0d020b11307003004100e50780344802c0c0216a90040703c1b00b44034030310480007400840e0f02c03400c0440e004030040d00c3c6042d4610802c40800c000074007611242e54020b920760000030345e0581410010303180c40c1082c0c50690303203003140480020034540d0250418050410559400d8540520030242c451800b10046c000401a65107c20078820140300e6012140145802c550554503070314403c000c1c00b10b07140b061041440042c60141750410690004c200b4140744191000507004140c540040c050016503d142c00b4804004071512400005061221080800443d80d0007400e0510700b05040c0c204071102604410144070013800a88 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16915231 1250 16913981 16914041
    0x10201021201210804060c0b0a0c0e1002030c0a0b040212060108030316030b090114100311070807022806030e0604020609010c020d06060801020a020c0909151003060203010603060801 80
    0xd04603005141d40084040496000c3c030100c15040c030001300441d01c0040c1c002a0140d00c0a40d4000349401968603108a40700c0310818002c0758030000301c1d9800f06544040c0c28810b441c145540c80740e0000c0900549240503584011181400030401c03040380e85c0041300c0240010b50030a07030002017003007030000020103403541040c507150390b68040101000c1035a0070030140799019510a40000b4060a801350400d9040c0d40c440421420300040200c4490140c50000c85c03503012a482070140b0845489030b10301c042d24044660b1102a6998481d14050740c0200e1030007456070306503100c425044c0158249000c4119000c5c10940c1c0202920f00b6080725031b0603544204240400341c1d580c04103d07020702a003428843c443c6e441c1480410340943c0d0506029052624000b4001080350040d0000c00d00c0404036400c0c2c0d06242046401c1001041c410740300e80036240c2c0501148400544029000ea030800001001e507004550340b0b950b210246d034401d82025000030f84500e0108410082401410a10300410302d0026400070000400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16916481 1250 16915231 16915267
    0x6010e010b13080303010611010f05060915030c0303070303020705070e06030c0103020a030f06060e0315010f0b071707050102180d02011403060a08010f0c020601050922020f030f0708060601020102 86
    0x4a21100d00040d0b880d205840d5800e50703000400c448420340f40c80f51781d141005040c0d0000110166403550a200b000d8400b200c140c400d061142c04000e1004440340c880103010b85c2441142c200b229014400c0c425450714a0f5400c20282c40751070b110f41d0340036076107465600d080d170b003085001e070305c842ca40074004402e01505540200b802c254041081ca001a03c80e0001c41d02100a400c20b010321144442c5001030101d00964812121003c0d007078140c0844104000c0c90720400c100160910440ca907455040d01c003448010110070040522a00414000d01c0103200343c40c40d52403a80c05100100c913340e6000031804421500c4200e4110064411078401c2c14074010390b00041c0c103100001c1d081c10440c1e040080003a056039a8110440c01809850001b0000030440c20000320040201034140c0c0701500c5504000216407030f06100d1244149030100740340782c01f6185d2401d2001d9081144c10300702c1e07200028a110614540f410031100140e448120b0041c0340161400c030400d8101032004d88444c2c116401004400d200210345025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16917731 1250 16916481 16916489
    0x503040509060a091404031409091308120f010510031404020904030207081203041104180303020c030403080f03040b0603010b01020c0d020303090303070804060807020102040509040206031e190e06010e01 89
    0x40e105141d9410000500d101d1a6404c14090f062412944030f0b404915004103d10a44c4243c0350200c0c0c0d540c1580e41510280103040d40b46602510300d1300003e20300f40480e0450744d8002d104990b01d6080014039000440005021181250045080401046503261215840460340c80904040004070320121151f280024020700190184680384003090400d0300c208000002401c1c1d101c20303a80300c1e40003180e071007186034016030b4103403040b4900110103130b058a0184a0300610045141c0c40c40002d080d035680a4019402080c0c0b402490700052200001140d0389500401c8070780c0c6803a00055907450146000300f0110009005103003e40c1c54580c1c880e1702071f600010400d2240404588802140c10503100003031441c030440703540d5500741c00301150070300800900d54050300c1500d40680302e000e03d5588481041b400c034020f600c10359034001c144101080150070610000c5802030340c0e43d13440344501c60100f024044101c005035003194100c46284010030b0760303180600c0380c41c3d8202d591002408155161002e51003034541d040c09 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16918981 1250 16917731 16917739
    0x204030b0105010818010e031803011104030b040503040b07030c0219360f0b0a080c0907050a03020d09050c030709050f010e060102150106021c02030703140d06080106090f0b06040305030405 83
    0x401710314002030440b0a0440c40c2c10600c024800d0241c5070f000c603901c0744c0041e4190410034548201c2440145410702600c215441510030307090900c1c4c07454458030446640a0f01c240c905010400021403c403c2c0540140781c050b000c2e440b0400754081910501058066002410902320103040040c0403141c4403050340382c6101c1c9882003a00014061280c0f1101d19000d0742c03402c01c02c240c5003048001c815000c07904070341c00c0701008490210070181c1d0303241081c1e112108081515407182c10b120001d500d1074020005407640c3d0300c0f9032900500b8030000311b051600702c45d990f403810703100e07640200640c0140d0718003004a0806000703000e0081c41141040c281004500006000343c8080342107607800203841344d00c2009920100c1c91321043d2100d640d6501c0708042d40b14419a801103000b0890009415502800082201c800079410355941001d00d46006080e901c2c0d800910010f036070745444110008451000f4003d001c045d001103000021110a00a00d10080701c1c0d006e2403a600a041c01c6c00100007048000c4181c0f022101e060b6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16920231 1250 16918981 16918997
    0x30201030f020d05100312050a02100f060b03071107060c050304122604050f01030207030509090c1605010e0d020c010c0305030a1b05070201080a0506151303060606020f070501030204030b010501 85
    0x7050002901441e1103d00310140b9110400c0b135480603c1c00540222070041401e4000c0c01b80c8640c0449942c85a15202d10240e40a01d603a030440703100a80c0054440e84d00b140300003034099100d00818415034415923100c8000703412048081c41c90901403108034024160b03401c2000140c0426035885403240034910442e2400404501c5440c1800507080c1c1028524503141007039020241b6080311203c140c3c200d4010103004aa10b10400c801c6540284201c546d01350309604c6241c10102d080702003201c06c0100404030106804107004c0d401c003d003114a400c1d20b0303d901c42d100110307061542903e04c51404024a140c031086600c101c0202c1203590f0002403900c0000c0c1c25207403039a6a41d4945001a02900f15030400d01072071243c801e00e182241c0e40c0030000e070015030301c01d0303070f5284940c1c4484810b00c090350000e41d803040d408140a00500c562a002e003000340100301e04600d114407516500e4460034111074543d03001d480503030001042c4401440b01072040304058003003421300710b08040c1180c032141c0c081e800500645050002c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16921481 1250 16920231 16920251
    0x5070e0d0807170a12060504020301060e09062e021b0604060f020115030f02271513020c150109050411010302070302011506090f05030105090604060b0a0801050412110c030703020103 80
    0xc0c3d080c00c44142e0070786011a650f502c03000c600511400d10f080400d0b030b425207425400700b010318180c02101d04a4136169107501caa60703404020442004c0c006891241d02041d022207030b0b840210442c9c0e903944110020300d1010031040001101038200b41408075085800b0076046545800c90f6500300c180e8050341c14514140c2c04d00039464005070300400001d81c045610100407000003041040798401900d00310300c299403459008600211980f03041c4035aa102a00259071071000800030310443c00e02c11440d0f8801030021108e6000010180100d034040301e0400500e03001010510040010310f15641c0c01860090380400032450692144203843d2010150541019000104101403610035000300a811040a4000118076500d800240c2a020340d40b050788550400c140e03000807245410f2240300c9c807444000015014070741c0c0301c1d941c081c02854890360700f50744910745813000305400c4405d114480c4070360300c61460030b051105403407000303484c8482e01c08131a03181c0e40c4502c1d4610701d07a850200d01c0760200d903820308010a01410b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16922731 1250 16921481 16921493
    0x9031203191b0c050f03040b0a1b150c05040f08010c0f08040302190c0e07080601080a02040806010b030604060803120105031501051008070201110a030906140103030804030e0607080f030a05070e0d0807 88
    0x451080da09906c80860003040080301a4001c11400ba803d0300c41440150b65a4910341865070802c6e00600010140d17030303c2a105103559082800e00903007500e07082c0c0c038064485c04e24810035140d0750800042a0341d00c42c1642c42c51600b06d0440000c544590901c996245000c2c2e800a5440c5100c00546081c4004440414100a58100740c00090612092450f4061030410801004190112111800a440c1c000070503080700584c402c81c0c00b41c5084601034110b50f030034610f04160f00e5002a2120b9005030b56004001050501407001c2c10b400c00c42c12310084099450801054a0000391000880c0811600f80c0104000d81d1510502c1c1f0150f5541d041c160400e81d5170700c0c0168010b0100961486150710001081079016a144d4086c400c0244207150421810f080c094015006c281c09010050100d20008003090129010b090101c00011303000b44500e10305102c60b44c0314181a00300804400321104044180302415941d402441da20810928241c03044403105400155400356004019100840000e51135042c061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16923981 1250 16922731 16922743
    0x90f0b04020304060b01090b0306060d020c0c04060b0d05100506040e070c0c060201140109020a170903070501090f0311010905100e010b030d2606090106030b0609031203191b0c05 78
    0x40018001c545914090034010050001410b0140c0040c00004000c038410030080d06503401100e002e002c080c18080c0e10513422000754451307002040284a0001e00c0140f6a64034010b00026090040c5010b481d0503401e4914005e485001d000b84101c034482ca40b00b03100c10781303851040e40c0442e0210310200504d41c943c05020790f025810745034040c081c0c02100030045056901500721101880c2c0c0540740b102c050f81c0c2e5419060032401510f03488000241d03591020449a500b020005400aa403001030301d14000540d500c0600311031110104803580c03102484040107140d001100d076103400d07850800034000000d05517143c50310341c0318031801141100c2e55013050391035070703102584071441001d40501200c0c00320384620b0b0060b240d46c044110400282040c180c6010446150305251800390310003030710140300340c4d00b403840a0f0045c00d0380200c0150400000d00194070b15540400141a240304840d419654a04084e07206642c06400c400450350002e0802d00b80100f000395054a69402c580d003464100740c04400b9181c400e003004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16925231 1250 16923981 16924001
    0xa0b0717090607020714030a14120a020c040e0a030207030204020f070f060608120a1b080f030f060a05010c0213090c050915130501081e010b0a180507020313090f 71
    0xe006040120300c400000e8950b00581c60f40d000c9641440d03440b11018160400c003c0200c2c7c0542140030003000203a5400e1580c1c024101c2c100685504d8044008810203e411641c1f42c603006a001c48400001d5052900c5404040150310010f00104002505c02079030356041848000d000310790016603900c09070703102402d84500c147d0004408865825504044002d0b212038011803004d8080c1e600780c0380c4081940011a143d6049a0b12800c00592545403101c01d400383d02c1c0c00c103440705601000441110b614000046200b50400c9403603d9503418030000f032101c64100c1d600400d0500c111410f450000d039860105884614242e80008a5a100986426200c1c1d82c0c15a1180742c0009280c818003950b141c0c240c000984003803064802229030786c0742d06a141d05442007032007101403580002c82c03042d007a040e520440c509003049940010804820f240040340c007101d0941e000070014034201c41000742041082c0226074001d60305200941c10040003400300b6000b0b00043c8500740c5003d40d10507651002c500c003600182006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16926481 1250 16925231 16925267
    0xe0f1f06050d051e0c030402040209040903021b01020105090c090405070f0b0403060f05060d020603090a020907020a03021006060509011803050106030b150102060114130605060f04030507090e0a0b07 87
    0x10394809001d8501d0b042055040344482c20440002c0c11004003100d0131111944049500e001501d45103400300081d84058026600315400700120070701ca403500d000c1c103140148254003c14002d021010703484060540011000e046905103001d00100400c00111691207080444002142c0c0c2c4030381c54000d15005013603000300700186100c1d0000440c840c10b080500201d0b40220018014a00d08800301030460300700b2528198030603101e1038507101508040e40035642c0460710004803a12403445800140215034112741d4100140d000035000010954107115030f00d00384c02d264809122aa081030720142490184001c46410046005c1c12900c1240300040da0300001c41d04040200074080e12401c090342850400c40340848099030079412505207505c0018503034120b40b008602c1d080000041000c220001012071202c007101a12004045031940e82c440080043c4200306822a50707885c65890b050f41040c07421307400401540c0c600040303001a10700c040f4007100102da0005161510ba660308005580300100b1801400171 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16927731 1250 16926481 16926541
    0x9060711030c16080d0e010518040f090b071103030402090402010e01050d020a02070f0501080f01061209020901090b01020601080a08030103061d01050a0603021c020604120302011b081e010e0f 84
    0x11082c001d40d030f106807800201980c2c50030703165910554402100700c0e1141d0011700200f00c45407025040109241ea04c07030000308040740024070011840103070f417464030007500d031040d10109112086802c8142c811350300c0d00d003201031410344c503140e00042c403034900090010b41880642c400001c0268400c00c120340c00004940307411522445040402955041c0d18001c0d00f181c40c0c00c034140030070150b0240c0201e0344640b44107003100199a00700841103400300d00341c00d0a0350156484072042d00050741c549200074041e1504000010301e00743c0002c002403070200180e22007c0c4070f0b00312302807540c0410f40d41c00450341500e4004101040d083c810080c402241d0710b001c41d03488495403a0005100d03605056400c101c04482c000c6555907030b413008460444d208441e643c100207512030003c01040080f4190b0700c0d4003040a80c040d0000180c900c1c3c60441c60101c2407588010000082c544004000f0b0007410103d61202440f400020040558106501c0c0e00a60002409641a00326201d002500c4428844c410701042d0420003101c100c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16928981 1250 16927731 16927753
    0x1020c0a0c03020a0603020408060a09050708030f130b0301150c1505010e040c0b030903180a0503030f0309070e060f01051803030c2a0102030f030a0906060f0314010509060711030c 79
    0x401d80d0a82d0008a100703102400000483c58440c2c004e80307041c0c0c0c034080060b18003603d41c1c610680090000070401c0310640140c20b030020301d0307007010b002038108840d0b5802c509a966240042c0e94603a26250b800076200c0b1201800103201034000400040700d101e4007410001964040d909016070310704032407450701c2400c074205000401d48100381108180102e01c1080d84800040e00e8003030881d810300045908004540c400e1041d009500075000d601e129085010301600700880d1100c012a0455000c004410794142d800400d0101d8103c041000030002c02400a085001c0d09042000074600903601c0300081c100f0101164505602040085c00c0c80417000090440f5035030641001400e460740e10710380780007120741c0c0f184007114201440c8440d407a0f44080164055841d0040c0003901c032506400107400d02050995815030030001907004c0c41560060906820100d00c0b8034076510305010480180009c101169042605100301c20303500050032600b060260810155511604250600d0340c0241032000c2201d00c1500c0e0040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16930231 1250 16928981 16928993
    0xf0a030f03150b07030e010f080c070f050d051c051005040506061c0b0f030f03040302091807030302010614180121020904080a030b010504120303020a0309050a06060e0105010e0607080304020301020c0a 88
    0x1c104c2d01d00c2602c542c050303004540015512540b40c80801c00c0410142c10029840d140c064004019052144040c5da40009491711442e103407440d024090b2001c0707070001981c00d4641814540c2000c0062000c034090001d440c068681a10f8615588149805951a000410b00999519003a6880303030f0507202d481091003001e0341d12880070300310481210380240c000410009241c180803a00000010b00c05c4010f52801c1e245900384030482038002c00301083e8105101c801030b840e950070f01002e401180a5030010550341e0401c0c031401545484a10514440d403100009210312191100946044400301105d0290442e48000b2190010a01c400001e600c40201c0d402c10040005000290595004940e01040620060001501c440c411070041c014443d040014240c0040d101e40c00801582c2020311340880c5200242d41c49614003080c20000720350076130700c42c1803c0c00b01001059282e80180000d01e07000940b24502804201c080c41500009081c0c404c0000010307081d91001d40440b032080602100b01d8800d07140b6400e0603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16931481 1250 16930231 16930237
    0x1214070b0a1d03041a1605070f0e0a06050d020f03030c010f0204140102060919170403032303060a0605130b070b010602010e010902060306010309050a0b01060906030b030f0a030f03150b 81
    0x5480d8488040080c10786054000040c0d40c1a10701110640840a510020000e00c03504440304540d40c000c1b09a80c0c40c3c00040c41071020388004c01440074160019406e0240c801104c0d07030000d040c4c0301c0552601a0401c02651061101183d581e0181c40c0d103000a446140403070b00b10310803030040c02815800e005014034504c0540c0c1c02001202e50762407a03140b413403501307600480c0c41b45001e40d1240c400b03900142620400e2003080c024100103e129403400d000800701d0041c0d80400b900954070641c046044041007200301100c104912607055007100041340755103002c00014004105a0040e84200800480c101d9070100c03010302090023501070043c2c81a2141258540310300e4070203007401098010350800200007518030050040480040c1d005005074190758034800110020b01c9050819141440f4850200340810031090b80940078055130f541d03c070609801d10a01400784d0304c0c4690303c98080c1d0700003d181091860007250b000d0303d581d4907180c944a001e882003000c81c064415a03102c2e0205106224000860940d50002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16932731 1250 16931481 16931501
    0x1030e030a0917010501030201020703031b02090a020c01050f0c030106050c030405040207080417060103030509121c02030903010c02060402030307060b01140a020c180f0a0c0c1406010509060a031214070b0a 90
    0x24203c00500912400340c20789a080c40000d000d6407100c5400d000080c0200d0008458075445414500e00004940005010390300c04d031492547c05a000410321117418080c002c0ea40e000d240c01c800c15100c0e050203201ca03140c0d4401441504204100071807807410b06841403044600401004006540310302060401c000c1c40c2c0d03c68030070000030464442d4220352884010a181c2c0c12240c040d101c85082a82000500c2000707800b288040c03410b80500c400702d10241a1026410161041e154029a00c918504082c5070854000902d40b00641d8441f2003004010380d000400c6074800daa00000200343d08440c400143d808216031441600c10324000304c0c90081c6140d0000d0f80c4a50114200c0380340c007080c8030b2440e2a40c06648245c8080512510b28000075152a045400c0900340100362310746014030840d25180c80c003501c00500d24200c0540c12403001080305107061303410b007504030300c04560241000d882c5603030700d0400042070480101070242c400040f40122210400340d942c00d0b500300c450228503117040340280009002c040a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16933981 1250 16932731 16932749
    0x1031505011e0b0a210b100908060a020703020a0b070201020c0613030c060b130e010504050c06160308060102100509010b010822020d02040f09051515011d01030e030a09 74
    0xc040240c20300010710b1500d41c40000302c0290421802100360750000d10800180500c0c1e001c08105242130040070450500d0708080011000700340c0c4100304d1058a141c558408010070348a040c031510101140190708903001d40e00050340c2e40c9071031030280c0c00c04032030039001f805e900b0f0b500003003210454041d0001c04100c01c6480c140e0316a80d0390010300382a00582450064001a0013402400c002843c80c1c0c0f110003448001003403802000440d5000c081941c4803481d441c880c594450007400100b0204004410b031200c411a10f4500300800030b0203034091a4044c4201804003c0c11001052107640284115031060752441030500603071600080440c080d1581e5501c031030010b41098002200c1200c10075030f04254102c0b400c0781e202c4100941d000c0055520007032a050b40c1c0700350384260010050368140300342030a0510400c007038050007001050b80040342c1d80040003c0074001104030300241c0d50380d102d03440820007198103581f44900c0d09480012030003012a511004814400001e81c5150a600b004500007210f050f50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16935231 1250 16933981 16933991
    0x8030702060601020714040f0b06040803040608010b03010b07170d141608070f0f0e030d03060501080a050c07030309050307050d031b02010615140f070b010306050a020309070e06040204050405010315 87
    0x200120b0381c50b01240b080c40c2480d020300b602400e652600741c2101c040d91341e104230301282d10550398000a116034002d51250741c29a00c0020100012500108102d0050003c602801e00395071401c00811154410075000820659000a08000010f0074006499101d68400c4c01080840d000041070200441e05031103500c1c0b007000b900d00c410300c0c19210740c8101d40300d413203103658200b80002d420718150b9044c10b2001c0000b091009066aa01740c07502c04000d0003c0e40c030300c41e540100d81c86e07242500140c1411006040d8004090500080101c0108000200d03040035170705241c0000c0140c2c150411908600410394010a103008241c0410760041c4c1c1500094030031000c1203803014680b071100f030301a0308880c114480d9514035954081c118801d18028034205003082440c081681c5001021555184140d10081c41100d80541550041c01401400d109065116050000c11407a40c1400801d1607a18500c603c070712143e0810103070000320140c071140c05840042c5000390003030007256104e1400c0307a0250500f2001c0307580d4901e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16936481 1250 16935231 16935241
    0xc0503030a0f030c090b0d090b01080703030906051305090f0a0506100801091104030b070f08010b0c03090f040609090803040b0702070509010e040602070b01120210030c0e04050a0e07030803070206 86
    0x4000c880d07912450340c403001c2c0c0314480480142e0107004019064414031102003400104102500000c002c006280701d00007400700210320303040c40300d0041038101d6402940310007000d0000a401100034010b4581905010740c175000043d06401c0100255040541c1040b40b0b1414801140000004075002e210502c90034401030f079550303084c0316032079204082440000d51444010800310515520054501e403511f01120310b019129100c060003030728262102c00000d00b4000505020b00d034852000c6006d031000d509011300e854110034a2a40d28000d02d99281e1084680258a2a0a96030b55100b4001010032407024000341d100d90905c020203820841e0103440e5400e50300c000890f1a84040343e44401c1d10303030040000e00c080c1d00300034141d0b4500200070002c890141e8200a0040807821000005000785100d8001c2e0140c5162071041c00105015000000c047c1420003558803001904010186e001d84000e03540010b00c2daa8820b040d0000e440e0015a01a00d03010b1160040f05001030600151b00c15001a002c440d904e441d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16937731 1250 16936481 16936483
    0x60703020f0d0207020a0b030c131203090603020d0605130b0102070e01120807050c060d0506011209120c02060d0e151b07120c14062410260f040c0503 66
    0x9254103101608000b0031052071011010f602904070907002600c0380740d425803110b00b8421603510a8903480c6004c00c0103c1c2580701c501c8410025000740008490886c0300b10601d039005442c20384c050281d0300070300da00820190411050b560000e00102001850241c040b001030441703400500b1b0488240b8018040d02c8000303d0306241c5003180360b0403104980300c0d422070a10315441d446c50300c1d04044000c484501603103040c03a14a5440d04c02030080c10011607000511418040005003a031a010304143c2c0140f8107084040011601512707001000c400982080300030054a07200040b09481803090120301d1524203c400c0b59640e40004010503003e1a0360007641c203d0321000c60824a54000c4200c0445180302085094006a551101c0c800a03100300c0c2807a60b1003581541e01e1b80d99442c3c240d083c9414660100041051203404062642c00c4500f040c41c19845206a09001c50046c0b2001c001203428000b030102495001503889840300c51000d9004640b40c0c0c50704003800011030011050f2030549000d044003401045501d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16938981 1250 16937731 16937737
    0xa1202070218070c061505040608010902090412020f0313090e030c0304030609020a0305010507020a050c0a03050606090403260604060b0f0901080606090d05030d0e010501060c0602030a1b0c030206070302 89
    0x50000c044001d003281c4560011142c40d8010501c4041050401e0341d100003130f100d4000d1282d900000003a0f1440e4900b08401d21044038550b81c00340312180e060404400c09a203540712504e400581024a00c00c4421166500f80d190020068110040344400904103442807109140c0c14140d6a00712001d100d01889110300603030b01d0054843c001c0ca0383d00100001c00c00101d15502840748e01e440549045440f9540340c64950840e10100c0310100907800c038440d01030400805001c2d06a458408880c4031a0350741c04d54882c1342d03031410010b10285c01452064042801e0500a05146810408030080d01c10b095241103050000302c1e40a4424602a504024003c21003140c0c501c00c0e6400d00800207200d6081201b40801103030b85220107400c454004c1c004021035041d9481c2c0802ca4440540a28004e55850300c4104200c400c40c0c07100100c86030143d00d000d00522101d6840250110a190805005038881d11203845441c001d2213007680d240c0d0281000c034150649981c00c42401000c19001e6025202159241101502648 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16940231 1250 16938981 16938983
    0x9040209010902130f0305150601180620010c090e0906040b0f04030e0901090204051302070b0105090a0212070f020d0e100f0e040207060504020306090c010509061b0a0303020a120207 80
    0x5600061285880c1c9a0251100700da0090b202a84c1c00d03a994000c40c4400b5481d0820344458000b40455404101d001b0b5025412200a02e0f04044c1083d40038446554a8510f00942007044800388100741d5100544c1c042d2448283c810300204610010034001800c460100e12a41031205450400240d41d0100481d105d8030941d080f004030032050391000d240290004006200f1000e02040c125900a00e4803480e8030f2314080c081041c001a03841d03040008201c80400e0321480304c10700032f004001e48000980039094450450f0030566400f00c00d07031504a0313540d0280c003810030030902c810503090400c2840c503031281c401d841032038458003a5440d40583c020200c0e02003621007411504a90340c2e8041c071440c0d03031040e5400980c00ca024604a0705003100c45000070166031040c441640d20b2603c41041c001545002e0241c07980000004000b4100076081c4c1001030424000d100d04180710f5031001c680140300709507900d8103818640d04007003640d240015a10b4050029044054079000051240903800b030011190f00c03ca848176 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16941481 1250 16940231 16940239
    0xa0b0f0601020a0f02120a050c03101107020420070804140415030212030c12040305070501020f121b030d0c0201050105190b070501020405030a060606030b040204060804060b0604150509030606090402 87
    0xf070302d264590f50065408000201d80002469001c03183c50041407154642c1e0380c0c4524050a40b114104040502d001c801c3c003103081c88640380c00804400500e12004503840150306450110f542c01c02016605400d00425020f0302c0340c1c000000350042045101c0c0f0090050728910758080d0a906800340034841100d5140310001005030381010280050f18080c0315508a668203030007180c0c1307800c1c42c0c510080c0c28000041200c0c42c07403403008603041c01089401c1c0003540142000b0310041c4080c0020f40300d01a0343c0c0c141d4140720258600300180b40c002007443c0d0b64040350b4010140b01245da417084002023075030061141100810040d440e00e80046228502080f02090400801002c00707811810040000034640c0301c000700f10740c69942008000f826444c240110123440b801514009000f61800d00c006c1d041e1001c003581c9900c12441040706020301a00000c3c0e00d50000c1d00701000091013014140450210700c2142c200070aa40c206000f9100f000d94008000d140005c01a400d80b10980c40b40014041420b0080da402544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16942731 1250 16941481 16941493
    0x1011060a0906021903050103020a0e090312090109020a1203030b0a050d02060306060d060b0406090b0a08011202010e041104080f030301050105250b180c0f030715020309060301080a0b0f060102 84
    0x10040340d8000014050265900514142807825403407800c810000c11000825103400c0100150300d414a1040010440b0f12000042c80c9841c1980d07903241e104150303191950b8001c400100740080425030101514139030103000c100749591102201144007603040c2080700001c0c2070036210f211600b04a55a0000c451000d410b42d0143c001c260308110f07241c1c000070710568001c3c2d4180542c00d000701c11406024020310720914080d41c1ca41c10b2600050110002d03402c04010318404104084c040b6a00400c0c0034119500d1501c078019481403407004950702e0702c0302d0000d50381c01404c003000c06505030300701c400070401c80c0c88a900b00e440003c8010411b41d1207000074811580414824000b48e10b44e0020441e401c0606250b0102082d04204540e0f1102e4004109440003500103c02000810300302d00204001c104010007298130440e43c01f05180080d903940528024032024100a00500084600810541c0d00400c001005079481c3d60311005035944d00e515025060320011034040200384204c4c804420240150011b84c0a042c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16943981 1250 16942731 16942741
    0x915060409110414040308070503010e060105030a0f06090f0f0605060a0806030a060504030201020306090708040f03050d0617010905071a040306020304020a12110406060f080f070309020a0605030402101106 90
    0x5007030324a07080e9010b80030486054580c0e92184600300241e42a0510714419003440d00340208a444024117000600c40100f0062000c9008255040e51004007480e0281d40c0703035030f1000031402625101d8100400c207400e10034041461450768019185400c4096410000d42030310411031000c0e100140f00d0960003800070040b1160440c450364401d0f601c5540032341119030400c0c2e01e039504005c881003128140d005075030200c244055454016009078002d140f0703103000005424551692101044200c500a040c040300162420b1402c1c2c81c0e4001000501000d0800381c10441e0004029000c0e0540d06800c41d118007804102182240c010000305482010381d40380c881c28181140d1700c120007035201620a99101c030300f8410000384403117010f21001d1414032561600aa030450501400143c0341030b500280c0a0089245046190541c44244668081b6442d4a20320300364541020036801040b000802a40100c0c10304000f081c416044802140220320982d980b0070744c81295035044900b0b00c201400d140300ba03003180000c96 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16945231 1250 16943981 16943989
    0x1060b0d0b0103180807060b04020301060215180703050a02030106060f05160501090c0303030e0606060910050711100903050601150f1d0402030109090201031103060105030423070b040905091506 85
    0x904101043c140040c15840d8a07002111310b4443e00d00031a080a8001050400c00c0a1400380d40c00800083d90194110350400074065180d806203100c5440e8803203050000350016402c07107040d0700c10880c480191850b1070b842c1d0400c00e07196271001205a003c0d600740381000403c6449100b40300044030796a03540905105542607003c1c46c5d2400c82000355025034807412000c000c1141180303a030000310301c0307601c0005005441c40c4010f800d2150003010346105880c140400c0720a502c0344404030380154054039016582d0509407a000010901c445540c60b0004040c102c0c7c08240b0390443c0e1f0940a0340d010f070080b6541680d850884491035100030fa42100080d140402d8035001c98040c050214009014844004003000d60001050498100341d100c509104c1d2500e0310401556091300c1040244510292602d25520300140040d14903c00070300014442c114400c407c41405503101d40f024180d00c01441a500815960031219110350490301441c56081d14140c00300c0c0880b000022501000c452500e048201d41c2e407107001b08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16946481 1250 16945231 16945241
    0x10030506011707090203070e0102010c08060105030606090a0e04050102070c0801050903040b030a020c011e06050402091f0203040806040606050f010509130b0409080d0603050d081302040b0d02060d09120201060b0d 93
    0xd01900d10444a0200300c4c10032500146205442555845440c0c0800100090075034440404400a00c42100f06010f400d9900c1002c495000500340e4409030340319811404158000207075808440b5043c83d0009010400c0810340052525038060125030406a8403500c0050032900c1c180c07500c030300316030040004101e074980c14005140d1042c0801801810042c4140c0d0031400e480031110255640381941035504410701480c4140809001c05850440c04d04010340045a4101003405d00540140d00301001e070000c49100b0800c0380e01a114034010342e0380501f041e01d005800390016028003031048810703210440c0c403544104240c400d40ca000902e0303c90340c2820f0003029401010b5000c2d6682d081903d42840c10701140b0301000612032042510b0b00042d0303603451402d146040c903449c024484100520b400074044c00030700d0b603503010841940441d80002c401403a400051800b02c402c03c0025000180820504c0c101c0307070340768040c0328141d0003421141000d20007050200c1c00c0b285030b402070706400c11050143d00e00b0070840d45c0c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16947731 1250 16946481 16946519
    0x30305070509030f07030203010507020d05090f190e0a1b27120308040c090c02030403060213090603060c0215090d030504050a0615180b131812020c01081003050601 72
    0x4954a00758122000c0f030700701041909200250b0340610400c03c214182441002d521121501c060441510040d130002c0030b13441118081842010a808081c01e42c1d5203000c4144000140340c00c66042150756240041c084980031903003100424035080015041403101c03810b8000c107886030303500c00c0c18001000c1e40d072100200c00940c0d9010500040540031485c000f9410b00c48145501a0722842610f1038a0302d080c81e00c41e216604680881410010346509060b000400d540a481c3c0c0903c0168840c23004030343c071200d1041c59520a03248141000320010512480758031181c2c000c0c0326035007900c4030001400314482000c1420340d4403944582c480c00d00d1806051082d44402c0d009841002924600d0109442d0002580c3c4200f0400c210341148910402a0740180c5101d48030204e0032a509104404800c00002c04480318401c11104098403040b402c09a09503e0b60303020300d8541c0c0150314030a00d040c0304800940d80d002c1c046800340422130a80100310044280502c0401f120340c404000c04e0140e09081081c00c1c3c0305a4007903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16948981 1250 16947731 16947737
    0x6120a06150203070605060d050a020d03020118030e0103240b0d06080a110901080a02060307080601020307050703110a050a050a05060f0f0a08040c06050703120216060906020a0809060f0403030507 86
    0x90101e20060454005460180168020343d210551401e011003150b070054201c5200d01da140c0407860004502040044000790101e540b0105c29245040030303409007602c0408130510342011440034040540000024501510070780e4200300b9421b640010640e506115000041c611f1034001040004205d0341c801030030803000008000c9021665510042c0ca04074a8100448401c070000e0300d6180c803030400d0201207004000140007002188000e4010502c9440064013140411030600000743c2c150f40200225440c1079486000c440e07a403035680c00c040c3c0414038040c81251144058000000e0b07a4544000f10406845000382180e0034030b0728040804c40301e64402411000408010700005840c0031008002c4e241980c00d0380c44410301890685401d55903036034581c111400b408001d00120010940c0002d1012014200c0400165a4400c0e03104050085490300f100500c0c5a0801000fa010841d80d50040d00e52851103840e4480241c460b4402c0329140c5400700d07030000c0c92209140000d408280b09400403508a08182 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16950231 1250 16948981 16948991
    0x60904020f28081302090411030a14010b01020c0a0b0a0309020901081f0225031b20010c050d05030403030f02070b070e0a050f01050d110a0207030606060306030206120a 74
    0x9014085a50403840c0c04842d00e02c444441e000b505414102c04004061080ca40000640341c18180d0030351846400d48042c1c01403000314001010840720340410341709004010708903003580b0118036042488200c440d2000d0318a5007001401442540000b9640b0400d4100a01189115042c403861020b10f4012046080070591240100e101507180d03101000c0c003a1040318054141c000008035030f0000c94002e19a0204040d204100501d1501710700032040c41b4160340f80920250300340305801c0031a08100c2002121702c10070202803140e8100800c9600032110814440a1407042450800065465090624000d4100e8021660b4020003601c2035008507802482424009000b00d08080c4440490300140c8044913810303500c5003845105900840390b542511000c0b12080300c280d061802082c1a0242114240e05000c40483e070305181040c80d8221070a00007960800340e40384e00d0a0300c0020b5907510700344016140b031860181e000c1003047c4030b030041c6400d8a8014020310b02d4040e40b0f00001804d07a200030200703041c0c50350310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16951481 1250 16950231 16950247
    0x909080909130302120301030206070f0302010e010c03020702030708030301060f140c0106090207050c0405090c0f031e060f1006080c210f1509010e0604020a0203040f1206050a05130206090402 84
    0x80c03100034040c41c008662900b5001c89460041c1c684000c08400303209582e0107100410041ea07036002151681c43d40684900c10b0f0b02e159207000e03805046480d20320040340d42031404446034160b16030b01409405000b20105d0700d003d6a51000a078581c072080c080c01000801040d99140a10301941e4000581e15410041d5407620000704d440c5d9084410f5604003042441d0001814000c2c000d04201001d010a4212010050740c100b0500c0580e6590351000ea550184094041110341680d01f0f018490b0b10420441303850180c040d410301800d03220441191004020f04c500c03400f0170320107011400400c0503650542c4845071141c40d48001100103410142440f8842d0100d130071505846000d05049034001c141e480202d0b06d0030308200d201001c0c1941c08100d114003078040c100c01003006400800e00d0039044507082c0c81c010303980d1501d0f4504a00710300c120f8200185620709208006078010404a0a00ca914001d1004100780c1d01c5004003503007905c00030b841e18024600800b40b80c501520317181e002440380d40b4000f84010300c1d020340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16952731 1250 16951481 16951489
    0x30506130902012001060906050102010c0c060506040902090c07020406060507050d0e0f1f020105160207090f0204080304030c03020301050601030e0616031b050301030c08010204080a030c02040609020304080304120f0909090809 99
    0xc1000d24104ea6510360351b04000c80d111600440003c3d24007400203201040d100d0200a20070071203520083d04c0a501c0b074000c21080d0700c95500000440e07401400702c80144c9046042515076074094141203002d0f82c0382c0480000d0b40c500c18025940f0240e4420040d014002ca0300b2130484a01c0c0360000c4142e40000f10000700c0c0180da0b2480241c10300c0800807580044000784a050290031100c00910054283c032840400408003036010601ea01a9000e0700000034500011180e210001d00854007d0103052000150200034440740300b02c25000c5a02c00c400a00c0181c0c0c4100c011015168210701035013081d8001400314801d010180d4204010100030320b00082e4816083c090302e0580680c0442c00008284000700520503c05d060010b1000351038004020342c5003920b400b1a040c3d80b02c0386024042c00b00515402c4510440d0340c0c4e41c2022005001d1309009541b81d0815041074035060340b003170310109c0d52281c2240240706e00c00c0c02074041c060840f00e992220306445280050b414040e0918003011a40160f04201207000f55071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16953981 1250 16952731 16952777
    0x503010b03071209050115050109080a030302030a02070f0302070e070306050f01081503010204090c0905030f03040506030c04030803040809130b0102060109090501060504050405030304020a171e0a050a150b0103050613090201 98
    0x17000748004610314101c1c020035106009160003840c1003042d00101032003001d40006200301c07802c1e40b502e401a603960341d10103108000c0c051104c0c01000c00204416203030a0550004039001075458500c0080344545034404190b0840d4198401c194000d0060140740300e0710760040700310503403017034800d094494a1140c11001a00320b0384590016079120365254070007202c0c2580b098810019203c00c1e402007440b40185120150343e4020382c0716241c440c50f800030003e46041030400c1601c000310b43c003105241c0c0300d05283c900444550010f00406004486511405088490078000c0c0e00c3c0002c0189c002d03149590074a04c031440070f0000100252015074844800180d2600d442c41000d04c60703405a0099500c80c20030f4410001a03030140d81c0b24141e0100003d981300030f40000460342c041d4440c08543d9030803006040d8090b45080c040b20a0001c0c0860203040020014020600e00180d40081c01500400070f00a040005404a4105a0320241c000300c005a40d2005246254029280c00b4014100081003d0500c0610381c0190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16955231 1250 16953981 16953983
    0x60c010b0910061704020306011202030307061b0e03010221150a1202040b01050c0c060a0903140a03030b15030c090604030210020102090307060c02091f090204140307060f0503010b03071209 83
    0xc10b105040001a0b4408850280d4503080080c50040c0d040c00e4000a80e2940180906400a500c944180085603401c00031120020352000050044001138002200340700038081c258401b213110180307440407601d0180308507451300c0d0016540d10f0041c07442040c5803200d0301d002454200005501607a904a550310480008001d0801000041c038030b041034414407007030399101c9484505000d03091006440c002c00200307400c116020180d070a10b80300c070146a001c032034003a140d03400a0080c003003000100170080d40c049000500f441c002e4a0900c1500c0c0382c0424800301d260415030380c004802060001c41c0b600c41540300100f50300300c402803c080c2481e803a500003c5140d0702280a880151303500280300d03402070405101c2d000c001c06c07003802c06402801458011482e11980203008002005950b241d84103040c44401506026110010b011501d807a150b440e401d0704801407007841c81c403a2150349000a08144070f0744a41880d441325582d482c0c2141d203000044d5400da00050250307030510046039000070321901c29101c0c0701c2a00b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16956481 1250 16955231 16955251
    0x503030f041401030506090106030c050d020309010903020601050306010609060e06040806070203040609050d120f03060e0705090a0f08071e030203060406050f130201020c060a1b0803090706020a0f02060c010b09 92
    0x52840c10b0060607004805440a5040c182403104110a0f40c0e40c08040c2c2c0e04481a9003000b00e416200300c04200c0f018800e50300102e100d68408802d102c004801540710a031928426000c44d407050340c8510402d40d48030b009214040004031400000d0020501c00e403030064008401400c0c1c14101500e6a40032030070403100701c89010060388085400c1041d141e000f0030700c800800045d1804600032440c0c0e1220700b102c840340190407080c016600e44245003d4800d0380600300608a010010000341010a002081a4405400e80784500c0c056140419091440c000300e400300d4452400811317586203840414107820b44d004100103507202403444c0000140e1018401c25210700c0c4286070002d041c3c54045040c1c0c007051070140c425641c001d507012850006076000918054501c00c202c4040da212030240307c007241c40c00620109054071411040c8001d0422031170030f015601803402e81c0305070303003913a030325031000300c6e9150500000503103079140441d0101d0241c2804401080c50083d10000490760004803400700701005d8060b141780f02c1d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16957731 1250 16956481 16956487
    0x3030a1e0b0a0e0403230301090c17011401140a0201020316020303071706030109020409050105041109040c0510030608030304030f0207150909050a0207050f060a0b0603010e0f0a060503030f 83
    0x34400d0340c08004010110a04001c119018110001c607801000e1402004103000d0300f0070100e8103240c019065030b003001e8400248120b420b6580451031b46260403c1c880e451840d81816100e44000b4001c441e040d424101740984010302d68601161400481d03d0031036043d046c000d0428000c11511340360801003003162840d4001590320f04008a844224404030160a811034009000340014954408081c45030701c4840202800c00d919200006401004c465800135400b0385400072940810406401c180e00c82c60041d606c0d110480c4151050060021040f00c0c002c0c070807486400d042c440381c0703452400c41420700d00f0303446c0004400340c443c22803034510391003a1001c0e400306010505040c40240e040002c0006007011518207500c01c0110705015001d82c555004880710b05807501c0014844400c203a068500d100d800c04d04503110100c0c285d0601d41c03580b005441c81844581407080344005410f0420031a4125501c448072000140e88126100500003006445043e0141d220240000c0796901000a0302d180005d036a45196 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16958981 1250 16957731 16957751
    0x4020315030a0c0f0506030405030a0c050f01020c06060a05060306030d050703050909010303020a06050c090f0402070203010b10080f101202010509030a0b010b040801140403050702011404050402130e060d02030d03110c03030a 98
    0x1101d400c84e0b018031b02c2030900b04200000a580801510794420403400d103a0b07030000c444d15095013840007845800c4000d61010a90040841c0002201340c004c0500b41d8010000c5500ea1044c03103101e10044078403d816500500818103450700c00c2000300340e41402490003504198181002801d860300c280d00540050380004404010311440d84070303058000b0703000c95545140100e800c01281000b10a0385a0300d01c2a5408155001507413001c0d0401c8000b160300601144520038078100c05042075800340c5804110b600c80343d0025911440300407000d010340702002a1356254400c1640116840d40c080183c0b1078045c011000c00100160014141034042c0442020042e103c40c2440d41c0d1f642143c24024440350039920900911011030741090450705215020710344000d0402c0d2120002032640300d241e0210340c000d4030020300c0c48084c01c1801e48500076900c010b03440854588414003041440f0250b104040d501d0b400c04012038925a01075440650891a141c1c43c2c5400d0601c42a84035095400448050f074030b06403511042c1c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16960231 1250 16958981 16958999
    0xa0c03030f200901020102130806010617060a140f0a0602030a0f0201060b040501030509070b22050409020901090209010e1c0201090e0106051210080f0109110411030604020315030a0c 80
    0x85803000326440c108402c59000610b485040215001031100300c1e0006640d480381d034401e4040b540010f0103620340840155650b03076415030700c031001d116010010302c004a89002c402e0014000c5400f91070001e10010b42141000000d412012000308400e030300040700590001c1e01d45030800f034007008284680285442c0c0c500744002811071504d044c200c00071645400c1d8280444544903040e5070aa940a10703000030241e030750802451502403640c0210324a1030000c02c0f803062504501d81c0a1000d146408204035019645006020a4540b24000254040921001805180040e81c050a080d13101417400711052151000032031b1072100034980c03d040c1280c0544040040d5604880ca4030002c0c00c40c02602c0740d040d0b1516030010310a020f011011601e1701c2042e804584440c050200703d001914009098807562a1140301150080c4003151003182e103402d42c002400060700d0305210f00740350740b1060f0611505c0d59403400c0403c402075200518040e84901d01a0700000b440c0c404000d23350b03801d88104111045e050038a01d0382 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16961481 1250 16960231 16960241
    0xb040309080304030201050d0b030a0b040b040507060e0105090d020102070515030105030106060503060303220b0c150106030c0504031e0606030b0702010e011a0f0a05030d030b1201090201080c03040312020a0c0303 93
    0x1c90050b8010401000143d9011080710740b04d548404001828010100c0000d0806000c2c1d403014040c050400207005c18442c004804e64080c1c0d219000b11900e031569003105488451204c1150341c04100180014001802c1401d1140d041d68070502c1a40c114a44610000f685800106611914a0404001032001d810240310304000340c0003d007042d42c03c500e08840020b64910445030600c080d004c00c60054490720045d0100781d4023408424a4880d100c040c1004015a9407002e0312200784856060070001800500070b119103480e60301c0300d40c0c50701c0c5001d0554482c5400e5103e280c0840407904001070b0f40d24042511482805c010310b00c10f84140300d2a00300030700000d09488171201d9900c1e69905d04510b444151910304110390007107609941020044004500107200d40c01d080e030081c0c2d01400340d10520544164168040e090b030890880d00e4080510440e4545400c0702c0c04207000a0100b220340e00840c2c0f07102c0303004005e168403034030130b18000140c1a0444507078003d82c0c021b09032103030100d20748000c6082015014028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16962731 1250 16961481 16961489
    0xc030c0109120303090b10031103010504170706021c0c0806010c050d0c1410020c0f0c09160203070b0c0405030708161e150206190e0706030e0c0301151a030c0a0305150405040b040309 80
    0xa0125037004e84404a01c1c1d01484100ca030f00301e600050380000c000b110780640b29222184000b6890074805590042d0242c0b0711805844005508940020032540c0103c210760242500a0014601060f008905417a40c44843d402a92078031900d010a840000c030401800141c1c00403520b016840b1441e0b00c90311860484004401d0305a600000030800075a150502d0980d0b200c1c261000b880428804010280e040d407089580140c502d1802808110000310454028001c40b441078086488855603841896241d075034401076041ca40030402001c000340e0802d0014030309405054800b0025403035880d80c0c4880c0440d8100c03650380158011404200c40074200c240c00584410107600b0900505101c8490785464005a0041c0c5e000d043d56010405a214410004107100314009402006945114540120342ca034040c403c1070342401c80144d080b030498140005603401064150180c1c1d085c82c050300741c00d8002d80401007404a2408003010079042c40e54541c0070f6a40568080c02800320175081c942030007000d800d001e0304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16963981 1250 16962731 16962733
    0x1030f02040e030a27030f03080414030405060708030403091212030f020a0509040906060f0e04050c03010c050d0e1f0507020c0102010209100507060605030a0302030406020c030c0109120303090b10031103 89
    0xb100c0007141c0d400c080415003050301c914907000d01840b00800407842c205c0d141c1000d001c10072140380610805421114850082e802542d0000080c02900e0915543e4803940c01403035000103042c00f40e100002e0200e005160401e129081c51440e0584444119000c00a6100180c820313a014540300c00b802134240c49455030004c0b6100c415868030912840161181c440c2e030400d940500e42c0c410841e03050140646c0458082c0112814010807140c0d182d13041402141c1c10358060b61180188960850325160510131141c0c106403d482c5c40c0d00300b031402c81d0280d0091600840b0300d86a4011751000c86100030126025241211448000151a00301084000d2034501010181419a881003000c1400341d44e406980381c02c2d02d0024036155607180b050303150190290105a11241e010700c03650a030001095004005030040c1c8080343d084071111b202003010160fa50126a040c0c42c007180312807506209801040c80649c242600904002c1401007155450203169803040b00e40807800c160191083c420080b2a0b00c059903242c808030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16965231 1250 16963981 16963987
    0xd0c02010515010503090705040f020a08160905060f0d0c080403020607090609140607080a050306100512010513141819051c0c060c0509010806060c101d0601030f02040e03 75
    0x388080040d18109034020f41030010210006540f151b040140c44050034000e04103008001c1c206000da8060741041c40c1090102d0094400a030380c907462043e02e450090744903541c000c0c1c102e26110601010780d100005007403402500f0000500f04d544940510003045003565a41e41581c40c003801c0c0203040c1080641030000300000300004019070395100702414142c520300c2e114002030445550000b2040d1068804c0282901400b08000710b0158000011750b1044800f500c0b00302c0e83c414540c400b1620352081c000030004010454005210310700f0181c0304510a4419060006030b80b07511043c04040c17003403080320001c003200b6045804280c450000d00602a0b000019201422100015690140c4613001201c80d4100364028800943d412407213605400d41a0340c110504204503031042c070000b031043e4407084070140801c50980110303e207410807078200c07540310007044050100010150342910103001c5031444404440e0034006801c0c0f800c0c80500106009500c030740910386808201d8814441928441003c5e100c443e0828 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16966481 1250 16965231 16965241
    0xc0a11090108060f16020c0a0e010e01170307080706061206060501030e16050f0105160b01080105060f030a020918030a090806220b0603010603080a0503070e10020309010c260d0c020105 81
    0x110342c5904150f002920301e100d00d01c0d16004910349050002d1f0f00d540001c2184001901500400d8802e050312510000031030142e881e280413082c1003080341c44081855000300314a401040056004d0718600e403040a0100d0001c3e0740303010f03298030104102c0d01500c07800d036140f50410580d0780510071030001140d00d20150502d81c0064400c100900c04621031b060040070401c841c0c101c0381c2e108008444041680100256480070581880e86c10030b6824040c2e020117619100c00314085203091316404440403001402441209096400d1083c005000340c51042c00710762842c0342d84003601050025108004150b641d00c11132a03d0090114070b01782018000100d1841404900309020350b82c2d40c60a01066000545048261181004a40101030a070b01c0542420004280044016884001036000d0101550b1b841556812802003210030b90040c0f4104026a1041010280950051f000000303018085e1140b42c5054078481820f40c6050840300c000d040380f8000040440b07808109105074000d14880348000c10841c505 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16967731 1250 16966481 16966501
    0xb01050d0908040503030313030212090901090c090f14010806040513140307020a030b0103110a080601180b04020406030207170304050d0804051903081b160311030c0a1109010806 78
    0x2440401103596844910a00c24000118125002010041c0443c0d0343c2c0e1415900d000141c1a2805040300180100054003000c10304010036904c000038010405001d603460b0498040040280e44095800c0c0049828005607109001f140c1c4402020507088924540000c040010910f106c0140708610032490123041c40000310b4448040045550f00550700c445052841040324918016260020740c042c1c13001d01c01004112600d920541281c0c411600e5011108000d41082840e611601411003660300520040100f9444c8031071249450141400c009500f100c0f01c00410281c0e0303c66000748010a400150b5001045a140702d10031906540d610401e0071818980d90716074490300580c400c0c004010840c800300c1e0901400388084400340c04070800c05920360b0b00074580505081030407504480e4003071040e13021506001e110070031039800911104184002c0700306640d0589106668283c1d44020b440244140304100c0404c10400d81990300400ca0021249860820080c1e01c01e4142c0220302a0f40001041c00300c0904 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16968981 1250 16967731 16967737
    0xa08041a04080a0f080d06080c100302160b0c0403020604080705030c0a080c0112020d0507030905060a0b03120a230403110f090a1a040f0b04051302010c0305070c17100c030b0105 78
    0x58811201c180d00304c540d05040d085400f8164103180018030388500011800b000040070041c0841c10755200c1c085420780b071820740c00c0340075540c030780308031010009440c0000401c40f5000325030106024200a01b06600e9030085105904207400c078410550120905005d5454108a030707a080d80011500881c1c01801d1400e824ac45c1d11102030000c0c103204c805200c606000c1011340544245010f4024100542d2501010040240c40448002d4583e8040c040c0440c4401e08240984a46810050b0060082c540c6840c200c402541c40b141001c1c0401c50403c0911020040035880001503058070311903280c61300d00314248042c0903104541d4561045040c000410754603140c00246c907921264907038000031070301d00100382540e00759071003004154072920702612426041a941d2080d140408140c404100a903a001c6c0100303c01ca201200290214521000001c0002e10440040ac0031612480c1d00000c15603030b4403880101d400c090184160039800c4591081e42c0341c40c2a101c3ca25010348680307002c0c01404c0842e0006005c42c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16970231 1250 16968981 16968983
    0xa050f04080d0506030304120501020a0921030c060e0601080a050601060206070f03050702120d0c030e010c0203040b0309030c0d0801091a09011211130617010c08060103020306040e0a08041a04080a 86
    0xd80340d030b000900c0e03680c06000380e47c001e203c9040400c803581101c0ca001c500035031000e2100c1000c2002e20b000400c801d121425401d4140500b01200364a0308400e44040c2d42800340d98004480454503122099100702c410720847c1d000b4000000248100c61191030060709001c81600032204540c00101002112603200c82d800104001d030707007400a241d0311405402ca080ca1168803540b00c0c05880010100c290450a6008103021000d41c1d0302007100250300203089003610ba03240321080050b8001e0209002031001d4900964000740e00004407031a09402d125010b040503400342c04100803814003001007200301901c0c040d18444904400c41000e03403021500000e600110180507458803040b01d941418100310041c5040b1649440041c0003042c1107100120200251015006604003480b020a03070410302101405000a0744040f80c0321040b03280d0703e08004400070b400042140354000d1b00c82c1d000f90000340040c450b400b0501d00900f005682c440c142080d42c003502e40341240da40340d16101084104002c6002044c0e144402d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16971481 1250 16970231 16970257
    0x60605120a0206031512010507020c030c01050403080d0c0908010501030507170607081b0c07120302150106020a020405060409060203040515060d02010504030204020c010209030304060207151403061302041502060a050f0408 97
    0x10304400b2010503c9500311b19944402c41d0300e0041845101d0b600002c00a1003400300f20100d91640c0580b0004440600441c40020082d000903c41c04940340c2c1c2e541c1040a4461103860544111566182c400b420b41e00c0030ba10075911608681014012035142c2035900c3d08283c81d44008048034100340d20020040c0c40000c5c2141141060b411000300f44407d9201110481c40045c000c50750390b1601c3c0c02c4512601144000118094481c00c0c2c681036007815401e0790141215040d070060206074902c1d400344005041d0040815900c20f549001100004000744043c50082d40558001c0420560340003d01529810240103540709020200203000107030b910078102c4083c0d039416507000d070306c0e81c41c4a00c4a501a008114400d42d05000128000c90b5041c3e0000d03000d41100d100c440302080c603650000e4145c40366904031b1081101d456003000010401d007000541400748640c6001d005181540e101c20f100008108d90030b0803001a00290140856002540121500a9051a42103806081c035030384035060391144400030800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16972731 1250 16971481 16971511
    0x9040302010b0307080c030c1009090c0e0409111306080316020303040906060c1b0609030212150705090f09060f0d1103070e0a05070c0203070909020301020f07060605120a020603 78
    0x1054400e4110310411038003c0d007180c80741919030108586032000c4015481c040d220f601d840d0f400d10701d058498480956032a49803011054180030420303000d412200c0043c024040c00550407419a00c40b4803420401e00d003c0c440c1412024188820400c00b40e41d11301030802c0c95401d14078240075a800c080122403079000e04c071540310070040052010034114000c0343d2104010354680440068460f401c03641d0700d41828404d403840001e44d01458040c00101d2402d0244100048048005000604029841074142514442210740112811805260018040f101c05c0d000410214880020342880801403981e120202e80b400601d15040c00490b4800d594540114410000d0400c0c80003800300000303260002d04800f070291042551a4644802d4407041518880051880c01000901d128440d40c4941550780d40240508880d601d0044008043c0220741000d0342c1c10355081100982d0b440c5601c004101041c800c24021840034034020801000000c0a0381640607600102c0441c401690f80b4400c032a07120b2140d81c00124 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16973981 1250 16972731 16972733
    0x60e1303090308030702061605030129070516050102010e15040602030402060f03040302010c110609060c13050406090e07050616060c030605060a0207050916020709020307031503080307090518060904 87
    0x2074201003030360024200c1100003090001c480c1d4003203006845482c041038120b000100b00042103450380310074443c10083c3d5452040b80409043c0600c0100c1d0400d091080301820301d604d0392180360620384460b040b20f00f001e400720700400c541d5030203010781041082010003500b116084140d80a403035000041c40104019400000a01155208019201c500340c042071210303200e01d040e1401238001c1008826040120704401c01201d410040040c0c078521401541c8080e0840e5119001d181d031072600710b14103c40800c04040004202c07901c442c41507070020a40c18901080f48544003e4060900300c0e141c126130b00403c0704028010030b8540900d421844564090400109480121030440c02030450341c209a901078400282c4010f482d0b40014684140c51046078440f030315440303612040c250001c1c07039060900541c000c59010420300702e6640c040c5910884c036040c0403e0304d441001a8502c0070074544c01c119400c0d4004014420ba003a8006089800b03000c0a403110b1403502c1c2d8048200c09000001405280b080f403c0c040090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16975231 1250 16973981 16973987
    0xc17040f05030c0d090b04050303090d020f0301180b0702030309030711010509090a150f060e01080a0b0a0305030408060606040b07080c010f0e010f05060405130f080715060612060e1303 81
    0x300000350000c003607070380f0307001d0300c04070302e5290903c450780100090400007022510f401840116800c81b01c0060007145410340050600840004108090b42d002c081860072079083d032002c0c083c082d031210039100d00100d0342c003441c036105030035035405001907003194002e204120074401c002080312881038020400c0c10409480a00480d161722030703c42c1050b0880440070501039207210766084000814007200011500316100c07485200c061032284110400200c1101e02d544c0d00c4d50040485c560403e8044102281420111021402600f0303c0e42c000ca400c0ea00000f000c00c20b015040c0041c2d03400c00c104956040c50035240c0750f00340040e0b001f607020107002c041000640f81c0010400354031403104481445418803d007000c0800c00c038000c0c41d0380ea0001d0300350380c00e18001070101c0c6803610400e44a030881030141c0c41c1034601c5403240214010317241d10840f1080b031b0411000380030a2407000c101641c060310b16404034201d030404000410800010a00740241c905100080c0700d80200a1200b5a104401c2c164050f00140c1a040131 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16976481 1250 16975231 16975253
    0x30b0103030809120409050108100b060307180503070602030703080f04050c040e1c022112040b0c12090d031802010c03110106120b06010801050d05070b0306011e020c030706030c1704 80
    0x2d07044c04600001c0005085000b0f801007812030310010283c5075401900d403440c0c0d080d55112514954000c8040002805150140100c03000d400c4a2400c4040095183d0010a141c0b05030341c3c01880160340082b40e440c00b0540d100321015403000c0c0103105490a41080d030343d016030f100140b4602c24070030b6845140340700c141c1e10200846440641d0800599007a110a40c034081c0d2a41d2810010040365010340f1040415000c0d164111170f00e0007002004134455507038984415001e07143c05403604803456420418880060304038200350780110400e00180c080c103100d070403003c0c04541929150140e1148492a40d40141c1e030804c160560254150400e80084030819501c603004100903003000e00c1024227200c840042c880c1094609104100a0b20b552075242d0300d84003007109030380d900c8000903c0340d40115014801990070a02564000c9818100043c1039602141c0ca140c00050f0a034044005031301811403801c040c6070801490004240c2414204060780091600030003802c3c0244102800c1010311000c179040012180003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16977731 1250 16976481 16976503
    0x10302071a01090e01020a0806150702030303101d060f010305040203010b130204090b0102010509030a0309050a08071a010e07020a03030e070801060b0c0106150909050a0605040609020409050c04030b0103030809 92
    0x10210081507101e0010108030a000b42c00000d40341641400d82e24070144200c5284907071a480d60603d03030f664041040345034400704500d50610ba10a001110040c2c900b0009140a500282c0c48001c401d8100031a140310301c01c6420105d081c00c140002401259100c981100c0900e007000c2c42d020565594034000300c3e000d08500d03c070302904200300303901c40c02d84034606501400940d4aa0740741403060b411320b04012402c2e10426100c8403405e800c02c00015400c24003d902940d04036208000340c480c100e0164503488060707040000300b600e500324507002e500c80c400611100140542802c03420041d617801c01890003952019000001024107644803444005043c04000040042c40020001e1000c02c5d10340b10481d800390000d2088890940c00c10f200440d021030040c0812000a80ca540c421403258900342015002e0f00018110081c0365a58000c0070925403107902400c2c01a10f440e410141c1e03070314542030342501280c1b00100000ca29038410b000600024060319041c0e070459130076180c850401c0d120a410282001c1c0e002c80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16978981 1250 16977731 16977743
    0x60605070609060b090c0c010f09030905010819020301180e0607050301050d0f050307060b030d0e18060d0c090605030c0103060b09010507080f0c070501120207050c060c07030804030b04020405060a030c090b01030207 94
    0x70840a00301c0700008100787c03030500000713000b00740c941d814280941e1040380e40200810b000c071405200e154420925164484000c5080410303501200500800f2a8000e8028019001030600b03032440d4035000c0c0c001c002c01044403800030082442c0800c4001c18a00042c00380c1445526085001d109010b98010b0b24030715035400c14141c070340e1803000d460510014610a80e149010b40580700060303140350302030700000d0790707a88019103c0208056a50314400815000800145d030200b000ea0026000c03170601c0c1c0340d14010704849000080d0684c18541054a0400304e03c0c1e14504240c28124180a0640340c0c2081d243d42d102d080c00c2c0a503c401561034040c440b40585181c0d0340e42a130003c07070401030500d000141f4500301e58080e214032105040c58401c1000380d100312080030f4915440400841d8160400d08010500d440408007500c0f0895245c1e91520500e40c400d900c19120a01010140010344c9042c0c41001c1c0c000108840e98101180355907a42e80381c04440e4803840d40c1007545d4000714800d0343d019404480010394045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16980231 1250 16978981 16978999
    0x80306091f06050a05220311240717030708010810090f0809040603020d06090c170c09060109050409060b03100e0607050d09020907020a03020c0301061d0a090605070801060e04060605070609060b 85
    0x11031b40f488100161300c400d4030701c0c40b440700d84460b013801c0848580c500c4107450722050081c3c0c081c24802d540300798400b20007205e54510321103003810718a090718040e45c003404240d80c4200719545030907407861411780728400c0944e003203252081c100b0004002c00000010507500080303580e1a0005100014014041c0d0fa00c040d400c402240040301c10440340d80d02015107a44240712658020b174a40e00e00300407102c00b201a0403c1c9500c004415030862600c004200d030b002405241460500f6200c10116080c0c900c100c17001c5910355100c480e240c102e40f90501c042c003005228a80d0400c4030b0016000340b1591518054088000d120300018840c940b142c1c80e411040c0c0d20790f0050049582420f00400c025074540f12541c0a070018024492591260329060081808a5080c109202c00804030750b03030b4120f11040064140d0a8140c0d40d034603080001605800f1305803007860a07403038441081d8507140c0080d0203584c6c011601d5100b145820028001a0340010aa904054000b02c0004855040d842c001000b415030011050b4880c00034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16981481 1250 16980231 16980277
    0x100c0501020c010908070b07020a0804050607060603051c0212030906070f09030f08040801050609010315020c0312090a05060709060203031506091306090614090705070203150103080306091f06050a05 87
    0xd400411b00c1034868a90540c0c60340d15000200d0715200889802800074500304010007152074110080c2036070b0b601880000551540d20b136500c501e0440b488407003450259043e8000e800035a018407407500001c085040c0076245151950426480e41030040107078062000e06210490113a01c0b0b06561000343d94032104d2702c0090b0402d13041041c101d800a1003500c2440d82490300040c001c0c100101894100da601c050100c60390000032000002941189141250900c000e02058200d445001c00070342c0104212406031032420b6860030200e060100042c40001406040003040041071b9002040f658003555048100c480b10882500081040c03044051260b0b00014200004006040ba984498100c0e28094000c1080503030b506405500d00719140784142d480b400110000c0c141d03034000c5008052a0348001e0560b01c9910920407100270650081e00103458450002c000c12207641050703c01c69400c100c4c00d5518a15914800709200150301183c02a2410080d000c540000080d008400751821039094020034040c50440e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16982731 1250 16981481 16981493
    0xc030309030b0901150302040c03290319080a08070e0402030a0506091303020a0f0f080304050307050607080f04110103020c010e03030a0c030c020d2a0308061e100c0501020c0109 78
    0x40307404203a498041080215100420500c40d8800c0010820401100240385408000040c00c1d4001020185a25450104801a2080720020512030890150644d40300108289440c01c010810b20b0400600c0301c4103224007041d5107006507944a451498a05901c1d61154404c503680307811400c030980c001e400030085c845c0d0b003402600f200313100351029a030020750f903514001b04081e0b1078201c04010340581c00c030307424000103d26083c1ca60b110707ca002c0c0145c4d101c62040c555549185a204440a90b01c540010400d00200032050100d581c001c43c0520748012241002001301e0362400c000f83c00205a41b0b110071503071040740d02903019a5a4042c0c031400030440100c074402c0c07454a07540200c4a0b034031950328055034009543c2c000e02c070348003000485500502440d84914801e4421000c0104415090600440c028107101c00003031102c001a80310b171340e844086040c540e042c02804107200103e8948602c501c901c020b51034440500f1040509664035040b041c0401310b08003507009104072003042c2290750070a000581030140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16983981 1250 16982731 16982747
    0x131a0304060b01021207030806060903030c0d0906050301030c060c02030a0206040f06080a020414090901061a07020111010504031d1f02030405100509010903030c0206090406060e030106050607050607110a0c0303 92
    0x4007501c402c2c000311181000481e1500240b044070745111030b0030300008021038800c0c5000d17a070000024040701e2a190a4100003850b5404c2030b0040d040300d90058901c030034515400b1404900622403400d240341194190303901d450b609085401400200320f0110f04041c1503550400c010000f25402420f2103556581b20b048009900d6a1805210081007a04001c9400056144221130450382c200316060740c6804d1100400401c448094103000e02036480b6040850680b00c00d00c0f11415546140f0202c580d6000a880058400b24002040b01a2a40f402c801c100110382c01c15043d04910641c00902da40d82d8034a400014071800764840c04404601b0062203407106a90000005c006440d81282e07243c01c0074400980481790341c400d00c03907400d0001d000e441003000020f0040300581003142c8000d00e0142400e41510110741114910361000340015260140004242402c0c420705003e04005d0341c0c59880e0641544556540e400c0151110781048421404507040c24414040d2052050380318002040c0e0f02e03035074203000b440e0344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16985231 1250 16983981 16983983
    0x201021b0601080c060309030d0e0a0501050903030a050705120103020609270103170307020a0b0c0c010c0f0908011802150c070617010e060108070c08160501060e0a050417131a0304 79
    0x441207400c240b240d1724091050300d120301d0341d034001146002440c0440380050401c4942c032030114840c601d0b983c00001c8084c050356116041e0b200c0215106c0c0703491103d003400d90700c000c0c04440900130b0070480172100070f44412100e070550340c050b110680d8034403200010030250215114913111481c002015621142140f41829040301c1c0900d20b0203000c10085026a1030b03a11065a40d280580e0048051a0004035484032890703224242c4c0144c41c1c10080c0c0c0340401c030300750350041c80d0650000d00e080c80000ca90903040340615000c0c140c000020842c242c5803c2c4142d2503060904000785c4a191940900000d1100c440c0445228000081c19540d826542d004068101d414440c10003c2400c0e850700007150000c501c04807184580700503540d5802e55240d610f81611a07841523041540c002c40d00b08110706204501c11010420640700d48000600d83c0c0c5010014240c60030040c00c2884420304040500c004100c039480c06550351100740043c01d650f6880303581800e401302d501c2e5000c1d0880b80e102040c400039108404018612407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16986481 1250 16985231 16985233
    0xa0603050a060f0b030f060409080301090b010207090522110607030203030f01050603070c0b0403020114090708100e1c0e0a12050606030106060518041113060207060504240201021b060108 82
    0x2d01d4480103041d0480c0d02d20b020f0b903183d103c014800101e070044458210740c0c000740b0141001800e40001c0e02c82e440143d0003600701c001b51a80b900c00055031542c2c100b194600a001c000740800c405e050841c901c10000346020b034044840702c0c0c0381700740d041400501203c1001000e002800c140d41c8400614010303460b07400071201c4203010a403810000a0300c4c00c008040707a10802d2180c0c0c400c00d070b4102a681d10304c0780c120702810a40441d0b680310030360000ca00d80c0702d40a5005c1c500080007401c0c254030313101c030071845c00b18804c101d201c1090403c00380c05000f800002d41a0722840c500b90119201d0002144100d030281900f8210603400321500c0720021b0500260040c101a40d40618141c0c0d4055440c1d2040c1800e2f240c2600ca03c0c40058000c01c0086002044002c03c040c9559000f80049202c042d15007181626800824a042d01c404c8021000c000c6d40d03404100d581b004090b54101142018941b00c510307078441d034100c0100d20049480003281110301d8800e5045602d081d400034041c41103903142488156656000b40a41009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16987731 1250 16986481 16986491
    0x30406150803070c0504020706020d090804051306080705060309100612030f05070c0302210601080c03061609180608010e010905010b150315010e1203090117040201020a0b150a0603050a 81
    0xc4048003004940285030450340c0184c0351850141400001c0d840303080300b903032980c1e428040c50305401c4803405134082c0c1c1c6d80908542d40d1500c0c10881080010b20102c801c044000340b900d4000c012991000c0b44440440c1c004503502c94403903032595000ca0404000c014107500a41c548580807825462940442c0300141c06a030b00c401c41c00c103082d00309440754401d42001502515441c50104010719004042890201047c40881c01702401c86044500c2c000702030304042c0e400e0f008080c3e1074209003410030845500c800c801c903130380d010b004e81c1240181696040d4010500c0c518074000c0702010305200780e0000c0c002044510000c02590840c003021398000e1031201401c43d495401e04126180c7d070b2a084040e841400c426800252070340d21400180c0241403281c3c00d40d103041c0020110089a0350303490b102d90030040d60050000d5a41c40c46614001440119403082450b4803445d140140005070744e0005070180f01c60751042c0c0d03164150b01c0c2d02051440c60394654038526484081c203031000c03411036410340046028010220060107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16988981 1250 16987731 16987739
    0x7030f030e210d140306040903030204080a0c0e0c0702150d06050a0b0a030509071404330306060f030f0b2806030c050405040206090105210c07051b09131703040615 72
    0x10b0134042840480145000503c0800d255181c140d01c071a401d18402d050042c506a42d4142d43c50511001c0c08065a15800111041011020010a8940c0145032648451400107240c1c005065985030403410078034001c012880d81d0909446500c8000507100051921407141d640f180808a82d61002a000340000e01b00004500a24000500c4506451041d40a49220075500d4148401084a070b41500f0080c11404500c0740e0045170701d0300e07104064074180c100e0074240d4118100a0140c80300c07a40183d5001c0d035a5102000402c2c107607600c428080d41c3c0b2155541c01606c0e89403041a61007c4065850707001c0142c0000700724020b00e40da01840489120390010603095683c1d904101c100c5004580c06904180100f004002940c40b03040145962801441030856509030599104074482d02240c4942000c08000740080500004100c151402000c081c8030034149000440840c1381030801400c0c08540e01500c14040b010041c5141c1c40400750782c8160003650722407400381880e5024040b124004032040164690201d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16990231 1250 16988981 16988987
    0x5070e04021c0201021207050114070305160207060203030c0c010219021c02010b0a0504020f040e010603140a090c0b090102100203040614070507050304060509011103180f1207030f030e210d 83
    0x100d00b1501600030b002c1540040b0f01007421944100c00844082d562817603000c7c3c443c10480c1000d4081c4c40356541c0000d051a106441300b07190391024400c14250b5000c11020080b003a800021203a004906010b1280c450f00c1c0d00311401e0190040c81200490000b40740703244032181c0ea00043d025161041055030020306041010241c2c02c0300c1000c4e445540003100750303d007403080e03060a400401c2800a00022245010394420030062640c4c020b170040e00c006500c950283c8540301e0021038070b6401c1500c542007006000801c0c0d0f9211603001c01882110407854012030560741c583e000f404014051340c0b5031441555a0314003890007400510300c04d06040283c4400b9004190b165102d0401c2d9581c4a50110085151604121055640303411a04400741080314240030307000d075000300740b0180040c1d03001000d100e00003c9484c41003003110310380510424040c4c107400741070050254002640804517034000840010030390a604044800d010010445034020103a07095007203006031071481d03032100490480306031030b940b014442d012 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16991481 1250 16990231 16990279
    0xc030b04020f0f0711030601060804020108010e160c0201030e010204030305090901150c03030905280c080f0d080603101806060803090d060507091505090a0506040b0304030804080705070e0402 84
    0x40c800b030100c244000703114040c000c40100720131030182c0300081440c1d1400001a207015402d80001d00002c038614144001c43d40c0048801c1d0151070607002072611494000400750300d1030070243d68401005101480d0005690184e0b1004000165010095645607264200500f4950051a005010700d49a4000103610340071716030585004100382d5500002d01106071400c0380a440e41c0031041e00c2d5405210b80f64184045c41c006c461040040c00c01d2601c7d092503441c00c1201c0e802c6805ea10048064100d1007d01d11a01404221000892010300f0a483c050b2903c4001c0381c90240d07000300b0200b40e94a0002c541c41d50420030303810740b0545131141c40305000c51500e03440e078152280541040250400b403518200c0700000d0035030b007101383d20059501e809900d0551b64001c1e06510034555040902040300003e02c600c5900b00342c038440d0090702003524518a0149810492090740c0700080000c0c1c00c0016600102d01000101e82c2250b40341c542000844541c15103419107400a0390382a2002c904c1610500d140182c1c00307141d0b2040e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16992731 1250 16991481 16991497
    0x30c1305030705030a0b0406020412031d030a02010206072105010b220302010c06050403020c030a0606170f03030c09151c0c110606010305150d050708070e15010507020f040f0c030b0402 81
    0x345c44042015610341404440103407003125240d0b000c1c80085244400d078515029114003030f94600c60342c9140302c48003003001c48008400302d0003500b0404501c0d0150340c000442035000310061800140c8411404080241e04500b50341d01401c0c1030030b1000001d1480400f070043c0000c8010a01049030140c2c00340002c060640307080c80001e0100c2c044502c601d004c210a640015401802401510346c07001c44540000d061054545084411030b81e110401d001c15400d40d48040001e005200003083c201035800302e0300e44e407404003d2185a580c1000100c80310740d91240e0b4150150380311a4140680c4410229100807040613440c1c1002c00e00502c4c0981810740c4900c103440c241c170001504c4002c1d082c03580359140110060b1200030120094004030600190f840d482c1c0d1039080404502941c0648065410800801d003059583c1c2d1201d00c450103e0001d100901da0f8000300001d9181c004d08100d03948480d240f002c140c032107403e001034039405450401404100107164000e0441c00415503410855103aa4a040004a01403194 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16993981 1250 16992731 16992733
    0x106050301140d020109080d0c0b060109030201020309040203131a160903020105191404030c140904020a0e04020a0308030403020102130609060c0b04020d0602030921041406070609050102030c130503070503 90
    0xc2c210a542000440000d48900614040300b5454484c04100e1a201781100c0107000181da00b008481070041c0c0e0315a81d80c202030240303010b205092458000030354a000e03d1040324072070350740040428019000100d000c0c940390382c00041c0006c0c402e45001c00340084402283c862880301450880844d2141c46030106d1400d036035050b1205801d1040804c0b44e814603281c2440480180b1600120021303013100844090002188501000c0300c4241c00d01000ea2101d180e03150310343e03010740c18020500c40180e484c41c4070f04064512403e075564083c0d4640c0002100311915510243c000000002071000380b5506400415403a0f281030004284607564a9088031403a10602c91200015482e0200e05c001818022000d6007141c0000c014100c0441a52105422640141c1d03201c02c10354008000440068010b524010085205620090900d4501020103102080845245101c3e0700e00141c43c008101d400c0e44100c0d102ca40240085459207042400ca101e560707c58800280444140c036400202031600050000550700058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16995231 1250 16993981 16994009
    0x70306050316030311071e0612050601081902040b031003050607020a080d0f0207060f020403020907030203061f03140103060515060403050d08040302120a050304030905030c0108070f03090606080303010501080106050301 96
    0x44c038110b855030b5003c0c2150400340615000041d070b280344181407002c0302c140810b421003060728062001d030603007443c5004400200d061000b044540d0307070050030b540d81c040b80707800000c10b5550900c1550402032269401c000c80703100c0003005003e00c070440c03aa6403401381c2c0d209100b114400e07218414140c0c1d86141c3c450000308040d801300302e072100300c401a412800840c000706101608002550f0fa83c0010380c1c00348494414801c1d4041810001e62901f400b0581d08008181011403070750800601003000c160030b25000c0e490b51011282000c000f103100e0b91000c1d48801c0c0c070b11b040c0c00007940c5925100c1c1c083c0c101943c072208030482c0107505050764138000c01190f0440e64004010701c10074500510a90320950020402d80540c090203034040300701031487c001801064121f94485560313181902d000340c4078027059006180030381e0001c8100b0045076040b04001303401c41803606044240d496120070440180c0f0840100520ba2030070400b0000d0408400800f4605948003600e40c0c17035250380c80c1c890440b0107000900c65408000085 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16996481 1250 16995231 16995233
    0x100f050109050f06010e01020c030a14010c0801030507121104020c07031103010c0509120c0a0e0a0606050703050d09080d06080106030212030c07060e03010f020301081609020c0d1416080307030605031603 89
    0x1b044200005070060054510114161000a0400301c2e891426600340c1040c81140c0708041d0223100311100d88500d814a010194199161a59900c415000c1d0100301d80f000c1c1401028007400100c410040400148155510a00030352815140e8030a0b110441c3d401c80b07034600e01c0c0607a00d01801000c855955590300e05040424003000c005161004014098460007030309281450303a210305590720084c203541158a0b02e18200107401c40d00322545580603208000c030500c01c1130000b0758050121038840f0081a0046004021404c002c02d00b07100d01e080d500003c5150501c0060302d102c064100350101e034022079406000101e440c107001c2c3c81c1d224000740b80c8000e400c558400d02c0824014000b07842c0158003c2d000280c4180312600920482e0b2082c4c21400c03150f880603904820700c840d42e83c003c070f026100c3c090f0103500f0702481220b210b58408074010710707400340551003800742c015102680940c0c501c0c24050703605544443c018100507407158001d64149001a061000100b510304002400c00b5440008001e00f00a00d491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16997731 1250 16996481 16996487
    0x2011e020306061e07081303030221040e07180602070602060c0304050a0308090a06020d0e1e10020d090605070503010302090a0504080702010804020d0b0c040f060809030409020a0c05100f050109050f0601 89
    0x4c21903030100341c50501c01500455005ca014180c9103c04001409007142581006440c00342c0c01800984044405458000c07900c82000a0705d0840d034020303c0e020443c0e16686000c1e09c42e00c0c00280b24990600b03840380c00150352a4005140412114550240c44254640c1505103501c1d00c002c480103421030f44403a4440c400a4869075235954001090310030f64160314003d503115426644010303405c0c0303c0306032035000304540c0c060700f40031940000d89104005420441403a01c05503d80041800058038558040b40f0710181503141e8200c0011140d200b1000c008a04d41500040e0542d0001c2c002a0700815813580003400e442c59a116407405550008070b107605006040d070044500010041040b60030001030030311440010203000141e0300910701d4a007455251414400ca0078440c04590303010307104221014040c48074030640401258280c0317440b603601507501c0510b82000da801c0810400001c150b803082018808a401c036551110740b255007402001e000b2642e0314030104c8244d43d802d48500000d010080040780c0d02e580 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16998981 1250 16997731 16997767
    0xd1d0102041e1214191b05010c02101d090103080a030e0f060109090303110a0206060306060f0901030b09030f030c03060109060807051602040b130f15030f03050d020f0a02011e02030606 81
    0x15514003210084132024490300d100e82c0110a04a850000c064804103403a1846d48409002d00400c1c604045406c07603540000f225007110582080034803100218000c20243c07030105e0403c0e044002791a6504950b501c0c0307031204603584014000000a0726101000c031100d00e0100d11060980c440302c00070030607a401c21010303d00a014a4108400303040c0d0321010146000350340c3c000380c01c0c4100f4603005030204ac41c1900500d070070440300030f0085106600c0111140310f5aa02d0804850540390801c1c0952941d43e83c2548152035880b4401300c445840c013007c0308100140003601c0040d0302c2440282e88a400c2141d80382c4060307401d030340203840000c0840c406001e000c04648007074400d4170f05c4c0e600042000c1119001d9001095824034404461461540c1700c00400031541618055054250f0203601042403151071038030f42c3d4500c1f090700c0074001c1c100440000d00b42110009034050381c0b0701d80000ca40c4656600001007029008224890780c0b011078241c1e0b83c100c0a980d14481c4252882884050f001c3d03480c00d0f690020201e0082 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17000231 1250 16998981 16999013
    0x30f090a060e061821060a061a04170c121e0313050d020109090204060201091a040201090b03090c15040302100207081b030a06052e0b0904020d1d0102041e12 69
    0x4100c040d540e11180008a0405c492421500301800c142d090141650043d0340c03068100442c101031742d008482c01d10050204075011208a0340d0280401190014880d0428018111090344a070310840c602c02c0d90380b0086141c1040d8000315120f0713424990b40000964503401000c3c880396480007101d00410403800c040056142d000e00c14904100c003d5200e5001904a070030542000c00180e6486540c0010041d012151200e180e0b441e40140c000e030300d810360000b881040311b4080d00e00d8605000c07010510090040122488041c001030030207060208403645030382d060f0450303c005da12604d5502c40340c2052500101d02102a00d02c664040c0c140b20483c0b0001c0c0c210307000107045460b0588520414080800d266108a60103003d800810031085d00072901c010503000061121140007440c0d1803c2044000c442c501180c0000340d0607540540c651400307032182c100034841c2070300084100c0058202d40104e80c2041d030090098a00c0d040140e000d4043c0900746034214802400f8560640c0aa807a0a0000c180e1a5071411141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17001481 1250 17000231 17000239
    0x1030903050706060803040618050a030215040801020a020309041b02060708060315090304140105030c0d0f090b150a060207080307020625030207050a150c0212010608030f090a060e0618 81
    0x2c9561075950b40e04403035041d40004501d800218050000c1075122800802014154400d40029410040000c402c05800c3c4002403249a10284036041c03c156041500c000740aa24000c5403141c120f030380d01a40b83d910045444d4401d0b03150940030010010030b034603001d10104e0b1680c000c00c40d80d41d442c081a00e900b0400b805095041c89041c0007101c5140f840460030784541103110203582c650307141507444031358130184007001410300c61306104205050411300c083c2c5803840c034941c03808035204001203042c1c001044d803040082c0002c1c14440800010985001c124100c1401c262110156990388900490322410346008403560750b0400c02040c805842d144001d41810489400001c005114440340c9501c42803401c0740450150700301d0b02c020000c92405500b420010909642403151204420303800410031141240000c1c4105000943d0329800403007540f1100240064204480c1c2c2c800801026690b00d41100f541e9910501c0052008a1802e1084016551160020308100c3c100302c039200000d4003401d1004249500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17002731 1250 17001481 17001487
    0x30712050c030a031406060a02100906110a02010c0e040203010803090d0203031b0703120206010b070609050c06030703060509010b0a020a0308090f0307061406010801140f010203090604030506090607020606010c020103090305 98
    0x7000405000030b115401e52034030001a5040c5054455001140007030400b031248405101e035210081d000300f0582201614110001540300407072420000a24440104400c544008280108042e805600c11211910251501aa1801c4040400c401d900c003d0285045a40043c000d000c030a0801c55514660940b006081e00d0030070b11400c000c0c4000c18840e9141803401e5024050400c1030160400d0b0340000d0a01d03034409041d407581015004640307849101d01c010215079980c10800140b00c81400210001c0030000c24065a908080000030094060380c0103442c81600f014000103200c00490f0103da01409490b00a00894400f5072401d41e41e10700c2c000c164a090740078101c841e041000c01400100480c80c440d000000b4013480650000c6a031078002481035050146140c014010020003038100780c00102c0071965041c0348401003004034114041d41180c03e812030008240070041100c04504644514a000c04907901a81c900c07000303c0e81c4030400c0d83d016001c1145221a0000355100b60020f070780a034080d05000e86 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17003981 1250 17002731 17002747
    0x703030f15050907050703090302010516061d01060605070c03030503130f0b07030509010e0705041e0501032d0c0506030a0207020d0b041209061d0f0a030623010803071205 75
    0x1d6502908601000c486294800d02c01c0307150211850350042d0140ca030682c00e040d85581c010b44002c1280c0006414003c02180390046941c04a65031044030742d00490034054140300481031040d5060f501c2007080a5400c080c0003207a045e1240e8187c2e5696904210140c203403614588054800780d20140c04001d003d414803003900d011601c42da02c060040c0d0711a546002052030b000500400b1184064090300c12a4180498007100f068005030090642c0c90888000541d4402a142600000e413282d44540010741420b00000a11203082c0e410210710700d041c00c40c2c106d04105210500d8589800744402404607050f40c0081c420340c02c00c500503580c060110800145028410f80000308040300000d0120358040d0b210b02080200044030048200318107080c01c24407206814504040c140311140300d100e81c4044104d51001000c2d50720540c0e1018640c0e00500100c1c0510703200c0c2040c01c00b0f4520f040c00f58a540c07610740e0405607c0400c0140c060f048482400c040c40c2000060782e282d015214440c610700c401c200d02845140c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17005231 1250 17003981 17004011
    0xc010605030706020a11100e01030e010e0a03020709050c030f01060302070201052115040507022503020a060f030b060301050d0803040203010902060f04090b04180b07120207060b0111010c05040605070303 89
    0x2e02600b080d400400081d8002e1070100300c0310245800143c0100c085a20102c466508845003014908003401c001c5051180184114010214205524658851542440b00349a0007240203c152086480c2c10b2040f552203000346170142c030040d01c003401400d42c0c0100402846100f030303020340a0b4920501d080d614154011102390220084445240303007203001301c0f05002c0041411140920004002e071000e1002c0d141440c0080d4071104071001c121008501882080c910140103d01c00000e507500500001d2895100c8100030955545046100040f034a40840703010149007001c00c0e00d040312030041030303c3c2812400f50390300301450300040d008a1300f41d900c51025900503695000a405507110103992143c84614000310301043d01c0c48220000e0103a45800c0080d04004c0f10b48a540010940003550243d00c4e85450070100d0b81e5a01c1c0c0000c2911951010400c40d04200342c1c3d0300040c01d24242680c9620401c41d107000c8080c00c032a81045101c0c08544c0030002000b4050244000d048607030301a00340064488140c035a61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17006481 1250 17005231 17005243
    0x1060e010b1c09080901031503050105090a030f08040203030a0f0e1203090f0109030818060403060c0507020a080c0d0605061203071a1e040305090402071b0f0501020f120c01060503 79
    0xc040c1c54002090301060452161107101280d001e00b41c05100c0411980c44210703151189024145c105a140c4940d09032150740c004100b0300650340b000c020842c0e46000788000b600c4610070780c0f045001070b08200d1252003c17881211214002d60700200031b50b282c0004002c060f1400d0000d512800148400d400d2983e80a40c6c400200700008100c10002d0b50b030f80d60407032042104058541015505000c0280c0050020650010544900388050300c100c20342d003010f01c0300240d028040c950004040780d04115a400010380e109001e022068801d48048586a0300d490095403244105100c1907080814000c018020601c0e0341c100640020028058030010400c4040c2281103600000301601e440c90100d403d030b000402c5082469a0014018688818900d120038144003040000340c8003504010020488010665550381223030041c0c0c1d8001c010702ca1030481340290760010760041c0b0038840e00c400f00050005403035001240d42220180310401502031007a40c00800a060382009010006641da500c0d804640340e2810840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17007731 1250 17006481 17006489
    0x1090f0e010507090501020d1403061504050604121506030203100c03061214120301050a060f090509090d020606010f090302090c0909010602160602030a12050403030905070f03020108090703051c0201060e01 90
    0x1d8913180301d0500001a180605108107a4100064000c404441c102400c080d260004000c503004407515102001468081c0110f4204c168099000600056070505004c010568a8403600c0307055048080b032460041205c5103440080e402d03400c41c0c1c0e43e83d040c18449602c0900034086d0350400090094691500002003101420300b2149040d51500b400aa820100003c00789601c41140645c590760400003c9083e801d2180b00d44410700c042e140348034036a24000c80d280c00c0680b002524214203407408141041c1e0740c10504008034050b005010200d2000d51250821195901c1d20b0b46400d001c2c80d26542c288100c2030340080040030300d10006e004441c001e0f550405014002c011560051444982004c680c816052a030340c0400c040d98020401600400d41110f00458500b07070305480040c4035500c605040d80680004200281140100440403d034007407003a00720000d0381d00030f070307260501561100c075410390741c600c580006442076106026181c04068000715450140e0843d200100f10640e8441106104040a0b00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17008981 1250 17007731 17007737
    0x90709020a0e010207090c090e090304150903031115011502030c030a02010b0306161205090a050106030605070e01080903040306020703020307050604030804031b031d06120405010501030309050d080301090f0e010507 94
    0x2540002c03581c0c10008007000d00a40c1c6802c200c1c0c000d149030080d1150000c0d12a4403403c0101c2c800080601c0d03414010765004103060300079810804120350300200135010380c0c041100402c8200945220a0740c00166114040c408003141100c02d07401c002074640d44c1c54132490380702c0842c40b04000610491405001030035001c9501c0d0008614a11100c0400d410298001c100b03050042d444c0a07045072066000f828543c504003d031800042c141c85d18501c0074100700102501070040d6081c0740c000010024154131591081e202c41d038500e00380380640001140d4900041e81d5010160b4804d010910110f2182d90003440020f200b030045918142441c1d0300c25040010845043c1c02140210003003000b403507040002c0d280c2c00010741c0c5800d003810110f0307900039081610f18843d038802030a0b01c40c40e0064507142c4008454480039604120340b080c1ca40361401901030402400100e0000d000c88900069508011024104041e8070070096400c6a08084100008080040800c820780c1c0d12002c2c41c412050081c4501c1d4000c86180c0d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17010231 1250 17008981 17008997
    0xc120403060c0804050606100905090f01030b0a0603050705310203010306140405030a08070e0301090605010510030204030803070e0406030c0b12090c030a140a080307020601031202150a0203090709020a 88
    0x818901c080720b00d0b40b80414180b0140400300030014078045601680400c040302e0311101e94024002c100c2d100b51141d00500e401031403190511140440c8030054034120b0f03100e81c2090a0543ea8200d1280a444d401d04c4010300300d510091040c8542d1602c3c01c41881d1800121400d241080c200178030041426005410005a250b40080140b0901c08940a01541401c049220030142e09099451503070303034420412a035003002004c0e0042607441e4801e56480f030018900500034406090300741000c000818080c03240d18401e820300c955a14040d1f00a00a4030700b04e94202400d1b0341036540f85001950691200c442c0c41d5401980c1d00350205c00142030b4803d4030003822a012120b03071a800711a00400003008003520700304075540b00f44818241a0340006601a089030b015a841420300000c5000754500b96540750020030802c40801000003039903000403840c0c101c0c0d008602032030107002441d0042e621401d110701c0c0c2c442c4003412580042d01200280d00210342048880302100c8620f84c0d10058003089800c030f0800200010403076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17011481 1250 17010231 17010233
    0x1050714033001060302041d060a08100b01080105030a030936060503060f010f060c05030c07031a010f03030801150e0a03080a030b061c05071115160302030603060a020c01020c120403 80
    0x461002c82c058182e50500b1441c280c1080c49000c00300000314010a49172084034000390190319013151610003060004212864030341940c0300c58000d03005919107980041c01c00c80001803680307400030308201059015143e01d40c074541007042410135065241403800c1e814038803102503212202080e131059100380c4c5581000a2050503c41054140080980b246002d6140880103101e81c075100148401140c3c03c80c10410076801d00b520f44107065006840f100c00c0c0ca0b01031400c2c00002d018484206810210076045040b04a83c0c07100101c1062500900018001503080700052101d214403c5e140c19912003030b828a52103105402000811427000340d04200d075070b0a404a04091919010f000f104024001115554104070100c14500c807150030b01c4004d000d60307039290400308071541d008101032030543d02d0348000c2d22580240300c2104281e02c0c07404c0e600c0b89030310710345841c9030b204240c0700c4d20070b480c021180100030f8080f40d160301070540065082401e50540c01d55080200041100d0108458481895242d012645452031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17012731 1250 17011481 17011567
    0x80a03030e06040201021e01091703090f061306090c08031b010e030412060203060118030501050f0a02070201080411010302190305010f05010302070b07050315041109030d0207050105071403 83
    0x11424854031550002c070038000145e13004100114003140040c180b0b00a01c00f502076890240c41d00a01c05040c202403804944101c0303400d04c004500c940854000c842416110242c02030765890211070001160f02d1a4241000190317003904040c035104e00075103240d10055100d9104038150350010050341d00146010700c400526032401c0c069a4040d41a4070301540c00e0910300724003009a4544030780d008010541c0000003070090717070059070354140b1000000300000c0301e5910703842c00702d00812050740e2110485843c04000b400d206030074000c603680107506a44034003998549940e680301803094840a43e06040e0280303e2090700b0484000984070b81c0041d5600401d4951402d04404032681c1d0b103170011410907004000000116606124040d04060700d4078001c0e80e2641d4010700c00c981040c40318000c507489410840f01c96034503c00700000c0c2050f68405c505a840e124200300e000d0741e4450091040a001c960240300a00100c0c0d0150306010071000c880f0256883e002c00c4a120469400b54441580900700c40004142c7c03003030340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17013981 1250 17012731 17012741
    0x2041e0606020303010f17010f02070807061404081821010903200c0607110405010608041e03020d030b03030d0c02030c0708030408070b0903010906050703020903010b06090904080a020a0507080a0303 87
    0x1c01070001c0c0d49594103010280f00d80400501402080009001c06a00c0c030700e41c01d600840564844440464542c5107a2030301c4074440d8040f0a0a4a905003440082c88074000c83c1d28140e0b0051354001e4041d4580324981074030890403a0125000c0e0762000168408801c0900244440007000100d0800001c1030320042c075001e416480e07045c50b08c0f4201c1d03024402c1080e4495000415005015040310783c030391101c3d554646824481e0004501c5500a03040800008007180c00040130b900451150400c00c0c0c0c2520340c2016052960f258110140050344800400705100e80039a00900d951507024059900d0a00d04419440c2590704a650410041c2e200151184078802e051201a01802c0c0000107186400d10f481d124a90798201d601804808003070009001d685030b90258031544003140c3c0300c1400d100601e002100680207400c0490024001c0d424111300c200d80d03107000e00031036a071078400805004c0c440c0c03030b19140d4220035007202d064031055100d92003028020030b0040105e000100100401020240c000e03180c0141a0340d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17015231 1250 17013981 17013989
    0x105090d211707140d0207200105070201090302060f0408010203010305070501020f150114010c141b010905010c0b0c09061c060f030506070804030905060f1201050a03082502041e06 79
    0x4480b0303412511140780da07019055000000b0345065400004a090010304c80e2050184011100c1c3c400110b0204202020352844140d03002e02843c500d955011030019200e40c4900b510003030000b05603280c20300c010b141003000303080c0002820040604050701d0b02500c0e4226402030f0410f03100c80c0e0154804002039070307041007020803068003c0d028040084400807626503110060003140d0080050303882e10a410b9100d440707141902031300005007410f44081e6008031911242c0c071150780f07805042d00041c010a00d5024a0543c2c0c01c0702d10695401d40400c0d0b1944550a051002500d00d04800c0300411907281079940704006004c42d004458180c0307540802000381c010441d00607501810324002c03c044200b010650110380c156204069041003e02907a903894129400601500f21030342c07000f404140f03d181021000081c120030f98405024841d1641c82e8000c0040342c41c02c911001300801420441d000c044181e841071840d400710345208000c9106030b1640040c040e41c0390010f1400e0303134090401900c8021115401400010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17016481 1250 17015231 17015237
    0x5030405090c0c06010e04030201091e02030c030d090b07080c03030103030909050a05100302010513050406120201030e03160f110a030602030a14010e180a0c0312020d050a0207090b0105090d21 84
    0x100c0b8816140e903441e002c4c14030909a03410010000a01454001e4200e400c00c90b074401c2d85c00d09032000701e1000740e840c03026080050b4001d00c0b500d001610f80f41400142c040000c0c41b03e440761015a4540500c0d120503034040f58048500130820310012500398410809540030754842e844007980d082c14240410100c42006042d0100a0300704000c0c000070468642c2c4000c103998080ca000d554855041c410035408032000d81c0040c4d00285400030010b0500c1341c00110080c207601c01d9909014a1310411107481c6e680c020882900024101d440080000031000c43c00110106d21a803101e41030a5140d800040c07100b40c0c56402507075110303000010072003441e14074407815448007508501e007203003035041140c110f41a840003481111071103002e50b91200780c0807081040d008404e5020050b2500151245000e4182c82115184500503101301d2080140d00e901034010741b0782c1920309500500b86580b07801140c002400b81c0c08800c905020003000021600d440b40c01361110b031180503100b29100d01d1501111101c000050004107020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17017731 1250 17016481 17016487
    0x10b0907020d0e04050a090f030e15040f0e0403021e0d09050d03020a02010302031906080a020109170c04090c15021b040606170402010302040b0a0801050411070506040b0c090d05030405090c 83
    0x600c1d04100324038142034066030005400d03543c6c0c082410080800200c080d0400454403548820107510040000d1444402e0b41d540107840d1180c0c020103120f0040b402848800403240340248248510018150741c0300e4001d20450308512007101980102401c007420100c0143c200901d82c1e9156a0071a440e0310041100350340300c1e164142c0c940c40003900c402004600904241d000004140c1412071100844812214881b0405ca0b079550345103940c0d60781c080603000b2030115018100c0020030986503040c0d02441003a40c800f408000d004c0004200040c01c031402c1c11281e000311300c54085a0503503055400c2c2c003240000d800401e505124480c8010f070001d884001d50f445181020003d0042c83c4e8089903c07801c0550b03000c241d4906407241c1c80181c0280c02560030007180802c0102d9914509a8000ea45504840060300d041080317070f204540a44c284d00c10208042c1903680a0f601040006070b030544115806100d13248224108680c1c01d0024001d0b40d6035550640380c903807000c1002c1c04246803840c0c0c016003042603004943c0c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17018981 1250 17017731 17017753
    0x4081c050a020606120f0d03020405040f050108060406090f0f0305030f1f030204020c0106120804030b0702120a050901020f03040f030b10050f060708040b07080a0338010e12010b090702 81
    0x340d03801d0020913181c09a0a0081c200001c22001c00040040740d89440a403500d620303600c08028000d410510880b80f14505001c1002d01d261aa4402d1505941b01800039108a5a858039040c02070500c40340c048440510b26442d000215144410040e2070901ca9a1926501e00f23113070079501c81c140c2e0083c1021002e1301206028240c030340d9900b018403088a50665015840f5440c805c0700341e00610240c3d0080c1e085503104107000041100035001401a40c3c0310303024454607519243ca0890f036030072560440c6017101034108580001a030051010f4010b00c441441160424903c2c401c1040c15070b04194010140f6a00c254018010071400808007a40003c0d070920100410b4070300000100c000740c1c0540d240740100c100181c130b2000d1040450880c0c0241c00c2500131a9595040361900c104170307a00400e801d40010349481c140c9041c40507518400e03691001c8a601c01404107000714807050354115030380b44244c1401105c51001c11280c8403c107a0f017a15021141c000a80c420b0781c5000d00460b49802850039045400130742d400740d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17020231 1250 17018981 17018983
    0x50405092a060c060c04050a09020c0304060c020f0a03120306080105130204110c030a05091302090a09050c04090e03040305010510150f0c1401090303060f0e0402040f0b0604081c050a02 81
    0x10066068040114014066403011400603c2403000c1010305010303010030062810344c03210003001225401d0b2803400c40300e980c43c403181c4124058000d00d80388a402c104001c11085115003c01064103000070f08880b0703240d64140014441042d80c3c0d104441d80d081040640b0030254051240a005000c00c40080c484c41c5802d001000701614588030081c41940c1c2e46400400d401490000e682280641034200e03591180c01c00f4001d05241c0058440c80d04c81c00c62800d9112032501c4034000d0781c0101c074025089042c4d103130030000198080c0100070044c074104c80081c800021062601d020306190003c110015580d103e0442c10101c2c00c2d0360000302580300c141545030081003007000624031124140d40c10300c0e06901d80d0980e0b0104030b40d911000c4802400518000c2e1182140c1403065000c500154800d49040000315503600f125210401075100b40c0700582d01010000d009410141c000042140c2c80660004000481d08005101e40d009070b0003990955010252a40180c00010b0f503240c1014480d050903170034490750010003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17021481 1250 17020231 17020273
    0x1509090105060307110601030503031b0405031c1103040b07050c010305010810020705070b07080a020706090803090105030915040c0e090a080405190b0c01020c06061c02010f0c02100302030105040509 87
    0x1c6004400010004852a11078030804034a51070a03820349013207507901d0410959030380007500c0a41c00c42200c0224080030280110848c2d0840c0c1e40074004e0031059101c61443e03038281540d4503a03241801046403051a600f14140010000b92a40110068550b25641401d501d440080685a4145881c010042c4981c03c1c1c0051030b0180e48e4611100903a580401d444d250f8200151540b02240c040000b14080c010800c000f0060034902d00980d0840c4c6002e65100d00460b036520b510711680000707804c1005203d00b42d505c240e0003960300c40301f00012660f07070461104c98541507000031036054950120050051056550440032250058004c500401c00d00903680c650750201c0c82a445000d120750000c040f40006642da60145500800d12044440e40300d54410703410034080e6101c42c0042c1d40f180a00340000c2d455103030412010104c42d0009404201c5841541d006641e64030710750300301e1402e00c03045e06807200046c0d031866201c90607000c140e9000358480d450071050006480307000d82141215000f03030019070300c80c0310350481c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17022731 1250 17021481 17021489
    0x924060d200301090308160c030503070302180904030306080d02010b0a0902090d0b070e120f0d080907150c03080105090f0402220e06010e0f070203040e0a0f0207030e15090901 77
    0x9095404210001d002200340c400750619015402e004d004020301d500040b80621404010488260304001503004803114500004001c020820604c00300c0c00750362007a400742a1100030000000c080307400340ea00184000008072012400262907100074840b0f12018070100c003440c64680003d121309155480042c40c44c0a0070701842c005a41d0105001a0a0781c801d008941c1140d00542188124100010020400d00e8109040e60244041c1241d885441c1c86c001010092030b1540400f6090b0504100e42c101c0c1c49020107072170b03103a0a211f81b10010401202002c3e4441010903240c0711818016512b1901800c2140160720007446515518100011108000d50041d8002d50403201d0302e2805402e04030780c2085040d40d100e00b24195141a0720350301401030005040381690a255104ca11d2507580481418000d8800c0b00d100e8016002400200250882d900341580c00100102c80030802c08500c0b40c0300406c80c2c2084030160006a0860494005810440c0e0800380c21000c1808035031030320641d10007180c0a1401841 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17023981 1250 17022731 17022743
    0x9140106020307030c060b0603040c050306010501051606020d0e030301081606050307020a030c080418050402040b060a020312040203031204030302092404140a05090907080606030604020901140d08030924060d 91
    0x117211040006550154400d101d00615040d101e00301800c103071100441a0182034024890040007080540c00b03181078484240e90540c5900c1e201c180703a074a10001c2e4000b91035070040280c5902c5503003d5108103001442c084c00b4004020300d483d010303050f01c00140e03040a5100b50306100007003040c888007e602080c0d8110458042c1071110007142c0901e0300300568031072540820365114000b10000b130f42009a4201600035402114288140e80030542002650720a28498001681c41040608944400c00c04a241d1160008081d00c0c140760181ca041a0b020408913001c400180d4001500328061800d9164680320b2151300b070000b1440b504940c07460b0300500c50f074050340c280c80e01c805104100035502c8081402c064400549030360740600340030300e1440d0745024038041c045190040e04c0029200303080000e081ca1045800908100b1070785d11300800700421502e0011840d420a440e40244c0c40403a2022006500034a2a41c005007a0b03104038000e86416104840c00034001541c400c5d06005090759000151100c3c80e410070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17025231 1250 17023981 17023997
    0x50403020603090c030609100f060b031305070308030f0609070906081f030f03020c1302030c030c0a050c0f0d020f0604170f040e0a05060103061203020d03240e010914010602030703 79
    0x2000103071404c1c500c1e6001542c5403140e04100200080b01240703249240d001c86100384550103e0b1030181c4241c131054000d00b44405400e01c001105480d880d164041406d000c0d8040c2c90560f51251600b6181e035104480300c0030200803507400c0c0246401d040b10115807200403890514042d50822000804910b0f02500300000050001c03120b5071500d00c010b00c00002182c1c090103120a110543ca406501c0d00da9211070300788079541e4110366511071503c030700803240704050340300603240b85a84040f40904241c0180c83c42a041010038840000103840c20404480c4040400c0700038050100f480200a141c0709000d501d401264100380140000601d40d8030140c062116803860043d214000c005c50340d0716034040ea60103040c083d217518052200030b6106d580310a009101c01c1c0e178180324068562844206c488803e64000b401a442000b052500a1183e4000741048a6034800c540107032000807009481240560801d1950f20b0f41807004010511591041c0c030203c40d05060a1a102c0d0b160800103510b174084c03030703101500340000c03a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17026481 1250 17025231 17025241
    0x403120e010b03060405060a0e0a1a04062c01050106020a051902010203120f0106120903050306010e0609130501080105060d022202040f080c031005161202070206040b0706060501080601050403020603 87
    0xe41040c1d004242c05800c0352420700d0729044c1599107040c00d0320210300b440c1c035085007491094004a80502d80d150003000c031811f6140d0001100d244400002d0003030764090380d103050100004000d035500040100c0d0b07070640300c0f0303511205041990031a20181e03c01c005641c8907000900014001140c900c0f60f1141141e50102560001d00040c0e04510803210b01c0740a07031030345008018050021402c00d9041e20029036031640000f10180c110001c17914442000303404a103090002070b00039031240301351118401d00581880d0504d50040042101390742d8074020a00340544071001800460400d2103050f52004045071501c00d90b9820303402003030b01d07216041400c00440c200c0104c0141300005503011580141070308024110b5043c1ea42c12110b440e600030b04c0e4050b00ca406410f036020207507081d9000d814011068031501455130360211509444901c10941c001c038003940c00344190300243c0d5900300900010507610300b8440d50b50b50305151581c2103270865081141400001c0302480303100d903400382c143d50a80394182c400c3c99803a151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17027731 1250 17026481 17026483
    0xb0a03080f0909090d0f020706090e0601030b120a020f0406030b010b0f070506070c0506060306010b031302010c0b01090507091706070509040209030a030908010c0207050f04110d05070302040e06090403120e 90
    0xb0324120940200410041c8501300341c0024452561088642d500441580c80c0d1504988031956407041c0000901c0b42c80c0305100b0181c0e01101c003904074205040c000307002515000817568011200f1549807850704498000025801d00c50083c1208003000c07102084040d0039607450103140300e418020038201c0000850320745c88815800040320411504101250a1485d000900400712821034400326858040d0001060440c200010098103848906291604686e503491100c180d104002c131042c0e04200082e929400400c101040d180c0c040c007126180801d05207024030000e048003106c2e62080d00c8010b2400c950354042e0340e01280d650f4000c51145085595003c4040025019003d1440340b640d050007240e00a80c03c05400c0100e0304200c0701e00c10000d2110b5440900c050382c50740414498241c0017025004012404c0c80d19074000d41c82c0d031920307081c0d56013406e40c0082044111482101c6900120b07500080a01c038168a8521080d8469011645000f03603140940d00284000030b008403200320340c0d0701e5441501c11068 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17028981 1250 17027731 17027737
    0x303050601140d02030a140403081503070f0803220e040206030711011b020c010507031b0c0f091a0604030201170405070902070305120a09050d05070503040504110d0507030b0a03080f 80
    0x6040007544400e03c142c6008020f520644036226428a4500308081c03010403074260038402d40d0142c8900030f15550361003118010b01c00c0d056059074140542c00d004156a40c00c3e880344c1d40a8582c071030082d030303d07015003013004804025204c0800e414061008070406c43c24030500119179010740d05a0340b0719202e0b111a00c064841d60408000408594288003101292500c0c50b806c100640c0070a40c211216607040c1001950944503001010380000c03204841003180708521500d07010b81503c150041802260b0360068034000c003201d0381200c880d0760740710b18684120f80c13000c2492503c4d8042c1105c0300c0340f801d45140d0010348185003130f100c0c11200000d0040003030103010090044c1c2005082218082d5941d0380980740007425075020641900303200304c1110108a0a030591b2045107003450340407005050303c22858005464603088050304988921040002007002d448500454810603a01c01c04d0586a030401040c030420303120018150800c244c60039000341819a980d48164084a8014040603034031101b01c098808170384 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17030231 1250 17028981 17029007
    0x1611030d0606030c030506120a060905160608010303170c0a08090708030a03021308010204030309030201141908010501030c0f0905040b030c06030c1e0705150a150801050907090501050d0303050601 86
    0x74580280040c00340d4064125000c07500303007039408101319643c081c20440c076200040200e0721243d01c1500848002245a4030205074540508200d40301a2030690010070045600d8009000040c03402004008254101c881c103045070070028642c0c44c1c0e0b03180c4000a51501c0c0101c6858a0400070002c0200700d8401060040790050100b18007625600c031013142c0e000c1c029500c100c071060041a01c600b4001000d907010703c01e5401ba00c4d41507032540a110300e550011222048003101020102004101000741e442660040c85400c941070f4840b90082c4d85810005801c682840c0700113000d0140f0007100400c9694003010300740603510100d400281c0c0c00c5926000c40c0c54448002042a0409000004c0c03000c0700001c00080c00f180003581704000440d200c3c41c511001766004684004002d50310004e440d90314000540c5929600060070000014184224a07440d0b080055030703841610749035941c0040c0104003105002c82c0f0060900c04c0d00034090f551414011454441d2604e0307000d0201599000403490076846081484070034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17031481 1250 17030231 17030257
    0x209070e040501090203011503140c1308010507030903110a03080415020f0d0204080d0512010501030f020c0a060905070603060b030a0509030c0303040c0f091a0904030203041d0108010b01020303161103 88
    0x5684541d1003c009600a01801408d04012180e021780b0304d1190143c7d4400d1503000318601101c0d2220228001c460700162507604108400304000304c4c104d502441094841c42c1c40e0b0380d010504811908019104001ca821505800d4000b0052080440e070803070740d80358103d6402040301080d031740c0e02580303140280103210242000d03800000320114041d5294010b001604c1380c04090318200451060705032054402c103020001e04103182c80c010440da40c0280c1c0100e0b81044030701405864034008880060401e1200c400460b4651b0703540c0c3e654020703c54100007010190019080421100e420503003c403a032030100034400704850380c6079000108441000d000391444018020f0407682c69081a150040c4441b01b540661403a140c1000030001d924071490050a40035900013040d00111010701c0180054bc40c0001c000344d081d48403c000000720910521704000100b110300c2c0c0c40a0103541842a001c2c00c1d640025045811944107109108a41d905284001907810050808264039101e0082c034a0a50142c00e41845c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17032731 1250 17031481 17031491
    0x1020f0c0a0203060a0e070b0307020106050a0306051b130515040906030b071101060b03150109080304090b030705040b060306101b0f050f010e0709020a05220e010b12040209070e04 79
    0x1400014106003100d10850a40f1020717640c41e140041180d0602580c6175090340008010421005014021500089c0600c004103546403101c010501c1d02410703034000c407030346070344c81c0d08001140355601080e201130100e15040a04c1d2203481d160030301503800203000d59482030600030020180c128102c01120020400b060061001c1c541d607041c5140e107000308644000100b0b0f0714110b81e402ca07280c11b10902c03042e2000d04c100581503440d00303065803544502a007aa6810711040d11400b1590940410203407000b855038280208e814981a800e00d818a50240c1c4558003d60074040e00f42c807503544200949a03c148169221100440e903000301b1240c0c0903602100414240e01d0705500c0040c8100300807003c203000c0c0070350204c4104400d400d2141d801c079410011031400c0354001b00010f002200b420740040c02400040e141203800c140740c40d0f170181c0d900c5001250304202800c402404200b41d0042400d0705006000b42c860b01c0d0304010394920340d1081c039000100028890703451000090003842c0291011142d0b0080600100301c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17033981 1250 17032731 17032747
    0x1c0e04050a0603030807020304060c03080402010513090209100908070b031e130b130c030201030e10060f0305061006080a050c0706050a20090105370201020d0b0607050a02100201020f 80
    0x40104280c0c0800d80000700c81d000046d860701d0000045800b03d0340160f80d000402d0980ba00d0440300c200003d4401c80c100007013000f00180021321036480c1c0d0050001c680c401a61614400708001c0c007144800702e00414401103420030842c181d808514481204e50013440742c1c0c0e4a9030f55213168500d64540f11941110f001c800414007001004c00c2c2204030315a80702d409104030580f541c40c86c40415035a032003c014500603079550140700552007504125042440002141c800c3d40e10082202c0c15114142c05c40c0c0c00306513862508106211040000c1c2c1e4106160034203854031181000b1004140754401440c8803901c0d922080840c036080c00780800c80f101c007500584200128200361442a0103070581d010040e0051400f61001c1c400305a6690844403814016100d1030f14000018041c640340c1c0c40240380b1503231203a800050218000e68542040000c040d0640d0005980b0401c04c142d001c1111103003110795000b080c06000c4800003410000e40d5801041e011150f071842d01010780b01c2240a13203d051580c110300d40010401c89 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17035231 1250 17033981 17034001
    0x3040509041a06090c03070f030204052814030607050c03040504060617070905010c02040e0c12030a03060803090d020603090c060409060504051815100f06091401020f1c0e0405 77
    0x2c2c06286081400b0031601d58004012400005581030b0748000020004181c81034010785800c0050412400c0250800d50303214009080c0300211100184281100c5500400e6682c920303411102030310088940340854400d0f48086607842d0320092282d024404001400380b04140d080081d80d00034240200300b0301c00340e5240c41c00149460100381c0602003c001620204000341d000765808410b4840607500c40300700062580070003024113280c2c0140c1c44c40c3e00072100c1d154055121181010f2416041e20011651758a81d0800141100c645900c04100340d00140400350b8240e580010700c2c060b0a40441d030b02034032503e80c140400c1c10720300c118802690080d00004c000840000701d4000c0e1040b50300450b82040680c1d02d1000880c0e401e040060600f0041d0044004000c24141107080c81e9082603203000d40b1100742d074075140d44072030240d10380e005440465040c00303003000401400d40c040d42045070284058018540c0e541d1240382d5840d2702e0751440920522403100381c0c1c411031051512207461034008ac418007950422341804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17036481 1250 17035231 17035253
    0xf020d05070f0f080c01030903020c0103110403051212010806090d0c11040504110301110301030b180304080d030204050424030b06010e040f0912080f010b0a0309020d05011b0201060b090907020304050904 89
    0xa180714085c8458001080d03000e07101c0c4094858168010f08842054200114010002202a00041c820510012022403401c000c004a20fa4800311080c0d034401e400c1d880000c100805031b1100340303640c0c070080800100c00c202203000703081c2c5002c50400c5d03640c0c81c2c06440c02c5a45802050305640c4c10501d00400c0106001c452242190f40b0395003a4001c0001042c0743c214651548024000a0801e9802c0c002040e03401c400c1c4801e024920b22500240c90405440303805c15030030104200704030b60000340c01240034042840c080c0300308050300718003049a1070403124618800902c0001440040e01114484c000100242d008980d1400311201c001c02c104050085907540c80c008106180050f143c03540069010a4250b004182041c01004900c50750310b030b5a032911105e10030f6035011042030400c05889421440c0142c035400d40450403075104c0e0001240300841c1690800e1041c044003c0c801c21681004410003489a4440480320019419100b0000540e5064010fa140d44101e03400a0340180b0584100014490500c0b80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17037731 1250 17036481 17036489
    0x3050d0c0b011401050f09041112040b0a02070f03080a06051002070305070803031b0702041104030b09011a06040e040f17030f060d0308010603050709030611041805040f020d05070f0f 80
    0x40d5081d030340c8a1064031100380c544064140030034000c00c210b2441c1c0c403108025088401004001043d60040d00506185035003001c5014030003420282c061104114811138180e60002c0b142100b1824071440e0344a12a10b41000e0201070140203440b00410401d030742a400c0003004c4c100207800400503c00a80c0d0003075841042e4032050340c031405080004990503a0110859005240c490001e040c3d00850301070800c101c0c0d0120604a034419916032039a0f902c0048000030b04000e600440c3e8117055460311140160940f21201051410f41054419540c440d42d00e40050300d0035541c01c012a07051940c0e441c41c0000091002040c090950040052400f1500900f5001548141c403600c4040c042512a58140508000d0b43346000b00465020001803020620070f501c03081e440003103490500107242d52034841e036086481c0300703a9400111034000780a2201c00b0441501c10600068084104100d21f0941c42e0141d03a02c01101e0020f10410740d5160390010700070104007400c05014103203803410003107a540071907080ca2440380c82 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17038981 1250 17037731 17037743
    0xc090f090c091207050609060c0304090924110d090303090f060c09080a02010203030c0c010b0a090501091103010803040e19020309060103020a0801090b0a020a031104080705011103160f03030603050d0c 88
    0x144083c0011002c25180d003280d102900140c14540764074100007181e000040c0348400c921040c400040c011049000342c2c0c413018025508400c04160300c000c18a0740352901245100d881e81070400443d00100300c10225000c2d0302602d4000102051186802c40180c0b036513143c040c0c00521804e00e90000d10003254044044184180c0b00c3c013079100c3da1652015194200c065019003d60014800107550070001d40c020080c20410300000500d082090000541c07195203600a035001641e02c0e001400500c0051040148c0c000c0040f40710780c11503150131041507680c440e5000780981e08a050011820b03404030780030b040812220b02c9000b591a071501d06c4007503556107024403007a8410444480b002400c0d21061103602510f540148501c0d106540b006000e1000e036002c3ca040004056035000500c80d203000b400b001d00094241f0740e0242003900d2419000400b01e14001c0389064254004015074201d0841d10b8401e000c9007540028481d903140c803d41800e0b030041c8000d0b800603080740509000000780036407100c2c4189405204103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17040231 1250 17038981 17038999
    0x40801050603150f13120f0305060d1104020a051204110102060112020603060f061306090503060a1b0c02060403020406140103050a15050d02120d120f050f0c090f090c09 74
    0xc04141e070fa1401c1140c59001103400d070000c560269080c00300a60700c24805442854000000e9a031580c00c2d80c0c1c00080e00000a19840e5900002c55042c019070b60000021a6034070700070b04143d11130483c07403100325596520031a1700250400340789000300e06880c2c00160001840c40366103854107015509200d6020300900500a600000c5051030301a8100010707160081e007181c0c02c2d6a548810311248948001406912035418401610702d412130001d180041c014960380c0c0e041940c1707048140351600c42e01415030b207401401c1a180649440c0320b42030790181e1078014078002000d04064008210507202c1c6801c040d40041c2002c2000c6030510f205924031000c14402c1c1e03002c00041e6200003d59044030000508042c070b1901c0403404110510f00203141c40714140c0000c101c0c82e0306c02e0040700201d01e40340d07a140c1c0c020042a5121100c1002c4c00040c0300e0180c80810080050005140400c4034030030f440002822507d08010100d00380809490701c0d218940d40d070f00c02a20500c264100413040094a400120020748100083c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17041481 1250 17040231 17040241
    0xb0a03030903050c030106060c0609050106051c0501050903070803070f0c020a030605060310060b0f0c0c1f0215010f050409230705042d110c01091101110d0206011a07020a030804080105 81
    0x500c100004c0781c10503990048031502580c1e0300e2b40500014501aa115900c446010030240d90399038130007a1043c8000841d580316000b61030070901751500180340310141c1e0800e10001001c00c0c0d044080303941c842290f261074004c0000800342507503610440c0001a400065100010041218607402540542c0e41201200e02c07a0741d4040d00031082d903185000d80d288a400c2488110703d4004510b014100030001c2e10705072008480d0316404203082d40000c0040100a41c4070f50b1014800300c0d01481000c1c0034070002440482e0642c1400c804400940031407050600596440d40d030003040c0441500046038038000442210664121300c43e5003070740d407207460107041e00c113034980840407003804202d003207094410414019041410491890290040c09039550030520200200100e01c03180300c0a1080355981c40c89001014112082d50f80010b0000c000700103000c0c1c042d407121141210380380d00091518111049500b515104241d43c220b0804903004020000f500304045071004070420072007102030000d440201c0c000700704503620 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17042731 1250 17041481 17041483
    0xb0306031506010e06030408030a060506070503121305030703020c0a08030702031009020d0c0b2a0a1103030415020a050d0201020333100302091008010503030406080a0b0a03030903050c03 82
    0x5441050380340e070010410540314a207600780d96500010504009444010000c04100c5681c01180c044560078030001c20402d408072107120700d8001d01810b0f582c07642440d09660711903540b0701c1074a100200c100061400a070040700c10712000344540b03a2010a403601c03501c041c81e010759244c070590b0040e445515445800300d0b0025002003a9107503a90010010a13a1524a1102400410381c09209913000b41c1407026080215010000070b0006000c4511413641d118450285e803c00300301102c0300c1c8085060341c0c862200c90200c00081d4904015003004000c00060100d400083c0b8602c1140d014031400320540452035030b91a00417905026450060041d100341340700300c031002c038203e110494400c2001542d503c10b10b807a056011514a9004140101c0303480c1804140d000109444540800e01001a400148482450805c0c051501c10f844803401c00b10f0465041c00c0c00a900c074003950240038100502000001e05050540e000f401c00c80c370000e01583e40306134417400d00030031840a6000540e00c5102c1d00703d4036400742c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17043981 1250 17042731 17042737
    0x906090308010e07090b0903030919030b06011404050105030a0b04180302061b030f0703020c120a0e030109150902010203040e1e1f060f030f0501060e12030316050304021504090f05010b 81
    0x151595071781540d50800c5101805034001281583d0107100a02c8500625103d83d15001c031807040d9604a44141803a61600171080c20f40107040504224070b507031140c0c420301560000e840030760b002401c1442d100ea4806042c04c005024107504254454240b00c810a41140040c03400d40c0c40d98065800d80b030a603611200190304020002420340d580c0f0b10200001110b426503c0000d0390132030740510300940b50803c00c0081d01e05d04007840030010000400000c081e5407858001030781d5549000250028080b400b040d840300d1141c62459803c40e101d0a4071140c102045a20910866002e81042141d950b61790601410f0305144804090b50104e0346c20109012480c030b10184c0c049074003103402d16102c500b5042d040080440c3c000800007885400e06841e031011016071744039801001d02030600c607901d001c10004a4030801401d4034016010740140d800402c1481040446104501c00c07400c0e090900c595207031224030101d1052400305210314141013000c5000b0a040740d1580146030140240f0f6814820b690700c50044203070071300c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17045231 1250 17043981 17043991
    0x15021306020c0a051002100c030209040b01110a060b0a0302030307050607030b011704020609040608030315010e0a03020102120f0906040305060f0f0603060703270303090209010b1303081c0906090308010e 89
    0x1083c4410801180c0f40a0394400c8000c401441550200c3c1031039441e2005480308607404001284d0042600f00090401c0c0c825130030305290034a0502900e22408079401c0c1c40710030342d22019082e592142040307011501c0b1900d4040c0110b6000d004c60342d0f00e03401030620726190702047e01d100c8002420081c4407511507100340b2891031165046403030425a9240c039420403125a0010419070b80180d12083e000a22080c140051489101055520b03e0350020050004080a58011007184146542c820038000740c0d0740003442d000807603a6400740300d66514142c800040e203030050501ca070350702660001740402045401b00c1c083e402281e83c035031406e5084c1c54886001c0c500c840d04590382038040d404207001810b4184a500040c14190840f20000041ca2010103807031043c466658040d00801d442d5041e100840c1070223080c0c14010306c14591164140049038408556110b190300c400f4080b00d41c0880c00112902d91200c0740d02c49610803840c00c0202d015207251030006403418907030540c085002c004c0001005034603041058410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17046481 1250 17045231 17045239
    0x180a05010f0c0302072301090b0a0c08010806010f09240f0303180303080f100306050c09010216120201050c010e0102030f160c020310021803060109140709030c0e0402060715021306020c 81
    0xb00700170703d56010f46c0305102c46400600e5902c403c80c040100b484c0e507501034014084440085600b0607031680c050b20012040e403003000264010001041050111800c4809680c0241c0006c5003014000c882515500b81d20314610300900b090300d00000e038190b48501000d048074484e40340c0c00b020605094109100401d5840701074003058000c00040c1e0b5070350701802c0b0b1075446a08400d4030100e81742c0702d8075482c0403580c04a4034000740c4140015101000d41c0c0410007007810812108035540840d0030041080081000e07050001d05011010400385040c00f42034201d2800304114100840d16494041c0d4008440b840950b02c1c4234480000401e590445486034000da2070b0290050010601f055920389810020b51000448541f10351260104038026a81400494001d004002c400b1803090034012210717141c40d03000b0b40100b06000c0d036518100002519400c003c0c0403600c1150752884144d860340040758903449010350040c000143c003411203100220719800340c491880510141c40b1282c0d29140103a030348040c01d500f95580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17047731 1250 17046481 17046503
    0x90d050904020307030e070b0a11010204120803090304030b1005040b0103020903120d06050d05010b040b0a0f09050a020d0207030f08130807020d08070f03050405030d08010e0f180a05010f0c030207 86
    0x2250801d0780085401c1145840e00280c22070030003210508101d41d64002c0b0164100000c1d030804203039440500c41c9074480544000f14509403038000b070040c1007a01002c0040840c000400005c071816400e0040e13070011600000800803600e00607070505182c40749402054450352410003d454607511174802d40340c0c079000240c010284a150505403080341d030001d003110030301d291b200c00b00401c084c4c4800c1e403003c9055100d2000031444440c4c070010802500d44294016000e00c2c120401042009141c2281c08216403083e0000141e40d291000380801070b00c591405149803d00003c0c2403001c05500c000060810380302036440c40310300d84034200e1000d02c4d0044004080c04c40321087c000e81025290010441001910404115281111668850f01e290444580981c0420800326040109080600030b4009050051400c643c075981401c001c402c01c000083d10343c1c000c0424140010780c3e00c11a0814009170003031064101c814508170b5240a03400390034440760307854036a42000342e07007007079103000703000f6140416448040040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17048981 1250 17047731 17047747
    0x90503030f010317030c030a0b0a080307051f0905070e0a02191101110c100b0409050a0b0108100903200106030206030c0703181203050c030f030114040b030a031b03050f0c0303070206090d05 83
    0x40505094034271580e0140380c000340052002c2040004003401807042003c0d01007100007803600180c596142241102d441d0800810b580012400f0801500b9a10b0340d00251616031102040301c0004d0142c0300c18003d003130142c01c1c0700040481d000040980c3d100b0740d220003441586004070504910780134030b40072001542d000c44202d500c13101003500042c0c107460b0064000600305106440d407a10388404040150b1300c2c021040f006001c118000c0c072204540c001040401e2011081a560040071807910007a9011040c0101f166003030f2002003908140010758008050f15142d05001c0c24039851980102001c8003c00d51042c8181c854404143c03400c01100d0320a01c0054101d51240ca0540300b03135200300c00c9820340c0d01081081424042d2000e02031406040b0b03001004034030403558018041103900d142000383c803030b520048103003001aa000d401c0e403003c1e682c2c1d0402100103d5452605403481c0c069545509038a80021410b01460070b030000141d4403030007540c0d080b284103442d418191503d0703507222005079001400c1084040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17050231 1250 17048981 17049001
    0x4050337120c060905070f062c010c020310050f0910050907030206031e010801091718100302090405040b0702010c08010e04060b060403140a0b15061804090503030f010317030c03 78
    0x402c40c0b40c0070760300c00f00c0c1002403a6241d90814010f40c01c08080d903940040c051080d203911902c64650030304107100312030320750301c20701440007411b002510418100242110040215142400046010010a40c0501050400304094403540004940101c1c2c94480c900301001d800303040c0c0c0503d5000350b540401800c9010300319002c0c031119510080c41240790302042c1c030b40301d070a00005c00074143c000c015103400001c80000764603118a041c080d6078101420540140325030303141101880c0380b503450300700e00702d4061618002800090b00070380600404550300503c1d140400c030900804440e020700c04c0c800369000b00301d0254010001e45480070280a00c03540c9640800c00200080c4055103c2d070301100004000a041960340e0365414500d141c0d8058803401c6401c001010700400c0500307a0096000748021000c2c1c820191184041110742c020405030398000c504c850300e410b2441c1c55507409111119000030070790b41d49280042404039155001c2c402141c54072001080d04094040d01130580c1d00a918024801d0b20310340f251101a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17051481 1250 17050231 17050247
    0xe0405040201030905120c010f0c050a0309060f06180b0603011802070317011212020d0e01030504060b2d01050708040501110f010f06170111090d0303020405033712 72
    0x100d060503661003142c0c0228170100040e80c4d40c00004c03024250344440c800015820750b0091700c03501c1103a500780440b40200c1c40d0404191451400c0a1138001044516410301c4805000d8904848911610340000840d070b803480d1806030702401a00c00c200388002c4034505c003480031a00c02403095500d084001a02600b104030985c00a044c818068a0b1000f402d803800d5980e8038030658207a1112600d6040c4508290412288401f002c00400c03803400a003c0c550741c1140702920b995540e043c810304256540e00000e0400c00c0c1c6601001c11300d10040c160340021901401c1540e42011b110840540789862040c5141c2d6035803233603088918065001000c40d0619250200549800c0b100e402c1001c20b9000e07608070f80c12200001d1040c491002c1e040792001c84d8440c0350400310001c1c00ba810040f000d0590402c14080c2d52800d020003110922042074801c014113900c6803d04034000d010f1a00407130740c54010020141d440c060030006140a0031241d00c0101600800421440c4131104108401000302070303160703a02d4a840d030160f00c407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17052731 1250 17051481 17051483
    0x5030105010513030605070c030305060306060307050d061107080909010806100b03090a06050c0d0b01020c090114010504030804030b060f04091709065a0a050409140117030a0e040504 80
    0x1104513803240d9a4100762142124140000391041d6400424140d1501845130000c00580181086040c8400403e03150700346401098010b25200b0070740010025603500842031480701100003500c9070110300d801442a40166a0756126440d40d00001c51803080c042001402288104ca00c107202d54500007070314040790401400504280911050b00010818500a03203100d00e0034000c0c150b95030841810880300b01c942e148207290441d8040c401040c0c007138845544071410744442e0718010380942507642c0100c44502c105e4000074043c4c20046000801c026407048854001d8408a901d80c90801540c400c3c80f08555001c10040c284003c2d00c4607442c0742c480544000c1104110107404a071915030480c4402800d4001640d0000e44c8544601c5a2185104420080285041d1682c03012000444031090a08000d05503844c042e010000003488445841c01003084400410501000303014601d41c1c1c4411041d204002d105032001a628004a280c2d104004011240d0007405500c6800319103c5031401d0100034000108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17053981 1250 17052731 17052757
    0x10080609030a03200d0501150c0f0803180307050102120c160b09010f0905060a0506100c060b060d05010303080a06080304050310090f080304080301060e27060d21140901050301050105 80
    0x10700820860481001030440c0d8150401c0840d087d45496103102c11200c10000650821841720300100c000346110302d5610701c0b550441c41071038581c0c4820a182400300c0194503910914440003e13a001000819006171850b60b400f21805203059440b0900166140b084454104100040340518000900c080c54245d4102e03440400001d42118441c000408849503101c0607a21588500200300d402c07620b6005443d88001d003a10502841914904064061128402c008140c0341e2103404c00340b12902c4040c180c0d27048550ce41414419940d40c0d050207800c01c101034410216150414401107480c0e58008115021108081c00920400b41c901080034000c0981244c100d95207512200300c80c4c00b007041400a5030081c0d028507030726680c0b9403601030050a003440401344503014000c5440c681440c03050303054141d2070b910514a08811642e031000001074884045113802071240b4005250700300401c11414a54024000a44660444490003c0300703241034000e021080b40010820001400b0b55446000a040e103600021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17055231 1250 17053981 17054021
    0xa03170702010b030d0e09010f05010c02090a09060212011e05060d11040b0c0d080f0c0304022107030308011403010e12070c0b0a03050609220602030603070314030310080609030a03 79
    0x40c00103400d240c2038040f1040010f006d158600924580440300c140102502084400980d2601001034074000e001d04000c0c0c440c40c9004001400180507421450318194444011551100c1c50904106442403e01584801041d0f100c00c40c4102200e100140e03040d00c0d80141101e080080c451055400f5103090307001c86010a0303048c4000640610f111000c0c0001d4020407024001520303458100402808005003803100d2000c02d00c050ac454a40301c2000c03a50482c1e0103a580c99403030340d590440010350011303820101d0303554852034100009140c1d0010f401d605031780d2880300101180601c0c40c01c00d03003651030040201c01d0680100716075400d40c0010b2801414000d1058080e4400290b545202c0c2125401914094011a44901c00c0154a2804801160f0300001c0340c652207001151a228003200c2104041d00101038503800000325005036401c203d00c01c01144d102c140d100e01e0f4554030444a859410582d250002c062030000007140954011600c0b51265007010015405c002c1100340c120054000c06103107201141c445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17056481 1250 17055231 17055251
    0x709030f050304060305060105030709030f03090302190602070602010e190314030403090e1b07030309020112020f04090c030506011e030603080c0a0c1401020a060509030c031603030506030a0317070201 88
    0x209014108841c0144080e40d1140c0c904074000c0d00741c030700042100741000f00400070454200d81100e81e40094a03040161445402441d1800341c2d0190f0b030a4001075844011504400303203000d2102074550990f0007076400e0f0382e145039803071400f82d080e42d0140072a885141c010150030b10707040a078070401c0400d15000745070468240402c1c500c00607080c1d1041d02c050300094681c035001c1c01031503403142c612034001c03060482294400d2106445840c0e18045d902c0c0c002c080684444004081da0b00c59079001200012006007150355040d141d1490f1000d902620407a040d45040090000384c1c1402072240a12984060711031590242c11400701000c01c00c250329111042c5030340e0301008004900804054802c815440c401040b40400c181030862040030154004055949045048d0300181d038045400031810740e1100c030100d0b154072014011425801205080001c0d48800b20703007415040d010080e04022203000b030b02c081142e61a05018141c446070088000f0340800e1803c084444114500150360754800214400040e1070030301 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17057731 1250 17056481 17056493
    0x308090303071208010311150d0c0210021314060405090402010c03030e01050103030906080f01080c010c0501060302030a030c03091a040b2503052101150302070804030602070804030b0f06031203070903 88
    0xb90f560440082d54020040c400c003d5046c10002c050241128000102c0202c1001601b49100b65039030b5444030b0f87c84a4030001d141d40208410315509294500940d11242f00c0340310b8114551481c850122448a0000d41e0260b60406200b01c070281c0e1009403000800d682c03290015140c00c0e102040840c10182d841c1c0c405001c01d84280702e0540a5442550340f409003a207842001045900e015185880c4a08442c0040100351400680400c80c101c00f800e0490040f002800d0040c010100c81d070001c0d4140c00741440000c201540312454510281c441c0d16001c0c03e654035030f00c0100311102c0e54492601c0081c0c04100600c25040c2034409080301b40c2900140c043e08507030403103065070951540381048010420210340702d055501c0448440d0780c603091403410b11441d5850008810b031764042c00d50460303040c960300080c49014410803008030380246401c0502556200c1180c504205a60304c14803040d03690581080104800c070240f125070b503009000c010010045400d07501000d03915039101401c0b001c107201c8400c00c00800210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17058981 1250 17057731 17057753
    0x203040308070813050316030605100b1306032703080402060d0c0207030b13020a120302030c0706020601060207050a0305061f05040c0302031504090203060a050408040b0c0115050102070b04030809030307 89
    0x1c89008416100c182c00130340081c02c07140c1900054444c2e0030441c1c100f5101c004050901c4103c86e044140820309880c0c04891800c0351405400046021a0000d080c0e0001d103100d404c084103c543c15541048484824030640180850030134140003050020340201c0042480f43d40505d82090000f4000e0b40380c80720421014044030981110f035000340e04002d00410910407a00c040d04d9001c8a40101c51030009410381c00256842c40501548144d02c0340103031484103151082017912844070300801121115034803a03901039601c081c244521130051180e20004181c038203003940800c0403290701000400f400d40780c80180d104a0080000c05c48801d52900000140715030395809a4608200642c400603030300e043c445811400038908112b81d60103a410101480010f8400081d100d5210508070400215500c65242160080c861584204009030012902d9881c1420641c00300d0580c040254114071441e6031400160703100c840500c0785000d40c11023070004001045506004105c040001400c1e00e1501c0c805507a041c911700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17060231 1250 17058981 17058983
    0xb130506070b06030601061b060e03070b270109030f0c0203010e0102030703020d0501080a0309180207050105040b07021509030f09040b0415030203060108030903120a020a020d0b090d03110a03050601020304030807 93
    0x40b08036000c1c0042c9040c10310091740901030300e2030440c0380e10440740c20300c0b250403403007410003056182ea440310000206420f1090720440ca511040082007070802c58015040351000040000f540032828072007148101052154407802e1758192140b03d050f00340e000d41a144001c1543c0d080e6015505d60001e103640500170702c01180302780080d8800503210070b9400070450817108143c124002d181e001070148000b0136044441c10f0111904540000109440c40340e0001c040d0144500c020419820a002d1204104900030000c0c85030030039a080b50a01991300512500042055030000c50a07042009480c89021140700286510800600003003180c80f40c5001150440e0102754821203843c03280441032085160a01000e801051aa00118244404540040e840d9003401000b40101c0400250303100f00c15000303110320405103400400e044189031680c24070305101c5100311443c2200b405410f000ea00c00c0d030300034400d0181c080081b90300d90307050404400303098000701000b80c030641c150300c0140030000000d11100010801c20b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17061481 1250 17060231 17060243
    0x5040606091802091b070b07030603200a03020f010201060e10090c1107060c02040e100b01020607030e030405090901062d090603020f0d03030b0409080c07120201090b13050607 77
    0x4246031000041c00c0365002803500990b40e04145015001da130f11000d0480d00901c0c800b84035640c900c1c1041c09a0320b18416181c004054122003004c200c0c130180c05500c0042141d02500c40300080c81c04d55801c200d0303c0f2290b020841d5004002c804240058103120b40c40d880d400c0418000058000d80369040d001004d601207405e11303613600e01c03110140094405030185501d904031a042854000010a6240b91190040d008100c1008203031600d81e815540c403500700481000d420025240040058120039000c0c105110007240035204040c04603903664442d02c140000102614041c0d402c250501c42080741d6503401500a50301e035900c80d10040743c4075a13112a201c00090990541e000107030b5104400350030a081c1640700c40c00d80b03407034001c040003da190910b50f52442d030001c44400c00080814a01540200710f8004ca02d030b0482d18000c43c000400030401700801a080d0340380c0440f06030350740c1c807007103030f86010f1000720000e00281d0000e0042080700001e401030001c1e0345106a44034041a01c40303001c140d180e04841415151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17062731 1250 17061481 17061491
    0x4030f050c0102010203041a060607080708030403030b060f070305070c1706010305012306040f1103190612120807140d0c030506040c0203041401021006030501020301080d0804020d02120c04050406 86
    0x400404018601c2600d80a000943c15403805884640c2d000c484034080715980d02580340040e8103a039410081302c41e0701c0c0d030003644291603484030309108840e9041260200d02107440c2c0ba60070300691030139a00340d41d040004049041d151a20581d41200c040d000100c0840750600482d5000c55841005035480041e80b1240c00140300f1036265040503400c2d100d2905861280c152081b0b01d29400100e5641c0040e8080e03406d981c08501071403800c0c0030380014024104803440126011080c00104080d41d81800c00105809a0500c09991120340c903054458044030020071000104099210240c090141d140e40100c0e2410803550010100300340302c129074030414445c00c3e103543c1c2e40103444007540c0505c20260090b80540b800c01400d2400c0d4006943c5e031055005284191801c0c400103045a0301c20040710403010340a4000f030001656a240042c040d400070b000345041e43c000e00441d00d41d2507114901541c0b007107800814031034080d1055024042c4650440349000781501440c00d010003107441d2806400c4c010380c411540054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17063981 1250 17062731 17062733
    0xf0901270905060601021002040e01050d052b090806061c020d080f030402181003080c03040f0f0801110f040905180114060406050a0b040b090102030910021507030204050607110609030304030f 84
    0x105211901f0b0040725110b1050000b80032117803a044401d819140190303803001c00014a07080071303032902d50a00e81211094084541c66000705501442d034040907500c40d00e40c812216122620141c95400c202c1d940c1d40c00030b071880118840c08445001a102d814000380503180307079007804d884020071036000c50840c5002020000c180f0046050070034005007400b4070800c0d0000759040140740030340d0248480c40301a006581c041658a5000710500c2243c6c02400c8492041814640d2800c0a4048124512612515510388000842890003c00072100c0039581c0700c550504d01030512001e9401800050400c08508400480c5401c4881091003a188801c4160040350001e00d001e40400c0306845254100700d015204400c0c041028000c1c00c0182c41c25900022425600c661a110041f4503600a4249069102013034400721507001d50040703150300300142c00d012801a00d80c1d80e4a401d030107a21403486543e40002d420020313000880d120100c0c181c04400002d1465113002c8088002034038541080c0c205a031040c000c1c0b51000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17065231 1250 17063981 17063983
    0x806010803120c03070804060b041b0c02030d020102040e0403030e070b1206030c010e010c02060309010908070b0a0b01030504020f060705010609021b0106090b03070608040519080a08060f090127090506060102 91
    0xc3e0700c00516004103241d45813250005003034513000752000304030700e03111400312009584070b400c03041030000545031021a01126400c0240903080c4090241d0003409100e15090007244180200d0b816680700c03103058082d684641c0e90480041c00b000500040318000d882d0080703181401900148681c8001e08801c0d4440d0409504150418440707022860610451081680c0c0a9800c0180b0b00011501260b94949030b035220309165000d009007201c010a0300340c2c00501c44003040140d404150003800403010411001004800640c115201940d010758030032115880078a00f440c0000082010a10440020400994540820050703806c81c0c005580b220b00d43c0340075451041c000f440381d10005d00c1801d50503c80303403407a540420b48444040c00b90000f0040751701c0c00034092040811003800380d11291740700e03c1c403012a80e082250352504144942c40c005103044c40820041e140881040040120003055805180d181c40081510380d003221401451304003c4415204901d00144603a45205000700081d240d0303450000002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17066481 1250 17065231 17065267
    0x906020d020a18060801170109080a03090507060809060a09030e09010603020d1817030c1207030f050105090f160c0507030f0209130c030308061201020a030b1207030510050606040806010803 83
    0x411500d034907800c0801c04c0b16840b072045811559442181c003000548090003501401e4400c1000c0c03d1004000b031082c00c081c0e1305500c0030318035034000c10641d0a52600d40a04035640c40b42a038101c0c03196408200441c0201d03a03190301031040c252080c20309880c0b25103100c0c041040c0049c03d0b403000003c00e5002c41c1c90710f102116401185029016015003265520751940c2e211400c543e99001c0c2072815402100007601580079004580c0050031040d01c0c0700302442c100c40010040c000405030446c55900300000042c05040c00810b00b1b00510400c075401c100da5a5141c5090441483d18184604200c401030403074000c90b00500004004d07500601c502d0034a143c6030300500402540c06040c14008494006000001c240480d800c00180d27030b454a09440e82d519114000389840304400c0c00d02680b9440062800c910a4040d0302c22501202c0a40d03e0414001d213211080e0b840303a68600c00606a07400c00802030407a80d1050340520384c0000020304042c1800e80320200c6514104090301706451582c40040d0403845006400c1c3c034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17067731 1250 17066481 17066507
    0x201020903060c0d09080304060506030d080702060f040302070f0f0e060109060f0f030f14070305010e16110f01140f0a020702010504050d020a05130903031d0705010804060906020d020a 81
    0x2589803440c0000072036956a8000d0408003050400714401c414106940c000c00d051035040a204e6840f41014103020b801400240c1b0405d01c80c2c420380341c0e40280903001d00811407203050760340c003d05507603036610303848081000000300201e086014009005ca90f0044441c90600541075441c442203a240c1801c0d030007204030700003030525030500ca5500e508101c02d1b1351190100c1440481840c244105c01420b82c01036001d00442c0440075006070415070107034801141e01c45a03130f00c20211942c0611090341d1310452052020b005645e1008020708c1c03030502404003409168840d04980c0e40c00101d81000069060f480c0c21500000b0b030151194000201b808403c1d146003070800d40050030500118908901c6a0003c0c02d24802c5108250240e2004400342080d90790f04598840140303c00b500762850500804810300c0100504202200864a440d00c035070791001c14081c0014038800310a0092000c0d504000056840c6900200101c03640c9841d1980c07000000e14038000b4040007a143c0b10050380740c07101010064801151546 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17068981 1250 17067731 17067733
    0x309010909050c04121406070c05060609010f0b130b030c03070906020d0801090b01021f0605100305060d020d05030706061409060105070b0c03130b01180608070602070b0a09080604050a1202 83
    0x4107202c20060540101e808803072105d4100868000c01c0d00d80f11103044144090007410703000d00d008100d01183c111424080e414803440035205265201c1003003080c0d00000b80a5038165600c11803051107200300c203c00622006003d107002c00302c640d54500c00c0e40c1080c0c0c41100d451030602408021711000a400519490190402d03001410030b140c025a002820440140b04905001c1c1d20745030107101c0b690080c060100c0c0c00340070078501e842c044000f084c100058041c81c4181802200e942c41d01865a0344688620780c011007005103c10b0f0210980c1e002c0041909807039206449a00003005140d0004010340300741d400409290b0b515040401014041246201c80102280c1c1801030400c80c0500207107145548aa001c43c209400720340380d40f00d042c544002d505030a0001042c807186a000400c00b01070000040000d0f40380b110052100365187d01125403030311420301c14080541d225100601000e101e0030f0140c0b505880a00d801c41d09640e403030082c40e01d000802d4905503902d812400d4410b0a01041040010500c2c0b1540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17070231 1250 17068981 17068991
    0x10605090c0d0c020a050c040c0903080c071401030c020307110102030f03040c0303080a020a02030723100203010906050103110414060d02070f02030c01081006081b03010b04240903020105070609050304080309010909 94
    0x28407450b4550041307c1802d07206943e1000150251401648044041d6070401841500c0e440d1100c00f155640c602d5010744655404511002d00da04c0d0701c24000c0680d2400039501031030400c80782d6524980d030598060031150541c001844203000c0845440003652146025041031311129285050103040f2102c09050b40c0c4149004100c40122aa00003048410f4160f201070034000b0111003e0442c11b444072100b4a680741030045280070000c200d11600a141a607020174010868541e80d00c005500302e4002c0c1c0382c0741c28001410700041114070b01d14690000e00c14000381c07040e450101c0d86515002203034060070341112581070500c0c40100398142009100280d0b82d00b820300003040d00b0000318403071103e0018491441040004000070b45646800f0302d004183c0c46c2c80c0c18007503031a5616100c40c0c400641082c050322001c100c038401d00c40406601c004032540f04440310f80f255400d460540d00115500d0f131080405603800c03616000e1110010740c04000a200a05080c000740d9111014680018403d80c0d481d40302c2c180b01803c007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17071481 1250 17070231 17070233
    0x21f0203010b0f0a02100509010b01030b030c09010e0c070501090305180d0206160f0203030307080405160b03060d0203010207020a08011509060503060105100c060e030a1103180111010605090c0d0c020a 88
    0x100121550038440c541400e4403002d44400032846c4c68203a080c11031a4a080505000c0d4404054101000c0000242c8062003c030440340d0a05545500103000c0390b40c050b01e42001000a1100044400d030000d80c06d1201a20306019500d4003801e44009807012000503100089010642d6a0000000200c0343c1c1140d40407420101a000144940944d10b04d00d43c0250304080c1d92400c00801c0c42090005a5002d0142d80c0c492400c05400b070801c110449060324240101d803104480391819100c080e081e21007000e43c060440c1c80e03240c18030081c4010308100b01e82643d4200300000242e03441100100040580100201d417104100d040da070040d103400c0d445040d00701d0a0140503c41a80c0c00b00d01d840c1901e81c152980c0448080c00041118a01d40c0d0001c0503248620b4900915402080032006000400c00b50b00d50081078411900d685540f88192198202c860351042021212580300f100c04091000e100000030130410b44500000f442c14038140c2c0d00791608900001c0380c062312403c83c010290500c110b4006804801a9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17072731 1250 17071481 17071499
    0x1309050f040213020c19080a020706050c060a05060a050d0b0108010c050423040204050a0b0403030219030c03140f0c0c0f03060103080d0e07090f14061002030706050c0408010903021f020301 83
    0x5000041c910f094011034021aa0441042030320304022058100e0191212a0300b0280d01c1c1e54000030419006003c2c0c0304003c10020f018101b2a0314196160000307210503650b8900180082c2400b0308415405070320444006000c4c0e40366a1980100c60048083c0049549030811040c04c4451000d100002c0c408207100401003c48125481582d0742c410101c10904100060b002400038410b54005a502c442e8622010810306064005003050780c0c400c1e022034100c40021041c2450004010031b0090004504014402c0040c0c4034846418102c0801d0703000c5810b028000d0078001c02600443c00e0603800e0741c03142d00844007500d0000308844a1403420780280c0700d503504644a41da210f120701e6841c0000180c41c0c92001d05001020042c902c01000f03442001c21521445241803400380050381902001c210030b4101060107458101000e024404558005504e003140384d45da03070005031a0003004200a90340601001886080c280910240c540c40795015020b0100d0002c1061710101420542e00201c0d441480140300010b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17073981 1250 17072731 17072749
    0x316091a0d0e0a0f0b0702010b06070b070c020409050123010504020a0504170a0b0a0c1d100c02190b0403030215130204020d0f0f0203010503010b0105120612121309050f0402 76
    0x41d00e254040ba200e034080704040d24118104000520300342440010300248807060a40e1406004554002e100b091003940410501c0d0007150341c090924a02040402d0503140107903120341c896840a072021400700d01c0d94480c0380c21280784580401250118040310141e0100100c1c0250140004403030131810403122003c01040342c002ca000c0d104030340300030200701040c1c41010406003156035800030032854107141c0029480064008000e040e008120f07651031701951a04801ca00b07000401c00900b80080021800501f1150341d1008030051782c00000107048010400040c064003405007221006d002d81c2d4900c1d52400914000c1c1c256031201c8211411001c2c403541d005039012000b40035804803000f41c0c5458400e0b11900c02004407407424038a19282840351220650380d50003441c100d4004070020031501190800659130340c40340202c42e40481c49550300040d2039292650300c1e26000700300e4030200e4010104010380c2180b1035208821107036080f00884409c21481c18140211544445034105110190401d51f001c191800c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17075231 1250 17073981 17073997
    0x605040e19030c0507080c09010b0a0f1b060603060b010e06040317070213020a0903020109060203070312110705030301080a0b0a060302091303030b031204091a09010306020901020a0204020316091a 86
    0x494081820307050520030420b4060301e51300503041c5c0b030000341c5d07400d080ca0f070740d13104006000c3c040c040c2d00b000069a00004010307510140e820361101ca0000c030141c05c044614003c01c50005912086001d907000200d695846610059841288000380c01004240050520144200e166115040400091002603102c1240d001d030720240d00401911550303a4400a810310303c0a1842000d030300e00c003041c0081810740c4101c038602200d000380c85034400d454840608236100e120709800500403980007105c2064024441d4001c54582405400c11401c200c032aa07541c600f560300a07800b00e4020781c0840c02040c140072428203811f4025100040030802e00345941d0100d41d44c1c800c0241180d0910501c9441c00d4241806500045107411005058031500701440703206134600e4109010f2510f5161a0050031080c035811401112440071000300002030f103038a0740d0b88a07800703540031030345550450045c0f0318007100585450001d14000d9018011103001040070a100800c0b41030700740e100d900b070504c0c1c0c030380d00d0b45013540081c0880d9821 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17076481 1250 17075231 17075263
    0xc0b0306060d0903080f010519060c08040f060504030c0e0103033c0c05010e070602030304021504210203010515060a030c090b030a050f0a0603020303040506030702011e0b03010605040e 81
    0xc0d40c80000060241c05240d0503000c0c0c030b03403c0041c1d107410198000002480b818250402500507601c3d1001d00440701518004240040002d0304103002c82d5015940000ca00d600c526407492415485000ca031005031120f52041e4003003980030409004008080b84464081e26200e18000110340c034545006001d0090199043c05600303108110102c4e110990b00d541e0b00c4000880e1000310031540d4074400404074040c1043c03c2d80c455180101522641d0000b103154011a4159401141191999002c1021000362094190300d8420104000184820a18030b02c02442d464010740f801200040e00606003540c000800034045250028600c8903e43d4030303003090b901906458030300011180380c1010b0a640c0d00300243c1090071141004420446000c02c0e541002c0d200311241036950b40c40381c4950100703400751172541c00000d503d41c10070b000610080c140600619803020081c0f00214020300e51000820340300710038403803039100103460349400d04450909004000080205550410400724400a466281c5204e1800c01c80c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17077731 1250 17076481 17076487
    0x3020f060706050c0301090e030c1c050d0e0105071205090a060e0f06090307060b12030a0807090b0d090201110c06030103080a0212030708010501080606030402060712090801020f030a06120c0b 84
    0x185484100a803a0020341c80780c81000300d03040038044000d09130401d00c21703950002d003011040c10311201d0100c00d6480c0c890346000200b02c0c0301d010081d440c3c03450501050002c01c00205000c0c03041c03c91041c0c040c145620810f03500004403420304100041044840c06034603500182080c00f48144100002840c05480da0811400100602054a0203060803090206a141403140742d0500500c041c0102c02030031002d01c188410021a0316110900299a803e0214405550420302110003514010822107030303c20503a14081034503607281c4004814541002d05803400c503940e02d80a900c11960007116040003200840001c0170f91f1600c540c0001c009220500005110110104125008038000c1100c0d00c2c480b84c00000c604d0700c03440c0a502c0242420b009100f2180008d08660110f03012f400c116003200d00454024024038078002d07042c3c664800301049489000100151140009400202071000d401e5085042d90b242c0d9072401c3c09200c000642d000c54004103030035070034003500340e000994230300301001261003d0040c83d072 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17078981 1250 17077731 17077759
    0x5010e071107050301060905010e0f040210030b0406030204050114030f06060a050d050c06041805010f0e06040504030c0b010602030403060b090c1603020a0b10030201030c0230041805060a090e070302 87
    0x1081c40300b2984107a403d58244030300842c488a0542216058683c4000540420ba40b940042001d0319000e4a0194014810418a40429101c0d03000740000c000080c001042081d0799034042011075509034021590711207030550150403460280801c0c0000e190b220300501c51418140c0018400b0f0b141442070030310a40396020505c1c2004402d206080b408100240714903252541c48280205540d83c1000e2150134914200000c100d48003803808502c02c0e2450450102e0841d9140c5040c0401004068801c1d8144603011141c600059200c811290281880f54003864031585549005006e03a03030840341441c4034000c02000c0082800000d81503802d0010b10784126110f00400c0e080590501c40c9449010744a240300d4010401c490100386a4041101d1003a83e0400010510340c408a0311600d002040c01c0ca20000c40100d06600e0b07074884c1c2070304580c128140b1401d01d015690384418205a01003403104003120740326000c000007880c00314549001018238041c10f1201b038a404140035100d41036404000e11800c3c059503401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17080231 1250 17078981 17078983
    0x507230a030608030f040f06080f1b0705060408090a05030c0603041214040303051c05043809010605011407080703050d020706090f05060a14010506030a1b030903020d0305010e0711 79
    0x100526907001a0395035044182c501c500c0c1341d4047d000c2c0d43c10500144000040d214400d05550788907000c115040c60b071070f17292101d8040038080721a0180104030018490340010134020700101d4082e82c8201d40391039035105c028013844240040c0340e00c03643c400e400c50307108425242c46038130407240c2c0030b54400c0c00d8203a00801030005450020b040811a5504000400d0100402d500030008007455881040304001c5101110001400d85601f00c6000305004141103070001126408044ca04102501e1503010190003a880a41703850710784100d4054201c1e030346410b4100101d58203c49848003229801c5880b03480d1100507195880703107200340000141000710004a80c3c171030103a40c1c2c1c169444140d1040301030050001c2810801c02c00c2d41c080c5019100d500170030012030a20941c52182400e80c0180c2018203156a1810003040110b800043c40412510b448041c09417291048900b0140b0049c035546000484000605000b85032005940c0000e0034549000014001c9010b14107202d50300005614003140b49500c04072602d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17081481 1250 17080231 17080241
    0x90d0512181501090f0501080a1104020c0d0504030c0b07080a0806040b0d08070c0b040f0506070203011409030d0501060509090117071710050903070c030210030207020d030906030507230a03 83
    0x100d40349001c0e00403080303a640c0030000c0b454122144004140044140c504500c0304981e005e01c124110785c1d00041c5040c00068030805080009030004100500703244c0320a9625082583c407103164400200001010310410880d5094400076040441d00720742001c0c52580e40c4001841282914010b100e02800010320569881e00311184000c0040c1c68811412068646001c1c00c0c1c0101d5400c0310380512040010855060a030199400c840324a4030340d4100b0b070302d440700780082540000f0041e41c040d500d13100e030203003400b1001000f82d02603c8260f0045903601d0144840000710741c0c041e001a81003040420054000e40d458100341030542e40403001e503400a8000b000c840c0d24043c1d661303019024101e0aa105110300b824049502c9004c0d241248082c015035890400b115105d1113030403c02480b0300d054201c18805410141107503e0f54141600b070040c604007080d000110302001c00c040880c0044d113031070000d100155160060381d4004a860514200745040c00f02c488841065100c041000950040350000401e4400c2d004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17082731 1250 17081481 17081521
    0xc0309011b0804060518010806031c14040b070b0106050708030c0307020102161104110f071103160e04060c0804110402031b0c0109050c030d020303070503040f0b07090509090d0512 79
    0xa40760750743d40e540b0b03400742440e040341d030020010008000005c40c0a5000701412445807400401601c03000200d1802c2d06020302c0c25034403244c100050b078040000560700910040010f4103610140310327219135407841e240401500c142c00c907000b001028000080020251000ea0b0740000c80c40006540f00e584040040340207000d000780150341048000600c2040c80f40e04400300c6880c80045c2c40501400701030201002c0c05215243d441c5003440303420884080482c3d00d40a0050426000401341e600d0192440a03041049043c0d0300303c80780c014640740070702c03007044014031581411440b942004241d514094544450344450f0401646c019500040000c102216418501d03c1d00021605080d031642c0c1d50b114190f0092002010455561260450031021450300146500001160750300442c9540d45904d0b04552070b40014100701c403c0944080791340b0000d41d1048a00b481b0f05c11301e54441002d240780c5410005501005030903105190003241241c2081c50340041100d442c40001c0c04c20401540310042c000d00780084c1002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17083981 1250 17082731 17082743
    0xd030914010f1505040e1902040b03030408060907120201020d03050a020d060b0306091f030f03020a020d0b09070b0406050409020f0c060711060a050f0708040606170d02070801020c0309011b 83
    0x101800c03045596224490020f9008000c0f078440d51a0024003085070400c80c40a80a0703804800c003614207070041007030310030030610140003c40c0c07844805006c00d04d0f50308503400182c5650442020010046410030003003004200b41c00d15000c2e99080341d00041c0d1100d0700800741404240e1100c00280000344036404948048000344010420706564180300c517490341040c0c030824858071030000480c9000b60103125160216100903417105c01d1030b20350740c0e0358400700814500440a500440801c080035a43c2c0c1c2d400d0032442c1e8040c90055525142c0321103d2410081d4540040038550301c188414401a03900c441513800340c407940d11005a59950501440025000c1c1040c007201d2031044000704000035038401d0301135840c200c0b5101200c0207038981003101c00030b84070103d0348a02e2064503d00041c62043c41400120340040c020000026415190358440207000004020352001d075000203a40d59102d541041100000e0110100850500c0001403881c0e4032841100c04041c10801d0181000e440d00204200e00528254009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17085231 1250 17083981 17083991
    0x703120c03030e12040305070f060e060307020a06020711040b010f080117070302030115030b130210030504080c01050f01050a0503210903100e011415090103080d09051902150c0d03091401 82
    0x8808600c445e07001d408202e8041c014404000b4003d600204200140c800c0c540701c00c1c8901e001c0b2818003250b904024444000c602c01d0741c21840100b10640b005181c0d16002d6620301e00e1001400c02444183d44240456604105433030300a50342050b448050349041d5003841008151541c0b481401c1c42c50002c007600040d526500c1c180c61304018000b0345200c1c408580c40f840c10350005079101040740149421415010750022150301000120920a5201c954014840d000d541d00f070050b11f9984508441044848481861203400180042e207001401c140c000d2030214020100e40c0380e504140e408442d541900019a00c00c0410700b21040d5900b80400c07008500c3d64042009140c0d41c5800c031034082e01282c9168002e031250300d0f001c80c00c0c5880c040c0303900725440e04c040c105602607480c580e03401071264000c0031250b48007075480c80b0030400100305001401c4044500002000244030380c1c010001024400070f09019041020011024204000300e084c818001c0c15040019140c4041c2c240b40c1c9a0585107807501c03609520380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17086337 1106 17085231 17085253
    0x6100c0314070b0f0405060a0e070302100509150d051602031c020d0e01021209010501060215070201090602030f041a011202061e1b0d020703120c03030e 67
    0x540d8951802c003140d2501044040280c0d190302a441200b801d200a10078201324454009034110000c02c0f203411100740e036559525561000a0056410100c54030740c0754011029189904406441103100045058403004541c2c0304090850040c1e2801f07004c2150b21440c1d0007200380044003600158580103030fa101010020803010703503010019400700b012520701d607540e00401d003400740340e50005038950b07103c3c6600d4840360740010807201e980c0e858032004004030b5a0020745501e4030300c4098070407000c41d203444d04124050f200c0c1c1a009000d0b64000420311800b480f080308a80d2285011b20782180c01044030f80c024044036031b401e204840c031004004441901625000000386680055004188a1410340603c2c510164215070f41d400010820300e000f08100300400d222450104a039437000e0b04007241155961160100c5820382942042000c42402080500940c8242c0034014002c0449501d0307180 = true := by decide +kernel

theorem cover : BRFrame.Cov 16906481 17086337 := by
  have h0 := BRFrame.cov_init 16906481
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16906481 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16906481 ≤ n) (h2 : n < 17086337) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
