-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0591
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:37:25.699507+00:00
-- url     : https://prove2.me/submissions/d945e909-a9d0-4a28-86a4-308aaf41c2ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 106115107 ≤ n < 106294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 106116357 1250 106115107 106115153
    0x70c0f0b090a14010e100f0f090f02010206060a061704031e0f08090a02010909050c0c190b060d0b0403031e020d0f0c090308032e090506011101020301140904080702060304 75
    0x401a000074201c075800e0640c10800e40100610a2a44029400002c0c0140710113501152564803148c0c18400c446820710304807142c81c840c001700021541c06210440d40404111111420343d803504401400e032170810058200307001d0984001404050080c1003402c40c10400c21048042c0300d88268020b000003140000c0320002c20703001000074040202c0003030380a4216906a443c4000c5510f0507400c0009004058100040c0450034007150008150800c1540701c168006c031361203502c125641c20801c070000005000d082c0208a124080c202040c1c1503103403079400035894900003442a905030104040c00d01046d10040643e0300008107074480c1d51840c1c00060050401800030814181c10741c1040d540c0e905144002015480240001880107045c0f41020780c02044681211403c00f0f4002030302c40d1280d80a03008200c07510b5849007486083c0d40d1101002134140c15950086140d941081e00c0445410000111107204006100001c2c00b00040030041e280155409008180c407402e0038a00904d02410281101c1d1341c440b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 106117607 1250 106116357 106116383
    0xa0203011a03030a050c120a0801150201021e0d110409140105120703152301030303180b13020d020d03050405120a080a050726040603140f070c0f0b090a 67
    0x100015800304030940000c2c011032030558001e4007604c10f908400c074602c0407800340b10070030308030b90010100500360b500041e0754840c2d1660608101d10104802a100a400c582c4144092009a060329859000e00070101c0c641c03907160f044020011010307102c108a086144a0302040004009030903070481104c0c01000b2960902503a01c8030240a0644881e4165200c0360b8082d4a003000411401381040c2c0d000070220001003424800316000c4c1b0003c4079010303100013100d03903002c0041082c16814810340f400b9010366003800e07a02806ca5154076041c06005404803d8180d81017a4080842d43c650070310440c006c0e0f02a12025502c0d0329824040e040f9005881500d02178a0451441c0c1000131020440f00d481d5607110300d4860501003100400c5569402404045618640d00c5d9030100220041034100540d140303000485556960030100002c0c02c3c0c0c0d01c1d0210149140d80e001081c0308030a070050030035136402001840c181182c0c07450360500c0300c4000b018040242100d500e090900408030008074209075010300510380441300c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 106118857 1250 106117607 106117631
    0x61201140a0b010806061e04150905040609200c0322030b0609010f090b130207150c14040e0703091202070e011203080f060307093b0a062a020a020301 66
    0x101c3e8044a01640c0844200000404401014241c2d00402507001c409410140c272074194500350904c81c4030b2a000b00d02c4d100d804110703501d09401958080d000d031050500903910001d0072600c02ea525481c80b09807001020404280f860340070420360301d015811811411781d0a100305421303205200300b400b0a5480c0005600020814144504980d040b07800c0d00d000c4040c1c4915004c001d10084c074105004540c40030013100b802c20340c2c00743d1b0300151804902522041c0c001b0343c9007912000898281107013050a2100c246030200c2c07000d0030817065a04507100880d14002d00e541d5108110000c14060500400300410780301d0520041d50700050f40781c195048030035403401c142d8a581003d0b07000f07295010014000b5204e0030003d0743d00301d45c0703410440c0c1080018044503c4c158a4000c0e070820340744d01c02c03032a901e0f0540d4802c07034240f0341401481280c40c030210099180c000045804da40c40d20303580351181c0604115100c0e140c0c15644881e22400300000d41046406080f9809100c1c3c00a40780c2c08a0213040e0302c40d609007442c0c501d00d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 106120107 1250 106118857 106118867
    0x60702030a02102316090e060604030201080c120f0f010803131e0902042306090a0e040809090103060605040f050105011b06021c02030103230a02010503061201140a0b01 74
    0x81d0881c0390010070a441c000c90b0003070090004030724a540d013120301e01c090700741c020440000340380115109003801c02c0880c0e52802c014092119a440780030911201e20502520b81c65040499090725028178210a0030368440740203690340e10a2042c101000080141009020141004018004c071411921a81c16980c0c0c2c43e03080d07a40e07000c2d01c13612002c5415507c0e802c01c51000b00b1062f08040c1e0b0000f51210003c00d42c0c50750440100e80044e4025a5000080703240e1f004410054000200d2540d4125505802c0c2401c0700d001c00c180c0d6800340242111045504045814403085030207854550034020942095903861b4681030010b005240303da1030140d400c3c45808000980c5a0150f903040c0c680681d20b00b01815441c18503540b40c00780400055400c60f0b400c001e0030807100c0b8406400f800300000644051380d254990310b009039461046100185588429501c0c10426440c0400c1403030a190f024a403c81d120307211280010700c800740607455150550310b81100081201e42240206100300007035401000300c01070104c01511 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 106121357 1250 106120107 106120117
    0x7080105150f1314010609060215010b0c030d020a090905010902031b03150a030606030b090708030d0c090b0a030603030815031f060e09030306090a02180f01020f0106120506070203 79
    0x158401c100d24203007055042114014050380c0b0001d10036104903000004082c02c46984440b680100345007038006200168000420400511035440240b140c400c0b00c46110180c110103025444440d0cc0014800c1d9900d41e00300141d07a403802110408640c0c0e51b03260340001c3c5c03030700441e07200720b8409a00300700000030103041070f109982c0725038501003050040816510603501706500c0107240398540540076088488c1c940312964888059449000d0004016055050000035950002c0040e101c0707910010303042c0400c01021003904c0d43d6034108940030500000c191820b5031030b8041c0b500852604400498500c18159140c0c102c20103c03030080c1c172901d1841e05c4580130418040e80721400550103500800d0340340d1458007104103c0064940140c0000f5540b5252040701c1500366080d00c400c4c0d040d07403010040c454549480f8001030741110003418214549940b8105c121500b00503000090322408144400d524141d001b4040807000300d16400080000c6071722a001f1648800f840c41c0305071500d2240350b000a08a600002c00c0315 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 106122607 1250 106121357 106121371
    0x18090706141603020712080c010f0e15061c1101120b0105070201051b010203071e08012417010f18021602060c0a020405040303020a12140610110d02030a0207080105 72
    0xa00d03101c0c2c0248112040c80e000701c021421842031240009495201c8204501220300c034565859586006041d002e094400800485802c14544030400c144c00b8000074110540103502d2140380700035a92840024501074540d009903070240000e1140c42c0401500c0c500710210070307000b40c1f2040c0116848120071b0382203950801c0c52a0104408000b204050b40c040c60140041944e680114869220303904511400d82e0010345241d4045060550518044200e04143c1d0030301104501d890a025850f00010111541c0e25090340b4139542a994104140d031849008400740703900b1504101160341d41d40c0c0d09001a034414a1140285d4100b08440d1050203e2503030003111051512182c0924030b4000980070814550b10420041401d031050414080c0162114010184101d0081e02c1c0181c8410031070002910002d0000c1450001031315000007010380d618001072241d0045425140c00013880d542440690380c0c00b459204092061040024946d4482e5000000380386200703031642a501c41e995903502c90350a03554152685 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 106123857 1250 106122607 106122647
    0xc080105130e07030f05030901120209030604030e06090306070e030f01051005100507060c17150d080307050c1203060411040e0a02090402070210090f08150a050702070518090706 78
    0x20055001440d08040c403120b56078016038081581c1c954440e4040c000c0d40307004480c580c00104000a156800100c83c051880e800c10055180c440d6080000b62140e400034002424000080000400c0b41c17141c0040e5a4002400b4003103480074200780c40003520420b07444c110584607202d0115102d60b80941130003268080c400319850300d80c0807410701003009101010203114000b0003409000c14004102e0500807c020301901d0384400c429000e0098070600b00c1310b8018a0310102c480f041d00c0d00385d540d07224a00c402c00760340d811004258990301c4512049030180700d111f161002c1c901c100d590300003000c07040340c0046000baa0104c40410441c8a49480c2000078088c621421507840300c28000030b490060690010117010317030000d00c01403030b1641a500099007900d40b0284140060001c2c141440500414103000001d01100300041246400041a1001c00d51005001ca11041d44031808109000e00801c480c40240c01d008100b40701d440564a00302c91710000403150a0014850760f034000034040e000b103540c541c201d030101441d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 106125107 1250 106123857 106123879
    0xa020d092303071e0201140406080a060501030b240d02040603020301050319021507081201060816020303060312070c09090b07081608040f03090503071205010b06040605040510090302090a0507030c080105 89
    0x41400c0600b1309141a41031110791a0302446040030345004001421064450929504000b0b01c46012540b890b0000e5040c546852803600c907655030981e015031136400c2501a0500f110341c10803d8100303070007902e0301c5a80d200d0001c80d0119001e40c05801850503507909030111201900c000e500c0203000303040480302a41106444c4600b66400c42c154000701040b6001d000c030586001030406d1828100c4000340d2002001881e4241444128141028000c0080040f03200170350440c00d103000025107074040c09c0740102c006178000a42504200d41e4003a80e000500401c1c504220101c06401d1208584500311f4103400000c4100e40024031034020b920700b04111a0760759036031203007655495482074a0803208260079030038807075800000034071940c04100900107004000d1003a0003074511803401500b511030070040300748511014001401501d9104040d035040b20000c403070360b521000300b402d82038540e40c1c0f150700082d400c0142c2004200e00a002904941d0003251255010001c00130071040441d82c200d03003070149951001e0300179a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 106126357 1250 106125107 106125143
    0x100219050a0c08040906060206100602030f0a020c130624020303010b0c0307020a03080406090603140403051318020301030c09050603060f06120703050f160303050904050a020d09230307 81
    0x1611001c281c40c02c01d00c00c00d01c02c585030640c003070704654400c284461322420140b0100754148103107901303d42e0301207003109410b08049002c0d4490040315803680e00d480c0301103036641001c4d00c200542e131030031130000d000b840ca203050540c0d2460281803140034144603080900740e182180e850342c056202d1030b07204580c05141141d0810b10510210740c45030502c10380d64401408150b001d0b90f21101d9080056100d4400e00d6030743e0b0310b0044042d210040560044c4281850504d1080411030412400341e881179152030103c1e0740700c2d5012410100c0e10600c0d0008581d2a2000303003d04990240c5500440c1600c2c0603610380e41d41c5a50b10341140060300d078100c5a043c1c25400010100d000740846113001a000540244071a041400403d406841c115540e40141e0f0399030301c444411208400c0c1402501d035103000c152a5180c255046480141080c45180b002d6801155210006000300b03102c1d078141e80585103074103c00d00c0ad070720303050500145000c4e040c41140c2c004c04501d080d41300d40b12400002c40d8032840c1e2141440458000200d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 106127607 1250 106126357 106126367
    0x60506060408010e0c03061027020f03010f0f210311070503100515011713050304051c020a0509070c020f0406050402030f011d04170d0e07060201020705100219 70
    0x160086801103001d1002144045080c010040140d81900c0104404d4941804041c540500948042402420288240003494000c98280110038412026040e141c101c4a20040280701c0d4104e00e564508001c000805d09019005078001101c500d41e41e01441c65031150010348844120411a170029407a181c3e40c1c80010f405241200c841c0300e0024156818150350343c001c030303052030075106503551081d58a80c00c003c641204569000d510310420328040070b456280300f610040d040c07005000303400400382c20b201030404c01204204484c06404060078440d40000346510008204003a20000c80c0320321103c0c613000c00d017406c01007400c6108448543e10f5001504080c4c084c4021241c01d20707104da4100e41c50b881c0204043d2100e0004502076030860b0941e5031a50302d044e014403251803180e000051101424414800410b031000302d840394071140980c0c103595070140321248000400e540b210712600c030300811800207084c07030f0194068450707140035000f9a00d2a0200e503412004a214034001c01846160115110003014461 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 106128857 1250 106127607 106127611
    0x510051006110a05010c030b090a050402012c040c0e030d020c030601120807050a0804031e0201050d0e250602070807180b01020a0f0510060509060915010e06190207170303040605 78
    0x340007030390030302803c070b481c1c3c1403d55003030b0750720400801d0721b070070500c1070078100b081c68154000101841003106040c594002000e140010090300300c082030032a0190340441d000d00c00d09a80d0000100108102e0380341002c00f5000c0c40c1d515145511038002e102261010354008100003034104001005041e0030783c00c18100d4441841c49080580d607010081c482c82d0300080013000300c2058540150041500c0d6131841c40c0c201f510040d28900072002d1030181d622072005076000400d540c070300640d030200419040300161402d840c00c0e00c420924180e04000c0c00c401c13001d02c0003400c00034054546680c01e0b03411164403800c2d500e41d9a501e620480c0404205094803590803041036010290000c414415102442903a0700e0300c0d100140c1741f81c8140c40340c1c1c100d400c0300c2c20740c8280d81c8188001814203070350640d81031a012000900c8240001c0c141680b811a01280003801c0c1c1c492640449013401c000d05580d01d0b4950030369010300004809080f94054412a040841c4002d10768040d50640c00d508002140b441e80c66560721006040c0c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 106130107 1250 106128857 106128887
    0xc01050f06013c0215010f1737080d0b1f02030409020310180b04140105130905031e0c0c010e0d060c03151401080723070503070b10030510051006 64
    0x45c0c801182c0e48041c11444080c003c001001444000c541488907491421000c440d21105540c00741d0421180242e0171484030381c030060480c480d0405900d01280741000c801801e103009214400010345501e150040703600540c0c06d820107a0341000021180034954480485241d00840940d000340010801074004d038006584c400d600c1d005d2011195954005104821441c00310169030640364a0030440714100b5115501d01d100c0c801c0e0513120345500d0031000c55000144010507004260711540c1c10b4041c084108119880c0425030744288485130801000a10030f90848a9610b1003409549800b40440d0711803080f421206a00801000c40e1007400e65651000780801040d0005250703e80c0801944c800e1071510b0280140640d40c04803034014080d000060041c10000c00c44424050300c252200fa41003403e482c01e24004010400399940d580590510a00c2c42c003c03894000c00c00f40b40a03080290031403c1d000c42000304c0348108100c4001c001c4442820043e90000c032004181441404820028184103001c011003000e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 106131357 1250 106130107 106130113
    0x60b0303091002060103031106010609120302010902060307090513020906120901151203030509070b0d0e0109020d06060302010807020109030c0f030512011725050402030c0c01050f06013c02 83
    0x11900082211005800c4042c8050303080480100141500300501082e40e0b480300c009003407036605010f000342014460b805403514204090141c00c0c00c040c002d5101c003010540040c101500e81ca0303d9034005102640170700070395000341d40492004640341030074026118910401019a4101001188030802c14000105481d100b59201c54007810b449410000110142281c0711700c2858007001401c01406480e005858801a030340411000c1041c1c00e0f01e0415990780040440303012a5241c80d042c1401e014020103c03004c3d5000210055083c1000b250368441c0085900c03c1e02c1d090119580c90409900300c80b01d01402a002c9407446003a240040e03464601000c296120741801814017402d00f801c8c19600409800411440e12082020f617054032003000011100d011003481c5100304c0500c2e40c2d440503043c4031486001c3c05290040302250890200300b0981d4600d01802008200078034001c074134000f10403030566074203011540300020803c044110002c42c90741280d10b0003410050402043c0191041c15910a0100441c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 106132607 1250 106131357 106131367
    0x609031509010f0612050703170f030a0209041107031407030c06020d0f060807050625021804020a050d020603070f0e04090f0b010b190503060d02060304080a0e04050112060b0303 78
    0x8103030104207405240d0010001070061200141c0c602181c0090f0080c00700302c2c24101045001401c006003100550342e0044880001c200032a11800650003909490b8040010110810040c004140d0140503000c600300c9091106038a00c54600f2000c2c0729144d0701800242c0c1c0000440720380f040440052003030034441d01d04406121025141c0108980100d40c3d603178512030f02c4000498020105025100c09060380c0d0015082540c5010b00084c40b03840b49038038040000311081207070fa941002c250015401150060a0b40c0511080c411a840b0081d104035022840390301200d00100300d5040400c2ca0010300c0b680580052b1541d00c800a00b03880f07141507814044108104d5802c0c0e0b002588a83c010038000520039040130000382160700c3c1c510721403001600900e91000c0240a001c0d408041c2c142005c85050b601d0818640d25116040410070310b00482c8070103504528000300f40020014100010101004190f90300300c00b03d66103d0400069030030a1140448072820403664a012656550100c9000e000c0113046038945 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 106133857 1250 106132607 106132633
    0x27060405060307050306030d09211106120f0c030114130906021b070e07020304030209090c150a02010f06080c06130510030c2a3305061804050a02060903 67
    0x903a02c11141400000c401100b03220300c50a04201456501d2101c1c10a9504582004400e0b41c41407042d40d2248621003503407880c9000c0c0b26590015001010000d044680d440c0d074604030980009030107450603201511001c00045407019001c064030b060f0f0700030100c02071005028034100703c0d010181c0c00c0020314a07a9180746040010358688001e00e0003080040c01800b0981c2a061440d0401400d603000203281e0a1000800500b1a400301c103c40907030764120303240861500e0340c20b541840c03c41000f1403c2d8014899a0404d480200058090442c4d0f2034250b000f4400c00807010140001e075245441000394a5205001181c04c501e4510060005c4151030080e0002c5140c3e510300250410b0420f00e070181c00702e540d03084684c2134079900aa83d1003103180082c138102d58220107070826030741640703105802401d55804800c4885d400880c0c01c11040060341048540d5180c007103600d107010014142581d107540f0543c010300640908922085a40d4460f6030040090541c118040e02441915030280c0310082e8540203184049443e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 106135107 1250 106133857 106133869
    0x304030c06020c1606030b01020309060f070507080d050301090b01020c130c02031c02030405070512190f0501021b1e15090f060702010606030533010201060503010c081b27060405 78
    0x41a13000649065145024000380880340c600201e141103400400c10f0001646440c41200d500700356600c0d60030795402c0c05040c054100302040d0024600742c02036108000d00250300001440c169038804008208200d0a01d0040ea501d0102d03420742900400c4042c2c40c40d04c0113542c2d52048450311218016a4a17090585461b1000121101e0201d640b00d0760100903c814040304110484c0a40810b965600d10194124101540e80304040039401d4184040b100392810809915506142264400025503e4a4590b070403c107100b540001c0b404030a00c10140340041164170104c0c039101d11414036000d490002000001614a82d000a2043c1064402c40c81e10b410403640400070a8031410403a40002506800d2500090940b41c000e0941100007207241000d40030011520840110050403c500b441020982d10040c0c0c05803045a001e280c0c10f51030103110742c004d250802e02e16445400e140c010085034002d03101d05a00b9502030001062020b207c81c006500075440140c1c1c80d051006001490181490356400001e58 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 106136357 1250 106135107 106135123
    0x2030c09060a15210b061603020a02150304020301051f05040e030c1c080901140601080a090b070c0311060709030b100305070b0901260a09110d030e0909070b0304030c06020c 76
    0x2803203280c102660342005200440b184141d04020311401050700001400c5014007c09903201030001640311003018000c0100045441e800b40c10750080c0c4601c5d401407100d5410031281a4083d50900c2e00007219608000c1040c40240c0c5500003000350a820842403000030300342c134814080140320400c20503003c003404100f094100703000a05441a600d10b01c0300018580d500160040203240e0420518900b0140040151a0300200a10340301ca855070f201100003010340b4078000301501c0b035141c0d41c0c14060001c0c1d00050000240c0d02984030030700b15803500b04000d5a0bd0300c0440d1040002100040c6c2400001c0e8921040350b0000c01040c80440c841e0317126192a81040034641c0640018500000d0304121940c114003034104030591a810042c2d84180c86090300300c5032100030070300201d482d0340740810741c20404c028203060078190340680040c41c002060314002d40701c0044120202d2289200d4400142d46038000540541134541b14010141107481d69038040d070b458034030440200d546940030f10403c03030001c8007006882 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 106137607 1250 106136357 106136399
    0xd0b04091a0610090f0314011b080a0c081302040c020f010606021f090c0501050306031204030b010509010803070503220302120604020114090616021c060e0106090902030c09060a 78
    0x800720305210040214141c0501405030520041c0d2408220802c448070f0400d040b44d40001391603031428003400e0340500400240b6425600550700701071900300140c1c23142041d4400d022040040000302c0c0402340c15950040700300c60810b80c50900c00d481c0300043c1425000307501c03c402d660044400b1041010364850039100030f07420030401a489a4010b0004090002c00340400c403070500d4003080100040e84510b06202c0c4580141418043c00201007005510108800e4014181e452026900d071a142e14040c1281c100c20b100f120310404026001190401c1e000c03003110380803075100c001145020362110402c01c1098001000c0041403031104800009a1580c40048500e80101c1000e00b0151401e44000b500c0301c001048420b01d02401844070030201e80f113450480328207a80300300c0c1c481b40c41080c40c40040e078910300c03000020f003080c90041010410401c958004403600e4484000a000380340d04e5184220884408103c003035455171002c08204c490341002803c841c0c12030000f810154501c0c1c2c41d2901e00385400f00440d440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 106138857 1250 106137607 106137653
    0xc02010b0a14010219020f0d0213060e0105040605030106150f090314031b0c0d020f06071202100c020316140f070b07140607020a0305131230050d0b0409 67
    0x4200b540c1d0521419224083d01d0307403150301c0c1040c10b13008503401d5080c1202850260b0b048012150079550303450014001c1203520b000600000c3d448a00902655100384130b103500407030034a50041034a01d03040c0510010349809060344445800101300c110350019903440b0000c240301c8a81000703c007041080041500303410601c001103680381322441d1281d140b0400c2200403d1280c0100030201c03034079030718100f03845940c5030100c0e0107004060913a0000780e018030951000521544814001c070b580c043d000714840071411031a21080021200c418070682e140d1041504284035010216a040001112081d4005032400000700311548007920903801031034184240c0204005080200c0c0303080070400c1d6041001c1480c80c804010301030710704203070300083c1d0b0325150710600038180b10000c600120183e0682d2180802080e0324002c6030582880c50409203c00c04a002c5040c3c40e40040c0c445a10304602034dd400a21065880d598183c1340400f80300c65a40100030b003800c4c15601c562540a10008207031160840b07010143c0100e40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 106140107 1250 106138857 106138889
    0x61c0b0a03120f030b130b01030f0903020105040203060f01030b06010c0302030d060305011e021911150c0a030501090b0f010e190e0a140108120a09031202010c0f0507080d0c02010b0a 80
    0x7024004999103c0c88004060503c0f03544000b0703844041c407200d04000c003040c010603a443c2c2c0f40c0041e4064000358040104842ca086080030905905411240c0100d0081c1c0641e14941c5a105901c103111100b4040500380340022030100b840395208440c000003a60080c03064a040490400c400340540d022503005940f01e0f915420107411a1510a01e03c120095600e8011860700342c07054800c000007161a10354500b8000180701015000200f48015402034070a510703582020720b02070800050076044105290002440c0c40000302d4104018410030000e8031000707016550203404078004441c050801070305150803043d0a41120200c40f100356a407005445129000140c5103802e03940340341190b40036501c424a00c48100c0042204180105000f1654440700040710350315044200103907a00c1d001030307000030701c8480c11344200031100780d06500880381f4a1456803180202500501d0031101e40c0039009000e0501c140800944007400c619502c8800c0d2002140000300308190898001045159182e020311008165034030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 106141357 1250 106140107 106140143
    0x60f02032d12070e0105120103021c021011010f0603030e0d06020415030501140102030702090a02160b090309030601050a1a0711040c0c0b060603040b0103201002010e0609030405061c0b0a03 83
    0x3203609240300d130070320f0040c4c18800004403c0c607040b48184001b901542800d14480c500d664800741d004426a0007608001841c0d0903d240141030008005010960b5460184000d01010441c01074030f04403070700f40e6150f0312180388503400c014034504c01c40412150030f9820440050303624921000f9900b20600e94400184035894256003661040c020b44103141190810013080340141e44002070240c014007100c3d80161115589000e010f400119040041e007900f21460401a151500000902103800c0c2034043c0c411991f41c50040c804060302c28012140c078024415144442541070002900c41c02e80903500c402c1500c0800c41c003003011912030400344000264400005418000d001c9686600400c00741c520b14514940358596028048043c00018080c50132850301c022204c1c0c49141443e014400244145160740d04010064001c000c42103804105020b48400651f0304100481600c0488030042d02e081d250001c07450281700207141c0c180d403800006594540c03aa2103030312007000c0e280255204040c807403100c0385100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 106142607 1250 106141357 106141367
    0x501090c18030308070503070903060203010e180c03100c0c0204051509090c090a0e0102070b01170123040f02010c0f05032113020913060510030b01060f02032d1207 72
    0x10001072680c1c803016a08100107a13101e0043c9620646910706a522070711a46802c840c5003449034000740c5818004000410143d080c0300c00e450051880310414100b50156442c0c5c10f40341c14032406029450703004500c00e4145040c6940028080c034240e840d20740c0040e0050350000c3c00319807003a40c11003a42100202e10b43d0a80c1003184440703030010300a0001300181d00004e800244c200e0700091240750100d4403038400440e540400d4069814481d030201214441e5a1a0a9500007010002120780030700d40c01c1c041a52489200045020b90510403828544020b036202e8403070081c2c80304400d0342203041041c421a9440441c503503001b80c80301d081c0710b1409940c0e80c4038015400e110618800e510800ba00b00d0300018000b0f152061803881d02c0344e82d030655250515507964501141a4101c1da0070281540e4140070070001c40d0b01504824000751f034440c16072004545d032140340c12900d00305034041031700150380200081d00c00d000488240c440010801040f0340d00394000c050003c2443e8000000c043d101014400031300c4a02e80d000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 106143857 1250 106142607 106142627
    0x10e011401030c1a0409020c0607020d030b0306061912050c01020c0f060306010f030f0603050a1e030503041e021201020c0f0f0d12110f030429040b070c060501090c 72
    0x242446a190394116120700380a81030503c01e11302d00c402c40c180b03030780c100360310410594008000d801411519400c00c425919150f00c0119030410050240035a80c002d03041c024850b00d20201400340041c0303242e66075041400244000a000c0e2a1980121040056060840c50001070802e00c01d40c091701241322031070700280c9002d81c00c1600c0c611a480c1080e0700a115150b20741031fa44c0c801d0007480c0203003c164503400254010410000c14509403030410502200784000059000580ea118a410032075000180d5840c052000c0003000c0100019020404540487e2450301c00100381d0501802451741c9445903070015002c43c840410150080c1d4000c10052107a25041c4956040c00e680d1002034400d0004640c4002d48030502018207006115880b04001c01104d040d078811083d04608081c4241d682c149101103511075002150110f5002101040c1c880913120483c41c10707900c030340d456008468035484998585000b140001e2100d010440c010690401243c01ca005042c02030083c1e42c0700150785001c1d480018581d18007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 106145107 1250 106143857 106143881
    0x201c110a0f0e181e0f0705031815040309030b0f01080309040e0c0312070c080d090501050901030212010b0a09090213120c090e0601051002010903020607050f0702040e010e01 76
    0x140032080880303421001d10004410741d071819061901d80c140000740c0036001d0382440300d07030115480300300880421802405003c01200c143c0b0070580d65070740d20f80100482422600400040d6060010480b0a44803c50b06654910f5240544007400301081604146050071601500000d081100420911040b001000d030400388641558410750f04100d0f07065070324401d404000f401180c0d50320420380813a070140003040d902d0400030b0541c0e0031034104440c0b26005800408041e241d0307544040c400240c148000031055007102464070f40340740c0785240c1001500e00d41c0040043c40d051580802801e00300722003044050b0702030514050700c20745840020400070100341c075a03008180102d1041109070811188103d65908940215501003182c684130701c0e0002c919100381d0b0200c2a00e40c104032449581460203d000c80c141c0e201070f81c01100000e00c55004900fa60350214010b00941c00c200301140b05e16100720001d00c65865850161b03460810140e000c10203e524591000800d65514800b0051102d003e004a01c0d030029 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 106146357 1250 106145107 106145141
    0xc01020711030615270a0b01030c1d13020f03100602010506010f08060d03030e03270603160f032004031505040203060a0504030314090c010906030e030d201c 69
    0x42d00c90204c090451401180b00c0c880e003890180405108108116240f54103c000e501d0035041c10031451020141103c1000036003c2418403111814031403051384550401c5428030381c1c0c0380744a82080c05001041805c6402d03406070030b408000701603451510000650040d28100c0246a402e07140030340007421114081c14285c1003044024000d651a079101450302d4100f501118210f0603515035240035002840210058030707041c04041f44007051885120801445201010521803198010304100f0000d407004480031220250000349040d1030034414942d280ba81d06450400003030f03103207101413001406080c1c015500315080700090184201300c03a02116030300c0031185c0e5000340800e052503400203450b07000040008500030340c1d950015007458440e4000c40e88000e00306242c8103460902480c15500ca02d200402c082c040b41554000245881c4207100c0d8010040100c0c001c0c43c246110350300b803003000d8400a5460311060242c0d0300e0754580d544201d0010702046141d5400041c0005100090740e0590f411152a805012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 106147607 1250 106146357 106146361
    0x80309061012061d0a081b070b070b091e010207030e03030415080a1112010806130203030a03090c0b0c030408160302180a090f11011701080c0d0c0b0c010207110306 72
    0x1140003068010b4050788100f020450a0105441040482d282d0581c588284110811901440051030040c5520160322a02e0000300911402c481e80e551810322a6a01098040100501147e01c6469054010344160240d83c151014048500c0e4152443c0b401070000d65030020718203081541001100301800019405542032503d800c00794908108800841c1c001d010441d40041c0e0f00c009160720010500451805854448103000c44030035800000b4042d1a805200c3d845c0443d0219060740f41035100c6a5000b0001d501d0024056822005440440c004544c1d2800d18a004155054480054041c0b81c5210000350348803460900031928240c1104003034207080d0f60481007800035885e032010082d02c401001c01600029140c2c04031440040c5907180c00502030341c0901a00d582040790031903000788003003001d03070394840c05828402c2c400462000a2040d041c0310741c06907244a80b142010454884454000c0031440d86442d81c1d4480c0e844a80e00c03c43c0001566580061480c08000e0050400800410142d0003000d9038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 106148857 1250 106147607 106147619
    0x909020303030103080a050c030a0509040b032e1409060901051602030d020f0702100305060102010501060e0a03062d05040201021c021f0e0706080411040504021305130f0803090610 79
    0xe02c03040c040034202030400529440440c2c010070454010213520803c8035983c10641c44001c0c0a80c00100100b84201d00b1f00000840b10b141c00142035860a4a45038450004042456804002511101d5940041c0d0b12a400070300220146690381e031290020790007405081c81c1440070642103840040820040090000449420503800025103682c100c1c40a0010703503594115804003000e0050003002940042e244a11105442c1d15030021030242c102038000b480030340d890b000141d480302c0d03404000c80c0c0c004218075401c1001c90450b0b0454070f01240c4c960022810000894442d004015096444040b40c0c0c2e10ba006000455038104401e9070600f000c04a080315200d81d07114000d48481c10200c8035044903034680105800d0300030a0380142440c507000d004131180c00d541c0d018003600c000d84c220307010344540e110740c1d803c4c00d1a402d250103079500c5941d008254001d9240340841c0f601c0140b00241911400c5a032551841d400104441310701e04256001c0c0760303415143d15083d50003a00d000d6004100d481072160307401d410000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 106150107 1250 106148857 106148863
    0xe010e0f01080d05030a1815052a0f040b040b0a0207080114060d03021e07060306050a08191401050f16030603020a050d02030a0614190e0c091302040903030f0609090203 74
    0x8088180303400b550380c0d01c13680c14101c0030340250034880103259401d0742c4180c200501c8c1004c0d04007052290405000d603035100c0c1c8840745040030007c00c103078064030410889402d10081400030085001e040304801d0800703840301151499a005504050a4103400107000e50300c258040100c0c80041072594003d000701c80e03402020f03916031070f00500b10034081c4040384400c0041500a204451107a81c00c0c02d0409440c5003160b2400307070350f00041c0c4990000308e854180d0210355810210160701c207407003442c0000d041044000d03543c601040c09091094607000740c25048100805428094180a440c4051880b40c1c0f40c184640140300c0d94101012000515203000000c000503113a107103050084540c121810a4071155500100341844120280100b030701e8a410701080742c2024244605004005a1001c1c00208400040c0481103c51260701c114043d070110007100513502e4030b4941142d009803800310490b04000c85031f02003030658130b1031041180420b8031609004000c0d00944030701e00042c0701102c000c2c001c00b0b01c29004252 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 106151357 1250 106150107 106150123
    0xf09050114090702010f32010b04030305160f03020a020405060d0c0306050a0f0213030506090d050d2a0f27030f0218070e100906022508070e010e0f0108 67
    0x40030700e40e501c00240f040b03030007036000c0444a02e20100c00d0281e40101c40c500801a80d40d00700e0b84a00110392001510300c041a283c03141d069891180400c7c2c5018110b8030240e80603003241c0800305603e035011820000084000380d81100c0d41c0c6c443c1d0010508400248100700540c0c8008140b00c1c00b030920086c410300484e5001c8010000c80fa004203001a0b40d4a5207400c3d000648a0051500e01d41d0b03000207070b40700c0c0000440c89444201c034019400d44400d500e4603201940c64000c4d41141d000000c1040c026800306c8025a44600301401d503400c0401c06d000340c83e68100451121640804011a200c50140503d15411440da103485500504d4000c959103402102c0105000c100e02024080300c2085a1047c01c540b19400000c1d1401c0955220028a2170540b400804488110725414040c82c0c1c081d101c911881d000e4060392007940e480b5000741500c584000c0d695141d0700d00d8028030b07903c003c2049070700180b510800d00c0504094001c0d900e01e202c0790740c1080c3c0622510840641049102601c0a00400c001800031500b05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 106152607 1250 106151357 106151359
    0x30509040e01020d0905100c11030a0f090f060e1005190c060e031603020c0303070c0e090a1509020114041508040515010905090d0e0a060c1b0f0f09050114 68
    0x40c00c101c80029076402070103180400c14265250901c01c10a1201c00240344c943c46100c0e400078011940100340465410304602d00640e040e031b00c00c0c003076848501c0c05031503413003180b5486203425aa182da8414240c090f10401f94029030110f191046e0524140c1402c04424140141d5030819903d4050707810080d0b450041c4003502402013082a48400b802c0110300d802502a500e9400212920f0720032400d611041165003e170101c2c0903200302480d61080703023004030686016503000250400914600702001c80ca5160013080d40205000e00601c50000a0517120b000406161350100000c2041c160720000d0318803501524110507522061200704528150404561104030031450f041d44640c9451800600d40003160b03040c1e0b80318040d034400109a031081e60344524030a913881400c031142c0228041c0c00f40e40c940c41041c1d80350b8001da45544240400c41c0184c0304000d0003485281c99858036441900e03100c5410380241c104003030381010f03400c0404c0f0a049800c0300801400400008120075458034800c000702201c03080e010307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 106153857 1250 106152607 106152611
    0x21020d0509040204090e01060f0e060303040b0d09021002010506010e060c0c04020f040306060803090114090f2101110a02070e07020c0409030e060d0f050108070e040602070c080d02070303030605090403050904 91
    0x120201c0e4403250141d034010164143e0a02998558940042c040c052901440344042d5034500b0001e04503601c000c00c2030190714058041c0d0b141a0503c07540043c103500c80d1708407125403516128030200584520140c900e840c7e0b01a40002180e052500004041004500740d90348554400d0001502e43d44000c03458044002d811035006a80780010b50002c9441d006941c4003a0000386032400010320450088010301320b200c42681c4600c2c0e07031114400454158011102c9050304000703480340751249420102000c0304080b0040441d200100414100a0b095511a041100c1100700101726124030a804000c0030303003d400c220020208615055000943d541d110700300544c8135688841840c0285030140c1d02071640000054038080d903500d4440c00030400740c0059404a070409103030200003e203101001c00c0003002e55109034503596040d2540e88604010b500710368426a22a54902d20000700064100150f101c0b00204c0c0e0041c0c1081895418041c04035030350382d40f0541c0905484400c00001035445011207094040c11500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 106155107 1250 106153857 106153867
    0xc020f0c10110706050306030c06040e150118060e0405181b0112050f1b03010605120907050402030103150e010b01050f030709090e0106180614060f07050d090321020d05 74
    0x104444841e502c00503142d460260103c00304059901a00940c800c90341541111000a8a01c0510010344203034400c0110341c440700c1021030b860030081c801c80d107000e00052600101d42c07091a2070380640c42d0510340c0000049181030401010760305140c040c10303912500d01c0441e82c0981c4514025140c550500c0000711414006400380280306a0003189a01c2040841810803c990700c0c0040b00340c1c20130301050301c04082840d511210b55500140c03541c11281600c1d1296540b031b040c2801407403071411025010341008141e003e010f84c0801d0b0340d1120704c00346008500950980b03401d8062240044200c450080740e8221a0b41092800c2d030080c0d82040440c0d4075600320007116552030b500c042c001c488a24003604171000141c10b001d6544c140a50540008007560300c541038040f0420355031000e01c0101c480c544500d190124002d003a0115034640000985032450203030500505d410010b50b901c41c281a000d40914010801304441030040c4542c034030107401180701080c40d6141c5c40c40001d50284d9a500d030788001c08104040010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 106156357 1250 106155107 106155139
    0x1103070507060f050f041e030207090b01090b220902120106050a12091b060201150902161b14030d02120903010603080304060f05130f020d021c0c0501030c020f0c 71
    0x8030055586010380b40c100013908142a201c4d400342c00554098404e00300c00e0300b100910b00c0a005801841c50742c542c000702000351414602c0406410b6a8084506000c0050700004030302e04070f50000c19030890007904103007662180790401e102c01907041d00328810262050003014a02045d42005906540290500c175407510020309007198030b488448900b082c09030600802c81c08004180e02e000851503000d400e07030f41d183c1d900c80d1401c90032550312000c4c0c9108014032070010407045045500903e003240d01070002c400f031100030340c6404802e440745000b440a001200c881c1007000301015610300218207011006024407840340c010080d52a20400203000c042840000c16900e1950258003050040d588145483d44a20300307400c01c5030007031102400c03000c8100e090400182c101e0600c02442100964000400c031910b4646800b403102a40d1000001c0b070300002505140b180340e04100b260326070614420303a0b00604e1a402d010004054444001e40d02c0701750340c03111a041441e8039003c681040b86050035182030000b42c40d946 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 106157607 1250 106156357 106156361
    0x6020f0312151e0301180507030206030c0408070e01090c0804020d0b06040b28060801030b0a0917030414010e161211150408120f0d0b040b030708010605040f110307050706 75
    0x1c00b4140e80003402c001c1c180d80301801801410300144044000304074805503559034203180300b40c00600074101e410a202c144010b1030118082d41d00414000205418192a500654600b410540240005c10402001084a0806030182c0c01400c2c030280f503c000941450383c0480e40006205c2401450b0092203c0010400d45983d070140480c8000145540d15011849410701040c0c4e00c1c0c003000c54400440310380080b03041409490994101c070b074009450405c42d62980c0e03400d401000140c0c012954000c0617100710a0507541040550700485c000c1798031494564400c0f60072821205410001d00041d0008040c49a8822100da0524104c0e03403221218280d00a40e458100801c01500e000c255000d44500b261110036203c9101810541d0803050817601d200c410701ca22040e4502541007616030000c810000c1c0400d01c1c00581110a9040d0041c0010a08009003030009090060036000020036270366481c0200b0591034240210703091000d400c1820000d009410720142958440208008140400041e8150400c11b40c4d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 106158857 1250 106157607 106157641
    0x9013c0e1f0b0a09151b060b0d0c090f0c080c090102030d09030503060a0803070f060e0f06010e0a0f02043006060b0a080916050f03100f0e0706020f0312 67
    0x800d1000310301d40d101c0b80b4240542c0c01030b01040000610b0000082104100070140b82903100c0c0742d03250f01044104001c00444091000c400456859859400c03054164071050601c20189108103240030406042a21300401c448846400807562810b0034214070206410a60068110407054412641d40c0c1d0450300507071a44c4605110740104a1074184400d0501d90701c40080d6001d4401100c840c1d44080d41c5226066990064140240c000d0840f845503070001081c0368060b0800000b01820348078604140340c8040d042c040240d11414281055400b0012000c1c101e10995034002c5c10301c2d07070440c01d05081c00750345840c1228076840801c0200d00100b40800245600c03042401040d40320350184409a115210302da82a041120b0500c0451080307000f040301010041807004440c2108a40c5201c081e14040030000800f0907002c190b42c250140c0710188501c008580184044084003076004588145100030791071411205901075811504518003101d007003500407040710700441c4100200046034503401c03880030b41c4442d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 106160107 1250 106158857 106158901
    0x909010c1d0105040e01141203040308040504020d090b0708070801060914040c1b03030b010806010509240c0a0606031101020c0117070525110909030d020d0b09013c0e 73
    0x7003080001032a1031f042c1a410140c00c4140c424601540380c629080740d40c0d01944c08003e2130040c050005011509081c0c1c003400c00004500d0010070350644a80350a070712008292012000a42c03000b04010740d09820240d12030040500340b404404c2145002c110480051038038020034419501c0701d440e4900c552181d480d0710b0201090495000050040d890003900134a0014812804140410001081980207005403103400b40003a2000c460740408070039521712062500c4500041d80014003520850f04810050b001030b152054400160751410360410300341050160a40d14119070100c40314a01c1c1e0b90303200320382c010380008529002105488800094500d4083c4010f00c1c580140300090481c14000098152032146003c1c414800420100d88188001d400003100c200c1ca45500130000000982050b40c01803c0e2041315101c0003070030a0034a40010f4001c20203a110400260f0020074400d00074441920000040d40000302201031743c1c16605c550808403a01d4030070611484858000510001c20142da90858120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 106161357 1250 106160107 106160129
    0x90606070b0c03040b072f010f0c120b0901150c0302010e03070825023307120801080a03080a090311010603060501081905101107061404020909010c1d010504 69
    0xd00010202c80caa04115000d0300c040c1c582a000c61000c0d40144000321a54028801c0f400003a41d10292102071350000c900305a0f032940d40c4030707220b610b00c1c0f405100f0030f440801c05680d8008038221084150701650602e440c0d041c0f084844d800108000d240b046c0380031131400034a0a2920000410b0b0800f0703801450740c600005007602000800d002001502c40040600075103002144d0035003000840000c1120f015164025000030613180c1141881200f05111150084115883c0990f445c0304985540079030400321040360690b184000c0a10402e40001d003080c05022014001e221103402620001d001140181080d1401c1e42d4900c0c2c0d4100340740c40f0701cad81c00e0010b24050009010740c590300d20f0180b0091034248141c60240c0914001e40302c03200202d107420481160000020a0402071040169005108601802c50101c0b010009800000c103680208241e00184607400c1740b0b6481d1074014000e003140300400001040c2d2400120840d44c070b802c502c6c0c0c0e0340321304112400c44030081d64000044c0c42a1055800c1600101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 106162607 1250 106161357 106161361
    0x6050405160b090111011506110304080f010e0d05130306020307030b12060108010e03040501050d0203060a03050703030201140609040812090c03100b1005030708010e060a030204050a0b0a0f0503070302090606070b 93
    0x308401c0003044403040a984015203508600c60300340c00c8801e047d0030034074488000c22041100034400c10b525007003610f900055906e05542c40300b62a103005a0000c400603c1d9440d84a050300240b0103001016860700e29040141c5055600121112a8031071404010056513010011032440c901c00d9200c8541c01c1d101520300004020440c2078107a48001c00d2090480946c2020389200710714101005030f07021500d06844550412400079000300182d080204441e41081030100b0000c0419000c00070280114081d070000203071ba41c641c0c0c00c00711a52000620803405403120711b0a1100082c074244c2181c6c140307503980380c028006448481009086c5250410300d903034544200001c00c000940341e603000c0440d01d4011038106030107405200701600e090200701c61382c00101d0400d500400600e620844211303400300c001800f1038282c5850754000b404990042d52802d6002d543c4140403041420241c43e240040c00d4500460400745203480006540c400d21400020300400854010644a0b12a0000e0303421240e030054581c1c40d54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 106163857 1250 106162607 106162619
    0x1509050a1206060602030405010c022b0c140301090c05010e030a240f053102041505040b150409020f0c0703060b030d0908060103080304030c0b0901060503150906040605040516 77
    0xd014201d0301560600e1400f039001401038000401c603011101f06864940342e10040303400f002000c403200300c4000103064a81c03100980400e048402e0591880c440d5450143d46410034a244404503104e0003114000c3c0c1c503203090b150100d000031007a007045500901c5c003402c42140c0030b07001c03070305040032100d006203503070100d80c45503483c001360f024135411007d0f8460f010007000c9044040750040e58015159000d40c0750855401d030301400c2404e005c60b40840080c103000350344642503a02040c21078241512180d09440c15680c144114a032074001d030028030104448500c078130707101c001c02040c0350702c102d00c50030315400d0b80092a220104240f1095440034814003050300c80c89650390400601500d021045a80f1034010b00a00c42d280c1c6006101c00d20039201e210005004603070840c0d448003083d80c0040c0044c6c040c0012003107404000b4000d40030851003111150008521189030070241490003140c40c03600081030020300c0c01c00c40100700014960f644075800c00c201284945031410941d050a4290112501c0b40d507880e00d0200300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 106165107 1250 106163857 106163879
    0x613050a060f0b12010f0c03140a0c021203040c060e0906090a0e070801020d090512030c040b09040209030a032102070302280203030a03020306190302030a060f0b18061201020a08011509050a 83
    0x5241b0728090030b01a28140c42c404500b1038042d00241c810216031a000b08140380749a50100c101058140100c0b2a6003d09030050459034004980466514800b160248a00744e8011741008081d0001c1c0c07010740581c24481c00040c20420000c2400e00078981c0e5940b2012104020014040100725030ae0086558000f2061400080c4c511560305840c184161030311107440711030030350171a4420014005074601b42401e107051000c0a512026003254480e409000c02c0210b50340510000410301c2c0719854040a6400040710700c00c08a9107452000621031051042801003a008201c0400341044c84200304542e45242c080700265001d4000060340512012a501c20b000f60154000c6000300ba00700d0380c0302c06a5000b080314141c00842c5000094168000240034070001d0f4242e00b064038007031482c03580401c18080a101050921a09940704c0031030120010500c4091f0505104c0c5d519009941c0c4020340c5400c80300c11001e808000d061141c01d00c840d460304800c403c054400c801ca1000307003d00803c901000c503504c40000b18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 106166357 1250 106165107 106165121
    0x1614041707050f010c1101020709020301090f0506030102030606160203151e060a030f02090411090705181c022101020f04060e010f0f05160506090f0613050a060f0b1201 74
    0x221074481c00d0008603041c985007041161180c0140c0d102040560207a69000c40d41c240140450b055101d00503020800180b6400a176003e4110b000300003801503031540e00c02061307035409003a2501036407041060101c0d980b2010300300c1c3c12464a04210005050b054804645800a6034060740b01c0004410107020348041c01c0f01800b0411001d0024050680c0c458a041040581544c44000c0c0340c54001c3d07180c0c10040c2008000380e48e01600a42c902c000b1101d03060045200d6031411a480c100049002074031041c0b40c24801001486d081c07040d03407421030142d90300034000d84261011002a1098a1803400184000080614160882c0760840203648814102c3ca20f55520341003801208040780d15070000b43d519512a1040143d42286075460a80f4aa4080401e40b000d602c07901300003070410010003000001c0f801c20054240074080d084018644460b00a1005003007010241441440d1010321b119000441c2c00000e20391900f94000100003002480540d007034005100c112400c54100088020f0624200c1065201d81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 106167607 1250 106166357 106166399
    0x70503011a071a06010f0827190c0812030606070303090503070c030b07080a0e0d03111b06150607050a020405070e03010e0f0105100503030d18020904061e0501080303161404 76
    0x1111044511b04180c42c0340000300c8228140718841a104242019082e09503180c186003802038030308010610180001c0000f001c201a514161071000800c00160100141c4607046000580181541072500009035503115000001d0101038490089406001050046400140d4000e03041d1039140e54a1403e1030039014211916400300d580000041c15180c083e004118030414280c0c060802080c0c02c0034180c00034050440c1041c2c0800d000c1c0600b0030150309900800500b00c1400700100890300d4a807050b0450040c2514940d8080c00003448880c0005000043d1036104a90403100800e0f00d07603076070008884442a000a065041d820985101421407010440006030100d080080c0302d00d940f02c801d03c5040d00311521800c0c1d01035100b003081510310131443e402010407402200e00307044c5403000c9070001100010240c4d01980c0803961802a401350120407034412540030b803040340034402d541c541072200307442e03010042050b070108003d070802c99001403050101030100c40c0c0c02c00c0810303242c5440d40b242c0c0c903041c65003039010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 106168857 1250 106167607 106167617
    0xe06030408090901141c050303070305090c0a0602071809080f2b0c12180213060815250c030806030f011e06090b0306010b18041b0314070503011a071a0601 68
    0x52054030040c806c01d2145030010011032642c2c440940031001480d00803c0c42041d030281080460540e038840c80d180380142090340c020078003181010407400801900004000e00c03186000038000c0002c0002c01510100c07040100059100c000540103170001c205624182c104d021600144000b45c8141030b8441071210240e0b40d82d503c0402c0041704500110344241454900c11554150404018034000c1646218603c0d150070105015980b0b0b04214070b02100d2410040403010121304221401ca204444a4403803003410500d4a0700c400c4045014150300300d00c80e005020043c10f00001001d40d1020450301d2440c500b40e000170440315400c0340c2d0314052400315060002140d07041100010b51039901d409040105140140600020391030705d1541d030741c079600a40300ca01301d4541c04a5807002c5917481d4820f4400b2540d01c00080e03401c0804115000b0101e9040001401407002c15100344804a40d103c41078905590720b109d102c40c00242c21288244440c00303914030080004100f640005d5041d80c003170840c00d0062100707880d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 106170107 1250 106168857 106168879
    0x6060806040b090c0702010201091b030b0702120f03061c12030b0f060f030402032a040c08151c08160501150e13030e121b01020304060e0603040809090114 68
    0x82000b91869200801d0340940e03014003140c101401d1000a03c2518414000041c914130b155480c8140710000944040402e004000200140071688a070641d00240c2403003c2c10044140360000d0009004031084065905d20101c000350031074548102805503005001e01f451400c0c0182c0c600700101d03004e1400c00900081c1028682c5006007024522002102c01c000c10003030410341c440840610642008205030b074917129081c03246890015809040c19203d011159110310071101e10184406e4070328550002c000c0080f4070f8100410400144400d200c4860111520544050101080c0c108047d20117009004000c00042c043c501008091000e00a103102d100248101000003880000d00001c602c00c040c0b18501940010302940104012803a4036031086c28091164213140002c1401040c0c0d207001d5500c2540070503081d10700f2103024000b110104400b44021880c0504000c401481d1080c9014203a004030000320110703041180707440641d0403551010380410b50380e603990001d6180c51407010031010b0003500200c071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 106171357 1250 106170107 106170109
    0x1202221505120601050d02150a020303160903120f230c01060504050103081e0d020301080607090509091f0f110a080a020f1215040c020102040905010f030c030b0901020403020307030606060806 84
    0x40806100b075020380f40580ca0304c4248020348041c01400c0313038009000c0c42c440f2941f146140280c003d0303e046078001c607245d14107d405c4040c8031a00c906d251082c0b0901040800014040380a040c01b0b6519528003c0b5100329826400c2d9011441c00108002c0c450509104180006ea00006092800c0800300280940c603a182c0601045840a000182c21a0020442c4403003d211248a40c8242c090440c500380c80c02008034107400880e0020b030000740107600078200380420190b202080c0740c0a07142c11282d1a2507420702030700103a038502d089010018140f051040f40005401182e11402440300d0b419414001e0701d81c8813a0b4241c0c1907100003281000f01d55240007150a03014140700350750340102190042c502e01059601d09086080004003000351307183c05c0300142007003611140141d910801c0c15030005070301c440c1009140e9042d240c05800408049038400030400c0800c51a140c08021207412030707501c007216120a8815800b9106a800c0690075104400c0b00004101541d84503034100e440c0e84e5960101d0f512060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 106172607 1250 106171357 106171369
    0xd0c0c06022106062802030d050c04170d080726040302030415140414030115030825020f0d0c031a04060612030e0121060305010209030d0f091202221505 67
    0x3581d45400c03992203001c2600c1603130817446040b5145600440c1d0500ca507024610b070940700b0403101600c00340004a41004128000550720b400741034040040c1c1002c99201e54020042440102800c0030030115030390a042c0c40c413900c440b40700c80004c0818143c18500e8142400380d070b25805881080c80301181904844a01882540405219003c0d550500d10f01403070400ca0b10891081013484513455561a9000000341313000c1001c03000218031401c52561101c040300050000040d003400603501d5508001c10003001a80c415070403a40400d004c5510240d0007203141041d045402c1c90303410040c44d00d50034801c907104401c40004954400c4c1e20413903045c00742644a02e0700b03e00d800e81113003004010070200d40c4071030030960140d0b400041e00030305602003056030b4000c200c0300c4c01941c0301944140c035140d5000445d0025400c05108d020500112418680c08418900500528084041c41800a07180c0160b00803011076a40c16003018410300185007500790030550001c002d00401480c080081d00195001d4001043e040c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 106173857 1250 106172607 106172617
    0x105010602150f010509040c210606050a0501020601030b040507030803150418050309040e1002070807021807050d0506010219050f06010f1203030f0b04060e1005040b060d0c0c0602210606 82
    0x200f4034103441d902c0c1030305004003490003a204840c10b100300340d000b203042c81036240000c6105c00070515584040402d400d14500700c4009412050140e10144d0313040c001b07a600090070504483c1d201202d4600350340c0d2800d0031400c1003920b1300700030088000002071110f1070008030703000c006454040390200302c00d2200c2d600c4820020008000142160820320210300710f031501c0e034003a86800050070180c907100515072803020100c4e40520703012940198040b40920135420203070400e01c000c4030680c0c104038603401e086d40003030814094441c4000300c85445500040842c2d20038401200300300002c0303425884440316490001d40b15404444050300602c01c2c200002610541d80d523451088903014446901c504125072001c80241004400541a680e1103480a554a031280d220707801c000c0c4140c02419105040035070300302202403103503409030b4407540c107140c40301c04180d940104807040000d0120b4005100c1d45519810f541c5903a80400151169101094103940d40902528440505207106030001a44d81c503802048890301507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 106175107 1250 106173857 106173871
    0x6010f090912050705011506020f070807050307050d2d110102060f1303020a0b0708040b0708040305090d02010c0b041b05030a200303040e0106120e030712080703020f0309010501060215 81
    0x5142c0620101500031002880c403180640d001003804c0c0c2e10031506000c903169a9202c02d006034090000038100003810300100d00900311000203020014a0000020754608550007881e00c00c82e000c0090a081000203a51304610310720704403d0001c0f01240e900e2180d1140800201500c4107900c0540041007584042005481940c9440c9000401c3e219100a5440c0c4105401d04406610030686944045541246014800e40721076071480e50a20b00b503e450481d03541c0c0600620b00340003040c030610000075000400d03074011010986580c0b01a000900049501760603c403005484c0d9000103043c0700501608407041220142c1c0c05041d1203505941d1020325540718160800500030300034907241e85200d189042d0104200c940010100c0e0300381525a107058883d90020703400714000c905400700881d0001854010111081c280e90041d504000c01511481041105004040e04001c2880d0024203258000e906940314030448100c444d442e8904410030328002c00c02809544094441c0c60301d64122007d03100081886810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 106176357 1250 106175107 106175123
    0x2180f041112030c1c020d0512040309090f0606030509160b0f040e0a0203040b0106050909070e06190507020901090501050d1e0b07020a12050c0d0c050102070209070206010f0909 78
    0x1403603807100c545082201c00d00c140d00248002d9a0400d1042c10000390481d40c1a4902602001c566260072015050b00306a805095400200c40c41c508a50058292164070f42c42403d1908182d54501c0c041310140d540d0f03040858401d14101d07040500d00c455500c0003043d0b034000e450800440d04c0b1541429519104800e0341d101d0301440050602802d28007401401720030151400484c102038503442d407156141d1040380d1004900b9404410030083c00700c10303034040d0300401d00c1c0c0c14200e2804803640c0210f00e40a00c02403d0b0740c1817003010103000e07495803075990842c2c0000c402e0001c507040c0858118801010360340101026481055a2400400c16001c648a503e040381e400030400d0046143c59920034800801900050640340c80401111000c00d540d522082d21480c15a13000c0c1c44103400d18030b82940c1d012820711400c0100a800d02c01c4242018000400c0300440160342044000709400b450400e0180c840d5800094104140b0801d200440c1c1d00092501d05861594000e01c0c041a29800b010003254403003040600740750 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 106177607 1250 106176357 106176361
    0x31e030c15100603090f0807030c05060109050408031501090b0301060903051b01090e070201090c030b0105010807030c080a0b060705070b0a0809030703020318060d050108071a0c060c0c0312011202180f 88
    0x10b03020754003484121b44900740214055240e81c462461a400038141500402d840b0328101d01003000038412980906520081080300d0f00f883d44640c2000c1c013009150900d044403500c44004980c0c007681c51040100034607402c1b541e4035030b11410020312600443c80111002d01ca1402c2c1c810320080d000c02c01c001654410795624541a14101010001c00c5026040c3e10655699065401c0032400340d01020001c1e60264590004651400c03000611180c0014600340c10149000c0c1894070700c1d0752001c0c4480d0082004000426a9180d00e80065854425007600905030b10980d000001d52201007006445400001d07164518581e903140d0040d0340300e220b010300003001a001000442c0008030744602d5003006010140c80c941c00c115140303000c1c004441003a00704000543c4284010011202c0701841009090503005c2d00e5820100341200c1c1c1c40c2d035408003820895040c0404030703002416007010029520000c1807403083d0085940d440010a01c043c0d1100426406001d81e0103412840f1120804107034042c020f009035a004c13607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 106178857 1250 106177607 106177619
    0xd050403110d09050a09090b06130f05130203010b240a05040302030d0905030d0504030503040b0307031103010303110d030903080f071103040902130e0408030114031e030c1510 77
    0x410004008605000c98150a680030700c0c8100820502080e081d11280519400c107001c01160403800e50240c16640d003490034840000d641c412455803c0041a03c20b180b104009031007002c0640040c83c8031400261074031007040952005115142590390081d002004062048018080c1c0b49001114510607200700711044900881501c1c010040d49400380390a5040948a40c0083e090400b00841c40d400180c03400c000380000d190900910b80484480d080c0a0b15052459a42603120300803445185940e4801000040406000b0b03000300b200d441917807294990740e40e140e00e001390031500c072150700c003e007031040c080c00b04c0e60b06000e44203414545401d902ca484a9079079420440703040042c000c004030100444120519801c01040010704094072010300056140c03411400085c18a1500d5071141c210090010140004922603000311fa05440c043c2500940c0c0d400c002d0046032a0a410341e5000050f409085586a0754001c048003406a0442100a844a16841300b04030054104252603200084100b89002c02032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106180107 1250 106178857 106178861
    0x10503060403110114040602180a061211131d07032304050a02040609021b01020f04050112021201140906030a03020c12150a02190207030503040506180d11030c04060503030d 76
    0x20000f40000701c0d640d0750184d404010740c0300980f01103403269000305003500e038011155000210301c1000c3e02c1003c4010300c0c16100401400c02001d10302c0707901d40c2d200d4002810701c0d0100d0443e0f45003040100001d0100340d541158048010b0f0383c0c05195002c4c9550070210328058441e00038000401d580d042d1b40101d5840000d84070782c0c1c020380540f0489151240c0303001000140c607140140c900624041e040161118050140003a020400240820150b48100408115810003000380c07016500c0a10300980c115800084042c000d200f02c4046c19070b29250303500001006a803005c04e200521f0026070701c1c0081510303030000785a89c92664034070050150700310700282e1030203050034000c07580d00c1f001c03c8084542217102d15501d070905140079202941c6007900000c2091494905020b015100a000d10007400d1041c80c540b0384a071a805a40a41031003501c000800303040b400460100c170321500e00e0050400000d0200c51814003200030703aa0101134000d02802c0325180d110725152240604490000c0d0180d40703403000203180a00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106181357 1250 106180107 106180127
    0xb07021201200c0c090108151305160f120507050103020f2503020d090b160c0302090f0403080901020a080112030302040807030f03020114071b02060409020a09051206010503060403 79
    0x40d1540da114025444403810202d100512002c04100036a211410305030641130901e1010002d000e1400d0b000100030803000007485a141c4032840884940c0381d12161b04207078135101c0480c0050468030075445142c0a10024108034022981140c562541c03803982d6071142140c851348110007900c9508007010421441d40241c0041c4110458034000600d00341d08002000e03c07101c0f901c1a00b821560481294904240c6c0400c6280000c050600b42640c5030342c03800f904242c0c80c3c81000246681303441081b85000410103900b00c2c203c0039541c020210a003030710300501c040c0400d000c2101c050300000c9003003010070f01090040c0708135043c082141e83e4500c0b280e824440d290100399800001202010f40c01c20001030621000e10618014511450010010f0801d6090080c25280e03d0751900443c54829018407010307a4110080d190449a0103400800100720f600004e001c1e4040e42c0c2c0b081c82d60b240005480c00401c0c0d403000e1000705440c030031078210341c503d2a005081665140309005c0c240c1c1690180011a0200703020300b000358 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106182607 1250 106181357 106181389
    0x60709050303161704091a0d05061f0e0915010b04120b13081209060c09090f06180106092301020304052115060103140601050a0c0606090e070303080c040b0702 70
    0x54038011104c49042c1480d403203039011000c02d590b1105005600700e8520240f0500810450b4116000c840c581c5034251030f10405004005040d11004443c00c080b100c180e211401004c105d074a840306403a00c4200181c880e00c2403521100030346140c03000401c40c00c01c030106aa06407009036149030124041640e40820800c030140c050000e074804403100c0c2d40000c091034000e05e100e0034014106910b41c2080130b111840d0501c0076107059600103083c801c04407262141d00b000e80d4020598004a000c585803440410b6540410a00c45c80c5160711000021910a420013400000c0307412080c14510052103900f409003000703401700c0c0102e0040e08100000c003c1c9240038110076030b01d81940c40280c1813100350a52040c0c80c18004c504c00d00001c5002000b0032085603054440c000e414a00d5541d0088140307003070b0b00020030700d10a943c94842407102c2e00071030b0028000b503a403200025000006041256420f8025625a130b0f8403503100c101c00140c04400050003882490702610200c4680c0311016051461030390801440c800264110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106183857 1250 106182607 106182623
    0x2030d0e010e0a0311070f030215031509010602010606090905100611190c03030306080a030905090903070f050604210909020f0f03040309090506040b0904080912160806070905030316 80
    0x4000303200018009002010b102c5c0d1902030f10341c0281211641062040e41c42110002e801000c20805611014450f141c16041000701650320741d90251140703070601c0318a004540168542e40007040c00364056103d041919015103448028a9035011904290744080341c0d03030603610305060010440a03004858030b4002d40c562209a4503c4500c00e0b915400103601a04155005410000100181074161280402404c1c1840180c00b01000d141c074050b16002ca544a11801542c003600054104442803055441160740015000101e54980c10026138030442070f0742c15240d81c544401403840d81c00350011400920340c496142c00a40314079061000b8006e40040e02100342e1000100408a682d200ea00001c1d440f440c4262180307403d203400c28070f544007240e50090116004502d40004254160313946181ca40c3c0c0554410403141e1340c1d035004c8cc082102c0f0f21500e050120079200d002424070268103000040c5082d104004100d451a94418104403026540c0e48a19501078100f0402c4c038040e103c81e0a15402c45600034426 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106185107 1250 106183857 106183871
    0xc060a050d0b0a0b1210150e1e0a060c1b060c0f03120203090d1706030703060207050c09090307030e040c0c060f060f4109070c021906180602030d0e01 66
    0x103809050b9114120b00410314507602c040042820b040c6410001400c47c14110f59500c0d60b880c0d8025050054904c1c44078800d0000342054a821700311001520189072024280f42d004d16134424010700242e02d001002c0f100e100f0202d00107481034040360a00e4084405590b10700c8020121521a69514881403400b582001381003140d0000c2c0d00c80380e00045000d45041001001d80c07090188001b0100c100c10b9a0702d82018403908144802c0703640000e468801da80e000100160758003ca03251052410b02c12101c540d4101d8022030405c8255107005c4081c000060080e207400d1841c0010380201300880b80c004550002042c12001210f001c10000c1e40704445086c61070500041e02d03519810f040700c1414031a4000c604607241c9810346000c81c0d4200d0105010b03121000039110f141c0c5503c403041403840040c3c007580b40c001c44d800d10000e42c1180c0b192001582540c0c0180c103914260b04232501000d83e905c424055900456024503011295003d0042150206c42c0300307a0207036003083e0a40a0b440d010b44034100c5232202642d203400c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106186357 1250 106185107 106185119
    0x10912120f050c01140f0702010509070611010605033a0807030902040b091f0b0301050f0105070c03060c08060f0628030b060d0204080c011419050f1206030c060a050d0b0a 75
    0x1040c42804107681404030031710720f4041181c40e201d00b4020b2508086904200030b03c83c00c0700c000500c0109803496410480c1e461a40781044600505079540840d915110325100c4107032030310031903e215546510702c410f01c00c203050940501e001c403240414210000244036070000344c0e2a0344203620240b20144001c002245014000e03001864035401515502c0d210ba05145142c18801660812007009100b0b00c0343d01415903241100041c980500103d6042c11300c1b00004001042105142c500e801039640624200811004910014100881160211f020324210010400300b4038005007601e062401505030740c40c0c51881e44400910040006240030305040d1102c00c51700c00c42d07a481d000341030401d403402401a112454038101d41d1400742d10407034485c1484220300d5004030303e90f0140101d4403089030640c404004418040001c484910680c04400b18514020a0b20401c0549269807240035060450448903201c0a400420589100e8890703c0310104001300304400000b116600203c068800080002c1001d5036100303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106187607 1250 106186357 106186361
    0x70509040b033702030a0f170f0702030c010c050a02040b041518050a0501030309090911060403081b071202040509030912070806070806010c08031015030605010912120f050c01 77
    0x69400714480101c40c05542d008105040150f80f0191408020f8485500e401094803100d54120180180290711890b000740540c001a244409100300c80d0540e9400c0c0c4d4005010040d00701c0340b0300702d10078024003803a0400341d0711640001c44456040409444c1020301c0f030382000001c20b0801d03801604503469440c45110620b4410341e0700003c0c4180e101d480031401c04c2148031011218002d00880d1500c0c542030040c03001c240c1c050011816643e50b0a030000f80180300c1d0410b000032207401000198403800004010040203a01301c05007107910308408201d455075409420158444a8900442c1d8101020051a101610301034000d6900719080100b40c0e450b250250021498140720000120800d600c4031104101d1603800f0440380c0d03807094140c54602c81c00d040c401d000901c2a40c0404010b083d551010000c22042c0e004030f148034004100300c0c0e41000309400681d00140141a0340c0c0316103800304042c8000003403068004069840c0c990f80c0030711500300c81401c610050b03c05010365515507007000384c240106140140d0074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106188857 1250 106187607 106187623
    0x307050715021c110f06011421030703050c07030f23010608061603060905070305040c1a0a08040303140901050702070906152718060914070e03030721020601050d0803070509040b03 79
    0x1700e81602040c8d070043c814044480d166408000c0042d220340089210720101100340c0321044d605183c016650185060018980b0038981c2000c1c141418000c1402d04100c1200c50840c203180d41302055030f21403080c600c91305088a400744200d1480b50003203000549800100740c000200d0307000d135041c001070080d11b03590701c0d0303045070700844204c0c2c04030b9170f01e005210922941c4020b540c010404045030300c0d132903c207552040304075000e90500030041c40300b03c001080407d4001e810040202c3d1484030786680c1c074605405110b01a241c160b03a501d001d4020440302050f011628080c51064849081c2c003002d101c0120700c0c0c200d40007012205039a0300381100c281c078003041160030300e100f10040070890095101203241207030140403a4101d6000c402d030645001d00c01200c203065100700035841f00150030a65004808100802c1c251310881900400c0d08948000034410b8030404440b111459109900f03d404a070380f11000d0201c0018444000f801c10901803002409161194004116a0801900100d48013030310307002180c505549 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106190107 1250 106188857 106188869
    0x60316081b0d030c02010302090a1815080a17031803040906140603071b03020106090c02210c061801090c06050703171e0411030307050715021c110f0601 67
    0x1c56020240011014444201d15031011038849a8000c1255405003e01411840c000e042c1500030498080940c0c0d01c5006000900c9150807500c02c229881c21004010700a055200d02141c1114802080f0440d001903808052070703015021a12000c038004e00030b03809030802840400c4204003015890648542480580010002d90b080070850509240700034100210035941d00b0f00070002031080202090f0300080a0001e040801140100a40107040481c007410386d6030000e01e0504d003055610802540c0c00500d035a01900c00407490369200003120f90b11a030740c4c4a2040e602c1120350010000c10021340c0b0302c51300c00006020135400040c2c044003550719548408a40c0d40501c020450208042042c503404c4090500091190040602c262600c01c48401204411000c43d050301100440060104103207600c40400968000701100d45072800c03072620603030b80c044038002d040c0b580c40b00d80d120004943c00000d2058820300c80c02d80329800c4240c290002c882003400c0415060350f62082c0c0e900ea01190074180140c90107084 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106191357 1250 106190107 106190113
    0x606090a080d02010c03150302040905100c05040f08190b1e011203030506010206060a090b0402070602030f010810050c07030305070c0c0308180303070f030c021306060504150e01020c0906031608 85
    0x3031510000381c2113922011404040c1801d007ca0201d044054000940c103a03541250005040346441c1003161606900c984404503851824600c0e150068000014000b214408200001c0c030300c0d164003c81d5240c08c00e10fa00682141c07603620f140400a80304079201548031182e0700c0e01e10075520202510441c62102a0b001c181c4002c10202032806265150180c0780c0c1c000401e0000b4401c0b81407800c0481e01102451040c0586140d0322028503071070369501c1d01222240c91300001d06640300d0805004c001d010741c000b84034140141c456140000c181400d240192880703880c1f40ea50690800c01651819006080d00410340420050866500c2c3c1c0020100080c190207540100902b503102d2145038402e8104050300d117500c620a91042c00384170001912000d181c0d014682c1450041e01042403440860b1a2a060310720305840745003040c40c0071401540c41006082245c10b0b103001702000c0d06143e402526002208cd0b0300a0041e08181100501410550f22103900000302404a400903107203000800302d90112078204080d190 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106192607 1250 106191357 106191373
    0x2061312110301052802040f03050f0c180a1a03030c0105010603060f0b030c0a03020405181012080910120903030510091b030f0b0904030e0108010906050105040b030606090a08 77
    0x480d0181d030940301c0c405a0003000941010310f2217032408100100e282d8501601c500c101000103202e901070314000c00c1d5124070081c0307054883ca00640ca82201e0140c1a429100d615a02c0582c2e1414040070f41c400007000183ca101511000000030141c0446c100b83d103207200f00c035065007105850400c01400b8003041d9900009880d41495002001d070b0b603e5501c200f031000d003418400c0c0f20041342001142d80001c00b2900c001e58482d2181020360285c007440e80704d00e910003020340040050322840b8640d41d20a81d07500d50002c042c2500d17240044800a09940043c1152000b03110568503801d200b105160520201e080450715410301c042202c00765400c00c0f804400103500e40052081d0355400301e000f40058210703048240403040004c1580b42d0040c80202145c004c1503140c0c101c0d0481c19150b648002103540703000e4100d02d011b203032504026080c03480f40714409000503000d400006d00c00c2a2031051205552059503000d1030a85400345030355058202600b915072000c0104207812040d0703142101c0600600c407802c0540098 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106193857 1250 106192607 106192613
    0xa0905040b060f0f04200f04090c0f0504031202070306050a090c050904080703081e010f081009031d0609030a050c03120903060403080403120c050309070b120f0402061312 75
    0x94480070b00300600800c0e9084500c2425910440b40e1040d0704400e0781c2c005200580352208803864001d01c1001c1c0e180680003c0c800d10040c000a00410030382d520054180650101c01e5400c2303903900320001045001641c14801400001c00305500607a1584180c411074070681c0d2691170308400c0310030694203600620b0760303001c40b40200260b010007203005020841e070f003a1551034640c60b030317a880d441085001005c0000200c00114503110b000250010b000d20030500021540c1c5507032010904080500850b461031141c4240764044855074040e565005605688006c1121321009461364800184065260f11000c2401231101303585007084024000c0b4001c00080007440d80c0c02c0145030400700d91040800b0116000c010a40413a2000200c1c5604030340e041c0741080a5940e103040444007803146d80900c0c03568508100030808901e40c040099030056170585c041c0c400b9556500007100c840d10603090b00a050400701c000184440b051045d14580c02800035003241d10b010046035260183c404540c00410a4100c2003080900b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106195107 1250 106193857 106193873
    0x6010b0d0b0415090c0507120201090309080a05120d0b130f0b090c09010804020103110307020703030f0228020102030705160e010b04060518010203041e03020316060503040609030203090a090504 85
    0x14032055604204003950301e6403071811003845020b11310a050300c8000b50182c2c9440381084540040e00322500504c0d8001455009000e0081e04009600241d480c140109800030046440d61015034481d006000901901110200c1c0c0e41049501c200850764a0039180d40648030060820107500ca08940011003100c440203072411601d040c821b003400b80440c9010400c0c81809581107600c60340302424204102d68962004902404080d151028501d03c08010f028007035400080c24000e503403103900c4080701d00640c044200c2e5a40c0c0004d00130f00e10847c1c03450f0b80303035241916031001c0c002150040c41564a440410f8171030601e450000b0448911030304621f002000906252840c840c05460100682c1e03140c41d1030240024140d0080001c40001c4800c06040d40440343c2c02007040710300a140c0100c004180e4034009480e483d40e88040d1006901901403e11031b10301c1c030b4007140d88841c1a5030098a6050540c2c03500d8940070000c02002c80d048007584000c0005100c43d81e10751507140002c005a01002c40c5c0380c941807600c421 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106196357 1250 106195107 106195121
    0x50702060c0f090406031401090309090203090d030504050709050907080f07050f0f010e120a02040f02070c0b07030306030b01150e0d02090a090c0506070f0c060c020f010c110306010b0d 81
    0x2103410a034140924000404116180100010940d64407050104001801082598802801c1d1040aa00440e8805040d04000003141c025228140d240780e480f440903090303110894081c00315805c40d180500700140a40e00c00b540150150701110388054a503140314040b10f40960300005180d008034402c2000c184208011034104074140c0c0130344201841c01c804249040e82c00ca04051095014071a01038190344280541d404c03a90005100c00c1c0060030080940e9118110f0040607030165080ca88103110f1a4024000c9945031517104102000491400032060840d2b007140008904041c1c40300800400b007486513044034041d1004824054014140f00c901a001c4540502c14038007410800c011800944e5488014a5025082c04070125501c0130354030781038890313141581085a110b080450204248440800500c00b018880c82c1030403141c0381c842900340c81074030030208000d51110303080810780341a5100364403070300300c15210700d1303c902d07100c980c00c40002d05092003600020507088010034400c12148660103108 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106197607 1250 106196357 106196371
    0xe060118020f070609110a1a03040b1801090620090603061203070804081c020d02060a050c0705120414032b05040e0f042001020a0807030c0203240a0b1e0109080a051005 74
    0xc8c4000e404800303021440d00000340040c000c022101c001a0700704400070340c0d80c107100f490b04000b0000c505080c50003000414802c07500714002040f03e01620011a1010102c0f00208801018a41941e845208000000c020510b015038140000d1044400040d82140030f4000341c071821024002208140a901d010301e100081c003201194084850040b840ba0045225900b0400660340401c09a48420b00d66000340b040580050a40c410050800c815011600240050340c041c444000c02d09200c24040642d1003050701d001c109018403c5a80e03070500100107044862400c52418070f2424140e50301c065924544003140c060304031100c02c804110070802c01003041c0c0084600a12014801039004000030355880c1040e20041040400040c240c080c0b60086011940e1241c3c0242141c01c4840f486011400d495042c1604040011082012a6221324280070703052240070060709808005004000580d0303a0016070360b009040c0140f555012170045428065100c1840c001c10041606d01d250031100022030f0b00090280c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106198857 1250 106197607 106197629
    0x6020304120e0d0f111509030705030106051302090a0302060307030b04052203050310090228050f0703030f0f181a070c080307030f02070c090e060118020f070609110a 73
    0xc0b010681da01d540704220103410800d909145201445c100c82c00800b03071140d40340c0c00034041d41000c0c120303204440201188a030503000d86100e50b54803c01d050070385405000d01d66011040c1a8400d40c40c48140d400b400c00c10320010880c00703485540e03801044059005440b4500004c1d1200c401500c14180750203596002a0816602421a0401a80c44804903112032004041000000124505410309d500c0c1d180608600003013190b44506000031741801c01c000c80003002da07070090b41e1408420710b40214142c1b400c43e014241707640e01d000c800b503808400900e080c845845200d0303a00d001150003e00f05106840c0d24100080c0c001400c100c07503080c19071083c10f13107240e2418207038466400c1042c0745a0007140407000e5035210000030744941b18680c0c1a405400c0e039215580c002840859000180500a0104000c440310000d04000e07924400c008141c40b642d09000b5510720000c8100c82d11080c4229600500240918a00d19410302c440c503503840d01500c00e0900141d890184030000d150452604468500040c0408114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106200107 1250 106198857 106198877
    0xf0703020d1a101103180102010b03030c061006030614090402120105010b03060a14060f0703050c0a110a060503070e15040902041d01050108161b0813030605090c010203340602030412 80
    0x22185d03a80c40382d086ca800483d4404450712034540d0003500a001c1124004094035254982c0d050100c0d41c6071000c47d5207000e1072226450001d0b03007038064880c1c8420340d0364410403040504100c0c402d01280d003c000d04106d0304031990f0b8424440b40b04081c8902d50203403980420103645c0313091210420103a01c040e41c0000004c804921401000e42ea140c200301c559058200d44110303101e2605080036619402615400d0029020f20001201000340c0c294100c0804001100c183c1d40306a2101011a1140000c0b2841c1000c6003010b203055003545812458481c3d2400103c1c41546050385a403c0113003641c02c140c0c080040d000e40c1000b004011184280001c1c0505420700c0c000083d460701c000900700d000303140c00740c0005000170001d1804101c410a18548601a0480070a5540307008510050016940d9444244d940610307090100b6080c85001c101e014000301c4c141c0c01181821103504190404070b409010301040c81c00c00d1101c43c4005140080705680c038a024480c0180c41780b9040c01e0a408002c10305109408000720710034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106201357 1250 106200107 106200137
    0x6010902090f0d020409050304080d0f034d030a0b0103020306030d11070b041203030501050a05010207061404080601060203040e0f010e0103060b0102010e010513170a080f0703020d1a10 81
    0x1240300500b0101c0b04480720120b0303400814010804090302400700e002c00580807a1110700010451404032455550108000d41407908504035150b001c1520644ac5c4441c0746ea0401c5030712442c02d00203a0030180b04c80b1070805015a110f45402002242c0803580803008820002d04010920820304045400e003010b44c5140740500c0000c2d1107030f0003110b44a080c80301d94403001552210402500c40038145002c0e0700c507600c6445040c40e510300b62880008a000a04000022416042c110f17160412603006030010300e08507040203011b03540960790400000300b0310741c103000000308104e0070031802d4001c0c5426005907588905081405201c42001040c4100c440c440304010410004911800c1e411242c003e88001801010b000040b405440d030000100041d6003880c091140344100c00c0b01580996200e07000c4c503c05074400900c143d42501485400d28041140400058098074100c051903500c60014a001880c00c451500c04074101d41c03162100145101030800a07542c1760a0080c0c50b0200001182010321039035521030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106202607 1250 106201357 106201369
    0x1407060e010c0c05060a030b042412030507020307141002010203010b1c020903100506040b010311030601050a0c08031303030c180303121e0b1005120403031a030109030e030601090209 80
    0x10354100700b40e42d06210203002554010303d000d088024592651001408070040c00780010003c00d0f4415440e1000c0750030020004500d0100350405251030916161508101d0b0002c4c42012000f6824003001f04002c80052b5428094000544103101c0d07090b10001d41c0e0390500c60141004e40004055a10410060141014040c140c079059005140250006614141040041d002c1d00014030307058410300740c0104010645400c014442c1409071070810182344007600440a480031603004401200c810001702c3d80c44e51150004081042c1c1604114500d0040c56890b1403882d072080301c2c0d9074000c50b01c003451704040562500400925030420720705800124400d4001540c411450302c00201880b10b036009200102d4104e4000c0300b000b050000e0b8074000c6818240a150141031256106845a00380c800c5071001c150144059800c0181e401e07246c0715450f070f140c1d6030580c024500000b0218180620101d142c40c035a509000d540c074498465614107104c24405418980b5103030341a00019100b40c01131204840d152911 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106203857 1250 106202607 106202627
    0x10801051f120606081005160504030b01140f060406020303040203163f0302010207050d05040f0e040503070b131b05060706150305240c031909030e0907020703140706 73
    0xd03071100b00b40311910305400140b00b254003204c000d001d28188548041c9151f030207a4410074030701c01c02245589404030304556a01ca01e00000f000290010014040007104403101904c0d150082c2c069401d20b450301c2c2c00203149030020b50218006030300000030081107080c2070080b2040316228030340c005c55081c10030841d94003405c030394100c0b060480c00044030001255280c0e10503003041d144280245400c88030310b050007030103507000c08425201c41c844da00c841d2108500c1078007100c085a140880030b000450820003d04058040503205aa04e44010702c500310200d0220303058640980c0100340c00e64030040c203d1070300c0ba454402070009448581400c0030f08000360b845a108541807980d100000003030880800d01480400b566540016119200b0b08401400081240c030010002048141105038940c1e264040f0859521044607280d8468079031142c0f91840c4ca106d504000751074ad22a0401c0700340b4806490100c1c805200031030b8100010f80c4800340820138811010154111101081d0141c0045420209c0103045007004c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106205107 1250 106203857 106203869
    0x3090d0807060912200304050901051918020c060906040302030f131203052110060c1a0c031801020f040608070504090204060f080106110a080d090218010801051f 71
    0x200003410381c01c100060707010790855548803114800300140540001c00d40300551220308140041c050015a05403800410340b422500000d14009150b8282001d101a00d007800e040365610b80643c6002081c8840340c411040143c4980301001038844030210344461804c0f40207026000c1d940c01c51014000844d6002c4200d540340007149140304d03515403c00040309111f400d40c0d400f0340d41c1c0f192040c1c5c0120400d03601200500700666846608400c01d82d4407404408080d0042c0e801110100704400200403003401071061080310b500034a41c1d244509400c00040b1200300d001c9804c0d01c0d40001c000200100001c1c7c0344e511910014503400214280b440311140e2003468481c034050752040c4103071030740007a46c1d0900c2102110060314035036106544491707a030700d00940b420500301c0c0700740080741c0302c50300221b02544900d003540c03d40005040103081002003034413070004603404881040e100c20b845009840240c1c1320100035000030040150340414a42c5440c85482c02c50304042c184001c10b0b4004550400c22030411800281540c3c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106206357 1250 106205107 106205123
    0x30402011418010e0f180901050f070909050709050607060606020d02030f070f020f030f01020c0111030606121519050307051903060506042901020d050a02030406032705100e03090d 79
    0x140c950001707002010080c1c1c88a41c0054242c804a40740c0710644000e900420a9000a0040f9210394000e01d403490012901080041e04400c4208019201500f05980000440c104a0081034441c0082001c56011400c107803074030354a41d6010040c05504012a807030018551000e107081c98140c1c031b0743e100103210b0039001410000380c1a404209642e02e0138038403903030300000408690320154a000307c81e000c1c2d009070301c1442840d464600b03056050340b4040c044920a11005050b281b0b41501c3d17000000c00701c00d024080511030350401c01c0940d81501d40e0b011a03c508a4030707940011145182c0303000c051400300340e42c1140340a0311195482d992862704851a040a49074011000301c0c8079a18540854003c0c08403810340c200c144803001909404a0305100c079140d8200007a426605040e007000d07000d8030103110303001800c00180d01c2000b04000d1a44264003e540107100021084820303c286c0803000007084401200359216004200c00301d40e11210351140504142c4007034091420000e4440005000c03000d5014080d020320 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106207607 1250 106206357 106206377
    0xb070f2109020f0306011e0501080c030604020304050a0209100807080a0201090509070c0204090602070605060132040b0c01150f03020f09040f050d080718030209370203040201141801 80
    0x99206903c258010501500b11001d81d070355821100440d00100694901039400280c01180340c2d44216507441c4a0680c3c20751302c0f1702d9501c403842030000a40c002001911580580c0b000980140e4814609a018140b95034881360802c3c01c114040d810810160300102d2258440c4c002c1c800140d8116140034220365040703071600d101c1d5650b8182616801e64180000794060b10740628501000344a5024002c90b50140b4000c00069844000545140c05202a0381d894198101030501480320300040160702041d4000b402030829513a032032050072070b8203c0700c040b1001d039440e50b03109102a00d002e13041c00002c01c0b03009001441c03186181c020400044400505071300030f4104800107014480e06040d20f00a050348441214800300705001300811900d410380344500021803081c12000d03e00442001d0100b80d0f034008090151030340311a03841c6501d40410002c0221003990078070100300f90300002c0301c42d18454000400c2c0540c0d64501803000401c2d0a41d0401c1d1000c503404148524003c100741ea51220180503030a0078100d080c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106208857 1250 106207607 106207609
    0x170c120304090f06030605090604031d030a020d050c0418080a120b1c06060504020f0405060313020a060206071202030f0601030f060909050304030213020a0203030a0c03060906030b070f210902 84
    0x1072045400c200601400e005101e002488a540504200c90182104001355101e40d40c1503030b02c03008280c8003e0b00150342d1f2004082000d4159004410485c00141111980f00f034507800f00343e50680c0c400c0240c1c1c0d26004101c800e015070405000b403289a4868548581c3c20004c181c0d90444140a0032800c142000b5004580c880b54926139840884e14200051203802d00f500c00140a80e0b14414455044848a080420009040c1414029078a145100007c11401c1034244428489039400041031004082292030380400036072a02c030009000b400d4142c0c00751440385008180a804240044e1280380128030400400200e0420142069007220003482c01103100b0b0003115000c0007502080d0044050140f401c0c4ca40400c0060000003401281d00c00d032800c001c5501075000c5603049008580c03a580c00360308100700040c8401c00941c0b221044001608000854a0310b031003400701140c802e90000c603844003090090042480c5c110802140f001e499103441d021100325030610f80c142640404001840d50b444444010071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106210107 1250 106208857 106208863
    0x70e010305160302100f0c020a032001020105060f010c0602070611040905010b07020607020409050c13150b0408032505010207030306061821031103031006140c030301050906120a1b170c12 82
    0x1f595400904078039030217071207017040200140140144103e010604007001d049500602405106010040803101c1d2000818015201110441c90460301c041e030801448000504074401c0c8694007056401d12078659050202040c1201c4041e0890100d464050044400594454048409103a030503600822140080e15040b842d20b01d40074100ca0b80143c074002442c142d0301c3c0c80c2c0c0c00b507520844140003040400ba50380c0340e03ca01501ca140102d403010b400030440e000c500e0342442c0320120f05116512504801b154161900d42c01c90308080800c0700000c4e11207500b00600c2d0750000b6892503400c098503003c01d9507450146202c00011640300041451003c50040e47d041c507002e8940e20f600d09441e0000d0303aa03680380400401c5561000c90240e040454103600300c1d00321107990700040c1c580300c4940000440c6507034205000c05c400c1410051400d40d11503100002c810907010244a0303445039a102d035060800201130042e06601290450b005101a101b07400f01c5031211030000981c400e0b0411003076038210000550000d240d0b017 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106211357 1250 106210107 106210127
    0x309060905220e0609031908090706081f030f060501050402030609061e180f09030c03160f0203011a0109050319060b0604050d120909020307021c030608070e010305160302100f 77
    0xf030718019601005404480880106220102c00c03e640c2d82d07440c0600320555258900303680f1082c40350f01c212030a01c94140210300d82604504041c80d40103880d0152003800101c040d881d001281c0070300c032001a440c20040769000c0e0b0741c0580000c490560030344c50308038007048072010f004200070b01c035443c420420b405030000041d440d0004d4078080c04400303100400b05212814808140c58a000d80d0001e00d00140e140c103004401d6a1203201260090b514000c030840d07400407840040001030303a060701e00f10503800040e5030910501c900c00001c12721300e20000d00c1080002d050008a81d0180d40260001c1035850002c1d4140c421948043c3d521040004040b499000451302a00594001c00d80222109100380144040c5029440c408885035490f1844a62640064001d9003c1030325010302681c0968012680d6548082c5c0036500020075290001380c050b5545181440c207041c0394040940500c41100600600c2014011100f0b00c1400441c400111803a56003c121540909034001c0c0070001c12007030400070300d803203121650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106212607 1250 106211357 106211381
    0x70f0c15060905010302030712050a06091a0103030f0306050f0307180f090804030501050a0902010906080603160f030203070503031207081005030706110d0c030f050c100203090a030906090522 84
    0x1240a4407021202c0c0100000c0c04180d10a01c1034041c00a00c1ca00c414400481c1c00f5030100140800b030780f0980c2d4910203414096070840d850089050410601030a100805000314000c3d6210300b83c5541e40180a02102d100e40c20583c0036440000e903014598070001040021900031400311003000640031407400040c610305100001450030f002041061001a5001e0400e50780034800801440e00d400c1c0e0120100e448c000402401306075028402c07c001030150710015448031001c0c003541c8048450f03019000302c41d440703600200360401040740c0500079810200010005054281c00031b5107480342c91440c4c0880c030b041c0100395004100c204400078524900003036200c0010f04016040718492503c620001c0e080e800c1e20010030186214004050070403a224214012000d0740585a140007040d48103800c0b1100c0d071001c07014012500ca2103514141241c40d610040d4480c65001c409030550607403915006040340c050340e116600f0010240001e00040ea41c000702e9002c2040190355960258008120b840301410f4284814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106213857 1250 106212607 106212611
    0x30c0d06050a0608041b140f18013512090a03050102032404090309030314040815040203010518120d0e03130801050108010204061e0c2306010509070f0c15 68
    0x1880701d801180640c0aa41b040c1d0b10607264900100807a034400304a48103500008005000340030f0107042480c0d0b403101d501c0c40941469043c400718201c2c010140c41c2a07202000c118410a2060444802d010700089a031480550301c4e404102d94281003a9114424204514040c0000032007000c80c3e550768404c40c0c01103902034004c1d9168584055580825170042c51240c4600051400300d1a2500c3c091040500307117a8075440700400142103444c00c0b12030003400366201800140030040404c50001c1080040107004000c0c210384414a4140f06040c252180038188071018455415038046030702003c200d082c01d444540038043d840e0086c0200e400040e10800e0640c01c0e9038000010a00c810b210041d110505440d00c920080c483da0343c0c1c032135416080780306520800300000d080c00c5550144259000d41c80c08691081d180111448020f615250027001890b110204800e0300d02140c0d0b00e40341c106001c560300506080f5041c81142c601002c2c0906443d8003c0007a070200710700d240b41e0608000035a14844a0b0003808902 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106215107 1250 106213857 106213859
    0x151503030e0103020a0815180a060f06050408030304060f1d0105090f0a051506010201060e0f04020a060801150c022e030c03060609060c140d170f04032c0603070804121103030c0d06050a 81
    0x2800002b030400380290032090b5443c1c10041001c6000f00102c1d000c544042d801549559620741351140200f4443c07103d44015034442c80c110b20800c15150284041d030f0810030001074103003010a0407916000c5094040720042d0040e03240a030120303502040c00180c1410076400d0000d541c1c0d0703420040303004154175041a401204080140012421541c00b1248a240709490020001b602c4481c2030700c02c90401d11940d2100940d0340d88140040340f05145180c0e40900c017502101e0b220350a0b8000e1a0a84540a40401a42c5c1c1401b01c9030101503041c0075803a06c04480d400d04101d11820090f005041c03a1190094504bc44028141b20301000302d0b0480703a04520b070301d460503201c061031082c00c010034030450342c07100c40340d41c0b513020000c1660007004d0709010340601e51540b60500703040d00340055002c0204c1003040e4080703007001407000003a45445903001184200229501c0103040d241610f03041d040400001d032400100045044e40001b4000000202c03a040080303181311a444240402520000c1c1100e9044560050607400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106216357 1250 106215107 106215121
    0x60423070e0601020f0a0c1401050d020703030207020112020f0f031f14121f0e100908120a0c080606030a090f050114090d0c03030504151503030e0103020a081518 71
    0x19424003030b12090303017a16103071031240b11802d59407580c00101401840034600100100629100110b101c6081070401c0360401c81440524000ca0b000090b007035000c280c001441300215030f8049007107151158401011424024444c800c8c9446011f002c41a10b801040000410301200c5038603170350801c009040440c04050b41d282c00e10304240c8542024881d004084070080b1300c110400104180c0e41200041036260654800d20903508064078428851401c14001c031036031040310f25028007800b600c00740a005510341e1754031351001c2e044040100801200c004c516092110b064a0343c03000c00d1580060084500f5610790b00c4000842000b031041001c02090070301d0580f070303a604110040d004000c081e605030195900c0e55444082158441d2031500c0c2080c00200c030200103a0000c3d02a0b80040d0b0042c0c0645c003003065600c0642823040c01c444201140c0750400e906814100105a8480c0c000781d03a10000780703015410b01e41c0132a07010b01040d401801030b40403c8124420462181ca9540c008040d14200075400c03c11420444 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106217607 1250 106216357 106216379
    0xb0f09040f0b01030f060e19090b0903070c05040c0f030906290405060102060402060403080a140a030e060a1503061e050c040f06170a18080c0304060e090906042307 72
    0x1482d4180440d007807144285d5040d86910404048840d032094807031b8240d40c0c1010301c101c030001110504c100c0580d200301c0f141c04100515161032042012000641d5510400d003084035000805900844c8203600704032501a00c141e010b00c3c90b6003d0421828041840c1e5454504000070300038142d0301581c0404202608903a218109040402000060302c0800039501e0380350049803103001c00ca50203500700804110400c0041c00e0b00c07000b0b0030301e9421132030810000c02d540380310f5100c2039000c0c400c294002a03d0300c6245049403028804240c204103848010014482c00031740341c0c1d8250440b44800f82c040d6a50350100f01c04240b66050000181c4550300e410010f610305601c01440c150818003d43c8501100c600c004503102d40500c104003520b9403600d4004a8596481c2041c2c409080c0140145420504841d404000242410080c6c0b13800f02203800556113580c203016004040012640d860351003034406070140203c075800811070540140d04100d10380c0406c4201860404003a22078690030b5a18454040e000a84031103003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106218857 1250 106217607 106217621
    0x30903050d0215060f0918030904060b0904051e0606090307090203040b041a01062c0a060201020c0d030912030e070e090d0305070203030f18120d02030907120803010b0f09040f 77
    0x20008007440c2c1c6510b01440320020460010ba90088058000329a50342401d69010900340301d00c008892800e11480085002cbe568603500c510403a0f400850808194a480d000d145e500100301e01081f2a0200450a03910310240c01904483c0650400292500d05032000d2108401400704e442082d03550307040901e4402c500c008101c03419a10510f01800708034444417a100c1950413110241d03110500310f80601e0340c405403040b0b040f420700e10140d071030028034100b034403001112401000d040d000180ca810003e011581000c100740b500324201b600d0410402c0000e04a083c8100f18403150389400152000c00291b00e500d0aa1035070041d808945008041010100000800d0300300d4500c142d07003d110303544424030180c0e0b40e07000035034612001040800000b402c120034800d10130308a51004046554040380408030280a40c409218441c4180d0000304001310303500f0400c0194000c01c2c180c00010410402038035240140c0c00180588609a82e0008007020400710440c02d45069003001441002020700d0149554000c003e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106220107 1250 106218857 106218883
    0x1e070606081906021b0a0b040302010c032307020312010b090102070b090607060f0b1201020315010503070c060203060303091c03030609060b090d05030d060807060e030303010b090904030903050d02 86
    0x409601007103640011448040910390030b44a00240c079190342e2844041d4215210341c0b149030340304040c0d60229403c01c00031103061500940c2a40ca8600780344c20000d0035213130302c0144c000c01c1c503061049200f0400f40144480d00c0110110348013018584802d082241103128006480504207416400071603d580d10b28014820748200b40c00b00c5d0a110356580d8040454042c010031903074010030501440000c02e01d250130040c030000958900042c8140b0a00c0042e030104200644a204c6030b41c08010001000403015108550240908005003140f03021407000704038000481d00100002d40200101b10303642c03400c00540300c442c1002040c022035071107080c1e84004141c001540980020f4140800064602c42900c500c1c420b1342c00c0c030039481d460700c100202031203000031748030608407028481080960400b0307041f0b208500107481841c01400500e1f140403801024884007204151007030b00100010030100c0040002c541c2c1082046d1146512944d580c102a218808154005400d034001c4c5018030300c40300c0d804a0000080c4003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106221357 1250 106220107 106220111
    0x25052206060905010815190b0705010b030303091903090305370312020c070302060d05040b090105070909111308030a09080c060a0e06190804030809030306090c030a021e0706 76
    0x10341c80504407005800c40c0b18103070101d09024045603001110f60329200718410090f01141c03800d0710b2001001d00c215030550101ca040d00001c44e0b0101000428042d01243c00c804038010344c11411b05c0d1560940f113030f082c840c2c0c0f810303031981c2d141902042600907000f0400540e08a02951080017100c55202540311001c240324040300520200d421035000100a490310968055407017805500c070f000e10b000d000b58001d00c00501c680c0f0800340c002006a44d00c100501c40c2080482020442e81406c1c40c1100714200050b02d403c10990500f01001400f5a002410004075000361101017561290079a01505510902008001d40303002d03a200885c01401c00001403800d01c1d41642e40c0b600e8141e90b1540e56071180110f00700c00b035000d0f030200190180c440c8641c402c503800c030340004c004906d00314a151010001b105e00c84460808948034008000502d41c208203511703841940c3c031002d5455441c080b030000c0c06080d4001c000108071b00001c03020a070400142c2c0e059404800c0310940484807000c50060b50310468103c00c40441e2028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106222607 1250 106221357 106221359
    0x201030609050403020a060c09050d0f14030a0804080f19030504020901081609020d0216030918060b09090910060e09250603050702030904020406050a090807060225052206 75
    0x821403041a03ca540c055024200800e00740c0e5a085c0a008411042000c00407440b0001c1225540d040d403a500d440e1240784a210400c94503c1c140c25244403502030040700d03400501c540d5560a41003c5050340c05a0b0001d0b01c10f5442d49460507100c00c0c1e004468000e65865132a4048034040ea030941d004501442c0212880740c941e83e40c1303803145980c8614480e11000410800d0300200301105e0160042c0600131070140b0003605154180b44035008032080040183c0c000ba01c2c501c0c1c10010070810444403402c41807490003d000c601d060401c101d0951052114050040030f901c0001036640d2002d100d1540c070844541d1052114070f5441c010180050000d580980c910301130760391004003082c1003407504c083c4440700410104506151980503801807000401c0b40040d0b0004000b49101592184002e00140019460344c0c0d80310500e0420050400303c031070b04415160f9120354020f00506800180f0103082072014101507481c0340301419421940c070f030705600158100c108004041078000460030304404003030b22014100005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106223857 1250 106222607 106222619
    0x7080c010f061404150e1e010608060d080702030a0b1602060c130302280603060915050616060e01020403051e03030f16180905100e0415050402030a050d080402010306 73
    0x4500611500c01c1401d4054a40c280c2821306402941d2903101c0000413107001c99840014000c80311089909950f861009854000c1c65200c5100300c5014109074034000c1c050b46024004969040e109210281c207110010070380e0740866074200150342030113034071040300300c514144000c0120005020f140c9010247c050080090440c00c8600181d40802c94041c40440460b0b24580a100c040c810f82441418440c41d8a01d0800414401d2072031900240555540013400b94503000b8032400300c07003841c0304a00307008240f80c5d800c2090b95162010380f540d1040c5882c0810070b01ca1145000c000070140c1103041c141c1540081000003d200c0c1c01314841030074240300c4101038280c087c0d0403200c6171a0300c0304403502c04003a400c00300403605041d00c01329944920285410300910f98090503428441129095011021040c1c54404003c880b100024000008060507452892036090541d1260161203508140a10659881e4001000c1d5602000744080568029040c0e035001d140395034000700000f404503404c0c0d0100341040400140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106225107 1250 106223857 106223861
    0x602100504080301030f2618010e1e04090c090209100512010b0a0e03010e06010f2312010204050d050303041e03050919171516091a0f07080c010f 64
    0xc5198002400ba1030343c0c0c02d5640b540e071540c05806080d81c03508482144564405118002d42200e94000140c039034451200c0002d04144422181c1142e040140c1101c07050203649418484802032004000940b07200340340800858014082200d0282068480200010718001c0d181d00402040d00245e48104a5681e500d6042c2e58501c039080e0841102c1d0b100c0c0e0010820000d04002800c240303070003031a1820301c07000040006429543c000c500542c06410840042250100445282c80285418002401d010300754620b07070554003466641c054021141241182c00d600303000c5d811140a0b000041c03100c0300d045000d041440d40d036042142d003210060009114240098550806207400e5a4103561340c031700e851803c00600440c070a0302141c03038519540087d004500040070040b15892000c00c04011b14054001c02207060002c003000e48081c1c001501800a03076803440c0e0140b04402518102a11201079074001290b01442d84a1010f030300d09183c9000c901c1c1c404001c0c0c10310003041c244941038020300c14110342440240c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106226357 1250 106225107 106225111
    0x61b010b041506050f0d0f020913051014030f0a0c0602061311012303011508130c03020108070504031b0617060907031d010207051c090b0a03020705030d0e030406021005 74
    0x5059000b412040112a21030320003811140f00043d00e5a0030919411448019504800c1c1d29182040d004607400045e403c242a80000d01c22080c4010b000b18180030000c42440102c5000c0c3c0d240702c481102c01c400c038503141004914007507400070b400c031140e181071800c1c03210100341d0600821006008a00105900a4a44080c002400e8000d0300c0c0b48101015900113540c03010706800c10104d03030762141600c2c0d031100140c00061402842c800c15021142144900014060b0000034000081d4103009544400420031204000c0241c079820308080381141c07100340060710140a50b0340000e05803010070000c02c05001d81400b84100300e880680312440e55484854170710711000d01c116056600304c0861030020307c58030b01c65000310100451040101d1040b40d03540040310b0aa9101c440150785941c082c00b96000501900001824170703140ca8a04442c505080070800c860500c0f030400c5900406401040d8401844418421107203510352645e010044a4525105103480307030003d01c00c0c4400341c010710ba0420ba603122280900b41c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106227607 1250 106226357 106226381
    0x30412020a031d120a03031a06040e011412012301081c081e040515060919020a031404150c0905060412110a0909110f030c0909010b061b010b04 63
    0x100d00415640740d40c1c1d0028203d281c1e561010280c80d01118010781801703100c410a00035a008180d084000d5a0f12084860002206000300820401040342c8240c920041c1e05440041030401c000c1c1c418080000c45102c0074941801c6d03d546400c035221304049007005040390710100403034003607203680e0390b0031030261510b4000303801c080c10344094040000c0952080188650042d191040f03480c00c0d1380c03500407072804c0c0c250459045540d039124038070407100440f01800c00c1d5072001040f1401d1040c2e1402110195080042882043c107564000c00c0e00ea502c14001d8011440c0d5800501e0002850b1800d0b08000001c48201d0000c0b6504a281006800109220b20204000c1e14005004285011703e0082c1014840c0300d03c0c641640c2c8001c0c1ca12411515030f58000c0030700e008006182011407440b00f03038208401f0f035410141c2d209200d1025102541d84540300840c0700070064000304c0c0e844801c2d40c3c40409903809400150107990340064001040c0640c518407109594491341d01500070440c0c116040d00b44011210300381011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106228857 1250 106227607 106227617
    0xa1109030a0b060a080307151104031a07120507020a02090a0e07181d030d240603020304060902030d050a0207140d120201020904090f02010305060a0f0b0a0504030512030412020a03 79
    0x4a00407808000c2d442d030b08104058110940503944071411415070b004008102e0322408910484410b54105004003015a0b94505503280350910315614020000440184980301b1812907001403049c43c006d100340d24030710754008018030080c40c1c850070094480c002004228070440aa001240045c2d8082c070420f551141980000c2040340e090650f2001d080b00310340d000c482030a0300ca4031529a030304402080b500c01422005d00850303e40c0c408000038010f80f07801d040052001585850190780505d50a4650f20482c1c1d01400c00607501d88980c10000043d0410a802030f4242c03050040e4090455445401009200c40d50390a5802407620382880303002806081c00c00540c022502c130302802c040fa85030444100c0c03041c0390307000051070710035a0f0340440c0c103a50100c0000e48400012404910035560140a42c0d81e1105081301c0080300c090400002070114189806a125903c00104a48088600640803100915003110440c1c6903090701c1410219981d00842e0111403004d2085c110840f2079000044c1c0c4480c45515840f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106230107 1250 106228857 106228873
    0x50a06050c19111c02030307111302070308060607030c05160f051f08180d0c12020c090a18170d0c09030f02040b0409080309070602060108070b0403060b01050708040e0a110903 77
    0x4c10000c0030b007601e032000040c00180304000042c0c0d4100000d040082c4240700b901c3c40714a28104000e06c0605076216003c10900410280d80060307408510b07182e11401c12104561104c0700c40c1001c8a88172407101c070041640c440d0920b10104c10700384540c0c86007140c108040c2c0305440742d2a01d003440040b248800d40c1241041040c0310f00c20f0840c0c020b0048540c031451035a00812201c07040740101e441c0c610070340b40c61400f285070380d07035042e0130701c1844003966980e0034050000344102001040891001c00380208120442035650007114801d41c220390785000c1843c1c105810b40300242e000c0043c1c02050340200244810f0030720f0203040c4508640a40c0d08407080702c5d04001038032414005c0d5024040074014094601c0d070b1241d920300202c8001103070700c809075000e81c3c41d8400800700141002c0019190010680002900e648081d000f0000c02101c4012101a29800040071544803c05001039406009011000303101180c0850701040b000c4800204500c10042c074201845403110110007281e00d07208803a5020b8050300704e240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106231357 1250 106230107 106230109
    0x200405010507060207020d0c06030f05070c0f020f04110f03010f05040603080a1202130902071401110409020c011401060c0b070f0804080c0a02040c050904140106020706080a06050a06050c1911 84
    0x4003030b00345c441c006803101d42c0010135651120400c00e5650003400c0030030760307500c0410540802131080300d520400314101222800c1da5500d51042070105100c000384a4010380c918007085484d01d4201050904640000c59115000a6a0041d55030003d008504401561a10010310342c50280075500459070001d4645242c81e144103030881e2241c60360340030420309a400700011b00e009111a8154002020100300050325038a40e441c05840900d184011310090b60b05040129200d050300c40100c50840719030040060b41d03801c410442d54090800403811220000d00c18000040f07060708840903056192003032404107001e0362440ca054881c1b021748031528000071180300001d030010b4a910014064107086000700c586400440d800101600d51032003038800041e0300440c1d0b0480b00d0400340104c240748400c40303200c20b903698107050b0025950355035445218200481d030800302d00441420f50014020b0000038145a20311074170b40402410720790210807022460710955000e005800701051010000c141e204507a8002c40800c1c1d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106232607 1250 106231357 106231361
    0x10e040f0b0c030a050a1104060f0e09360a0807020f0d061b08092d0f03040f05040e120c160e0406050c120610090306090620040501050706 61
    0x108211100140204818041480c125009200c2c0c090401507a42d0f921308401a0420707180301400554509041c80025014078905c0d0040e00c042d140c280ca08400d03a541002000c54807004a1000030341c2044400040c41400305169055410803c5294000703003035042e0014001e500044411180f20300c3c1e40000b00640b002940d54401010394034001003150182e05040c1c000030b5407059200c00202d842c50398481031444c82d20042e0303402030b100c0441820188c8a03850030032686074131161020020504441d00c888007000402c02c3c1d810075040d110660040740d04488003490001d5699010b4010103003020340e010340011741490107010381040e448034400580700b050250200ca8038907410078514160359000328411900c50710440c0011500070055071210404500b41800d00d00125100074141d90700118003040484c02108031142095001001601c1c50414072005e000e080780e00b82c1258000410b601d01b459a000300380011070b00280c039140c10032400400301e0350310b10944110074400c91040c28041181404200d02040c171a0b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106233857 1250 106232607 106232611
    0x81c030e0303070305070e01020d170c120106030f060509190522030302070b060604061403040201020a060e060411030c03070308130317190c0b040209070c0507230306070503010e 78
    0x904020550092a400003425a0401c640350400a90744004201c8000c0e8000307001d00003000203002810265442c3c00780100811188080030b224900007002060451249004031520000a00700103401c0f96100d20000307001e00084d040d4144030b02c1c03c3c68001b1441c1d150030f68030b15000c1c500010100000c0d10510132420040c000040410010340810b1014140c40d0751803024198500740709035401070351030903a0b00e051807030954042c040c64001c44040c4401c0c031540d50001c1c5540034440c0f41a207001e0312a130311071004074900a8484402030400341005000d688100c00000d0312030045110300240c03420308250070145a504c02c1010311130303030f0b00d40d02981d404c00105104400504144400135405c07248143c0300d846011116a641a0441e4029800640c40d020800d0300c684100d911103051502c41c003074100035151001c01c05170150010f4855065540800d060342c1c001c8480f0032001d41c0c00070039560402c3d42d40a004000a0403583c0c041c07200024502c450069240119005110302995203446081d83d003082c445003022140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106235107 1250 106233857 106233913
    0x3030c07031d040e0709061508041401110a030911010e090a0e0c03030310080708010b03030f0c0102090918100e030a0f09080304180e01090201120515040203011203031508 75
    0x100019901150f00c440c010f024448241600030100c0300c0c603180d4800b044070059400706840084180c034525460340e22180064100e90007460700103451000d03402407801081414010b007042c00740010b82540e502c1e010342014043c0c4d406003080900840b41c1a0040d14120051101746620409410000c0c000301c03080e90203d900d4007031143c1184c1c030384810030000c00d00d5176009403000c410301d18240c041040900800c02c5203602901d0410000d02c4840420305c0400c0e5280100c2c4080c1240100c040b4907030142581c254191203000c6002013191403641001c407908041600205c1000280c0e0103003211480c680303603450290760224211003000398030b014540002101d01044628000082203503002e80003604540803c041c001a1101c0c24500082d9601145242c00b12000c04100380241c0e410320241d500584c1e0000070315440f44014660108560351418040d42802c410820f52550140c030100c0003040140400d88140d44a52107910200030940680000c00d1204005114004565019514102d0750701c10880016000c148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106236357 1250 106235107 106235147
    0x40b030102070c09020c12030108010912020f0601050904060e0a030905030d0306030c09050c04081c030c090617060310090f1a10181401030b0709091a04021602030102040b070c0803030c0703 83
    0x444900700c7c800342e03100f030344152030300da45854001c03040c000041501441d814580c001850901520750540d13455603014462a48204d510034005010303ca843e401515503100b022003507d4038a916854050940c42641c05a64024480d0504028204d8001c0c8940016281c0201d040006180740c0340010b00a00710003003c044c0f24002c14000047c0f052402c10006d4400240c900c94440b6903910068002c04950380c00c00341600b0444074400422106070400310080800d441945844000d03501c07100420f150501004218a11501d0034003040280010380d001036a0041c0b00b0190341811600c459000751103004150b41d14005030458800c100980d0b00c0c50300c2103c031040c885040c042800c1d0038480d04080e1200003680306031000541c079820041e0140c1c3c4009030300090442000d081100f9640140e0003100044541c1c803030780c09a40d00003680050013411115002d2072560081c0250344c0c0300e454079030130382c002d070894481164280700420000c00d01c0f042c080141e0380b0800140e80c035203003080e445440441d2079880120094607034007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106237607 1250 106236357 106236373
    0x31602120322031505060f010c11090a020a0806192106060e09150c090d03021f020a021e0604060b01120c200109020a1a0d1406040b030102070c09020c 66
    0xa010050403007511100c120741007240503e50b08103079405500100141d14018513100c00c000361641d9201010110701d6081c82c1950b000009890441c03125450442115400030a40042240d802c0c120340081014020564980c151911400240b200110745050070b41400c8207049000c1c030003e0307013290500c501d000448001d180412943e0301c1c0c01c01160303250b1304958a062454030800c501a9810020380400c9500728428103103d10b4011101c020502130000c00c148550019101001031504c200803210403d1030001e03100802c0c260f0181048004c1d8020f4117401d02601810013410101c400d503400d0081410504005000b4a669540e60350f4010300c0d000007840d062008282411070389144c6841111200795181d1680351110000c41000e0b4034101800050b800a0303810250080010384940010360116422100800e002940c4120742e1103960061548001c400b43ca840070540e100c5840c0507035180213410558003000b5540c880002c0c5400c5c2d111345400a0038a13071042c101080100f20990090204104c4e1005903107002d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106238857 1250 106237607 106237627
    0x70b0301030c03030f170f09071d01050f09012301050706020c0f0105011a04030f050111070308221a07030b1c021305220f0b011203030c020316021203 66
    0x15410070303003069400b001803030720900030035400842140511002d8102015a02011032a5011000004010402841e40032000c00c040c814200b00d924007030104800c00340ba60700125810072003c201c01b4403e00d403146500210041030741c189414150305030b61084003c0c01d5440251552080c1c620850703103440c0d0401c0010400c010108020384003801c21515580041c1070001908084c590035504180c00c10080038006440302e601c07402e052821241120381c00304c03203010440140e0500034014050b010a4600c07103a8000f5004d010140c0c00703601107105441900c114003d00c0b281c00042800700f08400402400e42d456003a40d580701d242d041e0340c0d460348110315103408200100640c002c1f6081c0b940b0300c0700341c86000c1d800484a4086143c4a00c03d4100e0046510007000b45e0b180441d0050031004e0010081003a80206045400600c01954001c203070b92608403080902342d5070759515009807601440e500341d0001c3d140403055aa2284040100c6003a0090110301d8600c001c2c0c10303020001901d40c13006880340d41d44000c001143d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106240107 1250 106238857 106238879
    0x2060c160b0103030203070b010902040b121b0f0c0d0c03080601031d0d030b0406050d2406030b010b03090d02062701090b072003030709090b040b03060103051e070b0a0f0207 76
    0x1e180301740d02840d110319142c904406600d0040e013240e42042d0051000344004007215060764101840c41c21000001d455120b5600300c800c00381e80954443c007c0c0020158020341814000302400905d540449240c44100001220040f01800c401030010781c0d8180420785940c400d8121442100c0d4555403c0c40b54814031405a00c1c1c490300d201410086a2034a0f00d440321841d01e8416000248001d40c1c1c10958690182d13074010100c20810540d8080000c0c1c00001c80030140d01b07504c44006180e100d68903500550712030090385110b0308210f9900107148070b1001d08040c101c1c40170034071034064051a002c8040f00c02e0411000d40e0f02c4e22203038109102541d602d0307411201149082517680d0141d08141c039803c00d210704035100c1140c2400c1404440400b903000300240002c0c030398003015900c201d4030070803800034000c0180f0000402410402c8051549480b80d800040140100030600c18060038902004440490b40030625603100e81c0207101d0b60110361002d20954421602411051504000303901c140c0e6a065242d0810b940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106241357 1250 106240107 106240109
    0x1413021c0c060e0d0206030106030216080703050405040c0e03150c09130b0a08061501030221040c0509090705150304030e0a03050303011806080303070309030e0a0905190203060102060c160b01 84
    0x108071520080800629400800380308250009035031442d00041a0340102d4038920061017020209a40000c2030005401002404540d0070b40c41240c17903543e10b0302400e004040350004e005103072003240360440d4a0000341c00345071940781c0210050042c0081404004290360403980080c070042d655181000440e1499503840b040c1444881c8c80000007440d154420103100c0c00c4005600205890b41c80b08003480301d66a10060b1411080c1c03000d00c0d025a58030410b41106221209000700f24021000321400c0c0010032840201980540704240c43c01701d65581e64103040e0707a540a070391241d0358000d403011400d01104501100150b900500904088070001c1c290310216070600b506a00c140e44079000440144200710400c1c02c40d05400452440510007141010400d540b01c1c407000d00040180750361a04000201405146880e42ea41001044c4143d02d50340c43c3d08003006040229039507405004124a100f00c0014a442501e0048a06034010682a07640d0540c610483d030262045404105008048000290a4540c07480c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106242607 1250 106241357 106241363
    0x506280905121b010c050312070c140607020f1209060d0e03030c030406110a0e010f110106060f110d05120c0705010f020a0318051207060e0609010b131413021c 70
    0x880801ca6074101c3d4001043d6142e0b074907040060300b1464401040000080d40d600000c0700c265451036403140b05040c0c0c2d49200e81c4100401220034110003542848021a81074803c018075000d0340c221801c01c070803231525a0400c0290842500301404030043c0f6042040240c1103c4400d0703e000030342c031003802925038074540040b0380e0b581c0c444400100b00410044a801102c0103e0a0090401d08010a02c00060040310541003a00d040203018a02c1001d1244501c2001413620083c000070428036031910130090584021513168404204418004400c080300003a00c12055a1540d0710f903400c0c100100c6203015100e4000d840d0303002485040c0076203008140280708100441102c04c1c0c1c0140c1c0c803000707200080e0581d202c5400c2101d010821080b00320104070b010400310301050b040200765540c0c20352450101c00505094210300581e100e41c80c200080707d00c3c150f001d08540801159a64200c5d0981c01d0308406460301c005030b0015084888003c50904000c9081d8010400d02c001c101025048030b1010070000c0c1c2c80c0350307041a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106243857 1250 106242607 106242613
    0x1091802042c0601080603010b09010806090c01091415071203020a110c090601030f020706091a220f0201030209060715050901090f02090a060b0d021201050628090512 73
    0x40205018003500d00101165850081101000040c0640b80344280242580d050084810000b401070f6000c0d4810504004010941070007942c40d15075243c0d440000301c3c1da00384540320380b000703402c078960007000030030200d404041c5007103010b010100510801540701c400302071014400b485040009403800814040c0c02c0b0311590016250a80d0060040c46141d0b0004a000306401c0090050701d1134980c0308001d07034418020308000c1412041510004024450000054070443c50240004108071983c00703103000d004001d0620400503150300c1800030403080001c0c002000c18050300030380000203040c42c0e41321030070034014100142405501800300b01e49900c1000101e408200c514481c03006d624140c4607507900900500000c00c0341d0ba800750f413040201e6200c0100a4840c03401c1400140904400c0e41003c80a0416440080d469070b00390005c4901940206004d1491200084008591400d01c0c3c015281c5207001c225070030001d03e034030480702e69030300824614036402c00049d40c5000c00c20740c66566226150060b60002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106245107 1250 106243857 106243859
    0x403050a030606030e1c050408070303030501091d1504050304151101061413020c03250308060d0b0601030906140c120c030601210204031212140907060e0109180204 72
    0x1e04403010340d00400281071a01ca661586040d0009101c1d004002c4034002c104600100c00c400e9407e0700aa0344001d1541c428054044109545508214100c07000c1d4401405000318410318034400311380b8014020020382c0038084160080c0070640c19035403c81e010303038140c03481e258035541201d050310032801108010450880495900038800d00c54070b401401410005805003000000192150040c880d5070000c8580100342554081814808c0300c121200102941c0104180f09450750310100c00e0035000c1d03001c2030300c14000450038100040c9900b04958015002881940c401c40158003d01107440c041c2d90050741e50900e001d0303101401d080c00d4040c036005101a42c40303482071408110341c69002807000701000c400744140012a40c229450002a8480b9043c210840d101d207c81c80009014a6102410b450741c0e10030030264040c0c2201f0b2484007030f00040c2051101c030710f8101e4149440381081e203400e00154881038040000501c104101e04005c141450041e0285540c0ea21149545c207007540b80c010f581d580058 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106246357 1250 106245107 106245127
    0xa0b091312080103080f0a0905030a0302010b150901020c010302030c090d11040e150402010f02030c06190e030705060a0c020a0b010e10050a060e0f0d0f0605060915061e04030803040305 81
    0x10030640c001d6114503101e040c0c0d40c1965546251800390b0000e0404a40c2d020800c41e861501071600c00d809001d016044600503c41414000d0190440d0085580250000c07a42010307048001c404460318040c0603001005032907501c2c4011030083d88020900d50100b1030510429006a13540c00031800745901072142032807a144044100012502c110241c4000c580c0500701c0110030502084c0803030b5102c1d409013804c07d1003802c0500e046c3d00b03520813188030081e1406400100201e00e8001c2c1e8437400c4a0b2001c410410030b040696000b02d03a00d1149800c0680584e025400003541e20050350021929842d03148141c2c3d906100b01d686003402c5010a030032413454031032090b040050081c48031100200905040390034840507031900101030440303402d00c0a5540945260942c4c01400d4a50088a40c00542c1c03000ca04001c410765410702c0c40003418103581462159450740082003030304901100c50119490000d090510f0908050240c903040c030541d00315040b50070424000007010480b8200a5803041e03000783c80b003550312603480c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106247607 1250 106246357 106246373
    0xe06060102011401150507140706020c0907020a06090503040f0306020903011b094b06020c0f09090a050d09031205030c030f1302100906081e0403080a0b0913 69
    0xa001504580c5041442012941c070719801c80c0c110381030102007192a012080d0102c45500c1040d8018003024400303480c0450395a00001c03c04115100b035802c1d207002000e004200310058609a814100503408050f8480200c0c005038040c0c40780f10f101c2e40c00c513460160380d841c0c009068150f03a40242d03259076020990030703810b040038010303000003000d0200100c424541290029020341001e028680d81d040f10141c03010195144078200d2500f9104a181c145071124201c1d4124404005010320928070011290002460500024070030b0a6030a00800019240c0402418440e0b06c0b138000705140101d200b0713144003002155003800440807890107a92900061400c504045e0f005505619540c02044000c2042107040319840d801d80303401414450401c0e200d0340703e81802c4007d42004110103035014440c034500c0c2e40c2c00c03030304034600400310f407000d40311010165900340540f50007004a03900f61401040c80c0e80058006485207030791a80c0035039001c1c0c000402c10308440110720820b408440c0075808035405801001445544 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106248857 1250 106247607 106247611
    0x3e07050114070c030b1515040510020606010906111501091401080c090604020711220b030105090a1b090501090c0306080604120806010c0503070602092805100504180e06 74
    0xd01c0e16162200c1642e61804007940e520015100781110780209006d0075400c0b09000885000034802d003500b00021142c001e20354410302c18188038500f601d02d00c811590020a12511a040c16114244854505071081e2100c2c2c059081c46281800780b000f076280b005030464402c501030300000c80005164150380c079241c066000180c0008a00360300c05a010402e075078800c082d0944c019000c0e1005031712400e5074540a0302000000e01c840303510100d41c45002c44402c101c40620883c442c880d00080c00b0094040b801c0c103080b15815611406585c00168181001c2018240030103006001c0f82d080071442e6035908541c0c01121000e03042510300381c1e110308030b82403403540c10b00550014005d544043c00603400d01e59540841c80c1c01c0d404090081c81012800500c85030f0250080e03601464101003a80d5449106242c124000e501c001d0070180309280541407080c00c45085c00c42203160024031408564118117100800c1400e4a21b2981c0b1000c1050400010078540c0d4020010b568103056002c02007210768080b61050305103540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106250107 1250 106248857 106248887
    0x603070e011a1b01020319180c0506030c040e0103080c0c0609090f04150e0606040c050a0203070b06210606130b1e1305010e011d04033e070501 63
    0x2100c014408994000c0d150389031500b070804026903840c41c900050300009049001000c0795403011007000b030400e1100b08a1552400b840900300b01d100e40040b0482d0500b040540c001e8001c8a031070100b84001d05103c1c00442c2c01441c41003103641000e907103450620300040240c20450ba50744001c075160000ca00e04214414006004a94003401d04c031010011420002c401024982030341051030108003070000f218001c40e241b1211880031b0151000c040742a40e81c1e01d0f8184c078018011440c140442c00107a11820030b503554008140d000e149016a15200c0c2141c004000e0540390f48016900d0700364001421846403000040580000303000f00703140010800c04200302d54455411514100241002540c0e1800c00002d81c403019a14080005500c201c041544113402c10400205e40d4a000000701c0d0101c014020796048411691a880540d000e040642030302c02030955005010580381d47da14a01d55102000b11404a11102070f1500351846103840e400f0b5240280d5004074042c1c000040c180140d5920074030340389074a15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106251357 1250 106250107 106250129
    0x1b020708120f0a03021804060b2212141504030305160206100501111222060c0b1b07061103070e0d0b0403050703140307021506041406012102030906060307 68
    0x5003441401d4601e03c604142a002c040d8006081d088031300e11418480c030248406013042010f076480344000300166015042c0d012500c0302060028008540c00004002510000c06241c0311030010b5030345201030f0924089000c2140c1c00b6006055040404642603944160f0007903501150750b04119404002d03559400783c080c021500074008010607003440c0074030f22003111740030300e000c00c441601c803036010781040f550031101c00060200080d010f540e803498011031664040000384030907039180d95010954038200501c00040c05000c0200008220311082c0c1c0300c0001c3c0c010125091484d240c440c0da078507030484a000c0c0c0740000d40c61000c418041c0c0c0382e41c06102c0000d03194040c0e44076192410b07036131128003034050020302c0101001030024070700042502c9859440c05402042001e03645a04054401030344415414103c40c107001e9640d40007503a280f62034007414080b8840003c0441e826103443c401191400d0030b54005650910b8182d00d44040380c00700e80300035031050815201521341410486e003050b091032035a50180e0308261f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106252607 1250 106251357 106251367
    0x90b0306010303140405030102180f1804080702010509060a0c0c080c0127030203070801050a180807020d03050f070b0402030d0c080d020901090f0303020102092d06030a1b02070812 79
    0x1490004205054030340508080d000b00c403041d8500d403254802d94110980550012500300b014031980030035031403045c40498901d40254018414040903d0444005056420824002c1004522404014140603006152141c131781204103002c5007a81d401061117000141d04459500c00380594180794901510b4030201074020000503000080003034804207a441e0621222020380081c00300c40c61401401140c0c00f41c00c1c0d4804030f94903032107a4000c2104981e86941941420003030312480341000203820215601c100694100b40464090101142c04103400b00e00388001080054207024046c0c02411041d40725010100329031402d803051500303082c800c0d115241480460a07903500003504400030f50b120041c00110041c1c5076001c00c40100c42c24116a840342804080400c004414550706400501c4010020f4076140702100c0082c040e10728100240160100072082d801100702c20380ba22800860b001509801d010640700c00d02141d440164090382c06a80140e03028640420a0714014000a092190b200020900300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106253857 1250 106252607 106252609
    0x30227040f0605060904020c010603050d020f0f0a2a0308041502070b090102071e120b060102010c0e01080105150c0616020d030612080d0e0709060501090e0405070303050c03121906090b 81
    0x1303801000d03201486660080b43c0104a44000d6204000454000c02100c10581450a01a450b50000c2c400203089001d010380003201c1400008442c400c65510041d40d811482c5c00e05001c2036828140000e41c010a000e2070b0300080800d01101c0584040d25082c4020803c48840c0c040103840c003070b0340da4040b880c03004040c0b20014051380c010481d68121100c540d050403052007841c0c9050002c1c0d085802080e50314442c00c001c5030078000f83c1c400c2503108800a0f0000c1000700800981681ea07e55001241c500213850310300103001c1ca0030b240c4013a444100c10103030f51500b05201c0716801e6092000403160085403400d01c05c815061a541005503007104a0305040130440c4a00740100c010785a148500083c1003035400282070007420b07003076070700942d0700c484160196140346451703e01100141030f82e07114a03070000c0d6007400e0114590002c1e01c441405203074440001c0c1416440d6940941e0f07942c100310051069404180080b0007240c8890a025201e516445d5070702c04256141d250b400d0443d180f54000001044c0341081d4600707a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106255107 1250 106253857 106253869
    0xf0c180509040605061203070309210b01091107020a030b040209010609180207140d0305011401090b03060409060b0a03030c02130623130c0503010f06031806020a030227040f0605 78
    0x4190040c1d00483c040da141c0c0701048166492840340301c00381c480003680d88140b41c0d100b2032500c1076412f140110050000c043e17001c0300c1d03405120403019102c000807070300401007210180c2c0440301e912480c20055041a0301c603000035580701134540c4140c5811002404103c11403030401720142c0036001a007496031581e0304200e409001782c070200600d0100c1d613500140620600c0b05040100c103484a54800312044450b1340c0400a000d4442031103a51a8507004801100d45507006145c9803003611308546042d421640c900c9d080002420b101141500d01507950020340c00240c032800c074114040c6009403030741c80e150b40042c0b05201d025030b0f510f030903103140341d2811405204e0000c0b2051149240d03d09100e20641d41c801500006407225050709071b003016203103400c0c6000100d075005406941201c0440b106181419940c800540a43d1a09002000798880300d541140024004c0e9001d0408a0780b180750050a103850170301100e0596515403903403081003c4015054a03a4a0540201182c55084010034486289042c0c0423881c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106256357 1250 106255107 106255111
    0x6060e09120702030102040902040816060509061204080702091008070605041a0a12020c0708011a011e0306081504050f150a0f1107111201060311120c040f0c180509 72
    0x1c0d05480041c9074010740d0f4007501070398003500c003210b01103641c0d507034881d40a540c03400c0414107408101039030600022035500941c00c0c1c1d0500d8501a04851800200710281c02c04004018000c48881101348080005610741c00b56040c842e140500803021200d0400c41428078103d099403043c82001400c100c00d00010b6440448011500000c1100d01e8440700f0f1048107845202881d24408400340c401718503005203560010750074080f02d000c50000c00c00e00c8010b4943c1c1840801c26048a8041000913502e10210501068040240c028a00c1d0000b056516030054606001c00c1145541a00002400780302c14071005024450140e0a1080100343c8000e05550001c001c5100411f418109642c5410f55200508581c000c1c503071855418401c0c1d9680e108501d00303076910408a4498a02414a00400c003e44840501c501400c1ea0380042c060019a582c070b0040020010314020702c01500d008020207820140c840d030203195040c041ca0540421000004d0500601c4d582101c040c4003240303030402104020341c0d194001690b07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106257607 1250 106256357 106256383
    0x2070e01300f06060510030b030705060705190b071e020616090b120a050c0304050a060b1c0302060613142202031204030c05101d0f030f0a06060e09 65
    0x10140062812500d01041c0680c001d031007034441d44422410040035500400607240d080301c2c04005d0a4103440d04908850b013050b12150140d0142e00b0070b001601d0a400a40b8516100b0012605a40280e03090880e400034000720441d040098002440706054011401403a00c4c60b01c120402313841d910303c990007036440f800500003c4041810b41a0700c071a16106040080107410381c01d04030765840304c04010003007240500f10348035098503180001003031050301820201d0340500e0b0008002c243d6141d5940b0390f08000c020080190341c1c042c0c14803030200d0030100b202c01c0400303089009402908207490b0070f009000d004046282415601841c2030b00c1c6602490180038900d422070350710600c1c06100c986180b9441003d4902e02c0010798948910000d40180c454010010410380b48940d109a01d0aa40c6000744443c01903059124404240034003540c035052a0040811008004000c1080c01168421004242403c000d49601c0d0b5103900000e60180610015000e410018041301c0108881c81ca0034000b296168070001c0e0100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106258857 1250 106257607 106257659
    0x2060703140f0a080907051c0305030a02190522050d17041a13091802060306030a150f0b0f01020c060309070b0a0f11010c050405060a1106070305040302070e01 70
    0x20651038046019a14080440d002c030581e60f80c00c50101501151080700c0c641010b00c070315400401c1c142056807143d80d03030040c85117514030000c40f07a81d819109908001c1001641070340c00d001801801426081300381200541d502c0702655480190301500406031903042c6241c000d0540b4108210f41c2c0c0300e42c0000800d46400601001d0380c0032203114801c11902c1a540089036031081024050b0544890308018007214000c5480d40c001240d448541d0400e541052a80c04281e1501070a000f0140c00c04400840e84603e005007540c90034640c0b591041c005030080580508801d903134002e442c2c1250300354400d030220581c1c00c580c2d00c00d20452201c0000c0d6a0034a00724140e000f0100030000c00c5100384204030040c05040d511040584500705820000c05240101e9100d10002d0002407181d10694010700c100203580c113495540d103250500f8072080c04403551210a110080041605548140903005d119160045860f540e000c03030f560410381002450300c0b401d03411a03980384040c8401005502030070442c428481c55007500c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106260107 1250 106258857 106258877
    0x2121c29010c03030e06090c0108130b070509010c141e070e01051005211902131703130f140102060910090f0f03020703140f03040504180c090f06060c02060703 70
    0x21400785c05000180400d81c07050b142880050600810020174046007030741d1b01c80003a920b200c8a42c4000f041fa010150803502d0b0240401c07545031081303000307040d009418102284121016541c8904031009650131100580015103c081c0b03480500d10548500c800110007403890300d08003c0040e00ca81c1062050510550f2180b20010580340100251a007a850451040602d10b0200700401e500d00401c440902c0707400c00d49244000107a400e072083d42c450090b080d0729042c1d040e08007445128050810701c1c030320420344014000e685442985000c241e000d8094543c1c03628006281008024411031101403150554006a00304410008001100440a10040f102240d101d9850800c1030f0041700c1201d001e407050082c08485401d060300046c0e030f082180d2003a204040c01024050300182c80c2c606140c4121311075001004104050f217456000140c00d404241388216280307242c0c0c0c3d01c00d0035070801ea500c03100c1810b8540ea201d49000340144a80310040c612130814207a440e1842c1c2c00652984a0b5040040c02d000504c90 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106261357 1250 106260107 106260113
    0x30d02070f35030306010f0c20060409060609050f09060d080d0f0207050d021b01090e090c0307060f0f050a0507060507090504020c0109050705191502121c29010c 71
    0x1c180d9004180039040b8030403512080e03000740d16a88121400c9001c90120050b40042da4400c00900542940021401c00710040031100340368001001000d55a0041c4c007803002240542c11403291324010001500c0302441d941c0f50000340302c0000301c4a05e11910076a000820000300e904c43c41da5031103032140d002582942d61410704841000078900c654083c004180b01058000c208840050700074085005030b003c0311840b58206005210919010f103246000421012017000300b032842100440d00f040b0030209650f1406403220119241c11070303581c06100080c802c090b81d07034007140d000b4200e204c17040841d14180d0300e009902900a8000c0c86541c0c4020980b40d80c450025815601c68584003010b080c00400655a8550301d010b014040c04500c002a1070a0140362000143c138a81010078200c10f40c41d000c1c0010000780742c984003441c0440c04484200950203103203426041c01448600071b00320708051080010b05c4242100c3c09600300c5090b050340c400c41c00106e40000040092010013130440d80340034606055001400e00d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106262607 1250 106261357 106261409
    0x30f120a120e01020a0e1f14070203010f0507080f0c120403050a051e030109060e04020d140a0c0906210317070c020409080c0105070f0c02010e0a030f11030d02070f 72
    0xb640920301e95102081030401c65900821036010700d202102d0040003000510002e1a00980c490842804110700409041c50440d5900240110702c0c00203000142c1803148642400980d041110780d040041c07200c10801003180e201000c82030b0031803e8100b41a05101d00401d111030428005000a82071100c003194034404140f0031b008880b148403103023901401c141e6210700988070f1508203002c1d1341c9043d8102400820310494004031103201da0340082c40c850b0500b855481c0d101e030305e850701800e071a018044c1415403404165003141345c5004020011300041d200e8030b40070708480c10b84c001d964200841c0103501415004207500c2003031441340d01040b0b4a00519915044c00942e000442800001d401505200c1c04c4010302072103c0217030a001e08100000e002e01d030b8030001c00301c0720540e082281d08003045800c580500594420f10615090700d1019110074621522912801a02c0f010550200c0303519090720305450300c500301403040c0341a8020754002001c116041c030500d10121002030084c032007594541c0c02150f529101035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106263857 1250 106262607 106262621
    0x2070f0506070f050f1e1506040b03070302030604080307031503030c03120e1204030b0a06060801140a050618150f04060809120708040911040b0301060c050f10060302030f120a12 78
    0x210040b214071800d170704c03071440d21480c000e400c0125603c003c0c00340c685904004941d4040c00c03c1d1000140c4602d0782d40b40700300001055040c030816018400d610001c401618100041401030f03000b81d040c030f6202d15103079200078183ca000030702c0b01082e540c5290301000003c0e086241c031080c2039454185811002c88500c04c0c0c90080c00901300c142040e118064100400e2602c2c040140141d902450a03c0425600c0040780c4e0280d6401d03110720000114080e004109038403021700350302c038080c900502d1120156034550001e5800c3c2c02070b006900d0600c11082d400c10152a0108101c08201a019607a604282002c00e450f42c1074061482568203214440d000070b072030b09409000000c2d0084105592a444040d24142080030b50001c0c054540784d2031070b0102030441c03691280c1c02e90b001c941c1205103451840e0700f4a10202c4a8800c5040111558071400740300c0302e43d148050100c5580c2462100000803c04c1c038500405250980070310800107143c10040c04050030080c45400c03540c00e2130150400703480800400001c88010072078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106265107 1250 106263857 106263863
    0x40f06030f14010f030209011a03060616060c030b0f090103050c01030f110a0c05070905130303020a020c0901030602030613020c1e0708060a02030601090b09012705040207080306030d02070f0506070f 87
    0x7202c0007203030a9401640c884140d9009480009580c0c0c1c80300c041c074018642000d411480c0207414400240c051900c1c0000b46000d40e29102d03400040c071180d5070762109640590303c450340032903160711002c0902e00b03000e0f0421100e500100c900c1d00c01d41d490340d1500f68403550000c80341070401da15422192050382468100900ca102604144c07584c4a1024038010300960f02801c044885000303034580010607038801e00855024814000300741c0010203c0e82c4d8240c00035070200c8000400e50080344120301742903858090250007540901c4025a581c541344041040c02d8600401070a80984144000005c503100000c10310740c004000c0700c4000c081290441d20b50704e0015294400103041c0714030000c110480c101500918059603080c0c8075072150300d40340d203840c91090281424441c0081e08103900000c49035007402982100c21904507050040d43e86490216050b0307884014291140d4a00005201d102d0030108400308543c001403020308041400c0c101c0442d000c0d403607031050300d214400203e1801e05003c8065440d48a143e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106266357 1250 106265107 106265141
    0xb011e27080a11090c040521010203041401050a060b0d05060109050d030e01020d0806100e06130303020304030515040b070e0120010b030d031e09050c092a040f06030f 73
    0x35984503402c0d42d4210041c400c54401010f80300d42201401c081c544140a2000c2490107403c150805041c0f0030340800907854040d41401250a2811805c42880203500641c091041034021601401c151801c2d07541c042c10500102c5d14100040080b041d0b4401a984103008000d00860240c40b002e004031071041068008030741c031560f010140c008050300101c6010700320000f030f001e54020300c01c1d0071025034400354100d4100d07400580c4440b40c240c6182c801c44a901401c64009c02d20380c01c3c54130015080240c00110381048002d80c1c000103050091007030800034804002c405940c0e6203030768585a070b00e844400e000580038005001000b80c0c1514039078042c015040014400d001c034031080c01e8040b01c940e0301034006510400d009000300c904040100707100f405241403500c00704805201c110102c001081c02014008402d551f640114ad0b00390526541e2400382c14081e0280e444501c00318120203201c4541c42d14000e55040303070030004120070030158100c200c80504440c1203060004081e14551169400b0300b14010302170402107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106267607 1250 106266357 106266359
    0xb1504110405030c190f0e100501020a110d0303060b0f120f061c080f131508090616020307060608010c0807020109120c030318060e010c0801050f0f010c0b0a060302040b011e27 77
    0x186c4180b6054072a010808c2c1c0c40c42110b1307440b0300598a130080a04d015104070f0620041c0650303424045400e0128610274030f03001542d684e542d0300803903c542101220407800702001420b10740d2001003820840d040415070401c070740c0750304189002944005060402402d03c550068442e010700080000382d4101e44580001e56586002214650f00081d0060003900001e419614040c0c1c0c101d441000c00034072a00c0044002c0465440f034100342d00326030354210f104004600c81000710708000760240c0290401489032000108074007407045006070142d4030080020045a14003000b810110700b00c2840c00d2400765060504024480300d40c1030490190524508002d844502000c08104100142d4099007080c03454000810900071020001c81e000c40c001e11070250700c1502c1c3c0b5003141c6140b40400301a081240705041c001d6007040035030303507503e13400307208658650a50303035503040400079400d0500403074402c0d200901c0c04c0d100307008400071944d0380c807940d01c031030f030810130020b0f15400b00110700d1614401e101c0c0710144108422a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106268857 1250 106267607 106267619
    0x4050304270c02030304020f04110f130501030b030a150519020c060103230307172a2e05100801110301050a09020c0a0b040204090b1504110405030c190f 67
    0x641060241c410070524000030104a1032010040d40d0103180d005004095031380d040700c10440584074900d0032000084e000c2015602050070f080041c41c400e139904180381039245c680b400160480381c1d4044203501903003054004000084150200894031103002d440002c581c0c40d5031840c0e401100f00e40e00070002c91480014201c052080014216041300d1003000301c01e07007040a240000780c01182114482c5550352007441900009038004c0305010341074805c01005403c2c0785da441001c1242d10788071030010324000303002a1782c42c240300c00034800840804600d154540b50140701400800760f10242140604940e580c800225600a03541c003503150007420401d00a100c00380d46e00008801692007882858070a48031008001040041b034000d1f5034095400c84007404c6401241c0d200c5000400c0300a0080760b209607205040380c001003001102600400301003001200f17245591040c0002c9030588021203c034064280010030080e03134005682c608041c41960696802c1d10700b201c03243c003624440e4120303a40d280c207070507030110309 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106270107 1250 106268857 106268909
    0x30513030f1401050601020c010c080904020f120a0b01080c0304021905030709020d15060918020409110301260606010c0302011b0203370503060d061d010c0206010f050904050304 78
    0x2d9098640000c0249807903035001669200e9654590b10b0110743c0e010506400700703800c24042c0c0491440035002528014140d45105c0d40c56122201225242100009204149600f8403410071100d01c02c1c2454140d9042c190418091404001e000922600a00151101d01150815980300509010f801c2303401107900c80f40000d001e1740082001a001e1460b015000800c0000a14030200312000e5840e2a00d5403418844d0100c12058002c24a400842e0200000100c110140c8240b03c80303401541d01c40e580b2541001000c0003c10922407010300009074220b950b10740501d0110708203070041000d090000700e000ba40e140503030162981c1c80540c26009410600040746075004401032600e202481001c6965070074514101109456440d0f01c00803405c5080c4215441c035010b2002903401450040c8210b41500440c1d55840950310b417502c004841c0305070356481d1130011800340540019070103540064202981081e40122150701e140c440e4601c115103c401040c207001041c411078000d00642c1603110344510b101c10162030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106271357 1250 106270107 106270133
    0xb07030b0f031203010b1308030d0902150c060f07020115030f0212031207030c0e19030c080c06180f12031321060e0106050d1103010501050319030513030f 68
    0x80200e100d210070308a186404200c0d5480744207042d111034150f900b00b000b1656260003102068607100e0f1107642c0880d920100b000a0100d10210050201d050545407042c00040c0c040041c49040c1003a0a1001e40500e8201240007988000884640c40d107a680b0710b203080f400740ca0a002240300c54240171a01005225626a4140d8028026030b0035183c0480348240c52650f074801c014910040e00141c2d804a11084d11a410820440c2c960f490300ca0121036a4100141040c0c40d07214040420140b0210b0800412065204000c0100f50140c06025101da00401180c100d20441c0b46542c0c62044103000c605c0c847c0d6541e13500c0101000701401c0942d4412541c45000e0356035000b1103000580828038803002a01c01c64410182080103170440004121500a40e690409410f00d942450756a5490702c102241b141c0b078540068030a20300504c04041c0c8a507100050500f100c1c410b82242d8041e410800255240c034144241c0204150b9162038401e075110700d0070000620441264200a00091100c09490188100316409030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106272607 1250 106271357 106271359
    0x4060902070b130b1b090a0b030a1a010903150213150305090d0c03050d06030510020702011b020303030415020705011d06060409021003090305090a092007020a030209090a0b07030b 79
    0xc41c02c2d02c0e0300300c20001880b48240300504900c0304070700141741800c040424501c081200c0804c0b5081400030400144851300a40150590260100400003022464000d414009052030300b0110f034240f000f00000c143c006240005000d58155044460000d40c4a0b4100c0362024248140108103548075079480122121250030180040d0510003c10403980e000304405000e50703030700d856243d0b400a89644c02d5503160090103921500da56542e80020100d01c0501c48012883c0c10f00c01c0059403407000c0d1001604840310050f035804034841500e03418006840010480b600a030300710b00308205002c91146088041d101b04034006016500705540800f018400b0803200c0c1718902094181c07940350f0396620510007210141c5402035405186584c04140440c0240c3c884512180649026032404200201089120704690f00800c006c41d510b8920701ca1415041e84031203607500070142400d20340100ca40025040b040c0f180130191040c3c0c41080800c94042c010804100c119a00030501d01081c03030b080902030b0060103014a41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106273857 1250 106272607 106272623
    0xb070807030509030403030e0402070c0f06171009021608300603070501080a200a02011401060915110d080103020306011401080c070501150902040906050d031d01030b0406090207 78
    0x82a05a4002d0040600c50220715008508003480c51300c00311340c500c0480c40030329005a420841d0340081840082071802400199081001c101c0c036040c03000740000c2d0507000c00d101115051050200320043e2446020448080c0c0c03001503140c2034001000404002000b00c003c1c0038100024610f11100848030001d890040c1d181160b5640c58100c1020300b009140860f45c066050700201000e105941c002d10b8400d80240da907030800200030b207403200300606141c2d0203080e14103501804298545015824017503021003007041008800d5551409d08081e00c41040ba00070008004100720018010700e00c6000d0116000750303060100d0710205210b503400b030a10a028081680280600c0c000071a880800029810400c90180d40d9440c16a0350010044a0b80d04060400c403425522100e0700c2a821950002d041c001c1c000c5e010f001039503240b03040718900484440307501c96809000d0758418000400d400c501c4182e124a1119081d0f04850361040c0120010303c0c1c0c20042c00d522501d4840e01040b004600e80c0a400f0701d87c030400c80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106275107 1250 106273857 106273861
    0x80c0a110913030203092101020a030f1b023f0d15080718020705010c08090d0c03170403090902030c040303110a08070210031e0e011d100e0a020d0b0708 67
    0x1009002d181400040d015901c00c02464049003880d07100c81c1030303a4032031300f0a804d8224000c1802c41d00b0ba0744004010000640c413480700c00480d05544c840c5015000b4403c82e2407030450b144c00d030069103442140483c444080c4070307815181d522440d100c1c4c22f41007102446200411544c1202000c800a03040513a1a401d054600110b04000030390782052001604c0306c040c010301c0c120345412003007188515001044040b05809010a00010f00d09002c0c50440c40880c0e200d4034858030300b16882d0340c03820043c900316004011822802c60042038001001000305490804803200030f81e00e504040d80c240800303500495002c0d10000411200c981264040d00a80b0300c41e03590441841640721041d44da0340c14698000d0030440b402c000c1d50005151050341c1032805200740c00c004c540e002c03000503030855011182c43c0421081c0c0d2614212034012000384110083c3c030b090b404000004a10080c00719235190000848a89166a01c00e00046000010025001030a80c024490421581c441c94506c081c010141c3c0c0030008030740e003040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106276357 1250 106275107 106275121
    0xc0105070f120c0905061806210a020708030c210c0306030f010608031815030a0f0e0f121303051c0206010501090605070b040201090b03040b1009020a050403020d080c0a1109 76
    0x500448401103076540c2100c05d040a0811001d54864213103250030052049101d0f1050300d51002400402d000c0c0c190f00b81e044902ea034040e19022034000c0a8a1500c1d20400403000000c0890007603e40000365500c0c081c0d242c140100700655a10301ca14011418941800d0400c0b1904281000075449090143c1c1602d008504002c8034038262074085c0240211508184a0741200c19020080d0401c80c0340c00034484e4100c4c8249255034203680e40155411001030752200300c4d01d010078896006072100741003c000109811041201e900342c48030100b40e2003040c8901e00141660140c20300000781d00c040c44d000b405550718030240c2103403440f4014800510708094007c104c00002e03291701403038426044a541c0d0311810328087da1551001d0303003018001c0040f4144406c00101042c0200741d4005148103030f07c02d0b4048621410583c0040c0b103203a8095004050150040023510145a4000250340c2100d6041c1c4400402c0075551420802a0007041c4840d5054030030701075184144202d0b50407803c01c84500391220302c40d46d26409 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106277607 1250 106276357 106276361
    0xe0105071b03080613020f0c070501020d0801081902030106170f06010905090604031202130303110f060c0405130f110409140714090109090f02090415030c1205030c0105070f12 77
    0x800c01034042180d1100098441c2040d14441940d604900d01c0103142000950407441c7c9078100b400382c180a070340303e80030500440d60100090b074003040c0a03043c40d00256262188040d6580a1284110950007001c1403400441d2825000200540003c030b0541da600083e151540d42d0792800c0c002e040510b84120000010400018491b01d4000e40c21103001d4515680c0e961000d4401c0c3c4849030150040301e07030070803608101c3e40400d04500c0c0650310030350340c081c28100310200030740c6815840100d10360207411807018064410b18241c125811a141501c00181c041c003e02941c0c40102070703890840d880d1078140300b25040d0080d02c4030020030030b58001c6803080041040c1000e912070003aa0486184c000f09030f034164a1400b0022801c06401d40c01c1051400340c000340e46651102040e115005540d201541d00454880c060f454180113901c402c012000307008603840e24503210710800722400d1190548511481e032000e828085e0a108940a0f90364100007072003241440a80104030422031100700b00000d210380c950046100b135034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106278857 1250 106277607 106277657
    0x60e0f060a09050d050319080a0c021203070f030605060d050910050417070f0c170f030c120705030706090c03020f09071713020306040501050604150f0605090a0305010e010507 77
    0x60359820542c1070420041c0519a002903809498902c810303c08000540405c00802c0001e40341603603501c1c41424242d5600d400d545000d65140155041000000190740258083c2c1e6481402482c2240b0940308264050303006041d281c001c5038018500160102d848242da07005580280c04150844040b1007040701040b0840d60700381c500a013107803203c044040001c250080944100380c0030f004000c00120a80c0d031541a042c01c1e0303500c488040341c0b10440184034614180524807082d01c003c0d010794641541026030b2030b1a0403070040b1208140300085841000c0c40410001d0301d1840b0783c4400108000905410511100c4550348001c9219018a104520341c070704181c0041d40c0268015180e007060343d100c40340f5220f04d021006111400c2d250b4006031143c00742c1d03810044140201d00038000083c440c10315100b4002501c5138030300440075900c19200c04228009940305880c0c2160340a203802921043c880000034002c5c4201e62014060b903003070443c900d0031030078103502507030046406c1e41740c8544000001c4100d900307213503e13 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106280107 1250 106278857 106278877
    0x90f0d02033f0f0f010801060e06090405010e030d0b09010506180411160b04050d0c02060a030203190606080f07090510030e0a061b080f04080405040903020f010501060e0f06 76
    0x4031014030601520021044414403850308200e41c15500b0760a509940340e00102e440c400060540028416000708031102c050240c18407900a009003403c0c01407190b40100c003d00918002e807007460000b4103010342944011280b600f030307001b6660707600481c00050002d00150140d0745e2140c04000000215803900300222030780f0501940c1c900050b40c1420040000600c1d1880242d9040081003100c3c5281c034898040e00241b09104000e50030030f6061505006207842401c6400708140301c07031180b00d80090b070796160981d488003666240160743c03940c606408003801d03008c41030b40d141d6150402d60003140813608014424408d00d0480d2811320107a40d085012100b91203d403064075000ba00740c2c1c92808242c0e01c01e0b048902c0b00c075040f10464a906000d03076250b80031640c08402d22220755800d41c60540c00141e00402e25a000702003e0740f1040c5a0034035403681c0c1d10310310440c8622841542d64fc91400300b018001e1240341201042c20300204099a50f418000e46100100c9044038070441403444c4031100c900e0158181d07014501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 106281357 1250 106280107 106280137
    0x2011416050d11011a120c060a050403150606020c120106031a040501180c0b07050118060b150c0601060e030c0d0b01060f03020c10020906070602040902070b0c072006040b03090f0d0203 81
    0x2905c401c0c0104140c3d10400344201d03020344c8071080b109455490040201440c40d91b603ca40c0e8520358209072107080d090503490440c05080080c100030650b8009007080b160032007140c100c4030716412015514018003103a84010a10300080c00d45102001a41c40010711441c05a002404040d428800f640140d0088040050601c00c903040144071030950034026000d2184075000005003402122991000303512003000407601c43e0f4944a95102c81e0411207507a00411f10300c482e2543c20480c1c1081c50a0302c0d4001401494100640c00506811a0740c042140200c0362402401c52428191079042243e16006c09001d48400705204050f14000e0728072a100f203802d40d43c10780004c0c1c40e07004442c6010070003030f502105410342e004106001210200301284010130041c400104c0045c1c1c1c804072468031006407030000f410050081070a1220002140110041304840c2000382c0340900f00c00c0c0ca0030006880c80c052a001024068008010410f070200006104001004903104969000e40080c008a0380c81c0701344a02103100032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 106282607 1250 106281357 106281401
    0x70e03060414070512010e0c011b0209130b1008070b0c03070b0a092306060f0d0209061201090507031103160e04030309060c02060403030b0307060c02011416050d1101 73
    0x41c19a03042c004001c12100d042c0d507003003a6600c000405441003c651051565500c101049241c3d00412070340382045404e08120321001100d40c01e0480803c24614041d003e11580c0002404005004003201c035103540c4044800300c1070406101c00d401c4c05586010b907114a205000002c904205240207035551505210015850518a9510703218610b070081c040340155603c0710441d00c000f420069039109580303d01a015814150720011142c50124013a00741e80c0594110b50000c07480780c650b00c118048040e0181c40c46104ca89400e000b007010b02c211914800d50075443c0101d030303004003c40401d2000031a806401000c48a01c201d004064075212406a01c0d41c3c500ca50702400c0001101402c0309550150003402c4c0059140600d0b2904002d850140146400580021040204154051241800100040e8001d107011400c02c0009040b0701c80c8901c019040c020840c04483c45540c1031001c0302c141c0002d641c0707903c4e00c40c406841c0460356025034610b01d070081015907059100040c0c0500c920000500b060091900356 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 106283857 1250 106282607 106282613
    0x6090d030207050c09011d0114010f0e01021f1a0301050705030105010c1106040e0603060907061407150c05071e02030a0f081201060e040e03070c1e1203080609070e030604 75
    0xb940404000c4a9a000c2c0400c1e0110b2940c4510600e070090440d60f00c04a007040403c04042d81d040c0341600115000380c0c13080d0b80c420050368048a4002c0500c0d403410b1001d40254140300507442e110f03c03840312050992070190088104611900614284900041d09514a8070304030100b6098403011104200042c6c003d100401881d880f407010000c80318040e8180c0401003c40001182c010f6009030400c1c3d4030340038071400b44042801c2c100712031980080c7d03840190002a0078864010520406851801e0505002080031014040d01020b90403481d004100300b00708003280d80d40c0161440e003000ea0283c1c6c1c2200c000d03c90145035030714120a1114030f513006020704481425607446050800440109031a806414000e140c082801d41242902800503610741c0700098048404000c00e40c2c6601e805604c184d0010b000c044002401c4603010806d40e0503031540c1c0311280485403504500340119a1160000c01c08040b050410b241d00708411501804082d81d6004442e03452603c10f5402c03100c4005101c0d0140d200703100003004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 106285107 1250 106283857 106283861
    0x608041109040f05010203040b040c0b03040f060c0203040815090105071e140c01020a0903110301060b03130206090613030201030615050d090303020c070e2a070f020a03020612040501050906090d03 86
    0x2c0103210780481000d4401d83d8480a08a8000300d50444818413524180001d100d80b51203448010b041202c4141d2462a29a4800406445107000207000c980c8980450540320b0080c01a00c0c050240f80c800c440301d00d0800444120440d43c281c85c0100a9441c00001c2220603101c0c0b1000524840d40101d0000c003075400c00d404440b00e507240d540c038002d801001d000c0b0546078402800140400c08261381da0310b84081c11800d2070142d042d0306240e154400d81c580a01000711510150507245c0c480003401461181c80040e00102c0c0702449100c2030590701c80c0b070004965184c010003d2090043d01d000707076406c100c0c42d5240d02c80c1100d0108030f1080351000c0344061160080d85125030b00b010428034440d00e130141c204050f00d1910fa01c1c0000039007220809094410411586d00d48280030f101590260050610800c80080c02c9008980314a102c00ba00c040e256a051409540390f030f0002c18001c55000d010340369542844401040c0406080d2411a0b1755401c00c000302d26030520001d6418080c40c2140045d02c2010610001600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 106286357 1250 106285107 106285111
    0x20d080a0201180501050403020f06070f08060607020301140109181a06010e0909070503060a020301060e061b031606150317071407030b0414150a0203070e03010c180608041109 77
    0x3045640396042c40c0328881182e18400c00c2c4502c42c42c004101400c0071302d0081d0400c074201d000d640c2c882e03001c0410000c03250341c40864003c13000c032503040034009602c030040030600034401c0c0d0b88065055801d20b003540b803040241d50303002812611144800c104034072441000406800c0340c07210190100001c0441d0044c0d100482c0d5140d90070803014100011804004404911340e95011204030b04944c01c041b85c200038a00301030100550010b080b410441c0355604041c2c000d80741508040d44a4095034001c1240740c404050a94210300c80c0051004594441c48004686c0c003c0d00038492003140c0c0d0608214600c50390305000043d103000d89034001c40d080b5510f0303645103800c8216009040243c40d4414818003001400300203100301d401550145c40c80602614260030404246501d03480106d606a2140c22070402c0c5990f507000068201090030303005030356502c402004844800d030066034594507500c2e00594950281e002040c200c090300c00d008514440d540e54000a96001c8000c450207040c030f43c0209000301071898080d46070381d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 106287607 1250 106286357 106286377
    0xb060414060c19021c0302030d0f0b030d21091502070203030d0203010905150102030c120d0207020406080703020901120b06010c02010c1b061101061a0c21091305160309060b06270a03020d08 83
    0x2f0391100e1580c0020b20700a16084400040f900100002d00c01d140c080550b580741c045e0982003444500c025554100100c4c0301c90f01230690080c3c0c081001e50840d43e0a004070f401169100100f90349a5071200803213001802c05407250a401c11840260a80c0e650022081e52600003c5d0306c0542140e481075600071701c84e82e000744600c0442c01e03400c10640005985074400c1c28040c04c88600240021401c61060015161040e0444505205122024400918030300d582540c021820711b40000014001d2005a9031403194a400401034445c0d0307107201241c9807469007046e04940071640c82e8aa520a0080a80d080354850f00805840e40300c004c40040403480340000400ca401522022030300542a80303003e5960402034a4401d10031610001800a180d103070602100c0c0446c0884401040142060700b075400e80280c041e811030080c15215410f400512032264084280c0380350142600e0354800703009020307070a2748000700780100886134190b003152024144110702c0e41c20380b0f9014003a2040441681c5800300c881e040480c0f44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 106288857 1250 106287607 106287611
    0x603070c0804031b1401081f32040e1b0a030f080702040b06090a0b0c0a06060620120711040608010c020c1201051006180b0a050712030b060414060c19021c0302030d0f 73
    0x5041c0b00c0080441a072749200ca42081c02c2d078004054007003c20b00b0941c14051080b414007020b01000d803004038880e00c01400340c0c10854008000c05c00410060080e5910181c214001d8503506014080560020b000c1c2e40c0c0301b15000c01ca040805400c1181c075000d07090016400103614103050101c450100000c081c00345040307007120941e510070342da1082526015002680001c881511030307003036403414001c1524211003100c090078052520f00c08402d018040c01c100600b01c10341a2002005d1601c07a9800700024008080003407004e0742103480003941e04e00c00a4085401001198100c100d4640107100719070068003e001c4038881140380c02e0b403c544122a180050241c030071540000200c83c0024401050080307650744505455800700e0601080811a2810650615080a00018031a5100c03001c0f5000d9403081640b01d000580d2810100c3c101c0e0280c640a08014402d6a035a903050216009111a60724800c40302c01024440310400341d81415010035000740564010320440700d64802e1904414010703440e040c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 106290107 1250 106288857 106288859
    0x5010c023006011203051801030905010903032f0301050f0307080d3f1d07030b0109110406050f0d110304031701060302180603070c0804031b1401081f 66
    0x1444620429040c1005080c0118103030010705803034144295030040c6580d48001000c800c01da14043d0242c8036a9142405031a000007100b00315a00a600c80700e00f254001008015814461402030024108040b0102460303015016440d140d08080494070400401c2c0d02020741182d10b05000d0003641880351506d507a040c000c600010a081908000325800419107507910800303200b00c000551101480103441c66409041c140020401515109400149035941900010360754080003040010b602103650022160044003000400c1c03261020000341a990b84840030020303440000840034443c070070780c4100d0700440c500703104101d90101980b02900710724421b40c902059882d03808503d116103a0088900324041248000c0c0041e2112942e41014050540f42c1000c520b410044640c14a5020100321410f126090010024500c207102e10207203030b40158803010154850344c5a207800215141201d280c11100341c020b0710000748240c100312128400d184180c40700e04254485204d00307902d40f0301c2500302c0c02d225100500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 106291357 1250 106290107 106290139
    0x905100510020d0807050901020604030c05102a0207030c0303141b1c080108070302042c0708010e0604020f0405060102010905031605061006020607080919080307030b0a0b0405010c02 80
    0x2142500780469501401d900d120a4002418004000e00004100300e82403062a11a90300003070315681094145c02c022101d00c40f185462071418503041c8038004001d0800880d01101c00507489604080780302880c24400740c10060320100e0b41c521942c4409400350305505020800302e030181124802c80c10342e22000510700056030180c102221305801480f100c03a072200d101054408031fa9003886074000908e00d0301000951400380c00c16030381c080320b01003c0d1040d41d4864109149070301e001410380c1800c2c00311020b032440189483d60a0b40350065846008595401c0a0f419404030070f001c2880d5118079401004003514031178030010322000b003a000341840c1c150765850000302d000c5402000070b000a03144081b1400c814181034685181040d0024142039a014507108091001c3c03600407a0099204026245c4821a96100e42c40b403883d0034100303115040a81006d0405005110021004501c1a041d5450034009410300905028100155100300c805000050006200c550711900da421000d0740024a12504407803001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 106292607 1250 106291357 106291369
    0x605060a0c0311010b060307030e030403050703030801030201020609010509030a03020c10050c1306030203060d02010c02010c080d090309060f0e010305060102030403060f0203040209180607030b1206150102010608011509051005 99
    0x4035034100440d0000030010304060f84125010514a0f606000380550b02d48000400e480d408050303c00003c5c9504c0c3c621042c03e00404000750342c0115085012160b140d5924103010b01010000e0000382d0040c0a0140000c0c0201014000c0398000c0c0080c1c001103142c8101002c1c210000c0d08101078000250141045041d105200c0340aa213018020440320710745d55028125000c120b00225a020038145070041c030400c0030369507814403903071a4a078081c01c050144070001c1c401242c88181a1600802e4040d002c034840001e4000350380a000d030a8442e4031184209a29000141c40070040401e4503000130b4450680a26075510030f4100710341148043c012242090345039502d0100707954204c07a0818905901004000551a000a1071604020100032001c03160720044002a00d91311300402041c18961698144401a1030307044859142a11003c196030090401c16101140303080c10b205100e00540c00d200c008526804184680c8243c1050136030f502450b5441c1c44d800ea80508001000a94203202a140020350380d2222 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 106293857 1250 106292607 106292617
    0xa020609130f0501090f0e1209030a0f0609061505060702040e011d0a020f041e05070e0d0305030a05070e010c060f0204030c150201270b04050c27010905040302070b070303060506 78
    0x2402e4042034641c18a00031004840801610700e01440c103140d55004088808202c0d101c0110503a842d00350f59440f000007080c41d100301d018000300380e0f00081103c803041c0603c030b6021007401c500c2000188140728440110030082081c038000c141c1c1c481400c10845e80145029884844155816400402c18080726101000020010b045880140c1c100440e00011481c2651442c3c801d601d088404001d14600d400000340f00f007000100e80340d0b607190f42c0c00c0803d50084c003c03201803134990002041f50400c0400c80c40c001b031090304282c500640c610b0520011801884c00b88546640088060391240401d5070b6645441000e0728041c0c01d034482c4d13194200008004512218002d2000d014040c0748030300d2800f0000790007400c40784070121680040600c2504c514241107403c90407007802c0d4206195018540302c500b0010305080980040703d51080300107101c0b26942a88020700c51104030501d81034a03d680e40c600e2085c081d18400c690040060f0400c10061010302100409004468001d25000695580b540003248056101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 106294964 1107 106293857 106293881
    0x403030f1103030717090c090a0f15030c0e090705130504110a090e07080a050c28030303060e060402180f0112060311041d0a02060913 59
    0x42110003020100c1e07684103480d80e9060010010340a030511200c1ca00020342e20400140341c0560118800e000c0b0301014044000701d51320b00169000610605c0c0701010069907440c000c2c1e03600070748c42180301c010390320448030071081c1814083d00c0c0340c0380780000f000300d00f03a0f0b030040c2d6060006842e00454010758401c0c1000200d09511a46401100c40310425440c07600810003c0c00021340800030f42248507951020400c0d60201d503150007801c1e807503210b04407018209034040d16040c0154108007040000c44400400907910420b0a260000d480e1380e0243d0064001a886007000c1c040701c0342c2043d2880d0048001c440440c82c089403094940d5461117201c500e03603c10f4880310420340740340c0d004810304810b5118210080089645a10f00720b5540c82d45490982c0c0910300e000219190b03200081401c00301e0b00c8001d802401c0e215499402c00009034031000c0d640340c000902c000c0070000c55005009010300142 = true := by decide +kernel

theorem cover : BRFrame.Cov 106115107 106294964 := by
  have h0 := BRFrame.cov_init 106115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 106115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 106115107 ≤ n) (h2 : n < 106294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
