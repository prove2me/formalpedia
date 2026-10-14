-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:36.540652+00:00
-- url     : https://prove2.me/submissions/4eb8e86b-7ba8-4215-97a8-927307d82869

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583812949 ≤ n < 583992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583814199 1250 583812949 583812959
    0x501030309180f090302030909360307050a0305030108160315050711030f0a082d090c1306140a0e0c0f070b0109021b1621120f12060f 59
    0xa07455400c2c82040940018000c0d850b18803060035070f0400d1000b100180c2000560549520700140184c2e00100c40602810070448040b0f0010120144076481c90040d9007440344961480710700304115005c40b80e205080c0e540c848003512300074100e42c00a008001d000d00400504841040c4a0100d90b4116904400310b10007045200000f08000c110280110080117107240298141035000c2005101210400700340b00e90f1020041c0300201001400f415150392550035451004020003080b20001e1010000116880c0b25121044040c0c07510500b40500e64001a44191802107604654811b400f102c0c20900710b10b150b106158100400030000780202c0d007002c0040d002140820300c03c84007526081146114462400010740c0310b03840b19501c241d0081a1054001582990650425038009590380502e80104401c4000f100c1070642c51b413550091040c554a05c141e2070000d4254031a9000585400044500700d03856840d0b00240400424090031011402141502c0c0c1050070034807410044a8840d940002041c0c104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583815449 1250 583814199 583814219
    0xa06090e011a071101030b030609061905091b060417100e01021c0c050c150714040e0115051209101a01081303050c0f0601050a060e0603070c052a040b040501030309 72
    0x101130942d04040e03407841000c109450800030980201750a2004002601e064000c5042d20a24038840000190410040c0320101e14000f0b10301c10708a6940c140b045400b004200428603501079640f0040c200084003071264103441012401400807075450005100f6210741054150a034410381036030552144030440d1685018102d503201d000410100d103003003490b107001c0c3e114503071400d49000c0c2411804064141804040c82d00300240c03d00342c40034048100d0909107080e00005c02ca4905100b0700d001010b28213002c503100e41c0310300c0c1243e40c46140c5141011403414446406642c42010340c0308540c1c041c2ca000001202d2105001c0305124400f4141d40d01181035580c0a85004070700714a00044041c07003401d120310301348800188080110144514014041c5601d003500300802c0c070a07076901c0038040c80861101400340fa100c481c101c980c800b555081201141c0054501286091070752aa2400072051201c92401d10b09810050407001c68000c65040c40040503000802007101d000707100040200301e52920811000c1c8007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583816699 1250 583815449 583815473
    0x114010c0209090118030305180c060304030e1507030c0606060e060405010e0616210c0309140f0a1401030e0606011b1b17010c090b0d0e0c0a06090e011a07 68
    0x800f00013050301074445051005100c0d41190403808691240104502524050301c000300600c1070100509854100034081189448041c102034100210a131582c0131a844445022140801440c0c606584000c1400e00074010b0009010440707000b400e01c1c10000d4464442c030a0025852001001e01c0d142501d4600151048101c1d4108550419803d00c811584030002050f03619010f40103103000304600043c0a503281c1c42c03599000203001803010840c08c0d18080303684000c1c00b000350750760b520b6203200c00100d44d030005404e00703681030125504c40d82c088404104e039071030500300000741d14080e2000e21911460600c865140c020855500e40019607050000042c5580002003582180c001c08113000c0c040280388000600001641000d000c0314041c1920740c5a1072401d1003120900f46040c0b070b2202d02a806e2074011501481f52100444c49552111162031801506116040710704200424062030290b888401604505075031055004803001c440c0001062021408140e00140207260717020300c1c010300c0356124010100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583817949 1250 583816699 583816711
    0x70504020c010618020c0624040b03100c05190207050906060a121107150c0801030b09030c07090e01060512072112020f010c090303020a08030a141003030201050114010c0209 76
    0x3d240c2000092001c0700c00e240750160100d684000d42d03a002c050018178a41000648004414050103070510300d99280c00351403949074a011a40417070b101ca0f1440c00246050302e910341d40101c03545050701d50b02180350402c005128884051b0081c00250200c200280c0c0c460000c0d00c00c01c1d400a0746031002491071301d8240e006083c00c080701d040c484107070702011620500700c80b1018102e0070034441c0060310409101280499050301080840240151405000002c008071010710000b4409020b078804a00761400c02d2051b9075080d41c0020440342d0b11942c644804000d0445085480030395441c008000c2001c0c1001007804038a49060ba005040351864410082d0110703e4402800c0111a0503c4503400090303001c0c000680c0e101e0b03032907006000505010442d05e0842d40e0161800c0c0074084182d604200194000c00c400c048550031814981c0c0301d50302c49203a0300283c1040101d40b42d8140803102000009204070000c04180ea00941c003c004681c0c940300600305980104001a0101b4070344203d00c0c0040c030300401000d511074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583819199 1250 583817949 583817951
    0x5070e0a020c070611070e0103080a0815030f0c09060301091205090406090e010906060807120b040f0b181203130f061103130212030f07030c030c08032d09070504020c01 74
    0x141030100c5160400c0f1294000380001008002c0e56280c0007001c00003000030700b1100b40c212403254956070701c000c11485085000002c0c0a203800c00103e04048020781e1000840c0003400340c07034071803103864510740d1908015030380140320786607280110303042d030605104498103580e00c118440d038007210410060740c0300e411041c1080d41c851b860364404200d041040c003030b8003400c0c2c90500010404072040d10b0040150b036100d810010b0a075000403001c0100703900da01c0c60740d0304440d00001725040a44480c1444440101003034400780858000c481401101201845511912010102a80cac0150001c580a900d030740320a40b40c4064940d42c2c090a41c1c0444c1c000d08001c64054400c40d00016800c40040480a080d0022112041160445281c2c102513041185002424003481001b651400003564000d00b40c600880a01408029a507510001054010003a0500c1107070401000307a1246840d08104135028808000c24145403034000c10a0407101c001d070440b80c05070349540c000c5d003003050401040c040250800d01c01d80c0140c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 583820449 1250 583819199 583819207
    0x703031e021915020f0306030105060409021f0306030606060f2703020f01020313060305010f050108010e0c130f0e0709091506080712060b091503040c090f0e0114060301061205070e0a02 81
    0x1880c035100610005c02c1e10700c0d00f0780e00c034a4a20100343c00c60fa030041009000c1c2d0704144e000b4005035103046407142000c1201d080151012100142200200a2a00000c107071034900000401d419800c05154141e01235999610481280420200d0640b024040800d92084600f49014001480c09813011810b5000600c101ca0a007126502e511130104031a138460008240d82d80018800d4584000c001c1000e030600b0308100ca100d501d0218480040c40380241039081c204404120208101e80c2c0710b407041e0050240c01621490151210943c1101003800d50721000481c0c110480014106240e0007900c08250400340f0740e04000d0315014041d074491100418050400c110174220f4101403505104110280c40c4040704036455440c0d10303040c8450300c681c0c1c2d02e105a0701d08082c8100000182c40174032031003d4a4203940e0128442c8643c8140002610014210f1540c42d42401613401511141548181c03150714101c00030300006540b40f00e01c1000c018801c20252103500628407e119901000310907c0d00880c40c80401440c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 583821699 1250 583820449 583820483
    0x103020913090c1502120c0c100e01180303050a0c060209100806210706030e010902060318120301140d020a050303120106020115061715120703031e0219 67
    0x1540c58040c4020a00390b5410900c000e003c101e15200016000c0856001c03458442450041e640d806c0214101c0c202c1c80c1c001400300c969a00c04c1c0000c00d41903001900540d200c042d0030300081c0038000c2400308a4001809205141d01b0460f2880d03003030f0102c90b0940c848628050541604803070210360000280c075415001c004140c21501c600700c1c1002a00c1c215511000b990401204000840d06400d03042c0b070b00e00d0352922201c030782000041403103000c5450606000660f03400f02c0c00c1c458090803c1c07485c069407200d4040304000c00405001e03e40315907007011a003a24422180440b5001c02800280140d8040c00c982614014250800070003100d603a600041c40340c171031542c1c0e510001e45140c0c0302241903084c12100d070004010303e940900500e40c41c1152036940350030b06420468010107070004c166080c060300300100085001d165490403902e4940c10301030301d13260480100d25036541c1c0e256090b01c8114002100001004003803204102075440500155001d03140841040c800000d0f0b44010613403d541c482000a1483c1c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 583822949 1250 583821699 583821709
    0x8070803040c0f08100b0301060e0f04030c2f030106060f211b0f020d02030a0c060e063d091d10060f060c0213020d020c0f03070204060b0f03130201030209 68
    0x40130440010201c0f44003100c580b07010b07a00c980c200c03580242c0c1819018490403000710000350340200443c055128a41d01c078107088440c080d001002900400c40e0400044200e002d401d540c540392108800031110304c01001060600320380c9603125103030000364948403e4041910078517217814840c04401c0340184403a03c412043c42242c51010344a59101d81841400303880341e8009019448250090011303044490f00f110b4080d403030f4425444050200a607040048040183c503a03c00c1400c200b0071022540507241600e04020114040855009142440b660420302c1384c0307803107812548200001e420b24400500d850b850201900c4c260700141045041c05544040327540040000c04400c88001d2000b0800070700d46402510020b203030742c100004100c0b6029070080540c0b520120f00149840d103001c0181d80f504201d0310300e8000c1c054451310b4a014022160b910031400400800741503e2030085904104441ea1404214228400c803011102141400e00015002c1c0c042c8200c441c1150b80103040140c50252800000b032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 583824199 1250 583822949 583822979
    0x71515030b131703010305060f04210819020a0c060b04060812070b070c030804030c03110a06140a0608070b09180c0c15060d0b100e070f080a020708070803040c 70
    0x28640040582d008043c4a0442256640d1a2941c03400d5843c4d5411921040d40711200101001440380026012a040140ca125281140d851074800d85500034001368000304004c10940c0c8a0401e40600540751641103044d20899100743d03645c3d02c84011401d031564904029115031a000c41e40b05686810014504000b413101c0c580184a450303d0ba60742c1c00407454046000380300a00b00e5810051016207110009411107000d68100d40c16041c0080c0f400c201d440c088401020381c100980c032a010381c51034841040440c2e008081c04a548910342d800a5035012804011140144074008031940500d904102c2d00c09460700505418a000d0011030482c005641c40c0740c40007030141c3d50400c0b2010002000c50f1091000e0184c000b0b44850f00e0316100050400e180041c088002440e000b030100307078411010034240840d00c2401c80050400429890740c0d49080d545c003510381740c0c000403410042004800000ca24000714801c940030154840e82c030318113104550300d401e0b800c2e03000280200d134070b80d0260301c0104202c01803180e0f413 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 583825449 1250 583824199 583824211
    0x304170304030311070b03240a08010b030c0418030f0315031a28020f04090e01020301060212131401020109060603050f072102060901021e0105010e060105071515030b 73
    0x190795951862400800807440e010812036243c12009041c44800d402400700d82d00060f04804c0c84580100048000520380d18440c04980e002c041171600051408041d040031002d410102d0658002c0754040c0c0522058402d5840c0b090303016101c1403002c1700024040c0300c80600d0740045150005442c68980e001e580302c07030540d400a07140070000c4034103070400101d00c0e2082680400c11f544400c41c003030031724403006400c580c1590100e0f0200ea008208601c00907803038819140144080b21702446400090880c0d0741c000e41c001e000340350050150241025542180c0d80c2140e040b401807060245a5a191840d901c0f00d24500211450442d526000300c0004209280908005075008102814880101c00141442c02d450341c5d000000d80602c0c80782d40000c050030803181401ca6501550f140f961180090b004031705210303c200e4040c000300e1001801915422055000c903040e144020f07030b0369805803a20401510b0b5402032060080c1210620150408c1d402c0d80780c3c0020765500e003e4106220450340ba50f071004140341084402d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 583826699 1250 583825449 583825453
    0x50616020f010905031c0b0904081b0109060e0f060c030c21190c1412040f08040801150e0c070609080f040902031b090901031e021c02100914090405030417 68
    0x1c0003980c0b00448014000402840b201048101c031f40c14081091460000c1000d0500c4102180d03810f4100c5400c040e203000c0400d140000c03c002885464006c0040114180b191018400c98542000030000007455a005a10300c1c81141e0450341e0701c0795442102d91100040742c21303002c070840c0201c0c8100103002c20503006103052801d000701500050180404c42d240c02d0390000420651201c405d07488059141100c074202100007134018240c0d160300b00b140740c1c03002000c0700a00d14940028001220b140645c0480d6041030940d42544580d9920040c2d02001c1401f41c8104d00071550821070b030f83c0014240c0c1c4c864031001d4413401d4860b00b8941c0055000c3c4a40d00140d0115103e04d400104100f048000b82c030540c0085900640a41c0c1041386c91008100350a070b05000041104260020442d00380c4e4400307000c1001c2c6d540c0145002440b19010500c031440c59011a400c900506a070307600515064010b00000c8180e42c2038401d03058648295a0401070f09045c0680b0a4030980001c00000c14410541d810308840c80300c220340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 583827949 1250 583826699 583826707
    0x903050306040c08070f180e2401050702010539030d0b032b050f0403060e0c18070f03020904050a05040507060f080109090503120103050601170a050616020f01090503 73
    0x4188003c0d2550055031404101134101045a103d070040e4070f1002c0600d0318178020b80002000c0c00c10a00943c203640040e880c4001880400c001a0500e60008071000d05003100c04152152200042d01c5600814038000d022030300501a05082c4002d0300103075800c10700000c1c0b202d44240404c120000c0514100301a40b125a040010b0000d403444c0240949803d4800a500070301e2050f89074000c080c0205044920111169a006000b0005900c5801500c0c24100d00c0c0a2142ea00c075a2480c012006040c003030322540643c000e604891803607103070089200590b040280c80342c000d20341e2810002c850340300b82e0588140615509200241d4591218030540d403183c00d101d080040d2604140c2400c9140c10856400b0604004005034078104496001e4a0141124a41d035000301d1429481d00d805400c50007074a40040140e0380e0380000000744080054500d04860720000840140c60032203203610744030164001c01610a41c464404921103042e6803182c060b0003203252064403003021444903e00d080d24500301090311954008a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 583829199 1250 583827949 583827961
    0x31403030f04120c0b18010c11030d0c17090d030506100c0602030a090b1f121515050301020703030510080d051206040b120607170603190602130f0f0e0f010b0c03070609030503 77
    0x40300d4072302501c88505000035540d2292029654a1045034108442c0c161103056040525004021382400d1000503056001d0a2805940d21542c5841e034592840020b41480c01080c000e007400041d01240041c2542e9812040c4002d0319500060352004c4d1041d21040e42c0c2c0d03881034001c0317011810b4090003001e40000300f0401c480014a03a235528007881d04032010007102d0191340c2c0c0000364a00700d480c4510040f003901103400582e00f0041d485035010343c0d001e035400d0f500014021080581c15408148540049031101c0842a1541c08084d03940e48054405404280c2c20840d00420060240881e41e10803c01032003c1000b0100101007694455140d070b800c0700a62283d018098450381008540340d00c040542c1d03e5214030716084002036600c0064000c0000c0543d0b245545e00d040c022160110381010600312450444280da4101c00c440e1075010748500059088015070114100c1303034082040c3c0c001c0907907090050039a4240511800140c1c0b14140907e0a40301c20814000001d40a025004140e4040d07221035840c0c0c9020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 583830449 1250 583829199 583829201
    0x22808010b190f0e092e270b0a090204020703080a060501030213170c1020032d09190e0603070602120a12060f031403030f04120c0b1801 60
    0x4500451845907a61083c0701041050040388100d0300714594222441d116619000e0038030030300251402411a5245407420f2041140711020b0f030ba022194400c1042c061408100003840000000480c4020a00141600425001981203401c100711100c0041c6520307030f070350006040340c0c411a0100c012804820170041c03015141d20403500205401c1c00e055107003802c40c110440c1200c40501480300411014807914200f81c0f41000302c020200303006041c0710407225101c0e034090401e4110500c0c9002812a1483c1802c6040f400300a9500445034a8051000300b045138030518408000c0003141e00008006002000351303a074a4503854500c00f441000703003e9a50317003850441701044200500341d9010b540038010070400d040e030010b40e0300c40b041e131181901174031000088000c85409616600000e40c00707041c0680801d942c0e5010304103100301c80c415000700c0c1141c1d0304080519142d01048848008016940c0f001402143c24000c0c0802c0b060440c3c9021500ca60311070380ca041d0a43c4040d980300c00e881c040c100741110b107031500b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 583831699 1250 583830449 583830469
    0x20411130f080105010506070f150608010209130e0705040903050d09060b0906030c0a0306051b0c0106060f09031101080a060305030309070512070f18060509090a020301050601030c0c022808010b 85
    0x142c000240001e41c10600440c0213071040500090500096441d01d9050000400d9200e140440c8514244030040c1d50719074280c040d4200e800380c1da208459680b0000c5500300d05226480040320340130007410619190404000c0109801401902800b504000351541c211051061000303492003503400065030000311061000c2d02c080200101d0003580032850000c43e55640d011a0401c40b9400702000c034213580c2d15101002450360082d00e402000d40042003001600c203041d00301d481901c510b03540e010240e03642c0c031108941984142c80083c0c00342c040d40300c091045510500110768480c0c0301c030b0004540300b070b034a9030345503c0c503802190320400b160040e2000f841107240c5a013080c080500040010100c0509000d030200d220710721403207922054089440303081440009908200e006080041c500009440c08091180d00d445202d1000c0303200703502e05800640d0641c00303885540c405240c00d0780c2e0320801c020140e080c814268030b07100c031020358850850074003041c108120450300090503c10001095102400e0113204070303498 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 583832949 1250 583831699 583831709
    0x30f100e06070908150a0e0d0c050c010c021003090615230108070f080a1103091b0d1e031107140924190503122106030c010c020411130f 60
    0x10001c0100100c3c0400502804215100131003001700381c0780c0d580d00c1e100510b07040c101c40c0c58602035113810751101b40d0004051000030703004106a03001c854210004680d10026158000d5000d0f040004214031a0300c41c1d44504101842440006105c4003259441010b580c03040d881a20284287e000400011034400a201030a00007070a006000b810882e002810784c90a2003041010007400e01d00280e038415468010305c01e20418441c0042d903070b05000486c2512001409220803000045684140700c50a20104203010503811403094001d102d01d2600818040741c54003000e500700001c0b99180407890134103001a030001c11000002d40382d00701da00d10034440714170b01c014110220a81d03400320340011030742c08900884035414102c4036100280002055094100c00d039400107030300751260700240442510440010189034040850908450034105400309054008489058154200118002d132550140312030b01c525910080002c25140c0c030003c05080caa030044035940c0700c224400030080110b0303030003024208050a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 583834199 1250 583832949 583832957
    0x403080d0f1a011e0203092707050703050a0f3e03070506010e130c0609060306091a060d0902090c281b0c080102072102011811030f100e0607 62
    0x1040c2c00c40003a01d82c01c810b040c00016218205516003000c1d00c280100e40400d0001071160200320051031020329514846945541c0d006020000b09a003680114140c038481c541c151740300c518101c4c40703180468500303070070002000a2007080c5114a060610130a1500d07004100741d07600410380c4002c004545101e03001070076100c030650410401d83c80802d801055044c19249080c0c610021074803100e007800c070703600202080640801c0030300001244007070f0300154a070110307880c44d030f41401003984940c500801c640350814083c101c51480840c1418a0900c80d01030000c0c0e0140c0040050f203225a500410400b48041300c035081c42980000720164045009502c550b80c0e0603050300586208204018060400700f1182c0c00c41a01156040f00740080005408240d030150140c00020742d04c1c0da40514060000340380914110070b2040c0700c0d40903850118414880c483c008000e4401c07001761003405403201c00e401300d030310b500706a054001c0140404071030001b081011100101c9403800140d11080c04805800c045000e45580100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 583835449 1250 583834199 583834241
    0xd2006040b271c080918010e0702060a05072709020c010b09090105070801090902030c22050a0c0509060702032805010507030603020f010e0a030510060311040c0c170403080d0f 77
    0x12600208407064242d0b80a1001c5981c5c4d034010300000c100708075910711002c84070b100400208a219850320207a0085030242c08441407501d44002c1c0009881003110400d0024000f0701c120082c440c0700f08200b00150420400740011561942d6905003a40d000e8000c60213580c4d11006d80755090300b464003407503078081507210080045041861000704840418428120340944404001c0b0a41d0b070b080c0038460304510010813440142c2c0002150300a47d54152021207825882c21002400e06401800380540055441d0799192a06200d81c0402a49820504040e40c042c4503103110000d000c044d8040c00d04240d1f0011281f016102d419140c00360079103500804110170141004001c00068840741220119071000342860081200d040e00455884151580301038014820703001c0300110103046920002c01e40740102c18044501200c0c4040c003058030750070300a071030020301c4240c40d60380403500903040f0800e030303030310107403c00b450141d482d2107241c0c81e0781141903201121981d40f01c12100c01c20440c45140407000071000c0c42c002e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 583836699 1250 583835449 583835479
    0x330e100e1b041e09050a050103230c190918050d030b060702040908070c1e050301060503070b030702031611040e0610030605070507050604080310050d2006040b27 71
    0x119014074443d250306203000d080641c0c804841d9048203005400502001c00641c502145043d02a040a1001303481e100100071038901200040190202603200700c100a041103232554051108420500761a0b030340c6d241e80e10b40003189510f40ca00035040c0c1c0c24400f05030714038010414100207091568980100c801c1c940391100032490f44d11128180e5581c00c1d01110005880b0b41316042043c0d040c031031030200500d1071404230742c0030458143c021504100d80c0030300c000101000303480760285400ca5115000e42e0f58958400002000002c2145004560048051040c4c902f400400c14128900d1400c4c030100315035040d400311514942c1e05092240b03030303031212100340240711604103203100c45c3d915040c500016203400d072904006560700b0b01900454a80a07400400c0301c04900d01030a02038842c0d0010b894803110842d0403040007400c3d1504480340b901c4280c200b03001844c0030820f05a400300440b00318141907007180d0140f200041c3c0d0161352000d0400007640c5c00700010320300c070120308440203035089889480c403d004010000321 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 583837949 1250 583836699 583836751
    0x30209090f0705010813021003060315020405090103080306041407080708160507030c021f03090b0105040203091213120312110a02070513020409090f0302010f330e100e 74
    0x848400303081071415030b00c42d030141c0aa5480e06c104080d403c5292500915003080e807650050040380d00940401c41c02e507216071050410b030300c601d201d05039001c81000014000300e000c0a0003150010b01c01400003038101001014029024811907039107020031306010400c11030075049030348281d0041d0414240e080089070741c08040d01a000d07407100502081001440c80c030464807000c0c01c0c0103040800d905101059070001800502a21480c00e027150398080090000800d82050b0003524000c00000c405840c840303807031380544000740e040380c51102045107801500064440340f803d0f150306194026550b886600721510106810f0314401a040c20b140401008104882c4e0b9010a4505c2603850454600d94821420500e040182c080d5801420a40c1e281485c8441041a07028a009003580f09400078002081d01142c1c9204032000d4800e0320405040b452200c3d104803c00307a002c042c206059060004500340c032614042401c5504071070b114500310f5034480a000c00700c02c109505511050752614186030303031888200c440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 583839199 1250 583837949 583837963
    0x606010c0f0311010e0a0314030601020d08090c04060b030a05062422060f0f0810090903021516020c0307080d05031306090f061112060120010203010906030209090f 72
    0x6411907904558003030815200c1d0112151102d01d0314024800240300912080d1120700310071003180440c0c1b4480500c05403442900c2074a1180e00b050b00689165101000c00392584000101098024001c0b0603152075151790714410900540604144540c80b0700c1e008124100701c402c040c0c005071040003821b905003604c14521441320b0a040e1200040f584903000340d000b110298042c02c08051801015910100f0810b500280b07007035024071581da6200f122044100c00703903200c0c0015903610b0007819480c0c8080c40510030340c3d0080c1e60524428811a113181c80a8202d400000006076106206610400e14401c00c0f0380d81040780c00c10b60345045020b49515448c010046595102141c4900140700011000941d03030345800d6810400e40c0d07004041800b4104451501c108101e100040c225442468600081b10024501040d998200c844060b852603a03201ca80041d58030342c00035210310701c8c00002241c84a00e001d2082c0003035030082c405500c02140c1076081d07104006e8100070040040010358040c5500a01c00200002c41c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 583840449 1250 583839199 583839203
    0x40c050f10051602030a08030a060e01060816050421120e1e030f250e04021003050901021c02040807060503060d11010903080a0f0e060a050711040f110403050c030606010c 75
    0x2665551081c01080c50740580f03c64042e40c58054102d440c0180078022005501c00c190080b030400819886206076031100300d080c010007000500b0030000818045009802920031503450505900f0181d50308a45040644401c4052600c002d121504604115808051036000100390910303145140705440482d107200c1c4681c00340001c46e84840280c0381309407018445880d02c2c0d4580c030140d17840c1012980300c86440400031072840118507200070b0000340034030140d40d0082c021039005050a0710703401440d008502510b0040d201580d15542082541394821400c2d07404da40c100d20b8020056100c1f80f42c03495a80c100741960b88802c061000c100708001066580c1200c522505501512aa0700c001d040001254190041e0300b0003130060200040a42210b81c0010041882100301c3c0d960f0340482d00c2c41014040503005034014440811030a02c5400300103009214006040314016200007110703502d00302d28006844411084001d6480001380600500c503051003011b144060650041802d42008000200f65841c0c032180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 583841699 1250 583840449 583840457
    0x9020c030f09060c0607020307030206011a120a0f021611060f19030b04050403030f05070c0c063009030f05030f060d08090409061a090103080a03150e0c03040c050f10 73
    0x150201c5603a810f41915604591502190020301d05404040c1d40d07076000301802e40241c030400000080c600d005071801c0503041c440024490a0440c1c1010540d414013002e041d9000c899110412402a0b40852002c0c0c41200c0d054580303204052124200346071030001d5500e015019400411451481c00b45250403145003502d4010400c580700e16840d000c5004000d081615603100d070802052106165041d045120485860302007080745131111601600c4000364140c005040801807081040103d000d000880c115483d0301c0c240c030340420f144e196661854424501c50b210b03125074a03000748007816444031751040c040d41c844c1400b91440c202400741c00700b007107001042c0c00c0c03241c103105210108002450040d80c942c0940900240100d85080c64042c016107116485c001e450811043c44e00d643d468004501c90480c2e0304107455520f82080420220f001c1c0004c101500c01c0c1307070300f00074001807100c0c41310840310311034070400d8005501c0703040c1440c1c10007203803919601080c420103004c00c1e091115511440c00070b038207852900b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 583842949 1250 583841699 583841707
    0x10b0703090b07061512031d01020106120f0b090318040942091509080903071d06040c0503060d020f030f060105090603032508070803160909020c030f 66
    0x28045854203900e4101c8a80e50b2030104003c010424150030079031440f5001d001c0002c04075145c072040802c81c15203500c09000909415031001040203801120395030000c0600c0003099050b21801c04c5c1d4400070f80303072208450320025502c1c4070040c000c1d00080150400701d20310255160059208480e40e907810b0007804039226503030f649081010880f001056504e102039107032072019088405000c03440e0260440d1010090b00003604445401d580780c500c9040c0351a9848209600304055101c41e5a008020b240b070100e03500c210400c080f102035a010802c2c4e9000f04080c14201054078211440d100c2c82c084050b0509000d07e007071551161145400c14152603010406a400d640201c16500014490081420205406004512010b031040201103451416207000b9541750480d922401c0c2810f0ba20b1184d481a032458910060552807802c2e82130310200c0c041806044118141021502c0c3d0a0107640180c5c0c0312004820208a448626500608403500038400c002d01182004000c0c1000c5880f0300c40c081102d491707888001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 583844199 1250 583842949 583842953
    0xf0907201e03180303030c0d0218150d0c0905010f0302090301060504110408150603150403110d0905030c040e060703090203010e0d02030a140a09120f02090f0601090e060603010b07 79
    0x24418031072040c09000802800d03400000d07441e82d10003a800900c0c507000c44820b40003810000200c82c02200c1040d181460515052210f1000390130922415080c0c55140030801e4490b503881c042d17800c410302400c1d0000c1e038a80d00391110b0000c03603030309004200601281e140b0030405603800c500100501d03501d0f81405aa40d0000000003801081d40d50002948285040301c0020700c5601d4501820a0361603960450303284550b0110f4403c4c19110440c0d04650561001070810402081d404103d501b06101c1d007882030800349410340850074440c1c419885c1d400103c81c04020001c620742081049250401034908203d01400300c3c900503140d0800410407001c3c15142e04501c81152401d50152160060b00b4041d00c140300403860000f91284d12420506001640c0442032004060700c41086491084440d110302411504d020034070381d001c4042c80c0099524800000360a0007680307540c0d04041c4109070218030409940b400c02c001400074515074011045401c6500c1c200103541c1c0b2080b04403410350340101e56903a1503513154 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 583845449 1250 583844199 583844203
    0x6070809010b0a060801171c050a05040b071a010e04200a05040e0606030c180f0a091208090f07270608030a02011a090903030a0b12010908090f090720 66
    0xb07401200d800035070610340010241c0d480201981629940400031001c0d405000c521980e4803070800e200319101d100c080d9012882170141004024425250410307600700b9549550b40712842c0c01c8030100365171009040c05010070440b00380381d0041c00b4002c0c0c0c03101c401d16030030651100c07424070403614040e82444003407402540581c1da550700d03420b0003000020010b10180480c00001500c5110a407800c41c020b00c100d0301002417501e0302603408000049075150030419a6100c4a01e10708652015103010320160b5141030840201e1072010788090b55130031644954000e81441c0c0c4406140c0214100d04802d00d400c050750500240c1d8490060514459800c2d1028080c1c210030300302d4200500c01c40d444a1940d100018280000b0f40c0c040d04918244a045205600800300c198140a0600800c0300c900002c0d400c2000080c0040d5134a9002c88503025000e84144040b41c2c04060f00c9084601e60201500c9180d408030317410b185490846000140f0340e100751500710309070030141806003100720f01d8140301100d03d0365001050991001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 583846699 1250 583845449 583845461
    0x1329010207080f010f05060f0d08280f0e0103020306030d05030c09040c090317070c170f190c14060a11010e0a080306100306150e0303040801052508090607080901 71
    0x1001c2c0907542c1c3c800d002c101c894000c3c110008481045414500060b4551901303200b507080c0300742d01801882c42754001d96241445903009131440e4a245c0400210491500b91002d403022004000ea212408803040c15403001e440a4028080c2c14101401042084690784000c2131904408129040a40d00ca81b1840c4d0003c800c0d01494040981040c80c00b10040c64855010404208890207180c0c10903c070b1240f01501986840341500113002c9840c036040810480e2f2140c3c41c910003519850342a114042141e811283c102000d00049503540000c1c560304000344540030b0404402403403081000145100c079100403c0450041f07155444c14801c218004014041d03003904880742107400c0c501541d01c00191803400c99615002034825a00034200c3d4655031607102d0007441140281c980c0c540052030300700580c010464000e1846928079800d400f061000007140300302401158001d6000f5400a40fa0601c2c030202441004240151082040044800d020b080c00c4041005030b00700155203044881075135501c40280c05001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 583847949 1250 583846699 583846709
    0x50304140d021c0c060926070507050904050312010f0f090e10091b030609030305090a0f1103031b0d030b03060f010303120b060c0a0309080a020a12050f0304141329010207 75
    0x418a61b00008010356401006669046080d40b48400c085003441c040c5180244003008240381e008030010f000703c2c600740c045e50b58040c0c0f14808882c5842c80400c4c2c4040e0740e041c00e82c00308a1840b802002444042d00c40803552019065484081182c0d8040c10901542d509594149e09442950b07074112806000101ca40303100203018a103541d40c0101e0743d074900b4800030031000c1c03810b50000b86003c021882000e008905080c800d40c200501b03980400050700d0740284003043c02d0684d0780c0341c8800c02c1a07040320743c4954054058403d007a0094484551203880c00747c15a0780d5407404922942200040201c41600641030034192905450310040c840ca103c0c50b0200242001d04540c1c0d4407030000300d01c40192000c0084c07404c1c483d43c42a61580c2d08959520415507440e401030304000e5010300302032002d21124a0b4100315800e2603000c1c0045a9030407983c40301c802d003903034043e4103ca0301520008501d83c2407400d255040900d800103904d810000a0804880e5018034200c0b0074403103c02251803807110304160720070800c200140c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 583849199 1250 583847949 583847951
    0x130b030c190504080c010c110919181106070308010612090f050307030e0f03071703120403182102040b040e10141006021513050706050304140d021c0c06 67
    0x1000d44040584143c003c2d20914105105044031455154425011483e03210340c8106030351000381450040007030480000301140882413800444036a2402940510001240e919081000c181c40a0030300004403030302d401c0c040340540c0341023180d1000241e20508031030440d14940382180302c0c00d00301d8274000d002d0500c411014241c502a003030a0814030038044020803a0320b10984031180540280c13414400080b00401e00c02e541174002503020401c600302500c294107400c6000c070503246010720f02c02140c111a141542c0c1a0005407400b80c2c401c809500300800d050184c84a441528201500d555501d0740c1a02c10000080c0078039160743d40071042c1d45840e001002042964410745413610000d110b10001840b14024250241038800085442101400d610409680c0c86c1e6018100e0301690040082d19081c001e40001d501e081d200c1002008030300d0070300c200f901420b903a070384607982c03070510341004100703514008125403890308940009c05c55260005410307845810410b1311013044080d03150058130b080c032903080084c10503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 583850449 1250 583849199 583849237
    0xf0301120f08030c1803010e0d0516080a0207031703060f01141c0b0406060804110d14060a1b0e0d0209071101050c0726030c1312030306080601060203130b030c 70
    0x34aa488060545000d8418400321003c2c5c0ca0001c25003616403962a18080b41c0201c0e541001040c401c500400156071105c80801104ca0190740e0500640e1100783d9400068124090501c20000103040c1684409a108000ca007142003480005800081038040705d41400301e030f103940c00c0c035005200090300e50000d15541501200594040c0d00000782c40061549031240703141c8031000c680310307010380506030280341c1007006804c401d0066070500c80329410303605041e180000100c2014500710ba042019030310540b020b41b00800d40551000c2c610750781400e4480c009080c05400e950f040182c1e212030b1a160382191701190211495158100103469000301201884150f5080804004071011010000c14886101e250311100c81c56003088040070b00c01510950f030342c0a207010008900d0840303054019291205a21190a0322541c0d246220040c4001e2000c1c1100403e03101e020403c0000c40610180d8010700a60028514003a6101e60405041f1000e004929080c8004030200306d50303180250980e092120031109000d0a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 583851699 1250 583850449 583850461
    0x9020d0308041101021f090f0c0308130e0103081603091e030507060203030c07061a0405130605071d040f06050a0e09010608070f06030b0d15020a11030f0301120f0803 73
    0x2003104039010b42d0a00000e203c0c0040651000503079419501e03a920b401c55880002c1a00503000d44100e0800b42d60b07410f002440e03040400c06601e45c2e4002944100300b81035440c0c1d454119840281c00c00d51000d0080100c0c44010000704010708112800003101c0d071180c40c001e04c000e00d4240d0302d001480c1c1005405004220004103030301000c040e124180d07401902100c2095982c0d000890b524070048681d098142c2090150000184c1c5540000a10070240e2440c58804141440410110b40b0100c840c0002c55010040803814000c062003a55040341807460140f00c0c6081020340e60b4003801c1080900d5000c1c0b585c0750f003116142450790f030068010b420700804120340749036124502c84088100351520b40980d481d1010016556a0001c1c41d0800c80d4410032101000e0791502c1d4040c1c0040c505d0400da5038120084055420001d13000000ca4518030844040051f101d100302d42000380360002003459860607a108100070384000100e038096034119005030b8a08580b400c46e502d0981c103800d4a09100400c803000100034020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 583852949 1250 583851699 583851707
    0x8100819060f05012607080114042a1406131509060f02060412020f0f0304080c090f04020910150507060c0f09170304080f06010617041a040609020d03 66
    0x103a841e0096805222584107111454200c1c2c00a01c60704090030341c0c003080c601c0703155003020003025418407550a03298103a07642c003d200d003516540b101100309801403500308010800c9043d07035402c0070940c00031032171f10b07007410f440e5080c00303c40581c00703000381d040720f001f000030070300d50b559002c4901d281608040340e00f1181d82c80c050040c40411800807040454950784001c69043c0c03003003001c4507190703c035540100555129620741c00403044c11403907640c5c01c40c0100303143e9414501c010001604468502c600641c2d070746180446881c1460b00b20f03100c96103c0d08060f803d0001d000f2580c4201600140c0403502d041282d216280301d140c07000200d90000c0310100b900204030303001c59045406000700500480c4140404031141900702c07650a890302690020810400003840025002c1800e4100100791034100d0389441e48a2042625200d80381070b02d0499540000e006100344c0d81d00c9100e1440b0710070514400e104504080d41d444640c1c4030704141241c3c0b0000d00710009010712000b600a562095000b8018800210702400d00030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 583854199 1250 583852949 583852993
    0x180f01180201081b09012d090303080c04050a03080c0a0c0e09100e030d150f0b03090d0c1a090c0a0305010c0816021e150c1803011b081008 61
    0x82d011480003000108002480d004d04203030300c10320101e0a03181c84694001903d00c51200300700c03089480104070410102413102000310120304a10749880f11086d1a40c64000d19a0304000c0107020800000d100400c00c60704d940d1407900550398001403a42d1505400c1d0469841c11911130301c017910010307000200281207407000c00210b01400700b01055460505d0140c00ca60195009951004081d0b03008000c1c844950700d241d80442411007005c11100b42d035959520740700468030740303903044240088400424070030f070450200000000100076003000c034003140140d2210065114001900d040c1070f03241c070700092101c100034000d40e01318200045c403d038000754407428200e00034010000307201c0108014402013400c21885910a030401c9201e80d000b01040b0b40c601c1c1c1036080301801000d50320100c0c031901d10380601300510342c61503e108811035048152546224007564a10030802c945040c02a403501000240c1e0500003c5a10690b66550902529940b103620450302007030f2243e030010b030780390043e90a1182035115107c414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 583855449 1250 583854199 583854203
    0x1b010b040209240d2d0204050904150b060a0e18040807120e0d1103010f05100b0d02070605090330180c040912090b1c0b031204091b020a0308180f0118 66
    0x101d05c2200e154034101248a213006d040e44c80140c42002500141c801c01d28000c01400d81440402c2d07000514002c00c034a80c200d80d0741100850003611660b280c50621210700b01c1608001d0054003c07504141c0c450034084d21489034007604070008032109114060045002d110f03d00030240010355110001c0c14064034039a0800c203018803950802c140b1480581c00b07401041c1c051800e242803000b040f4a80203c00c400d0354010301104141c9074080c040000400c40e10300c141807141c1401c0e0b01840c0d41e81100e40030840700c1c00c0c00580750070041807500079980100f088045542d500511061904c240005002440c515081030b00b00c140354491300f8640c40300700700600704c032800000d00034030303120140c0e015140d10340000180540c40c03048003804041e400c0004400b515411610310080d001e030076110f090030100000c040c1a030040c0c110715212034407441010b03256110080c440300341e298103101801701d00f182580d004000d1603024000aa0040f040c0145285a410901050001880c4031000700030800b03c0107107900c2441c2c0b0b800d0007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583856699 1250 583855449 583855511
    0x9021c080406031b12020a111b030c011106130f0b070c0308070c0201020a020d020414041b1d0f2203020f0d020d020604170706021b010b040209240d 65
    0x144e401d20010180702aa98184241c54010b004030351822110000c0d0003042182c030820151f0141301700d00601c144070b0140303c4200c1c035003102c1c500d00070030f030500d490202447c0025042004d40c0001900419020aa917900002000c1200b20200c042d418194540f650408003d0244030030301c800c0c401c5050f0001c100c000c12920a4071400712584d5840e03010740c0c030a181840083d02580218004e20018a4690303500c801c0d4070720007400020b0000f26009038a001c81d408460449900760a206401d0041840340c01c1d000040c280c25000b81c01125030b566490829810241c2030b1076217160a84041a40101c0641003034170f20301c000d429012580c841c1c9050007035560201440d49a014080c0e0000a0a028404a550080c41c91250010007003a1100e554609440100510740200f00b5400c0c00400001a8140010318421200307451045110f08090100c42c01c41c2c4c01d0030b80c014401c80c4104011b0b1a95220040d61001406190098082e4198070a0200045100d40c886c0c0d03811403450080d002c000b910f0b60b1064031800b030318440c0b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 583857949 1250 583856699 583856711
    0x90b0607150c110705060d09050f0a050d02010605091e040203070302030105070c0201080105030606210313031101031d060c1c090606030507270203060f040e01050a1113060309021c08040603 83
    0x26143d5164441c501500d50840001c12586419502940003411040e00c40c03412142d00c00b5514140a08040c04d01404550766003243d0032815001303909005141c05828201c0781a219420303c610b568052240390b0003041c04480c02c00d40003800303540c2c05009070402541c01400030320051600e000006d02d021503510040380401d0442c030020540b0b05000400f00d00c18007000d0440d00660b0f1640c0e42c1031589030080001705040307100800824900c001d150700220011481a000022060040000542503480c0090902031444150140c0b6070000d00005105412215162443d50744a13051624082c010603024405182c00d810300030024200016039102030b045030300500135182440d45a41c0081ca19050a0440c04900c0c1380f82810002c0c22000c0360300854104100420f8400140c01d8440401d02b900d41d107480390065170750344000b003001000c0e0b140115030401262203001e600d0030f000007520144001c6140102c004241d551800e90046440e22180c0310168540602c1007040036041d854000301d02c2d800360040c040020700b800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 583859199 1250 583857949 583857977
    0x90c0806030a08070c0f030b0109050705090a050910030605180d0f021b010e030a120905010302040f0b0d0b0a0b07021003020c1905120c1006080a0c090b0607150c 71
    0x868054020100203028108a00580e1100c0b41c468104240a5032200d80040300000d40b803a00700a0340004500c00e981d00001c83d81340200000450f07200a0821003401410480c1809035a60482d509051780c1c03007192101c1c141d45450b05040b100080c0d81c0c00050409280005000070310040701440c1c559502000c0c210360503071450100c103ca60000c440300040140c2e022000000702101001215509040103140241c0ba106034100000d15000150900317440c010001d030309208041e03034081d070304030301500e428201075142510f0580e0b22200c5010611070394030602004a80300c450f41005421458460000801d4074003000d44990600c1075a81c4480030803445003060741c950755111400f0b802075a10204146002e001592900d0100d84007080d9048800c4450780200816018100207407805000802040f000800a41c2c000c0f144080440d2260340080000c0e5100341c07864000036084540300b0096400344c50001c070701c03d800a801328002e80103400004003110503240050340308140c1548072604052495491410b042d02c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 583860449 1250 583859199 583859207
    0x519050406090b03040224030703060b03100e090a0813210f1101270501022b260f061f0906030c11071205060901060f05011d0d0c090c 59
    0x103100703403004501c4001040001c1a031940146a0050000d001403e002c488210148013580040c00d1202c0000e03404007d0000441e45442a1000317403d0a005181c0746091040e4068100d00ca03500c501a41c010480000500010040c01501c1000c1e5200f0f11840d160050007032a0a62042140a0074540203200d1100c0400b0712021000d1118958011185026503034031902d41c0303620240d0b0081c03c10305000c0508400c0d151b034242903c11044001c568129010f9150400000900f8000030b0544030001241c000f120896252203400d40102030417141c10f040150001c154801c280812130030031f0102204d076070f420410012103c614422482002d0890f001000e0040d10030b04001a42070138942ca80028040c0308003030005c140030341e000e4801c20b00309040020740e450b11409031a191011a4000751949947c1000c16010031104102860700003140c04002d02c80242010b14038065000c0d98441c00e410070080251b1182d4140150365407800f070b44c5028150500c0d410840c00c5c08685a4043d22039140c5061a14848501c5140300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 583861699 1250 583860449 583860457
    0x2c0910030b130f030e0103200c07080105150d030c200109240f090302091302090c0a020a2925030e12070c050307092403030f0804050319051905 63
    0x8091071002000c2d01c962400c48803580b00b107040c5070516070f80c8c1e04020350452207030200c01422080d06565541e00d450000c04075082480c01e0703200554581c104014400c10004a546034403c00409650007000400b2a00b0300712404468841d028010541d9802e0007644080c03502500d4402c105d00307032201e020b101c1d03849042c2c11585502c800c0541c000611000d08042803031040741001c01102d41843d01c0c2d400c0c01d032203400084005030281e40c04042d0308013005050085080101003594080c0c24840242c0c10f040b2092000703510b0300c0000b440100b071040c17481429a10003140d85003482c4103503600ba4040c07001c0d28144910400700b61200b410b4000e11162010706014940c42409001e02a2002001402c0707210721400700710140d80c01c1810110740e0062840300215980c2c07002c02000c030080100c00e10215411b4084c2e039414040210110510421220001c070610200b600080140d140c01039516000007213a445007800c60460080c0494042400c01c1c180d03203d02c80560040c05000c0c0d89010118207034900c1101e0340203a40c0f6102e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 583862949 1250 583861699 583861703
    0xb0a02070303021c1718010f05010503010b0105041a0c0a06050a0506030708070b04060c0c0803160c0b070c0b03060d0203010c050915030f070c03110601030305070b07030c2c0910030b13 81
    0xc065100d444100c410042403682014840c506d4117441161250000d082d1a120018510303d5079554004101502d024058040d600e003007800d1103444c0500740101148020484048598800400070704138010380f1080181074400c94110904101c40d0030440c030918040c14095030341d00d109100b8503001181c1c0309808200300089501402c0064031f0302c1d14082013910f510550480c10744500411801c0021002cad400d10040c0407440001c50550f20240d0b81e17280103050040180c01c100c605940c148901d03000244c1d0010303400c060b101c11145081d125654180010102d40070008020741650a04060b031010365008006070a5486049440c00e19540020340c186c2003e01040322403001c00303007a4034081844980a0b404690a06000c0d190281c4511185a02c0910f085400c1c0c0c41280007810008000090180c18415943c21414502c0c0031710198040e035400418080d143c03c0c80c03510791000c41d540c4080001c00050b081000c00000b401c41d02044c54603040501803080c00340300944000860500044942c1c104c1765020030419 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 583864199 1250 583862949 583862957
    0x10e0d0f0b10330f020709050702151501080402150702030106030809030111160212030d0c0c0c0602010213090203150d0602070209090a0f080d0b06070507060e010c080405040b06040b0a02070303021c 87
    0x80031402c01101d0480c59138a203041580280341c00410302d05000e0007540d101d014103400074200d0901800500d009500c0003429005514400c503090710751a0381c040d5440d50880d4044a904007400c0703030b00180c040648a0032400035407642ca80040001004002070281041e41002c0b4005c00051218000200492007800040105100810540c00061400441003010b1076400c000300d0303003031a071912403030740c100c8906103984400318000c80400300402040e00184c4000d061188000d40c00c108810a0756030001a50340608030303c2a03004000a16034810960329154031030303030040c01009000f44904084000350300541042e401041ca42c030005900700fa0000301d44030b01c2c0342d00082c044080c50690300c580200c2d800c41035200060a44030000340b03a26907070700d50180c05220302801c042d1a0044c5000c20240102041e07201e0203041c0000301c0c10780c1c0c0201d1030000995040350350946001c500050040c4c0000c8075403040d0381045c0c48d500070100e18a04144c1c0d001070740c06d0070350b0310035005c4882d024601880f480714803000c040014005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 583865449 1250 583864199 583864289
    0x109060f14090a140103050601030b100303051812070e04210518040f0e0f010f11040b16020405131406060d120e0307080d0e040506010e0d0f0b10 64
    0x6042c05901d082d07200b4101c07031001404c1c0e06071582c3d2481c1c0140a920549440c1e1008006106010f0054502c58010400c041c410800d00e1440d40c0142440c001c40d4844801099001c00c00306503034940d400070701402c40300380c825142002d488140702c1c2d002e0a8280c0c0d05907802d45080000300c0410300f20403140001c00c1c03142d455050078901ca02031001021030416000d00c2d0030607158800f10303140c240f01c0c0c004c00004452400261a450f00c107040c1e52421501d008168064950500c0086111001060112170580e030a00308a580c0c1c0311030020210141a8030303005c0094009260500301701001c01820300040c0030030304c202d40c840d105c4000101007603034420051380ca240c0d2014502281100248044440304454002410044440c0102d1400241000d540340d016250380e070844015101659402540b90f01c240c0e104960800580c140748000030000c20009c1002c80c05500600e2009003480860511401c0c1540e010340820014030308034100141404580c807622100c84190b44000300c11280300700442680c04541c031128030b08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 583866699 1250 583865449 583865489
    0x180a050a1503231504090c05060a0306031205040503070e1e130203060103080a03060611031204050f060901091403120c030c1210080c0a0305100c030b04140109060f 72
    0x984050003001c0080c940e9411a601c24058150103003011074440e44480111490100000f54240c0ca0401603c1e208518000344500068490a00d560544405440140c2c0b06d051f05102503006100940001d410700f5024111440d410b68070000404c2074940503401c0d030700240c1d030701ca02c80b030390002041d00d1005c50452401c1d41e4100e1a24601c04640c1c1c80142240050756080381d039000300e42401000c2e0010303500410000340c604032203505070141000900d807034500200c000f100e0901d250740f02e02940301200d84686030400858188501000800c40103040d40301916402d05110190030f0081038081d0003122002d80580034021310340408403d84400c9050360440541c1d82e51140420089c50f4070050114440040034004103006c007040c4000d403031003654801c1c00084030b141803940d0107207002a5884c4040c07081b0034600c0309000088000c900c0c40c0707200003c20001300350f030200b440e800c1e00070700880760b60307c4c1d001881c01441c4080c807401030380e00c98121a1030710010450700ba15441b10a000e1002801400000c020b24419070301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 583867949 1250 583866699 583866719
    0xc1902030f060903091302070206070c0609050a06120209011e050a0906050903190201111f06050a05010c11031c020105040c0b030705090f0d0c0314010c0c020d060509150903180a050a 80
    0x5251b1210800040c5450616030010f051703600b0201055600030f41c2150180700050300b08100070007802007120f9001909183c03007030040c00904001a01f0100a4020032440da1990188260b1a01585400c3e450f0040100900005180d500010460750006e00640c00c0000c505020300c0c100c4072030b040058060151035a500ea136038500702c5003212080b070403c0f04101000071440c906001020100040322441e02e2580040f0301d81070244c401030f07040b05105181d060b80030845e607038200380231005299200c1008541c9906031000281000c100402c010601c090390082d0080d0280d065118174801ca100e0300403000090b4031100d5020031400200d40010105508200407a000c2c40c11803407400d00040005c0246c0381070036540d40c0e40f9070360b805a980101d50024020313180c5038103a40b0a0194034145121807804024005407900001c508455410024285d146d650021581801c0d00780800340c400354501c1041d1145082c0345c0036040d600c0c0e00c000e1140190b0180450050300c00e1500980460869200a0117a12704a0a0400d811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 583869199 1250 583867949 583867969
    0x503090111072d0c0f090609020a020c0108130b2706060102060711120d1409060f04060f02190207050a06050f12130501090f060c0e0d0b0a020c1902030f06090309 71
    0x83c885640e519444000640d807441c0e4407000d884030880c00a1800d140c079501405070b8800b50000c00c82c2c64011311282055607030010b40154107070340c01d10380410b654075140910140300007080000341900c0084020004420410030030b05003040600c1d0000105090001d801944484043e2080d500581044010a00880c46200c1042420807803101340e4028085103881e1004a0b4080e80300f0810007501c442d00f808940512018441e0b210041c1c2c009007070141341c842031791460703501d00500c0140203e690312800c50021607a031341500c51941c060f81140000d50105500a0754402441c454030b44a0a004200801c5051141c020b0390a90010300103924104103540b8a1044200c00041088614003000e20380100840e030240101c1400c18081c02c400c5044002600b00308058418034008881031185032401c000a5803546044180010340040198200b40c440d606284060710800441100900c54102841c21110060301084910740c4200c089558120203941000d0300c45004692000b0650001d0103841000c0c10000100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 583870449 1250 583869199 583869263
    0xf040201052a0706080c040810020d1b1106010504060308120702211309020f0714010b0d050c030601090b0603040b10050402040914091209130609020703050309011107 73
    0x2100b1100501c03401069420642d1800901903100401c1003200503001866180c05c81084001e00d80740c9400c0280031a070311814030020807200d903400a946480c0b00e0099018054805003942030007211030001c20b004242c11803072190503615008400c0001110715140c41110112039104120a04009403901c413426050401410302c02903004102e0244880304001c003c04002e03c8000d0070f500d032201400e0500880656442d048034118502c100144e6081c10103a100342c071040c48d8000c2c0d21004414208540902411000441c3c903040300480141808114012900c3c05c5001d0701502115a1030780d0342c1005030140c4100300307034071034010208001180104e18070070301d01e42d8003c1000c1d8102d001640d84d9800308040343e00c44d901c03e003541a035810341da0180c00c0702c00071095080b492002c0244003481e09144140076a110b04c5149500ca02d00703c007a008d600d0220798101e1030050402d400c003191a85520708001d40b4540c011100d82c0815480d000c171040c030070203038441070700c02064100b0f114a40710180c10403030030f11441d02c401c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 583871699 1250 583870449 583870477
    0x5030402060c0d08150409083a0212060603010b1b1c03050414210a0e1503040213110403060c030213140f01110c0103050402060415020c090a050f04020105 68
    0x120112490104002d01c10900566103d00c25803174032202c80c564040d003074800584940e08040b17008003c11485001da500728444000855201000d5054180b4000e90a5500341c0014020400864520300c2a6015050b401c803100c076800c501b6580c0e1030812060344800d000b1000b42c80e41c28080c0c5070303003444032400494002604030116520900ca0140d100521504600940300290300c590810081111155401860740b44074001864150b110707071420302c02000b114001c0944000c021a40c0c06c06184942940c2d02c0c1000003900c02d56400100720b41084096008440a90082010b03500300c00e0b86d40060700c43d0072081c41d02100d850742401d086558010190003c95201000c1503024008041440c0a040c0c21500800a9003540914205400d0901200d200c0301304001e81402b100220b401d4138942c02103901c5a80040034030340025182d07518030016040f402030340c0083c1240c401d800a03050046400150441d001c1d131086480e040169034002c0304d04150f030001c5800120700c1c6ca405011600550041c400b408a8085101e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 583872949 1250 583871699 583871707
    0x8191205040f1202040b120c060309070b0408150903040b090d060f021309290d03110d030204060201051005061c110a120b06161b0f06120c09150503040206 68
    0x1052800d04036043d04400c102c0c00c5894007200c11490319105a00710380b0070075294511034524480d003050300c0d0041004502d002c1c1d41c0000c00590807180c148103d2000c0c080c0c021440b600d49859002c001c3d5a44540341ca00940c45410b10040707625100c0020a4504842024490310309c0d200303011050140701d001e0031100f201c503e0340f40c0000320724102d038500140c428000003842d80289a890140d80c0030a071541c4172005181c8040d1111014034003820450100c00c90102900c4c56455080030303140c105d41d52400e01c3c1c040002c50094803041d60031070344e1540040088031b20300da0007802580c07662600142d8054041c80f8160784201c1c10000003007081550007030104244950f1000183d4291036400c070b203515922617012200050a0064158100007240c0b168040082003610083c0c10b01040040f5600e40c80350f8014003034900d141017240e03449885101c01102000e403251002a41ca00d43c2d4503600a841000d21202c0512054284040540131900c00c58a140448a4046210450741c2801c0c1094405510150040c0c3e04000104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 583874199 1250 583872949 583872959
    0x31801030603080d15150e01080a1a0f180408120c0406050a030509070312031e0621080c010c1d01080705090409030e270109050114010f020a0c030b060a0819120504 72
    0x15001c40b0b43d00c031038079100c090780001000100b2705400189228040c0c0e280c0883c1601e000107010b10700310710450940d0483c0e0500c81c01d50015101c030f02c8442a081191403204200420041480c011b4546481800600c00b20350302c0d640006030041c001c9029450000310306000c490302081c170a80201c2c4d00b24441038103a80340e540d240c2c0c03101440480b98041090229403128503030740c1a1020140e44003011010340c0300404c5151b041440c1c1290345000200034004410008140000744a44501102c2d9410320410007009440340103d400f601c403129800c1554083c0745000405402d6500405c002881240316a48040c035160381c40e000c01005201c5d0030000d030100140790340c07006801d4540b08001c101010030201844052511a800016550700507000074220b5414076004001c40e090b218000c40c99000c09081c00102c154044030100c0c039241d1202c1c4044c1c01d40a002d0400000c1c002c94100b102e015001c20740702001c40740e071101c140d103584072070245011540e0b100303082003000400c440000c03810f040d081c24a40b8502e4207990b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 583875449 1250 583874199 583874219
    0x90f1119060908210d090201051303050105010f0602160e070c0507030b01050a150e0105070201030e0115090e0d090e040812010b0307181203031a1002031801030603080d15 75
    0x660080303070106801031400d100c108400c00c01c540580004030fa07507461241061a260740603024609400b070f01641c895541d401160f000b2415503040421968100c050541d890400394081c1c0000c1c070590f950080418404101184003103101289441d0115213580030b54030b04900c04801503002403400c820849400c030704d84001b03002400703444001d5028401400d480c1d41844100199904240d01c0820420305022070602d0031500b11002004154090030202e40322030450005030040d003a120b0b0014415441c0500c00141c81005074108400c0d940c26a404010f209002d200032559030b003149844001207040c1c00300800c07110880c22511584288103401160078031145081001c80031400381c00401c4114008000c02c40035550207215001c20990032104151040d1506068594080800e0310103010140c8540300410070350402048951a0800908400c00e003204019000b510781c0c021103460080c44660b001c0c0348000f584a8003820742940d1700503079428609aa000740f084001c0c88000100d812540c003e10000900d41c4d10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 583876699 1250 583875449 583875499
    0x20f0f030c0402121015080f060a0b0a0302030415020c0c04020c0c030303090724050307030902121f0f11030117070306060b0301151d0f03030702030307060b13090f11 73
    0x7400c0b280029410844d0031540365000c241c02081002ca01300000340d880c258481c0c81c89030042e0070348d103901825403104d40c0810f02c02545500800340c20400040c1441d100d030750660041d0310850140d40310006030a00d5044c003000341c1c4200014101b5a45c40400c032201d40345416070061003003a4007001100c016044c0d11010074159001104c00c03a0031600541c500f0403c40c0c4400b0100c4141151200450484440c150f80261003400040e05010416644010500840d1910f5141000d1720381d02008540390316080700e400c1030584a030044050040c608141d58001c0400080c0542a40c2e0701c407400718181107a09014038012601c2c0c2400140a0714441d80000101145c0544a00005440e0b40401c40b40c1c0c0358145040c00400d40410b0704014200500721941d844100d00d0000341c4c0100c02c00854040040340c9c984000240366004070301c006541030100080d650100312046d80301c408407807002d41d00f21550100010724203088400d81c46014141182d4454100009482b04940c0203400800814500c00c44036030038407004814070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 583877949 1250 583876699 583876717
    0x60312040504240f0e16050a0309050a3002070f030f0221010603140a050606120a0b010b03070f080403140d1e0f0b04150302060f190909050c0304020f0f030c0402 71
    0x50a080c2840501d690301c0c501903000103900c0c01b0710740003106440003d003079100e11180e40c010159a0300c1c01d2020400b040c401d4540761a00204840c00311004515074150110002440e0401001500004803804d4004a81d21046400c0c095031440f04600d1520380d05400500280c7c04c036446811441502902640c4500802d0207042d407000001c1e41c2811864070f005440904194105a54003108281d0001500011100d5108000340c1c1c00072200d00030503200d18a401c000d182c0003001d031070b0190700105464484e80050351103003803d03030344606500f115000c0940e40f1820980e00540062003c445044144080d000100380c401300c46100010540c100700c208410403c21401c8084d40e40791070704800d4580c8603d5000c1c03a60f103003008480412841a81c2c040404140c503141c440280110004100720301820f0340202601e0501d0060342d01110070301c07000d1030300500b00b10442c001c41d5465032078007001c1a41100d0b40f0050328840d5a018261007400d001c10b10800803032680381600994180b05541d8407580726110780c005031103540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 583879199 1250 583877949 583877969
    0x3230102160803040209071e121d1c08010602060708060a2d05030c030c040b0604031712011e140f1c0b0105030a02090c1e160b06031204050424 63
    0x8201481044154000a0000c0d800c01034080205000050000040840d0b0f102a00f0809e01c141c1d946a0560701509104001314281403101203000301c81f06008c50740302050b45003484050700010000400340d504100a00440005030700030000110b0a60082c00c509070004d00040008440710303680c490f00a0b2121003086070380048508a111004164100b1410801070402203004d0002d040f031303441c08079582d140750f144a20322030303a20b8000d06140d54844800302e9024541200310480c0d401c5241040300303440c0d844901100f42c8020b54500000302403c42c44140c0c0e03190516888501c4c0c41c130b4502036507604011507450030b00340d2005004102c07a2440d5225552100b0000802c4840c1c002610203050807004840c050340000c0c001e4001501c0380c8010703540c140b04143d100e400c0c0042e554461400c0322a50005d6105034400ca440030200241804100c03014104402246105200c04429503881c2c00c01e140e110100b03059058003410041c0030a000e40d00d05034028016030b100c045c0412110041080101a2030034099006410300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 583880449 1250 583879199 583879201
    0xf060203070917120f0a03060e1303021204060207120204230601031d0601120f05151009180b1e04060207020a0b030f0a0c0e030f01061e03230102160803 67
    0x9180c1c2d5080951025011901518001e446a000d0581394414881c20b400034900c0015500419402030740000040d125001e0302110900c0c240c2400c2e00c03421b10444064000d072040e80740e0103c12005600842d800c1d1440746d805060003500e05407a000c00100e0803401240d0058032080c50110031080b0b103482d8101d0990700d440310b03006400c0c920000341c2161200c111060710b440d44007a480800100c0040d61a0443e00025a41c904074111410030042004141e1002005801086114003294501c040c4880c0280028080c00f0082941c5200e910200d8150b90040f8002140256175680480c0c0352340302d41a40071000c0c2408401145441c1a80600c1600c12517044a1455003c901c1e1000e40c107000507030001a1520500e21450b50038800705241801400400c081c1809071950301c2e145400d8405c968540d0000720240c210b6000c2e00e45102200d000e401d041c0030710001401d5004445c220b40c18119680c0341281c2d00f007400000e10840140ca6200b40c0620384a61150964003008000b0020150314540d44545001d95007050312 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 583881699 1250 583880449 583880459
    0x60705010b1201110306090604020c030a0c0b061c020114041e031202010501080325020a03140606031b0103270302073b0703060308130305071a12040f0602030709 71
    0x1441d9010708001510303890002680c031302001134000c41e9041081220905001d54a61000801a200d0351110100fa8040800d694680b2a04080d134140064811f258115550351404103101c003070040742c4003600315107408810100141d40107440300c2682c0d00a848240d8030301500c1d40b140000e0107110070f608034011300000d0b0080041c00004150708401c202c241c40203001c0c5500d411071080d601d01500741c03038000d030003141c20b40c03100c07001c01505a02401540c084c118015141d41ea007819072180703502880c40c0200b07004040c0000c0c09031a010800d4400100c0b41661540000f0148e0011401040101450a1f441b0b800d4042d815914400c114600b001d148680e00801c902c50400c40304403071451207510307003102c00c04403040b821400c100f07190000344801c640e08034440b90750341da00c1c4001c6001e001039520207071403004002801d05450810240110580c1e001300201c580d1030344d80e43d00200400342c850070201403206051008004180070140e40d160024003400129140340540d40700e000c105c0e40240c40403030224004003401c201e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 583882949 1250 583881699 583881709
    0x90c0503030313151401030201140c1c0f11190c080a12170c37031a0105090904020f0303040e0a0207020f060703170912191b210509060705010b 63
    0x41c00701132503030040c4030010030b940c0d40d001d2150042c0402410310040100842a40c1d00e1a020f0b0b802c143c02002c21110720102e04510030b00300800e040810400145500d103400d403018041c40354101c1003000c000003050181848800f07200314a03c4064102c50242030550f001910301000c11031150303020b006000305c1d4019201104003a0400b844040d1080c110004a020880320300c80780c90030b07607950348a180d0308a01000160307a400300010380154102074408002c41c0d00740c000140c1c19801603124030410420807642d60300260066405000f4480b61986c040300801c009001818020142910508040c088a04160702c408603807001000484c1c2c49021941c1c045245015441c08000c90740740204151849450700e6801d480003044c00a8440e03441c00100f20344404038140e80340410002420158800103284c5501d8212000f09501904c0d00e80c190024151141e4010141000141050b1700c0780d002d0900c4545102d080c0c0034081c600f485031950001d120f4184803505c8152110401401d0545c0b0030720000034207581c1c1c101008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 583884199 1250 583882949 583882973
    0xf0819060306090b1033050c0f0d03150503120d090c090506030c01030b03060610180306150b03101a131517060f040e03040506040e100504090206030604090c0503030313 74
    0x15a89004050103001400c4640d071469414029000f501d0314003451820a87c2c080c82a02d90a140034403410342480d19a4001080c3d24180f206159424007901401091010502c105030040e0350381030700044040c8080d80740181c000c26031145110000f04d05495503841d03020350022194489200c942e1103d04004507032409000381c0c5142d0100b400c0c1040b02c40b0f10003020039900d40700240389502469110100030038a0b4080c02e400b83ca43c1c107502600d40101d50300c4e49060030240070000081103042580b8400421100c9036142668403807012410f0341c0641d1850a00051540000054000202c4408106084030340c00c55031000400b800034031603d5a41d0500d0900014a18540061803000b003040c00c03018031110341c0d80c07100c070244010000c039000b190315512402014114411548561340c419400600007941003030100c8110300c00c4220303400c0214065501e900f804180c4501000003540320004000150b4680341542c403580d0b02d54003c441c11400e03161a034010900d035600540b0114204603044103980c0c100700e41c00c8042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 583885449 1250 583884199 583884209
    0x30a1517010b010207061709010b10050711090f070f0311040603090b0603070303091403031c050919020102072d03030320040815180105070806100f0819060306090b10 73
    0x400314a450b06a0040085000006c031f041c402e002900407810340c5009400c1181c1c42040181642090703c400d1002501c0b03903011150441e04035030078401c0d035686440c0c0800c41d00c4c4034040b41d40001c5070302e42d9082000c03150715040c03034200802e01d03640303100e42100c0e4084500035001030071315a1000110a512418100c6107100004c103101d1103507024120910029a201100078122180320f01c6402d8402031070300010b400c5024900c0c4070360304c100c0481146520503400341c1002d4019001001529611010481188654403150340007a001d0b0348640d42c01c00042c4004000130641307501c0081c44640c08207484c151400f10f2151030b4003e4002a0b107402d03901401d100003805140c045092213080c2c0d0b01c0e091401240d1134079850200940a401c11007400010035a0120601c280502c50702c00c8000c20a610304030a02808403c000c2d5900e41c05024108510781000380030720280d0030a000d480d204d01c24103968140da08180c3d200444601864692580000000100b1074000c4c00d05440c4603280b080b00901e004150719085040941c00703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 583886699 1250 583885449 583885453
    0x3050f0601171605040209030c132403030512060f0d061e06050a09050a02040e0406060905062209030e0607061b050901080406090606150807020d23030a1517010b0102 73
    0xa180c2d401000318100d0340c204c440986015807160328800000e8240020144213540202e4220700740c03240009258044100304405000303699080c1e070407904500b5006030350b0200a0225400b0040d4420b50390319250025804040105240052803592000c6503149113401e0045925030f0b211101a120044803400c0c04011210001080101e07500d00b00025100503924483e0784644d5070b54001065807007031950120f4000d0100d03500002250708051800344000c260700d100c3c40300b44070720344008a1980c4c0f41030500c900c80d01d024000e0007803051480910b030380e00a10010034200c00384180c0500c0c1113072079115103014103162802100001403240807010000d001264907105d0300b00300b140c10081c600a981e002a492900a600150000303402601c914088000b40900c0e0400a010008142e81c60745940d070103284a84181646d50a550108200700c000f82d03102c0d00803c41850104000081010b4000c0b900405540e01c00340c40c10012400c4118040c103240150b0070f0742c122203441a03441c00700e502191000d00401109440a00c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 583887949 1250 583886699 583886713
    0x1110408071a041508101a07020904142e050126011415011d061207020a050703060903020c0904020307051e0a03030207050a15120f0f050702240903030402061303050f060117 76
    0x382040742c810b908e0001d20800c1c17402d002c03401340202d0403d68207082900c6000c0380c80000c0024494000040011a851400f542079698010804101c0c007a090403a211a01d0750b01000041c0a011861554028444205c6641c0d03121201414101c401a40740140c28001610029208070740004152055003c0070303e520079115182c2030540d8854000300e07500e138081526001080d4407040d404034200005220060158803500c007010060000c103501c06420144241c0888511118000c144985408103c4001e541504030300410032007810b00c103032030210b0241c18021074852800030314002407a01d185900146e0041c5d04c004402c0c803490610401c0100548241c0e8050304000b07080c0040141551100d001c8541500d485410803091220380c1d03044600101425a8144a01d14049200a56581020190505501e0005107405000c551251510700a1110501a511350384e036540074410554020348180034006210500000496014044802208524000b511703c3d03500d01026060a90b0304a50031a1007504044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 583889199 1250 583887949 583887989
    0x4290607080a0e150a0306090513030c060509030d1b0e09040b1303090306091203110c0606090c12070c03142b110d06050301110408071a04150810 64
    0x400781d401c00011480c042c03d00b0069200400c3e10000b0f0340e07040141000c07000c141c40c4030703098064200a05942152030108195515981d8100710080d0b001c0014021445c1030003100e0205105030852980400b4100490b03141c01c410300700314412120b203401c856811584110b002090395500ca05801e1070a02c00b26080e00d21418a80c49802da00d20700500f0581c40603c0d074505010815028190a40c011900400b04019101c02d90804e0031010342c0c01290300000900c1e2010442c4c2020100d07040d6400070380300100402659480c00103001c186e01014110f141500c1040c400011041c4c0d8040501d40304003031560310050310810514010348228040e003207400c4512418040d98940b03000304c000a4081004c070f45a810420818441020700500e03503420f0300c5204080c000350002c3d8101068014400302c80041e1300030410284520000541801140100300c240d07080140c2c204103030000540c403130b040d2452a104a40ca0607940e0003488164500d00c1003a0400f084280d4100083c3d04e110302072a00040c4021101d5650801440c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 583890449 1250 583889199 583889213
    0x501050709031e260306150301061d0a030804080a05060c090d03120e01050a091401061a0a0302040b03070c0323031f0305150906090d2c04290607 64
    0x3e0303a21440f05480755103421051040200344115050001007001070765181c0060381e404250b00c1160038a000d1999103400503501c12458007124101d80786982c3d501481520980003110780025244d240c1c0c1d00c040701d040701102041c0c4800c0204002e09500c4014032106040307203001801c060004007412511003060140420648540040c07400b820b915203040e409084981542c08020320034544041410340c03030601040142c000c0c6078801c0070040d00a021007a03034600f440e081d5a003030354041d014400d00034207141d20840054690760302900b000c6170207040141c140303519103001c112141c0007264044006a0001c510405054020312b20001ca205c001e0010031191621119000c4c90b071101400f840301818040440141041030400d030100a9030f8820705840b00850300b14021001e40900795444c50b124042d1070041000b10b500000c0405000103107032104811344051003c041b121032800d0581050100c1030a108200380ea076148900c4001c40015140345885240d01140b02038580540390b143c500502081160f60041000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 583891699 1250 583890449 583890473
    0x9060207031a090102070605160e0d021c0201090e0a0f05130c03080f0405030a14010513030207030201050a170a090c0803040509130c0e0103050c030d03110915091c050105070903 78
    0x800e102d02d400988030304603d6802032142d60800f412851504040c0403044840003048500900b1395510195135102d00b804100540b200308500951001c041500b54060082d403140d161429401410081c42c880d544200e010114602240d000c05802c0c0e40d5521064034900c02d02c2070741d401c200418011441c0c00c1e03da980c3d03600c1411860001130a600804200e068018040c1c8049030080e01010f01651560006c40c07411203410003801c0c0010000d0750070301001039100724048410800d890303015402044001c0c5180c00554641c0d00581503d02000800050003c20f01407421f8000e026108019000491070058105001d01c80340c0c64006106c2900208410456641d071040e035039404c001102c030344901e24200b610b00012b2000765a8800000500d82c0c000000034070a0200d00c045002406405480d10100740440440455103595a900c000032024001e03070385282808814101030040006049207465400c2c40003855041c00401c102030243c240211840400c003080c004c8070341200c050309142d4902810340c1c4c0c5d11141900d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 583892949 1250 583891699 583891733
    0x11418030d050603120d0b180402030703030804170726030108280b01080607030e0106050d0602030402010e1c150204060c080c030d05010e0f071409120a02060d0c0906020703 76
    0x500c03500030a01c5603409001703e907641145180c4142c2d0342c081408001e00507202a00440344a03100c200c0c5c0300420a903000008607c140e900174040c08a007421540e05a0740c4081c0034005036010741d0050b24804081400000406020b40034040340722400c12900000b4285440c00c094045650074188010000c0490001784410051606150041042d1030718a10b40045602c042c0060a2201208000142c0b05c00220302c05000e03401c41eaa0071b000741d010040745182030b40d00c944503881e08980d103011000c0200d1440d6002d190094414035000700b4902d0fa41d0f0004600903801f088000131031a8015003e8200aa9800210320368541400c0c154101846c050015081a51001c13010300480c100250690344004103000701c4e84280c200e4401000300d5611641903126450301110403000e094259004110307158012003089600c0002c2520792407410f10300c08103200d030f41e0032411903d01562182030f810800584e40e482c0600490708402200203401c1e901b0305802070910746150b000078299000280c00784081000c00b081480159 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 583894199 1250 583892949 583892951
    0x906030908090918060901060303050909040809030a12030e0106080705010f140301080a060f022b09061a0a0518040323190201061508010e04080405060c011418030d 72
    0x20103504040180d84207110403154422004803c02980084c08030130180c030454070340c04841c5582d0390303408983e003216041d000c05004940c2c140010030705440c0c80e032810f0781c0c002e02c0b4800d45400c100b8400080780c58001074400880b02801c0d102e00040c20164144a01c140340d200240003030040301d10b031030606900c0b80c40c1070050a04105c110007069003010302401085070614010a5955035035a5191103ca85a0300d007054112011400c020750000d12031064001d494900d91110b00041c0e800c43c0d01340401100044601b003001c2000d0300c0380d2404000c2005403041c0c20141e4584c1e1700e08030a83c20340324200f0242d00300c02c1d04400c0c07040d84070081d224000032900005d1079010b07601d82800e2441c9003103c440c0108180c0546120140d02c0c2000a10b041141e540700510644100c140d002400ba030303900c0f1491a8050101c40c80c0c502c0016a00710f004201408108280302d401601521000d40f4042e15240815520b6101c1e00300c0381d6684c1c5d11984404156100d2448041d400076149403010320841800c0c90003601d0f40700d090f500c1240c40e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 583895449 1250 583894199 583894211
    0x140c03040f0b04050a0b13080327010e010203010509011d0c0a0309060903020a060f0b01020a031d030111030f0703061a2802010e0f03042103050f1314040b01090603 72
    0x10003030103031409a0b00080c00000ca0303d028504030307580f400200001c9840144c0744000c100107042c07481911001c0c03603010510038150354800f0140e0010700c102c11200000e4410311700c8c4519482000b0300c036100d4a1800b5000240e50303981801c081c09880c10b410303804150b44541003404100840c16000202d5046000702c0890f0b960745103000d000314060807542001824451030100601d041680015030441810310404060011a840c1d0301990f0444091040302d07405600511000c0c0006442035210038502517290141107025000c0c04082400c650654008034180354000060000139601e1046d026846030403882c0500101d81000c103d410700f074201200417000e445010400f02c034585019000c010502420000c40100c02c107021000034060100c00c010050140075011140b5a4004e000c01203070144e5a5002c10009158100000300e00c4d02002401e0a4003000000e0040c0c076104c03070f581002080181d25034001090340b6400d0440701840d40c2e019030080c0b48070342c1c81e0503407007500d0340d8000100d0402c0303450505000030a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 583896699 1250 583895449 583895453
    0x16080f0c030f060f1e190c08150607030207091103061815040b1c0303231302010f021e03041409061f0207120804170a05060a0b0f030a0303090213140c0304 68
    0x41075017500e540140c540e00f14100200340520300c07421028000000c00038800100f03400d000761031100095402240d00400070944190a05218009005841c402d10480d030310705940312101d108940c00b99a03000c1042c000041417000902c0d1010000f0075079140307038144842c3e5051170780101e1201e070942e00d042d600454481e20351070443d03a11005140320070444006406241c3c0034525004008100b084000c0d0b174002c3c48480c080c98070040c00081c0c42d20070191640b50044141241d0015600001c1621451003140f00d0f81c100301500402c1c0f000402c1031081000000c607111400c0000d000a5200d190102d540102200410011540c2d5a100c2908108081c0710404032a6489500b040f8140f12442d04010a00c0850065540070000004020011680d40103048003048800180031611050b450320007074055440000828000c4009500285c06420014569411101d010000c00c2c00e10028600039004079680703220143c25800e0110809402008031001002225649941d40c0072040c0050220450702d1000f10000301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 583897949 1250 583896699 583896721
    0x206151804060914070503060f040606030507080d0906110d0f0201020f040e1602070810021614010234170d050c03100603150e0916080f0c030f060f 65
    0x31a001203041468503600d040e0034a14007400100380e0890b040c01c0d1a003039202007080b002c0b4882080d00c0009000d0026070f142c0321002001520047c00583d5943c0c0d88090010010b40c003001690010f00d440030141c03456008040c006808030440d0f0303100340140020316040110109000c00d45030480642802e00001030f48151400300d00a002d58007140030351132800180440c2007454058194824140b200d10501c2848060350120f84400c010310420380c60754401c0e50540036140c159006026010a0000341100100036a02c600300301850072051a00036950000c1e60050569500b42000b42c043d40c0c070702c40305202054040144600142000c0f000d055080d044000c81002d8072290101c6482190401061006040040740c02d4015442500c0001d4203e031500c60000c0c00b40e019001d1016007180e83e10786905000c0c588000c0f1081d6036030080c1841000c3c0074103141030841c1080c18904001401c03016000305500d1510307001d864a8040701d2410300d4032a90000840e040044e0740011840e41c4400012082c0ba4107441d10f00500b4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 583899199 1250 583897949 583897969
    0x140406080c340203012301031e02090a0b13090b0601031113081c030b0603010b0c03070501240608040b0106051b070605120c1306110c03010501170f0607020615 70
    0x24852016000b09019000204081c0450306008500030803034211501c404a1100305038220b101e604a82450041000ca411903800c201000c117038482c034004202040d40012012441250302c2c0010b20741e2024285c0d9182004142c0c0c040050700d15a04114406094860142d40c13031380100101e04040e26080048a052040803d07642e00c00482113030414620307107640e006c9450790700c85c015268800d1300d0070780080c40d528840d005800488001500c400e20303603420500454900d500950318440b01c0d101c20031248000640910940e0151103d01410f9426900c4600000f40005503e030300c40410042c40b0f205000200e034130415014115030300342c14015940e11000c0748201202c0d500c4101d9020703500410340002556078020b8010704000c881075107041e00c2a03131041c1207a201402070182d84041c0c1d1070203c00610406018000980701500c050b011980c1d509285000a401c1d20002d17000f0303403041d0030444001c610004040142da004440c00102409807440e002200941d80c020090641020b844070f0141c03e44503803038058042e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583900449 1250 583899199 583899247
    0x60a0e0409050c122e061d0105270a020d14011503052d040302070b0705010b030105090303090a0605040219062001020406360312140406080c 62
    0x1840380755814140180c866824000141c01115800c4480f035000b0000300740401c60340a0850302c9018005401075030502c040c03030403420300011555404c0124005450003045018019410359148096051200344201280302c04000d82c01d511000342e4084480114200c070aa000341c0188005072603d00c2400d008000c0c12050002d40c10642c007100006c90301248040070000b4900c5581ca00b8402901d42d003500d414111182e400400045076914084140c6540041209030854001d00c11140425181c09551000e68440030089685070340d01d6004164506003070158651001000b0095425854480d00150f01d030403851030f00421003503481d00047d045569074050780014140407075100b68425100c0030060301340c0c2900f08804926003d005500c403024407050003201d003a1101a41d1311808013480c94042e01c207001d00c9400102204401480c00d030b81c401c11441400c0020750041c50700d00301d42c000848016060201f903088610814400308000d0041c1a0002e9a0f15001002042200d90f14000150348600981402c801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583901699 1250 583900449 583900451
    0x20d081c0f111b01061d0a05060108040b01150e0a0b0c0c0d030e15040e07090302030c0a1a0a1103070b011d0c0a1b0203010510080f01060311330a0e030c0f060a0e04 72
    0x158605001403681b09105000c1a14204500c0e100c600055940e403104441c010200050b20f40180210400607040c0c00354032402d400e03c403603145407000004000361304c46d4101001c0e61001048442245108105071a04074405840c41208440321f524018116218038001e280262411480b800e03084915604942c002c008031080c032030b158140f0308001440c04000d07110030380c42449285100103051607c40f103500211503038920075003020286c42c150402103401441e42607040c0015410804140b40080c0b00511905102e20b81000d0150b04005880c2600d9030650684210480300c10704101031032240c00102c410100c41424403209610841c036070000014610030009406500300000c3c8039005a00c0d0200c8000e540c801c1c2c09541040c2844500745080761500e11015001145101d42c003049070070003c40c10b143c0075000040c101142900e0704008181c1407c0e5601200c08450005002840c0d55400b001c00d179071080d8220302800801c1402e1000400c6a4a500d0315148503070300000f0245482409010b02405240c80640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583902949 1250 583901699 583901729
    0x105040801090605010923240904120f090b04090f06031a07030507022a0102070e04210c03022508100209090604140103030c020d081c0f111b0106 64
    0x50048080c00e0b0a108401d030740e6040200b4030452105001070702001f00a031005020240d60307030742d04400c000e406c0c0d6600e02d101380030703050300060003612030014aa12850143c44a52050091396500620f100c4031100103108000800b07000b84402012501120111500c0c0c040200746c48007003264110007041150700c014082e42e4440344500e00188234075109071066007c1c0d00e0800290703850800698a88040e0060ba002c1d60300c400200b143c03808505582290201010f20440d018591114010541d0600507242a220408034040c0c40080c1d451480e100c01c0c4803216460034000c4072003195800b9543d417903525680c0ea201030401c0b103036418280e90315013900020040c0d0011070756035121341701c0ca40c8000d5000c0b02e40c181c00750400d84005280c5040500480c8084006212101c6403603107552800c0700d10000c600801c83c2c0c8101d80c1a042c0c030100c0c900d80040c0c9001c0c80c0d20510508500a112030200484880c004001140b03400e08030b07079030b8603a0121000d50301c0d0f6032303810058032415803142c03070b0641d00500854202010011081c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583904199 1250 583902949 583902953
    0x1e040c0506032d060a030f21181a0f0d091b0f05041506110c10030e0c09010b0f18040c02030703140301030b0a091a16091e050609010504080109 63
    0x8618002c0352024103d0071540b400f031072404110b80e000c00c5982503000314000320100006085031304c407014001c0c0220720f031411402d0031070b411030620524500c40b10009020556824030b032600082010000781b03540c3c0d801041aa142d40c102300124042c40c0d1100e0301440021a20310400e442a0300114107003940110380300f400d25001802c244065a00740504000c09401c1000419142882d01c038002100d070700e403000c05e03002e00d1500c0710440b1540b070100c51000ca903014000c102030040d2100c20708602092800d450101d158003416607101d00d81418000054814495a0010010b001001c0c085409640500c100e03103544030b81000b030041583c3c901380c2801d604a4503118020651680c0480909030542c441d030303210309550003040200b1080d800280000390120359040003065802455a00c0030007807912a440d408803000c042030741c240c90104201e031121151081076840303a250301d07440a0110090b10b050121010300203210100404c628826020f654003e0300c0004200d401c680c0100150780080007107034001e001d10481e0b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583905449 1250 583904199 583904221
    0xa0b180d02010e0f060105151c020f09040506040c0804110111060f0a0605010908030a030c03090b090703050c030712020904020a1a07110d0f030e210a0c0e1e040c050603 74
    0x120a0f403600c40c2c018680d84406103400400c40c14121080249143d4440c2c10180280c8642c0e0300c075130b481e1105c101d05602c141c900500140094010b441d01d40520544070380781007040c4029520000d140034845c5181c1545122400c0d0403100c52a00710b9080910507080d041c1400059403560b0010303030001054811034081201c40c0308403400300c03441540050307014000155550300642d09544a40035005807600284503010300c1d45d109501032080008a440d002c6114010f40e1542c15145500f0344038641681c101110600501c541001800340301d9400740c00501c126883d100c0c42d5007549102c0c80d002489150604082000e40d0380340c1319824040d00c0c040c030b1045071400800300d8251050340207280840d40f411f0801a880d80b07034508800d04960164004006928011541ea81107500a007201d601541c8200e121300301c21031010500031314401000c2c0d81c038028040d1142a0030302e400442c00c00d51103001d06541031130402410380031401d6040300001d0364465101c0245c485e86001c16242070103810803500a84080308100d480901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583906699 1250 583905449 583905461
    0xb040f020304021c15050903090d050307022b020d050312100303110706091205010f2c01020403020102070315020d090c06080a05071b140a0606050a06050c0a0b180d0201 74
    0x1003142d0f0420035142c104403080205101c911301402c59104000c004003d00314580040764071130150406d5900d0f04440710001800003445100544955101081c80c5e000c509020200c40e28001030042915100c09209080340302440e0782c020028002c500c1c5034001c01c05c01008006030342c4ca02c1c5008a90300c40c14034158241e08034440f69032106500094456103901c9115001055440c19904983e444000b0541001d103007a40e4010082d00407201596100d0302c07041000d58074030030b00d462600802201196107803000c0e10040c110385d2500c4a001a640704201c1000142c2c1c002503003c2c1200e61081d642d403402041230795180028080c02c1c0344500079070b04101c80c00c01000106501c81087d61900c4c3c40c3d42005850320005ca00403510104c5d29040400c088020855052044900956206100d5080b0600c0c141c02c3c0759a00c0d0400d000c40b541160b0741900d4143c1030001c0d14250308440050316840c41d101d41029040c0124503580d00319a40d000c0d05484e11007010490000340c0f50814122a42620111400341c640c0840090081007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583907949 1250 583906699 583906703
    0x60f150708041e0e040f0b0424060510020c0307261006030b0708091b0d051b01030b061923030f0402040f0b0109051512010603060f06050304021809010b040f020304 72
    0x100c00f43e02080d0300f20701010b803e000d5038010489540b4055250703148030f29480090002d484000b244042c52071185034005920400168100e404140e140c940010701a922003961945019500f0841074200c560320002640e00848444206141a110624045400f0321400b0900b00c1c0d014061903a40040d000d01383e030000e4044070b100e244282060743d104801220306104c1a02d01c3c01c0c07142c108004480540240d0b444169814078000c2c034624004407140e644508d41489018a003114901d440d18031025503806204031081c21205448041c605405039100036541220380f1541c4c424040842c42c82c400d15070680f0781c521201400a05425901c2c1001c8403840740341c200441c0c0c01c0340b080e82000c0c2400314455250007240740060301138403201400d81c201010060010b4020300400c3d030180c01409440407140d1b010001034006d0103551000200241080340e080380008a5422203c1409802c1051000584550741c161a1840c2d595800c0000c40d200d00126502401c07840003910f03846418443c209880c01d0599000b076010318 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583909199 1250 583907949 583907999
    0x60c01090c1a0703110c0301061d0a0606090b21071d041505090606160b0106180b04050103020c01060906170c040c0e13091e1a060f15070804 62
    0x6560752a0b00da01c0d5a40300081c00c1e51850302802420b00007402440055090b200c0c0d041620422003100d00468212082d41d0310028845d441e4805200c1050b5140104e150071903508074040c0615410b180300a0150350440c45a1502901c0c009803411002c00c2d84070100790303000c40c68001c072030b40c0b070070a00700041030112410710350000c11030861082c031440d2074280705007101420b4401e04408014074050810100d18001044203401000400880d14440da5062040606500c1076100e0f000c2035051480c018868050300030440b0f03c01510030390900c1590150300a85040780c00c00d283c09a9a0210345200f9805800d0562080310600d04080c00410151a4031035030198507082c1e4000c0303403140000c010401c415101c124000703c021031041624041c45060014820a0391140140c000c990051107903a9913031205805804204032000a2040340708011885140c0c0384070000505108a1a00740400042c0c0e0400240105030302c1841400d844031039004a1720300f90340c07000d40c1007001e850300c4070740d81c58500f480442200e88041a003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583910449 1250 583909199 583909223
    0x503010f0507020f0c0108071b12210603031b0f12110f06042019121101020a172109010204060201110f0301050402031008030d090b011d0c0d0b060c0109 67
    0x1200013222400c04170141d4030140140c9503200c040d02c80f0020792094900c1000d4000145001c2098a2210b00202040c0e83e01c0c0c0d2100c0286510714140c2050901444c0c43c19810304108001107030340300d490f041e040d05146082c1d511000a03031401c07503c2c00c06c03020f100810903000d400742d034a90b8a810074490130004109800380c0301582003002549848003011100148015000700030074101c00d000e41d2120052180103810541c18100344202086403410f15441001001c0c240c8007100204040288400d00143c0c003800100348a04445d6115001443c800c034900c0c00868021810032005082032032010050b5801c2240d0350780d5801d121310402c2c080d501ca40141030256013040e10748002d400e00c2c03d0844010240d4000800c1c196400c01d0204030103940041e00800c60000b003041c01054519052009201280d902640090140410310300440101030582c031115002c0c0c001c2d481100501d00381618254010031001c40c0b540da9810001c074220040c81c0b40300a4580105000c0342d02c0035416015408810360724002d02c200070308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583911699 1250 583910449 583910473
    0x21e130c080109090b0a0216020a1503110f0a030507051b06180f06160504050a12140d140702041d160803070c0e060102010b04050c0904050604020a0f0c08040503010f050702 76
    0x9803000ca00c8000e102d0178680c1c0c0040d114134850343c054040f5012801c0540d4484505400299081c040354002521240240e18a10800703601485445698500392403503a007807040d0320602e980341c0d000d0701c3d4241c4217154072000000c00e0280300e1805c60b03070343c04989050703400340c1c00c000440b1a41e01d1070211007074085008800d5034680d800100041c01c140e4194a10b0090089a44200b920890703241c00f0f50100c001d00a09000100c0d0940c0d6140d103042c0076003950806082005200e042088401400b41103030300350b175044400846c1007030341c0c03060008102030001092a9a20384e05c0c0d202050040c071803802031480c2c0c2d030540c0b8110360403c1c1c408220040e180c40207103013804009450b031448a8882c45011001010461603140030810304e0741040045034411030500001500700245004601690800c98825503041c000040e10324080c135080c030a50350818000d59045051601c41e078002703003040c64004050010301041c158060104001031040740c0c00391202030000d025424591010f0f9000d4541500c0040160041d4510401d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583912949 1250 583911699 583911701
    0x30709031a09071e090203180d08090606120a05030c0f1b0607141f1e0b090604021303060908030703060b03040c0b030901020f120108060c070b04021e130c080109 71
    0x20260541d84060400b46203404c03007803092003038114090418203098500000e4075070441d2001d940308400e081c3c1c0390640030280b0007001c0e0070401e45445d90b03400c3c0803110052140444001030100d038000426200c400b14440045032040c42d1140150303005046d031200154180007080c021076140c185010000c211017042a010004044650260002c5508410140329032408100f058401c41c4489245a0a5980340010705503428001c0000000e049034098036a902c1c81650b8003519420008a9483c0030100091500c0c04000340b44d2035400b070203031441039401241e050103245840303880500031580301d5420440a0344500d00b000c0340b500112680008a4a0000d000a98001d14402c0364841c03980404244000c0d410031400b05010780020748801860b660038050501407105500042c131881007003d258598540c50203400d185000002400c07040c5005050104100042c00000f030942c02c030f50f04440520502500c04040401d07000d44403122644904c0c0c0002c025258440e0794001e8084898035038400b0700982e03c84812038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583914199 1250 583912949 583912951
    0xc030201080f04151d1b09100e0a0f0e030a0909050c1908100f080a0c06140d1e0f0e060f060310051009050c0a082202100c08030709031a 60
    0x80e107402c05658981070a003c02d544203003205c0e50f400040c04d1808841c0100c55142040143c010000d441c4403e010340d03101e16201c00c40d2644404643c3c040d012690a280c0c409008100c09130000c0790060f120903180d00704000b01e41182c410200300408407a00d43c104e58400030092051071160b00380180c60000480c041801c000103c601480f50706407501c480301d00582080340c125400902401502000403030101d410f90090200d54001e100c0d1800901110720a810100080c1400b030780322230240030181c44443d11200c01d20060303510034040c07071100190000312a1000d4641b64040042000701500d48100d400745c01c065940003a031060200c108980342552102d0090300d46000a480403941984800f11004d030109581c0c0040743e20101420340543c02d155240f10040c1602d0041c0d640807594100402c04140e003070ba010b10322544c402c0c21403101031101c458405031002c040040c214083c0c0211006503007401254041c202010320940c0c011040c554a1800c0b401c0181b0028541c0401c4480140080507000f0a008500c24030f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583915449 1250 583914199 583914203
    0x6020a0801031202030a0c0f11130207060b0a030c0308070305091003060612290f040906050103120e090c09010219060606090b0f12221101170714030a02090a030c030201080f04 77
    0xc007019401f43d21606103030203060800300c48000b612540440c03651a041d091006190700d01c0f5025031201900d1a083e81580d9140c000c050007038203d8131040001c52000620780048a410582140d0b80e0030031400d088805101c0d000c6840d40003001b0030883c500c525072540c410070031145265110140f0243c6281c1003810b99248a120f12070100b00716000004814405414039807400c00107165010447d07a00000c102a1291491309070f610325502c40042050195a4560815185031440c042c800f0f01038a0300040d0841e200034010003c08000403884044c0c6900230005221855050044800c50700710a01c6c1141c0600424020307400022641540002c2881140d0142e4101031040b0303070501d007000172070415130f26811030046c80546c0e80d6180224540384044011304584a00c0d000742c81c0712000810210001d89904803503c050124814420200070009078001c0e04c01070340041500003156640c5441480d08044e002e0a02451307808403000b4000820050344002002c11a8802c0e2103600841c0c4e103100c2900c0c9805021100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583916699 1250 583915449 583915457
    0xb07020d0905190f2d0305030f090f09180c0f03030d02030601030b060705010e0d0e090622020a11010b06040308040308070602070807030201051f1a03040f06020a0801031202030a 78
    0x1c1c0320510740100725500d01000c21020074889680d4100c2130b5a048600d41c007446280d42c03130750118040720103808214001c081004c0c5014203054a0355070350907030724810f903e2004a0301d9804a5002400d40e50748000c00101e1000510002080c10040202004040804259640c0e0b00c42c42014101904008203a0648500c0080180d030030011b0310310024020790f10082c080750401d9958010310340c4603070340c120142c81d54a01400000409090381400c003071410088015020038822404400c444998554082c5a44045c041d0707507010b241030344006c0629000134540072810000b4001300742806a2035100203100000b200d050000e1000200c0f500500c0a03038071481c000031b00110810070061002c02c050030000e05207244035040c0140b42000580700c240c4141c000c0708045005075191001e00820351040f0b400a2005d4040241203500ac0b46400d4a000700c044030020401f15a42c0701000180c28420003004003842c95401040c250b503100740d40c0b100144458400d0008031040b0146006016180b80700100b548e040c54501d1700c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583917949 1250 583916699 583916717
    0xb03090115061409130b04110d050604090f0f0c08060c070308010e0103050d0f2a060b041e0c03110c06060a090606140c030c070b1c0203130b0c070c030c030b07020d 72
    0x1172000702c4190b0303215940602e80b115035400c600d4079140b25405100c1c030a60f14441d120f0142e24607031005d4a0000e400c0038829400d100c010008101c28983c1c910300745512014154071075a0520384502d8080460380070746400e008441c10080601c003c10000c08590b48203a803890782d41c1c0c3c0c0318100c0803d07410b800e0201400780c0d40a14a5403103582c1c000c000560b050481c90074104a20700d49030740d55251445041d8441c041c1541c07035000300700c10040c550245110700d0030101c2c3c0c00c1c03040c55900441c01141c2c88004c1140006c0076210f000340320000340260310110081c1440f42c40190342d24140504a640c4071015550980a024804000504000b1a00c5441c1c00e0b195035640b51102d01502003241c16250b0446400300c40d050104200c02400800100640070050002da42030503100c008001c004004500d02d0b0035100b10703050040042040c130400c014600c03a261035000307540f4159500c0d80c0b280c43c4054000c58000510803a903c2d000801484807403400e40003121704c12420301c14140d42d0008101c2c1c44840c2c40e4402d8010a090b08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583919199 1250 583917949 583917967
    0x31110060803160507080715030c022a0f09040b0618090d031e140f070c03170703020c06070309050c06090d0f080c011d0f0c0d1b0b030901150614 64
    0x28003c04800c500420490700015100d6080324107000b499844003c1244820000084443e014010020004018005030000c0300d070b03000941c3c0b007021038110036201c920070384500d03d505039680c1404240011005840c110641c906807500e40300760f00f403d030f890b144034440700b940820b10551440c031a6489195402e0150102200030030044c1c005d40f49414040e5080d2000f0300042d00142414400e4a1146c134400010350010700f41981c80c8142c2e034001612603000c10420300b04880c04070b500714080c0c00e055500500011003d40e60810118001c1c01501c0070309149001d290301b404101a41500101c0f8030a0184040d18407003552013041200c544502c42c461034101900185450100b400c83d0554154240590807030351038140c801d048142101d811226004142c8101c03040400d40351020049520813942046c01000d48119200c00220480500e25005180405e050102b03280036a41103a0803000340300690300b16841781070101403940640500c401c4408030007520360000a5151040c08041e40d01d2003201c54080c030b06600c034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583920449 1250 583919199 583919227
    0xb0f19020702041103070c060e0f0d080612030708070c06090f0941060603010f0509090102040504020706020a26010b0918130201110c010207120f0609031110060803 72
    0x30301c0580c0d00c00c1e03640e44805141c2035164015440380301c0e213a651400002c11460030804949551900700c0695000306844103400500041010403030402d41010a0380795540000104d000da41c14041c880301340400305d080300c00c2112940242102600c030b40552142503840700d10440d4921070781c1c402d011041d42c0302d41040000705400c0d8404885c0041e1050a0301d191400c01028000020b000d07184502503040c0304028091200085503015080b12007120140e00c1c65141000d9568040928002e00f44141c49400206220f00025030480703004040152096440e45280d062003002900300c00500404500c0307a401e2030303001f18400d9400804405004010014590802c0401c0d141a04500003241e08901c039a880d1901b600329413074140d84a6103024071080600310701d03480010085000342d00e41d0807090b801106c50155a81c1c0110f4800150303482a07040ca4110409803c0240001000c171101030708852500f104001819881705a400c0e41c1c01d003400881d810400d6910200c0200c409a1081c200030360030a03c04503843c5212 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583921699 1250 583920449 583920457
    0x80303100e0c120906010503010b03030c0c150c0d080a0b010c02010c080a03020d0501080607032405091320030c0312040b030c0415020a05011b081b040f080a0b0f1902 73
    0x201524181000114030340d840c96002d8a5180c0c16038010385c0100171601d0240100c00803840154061400c1880000d8050b545410307954070035100300c0143c5008040d4001a800362203080001d201110740c804072005000d812100700f56020150345003090311564055004030914107a0550694a0300016090b42d200d0040a40180c80b4074000c05070200230b18581807041e0f0207514043c0207550081d1106c1c1c14114130140448205142c556118a5500c0700c2d01301001ca0310745000c007100c0c801c3d2902c0e8400da845040c0c82e1104010b101004240f480c4118401418200380b400d0044402016422204219145820180d54420f804900c80500d0002c03c420300100200801858010450403e03443c08c0c02c0d00c0c1d107802109548505a9000103a0041044200b40b01007400350303214062103040089440354007480c0c002e26260005014400d84031410a14540c1e901c0208212802040200081e94209448080c4603071140c1c0f07511f0060392018580b102044001c95004807180c00388030682500c1914a2041543c1400f07504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583922949 1250 583921699 583921711
    0xf0601051e0415020c0a0608010803031303030f0218011103041a070206040512060a0615052709131406070504180605040203040303061805010b090d210302070b01080303100e 76
    0x6814840011600e600304006000226a44c0141c0200d0950340c0900400990660020f4100401000100421000401142c1c0c10000140f2003000302051821705a01800fa400360394800b1510001d2850220343c001055141c01e10401da80b610303405103007407000365980d000328041c1604600c10f07441d01d81c0c5414442001404c1e040d202415250500d595000042c03c2185a1201d6400581001e420000700035000d124130009030410100301ca19508507840010003030301030711201a890840d1201501c40c4000030f00e03000340004000034441031440c904001c841c44a403074494000c9411452005107030010b4200403074103900c15680c40c0c2e23469003032a03c0d100d000000c00c4000c20800060f079540d84804a01500c5038001175104e0b900903200811480e103403540c1140d032100310b649105805483c10005200a00441007107403d40d003c2150b02801c40d2032982000b1143c04105a050030b0000482c41d988403040d5056009003203101d000f40c0080850360b0307039820b2042d00c80c4411070711113000744254401840010300440000f90000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583924199 1250 583922949 583923007
    0x4093c0c120510050910030302030409091e050f1b030a02091009020c030a0e0306040302100506121f0c110607080c191206140d121106150301050f060105 67
    0x8035031680c04045420075982011256440f25040c000c40c200700181a40100440c5200380c4480d1440c0c034001d44902850241688403500c2d9400a424030501840c90309040c03440301200304292005240550761602d0444801016010341c9600301d19200882180c44007481001e0050050501d0aa0800199010003444820140c50b43c40001c522800188040c2103c69070000042d55501080107029107442d03040e041840c03083c0d2050040100003030740480c0b038802c202601e8074040340a489000000c5e1302035004d240303510810f202d4003404940d54582c602004000447c035080800801d880882c04885100d441441904580d00920104105038481e41400fa4481182081c0c9820400d911005a00c0c0303003034040302840003038414038640156284511034400107003000c2800001240d038020214007500c1e0000b07409030407801034000d080c0f1640c2c041c001d49079072071140d90280c85441c030b0901d520080c43d0b190400003a0107580303082c00040403c44041d180c1130103608161a101c2c10291400c00c000c0b28501c00f00d60300c0c4408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583925449 1250 583924199 583924217
    0xd03140a230601171008070e09100e07121a060909030f0306010203122a1905220f03050606030304060c0237030314090f01050705011104093c0c 63
    0x5000b07843c00150040b9809108941400d11300000245007190308e030010040a5000014003901d60710008441d12610070301240407c0180940d2071043c01c0000c00d90000f03e03041c0d04d0034850420002c804004803c903028812900d0001d85a850a118513030f0030480d07a2046660081108461000482c00030b16404401403040341c3c43c00c4151880c032000840c00399980c000c49410550346c0c01c036035030314000364a2040380f9a0a0320750501000a104441c9182c2a42005043c00b4001800616121880c8001e0140c10003000f8560700030b958942107180c040600744000d4602c2e000d40000b0611600d0044220750131a00c80755183c61440c0255001c100d140d12401030512080400c00d05440c110b2204ca294060208007860013601c2034915500303028203540d80400701c0c84903100c0d080103804801d80d101c0c5440f0341c007180e080c41c05940318100c0d8034045006008440071213148500108001070380b48043e41008154891200581443e00301c1200d21444410103c04c280032900215080801520210360050300070340d072545040f40c4a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583926699 1250 583925449 583925477
    0x81009110315040e1923030705160302150d0b0a031118010308070605041713060e0102152202220b010f0f03150302030d03140a230601 59
    0x48598000c100103a000000c000c0251003203140612500c0600e00351402c0c04030f14900751566480d1000781c141d060a0500070303440c2805002000d01c0c0b405030040e80b5250494404070306c091032592900404c900b04c4251140203c2030143c95540c2c90203604a0744c1c080c3c0040160450180c40715030321382214a0b6485800e03580c001c021469a00c003440040214010907e580d04201c0d94001d0041441221817288119200d45c0c0041000810040c2110f443d90b400240001e89512107113822016501030700c24500c04070402240c00280a00449130410443d942c940340d211090340300a005a031280716540700039a2a8465100040d04d0b02103000c0160a024901a041d400c07040742540000d1002086140e000382c0fa018400a5140003469841802503030034003400e1010345192003031402081c1800c4c0b4040c0b901010b44848028032a8000800b9050241d94003e05466842118050003401001107413040c8507903c03a0b1001081003403403e445041c840500400319a01c83c854804142108000b0250002d410001c250541ca00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583927949 1250 583926699 583926701
    0x9060d0213030b0606070c03020d140703080a0f0905100309060209040c0e040c1704110109030f080a1205090a030e0604120c0807050103050f04021c1202030d110f0a081009 75
    0xc5003100c924688030082c11414110108100244480d01500080040c007003c11000007815013106d07170403900d5014612035484d04541916021080d40d505100b13604010041010700303006841c005126551300c16071800403030012144001302c2d2152541141044112403402442034120100190142c000503181450b0800410708417281c460b2054002540d8443c558424a014043c61003a801e980c90b0100d1007120705403e0700741d0b894010304001c0c400404a246003c899020300c14100c011500f14150086604180c02c000b8550b5015401450002e0f144c0c9041d10354101407841001d00407003080c0d000340114030355075509031004032921402a6106c0024000054001400d40c001c21003184900b0840c500d00741340254003881d001c05034104a06142c180401c01c40216075100c01d20741e015404640c101075903c452100c2e0320201c0c10000026100480000c040004a41c00000400d0789007800035040000c02c0100308100f8180c003450303d0019070b9460401401000138820034505802003070901c13a8203c0c8039510040c2c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583929199 1250 583927949 583927957
    0x160e041127030304081510080a060f0e0706050a0f0e06040906030201141e0702040b0d031d030303040203070306110d0c0f171504050702010b0405040b0103020a1d0c09060d02 76
    0x11882006108204a0400c0805410419010709038001c6040034241001d00e030b2913040d1010b915920040078000600d05c030780340780100c400800e07440c0f05a83c040340c00350800c075002e441c01c1e040d66550326052148103003a00d500059158220f4605950ba282441003403041110140c3c1d036204403070100140c65080c46000c0c0d83c1c020080008007042100010381901d5440050f1075000f90b1074820201340824045045d0700d101c1821000f03112401010005d90f101003e00c001002002098941500315241204000815800041e20454914004070765020910700c1410141d0703034071045400075003681041004000080e1036410030300c815804402c606040200860004084480c01c8144400003810302a031143d000780c008a00c41d05540340c101108200340703000d44134051085030700d100d504d008503501e40001e41d44074400c0d44a0548448000e00502c494101820322100c5603100707000036807140c0380754040082d100d80921400d010001c0c62a090740750940c4e40440c42001e5401c0301c5203003a0003c404002c0d07900c404603144010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583930449 1250 583929199 583929217
    0xe01030b120303070306150c080a0306120f051002040308070605040606051009030c090506180910060e0a05061f0813021203220b09330406020114160e0411 68
    0xc1d0348034541894001c05030382040d4846049180547c130342030129030340107030a1207045411509807541c400803100120b00500c415407010b84245050103504c1e007005000c0f00320428a502800480d1854451405000102e11a80c80000c4c1102d00401c01140000c521350040c42c0e000703000e1800041d20580d1031020441c1d10358441c0c44c24001950152085c01004030080c01c0e10054464444100550701d04180424107043e01c10044810420b641e01c0041c802c0c000403c1200ca0f41076500d01c050021582d070b84003500121800380c0f035400080d1704143c00281c1c2e41c18a450b4150354400d9525021008500c210003e84950a01420101500107145c2205015031035040c40d40000c01101002103644003182e1070060104942c00030034185a0080031001c0041d00610400d0340c5800c1c07421110801d901400380c10b00389440986905c0c0d014110300c000340903041107407060701070012a100c40c1c00038400c0e001120b40ca45041c0f903045907206d0b0002c4010382e201d8005880307903854406c1e000700948000343d45600d284144010f0741101c42c40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583931699 1250 583930449 583930453
    0xf05031e0c1005070801060309050705060f07020a09181b081c0e0d15110904090605072d0e0409050105010305060907090e0c04180f0804030209011d070e01030b12 71
    0x110490070307001040355400148100d1000c02c001d0034000b900074508007061040300201a1642c000300207002c01032007060b00514001708000d58800244a011410fa042340c0320580c030070707058036000088000e450302401198400c038070b49020038000181c1d2015444064648080c5040e05042004280038000304013414072241442c0d101112132840110043c18007000c0c42003140140b901d10245000a42c0c218005800d241588e41c2c017058003900800030f84107500545454650150809803820203201c1c55078000c5010301000c0d5282c101d1340040c00008082401040c42446840780c00e07400115409102d403814022040c0b0040011401c11282c1c0c842a095130000e03081034480350040c00a006024a04105039801801044400c2c03203032451282801b600d5a00b8580d030580565202c01106a20344a00c035880c508141e4882510741044106090001d556040790000b24001c1051900100722070700f000340c50030110f04051302444415074404804495214220140c1c60625403141425403444e075501d602c90980c4400900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583932949 1250 583931699 583931707
    0x13090302031201180c051e0c2e0606030b220e190b0c03010305190f02040203040606090e0f030d2304031d041a0d11181b2802100501080f0f190f05031e 66
    0x4002743c00c54044d540401c060500d3320308641c050b13032074040b19118110720f02e42170303441c0120031040810060700c075004107214030340a0041c9201d109484883c101000340c0c0512000c020b43d03500c2400f00c00d10b0748402c0c0409800c030740c0210b02030f004503e034594031040220309c1011034092108041d400324061380c1040e42e00300c91494441005100c02e4101d441100d41c026590303002410805942b00025407070f0701c503840d00c046105850b0940d105828440014800c000380e4080b1080b11a8502400c00400d21400600c1021840b1284d100b003d52901d064007905170320940c40c80018800b29451410042d6403001d030001100c55446208120106030b40c1c0404107402c011001d58503248070301e445480c40d183c07840b0000f00501039203024403103c86410207c0c4140c440e050300414001210030225881a894400040d00305442c030750418002003650440801c1c1c5541241c00102150700090140b80010703114000a010039405081d0201c8070f0700824070f075051000070350340140180d038134081b603602c00307050300d40c045010040882c00001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583934199 1250 583932949 583933033
    0x41509030215161407080f1c1802210a050d0215060607051f020f04032a0305190305070b0c03220213090302031201180c051e0c 56
    0x6a01640030001d420030019603080f2050181c000031180e03070707210070882c0d0105001c0e040096030003c03240414400c80c0042d071a0b84007403541d002840c40e0415104a924106000803a21008010201c07196960051400030700890503110500b040c0800002d00d0007500c145609500814010f02c00261110481d501404040c0340303261807a899610045c000034043c285c1044000081903012540c41000c1a0b590541990002c41c2458074029010ba00101c1c2d03018040080c0010410034285111403411040580700c007070090458030201a100010711001d0300c25007007680d0130340d81d68050402c07840c0410702c41c1c28214280441a1038404120004803030000306a00004207000c01c808071840003103104212015a03003100e41296020130700d41464080340700b42e580e0b107803a04601014024019102c0d5143c49150007070707003581c1d20050b2030042d0310903c00740c80000d4504000c42c032445204070101d542c190300b488025281c203107100300c143c402da13402407800142c00c0c01114141c1d00319000c1952181980f08040b81d08500d510518 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583935449 1250 583934199 583934233
    0xb03160f06021603200102030f0f09010815010f0e031014090106051e10051204060f15081b0312120a0c0f0f030e03190315090b0105120415090302 64
    0x18403d51901005004010000a8030702e090300e00607460a54502925100304100503891401003281d0242001c801062141d00341001001500a010099849140c0d6444001c0700b00040300310b201d920b60024030881250340780c117070160074000c2d400803001c0c00311000b0220030082801111003440800c4020107440f02401280c0e0802d00845019240c101c0d100c15040e8041191040000700e11605c440c01800d01040c40e01c8400d001d0025603910b0f40d1541e062406628161030220001c198503030051512500d89030450183c0b0204010580c15030f044c010040220a580712112206600d10f0716480303900d03200d5203d01d501d0b42c1e013840300075000b1a0180b00b0480200e08001300c120060354600546441000340c2c203c44048800c2c1d2102c005043c0440d182000559468500d02060a512640c00c030000c6404c10800b0000b80a070b450b91000e940d520b2a01803214455455444d2503007500e03660280180026000c0c00070000c100e124a500301d400070700ca04140b028804103400001c0c1503c122030b1064026802600e8030745854465 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583936699 1250 583935449 583935463
    0x5040b07020607121808040801050f0c1c1d030a0f0f05120109021e1818100b03070c0b040b04050d0f02100e01022a07060504080a060b03160f0602 64
    0x1400034001510f03208400a01c0741d01440748190f2130a840313919540c18a004208075a8889412032045651191600005406010103440c440f420914a04c0091481d40711001510748010642c0151031490b0940c000032005044001030810143c01d14071030300340e01104100010401d0382030031b0310382070f10904d00560702a045c0420814003409010040052000340c1006003410303070658403000030058454014903e94042c03c0340141005a1000000a0043d014495000d442100e8202200c400319100f006809a0030545401d45d111111141d1000e400d01054032000302841e403005192500c0c40c51080c158491040d03204c0c2c2500d0070f460086030301040c001442000e000300780200c0100d003040215610201d80083d5110501c0c4120a296590f606038501c4005082d01240c2d010074000802c2d401e101d908a0060b007103c0314042d6025864840c030000061803d000b84c0a07141241c034603102401d003000441d20f48001a00034004c3e04c0f98140242144d4406040400008101604043d5070004669081607000380ca8550 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583937949 1250 583936699 583936711
    0x30201091701150815011d011a1303050105010918020a0b0a17070905130207020a060806031e06160801030b040b150907030b033c0312090a020a05010302030106051207020f0a0605040b 80
    0x40c40d1f440c850380c203021480d0300f5411103c50300b0f2825480c14000c00c0140b00c1c4c0c0500c0305007101081014a000050010540206044c1d5220000402c81144904010400c2510b00274000790803140e02241009088410806015584a40d0610000b145210011880e0020084540700c000c00c80841080c4a64248841e104024040020003145003500a0300011034a80040c03080404002c1003034001041600c00b80b2000c0b0b00064110030004030f003030064a01e0398803010100c507040503d000401c040f84215101c2c00f1054100c0c0c0c0c2111203510191280d440d003206106006203050040602481c018401c1c0e140c2a00c007500c20941560b0000d03c0721100d104240c204a0600ca0400c0c0c25003001d030280c7c21038000140c0c4003040145090b89a1598041c5180d2107042d03005100c542ca1418204078100300b070090b00800c942d451a031007220120684d40d1100015030881c0402e000d44000580240702030f05510004000c0d90f90403c110380102c4044070b90070706a091031314000074011202c0ca40c46100303010410120119240d0404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583939199 1250 583937949 583937969
    0x303021603020f150c0106060e09280c05070804031112010c050406030203090705030f0d020115060503070c02010c0b190e0a020105030705160b0a09150603020109170115081501 77
    0x3403850b00018062035501d10040d01c102010703a80c951808108200711400a100302000348081a69132202421016048019a01541003003002800d8400d44030600013521a02400b501d000d20400510344004018206d80c000500100300f0217140030a1360380300500011849656146080c001c03800a22403640d568000c1151141e041180850145030040240c0701034805074540140c070fa644550100341b42c0480c40e07000b06d4041c000d2483e60f0403d03120100724003002c1181600203014084007881003500c440624445e0b030f00040c2003440801d1507035124030320b9074411a00500d0034200e81c49454644c14600728060329030028805107a00c01007800181070042941d8102c0c84005000154803540010304184030003082c80c010090005900c0110118580f400041710340c12290014040c9400040c68000742103503607086c4d903540ca03560349000301c03500e6500425003a29410380d1140392041c50a40c0c4060340122903200a007495485107228043e0380c403408a0000102030b800010110b0400710005110a0036040e0444a88a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583940449 1250 583939199 583939243
    0x90818010e0603070507020d080301080c12072403201806070b0424090809010909180204050a0204090e010b01090803161203021215030f0a02031002160f060204030302 73
    0x1039440b001070701d034401000d0402d20740d95004c2c1e2001610302e4002c58002000103001200200700c9100c0001e0a001000e01034901c070203181d020140055440c1c9082c425210a00440741211500c007440f01c6060070b900f00a4200429120001280c05801458000e0784e081003480215180b5068003100ca0190076100007070751120728000c407544a000418a0040006d41b00441c0402890184d150203040071156008445d41000700d040c03149096072203a405030340c415000600880001c603210180d44140c6041107042c0015080c0780e1920b5003400064007000300104030441d400d00c000115101203004003034446811000014010000d00f00241c5040b030303241c00034112a40b0611903242440d41c3e40200344100360300200c407c1203d00c1d441204402070312442c4c0e0f6800506040b00203109804203513056000d01080120252003030f011440c05119039403241007102960591005480d1071380c41100b075004040410101003919481c10040d210b5841405030200211507141d4005020030034998103100041c11405218150451 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583941699 1250 583940449 583940477
    0x607022e170610090b030109020403150e0303180309040e0f0d0f020d0c08090a0605130602010203070212030a060b0a02060901050a06051516140f0f0a030516051009081801 75
    0x10780040140303441e000d10310031000081c40c0c0d4081c022060042c8041d101441e96982c640c41c030301029420512084075001000c88840903640014024130050031003010003141581c1d204112002e80011004985606020400100d14992039501800e1007140100000309a03540450142d81d113003082c000300f101c04001344200c82030601c0ba400b10303440d50425410718203420248902e0400100600c200102035512a04c1e90000046080d0020302410718081461202907a00703540b184142e0907440121850f00c01030300710022451481c941e400140d90011a1072000045013911004406c00070b0b4030615034103001d40c2c0148100f02d48102c0c01d0003800d0780241d0600f0300b80603040c03609010034090b882102e501002d000020a00c100c41c0e1074011031801800c0d070000000e00101080c0c0300c00b1034481001d0340128845004601654140b000001405200258582d5685140540c54003030354055200410040300c1c1c901640091080c0072906002c0e80c1007049c06031260780d9980f8807613003841038840082004541445400081000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583942949 1250 583941699 583941737
    0x1e13141c0b0705040b03010f03022e0507050f03030c070c080715030207030314072601030809041d03070602030f0105220b0d1407031b030b0103020f0607022e 69
    0xc05607448002600540c80d0b8107401d56040c025500880e00d0300c07101100020381001d14183c1182100d0082d00c0021198040445090340380310500e070078150780019281000700c120b1160006019150251080d1038515000f034062034115401a6415180450b000c03c002c81840300780c11000d4010134000b8000c0490626005548510094100c1c464044c1580464442c0900d4046d42058159030760702006000640f0348544003800710402c02c2c140b007219010520780000b0300720409503000e0503640c0215450381445110001c00001d0060450ba800a040d4084071104680004002a10b40140b003003030056264070f05400c100c04403040517880244a80248800304501c65082199001c0800341c042d0041aa0300da0400824a038029468005251680ca66400c1145803000300e061b00a032481461020080c81c02c400f40403d00c0703103036800054840d03200c0c0d000420040c5040c9074140d0106001401c00e80c10b0820030f400141107081903d88682d0480407407034452040b048210004c0110305d4090800c1d410388142c942c800c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583944199 1250 583942949 583942999
    0x130603140a0212030a020d0f200a060623040c03060b0708120708270f03040b120705070309090e01091a07030c080c0a110c030d12052503021e1314 64
    0x3040c41001144da81e90f55105600301e031003051541d41c80c00382d47e0780003841158ac0c0318100f843c1650182c0c50040701082202d0458101700307203100041403100001000d6030400005000b80c1555605142c4e403000c0c00280c521201c400741c5112400340e001d098a91040c0f080003c04d41d80018a040c0070065040108024042c02540b1041c40207650380500816030b01c410080c4e403805078507074001c00c0d030341c400414000f880d00c002c000200304810b081c04c4526065210a00b013565140200d000007004907075441010710100890f0392110240100b80c8002003103084080d00c41c020208011000ba41040d0210010044140d406020741041007101d032410007203502e0301300008802409103c6141c42000380d007408110604400304011240050020140c46400d41d0040b0060314180310b00c1a25180c031800c1200251303d40303610b4003820700c4600c0c0f12292420850200c2d5030450096210074030f0041441008907002022100070310141495030041e4412369025070910340d01c0008a9840c0d81c45d64822404a011002494100c2c2225 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583945449 1250 583944199 583944223
    0x60904030503060a050406140f0f09160909110901020f060708012610061a041a030c0c1506010215010510050c190506040c050915130603140a0212030a02 67
    0x41070b140d4a4200020b88440c0840d80960340c03041c240940403c410fa0045101d40703400b001103901d14a0103460406200f21070011180e919445090280003031601e6883c00e017110213a00052400161144d01c80f80c0c0390701125104900f402904c0c0010036100340950301002002d40c2034540c0c1006241c01c1ca06404000c0031200140121041103120140203642508000314081c5600040406e9507c03106004500e000100054071600c0091040000485c1614041070110340950300d415600e01c00b400900c6914482d02e0b4005001100c24400c00c2040c44d403510350501205105040e86880d50207281404000245407602d228120740040c0c44103001000241d072141680340365818207003401511500140c802d02e0521207201032184d22100003000358810404003252040c452031140c2d0000d03000503203d40500060712804c51340c40940104c00ca016454607e4013880680d9000c2c00e424001c03440c01c0d22a96002c00345101e017075100c42654042d00e001c3c81180b42009144448070241c034020340c1810b01a81000b9a07662070030000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583946699 1250 583945449 583945457
    0x2304090e03031b1b1b031c0f05090d0b1305071a04050d05030f03040b061008191d0a0602040f0503010207021807140a0804170a2a0c06050403060b03010506090403 71
    0x90740310070244d0412490011030081c4251130620180020010392003c00401a5100e03015001c1581c01280360030380300550071821550b074108904040e401c00d80316580625265a442145100b05000240c2d20340a0507100b03180c074034031603034010030350f4079181e4901030042e088884401440f013240100400020306032421140d085640c4184040f0500707019045101e1101280d440300400410841846007504840b4040c500903286c1c5100312115850485819100781c2c4d03e070360844000b00d0423500c50340064015241c0d110400c0c0c21008020140d000407451b00781282801c80d400c0c0e40100301004401035034903191008101c1070b4029460100c031a40012a010410040071019070602004500d000b8890080080c60882d00c000341a0360b5030803400060f041e2941141c0881d540c0300000c010001d405141c0c0192103500c1040e40b250007180c40101e9580c2051200d100c802d5a8504a0b018007d01080074142c440009250720380313070656a5400c5040c040203032a98040064040c0e0b041c002070185c02d4440060003039000380c0501d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583947949 1250 583946699 583946707
    0x102030904200f0705100204030b0f070905041d010506032e020c010908070b060406031e0503121e090304060503130201031b0513050301090804060305072304090e03031b 74
    0x250b00001400d60300803080103050100351440e00e00581c00007800c18600980444150401c590004800c0c0d100e54040100800032183c045401c250b00705d000e0940229441c1070104055480d0030200341100d07950800c038100b05151840c03a010036074080c814660055411b03030281002c0503414505400c40d810306840000c0d211501030f0241400071142c1c0c180c600f911a0080280507100113030501668030340046000382c407a0188100418450b00d007500c01e0808581c0c3c80011a130021700c01404501b0300d00f80402d001d44a50000304260154802e090b07800d02e110718205001190545e9000d01c0702c07011000010102c0c0019801000244031180d000810340b130f4801c00f0410740303000d104100d200490241490500c100d10215403654250201a00300001d86680e400c52409001c005d035481007051b0a0b2141d88001800c03a103000c01c000e2081c0d503c281c0203658412076034240001c2108008940311800450185410f108040c0860309200c40c49141c06500202c5541f040203500314207100d180e2154112148907042c1c1c0c2c20341c0000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583949199 1250 583947949 583947971
    0x510060504180b0708060a1701061401030c020a0b100b0409060f05010c0f02191805061306050105030a0209011701080703061b1b02130c0e03070603051b0d090b0405160509060102030904 81
    0x80d0350001723414072800c030368022865040c550740a01746600401509290180f001e103201e51103440384868101080d801042d0002040e12441c0146101a111449200084c08003050f0551150300500c020018480c002921601d8441040b0082503140c00003410806801c44050104038040707030804c621601211902010010560b01444c40e5519901c0b5480750354907400c200410700310a43c850b902c9a141070b6a400000d03860b0103848401ca030002e0103480e011074002e1001c0f484010160380640704455041c10034280152100100702d40d14002607000800b1540300c0042841004018001c0c4014a04180e50840c15842030090143c60240200450b180d001e52040d0441d0035599040389030806101e1018081011601d503140050058900c49038090082c81148000102c040c868480c440c40350403100c0c40301700c030303866440c000c1c0c0b455900401c0c0d600c003c5038407425071001080543e001140a06c1c46440100146641c1454400d00c2c42410381c003e40c8110301d05403c00400366000300449180d40030403140020085520 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583950449 1250 583949199 583949209
    0x1413140613090506040207302111040308070b01030c0e0c0a0e04090c1e0509220303020d05161b030f050a270f0b160303020f070510060504180b070806 66
    0x90000900170751402203141c3c0f4040880c2c0542c40200000109050f080030b0410002c0d6050f540040f200fa160b18080f01c45c1c0e0b0344405617a4000030100c0322b0000c51034500340c0c0c1c903201c0043c2034108a00541f403106418004000f0000da000c2408000c148202c40000d140c0703442d01645079240101680d000c14042d04510000c456500e55010900c4542e2114410b454a9120200d8007109034410505000c03042e01e0b0040400e09142c80d407800f41c400c48204401c003205140c9000303100f100310f02001040781070507001d011081582c989400340030b02c01c2c0ba10814001c400c0a02c10300c01407419108640302e068841c030680807240400d40c00f005040103581242070a91303840e00445011500c910720b40c0280c0383d841ca001400e11748020703030340703070154007204c41014658050130784600c4000c200b4498041c0c41e102458400300da010000e402a0050f010445059694904000380341e10f604d400c0502c140c0d100c02029a0351201400300b450140b00c0c1c151007881980780310001032155034400a4842020b0b00071028407000d40e00060540e912 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583951699 1250 583950449 583950457
    0xb0d02220603050102030a0c1d0d02060c07060503060a050d02280305011104080105060a0e041104020c0f060103020103240909060b0a0905040308011409040b0714131406130905060402 80
    0x540e240411485581c1d04045000f50020380300c40038200c0c140f03010111031503c1040e00b034100071070013085507010514880c00c100c11004020000c07604540c0a00c41ea0b50a030386e00740003480041ca1152541caa82e403806a04100f0700d45035a801903417090015204c0d090160b2507003141d124414201143d01034003207002800090000c20b159000905039801d1072072030180000e405024004a61405000b031205031a29801c101d00b40500d4012104104c4c103000001d004a40907044210010030050001807400c0c0d08c080c0860f0030030303125101c6812154000300040085582c5446401100e83c400300c40001912901c020b0b54408030150300c244d504440e1140007140c1446a564400404400d0080c004046035540350106409018103c6055000c10605000000d1038914030906408440006001000c190394540d0303443c03070000740602b85504000000c03502e1011003414400600a07811880c00c1c0210062a02046200074a8080030041c0685001d00c82d10014010001051007035991081001c201035461102007002402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583952949 1250 583951699 583951759
    0x510150f090b0708091003050408181c0b06010f0203041503020d0f0222050a3605070e0a09060e011503110f04030b1e0c0703090e04030807020607030b0d02 68
    0xb00080d02104000304400240160003041c1c031189014042030300d00f68102c50341120b0203081700004011070101000b410722000032202000300040904e01c90755503095410310000400710b40c2e840c05541408207540e00b003c2542d401040742d10040d491300c0e00b0140e00241c001c00c081c0721030041c10780102c0c4204001049070400010701c4810794003152a030300c0c0a40001d0621003410320a140b010703e4590003080718107103040000301340e840c03440c1c9481582044000004000c01612400898400000c41d035100400060183c0e500464150b5271301d905810141080040780b140f0399120000091510000700f0130000303803140e03490456000650700244d4203440c25003600036044000500300c858070002240c51603c1020320103841640e006452185180e0794407503d0005c0111990603002c8034030346c0c100006110345540d2008040040c400d152407040950703910081280290b00743d03000c80100745003004000c201030b410031078140e02890303928080c412410303c040455a407103c03440c4042d000722031790090220080280003066003445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583954199 1250 583952949 583952969
    0x1407120c02150a02030f0106021b0904020d0507090f0b01030204080a0f0813080105160206270a080304060c080708040804060f03020910020c030610051509011b0303020c010510150f09 80
    0x103e0050301c00c9000350b00c200c0d6201c90000070300703001140d500e01c0090b448514004409030072070242c580c20300704440401e0040040741d00004035454280040d400303001c00310007044165804035005015160410941d8204540141007610600040155410029180300c0da0b6030000c010758580410b90429032606e1103a04100c808801110b038000801c1c050550040d0b129400594140301c1941c400320080f41c0f01c0c5000d03140414005503c0b0707448580c00701044101c41c0700c0341d810411115000c0341c540e82d0700440d801c222005d68016130703540d9405034031076000481c065001d441ca09c0c040125241c1643c6501e100d0040340034802c03c0008560030108400c2c0280d0441e1203000c001011500c240702820720003941c0740b80811505d806400ba100115032000790b4441c00209656000380301c0c03c210340261011003016002600d080b4100980241020300c1c8181c1e0000100010b070103070341c001d60351700e940c03080150945501900140050303801e1300c010004e0642c8500702e60722192a618000c0110312401804581144550300851088 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583955449 1250 583954199 583954201
    0x90c0905071b1209060c0308150102070504090308060a0b090604090b180f0714090609060d0213030f05061e0c0702040e03030c04090501120309060c030c060f0e011407120c0215 77
    0x203c51641000601507005a036a048107030b071981c00072920800020300042c00300c2c0c0944080364808000d02d12880c440c0c0c1d4184104c40382207a4401c0080c064a9140c101a00450000014000142003a49030000a09a10ae10f001d14048480004c600c00d445984501c905082d902c003030303800c03180d41c032183d180040450044a11380c4c10300700107a44641c0c0319010344d54400414550748036a000e00809809490b4814001072070f240c00c0204002c24000c00794420140c02c50300607402c22144194113420a00000910b02403110345004014503e09a4a0200041c04d10054480807000019440d004208410f9004000000c501d484241a2011501622103810498141d000c04420052600c0000e40544100d645052041c04103991320050142802800b401c0a00091100318052020901480c1c070503c40c01c3c0b003498150016602078a62408582120760800101030300c6982c80c42e030a80c403d00070380a500c10b00ca8546452814003040c05426103812404d606c14580e00c0d402e0449001d070091100001042d5003401c5a01c031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583956699 1250 583955449 583955453
    0xc011b12080f090c01081506040f1502070608040b0a0b12060a020a020d2a0c170a0606050402131401030204031a0603190f0602030c07080d0f0b04090c0905071b 70
    0x1254411904415041e00c0c02c400185804070004184640c040181c58184298449606183c4e2040744c0340399060300544108030015120b00c6080844000300090500b811f541003a14000909141d070355400310040024410134040031440303003031000341c10070348144000841c00d0000021811006580052849900800e402c025000705150001c14095600b41e0958104c07518410f000e550a03900030340701c211f03d010450740018205020702c4503a0450f074020a00343d030f40d0541e04c1040840c120405000700c111600416500380c10800540903090280000b00c80550501028039414008900588200c3d0703001086094000140d9010f41e045074050354220004100500c545d00f81144008810344025000344502700b880c4854401500011080d1688050305014001007900c41c20042d400c00341400b107a80208100740c40000d84064018100b00c00030714004914500403200032000c0f1007408051754000c509080080c40002c112170380f00707015181364180c00501c0e5126907130201e5030381101c8003510a6031150f0740f0890007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583957949 1250 583956699 583956707
    0xc090a080f0d09050d110d080922060b04050f040908040b040b0702031203130b0405120c1501090c0f08130c0e0103060507140a080613022101080f0c011b12 68
    0x1107142c2e911096040c65840052100200c126040904920861301c0c99000900c0c000c1d2061014034003445c2a0780c1003c13514000214223101c503071140131544150000b0f8010f02050350080c00c00a060070309070541003924060114100d046442a4148516915031000c410404088292000f0b44032001100380c079144c03a0007210b0026800420f007a03120b44180303600c12a81440400469104d0401c0000d6803100d03040c19600c0200381400a0700c01c9440d40030311245250030100c6d0001a11081c90685c00a00c400a01000c00d81c2c60203a068101503021030505180800158100520410100d241c0c945501d003981c0d002c482200c000c601040040569004103000643c001d0301e0803400d81a00d00502c2c00300000d485000059071040c0300b40c030b415441003a0038030100b2a0f050084042c07550000000d0300000d4606803002c0c00500301c1c3d0024080d64201c440c918100750840000c20502809441104018000070161016603645e0b20300b07200c04c07141000301c000030350001d51118100ca59a81a07200101c00002c0307d041d0b10142c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583959199 1250 583957949 583957963
    0x3080403180b04090614030304030f060f020a0e01030c020f07260d020f0f0c0d020d080c0f06010603060f05061213060c0806010f0c020f060a020c06130501110a0b0c090a080f 76
    0x30304d480e0400d00c0104070010941c0e1092000040100154a000e1840d40d600505082800c804d41e8085e0b43e1740c80082c00840103000520000102c4d40d548103c0010080014048800c0d0003548021940710031801c2802c602c001891206440340c0b0043c2c1c0019091850b000d2820001d812954112070240c0502c081c0c041d0340015200079540d24210a4503201035450701e03d183d42e00030008886a00111401e4002d015003041e803415150302c5e008900c0380d41f4103c1c2c401c10441c40d0a050400c000000d6000600403c0b03020303450301c600c40c06001e042c0b280b0500d892034180007070900d002d05c81c80e000f580c40400010410400040c1c900114441e8002c01c01d00c0b403224200b00c00313400031008840c1c6c103001c80d5594054030640da104109000d00d6070f900408580d0304003094000c5c0b1a403a00142c0c0c180c3d003540b1440b100002185d907508050144004d0a8142446c014102000103011000108825103541c1c4841c031a400000d0070110a268041840c03042107031070700c0800001072159020baa0000000c0e000b004800d000e0131002141c0c02c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583960449 1250 583959199 583959209
    0x8180a0f05060117070501120902040203070806151c02090301090f03050414040c020a110a21021003140109200403050f01050106020c0a03021507060c17090d0c03080403180b04 77
    0x42d44490380c2c3d4022886103605510412200da8200140601056008011860301496220b900040d0310000354045002c070790040da1480081204034013000704620741204c02610303441c0304109290511500d0542c04140d03103045120343c006550041001c0307015407025801020007541010300c40d0070060075400c000d4481d50042c0900700110300010b110001ca41401c2c0108280c1c000c40c0e5009049040701ca458140c5180c0d0502c400a5202c42c0343c2d4070010301604aa04d500001401641412400c03d525104211813051742105050a250414030030140c0c143c0c40c81407507811204451004a00b4240000c04c0504140e014072100048002c0440e01100780f04000071643c0c498045000200704991300c1e00016a681d0041d80013842d84440c000b0014001410810b4100d031030036000000d080d00b04151950342d40b0584100c0c0000e2000030301501d0907614018035000b480340d003101580c4042c02c1e02c1020490006c1c0890307480c10010382403000c904080340406109401200101c40824080d2602340d8a4040030032003588075200d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583961699 1250 583960449 583960453
    0xb07030e060609040320070801060f09090b04021507170c210d0b0409060c050a260103083610030509030d05090f010c0804020114031608180a0f05 64
    0x41200a0000051020b01400c00107009003500ea4540c0d4080310822440700405d203070403580e10305c0b810a800d4208041005054201c001142c99030400401c0c950040044c0e01200c0400e05104922011504545905030000c1d010303500b80118211001500c4414419010000d000c038211003544006807040c1e50180003280e21110039501e229601c4135030388001040012588058001c05c000340c0c068905140e2100300d8605016101084c08412a10b8210494080784500004034030001400b0102d1a48400c01070f070550084103038440c3d1650610100c1c1c014110500004001850004804103a101881d00380b8120b40c012201021008184007100c41d03c803c01400341c0b47c02203000c003170588401c0d07000303005252040b0348501c000c41c03c05150080200142801503c02e842c180150700d132000050400f0b0060b1a0032168580300c80c0760034105480010100c00901c07804140000080c07062008684010000c1904d500691408007100d44a1030500b02051440d444011002d2090400d2a4204120403d6480940d4081d4003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583962949 1250 583961699 583961711
    0x30809090609040b16090515120c0c0709020d110c0c011e0206160e0a0e070e0f012304080d020f0d0305060306071101110c03071506050609040e03090301090b0703 71
    0x902c1540903042c0d400416056807603001414502440c8440100c4900e2880d241415695500c0420414031042850f01540d03840091030341000041d5406c20394000001e400c660b8642030084860316140c03111401b440301c116400180c0b039140ca200c15002020344c45480b17890107036216010b004045d07594030383d2061380d401708988031907030300307000c0071445404022514a0b0083c000ba60ba500181d01c0c500c0480402590510140360803041c0b0546070142c0c201c01401c54404010ba0300e0500400c0503080e038182e941814410702c000640005142d0707000441c508a880316030000701c1d900c0100d03c02c0c3e42142c00360b074004604a1107281d01001721030b030340002c240c21424509015a003040c004848118103aa9003240c9498150b40a040400c8400e8800d5407002c45903904071000064440100450a0441c1d00034045040258804141401031000d418116407080c02185c000b080101d2801c0045040b5000d4401a1071040b5990341a050000c1e2050080301c8800c00020001c00050702070b4682408404030503908280001d10b004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583964199 1250 583962949 583962961
    0x3061a0702120105070e0415150c0501060b041505090d08130303080604020f030615090301020403290108060619030b0406020318120409180b151203090607110a0f03080909 75
    0xb22840380291505c6d656440303075401100a000c054a020001c00d25141400640001c00c0101400102071809840c1d49404188045042c49030941d111900f140326484006c1104102040745100f40303440900300f40c00d1032510741c450600055403400f4240e001810040740003d1502e400c3c854070701d44209491180d241d916160300ca2900348400c0380281d8800410301c0b503080000c140c003490089111030f24415800ca2107454000c605c03000c00c1c00c1e84c101d81d008072003a111000c642203502103035189483c1c1a40841a440e0f01035032501c81c10b60b6803540c0c05844607000e90003540c980f203020311f000700300c050145070085414041d07800c0500c0c000340203500032500e0340e500d500b0000301407848210215000781d001c03240342045070500b8200200c02c8010a12038075103003c0d09001c203858200040300c20003d14401d90340045000707282c42003003060041900c502c8540b44541c0c0c008011848007030b0f940324140c403031841d040008228154900b170301044001c180741d041000d00c800c0c000000001c0044210041c000d40000b41c50310006070b1145 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583965449 1250 583964199 583964201
    0x405100f02030606090105090d140a06390507170d0513051b0604090f09050118020a14031614010f050c03030f04110a081b01081006080703061a07021201 67
    0x90318056481202082905c1056214001510742c0782c40c020030715104010107640340200e44402e10b41c0f1000c1608040151401d10601c0e10640118000240502c1d4407001d0101200b0118a0b400450b440c9a03114185003100d10340c814000d4441c4c0c00d50140c40060f1408440c1140003d9400c903607046401241001c0002e81001c4100100801d070580c400020081034400b080700710003003800c240d440f58101c01c05020010f69104140500d59264928520001b10003155081a0b130a44012000001c007000180d01d0000050b210b004c00c110031201903810b00d02c400040c280c0000d0400d0480e03014a503001d1000040403403c014146c882c6040180244c982e40a000303002c0340c060316503004940004010350014030000300c8a045c100c880070341c403500c6900410f4091000d080040c6d8948032640000086504c004182070740741884964100c2c16110908045c0500e00c1c0101310540c4241c82402050104540c0001180095009400000241c611070580740c103c0b120645030400f681c4c00071041030f4818520f2000c0c001c503403101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583966699 1250 583965449 583965451
    0x204060614070b0a151707090b06090d05010e0105011707150e0409172101090905030403020607110301180b0a0b13110d050703240506091c0b0405100f0203 68
    0x91001c10500701290742d1107081e05410000d01c54203103691103e1140000c4e00560000901500c1122460b040c50b041031003001e880c00d2015003112800f549403075034540440da41c450a0341d0701054203c5010000302058076109025100d000711002d1990708200001c1003680070900c10070340c0401c0e84001c6504040d682d05112040b00c0182d0003071808603450f0811710700c403406c00d90094003030315003d12040c003a201011070468090780d10154540140b942c45004882c08410414034003801448911000e00c0b41c034107652107254a07882075110003440355000052001c03c00c01c45030b9078548030090040017000745070303071250b80c440000b02482d0702100d1480301a4001400180c01384101104060081c1c580e220701283c400f0707444010004006261884442806140c6494055024080c400c0c20030b5540403410b44914030300e410b080c400d401e400c0c29202034904424402a10b58405035050004100c403046146541064101080b42240d440070b44001c808030100410301c500000c510449481c44082004401564000d090803400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583967949 1250 583966699 583966727
    0x30215090d03081e100f0b090a05041508070b03060120060601051605061003061b080f060a210201110a0b0402120708060921071a040c1203020102030402040606 70
    0x51000710030404244a03840b5140c2c455000161140010a0389500c0c02079840c04a681000c1984080c0041c0014104140b000b80200320040c0e1041c1801180400900503158901a41e809290307100ca40703514040300001240000d004070f0080d02c620a842d14000000f0ba4411181a80404c2518400e06101b9121030415110f070a1900c0142c80561503440045805a100c4079980520303098500c00c06010600600c00d0074011000480c2c2d8900745490352078600141c65205501004010b098104560700542000d01603a200b89100c1000000b683da5400003105000c640d08119440300741d02440c1d035041040c07482c250392024001d8036201a00100244484c1c2e8800f10040000c00301c181510116005041010034944007500241c00e90300b00388d0700c0d50089460f25000b2240707021b142d808010582000c80b20700c1c3d1030440320840b0002c011701c1e101c22626454501da2880c0d400760003900d540800181448403095140025180241c0d0401810009080083c080e40064a0903440f41e45840b100142e0f441c0103800118081c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583969199 1250 583967949 583967959
    0x601030c0804081903020f0a02060f100e0705090103060f0b13090c120b0604030212071d0c03130212030d020d0e0c09060d051510090b0102011e0b03151003021509 71
    0x44c603a40e0048801c108480c030200305154090050321000750781d08016220481040d8001c190510b0000e85030082004054072158010b140e0038014400c030920001241c0d442881810301660700d03800000101c0040100303620100f0583c94019012071200d4002c0300030a103c504841c9100289500c500144c81210b00d0f086540c00400d899140750321409419070000418588028030070f509080c0c0e2030b000f142c05419072150300b4905030066103081c0945190301120b100031504c03004503a58280703050000c6030b250388006000d10340381c100ea07408400d04650f584441c0d2a00c00b11940152600c461003440300781c0c040e40200881224041c10a0318081c028400020000c03048500100302110b60b0300d50700c0900c900442036a8050790b40b402200070000101c8001d00b178030380c01f40d01130000c44454145030040c94012546210105411079061040c3d01000003800c000c81c02c95005030807000038811142800007482e24000e5002078042400d504100031005851492050407a802551004071319118103001d8803c40c801c406a40d80d000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583970449 1250 583969199 583969207
    0x503060718031401050f090a020a06050309010e0d1e020a050706050919180506040e211303060204060f020d08010b3a06050303090d12050f0a080601030c080408 70
    0x41d2007045801a28400c800c4400d6145480b07884510303503001031904071202691180c0600850b08090000300c1d90082c95080a08041d60b40d55000960b003a8151040c0403c1080c0030011845d408002c0d840350038481d0b00d210440c2c10600d004500a84501c0941c8400403920404010b602810307800402c2d00c2d004954810040d241840c03e142e000c4e07030b0f56002804125003090386d00b0441c0c01c82d50398190203080608041d07036159922203000248141500e000030400741c015414104450010f01001075690b101c000741c09101a1920040c8000b00454041c00114000000d01c0150000600180381d0041041e201c0303c3e519440b5004841e0026a0390300c000d02140c0d0b00180504d001049501c448801800c1c04007034990741150b183c100011203003e1480010011030b0134901d080c28080c658482d0740b09113002081e054000e142020ba14400060030a034500e4030240810301801940c81400303110f0800c8a040140c02070380d250f240d01907080c0080001600700c9601c0c1c08070b40350402e06210035000d0013415210b154021009864 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583971699 1250 583970449 583970461
    0x10c080c0c07080a030801050f04020c0a030c0201270306060b0c10020a0203091305090c0907020a060209150705031c09020f010f20160909120804030c020a09020919050306 75
    0x2958030000c10100107000b89a8041119082440348081c514000d41c0d64017100c2d4105020001010407072501607100c0c61040150070380821000c111010300607058208003003498064001618034507500c011031040325145030110b0b0448080d41d110030040c2c9002c3d80301004100c2e00e48118865034810f184802455500003c5034141402c110780040070000c2891065900f801101c80100e100d18020251600503261607204210198400b0050002440b0044a08203100d040c0204003070748a41255001600142d00018100b8942d01ca625416060514035100d8560715031890030003584a81102c0c0c1040c4011070203900e048215007e074011000c4080c0c005000302c2151550f90300645600e85010461801e10450139418403020074801f43c10704011030f005002c0c1607400000d5a540c2242c5486030405445685420803400c04202c00884026503182035080072042910380d42810b4416038100c00c070081d1300c00b040a078041086503494000c2c01859800303440f45000b040c034191840000c11030b00c1c002c89805600400001320 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583972949 1250 583971699 583971721
    0x703170408040b030f04051c140d0e030406080f0a0b03030307030207140f160602030f030a0b03031e040311031c0806210102030403090e011406030c16051e010c08 71
    0x6005071040e07000a01c1c1550b1030782100c001e90011181d02e000c144404e010001801014483c00d4407801c0e14041002169806100c050001d01c0304102d02500e045003c20302c80010304855000311a60300b58501101c2d203580c0e440340c0042c60840100e030178440102d2010003084410f10140155040350764010083c60666917810ba0446c025002200d0554072040c496201e0001070000f40030780060703044003a003e0101140118200c2440034003980c4000110b40c400c110001c290b52100055030b401c51400312005c01c02c01104000280385001c1d41c144140300f41d0b102260408a13441007001081100c0c41001c0c8a00600c50320810542c40300d0320440084072070703064014800c08492003200c030954010001403120b0801c0140118011841c1c1400e08510600e85d800410300091603005000ca000034120801c0b0303a0348640c10300e1b4080d080000006d00a0b409604007101040015000b00e090354203104422404c009084200c1c1415070341c4520f000010304080f0500c3c1c0c01303524103040600540702c03001d4064943c283c0580b65603003004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583974199 1250 583972949 583972951
    0x209120c0118030f0f1e03022a0607020409020a05090a1a0409050303181207230f0a0605100b031f061d0d150c08091632090117060c070317 61
    0x101c80582d10b24003044a0100e0f40450311b01c03503010b80c0c000d08a00c503040320301c0e8103000b100c0b00640b2102c1040b10091801c90f81c580c81210482c075415100429402e0302c078804500c0703100440d0401d650041c0c8010401101c4811980600c0e07040044000d20070500e00c0080903c011280b05590250131604100006841ca01d0050944032058840d041200e40f680d10785d06545410f5000204100c41c0d00c012060007900030035000d0118101140d0000c00381000f4803503888429910501c21000030400da403544006030f1581c2d211003103240145181140305550f85410107921044059207c2d4070f142c0050031200c08513409118102d518201c01c0100d03103801103800307201d08104500c911060110f40e00002f0f0f00c003034105100140a180003008103512443c17954100f904c00e80d800d0120030750b0210188840000c0c10005210603580c0505842200410003420511602030350300b00d043d44d08146500131007400c00006032032400f02c8070645043c0d0341e40e040d40c090f910344c220f00d401603104500025002400000100c0300700440c0c1440b10b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583975449 1250 583974199 583974203
    0x50d0f021305070f020105060a0506191407030918050c030a0209120307060c0f02031903050c1b0c031203010807260703050622031d03010209120c0118030f0f 69
    0x20419001ca00010200780e44040f162030b00001d041000440c0001d809028154000804550000c0b0250811000c82c40c140640b40009000d00c01000f155004180141481d000402507600c110340d60300603504002e001e010ba9031003016a0007904c2c490009444035079204043c0100b205448240c990f8581c8030318580650801c0720036660203201808240000340c81000205010f40c403c610209610041c0f04002d05034801c290f401c20705542080001181d101601803004401d55814100001e00d80c8a1110031800c1c1c0c01b41d03000907100c0700000d865040039004006842c204204040302192101c2c3c0e4007081000c1240020312a107038580c1d1002000b400002100542074a010066004084c0b440e00800e02183ca0070016a0003030301c070b80d004181800084403980d48401c05c00a59403448a0782e41c0c20b43e40d4010401c03420340c1e02d803041700b81c03010b400a5110341d829012034a034100000c11030a1182070400daa01c2d11000307a8218980420b09a20400c0c2e0f04441c4401441d086a0700041410680310443d00d030449811420081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583976699 1250 583975449 583975459
    0x10b01020706120b130f0b1e1c05030a030504050106050a0f0b0313170d0c2a02120a050105011e0513022101061d09090712060207140d021006050d0f02 66
    0x141a03480e44500d215141417a03980ca00100d542d1108031640c804030742191240e640901204c0352100c456001c101e464050700041540c0c2d81c112206858207030300d140d000301840100540030000f44c6001240d407540201d402907014200800c00c41d07556000f0001c0e007941074420b0a1074221251010055889008040c592240003028000c85001c615a034180c180440c0035800e42c15840c011a000b0501e000038440e0350b071502e005080203044030942d02d03005403202c00c2c40254010b01800950340c200445d06c90f4010f00d04640f044d201240c2d6222407610307047e0f018000900a12601c1904804190244000e00265104a400c064030501a00b0860301c8854041e40c44905035005400d060407440305050b1005104d20300a001715a20780103c85018140071038030603d1a11078038424080c5509001c544030010607040101c40f81009590706100395454100064050641d010b03189400c02651003148803000b1503107440c4640e8a500f964181c0300b020485004460182c000d5540004005d2100b4000070007060306902c0c0c0e1800200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583977949 1250 583976699 583976711
    0x141806190905120a020a1505040f021e040f2f03071407020a060503150d02030706030c0309060204080d1b030f050a1709010b150301141c0f050c12010b0102070612 71
    0x1c0e540fa8640c4a0b000100041c4e0140c401803051012402000e001e81c48054800d2090341450b403206020801d001c031000e4440c8014078034071640300d2a0304400000000c40a00144200303044101c1801c01845015201000e038224888507948071301c10120884800c40c00d105003242152690101241c02c2e1841c085003a100000400042d07000d44d9549503003000921960b92140d503240362642c0d1039180031404c803000c980544010364481005903400308008003910800d150000c0c5011401900301d010304038812000d490a80300080124030305902150080444031141c0b0340000300b41c12510500040300c41c2c008060300040000d00719030700091155004040000365403505109810581ea104640803e040d6171498050307554003103186c41d40c180780d409184480d20780a401350540d0324010140301200c260304c0c0e610b48280743c00140241d6101c1d0220140ca4031a4100300c045480410a00d0038030b40c1d80002241040c82020940d096903909003050042401030503043c0e0242c2359543c40c0c850306588461741da000310000c2c2a2904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583979199 1250 583977949 583977973
    0x204110c0c0f061b2103040c09090f0210030209061902010c1b110a1710180c090b04090b0a0903140c0c0909100e01050610051e090310141806190905 65
    0xb108000d48007030000c0e5560704140c9004194031602740c0c05004224100400900410000d19a1045e01c0b5010340c2d042040160100c0c00710300a20600650580c0201d01007135605003500403c090300c1840600350002c21440d5a4414103441c03128800310803008803004d58484a001508102c2c5d40703101c016001d0800c81034141c640c1540c41006501d00348516696010625080509400b40a180e00d2071001c1590450b030012162900c00c183d480601900c413840b91200e500d000c4985440d0300034011981c00c084182000c1c18131454140140c804540180c2c0047c0140003621039620b003290880303d07410b81240040070962640800d00030241c10080000d405401950a4920710b0362541c00350000203840341000041c40d05d4003204000114400107028000c000044c0500942803038841000758004500030501607c84c440040040e10b449020000401c015081ca20000d21103c105440140a2808501040314200c04507c40315510b1204880004145100303003500203000d400b96028092080c01802641e12070310080b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583980449 1250 583979199 583979233
    0x507180b1606140a1515081b0a0804030216140904020f0603091f0509060f0c04090207030f0e0405070203030a09060204081605010f0e0a15020a0204110c0c0f061b 71
    0x14814a0688120001c100034002d11300e8410b50700c0c0701c1c1028000d0f502c02030070111441141e41c0f984213584107100100c170214807200030155514480c845041242c59441216000062506030203a8080300544100030903101845000d07a072150036185070f9811080c28100c1d22081010140e40034000781e800103c1e0315618207042e00c55400640c45403c0845c0103092190648500702000d10310000c840c82031510700400e1241001021601c40d4200038a034400e08000c8c0c4600707000c040d052055030304c0008982e2001401404054105a0300303519502c1585480c0e644061100a10040d40c2080350309000580040000801810070307075000c1102e25025410060400c3e841d020340d01d250070140c00c584003c19880c070104100940c3d100c074030032001d600a4030300b111500c2d01260108011450901030303120614001070f2508542842003042d80d600701c1e0020b2041c030246400d184280080e0b403201340e4800c0d032170081c03009030541c070300b4003000b100201d000141005142220b0300040c0f0200c2900440b0300b1071680208480030480d81e0310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583981699 1250 583980449 583980461
    0x80304121218090618110306010f090f180b010c050d260a020304120f0e0f0d150c0905040e1506030712030203090a090902012f030a0c060507180b1606 66
    0xe039103002544500380158100c42d1020060a0344c80c0e1810811800a100700031b109891b0080001e00384a81e4029a0180580e541900364100040c10011480000780c001440320035410365036648101040242c01c418011910407080e6880981964031105507001998810202040042e484100010709900c20003004401b094043e00d411409903004030074003052041924000090a2031810401c0400d16043c601a080ca000d001c0014410700d000011025143c440c503c460010603448000b03060310245501c104d0000340185d42d40310f8001161204045924207092140c08aa4800e0000900c1360110703100030b4202c1d101c07009109a030103010b01a80040c868030400083c41c420f074460b070017658480c00341c003091182124082d0701030f444c4103041006220141c0d810070000140ca1200840003000d031158a9000107001c550700d885281b130303440001046c4084982c007490050701a0303c0b0700c038140015114544100c8144c0749801000303c414045c0c40c030030014031401034000c1c03111162600070b06250300c1280c2c4451044903a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583982949 1250 583981699 583981709
    0x1020405060c0f0d030e06070f0c0b04060e0f0303150402071104060305151b04060f3005010b0a05030705160b01090e060703050403021002070c05030d0c0b01080304121218 75
    0xc8420042414440d007481601400404d6240030800e400442e200c03070b0391301d040160401c01030009850043e8100c070b00c03400c8881038090b0050070307000726420540f401100030b12072743c07081e410107001301941c50f000c25002100301c0e406030300a0b0411040004100080000a40c0900d000b1581c0c8040520308082d0390700c4034001d000c01140141c016061200c08a003022500010080405003a405185541496502e40300c0036542501c40502c1e04070100380da440380543d02c0d1a0140703503208202a000c0d03400c16000381c03a041c02d0000e40d0a41401440143d80e00d12409001d030003200910004900148002244140300b03001400343c8010203803c800803052982c80d9203001500a81120042075100c14075201d48460420081e40c201c2080c1c501004a45400d480094484002e9480c6e41103103500091310b5818042c841500d0300c0076150050596070240c00048010b004551400d400b00c40c5c0c1c6124800015030b0441c0442079130201c40520002d4144081181c0d00d8100d4040c3e0f200410040c003501b01e42040ca80c01000d20b102020740 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583984199 1250 583982949 583982953
    0x3010e0606130b0a0303081302040f0f1107170a021501080606040605060a210e03040b030a150602061303121a03061b07060504030e090a060527160201020405060c 71
    0x41040d40c288400b16000b41e01504445042040350407060322441c1e042e4080f03d415141040481d260000d03007600c0c8000902d4041c0d40603040803180c60f81c11080ba84504001042d800c1c0c2040130307034800d003800e00c1c4a000b00c0b400034100100011050004404000013065800c516105071607003007002c07000380031000c50280c02644031680280c0c1004100d0500340310b003101401e01201c546042449074200184024031030741c2c04142811070001c6000142c80c081c0c0000c0441080c3e003003502e40700d54803040510410780046410701c1609080c0040c882c041030042c41a1070070789213141d001d050180d50316101d5041c0d24201480403010030400c0041c0c024440414800d0b0700e07880001d0003d110110510508262510742c014011200300d183c1004074000c0003401c1811a001d80d035100364003080c1e40e519410243e504103c40020b2582107404602041240d51250b4400301c01d07150104c4180c01c510511354a0303a00c8105500684903070080c0d030100410b668140202802c2c6a41400344005890b0a858030042410381d002106009415 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583985449 1250 583984199 583984201
    0x604030c050606011d01031e11030604050f06061603120603030507021201020c030a1419050c010e030f071b03151d03090123040f0f1d0f16020c03010e06 67
    0x81000d002d4103070071600c00d2800380c000e50344001d5050311161103250210b0500d903031a0f84c0003800344118502e01c103040d840e04804002c020440d00f0117541d07907030040394650f00c80e5103000d00041122460f003200c0b9000e070303001030185410208221103000d0351208400054007030048992482c008012580900e4000e144a6900c41d6107a1341d00d4414066002c4140c00310091590043c400ca650b42040001a074404044038504084064002c2110034050310405501d03600c1401600141252150490002d0409466000082218030547d548035502ca0044520041442e901003143d01c01140380d4161704450303906080c06000c00c007940d030394403500d03020031f081c0e5210707400d9407a203481481404070881e81c0d100ca01c1508000d540741410000008107603a00c105070140e01c8182d1640c2200c0800b00a03030036100a000d0504680f8501c503101c100c144911036040c0b0400b845808203050720085a500b001819002d0040002e0000301a01d0b89079801046440c0780004608620801584d00c0c1e8907039090003100300c0507005001510803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583986699 1250 583985449 583985453
    0x40602041809030f120e01020c03041e03050c090a2a121b140f0a031407020c01090e0c09061909050d051f09081210050a030807230604030c 61
    0x2034800014105042c40c200304400425000801e41041099030314100302015030540700c0d03400604092108150561000c54860301d500701c008024070035140c11100844082c91301704441403001c2170a00000340150000c003810600d0b410202149600a2030b86a4042400d01c0703c0c1189002c0000c25182000440022000381802140c1040918420964a4134148214021080502c440c0c038420090a020841d41d2000144e82c4484213080d00c10b4a550340d4451036941c00e04c1e5000a0203404c10300080b913113129680300890800c900004828400c2001a181c0f109482c4c607140b4240700b210802807000603545010416035455680c0c2c14000d02100070911124084040c20b040001d2010400e600840d004030901010b0801240c400201c030100c003080003036500320840c1c240081c81c026005046004109000206030f4880062002e0102072040391140054a030301c5956404101006400d440f003e00380480030070050000c10240441010700c144601007040d9042c12007842d00e89448001c86060b000125081c0003042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583987949 1250 583986699 583986719
    0x220303050106200615030313030b06030d110a110a050d03080901050c04120b07030b0a06110c01020105060a120c030807050304090e0610060c050c040e0c0108060d0b0c0304170304060204 81
    0x6806510711003043c0c204020811540d2440c0241144411140b84a103450295808208543c4005c044560283c0d40360b40d2403800e94070452059420368480c0c002c610b0307481c4d140c074030030320340b14403a442a5030040110b8180c4d40c82e20907000c1a40d040d102d40100030700102040c6612640e1003e19058400d03601c84140c1d15041000c41c3c02c6484c09032801801600400040100300500110000b005400210400387d5803100d117001d40082c80c0e80450070b5000a0945c0c80000c245800c40c4070003004680b18800d4660400c00d800049080310b0044410a40c030548080c0b050004502100c651144e80344548802402c0a440352165101901700020071203499200190034013000b28035010300890350540d00000d121505185480d5488903415025075410452450310b03060501c48104810465a8800340007000918014031400761241103184542e40400c0034140442e0550030800d4498014a40001103c1d01d9611510a402207070b900141007501c007038481209468004080400460242d4801c2c240103a941c0e103880c504d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583989199 1250 583987949 583987967
    0x5010507020a03051209010921030819060909051504171804092901050a090f230a111201031209030c150305130c14060d02040f080c031b09220303050106 67
    0x260944030b8189001c10494501d44109c000e00350315080500340b40c4e41e0409009640e03181103100ba031205003006d0b00012480714607030000c0340d100e001c0c1d0103884031080d012840c0761040006850082040ac1510800210418a1801340441c014580810100514003c00040075119104410350703443c2881541c0000c603404a4410300480c10400318a01c7c03030740d85080000348074510f842c4600301000382c88040220a04150383c0c000b40203c042e04142c807040e101903144507091224111456070440d842d100351000000300381e0080d41c048070142480328013645e086031340d110004d8400b2010b03541805080080400011545407901c0003800c110030f12014501941000282030700c002502c081e940c40a038202c10808a03418244090a40700f0510000e0002c60501c03000c620b05103c0c81c80344808c2e05201180201c0c60070240e4804c00101c62444c0122501d00c059403042503140c40010720040003428081c0c002c4885420084461640100010000542c4d070540780f01c500e01ea425201c8080b00000d0361400180501600a110a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583990449 1250 583989199 583989209
    0x9040501060f0219111309020906060403020607020d020409080a0f080f070219051018201e010c060603060c03111c020d0204050a03030906110a0c05010507020a030512090109 76
    0x440c00c800006034003e0745074018002c810b0b902c0388a88640d00c05120741c2a0050103032084c0903018036599a45203000000620786940b00b24411222000450301a28050f415501982c0d002001c5a2034000305a08000d66000c00755070498000351039003520300201d010a07019086003665910b404502001c09240201211360003820300240101000500001ca40c0c002002d807c0c010f01c1d00640c2c52000103600740246030141d4062081040c509040020055403085142d00c007900b8802c80035140d4003901c03211080a01e404110b08150012141d003134000400c0c100e141031040e950010304051040d81150749494051b152681c100f80c0d45251a0b00003555515414480d5040c0d08400300304040c106015952011440c03148540c03880d10042d004a021060000076504450050800400320001c40c0c1d503030b29029000511620400000c90343c01d030304041448d8404101e4074201680640904038043c1494019105500500c0040e600442e03803401c0400091307020400703070086101c50100d06440e02060b8000400c501955000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583991699 1250 583990449 583990457
    0x50303150102070605122e0f290a09180b090f0103020112020903030417071a04080c2107170f010e100b120339060106050f07060504080904050106 64
    0x82004040d80c06420307204503500340a81c1038a25290111000d50001070350141152820340101940d600c47e044500c000c040b9803164480544241d607417603160901c4410740d003a4107003030031490595528418290700101603042a50a0002100d9103c1501005040d60014004907940c1c0e40c000010040c83d280d0f204035802164500c4408266041d6030000340610300652880c481c0d03135004030744680103940500694018100180e028500301c240c0004041e034507240c1b403048850780c040980c1c02540281604d400c89094800480003800d200800c00f043c40100c1003001d032024007170116403403620500103050180b10024100e1040440e030700c8040d540c0403070400402144607429607142010483c6d10f50408200d154003c500300303c000801041480c0807031409840c41d00345c0001c0e80000a2540c00340d1031300710711011940c5c500a0b868080e54280b581e280225034074481c14491030380c2c440c0c8010060103101c4c100416034000310940d094104201035841106803201034070f04591240000c41d00c528039041500c00c0c140101090300d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583992805 1106 583991699 583991713
    0xa0605031603060605010f020c0105130504050a0c110c01020601050d02031204060f0813030c11040f020c010218010219033e010b010302040b0a03050919050303150102 73
    0x3c88001e4509200400c00354803038140003600c1031007030b00148500c42c00d042c0107542a800c0841e200c0d0881380c0200b0007003031a80711401103e010340000c0e90301103040c2d003c21101400c50000c0d040c20959951003083d800c0c0c126070340000d2150464500b0f03107520400400c1c07400800e05009001d0540032950b40300007000503510b9402440700c481c606441d03696118944400b003811541d041d401d1000390003e00020292130104503018042d540072100140000341c2c1d40240300c080f00903a00328850124044e540401d43d074032001c81660340744103141003d00c040e1180c00c04282c1d02440841e41d8100141c200141c0e104035403001007061011440341e000644003120b1080403100c60254426030b0300b614032a0f40d420314040c200039500900030703601603603445408203040500e20213048000b400001c1c080c0c201d9104031307416002d0b00c414600507a04240d00039400385950f454482000a104465250068115400a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 583812949 583992805 := by
  have h0 := BRFrame.cov_init 583812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583812949 ≤ n) (h2 : n < 583992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
