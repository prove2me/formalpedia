-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:26:15.960657+00:00
-- url     : https://prove2.me/submissions/bfd52ee5-0eb8-41f3-b993-fc51b40aeb69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 4856122 ≤ n < 5035978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 4857372 1250 4856122 4856143
    0x30f011e08010e0102041401050301080a030305060609040906090b010b040b071509080c0109020f0d080909040201030f0f020310080712030e01030f0e0c09070f09050f040e01060303090305010e07060c03080702 91
    0x2030012290300b003400d6000b917110344a500c1f00700325070280110855000341b05890480380514043d0070316008075241030b805080003c095a501400130002d18001b41e64600c01e0407100340c0504e4001840410030b02c0d142d140c0785c0d0180c11086c00f490b03092004000003142102102c0d1400d90210a00f654100345202020140400b164005d1080c0f01c0170a43c005803007415805020528002c441e907400b10900c134428460242034040000d0940380e010003142c54141022120950414410314001880031048601d6400311a0030301e91603903c09800100b4000c0b441c003100380316000707845d41001070301c1c1c014079126a03114103000700003004061180030017059641c0e80c042d61042030900c15201040c05040c001031005903d8001003002c0702d02c0303800c7c0301d404158a1485010801c403050706030f46607174020fa07080100300b20f08200038902c16980710703444110b01c03541d2001c20302811000394441e40760b4240c514150300d042070a685040d4031280255008080800030f055119403030110443d01810301d540d0305e89515508a0801c0d0314001d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 4858622 1250 4857372 4857389
    0x70f0807080c0d08011202010903030c050f0303091006090209010503060d03090b07080304021809060106050706060b0c0703020319200f04050f060a060804020a05062209020703080606030f011e 84
    0x25442c42000000c07400c2014286540e80301c4d07032281c0c3ca0700705240588151290181c001810501c050000a00a04807050700a02827070403030302c1c024103000055203980e104492002054102148520035660316020b184060041d11405508001502c00002c5c1075000080080b4462070558002105160040030b600c070140581c0c07201155500a507083c00a501e030f0003030340c01324090344100c030b030521030030a02d500f12500540b0b00f000504281c0c1d03e05041210b09400c1140107403000e903075890700010445035044c01040300103c041d01901c98079195004043c1440700c0450b00d45e0360080c0c151145000501c04032542c400d891407a01507600000c2600e808200c0e0f070140c0200d0682c11600e010184120500b00c0c1d40c0b640e02c00c010071244500917039119601122102410742d0000d41040e00554113100514225029240300d0b0070528481041450030b01c040b0320300c1c01c0740380d203e007603510b034000350b0030003407540c00102aa0b0000b42541c40700d1941c2080304820504c030005201e204914103500c00e240d541c412020305500c004000a6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 4859872 1250 4858622 4858627
    0x90503010e07030b07051c0e010c08011e0501030c021f0b010f02060903030105040504030e090a0501051e0102060c0f070c0303050901030c03020f071202012012070201060305100203060a0b030403030905010f060b070f080708 97
    0x8c03520394002c1c4061100c400105460100008200c103001805e412200616400c0c0141e29143c000198094507400c481c26040d8081e20f4104184208040b030040c0c25440c0040021501c072400900261403005c0e020b41c90030841d04440c040000025002003203c0c119102a60f0000f140e075210f00307003200c2801040c43e0340e5070b10500c02d40601040602c10b4004e5410f079841154031340340d010b07a0a1016880194110606030240c1c0041c80052507460001c0040c040c0e01448410b075520309402c5603a1b0080f5109103400407404950701180d01c03101940d052040300c1c596082420114604540e562039166240101030000380f8013602c80350324030b410074400e4012820800b145010881c4040341e80d4180c1405030080aa54505e8220b5480000c02045c1705010b00360860b5004009044d02d55a501042c40180d48010f000d29008440c3c0f26000421100c510b00071407003140642d5001035603000070310303043d800c1d0b034444a400014681007030000d10544400d00112000242e00c602c403200000c850746090300315401078801c00351400720003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 4861122 1250 4859872 4859891
    0x309030a270905180304080a0b0a060308030f0906060303090a03020d06060e0a0b12060106050318030708030f0901050603060708010b0a02010609020301030602040e0705070c0b0307020f01050403090503010e07030b07051c 96
    0x364100ca405200f1450091254103202130016949004503c46d1060951025009002040d01e64410982144030080f010650a4907031701d41c0c1c1441da2058030780200380000003041007460750382480001d0704224101e018514052013100081e6000c2c0c245c0c000a0703c98480e5808210801466a10150041c614446882014a8101101c03070042c46c40e0f0b109540568116180c250503054080384040c1641e5154880714199210f03506070341c0700d201c50142c2d0b10340944001c02c1107001003070540001e0340c13161140c1c0c2030840040c40c00010036825600082d20007030180e0320035401c1c400c2440c0c200380903a041d50f10840c041030715003600c2e000403409071041e50301860b0850310010000c010310096030000d100340d400000c040e101d1034642d8035080343d85200b4000041c0c40790304079a02c14404040e0007001503410440a00c11280104603014409003100d41c01d0f02d0842c0480d041f80ca04000301d00302800ba86c805070120340d020f4003500703141d0f8507041c411100040400d03040100025510f051500c0003054040c1021480d0010401e103600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 4862372 1250 4861122 4861139
    0xc0106031407120c0905040c1701050a110306010c0803070c0204060b03040209070906080118020409050a0902100306030312050702010e03030403090e0f15010309021318060c03020309030a27 83
    0x20007005040d0240501070010907400100000014401d60002190310101e10300325401d0010200600101c8401f442604001f82d01e0405400303403506106654000201d90078852003090883d010800310b8045254240100203c2d80e8100800706181c43d08268001c0d940c0d43d9041085a60414a290080d8003510b0000049000c003c030402641c80340740309451004c4035888208065418055a205410010307a030a4010f0021482c0130f1111904296040005418241c49650040550380c04a441106459441407980207624100c000246030b104541130401c100d0b81141c400400c0400c111990110740343c0c4640100b203242c2d02c01d6000301100d54424003542d0312800c01d850300400d040442c5c850440035205034004140616901e040d10784c0100c412070041c0e07116000d0309006402400c0700001c161f90000c1510031a840840080c0248460702c00c07451101c01d24002940f902c0c60846076504e0002040602c140b0401a51000004c1102c0c02c88465081960401844600d4100180200f520100ca0450565400a201e06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 4863622 1250 4862372 4862393
    0x8060f03010906050103060b0604081e0109080307050c010f0b06070b04050304030c030503130f140405040302070f060201020903150f180a0609080307030c020d0927060806010f0906050a090f020c010603 88
    0xa1080b11306020fa507040504209c540d0045001d481d80d5504000d0f04900381002051140c190042e00600100305080b5030f880d80100c1d1742080302c86101080e000a11100580340a01c04c502a44c90005c40422102280c000412003034016060010700080400b0003003014004c0c20426600103540c07008400407500d4407031610302d48039005040700442c11007502501280302c0c0c0d00f4650032029101c2d400c10211042ca00c00c0104005408040d00590550180c0c0401180482802d10710300040d0215800142e520100c5206140c506070422034050100720000090142200c1c061b440e068212888112844400e0070456040d070800320200c000801040ca01001d00b0f00b00240000514899802601c0402040707246400581e211100d410490300000d40030318084c030036040c400320001000b0102c00089014582c080d42107a085811581001d501588504010480080c1d00940c00c400f41003044c1e001d000c1285800701145000c0920300450304829142e83d400100f00310303e0340c1564201c8071074400920541e542c07070400d1000c06 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 4864872 1250 4863622 4863629
    0xb04080102040f0806040506060103020f090a0e070f0908060a090c0909150b0618190302060705010905060106050a050409020d11030406050402030606030c090109090203120f03010602010605010905010f08060f030109060501 97
    0x1035801100040140002c14006c2c031480d0024080c181c00d548031401100294400300000380b05481c01d006024450300c42c800010082c000d84420b48050b030620b8070001d00f02d000e030848403c2c1040300020f018410311030301050aa41028110401261802051800c04c10400c2243c000c0d4150916000b801c50a12442502d0380d9100741c00340f6000c000481680041c0002d0b44105400301c000e583d8601040491030500e10000102d10089000c25005162a48d001a28541c440c48056600340c0d100c003003200500c8400e200c1ca500400042c1000d51806141c084080c2103409284240354034207030b0218070b004400d14190040507824800101507a640d18191904000902003500d0581c001d01c81c100008a442c1000100c5480206005024102c507070310306010b41000d07140e5400201d0300750207a48602d074024210000034215a020301c2c1d04040d16981810002400c44925a00903810013509400401c60359070440300121829042e03150503942590b4103004105080b8401ca1b52030780640c84c1c5110002032140686c44603058 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 4866122 1250 4864872 4864889
    0x12010518090606010c0203010204050a0305010207020f04150b03090312040302030a0306080c0105090d0f020402030f070e0105040608270d0c0510020f03010620010203010311010e040905120f040b0408010204 90
    0x201690810100500c84211107000d5154054800700c1c00700c0d0300074911040c04600c010005880c1540301e001040182d06075034801c40d40c0d607402041e02c10442c60488a441c1044400b0766080007003580180c290300d520100d51042d480c0c1c907600003000ca849100140100c50807000c007030051404d0760509180080d50795201d1100391000134503003140400c0b440703400710310141000c60503588c00703043c81018010415080c2c1781070710854009064400c0c0c3c4005031944c0c00a1403041380d002e04079000c0c5151641c0087c202c0f9903490940c50400900b0042031141580180c69150800121038010803400c107003d41001000070032001154927403244003005403595910000c0d00c4000f500c54402d036a1100c0300c1d5031128050f070181c0701d94414081014070050050034403070084a1074420704502180c2042d00360a0146089034400e8206440c0340e408881070a5155800c45007581250070300b40c40030070051055444070354441105070411003024000054145481801005031070107440320500c1a5034803540d4000840c000e6100f44a030240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 4867372 1250 4866122 4866139
    0x6080109080301051e01020304050103021308070308120c0403050a0f03020f070305030406020c040603020a0308070201050d0f09060606050a020a030e0307030b01080106050103050c070b060d150504060608010e030c0a0b0703060803120105 103
    0x7240c03811740100c40001c00301a0011030500c0d05040c0150003a4101c420800512408402c0000700c00008114400085000e03054190303030740c080181302502c1c150004182ca000d1007010401040012000124545565080004601001c52a240480c200304a64080700d5281c801c000010003840008001401195120780031205d6035909141404240c1d589403101030750041046008201240460004107a011310500d881e13071820441d138107020101c554000551300b0055542e1004010024a481403401402031030500e607041c80e0140314001c0d601e03104640000e04120781c07285026400d45041008602540e40102a5002d540e16528918020314051141c00d0029090001091680380080d048079884c54100014680720b5039540c1c02d02c1a100103814088410700915000c2c1c4040b00314602c07410b800389210302804900e60f460078036201d00395400d21160031100e40040200352114140060000d00c0c01758008141101756a548406a005006590040800d4000001e40c0030700c044650b211035050f074000700c84160 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 4868622 1250 4867372 4867399
    0x2010e0705010507060207110d0807030806060f0304020f030708150405010507090602030d05090321060906120304050906030c03010e0a030206010b031605030901110a030606201507030608010908030105 88
    0x5a40d94641d1103241d01082c410040d00c2c0108a80e50010016103001b54000803c4441c01310100e4961107071200151010a00841c05104042d40b0807042a0491f50440f4100d01345105404016400e20001c0d000038811720500c1d014810544050121000404800f810b99050a90022445190020031a01290035500e41800100c2090203401c0ca0402d403041380c0d004504100b6403039200d80c010840030304003d14038481070090188410244142d0b103aa602001c40c0714105050010501201c2e01015181621844403a591071030180b0b000415078044540440b4102826102d440210341840c8040100315015400c141000c103065070b0000f1078600b95442582124010f80e40c41e0304081d810700080d911000080e07460181010b05c2442080615000000000001014032001280480c40c0c1d00080050340401e44408003001240d4101454100300001010340308005460b0708015500c8230340c07515400890950140102d010507110394041d502500c080002004454402d04040f009500244a40e0713206038100300016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 4869872 1250 4868622 4868651
    0xf08010b060705060c0d0905060103060207050c0a05060a1b0204020408010207020a090e0d1d100e040c090503070e070c06050903070b0601020d0903080f120114040e030403080405040f06090c0806010201 88
    0x8520340c54003c4068180f0340c035800c4040314658020310300c0c00d0f400b80e01c5000c0c150120700180505802036201e808010390720145c52070b155041120a4080d107101d0004501c041090b078a48004550140764030b450039614624a2101145035942a8000a50018808140440e18403030560080c4107641c0201d5010707209a03521444903054401e40030310402c041d0454607209013228059805c86804e1408613078520711468003030700450381e08501100305400003503100c1003000081c1010b2040391403103501c918214032094148804242d03650818400c48141e00c801c14000380140780b04030100c02900b94441d0040c08182040a541c1d0b0380c1e90000041aa001c25008020401b02e42c0001504c5201d90503503112661103902c0c50b01e0368401608002807008107000100440000200f04e4900d0740e010b030059204950411400009200c11a65482581c1d40310303034010001417004c218801c007510304440045030041a000c103d9410900a0b0a0550121200c1750030882208603a9401c507000601c912401c0e4000c00940210240d078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 4871122 1250 4869872 4869877
    0x7050a050c03030f0702040207030e060d06050a08070614030903090a0b0304110a08060f150604030c0e0a06030803130305041203030c17100303030b060c060709031703070e0607020406050a0f08010b06 87
    0x3503020815080181400500b0707d40c000c1c0c0700d828001c0c1031200000b02084081102c0707922044a03000f1065030742c07000f40184d01d000d0f08188043c0c52600c004140c078504001019201141c0031000300542c003c0880000c8000c3c0e000c0003218100c0c5006072850340c03019a111091031140c0c10545e021a028100c4800603550750400390128411a8410001085c0c1c46c3c41d80d0214102008000c2c00700680410107100c40b000d1500d9100080009520030411441d07020b00d030000d54001c2d050040c142c548014101402040858010800daa411030400305001810b00130314a0290b07018415940301f9099040384410200906030564000f08085a103910350394400e9600c91b803001d0030313030304100c41c2e40040c80340000045c00868400e0b4410f404071400508814a80b00e5402081441c04408840303400005039050810710030410f00510311604441e1081c41942581409100a451698a1100c1a000f00c2c004526142950f603150480001004040c040340c034100d440d0b200004810480e070041540359801c01001690b1410041c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 4872372 1250 4871122 4871137
    0x3080a0e061b03040501090204020414031209030312070203070c0914090106030201020601060309030c0203010608010501170d0c0308070c0b0c041401141206030708010509030711040b03060403030507030e0307050a050c0303 97
    0x641640700d82d045a2100c0c290400790040c0d44540d0384040001c0181c1326840104042d0240c0c414000111240388101880d286a0503801d4440324010f02c030050f0913071800015034101c4001900150b1459603100e07801c03843c501070781c4009060f10702c100d0400507410040364010240080701101500d456030301c400d545401c1c4d54484c84001d005a0040c00100300c081d00c6580b02a500038440d00d056182c01c007881d00000d094030855003241a540c0d40d0b6174010850f152100b002d03002ca01b80d9440141a102c1e03040348016204100a840c09400d1240b1303e4001101c01b403091091101440c5d00074203201e61800e1015000341c02d42c0050160100001044410090030340c02804081c07050841e58484610740804084242000003026209039007520610a020a81d49028094948240d0b0300303c2c01991600c4890070844c101c51201d01810380560318140c04044140c9000c51841d510541600b008906030315240c400303c0c018401c040e0401d41d18000480d00380f0400c2404030b012003603640101d01701d6565034081390400d07407644240d81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 4873622 1250 4872372 4872391
    0x20901030303050603071a0c190b0601031d0303090a020a0812040909030309020a03061401050402041d1005150309120c06130203070e150307060207050102030f0304020406030c0303080a0e06 83
    0x1401080042c1c881d8000303560003007000c1c1c1502c48a950b2900c084403804030380082002441c030080381d01c0b2810301c000c028206041c5a0354005031001c035004d0b02e4250445001800c91410146c403200d111808403841c4010145421821f01169680c2c41c040c1c8116881c2c0a0031031080b84514050307500020a400000f45000c444a0034100182c5014603080704c460090440000490a16440754248405a03494040c2d078801180182c2001c1a0741c4032303941c0190180c180580210344501e04c1440244000c600c0b90140300740703d404540103010180c9035200e90391761900580d8045d40d400104108200c40e400a140040c500034650702c0101c0d1444401c40d46a106640070390140060b032940030600180a90102c44040b4012500160540707500b01c0c4c481e00039101008007111080d1088a03407045030001d500f010002400249544e1010341142070605000070340702c1c4108041c1c418074020100100341503540d1075100d00f00a503408001c62040701e94928014203100c00c03c071680050f0a1500064145040b004110180b0505005c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 4874872 1250 4873622 4873639
    0x3090a0e060a0e180616020d0f090306090f0804060309140106080a03120609021315020a0309090906020c10050402031006120303020703022d010e070e0604050903070519030e060702 79
    0x115103c548000001c004903800c542d030300384181c0365210610486001c1c503902c200c240900c1d090000e010f07180c064185214000c10800c0341c1d100050580c880500010349606c20404a148101414100c06020a03860b014107610800500051801d030141d00001d0742d284255071220301c6880c04803045080303403082e1007078a017550040960480064402d6024448001780035100040c1c4988a4001d07004a811000c242c1500501d2820b05100c5103102d0603101801c441244010441e0300b41c2903a000f031145680f8441c201001d500c032183c43d000c002d41a0181c4070503000407070807103d40041d20307070082004e40000d4409034028025600ea1515401c00d500031141a1040f2115102e90a007590f40c0440007503101c10800c1d0118040c11100c010084403e00c488050075080c04115840c50140300c1e2800e0840340c0300b11940002e5404842c0811132076040e59005a8031840c1110005030365500c0c250610b065110b1080c00030418040c40c1c6000001e1414046401c2d9800e011340e80f411100b0801009028883c40781c18006075010060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 4876122 1250 4874872 4874879
    0x30f1406040b1c0209130803010f050f12120307030b040207080403030908060f04030f05070f05100f0b130218100513090603020d020405060102010e03070302070806070203040302060d02030606130803090a0e060a 92
    0x1405400c0d800c071400e20542070342e80e00030347c0340c035a12500281c00403009101c400004010524140c031201310442c0045543e0664061083c4240c2e90b02c0f100486061f00e600c40100001d0085400383d03000a000c3c40d0003400656807403100c0e14242d90185d12a0204801149001c000410241070025007940b10344400f60401303149842c2d0352016502c04001e180c036202042420403550001a5060146200d03441c490001080b82c101444426802e90f061400400d030b8180c5040c0e0140440d6460411010205410742001039840c01c20600c40c44c454100d620a03943c2000014034000881340c0e03c8001040c03d802ca5031725103c003942d19032001d801641d16030301c00a540002c160008a015140a9203e59000b0605000001d9528010190310b41544c005034002d0300540c01082d405c1000c44820701c074840c7d0280091000d0345c0f815040d5070018100c0d004101d00e1a0354070740e020001440c1a00c8072002c86140019048072029034a0796580350130350380c2c3d10410b00140900800340340040d811143c8202140207040041c624080c1c2400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 4877372 1250 4876122 4876129
    0x40f090612031404090c02030a02060c0306010c02090a150602030301090b010306030b010302040216050d0203090a0f080d0507060204080102030c0702040b012f011d0102030601020d0f050a0f030f1406040b1c02 91
    0xf552040b00c0030f101080f00040300c0c0001d2080161003002d580241d5195148e00401030b0411000414440d00c000c01003007007000580e0b0001420316008c0d4100d4071900745448056452004086081c4041d811310717070201c40410a140c0000186040300c0070404140402030041c001142519083c1c44006d00300110b6100600040c5019005880300d2200d0291009400344503482d220310704911185035a000da080050004914104a039459020305000000c1c0c00c2d04c40d1030210311950303135440c140d640020003802103013100c20032405804039402800900c000355101e04005031122119031225004900c96460010741c10501e50088484042015818401c0075880c2e240e10499001c40d0160311102d81155038950400c11040b241243d450503411100c000180c90b4985540060701c0c03c00c42c3c4503584248100c0010f15202c4c26400300c21035484034414641040848141b0100398041c0a1260b0b4000781c007030400102075000e6400e00d10440c40750108a03401d0046031a01c00520200840f940c0f00c121312800c0e8294003e01609 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 4878622 1250 4877372 4877387
    0xa0207050303160c02040f0b0109050f030a06110c0615090108010c080103080f0c06010e04050601081b04020d0b090f07030b010504031e051504060510050411120405030f0703020102040f09061203 85
    0x80d582c2130103400c901d0103600240c02c9612030000322640300c1d42da8050000d19648101784034081c010a4030605d17889508400040d50b6004944801805075840380342840100350108196840d024154045035100e0801550074810200010002805654408000510214140558000994141c440c2c82040e42140c40d601100c0c0d00800080c011300300c0800c003100025404000281c001e0452400042d80c40c100342c07078034600300b00040c3e0001b46181e0101d480300399101e5071300c10034035800d050444005959444229500c4090409040703120360000d4204200305032038000303000b4180310307224a40c1c2c200110785c448001515540581d0002516000b084441681000071040843c0c0040703002d0012a0400c0c0d02c3c21011078021082100d04a44103912030741846064400b03903091101800d4201d030203210443e0b280c2034048690040410140c0341c100b0b0703140441c050180074401c8600c80700c0c1c0e40462540d150102c1c14040d001c2d40c0180318a074422110101e0005149000c0d01c504010f5410000101c10281310380c3d2001c44521 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 4879872 1250 4878622 4878661
    0x2030708040f0204110408031b0304030209010b090d02040c0804060b0103050702030405040515040c11070906030b0c03130b0c09010e09010303050f0c0c1011010b0d020901090c03020903010c170a0207050303 90
    0x591785001c0d0407500c0400102901c01040c440d00190356549070360a401d00700d42d050f00e01d0800300d588140300600041e501c3d10885415200101c4165031140042d800140c418140d080b0041d401c186450003030410240d00c030502510550089209002100e80e10b80114211001100c407000180c000384018401c85c501038000581088070321150500054007200050308450100c0c02c040041405500b00e00d04420041c0810001081294020440e00d440c60300e4a07684040e0080c0002c0300b01c400000003d01205c011725048110680054045000e4a0095581d80d280e6108541d103c0c0450b1146907030714401e2404d654518142ca6069580b1424240b20000d01001500002c48220b014000c1a0498a02d500c50070504100c400c1030f85e0700d8025049018100c1801c6034902e482c29030003100c402d0b4200e405070b00c9882d075160458134514400a440391888130124002e018000f09a903040d42071621a088441e400b50fa0101c41c0440c03a41041566103c441000d012403158400c010002d42040c40010701d00150102c049001c4c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 4881122 1250 4879872 4879879
    0x90f03010207020301060e04020a0b0307050301030201030207050313060e12030301051003090525170a120807090e040501020306010206071b02090c0409050a0509010506010903030905040506010905130507021002030708040f02 98
    0x42c404150700003429a81180c111480b5807452004110551070090310441c020b10112180910351304000b00c0c003d00d9440140130207030600d40c001078010b04002c01081150800b490b50300001c061192584030050003d140b1200b498440c034400040c101c2c85d50004011241291001482e101c014401c0c80c2c0e00758098101c010056400e40610301c0030409544411011007a1840d4582c0c660302103074240003210461032074035640744601d40c1c040d00303400000403d0340d0350060552844d4281036200d565030f0350048412961a0700110304625000042c0001c008054001e98000c803401d80070740303056555586084800e00050441c00705101d4107032506502504003041c003d41c00c000501801e40c40d194a80f403080054843c01d0f07860811203591a401c0000c81902880b55030b0b00000d0910300000564556100280650314900825129079552070201e1056805880b49400510010300044021006505000e0042c40e01300d44403005402203c51ba40680e90052084910441160303c0b100d00e607071120380300d1800c0320f486540120380 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 4882372 1250 4881122 4881127
    0x3030903060901021306031b031d0307030903020310020f04120206040302090f0a050105030d0207090e030c010c0804030905040501031203090215030a090212030304030e1201110304081b06040206090f030102 90
    0x149031001d00495110b100030030005655070b101021108110301c0c1980c400800c00d842c0130b00a8235400c0700d05e0400d091450280c40d01140d96079545085c9254802d80d0507413181d1074440040c6510416401ca45101c0c02c480c000c0381070b1804100ea041c10b91081c3d100e468000106207104010a01000b24070f155441a02400680081d0910717440740d010804001c0262020107600d500d460412103000e006014041c0540410b80c0a0036010981d0840650340314183d010701c15240f80c0300d00090700c941000300700340d906441c40c0034001c2c804002c1e400405030440c202500d003580040e682e400d0120301420913020340f6040b66403156114600c10f0004604070300a120101317049038885d4180401800f8480c984000d140503803000b03c0d00090f04007a82c4100600f054401c0d2001c101c9410900800c40404d420500c1078481d00002e0303840c0541c000260018078010302a044030403080200210a21003030040440161050500b407000c203482d113400110120307650f0841140c0c001e600400070000e200040c100603071f201541c040e01800160 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 4883622 1250 4882372 4882387
    0xb07060e060106030b100e0102190f0506040f030f0305040507050f01031404120905090906130f0503040803090a0617070e040b0603130303050601050304030815060d0c0306030c05120a02040b0303 85
    0x3401e210080e4007841c0000c0d04e034006248245405001010102c0e102d09040e80c0d0001c4400020b900c8aa1020008840b0000504810309002848810b0407075142c2c0a0240da04626042c609004070f03005601c81940040c251841d490b035014028852107024030340140061072643c3c40c3c201003005580e083e4030320b03504240d2a01d00c00b8080e10340b860349483c080c9115841c2000a81951701000b400602540e125030310402ea11400c0c41039040c0c011960f0b0b500705008800c4200ca12469040c04528070341c1d11000140644400140020740000101c040c1c1401001100c1903486590364880484104903030340301580b107428024000c00c1480740650048480e40324060004a0900841800a0165002200c8400ca60b41004060408041d4180705841e884502401e102d400c40c106614020100e150050100e001500c0e40041c002c080d688070b0040d1a60031f00006400d018542c6030b150010042d100c0c80c4011110101740102c081024500414211a2015450010450000141c00300406402041035184d0140810400a07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 4884872 1250 4883622 4883651
    0x60209030d0c030305090106030c050603070c140606030105060d051005070207050a06030501090c08090307080d0207080a0216050a06050d02130905010e01030308090601050607020603090c190f0f050a0b0706 90
    0x14241a6210b03252a41da8454608014040d100002d00b81c0441d41d02d003440510006d01840d480d50141c8a059416a4695030b541e80705941079004030310050002d818102d189500880d00041c8035109075030a80003030295459060a00c400c50195406c02001500f28040007500348009500c141d601c07001a20444101e66030301c001144004c81590080350000b03441c0c1005004405903400b4800402a0314030700b1600c81d1070014603080d128040d48000a15080b400600403030030100300c1d015074101d203810900300740e542e10700080069596214440d0042ca0758403482c1d00000c00d89850780c1148101c84840d2034144c50107485a000b0b000a51001c5500055540b03000804034247c440c0b03108050103442080c0d071240140d4150b0901070660390740284802200d500c07030700c014002c40e02d890701690a9160306444071622038903490460343c01d12112003540c580014021040510000c40c042850044802c10707642100150748802030b0810b07404140c0a0a5080b61a030034013040340c1d030840d0005000c454001c42c0002841c6c0c0c10300114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 4886122 1250 4884872 4884883
    0xa090b030106030c020106080606010e09040807150204030b090a0803181f020912030405010c0303020702010302070b040501061706130305030603070906060e010e0924060904050f04060606090303140706020903 91
    0x40d00090751140141104e980910540b806400d11a0003008540340010009007285581c0c000c01c3d02400c0108041800c100e0160280d60b00e8642c400d1850125031024023141700290401d2005441c0c00344224046141c5040c0411100101034001c0b0030b04d440c44c2d41d002d6001c8940001240c10002030320610b00200c030040240707401400d50000046000d80d0b1021803c0401c5480e4203240c08844541e0001c0008028981c0c211000300718a0b649800c2c0541c542c001c17800140c000f40203202c805402c070700714032040004101c010750140c015600703249901000b90390441c401c5591000308803601d25a292020110704040381c0500055980803000408494005848685650903070300a544900041400c01d85298019a0807610240812005807095003051a21400d04054070420038040d01c5840c580130700600541c0c0b07581086036940d40001d8814405814005510b0b2880b840c12a81038034514500300001c41c10512402c084403c42c1d4050361289185103200300d00e41c40d154403005046507aa6401c00c20240c454030305015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 4887372 1250 4886122 4886129
    0x2030a09050607080106091509080307050705210a0206030411030304030605060f01030507021c090b0f040f050604030803010b0a020a0b070c06050108060910091707080711030d05070303020a090b0301 87
    0x22461039160310705903150003400381045080c00340a100500905611108600864a0400303070300220006205083c1c900c1e1706143c01c20305290000207181c4060140002c0c140c8102c03441512010381c040840812002e4100031320681e20500d40004041c44054035080c005550454015840e20302280b560800080c0385071701030707401120001e1301c8004101c010b161003184290200420300301805140b40085000707448000c1d00c2036801e188510f110361301012520134061440642000d1500d980d5829003c41000b03010740261140584103c4551004145410400240c0c2c0031280d1110085081d64204508101aa0040c1c00e81074214441d201444002c22011800d682c01001d20740c540e84100b001c94101842036030016002070480d5400801407015050000805004191144000040209691134080c0c004c0900c1546d03041000e40209003a414003548500a09141d0b2080c500114500c50840526480324400c07000d06003c540d040c418540464026001012800c0700d600d419001c0301d4840344009140d0708281c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 4888622 1250 4887372 4887391
    0x806010f05010e01080402040c140a09050406080a0308010302130b0409030915090602070b0901020a1b060f020106050102030301030b0c07021206091b030307080c030409050103030309020f18160e040203 88
    0x10032180309148211005072400b0310f0218100560040041c01c00640078000a0181d5500e04807120388030711510216000c040f011307100995414010340300814403000c0d030041074411480e054000420410000300b8440c265407603161f00105a1a680030480200200701381a0202526003440440c0c036a1680308036900b00d84030381c4039190403a042030f01011490b0308958500d030610803118424040f0580002d00003044031141125290ba600541c80100e041855a4500030b1045d60705091418903194a1a1508140c1c0c1007a50f610342040c00b6103608030300b07840352031181502503002080140003103010407181a6200d4421000d1928100113030b40424101482014003513038a0300010203015510300c0900c044032401d602c072220403003119805400030341c89101d0050018030b05407001600140e0020280b00355070040c80d00c01000c104a682d07909002c0c0141180b18001c038441c00300c0502c540303000c2c0391007000389002161101050145613100c0140d20340e01a2000f403000c05200c00004582180d0365140000c610446904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 4889872 1250 4888622 4888633
    0x5010f060e130507090c030f140f0f01150309020f060304030305040b06040204080304050618030706020304030201020706110d110f03070f1101080402060304060906060b030a0203091e070e0901020409050108 90
    0x41c400d15120305000d000520541018160200811030008541040d00c0c103142c3d0028030a080e0404c25070092081183d0301030180c0c01e144400444090512425104d0084101107144540e600100c61190a1090060140004902d02d043d60f159110780d200500342c07032005c1c10007501c072030f84c2c0b200141054208550880c0004d842e402040200a05086d0135a0071000990b8154209030500c18000d46034021400786a01541700840c0b00e01d05180a8100302c0c0401d1005400e8504c1280c035268001d40341e070302c2400300ba405403194260014460b03120305c0318a8400a40d00000c0d01d1010039400045a050143c4d162850b840d2180d0081600303812014001001c440b88181d400584200742881e0424110040d501d5540c140300952003040f0140c1c640c41c045070340c0301d80d0001e07000900f40071f2860804020300550700119580000402004000c060580c001d600400e070b14001c8030102082c0398111200c1c083c00009400890b08900b104100a0320706946540c1c02c588800c002500b401c0d1911701c01c100b1036000f43c0c401d042c1c3d940304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 4891122 1250 4889872 4889879
    0x20a0b090c0f03010608030702060d09060e0f010b01080105010804030c05010609050a0b03010f0203010b0301060c0f080301030803060102061f1206020d0504060207020a09020901050306130902030a050616020307020306040303020c0a05010f06 105
    0xc85a05200c158150024041d0f1761405001c1502ca01495802a005400002e1186a1400701e40d2003203004039070154003005003280302c1114580d0740460240142241d03280051980d0f0540c06013a03018101c030700580d51b2595a030743c0d617601141e2500b80414221600d641740d18022071303c001d43d802a5071040c108500002602c33611042010300f961007040d0500300d130310b20420050001d200c08038200c1e0b040d261103051000e4141c58910344400800d510a2002e0603114020002004200d9600300950055000342d0032a0f40c59107070300402600700312000210009203941c11108000d01c0b00f0f44885981268041c9000505080e00d2141485c1030b0b4100700c80c00c4a0031640001e5840031451302c1b03083c241c0945990b0108508002c900c40001c0c044d8400581100d104150030402901240c50681080055980c054181c030010310036450704d00e648020554908000051155050b1141880041510744240e001001801707581c490307131015002940080d0b003008044c041c0500c1003010417800d014054981c2d9030b000002684a15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 4892372 1250 4891122 4891129
    0x80a030b040b0a0e1005040e0706050f190302040f051906080703020d0501030507030204110f04050d0609120309110105070b0a0902180c04060e06030105030307030e0f13060503010c05070f03030c020a0b090c 90
    0x217541e04610b20462034004d44140020f0300060140c01e85803903092942d030b5800000341d01c1e032850080440708010803161080c0601c041d64181c01400440d4007954000942544800400004010b001310292503040303c42410810310344115043c98200d1440d003001883c140601c2555001d0f03403400d0300b080d50340f54410402002182003a110b0740801c031401f280107504003402000f40c103420344103a1090600c2450068040c03030501901d40d00c28207074164001c555992a000414000d005000c5a50060384e5136050ba603452400703035025a04031800e1541c001780e51181a95081010700080100b0041070b6003000c55090b001245400c2800900d0040550520700358540e49441001003d00d502036005900444061004100944002041c4c0703006d0359040c10041e40c001f04500110707041c090b03d240704907800350408111241c0b800350b40e071140d070507140c00f5030083c030a80180d0082911244600074008241c280039814800111b8440d03400865101107500c140d8820aa458440da0018071007a0344184560b0000d807418001481d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 4893622 1250 4892372 4892401
    0xc060601090509040b070201020d0e0105100b0406050d0e03040306020c03130602010605010503070c05010b03030d020909010803121602010207080a05040e09120301060e0114040f0e0112080a030b040b0a0e 89
    0x882440c0039111182482c01180c003e5030041e00040c10b0880310004a400d6038002c1d0191801400450070801030503007144412400703410103075682c003000860440042401c860b140301300e600362030705929180d14088107000c048005010f0203d1000c0360b40014880400003c2c1c2c20b000801d000f40c8020020f41d161440000300b54072880c1203034000d01c1903a01d070a00800450340c110301130325440b6030b45080c002208041c0d814914050540704d043c540d45804001185103040d001580078103207281e030030788940b16241e8948900c0b5540f8810414115042d402050000b101503e103d01a20310b00c581a2001504048195403034021a400010303c41000c10804a0140081c00c840304400c1c0e4408804e000814003d6030500400e0a5488103000c0d00c0d00f0811501c03562080e90340100c11005002e440404081c0da1213070b590340620242e00440c0120224810500c0001800d1110342c00000200c940003010a0702e88044420141c008080c2c0000e0f4640080d29001310301c400d6590f03954600020580da4100003c0d520348001003c9450 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 4894872 1250 4893622 4893631
    0x20607051609090201021f020c1507170603100207050f010606030603020f04020313080a03060e010b040603060e15090a0f0203040506100603180b060105070503040f0602010b010918050403050903070305030c06 91
    0x3945844071403c0540e90010b030407213494000e1108444412160403000011b8440d80120046030300c00c0b000040f24039000c10440c90700c0b4204036038800383c1303115180c0d03108c00b81d0740c0058481a03415400500c08605284455000700070301031181003181d20355240c5502c1c3c01d080d154103511010129580e04410425400d001aa07a40d9a08040b1421880d61a0100c0a0503005440c120050001e80b808124014514000d1b40b003500913107401b104550f115a5941015276155000c1d01a074400a8103100000614031314401d140c0d0302441c0c800c0c4050401840305402c1c0b0411400c000e100380801d640320400c0407001001407000f580a207004102511041c076091203045001100e5522190130507140402000300106000720340d03240c040d40401031040d030342c0fa6000100e616003d041e401800c0790100060000e14040701d1880e10701101c0c0f80f50000d128040c031450043d03d40000c24455540c0148901d190305846111720785c000c907485807003030038010300b003a41d00f00210b440d040c02074100701c0c0e480c0d200003605c0c001d05d48100500344c0e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 4896122 1250 4894872 4894889
    0x6060507050a0308060f0301090f02190602030f0708040b04030303020705010e0615040506040906021306020f030306010504140a0b0d02090102070906080a0f03050c0a0b0618010608010506090604030206070516 91
    0x400c500c0da941c0075642d0b406a407000d810041c8600c0450302d1a541c42c5a04104102c000300284410621424001d19592138810101d106000d03001d02480c00781c000600240803122280c003e181802d24440c41d0020990000c60100c03540c2d1010032010030f45210403400340001e540660b0f80161504038511f1b00c1030031a044a4103007200c5074090070811500910800d0031030303900c210550b0301140d183c071040042000340261110090505001068120f845400d5100c00c0c4211080340e82220060111441d005440748803d98806000840c1080305000b00100e09040e0400f03600090708030ba680c60703510003c400583c0c02c0f0050382446503400082100321507a0400402e40501100641000014a1f0100595a58000903801044000d5040060301414010000d0720604450201594550101443d1100100808941c11403060b0492800c1010314001d915000d410b9503520340320009a642000b040101c1600000d13035469111208120100051f00ca03d005007a000c0e104134020070f4140c0d0201c3d01c1180c07556498009101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 4897372 1250 4896122 4896127
    0xd030501080d03110903030f09030709050702191a0a0507030b040b030a120c150501030b0a020c06010302041508030c0f060105010c050a0303020d02040302040513030806060a0212130e0109050604060605 88
    0x1400700c08100a0103440042c02c0c0010289040d0030010520301071010026854040418089203065040300105041c00f811810b84081c240c03117038038102c12600b058500300016807000c5002d100801c41c02e4840c0681c64010104100c0e90003400c142c225032a0411540c281003540c40d00140320340180c04d8000c1e25510401164240440c22a1601003640c0340c04005000d040d00311580c0201d005103000340704910610740c10a054142810444807584007803d000c0c0b004540c07030312243c40080e0100304a442900c010402c450090401030340fa540800000c0d01480078948080300266000161214041000341294151000982604070300da1030050304140b0140d000754140420348003070b9030000d0313004144d00820680c5400c0042c0c441d140904e41304024040c6402c025001480c1c0700900c000c003820340409401440c030076690301c9525602e01d0305211407801030700d070548017503404410300418250b41d5401074a019104060303001911544d0b02041c4d02202820b034001c401395580c0b14180450386c00d080c0a801d0103000d90707040c05403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 4898622 1250 4897372 4897379
    0x20a02010212070c150509030601050406060e041508030a0309020a080a050a1e020a080c0301060603020c0a0b0901020903060f0106080a0c05030106081003050615040e010903050301030f11030601030b01080d030501 93
    0x3074803200a10b40040311640000303201410086000604e2000c0c0c01e140c402c851903e03070718840c05012a40300da0110307482407244200004023072400d405440c05031030701517940d0344942c001002480040c24004080c424200280700d004582400100090441c0003c203503400f10320010705006214414000e40c024104580040009501240d00007948000050340048d0140b10b140f510700079070f002e04031b420900a500c1004d0400010701c580000070554100c201c218001c210880c0c1c1c44109030124410000d617170201d90030544203400800c04401100340d1015152001528007e81c110029003458002c841e50300d40151103000501107550300400c29a808080705804000c1c825044030040c0c9103000510941040200490008090f02c0300c3d5a410002942c0c01401c40e407050401450303101e0fa0700c1c2850b0b00d03d805980b8259240360303a10414001c80d0a10781c4c06031100c51031a4210f07120034a880c030081009490841401ca18030107581c40801c0315038004d5000d80e02401741941880e0701c581c20003a6007000d84040509160050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4899872 1250 4898622 4898627
    0x50c0a0206040305030901060321021903020d030b0a030b010306020a020f06070c02040e0c04090b0106031107110603040201140301030b04060506030303040b0105090a1508031b06090601030206160609120e01020a0201 94
    0x250300a501803e14580340c3d600e031b0740702038050f050a420040500140c000d5105029803015000d40c0500144d8081d9500b007810384580080790181c0500240050748240c3d21844a00c0c000d6220f01d00140d809441c0700c0c0780a840b516040d031064001e074022100d031a40050303501a915170510410f8446881b103c00340141d410202c0e13000b01202010707040684915541e5032441c00c035003c1040000d00305217000d0403d000311314450800006401c401d101d1040480d041154441c1f1b0329420108035204281c3c09605410707420700b224240a05904010002c034140031a980500700503c408201450003144503104004c40c524052812034103940c2c02500c41c5010742d00a206110004a0b001c0b035850558509842e6400603a582d5060300000d482c11201040c4c16100101002c1480607020000700b02e14041c0010001410740322890342980c400c0201d904050b1a00b215006100620300800200034214114100328850015a11414112038114104071061220050a100380350b0b081501400005000d0000c0c1c00302d10441e4001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4901122 1250 4899872 4899883
    0x60109030c090506060705010e01060501090b0702030319270302030d050322020303090406080105010f060207030302060c0901020106090c020607080604050106050406120f090302030c0f0102030105060a050a030e01020d0f050c0a02 100
    0x5440c03a0701c0e1601d0000d403051721040191100c0a4000b0000c1c49240000106107009254501072140001c500c2e02c4007280140b0700d8000c8811299015006500c3c250045402c42982844a034001017003101c500c54003901004030040b03040c4001d05d482c41902d03915166104041ca0001032052110511000b40204462402d907c3ca09509020914401030552143e51000034154400c0684840d0300c00c3c0307008804240450158042d6040c1d032071031241f00d503a0a0f10340c401a030b0703940901c1c030004006a10940000f822407001c0005440034600c1170001203503444c0c8030b88035001174035071546000d801648880100560654802640c64000b20291010485541080b800070202d2007140191424031001c10002d441460300d80d4071628800303003449420003298030380e442c00941b01c2d80500c0c40c601c0300c2d00c10344044046c1c03008103100710fa0498500900761490003c100700b0545003074010100300410305590350030144001000703000030007842d490203034000b9082548158400880d840079000351501c220134040d004100349c00140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4902372 1250 4901122 4901129
    0x80a1802060702190f03020102120306030a170d020a0e1e09010b130308040b03011502010e0c0f0103020705010c050c15010f050108041401090503030601080a05060109030201121104030f0209060109030c 88
    0xc1d100d6640c04507002040c260300704913101882044800d200042e0070312035411400c060f24401d0742a100c1c66000e565605402c1d00040e03071030b036915400c03c13139950000a081102651030b0b0300a41174014100160298001300302c1e04502908000315900301d00300a100d203022145001c10740034440070030f1111400c100215410301414041c01250403400141d40f14609000c144110056512038000c643e61919005a180503400a10446100e03034444141a0340490040c00396041c48001c0e01e004113100036600302040b050001d9001e05505056003001281d02081d8203000725070003e030198031010340c1d8683d502da0142ca400c000f012a120140005001401001c0e40104030000719402440d02e44583e4a5a0801d21014066403407031650790b40c41c010689040002c044003031481507600343c9910300e45690b0920b44030181c601c01c5503064002001e001007840107600807610b81c00b04030110100014601c03c0190941c900c0d903c5900240c468400411003001189011010181c1c070020030302e050000d030361841e950310709549402e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4903622 1250 4902372 4902379
    0x14061303031505040911031e0a0602030402010c08130f17030906030403260f01050901032402090409030206100602070503060403030207030512040605150319030503040c0302100f080a1802 82
    0x2c1ca04010441c07a0300100019042c0103004211006503031600c00352960090300700c0c501034000d84204008141c00070f40c504540003140f501404c16000c0c00d83d6000020f5100903c12418450040f0f42c01001c120020050181c0c040a0180044044e05006807510300e0502d0fa88001a5101a00500720186c5d10110a5501420050381c0ca40c1e22034840c0d01e01590141d0010b8081e90041d020342080380c030a4500e066142e07008008003240e49201d40d880e0300030b1000d85942400040d000c0000503046501055140d070b5800e20b40c141c04000103040402c0d1900080640c0c00700f010650050b400801440b103030265800c0002e0082c0030b80e0009106880c074103001700f6145d1000610103001d2549c041401e02c20b05000e04110f8982464900080516207000d1910200401d403e484808603010480e40385820390600113906c4040000070031509a0401081d81c044809500080c8112003a04801100000588031209034292080403616503525640320440010301160004040a4020b07040402c0c0c0c06885200700b489500454055 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4904872 1250 4903622 4903631
    0x115020a0219030b0403020d091e1202010e100203070203010f14071101020f0310030302010c0305041112030c01022a01050105060a050c0c09010801061401030b060d090212030c06041406130303 84
    0x202d40c0c24045207490b6001400b1860401c00b040f080540c0460036841e050040c1d1605c2c241c0989500d480c649a01081c43e440e103200d0300001c4e05000550002c3d914840e140d105140c00710b0048044800b08913284460880030000d6400407905404515080c01012801c2c0081c0701c00f004840c0c2c9039903204043d148043c24000502c001030200c95001ca81c20b404a801072008601d8499690801c1c202141d03010361244070603401546045610441140b00e4000d590041d0742001882103011020010050b5a40120024a40910080142a919400a0010301180f84880240801c4a04188440300301344188030f10040140e490240184415903c80042c1d401c0c0511a183c05d07611010041107191a1280b000c03141d07070303205001200000c1c0c0290150082400c0d10150382c083c03641d240142d0300540503a42c0540036254460800d0107401004080755200442d040d000a00d00c01c803406004035030a055a106101186e01030b0880d070308010900c1030504404403141c9024008003120300d095505100c61220500c802400c260301e5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4906122 1250 4904872 4904899
    0x60201060b0708090609010c080406020c090702060403020c0907090f03110f2205040614040f02010f050f030612010204031502030f01060c080a0806030705030d03060e010b0403150b06130b0306090115020a02 90
    0x503454005448d90310461040d56140c40d0000a507070b03000c1040d030680c410851000014040d9101080880c05a030b4150020001071091030100041d1500081c00d503020040105000201e028594489200440c0a1180300481c3c1c0c003680140400c44085003641c41c001d0f2401c1681045084500c0011035000d00302070000551912245450000b0700003045a81900302650030034030061007000703401c0412043c804d0f00c0c1c2034458110100c003500c190207902c100c000b110320300b4400100355007080164031200c48842c0d030005140907201d644003012070304401c1141041c030b070b400300410480026641c241805001c2d80c0c140041d1201090b6500b00c142c3c40340d114071104104003040403858503101000b01001800004003a94200c140c41480107000341080e22841c805111f02e0400060f0115005045a05803a00b101440d5000b000c101c003010007900307064800a8005108101502d202e00345800c070b42028011458240742c0d07a0038a901002954a410b0f0004000030002600c503014480d000079180045540c1601c0c4005401e05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4907372 1250 4906122 4906127
    0x706050304031206050d12030f0b03070e040507080609030403030314010509010909020307030507061106060d0209070c14030409090501050702010501050a15020f030705070f14030a060e010209040e030301060201060b070809060901 100
    0x40550101b5044a4100c601c5020440c0c1620300419004c0640d03000c026040000c003204003a2601110b50b99010340056100748454820400e01c032340e01034040da04583e1255690b9440b1450100c0c1115420015080807409000301945070250b0002600e01c440125a44d50420300081c0031500107100703000030f840e9104405011500c0510540f4004c64004066491183e507500010f40001407410190030395026040014000c0c0c90280482030807650083c0940c68240d88185085e80c0c5659100000d456040003050100000b0500700000c1002e4000500045a41192032030014251503001d05441c05590420303005011a488525049084640750b403034003415500703001000d1b030034a0760000e1140c1460200080e5502070081c000750344421504125000d240343c9a4444160104182044889505400c1115480c02140841d08503100300718030340000600d40200400010200c41c0184101007443d080800100020340c2c082c0f2640004040305442c06d4602403855662680c0c5124054665104500105507101280d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4908622 1250 4907372 4907381
    0x304030e12010209040f090b06010807020a0b0106020d08010603200f0c0303011202030c01050301060203090402030a1407080405010c0e01050d05040303060e040507090c050a050a0c05030c0d0306090e07060503040312 94
    0x80c0040c1005006020064005010f5446042164059401c1c00005075403175031688604580c3d540c200e4807400c0103403a0540116444c950191518013148540c042d200041b0780342440550080009400511940c06000000350016505900c601c3c20700d031500c5001e42c2c0608541450503100c100107402c1c1c41d611000e02c5210071041c0101c55010b59240f04c040b00107c1c00301c04440403106080d000320202d640050490004480e184024003811005070802d00203804141815006540c00200d001400304001c0308940c2602ca1451045400c000020b001c0400d00050210a220398502079040d440c10403101c88034440042c01c1c9101e14100c20030010f40c5d400024082c588241c4c04100500140c2c1c0581f2803509103810165030301c00ca6405035010852034510003201e41809207045a03642e0003035403101e83c04d00d0300d08403099031440c1200310150b945000030440b10b10a500c1c10300001c803011a0588001030f0550518441904540300c02c0c22030141c1c0d43c0215018803071650044181da50113607242c070700707196141c0641180b0800ba0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4909872 1250 4908622 4908647
    0x317060f220608010207150908040b1312030e040c140714030d0507090305100204030b010909020a05041503050705060f041a0f0703050306090601031116030e060304050a020a06090308030c030403 85
    0x31032030b0034804a0f5030b40040d002070a0040c05800031509081000201104840660b84020880b0342e0421041040407a00380280c00040c1d801c00c0c41d8a215039a880300001c40700209401103000403141103038684507190a100342d50500e00d00d0300d00301c0c0444021000ca008284a00c0320094080c0004030a44140311204104841032172880c0c3c0400c3c403003402c047d81302401881d0180021107180c010b00040c0344501e403441c401d450071240c0020385118203034a031920b014001c04245c841641c0283e0885000700743c5807154016416054080280c1950710b07842c5041060130007503160000743c4290020015045440940c0058900395050011401ca11480c903402c140c05910078211340c1350012202003103000034143c014014520514040d1019070b85665071a00441c111030f183c8688400e125800c1c40356608088025804442a500c80e01300030589800a5001500c644c2007140c0c2111103501004941045041c5420301100402c441d04100500078190fa440d050300f13000042174902000008030001d000d0510808415811 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4911122 1250 4909872 4909939
    0x30102040906060504030b09060601120b0102100c0519020a170919060306030606090c09060e010e1806040608030f030601030b0114180907020c010210050705040509010b070317060f 79
    0x42c1950307418050065042403000703407814013404000502480c2c0100c3c415104020503581c007040f00e132207480484011314180031460b04501c00c0c0e0384d4601080c0082d110b011800b001d96103409813a0464440c9210500c0c105482c410219000000e1403070000c1c1501040c0651400c4094010382c440715410041541a1080001c0d840308089024000404039015840342055030b0080c1e0382800075a031211407007000c0c2c51116608800040301c07018108403551044030141c00102c0145050106001c0c1c490006100d0b80401c125107400b020080240072091030940314070700080c6820000b45003060350b80c0404614a000040206041c980c40b281b0020184e031054644000c590a501e204645130400c0b400400344141c2c141181d80c3c051041040404d8000d40001070f4100c1044d0141d000700050f0445546100162101401c0b01040c85800d20001c18641e460080c058040d00341e00000d9511440141801000307500c49101001072414000d00307001c3e2685500c2c1003e0000340d400d0790030000c02079800d4030b203403200a1841c803000070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4912372 1250 4911122 4911131
    0x405010912030203041104090807020111031c1e06030201050f0a170901050f07020606030714040902030304030305030717040c05010503041506080c011106090309090405011e1e0504020f01030b0301020409 89
    0x1c41c1c540640c040c501a40c05a40050482c52000703090004540d00250064440b400c240311850056104d001046219449442505d0805070040d0601d08504e9004521440554880d101e001143e04004400200c0000a800030b10040c0d103140c002900394407480c00d800c0c00910000600000d80d9003c0c8406940d6040c1c800c8420080d40b40c1345400c14000d04050b42c0386181c6121a030080b410281c03000490a0080c3c00040240558910b08064880c0003c04015481d8005840301007249c090b0380c1c2403000d80010343c000c1d110300340d403440c0c02070b0010460b5210590ba45021200d802c240030115400c45282070554500f800c00315940d440e5420a0101000c0c4002d002e24118200040400c800002080c2903c00101c2030300c80014841c0441441030300c5590884001500351310034001050140b81008046803c98040d00001901140e903d82a586081500b5058010340e52114018a80547c0c8a098581c00030340e00802004142060b038002804041c4450b52a030405450f000140b000e60307020f504540c001d0001000800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4913622 1250 4912372 4912403
    0x6021306030207020405060d0201140901020c031507090f12080304020301021e04170609060a09150501090507080601110619020f0d0504060c0504080a020114070b100305070909020906060304050109 86
    0xa002e5880f03035504a00450411000c1219400d00100b01510ba41d8161291186c1001d4803100203010b800c1304001f00c2c118403c074001c907000c1c4c0c2c5090116401402c104c0800150034034204d14060001844c81d80000160328698004008180b1002e864241c50359001ea50681c0e0380d165800002d0281c0079204070a0a03184903910100c07003911410004008440104012110702c40c1c40780b410a46800d0126401055600514009941a10b10340d000d052441e00c1a007a042c030f200303000c1000c5021240c3c02d8024074070050b0303100d0501c8001e039046045039070300031400d1800c101041c1240090640300c20016100881c0c0c26651100700002040a40642c1d0202041646080d120b040007c6040040d1074103560651f000d51402c001400c409100302c0450341a91000401880c07180426801110b01d414401f0305c030a4030503018000300c0002044900e00c40d001e01d190502c10200542182402c42c201b4901354485480d8a151005040041c2c80c0c200039203a01032422645e00d41c40785d0722820030030f01400f000140140108000f4441c034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4914872 1250 4913622 4913627
    0xc01020c01060e060604050108060f0103061503020304110609030307060506010905060708070611030105032109040203041202060106050a12020904150f0f0e060604050402160618060509030a140706021306 89
    0x210458050401c101100d4484e9420b1018070310582c007802d80021041000034590742044200220703164018500001d075550307120180c200d074619230340344a80001d40010612090094281c4881940d450458285181c00c0b00080065620301c035514004000603100e80000310aa80500c00310f1000340005803015a640c3c841c1c0c900900780b82e100d254100d0304e030392a00101c0d4414401500c00c0e03c0c166030000c0c00170005509403110600411403191040030f000340b07040083c0d00031034503240061401036100c0c20a032940c8800085000e81802070507000681088001d00c6031901d000e622041030920000c0d94140180e950008401040c00390428074101e4110106070500011914407001445080f14202d4411441303003502e80c00b000034105030945503558840e000340402d002501d440d50082c20100c1222021150200e1780da6124406c2d00c030350400709074450411889031810300030a4054940c0c044041805540b52500c5607001030000003060401c44440100460002c0c2003008950444000c042c201d5214000c4a5944800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4916122 1250 4914872 4914881
    0x30b0903070c08010603050a03140d23060d0302030307180503010c08180d02060601050d0b0d060506130212010311130e0c01030b040902011709010204030b01080d0801060c08030f0703020c01020c01 86
    0x1194002c00d00756000515003410300c2404143c0768401c01818400c45140c42c02c40d0f06115070100003980c00b508028940b40700060303100304c3c02d178002e82076401d581e202c020700c805260101c00240300c58058281d50340700100080e030220072030b503004090741040b071307001140300ad82105002216040384c0d8040d0320b4402484035490b04607420314800c560040c141d03104186605496621002a59844005a400303480803d000303600810140c00c03400040803001401540490014141c0782d280b42e0192242540c034400d01400c0c0c14003074588040c0048464065251034400b1211000500d014840a0094101e9010700304d100d503208001c10420a02c008030500c2014001214142c4034000448524041380c5001840d10b6982020b005110b030785034058590520034502142074074030301140104503a0035558200300c040b0004998a060078068801500100301181e110000a4002901a00200b0034011810113207400101c1120803691300c18140118041e0640b03804c001500a8041c091291210b54004203600051a005600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4917372 1250 4916122 4916137
    0x20d0906050f010f1a1e070f0b060d02030c040b0d020d12090f0b0901120209030706020106090b060c0712020d06050c220b07030309020310050106050c06010b040b090108090106030b0903 81
    0x2042c10350b0760703220408080124103104032000000801c0d07941e00d0001d409405050340031000c031181c10b220350503d80b10000a42c45280308640f046c0f200740c24041405030070b442c06c50b032025043d01c0d2240c9851091300003a40e07034803421010500c9a80c448a00c1803d98031010307100e1380b8a6501614442441c0494a412009a00300101346030004194031800a8513080104218044038064099180313000030070001100c01d0f01401c0b04103100b06400b081295600d480411412008080e03580c00000c1c00c45c18141d042003a00c030610f06040c4550000d2048080003c000b05601d801c036068600c0c1746841400910114a90a4404034058950392910301048910f00b065402046441503111800c83e0703c48055100c070584034618017508102c628144282c4000900035800410128001030440f00b03001d00141140c0c0179601c0c240c10000000f0b901007485114000300304845c2c4d000d807410b020068241400d284150740b95000707130305009040040e0740001c078034409400e40c02140a182c000c0414030940c50038070851542c0794008079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4918622 1250 4917372 4917391
    0xc0602010b040c050a030b01020a080d0606080604020f0a120b03010203012402061510030609110405010908030c1513020307080c0102070801141f0e130b0703090308040b0703020d090605 81
    0x7411400350745014410078060f080b42d40c131120304203075400324100e00920241c40300a040d03200d101c048070040380300000034011602c446030300400d442e401d051004282c400c028109502907401442240341a001c410305407501d0740d41900d016010f40d10821141000b421364401041d825502c00000450401707614000001e000303c1401384a1204412031108a80c0c940741119810100704412400110603c0e01c4d14004036210324624002c542c960300d07181c00f4011100d600b82120395020000a080000b075800001d81c100500003c80514181034001c0d101079191101c440a00c0b0180e01e0032400182400d0f0350b009031828403a005002c981c01e41d40c82c2d480f242d0b61507004c045690b01621031844c00190b0000140961a90355110060010907505da032802402c5e401700d01c410340c1964520711040411040c000ea0201c42c81036085001d042e100c18842d044c0a010b144025081408250402c45100046a001800290001e90000000c4100d80d60107404a00900070454054540d0b030a041d8883c040c820039401c898020103805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4919872 1250 4918622 4918631
    0x1309050402040c0e0d0b0702030f040e010e0709081005040204110a080a0b04020a020a060905010603051b01090906050603060d0302120f071103010203060102060a091e0501050a11040501020705060706020403020603040c060201 98
    0x41064400c000000c138681c0c0e0003135414440100003055a41c0c07168212a003401200c0c1090309964803c032071900660452180d0b000b031080100310b032841900d4019004a440d0800f40b194a08084080c0d86442d000d0401600050300d680101d01151110f600c64000351100f0458551102c400420003004004144c807140142402c0c440c0311840c6207003510884082c0d000d144c0040000e160706654080c054540b6100680f43c5560b1140004003140d824012172801c810f0624044550600d07040025100e801e283d00402030061511009000a0f11880c3c1101e4001000b12a0200001d000d45812072500e49540c06100c002d480c045600010a902d08029040d028072403002c4e1030816440009143c202d0004446050040c1d10000214030006469400469441d00449000c12000100b0f142b003c50a112401c048409a64500400c90003a40360311070364801403840803681e0b1600b480c04d070000703581e9805030240d580f08820000303140040010541c1180e0003540d01800d56520791034581448403419801e44244405035003030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4921122 1250 4919872 4919891
    0x406050103020903070303030504080909040803190507170414030c010207030905030a11010804050c0301020414010806030a0809010f0203040510090f0e01030305030103080703020f1b1203030112110303130905040204 94
    0x1d0080d100700f028080c0042201c28616107044001d84406801902c41764030400c0f0180c0f443d100c5854841c8103502a542e011b0392810f00403540c403d070300c1161001d545040c3c905024030507029400420154080c4040e60011001c1d1a83d06005d50700d5200a085041c032440001410f4080c59419000f41036454002d845581c030050790f0307200785601c0d480084801440c000002691100c1503008500d059000b5020700211264030304100f000c682203902c1034200704511004032100410941c0e002a2141e4070890640243c40300c000d42d03a6881010303003e01e0102c1c90600841008042034180300300140c500400009051100b980aa10406000201240240c8500b5206420003042a11513441d4490489505076242d0380383d070f803854803078544540000c04100c08501401c00c0b10040e02004010300340c1d02c80001d80001c0c503005c0c160020024105d0b130304101c070800303600280010403400b00548200da82450700b01c2c08190300f80100707400084c2507114409400140001d03101010a4060242d8001e62180d8801c3d00c08201c4c02c03c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4922372 1250 4921122 4921127
    0x90503030c0606010c0503120403020307060506120a0308061201060e1f0e01030f060902040f0e0105010501140313030c0f03030207030e06070f031103090a030609020a05010e0901030b0405150106030b04060501 91
    0x2034a01c800e41c25882040400d00f154400c030b0844030b08a02030410b41c2d040c003004040800855209803019001a80003180c00c1052200d144607990b00f10004880031076941c20089030380390b150117070b100001d000e0040400c0003818a448040c00082c2c8403200c8c500070052a0b4031014028481d03402030ba1141248609218007203522054040d044041e1107181880c038039030780c2ca1079542c0702100c22740500c1120180d8541205800507190b500a4060100e158900800c01c4e01c0014070b00c1d0708541d0143d100c0d604110702c0c40c44841c2502c0b400b2084a40000046200f0031007400c09080903641c4401490340106092191030501d4141580765002d01900c0c1e21a507588900c43c0c0c00c103010007805016410300902440c0032804980c0002e0301810be5000c400e0201401c0c0c900f04401c4400090784800143e2040c1c4d541511440707050218a094903011010f0082420813101c0e8092207030102d50701c54414040148450300100c041410b00c0020040c14901c06004800c2d25005c3da11180300a014090100703416009504008000c5015030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4923622 1250 4922372 4922377
    0x301091a030601030803040c0f0b03040302010b0303040b071511070302030c0c04060b040608040c090e0312010b030708130503070609031e020f1b01030f02040e04020102150103050a060209061207030c09050303 91
    0x4100034020481c40e425922401700c55480034200700c5078131184800c00206e26107080da00000400d52410b003143c480c91f0a00b00a42503400c0703444120f219410812062180740348441c10342e940680c00c04010200205400350320401800002a81d080708000402e0190406a0020051403110f01580030b4803c80071980701844192210750240d40f1000300f081c00240040c0d4450038000e548130340a01c80c0b01c100745546201c00400c9441c2c0c0140204544c000181c0ca4a61502c1060003500520100c18000e00d50b29091000401c0650003030007080d01e000e44c42020303400b40b000030002d4640301600003004010311481481c0c050180c094441410b88044401040810307180d0000c075100da135800d1580090071488070b00c5440020042c6801d01258107055032003581e040e03582040c0c0701400c0601400070380e41c216402e150001900c1c00d110000d008042da00d18000500000d030700480d0008400780c0c0440301503194100c3c1000144d05014480101c501959500d08201009606410107414086aa2130300c10741d06440324141612072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4924872 1250 4923622 4923671
    0x204030f141c03020703170412030c050906030103080901050c010606030203040b010603050912030703110c06040506010b0c12090409082209090804031106070503040806010503160e0a0b06090a0803030109 89
    0xb100c0d014950106034080d80040500b507100c2c0c90700802c4004008054000f040d01550250b03201441c2403d5161070603090311841d08103543c43c0c00d0180c02d10404c0c0340010124401400001c06500b1301248803402079000304280c52003139110100a01004da120800107000350412101610341080150002032918041d00c038a500a102a00262000c200f10450001041d407015004404041c0e50b1b1f46480f0781d50085001901c0b1568401c2c0151800e81803505009103000410703003103d84010800c12860480e003d0002c1d10458450750075100030344440280000400405400c0d00c00342c030788000091044a600315800a106003000d52501445803952118100c100703c512020005000b5403081005101107003400d410040444c10081c0040e24201c0140d45050842d00240c1c030082941d0320000c0180030906d418040f001c002441140008000752500840c20070702500a403030282203503507038040c1e4400794071000d088400704c1501401e00c1c82e00d00d644a040642e207502c03d01c034410b1514900740c2d140f80080140716001090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4926122 1250 4924872 4924903
    0xa030b0f0103021c05060a05030f010209030d08091507030f0e031201060e060f070501090f0b040c0501020a020a090e0c040612050709060503060708090a020d0c03110904080315030309040204030f14 86
    0x400c0301d0132030810060a010b0540b540c081c80e41040058103940c20451064400c034138000160b21003110405240c82c100301c1841450500c8100c03402c224801000203050311556100e01110714550310f4074402600204281e00011022a013003004070100000004000d003110880c445511541d42c0c1d880c9000c4800e40780b00d004469111400f004284031140c183e60262000364014000005c0e04e0070180c1d90000c50700000031046030000d16610070001031003082c655800c001c110078009855081d85690005070405024081d40c01d01c1551805401c869203401c100071158068094010040ca13a12400280600c0210f910108c40c0c52081c4800400c411285004000440300050024116030300c030769000380d40003040140035050500c00d110b0103001596480d044006220700441488003d1030846c101090848001d8068a0142410905010008100a00712580450140701e500200200b0100003400d501c207016040c2d9202d400414080240300c5031807140040070744504154403040140141158a681604010303000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4927372 1250 4926122 4926157
    0x30f070b19090e0406050105090c0301030206070305030a090b01030302071401050c03070204020f16061d010c080103060b030708010603060204140a030803010608060f09100501030f02121602070b0a030b0f010302 92
    0x441021207201501d07540541001c90300c10b521140c42d15480c81d4203d60035180192034400411203802c1400103140c0164403401080c0c0f8542c10b40e00402c0300c6105d01da100030204580000000da21a0a650041d588141d201c000003103196500d050095884003180541e80c000201c0310308541c01903008004590304c09140601030340c1804a039408100094214021003a04007a040281d40c0c01800640b41003040c0b98411800024003041c1c40000f900101c1203408850f80c16890541051103903500003c0c11411203130302c4100840c00310824004a03041801c158001e603080d41c2000c0c07012007008041d802420640f911142d00c40404100d481c20804101c0d0303648405000042d0030801840380c944140e000541c010380c040c019000722002c43e000310f07207064406c50321022800e07441c03a030a202c6582c5c1401080001580c244040d07080c8861414031161545d400781c078100c180c20100b070854070043e000b80041c20007881803100c4103803a82c1c0c0513240038005d000d80203a0740c4d1282e87c007541e0b40c2d0520f40c068800c0c1c48070b0700e44100e280074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4928622 1250 4927372 4927387
    0xc0201020d03090c0e04060e0706020703050105060103052403010204180b0306070f080103030e010c020d0312050114300102031806130b010501050d090501050c0403060b100f050a0302040305010911030f070b 90
    0x45d000710050420b0743e42c6a200c2c0109240d12074100a541e0003040d550b40109261443d50920303d00f1100d000e0807039410107080c02d007417110ba40001a54010481075501e081b01800d02100d001070300900c115441141c030f5100000d42c80000c0c1c409640704c4000e0080580943d203955072403480880c0c40400d00120800070410100041c40400c1c0300e040700340300003103048c101300c03c42c45940d0700010315a601101c0c04400059000311000036500241c000c0d603004003100f458410132034000c0300000d0a8010450010a014000186401044030b1307503a07442e01000b5040c1000b1542d0f41000c11072000080c48d82e11290942e0310427040492215400b9510b40f07045a0340184514010740d00384001183d080d40f00560410740c40c2e480319440c41c040b07042803085034041c9542e280119612891480c008095030240c0424500c200c01d800c2c001200c00b5040f080704840c507201807800c1eaa0b908418402540203003d1070300301918540c42d100340394040240c101c0c04207246c11411400c60304040501401203a90700301d50700031394651308014030907903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4929872 1250 4928622 4928639
    0x1703090d0308070c05030409050412030606021c0315140a080615010809030d0c020601082107020d020a030501020c0102180904050c120a080309010504110a030302030a14090306070c0201020d03090c 86
    0x20f81100c21841c0c0104865034075250986160401d4000602c1305e65900207100401000f025460040113103410248151450702d000a9120001004050304901e0b80b10707040c14085201e80d00c04d00062070502c0c10106500e40302c0d140c0905039008801000d003d80114440410f21040000e640c500c80c121999042510b071070b40c01e004551000700035011040c1d070321050108081803070907402900507010103503005060719071505c52480d240500010329a21064800b04040608513403d00407600180e4042d00e009100081070310103e01c010f080c0c2da00c05041e0b54400f040300c480301c0030103400800400005601d19200322091100704404a9015900240190f100311b00248660030040c07541c85402c80c007402954010001921428400c1c1c2c001c4503500c41c242d5483d410402013010a401800c50510b007941c00503404e50071f41e07802a66034420304170b005c800d120303420b10b42d507181c3e010300304c1112041e0740017a090f1051070070700c0fa1019100800717940c0c080f07001d809800d100d00e01c203d07c24410480c0c1c42d9003060703003001d10500d0003450 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4931122 1250 4929872 4929887
    0xc0302040b1c1406070c0506010b13080d02030306040b06030609060405040203160603090c0b0703020615031006030602070b01080c0d020609030f060c0403060507030b0a03031803020306010902041703090d03 90
    0x90716000a071032894032101c80503603810528410f0003500c420104008503450342d400e00b200280703640203100c071521103540442c80000e000c3d4151139003048110f03998110300e90001100b1030306601003009480b45079100c0c0315440d80400607500a440c00d0781c051258111004c10095135010407260503030008080700025000d0301c0e013a00440e4106001500741e81045942d075a01d00e4001c1d82036004500402e032280700000410440d090380308024010380c0c595034240ba50700d5030003e40750310010301481000d41031a840c0d0809544c01380706001c10701d8806041040b086a89140220194000c144151020584030000050301c06c400f1806102c1d9840007006418507041540c02c1000641004102c2a0103208001103040b80b081c0070860503000300b0603000c02d42d456a00d107181079001d4900062180c4209828403000d04c400361203100004042d02e80c1030400700012008410340401540d0740750b10195151250500008001c1a150300078802c0d07440b0900c040505101405183c1d5491048840b040d40004032401081e000c644207611 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4932372 1250 4931122 4931141
    0x6050105090d06140901090308010902031005090403020c090106030605030d020d091505040b04030302060115020a0f02090402190608070306080c03030d0207021504060203030a1a1f0e130c0305010509040c030204 92
    0x9000071301c2c00c64220780e52800c0c01c080ba000b211036036680d0b49002c10b051700309c0c44860044c41c403880103520318541b04980c80f118101501c54140220010000b01d0200b5000b03000e47d41d030030000904070320801d60307481c28010f0261580d03200c0c031800381c000c0d40c4015000c0c0f0310110b0f0058001b03541d1380341c1103045480c21104a9035014002048400c0020510011409080c200020030066000f80c0c01482c031035041c40e118220303440d080381e091015580b020250100003101c0e45542000c06404070f40c42c4115641d103001154115001082c3c501c1400005200804c1f10758014003400c2c010442d5075010002c95444143e00c0790350b0a1400c8110398164400d00c5104810312103600141800f510107011090310210501d0b04210039041608041c000d0b820201c2009144001482901c00d6000001105110301203110b010605e6400c504201580300001003245401c40c3c0d009068826660b84081c00091440028802090040450f280d0210010f07003400000269450903c2800e4010754100d01000b0129186500b00001001c01740b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4933622 1250 4932372 4932383
    0xc040c0f20010f0603050c09010e01030f030f0311030403020105090d02010204030c12080f030702030a14090f040c1b031709010b030d03020a090506070602070b070201110702041a0916020706020106050105090d 91
    0x269100d03205030442c0101301c0114410801041051164030800c034050205800864501910200420100b0542c20300d05245c6901403d19000580c0e109000300c015094120bc2c0103510f0300c00006000425905510540c4030742080000c3e115840aa01401c03803e0303114510000c0d1040c50012014008105d13000e5115019610400c40e452900310369441054480e0000c4402e43d025820205844842a801814032220640e41c94010744c9420122000951080c8528100710302440d582c0700004144c078010200c4440d0404680c0345000001c2c550318008018074400f0440d0349a4001e11408503030403070014054415002e5005001e0300c0101d804203400c400a410180e0f02004010300e094002036551105002450300b640500b4015a84120901f04190071000c040c003150110b82c50400080800301e03402c000d41d041031750704071400b1851b0b000c8003104000300d82d2a100c031581c0c4092410705004450b10711085907158a5529001c3d0307010f85560b0340d0281d00300d41d00303072084602191003044102d00c203103040c0981d840c0e414070a9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4934872 1250 4933622 4933631
    0x10050f0f0307060f0806030d1d0d0204020d0f0b04090302060403080705070611030106021507050307030b060d05010803070b130201020a030f050c1605011d0604090b0307090504050c040c0f2001 84
    0x800029250070390b141e000340d000ca0080c0c0d0f9051800ca80c8501c0180d03019000b54024001c140010304002e0800c440b5400115020120300444841ca60f9940c48105680750010010b40d264025111403c00510180000c44011454801c0c1074165050034081c442c40c4940640180845e9559910103a81c52074005000b07104201040003050002610380c410b440359410012035071a22981400300103807074108600181c8000311a607030100140e20341c0c44070031aa4444030718075011a896021902107803c9020305990a0b1941d81080001304003140e000025001d058051800402e42c1e0f210f1301802030084182d40c0e406401608005c03605800309018a0314080c4082044c50500e10304580886a54145042d031110200980f2080204211944e840490441000c13032200c0b0140d22140f0a070300095041c0b180307124031980d2640f104000c160b5650117100c83c030010821000e092244c2c1c502840c11613140d0082e44a02071065117480b10550090f480707851240b61140e1203480d4075032400e0505191801402500320401c1301c642d03d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4936122 1250 4934872 4934899
    0x20d050f0105070903141605010f03060518061503010803040b07020a0e1303030c020313030f0203010902060d09060606080601080a05040507080d050309010b01050a05040902030901060e04050f01110310050f 90
    0x2d124691150503103a0f284060b1034210702d070080e188420b41d00d4410803640070b13240d6603d000540410000442e402401c11803480000480d0a40c0a0300e030b250b000c10ba1241d000114141500c2c180100380744038110444400000d400201c01040c50f6010a0050480a50003400705100c403003a99001000c0243c0010302400900355995900c0c2c40d85c2c1821680c2d02c050310204450001019014000c015201085001071424002000a4014006494400a000715103d0540d40301951020f511540005070082c044035512805080c04802030300a00000f29240d40c84d10100043c424440c120f994014201655456155140e00d0341182c00382c50040c4c42030b80c450285650005140070200102c209c40742c013a840d15616444d055004500716008a411701c2d050000400410000941c04000c07542564251080140c5a0715003000981c01841660480c0c0c0e0900700d0f5405000611030009a44900715240c0e000a0104454000380342030036000980e0304280e0044c0d0303450184000e2620046040b84240003074810b5944180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4937372 1250 4936122 4936153
    0xa090309090504080903100203070e0112020c010203070908240403110f0105150906090106050304020d140d030207050d090f0911090303030c04080708070305060a0513020a090203060f040e0604020d05 87
    0x24182c0d42114944e0700000c62000700d0600f4041006c83d00d44810045080d4075001c10b0217805c040044c0d1405040100b0380c4503898940035960f0584107060320782c2c3c008540300c0c5418000034281c410140212046446441d0502070046842d02403681c1d65943c0e06460015902c0b96601030754074000e603c0404001e4014600452440d10b000d00c1010321400f00e1402e80017410f941c940c1401040480507240718024100500140300b9550020308881d0044d030306a42e41200c0c00c0042c1400e0b0018421100c550000b800740d1100010b802d64103801400c482400f81c800d0720910628401c05560801081c819a00c24140c40e420411000801c0d43c40308040392425114540340201c0c03403000034110b42c801c460000804e900410b0500c142d4200704028009009220700405640381181c4480e9075400c401403020320150b49400005060107000b6010b0581e2590103460b4540244e11422180040c1d00200d420502549214001452a00e0140201d041c3c082100c0007514451300c0796006d00001074a1fa03201030b2041d1207aa9000c0305001e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4938622 1250 4937372 4937381
    0x309050f0a0308010501110703020a12030c0f030203040302090a0b01080402010302090604050604030602030a050601050705030d0b0109120b0405060a09020a03020d020d08031e061203090108220506150d08030a09030909 95
    0x601c40c1d83c6400030b81d07042100140000800000880301c0d0350040c0d0003800141c03030b1640c40c2d9007a2440c40444844c040618a800c990074070000100030720404a0368a501c08054001000c4c0040d244200d0b0260f40340d036210542c100c02c0740d6107001c49500080c41540445c0c050f5000e980204035503280604160f26064841b00403840e41d80c0150310440d01742e5400001c0007031606252080c280c00481c2480c115190081c40c1c0c441c0d036524020322410340304642e91744c0760104584e070042c9500e2001705000d40e9600c03400846c6041020941c034045030300b56001d0040c0c000041401c00700348615042540d000b08851400b900b1a000e200704045141c00490301324000596800116035500c0107544145c0400c20000d02c0c00708440640300d031240b0702901250117021410101038000b10044250b400c0340d035003883e00d1100c680c0c50340b003840c90100001c0c1c5465004195461200300f4001e0100f0168896544007a40c44050103010301802107094242d400901418000d001080c14030340181c0100d00010701030715201c881d103600c071081c600454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4939872 1250 4938622 4938643
    0x30f011401031202030901020703060b06120106030c0305061002031606141003030210020906040504090c05040e0307050114010e0106080a06030c0608090c1206010b0a030e0a1b090e0d0309050f 84
    0x11440d06004104005158100000b82003241c80130f1410b0061703240c00031390750721203a00004203030b6610b58040300b0741600c070981174414030700200c402074081e941e4a00c0702500421a86c084403000a01388000603903141040425140488071a0f401545800c58512403150702d00740d50f810440b001521050b405401000c0b150009001e0b019201d101042c0c545980303006490150240b8000942c070b4018401d4640c1c5983e540141ca0844809a501054000c1d1030725081c00d890740660009580640340c0f4000b02c118540000c00340c104248914003c0000c0d440c0b580c18540241b4003442004603a00c0c0c804014030010340300740a8250042121000800c0e19926680c0e00e8100719480d03000040015120000c1010151041042d191030748070a031624406440c260400e65103c0405001e0b110104138000341503071065109030303c2a10404c8002c010340f0802400341c41d0850300c0c40c0007402401d140000302807021076520514401c00c0040d00c040c1000b030a40c0b030400d2206801504000c28240c0b19401846000f080c0c3c40810700000040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4941122 1250 4939872 4939901
    0x103020c030c01060b1c0c021e03091801050406060c08070206160b01060314010905060a0b18040501081507020607020309040504020a0306090501050105030f01060b120408210a110a020a11030f01 85
    0x710402c40c03180c1b071451428032402c2c4180c40e041540381a81e50340c0110b1003400030070b41c1c0341201c00044c44d102d004a2651003166005d0350400b140ca03249403040504047e05034141c80d400c0303e060000320b544003021602c80c0d604607006014004200325100040c81d2050080400b80d64030100c082d0088215101c4c15000348003640704030042070b20b816062680301c681d180c0840c058841303c8000c1210382170070750200341d829503640986072401000156143e0030102d603621007000448010014802581c480049e0354441c9903040200030403001144c04180040d0010600030710400d8150700544c00c2000480801c0050000a0000c0e40c00c950366a0001c004282280a0507070168003a60001c107e5524150501d450302c41107111020440c0d00d420414480c40200400326021021400350203015a10b40d410b021206100d609500350304140c2c07114070b0381a108001c0b061103109020380c0004002a052404c41c52030716118101a2100681080040c4000203140015585074014082d0445039035030807004c541c600312480d447c0f40422 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4942372 1250 4941122 4941127
    0x62d070c0b060d0f060f0e01060305031b06130602090d0f050102030906010803031303050d020f0c0601090b180105040207050a0c0603140c130e040f0c03030507020f03070303020303060103020c030c01060b 89
    0x10700000d210303055000081514944800715070b54542c6581001c02c2c2400516068075000c4000c440f0903180c200d041c40e00d42504c001c104690b03032807400d29560b80c06040c0340b0094000c0c40d22001c0150001050080c8501d00c0b94452411084055030388000a40c040e840b0a940321020401100c081250507000c3c2d071000e44524001a6a41030030440b407851300b4416403022000f0b81c0100200700b40060003480c130020484c0e040c00c0c01515600c0d9242288040d008ae441410380108011680030120b0400081681c12a00076080030803031008207800340280c0701030300c41d4103400c4510810700411545c1841c0e0b0051030814000d6003940c0c044c030a240d40b040c109814540c001c000182e210f80050903141c00c10801c0540041d070840140d40f4002104102030008462423290040403103105001605210400b181009000d80c418030594080381c40340341c050720b00d4111400503401003407038800c00752540c240044e0901c00d0702d403d40c005505581d9041c00460187d0b010481008083c0000e015241c1030080134010b0102038201c0c040070a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4943622 1250 4942372 4942397
    0x308122203120b0307030203030d0501060f02030a05040308090d02041104060306060c050c0405040305040305010c05030106030b060c060402040b01210609050903040e010303051b030d0b03100b03062d07 88
    0x45290305009051450300c003914600000007500070384204900c100d814408240c0165a00c006401e1420552000c0d4050000044841103103c10754003aa06880ca0303a04d0300707121105000070807640c80c020020b0003808200104801e0000c01d50040c050881480010042d00c4903105650119045e100791007045610141c0c081414441c10b038050040c8000703800c640c50201921409030b101c8aa41e1030184441c02d0280b95520041030915115000320350145800000a21100c4080b09004010794424420500040e28041d0400a2860110b0850f01003900d005d000380480e8940390200030080202025403814403040580086007030305000e12070903e103c08164002a603a16001100080e514018694019030308100001c1c04a0070840e01010b054a8041ca401a191400303403100542c89496402c0711007040c4008100c0c00c042e55050742003141501c0d426401c0d00c0950044008034016943d5440002c1d0b8140c000c0c13000143c02c2243c864100d8881c04012000360b010303404443c010f580c03021040e202e55002500030110103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4944872 1250 4943622 4943641
    0x603020a12030507080313050a030503040209010e04080d0507050408010c05030103050607030b06030406020309010209040204090c1107060e0607020a03060903020a0c051c021003270303110a050901050705010204030812 95
    0x30404072400707002100072640c008120f0312130708000500014011001c1910610030f907113103a03825544403045581c000072908000d407164108880c00c0380306010410000c14101d4141c943d4a014551011800e401c01a1090a00000d41001008101081814000054104001d000b90b500e603030002d03101d441d5a541075043c01400c1040080c8164145401c00b2604000c0e915540c00716507000c0d80050b0010b840789c91304141389001e4850b1107021a8842e002044c08207010030740b64404215100c0036110355003200400b010880e280c0781c561081d00040f40d02e60b10091501d041c400001d103210b61004040c403000a840c0c0d07503140d040f905204c1041e001a84401c02d46c108000e12510301300c020781011103004030800160322581002d001480300090142c0041c89024140e58040d80009006407400021750741442465550404461003503c03082c1c0002e424114a120100e11100c2126900101d40c0d440629082e0f1800c01075885600c042c200f202d40e5035007004008086501d6002a0005205d81c001482aa08004c64130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4946122 1250 4944872 4944889
    0x617010803030601020d05030403050403080304060b011d06040512030c03120702060903070506060d020402090d060209030111041d07020a14030a0e010203030906180c0306090109060518070501030504110d06060302 93
    0x848103660040081c8812aa00021070110119052400e0740d42c030b039501e14046071b13a0f0081c3da100a00c600d802001340000c02ca042e400482805001381e9540c9a810140c8400c241c2c04c0d000352501c2c1d5040b810410040c0050300307207000106074031948002200d151042c640700c11803950784144409100030001c00c2c1401080c540c144010f541050001c4002c50900d40681c480c0c03622131802a24191140904203800c10031500c17107030183c0380003000c018042c80d8004404d00b03154000e90300c00120706210754039002c504095440340c20152403e0341c4140700d0758605000c1c40032107010580c2019100400390b1040300e8100c07000800400b580341c4080c0c0e00e40d01942c0c07596030414000d41003803442c1c0011819908107008000c84114002041a40820310328414685401c41544450619142441d0150140150410440c08100541145400c030748904020881607983c015800001c40c03c031581240e05410100c01040158460b80081c0e4000e40904022000c034210040010010380800706c040744e0071900c5010800a41c40e06408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4947372 1250 4946122 4946129
    0xd02030f030109050709030618020405070c0b060d1407080c13020406020c0d080c0304060215010504050103050d030504030203160b1f0506070303021b01050103031205090c150a030b030601061701 85
    0x11410104100d180301594001400750074085690351001030603452103841d07001c009541100080010a03c02d5040b0795240b40307110010303409142071201290420740b241500761034280c1c0003040703a01e440e1602800c20500d1000c0040691714a0b99041e1207010007a000c0c41071400500e1142c0041030103000c1c14060290160301546031200303192040c1310070840d90350046a54591940700301c1d105c40b01c0050b83d00d400c581c00c1c0202c2d0124600c5100229000c40d6164002491103815082a1980c0e90541c2e40c8504120903920f003404000d140341c20400303100e48154080c0d000309400c2031103801500d090240c8140c6c080c0485258460a40703110010105100b62103802e40c1c45001c4550b04100d4823007216042102095451042d20710040c00c00d079000a08180c125180a002c075040321005009200f2541c0da41001041d01e000303c40301c1c40242d480c10300410360504000541403400391000e0110b84610042c00300001140d00540101020306842c0d8190401543c0d05000180c0a0a042e441d003d20750780303c045004044020581 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4948622 1250 4947372 4947377
    0xc02010504110415030b15010809070803090108071704080a080603062a040803040b0918060a0527040302060a0c0306080a082203120305060105030601120209121009050d 74
    0x18240004115803025420080302d0590700410101c1000c2aa005682c0d10765001408854510052082d60040d080302d000c10f004003680c0d0b403070300c80d02d520160fa900c89002c2e20494030341e5442000504910b50180b03100d1940304040b41801c0300000718070424142c103014125803c5419100c0000c004040a800090450f0030034420307001400107180000d06010740300c3e800d2403a001c500d106100322100b00f0080744c048402400b0900b003030b40d454560704c940d40e50b0315800040c160781c800d02003040c03c07911041d0800b0744a8481c80f4010101c014031450601030081411600550200302a0740806c0c1c2141000e06500c007a0045d0302c2076000f415145000f0100c00c00320380b990301d0800d00705408e11034100300940001640c00046900410072583d58680d84c181c86c1c91004151b040c91086080700d100020074000b661122403402140c0780c50610907a582e00c001103a291204036001c601041c041040f107010b070401540a01406040034000240860158030650320b412003400300802841e841c0c62034281040030600413464880c0c4c150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4949872 1250 4948622 4948631
    0x70606090f051303050f090d05010b010905030d020607030504020103060e0f0a06090b0105070206090a050306160207060905090411060c011107060b040902010c1103010b130203040c0509010b0f13030212060103060c0201 95
    0x840c0803d40d0418000c201408004010424060b0341040d1011070b0218980104400c01030945454440d0280c0140c0c40c0b1035001c10400b07580014a4140464010b000081541c050300701d41d07940c91303000d41c014040070700160304050380d50300c02068108820350358038040c1b007600031841103030701d0100038080c295400d940010084a0901c019402240d0f0080d058601856045130425210180c01c00450340e0152241e006950500c990030a11801c03e0486402150201040e401d0300c17025915040e06075806005817141c150000c0000c80010b000c1440058001614000102075925003405050020309488000701e460010900000711007040000310300c248ad403c42825107050000341e90036000640743c1e441c0c003c0054040008882c2202e55542c080d40710085118000700f40030014441d01120704000e4004880894032010000e00102d6585008503a841c121284490307000d14154440c2d100090076049905a0007040c8061040030006903101210840d050481400070049507146041440c103844031100b0040669240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4951122 1250 4949872 4949881
    0x30d030c090909081201030b0a0f0203041a07020a080a0914030a03020a0b100305010603060b090703050105030304061103040503010204080a05060a020a0e1e1503060102010b0102122a03070606090f05 87
    0xc4508003003250080e58002900c0030f070b81d0070000b00e41d11031314900b20482c41c2c10800100c2080003e0782c0312801403546140800c441006183c184007248029500501414103030060140e81281c005180355204035240706640740030000d6030722010280c100e0301c0c180010918803030060189500c15018600b60f0b041c1103004140003099034a0280d2108008403028080d10f103403000007518503a108a10741c00441d03014000b0006160750b41030030700040910900c40741c070480c0c0d55004a10741078401d0180c5416190300602540c078080c17503c03d00391000c01140130b109100b40001d1000040b6940c0a1010380001d0020601400648650b0719029051240040040c82454414020300c001a540120240d400c0002a60003130041e29000340204881da03121000e4a07440f4003417500f00e40200c60540091401403100fa0002c1c0600c0b2099001661031b84c840b5040035004500034005091155910042e800341070030340280c081c2050500d46680c1d411035102d50309c2650015154102000102080c0c4626500350080f02404c0066040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4952372 1250 4951122 4951127
    0x60102160b0307030c020313090209040b03010903020c010e030a020405180d050c0a120302070803100302030c01020d0804020d06060b040303020303040c0b0306131a0a090605030709020c1c09030b07020c030d030c 92
    0x1420150070140d45e281207450b00c900030011503011007400070300c0d2940d4903520b40c0d00101960007403080600850602e400c00c405410140035400d00c04d981070300078241126106d0011162080e054881d50b03410302c00c000741d01d000b40c5c51724404c446c042c4455030280d00c20a8100881d440c58070088030f08090030000e003080b150304401c8002c036066030302c1070340000b2400e501c111402080700a80101d0700701500340c01c0000148003441c1003e40d52102100e03c260f01361a049560030f0010f9071901d80d500314050209800c040010018038180c18840c5102e8815040003600c1501c0e01c0010744a504a40c008074007607440002488180300c1901c01250003401c2c03403c80e0514510b0103002150641c070700502c0a080550b20b9950028420b000704029035114a0040c0c101201350340c0d01c0580340080c04a903c0f0710b03800303805440404640000507008407200d107403040b0003e0404550111043e101008084d450320100403440c0800b0001038141d00703905028103607507401401e08030a00e008240c284600010100c041c54902107a0421094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4953622 1250 4952372 4952377
    0x1020312010605030403090905071101060e060d0b130b07020a0b060d0c0521060a060303080105030a0f020907020309040c03020d0c0207050112020c0f0708010501030c0f0b0909041401060608060102160b 88
    0xa21503d4810340340d032168a820f44660b0166003118050b90304080400c0406a48110101c1559901c00000d001103591420081010031060300d55a4000702c0303290b00800412924074115800481202c4219072501003602c034112255000c0e1009401600414010018070007108211500030f00e00315905541602c03103686508520100b445064024030381da002c84011400700722000e00382107513040c0903520070346080100d200080800d8041100030460b60000400ca606000030400d049aa020f100c100e50803940b602086121800201540c0440c4010008812240c0341c50080e0303034114006403400368948040d040f665007661047d910038001c40d40180410803041c2e0f4082036845112100384d50040c2d0b64070005250a040900d0718601103075504c24100c000500d101c0561200d41203d010300b1048200e0360311408080c0c10204584600c2981040030300440100385040c0880607045817081c103008007000d840710340b001d003990303a982d0240010551a004208542d45c05000d18003940c001c02c607032503c001707081080b40d54050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4954872 1250 4953622 4953629
    0x105030a1401150308030a0f1a040b06040306020a08040213020a080711071d0906090d05070201030b04061e06030609020a0206010909080903060906010603060b041203080703020d150302040b0102031201 88
    0x2419041224000301d40d0030343c00b941d45203000a003698007680d282c0c24141e480b030f4015541070340c00a02e05029902c2d00611752013600f0001046072140c4122080c10030420025010b0b0307529117540410100800400a0314910042c09a5440c54076034981074a802d0040003280301c104560b07031751518010001c6000c820743c0321000c19070101c03590418a002c0309800c0401860442c09030802c464041e5900713420360210455031400c6104030f5020b8202d030b52680e40c100f2025203c04a40342c3c41000f040701404034800540c000e4210003400c1e1400707000081e01c980d0300c042002d402501c2003580034044845401c144015030b07250140343d02801158005500d0301c1c402c0c80009586401c148101c002d1603036240c030200100003070b1504132101c00900500721480d900704044000d4440c02c080c402c40307020900d05440000d85403080b40c20f403800c950102c515245214040e0f00c0a8814072002040541059400c10030002400064401c6440d20300781002610748450542c41488121070120869505540c001d0040a41c04450107a03000d064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4956122 1250 4954872 4954883
    0x1404080306150c190606050103090503070803090309090a0b0301050901050705090d17030708070206090d090b09010210020406050403110a050306071115151008040803010501030b0a030b0c030106080a02030105030a 93
    0x3030720070010340b034903007030040001c00d032443d008600c241c0741d000c0250801106180e014040130441c0035074031401501141c035004002041d98005000c2a80810481d00280d0b51005143e01036030700d010b8001c3c002901402e0200c1d11820444d540d4420030159003801d21406900000503c0204014140444080c090340109195644078801500aa400301f02000c0f03051100446400e40164032401d0605d00507121640032100c85005104a0300000c08448000812854024241c0c80b041ca1840c02d150124550383e002c4804207040d0310414500500131010b80c40144000d10059503078549a9003513103060307507454621080140c80b40e11200d1052000e5540800c440d1b405c0a03950408a10703049030302a40c0e83c2482d10898401c5092840401081503100401c42e18030031001c821a012540c020200c0000c0e541c200d4290380140070f00e003042c001844071354002d034411901c030302005150900090350303a580c1c842d101c9400c8400d403084800c040010080700d0381141c001c50304107007041c00650a640c10100860740c0c1c0c1e80c1c00c0720302805 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4957372 1250 4956122 4956139
    0x604090501060803030703090b07020705060f09030f0703030201020c0705040501150f021501030b070e0102010203040506180f0618070605040b0708030402040609020a030504031803020d02060c160801050403031404080306 96
    0x1000390960184004100d48400e403510b134a80b03441c0140c01803d41c00820303101000e8403c0000c0c003d034404960002590f80c000c10403402c011542c0d1520040c3e4005046690301032041500c0d07000c45203c1002840300942c8070340e0002d40d4030350f48035444a06200d030644c4003500540c00c040051050300090290188100c00918203074401d040c0880d0104d1412032502460180c0400180010060040c91410548a40c0700340d1585024400c00c580124200e10040f03c020300b09800070f101003150313554000a03c04ca03108000080314924030407118481c0c2010420740361600d0120f02002c003894816011303c43c0790014441c0741406820b0a250940e000309612940e84014090400040028110758859101c8809000c200b00d00319203461042101500420040d00c0c2600803da120020844500c082003496050300e034090400c0300303007001d1a400e001198000d100c0a20880c0036040741c04441d00c807034020507402007444000100c0d50341400d040250488894030a010303900101d0030100404a41380b04222600000143c440301e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4958622 1250 4957372 4957391
    0xd11040207080f040603060515030c1605070801020d02090301050615030a02090a1d3702030c09100801030b09010c050901080604060504020408010603060e0c030c0d0c03020a170607080f0604 83
    0x3074602c6414590f4610020202d0301244a56155001c0c0099500c1500d010317810000ca40c0b01040280021540406071040402c21405a0359204091030800341c0304500302c4070055110350207203099811400720141c0c11540811000e81c10b2909008258001800b0344580641107400810480d40e484020110300000d5000030b0040450f48400c4810402050001c0c00400c0583c44441c0042e081281650040f02c01203d51180c86440303140502e411107516404403001da104c0901d007503c100030350002042c1c03061000c8140318000d4192500c01c00b06160600607629502c02e50706500d8052100140030b41060a140e2410311890216038014040310b02048007420032000076584c0c000001d0182080d90042c40d0410300100d0700041d5104150855015240b003604180400d040c2c850710503544004d6100c04943c50380c00084507440d0303400e004140802a074040c0010300f603125100d401007602500b09a1051003050300c034030f081c1140203005210306e0740c01940034a1301e24400d040104404014880182000d88141d90320201c03d0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4959872 1250 4958622 4958633
    0x51005010c02120f0a240510090b030a0602160302071203020604030e03100603080405040f0e0c0628080a05130f020f010201020c0f0d1704050709090c090f05150d11040207 75
    0x1c4c1c403403440e000112581c00110385440039520300d88840b000c3d1051907102c65000d8031841030041a201d041500c2030384103070601d803840c0f54000d440b541c100b46801d80070716001507012500b0390006203c0100d1040d10942264880d00d0001d191030341c0c85e801381d50900c140d1500040000d9021501a4100303400d45060703281400804000703410b100d50010054420740c03411200104200250b03024108450341145c1c20010280d00c41d0366001520b0600e900700e00103402042b030034111071401c400a080c2008a04041c002d8807038031501c011441954543c0c1d040086440c0c84100142a4100d000b030a03400010850340203807030343c1c8595030701c03400b203e20b410004e11a60b50016200c4059100750f06a50b4581100b0341104d02034001803860316103070074018000070002031270051b240803078090401140e07020315806002802a40d1500000d81c000380100d84044a1400c1c1c1c90340005098550343c007078264103207412080000c1d1420000758501c1122580d480e00c501910700840002c011444440054640c0d100944015903110300702e2a02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4961122 1250 4959872 4959883
    0xc15060503030a020a03020d050f0301030b070201020702030a0c0e0109021603030507050c030711100201050c030f060402040b030702011d010c0c020607020402070c0e0405060703060b070201050a1806050706051005010c0212 97
    0xc190507200229010b894180d0000c1c83d26011070094003520030085001d00d003141da40c481d034140c8511141c1c04000400c001446041800d91004040c400103051240d00d03030009050061100042d15084100c007024440710391420302940c01418111400c6241101c0410440000d030400d000107824555107000248007a8000d508446a44a90405403075031101c1c0f40c5031081c0412030b05031500d406144c480c802114681e00520669008680d0f8800e264155551005034074404200100101d801c0f84c4c0a104c001052542400914020704080c0c0010a0311141c00d0304842c9036242036080d03101c40780c1c104034149c0d43c00c80c0c018110101031a010794545a45148a0001c00c02911809400400303004500f0b03c00941c0640003900103014900c42d070b055910f02d0b102d41408500f602d059004d0101001400c014000c019800740000b0203041c030050408030540005058464107030705481c0c0c010ba0108200040c070b4010040c1c0c2c1d114541c0d20481003101c480c0a103083c400001c0030030400c500000c0c0100e0b829154204250000c006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4962372 1250 4961122 4961129
    0x601090b0301080109060515010917030c060403030b09090a02010522030803010603020703110609060606030403120e0304050a050d0c05060c07030605040302030901030605031b06030a0605030102031f060c030c1506 93
    0x419580e959440c1c40d20f500912005405581c0c80b4503040100e140c5000882425501050507943c0380c400508001086182c021115410340b0300388010080c1ca40c00b540f040c005140706a0194a000412201460a2000903c4020304c0b50307000d0303007251000750700507130300a415500d81c000f0445401c8070940e082a11422507440343d0704007034007143c000b2000041c1d2a0b4541c00814415100c0e580b210700041c03444001035900c0c64251602211a0012000504c16042407405191b200f4001e180c03541a45060310061021105401031207515070700002406d1043c0d040000f400e1004000c00e550000c014801c64665814100b454022a88151400240c074040c44204008190107103422101c2040b440c1007d240203540d9074000b00c00c0a01090034420005241d20700480d0017a824080e103080c00614a20032030810902d80d00007072500c1c4003103940d0b040c049103e0300c00f4400b45104030035040b0351071484071a26110b04d94904035607100c04200075211400e040025403050300a02c0c0f459200403002c11098070206481c0140401d0341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4963622 1250 4962372 4962389
    0x180d050a020c030a050304080106060c0c06030504060b04020304060b03070b0a0e0607050f030c010504031206080d03090305040801060303050702131104030f0f0602120a05010501020d0e01050306040e03030106090611010b1503060109 101
    0x104c4c06024400040028011a510400208080369072508290381030707480c0031405002240c00030002c0060500030f0b0801070380580710704400551085070600090498009a60544800369948800030160504000200203041140052030034002c080f81d000380700000090f25075002c0c2030040f5202c01044420041e40b010004420f00343c94071440c02d52031840c02070004403825800522140d41200b5114400d11030704042d100000060601600740c3d06007039024100940040f01000010400014608000c0c8160b0000e903100b50303965a03450a5030f004100c00c070301d03c4080e5407440e40d2030407460003108124101100d00720b03548408030241211250401e9051502d4030440600b0301c500010346501c002c500119682d1107000380b604100711b103076200c0004a0b52513030199940e4011880340304c030030885d942c010006564002c030020404581d41100c40000c0d810340c0c0080c0c2c0720401260000505005140c0c2180390500e803881c2240080007800b0303002d4001384283e8046800c1540008000000c1513003a40324a0569000d0010308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4964872 1250 4963622 4963633
    0x3010603050d0305010902040501080406151a0406030b0406050d14070305010203070f02010c0201060e0c0c0703060908090a0801150e070e03061015030911060310031a0708180d050a020c03 82
    0x7424596160801c0011030b1001916020000c00e9440b143d2081e130b400d271035041e5650110380d91240d031140c1c0204080340c00014041e1040d82c00060644500340030000141101d0182030311107162103405030035250940c646900c0380341400000d2000b611244006000c05411501034803140b000c2c4030310035041071410340000e4030b5940004100a4001d80205100c0802481c960080000d86c03000c00e802c030b00700d99141c020500b4400783c400c08144413040d21005401088200400d8801c00d56a0f940c2d5070040701c854140485103004041403104091030980800d43c010401c800003804401c070b6852030441c01c030015004103181c04844001140c0c819100d041600c50109021301240c206060400d65000c080541c0c0c8224000780e0049101100628828020040003962000204095921220821038583c000400d0219041444100080070440e00e070300070f000c1100e1640f02101e07181090407008103101401000e8855644002e03601c01480c1e440000c02601100036440c2caa41c4820071a8001c17403c2c1511200380b254140303d070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4966122 1250 4964872 4964879
    0x13020a020c1305090d0305060604080a0606030c0b03040f0204020304030309020415090509030408030301050d0311070e0f010e0103080304020405040201140406020601150903030203040902030a1401031101090503030316031802030106 101
    0xc01d0003003540c08842c180c001102203007004050311400c4914070690b4200c2e545444a40340260455500428000c1025007001e4541c641e880c03500c80c10f01425100302d030b00d40b02c041052002120503c17000c0c0c11420003081c55413500751610700f26200c20080083c0544d600200181c18035101f41c1c096019150700820070300210400c42201101c00c3c1681c001e800d0703090700d0040403d8010400000702c3d0100c61480f80a541141c0ca06000c100301962804025070911800c1c0c0080b4030307183e6060100c40050461400c82501c01d081191440d1003451050708001c812400340c9006001141649060b01c0d401681240c02061503961440102e03084c40301c954404503800000f05020a101d0b80218416058a01d0b10619118150012004880c0082e0320b210140140c1c0040109002c0031700d07107030010f661185804501140c4650300e12180c500440c005d0b070040e203103c070f84102c0b5003a0b0796a0010210b40248011002503003507040007d400d81040914441c02d8080c5030f601ca40192054813401c0e007811045800034000c010841d603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4967372 1250 4966122 4966127
    0x402030c0c0c04050106020706050705070801020a050703020d0c030909050916080c010e03010501120206030702010204081e06070c0309050d1104090b010302030609150a05090a0f15110c1b13020a 85
    0xc5044400140181c071140100341c01c040c130a0790304030b4075150300030440c0030710f0400150f032a90f010b0b986c01d46c4c030340c041c40401043c1480c007400182a60904c6a88140e41c0e201d403802c0c000e040203410b000290410078400d0041001c2540030750400c050307070310500c030014041c2c5030000740c5450001d404040700f81d090020b020001c0e001d14085482010b15800387c9440340e032445070908050032074409000e04917031300145161140150401e003010b568411114000140b0f01902c40390010302d17003c005001031820300c2e065402e80345c0c03600091041507000300030350511035162880c82c1d8000d000706907507009045c001d100904015003405007400200a00303840c0035000b00300d580c600382001d1081c40e10900050380039203c2d50001c103e03204030020f109041c012040028140e07584070240c041d0094000607291000c54420703040c9841c041030401000b4880d00344640780d400403281d01414607405680c0454843c4204600c00e0180c40300c186400708031030b6040e28a400949005008100c00a41d210791045025075010b8404a004603070981c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4968622 1250 4967372 4967377
    0x70c02090702030d0b03030702150906040317090111010c020c010e010215010f030c0506030108030306190b0a0c0605011205030405090703020f03040501090302060c19030b03030906130f060c0b0f04020d020402030c 93
    0x4d0510005016a190364400d050b540e1280303a800030341001c8085d001d50035505060014284012000308480d181554a4071040b108000424201c0380d940c20001e45202c080da0800c40000300c1c0300705030000740000010709401035100c070b0304450114140030304c402408203030345e10900020117560801e01c4d102540c0d50311405404185c3ea0340340012180c2460307152000c5080d05e041d0f002c1c0ca04945d00b01008510316a00c00c001d0041d0480b0044068811002d10345000c1a400c110304050708411038035503695400d0640b203007006420b868040e404001d41c0140d480c0407401050000c022a41554802c0d0340f0004c01e5142c401c411802849100e280d41003540e008801d00c800c01106402461241d8000d0b821541c483d203d9411064041c1b08165440e07081e20b003e0081c241c000d50190300051900040141541d00f0480c0c8000899440d5200001e1410082c0c5101c1e03003800402542d1040700068022440c00c6000c0e103025540e0760310500d10150442c440a9207182c00901196192034023080d0240d40604250b440c0e081c80441c07944a43c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4969872 1250 4968622 4968637
    0xc060f0f0902030d020102070503030103080d15080105100906080709022a03071205090d0209060a0302060307030212100308070b1801020a03020d14060619050c010501060e010906110309040203070c0209070203 91
    0x2801481c4a00402034414000d0303a00542d004002b551459103959105038550780000a00e110040c0c80d00b41003088035800e0a0510b0091021200200e45031a2040100e550b12141750401074410f860580b080c00203110009004040d0340b80060300580c1d814407080d29440301444c01020300c01c440c803492010316554401002401d60350f07202e62100c0b00202000302c03090364180500715074580c01600c1c1040410151030300440c0180c10503c041c6c11507038a652242c0120300d065008136075000200c0d800003454000c2044480320b06900204c0c00915261a9065540d95882031040d01c0000d00f10f00b000d05d020032146940b0f8205c05580000c100c0c0210340d030361a0341c10090f002c0e4004408105225180c805003500b0140701c1c40c0b4041c0314003c01480b092800540b03101c40b1490142505551007005001d2104110056091080c54042c1010384c44a1460701e2065000410307100f4240c0140c401c028130400010780414001007690703d000c0d01103401585a0791805804c8031320b07060385003020750300081503428041d0964000c0002d1820 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4971122 1250 4969872 4969879
    0x4030e0102280305070201050706060b03100603020705030d021b0f070e0105030c01170a02090603100807050d0c06081803070c0f08070602030306101715030d0e100c060f0f0902 77
    0x128000380300c8036160940b0111200c40300c0c1c07542d03030b0100001903c540010280c07644141070450034540180c807050121140351b08010b4010f0700002c2400711440e0705004c0310008010a1070107510f0001903a503100c0e02ea001d00d03440304406540200b41c0c000459040300c50a40340301c600c9c800711407450102804003640d6603007a208210103501094004211390502107000d40c104a010303100c0d07040c2c1c0d07010304150742041d1100500b881c0351580d003803082e00c81566441000b580280d21400b20ba03420300303042180160034100780750310140c8194102840d4070001040482100200c4025051001071a070390344440740448444070700150001c0c00001180c0c000c0041d2040d20909540450400c4c0060a0700da405040d036541c12400f440001d81c0c4144001441841d04e40a421071650240c90f2035130210340410341c2481ca0390010340301030040c40f10000a412440c14200010407504525107400d81e01c001d800f02c042540c2d070b07146082070401c00c00c1801c135850a002c80c0d50002c800c008240881004000316052950703004010b1007904a10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4972372 1250 4971122 4971133
    0x170303060a0e01060203030609040813030804050f0301020a17060102010f0906050a0608060c07060b040603050d0804050606010806090601030e1c020f0c121903020705061c0e06070801060e030a050604030e0102 91
    0x50040381072882c01e0680e10190011880c43d214002000900c0748010000c4506500401c40c000a04e400c2d00b501c080118454410f80391118141010004007611030b80310a030082c0e00c140601c1d41343c0b65212922480740140c0c460440e0f001d45401004070b01400c0c800b000240c113141428901c00802060307034403040c0303d0014180108032403522101c04589415055403401441c21040c00100c010031110340c0609481400148001039480d502d955a9040030003010140e40411418400c000c00c0c80000d004403540070000346406d564034a818400070340f850380041c1030b0a0400d42d5440c145800c04400b000784c00300407a851007403041d442c0c1007203030001d5485034146015002d5000d41ca41d840060b06001e01040140c0c40d40001a180c80c6c0c21003600f0314a40d000320300091b801c40c4940f4400042c036498010090000480d0f2480603c241000d412510099650403481080da80d4000000c2000195110124074150341191400414500400300060314000701c01c3c070045e14a00400c0144000c05401c2002021002e00c00e800740c85 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4973622 1250 4972372 4972379
    0xc041d0d020d080705091c2409030504030305090105070c0807081b060d0506060f0301060509040501050609090f06060f030901061706100501120e06090606010908010204050a0308030a06170303060a 86
    0x7601e0318040001d0740702007903d0b0408202c4c80b40c05007000e09194100600181d444550480840c422844105070a540013a00c800e0352040345400325078105c1c3d20190701c240910080800f59002411403080d80300150400c02e011900c15050381c0308e0704c115030800d90000081c1030b03d15210046ca68403030f169882040b815102c0c941c00803001a189160000d12000300038051400c0845000111014010090102d50701900030040602c00840410146029140c56900c0301d482e4420782d0180011100c040e044984580c9060120065594a510556a1200e2443c0e0b640354961591404588240222034540d2411180441085504071055018030216920100d004100511140010f9116502600d442d5906055a002030045500070704109800011040e400184040024042c4e418001c00396940d85a0350006010f003c0c10350381c80100030014003502c070001c502d0180b40c400003035400c880520008110240c0440028a40b920942c4071400401481001401041d06000c0c595225032041303d4251040001c1c81011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4974872 1250 4973622 4973627
    0x5030606010224040507030f0b010608151f0201020913020304020301060f03080706020a140408010c1701060e1203090301020f07060f090206090f0f10050a03110307081303020c041d0d 80
    0x21101e903407014103000c03c1c84419500c50120000d00410030340d541e01c105d483c00000100440e4000101c180182e0200315194148100200903801c0640714503901c84000c82100703965178800388841d03008140c00b18a00b051502c404000d9029006132441030f98001100304025a20345015001548614070032002042925100d00401e40841114000680300c1a0103001c407000240d081c0d8003d21443c501400e1268a454030b545008010350302603000744070181d450380803048116411250444008030300c8080c400403907060801c001d00c108241c1118603c5004d604048a40e0344c2c0052003141c0c13a00a02a000350340d240c403a8805c20180e81d10401044400d41e02c2c245000000d401944100c1200b240c1c01041240b4102d07148041282e502d1212000c0c9500c0508140302d01996500c10041d5001459561070381030301c030800c0d1003002d0100c6800c0c46103284080c1c402c10422441c0c583c8084611b500210300c032100d44405240342030803442c1c000320440950b045407902400c1c00703618408501302c0040d00c01c20811620804a40c0004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4976122 1250 4974872 4974883
    0x1050603030c0316030905060d060503100504020609010f05040302030307030905012a02040504020415090c030b010203070f0201140403081201090609021603030e0a080d0506010305010e01030c03020402030406180507050306060102 100
    0x45400620012201389503003020040414064074060200b29152000510310360311001020790442d0707a8140400680c14103000303500602c0d14141080250386400e4010403120700c40c03111841e0400030f000807419000c40c0a002580d010710703005012241c84810b1460b0281840b0410b0160501099400d00303d445c00d9620040f010810b9213424144d55030140e800d40c2840050724010380220780c071a4480403000e02903034500390f840000b044051004140d0803c1020060102d40003000d4503811504108100804140700c111802e10140d420328241542580498108130309018075040280401ea0009854040401b4426098165150b00604201c101c0d034401e1010200c2c41b42035050342020410920101c0071134080c2d071000d00506000025103042d82260754807040d40e5801340680003000783d40c50060100b01d51740340c46180d0150901c032001c141d4550541e00c1710000b40341c00303100c024840c580000000e42000a2900b11a0651143c51000810b040561805e2501c1c0c1d8024042c8030f001e403151000254540d88005207 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4977372 1250 4976122 4976137
    0x1020105010503120d0203071b0606030308070e0303090609030312010306090309060c050607080601120603030c0c080607080406020307020a0c080f060705030114060f04030203031209010609050408090906031e0a050105060303 98
    0x81007817070842107500040103500b004002c101440300302105968120340e0446000303c0b16100302400101242140f8016020181c0034007000300f000104082120281c80010440e2507045c022628151501c0700b0000107451752286448180d002011440004100604c0c1e40008100d94441e03190070f10019100c6408440d205401030004d030039540864042414139000c3d85c644c45d04220103162042d00e1441603d00340042e5081ea5204800283d0500c00300c04c10302c104400d0703242c050311010340075040d2414130001c0280683c101610203018194000007041c9103a000b0442c0d0840e940c3c0c0312107004501941e520000745c4560b2080940b2506002d04d40002e41010720500880e41030b50007111002010b240e802081c03101d60780064480d502c2a81c000c000100160380d041025100c00c2e4100c0b40d0745100c4e49000d102550035500faa501614030305080c003043c00009403251003520f40c40007040c2ca05c0c812503501d04001919049101603882c1202e081810460400e07440440c4440031540108020310082c0c40c0c080c1815521b02ca03006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4978622 1250 4977372 4977403
    0x7090e0706080c03160e010903051c020609010209010507030f091d040201120b010207060c020103020d060e0105130902030c0103091a040803090f0c0907050304051203010801020405131401050603060103020c010f090201020105010503 101
    0x686030901d45004051850390746e901072502d40e0706640c880e0394440ca03001c008405400c148840007031060515504000c3e50758880e841c00c00a40c28080d285001818600417150f004003403261140e01020154400d40c0b02c42c004001c0310f2a4513075030300e60790701844600c04401d42e404c2e0f000915606615450440710f001d00154284180e0080505501d000000c441d8002e81d408105e040540070005403081c410103010300f40107403224152074019540340c201046544101c007108501014140000d600143c5d80c08910780030380540a0902081c940c00a240c000d0010141c44507145a041684042c0070901110170041c51054614004442d07060b011100c030382c0d690b00104246550300009880014542501c034801841d0400e105104885a980c0d8002e100d10180d00241c1003400b150394046020400c600c0e001c1016006810018820486442c0c41c0f8801d0301340d5101409031501a060000200310b49912035070450f41103060920080000c0d03011300581c01d025001e8444203a0040d0b00344400411240360208043e022480c480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4979872 1250 4978622 4978651
    0x9050405071401030f060e06030d020a030206010902070305040504020309060703060f0503031b01090b040503070c0b030106021b1201090602030f0f0601050703030e0a080a0f02010609020a090e0907090e0706080c03 93
    0xc0944a58140b50001d41810551145810714074040c90f4040c06c0c000d041c0100e00c0c4080e03460309a09041c40c0c000704100100c1158400407145000c2900401c109054900210015035161203a04064075244542d901680d0840d00c0081080341044d000310750140545030685d03044c80b030503540b00c8880411600354014154950800c1014011915800d00641c8000040d1800410321050b1615004241070303084900713603003035040010308104121016044002a0038044a018115414000029a01d100c0b0b500b40c542418503441200304d03a9601c4518071083c42d40284001d00404a6914210b8003940060324410130102c81003003ca016410555a01840f441041c2c0da040c1c109801500c2c110060000e82400310724500941c12a00007007400280107000b043c245440700a001d1000e054000d0841f00207034060007101d40306004402c1800da10501c080300703d58051307502c00e0498484d90398072810b2040d940e1103303480a15217181e4010000e00881e00e003080700c440d510f4034041a558112044c0c020302c411100045109280e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4981122 1250 4979872 4979879
    0xb03071e1b06110f0418050106090e0402031c0203040611070b1204061401060305070210061424030109091208040b06040e1005090102040504110705030f0a18030803010f0905040507 79
    0x100c0c008261180d02a460104009003551507402c2c040c1d101301e2000c510040c0014060001810810a80c2660f0440399020402989071000050400d1003602a54058503000008101176607020032226000d0003e496084c2555021508040d507039070310601c9450701241c0d00344d401c90003c84011030310b041103811200e0310901e800980b00c544400320314000e00849400707a07944800504102c8200d441c6019010580300001c05041801003e0725101e5061040b441c254103004d0305020385101c0721082110300c003041d1742c0090100d00f0004240c010000c0c01e50f00c1101c8030000b100004000e00c2c41d030001840140280c8142c001041c440f00c080328410350460340940143c030300c50089016810a82c0c040c0c4522140081550110518080850305599050f58508180c0c0c3d00400d0500c1145840d02c83c0c180c00c1c12a17805842d04c3c0c072030b40d66951a140d0246114030f01c1160300101e065070070a03000d079015144808540b03854404c901d490345491101a0028080e41c400d0000514000c124843e0500c01c1600481d005070050592610307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4982372 1250 4981122 4981157
    0x40e0a0b01090308030a09020a08010506030703021009050904080904060e0906071407050d081902090904020402090109050d1202010b0406050f090603010f060905090f0307030801060c020315010b03071e 88
    0x14400c04640c1000b58584001010680f10800f841c01206000004601180300c1e0040220300c1c00d241c2c2142000740d00d0070003407003050b139000510042126419038512401507807460f0141da03504016806180c000d1080810072041203662402040c18181c2110b080162940b0741c100405421000c4842e40c00950044011071900340c0950322840d10358400b26105132820016a032411f0030050b02c040c0e9040452503c01c180880500d000071000c1003d6048201113040a1098000518240c000340c006800346a00141004a60344107408190141038060302c11401e00d0018034009501d0b01e9440280c4d8015468114880710718503240c0180070441301e006000883c5146240e04100c5c0c41c18010782203d5140d9602c1000c8032400409002d044001c04451a0025007481e0681800b82803200f42c6217500201d4208104140c0043c1c0c105503068103598035031400340c05007902ea00c007080c50010118a04065014044000100c2c0750b108401144a6405036a60000401c2d00810002c440f183c51b40c0b82901246d080c9108000015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4983622 1250 4982372 4982381
    0x60804050709110c010c0806030a0201080a09020901120c0602190206030a0605030d03020a0e10080f0a0212040f02010e0f01021c0210060b1908060d0809030f0d031a0402040e0a 77
    0x40c0540103031800260380704030410071a5440c0c010a044890b010880f41a00c001c00c3c41540204e500a0801501074a020400a501c0d000c80c59002814042580e006c1340c03660304958800c42d0784a40c05460300400c2c3d40c41d11811507005421540842d103c180f0240e011030014030229004c5462143d03160348162040c0d05501300851070f0001010801101c2d5240380c0090165810052140988400c0d10b0059664492000043c0031b4051810b110b0f000c0c20305400403a16a6500c0000282d000c80c05e003510142c580c80e42e94041c0080c1c407070b82100e01c840341c0044080c00b06000d48100240300303c038030036214000a690400c05003c0c1515400620501580011042c481c1d2904a400990401c100d64416243c404007082c1c81941200d8194211308001071000c54061a0b00000318501005607000341401d171014a0a42d0001d440c201e0300f020700600d03820010882c02c001d0745080010411400040f400d55180e20310b68000100200040c0810400b40c4044d0700048020307003458400c48081d214840d401900340e031381d02580f500140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4984872 1250 4983622 4983631
    0x30f02030109020406060917060606030105060703111501050405070305041101031505031009060506010206040f030c06110d050405070b1611010207030f030201060509070f05090112060801020703080a0507030203010f0608 96
    0x15502e85450340e005a403103125120290000c1c0c1ca580744141e041c0402c4456a500c0c150109005901c19801d1004554641054030304440c01156519526030140c13408880d01c50311079111900754420520003900b480030b0b580007541a80e400f5500bc00c660740d03803a0800c800b0755900f950040d1244401112030100c0d54441d8120505c1c01c0c0d424817a11802a9441001c40d11340781c415000c00117980c0e5103086d01c03000c100047c062150090000d00c01050f00741001e45842c0c151014942c4000d0078065492064010007203240c02010040b44001c802d25114050100d564014001c00c4500300c03224000c400003c20100d146605440d100f9540e00ea0711180000607964041a0501407002241544901d8200000040030b518019109610030740c00172540074640b0f0f0911000ca640a86104203201180b410a25841e61010607141c0151007480c040b42c1c03d2030484494801449541c02c5000d5550000030744506068116070014003c55101004101c40e80d542c82e03080b0101e02083c062104910300a03581000554410f00c02103801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4986122 1250 4984872 4984879
    0xc02040b03030a080a06050301050402090a150e090c0103050108010204120204050a0914030a020705010e060f03070903050f0a0c090506150f0c0102030112021008011a0c0106050405070c021905010207030f02 90
    0x1850203040024515044034080d003000449440801c41200b0340d078010800204002d0b0020301140c1031075030000e00810340043c11050b10366a2040381c0b10281255210b4000180380314070f40d401081c1016101c0603181c61000444e603011a051000000741c1d484140b00b01d900300d580c0101845003410076a8200310252034080c22101d070380c81d2500c3d50500420245a5500e03d01111880110750721494440080e0400826034030041c103201e1181081c42043c0c840c03404a884900380690404d6581d91500d405442c0288a6040500103100301250080c4940c0001192061240600d191a0341075643d01a03000079a4030440e865600f02102c10608010842e51401800008142c1401d207410504000290b508a810980c42a01031480c004603c1081d814490a400d503400342d6850000b050750b04181c1d8003002c440320504100b080032000903503111158420340c085005441c0042040c0124144078030005d000d684a030909921614101c42c854990004500d00041180d406070080c4c00c1152540c4c0703824542803030b2244241e80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4987372 1250 4986122 4986131
    0xc020102150a0203010810060e0408280909060b0f040501050702010909050405060403110313050f011803060209010e01111f02090303030f1504020403030c080304020604080708010f0b0405010302010806010c0204 92
    0x25032100c80301c0350348220a4114010f80b03940c540415985083c00090518403542c7ca881c1040c03191203032441c0307455440f03500040d034180c0d103a1810490301000206a180d21103041140c01c2c8920704168003000c0c0108660920409011040c0c54510300400351182d01070304100302e072040208009550068000d0250240141485940c0382ea40d00303284026554102c0b0103c90a03002102008200b5800c441c0c01205000070b00003c608090750901200c0030340000d401100c0c8925142503508840d60305c00d4030103881f503030342c504e8031281c00982e05d01c0c00704041d4010300369050208005035901080f07540700e84801c03070708481208010114803080904c51000c04007008003d00b24070380c0800010706aa00c040000b10301440d030310441c1b050340780392600c6119900102c1c480c6461046004101c2040402d50080240c405c050b0450701c2c00ea0f8949551001901501c115844401d00d07008a02001803251410762050000210111003440840c00400801007181c1007400024042201d500204601e035100345200400c0038805840001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4988622 1250 4987372 4987393
    0x3070504090302011e0605030d05071e02060d020d0603050708060622020405060406020f01050604060b0a110a020a030308040b070201050106050a0e030a0b0114040e0a0201020309060a050409050f040b16020705010c020102 96
    0x6900031345c020581d41c19251100f404102d1410b04005040e040e90315407900301d0a00e282e554500340400345a48275039814181c80300030501950740d1041102c90112400104564841c070380e0304002c02611603848161840c1c02640350001d6074000c0480c21500c501303001005956007040240150201200d444111007406a09000119068507404014400350610384c00901030703060161301c81400d48000801843c011800e180c420030107000076a040d241c0020725800c0002a280000c890f0328503140e070a160182d4000c101d684000309054000007001e00441c05901d0820303d80e51a028281d080e15000e01c42d68000072401c001d840c154511801410180213001002e5614100280d1102414801c1c01e8000200400000942000500e031074403401c400c42c1c141401500b000b020760b80001c1d489000f4510031a02841c40043d10094491054003114003034424900200018207003034006170783c00d40048500711446215540441d181c0c01002e0b0103283c0103042503006050450070200115001c420105d400c905511a189451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4989872 1250 4988622 4988651
    0x1050a1b0602030a050709030305160303021c020c0709140f04020f0301050403030209100306030206120403051c060302090606030603060103030e06070c1203020c060a050d180501230105040b0307050409030201 91
    0x200da2140a15000768403401d1070315045040710b1010307003003400303205000c83c0801c0065000340c00d0b0b0740013041915a490540c5a68281580a07100d065200d882682600d078041c4103520055014021000814003110300554540885100b2201038061080400c0c80500010302403030322031018940d0061000c1d141102c003a6495020a0949d24140c40441c0400e8002c240c0b0001800c0121780c4110400e1141340911009180d40c000c5100351042d0400328400c0c00104001600349401081180c00000d0720356070301900030420124440050007180000c030b2040450300f000c9100b5143c40300580340202c50080c050710140c3d185580c15a000c0c58800e00d030039003000050140f54003041c011205d6200130004815006201080762a000b8140316041d842c46202e1b0b032042c0b02e0384401650110035651280404a0006200341000066900014408130002c00ca5030074010002c41c4038800d003003810040c00d00412009000e0341c0740c1c0c0801040c2c4450310301c1035402d42e1180e117040021b8034240d00b103e98011f0281c000081c0d40e1a000640c8d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4991122 1250 4989872 4989917
    0x603050303040b220209010e0a060803040e150904150506030f030c070f06030905060106050a02070e0408070b01050406081207020607050d0203030108070806010501050a0c060f0c0909060b0306030a0201050a 90
    0x25143c1c510703140108414110b10480c40703241c4e40d842d004208a0116550300140d2240d406005401e41c02c0403941c00140744034450361081000d4200c0b401201d46540e0369419108040788100c80c403001c2c0300e456503a00d07201e80c146034664a0080340d200801d4003041c440701e03183c00000c1100400d40f40d818400e009254248440610060800d811440054113541d410080304c01d1000c0c3c15a031103002018a0844040b001c6a00851001e055801503e03141d0343e2030030002402c034501009500640300800e840014042000041c40c01008424401c2c6400009a80e0350f8080008551061142021582140c8200303c4144911001403005603c003e01d11820145a41c4649140c411540c0c040400342c1d00000040c88081001c004201c003c105182c0248455030400b40020080d00079000000c040c46080e1058000b000300c0f94104113100ca00c80d15082003005420b540040104480d8813038500200d1510a021510f008130004403845007002034010100d100d1260f00440d140c0d031110078503000b040715404c0300b91260704880d43c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4992372 1250 4991122 4991131
    0x204060f030201031b0e090417030c0406020c010c050615060c0307050109050f06010609030212010f1a100302030405030f0f07050105041208060306040209010302010503090c06040308070302010c050406120f0603050303 95
    0x40410305a07040d031002400302c3c0c015100741c2c003070785013400340c82411107600c160307004038610381900e46d8140354a8070700d010322010b0741704444d00d4503180001c020007a4615061024100700c900075401c0f200b03c100d6403001507888409041014016400a00000320100c0c0305220010b00c06e0405002b036840c212040a4003400d542068101300c50340e0351264000d00500c041040f16107003218040b03001c0e0020307504d000401b820103045803000034002c091b200031404210f082940220001480842c080c0840d4034191441c3c541b03c480d0245075803207000d84602c103904080c464800d481c81130394024001d602d04000195240500d800c030029440741100c0030806140003030400e02a172401280300d8144a2515008072201a0041100a00d0107000340d018904100c05695001e0720305d41120340a080ca0343c0d80781c56003c2014109030240c2c0e8400e40014002400100b0040c11800505070140030368001c10400c0440d9400700c59030302c101c0c0709010028640444984203046254070084481180902c0018850740c1c90b990b140c1150011034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4993622 1250 4992372 4992389
    0x6110301030506060a0b0a1d030105040b040309120b1306110c030414040209030d1202041502030c060702030405032806060b0910030b01020a0303051003020d050709060b0306060d0b0a03020406 84
    0x1041041410460190488130449a4240da13a0824100401501a401841c4100049a410b94006014402031101141d402070003e02c02442c0500b00200c00303a0064030110009504c03503d000400308144081c007100c09500481404403500d4008000381c003c0c80400065586907614041e0030010042007008080c83c10405000c0d41d101c80c5400701c14000c01c05c010040d980502d004110224481d9001b0441c4100000582015034070103861003044402802182c000e66481c800c002003c83c4600d8000020b082840d000c001243d100e0340e5100320403a101d0240e40b08890701070707009001581d2000300c10020300e5804000c0040e00c0b40c40f1344164540c00140c48051b40104126180020700f0360040c100743c1c6c4030107004034083c1014400c012128000035642c001e69880542059680c102080302c491118047c8e2008680050078880701508504010741c41c0c25240c4100b00c02c861501d400000d804558006880c0300d00c00082108c0c0c1006095082e04001d841d441194690100d07a0f51307030210060740c0d188982030142c031222 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4994872 1250 4993622 4993627
    0x7030324030317100608010e10031b051309020f06070f060c030515010305040309060e0a1205030a020601080c0d0f030e040f1a030312010306090201050c01020a0203070303110a08180304030611 84
    0x42980190f200d001341c0710340c8122620010a1000740c0c5c100421030304490002101ca0096135501c40402d003d00c1c119040146109200c00c14507011400706040b1206481c2c040f40c082c0007000c40c034450300b002c5581a2200941180003840c0182031450100d016080e1b6a004101440ba4486140d44a000f100e46508050340442c0d90307401402001620007452010005082c2001c12030b506083c3c82c00381001102c4d02c40c0808000c3d42c00c400d4911a150003a808000741020076100702500b60b03d00c2d10544a0f00100d152100510a00000050140002614000405010300020b40c02c54080d02c1d404281d014006050b4180040410110030903103a034412a01e100505410000304403142032000103802c0b440d00103152190707109000d2041d901640100c03441c1100c0d03100c480003400070003520040e540c03406004c2116182e54404600301d031850360080010076a0902c260380421003100008141c030014090a44a40002000c6c00001480c82d0344004265041d280601e00310780c00e280c0c2d2070b5a07800554107a070381044100b1101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4996122 1250 4994872 4994897
    0x1b0e0f060105030f011703070f06050402040b0303030412181e030204050903090102120d0e03030106050705070b040b03130201020c0d060608010e06070c08090f13020702030c04050705070303240303 86
    0x101029002042480e1a500d141000e600218000c1410f003e030646d40305181104141c2c85800b04129011140c1c0901c8000034080304e0309246004001c2160280c0c051030500421042a290100460f442182e008080c0b030b010301d8402404440c10b0344200d40042ca100000d220204a03081120140381d101040401c0e81c8503103904500c140402c3d140c01920003a03c560080c000f090740c40ea0085460004140440c04076030321410880782080c0605960110000303c1c0c040000081001903110f4010000e4601034800c0b00c00c503980d226500f500c544628401c109240e43c09002085500200d00d12011005005104481d0314400c601c000601035040030700c1c211200c6680f41030030003e00c2d400b8000e01d640c0c1e241b4403018010920f4a194058241d21f007005006090382c90019803442260346022402c540c0840150842244824040c1000c000b9032007854207910a1040042a90340d5290902499201d07020030b903141800c180940c0c1c0c064014204042c0084950704900d0210050038450561250007035008c0d544101c400d401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4997372 1250 4996122 4996141
    0x4020102010e07060f0503040f08040e091b09040f0f0206030a0c090807030b0402132a110703030504150504051207030b0c03040807030809010b100306080705090105030d0c1b0e 77
    0xc40c0b0000506401ca50410041e60340c100a030300030f041c41c0d6414800d0b0340703580794542643d01003984000100310701c00c04038010500e008407001241c4901d031014210f4851003440071610b61f01d061804249640b10081500042c00a2036900c3c0d443e0400340320351303902441c202041d80014469001280d40413100c070f50341c410f50000c0c603500243c03400061912300003518000b400c50715500c01c4038030010000b900840c20740c1640c405014455000c2c0c0100d00c019031440c0b8109503c80005443c40282d00f580000103020400c1000c0303120004544a41243d40c55105e003850285007524029586440880300d07002c2c445c0c04d1100003416211100000300d4540b111018103026402c0d40b4104585250141a4046032441801004002806042198030031070701810910010303034800d51000d0140c1000c0486503085109041c180101c035400d80c11041c01c0c3c1d00c0d05010b03120415241d00030720072102c400348100c6525522803020700307180340d00500099420318012264840c241070000210207420300e403540018001d02c119030800c9800207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4998622 1250 4997372 4997381
    0x501020a030b04050108060103020105031f060e010906110601090b270402090f1603090204060815090606041a040209040216150f09030f0e01020c13050907050102070503060f0a230402010201 83
    0x1c0040ba070130461541040d80d0700d80d8420050100078184000040804e440d0058000741102e401d207442d0301c8540c995181c0300020038900c1e0203ca0140821180300010400c00d00522044d20f4440061008004a86ca060307200b40c090103003400620707003100300948120f0405204015461150465140340030043c240792041c00070036039005000020645125041c4402c0c10380c110100042ca081c1d910b0302007403c3d1603600000700281016480100c0070311030454002007110070501200c0c4038903000380649041c0d070360b55828081616806c1000c040d2030400b013100e00d003203480e01d50301402100c0c0700508014103100381d214087d4404101d440e000d0f501c0041410304412001000e02076800c068940400030300612505075409443c560007100e0b04000d01c000441c0000243c4d108226500e01a80300800250100082002c50070040600307884414035401021808100c95000044001c100c2d00043c00500055403403200503100c400000e00040f608a480c4c54110541480607961200c0d02c01ca00c0c140e5068070f007414800079007180e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4999872 1250 4998622 4998641
    0x4080a0c050402090d0b090106050d030c050607030506010203070803100b040308070c06020304060909020c12030703020c0f0303070807050d0f020703050319050c0405040c02010e010c09050307081209060702030a0c030501020a03 99
    0x102c2c01000704600a451746150601141c2d80841c2e182038507100d0a40d000d0241000b81c20040e0441240310450040c150b10492494440b4090070a45051b502c41c04400c8080d510111211405a48208003050000740c40500460b0301885032844420b00a40350000c0c0074180d1300c203034025180440d022403c901441034410b004001010075000a6203407903d0548060942c007d5442000103d6078040741411031048107220142a0607400004107a0340e203080700c0003600075009550943c410b80301c3c980449101090003c1124001c4142d5120941c00d0341d1210401c4410790311810304141035130380390704038a0386554850010381001071090721620b8803850102c40d280c06110041500140e8a8101014003542c0f10a0208076015035900303840229480d900c010741039000d40941204a00c0c50b6281c04c00e5000c1807580444850151a800c42c15504011303030b2803143c6651501c501403400c200120400140141d458040018030303010b8030180c10346800039550344491003500e40e01d034010780d10340c1d40005040d82070315414415500039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5001122 1250 4999872 4999879
    0x90f03020a03021203010f03060207020d0209040303021305010203070b0a051b030403080106030e0606010f030c021509060103020a080609190c0504150905061203031306020f0304140105070302210612010204080a0c05 94
    0x40d585490703510b007c40d18051102070a1a07500258640641d200c40302c0b243c401c07580140103524a0300302850007c0003940010080320704000c40002c0401c0d103610200454907155000905034000340c43d10005640240320240850000b07010240b240d000ca00074aa016522460087d107803101550b00d400000f40903a08001e4030071030355402ca01c0801c27080740c1e0802743d420b280000d58a0002802641442d043c1d160002e2034210043d02d00009080142c1c402d0b001581ca030580788242c840c416110b6680c5d84a80c0d5400c010303280341030036802030844240f03000c07500d903c140e15450080070905245503031200814101d0b841d01c40d8804000d4400203050020f0740f803030b0082a401c084143c9001c103843c2209210140c40f400060030540a1000d004d000e0000e03c400c40e015500d210f4600c80b40c05940e070030107182200b03c21085c94640d01d015407c0ac000541001d0081c030a032181c5256610b10b41d100307980000318516038000000d10184c0e00c0714600ca403560000c10248090000707002070500800480b550360902c1459480c0e15801180f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5002372 1250 5001122 5001127
    0x4050d0321060315050414070902040302040b100c0f05120318010b06160602310f06030603021003050604090507121106040812030a09050105040305030609090c06030105060d090f03020a030212 84
    0x30400304140d00781300c820140006290300c65140c111a41300544c0c0e0182c0c15485203400101da003001503401441202c0c07007141c040101301281003e005c04140b02c003008a02044000e8040ea0104001041c4180094461001d8510095201420415613007056a08d1451140302908044034480e00344900241c154045039102d04180d18102c1810340c00205000c0200416004511440f071100c0c0044043e18420413000c030a000d891200750300341c115110620621420703c0e040703000015a0743c082e11640084e280c020304200310101d90800c09a0141001603c0540c0066075142c481000c140240b040502400204168003110030407814100c48212078003401620500d400c11080101d0704000980c1902c2406006205849030f9416034814000c01102d80b002c0c14550a107020001010303070010003903108190489400303882c0d446a141c410381d10540c001c1025080b8004100521052403d10b0107401c0d48240c921b400b180e55885076071141c5200c407403c94100e0240c0e004500480402d60188400201c41c0241c204050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5003622 1250 5002372 5002379
    0x30a0305010e0601020a12031503020a0303020a03090f0b0a08150a03120201060504020c06180a0501050a020310120c14060c0106030c0602010c080f0c0306040f140105011b0209040602090604050d032106 88
    0x47c040d4001c040c003d400d15a0319450002d0101c128000400107540003019034500a590b801d01035200d10031450300702d0008454060100d080d520200c2c0800503a450010914141400b0341d03020f1b50044070240c03001c1c1c04e103144040e00c04400d070f84514040000e94840c10040d41c406000c4003020303080d201c85400c2640b003a0b0040c024000b08003000989141e00229040001c446a68514803107800c0440440c40079005500709001c001801000d900107501900b044440000701543c1e89548040b02c1070b00000040255118a1040268040b05144200c0303500004080c18a8255080449400c491151b0b01c11510642920810030040780c080c49500c10852840c100f030030f02c620301429981107120b001860f50149840c040b01054035601d1703139030040445850883d000c02c0803288810161014040901c921030000f90310034a01c1c985110f0038a24800c0c02e66000d0951000c03178031642d60f508040d400030020160403130020701000440daa1364a1084000d01e00036111001a921882d040d101200d801c503c02107406c03030503c0c6040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5004872 1250 5003622 5003633
    0x30f05011208030609070309021005030609070509010c15060f0807181103071101110412151b03020c1204030803010f08010204030b060105070501060302040e0708061501050403021201060503030a0305010e0601020a 93
    0x1c07030f400002107540035520b51b11410183e00600282d8000b9401c05190441d00581540100086001e0b1504451210750b0713981d51881110280304490419000451042900c1c0c002602d448503944400717403041c4040350160311303041c50703544402c25603024140d031350b11074441040070240164080411002c0540b0a201f2483c400030b404003288001f1304030204201e006444080002400c0d030001042c401c023481c14591303d0f07540e032580b0040a6081c0c1810b540c1404131958118180d180791003a42c3c4410207407820140710000c0050290029000302e0003e062a0003410b4117a00070010140043c0003452146512a40725414500c13400031a403040c0c0c00031105a0301c100b00910101d03600d510060b40c80303002440c0040d5501018906140500065817009402c281462100c0524013008140710040d15503800031102181e99440d00301c12400b0800c041180840c0c02000705002600f403112010100700200d4001007459039540c400700f480e5134000c40440d00003c0e07903000103106c0e054030b0041807500039400748000c1c1034610403074440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5006122 1250 5004872 5004877
    0x604090201090302120102040b0d0504060506040e0606010c030504120309080d180308090d020904200d11190305060f070e010e01090e13020306010b09090601140a050d0f0507030f05011208 82
    0x45d1040c10542038909070050250110340261910b01401034442129400b00009420142c40881c6c140e800c1c135000413020708241c0714010b83c0802c03080080c801174035100300545131218880800d40403c03000708800b0034206d46080303600108500c641e03940902540f4020400c0d0905442c03442c404200f100100071019850044152102565081490a0355410103d00007d00082d00030b07500941000c2c007003007044240302104c0344410344410404c04c0c020590596404100303075203607150344c01001c4103900c009427015820000905131100d64100b503c41d0906440ba155189440380440f074100c041c0c95100308101900350b02100800444000f0f0800388446a580f400203030809200307008581c1d013100ca010000c1d02a210b600950002c0c40e40207001c1c0d94040d61200000750f400d40c450442540200b91201c00702c2c51551107008254600311030054143e0600448000450703159001500000105803205580b9280420700e1240d40d0051043d500c00042c15540b4061700d1090710760503800f080d00150b894540c40041a02d0208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5007372 1250 5006122 5006129
    0x705030604080304030f030902030f0a050115080303010b0a0c02060d06060f0302030906150307150e041d03030406020904090c0611010501060302041203050702030102040f0b03010905010803041a0a0c021002010c08060409020109 99
    0x1c2045560502140480042c2307011070000c0d5051113140d444010030f000124008140d180524024040f010212a41c00705141c6181301d505100d034420001001411940b030003514100405240104820f00c00c0d0b00002c0f2103401990044007000d076941410048540c1001071810012442d040035819403628200540d2500f03c014080213001d40302152000556405100036006400d04060300c98201d100342000400c1d05a00085507409180341141e6508a2811542c12100482044d8015403030360780c2e540c0e506070203500309c0d50405400c07540359041c10000803007010300070028200968070744400b0300340d003680b442c207540069014409062040006000ba160030000140c1c148c0c1e01070803c00d84d602428404a4020302c141d40c0121407842200e40c2c082800d00d43d5400031412074003d50700601203642c881100304c1d201c0c07103a4410203c030844c03219020103506d043c0d85c0c068071080b80103044c40325440d4080e03008207040e8100390003440700603559100720028254101d4000364110304281c07030410102c2c02681c0040c101550324003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5008622 1250 5007372 5007377
    0x501080c1911030409020406020f011802061305270601090e060d031202040801020304020a08031206010c080903070b0d0e01050c0a031d0703050705040509030702090402060c070302180702070503060408030403 91
    0x704000651402035411104000001d01140ea0b605e50310003190000350098001c240041c010140e981d90010014003030010b01440300241a001034482d94200640e5510920311642000d103040c00c0043c00f90f4a5003841c480c902c06103070103190041007281409480d440001e00c036a0522408240602c5000600310340640c0c40402a00c030050702000b1428141c8880c2e01d1000000c4100b07000181c0481d0500042d0060b5000e6882a951040c2154841110036102d0080840303000b441c0e0039007400524590302c01c00b07500800c0b9024980f582d28046c03070707500030905107561900014044e2a002820301d00c2e0350107520a18119681d8080200107905000014140c280b141407107100c2010b886081700701d594000680f45180e00741c81101100c034110390b45e151040d1541c80c14890f0714032891030a800107043c4c41000c011201e03881c0e03000344007141e240c2e00c9501304545074000321941d10180c4250304002c40180c941003210394a2804220081500b8500854028501046504154002e80001c23051000280014064907081036050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5009872 1250 5008622 5008657
    0x603050c0909090a0b0c040303050f09040e01020705010501030c0506040b030a0902030f1b0907050f03061221090a0605040501050703030f090f1b090e0304090b040221010905010501080c 81
    0x400044120702440648a5000001074103210100c10002000c0300c03da0310880407100c0c0343c0e58980400010780241e100140c0418000c110200060482400074241c40000610008854403503e00560880e0440c2c40c2c2102d95070f5568005105008400107040010134040361114901821b15824541c1c42c00043d200060231504d90b0504c504568060103841c620401d20803c4807180880d400411582c102560140f901039401c83c1b000c02c00003031290045800e16020820264950b459a1050100d03480c2517000d00c0800c9d024944a50020384491000940030701c017040c20b843d0315400500f007002140000c0d580803605100c4100402c01c01c0b070342c0040a0342c050b59014140066452050a40d080c080c0111400007002c9000c0d0104050400c80f141c1220030004c558010408100f5854824400c21204403c1e1004a261320501040017522419000559400e001a1025042c20aa48c1c040c520300c042c1c40200c0c1225002200060001a459118071401071400346440401401c0030344650a0502c10006550300140301c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5011122 1250 5009872 5009881
    0x13020702040b120604060c030c0c0209130503191202030603060c0d060504020f0c0c040b01090b0a02010e06010906050111030304020604120201020a0f08180316060e030f010c020a0201080105010513060305 89
    0x490307000114034840035190b0f0704460301456600c0d80b180801c58080b5000d500e0041558419480791280301c42100b00c50329400600200c0c1d408001c21490001e204103090424040d040c000140140080c010110740403541544c1d100301c01d0340151201c0305041184d8107080c030500410685641c000380031900918140c0c005640c1d0580503400300042c10546e045a074103d4000130300c10000a400c14024600290382405507a1b21180750820002030b01c0100446600040c8100420b0041c0209034004210308200c60000044d00c0c0f4180c1692070420340260310060440d5640c07801006256081016401d07407a08000c0a07510354900f690000b1264003640c02008cd0420400c1e414400b10b90080004a11017a0006000b0300d45458501d048011907001c2440101d504400304607808503820f00048900640d1007259683c0a641d0034048100c400b200e620303c0e0541c4c14400d40c10b191062200a1103000180c04442c0e01400160443e400050102032040c0c0c071007410840304001c1c1c035900300f00014481043e28100d207008180e640300c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5012372 1250 5011122 5011129
    0x603020c030f0c0a02130504021f05040306060806180304060206040f020112020d0b0a0501020706050d05060f220b0901050f090903040b1c061a030a05040201050403060e01050612070513020702 84
    0x5000e030b03038062201e400242a0340f400f0b80060500541031080300ca0301150395110208900340c0d0002c1c2c0d0002d40041070214500c2003c0020341d003800c98600c0074901182880d84e203444030310a0f1890b5031700803400c5420603410b004981b84e00d4010040142c0c0c0310001035143c1890203e00035a1003030010809030520101410030011684103100103040080c505806540b14007910341044002c151541c05544990101c2d103001402e0350000c51600c0031295192600390910401c580071030060f000081c840ea5202c261240303582030903516441100d00318031010003006c1d10200704001182c2103d103400b04031442001c0581c0100180d64920048415030341c0151400c18407a225500400e01d07600641c0c0003004404404154481c1c2c2c44081c8184401d001c02c60401400046d030f4400304007001c1c0c01d584a0014003034500304001036a503034207508810380262042c076025180650b6615070f001185c500001c40c001c1a5118001e0214a1030110341000141206da000b51400380c3c500350004080b040c150031821101900414103005555 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5013622 1250 5012372 5012377
    0x7091208090109180f0c180b030c16030f0201050a0504080406050d060504061401020709060317070c030605070905010215070504090e120c0106051c02030307031202070c0305010501060908160603020c03 88
    0x81c813211000f14600c900c4d4900014212000544108919080501410302d20a01c0000d180c45012600061030505219403c43c1580c4000c10304400c90004000380303019182690071003140d50f800381e681daa004d0180404003d0035a04054405c0100740c0c00c040522002c90314078801c640031600281001c1d43c0c1d654a51020402406c055800a68000d24284000494951000c0040d00f1201c00368260399440e0340382c4409004841060002420368082486541c0c14130030703a1030040080c103000d0156520003550341d079201c405641007200c0f100700251914104204650301002450410b0f260340c40e4401a6180c0b504000304140140d02c130303280f041510740d1004402c0348002e012811441380350b65565035651160001d0319010703140902c0303010f01407840d0b00f03100854505910080e800250307009020314903080698800f11000260f0600401c0c0c50f5a08015001c00030b80e6101000006507c19800414290300d0200d02401d08090f690049809802106131b5103640300c4600b404030242c0e149030900607110403140740001d1550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5014872 1250 5013622 5013629
    0x306040203090f1501050a08060c040b09030307052a010804031713080304060204030b0108031c050c0906130302030106170303040f0804050a0806060915011707030b060a0504050907091208090109 85
    0x107000300c0e0000074080600803044d41c16241d06070342164a442c6c1d40c01e07895035105411124000444000e20040c00010025001006140401070490703080440303d848441c2000380c0c0d4810100342c40d034800f0501d507800314121341a607107403003007401d19440e00d240546010707200e4250b69211401c0d6080c000b0000d03488141e80d25081c14180c0c0c0001807240c80b850b291a207030000354040d003c10b46484440c0e100024100400000302d490050f920804c0e07104000e0000010000340502030b0541e0101d40003400003007083d4554101802500742e11120b043c244502c1c2d030040c10b00712445074000ca10030b03417030501c1140700d05d18000045076007243c3c2c05144002c01b070310b45040460084c05181c0045601401000340011811400540c8602078481200c1844031078690010301c40030000c2070354940d1f0100d0300c1c00f0707800340c1525411004941d10070a58200803400c24548800500b466112400d20804104045800d004500303011030310a92111041c10880300c0300b400c0c100465404085143c00919800c000035210080341d01c030b140c100c1c006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5016122 1250 5014872 5014903
    0x100809071208070b010e0103050d050309100203070c170901050711030102040302030115060f020309090c13030203010f02070b010f0503061902090301020a030501080c0103060b0d02070309050303070c031b0308030604020309 97
    0x761010351910040e15031040c981551640200000810320032202c03401141220b51000c001d000b000300600c0d0a80c1c1c585c10040070302d00d0300c1c02208400091400580000d600c02c040c1a0340d215100c0f6294a800d0100304400311310408003410a00c10303d005030740c2040840d04802d802c6001364076994850790000e8064803603500025055400c0242400c520f65052201d002514025264075440d032084030403c0340d13203008503181640d1000281000c01c40c0c42008400600b541000059250451501e80d00440c0c2518175031142a1106a030004580040c000085c408601414040b41c0f50385155280400180c0e032083d01a00c5688500b40b000c200e40d14500490713045402c1d0400240003991100c2103044041d0060509100c1e104840c0200d14610301950b103e4403c940c25119610141c6040603904c0300100003e40240e41c1c100d003440720007880410103990410207008500e10421807040c03124110302d050b01d4410b09014005107017144c070810500010710f001064030f0303100d80103441c016100d50710329213000c0c03402d142c10901d09030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5017372 1250 5016122 5016149
    0xa020c030913090b150d06052d070e010207050a03030305090a0b01030c030b130201090e060607080d020307090506040305060a020313020904060b0f010c02030a110d0b0702010501060201061410080907 87
    0x1800c2c8410f8001029490003054000e400355100c410442e040e80101d05955489115008041c00180040d48800e401240d0011180010803807644201c06c2d032001d03003854405100c861400c104211340d10070641444c02e00c081c03000d080da003854440820320f11555070100078207140e164000500b0514042058001c126044010f01c0d800b03507902d00704540307055000d000503214050380b400002c200724405400c0c60036144d0b042c0e541c02c002501e0b1500031050080003400c00c650015007040107401050708440a04003410200c8801a038074100004041c0c5458650352010780220b80900003000865008606d240c3d00045038280541e680d520f04d4a04503566841440080d4000991002c0c44103025150703100c8580e150090301c0026903403440c0f000664042102960003589070b1b10100f420b00000d006001c080b0ba503488082e0019202d1941039442c10b5000104880d1080143c1d901c0b0010040c03a542402103100901c8001e015110108094010466241c0040c0740b0009002c90040031510006e4100481c03070046c2a0305450f40f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5018622 1250 5017372 5017399
    0x30f0417040605040602010c08040209040b0c0f13090501060804030207060e19060201020a08060402040513110c03070302060f0c070c05041a04150f090605060415020a0507030c17010b0105030a020c0309 88
    0xf41560400e0107072000542c07a111248680e1030282100c107009a40041c0060302c0c1c0d5550355942e001010008020985414091001d01043c45000000c0d118110b00141940c01c1d10382001421000c030b80b4140e00c00340c104030100303090001082d0086a1141610b049240c020f900306459400f040101d0880b03d2aa900c0e031691100014a16130b040d07001e0050f41c40c2556035142c49455682c01c200c168003c0d4010180c0c802c0200101e0300c01030160b07520610303200e40392600040c10040c00005907170954020f1082078003d44c04c138104101200c01c044800580c0000039900c9a4281045900c6410540b4614000d45000f295070788861080080c0400c4040c80d00c0b90001c01c1440441084400240903209611070794111007090000860700c1250b50007994240c410140a050805240c41d4014000718100b42c240402d500070350910310040b600c14040b100c0510302070361324400707844d2826002d103c2c002c41003000075610b03915014a040540e03905c101100c0c0c00002515000d80c4a60001c8070741819845001d00e2254005108001407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5019872 1250 5018622 5018627
    0x3090c0a0b0418090302030a1803061505090708040309030308061305040510150806040b060a09020a02010c11030306030c12120c01050403090608070509090a0204080109030206040507120206030f04170406 89
    0x51042e14141c03801100040840f4400400360703041907500030b0141c0c00510000342090b02c0341d1850352440100c0800303645c1007640e0341c0703c42003203510034280f0b2a203450390b0300414051410700741101c60300b005032450f0144492401e5140180b100c026800018100304003100400c000340d86440002500c0050407504200908141c50719540d035555240a0591890509030110408460201800102c0e5503440c0948503540c0c65984100700c0890042c05160720182460b0b021909200714409802c0080058000040300200341001030a40c407408a5030341103a500810811505460120301115809015038080290503c44130184e410040b000c1d13034188000d40302280700440c0d5581500005d00640c042c0c4c48449440e40c4a2004540c1010300b21440e2000c55008c00442c11141824012664440500c0c0360040c10181c071800c030b99081d5065070500303400580c800414002071003818031810009001008080001c0f00c103e5020071014000101610303080c84030100003070700b4461549801304940180110a90782e4540b9004007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5021122 1250 5019872 5019877
    0x7050f0c010f1b1103030f04031103060a052203020123150603040b010e04030c080a020309090108030313060203040c03060c080f0106080106080606090a05090705040503010e01050106050702010503090c0a0b 90
    0x21035002449000c41a41514090701403003100750803180b800701840d10035486003c41440008003490301803008100100d0f4000700000504082c5114181101034030005c070301010303e4003c01520308110180351406120703c8106c180d29040c4d00740f884000a403465109803c09a00501e44104100926100510115000d510300d4440510078512611001c1e50a16501e0502030f1034003013241c00074031007030341d6000500000044032031151303215210b0302d8150f07000c07581036994600a03040249001d02607400070504903102d00c0c0200c4101d0143c9058070003541580b42a002c0b01b008035001007405003101c1c0e8000045401e0100c0f8854000c06190042003e004401201360f0041c0042000c90303418140c0000280086221803180c0b89150485080d560ba546854455030304016091b4480e4498a903c10a00c1d10001900e440b200c4004d84520916110151610318007814103080d6415400074001c1f9900d0700005101090300710007035607801602841c2c04c1e030712070341e40c0c41c6e003503141c00000d14840e030340141503034000207503003021100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5022372 1250 5021122 5021143
    0x15060e101d040201082206110405012309060d06050a08031b030c06010510050d0501060201150e04050a0308040c0b070605040303060501020c10141303060209010e0a0b07060203040201030207050f 85
    0x80070390714208001110703030070701094030300a00185020000c10f104400010307a06500070b080c03e1a031072a010311551400c085031202c40351401c5012010a0412140d03030000206400b01070079885024003581210041c0880740703c1c5164091050002003034040c9603021940c080000703004080d003030540507074a4000c541d9480c0c00000b141c60003034000c210840c420510120540e030790b259041000300010f909000400c081d00000d1188202045401e101c401440003541c040d0381d000f031000385c000268001c0300803000404840300b0380102c9e80c0b40340340400303000028500240410b01c1a03007501d80040709490320314051000701215071000e6482031011941070700348035040c1c0c840e601807031080c0c0381000015950320044e61600c0507840c1d02d5900003400b07141000038500a181d100c00b0b01b2a504101c3d8030780f00d200c4a0001408003583c05c183c0c3d4150340411a00c005580003408070701c0c0c0700703411128800c15174503141e0094105d01c10f0300f0004140030f0700480440c0440e402a0180c450803903200d800c1c1c2c1c00008118040c41e40c0d031601c005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5023622 1250 5022372 5022389
    0x609010b0a0b040303050d020702040524010f02100b0103020f0301030c0f0f05030604030305060103060519030b0a0e0d0e03011808030a06140315040507030203030a0203120c130315060e10 82
    0x400354005241c44610001101c10070014103051624545080d6416080381008070119a000c110034030040c0d1341c5114645c0f140035410403c40080c443c2488500404804049041c144086800e044600b03a0b00010444411645910041401008000101d02030300519100c49400c80011001004111240c0c00e150142d13922105d12046265580104902c0c5481c1c6108175901070304500c01007030210b80b090b04032a90050042c10085440c9a03100d011440b80c070540c482031075424003528018410890301c031025541021100205016041d46141c141c0d441d50141c44042041c00424009541582c070207411004030b8a80c032580c14502407d05007001c0302546e20807100320030302c1e070303d05500484c1ca800e1b2804800940035000c0c6c02014842c64940b40c030488240301910079a8548542c01c0c0000040e581080108074081d075a6010390746400c41d55107034001020000d0304100c1c1d900c6040c45901ca4076912440400e0441c3c4c0c2046420b92030b84a01d075102801000250403a03441c81f01030300100320f40d0701e0900030b14004991040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5024872 1250 5023622 5023631
    0x1b020606010302040f060c020117070c03080606030405120307090803040e04030221090d020f03060903070209090706020a03030507030f0509010b0102070806010b040302060318010f0605091f09110403050708060901 93
    0x440110101e1149004480300b5105c403820034045144a840b40108440c41810107038004080f2111020340340204962480014208821420405503c42c0949030400400d9410030304500702a134555484090b000803c440c5010013000242019100d13080440c001d0014109030390341e954446d09600c0701c840c000c0f038040c2e025218500d0400c040f02c0b0109d07040d4064441e094106405c0c10b4004040086c0b005002c0010399211044a0101c41c0c0e83e40e0501000340030741001c100442c1d0f80e500d41d00c140010644014025201c540015904004d032031740208100301805d50601d400211542c800c8010380040c90b5400f0000d070b0440c5803904110700000154413030240078800340c0840307141981e13840b20513980c1c82c424000c44d091441d00348010001401c0030310140d5000043c00035202005103a0101441c02c40c0c1010750944903003500e42c3c00070045402d00c4007005411000004110107440381000f52404054031504c40d503001c580d600c1041ca0040301120701510003079503200060302c450a0351101055940d00301651906042d5280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5026122 1250 5024872 5024881
    0x20a020606010e0d050c060a03020c010204090204030303060b070c0501050f0d05100905010801020a0c02060a0e1503040204060b04060f0e030708120c01060b0a09090504020607080304050a030e0102010b061e040302041b0206 97
    0x30202c400002503110300101b070fa051800b014030215400c030075020f405058080c4034001d80030b1020b0001d0000f40080c102c0041e12546142030050a450265000706a0f1080402100001c280c110f20780340150f81003824142e50b90503c41c454409d1910038008181202481c1805000300f0340c104103684005c0700c0e04914180926601d404220b03080388a0040c1d0342c000300301a11090001401c8c9500a010015180d04208409020140118151080c000000480541c0000421046140030b2042c10040c2c9034800b00c03a800c0a090076009001c4c0c0b0fa840c103140040c408130300740e60b4100703503001c121407070103030031078500740d5412450394802031009400c402e9082d5115400e0079408101c50140c5425101001c0c440e44c0c40030006441c0034803080007408041c00507a0082020414200466258002940104d1213100200b001800c41d06000381440d0b030882145046905100d405003a640c2c41c00f0581d103009515070000444224500000c04c550700c00c550000b500941464900300c2074010b002d0f04413001865603000c1d112107546 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5027372 1250 5026122 5026129
    0x20c1e0d09050f03030c0609060910060501050304020105030a06051201020705060a0c0e010f020f01020703050702090604060308030c0d06080a08041d04020904120302090301090605060a1e0e04050a06020a020606010e 94
    0x24a005100c00185114108000034039041c0020740c0041030150940f4640790f0a18a05400d20320f0448003085554840f4080c0802c00104000401c9804800241000000d041100003131140c440680081d04008002c40800e100b2440c2c0d900136001458000d210580c0e514400701040d010350003002083e180c0740103020000c0c0b4403c480c2d0241c4083d8004581e946038069824000542c0d4504600d0160030451103150f440402d2007900344014540c0c5400303600c9054807980c0a01c1040703110035008007480d002c3ca0070508100006071004096940000c1202d110903104e04861200100802c000d91040b5014411416004140000700c4000d100799045540b50305d40000b01e158070f03070400800a407030094220410740c00050124240148d01c1c100101d01e454058a07201f40c1c0c40009007920f08080302611415510414054189001c161b090b0040500824255180191864802c1050034034400c100c0f4840c490300001c1d0401205110180d4440c3d4440030854640020040080d6078210440b1814003141410a20680a14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5028622 1250 5027372 5027383
    0x40504080403060c050403050712060606030b090c0901020a0206030114091608190b06030a06150309030504030209060303040b070b090607080405100e1204030302010b040f0605060a0e13020c1e 84
    0x350000d0016103401e156aa80100411502c1c3d140c1d401c009041c400880020b00500440c802000d0800402142e459541048804c440380c0c1d80c810300500d842c042d000c0004c1e0b12404c034a50b03440b040c07624085464103410340043c0d003001c9584500940c888800000800c0c00242c04202c0080d40c4c9083d80c015503135542d01091180040c50350082c0c080443c1e81d03440080c00d8542c00e02c4211007151140040460030400789000b003080c0e0380081d00c56000c00d5031100024403401d4004408003451059a1405100d00100e5440161541c8181d000c080d0144a05600083c11518108101ea00410b8241030f13483c1c1c0c91245042086c1c0882c015a450342c02c07401030201164020f807007040b000e0300503078214001d001c3d00001c41107100c1c0200407103100045203004105001240306020005800114007a40010944540c2401004100ea803403255100c40c4510b00780d4140000d0300d8010a0700d81000090810140d92030007079001580c1400080c08070301c1c103507000060140d41c150700071482c204101c80e600601058001c010b81020b81340c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5029872 1250 5028622 5028631
    0x121103090d230304020418060b010f090f031506050603010b0403050d050403020114030403021005090c01020708060103030f05030709030c0906030b0711030901051803060703150605030705030a0f0209030f1b0405 92
    0x248800c030564030b40c1080300001141c1251000b44001890f01c2d00e0107480d000780b501c09500b621210381d0707050030080a58018040800e10206840d0100307c0608154410510501a010141803481d00e00c0c4810041d05c0142c2c40780014140c002c160ba6142c1d03079690449912030303200e4081182c41f401a0041d024800d0300813400c6c0c406036a416101e80241e45130b800d103154030540004005400318880c0d09516100c00c1c01921401d0b0254801c01c015080000c4114006464a140c903030140c25590301640040000c2039100e401c901030207031185003140d9a61030f4a0030880d500500d60300040c01c0a08066400225404a83d10000031244100c0c3d158046a4881c0e4003600c40c01803800010003503420030088140c49600c62002018242c0384e40088200440c5a40c0220b03103070002c100c510101181d502c940d00381c0c0003407400064100a0250345410381c81c5141c0301714010014040a007100a1094456549002010880d0140d610041002c0d0403603a5125040c40c0280d9100002801d890003440c03c6203581c11542001d00906208 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5031122 1250 5029872 5029907
    0x20906030a0f0f0903030f060f0803300705030a05070c020d0204050907090e0105072705010305060a030614060906010903020607080306060408030c0f060a020301060c0f03121103090d 80
    0x856881c015848080c10b418208007400c0e603690043c03e005002035106a24501c0d000e42c0d00000c5641d020b4221400b1102d0a400c24850049900c408001c0c1040c000304807024039007030786030301580c0c1103405c05401500071000c9184600c22400004103c8071541c00030286100c1c0301103800034495500d94030070603141c241030010042d401c17119428520000d0306054010b16000a5000121004559100c12000448078110f10103556a5190018030480c660711000800103e001040c0b040c41e42d001e405078424440b802481844d06260315240001d00c0e90781e074040d4907002581c00003020301c9805620a80c554a00404640c824840e50200c80454415440f40c044c540a9a9000d000c4078130789020307074440b14081d800c024200c80c3d101c03001704404951040240054102d0b000030300010400f0381c0c0e104d2140c40c2050002080c0f490340610610041051540c00b20300c0e14040b540081d40103602001909003240c1207034410820744046810030414184103094100150320031890744090380d84e400c07139001040702c1150010602104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5032372 1250 5031122 5031127
    0x80c0901031521020f0906130902010e060307030207020301060b030c040e0604020412030c05010501050405060a0605030a090507120b090703050319020c0904080406030e06040c15030e0111090310020906 88
    0x5654000e078420000c8000b07540400b8002950360040d00340900b5052811a220300b005440182181020701c4200741c0403004583c111003d00e0417001103041419040030076034195860390701c0c80b410369000e031405030444100540740f1644da24241d500034020798070840d41280030790320746500021050b5046003624043c4e130007030340f00134542450071048111140e0098000e65200781e0800001904445a4142e03480d450310175100e514140960382803460858105900a50246090800300401640c030051043c055850300e080040e220340701d01040c40700030079030343d00020b10714803d091011500443d400404040d2a11036506a40320742d542d514015240c50301844020705503442402400607420b00311403900b00010705441101d020160702d500086954100356810ba401d2040000c0c140040d41e41406101c0d06c01c1c40c1c980040c2414141540c0c1c440705400644515500b002d60740b40c41d154428480d40003842209070207802032000c440d80006d0011b05500901607144a88241442c4440310603445c001e658401d8002003d150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5033622 1250 5032372 5032387
    0x1030803060f031603060e0d02070302060a050304051005010902090420041401050c0d03060609050102030c0d050d02090a0b19020a1a1803030a0b01030612050a021207050303030708090d080c 83
    0x160035035401e500b07941c0c540a441d0300c3c180640e130007540441c0103602543c07000c00c1000400c00001d0402c24280c0c1d8200440d00041400e1025032180800c841d0460f1051a180d40d40b5561400d1942c10007900103400d6488504200000940502c990003800e10648115410481905400a441082d84507a0b14200c040c0005110400c0800039150b80c900040c1c4040c1050b83c40d00d003500c004c55040038a4212220042a5105002d2124a5101c0d184074090482030000754034051003809556501c0c02511480c00801c031000840d8542901c00d85c05072071101901601e104180e945a81e8039200c1504500c2001c001c0e811002c401200d813600c00038800803006d40080c203140c500c0b20b8041d44d12841c003400801c00e5203645031075941c0390a00038040000750b21460744d85c400041d030310f000d00000400380c400c0c2d80c5c040c6514910185001010520204801d0a00b90341210b903224280d003000e0107141098801d51020340d01d40004420004560f23003258856106e04d0f1440c0039500003021000050318440019154540c00c070300c00b0300401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5034872 1250 5033622 5033629
    0x40501080604050a020f03070507030201050f06010804260a020606090a060312080c070c06080403020d08091207020a09051009110406081f0906060c030207080c030a02010f090905010902030415050103080306 90
    0x644c000d6045403001d46000660101d5001d141c3c000c0c2c440310009280015080185507080c8036640d08464249240c08490600c80002007003000050406860780751102e40c00ba0a021a840009a618070000412074507501109806910b6180494065005000b2140040c5403010b06103d0300c1c09490b40300c054074407000e40340e510403a144d0390020604071075460204a4080807a4a111542c0e004100d00c1c5c3d42c40c2040d2925140090500302031420001c148900481800150034001c03c1d14200d034034141002507201d40d801c3c000141b21a003147d00c054034aa00d00424040300300c8540000b4400e0f1250704000340180401050f245210744264868640042d1041c4081403001d0744802d55038642d80c000641c9035110640310800842102d859a1200e004a80450717200c808040d01400440020070402028200500352940481c1e2610040c060082c1001250203600e030b1410f00609080000e45401d6904004941e120301e8024002d50041d00c065030300154005003003200910a003d00c2d41a244e00484241c11500c43c003090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5035978 1106 5034872 5034881
    0x40b0301140d0803130503120405010b150f04050603130b0702011b02010b03070b0705070305030a03090c0509060a05011103070512090103150f030f0c0503010203090f0105010b040501080604 83
    0x20900451043d4054a41c0031400e00b080505c100010300c2c00c9070035072040304040301c0c0d4214a0000d01044c000c0544c05417030715990584126001c400f1041c24000c19000341080003842603810442840182001800f860300030110800804024140740e07a0444100000c940c0080140c0d07643e1002507030b034045500b0280e100c01450000704002c02d03002c0046505c600c0342c1e0103444810040081d03041d04000041010710b0040d41c000050700d490350031008005002e020501002d1b00e0f031150943c4003048603e00309203600c0c0a10002040440b107507182100541d0410810320038103403540000e010349000305500780825160048044280c5030703540c45030400903080f035108141c1c102c00d2880034001484201840f1a026068940140c62a40310003500d02e4600400c01054020b140c1550010040c850710711030010300900f8041042009100c16a21a40324149500451103800d0000d402080801c8007402c0c50b620 = true := by decide +kernel

theorem cover : BRFrame.Cov 4856122 5035978 := by
  have h0 := BRFrame.cov_init 4856122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4856122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 4856122 ≤ n) (h2 : n < 5035978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
