-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:54.228649+00:00
-- url     : https://prove2.me/submissions/6b1e372f-2487-4f6d-889e-08e35246f7b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758633093 ≤ n < 758812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758634343 1250 758633093 758633167
    0xd0906122c0f01021305090a05100909080d0513120306060219020301020903070618050603160804031403010605040906151e0509040f050405120c0601050d0215120703050c 75
    0x341480c0d055050b92406620110300c00b210040311903140741c2140c005445c0003100f44c0315003100301c1c00d6510440e10b0903110303c1c1c1d040301040071034000e074402541d107401441a90b0400f000d124004040c0d58095600d035007000c03440110035051200448020007014090b040410907036207004030194a41021300364044102c0f403104144415502c0a404031500e141c0024243e4030b05075141c0c0d0000d000c1801c451750251221485040100303940c01c1c08011207008040d40c4202c0800d00c0b05a000032030391650000c00032010080c08908501d503020382000510701a28082c0c54450b20365051140c00d0044514075800703030304440d52050f0042c0c1d0b21604000d410741500220070090a1001c0c145209607651f00c2284c0440da0040d2a0a812101611543d84910301580c41034040c0d45074040c9281c03110f10180501c045542c034682007203004212a01d001000d004c142032014007254141d19040c011b601090b04135483e1001c1410f000d8040101150749403040945c044900303900c041c105809090701c1d01c031045040000c008103940c0f02c0456 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758635593 1250 758634343 758634431
    0x5060a030216212a080f2a0a0f0b0402040908040b0c01050a05070806210a0503040f120c0b030a091a06010818030a08100306020c0a03030c0503161d030d090612 70
    0xb00d5400f03441c00140c81c1e441120922494190610b90504a9103440c0603001f10a003200208440041079044103500c621345141e921800324895004d030040740e00c955652240070000b40c10300f000d00001c014000a098950414044032400c2d22401000d001e041c51519040040b915040519035410030020f607000310703103220804200c0160070200d000c1c5183c2440707080d02c85c10800c203001000b00266120700701046052540c1e46c5650407001410302c3c00914400c0c1d2840180111500f20018580c0444044800b040c910016121418041d11003101103900c42d02c0d240030400b995030170032505508405130790030203071010502031803094803805008032800070440c0c01030218000c030143e40034a901850704420210768031840d0610042c2c1d9502c0c600002c40200f820110408c60345400f07042601c1c4519009001d5040c074080226013118520018101816560070361321803419a42c600300b0203040c0404580e06d401907481e040180203402e2980900b02c0b02c013030f00d05001d9000003820380800800302095101c010341c00803400701c0f200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758636843 1250 758635593 758635597
    0xb030103200d05061317120105060703031509051e1909020d14071d060a03111810090e03070f06050c07060e0102090a14030705060a030216212a08 64
    0x1c05000303032060030309014103001d802c5130030700f03c0d0fa03c10200346d2444140d0140260390380c0a6103c00060a10318040100320f9802c0100c020042d052203807a00050041540d8107003440b02405030400c030701380c41d030391010060361850300c2030031083c5507820030600315080c580301284080c032407100c1c0010f54a040d1642c8015045440300220b4a59903580a0b4807110003148071080a5581c1c43d0034807812104c0400c0021050704070030f1101910b4042c5030064030507444281152645505011504620fa42010f102c0740000c089040694106010700004410241d400d8a0201488143d6520b00c0b6500c0e00c40d0030800011000490100300c03405240d9002101082941d6180040c030f10a014800c806046541002801019100e06500400c14594102e901080705c6444841d40f130343d080340418025404d640a50800d01c43c80c81c040d0082c15503e50145400352801040040740004d191170450120740e0703407092004102c5c01d0104010004503104461030000e911718036403007031804404550704a40c04291250241101444203100c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758638093 1250 758636843 758636869
    0x60608060d140304090615080609100e1b18120102041d13080706090309060e060703081008031b121306030b01050f031303120516031d011104030c0b03010320 69
    0x240404c20556a07035920000e00c0e008501860014000b2340002d04285054070715180104070803001200058100710442071a900b0141001805039080640e40340c41d80314801c0100410034400340d101d0202c80c148130032f20002c01064015404640d006100501010000c06402040d54000300c409800940f10400100c813082156100581130850004840042c81740c907407c0288032a01c2a41c588401c180d45840441d95440030304845031344584204403c1002c00d100301e4041ea00300e0304040030748414550310714072585107078402c1e81e8010902480c0c0e00c1c00340481c0020b0103e250f8034038200380c0840c40c22229036036809130800c10380248828982e03100d140d04e0307603a4030038020b450304403908460076562414071800c40c0d8110200110102c00140c5207111072841101c1e02d0080d5030140c10190001c900c030041c028810b80c041c01598090100e982412096a10181400d0140c440b152030048560360380c8504505200d16506590780003401392480800c0108002001148000f6004003558110f138144403580000414044840c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758639343 1250 758638093 758638109
    0x807020c1932040207080f180a0603150f030f03050c010b130b040c14041a0906040b1b0a08040b070305070210020304090c0908060609100b0d060504060608060d140304 73
    0x24008038409440000c104a400b0b428070310a000c0004a54100700507845800380c001c0c400c800500a8180405850300a0030720446600041e85807440e000010401080040e4022000691a4102c00548a24540c10040038003803e000c1800003500755140c81d0051801d804004007041400922000404130a5102403405400182025040c0c8510a22000134180c4042828491450001d120a0041c06007102c140c1000075a51101d08041c5800e40030001003160801c1d83c04803450401c20205580d940a0003072002e01288010309850b1a05c0c40740d00304881103a2500703030382d865018201207808138240074182c2d01200e01190032250f4a050910b01128580900e4000940201c41e019850392110380120140007038a5a5913020000510740c5142107038030705103600c1076003155001140032800354103000b11299408441c1500d481d14103660f40251001c5a409001001e412990b10a0300384101e19090241d078008128600d03004000d4180300300001e92201d030070030740185800512140900544014420f4400070079039a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 758640593 1250 758639343 758639369
    0x515121923070206130b13020d051501120c0b031005060a09181503021e0a03030221040303210b1008040b0627070512071701060807020c19 61
    0x5030998050320310790341c1c14001c09046035000150304140b0000301075125401109503048480d00544400c1080e84001d04408802441481c40304e003d81c9444e9401a40b01d40300301c0080000c1d0008200e00c203880541030300407034031440441c90300c0b80210390f619601906071307001034504580c0d0f40c948849551034844d07607901494105070007144802200c2d42140b90340e0102e803164828012845034062010f401c89502684200c5804142181400941001e140b00c0b040c1d00c0d1881e62180310060600009628a403003a403080700141c1c0001240d550050f1207071104d880000408440600f01410350342d01600402c8000f04414403280940108041040d83c0d030088201190050a480d181070440b110060024130100c0d000d88000c003488e000729400f411312001c90300c010000c54156a80341c80002042d103404a10207015002040001c2c0156580b54204045490007004035880342e4801e64001c0e4121880107405900c010700f409011401c0008580e0042003c011140c0b04a4590b0f0b05403000c282c2e00740900e522604411180424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 758641843 1250 758640593 758640611
    0x4081801021e150106051c020c01060b03010f15030b130504020312180405010b04080c01050a050f1b010e0105060901140a17010501030213050c0d0207050118061505151219 75
    0x10108a0b40c1001c41c06040140031030b038890b40155607c1c4520566550100d0a40d59500540e50465002d0700360780c019440003182483d40c51003140070030340082e000404042100c20f02000540313140c80121540050300d007414003039598100c1c00074032488451001103103110b40b036000180456030103104035000007030b1414406844503807a5086100150072030036954003070741c0b8040001c51100c60301400ea0782141c070713040d0003406103040e031500440340c80d0803030181c000a001d4180700c0a43c201e0306201c00707061070f10f039040400c0e4081c5c5600c13911242550060300722004240d141c0800d204085c2c88005000d415945000e1101420342c0c0d00c03001044e5040481d501c9200180800030340d8200c00b00c13040d08114100d82c02103a0640070000c14811580845800b81e541d450510740800c401188119280c003d050002e010b5400001c1108400d050800c46034500a0304071a400d40c4c0d1440c0781c0a940121841c0d074003034802a1050041a8892006a0380f28400e854040101a81c5c82c00000d03044480c0a2401041c1e0044d10310521003008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 758643093 1250 758641843 758641903
    0x60a0c0516081b1e0a092d1a09070509090f0912031e280504020a140d0b04210206040611090f1207090908040305060606030408180102 59
    0x5241c1c06503040c9070003000c000043c41c40350203c6418a020700103096012001942162401c0d442a90300301c2038002558010008106070345103d0847c5a029602d64400d10910420f030891100304011541c9007220300e49035040c0c02d2002009a609100707042552008402c1e10780070003c1e15103000f45400c0e194410700329010005480c055985240c090500c1c0002c803802c0540b125482142804200c481888541d0b6204c4c86203071004401a0041e00480700c00100c403c241c149076660400080e41074084001141c0b2a01400300310300b80442c01c140203250302442902160300340d0b03001a100c146001c00c06484081e030880400c080c44211048072503017080609600041103c0340101035118001201c0c103403415450048850b01d01820401140c04c0610001e1421071050001c604120348244030011441c2248103803080840ca40d010380c0320380720340b0b0390051407450744039032661909503d001c0009140300d000711018010b00000422690641d14024680303401120b80401100040f0700c1c144051318507804a0640b0054007501c41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 758644343 1250 758643093 758643133
    0x10309062004050f03030f0a300e06010b190804020f1009031a060901030201050c341e05010804050c040c1101050a0c0509010c05151f091109060a0c05 66
    0xf9810740305103a0a951100c10951030f030050140c0a8401e420070404419210b220f002d8001920103800a01145030040c00f842805510303481c0900d511155840c00c1101c85010204100d0b4010814121414900203118042800e00241d96202034140300b03802c00840c2c2103550b80000d01b41c0c8160003074008800c0c0c11786600003c2c1022010b100a545030045c01d04010b021030004440180f20b540e015220328500d92859004540a9120103e01c01150080300c0100034a081610903012a0301001600408030305007490151100341c01e40d51010030b030011021b000c00000503041da01c41c1e003240d4003400c0c1f00c2c040c0d80d0b9a0400500784007212a41581c05480c2013446170400e44c2003c00c1c18041c2407050001c100955900501310121401e8000d041c010800030721140e09150300c1050340020a0784102c1c141e03800c01d130001403401094842a128140c0c81544042c107444201c1d00c03605c4031801055902e10600c0100d00c0301312081c15a10545003110700481002464801c201e008405110b00290f004086070303400b210602c0c03000101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 758645593 1250 758644343 758644349
    0x101101020706110909071103070b072606010905060c1222080a140118060510080f0309010f08010b0702010e1503130203010e01060501120b040e070608100b1602010309062004 76
    0x38083c0000440c4505e0f106136403100d51f2920307010003180380c001641ca0b420401303c4004d0000301003220500c0f04c4400f00d8445c0000c4c440c41d0f98203402c0a5000d040441c00034001c20708981000c1d0003a8400c3c80322521881d40096105980814a1407941d520b010354090000740d490304c51201c204504404134005805100001d101080c24050069601e0310980e5401c558266440301c81514255940807010714085001580710580020084a500c002d06940380c41d11070030040824403081b02c54001048110003540c2004841809940b10303e800542981003080a4400c0d004200d0040d0422414000411a0703850b0861507201310440c030350389143c5900e08100c4d102290140000202e006e5402c040c9485c08600d0140646803e0310b40503151495185d640c1a070110041140f00e0255074419250f0110741c0c08000c05000d2130003d8042560b8200381c62900c5100c00280a40b40e50010500f807404008005c0c118043d4416054619824030f404030302d0151500701600a0a40005500b0f040c41450410400c0300b10807000402c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 758646843 1250 758645593 758645599
    0x1b030a0c0e1b2d13030303050115020a0215070201030204030b0c0910180e040c09020304031214060f06030702010608012c030310031e0f121106061011010207061109 72
    0x14100780001c070460b18003070814026000e006200e641c0c01268001e15490101c03924000d1441d0900070030750122410b00345039620a8000c01d550304014085405814500f82030031700f09000410801c2100d0340450354580d1a07062010025001251820440e072203a01158015a0400d83c4840c050416805004140c0e0084007070320b105214a003d0003407a207010708800040d01c4440ca210b00006442d0045a00c15228020710813100e1a07950140450100e0131840034501590003941c0c0c6034444c50360070741c200080b40e100c03690040740c1c14050003c10407a5600c0d170511080d48030055645584a80390307488181c5c003501403a00603008039406c24908404100d022040a001c06081c49200211041303c6d254158076840261004036800c0346001041c008100032041c0d100154004c03410130004403d40c0d80ba24040c0c1c0c0c0310144100d40b415107441c0000d05540d031000c0e100c0c0d94000f0342405090386041203030008071007060911582c2d06104002e2000413690780207505a8003000e421a100744007109580b454125598000002c1500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 758648093 1250 758646843 758646871
    0x120304240905060613140c0304020111060402030705131814070e011a0715230a1a010e190e1807080309011b060f0f1b021b030a0c0e 58
    0x203034284080c01403100c0180c0000c050030341900d460060107503009000403803000c072030b03100ca001d0a0f442e1010740c0c07094840c1da240c1404980328149440018051086100d922140b50b00410034000544c0d0301149410440e24200c5120406c045900d448001810480805d0790b00070103d040a50140304210f0380516000c4000d2061341c0e13810307403120100032114000b80208001c1841440010101c4051b550081070024000d000010360b40d602584480180e420b6a1184419a60b1040a00350280e0362014825008495860306105d84d0b40519000b0f030300e0310510603900e810400040c0c40307985651190000e170180b01581c16041000140c642001d01a0141c044d0740720741e60010030081d41c00d007040012900741c003900d1061010707600e010100c1e001110a17010b03a40e20f804003100480000c100081d0984103070b16500e042c20b0070101d099151460348100b21001f08520021018544000e21400e5902242018840c00c03c040919008103544000c240f811035501002015018490b0000c1582d40001246900c80c01c3c130301c01c5182c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 758649343 1250 758648093 758648153
    0x9051302012c0d0c15111506090a0f020408032b0c02070306090602040b1b010c0e010509040e010207020301050906090f0a080406200304060315171e120304 68
    0x2500030050901540401c0100b000501075501d000f125503030440b405103e0441c501910f540c0490010900304c06002c012600b96142085181020f1200202c2d81e90480107078409403506801189000318000c0194007000c1d03441550310201c05140e410344028040307030422a5100c0c10490801000030000321010915603004041034014091107000b684441d035410341c0a42103151440d6a044040d04007000b080b00e441b5001d0001082252901e4080c020000b0385640641c842540451034a013110504500c402c20011038403000036060b6041000c98000304002d03074001408400107a1000d00900030f40c40c0096040d42071000340b1001c90340000c1c1032801101003501b0341d565800210201c9559280d8654014543d402c24801001035602503a9035003c4e080d01c4040f0305c0782c00010b803d115801e6a005e42c0006001c00c1e039403500741080710501c0c64900c024215034051f20b038403c21408032007a6168112640e40c40703415017494291090010a000050604042c107400546908151030038140341012005940820316000c1d90b15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 758650593 1250 758649343 758649377
    0x6271a12060d02010504170a061404060e12190309052b09060804030c0218010303120f2c190b1b03040332180102060c1216090905130201 60
    0x20b8503690b68141c66851405142400040001c8080580000140640e0a80d000451214007685400c1c110907a81083d040ca06031901c10308550082500c60a01c1c0c0c401d45d0142807074031182e07003250710303120504044101c8910b503540c045014280242c0014014003030140ca03440641c40c0031a03501420850107284507603038103030b9210072120500303984074840c0018000390102c1c1c08a8001e01c941524140050030b18030f01c1211070000340c04040c400382e02c00c400046199a08450711b0381c440c8035000a41d43d940714184100b281e514003070807001c601141c1080180312001c01406200270700700840c910314613040c0801d4195070060300300220f51120480e00f1050264052051160654410080ba40300347da26448068802941c1c0030078042590032030320050b42c11200c0b01314000d109400040500208546004284072405401d000281061030250003000c402c4030070700081c0703034280350303680340a50201c40720480c403410701100b01c4200c500a815600002d23145180c007080c80040d840c01f000e0040c0260007030301c82c0024010000380d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 758651843 1250 758650593 758650609
    0x6020f190512010605180909060a050a150512030405090c070c0e0105011b02010302091507022137060e0114101a070206120103050f030406271a1206 65
    0x580030816510b0401446014001c001500541400262088082c21060042020a04282c0e5011040d80c07050b002c1009924007030051035030201040006100e404c80c440241c200c03c204034000c00c1d2041d80e000c0e9680241ba40308106441c01460024500f45c45410052145042688101b9058070ac103207007141c0c0450709800e041a0b4074101c0714103944449405001c222403801ca0504000101d04050702004050b10580d00d26a5840d9003010380c034030203aa1020305104200c041c490117045a141002d2055038007080413008146001100084464080da60f107101400c0e03001c070751060110030fa168010700c69070410b0240c55806400d0381d480d00c1000b04900c1c2c03810700345410810402c65010a40c404210b2080c032410208500203540d80b000b06440340d0170301005500281d4507801c0401410024000c0b1001002800700c208402c0b007658103148080c51809060804c01054a89007401c1c541e4502c03485075100340ca00004082a100900c610404803214a01988000c00f450b0303c040c2c04510301c10707036801c0801c0179882c0801c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 758653093 1250 758651843 758651857
    0x1906051b0d02090f03120c1509031b0c06040e0415060b09010c0507030204141e0412030911130218032406060408030a05070b070809070302091306020f1905 68
    0x21106041400207180100a9844101c03080d80013084000c808849440402481c120a10034917a0390344c5072071900c010603203442e01480d6200450100c29041c0800081d0100480741d07850742c0e0441180e0343c104a0f0590030710700310f101c0e220103801078000140000e41004044455000790b1040b00130322000301d04000d80c00140c8420340600b8003040010018550158001c2c041c01419074815801e883c2c0c0d450352500002c0c11900c40c050102c00401d0100200002ca5401c0307140001100c4050b480507120341802d8a801c0c4182050780324120616644410304810700c15040300103d40e040008007414403483c140d801c014081c0d00918028042041d10850350201c0d4074010841c111040c0c4c2c011400001604001b1f4a1094004090041034100b0700802c00030940c9030052000304044441521025901c180501d0300c00e460502c0203107000100300da0324040c0038079881c01103041421030350126960071030380d116400398480ca1228080000c11081c8006601010603441c2c801900500d490745c094001c440c40ba08605a45500c5012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 758654343 1250 758653093 758653141
    0x901170906010e15041515050406080109020715020a0903050606030d080a020f1314010206060a03020d02010807050904150e0c0a050409020c1f1401080d0f20190605 72
    0x120052145092102c100c83d4881c1c03100c880600704001340800b00e803c03100319a4003040c4030340c01e801d07013400700078001020348410b20981c0c17903d249007914254006201c08818040c1500043e00010484240f003107404c0701890301240080d04550b2000c030444090010307081031004a034a80607800c0090110729010403e4a00440c07282c961002c1c564544150800a600c6903a03a0b48080600340b0a5040c00307c24107520350068620002d2041d10b1700e150500192501c5030052482d446160000c60900c01030700d803418030201280d828201214241c6030410240d0b041e0141501c0c00340c003d890070301040d6800e9000407400045600360b030384051203030312100c0c41c40d003840c8541340042007c40c02c200400c208004540c0d008155401e0600182d50307400c540b00400040514100f00b007120001d440340040558104000941e6005101d41c5009007205500301c0c20203401c0c03c4019002c10240080f105041c000405114813100c0c4200c80c80381600c04200050320f91403041f80c19041d041d10068940300000b014001c00301d1403803c00b03003d04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 758655593 1250 758654343 758654353
    0x712110a14010e0d0c0521070602031506160b01120503091203070c030b0f180715050f0a080106021614130f1127090408131a09011709 59
    0x10348410441d441d40101c41885503590f0300040901c03100900404607807108907a20461640f032581842841c0000e480c08100c0d501c00d080c00080d10281d48030040310405580080301503240e6645043c00c0e02e8080420f00180d8000e2000591511101207200381170b01036611801e400ca00c10f9807200039041800201d81320050082c0e0007003001040f01c1c94140704440f2081c41103c1101e10b406a950340d5126400f88940c000c45161500c3c1081c80400000c0c4543c0d29030158494002d60001c00e00d83c0c1c261a500c0701c04e0301c42c3c0008900084000500341d403090045400c00d810302d0a840c1c0d9286458003008140f21000d2184034014060306411310051104030142404503900390340440110781e400020403641200e640310440e8001d03556441912422110300178800c1c1d102c0303a040b0090f114104000002c00e4225905000e00d0300042e803891490a5540c1d1029194000b9000b205480e100e0010585003000000190088001c0c590301c0d006d0401c0c06004040100000c00c070a0381e42c078500b10345182c80c0e110515005e480010140e000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 758656843 1250 758655593 758655613
    0x52203080403110a0317090f0609090109020a030f0908030403030b010c0b0c1612090509130308150f0d060c0e0402031320100216060e130e071505071211 67
    0x3d201c1043c2988000200070040956496445881c0180c0e901e03900140c144d8080742c01c0106140449903440c1d803880aa60a6281c0b0f844a000580c00010500900e60780316030203d100c01c0300070b02c03980c4800d242c180340c1e00007004041c14504080c0e00c01d810444c0c04074002400e16050301900c0d44a600d040c88503035480300c03001510391140119440c0340e4101542c252420f02061000034085030f0210035034141c03008030f07466201085003444188006c00340000c1120401480f40b1159100283d071003020079903c02c5003040d80c450070320041000240001804442180d0100b021004030007480b46a0740010340305050ba0700d1f00d400260f503070000d00c0140d0008490ae081c05d0f0706658400310218010315456816612807041034805011180c00027905200c3c1003894500582c00f56925a00340c41034120f400700034115030b052590140d034101c40091400d100f800303d1807442944441d048095110200f0041024204091249056028441c4c0090075074114480c1a64120309040b402c4101a003e540c2c443c40c00704000c0c1c050708200304c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 758658093 1250 758656843 758656853
    0x140a0b070b0402010c0c0311180c12090c030d020f010b010c0f06020702130f0207031115040323030c1c0c120908091e100e030d2607052203080403 64
    0x40c0200b003a070512a10800d540c0c00500121840000b45116090140d640702d440000d01201d480c070149032100320554501840a00c0074150190b03664140da01c1c1c980345a650b00c0c5c158060406080c1ea00d015014840c90354203103c0160082810380964420b00c0c02084000d61030b10046513001c80109001c1c01070f0b100c410305940418a03a800500d11980040c0c0b1000380b094582400074100d40c04000600076060340405c1c2c1c1401c1661020581814120f400d0082c450701e50510725051502c01c0c0944000c0610000c2c4d0100865a02506000d04001c105800c40d1901d9141448000c01e89078400720004a8282d80d207070646660400da44144000850141e03070318140e0b05c030704803001001041050700c02d4860b00418800320000b82d43d03218208403261082c0180c000c0075046a02809400d0302c0749006a820300504110b108030b0740c2c1300010342a4004600e450300d0150321646030a690b0000c4e0710810355084800200d8100a5050b41110040110000407007035042c15070000e40c04080420301c0ca02008100c400c0c100b0082012a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 758659343 1250 758658093 758658113
    0x11502070605030a0b210318011d0d02130204031a090d020d0807031503050a0b240402090a0503010912110d091403010b0a180b100f0f0e031006140a0b07 67
    0xc0c05000c0903070408810310b0310041c15040004100d610004905001c10098900110005000c0c20b009090221186040d079008a08405890140c400bc50003003055503120107480e0260341201004554440e1030f414404109c100c204108028900044003007050280000382c1c41c2a101d52960251061107003440003201c2d4018080d00d01010142c450340740801040c1d440400400441c0310320000e11550045152003905154000c1880d4401c09041011254060039214009451481102c006a60308810000641c08217a160800e5825600e4100042c0c2003108034140c00030040b0950300c4001400c0420ba600700d599240c109480b81c00174001d030508101584821a8060040c0c4005001284031002080440c1900d9aa603102480704500d400f101810504a440361a49203d03041c0c415104000800e00f0161008680710402e404011920410f40281c80c418080b12803140e0000b810744100c208482c100301c01038926805941c2c00c07004000100d181524000e00e9410803142d54696050512020303843c0d0341490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 758660593 1250 758659343 758659361
    0x42307080d0c0b0718080d1205090307080f03040c0e0411120304050a0b0f040305011e061a0306010c050a02060f22140909010e0331050a050f040204031406011502070605030a 76
    0x945c804c002c0c0440c401c201404441c02e030301c50b0380c3d69a002c08000b0012079800c0c0d60000d065503400e0307001081074802040d41807044690b1324603401034203a50394a540c03034a000390170700310343c0061403c42607a0140000c0004908054900505c1100d0f020300c003480e945180d5840b44103a12580ea44000b00000403c803c0740e4503801b5061030307002071030317001d08199994840c81d0170740b403400e40e140c00322400c00140103d80e5070442c41421701904030a0b96644a0300040000d030742c0d070740c0f002500316414002e1004a141c1004410481d000155030f01800c016111440c40140035440c0d0000c0162030507006820a01245004d800445042211a4185010007100100307051100e00e090140260205540340c40051000310f8040005021200b00f039002510b102901b0b2014000008510284a419805080c4200660350b96169280281c41c0210340035007000703a028000070300074030540d4402010f407c284030403814204408030380541240c00942010303401e1080f1403c103d84940070703801401d000c9070701400852008901c5071720141070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 758661843 1250 758660593 758660627
    0x12019090906060507050615030c04410a060f05040b0609041a0a0504021e070201020a0506010303200d140c011e0b0a06052712061003120c031403042307080d0c0b07 72
    0x10210b860700d40109100040016000b4598cc24180a100512044c10740d540543d00c0e120030040d203420410503050081c464407032a446aa20303588089240d40d114011034034855001801040305401681c020075150110700f48a510500d65400002200d0420b8021115164031074485c400307207081d21440c03c8034184c110308401e90451182550000000d9400c000c0f2502a60190300ca030316241c100540d00300031503421150002d40b141c0124a5500029402081600c05c008079202c5468a481c0c00c5240b01d801001203603103044400b100101c0c0306500f254603a020b030700070100c10385d845014030f503c42c001a5240c0c81104046000081a10369108858050b006445052100201481000c0940842070382c40e008042c1d80e503440c4220b00e10800c00400000c5d040c0110307070000505001c6603000701c0d901d0141c902e500c555007601c50382000000150401101112414a00020880c441e20080c0c28090707960b5100c8290042a00920405c0708440007070780102194100640e01040c60f500350790311840300710343c400d07421015401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 758663093 1250 758661843 758661881
    0x307080a090e01080307061104080a0b0a0219030b24070b060319031e08010503030412061506021b030309061b010912030c02012019090906060507050615030c04 70
    0x200148004225802044c2d810011500c410060402c0701c2242d029401c120421441000b0401802c2d1020904560382900f08180c18041e594908007007000c1d2095a41030003007140380444594015401d80c2c0170003000d140546811b10a1061407a001c01042d015000c44c080070641401000d0015a410352095030010019007918880107056482c080e000039945401c40200d403084400600d010851042c0c0306400d0201d2500460035490280400e440784030358040c0b084d64910141201007800005d400a00b041c0810407000c408041d5144402516a51210748041c218030f00143c8003101c0307140010a890031010000d00a5191100344001e40a0220b041e91282031039540301c00511002c180300304d01c0b01100141030f0700c000c04c081d10040340003400c4036502015401d007210342d1084044081c4c0341800f80d4880300140ca102c045460412070040e21001034a900082c200741c1410004150f940e4400060320544c0d01c15001c58020391100a00c00a001c0f202062640e016400380e940a0b0703051519803c14001090350001c090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 758664343 1250 758663093 758663099
    0x31d011109120703150618050f0606130e15090106020309010207170f10150e04050606060327010c0f0c02030c0418080c0a03020d020613030c0305160501150503010e0307080a09 77
    0x1d400c1180d00d8400b2060340356111010000391f0030901c024052108101010410762800524a107007680014207250301903100804e03081c094511800301200a41105101c0c041d1515000355048085072010f554a4025960708000140540c0000181d58007654140c0141141904044000c5e002c8004c0c2c0c04609510700c03071190080c0d0003140c02d1103082109901e4003008180c22507a40360b1864240003980c410400e610b00001044040b500203e051500164111840396407a1a81c0828000400350552945100c080c039204880031500c0c152b00400040c206a1a40f0700c00c1e030a500d406440000c4e080501035055040002006180d00c1d156001100141c41d2861700300d1801150f4a65400c550020a40d81e030700e42e0f21079407801c0203154040081d00111a01740c0300a02c03440c034040c03252117040302d40d10030003d0501498601c0b203002c1601910584810703c0010f0304040d440a11420f280f4041c001440c0800d603022020140440d10f400c3c18001c41442007124801145084001e59480180b544407160303400804c40b11903008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 758665593 1250 758664343 758664353
    0x90a020105032509060315060804230706110c10081b040906090f11130320100305040b0903030615030c0708190207120218061807031d011109120703 65
    0x90210b0105643e2290404d504080002e000c03610181a03d0a415540620800c04960301030307040c941c4185d2000c000c2030302c0c1000383d00150119045a80c141d5050040140c040745540c1d101a017030048001d4203081f1640001c1c043c0a07c122030405c2c1e03a44000140000d00016080e00c080b2310405140b4040314450344c0341903a10301d102c2c0c00320391258100b21308250700c4084e40381d00d40e00c00d03020304100a01e04441051600c145030818191070740303403440010034042c0d2003044442240010300030441f285001800c2e0004600000c01c00400030708007224202c548080b08000701c0d07001c2c0c0d0004160303032003070601900040840c1d0300003030071a03019080202202e0340002d00700b010000240190020304140888130828080d00143d111001e402c05000b40c00044d640342c1d0b100000d00245c0e43c0c035407801c40c03072804011141c180d984841010810902d200385d20000301305121010700c80d040e50f0652019520006180525040c0414082c081e4240e9031020100e0b000d03078006000100840ca018914800507543d40307004c036844d5075a00d07951 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 758666843 1250 758665593 758665651
    0x61515050c150115120e06040f0804050603010f090507110613020307120302010501080d020105091507020c0d05071401030b030601060315081501050901140117060a050d0b0106030b09090a02010503 86
    0x40165460301259803402d10350b42000c4883c0031782800311014002c0304d0300068450303561400140090044d644600b24a8103025802084401401000d08919501d40c0c4031780e80c012004449210741c001b4249007000150429114a41609010012401929a540b0340c403e0504442c107000006982c54020000b0001e402242070701e2009100b40b02c1c2d0000300d26980350110003420201840301c0c032019641800204240e512002c60b85842e222034101410300b00792900c400c200d141040300b00c0d882d0340000c41e002c0d020040c03140c000f541d001143d0115410261202c8000011010f440c090000707180c259001c500184100c030f0180d040b1748040340329404e40380e442c80d50350031900e4608034101d0076807001442c2c3e250042c02141031201005002d088071f8003580c039829000d036000800400c1200c85141280810034041a803d58031030700c0c148018400101035040c3c58059042500116070280702c1c0300c01203480c24103142d80f03e0400c0c580d0a8850801c0760041c0042120300d40064406910007040d03031042140c141d1803040c00d6002c00785c13 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 758668093 1250 758666843 758666849
    0xb0a18050a1a0c040302041e0e010b04060501090b030a0c0507020d1b0e2712040b03160903210302070b0a1505030115060c17040303020a061515050c1501 67
    0xc00002070380782059109080c0003501c9000c002c15010030480d0800c1000200c40440c0d5040e2000950030b2000b54001c075600141404c40c4220341d003000303980c82d05010150810068442c046034208489552003005403a513028520466180c00b00600000b8040781c1254401c2d820003006080103490880594002000104440004c603603403550001c5160000b06e02c900350501415865840b826241050a00c504203014038241c4640c0300c100707600d0f80e000c8699061003401c6c400d056040d8095291a00c843c207064054004a840e88003250b212102d040c9200c4c0726044400840741c021201244141c04007044158811102c680704003816004c004003c001a03d405806100e128211000144541202c4400592022903030115100c1c1c1e043c60910340c0000003240904003218010300b86000c0c0c0d108945030400e84003200c50250054010081800010315030042402d6000d28451281000042460102d121218040340180710080242c042245142c0740600020841c1c0c500e004100c4441c1880c3c01ca5000c0e1b001005d030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 758669343 1250 758668093 758668103
    0x1107091506141312050c04180f1406130308221514100815060f010c0f060207080307021204030308070f20010b03010c0215060d08040e09030405150c06040b0a18 70
    0x43e88107003d05c01c003400542080b42c4102c4080c4086104071030388480c8070030300d404046c007071901480c0484100301c0c85001d0b01c0382d020140000c5d03402c1440c2940d45051480307000300d0700f9070100e00e0308400940343d01845201440300c40d5030810304803034144440e02c3d03140707a091142c030b15180303001d45d00e810782d404031070305d12002510402c5070450710f0042509000101c0d040206030300058076110038100901410b603030f0324140740700403480070b1030408d4583e209400c00d090003281110303028002500c0021141c081c0201070004522655968003102c05480e9403805100040c815848040c0020b4502808580c4091042d03043c080d2000e1a8981b9040c0c942c44514100c0812905441da160203030341d1403a201d045800e0030b00440d4503030001ca0011f005911683d002caa050148014295481140b03213205003400c212000d0181c0c0d025000c80301031001140385c85019280c0c3da03400380c01a1446a4821104001c00090b040200c51a0f80e550a010740565152a070f2070010700d0070050075001005880e03031220302201c41260381d0692041c0c024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 758670593 1250 758669343 758669369
    0x703020f0c0105131118041113020c0109110603010612020d0902100c0309050111060f04060e0f0f070b07050309190503030a03020d0624080406150611070915061413 72
    0x90f1500040000e01540c00ea0300401807030070b03506c5440e1840100c40e68066007002c040c0c010322031003038005848095048500241e65202146031a25407070154032010050384608804002110303540f0400c515170109105007400190b40c0f001c642ca141ca50380e005805d03482039039171010030b40c2507035580010014429040c002c3c000601559000f814981d20200c100300824080c01c0242e50301205c10b4140791103030f10060030641c0400e00c0c01c0200301000202e0340046e40945d160707410742e041da445400c82251035200001509010340708000c0045814140d2004590300180c1c090002c61a240c803e1003440501000000110034881d504000010f5586040c40184180300050f60016a10801101050110344031500107107050721492038444154409410103040500d801e08040c42e243e80c451a1000150200360080004010005c20005580740c22007400e250220940c0180d5071201e454074480f40449541e04000c40e0780054507402004210701400e214000396102c03a2081b40392901c3c2e40142401c101c1d659016005510748 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758671843 1250 758670593 758670631
    0xf180f06060b0414040e16081b01180e07140d020405090a090203032b0207030e101d0f0a03140f07090606050906030606070213050712090b0703020f0c0105 68
    0x3442284003800000c42c1e035a05083c2841107042881061944060203980da41601e046411820001002c0744102c3d59507207141c442c0c031000740d1512080c050b940c5144400745010f0120303140d030244640c0340c041048140441c06240c50142692580070010780042c0034071050580040060070070b44020207503100103a40142e07070b6620703282c1440084003000b0032820900303141115a074016038002c0101d0724800c0d00300168030700106042002c4444142c00488090701140f0004007075003015041125460303a034008941c800c06d07200348a5010b55001044840560410801c1410701c4039a00e00440c1c3e502e40c20002401c41c0024546941e16241c9220040c00019001c0c0d01540d61600403450800003a40500120501444542e150450240c050700803101020b11508000c0001041625003100b600c02070b40d00103000d02c01c844c0e4190392040003000f0690300100041c5c40d20b4004a2980c0e054000c16440c07039844180400030f90b40750007080b0000d4110603004d03108c200042002c40810b10007400f6040c0104441d441c403043d035880d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 758673093 1250 758671843 758671853
    0xb03100b0f190306050c0c0d12050a0b030a060203070e1e0901080304060206010605073009080c0627151c0e03160c090f0b120609100f180f 61
    0x340c8003220302c6000700315101c60103001490300c881c00b200d6000780c1c0401c0580324000001c50381d01071810311490501c41c0d10345c4800c02951025092207401a03011041040340c9a40d41d4042c10786001030500c0390198801d050400018141d640250340c40501440c00007808000d010024071040c403030303c12144100200b8030b03002e207032460242d440034018028080118a410b183c4035003c2e40b940d4051040d1028040046030240c280101b26171301d0b08121781b081b0101e22103c02c50001031750103000c0c09140040000c5444c2000f044455001503444401000200303520b0516032584400520404032034054603400011107203494054440d40720fa0001c1d0070048180716240da5200d442e210a0082101e400c0c1000e509007032001c00101804011280c0c100703040b20129100801d10f0800f003c0002843c2d100c0c2990b2450040d00f140b4a1500b9070102d2031000c411204c01c0380c900e0924601594460080da08000780360404140d9103001c00f0cc40c0e0240344880001075012901c002c04c06542416250440c406903010408a641c582c1000b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 758674343 1250 758673093 758673109
    0x503010605040b130e0703060507022512062c060703050603030a0818011e0f0b03030307090e1012060507030f06180903140a03021c18060f0b03100b 65
    0x480c0a540400116598000013100100703010a0320182c184c0d5403d44240b00c407024045100916007092042c07201f8142054001e550307026904098050020600000d59101c00c080040d07000c80728185e8042407103402c1512501c005150302100c40509980f00c60441510100c9140183e500d10807c001905961504000280903524000c0c1528071941041000f003403481d812007207064118020940c424400030180c03140600600c200c0d25040714404070080d10705804092604802100000b90744140640d0f5103190600d50b0f80d01040d41d41501203400454180300000303011381c0c19070b80f00f204080c02010159440c0c0c1d00d0825081c130f1345020f41c0e54035142d00c1000b601c00e405000f00c902c40054400704201a070310348004070000c015018012140740d601e1386002014984107014440e0007a04a02c00e0b296111070b6440050002d501c403a0364201d050b0702516000d900d142c1c6074030030100000c03c6804101d100541781d0b50b800004102c130b102030740f0b0003d0341c80032030f900715440c1003084840c0d2900c203c400048085a00c01000a14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 758675593 1250 758674343 758674349
    0x309021507050307140c0901090b0f0301110306060906040e04050c090609310c0b03160f0f0e0402211b0a05070209040f0b04060c0e0d1a040201051b010605030106 71
    0x50401c0640002480002100c0401d500854403400b401d2a407200b043c24103842c00f80c144d512210103000424483d0255100f600490340071241c1d060060310b144145800c2c0e030407007101c2266690f0180f000500d113081000080c13010b204001c10a520b0b140d21011449058501a10300b541c2a41c481d941401c010305054440540089084510010600d00003061021030260311b0f42c1f01445503401d485004921208860140d1041e9100321143c82164503030b00e07140e900343c104542da04070007801c4c001b8090f15103000d08170300e01300c4141d86d5840c440381034100c00e810340741e000311048105d030801e60030071481ca6030340300f040414903104443d4002c40d204ca040031713035828030404004000854000f80c2000030b02203294001085170030071541a1002d00030340c0d6aa040554007405040c00140400346000200010070209a100f45800c03006511390108040c14282806848041e940005140302d00580144500d403041c25007090b0701c00e03c14500b41d85401001201640c2d0030418039103d40c0c40b03a441d501c0070f0106184c00c0c0144805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 758676843 1250 758675593 758675629
    0x609090717041202070b04051f051c090b0a0207020a140a03120807030e010213140f04020a170106020a02010e01230c0109050c09101701110f03040b2a0f130303030902 73
    0x341030034140027a42c0b40c00b08401c00b040c05000e9800e072001c100d0003003080d20b1640c000c14000240099034045a0b00c01343c111404211031030600000054060f002510a86400301d801070102c040c418241004200400c1c0280c50150f071040143d54000001aa613000c5101c81205d00d0783d4000c203604082101505803003032107910b40542d13401404611050000717941c80c0070498a180c40c01c041414502d202140d0150071030f0349072a4000d40002880d0020607009644620a0a83e4511b01d21103030f079a4810498071800c2d0288c1c003d000420f60b400104496201e08810b1a0111100d0506440e40940d01e102d0b2829a10a092805940c2d450300c41c0c2500b402028445101c2056040e81c043d286450000030700003d14031140a49a0142036200100480b980250321180305c10300881c01c0950395800f1110444825041140c048072080d8a43c00012840468100904100c40d2002143e0354043e5101601c02e42e039070400581d03521300c00b0090251101c20350030100204000c50081e00c000030b4070504c500510a210300b0b80104070702 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 758678093 1250 758676843 758676847
    0x1106060a0608060609010306150504061706060d1e09030f030c03140604020a020a05100906050901140705160c0e01060e09011424070b0f07020c0609090717041202070b 73
    0x16007007002c07980e00141c101d82c5999035841c00c1006034000c0c291038005600c011803900e1800c4080c0e40000041c020741d0602d8907038403251320001c89804400013089440a801190601802c2058509600202589070201101d4000d0304584407070001102c40103001070700002c0786e0a124801d0702d13406106001d40021103140901c0191400350038407042c0000039040c503001784d90018403a40d12510038040302001d198010161492840c105200402a001800d025030355035107030501041c0094030500c5514800615821400e80c5940e4075841503c00d81c0190304035420807151800c1203c005400b580c44500a0000d40c030001c00c20f541410001051009500740035801250b9070801440031840c41c41404940100c01c40701002120310ad20303021001411445800305401d040410010104820424100c0c071a1000214003462950f4507001207903900301551843ea0403030700c208944441828003130f41c1164843d40d2802c10703000503c18211030380403411048405480c07c03c848032aa823519541406550020a003980b1014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 758679343 1250 758678093 758678099
    0x80f011a100c02120304030b0108070302030d050a1b0203030409021b0c0a03030203040b030705040b160b060915060706060b031003120503010627080714010201060e09030a0f020a0506071106060a 85
    0x9402c1d8041d140c406441120440c020414100d4204111030283d076201155141da540c4d5403615542d03032900e81c0000c9200340511040310809070300c540700342c2e203c544d0701d90b07140c4040ca0002d0410300c89500607030206903094002040041444500d50005041c00c90780b03801e090002c2c448102116062001e640b42040c41a0420002040403a80c0003060324181da05072240f541d0749455400080e02c0303030b100e03a40c00964128008990348000d18190300f0103812a0740a540c4948541e5600301c20815000011550072300b07500c001a07241c12180c2089406041c0191140000140d0107840704440340e080d4100722040c0c0340b5940c81c01402d10800410204a415540503420460b080d541040c0e006003645c030000b01301c40d03082e0200304192100c800c2015003080081104078140c0c0d44440d1100c14048030848044015800b643c20090300050000d080003141d41b040012601950070400100d208944046c8003800c0d42045200d24407903080480c0e0280801d5020b40c0f9544c880a0720b4400d40c40d001402c3c003000408091040040703007010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 758680593 1250 758679343 758679347
    0x2a0909070302031e032b0c020106052101020f07060608070909020105090925050a020d09290d05010e0a0c050703020a03032f0a0306210f0606080f011a10 67
    0x75204c0c2c40302911010b0081242c2900d003502c2c6000c0d40c10504050300000200b210924007080a84070400c0100c40c0c01c1c003400e0300d590b0099090f50362034400c0a4010440311643c0340a80c0c01c10350b4030303e8401c442a00241c980508581d40030302c2c0c0d4019000c01d6030381907a07a2004000502c0c080007204c004110b202410301480505400180c0b880c028000c074507000d20055800100581c2d08140007048100c80c80400c45000152030000801c1030300002203400161080442c46d090b030501400c1c40c1400c8900305040300300540110040170000707001d078520710400c00d8003d22001c001d0207942d002d494044e01c0d09104150040c600f1a031200243c8400d460740c83c2c280b010400c01d10010984c0803072a4044030b13800d4203001c900b441044503045038800d0800e0711680180da58242c0b0410710300c06e4000900c0029203da5042c485641c42c0c1c0c001100c001440c200f5603214502107400c00300001c0400c00c0c0e038004180030b200005061551000e0b003a00b4141c20100d0114140d40d10003e18240d8040807000e0941450240c0d60590385801c1a440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 758681843 1250 758680593 758680603
    0xb0d0e0f031611040e010e072709030513030305071509020603131e050709060506030112061a040e030307080a020f0a050904091202070f0605030c030f06032a090907030203 75
    0x144000c540c10b1101c0d21080c0000c102d4420021507020b0410450701c02c0342e802040c02008220364a045c2c41c003d0301d0380040c0e8000c42c40021101c000c2c207418002c558080400042c0003c1081100440038444c06102e140190f40c5014642c2c00114080c0c1c40f0140d0f104898600750707441380001580c2c0701d6000c0c0b40450800150715104140c0340e025010b020804c5601c01349062540042e00b0300311408002d0103030540c41e203042020100d640e200700d034081d2006018091319230b030420080b400240102000090807034102404a9100d8112035010f82d0468426020600060042000d543c044d4040c481c075907000209100c134030b82d40301f0b41d840e13400040407208506110016010701e485100b5000c80c0b50422402154000c902d942d50f03485103544592001000c404010900800b03925031005100b28510860b034090009220f1b80550110b91259042c5504649155104441507581c00e501a02c1c007030301031080740300c1e03c0341103010205100c003020000001c00c918000d6040400844a40c0180402c0c100d80090108000507140010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 758683093 1250 758681843 758681857
    0xd0903110a0305071403010e0601060507080a110d0807110601030206040512070f0905010806010b12070818063303060105010c0222020717070b0708070507050303010b0d0e0f03 77
    0x301440c180341032400150381c0a005410103009405465000904040324004041582c1390039002030003a00a183c0d4101e844400902c5081c0c0030400400c00b1000180242c0002c00324206139091403105200d1989100d46003105603200303071010480e9a4144550f064000c81447d0080311504000c1c2020345c110b0b40030031041c0c0030350701c0b07003500031a009640103890450500000000d445409440b0951603603e801003070281c10b00f849203402078004c003000420000c0040c0101e13088041000080788032512124400c0f141c014008200820300c107640d0b4083c00c4002c805100050051500303d000c0c0d514612521a400170040e038100c15840380e020700d256122115100494000d044880900307001648107640d001080501401040c0c0d00ca00c0c080003044030500d00d00300c0d405040c0c86401170103030f00c0741005030850000d180e110304c034400351403802e0a80c00a039060b81710b5468560310005516115003882c0c000c0e0b6031a4070f540c0082c1c00009041901045035401e0300418495074560300030080040a5004911a01d95140d200e00d035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 758684343 1250 758683093 758683103
    0x150c050f0106060203032e061d040203090d0905011b0807020d050a03090303180e0a0b0d020604080709061406071527050d210203060f12150907050f010c020d020904051e0d0903 77
    0x1249c41e07440c0c080103000060380b80d43e0280c010740d0303a0300d4610030341601e45000364203000100d4407030f0380082102d510988014601d0310400a4803901040c250300e8a45450b008580103d030311402e4100300b02e000030001e000400015101e40c4a030b004140c207502d8040d20640d6014594140b2045441c81041031241e602d0b1003d42010308420006090301c5100e0105008513032130400690090030014001408080c0002c0308411074540810412103d0f4488150700c02d800801ca2000d1752290090040d4404102000540b85480851000009031150789902c90030200c006190420030a881c00107050f81070010920941c4450261032410055125148201e0150a9000780282c000581d0100028103507841d801040703440b18400400100302041418040c0b0740d510000c8910b490465811404500c650384000360007020303110000c1c006840030784509c00460300b03c01c0c0c0000c182d900c440840205000340c2c40741c6c60520700a41c06140a8100f805605490080900000c41000b10301c0c0d01021031880650b034081410300c00c0c2d980c08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 758685593 1250 758684343 758684357
    0xc0b28021f090803010e07020706030501050a0e07020c04061d0901020c21040803040b032a0a050a0507020a0e0708070509090705030613062d150c050f0106060203032e06 74
    0x14801c0740c0700405400380020101200000007050b59901100703c14890100740d07003100c9080b41c460000f102561700c2889580c1d0001744c0d0090601901c5941044c407940501244100c56001c42c0c800c001405451680e4440122195a5030107104da2507031040031903074824100e100941c6440c1700720503004d50307500380b45111407542810103100b18000e168801c110740081000d08200c1e5221901c41d20303681415481502c407558104500c0301c901103511025261610904000c04509007401d1405500b90340681c0040350368001c00c40108074074001603079600d42c0403000e01403d440c52a854901300780d000c1c0503204013624010a0100a014207401d80c1d0b5181231959000000749441c1c2e46035110000881d46128002000b1008141065030100d40341e0506a850310062615091803001c03ca5165910f41c10017000b07000700c8014400e01c1b001c0402070360140300d0420401d8820070440c1d0002201001c03044c01c43d029900311500680cc00400d011141501034208041c0d161007901c41404842c40b19910039800303480380b05103014003480e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 758686843 1250 758685593 758685643
    0x130b0711091314060f062713020a030c03061118011b05011a211207051504121d0303030a0e0304080a03020a12020106060c140a0c0b2802 60
    0x90004508200b503103d080350f001039603540c40c281c2d10303444221444541c0c6603410001420500e0159129801e011600c40728a17200c484519000740300320700040292801c80c90b10314040006880d4520b03042d00850059452034091410341c40d104056829006031900c92080070b204800c008081c80080d481d841070242400400352800840500d4003a000c81d5028006505e455154004c5c0301400581d48010001115000421803008004165102d504284c074180c6a100410001440a45000a02d84107000f042214031010007141044a000c000700c0d0104c80300c4060b01143c00030103800c5020726070148803102204600c841008046592400300a100a940e661224143c440e140c03401d0049401510825090310085016410003954500c041e00088449000c1c1d2072a10800c940f040c85a5030039a1000e58465840b2009a1a00c4104d0003903058000118020b907000a000520300b00d5410001300703114819140c5411640140c1c42c500c8848a068194078055601404074450380030485d081144183e102e00c60300d4280b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 758688093 1250 758686843 758686861
    0x14060a050a0323011205100e030702330406030507051804090311120c1203061c06231905041502160b010306050906090a080412031112130b071109 64
    0x80040200c4070001c0443c4004125112115140c51240b070046044035000c000b00c0b240501210303002c0c001d088442e0030501c400b500600d81507100c1e164154540850302c003d0304000c08050325404a600c42d40c2e208980000e000c005003a01801480e900c44664101141802d0000c101102c040c4003181c041e903c5682c0d0764024000f0103024a0a42c1980f0820350f0895282041c207041c00803d603031140e0407800440c86030410001c858803688088a03c164000f8040307440e003451690480581c104010000c0340d0103034a8401c449500300078407031080c3c030703100230034480601a0a00c030107400c4d02070307400105074000503040000f00408074030200601c02103a62070000050303403013110030340140c002051440000d16444050000005204164214900807148101035900319107500c0c0d0314641c1e4404051000f4100b03070061008101d000c0b40320800c100f00c180030341401840c0c41c1c0700d10400c504080d00450703110300203038010581c541004070f000300b81c0d0090001010150b24001151312401c0303005000c2103010b0301c00e084c0f840004444403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 758689343 1250 758688093 758688131
    0x17071b15200f0106050a0e1005100219260c060601260c0a09150c0b060a05120a17131206180f020f0d030804020904030908030d0614060a050a03 63
    0x90391000b40d4409410b80d00b8054041e044900c0340a00c0b80c0c5440c5008607410040c205040d003ea00a130348a01c1d0100e00d40402e120205070b1025074241507001c0d01c0301c4031443e49240b003604d0b03510501c2100d1186200b00b00140642e04180006108049040148445c40480500144050b0001e4003401c08c0c0318003502622110312100107594880d0102000b410502141c1000310000c1d104038001d940b500c0c5551903c4005034900d0b030401811000000d0624000e80300032031090202e0f1070300b143c005030840c00d41c503880c2c1d40415922521240c00c450240d000750700a209110203044403c0418004400c818a4070b141c0b100311101281c12800303200518000c0c00c130310004004955021452103d580400080c04500604102040d0484c050080c1c0c040d0720044c1d851103c91801c01c0c00c01c103501742c0c0b41d22006440e45540d002d00560075001041181401040440460201810005002c440e40c08000c0459181d0a0156684604007400da910340158024020488032079002000d95008020781d02c0c0008001c00902c6400d1224 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 758690593 1250 758689343 758689397
    0xa2c0c0d05070e1501080c0901051b0a060e030a0e090603100c230a05070b04050a0b0c0d0e0604020901030219050604030320070509060f01090317071b15 67
    0x40c11400d030000c10030003107188800c90341210003912565aa1000f541c0c03a01c026820340a0000c0c980c980003c0354424000b0182c02d400300306142c05400e00002c10103010300f889104c4d020800f00c0e03101031004c0301044003078052507503440c20000c040d41c00c1c4101400040d110044a00b241482070300500006900b1392001c00400c05140b090b450180410790445d213018000c00d030480b103100b49d44454100d040030395003410001c80703000034100e83e40c1514151640d214241c0065000e03204a6043c0510004940400c4800c09402e00409e010100c2030b40e108840c4500760202e031103040b00b040041d0005010000942d440c2034103c0d0441c3d030192803c1008183e030004880c04d0303020300d0f044a90b0010b0041400310a040e484120161404004803c0340403c2c00c407034007819656602ca11038a07a001c6411400244941800030000030082011b040685990303449540e04105001042c00c1e811141d01c020032100d052186404080280c0350790084184161401e202a0242d42c1a88041600510803c20340c21030440710903201784000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 758691843 1250 758690593 758690599
    0x70c0515040b010e090a05064c0e0105060d09080c060903070b0f130305090d0f110a21120c1410051501050409050901060e150103050a2c0c 61
    0xc5460a03151030500004280100103d18031020300160030803000107114020950000018815541c2c2c44400704a0141d070340741c80200b4145598a2030282900101010b880210342d070018159a80d0400d5408075055120344c000d841d0121800010415504c0b08000c03284141c1d010800840c3c00140c505190a070b91040084002c0035114110400c41c50740000b0006d400811301c00c800501880d1104c0d0400300c601c100c02d40f200306100b0005804140024020002018600d2001c1c0102c103200c0e00380e40b9405401740408801351911040111400307450b01d00070710003001514502604500401c4882842e4030008808180103000d0540c201140d40168007900029583d41d034090754250211105608403a1903e00181604024a0602001c00d049a882d00174403200c50380c0681d5060700f00ba00c1d1102d2000a008013030484003581d5a6840c02081104003910600d03c6040010314941503101e51030001011160003d040c100410301c0c141420400f540115804400b21a81c1c1070203c07105440e010945003003036010f61007164 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 758693093 1250 758691843 758691883
    0x18050105040b0a051c05160309020306070c1b141f052b02030a0b0111070506091912080a0207080c0117040312050901090512040620070302310b09070c05 67
    0x1000c11504032510800e0a00c91f00c0c001da907050b150a409407030039010025410741042002541030392007900101c0045014680c030b051010f5200e0310034a031441490300400a000c25120200c880c0b4140344000103d0040545400741a407040c3d558000e000d8000c0444003c4007107141d4072120107010707044580240c07544084400b15034030300b05001e031007004107102e41000380400c2c3c4100c0d201341c1d20000850750344212103010307080504d01120079003000036508600035040440c902c0103401040c0c00c01e1800005500c144120702c0f440d40d508040001030b02c2d00d5403a42c4501010b902c010900714180e6408452880a01902d0701001d6060300c541c9001c2e600c008214064590300c80c41d1000f040508001504201c0203c2d018205aa0000d80c014800126920440c02075001003114123118900400564150340018103114055071000e9440781c0c00281d0315660a086241c0703071640044180500e10f40d564244241304404d00c410043c0803a080d0229441120080c800418080c500501740203000050000100c000041c669244c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 758694343 1250 758693093 758693137
    0x90c041802070204140411030f070603090201031b11150112030e01122d14040803130f080a03050702010203070212031e0a051e0c181c0308010618050105040b0a05 71
    0x4d001c41d00445087d601115804800306050401103810f6806c610180c014148417410071030f0503000380010300012810169a000c1016140600c00b011a0084005a6801d901c0300380382c8280d280b6184c840480d9100c041406001000b08a41000042101a0341401c1c25044030050780c1c0180c0b40e0f840d02c205c000e40d03142d00301480a80381080c0c486600c052642004d1005980d03d04010078201141c9070385243c03101c4040d00d1401304006c51348040255610840550525100c1c0802d9560204000403010040703501442c00700b1301c041040c0e05070103105d9105405100031070440c46c201e04025910346200300c50b038840101c00404200350444951440c01500c0c0d24244040c100c3c00c054a07070000400c2d0480310340c825441a8541070741030b405540b03000b40c010001e495000f130500c4941008000301552001c003a623405008040301b81da6a400a026414a1034040d8446050301d40c035195010f00b900502c410b0310904078803411010b000c1f50303802c0f10640f02941c800140045e1204406002034505101d070460300380b4194000c12000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 758695593 1250 758694343 758694371
    0xc1f110a020c010908191e080c011a0d1e080409020c0f0d05030c030f0603100c120605010e060a0311040f1502100501051e04110c011a090c041802070204 67
    0x79444003a80c0e03800c0c07403c1d078544100d511029220704400e80c41507050f6400c80800c5800e4046151f072280140c1d0490403034410780c0c80280b43d40c4070a080000d1651252043d42031a080440f0b00e000c030000650311181d4020030359032550301441a141c00403540303042c403868460901c40b00c6030035100078201e0300b02d04660f2403800300b1040e59502c0310320b4440e2001e4483d40800d40f070505d00c100152400780c0400d03801c0d42c0c1561070300d40d80c2448450f0002c20054161040800318103584420740181c0d0580900c80e15540e588000900c1c4510130354005030070113414030080020003011078132030b00d00f11000062981340019031055907211001140c840c562017400d00e98201840828038103804041d49444000716000c880f42d0140007407203c81950801d00c5600d40c840221841a42d081d101101807080c803003001400003d1105040240c20807170b8000c4102d040c500c0e0b568803d1100d007000c8044084285c240c1c00c880c122094a030505060309240b086001b800b0801120700960203101c0110b40503606110390041052150031105d41d05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 758696843 1250 758695593 758695603
    0xd0c1e0b190609020906030c0c03070b0112150b031f060302130e060a05010612090302010f1406031207020a05010e150712030b041505100c020d05010903030b0102030c1f110a02 77
    0x2101e11601d01e05100040d0301416032086419118000d05001d0070740d5907a2814a0b426000060f620b034190004000c0d2000107140e2042c813a01800c000301035a0403030701003401c2244500e0000c41048580f20b03d4642c4140a582d000501c0c0c43c484080d01d5030305102001007a40a00282196034402500030100c0800130600300d0040e00b002c420800150308541c002c1d56559003a00685d0302c20300c94817000c01e40100d410f4000185a4200e050410700a0002281151460100400b200d0004510244101d4a0410f00400f480c060018441074809000c841d801d12a00c1c0c1c000440c071030101d10400b0b06100042814040319124042c4501220421000c1c3d01d0b03c510307460501c0c145180301208007100091170201d00711002e182501c18001124850044070b4041c034200313002e000740100200c910f4000c1c403104003100d02c0103075608507a07a42d1080c0b0510020914014503c3c0180689550a810905540060100b03c403075100000c0c000001301e000320b004601610030b08103c2c400905402c1c04c01c107403200f4001201c0304c00c075400180e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 758698093 1250 758696843 758696881
    0x16360b03060610091a0c160303080702030a051204020301110d0b0301060b0316030b0f04060b0705060c0f0f16080a080405070e240315100311030d0c1e0b 67
    0x20664a0580da03010400403020a040301c0000800c41903141444000b0b80c519000c00c040800003801890214140b5040e440c1c1f42c0391181d91072000d11250701c03c0c41015400860f01d5000502c0b40025410141202e41c09000b40c0101a4491304200d4100e00003410766409401c0900158070038014659203a240c0c0c2401d0b0098010f0b480304c503000c0d41c2003000015020810700b0440b0b2044031503150f28210900000821005003580d8070803682d1100c0e404075001c120f070303850b48903980040c10026a056540c070300c1880c18a045c048001c2c42000c3d40c010038040005540e000004a0360301d02d0b9141c100aa40380714500200d0741d0700c0350141000c0c0601e0000f05114011a03040034845008078064012034a00965409c80c1c1c2c88881c40c01c50381e00b00240d0704a402c0f4648103c240c41803001c03408005081e039282c0011021074107001c640484402080d803060400400610080494200c48180c0a03000b40c20b01c1148200c01070800584440010204035000c4e80c00001245001201c510307140c0d0051a180c15420003490300041d00341440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 758699343 1250 758698093 758698099
    0x203070909150509060904030239120c090a150e0a0b030a02031e120307080f0709030f020913050f0607030e030712080c19030c09060216360b 62
    0x150b110300c01008100040c100e9100802c2c04000e41d650000f0700ca10460b0181c411405d42c400d80c0d0101d9a0016040c4100c40710811211540c444030115890035280b242c3c1e5005054000d000d80c2c01e000f100c00c100441d1003265084140d0303542615850380304d00d0b127005154400c3c20341c20b2108905000306100380d03c000e00a000ea111034100380031001d05041015196041204001d60541c044900300707400b40300201c0410b52290144060302d2000e0f50346071072800264011120800012118420024600001d0004036044001480c0c85c4041d582540e8408501000710080a84611210070005540e450000c9141102c50b50003429603a61140820006035280c40a40385000801c0c10023410045240002040d51003440c0c0001844021840c151400e40c1e070120044d1644000840c10440e43c0403100f14038001d0b03013071241e60781d500150702449039400500404e1950086811500005032000044c0070b10034500e41901c00c84401d0039040642e0404816622401300c40312101a8503900110300741400c680d00000781c1040035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 758700593 1250 758699343 758699351
    0x40c18030f02043c0902091f08070b041e0915050108130f0609020303090901063209090702031318200301061b0c08030304050f030c0a0f02060702040203070909 70
    0x2d105100301c0d1007000e4659241010710710b440142c4290003070030365000c104130540000320090304e42c0104001044c222614100484c0655420204403840d03180700c8010840d0728054903509041c80089501f51185224000d500007900c0d0020025190414003c401006d07040c00c200038240010503d4448080709116450201c0c806c4400a0300340c0041058524a03a903101c100e59800c00c8440c0c4e5841e00400c0130341e500ba0b800d0b100600c0440059142d19004030702078203940c1c8900c0c81030b01d03000c05401c0200d0445640028100c89208400701e060584505440310114115020303140d540d5441d508920314090f030120b204c901c40c02c44d5800180c0c035242d80d02c0040744c4048200103008109502a0600e00142840100348014008100400c01588100100822500c6201d0000041c858640724150361002d150410140d0390000414082080b40810044044d0310740c08016500304080707201d4080e1911100c49001d8064611001102c0c115941d0384104e4147c668000d1086403a814810340c000d0500301d0324000d20118a05d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 758701843 1250 758700593 758700611
    0x20f040c081e0112111f1d090106021f110c06100501020d0e0103090f060c03020a0210090804120809060403060501050415050306070507030216081e12072a0e0a0c11030405040c18030f0204 82
    0x4aa0588c5046e59913680043c211a0001a401d031200312983e1f4410f071300343c0e54a2848905140a040060007184403280c002d246600300381c07240c0c0500f000198003090640d401010246200340e0089401600b100f000d080004a8090a0a00e028009a006001819245008242e50a041d05540030308580089075085540301c03103111043d5021184031107400380000c1407d01c81080442c0f40a892802c1c4148548a0f590030208008041032a0740c009400441c1c200b5100c6005001034103203032080001c031051446019408620b4400031a841e000701401203810403400140707a500b40750003040000ea034620350f10881189195281d08654a40540901c10100030107003003485402100001881555864140310003890282c15a9407440b0701286965845000e0010503100404001800d00f618000c2c014110050014909580404110f40552403400140710043d20710030306844000007900c0944900761800100e0f5241d5035400e40e40400180a005500c0d138044201208100c080c0070317900d403031038400d0300e00348901c2e05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 758703093 1250 758701843 758701849
    0xc02090901150602162601090606090b040912030e16081c1706010e0f03030c0d200a120225090c080f070c020f040c081e0112111f1d 58
    0x40c81d13446000d01501451401d01c1900241a031801d040301010841b400d040c0c561128040c01e5500031802034600300e80d01c000410800c0082d00a803222010f045804128150456072424241d10300c2c05490820941d13100a076560b800d00c200119007880c03240c40403a814003607454002941c0c17584c1ca4804007058080e1102403024041c003440c0a081c52681e00d506a03c3da940d07801d00110350700034100b0301c515032000000c80314a4007034a00f03000800d0014090809000c0c2c00c0300012020300140c0c2044082c80140f4410440048038140208241c0c5647d07070300c0039460303070000d043c29800c9103003515800f022030656203050701d01064010710130381503c115500510240103030140204180d9482c81e00b26402200126003200007001c030380c031580c8801c01652004080b540f00115050100342201c4440404401003110942400100303140c0c180b2803c040e42c0b81411280503903041c0130701e00c01217040f4454003e005e6103a42b204503203d0741d9000c03025100101c00e4000141d91480494004101c102650541c03180180310000c848e2580c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 758704343 1250 758703093 758703103
    0x11090a0801090b0106031802090c090306060111100231080105070e1f11010c0309030908010506010507080c0a050a1a0a09170d200406020d08040b0402060a0c02090901150602 76
    0x5a04400703d4401d9a00c1c14105401829400103002c0d20066501c0c040d07801695418606402040d1a2410540f01d9031035006161070007101034505c0b414807203446200f200c000c2c0006071001142041180250304c80e003200050841103e0581d05401c402900260524002042020540119000c00009001c103490390901a55040148104e40382c004801000d40304401064907e1701d001800320f86403910a400041c4085400c45507000700590000f516002888285a0700c013602d0005000088002c00c0b403030a008002800a105054004203014800304130442036002c24003151402d190468280c44850816241140390180030340d004165070880130021071542002c910500d104640d00c468445a60381c81c21100c410b40c0d4000e56403002135503441d22414000001403440180c0c4072a503031440c0c079031030b075007481030180c248004003071310504001420081202040010b48550f401640681d1000d64490b20030307008480841d056003000c3d410003c024184082d8120540c480550442200701840030340351030760f2040781c0307030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 758705593 1250 758704343 758704361
    0x7080a1716030902180114010e01020715030902030304030b070c060e1617010b030106030c030b010e070203040605070c270c090e042d0b07020105010f03080a03050a0b0411090a0801 79
    0x3442a10040c2501c1c1030095102d19000c500040c510080082c00f800850841d0000b600642000b0520b922140519600614a904820024009415441c3c1014061100389108200300e00c20182c4807010901591000e0045a0186800c9641d608040c0f825800c0600310700c01c098011604d02c0d281030100d6800304004030b00055210900b0401818407072800c80c2c4000c0a40e0380441d10b40055696000419103550240b050300019882220200896855400c00c403480c0b1030140e1203003400886c0481003114190740402228141d80071404d040392070350828101110141d825402007007584074140135200710b1202c00d1164443c050303a07550003440001c402250858020803144514425400b0050105001034050b03450600c00071511441c0804000d1011440c41c00190144c0c0166901d24190b803e00c040540d082c05142c1c0908485101c14014a244d6582c01602d440b5068031101010b6560700400c0401c402500210400d1000030024030110340a42c0b9040070340e42c04403614a04c04c504510700000c3c1081c043c0111001c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 758706843 1250 758705593 758705611
    0x70219150507020f090a0f0c02011d03070209011518060206041101090b040506030a020f040618050108010509060603040323090f09010338070503010e13151a03010207080a17 76
    0x14040b00d4a091102c498009000e0001c1551107e800c0609140d9074404c83d4050f08242e40003040c00441e00301c601a00c0c0d030315240800b071241c00800404004d1781b1803850503811a21084204901c0e5a82c0e0581140c2070301081060300302e44d81428000203907031a0b0000380c007801070707025400780147d40100308019a00c011152044420340d54050200b00894500301020355481841c1400151a052600750340c4071850303010307802c19804200c010b4440084642503040e035601400342801e01e041c4d103504140c00240100c43c010203081c8a00d00000010b02010b119000001c000d202c0c184881441d46020344003241d00e42c1040261078007400c00711071400c03c07038905035000c00d0480b070704000d502d40b0048140c00380f01c41007098030817200b460f00040c50548003008040e40125102c0c42055407003548a5042c5880e5024562003d00762100140344001ca54011803607911000a103030541820000700102e0b0704801b0000721094040c15a81540301284040c00e104080c0014020129103545050103a440503502a641d10401d0b00c8050b6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 758708093 1250 758706843 758706859
    0x60804050609012f090316030b0c21090309040e1e12090d080403170421210921052b1214090f010b060c03090d0807021915050702 57
    0x1c820b508001c4000c0780550380418207107007000c1400403070b15080b1f1000c0000800c4211050030810321400312009900482c1c0552020703e0304540103000c9400200140211862102d03800c04945009800c0044500d00000900f09009004020311183d842d499072040c2500003100410040c0b00b18a408150320b881d0380d41d001d8446003000b0441003881700c0d5092061003151010000c010100202d500e4040500482d51401b0480756144d00300140c0340c02c1112030385090454070403182e115000261040361001c05400e4034076041c1e10f4031a04040e0885c1d840410340d11003941c07102c50300000e41c158a9034072a1140344a001b8000c07161741000600724209452445122032100c0204102050031261142c40000d003005110107001c5142a501440310300c14010a40d20102d03980d001540700c582405080c0180a40c122044582034144150f0483c3d09482c3e115040525102e606240c2100301042580011b4031081c540284c0020381c1c007030010510040d4031748a4011000a4140b0703d12038500103228a0498410b50b41c0904405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 758709343 1250 758708093 758708141
    0x60a0c0e040c0206010312020a1a150f13090c0b0a0c020901080c03060c0703090b0a0f020d0509010c02060d110f030a061e33020c0103060f30080406080405060901 71
    0x1943d41150108041103000d0224147c010a02c141404119540b0000c0ae07003005040c522076501c1c050b2104444140500806e0b40c946482d41e0710903851500c2000d0741100840d141c80145041ca548942d60380060004050101e00444070307030f50122600045a01c2134406021030303625010720994807a4844c45950381030f030040c0005403a900c114405401d4070752007401d1038201c8607110f80a81919400c40034003e80025141070400e00000d9041055030038a00d40345c2401d5142c16030b20400200701d2056040081d005800000740014401081e520103c0c8042c00003034078689450460811030800e51069681c00c255600700b1001042a02005048403986c2102848492005191045c1200c2d46091030344076107941d203c0300d609044070729006106079214100c6580a051041d40d03c03000503007180d405400c040c44501030b540b0140180c8142d014542201e000755514a044070340e001142c4025003440807030007450080b0110340002d00c90b800508c154001d170310402c1a0b4081e65140340c00f00d8201c0741007019141000c1d040004132 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 758710593 1250 758709343 758709353
    0x501030506070c152307090e01140a030b0703150e06090a0b0f193204021e04080c010e0301020c0c0f06040305010603080d0b030f070b090f03060a0c0e040c02060103 72
    0x3c80542d5105400c0160302c4888034480504480c1d02c07216050410440c408508001403800c80c0c0c02c1d03031140c101e003001b8001a080c41e14144509405010b1542c41612a482d01090f035070710009000c0045a005407800c4852400c400010013034645540c060b00f1921400742e0100d881c903400c0400c035100f84000790004030b45d5500c4001000140021401040d0030080c00d805400041d1180300e4514484002e030382184940b14606541d1810040c01808144101c0f40c0110000365892241e450010001c1c408075805611400c0b00282e2407004203084149000d00240007600044104001c5074007080050700342c885440309081803060600740d1003100116640b9422440350392480f8980a41b400170800300140c19503007059142e03925030b401c43d0350580041d520240c0110348007404000d28010400d98980c1580038000f011941e4514560391410f40c06038a4045034007003030f1034002c0c1e110b046081601c5040201102d25a0500d2350795100286164007083c00080d190102141190400c0e00580040801c503a00400305a0710f1500d403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 758711843 1250 758710593 758710607
    0x1c020a032c060307020105100801141311120c0102010f140f090c101d12030304110301020d0c0804050d110705150d060e01080f0604150c09030203010606120f050103050607 75
    0x5480ca10032511007030001c198903500c014510031132a03a00000340328182035083d4041c1c0d031140d52203c06031317a0402d00404100250135080030703080f01e6040e1070f00006150b54944035007480311101625402c080000c01d1012350600c0005c1810006e4420b030001c00c070100c40c030420a82590702c9015020780f0101c12101244c40036602d0701c0c4070780e44005407e041e220100302d94000a00020702141d4008005000000040c04003500d101c55546411411201104110841708595403030740002040505481c2d201440d2418549003074040704c4c0342204000c1d041040e42d203c644044c0c039202e000d48003621144209900540481e0040c2082001e036240c94000b0301d080c1d4507101c100070440520170254007403100280700903056203403a80110030180801300c83c9030002e03604081c8032a28259072255070441c154418810300c800f240300300c10041540c2801101c04207040f003040405440e241c4503a400250158a8628006000350380135040d130b40400c0c40c502d0705001c100d5140c40410180c503000c1c007002c0e20a07009400030030309090041403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 758713093 1250 758711843 758711897
    0x1b23070f03091815090e0a1509080703030504060e060907051309140c030f0111120916060210060603021c0203040f05070b07020f060703200106171c020a03 68
    0x5818a002c41e26011003080c441406526010b51544032652a030341804c10b000100b001c3c101880b02000000801640f50782da0f28070154001e00020455002140c544c03d01390802c0800c6078101c50380036940c0506243c000d0040c0301c100d070281c41007841d140600c0c40c1c01d900454200c1c0203011041c0108103980c10134041005030b61040f0218900303955108108070004000c101502c3c6e8042d0300780702920107411100103260500352080e994128a91400d048425000407450039505041d464500c0c8085644d0b039207401c00d10f001650a8006048079000400161745c0c3d600081140000044d6001407008540d6820190103034021014402c0c150352916038600691149a406540e100c2d01410040982022680b03650741407524030782004108000000c1c4007811740c182003036803031000c260030345000e072070450140c40042440401c0b11410301d08202c541c0821031006002d40248000d0a1052520b040840320209050b1380c1c0c203403c3c5040c180801e01c1d13203064080d8078000700f5000041034051302d40500701c030081c0c03100840c184218a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 758714343 1250 758713093 758713097
    0xa06140417030c070e0c1219020d050a110903030f03071803151109090a05060f0a0f05030d08040c0e0a020f040e0a1d0a170405041b23070f03 62
    0xc400000c00301e01050320303018140840c8002c0d503601e0541201290074454143c00080300603103400e062009061030402119400303001014106100d454008100149424901040703da03140007048a200700710b203551200d800380e08002410404440010140e0850780203401000da1b25400030b000740503203510b000005561069291a0130301c0b0107545580701e008418803941095584210540c01280901900e01c240e5860070f80c0c01d1101800d090042d8005030b001d41c0700411200145854002040c100d4807540c5460320450f6004042d01034098807011200c281082c2032280501ca8841d0054041c0a5030140d00e01c240601d4025100c50304503400d00c113108142010180c5001d810a1782081064072440b904405071028011f60913400e036a03420308480410580d41d002007018050348800c203c0402c41c820000d003080780581e001c030341803400700402c2100c1c0e252406a5030025070403a040002c4e04000200700d019203030301e02c0d0054640048282c0c0440c40f03003015040341800403070302c240100301d0500443ca411038144402441781c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 758715593 1250 758714343 758714347
    0x6031b060304140d020f15060a050d020d02130f0f050609040b041b06110c030127080c060a0b131a060904091a0106020f01140103030e1503330a0614 65
    0x10341c2c1001d04d4201d01221035070040c1c0020380440d208040c2480072444298400116146c1800d00000003200b884075481200e100b0410000010215140d8803c0340d00215001401c4034a03840603040d004000e02000c076040440359103003440381c40c40d8414610030380d070044a000d03116030000d640700d40e2103141120000d032043d2501500c282801500b0141180c0640180c510707039071484140260307800890318200c54040e110344664144408950342e1808003000d84080045a2061a0994001c0c01c040c541841819102c5006000c0d200411000390444e402440b000c120942c1c207003840050140d00030701140d40c406070b810b41c641034205010440c1d252600240030306402c001d00004031010141d54185104100c9481c00e0842d8480d1401005020b405001000006041d9070003030181c0b0300c5200215020301c005000040500c507403850100c200e0345031103800c044452010710006035681004411012190a020108c0100c1c1227440c0881c45040404120600e0000c4060131420001381002c000b907038180f5400ea40854880c80c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 758716843 1250 758715593 758715623
    0x402070f1e0813050a06080601230c1005040c061716050d0507020a12050f0904021e0a0302042402030d050919030c0204060e060108041202031e1206031b060304 70
    0x2e40002e1103000350084240241c2c03803900c1c0500a0410b2142d002d1002e100d104803c00445e660460480601e84000303440180030800380c145800502d00451480c284644501700c02c0e01042d485d107501241c06580900c1711039139a20798400d000c1700c0707020780c6401000741c12043d00040f4486400b07120f0510002c042e142880350a00105402150440358100c40c400010ba2014001a00f44810802212809a1989800d034600510306898583c540308800c03034103001e10340c00500614510580c0f42d54003018150005007507a20821a00c00a005e0341007030080c071654000c00c450320f810a5a41c10072540010b880c40d00603600700f0030074481c030354003c28004082e01003078001c03031080c0c81401f030030103003032008840c07103919481603040c1e06006100403260755810010801ea00303c01482400c3c0e03080061698020340c0030044d070752603908051049040d4065200d86040b8101c42c3c2141c022070045490140001400c071342d0803e4916529034003016503544543d880c4408190182c150a088c5003005001142e2160080d12101400d40e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 758718093 1250 758716843 758716853
    0x1b01091814150f040b062212031211070c140409080a051209071410090305010f020a030b030a03090b0702190602010506031006050a0b1809150a050402070f1e 69
    0x6021140e120600001400000c1c82d868005140002214159410041c0e442c00702c000c15030710b2160841c14490050741043c0b09503010fa03900e040c080500131500c035905d8a100c00f403601411500030031190403491401e05010f00076412140f000c1ea80c403250090b20074001c0380e141c00c820300e590400200e03000e9007081e1241840c0000c51308501c010825060f85590361503940030b190704401c401c0c2201910300480d0340c1041c2020070010301014030303a890141c02164410702004800000350b50b000c2c0b003584028583d50030030b07041c4515018141e000c1c0850380300300c3d02c0034030584442504141d1240c3c0c1c0520024045032054100b800300180794800780c0038080c8050b1500511815100d07109044401640c050710040c3e44038401c0001c41d080920225848900d642b5042c41400c1c1414001540c11081740640f22070b1070b402003040070040c824003c081d2042400507004c1c04650610034070101095065071082d42c05038080d00c00024040c01d051080305c080a8000c0010380400000d03503200e01c0601d01128900004d40c0000c040c1e400425 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 758719343 1250 758718093 758718131
    0xc0c01060f0602010b0d02061b16090c0e01050309120a020c04050a05060a0b0301030f02130609090c05030d0504080604060c02030c100207051504120c02041803111b010918 75
    0x22100c2942034000700d241000081c01e442d040c01203280201c00c80e11010b0010b80f111010f6030f10000a10030074403680300503050304c14a4118002d001610160410320300242454480e40580500e03c20ba0740d83c00e0840c0d445200540749840156080a0194008400c0321038100209010b4140c2100f10300c10740d810301d08560b00007015598151412450f860350341092100078641715030700300000d1550086440c00c41d0301d1512040c450701003121000c1d0084000000c8080c0c1e105055100e1743c00f40284440400a040740b07400c10302421112801400c1c0203214420201c00380900070300c150b0b030450700ca41000304071a50326555924041d081c03d0a2610641c40240072001c40518280700c4600445600340006071a08402d050041c50840c11401d1184503450b0b0030240004507140020141d44400d940c1051840c03281d071480850000c0c89181561401d003005441014201a44030b2a044061060402294040383c00d8070640303007068044580d0540802ca980c0350801c04480e43c03100040011000b00740010307140c08407202d1174043c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758720593 1250 758719343 758719349
    0xc030818031b030c2103070e0636040501050a03020f040204150804050c09010308070201030e0a17070b0603151b0903011104060807230f0c101d06060310050c0c0106 72
    0x340d0804900762055820070084601c15040c4400c0035070750b22110034185d40f82880080e0aa40401c44c003140c1140b55515014100c880f00c583c4419400040008040c108070b42500b001d005941800508030602000d24050256078103a07078000b400080b1241c45c40c3c0c20054604004019242c00940038040061240340080c01d08010301e8030f58a03005081d1609251803410800c081080900c94200400103001140750b000544294581c28240016010404004145080d180040080404440000b0002d40c02043d002400d15148986904005921000c0401d41c0303030384004421812209088001440340c1001c1554451099800700d81c440c5130000700c10100e425130f2500306084046620004d020481545c2c85601c5941c071202d14a0301e400a440c80c0c0360102c0903072154404803800c8500104200c1c007144601001c5400b40d0408404a442980c1c10001070000741c600c0d441d0b03961101c02d07400300c400600ca0000c01c45e680f0802e0020050000e054040c40020000c2002810310604000140b02c203041d03c0c58244600806 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758721843 1250 758720593 758720647
    0xe1302070c051302040b0f09040e0a03020d110a12080429010302090f06090c1b070914130809061e0c0a050c060c07050d06021213120c03081803 63
    0x50709081c1418003088410b92601030b54000d10400003008985a0072003039503080c01d03040c03486a985880400000d000b038401d090160031640100104401016000a184800da00c450b80350300501000158103103868119095014050460b10007207500c0c11446a00c10f9544a88609201c030031540e1a000e41096007074038002e4004102e05050f005105614210f011558040301c0c80300f110581e8076100010401010002c0d12003201c403100030500c5904e191070a600035440041600488401a683b8000b03100074241c41c6203100400d000b05804036414411042d0b04c92074440e0000f8529180030300d188284903442c1c1c49102040f107860100b030b030501e04075607000000b840c0301c07000ea0004182c03801140c14018103040105010078460441000070f11504500400c2d85802c6074400c0707803d044010032508103403010740300d032004641c1100040000c000550b030341050b90704541ea005041c252510054180d05a862480648010b00414110000108940b01883c50311041080300820f40b420700e100040d404410150071300303044031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758723093 1250 758721843 758721863
    0x30206040302060609041a0a02190804060b042906090a090e0d1d09150a030f1103071a0a0e060a0f0e0312030c03131208090c0a0b0301060e130207 64
    0x60582c10811190480d0007203400c0741d12814681d0340c064201e44940760a180b4913080c9000144504200e071f068803042c0c110a00158510a9003240041000c0320489003181c0c0c091609080b00e190382030030300c0f40005980201c0400e241c140591010190410310044030994060420010b075161034480360341c01c000600e0100d05c00300301021030404071420301d03001c07a000c0b000b08400e240d95001c100c11080b0048400c4042583c24409540b1a004a4821b2606801c05c079504000c0d8642c000042100c442680c4d95020f005495541342500034204140d2039180b14845d00c180002c1c000d00c401580b504810040c40790465905249400a1010f404035129411024038680411034051292450503046610801c5049045001d000b0300320707000c918280381e8040a0301c80060701c10084002980b001c20074030041405c5401031080c1e8904842601c0081500078100c03030204160140f0610641c6d1418181d0741002512210031409080da800c1c030204031038658402c81c200740d0044110111094203601d61000b002c0c41d9029009440d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758724343 1250 758723093 758723101
    0x8090618040906230c030a0903051201030f12080606030a02160204060f0504180210110a080408160602010e0c010f02031b0a0309080a120804030c0204050a0c030501062c0d0c03030206 80
    0x43c1603144e000713101041050018041000c6482c1700021a6408102e1003000507103c0c1080c1411a550b004080148006880180020080c8800c01ca0103c215a01c60940101d80010301e5604807003244060318156004802440131a82c00002d0703030040c2148190b014400d504884007600010b080d00e40035800312074030b00071070541800700703040c107010708085910031840c00c4560a040d98041900401500c80c010100841c5280e1b0b640d00c0e000620100400c0c64000d0b0f051030300e560721a00c40544489030700130004010201c40c40006081401070090112402e600c2000e0710080807620019070320083d9524802003103000030000b00d1160f924000c1c10a03100031070880203001c500194507000d40000e66030741100300c81d6403203030310180009100030858407624104c0d4605110351307448038034040ea8401c3d09580001d510501300000c100340d0302c030b00760b00c1400507001b00c0ea8284544d03661000143c4941d04044180f641c41084078020b1290b00c55220294070410001800781c491134100e42c0c0f1039030341002d403a400480040e000b5034240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758725593 1250 758724343 758724371
    0x10311132a1706040e1f02090a120f0b2a07020f09040c09020c010b0909010f14070f052a03040801050106051206131d01090215040308090618040906 65
    0x2982801007a0405948115031103040350201100101454070882d1100c42d0000504024401e42050701c45032802c07068002280f802c000c010750031030381040d400380e0001100040c10740d03460548501e0701e03a0050203901c0c054420781c40d40c42c00310f10001c0100c3d4031804910300110450392400d220510111444240a4590a0747e02c100110803040082c1c60348600d40c408240301c0460071071021207080f104440e034011394403c54036080a0140c96010700301c5500a605c8c40400402c2d80d41034009401004144504200007018000403440349541a18000001055401c00412440c0624005e144c126000d8003940003181c80d076010119107291b0410303030741a80c1d04040fa08004040090003428050645410701d1800c1c00883e8020741e07110703400140810b108407911001d80c000308040d0317880381c01c03202e00c00c90318440140d04001c1014041c14107040c04034054525985540900c280e52001c0e101a20b40c801c142c149011610b00070000942c02c0007100c49281e0050769410350b211b0765140300d00c00ca030610404012a904000c2d20304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758726843 1250 758725593 758725661
    0xb070c032306090706270b1303050c010f0f03020a0e09042904050a06020f120a0c11150a230901050a0614010c0209130c030b0103021c0b01031113 64
    0x30658040d07100550034081c26801006c0c0f01c11000100c81d4141a9941d03100790303e00d20b80c0300e503032091401c840b0000b0300c003500358003185000040d81c1c021001c40f5400c050400044480342c1401c0c4400c0000f640020000010b14440d13002443e6400c500d290150803210b08200180441505503421a142d0007400844920a49902001c04038401c56a4121080e490191622a2584072055000740060b600090141d1a4100c0d00244c0c4c10418044c10050f000b880d10449500040112200c41c1d03010820242a1400f080000070320030344400070085400402d611514940740c050700300c0202200812603904c0d030890040000800040c0f00c0c1c0f00b400000b01e0281000040785044801030307080007245401e050078a001a0760803502200449906568400316950b85965100c8400d054a100402c00b4a00c820300000b40514010a94140e03030084402910844104881408246c0000302c000c2c001030084004001140340e00c00401041600075004e184140745914085049550000c0c1c0f16609140c480d09a03400300c9884a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758728093 1250 758726843 758726851
    0x108010c02062d040c0e04060903180506090d1106070f031d0627060c01020d050f040b0106050f0909011d090d020c0d170c0312130b010b070c032306 65
    0x40d0203940800d6008030181c20b00b0040300c0250300700f521000b0030104042a41e80c9070060144501c000d05c42d040038503085000c0d104424040e00069082480f021303001198440110032030741c2c0141483c0c90041c110041c840104034007401070f590605021060751580d12000024200c280c4900c1c200215840180b8015140503048801c001d17000100c40c04000c502d4441ca000c03504018036400f03000041d0000e041d5400815030036040903940085000c070302d44411a0f815009010500c482038400e224958840352180d4040c1e204a401410501c003001c0100041409803000302005035050b204a4501040c41000c16a069020380c032803098041011003e400c0310590041854000060401910010101048c029030301d83c40512054494210001246c0400c048074810108103001c40307400680714215643ea494503031700f004660440c0c600c0d019000640300700d0302e610a60140344d84070b2280c501c240d00b440c4001c840790b009400c0460740b02c0014103000c008100000303240d19540410000d50368208181d10021760600d034002c5c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758729343 1250 758728093 758728111
    0x6130303080a0e0d2703120f0320040302010c060209090f06091e0a0c0c060c20070b19030b03010f06080c040614010f02101113060507170c01060e0108010c0206 70
    0x4c82c0500542e44002d428545130512929003d5034001c2c0e84c40280a84003a0741300400880c105810a20069000f40c2000308a4485480402050f000e1801c44904044190903030200d0500030042400158021180b003040d490007050010705084049010400f10001500e12004100786c41040207140c0c54100c80e415440180c800840b2909500300e21a440880c20282516140395100c105c18010644182c55400c5090740045c0c05120396041980c01420030912440030000c8003d040030101c1c11050000750b40c40c2250052000b4503c1c241214aa00301402407540c0603004150f01c4d02940e0903165000d02913100e03101e0f014400001c1a928000c03100f031130441c6002c42c030760041e81050320812040040d0f541540d00035a00382018280001c91807822414408030103420940300f4a461544802903500702c01418806c502c22020542441d02e41c0415582c40c0601c1c000200b14518002520b24150a804064000c0c01c5003d030010841548031181c0d1a091003090f0400c0c1e00d00c3c0c1d902d0b0001c0b031a04d42c0c10040c20360403500b48 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758730593 1250 758729343 758729353
    0x51e070c12021f0f09051903020c03070b040918050d0806030706030b0306010e0a090b0a0b0310110d0c02120a2304030b01300b091c09120206130303080a0e 68
    0x301811403501c421224404481c0e5180340107071590113550060401c80d0361080c1030f036244c0c038101040b40d0b40d4414211402e0f00188101aa02405402c0020b0490140c41c0c400e0031541c1001c0ca0032040c01d0150159800d0a104548890104800a2010442c40e40e121790540c590a41d10300c2c00d20241407408220354000070425050001201085e10081255410342e05d0350340710000030340d43c2c420b000e20107050039140050511608c0410041e2020450380801c400e9032080301641c0520107400b009030180c4002401c0355609550801031041a1280c56024500041103401640d460f84444114500300340c0000c07192002041d0306111403025842c404a560b441101481007850805013983c0b070b0450507500500558415650010081b502c0c404086403400400d4554400e0b45441e821901d4407442c00c00050328100003a1090307242295014014588105a0301402e54039003461070314210010b051000703048803d980069007003040c8407405a0090b0f007400078500031703194010b590802c401402d08a41c050100f9040903005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758731843 1250 758730593 758730613
    0x212090102180d0515040f0c090903081659011808010c090303031503020108061003090b27030403050705060912011d1005011503051e070c1202 63
    0x140c507510088208041d90711545400326480d0492074030702e04c081618403100c8018100701c100401c070b002900d00248540130701c40341d527699140d0340710035207040010050204094070001b40c14040d040f0035000034002c60340b1348041d50800c00c01c03c1011062248030740d980034201e9880c601031100d50002405564418841184c46030503540b0130009484a01210300c18108195080d019440300d008080755009440040000c01c400481d42c40080c0080c0c1c81c6200480c0424208400c802030041c080c0d262608076074040e1074580c03c44d900c9030200030a184200140106260b0364400c4240800e0a1070403a80c8110001c407c10501d21101c010340c110681416800340585500402c410700000d04045100e9003114016a2001d456800c01c000240c040c590b060091001503117400141c11003040c84520000348440b80c0401d031154030750b040c036a010540b2401d008400b85d01440c0501c200c40389200b544040d50106009440d6202c1240c0d0340502440080151880c4000071480021003050083d03d84203c1c074843c4440c0020008022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758733093 1250 758731843 758731867
    0xc02030702130e070e040f030e13020c070501081311100c0f11090c1c05060402091804060b0f0604050906030f0a030c0209010e0f040210120f020304110402030118050901090c090212090102 82
    0x241f0110000c0070080200e5640f840b940391001700610390003c0010540d26003480c1074495542d00e88502c03401c0c0c0000d00f4800401e49001c5981100752840340c11896002018001d44184585030644102070020401000c00c0132022418411651110612444500800c0080c1c0c200308089607a0241681844100421418003041da01d401040400407800f107021803aa5140c10001b00203020b0700010582100207080303041c1c4404000030040784510304c203040811654031003034103000b0f034804042982c90b04207104020910152811403201d643c008401030840741c038580344c4116503050007540034044000c954040515030440c81d22407611400b414001045046520b003401c038588541c1805080640510034024182c40d4a0b40b0492814032180c581c18000d200728081004040c00951048a040d6000f18920500c0001c41c9428000c490480b205031514100b00000091010020f00c8007918001c420340d83d520005001800c0100303200700900908900680703ca640c2c581621b800f03c0000d1140720307180d104201e405000c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758734343 1250 758733093 758733113
    0x50c0901080115021e21040f03321b06210603010e06271203040b0a150b030f0a1b03230c0415050a120c02030702130e070e04 55
    0x3903501507081c0d0409518400680c1480f20401880d40170443c03031950700d0f014400c001400008900c80050a0a4103180641320f203d4a008501540d1504c1c0302041c0d040000c10302d024482c0094020804069024021020344020074050882000f04550451001711100074800100002400c03001d5880f50310300ba401d500a655181c01155101449184c2400400d285440035401a0148185c3c0780850313910341001c03014400c030712001d901c010300010b108401c40e0940b002c0200300c0a071102c0d2070320700c00c5017103803034560780d820020030000d10604e04540d4500420304a4120004504010103000840c03d5403410605400e074030b0024000d1030100110300340700ea80005910244041081d50f0300c17510b400242d6101020400e0011101e0f0100083e03e691001c0501600b15280710090041320790005400c0034a842d0f41e88292154000c07035400b4000b183da4118181401e280c29003064400ca0b21520542e4680b21030b80d800169a4a1040c011081180e603449200a61034410810140a0b098260381e400382c81c82c107984c41d00c0c545 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758735593 1250 758734343 758734349
    0x17060402100302070c08210f040b091302030106082d0f151503011d0108250e0f040b060409110f01140d0c080604060810110f0d020409050c09010801 65
    0x1440700045646605120b64196090385501c46103e500360ba0f5603500e170a903103152512070402540300110b5050000b48520b021982207c00c0003005604251401d01030006039004001407135000000c004000888403030fa480114007800e0180c0700c003a45400d2842013071481c100041d01a01032a420010004403022041080300d50106420360700411307680d01c402d0640c0d111034040030b005030821071484a00d85000c41caa0f0145060752424600b046441c1481c01c40d407003141e40c0a1080340f00b15001030409010b42c1c0030025400e83c41e20559007490310f01300c5e500c0d10008030041c1d0803141e40361481c0d000414401008856400f0a40016044405110300610f0f50bca040464080000080c825005090520274a901400305480c4045070b8465040c1c503040c06070f00c1d40c00a001e004440c0d0000a4a0500040e00d0340380c0b034444c5130180c03642c00000742441c8010001d084000c0c6030048541c1c1048006008013075a8040c600010300303200c190400c1c003586481c5440c003203405540015101d40580c810130b1103044101d0340d10005641c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758736843 1250 758735593 758735599
    0x11d0405040629030f0102213103111218030a02030712150c0c02041505090703090308060a0e0f180a0c081506030d0e04020d020a090f17060402 63
    0xc0e10707503190480c000d1140350001410b9007044458805820f03203200c415001003400f40d050b9081028107002e160308038420940c00099003130103440c0301e40000800d162200c0d80403465040d045111580c2285003c030401440ea086690000c40340803d00030103510455000c0300c550b8090080c00d100d48500e1685085006140710341d100d154003048440030961b410070001807103c0d00034041c0c0d1034240d04c4007010360320b01d0007840007134540b860101c08d4190180720a2194017024112582c45111400d0310b40c4c2000081e0915411035101d09a40c6a004580303560b51072440c80c05a1040c0e00c2c00121031000385001380a281d00240128440e5142c080100321079041950041e50080d81510031040a40d20003951044950307600c0264415032003441c130f01504110b02c3c90040415514801d00300d5010740c608400101002504998154160b004a91181100b500400043c281c0301402003015041c07c0180d01d940080f82c2003070f64038000080844000708400c07042c0030041c102403e41501102182440b80c2189503803032801600c0240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758738093 1250 758736843 758736851
    0x10050403110d05090d061d0d2d080c07050f060601090602210903030d020a03140a1e151d270a0b06010905040f090201020c030d0903020409020a05031e01050105011d04 73
    0xf0401070254451440340c250a20a101821002488266600582300020004c12040f100c0c0c06000300f51805001c40c0a84062078000d0f000070340c2041225000c0d00940112110034003445090006141448a040c0140418000301035502d012000101044419404081550042d078441c0f1498120040d980303403041351120103580c0d18925900440d286110301625078103060f01c0412940e01480e0301da0000201c1540303000d1000d041e82ca81b0745002084400340302010a842e400341d501c15400842c03640244003291360510000003041e030303900d00f505200c811001084091400c000100008000a06001c0611100c00d0051040e11101d886000e0741e20f1004503030141c0200280170014215a1103082a0006814080e0003845600b10755118a0040e10200d88124058001c20242400d1414005040c1c1d03d42d00a0350f4903641c019180d9020f1000800c40c000081e070304007820040100d400c0e01d00b080700c0010102c2c00d62400d01d100500142c91800c4903c180c21040c104210070410380b0358141201400c07408003000f100e00117 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758739343 1250 758738093 758738119
    0x90506010b0a111023070203070609050c0a0b0913180b0a0b210c19180207050f0607030c05030f0f0916150206060f030d0f0302090310050403110d0509 66
    0xc1d07068102400511668414040004034400085d00b00c91394070301c000200600000070300c00d0340c1602184111901d50042c0c0c002c1c00088046400c4c0d412084155000c6c005844007050510041881e00c40150400c580321503000a81050904001f00010300c01203502c0ca04012018940141d103d10003000000038011680040100310021643d03405183e1500000308150352002800021114082c1d002c0c1c007514442c010401180c1c1c890030080f5020311400095540a241c1504040200001d840c45005040040364284850000510200200b10130005404001c01e0145042c041c0282603440039001c94080010600034049822610221590051800c04e0310796460358030b500c4080c0c274126810310501c0010b540072000003003c00c0094035501d0403081542c02e46103181d07240700a11070b4055803200b00c41c1d09a8400150b410181d8414044003512014524001d8900340b0348100107450030030800c24201d402c56a07401480201034222012415540c4420050200d07100480d101034550b0150718021402030703560b44103407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758740593 1250 758739343 758739347
    0x30a05071e0c030203010c0f0206010b07050a0c09091b05060307030207020d050723030703050a061116050d120c0c0b0c091915020703050304033c15090506010b0a 71
    0x820300c640c0320852181c803210002e06008040a22610050f4080c0d46040390b0050100c1c4102c44502c4c0a20382c40d001041543d00e00a1544030f25848a0300598003030191541520015110441c090001c1c040e4840100f0b04200038102203c03202c5264040c070340207031480e81082203251913010650740d00160034103005032211030340d0020400c940c2c0840e000404d40d014240001c10080303140c4100c0150380d60b03d42034200c010130300039090595503156804090900e5101810203800552147c01440c1900c030140a400c0c00e151b61070ac02c15000c07111844040f51140c000c0b00c00c000c2007036401000c07104c40e480646014003014040701c0e8040d0a12031102000b0f0320340541c10340003500041c4840c08071010610060003182e10300540300081342d440754581c0117010400d994600d00001945c8001148420b40c0c4e001000f80d450149907582c0e900c126034406480031400500d64050f82e409240c08049041c0d00355101c01e003090711a100d8500142e5540c400c99031140c00e245803001e03404c00700360005505c9055403401d212041d07403041c40e0303001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758741843 1250 758740593 758740613
    0x304060609090b041101230c3f0307081303020c0d060e240f07020718090521181c05150105101b0201030b03010f0b0a090608030a0507 59
    0x2004194038140000031080001c0c40100e44d00c12400341d10b19040c0907251800440301014007281da014140401900440d80076641d0004103000b100d824111503440301c489005201d4142024045107507491080550340540a280100f5241104182140b9240d4942048080c00245000d80070301c4a06103003440c1801014000c200c0e480f140318005041e021145420b15051020706908986450140524a00c1e10340e40346d113802ea803543c0703407682c0c100c4022565101c40c0705a40c1c182c40140a00118840c150000451600800f070490078400c0d121400710301034990b41042c514204400800d525000d014800d40c40040003500c0039504050300b0408002100c0e07a081c2c00240481c0b20f240c10386901044220300050801000061903c0885d1103800e610400b41c1e40c035400c000345000b1507074030040819504280c0c02d4280c01d8010815540d94814100001d40301140760200b82100c2d040010340c10101d548600121461030086558001041040028070040c0c1c1000c403a16120b001c0c00900005101012030204100190381c81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758743093 1250 758741843 758741849
    0x9270e0106031704050307080a031403071e0302070b0709060e0f1809010c08070305040305040e04021c081b070b190c1b14031606050a020f010e06060316030f03030203040606 76
    0x142403c601084100410030f5001d0711449110707115035280010702c5203000c2455100140c054454402451040340010041d078402090035040041411050000fa5100101603000010b169030050700c1d11907601e04010b1039100136040009000060b1410083c0300e5100d40e48154081c030076201000c5512158000c196000714800c081e0240040ea0000c01030a00c4d01503000b0344c000310f1261b6400348280c403068000da04440090f2005000a03008200901c8512945103469803c544064407910003d40421280c1e400121500411034240d01c000540b203017401050344180c4000300311003018250306841d180201e241c900c11840b280041080e001541b410f0b80e8007503421150402e070498006594405103404402d103840c0207001d611806854003460080c20309000800e1020700072060704101b121800c01e003090302c194010b0b58090003180300c0d0511190303030205d00380a107201c1441e00702d00030501820008105400d02001d20054038041d0b5802c182000800c0038007403030340019901810016a65125400c094002d040c0c690 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758744343 1250 758743093 758743103
    0x201122a05040e0a021201120f020906060d090c06090f05180901090203191a0c03060f120106120c060512130503093c03070302090a06090608060709270e010603 70
    0x4004c002d8402107540040c100341d6141c0140400030f030780310000c1c2c40054481847c0903103010481d0482da07005040140e80d81e0b80010300109031a061050040c403c03002d582c811041200c3c010502070341007100c10341126462026100344851100d803141840d01158102c3d01030f0107001d02d2100f403000800da0b9888294480c030000c94000d07040d200d100e4400300c106000200c00c2041218040740d070300710380324141200d03450543c06500ca20302c2161035078032618100004840c0100109038007280000c052030403100240f24500003082c0c606001b451424039420b244680300c010744d00180c2807010800c8000d04071144640c0442c0d0090440c0c04420308078106d8207041d80345004280e0025001545074822147c058100350b00030030030866201941d4401306e218115008402000505c240e0540e004590030b100514155106545c4520343c00030001d2071030359800003801655202e40c015400354000009000010354851210801360000c20505981100000403c80c2c080019510802603282daa0418091400007900468010343c1c100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758745593 1250 758744343 758744369
    0x1060c230c042408031207030b1e031002160b0f04021011030c0304260703020102072304050412120203060a12141e25090209030f0312040201122a0504 66
    0x84c1a00682d20703031140320340b00044410000001d14440c828003d46850f09400f816064010880c2c400f440c82075803400b12010b41c907018180402044010901c0908000015003844075800d165500740701c41c0300300c4040d100908141200e410040541c8950125592441c01c0b8500a0b01c4241d183c84c240d0304602400380c1001c050300002500140e0284200d94001038200180003116003400501903081d601d001520000340075030000e1600700080102950103240d144444648582a0301c09040080c1c104c402c1145c003181c051200000b41304c01198072550f941039250240000314036600708a00002c40002c0c00340701d2810071075202185501001030082601207800ba4100c111a400711241450305031060301c3c4091642c242c850005070f100d0800208541d00000748154400640080c1440110b8002e507000505294144c480c915003480da00d4801c10052017000c03c030003400d0003503040a1000400c200015a01401c0060610a44160b80c81c02e400e011510b200708648202e28004c0c801105503100c0c0296480210300500b2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758746843 1250 758745593 758745599
    0x20c0102030f060102030a0f03021605070f150804050c060f0f161b061205040f0c06080105041a100c020321030a0c1403151801060c230c0424 62
    0x54014501a00031111038600950382c0f00300490341c038001d0b03080c0f90000502d00a9403040d00d038003d5004201d643c0c1880150054007041b034030f4140c0350415590180d48880c0b0320703890400c02c408103562050900055072401c0000c50a060b00da80741c0c0c500007403c0d864441d18002071000c642603a644202c0d0041c5000195036511880c211f048410200300c4220196204010300541140e407a40780070501c01a03400c1a150760381002c020041c000000e01d4000d0044035580b5204443e030740800c031072900c102c0080803244d6403411a58107050600c4240e07008208040f0400380b44a1041e0400c1d5140080d03040c0c110501d2030070340a601410300010346003410b070b0031443c840c200c0007140362020595204000c0d441201080f03424007034161400422102c0008a100e000e10810041c0046140c40d20026194000302500500b030300c4080c20340c5409a0560202030340300f100801c11015031182080760b1a0600c2c0c004c043c00040c500640c0050740001e540f101516604d01c0e00c241e688045c03100400f00d10810b0b122014000000e40c1c080c66071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758748093 1250 758746843 758746867
    0x90b031504060c0e0102030f250204020f0a0e030102280e0a060c14071406030901111305011d0f010c0501020c0304080a0b1305102c0127201302 63
    0x10800180b00044c44d040322410240d400002101c13102c007100d000440c98040d00112540d02030200004e1503e88041c85d80c0204056906d074006442e015038241d1850b50b40300c000e0304001d044c240c0c201c0d1110740241d005009501d0300800d48c4c07030140080c4403030f01511000a001c0c1c6008a17a105501c4d0500c0342d2024444202280d03140d0b114002010140c8980c01003884180c0100407140d03190a24400c0e4101e000c0b07007a54455807401c005024580141d0494000715070342407100c00401494206160117240d295006a04000c03c1da4080700461b0300701c4010202e40c02d00e0007180081b4808901040c8000d05100240040d403040200c254101d0f038140344898150ba89407a100c0e01441c2c2ca44407010007e48502c28440e02144298005114519902d03510070000d0800b80340701d04600010702402c40100008181c0c1483d07440d00d103402d103c0110303134050086000041c6004e00204003000c9541c00d031042d203200780e204011080001c400107504c1440780c032a00340c0c000c0e0442c00308000516081200500070102d038004500381e20503c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758749343 1250 758748093 758748101
    0x15010923040c0305070e01090b030a09140a0b042f190504021306110d020307060b0f041d011a03031c09021305010503010501170c0904031803050f07090213090b03150406 74
    0x41402e586c2c02a882107400011901250346010310408054100040b075519010340d44601380c10340c49088001000c1c446484c055040150515041d038490400500b0442084010600401d13829500b4119450f1611749901d032a80d000e455882090050080e40700010503981d04c03400341002403000078030966541e80403104140b5024480d00c0f9030070125503a40c400510141001c60f1036044542d1036402903090000986504014001d02c02c01d8581014407986c404640f91141d000700070f10b02484003000c41d484410200f140e421600c00c100050303030b07081900503414040c1d40c011003110155030702403402d070001c2c40e01c4c2d01c1400010705a404009506c0041b01414032000e14168000a049035000c9008020300daa0f1160203403d10030088890703001d00d800182c0c051809103407903828540c00074003a2038034500d07031440d009828608210303a4000f9507159002c41f40b07483d92880e0800c2010003401c6201d01c19801d00d124404501000110780c05848150b60b04c500b0300f00b826441c00c105950308241002c4840285050a05241e0018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758750593 1250 758749343 758749351
    0x507050c0d020c032b140d0501230303040807170721110a050a120c050909010b090a06050105040b0c031314040c030c08010513091406060915010923040c0305 69
    0xe4001d000000d10318011142c1d5600201901c1d101e426020140258210f801e01301000c19000c20000900420800841a210f02c1d40a480300d41c4e03803140ad1340c40105000d14108000f4085074402d520400c014801004007080c180e08441151204000150640750300034240912a00310601c81c0901886200707010440a0801503024018000340e80309070300503130a10040c40100c1c00b0300c40e003041001c1c00800c55240c140d185028007602444100002ea41c441000400291045d10f6042150b03460380e24091261030700f0303004183c0141d54000e08000781c61820780060140c0c0641d01c01d5040307042010800100d04207081c01141c0030882c0424100030f142d500d03805040552903103450302c58091341c0380080c0c401c100b80c00784c441c40401a441c0d0f21070011680c6403400f040300c40c5400541e2200d0f01500c9498100c0055428589142c42200103000b4140514015080c0a01480001c3c01c0101d500040720a04500b66001813040303090b910f5103074016914204440c9104101c4600b403004580091400c12600d0440764150700041c02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758751843 1250 758750593 758750599
    0x303210c042106090203100507170609130503040806040b07140c120d0e011118010912020f040b0607201e0913020d0503120106031109040507050c0d020c 67
    0x1a94542600c0c040d0507004500030300240845940004080ea52207542e40c10700c4511071640400ca40000e03602081c2400c4a081c01c0c4401d40341c640d02401151600320f086d035401032403154131f02c4d00c07986440d03070001d20b81d00d10150411410b403030b0b4031000c8014004240110347c06840f6107400c44403281031524140303c510f102214080002482810b200504045980c129510081500300802500650316035011665125444200440b80d95200b15080c1100030300499441140c001d50706925920640e0f10001c0144107480c480381040b03d000001c1c49403d5044003440301e41d039010340c2c0415101c2c01c6000030400420094641507403081011550804102c07840b807038000c0302d84110701c1d000c1d1404101d109000f03018000210551001008402000ca9030500c203890a034003e5803c2c14144040040340c0100740c140000d400e0540e070907003000400c01480241040c0700c13401440ca81c54100503800805048196a00a00300c215202c1d0741c0f07620106480c50320500070340c4ca15105c04400d07501601080c800c080d5075a60304103d9140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758753093 1250 758751843 758751907
    0x10032003180604051b04090525090c050903010b040203040c0e0408070f0b06130c0c150f0603050a0605060102070605030a020d1439071727090604050903090409020409020303 76
    0x1400c0c140350140d247d074185e007c0018609805140d05a2925800740552080e61803491080050798920074025810003005070f8541a58039090384042c5400c0d144c3c5407490310701960040003848001001d42000f0002c440388010441a107868501d040003140c0715881014100941d40d20740c400900c0a10100680950012161050135218802d40d0b00e0030784a541020401045050301d0307040104031007413152004000c45490005480c00c0412220044903941e81007a520341d8000e840440c204a01d9205554205800f4001030001d1481c0943c020000e21008003030f04500e54012500c4d03038003484607400c201103814001042030442e10380400406d000080c030782c6800340c541d0265080c19011150320070b0000003101070065520302d82032403622520001d49428244411400d000c20032012116142d440e802a402401103114249131120740400203d0000548810310031440c28cc144100c4900002c21a0030441050b80c000c1070701201130002500030b0840200c00703501400006a486440c41520134600880650426410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758754343 1250 758753093 758753143
    0x5151e0301091b1b141203061201110301090911091f0603060e040b0714041d010501030510031506030222051305060402190b070605061003200318060405 67
    0x580e1015016501d8000301e04e81c461545070010340e24a1030700c20740340140c03d500025002c07070403054070b04401d507180383d0101c1401006005140c41c0002680300300d40d900000a210701841049075030761510042c4141165150749031340e007000300020b45039100c5820500500201e0586444041c1000b2035001c0d90f01d222845142e4140407074401d00a1103981700351007907121818101d98883ea2210382105020f403503e001e01c040741b0704045100361a20000d00140c1811030002c4c841c003090408010010006800081c145803d200802c144042030b040740c202100e4000c080f44a0101c54984c441c00180007640010303400c007400f510314440b8000325001501c0b0070592400100020354400100311407a5034003910007040c582007600420302500d05000130208031200300c001d40701c03032683d54462102c00d640286001c07100c542d100c200700807062400d00307102080480241000d00008001031006c1245a40100c500c0304926004000700790200c000c0320000000c0e15224003100c026040c903042446d07031110501110a40c0e5150f44e510a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758755593 1250 758754343 758754371
    0x201050c07321912110606041505060c03091801080a0b040606080d090e0115080a0209030304150305060127030b1b0a181410051c1d0609061005151e030109 68
    0xc640303620620006004e1b60f4030394004000103000d007515610300210340480c0114143c0c0d41c0700300070903400c030040c3d00a41d50b031881d0409201c8507161102c441980c40031203400405c00c420022842404265020070701940329540d5150441c010815a000f0421610a0510b40515030341c00400702e0041d903824403071807106a80e9845031050138440058025000a90b04000f0600e007000d51740181506040040130b403800c16868292803100501c020030240c0002ea02c41d0300b070101d40d50300300a180f40034110086594400302d004104440044c8550312004002101036000692000c514101c00b10610300790380000d556510702d524004007a0b04a0140c440c0a0225040c800075412811030401e2002d4078011b403001000f8a2915410345140d001902000501012440e10b00001e100070311a84110094265030061504445549149441001400300d0600c0d40014148a940341e01d0300194006c90300d0885a2032100c20f1203d214104501030700d5507009612030f000e42d40c2000c000c2800c0145059402c441c0041010340011058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758756843 1250 758755593 758755607
    0x601080f06013609080a0e100f08130309170102040f08030403020a060f0513241d040506180901050712021615020909090d0201050c07321912 62
    0x440d400061001d0061401c0240e040f00300d0003189940d080000d04400f00713840b00c580725030043c0558000124a0300d48001e4a00c0c00d01c1d4014503201c00c0e0b00d8441000c401245002c0d1000c40d0180407004c00c00c00c104982e07400c0500c944150409031a1100142900c0f08043c40314078080d40080c003889280d001c0b122004a44054000155422241c0017881c00a001d850004265000281042c249007042810020201c1d8030342021210002803458180c6c00c0c0c000034268994103090140f8405010030800c0304130349500003020f202000395a01e10200c6000603d501c4803000615040400d52401c0900b038408802c01c01481810342c0020312a013803d44a4021210400400b00c0c1280300b560501c0f48001d0003003c40c6404a0b00050841c82040500e96006103858014070002e6030128088980c0303007e0380d0014003202503456081c05841d070030003030300c1c00b03035900346061952150600c0d207940f0303010785200c00102e42000c49131401f59540050a80b85000f5115a1941c0420340e07004041031301c506071850040840c072034098510617a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758758093 1250 758756843 758756879
    0x705090a0b220b1005030402010822030f030606050a080109022d0d1d0322230f04090c150c0f0f050c03070f0b03100906270c050a03020703110601080f0601 68
    0x500d41b440e543da1a401035540c45009040380c04010300782040c0c0d03807074004040320b403048071802510352123800040000c00400350349a035007086d01008030510468003010b4218441d9810342d1340304074000d604c41d070300e000484c0c1c3c11050158905088000d0882c0c000007504203400102040c8d0850307035003444070081c01400000c20600203034050360150310030801e01400300020441540d46006110418461650385d44801003940c041003c01143d202c15035410400030301c0c1034003062590704d10075078080c4848485a103a24400081610800c0f194401034a000d0300e0700351260707444424040e404448e42921608a04100c807100106407000c803014410120f620b0614900001e2840c200c071214140250281d05025000e10b0540010744164043c800068003c00d8800321405860060540041010209101e0b039810302a041c184680007011140780078000741005a010044a109103160700700540d4691080c42d044440030b64a0510014034002c00303002150081c008144807041610f04001c03200c00781d072074104c00d202c3e50308880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758759343 1250 758758093 758758097
    0x903090f010c0c030210180f14090901090f0f05010518030a0f170403081b0705210c06040c091413022205070309140a02030705090a0b220b10 62
    0x82114a415031150030803107440c0344122061007402e0380c1d9174003107803482121504160214105112100c00e0087e40c0c540d0f40c0c014602a000e4280c810301c3c0c11800c14001c826640d040b07000b1313801d0301c0000d01e0b0b401c0250051b1421302d03031040c1601c00102140c10000783c000d00a034000c440550800c80070811341d00c00c012500e5010564100034529050503030348140e036030741d11b00c20003641404916a52654450b00b040191403040d8060f449109003450249800e442416806c0440016101d040c0041c001140c000a14884c5e12250114201d901c0e140381d4a4201c0940038a5000300c1192068008100130041441c03010f0084a60000d814007a01c03980c4011002030803021903a14002c0d054401c606005850084291560209502086824079502d0010079081d29421110180425201d2600904006d031000c4485001040310300070f440301e0300f2542c1c002a100d400c2c501c60f0707a104a16180129502e03041a038080300740f98100070300a000d24904144500403045c0d1001000f03201d580740c10740e03a40250500010b04c41640c80c041d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758760593 1250 758759343 758759359
    0xd170a0c0e06091c08040515041a0a0309060905010b0103060f1a0702150307030902031014190e01020403050a02040b03010b061c091a0f07021c050f070b0f010806090309 74
    0x402e024050b00850340c0340d540040821003580404160700440415540074120351990b8504090505c4a40858000080b0703102c0000c000c01c110094060304144206a01104019074070420368030124064040c0850140400b45840c0081040100562084452400a132800e010065a503843c2c11044078191040c0e039050181031000e0340300c0402070402410410300c0141820030307000f10b08071070b414241c00407502000403d58820510041d4a010815800e40d00c10240342800160552206107500d600080d01d004c085564405890381100c0c0142c0000d00040c10720030003103450765600d0a1941d51101030010a81c000c0340350880301c5409043c1801040507003100a0601c92401d000240383c0640e0380c0781e001004100f2a65403855200240801102182038120004815640d007465117203804400f001070701d10025940042d00b008038100101c4041015062241400c0b61281c0054200607181e218484008140044000c20003040c90200c0320114140ea44200c1112210713501c2401c41d80d40d130721407000c0d800da1184d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758761843 1250 758760593 758760617
    0x23090d051608030402030111070c080105150f0d050f01020a030c03060b04080a031d04050f041a0405121303080d090c1a030406110d0f2304080901050307110d170a0c 72
    0x2c503004540061000c0c0000406c1c03a040c001c0b401071074104950071184002046010010300000740641c5070480c0c13800221b4803c0b20214000038002c0030340d811285000e1488182c280c41480f00900144090401e214020740d903500c0c000c0c4001b40103005008045010034a4008041810100d600548040c0d61500d00103010601050b1015680207180b041d040300c0d0351004140030b441070b84650041c24011110030003522083c0c05c29241210307402c00c82060710409610314400304008584c5c00a160120202207940f00e99548400d90f113401d1711007005400140155100143c840c0e590720b40c950000000f03d000e4442c03001d2164454229103a500b00340c420108640d803040c00494007103419503010091000c032800540f8031300310707072004030805541c28540004c3d45560b441d400d0f18000c00070414682c43d50200380814408500c0c180d2b03528001401a000c1c800d0400c480440051050340c0141f80303140d0a0713610002143e81c16410b01c4402820900311265060846040e80042212620180203282140724540c81d41e41508003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758763093 1250 758761843 758761853
    0x2030a14070f1e1d061002010f1409060906040812063609030a0207030b070215090601060207060f050703030c02100f02090406170a060c0323090d0516 66
    0x128005a2508074020030030005004060580e03010002c00011440004615460075a0b55071021194840e6401103400c8040d00c440440e0f2000159000204440404110440680072030060001c40f21520442d8541844a1499005802d9451044c0090011502d20b9900c0b00a45500d511040d42e005000ea0018080d407410a041020315039072100d80900341c190f080044900005183d4100886241c50200201c001503071441c01c03041d81a8000a040010740c580618440000d58640c240e01c4040c01e0001901c0c00310740381c0ca200340704901d0703420b1440020f031159007890303001680c030b98400380305840240c86110310014480380074a50390010b65030b45498243c00e0000c4d6403004c0e00901a0a0540801c40c040c91504c40000301c0e240c807a4440d0041000710043c0c80d10070741070901049580c1c07500901040c070790001c3c0407100030400180020540340e00800101c1c419240c1d1500ba00605000c8401124110394985041510400000124441c649040c12111a030f0b1a0710070590300d81c484c00c4540c8080c1344c508184e41001c22 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758764343 1250 758763093 758763113
    0x120a020105160f2301150501090e060a03050a0302150f011401230313020120030322081602100c020102071a0f03010303020d0f051c05040201030222150c02030a 70
    0x16000d180400b151045a82c0c90740600702c244e00c00018400b0102c1900081c0300024414188080d0b00307a010140114244000a02041810710990b0801c80c100d80c00a940f0b80c40b00d059800c0115400b208032800755031180340c040e4450341020400402c0c0300c00360300001ea5070b400c03401d00035049541c14401c0310b0740e519032000112600242408943c01000d0030903094508041900000d5205400e641d08451800c94079100040240c04c0c00844002202980e50808080e503a0102c1100c0c1c015410148070043e00180d5440b00c040b850311010060300704c0034045901c09c3e5140a034119a45800d10842c1d4110405104034801d440182503102c000e401640250420311003011840901000b5400c07142c411402d10703050340700808442d8000d03041180143c0000e0042000582c001c660403d00b288076007005410000d4083d01101440061403185503001d480300040b8056900070390444018002c0792010303810700b0101194503040d5080900c10300000e040030310400c00c2c1183c455101221442e90060107401120103076101c401d459 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758765593 1250 758764343 758764387
    0xf1b07020907110d03051501050304050d0f141602011b1a151509041b0f2016050f150d090204150602011e110a080c16080405120a020105 60
    0x202441142600f070038001081401c55115070b942d03000c149481d0142c280c2c61910340080341141481700510a02c00045d0000c144c044000b4000c3c500380f14000f0009604640022441d200900040000131b20800c1d40541002d840039000c1c000e880f000c8814101c540040d00d100c802d42805040c4040c10351000700a0210200c140d90044000720050303200380c554100150350004101a400c4034040c001850581b00d080c81c1c0101c14000091400b01c807110304841d82c010345400c0300701508008006410018010800e40740b4a40955203100b0812519001034043e41180d00060710300480b4895003c40f4099203152900c0201440c0c01190301c1c400606200140c800c2e080035004141c012a0300a480d4001c0048003030000040000421040e4000301c1c1c5607011001170381c011a01c6100d07090545040403031a80443c021a02115050307105031038127070101d030f4400381c00e00c0441c01003002801e9102110640281841481805002a40c1c01160f0301003903c9480301800303070355202c0340d60020b0101e04180540750401c1d01e045914400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758766843 1250 758765593 758765597
    0xc150a0605031630110a09020a11010b03010b03070315060801020f18011e0503040309091a0a08010c08010e0a06050603100914090318010311040e0f1b07020907 70
    0x510345400020f07081451070901000060b00a00b020032103500c1c60903940708a240901c0c0c02c0c500c041e0514007180007160304010060031890040c0d9403038940d9100e2811000041c43d62610864075001041c50043c01050381e450300c1c4400390300303154502c800743c5018407c1902c1c5200040c0213100aa1456172100303031141203805414415990380300002202c1c00280020901d921100341c141c0c2d5900340170004004800c482da81620b041003800700180c1840c030094043c1c0d49a01d2440c0c207125403aa034451408481c0b1002c141c000c1d20b455814900b4101c0281010740105d10404400c071201070350a9180c80c08a42201c01121101e00099241070040000040d10b1100e00d802051a0300e0114506481c0c40200e01036900030b68200d10960100b10040081c80300601c100e0318030082403a8085d186040c030451007a5070303006802408406407070300300e00c0407803d81c043c0d80520ba15210344500152120742d2024680c1c000c220403940301000b0790806c4001420781c00ca648411200c500900c54007400d00710207409000c0c0700d2400904800c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758768093 1250 758766843 758766851
    0xc21020f0304050a0b010f03030804081606240902120103141011091503131509140604060b0603040f06090804090e0c0a090c0e04090f02090106020c01090b0c150a 71
    0x500e051540d402103106500800c020820340c5524541308a100e80140d00007010340001c3c030130501c00245c2c0090983e40180e004030f181615018080c140b00300a08904800404203880c110645210b0080301809480b8042e94511020300d00782c1c2c0d01ca00100782e12401c503d4a000d40c0d54400144001402c403580301d884101c1c1c0740c04807104510f0a00102c821985603001241c013103100070400e5400c624108840060b070600a00700d03039045003030103c00ca151000c280c1e0030040202d00e40d440682060041a071000c0540c9401404e0030b1a1401810700c415280c2c203080e102550b007141401050308450421008403402a030b03000b070701d0441001c03160326440c0c02407011000817684840c08200c0040c902002d8090030040c42c05c0f90000d0881003041100304802d80303c103135000b240e1043c148500c1712003080c1c1003e440300345c01c601560045a001071501e40300c0804480850000d501241c03003000400c065600084001c0f02e03140a0b2190811951111100007039406501d81c203203101e600580c02d28901c5502d070103503a5003210b04488049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758769343 1250 758768093 758768107
    0x30509240a2d0c030b031e0f0114100e0622200a030b090c0d020711100c0b1b03041416080a1106093a240c2102 49
    0xc4090719110310080070903410741c0300c101c20740b841c03a03c9802c00c8140941000c0003165442d0002c42c0d00c440d040d580c0b001403410a0320300300c0501c034014441c01c1c40844100300200003251000c101000b2185042e24a070700c44400b2100b020075000f120031680c0b4002c501c01800466410983e081c0c514000f03009071510003803162612500d20401500c9035000f01000d101162058071080a01002000c50311040c901503c6110034505000b00d40c000001140c5250b183c10740c0150341c615140c00c01c070130140e0070484440c1d003000d0102603000010f5440b0b0035404200784038003d030900c1d9440c0c41031110340402603607601e5440004104013060000e1b60325040d0802c0b081c03c1d402030f1081d120029807000312000c8503031700420098014030f00305030400c4607600c10b1000b03040003111781a0600c0703041400728480b4102d110000f00380c2405602910301c500c00c1808284031308500050110030f4a41240750800940340030004082c1282d840741c8460300ca01d905400f50b00d02c0741071140d6940002961480201c080c01560b10a05116103500708048 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758770593 1250 758769343 758769371
    0x9090703021e01020f07060e01110f0307060203010e1510050702030a02120d030b0109210f0b1003030807030203160f0903051b03060105100504090c050c0a06050601030509240a 77
    0xa0001001c504020408010b58a00181c248402d44c1c0e600386981d08240c2050143d25000f0130002c80c1088286801900c5803001c4a0451420749080502c41c81440302003082ca08004040d0003c5040c1c1e00310b81c1841445464028800c00010341e07010240e030303002c10304000c121002c1d031245029051080c0020308490030914036401080303945805032846031542e080071100c506956098054090030074028604445d03c285050300000601c00c032194000c0800401d183c02c541404002078100340583d40052907031800b82800301801c85400000d00c0210040782d43c520000d038803903000348262842405068003100114600c0750f421640c0806002c0e00b02c0910191400c003001194081200c081e4030943c1102c0b001a00801004041c5400c005034840c0d44104401990f07050070355808010349044603c40c0201081980785180180e8281c001c2502d8507441d0710416080038244036064004500032242078800300001e84030190760359140c174601803200c15004401c11a40c000c000d0703540d980c0d0b80d01030513000002480c00301d41a20b03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758771843 1250 758770593 758770609
    0xb0c04090216050607020a0b16110304120b072d0302040b0c1b0d05100509010b12030901120614010e030a0803271506090403030e030408030d110405010e0909070302 72
    0x200050201805902c80e08100040142e990454564001010210f41d15540c03000300c0c4030028000c0040160496160304064003e034a0501110313070300c00507280c58a4540c810514118900c940540e5030245850210740036500030010700106001030031380c400c203000c2008135101040f5112a150000c04d64200000680c04840002510070080c1200c00303843c0340b130600100d00041e640c0035046180f180c2c8404085000041000031020040c0407908408200c0d0760f07402e03d010b0b004248003200203400501c070005c10000f0450210080c000004240c84040070119500d00e03103001c0759401c1c0541d00d0694400c04031054290301130721082c9201e0301e00408a40084003142c2c0c1c0d41040703403c280c403a40b1a040d00d0f041d02d0300344410326804015042c0c401100800101108010140c288407028124070b0041c81107074041402d05220b50424a070070707585242181e50320361755040020303600e52120a04034080c80c6400800651401400225411684143d4880840342c1104c0c0412003c01c0c0080c00341d98461089990000c0149c6039004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758773093 1250 758771843 758771857
    0x10c0209010f0f050402030705270a1820090105220803091203070b152404170a02090f060a1d041401090c210501060e061207030305070b0c040902 64
    0x225030805883c100840d080e5001c1d9411940c4114018800c1040d2140d20005403004505a40c02009481d00c6000b1002010500800807a400c01135612001c51003644c40040000b652000c0c140803c8981060b00130802010814505258400310400c944192588224094074220350042d45000400305004480c0b28400b00c2d070380c0025031542010958030300601c1c00740d03040c82400d54550060752604a00781d46500544000820710380040c070700f0360f4200341d0b65141c0400c40c1c48845a501321856011421003880b8a19401034490411036503002e1400e0780e00304c1c02c041441c1d0300042c1e001d0040210358881140780542100000d22458100c054001d0001d0a04684d08044561503050b00642e1020305190402d452454043c2c0c1c90300195a06001c5820000b85c895404030007150b031102440e2540b07260b4104a100d0072240310304050001c0d800c0140c0440c0ca0040310400500400c02192413031514038920b08860386481c2a4840500402d03004e009150109002800881d4480d084ca04a03d14050720349000c5012600504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758774343 1250 758773093 758773109
    0xd0212010906170a03140304150c0e03071a0f0c0a051b0906040605030604030e13020c15100b041202030307081c0f0203160c080706111c14010303030902010c020901 72
    0x10104002c01004541041580683d09014000d081c0740c80c0c4000e13000106001c02d040c144103001000030300380302c0036101d06081a0303c0f0080a0085101802c13000302054602040c1c14440e019005000a000300081003620061003048403680c140b041030071950240f0340000c000e5070a5802046980e03000103d06100108104140c14900f0000031a4039043c0101040020881d90140c3d103880ca0502242c2d40005141d0780c01a032501d0925040405400440c115004580000c902d007400407880724100000840e800111180300301030004542ea990307034000030400c920300c500503c042d400c0009004c012007082280000a001900b224030304000d0350b85200b640e51001441400741da000c24030031810a206406424004c4026450940c00c50a2642140c031050081443c0c007028441440c61020401406da019203044036080b400410140d2260604408958003000000c100c07004401035001d0318403e40d01c14281240f4006205c0c00880e0700f9503400760020061440d05130705009000e01001d005030350300300c4a1400b83c0300c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758775593 1250 758774343 758774351
    0x2090106080403030c0305041a0a0914072c0601080702071e06020c1806010f09030f050a02150a020d050702060c0d0915030e0322080d030504030816080c0d02120109 72
    0x15090013070440e030702180c0c2507041500384014400400c00c0d0103c032284454070b040d26000540c42d100032180080a1681005020340c8152149000d400804944881251800c10030040310000100341158041540c803117952441c00e820000c04c101d54801c0031410b81c06640750045070f04940e10780c46100c40000380303551001b030846011002448101d0303040c4546031b02c40c8406c1e1903018076800904040f40b02000014001410448844098100244946074420081d500308040c600c9840070340c20304076158446c041f0164007030b08144a480035500055812690804620703405808200b081c110202d8043c0d0022000341e910803c140100c00d01c0c6c00302404203400c80d032195100d81e0301c244d182c035203910b0000e20a02008001d140c90640d08007105240801181c2c00c5070441c0194001d0490300f0341e0061164800c80c0c120f10403920849400aa100b03425510203800796010352600340349541c0c0c04808040401144440600048017080880c0301c00a01c88080c0c5400755400d0130150800c001b200310605004d800f40d100c036070f5140e19 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758776843 1250 758775593 758775601
    0x115050c16150215010b0a140c1c0503101202010e040f0501030b18120703170103060f0501050904120e040209030a0506010317090a170307020604060315051c02040b0d0209010608 78
    0x10280d0990360190300e0000d0400703113180c0710042e02c0010701441805074410000400000c464442c401d0f1800c08500402e07520385511750482a1a5a40d58560100342c031640b4140c1e034204041e000b6001d0382d1241d0105401c40c0d8150307043c80d1943c902ca240440e8100c5c148451000b00c50100c0d500d5008010354602101400140e81d8914200a091200e010303003090046482c54607d0645030f0404103c070344005d40c6040c1d000307513140080d10b01119522040e942e619030840d19100044200415600150080604e50f0014010790743c0700c1c41045110181034800504c92442c0c11880305480d80100c20110b600100208010b090440070f401207804c05c0092501183e107500000d0040c4100040f020741001c008031406070003030a2a00450110315654514080c144076843d240d500580c03a080b0800c11128030681c007030880d940790760b5100c4000d4040c02d251280d0400c1300c11000340120300b40c1020b41c119481e00d01d100e001510104020303001d000c000c0031000b00c4e40703402c007460a0440002d6102c2d540d10b54000e201c141c0e545901468 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758778093 1250 758776843 758776859
    0x34061b0e36130210080c0403020d0c0506070b0115090e0604050a1b020d08090604050a08030c0c07090c110a02090106030f2003090609060c0d112205120309090115050c16 74
    0x101409204c02c0c090040207110500e50440140c07400e0b2036054550040c0007140f030420b4402201598880b50780020700084900400018890150490305251010b0144426180056400200740d006810004c210440000d0042c6083d07008681c010300c400c0d00c00900800047d00e0300c0d402c581c03a4070640d00541d1020390b0080c400e540c07100030150b010688a014264a04099a88a07100d10350008083d0841001101045048a01d08112100315403010212030f5402e56170201a8082c101e18900d0710007046100000c815005001b141c1001701a178002c1441640381e00f0504154001d048000580314075170b550368600c24800c000705240c3d03031a0703d500320030094680c60001800b80c68802c2c02010505a81c01c00824014544240f0f001c2e540903166104e00810305e0700c0034162540d050b01500007245900300f85042c0c21031403141c920030400306442060300c0c03018401025a8030a030780c82c4216103003d40c001c3d08060040218403500700996401a10740e261603450a5070b50b404091400c043c0016510030070a1521003041305403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758779343 1250 758778093 758778109
    0x50a0c0c0e10050901080303132d0b06030a0b220b0405100501080d020c271003140106050a03080d150315051005010534061b0e361302 59
    0xf40c211034620701c56060038a0952240000741c00340c00114100c1b4964420000fa000341304031180469101108040c030240e00c0c0c107801c01c40211065070014500b401050740b50a000c80d03160312254110340170a1094039900320f075100711030044d141108140c5d038035840e4500007901a21001d02030350041c4000c203031030003d9459900480302c040c0d001c1c64090703110158003800b80341c0118a8010081040b5a1218841d08914031030f10300c600001e603994084c0820701d04000c002819000a2004c3da402107405200c0c209490442608985542c00b48035406643d56104100007070041e4003c00c0001280440031412503484010007000c042241c1040303c20718880c140000c4081c0091140607802004181401c420600e4040040c29070701c21401c86840721040c1d04002d03004209007a004000d8825030181e6221250620304290380200941604820601140d040d1917a900d07110310071642446030002e00141c2c0d4a250300761202401e80d01d05480c21620002005003140b008c44550806105450030741c1c400c0d480d080c0c00e2040203561 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758780593 1250 758779343 758779349
    0x210a11090106170c0a12051905150102070e0406020c0607020f1c080117010908041202010e0a060917010f02131d0709050411070b0406021209030a0f050a0c0c0e10 71
    0x1d003d075690a004110f0000e029040f4071003004556481200c1c1d00111100d24942c2d03040b0001c40d0030f08040c840c2078241c000300d03140d001c80362a100b0002a06e0300d400c92419005921145401680026414040d0005103c1c003e60440c0c41548010300d800c09081130b441c1800c00854241015030000c02040030030b00e409102c4800d40c82c403120800722071881c140f00050024101030142846140e82c1074103802c074100c000d5000031425034010b50840d840c3c999a0568a0301e014600104030300249040303141a0040c2059100c2006641c9262100c20b242c5041242c1e45440d006260308a010540d00e89400c0307501605103100030448200001c8004000d00e080600b59032801c0c3d12030ba4100c0007011342200b001040c640c444403010036034504480c0803500ca41090010886070098402c090311200380c950510003085650340c0200310341c6610248107001d959452101a03140d000d00c20206011038113000d050052184500000c00ea10310950030984040c254988907441d007141d0342d400ca42001d08205d4140543c802100e4016002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758781843 1250 758780593 758780597
    0xa060302030c0a0e0310050108030310090e0a0b0709090c090501031a0102100c02010b031f0c02060903030a05270106091802011b06021b032d09210a11090106 69
    0xa5801e0020002c0b229120381540ca4003007081c400c884440340d5030140901e000907280103c05010550b11005c0b02c49e221fa01c107440310070f0303030500303011000071924083e000e52080c00386002e01404404146880f40391603020020281c10402120180126480d0483c0c400d4102142541d55a00350113130608002400301ca6103190942d501480a042198003070ba0300081c04882c46500b160040b0300b0790f1030848160b01410070102007a0745130040f83d82115480b0003003488050b00d405480c000740708043c0512010b0b41ca40c0000d480f46481c0c0e40080000403050340303a9400142d00310b4401200080f1400c04803500008980389000c030b10b120b030394613000704000243d0103024954650003910b11108203103070144d00103400c0140f812054a00d1051010805051103190703070650700074005418003050909030a03000c0f40c0c0c0360390000e0200310303244102044240c42d0107c1d01e1141c001c9101c00710b0440d4900b150040400010001050b00102183c0d044010295010014080c070b50f10a842850b10724a258400406c029146905804c0801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758783093 1250 758781843 758781847
    0xd02031b0625110a050f0f040615210e0a0f020a0312050309160501020c01031a090106020706030e01110f03101809031e0c03050f07020307060c05100e10020d1404060b0a060302 77
    0x4210b550b00d1b80881d414001c01c4070041380c411601004540640b01503885628400303000705900b0070391074100c403e00c801d1116100c995403108444504184c229050143c0c101029440301001c080010b642840c54130034180010140680c0694907581c404500c446010503400259020080c084800c4082002e5440307942c807410b0443c009414040000e41d107a2001c083d441c101900c0700b01142024490002941b20480081c00d90051581c40b400081e59480c12440380e1000a031408040c1c840300101845640401c0c0000020646030080320003070180c00c0d4002a00014200307295480000e8040500f1030302c4604e83c2d444440100b47d208a80c1800b13031030182c440d000c80050310002c40f00d4110040d03100740c150300d0055150801b00e0321054800e900c0c9055000e64040250540300d002c8004c10000c0d080a2140700c3e041c420760440c0c48000c4542044400e0300c188d00e0380e01c0030b00d40c064401011000c4894002c1d228a4100550004400d50800d91075164034406950680e1150350300d201148103802c1c4000e01002403c42803c5c294 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758784343 1250 758783093 758783099
    0x1e0902010509040b040204052e02030f07030c0305161b06030b0616053a0309121d18060405060d0c15050408100c0801050d02031b0625110a 61
    0x18001e44509400a840f4655441d03206183e80d43c0d43d41a60007030305001c1d00c011017046010040d03116045500c0e0510010445051083c238941d0b00c008120b4080e070340c9100040b810584a42c1d000e4402140f900310480c00c1c80400c1c05820940b10300c3d15105034001c0e0240800b080011404500004034004641081080604140800319a0f032161b030101c40c140c4c4c4047d9545e00782550503050480c01c0c10200c0b20001802072400607902c5e92086100005640b00c0400c1800b0f030040d2003002815811208403040c014195042112440341c4a4000d6000503028802d0115240403018084009511000005114588810800148003003824984146580603d0695545012001c01e0b00c0e0721950040302c0c40345000d015824100000d0a40c814000d4500800f0402c040341e19841240350780801030300140c1c2603140040c000c41c000007818500864201070b41c54018010b4543c20342c01105d4040b46111502c4030f150000000c01180e01100280d03040b407400400c912091480941d1769286c0050b0355040d0045203807050348140000c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758785593 1250 758784343 758784347
    0x411070c0311120d050c100b010e0919290301050601050708090f04050702060a1a0a180e0d0203030405120f0f16020a0f170a082703060a1e090201 64
    0x1100c150394114030056003041580700003514082001c100d00c012401101c00112011340c02a01400822034170106994400c06801c0d03103001101c01844280340090350440c060340250800040d1103801c07403034404800740da60315140072a03004e40c2c3e0514407810b01c1044074200801101c50310001484090070450082c020340c101080000c280d4014074a01820403440040e40d42850755441c01300703030140d0502420501051400540103922190700300c441000480c20002089000e07142251010040700300284101ea11720b090010101c01c040d0707090501e100281d610102d403043c000f01004000d03444051603009507640d10701450003604100900300007406c0704000f840034860700c0c0d1030a4241d50340000d8034a00f69455907c1805001d010305a07109020703400000081e808101e08070b4100d10346013034403a02e0306680c4003081101556507a61264850107040c20380140b0011949482200c03030500e0b1313244480070141c1036012400005e03040c000181c80c161020380d900c0b13000360481c13211540f0b1040002e0480c0e2042040106039000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758786843 1250 758785593 758785613
    0x106080612030909010e25050f09030a02120a1b060903140c0405040b09010e0a0206160f0606060f0905030c0a030605100801090501090201021c090b0f0c0318041107 72
    0x9061203400141c000c01c00c8581c04005035a0984001018540f00f541c2d2400d144180c00420b807800c5164441400600152107842d1007a0702d403400f115591103103072510307001f036150058104208960b418015080c003440942c3c2c07407030380e8140105481806000401164a06041d40f00ea1400c5400302201d0000c0702080880d40000564084036003101113041483c07218049181403410903204d20ba4481d00d000140400d00450410843c49284000020400c14098061107541c0b01448480207600201c100300c1000c82d801101005008c1502c202440c007060354081e61042d05840090300810300003001c041c01140020b5210581c000101000e0b405030a041c1c9652010803400d407040e0201400180c2c4640c003140f00e100c0354081d00380050a8000c0204000156441c1050181c6440c040c185c2c014801c404103292520256038202209110503103030014000d1030401039145070b801a030002280360724140a0300704405800d100904007056060600070b080c9846030200002c540b44c100480c5c1005a00384035601c00a180030305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758788093 1250 758786843 758786851
    0x6080f01090c0504090e0d0e0114183c0f030a0b0919030903060609050906041502090d050109032007060302090a0b160b061c020f0f10050a020114010608 67
    0x1c80442c0c0000920010382d4203204a51180e15003503e000c003903a00d001408500341145000c82e80d82c201c4406100c0c0011100c0030903a030140303444500c08201c1c95050050380d029660013084080c0c2641e41801c0d0b603220344504401110340c83d4210308018a0707030400700551030340c40c000c080c20101d0b8040707907002e12000440c0e81e07204010001000c0030039820100b50800010081020140741c200001c642e0b885131441c0081000302644011941076007005408144a4418000e031807003141d00301c00070b02d01c50380c80c5d80762003402400d081c1c910811554204140130f116110340c100d42c1e007850b0180001242ca02e00300d01e001040c50049083c900e0701005096820031a1035004100d0200301d03100382c0740260700c40a41d480000c1e09018168894600c81c000000c001c1c1c1f104a40648101c0c80d140107070711a502075034404043c44548410f507030b68011120134004c0703800010711344020081d164403c09048011085512004900e1100b002e40f45900400c0021860345500e5a090007070661000c00c811020066514119000d8880d07000a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758789343 1250 758788093 758788109
    0xe0403030504030e0306010603020706061208120c04032102241302030f03070302010506090901020c0c041107020a0b04081e120307140310060f030219030e15190606080f01 75
    0x4008541070500c50600d84045134001010350b005560f48d60340c040d000394810a01115540d040003000a9902e500942c60044942c02105c4a80340202e40c1d000b6025171039008000f0700340410107100110218412000513181702412101906c008c10140c100645004d0215a441800500e00c1000d1002d005404081d19006002103c42c03401d2a1650b01c0040d003070100e03080e2800c000f84408540a41415415003009005072810303242c0c1c5900d511b80031191403e03881400d013a03551079402980d01b004642055800300e044110903401d480c0c00c1800f03581c001070103030103a40c0c88070f00c5011000c5001d105100d0103100c46003001d460b00008503d02400440050345a205d00c1d204054181c0000c0001495140901300c0b41c003582c0c1d40d1030350403a501d24050303010142d000c0090042e94001500c0744006401180244201c0d01c00071282d500101c00c005072070704102c002d1321030102c40d00014068404024803030441044168025200300c0e80002c0880f081034010800c84450743e104c6002c001c2864240284401507040190640d100e81d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758790593 1250 758789343 758789351
    0x12071a090a030e1003110304050601090b060301030b160c080c060709140f0d031b03030c0e06032203120f020706150f03030c1b0305060a11040810020d0908072108010e040303 76
    0x4200150001c001b004500c000c0c42d000001048100030020a081e4141c400303641040004410361000d1024030702003404001c040b41001d4011400903041c203580003d81003424917003c502945c1d260784501842d0483c0c1046911644000184401d65030804e4041c4050310300c1c098400610b590306000a40500b150a084900522440020005142c82120304405801480610344a98801403800400400e09030a4240004240484d609034034900a400c0300d006e455001203400103e1190303884800d113568251070032024803140382e29000d96a03245001d0040180104900103132a00c4550801000383ea21460400ea0000c5218a00707110289540c1e00c14007d4a405d4602501c8100c090b2802000790890110082c407004030712100041003040008003548206032000c400d000c0d003140303c004454180514043e0001c260405a05c200805c1000e5019000d0202c107900d012a20b103000b0780ba00c81007940070481c25140d050348510000d0074050f60820700c0c1c10303501440c5001c0078030b9131504d0041d40280c140600700a082580b2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758791843 1250 758790593 758790619
    0xa021e0a0f05030d06231c1401021c061d07050705060a020405100c0221010f24060e15031e0117150f010e0912071a090a030e 55
    0x8104506401507510101501c104400c0303090040c0c0d03a4000f40c1c00160883d040c0440420340814901e03042100d8400c0000011401e1014030400c00294030b0f00000d10071060644800c8000303c0c0600203541905225070000580c1c55440c2d001080f5101c5082071034220460418004100400340070600181d815200c003035130034590710703008400c50f807511a048028006120b21002d001840d06650700902c200e480444110b001d401c40d004040d14044500c1002035840040d13800c1440000d01e48036000c4040224003c0000f0702d4448204100040b58030040c4205046400e20090f1024464503d6001d0301034610743c1814007184140300001601825030303000c0c812640e032010001c2420010000900f0095204285241c0031a40e114290680800090f42040d50144240e0034040d421aa80f0b40c0110b000d60011000616940e0900401c680546405440340105114208200e02c401080c8405051800d01c1000705e05441924414000d1001c03602824565054103c82d00310310010b80c00c0905c002d01c924040e0f44501030419 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758793093 1250 758791843 758791903
    0xf0e1e280c030302060601090e040c031103120304110306010e0408030703150e150406090b01050403022803050d09061715010918020d060b030708190912050c120a02 72
    0x4440c00000380081c000e494040105500410074500c0f580e002c3c2c0e01d031078110741d0f900030000300400300b07a13005400030100034810f00c040b030791000340c050760024054100c0d1504281089000380e01c1e03008403400c0d40d44801c104840450707868140400b034018006500300f00e120b400c194551003402c1c4005401e4a0a16a44104c0d040039a03001e40c44c040b000340f104034800a02c501d03100c2c50410510b00c6904546200b20301e48240800d069000d846501446207040e5551403e01d41140d090004e50006c1c0301210b502111403000d42c0c045600111456805503101e58041d104181c0c001074090010110340d00441c05000312007460100080380700d0011a840000e00e19041c3c2d0000b40a00180d800c4030b01d64015820408185075000c1c01d6116640080140035811441000740c2d42c0c0d81e44102445000035200400024403140104e44d03048889480341c80603c6948800092000c07543c1c0d00e03943d0710612058198080340c004503400c80d80305018050300c9620780003c54418070703207544e4100080d00ca503001069440031416080301c01084035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758794343 1250 758793093 758793163
    0x20d030b180703151a04090f020c1603210e131b0201020c0c270a0e030a0c02010f0306060203030a1d0a210e0a031709040f0e1e 56
    0x62511031400070038240280700401810a03002e00e540c8540001000150040382c0009003518900c5440000381802d090480c07600141001000c0c07010a5a000d10602030503003024080003400414010400300954078603c0d0241c860518001c9a4510b190344074241141150042d030842d440b00c3c411503800d000000350801c0c2c10000d1140c104400d041036a403501e05802107805500030801401400c04507003820814008010044190041940540c0190122551a0b10080e80203503008842d00c80c01080b44c1820502d02480e58024504510004002140880c10365800c4074a10030710323466514052014034149100650740380f0020780181000360b0307202c4808090803c203a41416100400c1400e652100803242001d80c0e04130154003006900c0748226a600003050b004824400000300050800c914851550b12040c1c4c440709c401030200308030072081100101d1642e8600ca060340c0400c08174000141c0484004020389454440c5000801c4682c2010302501d488030000303030f00c0d1008403080001110400d10341045035200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758795593 1250 758794343 758794369
    0x10050d05040c050f03030f09010804030219060f050f040b0c0903010f0525110607030b0103060902030709080c010306230109050a030609110907050a0f02190506011d0601020d030b 78
    0x45403416090204010080510300304840045800710218007062040580324851140041800642004207800c03e500500c0ca285d44103000e40145d41d100c0940b41804140c1d08449181241c07596684c40074110f21146c07910566411544554214810389050764600c40c0150020304443d145c09000324120940399000d400c20a14550030031018086400c7c0b45041404032042c0e41c5120052000700103282040038400e0108007038021012004041686038810140c008010545480d0304050302c4072404180c601d56400118081c2c0810741e2080e03805403510180c5402c000740c000d5854101030401600b0051600d01040b45090a9080316141804540900040c3e841c00c110707134002a044408644000f007070110542c00300a4250203a04c03c42030403407070403040220300d25003243d000d4041801400300c0d0214510410b4000200740950044400b0220700c0f000c10380000c6c44c103480440d00c0c7d9000c3d80040c054035000f000705e0007810a000702200c0007410500300103911030040001038401c1594907041038001d030b5101003800b001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758796843 1250 758795593 758795617
    0x31605060d0938130309032603090c03100606090504021303050f061f0609060809150901020c1203100b070c120303021902060105031b0d020301020d020910050702060301051005 77
    0x440502108407810f800001410000c04402000809990b8184d05a440b660340c51741d00c807581315055903180070344014040480c100c15000400c0d81622001980005d50081420500a086070358040040501d401920b02c101c1c6041420503008100d295003281110f010750741c00710740158880c080165030082040d0b09074800751043c403801c904219170040103c1d03411702420f881d1540502c1c901001c11120b08101b100d20804002400c118010412a44110702680e0402001401d590484c101d05490090110040c0c82c5005203943c00a003003003452004224400c580e214170403d19080d40303018180041d90007081e00c00e84503408000121300040200038041803026250402900d404000503040007070081d040110210703c84029030340c486000b1800000c0c0d142c12618001e004101911001500c1c0480d280220b080c150002580c05502006a80a0001c1c04a07070004060068584850404001d074501001100e00d0a100d009c02141003d44c80303400489041da50706844401c0c4402e9031103800c80d0b05105100c0300c1c0c0c803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758798093 1250 758796843 758796893
    0xf09090c0228031103160201050a020120040f09150b0f0c0105010f090e0a050a0618080d14010b0a0e0108220c051f1b0201050417010506031605060d09 66
    0x91200720b251020301d424001c0c1d07620003c1880ca0600240c0c1c92041c0358074104404070b00515400150701c100020035200e0758500c008280202c0c00d45c1100745031041d07140804115880480e041c08900860610a4001c02041d00d06100c3d0f40b079444003001c10740305540500101d16200103200d080c2c140c3c600c0100c500c2e40390b41c0d000800c50396079280130702d00030241c003400340300d4005040c03030761b40c0300c10150001c1e50013403d54112000d8012040300390f0f034076402022144d1a400d04440c440c001040818210300240810032042000403440082c03c3d401d015200c50160801d03140454140b00c12070103103500070289042d80d0b20a0900390f0907030703c030392300d0387c54072080c02c85e0f0b120310550b0f25145100c04210060038101c0c1103d10a5070810843e80c0c034103d10584400103a40c0c408002100c41d8107080c4985071140400030800d0040c10064a032603160740c0792040401d105008000c20360f450710b0901019080402044554013081e195489003641001c0005505100e800c40018a49031166140b4050001c01040b10150742c0b01c0400c1c0c59 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758799343 1250 758798093 758798143
    0x2f120106080105011704080a0305041b14030105010602060705190302041a0702010e1e2124010e10090b0f191802090a03021e06070606030506070f09090c02 68
    0xd01c24602405080d00294804141e440710700300188501e801540e01542003810190845030850040a00500139266001181d0305100d02041c03100b200000b0301034503081c0c1001b00c01600300745801e542040c0c0c0030404540c0301900300480c0c41d51041c00e684c03040030942c0519448842c0703480c0841c0a8082c80c2c2045034603404140190100a00c090001e10129200380c0b180241c1e0f40e40c0a0421801d400e00c000f544241841010540d001e82c50300080321100c942d85205a0b004512000d1003aa1826091130115240c5981d038080d900e8004600c01500750050070700c0c0c40021050300e003003116580700008c00c0c86009202903e904034403403642d0341c111054580940c00f4290803440c081c054080d2403000d9240c46030103000d4034441c00da42c54200380d40c002c5440600300900344804003440c40d030074000320f2f40c0300d600c1091045210480780d5200b50396007401881041e00805000c1203070350031410040e0900350b0182191050090300841c5548064012140d44102c030f01e510380004100c080320300c0680c2040c0d50a8042e01e080c0068500c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758800593 1250 758799343 758799347
    0xc17210c0d0801291b10060f0302130c140306120f16052b020a030623060103020304051b03120408030d11040b07150e0a0605040303050a2f120106 64
    0x2c107040301c0001c4402c080700e100020702c28281c506808103000c1c141400300414045071000d948400b41400c685c8003100c4c480100741400b10b0403102143c0001503140d410000402c103529081e01440c0384e46071780c4401044141034541c005441d0000740503000708840030200001e00556030310700c1610031030703d000e6081d9003c80d6034a01c0c1e03007902c03507680100c00010240e00c0b400c0419035080101c6811240f0340100c4400d480a41070f1244070741604c007039074004c0b80e22800c903100c0440003525500988010a0b10401d000054000d03c000c401c030300040c020a0141010b2040c010880800d40c001a80c0750915285844444800203030300100b410488208520160f44100180004803003000000074074041182e00c40810058400c8001c040280c0f140380302d000c07410700042c0003820101c0d064404605900e5031760440003440c800074900d05800c04507000400d0b03869550b10410401419094011f896110707c007002e08111151081d0107226140c2c001c0d80703000d07400348400310700d170040140c45408486e42c0f480348180318660381d81c0d66000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758801843 1250 758800593 758800607
    0x18050d020a170a0209310512190f031e0c020309061c05090309010c06020f04090903030905061513051506270301020421030201110d090c17210c0d 64
    0x700703e005145c601d00088910603009561065001030b1640308191072109481514902c01410041c2d0b00c9004424000880e0759508000b4584039200d030100b800307000303200d02000d00842e4130012101c050604011107403400d01400004c8805200703100b1000260030b4000c8800f01c1c82c42c0a0700c540103400100008020300000d40341c8451a030040780c1c03000701340501e0765940380b059224010001084d000c035a84003408000610142c0240c92881045c4cd8182e05143e81c61910303a050f240348500c01d44c003099031340c0304a00034000c041c0041540400c110101d441581303103030000314401c1180d0364071403100c250b61900869a4618407988105100e2401070035940c82d0301074020029000125040c5a40d60551100344546180c14103009540886900d0700107030241c01d200b035030703600c0101001e003038120110356940d06240140034680300900b007190341c40b0714001803480d03040c504043c00403040d800458422050800c4805010000200c4051303190482d01d141f00701381d1202084132518000c000220030540070320b281c46020b095102c03072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758803093 1250 758801843 758801863
    0x6152107120507080106030209041203110301030303050108010c140f1c0921030b010e0f061204061b050f090f06040f15140910081806090102030405010c18050d020a17 73
    0xb40d83c2a0b90359100c0c01822280c4520000750003c1c188000100882d0483c03068441d40c03c003c0c03d003c600d0f05220340d22007606500980040f400700383e5440061100007800d07c14904080070a0815402954401d50851b007540240c1445070050700c400100110b01c1c0b0404c805000b114100d00c4e100344900c1040d4504658499105400c440c140c5004581070a0250300c40d00440c00942c8040e10356500004004092150b858000800f0303682020702003100e444565204101c1d1703445240102d00c0041c440080d1701e280141709100300100c03020080f052103006081c00918080741e0400300c044410400b19030400000c90b1590180e41d208100140400100281c4030f00d40c442d80880d0b482c080d617521020f000f075400505600b40a014810b64203d0110396514403898041d0040f25001082d100002903080e001903070507840e000c8100c4d0b00b06480d940120501c41008802d000740c0020a0503420404842520407400315011813881c82080d200d112880e4244003551105180032015101030071100f2580d05d0700703100d45075544600c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758804343 1250 758803093 758803103
    0xb1603110c100c02030a080c090a0e0405060601031506140313020a080c090703090f020906120f150915191b23030610050f040e090601080f0615210712 66
    0x81c3e80c0611051000c01164461760050b1145801602e999000e4030158200707448483d0486543c03032020a117142030020a910540c071403070080505141c4540010261000c18004000c50030258005000050b0065001000700c0e012044060304c84e80c0b5240314120303068605801a41100c503401001c910101e004c28500324800c2c0540d00e034043c546502001b20129800d044001c2c005c0c043c480304c1c4e00014034ac440c1140da00300d10001d0402c2c0501039550029414890700e210300c41c03915032042c4202d2010382c20501c1c40b158010100b0002d440001d8040343e124440100090483c00d000c0c2080c45150b288180b02d0348082c01401124000f0089840150400303014882407800816444000c2c001c03004940c0ba00d102140d00c00c002c0605031040d1801000016183e5030000304030300900c3e21341804046007222a00101d1486582c2c1c2d100280081d5260a01590a00307906c40581082078108004118465030a0300c2d80c0c2d00072010a80b10115249010030100988603540760382050140141e0340e0004481c0e078900c0700800003500030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758805593 1250 758804343 758804351
    0x414090304060e06090f04020913110408070914040b10031a01241d06040902070b0403140301030c051002150f0a111623060405030307030e0a0b1603110c10 68
    0xf81049400d01800038450b6006210130820200760415401034923040d200a44500d000c600301d00c0c00c0b0070681d140d00c00402d100760400324041000d440200f005d00010304e0110802c0113100e9502c01080750715000140017507c003d2207600819030b680074103150000115004192841c508946440181204c8428450b15030b5000c0d5000b41d002c03403d08030350140c0140d03c201b900c612401d0001100e03115110808e0080c0700345c1c029018000002c08010f43d0005003009072180c204100d652405180160150806014003008202c06000600c001580d40c408103069800490340c1581e555001003049240400214511fa02c00c6810018000700c08a0f000f20700307000710040d2a06100c0000700004d0300036540070305a0078210030003440e4500c002103a030581c064218044904000d210004221051a26000c0c041e00c040300d140e440082004001c55141c4600c02e1401d9403031026011170a5103407110300c102c00c0d018007001d040410fa211482d944500950018900034181c0f8040c9460343c41014040e0f4591901490410001b418 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758806843 1250 758805593 758805617
    0x807080f0a350411010c080711091f0311060705030a020703121706042c0709050f04110415090e0307211b060605091f0509091506041409030406 63
    0xc2d500300720344952030030404120a94031925000036400215804074184200c50002c44040b95094000300701882c010340c5281010f42040c414840070400061200da0b410082a034642001c08400d03481c0d600300d03508840c0039503802c0c0031540001c05a01c1a403800a200384400107070300e013080e40c000c03a0314003c903801100c0b08010403003068000c2e200a0049a0300038101100000080d03a00c2c51f041d8803490301070350a180220500c18140c048540310030b8289980708942d5201d5070b410032584045014165000f60740c80701c181103908182c1e44900000c0c0151030214805ca0702e42c85d0b2040541c0c456240d45006156140c070611481c2580c00d0307013580305d070b0101d00c00f61081c40c1a07000c414034680d5030840701084211242d6459141440308100300d200412916421110f59448200000c1e09903103c01205000c0c00103a0701c03150405d240140003802014040e1304c018000c80c491003c0003200b06c004105401000701d0613008032015a52640002c00800c03103082c2c00f40c51a003060b800d0040b5010000058000c1d544540c131654100d0701 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758808093 1250 758806843 758806907
    0x3010609110d090503070204020a020f060a020406080609040f170a0e030706020a0b090a082a010e060a020d1b020105040506010807080613140d02032706070807080f0a 73
    0x41c0d441e22190740c907010000003045600e0b0383d0004203030074041c0050b2820400e076540090183c3c4c0c130480417080160300033300c03040250b108148080d41e040080c8030b00071864107142107000b5048040c0208264440d2520074001818007001445610003650320011030050171141c5980c0c04001d4010402000000d44000a1007981d410005490025501e441d001401201040e903549080180000d111481e03c0c050401810300240d41207001e0820806a0104502c0e1900158500a02d141840c0b4407690f0b240c5c1040324905801e0008607885400c0142d50f0800740e600c6601561690181110141d0048000da81e482190b04466041d4030583c00344d0312920540f1070590f039680c2c41544c0d696150041055503004500400c0031030049a2408844c0303031044407041045850098094140841500b040000d600009084861805045515103440500c5010300c03005129910106005e8098403200030803803c0700090100900119006440354001004841e980d512203401005180f0000840c0b0402c0b1514180c590040f003d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758809343 1250 758808093 758808101
    0xe0115091d100b060c010c0e1320090604050303040b040f0f0b19032901030e190215190e100503071d01141611061c050403180e0603010609 61
    0x20400281485060000028020f1103460701c02076009200b0000b4101064081c020100d0b0040551502480405060306000d050780c070b60404400803500d4072048901c0303003110100c002c444034408681035403514884808680d032031103990001903042c40041000940410000010002e5845030120b203841f45681e142c60b11500c46040c0506801c008081c09885150207001e20303034000e54540c0c1c0c82d010911541003c0841c2e001e03494409511403210200801c405907503098000c00310b2070800c0c03000a10075100d15030700042c07040305910030080c41605081e5000c2880c1d0a85001d6504c0e00381c011400008216428802a00e10382c0d0f20104a030050360304020725541346010703005484c032400098850b410009514074400010181880310641030050803425002001c5441000c1c00d030103225060940302006060504001480500e28801e118000401858150801d610f00341d58002c925a040480c2c20340303440c942919400444a0b0101407001501c1c0c00080c0545009807880c050001039008004051325404403400b56 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758810593 1250 758809343 758809391
    0x1150302040b0a0e0a030804080105180c03070611010f02040608150303041a1315050d0b03011b0804060b0910090c03060308090d0512070f03110d02060109020c010e011509 75
    0x482c10a0041005041c0070704142c1041810041c0220000307502c076076500200b60001d8008200aa5481e070030410002d100c1105082c0110103000180300784d50300100060b43d5008180500802c1180040011082410035003148001e0461402c0940d122929810000e0a035142207405180c1c02e40442c40d5458103050100448043d03c8880d02c100c242e584c2c0d002003130111035200c00d0800700000120440000c5680c0c440501c1004101c00f42e4550303580e91030a01e040b10a8915441805102c2c0e4580407100500054800410101c2c2c20300742403c1d80701da519070400b00000e02c1c0c442e01130b54104180e80d040000890080c94a402601e0f8803207000c01c440a010642282240c00c04d010080040c4000c21040c1046d150907010120401d110b03004550104040c0d020140c21034001500485091907141034501c02c06400c52480042d003c442001000301180c02940255101810320403c80d02c2c0c2c7d030028503840548402c2d0000701118203c1802400800e80c1160401c0c1c0c0f802c502d00c103800d0024500b0202440321940e1130380415070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758811843 1250 758810593 758810609
    0x10609050402160506040302240112120c0f050705040f05070c0215040f0f051c05030d0b040b090f04110a03080712051c05090601120f1103031b060115030204 69
    0x9164101024880298400703081c051000d071a402070400001c80c1048907038030480c03080e40540207081c4000345554888100c400800d200c000c03028010322084105071070414004c1c2c0c0103030326203201400c0c6000544210031400d5002c0c2a446440e02c039402482000149541114003d94007000032141d92000c8004403182580c000c80090414030302040580ba20b207800003000c02c0e455001524095039845400800c013055400108203000004081005181c211144001c2040c8400500212180c40e42ca9640300c0c07056980785102165a8040860a52100c0e40001c0011902a043c00c100c3c1c285a035440d1641da10072141210004221040329255003080029641100d90000030076051012903a40c48951807880c0101c0802c01409002004841c1c9021501240300d4160000004042c10403034081402c180c4160002401003801c4485000041c13070f143e400d0761000b504407128550b180c9103900004c0c150f104d00e46908040c601602840c0b0303500c1c00086083c50480f20101c1c0c446200310a40e1505409038091403246040f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758812949 1106 758811843 758811857
    0xb0c0610050405010806070c08120c0d270204270804030b101a030901060e0907091b0f0513030204091203180210030209120708060405150106 62
    0x250a081d50207100c00c0d81005c00c2255960313000707841041040744040110061007800d005a510346001c47c109100d29082c4140340340459000302c00500d01c000d00d04203201c615000c81849000c040c096000e6030301d0800f0215002c001c01040c1c0d000c8403040309200b14a1140040080d00030011603103108015a94440f421070a18000c0c10100824884680c03280ea001808a98500035140700c0d6103c46600040d900d580b85c40340e403030140c0322580c0800c958040d00b5050000c07001000c01c0b000155100c81d80c0404c040c0941241000c0c2920344039072090003141010100075006849603004224a4130341c3c010929800b0313529804102254036000c41138a000c00404540c10040e9407501480e101211002451254800c20b40c00196112a04034110014150300040c0c3d11959282d00700d90b01041c2084c901602c21b12a038600304035888a4003100c08580a01800034040c04008180000c1070503582c4581d01c4003 = true := by decide +kernel

theorem cover : BRFrame.Cov 758633093 758812949 := by
  have h0 := BRFrame.cov_init 758633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758633093 ≤ n) (h2 : n < 758812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
