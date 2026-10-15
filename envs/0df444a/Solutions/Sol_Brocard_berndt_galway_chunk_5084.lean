-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:32.369045+00:00
-- url     : https://prove2.me/submissions/0c5ea38d-6f4f-4794-bd54-89fb6c4b2325

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 914208633 ≤ n < 914388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 914209883 1250 914208633 914208637
    0x1080604230601150e0315010512120c0703020916080a020904020f0c010b010f020a050304140406050604060203071e08120702030c1e06070c03050307050304110904060212101415 78
    0x9400c40c482c05000080c07820b60500d442e500c2c2c0206990f0803424083c00401c0680320a4041f02c90030001031494010300491410f65141c4200003103040840e5a0107081c048002c40710b420616503e0340c0d0f5046024200198140307203400307a5000d2250385600300c2c00341c1d501001409054000c0c1034007030384550225021000d6107070ba030b046910390040d007a24143c851140e500c2d00c45c041c00d04032a0b4140040c0f40051003c0d41030340005003001c1d01347e601c04055420f0a0070004602c0c2920766a0090710341c01a11000001540c0d1680001000941902c2c2c5c040e5544480314107190341c1005c80503e05c1103015042c031680502041e5000162004030100740491080da072920241285103003c0c50b04403085a01521414000c000c40001980d240414020282c82055603141c00642e441045804003401150040001605080c41240119031207846001a076110300700d0301010460103601220102c54450b03000501d0304c0e01020113800c055100c548002070644d0681442d004a2001c03810300c0007607002d1103ca1320400710b000e00001c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 914211133 1250 914209883 914209943
    0x20f0a030f1103040807021302041a030405010b1c060501141c11090a1505100e090403020724083304140901020a080f0f0601140c0708010b010e0102010501080604 71
    0x902ca03912410301e814116803076840100101d03c01c3d40d9070b042c0303c4205161402590100d1b0702c10400d00c1107031080c20240c1c46295000610446195584403060702a5a882140848501f070070240940500c820301c1c50110212101038200c05141c941140f41d203419903490214104095025108040c4560054500300e515612030000b69503000c041c0200b00040d0310200e80c802d800c510fa404c1d161074034a5680c0e4003070101d400c1c003090380c0c04000703492091322085c5070910075402600684a40f04070307001140d4602c032001c0d10a901243c0b61a41c442555001c00e43c0b03c3d40a554a500700103102d601c1000d00c000c0320b00804084000901045c96416400d111904940d525808150140c0051004000d2454071a003003034002c1d40302c09906004601c0c0d2001103900d900030320811a10031026985021866116000195014600650030003600c000400c46c1d000c2c524024400348004042500020540d1104640007421808031004d0407411680f40c44010840084009981c2c1d4000b604040754070105c0e4400e00290000200b444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 914212383 1250 914211133 914211161
    0x60a0f110a03020c0117040215130308030c090a080d12150306020c060105041103010e1909020315060112110412110a0f21081c02091e0a09020f0a030f 66
    0x4038030740e0030301d40c01050f0340a800303d0907600c03426803a2803020525200807040e100a50032980b4412601500000c01c00107091101e010547d08140540c4c980d00c1110351352089480b80010a030114a40e8a54101070f080c030b00180c011030001d0f0880d41700da0b10004080740810348120460703a031540317000300b01007103034521201c00342da0064425035886200601342c580e030721800e10543e13005034a05000e00900c40005425203042c2c072015540c0b900345450368080380b0788140c00d002209955940c0c80c03410f0301c0140d0701005600c01e00000144001400c0c078052002501c04100f140312090400d08103001c0c1840300f04070900311425070b6030303600007ca000d081d641028281d0700b601c0d442c2c030394000c84e803420041000d40c07c03440000d003100c2d5072072210030002000c464481c07680c1040c250008c100800a0104801e82c6040310b43d22580c04001c220700608045014000520603e40c40c0400e4220401a03087c0310103c0c101203901001030095a1000d40c5801c400c180440c81510811007041d01b0141e40e80e1211250003460f400c02c100d41403a41e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 914213633 1250 914212383 914212393
    0xd091106040603150905130b270d030c05162402030403090f050d0c050105030a0f020a0906080f101205010207050d080121020109060507020a120b0610030b060a0f11 72
    0x103100c0140081a029005444c15158410300140b00c1c03002d400f52610420b203080c2c0d03203181043c10755074031481100080e10842c00c115a8044d000c5641c0160b8009180c50f2a42c80024012150103480160840c0d41078900e04007005010019080303144c1c10082480022544223060401c26001c14820030307a00c020400542d034591303000100b03020901d40d006020b18160b828017080420707001d070303500b04000c0c010803003e100501010400900f04050740c05900a182d0003401124080380b08a481404007041760300a540080100361009018400e9039808000c0c1c40d40200501121085418201d001d6000c59180e0300c5000c4140e80000790b08000c005080d01035030701850344481181c0c0380a0f0900c5002d0200002402000e0345074420514151003a041014814200c0d90181c590175101d0b070030300e401202d45501044040e0382107414032400294105400000c00000f90103000c11007064108181080340f12081031649408050030101c40c9035955440c1c4041b1011888182061500c0328200101980c28a5072a00004428014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 914214883 1250 914213633 914213639
    0x4241d01090c08030c070b03090c131a0a211a01060801170d090504020d1e0b04060807080c0f01110f060703061e030f06020f0d020403170405060d09110604 68
    0x415000a03403040c0c401c44901d028142c44079685552401580c1140400d680820410400500030100564009580506482b503841d8404089081d0707410482d103206005e6961000c04043c008440c00648510200300c0750b00c154585401120054034440c03d08811155580804d4039040011708500a02c10030301022210890f581d4130240600008824070551100c075007000c0541070079407404174016415444603203d120700a07041a040c08001d4100d54818a4156500c12030203208945071241c1c083c21000032540450320000d0031091000b510030a52003928980e100e0b41060068403804611104c696100355494400f1a040a00488001c500e036a50352900d401030284140c20044081085171040040d51014440309940e210750b0f00051256000034070a40400243c180001800042031a5629000e43c00c0581800507032080708445900040340c0420003031340040e0820070049113020008400d40f2040016003403e00c0c02e000714a840c0310300c0c091402c2050703a0301000c00401030300440429030124041c00258845d40c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 914216133 1250 914214883 914214941
    0x4120809040213030b0a1a0102061303020c131a010903051506010302040b0415020c06032a0d050c0304140c280e0c130503210708040801020d140f0424 66
    0x2000f51850500b1b039080c001000c50071640d0301c2c860f640303814060f801000300360399081d0802480e07009035808170218040c115407000c40e40d55813040e070040034004020004552111420820346003000c60005414054000001c0020400108032060502e1840140b100f02d990382c1c00048000380f0030b84e000300c00c00950100300800c40f4103505c03e000070109255000c0b120624148410000140000c50794106040300411070b64084101c0501440c0c0d2642c0b249413854242403014030703c8801e07180d044617943c9041e071020040100780210318002040d440f003000080c001001480c0302052060f550110b11028030980c14901900200034943e80b20003c0c88950260007442c240901c041201d98000000400c4620340d81030041158a00400c0c2c40303010301020038040e070303400c40311210003075058010002c180e418140601000810300d400f0f000034002c0301d658010004003044942c05e0200004030140020300c1045003881040001115a060070764804080320081c0c100f80c8854002c030014000680040303e24005602d84d02218103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 914217383 1250 914216133 914216153
    0x130b090a02100f1b0b1302030a05032b060b0d0c110d020618033a06030c2c07032018180c0d090311060702100605060412080904021303 59
    0xf1075900c0300e03030320052005000c42c0300a4004004d81499942c10104883c1301b80002040074042c406030540380801080e1b00c40e6821a040001900010b001300c0c0c10224424859201c01c1d102c0455020040000034141210110325003e0201410113140e501ea10b510300303a07401a030000003000e101c01c04441c03c2c402c02c0d03078000303403185410b440780c204804c2d181c00081c00c442307004400d43c4d607807003030b42800899018121070400b20944e0303e8085020410503141d803e51131007001c40c0079413000745000d4a141e42c01d862030509001d454205900c07801140203030207428568010074540b2590381020072460081a56402d01100f030306070340d20a80580250001c0002c1c4081c600c0c004014080003a003080721074009155000010890140c1c0031076010026120401c072868200d002c50b03120030b148502a00e01264007550294602d85054015100c0d007000d070b880306400e0480c06140c1c1c05014040c25040e140c0e28101444d09100c1d01c10241d15000c020009040400c03080c4440c3c03195070580b1103684ca44401301188a03aa814240058 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 914218633 1250 914217383 914217407
    0xe0d0207080a02010804020405060a0e090601080607050304050604020108181b0f090129070b0106030504060509010b010212071b030305220321030b03120903070e130b090a0210 77
    0x240c058900c00207822140880c1c02241d464040c3c680789466a29a401c120042138002c2c20b8650002c0d0003100802e0300c1c070742445070b54420f40a050080c620380d41017901710f500c0e1140050a4004118041080200007400400c916400507420700300ba024a48590b14410b200001103014a0b05074803a030b90303002d2034110f03a90b042c00c5181c3c0410344546060b04208001e010035104c00340110300c1c3c9890074402c0701c01040c030041c400c00f410382d050842c1c0c00d041c10707241e640b50701500c1d6080c1e0080707001941350014403050240e688199500041c462008015406003600043c1d20b07800150100441440080f8070700081c440c80b0421105900c41d018039a100382034582c13501801da50400030b503420001c9144a06600660210f1800e039040d2030700411035101003020003a1401043c192203558400301030322044000840d45082140b60300100c0d400c4100c3da200c03031212081c9480e02c0400e520010000e1003050502c41800b0720550803001c6d840d00700042d02c0301d40d5202d400d06860005403120003900224602c955400302d55101180d4121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 914219883 1250 914218633 914218637
    0x1a042c010b09101a0703020f01090c0e09060609010b0c0705121e030a05030415140114100c11010c032a120206160305220c0603051605090d0309090e0d 66
    0xaaa1940703000750140e01c1e202e00610b04001e2807001c40e813041e0b0f406a0040c107440c500c6403040701c1e2011102c040d81401d49070f8441c022202c2452043c4140f0180c8000e0000301d03448441e03440144580d03d04203000820780743d0184a8460351050000d008902808140090f5020b000060f000880700521002466038814180507981d00c840c480104806900d000401240c14a402c01d5941a0958035140c84280d8000c505c402c406420079035664140d4028450621224000c2c2200d00d501d0582d000402c09004050079a47c1003032042040c8200704d40006400002c550700e043d2000c0c640410783c940b0074038050380c00300c000c0d01054a01ea9101c1100301d50b100002c41182c0c4000c3e1007081200300c806c074503100c01c5c2c0c0e5a00d015507001c42040981c0e03a410014505c65030041e644104040c100314480c01e03200703c4c211810b9501d42d5050360b078101d01250a02920b85c00d4018950031010ba109040101c11803418010528015041040d215100c00c1d8104c100f410b100312000c00c06000281c0040012129002c0c51a40c0c07100100704d0540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 914221133 1250 914219883 914219899
    0x11070b06030c0a0f0311130f0506040b030c0a030f060e0a05012c0d180906060309020411120103290a0b0a150c062f1305041a042c010b 59
    0x152509100e800c0104480a0200f0303071004d01d042d903403021211468021240e402c41c2008506100c0c034803990090b109071014042e000120350030000180700a0300d48040301980240d02c005502c1d032071902d54213240d4048031782180d140c4101000902e40038029050050600f111403003640b5214082c00810b60000da4038200e200b00901d203c00044081c2030f0307001ca035284e4090043d00700b00c2c00440583c0c059007070304441c1c185c85620551092345608030402182c1480d0403e20000e40d491480b2021410300780b240d00406640300500364105802c903258003050314030500008040242400c500004c22009001840030381d211401101c00c90310309511188000c00026460620a00d00c2c1d200004a61241115820135040a5610a03100034181c1d250600a1f11003018600d40301081711010003030714008510402d00c4000214071241d0348202c86801c401c5050b0380c0d5004107206901d400c206102d030010b101051030b010141070700c0104a0030280150540c2c0800c84000912003601007298000c840e90065002d200442800c43d5010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 914222383 1250 914221133 914221153
    0x80d0801140105040b0c010e0105070507051002161e0f03031b080411010f170a09050d08060a0314031317010e0609150603030d0f05160c0c03030f0311070b0603 70
    0x71411401c440801070200308200700034496811114000c04540164000200700e8070074030000c050031980c080302c85000140003c180d40007002424400e03043d08086900381541031505025882d1a1050301050007856440003407009040030f40602c102011040c0c0001d801d084681300340c00c0c060301401486a04083c40d05e114192094840e000c1c0a84601594100c4040030f0b0083d060f800547c0d540a0002e00c0d10306029140008140c1d002014441c2ca02c11494003501142d0303541540b4242e1303d041104004a418010a40700700141500c81850810440307400c000112144469500b002d41107114039283d04244004004020904800840f2a00362840d1035030020443ea03011403950a44404007aa048095900319805007001071715480951074010f04000e040d6442d001c201009031044419407586404c040b0303114420054025543d00700c140c6c000c10b090a1943c1c5007c2c071951102d50702c003100d010042c180004c558010f13000e544280d110501d16070100d2402553303040d841c2860f421040084401c64403902c42d5030348107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 914223633 1250 914222383 914222399
    0xf01030213090f0816050f0325030e1905060c0c1e01081f050d0b040c0e09101d10020403050c04060503060a02070812420d0804080106080d0801 63
    0x1c00744150f08070103c044400c010350355100d244c0c2d0000b036441484440300110381c0c0104030148031040e411070142004550b18502c0748110174907910100c180700140c190025110380880d401203040000100c0c02c440550b100110000d2451480c0025000160070080c0032a6500c005031001803c010710041c00c80310300080c0c12010039950004219181301c940020704113004180c5d01c45000c594001c20298550400113140d459501040050511800a40d2030006640501c8140301c42001083e019003500c0c000d1008501d480402e40ea60780a520400c94015907640c1d41c07105080c08201c42c51082c80403110103441000004100500280d000750006417440c0c000e4403510340302d07482c0c140720324811240e000e0045c0c2060350f50440752074020f4010240a640102c81041640403240c0d01c40b00b00e600ca104e04c03421401030303020400e8410b001c503421220018600c9610414807442ca2084640c000418401200c00345061151403034458503500032a4003282e215801c08102090b41100070400781084845552140a0381e82e9600d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 914224883 1250 914223633 914223641
    0x200306150d080d230f070203121501110706020109060e010204050a0302060c0c0607061a010c050309040e0304090905060609150108040b0a090c060e01030c05090a05010f170f01030213 80
    0x4020340c003007444410080010940c0d8040e00f80003068080c0041c3e014284c07085050140312200b4050b01e4101c114040001c02c0180350403064212096200450414034110300c00002030340c0141007241c402042d0407480340c280c0e100c2d01d03004080348010400d40d04150758a81c4040d0281819810885100d8184082031910010510079981242e00040c0503400161454007489a941d100c00d40c1c0c041c880c01803207031540850300c401c0020251244640c10005039101411518640003000119490401603000c01c680040307a4000180c2e900d244003210000390f1030745442c140c60728510480d070000b0012400d050150040c40008140280305000913202c00302c82d03135030f21a60f103c007a007440c07424503000c650274002150210b8107080245600003805c90000503003e03825100c0d4040c500103540a80000340d031700d0404441a51380341c001d44940c0580f03401d1070f42c14101c0c00c3d0001580b9080340c6c0901810441c1b040307010404203103c0c00c081d141c80500d04000c10340700c1c01d1140441d08507213824041070307005559400c00e4840e40b50301889 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 914226133 1250 914224883 914224921
    0x90102070602060903032802030412030b0301020a080103171c0609150f03030806041118040614090a09110604080106080d0503070206182a042f0c0703200306 69
    0x910724590b165181d1185002543c121fa00c2910032285030000c00782901d00c002c501650007907400c40d080701c003600350040a60f01d05015060090b40140300d41d0f00300c6600a150203054035444072002c170300b042162544600758080c600900190802140e030b00c1c44440b405a101c241501d03e52202401f070300080d000382c01ca41100f184101d11500488100030008a485207410b80e8000500400124218518001001d03280d00503200f001d0038052807010042c880e1416100700002409404184c44181060130000f1360a00002000c02c0e100f0790301c6440000400411801d92450360800404440d151512088170071300800c564003030a80340381701d145c0e111842c01d0301480c203480c0705101030707402000035998001d10315003030100c00f1001d4103140c42002c1c0c4c584c540c215141e4852812020b0050540070404be00e50410060364089000701865080c001c42c03503075480352a14401e26100600b100c1080c0da0701c004c40d41c0c4a00c0c10b440c0b50700160401c880d42c081d410329100581d50360714083c04d086040b034178141c4401d4030140480712506 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 914227383 1250 914226133 914226151
    0xe0d02030f0d15030303020a0e030c0d0b0415020f0d050f130204090312020f1c020f04060804030e040c0329010e0f12070803090102070b0901020c060f0903010903020309010207060206 80
    0x400300305150814207000308050030a04001007042c009441c00144600101d40044020a40204070070a415038008998104100200c00620306280c03688041444426006000340001b0b2880300044e0070300c00401d0b45203039000b011002c119500c1c141c80084a01a42002d521035509900348000300d10b0a5415000c43c80c05102100b90b90004950954200401056440b800b142403001130900d00c0d401c40e03024405404513055000f64103507a600060042500311025002c1006aa841442840740c90084501950250f801d64141032000b600c49080c00d84d090038101d096a984981068008240d10354181c1013400d281d44900280748000e181c0040311024101103042d018006900000c2e04c0f4218035002448000d842005018500e00031810780c08682001d020741c004468643c40014011441c0d40e04011400050510341e11310340c201000580001d407a1240700c1c10841c803032080811100c15030041c1d40111041150300600801c20300c0114a4065200d4016840071070150064000000d805400402c8181c4500740d42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 914228633 1250 914227383 914227387
    0x43905060706090204050f01080706094e020a12050a08030601170412020c0603040b06040515030d081f032102030c060f0f07030c0c03030b0f0a12060e0d0203 69
    0x110038000d4542240c03a058a42d240c0301d80d0160050780300c900c079460140c400040103035004d43c117083c040341c036080b1140c0c449400c208102c0c0c810022000707003203001d2100c5405d4041031707440341c1c1d404a5416444110000640403602500103a609030503824615a0b003a00c2c800d980d00f010480c0d440d403c000c0c50340d14681018100e41c001200210000303038a0030065034415014113165129580120000ca41120200c1d0700315082c4c1010340c140b10b81550100000300d403101e0101e0303c461071031900350340702802c0a03000b4041501807912040800c13240b09042c0181030200070302404403868042c145500801c500c1d4244c5090424498000214812918500761082520f4000c40d0741c400300f600f5841c088840c0c50070041c800381103020502034203110000074800340f8002c4051010f001c05034208241c072101c001c14090220004cbc14038194191468541112007114810307058240026404400d0000c05d003e8500819010744c020341c1c122001c00c0114004001c000300354000c1ca405c00040060f8500c05944005080110025a04c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 914229883 1250 914228633 914228639
    0x905150132101b050714330424081501050702060f09060318120307170901060312031a0d08040b13050d29010e0a0c020705090439 57
    0x400b841211608107440c180d01e68030300380380390303c0b42c1c0f0340e01000c0c100d440390429802002904074501c00141c580380126080748500130f04615a102480f549032070254200014007800900e02c0940059a00800e80c407448800d20b0103200240140390070110003201d010690000100f21103008495458107049010b031582807800c0000d80810041b6042996a20300111080022005586946010b0f500a1001900d407507420044090f4127410aa40d50388806081c5505204020310325502004401591482d000710720250745440f0304aa01410550304080c01c00c1c07901140d0350029540c076500c20b2442448003407502d2101020341040012103034200002a140311000d11090184290040040059109011040d6141a030301c0000c21040484903400390355038080c030784120008800e10f201c4500c40410031031445520350f0500300c83c0c2c01a01da0151070400200c0d41e4410340910b05008000c02406000f0040180c0042c0ca004c0c9001c2844003454254036005004a400300c03186a0301b00203218600ba8400c5080c0e43c80030742 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 914231133 1250 914229883 914229889
    0x10e0604080d110d09121d1503060d060e160f03050607270b121e0f090c0301320c03040f06090f1b0b0414090403030905150132 56
    0x240c042080c0f51002010004010b100400d84102034800d07100c0c6821881000314000d000c0c00c00d00004a0344d030300160511021120556404611045892001ca0020741b00e44440000c601040e450140040205140c40000700118400203400e51100608113202ea4425845070281e155010b114800100203030f1020010074812030040c02c1ca8080c589582020021030f00684070854445041e50340000002000000e459400324850071105030301461602110740b10020082c2209403083c002003124170101c40310b2000c12030886c1c00b40701c0e02500300d40080007840320303061003101000e02440110710929402101990144a000c00075070661003900c00711109419962141c03120480072440780c0080b108140c6d0b48042034001039881c0d01102100380214084814800410304c2c44600c0501d13a00450100c81090108105640e404210103160304401d80304032150351203614060b0050654178030300070007a014000c0503440c00c195042025040312034544000b85880380003106081440b200000c0560711031a03401c82e0030f1041c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 914232383 1250 914231133 914231141
    0xc090a022a07090e0604062706060e060612072001021317010501080a142a0a081609020702031002030c0a030f050c2b0e0a060e0625230903010e0604080d 67
    0x189488c802c00054000c104001ea140301c00d180000c0307039019030b243d0003401042460051145e00c054181c90f86c6241c40c500d803014100c080d00040c081420400c0d144083c84002403034000b26075041c00c01d04000d64807404400440f40c62041c46029003000103680c01110440c462050080da8120351046e0301900308070303d07551615850100c000ca200f441340e103c1c80c5410b0000c01403000c1e081c094607100910300d401608610041201896503a405100154000c0a9146260b8103022840003299000300c40165a00c8107440440d08040c4003907007902981d4408010001c1a1003820000c02e0030650301d075000c2000e91140c3c508041255015291407003801018000006900d0b440002245100c0d030800c20b1440c90400403400c2c03c1a20542c098140c80da41107011200100400e9014040d21a10f110002c0c04140c6009803c1341d503444d4032641001071400301120071000e83e0b0b005560704002012035040105142d0b0360a55007400d1130340203000e01c0740250310f4030400622410010410b9405154044286031a0a0b820385041d40a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 914233633 1250 914232383 914232401
    0x4150506091e0604090c12050705030c0705010902040c08040201090f1d0702102a09080a1209090203012c190c030e03030906040506010e01080c090a022a07090e060406 73
    0xa0000410202c0441d9280e0f0042c00080c054500082403c506d40358008001c00e500c100d1100c416420082803007822074125064030340c043c95010582d519071400d0306050b8050480408042c0d0090310f070000107400a0350100400d40706034000e07201d242100340d807507100e820503049900c520380802d41196003481e600000202d480781c1080c2103104560035005070b14074003800c0f142840b2280e42226103001041049910280b0102000402400c0002807145422102c03510382990400c01046000b041d207503d601e07180510030307100240040200c215169a112440380d04070300c1c90580d00c2141110362010580007010118820303446a4400e502200040da040c040c0140030301840300c101d030705260702e40c044040c0d0307042e080000c0e5110386000340040600381000d040482c10030701c041e00002c00d040d2308003006002e164070010b002410f05000b503d0812031a65110b810000a0081110708840d4800030000c444000246201840900b0f11a8081c8d806103030707450115804550260440c940941c004000060100f065644002d40e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 914234883 1250 914233633 914233669
    0x1110c0607050a2c010f030905060f040620130f03030f0e1f08160201090215030405030d0204060e040501050405060a050d050c0d080301060f090f0e070905030304080c0415050609 78
    0x501058082d1413401456a61190204980000c0910115603405520500402e000b42420409802552030325a00c036100203181d5003a060f03240000c40c0400909900143c1c42000711004007400c1100c1500310303011980706a402c2a00d6035100440070508100490181d42103c0e07068a940302c00d03c2c8007103c262164001050070503485004581000c0180102c4c001c444034154190740c1d000c0c0c043c17400c030301e0740d001c0c480070441c40c0411a0b00d0001c801c001619605446a040703840c180100b62680c0d03c2d4a800d5246204012102201500114000406580118202543d03030030884050090b41e881e0f82c10720048910850768990b008040000800040c00c20741035814025000304140c0ea40e904041022035022852400c0c00c603030041e00000108a265880466010001d055103840e5a04a15000d00101c00e42031902501e518901e01c0e6011884142c0522800d800800c40607054a4440340e41e10172050319000e07200004ca0256007031031180300300052040723948003d4440c001d020604106900c401d05c60308034008880070348 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 914236133 1250 914234883 914234897
    0xf050910030602130302011409030a0813050d0b061201200a050f070305120901090f0627060606090b07050d050a050f12010f0509040f20060d0204050301110c0607050a 73
    0x815043c0c0020003040400e0044800c46900d140b00042c5418170101d00c821801c28140003540c4140d50100c3d40500c00c64000d01080c1e2075902a072080e54100760380d40c0c840e6501c520444401800c20194101540c414a0111076404c0c2c1c1c0100340080747e0a03182003512800c000a40b00103445002d614002c09800308502d203180140c144020307440300803100d512524041e0301148001c141034003150643e109955201c580080280328610043d07840c0a0414800c0c000105025200e1003c1d05003d00c0305503a241c200c03841d0f0482031240441b0b50070046e008100c1801020001030704c0c0361021840b00c11080444120039407101c0105034a1140d00d1086601e82c01402d00b407130800074100801d01c4030344802c4000e0290044181005051545414049000240190b00050040c42c415041101090b602c4110304407050700321007035590403075003006036101a0781c214800c15848038010801d000e1000c41079010300182c0b14184d00070000700604503000311140c0034800e1101000e81c441c070001040c0c503100e100a40800152810320320 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 914237383 1250 914236133 914236139
    0xa021002030117011113051e090a050901060f03050705041512050d12060501051602040b03010e060a0c0e100e010513060305070315050618181f090203010f050910 71
    0x140e0340203034001590004032683c50403030700070b080c0b02c0d40440c82e41c8102e1180c80d10421040e480c81c0500140700e090700c034403060f060800c400c00a240384404884c0005080740340364036110610300c0050009841300c119540ca1b020000c00c4904444038900140c03908070b4010046e8504e00300c100b00c050704110894884248860308005070503c0e4040000c1c50451081014001c4400345800040c5140c454503091206130b400e04804205030b036009000c4408030704d100880310661588500102d009840034852490f0035600c0c11039030511b144008602107020700b04411082c00000c90000701107410000d1aa04140d0101441078060045401849070390a48001810031a0a042002c1a1500c10440990081c00840e4658080010742e81d4184252581d000b00f042c0c1c582061820880411203d002e4902c002010245004a106051780c3d1a144000003401c01e1442c2c40b16032074541c1c0c041540100070740b00c0c50550b1482c0c0300c02040031740c11802138030b060b00c40601d51050000d2402e001c102c1c070302201034145d80a10103004004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 914238633 1250 914237383 914237413
    0xe060607020a060507120203040e010308070203160b09091621060e012d0f090c031401080c0a080d0503040b070c02090c0340080c031c0c1b02060a02 65
    0x6280144400c0d03e600c0d80f100c1d25414000e40e03e41130046c400045402c1004240402e40e141c0130400d040d01d8010440f5511040244046850b114440c0b05400111021300300c005600380c03041004140640d025160b0001c6500e5603007040b103400102c01c02040101784404044010601a4030f0b00d50700b1091080c1000c6200f81e0b40b440c1001064400707030090340000d8655031030107864608030000302040a4501c1c0b0440e042c0d40c600080c024035a6002d00482d0308454a852100d503585100707411038040011080d041404559440c810b41d581d410301c0f0703035807107015504074200090280400f0482e014556020b484482c60f6a032181d440c60075008009180c001400355800d00d070703c09a04c0da0310010340705204c0105a255a0309210740f158050700c0040c0d4200e42d010328803e14542d02840900042c0c0b0940c0007000a90a40c1001481c01d1452405619003040d40d5100100f81111401541032003041c00c0050441d0420030440c40c001c1c1100c603005412301c2c12885052104001c80103091590082102000602c1580c203503050304405 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 914239883 1250 914238633 914238649
    0x6020c010203061c050a0206030c0d0f0c090503031c0203060d050a060e0601050303090a031103012004140603090c09150303040f05090108030a020709091502120a15050a0e06060702 79
    0x86852269804400c200107030030310f0f12440c030303050a121595010888540d80d44503580c80031018024040e64003c004a45452945015160013000c1c90720f0a0001028070500d2400a00a01180800180320150006214203012003111010001c0c62500c0d00c400200d0030944001c1e600103850290031040c01184070b004070314103004005d1a036100b2500403903800c01d540030440c6441e8060f00018842d800c100069861540ca00d8040d100f2645d01a654a0030710500400017401002c810801d91080c240702c2803c500641810002441591a040d00c12021000307a4000e1180601080701c1d52901a40891003046862809c01900c17503000b40040100c440f40c0c02c10501082c11a04113a2200c130f21302140c2c134070602851a08501c0a805010284019410926080402996001a841104030140e03946d0780c030a081c0803200f81590180d03000c1d0802590703952404a0301c0807052000301c800b0710346030303141a501804280030b09401800b1200c00074000c0142904000d85020003910161002e940000c04001000041c3c8400007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 914241133 1250 914239883 914239897
    0xb180603070e04060b0406200705030706021f022b09060204080d021209010f18030b0c0a020c010f02060610030608010e0127021c05030d110a020f07050a030f0503070602 74
    0x20b0b4408104120500b80002d07110740390400885030000380014070100b6844000c00c2c1120296000d2205905030303004005080c03c1e040d8011503018002e03e900824040d030001120300941e04036805c91480d2000d800884d10807801146002183d0b00000c1c400201140c0904003001081c1c42c80c1140081c084485a803a60100c1e032056014081d260040405003040d039070144400c00254400e0100e0518123010040001d062520980504083c041c040b00d06080c200c80403060900550b6000b410750256040000c00d5610b00d80041aa040c0180301d84a07050304294462160420861442e0b00206005e88408041081810100c62000200740d82c4d0040010405004d001d071601c200c00b04000018a500703100c3e009401008011041282180310110010060300c40300d0741c4401c071441e601e0b0f4465800035a8a4184e0540c41030125080740c0c2030a00305041e18036000380000f88803030542502150440d150400c52503448041c035128160340325a040c003040022070290310b2100c441a1207002a680740041650f200012038008036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 914242383 1250 914241133 914241137
    0x4051f090b01090506090a03060207240207110621070513030c050117090601050105030c070f06060f090905120d020708040906060e090108030307120f060b0c1c08010b18060307 77
    0x1d82503642940c102d681032000c0d18060781c042d0300d000d11a2005c43c0d400e00701031000403c51680011a5001c0c408c2e0211802d40d0045034000310198075042e0814031029402c415000d850750009031121040c1468030030211043e48940c00310405103c00041c0b201d1080c01002452501845420440f0302e40e1502202d468401035841032802420060501000509001100c80c0d03140038207404100380460560000b07201030441c1c50900e00241e0740d5440c0e5020340c03802c0c000c04800400300c00c029518041042015003100c029640c8204010f80340c10303030711641c0c2c3c4251807180d04007425581000940543e0403441c1401000000c802c15005440c19010303a550031031903070040d0700945503282e071400144000d81d1300c0180380c000440d045032069007650406030015200e201c0a08600148498610300407a01d01d1103400c544c4549000b00804c1103100d80d02c0202c031001340d01840a140c0640078003205002540c0043c00305031000003690380c4d02c5509a003041000d16641d03001d0001e26010380006060099940d844000452041e8096 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 914243633 1250 914242383 914242391
    0xf060b0d0905010f150e07020309130b18063006340503070f09080f0c01260408030702072402012901030207240c17010608040204051f09 60
    0x40c10b005007103800340070b818010070b424000040d58440b02c0d43c003000141c0f06190a02c5602d901c400e0000d1346540f181d00c0d416a04190510703038200c00745a4130303800582d0b0f6140a0781c4100b040018040c1107000010129042d56210b540900201400d5003c6503885c50941c3e0b01a50f0700e2102d1b582c95120320318000d021500010b01000700d010080402c1501510202c2c030141d003401004803182c0d030603409070083c0001841c074020019149560420a4480c031024002041e0343d1042c0d6100400c0190101d40f2045651a01400b2404050202088814400980070029440c50483d43d05484943e01c03075080b580003a081d00110310584201060408400e494a0100e00d94891019401405800064207660042d680c0400024500c0c0ea24600c080d150954107114030024640103035100b006161445000c3d030b001c0c020208080c2548040e03100310149900002d58121181c5a410b01d20701454081c20301074009000e42d500007150b000215005060035004560480001c58400144549408000400c00216803185070441e1312 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 914244883 1250 914243633 914243651
    0xb0409140708120304050601090b030a0204060b04091406060a050306031623010315051314040f230709270b060405010b0c0307020d02030a020d060f0b01050307020607030f060b0d 78
    0x208100f02240310f000103800742d0540c1382c213071038032030700e412051040508003629aa05285141d400b40590001d00303500400c1000151785030103034403816401c00d0050400f0f4500e881a807401800640121920a000003080c413444c100184500300e43c103401c00341011340c151040030484541c1d5050421000081d090114035890f1090b0034600500361b2040102586052614003a03905d032811700094401802c0c0c0b001614103c110b00d00d1504924001d00902c065181c00e00d401e6424003040050070400d1a107007500414030009845800c038020078081240d00d04100e11a84070541c10012100d083d00142c1c00680803814240c0b50520503c04100a0422102c08450b200c0000b02004420f280a100c3c0f40e015042c1c0400c0c10741000c50303021606940c2d21404c040a0722445028540e030003199000c112201c945680900802c100030810315040307025102ca60101c51049041114a08071940f040c401d6034070640666000705803d40f0740302400d0740240450440c40c0072040c1c641401203410038002009201104145c03c0010b01c0c101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 914246133 1250 914244883 914244899
    0x60b01020c010c0f060c11010e030d0e0c010804062706050402031203011a0913140702101b031503060606020d031805070302060d14010303030912080403120b04091407 73
    0x500315460b410b00c2a50400d40c00441d9100203241c514951000e00010380320322095054609a017084101c0c445982040c1e40303500440c09c044041d0409644424062003245240c42065131a00c0031450020f0000b160640000c0c0450010f0b040380c070301d141111490307110b06007100d00510501d007600740d01074480716103490a010840c182040380152020680c0626429541481034070341c3c03100740388542944494004207076002c4a80d1141d24070408015540410031100188402404070307807000300c079044c015002e010812801924036000e40302c0b1204082c5101c0761103203440c610a03001859101c00b1030010708031840001c00081c619101d0780010740440d07002401d03a900e10601c010192040b0100d4000a16888858174000400002d100015aa070480f1140d4071105503014040040c0ba944040380c014600c0d843c0008185030301a800742c4400b5024503804a1000c120005c03d960412040c2d600030001a048040081812150350100700b41d054000c001056000c2e0b280c5502003421400c0d0f40f00303005070b040107001b084030324 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 914247383 1250 914246133 914246143
    0x12081b0427140c0702010e0604090507080a02120a090f05010c050d1a031005060303070c0b0703091422090b0f060a1a09040c14030f010e0a020c071a040e04060b0102 72
    0x203206607024008010400225001800003428203003081601203440401c580c006c2d01d21603802000600080e4503540c6d51000813014104c140c42d034401044071038010840c0c149641c022078100d1005650032038003c0d01e8002c1414001c02e591082500c198003000496800900280900c0c2e428043c9a070350039441c0e0110b0044082260054801100d03940c2404c00216140e03200800c038240b01c40700445001a41f656110301003400c3d4401d681e4001d05903500607201240707140c4240043d01d88030307000f0340d9501001c60729020380d400c4549018800d0380d4040070090210b100419059001c100300520740f00301241100083d5102c540d00034054132000481c41ea21000c010042c01d02c80f0403c0000c0019400d9010031040c80b980444007803007414680b9024907212070741c490f0300383d0082f5040790508603541c2c8125628038101c001401031000a0203200c14032035040c1d0214401903014000c0c0c0d04025400c00180a003075117080d032220320300b4074100c0180e04070390001e120000300b029540e809244501c1c00b840003c100400181c00082c104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 914248633 1250 914247383 914247449
    0x250501020c030a020906060c03030a020d1a18070306180e1b0a0612060b03010608070806010e01020c0402071b03081b150a4a03030412081b04 62
    0x550001c1264035036541c001a881e07a8040d0199441d00c41502c8000c0031a2891150500e840503a20000090004404056000b0846426204410060a4a403d10b090a1181050707078180d4002461041140002d59103c10035401c4031280c140061101d5460304131301009072060000c10881e585d2813a04552500341804034041040d00820030301035000070140091141c1d41d050240b44200141c1c0c0b501d800d1074032020384c094070180c080f1007006600d030b40c2c0d52000106054012101000041c0b403c50101702554064114400360103c140c01500c00e008000e024000250840704042d01c128004800301035006150241507000f41d801000c00d40c2d40c0e05007000e0304500d091100c03c034080c1079034448101c04540d0440350b21400e03040f800000000c2502400034020024615481e100d8010980b0450018400c003800025140c03030490a121850b1840d0110b080c1c0942c50340411200602001c9040a4280589104554075980412411030f604a49500703030303420000c00e411640000200030004003005c1c0444402c02019120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 914249883 1250 914248633 914248637
    0xd020913140607091701022209150806130305070c0806010305160e0406020a121d010b061e130807080a060b03010903120f0902060c0601050f010f08071b05250501 71
    0x1031810803d5005044034001d128620401082e0480e01c102100c082d01261110181a41940764240d1102c917442d040118070b10809010a1514600d4401411202080b8045441c03210143c02e40c1d075107100d04044c05460a040c1142040b40410500c1c00040305880d400000d096013100403e030b40d604520f059840d144010b20110a008034001c0e04200244440a0302948180d0014000d0389800300b45100f84c403070801c07070300d000c402080c1003042e05e40c1c80903080303a08007000c022908000d11810001106000d81da00c9800b02d5034046031a002d104102000c4448003c00b99070012000c002500360b59680920301f806101d13000041a070300301e13400840c20712080d800784204601d0202c000304511015590b010382120f580d0201c001c040c0d5100e00c00702505800c540d003c2ca58158000d000036569001d0700a000f40c8503182409414840e6405900c0702040e135118404444811245854100036503d80910a031840c640e82200c64070a140a001c0c1e4000203a41803000010000b10041c000c0590100e94082c08400e807000c0e049141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 914251133 1250 914249883 914249893
    0x506030a0b060f01030204081f113402090903070303150608060415231002033a020723190305030c0405101806031401050f0d02091314 59
    0x8046803080c2207003504128100d0b602000680d0000068020703018942c402469030040c0c8941c0041d88188080030078255881c1d407020003550200a5132944540101c20790401c400c0041d012140c0c108101d00d041c12000f0059800002410703100350300103820342d1400c8540030034682012803600205500341c02560354000280c058070509a00700319004090110007004644900d03254400c82c0c0342d001d140051030000d070030040c6014100448008501140074807094840c0e010715185000132185600c084107840c0150610b0001e07222540050440311103060244511241c003e1404c241c4060404141c80201581031149848440d90310540604070405221843c1918442d000040600f24040c001c1d90a801269898241035860782ca90003c1c182c40ea0040703400c00c9410403a6580760114858000300d0551030a102c00d400c03c80c1d01070b2940c000b14181c1da007500c80742e00ba110400006000516000c00c00750407542e005494560344058940015401307001c1900c0e0f01500d2020700948806012441c0340100f60345244200500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 914252383 1250 914251133 914251153
    0x40807140609101206083910050a09080312010e16211d06010e0c04060e01110a150203070201230f25031a030c150a0504080a0503040801050603 63
    0x162090844900440811884c00b4559600d245140d1022018244c000100c407461407100014103c2d40b411240e540100010960300c07216040c00011083c0e43d1070a021380001c111140711304090740d242d082644200248910322402140b000720420241041404100c11100b03554035201c80761581c4917020344580d00c640351900c10320984075000510591202003104094440c1241030782c1c0342c4001d1000070f641392609655452280c61244001490905a80030140324031950344a9840541d02071050384109408101d00c041c2001166020306060900d40340340800b0754003840e080f035560304c0702c80c01c80c00c8a00c240326a0100034072010580c244202c1e2141d90030000104040e05007036144081140d002000d8050b03842c03250b80050a40c0b1904280f552074034004428540700031400c000c01901074001911440240900d1140070401458002150580c610014102040800d900b8289100542c483c0c86120709201c0200000201ca1108000d00289030703000d07101650b02ca80c20304803c00e0950740b0240100d880f1750300049400b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 914253633 1250 914252383 914252389
    0x61305041208090a0203070b0306030606120a1203060506191103180d080910111209060a030e011815050a09080307080601020a06090302011424060309070b040807140609 74
    0xa584001c40a0520301400d070380310102e141c501810b946009405001d15200001c01c40441005075006120403070a0b160250760700400e1161350301200d8145102c9a100788240d80125580c0000d02c070f0394a00c50b2902040b02900c07030010402c2c5078020840c2d90a8100a44082100b10341c0c030180c11003a0242240145141c43da1542214104414400300d542c424402c0c01002800c00c0001021510351741000b801880f815641041c01500010b080d0541c42c5207070285034902204510078030211404694024101400c0c4000c0100480042c219680340181540da1010004c034041504400b001d00148180d04480030a11814a020191a8064482e21000e420046d164000408410599501100c14a00319000c1e945000040340b604000000290890b071600b03501d0301c181507040d001a03c0901e00044030201d075844504107040e1b545940e8280f596401c03410303140312a01d0302e8900002d6030010a440d084440c19a2141440001c03a07100e41d108401c81c3e0b101d4003040180341120842824142000c888203410f21040d0004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 914254883 1250 914253633 914253653
    0xa0e010605012312011805060312032706190e03181005070b16200706031805012313050a171207021b031c0c1a0f06130504 54
    0x1400c0f8540d0342c0b0280350001000e141040e00c4000152998a100b02c0d6500c0c0303100f620380b11700d100f0201441030500e0000341c0c01c1d04000480403041c1601d5041d240c516620440d4602041100d0203805403c5004d49145548000c41007000b07a00500043c81d092030030313900d0504a4012070320342c0001c0c1c05841d0400e000e0218001100e0700c04c000d14040a0312440060003841074202e45a10410030010005001c041c18003603045810001040358100030b0321030f030b0b22a442286e200040c1032121455030b10079510252040c0f062900c0380d0845000981130030f0081c010011113641d554250b07a0b82180402c070b0810041200d0608601c00e01c1c042e40c1101509550094940300b51700c1e403580f01e40c220080501590440102e80e01800250700032100c0716121183c23800b80504245000039225104107208508000e0310840307045152070007080801c0e20820f1002d02e190300b480701c05416501c910800a0903604140024115002e412903114510b2098508a81d8a405032501c0010404568030325045214600d15000420001400e004d030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 914256133 1250 914254883 914254907
    0x30809032a190e0c0f25030f1704020f0105040803211f061409040f0519060f030f08090d03090e0f090c120c04110304020405060f03120a090302090705030a0e01060501 73
    0x110658900005507090b000c3e12503100c1c29506e074a88203614000e500c05045003500d0311072081e928000a681030324021140040d040109145860388840414011714065220200101c010304000e420300c1d554240503401c64001c810ba1000c44410756080080c400380d4204015480b800403004001400d240c1a042d81a8440c1402070f0070034008000b0001244034481021390325803040051081c02020204404d5002419003590034041c0c5410061042e060282d03180580c10a4416050390b01503500c0c603585030f01c40d82c000c10401c140d5070200200300a0f41079458204000d1411030080e11501c2e52546410302c9852200c0c0010f28040b550300000c0d0a02a0003013006c100c0844e00b00341101d07079040b0502d4546a0900f0300122100c2c0d180d020380f81c640c40311040800301000e140700340d008980400c01c0e5a154030911094021040101e58560031035000d440703180b52104040c0a010307180c0e18101451603160f030b000c1201c58005a40c0c00010400100401c5440c2200c0c2c010b01d070011442000038050325141000180c10000c01c16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 914257383 1250 914256133 914256151
    0x61403071505030604090228080f0a0308060a050901171c120c1e0e040b18010501050f0706060605030103140d0e0d08220302011116030809032a190e 65
    0x40b039110380d0b17560003540c051900100490b500c0c0041d00700d00851400c0c841014010790820b4600020441c01c0801d4100303110400c0c4002d001c04110b00c5d901103902c2e410003000540d000080341c9001ca4507888840456000e0111101c2d0480c101c1d103122241c2d4a810703155822100120025100034ad5006d9200341100c0c17864803100c102003000e888404003644e4004900c603540c07000141042203c1c680c643d100e518420011810b89081084801040500c081d00c00400c0c0e0102e00c20880301d004106d654030500082a64000200c0d40505144066803103005607082030344000001400030005206200e042c44010b0540240c56000384012a29208054801900001c59a204940d09403200702441104000c5419406188000c00317080c1003540f40601c0100c80d01d0005a001980c03003002d40b0111480000e071140d00a102c20b1030b0007451031843d95160004d502c803800051705030103108504185043c5401c14814040e2a05030310010580301c14060000b5161400800a003040240f40c04004e84040803070265080b041d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 914258633 1250 914257383 914257387
    0x6010b09130903030e121902070f0611030c01020a0509090a051b0d0f090516080615040f0e010f06180b010504031506051005070302060a0605130c03060b0a03061403071505 75
    0x50405400800c0550b00e2544280120075101d606c3d8041c40c80285803413101d24180c40c24000440c00200d079a000d990180b658451080c2c00d0a0191038080e0707540c218099036201c2200d2038018920f028500f60381044c07500307602143c4045031000da00d141140710307a03600103c81c410030081403030030b4260310480030341407885181074140000d1240b000c40c2960304540c402a00c070100034000d1b9030b141d280060350354041c0c5111101c462200c1001103501400822050301522401c1d600e401004002004c00c4020600848242802d550f80c405d5410320f19402e0003400c000905442c2c00281907071501d101c01c46227810410418410314941003843ca140d07a081010354091f40d8001c130800400c860b1200e6070303400511a0350801c80d4041c0d45072080c180d0960b400001080c05038842e5081d1341d4a900d9080340042620441d0150552203001c58035412960141c552012602100302e14000c904d15603100d01801d074540c05100200e000986950f020702480402840c0e40300303071b0107084c0c0c010062986414042d0071582034243d0024200400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 914259883 1250 914258633 914258651
    0x40c210f02030304050d081c09020102100e0705090403050c010b03010e0d0e120102040e18010612020d26071e02010e06280818070803030c0a0210180506010b0913 71
    0x803c150744c05403074090400000ca41150a00407181d0308262504e0a13484107650b00003100e24014010b5124042d0b068000341142d9000300b5140f0702800d09803c2c05619481038250000c0d660717980c044075a02a501903140c0c96980e00c2c200080c24250360f2100b80c00c600aa04040095444203000110101541c1743c0707141c90710440004c4000181a54424031101403150b00104000c5000c09070510803600403d188500b44003050b02d182a02801d0302d0702445440142e40b900020700005d0704040c0a0b82501c540b1170030480d41e8038822104880c035a01c1541640e2505003101092034030030021071088034503041400b03440010681d802540020301c82042405c10a005038008100e9124510303001d10490a040c0c0d01c0036910700e000320064002003600204a8007641d903c10151041111014040f44800680382c840014518564948800d40660750103594084114420b101c08450303910340ca071081085e02c1c003052a030001d130058581001131418806070804c0c04208020800c060b4203a60350310740b001c54040c00c0440415031200d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 914261133 1250 914259883 914259889
    0x80a050f0405040c0306150e0315060d050610060210021e1612031a10090e0c09030618150115030c030b060d050907140105070809031212040c210f02 65
    0x1541d01643d0403a040001c0ca070307942ca81540005080c1c0304100faa000980e0380c51902103841144005c95150150000080d03c941d09406040f032035031200010344969281015595100e00e0118225107400c200f0007039080c14400f80745c1c10b001503c41c3c46c81096055041038541c4401e0804c48a00d400d1020405100040815061081001c040c00b80350b040304020b01c03c1c1c8005440500a00a6406118008451443c114207285000b062a0001c5451030f600c06000e541412411644014050000d030306145040c0150310309544c04008081c81056160820000c5100f500e0003140f502c2490a0700c01501c0314000018089100303110501c0201581c50326003c00c502c0c0000c08141e0003003a0340b05841da0407440005420920080a802a90280254100b2140c51780d0b901d60002704407102d00b00410380007a1040101c01d0220700111f019110500c1c00500350f806450f030003080d054081e48403245180b0030540800c108401c2c0203585405000402481c842e600c2c510040d010f42114900003404028408489a191101903403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 914262383 1250 914261133 914261137
    0x720031c1b14071d0c070b0a090827030d020616141215150a0e280e070e0a03080301090207031e05070b10030803130302031c0c08060d080a050f 63
    0x71128001d5030a425200c8044e81800c114041c1080611a0a10082506003440c00d04680c10307a60045440c0c0325603190058140040d00c6401c0041d1124481441511a1044d09001091002c42083c0c2c41c0400b02c00c2c000149030038501115024404e640007013040041c2040000c00510200003545041d4403011b807902c1b8122001e000d60203200419103155410046030941001403094654070468180b4811078403034510702d000e40300307401804002034200c03002031625080c40c0c044c121038486200d2151392403101b00107a1004550040d8002488000b90605001119401c01e80b0340c0754400041d18081e20031411512030010510040c46034000345030f03002070700b5000e06201e1501c6840c12044005003000c12611404024103642060000781e030000710b0040802d1001000391141000c8950007070000381941e4450082032000c0607004015000d50004111501c5035229043d010440881740510000d102440d001009260b00401420745008840c0300d40c060b00400c0c400c030b081c2c80d1860902e2a203966600d030300c0c40d4034210034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 914263633 1250 914262383 914262413
    0x906020706060314120a0e030a05010906050615130b09030c180628052101152102011d03012403121e0c0303020720031c1b 54
    0x55840030a066041001e0303508003804880c02021403500942824085580701c155203401c440d0845000c100e0303480c009000e01c4110200070b00040945013014050f0311040c3c04e5449022089070a1691303042001241d20341801841c00c41d9140500d0507043c0300c0c1942c040c0c00517840078080c0759000398020400c07110aa508020590800c00c0240003698030040a004050741020192445407081190304904c0426903120041c10003640401c466070603450b4030f030106004520702c1000d291002195580b4212135520024043c81d0303030311009518100d948920b4600740701210765605444078410051680d80c80301503070380024807414850080203c440d12145013000240100f00501030000c00d01002c0d2000000141c1d0708000d03404590007078640311411507032800111501c00c48901ba00405070250101d07100200e00c910300c1000414400c1c1001407910100d0784400c0e402660202c1c01480f901c0082009200d542400c0c41500d244a17000c903207280030b2803000c08001d4802c04905003002100884010b0200038450000010040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 914264883 1250 914263633 914263643
    0xb0604090f0e0c120c0609060f0415020d05040503150901021c0b0a060212030a05071b081323090910050403020303010317070317130813050f0a1508070309 68
    0x1d02442a1501800703450100030505160140c0300710920f040c02c1c83c2410340030f0608410050240640410308103c0c40341c001d10600c03900034030f0a10010003100b80110003403025180b5205810b100703240d5408021f14240154482c2400c0040030312081105031000500e500c0601860040300700e0698540d000e180c0240110550424500c0312401e0070042c2004a5120b00b8041c00143d030014481e54580c0c00a980e6802c03122071642e10018204002650607006900103500002c03a0318001050a00c66500c42002441405090f2504031001849035500c16400c034155006040f5010140c540300f40750f8847e4001c1c0044200f0035070003058100d00007a45401c060110114913102ca0030104190304050a00940d40d400c01d000171516848080d9000f045c903162078080c3d6582c00d9140d2b032510749010010410000490000c0c080714212140815400000340c0c0c1c4002600e003207440e0045040c3e03503625250400000003403500183d405584a804140f2000d01c800503105000040d82c02c3c800340c50703121040110010700c110702c00580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 914266133 1250 914264883 914264891
    0xd060b0d050703120c1a250e04050108010509030403020904260306210c0411370c12050703031b050307121a1507060207050307030e120604030e06040905191107030c0201030b060409 79
    0x1c6a04010704903030380123055500700301c0c507a01c89804500b02c40040e141411b082d40144002c1006140c00082d16a20601c2150022102d0800c40600780c40200042c0c104110f00c00b002c01040070505000d4841c1c1c003a82c0c47c070000d0140840c40342d202144c43d03e11410403180140d0f01c4000a0504c030f18000103c2d0400c0c0009124454078050407907200f120442c801e483c1485012403002e154000d18418007070003405039002580402030035070b01c180075100c0e980310b5a422003d0540314042035405c2c0603a841c0e0544100c5c0c0c0c6440b80c0790759142c0030300d00900c841c2084105405c403030728121411011310720f14061042213540980341c2000300c44d021480c00c0d000e4015030030010082400068a40100f202c08005814140d2203900c409410100d500200021540d4001d500c10755136214400050200e4480d4191100c094400742c806172405403548540c1080c2c40c801c40c2c0c040301c4901001c5048207209060702c1001241c0100004003420000725680041c91044082406410182c640265807407039502e400854004100c01c0340c2c200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 914267383 1250 914266133 914266201
    0x1d151b070b0d060b040303091404110a020a05300714060117010f143c0603060c271c030305060f010305060a050d060b0d050703120c1a 59
    0x2001d540b00da280485801e052000005040780000c0544007134030760588502c411941044964441d05449805450340951506407510305950f1250043c404100399602800340d0260a00f44546002c07209049221403d0485204900e10100340d04100da4008008010303550704c1e80e0904011b0400112040f00300340a0141342d00006034402d05544007000045200000c0c0003200480742e07031904a17112290009100945400007501200005001411899400c0b42c450074814450758228644c8503440c0c0c0c04188a0241c10501c209843c040000580c030041002405140294142058940750300c103c0d00b44010440042e50311200c2c0e0307200711081e07221030224000b0310940d5140741801005803034141e4502d40220444030901c103040d44240622441005c0151090380d0013407900f0b05000e0301d400050000e44440d90707604070102d4540d0b100000070032501d010708001e00e200c2d070a500300481c818002c81c0c41c1e50b0600a00d6044880080c01090401d101010780c0707104401c4a40e40d400c0c200300c0340c4440320940003041100e00020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 914268633 1250 914267383 914267399
    0xc031c0c32070f02192d06030b030a081308010b030303160c05070b0703050403110406061b1a100807060c0201090e041119080106050111070905041401020301030b071d151b07 76
    0x481141e192603011b180004c03550070178081c07516015441c0060718169420902105029400a495081002c0d04503000e00690361246034181d005140c0c10207d068004904010410090140d00e0000c50700714040c502e181090300d00810466086404001805880b05040080c010700b804004000c00440701100da96804070b2800500740d5002c2e02003140c00c038280a80c80450740c1040e00c1400709803842515240d50b005119145131810440c0410304640c10a400e4041d480007000c0d06424074011402c044981101500301f080b0603091000e079802660400a600050f60050703039002c01c0400c1140c25a9150300841c1d21941010b100c4c00d851100c4003a04140c21320700c145a524070003a00101113500b0380c0003c00c001600c1e0f070011920b0804e03403100e80400e0b611905c005c1c04810402c1c0d025681151090b880c001002c1d855015050980e00300360b100b03580091181e81000401c1c5e40001e40c1d00300d40c80300d041d2012284210580000c60030a0712000003e0000400324171940c6070900030388180301c0406100b085844d030569940f09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 914269883 1250 914268633 914268679
    0xb0403030c170d14071107050105181201020904140f010324051323030f090f10020703050106060306080d08090102090303040f05031504050d050c031c0c32070f02 71
    0x1801040b80c0c0184001020300340300d0401d50321ba0440d10000380ca0b0152502e801100e054010141030707140c050340c500186103c0c2d901c60550518582c190000581c0340d021890800c42101d1004040d00e0b40a0400010460b00e409800031590640b60f0015145840c07602e001c8000040e07110051a18560078130742801c1c4620b540c1d4100c4205117062141c00c14180c221005046952810a241c00200710341d40300744040244291640003804203000080c1881c4001ea181000180d140d6602c10000009038004031000c2c02485020700a40003e490542014000360b17103860507060313890b03c04441d44400c00250202244519030300b0340440d0100080201107070745487d200c0d113840e4440c0b00b052045074440d00c1402900b0303840420302440c4130311464224025009804501d1810f0711944d2202120720400e0104000043c28150070440c8503068030010b1000140c5c0c0e0128003c01380c600f07611400240d41013441036a050848009411704040700070340c180c1800703480380b5040c64a416205505c5000a62110142c0c2c60800c03803c00102d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 914271133 1250 914269883 914269901
    0x141608031b1612051c140904091704060320070602181504050109052707090806070e10020c0609190504061203020d09120201270b040f0e010b0403030c170d 68
    0x548019401d40302c080382d02c114205c1c07507400105000152164507682d60388058800c10201400c08601156155540c1d01d0172401c9820715080c02001181c140452941032140450320101c20706000e81390108604488058090024000c08603038000850000c954410028403420041c0607050312161184400c00d04c1c80364029008042c005422038800203110710300002c069100c40a203040c00c0c6403000003d41d07444c42c507030401041401408001d0500040840040003124812401c598518030200d07801020400c543c4c207945030240441d0f102048240312a030b11081100c6075404200d13000700100c080b50703a600d000503025070310141e401803038201d00094001c2405442d404551095090f1038056a21500950b110407803409091010321207240c0b100019400380c0d91410324903410b08080c1e00c480d0076014122024100c40d070401c0202102c041130400801d00060b40c00c401602122410341d50a6040c440e241c0703d0b9005d184009010001d01c0030b418010300c0040c50044081c0c0c40400308095a420003c8000300c042c0201d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 914272383 1250 914271133 914271143
    0x60712170a06050117061f0903140a0b070e01020d030506120109050c04060501051c021b0f0f100c080a0b041404110f09240319141608031b1612 63
    0x130703050b0540124105c0c009203d008000c01c00440c000f050031140303601420b800900d03000e114460348084041961041024449400c2034000c1900816601d030100e01d681000e440306092022182845100360f80124000114111078900090240d9070880004e4152407102071000c081e5117000c50850074054003041d017a00e2080195010312087e17039250011540c41c032402c1aa44404015511444c0c0c04440503001000c01d601c02c0d0144c00080c195100116040841c10213428410313034012800600781340000c0c041c292646111141c200016949004080c10020000b400e945605544503010041a684e80d4800b2441c0309070300300c0030074a903c1d00d071401c031650922010b81181f0031061007869407400e1030600d5a007849414000f91001001c2c03110b119461001c0b4036210300640c54003580c0301034030b201041c00c400c0946c1a8010360014415104010b411400d00000ca00c1895140030b04103410700ca540000001c0319285c3d94015078410300300c00b00d45426410400e170051a40d00031501040001030010102180f000c01501030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 914273633 1250 914272383 914272397
    0x603020f0112062c0702120a0e0102010b0a1d07110a061e06380405010c0201140d0b040f0608120d020d020a03050411010905090a0e0c030d02060f07020c060712170a060501 75
    0x40728145d0387da48030000401c154400801c2182c0f240d40c402c40b0300115001c23041c000420583ea49100041d04c61003590030419501403840c40c1c000d4090041c4440c281c200030a800c0c455415914030030580c0d00c912411001421858681c5600b03490b070b0562a10251030441140405c008407074640d9402e03442c0d00f003030103503080d031040d80030415102980001b03ca0300d40c02944250380c940b5140ca0003005440440340e03810180d061010040310b8010208a250080083d69044038000503000100d1040004440e2075200c0d01568600d0000103000400b00003810310700581c0809003580d1241400c0390810040d10514081039544c2d070010488914694060b08040d0103113120310315424220350340b640119601e002500c1081d9205e1b4820000c6075401d84240d0010028507110026a81100c0c59800070914101d241c070070010041c1e101c0410800029402180340d0f0300990680f015143d0001504c002a403103014510f03000c1d14207112004441502d41c0205501803c81d801103100400310701c1c011485800800e050712415010581e9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 914274883 1250 914273633 914273641
    0x6020301080f06061012150f0918150509190b06010809160e0705070f1b170304090b0a0509041101110f031b150a0501090c030603020f0112062c 63
    0x1c2080c03845400c014006900e0041408400c441d0002c501e0301d50a8440d90340d800501f619001c0c1845031024100042281101c0751034411100205c0b4014598122000c071840117000000b11303500d260200100d00b26402141546030a0070a03410403d0150b0550400d0140c400404200000621030078451002601d0740080f0b0313502c00c031880c0e0700c036216a451502c20481c0d40e40d09020340c1c00c2249119801c007800b1728015081810300d070380d20b0300360302e190040c142c9903003480c0e411383d00103004403080d4500904120000c52041034480420203641e4001c070302510f1a91500c0d400010025207a00c24200001c01d0010070031925400d02c0e042c1506a28542e198986c0010807a03004c0e0010311a000400c41410700d608001185403454918103801c0c016140078284019004021005034103c01146ca02c501801038030100091551500c4d0b0014220350b4030052000c1810b041c542c040001d03940f2003148001d208001e082a40040c0c00340c225103401880309401411400840040307045151440410900b50104007050880300c0c0d0302c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 914276133 1250 914274883 914274913
    0x905060309241306050702030d060806060405150a21080a0f0311090a030f050a061409101107080c07050a080c0a090b03120f090a031401050703050f01051504120602030108 75
    0x2c0c00f201c641c2c0490404a000b0000154158096a8030214a105403800c10031000288003e880c001d0344460001e610080c02e0004501d058411660800340c1000740c1c4803070500c0c60300030030b02d02401031140711600b000040903001103528441c40741c410700794000305881c0e4a00701c5080281c05554180c480d07400091802d8100e088401d0100121a0002402050311144600d142d66145100b0303130340e0303104803041d016404020b0000359060103400680340249034405428501000e10034508420f412075039000d18106020507048440c2141183d9003140c102c60001c1d55200b10944180c5070160b0340c0e200c2c40c0c00000c01074000481c40c1020032204104074007190305800720303641c0d2041501550400210298141c0000281900318040d0200030f013120f01c03241d1110b5041601000015144103069882540c10401c44400e010300e072503003031250301c0c1d10804030300f0308014600780103454421003101405924019204141022050420142540e00401404810741c00303805003440c00301e0180d0000e100d802110701c071781581100442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 914277383 1250 914276133 914276203
    0x210c0105070c150f140702010c17010608061324180501140108130f0302070614121f0918050705030d05120406090807060c111b09070905060309 63
    0x80d040600405005001800c4000800310100321070422552408541702e85110200d0007403148040d0b0300005000c00c5884000b03031281e006141a207000003401c100500905030032101980d0401e4050312049070341d040031502600140080c6a20080d603144000b0103284012a074100780c0241e400070140d040b840303442c42c00000d040c0c450a004231a41034000c5000c4031029407184501c0c84d803110307034000400340d907052940794044590003102061b00142c011101c01c0c06499003004d041e002c040b07000040c0c18903006441501d2410154003504214a002181217002b100c80e80d607680c0c1d000075200350712080240800da40e080705445440e40800303c1e40c9004840f000641d074034020031440204649c5448680c42d109040034401ca002000410442d5440c1c3c2d0761103010081200d8a024001841c415000011104007803040a0542c0176401c80b820300c2644051011001525401c280d641c016609981622441e107a8207010340d140d5015400c01074100c03902004118880d50000361480da00c4a808619000441a1b0001c1071128 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 914278633 1250 914277383 914277407
    0x813060e0301090812060a150302030405010b0a032a08030c0123220620090a08010516080a020f0c031206060343020c090c0702090103080c210c010507 66
    0x105805109040301c060001712100e80c020300040480c40c0041c2ca5148441e90b080b10342c44c50100082d07000c0200010040c00348214480b40c4800c44013624800c0c40c596a0b884420022658225041c0c040011900080398080c84036000c0c102c404162612740c800006074500134142d4450412001407120761408082d20034203001070240070311022104c40100700b400200300c440050703001101c0781552807403000400080400700c11040c030f1140b02c20664804820007002000c0b0030b0368110107810b0349010240144c400c1c00d69a4010403080c2d504084c50f5a81d903d80401d002402003e113010b258400c00281c034444c22002000034a40c0088030545c2442940b40c2c0c0c424030a00b0300045a410044090b008121042451851269006604400240c14880450925001088a809c1204800b41e808544010080d03e0708400341c03580070851039151418101030350000f4811010601c400741c000c10f80001c0f0042d808005010038070121503443c1c3c0001c0020445040340413150f0100c181c0d103480303500c0e200108041d80d20070b4403200c000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 914279883 1250 914278633 914278643
    0xa020a11060f1605071d010501030f1a0f060d1a0a060207080d0c02030c03010c03051801090807020f0109080a0807030806060c070b03070504030b01120303060b12010e040305070813060e030109 84
    0x3c1c1040c901c00958070748440c61007660588584000040c0c41004038003070054000240c03d90121075490000050103650140c02c4a424031030410296015450070790304554141c0001b11101440300070744501040c080d22440b115890441d0900074086440c00d591103d00c401840c041c1c410501c8196500000c903160b14150048441942011018080861003500c11a9089000401b40c4104404550000e4211400c000324800841e071203004100d14005d072085807000c3c03034500318000d100c00d01c01540c48918138410504000e100707964200136071500b6445900700002a00424044581241c45400c00e29920b0700140c804400051000e03000461a040000541e0b080042ca000204411424a0540040c58100800300300400800b03200000c08a00f504424900810881c032007800038034500d050040c240c07001d41d007101c0b031260004c1080c1c40005280030003150461301c1640750b110312501e403403a00f220103200c0c50601600b0540040ba00c1c051f0000d00d420160b08444603034490312a1442e81206043c00c3e51003a00c40581 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 914281133 1250 914279883 914279887
    0x1303060b0306163015180605010504051915021b040e06180c030102070303150608130807020604090c080a0c0f09032315040506010e0408090d0f080a020a11060f 70
    0x18040c6640701c8510404c14100b0051201383c103010000408480720300c1c0c28002840d1080c002003100c070500c1544000b08072091001841824286400a441c0340318900c42c050185400781d00100d065031107007500e2806044503c2f0514440700400000a40d290000116a01701501101d184807030f07850544a192074241d0f401c03018140b15a03502c0c200051104c4580040051030048140c11281c40d0743c2880140f426510a44000602292442d6115002034641c0c20110900c40c2283c04c0c001c03142601c99030780a000703500c00040c80d80c0d000303584003080d2540038640c802d410181c10440c03034103215500302c81c2461160310011020801c00d0359a52007184c41d14001c0d000b400225103a1481400844c050420b02c8406444190300714096840551100e440c006000008581c07110f00602840208041484440d006007064044c1e42c655040688492111b4810b59403400e101c0c114024055040180c001405c0b402103801000399500d426170160080d46440820404407510700d0000300100c214a4000300f40c0381c00044c4080424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 914282383 1250 914281133 914281157
    0x1005010e061003050604061e08060903120402060715090c08010c090513091103070815070c240b09012907080406030c0221040f080a05120f1303060b030616 68
    0x29006260251044d90000e451f2080401d10345400300d4164000400201021041490211031504044000e0001c2c0b995420410025190a42003201660803e804940e4250744102500c0c1644030392040b010311100c45c80c10039102c00184210102a00121051640207109102003c0e404a490007142e0043ca50f201a030081d840083d014a43d008851030742c880c182d141103e080c0400000e25004455010405583c013070384034242c480c0c2900171640c0e00b0805a05143c0b00c0c40c42c3c43d9039580248005240d041689461211900185440f41c5d008040059400f400b0030903207507101e821010030003103142d1219120300880e03010440c0c1c2500b548120740e5425045122503080c039052007421400b501c20207204004600c034242c4200da0045111840c2c1095050105041c6d03a00c0345000030402c40c803000c9074030940035600042c540001103140459443c40085c5800a669582c003030350740c0174260700d0250007000301c040381104c1408020070100758807078160341904400310382082d07484507a00c0e50005813400000300041c80980300e01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 914283633 1250 914282383 914282387
    0xb010b03130c030807050c0a0f33020a0b160e400606320d0c030e190c152c01110106320a03051005010e0610 48
    0x2440d00310101031040010180705444900341c0600740e400c00d890782031000800b00e04020040081100c07060b01a9410400d5510704440c021680c1d40304d00c10005d0400d04d00da003219021210700340180074000400490074803504420310003591184250030484084d070448000c0f450340f01d070703003000805288102d6440208220070300b001e210851b601880c50032821000c0c1600b501c0501942400d00030080c0c4a01403001000c43c180d00c494068406690054050041c0c10040450324040c412007240d95003c004811405c15501404240c503902c10340c02990724851031310400201c60b076496082007050b22001c10403106000311042d1200c0c6002440c1c0d40080bc01d444500003007089600c41a03444500100605108218015441942c10110001240c00c00d0070881090102d2541d0781081c40307002000900c400800c0b290b0709191558038000c09040000020000c2000c40b403002892000001c0c612070780142c6541c240c19070b01d207000d0303644414134688160540d040034004a4030580d4041c0c3c86104d0600100308512403014000700b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 914284883 1250 914283633 914283637
    0x71e03060e0307060c0809060f0105011403060a051002070303030b0a060903141f0209010f08070f18080f01060f090b090c0d09050715030f02071709030f0708030a0306080a0b010b 78
    0x203007095400300f0b000003000303e0b4045c412014104881d403280020f0385420001c0504100000744540a103036924001070040b1b9038030034036082407901003615465480d00e8400000310718001a45c00740d40d1101e1100c4000c40c0e13032580410481c0c100c902c070751414060040b14008204603240903001302000100801d0040010502c1c0311002e403050302c2ea50055490070194500c0e50090380074074240e01c50311203400107410001c84d40e100c45c1d00d03c0d4801c481c0c5414111814441e20041c00e2400303402e806001c20500e400700708005a940c0c040301001349460412515064400403040b8040d10880c860300320120914a80000d9146c114007aaa08066008122110690314403003110382caa00603d04044505030f80b00281e400080c030400c1804003801c00b80c1c0000401c0c00001e18010252a0050342c0107004500500c11900000c203000c4009204061000b04192142e01d1a0b0209260040e6902c600e0a64801d4000000d031441c1c02000408030061281c0d007e0061540320050959616140f100007005c0541c400d004210004074040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 914286133 1250 914284883 914284901
    0x209160e15120c0f0708040f0608130b090309060d06090b0907050a03050a0905031209063312060a0e1c020c010804052112090703081b01150e0603071e0306 68
    0xf5241006070010b420443d540140208035800c4800150504c202802c914003c40140028940b0544070300e08124040c6480c800317203800030070000c103240204000350801c0c0b044e1540200040c5c500c545841a419582c00980b11070f100e0401c005107032050f42d496508100c03101300e1150060361601c500d070105800c0c0480003020020642e504d036596035180100000c4051008001d000d0b2284910034803818484030407420040007510424108092201103078a54440f6500e10107000050b0403034059802071100803c0780c1000818007000c241c01400204000261141e200461030105502140d120282881209800098140020015070b100e910a55a958490340980e42c1c424030900c15600c00800e41d407160f100c00741c000c0f080ca5500b01404141036801180d502c410f503a1001c800c1d8000d0001f60310b0f41d180c40105124500d90100342c001182203182580b1300c00d42100206021000182c4085562038181c109161800e582c038521030300850800141d01106225034070240710b00800d0140030145541d564030000d00540c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 914287383 1250 914286133 914286151
    0x50d06290307231c02130306151a03010f060c03080f070c0b1501023007030e09010b090f010e0901140409170a0f021612020301090209160e1512 63
    0x40300084050042c80c0441c191258003902503c0b099810280e42c0b484e82c4045850441e1413040c080940b0030340551b1160406c0b00e40100b80050030190000c00b40d9a00440380d040200f80b413554a12210f15400c00000541c1210340001d6a4061991203140441c0c03c1001c2800107000150360f60085580159152107468001c40305007454050750307a15581d01c090b03501044418004840f05032100d41105e503018403403c00d000403030007410f030454540c9580215400c611304801c1010101c0c042040c000305801040a00c15410700101102195030f51041c2540c80b90b4842c0d500d25019001858174000d07154011200f0080303c3c03800600181d080d0707003003200d250030210081070103903032294940705400c000c9299041100c40310200082900c0d50ad280342ca40280c403200b03011110404650004e410304903c4c0080d01072140c20f8500c0044036049000e2035000007400343c8101c580103540401403000380300903400300a5400314540801d803150303040c1c0e00e141c00c100010009055841c0d41d0014081008c0c41c15a100c800e1607981c820551 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 914288633 1250 914287383 914287397
    0xc030a020901020c210f060f07030209060408010f0605040c0e030a03051804090506041101090e0a0b04060e0f10080d0c080c01020c0a050313210609020102010609020a050d06290307 79
    0x140d000500c1e091462842c0c0b0020160f1450740c0764517072006001032081d10b60400c004040364100b2101414484600801584c1010782c01f040024840e61743d541110024941070000740b11218042d000f00000780501d129441c0305520b003500c041001c501603ea50b940301343c030041c0581200105030701d09883d20f600c07240011007c14041d0502007450b50b03e61054920003401680100041c0c601407500d140f0039503500300e016051001034201040b002444105560380540000004101c120452001c14050042a0003612001400c042003003103001d2010b04441c401c1d040b50000b10801ea6540440c0d94442241c2c003140c034000360b100000704000c03c40c0ba5000b1326102031800700041c0790032500717245c65040140002d4100c0b8660000120340402c0310007100d00e00c0141030392070f96906040321100702d000d098440c518070042819031644084825a8000e41c0014000c1100741010b5668007920040244540d0152051b40f0603540f400d400031a8444078a20262100c803552411780416107146d102c203c01e1a000100140100501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 914289883 1250 914288633 914288653
    0x70507060c0525060e031204120207050a141011150408070b16080708073f230403050906070c0812031509070f030c0212040305240c030a02090102 64
    0x14108a140b031440f80381050500305845103840c00070358031040810800c0750f1040c407800c9401342e01c3c0e020040c1c020b40e00110565030041903110036414006194000c5174002d80344074000030703140c40c854011503000000303d980c591130455035002500e00a191118407500ca90000710b480080c900c1c10311030203400c42d0042140c1e0782015010b903075001452400b00e80400c2e1000d11940c00f004055041107440740c0101d85400e000d03200c0e00d8401401005101a0241d01264100d040b040d407070b9005007180070210340350350b800c0600c0d8038000805031800600b0002e644507070000b41460107200855100c00c4450b018a0341076503110700e0418402c0410900381c02c070305c41c207841c030034201d0100003035094041100c54144460320a016407249001c0709007010411048a01ca40100d409034200015a944030141e602cbc80e03411800c00103900070b004101207150030341a0b414004a407500150101c1070201c0010300400151142151070900c03c400050540c03486da017603c90103d40e0405002140074001141c0143c40301a1043c41152482e200c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 914291133 1250 914289883 914289907
    0x151236350d02120f0c0732010b0102120708041412010219091e0509070507020d11151903110d02030a1401090207020f040b1f0207090b0405070507060c05 67
    0x488680059441e40c0d000401e50031081c204078006034007841380313200d4210514104030300021070311415000812510980d00101e0f00f8881d900045985d510f140300b10b444136900c2c000c0d840350080c2400700c0d009015102d40e404009170311506004a03800d440d806204541043e01d0541c101c1c3c0403800307a08000d40e0080141d8007480030b1220034030290600002940c4440320406c3d803210060203148580d04413910100300010200288440c92014804032034003911142c110b6030311481708903028083d200c0002d40c4507090310316003800d0080221700c182c0f5560003103074075640200c21415401214131541c0c0440f01a0700013640409110341c00b81d4000707140a85030616071880d000c44200003400300e920868220001950b6400710104030414003a0483c0545100242141f8014091f00011050301c0e0f0041e04910403525403280808c680c40d0707803410081003a0f86402c1002c00c80c2e0303211030103074446d030f1140a0890b44034549032100310300c0d1401b801101d00491301504e815142080380d03210500904400310418042c800200f001d08807040f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 914292383 1250 914291133 914291137
    0xc0d020105090904150b0f01050304033b0414100b0a05070b0112110a05060f0f07060c05180103180303022d040f050301060f15123635 59
    0x64414400c0c002035981c1508594100c1e15410380311b03401a0720214400802d80d8002003100c4e00141c060a00700c488024070011240a12000e10102c5010004e0f040144801c0645401424102c90b0468081c000003c59030113001021104442c1c00c561603a0603602005003a03d11030061039800c640c0d18060340b610015403a484101d08080e1b1001c8055150721080c82d09008901c0d581c01c00c4003a00303e0340b80d81d049103842c0000b10a4003e01d142d01a11050011342e611219101204a48505030301841c140207181c40300070f0290043e04a04e81c00000f504680640c2c5d44958801c1c4a1445000c103010b20a21400a50b910106c0007500546110103280301c0c0c5084103d050001c420f1004108100d6520300d42e610b60411005082c401801d40c0a14026814404240842c1511042c00b00956104c2d042541c1a4030702883c007100c881400b02c001160b0f40317181a00740044080d803075480111442e29141440c0071048203000448200341c003618050700c4000405c4441d0014600f8400c041d200404070b201c0e40c1502e0700e055403e170002f6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 914293633 1250 914292383 914292391
    0x130207060612110d08071a090d02060f0621010c0c0b13020919020706050108030d15080d0c0c0f06180e060d03030b030708060f01091107030504050f011704230f0c0d0201050909 77
    0x10074180710410400301401c00c01089c584806101508150401c0c118003c040742010300a54130039203030300c5a401c0340001c440c0f684001e8a00010000d211140f60340c00080c1000c207a0110030764801100300700182c900c580020740607200780e40c0a07200794510380e204907001910304070000f0000045a02000320744042038480c0905070280280b1300c0a1a610040241224210b40f07080303400d01c015880c440d0b002c110030303200031030403003405003080c2840c2c07074410094505142da854040e00241e080719030a0380c01244051748911035082c003d90b4014011249621160701546001c0201ea4003907014280b5880030000030b00c25006002100c501404540c0240d4480382c060b03081c41400c690001030b1000210040040041a000781c58100020340d0840d0b251600d1610018128411f47c003c0500400486080340e490ba40329400d40680c0d91320384124144142414682010b00c0b07005520074041c0114803801c8840c60140100f00c070b6002161050003403a980704682c0502c07009194000c01a4140f050038000b105017900c03002c403141c0c86 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 914294883 1250 914293633 914293673
    0x4090203060f19060509010312031103010b03011505091c330c09120b04030e0d1101020d03060b1606060302040c090303080f0c0324130207060612110d0807 68
    0x24a28100c854800080d03140c00c00003d189081c040100140d40b940c1101c41c1c103607504401d0701d40c0554090801503001c1c1000b0782241c1c284001c00800061102c030500040e5050302c10303408603446800710341242160640070360503600340c4c8405288000040c0c030009021502c40644a0742105080d00e4103103504691842d0580a503069203000c003040d0741c800030803a01c20404041001c3c10300c1941d4030b04044c3d91206451600c9802803030402100f000c601894010304240131014801481300f083c10f0f2071403501228488000040c00d001d071142e0705841040b40e0082c050001591000d8001a0070145c111400d40701c07600000906682c110350f10240480942c40d54003500d0386071030701c540364414110b1842c54010702c2000018540c02c0050242010701482651000c00c13a90001c2c289020012107003033100c0043c20080c0c0011800ea4425020b8460160b4103680303030058800d080c081c1d08100b000301d54661042501d07562408000b0450380d8152448c03041c0e0b10302036590000c4e9030302923901030703003041c0c260b6480202c9080c824070b03c028 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 914296133 1250 914294883 914294911
    0x182707090e060625030c0f0c090f1a040c052101050315070210020a1826010207050a08130306020706051801020a1d011b061b020f07060c020409020306 66
    0x4041c07010716500d03082481038545502e4581002c1c040420418482c180c4c40384408141e800a09042c4244200021903030880700e1001c80030030524040310102102d2050040290030460350842107042c82c8076200c13101070700000c21405018910100001005184040303c02d0103400d2100366840d05141d601c8180c4588840d0144d8001d50501042501d0000340d050b141c0486074841e01003140160b03000c038008199180c000d8000d615940c03081c90589039807481050201010700b21540c00110383c20351100402e070f10103055042c02001c0c054030800d10709030711940320042c22542c08041008c1c00102d654008240780b0015101c0c192841e5166038074031041e81d104039426035034030781c4460612803150303210214a003020914500843c42c0043c0a44042e00c08607035120b01d281e0026052181c46c919900400380e0740d00c21403000d1001007410b01c0a240075030091040d003182c000110000405001c0c9030b80000b900880c00345600005015040c5410400c0301d405040070002c07a0440c0d02d50072a140180c030f080040a024008034070803c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 914297383 1250 914296133 914296139
    0x1c020d0606200a0f150509010c080105042a020f030c01060806060409150f0e01090c0e06090601080a0e0a0f260f1806070f03090303120218270709 64
    0x34802d14140d4000520804001c1104103810b00c001a03407800a540302c40400144165410046052515015005100b60400301000058941035000c40303181140380d11084102d07601c0f1020b00003200c00011902d9108450114201c0c01210320300c80038013100c2031600c1221450904080c240d81141c000c000c130f103d0b1aa44607a028001d90105100132540410306440c104034064072929003004250415103002e5a40b81d40b07440351040388585030010703059191120300a202c420b889117410b01a4030841e109020300004d43e075001c10020300c0c00c259902d000d00c10596440501d922a40c0b510001400c5984660445200366054800041c00c1c500681d111035000f06440d4407484541d81c0c0258245900c083c0000c0400d000b08a00b074541c10f1118140c07910804002441e000c1c0c461010040343d0307940700d444006032280ea003001000c4101a0300c10f600c032098a2296541804422079181000141e01445850042075030f400b1034840d1a60500249140000340c52480301d01d06141040c444a4807150203413603000001d29600414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 914298633 1250 914297383 914297387
    0x50a060911074e02010c0e010c020a0504061211090403081f05090106050a11070323120304240207030509040b0120211309050717100302010e060711061c020d0606 71
    0x40761200f8600e000138020a42d9032403008200540403041c0c6418006800c03400000d41d2180ca20f100c1c05081c004c1c004000840d110360206e9003c85490b030044480380c815000d0759000341001c429681c002c9626440f42c90103522401c0800c10404040c200c081d1401c605620300041c1642d074045c4a80c000d0029450f610f0340c03014080c2c0010508140300da9a003daa074842c400401c0000c00c1c412110301110351a0840321680701504000c107050603000d44010030140c0e0084180b00c1070000303403030b80207900203e042100d4044901d08450742c0180c0c0100c50300500450f50078048041c142c140758000e00d00e0203034145050110074100f140e080492001d120008140c07503000c0007001d040c140c1074029402c5140103000c90340d8240309842842524200c100c5c01a07811064079140441d030300c28041ca070458191030b10b40360440c0141c03030604404403a1010902c420380c005014460640e2090801c2c004890101d500410044807092480041c09000d9028102c0c10040ca0501b45000011451500c0a0441750ba949040071032507600d80440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 914299883 1250 914298633 914298773
    0xc0503120118141005040518101401081902090c0d0c030603050f0c06040b1803120a260601031a0406030c050f0427020402070c060201050a06091107 65
    0x610b10b00c041d486001d01c4811844d0301e40442c120340003210007190990300c543e8140008160074054901c14407480348141410b001c9034100720300001008104800d144e0303031800d040b80c1e00c0e20000ca511400d4600303048801301600b419601360364071400c80381c5414a802c41c0e07800514119510016003500180d5990b03018020440c0a110072446400c0c4080148000103000300000e280748250321551605050005d004030f5480010665204d1901c00101543d07044000001d540300340c1e0380201660703000120340112010b0203604050303038000100341e07420000b0501e031380c0d0303000560091a030450140501c81e555101c04607580c1d070f00e024100165100d802138454a41c0340c00207000c08100c018031001c0c030440c10300040002c26440a80000c440742528a00c01036020081d0010800a100308100507141400c055804a403603030301508014010045090104842a03440e40203000b200d110000d132200802c810400f80740882c0011a004491201c000035002440180c00010300300300e04155200f10b015040e00300909202d00d26061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 914301133 1250 914299883 914299901
    0x40b0105030c1606060812070b01060801062106050402031314030a0804030f140721110c060967061e060911090a03030c0503120118 58
    0x30040d045040004025407240100300307200742112440b046560a000c0c0c0354005000400c1e80e10282c900441220040500c1c1e03520501c0207883c2c03c0e0003600005801c6104000c414126942550790303409422400115220044010350a0100f1365141c0c00302240659480c4020350060144015031450501640385c00c40d0204845404030b0b6081e0000d1203035401550304446c038280d101e5410b14100c010070340909401d07100b420800d02c29140e080808210801042050f21100c43d0200d0a80f18002c508a2150022115680c12200c5080b130b5400c0941c0c2d072800f9003000805010b0b2228001e00d50451030884d1a9808222400e1800e525040400c0c0d40c0b41c1818410031544ac07111030510188500d4400c90442c00020341d00064024a200560030304149100b8003207594000c04c0401c51f100a01c0725a4142e054801024140364020065003602c2c103540b111a00c61484114ad0380800c0c094101400607245407415580650b600d5001d0700e050004102a0440507094a02c00c0d02070204489080780003c101450b01c412140314607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 914302383 1250 914301133 914301137
    0x3020d0b13022d030f0907080607090f140120030d0f0207060b0d0f111c03020607090b070b160903020d0803040303050f0f06040b040e0f030d0f050105060a0c0c0f0311040b01 76
    0x4140d0320500340158046903032003040e2103191740c01d6480d4240340b50f01c1d01710740d9800b02507903000e90824040751540c8110050304542c1c241003c0e00d02e10307440c2c00c581e4a501480102e11030100708004031201c480016114000810140d43e026030b03060003500b815480c165006000359002841d80000e0060800c02c10344500c81c1e44000c1510f58806080c056601c4401590009030044c1c410030f1000c8100015640702c10081d020a5074525417070008021350703c1d02130340d00e0600b5140d0700081240c40c41e0210742291386d80e098566140d0003001050a40e12048080c0c400d07040502a00000c11107031140120242e124a00c40d01e010b00e03c5025219501e01c0e06050090444034082c207110700c040340040a2148179103a4850140d0042411140001e0080b100d00c0014018a00074540e100180205a044001d541001c00913081e5044514424002070f4005841c1c041103480c00d000c0d40c2e03848001803143c0083e041c483c901c0f1182e89407140124060305c9890b5190a14a40b03d070b070b802200d0012510407500c41c20f082c1070041011017803080c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 914303633 1250 914302383 914302447
    0x70602010219050708070602040306090b0105060309030d11130b1314090703020a110f01063023031602031905030a0c02030c15030403270603020d0b1302 67
    0x1070700700c0482d00070915014404004020408006201c12081110359542d480602195120750300d181450190021910a99912003880e00016642c20900103c074490783c8000040c500e05401030a507100200100000e43c070203010f0034061007012540301c20301d42c030280c03500000d85600c03000450007083c0800d400d41c2001c0c0ca0510300c00d11504040e01d58083d615040315031410003584401100720200c842680c41e0322041e44621596003044490300040d480710040d00c9a0400d0450001c518107501042c01c040585901c000030f00000010700480e05403031b1a8102581020389210360410f0303001c80c051071750300406403417a80400850701e203104601d0b0400640400000101d000803400b030094031029100d010358a4150188098500004110340d813301980da00710704010001d41036090300c00712048150304200c07000c42c00300c0c101c203e280400d0540b02c0300d0001c002d005200c9110301c43c1d0503c1c0d0102d000e50000d0040e600c01c1c9480701c1100700b00390385035000d000401d03000705001600c56901c0e081c0c00d00c01d5541e040b500d80c800444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 914304883 1250 914303633 914303647
    0xc0506070228020a180902040903080603120414040c12020c1b031507181707140a0b0702130b0d0317011a042918040b060a1e0905031501080706020102 66
    0x4004c403250071103c841400c184100310000045014010800e0001c0d802032402c0114410150442d201074020f0300180d0854220b07034010100800c0f130748600c0c05103034034000c03088031501143c1c581904015400811803404100c60450b0442d0705060382c0054035440d2194203c041106801030f20301808005416080300102801c5101d24101d100c00080900307039404014940744541c429181c40000c010041141e040000c10014001074280d45850b0302c4d0040000f50402078041ba41d46260610700381003a01c070790094113880d00c03d450f0708001c0501c0000c540c0840c0651104803002140e80e812060121503030182d2151310b4400c035120540300518205810003420414074106c0c030151401241d05a4098400c014114003401c1d440c3e0480701060580710320078426125000484501c0044030419580340c55170151800d00c40340e40d181e800c220b00e80c0a01d840910020ba24500700c41c04e00500c0c81c0c1c001d40b12803207a09000c0300c2c05880b900030070708018034a001c0d02151440c0900410488208012240c024861b5100031410044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 914306133 1250 914304883 914304889
    0x14150c0307030e0705060408031206040903080a0b01030f18150c090e0c0f13151704110406090c050901120501050102030f0a091206090203100501240c050607022802 72
    0x4040c0030751041690319840c0c0c5898020401c03c03400588030003855035072519075036103c03984e495001070340c403a00d03c44504011600c1c50416000f1100400d626072241d151a07610a0441c03c0240319005500f4101600d904910041c0900d45c030841500c035003400031901004006007429914280902030003000e0901d0101111041548003540b282582d050007025106030320b480d52203040c6c81c00380040e404103507040051141014020030035810f0484e15040890084c1030321a110036100501d0751280454104071038400100055001c0d80c8180152074002c0000551903154440c28003101c9200302c544012401c0040c00c00903035078114055000ba4a00c8990511441d810800000e4680c022139400d05c0910402080c40c002190180300f040018002070f40070744402d00c0450506d50042c10700000140e019002d40808410084214000c03103041e40c2c20254460020a50380c0162100d1000100c04e03682000188a81400018004e0200070700032201980107100c4500c0500d0040c004003140c180c4200c0441e07540381c4440040c0c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 914307383 1250 914306133 914306137
    0xb04090e0607091a090f0604080105040c150801090e0f0a060c111b01140d09050607090e10030215160c0305060610140a09080d0c03020106050d080f0c160314150c 71
    0x40070420070b80ba1a03c0f4010302040c41d01b540391810340d81c0b0520106001c10b4403070b415030002d440b9501036001e03001500d43d1940c407010b0410080d0301043c0054070480051085c214030350002d40b1701c58255002c8450030a041080382c0d00307084500c141150020380b60340c1c3d0b100001d0b41c0001d6032200241c280001d06400600500e100c0c0b4410200d0300514140406054134040d00b089040546840b00340440051101200602c1d00903103d44040b2880c00100c0c00e604401305030030a2803001148140426801401c0c40b609640811420000c04641d08201140400501001c6e4060100b0300024621681e51002400e041d490f215090440062006000313880ea10110911701c0c1d032058001810b184a52403184da52000b40b6421140341c0443d401503621391054000200a1941c499000050280240c0c0204000381e117500030814244000368024052150503c000031101060000900c000b0048604131450840740d07601e1541c4409036540107544240721114418a4807005000d0401c14035032060740d1040925080360022018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 914308633 1250 914307383 914307419
    0x10b0105120612030703030204031b03051504080408010606020a060b0108240429100f020c270c04080c0105090105040e04110301020d1d0610030803100b04090e060709 73
    0x141d500c55000c9401501d900c109290b1403003020f82942d50361401410042c0181d4064402200e80e001c603042c00c2000b0341c80d1400f032502076039800f0028100d804090400304060f024080e00a6901040070000052b40d0103091090b90028a625005807402c0c10300c0c1c1c02d05d03204071a080a50b0034180014041008041404040a509007115036150b507945668484081001007101c0c045d81600410100701120405414110860000c1d4048849c9650341070ba90608803036111003040302501582c0107264060785413070000d10102043d2203010880d14210702c000c54265081d8819140c0c441b5076940003074240401002401261455031081c2051031500342e561000030320622441c455100012a8080840c08100101d0b0202c0c1c03014200a0081d52a100c0d4043c2000081401070b00b0400954081c0d0001031800802282041c45a0110b00380b8990480c9140c0b03c0c042203920080c10945c44031403501c8007185c0346074203c01030800b42c140302c500018181214401d69141010103004081800b200701030400500c07048416854030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 914309883 1250 914308633 914308657
    0x40e013f0c330512010e0103060515152104080408100209060f0a0302121510031e0c0207180219110a14010b06031e01170a0b130209040308060111010b0105 68
    0x20b8080003090031111801041c2d0340e000f04203442c8000185014041130402e050700e0094400b003000342c440501c034000d90f1600700612134101b180c1b070002040d4640b420002c1c00b074038805406003904030f0707840300543c4415400c2100c1c2150b6030720001c0707410300c0940401c20001003080c0b40b00d502180b038036401000003910b41c05506403413213042c03000081200b4507500c2501910034407001c2e02c0012101f030902c88400c521402c248850507000d038a2107030150900c40c1c86130007851068010500c0c40300b4141841d000c0000034209020550b400d41c46600e4000540340c604801e10058001c44940040e154103002050b0314a0040f550780c064100100002500807040700450345411079a4800f640864011102201c1805440540f40d016408503011041102d5501240d140701d00a11461040d95a2a030700e841c0c0d00701c12000c0c401130204084d8000006070000650340c45869402000600703422001c100c40354005030041c042160120005503807041803252030b5070000c894182d0000094024003880c003140c0002070030740c0200598061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 914311133 1250 914309883 914309969
    0x3010f0b070212030d06061d0105030c090a0e0a09020a0e0402010503060409050c131d010207031d180703020919120b0a0e0111130b040e013f0c 63
    0x11566046821821482c11034141c1c1c5d2903003920442d080081080e80302d0b00d801302e8120901458603101d60034001c86000e00507102c0c02d046440d03241100a141d000800110380101c0ca0030130120b040f0040035426841a4903035400400c500ca07041c81804035a501503445802455821028800143e07040740c1682c0e88680265000074500342030341070031031900c40000405500607e030f108405030509410b0f0040c1c5900c920200ea0400d000d5000c0c02828204c1c446c420001d0001a003540401c040c42c3c041d811000100c0354003c11410317a10b2188030500e850b1400503502580400c1d40052412058100f0035202170f01d1104825025640703514013218000d92003030100300281100940c10001d818100d40c2c0e8080788090148400170040703044141102e0040d131b4040f203040b0317080c503004107c0000c0c40341141040790180c0e071081c44c100d150360f482c010300541081075a914205065070f00d001f2003094015910000120740030610400c040c11206801c0c014100c503400e8200361401d2034100c20090081c3c0074020001c56540307100040007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 914312383 1250 914311133 914311147
    0x2100e010e0a060203071703150d0f02060a09091503050c01050c160f180c1409041d10110909061c05061612150918020603040b04051203010f0b 63
    0x2589052002009075002c08503030004510f5660000240203c0b920401e6100f400c03041d00c00309041075020480d55140090120701a040d030314104102c026050900c80c2c2e8100442114550024045403c41c0c60b59000007001d205080005980502401c034003105801e400c1c141041c2191070301d507100e4a02000b65130621800045840d0351410411070342c54620f942c2c3d014102003070f440d414184a48050f82c4200c14041c4074004c0641c0c406400e610400004400710384458115408070203002c1040e81012510340e034840d6450b0f4004100c0b613030500e10817414a0a41e0054081c4540d1020380d141102c2d4801400d40b0b210038184407442c91512200340381034000e04201d50f903400c900040c00014940244100c002800d500400060058001803d80c0e280b408036102c1d00c401a040d000181c18804940240040328040521010200810b0145070b000707007a01004e02c48078191b40101174000c10303e2503105035821501080600100002d101c0f00b801101d200c0d001035004907155515205548001e40c0b59030086a2484000113540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 914313633 1250 914312383 914312387
    0x250f020103020f1c0b03060601080919080903160e07141e09190e0115050304150e010908030103050706030504210e0406081b0105190e13060807090e030702100e01 71
    0x1403003000d607044e0b0807250f40c1000046100d02510004003020f0286c490040415143e60007100002d00c2802a50004d000720092805000807658902e1020740b49408100300c440000d4400384841d9400b40c0d020780700d01464034505050010484001090202001003265000000c803071039808807030701050007109443e400405040114110321a0b9030456030701100b03d401e0080c10304503c04040048400800c42010141c1c4c2c0c5200b401e41d101c9400c1c0d1a0310015404200080004220158000e030141100307000098514070415041e0031559454030550f100c03140407004104211081009001401261606201d24240355450200242e0070083d603515407540841d0704009680b1a010106984000400c180006a51541c141d03807100420310b40003c800300380a40c0804654060401c0391880c5441c003402900c08182c0010446040751201a0306074802c4170215401091011070184001030154117010707003007481c81e0606100403902d820602400341d4006000d400d0160f6580000f840c441441802e10005140000d401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 914314883 1250 914313633 914313637
    0x7090f11161a0c091c05070f0317040b190513141008161805030106030b0610020a020a0506032208040510090e04030c03180902250f020103020f 63
    0x5080d064004264441840001060841031a001d06103000342c8000c0d0100c0e16507045000c480d543c2c06080c1c20808039070181002c10469100103000c080c001c00724006030ba103250404c12240e0040c0b5040581010520600442c007008508910a101005160a2800395180003d002d8003107581945103452171160074480c05841161407000175154404c012a40b94880820504075050407030340182e40300b2400c0d220031400780440034043c060050300c400402a1040c1f003200c2d0f1101c030607083d000b00d000b80da40010780c5490901449015511581c0c1c8540e051901c01d050106220680c0d0300ca000b190302c6200000c000d0384441030300d0f9058400903120507035030307648811400441b650031408110903034031802c42c08030503c030500c4098000e5034002caa030007012501540d030403508042c05025002c588200100440c001070301402c2c15000c0d080c0300e8180810200100c052506400c1d01c203500454919800051080070704201c082400b142c80c40550309000c001304a03841d1280c82e41d26408000b07042c15400215a0a08800e80c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 914316133 1250 914314883 914314901
    0x605091b152107030f0f180b0a270b061005032a120604060b0c1207140303010608010305150903030723070507051504030236070206040c150207090f 65
    0x641821810b003003c008004000040c4036044c0d981c03514491801107a024001c00780004405107055060615644a03072034020405030440241582e11104610350101d1581900320070208507200c2e904501850816421101c4c009104a01c00c01206031031001c030070f0300541620380044200390140014610a030603426886030880c3c04c11210310003c101e00091345125601e0920524007030302c060060b5a0f0311400c0c0400c0d805142440740c410340203040810b09114551000d42041030184820704000c0400101c11821540283c11000c0000d03510bc0042c000e00a08109804460b8840c00c503407a098035054035825102d000141c5240304105070482044c0207011610f4810b60584d01010b4080d079591040d1401c40d0b5039030140e104030f9016403d80c1000d40c201500842c2503600700c1e500684045042140b416800b0483c440c461080c0c5a1211031000010082088140e00d512840d02074006000904207400c212440c0880703030340140f03984030782c0019a00302d06602080c0c01c8110303540240040b560303140b03100407600a482440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 914317383 1250 914316133 914316187
    0xa0807030e150c01060e0c07080706020409020403081b0610060815041a04110a09181b080403020f010605032e020a0c0c06170103031d0d0605091b15 65
    0x40002c4030340c1d048090040a142000b4002040074580c1c98844180068048484200201e0305014900c0882c94101c01051464801d58006280a8841c240304040382c010350800e4590404c0440c40041510241901c41501d84540008103000e10385070701d6004550f0b1050090300e01304062034020402400050000a6109100501c2441000302c1e00908031055181c40d1100ea00c61400c0036484450300c00000203e5104001780d58420343c6840c10950944024010b10240303c452554804040b0050034418900c01c0315418103954000f00c9007007a00300246000300200b001f50311645003120800240d6000594401310034000d141503a2103c2c416038065600400d25040b028620f400020f82d003420991120b00c040d00341e4803d041d500465a01c1d628102ea1026006040c0240080424014404240194141000404902510490034030120081030344207280030400c8440070f8585081c01858001071028540c148440440b40742090105030004114040d03104401c4c4160074001006002e0022070305072060030310030103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 914318633 1250 914317383 914317399
    0x9010507061b09171e100e0d2a03030e030c0709060302180c0f090f060c0a02040605120307060903020a1b030c0906120201030e1908030405160302030a0807030e 70
    0x2600d00316154800294a0800055442001003906010b0041e001076000d41130004003000c1c085561174541d044001422100d0500c21006404148451405910380990a2030f01800c5030b1062100b014082141010541aa0a208013188800c3c0300da143c020b6250700c1c0d0540b0340444c3c06102c07108120b00318491171400d110b641c051010085040100d0790030840c1240d00c02d444c0c4a018600c20480151642001c0c0c5600c0e131845010010086104031846c0a00446600207081d544005001ca0001d225584041e6445d02981c100103052025450b10b8410040200f030103403940308080100745135894482c40380c0070004014989c0c820050b0203044c401c008094510b503110707600300c0540c0e004c0d24003540d0181c003500c8102c40054290304049000305150180400301d070030103188210744100d1a801074002c1c0c07441c6151032100344994481403100c21494080d6a40c0d081c0030301c00b8a60750f42010304142e0f003052551002c18010310b40344841080181c5000072150f008070313004000d650310340d615440c04032492403514a2996200c007207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 914319883 1250 914318633 914318651
    0x1d15043312030f020c15160c171b22050601090b0417161d1305010501061706010504030f1e150c110c010813080409110a0807300e030403081312020d080901050706 71
    0x1c0d040c03060202b403d402a41e000b219010062003981c10480380600c0490121086003110041d003001e500007134141461030342c083e140c0c0400c0c0d10a812640c090440e010078014030030a0364206001000241801d101d25003021750400045222560400040e80d464811b000000b41042072802d160050b0700d45e00c40300a101c10b507510300005000c080800090b914401c0700002140d900d40c050812941103950080e03031440b00d10b00030b071a0000c40c9005280b4000b4410004a0700c44005605540d00400c0d1480e0043c00080324000c40300c000381820100c0e8514622680059143d90203a07030000c101c0d030791200b040042621481001d02d451107040c019540003d0032641420303090b82e942d26825000d40500c0038030b40d6946280d5511540101d07030b440d401841d00050601d5000704144094088182d03100f20203140280401c83c000103c00d25071440e406940140d13155a000718030340c0c4210340d400c844c002c01042e0a04502011039800c0e0000340c0c90500600d4002c0c80030a0018001c156039002d6415900c92a0704079804002281c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 914321133 1250 914319883 914319929
    0x70501020408060f0f0705070602160b180a150e24040303050a0507090e090c0910031406070207120c1d15043312030f020c15160c 57
    0x10780520607050141c000080e46180c00144110300c90410302c0a0805c0d0343d00d4031102503031158807a00c1d081e90020340800c007549102001700e07424002c9912900803405a8581401d604524001d001c1c032070042d50b00490041d1000c01c462808034070940d060342d24001042d20281100714a040f005d0741d41404041c100b0551b800b51840d190405612490107518240025074500c0468030884a0483c0d0250200d001c45006100d841400c040199010382d004040754071004e032060002d0101c241c200c42026460700881424000c0140ba101e1002d40e0031a035800514007400c1c00c0c10007030344800880c0600d0a85c55074a0818406010014801d100204110200c0144180da000c5d040950300c84210b035105d8461003840d00358031741e6003003034450340104001440c501e45200c1d091046c010b5407844960641009141c40c000e0101d494881100381c50b030090701c00e440d6001c039131001840180c10b0544100101d031150420300e0000020100b8002100c0d56034140b910a130181900320f1400501c0d001c0b00ea00640c200e180b10120341c4117100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 914322383 1250 914321133 914321137
    0x40807030b0a0501060302040303051c271101030b0a030b0402041d010b0102010b010504050612150418140d050301121a0924060f1003060506130323032d07050102 71
    0x148120300c140f12036a00c484040c1d080c4d201c0c5120040020f5402c010090440c140504030704a0414500000f00b1b0740c5481e0030b03814072150340010300d41c0c500c000c0c05800a010410045d80e058102e00c5d0030b003018000705080301d002030f50700042440045e003d01c420f01c00290842d55640e001000c500b07800400429a94915178003540200044074003540503629010400100358000d405a2b000c130740c0010314940c94616074000490040001030420a0b43c2e600001c800b02407503446001e0765a66a140c100341000c08002c5041004001068004105072134100c1607002081e01e0b404411203054900007030b21500c1c2c216061800034880c51010b18a04075a21560080c0080100b0114030b0100d5603502e8040007200c2c00101c505411800d10070346501d42d0041c0c640c8404441d03800c0004c2140d003a4482d0741030000309a9a2a004608580d11110080e9240c03000c0010900400c2844411002006404049400c000c0c000c141066500d1251540e07180b810501c2c3c210a110b10802c031070a4006c07100341c21a1083d1140c040c3c1c50200d01075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 914323633 1250 914322383 914322391
    0x80f0d06090c0206100f050d0c0806040b100e010602060114061303080a02240412170703090210020c281e06030608030304050c0904060f0207050c090901021206090705040807030b 78
    0x60080302d0105d13010449010a110940d51341189800a8605d0b050410220250b50306080360300c1e8074026000200b1200030b110151055000c3c2c504404070340b601821941d1144140d803c51104210040010f00202e82c2c002132460640303058440400c00c10110070300140c440d010b40300c203032240c601090fa00032040200c804d018120000c25034080301c40c050854189950391904240300c6a112848140c00a001300b075140e041044103000034180015000340f13800300840f464030216461404252120a28411400c0018611420070742d1480030b0b10981001d100056102d2041c900c10340c012024440c0455031031494038050390004d01020116840e074242c8007011030800c0515204041c00720f0302d4a0300000c2c01120100031648650350200c040c2201920100c20048520005401641c51540d0b40d000b813100c08665100811505014070020b28002220508001481c0c40003440290b459005002240c0841c0002c03140d590815404c44002d14079036030f1084201c805000d81c0d400544148140036000040c080042d4682e401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 914324883 1250 914323633 914323637
    0x6080601210608010b030d1d01050c2a010906020604140f0d0206041407031e1104020d021902030a12051905390304080d09060c050405010320030103080f0d06090c 71
    0x217001c1d12881055141c5e40400c065001080c01220b4052440c041d80440402800050402e141040c00174542c9620303000452140030500070f91015071482802c005400c4e0324900cad2091900d14055030070b000c8025160724000e440108100c1d00002424000780c414080841c402d502501100daa031002000f00030b542c0c4406482c141c0d0b808116200c1d14420420104004040d00c0e0060700b00d100c103030840381300105c0440d401c0c40265040030750f0800940e11940d542c0020407014520b4480940c40d202c0111241c1207001c1d0342c4481009561040180c0c003101500520045010030602200003050f6403020003041d110602481310b103c81516050810140c560a202040241103c0c40ba46100c2038070440c490306200c00d842d207100381a01c401440041c1c0000c200c54000e02080c058544042414600d554808066906850302c00004c0341c0d02080c180b25950381441032050010401c0c1c13605003141110717007004000d03100c10300002c0c040c480b0000310070416100c020102c03100400594800c01001d82d61b0302208000345810a010381c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 914326133 1250 914324883 914324891
    0x40c03020405130c151407081e120a05090706030e0c040204091509090209040f1a0705190302160303090215030108030a090501030c271d0105010801061103040608060121060801 77
    0x140250300858151701c807601580700c3c20150609071011130744540015900302c856003003c010052003038200e94211344081600d40c0701e45071034807121051099003120080444c1d0070356180108004400400140072800c0b01c0395420006914010100c0e82c81c2401804035085400c07600000e0b00140d88040395201045600040300d0040d0950f4580c1d1186090ba92011406540f25400b5008140416070f08510060050310421700717420107a0f48a0100c1c0c034841030803514000031039000b0a01c0074141e0701c0c0c0820106200c0140c5030840c504000481c1c44019900d11410142c10541e840e0f03055011500c481000392405529614142c0c3c60f980d40c1e075400b0355240c5c4050030440000f41200c6000a40e540a4000e040408403a034032100075500052940b83c1e41d408800359142e2920082aa0020340745401f55580c0e580f050702c0300c040705450b6043c0f1001418200c0103034441c3d42080600d40700c3c3c20b135400b00407058400761015413402103001e4880000481e0350803403084c520700400c40080102d0b6884051a880001107500b5000248 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 914327383 1250 914326133 914326139
    0xf1b0f0703030c170d05090a0212071a0d0e0307060b040c08060d0605060a1e0807330309061803080601030e030f160b011e050402070c0905040c03020405130c 69
    0x10391a000d040c44001c020801101d1650300292080218001c14101a0034a508258200a40d40c003591015190b5103000d1b00284014025402d0407a20400442c2c244c0000340501032410080da042ca540102c5052140c840c081501080c80c0d0311034004c440300c03100000c11241c40e0042e034100403000b8200700c2d00c114070035441d0014801843d802684654410071009109042d0507006450344405000c005080c0d0303611081c804000b06451500b1050349040d10044501200250700b44200682340c4200c58000c0c02035500c115500c031002c2201301c0301100600ca54203000000f602610042078010b400d0144000342100e0078110600c0a208842010294903400703075507407580d651600d100540498254401090302a0802c1010111044882004240112001c5000c00070384182e5181d881c000c075801e8003c1540481c0c440c15111810303600c0410940a440304460451505915980d071a1a11215225581c025910340c4002000c0c0725900c4ca2000c001c40c0c020f0000d001c1c0c0e20b07041c10345040be0741009508846a1341695804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 914328633 1250 914327383 914327413
    0x3040e0405070806151026010909060b03030405061c14040807030f111216020405101d0c09090402030a05010903091703070c1e031b090506100906140f1b 67
    0x4103001c100071b42034900c42c01c00d03510205d0711a07074814007419a08480d41113421070414441441b5008003051040010b1403003107443d145040d02d507032500c1103100b83e20610050000da0395007021207940210300d44240540450341c05454014050703101058a00f000c03114200700911440c140240911403090340c80c85206140c054007a03441d4081040001a0355000340050b0391883c1c800002811195148000c20f8a0070303031145d00003025118200c1d01c20a21014103282007100650703107030340e44034208040341409056191074420f9000e680540d0a03030038800d00e070680201e0190b40342070142c5482c5a07041802400050303e1401d020340315200e20f105181c0d0076280169024508080881910000c0743d2042d2900d4001e8501620840d044c40814880d51210030b6040001000a100c82800c0c0a18505e42c80215540d03860080600e08070b900003401039000300d2507282d50641245d84240c5d080701303485042c281040441c41c0200041c2240c025545107100e8620006a038076440c408145d113400489032040116a4400c1102d40c40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 914329883 1250 914328633 914328661
    0x60724091514010e090c04090503090405061e19080f070302090903130b13080706020709050a06080a020d03141305031227040b06031302040b0301020406170903040e0405070806 77
    0x415458015240014045101e692030f4603504017461404403001c1100000000701203a540060885030b5900014120045007481d00030701c1e6110104941d001d5104402e556104a0000d902d076040780320300413843c54a007039980c029001001030000c2004841d543d04544c80c1056885c820350005920500c0079000107258410001304813170545002417151000e0700d10b00110700200c0e401500282c48032040d5404003003403086040282c200204902c1c5d00a00405141110100465a0150000095a0502c58140040e040000f003801d40399034151405001602607007001c072010307190360000189680c00000c01d0035002d1143c15070700003911400c80646175480300b5a54524458030844031701d0814040d15101c09691030240516440510001400110ba04503c980c00120103074002c40c2c40c1c2402420f842a03000c10350410f0b1048011411056000318a898245240501040e0410001d010b401d0100d0f400680206400d0041c1e60081000011042440c1402d207003180d15031500380a03c942620851000582821024035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 914331133 1250 914329883 914329901
    0x705061503030a0e0324070e0402270a0924170a0b09070b04091b170105060a200f060c03150d060e100209031501140607240915 56
    0x20003140303452415442654020401d07204e26502d4000c104111041801c002a80307100302c1003442c0601c8003460000400ba10001c26618541d01461040c8030310380d1740e0381e05140d280490b0b00400104c811002054400203214001c19000607121314140208061800b1103045107400c11680c403650402c0858464800e901c44c1c02914440020075401a040712002c03400032031a040c3c102100030140c03078405483d842c0042c641c0d482680003030320b03c0b651445000c07803001c040c080c84004080d0b1440c125003101701c2000140000b100600402d482103c0c001951000c00740241014620701005100b08070440404020700c94030390300302003c422131a0107851300013107c5003250b01c210f920074840114505002c04014040c0110707626425000c540440c0c0d661030f00860050104104034074a6104000175a543c86500107042c03c000440160a500301c680300b006102000c440100038225035808d07200c503a145c07602414480c061400e001180383c00310130b00800240503180107401008206000c0d00061084080049224049540f03082c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 914332383 1250 914331133 914331139
    0x50d052506142104030908030304030c0c0b030613020924071e050a03030f14151c03231c02030105090f04030c0f022403040c0b040b03040602090d0b010b07050615 71
    0x8408643c680c40c0d02d219401034064030708003185680320008107155600c00d581c280c011440e061913441c2044007851512010f826070011080c25820000d000c035800591720760180d1843d903008108c404e03850311202107110803c205140c4181d048a0782041c000f489520055064542181c44a081c1c8403000c0b10842d0391044542c05002800f084840e41c40890081200452034098a615001c240c08248002051980201c044103200103007040d00e08200040780c00c0c0580c1d00c10424004012407004240c01600750000f41407842c5495400034100d0000341c54900c01c1c600c40142007050310410100c2028240d01550583c0c03070a9645800c2c0b512104040301880340b0031100100000d120210600004404900e00590584050510b404540c04d06c5580c180b25080003820300d0081038080704010070b200589004d6401003404400301d0745420b040c24818140e602c40140003401c072540000e20085192101c1c620740c1350703a47d00880c1d07010351541c50350144079645c0d01c4140c0c00c2da000d201c1d00e404503c0d1100038041c2103035001401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 914333633 1250 914332383 914332417
    0x8060c07060f02070209090c03010e01051012050a02041d100b090a020a1709010f110a200f060709091d1e150403080402010215040c050d05250614 64
    0x303079031a440680115444050040c1e0248100c4e001611208005802081e9880141504159500616084030180701907204243e042c0303400c0c001e40d2110200e03040107480681c40c0389690b892150401620388540c01c0f20094015140030441d0180341c9204030b900c290318024a040e169080743e00b80305003041d9903402c1602380c1e2003411036021a03c0c10629500428850210741050540e100c0d15000383c12901e002114000b140d82d44540b41d54914800500c103060306540c0c800c4d4142d082c0601c20100510403110807646800201c03e4a01203584060f0801000800550800495000d803401c3e04006055190074442d1a08082c05d001e8480c1003c820035040b801450f1007c4000e040ea05650144c5a1405138031519083d860b00448185000c0700c500720104620030380c06911810000d0410744002880c103c0c900010700441c0341041c05100002c3d419124680886800722029014a04242855814410030950001da0756150307007400c110002182007041d080b255103440700c008803004108080418410a0b11305090031000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 914334883 1250 914333633 914333647
    0xa050715120c02010605040f15124b05150604020c0703050c0108101202044b0212040602070512030a0e01150803070f03030e030409050a0608060c 64
    0x18181445209440519200014462941c40c5a049030444986580141d4640c0380c203020905260081030800c0100b80801c008840080080d92040305960140d155490b411800d08002d100c0c400007203a00560382c0d840011030b000c040349040090886084684c2c07203080c440010301c00502c2c04c0c6120007107982da00100a0904910283c0210071580c1c07000700225032240c2e0a0003209144042040098099407141000b00000e124007000904150402050f640340c0002da443c0c107102e1001510064101654181c40200e83e1188031001200501e100510210b080407480d0f4065030110b583c88440a400d00001c3d0314501d46440024181040c3d02c00d4030000d82c20f0401800c0898001101035006125240c010420788d54140030801020040d50300c01d50b10280c500d520381c9140d5102010a01c501e980140301c810f081545940b4008056490380680e0034090041800b4181050515009070401c0241d001d4070800d4036619a203072800d4400a140640f009030030707589014000b00700a040012194001d41c0c1e080d0081e410210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 914336133 1250 914334883 914334899
    0x20d031b030509120c10060b09031c03092001030e030a0c1509050111040f0509010f031b05060a170907050d0b190c03020705210904020d110703200a0507 67
    0x7034104619413081ca41ca0003124807510025090020700c0388050070300d040c0342c2c2c0303c414207445d45900030a0701810f0822016405550001d0a02c07400010080c004d225240c20314820b900800556901500c0050942a110b000d00003503e01505010406d0700c04000b00c0410503541583d034000c0c403e011000c03035145900800865400a0620b100c1c204032100458084d03d160b65081c255455103000018140f0003141c10320552101e030b00381e400500f0050f1405c1c84190300d004110603518406200181140d50031135000c06001d1490390f2120007400307020304002c0e50741d800004020032501c4410aa980d15543e0200414040100030400f03400b1900010403050000207a900e070411000009803500d040080100d809494803c840c0c01540002e42c1035460058030b40317800c0e0811a003083c5454445400c0501d400c05900395401d003040980d00000400e030317001a01c41c80b5680043c2e004107001c20f045030034150080f9000082660000000c40c40c4034000241252524800c42e84550b07984d000000208290000340042c8251a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 914337383 1250 914336133 914336141
    0x100e0913230c0a080c100c0308060904150e1e0303010e0106050a02030c0a0302070e0106210b0a050a0306091a070203071b0e092b09170102040302060c0a03020d031b03 73
    0x24100810b5800e03800520001812048a5034840d81050300a0786440c0090714001c98440070107112410900965901642c0003440c41e00d008050b1403103208204013040601c082c1640c5d60728203c0e211b0000b003091440710401290f407500080c194000d6008505c0c1e81e9801e017140881502d04980c0c000006510070b9003000c0b015202604031300c0c81101180720038480028112401c10616a21600030703005014002c0c2004407010703078808140c102c00d051040681c001c1400e8121200203001000c00d541d00010403805410000b220000c1c1795000580c0318580010200500000382d025001c0144034030841e400340d03a000d086000600320b00f107601d100913030003e10000010815031000c22a1000d044002d9502061700c60340100301109084d10500360652140300e030714002058404001d650603241440f0307500c81159000c40241020141d004100c0d4a5000c0fa00c0b4111a8409405071000347d98018485511858076030320701c1d669644540d01c154010f126600c101c03042140a07200f00340240da604540c0c0e181b2060070400641c041c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 914338633 1250 914337383 914337443
    0x80a0f020a0819090203032d07200118081b010305060a0909110a060f0e03010e0309060c010213060c031205010b07020d02010e060a05091509061902010902100e0913 72
    0x1070b501e134500c100043e9014001414100b40c2c4a10502d01550711605445204c8007001084050450410400c4c002c20111400222010000300c0410155a80c88004a40d01c40d100c88080c07031002035100021440050100d01c02041ca061255010f806050035801101a21029034601d41c200c1c440e490203000180031504000d145070b0040004d0f01c441700c0807201003040508113604c000d0000e41c3d0b4165880c03000343e0180d516180081c8c118001e00c0f0041c1c0d40d03100942c49200310386065210b6540081c1c4c1c11080c002c01c0d0103540244840b5584c0e04c1230b140d524a400f074519030303030454200e00190100300580c2c0b00b845548291410303071b01040085824a80d0740d0b401c0c004488412003080e4180140003802140c01d07030700c0034000d00e00802e655540986451141003070080444407041100c413105d40500400c4080d8503120b09503035060721071440c0b914140944040590042105410280d0071241e16415030b80f000f604000650710b1000c0980b2082080e0f035994402d45800442c0c200d0080c000701446012401c6c00381c1a446560789 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 914339883 1250 914338633 914338681
    0x60406170c04150c06051b09130905012d0e070b0906220815040209040615031a01030309050f01023c0d08010503060f01060f05090d03080a0f020a08 65
    0xa801d48600c07000c60f00a0780c440c41080040c21010011003002210302034141c0040c100c44810003020f00da40304100d2a0700a4a600d04c2c020340c0070107041c0e18011199082004d495070890004c0100708050610001000e0009000508210ba4000001c140b1502c921440740010718a1000e000c0d03090514040440a5200c01510396010609000d800c0c05203101050f1070300718010100c1007c0030b5070715041899090002c91008812003500e01020803000da122100159030181d84071200044c82d404515180484101e1038101074190a1040e880740d44a111403015541030324002c0c1c0391440020b549070b08001c0d03e140740c2003003c3d0045c3c110855640c01c00b28115152156124949455a0400c0e104980c100c9610581902102d05a0000540b5003840d034001199034050b000680240816141151208500340c006124034402c01c58020034004406100c3e506a0344a00d1000709482c840d4045401d00a00d88081a0758a0310f05905c0c05a0340b640d846410320844896440c03640300d10034603076503004405003c3d81049800000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 914341133 1250 914339883 914339887
    0xc0304060c0c033507030f1b05070821010602062403100c0905030f07031202010644060a0b100c1b0302031501060e04050c030a0c0212031303020c060406170c 69
    0x1061803513908018420961981d0004010294402d000182c0b0501c001e542450b80b82600c0310888940d200c41240c0009412640301a900c80031108140203003040c1408900450030440c002040b00755002c9009070080041859155591032a410440d5032400c126041583c1a403100103800100c05589c0c005460000e0241440740b01c1c16928400b01303080564010144a113034004403400d2003001945040c4d2420300b44584003c10045080010707420030a541c21110381c88168001a113074940121012042c041c012003520700100030903a5210107a91414151104124241090004485402e00059402d041c40d503039902c1d1450722030340d5142c0b0050011160107000c40c1c4140d2000200252310200b00018407000c4e00e202c0c1c2d5983e90b140020007406a01c00a20003407040d400d01040c03108400c5404145c80c0c004030200c9000520501c00903080c1e1518a00c401011441100402002002811443c40c0c1c41c1060081d000d0348c1021201c7c10400c000c1c4d01c510f00501e004a03d002048540c1d0303117880f0b02d00a900c01c4820351014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 914342383 1250 914341133 914341217
    0x15030a0c060c03021005010605071713141011250807060f180303020304030b19050f18031c0c140d0203060f010c1101051608030c0304060c0c03 63
    0x218624500d41062022482c84107014003007581c100078000d000d65885100304500c1d410140d00401d00e2191302c03c0580102e4a28900143c0c41004600f181d103c1502030640c1c03240307aa6070f010680b90b5000c050030300501c01c907290814004200d008124a0354600700400240c40300000c101821544440034400b0301060721481400400d41400410a820150226844810882c2c521100060251000794001c00000b02e0013001080000d1300002035906899000f50850803643e02d01244484140da00c0c03038181f14a50414045c07180e00550f10059500501218152505024503007842c1c2d5581d2103040030035602a030303ca0031b460300200e40c541c0c021109541c85241130b0403e2100d450640d4020b4100040301e200d51a070000030302030741c0d14080b0024000c044083c01e020680c10315584965542c0c103030300141176043c03080c0011500b01c00b440219070b40075010345c44002c0d5901da09100c00d484140d50000c036012100941303402c002194140c040c07461640d10766407680e961000e200781020045c404280c00f041030f10000391103034411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 914343633 1250 914342383 914342393
    0x11e03020a0801050f10030308072a1103060703060e0429090708010b120a140c0a0306090b011e03111503040609050607081905040206040e0103050a2915030a 69
    0x801c0245041d80001c40d041c2801d6842e1784e5001c101030600016401004001c00000750004201c41d8000d40b5810301c0494440742c08154044d42508202c10700c00d960034450314004120030340c004014800415800c440e056074520000f601100c2c503600401502e141401e0018001031081544a05074500b08046040d00e01c803e11901d60350040155000349440e00080001d00030f02c0400d2140d500d039007000f115810064101c00d41c0346902e540704503001922402c0c0c1500e18485a0004103e9a80c900c0000b40c2010340541e0ba9080031801400b008008940c54089440009009200a5240d0040c8072220406111091555980004030020725040d10b4003c80080c242c80e03207210307102c00998031481c0500400700e0103140c1840c1c101d040080040c4400306100440043c0003903d00b0844e120380584401c200e00240e01d844170700000320507002d25844601c801101c04004400c02402042e8484501d1103100c80320280000345100b807940c0b00c180700c0c0300c007180d008660020f249084050404a01c030200034040d03841c0c0203c6a195 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 914344883 1250 914343633 914343649
    0x90b091212030108011a0f010e0102160602010e1b030c0603091504080a1e0518010908030304210e09071d120606031911090702030f040e04030f0c0308011e0302 70
    0x5040306540700400100103465080c0666480000d4152a0705250040580000c0864055010103410069803908040303050b4020443c514a069400c0da0316480b055031200024043e2801140300c0d02c43e8001e0700051404207540603207400703611030b000b8090640c02d88100180004d58100401a003d58410188882800d810058010b0b0040740035003156541d070b40704548060328100c012040340d82070304c0c10107031810541680407050306c142040186100ca10b8903400b0b00101c0340c806554214411307a0100000340820080c8403401c00700008912510101c58a2201034103a40c01400c07016038130b800c10b28050000380001d01c0f503490502c0300e91551068150944036000440c068079001544030a19502190a0041d079203010822110b8046559540980030f0301160349140d00c040641c01c2d9a4040d2010001050509000748246d0b144401c481c44282c1e141d954503051141c4d00702d0140c0c0c054020400d03050120b6007440c0b06409003107500381c0503120300c50305901e0f161104e0911021a2101301c102d0500c101e001c40141d0b54942 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 914346133 1250 914344883 914344903
    0x10030e070f1d07020a02150f0705030f1806120106080c0d1406010315080a08180315041e0b1807210b060307032d0c0e090715090b0912 59
    0xb05420058100000607038400c1000c1e09000c103560250040500594442c03410800a0740030512064842014229148641c0101c0000400130300002c610514240c89610182c0034100501191850031820041880018801c4541c000880004075005110003400b52400580001b00403c60610b0140c0f4240c0850440d0400003050403e1086901404682e41e490700542068030034945003014102c2c82c08464560f2050300b540c000b01800b82c0410840c034007940038001c00c0c035200710150035681d204d60010741240d00f07404115004c070b80f8044c50032500054076800380c900051181e4000c456104a8807105000745440c0c082c04064500341c07050400200c3c040e0480c2a407884507103e50350b41c0341300098040c504103014540081c83c041c040d51080808101089200d954408051034140c20034100e0309000008805100030520007611002001d0b000082810048406912078a951800d03181940c1d11001d880c502c00b0200509000055038608080c042d0958610042010940080001a4a50010a8030b41c244001c600d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 914347383 1250 914346133 914346149
    0x901061e050a14160c06020102030603070317040f1203032003063106080105060d020f060706060320011728060f090e0d050703080705030a0e070b0a02070602070510030e070f 76
    0x84508030401c00319413174200103001d860000f035040d46800d00c0407941d0303001148006407210003002c0302c0100c1c003100c4c42c0454002e48040f02008140540701c8100500f2000c0c050402c800003460301c0ea83d0080e080d007064022510729200c00c2014510780300d180403c000c648400e1000b6800c0444440b0184000611070841183c0301900381c0c02103a61403400d00b50b04e003112401480580034404220030743c0010394803100307507524540342120f069845445a0a03d01c0051840c0e42004101c0c411540300e0710010074a840582c41c10010907601e000c1000c130400b0700b20340340c0b90702550030740005100700c414840c8040c00702c0750340060039001c00b5000070f00c6581e034001d801010f000c0fa03100581480d510780e04203070b0300380b01805105180302d04c40c10400e14101c0c03e41e500820a410040008042000100110f1455a959000781c007801d8480012600019140d441c540d0140e84600f036818054401e1401c0061311500100e400e00c11240c00910b40c116502c41c4d1001900070f450103d00c0141c0e540210680810002050801c04010380070312 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 914348633 1250 914347383 914347417
    0x7020321091f0b03210a0f050d2906090d060c0c02041b02070608010b1c1407020c0901050a0501020705040c03060305060f010303020114010b160314070803060901061e050a14 76
    0x1c2e800341344c103000340e045507075002c024103038409840c0c0c040070800c40e82ea040d1079103440031140304003000856880c042d4803201c0c2d905034240891021a000c0b1040d40300000c1203101030460a403444202045140d106103030391190000340300505070f80842c0040e80103c11452007803c0150810403554005401c444128402080000c9a18041d40f2550740c1044400c000d4001410140225410302c40d05c68201e00842c510181c4400300c96080c5002d040664010a1042d0f5001100c15881e04201e03e02940380c0704c0981c100c5009040c0d000c000074081c80d26148013800c4545c1a00504041420041840042d21380c41c80000181038840740c00000040c41042482e00ca1407a0b000040510350540c43c000b030135580d440800d80180d000d42401401940c150000300c03040f94039000022820020343d8a015500201c0183d613040c0c498401181d440c051000c03510043d8400c040440b84401141c1e250481941d20030180a403035102030796502c20303c0c0c081c98002c6004005240706400d01124002c213070307a4800095030003100c00003811626 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 914349883 1250 914348633 914348651
    0x40f020d0b09040302030d05040203030d0c030c0e0a140d0f050304080a170403020f1201060b0d021c0c0509010503130f060b0102060a050f1f09150e07020321091f 71
    0xa40700d0702003550422144000242000d40b80295240030b402c0804164a540380b004c20119038081040302c0c201c02c58401c0a00c6017281c2d240700940281700320075042020030104a07441440345844458a001d48807000302100200901d0400d02040308003840048a00d103001041c40030100e86d04002030801000814014040940b1030301d00f0112410000800150800d0140700c14801681c52110f81c100f10481695144405007685003828050a02d40e0300c801c0f043d100000b1701c43d41c03002c0a0b400900800b00102c840310100c6041d004a4800c440d0550f03103440002d0300a04c0320321003641c0b05074011508004650507404942c11076454402c0710000500d411640c076542c5440d031000a58042c07040d283e02040c5244104600c1ca4202010000444024540802c01800d5019202114440d070b800c003024100081c001c010310101d03501c1d0a140000c650182d000100c0c0311400140b8640e20001c00c940c0045400109410b55680c0641885031034000500304c03114900800405130000030208900d182e07018804040403800c0d0613 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 914351133 1250 914349883 914349907
    0x1b060105011b12030209010512040605180303041e0f0501110406030f050907050f030a0b0903220807050d0602040302091335130510080103050d2a060b040f02 69
    0x145080d00c50021a400648071000b20700600f11602c42c9603c14100560359104542c01220383d8030440000035002c02e4040180401c0c02941d50205102d0366442e8400604090311100c265901e000031207000384000d00300045030900350800003650b64054800d4110451003400741d80c4050a4519080f401e50f250080481c04000f500e505010b00b820102c002c407801c0000b81000207513151929a180a16401440c051600100c1910200000c40c002500031409401d207040c5808450340f65482800c90302595102c5e02c0c242c08100c160000c6840c12500350340c004145040c031300310501103140a21031059512507820310000016840d071074141c0b481015862184880c0765030900e8941898000d00c0601441c200c24040b10030410b00c0c00c04031440c2050424050726858046440c405250300d0407135007000c0e4004001c00140c40751907800840d040d060388c3c800c038195012803000e02c10403a1880c10032822000d60b0005140c990703100417051861101050b00544000c2004445540894155100040b04c103c2d040d5000440a842c15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 914352383 1250 914351133 914351147
    0x15020303070207120818190b0304020f030c0d1101031d01050405010f060501050702010c080c0319110a030e100201061a120901050112080a170a051609050907141b06010501 75
    0x141300441d100407003041d42c075a140c2c24011640340507501907144400b541ca42c0e0780c006803c2001190b451a441c0c2c0317640c6039240b03d6003030303007094408070f004a0000c05440b0301454082007914071804050580110908140c68070040c504e100050581416620003650154103140d00c0a695000c84260011595052a10701542180d4610302d698414918002c002d2005a80c000200c0b11215024030b8040c03c4600749050a014900c40c210590b0b401d44000101030708038030700c1c09070080c019812a84620204084840f1010b841e0048500c004001032288035215405180c142c100c8060528144000110701d5101c4110064038190101700c05201c00c0080382c100c680201c1480c4030b030b038030019000c000c1c4110751501c080c19030303540c10550380200009030100d640c0046c0761107034048442289502070040c482d820407154140003060240c0d1450001061400303603041e02d030b0140b405842107030000740901c0c107256201c6404940305800d19081880d160f2017001201e100d100b81a80a00c80c02c0f450344050501c9516101c0050449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 914353633 1250 914352383 914352389
    0x12420030a0906120c050406050a110a260f042c180717060403140712080411040218060d150305030c0106060212090f0a03020d050a05010c020f060114060415020303070207 75
    0x580c04d01c00c0445c0d100c0c5d4404191000c403001810407030303295030000320241c4803144140800d1031184644030441c001d1080b8006032800c8008100d0b0810034017800c0141c031441500c80c242c0b5030340109004002c100600340401201804242d0a203610300300c0501d100c004110903240c140d83c010b8070014101c03400c4095807030070f01c12400144280d4a2140c15039840443c060341701c0c8401400907061001c480c1f008509600c6030700c104c812041c0e00c44241040d45140d07002c0640f05070750a03101940c0c406400c0d041c1380c005040078821140e8160141c561340b03407109400420084580d004828114420b034985804101030032050740d40300040c500c00c1002e035480d984000041821968103901074002c641c40a041c40240b40340c20f8080301c810b9103007a5003810600d1007440c00304132856540ea00c02500040300c0d100070750910901103080600980710b40000c0c0040d03130369100202d0750740400d21182c04a83c0c02010042042c0e078131200c200300340d07141e01a00507401e00d45e071366042d4104000850141d00150b04000100b20156070b05105803400313 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 914354883 1250 914353633 914353667
    0x1017090c03011b090e0c070c0b0c070e0712090203120c06040b090c090106111f020a0f020d120509010e06090d0e030a150f0b0a06090608012420030a0906 67
    0x441c0b00340c08001c228084500c0765505c0c01203188003290040301c3d0842164045908002c104440035500c0c0f0710007000e0f5011000d410038034020010f0100300c140050f04114001c800325602d0240346504030951500424682c90700300d03491f22070908006110351086028000ba80001e80180c4910302d4241055103a4031002404450160051410001155101070303540341910050301e4110350010000a48030301e0515400c0320390b400c00d03070215200400b0922940081c58645015998000310f030090ba01300f030381d030340403020070700f1000c245002c4018211f071506034003455000e510300b400412580750b405901810b02d4425a590949600071403140800c880e0094040c5044400a8004080d030414035100e0180c60342c6e0700804101d6460300ca4100c003111b205150000ca01d00c200061225031700680d15680684410031500c81c2c40301140c6500300004605081512042040710100380b690080d4004513002c6540c00f5140143c51513806006d8555501c24908001502100b01c00392103400c00a4240900a07180ca8101106401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 914356133 1250 914354883 914354921
    0x6050315011808120a14040b0f07050106030605151f090513140705091c031403090a050f160b031b03060a0f03080306041802010c2301020c01020d0b0312091017090c0301 74
    0x1231441c2a0111110101045d03107103034039020145841d50240c14541c1c00617010311700340310901c803803000707d1605070700c42031411102007104800e945020040c4c1040540350a001c981c0740c1c4810040c6003041c0d01d00e521111001c6e400016006005038100f00d458005540c560000303100810f14000034100555020346a040b100b04d240c41600b641d90303000703126001ca200c41e01c8940b180403010504101080010300849644203043d10720100c0c0c24030740241c3d1a43c15110f0241d40c19200400020b109801c031046902408509203013010303460f038451441c1041c0d4000343c8955000101300f000024469090f04c8810043c44c4128251540d0b0305000040009850b01050740c4080c21301c01d5015100141e82212359140590381c400745038054502e000409030f09980000c2c103c00215400000e01c0c450700c2c8410b5004254041c41c1910402c1181c500301c05255903800c000001c400600002c2040001c1d901e400510b80c5810b030320b035103012041c800e10580c0007440e100c015140f200081e4000319844084d803500307015100c0700002070301e0780d03103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 914357383 1250 914356133 914356139
    0x9150c03090f071511060c18040615080702061602300304030903020328240e06060a0b0304030c06051506042909100e040b1206090706050315011808120a1404 69
    0x1000c61701ca564040080440b244199008c03e0721160020802003000103010708803034841d400040e00c25041110f80c034006010701d00006069480340d5202494a003030a034001e00032041c0c18009011040f2039036003030102510a00c03030700484102c000e50043d40304502c08c0c0e0714040740901d98810700d807401f4942444000e40104101c45410b80600448030280c1d416002090070f803848041c076003840c0c1d01d10540750745003100341e04150750745000d10000203190303000381c03401d03510150450707628109958940010b540c000e00190700c10200c640841d4040c0c21aa8100840d4619098064000f000003011503100d81e1048042d0303104146080d140c40070090f6001242d100044c0c02c0d078070b4111040001003114110020020a00940104500142d125540701a21207440549241c00740c041a50f403150341c030349080713505207035501c140c1c1d0700030400c03074451b07000c0c0c3c5c0c060080071a51010100c9410300546d81d02d016035040c804074820b600d4000030b0007001046659501e100b100c80c0140e5a1010900041040c460100400072660f0204420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 914358633 1250 914357383 914357401
    0x10e070e10030c1d09070b07020d0f06150f051002030909040c0e01030f050f010605010e040c051c09020a060f09090b0310060f06110304030c030b040f06050a050105040509150c03090f07151106 84
    0x460541d40e040300da02c0c0300e0074ae481c5000d0f41d41421180c8081c1240b80f0300b558415410130b6000166059910711030003100225510010000418840103d600040c4c01c03c0c4418000e0b400c01280c1a500a4807601d00340c1c1017140c1b03507120260040402d0744188c407910105110403041c01400d008140002030305070002c2c4007060801c000070307002e21400000e50380140d940e480c05c80400d5100700b0540b802e4a4185e004101d12401c0850600d029021810b0300342e20641214100040c3c1c1c1e0300807180091109220780382c07032251a2402100d0b40c000d0900303500c0c1c0c1c2c1e01350090003d08682c0c204180301d83d4015240041d0020141070801d54000c0003901c1d0041c560300c099004020a001040700011403404480e444044005540c0d6545044c2c6585440c100005140d070b804c04040c001c030410507400c01030580c1e0060301d0401c03190b5248031704242d03a070b03020510a0040e8004040460901c0c001c01004591010301942224a082c582000399440c00549900c6050004041070308049010303404211808039400910040071a41001010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914359883 1250 914358633 914358637
    0x25030b100308212224090c050f09041511090d0c1a040513022b090506100518060f18010509060a08030a0c0c171e010e070e10030c1d09070b 61
    0x14003008040d0013030039000100c4445010690030414406d011b12481468200d01051040c05036a00c5040e040100c0e580360704200f5010340c450f80c2c001c4210080450640030b4040100303149030644110700e008102c5502582c844001a20300c45214950811846203410544502c08490f10103040c240e25080000300256607c64008200003a042040103139a0a40d644c17039544510704100e40c916481e0b02007070b1102c6d803a0036a644000308050086007070311115501c052011488284501070a0303440a0503584112102c20030a50311944441c01811003032481d0703084000512025260750000a90280900062185d0308195000e00d420102c1680d00e000c1890508180548a0240401c40300c104413030b500c01074040c0820840038200400c42000702d5101507144042c2903446a84034694480390501c0c040d28400e10314014800e10354080e1000b4040d2640d141402501114120081c00700005a03a0703202d40800030400c02c0d10020000e0044c0251094030006049074082a00f0000b800444150407480c4200301c92980c03001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914361133 1250 914359883 914359951
    0x207200a0611031b0c150406140301060f050d090b0108100f181403041e170703080d0209120102030108010c020f0a02100804051c0201020a0225030b10030821 69
    0x3408030036544c1030042c054a85481418a2a400310b0405407102c0c6200c0d0707605c01481500e55070365440e002c1d0a0000d00300d14840c4002e2056000007101074070007240303540c801c4001e007610100d07008011900354000d80b00c21807010421b81003205690044150a19649000d210300005099000c4c0103001ca08440d507407800e8a2504e0b150090302d103145600c4891204c01c42030040710040c2105404001d40d20500d104d5110190f1a1809103101c560883e035582c40c0499000038414044943c450314840c0f401c0e900c18000c601035000301e0402a00003102c0d20492115110a00256010b010514000a520124810000d01d030a0700c102c1072181603002041800056142c0d003910500340d4500b81450007071600c0e146041e0745403000b6181b140100c5020f0241010140c2e5042d00280b10b011425800c903480c12121584900d100c20b0000c0c291000c41c2440102000051880944d559000001121003d6030668a0b00c81d8012079115980d909801c40c0c51156480c00e1070307520140700d42c012a480e01440c030055408411071901520b520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914362383 1250 914361133 914361157
    0x304180b0603220b040b04060606020604020d080d020409090f03090e0c0a1d040c1806032717041e090203040302030901030906060510080a0c030e03030a0b040207200a061103 76
    0x3640b6003032520758203540c1c40c3d466503202141c0e0f4904e10301820403010403141660308480300d500700100090313034078800030301c0d14050394006204c401e02810654035044a03500c880d02c41410f03242c0030302c4000791a030041c0c0f0402d0750b218005c0d4030a1403c0081807500504800943d000400c1804e01181442a10034440c03080c0c400148103414544041c0b032402c200702d80c03c0011014a144d01c5400c0c45140c0c5c1403d50701c8070000c4006191070128600603604c9540c01c3e82a60740e03030305607000410700007050121454003401d04a029240580754540340900c1c1440100f040da4003d420010b0b4415020320702d0307140241565080c20040941038021811030070700341c2c0d00948030f201c0c087c1880c0c1090b844e001c10074107010f0300b40d0040b0300a0500600c20b00c20101c4804024004150031070325100340c103141c0035808948c0c074028068031525410410256186550302161000103052041380c00d030300140e080c80034400240e1031684030a0214a0013003210861244501004000c1c0001d4100c0410840b2034402c1c11100c0e9000000c0d41d8100d9612 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914363633 1250 914362383 914362411
    0x60506030115031101091a1309020a0e090c0904050708010812190302130e0703090212030901020c011107090f0615030b0112020d0e030f13060305090304170c030f0304180b0603 77
    0xc401214544010b4014880d29500c90207d800f080340640700402600b03181d110070070180740e510880c0d8070480c011441d503100821900c5d080200e540c6481c001c030641c480b918000a900b040751701d6010a0440c3c10456005002c904e6101c018400c03501c0030060018001c2864000300e14046a002c1004180040402c494061503000700b601c14408661814031400780c608003498003035a02e00010001d0180ca00b0400c103174041e050b05a0000e2421401004a68404d14185c00503d1a948a0001101c2d00c2e4ac0e030007280d00d0303036008000c03010550761254010641c00c2403505801003500c9051284a941030342b02c8410080500d481e00781c140c1440e0342c1141c000cac601034900d2280180c030b0f00f02e007000c1d520150007042502419404001840b00d00312404030041c2145942c0462044c03005501c0e403074240c085510654000980e58820b1104025080c84105218038883e00001940c04004090012a10b0302000300b091221540000c2802d20002480600f03104030070304c0070710085c4198886003001c6840d61202400c800349010071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914364883 1250 914363633 914363663
    0x702060c0f12060303070f050c0415080d0806060c01050108150702210a0c020306010e0a0b090705030103020d030c1a09010c03060b040b07050c100801150519030905120a090306050603011503 83
    0x814411b03102225001442400700d040c0394a042c80e00d0322202d48509114a10b410301041503100207a4041080c1d0300030000400302524629000c0e100741c0713001011141d002e04100311050300c01e03c00b07016103030080200800402e4640b04410f450400100010960003c65002d422080b000c07071070b116459040358107403078282d558600b4226400c0b2a04020713000b019402d440348500000e030310003881c0111032040d0b03d1a41e080000c400c2d4001006070031001680c0302c0700060b4040c0014800351421500016101b403003820450803660460360b40c4c0c40300c072820542007001000c040d010810ba5a9082c0140403d034542441c00708047c60800003500120300a90003150400c50001c0b0b4100200001001000310040e001416074400c00c1c0e00c054024100e800c00d009002481210100b40c140050003481a1181d010f04031905001c1058124170890081030281c0d02079509108013520f21881041d0a002803c603000280d41da00b4500742541042d40a440d40605840d0003607242c1400c510a03118000030110540380d104e1244005080d1b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914366133 1250 914364883 914364889
    0x209040b0c0906070b190902031b0d0605070e03010b0a121112061614031608040c05091e011d0403080c0904060b0a030c0e1f09090c05030702060c0f1206 67
    0x2900203000d8100400040b420b00307210000640501c503401b0040e401001683d0b55071890306907440010000e4150340203204400f0001c4400c158400c45050240865001c103000d500d415054540a13030740c12002c9050101d0742e19442c1001e00458128500a49581003030034944910030030700c21325900c1c02a08a640312088424036030b80f58028145041141021105141082810325480d2520f030300001000c607021903203842031130407100156072146203050498400040c0880d0b00707603a2054010821a4840b00c01d01e00170410340c3e1044941380c0554190600e0700200143d008402d501c0540c1a044148601101da010090007030102401d160700c6581031034403c00584501c540340e5403034080c0d401c0c2564001e0401794040f952800310400780c8448140e5a9061081d041102c41c00c1d60010034401105420040030f250386076134807900390440509055a0301d84031445559802007101201d96940684000440002c14450007a41c1040303500d030004c02154a0900e401c1e0301c0356103021141f2501c46008144140700c000a086a5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914367383 1250 914366133 914366137
    0x50c100c0501020d060602150132040e03040f050604030809040c121e110c0d050906070c0909210f0807031d0708190201050409050a021b150f040209040b0c 68
    0x81d400720083d0340b00c2082c0c0b101203002d0045401213400503c209000c1d080d808014408050480390f1258072400e02541083e94640b202040f12804010414019440139107600c4d80c4c451071540341c40b110003031070f16207060060740d080035241640114880d030418081030010940180841d291407038100c0700001d2903070040900742c0745d0140104480c07090501c0d007a51442c81c9400f520103040c0414400f0f008019000c45c0d07101e40d1040340214111402e15601c082248654180240e004100c0d080006102c18180041581d8421290426820001e0825102e01e400010008606504070803800001c103401c102141803000280086150741d102d1081080c9500403441d0280281d1203c0c64001c00d00c89203c19199000b2540c40d500c100c184102003451042071008690800c181d21002e040b40d50580da00c43c9084d10f031081080150102600c3c69200c59820000008502c1d01c51031400f03800443d280140940b1140e010003110300b00c50003060300c0c1403000050204401640d400038540e074802c0e88001d0b40c8100340c0703030036204000c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914368633 1250 914367383 914367407
    0x30906091924111f020408030a0c110a0305060c0d110d020702030c1c031d09040c060206011406030f040c031e0507080f03190e03010c051213050c10 65
    0x44189000e000c01c03082d0000d1146020081d101605120300074000504403400e02c0c2d40c440d50741a6400c2410f9011002509101c03101d281c104454015040603101d161150543d84440040070100300024440000c1281c4280c0c0b42c01289011907003c1c1e805840e42e12000e80b5503038001e14501440d400040c800080c0d1019038040c150541c2e40140c45611445060840b000070f41c003048007603101e4815030b070f0340f000c1c07a00e0500c0c108910130360b60707103002d2a9100da103950603079203602107a030b019040074044a80128142c54500b141c3d441117004208a0810701d1400c3c1001c1e04005060700a004090801d04001c415070f19a0310440c2e801803100504d90b412030351030b4204941d10310b81540004102100d0104802a9050341b4102000d0107401202524074207079480c030805580b40b2103007098180ca9002800701054442ca041140ca181c40c480d4203105064441742c0d00000d003190301d0b8406620120303001150150701001541d410681c001c2c0403814415449005446040c2da620f484000c0510811405403444040c4e0f02c5000b80d4811 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914369883 1250 914368633 914368669
    0x20613050c190e0a0603021309050d0e0d0212070f060206010b0403021c05060c130605042409150216091e0f110408030d3204030923040f0b0303090609 66
    0x65007419084e280103454141700c240d2061085940303920400845110f96245e840d0700c030008081c0b0907000b40e401d0340c960107440c00c07940d8000003070703c0f03e00007580301c14050300d000340300b448058030286081035130740058040550002c5d021980418010322080d4105011103060301e404440d080380c5164400c03c2c100c0300302c1e1822030040c414040c2c001841040703c10740c00904042d00741701c1d250000b040e88594044500d4000c3e40b048401d4242606c0c100d00c5100f0703544030003d0901c1001c1c41d0080b0003580f42c0560300402c0d043c40925100580c801c4290f1010b0f205402e4502000c0c000c84002070105020030405501160706010016500654800d1100384034000d903440020030704201c1e44600d80b44c6a9400d101c17520381d00200070400008dc140208a1410191081c103242c54810741210407040c07083d40b01040000e150010000c40500907401c00201d54130813411541210301c003640e10800508a4070780c0500041e2250b1841c1045980d08104a42c40030307035004401e0740c0c02a142500c1e00c5448426800004040501060321000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914371133 1250 914369883 914369909
    0x525140313090b060c06270601030b0702070515070210050417030702100c03050712090e0a05070e060a140f04030f150c1b060b011404090c020613050c19 67
    0x6081c8000c0452881110900107041000e0a00c1c0f40c140714491042c00500c40564000e500003407107400d500e40340c40c1d90250545100c140c2001d00d030000b05241c100203070010f80d4a50254010002190740c1000041d014000564009044c5020804e150b0040d01607a88001d12400c1c4e8640440e02851048040c0c400800004102c10541d60300038404589a50044400781d000c0d400030802c50705202c0c05002c110f006140d00d50f55a6152a079161034014071490681411410414004800503928441101e1940110420100010542848103015050201d48107949000d08020300502200c00d40164108030300f505484112991031754075210490781e07841142c100609d43c445101c3e9031024010300c5d03030031445840312241d02040320041000c02500c41c502c0e0303110002060603a1031300034030005015800c00460309006041424020100c01040811034000e5004001100d0761a40001e51b216030400550350890320102405c1000f000ca9110300780c50b4000d250b1158020340b0720001944800c0305c0c0608010003000c000552007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914372383 1250 914371133 914371147
    0xe220209011815050d02010507080702090a05010810050c0318011b02010c2703060e01022b1406060412140d0206100501031815021e0903010c05251403 66
    0x501c0010010b00380c80a0740d10382100e100224014150740c00550344000c060039a00c0d0082c3e4011a46640701000031100007506200b0000141c80d480186400341800060100d0b941d8181400c00f450081000030460200b4240360078003d074803803070380212904010240190010b030425121345a000d05220200c3e02c198001c1e15101c03c0d503140d81903210302c0f0614090340d00d440340310911510191604030480c0c020308031442d10710b404200040d2907511a41c40400304d00005410070012050790b010544030030042c0034405910000c0c2030343c0000a4860021039041d002c1030141c1c94100900890082d02481c0104c0b958109007031a22000d211010004080d2441041c0490b101111004e0000b500e0310000e542c9915000d42c000c034080703103a45c000e008000192105032010601c6800b542c64402540c80144200010b1907403c00061441500d12241822803450803680c1c140e40d2040b240034542120540b0007014200075040c4000c084201c135141481c03070030800180100c01034040d141440018003404080819052100050350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914373633 1250 914372383 914372399
    0xb0109051b07050d080115080c0d0e0a110a1a0d09020a0b0c010f18051f0f02040b13060c1a15040e0a02210309011d06072004060e22020901 61
    0x100365800c0c0c00d0344d60040b140d0781c9100303042c031f01001c994620010800340d0f000900350b50b031020080c003d00c08918101184000e118080c89050a800c2d42081e107290704050b807011128201922040010102c4010f4000e4540390081095011300030070b0740c0032811039218101c3c04159a10250607030094040c044d200d5542d1540b210304103000740304082c141159a82083da5015803a1303000104c0c80d160765000300290403d403940400e82215110402140c1d25207956850141c01d20304018400b4002800001e0440c568030f2400d540c41c0200c1c207481c1e0703000c1d03400c000405e071600000488944c400000780034103e41c400314540b10071902e041da26030004091074106107441d06038440c0381000100380000b0b6000303683e0814803403074840080c1c1030703900f00c00700c40c400640c02009182c8141d40300380c4840c1d011341c504400303225214481e24001640350b80820300076158821040b8600c601c0c003810380801140c040084600708902850480212864007004050711a0b0300080c8044400d90030602d085800c000d039005000541544c2c44100c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914374883 1250 914373633 914373643
    0x50d060b062d0708090d020109080609030408070b09010f080a02120f0106081509060d0201121d100204060e040926030702160e010b09030a06020408010605100c0b0109051b0705 77
    0xc5050300002d080040d240702a00402111075080c2c1084000c0c2c1380440c184284000005030385000c03810006000d0700000c6250702400382c4c82c002e000c3d040c0616071381c43c50044507130311389003070380d04a90404081000308840301d03070b080542c007602e16241d8180f5000300e540340d0450b0300003400f80207844100340001d4020802039245801a00d07040c1c904503201c541c12921001209513502c0e40c80e50601d600806102d010620700d00d8075070340c00c2045510500d89881ca001205d0f0404040e26280451182c001c0302900054210030070510440403c11840305046040604d8204000e024500e100c090500966803003030540d0038003141111800e01510340311401c005040f0020124202c1390300072103020005005a80244655044510310242210b00b030b4500ca505907424121309103c00da124200581d41486805041c0002074010300142008050700b03000014050b10340070502c00d140c41e82c204400100003011140100080010440078151441c00e000002c0326500c50340440480c24805a038958841c0e00400c400f0108100011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914376133 1250 914374883 914374927
    0x42102030403062702120a050f151e0106030c050f2221151e0c020607171602010209062b18031d0904050a0201031113050d060b06 57
    0xc0c10001200d05000c4100840400c060390000c80e02c0c4d60744210003500e08070102c0900e50100348180d41c04039403140c2d00c0300d191424070700d00fa41c002c2d0882502d40c0701c44810800d00c554810320a400d40003000c00d84000b0002c1d0490305003e140300341a580d900080c83c55200d2010340314130b2405030211035610740c00c244006c034220490115411510390800c001040604240c440600f40800f986480c1d0000031103503449a8107546c030002c80c40407035503860b58440c2440380090f0340c480185420110014103c1e0103044000d0038040c00402000601000b9074a041c060954407829580c03040f4445103101e0400750712801240039110302d010301a4449070106d018400040300001f104d40b440d08040f80b5921000f94003242074250740030650082e482283c03600582003c02d01070322959403079450070444030451000050014451020640d01914254071600201d0300715605403040c000460010a14141017110244500000141a001d4207019005ca80469410000702e42c11410401c00c0c0108503a403920315a85950b901454069 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914377383 1250 914376133 914376143
    0x209010611070920032e150c11120a06050c0c210f130801020711120708120a020a0b1302150909010308210c1306020f060f042102030403 60
    0x4100064000040c802d402141315140c3c22035a262021104454050304014030a006000400100844088a021610100f09402205440b4190410709030843c0941d44615401c18000d00d9000342c0c02283d000500700001907401c50b00300c0c0b1380c0091142d0080c02e09038080741c0200800d0a000c18000c661840b90050b00d480807200c0200c800d0f031140429080103650360b6000d0341c040c444e02000070704d001c3e501000050600500d04280101110b503154902c0b802ca0341300c00b00c292000380c008500382480e40f400c04090341c540e185100007031200c0c0e82481103894544000079485042e0700c000150880e4000e00902400300b05031f4106160030050301c1c150024600c0d18000801c00c900c60504040001604810b003c142c695549010700004541da0856542080d00e500c400c586000c418101c03043c68000c0f01e07031007000a2052964000b4143c40352003001d0740f038010400c2d40e044401550030180d08408442000034400d5400b180340310f012039003506c1e64105130b028180c2d050100740b2208908000d0407151600000100304681c0f1074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914378633 1250 914377383 914377393
    0x10c080a0c0b07110f0c060a20070f0e0c130b0a031e09020906030312071d030a2015030f06120a03110706080f0402010f0e03011e11070210080406090209010611 70
    0x14601072a200c011504c0c04035800b40d030520010702d20500c00d00c0a09d54411610380103100c5180c08140c6685003018a6100c5040c0846051003486103220310949141c1100307032585164106001280c1e1110130807807501070000802030100e01000418401d4100703140101d28884481440c48003e1a500003030584000300340c0c0079280c01004a02e16050000484080114200080303406460b603110886000480c0d041a20041600b81c00d00321150341e0078814a0591780c0704050000d4520710300500404007031010040326110310150b220381c40508202e9800c0765801243c1d0b0600c1241c681d207000000d480a01e000200030b8035445400441c0c81090782010031281003444d00c000722802c0547c0c41e8002c4401180480e04401c00c3c61000d80814010b50041807014066159030812124582400d40800c2c216a903c1031110709500180b100102c40101d01c3c03080d0003800c030000c0f000790300d01102c41d004070f8528980a101802004032410000e028045660300c0030b0b1040b07900500c60003055075910300050258002110848044c003807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914379883 1250 914378633 914378653
    0x603011407051204170a080901110408190224120f060d150608011e11071e080f0f09030606030f0d120b06030705120c09010c080a0c0b0711 61
    0x104810381c420329141da03950385400e80740c120303940002001400442e40d1640c2900040c1401c081c0b440604140c64565540418914028000c00e081d100355514181024a0412007400010b4000c511301003120a485405113686480e07102103110680c01c01c91000050b0800850400781e0440d1500908907108420941403190319013001301c6000240035122107510480760800500041c0303410040070803203222200001441a56080e00c6806d4400d0742144e40e15820380c0c0b8254010701640c9210302150385421301d03002410003041d544d501c00341d5445007000c0c2c003004807501200000c014200d41141e0300311044010003074559040b0900c00c181c54200c4803089101c0e014050006440382000941003515a100d000140959a08120305940800d0070000c0c006400e81c0320b200c010710f50f85444004500a000710b5603101d586105008215005020252100b2481d981c10800382c441c50380e00114491409d40c000c0c000950760844107030181c8420b04090f40041805030720300b0803c5440307900590f003200d400a80e0b406079401410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914381133 1250 914379883 914379911
    0x13060906031208010e07030f0b0406030b0105011803080a0e150403080301030c32030109020d0b01150915030b01091503050a05090f03120a090203030f031005010503061f0e0d0b060301 80
    0x1090040010721752114000076200c5120b500306d600e92100080002a401049001003000e4503040d4206603440e0560300c004100550340044641c80300c100036405002102c1c21956503070b14a100c0c5880580410004902d4485250b07186d600345411640804111a5110355034038101020b43c20921050343c1031a13049500141125078103000402500c3c1d40d00030030401114907403511884200f101d100d41d8042d0b40c4c0354920001a1104021510a2809221004001e61509014440c00700c2081d0211082101d0000304100802804220400b2602c58ac10046040301c101c0740121084002c40e400140641d00ca0310764600d000b07400d90300c030500400d05205d052001e40e883c100758a694580d88040420260300800600f4a10b50030740050f56000034208901250070a15600080c2c60350300942c40d0326003d00d100100f40015903407020002d1000706000e09210741507141010000d070000c1010703000041240d54404039181c0240c400c81362640d1a0038000c0c15941640b206d4101b01c10031007000c8540c2c0340a5803820f003d190714a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914382383 1250 914381133 914381147
    0xa031202150a0b0f010f021c030b0a172b0c080f270a060e130b1005250b0103060e1509030a030e0604020f120c03030a110c01080907090b130609060312 66
    0x903d03400502010307210f150344408c20803103484a14109070b6607000c030719019624100520020301041041071a15229500304a060602c00464000801c6c1200c0041441400038404a540510203060441c003209807810000c00078890164401c0143c080050400e50010101442207942c0c41d030101c9540c0c40c1c5200c60b00744518141d0301d009640c00701c0c12824241449240c145420720506506031004181c06100b48089968206201c592601081022400b00c8100c0f003000303500c01e40007c006a402d1460320650f140e00c02450018000038003656200d07803644913001020019508011032440d2200c0061902e500c000e034498216288250010342044040f40d0900c10009900b0b000782d40003230521b103c00708070b0400c00050024842c8810050700980c0ca441c0e25655050002d004411102d880e035840607000c2c0c0300001e00b81031a03441c0c900c2c10701c40800280300341c2c1d040010f4148240e0320304a40000c3d03100d0381000040c8140c0c0040c1c0600140c2c40c20300c0c1d40841d03070805c942c0100044030b00c02e094000c4060008001540c101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914383633 1250 914382383 914382407
    0xc0f01022b29061b071a030114040203180601060503060a06020f0d180305120315061e0a140409020a02070e04050a02040c0c0f060903020d030b0a031202150a0b0f01 72
    0x500d111503203016440c44040850b6860303200420480c68010113040060601c0341400c020301017a00004001c100c0f072020480004034404d0a98032142c80c6604210540c00e1041034500403a000780d0707001c00000d1007022286041031410803803004440c103546c1e40c1e085c0182558000c407402030081700100310000302c0e00d00010341001c0450b0b005000e449500d06d00e03d0111a04149144650700a603845140040840c02c28800d060301c581c010754501c0e1762482c0ca407004039010800b004040d40254401c2041c44241c252a241d04c003030102b80000c03105d5480c00c3d41c078011108a5090302c031100c00329400003800140f001c8141d00030022400036409540341c04d9551955070345a00d00440d8040d04e81e0300503240c200010302e020b511000b83d50395117040c0751300c4041c110b464200803011503039000c60b540e80d903400080048c1030301084003005000c0586801e02203490072354017103803002c40c9a100003400c44110120b00c0b1512030003031100d010a1104000101034a280c1780220b5400b40410306106800b540600c00c2c901921f501c100000215 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914384883 1250 914383633 914383661
    0x1707030512030705120a0221090c04110d0f0905160b191206081b0a0501050f070c05060307050d060f0b0a12060522060b030f04080c0f01022b 62
    0x11a9a0420000348070380c0c40100071000300481000700300101d40c42c0700b58490180300a9000161a4604140110030312440e0840092200e504c3c001005182c0c030300003a5801340c1160948000c40d50007410400d04960303005040d03101c52080e040c01a507980f4045c60b540300e47e880500401c119110b640108004010541c004d0041614441d010130001200ca114a465a07400c1549482c00624080c0d82002c83c03011250660440480d903040095000713880d81400c0143c035001d0108841c56030180c0e240900282c070703d2090b05105076104001042507010302190410354801824090610f598030319160354014500e0340301603a002e02d50b030701c0c20b0004161000461906016140580817040c9886074003601aa04c0229521049114580342e010110b1580c4403864000742050004101c19a0a5203030498071003511001d82100865003028810000e07200e140e010308542264000d0301d9159640d0a00c10904e0a00401c1074074020998000110310b290344030885044003441c5543c060201000242c858031000750b0300c003500e00e491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914386133 1250 914384883 914384893
    0xc150902030f0f010b090c0f0403021012091101110c010503011806080a140d02010513020d020301152c101203091a0304200904020f010c060509070905011d130206040302120717070305 80
    0x100500b40013010cd24140841d04044010903042e90010b0b05841210b0400c86100300703004a01009943c200e00c03c4c0d281c40b90380d400507000d00b8002e00002405404140729034004851400035a124030795040d0b01c2500604500001c1da500c80301241800ca000101441c4400705500c0340a101703483c81c030710602c111030042483c140118482d0505400300018480503070700903a0305540c0e42030700d420408910034a14008202003030940756220181c0c01809011070030410780075109a42e0408120740040b1300c000d01d40954000e01d14800044056003400c5801d030080703401c503441c1070701000c09140049860a002d940b2440c460200c543c200c05040350040c100408503142207800544110100d0018540f6450802204206141c50310904910391110b07810356400703035082c06070b41c0c200d40010707c00b04c05039002c0d9a0140188890100030701e61000201500d912005298005602160a40c00210358a202c2120019034000300b03422100b442101c034650f00ca210f03c1c03013040c4581118071000c1c8402d10740801c156044a4100015107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914387383 1250 914386133 914386139
    0x140307020712151803020f01150b0f0f07082502091602011b080103140c0306040b07090f030506070f08010b070201051e030f0709060c150902030f0f010b090c0f04 71
    0x402d0312102074404454034a458044500001c0301e51040c504084442d8007966600d000f01d003000f80c00c3c880301804007441a41480c070300c5d03180c0180c044040400ca9210a20055803081c1c12000c245040c000d104010b04a4900040c00e0418008020051b00040683e40a1400c1c44500840c0701c1500180c2800000c3d0002c02c564005010f04581e6003201884903050b0001240f00c07807040003808a00350804030550701090100e00103100b48190b6500c000031446980e402014440080000a42e0710000200700410070162800003800301449480781e00003c1114242e00c0d125241c403881c0468442c44201c43c0c0724009180364011844041c07181c005d1034100e0300408682840c00075107800450f540d5002c0700100c10030f80a022601c0010013013803001148201450094420981801540207000002c59401702c020400d0300d2491002040f00c09a1824034214003a1002030b22003400c0c03001ca400d00146503c070684900501140c0c82000c00103421680b80c0341400c40301d00b1115a92041c3e020400d005605e100e1310031500500c018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914388489 1106 914387383 914387399
    0xc011b09090b0442120308160f0302090d080c01060314010e030d0e0a050f030a090f080a0204020f0f1809071d060906070507080d1403070207 62
    0x140040b000d680e40300300d16400700554601c0502c2c9801074080072031440d40708030f00c48410130a40190b685a90f030b12881005c1d036900001500440c00c0e80000664540c009958058010101d4848a628510780039045000350001d0b445690042000d8000e84c0c041015140942650b40c107490000c102c1c0b504501d0f0203000b0801030503a070003140c2c0c10140307900b04011021040d00c048418241000821800ea50303e0203150440c3d0b468040d040d80114180614a42808070042c070181d1f041d80c8440345c0c026501c40354201c540d0a24402c401164020700450401840c1540060980000c2c0e00d41060903c1d1545505280c15806416480900c0c6c0c41310100405074200321203815408442410143c1c4140f50440003010040c15000400740301e800c3c00545000340d0342d1242c0039180d4080e04042201d1406454100d02640c42d0002012100480d02040c40c0908024410b021240b01e03000d15400f40c2545450540e007 = true := by decide +kernel

theorem cover : BRFrame.Cov 914208633 914388489 := by
  have h0 := BRFrame.cov_init 914208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 914208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 914208633 ≤ n) (h2 : n < 914388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
