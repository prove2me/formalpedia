-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:08:41.525983+00:00
-- url     : https://prove2.me/submissions/e8ceadb3-ba5e-4796-9040-4160b08c5c70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 27338135 ≤ n < 27517991 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 27339385 1250 27338135 27338137
    0x8010302040b0a08250503070501020d0c11060f0c0105060d0b01150207030602030403050406021b150904090c03061506111504080d090605010303111c0503070c050304181803021002 79
    0x800c80c050300b210b1943d03071280744891a01d9a05420b24015668005240240c10004211400103020079001410b0130741c10800040d480d4200c0c1c0b151201048254140401803040c0241907940900c1c000d40010355820820302c640c0560307030210451030349940c04c1c940400d0150611444041c0d0b4030790400d200302d029900340461144c4039501284800114425900c0c04404584148000c1d8000d80c0304e0303101c0d640e07624641440a4144000c1c60780041680038829102030181e1141d480007040e07000f81001480d52003100c4000203000305203024000c1c0c0380340804000070040101c2c9502c540c400380e450300f981490050766002c0440c0d21075481d9405e0303070143d002241d2140001e164400325903000780c450a00d15080244d0044403000300c420890003030721010313100c00c01041450b80212038184031001110103445d403045480d80d10030000c189800400c042000020000702c24510500000041650107001d90f603880c3d40d1030746200c600d4108030452a09540ca00000308401d8030301121001800c0e076040c2c005c0c2c48a03140d00300d40f070402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 27340635 1250 27339385 27339401
    0x16060806150a020a060c09080313030c050603090c09100803030f010303020c120a020f030a0f0803040b16050a0e011101020f0904050c070c0b03070e13090b0c040501092d0602030315060a0801030204 86
    0x18001d802d4804235018400b4005040c000f00617012040025287d41051b901502107a4400c6001c1c60040080c8101400003003091003042c8010344510344030340c441540c940d0307006e89142c2c8280c98a00011040c444008220034449040780e0003642194409840c5030104180c0b850700030304291403980110300347d500605200801070322045004050303903110901510303107442d05008080c0c100c911140000800c01080501c130302c001d402c040e1078070507030150700c143c132070045c15500c43c06565206001ca4268600c2c150b82c460341d20a120702c401c1100070343d101c0d07140000214050300560b410764440c1c3c0c2464001410070000d40e040d030b0041074001d008035212034a002c808148960001d00030f8000c0040c1103482ca02c140d00c4113004050b0b0300c049103c001800071424102484480b0018041c0c0492074002c20003000140e0b44055100150741116920100c0040516124181c0d01032620100403c1c0303035400320004800c0d4000c006180b00d100e40d00c2c9040801449581008014842c5100d241d000c241d20328014009801c055100280b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 27341885 1250 27340635 27340637
    0x50d060605060a020f06010902040302010e0906030f01020c03130512120d020c1c03050f01031101030c0e0409051e0a1208060402070b0c130e0c0a0f0216060806150a020a060c 76
    0x40e48a4689010036a50342c080d50003030000d84e00043c182100400c003049098010840d0500c00c6051504ad90b000a14001c003100340a840f65520f840407480a40d0248614280c0c0e0030140c00841d660031403c0342280e00c1c0c2c2c125200d2101451810800001c50b4203001041c50036904030003001d0004101142c00341401600804010719480e0303428070821180000030400740d0080110944548030722903011400400740c50006141c00c4880400340c00410000d00f44540700349044400342808508401c440c1011611a10180310b000d03403003401e20840708144038020810000e90300e924070030070f82856003901440d80e484403580001084404c1300d624145402e03104061440e0041c50091026140031016200c4802400094503410009080040e03010305000304040c01000402c1002ca40d100b003458260481102401100007200a01404081f8149550b10903c00800b0b0364541c648003595003500c030310b1300505290040b035030240101046c01c1e010302c4a0345000e00b41d912140e0294002e26450041d641d801025002e5001c4042c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 27343135 1250 27341885 27341891
    0x7060504051c02010609051305070302060c03070f0c0f1205070e0c0903030a030e010c090608131a0103060e010c0e03060411120d03020315040b01080c180603040302030a0e040b0a050d06 81
    0x719400c0aa061810b107105001d5001040040c2441139000442c0c401402c0101010341c0b071800e4000040010940c18112601101e89036295401400d515046218100e07005001d00340d41c82422040002104502060740c003a010301d40b403015150700d120314170045050009002035220f02c0041002c1c003298074403c7da1007000e8800c2241091280e50201c2e1450300030b510902c01103501e03005c1a001c560760910412002e1181854000f1566103400700c050312815019001a0742e141c496045041070000310341403402c400440c149582d14541c0d6a040c0309004040d0722072548860750a21000502d140d208980d80c4441c400001c3c0a0070440c0c0b20750742c1c0d0380c288080100b142074011440d040107411041d014420f61320403001036100582d0728a003506200c07060036043d05445200c1e0340b1f0178050301c120341d038032410081c1d01c05800040e80ea034901d600e1000c90f440101c025110359000400000308800c050703000c8080c01d0150300cac41c0c4800c0300c3c603c001810402514406441c0540081448400b00030074134286c520282d03083c2c00b80c1000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 27344385 1250 27343135 27343153
    0x3040f0c03080c010506030607020c130209060f0712020712120f031506030e0c031b010f0e031605040b0a061e0c0f08070302060c030108030406052224030b03030706050405 75
    0x11190f8102c0ca03510b010995441c1c0420840e400c1c1400450b0b4818400e00c040c2030011044070000342c50b0a101014440d107103502041c85403e5445010071101000701044aa5031122610301c0c20048209a10b520750005004600300001c3c00c00d0070760a02d09120b0790088212844910000e03007194851051210b0000701902c0c4c83e03140801c081c400c0700300c6015240d640c3c1c020851781d00c05e01d00d807031501051010850080e403003041d000c0c00140c0c41da030324440382c0e110919000c150140f1320320741240c00185040c001d50307040c0220710f4440340c000d0080c446442110401c2d5800d01800d9034410400820b01c000744151004030b84011000d07134210840a60040c16001e090800d404025016200c1d6603070b00a401104954503240024070805068040106607400051440c0c2c0328036660408190381d449000710300c525410702602050041d036061070002000c02c0070210016006099a4a040c1948582c03030140110407001c0040894244962082c003640d1010344003e801107182021b65992030008200040050303465008490107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 27345635 1250 27344385 27344393
    0x30207060908090f010e09060405070504080706081503011e0f020403050a110108090303070207030206090414070f030e03121302180a050f010906081905030f0d02120a0501050603040f0c03 82
    0x40c02070080d0003160302d1911440c0d118244030000c0c910301070070b9041c0141d003600b100d00d0b581d030280c42651280d002c0e01d0100c1c41d40c90701c0350f00352403601950b00700c140240a00c1d40c02003107107075001ca0018468401881440c1000c40c095041c10f003240c4c40c0c0008000c0c1e40b26031442c4180841890b412502d000403078523600518250b07036034882504002d6045011a0348044815140c0c4203581d000c0801c81d0862402c0380510701d1414007280c041d60b00c0d62140310003030291001103441c000c0750352a17a000e40d6a9520340c0305035954900c1c2001004000c0b03001d0300300307000c0420318001d45007039461030000c2036688030209020083c207503407900c841c50192040340c001b003207034400d80c006030a100d0303e001e0210386400755003200c1d400f003040e0508403200300080b6070580040c10074501e00703a0104540304000503040c10724400301c01241c00c4a0520b0910074254441e14501c1e9109460026038050250090f81c01404c11840b000e00003007071034941c01032203011b8071001c0c072a1a0b407200c81800420085102c0703030a03c506951040462024003903070ba9031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 27346885 1250 27345635 27345641
    0x6040c2c032508011505090f0402060702040212090d050a0f050c070f0b04060806030c090103060504030e120f010f0e0a021306050a0b0c01050a0e060705180607050a140a020d0b04020103020706 84
    0x101c52020382c1c0d0851001c0006540c24014030550745049805100c4031424030002c55945070004042c141e02d04240300c0490290340b030325000c070740040d038018200395640d00d00c464a07090742e644142d4490816100f00da4068207036a00c10340940b00403040300c0e9075002c0d58851404040300e19030003c00c2c003107005029051001400e40c0c5c8801c0e20000030401610100d07107440c64108043d0283c0b0340284901c0c000e40025400810540e5481c1d41c1c2415668001d800003040c2c1c895040403a000600050f999401c40818180103e082c03000043c03034031586601030000d02014010159160640d07800d10b0801d00c0d5584008145401440c000280810340d540d0010b000442c10f0b0f5410009448500c154000421071100280b964018076082c003500c0d6200710981018007400210050566503903000601c02002c2190224090b6248524014841e0b5503040003407403a5250b000328180349407611130f8060111401c4151031202c05d02c90344003107052400d80360001c0201000c00e2040e140c0010f02d2200034012810558200200000940544 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 27348135 1250 27346885 27346933
    0x9050108070503070b0406050406120902090106020f0c03190b07180e040201030b0108090a02011103090409140c01080906060123220906050603130c1d06040c2c03 71
    0x603004107003880c5800e00740340c01c0600c03e0b0010401a10100b00a01051341c00c201141e04a455603e4107003c0c4944058030240100784903c03000f5806078405c400040c0d002d500151042d031000903d010b8407000940041010b42d1010005483c00741c0304801941100030030942e85059600c245141880c07031541e0001c041d01e00401c80103400000b1b4440c007200c140019945d00d0b10800b0408042800d102c0d0480c200f41c01125a01c452205000341000083c0ca203a400300d250134026158aa0405007081c0440340440c60805019904130700030020511401041e00101e61061001c40d021361100310203041c0d0303a1601401103031401d400301c0000b00402c0c00d581c000707041003d03140300a20000030301119940f035030601410500701c071800aa20400c009414444140a81c3d5101d104480d00600c0030b07103a01401c100e682c5404d41020280da401000360007802808072a00b2016080524400d58007200e04008440d01000250b4403856200c501c0300845504840080e00000c1400c4865000031000f4201d036941c0301c001d0040600c10800c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 27349385 1250 27348135 27348149
    0x10e120a030206060405010b090f0604080a06020318060103030f03020705150403020c3c030c0405010b03041703070e040c0c020603010b04030302070503010b10140906030a0c0e0409020f0d020109090501 88
    0xc03900001456418010340743c001d0811034042c04503516100f0200300d913001c0d80021904c1000c1c1c00710842203da5550702201c0040104c1d0043c1c810503171007802c01c5030013904102e5083e060040e1041207924505008592981070703a40c0f54541c3c5c08840301c0420308a00940040404031407511406c203d041e607902c1c05190487c4924800e6004142852101007401200d40d00c1d01c606401c21191403c1d80203260a180420341c0b40010202e00404944103140000ba140410915609400a2030300c1c1c00442c44400440c015882240135005651340600361840100b2648800c0f90220001102c4c1c5103090403a18098008000c01d00591410410300d480303507000104258801e1384914040b6030700003410420907405009410050000718020070109180c24046080c0c103540d001808104000001031442d5140c020060b41c441c060064403454032440c010034064024000212030320003003440031001d14400e15060242e03d40496000c0c03c601e040940c60001d001300d00080702412414402d2199000c15084e40360f114541c001c00807 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 27350635 1250 27349385 27349393
    0xf0d020d02030105040b0a08060c070302070f060305040212070605030403111005010603020a0207051801061808010603110117040f06020a0507060906091e0f0b10120510050a0b0f0609010e12 83
    0x341c40200300c119a101b90f040c070f00440e88104100f00c00600450407651050382c10210310780e036594924049081050503041050140f15441c1c000c103240c0d52507840076100b41e1007528030403804000c0c0701c4910b6882d441482400300180e820000030b0006032003004001c198400d4841218030000102d0301c00015140247c10020009502291240394160304206040040c0380681d4055460100030000341e4048405004540a02c00450908884d0408165110300240340e150b000300002900d0b842c0c440785070348000070380900060050040c45080c0d00b0401d80316001e103a0040740c07401d0b000758030340e5a0406500b08512070824000103000e4000804d4081c010752420320311074000006e540c0b45503d494046180104800d0144410301c2d44031000060015040c04034046d000028499241e0700c0c60490001c6509903001a1418808003e020303007048000900600701c00c02142d001d002d540d03102e0703904004440908807255413103881c15409010b28107000c00101000c46040c50100c158000f41d60101e41c0030400d000300804a544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 27351885 1250 27350635 27350639
    0x3030e01090f0b0c0403020303071b031209052704030e0f130f06080a03020a030507020a050a060305090c040b03150a20030a1406010f030c0c12020c090108010c05030c0f0d020d020301 80
    0x103d04420550220a095185040504540120f903480c020090001e1001c1040d07581d03038400e1419500d4200085d42d02828015180005110081030748a051240724000c91113001a0b5481c001c2c03061120003c1d10703d030700c1c0e0784000e0740d501e40741150b840c0d41101841c0e402039501c151800341903e5411420708501c00741036000c05d010206040345411203025900a0b4090b40084526800080e4085210000150103140050701c039205030000500d4003c859000070351110820718000380e20754041c0c102c5c6200d070041f07a0a07a94180130440902080d40e40d200559545a0000030203100301d4403000d850700782c01801c440000a000424500d203810100417040c0d0903d40000b010040110218a601413112114480001c002c4141031007800640700b008225614803e2613101c0070200344503485102c036000b540b5008040d10000064851000c0e46580d00001c44a0180301c2d04c500209444405004206c03240301c00343d030360b02c1c69030f88c1d012000d9802e80c012010a0301c6111081010055000c014005031050401000005903294 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 27353135 1250 27351885 27351893
    0x80402010c2003100902010203070201050304050c10030b01180305060628090b28053705100203030115030c020304030503040801020306131406120a0212010c020d050408071203030e01090f 82
    0x2901013000461a400e0901c1040180d0340407017602c480a40c20701301607890b52a285040d900b00700c010039103190446903020000d48800e0385a001002d00b6002a201d00d40b141c1c08812000d0321419090001074000d0b408000030a40d542441c004240c1c100300079003154074026001041b0181c650003503500084019864802e05074081c07a0428403038040c1c002c0e1030300075141c10003050f4401e4103005051280307a2050300c840051215041100103810a80000030300d04e40b41c0000321103442e03036201c460b5014250040c00d207140d403c000d40d40000212416181c158003c01c4510285000c1100501030885030b81086000921000000882c1000a0b0001d4003a032400582c0724a040001c1c841440505103c1038403450a143c4003031803101c0e520310620382111064070700c40085200c52602c1c034038000448e000250409840d0780c0010806d42e065105047c0c00c8055801d0b50703003042d00048104e40314011801100700503000142e003000448140e03000c00d84a41e2280c00c02264540344007103281d08480541005580e1817400c220008104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 27354385 1250 27353135 27353143
    0xb01140405010e0f07030b0109030f150f090807020f01020f060106090801051312080a020f041202030105070c0803161b05060f06030f0c0d020a09061d130210080402010c2003 76
    0x5003807040b00f000f543d46800002d12401000103403170f00090580d01d0000e002d10380d215007210310140d81c21680d03074188a0b030070f440d004c60080b910110850041d0b00c1c2684a405a4085024548c00e00f40c205080030700303061103034007084070846c00c3c9074440b41544292110800c90100c01d002541c0200150740f509082c682c0340000d12030940f00c00034000311500308801800800a960b501c01c6503418401072406124035aa1403035a4030007845102e44250740074901290000b074881ca0090401703003082c401ea00900480d181c05e0000e45d030591492000501140c400c0c0000f520401e038002d1011058480c620b0610610442050031020340301480c242075649401400410088240d0480e01e150011001e4000303001b662000ca4080d5107501c81c101d8000d200380980c4107900305641d1808260405801381d040104600c1c0e40d28424014148001c0d008103440e0001040000e0f085880d10284401b100e401401c410b10308031810004592075040200101c0c18010b00550087c0801c81d0064103122002e031031180145c50516440401d407074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 27355635 1250 27354385 27354389
    0xc060f150a0b0301030303050a060b0c01020d1a0f0904060204030807060e0c030705030601090f0603081602090106030203040f02010806060c2d0609030f03040203030d14010f0506030403020d0e0d0b0114040501 91
    0x1c9003103030303000c100c01e803110002c90b411682c06150000e20f54842400b01d402401d126440b0840c0d021000c500c420100606500424a1010504c0100604011095071600007a038800003d0760200d49040d8071069414440c03034266000d48100801480c0c16103d5594003500e4105190955000303541c1d030000c01941c2810420303841d007603c0440052540a01c1c04000980e1008140140b001054507070300304020b501d2558000c94055944410034a480d40c0c0140d0042c90100400c403010792295900800004005000e071007100d02854000214405c44111030b00150380c40d034000b4212a400c000c00300a8840c4480c6d0500003541c003449080400c010f440c5989202c20102d011504a00c04542c11410600052010000841d00d02e0014086115143d90780da000290550285410800106080c0780c1055842e580c4082e502c5c0c10b03603088401e5411400d4031001482194002200c0040c0580e214101c0d2000041c0200e000007107c8000801c464480c0089a4481d01a051f00380d001050364080141e04103420b250070b004081c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 27356885 1250 27355635 27355639
    0x118060b010318020f0312070503130608011401050304031b1401060b13030605070507020909160f080607081902070503030603010b040225020a030b15280902090301020c060f15 77
    0xd481a0501c0030f404207400504020700c58000491501c0d010b0300c0900100c03809030f500c80b0102e5210b16990408070340f00da0241150001200d01c020010070800d020303c044c1b0f03060301d015001428028151400648895001500590a2050f21100c0e481c00041c60f00820041600ca041c80803189240700c2d07903041c05d603806500319042c198070a0203d02040807040300801b084070f410010100341511100020b840c0c3c0d218000c4043d4010210743e042081802c40001c07480c4010000d204081051503403000405070150300c070300036840d42c1d42048011030f89003031050808503085003041048400100322110ba2008a0381300e400103c82c65000030003000104c0c41d088c0b2035004410700590f810f6103000034007612150140b101c02c410740c11000480300c281c019501c489121001079035220100203a28181445140a5041900d404d40c0c803a440f40503102550001061a10746200a6042000ca240341000740c60f102941101594980666091104d00e0041804002c140d0007644211181c00850420300c11020002500301d541d14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 27358135 1250 27356885 27356891
    0x390303031302060904020d05070c05060609060109090f060f0602150a060b0901080c0706060e060f0a060207170313030303050601110106030209010501030203071b03051b0601050a030809030a050118060b0103 90
    0x128000000e545585180d40e0b044a020750b50300c0d00100014003c1c01000820384040b441c04040003221313a0000d038080f1002d802001240c50070741c0c91008000c444101110042c0c00143d41c001d08001100c5031b904044400748460501007000ba4030794805920400300c41d848900164000301c03020b02d111112001160300884d05070700074001d15041080c4c2d04480c2c842c40000f0350400c0000c034001409070144000703480e4420344c880010700c9116980c070640d50001d03400342c2e8000e02c039107488080c18107a0301c2d0903000f4408032079161b0007034131109140640d0345400c030480c0d0440d1821404100f002d020788880200005020710b100b900d000400741404070006200310111741031002c0076807400d101840035996048130700303044920074600075036655034400048401c00440c023180301d007420780007000d402059000005130444403101240c1c0680b2080e030150b96035407004280b281c55000000b0440a0020a981034020107ca080103001c440c110203503951804c1c00c440315808448048140900004104200c600412082c04801d203414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 27359385 1250 27358135 27358141
    0x60403020a03032303010801021b0309090402010e030f0a0c08070b070f0b040606120507030201020607020118080901090b0a030b04060b0909130c08030a1701060311040603020c39030303 81
    0x11070749a10382030202400340309000d80300b2079541d600c848902c407030048201d41542e1607503500c00c1414040e40014400c1000050035070031100003588000203035100384400500740c0225446a40041d00c0c80121044d540b5014014081580d64001c0100101d06803203205030294080c0602c0c001c001e609003103164000c0b9680c1c1c041000b1080100d11020300303580400e50451051502ca881c0c91030240700a1020354040715882c4040c5000303034144a0702280160403a0f0003038094407a0755440420480c00c0780c40080c3e0015842c0603c0c02241c010441d110042c00c114481810102c05458071241d0324041604004603507000a034840d55214010b04003405120000c20b24000e0040c140303400c032000201c40354401050142080f45007100c105c180620301140034000c0841070107a03951550740c00300c020441065a0f070749075085030410300000741203442880303500d06a1501c03080c0a801e150030711604030007a6100c03400c01230003442208d000442e07488050707003480401254070307501d04d208480c54002903845842006407584241c00034010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27360635 1250 27359385 27359389
    0x302031b0609030a1b1203020309070902030108100b06210106020d08010e1620030a08090a05070b0a050712090503010c030506011e030f092303090d020405040f1401061406040302 78
    0x641d4021012824417070341803082e003540e2080b6a02c08442c081c00314071981c07620101036a090b0f80154003840790503055400b101c0e2102401c2d003d0307100038800d480103640450026a420703070b4039a01c50340c900c8100601262610300303003108d0140001804910321000d004d0380c0740100005601000111410321090070a040c1715854128040340c240d0f8010a6a00816000c0c040003a41034440d40c510842d001c80c008191040d80041c1d10300d2562a0803410502c400710700e100000c0741058a00041e0b07a411942d0100003014054148428200f00783c101010340000d1203801e012080010b4440e00320038040c00001d07550503020900d00400c1500b5918481541401c0c540b41605203c1103036400305c510315010005620701114502980001c40040144488c0b141c092440c00ca0200d0030094492120b1141001d0310030801c0c0000c08059200c4d440348903071001c00c2d40c041900c1070b41c103005052540105900a000d40c01440c0d051545403220030442c0c200a240c0000399646203000c0c4411110344d00e041c01011030035100c140c1043c1c02e40e40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27361885 1250 27360635 27360637
    0x901020d031a28030b07030e0c0307030f080d05090c01030b270621010e1c0c0b0c070b0702060609101202060708040506070305040302030606041406040e03160302031b060903 76
    0x10303118001c0004158141e903c0c211003c0804018408800c0d03e440c880d40e90400b904421419210140064106204101404070001311303821703583c80050142449910b0360f138900b991035580c01400c03a2054801c2c00310840d0000c040c441c442c403402444010700341000440d80010f0445041c912003030312840c80c9190248122030034141c21500d810808501003040d884010000307040c8207401c102e40c542000c215605000d90041904003404100c0c8810485038498000c00e002001900ba03187e62a0008407411552000700707040703001560b0080240c50340302c0d02d000a41d4885c0c0e07228010854840c000350780310710300f48150380c1000191113500c09958145920345c24100a0081c00c40303180c41c03802a101d06008103040c018019001d04540051000030b01180d91403400c1d1034054140c0e00148030913407082c002e80c000548181840c0c0140d80030203040c4940400c440e9070703100400c00201040150300030b035840140020425928035280308036816000b42c0056464907142c0102c0000d52450881291254009000748804840000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27363135 1250 27361885 27361931
    0x3060e0c0d051b07050a020f09070503070522120b060402040803040905190c0207090608010203010e0408070c0305011e0b060a050304030c030e0604060305040302010b040e1002091c080901020d03 85
    0x50741c0416261200e40c98010002d40e103165182c41c00300300142180402a001448644040c400d03203103400503000c800d041100815003190900045802000020603151040000b000700c1c084009070f036503481840700340c000c0582040741c202515440762022030809001468580581c843c0044505500d001d0914000688a00030b40c0301d1000000d440380045048031800b060307000b049094481c010400c500700d02d840290703103403558403c0701b006a10384200810b802c04180201c038180c6950103940348154581d5034400301d4640c4400005d441c4010300103404000100e080c05481c19107142603030201c910700f01c5c00d036900080340e5000c0c140074441c04041014400150308142070384e0388150907060043c020a01401c0a907070081080a5480d4481c170001000325945400d035000d580154020740c002c1022440820501c0201d6071101118400c591000da001000080d130364009009411002d00b00072001400d08104a940c1c69140408031585030000c1001d0656590402c80b956105806140510030407109040607968600d842c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27364385 1250 27363135 27363157
    0xb1306032001050c0d0e100305010305190201020312010801060f0b07050a14030705060a05240d1b050619030506090103030912060204030506040c1a0703050d020d180302060703060e0c 80
    0x241c0305140c6160700600903640110750071015140d006800d82801402c03420007010300fa20410b00080c0d0000790b20f00c28130582d8140c0350320100500003009a403816000c4010300c4c520803811440100001e4504005240041c0e008211380350010a4160404040c10611a0b05030003030002101d0170300c07085000c2103000030f41c00b03103184c1c1010050045d00d0040790000d05611130103402416a20494050110322aa01d50080703100b00200c8010300d4400c40d200d0840140c1d015030f010313403d500c080380901100114810085050f65800300e4402e96042956840210b005500f100318400c5460a4810102e40ca0982500489900500480d14010258155a0040d1240449001c0c0003880a64040c800041020b150b046501950300700c01203994502c0d16140a0000143c035009141d481120b81d00341c81800c100c0c09095440190f4035032960703424040300401c500001d400509410005507260f00a134010300080b05d01c4440c0c1503001e9409010940740080010b4241c4800d548284440c00e450380400030f1400c0b0343e1060320164144 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27365635 1250 27364385 27364433
    0x30109050402030c0315060109050609010e010f09050a24050913020a0e0a03060203090f0d120905010b0a0b0d0b0306010f0302040b0f150a03050c07050312041a01090b130603 76
    0x7541c004a403401c20210300580c1c2510886500c040184003c03a00c3d240b052200343c1c1c0300301180d0341311814064180035503200c417804a00c110035090450360040007039601d45502031406055456031440042c1c8080751990013442d001002a000078a04d84e034208050844081e40e0521a00d403002280104008192600004c031000c0e43c08070300811414824481a100a02c00802c3c0d8068551070f8100080203610980c0c0c800103e1244d044403168840e0046031181c440003254542c2000311048030b4040c80170b4004010221403035581c0d5100721206980c1d21068401800303400000c00d0b10741c220705040b803045400b01000c09219a010f600104441d455100c0034100340c07541503602068a42c80c02001c00c0c4184501c010b25030b07002040c030b610b00850102c540e024101000c45a0b905004135190b441c61101e451050707003009403641d0802c01c0810043c08100010303541081c0b00c3c010003030002000ca01c0b0a48124802e0b00b001c4025521130381120703480d1806600d1030790148200d0030100451845c540d00c5a044500941c0900100c0e11 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27366885 1250 27365635 27365641
    0x8070513080114070f030905030d0905070f0b0307080a0e0712031125050a030b010e060a080a0302011a0306060907030f0209060d0f0c051e0708070f06090b0703020a020303010905 78
    0x20319900d150003081c02100030b00500031201c4402041802c101e90101c000b42140701302c101c0c090b12030b010700460036070010b0186140c84020042e5001030602ca103020351303440c45603901c00200f440c20710b54440002c0400c440c0e00c0703459041085d0001d00014001d0b1000400905041d071038007901c40c02140c00c5040f6480c0043d0f021501e002d900d4151540034405201d04601d02078003e4002e640a0300c0d861500c881c2503000c04440c140b035101d00420024001a0002500e003c011600510003407a0941071150000300040907402000e5607029160329202d061101100141d4403000000c11070703402000320b04ca82d09811000780460f80f80140c040348004500030019020541c5070001d8404a0f40281e0443d4200c0c3ca0142255a42d200101d00140141c810031003900e540307516040d0003c0809100300b0a0300e602d0b90f032542d581e400e909000c1c3d52018050704058825110200100203140000b00c0521941103440d104d0b8101080300d9089082244617000010f09220a040c010415420401d90102c1145e056544000780043c081d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27368135 1250 27366885 27366907
    0x3050c090613051501080108030f071202030705070b0711040e0a0201030b0424030506070e0a030312061212030c0e010207050108091c180801020414040b0d050303071101140403080705 80
    0x1100d212602c50240b460b000a028141c80a1001400c0c01d1a082c0c0b92440c50307907a80c00e429a60391040510081d43c5450a0003448001584920b0311043d480c07003481180c2c1070200d50303183c190410040d5889050000e00004116081010005010f44408012241004400605982d09860f0325801400904266031100580c1c01e55650b03501505d101c114942800d00b4001ca1803103a0f84114503580001c3e1814401c00d4000b462681c0b203000d001380311140262160050925598056a03c0000c110700c5482403a12920045007010103550181c0c0454083c80300301000125140c1c000e801c585180201134100001500f070240c4598000400e00225402071810b903000340c0d40c001400e03003403080c00100600000c0b900340346074900384d60103c1952001503440ba40c1410041d6a03c441e00c2c200d200d14400c1c1c41c60200c0c04219041030740b41941c446600b100014080e803e01c3e0100359076050440d032088940002141626154101e081c4091088050406290039281b1190410740c801404a0a006041c002000707070000b42c0300c100d9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27369385 1250 27368135 27368149
    0x120504020315090109030e0906010f050307090504020d0c0f020106050105041404020409020a0203070516030b01030605151036030807140a060515190605030c0c0f0d0e0a03050c0906 79
    0xb420030210240c072508204180c0781c060094043e082c0d0001d034820352941c1d41854000601409074074141c45040d685000d011040d1003a0f00014642c0701881300442c00011701c0c2d2518001048040351312080060f030440a50005444540d101e0380403030441e8500141409281d800c10200c6050351140c054864109900400040107403050341c04c0000c24a0002c10401c0031035800001801c2001c0c440ca0660340480f05016102c41160902d10001c0c0c1420780311001000800c1e02580050340161900c962900b075000564040303400c070072038016080c002600c046100d0a400c085038241c00700145031103201d00c0301e0605040e108000c0710035500001e80104000111842003100540d1900c03c03031000c1c0400e0700d04405081c14603800400040350f0b02c1c01c4158404400c819a0b00c0c0c600445000c09480640d0728040e035081c03001c11200354000a01c40f201c42c0e00c08122888035110200210003020a52000822456401c1c01f4000c00d065006900a40a810b441009000140011a003202501c2c0b05840d0b1985c0341c1e585400060310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27370635 1250 27369385 27369403
    0x90d05030409020c0c030604120c061b08040c090c05070818090406150e061003090302070f1e080a080a08060109030b0403020f0f030322020d241b1205040203 69
    0x2140310015002a1600b50354000e44140010341d015140b104410134107041d166441180c00500d0011400b45800d6224024400010428040d040c0051201c809429050310500b00c0015580811500301c204030800404c0d800c8080074003c012000e1180351020003011b0050b0068a030700400380c04020541d07480c00030005408881d0761350000e001c811141443d042807801884240700300c0d5507500740c0f0030b4042880d403403c05c1045e0142c0d80290420303161a641c00380c218001c204a5070110114041d107880002c900c4051104030000e450010600d0080320140000041c0380c0030254018001600b21074800400f180441d4242c1e4045039150030034022941d10a00129529011a000108030b95022002c0c00140750740050381e1320001d092001110180f0040941c0c1170343c1e0340000c070340c2c56a40190380d5007a0740011a040e00382a10403880075000801000160741d89201101002d094214002d60820080c3c2c107452190050b014820b1501e42400e18242117008002e02c1d00c611b034101d40a10350748a8021404548082140c484 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27371885 1250 27370635 27370643
    0xf110c0301110705010b010c23070902031006020c0d032001090501060e070f11100f0b040203130c15050904020a110d120f02031e0717010618080607020a0602090d 71
    0x3060b22400e140481a82050406541541c6032150322031655020b10400c2500d150043c1e0441080034008003090171400310422804940c0c0588038001a0000e1180060b50007164160b84900d03000382042e00081c40c6c2240c4205441c0314810801d0203d010030b811010900b003400e0600d040028440380f118a8078058400c803c0010890740c644000000e04913800c1c510345014001c01d5840341249510014111a032055035002c00e40c40340c001c0c1410404038101c683c01040d840301200c0001c583c9030701c4540050200d8204981c02c0c0d440c40c10712200b40040255014a0201426800c043d1a2a02c00030440007040e80c01502010703401103900081801d180c1e0302035a4280350307010842040390080b81000134018440300c5007402040e03c40341401a07052040c1c0301402520f00c02e10001c0012412460350320104180400c0281c41300d018441030b5940750b20150407210030607028100589404414080c921030140300c500c0c0c150312402e4540c00000500181c1c55020681c41070643d006000540c60344100d0340003541010401320b00030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27373135 1250 27371885 27371891
    0xa0c03050d110c01021e12070501090317190902010c05010213230102120307030b0306012309040506040b0c0d0f090507050d0305030a0f020910020102070210030c0f110c0301 76
    0x40050028480810841c03a0751201c40304101142c001c2c0c0d681020205050260b0801d00303444100c00303030041e518039201c94a102100c401d80329494045800b0380c4429015120b80e5119075410342031603000070078241c500202240400c0d4910b05080201c2941c2c81c080d210403000c903210203170502560f11509044040c0364125008547d170340c05040024080003240d20914001034520304481d094500b0110a010810038184c0282503200007403010b032080c1d644010890010f05981c0d0322044441d44040101c40d0103020950742014010a14202413120360b4110310031184500002420400000c5001c00c10035001580840703041119154403d01c042d00740180c0900f090380b281f804580004081864016120b598058001e0312085901d460070301c50560004500640400e0013040400d01803080c1e0f5000e1229030700031210050801441000103202100740d00e050900603900400c025066182100b20f41e64050001d04080000120440c1c0140174400d2800b888000e10450356210005001d042c404600d282e18020020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27374385 1250 27373135 27373139
    0x603010902090c1801020d02030409110408070e090c0a0b0f0a12020a0c02120f030901081b0d0b180105010e04020a0203070b090304080d0306450b100801030b0a0902030a0c 75
    0x2407409400181e103c401c4c2e82076050710200c241d40081740d090300a05a0364061490035060102d080050812102e074000500010080010b913043d0034441d82003e0108445058a1810200243c0345409608007c00d8420000f03840c08004035510b0104840011740c01c52100d54903240c00c528240d4209118040300342d44ca900000324261141d90015010110074402c0340c0d040d9410728a1400565500103c500e600c00981c02000840042c1d8002c080d25039004150407024006d00006000c40e81080e0020482681a2600c420729546203213003c0e8203448807188941c03001100c541c50000020b010b8114010050300036580042c501d03110f07a00c203208441e2041c0d00408a510741d8241400711594030780c007912414000e170040141c407c15140c403e0282d0000c594020540c00190700ca0003090b9807464070704c45a410010360f072543d581c4000c0c0d04250380d2100744085200001903480e100c01c0510a121030501018810819900014000910440c54158001401079000109140c641c03000ca032410044034006010301f1940680 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27375635 1250 27374385 27374401
    0x60822050d030e0105090c0114071403041401020309150f040504060f090e0d08010501081015020a0c0501030908031f081f0606090501050d090302011506030b0901060e090f060301090209 81
    0x805100c07000703035038040001408444034a82241c0056540c0300d443e410078001240e0300c0d03201d500c424000c10000f4004529104480ea920702014440b50f0f42d00c4c0385900003007000c01c0100184224010304d46c400f800518608062000000d10309a0640880c072607240000c11280c51024044040c2c0e0050701002d03100b004884d40740e041c01d1f15004464071840700481d080c004500c6d0704143c00710300d1030762810302c0b0344038445181d090500645d4080d04c0100100c11035006013100140500c0c031014411020b50b59600034118280c0319041070f52101d5032907080541458101310313845001400340c0f811071b98415040e003140890364461034030690300c0226a074442c2403244601ca41c414010458812204200c4490003001c105442c0d58217800e60b541c00891143c0c2d40441c4c42400713010160301c003a401801c42140300784000940c928400c01c1c0b16003149080d0b0030500c00a5070302e00f071880150801004250151880e81041209650704c000010f500840041000448000c21004204035450942190321015070013007040c5003e19012070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27376885 1250 27375635 27375643
    0xa110f010e0c04061e06080417030403170a050c040611010204030210021b04090b0604020304050a02030601060908070906080c01110102091809010b0a06080c07030e060c01052401050406082205 84
    0x42c141d840f03a403410400240c8103400c40b080303010f0000545a00c00696140190540f042c2c6801031007529030f5040340420310b0b03d07546030200661269210703407551805008810441c0d0f18801004005084644c40e11003072110600d0038500707481c00c80d541e620304610400189000c00d40039010f25031009400c00240300980040c941c001c6036000c001c6003a4485980780c00e90910401c002c0e94401140502011040008210541450f400460380300740aa01250b1800110b076011038a441d409900c2000040c0d15404240152401405800d00400c4056402d20000382024401c940718010070342290305000035003e901110030350079019181810001040c1c075202c0c2190202580c201c103001c880c540419442d2450407200b615288071200c007640c07101d5803880b88543d601035450342c447c1c4c02080f040e0140301d440d03c1d4910b05952024010305803840664000318090405500501040d50380c5030315940c90724480b801856059905c0310aa03070440d0309030301e0035204030b40380c2d165801000d9040a42400c0703186c120500c1c07442030010002d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27378135 1250 27376885 27376903
    0x60106020f0705060306010c020418030305070e03060603280506010e0403110d21020702041a010305100803090103050415180b010504060f15020304080f0607020c060702060a110f010e 80
    0x80c081d5004440407014031510b4404901440354403040a001040295204002002d07969101910000303607150044100c0d0140b80c80380d0411030019848400700701c60340e5030106141911400c254024480307401d0030030010341c9500762443c2480305808880ca61002c42c0501403240260349400c207066403002e503150580014994030032035040e1301052110314040b540d11000a80c5920034085542c80b07103200d00050408c900c03010244448a1241ea40038455540565a80c1c428400c103d00c3c3c1100300180d10980b03a0016080d104020001810070a1014080048260102c11210121800d10700000d0503a240c0c41c100380024045454849003900d0301c2144507590710b1100741030840d14000c0c60b03100c219a0b81d807800c10065034058080e0b211013003444901040b80041c07102100e001000240140c904141d12951a03500c5c1c2010170010703c0d4550b1042061111482d01030002249001c03042c3c64091030b040d0560082901481124101c03000c02c040b50021105164060040555026006009228545200d02440d0344d64a000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27379385 1250 27378135 27378137
    0xe010608060d110904020a0503010608060103021503010b18010c0609080a1202031504020d02070602030f0a0501080106050d08030612071e0f050a03080307050f030a02030103061a090a0c021005010305060106 90
    0xa000403500700d00e00002c048030356560000f004480254244180075512102400c200e03084010b1500100d400d543c01c4c01020094501c0100414103589036004021520350740300e0001d00490020001400002178490481c1d4018580f42c01340c0c0c1c0030410352001221860814603015103401c3c03a21104100b0440c1c3c1c03000814130869141d41d0801f01aa080069204a00c400d441000008071210300c02d400f182000e4000e85291200c2000050030000642c440070700740c0e402102c4c001420000c4404000401c8003902c203403401342004000030406541000d0114609408111010308180c5012000945550313608044085080421007502c0d0b8899407001c041c41c0c40303002c2449040e90349030030030b501092980290008100320b520043c03580e03400518603110407289900103030440c0100708040040c0003039010070b440214011140032100598a40c9181404003ca8181c00300696003120030f000c05080c2035862a04442d0011058180005c50407a0020142e180654180d144a4014281000081400800301d04141200c40d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27380635 1250 27379385 27379397
    0x12140f07020d0e15040e070504030c0918030305090c0a0b0a0201060503012a180807050108060105030f0f0702010e1207060e0a050a11010905030312150111060f0c0708040e0106 77
    0xa0a100340d864420840000b00040c8190303542034680d103050f480d1910903c05080c0242c0c9455221210030f100b1917012150100851000201041002030005d800e4000f020401c1b420403101c05241603008001544a00c00390406407100041007161f00c0600c5000d0104200400114528bc1d8451051510b50040c2110b240503501e03141c03002915017010301a42064944400051450702030100400521421007174015082207890016040441e900740070610282c4900c00c01881058075060005001d0300e0000c0042e41088414010300c07a13400c00d410803040d0031044040398082a5a070300d100c02c0b401000841408903551241213507101c01d4244c02d038010003125001700014490315000d80e10b01603980342d209000606591210a09102144070603000400f140414034003010711540c5e9000203441c540251210030703400315003001401116080c503c4000190802070906d0312690500005581d1140402402d00360416a441d0000e10104d00403801c0310803055108190b42e0305e85890344548068054240220030209007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27381885 1250 27380635 27380641
    0x70302040506060903030712030209030a03020c09010f0e13110d060f0b01050a02030f030402010c020901090c0320040501080a06120c0e07020613031d032a0d0c120312140f 75
    0x10507500721203025034045c0041d49019203543d1201c04820503a00b203c0101035090100110030fa8050002d410080c1c0280e0040003544070304400c2005140303042c5d210340340c203d801c80020400202d00c03440d1158011145060925080c0306800d1001d9445043c40400b58465140c0200b0800c01c04180d0041101101c1076004101d00c080510054859106003010b070b801691040c010b95041007031600c025940648103241c420042d03d0158049001c50320700703802450f00300ea280c110f16404158140b2401c1c0800a5001660030a800d210000d00410310584c001e650400c6112000210094002d4200c2001481d003039141d0740301d2006030b04010b9200e44403401461000098034011507216807000403024080c034800ca84011900010380d8060f40c4844407000404805505426546040d42d001c2c0540102443d041c00c6181540300316010341c0e01c1d400070048000748111004c60004021502e04d13410441901d490081018140340f40f400c00380c0b040d040004c076021480b402c0803905500b0010110f00c66000b90314012607015591 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27383135 1250 27381885 27381889
    0x1020a030603420b0303030a0209180105090c070503040b13030203060106030c050906030402120f0303010819050604030305060310021305010f0e31050a060302030f0f0303060112020f0c070302040506 87
    0x42141c3c840a07280070810403070401c1100510f24540322003401c42800194000025011a0554100f10b508024140c0c0c0424140d000c2d082c0301d42804010510146401000e60500300010072501000e072080b08060404104e034802c0210401c1218007a1080380311032900e41c80024150b0721043c20f01c1c00304038024040c260000a0440c00b90142021082080e103480c1d003009904000c1c44080d80000703000341d0b03001c1003d1080c0e0b04080130500001048407a020702450740ca604051080d0300d42035805d01000461100c0c58441c030007180700840c8403900030380e043c500840c0b15242e150000f031610b60710f0290407590500c00100200d240c6c89001c00282190400c0e02c1e1b949114425410590b0712400c038400e01c58120110101850700b01300c80c560042e900076020040300d00c8002d809140b030400c46c0c0c2c2c11030714445010342d900030500c02c0d07260401182055185c0750004000101c6012074841e124080508418140000c0600c030000007409501501c4c0030300017002d441c0c1e456052000c800359440f100c5100c20790045180201241e414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27384385 1250 27383135 27383183
    0x30c06090807030303021e13030b01060e06090d05070510020609010b0604030503070b060301110d0905070803160605060609091608070509010c08070602040b0f0408010c08011a07050f01020a030603 86
    0x64100c0409803402070303e1518203801a6100c42e0f8070940d04110040d07480240d14001024080e103030034440d074400c0072900314544000d404a04ae01b00301e09000c03200c00a1402943c80200312120f03000152502708940d81e251800034501599078002c00e1340042c140000300034a03a40003642030f01c41c419100080c0150341071001403001600c41c2e4040605260400c11096002c991707400180d5410510140001911003454891212103403c4000b1800c0318075191003620040c454100071043c09003803a04007562030700308402c00389121500c80b00f00c010002a200c100140b0a030340c40c0c0d42916040180540a1100352a00c10080302050a814400343c01040048010510040c4908140d0305401c1040c3c4940c1c81d4100c5640f81d1a0140d00030090844406030200008600c442c1c10802a0010400c261860ba44580c203240300c0c1403d4407100302c1003004004804004000c240158208502c0d074610342807c0039174030300681c14420300380703290004015442e60002520819251707069015204503070044010110032034810b1304110038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27385635 1250 27384385 27384389
    0x3021903080f090705032e1401181e020c06070c0206040605090a0512010203041e02030601050409021305011509080313060f020f12030402010305060402030708070f031d0304030c0609 80
    0x1807821000149040e020300a00d5410006035400c990f0501e50744d20002e4900010404000419980076440840b200800703030300c03601d802c2002c3d4810300c4244088003062403c444140300c1d02c04c20b140d400c03203032026803000c0750300405d00d40d581540142809202409840080c1d80503015405c1940304810010304542d204a10600a1660040010b441c1500c1c2940c100c2d0584c00001065510041c0008002a0365542041c12108440c00c0e100160b124038160400e1034100900c0310400b050b110002141d440180d4012440a06480d82140c0004021340d090010807180d8110841d2203c0312490b02c000031940d4500d2801680c1100015a503a40c0300c29107540d02c46032640034408521015810094080c0005030241245c07600d031014501c1202c00122400072014a40603428583c00c82820000007403200b9540c0c14002d03154014001d079025455414000f200420b000300c0200b03900c040140034856140c4840c03082e000f815288401d01c804400540d5800c040c140c883c4d1040c402190b40203010680022418064a03034542 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27386885 1250 27385635 27385637
    0x7030504030f0e0102070806040b0703051006020709090f0609050f0f010b0f04180c030303021306032310080d020601090f050603060106050c1c030515031207061104090603050a03021903 81
    0x1034140b0350304605482646803010014190701a900c00491f00820030454039104078020b030039400c003034205450081c1c01c0340c02c090011845014042020300000c1d40005132201103551000300080d2807561810003116245d095103004052508159050061100c00200c0c0e185200300300d000e40d00c03030160405001c0c1c00c03140381c081c100d0380180c008000d18000b490140e2040001c00c129400c0c50905050355a608090014185c00c200e010a6001c2003c600880c400c401040c043c0415080c200040d40003520b0340e0200241c4401840c110b111040001415100b81da004c04008084200031150003088200e406034491409004100c80325141016030b00da814103034083c1e40e00410700a4050603d90f42028001c5800b0790003208400c54900c1450f038140d40711380c0c80b008400c16812540e58005140c3c10800051101c2501000000b84070b40d1000031045103000d0003000303c40c50564000c9001409602c40c60403ca6180034641c080a100c03072a06600105001011560500040c426800c0e5540392056070700c0c1c03001c0c0303842098001e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27388135 1250 27386885 27386897
    0x1170304050a081608011a06030c0d02070b0109050105150f090d1415061e0915030313080c0118090f0902030a0614090601061e030212040302102304060c09091802090703050403 77
    0x241f0b460500000940c0c1104007030a102d40782102e100c0ca12001d07684045401c8070f04103010001000764208500c02c090150500310703580e482d4904904030300b03141d6002d580f04128010b4800101855240d850740d9401c4003043d446800b0f0901c0b1070b41c045101e912030000703d40401081000d0780000b810f910b04520b244c1d00c1c1c00f039400b004402e0302c9480810700c00b0184000384007501c05d1401c048080026501040901047c6d40d90545a800460501800d2402c0020480b1002d0501500080c0000030140d00d000d46404d68000d0040000d0500541d00440040c2c80c0c2c808001c0c0d010300610080000344034458000003000300c5d0400d0400981c0d2508001d195a9a00906c1100000f560343d600035035010104a021018002c4a80317009402c01851128044120500b900e0440141e03200c2640540068000d020306401060f1a80003185644c2d42441000404a00248024502c0f81e46044010000b401212800090020700d00204620900d01c203020408007440c4405030710030b06801d400141c1152183c041d05129a5059442c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27389385 1250 27388135 27388181
    0x120603080f090109030c0305010b0109050414060f030703020d0803010e060a0305060a050a060513060e090a03020a02120a08030a020d0605060702011b06020906180a0e01030b01170304050a08160801 86
    0x4902c2d00302254143c10000512400004918800c04000c0614000c80c000a40701011070005400b04001c0c2c0d200718012802c2003e0511044140151035070f004c50241c40c215070030700102000900704500d030740000303500100c0e031080c02040c001404e000d10f040c4c601c903c10400c10750319101c0420026040600c001001940000002180c0e5811b036004150050382d200804119280c40b04000798003e007101000d018080d80d1480104210396101707001581011080c0003503c0d43c5a501d4a0094440003810000390203003012120312286e542c401c000011038503406c03403806502c83c2041d42005000c3d600c0060a12956420300b44046101d1a2500c1242c0500d82c0c16181d07907258040807141c5040741d000048090362070390341c207005045054072031400511000c14800008035402e0130942c100303c0101140c3e0030155140c030041d0014800159490281815140100015402800000702c02d45c036520840e001103030442005400006e02070000101c200002002c141c200c029a5140d044580c05c0300c080c41c0c0c510b0702c5c0c2c0c03d4000360 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27390635 1250 27389385 27389407
    0x200d020d06050d030809060703020405030a03031a04052a031e060102120301060207030201110303040f0f0c0f0e0108061b03060607020a0f12021201050c0714160308040612060308 78
    0x106240101030002148866444000410300942030b5030603004100d0b10700810103052000d0207010790141a500b0214203250420000c25a20031510707030010140b40e500c8051000c2180d04500b245245100100148402c2c0703810440740c00e40038000c0c0408400032040300051040d030403000095038426507079264561490a400b01c20400710220140007641580070700040c906103800000001c1d40600666001040c07458035610006120060700810107000b03420a105000001c1c02d141c1c0010401a00b01c0d040510000c01c6092980500c070041d404140d4030205010006a52819a001241296a90b00696006964150320018140d82c1d010300a841500c0410005000c0d1800030003030031429002070b16400d80c50740c650086414424258010907881800041d5000c11490325a04040305654000028001c3d8105058220281d006200004069081c03108024102d60b034100704c00c0486940369000c001c401a41c03030400d410540d0003409801c0000310220360542c41301f0941d0081200b180c1d07004880700c4c42d0043d421a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27391885 1250 27390635 27390637
    0x30d0309052a0307030803010503100e0a080306060f03040501090209060105090a0314010608010e060a0e0d0503010e04060b0d2102150c0c010e03030a0f05010e060d12110a0b0901200d02 81
    0x140103884540e108141e04450703c0070442d81e805180700e6054107030340e0350403c4101454030f013642d055031207a1402c140c400c003040720010410034a410b900034103c0303480f51114000200c0e240140b42d0001c50704103001c0100410f00c0030541060407c58000c4d200864161140d500440300d070311681081c6504080e0300801080040c1c1d41481c0c4610f072910440000440342d031103500542c2585c0f80a040006642d2000060103e080345610a111006a5078802019440180040546503000502c1100406401e2500040510466400c418100c42d00100040001c403040d1400e00c17108189603d510030601c0700303202c42000da1400024003480368042001c6c0c2c0349595807600300c041c0040c1d1080d0100381281d500c0b800e002039090410000b81d801841240c8001c01d02c14000808241100c2050384034000c1c034290b00042c031030151101011342154982002411200d811030b4201954a052152072954040c400c4911003024002800e0100380501580d000034800007450a090700f00b151951840c1d21000c3c2010803624004200981c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27393135 1250 27391885 27391933
    0x503060d03140d06080703020f0a0e0708060a03080703030c110705030a060b0303070f03080a0507140d150513060801050c07110d0c0305030a050307030c030c05190302040902070809030d030905 84
    0x714040c3c50000c0004400003074a00d01d610070001944001c07424411171031309074182d4259810541c0d000c02c0356031500c11440c04942010341010244865000400e606c3c1c0c80701001c203409035070404400e0b40d45006a18006004064020700f000009450702c401005001d404206074088640c001c0003044444201c0e10707103000505105403c1c2d80d0511041200714005400c40703031060380c10b030b0003900c4289141c900300705c4030002c5d2100104200708000440194003418403090741a40d440345e51101d4005250340c1030300036110410740580c110552203c00b00d0b08030902c44140360088002c1d51000c2c00280015214044511102e00416000900000c141c180042050a00c20301c143d04650144500d050641da503915600e040d40d00040044001a40001c2000400703505030080400100e083d240400503500c2c0004003c0080c00307a08000e51001d1030190f180c0010301e109030140c50141c9001e1104640d2445a8034106000c2c1e4000d1040754000d00888601100c00e034040d2060382840364201001c3d005480040d03c11a90000b050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27394385 1250 27393135 27393167
    0x160206011a190c05060a020304021c03121a030705091003030e03150421020a02010f050a050c01050a06031406010b03010504090309091803030b060a09140303090d060209010305070503060d03 83
    0x501580c200c09a404003a482544800d4407640c443c01031a040035400d01d4402040307007a41a00401c14800107840307140340200201d6002058095085c1e0914048a030054004141c4410a050203d021403044242d102018080c0b400c50894040984d60800d100e485081110080400c8081e28420400f00f03000c0d116801161100a05a408d480c2c407441014445000a4400361040460b075148000000300140071462411010b0000b000b00c0003185d40001c1c80030049602400030480701050389031845000d101030710317803c1d1402c400030701c1545403206104d0000c2c000c6100036200301c104040c0d20070481e2030200318503050b5601280c01c40e20b168200400e02025229142c0101d007040b409020001e4215801c0c03050f5086504012003c0c6d00e50080350600400341e8003880c001c103100d06801c0021038200360b003015002040b90842c0102c0c400400020001a044d8000c0c0b081481c0c100d0500144501005580d0b4010180690240c81c03c005070740351141c0403103081c002210740c00d4001e8850190701011a00690140501c1105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27395635 1250 27394385 27394387
    0xf1718070303020601060e090105060d0e0316030507051b0607030309030c0209041104060b030606160204060305030a09030c060c03170603010f020c0703020a1d01170309061c05160206011a 82
    0x51051412980d64025001600b0800040c007400398005041185400108c2c1e410a483d410200002e901e4441c8048202280d5507900324090071400500c280d03550b031503007617017802c6070042c003801d000d807159004400483e8940169942d46a08107455800b02816a4015143c5800c0c00302e5507034154000c0c2190341c800d5083c0403200c0010401a9030303100030944590301c20000080310401240601050398130b0b42d00199070800e030620403c8165200d01060303070168561181c50040c01c1c0c07000e001080080085420240c142c0c0000299500c0d05a08580204201c911490324058000d644140c2160b241c844d0f43d10080002d0316240c0710070307000e0762092545604a0b0000700001075221441003118101e0b44000380341101e617003004008000703603e0040c40d400b0060100c94a000541c02d0309112000321600140541c0b24480512904400d10714402c009407080b21401a01b45540c4034441c0e4003071010b442204041e41d003031506003000200700190b07501d8009d45100b81c50b002440c2a03404d0a201d0481f01500c00c03268400018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27396885 1250 27395635 27395671
    0x40b1003050613120f0509040906020904020c0102030420090403121b0f0f08010302061603050403060c0201020301090501140306150d08070c0602070f030803040b060d08030906160f17 80
    0x40d0500c2030700c0c080c2140500310140c0150303074680041813140d0b05101500b4090340c84c1c0b00d450810340060445408502c2150000355800042c54003d00900500007019000307071012403100d050520541c021409503014400040d0855090304558504500e40308445070070003034240116001900401e0102c4c8610010200030580f80415403504142c010032411000020390100324810310603410420051200c1d90620704443e081d8110b1300030503018820801c00d1508010104805000c0c144180c090342c01440d0712000c1840300450811009020f5002802101c02c140d1900c4000216010f2100034500041005405804581d6414810a00412410301c030183c02c00410b000041c00075002d03e001740326061180340300c21581d42c2460002490580980c1201d0002c11200c83c0c28408a0030790010703603070302551010b4040c078240e07503130b202182260030a848002c1a4200c04030034003070001e40105d04684241401d024000304110011811200802404019004254040703400032100c2030080a0603406040814074400c004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27398135 1250 27396885 27396893
    0x5090d02030f10050c090312070602040503100504020a060c0302061f0f060503011701020405060d020c01021b0a050105060f0f120f060403080a0e030a0912030c0c06090806060301060e040b1003 84
    0x41c107501540040d540080c40359081c283c030700307101d41d503000041c0101c1141044003040100f0303900c07100c00502140303003440800e03104200320680e0102c0c3d0250a0180954180e040841e0460b0003600c0240e5089104014030000402c80ca403003548624841c1c1d405500038030700c40d11010104007001d400f560f40380c0341c0c2c00351804010a800340f02c00a24801800d050b0b1356556030358135109990b110150755861400f40f5074010007017004035903105010b6030107001d84c4401c010f0340e800088404a009105903c0307015003000c07201c83d0300c80c81c00c48003060102d0514001c4000780910707170300d00d030030402d94200d031a80755688040440040c070002e080075000394001c103990707404680601d40540210b0b07240100032182140010806002c019800c0100d016100455502000443c100003400801900301541030007050500403031000ca0400b854850401c07100f100c1e400503503075002a515074800401000320750182c0003e07441002c002c6100d5080500c03486048500314059110781d51500c0c0e440700600c0501405840b00310301c05000c0803002c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27399385 1250 27398135 27398143
    0x302040501060507030206010e04020a0e0c0412060204030201030b0306060603130507170c030d050c030304030e0319080301050f06070203030702062b140109050403020606040c0306030b0c03040209010e01080a0305090d0203 97
    0xa0542d5031200d40e00d40704a440c0091030428160021040300012805001c01600c030070294406035040915104095610307400b40031500d000d1a40201e44036201404e440c7d05000d0341d61700800070360f8003c5e44e0034800012210141a0b03180c0040e52980e400ca00c04000250149803104520341c00244070701c0a07200660355422181d0281c0500c1d14602e042600100c1c0c14101c40d18040060351405152408d02070300b4011031113099512400020006010312150131803d00850b5004c2c0480040107114200712000d02039141440c6070f05810034041d590140c0009400801c042c9081b209a40c580b541c01801945411095424031500d90010529602c1c400341c98948590351503454180066403900395040010091044030808804005c10f034040b40e03c0070710304401c2c0000b195003c10407030741c019070580d40890075190304081100284920b51015010310500c005000b4070092034001140a18001c903080c1c3c0d0641d8849800b04583c4000b84900e01291780b003c03212100185c000e50140005180c002d10101c8405641e0300400e081c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27400635 1250 27399385 27399389
    0xe03030c010908042117131520030f04090b04021c090501050109090f1b1706010f0501030c1d06040306020c100c05040f03232b05030705030103080c070302040501 71
    0x100d40c03c00301d03050200c0d03188402c0c16030049002200b90100c3c11650b0711078401c0320800c2044070315440c60000703205c4845d045410b100c00091100c0140c100004144e60030007807145501c0202c445100808071031209a403c0000190303180c101400d0202c81c9480d1034104903030000c00c4444049a0020780074003902c0020410740010b0303e81c407940c407203011410b10481d2400c01e0860340141c104401c010304d0a8a007101042c0c0703804685140381e40c401c9240c6006841c07031028000340c4605034400020078250103108001e910003c07509504803825195000d200070b844d8401581a0385510402c0c20024481c80004011104d20090580782c103000546150b10b856105c2d101e04003603911031000000709520841c1009441c804504c2440b02440c0e1910b4003900345424201400e0400125110281c80c903c3c00540e00501c004002511002e5028548203da2400b00e40002000030b40c00030b10705040f041420142080c0b5124000c10490384200c0d115503400f440e50782166100c40142d040421910f8691041900c0400141c44034491540 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27401885 1250 27400635 27400643
    0x101e0b0708070c090207110904060f052a16080d060513050712150504020c0c03010501061701080304060e06030c09181012050c090c07200405010b090d02010e03030c0109 74
    0x80e0b560058200740c10082c03d20b51004103134501c1040000042002c00c0315529000030100d80c240c40d251114285080680b9009030000174003031601042c04080d14410310100303c0c0b0342002005104101940030020010301a01d080c0030f11504203150310400207842d200050000c2183d805000a000703854001003881d91806071b01d05510590340e8401e0000301a0090340b070601d058007070102809105505010b0300d008180c00d226040c0999008030310b0940b13002080c01006800b420140081045680d1031070018003041065103440d24111000001156442e008070071101918801e88542044c940000305108003541300a000d40081e00f01030140707800c1551412122242c00e135003001c00c444a4104405030f501d00c5080c0340e00112800c01c3c1c2c200110005040807074101c1141c3d4045909111664072440420011701c24041e009203101e40b80342c0030700341c038880c030b521203103030b480c50a440421641c0e0300c60000d480240700342095151311400700000c40d001584200e60b0001040e501a050ba030804101d0001c0c3ca09551000c00121 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27403135 1250 27401885 27401887
    0x216080c03031b09031b0109030204230601082203050705030a020609010606020c090109050703020403020604060207150309020d0f03030f0216020f0102030f070f0206040f0602030c06010509101e0b0708 88
    0x114400b0070a0460b200d110f01502c10300c1c0d14214540300040d030b56000d042a00701c081000d8025100c0c107a070003805007000564000d04240280d00c1440503a0400c0b443c81158900d00024840103d02745520500f01140f0803501281400c1c025420140c404032440740c1d140080302007000c1080100b000500c140003600c101c0340307150001c0c003050030203031422400c1d00c142c8d8001d08115404103900c41c40c16951083c031141100c220b107000040e40c1d103c40303200300d010348240e0700040e4001e00c000400140c00e80d40020307520215019192004448080f090048059603420301c00070398041d0050340c182020403174881e50100340340e10a0900060303400c40f81d00300c5400d036040703485040014140d003582c14055092282e41810100302c05d102452405030244180700e41c60149101c05051280c4450010045454000c1210081c01c51000c000b90742c00e9441e00000e5030ba42c011018800eaa01856000041c030707041c000b0200380105070152020b42420b003071454480400c51504010080b40c11441c0f400110201160010101180294051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27404385 1250 27403135 27403141
    0x1a0a020f0a02060417090d030825020303070f080118050603150901140f0108060112060b06070f060b0a0b1e0706050106020c1e0105030a02090303070209010b0d060501051c0216080c0303 81
    0x319400c4505030030f590381401005441000ea6030007d8844000354142014603194a40c2c3d00b03c540c0714441220140101d81403c02240c0c081a0000055031060441341d450040d650000e40d01250740c50400e2113000c052842002681c540c48141c0d80080c0d0307010340003804071115901d46040c99420f0a2040d10101100d95484001d000c0318116040b02e40d600c01c1070044001d0465142186450f0744910500c0340c061408400e010758803c100340c0c1d400000752420010f00c00e41c0c81d003074181002c080040780d00d40c00322080d501e00f91018045040c4135540d50f00303c0700a15880b80c100403000500c401d00c03040904000c015075a040210200040d01441b9603800380020b64001c04402d11607005205402d43c1d1911100946402d00b04032016aaa11908a070b600407881100581c95101b620080307403850142d424000c4d848901e1400100d81e0703403030020140c00d0038a0620014085950f880e00195554400e101316050304100e100c11801c3c140c1502d8005000c0044003080c20203059041d40c03503642c82a003001c60b03140e00540000040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27405635 1250 27404385 27404393
    0x11010302220f1d01030b06010203041205010f0c0201090c051009090f0b0f0306130305070f050d030515040902030601050603090712200406050607022e03020405100203071a0a020f0a020604 82
    0x1084043c1c000341c0c800e9a0b141000705030110341a241440005c110200c2a400558580d03c20300030b80f4000d0a410600801c48682c6240c80b1340030b02a00101e170305110385049000d2103183d01c140207808060343c001910b0751820703040c2010300c4103034900c042100c1c2c00c0c4100821b002540d1045403203803c1c420303034640c68001041001c1400300142e00080c4d21019109901c000c0600c99181820076151030001d5060409640e201046d1400d614a8809010050024003840303e0400c2095059000244500c4940c40c5404810b44200200012952042c00194050b4030020040c440f42c02d1207001150040d05650403110b800e9a81c1d00e81003802c202092040700c0c4c0303a40200103038854a00f1895580c0d20044101e90500c120fa0406003c0351050040701313000303486007500d1301c402d0010301c94800c804900015210440c031081d008014000d00a54002d2143c64015000d000789502072a1003c000d0351070040c0c0c03000c40c03090455046800c0011701240600440704a40d801c1041519601603403009294070310507a000782a8615160030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27406885 1250 27405635 27405659
    0x901050d0b07110a0f11030d0f090b03040c08011e050c070308040f060b0306010b130b1905180405010f0504050609040b07030c0201110309030310090b030a1101030222 73
    0x404a402488a44068000039801811407503000803076250012454011210300d40c900008004064111a0f5102014040c00441d030034240342e160042e0100e42c0c5a8041070700031281e80100d1003c2200040488005005100e0802c00668001d4018002244040d49503030140c2d085400e8580d0046884a0103a0f1402c0000178600803268000b210092207810701d204c68401801560000f00003e02c410070320200401000090760200302081d601804441d2650b84400c0303d020103500400000706032401040002920502d1074003142e401480080130886440160a030a550ba0380180303802d200721034111100780a05427610b20a8900801c02149422075507490142030100b1200040e04460103410f9040030030000c184403540303081d00045503140000300c1120703050b0228010181029150201440001408906d0070000040c42c0500f44071b8108107109540c0740300b400b0480b100c42510f1034145d0010005000890380a00852034415010b040240c90310f009408004503600d140190702c0c0154203034420511502480803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27408135 1250 27406885 27406889
    0xc0108091e1e07050306150f0d061404050c010210051005060306060418020405040b0409032f01090f03030b100207030b0a0605040203040302101506051b0304030b04050109021816030b030f030a02010603020901 91
    0x44c9001003131210300c0d0100c0c81ca07000c400c0148c3d0080d15610301e01e60401c004d03548a4418211115610903403070405203040c075141c0465099042c0180305400410b1500f200b00c0c40b9141c01421400c808410b01c40c50701d003c3c04150b80000f000c3c01d600c24000d010000d1b007840700698078071030591500c0300141d42d5030030b1808000403a282c507905540541d281580880001c0d42000884d8003403410b01c4d03080c5000560b068950080501060418042c80d420030802e10b0402142c103a0300305180d48282c5080c861b5480c8030303060000b00c0030b0041c004401030740800410008a84203024460304619148008908036842e807000c5002e907030064404a00592003444181308440c400d106900031180e0030107142d0640c9140100c02001030062071621500c07c440c1482585120a0400c1140c0c021580100e003034505140cc3e041450080808040581c000d00a1141c207604803a5040c5000d0300c40d001c1401c0404030311295404c2280104400c86030b03c0d41502c1181c0c0071140c190700803c0540000c102c29400441c2d820b0561050002500040e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27409385 1250 27408135 27408151
    0x11d011a031503030c07080a1e03090603150e04080915030112020105090303130605041503020906030412030e03130311030f0a0206030a02091c050c0108091e1e07050306 74
    0x662040c180d185869007165041554151441c03480010080040d003188100204406540b041c2030340020b44400214002c2c1c0c01c14099410504c49203405664101550503080d0010009018100700f4003d95020340d114020012590203002222a215042403c556009442c05d407061000071401100903e450078011914614940348103003194076180b101c01c0075940350800281070000102e207040c202c1d1400c0041d6035000c01c100310001c14503035590708042e155030301c075000e82014a04490782a07201c080c000d000702d03001140b000d480c0f01d1550742d4a40321101c1081e200d440c8601016118140700c28030079020409848803821010801c10031501d5842c2c4150340d041483c0b6414020f4002c0302811001000210b0b0704070080d40c0681d5403075a240d48000020b8006e100718200c11368441403030010100400001c82281c1c41aa1161044882400152005458500b000c56200a41d0351100d0070741108403c503060300c0c0700414008012622004600e020580703a260140318200099407040208000c64601001803903000503c07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27410635 1250 27409385 27409409
    0xf06100e0102060c07031e091d010806010e04060207020301050a020307030c0e030a030c03021912080a05061f03020912030901030b0d080a03020313050114041b0503030315040e0303011d01 82
    0x400030001c2d49a0b01d00400d9030b80703000d101242050900d80650b05c02403100024000d0155a03050401c805409030350b19020300d0ba0f8413044002c031010141c0d08000c005068941c1000103008507843c00980e10034920008008440e4560240070380d01c0181c4090050703902038044030b540541c40340380105005046451403e66501049841c0340e00040c1c3d0340b400304040e0009905858000109903160800b6484c056060160940c1c418400d0162402e0245600d8041c0007420303990b480100301d482c1d1400003001d4620988101c0d6000c900801c459940400e008255080e0140c07506026050150301d0001031032000000384098903d4000150503111076905105a003624038003280c0700901e628a40c2c4902116005440354181415070001c04201c0b040c10802c1a4991564048020710141c44891f141c0007080d002510121501003901044a24041c010403103542980c0001d001503046640e102401040c66006912442d00680d44482c0e155003000c00348000d6010304984906091150001c040d800040c25059010700c0c015a4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27411885 1250 27410635 27410657
    0x1e031116030206030403020304050a0f0e070503091c020115030303051906030803040605070201060f08030705010509030a0c0314070b0c1902031204022202031602012007081308060f0610 81
    0xc224418500340c0b9019601113849903030700c2c58164a10311407504842d84c01502203030000340c0b99000c03035035010580b103a4403d0302501c3e0700e902038280c0f003e000a0310703580700315004100300080c2002c03058284c60720303046640700105504042075246207403c1000d403c2500000d0300e41c810000541114200200c0304403012038208027551454854011754080074100401c030300d03103800c00300708180c0c800d4200740c018204079100c007031002d5a1001c8041c1e90358000901144c0550801001078001030000c0140c51508455807a03541301c0c4807080e582110549075180c0280503005c0107104501c00701d1056185144903a80807604c1c65a113043c14903802881c18490f03036910301154802c02c00030400051140c0e81d02c0d04145c2c166048091041e0b03000b0f020008600ea14811005680b02004200005501901c03041c5804c07202d4000300900c0c8500c641c0f0000c0c1801310124860031a008100d170000113881407000b0488124030101515140b526207030540d080003000d403003410b400c41c5054107000c124079014150145c000d46d6400c1c5209039007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27413135 1250 27411885 27411913
    0x16030b040209040c0317070209090106030201050406140c0303070215010f0308041703070b04060605010311030108070e100b040b070605010e0f041101020c18010e07020d02061f031e0311 81
    0x5100203100038001e10000c0007240800150b4400703900510b0b4040901c0326483e0780c0110688254104103004d902c203425410204002000c1031180c2c034180c03501a91103900d46410080d0546402880e074644941038501080790043d01c002c00d1020314080c1c0c440c0c0d4041e041b00c403224502000000b606030070022088419181c02c00014602d6406c94003210808410012000780380c82d00c050442c01040000b07070030b45403024108020450198801000d48000341c80400203003050051162482c0024000c0e031070568400181404145c024251099002a021f800b035040e850300d0707003088446904140d0100d0030b4007402180700403c0128a02400d4090140c0000010252400c00d042c0100000003410142101c0e9194070601c8080e40309000389411160b0290120220f09031011001011081c00d110380b280740d03140800030400c2144045954010030740725074020310352901c2e01342e1004c460404000d0011501d03c0d2206000002a210303111700c000448440005015094860402500c4201c28103114420b036040100800000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27414385 1250 27413135 27413153
    0x10201050c041202040f0e1506030d03060308030a0e07080a0803040b0f0402030a03140d0207081903091a10030204061403060a0c121d07080303010311030304030308060108040609170c1603 82
    0x2501142c02040d8820516600c200500030481400c0546c010300d0f001001d204031423100c01e40600404c0d000c81c0c6145640c1c45c401ca0482c7c4980c00300030003000c3c0070408648400510303000030260b04109800e582e08241e841104924050b40c07210121800d13440403082100380640444050362200c0030024020791881c0075800a03840720300800c0001e091010a192454910b5000f00540303403c910401411591801c4908041c14107412038080031420860018000d083d0a10901440c01c20950003882c4103107a40302c060340141003210040062032099145000040503a842d4000c034401040311301c480320140ea100b841414103004000b04031512150a0035a420121075000a0b00c0007036500c02c8034005410080c5e400c08200c420189019240c0a1003003590110310010084011412039209147c2c0444e25111541416140d005a12019012482d200005000c550140444030b61251045000041909071075030381400314440300d84900411440490410f118841c04c100881150040201882d50760b803860f5929419 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27415635 1250 27414385 27414419
    0x2010c0f0503090c09070e030c060708161505040305040311030706020601060e06070c15090e1e0a0b0d06050910050f0105010e0118060509040b06090f191e05010201050c04 75
    0x1c01100000241e9494070901400b00d0106005040300303074074280010020140009284201d100740504201c5800c1486c000044464441d40484040d050299030106c40c245d48a072210141e808812200d40f0000003006813103454400c6c1e21a88445480d18158201000d240718600b00c0240030b5402944284030441cbc00090b51411118189840800908000003050316070141c210018071203456aa80880c03103a07200184101d11038110b80e0f8400901341c4d076040c001d807030700c8098400300f2560b24ada0044060040003041c00b20760201d52580040741c100b85c1203020a80c0d20004200c244c0b038595840c2d052211000060100d4440340140080502848c240003440643c12941846000e05202c800302c0b07508070326406045040e11041c3e2003413420610940e9110068050392103c007032213105e00d1510801e00755515021094462010002d0800000d1303040150500200d0204403c91070600503100400090030908040b9a881200864014100d5180b42200281c01d451000d4804c0c40031810902091000008021002c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27416885 1250 27415635 27415637
    0x1305060c0606091e010b040e07020303040f02042304060504020406090c1b111002010c02010b2b0305040b13090b01020c0904030503040305040b03151002060c0a0503041407120c0602010c0f 82
    0x90648130b602070040603840300300800185200a00000410011420250040350100200c0c0f44a95442d075204a8a0344000c580040812034640001c9015041c00e602011000a2440701c540041d503080d0340c50030200b0030885040702c007182c07070f44100300071403c00380641700c000e2405034424031003141030f910040c003031200c902e912906002c502d040020034442908aa045000806400c2e42100a100703c5c2c024041e10800d60458007560801180303000c0c906000300c40c079030100f100480c1d0341c1e11446001c140d81011076260200fa0704000d018000410910a548003c08015003102420b680441c54594180c00b5104405546411340d00080c402c1442d9407203c1000507441079040c078180741d076a62146801e440c18011600614414000841001040d2020b480030f0102e5020450340d00c000758403100c400700e0742e58504a0b0280c120b02e9041c8120481240a40003450b0014401d5440c40480500c10442d1460101c00d58080c41c41c4616400707180f001d00000c3c0b1924005000144020b00c8010b4914a01402c8070360f988401d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27418135 1250 27416885 27416899
    0x30d110a021501230a09050f01090608191506210201080a050606040308030c0708040306051e04050d030f0e030f03010509010801090b0105010c0f050d020d020708010b1c0213050406021305060c0606 86
    0x2000e45d58921480714040c0c1b0320340d1000c0000d802d041e818000d161000f4040c89429516003403010a080c80001805148035003003492420403559282d440e10046031000c0b910303c2d8078540360307403021402e0031000c400308000d20b44041408106a02d18000103108000262112592519040502646031140d004403030036a038220702d0143e035a44a42010980340e1041c004080d150f2a80440c02000b0040d03070703421460040900c031280380c0710440d0404840c0c400ca02e09a400070415441840d1a4803868000d82000e4401d02d1200b200047c02e44030002d03c40d066500a40716980c0e034407000001441585441400c1e00c1c09032081c203008101d0031029995964034240103008060502c04d0607503000041011000f21803510715408401d9480842d01108041d61390111542d0b46400750140900c0858900014483c1c540003440040c0240100c0c4c000311070095542d4451403080e0b07023044941c030001151090744e0007403030f018038800d54005988907200807003040c0640441c0c10480c4503001c10800c481a0000c009841038000300304070307286 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27419385 1250 27418135 27418199
    0xf06080405070b030112060b0102161a0702090c03060406080706020307031d030f070317070c0506030601020102071208060f040501060c020f06130305010506030610180509030d110a021501 82
    0x400c0c5000300b50b502110803a100000041000c0701c05802101081d4130a0500b4000f00c040d4100590301c80c501c1102100c00c0403501901040b6000700917a1021038400240e040a1409a00350045014074030100c0c8c5420151a0020030701c015424288a00e500a001070005481ea403418620001c0d01c902c40c41c4000340030000011000f074160f55010b200f01c800194028100c449115512540035120f0619110940380f800720210f900c4510000c0d2021110b50300d40c01500082c0e200d003000f0402c0384503003015240c0e43c1150360910184001450305150300c071500c1665200d00c040340c50040108402a65100422401942404010042a03805c8002d9070300c6140c1c11a45e900e00b007845180491828000c0707840002c4001041d40001041c01810340c84a0300620041c0c050700c04950b150082c440050132103200c1c01c2c01401c103481c180515690140c0c825900102481c06507407601d9905200401914601e80743e00f0000000050801e404940400079001c065050701801441585850415508120f0300f19601900080503045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27420635 1250 27419385 27419393
    0x30a0210050a0f0e060a06050a05030c120f0307030801080708010204231206010b07060515010c080a0203040509010605120f010e130302100c0503010312050705030702041802120d1403010f060804 85
    0x40e0014216040100460340c208040c0380e5030354400343c1e516a00d183c40c07e107005c1140d05240341c01e030050ba1409401404020402004c0c85041e1259145038121805900c03078104021b002800105002c80c021707581c4201e554103080d032860401700d4607402012981c4c4100410001c0e204a00301ca5148614130760503103000202941d010411050041003d0045809528000b18107070940ca4050074a8030300650081216644104c505040e0010b03030039540303010555003516000060742900080000321202d1055a0800d40d503000070898141007a0800340100c1c0001c40d103420410804141a0341c8109540803044065151074022124080046e00f00019102c13018070003030605008004280c0640c54089082180d1045484001c00c1c0340c0081c04201c540d0f040355440505014482e80c03c0c0c0d114a5000006186044220f5007004010400e802c140b010300c0b0780800000001da50382502240400011a010300404004024010000a400226080403000c00d0005220007180300d100c010075640c0a080c8024035890b1424 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27421885 1250 27420635 27420641
    0x302130e0604030c05030d0533030304050402161502040315090b0105011101060b040801020301060905030a11040f0b04050403020609060a0c050403021009050d030f1202030c070b06041e0914030a0210050a 89
    0x780030110107090000f03000201d5008400e03a00c4804c0c000c05101d00520f020344c0603210303403440d409c1f40c02d5266000303202c01e0105240c198000c1c01f045c440500c0c90500503ea694a01c1e500c1c4402041d4403011541c0840c0c00c0041c011b0300030744411003c0c04004108491103050b500d02c0d0030f5020600800341004042409003108050961041020f001ca0a07280c9460340c0c1c0e28200c0c14040d50003400303070300c0008a02050000d0179050009503c2c04803688103c040640405850512004003060700303440c0b103501e84130318038004e0a498a2041038000c80c0664040d0540f80b410400c03051801c14060000d68203d45005009500c881d4071509580541390f048448820b06940300c01e040310700c0c2e40f441d080075030301c00380d54046402095080102444420800d8075980c40101c4503440e031101702d0004441003000c1d1881000081e00059407400b4842c4d01c5100288002100f1a40041b40c0788103040501485a00360303510051503040c011000d070b050b90701821900c019490300e503243c0d0009480d520b50090b20340446403103001080323a90803150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27423135 1250 27421885 27421897
    0x30c020316030c0f0515030a090c0e0f0406060509090c04090501020c010612050105070905130209041b050d051302011704110d080301060e04060303090b0903030708130302130e0604030c0503 83
    0x70000000498a0b03040030203289919200303062048400c1d0700005a81d0038100d030400f1980650494850440d0340b42c00f02600644107448003210000d0300c030032002c100001c400007074501503604800c1000380d62419103802d82c2120890381051313120395000c404002c140303807000802c400c80350001c0d50041012001c614007640a03015900c5071900701c1d42810408181e10200d00c0c0000d8800f405100280701c00d85078041e003641c4200860141c640c2048000803040f80100c0d0f160018201220302a0000130002000040041011406c2402e5000075100160320501c4100300c3c041c603a0080d90003a41c4c80210031302a80003030031444402c18144180501900040c041c00220409121500c0004e81030b02e0741e00102d071401c102564401d00604020410540354645542010b11810007542e525486080d401414000c203c03d842d002440e881d989488204014400901c1d604064045120408080940c2038110310401003640d00d800c3e804200203203000c0000d200e1150005603a0b40040d05402e00214240441c207205041d0306c281 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27424385 1250 27423135 27423163
    0x70c030215030610030e07120212100c090e0f0703090812010e0708071706090a0f060807030c083c06070c050c0d02090f1012060c03050106110604030c0203 68
    0x861552482400c1d001c0118814503044407200100c54801c50164200d03801040078041c00d5003e03400a2004240d00f0b0340c102e0260b8002003046014a0114101910700104041c4465015403a201503076056604486004081c019176401c40c2100d20f401c0d100d00914041c004c01c10b204150311111644103020144084030101242e02542c280150317101c20b41c1001000c004d0750040c001890303110003e642c1d0751041004001d01c43d0040001c50640c0c1b200400c01ca8507100c042c1407101030310b5071030604400c50326541c40b403040240400b00c050003034107165040038466520344d54880301d05074014400e1291101c41e0b80785034100d0403051400454014000004004905100403035011840c070032402445152508005042d0074035110b00110741180003c042442951458410002e4000071000301142041c810030f031001e54040f00701e005105100d81da50b044495640e0300c0003c19106680d88560760214035a250042d43d001d8051824045206020010400d50f01c00006201501304900c2c50300b50030440d0f0b014040c1c240040c1302 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27425635 1250 27424385 27424399
    0x40903120b040b030a030206011e060206070f2006061908030409020708040f09020304020a08010204231c03090303020d02011e0504052a03010b0906010203040e0411040f1d0f030f070c0302 82
    0x30926010b9540d00f000e008ac4081e500c110040c0c0c04907003042d00156800ea07010ba0740030340410388070a4401d48000d1580c2c0c8095091003011450b125104401c0740003d81d8810010700104114100b403018054540900812420010700811003400984000400c450885080010046c0c0d00c4605090070a1b85011300c5d00301041143d8401c10001d0700406c540c0103540200d0003100c402e03201c1035507145c186080b0b200b81d00c6a0a5051660824000107400c140001c0320010310140201405900d07920046258a01c07801d4101c0c041600c40c081801415410006070311862000d0008200300024183c1c83d400c62070030803d030160420748900c001010080d040c41020700c030b400406441c00300740c0010118180d04882905081d4043e43c83c06581800d24541806458010f04e81038010f50710705400c1018228000d24000e0040c1c8442c1102e05500e40c0980711f038070900440004200700000c00200e4046001384091140b11a80c032560301100e41028643c102008452881d0044a18155141030910382072800140545c4080c3d84a2a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27426885 1250 27425635 27425653
    0x1306081506010e0a0e07031104030501022101081f0c181410020316020402030408040315050a050f160509010e03070b0702040506060301080a02010f0509040e0106080606040903120b040b03 82
    0x399484580500d9090f01c2d14000910500c0074045006014490320fa0034032182e00101d60403a000e54800000e0282c245107151505480342c0fa490b0a980c4031803819040b12420010501c000804607140e6800340c201800607061001100c42c0700801c200c038912450300e800341d8404a49051a0003a00ea0f41069440d46d5401540103a0f110004a0460051540340c0c0c051074441e106c20000701d01c007200b181c1c031034144042c0050660010350240002500300500440310401c04100c0072001c600079400c2c03804600d8000f400481c00e40303098040b55044e54005011079009500801c02d020307140901c0c248007120503183d460b0182e220202d62004807102c001a42e82c55406010f803510102d51684904000c22440307000b580d061205840e40c0041c803e10744000d11400310682c00c0a18018015846600c000e920030019241090a055420001034115036030f5030013801882c0e41d19070040064001c280011075103d60f04403406c10081800d501c02034542c0407002c08c4051a55502c4080304556910390344039241012001d411200703100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27428135 1250 27426885 27426913
    0x30303020901170f10170a0f05120304080915070b0609040201030b0a030303020d0b0102060403050a120b040513140105070e040504050304090905060f0115050904150306020d1a040605010e130608 85
    0x40741554442c04115917400041521011442d017400c0c0304c1d45c030b100100059113454a98140c5800000300464075401110204414581448060350280c0c0c00390700e0055507a001c0c0380c10411108030710300c850500380c18284203103404140250509a803061080e00d21480e04d503a60320048000704141e2090310344c442284070021047c198150f010300300c003180c2090104000f0f1490720059944500855004001a00411441c940248640e40400308041500c6000c5001d90458000500356281161484800c0c0d508060740c0c02413000d85040342c60704880d000c0c000c20490400c1c440080c440e41d105881ca6001d242c58401060820108204580080ca81c0010400c415002c0385002500c4001c1510290641c5002c0c03400450b182000c200907188600b5a5111507107012540000c3c0005007505c100780d03c41e403c0419a001012903c90300082c8a00c41689400050340442000709850049281100780c0c001ca02c3d00c14107000c076980100010541c46011180b1010744029202c800d005408290044102c6020b5001001c0b074203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27429385 1250 27428135 27428161
    0x5090102090306060a0b1611041a0102010b01090303050409020901020a0203010c0809160506030a11070f060606020115050a0501141303030c03120e0c040509010e0f03030114180103030302090117 85
    0x141c0c411003d851068490008004442165004480c0d850500300180315254141403500780c0250b1062880c83c04072204440060210346842c450303807100b01e8128204141960f42807141c0c030040b8000f420081d000380d00350f85000302a40111b0041c00d038056400200320515030b000704480e2003c43d40c002d00a02c4907020001c401040e441059901040382e104002ca0100025445a10241603c00145c40c041c00c56450044070405010220b442030080304041010f1008140383c01e04480380c6500404001c6910340c41d0203002421161200c188070042c01802c0418070440d0b6030040b03004100e960900e0080a44078590220003420312420350980c0c0001200302c0300000b05508041c0790040310f40242c03107090103040f4645d0b0340d02c182c032111005000c00d500942c0602d003287c9880d901c02c90304404960000a0042e07851039140b8a09040d040c5805d1b444d03840400100860034980e08001940c102c19036100d006003080b00441d03600420103000080501d0f8000c10302e0743c6a0303446990b040010a0b10421a404607042c0400b030400741e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27430635 1250 27429385 27429397
    0xa0308041206050606041d040c030f060501060f02030c0a06050907050613030201021506010203030718080a0b01140301020702150703030f020d020c0c09100302010c06020d0608030d1401060c0204020711030105090102 94
    0x110b070300302000a061490305009480441c1c41d60755030400910b0514000f48251a4020001c641c51045580041701041172803201d0f184651150600141550605070040d0003a8a9216100c0456000b0001032140c0e03c00420b14031030066004901040681b20444046d0600d10150011504150702040c85010031124102c141300301d03070003038007070b101e0500f00c00720070b42400310040300c040740581d10400109607010300c03410078411070070007044d414800c19807540c4003c0d0802007010425161a54100d0050105682c1c5a10307058007070200700d000714a400b810743e0200714403040d02c1d1000c0e20b8004e800b0407404149406500700b4a01006803840455403000004030f4180250000c141628503803003490000713031184c108228454020740d003a607198841d0512316401103074141112002210681d03001c2c004204401381d01c0c010301c8080e18404000d1600c461000b0740a00c12954040700d5061003e00e5840108681c0f900002c2ca000355070340503680940c0d140306605000061681000c1d05a400d9071030a001c1110301e01c01075000d13042c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27431885 1250 27430635 27430643
    0x40506070305041809080405060306040908030c040e090c031c0309050d120507030911040c030906020c06011a12010501080703090b090304061403090303060108040f060e0307020a150801050f0a03080412 88
    0x4c1300074415800b0b40200d6941d50030050060000300814012440d185015541c802c000800200e41c82d800b598a81056800c00d407200e200030400421709000241d92942142e030702c6149400145111040741c1e00080c0d0311684a0030f1045410060310081e010039120381c1090345060380250446600d202601750081002c0e4400310716444240c5044007040c02284280105694a904140c4e000400c031080c6e1304020040c035a0100010901da91007019a000408500180016101c0719000d083c032585810300c090b4207a40401080d03080300c10200420001c41812020443c15990203181c000e01581e40e0800907801060076440150807a100c40f800c00940c06c2001006000f60368183e514a480c2c1c0c451320340c01c0c00c910300050360f070050a031b0410710019006501c105011035005001c0c0700320304c802c8846910b420707040b5084102d0140c07960304005010410742c280010004001e0802c01d4070380848101c6828004c0034004107000e014490092000003804a5640c0c886c1240656001884180e586030f5480c810f000040b1400e004507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27433135 1250 27431885 27431909
    0x1a0717190c08060d0303020901020a020d06140c0715090f080c0106080c01030903020a1205070b01060c02010807080106170a060b04080304080f0a0510050a021c0504050c040506060703080c04050607030504 89
    0x1c1c1485554542d000c0c003409000054203400075070303040d0065000034044504502c80c00101c50b016a03900c034401071080740540000200091400324503101c0c04802890051b2015041055800080c0c169622002a00e135814000682c5c00c0305241904840058003409010400c0216600813550010340c4aa4111003e0302c0031101e20301e02000c0194142c0f003040c10080c1c00b41e00401990000b04090f60400d054604151130100c0c43d000b500c0d41c83c01d400320340170382041c0d0015007410144000c55810404458000c490b50400710042d41c501580105034428412055410800d9400403c07080541d540260010b801081c0204e61a251608a03843e80d80e0030a1080c41a917219114038019a60404289541c0302a0843c000e03199012011f04060054003010784034400669003048080340085e060210003003800c0ca10840400c041c106170506902d441c88034500f05104618150602c02203030759880c1103d04142c0d16042690b840e640f402c3e0303000d02078040e40d03100c1c40e040000020034a0825600000610540384202d50007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27434385 1250 27433135 27433151
    0x2c090907180218030304060503040c060e10030b0d02061605060f010305071a040f090f050a0c1d060910020a02090109050708040f050c0301090c05030c0d1a071719 71
    0x1540e15100c078400c690a120340101c003086444050b40040c00600b4a03e070781c001d408800c58012034910790080c4e0003c0006500441400f04000c0c441c00084021f000d1441c2641d100441711000030805607ca68681c0306050b5200c010168a40b101b10040d4a080c0d002455070761242843c01c80206043e80500046800d4001c0900007014190842403560580e80c2100003082040d080c100c201d2422010301c6604c503600e18041c880040c3e0300c04034003c0e48015083c50040030507004062036564042d6034020300b0704e41e0890300703000d56418815400350402003c22a255501c040c0880c2c403402203078041c0b1441d02420303049090051202007507074000858040040c42951100116a81e520074542140d50641d07800c3c000480460200e00420180c0f11017a01c464003a42c203444174941d240d00000d003102c02210048543c0103071207504000300c0c07034180300200140074181c814850f14000307a92440710300b100350100c404030b82c0c0840b40840e88a03446860080b50141ca0041403c1181c01c0419a01011100105c1001c1d0914181801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27435635 1250 27434385 27434401
    0xe060115080412030507050c060a0b2715180406020307020f0607091e09020a030c020d02070602060a021b15040c051005090112020c01020703050903010b0904150c2c09 73
    0x1542e20a030341060000210f078140c108210090100940013408100003440b05105220b02441464080c6e81c0c02100058403107002404e111003808080b81e039007046004180350026006c000e0306940d92004004840c0b1141c4030045000545900c2685042ea41140c10b2004220801c4802c0d401903024940356000c844445004081702da45d05c5d0812500b00f0006845100100600d28220403c4050100412440d600d0262107080c2c001c126000b19850710006038035840e03e080a0358041c411a08840083e10140101c0d6003080301c003030355580b005030850403015400a02e00c1302440039899502841c0018070140c40c1b0780e0220180546031806c040e0740035200e040089400281928011200134030407511a02c645040840510041da91101c1640c0b6901d41c20303800b04241d0305070391000e100030f01940344030f80c51f0191201e030460245421a54a050b46a000351034400c1404086282240800b500d00060303034010904100340395089450039817002d450310742191000344e13402c10065460a900003902096503203d00541d00c3c070407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27436885 1250 27435635 27435647
    0x9010e1506130b06040b070204020f0a021e060919021809060f06040203010e060603040c030203190302070b130312050409050f0a05060108010501051b0109020d06090308090106081f0f0e060115 84
    0x50f41c903034041c600704010403403218458080e000e90b50004100509202103004078002d5a03100c04c1d0800c0068000c01d150060000b008802012403980e07c50040003180350641050f603031100824610802040c0010000b4110344d5040085c03040c00e40401200c00b944e0034a14402c40ea5684241c03003104078041e106001407003905003803080c1c80c100e810920340419075880d40000d00c46180e00140080d00c1c0e0051070f40c80400942c5042103400d43c0b000a1030828024580d45040c02401c0241c15000700100b00410000200f26040251141c0d080d1307078000030140480a241641640d09100e15407103076414a08002c00c0010b450818020f041c451b02c02e49070207000c0c980d107400045031910000d02030540411030034044131001d02107203800034480540c00b000018a03580c0ca5000203030084405441144c115484080d04010964042071881c1c1003650180280029418541308a031200004081c0701c4005000c1c0c04e012810714103540250262007504941003000406c0209840d444180902a01c19400300c0403105400140c0300d03d0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27438135 1250 27436885 27436901
    0x31101080a020a0804030302090f0a080d0e060903070b0c071a0a030c02190314070204050405030310080f03040504020d111309060b0406090b0c010b030f010b010806010e011709010e150613 82
    0x15442c1804c070340d078541d002d034001d4020400241e00103ca60310352180703d460341004c481c054540100145007400c4011401001c070b003184640c240c018001800701c0c441a03200014164250f441031201c4079103400034850340a2034086203500c9920501307501030810002900c1d210061038890b10325074090007980d031303010000d076a218880da5520790046c03000c00389400420b1044140c0203002020200143c9082450340004050750003e603000d84550308008103103c0d011980084080003044404042e0440268013580907480340110b2003000d010769000070b100d035072102144d4410100c02500908064a644c60a5003400c6002001d0084c1e0408a2030808085810301103038003601c0c21103002e652407452050a025554150703070005810384405d0743d2100c5c0040b407103550602c10400e42041d2a0000906510000001400910081c2615040c40b4031000100e200380d2703010341c807030010b21641d4030b1010003620341d40800e6005180a4580b14028000c240c40c201c02c1b2072138883c200d8016003088401c2c040d00f131000e62100081791481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27439385 1250 27438135 27438137
    0xc040207080a140d02070303060e010e010308030c130302040c0206060a06050414010c061803050d050a020307051801110609031c0b0a03021c0213020c010f090309091e06031101080a020a 81
    0x240940d51500384182e0905543c02038048060341400d0504e141c26090b80c02a00084000c00d0311100c050000314201700d501401890307840c1811315654919191095103200c003034208181e200c0c000452101201d00061200000d5501500030042e00c203850f18025259502918040e10801403c4800208544a1020354007a00d00c40e003c80d001410300f210054800c41c0350200202c91b99a1113041c4200800b509182a0b45054006d8407542d64030845002c7c60030480e00000c1160010310b1051003400140b0341d00c401038442c89084005030226280c0d14000503220442c201d080600c2a105200805c00b11350b00100180c800000040030881100d0420034082c41030b030302c80c071f0138554011074100e07004c00145c5000201d4100495400221194184594000c150347e580f60035100c880d203540020700e40454038801d1140200c03412015101308010125540c2c000d04240e414420081c4898a41d4845584511144031725000000b9402c001c11615075240307444036101d071084000c0d9021545040024001d5107030b030700071542c100e045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27440635 1250 27439385 27439387
    0x40f0c03150e060402030714030f03030709031a010b0406030504080c060903090a05010207140105030417030705040501090509040308061333080607050703050a11010c020a02030c0607020a0b030604091b03050c04020708 95
    0x3c00c454401480303070314a08290b241c0318000381d0100c0c0c01c03030a00040d809140240d660443b5a030a506110309920030f00882c0040c0814203d004002002a40080c2c41c00e40f512850003240360384850038101c001e8020f00c0e5040c0700701e008400c24081c20784d400000411140d482907480b049055034440c016070b101e0b40d080c850306460840a0442412640c801d60003198824811000e100d0140d001c0320803204603810440d490030210308005400d000960700042000000c290880e241d0030903190540c2c0051241d0300250521f4011400c054620f41d440d407080e085400c030f800012103201c000d07140b42c110b80d00321401c2c01100e01240000b04070010900c127401140c01d074806c5041d0b4441c280b903c0328907030f0102e649074025502c1d9020002000c00c0b02e403054000b03005980f003040840e4010401710f14580100350416141d0401a80700c1c4004002400050702c0c0c8040d400c08580000c60301c5900e070303960000030401800311351400600400200d4050046140b450113103000352070040040700c0000402500348001c03072258400c09828848 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27441885 1250 27440635 27440639
    0x812040504020a02030408060c0901020114091009030306080a0609060c02030c0604120e0a090c02060106051312050705041407030f020708030402220204080c011d0603040803040f0c03150e0604020307 87
    0x3070076001400c4611040c41201e207007695820005080600130345085109040010301201c8540c2e09005a404007100c44000e100282032500140d42c0d14a11080b001000c00d031200428000c1c98066070140d4010424070042d110007000030b01e403d100604c80000c08035045031910843c203100a100100380c44480e02810020b0001d501c454590030701c100b01d2440c40c04100102c15200341203c0c0c4424a10070002d000c01d0070007140c403240c0c14002034145407058020900b0807a00f485042c000d00c24400024007280da40000840c012011424400c1c28200c1a80219801c5401c0c1101c44c07428281d14125140f240d501c5590030000d40384540c52650a03446061006440c0c20405e10209015240a81c50101107601444090b018501c0180f2140c050f40c22551201941d500b0065103035282c0c0d40c000140007801c10260b00c1c01b1600d5822040040d0703081c00080c001510b040300110016081203020700d5039480e440c0e049480c04486035034134505801c0040404c80d00300c441c2803d0004000c1d00030400941180182c1d4010090a9014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27443135 1250 27441885 27441889
    0x60603060105180406090509010c02120904020a1106040c030203070f050607060b030f060c030a0c09050306010306150803070809040f020304021f0e0603150a0e0c030115050913050106030608120405 86
    0x600f00400707201c03030f1038108040303030344195101c3c031528009050540c408141407900042c01c41c2110000c2c1e42c6202590400180130b0000803003030040b42d9241130112001a19901401004c840e09a0036150610280c400c5c2c01c01e02041c008540e4140c82241c3c403c07000c0b2810744c1d4072401d494640000c80e2160540040c000e0060b100080c145d500b1209001c1000380c1201c001c61454000c0510703020041d01c12100d039040020504c1034160680c01111465030142c02c04103c1985002c001c250786070750500c0040d0120383c2d541c003181c041c241035078604002004e00070100d030f07195040d038200f035803813644650041e500c114a070442c0d01008542c24002d50b4491a00182140c1d5140e4100419800310421010740c04108100d45a20f0091030387c52001560150700018484050144540e05201141c2020341100c481341040b1000c01040150982c00c0342d040d5124402d1203178100c0184002600c084c05240241940504568584d07140311525a002c54100c4040d43d03814041c4076034426516803142d54641c14245108401c00040c4814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27444385 1250 27443135 27443137
    0x702150c0f09060a110d0c020315060a03020315070810080a0201030903020705041401090c0203070c03030e0105130806060a090606090e130602210a0c080f040302102f03060603060105 80
    0x184021801c46251080e207900007071159000548520104001220980d0460000c01070801c0d034580300c2c2041d4008225603000241d890561621684403241d8150000302642c8401c2c0c50403008550150444240142e0211640340d000411140e40303000540744400102a10074501c0c010381290444006880740701240d4004401808100b80143c0c03d6100d81c01c80014107132960320035030580300c60300c428400342ca5051002d00004e54607503400c03d4003158410701003900402c0303401c148801100d0341400e2400d640443d942c016511802000e0142a244080300400a004a00400d80900c100022105410316980710140d91040311400e014001c0040d01c02101441480c0c0000302107a00503a610038100402d1403190b4410b01070b40e2000b803403a6501c2e6003200c402e41c0c9402104100681010900e8400d00c00c42d4409074004000d003000a00c40f40d4002101c1000c41c090500a1211110032000904c080c0006101c80340169008142560640a0000116072000740032051005481c065100141030030720390384440c0f00440705 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27445635 1250 27444385 27444397
    0x60f0406020d06150e0406090b06090d0507050402130602011508030f0a020a050a08090a060915051b06010e01180203010b090409150e0106050a091e0507020a0605040c030b0702150c 79
    0xb145036a058049070040e540741c80001c0b001801e595880720f611111086c44140d402d10351180d08001e040a00d41d0450780e58900030307034407143c0090703420780000103c1c1e00b002d901d00036095000d2a001480000c00112948035510200c00343e5610360003d000004400380b40a0003900b451040b1017160300207011219003201c21030300405441d07240d0310459145001c50b0b100d40307007821030747c8208070b0b14140700090700c0d9a01d0620750031100050480b07082044c100c51400d44c540801c100b078003c0c24400c22000141088000a8440440200c0b0f0340d501d00b00c07070300c83da101c10059001c2c0c1406c1c0100c54280c010124032a031032060724002c59068071050921641400100000d006c06040182c904680c03094096500017070308200c41c880d4480f0b42890000200300e9900d00014000000c00c4c40d00900b8032541003803580d0030401b0200310801540d10304454009031302d41e101c00c001c0b41001e00484c4c0080c152410041407206100801005809990146450a001d900c4114080c0d035103203594100c941c0d100c0001800569907c0380c0c0005090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27446885 1250 27445635 27445657
    0x607021b030705031002030f07080714070609060212040302010501151707021207061401120201080402091503100207050c0d031704020a0902040806090111030702191b0806040b0702060f040602 84
    0x149407a16400042e003000e104078a82d001d02c1791b010081140024a09107010341004407800c2404150501440040c10783e201130603581900c1000280f403400b00300d083e501c019469600a041191a1060000703509140724098600f90f00560a00c400400e014004180d510400000780d1202c11034141e00c0007030099510707001001e280c20750282c440d800c1d200c140b8131401041024031668000401440c56148407400403410303000021146040c118500060360000c02e0a500560100c03880c01c41a80e415107901d03082c000320b810b500c0d0580103c0c15080910f03e155005080c24900c600180c0e81d001c60540141320b884020b015000d40090090f0381c040003001d192200241c7c0160028000820090f150f99841050f6842640140401c1d0700100801808100a219404c0184000c031420742c50750070300e480c0007561803041c01e00c1200518603500090303040001d200310701f40c0c1d03210003c8901d27499130750760740702260f100e500440b0301380c409c00c01d0000015202c601c0410030900c40e0041780740c94005502d4035201c1100940046030800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27448135 1250 27446885 27446893
    0x1270609060507200601180e0106030206041205060606030c04050913020301020711120a05070603020901031b0201091403090a0603180b0f010609080c060403080f04150503180607021b03 81
    0x800458014040c4611440f01500d450200c0c0101018188403140050074000982e004180188038107030317a4281c1511103446520b8007144d00450a0780c0a4010b20311a44000c3d884100000c0005010503a0141088980d0040e800d03111140d56490910110b4403085800b00c620420403c0700b40050714260002c175421100b6418184c919070710759408242240d1040d00c0507582151000301c40c000c44d19018040360a40f100349009040d6000d0b244c1d07500ca648031094001c0c07905040d00845c0020150344294480c5071800c0303035180c000324104815038004c4c3c005c04090b0303801d0720b17510813a80d00c04030700f01c1d0700004540350f8a40240a9142c51803401008074003c0040d01d42034509115a040c008000c1408032601d6400758541d0300c10000d003940b600101500c21074540c1d122940c1c50300000502602e5036034070300540c0e08880d044183d0980d80e480c000b119425922660b0440003440031600381a0707248640c0507001e180718a82c1c0005041c1002c030030301402583e610303046400400690044120344410010f100040c203800300b01400312 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27449385 1250 27448135 27448151
    0x20d030f0c0b1e011508010e06120709020d0605030307150203040303060302040e0d020c2407020d0c18060909051914030f1c05060604090e15130201020708012706 71
    0x4038002c2a002c1e00c029075182e24102c03518207101c2500004600402050a00300715114075003d0142c50b804052056810154118000400544034480c503168500740150a0350052074660b07003440025040240e110149034a041008261420000102d0741080c1d0024910049410a0403090000c0d5000600480030181c44000c0000180c031071f40161100745031050080c0107040c502490082c40c00704804c810720300c0f5140d140303101c0c4c01103c180804504400140070810341d560040d1b0011039030001e90742400822420040000060ba42000341e82e04100819240080c000e0b90358890100d000e035103220b04080c000d0f4214492104416580040042e2054407a5000c0c5400b00811182da5003113410407080c0880100b0001445e449412280e5050152004060300810150421a000c40c005000700d00034400c40940d244400c3d940807908001c10000d12911041805181c54005000c0c0c4040c051035504901500c100c5001090f00e0806001c2c0b405c80c1a80d40061800c10064000c60082804512000382d405990326410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27450635 1250 27449385 27449393
    0x10801030803130c08060601030f0203010f0e04080c15071b12080901290a0f0f06180305070609170c1509060c070b0403051005041208060f03100606030c0309020d030f0c 74
    0xb40206607400c0078011b2443c000001600303850b1050116118284108014442c0c101100301413802e480741c140f00c40c6000c5d0341d1480c01c0d900340d2143e40c070030058920580c803180c00420b41c604019880b807030055035200c2680074040c412401000302150001c00d200b068040d0054600c1c450040140d020759818000301e0f1b070042c00c0c81100c080985105c03840d203446224680c1d9200c2c5003031020b01f034402444078503c850082c03850006041618403c0340924020070101c4010f1102c00c120701040708004e190040d040e21350565071b0380e82c040d1105023540705910302c80140c0c6000108844c03001c1243c0d4100071002e8448105c0c2640a11405069031002102e55801101404880c10182041064501525103400e001c2d90341c90450409c245441c4500c000552494100410000007030840f01d103041094015003803907481501da240003e10b0110f0380c400c2040e018882c0c14002484a07d050f045201111415101040f01242d03150302241a201813890194000101560307403070019109400558501d1080d01d42841180100e44d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27451885 1250 27450635 27450653
    0xf040302100903231c02040603060f23061e07020f04020c070b130305030d060305010e030c1203150301020a080403030b12030702090c12010305010903031109090a1a1503011a040501080103080313 85
    0x1a11218251b07000c03509100349a054414100038002102a07803803d580f801e4182101c940504400500030310008015100e1525418183e0701d0340c400354120060200e03038900f0103085641109000382d1142c0300d00c80851045013414803c4a6900c0c0000029100150608028194a030300018003513007260014040040481c00520140c080d400c003400c3c000c1039251550030a90300b03640340c140007411980c1081105900c1c0e060000395908801d0301c00c00c0480d071207035518071240c036500680c0b2a0075a010350001034205005036100c0b90b52840b03a440781c4ca0421052400750144000040402104040b41e802000144094a41881485e901c1285d1a03034040c07820707044c40c45205500c503081c0d104485603074540d0031900c10190180038101d209800406100e08003603030180041ca107040054981401566152402c8000034510311034044880780203426400c459031410000340302d540c000d00c90303c003c4002c56081c20170344d61441005c8600f180d405a4500f8400d0b421074441c3d40050f88041c0c031224000c00c0d02c010540001e0b20400c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27453135 1250 27451885 27451927
    0x60d0816030201050906070801150f020705040509300409020706020c120a02101103070c050c060f090a05040603020105070201050c070806042a030210030b04060e0f04030210090323 79
    0x9400820365040c6440c840b4580320001d4500d8048c03204480043c441c100594040300548080c0d071601c1c000d500401c0100b079040c6910341d04002d0b0032904010811680000014880f501000394607c240720f00d61138551401c0644081f9581e14003d690308001c1085124440d4001d8482580100d10061402c1d10000005250000c02c040650320854081104140e56405000031100c40c0003550081c024030042d0f00109540d032200030158024803104c170003180c00b03000040001282005024204940d1401a11000000741e00300c0b8002e80d101d1080a030000c1000e0501d401f03590304030b0f581a19001d0801c202d40e4019611074100076000d001c5132007035020004903083e040103482e018a0080f4020f82242c203055550b01c2e17800c5080c02c0414144001c601c02000140c03075260980e20043c019260000312520602c0010700980310310303400b51605044040501c010102038118032030090340b00e07400f2205400120341040c1e040e1003003c82d000d0f0100321046d41c0d214403055016011810742c071101c0b001030b10346030f641140011070306004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27454385 1250 27453135 27453137
    0x3010903030b03120301050d0201050a120c03020c0712051e0a0c0608061305090a02040218040207060f0b010c030c080a030e01050702010510080c0a09020f0f0d0203040209061503060d081603 83
    0x10307400ea02e82c142014040350380d418011280407459076050a0220b0381001500a0090400100080b800c100b14424017100c40740030800d65090015a0b400c0c4c200030301a40001001c0340a500800ca80003d0f03400c03c00c0719403401c1c694800c5c00f0f8800c400054010100c210001610030703145004d285410b0300080d803192010009441145c883c005d40381842d4051000e0450340074001d801540c60441440f6102030002901809a91f046030096581c074461041758900d201840400350b001030000c5281803c004c11034010034042d180380b440801c800361740080110303803070303e032945d8042c0100740e020540c44007140e0144000c103a10116410040795810900c0c00c00703821aa01140d2100060b59594240000040300d8400d6200502c4070000a0003a6089400010458202ca1040300c0c0550ba000074082d0f40410848280d0710b403485101d40f810344980c0501d031038001941c401c0710220b02c10b400c4440003484600c5c103084000160201000000d06564075402404104110342400351190b52050100400c0d44030f444d00704000f030700d2003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27455635 1250 27454385 27454391
    0x1e030109050c090f0f01030f1d0607021513030201021213060b01050301050315040c0b031006030e03190503100b19080604050705092b200f010206150402090301090303 73
    0x50144503004442000d002c1e44440c400400068100d91350341e2840342c0d0600750896aa8803032407501c8005800034803002126941e80307400c1c0010700340c6001c0c60009100f0301c0040300040d0f9680c5d0751154400c0b078450301103001c100840c261000210706a11450090011346c030b480381c0001850581460380350f001914040700c030001c000b55501038071010030009004d2012006000c1c2011401c550410000a8a807003402c200c2e002d0b6a0001d00004086c005200b130510014685003084650b44d040c9a0246802000e09000b81c4e030100e070500b820243d5691000007103400007032800c44541078040c0b42a000b1111b0b684080e14042c00c40b0301800d80031078007100ca00001c00b1107100285c210401103a02d164058600200182010300c0b0710b2820040090344c40c0c00108030303290070f40201c55aa0503001c000b00d030401840200480301c0781030720034500c6542c1004003906500060b440030401d080181c0d07030302400b00b2030103580001ea140d0040c1c001e280401d900001800682100140c02000941841003d00100b070846e1065102580041c3d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27456885 1250 27455635 27455639
    0x40221070f0e0114040506060315030114041b080c01020706120e071806050a05090f040c030510020304060e1c2f0a1208010b03060f0103090609060504021002071a0901051e0301 77
    0x40a03040144c02c481c054505101c54600580014a1130000a04180f0b0100c0c500d5510300c0540e40a41c050312050140041d0311542e801c180c1090268840b00740c0c82c0304142c44101c280800c80010005403040403c3d01640200009420300400322601c8451000800344280c452106c0600c5900a100d801c02130f04030102c081c50400d500c4401134080c1d83e4554080b80c00344d54100e0090225455404400d50b1140700c2c0c149041b4661518070385007155402940c0040c116018010b50454840c2c0243c0046000e60301850060144214050f803480c5c03a2040032900000002e0400c2065007118082c6d04110162035030030500d8004903111406185400d0895040e1852580107030b0a40d0f82049050003104150a52318500051250706106121201788005884a44207000f18800080b20768070a0304600c5500d60311000500c40100e56242c00006000b003038904074814014580c2c0747c100b05100051031002c4910780f1040e4500c0c2d0000b0071110707802d580030103da0f60401804001c40000c5030000110b4035080141070110568941c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27458135 1250 27456885 27456899
    0x30c0b01060e03120f090a0605070203070b04060806040b0102070503072702030712020702210a0b07030b01020c0909120712021c05120a0f06090c0206090105040221070f0e01 76
    0x108050300098140948403550200d162000607210442e0141d18819a56411060002a4440c026120050780c001005140468110383c004080e0070307000d1013901102e54480c3c8030304040c2458015401240009619540025803a2402c1d40018480c2c80c0d040c015901340310703100c0002c681000c5a07a00452014503200311260402d148105803c1c01c81d46403600118150704080c50010030705003007117401c0d9810300c0c1c01290b44025587e1350782240e414020140741e80c91216204294403a11502c405005035486800b8900080c00309001c1e01a094a000050f805014070b410140c007003003090b14000d8011403d900c40c08026101d815449802000c52500607007034420320140b400e00c004c1c0b4280403801100704010010140341c00035508079054030b1030a28058100292541d6051024000303000c0c10304120304003403c1c0b940004660700d45910081002a480c3c0c01d4600603078440150500ba1441650000c1d00025103030050031146036003814003039011541c10300b912003495880c4645204130010397c0002189003108401040a6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27459385 1250 27458135 27458153
    0x1030f02010810030c3503160c08160602010c18050d0602040503060709051005040b0d0b013b010905090403080718030308060a0501030903091404020c0102070b060901080303190b01030216030c 84
    0x2070368010903081c3c6c01d9500075103042d890740101110300c41501e06c0c04500c0740403c24010460b0020f0503401c011210b40f40e030801c808860101d1f2520480c40035510302624102414070415000d00c01c04c55125036841000c0c540350501c546803d114a0941d8520750074071011440d540c041c03201c140520107c0da038040c4c58508000400c8141c09682c44a0070a200c003c01003041f00850700c10035549660343c40240003c0303994803c80103a4a1141083d00c02e100c070603001c65900058004500c1029070f0100f0f81440e201c110308a40c005544080d458000c01e54880d134003400150000703104140c000d5002e079031807038980c540352008071050f00035a215030001c03000300c0c50307400030041d0300e040c44184580200002d107014000b24081c0d84003e000b805007070091002070210f20152031010b40b43da0301120580000d21008554460385818282481035054525078411020a0000200c040001080d40e0003010074116018404107400340040c024910721100e5030500d902031000007100003151284403c0e99000391a5002180200c0c5495000703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 27460635 1250 27459385 27459449
    0x6110d1b0501153003030f0908070303050f0112030e060705070308040906053a03020c060c010b031b03030d0b040f0207030c0203120c0c01050706090c06090807090501030f02010810030c 81
    0x14400313000b59042c0c804400480118503050300b40c00c00141010b2000300050203017a80d0b8038040c15010380002c002d41050b60652110b8440c805241003a1200c0e40c8898029041d54095140a000a84c00d030402c2100c2d403a05400405000d8840c00494811a0340d80c1c0d0744503015001580b00c14030403523541074200614100038408980311a5902928000b80d20034410811800b001034242c00180048000006d003054001c2140034074940000b8086a04e40842c10b5005000e03109041c1d20501901036640c1c10b9102c0c25131580111004440100030f541081c4205d142c45008214100180e03901903160355011020191074401048a103009039a130021030043c500502d8500f056051000300c00c100200680902010086000d5074800401d207800d581e1908107042841c0a0310f80444041c2c0342c00f0040b5000aa0f05030081c1d00750301290200d40517601c0707081d61442000105e8000b4480a4410001000354200640c0700b0003c1a6003c0d14559490355159100d40b2441844031a941000c55000e004960360121240407102e0441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 27461885 1250 27460635 27460679
    0x9030d05070b0604060303120e150a02070203011d060103081e070309061803020a05040c021e01050f0108071d0402010c0507030b07110a020d0308040203030d0903020606010906110d1b050115 83
    0x5e42ca90342d40104620002c5104030f002c01d0303640b074040301034040511010b400c01d040d14048115604043c0a200000d502c4503008034032035071800900002d4009038814205010000c8009007420342e207540c8855480d03034170001615418480e1141203004a9000801a00e00a4001ea41c0c01000718103095025151420a0b0201014132010f4481080141d461034044c0055440076107001c40c031214608010380c0f41622020b0011204140da2541c15894001540311611a100e00010303031106981e104e410b591550043c3c0504200e1a8001845080703000f0880b21040d0454410b161600301840396032941401c0650a0304201c40c200c880c0010304c80c0381980306280c1c210101d22440544003189190340020001c0b07400c5000241032042a100150a564083c81550b41c04001414184800c0019190084d100c00080300c1c0c050100e084198045510382c890300100905240500080c0300c03640f03101c50190b844020307030011810300082c4034408030001503082c00b548072081d044031000e0050604141e0480108500188189 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 27463135 1250 27461885 27461891
    0x5030403080c09130c0302040504020c010b0a0605120703090201090504020310091d0c0d0c120c06080f0f060904020307090204061d09060d03180e01030f0309170d1409030d05070b0604 80
    0x24442da41c52a41c00154203204c0040020301c0050b040040d000380c084ca0b444240c0c880e102140898502030103400010003404100d07500100c49840706000c1d1000d0041b20482c41d40c000803800051603040c0203a1060403614014100a110700d80e44500103801c0c0d900c220b84000c20305280510401c00d031103107030080f0301036072005180c80e50444a4070100d80741c2e0b50800f840018407034a0741c00490428081060b804202408280308044602ea03030354244206a51017a102c0c410000d08100300152440001e0a15280510200e45400c00030b6200c441c06c010388200050304c240d034140900c12000039191090b03c0100700800031a00e034400031001c0c15007143c94003800c0018a5016107031810410500759039040039503000d1549820a01c2c246040c68603502e20704106500f0a031007468594001100b80f0090064030144548240d0700ca041c12900c0340d00721100e0b114010040f01150340211010249280900c03550030305000581a01424001c1510000b07180a0b00c4028400204e2400503081d4240039500c001103522010584040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 27464385 1250 27463135 27463147
    0x907020705060d0f020c030a0512060405040209010303030c03110301090b18090d05031306020f030f130c0b0c0c28090203090a06021803010527060105030309040e07080a0305030403080c 81
    0x4030309180f08441400c10700300d54a000454403405079606666071a0303a40000c40b0b445207040c07140a401070748002c4911603000d4a480000d034031498076025540c03065501600c1c0640503480e640d42640607021003030060092544825030700e0803540010000c0c500030004114080b514054460034044020403d580301d10b64481201e041007401d4600161182501e01e03036240a03a500d54403100c14101c42010001c00900b840d000140d60908041c2460180d8040d81c0f8450f83d00b1540d03220600410740010f03001c0001450880030348010041c0751401300c041c1000e10b034a0410788005900400005c1d0041c01c007100c1034140002445502000c6c2680d01803010050111000708610790305141910315514821703402e0003080c0c00c0d00003031621160004a001552a84005002407045003408e19880b05103000c2d0440140344825482c01404c00142c00044103412181c1c050040d500d0702004406020251001d4031b2003004507c500c03000080e03000342c200485800b2900958071107481c3e00f401c5c0340c02800e00c80003900764040d40c8014000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 27465635 1250 27464385 27464389
    0x60906010e070c0501021804050a02070f0b060414130b07051305060a031d0609010b03070302010504090902030a0c0605090901060c080d05040516060201060306140708150d02040507020307020907020705 88
    0x54103065039a60080a071081e6596101103078031807040b0714003d1965001003003a03c4000040c00c10004080000c440500c0607980e084040002c134064800d0141c011080040c08802062014907201c2e000b42014101050842500c0e500b1a1038000c00d4035808a1b01165030515402e100b000c0b2074498201c2c2e510b01d0315030b203840c04204080f0140e403403a000d241c1c401d407800203c0b224000d00a0b840001d600d06890440110100d400d20b1454455004458000d120350034048030810b185008621101030300c0d4140c584904150414660000400c00e191080b41c240c0311302403208000c43e01c40b2501e50014840740c0e4400795074200c001c051069002041e4040c809100712890301c040005c08070800e80b9038944070346000185035600c5003041c0d0318140c00640314041e40c449030745000c5041981900200e007a24000c41c1c0500051116008001c4800350072100b01e400a800b100208904014140c00840c2c0b200c0000c01024090b00f01d0b40000c4d003200c02c10b940c01d101680c00055480c08509200c41c40e0740c0e2002c5280054154a031030640 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 27466885 1250 27465635 27465643
    0x30705060903060c160218070e010f02100f0204030b1611030307050711010e1002031b160302211605100c02060a050a110604050a030801081c1202090d05011505030609 73
    0x5a4450b000c02242105176034a0388104075410540040400985e183c0c07040e00c0030071044041d110100003484100c251012075002d0b0007400550009640100440c0810304002030003001d640d5a044941a002c10000021501418807140180c01000d801c5840000022000c1c1c0700044900294070a03401c1030080041c496000f005545081d81c01802000c80910428012514604105545c075845021031380254413a580c000040d04c10940d548a1840d000b80700e20740350310368403402005582e41c801849141440142000c15540041004100060384c0c034005411200c4d00f02a03600c02d1204031044800e604000070300c0c02c2c1d0034641e00200141440d40c41000c103500424100e1095411500500c40b002421007040303482803820701340d2201c0500c181d401504003481e1103521030340c2c402e5050700001d852500102d61608007144030b00e000300903003002d400700c5400c0120641d061201050000318580d401c4c0406421a11450325202800f8864800001c4030280c0d0031401340c25410039001a400f07640850104001070300005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 27468135 1250 27466885 27466891
    0x1814030a23040902030a0b10030605040c1b1101020304090203010608040201170411010e060f0705030c011409030d0c030204080a051f0606080105090a09050d0201090308130308041106040504020703090503070506090306 95
    0x21000d40c0d06d80d01d901c00a80a801001e11050b0009010400c0750061a8507a121001307640048809002d0304031030341c03c103c3d0100104401160090f00b0651000e0010380c0c40049200045010f0055a0806079581d003068200d801c264000c1005c0380c1c2030310402c821903900041100c2c40e52282802c2407080d01f041e403140118205580300190500c11050000c0314160380d404140c2d0048003400c07070151307501d103507a2a01039101d03005001ca0b00b1481d82846140d4440450509450b4803440b80c0000031401e0003000c0d4400c030068812540207805241d42004040344c00c1c901801042407040c00792004000315030b0500c5008086034188540c8410342c5181a0051000a0b4015001411101c1c121007400481e22410400c200415800394000d1040c4503c0f110152415010b40104a40901a440d0620b40e03540d490f656032000c004000c4001d00140710f9000080010b0340340003511414030b02c00f800103401c150f11000400e003242d00107042503000c0758035802d041005140c01c2212101803c800d852190819060401183d0b80c0d003009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 27469385 1250 27468135 27468149
    0xb0a080a0c0504120606180912030f0f060e04030807030203010f050f040209032d0304050108180c0907020109050601090606050405100e06041401030c02060907091814030a2304 77
    0x781c503821685a2041098034003501e81110b00024506980c9000710050159201c2e551000580b011141c0a511307044c484d911000b9040500703604074461210b8120010440389641c08030241c0d130ba00f1854540b020310f01c03d00020b0b1504403003403c101e003800d04000d4040030004061004060041005000244244126400f22081a60b516514147c0900050080d00406241c250107200d83d0514a0181e100154551610322540c002c10754807010b90700d59241c0340d100d14010103002c02c140c0004590b001c51141b00c00404e00501c42e0996500303040d8000004c0c0c284005446060050f07441c0c00000c0d05000080c0b1245006014420042007198900f0700054814000d61041c01c0c8900c089005950109008000300b146485009200c00d5483c1d40300c06c2c541018040d4680c41324002440d00e01c447c42040d0000906170700980c0700340c008000c9a40350184c050090300c001c51000102841006803980021001a42c68411901c0e01d0051900c0d001038110090541d10134070342d0365040c2c540e600310320315510020304201c0b015078000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 27470635 1250 27469385 27469391
    0x3020a050d0602040b03070f0908010b15070809030a05030901020d020a05061303050f0d15120c03080c071a04031703010b1903020903030a020601080c0402130e06040905030a02070303090b0a080a 85
    0x1250501000a024685c0541c1e0161800810026195403001c400c0f80100c03002c3d00c1d40001640c0f1502200d00301c410352580c003a0030200000700442004100c40c0500641c511070341d1003030301e0322449001090424480b041d040740ca41d840400d0140d69580c05100511202c000c0d403000b480d0941050300d4143c2d540c60050040f01c441005030b00000c2c01d02d4032a208440c2800c0800394038030360310440711451304000c2c20011016600c90213401802700c3c203402011006005560485401d000e240d0031341e191034030b03241c0c0180e245021a104d81440003464440d826140c001c00c2d04242151621140396040200035041300301c40c140403042041005020700b000034001d996a0000c082101c1c80c001502010a5000f40304400140da810312010684007440c917400240d10b81a1203054080d18101046001071000764042c00c2e03c204a078003a014000e00903c42058600c40e8048001440440c0c050101e803038282c00e552000c001000140c000c10022b00a0640040380d0030000d086110709a40f0380551100d00610641002c0c00c3d04240b103032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 27471885 1250 27470635 27470659
    0x170a09030e060a090e07080604050a06060c0201270b0c0607020c1e030106030b01030609050d02070f1404020f070f0506070503130b0702070519081e0c21030a03090308060a03020a05 79
    0x40704081385009407140d090445041d0611000240289401300c942d244950b0a14000401403180c3c0c0c080d080403144903807128406080d003503005584003045106020340b0f400400b400010041c030403100304402020383c02c40140d618010725080d1030521400900c01d200f03560286103058801d0315980d404101d0400030500a110070407446000034090440e507400070745082d41600c008028045958005044035104404840d00180582010fa844072000e103d104404140807104118602d10103e01b5400789500500051428140d01044000c60700140c0e81650001400da103071000700302d000c00100ea085030071418503905510382440741d03001243c05010000d000710303030b40d002082c2c0c006e0082100c0340150200400302c21000c0e1142d104c15507881030b00e100300e521038424444507101400714464404840340740314021f010380461034000c0c4855140a01c098440100b517184100240754070500141c805502c5c159404a810109130900500590014004030320890784e045080006984405070f4070b0031580155820301e4048 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 27473135 1250 27471885 27471887
    0x1202190c060e0604060e0f070b041214030703020109030f02060f04150f050a0c0f08060d12050d0e01050601090608060a03020907050702031b01140f0406051305030d170a09030e060a 79
    0x40202e500350415803185070144420007420360030000e00030f13400d18101c9041c514041034081d518140c0f4429807410505c200028044440c50310804480940600c00c5002e0280c00c1400892071644962801d80040c0d40d1210310f64105139101b140222a00c01c2c82c0700508880c10602105c10000ca800b13000200580040b28201c0d400c01100d81000c0c8905803010010002860041026400341c00255190b100084070380c1d01000146d80542c0260b0b005203400381c220000202c1c04c0d65006003105000e80110107210013880542407030441406200b182e912840004149820001c0c00548011030307540000d000d0040a40c00c01403d92505030030303801281d0b0101d07000103068a070220305a03800e209110010b034041c020f5014a111a04082040c501c02c1f200030b85e6002c14859107a1010380150007141c1c9a4880542d04001c2006003901c00d0b80508900704036a44010441e07035603540017034500b6043c2c024100101c0d241d04200692401303444a015440b010110301444240b1840d0380041403aa00d580c1e600e0310824020400b00045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 27474385 1250 27473135 27473141
    0x6080c07020f10030506040506010c1e1703040303020705011805100510050406141203191d0d060c030b030d05042d060203030405100b0901050918060c0405011202190c06 74
    0xb50703006440050342c00015400100508800c0b280c0c2c0303001b03070305003c0031880c43e502c40c003801c1c0790782c60300f002080c903811984088002c2c422200e05003c0d100301c035151808134000c00c4160000c40c0a40e11135200140d581071503151980c01d40d0700041d5045c1010140584c1c14001c6100440c0305000030603588000103490b900c1d510003000400503030b080503030050321f0801e01140368860000c0c2d0000c4103104640741d00da27213651005900d5480c03050003450300c42c0c062030b501000401c2d4007445044840001044024092450070008038120301b000d400305a8400d522004c10380782981d0984101c82203c3c400f9070192150240d10440030b40710b403066100b48982d11403000742c074401120300480300020303605542d01a03050903540c40d14020341c1c94005840646043c0500c0218503a8103410344070300780706408041e00c01d540680c03a240030055603280091800d80c81d942c01500e03103d071020052040c603200f202c0d0344a556440310308020006050035592045d10040a20400441c0c011070119601050132134650f282020800302c084c038102001d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 27475635 1250 27474385 27474409
    0x30503190f0e0a1403041a160b0f040b10050915031006090204030b100e0408030a02070501050108010c0f0201060b03010509040512030702060109110901090605030a02070c08030a02070f06080c0702 86
    0x41c052030080440b800d0030000c00d81c82d10b818014004401c00708146000c5a840344264407503241ca0b1040703d044141100007140c098441294030701c6020284800a803a031941c18002103542109134400007042104010800d02025046004070164400b03040c10300e008a0456100078103800d0a10081a1034405c03a5501044801300a6482e8042400b000c2d0784c0752001000794025000465084488800058204c20128031010480c6c07400220f108543d290764507824030540c4003519070000d15808020003404118240a424024a0b0203030000840000c0d40d04002c0185280040720b130116418800100301c01101c3d54244c1e815600100d80891040e12b407171400e03514111176028100410003020040120701d039008110380b812510342c030b00280f00541d0034402c07030101c6219500286020a80c568403c0c8910b9109401450740040c24003001490407503603840d414404040d550101442c0c0d07000049004001c2d032b050101e4002400045c541c2c800f26414194007510a0500034210f440214002c2214010740d43d44480c0184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 27476885 1250 27475635 27475661
    0x402042007052d0c09130f050d0f02030a020303010e0c070f0b010608060402190c03050c0304030807050f03030108190302010f05010b0703020c010f0c020603060f040507080f060d03050319 82
    0xc0d0394103a500d0140e48030000e8040f5403000ca004400e500380300c0001a80340d05841407660700680703c084110803c0040300a400381c80001c000c055203802c10001550601c039000510701410050408520622005295650392030348101150010712039112050b0300041a40e05444820101040c9540c9000c40c0606600407090042c1ca414401d01e2a9401d00848035009416259940c2d0b0711503c070369603402400309030711444003100c043c490f00b5a10000d01511034180345917003911a2901c0d03490100e120800601d90340064005030741920f00042d4042c20803d040043e4881d0303001d1040950b0440d80740900c0140c50300c24664290a10102c2c00c2488400c0607c02e6000c3c49942da9034103001c0090f0358680396080d0345030700240c00807405880350340101c21a56000b045800c44010135030382c0c1c5421700005582170150036000500704a4000b0361a42040d946d650f518002c281c4940101d0f030f0b070344800e440c01c44070541c0b6840000c0c01082c041c8078000071b82e001013a0721108a0307920100100f151915241d074221080e0007444a440d00c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 27478135 1250 27476885 27476887
    0x418090602071725030f0e1201060b0c010f0b0d080a0e03030415020c04050408040504020a030207050319120b0607020f03030c070305030301051216151206061715010804020420 77
    0x108142209602602c0c401c40c0c401d040b06130004000d40d440045144041c4050301080c4089615130b9401d204031180f50000f0800740109014840d01c00c0301c24250ba140d6041a02441c2e03001c264001c03400424442e00e0540c3d001e03c0000d0024560f0ac0011401001c0604800b030b00c3d00500003481007000e0300503000141d0004002d01261703901c40c1d44043d0040c22907440121761005001e220760b11001880c10f8002c0e0382c0699000141701c0c2c41c0038500000c000082d8046500e0b07009040e028848140803034004c1c0064a605007480c90202102c03014400014649081c14000b284494507041d49092541c41d5030041e26211a81902e09aa44800c03050001c1d195002e09141c0840520030b041003c42000404009941200c2c1c0550b03890409884107001c8d0342d01c420400341080a04400c03004104806128030391881c01c40d14803070618201200000c100315094070019080f02d40482c02e503290440c404031103524081d41c410745041040c0160105540002c109500142c000b03031082e030b124541c26644c1c40704540342402d101c0c18541d020f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 27479385 1250 27478135 27478163
    0x20c12090315090f01110405330d090204141905180a050304090b0d0b04030518090a0e010b0102150f0406062619020303090909070b0403050a110d0203030f0309070b0d140105010302041809060207 85
    0xac2d009044d9560049000320704020b1540e8202502c020f0710f50140c2c903000d142d41079101028001100030000140607090000e62203c000c0e101c188103200c041c87c4039000e8406980c1d164180042036054966203a1080d000f03000e5803810401095503844210b405c02e61620b00107903909426982c00c05082c0c0038000c0107500a600c40140482d5554642c00050300500b407000900400881c0001a61200302c00e80e00300d003440b09410001500080c40b0040641d00c20721036030002541070f4666807521103921544c4031045030f2001031010342e00c92000811020784074500e1041c41049281056011035140d0080000c513501a00622010510305042888002d01a000d01400d29031282d40e80e0610640c0e03809824402d40e08200352110645583c100b040403002140c1e001783c000d520300103041d041075209900c02400d012490047c1800803403650300560007003280f00418000803071503010781d804021580700180e0009051620420040110300d1040790a0f4800c1c3c0d80742a40085c048070070307040c0003001c0d03c13514030010f068401035098 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 27480635 1250 27479385 27479407
    0x6021810020a0c06030b0607110d08070b100b03010f1203020111030705070c0503061003080a0e1903030f02060601020d050904110304030c0506010603020c12090315090f0111040533 79
    0x80c0b0004601844040341015551201901250b844030000798002c64104045030100d610b5a880f080c1d140d10103800b01c0702c6600f00c0e4460a50640001a08984d0303001c0394410721540000c65044400503107402a100c0707155503d440461081c0c0385051140f070112103585011030040c14000e60042800520a84150b952480e0180008105601802c02101e110380404400f1856060001d1a90312896071010092009401e42d04c400c41170740c01c198286420400581001090754941d41c41d0a00c00c0c44441984115442c2903141c0540804080c40d54502154410b41c00c02c462030780c1c00143c00401e5001414810744c0c442c00a40414081e000294403809400390000c18403081590101058001c0c600603400d4070407a980b10790088040e80728000103015a90300103402d028007100c0600003014190001401c86402000210098040050840302c184040d0402c80c100e91028100303000d590380d0b164011882c2e510701410180090141d089444420010307280b0050b801181e00c0f001410404007c40e01e140c0702e611000c040c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 27481885 1250 27480635 27480643
    0x2a0305011a0906181201090c17010c0c0305030a06030c17010e070e040219030b15030c03160902030709080604050a0201030c030207021e060d090b0f060d08070602181002 74
    0x4211072150250144030032103480640199201810000d010f186030034075124103144040c40700300d0301c03076407188560f64845d901d44000d05c58078403802d1085550f140c6540c41c00171408048044090030754040d90414000b00c9800341d10002038103440d981403c0003038581d298180c5c0c000042c44203820083c003035170b200c10010502120f00f200c0900004a000d0091219010300c1100304d4807408144140c034211079000300407500600c4c0031080344001c00071171001950308039901d032509401d039501500e80d103125242d6030205084e02c3c2418010702050440540040c400d01030555903442c1c140c4a50711417004413aa0220102e0407032482840c03540010300c0400103c1d9190305040c1080342e118804001c08038040380c0351401500f0924003070b00a45a0203600102652102c804025416440d01c0401039000c1d800b0508121007001407c051003000310440c021291500c0c0f5117041d0070790091505028203d6071140603183c200600146020f021200015400540580c541001c108149201750603c02d12503400703102c0081320305104d68002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 27483135 1250 27481885 27481889
    0x2070317090706090603020a03090c03110f09070e010c0c031b0807090c0807180306051503010b040e190f080a03050906130203071707030f0b070801090b06030403032a030501 76
    0x3080c0d100305480c0c0000041d03848500340304910104000600401080303000741e024251441d128103012808900070f80e0340b040032035030071340084a07280c207074028500440c1801e400c004681441900c224446007081d032030107044901c0c030104060400800700c10300400c11403c1ca8025005650103982d840707066a42049050054105002c0c379101d600c41c03048001042c40300c41c01400120315460721540c1841c0c0700c1000854444c2d410008a0150703020810700000000d41900c80c00e4410114075140d035101010384020182901e80c7c11254030700c44d40c11301c2d0b501c8100d6203001c240d244851291600611a8181034a040e01c0d4510b106500a841c1007400300e95400015010b40200f8850741085c429207445603101051101e800007141d5020f0b4241e0300c0f01c1030a104012070400c81400803a01c645c112000c0940d240d03191414801c80d201c084451140c1c0c602070109094004d00a140585014582030206080242c00302d101800300078005004c0580310031a410401014a0540c0407012014104000c440c54201000d4041c0c1428 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 27484385 1250 27483135 27483167
    0x40b010e0a06050a0b0a020a0b09030307020c030f07060e0d06110715140606030702030d05040f06141311040603080d0e0d050f07080d020405060a03090201020607030e0a060504030210020703 83
    0x14000188807048074880c400c2511070040c448500b140c14910802180e400540240c0c003503100790321400e00491600e880c03403445144139030010740c1c0e43c0c074210798028104a800c002c102c0c0207601440d0f9107014075101241d02d2084d03a0740c40c60300d20780300c11707041c0e0001e98560b10962002d04901d203040302101c182419040100302103406032140410002002194400729007011000701c010840f8000440c5035450a05e00558015040344112410320740c0b605000c0d170448805440403662444c0b110440317810408140102c00703601070846841200b030301c0c00264149555000b4a0300074402c0c20401e180308a140e80395480b40000d550415001078440e524401d007800141804202d0411904c0f6414102c0c80c90780c411001c44400713001442010342001080d40c2c1d00b00f026000142c002d0301160302404041403a0f21a6005804029016a00402c03c41d40034000a41000c0000e030030201014182200462000d10000c2c11400855020400041e00e0b40e4904049051802840e10800c3c6580001240800c1c1980310b8044034040c2e0078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 27485635 1250 27484385 27484409
    0xf061204050327010203090d0303150e0f0c030c0412060204090609020c06090f0c01050304020a03020d03020a0c0503010507090b0306010311030a0e07120302061f09020f0a0305060a030510090614040b01 88
    0x41090f00d00c003010301209449005a01c208110103441c00c1001c1d02840643c42800c011904107507641400d031044000e5000044400040740c1086607031000003608641000f50f5140c145e20f142080c40c1000e030280320310b0160004600c03510400d01c040200f6076040300d000f801a41405c01016882d0400c600181d4403650350401d00e44150340100d401110081400c104805c190f2006101c0130241800540d640e4000402c1a40c1c0003000e8030000000da122040072401441c402d501624501005260100140101d50071880c0a030303151604001e6020381007134070307401a919405980c0d5241d070b42e84801203001d040e420445c403600420210920030240429008481c40c1c00700c82c02503400c103a0f100c1614030500758222601400507408140400d000068501a00102c025440764803240b25440704004410381e03001505c1104600f60004a0420b0b5540c5840b0342030b003000d001c60724440100d18503101c1a50364568007000c8402e582c5d540b03106d02d0811900342d01003808000c3c04009101c0600e402e051291030100c0901c0782294440d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 27486885 1250 27485635 27485677
    0x1060f030506100e04062102091005030709090501180809010e09060a05100c05161703130b0a090915090506180c0304081606091b0b0301050f0612040503 67
    0x8040d0069611800002d003d12803800c07040c480c21100d5610040a20360050380d18040404d20160014410003030280348a07130459100d510b40b040c072000e210000c00c084404142000b084c003031545c020070f18404903911b101d8085010032450034203d004002000044010240c0c148000041043c0680901f0840900b62214441300e507203001400300b010001c40d101d640c0915010003d1140786010040c804000320075180c1100400781e1741c5e564500d4a5180c0d07883d0300240300381076001c00000100201e84203105a50030b001c0c5080c07a423041d014072072107103840c05078004154020400c500719510848001005000d011400d10074001c14000404040038180240c900d158240f0000030b034a4240281c1400c500402080c1015030b55031190b841d8001600040c100301d80105c1d04110001201840182030542c59005141c001801013113464228090001d1103d00d15038a24a00f40410000c0300c400140d0741141c80070f440250003941480001402c52103500c2d802d142d03400e52003080c071040c010000080c083c014441c00540321815 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 27488135 1250 27486885 27486887
    0x30201050a0b031903020c09010902030f062d030c0612180d170406020702040203040501021209060c04030212030409092001020c060a03020a030e03031911030601020c010c03050c01060b0301060f 85
    0x58100041e00b501075028240c00d1300711880207106071160f18000c0c816a40303501e2281000404968081c1c1c00328140302d80101c103000c41c0345e41c020743c284c1e0044000c54190070580000044600640121807020342c500131000c104c0c4c0482e84013484803481c558002801d81e07684e20920900745c45854000c1d2607aa0501c160f840e2054038442d000201d103032203c42c03151592040921384410982c0d42e084002c20803560160280315103c01600c5600245000c0e40c0304030300140c1c40f1200340d4034000080000601030949540301e202801030001c1b803034003204e050302c2e01940d80c0303031001004a045520314440c83d4231404581d880c156883c41402036044003a0f01c0c40168004460880450400490303541d00c0101071194860307820040b6a800754081c0d03001300002ea60600300400d014401415441c119001210640e0760010740921900700040544101c0707001c00148241300b4114100f10300000c0d95036600d10041410301c60595481014113004105a0721a8040800280502c40c3c50728600c01607030b003003031040c42c2c0031030010707400d9074142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 27489385 1250 27488135 27488141
    0x3161b0302030403082b020703080601090303120b0f03060403032703090902090d0c241701062a1a010e04050c0f0409050102070b01050114030103050607080c090904030c030201050a 79
    0x265806030300850400c3e05540743e4420503402070300f00b24951041902411444407a900b00035150a14503080140c8440e950b05002d00020701c0101903038100064035005100198002d14448400c070245c400008640b2418000304a4001e203408403154940b140d00208010142e040d00034030003958542000030714041c000c17112080c004141080090100321081c60a02c12505280e000d41307200903004080002c80c0020392220040401c00e5009656070083e88122485000c0b281401c0400d42a03c40c0780c80b154a0821f9800d030b0200c060103015602c00c1001d02c80040c1400c440c10030f00510310030161034120030136480610b8200340d8a0300022954550003c11400000c030301182072000c501c500e801c10090143ea1104604110001206c0c041481d40140d456a40c940814400d20182164500c03030390408401d075040600241c034035401d04402640c5504200010b000081d00483e403203401010500308013406803500754802c0c0d03190090711001500000100100018141d11030017a250003402030b00201300645a01c1c91440507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 27490635 1250 27489385 27489437
    0x501050301140903030415090803040b0f090a0201050702060901050405060408060609010501050a0c02010c03020f07171207080703080408090409030c02090901020c0c0d0c1a0408011b08061c02060316 87
    0x1900b0500024020510070b141f504003a500c804000105407006960740c61490304165400c2c0d4880130f100c001c0003080070301c0321070765500120700342c0003800000c0e003a50000380644500b08001340035400100300328410740d000d181900c0190200070422a21b95880e441520341d100412200f180c40307854140e000043c01c0d40038508603102080e10707680d4000315240d640c0064500000300f81e022011403184801003050030398148903000c080c0042e405880b804401d614901490566080f070342002c0d000d002c2000b84001103d2104640300707240d050420100696a40c24420840e001d40707003003150018105406103040543c807408105600d4403c80311204991140300106e800c07030080307031604000d076444100014902d2070300316010fa0702d07544550148448580c4402c540d0b543c01190609411000f14081390034841c5d40d200b802843c510180005251101105400c0018103c07400a81440e0080000b00e2504000041000759020b549401900a90f034030701703096044580c0c2c00c064101c0c910029148510a0307010403413007034540c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 27491885 1250 27490635 27490651
    0x605090609060d0c03060e0304060806090708190f020708040e10030213180507080106080f0a0c090b0103090b0c1e0301030b0601031e0e0703030f0806150903120706050105030114 78
    0x465501e0b801031004000c00c1c0402070b19404000500000081e69a0103883c0c0280302210146da1a145040f002524022019181c2071090081904012401d5480640a98800c103513522840c52201052440001003011203003900d482800051030b60144484d00c4001c0044480016840c2c540d50384504400040401030300000f980045035108440c000101c0e2b4001d05012403840d284001c0007015551a2440c0c02d416174049105070751550700400500c1c009002e27580c40c00300b100f03000d402004115950039032040868002c900082d99a1005212264072a0b488444250380c0440d82d011700d401d0880004070325810510000b140d0b03c200009aa5603240c082050724101d952012465501c2e480744001903000e0329245600e456003a80704280c0418000d018012001100308040152540c5411130a00410351101c680c44078003400004418000c05441b019520004240740452154503600340c900040d00700344031903172078061207900894540c0c240321140d40254101c4100720002c10849000c03481c94940400221131010b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 27493135 1250 27491885 27491899
    0x703120e0709050604150905060108010b0a05030403200f06010f05030d02280f110f1807080a0e100209040c02060403020d050c0a0803010902090a0e09120f0c0d020307030306050906 79
    0x102c0072680c2e40025401440080021560806c4007503034004944240d88001821920b810500c0443e58100100302d01501c6078080700c070300d0040c851038040c000c0d201c003600050400416840f240450b45000c4075a6034019101c005490400214030501c90b82c0c0d580a0148010028681c2d200155501e40050b104c0c0000d075103600036003540c8141d40190045049200d40c1209a916034022107000220131448005145100b032410098900d1900d05202c9061000d044007401900c0880081d000010251041039000c2c00c1031501c00b0440c0d9501e01c400300540340203d25182d2500c102503243c00b0b110311540150034000e0060b03a0403c607049048000304d94450b03090703401402581000445a00340c901c18801484003812030001c9540340001c0e0364440c452644240c1c0f0548003560b003c14221214602030541c08028003c03c0507046d514140400c0c1582c0310780c00c001c1000701045000903500c00c1050602d040e40c00320456001a41c0624000c0755000c5d480f580040012800280f5000f0045018680402d0150048101038a29 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 27494385 1250 27493135 27493139
    0x50112020c0f070608010603180b040602210717090102030c0f1e040b0a0e090103021302091c0f05120f0901030b06090d06060f08010203150609010903170703120e07 72
    0x5400030340c84044100200e0003090018000c603141040f0883c000e080c5a95514040d6141c910010125510860a1a10200013640000c0401c1402088a40294000200603907407821b0000600310318800790106240c00c01c0542c00c100d81542c01010000b02214030400004699503401c00d2036080703110480e485030512109002d2984a030245402030490708041100c000c112803001c90000d041a00a03520900c0030303040026200c5400b941c8841d0381442544282c60400c0a0750550b400160300e0401d402484520585c0071603240403982d1030304101c090240400042c02031802450510f4200d48104020075619449061058012002d0117030895000d604052a000c1c1022000c00044000e00060840581d00030414001c20341c6076039510003c1d139802c038400c0200240386850a461000b100c002540901050792050041113810010804084035900c800c46543d9503c04220300180e40140c0190800b406000c0e0b0802041c80c15070003c0010701e0a42d000382c9580c280303083c00b046102d050f601c8841d18412507400540341 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 27495635 1250 27494385 27494417
    0x309070902250c080f0304150309051f290f03060403080c070c08030313060e0703020306060d02030102210405070e0105030d11010f1107020a050f0a120602040e04030e03070e010501 79
    0x30b11224980b041c503610484540e1828801d00e001d85500320300c60b05400008003001400020001411404200c0c01e040c1701c140400d072513a03078403403101d480702da29103100b802617102460803160321a501c030b40a10b42401c0c126042781441080c5102c41251528024048481542d06078580080e44521a1b903041c0d07200d070b1155030795211a0790590403188c011900106601070110311504280050752244113680c03061449400e0a0500300d05a44019041da4600c0e08407810a0000da1408180350b68800401d681c0c212615080d0300c0420f009100d007490f203954000881c3e40ba00220070045040034001e038040c4040310280341d151050007a20701002e00c621603060340140c00c100d4040e03004418410000c031a40c000005c02c035228040036030a0380c0d25144046900328001503100118030304075902c00301400d8140d071030f001410300c044042584480c4a016100781e05400c1600201000380d180c045501604201d0504105820075240241c516a200c1c07100511a001e0310102040442451908504a450503501d0012091958107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 27496885 1250 27495635 27495697
    0x1120b01140315090c10050c0c01080408040906030507030308060406050a0e060d050715111b01050f07020303070b09010506040905030a0302130503070b0c0d02060105030a120c0c09020309070902 85
    0x40201d4050082e8100d80ca03040403c0007005218501e2400030305016582401040700c01c5c000c18010300300740042031041c02e524440c0054070f6582c680d001cbc00d1181081d11103003014103031f42c0a2035200c410350900b04100071082010220383c0340101c038880d40358000e1a4840c0000c0000360f58690113120b8010840441c100000210150110780280740038115542c41c0310107888507801c0200d02d4100c032111107088a080d0103580d601030341c01c0c44500c01c894041e000740541c140003201e6080c10782500e40d04016020603109000030b80c0c08100c0c0c0f1111340c0181282d5030380c41e492800325a0848120fa04c00415441d0a00050710350403c0c0c0100c0c8401680300000e07500d048142d200540080d0001540c22200e0100b80e0710105141e2002c20800c4040c040502e030850311a0720049a40e40382c1100404404119004003004000c02c0d2030014891001c90f5001070425140c00e426142183c00c40844075002d00280401d60b00010303404500e60066005400381000e881e011915070030300206a2040c5000c00c02205070341c2c40942c0f03030b10038815 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 27498135 1250 27496885 27496919
    0x70b1303030b03010c0e010f08010e010b0c030c070801060311060702010f030213050a03111c0f0b25200c0d080306040e030d0204082407030e030903070e0402040501120b01 75
    0x1c240040c40031444400b1a00312018400520085010310b01400801c0d03800910144000da404c1c60400300d01c2d8144941035550a1061088500015020075080311003c01801030720b03240310a0b1000c440541d592074403694082c20b4180703c162015031a84d241c602e0603081c000111103e10380c044e141c1c1c10007502120000c900079441a041c01468441c0007401066682e07400490f03a000310301404e0340040c0d001c11a070401a0340807142c2e82d5030f00c240b50322116550004101c00e034080c1d07000790800682100b0f662100c0403003020509508180c2640403e4003040c070807141d0000388000304070045107080550410865145580d61101540555000d10b0602600740065200c80045900c008080d10120706071740f604c1c0c01c1510b59008400f00c68541078010505100c1d8030f00403c4030000304c1d04070300301d00f5113002041801c0100f5114051700610170140c90308004030300010104100c4a1080019044607180c0781e035a00340118048040d14200d1146040000007e2405501d80409d105282c104145180a0f460700081c641c14003904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 27499385 1250 27498135 27498137
    0x190c0522080118060e01020304150207110909030a0f09050a05041a0607031d0102060f04060504022101020711060c0706390506160206011e05030d030e0d0302070b1303 73
    0x11503408507040c0300a0083c5034148907403a40c100c028001911345181603036064400300c40580e01c180100030200700c24032207400703908550300300060740d0307400d0380c14541103090254047c9a00f000809050169490001004001119855944a024108840b012104100c0e10312516a01c403000380424002440e03e540662402e114541514401140d21400702d01140c010b031032706034007250503c01940e41080b0320300301001c2e01100c00d201900d4240361100c0804112100a40040d11a0783e80d030000508544a0a02d8001240c13038216240c0300440519080f40d0203944511005c0300d078002c030341030182c01074200075054860300ba015001910325503040100840e0705100707806441c443c41c01142100501030010381d002e80c4034052504a03400302182d003401d1481c604040508408140c03001204000c840c65400b1940d103055441120494500761141d0044224082c25900b00a80c540519410a1859901a4400100182d028060701d0b51280c5400d0164201d000381d100250468800c00e0018030700e140880741c604200d52007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 27500635 1250 27499385 27499447
    0x109020121020d15080d0201020a0815030a0b240103090b0a2004030503040f0605070f080a020a08031e250e130212040605010506040308090d0227190c05 67
    0x30843d000c1c041c0d480d1019508504142440c09105001e810300903405d180903580020b6241241c0040010f100c010014142d0703c2e52208950f42450075a424004801907a401c061540580e0030204803405103404a0f4180480041d0041400b5100707501a018180d1140e80014040d4030917030300e800e10940544103013080b01103100a20210720710302c07904080240003e50b010300c2c0219216800c00c6201c44151500d40c001e07030203120b01488080002110180700700340e00756000b0700403600d440002c001a890084a408010440c2801001700582182c0c1c1d100301c1e5000d4048000c03d04225200e20b40c0c041d049041010111020340403201400e401c00740241111211280060000d51000c900542400304907081440440d600250700300510043c09814083c00c1d015290071500d50b450540756985104041c4295940c1c0340c065204600c1034815540d81c2c040900c1805948444e02c4450200c1015124800e40203e4480925840c90424801c00c20824400d0a511b28440c1e12424507180c4900300c0400d9441840a10039410701c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 27501885 1250 27500635 27500647
    0xa0504020105120414070b090618010201020c07170d05030c0a030504020d080301060305040c0e0705090d0606030c180c14161103010c0e1507020f090c0d0c090303020c03010902012102 80
    0x144408002d4425409117484100b00c5400e850503608180d03071a4401c080c2000c00f80f0a8660541e115412107240c44040c1c2d042d034545288910040c1c0c0a4000c007081070419005400700041c9000b4a4142d9074401300d44141640e000303035800d400a4070507000036201d0f458040b2003406007043d06800303540320b0b680042c002044020f003e801656428587d9201343c101100081e00c039414481000754035113058000c1c00b983c03c03041280b0302c4c0134000201540600729010703209000440d102c40500c00f0907880b403005140c02c8124425515101e540c0c28030016241e08138008070074074108250300018814551007070180304109111f450f002e1510340c4040341d0000a8006c0e65061210001d130041d40c5d9013480b0b0f10b00c25410540350b52030aa00c0b00c0040202c40002a5030310500228100a030a0060369049003810b0224803c4445181c0ca44404251403107c1c09030203541c00003a441e1100c4400b2085c3c003c118141100e00c00d60845104107007182c2031500761190b40e040203020034030504400506201350210245c40c102241c138014100304c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 27503135 1250 27501885 27501907
    0xc0903010903030e0118020303030c0a0905060c0c15030c0d1d01090308060a0f0509010e0903040306090503030406050105011706061803070f050f01050c06010504020a0e061201090609140a0504020105 87
    0x25015503402c0300401d03524401450403c90038010724188100043c0007460950964000c80c5c1c07a80700081c60155442070010b040c100b118043c040d0f145c054503000d451540c8821007101466541d80615040d244540090300d038584003030401d42c3c1160b100342d8201107140d041c5000120445e01a15822000850f03001c1c074030340b0f40070910200b44500ca000d44d010755a0703010705041a000744420300980b5080720507030514401060066855124045046a021030900c0070641d4903000c0703560550245801c005d2003a401c1078419030a02100202860055009610070489a41d94500546500c044203400380c1e100190300001403960314106001e03040004890b942d0340c03d0170788248002800c004081d0002507041d80745240511140c00d1502c012032102c0c00070709001d8071b07000d144505141da4090520480d449950000740c18a4464803540000742004806484203884403c100c00d4000100740034014a40164605840040d007004c450041c0f2130207110b8941c1c0d524403030300c0e084060f40142c50000c0080c2d050100c200843c103010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 27504385 1250 27503135 27503141
    0x1030b060733020901080c0a030b06040303020304030b06060304050a02090c0d0e0f0607020c011205040809101d03070b070b06150309060916060905090612010c09031704030b01030b0c090301 83
    0x5000d0508607a40800030242481c458425044107040302d14414400b101183c0d070004282c0c0c0d001001188032540b20f0400a0040780600103503030180b504034102250002c1059000800307001a41c0c0718919042c115a80c19090004c00d01027140c01030000d0b4003801c44007016003000785060790010048440186880c007000700c600c0035a0300c22103c41c22903510220404d1084030301480340e10b0300400144060303d160118400000c0010010762583c02c009503450011804008002c000c868010401916502d03d445030904050011450b60400700040700c0300c40700c81081440c3c041428011b6483c08221142040e035aa142e4803c0030303034000e20f00703a00801d00801c0c01c2c40041003007001d944141e074036030018503452504560b0a03083c510041003055408080703040c240700941d0490844415030701c065440e0704a59452400050203051a01c43c950455483c25009012866000c0282020359000f005d4101e203041900002029902c030f10312010700408505801400020b00741080e1031380042a5022141c20039119400090031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 27505635 1250 27504385 27504413
    0x30c03090b03070f0e06030408030412051606050402010810030b07050d060504020c010b1005091507020301021902010b0a0608040b0601030b031f0204050109050d020a06140d060f051206070e01030b0607 88
    0x45500d142d0382d802d41c60b50092005c2e0001c0d00540f079250a41c1810fa44030100b40c00040c20082400800e07205024080e40300b4419507107091204d00351860307520301c0d9040c006d004000954081e80014081310002c0c0c1840003500075803013141e0b030103c0701445590b00c808003290b480e0480d210b8000681d8650100007460b545a002a1038043c03014000000d00003d03000800017101003484030702d018040180311026041c0c0d14a02000d40509650030502d0b5900040d04c0007900a1240c02040c9120008810310003020590561248114003c160741e000300341621898140c1d0400421240100500800b0780003d03083d5200c1e40210070700410290846000c4004440003403c410f0105500c02c11302c0da80410100302c030390f9001c55100020041500c40aa10107016004501d245019001d0581848110030130240342c24034003011030760841e9034104108806602e403141012500a213100c0c00e0705c101c40e00310641d880d45d11301045140c011141500c51403040c081401c0103501a02d034050301c10740d03c101c0038402c044c041400360f441000c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 27506885 1250 27505635 27505637
    0x20a05070b0301080d0f0e190506071101021002090f0d050a080f0a1218020f0604090207030201020d0b09060102060106081902031312030203060d060207050c03010e060a060e06010507030c03090b0307 87
    0x1c0c40c1c3d8100880789241c01e02d030b0300001c802c0044940c11002d107150442d0001228400c00e40e05c50452001000050806102d143e000607003001e0000303402c005116039001c1c00c00c3c2c0f04400b6800e544651034032070002002d90140301950395001510010500440c0303010042d01d44440d204400340d07500b0040304e45801d513154020b101c0a607880340c80007074260149640807291400f00d86207080300700328000c501c0600e50ba505045100090094100c1800e00340f03075540b5034050300d006100c05034080d55201c41c1072030028040d412250981511508080503000c41e80b60407144030340320b0003040c0c5c001d140980c60704404640411019101029a20401d400c22aa14000707000440c806d0000b18111842d40d1500d2501000030900c4019404c10103105106005090b07942440081d065600002e0258807440310b41440c41c1801c10f440d8541d40e1541c031304685401c10440201d4058030880ca110002c101c0b543c2c0d2200420303100c400c100e40070f07800104100043c81c00070380a2180000b4641c000d25003d16925112002e02080b9401950307010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 27508135 1250 27506885 27506887
    0xd020711060703260f010e06040e01020a05090301140114010503340807020d0e06070206040503060a091b05061b03070b010f15020f060106270905040c0e19020901020a05070b 76
    0xe001611019014014001d04c2010704a51804c2040c03d41505410b001e903140e50240c55000c21800d03581c50b0410050742e09520000c40d85d0300b2000e1400b421560185c1c503e14042d5007030540403c1d130103070140050790403038041c00500c0711196030f060011501640010030507031484072003c82a00b4200040d03503240c82d180044035004400c510008002400081004080804541c420301030740d0b07901c0e507100c2e260750440704060300c0719500c0d8125480040c02070300490300125054403450041040d4006507800481c980d50103100b0100c420011559511404012806895044441008048001c0407400070501010401400340c03403c0180035558152040c4007a40b05e1401220320210610054144c24a950f109201d14001843c02d00c0e201c80c0450744621051044800f8030000302d8840c0f01e92a00e00107480110401c42c00110300241e11001020001c02c415902540c4980c4a142c0218400c0c1c10702c44118000c44419014040c4400441a10740203544043c00032411400703080c1c010384c0020410402c05000d800c42c0b060903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 27509385 1250 27508135 27508157
    0xb2101020d1407020a060e0c030609011401050a0602030a08040804120b0601020f070f0b07060603080307020106030510020306010206040b06060903030409090519030807030f1e0207020907020607050d020711060703 93
    0x403010b5503038924151072a01d03007100074030441a8000031001003207a48448003003110b00100160900b0b22403108842900350003000104412180c0640c03099915039401c0000703400030390700e800a00c03110b80d0480c050880543c0c8200704040e151070103400c006500c144201c100501d415282c0002500c9115041170031510f0034400400d0000e03070740c0c040c020394181c02e480d00020b0101a20380704240c44000e02c1032181d035010030f1001034100148803450304902c0185402245c12680da0030310752002030080c40103120a032000c1c040d00480000c07001e45402100e0041d00c05a00420203a1244c2c5c84ae1018100050b0071b80790b020b407081051020548091010340f0080070711400000b0705110354202641009088540310507220780741d226800002e500440c0c80b40e00100b0038600098800580e445141c01414408070404032580d401c40b0707121500b038145c1c00600003d8401d851071506601c0d40002a42d8506040e21902c01040d0180803140303038044907901402102c0c0c007440d13401d04490b030428081109940005810307000548089a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 27510635 1250 27509385 27509407
    0x20604050d030510030b04060e010204120c0b0a050f09030a02040c0203091302090306010e130b0f07020d0f05040b1c06030308011a0325020115081606020a0807060b210102 75
    0x41865030072a605080c490341c90100e034074801c603619034080180002521000710702030140070341c0070041d030b042050000c5545503164182d90081400c0040116602c001881003c40d5000903003065592004c0c0c80c0e20340c1414a04060940001c940000038060f4242c40780c2c2d00000007590760f50244031142e102070780265640d00c00c90340c1401401c2c0030201203080800d0040008000d1510000703145811a241c11129a4007903c0300003000307030f1007010840c2c0905030343c0f000d40c1800005010032040c18010707210758003210314003030300c4c41c00540b00183e60000c224041001440200002c8181c01c0042c610304c85030848400c44005042000c8041314041d07002074001620240040c040085807420145401070715400c2ca0f410340c5000d44030703d2140c200c50f840c490404c070900395410788114000d40105030038042e00c3c8181384840d03440c2d446007543c4a55007200c6502c0048904070010341d1a0000c141c442110381c0007580701c3d250400345d44881d805850b1003280280c120305000d032075410702070b10300e0070805000030b0706400503a44042c00a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 27511885 1250 27510635 27510643
    0x150301050a0605131b080c0d0f0b1f0c08090312030f0108070b040312031508010f0903081303020304090213050a030f050d08070c0b062704060e0d02060103030305060a1502060405 78
    0x300065150501641c40a0f90340a01d04001d64111b00c6c0030300b000d1f030324100c0c034020030702804031100085070a20032424262460b03a003152001c2ea000741d954619148850308285c03003090ba178219140c0426454130440d0702158080d8010204614041c0072500303003160901d92440c41303520485404100322240801440990002d02410000b8a400403020f814a030950311503203102c400381e10441e000c1c10303034661040d41851140d0180000900c0414000c0003031011404060000c0c080d5803004a0000300c0c0c03180010848250070880061140e05030307001b10b0415040c1410f17100207501120400380322111003000002c8503581c515203000607521444a40101c44103a260851901d04802400424409028204072400303030f0181901e0f00c203941200150034140c90303120105030082400d07964607480c0115a500c0d8190702080301070140c080c41c8203840400001c4880d051864840611448403401030300040c0c0100040b0380b180d000713160000c1b0000c00c101c054541d50b00c0480c0503403603007840c0724026070042d504100074854140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 27513135 1250 27511885 27511909
    0x110a0609030503180a05130506010311130504090203011d0304030506151309020a0b0a0504050f0d050a0b07020f0706090303080702070501051e1611090903070206070b150301050a0605 80
    0x418065481070640d610740d602c03801601d45120303054620507440d08007943c0d109540700c020140a00608544000032200d04050181207540c40d02080c100726800400883d000111001c02d070041c1150b0288a013440104005403c05585c203980c075640320382c80040c914241841214070200d607400195651803031440e026051003070041500c12851403a0410309002d844141c03031800c00d0300310018001050101c42c070006003c190141c20005c0300220124032040760a412800900a540c4104c80c2803200d40b0020003000310009001d4002041504032101d8403000540c800009504480c0074015545031070159594107160204907804040000c402d58010402d050b0006c1c14541c100a552000c0d10505061a002034881c6c03041e024400000c071140034000808540b00300c00e60700e0030110f108072200c0d000c0a50501d006042d0b129846e0a02c44c03100c4501043c002e01c400001c03103070400d81c041c14950400600b601c52402a5000403e01502c0200d2120286c1e0680d40038031a040c410010b6440015400b81003c00348140f0344409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 27514385 1250 27513135 27513137
    0x4020111070806010302060c0a150c020f010510120f0f080304021e010c0305130e0901060602010509070303090b07031205250f090b09010504030203030c060412080103020907080411030703110a06 85
    0x1440c024002c601011401d0350540360161640395070350303203d000c06a1801c0c0c01c60b000540340009204081c040f004107074022045080d02a402c407280640d016031010708a80d01990545030300c085021080002c0309680c02c640820354085c45400403041415116680d070b000e0038000859140343c2c00420401140341c5a560350b41641201d80000310003903010304c0060243c4000d00700140910501282c4080d4484c0b032500d030000901202140070602d07007804070384c0318040d01d281c2c050400554203207800245451800141d1400312505070f0b80c2d0619440c43c0032121341040d0f0210300140c0420a4541074550030105a005a47c011070b8100143c1400503604011007800c40c0c00341d24a0b4041200000314980720f60341c41088801501c42803551180d4800582c001605c2c54802c3d90308c002e4041c00301041c03a58440c940840c081d4803e9008001c040801c0d16482400ca03019842408005d41c0605000702054046200703514180d440383c07191240c0321a80d641200002d00d0104c0590085400380c00c8040d1113600d5080ca080d40f44010400c0e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 27515635 1250 27514385 27514393
    0xb1503090303040201110102041a0c07090209060d020a05160f05010c09060e0105160b01031202010509030405100315051203070c0b030906070c0312050703050703150806060103150e0106050304020111 87
    0x4504641d0700c92001400282c1000300e0303038503a810480340c00c1d41280c00800050305103e0a038601d0404070200350b0808415124140100c000c001414980341c000c89000990041069141030042c500745c01c001d401000d03a075002c00c541400754800200100801c440d60900402c00105c02c40910714105003504c020014540800c01040d03010400d040e0800c0c8084400030007400e1a58807002c10a551001010400348041c00403102c02c1c000206000780c400012005801c1580240710075500e6a260341e0f50391069125158214541140a4560601c203500000741041800880e01d4880d64580c0050a2019000185000743d000040c110301044607020b4180c2c014280c01c1005811803418100480c0c81e040300900380c0b403d0040c0c01031180d0404d0712640c4900250b1884100400c040d05000034001c0007080100c4000e40400d20340550804130140e0804a4005c0716880c80040540303540c1c030310044000e0004980e01c51704c0c0c00020000801c00d1a07440c43c68501074181643c88544900c0d060000510303d8582c40301540080d00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 27516885 1250 27515635 27515641
    0xc140a02060d020c0f01090b06100305070c020105030a020d051005040c0c080301030f050a080d0207032601091104170a0605060d11040b0f040c090303120e19030207050d03030b1503 79
    0x1e800d800d0301d9034502a07420050f118400c150b00315040403003691004c02c0302d5290944401c02c002004c003803a0b010b02015112101d0207884008241d044501c1174820b0b1010490340890310b001903110701c004603806010f0403405410550006030207420b41d2400d4a0404108a449809200c1810140b180e10703600d0b0b1291401601640c0b00380c44261081c4411f00000d000d1240468884003808010800440b40076488030000e541c513544500854020b41000c0011000100384051441d044000205c0c845003824006541f03c44503482d090301d050050140c10441d000c1e5010501000554500d2844248003220748440a0071300711440b07241075822144021720031441078002242080106055942c00040c02030150307000240d440e00e40001440d501b03c0482c110768080d042002c840040740e80042100210b920a480b10010325101c2c11000090394000070b1144465404101a40100e00907201000324942c064019100304644130004980d05c024510030950120f0b4440b51509046e0402c070725130800032140714100d203084d42 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 27517991 1106 27516885 27516889
    0x200705060a06060203030a050709080d030905070e040305070305090112020403080c071a0d0b0a0b03040c080f070302220b03011805010f0902030601150306030c060c140a02 75
    0xc051540892221009070050200307882036074001d9400c43d6110082c0300002c1c0302c02080c420400000080c000f5420070240240c0d143c4894039500402e4a801d01e0800d40c0c40c041540e408240400990700801000c03a60020645681c903030301d442d15694415041c070048464100c074851030060944000780020400012600400304280c032a01501d003260380e82d9800010009407040600d0882c14100640b403140980e070303801914160b0000300481c01c4c4a84403004001150400c440455984d48070340010b205d1003404100380c01a1003140c1d40100307091415940030031080e00a00410207a20480c1412070801d00603150805219144003800801401c0042c4c0b4200c00303c900f185000707845c254030b010301c8404a01160300076083c030540c0140040215920380320001545040c4001000205580c1300f038003100241048500400914403039848100442c000e00f0401c4810150521100483d40202d40e0b0030010303 = true := by decide +kernel

theorem cover : BRFrame.Cov 27338135 27517991 := by
  have h0 := BRFrame.cov_init 27338135
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27338135 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 27338135 ≤ n) (h2 : n < 27517991) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
