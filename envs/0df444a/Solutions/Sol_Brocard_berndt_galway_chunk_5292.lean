-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:23:17.413156+00:00
-- url     : https://prove2.me/submissions/f052a20b-ccfe-4f56-a08c-bd409ae1e5c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951618705 ≤ n < 951798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951619955 1250 951618705 951618709
    0x8030c0601213c02030c0f010806121f02040603050c0a02061b0408070305010501031a0108120f0d02120402030c19031115040b0a02070e0f040b0718120507140a0302 72
    0x1000100c1c500707003074001d00040062100501401c540850390f02500c25a11100110314040108034000300c0c080c0c0740030385100c44804c00030344041c9014251903c0703850054203210100e0010040d09403095081010140120b040d08913400095005008440020b0300344800074a00002440460700c00d108180d00825650780c40008003a02000e02c40c1d400c00416204000010300300d01e00300001e0014600600000415503d103151000e81105240700e480784198102d8010000b181c1c0c00700306800014040c0510503034070340310307142c418550b4403a090070500801e1001c1000b0340d620001c0c10042d803155101f682140c1c0780881c00d000308103480b1814800ba0f541c030250304000340005420351000c800e00c01806080024040d034811050750107500300d41c206418090010403e008078030380c100f05143c000c2c03210701c0c115a1141003100c0c550107030a000900103004440703140301107500c0502c5291000103507203003403144108541c0c4492016207410341450042d42c05100b14100880d05481d10714106083c00b800502c110a144c0c0756a007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951621205 1250 951619955 951619973
    0x12102060403030e040b0a171b210a020904060e150f06130902040c0302070c090612061a03010501320d1115070f0b252708030c060121 59
    0x840d858000d41c481c03071030086c02d4031082c1809001e401c004000082c3c10024805c00b0345050300e17940d0854545105c56400a80d10b0301d2b108445206035002910540c03c402d038010645103030a1004000035008406d0f0810002071141550017046400c81c2601611214030008500c03610000054620010b002c694001060162410940c0101410041a4080340400141d00080c0407552840c2036000401c1c0c0010740c140403c6080030742c00c405008441401c1000c0350400c030b0160455903107680d0080a03240e4034208000c140c3d00000c0c01303000702c12004000f884a0341e10b8141d000352440070f10650070100800c3c99aa44481e500000c10400360400c041c241c003101d49000e03102c0010341750224840c2034200b4250226907018150040003000d60b14010290300807804035610388000d050f40c00070158140c1b03441d0000b4190392050103481ca081d4544540c542034621150840682d000e058240341319106c04c140102c03001030701c40d00100103449107032080c6083d520280c1e614036689410348a681c0e41140114541360f4a800000c2000c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951622455 1250 951621205 951621227
    0xb0315070903080301031506060c0804150e030a030f1107030b06091e0c0301060e0f03030a0e0310060905061c05030403030c05030d021b06070e01170c0903031201210206040303 77
    0x11604941e0956a92109181984207810940f0201c0d80d00041c5507094481d4003480004001918103044402c410b52102000d60155000e00700000b06500c180c41920f40c414000d040c0c03420401000c0c3c4184180619000d8080140000900045040254171441040c0041580c4085a4004030720070030641c0c0d0304040040041c070041c82c105c84860864416094240c3c080000707441030f0ac4a00c0c1d019a03a504018010b021311180b082103a00c607800140c021004c46e107010056681d80c0b8100e0401480003250840024100965003459a101d145048000540e10030302d03412040c00b404094800e54410040520060612141350401a0a0f40c1c01003004200192003410940c40e002d005000340c1c1c1c1001d000d03940740020799001c00b520000c03952003141d10342d150740c0c0e00f884074a4001500d401d068501c1c8215500107440c00b40e04001d00c40c0e410200c070b400241800c0c2c400044424540d401020780799102c0300c99000e86c05a082c28001c40e000340e00c0fa05440d8140c060b40b8161544040c0e0001e000c2810039145a908a0b2929200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951623705 1250 951622455 951622457
    0x15090308010f1206050c0d020712080a150e1801181401020a050f18040c09060305090f06010618030b041b0e0601080412020f0708060a0c05090a05120703080c07180b031507 75
    0x10800040301c0b106a2000e40b090034452b8202c00105001c1d0400205110000340c0340d003810f5440c0941040d00c0042c2c03100314a0403250281c1145081d0b40da400700324200503108115441c0d143d42400300c03080040448042d856516031152001008104456204500300d000b0807040d0340101c1c070704100c07a090010a40001e04003000411250a024980302c1c0c01180036102c0b20402d01c400300d40d40000030f010103605405141d0307201002400408000f0030340b00710550350b20300611900717050007480d022132512110070a0361360b0083d5401400d0390a280c02c0915108801d0a8122402a000c10b17194401140d402c0741502040d0041005035640341c2d041e21140c803a0340c10446145080810740c070400d050041044024040c00740101346000140c08035280005c51907050f41d110700014400c01200700300b1611180e40b100d903498282da2081d12040c8240d80b01400d82031a004640d00003500c0e007207000c81e80a250a400050318070036150003400b100c280e00010798291050710761056020f581600b01c1407108010728030301010545c0c000c6076 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951624955 1250 951623705 951623707
    0x806010509061219020405060306040b0f06010909050916050312030a0f020403050a050d0905030a0302070e0702190609020a090b13051005060c06090d230c0a15090308010f1206050c 79
    0xd00030350b8030701301500031041c4540316103000240039071078070744201f03584014264050020f0340703440c1e80d481c1141c20008040c1c6401c4803075107000c0b5480d41d102e40e5012015144081c000c1085091072010346a643d903003092000c40a003001c850101f00390034042480e880c2c881c081c10080341180c0f50203220b900541610345c914124540d00b0301c0000301240040000c0c865040c0a0700c0540210311001e640104116900e420050084e4404038072800040d900203641340c202e80d44001a8056600c681e0012030901c8500003080c5810362154040c4406d220303e65000400720391081300c003840b85550f6a5240c80980311149603080e0b00050b42d04402650321110303042182d11480e8170084a08481d2620001402908400386486060b07111000700040c94074100095142c000050807c8550100e500c05c500401c148180804114074801180183c4d94400401401c1c02c01c0e544100c24460070082d4080c3c2d0401812645019800201110300014a04c0e91000040003590030a80c21074541450580710800500300250001e40807a030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951626205 1250 951624955 951624979
    0x150c02010f140708010f0602070303080919080a0305070320130f0b0d110702030639071221150f1e080118140309151b0106080601050906 60
    0x1103119080100640d40b101c01d5081c00e08140050140b4416081645200b4584200f400000d80000e5010216030f458500890566501c1000d10f003055070a000c05a00103024501e18003c205410000c0c200d5654996030410a554070320324201c06840d0b5001a40c2d2807040c01f040214000000c48008000007000100c04d410301d981d030340c11411060030555003c9104e443c1d000c00d03041c40da94200d0107200001c052020405041c09100d8000a0301e5180241141e03855065400400c50304003809034501a14609000801200403074060070800d542e4000003045a03524108041c01141c02e0107505964596580e41420740c0ca03038100700c624200102020356103605042c4031110006120249401504003030214601c000244100540715007040b112140c102c9001b03641407003400b18200b90300001c489152030300403541446e19400c00a41d98190301c501d40010740c02031070000d10030440480140c000c0120400a007445030b0954010382c0fa45080b54070500030036455402c0350b00100711601e45907010300e030000c03802030030403042c06 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951627455 1250 951626205 951626231
    0xc060106020606040f15050415030804060815011b14100612110105030f0a09020607080c01241805100b070b040516030b07080405100e06010e1003150c0201 68
    0x1502603125100503408a010469182054010780c9108142c00f80e0a00541e10b90012440e100009400f800780610750720801030a00903000c0b1811002103030480142650b0b152100d00050a1507421544c1c0c1d2031610785824074406551040c840b4035004074070400c000c046803019a0f1510b000b1668070011081034410040344492000f4988035a0006003201c00b00104400c4ea1403800d51941e03140f01c1c01003414000c00303208112441e03ea80060031b0b84001811000520800d80f07100080050180610103400c005020403034202525056100000081074000041c694891440300701920503003501601c0540001c0140000100003d5003181e41c00c10b40c48a00c000c207003529111803c1c1160450340040d5500f24803c4c05010030f2080500a410500f00c00e004100002821902e814285150240100d42000040700014052140030701c01c120403006c600303c09000c0d45018543c041d0361003000707002d030040302e5101c1e0001c03070281001d28840d0f43c2101e500c038852031003800c0f4082902c0c008180000390f002c159521415905501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951628705 1250 951627455 951627463
    0x13050c10050c060703020f0a0c06060e0c36130b150706050c0306010f230408010c090b07120c15050f15040b01120209042406020f03030103030804080a050c 68
    0x100c8035074070180c8606a403010145083c4000c0c0004050510402c0903010f13040c40002124407941c20ba0030110612501d80c40d103503000b40318503400211031760981003e02800300300d240024000740c40b03a291105580001c08500419440707112060212420710038420350520300b090b100c400c992080d0001e0006016808802060b055400000803180d00c10000605404000082c840c0ea60072032840d1078100d04500c0d2480c00600304100041243e07042c0482d025004000701803004215a80d94884e0402c1a101c550b00d04249028106160003000400c5480b1300c00718110381001c0546070082e81222142075210070030441910b030031410281c295072001d080e110000c24070545011b094000c1c0b00111820069141010200324101040b00507540704034100034084c0c480b60703441450019007505040d0b0043e40c2e0101c40d00010001c04001800320b10403800050300d00c2c034009003042880100c03441e680030340f1002440908480d45a2000740001000b040043c070211340800d150601401e80c84040342001440d080c1c1c003541c036030b20b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951629955 1250 951628705 951628729
    0x60608221208041e0209042411041706153c0103050106020a02010207090b06040812040603150317031509100512031c0203040614010308030406110307050313050c 71
    0x11595010611041014181c0c01c04d07944507040c1e60b2840c44042c20703400550141800f80005e0411000c251801030320030010300c0e00c0604030b10b84650421060b0300c0a0721421813078005100e010001c0e2514400407480b68404103689104c1c08840d094260405000c404010700d480003920700361040c15070030382c4036910100c0c0f980d0b802d201e0345208030420004250070340006003960016042030085402410b4482c0044c0d8001502c042038403815440860070005040101300746000b241d1024085104001003111480a81030081c420fa0b841d556040c80074511140d42512890701a1000812040b408561588941d03410030281d50086809005848210f007c1c000181c581c0703600b513600c00c0350240704071010009458028001200080000301039404e000003640101d01c0704200c680704111068000001508000c0e443d8004040e07080c1c4443d525080b940c4900308002290011102251341610300544c07440560803131700681c2d11600d070a9403601d1071030740c0701440c840307041180c1c8004540e548180004e880c0950380f1b1900c1c000e9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951631205 1250 951629955 951629957
    0x509030a111c02010e040b04230405010e0a030f1b02060c010b030c03010c02100e0c0d0503030a1a0d0834030e060405030c060f0403060c030501080d030606082212 71
    0x260a8644000c00c82c02c100050303a4519441c1095200e800141d800042140c00f611084900242c11401400400c0203409503100000e158103005000f2844c002d03892260074043c2c0e00400080202101d00400036540d0b11105202501050021a2502290344202d00710b600c000e490318120000c0c40b1490380810303174039080040c100c0c005035110186042c0c00e0030100030641112900304c4c000c2c429100901d41c042d44400010042c400e40d56100c44d03e40d640110100320402d0950340207004036400e803205040040c2c90742c10503540c9080050901c0c01c0500200c0014020300401c0380004c0800e408400301d65289106036200e03207040c40c200709003440c0e24405d00314245644001400b48210148144115140040c442c50b510b8210354410340701440240202e072000103414440c1034042d02c04540c0d4104800c0c0c107170f4503401550700003000541001c126882055043d080941219601c200726030f52005441b1050f01520420302030900064009800245d0a804024040000c0c14900364080c1d080784190302d5010303010000740a000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951632455 1250 951631205 951631223
    0xc08060f06130f091101180f17030f030a02030103170c150a090510050106020d03050907060503041a0702070501111c081e0103050c0f100e0607060f0c0e310c0509030a 73
    0x2401c1e07947c0200c00301b40c0e00c40c02d0703000312501039040801c0075190880d2402001c1d0962000485243c941d0001c108031404141040700701c130748030314107403084e07a001c1d40c024081140d4180c800e01c40c5880003440382080c0d40d81200c9090260001201462007248842802001406104c0c2c84d2900a0b01003417040c0411540101400e1000c1040d60511101a103042080b98030340c0200340c45c020410007170000114404054413524030300503540c0d84440c10410300f801d1100c0004483e954411062080d04c2e1f0300058104101da2080e00d407000c00017550807010303481d0303000384103021801c50002101c040c82d41e20034031115900c840d6181010001000d178180c100715015003600b0481d51a440b59038030780c28524041e084620101c00444180101900c4840018031280140010300d0003124003094050401610340c00072020242403c02c100b241014160005258640e00c4803003901904030090913101c08286c005403400e00740b011f207040d00002c807003860084000346103108900c0c082000c207021000b01303542c041c044c5544403409a1016 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951633705 1250 951632455 951632483
    0x70e0a030b0709060216080a12200a0b0601031a010315180f06081903052505010b2d06070c0f0e071403010e1801090209070203070c08060f06130f09 65
    0x292424911b40e04000e100d40d40820100140c120004800019503849071440301e1820170114281d4201c1a220010110700d02d038403110b07001200c00058030002080c0a80f80c64505902d80100641c11200100b000c0300c00c07080d120030144960350003500b048491038071050042c40f400365600c044078580c3e1440a104041940c591000085c1031300c1c18003a410150045d40b01400600c881a2500203211240c2c072401004d00002142c3c110040601c0900010000703114020122601c80c1c503d03200c1e0080c41e5031009036115020701741544c84a00704648074080003c0320031170320390040e0043c1c0d020000d0541001d0130444140948601c0412060420290038004040a4010f8206030401b1600500001240e55460803095400e01c0104100d42104400a0300304d54010300000d0b00d81e41110000780900309806c0b005c0e41120003001400354442e0f0000041009900400081c0c81054403514070b41d480340c1040d03401d08020025000420a580b41800c48100011401c1400080050092402005480c00c41005450075134001c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951634955 1250 951633705 951633707
    0x90411120d05041a2b0227041d070611010e0102070302010b0a1d0708270304140a030503180a080706020354040501030605060a15020303070e0a030b070906 68
    0x8401d64440c83c101105040c81e01e8140c82109050a0340c1e48603a904000d840401c0099545e9811a66100c40021a02140c078500604420b2500e09801000380a1403401d10302c0078902c52030031025040c410b4824082e16115140200865038551151503049140d5600c0202c100300b401c0034401405960b109400100e0810b00c0f01080124000482e801034121801d594030000d041c6c009104901d5000c80641404038545d110b4003128030f402c05000c1055440010104071202e88503c0000183c0200e80c0742202010440d190101800040c03242e030b01c40101140d106100158400d0103140743c2075115400a06a00b00c2c9a941b01d241d41d140c000c01d5803001c005a040080c1150781e880028041d041190001d4165a01c101502d1140340840070503000317401100c2905070301c20445812050702d40e500103000208180030a585a0400341c004000660b40e070351050003030800014440c0d8030b581340d4280440361600130b1350540d03641c004181c8540001230305080d40a044404003000041c3d030070396070501500705913a60390344181c14018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951636205 1250 951634955 951634979
    0x1005090f0c071e140714010e060d0911131b080105010807080402010311120a0b0a08060414011e020d06060206010b0442020c040902090411120d0504 65
    0xe90504401014100030014209808440380c140d0312811207081c40400c0b6903c1c4000303045080008082d070443d40c44400c160207000842c102920001d441080c04030409100545000d415061802d030044c20500a01400c40711607408641100e010b450945240008200080d888440400d1003200c11566504c0720881d800804409001c1c0045500f09606294108000600f040000404070802c0002400029085900c80d40002c40700d00160701c002901e8500003c180a40440204d4510801500e0719501e050185840324503501201e51440c00b504203903d490321009a0906041c180020540d201c0c0c00ca94551404a845103a44181d00100180c6408008401c541034072000ea000c241154040401030080085800444c2c045600c6c1e103543c0e0590005206240c0341e0089000c0d000700c040381c84603400c071002140d00c010401e410280340c0e007911199286841000100c41d8000e2019400014a0000400084900c0e18045450320010006619400810b03129454804030300c0c1c1e20310004901040800603250140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951637455 1250 951636205 951636211
    0x1d060c0601030c210213110307030b01020609060f011518030c090f090c12031b03020c01090801050c0406050912012a0206040f0f020a33020604050d1115100509 70
    0x500e14000d0a503414403044d41074403200c20291140d8054028034980d1441980071070034240600620701d80700d181060010f0f00800801c4500c43c050f0284070700007030301d00d500401c0c41c9115880c11007689109900f0103941d9200c0a92118181c0c003448a042011401d80401c00300d50b01c0110321541c0c2c0300d17074500e04080409081e01c1082c08010407145c00c0c2500b140000360401c1e10b440507940984a95030040460f07080450f40c011182485a260a40b1000700d40300f0f140e804140b1a866100a80700c01100701c0c1c5d100d8180d402c07201d08a5043d418008140410b01005200d40001d010b817070300c000d2640107074189030b0130301d2421180040071544442e20303860300a28010b07006000c4048110058005440b0301c4c81c0540326103040703003400d100042c0440091030480045542d803840c00c0015141140c040d0700c1d07902a4800c0800c000d044c00c49050301801481110260302440000c52a1140340c2c4032000d41803041d185a41903540c05040702d000d54207805605602a0030030740441c41c407407044655801d1590702e02d140c03009010100b0b10103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951638705 1250 951637455 951637469
    0x9060e010c110d0b0f0124021504140105090a020a0b070b0a050408070f11042a111c120b03060c04030b04230f06090303090703031d060c0601030c 64
    0x52a1800580ea0003500408030940c101e405002840003610010301d900c0c1815500034082d4000e1401e120000440c2400e10781a10703802c0b02c1c61034080381d10081400c0401d592400321001a4401c60568825010038181aa0414811408042190a00246242034520448003c4ca5507030024020b01d003503141002c0554020b01c0701d852454500462a161000700010080221950988401c0420b0412a0003811a1116034111001e4510070b102441d000c20081900d440040c4a642072410091000000d00302c000600481140d409058844c0d4000644019080342821842e501810b004542c0c0034034206110030480c1034641d01c00041c40780c980065130841c0c3c10b0305070311400f0764019010030016410300800c480c00e4a40040c2c101009a031a80380038070442022414003115480d1018900401000028840c0001201c20044e28001d94600545a80c0e0b400101c91004542d4081d003405c1010030701502d045c0a8519481114010a000d504003003480d81d401500400c5460380488010001e00000d290100090140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951639955 1250 951638705 951638717
    0xa050c01180504090516060f0306050f090a0903020109060615170c040b16060204170c011e120b060a08010611010603120e0102031308071d090a06050405031215010906 73
    0x74046034181d0590442c0030b01401156906040300034003c0800c1207094400c10704850b00c00c215181d00f8028111700c1e0a0f0000000b00c0c1c101100803440749000301c003808020101503e411101d0b60365900b1000030303103e00407041c1c05556884414101041c0c00b4041c1e500940b4003104604030422031400021310044e84e40c60100e00800100d01445030031030005080f20704644c90407204903242d12003020503810340b680300d100c0103080d544005030006140c03007101d43e0a10b140030701c0c04c203407203e42c03010320010748403154202c410208815080d162710a0040c0560b161040d00d4607c1a400910b4010240200703055602801040c0045000c5000405c105903008070740911107120f80c1c0082c0042413070b50340c41002d21503407040e40341d007400140c000c8001e03641d00c02c02c191542401d44180a010507030b91200495140c0d40e03940650443d25400c01401230310118074050b442e015441c2040148105686902c0d580000c040247c4101c840f40010800d410f2404a09020503001e81c42c2d03c01002210500200090806000c960001040c081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 951641205 1250 951639955 951639977
    0x316050c0c060705032701120e0c010302030c0d05010902030610020d0c150b041d0d030902090f0907050907030b0109060c030c11040b030a03080a0b0105070206030c0a03090804080a050c01 82
    0x440c1d01e01c02000181c1c1c94584400705840c2440c2540248212918500c404030900c40d0b031000c00ca45001c1a0040a032640d070310200315000b4041c117a41c1d8481100a40b6400499000000d502c250300659010000e21503803800c040501e4201020748100303038040b445240d0080103000c024603040341c09201080b51400100a40c0c0c030020b5016000244054020300035950074484105001110341100304106030050007005442d2000f00b88118558900e075154840b4400d000308114001e0180c403070070101540040c96064141d4880707020314881c010013070020401c1d0150030400192a01d4041035076000b601c150301c0101d44403e01000040145182c1e43c40b2038204141c0004e5400400d07045240394540517000b041e50003002c4002c4010030003401b94010195098170a0031140418140e000349858040d03001843e003440340401d95401107520380a510780c0a58400d60410120303174104403103001445207400f58100400c040000d601c03610015041503000042072741202200c40c0c200003042c07002110b20711090921074180a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 951642455 1250 951641205 951641227
    0x72304031a071403040c0f0305100f0b0a0b07050a0602041811040312030213150302070507080d021504030c02060d02030f0934050409060209031e0c0918010908031605 73
    0xc0c01c24080410b0f0303010010100d410b201c00c46801001920b482e0b004182e04a94034a4501d88d0384070990700c00015207140219841c1601624050b0030340340360b00185800045818030200003042e500410301281c140c4640f02080c0c0000d00180041c00040800c0030034054004200c908103c291121940c0706010758030b0804c030070300c0010350040e00360b02070311440d00c0d005890382e4000b050300c114000e01f0340098915503400c981c0d40412a500d50020030481e0b00c2081a03c1420341c0d0744030b5071076480c0e816200010258024010314506d142c12500300d6503200d402803528040080254010079481da201a154140840d00001000740c0603000e55440342d0032200301c0c00103104002101e0144e0a0040840003460800c0360707412a01202e150ba40c1c0c003440040c200040080043d40c0441c600103009500c0442007a0090140780d200c021580b2480890105000b0f0303400c0548001e503100303002c21030000d074000c0284078154480f01108110740b001340b04c1c100c222440740aa099690900091754002e10a03040d10721000c02c041041109402c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 951643705 1250 951642455 951642467
    0x120a180b21010e0f06060d11030a0e070311061c0c020a060612151508100506041d2e0e06370902030319081506030c030609072304031a07 60
    0x3044038883c01d84e240344c03140c0c00080d5192061604041c021400e14401c0c41c400426080214041e2920b25010001c0201d41004240c4030b800030304c405449020340c68100340090130142c000300400c44c111044160b007203d140c803140c07003150400c0c092040140d00c94000d0004100251107804060104400c0400b96008140d441216075582c0f40c01d000000c584031043e000d030030980f640c041d802400304a029184801070040c64880100022968284150305240822459411124528595400700405000700350700000c00419a83e200300d03003c0b2180901110001c01000f124400c82c030003041c001b80909a6401c010390400c3c180805150700201006807510940c190f005c09548500001d401403034040740520303041c0002421400740ca600c961442003140342e142000350f400905d0314844d200824210140600c3c0d68103000260004440d83c045060f002c2001c90840d107004c1d2181d23035101200345803040030301c00040304400351440d01d0b462500040c60085024404c10100e2000c1940d41c0c4a219800b0305140b0300940010130b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 951644955 1250 951643705 951643711
    0xa0b030118060b16050309030a03261306050615030a0509060705180424080a1509020108150d02060c211204122f15010305120a180b21010e 61
    0x1390302040304070101000021310545000200c000c003031f41c07418440d504002c0c0400c107541519020046820041c0c1281e00b440c2c10f4018020501d4508c011408200350751001e004040c05090503a10102c3c51021032a00742104008601c81c00b580390010a0a080204115140440c040c0c450000d0150602c00e24032107940d801d030101d1242c17004440c04100341d900c010502c102d28160007400400c0c3c2050040204d5601e40c005542d1005910400c48003c0c0c60625807040e104036000000001d00055626000c00e810740d00b0007001c032000c008024946071382c0103066030001d00c00317520240812140f60012110a20a030802454540c1c000030150307800c0740340010360346040608200080000f482004800940152a803068003125141c0046030241070045071101400d0400394480d860585076841614070303030307c0c007895004810342c102c83c4d00c0030040c0410400648454038940000c65850308010314000c0c5c1c1c031501d070041c00b0030038010401800019070b2900900005601c0340030186000103800c01c4000100502240c824036158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 951646205 1250 951644955 951644977
    0x306011a07110402070c06090b030f0103060b0f1f0e090610030c020a17071e02150c010f0504060e06070f0206010b03190f0b010305131a150a0b030118060b 68
    0x181e59a501e00d407440ca59104428102d03005480440e540c0c04200201c1c1c51a4203803800f0b030719a00d050640d139071110f907200e02c42241d034140d072216218010000076155420229100c10b008044881c005a0440800e40e00c0308580c02d1014801d504a01c60154642c000c48294203142e8181d0f10b002241c50800b01141c5103850100d0b41c4410141e5401c800d04001c1e03c00d01601d203050b98400c41006012000341c03543d11994009032003e4842880c0080081a240380c07a0700d404054039406041d44c510310b810400c03c0a8690080503e00c203495407520188c400c042c1c118401d16103d80e101e1f00b400a504008102c06514088008040e42c0a0010144c012017940d0b4000800c1e9044070206010156241d0b10a450024061110340e5083d5905060044204820b180c82e00407000501702031760704020300e5480030080707400b2a40c03005024040c4a11a140c19841c0b002e18030405601c014501e0b4401000c2c80c1c94804201038010710f610043d00801c010005100158601890380310780d0038426000d005050420070003425602c50a00051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 951647455 1250 951646205 951646207
    0x6280203071a100503061e07031e050a060902070b01080c030105060105030a180b09030a3506040e07080703060e01060510110708030a0f0e09090d12060b0313020108060306011a 77
    0x50300200c2c85004403005010081d0a491947c102542c0c0744005011012140e0100350b054400248001c1c800e1145d40704402c9000048800c11141c0f0840200070034029040e40c00d681d0301c8a401050001c0c141c002000450303c102800000c3d90b2500300403e08048507203121324400d904100c24020725a038400191794001c3d6400314000340540560748000100c004480b00204100b071110208881150080094285030b8415200c8010010b01d25035a400c206241d00c107558150b0302040b003403404910120f000c0ba68000d101070400241182c0000c2d09929050066010f5041640100010b02c00c0000038092203c034a00342d2002800254180000039600c0c3c5540950741c002c0102c10b480400d0848410005400100082c406030ba80d10549844010850306d01035034a900801e000f0140791f800341c28440d401c1c9108205000107400d40c0078001108842078642c0404841e016511034602180c0035901d8801075000f01c0030000c3c0e0608500300b610016003521801080540700360060300040101c0400c05506212200480001d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 951648705 1250 951647455 951647461
    0x40e01230705071a010323071a04091503050d110c010806030102090a062003131511060a05100509130215040e19200a050a05070206280203071a 63
    0x2210340e4003a0090291030030900c4020490003050035007100d030586e4001e1049200c80518200703130300c84041a0b5009038440794032910f41080200403031040c0c00c0c000200c0c0c01c1c409280954070340c208421389108415031b0040a403810340c1001004410401004010100c9c00c2c44100f110400502a8a03404504c1c000d44c107003c52800000c847d690300703604403904c84400a000e1500349441d00d42c014501c441c2c0d609501009441c20b44064101d050000036580300f2816541158109814000100820104513000700c06205180c10400c01c094030034040c252007446041000030f542d02e840d400d4641d841d80c00b648040c0c060641c0900303200c403c012800d01c4099071030b0103807183d07a126030014502103040c1c4501c2d8402c41d80c46100c0345c02e00419420b08402000b1843c1c1030142400b22403801e45103000000c22034bc084c0c0da400e140c1001603140031703401140030702401e0010b4101207080c0710194004c41c0d83e0303511062400b01d0105503c03400d0001d6845c083c1e502880020140300641c2403820a56480d40743e44140c80780782c80901d101c0c2d400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 951649955 1250 951648705 951648707
    0xf0f07140d0204050a090b0109090b010312053c04060f030b0f03030a110c010503090d080403050d0c080a110306060a050714150f0105031c200607020c040e012307 71
    0x9040310642d000c2e004000901e0100005001420040401c941c001040000042d0b40d2042e800754614594102642805691841e03444010b00d40032041007005214090241c2c0d803590060f10790b1102417034189010200390042c403609441841416010b110050f01040c8000e1242e1548510324008804941c00c001800d0940c07000050207002e0301e807c030306070300d84000030f40d01140a920500b01d17500d45070040125141484c40300015140c501003207134044110f074004622442040c0c13084114640007402070401c14600442d4036070701c4013030b00c1d0716407a403401046d006414821207007101d10412a4800842a03a6811400c2c1400000c0c00392244000040c2003020218807039003481448035800c0c0c0306011400464528114001c940c0080803403c807032401c01c01c10160000100b6080200e03003100403181c42001103100e20030f2a2402e4403d1a00c0c8281d01c074180b9080c0390000c2242c0c50801199020369450f4004003248400c200403c415207200c441e8122899040c02c0301e60001e000c0e05407143c05000f07600e4001080075595010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 951651205 1250 951649955 951649969
    0x3020a030e0d030e01110301050315041e030c0b070903030e100504050405040b010f0e07090501030522050f07060905030c10180f0e0702030306012001060314030c0f0f0714 75
    0x3006035503000324042c848101e6019405082450061802449941603038113201e007241c0001d101c1c0d99090740040d10041410354004403101d40c4284107074981d0320046026104520581c600d903c003200807441103000740043c81440b0901a501568514100c02200e0855800812003843d021038107014421000c031452815001d0000d840252202070010402c2d450303d8140b00d40d01c80340a2044c14051008400c002c1509102c000701e05124400940720070403d545080b004400500c4000c040d4913081e101ea40c40d4900099100d500740201034059801040301c03251055625080c042c00b40e20010901100e4a0200720985003c5034080d0b4040d07040b0f070844a200c3c031000c81035800720100302e10b42e20040103201000c244603821340d8400c402d461210700584103d94401c3c200b60398a21080d5080c44c003040c403c9100400070304441a40c50040c002d604008110300795282d440483d01d0b13610302c0d4216080c1d003012030f80c0440c542e4100704105038803032a00d00614041c4004509262600c840d40200140400c40300c007460415242c0360 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 951652455 1250 951651205 951651221
    0x506031e0603210d150f1a070f06050f161b1b0602100b01110a060f02040504061719023601060f231c0e0f0f060105150a03020a03 57
    0x4140c00600b14442030103126501030080c44c80a14a0b2580301c0001c074030316100700402d0b518250600e075004c070b061800480001441c5080d115828104001003800115034200c0d000b6214840c1801040506004004aa40c4600103024820100b02c084c00400c180f40e02108a0b6890246500148041070f11f500701880c2c4003c02c401c140804103620303880001c1080d400940c0c00c05030b003a8402c00300080031550004640c405148550340c2050f030b00040068000c203d295119404540e9450001880c06a99002280c10385109600951030400c100040c500408024082d17142c80400f03103d0300815501141c0d00182040c0701c1c00460002880c003031800745181c01c1402c1c07000c0c9090171209400130010740c0c1d1168020b1459101c1a00c0400065202498015070704000c0b40460242e580260040e00340707103a540010011132400548060260380351280c2e0601000144207602c5c48003101c1016200d14500c0800300703460000c06912a0340280500c00b061841c910040d020b42e0030601e2285005603a03000b403100700300c0c080c042030303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 951653705 1250 951652455 951652483
    0x120e0a060507020609060a09030c0506030c0a11071a0a1b05122101030f060c170703020d060b0706052401051c0b22270201032d05060108010506031e0603 67
    0x541d51f0540e80e000f075400003c8a22910f00c50080a4490f0140a4207010a03200d1a08060040c00100a209e008603810240080c105040707c041035582e002d4004c43d580c4501100351115000a110152681d0000116401302400c11020341002541d07a503240d5104059021540b4090f00810041b14003659800040c0b607510000074880c0d407658480c00d2078100c0c10301104044900c1441c0c400fa0403090790141d6101400890401c410b5162503807420020b80c0654010352140311601d540b00340c0800c6480303030310010b4208680602c00000c3c607032418503a80300e041012400030f40010015070710a0003d036a4082c04480b8032103071011400030f125400f0f4002c50050a101c0c0390840d848000c95000354600c1050007540d00110f8002401844548841e94143d04c000c440c0400000c44d15103844a0440554040d07002580d0610011081c0c1820f620350b0314400d01c40e109580d80c0400b690381c880313061069640e80f0100d183e015120456a00e851400c043c030072045c01c1c54400c003030040f074035004070700094490780c0610440d840600c1c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 951654955 1250 951653705 951653707
    0xf1815030618080a410a0c080c0d11070819020d050d0c0302011b05070b040c121103071a030f1005220c210b0607150504120e0a06050702060906 63
    0x13090702e0141c031a02e040c00403050a5960b43c83c07405001d0440408502d0842c09944110300030003016020b8401c6a80403201000500032252103680014050000800c05004080054a041100e00c02d00070546800d039011750383e01c4c0d4000711080c840c42e0004200c035110400c00100902c400703036043c80418264103c00c2005402e60260710305018140ea007020b22000c016100754000c20000007412601900c0d89010148000054014000c01001403801d0000542041c050f0450701300d060b585036034410241030701030300440b0300c019038200017030031800c0812910340603000c0311004942c03c1040181e0910580801041c11441803080004101082510f648100141001901c064002d100780c401d41410311100444415600d86031100744500680728840413032143d5200400c0c41d07502610300c03801c90050035000070155449441044901d0000d0141803003411a2400355101080e5460302e42860b18103498045240f4083c0301c800030520301c0030f50701c0307100c000203039041800d0440e01c4002070700115941d07000d03840c52a900044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 951656205 1250 951654955 951654967
    0x241d010b0a050303031306020304050a050a0507030b0c030c030a09030e06210a11031617100602010c02060103170708120903030f0c070201092d0f181503061808 70
    0x5040d04845814042a260850035550707078400d0681e60712007210240b070041984080351002844039001590000d01400c104d601042c03143c4c54640c141010210700700c80543c000b4104000b00040e01691035489803144684508624110340124814840102a0340301d07180c1c3c0303004a00402d8080c101c8841d15500141241c0d40702c00d44d00040701c40120824140400301208000068003512440c0982c01e00e9a8050002904640301d0b0244d0841c280c6110074054240304c00b0301c0146854456800d100b611074883e0340c0f000b1400c00c1c41e00c0b10107421620441f01030011504504014800308901e00a1904100e0910040d19680c07540c2c0d00f4407030454024281040e200c1e6000b6001d1200c0247d0003c0611302412960b51407058544651741140e25a10030420000d0100d000d1803402c0140c002104954031210140030b0400c6940350b40c1c96191384500780141c0006d011101090024050141c07220b00c008452014880204607090340319140d10860501444003c055585960400401411005113a407025901c52030807a1108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 951657455 1250 951656205 951656261
    0x1020615121b1c1e080408010e100e0c09040201180e090a0512041811120910060807050109290c150703020f0d0e0102191d0d24 56
    0x2240101c1a4400e10320003503076100207248041c900814560050503074280c2c144c209072000d03d4800c8001d060342d07644414880007c29810a0017803a10400e21500a440400b4000322400700300d40d09001e00041c254403d48030311030180c40d0001019080341d0242001030a081207548a040c02510035004002424000d40c1400180c100014410398524070a20503198040d4039007000c000301d0f0040344212040c8806440f580c4400a80b16442240b00d080040d02840c5050192103240d0030f201400c4da481500d66100303400000d00910148614000f03040603c01400099183c2000201040b076103004036024980c1e04016105280090f1000c0c46241c02d6a6200756111440568150744441c1032030034240400d00c5260004017128803038422900b10341c480010b11814800c1d034250610080c01a8424031f0341c190f50810940c1002d03080c50303004056181d200d6485042e00c9141030743d01c0c070b12104e100b5100c41c01000508009000191910f400d01170000003003400e140d205c44020b03541409480d0000b08403040e201d00180a143c0300d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 951658705 1250 951657455 951657493
    0x30e030102040819021f020d05070c1a130501050408120c07030f0804080615060f090a26010f14010e041106040f051c0510090f06020a080f0903090102061512 69
    0x20305d0007260342030740c0400480703080500f07242a503d0200040e04160b070206407090244001d0103519006c1c500d00d034821500c9444080840003a10a4a000702c0d42c04110f0881c01ca0a910183c1e0143c102860710a0900c0d1401403925a00c081144d030f0307920409008140f0545007602045240010341d080a03072030103444c44134142201c0d143e21a00803100c6074050311001955015500c000f03202d81d2000600400c0c5400343c402d02201103600108040c1f0340c03000da6540005181034045883c842d01c80c02125000ba60898000c1ca01b500312413080750307030003051800c00c041c1c2d03010000c841c0c00340d5045858421a041e8546c3e180e1401da21118002c0035560b40c0300001040101d0020141800c85054600907155070b14440c144290030846604c06a00042846e0702c5560404070020040d0010902c0c40d11071200d003034180c200c65840d80d09076049003147c1c9000074103480070048400e42c110801600100404050740c030302203d210001351103280080844e01c1200c204107000d000c0d9250b41242c081445200016507e510307915008114074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 951659955 1250 951658705 951658753
    0x309031005090601060306050d0305071410020903150123011710030311160b0a03060306060b031b030903040605090d02100305041202070f180902060d0f0501150c030e0301020408 78
    0x6a100f100c0020500c075010384680c2055800c0103003988401440b50350f044400341d00c1180102c070083e41003000c00903525420070028000003200c14000d86c440c0d4a40c0d041c5841c00c003411051420320085000100621000c0703044c01d0b0403045072000720002007581c1c400182c0302c640c90400c0903c5410100c0c01009500c8000c1010002580e21030f03511001c02002291310741d556440502a034503e16540700300c0070004004240c00030030f003141c91030030045801c656907103803041110010780c010101c1c442e0020070030039440341e50100030407007900040845003541007564402c3e66034044ca014940900c4000075490300150340c0c20007000c1c0d050b40d0080403c2c510651780c1c07000030007070002610b049401c030003681200f0404500200c0c00c0419512501c1101c1c207c203290010303800007080c64030095511265501143e00c00341c0c4035440144410040c4240210b110340312140b504089900581c40f0710703803d00c180e501108051794001081660213030546840d0081c8207071840060300a20030707035101d0701c0c2521a0301c0d1803181c130203a05180084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 951661205 1250 951659955 951659971
    0x360a0b0304052e051f0306050a05010b04060207060c080723070503011a0108180d020609060a11180a0b191106060901030b04050a050303340e040e0309031005 69
    0x110700d08411290100500f00c440d151007203181c508a501d0240045911040d40400a081042e040e0058905a0040da482ca03400c00d4601c1505c8204011945c111401403134010708400203003d1410785040b000940f034030b40c00d004000c204a100317060b900034030074418190f80866410804a0058410140c5110113041c110030f01e130000e90080480000f034624041c4910141c2c0c121a0002a2048090000459480200800241103001e41d0b40210a84550070000c0d80b01c45d03c200d40041103541080c5400da840c00b0001002c02492a0403c007241c0506923100301030b10b40c075201d01603e2001d5451a040050444030342900404260180401d145500940302c0c0403d034401c2c5ca042c2c0b20101102c81c020800e50311207404640d966001782e854801080018401d1300019400b80c05942910081c03003c0b644c8141c2542c1c4150b83c088040407034213192120001070001d410b009202050600001c0c4c058803180500120041c0c0c1d62188502e40e5400d1190b01041c09008585074440d00506072007450043c2d11018000780000da0b2019 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 951662455 1250 951661205 951661213
    0xf1503050c0a2d0b0f09010215010f0b030a0b030a0506010f060903050a0308092b080106020d080c1813020a140403050304090c1b050606100302360a0b030405 69
    0x2070a003401560003081e540740c0341c5038100709403480e80b0100e45004091400c007924602c018001508031381c0c2c1009031110b40f80015006039103424030300c002881e10500440302010b1500a0f4010004080d103200c01d001140d80a021992722940d40006182c020104c410116130940074400c1a2001c10401040c1d0906940070703201441a0340c0d032074a02c1142d8a034268007009040e5401f01c0305200100e4001d4245e590722640c0e003821103042d01d9110454801ca120200490316814040ca0081c804450b01700c040c60740034000c4c83c40140310807800200001d01e40340d40034000524400c40000c103010550102c041001341581d005d0600710524800094410003075000000c40c10001b034889002d082c0064285080b6401c80c1d8100004508050038181903100074003072119000c0610000100d0101c55001c0a202d010340c0b103001d030002e007038580380080600000c882c02d900f0720820180304102d120b421140d0002c1414820091030071201800c5c40c04960840001e066608850313200061400c00126509100021403065114005031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 951663705 1250 951662455 951662473
    0x170702070602060a290301020906070c030201090918020f03030c1203010f21061a040c031d071a03090f030408030a110d050405040209030c210c0306010b0906030a0f150305 75
    0x30030200c0c3c1005400c0c0080d4a00c0042c26640410b01c5c0d0703607028901e003004000510f03083c40322001504a9001010843e04840c202004109541c3c01c81e011704003c058030381003804806540d07000d9416211400304024420240f503d01c180a54a04205440e50b0500c43d0040302c4007000d400e4910307140c94100740305e415213001494101050444850002003940c1d182a207808a001c002a6207560250604815241c0741010680c5c011520750f0750ba0007008504843c0d510009030301d8401400314400300c0c0d00c203c00c020085d071145004001c01c50700d81c4010941c0c420781070b590030303129116811030030304099002c0300303640961002080224205030040010b00c00e40c038880e102e84070f214100d1103506445480302100400421814041007015080680081600c1c03800103054501c84030410000a007160401042104100300d240440c0b944d00c03104116007003481c0402c900800c150740c5403984003815480b030394901c1c901480c0040046907060009030003910b14103000080038803c8546030f0141a4040f4001d00c41541c8921490b007070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 951664955 1250 951663705 951663721
    0x706060e0c070224120a0b1c060c0903110d020303130e01180c0906030e0c040501080102041d0c040324180303050a0e120c15040f0c171005060117070207060206 70
    0xc0550804001e100160600c0101d004641703110f13500900640000ea207504964480d5611802807404406504507280c0c000c0400303041c684112180030f06130505100702e210041c000314443c1c407112851224112000b4032024451300c08170b8158082c801100300f46104010000c07440349850748403141038500701024030800c00400303582c0901303a0754851200f2011446100d03040c000c0341d12a0300003402c08044802128298520240841c0845100f644481000c0c2d42c042000c0c00000781500020a8005000d20540c41c40c0c10000e80c10312803442288030041080c2544852034506400140a1484e400c40905040000100c0000302c4401e00303000c100101c00107482c00340010f41c5d440c86840346026150081000f000d08404980c42607000c1e520064255115104000100f0030303980099240074401c1c1d106501400d00d5644901d01001e03400102c2c0c1000300041c1047c4c1000c42c4403440020071582600c1c540a01040340e4403201d0058030030807140d0046441500d4501d04020049400041c3d8604680b0194200c402507590004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 951666205 1250 951664955 951664999
    0x100203070b04020f0f1002060603010509030c060a1d06070c05190317070522081612080d0609050115080a0b0d2405090f010c05041a0706060e0c0702 65
    0x100041105840d40701003000340c2042040e0f10b140d00405448040d10100c24000aa06105035040400060b4041020040a403c0c00e02900e90000103040045041502100c6416201c003001082c10485a5845001828a148140c4a0f0302c2c03084041056400c00d081004005000c0c1001f59015141e602c00c0025040c4c03240310000d580c8003201e401d6a20032050080c28003159a40f90405481070301080018440c4040a8904401e10b4540030410b00c50030300c1e002c3c03a1060040c10a00b10407030090000b0306c43e0100704031b03102030305030450381090f07001c0020f90742e5054075005040284241e401200320740d881c1400101d00103010485248a84542e030302e4203440c81d41d481f4041015580000354181c1c000a044100c540059020315600340304008800707002c40030385144010312003100c004a46a0710940e00500242c40005400e109404450f483d5140a516242c108180c044441ca06403d003196461b00001e543d400b03003c2c0300d9010342d004d046803014840799422704410754012604000000c0e4460340a40f4075201e00480018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 951667455 1250 951666205 951666217
    0xf0b0a180c090f030312241a0a02070b0c24180f03160804090e160b04051f1205010f141e06070203190609060b09040507030219030c0b0306100203 64
    0x50f030b15016055030340c115a0000400540f1030016107a400c0c03d8002c24810706034410b400640f44040c46202d2a0080546401c8584e400c030903040300741080321041c95917002c0f604d54241c445401e40190b6034134114403c24a003ca43c024080148040b641c1d0300d030041032040c421207008003000c403802102e4000c1480696210b0201e5102041e50798420805119000c03148043c0b40d840c28080c000c4603003403039507a20046058445041644155030800201c0603481410010b07454007400d0309801c00e074140f50406d004030f420800a21805445848158104210107200709803280385242c1c24541404956591000c4080c251003900030310480d0f0b07040c0c030500274940c240040360b265000728209560242c100d8003401c0c01440d50004505a81500030f010380d100710403211640f100c007418859180010440180e06100044660860884d4826001a41800701140c8000364810070b40340c040b510030f007807050013801e0000310401c140d0005103060011f40b00000c0107005940035610544007514614007030411038504984130300c640 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 951668705 1250 951667455 951667469
    0x19081c030f0c081906030c0f0501020f070f0e0a06031e140f06060d020d0f0b0a0f090b0703110c0706020a0b06010315380d1a060d0f0b0a180c09 63
    0x1e440003c004c00f0054a5020f0003403a50b07800043c80c65107985810b078503001c140d08880c1e2010004031003080ba5580c1007200b207084541482c06401c1e00e605103081da903100b68551040c0c003440c489400c08942030390507070350140700203550010300243c0c03030486801058400032002d601a203440d516a000391254050114086583c03134802d10103803246603075640404c0284203da420070307a0010301e046001c0001804c3c030401801c00318003c408a1400740f52559200c000d48500040c080f07003290a220940c00000c0060309442c3e008042030902040860000c510222540110400b440c901d00c162840011101c0e00414003203030403070080441d401d10350303030341001581030700c200c1d0174802503030112444104541c0003044004001d000066840c0c034501c2c0800b00800c19070303100700310b1401c4011078001412001c88219102d8800845a0700d07180d00c0d8059100e00009185000e007801e6000e01940758080d1042440450780000150a0000c09107803105803a4800c0410020050140d9540b007407400d803110390a1409000d2000480d001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 951669955 1250 951668705 951668717
    0x114120609010905070f0c0f0512070b22060b190618091a12030c0d1e0309050303071b0b0f01030b010b0f0a0302070809040e0c1011070519081c030f0c 66
    0x40c581b0111035007102078405880391085000ca83c0009001031001d111005105100c00d629864107003810314010a025005000c4100041ba4007050254080b07101f81c06039420000c0042e4040c05400441e00005602c401c5140d103103c20240070030044d8008c48041d00c0181d8402c0c844001c540c4a2500400304c404030405902c40e00d40300710380d041c014070b00155a080480000e009803030801c0b4168903024900394003400c4403004a2194603000448a2001c0028558078521349410301040605072142e0b03807039204c00781c00c2e031003013140d203003603000c00c481e00c5101d102e44042c0d1000c0d8604091500003c0100003103400e0204036010b8240300c00004510081105582d07501d002050b005280c80d02170002500254000b1200b00c0b201c44047c000d460040d901c034070800f5036550403000034080441030002000101c4070001d818505120051070b007260800c6000450b98103031901a02c0b4401c8a40031441210807003180ca070b0100794a1f1091407862031901807802c40c1c0052400207601c017072200360f00c00c8800c2030544038000e02e400c1c00124 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951671205 1250 951669955 951669977
    0x10203090d0c0c1703072f010e180a02090a0305102306240a0324180c02120309010209090705090d1106220305060c07020d0b0402011412060901090507 66
    0xd1382c401410a4411020499190080503170f10704100c080310300c46103101c00482484000805100b41c1c2800d01a040901c2c180445010b6000040c05600c02d01e910b2005c074170701c00360004841c3e004070f604803010560000c00400c2c2c40c076500d15140340d8a400304600b10405506148107046220b20450b0b2440715006603440c0e05206a9a000610034201c4d20462041011043d1240d03000d0b4202440c030081003401c8690f0740100e407500d59541c9490540c4c190b500000e15005c2d11701400c0004500c00c05c0e400118449500010840801541c02249081c1c0314403041100d5503c00000e00562010550041c00c0c1000c0030b030b86900003541c9019003900d10b4040c003400340b0f0300041031070301c9140020451540d0b1081e154000b00582c0c182440d41c070030480c1140c001034200c00f0481811805206001d01040910740c4400c1a07583e41d4902941c43d4040794040148081c0285001100c1001c1000c5a000e0301e04c2c1e0010741319000c0815103540f683c1700e185d0855502940c046000d10213031000819801c1d80b90142c20f2154049454240f601c070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 951672455 1250 951671205 951671219
    0x50105191b1b060c020c0a080c01050706110d0507200318120f16080708010204080a030f27050f01030b09132303040f150905130f0c02010203090d0c0c 66
    0x140002d1940710050511101c0303040020110b01c681070210381e165004081000260302403101c4500e59800c000d0340c0d540714002c44020307680c0c010700300d03403050364091804140001d0914104045008036055a80c0d0360341000101321405602200e1400311103950760b6000d4144044181c1c15071640326002c894400d245108a24040a05040a1001b09030141204496014280203591802c1810940d0125902481c40400b04204c00301004000060304800000710314180c07618481550340d019a400060501032901d40b10300b02103010380445a1410381609901c18500e4540e072818085c00428040c640c8142070441e107100b0b032540700e1712401c0c4074076402034464031254440c2c40c094283e081d40400121520404410140748108018454545131605103004544403410481d641c11520a940c000580b201240c1d103002e8006513000c140b40c8200c034070a40c1c5400690001002407070203404204c1142004500701514950041e505500a510070000e1105aa01c00c480c0b48400300c0355001110005403c0641c1c50307000380110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 951673705 1250 951672455 951672467
    0x90f0f030f080c07140a0911070f08042313141909080c070e0c070c0e06010903060e070501090909080301090b010302070b0a05060f060f030f090106050d050105191b 72
    0x1c901419015007010718000d4894500103254102c40c0d00b00081d01410401410109094400f0707140c1481c043c40480511300303044210740103034000a0b061719144074407007090003240000c580181c41409001140c039000c02e044a03411890112510b40101c64400c2c400d404401d803881880380220844441c4105522001c5080d40301c030180074046e044d032503551440200003550759001412006c0007400904400d40c80e1821180b00010000c00011b1003030800c100701c10000e22070952807419204030899108464945c080101c07509003082c0c0004180d203140007006182e014002405004449090707884803451a2250001d0742540c1e00030400a20040341400103010283c0301d9013104a42a030185801410070009450b1400e801d5802d90b1102d009590750303420b0000e142086503081040100c00c0c2c6520340703030034640c2045c60b9491000400d20900520840c0101e1034485082d044000180401055900e0031a8103040c094000d20058800e8941500748122880410309140504070f511490020641084401d0280c01e90740 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 951674955 1250 951673705 951673733
    0xc0201030e160807080c28050d0501020c070f1805090a0218160e1c0f051204260705060721090503011404021c06020c100903090f0f03 59
    0x1850380301e4480c81080710301041035004181e030501c0c410214074a08200b5604200950b0806985500170070701c0401e07070362142d8841000b042d80c149072040340c1d0a80b17017919041141c842c0d01701c1c5900141102500040c01415009048c001080400391000c0d986d5a40d48a40300381c05e24803900307021000704265103601c8469540001e034411040d100340d609184e1554002825a01015240d11800030036209112052000390884504029139060248007081e009000034001c03d425508001390030900c44030001000280480348880b550b2000441d40340f400c078248503a87c2d90b0041e004045581400c0142070740320035200c000d44e4800340c85c031101800466042106018550788030b05815200030903200b1900361601c00090f44400c520880342e072490780045c10700c020582990105289200e460000100f440056915520344140181071f6a5404095501a140020103802080c2d940a141c1c0503054041d41040c0f1160004400349120307513100711038036448000040c215038007400781c08142c4444043c00d1000070320366042146 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 951676205 1250 951674955 951674957
    0x1a060307060f02010212070203120708480307031107150b01180801051504050402100807020a08070f0203150f0f06040603050604110f0303090d061802120a0302101b0c0201 75
    0x2c031b86225000d40aa600d0401d03209000141d200003081d00b0000545030b807003a000901c2d0f00d00340041c4c4c2402268403549203003014000012150344203107150109500503000c0c405000c44816407074000781c1030380f0b1603049802c02c50705600403a0030590082c0d0038420740821a000070340e10840c6d1900440c4465070f031a0080140018060510180e103c10785800904500840000c207080d03000803810745058041c00b00c00c0921140e400b4065410401800016070b03602d014000500c405d45059407041c1d49116089140140400d00604030340d074000750030020300441d10410341e50503000340d0848918512280b0202c0b80b64070211200720f490071414003c12aa0b800360b40c661500048010700200b09642c4a4460505090301541c0803a07001e8150900b000050520340314560796644124007441c20502c034000070580d100c00450300107008a94620191180744115004810100e401a10444012440207405940d4024503030058001d48588203601c142c00f00d890003041d401c10342c1202e4602c0c0004080400755455428145c04034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 951677455 1250 951676205 951676207
    0x3030c060c0a030e061003050c09060d0f0c05040f090c1a04030b1e0903030609070e15070218040f03020f0309010e1c1401090c150e01050d0e0a08071a060307060f020102 74
    0x84d0542c0c1c420030005004480b8010104102440c1d403a145103040b001e00c80050007001d807081008281e45c1c6003006205a00d4014403042c50303414103440c06d20120840350b005140c0c040e14080c44c22501c54901d82c003441f2064490402100465190807a081006841103a86101018200018400101c00f41c1900d501b100e61045203090010304041c000032040021200d20034103920110230440300349025080700741c000c2c125042c80c01d030501110022845810807e004a4005100060088110b450b03030b40020100340d07040890030364980ac06141200d40c040191a06070700500c100d8124000211000c000c40d640924140c6400407440c1980040c03100186049041e03003180d540c014000b002140b003000883c0400f10042000280c408043c0c5096686420190009905c60041a040704055900458482100c0c0006d0810b1a02c42080000c24001792140040030301e094003d1781d104e00c080144030006040c6c2da03031081058030140101d61031814080b040c1168201d5142d07102d0341c0e0400c949402005c03407a0b00f2000c41e20000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 951678705 1250 951677455 951677471
    0xe06130213022a0c0a0b0301092d0209030607050f0304060e010f0e1c0302130e0402150703080a050a0915110405030a0b040506101a13181a03030c060c0a03 68
    0x91a80041e10318200c4001e00c0c40c801404410f1142880294010402140e420080a0526240c04014001406186d442507a90340404854422820035610404103485015003d584102040c5010b5040071004901038410b0001007100e850062003501c440290009a0f14255a10b0303482d00c074080c081c02c000841d00e03035581d000341c0341d003500c00d5000f0300035041007110042102404000402a0180c3c030350a80c201014418000701d0681042001040100c400b62211007466854600000d152140010841030b03070b180c400078141e8209504410700c5440380c84400c1c03041119540780c111400a54480705002030103400029009208801540c0c812010607896500c0eaa040c0f940ba500840e1078003010401c00e50b83c01030200204000c02c0070030811140d03c84a500a0f02d01428908014041c180c00c429040d000400408140d51294940040c2280020001e8050088801c0007001c6000005c00a416070703010a080303010070f403e845013800421200342c0100030380186800e41d194a0828a2508000150380c100b580310020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 951679955 1250 951678705 951678727
    0xf190f08030a060e07110613020a0815070305070905010c33090209060d17070317071e0816050d0b0306040b150a060f120f06180e0613021302 62
    0x6544a0b03032520100090b082e040505844207060700910010030800c004102e040700b903202081c000d4005d44200d0580c0307101241e5200141124880e80c000d40c11511a08400d4442e05a015103020b00501d03003074408000035141e01204642c800c419029043c04180c3c0c1101420008032848580790390078210f61500040c015070b10140c01022039200201905042c0c132800807105621300b200c1c05a4224804454288070710415944032860041c038180c140345204c0c070100b442028980a11242a42d040b800080201c540c50909005400c110102e151401504100903a460354680640c48242c056180319100f81d44010700b0110481c0c13158400c1924001107601c41c0e10b5404c5a480400485019a00c81c940400c1d007881c110b0349048145a00b049070510554004508204081c0c200321100504041d62606500c5406072004040107040c07210580c422741494444001000c024000d40165001c0d4101c05c24440e41641008032a9100e00640e903100c0d0449007a00c0038401803818040748010400011400342c1410341c0300c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 951681205 1250 951679955 951679957
    0x100503030a210b190f170d050c0309030304090e160e0a0e0106030606030807171c05070c050d05040510050408060606130e070302090901060c0b0a05061516030801080f190f08 76
    0x713070020b94001c00b540140312111485158a000e40400440c001a0280c420046941c0d10384c1c0d803040b031007808800600104684002c1c82280c6c0703262806030449a03600d683c0d0000100408030309032014694068425984201c010041c1d008007100c3d00749410b201c2c1a02c50070030840c01002c003e020300f841596205400000130703069004030401540600300d0191544000e0420000a40760003e001000c04410404008059522000701d040c3c110200c0c00001c04c3c0d55005401c0e80e42004040c0301820600c0707800054140950701100400603203100382d81c0b1000310300c00410141c035140a43d020740070303951304600c000400030304020000c2d204140c5000c0c01d440d205599816143c174a1002a0707500c1f40000e400142c1898281016819240141aa4903009503119003c0e265282c02000c00380c0803826050f10354001c9031003a82d03180d024002024100c2c1d101944e0703480b00c020400c10411030316012000b25580100005404401091407081020110041c100d4119000030740079043d0164101120b8032079800c000c1c0000f00e09180c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 951682455 1250 951681205 951681229
    0x50708061e0d05160b160305090103110309060a0b060c06040213110d02180a050907030e10060611070801050906070f090e090c0306061e041104050d0b100503030a210b 73
    0x12000c0c001140513244106181c0e402a04840e004450400c042a04c0c40c00d4000480300481c0c040c58540c1c0c84103580e0340120090f103410702080009440220074030a003120040b50701809282c1d00f44080000351151000e2005c640200d1140141582000e400940941015851070301e0301202048002104118100040450b82200c1f040141080d808a440c003c503440c0443d5484040308100c482c003805501c0c1000085200200602c0707641095158442c5d01c800700000c20642c051859640003d1140f2515140010088090030180c041d482c41644030000701c5940c1071041a025030a07244c05000b803a6a00d5a007030324192041c002100421000640c0020100350044e401c50082210300c1c00f0b44045c4001104052900700007604192041603038001d000d092152554049401400564020803012003046070b03074409014583c8295040044200300004200d00c1003c86071050509842003400c04d51a030052507903034051284c2c0349002ca406518071000c081050041100b8219165902180b590004404180303108a04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 951683705 1250 951682455 951682463
    0x60f0a0c0c05010311090f0112050106030911040c090e0403110706090510020f0304151b210f020312130212030406030b0f102727050708061e0d 63
    0x1105054208070314024490000c00091905100c1c4040d21104044903100340480144103441c42c5012910507401080245641481c40300704000c1c0d0340c0d403150058080e00343d1650880b001d8a820f942202c145c40c080c410660b2010181d9150030300c0350b00740a030841c031400015009a050040445001c61110300800c4088064a46540c0700d400702d52030402444614404040a030302175400007090854800c02c0001075404480011109007584950210203a5000c019061582e01c00d9060f00342d071405102102c0c2240300c5148540d13400c1111320003075140403109007001041441c0140c10800a03100d10312500e080e480e4221a01100500d5032054550005041d00c100c02043e4810b5000481d041264640600c640d0302101c1054800300c55050070500068205a0645810301c1800586892070742e006c1010701c50b01c0b280030550220241541d84a010005003140781c800c2c80d00b00e050b5044031501c80040c4501413580139241d40e4550300c806450315001c03c038000030000c050807003506049504000300d079510050f62180d44c0c02 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 951684955 1250 951683705 951683717
    0x10302090a0803210601020a03021209041e1505030304120209180a050f0c1503010e0411030a1406070903030c0f1401140f180304030611070213140a0e0c040506060f0a 73
    0x6813107040c807201d4000a040c0b9040d0341003400408042900401e40304100e0100c0100c1d56600c1008200040040064218049036070800c00440500402e103a4400305445200b0342008d245103680300c00300743d03880c031950059080109000c0540710050400c0b828090b0010418076070141d40400d812041031419004c204140c0303090744000e2a0346c95801003444502e500c0d80301034403102c50004940b250070403a40300c10300c102c40c0c030284118000b400b40500d40c1025000004000d00303880c1c0010b10303400c00413050100b03801c0306202d9010380b00126805a004000c80001c490303142d00c400f44d403407031a40c0f101003e03040141010b803400240b400c2a00c443c20402c0c03182001842c01540510450b0500690004003024010a6000c003065546415142c0090000a9404403503000e03a0108a6010142e5040c1060181c08002034111044441041c0d1005107a00302c9907014414140240300b65030b40a0450702656207001000b1882c4c0c01a010102d01c80c2481c1c1c201c25403001010f00760528000040100c0250360f40721000307203000508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 951686205 1250 951684955 951684997
    0x705090117150d050a1b06171b0a1e0507050114040206160f020d03170f06060f130f090c02060f06091302010c0f120f14030105010302090a0803 63
    0x70300140740181010216101a405103011251500702c0340b80502142d110721000d00c06031003004800c00c00952200d90003e801d0b41e001625030300100040a203402400302185040c1c02008404400502d032a104a2a6191245038030f004c00340d12031055030010488070204940862003041c48400b802c100d46c20324103256540ca5a480490821500b1900640c0e10107107100a00000e003c0503a4580c820744402d11506085890b0310031052a0002001350782107002500554944180c02c141070b006008465030b030854441154030340e90341020701c51003090203c0d915903122a0900181c12885206000381502100c02030041c4002901e94030041d130441da0540c4040840c5488a003801d00781981400120741050b0300c40086812400d00800161007440d0041601011101211070a419a03218131241c503003c6070003214000b510b0106007090001d803c03001a00c4004074001044060f2500c0c81040304100c01d9480c1003c03641540d00340001140070b03601021106910840c040d4000c130752084180002c082e40c8056800d181a410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 951687455 1250 951686205 951686207
    0x18020c3c16170f0312010e09150405061611070308130f03061a090106050409020a0c1202011b0912080901110f010207050c090c031306112b050106050f0a09090507050901 74
    0x82c1c1d85400043c4141c009108851044002c059068107641d081d2590007255501c400082d840d00359110981c1500400d032078207010a00c5008a90b050003107130300076000b0340072088006054601e0005071007008099845100108085414040501340c021b500000d0407a1507940c8030712200b00350002e0b400541d8150b45e01d40b40d10701c0d6041d140c0c159407004c0e5400d0b0b510003081c0d8509600900310380035601c22061082e400062103086c182c81840060401580075480145400c4030300d10090080c90980e0f070700340c0300200300c030103a070400d6004d85444422200d1175410045204155922110b20341c000525281c10710a032040128201e90060103510005005200011b071103080a0600502d80128003401c140200340c0142880814980e44003100c1e440034400303e14080400b01071a06500925551110030f1480c6000f08100b0075401504000510106004400c0462404400f003900700301e41d000e00c221004510300700502a132590450015003441e030320700d042c40d5814541d50b4290300f055800482e5010002000018018515 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 951688705 1250 951687455 951687463
    0xc03050c0f1507020105070c030c020f06280806030c040e0c031c08060f0a210209010801020a120b1807020708070b0a08180607140418020c3c1617 64
    0x200f1001e10081c800c03401c0c0030314041d11640313600f44040e080200001c00d000035521418540103032014042c2c03210f07075070701090180f2844808441880b14104854000490003480c8140601405400010050540304041104000040000b40b101c00c480e8000d020402a090740c05000100c0b01c0132220104101260461400070a42c240061a45100e4000480c00b105070b03446882400084c2d821003400e410380c0c014814290074a011040740b0081d4801c9100c0c0c00415000410340181c808030000e500c0d503c01d82c102d20f607909410303035030807031060740c0c00240c0c0307a066007412107000103269041681c90058034540398503265021b041c031a8507040681d040d00b00003807030320509600c00d1700d040e0700010451030001e0f50084882615190718003d41400208490340380400c030318040708000c0780c0003001801c4007411003511a28094010750401079900720140503189d0000b903140744280c600b2040d08590308460713455640000340b00c0420102c030a04064584603021000c203550b200003142401a01401100c9540d103074181214601d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 951689955 1250 951688705 951688711
    0x270f0314160303020c090c0c07170f031204120c0501050408040608090303160e01051c09110d0b0a0c030209060315100c17070f0f06021e09100c03050c0f15 68
    0x80c10101c081011950215103181304800403220b01d09207480d40700c4200600d01560f01002082c1c080c0d1440007503002c2a50080e03041c194002c0c41600c160400b000c0401e503c0b4002c442c2210b00180b183d400140025200342d103844854262401c08013514804c42c0c40700c6c0d003103460031103084860740c0300050107200c0c09401440701e90f80011110300951443c0350445c011040c1c00109050315050101c10740000607203070301900645202c081d1039004140c0701505406110050318102405a484200c15118070a0360300b4180c0200c0303c11138102c2c2c00c060181c1c5801040c03100920016842d00c042590a0003640c48a0391804000c1d406030041006000080d804031003040036408070058210180030700070000000040c1121120b0840d0018100010307260035082c00c0401c1407003184000101158801400c1604001c000d0f400b0782122158001000e4100d1055900c5286a200c0d00502e5684920f40c000e0071800b4501c5000841c01d183e20030f240c42c504140309649440c0c504000b124420402c0d81007180602490a03658904940c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 951691205 1250 951689955 951689983
    0x60702450103050a0311011112010e0604020a050f030c040e1807050f031e0a0501052404060b030a203403080403201e0f070501270f0314 60
    0x240c0d501d95910310381d840881c01c40c000c0901a0300724103848070010a40c0305140c0340341c200002c55a104808010070041c440240500c01072040c160000c9400d0703007864400d030752442c020794440342e00d0218bc040031108607030001001c82000701c00400001c101c4011028601e40211010f6491940100601d10001d040034003c1d0030490264001b2455100965030000d000b4a41c0c0f05d004015540c0c2c0811400043c2c24000c96400c060010760901007801a00004000c0112a402c4d0040d0001000019036040100392122441041c3c0e0f254800d10100b003100c0e0302c550041141000700080b40e4180c0d04c0290b00114030ba04403200d4415000880000d48402c1c40041611004021080b00b88003c012129580542000809040a020443c3d0072102c0040c02011a100403152095001111040501c001340b0380d0345034440300aa81114040c219010703900070704c001030035420345905031240b0403407503502c0c0d8600c2d91304180b140c580c1c42058448080003500b0700441c490000554018040300614000100a4629004000c141c843d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 951692455 1250 951691205 951691339
    0x9030c240a0c080a180b090a021503090a0b0718240e0607080f120f1005030a0b060f0607060e0d09081c0c1110021c0f0e060702 56
    0x14010b6600c810b01c01d610521050002407601c0e2003450b0b140144000100040c9590640020301c00c1c440000035410890920807034012b8040305440c0500c0b20540010f4495594684c8a40201c500280c0c220500d81e40c020450700e0508030035a03000000707031245840f40d0300c00d04840c414244098a0200001e0428110222906114590b1038480c801300b440d91003402d80103060741c4008286a4450600441212080a000c4202c03444d17900304001c103114008800e40d55091641c000045c001000e0902162250200d070f003003907086183c0d90700c110034040d1265107400c0b0168000410810074000601503c111044071b4011801031000b0100304001521340c0b08607411500385940004031602034849045089560041549000655900d50746000801507500180460780024000f1290640d243c5c0040e20000090340f07014410207000580788143c0381460341001070400117200080c07201c02410105e004244852010300061008805020f1034601d40000034509a5046898140010f9a240800c40f6442c0210495002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 951693705 1250 951692455 951692471
    0x1401080c030304030615030b0a0b2d19050307080f0f030702030d0309060b0a03060903030f1a01051605190c09020901080f0603070e07050c01060f0308040302060309030c240a 76
    0x181d601e010f0780c84001d01a40c1c680d84920558110f43c124000103551040c4155181d0030300011040103810150041d5004d00500840141d1400070702102c0890341a030a50282c4043e6a0142070105800c46c545074071004a41c200320000351038800300a2100280b59141c0036000c4210482c0300c079410241c0ea840300040c294828802c98000d6039001c6002000e91509080005840c03015180c0360300903000306006c6562125480400000303100c01c3c1d0704034805e000c0c0f003594200300d0240c0b07019503481100e20203c100c401c030084080ca0300e002c5500910080070324291440d01160060140c1d91401c2c94900d0491a0f03005071066403102004000b004403141c805880c01050a5040190110001344a11002040c4074444800400419515101882500c02a01050104881e0340c0b510307010141c801d900034075489001e50310f032800002c0c4440078030f451541a25030007030420346030070b1842c0c00f0082c0903000a01040c1080c081001041000d060802024102d10442c14071110041c20b0080c4041603460002c02c6420383c54140481 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 951694955 1250 951693705 951693709
    0x13020315130c080f1e090a02030d050a02010b09040b010501120207020405090a1202030c0619090b0f100f03020901030f0c080604051c0f08010b130302061305040c020a0b0601080a090203101401080c 86
    0x400302c84c0841c1000c0001c1c0651b6021a604d00c0c21864001c041d4140c06400c661090580c0d0080040c8183c5455030001d110720250841400005c0c14110b90103040c0400050040c00070750311881d01c0342c00340364070f10390050b041c0b05c5650002400c0341d0041d1180075543e840b4044041c20800c8109640c80701018a001445c244401040101d0b10303640f009007003030211000407400004088455000300b20790703500206404e40b24909144080310088017a5980e55070000301d000d0015148031014040700540c3e6000d4400500350b480c66450307003101c4010000889541d030007024007141c1040100308491045006400800c408a840410000d180c80e21403138800401082030a90880300707803c860311904407400c1c958180d07690501ca00440310200140d810095204000045400342c4020014020080d145c0865080011a091400584c0d9540c40b0b500020003104c0d4242c0060030660098110320f6202403071440124a52032a580001d08181c06d40e032062403450368450318404408040c2e03680030f01400b002d030010401e10800c070340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 951696205 1250 951694955 951694981
    0x60f0910170109110d0f0606080603010c21110a090302090705030f070806011101020a0e030f0c0117040501060b03070201020703030c09060c02091503030406091703030613020315130c080f 82
    0x30000420780754038040c8000d00d0703103d00305c5110b0001d0560030485013100b00341050182c900d03445154006181c8601250f0b26103010b00c124040305505071180b15101030b6901150441c0130700d040b884030980b9960884580d841c1c002038003c107240180c1c0e039211304026007944104698010058000b4041000a20402114071903140b51240c06c00101d05141747c0582c0c0d501300480e45c01c0d90286e10017411354004200c2c01101c980160641c650700000b14151030300e05603e44244c030f540d03010b030400e0303030740007440407843c60041480c1d0001c0c0c260003901810000c0780e4070b5103410380030f2810b46c0f080c1c940340c0040c0e6001400c0b6040c194540b0035001c0260341c0d858180d566030b140c064001c0c0480d101300c2010384500400008038018204546c6240700c6160081c00ba2911980e503210b01030003c5000b441075030700c5203090340c00c203190501000c82141e101d2070740107008200c0441192000002504001c00540c645803200d50f0380000d680d209000414ac0c0c1144110100f6664000ba10040c01c000d00508100217030001d0340c040c0300d00005102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 951697455 1250 951696205 951696209
    0x32d04030804030f21020d02070902121306090602030403080105011b02013612020102060106230705030715150e010b0f0705070f120b1f05011d060f09101701 69
    0x281c3e0601e1610b2a04204025651010710101003030306001c040c24500d86c02148012600b132280e000d981d80d80745d07907224483c20f0740300305030500d900d080c071803c002010b0316a4140c007907010302c0c083d000000c4d01c2440342d6a99000c070b82c0f0a940960100c0c01e01c41c010441ea603441849800400b4402189059205040e070010b003540080c1075003000300d940300ca61104210f1690500c141246004042c20300199951040c1810000391802e80503070060007041c0c0046032103802181c40301e403ca44802c80305043c2010081a000c500c0c1c10582040b5064041000142d010940101e500c52140c8050400003c2e14800141e194000c40100c0d84032151903014140100700c0344c0041015150703034943d401d5a01c1c1d070f030f14824507056040102e15044080d4505c043c8402043c801c481c5401515060321944e0603130880c2e19464412000b01c0d032030b500e2a1803c0b101c0b014043c05254450200c80441e41c613148104102091040c0c0064015042540425103220000c540b0300307a145071900740c2e0345005145080490313452602c5c030104840c83c4414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 951698705 1250 951697455 951697463
    0x1c0b031f0f020705070b0405030c0105040815280e0c0d0203070b160f11010f030b031c1806020c030c09010509040f0c03080a0503060f0a082d032d0403080403 69
    0x8485801044100b078040b9074105030311200790390300c0d2929120032800c02c1d00b290013018001d01c580300848506500590444064030040001030950314419554926401c000a040001100008107450212009040444001601d00d1800301e00a6110313420303980391920b6851324900c03c8411111010250b1408540710781070710640403078075589010202c030f100020401c50700020700c240e04107801310341405a24504400c0442d800d0740c42500a01c14000100c040d2212a213600e581038010740b032098036504550208040c61030880c01d00b90b210031320200c04001c1848c103652105025030404402c0c1841803a0a2200300241c6900b11207019065041101144540c2c60040009041031101880c0e48184603d078403860b402154000303092680c460f58100018920b400941d0103d01801640c50b00c0c9103180703084000e110550302c0d00c0f070043c030014403d0384000d141e003038074107004501d50151031003c518640f01c01d1004200f1200c003500b8140d001e070041d4191040c10078180102d0342c414001030105000040010044508607900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 951699955 1250 951698705 951698711
    0x7110607210212070513080304140d0201030f1803120c0507080c0c061303060f0c020303070e0a08060a05010312080402060a050c030d0e2406130903020f031c0b031f 72
    0x5007068081c0280705024181002c003984100300010558080e008108116140302150042c558854284c1da6038001c0d4001e8804c01c0c28000d07c40701303583c1440011034203941e0051402180d0b04004000100c2103500d19800c0002c14507000d140c0c0344c18181c00018a0b0140c0b910f00c4420080066441d000901d14012610020440c030400140c1d09494038003003091542110b0020100c42e52650b0900c100c5100110510003180d4260a000e448010b8a21902c540b07584a8407a401031803a44c0c2c0c40d06011503075440d80301c52043e400ba41501000ca002001044a075105500600c000256035040d42408001c0070100c0c094413041102440030407006803200c209641c03482e001424065151680149101d0441c01001c030008031a0785002c1103a20b085074002568116540c01c6001d801c412408105401e041110444186400150032000074400d0032581c2d01c00e02c02c3c00e0103032040d2090039041c181200d045034003a100c004402003181e903860240101e144a840d0010fa0110020828040c40c00145c0c4248a00c2004c00301c08565 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 951701205 1250 951699955 951700007
    0x1e0f0103030c2415120201082a030a0e0106051207050d140d0e0f03011a1201020f03040302060f1501020d1404050d0c15050f03040611090a0e07110607 66
    0x4000305400841c0d59150750503003d030b80ca620024038010200d0882a2081840d072860003c2c0403a03245031455200350301a034441741c1a0b6102c1403c2104004488682c00c00f01500c45403001010b007864002d98020741061300040340401b03401c40c0310380c00e441e01d0703400040c401d016800b1040d00120780011140101d40c01501c0040450380581421040c456112541c49864080c0a00030100740b0b5010f0021030b165101181c043c508088008180f5080754403610382c040007041410501495858a08070002c02c64408a0001d441e02d4500c83c1160300513001030ba82100075901c00c40511803412040320002d0782c054844c01d02072403401001c1e00000c1d6140c4401e44e5200500480d61004400b20255004840c05060080c0c1030000c41022460001401e100c0c0e44640c21700116108120914940325030100d500d9201c2030030b4400d00319102d9450703100041c9401c40b0700ca80c0c0401c0802c02000680c580118201c02081802800c0400e403500e21409441010000c000c42c5107604404100035000760084440d0810040340382c508000d0354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 951702455 1250 951701205 951701213
    0xe03030c063c0a1d0d1403010b0405060c0a06090f1202060f040803070c21080a061406130e012303121b030f0d020c210d0b0414010803031e0f0103030c 66
    0x500b4048080035500c02c0d1500071100b80010b580445c0000d65551810281010110810540000c5c0142040d4075010041003141e0f1509502030940c221064064a900034455070700d08080b03038180881243c24180c003612007820f00c010000e800107200744500282c8140e00d010244215603180c01000103150040100202e41960712940f1b5401850340c1c40405406000c2641c1038022260328061100340014824000084850141c0d0140200f164034140340c000090811900300102c50304021114144001c054000240244481c810700d402445a50080001980440e41d1b000700200d01f811403074000c0e0300c44125680c040e4078600480780390b15601103400e040404202d03000e0707095110f0500c0d103052900e000b00d40c1000200281e8010841411410112902c408050600f00c03141ca0310881d151540000500519901004941104504a000030000540080a400c69042c2020300b0f030000340140e48048100300ca0440031186880d40c4035400c1c11030514529100794010311015050000a0801041001c1d507030801c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 951703705 1250 951702455 951702461
    0xc0f0c0a05010509011a010e0d02010c051912141318111b0607020609031903091e05010b01110a02040f02210708060901150c030e03030c063c0a 63
    0x12581c030000034000c2d4145000301da03004c0e01681c4c041303100715081d03150010050340c010f050041d4101d04c00303403104800c001c0680064500141c880d02c01e4800380910584440ea610300f04c0400c0300c00501c1002c240384180d00e4401d000b45000d81c140b0b1030b070319042002c02080c648035160894060840d04054207000703000030156001c0b00540092001c0310324111002c01d000320f223180c2405200e41c130fa100720000c0751040d9950000490742c8100548024190790010010510f014404001e4074011a0141c100440c410f043c669810f0181c0d040c5212450900e035000d01c001081141c280100e202800342481c081d808507403041007003520f61261240c0240304980d6020007009000c00754050380c0c070388082c0503600c4030010b0038010080f00c4913004454200c0000e01c0080003070700760719000422174161064042071142c40e101c2041c0a40c0c45035083d0300300b5418001d0341c40306020650380420082040c24501b602400c0c450421416070b42c2c2c2e000c1ca0011148036511007a000b81104200c4110f218035482240c000301101d91681100c450003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 951704955 1250 951703705 951703723
    0x6030a1e02120105091003020907050315130219050a05040e100e0c2d04140f040c0201020a02010e0a02010203031b120f04020f03060f2a03010e01031a0c0f0c 69
    0x4801c1c00400c2d6207118481c0905160304031a0f090303c445400340d070f03003685203078241c0b0160200950000c41680411420b922610145a0004030441405c030340d9240000000c4039100319400320b4a0031500010303008001900d00345903001010342414002d040074000040540140628003074011303a000c1c2c5d8800105140d0781d42850500422a07600340d04410b08090f40e0b0003070294002c41585200307100840301300840d03c681701407003015001903d55503400c140c02c001c00d1441c81c140740310170180d0050f00d8140c1240265218402d42009591a40006a4810180d60083d0075502c0a06440006402c10800c110240c1d8002c02220b071b02000c407110380602d07146100030003a081c2c001d100d40f141e0714180324403c001c3c01901355090640a2802129003510314101c4104059903100700b1610f009d80068a4070100d04454001c1909454424114443e2010f01c9005000480c49400c264002d10201c054000104140550154030b9110420030100c144072a28000705041c00522440800c503810702c2d40040d51061169040c004522 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 951706205 1250 951704955 951705011
    0x5040f15060c021503060d1509120e0a0806040b0412090803160c091b0e061c06031b140d170705100609020703080a020919030f0b011406030a 62
    0x91100e40300c410080041542940482c05003900d03010310803c040c403c13810740e0b10900008002c1000d0841c5655001200d4409602010b501911080b1700b0700010302003402c018001800e551a041003039899000c001005081341c1c001c076804d801000611010980060310203602030382004c0c82c40d051910403807080352003101c940e02c00c1c203007400007090314003141a811030301120381401500340c2503102e80c03140c6051084171110104000c40c5101c0d0004040030300d002c1c1ca110001454000e01044c200b010802800b80481c05400840380c1c1d06039140020701c1005260442c0004059400500ba03440506007040c180c034080c0100346240c41a40101910700800c81c101c654030071106140d04429464401d5072600d6950303940301c403280d44040313130410310b011803110001e10a0b283c443c2e0b0160f0b03406080c5c1d1104070001c002540600d21058011104c6e641e8031a0040800d101e10005503c40d0b90b19803000c014034140b42d8000b44068108400082c0d0100c50300c14143c2e10348007565001100e607180003590700105c0c550034244201c0707655060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 951707455 1250 951706205 951706241
    0x20a0b0a02030a050604061220061210080d0f110a0614061518060d0f060305070e09061303050d2403021e010207030f0c030512070510051005040f 64
    0x14031854000d180980104001400329441d0442040705540c110b008081c0003000001c001c101041c061007940f10030b0b5940700b00c104440c001040104881e0360094181d01650840318042c08000708024007108010140ca8010b0000c1500c506030040c2141c504410031030030099980c84901c00c0301e109210900313215602290412440d690064120408a405c0720703500d103d0b0701030f80110f08001070a04112044420b59807100d0100b14601410080c080d00608022050310341c0c1c030b40d1080c02a030b21902c0303510091401035006046151910144080c0058020310395503580c1c10400a1044120059903c03001c50391345402e241d0b0f1940b114214540081480c0050000c01143c1d01d035074508002e914020340c20a8034025109508045140a0b02e00d2500300582030480c0143d000c8003042021421003408900040d120701e03035141c025941c0381c41c2c8914148490f107080156410000390034040010030054000140d99082d402d0060385010b5041c034004c900306100e054020791b203500f9540c1d10f41e050340e4801400080000200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 951708705 1250 951707455 951707461
    0x30608060a0905061005061e07020406080606130e06010b160507060e13060305031602130207030201020901030b100e060d020702090103082110120303110318070f0302010512040201020a0b 82
    0x50b0000300707010b480600030303100030a013a1040e011301340382a2540030b0300300e51a00c44031181d4079110b0001001580448101030229030016915400b03804000c013440001000c41e4100707142000115100c008800003028900408000300b0900800e0150440e11446131207a103480c0d01c00c0e0410556418034000620501032240081001500005600005003040d0755250030241700c9881e42c4212551400040c2aa41c018442c810250405030f03150301000d880a030000e00300310601c29100d0203a800c032200480141c0d4001c0703950101e95a0521818628010444914451031404035001c1d049050301a19503004400c005140078906040350111b41c003140e80601094050369490501c07404540250055004001302d000c98001604070b070202d01d9000b5000f42046038001e03468001300500300e504158088090541354040603610003081400b841c4030b000705604900d500104044054286020703a00006400d41c865003003407000d80d80c0042500c4001c01512030503034090302d0714001030380341c034003010f070014603220041d010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 951709955 1250 951708705 951708721
    0x1020f0c060d11130905090c18100e07030b100c0b390d15150f091d04020a061d0108060f0d14100603080702091f08070501080c0414060a03060806 64
    0x11a6040703460170a4100a5912010b0306ca50725104144d04081d4041910000b00b1102440900340c141c00602c01958251083d40d01c0d040c1c0992a1400c03038410000c2aa0740d0b4118030241040d004d006401119440c2c402c0c0724101d02d035241d081c00c4030013501c800c09140748400190003450704417a580d002514540a030684941031003c00e2a0b02e0340c821840180e80d1410101c2500100b06800100b0701610f0a1440c00001541c2000c02224101d0340703142d43c2410004081c0c800038034066003481d140154104069114030700d11b054010b0201c1d030713000740d4400760400007011007803a410580641801d1281a00746070051140e1102130002c1c119006000b904c0d80d00c8010b500f1640108020b041c6c464186840400540e015101044020012a0b2480c40081c0c030348481041110700604d000e082065215846c0301d484100000501465101c0310170b680c000c459654007400e4180725030b41c0c001c02d0140c0e00c91020b42040e8541400c0107200780808249074002b07402042e000c00d1891400d030190b00040060a1240210355061400da10303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 951711205 1250 951709955 951709987
    0x304240b04020429090f060313022e020f03180301020d020a020312011205070e040201020f0d080a110414062803060f050f09190e0a0c1401020f0c060d11 67
    0x49620390008011344c030188003241101a107041c035200512072404803d03180180300c0d1a07480108207842d42940c529900c4c00594404440d0340032980000d5110450402c0140a09095116810444c080d94881c100341c41c0451400011203000c0c2c0c1010078104074070041d20700413902a00a8a0f20000704c00d001103100e44020760b0000151444920410f840c014907644d0740e0030008004540f0402405a0708800360922501501c181034070341062040c0704650358105001c2ca130324140b200702d5086c04005a428014007031482d4842c001c00711210b0020540520700f03841d0910b0300e4010320084400d03a0080304c0c042501c1c010f0202c8407905980c0042c1c5100b900044184100f002002840c46004030030031400807610100d0310f41400076800341054405481d403402074844943d1002030001c2980007d0b021030300e804180403a0041401801d02c003c0c4580b14003d030041c103184016040c1c00081d440740307045500c01a2500615880042c4015100c8029100c00d995002241d4922001d01402d424102071140000742c00070302812020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 951712455 1250 951711205 951711239
    0x60a1403330112030f0e060f0316020d2c0303120a0f150e040615051002010203160c021f030f02030117010e0105060607021905040c02030d0b060304240b040204 70
    0x810302240607a00c50358146001c0310f04400c0036001500c8420100d00407030280310312803a00b00340204204e041484008500c2000e40c41215511408000e101c03070507182d19010044840312101c1c82c01d00d40088480502010740c0059602c00b015948814030703580d54540d031024411110340d40d4201410988501e401c01000b805895281100c18ae214034010800e1031140901c50300c0c609441e082c2070840c100c2c0d00c41d80c4517003000e810707621004440f1644611001600b5030300d50140820030b0032140c002581720318194490343d2086003464000b00c11700042601c1c580040c1e49086282710000c0740142c03005844105000c0071030040080b100c900400910000002c81d00800710084035060040302402844201d000c0780714113003601e10648200341c12020600c5400e0061615034403171504200380744800da444c0ca44c0d070380000d0151380c0412080c0d0050307040020b8540840710b09001d0001c2d10030003528014950b050566a004040c543d04880c04201c012210389000c89200d26000f000b400d80c001841503488944920600b81104402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 951713705 1250 951712455 951712543
    0xc031a0109090b15010e0a06030b01080a0c09120c0e040305190e1012020f030a0b090f060607080901030b0a03060e010c11150618090c090609060a1403 66
    0x1000002080345050082c100c04941c81a1038041c552100c003903280260002001143c18400300307450aa801c0d0b100d007031203080108290742d401b1800340c900c000003511202c0041c0c54040c041c0c2c1071a0388203842c02d0300442c003601240c4400e02d0f0507070800f04904041e803c9640d1a080b0f404611007400a100500d80d00802405010000b0248400c8201b4080400e84c0c0d00305500c4200d82d005007102060049035402038550344000c85503220058541030108511109607807085461385141c03650394008042e1400c0c080301d25135001ea0428680070075410f150000852500642500a0048500190544099120750807807040c01402901145c402ca85070300d411406840b0710300700078445602c2e20140c425464856810301e40480003c6018040d0045070601081320080020020f0b50020454510001c0c070b54140100b131881002604090118148044100490444081c0199114000311070621002c2c1c1e40d030617140c0c1c00300c4902c48420415018024040790400c1c3c1c24070100e031201c219407041d226054148082c403495407222 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 951714955 1250 951713705 951713753
    0x18060f0e040903080601050a1107080d09080a11040207080c0a060b040e1f090c0506030712110a051c11161b18050c0f0f1809011802160c03 61
    0xe03900601003191000380c0083c0c0021500c1000c11010350042c3e0007000b60303109910705060740790494a00c1a18046440c0e004407443d50108a0680e4001d41c8090110040e0413000d01400d00d41e0b80b680c98210400e110340081c50310031940000c209041100402c22a4425200b9005070740c4811540d00b0440010081c0a402c540900c0c2020001c0243e1503011030700304003585031000031455030f03031003840300c980103007500c8204a0f24107440250100302e81d40c40e10080c5200d12407070b0395048207588100c00e6150070b0300c100a400c3c1070264424404004031b2504201610460b04001045071303030004400c0e60300c40242244030402e0420300000510703003a1942030a81400d440070b000701042a4000565244200a191203129400c8441c0d6000c4145408254036004150000d207038043c000c1c1400c1450503100903d50116412409240b400512010f000b4818401180c1180c1c2c101c0d07a8524561411003039640707101c1520b00840c009039001400400581c0c080c000d00c201c0580064598031b00607100d1400d04010034a0b038402c4a02002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 951716205 1250 951714955 951714977
    0x4051b16020d03030911031c1b0f051614010f050d110f12060d0b1801061d0a0b010903050c04180605010801062607030201110c1201050610030e1c18060f 67
    0x1000203120700040790b40a040e4548201c503120442d02602c1c0c00714107509d03102c680f44580012840c11010340c500280684040e001800e84c03904110b51100641e40710b03100e034411090103060203a0b080780402c0c4100225040440d900c03240c60149900804444d40c051002c554086401c10320a01c114003c1c29901510307801080164951800300943d4880020300101040c0c00d003000100b07020030303140c0e1058103000700000100e851074640342c1c441c1440d84000e4004bd200300d507080c1042a0403025005020001c5401c1c00d25040190940d11517584918a100d1410f00854503060f42041c0c0e910300030322403030341540c005400b00311558590780094080c149a21607020030698650f86001a05010141d403034111800100034500e10b440d69006492000040802008034003a04008064075110150b503003001c0c23213070311000250b0341c07801030204100e211060b04640105031030504441209200000e0390b4800f103000310960b159414184008990b075429400c00d0f455206000d1000160864001100c04021410b0361200040b00c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 951717455 1250 951716205 951716209
    0x715052703090a030f05120c100614030d0320040906170303070c060510050618030115230f0a080a02040b04270503090d051b04051b16020d03030911 65
    0x40951400654001d11883c4104001200d540306000341900c60800d4801d8010b00c0b90104c862a0004035014141da00451008042800079101d00c0020342101405010090b001001007656070796000c4030f620074140d031101c650703088440203040b00d4800440e00000302e554648034002040604518421810045486c000d80c0e0700503600401a01d129444030790312f0113104902a210440600409405000100445400070a060301c41c80c00a04225000d88024407140503023100785802c56881c3c03c0c04101e0541803000030b02c04001d01e985003001004600b684800314a0071000015001c22034201440da100c01c1d1081c00048114010540402080c003c50b020001ca4801c0000c0c4801d0758945c0242003d802da1740c40000480d401004900e2040c1401401143c0c00d140b01c8202040602040007826240c6911980b280b001018030202d5200e40d85005450600c440c0c24541c840115207a518002617062030030104441841000090f00c20043e1500281540d4445005050290042a120005036a5540c1c0035840010394 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 951718705 1250 951717455 951717457
    0x5030f0322060516031202030103060504110405091e07080303070c2117070212041e05030c011e110d05030f0618161b1a07090302030a080715052703 65
    0x2c41c82c584079a894407201d190405403290403402c048041c132040c800c0000c29184680301840c041d5109100006030703401c00341407505018090000c000e125504110400c441480e0100c0d00d0016103120504a002c01d407485220241840c41640141c0f10a10010082112071513000420491a6000d60440081c01034206031a880d0040b01d401c0310008034000302e481c100c0748140030494543c407842c18410341d1160650541d14005c2a4080e90241d031141c1c41c0b4120039400e0001e00d441503001400228001c1c8400b59050380080c5c44005401c10840d074810341d00d801d6501541c002d018907503481001c0b90170f4903401c0f4543c01c2c0c0604544c20a550740c0243d00c0200300080d4017410040c00301190111000d000c0301066544032651340c00c41070116088410030000c0c0801624016840010b90141c6102d8895415030714121801011140341c01800603041058004040015840101c2c0002c822078202c4200bd69130398240c189941c603600d16202c44403006180a00304800780c0c0941c4141c1c081400d10140710225544071003001035032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951719955 1250 951718705 951718709
    0xb011101110405062101030507150c0c120812070503011502151b161a1b0901080601050f070302010b0a120302100e0a14070e0c0a021e0705030f0322 65
    0x503040c1c00300301c02c0c042481d1200c05044a202055049007031201c030002100b004140030780c400c84030f55010103020300090400301c41d00c0401c3c20042c586204041c1443e203812a5900240c4507501c03c031510444601e0030f0102000403074003000c01d030945e0030f00340e82449507004210380e009110302000b8110380d83c244110326201065071034850794070707a5454040342c68482040b416405c50b40c0381c17028101c008111580a124140302c000c00158002c208413003e41141207425281042d0003404010b041c21580c0300d08010142c00416118005820320b0040501d0f0341350340c01624184501402c1c80340d1038401040d074404155054021000000d402d5400000081d50380c000743d403043c105903900802681203a024410344000641c40303011a0081a001c8491a0780b080e10344001a00c00009503003080d8001c03030020700050700c1c81c03002541c220002525076413800c172150741300079110004511041c3c0182d00104a0360f468007420409100505001410b465130600011400360340c03a4843c049542410310940180c5111071041c2000c0d001b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951721205 1250 951719955 951719981
    0x607350c2119260609270d0201020d110406020712050102120411040c050a120504050a0f08030708061e1e06040b040311030303010305210c0706030e011a101419030b011101 75
    0x881d9844100c54840040410713486d0b050b040490f0b041c02030b402c0c0c03420410071195a031547c0006a41e40c1d01d1035200c40c10b94807600048038050720b08120401c80340d68009280011202c1e4070042c007214070710515220340a0f2084001c0004c1121461080c8402e00480ea40d5000300039200709d070208040964001d054615024504d141d07000f142c00000d11010903c01a00110350080c410741c140c440b202078580c1d4400e4a855019002d1f500311501208000481d07402001c0c0b21741010301210005415800343c1684031451358141e010500a8800b09464040c1080c040d07191000401c0081100303031125210703112605640c0040c441519500d0344080c80c1207990502008503410389400001070320341d0b030301c075008183c0180744040c40c41d289150040110703641106080c00b6850107082070740e5010071080c4038030704250300751500c140282240300c400022190080c1d03580c000003108101281407005189404180048507401007901112040304003d03121940164180d02c03052510340240c0f5225140b04c0d0030100707142201c03080c00c5514 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951722455 1250 951721205 951721219
    0xc030e0f0106060e1c0b0403080601021608030d0c030f0c0503070e0d0c0b0f0c010c080610022b051e07060e030307020303150607350c21192606 63
    0x100803400c1c0041c440e90340c8081d03100f10110300d0702141d949240343d110465088d000101640180300301503031f050042c06004440240c00280d814100b0307100640703d1061038560000a99142c00c542d140074000c0e0041a042030550301d040007082c044841c003502550040314040f00140150b00701e40c031300e07180034122609800d4101c086a241181005075150007a80201002100d0110501403544004024010107903102055038079400c45082c02414000600744030f0b1514000c3d90803064110320b801c190031007800c2120380e040e140ca120210007814169882c0c490988210815aa0400b40c644881351b140000c2017000d1085400304661410452040d403240820303154000145c000700b0100e100304440408424200e10024841c2d4901900ca603200d0414482900c1c1c42500b0260840700358050403402240c08500c00f103480c1c00e25151919041c1c4580d2181030f8013041d0040000ca15071010414640076040c0d8000b500708620711003c100c86104058910720090b10a8801d00a03004802c040300088010400e02500018100d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951723705 1250 951722455 951722477
    0x3050c16020f03031e0403020a0e040503090d020604090c0801051003061224090b06041109010207054b24031801060b0c06060a0b0702060c0f010c030e0f010606 70
    0x2034031544540000350f2612042c080e09016001c0d507441c0705907403040c0800c5a580c60b403440c4140006060760b0392000100c2c0c2c0201f800c000100b040802210306610302111007910341c0300540300046440c0240d81101d07011600d4442050070740c54104c3c82081c1031b2801107a0300c400851007210101c054070070900581c00351074019421007000652031842d140b511100014841da074100e24144100460f03c80f42402c0d01c800c2e081c8414804941130a1250300072554035002658684145000080e640e8a5175202d0a40241749a10b1505068402c0d000f80505101c1c6540204a1410010f5a02010010f13240c04041602000842da40054540084c048004e43c00e07a50308081c0c210038405079245170780c1000b000080c1142515040e012151803c1c401c640150221460b0180c03160031b1204694642a80108150301a80728200140000c0031014180d034449a4102c64030f90780c91001a000e142032107115034040b50150700b85039280c3c00144c0c01d40c10071642e00c520241100c207402c00d84130b007503403d8036018400d103408a4802018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951724955 1250 951723705 951723709
    0x1107060c0b07020f031206011d060a050c0109020904230303240415030605010f0b0702061213060c0e090a05190b03010b0303210f2206090506040f0303050c1602 70
    0x1207502c8032450041c2c4004c81c1207008004c2c11a4000000403514041b00d404205166800418404442c0303001242d24409103081c102003a0107206030301800041c804041150300c1040c00c25004400c12a9014011a0003410180740114040d1200f84d031403d84012051283c821000002013564480e0421301507031101c84200318144a412052010800d40040d12001c40214041c00c10b00c0300c0e401107100c1d00300095658034004250318140005d41044200d404204800405640c822003a03444001e11303400c000c0c0540c1c07580314600c402014000c40007401c590034405800310310343d0400200c09001c00140d40700305082d903c019003402103900071984540541ca080c8400440075000345e00580203d940600005040d40406000038a03580100360721080034040c104450181841b0507400701d03086511200c01034501d08004030f0341c0c08440902845042c4038000038201c2e40c02e0041a0300b19a085a4100381a2081420300341002d610302184403206a000c80e00305800701c0c0903039004008954101308100240c14181e54142e00b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951726205 1250 951724955 951724973
    0xd0506061c0506060c01020703080a1109030309060d0e0a03030c08060901080a1b1a09190602100905120313020306060a1a0c34050f0108010506070c03050610061107060c 74
    0x3c10035401001c103008101000d142480284401c0b802600c07604081d00c1c158042c0415907200300c102480d01202844150302588000041d120b4090f000c507129030300c1d21004e0b400c26000307122070517600001c2d124103c1000c00303054250341301e806004402d5440c4c040c0c9645003010b1040900c801e1107508103a13441401d040000ca01e240c00768450944960501244450b5100350040700020000c840c1c1b442c00b10000380489051602000b5103040c00701c200d800da00c2942c0f5020019407602480310040502c0d40d05c5465410401a00b8072446d006a51038010640d268144546a8000b502132140b00724080d114590200d406454182c201c2c200301c84452150307413080f00120155400c01c1c1c1040141c0d458a11900100440a144001c4403d00c0301841c0040002000b651030a071109140c540e80c031560160468405102459a21001c450b040d1481500c4499603140285400c881c41e0996500182450060100f030183e00d41c48045000100d8959075504a00e100b6480301c650b40340c074091b01c104000704145100782000208015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951727455 1250 951726205 951726211
    0xf040c09090b0a361a030709051e04030201090606030602070212011119260402010210060e0c0c19031e09050f0111120a031b21020309011d030d0506061c05 68
    0x4040d031804c42003021030210940d400c1041c800345801c00720003049a1342c101040762000030008000e040c85181000d028000d204460202c0e900b186034000000501490f00035000480c0d02c96003c07a01304501d03a500d003002c100942010404901c20450202810003840f01409144030340520818198980ba8600d00444011010303440034405100c0344070004502808030150300c006c101502d0a8548003031420384002400c00e0142070600704507519040082c003040b010007521307560102c4249811035988025644907441c00403460b0b044204004490201410558480c44d50300020035140d6180812000020040d144e440c000d01601d500500f83d10b202c1a00d9603c038203014800c80d8104002d60306414072a849005a40e44042c854202094440c80a800c644858004440445682e80b8100c0d00c4400c2000318004028000b00340540c1050700407001c036521003000c0d4490034070701c4455003500c0581860382000d142c4a03007204ca60045020f18110000b1101c0c20070030b0450f05002070303815420a480c84070740e0a88008101c06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951728705 1250 951727455 951727529
    0x150518010e0d14030a030e2a1809011a0d020f060f04030b072d0c0b0403031806060509090105060603010b0313150f0b19140f040c09090b0a 61
    0x246203402c08900440c4101d541d4aa14001856841c2d24505018094501081c1341200d00c7d440f4810a09407a8105840d083e4829113551425500d1000d210010f482080d40c82c500e942d90811f0078003440585581513110140300b1808a96a607500642041040305002c40010082d42280440384091814503049004150340a07910b079005040c50b0b00c0e07440700c4d800300900700c9040c03000c10b0300903080b414007070000281803086001050040000e581d0042005009844040c4010150301006e8003103810140030f40c20032040a40b10010901c0b01c28014200a0050105440703428007135800c0c035001c160440700c180100c03840b541c03000c1c26080c03860f4600a403d051642c4002e111501c00008400e141001030040030b601000450300d500c0c04281940841e07001c2007115900c48419108003c44c1c12015400f11400203040300b141c016884a06c01580c0060225640d000d120880c160b001f0b107080400450380780c22500a1080e101c01000401c45048581c00b0302c0740d052017038020754404000091039100311005d49203000d4000007503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951729955 1250 951728705 951728719
    0x22e090507090608150c04051e180c13150c030f11030406051c0e06060f0103060506040e2401020c060304060906050103080306040e0604080304030e0a170304150518010e 74
    0x240750080c2c1c00700c511580000e40f442d0480000300300760071001112286c100c400b60901c64541850840012210710341142074002d4000b0000c0050390070754414541e00c4c0c40502c190000310303083c680419007482c0ea0740200034500006045040200b195000ca0003243d03000d0f48241c5840450500719101980d240001c4102c08040010b066130080400e08144085c0004003180e40b66151211a40c8a029042c2c0003120101100c0704d141c240c0d104400346000821a8122005442c079a039101c10b0100101c01820440d009a03400c01400100041c68030214540140f260f5540a41c540c4100300d2210154107812004034004d00590080110781224540031004541081c41400e0010300b0000582d2141c2c21390700d0903441a2a0350402004000c10340c182800f509c08a040d10720042c003c0c0b850079684c4c0c11211700000d04007504101f150300d87c107000c64403500c0b409409800080b645280304145009203039500e81c05402440c807000c800e41040c0d00d4042c000c00949010f80464041c2c9205a80100011181c4d558a0a401680410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951731205 1250 951729955 951729959
    0xf20070203160905010906050603100306053408101401030c1b060926030c0a0e0306090102031b042d0909030207030c060504050603010603050c0d050f0601022e090507 73
    0x40002c4901d0000d059082c0080b9003589007900d2101118100c0d40000c0c0200303420000c220815011100820541e5408040006c19031250480c04120088000d14252055040e41504041c00d41c3d80807285a44400e9035562580c0390b0b15144a0b8504c0d49140c030444200403120400c2403400d6021f42c00070b03480d0124900d055140c2510110144003460105c0740e0641d481541c07280301e40c2c180a0000c1111146090781507081007005803c0071034020a210041c02c0031540310001c01d03101c40a5102d4103000200c106c00608072211420026007041c000d520a5078036540841c11800164a886a80782c1520100c42004040941d00280c0041c407142d9000101103000303004185500105401180c7e01c1052001d80c000da00510740d00c3c3c08c8d07151450045440d50001003d03c40280401c000c2c95030303010f044906450640c90042503507150250b0103451070003110000c441c03032800e002c100500c408140c078441c2d1084009a003201c1100d007030750361072450300840011009202c0040c260310300081103e0384c02c00300f001c0e445a0300300e40510b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951732455 1250 951731205 951731233
    0x60708030c0d111e03010810110d020a111911041a10052101050d08070f0804031113110a03180b0f0106080a14060108070c060603030e040f20070203 65
    0x243c100311201d2866030001c90160020f04841ca285115100c1191a0504d154140055541d403280e169400050603a00e8000030035405185105442c0d0440c040381d030564407a90813500162070015012014000340c416074058041040068000c940030a4024900143c103d11080510010700104555540c40411094000060f030702d4203482c0070f81000c1c07981d55494843c42c00740514060756414112240352040f00400510603070b03503005200c1c80c0d510b40c00440140e03198658540101c15245108014103158004030f400001c0c840400385003950007a00301c41148120781450b480c802110241400e550b4000018449010101d01942c40106c02c4130340200095004021955002c155660880e440303a071045400b001003205640000015800c980e403041c060001c1c07003104548824070f9070f006003c00d04215400b0b020451075030040f00780c101130070f4004900b0303ca82516030a0144c01c1602800305039000b103251000c8803194030780034410325006081d03000b001e004501d080d541c00c10b699086140144e9250003850103c0f9912 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951733705 1250 951732455 951732461
    0x12012a120c0e1201180b1e040c1203140c01150e1b0d0b06030405010606030c02150f15060a020a0b0a020705060627010801051504020403080d05070207081207020f0f060708030c0d 78
    0x14030911003000a807810106d00c1f4501c2100340340e83d001040d110801d002c005141642940140c407002e0002c4034400a0901701140d04500320070b5101d07404c1500141c1c080ca4410107401201c2c901003018018281140d0b900400040c000085450b4081e42c60f032460403a6041d10b14400610110000c1c460100d0a0000140001c200d9401510211041c1e9564601004602d42500584012048900140800700e091035078a143c4a50010a201002d241300000603105045440740100c070002c0c0a00500d071621044040a03503612083d920540c2c0183c004c00001e542400d040c0220b505041d44040540041d8896006110b20404062943d06150a11408400d10b02c03500e40f071114000c1064400200d024107044010715018080d1280c61409180100418400b044904003107c0d004070262600284036034506408909251a0303800c40200c5003d40d8807820300841907000903050003070007190300e144d802c150b600030080100c9941c0b032200d1b0044003e1108602281080c800385a0041d89104903d140c8100d091120b011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951734955 1250 951733705 951733751
    0x90801112a010e010c20010509030f0306190b0d14060d0212150c1e0a080103020d0f02060a020106050306101212050706150602010c170612012a120c0e1201 68
    0x40e8801c0b40c0389042d1210303d03082c6d03800b41a0341002000700f42441007565807030744108090720107900720001c085001d035151005600c01e2098103012601c0259100d000501940d400810001c0844d410015410300101c07014080601500008003590100d41031a401e1051900c100001d4003620700840c07680c00c0c65410041d0300284145c210404140d5210440080d2071820518000702d612a0a0b0a000c49000b4a030411003481c1946d070111807005803404035150550b5801c1ca40c2e20001d422401c085022941c1c0d03078054003c0d4099070411410340381142d5070348605038403200440c40b40103040c19440360004041910720002c280381a03120300c1c101d490700180d91204070607588200300031034001c2c3c0001402c010450b42071141e0030398150306203404400e403055842d0707400c0c04844c0501200e00c521140b04a403400c03103000354040c4101300598505928046103021b900c2d075804c18441886000b003080c02c010030070401c50030300c559412040701740c0b5090001c015a50500840284507049200304c2e6594520040d1b2499078240010a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951736205 1250 951734955 951734957
    0x91507020d120f1a010908060708060904082b1416051e0406080a1a091b0705010f0b0a06080c0d050402011403190b060a05030f1015090801112a010e010c 67
    0x300c4e0300001c1000404101c180ea10046c040e80009091122140c0d0150540b9000b001c211110142a00c450405a41602c50301450b070340c02c5c3c0b500119110701c40700b81068184040034880c5c42049075224140f2417034404a4102c4411040032a0a040107140754007400c090080c6601d030340d84c078010480403411400b850b0b074810f40040012550a03c20408210654014081000703482d21342c07010155000004100c8116000d400c00c07044c1e81d0458000c82000c64042e00382c0724410b03000b000a12190b14061280302c010000f50100e54040c41c1001c10210f00ea49c00b40602e18018400301044e01d02d01050303041d00c00000c1402500807410800c001244500160b00500911300500004000c402e1015000c00f0740030403035000004640c011341040c031001d561749400c0b9041c1c0b54007030b281c0007640005988024035918030185940200300c1d41180c0d03401d0301e44642e5004071000140c40800780200480804c03846110305a00640c115002c9c01d115a0445a15a4035802c540304000701e90040049a40001c0b840702d035080da0441c0391040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951737455 1250 951736205 951736241
    0x10203010906050f0d020f01050d060e0f0f09251a0d05150114070c03050102121b0712110f0d050702180c1e0d02040905091507020d120f 60
    0x8080115030b0b100305001400120380c254202c0c2d0002000c240000381a0b10041d201e10850111050164040d404a4000030040c82003005072645400c400e0180407400d03101c6055610004c400200d000c9030113040d1a00820885004110a44051842c1c6032070382e01c1107044980b26514200700103820001001c80140142030302c0e215944032502c1481590440304000d00089084511010507001c030390f00000307584089d02e100c680311950740c02d503410024004503807580000c00700d40c400603480340d000451220050007524151016400c041c800c09000d0101c0c000c152010780032a103190400c2030305500496008440601c024255080091107460490820032204043d0380401c40000f0a90114034010807411b650000308481c1e541c0c00e080a9011496601658990042104a800507000c90999101c01d40b105a080403006542d07031034840300140041c1c04150784150603449180202d81c1d9440c8001d103101d11400540c0d0040c110010110340442d407001758055440e002e1a075800503035040e051113004489020030030701046 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951738705 1250 951737455 951737459
    0xc250206030a0905061b0d021e0406110d0e13020a020c030d0306140105210603150709030606120215090d05121306020d020d0311120703060810020a082a03010801020301 74
    0x6a05010000304070220444000707003806c00c0b000142c020b0354100c9010b2600161541c580c2c82c0380308541c0346148500b5114074800b08001911941c44800d121007031004105448a0220719030056416840320381c040c0c1d80c04250304030783d80709400b0b00c6ea02500380648144100c2c0d19150000e008681407000104050000039101d90702400aa050501c181480c103200f03181c56860310421050411302e0400f032505000700b1002080c0814126a0300f08003840035482445030a00d0181440c0f8809002500d80d0310007101d54a05000c0c002901d00b086503500c80c0d01e0b90b0040c0c12000d0706204500e600240341d01c0103401560013a1450b0044011030800c111300c0c2501500100c0b02e954550009114032038404040d8028401c5620000d00c61a40581c040382540c901003141c2030110b620354002e0b546070294041d03000148105c20100f0104011240e00d9040722046814010a507030fa9006466240d405901c510304400c00031450714004109514201400413402e0f2040c07540d1448423103070f4680094403d5100303a104020a80d004001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951739955 1250 951738705 951738713
    0xd0e060c1215180a0e0f15100b2106040b060a0f3525050c03040b0307021e0601230a05031218030c13050a14100306140c250206030a09 59
    0x5040c4840840d40c014050448499404c0356144201c84607008071f20045400b1440d410301030440315010788501c5002c9a29001181080d0b85681540485a000000500c011605d113051501c50184031b0302e4081c0440b031030a8103076070f41600e8981300207241c00100003290304c0116110380c600c1c1000d404495550b0001c01a01c00c40c085058514802610088403ca0b00341001d0b5009940f010042c01c0306802c2c0d060132a1034148101d40070703066004507403050070710407000820000340baa40454034000760b805031340c02c400896000b182860b40d03600f001d0103074412050280d1002000381080042c4201031105c002e054100391038580780403d09014208854100c40c8401084c000049540c03405030740414a003d90007820203d00b80300004900c00b9200640400b020350310004240c5c110002d40203400b800842110074500303410100b20104503281c1501c0296000381c17030456a00c001c1003020940c1801006041015401c091003c008090851458440310320041c0c24a020074005880300000781d4417861b030031270300010065401c0c18 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951741205 1250 951739955 951739961
    0x30c0310021c02131206090b0a0615111e0109061505090a09030e0906030c040c0806040c0806130b0112090605101403060c0d060b0403080d0e060c1215180a 68
    0x107a5000e54500520401c0c0c1c0e01000f802c03020f011980c0c50941d21764111080c0c00c0c10317002014003400192075010400100720164440c0d030000307400ca0318480c4001450f8100e100084a426844031103c1400340c008440ba901200c0030100c0705800100d42400011744110181e89038400c55103070a10801864181440411592420b071401c0d903400041c000301840708c80c5595400a002da594507074464407406184011a405072420007018042c1c4101034410001500e07070070005000150212030440c881d07424000560303186481500e00d58094113020741460078a83d02c45082c400900703004690a41001000c00e6040900c00701c1e030065051030760060b100010181015040c000481c0d6054001204c4d1100f8a0002540e0703450000704070340d1180703141c04000d417101400c100072806010706a100d60b10360b00d0085030100c14032a0010041c00a80800501004000e0110820985510080703602842410061000145072000c40000b40d0f8002d888a005d100030448100028005400c02c568020701c06070700204200407a980382c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951742455 1250 951741205 951741247
    0x51503070b120403081308130305060601032705160b03010807060305010305031c0e030408060603070e060a0909080d0204090f0e030306060d02070f1a0906010b0f0414030c031002 78
    0x35181d02c0c038040d00d04040051000c00900001c003046010301c0082c580601d0f46801a04c0150312020841e600c1101d49040e0300140700500040d1030314001c0d000800c469600034030400005010b0024040c2c0c0c0d0158103120b00c400c111003604185c940e4003d002c2803150414400000303001808016003415200c0d418401030b50700c0e00300150408000c1c5440c100041c004660000291003011200103005801c0110a42c148400703814150b203007110301e100200e004a020f40700858420311480c0c042d012074030440e5a402c0fa00d02c0340c00702079a0090b0004a00c010900c02404660080441280541c4000345485d540b0000c0200700d0707005e03a000c05e41c069030715034034003090464901988000101c03020040d82581080b5000941030f10410704002030250b80001d49504010040c000c141607280c1007000c000c5030700709520a54628860403281c10300c4d00d01030034001040000e010400d84aa204122128506280c1031030881c140c1e240e25502c0f4030745d040c0709032000c409030365508000045060801c4a009601c811161031a017001c40500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951743705 1250 951742455 951742469
    0x70e0102070e1302011107060e040f05060f010c030507021f0f020616050c150127020c030901032a0f030f0e1c050d0905011b020a110f01021005150307 66
    0x1d04400c00c05940b141c0c0000303420040740310002a5103500c910040c1d40e50f04240e010070030140500c2000050741a04041b016440c43c0c015282442482d104c2d00b1038a040f5502218425481490b800c03500c401c65204611002e207407031003030400914110190700000c800b410304901c80c030201046403468518540d4405280e50311405280020807180c2480508003144210301181e40f03040203c0410020b079040820801c186658804202c0982c0a507121904c9041046010104403001c041c000300f40c0c101c400d905d200b103d076880c09020103141401c800314011000707003480c400c0c014148a01101c3d142c000d44103c1d540c1c600801c800340c840d80083d00d032584000c0d0a03034040b82c0c500d662395840e1079520142c0400c081010b0500302d052100701c42e20142030100c161280e000740145007107580d1401019808100055000600030f80f5506480f52034001000300403039586c40900001802107502c80c501329024100802100c0e0a03040c1401900c01c8118007040780811607800311141d01c11100102445e440364181446088043c1c102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951744955 1250 951743705 951743713
    0x40306020f1b060717090a0b1302030c0a0e010504110d14090606010e150307020102130b091305010b070f06110d0b0a050a12030806030102161b0b1801050d1d06070e0102 74
    0x4a130340940042c0d0804100c020080b4400d00003060841e06000c1d4102d420b610800880d07003418442018400c20709184803c81c020311895116208515184030303418200d0305041c40b104510b03803c010500015020781c40c1d2100b90601c00b4003581455031003502070201c0700000d580e08103e051400c1c2124600c0c02d000038018505002074025080d1554603580300305d011003034060390001e40d43e4a6041040340288190350710748c68207003481c140c0842c2c0503e43ea40107004400b01100c445e925544080d05000407144203202c4c641c6085020400c5000240c1d0307840b00112034038000c002c0090003003c410350b05241ea5104204240340660f44001c0203c85140c1148294040c00c02525001d003410300704201258142c1d0103082c0901070103c0180040e4841d6004d404a07000c174080580c081e60014401d14001469400309110000006d08140022030512040d1050341c2c8100c03149600720810002e05401503d45074000040d010019480d003404014102c1450f00a10942a840b0014500d034940350500803d134603400301c8a1411504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951746205 1250 951744955 951744961
    0x12060f230a0b061e07050a0302030a0f0302030f0123061b0f03120402010c0611040e041a091c170903090a0b07030906030b1314060102010608160603050705040306020f1b06 75
    0x2140c405455a9451100c03055400c43c2000f02e544084c0c2c080d0182c000c0091044080c22001c15a012014181e188078540b00c800030b82a002c4002c0c0c00ba4041200d82000c0007504600400803c00802c5444d4100504c0c48038800034130b01c4450125929034840e0641107401011441002c00310740080000342150708400000d141000d0f11401106c2900b0300c00b0340b002e410031510b001c01c60300f40115a130203022400f00c40c807c1a07580c0d0341d903280301c0f07201c100003268107581402403480d004404030b400d20220707485030a14101808011840c483c03010051002c010380350b8108a03502626825080503014500c0c0136a108000071a00c410708001040855551a00003c0e9880020b01c80c04000076000810303542035030400c1c100458181c80c0b441c04180d851090704100d00d90030303040c043e0360710414203004d6040340183e10030f900030320000303413105045a0386034114100d1700e0101c43c011008010180c801c1d03114642014151a1051500f031fa02d0f1922002ea8001d1144200b5003040040c205a0189001c004655580d03c141701a011034a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951747455 1250 951746205 951746209
    0x50303030c03060a090212040b06010f020a02101404141203070c090203130506070906110304050d060e160320010905030a0f030e21070905010f12060f230a0b 69
    0x40009810204425008004038019545065644c1c0152a02e1070b011501c0e04c1b100c4d04911845081520f0940741c00744100042110713540b04100114a60801e60001c10114485d41d0034040d61510162080c02033007000513403680108070703001c0240000d00040542c1e460b2110382208200710342d0100c50405480354010481600041c544e00340f00e40c11100024001616070340c400d0125440040346010003800750050104000d6819046880b06040d2030399a81ca50034a58000703031001d642c030321490160035803040300205d40070001107250b084014a4012181615516041c50800d84810710144d00106c4030807620410030220007041c40501214441c0034a04149518600008030342c4500e0b40c800f0203002d524103040c810302414098462400c0d0745030094030594441d44400d030b5506203500c20144005003409408800075145005000e054140d4035042d00012201b1715003d07000c4602e080d4094125541c41d242c135403c1510003010b204882d070000024000c941c55a42e04c0c400c2504807000203180d040124a4110480071a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951748705 1250 951747455 951747457
    0x1812020301060f051011071a120106050a122403050304150509060d090501091401090b09030906090132040519060f050a0e12030903100e06040f03030905070f150207050303 75
    0x141050b007041c0c072140300c61401250905c900364008c2e10f505029451a0008028468024003e00200001c07401603640c03210300032070743e82c40b480f007041002886100510f0201201c1d98080e2a5106100ca03134242070b091000c10341180328a5651082d149a0400f0404102030100b15548210823000b03450000d20f03160781d0701c0000d0031030b01480021141d600c1e601e081c4501041400d511a0300d0458100380c0c042801c00d004039059018101401c800c5400306654004900c00307070000819220307580c000815260400ca1840c0045510780c1100c0401040310440da002003400e010507407040400a42e2003c0003954a5080c4000d00400103400e100c0f2460805000c04104402a4440c0701d01c1c21100d0383d843c105980300040700007110b0510b086a20280c0c003246001b100c5805441c0007000f03100100f016010384805102c990120400c035400404007411035002a80000c000518210b02034032007a101b81400242002251180d500d441d003650001280c002001b00e06000d40421562460500940c5100402da581c1c00c0170042512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951749955 1250 951748705 951748729
    0x3070c090b0a0341100203040c0b2512030506010203190e030705061204051911010e062109071e091d0303041a010e0f0402101812020301060f05 63
    0x140a910f43d1440000d140c100c0050030f59100c4e1031140d80c0703c0304141600d94049420000094000307105865100c1642c030030314000d480c422038000f9011b1a696103010024080e0f940005005594055502d401482803203a508003c001c1a01880d080c0c842007482e03c1c0043c084420240c00c55066600c01d01001540d48808080d0319101e240920704a00b58a60280201c0d14103c050f42005034070410205a90014804441815201d14002e06c110794000c0c50860f408500041c182c0c0c1e0107490f115407804050101e5004408008075204091f0001d0310b00354940480440068403801c402c50103124040610076408030400502c2d0150068400b15400d0122424a12400c0005c2d0b1041014694032912040070140030341802000d915800410303203903285031600d010070341502c110000040041d107403000403238201450303c102d91140380c581c1d01100b850303200c0c0d808110b1218480c50300c51040000d456030a00040c9509c1c4130810040ca43c002c85001d213640303244105401d40b17600e80c100e001e00160b062000c202c1a81da00d220550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951751205 1250 951749955 951749963
    0x1206050703290a15050d0612170336010c0e033003010602070812040509010902071b061211090d020d15050c03010303120b10030b03071703070c090b0a03 67
    0x1950207034400483c28400761507109140b004a003107042d81d6111307045030040244907081c1d40c0400240c1d458480500c1000000b103000380000152115180c440000340d40110b13000750345810b225050351a400881d51110b6a40b40c4140c000d4220b003040c00c00e2043c003d0241c150450110704000310301c0704038a00800c5e50391a4000141e9640401b2090090a0700035103004165003503044200c5171b07642d60316420042d544000621440d00740d4865000d002c8030b88000c0398141d800b5030f0790080101401d6440d010350580a5000014103440018103001c2070040071030f850740020004c00a5403500f04400b00c91824a0003101c411203107040c0301d14400c118154899807040400300e01950304440210390301d400782c1803000947c04a0303100020079034034200501005d400d20001445c100e900c00e90302d04d824140740400c0e000503107107404201d80d00312418030382000d03003c0e010b5045010481c03800b03411241c01558912110210110b00b00e00600e40750400504182801507e03085407001d4109580c00303014000503000400c03405c41092001030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951752455 1250 951751205 951751271
    0x60105150702010e03060c22181d010c1101110403050c0405090f0109060b0f060a020607050f1c0212130b0c0d0f0e06091b13020c15011206050703 64
    0x1c801c41e030252280f4418074038003900702ca00300d28100302404030039400328800416840498a0651051a1801907842500c480141805905d0700b01c010450103802c04284c0c21392850f07598064502c2c104400d1244000c203003203c0e604c1907c09a084403210b800c41340300b4403903003002840401050010a0002484d21700358001540c00181c00e6403120000c034101b40c0200c603402c60550030040303c0000c0c00140e80020141c1541102c91050354030484041220500c118560000582c00c10000140081e001b2409070071203402a01c0020700d400300fa81501491440c000b002400170f00e030f0101e0048544820241c1d150741c40043e032025107400c0f04c3c658444c100300725402020000c407054001584003e01e089600690076203813225030180030f01105801219124001192591014412050300c500e0105640e40492440c000c09050800b8400c00b1a0b6554040e41c0000c600c0d508d54440c4003060034100204e85c1280b8000c003482e40301d00c0400f11240c0307460701c19a40d01410342001c0504080d1110100c2490403902401100c201c1804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951753705 1250 951752455 951752467
    0x70302060a020a08190806010804030c0f020f0612090f160b0a14030123010e01090612020f03100f06031a040b130f020d0506030f030901080c0c070b0702011106010515 73
    0xca240c03c000c00300080c15a44003003581d92101020f280086498401a101d25050395106401102c00c1c10080b0790103400101042c40000115500841644e06140040c20028485c003504c8003144259111070345a40e00c0c6152001001141e50003402142e001690003400385c842034005071030b280e04488480c0a00014600c001032490f5145028505c41e4070545c7d60000203c0e1690b95400e2540094145003980000d10301d10f09880000780e41c808c5079030103010a016103485030490708100e0111104a801643d40840c10350801208409104441c09180b203441c0c40303400040c3e11810b141c200104402c15030b000c03409040c100000c0040e040000c44404070303003000950700003404040360800240c4c10500c4040d240d28081c079051203544c1c4038141d600100554006118140815203c4d103003071564480011030b03104648d81003800183c030150b208083c29900074801c5c078501030601030007600a0b405d0000f0b0f43d0080005180000d121004c5580145501e042c60301c40c00d01410340b56140ca8003040c144c011410703094409800001384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951754955 1250 951753705 951753707
    0x903030f0309120c120809191e06052a0a12090605041115090639060105182703040902070b0a05131502130302121b010c020102070302060a 61
    0x480740740260800301e0000103520401003d0300100f81c4d01415544441407280b00c1d51424060030445006a1080e002804150f0f100711061040c0d80103003a00310345c0681d0a01445040c01201c0074404d1910740109800642428828010520141c3c03640900400c0c6242400b04100000250181c0d0007081041c24850f4044031a0304110005000151005001c0c6103840c4c148021b03c80c0c0241403c25023034040d01d2601110341900c0080083d4040d01c2c880581c410010000703440000310000c000a86103003040c11140c6607400d1040c0200001000703110280d01c582c0080010005443e040c107088c0c48202c0031090741e60840c1401e200b1281040d200d07440e00d0308040c2d6101c107020007031b110810880b0020306005100715144d002c44d1030480224101a1155540c2d0b40c202030218031a00e140300301c60894030764010030801d440782c200b404002c0a5046600419141c1c61041e0001015032115a140f04071521000d0142c0160030042d50300041507207940889904000440b060301c00140d80001d05d000c140ea8040750200c1d100c6180e580 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951756205 1250 951754955 951754961
    0x9060903070b1b1c110c061504020c0d020c0906042c070b0408060103050f01140a09260d1a0f0d060b06040b040e010b070308060621092b0903030f03 65
    0xc20701c5060403000503810003020194511031000f2110050038008200c0c5150a0b58150103046c40c00e1001350803813400314100e1000051490f402007005000036041071540c6800a041520240313007040940c0068441d5000c61404440541e40024101c07002c00c00c41402c1e00c800488605608450440e4060f0300308050100c0b08100044001031001c00251686c035034450480303a44407507080c40211381c03621075103e08800c070610600802408034460700b018141c1c0c2c3c3d9000c1c84c0c45c02a0910440c1a01c8075218484d8062461040031001c40c1880031005000340da03a210701d0329040444081409440c0c1d0382c01d441101c0d21255079402d01d4140e44120803150400526090306040000700280d4500c47da1240d000200041c0000c03c0c071014004480e4020b0103209161390b604006841d5104070f01004002810600c0051541d151881c083c110078100d6404007401c0d400c00c0c070808100fa200c00d0703c04082c540c0c00003821444070340d14503045050082030440c0c034240a114010024202c0b81d41070000070b00307004e4039014800c0d00364420742c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951757455 1250 951756205 951756241
    0xa020303042303030406230d020d0228020709150e04030e03150f060d0812040602130602070b16020d050715111b12030702040203160809060903070b 65
    0x1000d580d9615661103482d0055001c50810420480018454400c54500803058400b01c0e201902c0b05081040d85150441d203200301300c40340030118641400940c0c9010800d10140a00b080f0280c4016940c080103c038210310b1460650a030101c0d54032240707030340d0252540030070400221405400c0100d006500300100d07085e80111500680c03161820340c810002456400036108981200550a41c0c141d000070240c251540001260403140c4500003202180150510001e0000c40c07a020f00c1240d41400308094502504180655050307920680200307550f01580c40c0c0188841c001c0c02140000e00e003e0303141c9503900c02d080c054108030450071071078511600107540f038588194490320390160640d415982c4421029506000c060745240000c3c41080d0014a244000a10003c00c07080403800180c41d15503175010440302140c5d58001c0342d00c0d40010312032000161243e001450007501400c00703000420035801c0c2d001705460710050078018160b004c14203101120724040201c4e549075030451034114503a6103a01045e04403030804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951758705 1250 951757455 951757459
    0xa1715090a0210031128080609250c1b0f14010e060306120f0607170106482a0b0315130b0103060503160b032509060f0813080703020a02 60
    0x70594034100306e2000242808810701e41c0c13201da4580e01e45000388450b018040324030035102c1d10342903007040800c00c5441c0c41600c2d9071304503d40801001c90555540d82c241684a840150140c0e000409100c150300000f8040040c2a03104603070200704022100090034489050004c0d07004250000c0815a86e850383c2601040d06440c0c4401c49000c0d00c001000d03280e4503502160104001001100d0a002d0001d80920f4203049984640e603460705e161136000c4107060044003102c0401c0b0002c0c4140030510b0400341c1c0b0300f80061502040090400304019051401c01895070b90250640c185d607004640e500082e090084000ba21814481c0d039440781d803403803000103e081d01c01006035400f94003513041801035030072a002946410000c0e6004d20195907150241981d412012103401003030010584240000d900441c0950307400305400c111f45040140400912541443c46044000012005002030042c160080110308400c0018a00540c1e40d00e031110240740c1c050041403001740300800004502c0140741c4208118042c045d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951759955 1250 951758705 951758737
    0x910120206070c23060301030c0314070e090304051503060306041205090a090221040b07030207020f130c0207080706020a1103031210080c03010b03030909060a1715090a02100311 78
    0x10f900301884043c54a24030081074001240750f84e03034a410228140d80c107c0ea445030718004240d0450303071403501801304520f1610551062240024015515007042800b8520030700c05107070707030358102000d00103070040440707000c20200410820302482d5200000e5081d40180c000c0d12403a0051040641220148182d180c0540d0080300c07200d0225980400358000c0c1400d080d00028160220f182008101003402c08440c050400031078200059801381c007a03001004113510040c401e02441d1500d03000200e01500d10240b000200d50780341441c2035110380400c144005000c0a000804030146000c4009588002030000141883e60b900d40c0241107440c10810385289441001c2c44c0800c40c5000000e00c4c6035002d05206107000f601c034508100095017010300c01c0754040034014000d940703414414828007082031000b419107604070803001800264481c46441e0b02506440c5400a01031185020034074028443c8060840000c50300130600d85070040e03480100d460480389550501099521018114101e54095641402e01c1210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951761205 1250 951759955 951759959
    0x1002031209100b010201050402030c010e0d050106090903091205030f13082407050906040e0903190203070309140d060f02161b140913110a12020108060910120206070c 73
    0x300200d000c4107182d885007400c0000701c14882c0124240c40040e90040d4154010f4000c5510350f5104014540d5880e001408240801c074040d03552600b128501e6100b0140700f80c2d90006c8100f0160702c8840744000b803c2442800800300c4454841c2a128821144c0e007880158001400c800d0016401280c40010f1280e14203070707040442c4410228804401d04200c81d8003001d40140051045805041076840c10b0380054075084c09c050505800c460400c10140c01c2072001d1109203c628501d6864800388034181659078055500d03407400745005082c008854012105c0c6080c3c944034001151103510040400b80c8d040000481d6076a1010181c00080c49042d4160103074035846070080302480f0088404405607c0912480c0c50416550030342c1c42128141c1804003540822454089490003a10411500490740260402c0041e100c00304001905012107902403030341c0c0b03100040e50034195a0000d99440e8407100640c1c0301d414910700314074101d07641c01e03203030242600301080e501030301c000e54036040241d800c000c1d8030082c0107004a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951762455 1250 951761205 951761221
    0x20d080901092a06030e0d12060305160f090b1804020a030b0c070c0e060a0b0304150603060501060305241011030708031006020c0a0b0a0e030a0309081b0f10020312 72
    0x41541c48405180d070f041030005195209100d1040f00e01c4403107000c3d045015080e10308880c1c24400c007848000c2c0503202c1d031022021990510070240c00380c0c080c100780241203140c10003000c206040c0d0780c42809803614084071803080c0c2d01c4080300d0340c0040c07014950301c0542d541c807480021040304150300007801c001043c004225511484500400c40b00d03000303009e5080420707036618190f441d442c002c41e40541c11101c40d400c20444c054500f40550b0f00319200b180c1200880960780300c4401121090350080d1a4982c64500400004e174051141c2a001002c9416051003040d1084042120a0355a00414040c4810150410b0b51b0340c41022414982c003488820b6036035803002030420280c0b41d042540d0b04944040d00f6140018900d00000d01c1c20307034803007016018070101481d18448420303681050720701406010b44c507185881961340c20702408081030b10946034040e91500308120b040c0380c9011400c4801c0c3c560071910340c0104503920200f0150314910b084400070340314540010120b081d809141c2584260048800501c0024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951763705 1250 951762455 951762503
    0x16080915160e190303140f0a03090b150f062505060417040305070303051c1e18020d171908040302060630210301091506020d08090109 59
    0x90342a6034802e821464200104002c8580d0038105140065540c00100002401500d00303826608035025080d0070700c48080c0c15018a03612a4207000300003a5140d426004004080c84516001a200c1c4520310001070050089040f004001d60045c1c0b0a900c04140c0410810895540b200b1300d611288411140c4580d51030401d03034800781501c0803111142000c1c0c0000b440c1c54402d050314200d03900b000003006083d107143c40076144e0b9030140e099a80c028000e01038181050b1440d00407100803d003c00042c0040d07855040e80b40086480303c0240b40d60b12000010104003607550042001c0482d900420400c0d4000c005008154542c400c40d011007035808104070b01d5840701904150468451800394083d0380040d9030f03480400c05142094440216280c4c0c202c0750f602d118041c03240a031a0050140720845808501901a052400c04041c0460007070100000c018002007605000e54000d0285407403c8032950380c01c0080294441c0a400f40c42402c125540000a150002c2504000c02c030a030441c207203010404841d0891240307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951764955 1250 951763705 951763741
    0x11040f0b0702030f0328201b060901021209040f052503022502010e060c1b100507021c3e0a1701090605070306050a090516080915 57
    0x103e4080c00070b07210b850381400301c03c50380c00c464011403440c010241c20306024a00070f4403d0200080040e8400c15044a04040d8824428840342c04000c10801d903140c0c00c45176440204248090140300b060200800a98000840e04004c041d203811040d103920b2034102081c0100640103101c00f0030340c184000d1150500c0d40a0065841061000c8111012000000180c5c01e1344030310b0328000c0e0300805410b82d02c0a49007030341e18466000f074414505003100070020400a84a50002c0a07500e0068000950740c1c81c010041800e0740a4040050303540b0b035460300e048440a445405849800780c0948010b0300c1c804441010381d2081c1c12840c0e40f0001811800c1440c0c0409411400c840f00c141780c7c2c20800ca03481e20f070260010950702c1d01620008003500c20721030808412000003000200600515903d5990000c0091b40a000d0035105080d103580c0041e155103400e040205544003a803104003214546802c0c000380900b211190441000c0c03078288440700c0d03102c00e10a24a007124803000d0034880741c00081480222800040741140c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951766205 1250 951764955 951764959
    0x1803010f0b010206070c02010e0f032508010b030c0915030f120315010c020a0303140c150603060c0a02030d0518030307091e0f030f05010e061510080f0a11040f0b0702 73
    0x7102d81d181c0070299100d002c480d4010740849c031558006c03c1c0c036290200f094610358501409555009900030051107007101c0750401c11504049244041c0445402441541c1c000c0342c0440051811b01e900b400481d105131000b0b441c1198010101100f8821a01c041180c0f0315140f110308110752003050070a14102640d0801d80e900030f00c2400da19190f014035840b4815860040c0e030010105040e1519554003030307818043d4a00d6841c0800000d002c02c00c0100030501440c2001c003500aa20101ca14041c000c15040c140700502c5401690380a0100806d202e60000c1500c0b842c28140c040000c15854001d103034150613125102400140c0f00c00401c1103049540120002c00310344402c3c1442c0103000c1404985410200305d0701515048200780401040070a00003425a20031a025600000d02e11224040907403c11408849440c410900c1d0f0101d9052410403050358181a14245080030482c1803085043d020740f070b405031002811a41f108240b00108503030300100c0c3c00500d02445d04035141b40d0348440e03541040d04001000d80c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951767455 1250 951766205 951766213
    0x90b011e17030d05150d0510050f070503150a0504060b1206060f07150213060f08070c020a030311011b022104120311011107230706050f1803010f0b0102 67
    0x40c861196840d041c08103003a100180d03050040100c1c8003802014001c011a95801404e40800380326201c1d41031004845000e03401804911050304410400e4a1000c1c03d4680c1045120b410040c001e940441526004034800d500d0024007080c88000500356221900304507030051409900043c858001402000742680d094060b540964450081083c940500504460a084100b00900c002144141d003017411601d10f803001400d10184c0e2815520300c501a0f001040840d2008810a0400303030000c24645e4401c40c40e2800c032061001c80d03408581c100200340b100400303011034407031f590520020a4002007000742040060841201c500c0d10001d46d04e03200c51a1100404c07000e904e14501046440041f1000c0c0e0702040780e0b1000340c1c84680d600315001d0ba0300802480340c5540c0d90301c0d07000d51850850300400801e8050050981034042c96500c8210814044030006d01a601200c01002060741103030542c3d50500580360f100d038440d6000b40e207804400d038042100d26850f502c0c040040903c5007180e8002c816848003a4212 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951768705 1250 951767455 951767459
    0x10603061a03011a031b1c030c05100504020f130e06150f0409110603090304031403041403011a100e121606050c0601090c090302061b2a090a090b011e 66
    0x13448000940c880098043e00280101c202008004909102410f400b5200d0381e43c8084160800150850000003240000c0c036851200717050000410500c18407000b00401004a814182c0c006909028444050f07801600d60703035004041c8015951011640c200101d050720b00380d140c054100012880e015441c648100d605902c2c01c0d1321400c141c41007020041c0c1c00010424000a036100300420382d04014828415448204008030020705011844861101c05100942d2203074203090b2410700b0040349000145c02603151240b003000030300b11100060800b030010f45240c0350f141c0d0302103000c440d8080c1e40d46949401c104c1d040d100401d8000c00081d204400030080000c52001034860600300e40c03600c4ae00c8d0000c03e290b4010801485000419170003682110710382d080440e10305c3d64aa010030082d411031080440501c04980001b802001d05200c0043c1011000c10346856600020b02d10036078030042c54405130300a10515001690f80e81041d0b002600c029080a00a64035680d5041740c00c00045046030f5112007900e0398180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951769955 1250 951768705 951768731
    0x10051e090a0221040c080f0606120313091b030b0d0204091b0b071e0308010303050a0c060e0a050c030106050a140a0503010228140f1e0c010212010e0c070f05010603061a0301 76
    0x4094280b0003084043c8c82181c480c1002c1000b142d048005100d450b01040042c0c0c0d0f40c5045011941001380009074003c2810f0603846070b0040b056240b0411201818146000d03d00d40d5919090303034a0b52075a0494000406641e98200707212080000c49501c100640d845201251030700f118409814903074401c034000b44208401001400c884803850383c000300401c40800c01031000074052000b034691580d2601c1c0054590220343c840d0002d40d0450450404075800001804061040a01910000c6001a00240302141c504004a4107141891040702d21000340c141000780d03940e070f4100b020b50007031400500030354651048450700c0e103081100443c45403103803460b4200c00c008140140c402d0080d5503460f4111a0920f240e205861340503a120000d035082505002d051200300709008005070100345915000162102501c4c18010321401c41a0891801140d03054200309904605800b00d034122175211113004581c100501d440b40c094520364200030455404c10030100a06451110305000102c42140240801800210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951771205 1250 951769955 951769963
    0x60c0102071e0804030803070201021c09020f09010b190c020a0e060111160308030421083108090105040e04060506150a0e01030e0a05100510051e090a0221040c08 71
    0x14000f0038050302800200042007288015647c001400e00003d4500002900180d01000e00816124142c5940340f10b4441075003006050807540c000e094611003825410007030031503030303501920303103071241e881d940f0f030500d850491081400e00d07035155024103200e40c1035460720409c1040502c12603241d40022048046040e1002001403500e20803082000032201031403c68698485d00d41c8010f1055460b160000700412000902500641044005940c0d06034142040e102105103440750451400e4450528200da045014104044800255103c00341300ea0703481366080160b605001d194000d90520345c2c0c810801080c0300042d00320510559044595500b85c2c0b078401100350b020702541861200007145003003074001030f5010381e0005d5000c2c03050800b200e401d0f21003a41e41500d03241d001c0c8448526070761110306012a020f004014503024000444007021041c00ca560303804071805d0001c551a22070042c02010907a100c03482d6040b00e050032030710245d240c0701c14100340300b40590002c141c4089070307020040030300003c1680d0081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951772455 1250 951771205 951771263
    0x601030510060e090601091211010e030c0a14040e0708010c0201150b0327071805090708030304030c1e23062403030912060403020601050d02010c03031a060c010207 72
    0x5114803120010070404d000d40040010720f12410300004c6e110100b00c4001400851422500c00c00c0100311440f004c01c0010183c80c4500600b50081d88100c1c10300c800d0b55203000041051b44c12003020101d601600c0c50002c1c010303118004000945000744040802d45036011b400c1640314001c10f03002030055645e010580200103120b0711883d01c90040074408200c0c13101c4903441c00b2602d05010300100c0110102e50b4421402d2150139400400581021200d0340134040d010701420742e01c40070f044098040186000300c481c0c1c40b880014001070801030058000b504109070383c5480c80841c80c5407212081d10404500c0c06610744505006480411fa61503030320180300318800183d82d0700c609001c0481d22504031083e24042015402d11a03441d80c03500060245100940313601d10207410404001c0010300783c904090801038104070b03046c0c1050703000309200800030b00540d0b002038864a20136494600041c0703c03e2002d465160034441340390226440f2400140328003070b050054028089090095881900c401c01d507098440c101c1e4024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951773705 1250 951772455 951772457
    0x70b040303080609070c060c0c0b0f010e0412021005040b0403020f0d050913061203080412230a0c0b01030c0f080105090d0f091d012d05120f060f060103051006 70
    0x2d000140682802129540c1004a178100755012107400e17502c140544666140c0c180018562418800c188000444802e8000c1c4001c0007519103541096880c10402030003c101400d840504030a01403890720070003141d692158500c0040000f41424940480c0865007030780c0c194014032680c1c403202030403140850359800d82600b5072101c0d0700c1c024207402400501e00c580109482c0c800e940729000030f02c9000348914240e000d403090f900c00e40c91749480e10300046500d030312140385000c116482803120600900582880e103141c8540714104d40741c072488032080342d46580c0004024102d45917030000008100c040d051590580d081003d00e54032058642186c51708803141120700c90510362041420082c40c0e4062084455803945604d00124255205c0aa51b090170321000d0f41d81207c0702c0c96500400010a0030840c402c603100c4100e150300c80c900400f40e00d20504040d18011603116410074a1404e841d0315080181d0703100100800b068030070700c0c5890300035500c00d0755003280d04a010901703000000d102c9a0301502494161441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951774955 1250 951773705 951773717
    0x311a040e0c090a03030e12010e010906110c070b0702040f0c2f03161e0c0303030c080c03061e0d0f0506070c02031203370627020c010f0914070b040303 66
    0x1444d141207614002e0800c6d11a001640789100701e03440c1c0030030700592115070416800800e9401152403c3c0045a510010907815001c0a00100e8603010f8041914030440364101d820740e07182d441c0d500004004010003503e1011551800701e0240038103404c89032007844a49682c4d10348909942200815950f1700e500c4000c02c450750801c1001d58080c100300c881021091b4010700d00703941401458800d40c2c2a102419030140d900c182e84540c200201a414000c07c4426085480d10b0045420414020300d0b0703a000190203240f0410119509645d02c200c61040341c1d0300800020104a00070641d4100420142c0f50300206485a0080304001002d40e07002d41d51344128141d0160040400002104a411850700054120b1080c078658054000d99805031004098803c2088a4035051b03070781b03003036410b0004c40b0380b568044c00020041c240c5807088103902c030303812003284036001704003581d1a608400c2c0e0600409041c4d003609a800d14004412040c425520b554809800c2520225000207813621080304290040348001000160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951776205 1250 951774955 951774959
    0x30b100c3c1109100816050f011d091e091b131416020c010c05032b11070c0e150f0105071a1b311a040e0c090a 49
    0x10700c0100c840918050b001c41003100c082400050194001a1599041000400c1c810711604034140028000c0185075000182c81d240361101250131012048100b905100c14612013000702c201207035010255103030003801d41300c1e2454000c80c1e0b56103c0050f040700f6045200000002004d07814005181c60548824130010001c3d020381d1010003601300710013a011001181c580e203205850821080383c140c012602d01d18440c01c40c0c0e0198a0003490056060310381c0d410401c286007154080740c40403086403a0541152014282c200344258484981e401c04178180310f0b21031610010702c00700c03900f030360190101911440306031000c990748645072002807806030b0b0040784040d084004221580b030000204000c802c810b041036030a00350551103842440480552075618102c0c407500300103d8602040d040000901c02c0c0d050f8900f018000545205a1030405e4003103690614804285540c1251a0056038010108001c40b00008030084001c40b4094009109000c44043e8200100e111008141c6c2600d40e00e00000e05034280040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951777455 1250 951776205 951776303
    0x5030103031e2f070609081009170708070b130c05041109210d17010b0a120c02010509191a0a090206040b0c100b03101e09060b03100603030f03020703030b100c 70
    0x29078103108468010030300108141120388200500142f1f401060107984609140c101000003400003040c0050320351001006000027440f410641047c0d0b0029240040c03801c0310001c95a1041c41442c0381d817544006040151030744030250704000d1200c5491042a0f9050340c180c0075054502540e124400000e651605005001c0c04011340080d0003001c407145007102070340480c500904100c1e51081c0482c0c0060751036504005e83e5001c101b000103214110b40c134400500260a454841290140a6200c0b407956114804100a2051a00074a9034141c00420389a0798039940c85000340550300c0b02a10302191302a04120000103007181c0300f00300d001c40300940134165542817008510b008184019402042d0a24011300e040c1072205440b600b080380b88562000203102030180109450b01d100040c40364401401d000701400006d60150001001540f1420050f84854161600380d001d0402c0c818002c0d0450144010940c40319804107070080c1040c02908c401c00070b02186809041e800d400351100c620b04610400c0340100704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951778705 1250 951777455 951777461
    0x70b04180906020d09120824041407020607020c010305061804020112020f040e220f031e120b0f03120f04030c0b091005030103031e2f0706090810 64
    0x101485400001d514512942d6001c100d80141003034401040c0c1d1010090100a104600740514904509201c012443c080003407039501c91180c01361600c2d2204003a00c0006507101c03900f0600106101d400c1010152400110080d5500c00840300c0c500184070300e00103114a540207214950250401420f220103114200202a21941010740201d0410050314010744811400c1e1001d0070281800005150b5214589201d1194810010f0b0440a588484c000d0f4000e0114800c07041c078055a42c416030204900405041c15511401c030f0b26948040034080100010b0160b41c040000014090082c00401a045d0500184086100391400b415099400140941c4280038020090010140c0880c030300d0b85003d4803551150224561681710035102d0300041100d40141c0340c02250700c00d288106281203815585191002001405201030401000301525400c0304050300c070344068104481088614404030031210a03000c1c2d8855540d14042d01406807001c0450345501c178103020b000310b80c10034005040c0240100001402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951779955 1250 951778705 951778739
    0xc080a0905071a0c0708010614040203060a0905040302030c0f070e0f100303080916090203150d05100513060911132a03021b03030105150901020a06110c010e0618070b04 74
    0x1e2010070301004100c4e440420030703400a804214004038802c2e00d4008109042101c80e80018850b60040c0200116600c0762100502200c008050220b81500c03581000c0c0d05512424900c20201c1c0101d9503142c0c0c3c429000100384003260b036480302904c0945d82d00066211400382c25641c40f00300c00840901000802c1c8071381205508401c1312419078048141026459030001c42c6544003640b101e07004000c000d120103010655000da003d06840d15614034059643c0d50742c960b10505c10f200380345076860002c1001a0a980841d440490f0b00c8078081240c10480d0810035829520030410364070598000d40118044480740c041e8403c40c4030000380c04031807070310030424020910352000400400c02d5800e105403051188012141e1001c5148007024643d80d50600092007109228241000c850040c01c02c580c0500d039a000a8140d103840d0058000070b902d04001504400b548251304526002e582000712454104501090150280015130082000f0900a02825448482034440c05540480274003040054070803110704404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951781205 1250 951779955 951779999
    0x2402010e0f01060e060f0d1e0602040308030414011a01030509030f040e01090e0703120302090f1002011d07031a0c1c06080f0114010b090406090f0c080a090507 70
    0x501106403480325890003400c9000718945a4403050100b091007040c2050f00c0e000301c0c0940760070f44094420340c0404c5800020300801080d20044a40c541b0080048a51040711240d010344199a503a5990809045c1500245c40685003103840e070b141e909084005100c5c81c012810b0750100711403000040c800560060500500d01076080c007040210900c102080d00040c4050300c04082c00d03183e5941000040d8045846428441071030750b1040e5420301c007148081041d160341460a1501603510184100480d19032842c4100031600300355888004500c4680641103007600f208140205c10900190354155980d82100784400341203158600607003100d0300310300031250358060040c1e2002851b03d08904500c40b401c0c404030860a140b00da40e01018041000c060100d81d22504c245002804152042c0c00f91500340481845142d00c4c01c003000500c0b0516860780e0700201c00070078410004201814002070018040d0401f49c44410000f885030001424100f40b1784134060065070000010505541071000c9182c101c0344182c031800c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951782455 1250 951781205 951781211
    0x5041d0402130b030106030213051605030c03011401030f1506020c040204030f020108090307080a0207030b0123091017010c080105032a0604080a030c030f2a2402070b010e01240201 79
    0x400075031600c9d0b00840c3d122861000014051411000001e14481e10481c460300b081410001d10507503130011010341b4152034100d443c517103401a62000507001801080b010300541400e040c52840e1504107070b80c0c10021a17000b40c0070303a45450318481c104800c910841c000140031881c0407030300e400954810390701113a01c455100d08a0b8036007403c0e51206c03003054000c25110401070788404028002c1060510380e5500501001d40c0f9114100024002d6040c2186400b450340d0040100000152242c0500b40c45480103103941d012503010401e4003007840c0c2c080c0c000607803e5004559100000034a5080001f131034540d5610b0000550080200d41d00307003014026014144580c424030900010521402c1440380ea00207922903203c42c259249145005020110b041100505002320300c2001450391900070f07c0300c140c440e103e10b0f40b0b0a849071076141108024960065940b000c51030520090808504e644c0200002c5002d400103e9550f81d1319800c0b80140c07002400f07072050030340040080d1903030111250070074286001c042c0008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951783705 1250 951782455 951782459
    0x60c020703080f030601021b10141314040b010e03030304080a091d0f0a0509152d09010e240a06030629030a05070605030406060e040305041d0402130b030106 69
    0xa1035443e00041100d108028002060204075a010400c41040b1607606040350102c1c3e00d0f0000183d01c6110444030301050128400404145910304030880da00c1c035045030481090f8030740310204805480d40c41000b080c003403072600100c19140d41c05094020700b5404005d0045241d541e0b02d0b03540607201d4102c029020107010420034081000140451020304200011040a85074907001c1441101440701070115411140740c0018000c001002040488503000802200c1c015600daa221002d44178070105041c16810f0309001c2c1d01c4480b01c41d0020f005008130304000c000e000005043d00e070342d9220f0b85141d051002d0140003040d1080e4921714100c18681c811080d420000e01c0a560b902d07a0400d80d6203452052011070164110304220440c41c1c66110480c1109400410480c002503480e10358a060501501d4248030001c00002c04205443d0004400303005408000501b1742010314010381f203a00b140c0141c500802d9214141d050341c4800d07103400d51046030010711101c00c01040105510040c5413449006815540790000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951784955 1250 951783705 951783713
    0x2090718030507031202160f0b0f0c16030b0108032704020c010501060f03061406121306060312080106030c1418040614030120070b060f1207180204030807060c020703 73
    0xf44000842c041d80549412a002e41c0c03000b8140001f0104200d9003601c607040a02030000e41401400540305014249aa50101c503a0041040d000300d0743d4201c00d5200e0049603c458500045c0301d041201d00c01c5002c051240d80305d042e01c6859000703c030003000b80364442054520380305000d00c10001907204003800052030000a4888c1900b9940240c00c00004a11740000340707441c082e8144203820040c0710f072900c250854a0400c0000c1c0b094851000e034140c00c0783c0404007180042c1c208207809418143c1c00b80c3c04105040d62880d00c400c44207040446080030400c403030300000b684d90003401200b42c00a1141d44018041d4400c070705800840c1c000d068030807001d18100382c185c82262103d204d008042c00910440e807410040d50000c050948201030004030410301901910150300c4d242e03401741d03080e00340e08c0303402658240d541790b01049030345001c880c40f140e2051908400305000f041c0440c0c80000e48105804d1880702000d45420700050744100d01c0004d0403e0820001e80000c200e0643c880302c03400d002e43c41a20400741d6241c131 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951786205 1250 951784955 951784963
    0x3070c0c090e0f1b01020a120323070f030606081801020d02040806250f0e0f100305090f0c0d06050c0d020403140105011d0a0c030e030307030905070e04020907180305 73
    0x11001d885a0f002050750030300401c0420800b68000c40140c0340c1c801c40b981c8000001d496090090000f031000c05c2d0303105084000d9019820800c1044c0c10b01d01040c40c103400c40c034086a40e503c01034130b01c480801e4101c0034902010f40b00f07000d054203681b42c40e21240c00a4072050341000d903048461503021005e5500303014035200da000b40d000810062001100600c0c0904001e0400c10a606002d840040352070640e9081010300e44d040b9916441070348044c20001c0b094421540884c04050350426a0b590241e2480c101d00d42c915016030000b8002c05c0303000103d0356040c3c42248160743d500d031400103080d84170559985c800c0000d411030b00500d40c800007816940d400d00050100040a0341c00035007044869981d1481c4203030142c0000d114140c0100316903019524002c0005e00b9100d1041405040e00075240e403910140300c0c80c07034020f4100440c441202c10440b5541c0c64011001001814002c20841d01400f5201001500c80702c480c942c5805160002c00d4008661907415042d07030100140f109098a01e80710120020110300c1c180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951787455 1250 951786205 951786221
    0x512060108042a050319210311130e0f0106020c0d020d05010903021f0506060d0b010203120a063206030601090b070614010b0724110403060b120d020303070c0c09 71
    0x3c0c56041c15079007418201420a40d030314041c800b04018601c8074002069603601a40e00000076040c040d204608101d070304402402070147d60b61810140080e05140c510440e465607401c4412403803203049180c03900d040c1d040205d40288220070059012844090241c50080c90b0780300c0151004101158103c401d55426081d41c09a08003540543c1002d00c600c107042c40e500e5130818414104900c104114508080007a096014000c0403c0016994510300620b40c1d000f0400c4503254840e003000c0d02002d240c0f1160b0000038052034026944c121380004001e440103282c0000d4000307501121400c1d46003134180c20742402455040101051304000d03030100001200c03031224000f00b004500505010540503003940c001410a00117a110300000700080083d01c02040c0c101c0605404000b502c040c0c5108148046039081c0549243c440250ba41803001800000f040816404503038075900c1a22800e40002c19030300403c1c0c44c0c41c3c80c1002207025800c05c0000810b21403040c0c031107806561145100344902034440c18100120f45c544 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951788705 1250 951787455 951787523
    0xb0c060c0310180606020c010c0c060c06021c0903030c0c0f0206030901110a020d080f15041109060d0e011a13050901110d09060518031e07050f07090c051206010804 72
    0x741c034090181c1369047c844242040300c00e00740300040c603200d65140c604110503441441c04002d0000000f80c1000a40c0c0c040302c5081a49281072003100c0c94000c1407000a01403402d041b40400d240c11742c40203245005003104102c15801146100c901c01c0c0a80a01080b54401003482c0311a541c1c7d601c03103440d50f1001c88050701c41480c860b40241003404250a01401100b0094149050901e8000800488400c10b0301840c1c8000000d035008070341a00d490a542038540548800350398849400f041d03184042c0c0e215400245828050b90080c4610700c240d0070f04609003079a8a041e181c00100040c110f10511340d060b005250030074014800010651100000ca030340a030850303541070f050302c0d07220a07a02c030a1244078050304d42c100d0318104140c4a103180014141d60b45c0d2140030341c140c7c1c041e8204084201d0088c410f100f030b0740820b5045015501071351000c0304010f440700c0f428000c0c25025032030118802c610303c3c810815111260388568002503145c44c0c1d54010343c0d500c90300401c00c0741c00402c04503501c3e407003041c014141c07035110300381c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951789955 1250 951788705 951788711
    0x90606021605031b0d051011120f06010c1205090405190b10021b0d120305041509020d03121e06090b060310031101050f13050405010b0c060c031018 65
    0x2484036401041c0400307074480d6109902100301840b98400421800c0c05900c011038459414480740d00e42503003407020883d0425829454031401405201090004055030070903c0e43c241002d5070b4495441071904016101940042c0005903440c0000322203060300d65004660b8146141072804140000e0144e41040320201c00384c0d0305102c0b0350340c1007003400d0003806101c0e40203d6400b4007090901c0402507882c212034070b541c1042903e043c000030031a00e40745041e841490b007118400170380b990200f00160141c4000d0b030f4100c4041da0714071030b81d4482d2803252060004071580140202440012034074115088000303051030f640d16680d0380b038030401010388400c41031424682e4a003002c03404520300003400d001c0702c580c0e000090154504000b00b0650b802110304041c2625406008020203000141c0101e50a0044042441000720300044030307032581d00e0302c074011421210200e406020350782e03c03200c140500f030040b44d103010019030048000c62600061800615031290500c0c140b20300f1140c0c1c1d025150316892800c0c220701100384e9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951791205 1250 951789955 951789973
    0xc0f0415050d0c0507051b040f06090504111c080f0d0207140d0906080a0903111207120906020d0e0114070303060911040e0f0402011725140d110409060602 68
    0x5014000c1c002c6407501030402a0401985841d040d032210999002060500c070002d003222048c6e5213591020030003107580310003040b281d40c5039448007005110039a0306507103040752442042c030345151501c4404a505800e010710b11015905030346812454109801c43c1a040905000d00711101500d8800360541d240103080d8000c03010744c001c040b02c0c104000f80712400c04200d20304400784a001d801420054004172400400181221b40d03003412540800c5020102c00c807402003004091ba0089018040c00c1500c3c0034043c0700521140e0321a058030b1a6a0078495038000d1b800c1051501c81050289540061380d101c1070400322030081180d07142c11201d41c080b52040f0042642c8440902026605101e240111071b0b54400d118035080c00d14400e11003042c001403000100340b02920014046903c91101340c460380c80c4d144d2180c002d07414000400d4040c2d2442c0700b42d030514180025130b041d403407038850080c0000034006031010500d0010480600405407100341c0c00c804003480108000210301c0c429114040083c00c859028080d490 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951792455 1250 951791205 951791227
    0x804090509161a0f0f21040c0b16060b120303130c090203040f0b091002160b060f0a091d07080105010807090902060901030216140609100e060c0f041505 67
    0x4500741d0004442d10034a2068690f10075420000c0780c0c4000382280c1407944070980700e24115540c2c403400e00300e01c2c0550041d4000744104100c100385280214441d4850020b030945811000145000710707002c0023007004059a09001080440c2d01c001d00d01d85000d404002c40c1855503607141e1556005592180700c0030741d610040014803c01e460380d0000b42034035913000d51441c1850b49601c2800202000090503d6444d4008134119500400859005c00f01041c3e040d0f4480d08104c041c44c0c490031291006032401c1c01d96400242c52490020184040504000c1c0b80d05411b03800c1c142944000e11b4020382d01d45940105660490134042d08100c450300070308145002040d9503041164003810302003c5e611a030030241c2000c641e140146d840d4402c0d10400002032038016110500510304607480900309030046c00e003112401c0310202100001c1805440b815242c000c450f190216404040200e400ca440c001440d40c000e035010952150300318000b80300309100581c00e5030400d6142c0302c04c0c100030344621201c03101241c00001c0e400442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951793705 1250 951792455 951792493
    0xd0b060a0501023c01050a020403170307080c13080609032208061906051807080c0c071814090d121a090c0c1f0f110a0c0804090509 58
    0x740c4000e2020301944000e46601c100c1e15102c03c4500d140000c101d100d40790581d2841c11a185150502100031702050401880c8580207500038001602c2d44e180101005032880c1e00c1074216400341445540d8088255198610745541d50010040402241600c030000180f01d04104110303806080c40344007851b07503686000c48031840000660045810152805c40c00c00681d140401c03038643c06120203050443c04203040300300d800100388942010303a00a0440a80881043c100d514140c4100e0f40c60b1169019a1a0500321f965240240a50760000c2ea01c00300d000e002ca1081c1580755884803109d0100031030300c070a60b011466481c030f1040704c501410342d01814190105c0e0760300c0102d92204000c811400c0028181030701c9190040d0f102829030030300541c00e48020a080d01e2119089440c00c07808001a640f4024103c01c42e80511180620b64425946c18500c00f195500326501c0b5058255952400b010314000d0410015101e610007000c0644102800b4000050070362700714040c1078130a1900002030700d18494121444101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951794955 1250 951793705 951793709
    0xb030603070e071413030f030c03110102041a0f09092a0a0507030825020f0c0a0b0406180b0304030c020316030b01050f060f0c0f0d0302090303040e0603010b0d0b060a 73
    0xc0c0031030300402d0158954115844882c1503440d01e0301315581d40a012480c000030b001d554801400340403d010f5180c1416400070440c601d040c8682d139071409170850f0200e002e0030303402940030300140a061a6692060342441400410300c2c00b0104c0089414044040001408810211707144120005004908200d06400c144018000c5c0d9141400f5400c1c8281c81c00d000700070b8007800f00001c090041d240040341e224040304c8010045503103111415000c0f2140c0c801c0c02034480038400303102800f900c01c0e1001c0540c140340c44803880050b9a46032010900345450080c0895003101c5002c20b4091922850f4001f20f080b03c140f1005510480c000c5d25502d00f80800c600c1498546030518101390901c0d0400d20701480000c580c10b16031411141e089a042c80001e40080004600d44603400580b130506d0740018103131850840118580f20000412410744188044106059040c2d208501d50103905400800c0144a69a0018041c42d00104050300005100b12040d011800880c41c031034069800c4041c030700401146103050307160140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951796205 1250 951794955 951794969
    0x120c060a090608100f090203040501180302010608070506040e04031b150605090601110a14120304061a01090f1e080609060114030d0c0b250909050c040e07120e070b03060307 76
    0x40051524004603154000c40c042c00d00306c0c0c2d4001001c20144042500003072161912520203408501080c98064020007581c82254450700411000140341d1030064103032400c40e032508200c0b1000d540c2d50707034040710f03071010103c1035034408107840e0721200c0807465052085940c0d440302c0c0e90016010f4145010841000d0000305118100f1500342c4c42c05c080e60301c01141103d1043d5116011484046281500c036062050031501c0f110090400310800041c4409a0030445030384150740304102c00d004040c03004664420280c054641040d00104041060311903451280e41520800c02000100035110008141001d070291091810340c0d00400051081e01116074483e510783c1da003100140358184c400b02019045890141000c4d0244010000080240120a4020078840c0b100108403454601c00d0601900c5444180110540b50340b60800094240d02640e045406440e90410340c101d66540c0ca210450f580b2201012881d00c05464002006503440d04004620241802c1201c481e143d103099414907150600a502c115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951797455 1250 951796205 951796231
    0x1020a12080708101d04150906020d0501052e0e0a08030a0908160b0304150207080301090522080306031006090606320c0c10050c010f1a120c060a090608 67
    0x45500d000e1005c80c1d424004602c0a410aa65507003410700b901c41092400040040c2000c486808010203540102040c0c480c0400400c1241d8030780f020b11101441c240c00403900201260750b03504407a10f8500014841403500d151102e46d8150440c00314800c0c00c0301e40e2128003580c1c0007140501001d500070103a070028104c0d0a0040c020005410b48456042903607200d160940032001010405101c40e03040c00c10003807000400203554442180c82c15401543c024807030000010306c0c100104024401d00c1c0d4101010404015503183c2800f9141c07215030195201800c0030354184540d8030700e0400110103003c4c1a000300403841e400100d461501030050201034540d4900948200030312005e40c41c0b0903500f0b410383c0815214000755525000303455407c51800c4100c07100d095001007100045454182e10400510349114464000c3c403032407050925010175074078000d4000c00d00e500c142000ea08542005402c03603503420b02280c11a502d01c000000442d1142d40441d800f800098143c0100f80070342a00025265040b40d443c82d889 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951798561 1106 951797455 951797459
    0xe0a051501030519150b060c010c0201061511100207050a0f06050a2405091003170a091a0904020a030f0c11010605010912060b01020a1208070810 64
    0x1c599601c1070309007034031409103001d1500c28013503800020076106190045c1d040300505140303606941c200d0b0042c0941c0180c1c40003405040502051a000050481d0601c150403000a00c40808003051005600b0401c01348280010080902805848010303196007407841c006091405460020301204103a058040903c2015400a80203201c400c4003000600912448654101150744c0d40c80040d01c00090b041115040001216900143d01142040c00a440c0d542c1c1810507000000b981604040100b410204d46800c0000040900100308071410f001c0d00c517880201c0280f04004942e4061030700898482c8440303000341c100151915100c04180300c5803901c5000240610640e0000509560800c1c0e000079071540510034100c03d444c0090702d41c1001d1212500c0d45005400b8401c1400e04501c036207004a0041480384403d0061403965598034841414400401821500301401c400302e8201d2480382 = true := by decide +kernel

theorem cover : BRFrame.Cov 951618705 951798561 := by
  have h0 := BRFrame.cov_init 951618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951618705 ≤ n) (h2 : n < 951798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
