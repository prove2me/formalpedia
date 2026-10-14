-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:27:17.023092+00:00
-- url     : https://prove2.me/submissions/836b6740-9e63-4bb9-9c55-8ec780b6bdfe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 276079136 ≤ n < 276258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 276080386 1250 276079136 276079151
    0x1107081903050c0c031c0311070206040b09011103131d01031221060603060602010f111801200a1505101427011a0304020901090b130912030e030c10 65
    0x4142001c0c20040005d8046c091b0741c10110001405242e44003899080d510708210122801c1405031060042c8900290454402c20060040800d00c0010709503a82c0c1c140350000d11031064400e10380c11500700300e040c801d03052941001440301503103008884078080c0f0044a4451190b2443d107846d8803503180324001c1c0c4144420340c2100c28031005a4800034800c1c41ea41c1c141030190b00d56a14005008100a1084400652a041d040056000c041c0903c075141c4e08071189860403c4a917100d00960f071404504141e0501019542006c4c020b1000c228040313000e405035016009001403402c0042e000d4490301c0110140510708001c001000c0c2d0060041401d0f42d140c501c0e0240514820404101c2c805941c08000c40641040c01a2107450032080c007015059510b02c521202c8206422b141c5c1c00c48500090b03400951000d02c000040c80b008440d03503c001d000b2280141040e82c03d004c400105c40844401400580725508450711210031103805000341f2180c0d41d1aa40250b2030040701c040e000d1307101d51243e015880c0d1103490b00030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 276081636 1250 276080386 276080407
    0x4150201021e2212030305010e190506010203120108030304030906020d080103061d0f06072c0f01030209090a0c0810150804170c01060503100e06010303050702060403080703110708190305 82
    0x11000c2040d0f0b400001c55022920f600301010304120005085001030704000021403030300203a580f080d00036205c05d40e11800000240311500701030300b8028241c504621044c824a902a6203680a0900030b10071040512b03600c3c2010b0400400c0c100154221030305550140501803400c1e41c0c000c90450449811450005544504071114410300c002c40320600054882c0031080d500008004c1000d50041610741c84018031070061494502118040e0400e802642032440e000c0b82d51414120144448003005140040c17030540030300001031b840300b002d885411600740e85001c181c0005811101041e0045002507031801c89914040422045040c0180700c4c80420032300002007410044444482452650b0300b10a054a43c400090350300c1c020000c1740305d8a4440c0c41240c0c482c0342c031031549102e85250ba51541c00a407405a00b142c030140c6181c3d000000498102e0070400c000008169000c0c09025098441c0d40d0f41d0545103540b005981c41e0118030307000210310350840480c0301c1814004240c460b01840d4581402501c0e1400c2c0d20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 276082886 1250 276081636 276081667
    0x5070521040b03060f15091905030d2003040b0a021b0a050120060a0e1203220804081204052e1b020a030b060a0603020901090909020d020a03030504150201021e 70
    0x148283c0041003d0701b5041280791050240031009015110042021405072401d03103004034070310689405810001e0030f155481d2040306091a010f01e64011580050909030080346135074410b5218014420700451308a52103507042c01420000001102c4125925140500184a020a61042a051085000da40304103e552095050714400c002019a002480c02150982c09001000030b141803900400d0102b162a88540054a0040b89901500c0131100701c00c4003503e594112a11040e155813509010000d0b68402c1000a40d4044220b1742a071a00c3c0d6103482c05000c02d042041c03803503264a012001540c41f04049602207145c03981450f01e86000d60380d07081c082070380404029450107508030038444004810b00c0084046180504416516070038400d40d02c4204408a00480084c01e0020b104040308014951603900721442d624001400000c40d40c106a00180105045500c100d020a0011804106114060b1000f0140c5852070000b5458607072080c07595003620f03100c980038000d100400b083c075051522030407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 276084136 1250 276082886 276082909
    0xb03070c1406220303090f060f1808070b06060403080a09140f0114031009050f04030215010e010315020d0c020a05100b1302030408040f2301091d09030c0a0305070521040b0306 77
    0x8100000070f007c14100302d80507141d4190060112801c00c081e414008800201200046800409160070a4059078459115480141c2132035170140302030001002044441004160810040e00c44044c8030303150880b0300030142e14041480d8030480300700d240d82086982007000d841310311617175001c20380e5281d4030400080031030318003600415501880c00d0204803201c04410403080c000e0b4040d40869202e00e071418001c0712020401d0042940b00c5046d02c0c01000010155405005410131050001d401c0090b031070340170400c0b9030f0791000290041c5e00806002051000601090300c03440058903051010311229804641036594a0062907081540080081e0500c00c0c0001602d01401251000044c1c440c0d40c0c51050018124060f4514401c5d58480b07007480e00e542c0980401011200314180d0200a0051003039000c0141100501017030041c04100b0481d48010414400c5480c072a107e034541503141c01007400e0076031400702001c0700d1500f07107124402d2401203044014242c608945180741c903107541c1d9481d000400c081c031503031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 276085386 1250 276084136 276084143
    0x12030c180420030a0f0207020a061b022d06041a1b16030c05031c0e010e09011715070504050d03050d0c030203010540060b03070c140622030309 63
    0x50714400d0ba511091400190b0150300c000c04180201c0c095000110124890303c1002507000c0301c000010030245010b11201500c050400c0b0703d8144c01d10640d008224840703206404c04074200050043c0f4070410680c55801d0f40148415600c40b404c00381040e64012410824000640d186040072401e8102c10b80b0740007400c1d807200079500640d80c02c4544a15a0b1200780000d0100300e4800100c92030204460400050840c450103901e0070140440c0040002940c03012182c0c48200d0410116881d520900d49450404600038801e840300484448240b1340c0e0303141080507003440b900e4000d40d00790a005440703070311406503016224215141241f0402d20303c0c1c195403078410800c9000201c0e003811000c041c0950560b0186040362002d40f40c3c0c00021801058052070755102e0b03810076980321b07074041c2c1c00386800b41e0402c40a000c0c0451000005402520f0b9540401c1c0340d0002c0704c00800007030322441c501d4200310080c000e10076240d107404000d200500b07010181e002c0c12841510041d10107140d42c03881c001858448d0700300c51032480d00b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 276086636 1250 276085386 276085421
    0x908041406040f0e010501080711060402040506041803050306030d0905031e0307150b0a0602011e02030a020c060c03042904020103020304150228020706050403150603022112030c1804 80
    0x130342e00305413100c0f4902403184a02242000000818450162064030045100c94019101c2c80d95982d007000001d0102500c11a08240d58881d111103611810510703112403070107515a9511b901e007003003c00d46041c0910920504100b40c8190401082d10000b8481188006001c0400c0d07400c40d01102c44d03032443c0202000582400c604008203c0c1c14101c641c0601d10900081e11a40c2c6456102c09060f4203032028a050220240c19040b0940c0c80300307134664081d580100103948007525094000305c07440e00c2c004c0143d1307084c0740709079000083c0001c016941c0d41d001d4240300e500400095030f19001582c12000c000081010b8141a0008006420407290040405090450000854607034051542014207160124410388203407000c101005041d90000400e10100c8540c2d030f0b14185410b01b185e542c1c43c0d902040b151020130b055129100407006039204003004404074a170302940c1002c0401051183d03e00265441104241002001030016403414141141d445100d8000c8020030729400c20b02250007401d44071044150b140c1f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 276087886 1250 276086636 276086639
    0x303180301090f0c1d0903120702010b1008150909060a0b0103060f060c0309060504050609040905030c1e060c040e13052d060901060b04061107050a03060504030809010908041406040f 80
    0x1115140b21801c0e00c0e031600945d0f50580700d0400c502080d1009607032900c06a441882004003282403044190b601024920011856880a80105024003040014400400c82d814204402400b114000010842c0c045440004a08011110315107030740001d03011041860701c0c0c3c50390601c0c59000c3c5c2c201030001d1907500d042c50541c3c0e80d201001081c8548011007100010143c05c4c001035454440d0040d01c007500d00c0108050700c0c15a81d0300c204001008001c000f103d40e40400d00004600400612030710303854000c01440c01c44a1600c243d45d00b4100f50000b0864100040d050009001c03110000608941c081003480031586400b056061440c68502104c4107202520740c1c042248210400742d164a02d80714001208452a94503204030142c03d13110035008030704040c001444104051440307010450002c072091402d40b10010780311404a0261581a0400e403003e17901d0390705100405901064a95226410900801000e0880d5841c201c141c0b08034420780c0103030002c0104c2e054941d95110211402071481140344045107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 276089136 1250 276087886 276087893
    0x90a0b0307060f0806041a06070f0c06021e0106150323070203090307060c050c060a090b041e0b07020d1101020102040b16230d030c030216140105070504050303180301090f 75
    0x80c0394010800d400607044c4808103800307060a0061a00000081d10300e1130302001c1e1013060000c150481c482c140c030201c40b04100c240205212850010103090b09138064107185c85210508000d01124080d200442e0b0314004003001031011100204124022520300030603580042c01032039564100d8070000c0b5244844000600c203660350000024407480202341d00791b4003d40d170788980980c3d0f07801168401404c2504030a08060451a00c44020041314105003080381e24070351110a1011a40c11640000554110718040d10000d200c80300030300002841e500c540310303103041c8090703001c581410300e4404000d00d0711120410701c03083c582c000c0d016500070705042c40e1300e02c2e1541744130040d16049540e41c800c1035440744814003076140041d1609911034462900d80b402003104c0d00c40f40100300d005040c40c0c0f15000402d5401e219819180a0b07002c0e0600680d40681c00340740d0708461881580e42100c601511510a10008000c00c201c02d40f401b01c10703144c56045110030a0f144000b01d502103405029080300c02021401c030301c640c00c1c040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 276090386 1250 276089136 276089147
    0x403080a02070303200a080307090305240c040501120e1903030207060b03010204033c08030708061c1113060308130617180f010e01020409050c0702010e090a0b030706 73
    0x200c0703001e607a5600748803012080203890240840c05c20103450f00045007240108058000031a0030087d03c0c501000ca50307690317858503807c00c00d810025082e00074007402c042d8003210740b0300204c80e00840c02540551030603207003c0000e84a803803c8506056401c5d16442c4a990641c428860b060340c000ca0355400c4854401140b4000b0029400703050215a110b20b00001656241414420383d011340b41d208040070711440401e0071100703c1d00f459010706810540e400b8910641018160300b50301070703d8800c420300c1e03849081c40300010305010030080c0030324080e00104001304481d0303034000c8107070001c160040c045420686841e8086070b0150381c003c0901e220a81045000020486214010071030704184203c1000c007607458080031a080001c601101130120210350120b507000c41d4140d441130720303412103004690100c40110704040c2900c0440100c0203860b5404202001242014000c56a01a01c0740d038081d0b00c2c00b40140d001038a900d1001c4c440c45d001e0500080050850034055100384102c041c014201c4035031503540c1c2c500820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 276091636 1250 276090386 276090389
    0x230102010905300c0703170c011d0105060f150c0c190602060106030b01080f0a0209040911100206061e06040f0801050402041406091b0d0509010b010212180d03050403080a0207 77
    0x21a80c0d080000b0f00c0490040c0c4040d20720401c0c03000c0240ca9170f50300e10b4480152000c501100030390f08640800c071243c2c0750b0009100c1d98075004407000031038242c3e80702c2c0f050b00c0c2c1c21910002c124500403512203101c007981d507482d5004030704a895100380581e1503004411415203807840110205070000c0c0d1003e42c00303075150440c0e501c80080301c900742e00b00c0c0c680b0307070701c5290132003da6030509281404640810302198400317000c0c2409079405450130f080141402800e000083c1610807400040c0c60618001c40341c2c55075410b09810502e6120030500041641e0301700a40030609101064014901155440c548c00b04240d843c041294000c181c1080081d20164646d12010700a12042c0e808a110794600007010211000c07014590340325140003044045147ea84540703004000d2110f1a11485c100320400030080110017910401d4091030000000081f01e100030000685000c40401d1203100c6e0560a0014101507410080f0103020301300c2c00e40e010101d5041311314058807280159000240802d80104489641540c0086c07141c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 276092886 1250 276091636 276091693
    0x60a090905190501150c1e1a0a0507022404020109080709290f0111100603141207080304030c020f04060b0307030b06041802070215040b0c010e07230102010905 70
    0x2c60340da5000001c8000c0460050b0350100300086c900d1b00201d03149810003a0b9490010305002c1800c0d00940d101c10b9404c65072807090030300011503414070200e00703ca80700741680720405000810214401d80190244c0701000305010f012940800002401c5911484004000785400c0c011214829103580400026200210b205440115115800120070350018552030003071030050000700c032044c0c0e802c00444000b003c0f0340421005118094204514600394403e030300045010345141004490424400c1e81801e182c030410703200b0000241304020100e500c000480e5042641400c00b20b46d100ca082c800704075002904c480c1c0b194094135010000400c03000b048021031190901e540e0400c1071520940c2040348034000e50103078203000c0302810b501042c4119141d0040c0300ca00d0008180c051101d80450080e000e550282e080110716103000301d04409010000d01515000130541c10203410418101012502e9aa6400c551601500e440036a10b0300164004e40c07115445640000c181c5941d802d601c1c101400311901c260518 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 276094136 1250 276092886 276092891
    0x1e030d06082b050313052806060905013005100603030806180723040b09031204050906040c2c0a080a08030c0309030f0705060109060e040b06060a09090519 68
    0x880c01d600c1c56205140507400c0580f94203041d91101000303248000e85a4108035000d102d001d1211203d0400a40d0070320400d48240700c01590843d062902e40169003455003c7c141460500d00180071a18405d8440d54069041c04250200890f426107126600200c1c070344090094081d1095100a0344031075003104042c1d1303000703445040590300c400d000d121790901c410800140c3c400020010070402c40c8100304600480407602c60380c030180c2d40415401e01c0b265020b0b074007581041100095800e51410306000840d40d41030b5101c0100d090602e840042010740d03500130f1007a441150346e8040d00c01c846002d2054001d001950389101e1131308003681c4402606c1102004000b40c030809603035200007001440000c4240ca11035016042a0031601d9220f2803d0389a00082c10902c5c00380400c1c0b0a4804142c0c001004d460b0706801103008003003951501240004a95080d0000803914110b0010000030551034490140c105105940c281d82d1810600c6044880a0058000700080c0e41028103011b003041003d50804422800450708 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 276095386 1250 276094136 276094183
    0x313060e03090f040f0e030c0304300210030624030b03010c05040e130206030901052208160206090301020403030504050f090402030714060f030106020604231e030d0608 74
    0x10355924001c00100590040c1c003e0145141e5040ca41c1015031450301d1044081825403400705242d045030401110b4255641c40802c00300300c01240e43c613103824003200b4100030400ca2047d9004034043c0c440c1e010700c040e02410302c4004c0720141d03a111758000e00081c4903681107404041e01500341c0c1e4621100c8000306100003414180c001041d89010301c203aa041c80d903583c48441c0740516105070b400b0807120050084904100a001000160321450025440f50501d0000010750346007410702c0d0600f40413500c0c0d104a6920b01a590100090340b207030202c510360541103140c240300c0c0c40c01e0310000d00a0b2141000250b05540045000402c00da080809042662400c6900c81c4003401ca040a0028a150481d4041d50591040c102007005a00703110700c0405410010740f105140c15215051001a58402c0e1b2050005a21007130400062011240340302c615005d2142aa01d004440d1301030085c1c2d110945004c440340411034904c80da4401c0c20802c102d49071342e03141c603200348081d0b1755030003c403500c803400740d0200c441c018040f816 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 276096636 1250 276095386 276095411
    0x415050c031012060f09140d050f07081e04060e0f0d0b0606030406090515090d090b031f030f080417060f04060e0a1407050109140901050d02031002031306 68
    0x7928070580900000070a040d150486884444070f20482c1614643e40d40c18403d640312509010300c8003400d0050380d01031009007080741643e24107103c00c0810000c0000174801e0316582e605101c2101d640c1900903102a07140c0d901004544451034203552841b8200400090000e649a000220888914400c40380e04005000c4c0b0418003800d103008050062140440c1400a003081c6819000381d13030018012078002801c1640d6584a0385400301c05980712030b4800084003040440c0204010b800008412494140380c05031914048400f00d00020340442d20481220702d4846416001110900c02150820412282c0c800f25041076482075000e130041c2c000181c0d40d42c00e040c0b240340001070264041e0358242141074140d0b5480d201d00d001025003100d0807003a4010246c140001c210094100642c1602032400380806a02c1e010001d0070952050f402401404110306419101d69a000d103013070704465066541c09080915032000a003805d0000058602c2c483c80882840703160705c2c1c1004041d01c041e200b42c000300101d038003044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 276097886 1250 276096636 276096661
    0x110708070f030605040323250f03031d100e0f0319030c0c020919050601030b0102060f0a1e0b0109050d050a3008040b01050a030b0c07030e09041505 65
    0x1d000000c880e8401d0420004800341e100551040c000d01e040a2503c40c80384403071805400a4611140340e03000450744d580840ba4200708440b0140c20b42c00101313000300c0103a41d00c03031f010101c0d0794014040c0341d60f0325411420318030030240b00c1002c040d1400c140c54003004a05220701c0240601c5e0603d02e280e00c1044c0210804650010485034581c4c43e00d0104000481502011400350401c041c05c1820000401c03003420060301c1d0342e240e1501503c10020592254009194420100c500c003c0c025410107050501a50042c0d8010400d0f0fa00a00c0c02402c0810710f0340e9000c0d1080107041e0500c107040443e0000703202015480482c0d400202204e400340e0300c08140b03e944404110b6142c07280f05001e40250850400c0c1c44c0014180c000c20f4001e200340c4111048800703040200021100d54040c1700c5070120310954104410010000075880c00b52104807100140c40e42107850715402c3c0b1900900e048a0b11313400083c1c0600781030240d2801401150020950b04203440c6c140b51100341a915400e0710041117090401095041e00e81c0e6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 276099136 1250 276097886 276097889
    0xf09030c120a210c02060c130306090203030f1201061727010f06080a0611030c12070c020d0f120809030306132003040506070c0302030d0b010e1011070807 68
    0x50040078980590035001d522544070154000900c90000d0204202d10507000b1198500300301500c0004000160441c041c0c00d2541c02801800c00300310800021030345503149000c07801601c2e040240000e265401f440400c0c510301c15202584821000070802c0c0000340522a182c40c140c40480d91070b800313409040200c1c1c00506105680024000e01e1418402095601d01c3c0c8686004c06144000442c7d94a00c100342c0d0720480d14241c1015240b50408503210041c011307a801a040347c07005005505180d894104201d102c2805a080596a154030500100f17052a04c64134a9854460700184031048104081c90440b5100e10035540440d01c004041c0c1c011003001c0d00410625201e68100800f40d8591b607036400c20840c6001140c604000c10399a11840000c00305141d1503100c855070800b10805940e0700703140c10b0007032411a0003800034041004441c0380c0c0d00046d82c04025a503031040035000c0426125a2300c1d0050301c080601d500e40d01c0d00006280c2440c48000c0d4030940100c1c0325030b4002c0a41d203609449800752a03d9400e00e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 276100386 1250 276099136 276099157
    0x5011d061509090a020d0c05031e06010303030c0c050f0d080c03060108181518160b0708070f02030a050a0c15170702030c0307030203190c0b04020907020102210f0903 73
    0x1500407900d540c00c0040c00c80c3d0f8040d6078a419a0440142680012044149000103448244c6003034010700540c1010440d040d007100c0241c1d000c61a900c0102130143d0380d1101400020101034561048480860091211340c0c071456000007602d415404965600f941c2d404845400d01c001ba540d08003055050200b6001c0740c2c0a92010394a20745540c0d42c452510020170407034102c8100601c46c0b200340c0400503001008042c05603110740c08002d941c810b115446032130050400c10320821541d00e42001c10410381c01004880d401e07640710b000151202c80504010180031003102029405000301c0070940c1c05c0000120300c101c41a40703d03500200d104d9484121120820240d40c82c0d11020031041001441403d4900c0c0800c0ea2041042c03040300c1c5000880c00509003941c001d0403049000d42c1c8042082082c4200c03050075086802c80524044140c1507250300d40c0340c1802c001800103801500c001d004164031520030f4044482010703a6090041e0490f10f9980400c0c44000c046401c04140304000c00840d01458010041311203c018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 276101636 1250 276100386 276100411
    0x40b0a05090c01031a040218100203041d0603011419060f15050c030c150703051b090105092d04050a050106080613060e0f010905180d1107030c0305011d06 68
    0x14400190028074075020550b017105c607664400209a910750009120f890b101100c0008400411014010f00042581030b41040d5041440705103ca1100002407064806418410660325210040400d0040c984142c50b08040301d480c5040282d15640700f00142a9001044410401c0a5035030700b503aa41c6104c2c43c0075040e121400924041040307485200a420b1703110002e400e07240342134000c0350320b685085103c40d1480d518040090170000b5098243c440c480c0d21402d0200c0ca1144484107401402240c4507000d4194148900803425104075110301e460703181c54100d030340400007a114600c1c0b40e200e01800010503403071080c0c0c14040050742046140c011141243c1003034940042c05d4495008001d208446004081c1042d6502c0308006440703108540964018005600200b841b941494441000e40300000c0c03039003120300a4600c40384070003d00050b00b02400f00541c81c000456070316440b1400d00b005001d60000d0306a000c03c6070040140310066200104017011409003000315031610702c1e800e031288801c6900182e040c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 276102886 1250 276101636 276101653
    0x10060f021c0e0105090604030f0b10080705012105072c09070e060706050a0902090106030902030a080f0c03030a02040603240902070c03120c020a05010c0b0114040204030503040e040b0a0509 83
    0x80c0501c01d12106000b050500703030304003034141d0042820364104e81c2c419030340c96400a44d03080c14010080100742e000920700c550640300c50304001e0016680d50003031040320704002584d448801c500344c01d508071803c5402e41309018050341c02e00340e074018201f0036040244d82a21882550111044d8803051007481400d6002c1c1295000d035a44100640703020403a00030721600b120081080d40000340d120720031140700d4100d01400180c09403007030040c0400600142c100506051502d640b55000d60740010f100008c241d07011100c60303900c0407010240c1140d4000d81640d44007074800032085c00603060303040d0050002e9660340e5034200203420030f5030202c4031080e0440e00c0742c66141d400d0040600c44401c1036001403880c0d600540e404000641d0703950316041c07048a0180c0380c000160b18040320004510b45101172000809003460464071034015902c90b501d0112040c0300781411010300014440007621145c040d00e0055030880180c80c0c0303880e40c4900c03401a02400300d03422201e06c0140000500e01e01118403030a40998151801080b154 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 276104136 1250 276102886 276102943
    0x30906041203151802070c0803181005220f060504080d05030c0a0c061803080603010615051606090c080f0d02031612121514040c0219080408030310060f02 68
    0x2501c8001c00c800313800380c007004040c0c04035504520190080c24000011a900c007849001d044040d03070300c158800c3c0704001f4100c4101c0000e030311805132031000c3d05402031445c48582060441c1054000c40d404005000c0040e42c00280007500580a4000c071007020056810b4040002403c407000e10003110800260780b4107001814141d40705600c0998114410200020306209103600048010343c003103011800155010100a800d08082c00307100010a10341c00c0c401c940c0c5040c4000034115010342200520b59400c400065400c1c0701690300004965038110008802c401e44a480868823a0703a028015103580c030500d00707510140e81c800021200c2d011394207544900d4001c00c50b5070702c012292045100000300000003410082c60182d03403050f546011b200d10700d002c01c0d461410301619410b40100c84200d224500d4102c000e09581e1700441c544641e50302480760100c3d8484c69142c0082c103401160444a0188004001c000400030710303040d800141d803820344600000401f403620490340c0d4042c105102892a038040100d50b541d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 276105386 1250 276104136 276104159
    0x906081f3c06080403020102120109060501200706050f09090924040210052b0b03010b0406030809240a03060608061207061b0512070b070c0f030e0f0603090604120315 73
    0x454440e00c0054a401851427141e0f07030118003030700581825039030303407100300f01d950780080226104000484007081c4034003507460b0144e120a0548510001e10200052180803425460111101e9180040c00001c09007000000c103603403806001c01090307010b50b86401d4005224101102103204590080007601c2040743c2220444007508941829080e1030010b0401c010703100c603000410310004600b000d00055200c201c1c2e0801d400d450742c10810342d00070fa2401600740041010f14088a901000680f460560002040502d11120310a5800010840780c0800c440d056240e00d900001d044031020b0752603184507280d00c010404000380010584001e03510401d0108102c034001c3e0259402400030800c15101160b8544655040411038480a0b032080760000d240740c204400e052900d40c00111520381031000d0920b40d5240000410b5001b000b5090107840aa001d22965509224080820740508000c0c0c90b8240401080d540c0c0724203130b4089580141444000001512034800e99846291a10118200c1880c140c1d10185 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 276106636 1250 276105386 276105391
    0x6110a15150905040b06010f03020a080c0f0c120301051003060803192a050709020705150903040515191b110f0303040602070e07050a0906081f3c0608 66
    0x1044800d150000794002e82c0d40f1a03980b06901480d803000503440c100000610080e80390130120241481403102c1c0c50602c0e80400601c1d03001c01c1006c000c0740d48180b5000709039060b000701e5440c88518031545040c084140f1820b0701035070403524192440d018003c1461025820b0b100c11b0700504105620502000b039413100a0005131103c84641e04001c18800a85421903600c0702088c0031400310030b20134042c40410404100000f000800c00c0c58001c50602e001036482984a0303009807442039600c60418082031750004280122402840014504141c4d540c0160004440d80c011030483d0510303840300c10f1150190790150840e20707041d15a11905001410300c40d900c2459070044030604a03000b03503130b0010300006514204014005000260000d084031b1303240014030010754800912100400c02c09220007182d26070440e840d102501c01e079003020510380d6140041700d00c1e08200c9070700354480700141c12800100010f91070100d0b0541c2960000740c81e00c08441ca10511994854403412442c90746548004000d8103220321191074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 276107886 1250 276106636 276106661
    0x2060105010804151b030b1f020703022704111309080409021c0e07031b050a0308090f100915091505071a0f100501080f010e1017060106110a15 63
    0x41c2d8000f103800726488000301c1c217549001003070360342c00c07501e401c0d02e030041c0c42c62004480c40346002c0181240c4070000392180d01d20b01c0300901a081060b01b100103c002e82109659218412091080174649824100c02c3e0f50045400b180c00780304c4100c0010000e0200740213140c1e416400c80c0303820b4a043c0c50043d40d04d000b5488685540740f5081e10203000c07203045115000751441c032003084000780045415400e008030400c200480f1b071202030356020420042511a04020720442f034103c0041501c0300d814401240840c90307515141c0b9404214105031270740043e081101c0100340c038003540d0030fa18084115141a0b904c888180144017201c0803800c400d1500e02e00c075400600895104116068501a100440c3c03480190207440417407548611004110480340f03108408401001c0900c3d09121710f00304035a1200d86035406014890514040d04001015890b100110100401100028604003010344068548509087c000c203c006a0013031000c460400000420b84007103908409940c00120a00700c1f4231700101081c00d03811 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 276109136 1250 276107886 276107891
    0x20d020601180612060626061f030b0709060e0418060507140c0106060e0d0308061212180406080a08040603050703061809020f0301020408250e160f0206010501080415 73
    0x2180014000b08041305443c800c2501003003240c200390008002c00b0b025031892001c001d09490288510000240d16900003440380442102501044070304010b403a110b4001901054610043c8845280e100e9010804c662095403007440096039041000140c4031400a07076103100c9014503c010104e1a6580001e42140302400c08044c1900f081400403020b811104c110a010395451004102039a00103800e030400480480d501101010075540180c8100406003485009100f14081030141c0760301044010780c915444606107840389810680205803544c086482030040703081180c0020072420002d50120020b511002041c28581030201c03c07401030800400d01020540c55440016056907a440355100305800000082101c408500510002c0c104043d4920f02036072040000700441003000c280340744520102031061124030f05160a4800800c001d070421b0342210b150340700340800f099901101120010050f29916105510900184d0711030f03500340324440c04201110000790014483c803049585610031200c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 276110386 1250 276109136 276109139
    0xb0c0106050108090a2a060c03030c090506120a0f020f0703030b030705010512070306090f0b09250f030902090702010c02120703020712050102160309090e01051306050c0d1104090c020d0206011806 86
    0x140310034142d9100e00081488e083d003110505071f140c02a1280c510041c244100e00030b14210109a0030b02c01c1d028046041018803000ca0b0040880e50401c91448540c01d00c10744d143c0c000c00c40021407e500c16201100131034a05454041182401302e60380080b00c1d4143c588a0411010440d80c0c0100a0010662410180c2d074000114905c0120322511040c40c55080000603c02401002d11010203c05030909a00300f00b00690351140000d031401240e04d035205071406800d130700208407003680030303014054009602018940070808510b6056201c0c45100001d075003214a040310502d04074805226030030002d001038104050510009509500c3e46000c64414130006141c8040d0025000f80842813440460014040090422401e0010f0081303400e40d8589200810050601000a40040b011818010b00311500c0d5000103d42d042e071b07101601c080c02c0080c007050103410240f81f5003007140d9102e4020202e881e4944a41043c0c00d9200007138054059507e50014003490342008003a40c103a16039429030030030040e2102070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 276111636 1250 276110386 276110453
    0x51902150f040c1701051e100902090315011508180c041104230306070e0307120c0b04030b010302040f0207030c23010e010b0301060e060306070c1b0b0c0106050108090a 74
    0x1d151900210303a1000048908040f81e040000700303140b003045840781f85898180209103940030f003002c044070500900165103689080129087c20004084c0c0005000002e0000410120600080b040e08141d03a603000d0140d6100f40d00700c3d8206c0001ca0300d00c0344550008617a20742c01d0406034480a111091010064103040c2d0311504818036011035109902201807a40e00e551882c24204092600041281448402a003644000c81d079507a6242c81900d042e40c00100b9000c00b40007482c02d4074806000c4c070003030041c1e41c1c6440c0e0810510813803007032008078040c0c1e140c000000424041c40c802c4e668005e5040c0d48081603446a6190b403000b0602c035900d0a40f04c4d21005606003250380091003070091141c11a000800c0300ba128104050850345079600003130381200b24408200c1283e501080280e4881c01070b040941d0304e0300d59810003c1f8444648011400500c00340e860200d0b815007000b0241404440040c028041103031a02c0c0111500340082c0c0b4518040d5001d10800f600103001c0003101d14420031104240d1140744080030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 276112886 1250 276111636 276111659
    0x40302060c0307050105090c0607080904090816050705010305040f0f03030e3406020d080702030c03070309090e0d0f030b1c080c06100506030402060906070f03051902150f040c 77
    0xc1c0110641d000044000030404203001b0b0590002051010382a40076628000c036500d8401c110000344503510020b25041603070b66a500041d510303a04200841e0710fa046c410601a5100907002c0191030300c6c41400e000203440c4d80b20703020b0305109035404000a080c08030381e6030b01d01e0b1044a60700c3c0c08130140358580c08040b107581e030100030b801440803e0300c1d0510303408100004606c9007140c0c0180c150300910700f01c25007400b4880d00002c0c210140f0b0003d1034120301d10741e1030600032070450107444040b603118000020424203061303000d030070700069500c80329041001d0b010080903031350b0f01d5084010090104110940740b00e00180030b90301180d010b00018041100c1720000400d0313502010324004040390607200100d0415480030f0208a031691101d00c4508a4a1050600000402c136010041000703102c0c503000124410241c491105880601da0703c0340c900040050303940b801500707a03041840748550040400c61080a02480041c0d00700102c48081300420007074603622034815120b4001007054604010300d1500081da80b5042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 276114136 1250 276112886 276112897
    0x8091005160f0203070804050906010c0501060920090a090c0306030206032403061b0d06031b1e0501080a200c03070b0601080402010f0c26040513062904030206 70
    0x11407611444028041028108041580703140b021075009000c2c0100013200b15003102d09a841c22030720220259a2a80100c1c1d000940c00c00003012542400d40001d8052881c2c0c000805540ca9010a110000d80081c2e40842a0164403079145e800500e100041000c0241907004a046900134500811103a4a07a0042041e5034004c0e40e076506c6088141c1c028400b00d0100810b0008103002c200c02400050411078080c80c102500c0054180c074060001601c1107503020303158403110065501000c042c010380440b1084c40c16142c00d40c4204e2024840f02c4905000c00c10300e001c40ca8040c2c070016145e0901c55280e0001500c0248104c40d441c07800c0d543c11003065055150320b000600f281d8090b1303100442d580c1d51180761000300000040d013014140241a814040140c4e006125000b0016591403c0400d12115092909900b105c410b000d5521080d00742400b2101031107840100b003500d13003d0300c01e21010880003501d00300325812840360520240084030a01d20000000c0729108482030386a120a0516840360005032865018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 276115386 1250 276114136 276114151
    0x121801291011120306030a0606032003160b030a09021f03110412060e1006080f071a0306130204050a060c02040b010f0815011e02030a090e150108091005 67
    0xe18805100074648844240040c0840d490000b8001ca0303652401950b821080401003a03011012002036029141080032103036054101c1c105000d0300d82c1e60f0821800d2510307a000c0c1560a00303c038110743c0401e403c1c001210742a05030440c4502005910f400309040f9039070009402080e800c0c0c3c90710050800b6036601640401e0b81001040d114400710203040000c1d084811540f00b420b0803060074041003080840c100030543d035540d08041d001c9443c40340715400c18108480a0400120a45400d00204d29a0310001310820455004000c44680e162144901800e94081031003c002d0f840d41000092094101890300b810f403213040d10805810146c8031000100d050394181c0005001441c0d41d544031065192501421188402c02c0c205074604a444c000700410090000f0308400c030100079044542d4990348a400d1055131410300d02e000c1c001301014440001c4d202d0340507000c0e442c005901c0c0300e00400c020b0300da00b0010780100c1c90040c4900d0320340540e030015030b440040101000b10368041e007200c0c80d918614030b010b0984941803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 276116636 1250 276115386 276115451
    0x70206130f080705010e073807061a0310023f012715051e04050a050907150509090a0f02030711071e0b07021210061a121801 55
    0x70506242e2a000c1a0b5020100c10301c0c8507902100710401110000311140b84001c02008070b03a454008084491242780740040c92145095030281c100103088140b018406021810345083c08185142001603005000007122030f0100c56900d040da0382c03c14058420130724038010080c1c0c040702d1120740b104500c8800f40c0c40071002605480d104944441681d086000d01002c1400401244040303041117006410315009107030181c01c959400d4402e480800c0300120421000820a1000d03107085070301907000c2c00040c4d441003054416004081010340c1d41c040541c1c001401076548030b060031580810800358603406401c0e0140543e66000041c0d00002d0750006501c05d0040383c9907400402c0703006940b2440d000503a401300d0075160b4001d8004e104104004100c1045074821246141c580c2d10034000500c80810095685403244900d066042001c440c2d900407004407810b03004000c0c0500b01144e00c4642c0740c4141038040c882241c201000900803040444648200191440006131001c0401d01401d12040d0b048460b000240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 276117886 1250 276116636 276116651
    0xd0816240b090703020a1d0310020a0c0b06060301050105070f06090204110901090f05010e270f04140607080703090303060308040b0409060902092d060d020d050708070206130f08070501 81
    0x7041425583c10100b14503085160511404c0700511025114140d6958210300000c880035540e01000311491340884d00600719510b0032180405803a00032a2441240c45000d2080090013500c3c1042c1664126071041e191280b0b483d906990b50054409481c004880659480e03078080050389440c070407800d000009050543e51102d141c0e0000d0102115907001126400140100784181d903805100c3c1c01003948203075100d15000b0802e0410549044030420042d0013408010208840060005c0310b840c025800b511003155044840e07104562514811287e860100d8400408180f0440c402e91020603424028039000403556140c0e95845119031240d8094076a402005c5003d001c1e10b9800d00c02e1070001c000b940c008500d40010b540100754a03d801c511344480b40a41425150b80198214a069811003402007d007030340d80c00c009207000c00070340000d8150f1041c07600c1d0000080465014180c0203016540da5002411745075292440200410b0b0600000c45418400646100c0010458406070280c988030b0400440d600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 276119136 1250 276117886 276117889
    0x17210105030c0a030210050703120c0915112805060123030609070501050c1e0d03051f05090622050f090a030504060315051201050f060d0816240b 64
    0x480c958100610031103c0d49010001a90391441c0c090000d40d03503007003003501d440c01420151803010700c280b23481003e103040010382c1250360351002103102910140d80f400c044080110000f15a5140e00d6506004943d1103c01001030700402d00004142507003001d103182d01001120707501c039820070f1420b0f4801000d0003625180a4090070345072081104941c1c00b580181240e1510600f0942e5074503c0d80310b414140039001036003480740c12050080c43d01617100d801d82030203c0462a01296a02e84492115400280c6000042a0a0a48150810200c524000801400a040070308112102802400460344804003c1c00c0004004072480d0381c661803146241e00051a240c01c00c1040f54045c80104468030b80d030410303081e400010b500170040d60300b0f0300e09030f10f80040d00030042480c42010700e483c3d40100d5072001e15500140c5540b481500958402c1980c1b03c4404803035114001880074030100110000e01d4454103200802c2e008200c0701c4800e946602448508003502c1c0b00303010400f501d100d04480360341e040b0b45814903035045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 276120386 1250 276119136 276119143
    0x11e0501080a0f02040c05070210170f0f04020f060d0c0c060c050a05070312090804081b120d0806040b190e01050d020f01030e160f0f080f0601031721010503 69
    0x6080440c00381401c03486542c2e8440f45244020070080c816580e540c4510351140c49402543c0d40c039980a415030b8030490441001900c054640d800e2803903455007000003e01c032440d60046081c09100d4500401000d0b4031540d0820050500090485820900c01e0081400000480c01110416200d40d220f0501c401d0310390510209842c482c613202414032004001205419600c0b10031a508a501031920341c01201598650a0182207441c00103440001d0201e8040380030780000c11601e2000c0080314006d055000c13480b00380401114001c1801c0110703040b641a80c103540b4010007807603071303c0782c00100002103080e24000010303003d60303038501104088002038600b4490146090700340350151404031200303003220b1203d50010f002c0c0030082003003504160311350007403c3c005082040a0452451505440c1d4001d42d00c444c00c44603003900e544a2400890410f03800022207100110310720b8207000100c8094142a82540c42d24050100000d5003401807400801280c0510000040324540c0350900843c00c41c019450001014503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 276121636 1250 276120386 276120389
    0x5011121040203060105060f04050904060e010c090302010504180e0102030915091b2e020609010b0108061311190503011409160f020307080d0c1103040e010b1803011e0501 75
    0x36841000e00501025030703400181a81110401ca601560310020b030307402c9000600507540304d660017084080520081015030f8001640d04891100200301822985000b120316241d039220113404104104000e0108000c0d0400e031a49005400c1000b049030040500b0007800c991084850006a03004100341c4681008a03072045504402c2070801000740c2601d82e250900188032004c0c000d4855140380c4040320940d85006440424451503810007480e00358061070103515100c048401310895460a001e400c0250f02406501e805048003514803103c0099100f140d40041440d000c6c4008215004d1100c9401400f40911040c00001d580c0e4070103499515015108080c40175a2155521030b01101040240b042024460b030300b03071803105160404100300440001d03030641c40350101c0504095400200d0914000d060b170405110b040c119681c03a182d041443e00180e4030382c0500d00501000035100d034010015031150703102900f103030320030a143c1581840152000078219001d00d5074080760760b48185170780b54400700c09206003070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 276122886 1250 276121636 276121687
    0x312020f030c1903120c0804110409080337060303120507051206130905030c190c062703060c030b4603241404080702030a050111 57
    0x40c10482422015516003c043d031606102e0b00d0351405040c1810b01c00c0042808a007500343d41004100103c1c04028050b10003203c050350900e680f1800c0707001900f00b81c8500b02089400c08485411030300c0b020740c6040200b41d000b503036110800c03910000f000140c0480095420b00150040009403407495454040c00540014824958107032400d070030814160780000c11a207010310740206400860303035941d00050102c02049411903089103418040307020444000010a1155040e90441e460184205050128445c0d01c4400400008011000704000703800303070315030203101542503255a02c040144047d01078403c41c998416241c2603224210358602c00c0d00352040e81100b02007a00c0900400c000b0500c03140721030740da00c807549a5500b0490b038903400540f032041c95813458545801c059007400d95281089001c40c0d011503200d41103001c5012803021b0024a62140d6912284903104403c21641c4586030713070f029034102090607600341c021580418000f50707007072007140704406c0c1c071785107280d1034003901d0f87c1c200c03540f00d101c1c900315 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 276124136 1250 276122886 276122893
    0x90d0503031321080a240b0c0f0304120b04030905030604060c0f0206010b03011404060504020f0903070906051302070203030c1c09061d06130321030b060a0903020603100f0312020f 79
    0x20f81540050450b80c000d0701030902040031260904140010b0821080e507104080b0918030100300c1121843c01085000c0d5040c003100d0101c0d10400031303e0b440344a07074401c0c0000b580304520114000b9031108900d981c058003904212400075510300c0442c0c185002100d0840e11039070b541c0e59000d58146c00403082d440001d26880202050f45c10695008081d20040c05076a0380a186400581c403c0d985a4000c83c000c0c140251065403142c034500f120b884a40c110342481440b07805100e8020a601c8003d20402c2c0c01c80c0c10081190440c040060180002507005500aa8040c00104440001c040007040108a40c24075001d4030b905181d9a150001c1c1902129003107142003003a84490020704580786080306581a100303c1e100b981d203c005040b844039800e441d5000601202c0a8034aa5200703d1a102d810010502a911300b032000529080070404a4072480c209030005c520000c1b020f1000d4100344000e194040380480b071580701c00c2d442d11300030f5945980c0c9510407031b401d0240310102c6803420350511521641541c1e01008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 276125386 1250 276124136 276124193
    0xd0215060f060c2b031814010b06070501020415050f090603150d150606020f06220b07030203070306061715010905120f1002041d1b03010803030915150402090d05030313 74
    0x710800c41880c142c0502a00d0b02c014458030241804c4d4130500d4014001418ad40e0780704c4403440c2c658041e410a01c5159885400d1812000d40300c0d000c0d20446000350b03c107106103450019004204011b5030000342c12003c100401c1007510116844526a141c0300500441c011207200c420007910703e00b50f0360103030400700441d0403441640303c3c60800060340702d4000b80b003411140e0f1704440100d030100021101c0130000d00903403070070020f024446800d54002c2d40556419581813140d2034442c07100390b03140700c104400000c4480310f88002565400e50300000310500c400500d84000036a981e00001402500b00700c3e5000304940001d44031904c8034070208069010101d91010541c103040c6000c0020f40101240301501380000360140006900c0c0c24901010960050385030711468903540c40d05909542da410484038802c0034458070f100304c1c100c00c80841540c0d10648820308000b050814400500000c1e400102e1a90b4100034400c0648002030003e002461140440c2916116084040c1c2420184c003254031110311070540e14243d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 276126636 1250 276125386 276125411
    0x904060909060501080c1e0f06070f060501150c03050306190b0c0114010f0b030702120d06080c010201110d11070605040605040201080f0c0405060c0c090106050307020d0215060f060c2b03 82
    0x185402032000c1d9008082e4290068000c03401240076091019070009c400104072081041c01c0c500e080717004d80035281c20000c5a03201c030381400440460f0141ea0700441c840d40300280010740b01d1b00065501c004007810b824034404009000101a000c540c0000c07030b00f40d07000705020102d0a0244075400d50064104001c81055151422401c200306d140d00500696210010018801500801504c8612043e0f241500c1d0ba806a44030b200740141451f01510b0040d000c0e240c0c20000707641c414054007402c0e0b0f90040106282021001044008103034000510408601c00e00c0658003082003482242d2040b40103078804200c500c0c2900c00104001701c02021703450011214800d00166011306001d42e42980d4040d141e0640d51842c131903800b450a40007002d102d60141e0120000728026178488065801031b5015002c440111140440c140e8580d0b403080e6450f415600c907400003c8584c0361100c020160304401820180ca800c03480f02c0c010782480c80600c002d034616012043c2e003120740c400740e9003420b089100600e410007070302070080c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 276127886 1250 276126636 276126649
    0x807140d12032003090606120c09220503121b04060c0201080a020c0318041505030c060904110a020d090603050126010204151e0804050717030904060909060501080c 72
    0x1503409040507a910030a05078800041148064885981e050f5034032440c144030401d81e503001c1120414040c40c40240070344034080001a44d281016002000602c0c95690114003448001000c0021000c40a07560954008280d0620090040c0c54545042c40268901904202824101c908140e1001101040208030150b40480e030581925030928040c07615407210900384c0c000c0e004007080103889010004110107114024a06003c680005407020b00c4040040302c1d01c10000c1403c0c3c4511a0150802002500710b071900d00700400c90b105000300001401e500ca2540a2a0703034004610750300150f40440c05281d100b40d08500b1940040c1141d1400380110740c101042e469084409210703a1103101007903400311200c08400c0d015140940910004c01642c0b039450040107000c9a4113034060342d000b0a950240d4440b80c0c0c400c0340300ca071049401000a001719454034440c001c111101c809007102c1404140460f0301e41c0d07600ca0080f4401054050700102d041c80b21410068211641a84540d100d0380c494181b8414036107074070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 276129136 1250 276127886 276127913
    0xc060207051f020a120507050d08011d04021f0c0c090c1202160210020c01080a02030705040b03040f0204090f050618071818030c20091914010807140d 66
    0x1107082c80301101d01000c00b81d29100b00d03200300511000c1c8410703190340c94075409800b600a0602070b0085450030300f1118000c0d11080300c01c1c0100c3c0281070310700300051140c50780f941103207422a20140ca12040d1a41d8860140040642c0c240c081e800190350011600030720001d584100047d08012900300244407032080098500103c8003240100c1c03e802040c0c0c02c10801500c000004141d4010f071050408407040c040c0252150562603965010800160214544401318400d07a44109243d4450074a018203001ca0201180c10082c0102e5880098020100058480e4012012481c0c81500500308080701ca261190038090020400101c440d64440307419540340000800c0000ca410041c442c0c240b0700907070542c1c4400b60003a91580003107075040001c80c804056001d10592200ca0182081d8110034000c2130343d54805144001c0d4040d4400b0445022581107a0701c4424400207503640040015411444520b01d29801d40c240d10040403604426010000960320b1081401c2880e0200c1d03840600781080d40d00c8141401c8003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 276130386 1250 276129136 276129169
    0x601080105090c07020a150306061b020402131a030103021c02010e010e04020705061f050303030c03040201050d06090e010b0319030203030a091a0406060503100c0806040e1f0501030c06020705 84
    0x10702c0c04640c811485008980304181c000d000310100d2900c07000d20300200008903411400003441c1c034000107200744c407903411503440641c1074144105115207602000302940240010a4400105200001d0341144800d80310001401a4508546035032550040110154140c2110110a031000b0a00001070781e10071103a4180348024244000c111240001103002030040d1200281507205250a1220101e03031125442d061350510603108469030f89440600d0f0300d81c0010703200c8640d4043c007800405c0c019070040340a844c07982e04001002609680e603031440d5050740c2102d445104075965540000c500350805000150f402111403025644000e03599500035505d11000780a219a140d07518070002c101b103040140e81d513070010f8615184103181014180341380100712034451a0700c039201d0940f200c00400d4130707401140d40390106600e07034010359520007040c0000f400601056441c80e002c0c0004902c03540020243c1c0101b882c15107a4002440d42c15817a02c4154009a50400800d652101404000a585240c0006904140e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 276131636 1250 276130386 276130399
    0x204051f090504231b070f0c12050d050c01090639022a03012414100c0c090c0302070203100504021c030905060417010f0e030406051305300102030601080105 69
    0x449411a020002d03074480c5a000131000010f0101c20710a82e10840ca502a0223a280d855105540311450519074542003402446600240030b948041d5000e60080c0034072003580c0f00041024110b80d510301040340c0414401780c50420a6440424000b07030307100f403a40c8003d1401205080c03240c103500790103941d80441d100f49447e40114075004462014180350110010780001e4000e104400640344000c1141b00c0c2200360346507440d0208400100f43d030070303080d01c80c0314050050048006c034aa090710850354140c222005981c1122030351800503010b03125105070f141240650703a0060329244207104140c10300303594034888004242403030b0500001d0317038441e80c50000e01507039002c940600104500d02500c42200e20b500c450791115001c28002102043c1d004110980e40c1070303000800c80c10301c82c02e01d01d0013164503640c2c04841c2c0d603000740002c3c000c4500030401462503a1508910725815590740b00081e10701c1545450404460510803032403882c400840c8180103200c1004d0f0002e43c02c601d41500024098041441264071410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 276132886 1250 276131636 276131641
    0x180908090402040801050f070201090b06280b0901090807030b01060809120f1201060c0f0b0a02040b03150117131b0503060702010c1e120b01030204051f09050423 71
    0x1164004031002424058030654486558650150080a00729244000a0000c1001a07080d503c1841911402a071000712a2165240c40013880840c9039000c0c0300c1807a401c2d4503070202c64020320059125008180340c0c0c1d550b81d600c254600005100c04c00e036074081c4505602c4010b080c40020380c0d40d030310241505c22500c0c0488042d42d8100a4502d02070314103462944282c1d00040196507042c040c0300070111112500c00340b40403079030394001c126000c01030f040f03010746400d6082c08001c00040b0744045154000031582805800c190b100c262046c0b041d4030a0f00d18200340200080005280e5030400c1d01d20181d20669550f90707003146005450000c800110f80d030010070b1582ca180b915026440b140c00d1400240602504403445ea24002e2400f0b802410100001c2000c10b016001c9528200210000103114031416900e604812202c1c4031600d020b812900121410f1540034070010490303884d44102c001003101c3e68441501003041241c1c000e040b101b00342d00f025000f41d040103d0220039403072200c40014020007144000200d513 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 276134136 1250 276132886 276132893
    0x1150b03150a0f090b061911030d0617010606050a0906030c050d050a05040212030306150c0a0803100f09020a0c0b06030109020a15030501050405040b0f041a01180b01091809 76
    0x990741c510302650b00000c040c2c4080750320480c0301d4000b8150345110b042080142d1982040101501612046000e200034543c09040d0703041c17080c0110b891180040c41181e04080b04901003000303486075a04002d800d0443d00f80b4014070404240074190041c103e5051041c6002d03000c080040940d11140117041c207250b01c500300c90443c584a0012501091020be40410171418021401c0c0003500301601c4c241d04c07030f00800401881000010044134000d58004200e0184094403d04082080d00006060712050084021800106880c40015031060204a40b411551800d00b0704424903100d003500300c0d45405105010803151907800a18130680c90340c000c801e45401d41d035000006800b4000c0c10b04002d400440712400010790303a0460000c0d10307204119880610103689c0f50001d100c2140c004903000f8140d200d105002c62000c18500401030f41040c060344407148000c480e900703558052482a4001c2510075a020098080d10310140318800c920002440d0450308185080321991442e02c1ca0209000d01903038400605c800c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 276135386 1250 276134136 276134161
    0x3050606070203490e030609060117120f1201060c050a02011218061a06070f140a0506100f0b0304051b0102010e0a05030a03050f040b19140a060807060201150b03 71
    0x804011400c0c3c2011005642c224415030942403002000b01796004200c0900346000700d180791290911000800b810782ca0021200745900e11000b04042074018152507144803007426004100c2c8003509548503030b40340c8418000162040d8140c0c0300314104240c4980b11000141c01156400c032040e024a00310700c1c4160045400002451405110101e03000342d0501602000580d4000008807130511034605045050a0240480352003484401000c20f029500107100145540d5034014100c52008112165501c40781d8a15141240039100003009014003101000b01910aa40c40c40150424020b42410760410350303260b1f603440344081001031001400140805590f4402d52041c029001c40e8012568000d00707a0808075225400b1400001c0001c0c10000055482c004681c4018000c40d80559090555a6807801043e4800076000000880d10344491000304400b4903066081c0c050704c83c0f40e90000d06103150900c018584032584e0701050559041403040c00c0d018002a95802c00c403000c0a00b1540c1e660340d407808200310f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 276136636 1250 276135386 276135463
    0x3021503040c0f08120a450e180109080703030603060b041b0f02121303140f031204020301020706050a1b0807171e1602100605060301060f03060b0a050a03050606070203 74
    0x20600315541c207000741d21000001c220300140500d41149500880652100200c2c0c1f80750040c1c2d8180d0f181c0744041040550040c9805007034007000000001c04011960b14440c4d507500c900700603000652569018400d02c0550710403540042c500b01c50805c111a00034400b40e1500080410708414060000756a5036281d0080c0040400d5007d44020655500f250750121004050136010541d240d03240e5050b0546400d01c000303449405403980100840c2084c200303400207410440020402ca030555024030040d4001402401030701e0281c83c0c2c015000c600c0e4031a803964071290b401c091440d0380400540700c05000d20150084902e1b01924440405450300b660792040e010015021442504a0003200380f0801c208585040b0225040c418140e00b03039280d83c00c05044c40d0056581134003420f640302000b080104200d600074690001c65010500b004510701c0c1c0e8610700001c068008280f0b5a000c1480040d2152106505109156016100b110404e08010b001d401181d60b074005c440f61407042c05110451410040c140d20f0b0700c0c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 276137886 1250 276136636 276136667
    0x5010b03010501060309030e1512090312013002091305070308070303020a110f1c030b0a08030901090b03090d0c140a11010905040515010e010903021503040c0f08120a 73
    0x21565100c0c0e004001b09510001038000582c142803030b11062030b104200880504124007000c0c10312445243c401a8520040c2911515210030403a04450254240c0d0240c002e00709044801c00440145030007856003e1029400c21070b1030b5655071040d00580e1b0f000d4045405c9143c041045198481c14540f840c64100346801c05849410045040020968036400400c00380983e551510301201140100d2a5500300380d501c03800141d001031064011303600080340c0340c02010241d0710340407582e4440d00c1e000c14000095034003c00141d03000082c44074a5075811802507002800025462813131480c12251791034540c0f003c1080a001c200e1094003080511509447c2030214040711002d031100c01e1407914005440651300e0324001d010407040c0d1030021310f6107018072980e486040028102034a500c015001160100091456603060002e10800407002d80c54803d034121034003401c20001c80d580c3c01c090030000000e03416540210000b00c0c02c19401d01c900381000c100d4a07600c03480200016100c9017824415a480154040700070b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 276139136 1250 276137886 276137891
    0x30b0307090b0f1c06021e0d05090f0307150905160b090301050a02030403020c01031113030605010e1303140a051902010c030f0b030c0108060a0806090a1401151205010b0301 76
    0x200c0c4484190b486109071400844111000d50280c10074400b160a403410030080f803044a01205020800a400400b40c00d07000700100b44895134440482d04c86600320840000c1590390b24010464118010041c10103a240240000c40c20109180d0321003c00714160714105040b0307601c4400000410a0030003201d02401d4000004481c00b03a110960030a245c0c114031b0300b4612075030802c400f14141c10140e1003103c0c011601607002e00f404141d1500103501502003465801010341042024444940c1c40040100c00b4602c240c0000c101c5501d04005a0000c40d4042c0000d190102c02c5100c4d1000607401a8194000011046460741c85071540c00c010389140c003880690703130b26807031a100001c8950346d410340c002c0d050748075161000c0100515841c0c607a011200c502e4021b5400d1741c00808072140700d43c09021a140d1100e07000f09144041c40d00d4401c8141408001d0b00c00184c0c81e803206807603404020805560500a4901d140200400514036113040303040d144030710840461140c64112901448029000126800c0c0f01138000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 276140386 1250 276139136 276139139
    0x161808121210181a0306090c1e090121020d03050c01150b0d0f0f0e010606120e070b090d0204140a0b04050402030307080a02070f080304090507030203091c030b0307 72
    0x2a104194040030301c000700076440000280240d5501c0c100300040d075403590710035440d1514000c0404010a0b0961000000021006040c49507990400416205a4040000d4000c0000c20001e1040b040100c01061044140702c40c00c070025511040b03c2c003030440d0000d94140840c4160010400703401d42c3c4405010790040042ea1295080c507411a000700703507021000008028080001d00c0b2400388090710301a00d807952004102881c0c01500c1500840ea00900c1d561001400401c0c180700c007011140f0b0042d001034565141c000420800c0e402c4515580c800f203988509210b107a111552040c2c852185000b01c1d8008080801d0300505611401c4510710400d42c05402003100d5423010542e0090603004861102c80c5506201d03044e4103038100b40c01039900035a4064015404c140007592801e1003500410790350800c5205550b0006100041c0840030f8000348030050103550307a42e0500035034106890008103400b040c10700400a1201d110300020301d609041c055511021180704c6810821000b400f91000100c1e40f40c0300700e000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 276141636 1250 276140386 276140413
    0x1e060815041d0d09030c060c0c0501050c030409290603190515060304110a050102030a0c200a06030506030c0628050d150503010b01020a0210080c07060603050309030114161808 77
    0xf09502071780d0141000e00340e11aa251030480c1e00c0c0c141c070800200005080c18040107103500480142c14038008080c180c904054071548400102c5840c0c1d55410008428400c4003030500e40385a8462001c0c4000fa61910b203035190400c402120526040d194101c20395484001490961022002d4910504001c020710360b02c2c1018148080701c0ca00a1030101e200d0703c0d440400240960002045540c03010582c1c550484558803500c17844101d00e100c221107641c1180080b4091401d91310184520702602544e103000a1600f0504103243c44c3c40c6014035000c0c095442005507540d03028043c2e550b02e400200c10b5102d9a810f0440364021603050007401d4030040320600f00481c1200401d6228010000d6a50030380c000c21012011400480c1d49124004002c0e400c00d04036804440b26030310034200554090b00030840140f4010700d5079624000c4902035481640e0907000403030110b285240a0151816050032025501c100341070902001c03107081d10014140f001e01034030030300c0b511280c16400c0444008110071f105403030b0b9401c840070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 276142886 1250 276141636 276141647
    0x20403022107060504120b060307150203030f01050406030b06130b040c021e0a0b0f070c080f0a080f0103050d0c02010e04110a110d0f030906151e060815041d0d 70
    0x8040c401c450240c40d1000c14203d02c51800e43d0102c0780c024030800b040701c50b1500c80f000c03004406000caa40500681401088000e0800201106031a0a600942d03482c03416409205004d50103030407191189052010400c04a083c1c660201e42005080341e403581009220740b00d4100074000c0424a5420609009810003616004118a00c000101280c2c1500900144480d07603201e020b000001040040c40c0c50200761001c841c00345103580301c0c003030b420400c0d038590301c03a04d031076120750052a07991184010001300100c601c0d07070058869402c900100b020139a035504540c0c03041c0d250030000d4147c00030840c40420f110b05583c031580802c408007001800400111075101ea942c07103180d00c001450400f003400c19034a020b03c0d000000704051054160703559000c004425080860240a41510079252140c0342d804040e0301d4401800058000c00020140082c8142031018411280c00c040c0e01c0302c810b00601500b003150403030356070003840f0065000300d4000518081c920030911410500c0b2502041501c94120030300d1b481604134 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 276144136 1250 276142886 276142939
    0x70509040f1a090610030507050706390c062d060501030c02060108150604060b0c0601030203070b04030c050f0a031205090102060a09050309040c050c031c0c0e150901020102040302 79
    0x6400016030052540c050055074942500c0641d000040a80300c04c0c174441c42036111070780012840c9401450400a919000140c440e100d043c9040b20190f480305810f8019080b07071079400350214800d006101458108064601d500c9503201600c1107032240d07081192020340124a100e454200880d101c02038076100c00b039500414550080c3d0b80070900d000006401e950000840c80e040f108040d00a040003000b08a078050b00c0100a824240c0107622000b010800d55040d901410481c1d18503001401d9540c51401018584841a0f02c81224404204800c0c0086415500f00c1c0382a244240e0b91415180548000304520480d29440500b00001b9120021242c551090080c80048402d03805c8440a403903000303040d01142c1c40b142004040380d0007000004294202078008096a04c2c0c07a0134254140303404000c9190459100ca41c440c904204c1420f641d0b8517112462088100c02e032a14542210500480340100d505907070115a010f0605a0114280300203a02c00d40484000e03540c00740c01d514091600350250340050018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 276145386 1250 276144136 276144161
    0xf02070b07030b03060a18080c0d0905060414040207050708030f0a08010801110a0e0d05060114030106080d2012120a0b0123070203190b09070f060e0405070509040f 72
    0x403003000c65a180d20900030410b50300c1d0000c01814490b00c80c5080a401040d000c420414880300341840c070b2010030220310142c440c1c031300442c01400b1002031b401e20040c040c43c130700d4104178490403040c0014031100001144a12181d203085d5401a5601c10904011b0318180703596001d442c3c5448000343c5030001c400b100010301000c1e40c1c00d032940b54980c2d0302d490409099521520603d254050140f10f2034090b103100301c5038040c14201c09011042200106d0315403909040c401d1300000b0032020003884c510590f003424840c070401400010080c00003054020402000500b08494100c8048020480c500b035011050111411600b040040c41382c1e40e0440a003a08107004089964400c02850001449541d501800005c1443e0032a168103130940341e01070714424940d8128440580c3c02d481800e0750345010b4101d40c880d802811340540079021152802e1100307680f0300b40154101c8030608000c04020001c054020384e1181051404980104040c0d858080c12681406400e5205034000e007000e4200240e031420794040d00c4801d65 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 276146636 1250 276145386 276145403
    0x40603030207050a090e030a050f0904060b1b010504050c0904031e030b0406170627030c061609060f2019060b0604051f0207050306040b070807090302030a150605040f0207 75
    0xa888070030a00700c8140c8000600a50010800032101ca031068008140e8010345995181c100bc1d4414007060845a113a006403480034800901d0f000440004540d1111400103500240264a001d40c0c0703e580b00c80d10301904d50300540c14080414101030003000500803500344c5101c190a0000b0140000b00940b10095085015030314155001c610450401000680e6035000703001099a41c4402c611240824101245000c180e060084151241c2d03a09100030720500006800031300700740c10095404580d20f5503e51004040c4640d1290400c01280c001c2c00c0c03160400360303508044c511205204a0240800307034114000000340075444400d000703c2690304e040c01c020350007401d080050035000402e0112510480c0113a40d406030b0142880342401410b91281c09010005205a075100380d0350740046403034020140c6040b40d01e947c45804204e4007a502190f500d82c401307203901d00350300b6652554001c20b45408075413801900000b2203540c86002c4a140d070700844010f00014008115818000401c44020340010004854204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 276147886 1250 276146636 276146639
    0x831030215090a0b0f04050c010e060910030911180112020307030f080a02060f150d140a080c19080d201c0f0207120f02150a0b01020609010e1e030702040603030207050a 74
    0x5044005c0030f841594044000e00d032003005c080043d520b5110000200d68011001c00400215443e11640a030110805440c04540c030301c894600400703846140b0903803500410407034003040c1240380100445070468130ba400c50481d03d22168000b1070b0802d0a80d4101600c04003004007103804019140008007510b01c4550b0235144651030302421503812000035900c2c180f5010390101002d074070703150070311406d2802403250070105a0807c480305068144010003005558401c000300b9140c81d4150248004409100c140042210382c15241d940c1c00c66034000c10580040880d5071340d001c101c45030701d003030802050520703821344068079020203100101c040e00d046100148c8480c1441050303600010240280e49555500180f42c16034009010000c0b2214645d000d050000c512980e00445a00b00c2040d410740d0040c00c07144004120080e803072001924041010701020a00e82c07400d110354074004000b18469800081810b603d0000607030011034103156009d00c84010f5030052511000100701600014a40c0454405a44030034249 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 276149136 1250 276147886 276147901
    0xb0a030f0e06011a12130510090c0e09010f110c0706031b050c03040905040c0911120c0903010621060c0206070215060a0b0d0506010831030215090a0b 66
    0x72518032031510800c1d444000140b1207200d0f2440754214014051162a06140c40359031407448030b040a59101c000c2180310007540c001d0241c02c0c002c400748100c42c200c090040b0421950b4802000c100340c410301802070310010100d00101c20030b4121000441c0c82c2001070103058071001c82480e0b070358040c0d41d840c1900e128482c0001809400b9010303001c81c1b0ac0b00751040510001c10002c0c10740c2c840c0d2140c0c00e01841e07804204808071303114a0f01d1040728021806102d0400002c0c0c2003e207100110790803a4044c030100601440851401080c0d107401d0703507100a000414a844601c02e41c00f003405400c40b03400003070904440d070f4a251843c41c2c0380400101058003c0500340305150300c04005903140d000503940c120041e08800c0c002d19503c03464440c41a003004000e000d0801a44e50340003510ec198100203112480c040d15032080c0b080640c0c2c010005d0f500400c0321800701b0080084603514109040a94080d001450520000301d4141070081c00051080e2862a50841d07103480c000d00c196440e100c05c103104503503400781c2c6170100b40c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 276150386 1250 276149136 276149141
    0x31d100206040602070305120c0306150c0a060e0102090d152f0702191e0501080712050a060e0c0c070603090209071d100203040603050108190f0303150b0a030f 70
    0x191009038018103015116901c0b124081c0d404a6416024008104061a2000307925072106226110062101e6101d007018410004030018076440b0686042c001c1c0010701c0801400b04010003110b5001f46c00045140543c809e96019000d810111544a503084a024050050f500d201c0c0b010190a001c007003050301c484404c081ca15803c1400c00d20405030461000c00102601c0b00e005114007400140408401c9016000c8185221386a4111400d40c6030010a88400b02ca2080d940c00c0c041d160034240f621031440e110b40020f0507805000300c003104c074680b0b1b0fa002c100b00440e184c1c000c50107000100b0701401c0b64541b00c4943c00c0e040c0d01a07900ea036403e00c6041400240f03e4442d10403041001d078020210a0b007600e680781c0844140300c071404011800d41e000b100705215076941019040c0001c103107030040d42c0c4452038401e01070308540c0141e10102003034008900c0c1107603241d00c0b05002008039500a413410b86004803410308038000c10b03a080158600388542c2c80082465500c010141c04500c14560f42480b80306c10f0386418106 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 276151636 1250 276150386 276150409
    0x21f120e01051b0c1f020a0e0d0b0601230c030702090c07022d031507090b0c0709020a1e03091719140d05010905010329060609150304031d 61
    0x32000d10450031405031403601c4008145040603001125600d17116600d61851250195901d40b004a50000c1c0160b0007a42005400381e640100f102d42d1a92030354640c4444c18040c070010000da0401c83c18100088071100160035422031002e803801c031030b9110205140d05aa0300e0303000325002d901c070705414400030703800060310340440e0a000d41c0540403481c1c0701c3d409402c241c1d4018032072400002c14092400e1540c4240c80802051003009200a500307100341c1030143c1e000c0c103c41d0880d04804c404c11410000b68400c0c03a000140c6004440100d200103940c0c081e04002103c4e900c42e0200203001c94480c0b0403103451000d0745600045c00150060700d08003051210700c102c040140c03140d000101040c2e2014000358440c00d005100c1c114854110903e814a40503e008103002110001d801c012071140d51003005006000c106029640c810f01494030103007000d0540c268800c2082c070001c000603c1241c2c00a68020300da15042403107440084680240741d241d080602d0040c11481c803220805038803422090078040a440c0c0020040f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 276152886 1250 276151636 276151651
    0x5060c130e130809040902061305090702010b01140705010b090901150f080c240705031e0918090709050702010c030c03020f0a03021b0a0b0a0b06091507021f120e0105 73
    0x180358286946501d03184c2c0210810a1340f141c0e4468030400540c0303070000144a41030f540005055850300380000c00188480150804d011a03142c00381000d20341e41c1119a00e600000900304090b180c016515101c1d003d0210316a0140e0060b5020b401d10038104815000003082244200d06940c55507101c0380300d0404030f0100d10481c00030b039000103899486810f101c00c4282c600c8411118405103506c400380748031444d90100d02c085410340c0c0300086484400f44509410f6209190b40c0c5042c9180607044800034000460400703541c0150030030040421503a560800c074060042c00d40c07030402d20540c0f4000c50080e0003030414100141c0402d0030100894003042c8a0301c202e500000003000c0c1c0c1810082c040404a0003508441060484085101a0300409003002c21000c1d80e040d225120061091511803220426200304410b000e02600c41440388651943e80d02d0805600c4a403d402c001da00d40c51240001011003c1d8103040021a0900d121185942c07a84051841100300085506108024826401c0d508a600446814 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 276154136 1250 276152886 276152911
    0x204180641010302040c0908070b070c08010b21010e060a09020414010b0a0e010903050102040806190e330403030c0f02060c0d05180708160b07050606040e010905060c130e 75
    0x503c014a8590300041c2d01c00040c0c502411140c0e1034812061601d851604400510f02d0040b844108114121200901070140c54000b4069511060081068454a0721500003004e60582510308052001d600c003000105444007200c03100c0c2800701260008011240c41a8002c074144004003a001c140c1d81152412281000b0b0105d1802040780e10480e8a001c02c03000241c10800190000030118509001800281110402400460a004151800ca015200a0700103081d04048426601c0e603008078014038080f03822429100540000019115801c821000034155040c0b01c1080c4400e244e81079101c600018016200d41140d000000c405a80e1441c4c1151010207041d42003041c00360032410380d007001d5045520201540410130007a00a07a041c1421900458803650042a1406821f0075034440d2100034000305100c1454030921b611a2500c1d594020a03d5010b076071107480c0b00d2903c60707003584480005504441581c1e158144100040c0d43c540c03120b41407408048100c403011070b501e401880500d0181455243c413 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 276155386 1250 276154136 276154139
    0xb06010509130e01090819020606010f020a0615050618011d0d140f030d0c08061f08150d0b0a050c160f020a152d0903020418064101 58
    0x645028142e040445042c6540341c17400c000000364184051701010442c43c004444040611900a241c264010009410060070b0412488e10513008034854065681107003003c50041c40d0355105003560403442e400141c10a00010b5110344113614100c00600b00c0e10260798900d80d0710f16010070941c1d403d148800059100600380c4031000003e040c4d42034001c0ca800d000d03090340c40c4101d142c0c0700d540c1503400c003e01302440e082d01d89a004006542c050701140d03000c0c000711006200e040d218116120060408501e00090004c0840400e80d840a102c1042e54420320003440b5243e41311319071420b850018429141003c0b50f80c20403021030f20359130b203840540da02d007c28004101c0c400100390701d612140d13403010817041c1d8010f9421b41020500b001c40d030b510170000000a0b01e850020308003c0850789112600b20011942003ca1840c005500a61001e000401c40350103c80100d00626541c00d181c0c00680282401002c5900e01a0784c2405a080040c070109841741528205001d14610400102c900003190f00501d191041c1100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 276156636 1250 276155386 276155419
    0x405130f0b030c01051c06091404030806010503070f08131403040302040506040b0d0201051b0706030c0e090c03180c0306131a090601050405090309030d0207050411091f02150708040b06010509 84
    0xf61102c1d0700b1200d280110b400380d9141000411528800c1d441e40080800008210605030010782ccc4a4102c00c003860b0082c0355241410004169031081c1c514001040020408900740038524413803090b2042c2c003c02210304d148907440013144d513948948402c85c000d60030840090b83c285007030311669007030000c082d04401d401e0920354011109c641c01001c9100000700c0411081640c010100302d018041d1200d03440c001458078400c0e2024100081c26240e252142d00c4120820007640364510a0726000383d114015000c00007c20305120742008114412315400d07200d11420001c080c0461004500d28501400c402201759001c0d0314150300340309048400c2032140d40003c004104a04155100641c0300180c1c0c2c091300c3c141100b180001e401c218074070045200590001c00148801e06e45417184400e55170740f11b090a45040c0c0c03100d01007429814240540d4100402d0701900c42c049600034481e1416500007010020a1490034100151a03000c00307680903034010350346100042d110b5028a0442d046400003c0140801c60035092 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 276157886 1250 276156636 276156667
    0x20d1109100e13090f02011e170903120a02040f1d010608041106160203190b06090402010314010b1e070305070f05010e0307050303041b030c09110405130f0b030c0105 73
    0x19201600248440c006448042e03d0744a00c0a042d8850030464007400400d000050102840100d524910025043c4170b030b192580240d184181a400a01e01040b40e5641e604910b0070f50207141c1d40d00249942450030488148030301d0303004000761101c0721f240e003c5054407003102c5844000c401189103510700141e0014081103000e00c0050751f1282c45403940c00c81000c0c0801c0418003d402411140741d40400300c48500007180f8080c8071021a06004904219a000158a82e14983c03500542040d000d010145c01040c00c0da44250880b80c50101d0000d80b158481d44d440040c00c4150f401480101e07001d44165005202c0250305000b200d044e5501a036585041201c01d403035150303081d05080c000302c560303659130366160101d60000e00140c2089400b0b54091a100d142c00d042c102c0c2d000d1600c0c00c0c58680440c81050a20001e44640100700584d881c0d6540010700c40400c2100345224451a044281c0c04141075841441c9c0403600d40102601d81040f0105120140c841c4003419500c0c24029141404101c007400014030364400b01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 276159136 1250 276157886 276157907
    0x3010b03010e13020a062c0f040509010f060f03110109031505180111090103060803070b011802160803010518220201050f0d020306030d090e040305160213020d110910 73
    0x14010200803480a44c0000c4c00980198000ea01155080780002c21441a0701400350071644103080c005001b20400c00002c0e040d500740d091051040c2d907036001003001408250301208129420240030041c40b922040c0c0c00b4a02c403110b110442c1c41c5901c41c124241c1a5206501010803a0b50041e80303142190381681080002e090020b1112654003c8088500c0b10381809000c0d6174000d448502d4115925280000010300707460391034109081c10780c02000b90030300003031107041c01604490030013054100d40c249042c03175440a445030f031440c0580e00300820051024420014001d40c100c903400c4940e03100494100c08620030780f01781140d01d40782c0b1034940b0000b44680042c2c468258450b51051608501d88401e600141c86c2d40d804ca0900002910350100030040d80e82400c016400304401c060410f13114240ca004a51141500010300c0141000401b146034005c94848940c030050260303004042c1d003020031240700301c0350080d00000c15000c402da042c070790b01c20401c0110034100c0d4424600900940b0003138007405400e40720040b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 276160386 1250 276159136 276159151
    0xf02030403021c0b040b06030d031505041503060614041b0c12170901050115051e090f180727030b071b0303060305070608010e1506041a120c03010b03010e 68
    0x6203c0e1180011060795800e4811407040f0700503500360400005051501010f501c1e4041454070300b120103030060120704403400440b0012034021840c0514940403e08101c001c5c0d000811083c106180415a5035a403902d40b00043c031b05460070043c24407800c4009401d00b9181f251000407508010703807400440c0307840403080008101414100c0c0035161200300c038051403104541400c0d807a503650005000351461140e04503103008492400328208580718242c6580100c200c0c190444c10b00001841418030b448106200100140040c8041c0225021101c0c21045001c11035080d0002415002800100c0f410700c410780d4001c900c0d4502c02070741c1130305580c3c801480354800340c504014418030004589a00c400110300c00c01c0188290380210740c0601d50b00e0b1441c9403440541003e000d1006031801802009c00e0010074a901c02528400454620240c40108210b07100300d401288680703485000c040514940b0b0030003050f02d28404c8441d81c00d15601d90105400d00e0000f801009043d0b01e003040104441540e91b03c2d1705030880a03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 276161636 1250 276160386 276160429
    0x4140409020a0b0a1716030c050c0d0e030f010c090b07060f0509010c08010902180108060613030c062a02010c030e091003170405061207090b0307030c020d03111c090605040b040506070f0203040302 86
    0x2140080d40d103041c0100c00e2f61340000340400c8101c0001c0c14180141c90741420201d003b4440711005a10261101800d07000d5001056004102502402020341002c0c4408600040421141c00c00140f00c0380a0002d00c0a4a07001c90f00003000041c0c1c00406108581f0301050201100304181c48040044500c6079010300b100f80d0188084c0b01078540e00380d5074207803600210304c52013800c19040e190000c0a424540c051402c4102c139009101c110500c0c03c1c0a6108010465092a013010640120b1805607008450f003d54650080001820027110b14000c00c1030005480c0200c807480d0b00e00036609440d00c5103105600801d9000f48082c0074501e01034000480c1643c01182c2130400b4803406450b01e10400742600b04881100000ea143e0241e80251901444007100d604030b6031a0500141080000104003031050090351a581070301d141c0e0600600741994401451503502c05814089030815003080802c1c00003c2e28180c81900525010951141c0070309002201155990069410146160200030f142d031040441007900c1d15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 276162886 1250 276161636 276161647
    0xa05060d1509031403131202010509062d010e0703200a030905070b2107032003071709010b030f06040c050f010c0803090105071803020604140409020a0b0a1716030c05 73
    0x1444e40010310300c01c1c140340c0b607841801092800c01c00040601d41d4290425a41f40805104a038400810700c1351344400200c850408041e40c1034084000c0c072206190007450b071900071001180c0120410841d901814481c0d901740b00c0750030b10790844854000e201081b44c1c41c444040210320718403400b0360480700d140d80c000c030103036990345944084500540d80013001c0c820110071619800415070124a0505030041490302d420422008440c1070140380c028072a4200d00c1c002c902000092043e4800c22140d403100e0203000c06d02d02d09090050146000c0c02c4e900c40d845210b401410302c841400840054064821034010390990a2a03250406001d8070744440c1c2503690400140c402103c000c150003400942c0034078550000003940c0d1424050041c030829450b40401015441e00600700b0151341c1d0358060301c0507a800d5a00f402e03200c42810000270014890348400941044115800050262207032001c4c4c01b10101076101d1000903000b65016180142c0c0c200c9400441850420408851510075403081d03402c001c20f802d01500c0c06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 276164136 1250 276162886 276162917
    0x11121314030f0312040318422006090304060f0c17090301060501020106050d06020c01200a030609020703050d0209030a0c180605151207021f050a05060d150903 70
    0x160300c40000030103821341c41028442019441508401e41000a1601003903150030070002c031a80c0314441c3c0000000d201044c402480030308002000100c2c1c0701d12883d42c40004a0112009460014000702942000c0329003281032095210201d983c92003900580051442c0030f0a1030810303107020070704012400401c449000e0940004000414580030381c040812400e440f005d02004160944d031f4140c10050441e4100f020810283d00c90246180040d0350203100580c584030f03030540d0f01e80100092016462400c081d8800c5c0c0024000c55401021050b8482c0e409200c0181c0703801914081c2e01c83e9400c001c0025104100341140b81c00941d0140200c0318004041da50311040c3c50325000702041103600306000c0c0b0320b104010300d000644180729401c003c1c0800c2d6660074100c1f10355802c1c40103c0c005c07000c01580021078003001428141c130901c01c3d02002c820745070341d6880c288881c104603001040b0071641749803590b180c10081042480c05800028080d079110342581e02d84446880303650701a043c038003002c83c00c0c0140e622980600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 276165386 1250 276164136 276164143
    0x31122020f04090f0e060106030911040c050a080901200c1f020d0c1403010302060f1b010518060609070e0607020a0905060418051c0c021011121314030f 67
    0x400c41c1603844241c40d2400c0c12003800403a0515800c200d40300b4940f640f06140380c4d82c0461403c3c1180d40a060000b6981d86508001000c0030f17000003c55401460004070b1405940c0040140c408503101d80c1c0c5407415070b0745210f0218201c030001645400d106030810700c200200b8010310000c004552114081d00c04206002a003540c5450301e2090004486402144405030540b02c0c0c4251025412285040a80d4240d10fa0b0f06041921041c00064096240041d8500d90707500440f045076003405981c1c50b035000c60020005424000c09080d501c07444000814944018400c6002071828000d0000410140240e268120180c90043d4180c516580040d024010000036984031150b4000910005030041180e203490001c0100b241c111200e184155600c2c1d0b901540402c0c6c1c00110908030407025042485a03503a508015181525400c100a44c000360200d1002d40850340100080501201841143c194140d041d500d070145015030b52022982c00b00d5a00c04011030307000410041c03490380340075040d202542c1303c00b0b0f03400e0708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 276166636 1250 276165386 276165397
    0x71202060a05091203040f0317010b07050706081e072001090605010801020c030406031104230a080c0102030909060a090c020303070e030703030f030506040b09090106170703112202 79
    0x15810160400603601c0450003020381c401c004034080c202034a504a24480a800060303c0903094400080420003010302824058031400d45110030004c0d60b42c0d440a5042c001d41c07088000704c9060065160014009000d070100034050b070104200b40010400c841000281008020000743c1040300c1030303150180f2440740a1200c86001803113000810640d001d410130505865061f401958240e01c1001090061100130007510140d401a10b0082001d10201512070094041d07900040c00b1000441502000070150b107503283c45a580a850440c01140d8481200d6141e0602c940f04034096041006800c1052400505403540941f0080815024503201c0c01c03868126040c10610801590000003800b000c2c941140d41c0190156046000340101429507a00400203800d401900007415192008a03865607540d411030030000300064010356882c9890300079503018060501c100b840441110302c1804071410045501ca080e2500907c050190b2000300041c000300011100d01100d82140750410b000c40c80712540000c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 276167886 1250 276166636 276166673
    0x9060602010e150403050318070902030a0902010215060603012c0c0405150a020d0807020f0109150c050f030c07030c080c06010f170601061b0503030c070b010b0f030a050c07 76
    0x20341c450b101050589003440c403100050a0103854010400042e84c0003049130750204a44501d02e05107048120740c5490701d02550401090341d80084100703c1e042e122607100c81c080500036800c4480c4180d040c80039a8202005176100380e005101040107204900b0061001c18500e8010303802c0b0826915900110200c0359000c2c1c038030307140001d400182080b8070300c0c0042594104c0104901c000b0310b40f402000300699160f040f02581000c0c82185800682c1c4940280030385890700300550f00901c4505e0f0146400c510304c0c81d1103011110300303914100080001c079210344142c03940405030740d000300e185844210b060740240e00170f0354084007080038001c41400001c010703202502c2204034220060007294101505107241d180640c2182001c2104104454559400080d00c1c904440d444d082c5591201000200614150b5070050050071a100005c2030114091005004282030360180007a001166250b031030b82c004a10440c400190403031020b002280f11303542c06502c02a00203401d41c200321b1038000c0704c3d43c40301e14280b038034040303507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 276169136 1250 276167886 276167891
    0x4060c0e090a0b0f030304060503041e02100305011a130e0408040315020304150b0d11060904020a0504051306121118040b091b03070b0c240114010309020a050909070906060201 77
    0xc43c8207081a040c4424002c00c02c8010794145414860028174902000700090071820500d803021843ca4100805600000d40240003682e8104071003c01070050402840b50440f1280031039807050030480d1010950308400d41c00b40c502c1e04801e1916500340003d0307001400603100c5074010071000002641c15444040d10303441b1000096260b01d09414036951115800c03240c2851142004005015540c2d04100000e80c030f80d2160505c0041428070003c10b000d40130700c01519030460310000b580c04002d50490050000c0381d0701181c013606001d0004900100740d0b10113115005400c07440e10181000501d00000020000e0000b5000e00d14180c0d01c000542842031301681d05481140109007484003d18040c01040c407480300344a0755080c0b091046c2c003c26a0361095200d508016280400d2036540c9260034070014441007500b80c0c15440248000400b404181c0017840340304928041088030380700c03550107030044940150b0014503070348805192109000070200001c1c90203e0a015020001c140226507220314400b43c03003241d000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 276170386 1250 276169136 276169151
    0x80f010f03081c2306190909030905040c0207083d1e1a0a2301050715050f09060c120712060303031d0304050f060c030409050702030703030c0e0904060c0e090a 70
    0x46071444d400380c03010380182010410060800381084a0108a840d640000200419241012500c54540d508055070081c10005450000c1d603000880c882500c00c1117040d18010702c0516400d121400542145260000d0000101400c4819442d006c0c06280a508030110308112307440704210080c0c1040c00519400c0b55242c0c0c4e82d000768203054441b0240d80000346da80d045150704107440b442d080c0c00c06001c640201c03820240301c030a60740d100300c0a031030086a002010340846101450303100094502128000034505000380090b0281c0c42c0005c01c00d00594401124628050103540610f0b0884401031900c82480b00c600303440464418103110b010001c5021760390010b112100002010701c09000000310b82116402440140b155556028041d00c0101084402c2079407400250040ca04502895000e110300926003030801811980200c02480f40a1290743d0403c100e51031410103480c40071144030079681008890002030b000801546c4412524521411301ca5150414140000d0b90300f60101d0751b219046460703200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 276171636 1250 276170386 276170441
    0x30301030c14011805040507090b0705031e0a0c030c0311030a110105060f13020d090c06050a0e0105180d0503190c11030303062404051807080f010f03081c 68
    0x82d0341d0a000003441c14201e01000b0780c0b910304154405019907132040d80e4690100b00101d018094510051201c2c107502e03070300c078a4241095a100d4001488041e69001215030711301282d21030404940c1040c0c040e49844644001c651021150314422800443c117010b0450760021009504101412540340c0700e945441621187c40040303402e450014003450301581d1404072000701743c1d0310041c0104000941082c01038a520342d4510b17500c054070960402401c00000a00041011903000c40200001640758441c0c540c16042100115405e11503060303421040e04050740f440d0306074034113021002c0d0b0050050048a045c0010000401c070704038501c8a2a002003040c0e4217075407040100044900f89200000c030055800c52400e44041142038400f5009415001e102c4842d03041c0203da010240c0b0060880546060509158100718200c565001d07117050001c111610700003807030211041580c60607102c0684030090102d01e940d581c10382d16003000985500c0d400c0402144a0f020a4034131a49049809216030405010270418 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 276172886 1250 276171636 276171659
    0xe0a090201030e0c0d060203090a390302090609091015050a0e07051b07121a1501090b0904020909040506011a0405010507080f0d06030606170a02101b05030301030c 72
    0x1081c0003d03608070100801c25551102c55141d03005030070030800f603926644c03686010b00700102944028880300c10400d000f8042d0b0144211b1070031b50307018049442c0c03150036000107515203003480c0c2c072000354803d059030002501420250001340d0010001011521400c1e007407e0200d00307880500c84260017002c0023000410203407800030741050042494150403101ca0034070a60040140c0304401c000c46485801024800c40c804003017103900300900c00b1000103201024180380c00c09484111040c600c079041c0503100810b440da08620a4154a014141c40700f0740e803070f440e214144c000764201900c400e0313005a080c4405071040e107602110600c41c500c00c2000e4951036061502c03205c0785080807410038281c0700e420b001c1840180d802c40c045461564204401c1525a200e14000304918490444000c1541c1c2c1003210020410401d43c0003d0180d90901042064010f05070301210f41d00c80310440081d6100079030540d5a074070703180107081514400510074134038a20003807107455291070342c2d100380d008031140c1d03034501d0f4104221030a24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 276174136 1250 276172886 276172901
    0x1a1e1209060a0c0c1214040b0d02030f010803130e060d0506090307030f0203031012080403150e0d02010b0901090513050601060e0414071e0302160317090a0c031401060e0a09020103 79
    0x9080c90184d4007015200e912000c000100140140b110101c0c84d000c244151500303540c02440a0700e00302c0d640b1040c924041020350000e03074803141103441440002c5000c03135020003a40d8100d075169408181903450880c19541200000d89410740240b500500400803400510501d4440c18160000310354920461500030540800700c6c1c03000c2c045400500510603a1814507015a04450701e040c44251264030900304041e1a200e0703070340700400440c1c9590020030344041c0e41c1c010300100c11603141600d101c2c0c43c441c0c0083e402d882c001080301d03502459450050140186a500158012410071f6000200c00e60a0b0743d1a4503028007038000c10080784529280319010318041c000c4440314080c40684e030025042c04080640b01c1c0d11186040f050b511442c040c001e0031240f1030b0303066554100801d40410380921a505000d0f1940310111420110540c9900015a20140000c0e50402c008d600c0341d0030b07002292941c1c403090305954200050103444e5485650000e00510100b1106000b072484420025540505100140845001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 276175386 1250 276174136 276174161
    0x30503100911040905071418031527071d0f0108010204030b0c03090127020a080c060412030903080f090f030601050102030f0c0c0306010e07091a1e1209060a 69
    0x9000d1544500708002090343e00b140d103040c1001c01c107611448010f660084d804a0802036000f0089011040e9840051340e540e017908050341942c0540c1c1101d10074100405c011103400041003209085a008440440080e5104119503015141215203c19803080b0288140d44040311340300040341403100c2c0070b03444000240140300c030000031440d2500e15070380c41c40603d4004003800c070309030070100009030400021b40043e009110101c6070840c4600c1000340c2002a0340040c0d009070b0048400c964007251051001486001c41d94000317001900f058a0040141d8035000d10090407810443c0c0c44070000000340594015105030741882d50056194071510040c08021080c0d640046d00c41d1740494010026039070003004a40000d8159a5800d40d03034640200000c2c03402c2290081075400d4402d22000040051100034034a00440c100e42e20710078280c0d55031840c070205001c001c80310351640300100a03030748100106c0d0082412200400c1100ba007004080c0505100c0074001301e442186903000750303041100a111350300c20700107100c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 276176636 1250 276175386 276175391
    0xf02070f050d03030f0b1008070e03030301080a17070503030f22020a09050c040b070b061f0e01050a0e0904120e01021603020402030a090b0a2a080f220305031009 71
    0x14103000118628030102e0302a0604d83d8500b48090303178003403503000048241c10290108000a03120748000305413000480d83d020000310408607482d820316000c41140c0c100d920320b9004080081c0b58ad160302d40448484a509050381104001800010300103202075481f96208420910140c9032400340700390441d000c80c0640d10741d03c03030301081140180d85d40796983c02610140000000c4a42d01c840c80306607680310b26007084801c0000403903100e0810074003017901c911664007030f02d030039400f5680031020040040d150761140d070208c2d80714442d0b9001540305201409103000e03e40b400003840c0d014000072480c181003d6a0554045d21414014680d80390000600c0740d4031002840100100040051000044045800001e100e0354000021900b0342c42143c201030b5034650800c80d030761707202d003007070214000200b880c0c0080b000342400310b0074001c440d904040c2e825486480f09403603040e07107030b5141c003030a0031908401040c600c621840080c070310394004607118407585a20b1203070301c47c1d903030304d0a003004003003540c480b1980070384021070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 276177886 1250 276176636 276176639
    0xa1b0e0610080703050403030b03120304020f0616080a02010b10020f0609030f04090f0609020f0c06100e0f04020409080310030605060406051804060b180103020f09060303031b0405040c0f02070f 85
    0x5070b102c810140e0040c854a0001840e440700d01e0100d0141188117040ea915106400303070301d040301165400650081340300707d400341c5c041d151140c2400380034010010743c110003080b03028000c004128910b00401081c00140300009003088040d0001311288541c1d51007500591000003211601c00c0100031664201b04d6a00003507084c00d003500c40c40715491046000702d01c035240e10369000114142e02600498040c001920007551582098040300840f40c00541236a4454441d0304085000c1c0b0a40389291010740351400380207034496440c1032120424100240c42203801c65954840307040031075000805035014004007a00010103d1540c10204203030b800160a0500ca6850410308001076642d141041030010600c0310000d91039980c0741005401820b010025a07085003061295980300d64410501038182c81c400c69820b400c444a40c01070014885e0111042074040c1c5c0100080f507501600781c16145d0400305030b903015503d050703250008141030b142070f6400c0d00c020404011400d52b1741a0140b10b140040c2041c207a0014205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 276179136 1250 276177886 276177919
    0xd020d0213080f0f2e0c03021909030201120b03030c1002090a050a0b0406080c04080109030207051e0a0311040b060c030309190c090c05090d11041a09010b03090a1b0e06 74
    0x30702c0b21000b07006030b180520a500804070071129620026035039000c400c011320041b01da0003401a5010040d95551006200040e55446000740003c1c1c054a4061391020300210091010b1001407407068a034683c540b1052101038001c960802801081d0707461000c000d40ca401492052058002d15074100b1807007441c0b10b003010b00401c08814181c90882d182c0f490510320684551005003d580700d0b60b000301e8000d5003849010b5061640000d03a08040304c2c02030312510008461029555440c851540c186648111030701c034100702180c0103603040e400e880c0c0024000603001445500081d21036004c02c10040d01c0b500040104446e14009225035206002c6d02d074095006400c581e5603001d150741c1e039070142016442d40c8543c8020004d106d03500b9a0381040d409054200d04504904107041d203d400408241e115600300400820102a00481300c5030560300580401a0369007002203c8803903400050440c0514494604070101103580c00345a0302024602056464449062220f400301d0510001d1603903005420560810814 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276180386 1250 276179136 276179143
    0xd1404121a0a2a03020c070b04030b0f0601021b03032a01052d0901110a050d051510030f0908070803070311160b060d0b090c090a06030809060d020d0213080f0f 70
    0x1849410f030700341d5020300800d0540c02401a2040350b086480b50b1b200200e07400403d54001d01c242c83c040d01c040b03076040e83d85608416110030704544042c01600049207464420a2461070a40c0318030b8010140c070300b0700c00100c551015003103415038028007a8003042d0340103641100a100d0181c0001c0c242900717559200718040040341081c80425040030400d005400110031040a500c00d4007244075940e040e0303a4441400308001c2154001c4100e102d4000d1410010900e0011f500b041503088010180404038450520300c0160b000b01200341c48551a2a00d91a981c8001031207000105015032243c02c100e900c2c0e00700510002c0458400191a410394101003001e510a00e002c00e0300720180e160b0005402a441c0c0e5588040754142c1c050010003007180080c001400164000844d54400010094540c0c2000c0c0d500c1442c1a820340d4050300c0007030702160f010402d107411410048014000c52509010162400303000d0003500003281c1c0f0002c0100d0441071082410301c80c0380c00c140304903520b00145c003004191002c1c801044544 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276181636 1250 276180386 276180431
    0x160b07031e06050907080408070c06080411180621010f0204060f031104091a0907030c0f0206010b03270313030c050103142202120a020f120d1404121a0a 67
    0x14408001b001a04010001d0111280650b0000c00700c0703205655000050441001550f0494952041429025507410071514111000402c40c8481c550340d1152018400412031803800e4100c01d5900103482c6103240c02c00d0040454426040400503912864804004d022142d01112441018144403141c281d440141c4241d400b074a090200000e80828841107202900c40c850f0b0301d00390001c2d80f1508020341982c06910600e0013000341d41340c80321014403010040ba2202c0c424010b140f0f0b02e5400340302040ca07075914419010710210000c1c00c80c03044082d6501c0018a143c200504548000b58840014030400c40040550130040c602820240801010300d00c0f544000a40182007031080000e48103100b50341040300751000b09964002e4622504800e610181c140c075005202c0060b8007464800c0614205c509000b04028400000344000e020040520341c000c40d0040c10f898040324118400307020105240c0d824119031001e540c03040c4260400d00ea0700c00c400300388000c0c0040c1804c1480d45864907044102e0030300b80702c407034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276182886 1250 276181636 276181651
    0x614040c1e1803021306170a02060304060e07080a1b0e0c0702010f120f06090c1701060f200c1002010b0f131103010803120c090a0b160b07031e060509 66
    0x800e400400301d4081c0482d1510f9002135480080d01071051542c544036880301c02912208401840e5107214004455034440c42e541e8000e4111800b080001c01084403684070440c02e00307881e001e1300c6481e07980e04203491038012410380c26034200340c8035007425524100c02240540200a0703001291510301c0d088100000b00d0046800c00703070601c602d07001802101d900c66116090b1000c4081000c100c2140ba41c01424000c21460090710801c61604c1000305482c0d00030320079217a404007a01c0b0004180d07800d14404841500c400c04042c03090050942c3c60504000c1c560607110003090042c001451aa51042c04109a055080e0966025039242c1198060b160b100c89240f41122082a28151108401848210b0082404403800300c0003500100000c240c41320040004d0442034100c80030100e20b43c5800501c1340d100e2086810642d80304402c808100030b15903a010203400d0640d022902c1140105940d00c074207000c0d10f4211040303000260707903000448002e00c00001484040f441548100507590815005c598021006005203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276184136 1250 276182886 276182897
    0x106030612150615030c020c030318061e160b0f0403120218030703060203040c06110a02010806010e03011b02160b090409081b07060e18010905090c040614040c1e 71
    0x140ca604506803c518001d142c2c520100c6041c0c03e910600400500000140394018000c032092400d4a02e000002d4555410005074003c4c2c8411412080003490b6200d05400c0176002480c011140700030315584003911125981c80840200711199141c80707000d80d50b00402c4900c1c0c001841d0244008a5480100b0012800d00035030016aa4804000d01544020441c2038080d4980318050004c810401c240d00503601840c40780012201090322048103035004044000300151913405510742c1c00143d84150291030700100107040031800e0050190100b0300f91000140c0c0880016000700c004103442d91b040010841c4182541600c64100d400c01c00018454410030285510a41d2203032001414015024116443d032035092020b68506541d010405071a4041845010045142e05a400640f820500040205003900c0035901d20b4980c20040038100401d80503220000520921203803c1c2141c50300d00c554806814503035003843e00d86204404001c00c2e103065400700c4041101652410381d001d400341541182c0c040c942e0425 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276185386 1250 276184136 276184163
    0x50304050c090a090c090f0c02030c0319030b2809090809040903050912010b09060609060d0c18060201061e0509040308070309080d0506010908060c07031103040b0408150106030612 79
    0x18031000c4d0124040c06002c8085c40c40c40024184090f5000c40080004100c040c010004071850580c0c5902410f491108240c1040141208003481e880d42062004403504000658060703010100740d00001c6842c071010b1403540d200e60801848005005c1c1001000f940506100808143d901e89442d4020740045038001c0b078840440c0390401d8001c809450a50f88042d242e04468408006d540e40680346420196010700c400c100400d2a41c244141102d68104002e0201840d000350002024010003200c1e00b0442004003040d406c3c0e425215602183e00101003642c00490b04078200114008540d010a010ba0f15400c2c0104080025844004440b035116805013018012582c4d04030064000c0e041828004210000016810b40c0c9180558002c2d80541e9013aa248a0303507988a00081b0b0342c40a096858801818060002c1c80001c0c1c03041d1064198580c1c0e2106590038250740d59000e811582240d000b9800700c0e005100c0b20500d029030403003040d004141ca031805101c1b2518055201c02d684040490141015250b402c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276186636 1250 276185386 276185401
    0x31106070b040506040b0f01060504170111130311040e07030213090b01030c150908060619080727200a020a050a050c030709150512070e25050304050c09 67
    0x2a40c009681110108070280340c40e152040c0c40e103400311800c0315202c00080218011800000301641031b68100e444007440c050410906104918030f41648240d00d640355a8050710340107050001e00b160016401c0c2c0ba82c20b040c00c41c03a1401e85203580000389402580b0f071607260080480c0000b4580c042f2a0140c030280c00da841d0050f110406000c880c8405062480c5403000042000354070104801150010107001c0468030300440c08542941242c4075502040e803200c40440c040346443c5000540219070b10340188109aa10907006090681e02d6001d2000a881d0050040d0030401c01c920b910034522007184200100d08808818071084010980800100a000b06032444814002c0018815040d003200c00c0f2142c202d0b603487d00340d40e54820406c0c0340380079014407200010038100342d014212621040444481c0510700f408248804501f06030424079107842818000030740700f070b240c4500703e0251401d540503103042503560341c0c0c054001c1142c281c18402c00504104100200c1c2010038090034008044444882c640c65020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276187886 1250 276186636 276186649
    0x8090d0c030803010f170316030e0a05030a051606140301060f090806042d170306032a0f01080103051e100c03020315040606080703020c01110409020a030b15040311 72
    0x204002c011420010001c00d01c8241c03252040112607040d00c0045210503070010032500c0340140605600628999001080024000c9070b902843c50b40291140c000f9a84d114002840c0c01001c0100341c40e242c004201d0f94840c0201d0351070f00700140001e814503215400700004582800c1c4014880d400c20482c540c0444c9400c50302c5614004002d25034042101c0440c241800c11850400d492805030000b0800c2049004041e0300b850003035032149410034038a0301c0d440d0790380701100d01d140d200030503080d418081c1039819505580401c0325a0080481001e11032a4000a2024042c3c0a204e0306091814404440d00410010781c001420b80e40c0580500322002880d0038058a40d0324002d01d01c01d859440398100b858401c14a50303da0302452044000107040d2820f4070340403090104454a90080714002005c1c04c0008000c03a010741c0040201b180c2c00000005e00c6c45290390507414517041600010300080d00010352000c0c85505020b4442c0d00d60302114444100c92202e02d02d90740c90b01c1a4400201002c000c170107081c1d007643d00c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276189136 1250 276187886 276187889
    0x60307110c04060b0d1a1c0809060301060801081504150c020a0215091e03060601050a2a1203050c030105010c02030102090a0603150801050105060702010e042c0d02030708090d0c 78
    0x341c0b091004079250201140c0c0c0360490302c0d001c2e101c54a08030003109800f5807800482c4407400041d182401304083c0c18a40003010b68003000584a1400c1003180c00740a84481c40110300030800c95036444195410004c100e428503845807086004182d01000384400700b2311000c46049071a40501d030008001c3e4900c40700342d04004100d40f000e50f205043c001c1902c0d103040c0f400c005058a000c01c860421401c4a11a20a001000c24000300d90b0161701440028080b94081c2d401050b90841070b0a185d0a0508007400041d42e60460700080049107542ea20410204940b40304e103040344031031605042c04646040d0501030b10b2400b05106040c100150726245800f903480030350480c0e0300080040e044420b01600c1d0365024000d06140501907022081490700015016410b101e800c2c10b8400040600c0c0c0b034250150011203480004c00b211541c045d5644448501621210002e444400722184880c00200414a0791074201002c040b603010a40d00f04012120000e2001d070126512148200c0d84000c2c405c50034100359204045d035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276190386 1250 276189136 276189139
    0x1080d050a2a05010203060a0602010e031603050d0606020a14010b0f06031f0e0601020c0613140a080a141c0509090907080304090b03070605090603060909010f020a09080d02070302060307110c 84
    0xc2e02c0005003840f9040d00214030880042e00c481c10381c030380e03105822805c940c1c00c110120000e8009101d0164010340c28503510100a0080c5007450034255070012540c100c030742943c000005a8820081e440800c403c5800010351080c164008210a002450201b02c00042c1c50741414441c080000000b6404044405070356446003034000e1140c0c2c10f6844102240c180b010648851b4094402c21072551458070b0088115481d110103080a2001d15140c17005104c440140ca00f12a40d1003245031401052456041058a03c028080d6003d00541110745600501b0171280b1690100c2410280391410300045e04082101c546803816120800c160ba20300c15218140211500003240030700000500294075403030f54000d288215012010380d0030b81c2ea41c40c0002c0d2001d22800c0180c0e03401c085c051000611500c1c103000e01ca0b6000305003400109004094040034022a4042c0b00c0c1d04c0c003c01c0143c18140191801001940701d20f500b580002d1081c5e5003107800040490200904440c100301000c00c9481c0c1c1030100344400165201c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276191636 1250 276190386 276190457
    0x3180f12020111121905241c05150a050601091421060a06060f0e212a03010c0e1e0604030309150206060109060c050a08040f030b01080d050a 62
    0xe0306064411540c0c2179440040d02540745c0b05c03038000e04003148601e0b0300403c120202d80e545c50b10703c0450355031502ca8203000350341c0c408c80c1055100d40c4400c41421145849210f030001c0e244411054030158000f64015201f41038051814007040166600500348002395140d500c140b003018140440040c560000144031081c10701c10090382c1d075003800d40000e01e49004080c5500c040c0034180d2607104c22100480d40c1000400002c01c1101680e00e1030500580f2040010301c00710007c40143c046d405003d203000c0206103c009210b0070203000400301d40810039400b180c0c0700210003d00c044820044020035080500e684035201c0c6c90a1003502000d40e2070700040d076440fa1009000c2c19103030780e80ca0401420f0301d0402c2c840c0c0c40502d900d0b1200c0700c229a1002c2561882410161950380825040040446000340b1280c01142c1d20b00c1204601c00100d1070440183c00188040c1080082d61411880c21040380c14041e03001070008e074007a0100a05003900301054514040075441e07c2d01000c3c0115000225100d580844a1007614 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276192886 1250 276191636 276191647
    0x2070c030f082a0714011e0f020d080606070b06180406091406092e060308040f05010801032004020f0c010b0411070221030f0a090603180f12020111 65
    0x1d07040028000c42c0ba04000140f201000b2840d141e40340b65071900490029401202080c00401c0d201801c200d031404040c90100303500700820b294102441010707140600400c4c4042c24a15009a04000703141c41c142481c542020142050408070310745000c1c1e050014075400020f400a46d49480e620721490300002c00c1c480002e4281441d0034407030001c0007912000d4070141056001078428040004045004106a030f000b0882c08003a84004007640200310364090801c9030320303081407211002500402000c0e600407982180e6542c6450441d9042c3d003501d5012506100d40076004201041360606102d07151440040300c016150b010b840040c00911660728407944840e404241d0f02203140d4158080e0285a00540b82000512620b0304040154000c10b840290b0049000b4484500c0e09404070494410b040c008003140c0c02d011403010180040c0d0800200078000410b034440c01c002003079240c00b9544015180500c101544002500c44420280c80810064042d211100e0900b04091003580b2200308003045807903450f01d48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276194136 1250 276192886 276192893
    0x2120d230a05010f050906010c0302010609150f15050406030207051603030c0203060604110711040902060703021605061809061302031303020715020c0d030215010b0d050714030a02070c030f 83
    0x154000e60710310101c28903040020400707861852404058520050030345000d0b55445004680d178000d807500803011035480e0200001c405200380a189000c3c0d5199030110400c50416000e00441551a88000144280800e10400d250381140c101e40c107980d040e25004d65100032600300146042200d94503c0d85900750121f00105041e403040c120001e0174800c1f0141c0d04507885400c01c11041e41c3d40c4420100e24010304204410008a541c0c2c941804000d0180010840020503000030310550001c003003c0d00560000c0300a03031100301c0644200c00140030304035483c1c0c0c240740180d003107100701c3e8644504007070041384100c0108040e0f9460f4a01c62801c07060b402810340d501d00d07020340c507007649502c0242c088001d031060210100d804010703050f20303608464041d801002004080b004201c842c4020312002d50960162001052034200c9a840d2180030300740948010365152844010038044030402405041041161012680c1105500c01101d4125078200805601c4070002d0a014112901c0c0d0751000303003129191605d41080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276195386 1250 276194136 276194201
    0x50714100c0315030c06110a0b0403020c130e030702040504080d061502010b0301052a07050307110a120506010303030b030304180b03191110030e03070b040b0105030a0302120d 77
    0x21004255018000c00d19408000c001001039804020071a44452801b440818441c035142e882812950044070b40035030507902d4901c41c0000a440950040e0440501c614241c01e10401e036a91a0141803001c202e60300800c3e10f010b850303010741309000780f055441d00c0210b414820544103551550140c0303a42044200e0b134449920541220a4210101550810160001c1e918040c0703d014880c080d4501c0440f20f000c2a01041c000791401c1d0001e00561a80500c0350001003070301007014000c82071161880f180c0c1e9420000400005443c590310690f016901c00348420006240881c071541181d82c54240401c0481e10140080e08ad030180d500610101c80c0c00e5104600c00c542e0700d410007040d8440030b8080e143e0030b0520202d440c0ca08070681002400072486007680c0342c50380c00c0205070b10030a0303082860001616026054081e04640c450751040d2080c13405482400140800b9021990052800b02c000f4004010b1954004e5101c1c110108144101c1d1004544c0a034504515000310f0b20303000181010ba0b098a0700d00706842c20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276196636 1250 276195386 276195401
    0x324190f0609080c150f0f1e03040f0f0c12050a0b0106020c0303040b0a0903060e0109030e0f0112050c0d0509030309060106050406050d0c0918060302040b040b0108040305071410 78
    0xc8030040110008920740981c2c40c200680d502d22026040800d0310906000780d140e02c642421101684c20400c11044d14182c0c80030780309405014220640c3c0d219651040c0c810203c1030403020600c01401c00a000000318401c0e40c0105003035000301010756455840c101244000c805910202469458480302010008003242d8100308900c240208062641c81d0b1508995580c09441d245815078400c21080c4889214240640b00c420803e18000b074100c2e80307940e90300c829076403030b01580e00d600c0c1c1d102c0302c10008058000000b41c1102c0810741e584c951001450000030300304041503e00401761075a40c0f01041041c04404219000840148001c0c0f056041139882e07981d80741d10485d1020114040e62001103180c0d441072003214121541c5540f03140c10606040c0c1ca41c1c0c0100683d4820708140801d011000800c050844440400b100800ca00003c16510310300503c070903110b401156030322462038070031003041613070304400c04640103500f500d8925211092072900c0ca200444850b5580414400c6188000704407149402100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276197886 1250 276196636 276196649
    0x5130e0102310303091a090d03170609060901051009051503072303010b030603031603050c16150c0215070b04020109080d120c1701030b0f09060408032419 68
    0x160700164107100020102c1c280001400505100c80411080c6c016411248205009900042c07811a90b400090405614124210041644000b50742a4000040310240d44110241c0340008a886c103507002904106050003994860301103c413050200341c0c404d0110b00c3c040c250180920034641b580403010407039034008450100000305032003060f40844240ca00c140c03080e1035003080e00d00c2c00d40e42003481d000405c0d00300905094140c0b106004601d1140d41624441200e28081c1e12000c0d03985c03d603840024108503184982c80d05250307115108100c1c681e0b1410208001c48031034a08102036031010320000d00b54800c0a5a40c200e455408640780c01406440411507000701d10176210719501d0f550316060245c5034102c183e001c4011404010303584011101a800064458400d8030b040e02814290490314a2000001c2c2c00030780300e24403140100441e04c001119030030341000510f40240300134501a66030401c02d00c00106092102c001002410015007201c0e142121038903401010006032514001c070880f1803800311300c80c41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276199136 1250 276197886 276197947
    0x1b021314010b040f15020c10030905101b0c020a0312020a02180709060804020d12050c030406030f1d0a060906060e1302130b012f06010f03030906030b010905130e0102 73
    0x3c0c43c071600f1700d00402221542d401034203a03800e01c641003100c000c02e41d0002c0414981c40340d00c172100040e428448080407540003c0006440381c11024010b136182c0300890903505020340c0c0c0c003101e030241e0f98802c568401c81e5070291107001281c2c0603040481c03d02c040d4403002508030411030b11100b01d010307480408038420006641e50f900d0b425684c85049440c002e00b07036000b84d0055400d40c40000400d500c602c407003407558120700b41240b800000041c05440c540c4242e00040020b80d456024200c2c150540c02070300004a00a01d803034100308203007030095444000e603043c020042e5a1322041d02040140d41d0f00500c0040182e0400c0012625121441d0020231b40c40c0d610481c46402514000d9011400500c03491180c0101a9600d01e110048541d40004c0c04500014140e40e1075031704600724042c0003041102c0781c0a080b101002c1e007032030344c51031801601c4003259402810500d0306002c64850542d905c980c1d100101d60003100e41612041191a6820040901c492010559400001c500f101600c108c01105201191170400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276200386 1250 276199136 276199139
    0x6060c1202070b04030206070c0e07111e0d080a06080304090f0c0908060606070f050706021606110615130c02010209130204050303030604020c190309151b021314010b040f 75
    0x101d0300d540ca68011002d0f4030100740000d0000d418402c01401c0c0f5544a1010300c40b025072102d14903921003c049556200141c03c904a60b40103540a00018502104007034800d600710714800001c41e119038003a03410300100030700b440000c1c504602070b4000034010505001900da480d5258201440038000d8040c4a01d03100c0c0c1020070010401c4d104814600c116101c0402401c0d00352110b90800c0415800340c0c9040d140c101c848955540810010b00840c0c0090541d900100704604a0140031074203402160b022505110240c03400180c860750100d04264044540b8541d089280c0030380000503059460340030001003280c41d0041c400e11050b01540100707594141240c0390070020b00c240c03d04106a00c10390003141d4054005002050361400d140c0c0241c203502490300c0642d1020740944100e1501a801280140d0004000e840100041c0105804d10307546114a483c08808001c4000d0201119a98641009000e5a44034240080f2840e40368009a411340710400b1090311755a46031417003552500039004451525481420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276201636 1250 276200386 276200423
    0x1f150501020307020f010503091005010b1206031f090f12020c010207080304050d060b011e080105090618070c1b0e15090105031f0906110a232b06060c 66
    0x3e64a01c264028006021109035a00465060300b0191842034280b140811300100e0403024040d42e40039004250317400c0c0d21079510045206641d14064211802074101314485280b500c0841e4205404118850010824410303501c0c01d0007910400314005002440742601c8140700c0c079800310741c0c5000c15070242e084034002500e60710100c0c1c07030744200d01c02c555001c20f40140c80f100160f11601711510248050404640c806081c08504148140c04420035000a980700018401484d04040a44d0403030001e03280c41c80c81e80c0314a00d150041c4840541710409001441010404000f41d16406580c01164602900100d41c0e813460728401d910000d40300600d219aa18010b0320660500080b400e040f01c600500070010704d00d5146101004541003620705801c1500d031450100403030380500035100d404543c0144e140d83e454419100510301d944001c480350580c011460003c00a41c40e00042c1c5010306200d4444500107040714003680c840e0009101b068a1041c1060303070029655400c0550400003a01075990301010814003c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276202886 1250 276201636 276201643
    0x210140f060324060301020702270705040308070f140f0f0c030d202a010e04110301090b04060305070807050108010806010501082d0411030c12030a050901021f15050102 74
    0x2180ea00c0990f0120b456440e11004040d580783c211802034001880c0660580119284640c054840f604032400b095200c010001013039500b5620005910707165041a00b0740d52130502600c01c21502410038428403007940c0c00d10405000094150b80c1c9001280c11981c1e02c408110b0321410070b411940500c0c084d195440b07031641000b090204054106603290b411520420300030074003807880170845a50750b00c1180c40f00080020b50724010003420442a00c2d00c07541c00c0e410000105000c96030821640254200000e51039400848c0382540c1c1134800d402c4020680415000c04540282040d90010301a48900780d4000380080010824a080c0c0d4002e13603070020540c2c0ca8003400c0350307906000e00c101d500250800f000240c061200a00304003800d44031107031a848010b03007810005c0600e0340681d0309403a096028210b00c1b84900c0c0c10000205c030f81d034054651400c002c590148154503401129545401d0000009840380c2ca41c5c420701c4000040d007030403d00c202201100c619003000a29045031013544952402802054960000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276204136 1250 276202886 276202903
    0x150b040e0705010f020703052d0a1110050f0708040306050705030108070303050a0903060f051807230418050a0204050711031c020408010c020a060b0f06040e04030210140f0603 77
    0x80c010803505152600456401180c24555402c5010385e00d00800001c000340940079818980c0000800d04020940c41a0100c003103c050200081c0d0103070039520300045490703068031460b0740c04032007420040c10040401d80305481800700f0000849400a0380c5410070100c1c802030001d0301d0155000700041c3da078004054071680720a0094080319448603400304002171040d030040000c0c001605d02000003569075944c007c1555406600c030540251990101305c0c6071501001c0103102003c1200080c0300403403034255524140c2c1c0d0360f2819120010b01c0000110080d03100ca403c03201500840c040411120b40300c40c2401910b17000d0b2030408a21407030a140100c1e001c2845520003004d06002100611310349411114038000d01b038842c0402c400310300c0c0c00740300000e04c9100a03c41d1040c07010240d005000c0071011890700301d04550005a00c1c912846011508111640326002907805071a83c0c1030f13941c00316071224142070b4501442800e070864143c1c10709001c52803400d500010540038081c83e059501480d03ca02c800c05403900d040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276205386 1250 276204136 276204161
    0x70804080d02070206160609050d020d0f1202090603070c1703150603090a0b01060c1415040312091b030605060103140604390206090a03050a110316150b04 68
    0x501071004140c08075401420300e684003d2030980341c810003c801589208820704152a4195200d84880901c103040c0119030102510b1300c0940114810740402030b02d081c0110010004002c074200800c5040f443c240d04403111100021310980c1c0380e01e400c3c82c00a1a8800350a401c0b240ca07003134115030304c00c20145101901e000f103802100e403d42c0c0b001c000d002d020850b040200139042c94407440b840b22010810090341140688100d9484074207042c09418000303050844410300d0768242c0e02001c16960303006140c0c1d50058005901d450402d050a2201c802e0502800726604041c164103400d000020f000210141d041080780c4c45100c003805030707654540065045400386505819218400c1000404c9450254090600386800350840751701e0f20001c4d611400301b02400e20084420205246180c99440e8040200c0c40e4010311036802402c0e49003d0b50b0340202240a0600c03040144444440000c0c0708000a00c25202960b20351300c0c2c1848118000d050600c803c464105254802030b00d41030260249003064050703503d03245038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276206636 1250 276205386 276205403
    0x7090207030512130c080601060212030103020f0f150309070303030609050907030204020d021216021c1b06021605010b0f1815062709070f0c060e0708030a17070804 72
    0xd4030075920f02c010500404030140001c031030045100080b442001c901c0a099078000400b025810103a000e841e21001c00c40c1e88080d40c2041c00100010f03520602c7c520082c00c019140300b0f006e00b4541012444001c000e03d140d400c130f103002001b04803c041000607800e08582c003a64044c400240c1d0344440c4003c40760152110303181e580200105201504043d0010310f003071002e60100625204907a01c01c030700d901509880d40034041130054154211241d0400114800e006e045224410246050300050f0200d65802202c580902c0c41d99005820b0100301c0c0e06607201c41c0c4c424444050400841d1415030b0003417043e1010a031207505800051840e03424042c070401c101c5e201c2552000816110540d039164440c4041000f96882001000140f45141c1c1402500480b01c08005081106400c03c1080144203000200340c8000c100300c1c49400b003001e039400988100c0c00341c0c100200060106a075080d603030402140c1d400c1400e0f03a2000050b510340c036942c00700030075000c0a0300d000c460250380c8a8440845240d4019540a0140071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276207886 1250 276206636 276206647
    0xa0606020c151312110a08030a0305070302070c150f030b0609010302091f0507061107080706020a110d05120a02040609171f0515040c080114120a0602040602070902070305 75
    0x1492003403021403040b400e10150800d01c0420400d071118056030425900d88032104607403030800c1603050166036200006c0303d00c4070703600c0c0c10080314640d20300401d41d10408040d100d41c046001a03000754101c40c400c5800004050b030690b01e0740f101900710b4000c82100c000040e001e5807074070b6080e031081c0b0850551310001040e040c54040b409004401039000000c0c12a071062001c0d18407019a030310200c500d00701c00c40d15202c96403100500d0800d403044030390340c202800c01b003081003140600003900740045078009503002000507196991824200ea5003020280d2000003840740c4280c00c0d51940e08135011744050320342d850301c1c9a81542c840d601002a07029512807817002c11500e100502141c1d2145007955401c1c02070f00b0464051281c1540c0701c681803410890240b800b00d031740710140101000d2074885420104016501403180be514014001c003404014424002c000111168075074060744d90101b08110320007400126182c2484504246000394401d1281c0e4016224072200060500b1590007507680d025010344810303050a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276209136 1250 276207886 276207889
    0x3020c01020c1e2d0112020304030905090a23090d030608070b0a140d060501111f0506031912170403090b1305030d0206041b141c020a0305010b090a0606020c 69
    0x40510501656004c800880e140c441d0f50034030a882080190780c402079103480511040058080c040c80101c1e40c0510340108104000300760444400c01c00c48400380c600302451790701d00640400078180c0600400c078494503001002c0760380b900c42d03180c00d02031030342c040c00e92f0004d848032041901260141e1180d051903401c001801c200c1e40240d1005840110f0050030700d05038030280401c015059038402210055900d030b40e400305024a5901c540300008125000c0c2c01444400d510041c3e8003803040d082c91840c00b0030340d10360000580f6030300e0134050030340780145a00040b6134429840c40e003403a001901d2484030002403c0140f038501d00e002003407881030096406031590107010303080124443c113503842a0760784895503103102c100242c151020000c5034480300e410f602409560505280000c011004d240e0304040304008410705108084140c10302000035903086403101803c40c0c21506003103800445034806584900514070010500c0010740150110243c01c54403289183e0324040ba05049a499000e1040140e024602c0460306 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276210386 1250 276209136 276209179
    0x60303020c060708090d0c06020733030e030a0905090702030a0804111504150306230402070c0317070303140408220306050a02091e0907050d09020307030602040303020c01020c 77
    0x2054054100f0624282010000c903841031042d46c0300f247c1800c064041008031719030510102002d044c01e801c8503448a4900c11240b030414540b1402c2c14041609203085d04400c134065800760254100b8201601c0c0c5071020340c0c0c2c01411a030003620515024008401c0000c0000d440441100c28403003042e1220b0038903484079200d00a50072503038691035070032994042141c001c40d44080c028000400b1000c80514126a075100e00400342c2e01c06500039600d07442450322803114800c0c024030b0752000d0f200a0700c00584668190401042d80700080d0700280c41c440030030201300c00d1850703200020020a03019442c180003411905545400c601802c80303025104500501071780401d1161441c1000e840e00e00018200702498a944a5000310b030380c1030b40c1c000c001e00e1f40024506024140b0429500812104540004ea40090301c804903100368401020081003010016086c241840b05600030040640c01404503a02c4030b45034a0100000e50244c0400c0d03004d48241c0c540c84117558070001e040b0b44a040d002d0a1031007601d51181d030b210f03503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276211636 1250 276210386 276210397
    0x5060c031302220c08090606040f180302011b050f0d020a020f011a01172a1912140402030705040507020a0f0b0601091508131505130c0801060303020c06 67
    0x200c040d40203600007581e1a0f841540442d524440e240c01e03402d00b9182003000704d501d00380780041444208000c200790520085100c40d071000050b5800305410900a02290080101c98083c0b118030384011300800034194150320030105020072041641d00201e1807030080e1110300551850003086402049405107004080d00584546081030045406150003040c02c00d007500c1440034038001b0704200c98150040e5692040ea02e4128182071ba06003c014200320410303246807194a00129502e07150280103140d000120070840f8242d941206c5851503484100720001c14940000f589555901e0400100c2d94880c0c0b80c2c5440f080c05168010b000f80103261400041c080903043c01020f640075802a0b02022010602c4c030000340d20050700c0f030802c94101d0320f4408005000b120036500030079040501c1126044c050340e04150119001340c41c0d040c0b5105050018035101c0140868284210302c9542480c0034041413200d41d00540c40c0880c4500d2490347d58546849055003242d110344030181c0140d01000c0c8540ca2030410303130002c0c02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276212886 1250 276211636 276211651
    0x120a0c0203060a0b0a170a140a1401050901060515120a0f0f06030204060603090812041118150105092209060603140105131703070c060e01060305010608070305060c03 73
    0x140025000030b81014021101421482d483d58124001845d00e00d03c103a0240c000c2929070383c1d4449080c0101651482103403001480d5101504080340210b034100039060320194860343d056030241d42240100d002c1c03c000c0c0e4021f601e540c200381d804070712131a01e01c403900071282e45d5202c2c0c5414151300031800180346602030003812030a80c3e540b2400804036158020345400a4441102042c00c518501c144812524194400410940b42107034440002d014101101c156030840780b0042c00035203850030603160404800e1a00c540c002220a9500100d41c07000310764500c02c0102c2218120a04075400c01074441d8410f410100e50700144035203219104440c0d04101c1b14260952080000e0400c0c09035484104407403440e003040d511320149048096800c4401d004255000b01003104c05200718100781d43d07021986000360800145d00c4008800181c03518400c001c9203200b00d403c2030f004d000300d074103640246000704180d0105039440e50a103100803034030380300004800d0b040701e90160003010940c1d1198504001600080e00c800d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276214136 1250 276212886 276212897
    0xe06060603160e0621090622031202120405011802010504061d0409110a1d04030c080903060f01140405010b030705091206092404020102070e0c0c24010602030309120a 73
    0x280190b02c8010151800c001e0751100c24602c43e80017200068160401001c0640c41d50012081100f2000440c2c666000131a4041200d0714502180c502940c014080f0390403003000600c041010038015409030400c90189014000803c69400340c0c0d001e240100c90301141c083d000c104204401c2001b1032003201e0031913204803805800748801400b500040d0a40e100c000059030342036124000244e480c9402e4410328000c1c090760b940e802ca4044140d403010304250004001505000e109060401400f02e02ca044071500c08008060702d0b11803402c8180e00c4481b88081c00780400d5603015844494190400c0d1080d641a904d1510b400c03400c540d1101e1080307401d507028440303079a0000603415003003000c04800c014150003039103d1400303050803110300c24041d1400d200311602c4c44102d00340c5105000260340c0101e01101a2010317001c1030302ca40d5a401503080e089100e0f801940d5020300c508036403003003014064040b5100a6100ca101c0350502d90f625181240d8900095640c0c0e0050f800c0103100a60f01000a802401c1c21181e80c20302 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276215386 1250 276214136 276214157
    0x7170901080f070e06120a05070f0c0f030c2102100218040506031207050312071706090a060807030804081b030d0819020406080604110406020705010323010602030c010e0606060316 79
    0x22910350f8206c003a030b0800080c0c42c402800036140080c0913943c1d00480900c0c2103030400c005104000c00394010008040c06880512000c801814802e810741da00f0103821100607803400507005802ca09048440d00108014080c059801031000d056008075440398000c86180e240c901d25000800004020150441341c0c18440c5214004a046900b0007500001d8011005140c480c800c0c11204018024010a0b4004010b41a18447e01c0c080040a200b07401800664200d035195070b40c240c1c428010403603500050110f2040c0c800000400a1300c4002f07000b030707031010015101d44c41113000e003140510228100e4250f050300310300150307032140744200d03078080d070001d480d0744040c11865082140d031040f0392194100100294088042241d00e040c01c5c061000704050303e042403440c3c04c0c94180000d40350b510b1401202c1c10140ca420400e80c036003414103600050201030f002100038a5a440340040e54036440502d00204039428100081804107020500038805d20019141350324540c2c410100d1407000404132141414001201c0300b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276216636 1250 276215386 276215389
    0x2101060305010c0f0e010c0215030a110c0309041409030301060f0216060305270c060d0f0203100302091609030807060e060708011707051e010c080307030207170901080f070e 76
    0x703c0c554100141c6030380480900214005000c00e02c41205281400341042c030120068480c14180d00300948140d0401c0d440ba02c500300300034041c105410091014035800b1481a02402c0c0c080010154200700700d80400010045980402079140c0856400340981c0080c401000000d0160040700f6207500c1ca48191480310109a086003107040207600076a000a40d00c1d010801c80151011030050720290b80307014200e003031040600c5642e5800310108100c0c014900811b6000951401da00403000d06501da0381c056403a807426407400008108248020303842840000049000703107034042c910741c0003c01280e03142943c05086459290003548940ca0499030582d41e0080810650381c01e0120703030b0050505580e00c00307007545000c2c00d6400c49907101259030400e0f007010504100c15a240b114075606011042c5520651030f20f950016a0701c50749036100580307000790000800c491680c0c19030042048a218808280701913401c040105024042c4001c01c0b4045506240480c0701040804c004580c410030524010410070020f40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276217886 1250 276216636 276216641
    0x50712060306020405010f02010e070510020703050a1515030804030b0402010c060e0607120e1e0109081305190501020c01031e09050102070b07080415090615260309210106030501 78
    0x70301c29608240d0104041c0200d6a100c403000c00301c52200d200034000e42c450a50b90b0341d110091032040c41e00c20303440070904c0300f41e5900038000d82004541040c00e8912402c1103040542018110002c0005070301d24014011280d80103600412040e40d41022115050504598902c04048406042681400000a4031a001030400c3c014494581c04110240c820350170040c1c405050b4442e2040340b41c0b0580e041c0645003e113581c0c0020802c9880700d0784007210600c00300c142442401000d10460140c004000025810040503a1a03d0107086420641752a00341c02020007c46403596024058107006070001c0340c50b80c010390b10030740181c18112404440c0004400c00c4015000031100d4411044550740d401040040c14403240400550f4400072508000070180b500703036514a180c40f0000c0711029503590781c50380c0c0d03000c3c420103a00202c07101310754911070142140c50303103444d22090b0030104101500c06030308541c81717941e018040182d0707454a00c06003a003005d411000c50b41545c0241112085000d41d96603400c0000411002d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276219136 1250 276217886 276217889
    0x7030519021c060f1a030a110c1606050703090e1009060f18090f030c0807020a14190510031e0507030e0601210204050601030905060405100f0e07030605071206 70
    0x84a10326100c00b00101040305840140d441803000c0e02d00904204451031000300b0a028215004212959903a0f80d011158011b10300317851380615011020030380d01030380f0741e0000f0215012901200b00e40340e8656070782e00490352807041d0b800050014003905030420842c1e12000055401502002c40350355556114190041102d1150f88a1000304507014000c2103000c101c00e20541c81560004018480552940c49440446800340c0c0d0040c01c00440d031880209000c050400d03a61341950003020340345c20640d10001210300b40d4124010300c1c030812201c818001c0780c01801c020201106c4020300300350b180b0400c64000390002e00142e01e41110080030905602d0f0259030701d100c0c15100300c1540c0c6000804447c6044c11504d001c105030003840c0441ca80010051440221480103000765030304840104e002c2e6500001200603080b507500040142c862203061208108003c201030740742d0030801c50304008554001010400741c441c01007458413150080d071001c1c00443c0440d040b240d4401900c0c241120b091104205c41802c035100c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276220386 1250 276219136 276219157
    0xa0c02033a1a0117040f080d1e0b0909070605090103020f0c011d030c03030a050408250b072607020c0a06030e0106090605062208030730080703051902 66
    0x44000a080ba0040480003142841082ca8141c441e0061003c0520034088098409000b494442c03104034200400f007421600710035083c8005001440c064450160320401c40c001c094015070500041c2103250500e1300702107100704102c3d0300901403585007400a481640c003c401d1603041580030010703c0c03c0581c40d00000c0c400c103c00c0600014203010f481440c200c0d4100000c004891a8004000783c54034440b0000589070081044900010203032118a8001f0052088503a01e040744450810010340490380001d0b03100e13805000c0c10001c8180da44640d4200c3c0c00e001c01c10108848590442100da00c91031800d40b80c56407141c4640100c03020090701740300103a8403008544c030100000e0789907544180310f64828000c0703400610842d070040c40054203040003e620740c0903001e5650b890b0b40c4841c0d04407103640d99429271007008140f202c0503640c0d0750701e19091101c1e008220b007842d41010750121032840351600c400021411040525913480c03034030b45c88908044003d040c02a058000b450401c05800050b14203510013005060b54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276221636 1250 276220386 276220391
    0x6080606030606091614070204050106020c01091a0703180e0c130b030105010819200405040615080c07030905030304060f080906090318060d0e06010e0a0c02033a 71
    0x34010101454004014086409992104103006030b01c8045000030001c4600c5040c000400d03802410307120702c0c0e4024050043e6000d402d1a000281c3d031500402c150702d4070b00003aa1101c2c1780a031120410322601422071003504070b4503010883c140209105010303120341d03190303862000c1e210503659482c806000c4200740c075801260400050219040c50403810300000038030410220506541c54540040c0405800410b2040b4460b880d20800d03040e480e565010390750f01b1865031031200201d900f00b4a5050f03076800501555014030328040020646081101541411016503650484a83cbc1c480075003540740d0f08002c408506000b05c0c0c2102040325901400900040c080589d52000403410842c001407440c0001781100e241600082c0504c0710f0307000f0100c100e880e400d5a41480d0540710350b400010a03183d100782d03501400003e10f09201140034950129019048455800100680f0746540300381e03070308440b1500b40703034809603004100a10a01c25440d031008400301d0400310120000f5503010b65804022401d0400c03264855 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276222886 1250 276221636 276221641
    0x40b0604140118061b060905060f09010e07030c090905100f0c080105100903030f020f010501030f0203010c021b04050c0403060c0c02040501152307080c16060c0812060f04060806 78
    0x503480f404210601ea0424048400146011009400001000d030241140303076000c0108000d1001c4ea41107081c10301c1d80202100c4003427a1811446400300d40a88881102c1c2d400c0c181710007a103e00004038007080d2030300105aa080c50b4035040101c4000d0031108421201c9002b03c2d040d01003144c485225800c442d40a540003c181402001070080c08250140c1019210743c000310040407400794054000e1060325454140700c99000d4807100103030300e0b01400f031140c2503056081000100c00c01200030b00101c04940b0a030002d2049101d079190690301c50b050304950b05102c81510400c84030614043d0030407600141990201b82c90b00c1c2e03c0f901c6840940381585804008109008a02c0b0110b003810b00c540d40c01000c40070444c0801c403982800c000d00e0800071180360740962038000c049901641d45182107a1440ea40b20701100da603201c41c0c1c42c00944036090711401208921b455080052414005d09411090325800b040d0b592403ca14210f40c1c0710743c20406091581c00010009652220743c58a2007040080c124441c010420391 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276224136 1250 276222886 276222889
    0x2120a1106190f020c03070609030614010501080426071a0106090b070204091a040f0c050103051b0a020c19080c06091008041509150510140609040b060414 68
    0x280328420003401803000304071150300c40808499040d0a440589001240400c0b454001c80c9005030b003c0030950315000c0c401c0e0001e03000d40c002100d00110b034401c800c18000300c00302d11008031031128240304042c00701e151a80001d00081d0320344030000216810464008210a00941c40c0c01c298012610458900d1101c8000041009040007058010441343c41c00d04449030800803001103502614030003d01440d01d520604080020807000c540d0403406e0a1509201c0d843e06041006201054940070f5606a0305c000c2e0109455211b401098070900003080589a006108d290517011684026500d000b10b00400e0403c1e0000d6444074003101490301280303c800505070805401070700340140544214070984082242c9001c3c1c0d05c48081c42e82001d540e83c1010310303c4c0d0707885081c03601250f884c88500c0150a40b506440c0410402c21200303a04450344201c20070017041d6282c10389040c00c0c00e8140110701d5000054410142249031400c020881d0840180001c2200004e40b4080364442d00309c0d800003641c0003260078420002c0d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276225386 1250 276224136 276224153
    0xe0607031a0306190f02040515091003060303020a03110c03010905100c0503040f02210303040302061017071809080d0c180b030f0c090603090a02100207061b020d02120a 74
    0x1e41c1e07802c801400b003a0420a455640e18a504210189010748a0051954010136035040c1c5008080181000c00c404d10340d80c071040560b5114404052042c107013500c0b54030b070551003481401d080d40c3c9d040e0001c0020001944090f50801842c0140103024401e00401170b426032401e009840416100710003c244034546002c44a040d03440005041c01001414000c110105110ba082c119801d501682d06a03540101800783c00c541d10040703039518256100c00400c0c4010150300040046c81900d154600c4801c0c0c80e1207410301c041c40200540061020f50102c60244040e0500d1301c0d0600164504010000da18040d50352040c000750881d25014107642d030307144030920030070307070480100e01001c0c00b0300c0d400c00321050603d1340e000c90314000a4000c4011400303c2000a480710244400c841c4203840007082c8980700d14148520300d50758000c80004074001d280380d0308410819800000d03220b06840d601c0c0c441107811f00d000c0000103104410b140090703074003c120308450f802682b603c001c42181c2c4111100601009002401d180f0714 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276226636 1250 276225386 276225431
    0xa0c050109090e030403120207050607080717040323010e0d0206090601150c2a330203310b0c010b0d03090501180905160305130b0106050d0e060703 65
    0xc2c45090140c0342c40e0500d8084215000c1c2d076403003440142d40f1190030300700700d1030500c064210641100c1c0005200341030190484c017404c500e030322484042c848910a144102424060740c403000300b0b40036106d0078041156110181400e0754804140c0001008007070001500d140042c140741d4040903801c15018821019428401903001d4041072010002d80d9503008401817052076002c1015100410803400d581e0190b0311007100d60751501c1141e401c0000300344ca50103050355000108401081c4c0900001d6640d00d0244041007010042100e13401641c2800b0500b0a181041641c1d0507140e0f902d481a00b1007030007802c05902ca480050520f642c034244d1a1411440382c182141d072009181071040c040417140f94000b03903009441d17109407102883c0007005c0c600c240c8407040e010582a004070303338641d051108100c0000b022a9100c030704151240d030309002a403034a00960210004010000c0c0050b80d030b20006100141c0903c0051529503080e6000280641d003050002c2d003001700076111180007a490300210310380f10762510075011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276227886 1250 276226636 276226649
    0x20c03060402060307050c0316060204090b09040b060607052404050d0e03030414040f0c050a09090603020901060c050a0819090605030906010e1b04030521070b0a090807050a0c050109 80
    0x190301e040039000100b032400010501820050005020030740c0d607400744180d0b11115000c101e280c010301ca01e842e00f500650028024110311a02d8a0012112460305054540c080ca070003000d040c1710f41e158035061160a034002c05056070a48103c5903280d03880c20050348801e804048804e4024902e00300341c9811400c2600c00300c000410444041217043c0c0c0c0766000320031901110400340420340004522008900a0a503c070300101c03e65180c8001c001d20705030084014140c180b01940d0301070070541c0fa10a650116000f502019410002d94401800030070b000352041072049000c5c0c0c0844841581c6070391980c01e2540a50800d002c0341c900c1916001d4842d800620010241c506824400d09610344140002d40d10641403140025001c448004200e080e91000381c54a19003640d04402a5100e0712420301aa0b0340b0301038607003040080c81688200c220780481c4001d43d941e8aa002c854002242c030740c100040080c0c402003030140d070704150400039130300007480130000c4607405482442c4901c8814601700014010300302c141e0100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276229136 1250 276227886 276227893
    0x111b0105010611031801260708101802030c160807020411030603060f07090f06020c1c0b040305070c0b0309010f0c05030714030c1308030301080c010f0e01050c0a02041803020c03 78
    0x10b1032804004401e50343c981c1c0f82203155080e005c185500495500c685c1c4c000c00452040c00404034162400803115a41c031400b00794480d200d1544580121403403031b4120b4880d40005d40021030580a00b14620b400440c0c01c4150005000d04003820301542c2c500c03a000580e01198881c60026003481181441d02643c01c03a01754488101341185041e6003c40d84507180240031132100003841d00002e00b698082c00f443c0c0c0c081d245002c42c82c0c00380740d00c0d00c602941d1082c0c1ca0858070720030744040110380f00d56074144e40d00c140d80c0b503405030822445859a0760180c8103904813035012592101c0151011801c503621720007651240080b40c0020400341c040359940c500329480301c000300b400c02108000b04280d02c0e030020026100d105d0f04403207c03952581d441004260500a0124005594900e14000502c0020000c0518181c40128023541c506003810001502d8200c05c43d11080c000c150900210942907000714040c0c00001c0c018816541240d00b01e0b800034048800c015041c07640c1811065680b820f00d64100909038000d88294000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276230386 1250 276229136 276229157
    0x150909180f06091403031509010510020706080a06080114270c011409060d0902030f0106140d081612030608160b070804080601031211011b030f111b01050106 69
    0xd40c03040714580301000c0c202c29201e0303e00d0020428030290710000700c0800c5080da44c480c14031103c022007071244035a0480c45695410300120326450021805070182d04650010b110440c588107042d50605001000f10003850780c0c5500001e4103a50a00900d98101d487e50074540c202d2411170407004103c8880348071100d00c1c01070075041c1140c1800000300c901200d002401c000705103422500c4d91101030f1090780c8000b0707009000400c1d80039050034a5040304040c070b0310031800d64801404901d1220b08840e00c40c440e910ba410000070060302c55080159403041e41c14010002c1d14070b0b0442188010800da1081001201e06540340d4495019181d072601c135400180a01c1c002030100840c04101e4240c1804040c0a854044c20700011443d0420191904070740c01480e1810550b420f969607810542122907a02c003ea50100b09200084142c0c11010302c10200c1543e444074900e000d1801c540000c400400c19480040e8006039124003840900380640b002e00b9041440c2080e42c01400001c0400a082d900182d00403001e201c01c1031070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276231636 1250 276230386 276230393
    0xd0f051e1b041802120717120d0b210705040b0f0603010306020d140702060403021002070f0f0203070914060a060206010e0f10050915040b010e03070306050405030415090918 76
    0x2011160040100c40c086002d45001da00e0708420360a40e40c00a612084401c03050484000c04983c0d00c0c1116040e1010440e044038150065232100100708400c50014010040c440850000750b0041c0c0c0500d00c054400d903c052101d8600d6522890264030000f00350b8400365007040689824001d1b900328440945000e40f060050402003003480c00107020051255401144284100055510000b100c0703040c00c0056249081c200d42c042d440d0682a50240d00500440c100e03682401090b0003280c80007680100006032099468403040420203240300d04036814000c0344000200e5000c030740a038240003c0c001211090905282d001c1141d078160303e80c04541550031550040191314078002103564001038118488013540c0e01d820f0403000b03120490b00000d42c80702402007403044400350610751622510f01500c0c108112002000159401e00040800030761560140300180002030ba80d070492900076120307204403400c0c56190011703000c88580f11248a00000c8854100700050f03805801201203841a81159107000a541e45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276232886 1250 276231636 276231673
    0xb060102120403060e010209150705060601090506090108090a0c06021b090108120c0c0405010603061415030105120705210d0f09060522090f0c050909150d0f051e 71
    0x220240c0703036507918200014849002c1d01100d0723001000801a04098000c0007101d0901d40029800780c9141c86600002107165018a5100c01610001400c0504006102004490a80009180e120140a01d2103401c00007400b82242801030585a00a4840482c000d41d004005600a001c843d200d00e004100400c070307050380451044088000109a41d43c0c401c2d00030314551800c040c00713146981043c0f82200004031140d0580c0100300741c40f404404d46040d241c02204104046400520000501601f0001040240740080d401061201100c00740d800e80341d43d0b0383c0081c424100b042e00c1030822043c0c0e9900c55074407082c188400078240302c49003015a00e4a5143c0001011000c42d8014102840800106410a11000c2c0c4030001c3e10103e00134016034040d04d81a901025082d40214520420304000c0e20f8850756000300c003550003001740913004e01a41c0d40c45007132180009445010846d005004d003003500011900360800c2c070700c2040c0110000c241140d5012000d00004549207210030054000c0c61456101407940c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276234136 1250 276232886 276232889
    0x11030406090212060a06090c02030c100203130503070c1721360a0f0509040b0a140a021c05070507060905030f1308070b03040309150e0414040b0601021204 68
    0x250300012046042c0c80841c0385105540700504091080d1001c211168215800107001d96031820403d22100c0c0601d1020f990301e000b02c0144606a0300100c080460b100c56503405140d200e021b06190034101e502070b4a80c0e41c02c41d44a814142c0d08100d0001041c0480b40e81c123044c040ba12000c020007003802c0500300280980311550040380408202d070002d28010000031030511200c03602c0548174410031703003181d03c018030b02d0310703901d03824a00d0060340d00b000001020804075650304112000600b058115582e80da55550130000c00400d2481469a40c000342e1000d06e0b8001c1910744900b18403e00182d645a800d02d400e10300100d14460240018181000c11a009034018165030460743e008901040300c0f00540b13441030541c05070080c010000c40b004600202603441010400d81200c21140650b6941521a150400540310440300030700400c43d00881005040141c2c10182803400c400d10304030240d1000c5600080559880703141c1c041e004d030350000a010502032952690342e04500c090004002040c0e4047c4103100701d002d40e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276235386 1250 276234136 276234143
    0x70212041203391101112e0c0806031e03040603020d020712020d0305101805040c08011b11010203310b130b070305040b18070302100302070308010e010f03021018080f10110304 77
    0x5007640ca047c00010784205140031070340188280700300100003000070305059040b58854400c0c810402520742c0d1804150b54080c0c2c907440c0002a44c60030b0b0030007c0544c044d61140001030669030f030800140c00400d8110840780c40714411035010b0102c1d5149848000e0a0b038001a02021400400d40b1040280703022a03080f001e800400c1c010040b801c0e549a00f0000d0301c184265115013115404c040c55040b0758409034000540921031600c5003100900000010303804c07070000329418048000550481d521210880031071034241e024100100d0044205079035504501001500c0b40402c43d40c04544480c01c000c1032000e0306034001401e140c10070691810341c542d24500f0f8000750613091000211048940c02d04800c1c013000c8055900600148945000f070403000700298496682034000460f1040003241c00214040d205d4100ca82002504800318116000c0190b82d002c00800c490606c4a8150705009181c00c0a412200401200007d0708424600d40101424200502c03541c0b4075192910651080d03000181e002d81c0d400980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276236636 1250 276235386 276235423
    0x110306151201080601180603021008060a1d04060b0607110f06040317030609090a030e010807270e150a0902070201091a0307021204120339110111 64
    0x101410000840d10910301d0020350814034000104842c480000d4090417100010300d40000502461780c200200c3d401400002d5015a0040100780b140348980500e0760080302c005c00f1400c0d059642d881d00c020031454002e240101d40316110030002800304501c95011824800d40d5403c5c81c00e0b22a03998034a0502c880d4030024490307814018040c000b62554019a400f03103074800244185501040e8038020345170012a03902c0d10841c103403800108a4000811240040d591541366085c1c4104044019601104010050700400c880e00c100d64007020342c3d110205420501000f50548841d007003080d841107240c2c001301a1200c0c516031409542c160303160704888070704640074240016113400780c6100480b0410015485208808201c500c13600109100000650082610b6000ca441724030040c1034111040c09a80318003d80311500e003907100e01190190154100c246002c2800c0318914800307400e5003c4421000c0c1100b0000c9030000100020045484940c1c9081c00302420715444610340c10341d201e552000581c0d46100481c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276237886 1250 276236636 276236659
    0x6021006081e0f07120b0115022a1e040608160317090d081201051005070602090307081608010e03090a180906060e04020f040b0105090118150504080709110306 70
    0x140d042c4000e00040c00801e0541306000c0d0303195020545500308581c1039840030b241e6000083c0d13440944a46100c0b4090341c0e000b1305200e98109190f904100381030322000410441c01000c41560b5990301c1c4d41c20b404110141d0000d80400d8008090204841e002d4004080e1548110044000f101c40c803c0c2c407804030395004e03110122001c01d46110410501640ca222900200040c44020400a801000c0c1002800442c0c885203d6a070320801c0000340c01003560551f0124400300511401710b00c3e1030b0000c2c5144400a4125001c255481031400d181184035403a0750707900e4428003000d03c1101020700a211140f80c00900031070900d4039600014040b4040c40c4200702d010039850003d030b0307465001c98204d01002c0780c014400300446641c40f401c1080c001404c0368128420038085082e40c00e207140c42d104041550307406a651900b01501c20b801940c205565a04049d0250440c450000d40041c0c2c031101c030548074480c0e5580030745039850000c0a03403408940e5008183d40c103080000768600510007405480e0f110008444888481 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276239136 1250 276237886 276237943
    0x3070c241b021305070206091b0603010308070f0f0302030d0c020105040c06080405070e0408090a052d1210020702040e060108034006020607110304090b15030a060602100608 76
    0x103100d540340f11603d660400c01044001034011030f08512130224401580c065503000203e4180d481100c2803640c0d4001402e00c014000711302d403880135204c10f0344907130303104c8058003071540380c01003075102022040f07005034400100b54400603040e00807440400c0b0f00740024451820541d5a116080082d40104030803c4103c40000c3c05102003042800000c000b120401c29981c2028100344c221640050b8809004220150000540c2c0c00c0150700d00f10026401c021b042c591300c00e641c101d80e980000702e2515540c450b40e200d840e1400c0d0303141803082004100c1c0340000103a440d0701d50b205000c10342c0e620304640380303494000da001044000000700c00c035002207400d100141c2e28406a0148840346042041020501c100b020004400b0309402803c1c0c02c0a542e0b16800700e030b62a50750b500b0121222008520184074942007440200100b0426030042040f0040090003840c801c404c40c00440b030b070382d0400c0b6100017400362540404c00c05e0540501c0444500381d0580003d202c0c03030b4148981c40d80d5a80310024002046a02e210103020072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276240386 1250 276239136 276239149
    0xa0507090f0b0703021203070806010e0a09290102030c0a032604060c0809030c0c1504030b0c071a07090312140c0102090f0a060804020616020303070c241b02 69
    0x900044603400061945035450380b1840d42110404801512828070035014054003501503a120703000b95910100710350350741c000441c0c2c0068401c10041d007102105c540400c001000e4080c4a5811018046000c6a44090b100112880014403a4141550010003120610020114003244002d4050070038003d90a001e8201114a001c0e24100000102c103400601007003203226040154490b032103542d00402501c0d40340e40c007610ba102e660309001850b07101c8041660541801120034080b02c1c2a01540c2d81410b03a00d480b40c60f0041c4040320101501400015000b0401c190348070355950f0b100311114410010b02e44030300064640ca03158000546800708840500c010a403144600c020994080d410303060f1243c01c000c2100e4007030340209980602c0794103030064403005820034200700d000b2a809952040003645940e001c7c0407043e4000b01c400c40081c00400d2007407001d601e0400c010030a642c441c041c01501203140c00c51254802d200405c070340d05072500c880220380136070754482d0701c0000008a07060036013080d841d1480020300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276241636 1250 276240386 276240389
    0x60608060d050705041803020f061006110f010f020403020a060806010c110325061d1e120a03080708060d050c09181e0705061c021b1606030f0c080a050709 68
    0x85c024140303030581d034150b81d66404c4041c00034030940031601c00340a840c65454603039000301c8001c061850381c00d400700012445140200345452004080d5100c040541c0f02180c20741d030324800300090130b40c1c001a04204500308800500001d00303061500c4c00503401e1050000f0404e01c4d002c000985482c520719401d09240d501448881c1c003150703101540b0121241d1441da40030a0012502c030780b001240c80404004200b200b010411004040020000d003091403149101480c1c10800c000b00940240b4907a441c040039402c204001e1280c24060740b5041000d2810110040c90420002c083d140141411103030000000c00000e40300881d8201241c088526175112691025000c2c041c5160b10000e20445c1c086580200c0350000c4100c0c41c0c0f00c0c03901500d50b0130f911030080c000319100e526000c4104494461050170042015405003040f0070040210300d181c1c17040c0c0703016249400a407010f030901120f40610f04005094243c0b1400006a040c01002d00c1200c0401502405040c001050b8030b88813a11240000c859130300c10300c039800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276242886 1250 276241636 276241639
    0x3010b0a0306050621091b0d03090302090a090c0611031204080f0d020304061b0203030a1e060b0a021b060f07020a080601030807030305150d080901020703050105010801020c10060608060d050705 85
    0x2a280c00300300349035038510380f450785101d5111760600c000f2807564400030803420b2800d003061500071050903640c030030b0149101c800b0703909808100b01d202c0c0100c01a0ba5241da2240980103520000c40d5542c01410290302d21683c030792210303041c01030945411541e0032020060310500011446c0307442140c0e40303030309000c1c00720300c1003000305440030f4030000b101c12400615501441c0554000c6034200500a0394540d031000c0d0007140710022000d41d209100194241049801c071480020503c000c80c66251031020108040e11040e4001c0c2802c09000300d0400c040560400981c0d520540c03600819140c0e01e001000300c1d84601c140882a13140510002c0c000080d034880d0b03001da000a003c8001118100e680d03900b80850aa0003428088000905000c00714846c098500100f2810341340040c86418003562aa890f032205a20410015066010312580080450001e00c20140201130742c40c0003580d200d1009140d0750800440c90701e1030345480c0c03034601d081c001c05501c0030050358044015103039031684298078100b5030324000d03141d803145 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276244136 1250 276242886 276242899
    0x717070203070611040617090307022706033c0d030e1b10110a0c081b03010608030901030c020a0b07020325170f0c07030b010806011a03010b0a030605 66
    0x1250480d4004001c02d003042c00741d08100402421605840c08a2042e0710690000a140491492501880078006500a04554101c034504141d590115503030281412403200940c11035403403500304001600005078448000c8020388003000318240c1040b802d59000c40e01959610200e0794070064000e01d03115600199441900312946c08190f510000d01804407020f814010380507901e1001d014090031000b0350100c14000b000441c0010001c0c1c1d0841d003018100710203909512564070ba0a0115902c4090388002c1c04400c400b4200c844103400c1c0d002c841c0040140703054040d0b80b404404016261011054a0b2203990901c0d01241860001c10100d14040c0070010140080c1c51480c00e01c9266a0000000d00043d007440d0001241200f9440300c0c0d4407000075049014003031000401d5a100d03121a003c1c000c044186484a240d404d0102c0c1008e1245802001d4204442c400925401485060f0b42040018010903c03109102801c0d0b2400d80140f0446c0411b11a0036030103400401c0c20421180260407010140002034501d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276245386 1250 276244136 276244141
    0x30516081306140a0e090c12100f05060903070521101e060806040b100f080c0909030304020a030f0201020102070b0a02031006111504020402090603010b1b0a0b07080717 74
    0x8455007040300e48102c0011075504000c1c00040011401500d035414040e44407407403403840a00500864250003028440a40d00c100000303d4400903105516019543c0709558145082c1002d100c24245080303a02314a00c039940c20b10000f107142d60b0000d10350302503400a49030144581002c180400000d00d14420610481c0150285e01300300c084180d201c0d1001d101105540400542d2a8080030121075050103522102c0d008000040c01045403007904907040308441000c0c43d40d840d074a0390114000c07043ca4005980f581c22880c000c3c0c031103141074012980c00c0482400a5855818030f640042c58815180c44002c1c58842d5496212095a00031760540d8010b0f9000380d00741085181c10100b5900031b520464203034090919428022880d0b034032489484d91440c40d00401040c054001042414026130024412a0f00c140c00b085424419101d600285000b021501d05103600c61742030085004850010f0300700b1541562100b4480780214804682141c0c01114070308158090f0b460f00c800071110102c5005000700f01900b610103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276246636 1250 276245386 276245407
    0x504052d0105090411190f050117010503030a3c02190503090402090a09090501090c0801020307021207050a020a181d0c01112a12011803051608 63
    0x146042108021105208084034000e840380005000b8064070b43c0081e2000000340014030200044130350703000b00901141da4001c90708003940c89102d140d0055004440d0b400e104006a580200c5031a03c2803aa85094001c0d540c14600442d1340d901584a0303a60030400140c0e030404060365041c110840e21035040b081c110500f419260510004511004031030018443c20307118942040303484c548591034070340c0075020b185011151401c0101a4114441c0d240d40715280b000002443c4020b445104c41c614411400441c9440c0141004007004040b80e001200301d9004000704451264041030b043c43d0084c8000c445601c580752800c203103241c540c0d541d03030094210699400c085248200ea00000f0702600c0700d11020300c070800f49c6c80042d518140e00b01090b0511a4825040225a5030158100d0b80305441c8100c103c0d00180b905000b0a550200c03070b04203601d5901036000c080d6145003003d070303440071401014a00900c01c1196105103d0074002d90030002500b003003404074014205c1c01c43d02c0000c1c0d080a811446064441e0101c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276247886 1250 276246636 276246661
    0xe0111070b061314010e0609090d081504090c080610031101050703120207030905040c0306060207050d0f051203041707030e04050c0d09030509030c0411041502100e0d020601140f0402070804050405 86
    0x1d039440d0640b82000051f8149842d207290781c4103001640c0600403050740c1900c10307a0030610103080109001d00892a064803515103110322840c09008442c110901854018440e00b0300801600c11007802d20900d0040c4040341a0b001e82c55801c540a20b0281e40d5032105003400c4901e424401c100c006154000a0007405250303009030b004c420b0300e07012642000144404070082c1e0480301148140781c09a000050200001d1074115654041203009000242c2403001540d201400c110015481003260040071080c082805404088070320402c01c04c0c80000d01d80402034402410884020040e0703441140c81e0030000d2100240f01d81541c2e0161a2004184071000e42e910700a09503030425110940244036280c1000e00524282c0200e090000b40c1100c0c880c642400d00403080ad07000244140b44e0254800c1c900c81118001441c45040d001d542580b0290a00c030008440c003d08045060b40642c2c005264143c3e883c0407950307508100d0500a004480060391540c0c0303841c2c201b4207400740750301c1942e1240c60101040071030038881 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276249136 1250 276247886 276247889
    0x3080d0b01080a020921100c0c03080903031e07030605060f0403110402040b0a0c05150c070209090705090a020d0b0d141c020c0907170a020d0e0111070b06131401 71
    0x240c0707030182c069860b24044001c84c041c4950503a801000304c103809407503981c101803c41c030708203002041d1603c4419034452001910304480c0000f000440049181c000d2644c803014140c1c100040c0710103145142480202d404c141400d405400c2600e810660206001030701036031040000b0329024050b40d40340c00002400c1900d5800620041d54a15184009241c451900b80f00b12803d60300d4040c14a030400c40e520310b0484074002c0c15034003140c0b42c0c8641080c2d03200405060708042c0c464200d010315103603140d030640305100c0503c0001d004003520341e000150502955541d45a40e5501242501005032241c4403c141c103000b602d1104451030300203d030303840d041c41404000e0020f40d110300ca060085481011203220300403203051a130000302c030043e0494113140165140c210844c0d034003ea4289050b500c0b503296075810184241058620152503540004c8480861521303003d21030007078842e038000708224403200300210410b21440d08e0044c0220b52100004409540c1c1c40c001c1ca15900d0300200070041c02d405811110b0a5208c213 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276250386 1250 276249136 276249139
    0x1209060e0d12050f0c0106090603062901080a0207150203180d02070b03040c0b0d0c0201060f06050f030406020c0708010f0f0b0609040e122a07030b0c1303080d0b 71
    0x1200200d14282080081142030560003199400d92248280085500d50412100710040400400c013600190394240666000340c81203a40014140e882c5207880c01c02c503203c0740000314418003401c11089801440c90540c0104040c00c2c24443c0042d03440d54203010003841001c2009100b00c00704020b4000b07001007a4060340c41845081c1c000d200304099100b0032a9218104140d50f401a0b01c0028188032401864000d50317001482103a21480d40780c5c40e0b900d0110640c2020048003001d0340d58842c800017040e03090042800418091001e860098103100c4003e19911440c0b6a1642c041e00001c040b4040040650444614441001c01d03548616212203101c0d01030304d201c4088042450600c2d1103041c0303d017000d101e901c041c210024200b52401440405000c00b42080d00b40203400e5000e1251151043c40407000200017507076006500140e4440b16025201c40d400180d98410203c0d030182c1070510016030b075246205d40003144d90000a442e07180c5d56030b0014104801d034100134800f140214241d08800a0703600b0581040c00d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276251636 1250 276250386 276250397
    0x6030b070503040804090e100f150b03190203041406190f0501060806010e132c07030809120f0a08031503060601020d03020903010621050d0c0b01090506010c120906 72
    0x100c15100700d0300790100b590040c00801d4100f01c10840f0801c1d90b0310960006030b030101540c50580368504401e084820303402002044944a5070400518440801c0d02c2d009481440015030545c104011816543e05004184042890780000440d040c092036504180d05422740300700311421468200008000316028405c001c1001d400c0103940d800005850081c64183d60155440f03c9166a0310401142c451442c202800d820500d00c100c3c0050000c42070141301c080c500c179801c407045d91405d02441d5910280c0300002003030103078200c04414800544c00100b2251000001c4501c0501c400d0280c10040c2040302c0314103c01d0252003130031126820488401c0c0038500c80d9440700c0586214000e864141038498500702c80080c010707000a4048041c80d030095015189840e0080d00025203681c41c1e21a40f0549120344a0508000c80020030342d00400208100c0071005040320316080790801c8266583c1c84529074180180a411500d640c001841c6910441780d49420396000090131400281c042da0152254550740903040c001072 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276252886 1250 276251636 276251641
    0x3030203070201120c020d12020705060c190e030d030207080c0601080d0305010909051e010b120a120504120206030604020904050411090c04060507080912030703110c01030905060601030b030f0a030306030b 90
    0x101c044c41010074454050b00500140100171504440b41c03d0091230981c0819420301c0180d001c00d50400c4141c0c420701802d80440c3d51024000078030a283c01c0b004c103841c010800e0007030040d0700d82c0e00c001c07580c10b0039005a0305000d61114400d19004040740254442c040c69446100300000d9001000a04a00100403a8034100801e0b40c175162488140c8000c400054011361102402484542c224009c0c503904903004030000840e0815240040c048800c000394400e4540c4c00031028809000c0b48580d441c0040416040123868a0301e01540100d4021340d02d80040e1103420040002400741e210794049507244d001c000c00c01c000501d4030b45010710840860030301890040d030b07100000840f041303d500304440a5950744c0e2626410021340c1e50398188180d00003041c1d2a08289503003185001c121080005c2c05140748241c503040c400a028155503403424024141e8141054180010080450004a402d0f03420100a28001c03440000e942d010914000c0400a000410701c5805551014180d06502c0724003038a105441202d40e64 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276254136 1250 276252886 276252917
    0x19051c090e222a0e060a14011d0102030f0403150c2303250f1205100b0901140412030e0906010203040509041502030a0b030c04110a030c030f0603030203070201 70
    0x5074000049030440c050000c41010214049030031841100c01001145050303404000111038111101d07a204c241194181d4092003228606955030740040d2529452512014800400003081032500c800b03090094222407100d00881c2e4402d00c2150309010844924039900c0c0e40c2c81c50254006840f05402030a00d0340f802e058404018425002001c3c900100d4001d910080407442c0e0301041980007900542c3e0182c0724400460788083c580400501c85510340e212144201c90200f070142031828080300084049103000c0c20071111222502072031042d40c00c030000385500c03900c81800580e101c2c0d181c01c1104a21510104000070390341151110040d10030700c06e40c0c1c0d030040a003007007003848550413098510034007580080c030081c00b250900200041c0d0090140607055044005c1001001c1241d00903601035002c541c0792400400d050408012001c2c1b8448156003c118a88a000040d019401041082000c060701c403450104030074070981108900641d0280c0421541d55249006580ca42c040403040780401c21a80310142d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276255386 1250 276254136 276254161
    0x60f0306040b0c04080610060e040b0901060e03281a100e0405030d11040501090b1863010605030c040b040e0f180d0305041a09060103170c19051c090e 66
    0x5440014150861590904003f07545200d480c1e091290148a00050000c1040441c8014120704210060071a110030080c20450380058800c42c50f0240458110240807007101130f0300c1e01c0000c640ea01d96010800d92510300c0c0243c00c6202e0b02c200e1580180c1403143c3c890410501c800140125003098848681c1155100744100090003881418039407001e00c5c4d58203603001d060203c0304c445803128045407a9204075408580d0030724078210b5141d814840508a11122600d4803a0121641c4841030300c03226410031940e8a070f400000b186c1405850108080400441c00920481741a50090302c5050051a116904d4114406001d5401c68841403403a0101000c0b416002d498440300d0740c550000000f40c5280c580c142820b8016181c090400c4409110038612203200c4401600b22502a0f4000c9000c0d102c10f51550509910401503840c4c8901410401c00c4401401030b0002842d8403400f1000356a035400449904100e818161081c101040302904483c0703101e003407a0301c0020102580d0300c400d511501ca071501020480c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276256636 1250 276255386 276255401
    0x40210091e05130e030f0705010209060a050d050a0902030309040c031d0124080304170a150f0e030903031215030d0f0201050a18030c0606031203020a0206060f0306040b0c04080610060e04 82
    0x409800402c000302d0110005d0008110b41750023071001518106086001c12450350001c1001f8000841c0410300300f82d003000b1800307282e4100c00100c0c828403000c2d045800003612031041c541100d1060b6910854a01800e0290300b100b0f20010b1842401a00480707004d40040c0038200b00e095000c044054400707071404500c8251251800c2e00c2c2032900a500301410440c20301c544d61072824040c2807906c208203030074000600c000d01100c82c003109403401081000300f2001e200c0a0350940425411650024041010292800020b40307004641703800c504411a148d0003454813500003a0b444181e0580100d44110103000d0300404c450002ca03c25600810151351220200c904a81c1100204909039882050500100f449006076040c01400340d500011116580d41d81ca03202120704101d81070100382c0110340070462a805101c0a130f80610b003616203003100e029220001343c880800400090080d401d0501107003852300c1c3c400a48000d45080c0c400c66005041480d5002d0b440552842040006001c10150880600f000d004141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276257886 1250 276256636 276256661
    0xf01090b0f0a0209041503020906010306032103020409090609030f09180b01050c1b130204080601050411130816060c1109060409020a0b070209010b0a08040210091e0513 74
    0x581601c0703000c030040032284050300001d0300c29002d2052568a0385c0710311a91081045003016030303444a166105004040400424403418540b61100400104041c4403405544842d003617400a10070603841e03030580003802140c012a0489240105440c1000016400003400d94000d4807407010341450b5035030464002c105400780040c060341000d500f90481e4150f8001880040f414104503080c0048203259034502440f40c4175940c0303506400011120300d402e00d9200c2e84900000c103402503282500b4581441c1c2c7d14a018414180142c3d5201120a4100c900d5425a901441455a4482030036074504a00c1d0395410041c2034403045200710700c400916107000c0ca20343c19100743d22034504016000c401d030802000300e2003b81110303001134617251600300603900d00a40e0300140510000c49a140d18290041c02480d02c0148c0110002d4a010081c02c3d01050700070180302e505c43c0d030446101141d005c030034104a50a458980c81403841c00442550100c03060000062081070364002d4450b80c007201540003544060f0754020382282c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276258992 1106 276257886 276257903
    0xc15090e090307030905060706020403210206070806030d0e0604050307030b01080c0f0a0e070507020d030c0b060418110312130303030b01020303070e280602030c0f0109 74
    0x750030501507401542415035a90380907000d540e56010350f51207a40b001c1783c400c04110482d011600655800010317111055540360314085034125403400500580a00000182000c0c403504070341d441020001c0007414101d00105041e11580d0441c07142c160084070800011885460400c9028000c0d4420302c4600703010343c905408241021104003119204107015203020019550314114030003560741c3c3c03882c1300a05840300c800030b131414131071380800030f4012480300481d071300b4581c000c08070b10300d514000d0303800300c980799a100c0400040740c03084409001201800c1a507400170480f2441c01107009000a000c80c2e040342e09241c04804107400c400c82d8200c022100140a00c10036901d0300400c01c1040d8280000e40c02c40c100b840d000741c6541410302015002d800c1342c925403489111185025117822a01505100c0c202d030312004000d45941c402080180d09100d0b44c81c1d0248000b80500c103083c2c0da1604141d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 276079136 276258992 := by
  have h0 := BRFrame.cov_init 276079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 276079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 276079136 ≤ n) (h2 : n < 276258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
