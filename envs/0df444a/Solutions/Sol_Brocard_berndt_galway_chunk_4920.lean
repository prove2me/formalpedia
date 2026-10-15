-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4920
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:32.613191+00:00
-- url     : https://prove2.me/submissions/759e3644-a3c4-430e-b17d-04869cef6778

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 884712230 ≤ n < 884892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 884713480 1250 884712230 884712259
    0x1080a080c0f150a060503010504350c0a140a030912080405060304150e0a020904060911090114040c030c1e030b030d12052d0a06090e0f2e0b 62
    0x1c1c8041490300f45101003c2d9028900010f40004480341030b00a540aa890a003c1100191014401100c11240c22503088110201e580100825004407a01803031350480c0401e030300c59540343c0040d940e90000e01c54201291041090410ba66880d59003010190002c0d0140d0030410a20880f4a01428000d004e2a0711a15242d2100041505544103580890746e400e0103111042c401541c500c03c0311904100540500780b000c8039900020107515001c0c0c005040d0940d076600c41d40c200f0282d000421102030700503106d50315541c7d5900b141c8ca40c1501c4c003d02203006038102000303d81c10380e20030301c509000025541c9a8404003950800d0360705140864628482c181a038130014801990b0342000840d0700c0fa41550b880070a608055003031035042e2030020f0f000628035001c28903440c10700484102e15049440c070407605070030f40b6914444114003a00342580065002c41c0380101446003000c0205001d145016814200c1d1041310307005251982150300c100c031004031845010982c006104140d00b01c454444001010105400701c2c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 884714730 1250 884713480 884713483
    0x41203021c020f01060b130e090a120503070315050d0b0a091502040303120b0a030206030702030d0614011b080d020904093f020a0b07180f051801080a080c0f 69
    0x1049003007000769008070320303140380b8080074081c2c030001d004640304150800e0b81000c0800701010141c060390114407200400552030380350070864410761070f4008110507800d06140c80080c0256009843c0340002a003082c0351407503803d0192500004584014000007409401600d48601d503650141c50003007060745600100006c1080301c0564030740e0100d041c02c01603941d803542c540035100c501e5006841c40c510303042124007121036885941c1101140e070140c2e90540e4a80d2003903805c038158400c40d4156080e041c54010003207410040c00a84010303e00b070a880311000c07400781905581c0080085240180742240812110256910540140c0411000900041851403007595100e440301d844051010036207070242c0c820006802a1900604201040a032108080c01c400c040207440301810328010340700407400700100e1000c0b846540780e0011444114480f01503541ca9807040d412030286445041d10610204291110081042e04064100c59039100200b100c11115502c910b4a908440ca50442c980603240800c0840da40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 884715980 1250 884714730 884714773
    0x10b04080618031c0b220b0904020f15040b0c0714041506030b150c0c041b02120703140d06030201080601022a120d02060412090302030a1113020a0e04180804120302 72
    0x8421807034031068514007006c00302c03900140c07003030b208a448801780303c05602c1e11100c5a90b443e01c1501d0801302c0207518840b82d01035104650016031042400100680603140100c0c000003a280c006840e82080d070003120802040d83c0c04042c010503050061442080128001d52180b40e2025003e013185c030140c80400483e00854004540d01203107500010b0341545289041d00ca042d9030f04080010f441c04039030007081c00941e51803200d1403c071180d00000401714141401408207000020310044104d5407800f8422020010708510312080380031540305404501e06600124070203445030740c000391220400b886503200004040303500c0c0007241c1101016074a803d104405000300c081604144e00202540c0c24a40307881024102420a000b0400407100001c0c40140da021403a2107819400c821800f11103160100003803240440d2501c88034089100244041c50359802c4a28000c1444044808000025040310b210303404009488000702806020007044c01007004141c1444015400391044401090042500058201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 884717230 1250 884715980 884716009
    0x4230f03011a040501060203340f060209132708090414011a1c02030703060806010602100b0d020607080a02010209030a0b241e030c09010b04080618031c0b 68
    0x1102080b003501c1d9030a003070140c1801800d90b44015881d100241c200c542103a072600b450740300311059074200101240722840b400500c00790040c844c540780e90550300d4940001d61216450500419200c0e030301e07100c201114494460b21000355044002180c00224042100c1c3d0480c14046903c180c082c801059961144d125211851034001500d02c0780354105017402d40403619402c1b44038201002041011120016075a0a805080a814003d80c0700c2d100c9400c00d03005420319070410882481908000250f080d070001c2d010b240035034080ea0030040e05012109015188a05001c003942180d070410610b40068401e000521583c811480010700b0061030b100081e08103282e441c825101810400c080c001d820300f5901ca210740c040f0b01c0074070609503c2e2000c0081840c0c50181d1a500415900c01d03008084183c070103001d02c44500c2d4005141c10310542c1c441c0d2103100d86800078028070105218200007e0b41589002401c034841022181c015800d1000d0030f0245036881420704100400580c4841252300d0f2601c039148980c1001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 884718480 1250 884717230 884717261
    0x60a0c0606081f0b0a21050a060b01090605040308070f0f1704170d08010311061b011a0604060c11180a0902010806190b0f16030903020406090204230f0301 68
    0x404446010304481203400e181058281c030309120f9007030039175540d1100800c0702c007100b900d00310044080030024031640e0400006012802051402401c100d259400700007100303802d8031602001c903120b1000711a1405140002020040701b0400180820030709007115101501ca0006881006250390712540e0b143d811114040c80f00c03401040074081c03040080c4281014103598070091560402c2141c0003000340740188005401c0380d109180a41b000c0e20f540c0d0840318800048528003040c14281c65000d802081c0c5201c3c60b4070103850a00c03200400f0324102d0200c03400c55800b070f500d00d19030031800c1d190038001d0000380810f20ba200c96180c00c4298040004103d01c1d11a8020320000110345495000161600a008216a1189900410403004502000f684e00191a03410040640303900d4060141c100e948600101c0c0186101e003607001008142d401815202524802d0750203101040d914640081680180d0041d403080043e1003281e80d001c0c1a078241c08000500005106000103048000400d003119000740b54142d18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884719730 1250 884718480 884718493
    0x3f0102041a04080705060903060f0c1908063d090509090109020a0906080a031b0f050f07080102090a17010b090a060e0f090d0c0302011413230c060a0c060608 69
    0x403281132164000070182a80c0c4d040c90303e80080e0000ba01c0b000010002e20152300028040342c125011032050b1114000c00040c060700c0d48103c184c000d4450b00003151002e12403036601380c01401517864009420084203031411590028404d01c40c107041440701c0c0503901801c03c0410a00010503984601c1d225000e03c031200300010320042c1038018040c2032001600210074490511a0400c140c10300010215281d03501031a102901030000e120b01031181101c0c1a025008180c5000e1003010f010010030300c446169811802c8910040e5254040c6080c0d02505450550040e2007038002c100400070040c1400c5030704207500000800c0c1070f110001440d80201510000e0b861503803100d041c030608503000403098011041103070b2400c583c642100c0155a0b41664a00b45041200890848007014000d40010303a03031203c001d0070b90940b4a42000a0001194090800d8071114003221046200408064052460b803502002405071200303c82d0038003003540c8c000c400c01010010b0680c130749404900c0074451480a0606480645513 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884720980 1250 884719730 884719739
    0x90a060e100608061005090d05030306030d030c2a1a0a0b0108010b030a090807060c0c1a070f030e10110c0c01020d1704020d1a01053f0102041a04 64
    0x303000300a0001e0818100800e0a2005540160210394004c00c211802c480b290680c240486150248100d026000320800c0107038020800003102a600c40c00c000d50484401520700c81040f001d940d00e41d2211008a1074212340100c520311320346001d20140b542e10b50346001d130b00300507611201070010040800184004110520110464034010003007001c10034a0080e0940d4100031300c441c25848050000314040303984c2c0ca0f542003001040d400340e0f56015049403042102e042c0b1100c0280c644407016104039240842d028180010340311803001640a20712543e02e42403c2d910b601825002032070003c0180f905881000f5689035245424003541c0821007020303503441d03142c4034801e0150f46000340503103445d070541d08050ba9546115038031034940012500c1482190302d10344c445e030010070b8090300348583c06090443d507242c1d00c18600b0082d244403412590165007000c018032301d01c0381f0400b9944070000c030280041038404e105400400303141c204c031200600038400145410355502000d0010084588c040c000c00101040800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884722230 1250 884720980 884720999
    0xa050c0120100c030905061e06091e072c03060a020301061407030c17210105132304030c0507090c0522090e011415062502090a06 57
    0x2803440404060700150031000e104280d141c010300302e003000d4407598801c0c1d42c4030a184282c00181c150360700b00044d91030f1403d0210507150200c03181d80c000c908070404000030601a0510078145442800c01807404990080c41b68100c2d480b51070083e100c8400c01101c490001103824030000303288198100010703440f902400450030705003841c0005161408052040c80108505a0000c840c8440000082000c0750f80f8402441c0556810800ba500506a21a645080c451070321800c0018010050203100e000c500001c451030402d07000d0001d000e500d81020f80c82206c80003102050b000541d041000421020b00842c090300c40c00541c550898045d000103c0b00d020941c1801014815580542580074080c0144030418601400c10b1041922011030301040100245201101d1a1030380054a01c806050001401001440b40030b0020f00c41c01582184240000c500d864420441c10707032038030b40003070f1545007000300325200313200c00300300d0350314075190a212486156005a0b07800781081c1c8a04505200003841c20705000000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884723480 1250 884722230 884722247
    0x21815070b09210c01060f0f1706010b250203030708091002120403120512090c040b1c060203040512070c090605010f021e1204170d05031311120a050c01 67
    0x566160003055104000101c0c002e404040040f00900e41030b50b6000701200c041c01000b02d603000392400308204a02007030700c064913800030f003c681150340d54007004100c90b010140c6820f000e10604141d003070100000910b10401e600a80781c4030310325240d14024000c01d500440e04681c0480c000300c40301c0e58000340c03004961600d618044002d06261000b0040c1c002c00410441e114460f500011309104041500350320748a00c208125000251352216021705420000300c800d03911007031030a002d88580d04010f41c0e210305080201254010894801404400700702e01d49488009600c0900144c0e49801410a00e4402d074441c01d000b80b0180b4400d21807404600d00d070003a140c00702c1e10315421160411101d030822031807060340080c1405540c3d449083d0075241307082d040c05030352403c05003808200000f54082000100e0481201001502c000c14030159007402506950031682c40c40200e07485020182d20014003408104204801c0c0c82440010308854518103039038034001c0c9000c1c5201d100712015032140000c8201540d010f0b00e82c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884724730 1250 884723480 884723491
    0x140c0102032a0901030207060204090e0c1513090c0e0d0305130e0c0304110a12140705010807021005040f0602070b040201030b06030603030d0e0c0a0f0807050f090a021815070b 77
    0xc010a81850b61928150348900c901d810304044d008a441d20902159904030f030014000b402d01005800044694a0f4aa04034062882e00c41c00f1030002d10040301c0d90140803112900c001031079011410b820802508001c1082c051044104140d0725400c0b0b0b0903445910041442d44d00a0f25050703104d00c55460544c2008010f13030810a0192440001d01104a4600c0b05403034225600c0b411444c40840f2001c04600e59081c103611039403840344031040c500188407601e50100d0100c200714095400301c6490720010749202c40292004401079014009102868480c1c0d80322503005442044000fa4940c296220b00702641c22680c0c0980f1408a00014001150b07014411011f0996080c4c421138114904540065224065000070501c040d4452510072842e88060041215801004041a13171454a44004169101c900d01841e0760b24480d0a801140c0d80c5001002c41d43d04090082048403607545000301300001c0e4010382c1103d1044004402e84504507503590000710781ca50b03550170303013203459010341e0418a5900201a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884725980 1250 884724730 884724781
    0x7050c10021e072105180307120201050d0b06070606090e0c0108180f0307060e0708070f14010516200616060203042306070807020d020616140c010203 66
    0x20b81c0142c01191080b040080522110340354451415003090305440c81c11340540c1e58449071001c440041141c01001400c000881c650303c1000341a000014150f1318001405048040c0e0250000480150b00c5440100a501c0d5801c40201d050041c40010404542002004590003502d03110140800d05862291808900600000303000e207030007980001c0d2248001900715601001d1891601000c4041000b08a1311404030f0411070f9079504160070300ca001000d0640080c0c01038051000300145079280050200195003030f0381841408241b03420a11001c607000102c1c6a4140001844001207040a00e4600003009002d2169109000b0801d0402115041c6072180700384604030038007458182040390301c0c0e000b414a5005000507a66101e0b0f003824200c1c418130824040341104000d019421806010030114060103031a103030b55000d07881700300050381c1311901902c440d0016845100056030b00c5c2c1001004c00310100a5003002c80c4002c107031768001c00159004113200c4c45542c2d000800e002140e8800000c007145d900100703070f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884727230 1250 884725980 884725987
    0x3121e0f140c07030b010b09040c2c0a0806070801030b10030f020d02010c15090b06060715050711030409020c120a050418060e090c040c0e0a0608040807050607050c1002 74
    0x114050011000d201d600701c6109800704074450b070100b00300902d501950300041d10040710740e5500307008200c0e035014420190040b410540032540107401000e000894102c1100c121804803626403c2c00028090100c074a944500d40e0100010307051414040139000d4003940e03442604560660800000c542000b41500c138041c00c42c45800c00104039045510802c1c1c0703504481c0c1318a03044d180c0c00100c03000035020344050200880d00444c1801c1d00b00b82e40c000c1d903803284076041d8621203540f4103081200502070a14042c200c0001c0070001402c141c413a60045a006a0500b42482c504481c860510724580194000c4014a6400500303171140175420002c0040d035106a0341c07040d1400c2484d060003409802607102d207001d800198644400c20990542114000c0c180b0900c01071560305d00034030036a545241d681d60a60080d0f00c2c001d5840030991144031041c1807a00060007002070945800001c6550340d00041068880307034414050540040c10902003c0c2c01180203075a12500c070520720b091a41070400750310440352142e1040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884728480 1250 884727230 884727257
    0x15090d050d0f06170a03020d0c02010c02120106080607020f1207030507122d18030c050d030e0a030b070f0c20010e03060106050a180503060604051003121e 68
    0x24080300c154601c0120041000502401c0c0b0001411540e0019600070030030480c400f02c030f0203000500c2030003e8040da0850f00110000d85080c4d82c080400d42000e4005000403805001505001a00d10315140c104000015607a58450403c1d0511405641071001a0020104040350711000c00c15180d02c07007500c003085860700520b907a0242c41071144420040c0b80228107441d020000740541000081099019007807000c4c014142c04141c0710a107500d41190110300240309040c0303284020120401030741d6100205601c00b50802042001c0380d840114110200241121030040310380310f20000f40000d511500e0188240c2c24106d8015000901d01e00d444c0301000510080d42010071050054004a4031091407001603045c4c4510040760782c040040803041e010303c03c04000060556014008014264243d580c2d0040300c02c8600881d8610744081c400c03030750305034094404a00c1074034107644100e401107021041c81040a80d2591a0b108400004000070080348160070213443c0b40409e06403810f06807a19182181005151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884729730 1250 884728480 884728487
    0x7060e030d08130507151d010903080f0d020d020405010e0d050d1d03010509060f130b010b0906160f0201020111040e0f040203030c0f0f1207020901060305090a0b0915090d 75
    0x81e05480000c00140344041981141c60f18000145035420100f40e401044e20307210711604650205c5174040000c0e1540d103030309160080300002a00a90700594655441600d5504c0f50300309500300b241040f41e441d000b080454903051051000b40501c0104100150f1240c3c038102c0050443c4140e4a0580d0041c00c0c4040700038005140825121134401c0b490070701082c510350100d1001100a00509520b030035610704802d00148207000906c0034417602061b010344d00715545183c0400c40c0002d0126000b0404c2614030010302c003c50944000d046400005813141c0e00300078044603402c0e002400741000f030350559840700310704055590a010701a15003007200069403400c1c2c41e1805d03030104c45d04020702021107486000049001c543d010700c01c45400005007405c480c400d0445003070302910781800c848400c41d80c0c0700e1380d038916258060920903030b1a442d0b001040300446a181079400d601070040280312120501483d00450005001c000e9582e009403902c00051240c000410400c1d030300c43d1800741c03900da01039011100c2413070391950 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884730980 1250 884729730 884729743
    0x103020f04090e0c1c050d1e11191b05011704030c0219170c030f1e0a1505071205010b190302040f030f020112111b0a0c090b0307060e03 60
    0xa26038001480d541e0005006080c004c0030418242d01010743e40c080070405408042c031140c45401002600d4003000e50040580f4100c0d41250b448a8200140c100201414041c08a080c00741c107410041d14511098601c41314810010b118045404c601d02110004203c85484c408102800e001c1c2420441c0701002d00e640d84020718007d200800300624a5004011134030703510b901c510310003800207200007055201c040e4120061000c1b456a030f1144180c6003050018070300000d0015203600b0303030400781c10400e003a804076506c1989540c0c0305180358481c1c13010b50000205040d54908034003c94030000142403c100341c0052050820a4081e045a8188001032205904850842d440c15203042440b00c000300c0807150a4010f40550b6010b0010070722404000800c2c44010402c0385041c034401da0710807000c2c44500c9151412600221500c16900b641442041d4840b59640c2601740d00c03001d120101c1c0d014000366501c0c0c00b56201c80b50000f500140e11521650154207040205002600e15400c20b4010007d9a401199950a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884732230 1250 884730980 884730989
    0x17071b0c1d0a0204050a12060f0e01200f0a0e010c0b070306180b030d0315030b0a0b0f0d0506041e051e0106090b03120d09021c0510050408070b0a0608030c1006050103020f04 76
    0x4840c0e2076030010403085500004027807174204c4050020283c3c1c0c1c24050300908080503100d003c881d4040075041c1c0d02545a00b00c070060400c0d0003016060241400040b41c00a17604014503043c840400a42c401148100a06620842d01a600401c403e8181754810050b00c9440b40901d00150800c0c003240c103a940e0102c1d0365041180d05e8600003031443c644003480b07000b860b51644050418150b4205224182e582604440c07000001601d8411900e130301042484407400c0702c0382313001d01175420400105000600d040c0140c0c4000c00801c809220180c6907450f11424403020504001d0281e1310a40515103c00081c05498010b10b07282c1010404440307244c011988500c090001111400030004428030035600c203030f001c404000e40103000b4202d0500901214800b0981141007500c01e80300d6200410134008403402003500c03d9a01180c00703400c0022650364049041400751090b151551a25400b14280c0820400ba29120003400010213040c941055000b04452950704614100341c01001181c12440000b8111801c8a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884733480 1250 884732230 884732249
    0x6032012070e0604060908060105090402030d030c2a051e070501051b0303040b011d010315090f0516030b10050105040512010b0a03060209030d17071b0c1d0a0204050a 73
    0x15510200201e442c040781901c40340d80f05501290105a0992040c1c1c030000b56034540f000c40d98541d8a0340c0070041004d908440096042d4405441c0005051207900300035031400c00c81c101008410740f00741080f600079004686070b048108016441070103000040104520085142581c00600c60f00d4840054507a40580141c5041c440c0004411111400f00c6000d60001c00300c83d81901d482e402c0c0f910705004905000c1c8100800c43c40d9a262061500c440c052595048075400000c07004003c414038035020140545020039280c0b12071280f00000420014442404420310203c4448512800d40c03400c0c03011408064a0f000c28814454418040350760482c00300d0b42950f0303044854000180001c1c0d10703603015028920700a0341103184504000108203c94024002a1208400b40d035100c1103000400c0301d80010b0500d6015041250341e010a1490340100242e410401c0a08100c00c1441c105498405030066268000c3d00354400112082c90360201c08060650465082c00007549131614020005020b03100c503000c2d10b40035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884734730 1250 884733480 884733517
    0x9050c040c090906030506250203030a0f020909010303020c011202040518040212010f06030204180507180f050906040c0509131506050d1211030702090a09020a050603040c060320 78
    0x490b4020104540100054802071008036180c0c5012620307868152030401409400115980034080d5440d00008610340990007182140d40c0c44810401030301300c1102d0802d6195080100c8142030315050b6250f40038500a0300144000899400014188001c0c140c80d034882c2c1c0e20511040c0503e60b42d07990400200c1000307016a60300d603241d0307000080d000b10f240001007c40f58a000d25541020240c7d42003541140d0088408004c1d9284600c040c0203070640c04180200305030000101030001010741030140d518100c180720300083c070b407017026004401c440041d0744499150744260100020407608101c1d000141c00f05580c0394601c0d06002d02003d0302c0741ca079000d00820030200c02d07095120304002c40d03001100402c0010201c140c03690b45801c0c001d40d24081c0d04101300c001640d113941821001800812168001e0b40503203c41c510f9074440c80544020001407100b20b07807292449000244581c0c3d6a0059405a8000c104c6810514a00180030b000ca43e011440901a0f1050f4442d2042d540c4010041e140c640d01e507405030b00700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884735980 1250 884734730 884734751
    0x5180409020f0315040b06011707120612050a02090901060e010b03060303071703100608240d1a0a0b01080c09061305090a1401090209030a12090b03250309050c04 71
    0x4415002d50416816110340050050014500c0b019680580d000d0107a000445c2c0f2a0401102c8890b0500300c04100e40054501017200603101d0300c040c1c0c0c4003c0699800283d100e403143d40c100000032546009031003039800350346808203525198444903081346d1814020407010380381c40702c03c40000c541403007445240c81020000513916103061044929455000000007500d01814110040940042c0d03240c8403103600103003002c900b41e409081e00e030f4060284107003040e003000520081c90320502800640b15801103821f2981c4000140341c2e0054001c0940e03540c412075045c0c03603c004564225081c0f0203104d030402c032149007401010f450260032244100c000740c60507a56600010a20f810b00501030b4803041d00008800e0401146000507446010072100c80c4002009990346c90046506a00415034807a0740345c0c110034020400901000c00c4201410158140091a6030395800e81c4202e64008a401749124658a1010340903215004c0380081c124906060412000050391106640da0340d0103481c41d07005580c2d4004840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884737230 1250 884735980 884735989
    0x50d030e0603010303030c02060a150b0702040603150b121c050304050309130e070801060f09090309080613171813090f1a010803031b090a03060e0c030d0518040902 72
    0x900c4910041c111035583d503582d150040041c068007030144018064a000f142c03400b685c0d4001c600383d0300e415022800c0300d941014a01c85d41d0781d01501089900c02d41e80c080000c002000e01d10100c603640140c01000030450110300500c051108140180c0d1000e421841409a0103120381c9400070b0300e00e0140c13409a4490741c0d14584103103141710714402185c0c498890100400d0140144d005181984014000d903188181d4800d421800c2c1c401900070400340110b0b00006100e1640d0b5a400055000e0180c50240030542c6e903925002d040a5050300d040d200715590202000038000645035078a000140702c0e014a00c0c14140c0c0d03000c10303000e00c001111a4410303121500001c032480883c0e0081000280c2042020003550304624000b05480310820014000b4041d4400002c0d44000c04429a4415070102103400d00580c0480d0390240142d1002d61000e601c120b0402020021450741e1068204620784900105941c500000405180030a000300344001c02c082080b0000c0313a107a50500c0002003090944010804a240d0701c0080c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884738480 1250 884737230 884737247
    0xd0e010e090910060f08030715200a090e0106050313151d010e070605030a02090d080c060a060e0712020d0621030e060a05070308060d08031006030b0d020a050d03 71
    0x35401103801c428400148000700e10480d40300f8100d1010001d25540d1140d1034501501072203500e01680041c001da070085280101130414650b0301c4680002d031841071820456480c01d42c0005540000c0c008107142281701e801a000c0400390600040600d429850a400104688001000440403402c203c800500f04017001034050402e80c6820018001c04e8060000f0301a10080a900112250701b860207110a10802155810603902c059039014035599441c030440010f5030020500f0b503089040030081101082e010350203085103454600103444a401e04200c0322003550280d13007000781000041d10512400c0b40d000908081e182046c450f000d030712040300807140c200034807440d4400e21980c01d80d0440d07009468040301d268082c01e4866101e41007400120310510220f03009080802000c01d90401c81d10001c240600b44141e07008000800e11144a04280e803504940d4009032101f1120001302001480160f4050041095100c026a1410b00044807900001c0b8007580910400c0c2c05500181c0b24201450320502c0704 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884739730 1250 884738480 884738507
    0x15110304051c06110a031e05010b030f0907240315150c0c12060c080c210a1b02031809040c03080a050c030c150a291309062307020d0e01 60
    0x4d20384510300940050090310184011401321035104241020410aa214850503500fa5502c142e04503560a42a00580b05014020f40842e01c50290b0018544c940c400910040c280701c5000300708000c02d1600c016064030a400f01041051352984803c0c03007800c22031101c0c0405034149207840c401840c0701d410604146420394100c2c140340381c02c500f001c609120442d084210310700c00c540d56a00a0f85c0d00d02d560000d480c02a118101c02542c018075801c101e9445882001e500b0108040c400940d211441810080240d01d8140100141e00041050b0003000d10008003082e0180003a901d900c080e28084d035402c1041440c80c0802072203114040307041c8819030b219400340c920038521300c02140e643e0500c4440c4e0560382c0da401c0111105240e580c50000b5440541d5000d444122490700b44040a9161002140c0045003c01c0c80542c0e086010311410090418550003003d520a000e9800054848001d080380d03000131070180320091922100b40144200c80c1ea00158000183d011031602d01c41a101c02c80040b80c3c080b942081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884740980 1250 884739730 884739761
    0x70e03060c090114131a040b030a0603061d100515030a061b0309200f0a0b12070e0a1a040902030103082212020d17030115110304051c06 60
    0x2044071240d07201c002000c9800c0240c80f01c004540f01c2010b4a4680c1c441c0c01c01042d2076118444042150080c11504030039a01c5440e2501402e15884107103815144d007080f2070791307900551501410018021144200b40885100744507115030340d000100d107143d9030707441d902c00c0e82c3c2c981e0755800024850103c2d0b03880c04000401c0c0202501e15080041c14000003501450004090b024000b003000c40c3d9940c001d116000c1400d6000380c942d6040340900b00048910100c40c400c0d02d8211544240403106544c0d40010f25025084d0417260340d480c1c5075000c0c50402c1c4c4d06001040c0d1028452103c40501d1142e44a103420380440301c80c00d051507a0581c02202170840d40c00b40f6404220402d0011001008000e00f010141c404903901d6110400d0100700076480011320b0728107105144002205041150150078503440b01c1e071485009100070590300e00155100910744d03201360720400c2d048802c840c10319007131a0303c00030340042c14150340000d50505003094005040c5c1c0000c5141d0b800403e07000d80c040e03006c11401350400b0001e14003510 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884742230 1250 884740980 884740993
    0x60d0e0d080901050a050115110f0303011701050f040201140f07050313240801090f021303120f0507020303030c0c160e10080303090d0f02030d060f0906090e1005070e03 74
    0xe4020389050400d031081c9009508040c00100305511602c111ba04850120341940074000301d080c400e542c144001c40000100d03005480c0c5200c1c8124003040154000c0200c00d41d00c540c4a1003140f0790b9804c40754040c1071711054154603424000542c0c2c2c0040080e040b51103202c4900da44907003080705800c80d0f1203119001800da000c0480c50b06030b071004611081d8101c40600d041c107810a82c114142140c007030701a0a020011858200040c8041c00c00c9a000100060b1840c2c0010b01c0d001840003640b0341490198401c8a40a00b105202d50205a02030442e52031204032741800350400d449540001d869000c01804040d055070081031b4020a40b504000341050107428241e101d00341078a808a40c200c0d0b1100700c079002003110078401c0c000340102e00001184d11640d0200040c22420320003900880c0e4001803c4000001c40c4820b016401d030141c2d0350302c00c0a000b440012070034002035140042400030ba820344ea200a03d5a880c00c800003001000204007c0340300859040d0021301a690700a0540361751403201e050b00c1d054810b08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884743480 1250 884742230 884742253
    0x4110d060507260f071107030c0b07050f0d0c020f0a050423060f060912030f03011706061c0201230d0222051f020a080c2a030309060d0e 60
    0x2c0743c800342c50102003560501d9480f100f00391031521201914500c41c07041481c4001810355120b000f1a00c1d50501c1c48055941c1e40b941c0c0c2d01e440d815030b0540c4d04078141d450b000080c9001041000c026524503c0da40d480502501c0300c0c2800d02514403d09800b020307015440031403002e100360b074400950310040c183c0107000f08030011310091980e0f91003e502004811880c9d400020030002c1c40e0904011207418002030a242c9460307810340c02e02c807c030314055400d0425444188800c880b1328001e000510702030b001c1905040340c10350b4080c0711545081006415240541903860910030010148080000601d4082c00c100501103050755203110028112065101502e0340890540d0100d4150340080110400400121103461281844070701c6000b058801e25030b020007007809581c080344042c0558950400b59005a8850314056112050b0590024140790120b4101c0c01ca00c500b503285208403928013182803051100300c218440003083c0d683c843c0b003480500c141008100700c80c42550307541150f00310b04104400d940a61166 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884744730 1250 884743480 884743487
    0x270305070528030e30070312050c010501140907031e020d0b01021002031e130b10050102060901090506130206071218080c0604030605090f0a030e1e0904110d060507 72
    0x4a10b00b2400103110900c048841c0c03a2050707450180c1e0040c1c80c0d00400104102d0402da1011078417003881d078618040d41c1300010101c1c0f5410903c1344290320726140c142d5103120400100d8211541604103101202100c8290543d0fa105e05154684c48078480c18001401285c8405904010381c055540070310603400018405101212900309448000080e001c444000e6000c51b03c0c1c0c0d0590000f1036049043c1c2000c03c00c06100e00040c110b03880c6c2c0110070140040c0d04062143c4940346003200480d560030b000710381001c00b003260303580c1048403541c060290700c000c10903d982c1c2d55907651200c5010307103001c05032403036141000705542d1550200c1ea0056031209004160a5031070001900d000030b02c150003031801c003503a040058054400f082c5d160303040c640203108a00d42820340d50384c1c00c024200505610024424800385840d0301c03400b040490140c03402519000b00344522880ac01043c0f203030440320703032004c80b4600c0c1103400e05842c0d9102094100b0361100c0440c00c0e0b00c07003000204030b14280c0240f02074016408c200038085510782 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884745980 1250 884744730 884744803
    0xa05150d02012003041d090c060a120f06060807020a020a0501080603070f0e180708060f151e040e0a02010e150c12030103050d050a050a08060f150d2703050705 70
    0x46004400c0319280c0285004680054212105887c54114091180052810310300500485a045c14440b2018420180d820100c41006040c43d21681e600e500601038560003413911940512648000c01003040d00764080f5400000b03501c21075051003e190049601543e0a114000140c0f16452890000075526601e0714a0414103849000030440d50641d54414013074081807500c142c3d681000201000c0d1600c01280341454002400301200b0507a0030b0301714542d599045000050100b1200102d07a40c00020001c2000f03c551214100c580d42c0d00c00031f254001030f600843c3c02c02000030b0469201004c9004940348406c030303100b100b0240e00c40c0d01500704030ba582200400301441c1030300d0049007141c0d00d4004101c000d490501c183c86642011071404d1016030281c0d8403450745c0990010024080100f00929000403910303050b0824203402032000701248001c0540820710507003109060914080580449241000380741f2281c20101034208080000c0b034034140001000b1001c1c0c00105203050291440300449000000c44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884747230 1250 884745980 884745989
    0x6070803060f010c0f030e03100c020a0605060f100305090c0301090f050f03070b0f150405090a2d08070501090b01120201110d0f110109290a05150d0201200304 70
    0x30014080d08465500c0b4411310000c00340c1c0310340b81107031145060f10107a98119601c50582e070f0601c640102d400080da0719004d59030007420948c000703003401c5402c0d2030000240c4000512a900030a600000c4407020b1751154260030bd078000c1c604000413940c0f2848816428060141c000681540c03d08132440104a10503100078a614029001d6415044030301d004641c5a00c144400035052110200208501d012000c003900e1300701001d405083c1030b01400202040c250b4400b154180c41940041d0b003614140180010141d0b402c490a041c80c9100190301c030b8524400003a100b03030260403078a020882d04100f01c401d500c61845c1503000080c3e0741c590b603503504c044030401c1041e1104038001044090400c50000300062880d4140c502901c83c00504d101c819130483d05454003a801603070540d00c424032400401c410b0350f0080750070014000460142c070084103500b9208440903040000881c07034401003107441610b40d80800b11810081b1201d2001c08000e0004a5084940c00481e80550100003050f00c0c40581c004001d100b101d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884748480 1250 884747230 884747239
    0xd0f05030304021f052a010c081504110d0908040b070f060b04051006260a0c030c081918080d0509100e03030109110408120702011b0305090409110607080306 69
    0x30141e010f000c21325100c260039040814030500001c944445400c11108181d2440101511080c14a00c0c0e10382c29903000903010800b152240080c42120b10602030900d50310039007a18207200110071601e0402c01446820802c0321300c1d40c0e0741c0284504203e58903003282c004010704a51952500c1c0c0505192104010051003120820b18050608485003003d004e079a101c0c08100c40b0700000340b4a890343c00d6038401c02c104001c1c007907010032020510f0309441154825014003c0c00310700090540d503d490150840740c000b007040003802082e60802596420b079001074401d400c040d41c0701090481480c42d880d9110340b24000d00034600c5402142e42d5810080c50361005209510340403c0303407290b0f210789064808031440f0000c0c4084640042005000c0003559030018918415258001842e15070395807102030920302a280445418440001d1039805d541e4008103a0a50b0a25051a11100001580c001c1d0130ba07c5681203142c052034a4004210600400c42109000ba41014004079a81ca40300d1800740d4545c0e00454007075215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884749730 1250 884748480 884748499
    0x806010806091e070e0a06030e1608070603110f0406020d120c020703080c070504050f0a0e0d0804060c11060705130e1536070f020111090d020d0f0503030402 69
    0x1440c1502c48280030320b10b2903440c842200003441c0b00d403c0c81c80009011304140503075000c0c0c04805841d05626400280055600013030803030701d04003e5505060105c4402e088840c2d094000303020210340030a602c0201c610741e007400075295080005207545030081d901ca40807001c0c00418006101600456410400301c125075034400d80e00b1070a07011008443d072920340400164000c80c000d200141511004080b0010280d0403248050740d074800084c01c0d103608540c66450300e0030b228280004141940521729020700c40d200a0501e42c0c41900b001061024020310151403151101c140400c0c0c18026000301c0744806034182515802e1034105000307001c0e45d001c0d04020711800e04880300003841116103444640035a600c41218603200710f0240800160480400070b03101026802000c40009280124a040c0c5110542c0c10384107492802480281042070003c1c402001c0d0b9041c907411000b160707070701411110010012504505402d01600104515000340740300102002070341c0f0480d106001000000e1072085200300c07803101d04c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884750980 1250 884749730 884749741
    0x10e01180603030f030209120102190f0905010c030e040f15060e0607020a06030519091104230c1b1002280c0b0402041404030806040e070305060c03060409050d08060108 74
    0x403a8020b200c06000a0041301c0700340f400c0c51198000300416a001045107601d9800420040c0c2240d00000d070480712107031411004e800307490b00a01444182c070030906040210b00d00e0f0500113060b103c2c45100060400144101c200c0c902c2c0d64a40c0416218540204100028440c503416080f0560f0103000b080c0115100701c4a11140d4500202101c0d402e40c1d02a0450502501e01039007503016040103002585188045801c0d0748040f5a01d12440329200c0c0581c08200059100b030007400215008003a2010501c80c50b24400b4092090507880384d5048221a4a010fa441e5001e620200d02d81c4d980c1c40e44007c1c58081c2d11164900d0801c2034010f0190301c2800100504440c90091044075005660313101100850210fa0425001c00ca2484030b15501c2400504045122250391104511105048800710046800c01c01400980d040610034600100d10a4006190700e50940d2142d542d00d89004021000407040000005c11545664200c41d48007640f00c0d08071001c040001d2030141c0081e84c1280d00c0d0b800100040001117 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884752230 1250 884750980 884751029
    0x12020304050703021f05120901020f19081501020a021012060b0d06060f080a1109130e07081b130e030c03071109060d0b04030306030c0f03021c0503160507030506010e01 74
    0x240d205441ba240ba200d50000ca100c0ba8840007021507007255428024803e001c1041002841070b0382c4509805d00f001e20f60903070040c0142c1409801000700d0345001000c0c0d216640c0018a50140c203030101d43d46540d1840288084802c240d0b080d490742d2541e130800000140603404c040280c5404481c584040c045242c46440880b252203032044048001590000400c140e10300c15130142c0750207140d03150700c2850028550003082e040304000340c4c1000d00d03640d0388c4103c10605605200d004003801000014084d61110741d10501004004035403000d1088070f000b02025151895940324401441c036100607a0b0b11a100b610400d51250810607042d5070f106001c00280ca00c030b150111b0590702c10b07130b0010040302c28000140c4a03288811001041182490354480000c408580b0b80d224030001005072006403004d050840c414000706100542c140c00c4502c00800308600010300c0071003902d1070f121200c3c1c0c22011f08920303414920b20701042d941c00582940100c1c6c0c0042121070340b00d0303007407030607910302d1884089008401d40828 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884753480 1250 884752230 884752279
    0x10e160b22120512090d170409060e0915010303090911040e090a020901060f0507120e0307031514041a06030a0812070e0102030c15060109030203010609021e0f04151202030405070302 80
    0x2d5001805e0305c003d40000f00e080700647c03120b00d0702401031424070f03440e0560a001c40744503070040c2602c00003010030081e409000700305139510a40d0040c010120b5524555000e07209880c14000c0241803078403004200c83d0070a15006582c014200001019414140a0303546500ca051003281039018050750350012a01c18000e941001074500c80e035403654130f005515101d004e8224408072a410801007101c0400603a6a8104051000f95000d0720740203c0880607400f420b011108214038109007611010100001f01c0c2d10114000301c403c89084000c1030325650718001900306051000c0c01042d00c800801d03400005010301c2c0c940752003101c176912010074194444005980d40d00030110a400350394005030030f034082c01880011240c0c015006052043c5229180d60000303080d1006500b020303640c990301080724642e007034001e64011140d0b10381001c0d5034900804220400c54a1149000e801408102d0201440c030789445500c1910401d4080a011912800c251600030b40b90071051106134803d4800f030686400941c1200120b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884754730 1250 884753480 884753497
    0x31b0d09060506220b01054f05060714060103030801140108090d0f020f0a0f05060f01030818060708040b03060f0103020c03073008010602010e160b22120512 69
    0x1420701c42c81070885500c041d21110f800181000018441200f4582c116107540b04c8224110b01010051083e84501024289182305d0b80006012070341c03410301420000c003848205880c810341d619582d80200f804d01250030303940c40d10705c44e003544600e2000009143d44a40e481d4181e40030281c400f8428501d20b401181d50070402e6440a0181e0007421095410500030920f0185840b01030055845a420604109090103007202044e602004030800082c10020b0510945134842e41c100f07100c00c0c80707505507116407615004a0420b018003454441d070840107690b4003400c2d1480c036035024004031ba40c0c0d500c2d02e906440d45e4006803580d85c014112510415070303560290080d07400c8031401b40011130400c455512140e03a8507400382c0c1d00a0700458060201c8404021b18940300300d64140d00c0e03e130f0a00c59454014001c2c00c580c903050039034000703400004651090120400414048440c2c0c61002d940f0348914500e41102c4e1490320204000780d0178403410026201c1c0030f05030850301c0d1600034400d68584000c020b2030880300d803050410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884755980 1250 884754730 884754769
    0x6030803070504090b0f0901180b120c0a050d1707050c1c02090a09150213080d1106010e060d0b0c1b06061306080307080c10180b06060a0212031b0d09060506 69
    0x52040d50380e05800d50307080c0c1c481d480020446120900100c0c1101c0c2c4010410352880d00560b203c8122818537081e02d10081406803695811420307a520b40b0b910714401102c005003440c00028a060500c80d042040321400c0c0d00040074055107000e0707942c2c0c000f01e210202504a0140038040001410480c85101e503c0b42a50011003080c551240c0019042c0254441e2212000740e000c440404620b130401000103108000c0e603900d0b0000c20300c04051040d8075241d0305034805594850301100300005911025240240958440c0c00481640c460388026109409042d51140800200c8450409600c0001507440e00441d1d0980710400d0308550301d54008140c407800e01035850268000c00c42c182c0018140741c01000e00c0500001a00d484000c03141c0b80400780c65034003003010058528900d600b001e01903440b020640000d022a40341d40307405803410020f5200d000c070038911540244040300244403458819200303880304040091499030355100420400c001e02c00d840e01910814074210000c0c2090522641c03841c5507202000f07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884757230 1250 884755980 884755999
    0x40e2a072d060f0f0f0b0a080d0c030305060409050d0f181a210c04030213140f040809030a2303040506180f0901060206160207061d0406030803070504090b0f 69
    0x2c84a50140880341d0480400c00e5070740d049043c0401852142c0450516400b01c007046072204207003000110845600088000d802c550070510300380c5e400c00c0078054a9076040c1008200d540c1c840e4005001050041d1000d0424041c031110200e600c1d42c0300204001e90300306600c407000d9065044a80380c0e10300185029800003500c500000102d25415100540309481d00c40114031b41c11a107522061180c240182d070400211030000c0b80c2401149460020104106408031003000030100492480d00c14250241c43c04c0c0c800d0018030f002c1424031206804407214203002a0860b4000000c5241c00700e00c1d03903c00c02965031380340b8050034000742003040402210110303240203020504100b901a00380c3c3c900c102170240c4036800214960004030a4513042c41c294000d080a07005807040d0720304825103030180b18003000702034110b4000240038006a5049280d0b1401c0050f074580741d492126101010500801c00741d08064140c0c0d83c04403c025900c5ea0110040c0705035048100305200b10000203081c005c0b260318401d00030368482c1e00007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884758480 1250 884757230 884757233
    0x14030403151b1e080405030c0a0c03050708010c050301050607060f05100f0b03042a080114040b0717011202010c05030d06050315040c06080405010902041505040b03030c03040e2a072d 80
    0x894640d03400070301901c151f81c0748c41c1e80001054903026a8140c00c441d500c98003001003003030045c180b00480040100320000e12510078922402007462005001d0b00e885886c01141001c1846481e6200c01402041c5440410050410481c2d11210401e5481110441806c3d440c0201d411207401c002e80b40560361091030640245083c02542d0340c00401800450310a0791403072000500c0900900070700c0704100170140d87c100c050a180c1026010034800030400b40900c0008011324400d20b140d2030481341100d0030120400c41c14152032004031981c480c8480050424070010440d00c8070440f50f5401002254011821180199800080c070f119154080f02c1c003401e0034619002c01c001f0140184038066001e842140001000840d0340d0000d8200c0d80607000c40304180034415810300c180c0c2010710030180302c20001c41c020341c00c2400031041c1554900c903074003582a04618183c0802d03003a4291040440601030340c1003094440709005041c0c03802640068200b41c2d040307600c0e003014a6086110240b01c9204903d4044051500701c002e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884759730 1250 884758480 884758487
    0x150903150718030f03110a02130c0512150f0108160c020105090402070c0e0604180813030b010603050901150302010e0108180f010603050d02031614030403151b1e 71
    0xe1810052060300200d40030310b080190041c502840c1304102505031a001401c2c002d04034a90151005220391215541d032000d03940d1910180000303440800c000c605d1040c8108221404c2c020112501d101d0308051080c4150044d03203248020b000300e8155041b032107205103007004450849003514000315a01d05503140c03d103024891003c1c41d8410f4018140940740060140210f41241c0c440c0c041501d080340d403040b060012400855005400c200b044030305024440309890103038100c14400000903c0e0ba1000a01007690101a41c1e60070001c1d81c104441e00d4956a4602c0058058981110188031075442c0a4050002c3c201080b542c6040c0ca404ac2c3d500c0d841000040015101c0f100040c0182c080002c20107040d50840745c04201580841c0c846000211741180703980b5099203050b01c445500c00075074105001c403882d489003140322a803900c0d82028000c140d03014128803582c194070560304050000f0307040081a29002c00c003a00100c0d4203d81400c4101d2540240f40c100b01c8a1030310800c00c854005030b040d0a4004402d22 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884760980 1250 884759730 884759773
    0x1525060b09071d011b1a07090f0e09120c03030a2306040b010c12111006031121121c0902030304231017010801050c04062007090b150903 60
    0x8060406982d0180b0340d8010381703203600e12244102d0710043d00302201400310907080c152540141c120b09100c1165410160750803c1840203003c0c59588001c07020010b0000141001001e460303803090b45125595007046104c0075100d500880f850301401d81411000c0041414040650345001c01c2d2124001d540d4031100100006003941a04040c10054001007006c0400c1c8107004003003142000c1e445440707505941080301c904081c40000401c442c1c918042040003c51000c403416a03180c9011144450380410700307807158400c142c801c0001d81803446080315880c1090943c0005102801d5003aa140700c1e04030382810345405450401c20025019041407204000413016071500b003142d0340e00e4406801e01d040c00c81001c41d401480c0041500002282410203113003640d0041201405480b03103500911052400c016500e60500c03c2d0b10903001000070042c1e2400c1200031807440c03c02204040401d4030742d150760310f40441d07010745407005107a40f20704082c204145000642808580d01550041c018040c5071a21503640d000660 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884762230 1250 884760980 884761037
    0x26030703051c0e0d020120030a090804030f030815040b010c02090a0609090b01050405090303090c06031008030307080108071d041e08030405060919030804021525060b0907 75
    0x45446a60001500300f8000c030401d036189100184504c0c95003807402401c1d240c0c0c1c603144038003651940414400502c05074003125400728010101052244d010b1510b003941d482035500247c015550000078008042c0d1114400340201c3e00310040e2000c1d4102c0704204003c40f070a03c40c5442c045105040088018100440101e078445012080007c0d2643d94894a000b0740b00406000c85e07960a0010061042c0c4c07419201e8280c1202c000c400540c11440c20f00c16003691621100021446808080b00003969103200250301c0d0050301c503000c1926100e0805c0720001e4001502801100a03500841e04d010030b60110080d03c22034104d0724150700c140305440d9030310341e6500c44040c0c0d1003030f00d480b006010249004c07038000002540510300c01d6009041501d400c21510b4145400f021786100105102c1c0d000502095100204175003103038044500701c90802c00c4030840c682600c5100c4000308411001c0401d0710041e210218241c076502d0203904140318884061041001e000411100040410041049200e00320b064032801142c55 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884763480 1250 884762230 884762257
    0x1e030304150608070611010c030501120602090d20013513020402040308041a03190513060e0a02130e03040317090a09061d040201021b04180b012603070305 68
    0x50300c0f030312031600700412604200d01050b007400156058100034459442c503030308035140400055050035a40050710040702c1000d80003903008502401c1e580d031000b041e0043c05502407250380070302d00040b6400c1c8819007820f4069011030004000f1905220140100b0341010600b0480100c10600701c40580700480005054030702865a41c814090040e1158070041c0060f5009080c0141c80c0c1e0f00d4082c0c0c559801600c2c1d04c10626594040c0309111458003200180c807141c200303000300400c25035100000048450644000074044504064100041240c08200d01e4406070003540c0054a103c20001010182c0d218001541034aa1040208001103602c00c81c0d10844440000501490000a80c000441e040c042d904441e030203035542c0a04002c21a131144545649e10588001416180380c84d40010b91911243c851801681031110307160102547c41d50301c24100d24925000401c04912103051251240401340500c56042c0323010f00c1350a04a40c402d06003420050b070118015883e102ca641d4045a803a0800c0303042c203190 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884764730 1250 884763480 884763491
    0xf0203010e150901110307030b0d0c0608150103050114122a100c110411041a0a0f02070e06130e010c03140606090a0b0a090302060c0705031e03030415 66
    0x5940a004200000580c00c0c000c0402d804101c826448a00020340001c100da8982080b0180844808050700d92090141c10000b80200b4080702080e104403070410010800b074000000403400c990000320f80d6010b150800d4440040307100381d10055003124402c1c06441e84820300111040c2c0d0610b000802446501980810340b06c00301c1c40d000b108109010005c6064000e03140b078548109443c200701da5030106601c168580240032102c3c944511407007443c00100e19000396141c0d03034180c06030202181100c0080010002da000c081c40610204521034000054142c0015680742d03a08010313610005821b419540030415180c0d0366240c00701000008804c000e2030500581c0c80740d51a600b41002886156681c1d5025103010a2101c3e546011069050b0b004040510590080c001c8150648a00e03e000e4152000c100340303c0e507658820392050302e182520740d0000b0340c40100003075000d83c582e101189220403600107804440200b4407030f48a80e49046040c129040390f541c0103000140208282c0c00200c0c80e1000e81d80c400260 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884765980 1250 884764730 884764733
    0x5030306090a090f0c1e21050106050a081b0f030706050901091d090106170d0c0c0b04120c091802131d01021809061f0e0d0606180c050a03090f 63
    0x4403213100c0600392445c445101d030401010ba0203401c1d0724259031001d000300520302c0c10302c00d03003094800351110001c40c41e01c0d1808051040003000d510060190000070f0a0189140d03440d494659600e00c19a01103d881154a112a070b0f541040203104e080000003c02422206081080c00c03078958006201d0b240c10020040300000d50407210b905003454111100e104040c0ca807400e90710540c03d4401c079a101c285800c0e500500802d0782e05c00402c0103080511a841c1440c0410312604000c80c000100f500a40410b8400050001c6d8104407090203e4440784115480d98025607251061401c84090040905e02c60110600c41001407815128030300396035090070800a40940b106482c00e5140c024859007800f0350707500003883e5611940d403541510b0a44800c5808510516142001c0780e02070700c820240f5840d400340303140141c452502030000c040803c1e001400c3c40d03151450508112014001e14030940ca05008000b9510007440401c0c010b036513140150340c580e1450585201c000711700500c4404802d548070191280e842c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884767230 1250 884765980 884765993
    0x209040c030c09050a1805190f0b01121203060305100b04021207030b03010b09010b120730050c180609031f060504061e09020d0b0303130603110705030306090a09 71
    0x8090075040d0340c0010b191809414040469a40c4c5001e0052a2108060140020800186000240400341c0481300c0c0c000b49203007024209184403070062410208800114040ca4101005115a030050074052000c00800d0f503b5800c0321250300020741a50018240c2072410091500410f0000c10058030040c5403000e0b00c280001c608200b918450000307600c6940d414558907003405111401002143c01c03036410351518184001d01e11901c14a92003140755040000c07011402400d00761064000400701d401000c51901000d90703190b203800d0140008614042c08030390089030702c1050f1811700511071604011150501c00304172554008880999040c880d103403040c10b0b1800c0c1d11408248011100d0804a82c41d824001088140c5915400c242241940c3e90403500414042d680c548040b9114500d0040e41d03259842d06403406071031900f500301e4045c40005803818001d480e81014500300c0f0a2507034200045240610807116501c43c030380d4054816441480412620310f005c06090350000e98040b03000a0702c01a82e900c09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884768480 1250 884767230 884767253
    0x8280903031e0b06180102031b06070f050a0c0f020303091306050414060907080a090206030f07080a0e0a0311070f0b1b0111040e07020a06110c070f0605070209040c03 73
    0x44000a440701e0b800380380d440c0010744400780101540c00901c40c510754600880d01d94040e405900d100201048001c090590003802260425001c03004a002084114101d50b6900c01083c0c1c1d00354001403515030a15005480b41064541081c4580e50381891000a5200e0709909c00c03c91000b40d9050000b00b150300201d035a000b01011101c0200306000c150b0354034042c100b200b01c80f5a1403000460b40c980d9000c210040d0394051030140d129900d814400425118245c010300145131281000350803120010038020070051002d0303c14807c0c482942c680f80c141e6188204031b01030350400c001d800c89591104600e0310000303001c0c0340c4c11541180d005040b50380302c5a03100c0d60410a40c50561021503400400602e6800303080074034148501000343c45009202841c118007050041d445141305480c0180000c20103e040d0610901059000c29000b90092080101004c0c0222442d4041000fa0405200e1400c00091250612003990f00303d0710180c64440c102080354003400400390004108490350301c02c01c200880060b2403441e00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884769730 1250 884768480 884768483
    0xc082a0106080c030604021c050106150305060f010c0b1b09060301090c180e16020c0d060605012a110a030611030f010608041722032a06082809 63
    0xc101e00749482485810003000790b126a000b41c01c541d003000050703252014454074404c002903d1514030a490b0405900410554029282d064104410020341c641c1c59000035000d044122500c00f04000c1c568015910800d00140013010240c40d10002103062010746040d250314050415514034010301d501c0019070301d9100f40c0080110720f43d030300b90002c221a80308180303050060001d86407a608a0034984004252000100580303850380100b0911203025100744055075171101702600702c50701ea669030300d031180c060301c40e034001d0500007903003540490300c5080f05010400c0a140031008070500c11080e511340710a01c1c1e51030078a0b250010503000d40000056482c0c8280152205008000c64a074103080ac8007002031541a4028002c1090480601000c0340740400900008078407003410550f81e80c45800070100000c01c08141701c01079646030000000340012940900640390380d0381c1e41c18410f07120300c0c1302007013003440d00c1d000d49400070390341c071000a180c031300e000c1c030140035501c0700720062400c0008004a0b00255000d1b00030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884770980 1250 884769730 884769733
    0x70c05030607210627060f1212030204050306100812070b060906040b1302030405060c0a0e0d020415090902030709020a0207090e0c100e0108010504060b25300305070c082a 75
    0x546190400480c410302c1b006d094a0000070289078648441045211010b4801504c00f40301c0c4401492018066412200200f5021302940d242d1324041c051405038107030070310411406004601e031900f001800c20044035402680220b04000f25101c010034132020303010080003e6000356840289001c10b580e0100106596141d0300f90140e0340e407501c1d18110741071040207041e0101c0040144032200300d00d50800b0103012001000d642081d00040c0f03a0000802804002030701010742841078501251209040d004540a64020307411920200d6883c7d05103000c91148800c0000113801c189001c1c82030301c0c4aa0000d54240e80c559049410210108000401c12012400100302162001c1040d1b2803958100a8442c01040100c0d030400c0703454074140d000b18551003918242105504000080105c90001001013024240c026541240c44280d0050f900101201c0300403241d0b005250140c50301082e4404c4c091148115426910003011b85910b41e554551a003049545c004103c000d01e114654030a06405028a038101560 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884772230 1250 884770980 884771039
    0x803070b04110118030303020c0c060a05040e060904020a05130b13050f06120d2d020a03021605030d0302090f042a034805070c050306072106 62
    0x2e09240c0c181c0401d4442810b122480400040301d5000c84030700c1c030440350982000350f6500410074849090618410340c55500c400b01003510040207a00c40d02800941d030640c590f42009840c0c1c0c004019400c0000c440c001e500c11b003061010f01241c28805084415084003030300114140c010100025180d11000d044011002e41e580704000480001140580d0448070607281415100c3c0c48407c26600e900b0084400014080007282d019003040e00b0070191404541e4102c04c50129102e2808001d48650b2030807001d90042c401c405c0d0102c2030048034041201204c800a00406080e0550300d0190701135000802d1065001c13054100c0c5040b19100d90080e400001005181003088a440e5000c036080c5a54510501341018600280e0066a4955613580c0700769025401c0303c4080c0c03200040381c18000ba005003801355400031401082e82170880d0071001520072144a40b095036081905c9100385941c540c0c0032203100e800103000c0014003860420030400108484204e4070301140b8980c0380c912001c0303000750403d03d80c0c00c01d06004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884773480 1250 884772230 884772233
    0xc1617070c06110604140c22060b040f060f260f07020c0d11120703030f0915170601050405031609050a0209031b0301021201060305040203010e07180f02040803070b04 73
    0x29500a001e040c2043c40701028821030080c0c1c0d0ba04010401081b02c104512050460202040043d03002e880082c07401c5100c2c40303188500c00354030110055403900720b0700300b0341d011501003110415030302034407070b4128440004d9150000c21a100d84900b024042400038048911804201b52803503000c900302100000c0c00300b4140407150b015017410007000c400c1150800150007006540f4440c0c00380071184c1280003c000f4044000c009078110280007001a0075208140d4000101600007102c0603840140791198100140c2d6408100561f2003201032402c0041d00040100d681c01c00c1505020740c010a041c90700f40d0500d07840e4008245030049400f5000c2c900c103031070b0f1010420781d03140b405050fa02c107451b4401981400d8a80021030b942d0004d4400d014450743d41c100b40f4426544095041d01c88070b003031aa601312035550303490b1405801400259021703030083d4280313210b45504420000d4580704982e40d911051115200103880000240410905e040d0a01d40800000409040410143c25001d000b080c005080d81403031b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884774730 1250 884773480 884773493
    0x20d06061d03070b0d0e070b07050708060609010b0304080a030615033312051009120816020c0f04020d14070908010e1e0f01061410030b090c161707 65
    0xc225003248650300c0000240b010304d500c0403d03071380410520400400e401e1a0000303a28200802e03904620048880400e4a20030311100050050403210103c05032035150b01d850060181c501c2090140300c068000130800f060004000c100103241e078a02c94074000a0a03922000543e2040c03d4050b00c00000075121406020603d194213aa8110441070342c09203000101d419800c1c550a0724548240e11105d91b203001f0690a0150070707c1401d0100406c59800c011a8506180080340e13074540500c4400001c600c14001540036002c9a0040d0b1183c100da00240b003201644010001000b10075520b41c0d4005409022503040c074100c82c02030f101c0015059502c1c070001e00e40510024280c0c41d030b50380009026810070085401511000c81c010000d03600d03003c0c0203940340d040c0c04d60082c0340040801000d900c43d032070501c0000d03400c401640c1840203900200d038085001c1407085022010382c0c4034000141d070b004407810041580040140001e01c11501da0501d0b8000100f8941caa00905500780b4060446240c80064050108a907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884775980 1250 884774730 884774777
    0x1082e060302041e0312030507120905011d060601020721050303011805090a0f15290306090d08131a0903090f010306060c021504050409060b0a12080a050d020d0606 72
    0x30f2900f034130341e21451a221120f0100441320882c042c10750fa0307804180000e2040302c680701030384882c44040c4070325049031401034028600900703000300b4113a0422281e1100680400c04501900d4141c1c01004550700b00000401021014501c4c03814a11b0b81140b00b20006030240040c40c0241082c5810b030b0b14255103a0400c0c019a04000d001c044980c002035180000918180309095403150000741c0d0005000400301918010300d2a1204005640d511071043c0180c40100c000c03050b46810113a044c0c8082e52240300c225940c0c0e200750485400810260b40020305602c40903183d1003482030041c491441c561110003141190400b0540e50200c4a07040040d59031400e040c0083d10b190011400e280c10000d55140c03080041c92520260b100911a41044c001c10015181d14003c3d00c1c0542030040040200451501d0136600130565400030b03d0040c00401d00024800e0316843c1d14032a4660029511850320f0301d01d8400b296594018070b9074030500c40e803e100034100fa1460307201c0d400c080c04003601e03518070503000903011010058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884777230 1250 884775980 884776019
    0xa0e071518150507080a0509120309102109020d02060309240f130507030203100204050901090603020a1505042301030509161a04080a060501050a08010b01082e06030204 74
    0x1c800d081c1902d080d030310200302c0b2070280d000748070180c8500000d142120148107910f000703a031090021400c450360b003034040001c0c1100c1c00122032546200d90401410349210714000c02d100040d07400c00c480903c0c030f03c0305604500f928503c0180009841c0403150300080030b940042d039060406a11501c4025850302141c3c0c0320036840d016401d1403518600d0b221005a040410041c070140c13050a40466040030050100726810103180d0003000d86c0d040c0c1c0d130a421280700035001481a144a00f01540c000151000303148503040990343c001c2c1c241b15440b8108012104510030000c0c020007044010000007a0000f0340c50700710010004440c1d0a81a0f017640d02d0001400d55074003601d0707640e20341c200402c40e41c4042c0d03540110504441c406440b840c6800155004088140100d51143e451805401112010040142d1110781a14000ca92102095841d03100041c00c0312480440140450800804036100c0355107449889015811504840f041150700c1181ea0b080005a50244020a8000c1014800c0301a031055131100d52 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884778480 1250 884777230 884777249
    0xf06070c05030703111f05070e01140703053006150c0d0f030e0f0c01020124050607170a2d0e0402070303110f070c0e0f0a0e071518 58
    0x801d4440680301c0c0f0645200401340030344000e0070905201e041c01a0502c00a040241c0d0451000160f4207a002d80b01c110fa07002e00207840088684502e600074409030403c0c800c40c10500d410568541c1d005e941d00e901c2100703c041d21284555034a020380c00c000c07010b03208504c01004850703984c1c141501401114846030308200400c40040c09050503e00002030003030809030081c42d000c442061451020340003028201040d0455001769900d0121403000040d0502d0401000e0740200328621161000e110003c0100000801798815911300704030a01c0c1a50107041c03103074001e07a0400103896903000d0f02031059009001e060046115803140181c0f924820b05c007104440341101c40300c0000c0303d00b8800241507100b03500000384a40c1e408031b9450185407103131f40524200c2d8025492240d541c0350740228801c41d80c01141c012500040d10b60300100d1541c41c1c080300b06014034090481c000c10394540d031041001604030400503546a214035000040c60b04005e10244401d10016101e031809821603a4100d040d00c0301d56048000c06 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884779730 1250 884778480 884778497
    0x80706030c0e030a02040c031107031707030227010302040510030b1f122f040e090d08061c120e2103072a180e0106030521070c080f0607 60
    0x2a42c40c081204c410711035040b14001000e0040030b000307400404008901c5102d00902055000c10507403c80f040740089048281d8080e09650341c1c007c00c030107074447c0040c000485024152501c00c0d40840e400217a0000300141070160070b1585030b0f070100300c1140e620810100041c0d21860f262840341080c0200038004080038444000d030141c2c00c00c015182d03241c03555265034000e0b0340705510016500313603c0070107003900b040c40700507541425a0a10800c558101d400380002210040000c40c02d4024000341948079200f03076451327058555403403d080055500141110702c0742803075400010b00c0080c65001342c1d2aa4120143c4444080310401002d022180c1c080d02c141c18460001140390001c404000030541d10004e41c045020040d910320010345403850007124940c0c800ba2a0080d9011400141840d172440d1400d241c00d10030000c075141c444140f42a47c10780d02c000b405d02e401041e114400b507281011141c081000521070355240501c99a5081b002000662181641d0741040a0306e50184009004160f00311106182100c034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884780980 1250 884779730 884779757
    0x20d0b010f0503160507020301051612020a1b0201020a14011e0e060a150305010e0102030a0b19090f061e050a1d150d02060c1501060219200604080706030c 68
    0x18030003e0100d079041e80c444100714107131030700c44c004655440c0da001e00203114030b06003428070b403400e440708100d44000b08070240300b0404081124420f807000084a83d82e00b0340c2250b005640003805c414090000c0c0c0c11405100707000000b0038429104d40c05400f040b50000a51210000074a100821040d007400c220380d810100f1080e40440006050b40d0081b0180c100081e164001c209081040c188d9680000d040c2e5080c007401c4d050002066015601c80c0d0080c120a01480280e0003c02004405e0440540d5038501020001e01c00760b05968851401c0d13041108000031681d0b240c000c9201401c9100a415800100c800014000350920304020300c0200a400c50410103080c00d4540d4007040c120003840701d8001901812114a07d644d034403c403c05a0350081c2c1195658802000e000c0e80701c081207022041c01151002c00012150b100061110f101400340d4200b801e804400d9440c081d812803001d12aa0a064050f900320b8659078606000308020540704004001452510202078242c600a55000050140c1c0558044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884782230 1250 884780980 884780987
    0x1110304080c0609030109121706060f03070e040609140412090e13060b060d0525120b0a0e0c0c0607090b3009010e07050303070c12080d0906020d0b010f 67
    0x106400c03c4454903210b01095000c01d004101c900e00c060a8202000c01509601e50800d00700c601801c04400704030041d9441e40c042c0002031040c034158694100c01007000682c51340c482d070801481c00d40d000744049440d03a0b079800c80c1002c0d0b441a07040c4804045036103040c8001c003e000d40f50128510300c2820f2450603c0e1901c0310007914440c00401543d01c000212016200b080074079030020b09111402032019849404420108000317000c2180d40361010f001402c4080040301ca5580c21812903e860741d500301c94601c410020034003802140303580300c4c7c12080881d40443c941d4a01001c440c425441401391a8441d9411180c052608002030042c0003801001d50043c00b03640c21400441e2800f2007840f2582c6c00700031302003140e04070700c0380601039452200d010700080c0405010190800700c0004018000c6071200d9450f0300c101901c0307104451004040b08686281001210401548400c915004041280c14400700290043c00c0c1c482510381126050350001d40030702031070014418014211070030300e0072148d04480c091024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884783480 1250 884782230 884782243
    0x5060306040b100f090c020c03060f0a11130603020a0f260405031209030c010c08061e0607140607111f020306040609061701200a0f111b0111030408 65
    0x54885030b120400503414480640d0354034024800a11401040c69a0710b14034001401c500781000c00502030096a5155071800151041c0140c80070489161140c46840e0680000d210000b001c1000300402d20020890f4290090b046000b000c0c181c40c0560760300d001e0702c1c0040c00d000e00c03456a9402c2c0440086480f10b100786ca4011520100030a403400d0585403200d003401490742c000e0300044042c2c81c444108001032500048003505060788004024020008418400d45400404496254103c10303442c80716444d00314015a019109400a0503803490005a40c0714002102c01d0301c4100889544540c061100090344101c100440650510107401c00040a15aa648a0a489001d4080a50044007140e4180d9456000c2130041a030070800b0811140e41d40c4e8501c80f000048080320b450303546403840b5815083c8401e40f4143c0203030303002d0a51070314200320560207846c003401c02044c403020170141e82c0203000081410007503907100d040c0031132146000e050028001481d9400da02a0500203030818401081a08070000c0c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884784730 1250 884783480 884783483
    0x41e0305190c02090907050102070609080c0607082106191409060a1e14010302030103031202071505090a1119051e0402030c0a09061b020613080d02031c0506030604 72
    0x40c81d1880c030782070100c407244100c54020358080062005c0c80410b42001640000b128000e80a03036510983c1c070201565000c00300d01c20039405402c040d624060394a0010010402ea1344125000e1f03041c10510180410340200c44006810703910241000c0c8101c510f02345d890111b9018001501c5800c0c50300345030248058030f07900c10b4802d00910000000c11419076481c0e84000c040d01303c80982c40036400c014002c0390308211042c8501b0b9000c01c01706841d00d1465209000300c80c140c0e40c050f160b045035800b40301d0b0740c50001e502280c1e0646501e1200340004070204250700400d809403401c070000b04010075803070911403010b00304840207621401d01d01d440405d1960b1040b036000104d50003254020301d0030311030f10040390707192a0707150800741d00c41c0c40001000214107a000207001d40100c02c1d640c0754412505c600041d21300400002c040c00700d14403040041c43c010303d00540108000c800480e0319040c1d0658070107030715140814141000c0050303000898420021096101c0b605060820740b10148154185500843c0d20b82c1c2c0d01500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884785980 1250 884784730 884784757
    0x4030515101707032001080a060303050301180b0a1d060109032a0801020a08040b01080610170a0f03030506040b0d0b0604110f121008010507023012041e0305 69
    0x80c1e802d100e40a00045005641120101e41103032120f210794505040e2020355140811124008504021058480c20003034075031585030580755900b004000204c034188007551507038564403401d10b80b90585605140c0d074010040600c0808000c881c0710100003000c04010308490421503d07050070000309032501503020080b13a80203040044c42e907110118504000305d50b0420f80413580001245146642e2240c01c45100c2c1c1d01404020b0380e10390302c03a403500391501c0341a180c00f00501c018010070f101c1112800210303425068904103d0b1a0308000395100e14028903540350503130119039504100910ba040901910b0402001250f0280d07400d0210769540384503081c0648540c0c02950388464400058000c0c0d4125103201483c0341c40d1035280c04001c01e4000360404100c1d4144602080c0c540001912038050060fa80101c050790080d0816030340c00100c045464004505103152415040c0b10254110907007001003a02ca9044c140c041d20501e8681401c81d620004128140d188510403015117021a9000c015200311818816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884787230 1250 884785980 884786009
    0x9041202030702041805010506031504080a0e091e0117030f0c010908121e060f040b0a090c050c070803040f0603051306020c0a11030610290a050403051510 68
    0x84124550302500398000c1d0400e02c0e248840c0c40240c480e8491640e400e1042000740484e540744c0082c19191000903001007943d100c0b00300800e0001d01500301a001c3d842c07641c5030425002c280c141c0001d0900b14250380c2a8906410b040600c0740c14008074002c00d0141001c01141700940c44440680380c2c2c0e9204e451401714030728070040f804406001081d0405201a5045066942c0712801c10038035085401080e501003290341d09440e5100c50001144402510500d4000d0401500c50030510500026060300e03040d03564001c11030a0040f4985004d41701e1420b41c240950344280d2640510f41c000d0b0700d0600c0e2500005403582c0700303203c01c10018000811038419a00300307240110b001c0c2ca40e64003501c280c40c0ca503500140304e44e00109444e509445c000681d0000540a005070311800400001416203400c0107694500300009500f0040c00441e42e0407004c000400260100001c1549281041200302d801016000c000100300190400522408101140003421a4114a0a41c0c00c20008100104801c1e11801c941c014200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884788480 1250 884787230 884787263
    0xe01110a0c05010b0d0503130510050405131d2104050901180603051b040b010c0b0a1a04090b06090906070f1202130b0307090b12061507140c040606020105060904 71
    0x4e40060b400b46001410a0130300580c1d03403034910f8880e0010403510704090b0440b800001c40d440d00a0780006140103d881d440d260608080a001d48080708291012025442d04080c080c400d0a048201024009c20800fa004113200c010740d4044c0d15030283d030b065920305000d0005015a9a4802e06541154060a014081b0704024096180608086e03840602240140205c04440500003000781c0241c070412202006010340c00d10041d40c01200c000b0014090521482c0080e80440e03150b03000d01d0f2004444008180140851400039090702c28461003160300402c0710007072088605010258540240302e180203030103607103000c5500800c0c42c0290b40e04c1700c0420101c098441c440d48031a030704842c800d2035110303030340a04035440c0c40561001c1c1d0702c1035a9000016041020010b040c20041c0c0941d020050590406881030b2a40020041c2d5a004851520340604007001018000b5280908143c10401c1c10005817101c114900100400c030b4440303074030003029a4107000410000750344030180154443d42c440020100c041c10b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884789730 1250 884788480 884788483
    0x301021c0203040201090b040f0f0e13060b010903061508060702030f070b101707051c050319050c0d08010321020d08041407140307060302091509030a080414040e01110a0c05 76
    0x847d0700900c01c0303030300005001c10001698140f05013620707003402001e07510a996a01504c00030200311020465076004041403400503000d6080126504c070705142503c035281d1a5114031b4100e50b1454451403c83e002c41030108a8908240000350380b00003140051170030510801007540c258800d1400040c120842400010412250300f429a03004d0000914125281d1040184455071900103018252040d10102d212028400e05001c04150165218000e5410000c45a80c82c0b220650003003400b0341480424006022039113810440320009503203c1c1da5a000710352440c01d144070810b000038a01c480210700d100f0b10044082d000140d01484c01d070240fa080c90150348500300240c07413113074940036562070b80103188000401489290107103440c08030840030f0b511641c0c4d98030b0041c0c0882c851012960f404c8415011100f051040c001f01410b200500034013580c0070485250743d555410341c4542c00c040c080d40103110300128a42850f00c15070b0540c0c1d042c2d00080011280884201815020364001c50040103043c45400c800c0020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884790980 1250 884789730 884789747
    0xb0406020d0216061109060a0302130302030a0309031527170a0c0b0f0405071a040801023910091a07090510051c0b1207140a050301021c0203040201 65
    0x10030301c02c41d200c10400c0389620041c5148001030702d2140c208600500d8002501c001c5644502c80202181d02e80841c0c40d4054000e03420000c030100398404400f0002016807002d200c0e0310341d805e11a6031000815421440c008428803003107900000300c145003210806220542407a0b654003810500080b6400d41403d241480d004042d9241030b62120202161f10003182d40c1203484c1c7c2009a104141c03051041e075034004071120585040314003508d242e2210000f0401140c1e0554080300d1a5880da90080ca09510344139000e0a990010001d4030b10101d564003c01103c807800c05540c070794152031030303180030703800000034801640ca800c2449148005030752004e0a10401503050200e04103168501420460b500c0c1c40300c0080d201481500c200e40c001d2544404059109110f0803c80d02c101e40f1300000e0940b581c0070540140000c00f40701540c0ca400020340f01050340d00c0b030301c00c21a903001880b5402c200c032847c1d80941c0c00e00601300600c3e0b00ca0760080e070040c0300705810304e13503466000902c69500000040e1640e4941c00101c56405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884792230 1250 884790980 884790997
    0xc031706030c0d05070f090b06070308100e0405100c020f0709051302040603050d030c021612082101050301110702030c06071106041206060e04030503192403051212040b040602 77
    0x83d20303242a00704001c0085200300031254241c0c00545229a6494281d00352040f11722201e61003001044908002801076a045d9000b4036540c601007980c030b8a5003005201c21500f40d4003900c031030388200260040f440350707806041301c502d400303101078209102e0032400e01c1c1e5100b8490262510050310707580002c014500380324002c3c50b007540082c400c0c40055130302e090517903c806070904540700203401e1203806511903000150780040700c4029100c00075010b1034082d9240080b05070410450310701c50300304a502c0300c40f0b03141172009543ea40d000c0700b144000c0d49040304040c02c403a5103800189007043d050292501680d804070707150200650940745642c0d600414948003803a40c6140f1001c0c0e50008010401088814400344034489103845124104816a164881102003560444005000540801c000b07500447c0000e10030107820840500410285043c0301040240f0522411036282420008420814080100070b00b411503803141d10140e00e404132a000c201028180240064082291400441c04115a9504490001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884793480 1250 884792230 884792239
    0x150912070303020c1002030420060d061e050a06050a0c1406010303020d0e06090603150406051e0112020a0c080c1f0519060b1b0a0b0f090d0c031706030c 67
    0x44409140c0034000b500060b44c4140b280c803032182200c0b41002c11b48201ca014580004413000c14014000f40074000c0404002e0050f00450300b4444299158094014400905451895601d94100d80c45611400040552000b44208180d4800f088141d130010201e50751040c1c12b25200307018503058145161400c04034a40d415552290500001c01c1c1030340400c092a10307102d16a1100610640c100802c0154060700c141d0985c0804104017107180040c0c845181400580090710114450b6070b1680000d410425400c1c201c02054424841e0321419030784218414004040e400d42181002c600c9200100b503a8003c0b50001c000300000210050b0350b81d0f0412010b1071101c52200b1101d014080700e800340c00500350a131074102644401a141d00d0b82c6031500d00505d03003581c403200905810403031007010110744c03020340b882030380120700402d0003000200b07030038124491051110043c142ea07181401011a4034000e59044d083c400c1210501942c80020b5201c440890407001502100925480360310001e410b01410300080d5070301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884794730 1250 884793480 884793487
    0x60f040e0f0f0105010e1510030c11010e03041403071a0703180f0f06032306041103041a1b0304020d030525150908120405030405060f0c060117150912 66
    0x8009054000700c5c16500b0744c55803001030f5200e0303013500e070304101c604d5034455844141d014074104114481d0740701d010590401c1c41c001001c1d010540c445821503800711384c80c044503040000c0500490a0b00880c9440d40c1d241500200071075454040607032200036040b801c0002e04000041c10300e0034103100700303074074803444040a01081c002070b03907948208e1117071680d40304840c14149800d0000400d180a03100d911100c280581c5042e0034403901190092043c5002402e642d4081d03640c00d00081c1c0d09644801542c400d0b842003001d041080c549000c2c01c008140010085036001c080444004020740108040d20f0300240c0c1030300d555903c12214642910180640c03083c0814a2240d101061040b508440d41115400e011320030301d0b150a005001204151805c1150203880103d041140480000c608248540c2c01030103102901d06058035800011312690181c100410f2200020071b540f1510710302404110300420864000806120040c640c8540707d00038850096042540e00e4006266442c040c41030036801c1c9203103030116a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884795980 1250 884794730 884794753
    0x10603060302090601170a050606160b0604180f0b091c05071407080c06090604270605040b010e010c05120c0a0303180f0f050102041206091a060f040e0f 67
    0x2406a4442a80309600300b50201c1c000c5d501564039050b00b045040403d031060390701c544450004c1c21001d098250009000c00000b60074200d520400c0251a11039840c050303182c10f1a808020030b9076120840401c541d00101d04030000100c1c060243c81c86150300c0803800c0b4195460f800e0030350412608401184604201d03401c2e15061560290040c4a06803044036503003469011a12019902c4d60300d80a200c0156200840007c070926141c4080d10b01c1c0e82008181510f042d45aa401e03041d0b02400214481c07141d003502d900041290601d006d00809020207440800449407140002494024840383c0f00b0705101e21145500300340701c814409005d036843c981c0c0001d41c0d1105207011065036240c040e04141c0004e441c01c6e13016100c00c04c5a088114109400800c44910b07850152100d42104142c1c00c01150999420800020000081101401c415015540000b40c0d00114140300440050340010340ca0048813010800c5802d0703842800b01000303410151800900204d003c2d22092610300a911200601d2091180340203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884797230 1250 884795980 884795987
    0x30a030b031b22020c10060303020f030f040e150d2a0e040b100e0c0d0c0320160b13020102010e0a1a27010b0102071409130203150106 59
    0x40c49100c1a0700720341030060080016034403005500d1569a114840003868098030070510390401c58009100401460f001098106500d0b21582d502c59000303850300c03000200181030301804120441407410f800355162002d860007440d0f15100c0c1d8042c5100008103e1b010500540c0e10b500d08802c440801380c15030040310440d00340034180c1d190398002102d00134200d005440756448200c142104560b00100111920b483e15569104c0151000b04035100004011b000080c0c0d80c043c00c02458003900c0d0301c1c115030f0790360a100740c490416a0708030412907081c5130511010191416014990b4100200d401e6040c60f10b414034040a03944228030180041c01e008103035401d108a20608088904040d80300360000c020400d880c41e9056126040403201a15a10032404018441e10213207180d51f42c801201c0601003003100c0b801303007181c2002c414042c036480340b60364440c0d8903441940c0401c44a8081e1040c1d104414a00c400640003800c0c02e240204190054240e9010303280854508003c101c60440200c00400560f40e112031005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884798480 1250 884797230 884797241
    0xc01051b0a05070e09030f09330d1104350115090506150f0703020721120212070809040b120f0105130b01120f02040609060504150605040e0c0c030a03 66
    0x104c04030114003003104500000101e90611003802440e508000000040040320003496403d14448540051191050540844600b40d90034103c03110076150032481000c442220b41001320500b03519000c01c0140300a40640c0b000c403101c039079031441c0d42e030707404421030b010003840d41c81c04100c12803640c00d003e1014103024410418400b501c800a00c104590b0380c2e6a810030800e03c1d40d81d45001c001100800c24000d904210300c0050407807500a00448010399070399800094034400114071841554000c070032003010041c0c0403c2d6102c40c111248020030501d0300c4100c071000b1078850194020011040010040322a858603000030f00f924400829010204808454890700d4240380300000115510348800980d002008150381c0031040d40241e104049682000c079081803030100140c0c1640c17075000012000006a585004940c090844008049003607442d1109101c241c942824a8a4008074408414002281d1000a40d8103e81c0d5107074241020f611804640c03003d902c140d64420301140000503481515a8064205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884799730 1250 884798480 884798489
    0x11401120203151e0603010320030a0809030c010903080306280b0405010810031e03170403050c16030f0b060d15380909030c0610030201140c0c01051b0a0507 69
    0x24515840d40746000011884015100700f85e1000007070006002181803040f1050408c0c9040d210401765203424400203141589403030080307a241a00089002160030140300403540a02c0c00e09101c0c0903581180d6440f0044d0000800c0c00d801110980e0200341c400c41208800e0400b15138a2074800d0302541c0702c1b2803004c0e1a40c0b040c024580816000300126150b800c016000400300d981150500d001c00200514003190305009000580030081802c0c13510182c4603002910130700071803003a11159910103031220014201207116003840c002220610b0100041500f1414410486910507412070306a600d44c0000341c0d00380444400500001107030082d0940c00450703580700d031003808501c0c0c2d8602164110b1002e000008400d08020581d580c40020b0705802d64200b0701c0c04990450700d00020380b070038104611300e01860030504982c0241100320b4100c0070000c0d540c10400c460b0450071844e805074502200c00285964920040d4805070402c00005480012034000c0840d04028200080c241c0340d038a8003904100e55101d070103000303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884800980 1250 884799730 884799739
    0x20f040b091006091a041203050d0218030105090a15091a01090609110703050901120b12210a050412020a0f15020d0e100e04021909080d090e01140112020315 69
    0x104150b40d0401c5d100c2c4d40140030038031a9140600345900f04900fa084648210180079003071100e842ca4040c0350001d01044030543c1c80508110f244e2804150960360040c001e41603d401400c01c0e80e01050721100360f03401120494001041556152520f03800c0c03455500d0301160352010072000441e042e000c9400110403901c0071b20090000b440c0060040e80c25119a10b0000e0105404010310261940a00103426040800b10800100c00803540007040401211409401d10341c0c2001c10424150100e0003505d140c1c1118035400e036401c00101510181042c86140240411041c0781c04400c0119501d8182038030140005800c10005983e641e50ba11010480c0040030f03c5c094014001035940192064900c0703103200c03100824451808456079404da411403061460035401c507800304040e0030707904816100c010750002c999440303031103092900c4c032201d043c01c50075030001d01080b910070000c00c10b02c11402d50310340c19296000145500d024603100180c0300741c41041480b490103400801000501c2210120f0001c1d660001c3d00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884802230 1250 884800980 884800997
    0x50609030a031a010e0d111e190302090c0c100212040b06121b0103020d021b1002090a030803060d02040603030e0f0402030906151512041505090604020f040b091006 72
    0xc8607003c008070f120f0000340029081071540d10a03152035041104414051039010b40da050901c0301055450b143c2c030602e1000c0b5041d100c4010920b0810003104602d41e0400801c00007840d0643e030004140d40005400c0850000d004a000c00612100780111203508170704280c215074807118000d250013502c20484090340c030550f04100043c00c0d420080000b45c0701c892004081c16408064045498040340e03540040c504050382400032901000051001f010103181080c5201c0b107200d48488100d2400d4000900120058010710042807a92030301c104420035a83d0003660f05440342d9800303000c20141d607424080694450b0900b44000107141d0002074841c0c105606550a1100307904c03040c1032005078401903502165590164000440c1461600c0000348800c100030000140c003400c020103116660041490310f80002664424841040700070f08000405441c8200140014a898800a40c40300c0c8010006400b070f00b0308030300030b005658a540c17005503819001081a031413400e0503c0507200c2c003d041d0080d4000710b80c030719 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884803480 1250 884802230 884802251
    0x1c0b030d03092d1e11120a0b0a050f180c0d030e0409140d0c050304030f020607020307092a02030702011206051008061005072d17180109062307050609030a03 69
    0x42003409001c3d0442006580021180c00313002c0010411b541d20840340c0109103c3d000019843c16029000e01400d5001103442d0070002c84142c1140303070182010609010107000003111240114012400c071504642411121031182400e40300c0c0d00301495801c0c0d020740391903210410040c032110342010345c016000403a04190005141519840e01ca0b060140450b0300911013000012004c1d58960b004c64405407502d4200f48466021034541141038121b10383d540e440c1d1580c1761028a00d02107042140d030680d02c16040e8030138002c101039105d102d03c1c2c0b4081d04001e04e000080b0070018039a04004001c1c20060200d2034020828000103102200540c0c41d50f2050350780780c1551f641144180140c4414a410401e41000041c030980c100c0d4141501e6810f400f565242e01d101c0c400459061014680e840040c0c4018a90314520702c4070038001c0d044640945070500c000c0040a00490303078030560604111072106421880000e140a0380f01143c045e01c90010403d00c541d5081024021001c00a445c0300e8070981c5092104d0b061030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884804730 1250 884803480 884803523
    0x2040b1c140c040902030402030a020603100905060a0302060f0d151508100f0b03090a021009060206090115061101063602070b040b041104050106051c0b030d03092d 72
    0x15100b64071100d0341408113200700141c0740d00440d0450720040c1220a10103c96000c2006604210341802d014503003518108036042c01401900c0c2c4c03151044541403084ca08560000300ba601038568404550300001c6600c41130040a5070069840002810041c440195560f10705481007018244000000b40c1002c0450103020001c2171a17400d40b140207a241017154105902c084c0d958000030b1054036244142404400583c6a4408811020704999105041181441c80c06813030705c1c0c00030741500080da24062903409848220403e10b019078907a450410321440114150601501550704000c00f23281d00318669500c040340c1c0114075603d00f1a03c0c15000000120100254104d0140b40c80181c130318071402000800040c3d00b01d90460340584201581034018820402140440c1c900b45c0004000c100700041c20440042207058006590941c014203214040040011a4868a8052040b401d042d101c0c00c1d001c00b000950130f00500215802e010b404e500c5010b000180f0f4111034150025a403010803140c01181c01c614 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884805980 1250 884804730 884804771
    0xb0f0901060906030c1a0706020c0313050f0d02040b15040f0e01060906020a02010e062206021c1d0a2301090506120403182c07030507090303030f02040b1c 68
    0x400044600c0c0300303480c101d240c0c00b0361440701600302a0f8007030400108001235052301c003410040c3e21080065480300700407101d9581c80c44d01781e00030600c40e0b0030952082c82150784900b104111107038151000329540c500300e404105007805410140c0e40c441d50118010400c54612070801e01242c07003004200b55a81d07615801079406185038000c10005070058036021000d940200e8034201d0360a0090035080c45c002084224009509080410049144c0c0350b15007007203903d40c1000300641c001403d9100d0089110515800341980c0d00100800b01011207001040202d0366510b88400c00500200c001081c078410b4510f00b818003602c40c903a0440c0032444079840803443e03003801000d45041115603481d001007915591001d696402d40c0001400500082c40e001051600ba02d8803050f060030203c00c098204049460500c0c005508010704c003404051070401000102984200a0307011641c25090018440d11080442c4010f88219003200d4078044000404030b8403003180600f844400c0c42101c100f0400d40d01c5102241c00710a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884807230 1250 884805980 884805983
    0xf1110121b08070305131509050d0302040b072301052d070518130213030204180506060d031115070314010807052b03200607120207030c0b0f090106090603 68
    0x18240300004031004e009520036a004900500003040e06511552500e04403029515030f00c0700e8940b158804010408200f050b04842443c50806500702400e1441044243c0034480010300040492007088413200340740075804074100c8900b4001d0125190a24850801010310112090b0900054a035507110b801c02510350b6001d40000d680307161908400314a400c640b000388070000ba90002c400500d81003109241e200601610b1a2002684072013855030042004071411041d602c0804c0b1602c90410000800104000b640f01c4402ca840070204506810101c4072052100034908480c805e200b4903106204030f0484107445014169001e000c0d00380e000c07069080910007031045410030351061070144181e1404245200b50107000741c443c50004a4000b14003416510065020b4002c9101440010121075000948101205038140200307960b0426103801411a03400541c081111740c1e01141c82800c141c0700c0c0d84401e00464104240d400700d404d046590000008042c1d940d40590362800b0302c0000e014655004820840303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884808480 1250 884807230 884807237
    0xc010f14180f0901091b021b10090f0f03140a11060d11040f03030f0903050a0609020d0206070b0a0614010c02060a09080d020d1b08070f1110121b 64
    0x5091070310a050030a070000300160744031021489441003a220340146500a05604d0b10208141c106802054802012100d00e02c086400c03190f00304410401802450400b00c0c025038254051100140c1c0c00c0300d00c0c151a400c07410760380080010000d03041c03420045807000e40303004411241810118401c51940d03054030f080020014030400b2002c8070a0b2400d00c0141905021000c00400d024080c680324480981c0700c0e4100c2c1c100c01d00c0003e03062090561050822000c80560308081134158119201c00c0c5d5100343c0c0c0d2a00810007620b071141942192101c58070301548544c0900419119051441d00b100c10360011503458502610381140003c1503a0851900c50484d441030310b4401e00c2d5003568083c000340358000418038007071211180000904090410162000c0300035540503000750400088000c0056005001916031041360010b07540202d9030450803079818660080f60110a60902e01d003e030032078480c0c00741c00e80c6e110f400f000500030701c541c110500129540400804201c00c681d14214400f40000300404000007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884809730 1250 884808480 884808487
    0x7080a08010e150d020609030d08160c0309090e01060b03010b090f040606050d02031f08060103062019020106080303070909060806150d03141c05071103090409020d0803090c010f14 79
    0xb5030900f91301800207103001400140c41d02c034171750011916103010281c2c800b00149564003045803510340060303469000d0340343d0f260078504403c807030f200204081514029030740c101d90b81e12803072107105409601000050881b5005681c41750307500e6149400580040392218001d0029420801031480e06101d00c2c801e80d0b400392104c905008141d24500c0007504020700102194a40c416400d180840550141c802008698000c1c00950f0451525109842d131005580e00c02d04001c000b4943e15012030700903641205800070000c03240c00c202c8402240134100c658058403050000106000903581c0c001451816152604820701c1219a076003a80780e0f4810049502c1d400041d00154003482600d042c41107c0c41c524042e00d0310090031001000307441841d0340000040080040c0ca03040600140e480c500a07030341c0c0320740182021902c908200170140d03168400c200b219440b840e525498202151f51318104540d0040d00920701c207880b4609507004a54544408030582d000c2a00c0e85440716190344101c01d65046c40c042005803504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884810980 1250 884809730 884809771
    0x270603050a06081236030d080601170c1b010b011b05121309020c0d1d030606010302130e09160f2d0b2214060301170a0807080a08010e 59
    0x1455080b00c540c92100c03409004100e540b4166880962103603030800d492401170014442c08152508440009a9003409040010440355a030071000f0520560542c020002c010b40d94030207810f005124141400c41e55184420306541d040405511800320f8080c02c2c6c80d18240501000e07d6100c070801246c00042499021140700003003000d61f40e002e052100c600808200800d61186c550005a8100410008135584650151564540d010f1280c2000c0482483d5400386400103001103078071500001c00560515400040340c01180c0c503c40c400d60010f001e80b401d0401c880c24a600360a880308282d104c032000c92000c0440200b10140d00380c1254084a20f580700246031080c0300c80d0685451070414400c40c0b41274521010000c0d01d150050020020041c40c500580300040c2c80840e010100000d6811070f800b6400c107501d840380176071261803c4078159200b43c1c2414407040c4008028914000b136a1400402003c1d0124a0070b08200401c0090708403085607482e41c0310380361381320611090b60a03c22684070122103215003a080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884812230 1250 884810980 884811013
    0xe0a031707020609030a0809090105090108102a0e030601080102031314011503030e04050a050114060336010501050102160608191503031704081207270603050a0608 72
    0x6081c2c4094540d604003044040081d08107420b100c000c2c3e50702d510001e590702d854a02081020302521f001c45028040c0d5042900c91030361581071012580ca8540d0724170b0b04425400404074048486a880b1001c510142c2e24088020720344011260400d000b48200800800e2150060007524810b064183c0d001c001d2407526119a440c100d00c601c441501551b84101b40e680f14102041a0000755000c0d45503108142900c0c0248821154001c01030000306203440c0041c0314844441c0a2090041ca00302d60103901ca40382c2d558041c00100200741d0410702030700c1080d01151405092000c220860711740c2c4000300030343d84c1c0e114010784c0c4810b202d130914841c501b511b9206028142c001c022950b080903440c0700c0704805500203480f10084030894000000400c283d15030404c1010b0748526403107280a00e404c3d1005d110f00b000e079104c5505000e25440401201203035000554140d110714103500c0140e00400300d02034080000860040c03241d80718024080064106000111100601d02a440c2121907002c02400d01604554501307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884813480 1250 884812230 884812237
    0x112030f03060305010212071d09150f10030b1309020a150203130b0c0106120f26131d040201090603110702030715090611060a05071b0b070e0a0317 65
    0x803000e05a0320140800402c000344064030403412150320608041c1044440501103182052248801410000c1040c100f0b4407890074058105400c04810040c02101c58001032030240c40b510007036003000c503010901031700c190705800038103084d1003d035034141b079031652107012100343c51803030750b001e508421407040030050000c24400c0190245024415281005103c0e60402c200726101ea201484050001ca1000401c0c0030070f20586005103444040b001d809002c86e80c8502c1104803251024240351141e00204188500e07d036540c14000c499407110982d41c02c0c4038401d0096140180c000c0403542403900803441c10780320004008500480e016100d2414161074018100c3c060482e44032220302c1100103001c82c4005031010800c503400341030720450741149518412402480004198010f004008a1348117826045401280954203d081d0101c085520f564040055525503100f0b00e000c9030000c001c0ca0401c0520400c3c54041e80211110b40d640742000010400304020300016000c05804400b07511701c01240050700d030008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884814730 1250 884813480 884813507
    0x1b0c0312010e15061605150f1602060c0f160c031a070c020d1b080109050c01210b0114030c09032b080415050705030f0a14150a03020a17100203011203 66
    0x5a171a4001c07190781d0340c1d0611242c0a9000e4202c0300003c18000c400d1801e80105030b020200c02043d40410101450080d0b59000107400e490072100001501102031801c68100c414a10780c1c00d440400c10940c2d450725130f05015040c0f10a1314541005070790101604120051381c2c3c0186607a6403040e01d81c1615808201c0e21201c0102c04654031402251144134821045c0099030060000100000e254449810041d0078018043d03a0181041002085001540004101840d403c520610000303081500400180c0c0c40003001e0420000700f4002108000c8581c080e0001421b000005905442a2000320b0b205c00c100007080001213070042c88004080800c41e481261441c1c1e001e4051407140b5030020011424001721030040c0d5155000541c0002000480c68034081e0483e00503242410800581040400010707005a02810340a13200d08043c543c5046652034401c10400385400400e07542c803055403442e1640e20040c42c00310001482c0501e8008100521451003500e0423241403480d107840d1070300c07680d4040303c04818100f0b8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884815980 1250 884814730 884814757
    0xc080d121a130209010210231801060b0a030e15010b0c030418050103020a270c02031e03270c062104030804030e0d030f081b0c0312010e1506 62
    0x841e5009994208699607882d00c03030900166541c1e801d000090412810100e01403100e0b0824241c0841009051842d000440007410400b14075251483c0b500410341490107101200d600745000415031880030001804079004a0720b00f0054040c0c501070158445007a07100f449041c4012a0040051503030100043c07240084410a492500d5118400d070f1203000b881075690b054031030b41c810051045003030810f000c00c00f405400d0b44030900004c1d440c22080855000961440c82d17982c0f601c11001000d4002c00c1031f00d42105400c04a58001603031000c044405800840c0c400c1c2107088075441c560340194102d1408000b214000c405441000400d0092291a41c003803002d448103008036407404a010821004514001c5200c2d41e104041828a401c005260140e10001c0c24401c00642c8011000a5004001200c3d0144caa0500035521b07034800b030505e5102000300510500c42e2000284e10f56255801200401d0944a405150925a41ca40c07440c40600d0b202151360029000d45492060602d191840241100da4100003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884817230 1250 884815980 884816021
    0x132906040509041514160518101812020a030b040f0b01090e0111120f0c09190e10150305150d060219231605060f040c080d12 55
    0xc10950301d070858054445540344600000e65130614040c1d030003c01310345511034035030742440700500d4403180c1000820f10034008002681d2601e0400b44a040780c13800401001d10950851202016041005c02135040800c44100c010118003801210040e401c1030b034000e01624015410342c0d0b141801c2d04030250080e1001c846200b07410700046ca0700b481c15401f074440e0b020003290b400c80800100307080d41d0800b20080e04800c4280b180140482c000e1074145e0b44a805c2000d810280c1e00c903040503282c1881803444e2141c0191a01201d011419070744134082c3c04960103418038803070694074040700c03103041c2e100707802503a8841620040034450240300382c00883e001a00e20140c030410885020000da1b43c2140301c1c00880d500ca80224024a1680d180c1d103145a4201d51401c0100d081094080444090603182010ba8110a004a070b519140c19010920307506a42c0c1c8003080394250b041103601030b2078007081110f0842d2407180b00c0c640031400321008101001c815103542c4880f03002c0c1d42c03800d05406c081d10400d1242c030720900d08c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884818480 1250 884817230 884817239
    0x220b04060603050f181f0b060c030d0e0a02010503130c080d020705120304060c031d0301140906060a050a12051e0c030616080c0a020a061406130509120a090e0c030613290604 76
    0x2801082402910b8009582c0c6a19811140c01070333401e0340248074110b0b0884000344016076005001c880d44943c03003070a0b110043c80e4904e40741d000d0518580010034148281e01d0407041840c0c0004000054030811a0014407640342d03120240c2d902d1090380a004009050b0100c6040024011041500c500f2500906044000322107030100f402c50b900f1440c04191960050113109141c0400e01030107030010700a803021410b4034107050102c2d01c880041e10502c4494000040e070b18003400003d0107943c0c4e121805c21800140c9050400c07845598094081d881ea2082c041c000205810b5100d52600340c040302d0b80c540380c6100540c0c500c1551003254124418010540c02510800b41c00164a84259545100318004451a0341041824001c1482d1a00d880c1601140740105101d042a0005050840384540780780c03255846450704011038640d100369001580000f018401d00c20021683d00255121700030940e02020315980080b101c40075119451074004950121204c000700d801e41101500d100d121000d807100d46032560720b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884819730 1250 884818480 884818489
    0x6060904200d0c03061517100506120906131a131202150a18060209060708030f01031e03080412090b12040203010b060306220b04060603050f181f0b 65
    0x42d800581c8543d4078460b0b00d18264141c4100c20160202000d03150100c14002000391501d0501c146900d81c01d01800000f544205c138449601d0094000580f115031240c1803d0500c884521003a14100c2e440d009110004445c000b07103040c40c00060f50842c80c0604d004007995041240c400d03000d40222500e07207180d80c0c0303035021601c0c601504000000503401003400300350504d1b050340051409455007038213030700786010200310f40004041e070f003a019006a070050307850750b00000080c1c4900c2402e01c000c08906011040050740e42e541e450300b07030482c0d00810004400886400040958005051004012a8030321000c42c0c08107450943c0d40031754040b03604100f80f14036220a10134040c0d40144031010310713400f803907005c02003182004c0c041d03000906815103141d070650504d0400240c100c03404145664240b5100001c904906070150442000154041e004004980c2c651b9002000b91004070b41900e480810724020500c40000c00030765003003910784200940845681100000001003500301020f5182c0d031a9207080c14690b88 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 884820980 1250 884819730 884819737
    0x40b0a021e03070c0608100603050a0e0a0c0807060c081b2b09080307080306060703030b090703021b150606070c05120303010810050108032b0f0f11030606090420 71
    0x211100442c0c0f201214a004044006650807003000c018682c810300480052442d24a400c1c2d41c0d030384c00c2c040b445560302e01858009004120250013103100d0151480305110385400140107894100f815514042e0f2108004c0da85401c41a4004103120001c2040400205a04840e01604002c20b070941d403200801804021150a20030100012052074440c24031039035400c00310b6140141a1040954105900bd40702c1079604d000040c2140d001d094000703001c0741094801d50010240728001460400c2d6800c156070000e00940100754070010b03441c240d6490b8400e001c00041ca030369401c2003900d0f00780c2c4030303550b90030a1090a42000e00211080050410085179640e644041d5158a05085004684940c07425030300381d280c02c480d010006c04461401c0011710030900044200c44081034003003c10b94010005110341c1d240c3c1141100a1800300b0b1809401c0014101160800748503000c41850902c04800020402c5403640300941c1d14a5002c2c2003048002d81c0360a1030740240c02504450780125001450020500c800d513030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 884822230 1250 884820980 884821033
    0x70201020d0f1a01020c090a2c103914041403151b0714101d0706021009050309090408031918170f13030c0911040b0a02 53
    0x10b450f060850115041080211000c4509200038241448400045000400e002d40a0601c00f0b40b07030031204405034210600005200018400d20800d002c040607c0380d00d401841c1141c410150a09181590064102003408100d44160040b841c0c0d51010b0890640028860400303c2c00384402a0105041103500790090002015190080c50100a00d10205804c00445c45160b2404031b5014091103000c003074180c02c020015298119160380e8400c1c6050021140b403224086071524481e040307106414a00e00c0e0082c900700724010380700204c0704e032100f034400b0703210070a40c0251001a40000381c8001e00340da150f044281d640340680c00362841d1001c1ca1002c10071070001242c003503501c00c0c400024040c4c68140c01d4505040d40070000e0040000300020b9014078442004580060800618402801c840e6803100007141d405004d50034000d561100580180031480d88144000e5610540b4030b100001c07000c0440c015026004031142415191500f440183c0c01c40750040140c0c441140b00c0c11400c030000d40c0e2080d15480452 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 884823480 1250 884822230 884822261
    0xc21020301030204230411010c140d0f080c0a031107171c02030c070f0c0906061112031006050a0e0901180f09050c01050c19121805060d05070201020d 66
    0x350706500610040d5204111840400c1e6170311400d0300040810030024035003069221900980c032030003a1004035020329a0101c0504072040d07502030340c0703d1802c00085130003011889403501c410410703003110150707400d100c11240591000000c1002191a034801d40c0320381d42201201c90800d0070907143d40c40e0452402d444e00d101c1c0d0903074040001c0f130100351002826180e001001084040d803035450700200000716801402401010a40c40c8000841007161201201000c2c15a142c801c0000030fa98500040190701013106c0200d04d40501400b04a107403407010200c9205034a0316131a5011079187c100119510380c002407003642080b0007150b0b9150140e481c291210b000303280240c1c00181050000003c0c500700d59550800320803052a007c4000c2c00941c011a40d0901c2d02401d0900c0750712031610004a40c00d200d00341d00396000c5107012520420810100402c0361024801c0d44d9108000081c46034051281d2403050701a10758013650611540140c82c4003030700300e25400034080c4005404c6c101008001d009580a40b00500c41c031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 884824730 1250 884823480 884823487
    0xf180915032e020708132102210a200d17090307080f0c120102031b0c010906051f06080915270a02040e010204061b080c0d05030403090e01030201080a0c2102 69
    0x10400341b10780d200c0505400c000c441e800304c40141c0e50090300c6602e501c0c000d0162034480c40c0400c0418030513460030071003071503d8147d41c8040400d02d001003804c0100421100800c02107005401241070000f110b5100a034080b02c2c1ca0003060350360454041513002a100070391316218400307002c588601b0901448004a6111000b0700d18030500b00e0030410b20011840c6a90404da2052080092041c940d0381401564040b00c403961fa0340d004903044950141500000141055040c44144040c107103480000080c24507810f4044c0718520340300c03803049031040c805458850250b03120301c82442d016200c1c0246260016003903021032070303100c04600d284540101403400b4040700f40c00904811041d803d103800b418480e10088402140b8080c1041009004046883d4222150900d540c4070301c02000526011502c0182242041b80e000c0c0e01808001071055004480c2100090518980095841420603125040c2c942c1610791807007907a61440c00700c0041060825101c10050303142c0c0158011030015101c0031602050031409640d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 884825980 1250 884824730 884824747
    0x702030c0607030f08330301020f16020411040612050712110c0f01270f0606030803090d03020a050d0c21140906011203050c030f180915032e020708 65
    0xa0b10030000c00191441c030a280c0c103016905010100c1c1c1b44244001d036100403128000c040402c1c028040c4204494800380300280707218141d1007060f140404603100722010722049000d030346241ca680c000c500c01c0f40e0105400007410074132240c940d00304552000d41c61502100c50808040200c0a4500000c90071200c100002a83c0714146070600010345046d101d903009100c82d180a0540729103c62203a540100000806c907054420019140465560359411550501c4031130340380e09010134a03038002d4403612803502c10164448140d078003030300a5450660070790700d40c3c0f4246660109281c01410400c000c0100b0072001c102c111544400210045880804071a00040c40da2080040312440180c0601025007a91043c0e004120101007004000c241302d905107400380c4c480c0c1e9440c1c070b103504d14002d41d031001c1c20241c804281005014064007907a6030417002100ea01d42c4a40b1041039450b40c40c00c0780c958207500340e000800300d50f4030b1322010091040c61081014560040b007401d500302c00300300e0f041010111694040040c1000303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 884827230 1250 884825980 884825987
    0x50f060f0a0303080c070204021e032205061915080f07120804170f0607031e0212011a04050d0602120105030304151d030307030903030210021303080702030c0607030f 73
    0x52612410354072280c0640c00c5072405480320500a2035000110400200c000c01c640715501940c10700070381c040d030703040c98009400f0412800d41c02c11107802d440000181c601880115824081c1e032102c58204001d840321fa1100d9041c10b46008100c1176090406440d02c0f071500d407185004141c0e40081410001400a5803200350315242011844c1d80f0401000340b640000f0408185050112030031180e031014031900c0842c00d1500581002070010700c100315802a034042040c142c2e01a00050b0070040107140c0140114184110301c02203000f15011001c4a0395844014403c000313200710001084124420100e0800d5500c0000980b0403490050440f80c0e20340100c1c8440c101ca8400b0310a502500c4d003180590f080c40d0034203039030030480c200b002024404c21400392040b0340c0d41e68042c94020101000501565035030100350602402d4000345100c1100140b1941c0300341034010100340f0a48601c041c0e4000c51854140c51602d405e400740d08900d0059900d070050150021840d50341800411103184a80c54550a01d00d0403030014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 884828480 1250 884827230 884827249
    0x9080d09110303070809060c19030503161b11060d06030303060f090501030203030f031b04061106091911040f02160c0b0f042112022a220b04050f06 65
    0x2e01a0784288500b8000908100546181e03640c01d0718055210b00b010240646000000724010b81c0e505451010a01855440001035128040649091701e580b9200706c41101d034a0300346004070b409007041200712000100f0141c03c1d002c03a860b0080c01d250410101e8250b01d0201c0b20650b20403400f00c0d03510b03417080152104580e148001010540c00030001c5614540120351a442888210a900c0c140000007440301c6856410071f407007080c900749156441c0d50716008003030001804111076401d0f6101d558005180241c00003100400c01002043d62240c41141f0b80d40c0c0550b220b2400c41103603200303894203840b0000540c148007814220300345149855819166082261180d01130b6005200915020401e07901d0070305c00c07902140e00b2681a41e00f56010411a14a81c1c5262145000010007501d650030115081603800200c410703850354000c03810301c423142c0002083c100740124a08943d4220b510300302a42002401401e0614000340c0312500883c0f64452034001070100c5001b2140e052410010b07000b486124106801c0c0c0703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 884829730 1250 884828480 884828513
    0x2070807080c0f0904240e03040608150a0f12080d0507031b0801061d010c0b070203041e0509011a04150c030807030921050702041a10090b0f0d09080d09 67
    0x82d005942401d80b902000e503403550345006c0002d1044054064106241d600c204980a28202680e807900c0d140c0380003c08204080e144030403040040070090b0250302e004620304040320703c051505005149800c2d0700c6070f5000d000031415611140140280e0122200314020248a4031300d9650010301c0c07421010003c40540b161890754020031400b08014016a81c100d096901c1480d18415081815207a0760012191180d43c40c10060056146c0ea082c04481d82e00040a00190380b03e06402409031514070350110149401845503583c460303403400041040e4008520717000301e8103885501143c0380907100d680d2201c0202c2e079074030ba00c00052a14101d01d42410780c000d580740e4000f28203203010b0204270071944500c0104005030070f00380c80700039101d000b01ca0180d004104840f143c681c041d009004c8840c0e401d03100310b00185901c401502034a00e0140e445200c9208078058400da40040c07284508021602d035000d02150403013441214001c0d07458007010080341032400034001c00701d000300340480c012080e49030116400b1441c441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 884830980 1250 884829730 884829739
    0xc080106080118111c1802011706030703020604080d1706060703030c031d031305030604050a14070e280b0a0608060d0f0f1209050a03030f02070807080c0f 68
    0x14003500c1d038080d07a51411500011010b054150743c03c00d0260040000349144010040002028001985440581a030500c0c0c203000801000302c5050b142500086840300090003e000b0140320f14080600c108616048500a400c5941c8a03483e5408141e07954401e070071001d2142d002c49a00007402c0d41c48401418010400368000440303050400100e00305000340c00000b4285a101c2d8404c03114030744260700c482400c4050300031900101041103861a1a5070092601c02064001c0c0c040210b42414009405802140c0c13000049c0003601064540c074003550444c8400d0b000d1801080000031f20b0701081b0382c1e0301c0d01501c1940c2661101c3c00351026400c01020320050641c45003410310708440320540c1c0700064035085940c0c0e42030200041d030f40c06000032058101502d00801c0622070314540d80521000c071000000492041c00c00c912400055041640e032003055100c0c40f83d208a0701941403000a206241079102d103481030044030000e540740d1881d01e051002da038000008952081c02c07514943d18002e1201d0303200020a88 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 884832230 1250 884830980 884830997
    0xb090c01030903080c0325090f1a0403021c060507090501020c0d05210708070b010315020c03090111031927030c0b090d05150609090c2404050a030b0a0c 67
    0x540c0034008440040400d00308100100016290444510180701031502c110303047d003046504884040c0680c07815014100c011040e444d0007042c00300c1100d00003080510b0041d20581010314680c01c2000024071f200b002054103109081c3e0710000b9046001c0d150107034445450721088241081d00092420b11000f03002407080d0040000e81c401b01d00042045518406c1da8200d0b40c0510b20314010900003445910801404884001025018403c07081009410f0300c0c8980a03040745519000d11042c164050071180d01d9003070300b081080c08400d43c001d503900d02d402000d01080e0303402c0c036061001d607080780540c03003504001155466044140854185039a07030b42140002c09549032041c1152100413010501d40070f1804015000900850156501441041c00c07650103000c40d0062401e42d89182e007000300c1500da042c014084000401c80000c400300e00081a84c81c0500064202c2c0c0142c000200e658030041011200c41004000100c1c180d107804804401450041c00810007900388800c0c01001c407103443d000702c010040d036039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 884833480 1250 884832230 884832233
    0x304030f0c05090708190203100503030301030b01090b030619090c030b0a0506281e12060c08240904111009031e1e0201020304091805010e0f070e100906030b090c010309 74
    0x442e580c6c0c81d20074075a0350058a0380c1d648121610000c4654201d076a040c03201200000400c4003406a581c1600c0b2003102c01c0c010b1445500c245036071005c081e0750b440030309100c4411404001113654010041c0c60f005d01440d8410541e01e4603000352002064910810b21a156010420541031003410480340b02c1c03001822040b0240c0151280c501c883c2103001d0300c15031000d12a0351403400c0c0d1540304114054000918244d9484525207030280040c64803031703103080c0803e4902c000291901041c041c512160a142400010f880c8044400c204901e00c00034000c40d85035050320b034a001a500c0e42009402c504126440340d182090075402d00004582c011943c810903481107103d0007000507030031055503440c545120710b00018070410340700503030071801240c101002c914a00b144080140d0118060340c822140550300800134084882c561941311a020410341c0030301c3e8012031003040400c4140c2c00440d4042ca8111407150000e4890040788240d42103648140d440d1603c1c1c00500003001018484201000024241008440f19a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 884834730 1250 884833480 884833501
    0x7080c0a0e0c0405100804120804150e0a050106080a060506060903120f090301050f18010c081501260f0f06011205060102010906050c030907060512040f03020304030f0c05090708 78
    0x25008089070422080c0124020020a806440141c0700040004140c000c403030f00000c0440c00704403004d880c1d0340e00b9200c1825200b4042d03007210340501d801001e01c1003041da0a003c00c03070140c07141064a107160701c5007070b0b20070022950030311414002c1c0001c83c01030f00303c840785414007406891010b07050034420072003042021815900010388210400744200740548843d1800b0380c0595a000c0c1d054120b0b015401c2c036003005012120004401d2180c140a8000c403054600780800c01c0c00c80711417060a201081e00070002c02ca1000129070303600824803052401c0003903003580843c070344503145458452182004696040c4100070b426280400d500250007080e2800e00d160010008000342c051007207802d842640c03500801d0340b591003900804045500620180214100001040303856441129100e542d0701800030040385881c030960480f6030818810740003100c161100c1d103c500c4c1c443c280103800c0701584420040000020704d0250216841d03405001d4400c1260726203010700080d054000d1003003040103140c104111071000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 884835980 1250 884834730 884834749
    0x4180c06051b0102180103050c070609060603030807021623150417030703080109050c04030b0f07080709081b04021902010e01140103030804031206091e0c1b03182607080c 75
    0x5c0c05d20b0081503c0c1c50341c0048200070b2092005c040c0846040c51150814010142c0099045034401e81d02c0001680d40c50030b08a0b00d411072144410f0030181034481c1000740403454503040351085a40c00d6416142d58202e00000c0d506c0e507460003000d071184008101041300c099040743c1000c00f594001c002d14901030255070000c00c81c59050041c4071075143d6a0000c81c2207540801d09842c007866101102541340e0503c81c01a410301c2c0c03000ca5400b030000721004001000f0501c83d005c04001c41d281c45000705007400e17152030b50721a01003e00c480716030000d6080c004609800c02e0700d203803644004000c0e00002000d1190400072381c2960228a0003940203e107031030042001a50010000d90712540500d030514480700b2a28502026007440c4d030228403c241800e4100109840407100c00501c01d1880f403007040a580c0303400c400d1301d0354075480c0e000d903490b2024035080b900803030f001d000c07800514440e0700c1c4070b14049078440307040c2012884903440103a0646000b031800040d810301004803502601d5480d0060500d00c86000c001400482c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 884837230 1250 884835980 884836027
    0x7021906020a050405060409020d06090b24210412140a05071a010f06080108061308030c0c0118060e1c03020901030b03070905060a12080904180c06051b0102 69
    0x3940054080402d82c480d070b058074083d080082a481d40c89507a034000b00041d40088180810030381c84c07c440000c03402e505100d00b00003510040c1041440ca00d5101c5085400c0089480564102b00c1c1000710004400d6900c002500700c50007860103a0300c0781420b080c9020794a407000900024802ca541513564901902c0b030946480c0d00c0d070ba24249e9901c004610b04101500e400c44000701d00b8619540010990543c192111001d640040d55079001c2603a84081701d65598509886079622216184603150114000a004643c8145a912a0740c03405a11806c0542101c2c45410782c1d01d404e50000c000d2108019403401a2038030300c0e008200424400c6101d0340c031030380100805020f26007890750005603020a640030360000c0340518030003010364031080d9603081403e0190404480031071089038280d0001c5051302d010020004030300e07003010000d404d06280c8001d02c401003404030b45003080c1c440c003540802d00251500117100040c1015075191501c0e184214020014080c44118103606c51f40140070303203200c88008503106070010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 884838480 1250 884837230 884837243
    0x13212070f02030903060f15090c0a232d030108030304060f0c0f05030a23010503190803041712160306050109141003060b0415020d0504140d05010e190b070219 70
    0xa460742d0380817081600c0104203c03600070700310000300410701e22020007032f103140209901c0c0d5000e030141551003a029481146000c041c012010f005408400600da590602c036805c09110b0404441c07201c0c040d400e81074009078416603003680004104410000c0c2c034005d5040c0c60442100900256090300c601800913010010a1002c000d004000107909a405401000c00c0c00c2064118130380400003924880201e0070309008a03402440341406400441301c0c852a680001a000310072182107850f81c2d9507141e80316000301d9101c0c8074a80c06004c07240280003a155010f00070005000c00d8031800d2842d48000d82075074441e600c801c0c10b0044403007041122048020f4146031403070b4101c440c0c404240811a095004103096040700d0150800804c0200e1551480c50321980d0742e444035000c442c1c1048602c2c0040300c181c42240201c0c005d200144c134109541381010000301d11482d1040c0c0c00420040c0300c0d4403605141000303140181072101000c40c4682c0a000c1030910003078100da0b09102404480300803541d170923905903a181c80108503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 884839730 1250 884838480 884838511
    0x6010309020f060705070509060a062703021305061908030912160b04030c232e030605190806060d050f060f0a0b0d02013212070f0203090306 62
    0x8542d50040d000b507810100400c03003a16116642041542d44001c2c0c010980969401c2c008180300780b8000204104860440d520325200180844030502004052400a414003803610004401a500c440c5075131020044144009180d15000040241c20884080c1080b01c20715115410f2000202c0402240d4500e1000d584801c4001c4e4400c1c0c81505e8030a8003002100200d07a00765022410b1500c031b00040c0300300c0c0d0141241842d0640c0f00c4d8151102118105040386a42c0110415100c803030411748001600c2c1200b036100c00340200810b00304002203251608a00c80020750300c410a20480c6000c02c1030014580c00520310080d501c0c2070010166070f6140141c00e0340d228001c0703149400c0400100300800c49054200c3e0068402d50b00700a001c01251800c2590134880c00c83c1040150a03e50074200c41380f40000303405030b440122944501105502d103d18000d80c1d0355207441502c15902e83c0843d004014895482c806030071500c10714000400034804600e0420410454008011280741075400203503081e040704003461b030180c1d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 884840980 1250 884839730 884839733
    0x40603031b1112011d16050904060f0609021b03130915170a1e050c040515041b080105031f0b0a150903110d03020709021b0a0c05010311030f06010309 66
    0x80c10b403988042c25405006480c40804580042d0014504504038500311400d4000e1110170a403034410000600020413001c0008100b20310341514074980040c011040040c621400f521800705588854000c01342140e0009290402c480200c0500454a900c48024500f060000402d1941140141c81425115615000c2184000d103100601740000c0c11004003048800c03807660105d94036068100d900b41c5e1800c03401480b141c8022100c200c044909540500034081031303043c20003044004d210241400c81e080b0740c1030843c01c1c031a860328400d0b04c0c05c0070710148100d020303652000002045200141c02940c000d070045803400403813081500301c0e041c3d01210034501041880c0c2c080f01241c0e000a040d0302c4485030311143e9001444a03a0400038403c281c0c0c1c000d114154141d04214207110140c0082c5000900507070080c24100005505540508520825008a8072007901107215580c03400c84022025188144403c108208560701849079000c01200e6060700c2d81503180c00f801050049900038900303414140c4614240c030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 884842230 1250 884840980 884840993
    0x203041202120a11041109010c20100c06110c06220c0b0903070b0903150a0b030307030f0305010807140118032012011103180304090c1d040603031b 65
    0x40d015048408841c4241000c4c1080510b100307404d880e00d8041c5150000c1c00035010481421180281d006071295a8558044d80d0b50320004500004510311403c010240303840c16035103010784c042da43c1d000d980e82c00c4038007550350411000b142c58080b4503950b00e5000700f00b83d5505030800304a8503445035201c140e100001c442c2d1000088554403080004000565524002c55400310000240803024004d070116440607440d03d0400e01140700d142c59195065000e4407401d9605100c0a5046d54005031004020480381041400300307203140c00c40d400450214145001a00e040e80d41845010700401c2c03004000c01e40180f6180c4034030b00c0d035582520345904210044400d82d400c502d034088400c0040d0381c08071a0510700401c070304006c005600716140091003414201840f16554505016101c101120444018596140c00f03210405c50800d01c4202c001c580010712000036401c105203e0304104400d10341715804003140c02070201d14600700c0342c02c245120754601401440801e41c006888200000411031078084030b1510f08006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 884843480 1250 884842230 884842249
    0x1110c0d021003090b010b0c011a330f03090d08010e1303052a0f01023a020703050304061107120f02030708040801060e070c08030406020306040f0c030501030c05010507030203041202 80
    0x5008021003400010340d0a02c00c1d0018048802301074020011001c0740002e0021580d10f2035602ca80c00040762400803000d0741c10304c071f10480f0a070744402c084030185084103040111350011500410340f15004420002441c1c018040c541e19101c480c80c002c452981400760500e20900017809100100d206a07500904142c020402c50710707800040707555078600c08804042d0400030561101c901401d0300690078040c0b0042d0050083d60310a116201c804201044800c41c4107561041d402c9220a100f02600028007144806200401d2810f000382c3c0c0f9103a40b494181840300070340741d500790f2f5255400070411a10001c212a81082d0411894038031b0b0240c160050000301700d1a600406101a020320343c0081e00090f50403055002108903010300c60706288907a00e00c84151141c1032069005400300c0f030104006030001e81154019a0702c00b800500014918007011400c10031190203d49000200740e4910051091015803030303c0c000149400d1800318609003450b54001c3d00c034004c5104c0d45005180659085d42107590300d4a20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 884844730 1250 884843480 884843483
    0x100b13030f02180907030c0801060602100c2f0d0c23011b120c03050106050a0e19140a08030f0d050c0c0109150c0c020109260d03020901110c0d02100309 67
    0x383c140c24148660b0442e20b0742c2041c4801c07201d40001e000000398050b81802a81c0488030540c016101841032081030901428081865000300f0204106402e41418070141040c04c503210310440343e40d424440458186461542e004082c1440100200c20300001c40c0b0000b68801c44100380e0340d1051a2101346000c0e0b000d441404010f2034800c0000039280704066000c034100d42c0c58a40100c0520464a00d000300f5800c81e0000c0c018880069000c02c407281625005030720112a0703000140c0b0344505900c002108809000700d0360000c07800c0303c40007195040b440c50644009800383c01c294020318540743e001c1803005034034402e48000c801807903201c2e00056010309118058582e01503c210007404a5281031070245500101c00418181d1a80703040c10000c0c100f8030071039581d140d00d039041e110340c0340042c02d000581840c020604c80600b0188400b18451806281c1449110b9080d03400d91005600c80d408003001601072214001c0c2d14281d5030120305e140e42995110700094041c2da030140c65521603001511030440c041c2246140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 884845980 1250 884844730 884844769
    0x90409080a0201090528020d030210020406050901080f061c030e0301110901270e060409150f0605271e010e151806040f0212040b100b13030f02 63
    0x207081144a4040d040051014810010b56a0516020808005502e651540504140b45540d41d500040c280400d9400d1814000d0044505080c1c40700d004000703a0f8000c6c2c0045000401c080f607003d01c079582145009070004e03009951040245810340c04241101000742c0901240e400c0b443c071040074107020302c01c440c0d41554090000e010421081c83c6412880c0c0c46420401d0001d16903001070042c40c103003091041c0141c0842c2000d800d90502d0011009080c001c084c0c01c859020356640034000024101154102140101d4800421100c48085240d8100d92141c1e00c0a0b00415018044265050001001618041070ba22a00714591203030700c03140e10f41d11900002e8944c00010310340040743c00310200e51001c0c4501e0842e840010380c804020103101c030a0501d000700c0c680445c1224040741561406030492401c01d13400040043c10701d13850100000c0e4000082d202134520000120501c0300521100950b50050102c0c0c01c1d4140c60001c1110f66141443d00710320004d84140d17500f071070041c21961180059a0084000c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 884847230 1250 884845980 884845987
    0x4110f12010e060d0f031d0d0303060810061208032214010f090f140f010c030e0c01020f0601060e060d02030a0f05060a0830040b180f0d020609040908 66
    0x840c40c1440d60030a000e804040c0d0201c0e00041e860380ba041d00c1c01d0545941c010b410074a01e4180c2d680a8907107000a0170901d45800078032004082d40d841351701a403180e0b9030113035401180b400d14000350039003014403540c6a400c0c00783c1403020038060f000407110180380941d40316440c1c581e00e50300d0304002d038004000c4854105e080c4032000310402c10b016541212134a50302c51840200034055070102100201c40840c80014800c0d1858944003001c80d822050640c1303103c0320001620f0310b0708060440c45d030855010007420400300e651116864a0241c04124084c2070140038001010714140405590b0b581e50030500c1240c0401940755041005a2184419a1b0865135908825512030800f1903000002e44a83d002d012a91807404002507164a444d9003214210389580380134044001e00b80072174030f802c413507040c422540c001940000c1820400c2544000d20041c480750f51010345406218840060baa004c800c1d9045c481c0e01c41d20f079a9001030355010100481c0316811110300d42c2d00c0c0741c0a000b0601400c0a850082d242d8030022 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 884848480 1250 884847230 884847247
    0x61d0c09120d09080c0a09091a1303110321130f0605010501020606040b13110f040303020d171012051510090e031204120c050d180905090a0204110f 65
    0x90b614a00c10351a0300d90701d05084d2a015490b0b0303a440756901e51644102001030400040c4a107a209076a414050040d0580c0d070f05244640c41d1120b40281c5030910303500e16400c110000d040d441040c0700d10056451000d11b160480b401c0c981d0078002d042425037002100204045000c1c10161092402d40e598000e4500c00340740e0383e82c24070b00010042485624003600603800003580d5460544900b0f01c4120005044207001c04103031186000509000c210900a1103081081440c0f1103441e001400055229900409403014045c800a1941c0c4021030402d620001c07039418080014041120401a0354101030082148621401d009141040b020071a9460b141c42c0814841c15041088e10141500d460030303c14081d02c400248080d13560711130b07219080b4051400c03401240000b0111302c2c01003442c2c1d902d07141a05040c0d00545441d400c00560340d4240020070b0546101801c1400398903090402088650030420052030b05085664654041100c000d00c100e940c1e9804130030420350441034450369035042e0809512500b44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 884849730 1250 884848480 884848483
    0x601110a03170105010804150e0c06040e01051c050705152101050108090a03080114010c020a151209320304060801170a0302100207150c020c13061d0c0912 68
    0x352402c0c0000a8140760020456500581d1124020399200d01e0042d40c50112014840003411405030034602401101040d5620350384000c0a8005022000c000003440c3d450b150070000c9a0180141d030351400d040c20078400c03012030380100b0642c08403182620301d403c1400c0751103002042c0c0d22941e4860003805003546650950884c483c41a14140d801c03e0f224056945c40c0e40c050b82d6a02c3d000030700014009103c04006110a0440840c0e4400403e018108900078804660000e02010241d40101c000e90000003079485080364040c43c0100b502d004030904201c600403d498405118100c8101c00c03903002c4100035156049144080300706001b20803141583c2d01c81e40c48003c020118a420311502c2e05007603402d50014119500844c003000103a605030010804921086a0030002e900109020384144103c0c0014002c0e4400c0c0307020301d18a0074110342c081c00480c4070703480800038007813800c000900c111803803c1414001c0c150b18800031881c0c0071004582200f00d50321101d0f0f5020611841010b603030080008600d84c0b00300e400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 884850980 1250 884849730 884849747
    0xc23031b0a0c0203060c1e090a0503010603052811010807140309152409070203070204060308042607090e0a061505030d0201020307140d0f051f0501030902090402090601110a03 77
    0xc01c0313061301e589446401e0144039a010340507044d1709020291400d0302c00c100c0c0010080040c0003014090074480c035911000242160142e610544031500810103002c1001c1c4020401071046090002610500e11203440c0e0040402810b00b40e103042c401c0c0440801e5800b0f000305240c0307115541c1100c220796680f44c44190542c440d00000703140c3c5801080c3c0004610443c502404021b9215000111216200b80301c6042100c504405031001095000c100700c4140540c130750f4001d400246014015140e9940c0c607209543d008030016040303c5100c0109000c6003001c140b00400c2c140d04584140e00042148066030288a040c10300700c48000344418608134a400c20420501032000840e1011010b450031101c2c641070036402d074031044400c14001080041400481814440600142000d40c4000581240a80b442c0002c0320026034821220420500000920350020106030002e03120a180074410602c017a800318100c560302600080c8a09260400510184d2246095000c16819074048600e10741080c200503284030b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 884852230 1250 884850980 884850983
    0x61b0b01230f13050403090f030b07090506130303141c09210207061209050d09140409080d05041e0f0201030b04111b1e0f010c23031b0a0c 61
    0x10014000781090b00c1c0850021000210280c207181941410b0a8600b0003032900400407010312010070070201c1c8000602c24104080d61260307a098405060103c0c000d050740c1215803141c0d125140401c0200301c88402111100100c03075050608807880600b0081c03400e032500590000b81d000210514210f14440b0103501b00291040c0030340605400443c0d01200c5103c00341b0304d50300a07405648014000c018a51044600d50700003c420540082e486850340d450600345070000d080c000011b90303144014030a0080c49034a448400c8402ca8040007042515070360081c2c6070040d440220082684c82e80041c050054200c991980ca00d0502c0c086100e200d1246003607403410b911040186c4c000fa2034003201c0c540608082c40b5000c4c1e21901440c0c408d04081c00c1100c0510381826202488507a80900701c019404000c500b0011641081c084d00548488001c81d50540d0844241c204a0b10400c4141c0c0030154211012010750382c900c200c070609442d520b5aa40f03030800c0280507081d50f010030300f5000144440503550f0100c550840923 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 884853480 1250 884852230 884852279
    0x70b0603102a0302040e0114041512030e010f0f110a060c180f14040906140720060c0901180f09090615030503090f01031107051c09030c061b0b01 64
    0x8100302d1070101c0480c0100c2c0903621962607070b40010300c115210200500c940035001040802c070a6144a03a80c1c0d0844001d60110300340e4020740b90004101a004074000f00c56080a1920f40c0e203000c4c04aa0080c0364840c01a403000901a980c00003100c402400e000f030501e1903401850521000910000040100c2603c2006001c0b0321011100401c00c0445d0002ca00e0480e58402020711002c4141401c00c0005c05440204070340150369075079454824403103a0b170386c14458032440c1c4404040300c6130590901489422016941ca60b41c01413002c2004404c612025114102e00a2a040c030460b0200c4000103106440f9400c48080d02c11030b100c4c0011481815040880740700c3c40340d2401d100c2c01801005101e203403007150100401940007070001c0c141c03606007501c0c2da81013980305141c003150f10601c11072102d4955000000c2900c098005042c0081c0521100d40712040348441c500e81940ca80d440d58641034440c070a2401400c2c20007211500e01d030881489212400e00c2260400f0150205507501c09031010841820311143e0140c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 884854730 1250 884853480 884853551
    0x12032202032d0a050a080d090501050f0a0c0903021807020f010501090c0e010804030f1d09092b050a0c0c080102220906120b04050a0b10080c060a05070b060310 70
    0x86035003c07840741141c0f0781c084000c120740910340c1c0d13036400a5045008140d4196035100b00d80313008100b0074001c184c00f0b01403100c17061003541000f06d2501d043e1100c000380d038000e004021030704100680301c00e19448818200065040019207501108038100321085020550660030140040745010350341d8011400358203592140342030507401c00019950a1000c56014000c186d52407030402030103014084842520041e140c02c907140e09116000076012010a5403858025841510f6115484014003954510a08020101403501c00340100042c040d210f00a03060040103000340d540010024410030440c06000070b030303000b035480c0c0e0a0500090080482c540c42428400001000001d035000039204000640b00041e1200444034008c1c1c80c0c1010300310002c0c0044902d0320980007490b003c102d4460328075004030801c0300d00c501c02500d448021898091580519407188104103c83c80000b030f0003000f00e0340e034141c1c4100700185541c0e4000000341480c83c81841222001d050020000f190380d02030a044288400d0141d58001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 884855980 1250 884854730 884854813
    0x904030207240203030609040510090302031b0a2102010902040603050a0c0905060604122904061a091f261018140118080901030b01021203220203 64
    0x7002c1e07031000158000340c0c1041002c01c0352402d00702140d640c02405141160346900700c1c0c0c2881c00886110b0201503005801c0424502d01c0d00031500980081d00b0140c000401710082035848602c04014080503416010840401041c8030b14003e4010704003041c0c004108010003941d80c14100d80307174482984200c910864086004c540ca9009101e414002c0704090012420241400c0c540561491074140680710310700000c50002d500c90100d0562000c01007540c0e0a00040e0400303143c42e0080d0340042c41540c813500644200c00c191a25401d25407540700c00d140a0201c600020a0550398200c412a04004120a00280200859280788110105084016044503040e01d220246041150000c000e500d40082c4061400c8000c6001b080314000c04070648070001a41803131904014480340041c3d04110b550410205401c03081d90303058802c1c421414001c0c00039105055200c0d00c071050300e1100074a0081c505900340600c864983c03001c004444d1103503010b4200d5004040181e01d05030400603802c4192500e002000c1d40701e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 884857230 1250 884855980 884856029
    0x3050939220e070807061103120a0b03070909050307063b10091502030415022b0b180a09020603040624081f09050d180b1c09020402090904030207 64
    0x20304031003c1c038004d081701a052610888045041030b40642c041c8c8014132990f1220741d1090100c41c020b9586140c0069a5240442414207045003070317001c10540303440d14021a010540220449021a500030800102c4040340c140e10315441d411403041c1c048450f40316a51590405444205442524414040701d1006070400054000d0381e490700b100a050841c0302200051380c2c0e00d244c01a5030400c0c03042c0160000b441250004030101d8000c10aa10247c0760850820410a6001580401e800d08100001e011100f40d6401081c0141a0144650418001d000c001442892a41c0c0005c071100c3c1c1c01040540d690610307091031009020340400948802038900500074000c5035607840c0908865002001e8805904900744100382591100000d44c101d985602c02000022814001420054113540390b41e00f5120b40000c3c01080c44469800020b1840030400021070b0300250942c10f540401f44082c0e000c20301400d2440850040d0281c460580d80100c7ca501c02e0100301500400c0d65001d80b06000810f000a411004021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 884858480 1250 884857230 884857243
    0x606030b12031603020f0a0312142401091509080d210f0b060c0609010b1c020906030a0c121a06010806191505040603050939220e 57
    0x708001c0c0e208002d030018010343d00600c00f0b041c0780030303006030b90303800d9640d41c581814404542070032400107119880d1000d1090039403246600d115044200c2c20b02a140c030340e00c60039039990140368004c4240701300340001900341c2c840c42000c03005e0070807000794842e40807142002419501081c02100b01c43c1c0100000302044a00c0b94800031a660003c1501c0e000401c4900c0700d8000811009504450315606d42d44180c0140e1210f40050060350400c1c00100203a1070074031401400c45600c008014812002d10b5130307103c5610070390541669a982c0455020321140c4070180000e00d0048617040c000d01d20360740c1c003c0004101200ca400c0c03110203801000c6080218094081c000d00d80c07007044650300d001c00d11080104240d400c101d6002d41c60b5407000e0400714240303a2607042c0d8540007060700203480002480090306102c80780d49801901d0300088800020325280c0c802e091070410301c0c00d0722558503400c9140d80e10754401001d074075000600400c01c080c085140300660240800302455482c001c1114843c00e000f070784c41e1028400a542e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 884859730 1250 884858480 884858509
    0x11a01020c040902031f020d05040305250201121112040f050d0503040f08161b05040b0f030319050d0c02070303030524090a0b090a090b060118090c05160302010606030b 74
    0x2a001021303450040d2502c000621b140c10244030380c01c0c440114000d4207880360a0250740240c8445889a040c802120140503400507090b08411035802d0690050741c0019015520056020b004908400c2342d40c141080d0f0301032403003aa080c0313600c0fa0b0309100a100c2d04440c890b2185000f40e05454403150310160507601791100340c8005016000320408030001c1011318020b0305401c44440814550f414480d203508568019540d038240050803445e00030041d40c546849822518001a600d9000031805c1000181c1c5070700030b55804483d400b1800b04c412202620841c06c440c1041040e440800040350740c1c000095907003000e40030807004245000049103042341c0302505401515003880e2b00c07105000c2e802c0e00f40b0410202c06000c2d600745d281c0300d9200d2682c8c0d80d11140d499100300c000850024581a550a04c1e4144074000f604890511450759880900003c0340fa00340e00682e48540360108010f01072050448082c400c0500c5007183c0c01e24190403800701030307041d04100107c0c0c966035001d220740340311041002022090fa001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 884860980 1250 884859730 884859733
    0x6011509060e18070e0337060b0a080703030207090227150706020909070f020d0f020307060608010b090606090f0d08040e0103080c0f0106030b040b1008011a01020c04090203 76
    0x1020403810380328205294030b120014214440400f0000c001488011050741d80101103a010f140070507960a04000c894034240c4030300c210b45c4d007c0440900e10740303003007086418008800c40400316040c14050306402c0130b0034801c0d002d841c401e00c0c15620107080791990350b1400101c0050140220009501d031b041e000b039801c1044812306610f1442c003d0014554040c40126003103411030401400c59000200c1d0001a01025000e4040541d48064200400101c01c900525110a0040ba0002002070990001c0d0492036202c40e03007170001ea030348041ca40982c50341c06480402000e035070900c400416501019006075a0301d0781c05032240c0613143c81d103804006c01030280d0715003141c004203154a8580280303400700521141c10b02641140780703070945850440310028801d03001601c075040001100703402004208102c110f0100ca550080041ca0308650f54880c540780082e001428486400340070405940d9803c1030240100581c0000f04442c20500d03030340b5503040c0349410103540503028219104d600b60529001d041d0525a0040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 884862230 1250 884860980 884860997
    0x302130903020106050a0810060f0b04030b092a030d080c0a0f050c0106030b09060c0f0409020d02090d050c0a24031d030a09050a0b07030c081605010617060115 70
    0x600480101098901501150349501002445468040c090009003c00e2009825520103100b4a03d083c1d03403645d440040b040707101d101c080164889000c161000d80354400c110302e02903100c800e007540c68500d000c200412417412003141d4901e440c024200441c83c0c0c9806800359501003242103415203152000719901010b108041064000c01d030b100b82840580000241000c1d070402c02c00f1006a821602e868108076218084501840540d030420081c445d40300500c481c008d07140940090507c0c1c3c880c0224800e003103200360041a03503143c10b030740350301501c41e80c6101a0040d044400c4d14140242d803610350240741390203086a14000f0807042400e50101b0755443c1c054001101640078100c2c2103000308215444402a03c60381070a02c1140281130004100d89100d59648002c254182000c11240c6121a4081205060204201300020b9080180704400e940c0250001c0d0302c3d40554400e030391100d402c81740002c01a510b440c6000c610b2110101c489854558010304a844a80e01c400c071009502043e07001d594046403805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 884863480 1250 884862230 884862259
    0x90c0603090f1509060c25240c03060510051605121306140408061504020f070807061505031b0415080d12060f170a0b0c220302 56
    0x1000215040751030a000c541d02d4080c20240503050100003002c800d000f903040da09200b1040000c000302c5800807072002125107404c203a1307a558986504440c13000282c8002d520002001d02c60240903048182000448020801c1d001c200100000c1c01c8403020f0001003072a080c0041960708103940070004148850702e0321490005184d01502c40c0c04501c450444203441040c0b0072640083c038880c00b8248051181042c410a941001c10152142079103031300403190840144410013084000041181d00b0100c3c0407002d0301c14842d898081000f91058075804030003e4030004000042000c0300700100700160050408004100a030301402240065511a0b00e5155105260500f403100074039503081d4880038020400203014a4500d80710402460325840042250400416103600b80e030840056a0307106d00440b402c200803418080070440c0d100c541d01641d40901c81e42c1c1184681800d04004e031031070700d64110b20311f5240361900903050340860340868081b03602841240c9000180c00340b6440e44800341d0354000d15012641710b0300d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 884864730 1250 884863480 884863489
    0x302120109020a0504180605030f211306110c15070302061014131514010f140a030e0a051005041506050f060c150108101d03030103060e030705070905061503090c 71
    0x206030f56060b070130341e10030000030175035020003e0b0b032b8100525002030464020707001002d0070b08a00907001c0042d003550820210625881d450031f07107019900d49003801c007642504140800e14007584212520f070013800401619540030004009041201d200b94210f07045079541241100c50f59102d40318a0588504800090301c00b0305c2c1000c030b40303003402c00c0307251000807185410907803456900303a1940300b00804000c00320b8187d16940c0c005c4201544450710700f08480d50b46081d400100451240100798400c1550f90300010546010521415a513070341c00100300c5440f0100312480d40000c10040d01e0803590a00390a4402c3c5800c051400340c0c2084650041c18003066030740b040284251a071107000000050302071940181142c05c8041d400c90b020301a154010701008808a15039001c0740e000d640424410f0036480194200040000700b10380c19268011030205107240c4840c940d40c0b4601849034010020302440d00080781070940d03944464840d0704220390110181e4008204a50750384803d80d01c00c03040303401260001026040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 884865980 1250 884864730 884864759
    0x2106331e03060902180c030f130c03062003090709150b040b03060d050f07050102010c020c0d082101180b0105030408070b090f0703031d1801090c020312070302120109020a0504 77
    0x240440401c0c40fa2080c00d83c542c02422100706c111850040140109034180c9100e1507800b00e801c007500311000002d515640401411444020319054480311400d2614540450026018081400e59510b0303040001045407038882c0b5019401990746080c801441e049401051001201c00d442c84540c0b9041c1011010400c41e40010074050700220740b00d81b180c0001d801004039445240d003502c050302c0e80c0c60031300740024295a1180800001c41d405150b043d81d80e640d4042c081e0171902d5008d000700e0b80d210300e05d40f8540e40070900034465280401d42e54000040a0540e64500c2009100054081144c9003461005681074081950060b1040c00c00b0b100000004100c495241d8111103c42e088440601601410078500384098004900007030600303030700040e4500998410b44180104a075000703100215030301811307503d800520503014220b4403490540001030081c000c0700e29031a4404c1031105076191108004e4080e500030302000004459050000903a1141c510070745164854a54400b803810340f406001043ca0300c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 884867230 1250 884865980 884865983
    0x30d020d0b010e0d1e1226090c060315040203071d010512061014040909060b0a140108070c020904030903120e090c18090406140c03012106331e030609 66
    0x66446000400308942c0400d560b06c0803102c1d5220102c54003039541d40c130415030300c1108420755088540e09001504034007041c0950003400030760b0b1954880c0d481105c0c0340c00c440f012400064105100000303008460313a002000c0760f0034112502d105540e0345140750046401d4440c00c20000d5104403004007140b801e1621061000211059190074440c40841400c450004c0d4425800702e844269039506010400c642c600940d85241d0045a01c10350a51078142141d5140c14010a240e04104912000580183c000c0e28000500341c0c0280c14964545840c0c600136040154900080e69104d901d050002c500b10311840b030300340084e540640181e009460b49d0303000e0704072504044000001a007240d540d82500780c80d41c00b0841c0c400c43c000c0f040072580b140130450a1101d04005000300e4440c0c0e00400040c0414641d8000c80e929000b01a225004109079500302140108007541d4118240e159170240640842c0c0c0015114156002ca485840c050b5999200d850615403110343d01c1480e00d2000c00340810100701c2562050320300a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 884868480 1250 884867230 884867273
    0x40506060c01151a19030209130c020d08060405040c14031005310c0e04020a0b1c060909050a12020f060a0204030c05040515040c0203040503030d020d0b010e0d 70
    0x841c410a40303420b40300400524480c141552908111185514500220084411007014031340100b20044c4010145046011401e054001451401584901c2035a03000024409020070501e112810000d4640d010800d00300c0000c1e0740500032460500e0188038160260b540200e0892509180c4842840c1122114955550500030b426100d0540e050701e00a45202d00c5004a1484460722280e000c15002816580721102c42e600e603480c1180082d440e007070340b1420b0340c003144d2a25034640c1d40c501c00501694100c1d0006103056901240e0920141c1c000040b560030621142d6081c841c40b51111000b5003100c040310700150040d480071010401040c81c540f007080d0140484d00c1a01c0c450002085124130b4410306890f810300c5140d001500300103000007100510027504046806020741d0800303044100045034109401e074400d60707031084690f903480d00030000c580c000e110103029640c82c0d0000b684650002d400040c0780d000680c0c00c20b500700a01e136214026803250800007d000701e20341806074460315200f5284d403124158070b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 884869730 1250 884868480 884868487
    0xa060e191104060215070305040b0f040512071514060f0607060209101205010b0a09060f020703240f02190c0302011416030f0506030c010e04060b03010e070207170a0204050606 77
    0x841071400800160400c0e0b00149000009804c4a1821100081c501d108051624040c000001d00588006800100c01185080c1503101c60421504124500c10b110239108000500d803400c0080d011061903624003004001c0040e400c2074014001d03030581c111b032025404074400060f0704441c90a00d01600c41030340103442c01030401c0009008648040d030101ca030407000c54200301c1200070078051401004c0c05400d10050b40d9040a00d55040504000caa501805041c460208005c9280501c00c1052500445d081000b054078140916409003040441c0d503c0e0801036820034049091010303441c021581e4501c00e0b5100701c420300428840445440c0c080540c12021552503002c0c5028600d800d0310402c3c000d0b16010881d11403070310540e030058101e66049003d251014140001c22626680200e50002c14044c20300f44000f403110907200050003405503412a665128000c40041200c0d1141d40c6624420940d5400719143d49449025541041e00750302003140a5900c819029001801c041c4c0040340c000e800500320504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 884870980 1250 884869730 884869751
    0x906010e03031c11070f0203100c14030a1401170717120c070b040303030c030c08090a060f0e0331180914060f090d0e010c1e1403120a060e19 62
    0x4240d448480180c811011006c44c40080d8034081c44140800404828108100321800d50043d040303103800c0c00d090500b03a00c08400a0141c2c807454210b40c09813480d03030f104ca500703540c2c40c1e400c6200c05202c40c0000b0041c2e803084120224801e03100160400000070044001c1c01d04030741c000600a020303407201201d4613040c01014000219a8404806030001d54402c1d06c010501d100d03c8480142110043c3c4c460703108106885c814030000d07031404221813041c140c0140000c99034244401c00b2401600a000c0122098400050f095501a03044030103030041518400002040c80c0158480303405101d0300b4001c20000106035507076503062a42079403140050034401e8003460401818a0500c0b42011021601034280b2405041000083c1c082840754846040b50340c10302106e15007010380001c112444514006040003000303200c2d00041c0c0c0d00810351560107176020f0400d41c2e200c800030500e00c1d1250000804440041c42e42404924010b00ca0700030030007642c4242c000b8640990790540c1030400c01480c01681404940d540e0718015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 884872230 1250 884870980 884871011
    0x904020d1803050a080609061011012c0708030f030718050409110a060503070f030b0f09040c031208060612040c0314010b09130506010e1b13050906010e03031c 70
    0x201418040d0715180d1301c07910030074406411300c04000c00c410b101d00e17001c1007048410b17601d0869410204004d882e00155005105810f14010070750000c440d5100406414408140c0d0324030001c2c2c101000032441508c1381d007541d0b9800c041e40c1e4015049003d020320810320000d03031880d02c0b682070070407030a4042900f282d41c0ea5840011034100c0e41541020344040403080e54103101400c00c00340050007001a072074040e00e1032030f06501c010002e103010017140c820540c84e003059031400d0740d80d411440c0034000003e0010900e810507140460703603603845200466056010f841c04412140c094118103101e034070003a04562411040e40d40c4e090350b40700d00a008603200383c0741c0d002c01b10105181d03610120301142c020000142085004042003403102d4004d00d222020929003030010002640455400e04588010202c0320064654801c4020920401c0c00d0001100314007080a4012400c00d0b943d01003143c001755201449074a4000c01120342010601d400364141c0e1007003000940c459001c084240b45011010400102d03080e81c8403c40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 884873480 1250 884872230 884872271
    0x111042606061207031a0106030b010f021b130c0503180d0f0c05100906061701110f0a11120706050c0a08150607081821070302040b01030e0a060903020c060c030904020d 74
    0x503806d0342c940100503c0b03425007602c10340180d62000d080a11407801c1100c402940d42c0c2c030109411300410310040c0b46042640b50456041d8070031100442c2803000350308190006040b40c00031038001ea46c8508a04c40308051a00200d0a4200c04010327a4a491700080d0280c4145e58010b00d2020485180c440e941d0205441860f921030303500c44d41d1140401241803171070f00c0034809165800c200802e0301039141c99140c2911283c0c840803507104035000c03040c89480782100d8500f581c0c101d40000032901d00b8050305914503005518078008000e180c0c4a25010451a104e828108607a8010321103d000840d036044040ba2500c090071080c0b01d40040000c11492400d10140c0d90146150800b9508071a010a0800291030604d40f0604101105501c504203215400021550311b41d9110640700103400755a9922003c00c42e64840e80080240c04010b00459003c01000d20b1f1079802040542e105600500854500003042d103410011500300e008070078025402d044039201044004d501040c100007d0581c0c2c0e071095101e58a42c002c85 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 884874730 1250 884873480 884873513
    0x3072007030b09010b0a05040b06090a061e0507030806011121190c020a1202030a06020c0a0c060f09031e0b090304211a1008011104260606120703 64
    0x94401a441c500c0d000015400107000d40c3c040f0b9042016020755910b40011400807a0390448000c01c1120040d0041040e40c4100e0040940001741d9000208800380c008600b0b07120100600e420095000e0b103000216241d000d00a00200010001e00100300381750b2080002d40d076001d80040c161503031110411104803450b0300500c805010000045074450441c0707940c0701d105440361400d060580303000341190b0002d03040640d01e00604c1d04444101401c101503460030409212407980c413180031582e582c00351040700d594865030041142c20790221000401d40790312a6488203900021a00c1d56a0703901c3c15956010396000042c211b95070b20717620841045002c14040c9912030301442c4400c0141d50b030766091001c03500c4031842d1180c5034a020b258489140380091420000c1070b500c039200059141c51900d618000701140c80715030b0b000c40e42542c2042e540581050031840100304480c840321132814540940b0180c54000500c02c20060305680116002501c0e6081104014062105a005950481e0b4580c0e235107a80c440881000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 884875980 1250 884874730 884874733
    0x80709140108010903050f220308070219181e020708030f0c0717220806010f061715060c070906030b090a1218030b041b05060a0503010b030720 63
    0x30345035900155032410078090078400000b84504825901c1c05800d5210b141d07208209254001030b14004e14145007c2c40c09840c0a10f0401c0940a43c0c2c0c1c20201e0311600901000e0740704801c654141c19070303104050b03503040071620124815094080d401c40030400409003c0380e40102d188070000d40a0315a04144010040030340310f01c40c180e8032414624030b01c071603d58008043d101046010400700001c2500e07540c01142c482c0d5040d02459450710b04481c000301141500e03420644607622001c01240149021600341d050721004410b0851642c1e8451040324a100030340f10015812610b0f00c04190000a4a250790b903104a0280601d0300e0401a00400c501e04082540518406170383c07003a0500400c501c0064490b0040c55100050004401d41d464038240c8800c812085000e22005d038802007841413034001b01d50011900b11807200c4140c50a0305040e01282a0f411080211a40000d404511882c1c020169035141e40b403965030a04687c24040c0ba44080d901c0030341440c0c01d000c040c411030b0003603942015200340065407810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884877230 1250 884875980 884875991
    0x10b04030c0f03030c08031302060c0604060509011a0f0402120f040b01050402070b07180504150512030403080301090f0f06240509031504080c06090d020d0302070804030201030f06080709 82
    0x4100707004a40e941c0100c480c1201d518410804603070700160008a1079081412250340c4d0719484100d45040e104040025089040401c000c00142000b24a0500c13903406144180010340d21404034500722500c0008900c1d225a49020302409403c0400c0100402d00000d00018501840300381c0110081204444240c007181c28002000100485840b80c603005100580c0c0a40c2082e81694581005810040007501006000d4101e181d0700c05003c0c0c910401010080d20401c002607401840210700d0115000e001e005c0c8060050300c011400740001141e0032680c120912509607420003a40380041c1c081c49103c1503c0e2500c41c1420716906d906841190b0080c0101d80c12201e054a0052100195031903011555003030000c2404200c03170580700480d28801036000d10410952960303540c07610500764011400086594490131007040201500054842c00030100c0f5002c80e407506031802c10403000c2e4132074070700300903c000001c3c0300c1000194040c3c2c1280711032020703914001c0361071038560030840d1074044940d00085800c1c1c3c995 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 884878480 1250 884877230 884877233
    0x1005130821011503200f13030803070518030a03050712020102070c2309010506030c1e07030e0307230108040f120f030605030f030301270c0f03060b09031c020312010b0403 75
    0x45c4504402003050035260001801c0010989115000b55480031445e0300e400941c008a4145074807020000c0e503407203030a032500c80c00c00700d00c02001034100003008441d803100400c00e219a0300d00015400d40c5a40d150f59014609582550342030b01004c14100d40c1e805564090104d00700254040d841000904008d4503038801407104038002c1c400000c0d8802070203000e022510700500146e110401140e5005e12100e03003440d03450700081c1c080c4070b414005114202c22310f507000c9a04005c0552081d90541c0c0c0c003008800b00d41e60a5201d90840e410400c1c2c070104443d6801180d40540141d50090b0038007503001c1d00940f0561980915a142c81d03c4000c600d0000074002103e641035031107a150144030b108050b040540040c005a803c0810f0309940740700c180107480c2100c0c410144800031f1400600540c2c1c12205d110410300900100d01c0340504022922002c2d44d021905040380031400b078208070141d0300c4080004005141d102d00500b10000c1c5009044001c030700f140020426091200c501041040c024040089a50340c1c66155 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 884879730 1250 884878480 884878487
    0xe1206041208060d0f0201030b01021006150806091302010309030905090403020c03010c05040302240c030a03050604050610080424060b07050c0a0b04171504060e10051308210115 78
    0x103101901c41c0d49030710600d0300480d0205c0150040c2e181d0a08001540001c8000181d10700805405502060741c14100c0102d42004002ea040030110041d49030620651142c00400c50044022a116a4081c1c914201400550320a4205804040c000d00344600c1c040d071980082074150904980aa000d6488411140d43da030500f441100d01c00243d03850210701702400c640c0042c81c0b0170070345039680e01e2100310710003000844000070040300d5034103051200300ca03500c48100d400500034100c220b959902c80e03840c100010f0101c0c03d05101c0c03409240c80554610040307550795910f50750002d0080c400c4a00240c2c030310310f400b04c10480e984140400740400f403c40380d0701c03541d00d85005450107044a1829009800c0f03090200070030b554050a0314240d680014040c1e1364100121040c510f032509211b40c5141028513403041c002408559070001c0d2400301000140c540c21810b2a14882c00c1e201305a600040b01c00c104048280804c01d201c01504ea100020f00c07a141544004901441c08e0900a0308400c0d4601255109150340c0b940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 884880980 1250 884879730 884879747
    0x1b0604170a090614040f0611070b0316050a2705090108120306061804020d0501030b10050105030115020c03061f09051504020a02030c060a1d0712030e12060412 70
    0xc100d1519880c00022500003880c80c25103100310f009000c0d480070f1305041034900c50309950160003049070144025903908001000e0144a844040890141308404212000d8420450388100c0710107a4010507480e80200482c3c2607841000d5080c01c000c3d4408241c101c5404160700e20107000018580a17040500740001c0040c4030b241039000030405d50103401520345540000f02501e900500840f0b02d1911030494103c091440c00b01a03000550251000480220085031584628140d0340140d48100a0799030380700c251044880240aa02c0c041441030004104818003114140b0100e16203206491784c0d9007060b170100786410000d44c0c480c185610078240b080303c1c14015100300c40041c5070a0400340000e0628080d503000050400003c68040e507000681e207000d0500070011601c40e01030900c01c0f1405450029040c5006104c07002001d60080e0044d4500860040b0005442c4207031400c9514103940510a50341c103a402c14000c1d8902508110240b16540314804240f149510442c003403d40c13070044401f03035800201100f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 884882230 1250 884880980 884881013
    0x5010c02010c1d090402030a06060b041503140f060a03170a0e0904111504030b1f05060c060a0203090c030a080903010501170c011d0a06120f0606080c0304081b0604 72
    0x180f00440c02044905002c0c09480c00c1d142940d945105803240e002007030401c40c0605d8041c1c500341c00c044d00041c41100c084002c2003114040318604610500a03a411026034a0058001030000f501070081100000410005504400300030f0648900e1513031b81d0365811526416070541c482c0c80c0b41c04159040b403207030002090034030100d04485d41e031142d00d407565075507004088000c121406003010021880d00703036200d0400c41d4041d540003030f0009000e103030042c0480400541580c0d01080001804030000d62428018246d03041c031a0f0340c001420346070345c8a200d00f40080d003000703000501511605200000a8909200e034580090040034066a107080d03910a041c01c1d120b041e0301c05140c4000310f6001004a1101040e40c021119003441c03e070010840d904c2007401c1d07038000c802c0d100790300403d801800204590000710f0101d840d00c1d200410f0204002100403641100d0140c41018040b42002c2d0020b110151103100444e4440d100e00c04482c2004c0c03206608040390b0f401c017010540c066010000348024400314403c00203528 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 884883480 1250 884882230 884882237
    0x6080a0c060509130507140d2c19020d2406051f050928030204111204081e0d0203060f0409410a03080a1109010f02031605010c02010c 59
    0x2843c01241c104c0c400f011180f4041d664520204040d60f205030020300781c10b0190f480060700d030a003506d070301d200404c52130664205d030403d41034504080c40482d00207100000d00c4c1c0d0300546180c241c064282d00c4400428201240e20900107000c000000352440c01c40a00a028080807010a50b00100d9940407078250350009803040c0d03a0303e511103442802840ca0184c1901261414503240e025800c0406c0085807001810303030480b1250031102d6002c110381c0d4004001c89008072400d0100300080140281c10b881400014078000b1044800030b000b00308104010609640c807145c2a29828108a5110415401200d000c03880c45400100340307c1149490311241131900d00031142004000181d55844c409e00010711721304030b09001d54000c40d03003455400031881c150010a01d0303a424581c00d064181942c40f02d150390b50440c04210030b41c010501c0040c4600c180441b12550160b11881c10360342000645801454241341c00440c841000281e018021104d00004000c0c46000082480c80b15904081e09540b2006c5661040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 884884730 1250 884883480 884883487
    0x10300b0a08030c1011070501050702100f06030203060f180115140f090a0b0d02090118050f0f0106031e021b070602010b01122003090d0311090d0b091006080a0c0605 72
    0x43e008041030408000044030400603802d03004c2c40604c038082c0610701000d8065440c040801001035000718040500c0c6204d07440400225404101010403250741e40130294065010034000381981c1101b103161a007099607100020f00580030601001e081d0f40d44c0386584030481424020400084031811024107155204a81d81c40c14045130303c0c007184581400810310703500c0319221000d5600c90b403250700001d0724058001d0b0a071103d07583c5031540c49451410f514801501e061900c800640c1c50200010380794020315000d880030350703542d10b400c00840140128022190301100541010075544469200401c83c030640a0540100800c0304810141400815400300040da4140800c92090380e034440310f1030701c1a2000e2000050541c100c054101d0800049100e100105800002445100c0c0d03400642c000d511092998184201045030f5240b2840340200e03078403c0e8109031451034240014404010541d0721160140898050421240885043e14103a510040050300241d031654240090680440b010302076505081c0d26 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 884885980 1250 884884730 884884747
    0x1213050109061115060a1a1e03040c12082701020106060509280b13080f19080c0a05120c010b04180b10030c090f14040210300b0a0803 59
    0x1c480d0016600d000d20581101e0000e106a646c0d40d60010182140c14003090200000700815507185c0d02034880c070662181d0585c56899420703400d0040301d120b281d1146c461a00c044c03400d45441c001412829003140e214009011802d404400c14403204400003040040443c1c0c800c640c00060301315010364018000700003041280c400f40c0e848400d00c05c0f020038840d01c441041e45101a1044000326080d800c004601e0100003034500185006e940001d0580d4150802c0c1c400142e64060601c1e511a201071151614008002619000c14452400340c00e00411840540b0000e1105a44d43c0c1d04040c51403040801113403010a50750000d003001d124007484117100307841c1000022208003407941003501891000300540e8034000024145220701000800866101080380087c986a655440292a900c026007000510300102d1041e100a0560342c0c0780140d80140803002e050442d440d007141d80301000c2c44030301c24141c400059107d1445280b03040c01c0300c2d40441000004c010f21180300700021034010754001c862550041c8101d20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 884887230 1250 884885980 884885983
    0xd0804030f11120708070605070c2d080304080702120105090118080306060f1207201f02031b07151112070806040b040f05010e01050d0818010212130501090611 70
    0x1d540d10402c40941d44407081450600141d01c00e0040080007a808d20003841f86050f04264800d90301803080503034a00c4000c0a1054403405509481400e210034002240c040104020500442c1c0050084111500d41550f41d00030030b44480000d0140040e9039035560402a008200f0b1048851100304800788002d07024040d19a5070140c013000e4926440b1302070004096000b180b00030304842c0541d4000b920603030585000c901c040d04c0454460b640741c2a10048406040079800c021034a41800c01030f43c2101b14042c03295441080087d08010709100d0ba05c03204a203007600300361000c07010780300c0315210701c000d605101e0288514130262203080d056084590810303c44000101690f03102d5541c020324518200021b41d07151b00020300074150062080343c10901d4001c901c140d070102a007065050f60100f21580710942d07603890a00084802c2200060007081040c80188105016040340c2035002c281481200c039a0b19001c00550f1035588842e0043c5a0403000900802c1a541c0000c08400141140c1c24100141003054000300d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 884888480 1250 884887230 884887243
    0x40516080408031005031f1a22180b04140c09130c050d0803070806120c060c010f15060306150518150f1201090b0a050d140d0804030f11 60
    0x240090b1010001500114001207040000e050007000c0300c2c4500072003c4c2c03202d00f103000d103240c00c800b040c2862241a210541040c11b11075526010703080c190402030010080303a403c40250843d0120070703150340b040703140c0080c03000291203014018040c41009060501e080301000b6140045021241c0290404841c595190402d495016000314a8042a010103251112007661140c004070741c8444070300008024003007100040c6219139078640300c0a4076510351000b0060040c8003d400c105040d03200824040701410716201a01c5100311050002c6450710705014042d0648040b0002640c5012006408014081d418002d64000707000d11210380c81e41d02d160320b400070642c0c070030141d848940107032080d0312010070349a40314230710a40d410b4a5907258444200e0307803031a40b1a600002e0550003020101002140c0c040341880355110202000f00001a84c610748402c0c0b09003081f81c0d020036200d4400c01031100030091424000000c130760a156545030003600e82486d01400e50020388c4901800c01c800d42c3c641034040c0b030f07000585 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 884889730 1250 884888480 884888483
    0x9011b021b091614070c030b04030f080c030c07080c0706020f2404020f061c2f0a08090a05010e06071b120e061c051e0912030402040e010c09050405160804 68
    0x5102c4e50341500c094205188550680141054468140001400140c10006010310f2096854040000b50b1900c111465801a01c2c900c00d2003200b0000700303000d00d81c141d00901150340b041400c0c0d4108422001c1d09420000f06610400240e00440c145850044c81070011043c02442e100d82c02d4041d11251110041034040244024083c1e103420b40d00009a81c2c0b180305079000c11042196039140440d851441501604101c44880c1741042c51810412110042c3d81c003082819440310344d00b0b402d06d038882404a504031806482001d85000e01d06a0300d022603002c2c00780007906080c0c240141060b04040400a14000540d251520340c080c10224040c00078100303c80b051141001031422205448507080010032621509511101900d140b4042544403d0207070005481400c0c1685200d08400070400400148001110124801c1e00b00e0706100580c024818065a040b0f40083c1000803a01e144040c820f0031a00c020740c415012411003c0d0400461400b8064a988090540885191802200e0015214040c007070710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 884890980 1250 884889730 884889737
    0x11191d04090609060c110c060f0313020a0521150915061903060905120327030d111e040f06050912120307142109011b021b0916 56
    0x401c001885140d8210504241d0000c00800480d01c1d080c01c007078181e104c500f0720071109004900040ba1580341c030300f054444401c4080e204914503592100d020b081009415401c0340d018500c90b001040c80e480300040040100280103514040c840f0b0700c1a00c1d031a01507440307502c0a003043c0c0c00d4108080c1502c08182c1003504a2800d60340b012980303035100003d0110300882e844225a80340f82d0000014071145400a2001074001d40996103001c0c2c0c0814030108501c000c036800f11051308980c80b44800c41d241d50040444800d07444098a060003524014042943c80202401051070b1010035000341d9510380d040280641007210915034581460981c111003019001d201c1d040c140600451070b002540c890442d00c0f446036826900b03031002d109184200c00d4641d041030300c442c0001607024038010140340200e0104ca46103024504401c0c43d000003000406800d060041c1000c06954031001072a14007540e920302c03401d0061503a00078185850400c182d404800d03001000d403a205059171401d01440959490820303019000030725 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 884892086 1106 884890980 884890991
    0x30501090902060316020705060d02030411010206010303080a150803070503041508010302061903090507030327180c0207080f030d060e0f0109021303050111191d04 72
    0x5070000d401c0344040010aa45681e800c10001a08032284120f1340480d80310700104040c1c1e0040002c4046103034000c802e2100300b041c130040b0502c20300c0c02071008250543c51a140107200c010040c003100d2200c0e50b07480d460500030314102c140c000981015030480756180198035229560740e04c5480340c010a00c21080000b00140e00c9a1002c80c1200e8004000500b42020380546401440702460503105159603002c2e440300061062241c3c60056009498040d0b02c15104000361442040c20250501100e4820b403061000c90008000140841c3c180200080c03161b4030420243e192565580080003584200b2003896443c0000100030030140e410044280030442e40c40d5404144a41c00340e541c103480591780b400510802c4699030107450703686504456130300c606550740c984908640684490030929400000c516404408a08010324100500c2c03812510419002c07130dc029800071803100b1644100e4889 = true := by decide +kernel

theorem cover : BRFrame.Cov 884712230 884892086 := by
  have h0 := BRFrame.cov_init 884712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 884712230 ≤ n) (h2 : n < 884892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
