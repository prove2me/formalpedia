-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:14:06.068464+00:00
-- url     : https://prove2.me/submissions/c4e62257-96c9-4a9f-b491-f7661430cf3d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 943705035 ≤ n < 943884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 943706285 1250 943705035 943705051
    0x35070605040201020f1b1e090a020a02241b041202040f060b071428110d0f050d02190807110310020a080f01170a060903090e2e060215 59
    0x16007200c00171109450004101d68100c281c01d11103104025500340120001b1000200380d240ca01040d690900040e980400189000c0c14aa800300360703a005a031007000041c052200461f0b01c81d0303059003010034203c94100d0841d41100764800103500001d080a9001c12102210f48a07140d0b0800410b041c0e00300700180071244c1003602100c3d240c481c041444d45101000701500ca124980c0c00c075540d4001380001d1f003080c1c007130444503400041da4001400070301c20000d030304450036074045c0c900704501d80340000044e010904090040e040c04c1032100714504100001811440d1592a5000c4034011609000d000701c5501051030014102042417100c00c4c00280003100480c840c05005007511740c0d4080345190700040740c02c5120400005071b00007045c130a000503000c5189001d080c140311505428010fa0702e01541e96080618002c00c6103548031003c00034584607955200250407904844851800c021007070503140c041c0d4030162480d801c1c040280c0020521011401e408490407074015004c1007101007c102460580104074613 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 943707535 1250 943706285 943706293
    0x5130e0f0a110d0c02010b040c030e0c060309071e03050c03030304080d200309070501030b03030a051c02090406150f090503060a0e0a0503030709060230160b043507060504020102 78
    0x30100f242034024201e84c00141d50000a6641100c01000141d03120b1481c0745003854031f018052500d00b00041f45240410a0550f8035aaa035181d15060910701440381d4848003803040c14580340c0345800300e10b0b5031a004482c0540210707042d00078014101034580c80709440003400d15000b0031080940035299040145e0141e0074466910040010036100801ca9208552054458000c41000c1c45550707014483d00c008954140d00444c10120304220141c5036106280703140c0d581001c41d1032040c00440554040320804200988207000e0382c1e94800070520190541080e0b003000c01c1a55141e01c1c405440381122004407500100248040d4554050000041c81d000f210100309002d003030b50400100702c0c10402540500420381e0303604a0280307861402070030080c00203d269190f10442994070405040c041004804c1514008020703070365a00843c190540c003050850003030001082508010501408001420300400c41c046080c07501c0c403c2404d81195808002403c5030881c6003070000e500403031381903401f442d80148107004075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 943708785 1250 943707535 943707547
    0x1060c050a0c141005030c030606090d0c0f1a0c0d1b1b0501080612030901081305010e0106180c0801030615030c080f120c3a05130e0f0a11 61
    0x11425100303150450707440e41c00b88540e0034440d07007420107000c2200d130740d14540320341941000c0c108842203101c0504454801d40010070f24440315a190f90b1400b03505a44440c0301401139645480011510180784143d2520711162284caa01c44a4110112010170840e44007610040003025419100710204190115010284a40c4000055440c80d0f01e0a014160308200207191803074032000505a11000380001d001c0d103242c03070381c2d4818800c0000540712804070908003400c02c4d50318038a40c1802e800d01c03044081c0c45982854010640d0074019031109041e1520000c07200040c11600103c3c00c240c400a514500006180d14010408070b4032560002180403004106c800c00a9070341d4031108404141500150703100e400803c038400d100d5004001549015200b2000e1b42e080004601301181c5801035002441d407045100c3d0401c161001030f00c0d14000303070341d000e66042c1076008011000c02403054000701d14400d4002000341001c01e85405a0301024480c0ba240812203074a540c031450040d01502901140041d5980d0900c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 943710035 1250 943708785 943708793
    0x7060e030c01020f0d380f091305010605120a1b08070f2904030210110316021206040b060105070305120424090c051905030a051c0201020f0301060c050a 67
    0x41203549104104503407202d0007941101c0817030f004400d0b0104046c0b41808614188111480d68800444000f6840708414003c0310102d12400711605141e40c1c0100c0400402c03481719246c0080740b00c02e90080c4000c00c0309a864000380600307043c1181f200b0301d40368007003d1494000b41c010241e010040d14034507042d001990350b41700000c0c5009420b8000b003000700c40c0c0f80c20038030881c0321803461090803a003605c01c4a005194030300c102d10410b00c110300000e0302502c80c1c51031480c1901e001d11880000444954101c0350340f428504586001d0020101c4221710400508000780d042400000c0d046000b6600421800d09903140c01b0015129a0b01600b81201070240c00e00242155029032310b1824415130203404400c903080081c9002c0100c0c80c1c4d05807211107405260000101c046000e42480f4000d4030001d0300c1500cac060194041c1c1d034902150303d43c00542d0610a540002040240200b2001c100c0c5900301e0b54180401c1c0c1c0c001e070613400d074000c607802c81500850030700041040d0b61184038201c20403406030065a0001a080d10307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 943711285 1250 943710035 943710037
    0x308190c201603061d06010623220501020c06070b06010c0311060106050a0f11060705090103060902030921160807061d0a1209030f0605091203091b09010b07060e030c0102 75
    0x84107503060743e55001c1020340c0d03405c01d040c0f2020710070b030200241c0159810700320060078610002c0450b002c0484001d60700b5202070000303021200c0c051000070701060f4500e000b1000d002042810701805005000310300401900b4185102a204500d500604c41010740d6a244011210041c1400080d4108000080b0140072224140314032806818107641d40c56903082d01241c0a00b0400c0f401202004000302200c000c0000540030615a40103d098a44070307075180c0000c00101c0180100390460620284000107000d030090300090349401041e81e09101840c0f0640542e0150154040c2000ca107580c400d111110100056880004050070791051100007800b0031f090110390402d03900200c05810b40c0e44100000000c0c008034841003d01507507185001000641560b40d4201c500641d0b4000070070298450001c901c845c1400d000180d885030030f01c4507941d02c03440c1c5507040656904d400b40150003080d0350741441d854641040044035050781d40c0d8050b21450310b406680c6143c014110032080e0f480ca4003041c09060342a4100380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 943712535 1250 943711285 943711289
    0x20f10050418050702430504060b040306050708010503030703110a1a04020118060210320f0603061510020a05160e0a0c1421040308190c2016 62
    0x82d50000395480c00f500b02a00d010288100041c00c118000c5014403a007245803403003c1120450003108815182003079858001c2d18558000316030040c2040303808038500301820058000c0343d005003828400c41e01c80c03010503a140c4200b80110b64041e00f08100c12404607014000b0a1101100a001c0311054141601d4400110b040c414000040c0c50034002072005569000c41e1820002019040015215141040181d07464007801002610300c0e8444183c0d4a0300004085200300e042d150003080044000144d0540380d40090840720140450181008a0f01070b0600080e814810001100c2c9802e1090160381003280400104040ba0118400c040c00d0381c0004200b8031070720a00c500626481000c180c00c02ea4405694030700103004098203442e02006042527640100741c0640104260100359444004900580350010f24a03001100041c1da0002c0c4020035500c40c0b1074620070702815840d0070420165858043c1501c40c1c044108001620150031608441c80b03480d100050102000b08640e000c00500009100d5014a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 943713785 1250 943712535 943712579
    0x204090b01030501050a0e07090902030a0f05300706020f090d110126040803040309030503030f24010e060d0b04060b03040b0106111005150310090201120603020f100504 74
    0x54010803c000c070034083c0603000518164240f141221141c9117a54540030b40c850718400c41e4659492000b507480038400d10018940003071801d559840c0500f080359448589925128000c943c0d1a1408140d80307440206030184620f250300d262034100ca039140d680194105010b1240340410400030000c066a4244004d448184101c0e50141d00c40010070014080140000711414015020001c2d03074181d01c11851181d500c25070254205403240c503542421a101002500003c14a00c800818003d140100742d1085100b0f03c0306035044034040d0000b1b041072400034035504641d4082a81d00360b482105250201c040c19140c1e584090000c2d031145008005010b49406074090299202d0000500061042c16041d0303502525607401c02c0ea0303c15140b414034598684540e03007080c2140b6525400b1805c5c500c22400e40c0200c00382c0003422280c0d40340700d0080b000020114218221301003610f8503400d107201134aa02402003183d80050401c08280502024004c0c000c1c2154507242c00c0040401020038102403803003150303030040c00d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 943715035 1250 943713785 943713803
    0xd08010608070509030601170c21060709140d06020c030f03041103030c07270e0d02010606030506031b1305190e0a020f060c0f07060f021015060c030507020409 70
    0x1400c40003818015014040b481002010000c20569480c00200d40b811121a900741404003101c844000b801d010f02c3c60f007210303031100025111000c0100c9a0300c80380c04202c6400c080c2d8100d6100c1490680340c10081d03101e0701b0b8800340e18851000492400300c25420825014203c0549000315050000c6c0c00d40e8040c0c1814416044080180710610081308280000104c1c158025484d042c84030f00003030390314889442a1405804002040582100d41e403540166141e0400414095035040c04070064a621100907500015031821070b0000d2030b11b10a0095500030b1b0710180144c40d907a209d000040c000d0fa0304070008580c00c9031074011168170070009442124405d007110880004685080c050410550f0003c0c80d40b246c0a82c000c0340001d025940c0c01114440b050781c2259034030348e1204180c004d1420060700880400b001c0c0904400052102d4010569485d20500c607400d598a400d80607100e44100c44620311000900c004620b001d00002d03008061003100c0900a041650400724680d0004003035451603101221000c1c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 943716285 1250 943715035 943715039
    0x1d0f09070f14070f230703060903081e070f050c10060320030c010809150106031a0102520e090a0b04020f060408010e0601030b010b041206050c0c0d0801 67
    0x141c031018808210480b014442d1030030b00142c0f0f039044207181c40d14000d48504540c040e2090320001d240499080001004180c07000e8030f0313803800d10344000d0400c03110076008580d0210010760040b01d00c20202200d46542c213600c082503110890111801c40c00300541c602401410071000800d0729041011001800e0340c004041502c50462425940c002e541c01070b2000070030029030b10030019a07001b040d011500c02c03082ca0602c4003951040d282c140781014441c1e0035a100c0720158000710344140c0c15044000003070010b046070020b1148610049035144245030000c43c006603441c140711490112440010440da40407039410303c00b2084460407e82e0006807500070300d0900c64100003000610010700d652640400c2403405446200c0300c07074a650742603480003003000b8481c1c0d04a03801100c040d0b5603030095038060042e00380200b1450002903410350341c0d0802800706803130400300400002034801d40403040b1001d560f2100d41d4030356604001d541382400b0300000340000b2800d00701401404803c1c10104109400c001895945c401d07254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 943717535 1250 943716285 943716287
    0x30e030d06082503080a0e01030605090907030b0c0906120604021e0702090a050601081609120f020307080f031b010605150a0f03050610050d0b1203030103030e01050a1d0f09070f 78
    0x20041d5070b482e040c1041124040010440d450140c585000072414100a11f2041c0f5004a004250b9078001c01d42c0000d08105001c800280081c065080e6486150056203e40f00c42d80f1550950281d100701c25800203007044448512180c0d01081a00041c002e00702500302b5803038180c03021074103050891040090340c0214408066284c400b4419403c4100c18000700044c5c104400000c20104004050002c000a0401041d56036445450120000d140320b003400d80d580882c1d0b1500340c5454203144001c0e407280c8112440891201d8000c200d0070031101040005603d481c8880c40349100302d04030a81e10b0341940d583c852001959880740b070501d05840c4001c01000d5524549450040d00c980300d07822040042600c0c010410005485e481c50309801c2d160300d410314940300d8240c00030600152403243c81194200c5101503d05040400020146041e40e21a860701c0820f00611b000444030340c06030715044d20000303248840b104807412042d50903d030700c1170000e4450b8484241305800708489404c10f0303908400264045038400291 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 943718785 1250 943717535 943717573
    0x3070e04050105101d130b01080c040f020c0c091509040b07030c09080c2e0c14030307080115050c011505040e0304051027090c0f0e0d03030e030d0608 66
    0x2030011044942c0403170600940c1010180700144050741c22a005004c102608042c2141188540d0f0089003111700d581c4459060b619402103800190040b420255201102d94842c000d0701e42d138000f20002001ca41c0c2c0b10004000008030050561550f14620218036140c0d915501d10151040d4069000320f1007a0820380e03801012142c101c92030070104006140d061188000115110001c248202e80c0d0100101c03100f00040146818080117404d104070304941d17144c0f803d4000c00300c6108179004150b80c0c8800c8200e1a8030644a110880746d55001459410041c060000b40a00c443c020095925110f800c0460300d504281c01c584c42c0c9a0b100c0c070810180501000320346000c0c055070000c180410065420540b5240100c0c0d8043d43c120b031104184100485821a51009021400e003a40005045805500d9139a501c0c0c5000785108020700c0c000602040c030103250300740902c1071101c2200c03018040488011040d14220010034009482d2185e902041000d054400043d02030400540710003409424907451100c4940b4a07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943720035 1250 943718785 943718791
    0x40308090f3f0303060a0603020a11070305070806091603031b2a05040c020c04020a26160f1d13150503070504091a100e010e09060612030a0c0f0203070e04050105 71
    0x4a510130001c2101035111610f0b04c0044030b403503040150321340300510401e80305000010f02d512610706c18202c001084c0320001074150200e8a000d001d40e000750721040b22484d1155100c2000f400c81076146402000001d201c0c0c00380c13000f07171b5000340713121203100c0c0c610780d201c2581c1000780140840d10102c1c00300c12002800e000042400400b401c0382c003040b40d041055800303034a4006a100407407181c0d038045070f0a00c140d030151410311b001c0d031021000c4040d90041c2105140307480c0001d443c00c980c0f14281c0503144001a00030f007114140604e0329212010903d182d0342030107070007021010229401210221082c46c2e04205c40c092100c0c100040b03d144030300581001e0601d03141c8100e070350102e8419400d09081001052444500f0079404400490216003a0744404040000c034909600c501e9004442000008184880c041014081d8560005892494485a04001d442c4031030f00828085500b04000441c1c07860300800300b20311094440c0100214419031500080e00309006588503039070016015040100b048002e102c1c007a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943721285 1250 943720035 943720159
    0x6040c05040b0d08070f050d0f0201060603060b1911060a092a1802040509040602210f01090c03060305030408010519090f110f040f06081002040308090f 67
    0x7064600b40d41c0001c2e264255040c02801c040800070302d0805101c0101e0500e1402c40c3c01c9001c13901582040940182040030a40a51005500e030290200f4198800c0c081c0342d044481c0261303080d0070310381c0c0308800441c01d400c500c0c200414403000070708034041c0d158148802e070b204007441c0c90005443c9040c1d003042c50b0001058030210000ca000c842c900c0201a0310328901c41d040c1c51400c000d04c2c0c00c640280005100034400e43c1c01c46a801080c0e9020801080a01c0c0c0080c0344c6005e032000d001d5400c2c4490b0020100b80001582d2480b010302d40803005000742e407a1640f0003080c04041d4034021503185e66980740c007800c40d0b1040e0001000c59440d042040020001c04100c0005000c601d2000c022942c0d81d911030540201401c103005085484413180403015980e0703042115035600c0020000c00c140c592180c0c2000c000c1105114400d200d0003420b808035003440c0315109450480c0e80286520b0f1800030200c2c104000c840390300b0304646c0e204100081a880020748070f91104610b00441142205985403a8001928402001c0c5011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943722535 1250 943721285 943721291
    0x6210304051e100e010c0803040b01031e0b06040e07030b04140706050f090f040609020c060f07020c18060d05030a0302030108070504060302010519050d090f1716030e04021b06040c0504 81
    0x412645903c095225552203d140c651103880b2480300403a025003005030050149600842400140075660b10401d0403071703208019880744200b41954440c800043d0001c042e0030280c0000016000e414603402054001e0398013000e480d0042c1e02c86d03503000041c0303805643c240e50781d8140c00d6013120500020407c00000d4a03032810480d040071981015010144904103101d0701a82d0b0090340c19000740c9803034110700050200c9220641d1103400312109a641c912044032031104244455021841c0c041c00480e030030030410790180c03501700b03450014140c01c0c02d407120207008682c011400100c15004101c05001420001460b9500581c0e00e500d4034054510740325040c0c0243d44954074204d0304000507030f0010200c40d181444100344401001e51143c041d40e1900910043e2003090b400c004031a0100000940b0051560b0300c0b9903040c580c4400e403411403980750f0191030080000e0003002d51318500800c1c02040e000700b201c1c5004002514040c04141201c40001010900c0c00d0558000810f200030044010340c2030000d86004c8c3c50070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943723785 1250 943722535 943722589
    0x318090a060f0b0a050f0d02070318060c02090c09100c110312031503011d2409070614090d1220030d020c07050d0813120f0b0621030405 60
    0x4480820010700c01c40b4900d00340004c0d80340c280e6018000380e075000c61000108a0b01c0b00e04031360018010303512218044000820b40814a2002600000d1110986445039610004500780303038240402d0740c00c06007900da0100414082ca8295580e540201440c0c5502d40d034802e07048030131624000000e80c40c03002020340700340c002c1408580501e210200340e036801143c0725104003409041e080480d00418008110380c00126440d081040e61050020f014007908a011002522081c8043c094410901c2c081e584007480b600503402c100b14280c400d10070100706110386070f0402c0c5042ca14000240c054040f0502c03c030344540a485d00611265009010078207928080700300760644000151051f40c0324415511961316281d8013080e01461400c040290038050400a041c4100540f1942459a1150030003000c503a0b525805443c082070500c8160300344568558840c01c81d1400885940d0703000c090240c028001d54101c0d0740840b05070101040c0c815403000712010304016503910740c102401e02c03e10b080302081c2c40302800006039407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943725035 1250 943723785 943723799
    0x1d0a170601170c0d030338030a050d2709090c0617040b09100203100f080a0c0e130503160b15010207140102010219030f0f0c05031b09030318090a06 65
    0x40c04109403402ca030504013100346481c054005004022400743d002c000d101b891718185090840c049010a078050070f45161030842d40c10076540b10039000b402042500007190f2554a5030043c002c0301524001140900440a108140c0428030b1849a104018403501d80c006541407050a40000d000780c446403404500703403000721104500e102d4001c0d000501d04510a80082c6540c007003030203484411222860300755501d08250f20440540d10940c0a501c880079806a8001400540090030b201020f0303000c010064040c1c5803490346c0d04082001402440741e100340170344203800035006000801c80d0284000303910340861030301c2c1060300c90900000e1245149400300402d0301c0d82607030002032074070890b09104100f05081d07441c2c3c80101c0c064050705400c2c2c0d000c50760210314070340da268154220300340800c91404204201e882d9140c010b002d883c5115082c20100b2000c0001c9290848c0c0241d00d02c1c0884410000b903441c001c03180d0003092940d4004c00840020004111f4114250328001840c00d07080a20340209001d581c1c04e01103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943726285 1250 943725035 943725043
    0x25090b040b01080415020c0a0c031a04020102100203060d021002030309060a150b0304060b102a0b0c03040c030510090309090605031c030f09030906030c021209011d0a17060117 77
    0x800603080030151140c45504217003680403142c2025907201030b518540d0740d81ca043c8061040602084413003254004000c606081c103807034454801d907016802025030000c9070310b51030000e50018043c0c0341c001b4001019040540c84400407080d5031811640119540c0c980062040e0508401405140c242030520006d07269091800034960183c0700541d180307580da602c1e240f0300340700203020481c030840d0010344100e801c5080c1e0703800c0010004220354040c1642c0754552900303a4002c140e2117005004100c8421000440e103511225805194054440c1c01910700d04d5499403941450614940305020b0900d46401d101000c00d5400726016008028040041c400c2ca130034400081d4848003e030b40d0710b03070840304407013596900703140300307800804401c00088800c104d4600d248c20020031030015406108007107801d19030342e01c0c04107100003400c10350000300480484c2001c5002004603400c00700e220b9800304009410f10004180e5507240d050300001e08895500041c00c0a00340080b43c1050016400003921307240c05520307214680000f02e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943727535 1250 943726285 943726291
    0xf060105092701090921170903090406080106150203040f062304030302010504020117060f011421090d02030708160c0905090d111204090e25090b040b0108 68
    0x1a40c5482d010701000030308800c155100390a2180203500030002440c28096409016020302940199501e007414100c00705140c0c03c0080ca400c00145600c81d2050402860b100310358108034030300141ca00c1d00a29200203802e0ba2842c0c2c0080354035940d00d000800000f030a27008228503030f042a0018605151078540285000c0d120717880f600080c010440d07030306501110320301a15500071006080e59625503403030381402402004111412404070b2058101c081024a105484600c120170041031382c10480c0b02d1200440d087c101c4c0e04491501c6c41000d20400700c0100485280340c0300c00b4420441080036141075000c580c6440c15003204802990002c006190115142d01d0403100c002c42402025000e00304285807201600c0307065032141d50403034509810320100e00004a0101e552244c2955040603040d05070088030b0700d5030000c50707201204540c1044104060f189642001c1600514141942d01c0c00f03140c81c8011040d13517000c038640100c2d0030994900f884010454407400c030341c149003070b2070400110741c8042c000713886c0800107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943728785 1250 943727535 943727539
    0x7030b030f07090e0c0a03050a0501140c0a0309051e0610060809100209180705120a06080c0f13050405070303031406060403230304090b092508130503210f06010509 72
    0x13881c503c00c2081000c202c8207090080141460801d6071f601c1c103042d40c07103114203201160154240551020b2034541c2d04031050040706410140f91030318a885c0c00076801418a1a000ca415000b031065600071900c0a00d6078040014240303020304561b00e00409a21600c541d140c11860038000304000340041403400040c4859070500754a00180c8c2c41d0450307400030f000c00c03000c0c00b2074018980c48001000003641d4081c000d0700703a07035003400c54224040d12a9440d05080d50994011208950f101600040243c40d100130011407030a40501101c00e01c0b0000c041d00e070280c440480d4252040e50100c0300030002c0503071601c0303118504082c54219080c0c0b400c16100288180c0314500c00a009180e000c60036401d91070f1900118811014503200310b070380d240e56801070400a000c00d5402c482c400c52034500001d00100601035803180e10901d001210346444490481039884203000f40100c030b8041d07004031920780001c6080000341542d040c4440c40001c48a02a003c1d40350380000101180c9910012078240625a604402910501002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943730035 1250 943728785 943728791
    0xd0b060f04030212032701020f1c23030703020a0809010501231f02061504180201180b03040302100f0c020705010518040204031101090e100506070305040905090607030b030f0709 78
    0xc03c401303151031402440e83d11194010a004c0f098001400002d50016502c1c0c00c2e000c0c1c5003008541916075803181c0240c00080405400600d41158880c82501d018100711003407005826a01100b0440c801030307800c125108000b0a40c00110700f044160842802a40726081c200240425818071103001d411400c104655440c8094101c04030540d907441c0041100c03e0400b01e58110030f070b10320201000b503031408160345040400900e0101200030b400c040c040c04401c00180f84502c80c680075180d00469010124462100c0e0f8200d8030400403d100c40c4210003180141d0081d801824aa221030f440f60007218641d0342d50b030707046515000c0c0e00003078a500410702200304e4409081490b04c1d850b4064204118980c5440d600f0390243c070000d008400c002c900034500030041d4003a070b42c1994240c0c46000529a00f41e041d42d03240011914010100702c6884c1c013200811510384645402e03814507990701e0440098034816180c1d503a25400c03410804c114a5418801c004407030108600404c00700b4001000301d0340300c003507a001d11400551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943731285 1250 943730035 943730059
    0xb150f0d090213140109020c120f0f04030f1104020306100e0303040f06050316090806010b0903030f0a110f0712020f24030f0106051c0e1608030d0b060f040302 70
    0x106074081d80e1810b801a0508088828110540d0000e224511800200c240641c00210356079406109496030f0341074000050488040400d201c042540191a041c0c0280408201121503110020003030002540b095048015581c0c0070300d03014100300401d032801170280b8414010003446030794481d1100601c111070304040ca40c580075580801e0851090f50841d41203540e10720b00c00590240d00c00000d6200342800708580608211005089400540d02e20444445a01ca0b02c018040760700220010056800001c1c00c49181c10800d200040c4543c02500703012010030a05102c00c1d86080d42803140380103042441c406817000c6030601d0b1950403100c2072208080e00030f800b4880c5260503a02c440418941f00320428030000b0103c100c00285205681c421100c40700c2c044620000001c4280c052000c3e80c0c45c407116441e205c550089203031445002041c41404041052040c010410700e0b030403019804001811650014680d100810b21480c0c040c0c81d80380c0b00d218007a0100b04402d0710201c14580641b01075030b604940501d668a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943732535 1250 943731285 943731307
    0x106080a0317060f04050705090114041a031e01060504150305071b080705010e011d12030117010b0a0f140f060301050d141c0e01080609180a080c100b150f 68
    0x808804d5005132800040c041105d030042c000e030805074030903a02c80d011038035003207403510203401103210321220744c0510310007518002d1744000a1980000300d4a14100c040748941e00c021200a0207030311007000b01d0710002d0140000110000340300001400e90034244014100300341300401007120466600080001803c0c0c04041040b820212010345410000900003c04032340300c540d000f17089102640300300010142c420201194042020303184400c6800c89182103a10b02011901d52146a0240a00075540e8600b4107809035141c2410201400903907188011940c10480e0055002c1400000c19100e40d540401c03244055441c6400c507030565900f680e20f10092180d500e04480e101141110020160240500105201c8094035800e504280d45035038540c81d81501c0401506c0180d800c2e51300725002001040007410070303004040c028404001351000c60362816100e450f10a0343d07230040b140c44507554004082d48916850140640d4010035000c4074104440040c0400c17030692413049100440e50400301040c0e00303400d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943733785 1250 943732535 943732549
    0x1e09010e0306010e060108180d08100e07080105210601140613030308090d0c03020604121806050409201c09080403060b0901150219051606110106080a031706 69
    0x840c018040300c1c4a544c4441126456150480d0f1544c00502d404c0009034030160040401c1c3c0000e00c41d000a0003035000b203000102e5030144010300000e80350002d02c800003080402d000c0641d20640d49a074841c030746135040204004808040018039207820800f43c1050400c20400300e1240d0445004000c550344401e072140c0450468000c186601c084c511204800100740b540140c4c600c1d00c00e1540c076068038020b0303500c102d058410b108504800f070010382c40200000c0005500200d1085182450f0601d640e8404c81c10207030170482103c60300b118000440c0441c00300065807590042c0d000d280800c0020385001e8458903004071503406440001c281c1064200da80c2c100c1450b02d580a1103100d038000b0300e80fa41c0d642c1c480c2042e0b4098203104070f0780c0707020356400f9000082065440c80d107440d4110340e80d40600004802c003500700403100c0c0068400e6492340190a1800002d10700080c854000f0301241e06d4992041041080081c2141c00360b85c0184903075000b684d50800020f9104550003008210034044803c980c468401062078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943735035 1250 943733785 943733807
    0xd030309412506140307091206090b131e02061207050903060c190807121e0510061701031a090f01060608060406050a031a06060c0d09050909031e0901 66
    0x80c032101d44001d00b9801e01c2030320084055500030f440c0c41450904001ca801d200344000c131503141c000744155806001c10056014141040c90044002140d116520340350020030403420344a102c040e109194151041007048008900781c6480308107030503d0310085401083d40d0b84514400700b041080e0b00000100e0660140d010303580400c20280880300c5602d80700449403a02c0c1d1144e01c0c0b58408042046101281303c4c803c1c00090b128001c16943c400d44503105015200180c0f00140041d4103c1101810381c1c508200c003803140a104820140891240300c5c50520040d050030640c100320040400c200700140041851b1240600c0503c158a540203c283e81d0ba912080c10401c840300300800f15400c0020000e82541c3c41118a40030340c03012a170400c6125541d0f400c006040c4210312005040040c1003409103000c1c2c80c0d560401e0b500403c050b01291905c4020b01455080080050044001c240d0300c03102441035051080740181e11041c02001140b0708014000e121000861402c9182c822610024114406900c24185000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943736285 1250 943735035 943735063
    0x9010b0705150736151116140603090c060d0e03070c030c08012007080417150a0c0804110613081005060411180109050d03030941 57
    0x29508294030000c108510080d130031101d038144c041c0054003504d0f01e8465810348140540300544060300c3c103c0da864994441c0070071502130182980500d00542c2c018080c2c10420007406000020389030800005490100030315401c00c0c000c103c180100003000800150f4a104140c0441d07800b91110a51149032028042d03640f150350b464000418541c0c100802c034030400055034880e90346900c1040e01c0740540b9003207440e0040d91140c008914150440c49402160003440e070580500d42d120b29044d00c46000a90044600e111100e09921407043c04289642c0b2000b00f41d0048a00328043c0a91240c5810007040b10b80c02400c0901500e0011901c911a544d650301143d0307051030103101d000d40181d560303c070b025100c80e00e160309207290b58101800030320f840c03a140c401c0303610314280f180d86503040c0701c460700380070381e0004010392040d0501024400c041902c0d5a0035180040442c4203031740104401c51549407017601c0310901010322400100420b50303406031a4240c801c0012444480d4040d418210500b5411880c01004200d411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943737535 1250 943736285 943736323
    0x603030c1b0b0d050a0509011104031b0e1e06010e06070222050a0207061802030a030525111306080d0309080d0501330503070507030c0b01260102040509010b0705 71
    0x22418a62a00414811208070170100f2940d1703559091582642c001000d10714501d41c0c2004103100081e8410f5100d002243d28454086082e902c81352458141041540d09102c2e0007500803040390901c0c0c000c046070f5030154081c6821a61600400c021580c40c1c05050b030024403501c0c3c1a50000540b840f90742070300d440c0303890704d10701801582071600f1044000d40c40315805443c01428210810583d480c1704400e440390f5035001c1c0040c0200039098070704440e47d03000400031607425110340c0003480a804441d0100c10341d1074010900c0007035010701001004001d040141d40140c0403402c0c1881000403400c04a00309110030414103000c01c0d440c03501d281a040c2403103a0a071158a19140c0000850b43d5643d18840d081c01034941c0e8240c001151044045128042032208030000240e0200b0015100600c900064040c0c60b11030b0425002d125096600c008004200340c0040d00180e510b554801840d041403000748803041a280d008600d805d08000100b1100c0005000d5080c921400091200810504105403105483c02035003035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943738785 1250 943737535 943737547
    0xc010c050408070605030f06012601060207150e0d0b10031e0204110c030901140c0619060906030c09021305030a050f06071d0d03030e01020a030506030708010603030c1b0b 75
    0x240207904507004101040c0714882d00407034058000c2e0102c0703005502c0c81c003010105584a000441d1442aa4030031420080000e9004440d03070b180d29403d1034064003450300508034440c100350070040812509120302c81089101109030f4803a03114942806110340d044122980e856490000e00d001a8400d580002c0c0300c1d844054000711443c01c1181c01700b0400e8400c5805012491800040d4a0325015082403400160010818016550f0080745001c0d111241c0401c1380c5e00b45040d03040c88030700301241168050715001000d01d0f920301004c2d95104082c00ba24010701c0c2000003a0443c4c0300c02c2400344590042c900d60590005407248180307400d41045000f04030003000c03507000f03210303603d1320070b03180c2201030780c102c01798414a801704a03814001c0c140401030b1034040c3d010000d0381501d1801c000e0b004018032402d400341580d0b694001078107042800101640c0e191901d000c110303414040b003030525091943c0e1025007d81d141400600006c0d0f400310103046126040303441001e20384d8150401218540311680888614040003c203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943740035 1250 943738785 943738787
    0xf030a02070f08070f0b07030c080c0c1014121503010608030c010b09041106160204021902070f080d120e07090515030c012709050f010e070f020a1202030c010c 70
    0x30010380d400c4091a6003255a10600599116184d00445d0f00c0a05050001e11140c0805805800c2e603034001d143c4440c0440e52603c804090b580300310701a89294024603140045c41c185040d480e1924034440c135150051041c0111858030901604080b0019200d0a0021401d0070210714000200010010001c101007035507403038440d589030300c000090b101a50070400c0c40c0b41c491418041c2e8034030640d0011450808038149c4810410540d201000034411025003240640250705d542c40030b009041c02e01c20186640380c0140402910704402030f8005171050b04480f405101c00080420000704a21140c10405a2400c1d0840c40a0281002c5582c4010324031920100144130b1400360030103070055852280e80580034581200340340c3c84803c030000044c081b801d02200000340301c43c0b4a900c07440030700802074184800e5849009a10941c0c90640c0d12405800308a0b006111010f030344400c0503080307001400d01d000160020317103029440d640e50f040040d0401b84040620000d050003481200c4000100100810000300243c070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943741285 1250 943740035 943740043
    0x60901030e070602160905070c151d031e0c1005040309080604051c0e01090b160204050a0c030b01020304060804020907090905180d0e0d0b060d0506090a1511070b090f030a02 76
    0x5d40d0403140301605002414561501c0303924000c4200390390f4801070b450b4903240c030054600c150001c245290782da07603810107010b02000703142c521100071035025503038400340d070b120100b402c074140c10841c1254081044100080c5900040300050000307401000728040e81c40b4181941d07803c0c4198080e2100d409108104010048003191418403900b242c00c07001c41d84075a016040307480f441d0b11a5051b0104a500000384800d0102c180a07100c00d4000e603a5101c6400d0740b56000c0f40546000343c0d07405200c0f5894041c2c1c1042c103034040c01040f141c44030038030080d0300346840e1a50003814001d015001a000e50044404174644902c03440024000d07080040d030900041c1020038844602100c030325408201070240901d00441c5a214542d51010750900801c04c43d00c9500c203840704003581c1c40150055901460b600d46d4070002880c00e2014911488504002d4240c0c5103d17810700b2607180f250f207502c140c500c602c5d0901082e18002c0d82d03c03d80d000517401c80842d4003550345810b6458a03124003c4094440d40c4400304d040310700e06074005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943742535 1250 943741285 943741303
    0x150915040603140603100e0106090903020703332a0c170307091809120206070912211116030c09020c03070f1502070b060f0307050f060901030e070602 66
    0x182c0d0403c802c0080c451064118541a40c140782d00da00300912200d01d201e03aa8000303c8082090b04000990382c2ea40d0f90782d0900b200c141c2107040b000360700030031000c0081c0007074811020190b81d807921800500a801000450446022840728401340e0358034542038a909035100004100400c900007018142030101c4400f6003991140c80084402d0441c200031204a05002c10580380102c00c00c2c1c80e4658a039007407415400c0c0e101110741810304861f540b0011180410b04d1000504440032503500a42980d003400c820042c0105a2904200c031841442031220000401c0140100f40e11035036090031540441038035008175261803000d41440500e21078403410b40080d50320500c1140840348104e100405155a510141040c0e004004154005800502105c004507521f030b520005400e105907a048407140c0d000d03207803c0403a000904155402c00c07441c0c1c00c020a42c1400e0f008140320700c030700f00e0041907a28500f0300080d40200101701d2140c0500d102240200c10760740280c0046480303548040988040d5501c5020095483d0142 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943743785 1250 943742535 943742537
    0xa12050705060d0f180203030d0e030c0114091006140f01030b090411030d0306080601121a0114120109020a0501050d0b040203090607081008101a030a1203050702030f0301051509150406 81
    0x556140c1c010108030000c0e00e01d5000c1e008e103003811075000d55003004041d8451591241d0004001c801092074007803180c40b040242d41d001c1401b403070800c00801841d03c2c004a024451941c42d241050045c10b403c0e44050207460811074000e90303550307014001207024003420310f4055004040319080c070042243c0ca00b400c20411100743e085968460148404909031070552007000c01ca60008001449001e4034500020111400b402c0300480070041c28044d05103030042640000c0c840c0c0d40910001c1c01a18244201440081d0500001d1010303281c01c2e0001103090080303101d968140000010b40c0c8089810316004581c4000c401042151a4500b07040d00350b4a4401c2111600c00158441001481e058080d184901c01e481400000704041c03c02094442c00400c0303200603060008585032031004550f07404020a500040c03003820a14055114403802400741c40d0007030030344015500b09010409070b01e0b030410b050741d0442d107040301c24000d0105003e0700044188122035840340c00030b0020b48020010b802007c002c00c120342803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943745035 1250 943743785 943743791
    0x711032a100501150c0f0602090301022505120703080a0c02100c02150115090603090c12210201050601050703050708042607050406120624090606080a05060a12050705060d0f 76
    0x1340c0740c115140c3c014141e009040303510301401c1002080980c4d01a01103048003900051420070220340b40800c0300901000500c0c2c902080b02c1034020458240000d00072610004031050a046c4a42d41c060715140c001811036444507610a000d00b20b02c1d10802c45c0c01c0e0709240100040040300440e500c0207441d00f2071001481030401041c0d000241328038031012241c120700c21590380c60005509041c000c070007618900000703a5010074071035008910340203218800601280320b9050380c0b00e181010364085003007103d0440c50005592410081000598012084500706545890081c0e603540e6540341440940c061600100369103510556008001022b041312420380f0030302201103c2095941340708002c2500c2c0c880c00f0705030b5101800314590f4006031054011010070405140e56826204d105400c00640380304036400740c3c1c0c0582e1508410041c450300085c88070382010160209002500d800800300d0469080c1c0d20444c00c3c0341030691604014020140103c0c406000e0042406948955015540d005010f090080040b10741c6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943746285 1250 943745035 943745069
    0xd02040519050105070312020408060115020c0d47060307080f12071a041506050108060a0608041707060b04180c2c100801050711032a100501 62
    0x15001c10311001c0702d038143d446a140161300c0c0e074219141074400c811011740340d40911000ca400030060203010301030883c3c9c80c00103a98461513107000340340c2030b4008051409110307545003402c0031451441110103039407946072250451890400030386482c55406400416a4070304192308580c0c20390206207040c007540d41201159109034407003940c0c2e0b850f84580508224240d12003060003d44203e40c40c0074042560080d4984001c0c09559201c045519508560171102100c0540b6440c8100000d481000e010f00001c1c03812461514054000c5884d50a50303000760000c0c0400c10f40041d0804c10004250042015044121501e50600385030401c040d0440d07041710303881f56080014140044a0044d404000190801d101980051804240e95407840100c6442c8000303103040c4a081c1c402c05403031604103000e120701c40c0070640d4285c83c09400d08d0854001074450400c0200704210203090b44800400c2c0c808051500910008105200c0700c1e440d403141c3d02e40352400c143e00881e04040c000309040d0b803199040340d964203042c0610032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943747535 1250 943746285 943746319
    0x1305010e060405071502101a060705010f060911041a1b06060301050a0203061f03060503030703120c03060806041b030f03120c02072601020706090510270204200d020405 74
    0x1011030300f0405d0040c0e020315401d0440e084980c00000c0c82203002903115401d40c00500c045030743d90340190000d54150391140c4d80640c1a203264030840303000304040c03001040307000500b20300c1d800306109500c03440d00000010100d00c0311701e07040d5400f200c000f140f582e107144423922550286651901c8085640500c0780d40782c10300040c5846032a000f00c2c0d00c1801e00a240400f140117662902540840c034103410b504159880c01c010481d07403010002848030034042d440d0340742e0300c0d5102ca100c4010388100010003030801d820100100829103000600075001a407100100c2c1c00c4481014054140c2c2c01180e00c060400da8402d0140c000307058110341c000440906500050024800c034801c01d81c0da03102035100b003140480740c110315000324403001003000001d0000400058503003540c07603c410054503240107056480341c01c404c40a500c0c0036038034842e49814092001e98034010610300d001944030640304c440c000c1d00460b150b90304c06401c1e5810045000000010b95420358440200700884802504103004c4c590040d50308641d40382c003503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943748785 1250 943747535 943747559
    0xb040e04050c0102071d041a07030917120c07050f031b1507050307050c100903031b0c0807020907020a02030607031b091203180b0a02030706050105271305010e06040507 74
    0x40d580c02d081e0610700d54190080d41b41c091200130402d90740c00c1c4690b80e18042040d190340c9140e0040480c1d40d00030585503002c0c10200b0a142a2051100400d81c0400108a101c2d03034409505503c414180d400c16162081800c040d41000050303030394250a8000001c039500b400c0290540f50300e00c002d2690444204c8028a908600d4031507050f6014008190b0510005158a00c2400140240351413103003903c201911842c80720050301d403441d00c00c401207034944c0e0010601c880200301400b5541540e00d0219040c280c0c0c0c0d200c1260a10400350003030b015444040000710302c5c9000f0410611800d42c003408541c401d252601000300241100d00c92480c20982d445800049680700700d020100342c41c0c50810131a00c0c4012540d040c1c500b2112101c4200e000f02c402040007440010442c040d11600c1c2d02d0743c002c0d6964410703915001c41162416046140328035062074500b400d020703521032a48500001c1c580690030395151460450310024001400070085d40c03c025600d440e8a40c04210580030b10704c9041140c003016201c11440c0d00e9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943750035 1250 943748785 943748789
    0x170f1b010504150c1101140a0c05030f01140a031b080c0d0b181510030c0e162a061b0e010c0318030803040308090607020f030901030b06040b040e04050c010207 70
    0x152007000245240f07150107079404020f03030300054200700d841c046080c01900d0030340300e1a000d103400c0702480004118001905001e02110355200c0d04d402032843c44d050501c8520600103008480c1103030000030020f480c640754240303040041e64014900400c42e0010004030180300c0101c3c020580580180542c03484242843e48941c0320665106920300300711350304d5400c071001070303002070740da402d1103114500c00b800c4946d0901d040c41d80101e981c1c42d007540841303046040c4142d0142180c0d0100300465035050030481c0c100f40c000d405c104403408a1501c4c4800c1e600c20240c01e40001d0036143c0c070b951207a07141d6419504003c1c1d42d900c808440e039244105008132801c10001512400c251200c042e000c90303400700c603d0f40002c5c81210604405c01000480d135a880d80c0f00c1d00c429807140c004a8049000c0f803076840600410381700400c1110303408010352005003a08045130715140e44034001d80c0c0b201c9040c940c46080e030803030310394030034040e20003a01d04e113004592140e50790000c1e1307241090192070649050141c080107052a510104010003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943751285 1250 943750035 943750043
    0x1020304060c1b0906030317011a0d230108150f06011707110102031905100803042310210213030206030403200714091b0304170f1b010504 61
    0x10321460b458440d00d0501d000316148070992600b009010810b02614811900910f020355103107110540080107030344040078185c004403034030004032264081d000300200407200c10120460307001c1101007564101032039012103403c183c01014140c600202c0c1001c0000385403d5000003150b003900b401d403a4100d80f1030107c90103547c102c2c0000c00f07080705c41414100100c00340750024514604405030016581445003207800642c0c401800304d1a0310783d440c80800d002c0c00f0b40f0f174200c1c1a64040c3c0900900c2e10040c070f95070344213502c6086c0c0081103841034020740100c4048030720101c600180004003001c10350000100a0314508120305030a40a4540c24204035600d0f200b50707081c10920b0010842014150f408006003900014012400c10141c030003e00900ca11f00325102e034440240c40020415103060001c0c2055401c280821640200703814001c00c1820300041c1c0e1510000300a50300c04682e00d4a983c02c007030199500e0303041c1100600000094064580daa03103c005c09018852074203603110000c42200d000c1c01c0e6070b8103036000b030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943752535 1250 943751285 943751297
    0xc0e070f2f030d1415041b2007090c092304090f02040e06010e010803090109090e1207030504090c0302071109071101060f1502061b070609060f0510050102030406 71
    0x9401c4400821111504444000b100d0500500c0150030b07040d110042d181d10940150368040c44040350070f6403c60103034682c080320140716151000706c0303514200702c0f4128224100002c810610302c440c9014a0340319101301211080c0c4e03011036210480403010701001c502100000d400070000103103000c5680003001c8a0150429030058840200d403c01c4081d100110082c1d5203840001e400340c00599451041450001071000500b015615280e0310900c0780c0300503404280c00c1d030400c0150a98603a40404000140d41401400041c04c60040c25540e19003440458013201035940040c15106158004000d4000c50758501303024010400da110086040e8051720b2001855195600c1c90010540f03010068158000c81a140503060031400c014480d0075980503034442c0700c01201ca80300501c00803059850305014240340340010070641c01d000304510b80d04da8011041c1160034401081080400140c1e40000414641024041c445250207032038a9000384825941c4050300011305d080015954000300980d02202d0300ca44810b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943753785 1250 943752535 943752587
    0x902010f2316050105060f01140c070306090b01170d120c030f024005212e050405060a021e0c070e18061902070c0e070f 53
    0x545100031603000c101d140c0950500d5240c1c000764034030081c0c1040000c02500a03007084050824038215000600400c0c042d80e648040702c03410740d805c00300407111010302030a0551b40790ba100c2d40c0b00303081100d44c4d080104043d003414540801e02c40400602410303038041c00700746c0c100c00000040031070307882401680c0800410300700320282c0840c000c164846080c0307155506000c0354050341c02100e1001c030f0303204280c607000505c6400680c043d201541d4901420720006030711003640c1268606201c810901c2035124a502ca80b80354005100d00754404138101100d81d02c030908a884952503a07004092002d00080c0b009030303804141e200054102d206002d4540100e4100c800ba0205403940000300700a0350103103040c0c460120504070700d141c0304103007400148815045840a051002d0601ca0240030141016180c107844810100200d26005004101a600411030400f15404890f010107480068042c1c406e0141c52808035034800550440881495845110181d50b6008081d00c0740c0410ba885003410000b40150340310440354 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943755035 1250 943753785 943753787
    0x70906020a080d09020a090608010b0105181203120109270308150604030b010905160504080616120207030e09070504060c0f0201090b190f080f190e030c0318040902010f 74
    0x51012030002040841d40c132840d5004521880300030b40c0103035011a50b0340f50800c0418400e101d0700040301424a400b40c54240d40315402034840303490185075031099212920001c882c110800480c0e01103007981320060165a515841c0000a1103c50080c881d10440ea90b441015018034403509100701e5413644031138405842e007607200c000704560055070503005942004048013040b0103055007402030a5a040118140c50000700000300700403403820b80403d10900348010300c400f41d030100300302d6030041c1081e0310f400a2507800d240c00c0390390030b51010700c07080003030310004000d41410b6000c1944410307050140c43c042101e8981440440301d92060303104580010741c8145045000410019104103498014504202e04540743d031100110f981c000383c0012903000c04840111301c0140c025007032401240f09810306901500c5c0041e0148409840101420004103848050800004145e0b000e20000341d4040d0480c5d8a504078540c80d40d98990264203a1082c58484212507042c071b140500034510740c1c1d0343c1a91502c0c07440303003940d80c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943756285 1250 943755035 943755037
    0xc0d050c1b2d220605090601080a0c02010902060703080618090a0605090c0909070608060910060c03170a060e0f06150a0504120b0a050709060207170a0501090b0f070906020a08 77
    0xb80e0800a000d8118001001d40d658001d080014503820280c401d9411043c030040c421144540d10150040c95880304100340d680e0040d54003035100c02502030200c0d01802c002c0049005000508000f580070300e000c40d40b0414142e003e0700583c0700ba44244c5100c0607420091903202c1c441441200c035114554000082c8900151260300681c1d081185041215040350124002174220741040b1506461030703104000400c2074542c400032094101300c0a40f04004103041035190122900e8090042d10244000110b80004042c880e1004031009205080d10b04010306203100d001018144034030441d0104180f01002c44d0134603100c9c1c00410f000d4400200200400b50200e01061126046141c42c402404402d0200081381c00140002c0304030700340300341071020b4545081c1e4102c2c4100c07840600080200325200d03806101a41c1c000034210f01760f640191700d050078414400c3d041441c4c1151080000d10340d5080022150400003210f0b0b810340140e200520301e07003a503070381d0090450b208a260b11a040040e48a6004c103000700354020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943757535 1250 943756285 943756339
    0x4110109050a140114030a0905150603070611030903060108030c070b21060109030506090a030f0206043207083a08040c17060a06140d02150c0d050c1b 66
    0x204105c0c400024003600e00510380c20407180b116019440d803e0060030000207104107002c550404056044038200307040401e0350741f2000d020340824031200440c252051501003054a09040d002001c44100b036848100e07090b140e801034181c545c25485010343c0407501c440b004098445010541d0a10701001c0c0200107450303004180a400745042c415401d0740031002c0b0b8828001180301712102d800811076807002e458003c10102c844500d600031504030a00748000501c4100b80da07042d4242528019004082c0c01400541c2c5000340d60540302244981040051084000b040d00100459055211801400004505445490071990b800742420a0703e4804156601942c50300d9005402200407040c41501c07529101c1001c02e03540d960603842ea00c12010016406824011040a0f090625860720609a0840458440418048024481d60800360f00181846240c8140c801902c99001101d0240b0400800545aa407018a008859000303080080d5aa20381200f0b0341c000d0100090301185415003110805010000c6034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943758785 1250 943757535 943757537
    0x81c020604111c0c0e0f19111c09021003020c060f100e070c410102131d0f131b09020f0c070e01050d08070f021804110109050a1401 58
    0x102c01182c3c030034024440400181ca11900c0e2208010f4280740c01420200c00c01000c440c02000c9a0040102d09905d4055000880d40d0031000403608070240a01c81501d03010b442e041c1201d0001801c40d14503032030500d400006645000755076500705003190400407001da12500490720302a03840000400c00c0080ca5800340c5074480340b407101c01442d050f01c521381c0142448003503030741000154000d540002401090741c50402e554850f0b00303070340007808001030499101c044048064900e04001d140c017041c0a21080d01210003601401c1080c00590751614100740080780c00c04030001c14081c0b50380005407141c40d00d403810750244016000080810b60581c0c1c8034050b110040341e03444040349941f903000404050301d00140c4403045070080301c0b07512000040150352910311980d0210590050002c01000030b44c6034204840746280c4c101c40c0360b940e1483c4500384036151000442e002900311204407500c1800d50311407a9164000c611802000c0300d240451801150306a02e079000d01c6900c28a01141001301400c1246490948501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943760035 1250 943758785 943758799
    0x10b0111063c070e010f0e24130303020d08070215010e040303020d060e01090f09150e03040f15080601020f060f15090c04050319080d0c09030f0507081c02060411 71
    0x41c00128414010f50b1201c0100d180f1007502c801a42e00b168005a20840d04d10b890b180c1608114001846403102c0b503180441ba80381544c10f02c045c060a0000c856484280300c020028581c0d0f6807900035500c0a45000c403c001035002c50104085600c00b04d48048012480f0481c510300341d0030000381d9860044c0160086081c56403c1120701a8201d030b81c02108001d0250400f910007641c544041c900035140815000e10b4030760720301750b1310b00d0004804080410705480c0041e00003a00c051041c07401071440c0301e2504400a101c80c03070100040c10488410700d569003680d459640c0ca03003a40350031005996842650b031003082c2c550080d9001035141181c0010583c0d1001c2035150020388004028042180100700b51644585d038240000c00b4402403e0400080030030345902e034005c103030700308480e00c44018a0140308810050746d9110045e0a0540b840342111030080c42d04594211a442c0d018a4081e0742c8226502c42e4400600400001c01102d4142d500e9558012809070058461940d8941d6031040082400032510f5009103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943761285 1250 943760035 943760131
    0xe1b04140f030f0a1712160311040902030714091027030c0503010e070803030a0f090c140909031606090203250303080907030309270e010b011106 64
    0x1d402c004244900380d06030060011304c141402d00240910700c40038680301e210010080c0700008000c03e840917a210700c0c4071031552450112080d04801914490324443c803080c0c008100860310341e0180d402540540e109840d04240340800004140d07140c0a030036001d6901080885005a88500440c0445642803c0c42008101d00c610504a01c0156109400503504800382c82018000c508013442541440c00c0c510005000c0c5610701150b0507664400145040b108035210000c1564280e55034100114165010055144040c1c8404c50601002c9030310041510504541c80412411a4040304507002919440441500085181c03038201c0a400360708022178061090700010400c40503040d11056140103440a84141d0b5851030400070107612001d080310015800903042040001d0f0070000b008201c80c20345401e50790449071800c0c00b5414556050f007d10b026400c00810f80340d6003030198060002c3c40c009880302c05121902103640d0f035070741d102202d8035045100460100b120280e085c0113000f41000c401030504030807003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943762535 1250 943761285 943761289
    0x50c011b052b0f0603021318081303050d0509040b120c0d1e052a010c39080d09141203071203060306060e132612010e1b04140f 56
    0x80b102c0d0400d4003c65954401881140b07025200d90306000c4a050050011a805d00f15021446a1054000701140b070005120b0b0040356480d400900215001410f80c4d440b00c402200107811075002c040098070a600c0e00c2d158600c107240201c222414041400300030300780d82441005000c0050010303041620700711142c1d010009d20341c003a034400ca04100e2281c000f80c260001c103000c60207040c00b4021810b5881c484013100007211a607110501400e800d4001d640c2011682409080502403255a4010610003a604140b460041c0302041403200700c1d00b0071422100301c0900e464080b41c030075000380030700b00014515140c80041c0340b40403021800420008401e43c1e01e005115610078180d40c0f96100c1401c0801c1d1070791001c01c10701400f0701c0703200300901054000c841146040c1a014041d0860000c0c000d0441c150540302c0c58000d0701c80700c684940c00c4980c4d2551940c030442c4200040e0030000074424400c100001c0c4001440c250340481c4490240c8039007444803401d140c00c040500c007440c0c18001c080303078010b000500302451039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943763785 1250 943762535 943762541
    0x2012127241e02090a05150304030e0a05040c09051009052d06070b01080c090c030601080a0b0303120a0f02040303140f0f070609021809070303080402030a0b07050c011b052b 76
    0xc0b40c15510010307910040c04d42844120195644490310031441c440c4103a129010342804c507940a5817602d0106c01c482c044500141c42102160003158006107001001030f107190700403600e5025a4070482c1d112420505142c3c04a07041d8a15004054010841403900e54640300d50b05400c0484160701211802d810343c090010940c980c000c01015100c0c0c50080c0010840400e090158200400342645d4140c00c074030b01032840031090311028002a0400860f040054800c03400c0d5032014800721030050541e951284078a20840c011320050741d001c120b00340742001100d036441c103038400c540071a0350684504900b031504c1580070407182c20201045183d1030080202d6290109450010003106204501c0007031024190300501c10003180c0d01e00301a850915000c1440b200d01d60000d01c0f0f1044030340c13500d00800c060703640d032020038103095400c60001c16000f106410b00c4406074201000e001c200e0880700c02004411900e07000e14440061208504010440810410388510f501c0841580e80b20039403443d02160303100000542d400c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943765035 1250 943763785 943763831
    0x2191407080c03031b07110918010e0109030908070509060d0618030507050d0903020901090e010603060c050406020d020604230a02120c0109060302091c0201212724 72
    0xb160000000c20076410240c113069410000900505400c25803030783d03120a154204020403c2c807d000b900c00181c4c1c007010041c5443d444500403802400541505e0a0301800303000c99483c03c0340412400307080442c5000000a072174088900044c00110b20b51501400d0003102c1140d8002562a0342d16842c080e01400ba0f10340d412094075100380d81d407555851581c10181c0c00e103404074a6900c10007407140c02c00c2002d41c1d645140c003030548071500c0000460701c509500941c0107000d2a0b10040c10745061111045540d9004405401160403a400b40d0315409070580b4220780f2013030101c03802801c050003d580003089022030840700c0e460760380500c103e80d1300c0c200c01d400151505440d6030f42c82800e0382c841c440c54007465a1000d465002030450303090030341c03d1440c10400281e061070f0069076981d840e1078807800c400c00c2d60b11031110b01082076840c41c40d1420300300c0c5840120000c2c10707508144900c200070446100d409802c04004143d11131343c01c0300b4040000900c2c9419040788041c005800d40d000307900c038900704101703072152004004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943766285 1250 943765035 943765057
    0x60303392312030a0f1505040c0203040305160e010510120203150d120f0201020711040209040b150405040c0f050a0f1101063c060e01050f0414130219140708 69
    0x346a2800c40104001d69030314043c1017010030704150240b4080d4000112040640b1022a004202c140078101c04034910b0265900162862007601c1d8040800e07100c600c20a8241c030000820a000b9031f03215024001042c460069640000301360340c8003840402c0300c540c0a540c001c07040a80341c060501401000a40c4000d880c0c03400d6800d0f2140104280450343c0040c00340c41458002c0c0021f60400756030b41c0368240d200320351f1f00f00c85001d2900001d1b550800c0e6a00e6014090134040208500341c00142c100703029841d508035006241c00307680707030441c40f1075418081c2c0e1803003400700c2c05642c2c0c4601d48002e041c4111410441e0b09882e03c14481c000325866407014080c010b040103860615a4400f400c04c0a0440e00680382107480d51100a003041800d00385100c54200038070b0107480060800709040048100101d0303043c0b00f420280701083c0c0c03002c00d01045181c2204055102c04e80c040350b02c40403014000039440100c0c411083c9140c14900702c04400001e46004001030086c807500c4c940310600704043d0303484141c8a58041c12070f0744 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943767535 1250 943766285 943766287
    0x3130618061d060114030c09100b0f0c060c0f040b180301020a0216051c1e02031c0215060604141203070b04050d05040b04060e040f060303392312 64
    0x1082e0b0620820800e401880c511486404400401c404681c0721100220031a0041ea00c04c80058103180300107845800600d0505115555800b1070141c4802c180c005035010715450040d4400f05503c800d001090b5124060075840f480d00d02483d00300c229211360f02001480045400801501c051a5001c0c809040314503100d0700074100c000a60700d02403003000526007000d441006c3d224455414681000c084014082c2e100782617071003c0c99444a01103102c68200380c004e51500c1220440c10310503c01c24618110540e4035021a00d601c1495030003010441c4044445540216060000304100100004034408080c0042c0240071a5080301900d641158090701050320728803a40c01c28801002010403844540e040e06103407807401c25003003c0304840c030352040703204900400581c04c0c291407469880b50301008003480722840800c2120307603e02c0c002d08650046d51018030b07842012078220f484403400485100e0340132440160300f2724254051b80c440300d10101090f40104101d28904489000d4042045000007400031680340c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943768785 1250 943767535 943767581
    0x61315030803012c0a0b0d0f120825080a1103160206060603091504080409150501140705030412060b0d05060a18031b0516121203020313061806 63
    0x900e0041245881000862113042100100ea0b480134009600302c5005100466004142c100040150481d050081c2241e111901114100a03c49881810b401c440c1d484410507503488c0c25500c1d078904654458a014540003504501c00e032841590040c0e8060290500096404008885130300ca940003150a130b411101c1c2091902940d030780401000381d000320211043d901d149480e4007015101c0ca594000c4000d05410741000c01d0800070f400d001d840140640301010003030540044107074404280e0603c2000d0210b0008002c1502080555086074040c0341c10200451600d8a41003900c4049003010034181e62680c0d8a034041030140d86c1c0c0c1c40541074040d0081004003c1418215a1030084a0b00303100c5019045000d1200780c8006a04814229018400e54540d03409401150a00354180b921040c00701310b1903c00c405000c5000390707800704280850743c00354911a41000d040b940c160201c5c4426240c2100c0c0704541c03411080055019081024004600b01c1400d040e03150b6680c0e03600540320b11030030035510b03001c1551030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943770035 1250 943768785 943768799
    0x94808010e0303010f030602182d10170a06050301060b181c06020306010c0c080a05060912030105060c2401030201080a0c051c14090f150105060306131503080301 71
    0x1c00704a841000040c40ca59407515022100c1c0703071454030004004a4000c650380d141c4220020110302c050002405c1801d5030340b00054013010b03041d403054034480096013950311045642403000362903504d054642c440c880141c420070095400c00c00c0040c00d42e10619214003000c03441c0d0702c082c02144020f040c2d516506443d4150141e41c0160b1144c03c800c0d180c042c5445c510300304201c0c4620300d00001c1d003e03000000142d07030b0384840c4012100d100c080380010701700025144001640c140b0010b54001158080c100f918001e41b15096000d44508080107040501d007820310050140e490504001c0c00d00344043c034122070401155500d071a40180e841a90506005081c00040040d96000103006a026401d40000c102d00b181c1c003a4054118000c1499800e203000340011014091400c0d035110950320800b004035a14981340c40f502c074964401c0e00444608450203890000004c0d0740c3c80041c003d040e140c0c02095a0f095941e00403d01c084042c042d070f1754000352603c510940020002e603905100285000f083c51136640d60410701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943771285 1250 943770035 943770041
    0x60b130f0e0c0f0928080706020c03030a030509070e0f0109050c21180708100b100f0807050f161101050f0306040e0c22060909480801 59
    0xc001e070310085840d4100441c03140868100ca080c5901c4050690b111196000410041c1402403124481281d61500700d800301d480c00420082110050710844180e0b03511804102c1e111210038072019010b500c10f006c901d20700ca021b83c0000b0740c043c40d40800c0380d10065981314002010b2000752405411551888014032243c0560b001d01540140103012092905c003030390140c82c020241c2d030176403184000c41400215022120401e0140700021751002104c9445881c2c034a010745400c420202e645026180040311051f90924280064455010303403225000e1004586007900c42c402c0061413601008020892071103240b103128090600018107081503001c80c0440c0c42c1030161a10306103204d5040c041c040c4040a9503409045c100d07030b8007020a58020821851010760340d49010701c0c140f102c0358840b50341c0106201e0b6850465848155013644501446407076a00e150b4103040f50b1280e000603103600241034003071042c501c000781c40b2103080030903000c0345048929034031140000c0c03150225000d40554103042d0420020000340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943772535 1250 943771285 943771289
    0x90103090f0609030e0d030c030e03011b050301080c01110703060b030118030315240c0f0605010b120115080c2206090801060e0f06010f0203040f0f03060e01090506060112060b130f 79
    0x646d080c4100340340c0362070207007032401e4803000101000025a40200280c42c00e4018160135111061070811300340030030340080d1094000340a1822544512006040c19610850090080c511440302a04406055071100e401401c14a80481e030551b40b510421904010b2042d1040c00b03481c0079540000303c090f011a0401e118521a41c400780030716145205407600c1100b410240a03120300e0500f050500340529203814402d0300c14031203004d041c00e072074680000ba46845000003010f0300080d4002c48c3c801a80c8800901082c58500b4400000103241500000c403004110f20040821519140303a906c200c4800840404485d200340d0044070000d8200e0b0307005c011404090142d0409000d4940c4030130b2242c64046020050381000420b011f04000d0f071810410072241c001d004641c09441e00c0f440d4040220b495080c85261401d042c03100f12442c80c5800c00c0400000010b118a80d1400d0b4000d001d05401d88030200111a25900f458139155420b41c0d561001402400840c02003400c0310898508101452420412a07580c580a0f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943773785 1250 943772535 943772539
    0x70f030b011404091e1127180706030507051209030a11071a090118150e0d0c060305060a05091503060709030308063a1511030c090103090f0609030e 65
    0x1040c0200000741c800d40d50402d4042c2c0401d8602e044003506e0404240d0508802c06c4c082d001400241c011000074110344449215480005648107141c90b0380b0b00032072522100c0342c40c00d406504598030501c0840d01c02d402080c2c020030740b4544541020b00e008541c0183c52004d4843c90b03915130001035030113846900045e11292502c00b4801400e00030b80b03051850000c0c2e10b4400790014001c0c000040c080d4083e07028142c50039102900003030588a4070303241c0e81100c4020160f4540c0b00c1c08a41c81c0c100c481078619008402c46103a82d804500016128034010040e00030344009020a940809034420224403900c42e10441c0d48030b42e501030141d00c0501c9240050604100001c0d0209007080000750041c4086608094038541082050380d020f05808141d102002c81d50042c0280c6071101c2200388008801090320b03428500a80b406200c801e000340c100f600d03485c2c04440030104810b605280a0000540d0700d90b401010303011060307041c1000709550055070740c0d041c4400c0720104200d40c15540c906115041c9035108002604000c02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943775035 1250 943773785 943773791
    0x15051c150f290d15090c120507050a030b0609060c10061508011401031409060a0f05010807090e0a0204021303050c090f0f0603070b030907060219030c0f0302070f030b011404 76
    0x102d41c18032800891000c04030150014006903520001000781d0080145540d82c429150002c1e8884030044043c0442c03803a400e000584240030300524178014814240299840d89070746240a030842400d9010b0400c01c00b0143c0d0160083c4203003a0340742c4400d40189001200c1d400039060540000090b03c2c00c0350190b030400000d0169030b00c4038046030703030301301c0303561419038024211440302d000305a40100d016004070940c0c02152941407003845460840000e81d54062081e143e4244040190f401a54080700d03000d1003456030990003145c1c1042600200d900c81e610006842d41030740d408000540224080ea8014103a4101807900103d041090004c103000c40ca113410380458000b4040e08060500d9095100c0c0501412001c510000c0407941c541c4e003c220070001016011400e980702d2400040082e00c0e00303103a00c280d0b03025008103110f038009000c0010000c0f625580c0b40e252007455840c00d441e80f29414101141c11010b51151000115940450100c403130001c6214000c24001c85d81025031000c803840d8201c1803e409541 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943776285 1250 943775035 943775069
    0x4080f070b07260426010c082811030118110a030f090f05160e0f0711071a091215040227130201030c02030415051c150f 53
    0x105842160702854108207280703000010b40865003441e4014401c0709100300d00c0040d00060310b40f840494116580f5032a40e4102c1400b90000c0c0172400c2e140320002c1003000a01c00c0e000500e40524840d103d42d00b441450741400d25a9011607000000c072640d8100d200c00c0141c0120040110501c1003030301906046c038803030301030100075400400b031041030180110400a142e00c490300800004034640c4615090364111415400420b0385003019070b1a0b00108603000c046084a010100b1400720131040c1e46d0040d840c42c00c4130a4650b03101e400444803c5200310300c0107000c1c0180840020b18841e2079445c0c080c1d07071040d001d8135960740904100b0010b019020700c07003030340407a003003e04030003c0743c1c1d4505c043e150f100d038050380c1c1800c0740e4224030222810f49610403859180c02c078640040c011440d011041e0307601818800c2e241042500020041603a0317034011485400f1081114800d59500244500007500c1104c00003a04003030420041790350304096031540589840c0d000f0720043c0802042503802e2102004080040d0702c045051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943777535 1250 943776285 943776299
    0x90b010f0f2408061503070903020a0b090303090609011b030504080106150e041d0d030b090c03060d0f060b1f022b2109080a02060603160302120a0c080304080f07 71
    0x1c0600030200248043c0300001342598481d504180d07211002108610751781e107040040944034400500085c3c0c001c0030710000108036007220b030040b6801048028015420070307000384104907507039101e801140d041010401b01d0f804d92a40c0c0140308281c4511903100e050f100d80c104507515086800380c1d80145100700032102036a0041b90003209280101c0425200403d103840780f440307174204503d502c0062140c5841040c54480806a15500031001840100c5920201d626146000d84040c00103607100c1b64000180580000058126a00a01628410100805d4403003241e4002042000e010400368291440000e00000803603040c40007d840000880c829008008900300350a1030703103007241015003402081c038084041441038000400500f200c104051100c018945440d80a540180c242000540700e0715011032101d10b40480e10001065034074060094940c40d540030020103619130806100c0900074980a0404a1b004010760070240c0201d0b8000e6540758600030f420340c07500021040c41c0c200d5411020081c0120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943778785 1250 943777535 943777589
    0x30f1a1003060e070f030b060403110909010e070e0402100315060507061b0207031205030411090604020c0604080307020c030c03120c030c010c0f12020c0706030e01090b010f0f 77
    0x54405031114244620121415401040e00703800240030401c40c0010005820390040c032039004503056550500c0101d0b101414400e8034051404010903443d030380c00b80c5440604148100603409019100082400c00108050508005050f00040070f588544000c200560400046101c09034009140402501d120001e9000c0b1f450038600510301000307400a001e60512250b80c2050070f1907085281e41c44450000610003942c0e51200748411522600c00c801034142040c00741c000c1e03d128580240c40c29204040391020000140c1004024a5000382d0921030006803210410103580b040e441410040c1e5030b030620b00300281c07a240001d1034461080e4060030510744591004a000380c010481406001c0c2c454000041e0700c0d045005020701d40520358600b4422580d46544529013228001c041c0d141c1600d8151030801c440b09a1240041400341503000b4401000302602c02d038010440c2e444002c0001850820b070380e4680004080c2a807102c41c000d80300382428000d00d400124400001d24001406403c01740c110010b001d40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943780035 1250 943778785 943778831
    0x906040b0411030312131202030c280b0403030905070503010b030a02060a03090b071701060e18040204110d0b1807080f04031206260c030705041805030705060106030f 73
    0x7030301c4090150811030f2001c009444117017522816802c070501e002402e084031800c02c00c006660054800c1100c122403800071040760f444e140030b40d024211b0720000394140c0d1040700c02c103450505103481d5040f200d008142c040503c3c034042c5106e40ea012482c82c00500b0440e18003111a0005da02c26498100640000da0b0b00241141c41964151071083d01d8094848040d0024001e2a00150846d00c1c0344003007210007540402101159480380480b02da25988405048507007614151502e90851042410301c0c0000f0010101d280e4010720041002c00d00100b10240050a40c21000807480e2017a118413518540d8074007802840706515015841c040f440c40c2c414001041098060b1403030704521410301c041001d052169001040d8a1880c50003031114699610a0081601d200640f18271200745403103e003040709002082480410b64000c00400b012420803003004018003070b2000c44890702c1528490140014002c0c005094603d0241c3c0c00b810b481e61600134098165440340000007165890070411403110380c409011801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943781285 1250 943780035 943780043
    0x50a06051605010b090403120f1b0c0c180204061d1810090510050108060d0c06030c0c050109110a0905160806060d0e160503070b030f1e0910050906040b04 68
    0x21941c5450500074010511200030f150418a202c0030002415001031040c1000441118204401e4080b091188200c6582011203180301040000c5808058481c0c51002c11050285c1040c042e4660794580c8403c10541c40b030040d508045e00410704000d11500500f0f2020401242c2c04424240d035150b00004000a00c031000020100c0d031001d01141880400c010048043e0a44a104000d10f0030880c807c4021080301c0e1181e140000c0d0030b20000342180c2000d0b401e0250041d8800c0c44590400c7c200341c0103502802a5407042c4082210f41c0c5444008184d003405840f0145018560302d40e80341a484051144083c01900a00d034024101000c6c40000d250259918000f06401c1c500700c039860300c07142d000413450700c20310600e11007480c1018041c011a030004036208043c0c060b404141c2c4a461759510625803504840e10400012060510028510400b46280d05a00c5804264128003440d0003904a03100c15100b5070369a100c5a21180004901c00d4861045603003015a01c4010801c80c80e2a685644200c24000d02c020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943782535 1250 943781285 943781317
    0x2e11070e04120507050a080702040c050c1002031e041505010b070f110402070602070b06090108010b060403021905060c0609010507050c0606010c1104020a080604050703140103030f180b13050a0605 86
    0x11411403051013680c0849501400342c0d0305498040c00c2811642d0040502680308a00d40f08101c025a4020801c86040d1440800a8440300400b4400f001c002e4000406a08417410701c002c3c000092412080e409100e0780c41a02d0360075a0748405500c42c011140144c1102140c0c0300104100008108400342c41070035203a124506440c6450241c0119010703011300c030001010340d4004070300d4104014039050340d5846500700390742d18446a0703030708d654441c01c1e00c80d40540c1580090040005001505110742d40160b480404052070300016560800700e0f803543d0003c2d1801032141c0000090040b400402c0c051513410007a5480e286003480b0290a410f070326420050a2941404600105841002481a40b00b270039000014030454071030b07407230740000b070503a0400b26641880703140b84c540015810b60080c41040c80900c440b03030801c9010703800c640e0291803003e00480090140100900d440040345165103540014200586041d0b0300c1d80103c030890303802e889007a00598801d0303104420600c00d8660120590b59591900c204030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943783785 1250 943782535 943782563
    0xd02030d090503190201021804021303060e07150210051b0a23160c05040501080a03110a08040303030e0c09010b09101110050711060402030601142e11070e04 69
    0x2c14030310310401c0700d840d007a40d843d6a0a504001e4040d03000d0107080e0b00e0800017080244044c408c00080344541095619020106101403000c11225130041e0203441d4001c04940845407200c0c000c3c0c40960448851000591240040c189200198051207401c03a00315405400d14405200042169005103104030b400c00511a00e2507100011050380048619544404241d07074448685500500302c0980b0f0041e990210000300c0044c0c11709051003680c4c12111140c0161050003203a135811500720002000c02c0c1c2c010b10940300070300081002c442c02031008510903140042c20361096486c80741025003c90310948200c01000c010031040742e0745400c561030804e003140c2105c2804c1c0f00c0441a128081d108442703500c07034031405220340303400152a4410b501401103502d4003444038492404c12035030303040111070094060304414010480560b83c2100d481200d44020001040355060020703070421100c2c003c500d0403a10198200b00c5503601d40000407900c6170706154000e451964100000000900301c00340000340351480000716 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943785035 1250 943783785 943783793
    0x902030f040b2a0d3210030b0a05010e0a0b0a05100207081005060102010e1204060503040c211e03021e011e231e040809030724020d02030d09 62
    0x24611004883d00c2d40403856807100226401c441d00510b0442e02600d2912196000c10407400700d5a54521003074406001a5100020980c5114540903100b240d810846803404400100728181300ca104500e840c4c4001695803520102815000000e000710203003501e80b100500c0e950b02c0d540b803400c0581e4801da8004084003010241207160110715030140040740200b200c0003a02403900d8003c540960300980c020300175040c1c000c40094031202e0906000c0b8040354100800c008090041c009964042d001d0408400000d42e5080d841c08501d0200811088a1406230982c0003046030b0482e46500400c0034040081483e202030390040d60320209204103960303150300600c01d50a1400e0940000c929649100c2e110401899803c00030350250041300984139003100500550060201d40301100740c811450b51540024007030300100c80c6240e82c100580151080e031010040b0786c000f501c081028200509902006090303103285111100d202c01c6d80c00340b41c142150001410054510343c0001583c0c0c0c10522408005404c2d009450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943786285 1250 943785035 943785061
    0x10090803030a0c1403010b161e0f170406020601140109030c03030816050408100203090a0204090c0e0901090b07050d060e1306060801090309030318150f11060603191a18070902030f040b 81
    0x54180f07102042d01c140c02c00700500c0d20384a4ad140c5205902c1880d41c41d42d40f511200e00c60065019241c01a40071000401c4216076405c501d2640c0081030510001c0d0700d4a030f40303c400740c6c0703c52500280d0124402600784590300c0e4420a0f030003418261441e00e5401c060420010381d4480c10241d1005407101c0e00400031448610b4240845502580e00900030000f020303481c5041c0c60400c49a116400f40728021034002012943c0600401c88d4050f40444100001d5590340e1007030320681c01004800304030551f9500042076945151100a000d40c52a1402c80c89440701c5d0324001058811503000346500340d05200500c00000d0300b11440034140ea078182414a0138941e01d10070a415030110754049102c0e86c5a45c4e00400800e41c000c03d012024603072030758400b228441d0b200c05450307035601c007a510700e901903000c042281628801c1c4a00c00303412502c142e20f241c40090400c3c001e541c0e003840648006001000c4402c034a001c4607010042c820081044007019400d5141041c4078003c00174001300302911101c00c180001e080c0703070b103241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943787535 1250 943786285 943786313
    0x605012904121b08010608060106080c0901030908480705090c0d06060c12020a1101200102030a0605030c030a120c06020928120206070210090803030a0c1403010b16 72
    0x400218030160b4411900317000c0e000034468844940200000812114483d001d414894503a2004c800c2c9810142001100100302004058071ba544051120080140b071440150100d81c1e841006045000340b01c4500a4003126415668800071f17103154821140c0c04000710300340080320030840b4911050b64940c508100e852041411107a002d43c50020081407040c2c0146e040d4450310b00079411601510f4224100360303619425800d000c0e0507400380410030110741d0311070390390502d4a101180c04c43c600c10a48852003801c0e40c005440360b03454952269000c0c061400c042010a07030100085000b000080c0c0152641d0820b803140480d50002c0001480c001014811030b60110751501300090014888006020150b0450030341041c00d01c4120b500540c00069568246580d685031142c00402036441c141c4c0c030354208003540d10f04009504c1404404000000c00340c000348041e52090030b0250000c00c2002e440540100b1214001e0804212140148010f11808103110151080d121244029400c20805810004c498035440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943788785 1250 943787535 943787573
    0x1c0501151d0406080f1b0607081903020d0f140915010b07110d110f03030c070501032f0a1416060c020f120d05010b03070804031b0b04060501290412 65
    0x814481317086100095045030103050302000404004008100f01d4144500440a085410188103000407140e45911401ca4041241001464404040c00d0101510058050f10321080c2d40c4080d000008104000000e600a0300000a001100d107902002c101800701070140e080c032001c02003004020008030700c0e4818a00500140b66010092980c58000c66046400d038015000c0c00c104400c00d000d508000054440c45c40300800908400e50034180110002d0041c2c0c9800d90012071071101804810ba07880182201504c40d1500d02c41d0340d500412009031070048148c0a5076803114040102c00c0796000c0c074551812001d54002d001240d40e6100500c100e14200c0c80440704900c60090b003d032102064120307001030029201c4c48505000320380c2d0385e4070010040e0004a803503501140c45c070800180001e115646201e4030308079603c038044455005440b070000400702202d0846001c1da440c030040c44002500c0850208100201030401844201200c030507a0a014038450510141e035202013900802c44840316000420843c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943790035 1250 943788785 943788793
    0x6130512040b1b0a0519030315060509190e041524050406050a1a1c02040b030f0a0513020103022b060302040b033903031c0501151d040608 61
    0x21030b4045006a031241d9a10f402010021072000a40c48003c01c403101210f4014025000d811050041c1562482c210401101015500d10001008041c40b403003490140901d13070b90b000d031950140010b2280c1c982c0c610000b20a10840500c0070401034030030300b0803194040d0744a01c00c00e19600f60341e072045002d81100d84141d061800303c440070040440800e8043c500b00c0743d00302c401380700c0d1556600c1400440c10701806040c01001051a40180d402d2115005014500d5424000d0341e91044843c6030700d0807604a50060f400302d00b40001400700c803d18041d14240c02004020b02008a41022001e08000c072140b018000d052540109150521005041100007402c000c5c02d0b0141a0400c1008490024074460208900c1a4640200980710f824000783c02c0c000c2512800010000d9803c04502c100400128820228034203202d440354192a01c1c1440604001d1030042c42019000d1801c103840c40c2550016080044503001c41c0449000c9035520181e50080c5030001c80d00890140c8050010601401094004888501c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943791285 1250 943790035 943790039
    0x4090b041524050910170c04060e09100b0a080105040b060c1e0723041b020d03021303022d0f030a02061312030503040c080712060509150907090f020703020613051204 73
    0x14001702d400032207980f22101074006d503440c04170361200c900441c01030f41c001a60fa21045070140c1000160143c00c0a0701c2440001c0c540e13901c1c03640c00710a174000c140320000a042000104414242400384604500044541754100710f02c03111229564109640d003517003510821424018241b07002d00400015024951039140801c2e80e071031071a8451403810000310300803450000c4d9444480d01c00c0440110800140d4003905100070321900840194008881c403800600c2803840000041e0b58182605074030100f41c0c07c05c04142c001b4440135914080180c003902c0e011700300b0302e000d62060340c2d030205030780346850303030448640f6190612410b1200b251a12500100c81d9160050807801c11300d40c11038051840b0342d204007110340740c543d141c4648035124001e030301c03400c2c104c0740d21a001040003c1554100d01d40c07000500381141d4414003685089a07560005440d50107240d0441c860a200350907a40c024103503414036905040d442c140c0c3d90ba030000c0d40ca04000780310b030300541d24001800c1f042000a001000000307500c2c0e01c5203a1219 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943792535 1250 943791285 943791287
    0x121805061611060f1b220513150b130e13050f070503031903180606060e01030212061215041209080a17130b04090b041524050910 57
    0xc4002640000c03420440258007404400075500340b1074040d05410300313076980b03542d085401e840e011295802c841d1041400b50203e0036904115199440d0255100c200d41546442d00f4400d54080c1c43c0c01c120000307401e107034002500d5a001c01d1041e0840b5800c038011942c0c1c015081c140c44104500360005050700e1000c200340490104085010344030340303000e4803d0328216000103c006544070362a100c8c3c580c1642090200488803c05104020008142420042292000040c4605101c4000802103404030354408050040310b41c0071a00c2c2c26031a04c01c3c00c1c01c520f064003103041000c0b0707000020013491207040040c0c2c00c04060203003486612442c4170502d0000d03801d81483d00d411000e007243c000003480007442d403602c00605c0c060001514440c131900709005860481c3d202680440c01d6000c014100b401c50044100090660b04403401080142400e04000400340312100410080c1c4210305800e82ca1070390380301c8081c413547c41c810031071300060f03076480001060b14030f440101070342c080c06005c0340254042e480340003003942c40b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943793785 1250 943792535 943792561
    0x50c09061c300f030902041b210b0102060103080c120307050915250201030e070b03090c010507020a060c030e060c0307150c12091e1506050f0112180506 67
    0x290aa0606a0300030b801c0c401c03000c005800c0318004000019003142a00c100141c0258407a052250000c0c1c000b00e802c020f40c10700e04d6030540381c104405002410040302058100c00940030081a0b1030040300c140003000b201c41c0000d654080601001d441800300103440c1c204210704220707012240201e18600c1c2d40b03030302d0f02c150301400b16040722000768022901c0400414040810308212070303501a40303800003032030314175001d4500410b00b010440072810b00d0b96802d41e10040341030401c0030000030440f0f801d00719503c1c03802c4041d181c1000d0240f1401c2d0b060003000d11806006988680340403040d14084d203044c071b08000090a0803142c1400c0214086d80051000a503660800340110061a072680203060351002d0a00c80c0a1400407501415043c000007041000081d03000b0000d50404000c1c1c50007040050b1000f88107904500301d4070f509110442c1c40e07100703151110110364014000e04004000c1203d82107080c4841800207001030407211030240d100760b0781c0c00e40001404010104150040c3e0014200e458500c1d0010340e690349 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943795035 1250 943793785 943793813
    0xd0501080f070e060a03030806040e03040909050f0a02281a0a031503151e0c0503040512120109021c110423030d0503090a05030a0c12020a050c09061c 66
    0x41e015000c00461049143c9107468014103018169904140c80d41c0c500322000380024120690140e01c82283c031441120800c06800901280040040d642c40720b454180d250011030410b03001c01e82c00080040002d030b81c4414400302c840400f00c031100f60248006501d505410802c0e048558a4032100d06400c1040301000050420780e002c0e914104501c040100f07010500b0781c1c4500c00180a020425a003201c02425900310382c04400b85000d0b00c261800705126100c040d62807000d0300100007417022040105014041005801d801030508485103400e60402c0300701c4040605000f040c0c00310b50001090464001a841400482c1820b84410003103032207a400107100b039034000c0c0f080c0c0e0034062139030301c50301480401a07070f500c101d80758000c0084c1846101c860042d903090300000d0240c506400f403a9250008503802340003c06001400340d4440030400d40d01d00e0035024a5480162160031588003202c1803000817000104450641030071510062190707200000920302d038036070340000d220691503a1982e104003c055170541d01c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943796285 1250 943795035 943795063
    0xc080c01181208090709180618110108070e010f0e06070b0a06060315050d0f020a033c06050408040b0a02070f050f01050304060506010c02090c07050f07060c11060d050108 75
    0x2110142c0300800701c0f480c0d002034690282c103801c214802c00802070a41e01204000d00e450342103585400d02034480b0303012074002800400003400c03640155020010811030464450909080c2415581020a00200400140e00c1c0c4035062000c2d00d2910301040340610128440944000c1c0074951b40d214a00e0300c1c18403040c3c29181412aa0304051000ca07040307009002d4000d020701c07907800c9080610b00c0e1a040104c0c3c80403150041d5011281070000c40050b85803e40c1040c0614000c500c019264502500b01410301c040c0f03440d000300d100341c00714803046c80f865030340071015034682d000480803030f8a4a5500b02011180308a0b40102e162203000201d8010442e00801c07050b044030243c42410f100140c1e544140112002340c18040c03800940300b00300160015240d40e0000e0340205040c507010400111580c0842e4808606075134450468601080c0102002020003620000400c13000290005915000c0c014100c5c00e650f040c0102981c0622a242c905a107039001502e56014130282c080c405969100d4240380c0b601d280ca00c0c014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943797535 1250 943796285 943796303
    0xa031401081903030203100b04030807150b010e041e020a11070803030609010303050a1107060c062409090f060f050702240c0c03070c030503030a0b0f09070c080c0118 73
    0x14003030404501d6010b11145110000d8802030076580407002944001d0030244081c035000c1c004204000d4010280018510840c0c00e15510801d80c102800003240c4031500701100703402d01c04501d4103645e2102250340508425a004030311254440381000c0040c400d546070b214510310208401d40702e540c4c0300303941c41a8044403005680d0b01544030200d003a1079200456001ea04960010300410020f03216400411035030160703207480100e442500d0300207402d1225a910040005840d54a00c009009162062038154047e541e2946070b050303503000384510a0009445840c501c196903510341c0b824021a440305c00e40d40c9034050750400504214400c041c00a0a040d155100140716611065000030b8114260030390718040c4408900c06980c849070303080015400300d8440ca0aa010501c40b000000380c0e00408030000c0d5204102071a22468a00161030803681000d503081d2180d0541c040071440c94807800349d02500015035140030040c2c42c41c1030820009600ca4800354400641c82e002100180307200b24002c2c06201d80c85810302c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943798785 1250 943797535 943797539
    0xd060f051b070203033f0106030c020309010e090901180b0a0e12070209100909120305060103090b1308040e090304180203091b0307170606120a030206040303020913020a031401 77
    0x70112030185540c0250550302c20808601e10750941c0c2d061500709050220208038a01c401c00c83c28803000e1020100042100d1914014490709406000d03030f4121070030b144000c0d810290070a000a22032811400124000c50f10b29002c244c1c8001c0c29005038071002001441c0300c504c007110f49402c0070b0f040710448110031418640390f26180340000c0896011700303822410f80c3c041d0070003800390208604103501409a00d41441d81e64000640c4172942d001d003400f0240100049030117800d80c400043c064541c001c2205040516004807200051361100d5030302d80003000020206401d96039450a0700c00340c8500d80103c040751a540c410801c0080c3d00100030402d6420960165503080c00c004101740580c04241e03010082da401000505000d51020107154a19440c024201d400d01680c50118140c0041e1540d500e42e000d0b00b14600b00300070350030607070580f05240a0000040a42d1140744d1002900d5030b40103070004007050340002d0b05244075a01ca56000c40b02d070807002d0085582e40d0700090007600600e401e40104501484031400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943800035 1250 943798785 943798831
    0x60506160203070b04030201051207021e0604140303090a060f0605120303070e18040f03020a0819020c120c120309100c110301060806071404031e0203061f0b090d060f05 74
    0x5171001c486d03060319903034280128141c1c1950500c400500100c11407045214681c011421040410481000d0001034400c47c241420140f00380b80c03000044003800d48c01041401082000001c052006980010000408080d1f4507040d0303014190741ea200c1d5078401220f900007031a0f22000b00045004000c20b4a440705005407003010f00200701149100c096102a01d800024045100d00180d440d07458800d1043d12101e00c03c503075030303014641c20540c400100704c640c0c4050f504405404110014280ca01260314081c86484428625031b1664190740b481e020707016400c00f400049008200303850f01c60100400d11609035844001c020100e1a030540283d8181c0c04102001010741018481d940c1950b41d0b4001514055544050a4031a02086c1281081294081100102050440b040329109090348000c1c082007800c580100751521038043d248007120f14103694500081e500c6c080b4607204a4001100c50741c0c842001d400003c00014449030301820850a002c0350b00030050840d03000b54400d0181080c00c0007265140d5039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943801285 1250 943800035 943800037
    0xc11070302030a06111e0a120e03070219090e060f010b1903020f090d11100f0e010f09150c02033f040302030d02010903200619060506160203070b 64
    0x100c06034050b042152600013042d242d80042d003010001c010340c5440c0c108044085441c072002004d550604c10307008031308064030680c4150a0709800d00320700d00030301080b002c02d012300ea102d00c9000d9000f4492009040c01009285003c1c43c410003c04009108000b44000032801340d494010444003c00702c0c007111400031682c161142e0a55a01403c2e00b03c110001c00e0112303805a000350b0040815942e0384005009018480d80c408040c0314a40c0c0c8500c11220a02e4402010304c080301000040d00028003402c1d580044815500000f040c881070006d181409000c88003502c2900c8444c05508110700b0050110110210079401c01007802d410340c401d400f1540d8640c204a0445407403d070102035104060803002c0d80070003e50011405080404c07485100c2403406969074006480c01c0319416514001d41d441c0d8281e801855004071058004e05c0582d035440080d00c0501c442c060311600300820341d003010004480c01c0c106003140c5234083c2000e05006442079640720251040c0130300d400d0380440224824840c4450103e40000c0c0702c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943802535 1250 943801285 943801289
    0x801030c06170f101211030d031112280912050315120114010609031109071202070302071512050c04060206070f020c041104031101030b0120150405010c1107 69
    0x200000b07509803030300c80340c200c682da074007912481c0740c00081040860007408511041c00d4084c42204420440d80401050600f424541c100700e40600d498000b10220410130007013222904403000b813001d4881d646481c0d0072504c1004460406080305450541740d40350404903409030320018044c8159003c0b094a143e01255544421101c406150040c288a180e103400c240c600926242205400407950180407980190b03120000d030f024200107206800d042080c0712488400340080074064541041d503107480c440c00303046a001e50114091181e40001c00d0300905100b0300280d0301070310340c80f0035854841c1071004005040744200701c08008124545808244507017078890858040301c0841d00642510760b100300040c1d545072039101500095008250300741189a4bd00d2141250f0508010080c3e0303203880c214104600d40101078003455042c1407508a50540300d070380081c0031041d000300011084a04c0c0303d0074080c290500c2c1c01300c000000b03148806800c0c803007086810b410950414040f03560b01c06e20200c91000c015a00e02c103034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943803785 1250 943802535 943802567
    0x22503120b1309080415050307080717240301050c04050f09060312091306090c030b01050333030a080309010b09040f03050a05040503030310060e0a05150901020a05030a0801030c06 79
    0x960002012403042d07801080c29103000e51100707424a503590b410007021404659805000600000801005031b0700400000c0d00480341d40f034054045140c08401139220007014140040c1c0440a08006901110780020f80202d010003800901490500000395071035a0132034024244140d1512074440c0c01c2d4281003035110f12600004006003400301c00400310081a034001090750b0380000030105101d401c0480c034001c0ca00146500480043c00c59036008000701140d480603420313410841c040050210126000f80510181c0702c01981c0e60b0046400da903680d00e58424000304603905409003170b0a040074806400060751080801c40000d10008009800b00040c0140858004154440307150f0410040b9109a0240140c185a41429450103840b20002882c0da00200c406801c2802c0038542804107a900000059101801765026500613090400187c2208100342e1080c0c841200458035840a81c0300b00007400c0301c0c03900001501d40e038508100c402030124030700340019904428050303400203900b84502d80d00300d500980 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943805035 1250 943803785 943803799
    0xd030b04270f08091e1f080f0a020c0f2a10030c02030d140a0c0504120305070609230d2a14030d0e07090e0304030b0a022503120b 57
    0x45541c40d4403641402c00b20a4541840030320000c0c51540302d4141c0c0410411070203403a40c4460808a0400003c217a0001aa281c102d003140c600e11250f1360400400364102003808050102540c1e00702701007000b07009400c15a0154418003420703100d442e101103000384454410300c8030103004c0c500c03100501c1101e1482207030759504034207018080c105a510070b42c007800c03000c40c0c6807060f03030b01c0c211000d40720200341c407190301880e12042100000d02441038014416007600d00ca060508504207850080741c810b161000000c0601440000298001007040a41c040007601e60b0110311f9444450301d004880d0440491103282d04070360b01c00c11280000c95401500c0b1100a900d8003581c0103440790000100503201c0300700002c07c41d100e2500c904140c070603003818400341c1285a0b000f2000142d005680843d903140920b213a010301d40191030704480301c02c3c0354004400c036415203410594100c45502da040700306000740304260105c000c9114000d039540507100c0031400c414526019517502280f80300ea000c0003000f2508005613960b80044d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943806285 1250 943805035 943805111
    0x403360f0e0c1b061005010318050c0f04020f160c0b04080a020d080903010c05190e03060406051b040b0409060e240a05041104030b011205060411120d030b04 69
    0x1041c0e02c01401c5040d400d0200040e0903c0074140d5a04d0920140d07418150114402014801075916100c0c911888181d00c52034909240540c0318a030303c60908003c407038040c030a42f5101d041180c58035011508800307501594140c1d1004028882000010b04a004603803d590352000007507403a040c1000d0701c9c10380350700c80007921040403180d081001103c00b0510843d9030000602c90700799140d80030b1081a6520115848195543c00f151501203441c001a5800c18144800c0100001294600082d12170340704e0350000c4005155254208041d2888514440c0c070301d1034100001b8003040d041120005401100e0b0029014440e0a0303c13078242d40f52070b0300111242c0390071918080ca20f0346c0c8180fa06e01c1c207000088001d00401511f6444501007004c1d15906c5500f090101000135040041081f60300c0c80c075004010714003050102d40055610310381c907000050000b50505100f8000e00d001943e403040c00014a804080454400d006042000b9000e85012034600348154136114119001c0017000300d01c0ea0210480315800310400c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943807535 1250 943806285 943806301
    0x50f0f090a0902030901050709053a0c03050a031806020307122105010e0906060114090102120d0e01050a0b030307140c060f1902160504050403360f0e 66
    0x28200ca800386038408000724002070b1070380729403005500640a040001ca11454142c0b0058810481030303122a01800103078555542c400f415114404440b4030b0304009018048451140250415a03090003406400504000004124002951425203803090302c8142144042c1c0301c240e0300d11b4882c2d104d52005a04204910130004550003104e05002c074040c2042489065072081c11040802d544281c90441c9a07148010303c00e00061500d45940156440d00509103880c0c800c1c0002c0c07440ca0110107444c2903080205410720168000e10a29240c1269083e1107911031007904800d1000d4440c132100703090303d5482d18000c9401c0d001e1074000c451648201400944c42d1401540e250711030034851503050700c00790260510340e03440f0399035000c02840858415003806032a10390408140041710342d5038110105541c080340703002107100800b41950301151412180003942e40e84508090360b41e00250350b140403220194001e22201c8460000b560b01859080031b0141001c20307210183c42250a00078016008091103000000e0f44031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943808785 1250 943807535 943807537
    0x90a0b010e042609041505031504051c0f0e041b0f110a0501060303020601090b130b040219050c0d050403021e010c08040305030d0515091602012c060601050f0f 70
    0x15200c2e070340c41092070096450000c3c4107080b4026020118000103031094042c6480d010343d0044540ba101051000b6240c080026940c0c031012251540901c2c00800180c11b001c0705000b46100204440c000e0300b28001d0008000308400c84021065000c1040c089007e00c2c18105441fa0321540500e1450003050780851301003c2d00e942c02c01020040c100011407030082c01c403541c00e10020307528078801c1d0004a40d081c03c0d880c005c0d08001d4140c20020700780f440c0c9014442c0c1561004180100c0402c100c8001461310080e03008600648503070200c0c640803200c0301d905903440c0c0d0b078400d008040042e43e840540304c0035003000808a8140c819032002951000c440d10380106140c0384080041003000050411080340a4503a60b0403d07547c00542c0155229000407030914072900c8030303000310380c0c0c400309046005515514643c0060b446081c050700100035464484251048503000350311035402c1503080e08024000034021007019000360490280202c0314000c040c04901c07a540148140c445090041114902704412082000c81e2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943810035 1250 943808785 943808791
    0x26040b0402150c011d0f12040b07060615090e1e060f010207050a03080d0b0a0302061603091805010311100c0f0201050904020307111b011d060d020c0303010905090a0b010e 75
    0x101082c10003010010180905c14252450940180c48560680d050051420103208013840185a00244c1e25980160682c10440701030304c0001c085c0f1034503845141002401881c0640003440882d4442440c0f041300340c0c211321084212441031201c00300d50364803c0039006038112941d095039601c0c0d04200110341280303000ba454a080d21010700c11620110364a10014014150651040e120b40e60002210701e00d001190003801021035068500c10661861035020807428441d07600250680003000e00790000705441104d0b040d0052025088410190b0f21100c0030500800080c4000c41d240341075040303d1882801c00b0040290b103100710380c41e500b00c410039684424002c00c481d090704030304012003005030002682e140d10143d4010746455840d40c68891000d000149009000c0001441e8424002e8582209a034404668000441110200114004000c0c04521180190903802d40b0303582c00415213000d06200040a14100e801e080300034490764498440740c644650078840b02804450491006101701603400f10003a070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943811285 1250 943810035 943810069
    0x1110f0706090c0303120b0306010b040b3a0b040c090b030703060e0f04052416020a08070614130b0103030c0203150127020c07150903050a0326040b0402 67
    0x60b80c4415981c51000c040003941003240442c4003840d01d401ca43d015481004180380040d40100259414043d01103010b02841c4203e41c68207000003520610780a001602100290740540c115103000145c1d0305811030041c1d0050b400100742d03c0d01d119030500e07140c2030245004081030303600ca8022072030034204001040e6000a09030010305488440024905005c0000d4510801e00640d1614075802c203858070781d00307115a01401540407100e81c102905586200700c0c28541040d811035103005403255840041e41800030b0580e01821942e03000c180b500610266401010342c80c004030b40704240b6941d90404142e4540c10540c406031420010384018000a40204c2449207a10b000408480420820384a00070000c80260054000c20b290103d24001c0b042080c030b04203c414000010540c201a10b4801c42955419244120203c1e5120143c80e28607042c0920103000141d0b80140956140e261207080c042d0150100580709220010402d4000d1490317030500403400d024540c40002106141ca0319020803043c9459155441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943812535 1250 943811285 943811291
    0x71404090f0c0308090a0608041716020d1208070206010f0e060a030f230a0503091005070c06030b010e04060b0304152d050c070b04120309140c030f01110f0706 70
    0x412010b540880041d4820007103150b560581c0818040c2c0e18030305511170400d2012001c02d00000600a550300741c400342001d2000c5494919401000c0d0540800810107500040019070403000e02030001c030500080e542e030b078499840300d4a544100326951174091050014955030030009100616403003403141d420080007001e402c1c1858894403000031000d881041140d03482d00403102c08094011002118040c60040c801030103460209440d0b846d00d030310400003102d03c1a0350100720018658080d10030344140d5508480f200c1403170307615054050000c04c0700160b5207003c0740d142d41d5100314a203001d000d51001c4c0c9070308001d1203003140c89564685c07031f881e85140800210300740c442113141c01c0e20000791040800c03a4110402103d00d44448442d40b0110f40e009003164026075010000800411480301c00107800c980e1150220b050940c802d90304034001d01319100d00a1282c072401d94a22880c40f00010401c000403030883c162042800320004490884001902166244205001054050320110040c1013118056a004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943813785 1250 943812535 943812563
    0x30f07091d0c09101d09130b1803030c04090605030613080a02070302100306030303050f040b01151b11130504030905210303090a170a0c11130504050304061107140409 73
    0x1c0c10418030440104c0000350f184003241403090000d04100c2441405850000803405c002c503021440521aa90140103034801c10040340e44100d1110407180000303101c1041d02d859051808140c6041c0e80702d07100300e03150281050030204041c500410828050f41001c04048586a040d68544010347c1000701d003807044d400303107040c0000561144091440c500b0015a00000c4150943c40e02400321407000e009030301d04e010203004000000d000ca212241c1502c5181900c0ca9000e544c03100d0454441e40005240815030340e0130714800e000c2102840c0070340b1a10408555100e1060000e4003000d04507070b811640a40003802901c1e04000d40d09200318080303104030401c1e8600d00079101d01075030326145a000303440d8955141d2144a000c001e102c2d4104850403042085c404007803500d0a070840082184421480c0600204290003900c2102d50340c2000c9800342c01d0000c00700340210318090401c50703200d4005210781004074101030b0b84881959000b00d488000c1c3c507000e90140750040e036403a05110042904260880d50541441d40c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943815035 1250 943813785 943813789
    0x270301090b04051f0b030a0206031308040e0a0e011802190b040305160f0602060115090e13061b1b2a091407020a031110060605030f07091d0c09 63
    0x1c0d9449107015034001c1054000d820041c0c00c140000c0202514150300e0b0581c01c9030b00383e17804501c484100c2d40442d6001d40b40d45030a40c1c0c00c1901c04061000030b0070072500280c0000e84040951183d8070960403010100010161030300d0450907919500c009130001c3c0b503105134104c010728116030315880c0104048442107400d03840d000c40c201c003503009402c02e490b65800030103a40c015029481410002d090100c1e441a40f61307107407800c041d40c1c460040c0100b614440ca904501014584034203a21401000c2d421580000d6007091121072141402100081d10414140603541c40e601c2c02854141e0b03090340382030f6120035251100344040b10311300703058802c2110440e0a10aa195480c220b001044940d080c88020380c06000c0d1a1160280444a0113804c1031400780c4004200484590040b407686c034200d4050401d142c188403800b001074102010b06c00400d18141c60002c01185541d0700c00b002d90f200e400050a04d0510f44c0b507060702916103400e58414880d0107682e09030000301985036600225001440030100b40e042c4014000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943816285 1250 943815035 943815053
    0x91b0d0e0102091c020d06110906040909020306070912030e060d0c0f0e0d0320071e030c05032b2327011b02010c08070c05031227030109 60
    0x3004680c1a9000306400c4928540054501c1d0725820440200e02d625035285d0200744480b424160150200c3d55039152136400401e11001c9400340f40000305090750756900e994860008101c621001e0780a0712a0340c000a0300740d405442c00c2c4c0d05030355902507100c0540700c5c141d90031a2032030350000506030000700c18001455000c1180c003c00201221507110306900411820300208030481074119644120030680c104004641c000523a940aa10503481c0103000c140e15101c286d142002a0740100010255080d120314802040006d15081c2e03031050306640c03040356032102056030310f090045200c0204680c41d0011609412070b400c0030040d100460070029505142441050410000f100140001800010f21a24100c580459108040000039540c00c3d0082d40300380001c10040885004480320a0071186040075a80204008440d803984800c0702c0707680d02d440f0302e460305070444c051080030b02030303c40c900c1080010f1202c0030541d1031642401c0440f03a150031015040c8900c80307054664450b05556070b0601030010880e803075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943817535 1250 943816285 943816301
    0x903020406150f020d0914120604030207050406080f06070e011e0f14210c12090106240e06210f040b060409111509130b09010e06091b0d 60
    0x4585801d6100600000f60088401c81890340442d00304c04000420150000311a105407511004c820070702c20142400300b6400000042d902c000c0348280810001010790001c0d801c1c0590340240c40501c107903a0340d110f94a9645164401c44515030b0440c0000541d8a80308040103440c40805140013001c47c044c100342e00400c4a00080c85800260002d02c041c1010b030707042800c555442d030340014840c0c03400e1001462840c480c50005071411409040d10040b07002240604c090329202c0c46130329240405814986010350003441c0c1403042017051490500660008900c0c18800304020701e40c1e4643d0352010f405001088820342c00140408030b02c0c40c100d00b1850607003016400c00c42c4074940361190366600741441d040080440500425582c480da0924481c400000c0400100703c0300000280c0324002c0c100780d28040d41c3c0060041d00206604040d404084080300b0400ba040390300010f500303030b40c0040d90380d89400390420b0301c440c11208181c2001c8a000843c2111840098410001107444a05420311643c5040300040d56020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943818785 1250 943817535 943817549
    0x30b09011103160e030f010c02010e0f0307082d0703020604170c070302040b0a0905071e0f09170715050d050c0304022d030313060f0e1507030903020406 67
    0x44410088081024071921500304204480c41d811071a2140428603154080729004041040c0910b0304861600c040110901e60042d50b002070280c1080140000d0007042220710703600081c41582140f120001c40801240d00041c0c10070b10480c6040a60380d0110141407400d00a0f02d1380703000840b8000642e100032805001c1036071180d400f42030349051500303142d815042d0002c0000f40c46541046040144d1500092000860350b0548003c610f100354440040c003104850703801051000e0a0000300046540e0010480f41050500202030348a10a4a00e0440d04900903142180210703003118410f0000818160581c54458517030030480f42c550f40c45540b6003800313940400340350000c5038001c184292401858000d4941c400100340c40d1506503c1c3c02c2d000144928240010034010034107603555000e40c02d401c0841e00800d5600501260b65070341d0040e0303840c1070700102071140d0000140c80300b501c1c1c5a00c070300c43c080984c10007000406e5002095458040200b4550001d0012010b00c40c0644002005803203a000b075000400325 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943820035 1250 943818785 943818803
    0xa0221010606120c1106070e060702040527010b010c0201110a051213050103020313030e0a091118010c0210032403050d021c08010e062b12020c0105040b0c01110403 72
    0x110f20101002e50700c2c40d800301e0003803000c0086155801d240020f00564008075a240c4030a07015000008960188510040030b03401900308010450740384005c85500c074095040c0d00c0c500b00340e010000701c11402c03101c2c04048180041c00282c088800746d8885c0c4c0c0c4440d00c105403c0141d42544583e0341c1c80c1403600c22403070b43e9403010301d1001c18a034041140d0700310101c009240a00b0198035510b888881270110310380451008003803020618a0300c1c000e89800d90050081d0018110400110520303200c0000c89410480416800c0ba01c054540040340d445448596101640a441d0f0158505902000d4000d0725540a00805414400d00141c00340c1c4000e0003040021801080680072208c0c6040d0001d04000c1c9055000c1c1c20460210000341d44154071202903411691600d45d00b03111910741c0c0c0d0000304c1903100103644011244d05c1291441905548000383c4031258841d40c0b03800c0c0d00148001c000d0f41c548072105840c038040740043c8010044030f42d620006141015101c80000341e1901d00c0400c0100c00e030420b41080e221902 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 943821285 1250 943820035 943820057
    0x2030717040b04141605240c280b06010f0e0d0305040f06140703110c09180c010e1305180a0b04060e010513021c0c141806030a0221010606 61
    0x140803080c0c1007042d00200075101c60317411800d00828403038440c070640c2d02900c040c118201c0b403482e19100805045c1403107a07001c0ea80b0301c184001c01e980e48429916420300d040c4444d0102240c2e9401c01d00c40b110349540040d0707030210fa82d9103100556030a043e00306038a061100300c11015041c0e0340c8505c4110400340c801d071185030700d503800c146950042003400d41003002880004148001a41841380659486550519204200041c0010f000c1d080480151000740c1054114080c800d12601900b802d28151050304115901108071500459200c900325107459001011070b60380c5540808503400031a40010511248031402d62000310b1030b07281400d951407c0d140c4081c50000e00007042621b0003030802c181e0b0014000d1001c2e040c0301030515050900300d20028031410030840d007501c044001c604400c8589820001c5048802d59031903581d500a645004203503c143c40349100f541ea40c094a1504a010701c178040e0040147e0714146e424000103200208060384040d4070700381240303085902401150081c1c41e0355615004564 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 943822535 1250 943821285 943821293
    0x90a270902280905131e210c0c0f05040b09010b0f0d060b0703030e061f17150106020f0f070b0f1e07060614010806090f1801020711151c02030717040b04 67
    0x1078966601d6044540d80501c00c48007094000c01030311f2410803448a043c0d40701c40c0284040d103611414686c0140360241450300080e050b00004c0000e41116020b035424003100c401103040040900e0240604100d4000134005129480c1400d40541000d42c01c0b01e40000c1c6054a03580704150781d0b000301408030f0010b5107400d020b0405010500400c0d4206030103c100f803aa5503c1e4000b1501c0c2c0c4125406102106564042c00c20399007402003000840744160040100c6140d40c441c5002511051003020007082c9101d0342c0c400d00161540002c040c0c080300c551220480c00d1030305403140003140d980042d08183c945a620f03226a5050b0f0b42c090018200544107140003d0041d180c112000242000841024180091074041118503150448020b5001282c040030165582c2c8c0c94014009004103c0c2445403590301c04100c140070828424401da40944045545600844400d13000075003e1103a00e80106005002c1050a500d540c000c3d000b8581100003030500b00a620010b2030301c3c00e030707480046900340c40c1c503034407078090100380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 943823785 1250 943822535 943822553
    0x12140c0304090204091803020a0201080703061205060402090c0405090a1a130204050913020105160318030501020c1002030c0f07111509040c0e0a03110303090a27090228090513 77
    0x1400707005803807044001b140c4019488007410240a818000c45000146600e4840d511440c041c0001e0814102c0381902410042d540d11001c940490007600d481020980d001c0e4a2000c0c0c504845004003405000e40c0e8a40b4450081c14070706510030941c544542d5422400d9a4842c652909800000380058a861800d01006034a0001524104044544241143c0582d9009086030590441ca10101d40c0c2c09115241c22141a840c0c1d17141c007600c00c0c850000c0401001019001003100c3c240c100211000a40c80e81e20300012480281d65001b1408030801c801c00149090102420550740a00715076102d81c3c40441c04102c0802c030300d407000704030f452001811044910b0244aa0300f80407405151040c040825a00130a1510079103000c00340c0480200302c0c03001c07027039a810000c5484500c00138140f0045590356a001701e04844660031031039002000c000a196200c00c1502c40c0c100f81907001000f54046400c0302c06501e0710210840c80d00c450600803104081003a688902800f4081c01c52860300100505440c1082115 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 943825035 1250 943823785 943823801
    0x1305010f020720131b09090b0d260d140703060e0612011b020f0f1203010306020309030702040c021c1826160e010501080412140c030409020409 63
    0x1981c8180003401c0840c0c5024070921014981144203085044103a0010700c0010943d020015140d09000a2070392240031502e203041d40c4c610940310510010344030324101c020340314813142041d044114082d080c0c01180403114034088006018420003210241d00e240708940740e004101d14804581c45852099503403d003580c441d54014020718003008180d08103e21440c000502400c45031103080003100b5010281000e6105584098031242c45804203000b8508c040d4454080391600c51090080d8a07980c1401070000c5280c0d0100c88161603540e140d607085945140094001a01c00c154a100901003880140c0300c601c01d8001809040e00180f00d44219144900360761044c00b00f8850400484a03603024001311284038660070b070740e42d0b50100080248003a40a0031010980c0140300a580301e5404410312030401c00e41584143c4402c450221000d0f80ca400055502207030a88000706102380506401c00f040b40b050b4800c0c0300013a5a08051464028003000c0306140d904550000e007030490b800201000700591034070480355 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 943826285 1250 943825035 943825061
    0xc021f05190e0a030303020903010f02071a0f01140409031b0c03050106050f03070b18061b010c030b0d020910050a0e090c011404120206070b070503090f06100b130b03130501 76
    0x5141030b00ba10120b481241c2c603100040516801040e9507506580030b420100c503041c9640011034031000c50b820982d45015489045081c0e070308419000c02c000424000c6c0090680e49040c0380c01120603560420b210040c001d81c1c3c01a42084081c21214035038507580310380904002e008003d000c21450550034010308407409980610310404046040c01d026480110b80202127488e1010040c2c0c540035000d03104a00020401d000d940e001d1000140c03140b001c003040c001c4c03060750349a0000811800f072182e00d003a01194035070062180e0085409884c100149070150240d41c0c8124030700050b10b0125a03a501140c2c2c01042034115100d0750b00c0d1038007003101e469020049511001d000346842b1440c00700ca1402c0318131030310950156801c03e8411000110035034030360008035003080341d2240c0f10503020700c0c242c00c000b045074009541d507085900890408100c500d00000303180f8080e00f0340900c00e50001d031030140050010344c011001111825024000010418802000b4511442007905075a01d1700e030492401c10b003140c1c4000d000403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 943827535 1250 943826285 943826297
    0xd0801080c030705010804060f020a0504030308090706210b060c03040e090607080106141c270c06051e071a0c040b03010b0c030d2c15070c021f0519 65
    0x1860782d4001184400c459080c00e2000d46502c9a05000d0060011501c0b5045070f24000940590150f50002c0200210782c06551000b409450f89401e82da1141075911440340000c4424911080c0550f0410f03208030541d006a5001a89030154404139980f83c100480908080d00701080800c0302d0b141802c1c0309170307102030114040c059910380364001502040044c045c0c01c2c100406107089080202100c2c0803500120f5403e54244000303880b042820700034003403424404480c081a2921903014201000201102d1640007a41405060500000f158203400110b940160448045500d4400d50802801402c0709401400b066189607000c2001c8001c0a501418401c40424100000c028041d0b008003a40d040d200200310140d52040c8180b101407460041c01982c20a8614110310700b1400c00030041c0c0980c0c0e80a42d800c9844540001d683e01c1501e5003154006d240781500d001c00029100e5125180740701c80c0600c0140f640200a1201d2a0040101205481076020400001d0003210314101c5040c0009102d801d80f410b9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 943828785 1250 943827535 943827553
    0x160512030702151e040b07030912121809060311010305010e040b010302040c1103190e0303070b0a052205010e060f480d1109031221090d080108 63
    0x41114000c51003100501030030301241001405040c008011040c4c8031400b107158640c0c1d142d0803e200a0f034403018088012480819000034100e65850f030615900340c0040008003601910030064809000001044106005041020034440054425100950b001d40d10026009441000240c22240103030001030308052020308100001303480040c100d0540350705440120307400c03220343e4050303e01d01030b0742c1c1102a50703010214800861562281c00050403000e5a5108606a58a03000385512442000350180140c0c2c4c21200080303102c00a60807958028004246204160180201d08032000501c804200c0d42a5100c80f101d8018401c10071501d6040402c120403200141402c4006a02e181e200743c0150f0440c070007018941c0009048942c8000f000ea0301418210a07a40c00164811810350044401641081c50f2803071004400e070300c900540b1030071040907000300021020880e5061b81908081c0081440c0c800d82c0e0381c648003c070509184031303001d112481d000300356001c9104405016103005030410300b4913900039445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 943830035 1250 943828785 943828789
    0x3011508193c03050c1b0a0e190603200103050f01060309030c021003240f0b0708190905120622110904050604050709021c0c050705160512030702 64
    0x49501119000c1004100405882010b00090068811071440c0034101140507024580c1000003403e07a4070000041c0c418100c031943c2501d0400c142000c0d12034001c0c0e0441d500780052403d1541454003c03002d07540c0411a07008041307440c0242c80058100300c0c1c4960900300340300c3d501c03202c8a0000329991000d08007488180b524170b2480100729014400c6030201500c030300c0301c0001d01d4002e4010100454000d403000072030a41d00e00000e8090481c0c600006003680d1042011082018003100a0b011b450b042c0844458880c0f4104036400075401440058030810010000d40d0701004042003011b40d4180b046d00c0d0380d1603491500e400c100000e115031000e541d42d6008641003108015900010b49180d5010f0010001c0240362803c00101e10702c1600c1206410104080c00c5c0000d2060000380c10384a00d2080c1c04503203550307441e081070740140d0240c81803007800d02d0180403110008000030b4000c1d5000c0c000510781030b410021642c0b00c90b4030704489034004000c455030303111083c082403c00f01d44100309004480300441c5000f00f0703680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 943831285 1250 943830035 943830053
    0x11240a051201060806061e130e06011b05070303081009020d1a0102010209010c0210030e0f0f0607020304030c0506072406060e0a12020402030903040518090d0801140d030e0301150819 80
    0x8040c2030701000c0b07c52040030f481090980e5410072030301501180081c2c850b0342d401640d00094a60601061010f0104508203c101080c6003440394480090001c80707203141e90943c3c03010b03000341c142e040d6106c0c1c0c4e440124001d0818805080324003c1e440d80401d003000070700445000c81d4400e06849045900410013410141d800000c82c01d01d00b64150350324444401050000c80051450221410b1180036903c4000340d41c41c400030b81c407a4000310070402d1750f030242c9072000c06a95920075484020402107260740100518901400500305050154020400c0e0481c680401510110502000d41324903079903040c10300c00207a0011044240020a072046410b0500b0541103d20458910400038400d40d0000b00054072101c1c21702c1030f2002001c4c0504034000b2141003848600d00040e045590858074410700c83e00c046c81e1071060f00300c0f904842a07a00c070384d0106042c0100344109580e111405030113100c403a942045203a1000d10400074031502d4442213410041c1004103007402c0c0f500d07010503000400e464106543c08195a20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 943832535 1250 943831285 943831297
    0x803040605181f061505090f0f180a02091206100f0605090f1809071403070609170f060c21161107030506070302030405100911240a05120106080606 65
    0x4101d0a210000c3d112182001d400c1c00c4e00440c80d00d2420000350403915030030001070400c601c0211002440c04030f0b001c06101d001e0003031151040d80704400500c1d11044c4103c41030100d821000c5028058904429072002c03a18081a80c143d6440e9a4051010002d244042c501950081c1034810542c0d800326142060082c503a0050061003842a40c00c1d003a5400250340e184c40340741d0881000300b07a01442e480c01c203842039280c1350944140d030003190010440b1400ca240204152080e02c8494407014030407400d06640c5c410503010840d02c500c1134070030001e07444d610b200200714032841035108905d04c3c2c0da0780c0b141d000901e200c80101d00181c00d0318120417051000d001000994030b41e00120f02d1400b10f42c07400d0403901c0c0340d20780425580050b200703008032800d2001c086d605070000d602c55030148084404030644091075030129540104040c000d05800407d0b0600e41c42d04100452202414100c07450010f2003018050080f03501000440000c901d0000d11030900003483c01e0080d0040c81c0c1810880640d11340b0704c001c54150b224034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 943833785 1250 943832535 943832563
    0x318030207051207120b0712022502060909101403010e07031e060e010204030309050d2402040812030f010e0408040504050c040b030910050c070c12020109050d080304060518 76
    0x20703d41c8142014010060903008100c100805403204083e17003003e080980c07040c0c4202d400540580010084a5150b000311040c8020f04c070502d10307a811b0581800060309422000c104d034400030400c59550b075555a208020300590403002c04c000710170b01c0c0c44061700c0d9610708050102c0c083e07414252080c22020010a04a017207940101101400171491316000a0059030b101009009905c0c10000c030050b40415400780c03044c1e034841d441d01190130761140300b00714554600c441c0080c24001070001c03202000401e004010241d1105100140c10300e910703803841a04051845005000c1000040204000003407151801401000e0010351042141415180c802031403186000740ba0185403a840407071b82c4084400110b03002000740c6005039441e4101103000c41d403500502c00c00c11903220f01700740220351000c14a000312900107510596100043d450000242100403a43c04181d0501c02c5100c0005420741700c582e0b00c4103040e40b0425080f50340b407a241c41d00f20207c58000d0081007a20030885141200b414000400340500c100d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 943835035 1250 943833785 943833799
    0x1e01030f1812020322050306011a0a2a030e0f0607080d0c12060b130e061e030f011107210c060209041e060e0a0207020a03030c030210090f03031803020705 68
    0x2c10007041c1d01d5482040e07220400308030b80c206598050b218040300380303040d550114107a40d040d9a890744103840300f41180322080d001007806c00100500d03078000c00c2c0a58182c0164a8060041c40151420b890a010340d820f00b58041000c1500401d00307450240c40020f29518103d6104d800c080c5c0c5c54542075483d00400c20160011580c80715034481003401030070600c00002c2003660a204084d241c0381880d1143d0080e0400940c41e521814001c01d18500c052803651044102800c80c03200075490080a00d211060460f22a0305802031580c2c10303804010a01501c90400b07849040c071a03507501d01d0310b0001c0840a0526990040440b020001204664060b26265503690003150250700e402c00f0030006002880300701103c000d00c0c0b00030740e8003c5000d041c41d040701c403c540c440042400e959a0300c042110582c402d1040023948040c03d500c00340000790042e001c0030b02040c060303c1241c1c400d400d1028154100e031107180040d166901d0403203c40041580c14015150911504600d001340c3c7d080b903a501a59a0b00c09004041c1710301e031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 943836285 1250 943835035 943835063
    0x90c05010503100b160b0a05090606150d1b09060203030c0d0e0309090f061306050d08131205030904060801021e0c010f11040f0e04031e05091e01030f18 67
    0x3d2225020005054210f01c444e030703604e48492858a90700c440210480304400d9060001d40240d0141c031449125441150180c021680c0d401d04000500d201120b45400e1107209200e42d1980803804c4c441ca01c403011150b402d928421126100190440c60b1950080d02150300401c100030050304150241d5030300d070240c080003044c001e9140c2101400e50003482101c640103054032040045514541c405c4c0b0b4010308055400c131300521450304c00c1c1020307140b244c0146a0010000482c4000240072980104103084905150454440d2120b1140700b401c8504d040c00c1d5407a9101007494081407425200d2403004140803002185080c8010544c0c100356002c88030420310080700810403120410003034102d1020480b48030001c125150381ca0b2916403542d0060300030b003071002d0300d059000b085c00703480031015500480c0c0540750030040b03000800340c118840c0300a0303010004119080c4201203490f100c010740c8202c4543c0c800344480c411051080010b013210a803055103030b2043d040804032611a07202090325602c050308004900080c903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 943837535 1250 943836285 943836301
    0x81c17060607150b130c08041118150102101802150f0d1d2a0109120803043305150a0e0a050106140a030b03070306050901020d0f090c05010503 63
    0x4042e00e000a0a1401c3c6190000b00c040165070001010400c1151000301d100414004142200d4036019a103001c41d810001080c042910044181107005000744404402880f4510b180302c142c1341554403242124102c00c402d1495a014440d50b40501508002041850054090a83c50104010380680204040c200c5186200f02c0e03102121410355422101c0b565801b81080030340014181d00b43c940e040100e400313070344038400040811500102036030421405182047d2410306c1103002d40c040000790510141d10000203103000c0141c0d42030301a5000304d180585903c1c241c1015034641a100e401c40a07060403050704100c10900818051103944e04100c1d0029040c0c0d192aa00014101c0c0703000110b501c406601d070300007200e4003001c0d045d51040144240c148420703640e9a03001d4800701390740700b1015007010052045042c0b052099001905c00c03100201111401c40d07580d1119001c5a0007030f00c010b03c40b80d40006040290008500408601d03d481c50b42c1003008515540b2210391903051402201c7c104000000415000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 943838785 1250 943837535 943837537
    0xf0d2a0f0909020a090302010e1801170705040501180b0906150f1210080706080609280c110d0509030304090509100606081b090d020f01050f13081c170606 68
    0x42c2208990855903540b48400140c41d00303c440c40200d000501c808004015400c000c03d0181160800079800d4001c0d03401c0034090000e540f100100b8a0081c81150400a09036440740101e034000d007070a45412401100712a81ca500b82c07000101e070346008000300824040c16480d08060308041d01244554961203403421803600340d0511401d07084030941c0f0b0b22842401000c2000d43c0c010310031105020200c4200742d40c0e814003981c442c8012108640c0c02480100090000400765580e00f01c1441d46400c3c0c03101130040b055070042160b0702c551801001a40541d403040801078204101d5003407403814182141001c0021000070360383d110704d004500740c0e19290404560400410403103555262401c00c804d00016407110320081540c05c1c21252008204103a010b004040603102c02103480c02100a010034038450700ca034003880001100040c03880d0410404004460701c00380d4803400b5060000b812294100302c0f52401000350700c0c006000a4100034021140300002d03101303421046064522050090284183d40c507000000e101d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 943840035 1250 943838785 943838789
    0x4020309030c0a0c0f0e090304140d050615040c050909042d060e12090f28081005061804030c0305091f180b0403110409080f0d2a0f09 59
    0x252044406a40800c80f40c1d52005085d0352031005403c88081c0d450302040741d8158107456004c62908100803d02c5800030510754040c2c01e500203022104a0b80305551001c1c0303061070032500105d807a0400103a03d40a0319060044c1c40c0009080c1c6400c07403d1100220000c0c801481c0604001c04500003454100b84c4d9007115401c100a00d95204040040100300f130400740094580c0311540c05450103401103140e50038000800743e43d800840501701140340035055040c42207041103e2280300c07801c01c0c81c50102e0000d4003038108000180c000d50016001401044000400341c0f28003400c8a07124810000013031114081d035402d040d82c01509490440b200600b0b504042e51070384120494503030032003040040340e80031220345140c05000440d160756100300b04106030f41c070b055603003100e00908813124010401003001c5510042c143c00c0e0118010030000307140459642e0f10480b948580301400840c4000703c1d04040c1a401c03481681c00150704110321340852001c591001421140c200144414407002009901c4194491810307040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 943841285 1250 943840035 943840057
    0xf060406080607090b03090a0b13030207120b0403031a03030415020c04270f1b03021c122a0501050121020303030105090a0905101a0d08090f01021011030429060402030903 75
    0xc103506169074802035a118819007580035204200c00054ed00d115503070002200d58000340144401e40760740c2c0d012409000c500c94204664003002108110075601400144003d05000c85810221700d0212400790801c50300c1c02c40700784660720348140101c0c8103c00606401544d0142c446680d0031005926040118002802000e40010000c0f0040610907034109546015a802158008041500385001c116404040c42000740320340320801d42065542c0c0501031182c00d9000903200c84008900220b0b40c541000f2003080c0545250b916040108490040700201d044800703072000c90034850001c29004241d403840188100c43c090716800300043d02414065000c184030076444400d44900700030006200d07010304a020075444082e4281001f860703c600d8010300002c0301507440614035007001c454a0400646007940b00e8800e0560164030022490843c45108643c0d1115150f0a07242c1c9a003440d0900552a00c80c0c00f022215007542014400008641413140e242e001c0304c01c0742c01590702d980b00e030b40701d40c00d5010721000c2c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 943842535 1250 943841285 943841303
    0x1050c0607051305030f0a03030c0e030f01021306090819061d1507030e06130302030705060f070912050a15060f0906090e0601050a060f050f030f060406080607090b03090a 75
    0x1ca040c0d4048000c060703802c801080c11095586803410503813540198a50749006500400d10b00001a0023500a095441e1480c18201c140c2c0c100c01d004242004a402c1420405940c0003420510490035641c2032009002503207805a00c550034220241d0344c1710b8001c50b5400300007a03058a02401c00ca13039500a90b102c10510400c0240ca0840f1200d2a940d4440042c820a02d14550300001502d0911911420980100380c5002b4500d0740c490b00b050501c2d19041600a0b01180010440784020071001c0000a0203000410352118031072500441c02800701e5a9900900c014150300c182100c0410000603e118a85402030b0404070600106d440502c0142a0b0350705c203902900d0310301c500041a02c41580b0075000c0309d10070700b803e1140d0000710014a4907500240941c50b8400c8807010184440c510540c0c0a007407000507810b01c180f4200e0f0741200c2c90300582040326071802c0391141104002c0282400d015450050003030724014985801d140ca0054041d4029024440d2580400310009400600405c0703c0703d18103030040d00740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 943843785 1250 943842535 943842541
    0xc0807140d0f0b0f01030b1c060b060f130608060607230708010b0316120b070311040e0601110f061605040306020f030f01150e040507180f1a04050a060e01050c06 71
    0x602d0107010010302d00c030302c103901e0b1041d046a071354000e00800141c00401401c4030444801d500c0702c00c1783c0c0700019205907945592162000c002c2d444440040089007000000e583e11a09419250b1080020070342240307042100740c2c0184851a01c0e904161100c03240e008200000580106040f1a050500840310b1841485104c00c00035440ca419400024011400d801361210000e1802c005082d5080c0d61044003200079083c0101c17008980001d02003900007030741b03240218514a4000708081503401980240ca405c0c1480f00c140209503030031a5000324801c0c6104c4c0901541d4a46840b51a140d14009200711401103001402c81b001034490012940590341c094411502c0e240c400c1b060203c9038200310f030f000449030003040c00450402100c840013040804aa6a0b041c0003100040900c4041c0074041c01420034460f800440c0790700c0b619071300401e50284c64071166603503030340307180603900760b0070b00c400624603074081001700800c3c407031074848510420035103449060141d00c0c0d200041c01201c00d1300c5410040b079864005c01d014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 943845035 1250 943843785 943843811
    0x270d080316080415020a140309010b0111060609181e0d1404140f06090306040b0a05070302090109120c030c0825060c0605101203030b030f010c0807140d 67
    0x9540120019100302062101c01c00e000e548000003518054120b580c03626404e0080211500101035140d90307071505042d003c01206c030003030140d0800d44018881d40d456030084629561300c602d034100d510820300c00030402030030082c021400110014043d525440c1034405c07a80042c00d0100f012003100805081007a4039140e140092a80301c0602211200c0080e9184000d0443c0d0120341041d1000d0726100c4001e414454031030010059204e003100040340d007018003440180000d03078043c0041407040d03001c1c061000702071800710120f0701114401805201031600c10300c40003c060740e002d800703481030f200c0e4000a5015004c0c54101051061a250301c003e050301c40d03655020440c00e90100381c0341c0c0c01861000d6500300714083e07540420344046160040e080091500102030000c41c1c85504115000500d49162070300168640907a10301d0b4080d040d405601281c0c440da1201c40b02e080400060680f420440001c208289030504028004071000d840d0710200034185550603495101041154010750200904024280051807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 943846285 1250 943845035 943845037
    0x90e040f140f03030a111e340b0a02030c04030611070605160f031a0f01030609021305011106060d030c060212040b0105030f0d0527060307080103020a09020f270d08 72
    0x140e0105c52905154203210320f09a0241607540e520700404140a640303c0c1500c0c104982d41100d801d005c1081884810b10384880503411124907141045241541200442e007840c5400e0300000d81100034a0744100100104c0ea45076100791402e80c4e0780120080307806142800030360013038010b1020250580b0702e48010b00914a210541c1504054040d4450382d200301c0719407400317a00b1100c0c052040c03055450883d00c000c4451070240300f5081c0e04001414009074180d100c00140c001c83e0449050040c1c0d1a80d210010300c131660b04035102c240d4004550000304424030b03005000c103181d021169002018000f000001e07404110300794056030041c6007044000b030304500d89030410741045127080c460b050203802080c0580d4180350010582c500c039246c0719100d00e0b00c0d1060f0901101c80c0030340c00c64001700585400011100d284c1c2d45610003035000300c1d007640e108403a950550040140c81810380c4d100201c118410480a288802c2040a8860b0303801501208003091814801100000b8422013025a00178000350200c002c128a0384 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 943847535 1250 943846285 943846291
    0x2070f0e07090e0f04030c0302031207181a070201030203040c12030201061d1513060e0f04110319150f05090d020c03010b0a0b03040606050303041205010507090e040f140f0303 77
    0xd940c42003480c0d03032103c0c0729900741000d4034108443c0c0c113120000742c0441c2c020b9084915461192044038586401c04282c4403031668291144c40000e01c00810400070071840702e1002d4054550541c1c0e1581483c0200d0740201240301e40302c0004c0c14907070040009010302c964071409400403d03070408013001e08015460000e00030030076402214184074043d0b01c840d0301c2c0300d000d200c85882001102c11000041442c0000c2100f9841c1c0b80188420003030b202c0c0d00c041801ba030781c1480c441c090a401d502e280350505051420090120b0441a01c034001d0f0301c6403010604086002d18516000c5800144c0b4188100900185401034030b81801b2a0203400d06280501060300c800184821030700d2b0300c6509855184550401f05401d0b01e02e01c0075541d50100f02c10a06102c0382007140010350300503106040c00030b080380d51640440d0a541180d4440301264050303c1c444024444280243d6500010500c1c103c0c2913a820510740441480d4090000f900c800d41da4900b6a0403c58060303441916106507600312404090406246c1781c1e254012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 943848785 1250 943847535 943847537
    0x2010e01050c060a0b0a1809051209030309010e040f09060b0a05031f02090f0a1e050a0b0a0503060301090c031b15050301090902030a050115090e070b09090a1407120b0a081c02070f0e07 81
    0xca600000b102100d00b0340c1c2f41142c004010318600550040110340203603451040641c4181d136400030621800304e902c1a04030b6075200780310200e040300f402d0341008810840d03544003d009420805041e0760341010307000340c8150451903402c010b80b13480710320003c144102d11107020f4a803c00c2c424200803612106018080b20192012b51540045588039402e210840c02280709004202200b809100080c502507000346d5400100038000286059840c1c540e403180c014580d10903070340282051480346141c1c00c01080c407009407041101c2400c0c2107020ba0030081c40c900c014803400c0d08082da107034009001c540e000e2100040700d941260081c04040980f145021001d01548191030600e403521720441040080410120103d50000307201c81d050017007410510604030390003010344c0c0d030a581c0d511190800354982e100540c01900e4a60b9590301e103808a051300c030121011611954450707203036135408001c200f200150881c0c1c2c4400700c599030700441070f03028016460103c4a811800500c07406039004182ea81d40098418400c03035003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 943850035 1250 943848785 943848793
    0x91513060203330906040c0507081303140a0b0402131d03030907081b040506030f01050a090b011d0c1b10090c1a0706110c100902010e01050c060a0b0a180905 69
    0x9880f00310b41c0a1280000141c2d0001c504200003072441c505036215008020302c82c01c019140c00582d0b0750391800c65000008413020140c030503d041c4103000b140c0c00c1e98160100c3e5180145100b200380d4854150f00038008200030b1040d80000621054002035400968040c800001d44200d100f80da141869101e030000c6031030980a201e8400006900100000d80404110054040003000302c1c145061202802e1b00030003140d010311a01c800740108003802d2180f68400c3c10306650015984005240c4141100d6044e0f02100500c1d1101040051000d10f01411a420420015030343e0303903500241c514400c03601d0711103104c902940a5210035541c080c045070840001c0d10b105020001c4590f848880d0a803c7c0d01800c0345d1403480c10010700140c400228190300c00305040100c0c02c427080c107101f00d135817680c0d142c00000740a0600c5c0d0354651029804550304044410380c01002401d1181c00c0c001d08c49035455480300020207040c1016203400700c3c20100e443e21144103028021420b45500c0c151070000348a0050104a407003110f0b6449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 943851285 1250 943850035 943850101
    0x61209061504060315020d1b030213092c0f0a08030604050a0216030f090302040218040c03020405030a020105070c030f2609010c0b04060b0a090c0314091513060203 72
    0x1034035100f000c00380c0780d0201c1c010700004815556800250081c40c18071220a40d81c0c0406c954620302c1c145011032290003a507015a0b00c042d0854182c888554541c0219100e6090031054000c0103002000042e1103910442643c0741e09202c101100d01c1d000403210060114014400740d4828420071b50001d6201d01000d803002d00c0503460b0f4914085c120b05c05c0d20000c808940ca11a400d5000a104800070000c2b0a0285045025192a500007a003280e0000101814640051078543e034581024021201003200506086040c54640300c00b080d00c80e18150300080c10840300040c000100b10107624180003940e0420070b01c1c004100203103400301d241964040c481d20544c0c00201145280d0180c8002c4602c0d00406a42d8111403440c140d5a00e0448540600200c85990300c2d1095108287c45401342000107010104021450540c02c41c00030b8100c5807444811502c442290081040101c0000342c03801180480303042ca85456a80d1012135010100341e100003c200354000402e10411a1012141403a5018a5401500200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 943852535 1250 943851285 943851289
    0x60302120d0e0d022407150b0102010e010902011b080408010501060314090c010e0603281509050105061806070512040905090f0715090302030a0f05060f010b180612090615 75
    0x81c0600007948144034010309250310300ca080b82000208580445c0c0e509000c841e5940303415003050500b0111a040d41c03100024403941e4240a910940010b60008000c85201900000d02e518065926513001000c40300d00001003140c608200d034018210b00d4000c0155584500c0002d0280c00d6120510601c409100c010900d8184081440340580070161a10000072440c0780074031103145c00050020010201e0000c02040c43d0107296101d1403034820034600003545840c485850180d645941c0c010020440c0b60400510241c0c91341c00481c1c550305081d451142c0380305401000551240301c0c0d8140100365009034424803020700c0340b0101400a64240f0b0009100b1540d500305400d944400b00c420516299010b81d07001c000102c00644103410b04481031070410907040d00c0b0b0300030a1511402090880301501d12294650905c181841065088581d00410f403809525280306141c00d80160b130202410755800f05003122860343c1d00001c540c83c010800601402a25120b41b0f001d80b035107400c031000c4144d0800071030560303014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 943853785 1250 943852535 943852549
    0x3060106090e07050d0c02070512010c0806040b120307060f0f02030903180f030312040b01090203010609060e0301060512010b1519030513020d0507061202090919060302120d0e 77
    0x80d681075660021281c1c54840c004514000207031a06040c04400c2200c0c0ea02c16905000310341c0115215001012420724181c00d2019a4403400907207951079141410503030045502c01121070300040101c2d00845c016030403500040a814401d146882daa200c002880380c200515034008c030050500c00002001040c40d40140d400503440203c603a601650410060003019600f07207000e0f8020031402074640c281d010741402c0400d2440d44400b19902d000c902100820040051019619014150700c00d02981154502180980b5100079405082c0510481b07000c410070a440035407000e0010000209015080e0840502e40ca009116074294140544032035203c0c4440d040700f600c121884144444107180030f901c00311204600600d40904101c121507034807880746015907181340882c0c800d84d0141c0050241c9a141040c0900f0000340d214100080034018404400c0540d40e000c0290f5008080021000d010034883c1da01070001c0840d07403c000d40c00a000c0d80c40d00342c2c0d50030029104c09001d155803503114802050108004103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 943855035 1250 943853785 943853789
    0x1b170d0e0d020c0a0f0e0a1b111c020a0b07050c0d0e031504110f0a0302041119080606040b0a0e030109030207081608030711130507020610060f140f0408010204030c0f05030601 77
    0x110022140042001c0d0740e00f0886c00b50b22501d009000900d400b00d80c04030414038290303000c041c40016054080103a0b8110140a040104280c440751059282042c40c00070351507501044010f0020b10b1098000b4002500407000c03551061100b805581400c984040050400000445020f010307229000e41c546800311b1720300040d4021078200300040143c6400c5010841500401c18007540c119225060010058481c1d00944440d011402c41d420707120000140740400703c030545005807042006440074801662120401ca0f001c0d503c0005c6a00e541e01c4000c10b0030b035049100d000200750550310300303502c0c18249603003c00c8403010740308440d0a4540c0c03801148004508007946004d03403044c540080100700c0001d00a40080240c800000d441500101105501001103682c11910b100c0543c00030010890360214500e03201d405021942040088403940d80c4008003102540143d8400381e0000040511001d40b190301650014030b004402950707030300d44a2a202407440c1d9140b10301102c0d04842240803605180115550741 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 943856285 1250 943855035 943855049
    0x906020c01080a0c090f170606031b061b190606060f0e04390e0117040b04050f0304030c0920030f0601051312020906011b170d0e0d020c0a 61
    0x8415243d8080060042c518a211441400f826113800145002d8800901d00141251405941c80741990140c03241407480041c24140b003500035070004c20311201e2600e040302c4070300000e80c0d829845010740000305845448140303c07101944030b0000f8207030200ca880002c0c011814401d56041c020340396a40421344404800c013000354040781210400740752500782540500c0703018900f48041d010350103070314145203280054550039401c1c003002e441907425a00d4100720030003084103003842c0c1050005a28031303071844c200c900a04010103214000010505019007040340160302c001500a8030303681c40c0ea91401e40c940d0b003843c2c0b040e070b100c0d1420440c41745150130000b1212000d403510408001d1540c0d4450780c1d0814040802004941409018851441c000d407601c44141c001d01410184000da80486004010524100600050400501d441006014070300902e070010744030f0340321143c8031030ba15120800005134012900c481c000c0520304002900509000a07256002c0c215a400b0b581c2c980d68850144140d8020b02d000b220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 943857535 1250 943856285 943856297
    0xb09160825050a060f090602160b0c0a021c030306050d050d051c060902090405250309150e160f2105010905010504080d1503020f060a05070c060507030906020c01 71
    0x4115410207400ca00441c689003180c161a0390b1150001030101180b500034000044414000c10034154008000f40d000c1c0000303000410381109080001c000300001405800148800820841e1740c0d0300c000c009011240350b004220110340007414000c0041d8011021342600000c0c2040300029081c10400f100700381d01074104003d041c0c2c00710602000d540342d900c901c1b404d49102c1500c02c8480781c456400d02c94600a090790080c0560785511800400050b284090400e40407190150002048003d54507104903c45109003004502082c130703818400150380c0070340f01c01e000450402c042004d100c1ca0200d000c5424442078a0b00c0c19030141c0711641c101403103155004484a80b204042154420304010204264142c4100000308481021750713112402d42c0c40983d001c0700d1108000c980643d0680d000c0c0a0501d52001c1e08c820320611602d117030001442d01c0d0701050f826004460010700401c90780e20a01c01c0362175640c5c000140c02c0040d607803010020030307036400340e103080c1e001807401c0102107042880031600140a550581d540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 943858785 1250 943857535 943857553
    0x7021e102c01020712150506031f0b030a08030c0c062d0c07061a030c010315120f050303070c021509010e010809010f0e030301150906091e030606030b091608 69
    0x12414280007606181544580840000c2c010310845444003a503229942a02c5041c0c551080c43c0141d403009082c2500c65045500d2407007038610100105880b003044010301041545e92a00441d0a00c140d5540151051100208002901c3c2d6030f00300603e0380055200032a0314a07500d040711080f0389a02103041003034440490460500c0b4a0141e19030136000f00d10000c545180041c1c86c1d81c0e1808444413141c0384c0000020441860007945024000303180f144c0000c0c2400d01c809241034202010500c000e009050304560192106800d01c21701a04071251598405d003281e83c0c9040581d00030300704614201342284500c1d950740191100b402114141e6030504010b84810401421070310054a506000800c5a00a507507140c050004140f024046c2104051145010350364039414001c00c800c0468540c4024030900080260811540340d02c80481411598010301036581038512040c0300c3c59488440c0d00241c081414010048103100000c0c4800f8001e121060407607803200e07140500c0030020025442240000d803c01001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 943860035 1250 943858785 943858847
    0xb0301030b150603090d091a0d1107050f06240d0303020a03110a0e0a05030105011a0705031306090603181101050a0e04050108030310091b0f030207021e10 68
    0x1582d0800080d1030340b01c1c0c00c00650700110302690812200904c40c2c2d8030142c0201d41054201c0070140240001203040b030741c40c01070b20540048922850804000c4141d4a81c580c1000303108400a944d19554040e00391424212427007000b80e03445009031400d04804070111050320200c800d06508403c0c014010380711001e40b81090314140c000f0341007035240302e049c151140030b0800c0c980c208000402040c0802d8442d11104200b510a1020541c486c0c0c1010340a40c1c0f410006001800110700b0070b40c04098051400c968031016032070102e0950040110258128410744400700c2c60341d0300003980c60251001e41d501080011103102c120f240e000280c035005002c4002c950408480c42d48542c2c0107080008803810141d4990007a007010808031030b001d80c07043c2c2c42e640003c0140080451000c401d80020b012012051121b1812100036103002030344140150240101d0201c0314a00038002d805503030000d50010404418103400080c40720105001c013076801d20440d0710700e10740e5207a540551400c0c1d6208000b81005510403c00d964 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 943861285 1250 943860035 943860053
    0x402010f0c02030c041b090b03190c11060a06050f01020a030918020702031e16140105030604060905100302040f1116050309030f1501050907080708040819110d08010b030103 76
    0x720903a018065008080d80940310341c0251102c00624030a0310420305504203008004020a4200c01c0d400c107401c0091000101c0c4995540850b000700f410002410342c55490141d5101d01e60605590f0240541401c2140380f2516520980480d0b0080d1684c024800c03040e401203848601d40d2030000d000c680c0c15030043c005103443c00c0c2c1410300c03040984801440c0200341e400103460204031f0700311480007015480704100003081c140041c020706000255000c00b0b0b2800c3c0000703004c01800394100c0e14100003010000980c0c95849800c00f40040640c401c0410079400e007621314041d100441d00081e4010360805846c0340d1790a100313124040c14803407004100b90910250040c1c0030b840c5030036480f003901d00f88020701c10001d0740c0d6000d10030016407140e030b4401070528864242488014500513070010b40304a116508201d05140c124400c1903000c00380b442e000320980d40d80d280c042d5850280b90004e0350302c01100004c50100a800c101045c040142d003404685050781c0c1413000311044002406080c141c41000d01c010800559505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 943862535 1250 943861285 943861307
    0x105060a1d0c160b090c06030907060f021603060504230d11070306050c04030b0114060301050f031e030a0809010506010c0212010605031005190504030e010c020102150109230402010f 80
    0x41e030b2007440e140282291060f110303400d0b0015140084d104042c82081c110401c1610541c1100780d90150444ca0003074010390b15043c0c580304980501180b0300c09850180d1081c00806240c07925200401451622810a000109400ca038210740740d811300428601c00489005c8000c481d5955840105203040342040c0480f18203d80d00340811051160440120003c0d5035800b03542d20800d1607012161b19645141000d0b04050410303030121280511440458007240c0326607045a0555200307442e111003814440c030101c1d203400301c10714481c0b03c20368140c8103040c0350600200003003c2c40123182d566159240c03243d180c43e500f01c2c0c5094606901050b949150100181007148440d5111105c0710000600a90b85a000c01c4c01c080000002500c1c05581e642001860b4800440807491a5a0324a0030401c1e8039080d6805401144000100c50522a0801e51307a011a8420054120260038005240e10345503035500400000c1c4c40c00603202c52400d5540e68400200c640301c000e00512454059480050300828010300703460000d820 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 943863785 1250 943862535 943862551
    0x3010b2512140f03040b0f010603060503030703141902030405041104051804230c100c03021e0703060207061b020d0c0f03030608060420010507020d020f04090f0f050105060a1d 77
    0xd000301c40002c80f24802070341c41507008074001241850081c4400c118018141c005409140c40c1500500041d00c00000b40d40d80c0642c141003803441524110000380d51806414015041500154071041d04c0c00d5012018000710f0705d00b583c050110780c070039404426980c0224014144c1140d90302da458180c0038043c0c582142c0082c00344030000c901144540850250b079000d60020032050707000d41c2211845080031041c40000203002c2c509030051000c207070340c025102c1c1440714524501d410b0803001160001400e20501c4000c590004085654030340781d00d0003402801503580b503901241080c2020b0f03510342c1c1c00881c4600031601d540d52000844110759655181600d00310038144d080580d02d24001c01c3d8401d04000030341c0514068288160310350b40d00c40d4112100c1038503c0d0450304000052020000580b03a280f400c0c03415035412124003034810001c1c004103008020480c0080e0002014900d02800d21010510075035041e802040203000e00c0c1e032001d007880040340d02c80c8603a01e10940c0244600e81081c801c03075070740d82d00031401c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 943865035 1250 943863785 943863787
    0xc03020c070806330d0c0504021206091b0d0f0f0612021003021306051b0106030305031807030b060f12060108011e050c1c09060203010b251214 63
    0x40d100c0d803614100703541e00140e0082c2d10100c2070004408030341034110354001c2001516404842c1569860040003048078030070340550f42800180b82046001c5000c00c0240c18082c2c000c5407034070300d200e5464224040580700e090254680c01e000c548410000841850407039640c6464520f08259036450800030940001c8075500c4641e202c65048815905001c0d9600811a1480e15034030045140104000301100500100615104001d0042440740d0f03141803500f12802401c000c1d4445603540005035078a075842d0043d000e80e500c0d0034404005c240d0044051401040344010442d46011851035550756106c3c18003000d02034410810000340d00b8601070000d44440c00e0060302c0312800c1d139040e06286282440a03003001a06075100e202c2c124160398a1011200b140c01e201405108134200084109400d22403c15414241101c07000765075040010354011804c0f0030350002c0d04659940c1d5410400181d0303082140c00281121581840441000e4145142040d0341d803c084940140c0c085000f0607283d1215070400000f80c010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 943866285 1250 943865035 943865047
    0xa030c031d1c110d030b03010f060e060607060f1d070905130b0c0c010603080c010b0109030c03020910170309100315050402160f1a010602161e030210030f1a0906040c0302 75
    0x105004c0380800308070a46001c0750101848040600b03450889501c1c4981d14070300b0b84100942c005092030250000c0c0300740e0310150341d40710a0038200064440702071075400650401c5403003400500c2e00c00b000d0000b0a500001d543c0c1d002e4440941300c0982e8400e913003102040d103005080c0404280009e40180d048840e0031301072807130714029020003800d5071641d42c8143d401c05408521503422000038042c01003508800d1912165003401c50350b41120702416400007030b0103624080c0c001a06141111400300260400c203400009082c0c40c072644c20340d280e1080420a0080c10301c4409a640c090081c00f8040344440c1c289402c00200b8246014070000350400710308058803034403006010780810440c42100102030300500002c02c0a40350b010700c4c58180705040e0300080441d0b00004d4203c0d8684241514541961000c00b8180d1031a1038800005030b80260a410183d84098207410508a171501684500300000321080c0034050080205811450b0801d00120590012003040c000798044c609a404420001740b03605006007407039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 943867535 1250 943866285 943866317
    0xb0910090513060303180807030b060105040815040303060e061309050727050603210a020c1809120a020c01051c061203080a020f0a08040213020a030c031d1c 69
    0x1590003404141d0303031a5100d00600170f040c0c3c0040c001908580c0c0010344100303549003005040d030300d154510018221210f01c001040940c1e11683c11140200000f03021114050104102c00800040650302100402d00d0000c00042c600c044014051041000915410200060904810207400c102404803240c2c015440c01103036450540706201e44030182c6420540109448414400445101400c0c0a11030703440100c014440700311801520000d4000010101c3e2162180075060303141c09454030780c180d4480d42caa042c0050710ba5040f092980f250a0320000c603100200c2c68000c40362a80b00c0d64040c03a0041c2c01c000c03403859503035000d0f5000300003140410b442580c007030300c1c40301070b4008455441d000f00e582101d00c0303080c8000b4140e100d6002c40d000040c1800851404070040c0c901c0f11988a02002002070103108000a4155501d46a0041101c245d650b000c0d0b660300380c6000020000c0404072001030109240c0341c20003258000c282c0d035994110807040c00404540d190032403031440c16584c1e18122020400c0680c8a50304c91 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 943868785 1250 943867535 943867549
    0x105090a0312050408150402090103032001050a050a05163006080a0302070b0405220212040605060111070b0d110403060e1b01050304200112050921040b09100905 71
    0x5007107543e03510382c031203081c8482c0604000c0d4410403010703005c01c1b03070081c4070150340d4a10015045035810b09046202c403100a440031125000e400f107245081d440c1400700410900303aa00b015103e0f20043c8002c004541e1003880c644840e0781c269034541c001445a04d2030905580c0c1c1081c000e06825071082010388811030718541d0505a030382075040070900b90007460b0403004042e010440000074103102000b2900705803c08000c51400e8146202c0384006c1e40076524803041c000707010360482d514030f1000300440140346407905021001d020140c43e2140020b80305526504600c1380400e40e81c2c140d0741040d034214640380e502c90b0707060058040000c84e15017082d010480000003d41504c00c0240c02400c0d040070740316140503c000300b04200d10010f690b80c18090108100030024070071a0101e07030600b0b00500600300420003200100c401202400504011070f01d042c06200b0115800034002c105a00c001c0c1909100142a03a5408400d02581c81140d922000c2480502c01d5072030441a07d810b59480c916245081a81e02c50000b904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 943870035 1250 943868785 943868813
    0x1103072402060f191e0218030c0321030406060b04030c06032901080408041a07050f030c060f150d080a021c05040b1b1203070e100e0105090a03 63
    0x2422242690803103480e074041c0311803a84040d101450410610b42596080c0d69000c1c50640c640d00c0a80d10000304541d8441401604464070140380215100d8060403c0c9403040640c0d0300c07041b0710901c034401d1142103901d40004c103559000c0d00d010f50540b40c0490503481c0f1899800160040b1011600d0300d101040c0d040f6040c001d80010360140c00000c10395803405d0b1015040b6a5612028541d0054480c6e403950341602c0b1440ac1112200c00780303001c80d590342c0d40b8140000a80181e4100b5100b03042c2420340c400f4107034100000f0f03000036401032013520030000340302603940ea4911500c04021901d8020a00140340410440d086540c080c2040e1002020082490f00180da9820031580455803c100171034000516a41008005641054800c034181e10030155840a0028041d511138075080704400502110704803001e0311000b5013031000a041714403400c180c0424400310740084445800240454801010520f440c072004030030700c2103031348612408054460044480d039000c0f40c2442d4000300d42c60703800800104001c1b03603094 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 943871285 1250 943870035 943870079
    0xd080f030c03042603071d060406030e0f2d0c040f090605151e030705060703030b27010905070e030a0605100503060c1b0a06050a050109110c0a110307 66
    0x140d02d141070300e001040c1d0b01e003004c03400104241c07041070503000c065141e04a0741c100606007069603828440c00e6055090900c1000701304d4000c0d201050015049070503410854011074100161504503c0c3c5400055480741020b001d41c00c6141c070b01d5110001c10b007400007500c10100c6503000b90351403165a48049010b41d0900d5003c20302441e034607582c1c8000c0c04001d00c20b2582044100b50720081c4512581d000401580d880c02e0300d41c1d01045910b848c0302c1665010000100140000f4110945400013410013134014080140c150740603006c00b005403403000340f09640c0c20314007038403262207255140d0030001100c0060200811713220901800c204c0e20501075508002c002e800354405e05c408125454031200613500e140070341e4806802071f4410340c280989958401d00b507440da9a9484580c50121090407800741c68140e40c1c10f0040c00301c030314040600c2007480319030300443c1c140e0703800c84001e105c00010824980f03210711a00e01c0e45d044603000080c1c0c0390700080c640705c42455001c000900301c41f04030380c4900c1c070784950001f4001880 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 943872535 1250 943871285 943871287
    0x1110f0a14300601020109050624030a0534030b0402181f0803070803150d120f0201050114061c0b06180f030a05070b0a032903010609050c090d080f030c 67
    0x90321032036420682e100f0310030b100902031100c0c960303a1aa5607813800307044080203072001c40103c1c480007500b1401e95034070b0070000c08440100b40c884c101a41c51300544204c00040c0b1002065940700480b240005827101a60001d880480d54919180d09003003100190049900c07000781001148604440a0700e10300821f00c1c4000c65003d401d150810319907500703043d0305c0120b40e504240490004100c2102c02d499200208221004090a4a100003644100e82031030080480340e2940c03115603240d91000c3e10001d03040258008100c0c90742c03105104070219401408141d0310100400c8550103c1001000e107820040c0d45100100d0300c102c1d450006642a0841b240018181c2505c00f010490380c5880149500c07805010782c0a480d00703602607241c41da19629540602c019070f040000309180c2c52131190f8020f004404000c401c400361080058681084080c00c61030003403003503090440100c0c01c20810312a441c02040c00c144102c0c81d00307100000340032242491520541d1102c1090101424061010004507c55000340b5041c07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 943873785 1250 943872535 943872607
    0x603020304060609110c0d080c0904020f0d0e0d020105060102210a1418130501050901151809091a01081b030c0316180e0307020f0402220801110f0a14 66
    0x707441d01103804881c00c08c01140340c0074800288a040c0403907000e503c09450148c1e03070300d440031400300312403140d2040032541c0352034030342c102603112008104400c02a201d83c0c02841686c84000c01240d83e441c02d052040c043d01040c0404c10f0382c501d00b200041c600b94600703040141000b00000150b82ca81d40042482010021018080c1c100ca885d104c00d09000898003200104034950401010a0030010b050040083e1040301c11050302c0c900d8041c4540b90302c5c00d102c1480c0c118000751501c100e00040c1800480480b011003c10356250700340c0980c040b019040c0e5040754010940607401c8107c21401302c240340d0b41d003501130003004514069601d0a10046400031280901c984005181022140c0e0380a4800c8074513084078548030002d618150040308503401c00e074044811f9090324045c1c4001900074440d4001c0e03001c1c011090b10403214408202212602126010b00003008076200004a00100307200d450034040c075000c0e08102058049001c2e4045002080000002d10f09120030740740c00007400909104e41c02c1882d1092601 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 943875035 1250 943873785 943873807
    0x10f0201090b010303201903141204051c031802010f0c020901170c12070e0a0b030d08011a0403170c011b020f0c040b090a05062209150b01050301060302030406060911 73
    0x201542c2410884010072400300d030b510100650007da62002010000344c80701020130803140720265a158080025032500c2ca00f414a0890390300c1504051a000080644018041d2a40a80318413841e08042109400002c1c54945c011242d0ba48486040002c1c004a4002c20002d41c40c1e840da201c2c080c0640212003200311103082407040c94500c1002040d48035040c0b009000d81500e0000c06c859007200c0440810440d144c55405429025241041310a81c05224070b4032181800c0da44a90040d040740c1d0302c4400c481080c058456074015521550202505400240000b900f841810360010850040c0c2c3d90000540d0030b51003641c50303d401c00d42842d03e10046c2e000d03000b42400880188508840120304580c1004038048640100d07181c410028000c00000e50f171103000038859110880d00c55807180d492100d0400c100c05420388500240941c0c0000e1320f549040143c50300602420b0301c5200d0200d60141c4427241941c0c07031300c1002c44c040c1d8402842141d04039111800003503803800318041d52884408506003c1e0311040704400b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 943876285 1250 943875035 943875077
    0x5100c020c0405011a07080c0102040314030a080601080c070b09010905060916090c1209050c030d03021b0f03070206070609050604031e020606060906071a010e01030c08010e0c010f0201090b010303 86
    0x8450003286108040d169003010300d8085030500769000321f0158440d1241512103009004e6640050016126990a81c0580c50040b005102800e555291224651640401150082c40c21509480034071810030100340404e2104034415804000940082410140d6036121418000b095500506540c0051003800c915810443d9000140080f907030204590780c101b0800900c0413000304951913031a581d03800f0500c141708041c40707030003d80c44018085400061180780005d00943c85050408140e1240694548078805c0110708542d040449800450070f01c103040c0c0070040141c0c09803404032451075032000781000040091010511860003030301c5590080882c0c500b9040c96100e0051814210740210080022075540d80040d50300c050030558002d5183c0d401d620344480d1400403c01d1400718840540c0c0001800c00c0c1140e60b10741600d215004489841d9521003009080c0e0b80c00e40d01d49811034101544801c2e15500c5081400101509c0344000300d08401d06884814041304203070000d900003428044100d0555913414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 943877535 1250 943876285 943876289
    0x10501080114210a020a0303051c06050d060c12050103080a2a1103011512031103120708040c030609060c031508073602040513021206040905100c020c040501 69
    0xc01c95a8400d440400000c92500d2080f81141d02c0b202c010a1000030b224040150130042c1d82c0c06040c2140d910b031241800b030442e03006080d01e0601c0d03c08481c07041502650701d000d00401c841001d003c001c0c840080d41d403080082e04410004004002c0814113076111446a03010740c41c0207502a11000750b0302c2003100d000400004c0914078039a040301169840890700841b00c08910344030341d0002000210640f4a000103805008118a1000c0700c8050341c50205400703008031003801c0158425182c3c4c6407104540d40b8981c0c0c4a00420f401034410100140004041a014a8002d680180710304032048045486c8d5895504442901c0360540d200389e5599400140c05070948a010701081021080c1c2d24110326102410b0f44d00c0791140170f8051036125440c10641d03121424025075026403201c061035000701103132100260007500710348a5a4032489441c0f4410742440106d03c03c694240e5008044400c190342c546003808003501304800104d4417031040c1d10705803111040340c0c814911400503e07406080c0b0640b002d41000309840c41a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 943878785 1250 943877535 943877549
    0x40608010315020c1c020c0316080d0206010e0a0e071703070b010806060a0603020d09020a0b1c05010b031f03060f060f050a0b070f060e12071b0b1c020708070501050105010801 77
    0x1005803004c0e04000188190a5031844101e40c41c2c444007110f022803d04890a80071909840b400d1b008002140701401000d007074844490440340301c0d80d114001240c1d501420301c200c4851b4050720700450815002c1c0e410050b031140c0c102c030413a107856585426100b049a0b43c2000008160404540700040094440081e40141000d000030a503500307140d00020000c60f041e00c6500300b07140c1d00040c50040b500541e0010040e03150010201a8002d03550541103245600141c40e074008204589101050304800d41701e03c40c140c884000c1024210340c0ca1409201c4040904000c600411010001c0000000c290b40034924440540708000300d0369601d815100c0d1415190fa8210601c02d0f205160288081003400b010358810b2500308504840c5c101e01802d11000070001400c0001c3c1e81c0c0210252002028020300c0200980343c41250344800071041c2e9202003400e10041e01591a1610003041061900d01007600c1c242d640109013030006152800940d00c1000983c44040304880c5030b51a00c004010541e00150160300400e02c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 943880035 1250 943878785 943878787
    0x703112104140f0604120204150f030302060c040e1602031207020c0a060306140402130b04082a09160e040f06050907080103030e10030b12010e06010503070317031302030304060801031502 82
    0x203d5000411501450003100b9400300c40c109401e0039590b4542000c41d010f4020940070322410f4540302d1021401090740426005881484081907004c07194000f201d048038042d0030340f22082d4841415800c2c5a040440b4110110b1000f407040103003072299150030301c1c0900365580043c0040c41303410040c4004440e80342d0143d4240745c582101040092914100d000e40003a003250016a260301c03907018407644d4020b913080300303000e00004100400c60807000541a4000c0708404242c5071881506032403008003212a03d6510341120001300862101039650001060289030340c1080d04100b502c120101e402c81c1c1160041c01e16480e00c40508102d036040408e0003035049a10f51618600d55030540c0c44c09031002da05e030681c650040c0c19103120b1105043c842c1c1d01c20000b00c1c40c01404203d00040d1481018003806003902c080c141b0740110000003500d441c0016100d42101d82c0220030131f8071000e80c20b100740c226400040500141e202490420340c01a0303428001070020305602e41b02e2814950550900c1688040ba1080384910a48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 943881285 1250 943880035 943880059
    0xa022526040b0f12150f2b06020c0115091d0307170405040c030f0e06011409270a060614012703170a1e05070311210414 53
    0x98280101c07015150348000340e6aa92800c9001824284a0b1001105401006005100207094181c8501e0a0490220b0b810703258000004200003100244410382c00b50070007240300f4061411007200001c0380ca2405204014140f00c051001d4a0039521282a0f1143c6200300000c18001c030310640c4929004615001e0084070400c05240b62141d89101d441009032031141001c02d0805220703910012107000e00303400b0304140f2021140040140c041c0c00404907004031070303007070a5103103c1c00c80c00082c050f0704031036100c080f4400d01c80003041840410030000d8401520501c1d080b0440d03490210032551000703c038140c0e00c000c6c0100c4620f402c02d0021038529400180b03050f64070960402d4941c0c3c0c0007035441c0c00012000c11814924068a61004100303c541c0e100406106070b0b0400f00c07070010416009000c5d4240319884a440007607400407540d40c40d944540344c1c040800c00900c40680824172079020a241040e20706d0403280c103011407280440d070048482c001488000701c0043c0610002c08581c04c0d0000300842510a809004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 943882535 1250 943881285 943881353
    0x1902031504021507080c0304170d08151302070237080a080c010b0904150c36032a0806100e060301060b0f0306041401030b010e0a0225 59
    0x1460396080c5421203400400d202c0140412501200c2c64002500c6c00c495946030303248019038010064684510700d9014414040d07900c0c50140303a4a0f4030406920020343d400e941e425040040031071042801000d081d5081c8202e0b001a00c60a03a00e000030817036011184000c00d402c00103280454203010403030400e0f21020808200340d035070000781c0c9050703181d2014800391565401c45811b40100380c0341d004942c1c440000402d103c1444400003503020098551642480f4864460006941a49044c103050546400501031580c50a005000701c00500e00c603a00c4000655580703880f0f4a0b481c840201c40c6012032074030a0008409c00c80d0a0480d00020040303480600550b18ac6242c10454008180c85030f5101c403c208000912940d40a40c05180609035514180361910301000b800e0189400440e415070045107051441d1100301740c5480c895048980c80348212610740e091403804503948901401e4000a144c0a0060703c0700d400c06001040700d440040c02c2d0030f4036415454140256440b42003c00c0181d45401c4100340b00c410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 943883785 1250 943882535 943882549
    0xd110a080103060b062104060c030209010804141911040b0a03050a0b07020f030a030516080103080a03090201030f0f1e180308060f0301021b0d0212121008190203150402 74
    0x59402103c005003021000300464500d214031414661095294490752100b0611604424040c60040710700f00107040f03400c41e0a40032481a45003950100341d45400043c006400381c1c14801e800784425007030b141100710240003c017072000c916008560050a1901034412400c0038031540300c03642806c48005c0c201c103186440346510b8845036032000c1d00b840c2408001030f115034000c0021100000c081001c40f43d8811000d04020010003041d2a41c17054100140b0604603814410031419040c1c0e900074910702e123060017181064000f0000c40030304034107068a4407000b061000d5644500b01e0001d186440200721110b015181d04909086410001001441c050076540c50440c0345000041d065070608020145d9110180003130b140340208450300d0b41c5503000103003241b0004000f0b104448860300b0b0300c08482c0c40c03807500300c401d9840e88912012610903900500140e400f80c50b46262103900000031201d5042c4082e254100f150401e0f034070030540742078601316025a500718182008807c651000d01420350195003040d038009824 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 943884892 1107 943883785 943883789
    0x2010e0906011e140316020f0d0504050415080a06021b0309131e0e030a020c190e090f06040501060e090313091a0301020d020d110a0801 60
    0x101420035040d024040c4105840740514404000e0091403105207030705150007007104550b5074291034403a40c0000c0d8010050b1099040c01d900d02110081d03d04080d001d01c2502d04d40c014542e1484056000c0d0694064610440300418824901000507039800540e400c4070829000d04802d24007001203e9005114040941c0c2c542c68040e840c559445403039000d10b920381a000408520303400c241420702c0e40080082c1701c0c0d034100002c10840059400e401c85c8c00305c00c000d203195800082c1c00c06e041c42d010410b0241d40c00040302e0601601441401d0f400d207201440c0320700715404140c00b010801000040c0940021320211404075a0715180c2800c00300c3c040c0049102d244401c2c0709102c040f440742080403040b141040c0117020510740861900340004010440181e03202545040701c0841c3c1c01658080c0001c0103801003122000d619140310064a42c02c5950000d140111540d08100502d802070704000c002e81 = true := by decide +kernel

theorem cover : BRFrame.Cov 943705035 943884892 := by
  have h0 := BRFrame.cov_init 943705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 943705035 ≤ n) (h2 : n < 943884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
