-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:15:42.722758+00:00
-- url     : https://prove2.me/submissions/59c71a97-9151-45a6-8459-78d7ea67a32b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269064748 ≤ n < 269244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269065998 1250 269064748 269064769
    0x2e150e1315051302031b0405100b07060902010309060c03090b0903040501020a11150d091203020f07062f0310090213030f03170f06030105090c031906110a02030d05060d02 75
    0x615494803a0040781901c80000f450b0901d990f00202529811038102d00710300c041c00c3c0300b43d02886c002e5042000254041e414005205d00303d0700b128558071301d824001c1e030f11003009007120f0900f01c0c18581d80c2c01d003000202d010791250b4420008181c50020307214000c2d00b416085240c006100003e1b5a004100030700050764007090012403e580200313036045018507040080d10240c65a0407100350220b02007900380d10008690007070745500b070041c40a00f01079108080110280e10540088150000003080b1800003da41c59000c070b0303004848170300840c414420050555400c440224101000c0d40008001d1091a00c80c0400c16001041c10704421480c010701c089c6130078405082e612001d080500c0c00f4905a00381401031455500e440d1a444821015190076601140c06003010751b0124003d62074400050054400080e903031000b204000c0080400e9030410304422006021581c0c00c541031600c49a070088500310940140407414000c1d0061a2105041d035030b400111040104201c1c8610100019080580c4030344070400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269067248 1250 269065998 269066033
    0x3100506060a080a18120906020a02010c02010c14060a0c090f030b060d03090509042102120f0a020705041d1605130b030a020a031b0906082e150e13 65
    0x8035070039030758130b04480001c20b440700071084100c0085005e0070400201c075282035032844054490302000c1d42c440004036610160b91070700070f0200f01d61038004005076009072809000c6038890f249195140c0399460900f0b00380304c0c0949400e01c0302a1903000d0f81300c1583c1c1001c01d103005050030001c0000344525646600240f9000505a03034041c00031810b00301d00b498400c1c00c4200241c1009800c40d0001d04142c41c091007a50340d43d04003140c0408801c81909142d620100349a90180c20014105040c0002c0e0600030310140c2c000064801544250350b4002450b454601441b0a104100302c40b5480c0c50540002ea1814a20108044420b6201c80340060005a642c2038400c02507018181c40001d0b89807452002c81d14101c8000b0000e9403100d01201d0000401c0021403030200e0a200c039140000d140d9940d0103003442560203501505e40303a42c21141440700d00d041c000114265506960310540c1851941c0b06410701110f007008900c5681d00c42d0f141c401d01181d5511000c1075000490740c80030b10043c050130707201c24542a2011825 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269068498 1250 269067248 269067257
    0xc06070c0203100207081c021801050c1e03030f09160303050304030e090f061203070f060b061b030c060105121c0908010c2d090b09012001050603100506060a 69
    0x4980079902c0800c00084000000302c011584c0d00300b507007400311980d0045004c110800e8801000b083c0c11421078026034801c5d400c82c0d840703501300d200e80b500151003c4d00400160b086500c10300c0544180c40c3e14101400c486003507010007a56507030408148902d0300d0350000f44012072907070000e10881031042d6192803080469805180c0251651290324007110742003c1c038044158400700308414002c403400824a00350040300304583c024050351003a60015141e0044010184c16040116044800b003403072a00402d84188008203020f140c64032000b2964101b000c40751360503145900101c0c006c400c5007420094940900000c9410505d10000c54a5980d903e80211020307a00291001d9074071249035000721403050250020000a0000c80b0202c01c000780007003e15565680301401240c09000341d01c15206d8588100c81c05a902e0520190a143c2c2a00443c0e0002007014108804a180b82c03179000e542c4900921a020010004141400d060701007501e04091021008030041c0703444148407440d52048104d585c2890b00741070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269069748 1250 269068498 269068517
    0x5090609190c0e07110601050a0f0e0c04052e02060c0a0e010306051002030a1706100c0f05030310030308070206150f0a030c09051009090c090e030903010c120608030c0607 75
    0x4003030b15400c0c0154003040304a0390003000d102220740c001c100170300e11004000c204e80103603070b83e2410440c02c03820610444812b49040407060010203905080d0584c014102d2070103d2420f59580080f64040c40314064807a03510349184491603800e0409060442a0500741c40105120f0402c6640c00c600c1d485440e0348603050120340d01c8082c0103a4000d400c5a0010303c00240040300804001c84082e40781e511035064880004d000c4100300412440300c02d0003034010100a0440c070410641e0b07240903982c0244004050f00d5400c030000c070080008d034007000118030640001806036241071652601404014024000c0800c0d03400260400091125858000d42010000c542d40c84c800751409000c60030000c5640c001900426068401295011072500014043c0380020303000c0e03070b210380d88540d14012200010402000e2000c240e07010007007468107400c4056807000000c250f900e00f007414000a8215000d40c2200c4000c6514684c40d03007080c01c06446128010610580603601d080b1466984507141d043c020185814800c1002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269070998 1250 269069748 269069753
    0x20f131215140f0402041503031d01140a2a05070905010b120609060a0f08010506030c010921020f040c031a01030218150f0301080a05100207022215030b06040509060919 74
    0xc10105a001403148461401c923240d0400600c000001d8144512141105a0802c16035124484861407000700b01c200a00780b040d0094103c56080045184080c4081c44983e512030980b00350500c104424400c00060100c9490300b041c0c4405d5034030590208580354820310650181c800c07540400ca40c428401ca40201161741c5460000b8803001d10394202080880000c0c001250100f0154000c5001c1c040c210103c84050340030500441c0d0000450182c4007844842ca00c0c48030203820a08241c07019948000c0008054000d140b000c202125484162040043e884181010000240d0000300300000d0f070a203015860f01040301c0141c04a586101001405240101c01c0c01c0c4003000890281c5005d22101c903006642c0c1d50b0340790100c56483c54400c0041d03407180a0b28102c2101c030311140c8212a40d182d030140550b480d07072108888601c00b130a83d00324000c07440c82c0c0f90861400c10b46081d26008015520400007044c903418041c06000031921700500050305c4c0c0e8052002d00030b840200217110340c02b16400c012003c035140d0103031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269072248 1250 269070998 269071001
    0x110103021608030a14060d06050a0f020d05060103050109020f09010c05030c011404150207110f1305090a170906070213020706150303081b030a020f131215140f040204 73
    0x841c401002810301015a0300300603240000314066070b1400010310103c80901280c460084060702c500d940840303012003040c0000d240b50080c951101d0321000000fa400c400c142c0c0e510503a0b1040b01da0030205070307544040001a68040c811180500052601141003e600030240b110034807440d00c2d44d40c103014501082100300314081046805d00682c542c0240019074500303040000b482d106803011241b81d602c0b00410900e0303825074400e5402c219007003250408009000b0040c0010300d40301d08012904403c80240c0304d002c410540c02024040d079070020007004146060300308005a07880c6000044542c0c0c2c020460410256114001d072401190125503040c4141a00c19100000748030310701c0010400c80c20061a000340f50981050071007224002e4848032050380c1c0380126500708040501902000400c00d001103070070080c0b16030113001c401c410090a00d240a00312085036201d24400d1344010440e003a82d00844c0c0401175511040740082c90039480a05c09420440001514003030010000d20360405468000b42c195070300d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269073498 1250 269072248 269072257
    0x90604120c150204080604020a170a020d05153c0403081e10170f060f091608071d0906010603020904091a0f0601020c0307091a100e011b080711010302 66
    0x502d4086586540e41c40b0104c0d01c802c02101c05900c10010f6410010b44a040502413000181c05900502041c0c1071907420414506c850f400180d0b0382d4880c5084510001c01c41c501a80d0282041000d080150700304018492000242030316407451041404480a031071880700450aa005941030502c003210307a46070344210b2001c0329220300c407491880442c0d0a22003c000d400007413806403007085868204442441c4c80541e60744008518540040d07000c2000110950401039540d60001e82240540d0490144504072010004080c0c010000e2500441c0081080c5507402200808054002c030b0035403d6854508202500c46d001445850140742c4c001540650607980c07a48403044450f404405201c14002034591201d910400300c80d21002d02101d90003080c038540c0002081a4503d100400811110b814108500050f10902140d0904003650000143c2160381d0b285000c0295100c45e0707507180d1010701a000040c1818a50515902442010003490300030521f40f00443e201e294120103000c44200c4080d0048009105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269074748 1250 269073498 269073533
    0x4090c0c0f0f110108040812060f0402180a05240c1606171012031b020a0e0901050a1e0b0a03060501090b1201020c06070804031403040305070506090604120c 69
    0x24000851081000c1d003802e42d02c2c0140503041d14250003040f4001524107840c10740380544130790740034000c19001060040d9a260f00c07c030040c101e5605c21600300041000d81c0c220380300310390140800b8000e502c01030511121050040204545a4014205411001d10407031a400780189003940c000070380ca000070000f0450601c180300200c4051500d00d903500001481400c00c4600369440520020120708940e03580303100708003543c2d0302a07000e070340b011850b80d000d8808400006a01c214001d08120750000341e0f803810300c402d00820700c0070140c2926142c1182d24034211003006000d494058602179501c5000388420202d0001da4105080005005030001c0c005175680b001c0e5400200060304000001c1408110354100c42131b50602520000c42c4100d04c0341d002800e1b0b00820b80d200c4040e510a00c00145140c0c45001a0380c0c00601904140c0c281010030001d4142640c0308a170107070302050001647c03030304004003048610341c0103040d10068203d60030305035a1424818500401c0704200081c00c00c5040c18041d0f0148810706002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269075998 1250 269074748 269074763
    0x20105090d241b0c080906090112020c06270706080a021e09040b0307030b070e0a080f011b0c11150c01060f0e10060804021c0206070606031403070804090c0c 69
    0x425600060280006011400b000b480340c1c00f91410303c5000d100185125a8042c000d54140004030f4188804c03904400c030540d0411210351817000ba039400c6480204642100303607015001c0c074074080c54801d00d02c0f1283c0c4036062900030550580c88504001054200c240c5420f454500c1481d00d9510042d80640108981c10500110780207851820501c00001001103c0c4255002d0050303203040d1080584401c89d6200207407a8490500c0055922840f900c1003200070700000704107003002c9440b82030386440c0ca10300e06440e50707190713641d842e640c0e40106400b518010385c0340561805c0102400550f43e0300710080c080004a60007079604140341001e0410038802c1d15140d00c03134180200003042d9070300c1c0f0b600c003221050b2042074204000c0102084800308407450200582d0030320307250300030031751140d40c01d10138030722448005000120001d011600050380d441c00244102805800081405807c5040c5800a031040303400c1c0340b4403a8000c00201e000034102c502581c04940c036030240020104002a015940d402c09010014840c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269077248 1250 269075998 269076053
    0xc100c0e09090f0705060a020c040b2809060e010b0d09030221030f18071406040302040f0b03060907080a0807050a081603080108011503080c0114150f0409020105090d 73
    0x55070000d148911600e40300d0848513460b50355410302410b0300c07401c004a00140c020120181481c182900015819a0041c2400ca417100b588181d0f508441c805801c440c030b0300510601c1c200300c021928012000542801c102108455251560460b020303c41e12280d5981c19443e2111202414000d20405445031001180750440c01042010300d98036620403030361910860000d00c00303d2800e800c000a4601e00001f4000188040343c28614070105c0030260220403a4400340030000400140c4640c001c0d0401c03002c28110101b0070b540084c0030076080c00002000100c499000318810441320100158000b03000d074128603060f5a5000c00d04103207050600a4101a00703ca03c005050650740b81c1c24060030010381d00903990208a640c0300c400441c241c90400304050100341e05501c0c01d101051000d4000c6c0800341017280001004c0e80e20500401e4402c400302e40f444030641000c146801c00e07080a40c0c4011801c9400c4904005500701c07640060032074003c008009000d03881205035181089905d2100d43c00900d5440c5940d0300c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269078498 1250 269077248 269077261
    0xe06040f0306051e010b0903061305120309010f112d09061b01050106020a02130504050c0909010b100f1202390109210f0909151208030901110c100c0e09 67
    0x41f42e1000c1d00140c00380c443c880003d10030381000715019000c16030080103400d12280c0840303115195040030380814159541e0380c1600d603289600788640398000f4000701e0314948856400d40d041c102c0303100300560704d00403084000c064901d0301c80d84801c50b96510360032295561030b940034100d0b50b0024000801680310301c3d880c100001c034140381c0028490141a200715110b02d5903141d01c1c0701520070b82c0ca080c0d030000e250b50311820328940d2504d800c040381903103c2d208600008014203030500044400010081078030101390202c0607150b0035648130300c03c0100c0d0f006021096250041080b080030750b10b414603091400b500c0f141c030804e440032480c0241040700c44c481c0b42c0003032091402c0350038008403900c100c0d10301c04000260000448159801007403284055030741522000480c1341b800007203901411004d000c0400041040101003502080e0b400d58650702801042d501e5241d182030008107084420304031110410031010b00918030105800910201a0a04408041445140584e00b941c0030078140c0045a80301c6800f60030002d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269079748 1250 269078498 269078519
    0xf06160c1407090b0d0512090409060c080a0c02010c050405040b0102070503031809061c02040b0319081b061006030b030a140c040609180204150509070f0e06040f0306051e01 76
    0xf911403d9101300000e00d010000c009400142e00002002500f140f50800901c8191101a20030300b81c1c00350020641c00c04035513800d011500154448800300d044e00060155101076440b0b90842a41e090000708024561144040c117a8081c80c41194411030310342c030945101d03903c00d1040038003c003006000c9075110000d62180e0703c1d8000202140741d000b40301031000283d6526110f00503052104400101c3d854903800383d002d000c060145804200e41610400040d081d40030300250000e03201e030303028100d095117911501d1004100c0f000b80e040c0480f120351050061000104004a801c811244141000183c2814081c0404d041041d00800a401038852040100c461840032506691004007101d04000c40307915800c80c401110300c507a018410000ca680b04400050610703610070b04804035032075442d207202a603400006d0241c0c1c030700701d0385c043c00070300c851041d2404583c002d2807141840808642c540e06003403d00742066448d56043c44090246038445002c80c4021401840b004c00007040c0301d04201c101c0d1384030340c00c810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269080998 1250 269079748 269079763
    0xf0607080d05070917060c040b0d06050a060e0f0f01020d120b040f09060c0f12020a020c03011122050306070e0f1302250b040807080d05041b080f06160c14 68
    0x5d8040d260400002c4490700410a81d05c1940a1018181840d040c11003d40c43c540201100100b51541da40c004541d580d11701d80c150005041984d20584081c0181c424800110b060000c40d134000d180c0408040b91580e000703e420955441c00d4a0701c0c0c0d411002c80c41000005c1c1070308803500c40e0424030b0183c0c200c401615a4024400050140702d0030701492403000400c68124440da0510b00c0090030826002428210f01e40050540b00c1c00c0d481110550100600000d0844200c0031007245801c10010382c100d000d071690105050440c0d00c10396211b13401c52820005c40c0d00e03050020065800c00540d904143e0f080d9890400e0003d8140020340313540384402e844a08603001f076202511800c500741d401c0c1c100d4414550440003019001c1d501c424003c425403669506d0b80c0c015001043d0440c1c4000c0c0600c554088070207148031303040c40b5030300542d41280d84e028803000d01e000c0c1c85916084201d603030300800141400f135900040d1440c0c008121103000d2891248502040380c2c11658440d000f08091194041c09980d80c00025043c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269082248 1250 269080998 269081009
    0x1305090304051f090506181801170a1212090f0609050c041e0203060402040b21010b090609010809100f060f08070f0b070609060f140a0203060f0607080d050709 70
    0x3100460b10404481000f0b2141e06190700001c038000d10070b0017181804009064007a602528841421304044000344888142c0701e68424003c030f55000411aa072042c0c1c1d10f500d9503400c0703000a0082c000b450f8907404610141c180d01315050080030b10060003400026800340c0c0f045500420071859812282c40c208018094405041e1014401d4414050840c6424811100131084107400c41900d07a00307127161803001e0742004141c0b079030140e800d0000041181c1c40d81c00070a14031a4620746590842c407448540c1d104e159041c0c001884c45241031010803442c2d00c07101c048075681c19090904200540d200a619031401c0c803e80c803602c107140d0401140800c07a00403034200704151080080105415034a03119415a5030a20b845085040001c54004014100a8200400b141400303a0f0740450280344646402040e1403400307240c0c0b1f400540e00c9068034511081c080d03180b608099501d10a5141d03044c680c0c006600503142e0f61701c803417144000203041002c01c01036030112250241c00b03aa05003e00e203130624000c0d21880592048 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269083498 1250 269082248 269082259
    0x10c030c1b0b04080f04030f14010207020a05090a090210170f040507030b190c090509060108160f0302091003090213110307050d09060f0501050f0d080a030902130509030405 76
    0x80c000814090403154031003044418900d00ea52115454000a020029000b640c03c190100402015000c1520044c0301840c02010802c022a080d0f1030722810a104c001803c4100341d20600100c1d0059569180000c2103e80896890060303488800c0440010454501c0086d8440110f14905441c59003281c2c1d03d03403000407a10088a800e0351080c0c03000c005010101c900901c65040840240000703050305005640100c42040040781007040741190200704c80e0321500b0380006c940406401c001c146840040390364480000e00e00300c4803c1c2401c8030700c01850011504807409010803024021041c80c0b00b541170390000c03a00184003d414543c0c00c0d1000d0020701d17809500380d0241030b80c1e5520310341e603009a001d1b4000030a00f81400c240703542e4034400c0c21941900403042840400e5180c604500204020307001d1010069404180010741c0d52402080285a00c621002240a8501c441482022a1022041d16040c5030030341000b007104c4200340300003400f94400010840e900b070300c1c040c14041ca01d040040500f007501c070151031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269084748 1250 269083498 269083511
    0x303091e0c030a030e03070909111c080a0503040606050415090e0c060423030d0e1905040e07060306061b1e081315030e0d0e0103020f0c06060a05040213090b030a0b0405010c03 77
    0x202914014003001d800700301c191058001030305014000c2003022f00c008242203100420b42e070302c44040ba8087c0c5100300000d800402404140a0702c0c0c840d030b42c0102800c0b2805c1107104d4403e180000528103c0c4540007840ea41c2d10b07202508284180510b48241d600104403554941e03c0f4001c03641d00750f140404200100600e0902c041071400c000503800c846502d0f0340c41d84002081503008220300441e21401a07040c282c0c4140c0009459229401011085070400c03014004090030490010300700d481e40e6000c24204041d0f1504241c0761080103c4004940340c0000445c202041b018180900c40c6000d100010980400000c441d50040420304a80c0e068416021083d80300b084901d1003102a02d11001ca03105198000b0215416454020203029480300c00c18100076003844142082d82e046038200807070301502500032204110303142c6001c6180001910b011035085081400c8110812546181d07809905c1d1074680d545c900c0f840c555801c01c100803909500011599445c078282c0b602038040c1161070300d803802003401c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269085998 1250 269084748 269084759
    0xf0905150a02030c1b0c090a05070314060d0b0603030f07030504140a0f0b030916080a0309050907021221131e0b070c0303240806090303091e0c030a030e0307 69
    0xc50b030042e0100d1525901340506040d20171604151100e40e110300744160b85410440f900c6150440d0320038402c40703034005500d1500d034402405480590142000900742e4008100745591051195032015402040360201660ac0300003180c42c1d4401c111465082d0900400e084040550000c01881500e005c0d1907009001265801480f5032000340d8001c5040c0c030100b80c80b051280d03402d003201450b80480315a00b00c0d0306040e029240000c429801e604028581d070412000300f8141034001070075900401c8192020f40c0c040c5041d400007510b85800345200c004031100024080d0a68100491f102c4d002c5924040d04e04a500b0f14078401440344071003100132200000b11410413980c0350035400512050a410800d5081d2555805034211800980124103e05140d601c800c0d0341078414401071501209130a194103505002d0038004100c1c9090340040c00a400c551040007006030141000c1102d01d5014440d442c103180030101205d14504225118494542510441d1401d5090540c04072000400c3c4009905842c182e51304c69 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269087248 1250 269085998 269086001
    0x60a0c171303050d2a030606141e070c06030b1002031615060b042d14010c02011202030702100b030d0c020603040f020a0e04060f06030b06130f0905150a 67
    0x3201d44840d1009000552000b0038001d00040905001e40700d000101c00c00340031403010800803a20400380015518210021205402d0700c1072601a001a04004203d0405000e400c55a8822540b11101101c0b103c015000c07005c0010054403290b0f0381c0090f25917200358403a40c004006007038040d0141e02c90000d010740c1c00324a5002108a0740001c00490890b0000d10640d12812000410a4900d00010380d42c4c000000304e5801c9400508003518642e4102000f04031103588911000d0491007681002c042045010089040d003d02d00034045007081c01c011883d06000c0c00107980803605038221a420030300000401ca1526400f180842241107030040402c5030102180505503641c0c800d40340200450a0034100001600d043c00143d0341c0700d03204900807000000c040d40800c9500c030495001001a0405038203001c100324450240700d210f04136945003000074520b592100581107001600c0300d03000d01034031a0701e90060a80d90300030a041f82050308083c0b124441600d046e0b591225600d030a075000c0081d03840070031881c800d10f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269088498 1250 269087248 269087251
    0x306180d0c0209270d110601092901171f0602010e030406050d02070c06020d030e03032503060306051e01080102120601181a0d1404032001090203060a0c17 68
    0x83c01e003e400396201035a10311241c0d40102e50b00c1841030850403c5919000800c0703480302051003590345c1c840301088545070078500a01a088a2401814a030440710307079038034040307140c00c028444410a644010038040140c2c1d16481801da0045c145007180b082149503401c40310072a02c042d01c0041c0324410942c0c0c1e008100c1c00c0700e54684408182e0b40082104215885c403032405000800326405005250003000d954500b107100f00c0798880000b58104000144000e0f425101c1c1c40c6120b6900c501071f42c034614100c01540e052441351550080f0702d5003c81260320049200303a116401450307001e0713010007080c04c1c00030413404001400040e84203890003c4001249585043c0292600c00c0800511103030b9503181ea5006441c80c8500c0301102d241c4240e800e000060390645175447c2d10762400a14000f9981d01c1d011a07d050685030961800c07804614040103210020f98441c6620003500224801c44543d445c02e4400580900301124000e03600d03220b40c20a0040c0b0011079405051041d8241e169030300c00e600064900d11184c00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269089748 1250 269088498 269088503
    0xe07080a090c0512030d0603230706080109110d06030c0911180904022805040b04140606090409061a011107081f0209031609060b1e0a020109020306180d0c 68
    0x140c4001c10401c3e4141040110081c40c482000c1c0c0342060110700c0510704031507186d801a90201e4607030304030b01c0f298221000d00d42d101d01c51410251400700d0410030050245017040c401c0c401910f0752152211051414041540c080e506443d00510140e5941d091541142c0594064040d1951501019074440048181110b05a01d0340045404907000428200681744030001d1040c0d07000202420540e201c512501d82c2d00709000300010000b0f0b0994206810700040f519118101401380d45050803541103401c0d106c88256100c0c904481701703a80d444540e40450040d0085a5004049034100b56008024031003007246800130712000c3c0c1c1c490120301f070500c40040e42c0d401c0c3c0c2d10645003190808114103060b14286900e042d040407110101503e09080380000c64609a140314001c40c92154245051286400c1800b821004001001c032050811410038014248101c1900002d04285400114007940e0b42c003e403c4a02481d4006050380c10b545007103691080f0541e0515a00a12070040d400700c900c1581c040d0414030001c0d43c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269090998 1250 269089748 269089763
    0x1502070203100b0102010b0d050a030801120b0f0703020408190209100b040905060301021207080a0c08091b0d0c0e040b090102040312080403091703040f050a080a0b07050d02040e07080a09 82
    0xc02d440b2218010408154164115501c0300402003141d102d00d44006d81e110b103c2c5c40103040f200600d0400921b46079068010b6100b000c03400e6600404111800c00c055000846d040065110380c5401c00305030000d1080c1e50004406000d83c008034001e510b4050020040e480c02540c2005103581e8003114101005007600581c82482e0090009000d0360b90154082c030f41c4214040c0c001071030807220002c00c480c1c5045c00c440341e03000144504108074103101540a800b61100341800e04513864100351103603940f240d0401001200c60f0107d10713600c4116503280c075540c803101d44c2c0254400c07070415198030410301d80d107104031015103c0340448004215107041c144210341c100d90b00440351122440034190126200b90307020740140d041010100010800c0510b50081c10403015980c00115607591500c0c01c040e818030915031040c2d00c5410300d0403080250b01c0300880c04041c6d10f45d0081e168050750b039408405580e280502c0700c081c02c1c91840032501003500041210b580c1d00070301d12a1103c001c1540c803002d0043c1a1540c1d408018400c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269092248 1250 269090998 269091013
    0x90117061303090902030408040501171b070c030b01090203061c0201020330150102070801110f0c0f060106020c0a0b071502030615131511032a01020a03091502070203 73
    0xa4000010910064441c3c41d2416a1643d100c2d1042c007039030003d80c0d05445421000404014960308501808054034602020981358a02129242303d415220040c2500310034002a115041040e4000120081c503842505203081d5611080d040009400854855014034901500304144a6a030000c50541c40d41c141e00852801c5d0641d130041d454441030100c101c103e002e50b110200e10000f00600790510501c0b0140100700001c008000091801200d075200c05a01d901d01000a200080482e003102c03103040b21488115036807068030a00d5854806414045940b50280c440007052440d80407400f204240d03400c50740c4403038540d11800c28504912418070002c10140d40c84000d0713404401c0079005940c3c4100c004010840b540154030405030f4550007804110340f407201031601848608900041003100003440e00c0d19080f042c0001250315034910442801d00c00d00c0007040c4a0220243c508850320a0b940c00d5070000355120003180340c001d8060075200808a4610610380550420f110445c425500e10540040050000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269093498 1250 269092248 269092261
    0x103110744070819020a06110901051b0712050c040f050c03040201141306081801090f060e071502100c0e01021005100e0c0408070603111801020a050d090509011706 72
    0x35031040408550b034042c02c1c0128001404d0040707084030303080160303000b80540c0101860603000725007a07105a20340071700d014007180c49141d03800800e44807820a40d1180e403041d41c0b0b01c681034900d07045030382e403050210026800502c0c00300900854400c0307611405aa017448890070405040e016181c084031042c81c0803d00f403000078090741c8504040702c0080007040c030207440c0c1849080d841da91200180c0107234021841d05014000421448600015541d041100800c2207001d181d6401c041503818042c040d01e11a2210b20100d008142803045400070140d040108045050104010b0b4584110b032413440516850309428101c06400380090f800350b410140c0c050603220944546e05401000c0c040c9c045800080c1e80d400c04039456001440c6540110104421103031218500500c4c01c1c60008517030020801c040c00c11010220328281c0d07500340c41e5012154000c116010000c0e10040b0724015038000040d00b0fa03ca002d1400708101c2c0c00070110b80a035074040c0c0300c010311603072122007050b400144400400c03240c0d400030002911 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269094748 1250 269093498 269093633
    0x19020703030c12091a0a11010e031209030c010507110615030c01030221101802040b0313020609030a0605100b03040210080c0d090b010504050a151401031107 69
    0x81c0f004242480c0880c0d0781c95184840c0c000c1880450f10b01d0110001440100c07454000d881e04000c010840d000303208100d032551074142c40303000e80c04851052400c1ca90128007070034014400e540010006900800441c80e0440000b04020a0301c1041c104501a21001c1260035a054444c456400e90280081c8011305098004400950041100c00d100c030400b400d40004040440c0300260142c00b109107007948190409843c01d5500011820100c1114030401080000026070400e4030f600c500410995035000c50b0b6400443c955120b1034056950501030003a400042041c25071000c0e004546c2e00003001c080b1074503880b18822030300c402d4801940c00f17030650040c3c2c25264803d541403680240000c0d0414100b08103d200303101601c0791980100c0b040311030b83d00103000c00c0c04e25104050340708802c002c1c180401580d5840310407901040d8042c0740c0905030030740006100359019400680816140d0b4010b01e036202040d0074500c50031140075008400d15500b00e80085414100c40c08001c501581c60b0440c002c1c04600c441c24441c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269095998 1250 269094748 269094773
    0x914010e0915030109050606190f05011805280602070e182d0105060103091e03180b03010810150603050907090504080a0201050601020f0a0201080a0b09040819020703030c 75
    0x880070490405507a560348081c042c5daa031292040c0010202c41c01c0c000d0070845151800300302801b00030202c8000704544245809004210703202800c205030982d80303000d90482614590742010b50024407100300c10100038900c0010720703003540d6400a0a910f0301d071030781ca08986460f8030780304039549010200041240000522561041200900100d440b200a01710600d1990401024030401e41103800540b41440c0c4030a0103811350045007440c040011010070764070022100c04050001d551000c155032020b0415000c7c4203c11b00790b41040c000b14002c1c1d503445540c121a94001d02518900b80607114130b11488038483c3c0540d08100103800480320185051450072401440010601c0c1c1d00d5104480000a000c2d0a51140a00560103403c040d41e4844003481d001c0d003910006010241194030008492220320404038028410581c24070f400591500c1e248407400c060a150385071980d0100d4a4020300040182d86401007550348201003100549260081c001d0362200700910020300442d40862040002416000e01c0c034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269097248 1250 269095998 269096011
    0xb1f05030111041707080a050d0201230103061d0303090a0213063002040207030e031e0d0f0e040c030504121107030308130605010e01050a05031b01110f0d09060914010e09 75
    0x5e843c1c1c641e60301c404074605040418107503810307044400300110303642c0e080c010072580c1e10140d541c1c02e554516006080142030414880076224035561a408041b03c0185014560b82c640c02c0f00403a034aa041841410762a050036410803845503c1d41303a000c00403c1d8207402404100e602c0581510088849d503004805000d03a00100d0f101520442500c100043e40d980c405409080c2c040c2e500c4c01c48070f542400500d840c1c9003032017140440a0841c05c44180c86c008001546034014a03092803c41c0140880c00390a48041c02440d184c0c940c01400c10790b004111951581c8103610aa01a00d004d08450035900015115085103d07032a8070035810550080c0007082c0507006441c0c00c0060f004004000301c1d160b444002c100e0b44280c014106203050b540041203a80782110400010300411400f03400b80f00c0300c400d161207141040c502400d043c407661080c0c2040c1c00c00180070604502200c4026075200100e078a0780180209180e0003200c000c03801180c004245600309101e82e005031081a11049a44000101000300c14038004104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269098498 1250 269097248 269097253
    0x304060209012a0606051e06210a05040c06050412030804150e07151b061a1f030c09081b0604050a0807092f0d02070b1f050301110417 59
    0x30100f0954440d04403516101c19010701c003800700280c0741c05000c1d13a00b41d5010600c0384c0c52000886031442100503160203d8403040707d203980c2c0d5425840381207010309603045800352001d070791004100241c0410b0b00480d2146100c0c0f50f0b0304400903122102560540560701601400461701c05203100000d005000c00354100d4042c0400f80340d4200c240300c0c07460503140c50a074082c1003900012030810540040c09009158030f04a41001c000803170418004600c62690300c90040c040355182c0074072508482c0340880d4407114081c040c14450a109800740c02d00c0b442201c05076801c0009142c4010208aa0310030b041c4030080e1000b600142c20b019440b0002414290305c80c0ca0640d510030b004101c00207a070303600d180074800281003400c06880d5aa15120100e0212141222540300240781e40d600110340070b0603040090f11081c10a0b14041d1180d5903810f0340d0009006032030000b0f04c90f221201c2848024034954540300000481e0480d40310881d5221814142690843c2003d0740300e1207014003060103d241c42c130070a200c5400c00d1408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269099748 1250 269098498 269098517
    0xc030c06100303090e43090605161103150915010605030106050307020715020d12020405090f04060902060a200f030d0c050906070609021c0314031e0108030a1112030406020901 77
    0x80000d07100103400c0c8002d81c104107a0010681c2d9108507540c0c203d04030350f0b01f0701c00340c020f10f801d2016000b8070030040045901c07802c0d40d80140400404c070f42d01d11f028480c0601112941e8111101c80c0c5032414058410340054801d02d006044060070598545050385c1c0d859440a00b1070f46440002c2c0c0f52600040d12160960140140120383d41c00500c0f084441c6541039801800480b81041014013501d0343c000200c80846d0041006119035103882da941900130090100b401c0301703941c07541040002040e007080025800440060216120b07540408441941d0000c6002c001c1440b8511880d103940c0d24035001028619042803100300d82050040d406032103089400d04006242000c00000a0b1843c0c1c0300250483c0e1080d55883c0d41c0003507007003107086400c1030703801e07003808031061151a10702030590401c5040d500d911250000001e00110030b02480c000700d00076414620801540c580c0072103030b2240c11403008070000071599401451004bc00140541001354152411440c6484d151202d20107588440499414440e6000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 269100998 1250 269099748 269099791
    0x3120702030124090f020301031112030418021e090d06110c0a08040602070b250206041e0503060c1e0a1e030207050c06090102061504110c030c06100303090e 69
    0xb20820500f80d021044021028103122003a0100c4003000038180d1002d10510060002682c1114084565402100e02c03510781c0c3c20fa00742c554514481d94029070f00101c0002e66001040910f500074006034038075020361556000d402d042d0303040303940260700c40c09601440303950308036012500ca540030b0400540308990251414171030070481e41c5800398811049620100000b02044a1541030050748054031008032000d1426404203990f00c40421b1035425011074004100895003155070354011940244009480128100c50468401c4038402c503e10943d4000d006420000300c504c0d000ba000c071441c42c444100e0140402045200740c0906400040c038100910a0950461407521043d4602d002000203644c0c01581d2807415180032400c0004000c01280141804e004805090b0b0300411100d1340a10104641540346000c20000340181144604079906c00c41c0006140010038800b10040100c1c010040c05c031241c5440303030140d4000003d8144000390000d10128018804803003103c001c07075045014440441901420764 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 269102248 1250 269100998 269101031
    0x31303020a23241c0510120308070e04180b07181a0c060f0115050a080115140d0204030c05031501060f020c03190203010f0501061d01020106080d2c031207020301 71
    0x102c0701490510280d1000341001d140c14091140c0c881e003220309402d085481e04940d00c047c030349034403002801d0201c41800111401d100716900780164a00410502c480e2000e013207090000a0010001e503410811380001400c0f042c000c54620700400000d140600a0506e0001d51310000b03210700280b00303072440b000c001130550341c00e040101500070b4140c4051011294541181036000c40c0c240300e40d4a0600405004941340c003600611510f04403440d41003441100840140e080700c1307200c80c032242440c003c040071990351140322255024206503846a507286083c00c0c0c9441c00c240ea14140349480c5480b02c010840103003c07035841031001c01c3c3c407a03007d401210010704ca100c1c006420144245441c0b2001000003210005601d400d003e002c601c400310f140c0401040d4103003000102680c541c09140c2c0301164040272402c00a9200b544903400400b0007406480d11440103050043c02d13145d04100d6542d01000051081c4440d0000008110388602c0040080541d86d40d210607284080c0c001a5040e40d00d5583ca058128600d07020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 269103498 1250 269102248 269102257
    0x160804030c1410020d1205060d0b04050f0705010c020303070f020604030503070812061905010807020312150a0f080733020a0605011403060109050c0903031303020a2324 74
    0x8045002802c40000b03004400c500e0f000000110360001c0040708485810149501540030b01c03450200d003698440f030200e652101001e100074003440920041000b0b1020210f40d03070030452412000c0e6001c03180c0d540011150901c1115021354590001c200c550b00040300c0c0c294a0310f00c00c1c8050300c2c11b401c1c69525100c2d54115001104241c58100001856540044080c1d00036580600200c80c0c0c1c2c80d6103007a29899410f110710300c2c0180d074140f140308800300f05014020001d840302c601c615100d44507103140200e00b40380c0c50a440c044050181c0220680840d8199080c0b54031420b440c5076a00802c0340c81c3c6003a840500c0d2000900603000441e40012041d040280284404007000515400802030840103160580894030164003d00f1a52030403581c0004e25900402c80703a044502c000d10100783d645914000000520804d04203d9041c40000f40c1e4000b00c0901019040880307000f02e0700c1605065441e401c040c659a2190601201440b03400764915103443e10000122144000c2e6020002c03c810021107040345902c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 269104748 1250 269103498 269103509
    0x120a020601090501210201031e1505031e030d050c12010801020703180501020703030c050c090f0f0912070210030e120702030f0a030c0308130b040f030e03070b160804030c 75
    0x31005005492140c040c036401040d41c0c00320400740c2600441003080704820000c0007410540c4441603002004d00324109030306100501c4400b045a031a0306c0320703036410011080c81414000c1c0661340500700240720024500c02004091000f841c43d0a2020850340020b01c3d000f0a0040c03800d0040c071454000c1c44000c00c1041c0a443c007500010381d121414100509208510b503002200600c00ca0424071440e64003140d890b0490b90f1500348800c04031814600741d070800003003220032500501d00c0f00411510f05900176805010700e1154114001035120700f48219103417940e44103c0a4201403c01c0301000508010340100c0c0d042c1128030300060b0007040404990708024884000380c3c0070081c00310b008002e5207024040c03041c150904400410320001e1954010b000c50800d400041e050280140010f981d55285120441c60039910441035201c80c5098035002c030102e04100016000942103030003203415410b001401c0c100f0344a400c14950304086840000469165005000f11400103040c4400400607449070030071400b404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 269105998 1250 269104748 269104753
    0xb040303030e1c020c010f0311130302100309110d0305070c0f09150e01030809030a0c0612141003021909050a09020126011404110a020f070518010b0a02120a02 70
    0x98400d00ca00e0440d00d07034034080c524048510201e84003500000c11748440c20081c2000811040400f0f4250010040b0f20400044240005461074038858006154000d0f01d01c02c50361024a0761041c041102190880c4000501044100c0310256182c60b1007582030f54240e200c1d25001d4030380b038115a5004000030f41c903404440501280b82c0f0600150181d03000300180c030f81c080c181010072940b500c6500c8521040c1884040c0c420100018900d109480078428604a146c1010b082c02d9042d42d200390050585c1d00c900706c00751849140c00c00f580003940c0710a44083c01408510400444142150200861642c480907044070f0181020000224030350103005240c800c100b041030005403014180005010094250406903c0346002c051015051103444042c905560301d035008500c4a28040b400300e4024a10400039011241000c62071901080e800200441c0007034110701a1030045c0d80e54000c1c44100d0701803160401c00003d039440140080007500025020340007462040f40c5c0798042d941d803030480a0f40094805401038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 269107248 1250 269105998 269106011
    0x30b34030e0c0d0b06060d020f1305150703080406052d010510030605030303010303030903020313030f11060c0d120603140f070608010303170402010c0b15030105010803030c03011e0b04030303 84
    0x951091014500c029401c0d00d4000d02260030740e80b002011440107000b103204040126403029148400d07810358010500000d130381650b80000003400070950076544911440740cc100c041410382501c0a03000d5038149030385501d1368469a1620313955000034080082c20022080d0b1404011410032100c0c48081181900321002e00c1015414981800794803004000403905040c18060b04204e00c3d103001084a0441e0303014940002c2800107442c00324110303c20b50720800e10700c0b240e00201000340200840e0710891a48151801c01d00b150a01050041c14060818981e1003504801c0352140510700401c1e0500710040d4091000606a46035642e0303400c080c0c40b40c42c58003e503038418001d80b11000410031940000e4419814150015859a83e005086810305030503041441c0e100c2002c10116401780060f03c50056001030f00c1002450107100c0000d1020340b04041e20720130740c206000065994004402c81e8044d081200c0070340d29507030900704000501d003040030244c00c61140070300c0001040070001e00600055031080c2e8022806 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 269108498 1250 269107248 269107271
    0x270e04061808270402090306160203040b2704050606090d061401120309061d040f0e0f030903120721210203060f030331090e0105040302011401030b3403 67
    0x10101c40c54482c0b40901d01c1044916095500000c01c2275011072001c026180c20704140c0012801c5008030350040b61810b5003c01c5a452092101880ca05c40d0881c41e500d00b80002c40540400041c3d50b81941c050760000c1c000c000c94006800c081e03144450032806000003185000c250340070004d408ad402d0703108899240f02000c48a0405520045460051a892420000e01250303600c11a0404003d101b110f0301c503596948065125000c10340068514400c00c200741c400924409011585a600004806101e0702601001025804130301080e100c0c4280c002003103000302552030302003413103040011000005001401441d1680c016501014000303541c14802e002d80c5a013443c60900020709404480180300e9003050000c10241c1c4060400900b07000600000c1c000c1c604000c42d00303400c59074600e411800238241001042098070205400450080703100b0f500810000301990551066a002800002e00d004864004524010000ca403500d40c680144d80c8003407404580c40c081c80075421518447e0700042074550100c60341 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 269109748 1250 269108498 269108557
    0x31302030a1a0606070503040905060d020d14070f080705060c030c030a0c0501110c431a030402010c1401060f0e070801090c09030f051c270e04061808 66
    0x40104081da0014140805d650328291a40070300d0040311030465a881c002030880d5210f5420301d100710303006482c4c01103030021803c165613400503182c40c40550303118403a070004018142c04025001c6401d50806001036900701740c00c01034150700c0400300410030b100500091b1131020081c0014640001507840d843d0852105150850a42e074541044c2001c002c003d2003042c3d1090303000301d440100c0c0d901c003402030b0900910304551441c10320075400304640e500d043e5058000c0c08480000301c00003a5280311308a810200010003440a03d4402114028006000509004002908400100c40d100601000815000e849414400501c800382d4403c1558a140c030303003031204694100d030209002d0300d204a41071059400f11603002d000610a13210003003501c65000152000c2c4003052200c8c211281c00c60501c102c0300d00e42c0c001d00038044020318100c0d1003100080b904440e100c0782c0b40d691510458602d481e80901580c5c0f951909030040064058092202112030085800079280000400005010440407104207442604001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 269110998 1250 269109748 269109751
    0x203070c08030a0c02010e031c0e090f090316080436150b0a0c06020309010209010206250f030222090b151b0a06091a0703051605031302030a1a 63
    0x44a4000300300007a51558440c4e0040001034081c00d10b2404115881c001c2850003904c008482c9922046611080406921442e001d803020011549030025031130b558142d07405000309076010910b540c0304010060021b0031108040210f00c0c0500115420706a070f40244034400940e10082c2c43e030450700c0007541110b10404890107038201600001c00c000c7c11010142001c03030010385000e610706200c0040f4a10070403074070a030102d4240c154040b030299200d040c1103003094080c0d082002000d0141c0940d10029402039040e04070b014070403800703840010026a000d103040e41c4410900305000101a020020350441c458407482e00e00c0a4440c403141406031070703d0954000100c861081889102e403a008a502c070300d01c0742c0b04060701d05000245113290390110410604601e0b041c0d407032200601c0c40d820074901300184a8480c043c1905103050381241c4107542e0750b070308080b000c03540300301c4150070a800b0700c1d600d9126141c4107401840c0c3c80f0491130422860300d10145c0000340381005220045440030303000403d070340030001e4591415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 269112248 1250 269110998 269111009
    0x303041403160813050d06061a030919060b0d0302100e0d0903021203071509030f030b1f1b05060a18020d0303090f0f0311061005010c0305090303190203070c 69
    0xd60a1070469074545500c841d0785032014043d403c010032045002d2581040f400010300c001031101c04081468944100a09800c2c49002c45803900f403100036400c0d61401041f24825060400074048034900303810f560228a002034400e8400558890ba000915103030341060b166150b009400415205c2a40c04d84a81070392110140c06000d0b4101c100b00c641025004203060056980c1101c0d81580b40904212952850042440180a00c000c861010030214903a03809030b4901c0f80a40e6655442c4001c103170054081c0c4403a1201c05c0e42000b01214420a2082c40100043c0c2010580c40c0160303100d400324a81c40034641400c101030711107030060010b04c6100050f41c4a544002c0320648428456110f0170b400007030002c0c8019001038145034560b50082c0070042d400b0b024011055001003050310b108036070300b801040e08003074044600e000d11400b404100b01c0b080e0310640b10110347c0141e40e0003011030750b250350468468004400700f5415210910042501040036825032400c034000390300a54072a012810a02c02050f200d9005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 269113498 1250 269112248 269112253
    0xb1c0510060509061c0c0507050c09060d0602071121070e07020303160302041d0703150506031b0702030f0c09010608190c020a02100f030b030105010b0a260903030414 73
    0x80207030a822005499466074100d07141902c2c0d10724540212415002404130041c1c07a80b034504404080350304140035042c61401030003105c03800c41c0c18605004403484140e03000c0b5407006440d12440001034082d0018002240320f000f42e90128103800e0301113580084002c00c0e8030a10701414090007146001001408000e00b10f061603501c0c503007450356019480f88800340c020561000e4546a601019000f501150000c04486880700041c84030220b05080995054407006c0020b070030000d070390354155802e03d41d1400b5100001c141c40e185859510010101c06104c5198071210346040c410b2801580d8140803400246e24000c1c082c1c101c0764a0701003006202c950582012081c0038440c814041002800c10840014103a0640f0020f0180400402a8030700041c07008000c2d806000e1504450720300d94401c4400810341182d440904c00f82c0004000c01d400d0b640240036103610f4507028402040c031640b144e800c002c1c19003078007240a403600500380400c0e07001600484a40c403035a44008203020410118140822928040502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 269114748 1250 269113498 269113531
    0x90b010621061a130b070c030b0a1a060c0703021503060414070206060f15030403090503061303050708031806040c030b0a05150f010908070905010305010b01050306061c060b1c05 78
    0x21078003c0301d000d0b10429900d200b000c00c40b83c07101400c076440f200280544500340d64030b0381110b21b4000c1c0e00180740e0000b1a410480080410440082c0b80152452070310b80c0d900c031955000c80403082c004548c00c010764289403840b415100002580700c110841c2104000501a1607892a056081c002035030003000c20054a1340440040040190780400d0762a00a58100c0e0200e1a11442c5800103149040803040d000418800006010405810040300012110150309841d8656500511480c003150201c1f000b9010a1040040c07100085072031f001594000da640c0c1c0c503001c1c02100462690300e440310495080302d002c00a00000d00c140600c0000055018070b1803c3c0c01e000c00d2601030009064102ca440310701d4040c02103c41004020f80c003420341c0c0c0010b00000e008952269544007200c2e0b003d00400c5c80f00341c5155107071590f440384c0741d4416002c60340315210107002d283c60100500511037884003e03410040c80c01e42d41ea40042a8055030700010803280212080c0343c000604400c1c264030880304007504e1400c0c259003200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 269115998 1250 269114748 269114759
    0x10b010c02010903290901050403030e06010506040603020f0d0915110f04180e06090a0209130305030c0c010902030102040e0f090a050c0105090a09060f060f111b0301090b01062106 79
    0x41e40d201900e603c032442d50205d00c80c101c1d40c80e902d005041e0301e040344074044004220a10005510641c8154041e0343e013800001188941562260400c1c080c594109808100a01c04903000781c00900c03002ca83d0007041807030b2408807044041280c0c10803038110389405810030180b0b03072a52280501e84c95070b400c04861070700c0c5c03000d40003204891f44100d01c03d00c40c0902010b0060618100e00381d0003620a4803644c82583c1c16440c0c030544d1592640b800b0802284140270302808038403150303c02244844d10540c152203880c91030b201c2c0d002c400c00c9500030154a0b200c0e03640390301c03a58005032804e0014000070708004480e000e250901302c0107681d0007031005280480f0b5600c0040e2000128030000b42030071181400b8200240ea03204d042d40401d26950380e40c0c00400929003062800200d12080700d0310384084170701554417100005141c0e48122540e040504541040c0d50059580300031030820640e00090b0094000c000103500b1070640d0320260700d10001d81c80080441c2554031649021003070761045000c0124849000c001060409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 269117248 1250 269115998 269116007
    0x60810140a05011d040f050a2007020d0c030c03150f02070201140a050c01090b01050319030212130305011e06050301021c020f09060313060b0409050a03030908131205010b010c0201 79
    0x1807040904105441e40c1c0a01d000c0144008003983c910041c009000c3d40c6d282a040b0009060147c5000f15518a000705014030303441c03812a804ca80d4032140441d41c0c0740075081d80800c400f8180700041665080d10408000001a44a07805030004520402e110003048030031902120455611000c41e2008600410207100142e1b03102e12200b41d10340c804041652074031030042045646010708210101d00c1d40ca0000c1c1d600500c592605018120785d011021110000d41d408200d00c03000540910080240c0c0c041c501400c6030b000d128025002ca030144145001000d6a640c4401d401d440020045081e21000c0c41c9903030101005074014140546010b034000e40c0b51040038a14038101500c00507040a201e80d01040c482a1807405100319141000b00800882e20781c1400310903100c03148603561044070603074601035200e00c40b407c003806040350294000c0090f0142d000c841d201034018001211040311900400c000843d0700140c0e403002c0e08041c1842044003400d0104524195085031001008a4144003580071500d00503a0311 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 269118498 1250 269117248 269117269
    0xa050418060e100806072708010609052a070f0807030305070e060406020309120a170414040b010e130609050702101a0306060114041511160e06010c050c060406081014 73
    0x1985040c407c28802c0088005080696030203405038984010b02c0060b41900542122058801a113400c102d1070b240d07451070346c648070821801c010801c0340c6400350140301015940a84001402028401c0c50300c9a03650725465144d004460481c040ba503034400b070100c4240d2210445004060503540145010f04018001e0342d02d01520804d680300d080d0720140b200740c00c1c03420302111001c541c1c41686003020742d40403000c12105030420301801d80410143c0990000f10700d424080d0902c42c94040c0c5480c001812036109004400c0300e03080300e01c40050303180c01c5c0c0018007104911410b44144020303400f504500c0d9140301c07804151405000d80b031903410300c081d88464640e900402c0d9160409824249a0078810b40404040100d004d00d0380865144d05010400d10b140719007101400d8000480300d000d4801c0141c01401d505041c1600d4040c80c40c1848080c00040d4095000c1c0c03903800f10380e9014400300c07064021b0307140010300c86910a0700b004001900311001c1c00345031101415040064100500d0b80c019031b000060201b0302c200e10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 269119748 1250 269118498 269118511
    0x2010902130902010507050304082109060306010c03030902031020030f070c020a0806100f05090f0f1b0301121110020a03030507050f220501030c050706020a050418060e100806 77
    0x36200d02c41e80031a80114221a0ba0b5940300e4143ca8a1715036980440c0d40b54401d01b506500038800c035040361080703c0409812200a190000c0032503080d925408011134a091142e0800c40034075035030744860005a178040080c03928601040c03001040c98080e144010410b051038003070f14540c0007018002d000c0003c0c6600d80c0ca55100c895858004000c1d1903a000069603e020741d440860240035070340071f12070039420001c0da080582c0c9038800d202c00700b19920310034000340c03000450741c109040b40c6000c085024034912034a1603410030501826007925450000255000b68800e91219546403146a610010000d0314443c00450000c21205514820307205940031b5114812484000c04041c3d481000811042c040d60550f03000207907016156488040d0006d042c513a1610426441d41d100c40c1d00743c1e0020385980f1034000c200c948945684c0d01c80c1840820b5036048069002040d003d400e03c0f00601c030104041144060603041036800030000b043e960703c2e2032240002e00f0005801d888205407c91802d0201010016603990040c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 269120998 1250 269119748 269119751
    0x519050a0609051203010e0916140f0a0512030310090b03120a090e0403050901140306060409150e04080310080105010311100201111b120a02120703030612060c08070201090213 77
    0x44840c0f8049090061141c841c2526000101c00483c1020032554003600c03030303200202103e251418a040c1c0255100403403248007040312124039000c0407414a60f810782c44006028248440e8143ca800005110b80606842d4140950000c001c0101c2441d4803410f2000070011003000b000355000000102c1d440c4c914a0701d80f01041c44001500003c0f00d40300d1013040e001000b440310014030034141881e000b0326592100c45802e001078856415000070f84500340c00c490045100500682c0fa180c0303018012030142030003512480308480325000000d6403015200302c40d40304074403c3c000183c2e81d1419081c0802d06070709540241205030300d458018000611071980320b03034290700110384890410040ca07604a0240401007074040a42c040421b036400221181c0c20304202c40303c1e00304140e6083c000c0301084881180035444070100141c3c00384a80b40c40300c00380b8034000e040075800703440c1c00b1030400d89510301c18501d10900f89040f145650350b1940540350990000d01c1c41e800140d5480244510280d540004800e40c140911114005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 269122248 1250 269120998 269121011
    0x51503030702061e1308011506211508010203100801063005070608181f0c02280303230103140a0f050706090803040608043c0519050a06 60
    0xe00b11041030002507034010740c3c1c5d00c41c103402901005d04188100340301d560811040c00900701c14101d1050540324955200400c09001100d64220f40c1c00c01c240010825545600480c41d5002d0910340c03c010745207a2001603900d06141c40003450500440e40a4a080c0e413400d40c0a01c80314480481c41007100c400301c07030101c82ca0078a041080c2c861520107280103041b4428108009070064001c5034041c45800f02d019501803a0035420707441a280c01381c0300801041004500760811120301c0350b500030421030300c081c4100c4e80c4076064507901c5401511500c00c844070b0030049002c41801c00d43c2c580581b000c10840e9075503d5002544c6101701c480f00d030406001c020200100241b07101c1030510100f1201c0100d54010000c80c507071120700e082261310b0b540940070b0b1000007600345a01140e000b00c0081102c085554556803455036a940f070301c48941e100e02030154254440341910042007551200c0c40c410000f000c0700140c800e4881d03403915100b488d0004044c1c84000c010404074150020442c0850403950268101c00c02041d01c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 269123498 1250 269122248 269122267
    0x412050c030f3601110309012114090f1006080a0f170a030204050405250e15071203050a15031e0803040b04030207060203090607020d050c150a020105150303070206 72
    0x1100c0700c110000300c00072605048aa582400b46504007400b203405e0301c400c072425004c0c1408a40380d101d282e000c9400320310310160001d241e100c42c4203000c9040c3c0c01d2074400035084c11240304c2c0000014090710000140e40c4041c4031191003020905c92402001c10000003040039514040c41c13140c07610300f000d0000d0074251003c903409043c461011852111243d20001d1280d03141058507002d00250454088e8078011840e00c0700140c038003004402c0c0300c1d102d1403c03400b42104580040d042103440c080101d0b00c543c2c1200849030200503051040014111091042041c034011030310300b900003002c03a00014800c0c0035860801c9055840b500420724148241d0b60040f07540c1d007001c012100344402c90781401400a015000010030002840f81400c034403070240b80300354240e81e042c42d514141281c1d40d0041c1c00c00035501040c05c000c1400146400d01d44607001c280b040d0706950700a0100d0001031014600c00e0090380700e500700004c955240590a104465000d80041007a2403004280000701c0e07a00e000c0c0510080c06404005050b199 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 269124748 1250 269123498 269123527
    0x302010e06030709240e0405010e0f04060f0203040f0219030c060309050304170d080108010c0503060f010e030a06020c0d08100b09130912120b0f01050a050702090f0412050c030f 78
    0x30701800010f00c0500c5840c1c2c00b140901c60880201c3c000040c003049004c1b113a41c80c00f40902c40c1225407840c0d800d03030144c6a20714080103070300020740200c5503640e580d2030081e610001c1e80055413246015412024145601d801070003241298190039a00c00d00b0913246c107000142103000e12074291003c0f4a00019007840d46c0c9006455841107403c8400b00d0200c240c8041c0881100041c00c00081c0b550b6a100402d9076030314051107003a0340240220b03102180c414000a052414400d450410380d890502d040d0ba20310104201190030400780300c0c420343e495900007604501032038003084602c1c0148585d04e041240b9241c10f0070b80307010070a502d02402c91650800500410182d50785001242240c20304bc2c01041158220300c2c120080c1c0344402c6010000c071380c219000c0d0701c0c01c0d00c1710710a420048201a041d001101601001183c90f80d02c65542d150620800703000c6000562281c014003413107000407601c0b04150f410a81407185136444034080c40d100b040020007084800d00c0010081ea00344801d0030121075182d010f00856001c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 269125998 1250 269124748 269124767
    0x20307150c08011203140d020c01050c0903010c090f031b1d0105030d0c1e03020a0215130e27071701050411220c0903120302030a05070e010512060402120408070b0603070302010e060307 81
    0x4000c2d40c2000d0610114840c880000c000400dc2140204100e0840450a854142a601c22201c0c42d001d2003008202040001940c030b030100b5020104034007415102d0126103083e41a2402a00c2d2003032110005025905082000c103540c00071a081c040e90114241d900c165861044080040806c13403156110b4003007500800281840b20f50081c400c3d01c051300e10003072580c05078010008140d03810303440c044c0000c0c1c0c07060aa49454054140c945191803070704404034800210150a040b685094411780d50300003845c001c980003540007103150700d0005c10701c6d0030f140c01c2241c0043c48030224648950f13041c913040c801c0354010009001246020340000315010618040c203840b494003070350000e407e0802d660300703141420394154000c510649032880200410f4413107000807601c4110044005001c107508201606400c000c01070306540c00100100050320b44072018914031411a820f55007102e9190000c43c910040000300121741d580080140c00400e00b55246400007010882401925401b4501c000302060300fa500c030f0200384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 269127248 1250 269125998 269126017
    0xd050a02060c060405100b010806040515031c08060303040b19050906030a0207061a030619110d0504020a0e04020604030b04141c020c03060c0a03020307020307150c08011203140d02 79
    0x303a07182c860b03140c4000c2d141c280480d41101c0a001e4000c41202c1c600f0503114042404006955140e00359494100340001040040d01e88060f111410382d03241e00030340e01003040c40d0356400107070070011724403040090240451802601c03240c07080e08180710500544000505a596958400d00000c2071064220400c0e10248150400d4a400c49070000800540c202140c0040241601c500700800c054800300d50348041810400d820140e00d80c110402092407031a1b6100307400031002a803c40010703420600a101c52566100d81b00c5050040d484200308010340c41e00e562240300600c000d0f02d80c0c41f840d00e850340c001207040c4074074000204a040c4500c045801c0c4030503900c4108507520180300315044914080c4081203103020541c2032000510414209031001d09000c5802406801104c1409040c40c0030801c00340c1c0039400040c058011071200f4041080403541c00c1c1d107120000000e40d900041c40c0c00704490000c2a80c58140c008010301c601421451001a80c00796649c0701c825869018152203030302c1094188068803d82e01103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 269128498 1250 269127248 269127259
    0x2091503010b030411030c010c060b03070f0e100f0b040b131d0114010302070803040605041106030c04060906050406020c010f1206030b0603061614070804030c0b0a1215050d050a02 79
    0x490b1415802c030041d8021401141c40e8088070565804059503080c0c407404241c00144105d11050024042c0d0300403200c40600101502c40403074484000d02042c40c4c096220382000c402020034840007080d01020503000d490311704e4001405030b0400d41c081d4100d00c220320400d8944080010940034034035a647c40c1c00050820705281031544400000310350401c01d0203005282c952600c0c5c2e10b00070a6076000c2e01c00c6440b4150303c0001503055603119110100281001401521891400038120a03103a5502c1b000354440c0300c0c608145030703c5030b05019000303001d03c2e0b964000d007007844400c000511030a90000790701d5000c0c0b40309290070380c01803200780b1040700e240c643e10340348202075030a2100c048104100d80000501ca454250116152a80e640ca9a8003000c11902c0300c62020580a550304000c50400d9001008858001e0312040e190640c7c9540b20525243c2c6940841c05640f40410780c2c280c9103a01401c0102c443c0c501d244180b102007118010000a0203462149910070712110009108014040c0480280c49400816 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 269129748 1250 269128498 269128501
    0xc0d17162303090a031401091b0f060503060112020a030605100509010311040f33080103110406031104020714011103250207050603130c06090513060509040602091503 73
    0x105810000101d8080100c0202412080700394503034008155821000300810540445286484101500d0b140e815a021a9504c3c0d282140200d411703070000c41340c42009603000007a02454031410711044151a00060100001003081c0115a0b07400040c44490203500d60005a036200307003c205400529081c1e02180d00f06101c0006410b049422802400252500784c80c10300013030243d6400d004952081d402411301c45030403004240b02003d00c0d880c8240b0600080c8500c107440c0ca143c41f0f0300000704035107180240e000400010040c010000d4010301c0c01034446041d1418802607045540d0901c0c510242c0d68a5809180d010403140180404103011404492040c4001c00c002d00d8096980741c507650040302d030700078400d030801050241c0e48102800d000110b240340d0302400129080c0002c00c00c0691001d00b001800035a01c03403030300010170b8048035081c0041013280c0311094640d1a0800703200a0303541c4800c202c4402458444100125110090b099500a03440715005a8611103440003a01e1560944068465402e0110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 269130998 1250 269129748 269129753
    0x1080a0816240b010305161b0b27010212240a0801020406090b0c060c09040605031507081003030c11010302041a0405150304081e0c030703030b09090c0d1716 69
    0x401810114907000107000b00c0c040540150142d410a503007d00b100f008481808240c40c2c03081c5000c101e69191641d015501d003502e9141c01403120819035108800b80f24000e51049045069006125401f40303140c000d504140c5030300c000c41c5840742c0c000c280b640b05c00a903800e1b00c02e4802e003a07508080412b0005081034501d40c0c40c0d01405000703400034082c00b00460780d031201c0400c1c00008001074960850440d4010300c82940c40d00c0c07000b810341d081400b14a4005844240204850ba424450b800600f0019a443c2c06145001a001002042c000c0c1242c0c4241030381e8002407011952000034000403035005550b0420703035100000101d00922442e0302c10007061180711000048210700707600400440d40220f407501c1c2c0781c021040006090748001e46000b01003d40401424241d200e101c4411260040640100b40c03c294034000a0b500b580e200c11401c90001340d584100480741c2c40d1060303103a82c0240034003005108090b503800200ea0398807801c0d480503042450384111040351030703d844100d42c0302d80d07010208800e09250b10b2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 269132248 1250 269130998 269131043
    0x4200a09180b0c1207111009030305270d031113060207080f1507230d060302041b08010506030c04033f08070e0112140405070e01080a0816 61
    0xc241c2211882d03074a03004034049500100a42c2e840344140703002d01d07210b0303110200103031410b05098403c100940511a5004030803d498464a03440f14000d840c0858540303001200590030a50300413039043c1079a011301b500c6030340030000144405107400c24207002482906c0c0030383c0468a40074851160f805007800c8000800d4203580400c0d140126040b8104a5012220181c005603c401e444d0009d42160b01d142c2c000169114404c40f440728141004e0030b0450709000380000c0aa14940c004a200302c0f12a807920401c104506040c890f00b42c00241c00800d800842d008042c1c028030f10507049c45101e108260100102d0b9042c03c0300d000700e5000350307407003001d100602c1d886840e030844038500a41200080e003c0c5a9000030158414000111002d020740d0b1100002c3d81d038000160f445140300381d41e050400c00203501004c10302c14203200f8407403080c8000f00100c1192405161061802e030031a04000e10000d660001007209900c0020010390050340b007100030380c55a00c07060300c40700108528000501400710310801c0c0041c03003c86 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 269133498 1250 269132248 269132291
    0x307060603060626100902010507140d0906030e0309040b0a0801020a0c0303140412080702030d051008010605030f0c04050a0f24050307120b040507081e0705040504200a09 75
    0x36030070300403131254050310303582c0540000c5040314001c1d088a0340c0c42c0030050580d4009144548141412801c1c440e098031801c541140c449420403065120b00300503c41e003a085895140140941c0c50b0030f00c08040c02100064803801000e000c81d02440d284e03140406140c1d2807035189009403003410002c549890000798001d000b59111070b400e402091810500d0080c03070150f0810288216006510150881d440c460708458888004001c00e04500050140086444c150b00405001c0c0700c0d104404901e0a09202034a800c40312140c2c8510310950081042144a140c0030a150712000c00444001643d83e0718a29008058020000f40c2d0066510b0031245054441000e1f00c0d0b03140700c0382000b819214140d20b0300185580c50201e8080caa400068054080300091603504c541e5a22503c83e1050303c0c8c43d26590500b50345032400c1c807100444440760f4251144103044040100100405c0c0c221410b10840c1007a80b01e00c0c08a040b4030341c94440e507503002184080c0640b140700420000713001c4030b0f0003002680000740c95803540010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 269134748 1250 269133498 269133509
    0xc0b0604091e03090501080f0f0a15260a1203090602040302060307080a06140d08130f0b04150f0905010e030a020310020c0f030702010f081305030a030501030b06030a11100203070606030606 83
    0x264940c4c04031346035208248917031103903e8140d9802070f5034503911030740401d2200c020646c4000f251110716004102c50443c41c1080103181c119840d881e2100c40300380c500030010320356410404030380c0103c820314046040e0782c41d0031001202c02e060000d50020a401c0c907501030b128903040a07410800020502140c80c0e44068485e100342445001080801e45940f41c0321020f000c40d00b44140c1c03000004d070700c90300464407440080c2111020700b4170280700760340c4c2c2e0300080d5000c285503402540c01c09000310b070801040322640d176403442a9000d0724145e900304c551807001500140c841d014181c1040f840c0550004991000c04c800b01c2c5a90300201119a422a9050180069070086102c1d0000740603c100410381704800005841009505840307841022502d1017040702c90100091002100c40300c06800000450303000c2c0000d00c40d05145039804540ca604500340041c0ca9403020740701174003a61280054101140b54500c0e440c40044017201c80141d0302da28801c089240d801104d01c060040c0f80383c48400800c120700d03580712804581 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 269135998 1250 269134748 269134757
    0x110106060e131406100c06110c0f16031e0b090609010b030703050705010809100606030504030e0f090a0e0c040f0902030d050301030c0302040510030b160305010f060c0b0604091e03 79
    0x50b41c1c501d901056a0100080740318503000c0d88045502442c00b0403002c0d8400f131203854204c1c4c24074081d0311898141d541c20000d43c0d14007800005c04403045c0a090000034450120306000b05452403034144416901003284c80098a4240e40c1a80020400b4022441c2414150804200141c0d8203100c0c4541d80c485401740c03001c0d191503190100c4031701d09003408141a400c03260400c01074444140741c4001900c03800001002c0044500415004007501d000a21500000c4c0001c3c0d0b400084610740b42c40c000d8107031554130443c4c51141c6030070038041d4034a644a00c8000d170b1160800717001280030310803070140d1490440a409480d512078207100c9140e035a8105980a150658002c0b1300702c0340c0588040c0002c1e11b40344420b00016028421500090008d4103098001d550400320b503007006160950b4076107c19500f0700040d50304140050075000360030303000355240c02294050107048282d441042d28001028003241a419001403a1032071100008689a4896022080309508402c01281c4045203500740812a00d600d1011400324 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 269137248 1250 269135998 269136019
    0x4050d050301181d010219090f0f05060309120304112b060b0a080a0f06050f1308090105190302030603070b04050d060504021906180b090a03110d0813080c040b1f110106060e 76
    0x801010012504880024281c2b1400d18204400e00c00d441c1c2c0001c01c911507910940c00300a410020302c0002750720030350080c40c41d428184490f408200c118840c07440d641c0e07510410852411104c024040d2440d400d550700600004d000c3c28440c012030750b500c45a0f40300301c031180500f00260f4184001c2c03504030682207100d2201000342d45c0d508012003c0d00f000540f80806109090034a040020380d4900c001c0c480110141801030409681c050029040fa001109100001c0d40210500c00c083c08c0400001c0040d1a004040034206800c0c003010071865031140d100500b40030385410105d4255201c000f0010354001420701c4010540752500e40240085076651310703440c22416841c4000801e682c900c02901c01042e0000d26031980c992031512802610000b5940d000e61180750040c440e00040e5180c0000e0500c1c0c800c01e03174816a110303d80000e082c101070110040c075014a04140201a203339441043c91750b13000d900c054050800003980c8404030b40580355103c4140326580380c40c0000c0b0300241c1000046070310001c120b581e01c403070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 269138498 1250 269137248 269137259
    0x100201021b07030c03021309051b010f0e090a0f20090a06081e0a0b0406030c1701060b0708450f090705160602040b0304050d050301181d01021909 64
    0xb20429844041c00c41c1400b00401d00052030094190303076507261104404140300300e00e501c070302d810803c6055000c0315075100180c0400b00c55801c01082544442c090400d04407881074000460380b00740c00100171180305035554207035008450740380c1d00811010106100b141045040c9556900781d540c03088203d07034071410340c1c4100020181e1040c0f00c018880c880300d603002d14403035070b400c440c50810100c0503094000090301c445055000744c64a21075440114012120001d50514000c207400d12001c000030701e8006a4184071041c4540482c070400ca43c2e445504c91050359035400188402c00c4290202e40c010039041001c650383d00705410040e01c421a10403c1401d800d00840503000c1007090051400107440d130002c2c04c2000240344a40100d000d800000b551018642c1c50300306039604c12080741c0c4250001e0301d00d2500413051206104c4100240782c100a011305041d8690350400ea1040704001e0780803100070149442391300180a078040c40e4610404658000003c0d900c89010071460703507820b0300304a4094009101d007000042c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 269139748 1250 269138498 269138503
    0x1050103060e0303130807020105040305011404141b1011070605030402090c0301060807030905010615030203150d080d0b130509010c021b060d090f0b0108101a100305040c0302100201021b 82
    0xc0c80169500d905d4210686c0da444035250440082a81404024080003001c04e4081c0a5801c9526050101c1c807007600d010f04e018190b811130b85070741000e00c1e4844400c07031305140c048007424074038144212010481400c03030b000c0840b0079242c240800003042c05980360010f20940c100c4043c41c0124400c55070f409036590784454140b034034042440b070000003c000d080030800460203a80300340303582401580081080c0d5120700d00880f80b0050a45800d00080d4000104006541402040380c01c50004456140404655454889881c0501883c0903111560f81c6030b802c001c1c1da40c0742d0108150b4925100144501d1a1081600b4000c1c1100c1d0034102c0075000c0c009004002211440010720300d210000c161900b40030008400703900034050381504451191a84c0204004207400e6041e1600824502d40281031135401d980518069410b05245031001d00d0070600902010380d076041c82d8186140c02c91400180a94590904c40002c6901ea0710181d00030400d200c0d864413042d41900204000100445000704803a80744403e683d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 269140998 1250 269139748 269139751
    0xc0f02011103100e06181807090605030319030608010f0209030c0306270712060c09080f0604030503061903030905010315030213020c120a0903030e030a050d03110c030c01050103060e0303 82
    0x1032100107429814005001c00c1020359400c10303400742c880c2c2d0b1454416500040d1b00c80d4180e66030b0708402105130100f0100c0008022000140c4480f2000744285840c010100b5070341c2c09008183c1e038048406d00c4400b10940e11940c05100140b00c1c0d08001c2c412100000c103100025808516042c0c020702403004280001d04001480303601504840440c4501a00070401c0030000f00d18006241e41d540c040c490300000c400c1c28845041c2c40ea0740c002c440c005080559694080c00b0b07103509600c0900907800c0700381404014100400c1084d030003600b50801d079035640e550800154425460031909075003c00420008824140d00046400683d0020f0324108000003025104900c0c05005100081d4000d0510034880096811a00a41220008881203c3c0380c090014410780f500d402440001d0002119071200f003060591000d030203517140005901401418809864040d01c5410b0218030714141501c48801e17604074016501151403600342038042d66102d6110300c034454003810b420320003a030f00b80e401c05503503a01c024400300403603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 269142248 1250 269140998 269141011
    0x1050f1905060906040c0903060f0608070e0103030c080d180f060c020712150b0904060b13020307081305030c0f060f0114010804060b0a1d0610031503030509030a060c0f02011103 78
    0x803c40ca40d2820108405880e5840001013081900c007000400070f5103c2c001e07140040646180482c69606003178149141409607403200e5a000d85400040000c40d4000d04003880c0c454101546a030764070030170801c01b000f070f11816044e54524514803100d01c051007a8200f10220981c41060140084122080200c1e9544064000c100c0e8034480f140700c0ba80000c0e0014081d202c40f0810203c04610505220300044040408440507074040d5190810801b40f032914020000ea1002a0f03c07046085040200d0b006000031001040d0300e044440700e14911044c0b0004205032144000820204c0351814100d0034035030349420742a01c08441641c424400031a0340f45032001d07481030610741a9504140b85d6a035807100f001400c441402d49402c58801c0340b010511100017198030000c0103032108040c40f1402d22505204012180c0b0740d040080504d080d842401400c14001848122509882c01603240c001500029040c0311080c0d2009000a00e0300303121011241e0002a01880f074003240d0000c1000d8000c04c100b8000621084942 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 269143498 1250 269142248 269142259
    0x304060615200f06011502060a020a17040201120f020c07050603010806071404180615030b060328020a0201091401020a020607140705060f060f120703030804031101050f190506 77
    0x600b50000c0103540000c0c1d6502d506012288055004681c0300d0810000380c011139003080d8040d1292145540400c582034000201002c21407420350300500007401c10b984d4440c0c2e0301c26401c010010906580c49039035004d4403040b4034075041010304a11a01e80b00290b112080c02c51060141100008003071900d001030b01e04a480b844054021030340c8501d021101031041c00502030320500c00303010101300d081500103c01d5042d14082c1000030304d10706210110034203450280d034a108050420712014002c4d183c8038180c90700021110110b0010310343c4420680d40c11540c00303030000c007506d1021a4000c00c0950541000403414013444411811484204580c0e00340c2c46041041e00250f070058000c2101c1c20b00c6050314014194841e11118203141155880d40d0030300c0e1007a02d88400b00f1002d0400d0001600d0300c4070907110b60030001c0360306520565161004945600300c6200c042c05001d038100008007414010f00c210848040c005000b0812807a1403581c0344204102601d0500403028070b0f036801a050031851041c1c5001d803c2c003c20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 269144748 1250 269143498 269143517
    0x50609040f02121531120e06130306061d0f0403091203090807140109140a05030a051515030c1011160512060606040306051f0801020304060615 63
    0x21068076889a0110072030304411094a2200c2020042c00407583c80200000d0408050034400100282003001c03d038074110ba0301030a0034080407a80c209444205040d8401c081c40c0e241094080103652584101e881329070008800141002c0c0c41f04800e50080a03288070b400200001529034200c00e0719204d00841c941c0c03081d10800f010840c00900c114032540c1c031034404e181c065092038884581c0a284840c00c0d900301c010550a01080c4500c05c010302c001405448285d00080c0d1100d8440c000030082e016611403844c080e000350703c4981d141d440e04070048000d0304003d0212211131001d0715203180d451b1191001140d0249410b408200881c0764941540c1441e800180248a18290b8408014811044245140034840394030040d01707021106205441c0305507000f001010f003035446c09080c0440348117000c00002c41504800c0c200030f0540e80305015201601e42010002803150342c1d19501d13611480d120310402c030031400401c0001544400540041d40304520451003403103620307502d802d110400320a24040d000896080c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 269145998 1250 269144748 269144753
    0x807030b1f090c022b020d03110409020a08090607050301030b06012d02160e010b04120303060315050406140105060f0a09050405040b160801060f050d0e0610051305060904 75
    0x2803100c00106244028490640e503400b810021a4030b207040343d50158000891412020301c0c0d03500d407403605000320280e01004c040640d000030748072203c0407200d1080c19602c08242c203000e80c01005030340c06059803840031940d07204d01c00005031542900300e4050085103e0040052807051084040c0c904803688460280003603180c400066030340c0d01402391032620341280a288080041a4014202600311702074002e40322501c8210200d5441032440d8000c03040c924400b000411070000c13104102e40840d0921601d41e400101d2a2500310050301d0a540050507154450280c400060b000e0b521680c05035110303803400c003c0d814886074011001442480340582c020000e00044281c0ea01d108000d003d0810710b45850340c40320351120700150445205076001e9580806900401242c0140340c1050681403103142080205d84d813504000514400780e104040c010054007007281ca0001462b83c0280048035545020340b4140d1800c01c002c2c125031021482a24031694219004901c400960700c0344a004090161040509907120b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 269147248 1250 269145998 269146021
    0x50a060302070305090d0804050127030209060607080309010b011214010312050d02071a0601091a0a2001050411040b0303040e041a07051201061b030305190914070807030b 75
    0x4080550a000c1d0402c845a15903489130116215076106907401c41d08d40341050f000403c0000042a00404030640f60015120381200c0341c01c26080b04e504540c80c0f00d003a034030680424218042c411000f00039901c08030a1240e181019041000982000e988441014001d4001c51040c3d6406030203d01c15508484014808516055803d032002420760601038604926080030340c0899000c50700503618480b02d1800c8000001d18100c0054000000f40390004000781032030301d800041c05c84d00d02402100704002a003040c405015005000d400300039480440d84440001a0b8180a0002250300320341116480c0c060900e18542403080520141d800f030b0055080070b08041c3c411060700005402940c6000041a0b400f04004c0c0c1503201d64455030140d52200d03254100049481d90015068001d4000d124800785402d00c0d5194250300782c02c507560140783c042445d0b00c403840b000c034602c2034081d140c00880b8100b030b50820511181ca1241014000d814044a40f1070b6600c0721100d4031403040f800b00804100d0518007046904049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 269148498 1250 269147248 269147257
    0x1050f0106120e0f120711010c08030106030e10060e1801020f09121c0c0606050906060f07110406120213020a0f11010204081905010b0102010912050a090e0c0c070f050a060302 77
    0x8a021030310b04074136180d01503144c0201451031003481c4d200050500c041001d41c0c803415a8207a002c0c200b0314003800195441c05040e01050103120101030341c45d1403c0b00001c8003006040d5440141d050101302940d250003902904104c1100c0215040100c1c0803c00d0880005108480075880ca43d5885810b0080500822000c5c807086803002e110347c401c400c03c06070502640a40c0d500201010f448104401c1107625002040d514254003044c811b0800703004001054445408850640d190501d0060307481d0028500502c1114080c16040d410619001c00451642a070f0030783e03100032500803104203040c1d1a80101c980164460301c10600009034440300c0c2170a0950207235150900070100440098281a02e80203140c0c03a2504543e0260702211000301c0420502000b071140d1400a0000e01c0240220010f40d201c003500c000d0024000400c00c4000113002c1c4140f4421002c141c0900a403817500302081c204a00c079040d498000c5402c046182c01080400900b2a100701d0401003160000340001d9201c52a054040c1c009400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 269149748 1250 269148498 269148521
    0x10e1303021c05071b1502120d020304150608010f0b0603090a03050304050a150b0a06050306010f18030506130204051e01031b09050405070303020f010b0901090507021212070201050f010612 83
    0x91080c4800601902d450441c8171200180070b15000d440d03e44034010310010402c0030300540d00710001c25045c400c028000c907012288000c0001d40e0302e407220318100c0701060541403d00e403070501c4c01801180e003403810340200340180d80049052110341402e1080041611040e2000b030265880000701c400000d00034000b541d4800d0150041e1400005261a05c000030103400392881c224a58800041003246865003041005e010a4900036095241103070002c0c010400418900c024060010300003090040e16078114009035521100f645e040e402d007920110001101382c40e040303200c0c07820400000c518400c18460003105601c5003402140c03513441c0d81c072848169001440154050550a203010440907003e002d507038042c41c4618018146245582402400d0140711a50540c8503410456000551b6481ca840c8030b0544015003000120780e01ea01005034070b4041b4001704200e00800100e4000014020180ea4500c035510b035400910047d5078440e03000c50110024012440440c071010890920072940f43e01034903d256 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 269150998 1250 269149748 269149757
    0x1020d260a110703030605090c0301031a04080d020f04031703040b070c1b0e0402040e1b0103020c0709110304060b0901060f0806010e0a0b0c010e0a0302030f0c010b0d0605010e1303021c 81
    0xb509006480c550303501010064000ca504c0b00001c110504195141540c003144c0702e05214259410b603600c8464000c10101c0400d03000008201180c240b082060441d203190308113186c215518082074107242c80d6900544000c0d034021506912a001c481103400803203104a82c0720a00d480240d550000664280d201c41d00d050300e00f0b0300900a030b11440c180184104000d04180c410302d44a2f40f03454410401522000b05a00300c00750005000148204241002491158404d08000d81c985003d070031080e03c3c0c9049a8055040c0f241020000782c41e00504000842c06940501c1040c408000008123001c400c600070305c2074000040511400203000d500c01c201031600924140b50107806032181e04d00003001803801c0c1e00044605480050840c0c0441c0007442007a80204100000e0544400c0c140c81c00f135102e015480d8240f944500000380141050020741c00700c172200300c00074040b05403110381d0700703200e00240000d0180041c90102c140114182e803501411014101d40e06074010500e0084440c0140c6024081414100600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 269152248 1250 269150998 269151011
    0xd0315090209181b030f040516030b06060d0f02031501090b0a090306240902030702010c020703020a090c200c042f090a050904050319080112060b1c030306030201020d260a 75
    0xd8007080c4c0118002c000c01e003202001800c2500700390342041e0003441c4044007811106410000550140d01060344800308a802c2611f59403443c0d4810003903c1180210000d0a100000b00181c405010345070400400085c0da4100c10701e03031100c1f801c825030710407092003002159038080d00b0000501960440c10002e074172406070000074500201c0c0c3d851816101e42100341c14503004020000314642c24425040652402e20040203414515001300300a0340d1103005822405403a003055100d540e000e108040e4480c003c003a180000540c3c107911094440740001516480780b81050030a405002d45409450301217021001d1152503c4440b9461aa49910614a0b0341d00224400d000003007a6484a0100381b2a9000380050b685e11034100140c003c01486c000c00c89000d00c8242c00041c00010a2044d4040746154070a0000819400280002d100305480411150b41503803c0c42004041641c15001041124400e070202c41340c4a901180c1030300c0d40030300904444014504038800409060054403104c0d003084c1c4020001588 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 269153498 1250 269152248 269152291
    0x13020405060a080703051608040b06010225180e0c040e07090903080a0501060f02120702030703140d030e03030c0906070f02041b080906070815010e030d031509020918 73
    0x11500310310b40031000301d200e020800c000603400d809440c4e44882000b080911582050350050035192010b00050b03e070461460000d03203241d00030010304001042c050381440003030354180e0024200c2d41c3c032401840400760354003400682206140c0201000103200c203002d441444120400c2c000102134000090247e071041000000b1142442c0c85a030409500a940d5440107180903100035040d2001a032010b010891a1032080e210981d010601403802c3c280d500351540c0e645214000280780010640020f0000846503511403400c4800290301480030589440070300c0158100301c451034a0740012958184520010804c0000b1494490020014a4410030070003003407140a0700803a00311080111100c6003a02070780c104d115480e4000c54041c0c0e2140103d40106818900848000c007004400340005c01188518408440103038001c14003074180800240813107420514250005001d0000c00d880c900706001303c81e0001c1000b46050003107440601000e04102c0281c0f200741520207071301e003006140080c15451903003003080c0e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269154748 1250 269153498 269153509
    0xb03010506013203100f0b030402150c0a02130207060b010305010305030405011809020c0a0c0e0402010c0b0702010f140105120303010e070f09031b14041e050c07051c020c01050c060613020405 84
    0x10114601c901c94402c0c108070050f110441c06e50030021410314280200001039841140b4038a0030414001641d4031070074003800c260300e00300940b00001d42c082032210016100c2c0d034070390303000d03102c20340c0502030900c40c5461607401542154001e00014001e0340042006002c5540140318998a8101c142d15641d06107a9a088000c01c9800c2001784256541001103400203102d40d40c40070001034020780307004074481e0a140d40081c00e12024504014060680400054a100c1c000e41c003140604510318000e205011b1030401c403440d60708003401020307c10040c40c40810b40c0e00703000009690688000c0c6001112a84030340c00c003a50102c0d4002d501d102084080b040100c0080e0701d01704045807d4521816a212007401c15010704505181103d42c1c0703000c3c0346801e10700e007061820404404007003d014980020213444681240c5e505100f40440130301548200c8001d415905490070700e01c02c0706c003007a42c01d0725a0b4520341c000445040c0704040803407120b54000008604607240251307002d0104070f8052801481c0c2943c62000c00e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 269155998 1250 269154748 269154751
    0x506220308040603060605030903090d0606150c0b010f120602030405011508070e180318040b1c0b0c0a050a1419020f0f010e0a0b22080705010b03010506013203 70
    0x11501c0740042401c000c030316014040c08001e0196401c00070700b50b1078013054441d92030181444880c85110060090340900a05030710a001524400d040c07261124004800588401c4407424100d903401f040b5000040c0c145030b0665000107580d8550300300c01c0d84288079100e120203904054003c1d5025545e55208020314030058281400501c240c001805845103809080301e6940380c02407100101c801403544c42d0301d14620100850b540b0300442d0000c580300001c00310109008000d55800035801012400781101724800b41c056402040d4800d1801c050b00d683cbd41c2690141c3c6024807448440499800d002100da0240500c00b0491414840d0301c025086c142c20414126410042030171120241c1c0181390742c1c100c0e080d0203004030b60040854074001c1c00800700008200e03580d027a00e000003801103030b003110109030451025060302e4148002c800c00c0317150705c040c075051102040d8007071081144c1030f620b01003c2c511a410103025140c80b40d48143c4403018000c0030040300304040307891102041c5105143c0c0042d502029075440145 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 269157248 1250 269155998 269156003
    0x90d0308070e01032c12030c0c010605060406050301031202010905030a0804050c01020c01200c060c0c090f0103050c0103021c060905101712090a2309060d0201020705062203 76
    0x1010903052850703025001400481c10b950401d420820542c0206000e0820700078000b07410800d4031986010624007a0801d000c81c10210035644000062260000da80703000751901d17050090003000002c0d0350b4400c01c4014031030b41c411080414400d100400100b1302603a8031240c1c5400600011840740ca241c1ea0b0b84e4259031158a0410101784a5001e01c0709126040184845400003800106444021074001070701c89a0300148030b11314000e82003400351718504180460100c01c80060003ca07295604801415141c95005410798003410501d000100806a4039060b54100c80d0400c014003030713158030580114085e601c0118060078291800e280b0010309100f510504000f03180501e40080c013400d1865644d01e8141c2654000513554500740709200c1842e90100e07004160003c503440c0c1682ea5107101c0082001b0240c1d591007004280c000d5100706d440080f0303548440780a444122aa0030090380c1e95000c0140c811828000a1300507400107005100c83e040c40d5000307104111500000c11885210000c0b40034203510150000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 269158498 1250 269157248 269157257
    0x61302070305040f0902070b010803120a050a1401091a010f0e0906010507020618010305060312091912030201020d3804020c0106060c0b0a060e0f040201050f22080304060903110303090d03 82
    0xc1f10103026804000502500c0810091894804003000742a4125001f41141c101250790b00d0124400410590000604201c94092034650f90303582c41a040c028114141c00c0d00700d80780f0402e0446c21039841200e02d51006111903c0f4081003d041e00140040e455004150a0601204000d10350141ea00c40c0064034490003200c480316200210280010240e62024000720300075440380d01d03009402d401800594a01079400e54060041448c40c07071117200034507100e510942d4102080030707001090690640003000f0454000d603062080ca05041820080d11541401d04038031186981550912106503040000d88154024000f5013055122032065084030b03155440072000c00c10600340c21040007512190594010450401042030900c6c1503101140d40200408404041064000143c110780c05981501d1001140c2c42c846511691070440762084003d03129041c20341280d4640000a0341013001003140c013031300c000d5981c00001034919500c7c13241005030308914503452b0000b40410034141c3c8500300303c480054040e544 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 269159748 1250 269158498 269158507
    0x60e0402090112260903070b090a030b0c0f03040507090c0c02060a081f1806290309160905060f0907210b09132604060e0102010212090309120105061302070305040f0902 74
    0x10103203047c03507980c0000a4014280015241580c80c8102c4000726500945800c2040d0b449000d01100c900c180094449094000720a020030711070001008415a141410b04004104960b0f0b820b8410034681c0c0c00c003d50041d420440e0b10043c80c82442415005076020200c8140300800c2c07096102190104c0d0400070140002141e25a06040720b4000c0d8402000c01d2201042c05803e00a011003007181080c82101548500002044011400b006800c15016200e2081e00505882c1c03c41c21000d000299444c03407003a40a1030350034041f1302e032800b1124000c04407910b4020001c1c3e03010f00203c0700c034940030065000f50380c0c1d02c0b010681a030700c1d401c0e0040d100c1d103100482c1070502001464826060b01c81c04054840d40d01c6103002100e10195000f04440548510703040000c403411000c00100c3c06803240545401f6411003070b00920054400010141007030f90342c01c549250010304c0c4150580d0885100f01e80d1180d003d8040d201c00e0614403002c4c4d00500c4000c2c00703031400e0362820b500c3d56410048520a0352208080307a90004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 269160998 1250 269159748 269159767
    0x2030f0105100f150c0f0b0907090c020102030601080103060b061c050a0c09080619020d020a0305061c05070b0f070c08030403021c05100f0e100f060e040209011226 72
    0x3401c0c42e01800f0890f50303440c040350070040703001c00507a21041140140422240c18405002540850010309680000100f040e451300a1000d83c0f21083c030301ca007040ca94180308003184c03554010b0096038070454040e07440100580c03942c2c450601038007041c0340440d0810020001e50310000c150400d40c40741003070325180118041c1408550380b030845008140300b0003000034103075080c00300480c082880f5802c80074100a1641e504400e014101c002d100380c0d00b02c1d1656910010314504400e8154004502c41c600403603c1c40d0f40908031025080c1c8501244600805a40007003609101c081c040401502307000415658890400e0030030317030380c41d0341c100940d80011920747c0c4003007020021481c0c0b031080780c84070080005040c19001915550301c0d969540309441c045100751a10400d2100c04040d920240a0241c46000c840c040d104501800c8014411884000485070410300e012031540c540240c01c0340140d0307015041403010380c0f801c0c3d20114130802c144400c41e2035000c01ca59a004180c0b69101d40b80d000d2403400d6220766281c5500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 269162248 1250 269160998 269161021
    0xf0203091501050303030403120626010510080307200a0f0e1605090108070e03030339040b07060b0306071e0e10030b0d020901060302041d01181802030f0105 69
    0x16401e4050910394100600c000c1c2c50200541e40c0040d41030070314200004c840b40100002d45126000190003280a140c048241c0c0c80d00c03240c0311641d12001000300240d440b4000007500100c5a8055058150700400030680010034240d00000040901d46e400d0400400d041e002540c0381c085640016000e0040000c203200d284400448160044040d80e400c15141800c1940a0501e01580c01d0303140c14040c4c1d034800510b0407406103210081d08030004080e250389180188100b09868500b8031011030100b480c0000500031000e11030025401c10812400c136042610b0700c40c4408403540711020488886031036504140b41ca0f2400c010140c010072060702d0345092812070000d035441c8100414002c07410400c03041451007603610303604130114441d80c0919001c074000921030080b6150345410360000b50400121400000c3c03481d0b00da8041d00580b50303080c1a851803898080f01440007541d0a014030400031006c00c0040004641c10740c0800b158004002d180c1c628004a0340010782080c4c04c0c6184445103035160001c002c10004407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 269163498 1250 269162248 269162263
    0x70306020d05101e2105010f0507090501090e06220504030302180105030709170a0804120512040e0601080a0e01020c16080708100e0708060702100b0d02061204020406090f020309 78
    0xc00384100c4064138015151100f2400901c2442c0711103000500e40780c20b182561121880c59508000288100b88000c00100001c040480315000000c2402e0320110f2650b1180c03c8043c102d480c020754498032620340c0002c114075800b40f05003180890700b02d03200011500310f8a00920f48114001c1e100141c640305050320340021011310020302410400c082082040054108020780e05481c841081c101d000345611840c5450705030660303800307841c180e80420001171078404905074404041c0b040094940e140c0204690030384c50b00450142d030100030319040009085500c50403a29602155241000c510300d10b80070f42407800c80c1c2c00401d0081d030b160042d826100c140c8004401c081700400c0304400a0107080e141109071601c03603207820b00c0c80c0f0b40c9a444004100210804001c00c101901c40315003030303500c1c60400500283d070b00d8010110076000e9500305500480145000b0040c809402e8000d05400d01c0d1507602c11a50714440c00044c0100d070311070342e500790108142d00d0501c250321450100e858010b81e40d0a040082c40d141800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 269164748 1250 269163498 269163509
    0x308030601031802060304060504020f190f081617031e1e0910110703060e030d05150d060e1c110c03061519050d0305030f070c1112070306020d0510 65
    0x10f05035071610044c2c8642c01200d50040d004000003450b0b807554400900c0001c10303032a0703565000b46564005020407500045801c100d5000c000134548695554184580b0b40019511110792031401542c10084103082c010032194030520034040c1c130b280c0020000d044000500c4651681c07029440400c0408298031240300050708002201c2d08982800c07040400100e00c015145620420028607009100d00214108240400b17541d004406002613903100305003c6d582d800003a40a48140e007000085415040d01118000500c0ba0140883c010070183d07440c1c0740c01400e0020f4030b1741414404d207034406041aa41c0c9440340a00740803550f801d00100030717105810f41b5041030340c90040e20a41007801807003400125160306c614151000c2e02e01c51000700418241003140303103131907000d40d4010540c0c2e04038900305507000b401940324104040c0c030030600761111182140d428003070703a1009003044600c1c081d0130f400b4505118414a0f07481003d0880301c0e4192a0380e114001d0743c000c0c081c04004144c03250240200782c00c0ac1c807580400ba25 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 269165998 1250 269164748 269164781
    0x708090114071407050105040f0506070302071109250e040e07080604031b0b0a0f061e0b0309010e121801050a09050d0606230f06161713030803060103 66
    0x4403114809400000a0002d205109a84040c8107041c0e4440b0199001140c0020080003980340900f1700c05030300000b40304222100d001392400102c100703001e031003030341c103196040002140140010310034040743d6000541840040d03001d11006400e075040201c0c41c021a090280d40311a00d14143c54280f2040c2d030210420065a070308005024001d0000014856901c40c1c0c0610b054486c0303c000b43c8016000d994000005030100c1140020010404e10580018250841070350741049907540d980e500c0300d18585008041102003081c003004001c81c0f031481000c0d42d04001c0c4000002a5142d091214500e0074121000c21358100001041c0802c2070300c45420317044080482800e049240072041c02000301030001c2406264401e41b04545440e050008540c44031001d0400c242140380c0700110b44a24140042d050680540320b5140c50301e6882c610700309107082d100c03030380c50050341c0d0320322681c490790745a00344480d2200e00308915505100303440c5084030400c0d0050066001c0c401950b81d904020000500303842500710141200c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 269167248 1250 269165998 269166011
    0x40e01141014040b010908030a020304051f1718070620030f16060906180c0501020c031e0c0316030c08060412180b1c1802060306010f1e050307080901 66
    0x10b40340d900c960002c40c10803200010300c040d0660040c2c505d820f268000044a1001181c0c0d4000c958001000b0001d40d030085500b12050851402012291418044c140c00002c01d0325600100200c450307000726420a41400224091109481259140030842d912020000c0c0d82c035040e034180303590031034800d29400d0b1040025501d0030f6841c07413130400d030313485800c0c5448601030540406105114403613020010a40d840710003030110b55201403c07a0891900210290380f94458400006400d41c000200c00701c030400701a000c5d0040c07140c010b60390210b607100ca040541440c00341e1240310344156014849903910104005001a9080c01c3d41008110044580c01a60203540050140800704003034030b901ca01508bc142c5480c1c44040220380f0004c0c010306255001c0040c140e0b0118040704801200e150302260120100410410b6038042012034072100c5500b00c001c0d4001800700049040c9520544c135109940003d420141e4104035180c4034440c941584810002c0001d001000380500c2951003040d45400a05d0b41009000d80c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 269168498 1250 269167248 269167259
    0x11030d02091503040c0e0a0906020a08090c0f010f110a0f1416030c03080a05190504050f010302120a150e07030603060e21030714040b0405280509070c02040e011410 72
    0x45c0a4042d034100102a0000030b036441c0d5803504000b02e2650302440940d1102918480030708001c1e0159800403282c02810f0505c20503003132072403c0ca1441300e0140d45000c0b4900c249002514400150101200c03140100400c460110f0040800b0000702c074030550559001080c2c0c00d056030f081c5110a0301c0d4180034071852404101040200d680101030320740010481756a50716841c3c0c195880e100e016426294018103840040c00d958000c03014008890095803800b41c62512040110301b203100307243c0d050102103610408612440340b29480f4448120a007500121000d44a40305032034500411601d140029403200410310130071099024080c9005408001041d90340c17048211840c851902950a10310a0000310002d404e03240320740307071506009071103400d000d94860b1100c0c0e004840b58040c3c000c10b801100d14a84001080014a076004400c0741807104401296003400100b000038000503002100300079150280d000036940e0342c89032410009219000040f01c40000c1d0041c00c82c0d20b0000c044400c40740441d01c0401c103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 269169748 1250 269168498 269168513
    0x30b0c0705030712030b10020f060702120301181808030115050405060a082809050d02030c1b0102010b12010b01020606040b1003090807061401091503020a051011030d0209150304 78
    0x1a8144c2c00110b1841403103003000100c000340890721400e6404428041c05a1203240c0201c0c50540e4a44040d05540640d66040d006a84e1024050b01d1600300d001c08000411050300e100f00e4142004010400c04543c1130a1000c0340c2c00c0740010008140d071034000c00401089070080d00510060004101c3c18542c0c01c082c40d01c400920a401601703100b40c14082d40c8000940d0304041403120003c40c641908008918100140c400d10080914100454281c4248561701103264000400d0301c0c105030400005081e8020039011442c1d10480e4601e40c0b0b810b5649400c05045180e85103201c458401600c08000202ea04a80000900e49440581040c1c0a2071501c1140d02c119200c426040500219905012031101980d1a148005209191010b0803286c5489081c1c0003910104070114100c0e00a02c400707005e0000342000003100400030384070081d4400103442e4204aa4102090305007651000d0342040c111000705050120708580c0104010813407a42d000964001030300c1c1006640328014038008003581149000c0d07455a2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 269170998 1250 269169748 269169757
    0x70e01150e0f15070203070f08010b1c0f1511210a0b010e1e0907020102130b0903060a05070c02130203010f0e090d050c0a1a06010e0409051b01090b03040c030b0c070503 74
    0xa420b0389000072441d06641b410015000204034210705c03004c0c16581c1e4041d4900910303003451054440ca4090020381000200030032155500c1d50000040b1300c030aa450350f0790310f050f074801c109404100b41e25010080c0358030b91500090038081404001c10381d64100091112040b001c00100000c4100b49042207490069920921540c2c000b00103039072020425419a18420520304150380096010444e40b040040350381d0b041d0080c0410248000c1c4003a06103032191800c9015029080d103c80d0150b029000042c09207031550070a98210fa4203082415025516801080d00c02d2038040383c680400307030000010401c0840848000000300640d1582d8400c60815880385078980c0c83d04600e09081000218002020150520014440540c002181c0810b507403005000c04c80104106e4089011642088070346200c2d080a010b054001a40403000c3c1924000c403100020b0b01c500f9200d0031030b041003d030320310208103090700780021400380b40114040502c0a18501c0e007600305510007403151440d041c3c14800725001440004c29078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 269172248 1250 269170998 269171029
    0xe0702010e121b0109062c0d0c021f020f250909030e0d0506090d08040302060f04050c180a0b0d1a0a0212010b0904050a021e0903070e01150e0f 63
    0x583e40d8408003400804441ca820410510951914504804120455002e80c03a4003046d5010349661502c15610035241191030009081140c11803101051403910803052210814801007400e00c40600320f0206c2030b10b0005012004000d40d000c507059005c0d161080101070000310100017000c0c000303032070071045d000c2030340c285d106803606075803120710313200816001c0c2c0c05020b282e0380040c01e03450940d403550900c0341c3c2ea0603094940700c600e40a50403200c0080e40c422405a8030441c0c05400914064448064007000d143c40200103494a0141200000b12540c0728903444141055025898280d800e003400418221140959101d1040700c1000c020f10002d02003041c00d110708000c5201c0848181d6075404c0c540e000c0e00c0f4014408003030700e03240c0002061751905040500b44440c1c007550104403a640b5661020200d2140c00084071082200260703103204c1c032007880001c00c080d00d80034041c0c41205584aa1201928200384c02001c60700d80444041309040394015003a10403042c1c02c0f82d1251902c1103400200d00001d4010a06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 269173498 1250 269172248 269172283
    0xe1209090c09030f10050601020307030c021309051920030706111903090905130c0b0702030f0a0309060212040609120204090f060510051206072a08040e0702010e 71
    0x502865100d01920b5540201074140d54200d0301c0383c643d03c2e4841c0c031110124880c15203041c0200f10b00b54800000d5460b8141c7c142c403a81d5541f0f0b107a07020444908104514030f800d80c0d23100c9150400040c01400824500c01046d02400051403641c50012740d100061050f0003c1c115900c200001e907603800240c010220f620604019283e440030515581c10065011a0f400002d1190381c030079000c2560145400003242e84042c0c080243e911980c8505c516014030850152680f100c07044240801c4020340000c14000344000d04440500c0c0b100400139003070564442040d070205803146420003e00e6014400104070400700b80850b480e02d4103100c8003800154107070043c4002c400c912410f940464496500148440740c000036081900449403502c100a000b048600c040d803814180c00003d4a8280003010700140c0a060300a0300050343c1d0200115510700d40140728010461a10700010501744544403031904680c02040c42c560703100c6c1461b4256105090141c40541107a140160341a91038801203006042292880ca1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 269174748 1250 269173498 269173501
    0x21150b010212040e1603051509090a020d2603160f121a010f0c02150a0e0a0b0d0b010804050c0d0c171b04060612020c1914010e120909 59
    0x40b8900020680500126040081c2c0800d2900290507264400c003010349001d031100c081128102c0030741c0c5040d074902d0031031044009081418179185080c07a601081a4045401800703c9400003031023203031440340076540d03203040080300c0243c54056000311032034001c00c1c24000d01d1414000e03424018403644040c6c0030100300200308025049032141c681043e003a4500e0f8002d001b2050702002000c01c0038010201c0c1404150080e84881d01c0700c0c05041100d0031681c0081c07029020090b1050344011951141c4034040421190fa10302d00d04503500c002002e0081c0010034615034491040703554801c2200d0300050030505000958003004000394000800c01040701c010381c2d0b04440f60505d4540145004c00e0f0360002c10b103c1c0c6000c1c9400124080028080a2600c0c0c4501c0103d40d0800c24414030040b1030181c002c03140004e421002001c035031101d0360000c00a8801038822103400310b000c0c0f038a80803960a60302003140c08a001401f1100c2c1c0e0b01c803d00a9078a550030f4440501000304d60030321858079500c41c603520700d40135048a50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 269175998 1250 269174748 269174771
    0x13180602180607080c011409151816030c060c0b041101020a0b01090c12020a08130f0210030504021831050d0e090708060d060f242115 59
    0x74000d1100d0240a010180c84002038503014506801000741a1001d610340b443d0740060610743c840b1903010b0b00700c41010342001018121111584003004100d0041e411811140c060040000c00044d0500c41d02e00b11045507482c250329081d00c0c850926441001004019804413010175000705407903400a50207171000c030785000c42c400141e003054883c2c1c8014100400103000004c082e600c9400840843e90b0565401c48590554101d65080780500c21240c40001c14050004e088170800c00120402d15009a80030058100e20b0341c0096800c1500d1400040026205c5082c0000c42c104500c50100008828444e00040d10b01295401d62804041e0260000030081035103030000c940c040e455000b00d164002054034018451604040c0019141d03070b4465010f0308450002502c100e01c02c0e00b20500540000f020100c24415944403400036002e81c03545070000782d5803071091a0b90709021301000900245400240d5541c5c7c0d150101541c00c0c01c680103103503000380d12281c0c6000c0010b041c0c0c401801d04001051400500e501000307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 269177248 1250 269175998 269176027
    0x50703020c12030306030c0102030f2a0318091e04060f110c15060102030c0c0d020a09020d050a06050604050f040f140a0e100c020d0c030e060403030e13180602 70
    0x1038540982040d200c0003400600b41c4044001e6200342c000b601161020030017003004a99900c160748a03c004000140a006980c3c00b1445040c1c600040d06221540c2220f0303444007890071079000b80340d1000781480840c8050081d060040040e40e00c40070705040341440010318009605240801040101915543d0400304607030180741d80030140d010041e4151503101c04450001c1035490a114009000ba042d2680016030f440d840003040f10000ca51103809440034078005024031040c42000501241e001c4071500c030100d04a190362005d081c00800c2590081100d09007102820205c920b150485401414104000d02003601c1e03451116000b80700591740011b05410300c0081400810201110b040040c0c04442881041c44c456000040301c0700f84a0241ca0502100c031907000125000c82011801580020082d0308040d80a40074081c42c0e40d00a040001a41000c5d4000407442d600c6070300210045000c0301c00440b0603040c14000700c1c030a00d0316030404100c400803400e007101c0341c00d0041030014100c43d0001042070f21100c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 269178498 1250 269177248 269177263
    0xb0a030302031b16090b04060f081f1407030510060206011a070204151e09140c0304020a05041e0e0106060903021012050414010f0b010503060d060603050304061806050901050a05070302 81
    0x316811404099100c40400011b0000400c485101e582880400304400c400718211008486141c002807a10440746101840d40300414203903004c1c0b5581d03d20480200b8101090001d2040d801da5900198a2030411801c40f58009142c10601c11540104014011401182080081c00c00d001c1c039203d403281d501d44001005008804460318582c061078200007034001ca041031007482c50551006081c0117503200e15005044960380701420b00c120b642540400c850500c200000c41e0410b00240100500a4039540481c060b01c50101941043c4a540074410541c0c0ca4036100700c480111803d0000c1c001249065030040010f15a408080d224903580e40310449101d000d203880e2098100b068105010700d103421f0034400001c191003085d14083d9400d0844c0d8820a0080e032144481180d8140c45d4242540c46a009000607200040001c94005507035440110100710100040c000520156442c0b50303c0301110480c41c80e9a030519806a0b00b4000240000c580070f0f0703008001d650745004603180054a0307880501b0100d242ca0300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 269179748 1250 269178498 269178523
    0x91a1201061a070803070305041b0e011e230a080f0c0a0503030a08070e060c06010e100e040c05040504110607060905190c03110303070b1501030b0a030302031b 70
    0x400005011080040d04044200c1d02945034001c02c00b40d12010319a0107204400004142c280c0800000d100300e0f0090b0701231a0840d02440030380c0041003000c92855030140b41e5230410100030901e03030010018101c100003800305c5254a600c0b21094148dc0c45407030700a0140048103002061111403d505560b00d40c407140100801c1320f0000c440e42c58080c080b103142c039900184041c0f4000c170030040b80400e90b410700000f1986101e40c55035441c5115555000c00310740e010b400c1103509070310540400c00410000c80421040340600a00220b80100c1d0508030f1407800040f440c0d62008a04103964410440400d814143c402e04903001507a001c600e03581c0f1440c03c02144d003590f10180754020808034801c01409141c1e4019101c45200d10120703a4100c8100c480c160f0a103041c810028000114180b00f88000381c02c0402c0300740d1001c1c010341124280120b9940d1030000314022640200c02c00c005041a54140d0303030601500203e2081a2101d403501402c50314000d4480c49150f08071011803c2800c07144185540800001e090b170340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269180998 1250 269179748 269179759
    0x1412070c080d06030210090602060f070912050705180112060207030e04110d05010e012d030c1206140106050d0903141b060603030c0d14130f0627091a 66
    0xa8000b22920010b05550100b80e01540b40c505000410034019211001038440b10b800600741c6079294001a501c403e030003031030201081050000042c42c6404c1003111881907114402900c1c0d001e05203814410074101300340c50345c02e03511164001048110704402d40c01c0c031041d800c10005139540006060580ba00010740181641180c504050613034102c0c0c20070081c000140c181d241c11700050340d880300410000b20085c000d0034940207144411091852400c48114540c120141c95060303015544d40721407510140a900545820590785ca075002081690f224003d210841075800b1a169414108010401c0c080e6a0000803010755405a00082c1801610f154188072403c10583d40d03140d440065450300d46064031400902071040c20040fa12900e40442a61101d10840c801072402401425044a4184c89811601d8280d94108038101e581302c001180280580701c40e20094495134642a0000c08983c0010040f4098200429288400c0d2088041c1c5001300d0304c1003803000ca10034035580e40303000c2c0003042c00ba14942d07c074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269182248 1250 269180998 269181007
    0x110607031e080402040e0a050c0f0307030b070203090a09020f0f03060301020c06090f07060804082b0509010b1005120408090103180528030f120605060a0206090c011412070c08 77
    0x1990700c00741d11403059109607010b104c1b11142c01541c541c0d40e0001600100680c00c1410a82c1e49420580303c4101e62541c000c00302d40c00e090b03480d100c500c4071803001e036203140041c0c01c0092100c40b141040040b0000401c0740342d00440c60304990f80910103080c000c202d141c0039a202c0000100300180e90035015207034105031a038181e84441c2811000d00b036480d07625450100607402212800500d82e4041d003401e03482260400c4003545882c1d02c4d01ca4004601c00c0e58860200320326115040c0c9003081e4854401c03240b28080100000440400f86800c00103078141c00451101000000c0207600c0402d13219001050304154410750a41d1103004c214016030260484101c4256803905000188050040c00503a1032030040d03030441110700d04881824071080c5d400411388080c022400c88950300d805c0c0e91007041c00be5001112410009040c2c0d4882000540b65845141b4450043e0b00a03018040500f070207010350710144900b401d02d6401405444460583e0b8081c0d0900c20803c0000c10340013961150288520030301a95020059503500d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269183498 1250 269182248 269182307
    0x7171015050d021305040f110f07051603050d14030601051803010e010911090f0106020a14190501091a0112031d06040f0f150801050405040c0308130503011811060703 73
    0x13014400d104541c0305506015010921180340d00c164000400e011225074980b03c061340114849074040c0307000710340da44a402c00300c0080004031426200030b184504007900c060360300f583c0c0007031040440c052000100003042092010a81e0884100c5003641d035903a20807020414032800190045c82c03c1030340b280703495003040da41108101d08145032081c0e100c0d048808922940b03810749040e6102e61300b4022100540d1092a000c1e000c038401c0002c2c0b10410840d10201c81c102542450b1100d650b005001c8201c4690b0b44030034416042000316104061500e00407014040d0303c1d854641032100800d0598000307010b1000b00c190b030780003640c88c00c101e04094a5001c0d00e110f40d1280c1d01c0d0350400b440045441514628607561b1000726100200715520303031514442e940c508165034244001c101c01040080c00803500c107461107400000050b035490281c443c896424071102002843c20082c5404d6590904e17480c140035000c10707214000104150000000070710183c4002c0d44a0f001440c007698080b00342004200324002d111000d021 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269184748 1250 269183498 269183527
    0x902030106020a0302070b04060e0603040606050a090507020d0c0c060302070809100c0209090106030213110c01050f07030b0a081b060c01020423010806030c0103180f0b07171015050d02 81
    0x40b054485d40c00c03250000d81d030b0071690540d0b009030300a030030010b201e802c4401860314080001d15001400f42d000042d0782c07035030380d0000750420780103a02000c802a1140c082044094040c40400300710085800c11100045842e640d52100c54051301500081c980e0120740c0a040c001040f094540244018000b003c00f042c1d00c8802405021004800301c1c4501c030300000140200c0f07818003400003182c0d80600007804001e42104001d000e045c0ca070a4ac0d1048080511035100c0d410002d001d0f41c0d000f0304e02c010140302d803402d013014010b0541d54105c1106020b50503420080044d4440011a42c136100c44075002c441c940417034031001800701c0c41884101c000e03644c00441e010441c1d40121070f60104c2d00901d1030001d11503800e6907005660600d41204c0c02ea5040e041012240c0c8554007030740140b0044150424015052201d907558240c1906100000342e421210300c404220784145c000c3c08071111038004000d0a01103140c00401c11451a109000e007840c1d03c90aa848050340034000c0342a5203403013005003015900c03403400a554a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269185998 1250 269184748 269184763
    0xd030c03110742090b0a0c050a0f050c060703051b0703020d0c2303030913061d040519051e19030503161407060207140f06090d0302090a0e10090203010602 68
    0xc42c907540b1001d1040f5600c5407529120b40b1aa81920788140755490300300e55a09580040d800e0400380034080c0a8040003c1e001d0101c2c0346070070310420161625a6181c10f20501d01904c04980d1400703903504214007804207402c40300340c0300c050f0100d20300d80b8400044500072604060741a800250030a01000c131a03410803d1101e200010ba54409903000d8640c500844500c4400058840158058004100d5031052382441c610082960000900128078182e0755400e4035604e249004103044600003550031301040000c01e00ca030615040d480d0480a4000844d52980ca403034601034100d4004a251036501404241000d002420344240d07030401e1607206a8033428041c1480d841141c03060100c0400399641841217014a0107a12141c0b80664a241046010390740c14000b50702c08136040d12030365040301c0d0501100303d0030400c440100000c50003410391400c6ca40c509514140d6001c201d90141401408604070544502c05000d04440220040c90b5094030343c02444100b01802d50014080140000004280560001005e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269187248 1250 269185998 269186069
    0x9061f08180a0c0504020a1107080102040f0f0605030f0a0b0303030406060905070c03091701090602040303210209030c0105280305060f0607050c0105070302030c03030f060a050d030c031107 83
    0x312180004800110b03100e610818005115200303024090100303042c15405000350089034104804511340b04a8140d2424a1681c00410103a400060501c00c0200d006588001044400021a4814103001d0082e080d8000104a40d803040100c80015040800300e030060f103007019014095035600c0c102800d004001e40001d00800100070300380000314203800c2c0f188100c1c00760107402d40d4560b4295418201e0301c80c044001c003040841c0ca0364a402107100403c9280c4002c1c00258840d407544441e4406400c40002c2c1c1d00002c40d4494010382c0305211420f11601c003c1680034200e2000d2a020780d64410a4410300f06203055003030881186802d07170161510098241e84058000c040c201c9074400700500207410003245100f4480b0080c100c0d0010b0311180f0032540284003a1046500c28016607043c810003416451454008840110200d0043c0050003078034240204070401604e01610301080d0b200d00d645028083e000340c100020704200000d12840c202240601c290340180c5110400512410b40544150f14900d02c4030301d00c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269188498 1250 269187248 269187271
    0x315060c031615061203020604030509010314010b0a030507091a0306010c0b040c05041a010e1905030a0309090506010c02090601080a1d0a1704081c0228060e01150509061f08 76
    0x824440f03885d403811000c0b03650581c0101070030f54545d078003114103801c0000e0302410305440313611002000250040c0b07140a4411a83c0c0c0729124540820000c00740e600141004d000c1c4029441d0501807800c441c1002c281e0700c001e100034543c0d00c6d221403004a8200d11002c038058203e115150511081260340304e900030890b00200c0c0c090012000e0307070302172401c0c3d0384080c48418042144000b18418500f0805120400f41d40300340c102d80d1030719640b8400700f4200082490202c0c00034010003c1407010f41424820790350415000e22b004128804a64086680540058103040c180a000f20018a0103200f64004402280300c0701d02c00ba81221101c0e0825540b1810020116603101002e010080c8940c504010b0b40d04546980c0010a42d0b1150f91590201c0c40000c0c50400c0114054010010040e800e103100410109100b0450003000d1034250a000c03003160141101415aa41054881c10311513289a036201c041d0b0b00d044800c1c01040e150080000e0444e8408a040710743d80002d600344e00c8500342c0040d4041d110785a40f500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269189748 1250 269188498 269188511
    0x60308071a0c070b06030106080109050708060702030f1b1c0201020703021b030c010c05030d1814010e0607030b0414070203032e030326190609020315060c031615 71
    0x440507465404a40030b034440201404110040356031070410581102c40070f000081d001e51940c031003a0949840c01e00030350745039101c0c20040003440c0041000f1a4404110b101550900388059000702c5513204101010844068a175012031807141c0500003500744040b461115541040302820190103500640d0f000d4026001e0482034242c1a000d52250b40c54511000b0060080404054010f41c0c0441c1598011380d01d6200502506060407a54450015084002140a0b846c44818078020408040500200342d940e4140400e14141541c0000c2954009487e8100401c588044401050003402e800b00b1404881c3c190000340205190040001c500549010b1003100900c082d10801014900c04502c4851100f602e1840410102c4c1c440c98904048440c2e4140b070b0300c0c4402c1018103450904000341c1d0b021a00469281c8003802c2222588111802020504029410b618005100d42d8000000040e983c0c002c1c90009452104104244100c945201c94400001e00d15103541c103024031620b80e0200c0c411304141c039107107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269190998 1250 269189748 269189783
    0x1c020106060905090606041215020c0721020f0111030d0504060209040501050312030f0c0909040308010501110109021e0111030a08090c041802120c10020f010b0a06021e0c0406030807 80
    0x29a6281702e91400341c8202c0c5820b00e40305903000c00c0a821f0308240c5040551219001c0c4c0440e40c0d00043c0041210360b03006200c00e9041c4000600410808400c084200298070030000c01600d609030a21001c07542420042242c0c0d0950344001c1c02c42c464550780e07150b0145020100810000320754040c0c0b40d421410358041001d0303a00d45090540c2e90340010140010200180001418021424001d541c003404200a550500001801160418500f40da040b00810103003001881075590011400703200185c0c1d14004e005003481078000c108011407840d40721100340181d0703408011590094410b00428134481040301c2d43d6a07100c0800604028094480480c0c6014180e40641c542c07416010303902c40220b400b0003502451203075500f04288900091800400c602440440700300c1c641d280060710445540c250050440b82d002a10800c1c2103c184110141c030a0885e0030060140c1f40c0d00103400c000584100c9000784941c40141c508903d0300705441c0000da0b1260904101208101000025110382481410303840f4503180c055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269192248 1250 269190998 269191009
    0xb0610020303010b0c03090a060f081b04290307020a050607171302040e0d0c0c0b04150c11040612060e0d08070c0c0305060f100803031b0703021c020106060905 70
    0x8110016803003440180300714912000100001040d901c03c6900d800d128a010a00e000316591280c00455621100c0341d9520f900442450361000002c1043c06000c0c010b0400403913517000d58040c1c420b0528500602800115440310006004010130b0f030f020fa142d00e01228001e546103050141101c00e070140381c000c600628001c0c040b0142840c400020018640c0e1040b003803514032003400109a03841500e078841c1c04442c03801880088082d0005981e6601c0b020560306100c200400c0c207030700c9001d52410400082050600341d40140000071041e141c403215040b810b040c81c864a250829003203174880d150000008148010402641c846031181c8000e00103c00176144058440719070314400400f00701003000062078544900c42411311144126032110019407a40c950924100007110000c0c3c1d0700030000d0501902e0a02286098020042d950003146146080746098100c04000008001d60b110013003044004c04d8000d01549215410099003481d194203e620005c2c0a01050722841000c0750040c503002c01c650400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269193498 1250 269192248 269192269
    0x30317040201020a060504030e130507091e0504110408030f030103060e060709060503090f0f0615060c07030305070c03080c0c040b12030f0d15090b010e09060117040201020712030504030b06 83
    0x5801071300d981d00d030544640000e80307401442282088428443d0003c250741303003183c03001e1110301e490f400111880d0504007d0020705d865044925000180d000c0039082c4030729a407168068400c180c401081000178000c00b2505401180c0200740f00d4000030070703d061030182c0000a076040b28020355080c040e503003210042e00d031039403816203025000074105407081c4038050152004503001100001241c0c9115564024181021ba001984402c150050360a01c4a4284040030f0350441c40411200e0910b800c0c0c0070554981c5e00c1016200045c18003501081c05800e0040001e107483c02581c00003101969400300106580d01c0d0b80380000c44e0b6105c0d614200d40f0440314104480401030312060741004528103040d044441406800555010000c81d8503990124044144800004001c00340600c0100d46150b03800005045854282002d500070160207080065584e4040d078401c03120740780c90b0b4400780c9a48840c00101c2c100019030300203801d80003903481d11000300354bc010003c1045034010240d0811070b444840400c808040e6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269194748 1250 269193498 269193503
    0xa0c030807030e0d0534060314160503012327011413051003050708030c0601240c030e09011701060b121f0e01120506090a03140c190b0103031704 64
    0x21803d00701012000c4200e00d00c0d0342d506c00c1c039401c1c10f400307441c03543c80700343c021540003640040e80b21040300391500341c3c0d0114160403400001040c9501141580000c2a5010521a05017000e1a041030751000200701403c40341c030408050640b07125214a642c54049004418603021110304241000044040403030806460040b8002c0003a10800c2120a030080a042d01901c1807800411880e00040006c9041062100810340701c07020f1500c0305005419507040c040b05a02410f1504030411680306000420400c0200d141010f080c629511f19142c00c0449044250748862504214403100101d04494100c8000f60b2807000c1a0007441025281c0d250100a4003485900c400c0450100010030810740c0e82c21011074440050340030f003500f0903650721a0581094400e034800049500740440c1c03542888424442e199000400d4070040c181c405540e0340042c10504a910405044000410030360b50710310050049d0441c0c140029980360303c800047c10300c01103c201c280300803004103500511900c401d00307000140038811038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269195998 1250 269194748 269194753
    0x602061302090109110903151b07030207050907051903050603120c070303081305072319051504090501090e010c020601060912030e0306040f020120060c0c0a0c030807030e0d05 77
    0x4d2800c41c041c0080e004d83d4215942c091814003100d803080c0c80070801c02c031034010800e84281e00f03400d2019100c190f0285e6420111a00c000411082c0f02080e00001d0b03101c110350042e03900d6040745d80e400000322060b01841200d82d0b48207070a40d454102c119410741101340110412800d64814813038080c8190703110312a402c4440800d402a117410000f0901507500958410000c24000740603c0040d961030b404e0043c0c503003010074025801203815040303d40f403210700034007207100f030b504140c80f128502c031b40005d00c802c1ca00c5400e10543c0c031042e000415542d2031080e00c004003007170b000c1070089584602e003d0020700408041440c4c03e40c649000c81c41001e200041441c1290100d8940025050828120300d002038201e00c405c2d0203100d4044081c0c28107031001c01c01e040c4518040c61151407000341c18400140b058601c8501103050043d20407000c1503000000c12110f0b08441240042e40d40c070b21004171a41e040250008010f000035142030800021710000364010800180710b40e4800b24041803210030000d000032801e401500780e9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269197248 1250 269195998 269196001
    0x9060c021207031e170f0a060e011413230402270403050901032903060105040221150a080609010e1c08100306020324040b06070b070903050a03050301060206130209 72
    0x660510354101c5072a19980f40c41485e00c4514002c1c0b1490100941c3e42c0d60a18050004010341140e852080d00082d01e1803540d40172181d494800040030b0001c1da811803038890080c1e54a407044105a661000380030203010342260681c403032004d20f1402091421101a8004ca0504009440090030059a510300b03210040c9100c000c0c0c1c44580741203905811403001a0f05050ba140c1707052140008150950302201e00200c42d28594040240c141410b01006a004500650062113403051910087c00294018002d9002516980d950151003030301d000541c54107550000000100810342043c0410014402e00c2104000e01140d00c412011554900000d0700e02d03840c2a20410803200c117684902401600801d4001214014949944814007264000e0343c90200580110822501e11804040040c003001b00840e020070030420f0304408602148a1044020855041d04000424403030040041c50061740d00401156a1200030340741c0503241303620a01502015200d1280010049002c013a0030350a00303075020f410354126 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269198498 1250 269197248 269197277
    0x2301081011041d070903171803060c1b0102070206030a0507090602070305030d05091005090c04060803040b0306060f19020a11120706030507110f0109110d20010c050109060c02120703 80
    0x5007000307040c41301042603941001000c640707030090582c100034440c808240d482424a1001c0211400499000d010750417034010030142c80080403e460705035003191030b0f01c661a42d10320b440600901c18108025801100802800109403144d4001c40c4100c800d80c031400c1c4031030f4032000240d0340c0700300a10000b0f1565108014a6001d5512500300c643c01c5030b01c50b821a014903c0c1c0d6219141998030480c0d400103141d10510f282c06c054a01801200000d0a140e801366190504000c852035081c80000c020602a010010720f501803100510111410f0381c510441d45000d401d0130403002074550165035400e440c5070390a0752000d8403e20b00304042c41060140f150042034218a04070060b0301800000380800c05200541000c9880c514060003c0c030301240540d80000f8045d03806160014000480094090056403101d403000c000034044010312080300c004206245510150100403941894052801813042d400c00c54a4000c10a45412010400f2143e07026692401940303901d0105d00c0c00740039005000901400480481d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269199748 1250 269198498 269198549
    0x1120b0a020d0e0a0506071206060509040b0604050d0b10090605180a06050d14060702010501060903140c060c15010b03070c0204051008010e0f070603090206040504230108101104 78
    0x15040400400410a420581050350515500d90b9017035400e50041c504200c0040e9108101d55500f000c0c00b83c08014090034040010071500804000c140603690f03a900c0480782d541d807501680d0080500406064880b079141c44c090364081001d0707805080c0c0c1c1046600c00324414000740a41420b80c0e8028161050741a0701a240c442000301c054074500316990b481102003034039120380b03075a001d180d8007801c6103c40040a005e80d952500800070540c1086914100042c007000f5800340700481100d80010892004c8820845020b00701401d664130264840300024580d200350a010601d04044041d03082104101e03a6100030003042d0384421101391000550710b4a201c3c0052500e80d10041e040715031081d47d0300b00070351607201d82400c4070f80201211900741e0060801d008030b0707442002914003510380ca00d000d1100e03030301a0340480d80c04c1c000e9000d500d11407a12603290807111640010400082a180c4444c283c40d56910310f041600c0f42003840c0108030481c181900b03070300741c4480c80e41100d0488980d0125400d8005001116a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269200998 1250 269199748 269199757
    0x30f0402040b12060c09090a050424180c050306060306040c090903030b030d0206011a120403030b01050d0606050c0d0c050703080a171e0619180f02040801050103030801120b0a02 78
    0x154007080f00048040004420060300f03100d074105001903507603941881d040115035240184200c00c1c140c01c18003000001030319a4400c40412140c440d1441d1040001d0448001030043d40b0301c640e00044003141900709010040c890344044803000c0d03054405649071802030545425088070003802541851404010418856000d102014045c0ca00012103c0d02c03035000030709000c0021a03d40040e44510b0050141100c02d4400c20710034004074030210300d0011000104c40b2544801800542415034819154031a6409001140c0031112108820054a0744580300641990040c040304210b6100d20038052010304e0080710004030440d0000000d196203440c40c0d0b103c203510f40c030800020b0300f045100b4945402c007000e441d100030700070980f1845010481195200303402d0381e02c200a0406d4841c01d6052701d40b140420040d59158250f0301e84509010390f401c603500110001d008208a21a9003502c00900015070303400661101c0c0c181e910130b540d2421075036a6021040d14042814401038010b8a0310800304000114590040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269202248 1250 269200998 269201021
    0x4210b0403120f1401050105131e150207060c06231303090909030c080d091e061103060f01110c060a020f0f0313120323120f010602070b07210c0c060203030f040204 72
    0x503000ca45608c1c4800c04500ea0ac08a203041c03020880d418400701c89581c0202186410f42e2004010315480c01c030004100070000c01e006006a552089490f4403050440b88112800d10080240f180c40c1c204410718814040d1107a80690004031034540110710845140a25500150155a4500100c14640f1130f1103d1381c0c0804002d5400a5a40c44040c00140851020040000003200c2a09500a03141000010361354210000d000c1c491080003049055594034030b0848100c00c0a1030425000b0070982661803403c0d41d505101d42c0c2c046000300d480352806900103000b404036400c1c20180c40c2111030f2101025500c0c040c41c9105441038210040502c028420301074103400c8203000e490640070f05c640c030240382103030001940c0511a0801300001d0030404038003212940d82d00030905a81402e0b440d890200000d4642c840c1c3d0007034200c401000032b41d40f03003881a10b40d07114106000015041e2100c03108207002800034180ca52085403440b8030828001005800031042e0f078402d845c3d50101c1c403003030b58803507003004020401c80200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269203498 1250 269202248 269202277
    0xb090607050f030a1410061d01200703170c07050319080a05070227100b030c0705031902070501090602060108062e08030901200304210b0403120f1401050105 69
    0x4001e1170b0441342ca5182c080c2c0b150410381240705080c07020090500ea801d0301041c601840310201d00c403850743e104c01000300e10403500d0b03a03007a2030081c080a114100030055002034190000c1c0c4500440c190b8168004007000c0540300120360480d65114103141d15420300404d4078003445030b840441c20104070368a00520811401d45007262514032540c1c00591003034020200600b42c0c0f1078140503812031010006420382c1181d00c0c0d24410301007134070300101700c52140310052040024000100b2518100705040050340c1200b9141400c618440d058100c5c02561151980b02d280d00184031040300296050001c520141030790072490250042c0d0f601e020030031901c1ca0b00d0000d80c2040d01407805913849030a010061034809886030760042d559505155000403c895480c01d40b0540030200100c0e20886c22070000300f100c0898043e00040c0001d241404d2841041a461a001030540780008080008041e07001003c1c1d01983e551410410000c006c01103050102d03016810304140441c1c090005100c1ca6000c2c0001d044803024102c03d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269204748 1250 269203498 269203511
    0x1204140303070807030506030604020a1a040f03141e0d0806131a09013002060f040f0305120306100e030115080102040306060902120103060203130209040308040b090607050f030a 78
    0x1500d00d15031080390721100040010003400a09980b501072180c00c060102c00a1a00703050540018103c8200c900c0f03072600800b03201e51000303d03942c94603080c0c3c2d0040403c103510700c11090b235a040031200001345440f500464055860904400e03406188084402000040100041e0a9000341a940d00f8405030180d03500c415000040e0540402900414040004406040c1c40308041107007400b4180307506811410040130180381d0031003214403150320000c401a20400e5940c00e04454004195140314062030072407240400540420587c4001444000700e82c4a0030440e00501110300084103103000607642c3e640d000100202d1580c81c148100c81803140b09030010000070358500900101d00003c6402d5010300361a1750041410428060716124120050644c20300551411300c00803070000241005001c0200a1075002c804a0740c07407421800c0906549a0103860b60301070f81030504000e80a0281240c003190003a001100007140208041070303442c040c81030b68440b281869041040b541041e00014030000166603580e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269205998 1250 269204748 269204783
    0x10903060504030e152d0c03040e040519020d11040b060301080109140102040f170c0418060e1c120e061302030706030e1c031b0306150e061204 63
    0x1c112801144642c0f508000003420390300780f04c032040b0030012501440809112684407102910503079a800c40c507202c5210703c06040b110126025001d0f1480a1185200c0030030007082400703a62000078062030040d0200e9079a02c207000f10581e55608410741c0250480043c101140c0020901c00c20a41003203c01040411b000c011031300814081d0b00260300c05a201e80d110354111043c408441000800004010000d42c605400c0007500c10360083c0600c20744613003c25450000101c00001c0c00507280d0030000900a00c07001a44d01502504036042000644800386411944a900c1a0009400007095443d590182e0480310700803003078400d40641614800c2c4d0588231032020040070003e205c4a446045250704480c2141c1c03a80c018989000d0903500001c0c1450302c0c1001c04030b0550800111500d2420f0340b07001158541c11021000c4015111000300444422030701d6090050302501500024140c5951030440c0400540400086640f0003a440f400ea4001c1001c00040f0342041c0d240301125800343c004d00c0050401490403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269207248 1250 269205998 269206001
    0x50d050403021515010f0302090a03020f061603080106090621020906040801050108012a021c050c010203100302100306030b06090411090403080702061e061306090e0a050d03060b031501090306 84
    0xc07a00c01c0c1c440d1013400940d007610340e00103d00d0490890580303421818038081c0b1001c2400e0305a03a000c068800d29040b85040c81c60b0380c4d00001c8424071038021403400300c03042103442c018245080a0041002003403c201004c2a0b02d40f08413000306111401240100404c41e480d000b04000350f128038002504140e041201040740c0409005803402040d148000180c14240345035240400c1c40c0c6d84a1420216480c0300c25100540d50000d1102650500c0e02188844000a25010760780c9100c4d001680310554000300802004404c241301d4003044a0081d01c03403003603603074013510f0072801c48149000080c4032180c014007191880c01e2001e24641e005210341c80301004102d8a500050003460122001c0340040c411340108544150f040c4400c981001c1c0d220b12802e00310010810700000004001c05a0740610720b17424203a15100b50740d804c140018000301c40300700321814402803c171341c55007036161003901d4501c40d00d944295610300c24840d40003114030031040303541152101018a6070400b8190301050400101545c00b0011a10a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269208498 1250 269207248 269207251
    0x30306031207240204080f030c070501050c120a02010912030c0908030f0a030b03070909260a09090906061707170c01021c0309050304090501030203010e0a03050906070f140a031806050d0504030215 86
    0x7c00e802540ca0f0300c00311546a2402125800440c10044144515507401314001456070080012808150b00c40741d811070300302e00516021a0103032114a240508022454056010051109245d0380310040720340c0f1143c099507030303203e0540b44c0741a0780400c000d1440c401e441f0347c0c80344900710002400e5803051541e1f0700d5110107541190400740d0b03c851030f07441224919101c02604441440340c1c016103605100c80403038050702c80d2105120340382d03840307454184c940d0400415502180103407000f09080702c41c070000d4010ba140c0d1810113026840c0100318141c81820400400200e40201400c143d008094001102c4021013200d4190160b14003450348851802000078400d00c0600f02400e00d198000401d5071460040500303682d6014030001003070f0042c42c0c10001080c1e000080700c0300c022090313400960f10340080c50a0245590031000103802d1424002e60035031420000305d03d8060305806541c41d15034075030f1b40261032050344069124480204004000340c2116600641029500038080d0054130f5a02c0004600704074101e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269209748 1250 269208498 269208523
    0x6030f0f03250507061121120c0c0a0c06020c030a020906190b0a18060503041a06031504110a0e0c1611041b0906031103132303030603120724020408 65
    0x5131b415190070f0000411601420300c00003083c1c940c43e40e10f03107040c07010039100e40c01a000c1d10010060002d244909600c0440e182903000c0c0301111110017031810a05844201400b51000602800d0310821807071400184120751150024900c1c00d403504c80b0810000d1f48640f82c4d0040d2110758140c80d0007d005c9400c1009810801c81540b030301c00320311105501d000c0c0e149800343c200c002070020034020700c80400d00140b5241c1c96034402c50340550090300c5080000e0b1511100010380505414404200810003480001c1c2c6801c900040c6c402c00740301903d0340d12540d44008200d81c4411081c0040c0103009070103100403828000f10740181d00e052100c80000d0045400c0c0d500031502041e407000d9031240010000d6002c54908000c240b039140c00c106a40d2032040c0b1604a10003e0039001c4000e4201c03000600b0702005441100c607800d0711000740c503914460038003112380b47e0708110f91283c40b9001d242e0b464100020160100d80d0340592059080e088000c2140c419000c4142c042c6084005070341c24800031800000c1007184131211740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269210998 1250 269209748 269209757
    0x2010902030c1e120c030703061409060402010c060f0f05091c0207080d12022a060603010b06090d03020a02060a05040f051c0b04060b0d0b06030f0f0325050706 70
    0x1901801814500140724018900a0b52558501c0c0e8180015509081e02281c1c200d03004100d88140c620703000d241c40c1e4054401503060003501800420001381e5032000c083d40a0f0940e500c050f40d540c0420312a118a821a40a030205400c00182e40000d05954054540140c000c2000145444003141c51421a1003c80d4100030036032040300070190940040306100c80d40702c41480180101820018125103801c100342141062100e1044410340e11601038050721071402c2002c4c60701d01000350300012240d040c036900c2011906801000c000c2081c0d82418000e0064030743d809002c80386840403410a0059a48040c00c0580850092070808401a61b640b402000700b005a44d80b1280c50b40d080c9900f824820303007594050352183c070014400c0d906440c502865100e000b900440d01070716a60f21400e086024250016407103074003802c202c590908000c0d144418501a00090b000c4900401e60400d0180d42c82c0c01141c0b030500c103580280a0b41219510417410202e2132f180a0b0b8204040c1c0c01035580703007490100c540d04a0030104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269212248 1250 269210998 269211011
    0xc010207061a040b0a14061b010213090606020a141e011d01090f061d060408120901020702010e1e03150901111309020d0b100e03011a06030a0507020109120201 70
    0x103402d107140ca05003419080b40e0420218004100041d08a9118400d03a4042032a1030703034000c060750381c3d003080e036902d8845002840314070306002d00c2c0039000b9400300c1c601007804130460401040c07500d118402d02c2e023a1005a0000c2c401e613002d688811000c2c401540d040c101c00d200f068041c21072142e201c00a2154511183e00200d02c92034019110201042c0741522b500300f581c0340510345d9011407100c2c0000c04c10b41d0341200c0002910404480842d0000b80f1000105100d803080009004c20080f048008066911000b4600602034984019890a1b8800c1b810007900158103805011041d02d803c1300d10920404024030181560040d000220b4204034500c1d91500784212100300304600540203005004980103c01e40c2c2034a000e46000d1a20b411917424050000030703070383c040351981c2d1441d800d1307000745ca0752440200036500c50070408200030007902a00d44000e00039428010007000c41e0300000080994041c0c010205811079450120340002880300505410441d920b841c9847c0102d5503500e10788294050690020409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269213498 1250 269212248 269212271
    0x30a0302010f0e0109020a140d05150a060e280605030115140907050a0f0c0209040f03030f0e0a0213020d020f04090b0d020108150a1a04181803140c01020706 69
    0xc40c0e00f019801601641845550300060f9101c0701329500f5031b42850000c04c01e900804c0c0208880200f48a4001d101d032103461540b0100b1740903001f00314410382c203841c02880f0f41c40d00e0303446041040d00140e881d20102a000904105100455180540e04010560001403400c0c3c3ea640001c0c02c2d520310604050307510584110502c00740244512144071510265402201410301e000001d05078400c450b26070041102102d000b981e40e6224442007113150750000c3c4000101d05103030170320a41c81b14041200300c000c00c4c074007684005044014040c000c4201d40e81e0020b400343e14500d40078051420091101c0e5a4080c0d402c00c005010031100e407016040e4641071000303c503122414036040c002203500c40c900c800d1140c0c03184800c00c80103030707030043c201544074504552040000458a01003400d8103c540c001d502400215200c414619105501030402c0f03464104070b00703d0340b8800c4605501200c00c0303007003013400c1c903041060041d0120b401110034040c041d4219207114170b00045007040d1741c00ca03001590201d0b6000c1c0c03201e070541d41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269214748 1250 269213498 269213501
    0xe010507031505090c0a081b1801030c0c03020d0513080f030403030221070f151e15050915190602030301050f120a030e060d140f070f02070605090609030a0302010f 72
    0x207410144c407a864981030440c400500c9025a09103e410042c2d0740c3d0001e0400c180d0410f0b01340c0c0f403181e0302c01e130591a11550f040104620365a05010f42c0042c0c43c005940c070f203240c8180c407800e00705501342e0080c08a004603004200d80300d40c08203001e01c5458080c030500103043c4070308000140310101080e01a6884078118070f4024105010410a4010101d4070f00c07110034088003000464030b02c6d9038403418000c000707401840c00c0402030081c88000e0320000e1905071804030401485d824180d90000d1908200b01840c0e000321142c45981c140c0c01070b903401c40e00d500001810b40c801421418001c0e1401400500c2040d00c05a40d00c0592031940c000d480141c1020004200740d04151000b0356a0721800c4610510205042d41f0103680c1b800c42c40d0380603007005200c00d03035042c4030340310740e41111031800041c10140500307c0c01004490203120300369454211124028001250544294240c0817003540c00e50182500a181c5a000c480c04e40000082a6000c0000c0203545420b580400024181781e00c02d8001086041440f600c4130f0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269215998 1250 269214748 269214791
    0x70908070605030a09021f030509060603032b111b060a0c051603031e09050708030a09120503040f150201060801020a090e0c04050a060903110105190804060e01050703 73
    0x10050380050014004680c00c141075990144c20030400081402450001a14120040d00135650074011049030010242e416005948660040c000303c54203602e481e01030607a80d1290b22140748030004070740744580c0001c0c000b4401c5041c1e0072800e06c01040d043c40c1c4110a4030300b50300c07072a64844c0700700d2492120f80d00f618040c80641c0c2d22581e07808040000b4245a20082d19920950350340302c4c4400c3e804085807040602030380c032072f440e201204445040400b100c1030f11500100500c000984183c495079000044e0207030700004441c0b0300d846582d120b6451910304491903030f800d040080200c5c3c403400203000208c1c00d0750003c42a04020302c0e96404a600d10415a500079084542d580c00410319a4010420b0900321500302695004440460908481c1e596620301001400e0261b81c0003a9405100341d800003a40c03550012001b01503e000300e218032015064000190359920803080f080d15402c404462070f15106004040c140c0e4024040c01010800241e05d0194a00711303401100d0190103c0d03998550813410311103803e00306 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269217248 1250 269215998 269216009
    0x1e06061e01030203041b0801020a030e01020a090b0a090503031801180b03010b1b0a050303010f0f0e01050d15060e01150305091c050708030406020703031b0801170c09010e0709 77
    0x2940d04540904408650503200d18180c185600000480c0c100000c4044000000320151105505507880e141580c0c043d50040c504030002a062a801c0c840c418018803c40c0d20034603240c3c54a000031440c010082c80c150f00714242030000d00c46042c000044a072418401003141e640e442c03804c9905126030707000260507101003590f41c895185c5168803d0200c40e0900c0e044a0542d5040090700e521023600000507598806817580070b01150040d0713802c807020400004040d50503074500743c1c03860910648070f0903602c0c4501da00740b14a40b421041400104410304020035031030740301c900403c0311154608217104400e054680b298448490b62150100401c0080762400503500910000d240c10700090900790070081c3e0710301250200e191060120800501000d00817012107181ca54090490f9449251a081640007908800340c240d01090a009080210a03030f0242c402c1003c502c0c0c1d4440782010f03400c21403015214060782c5007090040c402d1406940184c0d550090641c000e00d5a00c8001c860352402000c010114003103613119 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269218498 1250 269217248 269217259
    0xa0f0203160605120708090607051b0a050105042f01030218040e07080d14090f061201080322030816110d0807020f010207030f08030c040e0f06120601080d050306030106081e0606 78
    0x20300c6a9040003180d101d03040026860103a4a1712f08a0518141ca0745e51581c001100d03110741c5044e82d04110b0b064207d43e20560040310240c50b0741c09500c0c041c0d0f004064048400240580345915103505600035409000b264844445010041810700042400c0340c640070104503055024860400902204000ca58001002e51601c081500e54480d0340f41e803540030f0069018840e00100d100e00e003a0b0f444180036509600f51444084010b969a03440c0740c0d84a600103583c010044903000401d56540000110140c1100e50229640c1e2502c0c10b820003050025000c81d604450807800084007601d00c0c0c0d00c820340c500505000e00d1070240d0b03440051042003c0f07602d0130700c48981035410003081000402d4007100c400d0821504500d00c3c0b80d40e95514070344140c1e41d00c140d400c0044845407200c04e02c520b40e4164843c40b4886e02044d0307a00171036100521041c030344c3c8a10074440c0c000107900c6900c800810500c584040c503001304d400340000c5030141e100c044190512a01c29200800000b03a0000745258070030800c8029046131007500c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269219748 1250 269218498 269218501
    0xc031e1614150a140d09240c08010302090106030c02011e0b01091a0a0c05010e0d0f0f080c0d0902040e0a1a0c0c0705120a0204110405130b030a0f0203160605120708 72
    0x20261016510400c140210503005c1614900d240558004a035801c2e8098052150891205c0380c94036102d50f00075024403011324060203c030f18240502d01c0141aa03070000c3c13295555a203000e000300c02170090020748104654a03428440000f03a41d0310000e030601040c1840100307e103030494000501520460344000702c8603423602d5000301c081c00c10a04075a00d80c1c1c05072606502840c41424428094007a8600001051088894440740c090f404402c0041e2812159185651000c0b1717130404681e81c0ea01911100400d8804024900f07445030b00d03900001d2054400740001c079980d400c409e415400c000d2100025284c3c07015000802c80d240c1d045100da603038014612400d072400e000328084026520b411074094103010f100009100c2d07100d40f40c100b06900520b81d008000344080c85d0a840040c00755000340c441c403405204980030f02500982035010300150080e01030003e22840840d80c440032a0f045e2a001c0690300b40c003e48101a803d5a61245420080c1c02c0c1c43e221641d5410841e18045070721480180f200c8200b046050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269220998 1250 269219748 269219767
    0xc03120406050307090e100f0501030507020706081e01030b060901080a0818040603020627040902091302010507120c050706090305150c0c03070302060a06080c031e161415 75
    0x10180c409840d49031074280e03180e03580c024050380c440d1001d81102400ca01a80100419140d010201c102940d0707210789042202584d500055081d9407040c0c0c2d041016800040090081501c225020355008190b02c2c0340180c1c0c0b513002041184214006e81050b690301c0300040c100013031401c048c4403503401048070328010b200b44040b41d22250801d000b0021081d000107042a14607884c0c4e90b40e42c004c1c0c009140c004001a030388904c45407441e05c00400c07400a001d886c02100e10125060301d410300c140e10001d500a0320151450743c803090403040d0b02810040480c1480307401d03c48a00400c00c00d401042810038182c403181c080100508240f4a4000700d0b92140e020070064034814400528041000c2c4942003290880340000e450354080001107000f0032003458440e22012507078005144d40004c1c018000c1e01501070810090351140c1c0c045850703200503048180c15501c00e480054010700c1c4080300204808040d03045c0d64030700710411001c6030800340319801551718401422000c5003625201e1030704075401031a030000030715099080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269222248 1250 269220998 269221033
    0x106020f030a0f030b0a08010207060606080912071502070b010f1a0a0c03021e0309040501050a0803040b0c0a0605151905030c0f0303040e041b060c021e180103080c0c03 74
    0x51215030100180100200c0320f082c0640c1041990400c0244030071292512208124001e4008460558540313003441c0e0005a40c1340224082c4c1d014200280c06060b2580d80b4500040041e807007000e0880e401c080303a000795551441144040e00045120301c0402d0319a52500703500903120752141d01302407507295503105da1000030b4100204480c0900e4142c01c0c072122030441428180d04014501000e003c903265a00c605039041c1c03c010005181d54101110100100c0c1d0301d031400e02c1400d0085011f810019481000140800c1030b084010304031b2034141608848034544ca564030f41081c1c40d42916145142e0f41d0200c0100348626100202100f00c00c010120b00400c240341400107a9941e00900489010b440680d0b03400003562403c0c802c44002d840c428103608a0b50410f85000c0c01c2c100c940340040040b49580042c0071444600c903c955140c800c0d0018240c0760168083c500d00540d801c001022540d20085a010500c50070b101e22400b03500960103030307005a807141c07004a00a420820000c41c060304c290010261045a259103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269223498 1250 269222248 269222257
    0x1081b10030b0316030b07030f020f04060309020a03140604030e09040c180e0115030c050108040809190504050411030c0114121f090b040b06070b0f0703110711090106020f03 76
    0x25180200b210b181c00b00110381440700c0300c106142d000c40700701c40110a00400c0201c0b5030054030650340400c000d402145007070040340070f42001040001000c000c20070080e4840d070007840c0e0590004001000456803070395501c03010b0000c0300da01c1a07030f03410460801052540003480300d0f001d8070f42621103440c1490300d40c4e903241c0f1001982c0600c0d40000b40c050000303182c0013643e80c8000900e40d02c43c0001c001c503003030f0a01042d00c50b03c1d0300c0c4030031104920390100201d015440b4034107442c040ca501c850301504041d80300e410041640d40480310300359904010000040c050792180a000d0241e4002c511120301800700303100703240c01c2072420901ca50601ca9400d007400136078106003084030507201c000b20071400b980e10341c641110200e06090340381020100b80c0100101e901c009543c05043c240404a40400c8a161901d0a101043c0160310300a0054000d4000040c01d0b440c1042d583e40d072001d0319260000e540358021007a070140d6007040c3c505503007605402c0040d603101d00f000801c40b400340c40e2038001000c0500c0002da01e141d59118 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269224748 1250 269223498 269223529
    0x501050c07120305091c021b0109211e0303141503100b0a030501090b010e100509070507050f10090b0a02030c070f03090b07122c1c0204060e01081b 65
    0x44e11301c00070382045c2081c40407010300b02d0702140809110850307a4000b952049585c44441b034481e012003c80b619580908020b07400c0f030382030950301804401e034495101402d2240000a80e100030f001d00c00003070701c6450a00b80c154141c0c0309890000703c10300d0380c81111240cd407004040112030a004840c3c040580d07000030742034070b180304010800704d104400800804c0c002c010540c4010040e608194030b003010040c0307501c4524140c40750074001c101706681d403940c4404441814030420360007440403400300d08128418801480d260f03003d0412200c00e1031102075410701d060031010180c810255946400030401c5212860150803d024100542c15814106400e001600c030303401d4000d1407115840d09180800d4010041400208040c400d00358079034249041050201328a8031903100045c0000740402003100c0b459203d2601d9003400021b8842d00c10b0488244030b02480380c03000b0700601a10344001c040069031a400f80c600500300550400c903680d4904061a440d2240d40f00440b01d0640040c10905241c0c0c640d480e0342d809100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269225998 1250 269224748 269224751
    0xc180e0d080c0702010c0f03030c120c0e0105072307080c010e0a050402030603120a0e0f0d0b0a0218040e010905060c040612020f070f060c0f050c0a14010b1c0501050c071203 76
    0x200510050b40c0b042d004140050007400c4080c02c7d4402d064043e4402c0c4103a90b041d443d0409070720080d003801d004968004001c440480d01d243e40007020741d4030881c05016210302c501505d0341d401d003969500000140c0c0d1500908500e910a00701407060400503c40c0780440c81c820300b4086140c3c8140000107a052016014450050354080f000441c56070342008480e4005020700f4905940b02103a0900801140258a90710b00504803252209518100a20124411504415040b4403503c034402c1030fa000e980b025054803031840c9030340f40302ca00310303640d43c41445218031000e00009501d000c0c0349003160502000414080b030114042c0410002144c0000d4003d207210f0b051140184c0c0c1d041c60260520050040da8406000d10013020007150030008280e0055120b2502e0f5200c4030240c0c101801e084031070f48211030003021603801c8034100ca4000340d00043e03040c001d90060400446c42441720000700c0c0c070200c54000c00480098250301d0160900400780300d540d81007200d901c242d030315000c86500d90958000d0945107040405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269227248 1250 269225998 269226007
    0xa050106021e060c0a180b0d050c120a0c0905030f06060901060f08041118011d06100e040b030c1009090c0203070c0e0709030b0a02040611030309071707030c180e0d080c 74
    0x40e00c0380c626130b044840c0c1c81d541440c0c3c80b601c41100710402e402c02100042023500c3e0001007a01080b0510030b40f4850030107a0407043d443d5440c02182c3c400381142c410302205000c00544045003680c0c040c0118160521000002e1185107092810041c011a044c0d000c5028044000140100300354001403144d0320a41203804103e40900c8200840d403030340c00c0104004110325982002042264016401c16040d1050500a4180762105030411500200e0442070a000c1010758220400d40d003041d802c04550850003c0030354880c0c0c0e1720b00011400c8000c82031288000500490018800d240b4180b14003d00b012a80c03005500b011021b58030b05141c04080d0040c0754440c0401c00006180714440c084030030103550b10182614640c01c1c0121004080d4025024120108a0104408a8030740000003a41c2c0b04d408604001c101d560700d40101c030802400620031030103c5001e820750200104c0d9454480500030070070003202c1c841080040710001c0845404409224503030300124030035207007554048405500b160300480105c1c2d55 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269228498 1250 269227248 269227267
    0xf040b0414031e0405030f07050109090b1311090108100e0c0714010c12060b1204170d140604060b0a1e0306030f08130b070b01090b01050c060a050106021e060c 70
    0xb035019440c4010b0521869040140310120301501400c11920168201c0e0546000c0a066a485000c00d0142c81c3c00203030301503410050703403250703401c906910600030300703107108860740d4074250b0040d50056141c40c000500c000030103011079640900140e0703105101d10000c1d04580c1c1070600e0001800300191683c0e994940c082405800e011400c14985800000c5000810011140110140c030f131814031002c40b0705591074020300040940c010011a111510380c940052010303925070b5110702c000c40321800700720340c801418007030610040060312401020305c1060852114902e082800c000540f212600500f0210748144100a078450b0401c440914040d41c00b03a0070001c0030600c440880c01044240d01c00b50869460040c003205101035440141100e404210750b43c600035440710800300b03541c4160800203041d6040c4030010446845249c1c081d0241180500d0602e143c05000c0c002245842010f8803504205655a0010880d41c1d070100200581d40c0700d128030800240804002040c0c4418004014404a40000482440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269229748 1250 269228498 269228503
    0x17030705040b1b15060a080d02070306330302030c0d0809210304030303020301140a060207090203060310050f0a2423060703090806130804060c032003120f040b0414 72
    0x940d9060f10044800140411160008600d0107a44060180f2007a081c04503205801190310010001260001c08446186a65050040c06010403d82c00b00140c01e0300c060440001d400d1607145104c1c0300041d52a0b49045004050400b5441004544901d6041324500b001413000420344400340c0e401c40300001c0000000b1400000c00d26060780c180341a0000003400f000f0540c060340030350706803a80184100300da042c410041c025040d031180034032000750b40040e0341000a02c207a034000f1540100064151184e00c111131002006982d005d440314401c0d80020710402440ca5424464840915025100711050006d044190950440036009010b401500c209000164800c111442e0440190107400326a40d0580e5040003404072901d17028481944c0220303408207241c1810000d03d0b40c800b0340c001e08098501450701105842e8404c05c190f088003406a80900480b240c0e200e400d0074206010010091950740811004d040c1c060800200480e03aa41000000d000106015204165119601140440000c00d018110300d1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269230998 1250 269229748 269229787
    0xe15030c0f06071722050405010503060c070512030106090915030312092901060807080106050d0218031015050108090d081305010c0201140f0412030507140409060317030705040b 78
    0x84e40680001d207490a03081d4080003a500c1c8001070b00f268032150701c501c01c02c02611400c1c454140d05a01000c049040400c840e0000c0c5151480781d0101d5403a83c01510b401d02c40c41d0400d83c07120020481c890380402c61404640500d281c590241e14090300c00d0f07803d5070344c0902910020904190050368440c049410401303014013409030900018043c0b090703804152201c441c0f60070309010710400200002c0110303003400d000300c00141c1a81c3c200e854181c01c00c02c198000c81c00940000740c002c1412140d090700341c0c640352818041c0d8555280180c40104061b85011007488500a00e0352000d0f040015450401641d0500402d46804c040580c1c070340516180c90794884c50b01415440d6402074041d501e4100494141601580400036054080240f46803e5a54010845100ca001c80300901460203500100c40300074441d0384880e50050302e41c10440d40e00c4100000b070030300503003052704500003407951408140306000c0d0302404404014420b2000d14510f2800031402401c50142d803180b0116458003007000140e14060a2514 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269232248 1250 269230998 269231033
    0x51602120a05160f0611030c070305130302130f050c130314070e010b07030f08070206040605041403070615090c0c11061e120702010621020315010e15030c0f0607 71
    0x1200d400604000e1131001042d00120780241c078000002d40b4403021442500e1003104090001030901002d601c0540d42c030342c0000c40005100316035106c00320069417003c05900c034103d8084400941c45040710003000c2240d80c06894031a8448042c805100f0a0079400c58940c10b4130b5210790b030506c1d4098142c60462600d00b0301d030000200e20301000004100ba25200c00509012030090b92480d070f0081c2654400e81c0e0500e016208000141c00071000180890303490f4000c1c6412600c6858000c0310070300e05154890840e0882030b012180151540003020741500b050f02ca50002d031103400740800080000e1000508480750160004208a11145860245595800c15503881c0e607200007940081c030481c070074144104e40c00300d07443c0b44048040301c01060303030310b44144038210a90318010041443d58203040c0d45510441c0d210300c0200d925208810154003d0000e68110b2402003141880341c041c6810682d00740030380c0844960015002e60700520720b12085980304480d66001e110b055650641d80c41050800940d11708062942 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269233498 1250 269232248 269232277
    0xc030b0a1e1229240307031e0b01080c1012020d090308010306141501030b031c0806030d050a140304020301020c07030803061516140f1609051602120a05 67
    0x581e020b00403d0700d4030100144107000300303044803610581c03484010942a640007200a46110401480f600080b50360904240700604035070f00c0e0342e0349135102c10790070041d040030304031100c81f44440c5810080b1520100d400740c60303808043d05003000c2c0b04002c222521b41201c040c000f000f401094000c00c05000342c3c110f902034080c2d080c061200091905000d000d00c60284001c41e50f2038504a403035940003040c180094001d0350326064003040040400700450280c065664502d0b454050019600c0029085d10140c07001d0100c561590300c001e107842010541030034640d0782c1c008244001081101001e036400300c00300c40d44041e55000c0d40c5c0c4170b46130340c000300e40240030350480c00d0050711810030044107001c81c00014500c034250032a20140800b82103452070000b0700950910002100300610080001480b00d000f401c41c00c66030741c0c01c9030071820201402e5440c3c80c8081528076210504258144407014160046603403118990404c2c00940318105c400170754621600c4001c0103500780120314403a8007031160040ba00d030309000702c20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269234748 1250 269233498 269233529
    0x408030606091203160c08060709050405060f0604030606050a0b0a0206010e041424150915040e10090303050f06011b0201021e011a010206010b03130807080d0f0c030b0a1e 75
    0x26018a0101c1171801555002900c2c03900091141c0c0021b1524860420b0f983c418484518200034080908030203080c640c2d010799090404c00c0280c4030403000d440254003c1401245240c80d140900001003150f810100c0c8800c000c001500c40b842d00020841c1c119440c100880380d860380c481c00c140150712101c1010561078010502d0000c02109182c5900400704052140c2c0003481d228044000e9220400404040c1c012800c000021480da103030f004420078904000d00040740749a0108541e80c244480d11582428203a84c0d02400710616605224995100c00d80000c0c9640c0b030b0610000180c000306e561400f406c2455107180c002da0440e48240080d40c0d0280d201a40c2c0582d0544554140d4080c0c1241a41c040c509480450060615031000030458101c0703003200c01080ca962219641e201c5c02078690344040d5005c1404000c0e02000030380401c024214104040c80000b8482503402c500c0c0305480101304000101350400b800f01c511690348800343c00468103000302c01a0005c010100a84800304564482c034042e425040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269235998 1250 269234748 269234767
    0x21003050405070e070f0e030c030a0c0312050f030604020304060b040c030c02060a0c05030f220605040b0901060501080c0d06030c060c0b010605040b0405060a0203090306070e0a0902030408030606091203 89
    0xc00481c0600c2c80ba10541e000c40381c03030702c0c800c00007244115500c2c000500c00780140006103020b909845100f09002d401da071054a5060013007441e0440707400c8201d900140c802400c200f844603042e10348100201a18040c0d1804050310b80b40c035461302018091034800c5074000082420041254481d840200b0041c1050050250030341c40074006104505450f4050b0247c88001005004a4400c0d41d50307405164480905540310541000c48a0350010400e480000120381004805030141034454040c0d40720361300118007072909181c4a9030f00700024110a40d141e04181e804e21550ba0009400c1e0703813000041201a840e04010402a405081c0f540c3c005443d03151f0002005c101c01d50b014958034003c034050442c550280e6603460b0112120701c11840f0706100044240b00503c214a0001c004000c80c1c1c4ca184103d0f0b003042c00700030010b400e090007a51300b0808190048002c080c1420644911f600505a281c030071170852909444003810351000502051080c40000703906082079540d2100b10f0400060a02160b48070120031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269237248 1250 269235998 269236001
    0x10302090d06021314090a0c0207030501050114010e040209010206010605091c050604050d0503040b040f020103020c0607081803070201021002030c1303060c18152a0f06060509040804030f0f021003 86
    0x1345080d041989021501180c8041182004641101e011380403c48076615000020001d01c1c5001c005021401449000030103e0401d005050180003a00080d01c0120803810024080400603c41c6e54003c5005003c065040ea8001c160f450458055090540c3d5500d002d400146400c0903561401d07021a081e040c0079800d0200000d0700a100324465801c68540c8000da0310103803400e000445008021078440740014001903803144040a00901c10f04000d81032000c24140c1030300786542111a41b0000d001642040303060062031016100d40c041c200059407a01c0c1007500001e4941800b10000130310302343c0000c0031075141c110b25800c50b102c1041d07403804070325895201c1c60014080e00204460f000042c101509802008280100000449000078503600940c510080d003503c0c9160301e0341c041b900d5641c605070a2f0045603211a02040c106109034a012200d08152a01e182203444a822050196124400308000203c0e40c000722002d4940141034207041c00b10301c4c50614130032100c40700f009400480150f40e9140e800d805 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269238498 1250 269237248 269237257
    0x1081b0f040f050a0f0e0c16080309010506010206010f14040b0a0f0608070e0901051c062403020109080f0c1509150301170c03101805150405101e0506010302090d0602 73
    0x4464600d03013182d41c0c1030844400709403402582030301d034855404501e00d8050744c03006106003508030107142214030b0300341c0314400c45070412500e952060351520100142c641e0306120b91405800b000c0e000c0c1a18a0800d400200010780d50b0503801d0003565102c1c400c082c03580d01c0092610003064515801541e2685418005144d10307400d44d0702c6c80200320780e2144060140350240205060b00ca010b058441554881403200c2c110400101c802c2c2d6130706590b024001050078009e101102942d2104401d218064614800104003148036407256805800400060001e0307580402e811200d460122650213091202d18121201449408059039001c01d4100003030b400c601941016604a070b4a4415211140d007621450790b0b01c420191800590681120f4401d070030780c88007540442c1d22458031203c140d0329110203544607440c014400d11118455011b03d0208410880100141501c0340395810051003c004c58501205c41c2d5003c2e4455403900d035407684001180359120307030306440390414018404500c042c1c0a041c0000203601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269239748 1250 269238498 269238509
    0x215100501020f030a050a0c110409231b090702100e060105120c090a11041703220605120a140a0b030f01060302060d02090604030213020405180601081b0f040f 70
    0x21076401400c03c05000c0b056a444c0010358440500d001d2803e8000c0303e03005202030085821081c000c2c5140c40030b44440c800e4104c507a1145200407684170b0b102c002c102d0305201030074609459038458010b50051008080344000342203401d85041c0410b44030510140d0612141007004400f1b01e1038001000149180010f8190482e001561114900c40000104640703511103c2c2445030000180030210381d44404590052102c2c00c01030500320b0a0607102c6410000d088000030240032107600100d0820f03410082c0c3d55401c08400003178104e0301c0d442880c1020180040c001c0d02403075207601c118400003500900b03458122000d108c01000c070001140c58100c0e1070301c008001400c941030203403080d215452201c84c0144180c0d4207480e0006c04007805c00013844880310280d48006110f03900315001f03100020060f110b095103180d95107009180036841d64202400c0c413512a18040d1881404110340c2d0a01070243d80119035150000948014803800041c05450f000030340c852096007141e07000000800042103060399240070203588 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269240998 1250 269239748 269239753
    0x131407020a0c0f0e1302030709021201030606050402030f0103060c05070f0807051c14090406080d081801200702040e06180105090a05070b07030e0d0b07020c0d110f01021510050102 79
    0x41d01c40600c200c0310401e50140c50300742403044000c2407405c0742084181144610060440b40416160150b000c284c0e0001d415005031010000700600420149009500152109803000c6081d0310705a48010303c144418800a0902684c0c0d24024501034410011070324034580000340300180c03000170702e0186410fa200000680341030194560403000e0042c4180642c4500503140ea61900c10f5441c0c04440b204e941c003001543d0740c091b81d03400d000201e0070001c0c46941c241494a41756004a883c25000d2071726220310010300c1d0045039140401400c001140f45e810b40b6100881e0282043d101c48140c80490010604a011758499100b45030812030101c4010140700c041038030347c900a022075202d501d6115034918130400000d2a40d04107134030903c014460280908291400303442c01858440f200c0000c904060000352003616074002030810080420303010025000c0c45003081c0c51300c40ca00032003600c0d628090803e84c1c1610307208180b5072045401c0c076031081100741d5000f08000700304552070601140700b44c4140014030a580c00360 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269242248 1250 269240998 269241023
    0x6030c0d05150901051003021201090b1903080a050705160305062a0f0307120903030f2d0e120c06010e0f160f090803070f0c0b04080309131407020a 65
    0x901d40412001144501900300f00c40c036424201003004004040041c0300c02c069080c8450394104000303400300342c020300e00c207800040d020f00860140f00c20000058072030a044000c140003040010940c80c101c07628a109454a580c0300c4d0401d02d06682010084040c01c0c1200960710008000c0c0840030400c10b000b01c0000c00400c038658000941003196640380c25458180c00420300c04d52203405c40441c01564000f2181c035000411050710126041102c541d070100340c0000e41d4810b221020310b18980716400540d66601810403024000902d1800c1e9000000d5290000780d40307400321f200642c0d008000180d801c00c1d01e0000c9039262903411080c50340d110f02c244100010f0050b1900864488601188201d010f1840303030210020b0b06491040c1640c44252502c609000c00284007800104204140040e1031424403466181e505d03100a802c1c25000c01e511504502946c6004010401200800004480d010001580d072100b4940701c0720b000800401e0309142101081400c0300821a00660202e443c1251038410400c49514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269243498 1250 269242248 269242261
    0x10c17010807030b0a020d0b090103050c01020723150c071205060c04030b04030804050a0b040311060601050a0f0c020a03060603050d030f0902060d0e16150e0d0305031306020906030c0d05 82
    0x4902d2540b00107000c030b00c05100481d200c5c4225400030040c81544482c00700b941c40c8000041181420240d00584964200e402542880e60b0b0511658009180e0701112600c003100864603021071070000e290b007500c1810550040c54000010905981c440e91198081d20100d566030801d9094440710340c4011a014080e03540050207045a040546081e81e800081d01545e1740d44c2c564003aa48074002610940721842581c0d0401c00040c81c1c40d0303076184503d00c42c0c1c1e40e034841102109038482c80e06001a0190307040c07040600c4590140e95000b22099200c044610301503603034416500106000c0100d6801c0034041c90304101022090280004000714003102c280e07820444c200d00d000c10301c4200d80301e400c1e00079800b141c108101111558690081c484504828082d18082c1a903101083d401803521f900c101c0030441803071110107040e42c000c0126103e020041d2500302041d6015680100a448002d01100c03102d042c0c2429141404013a9043d945046405040e580c1c0c2d1b824011240801e641180d2000a162030400001684 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269244604 1106 269243498 269243503
    0xf07051b03030c0c190308161112190216120218250203030105150a09080d0305010906140d03030b010509061305010801050904030509040506040b03010c170108 70
    0xe4031340303070314103c1d40c24075010210700400e07103034a898000003107038000711210b5011403001c0001440368181c14058030142040e00ca0030606100d65001d81d12a400500001d050400f10a04601480c001400040341d55022110745858040b0206000304155840500981841e51000b4161000b1107112401c00030544022204a404c6074040785805a014414011048061100d840030314515810280820703403201e01c201440da03044100140d000e02d003506c41d81c2c00a014010710f8040d200701c2d1299401c01005020700380a0404030031b14101e400240302400907010052014064242e2003e081a81c030203800600da403a01490600c03c0030000000d0b90b0341c42c00d0080001100d00c50000d03500d241000001051100160401405141c0c0c200501c000b00360018150b45008900f01c401140558440000c54090241e11155642640c203150784070900c43c1c0c01000386611181100c0001481fa81e90b03008003036 = true := by decide +kernel

theorem cover : BRFrame.Cov 269064748 269244604 := by
  have h0 := BRFrame.cov_init 269064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269064748 ≤ n) (h2 : n < 269244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
