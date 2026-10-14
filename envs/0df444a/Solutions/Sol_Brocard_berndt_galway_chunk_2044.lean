-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:31:17.875669+00:00
-- url     : https://prove2.me/submissions/b40c44a0-89e4-4e52-81ca-4a602945405f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367446043 ≤ n < 367625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367447293 1250 367446043 367446061
    0xd062d1a1603080106110a0503090f04020903060c0a090e0f01060e010203070b010e010f0b09060403140a0609060203040204050601030905060705130e250503070504120213091a072c0a080d030203 85
    0x1400080e15806e641c0405000008503100000341c82c0e00003c211134002c42044075202007806801500c11540d018071514080c0440c5070f8020340a02907008207550380500c6903940e02c1c04000d8803401a40e400501080c1500180420b41c07044a080d0041e200c1801202d28010700c0307588114100209900c4400e40005000c01485400d100e0914007005002400b5068100909000040c03405d119620006000d1365000c45a0300700c1000510211200a07009881008010f40368101341000c0d500480d400c0388517a14110020703280d036019120f50080c5980040003018241c1d2150000e45140e8040558280e21500c4418001146982c0c20001c5110b4421021444c18052084d0a06000c880c842c000510601105200300500158084151000c644000d480d04420b2403843c0003041d039000d504100e652105041403000d40500001a01d0505085a800c5e480709107561002022034610381408820042016418000d43c44580502c241600094000341000360181d52841c42c9894003031152255008a0340100800c1840f11b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367448543 1250 367447293 367447307
    0x160605150102150604110f18010302180d06020c0f0109060b0102060415054302060613111b151b070b070903080d062d1a1603080106 58
    0x119030041010000050080041e403140c00d401860000c19442100003521a51036800408100d84031309034040c3d0362103500848100aa104480d012002d2481460840036035120707100b119410034030b0300400d18030003070004204210000d9016040d00c203c1d03020301c8101c400c030509101482021111000018898105280c0f020560b0020300169056400c01c1c801c01021a100c2c40010714960700c0e12800084503612103c40121541e0400c05405c40800d0004007140d04510202c0b0b820320aa031080701c4400070b40ca030448200e94507807080b150a80c20038180683c01420820070703041200b45182000c20142813040c00c540840c900310110040f20400d9002d8180403588070b0001c81c0c1c090f00414610030703003801d6840140d01c4e03002e18440c3c80c2004041000d040009070303000344030700c00c04c00c09540d003d4002c5d6030b142146000340000d07080310301901e0381d014100c0e4030741c0f8010542e04502c48031200d0750402e030303403039480c90003070068180101c2c50800606401c0410010b4540e0340380035400244c5601ca03440e81901075051000c014046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367449793 1250 367448543 367448551
    0x501030b0d0302030702010f02160e071e0f0e01050702061809221217100812090a0b0c10050405100b03060f010509060f04020409050105010f02031c180503160605 71
    0x100100741e11400481e07401310896100940a0070042221081006c0032881c0141c484149040790361604004604007550310007080c006c08060b581c503000c0201c0041040c4503091503030490404185080040c0785e02d2030142014030380b90181410b03c18100b03403e903000b0400035444106101c1e901c0d041103c0c0c40920345481414180c05c00c482d20341402d020071694076419001c1040400107801d1140084c000303841c00e4070030381d881000d1005580c2200e0aa041c400406c210381c00c8207000c0c1c010f0074000c442c642200310722190180e50380014010300b9001c403a803601751100116032000007059000d010f440e640c202c41c140c80380900c03030040748104020640a80360200d042d0440300040e01d00c80c40790b04181c0602850318081c01005056440445049005032960000503054598110340b0940190001c00c1c002402101a446035040303440c20b0322104030500302c00740126100d1050a521071100b2540048280c80da24603503000c0714040f1302e100d51015446417151591803654004020300c829038030510b540c800030061030340a5a500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367451043 1250 367449793 367449799
    0x1409010906110c0307110a03061d0714031507200307060c050304030816120e03091c150b040204090e06070f030204120602031e010314210d0b0f1005040501030b 70
    0x1c108041014645905c00c000001c0c1280490901d903450a03a181d11010b4000c6074400010810450a6000c89190303401c0722904484ca40500e40c80080e01022507000a548a90300401810b01c0381c03030349441040114400f50001081108070320090308504489007110f1200c040042c01941c403911645401030a54540b9079500b0200722081c014000001e8224126030f400c100c103500c7d05ca400ca0811081202c0c41400140b48412150910901d01580c5d400440180074a410564441d420682c0000c112050720240c0600140805031204004068403000e80c404000c80318000d0004d45080d6841c02158261240102d203913049400000600060a0f0007004401060300942010f40c1071034901410285e40001d1000090701803a0000001400d500d120003607003c06483e41c00701c10038256124100701900c41100c8110000520400342c00021600801c0c5820070801540324042e4134041810380c1e40e40103050f034040c0b45908207007400b24401c0140d40d680329208800c2c000395035203901d91380b6000c0010240c1f6203102074540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367452293 1250 367451043 367451047
    0xc0c01060e0a0e0706050901052115040609060e060d0c0321080a06080c13060e0108010603140f0705011d040c03020903190c0603020f0c0a05010b040e010c08040312140901090611 78
    0x1c00c260704141601c0f070151090801c1c80d16111130380110b49548803840402410154204200000342f030b280c02070b100750302005907000c01c202501d41d01d140007202d02d41d024484a05081c0c03070020356180740a1009140c0d051040d8543c10980303580b69030314134003412071150b1001c480d055607940c3c0180d590300c242903683c080c0c900360003840309a19201c00e9503101c0d5403403000b041c001c4032035030640c03214103078280c0007480201400321400101e0340c2d4801915000b4045030000700d030306504030b206111403403000003505048800100e01401002c4d16003001942d0320b004010180b16a8200801e50001595851180d80c4140e200b90f02c016070703140b04000c201402c1010a01c031403900d2500c0540700b100801c01e0190220b0603580d01d030900603a02c45032402c1c0000d85008100f0904214811682c0c2c4504002040d00540c000f414141da06102425424421a080e111a524007a0000350ba5600003408a442a0301c9003458882c00304001484210a8416100d108004c54031042d00303070b4640916504015541c4070b802034400e1580c2d81c980c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367453543 1250 367452293 367452299
    0x3080a0b09040308040b0a02041a040e160e130e01021b0d0f0207090c0530063c04230703060b0f130b03011202010801090e0a0b0c0c01060e0a0e07 64
    0xc4c10921000e0005840c2a52002c005011a2550390485000c1c0c240100b009260344114007000410ba4018010003085d005400c000ca011446a40c58854110a0a03261021052040300c00d10031084420907821141035120801c01800c1142803004103000400c81070040c0c415149030315100e2600c12020107482c20000742902c82103000b071b404101c400595000507070108140c19003081c210b8240c09621070a9003e0300402403002200e070061541108c41c95170782c11002c0d1240d510502040425002d4518182c20701c4503103059a41481c4090001c10005d0304090480c000c1d08140c0d4000c1812030720002c4c0c1802d44c10803410f1401d0800420000a0343e8030910300d142c280b1041e403d1656100e8980908200e050030042d003c100c400e43e1021202c4d03040c1c080e114000020b5100d42e90780688280c0400200707020f9002c0b48048002150502c028000c441c0d00905600040c0009001a6142090180c000300244a41e0806006561940d08203014680c01400c10800c0b610041c200300c10380c2401c480c50f0039041100350384641020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367454793 1250 367453543 367453547
    0x130b0301081509070b190801050d030e060706200702030105010b03092a03030a0530070f030f020315011403060a14010c060c02100b0307030803130812010303080a0b090403 75
    0x101102000c0400b904260f01d40c0300340d0364505100341d0410039150002060359032804000b80305012480080f6900c00c0d015036682d00603c0b03058410000060002940e03800f0310310080c10102c000700142441180300040383d004540c801038414007007004484440341c000070000254a001d000c0ea0380900000c510031803850a01030001a601e001d5984088944142031040c20700d41662803240c81f40b480e0000e020390307588540b40c45004000d0f52120701d201200220340103c800c44001440424450480c19070702c1e9142949400304240c0300418640a4a0109902e401c1940440182c5002460203688441c601d5807a2801c01390003d00701c1d02011074450305510381401085403903513902036100c040301d1010040340071200c01000101c410902c9050064100740c104000c4548880d400104d50300c07000c9100104211022000c8105038459040d44130180c5400030500c08611003807014080d2903078076889801554909881a0b10341c80c18000268010303404100b100040005008090054001d07d04084410b0401780c40c0c01d41d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367456043 1250 367454793 367454803
    0x106080c0d0605070c0b0708012310080c0f0f032a09130b030a050a020a081f0209010203090306090703171c0b0f1504080d0503060a0303030c020c0d08130b030108 71
    0x1400d040c0e01c80c00410b5040340118460b00c5c500d0b800c020141c9143c81c3c52200130301000070a10500354218a1000056545002c01c01281c685481c02018540c1c80c5007002d004417202d000c0039100105804007003000300c0c10100ba0000508890240c514802c0e102d181000070300e048034080303840c42c1e51001c205600c28908d03940d10808a60140004980384500d0078080e40d01d10700203004a03001c05030144a1181c080040c00b2f4000f40d20340c100e5100300e6882040540340c1a0300c0b6191003218860076240340141c00e50304000411600548602030341841180e0a0003403120000c3c0c50000213441c2d0300625040701000b8000e02041d501e107640000204c0140a14180303901c003004150420100114400c19600d40360340001d582c403111440440c00c4024050040141d4401c4121000e034024800c0b40b560348a590b0048903118061403d480c41040d004060398840d61454409401401c00f41c0040030842c0a2081090110754a600b074803680507004000450315090721905010b0070300c009400866490600b400100215100058 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367457293 1250 367456043 367456069
    0x51f030305070516031109070509011205040f020a0b0a090605070309140a0b0c072402060415021207050d180b13020f0901031a010e04080405210a03050c0106080c 71
    0x90240d0362100c107403c042d03080c4901101181075003550410008140004001000748510048451100799200d160007038030b0b5807241c04015408070b56083c00c0b607482d00890303902c120fa00a02070a40c0740e0182d4056800140c0e1012640c20208143d0000300b80390389070b0741e07021100202070441c600f4070501c0d04560b501e001c0c0c8044007600c072b201d20085200c1c0d01c00050740c0310464800024000d0410180c1c458008408040e02c607032140c09054aa9602c20303c5044140303038000000d07110b00070300b0340160505840d66240c406200301030086c2841d140d90200070a4440070840b014a500c1014581c1da60354179010714007031210070355059040b04104000c0c40080140400d204410080d04901c25905c0030407124294404101814660741d00360343c0c0004010000070030300c8030100c990701c4179286181c1c0c81201c45c0c0c1c136007a031411003000a87e005400c5910900051103681131004034060000071800f02d00c0c00d60564046007d107032512a82c800c0b0b000810110342040c1002d024000d800141c450b10000d0704805519401160b44042c01e45 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367458543 1250 367457293 367457297
    0x30a0f08101802090613081b22050402061b0705120f070504050601020f0106120b010e0129041e030209091b062805031b0f0a081012060f051f0303 64
    0x1508001680d9101c11241c4000c81c3e06d4880c0001d55032078510b207444145049080d4088203003204184507030b00c0d0440c501c048803900c0080310f0340440d110581ea5401003e00902c1240c00160810040e19200059240340314010090002040d103141030806026914480301e680300380962045c103448480031000b084202c20b50340141da0000d9540d03100130040740b6140c541c0071701124951074990007088409a4125014906004070040405a640c586d046012000c09205010007622110110342e070100d41030180c2c120788000c034101c250801d43c50300849122800d44401200501002000c01c0045041000c02c9a0b40140300380082c200801c039003030001522001c0e40360400d200b11800280040c000440c00d40950700540030f004541140c0e1811036016040c0c2e130084e9400c0b075000d030210354134004a21408084845145803015800e003030008200c020f0b500400003524034003000d04240c1e0046060480c1d40c001c42c0d5450b016400101c4c0c2d188108080b0011034001138111044028411088440b1111603d02802200e6140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367459793 1250 367458543 367458547
    0xc02030d0e01090f060513080d02120913050a0509010b0102011b1404091404050c0f0d020906031f140610080c13050901090603050c0a180e070503030a0f08101802 71
    0x1040049600d000706800080c00b202c3c4d4200c001c5180c81e40304000d440000e448400e61800d40703444d1404140d41d9882e0294180c010fa11001c00d9a030b101e1031050150001aa0180500400a0b80310380d00c0d03030641d402244d00045039030341c442c200640324100740504030170080d081c0001c000d01c2115038621440c0325854401c110034841c0c8907035507200c000001d400300c0b0f0040003c80710800284841d114481c44100d42650280d07100d10030400304888900d0003400c01441408028207208084006078284240c0820042241d503050241c1d002204842d000c080c1e02500d0341034000000113014074240840030038602e002e0300c0d0a00a07813501d600c21000507001a034080d0401c00c0c003000e85c1d88520bc040c0305500d0842007070f0002500304034620000104489c0941003030b420341303114900340c445c01c0c0300380828000030942d20301c16001020213111601c2c03607145460f481004841c00c1c86068a40d500d0322075012a1440d44084501030000d80600d401e404202da07c80360858019011411002c0ca15180c109040801da002080510b68540c2c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 367461043 1250 367459793 367459817
    0x9010501030e0309030d030b0306090102120106030506030a020307030507050118050f0418060c050403140312010513022115090f040b15210601050d0c09020a0306030c0b030a0c0c02030d 81
    0x1040040d038041d0310700242102c1d46d29414845c010060500c03007158074000d02c1401d001c103803c2c01060094920b800030040314060aa0301e0840120091b190280039103400d4010301881e400561000d10410000c2d50250004050042c03501c800102019150100040d550351000d40c1802643e0303900602040d04078088802113034503070740000941040450005d009258600d445070040e5204e4200c07000c1d1007181e0041d00c2070680480c40c21101510780c4200e40c1401d140700828070043c403c40ca480150f070004d0020440c40141002e000c041c014007284142a071407405000305404000111010920711908000c094074085864189204550850000a4030080014841100054a2141c80140c0c0c0030140002049402000182290b000098444128202c05401820000308950902524000305140d204e2400104c1e07505e400b601400135003041c0000780030903444c1c450002c0825500300c40d4a02030210a500c565803810119406021100300c841448140880f07040d80c0070143e0380105071103d0803106424200f0120b12 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 367462293 1250 367461043 367461071
    0x2120a0504030b07051c0f050708010305210c1009120e010804030c05120a0e03012004030f14070b042405161104050a061a040e04030f03020d020409090302011503020901050103 77
    0x40d428249071101250304486c07040300c0c10360488040711800c0c41080044c0d8440060803503824500b400007a2841c1e015001541044100101c03078000d5100ca60062818074050490040c02c2c11340680f130713440343d1b2500d0300b40c0e83d002e01504a42c0004581110704010b070000e0390240010700b01840040003c5c0600c14801600e01c18084c050012081402c0380d441220756890450308003030100709a0b001054000d600c6d06c445103070401480f031090410000b501880c0e609180ca103035184d110f89144581c04644070400030221420841c41042a000504181034595486c2c82c200802441d000101146941484524003043c1d212a03410904440144000c85da030052450010300703000300450708440d03036a90441d250804102604145910074019210251b80d151100034082580d20a01d0249000d0a91a40004000705000034010700c01c03030707095640904001d810103e007500664200e0308903034400307014992071f8820101015420b1092000c1030818000940c011400c5070041980400140030712814169603205c40c507030840c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 367463543 1250 367462293 367462297
    0x110a1421031005240409020d0f0c050405060a0c0b04120f09050d021302190302130812030a02130b070c060f020f0c04200d020a030c0c050c010f0507050609070602120a0504030b0705 79
    0xd0481c80d920b1b6660030707250f4000e5204125103010285041d1030760400d54524001c0740d81402c0c9036a606030516041c64204016580105544418003901c101c2d40c2c40081c1990341044d220300c0c040c44010764034008100024140c0c3c00e240240304200140f5104c180625510f8200002c10550155824810400d007410450002c3c403030000710444030036004402c4142c465142d00203128050010b50fa01d024035590711010303540d65082006402c0c0c0c2c00c0c0c080c400585901040c0d806000201c0c001c1007814036496580791607440c00d510101058884465501050014a030082201c86441e2a144000c0c0103050044a4940e181e40c1d140310447e115a4a0309000d07002c000d8000600d4068074800c0d00c03410b56520440425000a50000207904046811700014580ea680541d10000086404c200500700c940c0d89a8011140c0622203040300e014000b00b03010351b00c00f01e0400c10501384038211a10041c654181840c40c040d2908900075806400d2000c02c1011100442e40002174800b120f511480174072051b03c800205032401c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 367464793 1250 367463543 367463599
    0x30b07120f05010807080d0c060b030109020a060f030c170402010c050f1006050f0f090406022805090103060f080709021e0a0206150405010b0307110a1421031005 71
    0x140c1c100340d210320649000b940030074100c40e100421181c00030781c0e03540c0c015211084070b1000030110303440c590f404000c240030390001c58044500400000f0350b03884660002e11040700310382003940094041c03005041445d80510810000b40300074140700c81c40418084540541650040c4001e0400082200c00010014108490396008102c142910b0403a4140c10701d1100602440c452584204504141c02074107040280101000c01c0300503080b06515511901d5a101a60256944030350398000c81622402c1c1c28040101d1011007a41070b85d48a5031401c0860004060303565039000b6408601449108002d12400014001304881d281c0d0000358a503caa568918582a032880745642c0403840000d00030455603021030301921422803540382100ca491510140300807680240282000048104041703260103001d140d84003d9000f40404503104960903a80e00c8034201081c0c0b0012545e9840440300754801e850600f58083d03e0085200170714223511300010348104110b2a441414090300c04000420300d0050f2904004a40b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 367466043 1250 367464793 367464827
    0x1c050d090c1512020310032004020f07020306090105160309020312030124080601021002090d1b050111030903061b0c15100801022b0b210f07030c030b07 67
    0xc656990b407608210400345000d103000038800d44110100c10390340d100343c900602110210740b407010b0842e034442480c400780c420310340c0c55540403140304a400c0d80e490004080c40e000c0406582d480d0241e92050510f0080054144103440e4182410064031542058848003202140d15002c1040000c50000c0f900341141802d81809010000001280c00d4110246c2c801d440319210744d008442c0c1d100c00c0400c0340c030381074280d400d41c0c0143c200d5240c030044c00400b500542210750780104035011700788059807840f050800d07050f004000c00d01c01041c01c104560300804004920803450000c1c0d4580160b9500194403928010140c00806403448400036280940e44280ca00c00041c200894035000030308030341c240340750800b143c003102d0400c111030003c91011011300a440340503144c4480034036004030307450820181c84510100421140da440308504029a600442c1024548820b0440d032244440b41c00458203046d130323906403403a09622042081001411400100c400c0342d0304258290b81e5600c8040007143e404001242e1404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 367467293 1250 367466043 367466063
    0x8060423060306100305030a03151806082a06130503060c030417090612060f1e0a0f0b03070503040f0b070806090106020607120f0902120313081c050d09 67
    0x1180e81010340003240104011001c490007959041c0c0c03000b950f10b0f6240002012500280030504455000741c01000702001851540301d201c40c1c43d440c0a0302d1072102c2e1f440e1210340700e440c1c04041040c80c03001e000d08a0306200d80105000170000302c070003403100310001106845c0038150000c1c1480b0b6500c0d0200e4104042c1c50000c068401d1810300c3c3d400c01159400c19281903410001e00f100c2c05503a50202c408450f84c001001d0655420000b040d00501075007440100a580c104695001c1105159908855401e040220b85080c414200c00d90060100c0401c0c1d540005c40c0e104510b15040c0002211401070700d80c06800c0e4a03080390382c0d42d40c40c507211048040350300d0010007240f4010700b0300104030b800c00350032403060340c06071100b44060b0b81c1d412007207a44410a55860021504944d582d204407043c3d904440706c0b103030880c04081000003441d4089900c1c0d00e400700e2594120340010940591503c05a000b000040080800800c0702c45504049101c81406110401080c810300044183c005c140340d4103c40c01a98022035400c7c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 367468543 1250 367467293 367467341
    0x30822060512010f0509070c02030c0907170a090c0b0a030204030c0e0f0a05160c14120307230904052208030601020c0d0b060108060102030408060a0209130e0d080604 73
    0x341581e0415100c0038401c0d0010800804e002d008007541c2402c880000300301040c0303a22402e07000d0310311a034000000c3c1d8044c01003a070b014a05803540e81d4078034054819540c03460403403040c070956440c03440c1c0040c01858031141444401804150f405141805031207143d0b124541d90072500350284c009110300e920041040f00010300000360074520007030491243e0000b034a0b40240c0d585145a09007160303021104004412619105030500ba03220700b40d00d140c00c030700c507984805075030b1401031500e031130580d4268488401c640004104084541d01c42038803810000358160001c100078112110a400d40100c96226004039554000103203203064411080c0f1085141d81c283c210101940d047c4000c1951080320894003601c20401d140045080060000c03c4964214803403c801d130300c0d60401141c0c0c007100038002034110311040c0008140d007902401603a02400700003000503a0780745036206001580c000c0c5455481000d14048007082850f0b00425504041c0020b8507141e202035a07003070001002008000201140e09020740171318 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 367469793 1250 367468543 367468547
    0x50c12040e06030c0a0312021f050406060e0c0a1b080a020a1205040e060d0f08031302010233061903060f0e19080d140f0417040f03082206 61
    0x30000d403060240c10500780e68511080c1641c40c021500d4440d00241c100d5000c20216400e00c4070184a00900d00c16210a040b9400d000e0020840014441e0a0307141c5c1c810600c4100034407403050000405400755401094503281d00b0010302800790090440c2070190160391416240c010034a0a68840d510141050b1140c0916100958815008030201e0304030001654412006000d07105842c103c0b04c0c00c10755202c4982e03030ba000f481001804201c00b280e41c9003481301244c002613822000386200f01101000d4099400b928000245040c60070000c644100b0124075820001042104ea0003161841d203e138820850303182d05000c110f64000d0745112010202c20b010000c004c00119401484000065007404d10003200c112105c1034030303030030140040c50612805040e40300000e0880750240444940d0032000150308001c12284c0981c0000031603101380020202400c10040003800403101c0802c501054007142414201a1810841549400054a01040420040041011850742e0040c0b2426a0b0f0846801d5956040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 367471043 1250 367469793 367469797
    0x140f0c031213120609030f0207050303040306090501060902030c13050910050d032d02011d0613060906020703050a030c0305091b13060e010f15080f09010e07031202010e0606100f050c12 81
    0x700300d000491f00a8074000d2113100281043c1603503c01006546010301d166034640c01452038580440b05552503520000700c54261f0310141d80300301c40303000301c441d550070408014440d00091030300075501c918500380510144810b502e070302505680003a180340d90690303e80d080c20b5810314148401041c0d40b86481c000c0c05620085c549c0e400e200c020082d0000d00440e280001e0080c00d510920a60744184e40c40480014020b0542c000e0108450b4020040040c1c3c2c2061600d800342643d2100100350003140c00044c0c01200b80d5814400e4410f52a554603040046040003107440382c496407082048251040601010303140343d50703a150b41103100c1010100802c142c1d0b43e00e48004d5050711f000d100340c00c254043d84900065145d96500041c01060750b50380d60548035540c644c50184124800b9100c0c114070b66032002403061108040141da4080e5001e80f4040c0c415080c1b6060003429910340704810031060b04200305000980d2250701c07907228041035904140103520300884084885004403168801e01c1e1003042e01c04031040241d480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 367472293 1250 367471043 367471061
    0x30302040614040b0d050c1306050301030b01051c0312140f4f081809060a0602030403140c0d0c030501150b0913020d09140f0c0312131206 61
    0x440c005481c400031016041c5000c0e5100e00d0b080008100005036117503a450340301c140d1241100f20210704148600381e4040700c01c401078120070049031700080180107008041c003440c0e00424044840c141060600e1000021024660100030305000501d00e42009011450b00100c80c0446458502521440c0030302d0130084940058a01d02c41800d004490b1040d050f00641e01444540103440048140480c601014004945500d0410008070800c1c1c03200400218044007c0c1480c07090f9481c400384403108041044402d00f80906400d00c6046011010840d0130b801100303a80c106d80c0c1003860482d5451410002c107040642d4000107990240741c0007441d00c01c202d418001207081c0c90040c0020096200011416012403e00e40240c00c65140140002c2c60286482d0a01044811a0600c090700f0604144018000e1714000c01c2c0444502c030f150540140c141d0420040440071840c2c800c02004032141c1c81e00820744441002c211192943e000040d03070203c240c032181d00380008103442a00314a400d10681403000c010300c5240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 367473543 1250 367472293 367472297
    0x1290907020102030f070e01090b0301030b10090b0a140f1528081303090801050a0b011103030f040f11030604060e061018020714070602010b0102060a020a090e06060702030a0303020406 81
    0x18010491092051080d02d20416a1004901107525050015115182032070310250411110040100b00c050051003d14000c521400381103100c0c0c141488000c2c0ea00210b5080100190b00d05991806503540e810315a0342102d0001141e40f5a00d10350b800406ca05201c018800c0d500840d01d46100b00c001d40454004040150384041c5601c50704800d000020364891030500c2181c0061050004548040c0388081704014080c80ba040441c507141e85c0f800c0160075281c0440e03804a809035078540c0d011095800010000500c10800041c3d840c519061085a0355110080c1c0042c025205007440d4800b00003030842887c401d504004c04407030b881d00d8180781140241030000c00e00c0105008100c0419008540c091821007540c520045801c82d1980d5807050000941249005541c00451081c0f003c079010030078005040a0b02c04c95001050762020000064078200c1c000d0308a81d42d035441044180c10840e40b108a01058070800085510a0740300c3c1800a400d40c025010042e6050048030000801c051301030380100111740041d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 367474793 1250 367473543 367473559
    0x6010519080c040f0f0e07060e01080c0d0506030304030501051014090603100f090606082b0e1009082505010504030510090f050304030c06090f03030509040e0129 71
    0x90200012140e030389105285481d03000c038500045502e49034002e81a644400346001500c100582c20980c1079a13041150652642c01c00c1724244401d40d401b208070078242c0f1003801c00201d18200700310f40c1400f46c8280703003d4816a540e074201140d001ea40c02d00c01c44000b0b58000009100b20306088480308038400b200d1080c1403514107042001240d034100380700210701c070b02d0000f4007500e4001807184014014000103107650380c4150b82c03030301034174001200d03413203017401800c000d00042c201c2640340f2000940b017405606906619014413031a04200640c060340401030300005072070784071130b8840400c0b098071100a1500301c0f4060780118222420040c001091803802a00c40300c02e00308016644100545441c0300742c0c0006050758010401410318036207142c000d0980540b00704031480420181e500e8241c00d58000d60000c50340c0460940003086056804005140a811070941038401c540c610350700034005100d129038140c0510345038566030729000000c0d07100b0318101050b160110800d140d40d2101202000c00395050906c0b031401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 367476043 1250 367474793 367474819
    0xc03120c040839061812031b0f0a1e06110a05030405070501092102030c092d01060c061508031303021207030c0b13051306060f0212040603020c010603021002060105 72
    0x842c0310f100c038808400b0307015a1500503c99030b0074030f02d084030a80641c0c200c40e4210240c11740d00c20030401044c2c0250714299100070f803841400011300f05134442040c8405d650086201d007011402c144c000c00c100b01000d00480310016074518020003d0075040c7d8048008403004120298030a4002008520bc5c6114405650034170b41c0b02c0006444607001400340c401c0c01c000280c411000700d880d1320078004a403400101190280703180440040e5282104484414000c2250880d100d400e12442414006c40740f80c404410b801d0b58188000201046403001c4060001502c405400c03659480e080c640e10003030510441502da80b1041d03018100064000fa1000f06d00072010003640c031060b61804204035003500c0d88404c8140b0700d82e2074118241d13116002800e8a036039051654000151958810028052031901140c010840030f14002014190b40a40c841c134070159007064180310b100d4000d9204a4042d17508a060040e1540d841803521801444079400003034000d076540d15110001500000d401c0d0480e81c0c100ca2040103da0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 367477293 1250 367476043 367476133
    0xf02030d08040308070f050906160312110906030c070204050c191b110a090507180602152d040606080f030c030a0f170a0c03060602030c03120c0408 65
    0x10100e401070b0000d525203000c1703800244105141041c040c1e40d480c005041120072000101c4640c86000d2207880007080302031442c101034219000007000a0302003020030000010800c0c0980f6489844007451041c81c0010018a210300c2c1c14058481c81500a03208100e6480d295064100c40d50000c0500d40410100304659480300744220b6080b26041c4503403c1c3c070100c104065990310b0b1811410b2481e00e5209002090106d032440407486210722424813a51001c00d0310400810405a507405501b1110454006800d40f220101400c0002600406402c40010341100100c40c407100079403003180035540d001e6054040c0414002c880d0012030540c0c1d0000b040c0d40044403452000345d50b9108184403246136800a2000701000c6c1d0150600c1032884c041c1d41402d0703803500c101d44031038a85140c088504c000790703e58464070103258980c58801c16000d00810b00043d8030b08100c840c801c658a0051002e05c00a009020000444458451041e1002010750504a44180310100c0007101c500c81c101d540500a405911081c0080c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 367478543 1250 367477293 367477307
    0x909051e130201090513090b07120b010c020d151b050c061513020a031401030807060b040c0c08070503070b07230f041401090510030b0312070209060d1a040f02030d 72
    0x540c0c142c5910440034641818011b48203220744d4031442d190341c0c0317030915400700e480c490300035100ea160342d642d802c4140b03414944982110110b1141b20304001ea03403540f80b801602c0d002003d507a12604100140070322030b41045908050150001948003101c80007003944000c5421002511515003100140c0307131182d40c1c0c440301041002140c00495403064000f811a280c20380030b54002d00c400c902d58a40400c04903030358010010040b0083e802110f07401d800003917034828000f4501c244105904111000e1090002c440780003021602d40030005400034000203649000c0280030005c60320201d501c20042d400c07a150800307000d450121003440301c00b12000c07011031015a8012040840b90100400c4038480c0c146400c000020540011480c05141401079401d800310b000e0740c03440c40007000946d1965000c82c80484480504d420510703c040d11441108082c01080010b03518400c02c4c65001c942a600d20b51181854200181290702d40300c200d2000800d80070030b00051004002035130b2261402603044802c101f0101404907165 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 367479793 1250 367478543 367478581
    0x70311060c030403050f040f12021008070503060f060c070303031b080601020318030c030f06090d0e030705010509030a06050c1b0c100f021f0203092b050a0909051e 72
    0x81e030010800100002e0141002d054030182c410382ca0741c1003648840107543c0b101c2c040d800c540b0407129226210003c516010120205407011880c0088a0f800c100300b0103410350201501e143d11035100e00d0190700040d01c820341036402c028404400c0f01c801a6036400d002e401000825000301114158954400c022030148004a0040e2010381c02189820f81c030180c441807940c1c0706554540d06000d201e116140c55035041280e28a0068110040d00040c00c0c07089020b1715000044c0c8400040c025147d1303021000e507801240c014100d50081c00d00c2e0350303035070180f000103400d2002e41000104610300d0320b802d0045002041c03000d00041202c821720f003860344006181160382e403100001c1080d4010342c0c0d540f104903d5441204410009280d5004403a042c44c00e0306503a02070319144411030444c590303003c4104943c6450800c64106d0f0001250708070811080600c82c46602c1008800350501844070005446074441d205503040002024064420052030a2042000544902c02d1865440810180d00815540308504903c0d82c09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 367481043 1250 367479793 367479811
    0x110a03090515070609051006090c090509070215130b010609140d02030102090310020d0b060307020d0e01120f02031504020405210a020d0308010305070803070b06040e2107031106 78
    0x603261914040181d00d0024400e2001d160606101c800000781044c05002c25a603c2071000d808880e0302c101081e03003141c0259104140483c02d00c2095014145c1040030354040d43c1059518021640d51800240d14220544940d41841642d03907041040011305441110452849018001e115986c0c03008221740c0c14121340905403112074050704070100c502d8044580511148041e0015040241510009083c4030700c03410034038500e60700080c014211403140d02c038100400c1411036943e401c6040c14031000f580d0fa00002030070004d000081c8200001c070380c00340c00007405101c0092014058070003200743c1640690002c1d0784100315288201031404043c5000d0090710b043e541b001c3d04540e00c4041030340203410041c0503001c0345034480c0030740e40d46000580c449202d403e1a85000ba1a481c0b50703135146242c031914194250303111a80c00e810902c6420006075070f22070b2540d00403030221404610301c00004101030508240c2030305609100c040032410381c5440c402001402c0c5440c003a450b2005000c02240304c903070315048202e6000390 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 367482293 1250 367481043 367481057
    0x408010c0f0815032a040e010507020c0607050109080d09051603080f220f05120c0906151b061009020f03010e0c13030302010501090f150b0a110319110a03 68
    0x81c49141142d50000c1040f03001302112055008604003214458510b55a90048030801002c080796081030700659003840c0b0b030f0714000c0005103080d160003900d41d03000318500342c441c3c0790014001040c01003d410a0003c40d4002d0758060792100079441d000000d10120b14100c405004600f54204480918810281141c1c2c015400b54501a11801000c860768404240207015a00d410000341d40503000700c8015018048050b44000b0f05800c00c8204940d00208084e984c09070f038030025600d40640c5400b4940c5801039000d4a16807860000904401a98040d44c00520b500d010000c0403403140860000368240140c05500094003629241e45903441a407207490340c120001003042004200742c2100c401d849038082218401d02d4281840103070b0f08180503c01e90700a4005030b44900040c40024402d10500010350b9011908001e68000c2840c1c407034a050140c41007100c1610042680c4202e24000c071665140c2c0d104038000d481d0f4522070300c0071140003a042c40480ca80000d604020a000b010340c005041c050180c0c02d915044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 367483543 1250 367482293 367482301
    0x2031f0e09060c0c0102040906080705030120180409020612150f030a0b0c0712050403050c011e030b150a030e0c03030a080a0207031b081206040605060f030612070b0408010c0f08 78
    0x43c5082d4040030315010999802c1000155918140c0300b0040581034050150204600d003a08250a40cae2581050b0310001c104a4650802414000c2c2201c03254500060360141018028001800611340040d0181d000440080c1b07e0785498425007081e1b104002001c0e04400a414207014082081003100c0ea0700c3d0543c0c0540c2011000c0b90000602903030200407924800e2a012469407003103071903031464a0b16400300e200410103000300001030144401d018020300c0d1100300e4903d06035a58150b030b11154903a9081c0f550305d8801c5120754803035180040d0b00e0310074040300d00d036140740035440180200500014a113490041c0440b44030070b440c01004540350040d280e941d02c0000d48400c02c001c0020340c4900012000c1c020890380c1640e007001c003461940c010324001c014958441030320340c00040500c01d0080c03446100c2c070b11340b038810701c0f859a8500c06e940b40b10000300c455640741e9803290007040030030300e0310424021a44629440010740d062510002c00c25280c0f200001d00c008490300c6816a03086c01c0d100318001c08518120002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 367484793 1250 367483543 367483561
    0x6051e090415060203071202010213030605151203090a080604030e09071701031101080702010e0d05160c03050127020a0314100e01020a020c010c231002031f0e0906 72
    0x60060010014800958103030102d59542d0300030182d620000c09604082030740c40c1440840c60108007004203500081d40741003942400c4070444556400000e003007582e110003043c80340f020b015070b800d0440d4015040f68811181307070701c140740e83c0e800847d100c0c0c1c841e81841c90b0214107802c01041d540d000d070351b0686842c1c11444800082114408000b840c1804000303041f5040b244071441004242c2c0214026a005c02c5e5200102e400142044001404101568105110580900130000e10881c1b80e2095141464a03035070060000303400040c5611002c1c298076441070b008002d028043d48580d010000021030802c9110b02968002c7c40c0d000c03990700c007030f500c83c0c9004010008a40300703071100012420444256170410b00e481001d0300480d1614035050740300c1d079030201d40448944e404010584001c802420700c40c4e460412560b0b0f07080c005007c0b00080300000780c40c0b9400c01004004124595508002520954607032074030202007003010021540700d1085440d11000000e40c0049d901c00c0501411620740030340141d42e64502c079 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 367486043 1250 367484793 367484797
    0x905120a1a07020a0f0f030e1f030c12060b0d051803040303031109270c0c030301140d080c0a020a12080304020d03020f01090c030c1401091403070e01090203060a06051e 74
    0x60020f5005060003034000516145000e640244500319111001e500c908005011340c0d40074071002d01400c1860020400982c5d0206e502c80742520900e004214001103e10858020b210700d06500090b50804201040305608071000d04011040c074081000715540d0700e8400084005d40644142264204100510119120f43c02c603030041141e0540301843c048122002c0345819240243e00c0e40803c60030021496003042114460f50451044030201e401c3c8001044459142d1006200300c0e42041040004048580c58182c00c43c030a03150440e0440313884110300001d990b100c3c0007010007240708a8400300046031450200d1800050190401c00305811955580d013031110504460100398203501c81e445044c19031560902492a034a84a00c0705010410300e1840c1070500b00342d103900102c403030040e1600c03815080d0340c1c00310b00701c012104000d4071148101150001300341800000d0300102003080e468030010804100360f40045000306004d58035450090354030344046440d8019180c0240403030f0114840301501c0c640c4500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 367487293 1250 367486043 367486051
    0x51f03060b0c0d02060702010e031605150c0c060601180308160b070c29040312240305160303020c010e040608010203010e0906010807031e0302010f0c0905120a1a 71
    0x5001800c0c544441c2110026009070325401d103164010f0081c0100386074180451500b1641e1400244001124081241d03241d020300002c5807a40c01d4502c40d0782041c0101000039101481c1c20030700b900e065003858114460702c0d611189821a00f8031461b80402d046501c42d082c0880310000c1d0a025a88242c1942c1c1c805900d03501183c01e40b40780030005400754000c91045d041d1940560015143c44000011501c1e01c16803d464026030480001321420b07442c41050007154826600039414038114265042c000707c03e1380182030342403400e1009031480d1b82001c0d0408040d880502528061011100319802d14036800000d40040e010060041e0056420000c40e940520515000e20300002c1001c00d1640d11280001c6c00ca030000d038012001030002c00217100c030382841030080074054580c01018208042c01d54a406840c0600303441c11413071414601c0c8130842810f100b90b016072000c54290400748205090008010014001070181600c00c1d0f0b6601d60b103602e900000100380304290f50011841207460444882d003850108020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 367488543 1250 367487293 367487297
    0x60c090a030602030c070203071401120204030f2303030a0b121b090703090203030d021e03010326250b0106030b030a060e03040b0d140705311502060a050907051f 71
    0x803080b400166000e111510242030004ac0355404480e1a0303000502c0400c9001d1948100c2d0710400051020401a82c42e0009141e08507590130030300200003c0e0700e000d103140b0b038607060000d0201100784003142038a6040681800d4084468501d5a4a90440c4031384522203511409042c411554503554203040024409500100070f080c00503444d0325a4003c241940e0142500c103080c00d9002a214582010444103400c2100c98581201c0c1150305642d1610f8031448002d0440d40000c0b15480601850000441211031004d507003564031b113082c411405c8150807030221036000c94610029100206800e4428804c506002c0d40017401801440142e844030350040c00104105040740c04108004034900711450014504180103032000140c0c10b42c00704000e0101c0b00017400d10003c010b0208001d181c24a2007c5400012002c000c2a110303107000003034a4024043c0c911740c4551100300b0020807610380d040e0040760300b034414400081e040c089a80e941001e151a006a4010103900c10300c1c403002c00e410800c0b10f0030342c12001e0300c4174 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 367489793 1250 367488543 367488547
    0x30a151502060f0c1605030c070902090d11060d0c120b011e08040206040906060f03150b220906080f07121703100801181b0e1602010612050f060c090a030602030c 71
    0xa40c0760040d00c00c1080130303186c560000611014441c410804000280711081e001c5003050b903031100080b6030b40f00c21240900402e03000741300241c00d507030750380100da07214140c2c40f000f0440f092903094050104480030021840613443c0444012142d4054028002001a110a00110102005000e07682c034800a40140d8000d0414440403400030300b0780c07040d13030045c1c820340c2ca407402c2d600d154040c01401e031400480000e628100c4400c080001c4500034094507120b01c5820710880600500c5000c51441d014240d105e81c0d0309509027100003a1406020030711907002e02100c0c00f9074007403030b0b103c0c1440d1008002e0003030000d040b00d4940d031031079001b5031480000e03540105299110300102d030703a15055982520142e158558660300d06c80710400400641070201c0f5904440d0540030310b9407e1070406040014100105110502c0706203081400d40c0034400e43c00704014014440305840c12100c941403180ea82c13020080340c0341d030340d101b241c0200b0750525a800031788803038010040006c5040780c00e5070350704000b81d04050401000f500c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 367491043 1250 367489793 367489807
    0x10503120714010507030509070803040303080109090201031b03020406110303010b25170913050f07050a09260c0612190b03150702010b040c090306050903040506030a151502060f0c 79
    0x10a016841c018a00d61b03602040c0c1d400d100901508226566101a126a20401c001c10000f500034400e141160541003001900032810b00042e40a003d0a054400c1c1d2035154042c0d400549815902600540b000d50342e03640c9010f00c0c0290300743d41e03910080c040c12140c83d5041c000c03a0a003072554039060300316106c0355480342d4501d02c0b1036075100448440741342070207102e107404120801541000d103021040400600300910007424400003038202041d0180001041010000312890f01c28041c80c0d0341802416401c0140c032003402110018500f01c1c0d6030094402190285088a01c09880c001d8140c95004248010b060003031380b241141c3d00203400205131718907030113510b0300d50b5081c0316070341845412002c00d64000303108580d00d400d41009007150900c034443c0b0b2207289010010014158000080d0303069a034850000550394440206d80d9146009035444982e01c280000100300c0225907581100307850000002c1404105a201d1046400643c001e4860b0401070b4402000500e9045680c0c000326040070001180c02e240c0f00c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 367492293 1250 367491043 367491083
    0xb180c01030920180403021b060702090f040c0f0608090f03130e0405160b03060307060201062d120f0515150d03030605121b0916080a060504021603170105031207 71
    0x44102d1701500541c001b00341c012401540c8010381d03a8810780c00c42d00645072084680c00036041c0000600110300c58600d450006040083c000c0c820350240808022444407540e40d0301000b03200d0981221041818001e42d140e9545020000007034400e0402d60a28904640c1d08220010441c040002c0c426105449104840c07100c001110143c0401780100d02da005960340f80c50750a00d85002e0070742e4484804c581c5407540401c02515201c0b2020560020059410701d00d403280b20364204081d55541091200846400d681c0007044800c100410109100f14280d90020900d41e203c1c8030170034001c48000c00c2d52030380300c80c10a501d46052403070040c98901c00d08000034115103910106400c2d84102805503102d80c401c00b80c0344a01c00307030b030800c5c100b00c510700b201d032805245040c0703042079180000e441c01c0c2001c1c0082d51001c02c1c00010140c100b4070141101070000c6407a03808500d20030303040c150058815000315211661110b1501c07410000141641d0010303008080c440d04000180344030fa0f110010940d5840b00104004803102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 367493543 1250 367492293 367492339
    0x2010909110901050d143c132603040b01080c012102130f08101a010810330e1e0406090f02030103030e12060406050c04030b180c01030920 61
    0x6010003071070387c40c3d100200011011003003820040b0f1002100d88681c121040c10b5118154880258038201c03501c1006071809942d100d4490030071a0501d8104000001e08480d1180a588a42d014425011059036248451500c1d80700105a0701e001510803010309078651f10740c403581034983ca5803500052030140c045401a070003100641100001d442140130400c0002c504000000c0d05c071038074810404c041c008207810b181045000a5060341840790003c00550288271621200c0300411403550409405000d4000e070b8140c0854240e079405003040f484011a40d4284a00000d80e4954409015061000880e042440c1440b0031664141e9110703031541400b1a001c0c407140034520072152600340141e00c0e9415841e011344840031607026140a0481e40300301d02d0484400041c41d0f900982c01000005654440b0311403110750f8403481d04050803101d4090305002c0b440f200d441302d0015000160082d201101c10603001101600c01e020070141044203c42c42e58040303e0301c03031408401003605c001c0c01c6180c0412080d200003004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 367494793 1250 367493543 367493551
    0x1206220513060c090602100921170f040201020a0b04080d1811030102030c0d0207020301021b0f01050606030106121503022101140f010608070e03160302010909110901050d14 76
    0x2010381c0c00380180400c03900e4050750011050900f4400c1d01c582c00d00c1d2000b55140b00c4030100750345683d258500350080c8121003581c080b04079640c403c0320301f0143c811100981450b00100c4001d017400c1200000551030805660514040c1d50305030301410340244c483c0c4480ba0f0300003028200b42c860300c1c400c21518103a0340c0207200300f1413032848081c80d102400d102410300340c07498040b00e07000f18080d074010420003c03003000d060100c03500c9060354200182c6802d030324000b0078028018041e964110582c102c06080d412280003490000108441000380856542d0406001e814042031007200085419959440ca503a012500880f04d1044c084803c0b24003da50b03a0000f80280040030000d02c1c00f041c42042081000c4420300595205401c00700c0141c0aa050124841100d072105100d01002c1084c0580800c841c24400e500c482c42050000f400c49203440969040742c040721641c0d1004a0110380c200c800000c030004a0b014141e800300000c5031071070420061134010759880e48000c0d0702c00152039854000550110b1400e03401401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 367496043 1250 367494793 367494811
    0x90f0d020d1205060f01050d0605090709050418083106080f01060207061e2609010605010c1505070c08040312140711130914030a0e0612062205 63
    0x180c80e00700c4006451034040900005406043c0b20030000f9a071204040034110700428a0302903030704c12400c900c40c0c00070140c2c3e401c000d906c46207110605c0041035103c1e001c0b10070f5640441d000c008050710100002c2c03204404040c01003e8220a0060180d1048103800d0b10940c18104004441403200c1c21148640090f020303005040450b02210a020008080c3d044a5015041c20f0004190b0b5604000010f04030540c0420b454840c4c200a10303003045280d1040c0c844480412813105140710200a01c1600d000301c0000710307404c25081d840c01c14000340940c407950301998503e81203680a506050b1600382030020f414001c0c02c2405111a41d806000040e042d540100025405141504000d40c03030a03000070250440d066502604800910415011900303200c2e019412460455030700c0103942840c42d2680260040e14005031104041c8203140d61134180100090205085070f40d24a04022a203008000d01800707040700d0750840c0e5500c5800109503040040a02002c4100d110b00e45e0185c0040b11020425075200300c0b08555 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 367497293 1250 367496043 367496053
    0x306090b010e0c0f030a14090109050d022a040b090c09152106040b040213140108130305090f0904030e10030608151506030106050315030109020612090f0d02 69
    0x1040c40622225180900b080da1800361550802000e1503806008002c00d41624400000200700c060308a17500c0b103102401c0c180401980c40c60321440e010b000300564002512035018040410f0300c12480481e20040c07540c1a0b81e00012001d40440007c9a1000d181d81c20030f80155554070900c1c86a40d441011503c90200c1c01c051960f9000305500340f050710407100c0340c1c18070113880500144800020b00318882c1d411001080c051140ca0b0344080024000e007030304400f5180c000d440050b040d503c1004a04405081c1c03015090103802c180b841c400111880b403801c58540c25543d0001800c0c0300080c0c0300f0b00c01002e950354020a030003d20010400005d040190540d01240840c400501400702424940c2140c001c610040c2001c00a060ac1c010225440d1304c2c4001d407103940d180404000405144010360340c080d0548018103038580f07944c1c4a24018001d50701c240c5001c0c1700340d85012584505072030b050043d0391788941d014010600345210405c800030800c0000d4586c0500380a83c100c046440c84c1c0c100b120003446099a0700400d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 367498543 1250 367497293 367497311
    0x1305090f100b1606020a0306031b140a0b1611130501061b120c020604080a0803010816050d03080414011a0f0901050a060e011103040909110402030402030a11190306 72
    0x146080e120351089401040030f22050001180d24855580141e402000c0561785a1028004400405864100400c072906000d22040d810740d005200000f501e015515070b801d00d200010800114401610400802c00390400c0080721050650b131107418442d10a0080c0241001d0fa940000c3c002d0810400d80030010b640d5200401409038044420f0044d650010b0303d1100307006580c1c075001902900400702c2000c0c00013020404085440340c02c21140100154410b41d135074443c843c580008254028030900940344580c0b2100d50014a81c010001e089403801000c0700c401441d15075084c0c2c1c07020380040003684d040170030103420749480e1428081e452a102d9a401100822550030040005031032124401500921480e00103001070388039074200d07005540d880d0130001106102e035070049400c8000045d250011380004180068085610781240c91540e20810303c45c0e00c201d174a60284400c80c00122030103907041c2d100d0f824020102c0c044076030250320b0050151a8200c10898000000c030480c925a004940c40c65681c0a11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 367499793 1250 367498543 367498561
    0x1a040501150c1716020a12200307030b040c150801060f0831050d0e0d080c0a0507090606080c0a3903170c0306061210030c0803030a0c020f070b1305090f 67
    0x306c1c0a0300100100c0c103120495616481403c4642c450f0036552401921040d017900e0760100426070066a02052010aa2400d0f1408c0c5000300c210340700d98101046c0c1c011415500900440700079050301e0380c681c1c8000c40d082c0e88040032200711034080c0c156090f280c1e1212500d80c0d0344d40708041c8882070000c4034080030115051403070014500704103c0034003000c000c0d80f00d540c0e42c000d980d040c0e90f180035560030804003030700c0d00301d02400c0504104800f840200b0070b00c610a400034114030f061300320030100c0f0125101d042c0c403035403140090340c520711038200d08000041030b22040c0e008040048026940d185d00c5c2c0c04400001d00c46d0074106000c4000846015408256954070400700d441e5030580740d551049026004505604140e004150345000c0d040030000048041000140d015040d03a41800003541c00004803040980c0d01d05c0c2a545a0344259003a280460034840ca4030200c900018807224583c65020007070a000d45481008002c1d6001800c2d2442c2c040c40311103001800340d43d091086ea008201144a440080c10b1400c1c0b8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 367501043 1250 367499793 367499809
    0xb1e090d08010503010e0706030203060a2402010c020c060403030804110303041706130317040807080d140a1407270e180f0a030309050a050a061a040501150c171602 72
    0x250b8805d0307062181c801548600070a041c03045841c603040140c1c0329140c03032000600c40fa4140d000503a07000180c0c1c401c000030140000c2c41c3c03010050541c00030400300040702c00481c0c490b2020180103070080410001040080e21507050aa07106008049003000c049044d4002402c4da0f0007940900c0c4010b00300801010034010500190342c100c0c80c0507605602e140203940c2c01910b00c50a4a0611040180c104001002c0c0701d543d1040359603150717014000b80d40d590641c51840d8014002c0c50355441c80404800005442c00141d8410200020013140300300c0c0e203a59031080211510340d5400d1009154038581c0910324400b01020050742c02a02c003540d011409440c098000303605980c0840f1100ea81e40e484201c214010200205190740c0c1c0325094500491084803e050091408019410051241c46030051200a21805620401c4841c0f07035421080c440a00304010081600c500307000c9c0c40f40c00c07404404441c0686004c0c0030050b59183c03141d4030411016003284d40d0405179401040343c0310136281500d4401d004610f02050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 367502293 1250 367501043 367501049
    0x90608060402130e0708121201060320090f0303070b040201110303040b07030903090e0a0507030501090207081c0b09070c020117190c0e0d03030608070609080a0b1e090d0801 76
    0x140100e103055000984001c082c00c080d815565514402408013140910003030001c0c0034650201c035158001c520104150f5440090313030240e0200050008107905c3d00ca40150742c0c2503036001c040a590003035050004981d60707201d001c40a50044000d85140c2c40ca44080c00500840c82c05041840603e2402d40005400c00b400024060002e070002c108000c00954018035042e001669031a00096003001c0d0300d016a03444040b030704144010051a01002600c0101e500498440c90309603505101c02c1e41d0703030744c0341c4426401140401007a00005000e506035001030303c0d8052013800304030780b4003146410820012034841c000585030be50002d1789887d446d10555800c1072234103404000d4a01104080d14042d1545600c0b80c94060b541c58805450f084500081442008401c19881006148003088803e03450050010540d40c89a01322034010000300090040c000d40d401310807101800c2c0500b02c4070780c150f69107090301c3c44024095075080c00e01500846506210048851144801c1e0307008200c0c0040c580c10242c8806d20581c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 367503543 1250 367502293 367502309
    0x102070b16020604140c062a0c060a030b150a0215060a0f05060d150f080c0d0203070e04080706020f0a1101050108030a0c0507050418150b180601050c0d0503010906 72
    0x1441010715500299030f0740e1050b0080312443d202200c845005060210300d40c08035038050804100010f1384000004a000751801d41e68044030052803d19009445201900b125940038009100c11140300e030181d00030089a0b0700040000c0030412407003245040300d401180141005a00a855040442030541c178481c1d0010740c01c55007216254544580c81241484a004880c01035001041c0403802c603000c1e4001c0c18030142c004008503041900c445a40100c01030904c55024203114414183c540c900b040e190324400940c026001d40616814080c0301d032001e0b000648115031074141000070b00003051091000d861118001c146042d520701c03d13544000d25201d0306140d5a481645080010407040100004560244c140b0f41040b500503507031750400c50b0810000d580031079041030409038000c411560300d040384a4240d108001c9040d00c0005900d6803000c60388030902d02600007100741d0040440d90b5042010355482007051400e0352804c640142c040e130801e062100f2045c0445d030f0220041c01856054014200503009403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 367504793 1250 367503543 367503571
    0xc0f0f03020310090e03090306010312091208030a020702030304030506070905010905030d0e0112020d05012d1503021b100e06010b1204123501230415090e0102070b 72
    0x100f107005050120341c0308000c1e540c0e58800030650080800c0c8161158460b0080a682e030a60b0b49062084000240765555800120a904080703111600148011b81041c1c02c589040c4c02c40d42d5007542e22000f0340c40240281d034540300901002000030010009140302d1000303607882c0d20385d0a18080000d0480c0441d604003c1c42a00303e211060551a0f00a010300006642480d007800e04000c1c000c02c406c024411002032608090401001003000400c03100c0a8400c10f5603d04a001c40301c40400304071602e1802405103010a07012000da55098502c250042c100070301805498200030304550200b80d1a204403120740c0810340751643d014000942d0140031150042c901c0d61456031600c04150301c00c1c130129500610003480782000c80940c00d40a48280703405801c06025804d80c1c112402c0c0f0034100240d0301d01c2003000d0341101c0a01000800e5040342c41c001080505800000b16a09816501c10400135100c181480403000c040101c0000d0010303101d020b03c40341901214001640daa03004d052410072070f14010004910400300d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 367506043 1250 367504793 367504801
    0x150509010f09030201081603020c0706090314010204030c0e191a0414010503030f0f0c1f0c031401060f0311030a15090507081b0c06240a05060f09130c0f0f030203 71
    0x4400643d02080c0030b010701c0c2009409070400d230000d005041c4280a54450200c0c003240003500f0800c440300740c0380114848441c1000e1100054280c0c460350000800f05030282d00100000c51400056541000710400c4d4100c8881c514100001100d04150800c8003c80350200c0710030050070726109140c6040c011900e0100158100400310307a6034407900a0b43c803500e490020f8500305443c4400162000714164000381c40943ca8079031900743d4814041030540c0f004518084c5442003490091007242c035440608040500e8a038645001a00c11402e038080ca50305150f01ca0051903c1c20070343c00000d500c80d076500c103400150320b80604404000040700b5080700ca03d2030700e0802409203007071700f00c02065803001c805041649480702103254915140941c003201080e40c81488280140384000c05511800b0920400442d51950100e10401040c01c9075849a150003080406c01340001551400007409620405008022284160030068003290304040600c0c0004607151341d505403250340030080d0319000172030303140c10360640c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 367507293 1250 367506043 367506047
    0x608091903032a2309030118031b0201020604080705030d110a1d060d1113030b0103110123090307030b1009140108150a09061b020d0201090309120309150509010f09030201 75
    0x2d8156205101c4034040c1c4d00d00352a84030004122980e60300050000e000c14841000316480d28030314071760200d0204510383c88842c440302e9158001d016450b01640100180c3e120794880c1e180d03660108609980c41d000405c50900d500c60940903040e805800c8810f00390b51307095100b40040c80c10f81050056540901d8080e0001200c5d42e54400b61440d04030404000a0b5080e2004004001d41c41f641c0c0098140c0c0d04101000410f0240e900c0c69641224050b21103034882162802c01180d51500841402941c2c64205400d100e440404002515aa20b80501210b0400d034913a25071103060501100d901310001c48010061062106a000304480041c0c0c2450341640d55041c03c9402d030b210004400403880110030903000540306070468100003401a00410304115421305800007913003810300c15007018054410680900c026502c14458415810f0301542c03940c00301802c050001e130841d24052030640404c54180004a008050807500c0642d880c4607448103942c2d1800c0304005840210036220f6001400110784041001d80d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 367508543 1250 367507293 367507307
    0x61509090105060306060408190314091012020c0a0605060a0801150b0309010b1c2d02150d02210f0103020d121206060e040b190608091903032a 63
    0x3201110440c0d281d50301d0380003003903140c09544d000035050f11401c60000480d500300075102202e940265100b00800bc900301c403134040f902c24640c1094020401c00c0e00c41851612540b140202e01c011a80050700e45a01d80c0802850a54090000e540700c55461090101e5480c20204403402864050020f00200400d06409520800588140004200300100050b11702000390b21204c01c4240060a5a900e688140c0d101c1c0b107140800e031821a01010100c1900e44017450700a408504203075035180d010020480b6030f092100d0f2500e00d503181628207005120300b001041ca14006010075141804004540c1080e40f0b10844048001030f0034860b402043c0303c014005a141c510f00c40f200207412040c5444c141c1022601210001d29518500448500d00440801c0c4954440d40c600c056a004581c00c0c800071200f00300b00901c58446480c84848042c1f810700c02c00c00503000306400f96100d501c06096500300220340000030803204010700d088000030780c0e541c0c60709078036101c00d07070b5143e603504d20204198507031404c0c00c6020b0902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 367509793 1250 367508543 367508549
    0x60609120c1e121524050402180603180d0503221a01030510060801020414090c0403060f140c0a080a0e0c0307091a06120105010c02270615090901 64
    0x9801484100389600c0340c118400401040b842a4552491129003400b40d0302840c0304031800c3c801400d0010344030101a100c1c0100c04006105c221300d40c41540b900041000030340c4528800a40c6440b030101d11102542c1d0707000610300c42c041050444a000b20007c0f4024107099140056100340442841072041c055080c000300000100c07211003440b8246024201b941180c50a102e00c1c40754400030314008070400c03502081180c0b03224580b200070f00031549c48100ca0340c03d03070184e4000c22802403203160b1414401d02c0c01d01e003015004980141c1d180d203801d8a0341c139040256402da26290541688901281c1c01003500e90740410f178011214205070b81000c0400c440205605000f41580e200340f0b4841030954604142070052034209140141290f0805660b542a4405007542d075401c1985503000b00d5501405041c02021554101540d00300514540c1c02d2000554007020049010307a007000c3c1c002440c43c481d106c3e07605040c0068801c520321300704030324000040010044c05521120b0980c40c007030150b00f280c1d03100c1e401d000c0d041d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 367511043 1250 367509793 367509809
    0x71e06080a0b0a05040c020a05070f03050604080a18030c030218060904111302071a01150203071401110406020a0507051c020f0409300f0e0d0212060703060609120c 72
    0x69240d182c00003881000440e0811a405031904001180180e00015043c5070700344101c054880e0143d03141c0c40c1c1708490716544005843c5411807000540041e11031001402c3c2d401e01c03414084403e1602180c061410403080e0402c41c3c00800c22403060041d442d280b110111626144e5070010140e282c8103001c03031320042d00940020440c11803102d030412166209440299001005101151200d4682c201901d15040c10403d8007843c101c1c0000205183c4003040e030404160b401d0703400440c5000803641d10340d000d44410004039400c555862114204404000c3c0040000b08640e5008001028a0342010350900c0651350110384600d00000110140b15411000d200001d50110381c00092009200c000ca00940800c0c08003c2442d210341e18030020888008080c01ca4411a0100d03114050302d03c0641500c0700c1401c2d11074000130402a000909151414203030008a26101503c1d0204200d08205001d00d40802582c1390300c0070a072a0b0506105641d80b1116810043c00c94040040c0d6029140d260780600030a54003031080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 367512293 1250 367511043 367511051
    0x80703051204050a030f020d150212090a110613051306090b0a050a06030b0f0604090903020615061209030d0501090209040b0102281a04050a0b0f04020a170a06020c071e06080a 77
    0x20070342d0741e0348001c20302030b07a000054003803009d042c0c15402009600982208a9a401741d40114845d440001508a0100d81c8031064020b11003005080100b40d80007103084ca03100814030000414161a400c90f003003134038040f1101c0440c80c0c5003041c0004041d200d0142c446805402412010007041d640d403003180d001c80350f00e82000241d821482002c5203540098040040e0401000540024140e003994000c4d02c08074060790a444464440c1d004002d40c512200c0d108a91200c41882003902a05035602c0e0306801024503802c8a1510501d148030a0648000340e011821031503021072105030a08060040c041842c0e424409014410020003c0407031102c16405100200668503c140042294400d40000c480b5600c9100761602c1c078052070400c1d80c440c0d503070108851500c5d100c0080381e0b0004d9007440b06805194000d000440c454108000787e03100c5400d40300d0800c040d1041034030b0f070004a10300744020b26440c44131708083c0140301e0410010314584142d1070090034610400d4402000800e41c484d600c1c9412038040c101c041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 367513543 1250 367512293 367512323
    0x4050f07051c020403050d020706080705040b0a030617010b04051018051503030705030306041d1504030513060c0b01050a061205040c09060b031503010203060109090e16080703051204050a03 83
    0x440d084044110560b4510000d40802444000203583c0d8107203020703031700f142d0a55480d6007048801440544030500858401e01090150510703000c06030100c01c40e1454000354041c0d4031810340d2103000c08400305200c16551504403a46504060042c1e0b6842006c0304910810b80740751800011280100e51610280150783e14045142c440d5414055408440000d003203036103c00c110705100f40c80360300544806101d03515009454160071002c50104500f09040c20103024031414030400040c000b072005100b1010804100550305c1e8505035030b401c540c040d10701651001e1081d100c61034199029101a0441c520900803407400f00152640944200c07021040a0404241c946640c90000c401c0213150300034070740e92030400c0000b2400210b90301c05903100d44101c02c0e644a0681c208402c3c10b00f03c0c841510001d000860720316040c0032410894000100e080300c110b00300c8240b04a030460700020940381d600038800740e1b040040b081050020410803070903401c0000074001d01c2c1920b410001040c1000d02c0c0320090166134002e85007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 367514793 1250 367513543 367513567
    0x19050903180f030109170c010605030105010b192a0204050f0c070321050c0901080a0b0108130c0512010c0f030c1d1306060905010f020a050303010303080603030d020708120604050f0705 81
    0x15400c0305512441010080c2d17804c2001d1ba965400c00442400958600b2200080901c0c0500079541211105001145071005c180140c5103030b800c03684061130038442200d081404803440e0102900c60920f850940d04091103085c41088203845024203421040d1840c4014044d034801054100d4006650504000d04400d2900704030744000044c541d91041c859213008108106034070904010294158241d0f01c01302640c0e20034106104407614038118500003070042000600c00e903140c6007541001da0103100040042039031180042c5107402c040c108600c00d0303511982e0400000f9003000f100e021000d6141010302c20103030010b600030540c45d2050408a80c6020b10721511129071100300364041e00100d01042070100e561103000c0035003140e6462207101d0000702c0004440e8252403000c41e40d104810341c0038001d1807031031340780d80c0381212354810142c07010360f0600080029000c020254030050406611408216032900c0c05102051280d00000b44181e00a034103000802c00d02d42d15008049038007103202d040c100d131556248132803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 367516043 1250 367514793 367514801
    0x7030606060f361e0e010618060e06090303160203060106090b030402100309020d0609020108060117011422060e13050a0201181d04120e01051c0b040519050903180f0301 74
    0x222131131111380400051a4610032040b104150b481c0c8226035220303a60303141c40841d002c800d1540607074a011400c0f0014402a0b20601c604c000c5000d004200034140b060b018002820750380251740c4005a2508910404114201880400d00424941c1000140305281c51240b842c5403100810092188000164851400d80258015403925070090f140311040801480c00380e00a104004050380410964000101c156200700f106850340c40b02948544066441d101c0251110300b000700e40c10398005204544000100315040389007504030140c00010401500d090070110340c0d900041d101040380455540b0078004100e001401406039a420b10f89090a05022244240706a8040e0012034803800a029407410944a255200740a14003900d8424905240e0003000c0d10001c1e0902c0c101400709806100c86283e00c880011008140c22004102103000448003001404560045036250038048008a401680501a10a103548403050000440c034087c4500c001c00460030910310312511481404440ca451500d085d08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 367517293 1250 367516043 367516049
    0x30a090b011e091109010c0206040522150b032202040507020a030e0f010806130905060c03180a02031905100507020f060708040803190e07030606060f36 67
    0x1400380034550719800350140030282c400c0c0c01030300c02c5110030002c94240b10703d200e82c42000f05041e00c040d25100c030610054500e119044820382c2d10203002d120005480d11040501c0c4c8441813200380c0b03502419603024003e000c4408440c2c20b100c800030003000502c2075400d1001103d0b085142c0c0a40c086048075182e40c0d0904211103508001d40280c02c0006008406800040311128a4401c0e21100c10880c00304041c04843c14071400c60a002802d0350011822504001030000021801e00305e010803051b96070746400345040f1041c0c42c0d180720150000700b044074414051050020031149400a4224007603103400190f950740d10244410283c0c503083c0c410304100802000000e0041d120314030140050b281c1660069118074004214000c140508000641a140701c0d0b50301307511881c1d00807141410350300c070740503d01482040c0c2c03460021040d9840c0e4007902c1f036080803c0b45100540c070460340400e199050210013416080342d80c1c6c0304002c0c0102d20004035003014008525407802200c00161040c402040101c82c402c482c3c4940c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 367518543 1250 367517293 367517303
    0xc0a050c010e0d08061c050a170c060112031e0818031e091809060c071505100317131703040e0403080402031b0607060b01030e070b040f05010e010f05030a09 69
    0xc02d43d000442d00500000d00c5400f0803201c2d41c0c4080c0740240300c01c1c4065042c250080c01d54011200e4000026004100e00a07249800d0145504005260018614252003030300400d00c41c05c0d0313044a1400b0107902925080007600555036081e03c1160041c4041c08015000d05510380345a40c0ea0402c0c042d2010030001c0c2c0708c050668842c004e0003412010301e03150450b4408110300e4040c030b403410305282d50b444612000c0d42c0509541402010642e03543c81e029115034109003000c031444c0b084e141f0380e0140e40d0414020380303019034040b55815140f54514a414201e810310304c40300d075405030018080c0800040030210140c044814694007a24000110021f030350130f500c200d400c8560b030300c0c04000501007070540c491000c03480765201750100c803030303601501d040c2c400e4a40120208a6008030f04103d98000160325400100b48240e0606010840340c2440d01c0c001d0901c100c5030040b81c01e0b04000300d0b0030001d48260480700401060203003013142d60070780103a00081549203100b52140c28040000040b030f241451a90122810075048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 367519793 1250 367518543 367518553
    0x610020c0627041e02180907050a030b1009030b090102070506090a110d08090f18130b06040b0a06050f0c160305010b010e131503061817030c0a050c010e 67
    0x75080000b400141080d9411450254003a450b5041c1800d200fa19400640a00540214590100040003941c000c00500c01c0054840004503125110b100b000c80c0522a251511a2906803200c00141100c051a20040c81641e2060000ca030540d080b01c405800d49801205081c03441d6503c20915002e44585900208035115003800c00c048180041848000726200c1c1402884200a204c204610415202000341a540c030411925006203403080402c000482c0142c000c2142d50415440050200000c680c0740302071100c0a141c5504001500d40100d42c020402c9400f00003103107440021806688003405904140000045d030440590500d505135054540c4620444107801c5280450215101d030500c021242507090841c0c6040641c01220010100301c0c0192000c50034920310079420020304984448031920b040302c1200030011658601410541d402012500c00f000e1115150005000c0e40c071103c00c08008000f4400e1160310003020301140c4859145150258460f01000c00d2a4010b28400e85044c5c560b00c50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 367521043 1250 367519793 367519807
    0xa0611030c031602010801170601060e040902120c04110708040308030408070501150518160e0a180b18040305030604050403030b03030c070611010218130b06041403061b030610020c06 80
    0x158000f440015072003aa40c0003160b036621680e244c054000040380c10450f42061006100080c40b801310892a0f440042012403a4881030f00800d01c064210782d110345a94100e40341c80d00c91414540201091342003154902d40ca000c8070360310b5021060245000003040100000086024010040c1c183c4262a030000000c01442081060304402031540307108042c080d01d1010300440e8010340b5180c109100d2000d000340c0b85400502520100c0d0040030b0a407183d0740c0302010200c0400d9004c0485e003103095407682e2040006111841404000303a52245401c401411030320320b8200400641d0110540c0e0300a8019240411701e80c5079480c00340e01500400001c241c00d07100200d428019000d000402000305c031201e48802d4040e0003c41c40355801d07031040300746114042458087c49120342c02e003020a068803d00b0480002800303006100012840da206a00c845ca007108001e0148080e440d0034005690050310545042b0b040140c1c4070f611803002d01005090354480d0424022a5028034000d1000f1a200c4130000c04265039000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 367522293 1250 367521043 367521067
    0x81c1116031805031903020708030a180b0717030c0d02071b0f0b2b090c08011112013c09140408220302130e060a06050a0611030c03 58
    0x11261040e8000380c6030000c09002c40c84811014810f440014015181c800800000f245510444aa045085204643c3d000030005018405004407522507528491041c02d210800409040700c0d402c5070011b031100b040610002428020000c50700c2c80301310301c2d2a0716540e031981d441000340100042000c00ba400040c3d070904010502114110321a4100212030100e5101c4094005452940c02404492003003000754082e40b0079021444041514000b50800d050030140d200702094820700d2500703c0f0303001c00220051099150a0040c056003040d0101d015040c00440c040c0b0341e40c4c1403818031402c0010002030a9000c8003100c1c20100c0c003850f80c3e007105507002c2101c0651503513810742481e200302c07102603191018988460712040345460055400401c02c03402e0100c102d54400442042001e08000103160050000060b1078240d820030031061b8406c00001d0410112a0300d03070030706000904500c0e031117240a505015556441d803800d41602c0386e516000003079081050300c031407440c0306040034205244400300c1c40180401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 367523543 1250 367522293 367522327
    0xc23091503061c05190804050a0f03170c0a02010e040b09101a0301050f121c020312010503030c0a03080a021e0a030608061618050904051513081c11 65
    0x141c0d07440c860000012400e0618102180f001425604a8001c1191140c40d651040c0c540038000c3c03c003503180680d110002040b00b8183d510100d2403051a0608000380200c5500303020007810078085582c81c0c103461400207500c52140c0c2c41300905201d80c3d54480c00c1e00c2c2e1140c0d80039246044010b00503200d50f04100303420200c0c805d028424150700d02c40c1d4500c0e004410b8940000c2e030b8101c4401800c03140404074040c0810002401c02816500244240058030304d43e80036290100900c50619005155660040020501d80f00703030503000a07000303610400448009050020b200314460b50103107440d880c982c0300c5480c00c0002e44220ba50b5181c5090208080c800c0300003401b40207041d88201c0d5241045804c2d42c0c1ea001d1500c1d8401101c005610050280c0e06103070060290007140c800e00e180300000142c09848900241a800c000e8400f59007a502203030b25002d10030b2504520580140c6800030044504900b030746d40c000306114901103607880303141402c19204034a11030340110542c03210314070394140c541c0c0811034440108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 367524793 1250 367523543 367523551
    0x1e090204240504050603010e030a05030702150c1204111009080105011202011205090307021002010b010807020c03030a110a020307030b07020c0109050f0603041502040f030c090c23091503 82
    0x29072070007503150034803500d20682004215440608250311481e100800008007001013415826548441105450041c00d00051500c4c2015845154503030600030002858055505040c1c0340c1070f010a01445081e40c20f2800b5038a8290240101e18600d0b0f0b500d01c0c0005004108401a41e04601028183d80046030844100400c0d100b4400080100761382e540d03400500c0100d90303000680410b8507200c011420209682001d40d2000701681142d18194440d4046650307075640c00009070060351f440c42032800669000c040310780c02405600c020803130300c220200000d85911a09407102e090006540007a00b6106041c4140d4601c0e40c2c0060540e44041d0b920304205118410440b0018010301804101d402c0c45d40c01100e000c0155000038041c51503a110701e4052103042c0d840035009640512140410882610b000d00080c1301a10480c0d0014008074507500e001d204020490300444811810400020f585035880043c1e2408040c00300c204000d0740010b840d0b980d509200707019000307402c044400b042030394000f140702c011405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 367526043 1250 367524793 367524799
    0x6020d110303060a0b0703140a0806090601030615181e030b090a0c060302070816060e010614130b0d050703030503010e18060c0306010e0d0c03020f061e0304061e0902 73
    0xd24031800030345840780300c200e600650141d468602401100c86100140c4039441c441e050000f5442c40161031803d043c2c05c02c00658001403c100100422401c02c4001c2503080350080c00c0900100d41080e10b04003210700501c1102007005060803c40c410b012220300400001c00c5e414040c0c4011001c041e8502001c000309000940744040b070000030400c3c01e040081c200b5100e9070030a080024550400303c007200a94014075065480042c144640942d20603c03d1419141502c204800681c2400d0070f0421402e6403c076038070826881e0262920b00f8440d031680010001e07800a4040300140751590300300020581282203101070020b10038900003008154115000390b050301d6030312015060568070414400c21001b000101c0315000d42000000c910001c8041c0090350b080b80050400e031903a45510008555001250075082e1207045082c4810001c0d802e1540a0480300300083c0c1e410f5240c20700c140c044800401c0c0c02881d1076541038001000900b44801c0ba03108421291000e8a56a1200a0036054030064003004a040c2d01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 367527293 1250 367526043 367526057
    0x6090912021b2709070e0601050403032f06091b0f01020d1206090c020615040b0603070f030f14150109180e0307060e07060e060405010c0b04060b0a06020d 68
    0x10240740005841000c0000000a0401d01c46a6409006540c00400c0c541c414050090750304005200900d126180314a0302900101030310340c0303003844184500c403000e0a000e051100420041c80030130760107000100c40c200c107010100030741c1039890318105007250441d0102041b40140000d2050214002c5421071054040320300e007110140b1078004119070340340354400c410701503031292800d110203d0103090103010425903a40c0004d881c6076140c0c41ca00c240c076140c500b01001604000200700410000901ea19224042550100405200e410101d00284000fa009905001590540100032031107030704400c40404c016042404440d01008204581c2002034800c4040b241d042449180f0f1541700d10100d42c2141e003003504450800d80310100c80740080084401d02c04640c00104480703030114800e40688401d69401000030030265151003801802146610940c62007000c0400c4204016a8440a5151203640140702c02c0b1980d1140e142400003004039018258100c441c0d40c000252440c1c001c03425060a00d20703919229 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 367528543 1250 367527293 367527323
    0x30c050d03020a1205090c06040f0905090318011101020d020f19020a0201050405100c0503070515010b040302030a06051306060605041d040215031308120402040b092e0306060909 78
    0x1030243e00680080c1c100040c0190354502a828031074020503008000c40080d900f018801e0804a41941e00a40101d021a540e0a00c02c010211003446510307803103503100c0007a60400e6601d035501004c0b2400d404c101410050341c0b0580d0744d131b07011003941240c000c06240c240c2155100b1794076140103082d4100d264040d10642c0b429600c4e049081c0040341803208079a05965040c81e00c2d003044104009035071422210810030030038651400004104000400a03a8052401085110082820034621a005030410310405100303000400c01a100041c41101042e40a48081080d561300c071300e12340182c020000c015004034104600000e801360098020001d407102c4011954016003a040f012a20840030380740290032065210310840030400640103181c110040c2d085203110106181c036440036907042403640c00b0306a10143c045c1b0045103801d128462000405031a102c605140c052080c1f1241e000c42d00c80c00e0341101001d45180c2070100c40c0402c4001955011008001e001c0c4c03160b2001c0c2c0102101c0c10b0403140c2e810361031000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 367529793 1250 367528543 367528547
    0x1110c01120e0a0f1b05060c0718023a110702090703020906040806011e03030806040f02090303070605040204060b0403120c230d120606050d1e09030c050d 68
    0x1408450006841e0300d80d0090105403030000915459542a1043c014141e1400c00185040b11444c9064058428000803000c1c071036400d900c40f01c00754000352045901308840235040f030011616a084442e10035440030f001c51352601480207072284080c4080c004140c418058844000b000100c40c640c09a14a940121910002c0040c00c4808500c50038154003014402a001494000c0340d40d944a040d624000d814582d460300460304541054000305e0b030750b40202d030042c4014030503900c144001400c402081c2a07500d25548001d404604007405103070280e502d0b10150300c084501a0103c030703150803001d8116661a2018107103200200030640d41244035904040c80024444003010507901900d80010740380c88450004241610001b103081c03011902401c4000010450890514014022418200140c8502c0a070401c0083c400e030102056203ca4074030305041407003840c1d07208054581201f1000400a4030201000c00c0d07800e990740000010f507096040011007020141d00c2000841406d10440443e94803c0f850030003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 367531043 1250 367529793 367529803
    0x102060702210f030405030301150815010c05070503030a051b0c181305030d0203060f09150111031201080d1205010602060a1d010f0b0102070509090706050703090b0403110111 77
    0x15100142e0018262451940c054002c1c0e541c41e010b00c0c0d07112807401d03040c80c00e4003080b508111402c3d03805070404001049a03640f105010300346c1c2081454000550300d0070740010b10f00c981c0014640c3d410402002c1045041000410500018100040c200c0740c649000c03100050065015850401c041e142c26080341030880c60000703145c0805070300108480b50720781c51901012440ea0300105401c450243d030021070800301ea01403004041c2103808600141e920b02d0500140440e00e440d4407546800750741c00d24100076004c5090f41c010301741d070203007440c01551050150304418030314042c20a51100c081d025600005032110005a042d400044544034080c00501c821300c0541100c02c2407040c070f00541c00072400035512010b10b5008003c1210ba00100c0c40014004401640c21581c40411003000c80e55184d455070395075a0100061401014102c03164065881d00e40c034455180d0700d00f480740c0c00500c030000c594172b01094003038541040035146115074991295602c2c00c01601644204c0c842502090114102407512000811 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 367532293 1250 367531043 367531051
    0x9150a030c0507050a0605130c0303020d03050f060a1a0702060301120c0611030307050d020d0c0e0915030c0f010207030b09060a0f060602061906050d080309010f0504050d110c0924010206 82
    0x5410b1700e44a80e22010098540100403010354040c00d003418001880b50440300c400f641c044d9000f09240c111010014045410281104201d1102c8030100000d95035109030080070381e420700260b41c3e0b08000021143c0043c0c081c014000707501034070200000c20000d401031441ca1100d03000301100380c026641d03080240c403010031000d004082c0d03400410000d2200d50192005200c02121004014a89120940c1b014101c4035890011000a001d41d00525020b1506500440d006403001504081d40344603400003e039620352811b140c501591076003801c440281e00902c150001140c0102c7e05000c0c038545000e185d900c9440455410310158038050300a0001a101c1c8200c8040c4c038100e4000b4111500d6051a1f41201000701000700b1105407031701c1000c140354450560400e10f480c8610341050b00ca05014000070b003500c40c2c0710101591185420304201c0440c00006d03100400803800d0601c14400e411442d606801c0c0041004010f8000d44210b061200125101666101403040c4140300d41450340b100c001242c448506407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 367533543 1250 367532293 367532303
    0x4200a09020c1f05040c2706060e040c030b0319020402070f03020d02010c020c0a0512070f0f0807050d03051c0e06041415040b0a2304061d070509190209150a030c0507 73
    0x802c00b40704007200e882000c0c0c011f040740091f5403040803d40451a080e40c1480c1c1210b0300042050161103c1400c050250f0394403003280d07060a11000d90f9000c0481e56a040e07425201a40c07001c404104800c0d5103c0d5412281e107242c0100000840501604000e5a50038510911a00540c42c0c0b4811095071480400c0c070011042006000c010348a14240421003000c9040a00c64090b0003110800140341641200e9400240849841565450714000c01c444c01d15019a002501941f030003480d020002e5488411100344200351800318043c0d42551300a000200044904594144940414002400403040034903005c407104101b210004070038407404c100c6a100a032070080460030b41e80e003c1040100c40c3e4200c207003142400350360b40d4041401c0304d0b805034040c502a20241c92541c2e850822084d508941800000b020554500034403e10b13107800046aa418802400312100d524030103003540b07141186404403041d20400034020a00f00e5440c1700084810790040700e500011074a031400341d040c0302d4060000e170780380a5084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 367534793 1250 367533543 367533563
    0x1407080123030f06010602010515010521070903140601091b0206010501080c130b0405030706020f0307150e0109110a050102010606120b0a081507020d050304200a09020c1f0504 77
    0x818442040340781c0304060940c10b02030340080f8001d03540c00b04a494006c001075400402c060404005151800400301e541c541002410400f00c0e01503046c4051b9070112030280c0c407041c403003603540000c01c0b070303600303296800080008085424415071f0600015800c1e041c1c2c0d41c038000070421004503050744422594800c4000c000368220400400407903005c0d03118a54022150000c503403400049600402074151150420000650007080c180301c030303040800c48100a064640000c020040042620fa030fa28054110003c00d503608103685500051080d82015041598100080c803005000b440c0603c40c008100303003338500454411000281c04e601c140210412192b0301d03201d07417049503044440748000d8140b07060010f07007080c407803940000c000004100c03403440300010300410a2203080c01d40c402403c214620a0680800c2400e100b40004964150b40340c0c8580c54902c4540f51028000001040512000707a01c00d98550303201113444400030001266881d08601d682051003490007480c107005044400940d40500f0580340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 367536043 1250 367534793 367534829
    0x3060f100806100908192d2a140102151303110c0d0503070c1e06050d0f0501080f0601050411040e0c0d0207030c05010b1005030c0d0f020406020114070801 68
    0x1d009140041e001e24102d9030f0359440307207000342c5010100c00002c0700e03c858a618900034041d2000042811090856920029001012080d50704101594001e08980c010701c1d41c503403003214801c10200c450070b042e000010301c00c2d560f21509c14625600b028802d0160080c101d6942002803c20440c51140e0a00022111307400030640707040f900201d541c8880202d034400c1e01c00d031796020b80da858003014805104400840c2d1b900d1540c640070a046190341e226041c2c40d0b80080b03001140307490050100c4180c0c1c950380340540e00c8112051a01002e041c00d8009448140d1401001044504021580d00f81000c200030407146e850340d03120184004c840861085031241002400248010800142c0484d00405c400c0061420078100006a0040f43d0040388228040b0b03003030104640c2048000e01400d2041d8400b202c40c050807001c642030141191000404040140000182c02582d200c85940850640d0144080440d201da4581c51b02074000c2800315030205041030340c1d000245039544240511816540300c5008070380410b017 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 367537293 1250 367536043 367536049
    0x140a11040915090510170c03030702060702010516050c0312040515091807030b13200918011517010602030a0c0602040e0a090b060102030c19050c130203060f100806 72
    0x15001c1c42d40d520305540b4080028490420b014003401002e03001c4040d154540b825036600c1c100d1081c401d0a03841030700708080d03042c490340c1d0100a858030300e901500c0c221f0f44da581d90310040b242c9104102c80452011f1101c031840003401800179901011100c141d0071a00805002460124523010301d110311a442064070240c44600041c03100a8035070740601815480c0c0c2c04015441e40810050211520000a40c0d9401d114140d880d040300300322204190f02c00300700500c0d01c403820700910220422401c0c12114900007480f81881c0c0301e000b05000401c0c08043d04081d55611030030708a40500b0314000c020001500c01c0707603d449845040400c6412203c8640095142c003903820801d031000090560155001c079405d00000074800c81300a022882906031070030004401d161890911103c400161803e81154024020148204d03000940907000b52400c0213160000d210500c1e0403450004e4290940d41c11403c900e641941c0f824441c1c0145020344d104640b14089118402e00b1b01c1072100c140440140050104004503510741 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 367538543 1250 367537293 367537301
    0x1e0c0f01090b1c150b07030804171c05010e01050102071203051332130203151018050904020105070605180f0d0905061e0a21140a110409 60
    0x1000604101440d030b03030740d0405424550802c3c1e03110b410300c0000c0700e650034008282d445601d4200c4c4508803480301c802c0c10710840401c4c5004642e802070521a0201c045000d1003030081c250301d500c2030171007032550384c0d035061203010b40e40400d508068240702c2d8282000070802c104110041030581d03406a000300140c0d483d218440403900d01c1004254140a400c00c400814101c12443e26070142019903805015021034003100d400d81a40f5448012824803845043c006954078801c1e152001c464010340503032a9101d0080445c0c02c9461060b142d13900c048140c8c3c9000110b500174070500c0d503a51542841c401e1459480060000740705003120002c9c00201c08000501c00200a980b042c1c0c0c0050520691303020b0180039841d000d25017426141e1104459000010170b84016610101c42406040240d5149043c00003107100309240750014690028103e40201c0d251901500c18201c64540b4181c0d895403004441109807104010000c070b00e0301c1801032544074001005803585d80030b0008e950719041006450a0315240c0350350b00030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367539793 1250 367538543 367538569
    0xe060103120c030c050106120212060f150a1509150f0f0804031b050f0f0102160b061c1203240501030b0105070605010306050906100e040602071406040507081e0c 71
    0x304c000399144501080c0248900c6001d800480e901151050302c50040054011600c1c484420a0b48008104660f00300d00ba41c00942052240001c2c2440e41d2410002030303009140780d004188001300c154401002d455000010408540000d040107851560640c0d04449a1084854480100310106451040907204400132680903019160402e00600d08181c011071400045c60240c030113038059450504e08650601c801c00315800e00d030008520f03141c00b07d5001f01c140054440054001c10388040042c0103900d40b1030081129401d2498100654903103490304a071807003010212800003a02c0c15528a0341c20b100d85120018124a60740d420f00d13158a0f160045016018143c5910f041001c00c5c007070a400581d1501646010f948120008943c515083e26440c0c903220000f842416107031000c03841003180030000c500c030b940c2164111801507503e03201800c000c03040c040840035503100c5100306403c200030b0100100e8208242d54107001951000c04003041d0101c01a40c102043c00c61a802c406031010191034092148405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367541043 1250 367539793 367539797
    0xf0a030c0f050f06040302060612060a0c020c031903020714130f110d0209120607120f0213120302100b0307090506192423031005060409060303030e060103120c03 71
    0x8680324a50b0b40504101e0f540c400602caa60000042c0010542c0602200c0c0c1d002c13100341c402c20302440140034529550f00c1d010348a80e1003170341c0d2070030031840d5184240450403ca40024084481044000b040d0808052003400281d005006e04800822001500d140107241608020a480c2d04210700c0300d2290300510b80c5085d507903000c580d00c3c5071582c51440c40e400a000035841c901d90041c0c40381c82c1c00701401441c541c0c02175000b206400c040c003080321003900001c80d880c1150383c4500018600e42c0c4400782100034032460f12400170341e02030300000003805040191140080e510941c243e0700320f048951601c1041c0e03802d200c00580d140e0080c11003400710240c981c1c0200e6000500030842c4030394075031004140702c0c0d80c20356810109010079043c1e103025410b904c0140c0070000304044d16000d0201552911410682c032950070110081d18800804600070852900002e00034003002000e05503101d039901d140400511903480200e0100381810110480300c1d00128070300d41200e42080d214140012850030444a03130f0760b80030080307003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367542293 1250 367541043 367541063
    0x6050c07090c05040317042d03080d0501150e011d19030f02011409030601140d02040606020c13090206040504110408150f0f040317100801050f0a0e0f0a030c 69
    0x781c007040340d0050320300080039a220b0395651130850a000ba50b00080c03e0107448001c800300400c1041d003041c12100f0710315405040c01001d2000038941d5040310300d4810f51014100c880d0119141080360901d500c403604960703008282c4400c5141403581502c40c180000783d4540031640c544480038034550000710030103840c20001c4c000d1064040b520201045000c25800a5650102001c0b4079011560003242041c0c22226841d200ca01309000306002940e503410501881d685103002011204458481000d200d4400b5402041446107507103c090080d0748081683c080707403140070144015039400c1e8692003840d90064000e000945000d0038281800042c02030103981c00c3e6140010000020404014880403150140011a074096818012546d001c0300740c01400074800100101d05110000750071070094440382103401400300090b92480f551842d1891517034403801c202d50a250800500e00b2800e040b0741d12842042100304940e12040a150341e83e420051a40c0c0020781c80140c00d100841d0090f10841e800512a8000382 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367543543 1250 367542293 367542299
    0xf060504020708070606061d06070215180901141e21010605030114090c010e03100603050123040c12050c04020408011a03010c020c040b040e0a0309030b07080f0106050c07 75
    0x80c0407680080c0c0290f84200c404591601000818040c4000a10140c5001002542038004800c6011340504101c0c1c4905000540d8000310b4860b00150741c10200030b505407035110450060994030400005248607c41d0380200c00106807401c0360100d5510310a00035000d8000504180080511011800300d1541c0c0308440c040040c00c00360400c01a200540c10841c00840e1462900c1c09050946900b44440420900d002d41001410f4400040041402d031003440c144c0f0400d580d00002c00c1c2802c03403000e04003002d6400c08e0300100c24400150400d000000d882440e084810724a2113045664100c1a600101380440c0302908005da02c03d1012105400b0303007d0000d82e40302801d4480001c00700e80c41a801212565180d002701036400d201c5a1140007041e400744c0003804070548200009445910303403041d052141c1d554150102d450713280c0350703c0005d07032121810071550780a08600b4040c0c404525448104d40e44070a071030011b200c103446aa42c5034081c40040304c3d106040d034244041aa52904942c200340300300d209041d000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367544793 1250 367543543 367543549
    0xc0726120a06081f0b03060705070f0201270807050607080a080c04150e01020f011a010f030209100e1201020909070f02150703050601090602011a09100e01140a05031f0f0605 76
    0x2545280210a2a10201004d0b2910582510071113000213200390040700800c021950800c2c1143c0009504c500641000b50a038801a0740510140700d501e00382c14800305030340d000440e48141460540d152641111075965603203040189034410b00303400500a0106105004500d4002c140031030f0041d404145440c20241c8801824100942500d00600010388500e030342259540c040c41030b1815003400d400240320404207249100074541101c00b5043c10001000548915144030741d0603290300b200000c0202541c1c0010b094010151030703822544e07900c140354040038044507030014821255111805450000306559010041d1004000c00c5803c00940c01070003841e031500007162070390600c1441180c4002502c0d0078072000041c22101e59402860542e850180c401030120074542c18014800d00440740100c440d0f0340d401d8a011000f48070781c00baa2200711244000714885110a50405150005584a200d415915810035a0341c6284ca44240c0c1c64072040e203140c590701042071704201c0b403600c04104081400e540da0808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367546043 1250 367544793 367544803
    0x7020a1502090109060206040506070f0c020402040906051c050a080a050c060a0c090f320603190b0d11040903030e0f0304030c080102040806071d090c0726120a0608 72
    0x48984032540020500c40d40d60b044101c400140c0010704c000c041c44d1604d90740f1580d43d0b6030060061018400800c8480c0309140c468082480a80d9000e0820754499540d614120064900c40c000c41d80b059603a864190160f22a0b4a022a42150010001c0c80a580780d82c0310014a58008450769003049010004121a010200021801403903456800281d0015600c00107144001503040750000c52034801040007c0c58505904002820241c1620300c200c6c650100d1a0b4403003440020f1568000c44040200003403060700d501f0790001c00300806004d003c002c0201d010041082003140c00107142401010aa051038206540f21401040c840d0400050f60131042c580545403000240b0301c0e00690380000b4090041004010707a0703000402010009500b4030703040c042456201c2000421700c2c01002841d01c11240004007284c0050031484001d0042203407030410120250160f440305d901507501240080802d0f20488000d02100300180f0302d0310b08541040d410900d4a0079201c0007502000b001e645039000881d20450501c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367547293 1250 367546043 367546073
    0x30d02040e0a0605060a020d032a0908010b01020730060e071a13120503040b0d0b190e070e030c1e24030708090102130303020c040e070f0e07020a 64
    0x1a12032102d182034a400001c1e15000d80045000720001d0204840180c0c001400c2c203258051030501290604908180500c1c8042e45204845140700f50b40300c0700315480c0c214a074041981d05050003400211f81c40c00040e6510600341c070a0740c0041690f110030030340d910111410004184181c0d54056104241030301d42105842c20007021400d5508158000c00c5550712194600098041002d92142068001c0f0740760307003646010303104000b09000001003410402c0b40c1401140d0107000280d00e42a12039004004800041c42107040c49801003281496641c1c2000d40250100110b9054001d90744881d0795480c0d00f1284002828081d0703816201d207224125482d47d88849442442c0d0309000405510700d42c5604200003504800720341c500c942070107840d04030400058000c49500c580e132410601c103240c4402031010b009100c0c10038400d1140c042400044201640481c000d103038008200c034144910491a203096031036219520800c0c00e10f50b162401000400c00b03501c24140d010b81c090065031411541d0f500d0302c45150310505 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367548543 1250 367547293 367547309
    0x2e0803090f1e092206060317070c06030b0d0206030c1201051e041a0d0b01060210180609032a0b0f06030d030510051002210708070b0702030d0204 64
    0x40392045090400514510007014200c42494800021a22969907002c403060340714011208030b40002c2d02060b003000c0300c1100526103a905004c4d0901400c01c0001003900340411110000c4152070906902007007000d0b50b0009400c40c43c80544c0a1800c1c005070001e00140303000c2034008808001c40303c056502c900245104103005401180e980010032400407104205030040c510441034040050a5803d208042e028006815140015514000311440441e4100300340030342c0e40101180e503039404000304440803078100c80054003201d550318070b20740010064640c144003910904025080e01c0001c07800039000711204602070704140040394010100d4000f44415502c0b205054001001e545081211104043e64801d00050003080e941c100310300040c2c1c072007080c14615400c041c0c480700803d6403101d01c0b18404000340710040a01c010034000102c087d45404620714030019002c4018564444241c1c00801c49544030ba121101d10b02d0401250b503a07091851003d00f2640c11440240410740071f0900c1c500c000d0020740310407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367549793 1250 367548543 367548547
    0x6060904111810090e0a03140d0905030909060906010e223615090213020a02010e01050108010b010c03050c010e10021206240702011101110702180f2e0803 68
    0x40c452402102495004c9039040e803800300e06103081040440c981018542c945414690300007084450300c154010001c410001c545481600d2007082400001008040025194125a940c515040001d080d000301c4045020500303224019207a86003000c0080c00400104c2a0b4014842041141a00300e8906c0c3c1844400d500300707014840d1503c2c5000a0000e4207e40300b00440380c82d4581030f602c0d2580d540141e2a1031180341d4a41600c102150384025628000f20103220045466029038003000340a00b0900281101a504e800f0010078285410700901c01034940c1a140c0030344078241d503601103401e5032108015071419540e541c5008289a400d20001550701a092005030700e6001d2a040c2d01c3c007441019109038800e140c250109030760781c454940426001840c0e520040d454000f81d0006807406101102c00c5d43c41075280040341d00e2a40807800251402d076000341c40c0300c82903072a42810012485015540b85140c04040c500113110780704801c68201c41d5001c00700000c00c1c0d01d2413540280b20307040e105400c00c400035040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367551043 1250 367549793 367549801
    0x5070f0507051809070e0901020904051911030c0403080901110d0905040c0e0a06110f0619060b030c09060a0c21080a15031202030405150a020c04050702060609041118 73
    0xb040d044105100b5921443c40310030b0804481c0b4650f140d00c18460404080a114005580c2e0002981511550200078005001c2860600100ea408080000029070440c0c6030103d042813141d442e20641c0c3c03044408028092500b400c503240e909031504064400c60401612400100c1c14030030611006541c900192213034159907052808020603a203481c00500100140784407803141a948000aa400b00d50b0319003015030b0320b5203103544400e04010015034018401e00c15901070007004040320b40342c00d80410701800308112080d207030500d10019100540741041d07080c3d4140030401c02032518200a10321046982003038400301406641d4412940400d480c0140300303090015074140b009400c40d07012a4407801d01c07001080042c8001c1b82c1c007014a039141c00080c040d052a0004440003900030000c0368098140104081d08003a40088103d0180c3c0c0121007081c01800756842590440c18135000e038a000701c1d050f0300500110750b151000d000010744020030641d04140d4031a120300380d548a850641c4c580110080041c3c0345864 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367552293 1250 367551043 367551049
    0x1503030f0712111e01110a0c060b03030306010c08030c070209090102120a200d2d1503150915020c01060602010b0604080601030b190614040515060f0a05070f050705 72
    0x1464155070300030702018060108000da4040756a40c4500400600c0441d94130010790820f0050244030043e00450500082110805030061000040305201300b0701804200010004d0588030f01007641c245001c180140d5502000a02050107075521140c0c1401c8d0324280002500003820a0500340d548a40d03d0f5030004000c083c03a801c0e0100340354417548c01582405114124580305d20b4000c001264510480000300b00304981c460281c010b40d9a98130b203181d0000c2c03080c100241c000820a58074004450303580c40c01000c003010010000b00c0c0700407260070200ca465429041c080c040090801200122040780111401801d1040944050409070411500000c5c039141012000b0307003100e0004c044203110700420301c42040b9407103000515030b055076845044555140c8403499a1511401c1000c41c200d209130820a02164000c901228000e60040485d014802c030f8855071000199144809083c0b9080b040030000d90a407060b110340100400b07451481d16a1a00348607483e10b581070401d0b1201202d89810118040140345 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367553543 1250 367552293 367552313
    0xc131719060603031209020121060504090503030105032406100c0506040b010f0603141609030c080a11011d01110c0a09141e010e15040f0c1d13051503030f07 69
    0x681902e400c0041c1b030345e42d40010f0141000003800c02600d07140e41450303880411164004d40010180540244035443d2a458481d0720f0750001d00956021380324041d08241c1d10034a9002c1e4080c41d00b6142c1064400c0c0d1074401c2800102e5560100220500180b07440e9900000d0081126520440c01460010f280d94103006083c50401030782d50000c420142040907414011001104a40c0c1018101d01700d8040001c1200d41076803003c480d988058009000030200144594000c0744403983ca5104040004901880c1401561641d80441c49201c404000f200c022000b135009010100100c00c40808071020342e030444c000030b0b6804210380c000d41001d0b0785030404807106800c40203046070060284020313142c0131030040014881100c01403043e09620388112001c80c1c2c00501ca0b034010b2a038010702400c2801600f9003101c103400030f080c0b111607100000e034035a0718148101244c20054241604002c00c000c1036130581c4044031010b0107015101140c1e1180185030b0208a9034100014140c151481015984840250030221080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367554793 1250 367553543 367553567
    0x6090b090109060b1005030f0a0b03030301090902130c050904050a180c05030606012307060219020a02090603030901120f0e070305060910050402090112050a0203011508060c13171906060303 83
    0x117105085446101d59044400d582d8400740b400d14002032a41c907001e801010b040c11004654060000000124441c8082c0d0450030080b0f0080e9070000020302d03181aa10104e4a60b04140400030307000344984101c601d001c1d04507580100104002041081b210400340c0351080705441c1c1200c11050a000402907400c040c00110b40c854005d09086105002c0c8803141d03100740d00078804c0c05c40c2800b00010f45000300b2186505403411098003408270103042c0419030000c0c2da10741010a007030744035501140c0051030601d0300000b140c0b01e074401a5183c0007042d0f010007060010f0010b8030781e03036251683c41c1c4440706e20184040003d074000318065002401d45061041150b800c0c0300540034a031840c00d0400f4104009a101c0e8005141140e10500e00006031f2a45030800c2401c000c05500000e5040d401c00d10001c03c90400b030712034441940c1ca40002e41d011a1504406280300e0b2188414810f81c11180d42c008020700c4c5980c203620785900d0080c00c160350001c4558544c2c0d11211680000c1265071a603195018014190710021319180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367556043 1250 367554793 367554799
    0x1060b0a17090619090c120213060503120a02010b1504060908010b0f01050702010522090b03010e210d02040f0e010603022d040305010e07030b0c03041e06090b090109060b 75
    0x35030814071035140d11594014400c403040301d001510795400130f002d503000d13210141d004a01030944c41d0b12240300124070012800c082e4030480c110407035828400200d104072000c80301c0081c002c161280c941c05204080d03410054240c420755603100d020305000d0300c03110f4009610700301820050340e449003002ea01404001e410f40002d18142e151400d011011f465981502d5402042420015140d005070300c0120707428812a0250311312251401d607100344140038600303000142d42c604203040c4450943e640c245400c03a2401071006085603c074803483c040c0341c0d9287e1421700d890f80600c8025490b0141854100d42a68895845140140c44605040201c01c01343c0340c190f405084146001c0d8649206829100e4010901c240c4000e41c81000491061644084a04807002181e0000082c4014409040000c4e21406144015180440803400141c041150003048034803840e88200301c0d048016140805c4100300d1080d480c102d03401a9280400c50103d044550301e68420741e41d8400208041e000c030310345501940c92541c06540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367557293 1250 367556043 367556087
    0x6040212060c031314371511040b070b0a0606140a0305090304080a03030b0f180a020702061303060516030501080c06030a0908070302030a08100b0a0807020a0501060b0a 74
    0x41c2e41c08440003101c1c0c01c03080c8484007114070411403e05915a142c0480e80c2100381c45600c146d5003101c02203580c1c0f28205260b030b45000441003040c1905008a10701403d00800359603002c42004014070403580312049202d031a40c41e550410f40c40b041d4124031584400b0b001c2e101a4500303810400490a207019500c0a445140f5107000c4240c0c02100607505405050070f5441031685610000f90411000c00940d0010891801201c00401c00c506018008240055000780140c07100d90002e030071410f0200c15400c106140000d40b0300f640e92440400002034000c14022039101000308104264600655003075400f450140c0f50002d07060a0a1040d01d03035a1001a102205140c00d1000402045e000480d8030000b0400585200d5541e698101c1803200410030a07500800322080401c60405140c0d00001a240e0a601c43c1c50300f407442c0d1904158a12071007001d102e050501001008454145403141b02090340003e0540102c0d203540c81e0380e666150940d4011f4214914081c0c003c02c0c2184010707845090b0001045150403500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367558543 1250 367557293 367557301
    0x604050d030503151507050105010b0f0703110a080403120206061e100c020301022109012009010e0907030b01020111070f030e01110706031d1605010e060408010e0604021206 76
    0x18828000010007405105000c00080e10030030404181c50b40c00c10006113900c010b9840780201c003031039800c4070000351143d6103080b0002c00c1450b0048210340c0078103000d4604604080c8a950204c03095140a021184103010f101c1c883c80008118101503c05140300d441c1d8040f9003000820001c0c03071b090000706030030310400c0f502c04020071380c9a019025400d22041a034885040d1150070100380e8202500c504029015840010a04030046103c0c001102c01c020f4910500301c503843e20083c65091340d1402400c5a2404030720180b01d1410030000d0000d2068900604021800c00b140000066440034103c4011021075103500110140390703428400d20045050f0740040303a0601c2d0b01900d4400e6214400c06000701031000002c417007030071680205641090100400c00304c403444c50303d07548020f0140481c0740c18420312a00340000203100d08404280050b51186c82c004d0010050b15180044500e8910180482d400000030080412503620078003c582c07490042100400550400b44103000c0b889401030b41c4c1c0c44040e04424144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367559793 1250 367558543 367558549
    0x2a07090c0e0915010908030c011b090305100c030b0d0b070e1509100c020d050703021f021c0302090612011712040603090c05090117010501080d0504091104050306190b060405 76
    0x9180c004410142c40da10f110405001620f24050740c0d0000781c81c034840410894001981500290052040c0b0386004441c00c4c0c0011007526104202e02006000b6040051140d42c1611f15600c14080188145400f046445814001c0ac81c202000d5105032403180b226001c00095940082d40c0003c12501500c901d40e00c0c0280020b5410240584040d076032280c080c00949940140c461604c02e0905e40e001015242d0400030b07850110740d2a241448224040c0c0c0f001c50324403408490422542240c0300954000d800b80440800d9411001d40f1811124400d06909110511303950b2154000703001f40c050027940c0e088065040c400c106818040110007100554040640e0003c00500c207010b40b003c58980c1d0601003040001442c01722082505070f0080ca4220b0f02800c00055004114003a180040c0b200320700030003160f40c030b406c0415110300071800090080340c0204010003108110340e228032038075800011403078149500c4d840040d0606509136415070081101909210015501c2d102d40d00e01008111503c5150614103004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367561043 1250 367559793 367559809
    0xc060906070e010309050109081c0605040c0503131406011d09030403020d03140904090b01030201080603011b0e03120c0f0f0a03211506021006050405040510022a07090c0e 75
    0x280d90400d92179045901c100f003801d4001008082c4e202c42d025446142004101e00c0320802001c5100c9024244200041d66050601c102c0426034401c0c1c0d10f00e46140d8440c540104564401d00044450720015030070803207914000e200c918041d002c0140003400622030502c5014401002608084454208000170801139403840810884541c1c941000504102118010308041c001e010015030400d00700400d00e401c0110b0b245107281602c0c400d0700c406038292038003c1130608803004c65100d0b80d091100d100c202014540211110104200020116041c0b00a440c00d40217030707a00700071002c0d0925801040c481d10004010300c608190080c84034000c2410042e562002050b03445145011854000507900c2c01a030300000360004030341203442c00ca0b440056a541c00c4003c2d40c0d45a20f400c40162145010400726441ca4603004140c05540c0041c010300b8480308001740d8400952082c0c68012101e2021180e1001c60303250004600c045650b44000740200340c2c0b034044010143e070303c401d550342c00700100b4540074200c03940c032081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367562293 1250 367561043 367561067
    0xc17010b0a030c110d083108090f0301022701180902210403080402040501050d08071704030b0c040f0b03010605191103040306060f050303090108070f170901020c06090607 75
    0x42c000c100307040942c5055503500310400707a400710740c09072901c80240c00340c122800d1400f0700e09807030000503106408090300940c1e9500b02c080009a9112a4281002c40c8060005e07001111b0020801e100a640e038900007401c90740701189803904020065140080b1044080c03000215990038280204954642032107801104600e000d03c1c1951030f8041000710011511507081268407129920312002400d09040c09046c040003220700706d20035400c1100100b4107003080f400700ca00d555804119507041c0b40305580c910f0345850084000e1283c5060078040000070a0601c00d405008031441c1e02203079a2182403403c6559460b403603030001d10302d00500b0001003200c0c40d807004c11100c0d0040c000555545000300d48800f11004d0350040003400e02c1c0e00c8049800300c28007005a1005e0110751100480d034034015510703400c1c03544a00078001140d02140d100c0e000114668005c641d000504034585c60b000758ac03002d010281c0103040340242da10f04080d80d40070418094404080040a1300b0070040c100800300d910b800c5200800c052030a071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367563543 1250 367562293 367562297
    0x402060a14130305010212010f1203081305010504030804140a02150a0306091b020c0405060f150424031a0f0607031206081f06061b0221010c17010b0a 66
    0x440300512010340401500e410103540041500d01c0b9030389052450103501f142440080300c0540100010303072441d601e00c1360811240b900da0000880300d02501e080e60340640003008254000c40200c00e10300001d4003840352601c19846134889a103142070604011080100c1450b01600c2c50b803004910b00090794505032001c40d850760300b0700c1072555001c071030700118041c01855010038415414000e0010f1001d01104034a00040c816900f2105002006010042621800d840c01e60f00001c007181a0704103418911051031070705a60a003454580307507031a01202d2809444402d0880e214185050003095554140100301c513003405110b00120b1080c404c07000a21404614524512540c000030f0f00d40101400b50354528400721804400300903081e81d13090303800d80315101a6071a0000803000318003030380070002e68400c4e141602c3e4103585448900613000c90401220300b200e0416a40030744c0c508064050350a8880c0c031441c003e0b08800c000b10b106100540d000d030111208451600b00d4140100050220200f450240d515160707080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367564793 1250 367563543 367563557
    0xb0f130b06060d020d0903031a0411091516030810080f0c01030e0c1509100203040602060105040f02070f060b12150c1e03130b0a0b0d03120b040e0a020a0501080402060a 74
    0x1958424009201792403501510764200301e01001417540590018a8001014100320003065030041000121190200045e102c03c0052100d002e81e4281030382908220300e20005a541707030032040b06540b0000c4840c654110000b80300c2d4410000d03035180000d1250010403403603004041c040040300c9400d445001042035241019a100180051601c0822501d0450034000d0000f0901e0744203c00c245046602c443d0f5002d0141d009912482441480001210111041c41d03016040a909150030413010f4a4641b04d07501c000e513000d00c8000e001c11624071003221404d200c4d01c07000404200880c144242e80411079441d041540000401082034081e00d02c510f0360107144d44480c15680d040c02c0440c0001c05003c06150a0040c07000300070001e040c8a400342e8649043d004110825465644400d18829907800020413900040020510000a0b026061040e521011610040b80c4080308030017140c1261011517a000107944011a404c1c02e41c20721040281c0170305002e282010145c9886d80210b44a4482e0402000400c030179 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367566043 1250 367564793 367564807
    0x30c29070b04060b132a18030f03050f1b0c06041a0f1615061401051c1416080109090f15020c030f030105090f0103020109060e01110a0b0f130b0606 65
    0x21203c403091902c070260700400c510345541100006c2c12520300c6920b4040d00e0318042c0408064050b500c00002c443c0c214024014590440d40c3d0b1090340104004100c081c848203005a11000712403038094071554020b0301140404c041c0c1542100d00e441d82e204000c50054900b00000c0c04207072901d03898a00315076280101d440d59600c51b000d9110322446910040d61a000003164600c0421807444c00000e0042d80340002441000e4460310191f40550500750001e0200300e042100801c54200c130b0382d0828034468a6600080c05903101e460313600c003025003210151640b0000d00400d07241c150b0004c640601400c84920204071920496441003445949848007410b28071843d0080c09600e0380b583c0440780ca021303204050b207480d02d061664211aa410a0040a1050030300e000083d40d00e81401c007a80d41200e4059507080c03800ea14101c5d007a03540202102c0801e0402c14085080800b03076504018103007600b4812654003d8610b8805081482050082c1404d28101d0b003200c07514020a00c552180d5070442800c40740c1d40d54130030b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367567293 1250 367566043 367566049
    0x315030a0c0f0302090a0204080a06050c120f09010e0c0d0219180f05181005061917010605030d1202181801030210030207021c0507030c29070b04060b 66
    0x42403540c014491100e514012070030000021910b8100d81c82034407800403c0d198940a0001e80c06a07020b02c03803d9500c41825980404d00740e40020385c008005002d110720704903803d4110042501d0444016417244040c0707061141a060911508908000c0740e03028101401241d400038602800c1c0600191140c40142410a40b00340c4407000a002000203080c01581ca08150028101074014508070384002440d11001542d0801504024007410510001a0114101c544943d40c01440e0103031020703802c10340c400e5403504007112829956001d030865540d150800700c4d400307000b00c0c00c1d99480c2d04194002e410594505210580005200c405031407500350158540c00c01a4110316040310030040e265000c003c40c9045c114000382524410b043e28000e450307442400c1d800c15419070a074844c2d400c000303400009400c00c0c05c450340303501c1c00100c0070075110f40305540d0002d5594071200f1010f107980c2c001074582e5994000c80740700c003140030b01003210725038001c3e0180d801c00c01191a400300303110009002400154907000c0e02d40c8255 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367568543 1250 367567293 367567303
    0x207120f061b03060f0509060904020d061b0203070212150414011806020a0306050a060905120f150109050609010302131808040906060306170c060f1207030b1f05031503 74
    0x12072010360042c650354480c00030050a4107101d1611410748005002c10a13040446569120341c50240034900c05448030790920054038801e040c2070751842c0e5120108021002e104082010010040c0d00644c0c807100ca900411003040d5441080039150340c050a112180700c0001d000c1030341d105400900348031002007000016409415000300181118011440003400c10456a01600b0744801580d07041203503c0d220800d11010400500034078010503070f140402c0120703280c54400b0b2005c6a00c40300643d400440d06410140c80d0a84a843c2031000c210f890006100c804018821690301000c02c41c2c1800055165401180108200741e000c44049504d403940c0080000d2020030105096501100503a907840d40c0b171a0200050009004120000741012800502e0300203c024203054401d151000d81f02e000000307020020303994483c4c07116031015103003401040001c40c514402e80e4859822510040f82c00b0010b40e04110030070040c8600c1511098054840207265948807040c0c0f80d00c0311006a1100840c100303800000d2400e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367569793 1250 367568543 367568561
    0x616080a1205010b04181e0c0207080d21020412020d0311100501260715090b0c150901150905100b0d0c0e0619030c0c051e0c010207120f06 61
    0x2072401c0500028a00303062000800c201d90308500011181c040d00010801560143c041000e41d941d81101c040b41c0125440d0f0100181c0040385c0104d0319601e5076804018100303551b811072000071401281c4080040045001044410241ca0300c04620303280c01d10300380031907034081e00300c001e405003102050800400d40907900c280d50816000040b10f0f048542030100c5006844240240c03241e500004500441030041c1c80c00085604072004050305640b800d204001c0041c0038002c0c000301c100b110300d01000038001f19880013400290100c070b014284441003a00060000750014120300750903031400c8103003044841c0f40d55900f4187d0700d140c0004649070321485d004803580646904011403160b030000300104035101540c000c03003d0410031344072030080f0140d1204010f05ca006d0103c82d41120342d20035003a11400e5119501c5001c4c0084075080c4410390417480c0d12004d143c1b60340c42c0032a850104031041e5640d14110200f03ca151908000d00c01009140e0421180c03803c1c0d1481d8000c0201501d103241c0c0c1d10070030401650868015 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367571043 1250 367569793 367569827
    0x1b0f0603050a020715050702160302090f090304050901030311070b04060c120201021b060a060b0a0801060e04060306020f030402010e060c03090405060d140601031e0305031909020402041e050616080a 87
    0x28140ca885d04001010144c8105015101d482006441851111403000440e500142504001c0e500d4402c0e00c219014010024103490008020209041c0d5403c04014040e42c040e80e1080380b098002070015150401c19001030400315030a000070071410ba80141e0406981d94050f02005601c481d500040c2d0180c080c50141c4200c0d01c9449500e10151280042c409104540d42031040c04403607036800700300d0441d00c25280b0b204001003038040140101c50046560040390140600000744a99a948440040360003105501c840080d001091009542c0d100404092012044800a107000002003420313a480c4115a030050195031034400040d61603441d001c041c0c4400707804c00255601606100e9000fa2114801d010480c0c81354407168130300704490f90407110440d5440e8151035440c41e50300c0d82c000030004d070085503112072082616411060016241c50000d030000f0710301452071116443c00003031a4540001c8582004c1d014034814007801804d850690903107814103030407045c1c042d0b8070b444410307003280c60f40340702d00034100f07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367572293 1250 367571043 367571063
    0x4060305190b0f1e07020c030d091e0f09090501090803010e18060f0601140918010906090e061f240e010c0b0612010f050f041b0f0603050a0207 63
    0x1da212284454104451188941220a0f0b50301215014031880694446140700461960000d9000c4c2080f45190401e182e8011500c200c031440c0002803a10b00342d107101100040d04d80c501008a0001041c1d59518501845481409541402c4215007841130074410078103101e4403002030bc0301784202940315800303c90300560b1150b038079a15405a2201e00c81d040e505a505410420400c3d25a41c0e80072a00c1c070f0149c545e0700c0d804485903c40030700440c0c56402004070110041000c000089050f43c0e00c8201d0607011a088418207280d41c90080f0342000c44000f540401d00342800e041c200d1121140100700030381d20419022100180c01c02c400395500103203091b500005003880401003240680b90092814040502081d2b4540003418422401108c541030306010013400d0440300400302d443c516110700760449010304100000b443e0040c010000c0140ea000707a0348094480036400600040c44910440c100103c0300e00c0000000d000e1408510321510051481340d60105640c80c03000c0380440c121034040f04c41c11904011400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367573543 1250 367572293 367572313
    0xf0c0609030a09270b0a09050f0a1d100c0c050f010f1805150603010b0d110907211e0c020d090e06010504060c06020408070602060405070b09150904060305 68
    0x10380c1d00c2d80810005404242c00c034000042802c44001d1074545401c01c040051441040110707440e0152010f0b0503103e521191824020610401d94812184949891004044141400a80041124258024094810000325118508010019aaa40e000750302d10000842114000c4111883c04e60640010442c0c092a040c8e0341c07003030205406c402c0000581035002c02c0140d00b210f0340c6010031b02103003100600f160407031880010010038104003d907000c2000b90020541c01d60f0200000c0000049082c2118001e03400e40d80340b0400d041c0080681c1c0e205907241841d8204540c00d20104114021034900450019124105c040441c185002e02081c9107400d01e60500500c10f03c6000a51506016819800010004400050b81100340e0784924010101038650500d0682842c1049070200b00e0384000b50760060302040001071200f002c01ca020020b25059014044034206844c1080c1030115030303441030306d00d1b030014030018803507541d407030030380501d01d114021200d548400e540041005416244d2001c9c1880c01802014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367574793 1250 367573543 367573561
    0x2120c180702010b01051602060d14010b040305070e09071203020f031206041506091809051b011d0a1205101103060a08060112020d021302070303020910020604020310020f0c06 77
    0x1e000e469150002d010883c90340004503400e0007201f00081201000c0136045c405400c10300e0090840400841000c140c08542454244800c5820b03404800091000079040060140a0100101030000440040c1950a000400c140d8492550044204203401d48440104040c02001103a03071002c80c40055a0300e5811120144903412011185180124102400d07a10405a03004202c0e00780c80d40e9845a448540c1410701e80048400e40e00485150542c2d15106000816020006c2c800ca45078041a401e0140c104400014640d400041459035501c00205141c0390580d280b00781d840079a01075001d81c42505226041081c9801c40c02e04407101e419242c54640f01e644620700300150302c10141600e44d000080d940d012403e0b035402c1c0c244203810301150401100001031408041c807211541c0020850030b00c04190750054002c0381e0041d400ac83c0071039800070f005c207a43e0901901e0321003c02c0e21400500980d283c03e40110380ca0b850526070b074260166000405190480911090340c0303e090245c021600c56180003400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367576043 1250 367574793 367574839
    0x525051c05070f0c02090a1802031204091d030406080415050907031e0b060d03030902130501061707050a0806031c180803041a0a0c06051512030301060c02120c 70
    0xc01001405100e580d02445005070044070307200b036000d4801c02c1d4564034051510010035210705140c01d8159231030301c10000341c2d9042041e0f003003201131034050540da0361805030a03808a482424101c0c2d05c0d002c400a0000f62001c010054a044560500b01401580d44501d000707616043e000c8500110a4030384000d02904501c009180c0702640d1045030360403007103026410004484415420002c06240ca030000203400d0341019094420010b1007801d000caa000d0302c0e540000c020780303602c2005e100e1455a0b140100710702c9070300030220041c0500140304042d40c2d0800500040061003484040b82c00e2000c06030108182d038034100100c0309450078000048480003038618004100a000b40300c00a6414a004000b080110021045a0032643e81614585081014602180a607002130100c502403040e4008c00034040341c007500406200c0c10408940210b51180c0104002d18200030542001c9a9802480141710760b03500200c1d81910950100c80c0001d13282c03042c42d080c0d4a0510380c24101904034000c5196441082c2103854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367577293 1250 367576043 367576051
    0x70e04051b0609151b0c060412080904050910050c180f150d020901080c090102190303060f06030e0f01060501050301061803060c020309032b140c06070203130503010525051c05 77
    0x2c1000011104a05e019620f030103140c01e4540c1300404100410011a200f21003403140303842101d03000d05060501c4000707000c46400b04c825405075005540840c000003007600c03542c5d1744100b0615065080c90146405084449000d2248500502d00320703807549516501d400c0c040031040d440458117640c1c0c9036100000710280d0020000e40e40811046804074081542c0301080c2c6418100603030040c1110114500c4103140204030726425401e2564804022070071241c1c40c9805401361100d03450206d40c20a204082501d00070031012880e1031170b4034000080c440b5a03407080c1100c1c1151380f580f0300540c01200190052601482c4c9500c0101020b15003401210026004806814481d07000c40980d920200c00c100c0c2d966403510801c1302004406040c0240c91303002030040b24000c0e001c031041c0a100341008141c0d0401481c000050341c040c0050f90000c02c40c05600700c07000b16030a000d0001030b0001d004030308121180012804400040b064814170003c80c405d04a8401e806880c0c1660184060301c010001c000d081d1001404151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367578543 1250 367577293 367577317
    0x70503010c0509090c070f060203041113020c070603050a060f030b040b2a0f07020d0516061d0f04020708030f06130203070206180c030703030201020c070e04051b060915 74
    0x14401c40342050185003981ca907100040d0000015946450507540c40e644840b01c11101c4004e90300509010405a01c0510f2280d07120745c0c0326140401c2c04404100c0308800007505d000c901801000740394108540810541c00721070240c02d0120b102c0c0c840140340e00160000360410805c00c0030041000080c014074002c400d009034021052005a51036000481e404511001d400d004080340080d604c0c420045450000c02c03100b00c0105046090070781d1a800a40340e02601c280a80700e40d484005203042c1400994401d00c0206070904185040c080e100c5400d44c0b0b55009000e055200d001219091030350b5071100d40454100b0384e80090880c0e0b5902d400d494013812244195440e500840034010314900c03a0340c2c82d02c03c50f406100a50003e1415540790360800603110200c0d07214140501811004a0081e01d0802c2000e01440c0b0980026854008821400d458059160710178a58090420240404038101054400c070b400c00a0301180310031000d10300030821a101d401a00c80e004800340328188411031841004e030040407540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367579793 1250 367578543 367578551
    0x80109050c070231060f0609051e19080d020615100e19060906020f190b090f060702010914070f0510030b031f05100e0c09030f010e0304031202060412050c03070c030507050301 77
    0x655801c55403016140a0345411404880002c280000c2005c410124840010045170340c082e00c44039207442c945cbd01c40d408004158030006101c9502c0f43c0610600b079101d1188031208102c07195a2000400440504440c1c07400d1107049003030403840c1d0f1186201d11112000881c001041d81e60f40305c000074024180c41c480c42c001806900325084001401040140d0907001d503140d90b0704c030b01c1e90b95142c0040e0000094000003241c0310300e5840211244090101610810300c6400015414815003442007403d80041c180700341542065809000c991000380024042e1035054825074400c0801c0c0c42c0c180c0040c40a0000c43da490703c609502e0b850180b40341010110310780e40e10038044c4215150942c01042e01255805107180100e884000910300d500b001e0301621041d03138001c048038000000a03521900b10303042d0840b6007507175410001d814070512900b03108a1100002c248000c103403d1500e40c0310980744401c1030b131600b4104040050314000c2c801041060703c46454000f00064041c81c4e40b4039004c3e41c0c0c2c0c0c3c0c0d144910b501175420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367581043 1250 367579793 367579799
    0xa03020d0f021507030e070806010f050315070f020307061b090e15061305040203040b0f010f0b030408070204270501050a0218040906180b0601080109050c070231060f 73
    0x4a5003024040905580003032031070201d00800d0070260300004240000301031b9918000c0c2c10320001000720000030540c100c0601125410301d461508000311030b4202c00d019502c1034000001684040c0314250780300c840c9190035040036079a108200e08521030070601804030b901b403071030600d0020221131810154400c40c4e11880d402c15510801240114001c0700c0515158407811000141e40c1400350013000e811007141e4004107071a4442000804030b030015a4103036000f0f4804020843c0c801c800c0c400d4640505000c52004e016946020308440e0b051200400c014181580403a11000315121038028040b03007621080343d030105103119100304ca030142e05100e003a5141d6007820f0104110001c81d208032001c2d80c0340241e08440e00c40160f820700c8003401d80c041007240c40d41e41c1c50000542c0c0400c90076070003041ca84106000d00403410900300051401c101a00081009441c00c0c0074403c00800d01002c071422103a055650600c0c203999001d1000918009400302070941103420010031044002da400171060300d01300c014410000352 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367582293 1250 367581043 367581047
    0xf05030a021c0f170402240403060e0604050a06020c030f0a02011407111e1504031d0405070504210b070c1a010305031b0c03030a08010501030c0305160c020d0b090a03020d 75
    0x15000c8095404038403202072454910b50403c044030fa11900187c008511b0818a480d43c544810b11041c41002014001c038051040080741d01802d02e412034001d009042c9401d240c1c40d203544a85107070f100104410360006020003801000d06c10780300000600026070782c45049143c80a4060640d0500e412a4903005000044540f4011185064a0001d1320000c0040300c00c0365102c540300040000754021107124a051185100c8010225148250b1184d922040004621440102d120740c14140702072159003000100280141e01c441560211418a00308031000d40c800500c1d43c1e01c481300e40b80080d16400c461402c110401d074102c1d02d00070040c0d2190007480800d5400c0c11303810304001d60a00008145800403c00200380d07800801050a4038080041030b40c03981c40c1d01d03000091440e404640445c011070081d2004110b15030b0184107450105002d42024440e41c540485070f0002c810480c0003075414882003540c100c0954880048c14407190b544910342003150701342070500f00c0d034519807240304030300510403000034114143c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367583543 1250 367582293 367582307
    0x14183705040f11030a0e0c0405010b0a09080105160c0201051309050115030b1e011107060903030f050702010e04240b07060b1c060b010e0303030f07030b030c1c0f05030a021c 76
    0xc09042140c41c01c0d500c44420180103000f030b0310010700c41b0744900c1a00611a90355480764074000c2802038031030307603860780785401c00350001d59582c0c00040301d03034984400c11003469403250010364a02214680940907014505c0140c4041c000c44101020510503070b1400300d94800c2d41e03803265044c1d0b070000d00c0070300000d40399000442c1034540302c00101c0d17000303a15008070728106842d603020909080c00c1410035051050100d24a240740c4203503503004400140f20b43c0d2003001850780003010355141184501d070042c6072043c00e80002c0c221505107005903005aa0700d802100141691580140040100411201c1950b9803003034210259000007200b640d80a2406c07440079a1480d002204103040180f940040044200300c0e1914802409100d00e0b4605101521800180340e68083c07005603c1540101d04c02035850420240007005c48212156481c0264001900b48805682c1c60b1181890303402e80d910075040c07400b100c0c079103a00d0803000d29500929601c8045501c5545036000f10340511144482c4c0e01c1e8003407900d0460360890b148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367584793 1250 367583543 367583561
    0x105180c0a0b1b1203071d011b08090406030503040503100b09012106021b06010506030c310308070b0606070809041a1c0314183705040f 60
    0x2003000709040140c809480060038600b40a8078440204401440c00e0038101410fa003130503900d6050000410400b41c0c0c200b000620002151101040800f1201001030300500703045416840d03101a40d28040b081040b0300d011101030180103007041c8620b540da850000d56a4005024191003800b0700c01c054071600d00c0318402d003094000000c0940000b6440c200c41e04044500c1217009003403003081307054140d000c02d0b01400102080b04042c815014010803080f041c40c140903040e00014800c120400620a400e51840c0540e0610409010a41410718128106548a00d103d42081481c0a03e40c0d80010502410501406016009142003c1556181001c001080c419990020007004050000d82d55504041c3c0c00050703030000e200101d6290039400f4000920001284d005521040c041006e1a07007019031104400300c020b00f030401c400303007849030782c03c049184e000303032004000d00507818411030112001e220034203140c0c4c0d112092080700010140c07080f501414092030044a014070305003800310b00e4404683c030590f400c1e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367586043 1250 367584793 367584799
    0x60a110405060a02070801090819091802130e0a02041502010e030d0203062205060102011a0a031202100204060207051c0f03030218030f0322060c030813140105180c 72
    0x2400303050900704549500300c0043d00e021031144c24070104581509110b80441c15000701d9401c0e03220303401070b82c00e41003c3c0490084081006800c840810840700584000b405401e260040907071504000203502a0030303002c0354018000c40310504244031107415039600400c2640e489126084100d0700c0035a00fa0300340d8060802425042d8420850040080441d40c095500f1901c010311a098890f51030311100c141c414141c18001185a40e0005c0c02015a0244901d07100e201607000c3e001c00c401d12000c00601500e002d40f00107441c43e070690408210080c400c0c880100d0405017040210740700c5032980f20095030740305903004142c01141e20403100c10348a8900c007182c00d9055408083e40c503508031255802c038043e410844452582800082c400c12480e03405000c04611001c81c03000a5880e243c03074030841941c50081382c28206164a4144040c0140f603401340c4180180c0e5050700705500f181c1c60318401d1201e02140c801c006005144801c134521041d10045d00020b00540c0c43d10120030310045842502c5813103008840300f441e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367587293 1250 367586043 367586047
    0xa0308010e0703060b0304061a031204090b040e0307050106030b06090105091b040b0418050f090a1e08190f03051e060a09050403050a08011e0b0306120d0507020102060a11 75
    0x8816a401c1c1039455008580c2c0c034003c0340305a520055210a44c005840c2160001c3d00e54050320810101c62040203003c41080b00108847d40c1d0b03820091686108a01a0440c0c182d20341c0211201c076103d039040307016890425021265184003030700b0050b0080200e400100c3d030b81139050004c50118903000141c0c0c1e068a50003880c074500e9450303100500b1000c040c11000d45460900501c800110b1046001c090320040c1041c11110300004000c0c0001c0080381e4005001000c09081d0a0038441031420020b00c0c000d00540c44000303901d4061514145004030341e003e140041c0301c13850000f9008419131402803005202411600da40e80e94405a1170150305955040312000d081d2545070742d04840400030010b1554218002508070826652110003203810703239404584c2907000c034100146000801e03a20480c3c0d1401801c0c1e0360301403000d00c000c180310300306248020300c82c01010040100100301c040d070700d8010391111410804101d500c0d000091a000c0d0098009100036030150189400148212555004400d01007810060440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367588543 1250 367587293 367587299
    0x20105030703150e010b1c091703040f061a01020c04050c090d030c0609210201020901021f180c0617151c0507080a0c0914040809032d0601080a030801 66
    0x30000c0003070100c0009004140c0f400021441d6041d00c083c2d02802e422040c542d651703084400c000e802600103008503080640340041003404038001d940c409800b0325110351f12940ea62911709205110312012940940300910b007a000c28405044034006581d402400e07020740f00b1416000d0308000855200712841d895124041080c4105883e16040d020401c0d84a4244551481843d444901c226040b580382161007040c0446280c4001c012911850100d400307034030081d85001034080000f51520401051307601c2407100c116034880e0324a800d4019409204042c820120070741d9440c1050742e4810348030310844012560010101888d01100542140b183c1020381c0f5039a1700081c414140310082c00005800c486101c604044c0100150051056074011f00c001c800a000b003115a0803e00300c0c0c07201d15480055400e15000007000d592180d14240c551040e040040c29440d50083e03c042420b00b0000c0e02d9800c0064000721440c0d102c1034445611b1400008402c0484550740c0e20707600c03175551703035a008070000d000f04240030010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367589793 1250 367588543 367588547
    0x709140a0326191d130b0d05060a0203010303021603030c1707050a060b130204030f140c030715021e0d08100b0a05071b05010512070207030f050a0308150f0111010605031509010b06070201050307 85
    0x81b00a08005088414440c3d004d80383d4605105043d505c1c1590190000010030605038108400a0000804041841041e00d5a5805052400d09803801002183c0c940c0e0b5005408852409552126401c14280c40000841d0710740740c0010b15041214610410340c002802d042e20003984244c3d803c0d26480085000c101f280c68071088080100f01c115502c446c80f4030420000b8a44041c03007000010207640746800484402c1c000082e0410003c001e104810900701102042640700001d10140110200d0411413982c3e1903448550000d0440c41c0c104030042d800006841c0300b03c9900100078002d4a000701c804807010340d909172100700400540e2261a00241090114048141020003055013101c00c50040f24038040da00c2d40c448a9148054000b6140c54100c801c0f488181600110f801d58024580c4a00300e10130f80a00c030000d039180e00d607040c016040000100704040130070003d5003e10090b1800400321242485d072141043c503548811103107007195500301000d0681c0c600341802601e03080c55050311040e08580c0c4031017003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367591043 1250 367589793 367589801
    0x2270f150109061202070602191d010f08040f020907050c0105150901210c0609033513081b0a0605070305030a0b030a060903080709140a0326191d13 65
    0x4e000c40d07240d401c1060300005903252004045140300003800c40025601b41c9400f905142c40034a4080c55917410006030303507190303034003000003040070401e414001c5068595050007144001c181c50001d401ca1840c00030301a110f40c0084c0a44500404840280011307603e03080c80d803c6d0a2084070215401980040040c03040380e9840100c140085500c0c00c108200248607200d038885424a1350215001c034031540c10038014448418006420b289102580e03e4002041d80300301e110044c82990101c5c80800d001c150480541c1410040000814200c011101e04845c01108640d0024280c0358003480340500c0340c0c000640300c0c000c0081d41c0016400d074075018156502c00301054042c082d1002c600d54036000b8071840d01c0c00500c0c41c0c41951895402175032045c080f4a44440f020b052019650841807482500402e0348070940d40c0c5c940d01c00241d0f50320518103003041064040c0e24080c0c04003104101400e58000c01e00035044099203c10000d02052551140e4820208210302c2c0c121041c050036280d005502c1c001101750a40175504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367592293 1250 367591043 367591067
    0x8060406020f0c030d06030b01050402090901091d061e01080a1a0a291207080c1005130b0307120e10090309120b01050a050a081902270f15010906 64
    0x2600c1883c04403605041801e5078000c900301a40703203940f04800e00c14080c0c019005805010190b40c11894400104c00081c0b40c42c20502c01c2810305515000072801c0c3e500907000d65983e21100504407451403c0c0380c0701d00c08a85070b0000d03500410b003203d0000051000d2000030030a103c10b030071840c401020f1820381191401010020700c040406911440700100c4211a40e00550900002041011180447e8000c1007403601e02030004100651019905015101c00411030f2080303101c5c1140d0b0040c1151000200703490078018904030450a43ca5400b001800c1d284260040d032185c84280e0386c4e89100620305051004580c09910001440da2298610400307100c510b80c081c4481a009003464040c02d603540c0c0c1082c40f0342890650407621800c0c50b40040103242042400613001d000112042080181001720f000c2d0389140e5818018180e0030140803210640d00c52548221100560070b04210009030420114401d480e030907a920380c0f000251000295408020401076805030405940c0c08041d1450320300d0403680841005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367593543 1250 367592293 367592317
    0x60d0206220f08010b0406080f0c010c170f040810021809040c0902041217070308040f0c0f0b030403081f050d06180302011e02040506070210030e0a1b08070806040602 73
    0x1000c045006210400180c0080101c20000305243c6017501c1488145d818650010b2035030703031050f401500744120102e00c1b005404401e10f8288144010b50030840114445030220664440002030312840080d40303035000f401600e200f041110304090300c1c281c049040b48034142d114242c4090303c4294000364541100103540042c02007003032186660f2500d19070300880e8401d40c4541d42c590000c440c04000c00131620144103002c1c0b1104409420b207801920064000c0c44024401406501112118002c01000d541504007802401550802c1540c43d401650704543c02603c0c1a03011070306940c00155140400341c0c00c2da55103009098086090351900060007000001d40c0411501652102a094000000b5101c0004454000c0d800882c1c2a1250170012003c0b4251107441024940108424081c1391074640883c1c80851f4199070340545c0c0312440c98101d0042c844426515007500400754800c007401240c1c0401c20f0f100c0910032080e500107644000070343e6201141c3c0b154210300d80085000401240c0982c0c09401403910708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367594793 1250 367593543 367593607
    0x5030313030309210905090103080a050702060d1e060806070e04050a0e0f07030201080106110c011b0b04030905041b080c0a0c12031b0503190f0b0415030b060d0206 72
    0xa56034460041186928200c0d402884c42c05400b0322075106010340c004140680d0010308070350468a84840074802c41c0300c050305004001405c03070b007152900c0c1c00316103440000c00740801c0f2000065010126604410741c1e80c0002c64108003012a13031450124103240a601c5503207515090710b661209120141400504c489030099685108030030b000b209200d2003180201c41c002034403070a400e510000d0149001a0890b1041003140d0407540c1d070341040000c1c0801048401d0030216502c4036141d81c0a006286040001004484800b00340000c050b0010804801d5680480c0d00348411858a05070305444080300d01c1d11070010301d1250200743c18507110300c0100a2a00103107403003400750f03501d52600c0001081c0c4051542c00a9611046443c503200d407d28070710428000e80c42c2552550501e100214580c40794001245801661881117003035951152348590764004000d00140300011085c40c0307020200c5114417007078600d400301a000904038030b0310704054411282e008140a060150a000042803252116040c3d5080440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367596043 1250 367594793 367594811
    0x90d111306030503070218040b1b070c081c1b020108040c1a210610081f080309040f02130e07030e011a03010b03061b0a0302090d111c050303130303 65
    0x2802101d0245010f83c0042d5600d18992051002c100b0b0348603082603a4505180c144000540b41d622140d801c14210300560036403041c206100055445640c01c001e04102c400d0030300203040c0f980420b2641c8404964542003003600c9510906680d13000d48103118101d00654403046400541c0120034240d000350003081c1d01200c1c143c4880303504d100b01190701d09c060a8900080342c0c041146404034030001495150400920007410b000011a0b03040a458104e03005003c03000001076107901022401d10000e0030051800c050311959500a151a07034060700106016a08114443c01418401d000321003031a140100c00e06100e0f40f4102155507481e4001e0081d10030140c4a5250b00c600381e409000b040d40c1c00b5855842072000418840405007111001c01e000c0d07000380c10000070002c6581c519500f0103955680550800e42c1c4410101e41180240b050218840d48000074031001000d00c00d0841c160710340b4442c240c4800c06121241c00c1000c505201d01d180c01015070b4410000180550340200c5040000340c86800c0100716400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367597293 1250 367596043 367596079
    0x40c090e040b010e0108010209010504090504020f04090b0109060b1305012a0602030a0506031507110c030f06040b010503161a0d140402030d1103030a200a020714010302090d11 77
    0xc0240c0e81580d1110025005000705424034040900405203103008603d4101c51000103000c1d030081d4070490f02c92035660800a01991101e00016814180c018010007082c0301c00e140c10b0000305000c0c00740341d8115140402c00308880030004103c401c05c032010074100d0000d0346050011500c130a414070500028911500d60055080d41e498500c504a42c800e0345c0158892501d21403020881d00002d08940c42648181d032620459000c44a4041c0c100c0042d280840c40540345800d1a03181100c02c1034010340601c1090742c140e4518901046a6025510074038220340107076650410113039640a10040d140401d2a02d0b00104481000c0103040841008215465424110080d2080c070880e5541d4844d015110441f0741003004510f018020001000b0b401c3c104040c012480d4040180c0d603000080070820700d03a603980c40803904102c003250018101c900c10b05000c1d58401001800940383c07812441844265151070600a80c2ca41c080e00a0b14040b040c045d02140001c2c039a41c64500e00600f8a180c40d5801c4505001141d461003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367598543 1250 367597293 367597319
    0x3070e070c140c0f040605010806010305060f1309060b0f060a0302220605130605031909060609242106180203030f2a070b0c1c0804030e0d050606040c09 67
    0x14034040203458090030303e030107108102e490240b075075200b40d00e008000d0007160382001210f60040c2c403c5c80c001400b651101c020404403442400041d910034400c1c03a11286c1598160415200345110701c6c0c00f4420410110140442c201501080740d83c07110062004024180c070030383c0501130340038524100d080d01c101030400964054110340c00c4840001c00018092035284612800000101000c2c40c1ca2840c520f0102018a004030051b40c0042443e6220540c100921840703400c80070140954000410407160107006c40140380c0c419080d00c25154203400d6000448020080d404980c00200300b020b41e100d440c4c07a6482c01c4c02454581c04104808404241050142c3c504002421102c81c0c200c1045a90304031000d8100b004030320510040f0503201e0281448105400d02240c0702c3d0864208071126510346003150081c130b0410240c00f801044030380c415682801842c2d40030b108540214000c2d254000f00c56841001d02840700005500641143c0c00711021822608003584452070454a628184528a866988505c000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367599793 1250 367598543 367598573
    0xf08101203050c010518030d0b04060902040b1c090f1e3903080405220f05060a0e0907030b07120504050d02060c1303020d0c33020c03070e070c 63
    0xe440442e82402500003446180e0300030070780e0751100c1d036030003600344800c2e55920034626412003882d20358035409e000c3d44458000308041c040350202591074644a8800400075002100d140540c4e2a07403503c8841043e80610074021015000010398503c0c0c1c0107610348842c41e802c80510070255040702c4c102040460f2503c07403039035101020412403001c0d0400d10f2000da06a808540d05022501c00d400c03808200103050340088404690064882c0030f011180c00040d908505004101136000c0760401414104050150380254840c040807142100c0c0d00340c0354a40c6d0f8030304102c00c039200b46483d0700486090004c0b80122144552011851500d5096003540d0340110b400d840701900c0407600350b1b010102440901d40c0512003590b2180d0035440581c1096421185084020200d2001a0140c846000d00c01d05109a208080010f015541d0700c42c2080f0280d421002a40a010707640485400214200010013910102c1c1e25092500f00400900e540d50502c1c1d61420648005080881405500111600003800b40d54503c046 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367601043 1250 367599793 367599797
    0x708070c050612040b0a0c09030b070908060103060204050306010f03240209030d050c190b0103031101020702060a020606010e040b0d232505060708040e04050a15090201031802010f08101203 83
    0x96070130a07141110541001030b054500300e03410154200d078503503170020070308044035001200503150b600c440700d081c7e401c20b00c2500010381c41d01940c8004001c0c40303480d030010421210301790100d0b00c15aa1f42c100803903600f0114040200700b130307524500c1140200c2c60780c0903540401e10b1820005243c0444c6500192401248440714004644007144090b42504180500d50140c14038110301140f1100301c1d40c0d01c020051050000030180110000221807141c02541550031559025000726a1210401e001940d41c501c1158514006007480c4590b42c103900b05405205070903980580405035030790361036480c1910810039102c28880321a4044044000c142d041186018212550f80ca255075808180159000940560800c40c01084100100000075020500701e404071174282904020949880c503019041498010002d000c0561102d1400d81e40c810540c000030145100b43c90821420905444604012080800190105a81454100e00180148400c6134000540098020b8458030341864900180c0c13045400c1d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367602293 1250 367601043 367601077
    0x5060313151d010b09010b1b0a0b1312090b0928090b01090b030601082d070f020c040b0d3512090109050703141e010c02011d030708070c0506 62
    0x100900013841028201d60050f11000c0380c640c105070350396640e4800d44001c181e01000445890f40ca07004180240316025900c002ca80a00e8100000040501080030380c050f0ba0015282407a101c003140110000c10403150066142410311114a0030081d400f50001040d440b0207800700c400c011200421214000030b46110100050000705207400141000529002040180c0c810814041ea50707030004074050b4070041c0320007100c41004600400b400d4032600f02d150001030070b89500034410a941c004111500003081982180e1121009004001c00d60314203040c0031344c05c0074510007600d0105041c08488006100d80003507000314850203040840509805100400a0610100359808514031030300210390803440c0c0d04001c0c0325992168854607210442c52000500d0800080c40c0407401c90741c1031140c1807000140c2c07003160103043c04000c262400390520480e40b070b0065192943c50907600003031042003252042c0845c001c41c10088182c0c1c440d9480d600c80f150a560300c41c41e090700014a6030740c040081400b125a107074030803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367603543 1250 367602293 367602341
    0x309031317010e12071104060b130306050903120c090a0f0605090306010e04021806130207030206090c060f19030204050901060f090b091507020406050312220506031315 74
    0x40e007154002c0c0107000c0d1035044a4480300c0e40e100d0ba0805da036000364100001c0c2c40c200c0c0ca0080010000c000170351049514600104c9c10901c2d01d0007180c4c100c0201c034001c034002e1005a90b40300610b522032081d4840b080c149140103000c140c213624008060000300e50040d201800f01c540303420152505c5505035120000003003000038600780f20f0405004140c010519200b07050784a040075070008680147c1c40d8007403510385111100203a581c3d0384032062800c5a0640160455485440e814002d480707401c1100d103c40c2d42d101d00c0b180d40b0900c0c20000100d50751152170441050401c41c52000b180c01c0034090843c5e840402d5020f0001165139500d0100060081c03410b0744583c4c503041e401c8000a8a0520281d000e5051003509100701006c64460b809002054035640d40c203203603a0030191000030000c14050700456014455a8094401590210b000f4107820250107004444da40c0100c40c1524403007420300516401031424030218070a0750283c1c900e07010b039071710903024510034088042d903050440b41000c101a94240108840d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367604793 1250 367603543 367603589
    0x81c050d0e1218030d0f0c02040b0a081615090e0c130b0901020c040e03160212061812070c1206020c0607120b040234120503060f030f1203090313 64
    0x41c1208a2040e0007034072038178140c02d01c060112110800c01c0c03001c1c05078142449003150790310707440034402c49001010030000076280c0798410342d1070b068403917030000700d1600000220b1444104005501004140c1d656902030301e0504656034490800500841802d801c203100054041c4601460746d805401241c0e040ca07250550761000914001842c0c0b1014080e84c580b0b140c1002102005c012100181c0501c0591203491a051022a0b00f0354001d0030990014010b41051014800710100ca0408005a5000303c40f904040c84126100c02d00c00c03988003e040f075940507c10056040c000c0004000d05001c3d2038011f0801580d042000e0600e4000c840240009034800fa82e00c0940129210b680c804a009840860a01b8007401ca41c1d090b003403020140c5a0f005d81c035100703903800603c5202e00810003113500007401b440b0258032a602401d039030400d5034100d01c90f88590840e0a024100001c0303102c031640b4a580181407000c10500701004a07840034040b074034140410054411501c0007500c010000305491051120140705808075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367606043 1250 367604793 367604827
    0x4050d03051e04110a0506040311041d071a27120703170306120f010204050a1409041502040504180c1a0403030e0d0b0403080a06081c050d0e12 63
    0x1046500c0010161400b4010303510021036620992003040420070070019400134000e915254032840e03102c0b400244c048100310100003d0304075080240d40a20601460f41081902c83e141a0310101195018103010401c8441007060340800300000700c43c0610300078828802e0350501586255041ca1040041c1c4002d245017858426980c3d6410080e014190080c1159502c0c442145240840100d110001c404100241d650480b20115005050f0880b613107242c1200d20503010303400c81d101d060b129050300f4200241040c95004100281d0000a01c920369039540e991b5808012450007450101103a400d00c4082840d80341c920a8140036942e009044031030184a16295104002c83d8000803031221449524407807100e01442980d003680da040c141040d4442000021410601403070300061b003003181c0c0380c06000516401a804c54003503040030005021064a83c050907aa5102c043c2a2141411054082000c0309105101500c18090900390108ad0005004003003441d05130350345400090781800250440c3e0b60404024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367607293 1250 367606043 367606051
    0x3110f010f0c02010c020303160302150601030903090315060f06030f150503120f25120c050c0d050109020301021216091401050304060f0f0f060603050606030c0a1704050d0305 77
    0xa4980e26200031188010000200207034021305001c80000306104542e81030094031180103040c80341e001c00030a0f50800a641c0c80041111075603440034140406c01c0307548a07004014a42e609521803a4805166542d01501c1c00c003840b103003050341f07a9034a8000c41e004c00880c000034001e0040d580c0c04141d56411042d10b00c11110070b4102003589503c101001c1195480c049480d0f808901c44001d21621071200811607000383c8201000c00b00c03844104a404020712081c1c10309480d4050180062000c81c0d0901d40c02910804145440a41568001200c0b51120714200000c1310360240b140001040d0046d0581c00301e82613801850f1021100502c0104003c6a2030385020b610309003118600d003c100c0c1c18a055404a001404070030780398100100000003409000c00ca07000b0300e41011244904010030942010000001d10f0f40075130035107e01e800d00d04001603c61290088500400d80103003030b40d185840d001543d40c5540c0c0304040350028060140003620f0740030164a0000d01c194002d801400e03800510307440c020304485000b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367608543 1250 367607293 367607297
    0x30a0302031909030b060405040203120307020a0b090f060a0e0a020d050c0108221101030b18040b16050d0c030e060103060204050f0105040312030f11130f090605010c0305180a03110f01 81
    0x804202003005c0e0200c407074000b44207440000c0c85444500100b8185a0300c081070100310200001400205540058844450b600840a0b01800d03200c1800c01c689805c01d448009029501000105140030078030352202d0012080c1000322001c0c0040d580c0416504442c00c08103540c5500440e03859007155070072103a0554230200b000d881c1c3c451303513448401511005074006001703021002c000c4092003159000f41d00845200714000d01401c5140700548500b00054012170301102c1d070300c1d0368401092102201844c3c0021500c03154407002c1c2490f01a1000c10001c2031030207281c03400c26403030700c03441417045c1401d00040d4003031809404050396403410807051108405062440d181000b10810041000c200e56130200c0510380081d06d40460456041020180031b4141e6103103542614200050307032082039128001480031030386440319055400303580b410035a0485203070380701d0b090126440d1030709030000038483d40046c4400b8101c25180340c441d813864808a40495400c2d00111128040c541c4503506500c2e0803104082480c40034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367609793 1250 367608543 367608557
    0x160501090e0a090b0c0c1b0109030f0f0c0b0304290c0c2e0b0312030708100b031018090c0b130306050906040c15090e06030c030a03020319 61
    0x4400000e00ca02010721906400d51220710115842c5000380e0480900d80c3d40000b500b01c254146400810006d9001010011403803003946449018050b041c003000881080c161a8074898500d55150803076000c111010484102166610010010b103490300000098100981a00d0705d03880c052604408082c2003d44104c1c141a69103002c128103d0070010584d4896240400305445811444800d0300d0212140902d805088080c2c030507800c09152044403941005a40d8400e111a440324400d06807141000c4410100da04402c0001400c50b601443c200341d0840142c209001d01e01e6035030f075465001d07a001903d040d415200e00c81c1d82001000c410400510312070114036420400010b240c0e554424680d414400c8407640c4601298580c101c4624505240c000c44d0070480a102d185404104180c4814080302d04031307070f50420b14a0128180d10441c0c0c40d04020052a2510586241800c5044065240040c0300603894440c85140c0700c1c9949081c480342c0c0040d80709400841e1903803244500940c420400c02a050200700388 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367611043 1250 367609793 367609799
    0x501050307080601032d0501090b06130e060a09050a0c06050304121b150603020618030d02030a08043c0c120206040e04020316080a060c08060306150126010816 70
    0x3d201c241c1c1648103102c06e104d00411401d81101000c0c192440009030995180203884020f0203107800005104e50800c0343c0c00340d04050108500d00498060703141c80d40a90380b1400001d031689a03503030310010b040340c001d03400c0b141c071140e055485540401d6580c01043c0014070100600040286000300490304000c030381484d1810304080c607002104151060809440c119001511143c8217209501c558080c40e006032501c3d0b0b480592040e448404e01101031224003030300c83d04130008280d500c003000b9141289040c3e80c2e18641c60f00d5545980440d00140d0f903413441c3c0010703200b5a1030901c44281c24064070901241d12031440c08146800c01101c0e000880e4450b02840030407090341401a51550101c42c1946e0105e4119030440c2c545002280c40c12400f2002e0f001802990440070690040005c1c11080440c0301750802e00550791508400c4504080c1559603c2d0907500039404111418115007420783d0565061403d400b0307240b4040f60301c114203601500412910f192140c0180315400051217212001016460700b1211186 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367612293 1250 367611043 367611053
    0x70806010c0b190f02070c140607061a0a06020a0c0e0c0d0e030c0d090f0b1806030a09050d0e0307050f15030702190303050603010c08100605070602120901050105030708060103 77
    0xc86040003414120803000040c2000e42c2281404000343c01c9040801280c86600365035030095120300d81c10b40d1107000140c40052051096450203a003d04081d0050b42092499503c01028050320241d0000544148084c25103035200c03170401000030000e90f4010b054a03000b604002a62a05c01c2d0081c0d44102c03260400c004451740c17080115400b0070020030000031402c001c600030500b50b0043c1207000309a4020b00f50601c1100340e10486c480e050304d034400782e082461a0b41e400c12800c1c5101d03011400e002d068030035007090032a00c2e00300050340d07014031008030104e031010203940c407142082c11f00c140c008081060b40701403001038181007011401400707040c1d40e2180d0840781c480c0014255100301940c04640b0000000280800f4402c1c4004059901d4440050300000741d02d01d8050090300b42203581030300035840d010108280d18413451055006a0b145110501c44a003000c030201c440741e10126050710305540070404440f8421480342c113140f0a0702440300024540d41000105030900070264801542a03101d47c0050010074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367613543 1250 367612293 367612307
    0xc070501021c180201093b011701050714090316030318061706040507110607030c110a021f0203130803040305010c0203070b0609130b090d0315180903050c06010b07030807080601 78
    0x220082c1c1024141040c2081c4981841c200031303810402c7e01400243d40519000030105141071303c0074040e503840c000e40389007055402c90f03d00700c81401c000f54640c4100151300d00d03141e004021450010701940d04910b261080600d8049142c0d0048002403008129410005024442e5001030a0b0f0303880c004010b488070088541300f400000e8145071080d5528008900c041e400f031301d206000c142c0d013881074601d9403400400140007045006641004201c0501c0007440035400840c00821032640285080201c0301341906080352a0034405140c0203501c8104225a00c0190704000c3c100102580401156124150310303249003500d200d001c0300300a543c400d200400000b40542d80d4668003d9040d1012582d55131140210301c00380c0b61140010b8481c54044080c8240d244000c0756014088951740c0f0184021154000090400d074254454110341c0000c42031080107164080d00b020036000c1c020b00e4174608002921060504162080c1d212020f0764900050050415030488005a80300c03e0030700303090b000f0303140990010b4902 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367614793 1250 367613543 367613549
    0xc01050a020a02120c0d120201060e01030305030714090406080a1b06050d05090c0d030309030311030106050d020c01200d0b04090b0402090a1b030605360c070501021c18020109 77
    0x540813440080444950402445501413001000c1d0310300f45a06091501010200c065640019400c21a01080e00d00c3e41c001128100ca03031690b12a4519aa074400440c4c3c550380484144e143c5107010000310072169110f000300f20182900d10060400014586000e040c020401458446079240041c0c04016241d008410f4031503d802c40e620210300740d41c035a4021800c2c03d4002c074506921421110101e0141580b40d40b0442c4503034441d4900b0002c0701ea00080003d0760340001d1147c42d001400070015a46409150380103006084903060020604481c0070802141c9507000b80b09032034541c01e0100b1120410701c4103000e80d660070350094408001c0d03900760f81c89050038400300400180c00348007a580807412020903075100c1c102d1070004000c0032b04405075051008014180922801e0310420064003038041271010040c0886c03051106c90440011681d940d40c070411103407002040c1c058207407024019107011600c00c0c001001071510744226030101e07401034403515040700c421344040d840b90b081c120368442c0143d800142074025 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367616043 1250 367614793 367614799
    0x15080d1206060f0f02100c051206030601030819020a0203060903120106090f0e04051f0f0e01110a030509070b0406082d010e0604020d020f030105030c0d03020c150f0a08090c01050a020a02 82
    0x1134030340444416441c1698460008104074503102c0c1c4010180c1d0300202400c42c1c8402c1011705030041d06c0b00000c0550b145402e000240200c0710400c42c85110100e402162203080301c076030056440c01c2c541134000a08001e02218000c44035000001c031306040840640105024029509200101ca410a2011000d21400d070140c01c07250600c2d80301080a0000410410003e2030031500c42e40380480d01c406186010f00104030b442c4c105281840180b98104006000d41840e2891808ac00c60402e10b640f0412409084003030001c5c1000e0040d484e010440c2c0c1c8d003c500800c0500480d403513801180c02c028040317103500d908044501c1c401c80e00c0c0e0003100503564140da46450440b08001a40d662540382c00001034028425000800203442c40001d80304040c41c1c9401c05035040f264110141d6050205890a100903122031500c000c00507003000314402014a031100840e1152811224103a0038825281000400f0380d1041d151702010400784000c00000c02401c01c4041300302c81c002c4c40c4c4a0b04143c0c1c2d032140170355075000728840288 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367617293 1250 367616043 367616057
    0x303020309010f1704210309020d0209040819090807170d110115091a0613090f1d21040f050108090c03030f250201050909060415080d1206060f 63
    0x1803140304640c001e604c2c46611800b041c181840d10640980d02d580000341070302e03170542440c0280c0340248604050780c0d4001e0401201c03003640b07600700480c661004200b100e070103900303000c001110804005807030031100e10750b05c60302c20072820050864030344229680400e2402d410f4401c2c8000c03180c808281340c60008201d00b442021966500885070250004620920948240d6400014030b91025003090b03900007162148004541c5504041c08064480d2160820356926940410082c2421607031103411000810a00042c40d210440c10901d9444c1c07401c102c260141c0d02095465040c8007000c0a0542c07086000f01c2c0003403a041c90484d401d203205840b0701c2a1810f000d00f990001d0310050080c08040c0920034000e0a50b59101a6980e40c130400d500821300c0d5a140d0410505000e0320002d003403008400480e016100c050410003004100684284010302c000c0d00183c54070384000314030b00540030b440007505c440d0000d800c640d51007450003800051105507007002d141c1089000c01501d07400c440c1c1c004000c046864081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367618543 1250 367617293 367617317
    0x612080d050603010b090c0d1103100302132904050a0504020906010c02060c010e1608031e0a0c120906021603020901060c020a180203060109060302090a06050310030515040b10030302030901 83
    0x1134010303c03030303442c85d40d80040c80030003002950301740c590040403c0c800145040180d8501c0c2140034003903001c2110800050100f1036420f001510b0f01d8500702d8041b07110307180085000781c10010306424203950f0b6148249950900d5190171507600d4039010b11580418101c00801c590320f0650002001142e01500d013906201d541d28241e0150b4840c001240c0e035036809000240003403010b828400f5520201c840b4111141920310340040f540705008002c583d100580c100e00300c3c000010f8500388080c81e6000b11a804280300100040c040090990010805025180e40340c0000c154503140c03000c2c1c20160340926003d50f08000b1041071005982e000034460540340149000c525807030241c40800c139050501d030080c51145117041d00f00f14081c0b0140e00158411282030b82c4030301e0710595445064059016003807400d5808410900c013400440c0c41440a1540010003001c820b503940d55030740381d00741800541c0b036801100c0103882081005001056021680103010f41e81c20180081c55038400944a00810700701504001d000c0c0490 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367619793 1250 367618543 367618549
    0x7080412050408190b0903070803190b040c08191107060b040908070501090510050c090f0f040c05040e01080316060b030304030c06120e01050c0406030207050a0c0e0405010612080d0506 81
    0x91006031031014104c0d4803070b601000c65000c01c24006642154000396407000201d444101105440c22103034024000c44c21502c41d440c05500c40c140540c1001c100990300c0502c03c040f1340d1180500c94a00c0c01c59107412419050003505090034a400400010186080c00602c00c0c11840b003000f219800380c1c0000c1c002070b807409628000b402905078900d0190414a0106008061142c1903100119040c400c13802c0b80c00301d19505c55420705460003203489100d0220b0a20190f152411300b0452100d2100d030051101c01088440b2000400300c0f00340f01d6584000400108040c00b0350001c2d20700740c40c094480c40b00218104100101d200880d0284200000c090701e4a4400300c00080e2410030580740a51b500a2a481405403a41d50003855204e01c83c0140b440d0780c1c100b03107a82c000b03640c0610405003e002c1107034540346800d0501e8030603800f943c0168030844082c49210650700c04141540c00d8103001e891807803010121420300c4e080541c05e40e0920b82150b03200c0c000c03107040ca0300000c110404951072140040804a0306503615400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367621043 1250 367619793 367619797
    0x50906070f0b0906090a0b010915030203011109030124120311150f1003030e010e03100c1e02070b070b04110909010e07120503030112051c02150903030708041205 71
    0xc020460703884070102a040000d8800c001c0d2081010904407003207562160700c010740d03da40d03210700505944201c2e0010301c0340c000260098288a51902c280d801b10b66503e0b4040b90231505616013210500c08003182e83c00e05403030280908140181480c60680107145002c402c040e1920051043c3d41e40c1e04100440745c41090302031002886502a9801507c481c4038040c0751100444000722012408401e1400000d042c20100c114200262900755813095403050004c1c0c01982d030105001e40070b5034941724005070161803030498040c404411745180d6591000910010484242008021001c81550059807040c404050254142c134225900b15007005100c1d1200d08100c110000008107007074204008104100c0c0b06481500000d0310300381e4403800c0fa150196103982c0e41f5040c0c0510600184960010401008014149078070208014000c00c00d9540c01c003d10101d200700c03036081001490158101c00450120030181d04100c0d07501040e004051461458100ba0050003200000c1c4010076240f10a86070303100303035032103902 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367622293 1250 367621043 367621057
    0x60f07020f100605181308030703140411010e0603190b0111010c0e010905040b3d090603060f082104080d030207051006060203032a04060f02010f0e0d050906 69
    0x400e5031540c468042e084005440305004150041a24601d40d1900c0c00d0101c031071503c00c07200c081e4400880d00d520760b503104403584054010810144c64001c00000c2040c280c258030b0256101700740f003542001d440740c005854a407038044a148211014400c00603d43c0106510465a95407048001010315070316005179600030200a8030f000c15031038a80034030366094001e0781c50000c03854240c035a00d010655a2040200755801c500b81c00b500700c2c45100c842103481d003a14003910481202204290138005c2c45070000c00b4480782d00401c40c0e00103110325030f0801020340c05118600c040c2c80280c08944070582059409981c45504034007034102e0800c02240040f410940794181ca01a01d420300a84814143d0190002c0194001c45000d5400c0e0054070309403c03103013940b44039400881e0010b40155047d541d510388000001071000400e81c21801826036060f040200520080c00a442c1035202e14045440c031640003401c40700c240d0314030003115252080700c012142c0001340d800c203245402e25040c1c2c0d45142d80000300307005010b011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367623543 1250 367622293 367622323
    0x907120f0b090d0908010c0e01050d020d0e07060e010c170c100519060e01151d040203240f06090d110a08070611031204140a0f0b0603070b0309060f0702 67
    0x1d414450626804624000b80308816941c0400c050303100c030900c900300c40243e60100042241401041802c3d4040c4004d04031001c2c80301e80040c00d0004183d0070740161a0403920442454102c64400c1c00300700c3c4c220400d100e00e850203281c04901c80d005655018001a200864011100c80c0801c002040c2e007808c1100c0700f27081040e0340d414089410300785c2c088411034522000d60b04009040c10008644841d03006604c60490301150b8227900d2480b440401565188414000c020b1b481c1d2583c1c075414560b4071640001c5010300015401c06440c14140e2190035003102508200910070103940750041c00594418040c0d400d200e40c00c4404295030021460880030110044c881c0e140c101a0039140001c14902c041391481c119126500e0740d18203803203910300f5241c40e4800c44500709414810b88010901060001c1d03001500c40a0642c2241c003004010349814403139200c51041101c9800f00a000c1244505041c0221002804030800c0c40d1300f075007846c1082c03980300c51008202e0024050b1580000d4281031081280e40043d030001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367624793 1250 367623543 367623563
    0x7080702030a1a010614120604020c0f060718050d24020903010e0a0b0f1003060b06090306100512010608151b0309030d0516020a12141201030501140907120f 69
    0xf40994a403214401d200307820215004082104c041a914070071070f07000000c0c0031210322442d551101004025000040350706024414030001301c0c005001084028005c007100d0b01c41c91400400441e03494107100b01904010b003d400000b03070441c00191103081200e201400c101c6040703142c0c2c2c24103002200901494180c23640c15800d082d03500b0459400032a031060018041e8443d40c4895442d6070603102421004e403510b040081c288002080841c0c42544000e6800350000c0c086442e03d41d003500064038200781649c2d4142480c0309400108000c1c40e00056205030036401000901c41c444c6014100b40d111554115081301c1111090b002851100e860174100540c03030003a003920760302c80c2042d00d4082ea070f0342c01110b4003880643c603003c0800e80a03003841d441c140100025500a080c0c040301603580002c000070b103d0461041c00902c103503130118021000052b0003c0212200c00302003541c510f0803c142920a50400b82412841140c02c0c08003904010410070181c0d000380807200380d004540c0c070304034440c04510740c2c001c2c03c00400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367625899 1106 367624793 367624823
    0x3040201051e091003050603121c05040b040308010501020606100f180602010c020c04050106051b0f0a06050402090f091c09050d050307051204080307080702030a 71
    0x4103150480c14550b0072036500c005000040c004102d142804103010580d07060406800d40c524069180c1803003c0d0404c4008240c59007036050b401d03590301c1e40002d16a00c610b5510f0f981030244400e086005c00141c9880e0414548104090f10200c00160040000084a44c130002d0141d01846000301044002c2c040c511058030440103028141d4280200345164a002042c0c60381c4040c0140703c1500085481d00034004006d007003428500400c0d210b1b80c6000014807441e540f000c2901c41203805046601d000301c484030300091800303425100752061485002c0000c01085201d0308018000c074400c0d9840342043d107881d810310354805001c82c2c12351032076400303200140c400c6a040041c0c803088007941d092643d506038860b0041448003541800988443e800002c1ca0305c20050108101c88540ca900c50b02d0505050921000c0c5807644991306000d40f000d40702180c0707903081d1f550500075160340b6035001e440d034050205 = true := by decide +kernel

theorem cover : BRFrame.Cov 367446043 367625899 := by
  have h0 := BRFrame.cov_init 367446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367446043 ≤ n) (h2 : n < 367625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
