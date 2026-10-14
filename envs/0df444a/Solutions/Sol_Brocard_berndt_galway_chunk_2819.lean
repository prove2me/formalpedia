-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2819
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:50:06.414976+00:00
-- url     : https://prove2.me/submissions/0502983e-5384-4848-a80d-2aa2c5b3d3ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 506834532 ≤ n < 507014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 506835782 1250 506834532 506834561
    0xf03110d0503042d060e03120a0f0c0825030809010543091a0a0504060c110d030e24030a0c0207030210090f060503010506070b06030a0209010f060e0301 67
    0x3004200d000c1550180c62841c00211342d854698900f014105480088240d01c480082611088000c145250070f104a90451407031007801420000e070b00b800200612040b10343c140c2809007178410941400240c2c41a503001d00703034400b800e4000080b502c44510460b070700c0000031408940d0400c04603803555010f0140341c1c445d0781c50703010805110003924024034030180044040002e034551440c104000d04458002d4180d810300684581c0507552178000440c42c2c2843ca4055140362410511103c5103003039010b01117808856043c07038007100c201458107200182601b03a02d9001d03440143d40114800305904581e00d05807100c400c072543d54844040380f0a0b28840b5440344082442400b00704002904591180e202c0c0f2001d010910485071169203075408101c1000f1100c0754100031480e410b4042129006008900d4068019440e00380c4c11755142201140081c069010001c00500001c03000074080e8408015400c01d05800500d000740d1543e444841d0745948001d07014540026000e040314544a0405005c1c44c8400c06c5486d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 506837032 1250 506835782 506835787
    0xc0a02061302040b19060f020106120b330a09050412051e16021c0804180b2701060f050301030803040f0b09010209040c0c02090a0c0311040f03110d0503 67
    0x8818045424020000c82c3d10690ba0034601300c9549407010b841400100d0750030354032072803400c0c01005049000c0c030403030120031681407910034003000c851303000001d1140d82e11050075a241e031600c901183d400204044001241e00682130b0590302030a9140480e12100c600340c0d40d921185881b001c6190585104071009000002002d12090b01c041c4500b00808010382221450009101d02c9080020654800b0f54000850f90b06a42980c0951500f10100c40348403824940b100c420794010f9031070000c0b82c012445101300800c9094105540b01c2c1c0c05401010fa5503034000e0030130b89031040d141c4464641004440c4118054003029001041540c020040b50000b803a181d203c4500f1603180d81d071000e400e540020710480d08a40c0c0c64460b00c000503100701d03030540030301e80c0c00303002580b5510310b030301484101c03502d0707840380c1c01040418803c11016886c0c4240480c1c02900800700410a1a01d04905074042c2c00300601120172190300040c002400315445522030140d9110b020350340c50302d0b000e10703042040d41c144110303004d4000c0c2c104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 506838282 1250 506837032 506837041
    0xb0d0303153c23040f0c170a0228140412020f06090d141c0c0b07020c060a03060303020c0303031012030207090f0603031b03050d0b01180f05090c0a0206 67
    0xe03004180802520007003007800c03540703c83d4000034008a810204415184201c550440c070318182c0902840014840010000c0340403006000b8040300c08810000031103410040441c1c00d4040e60740450b22103003140058602c8520740d50741510810038850050340c0010310750314032040440240200701c90444041c0311111000c51582e4082100e5034000301d03d0550300c2401000070b540c513030f120303881f091040038014480700a100021840c203500388940300c6059096400302501440e0401d80255882c0001a0032405c407082564804100f42c1c6020240140786910040c0813a81c40d039115407641040080d20b110381c0c00e9a042102107030900d6928041540e814103004a101400e201d58400006043d400b01e020b0310480f0112940d403460141160078042c03181d60ba0544645c403d00615811800760780c0710413512040c0c0e01d051200e54070018100e005422000040079107411280210341c1c0b042c00c11080d15a112604c40707400b1555130b01050181d02252003446d018001e682d00007141072108800f0f41c0c481c400f1540160109954 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 506839532 1250 506838282 506838359
    0x6090708060f060c010c03061a04080d0311090405160e01020a120f1704050102090a0608060d151d0a03020c060708221806030b0a0902060d0f0b0d030315 67
    0x6080c0b01c05600314505005078461100c00340180c03040700d40c0b151800a8014105500c1c0140c05003421011020018100002c0000380300008200400e0000d5290000310105000241c04141c8100c00d1000e5001d03003814248000702400031050359264841d52518042907100b0360059888820541e80503180c17200101600b40341a02a0010030010009032a0144d402c035032805844000d51026035055906a602061590060500815180181209040003002850000300195501040c00e00081c0030144034504441611400d0b000300002c040000b00698208030201c40e460b07541ca0002000b0760045c480c040501440b8104130303044604103a00108028030b0142440c1c5240c1d4001340352181040b800e240310400241050005442c0c180b558070743c0401080003461800e0803003425202400400c600d520b803018800c0141e4984040783c44076802498040b440d0310382000c502c40200011030340f03207400441801c40c40007010380c1f550051000e40e10480c00e8200d4a9100ca04044003404000d0802402c0c0c00d000d0221001041c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 506840782 1250 506839532 506839549
    0x60f14011e0e070207031a07030f1e09050304050a06121109151e04030506041110051606090b010b0301090c0302090d020909160f050307080114130f050a1a0609070806 73
    0x145801140c0c4086c1d07881c2e0300c0310318500c0740141041000c82141300340030348503515018000c018081d40900b0b0112564909040c40814152031503200d02a0b552000c140c20090203005580c002c04000f040c10030030642e01c0002504200c150b008101d0658640094450314041182c151841224040c000b07410115101041d9030103030b4000410050b06041c200c40190a8800c0340f03000f800507501c51800fa103154202494494105910f89012501c512031082181030030700d40c00410b40b25035100580114410a60909052000f440ca000015048041000c00031460040c42c4000b94100d5880813010031003401116070840c2280a000c034229030041c021030080002d45400c290300d582101d0303040b0648004c500b88444601e4842c0075a0b100709109510f40c1010086441c0500c548402030240c0c02c000e0161405120654101a100500007008030120b40d24130b0045c04010f50b06410719590003022141401040d04100c2c042d1250524048407090001d03000503001c0c206540024021510b5880d482c0c1c05450315003c210094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 506842032 1250 506840782 506840791
    0x12011a03150103080a05030c09032e0e0d0c140d030c080106180302061b06191a0303071212020a03020904060b12041202010f05130201260609040201030207060f14011e0e 74
    0x80d48180400d40c100c2d43c051090000c000e90b14040c1084240b00c00c504d5138401181cbc084959a414034200c460300d88240c0204401c0e2800c040d81c81c002000301030900e00008806261000d00366584a00462903c090350160310000c0303440603a4072000016a0795110844400701207800d400b1000007821001c10050405002800c40d0060950303041008078150b04070f091030440200c81c001200e41c024007030060101e410b442000100e002c0d85020341c08804204000c00d0762807003030410080046414400c0c03c507959100c1c404411030444403a105543d12000a40020081d41144c1d2400748103d14010700010f80c12102c0c01150402c030040b90080d2580d5586072034003400c0c100896010025552203c0b0450708080c460b200b4548550341020915240c000c0ca400014504042c02c0400801c2164210603808130b20400030308140e0010701140ca2100035500ca20040b8007078003038664010101c038281000400031100f070350400041d00004110b103d00c1c903a03030f8074010544088800100b51951148004c144003440c4403040c0349500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 506843282 1250 506842032 506842051
    0xc0a1425060e011802040509010207110d140303040302100c09440a140a0209041e06061d060f060a0e06090a0602250609060e12011a03150103080a0503 66
    0x140001140420b0130340d9940c280c03403c0302c0c9200200c000c045190501c100381d0000c100343e00841c00c02c01c0c96611904203c20108080d840344043d0070792042000410b04c031620807101850103490703c0741080d180180d911043e1070245405d144c140300ea80711a040c446c884400403240c81c10344d1600b0344045900e0201005038585a501c0f4125040b54007070841e407402e405a2020300700040c008142078003803400c181c00c8002c032480c0d1000d00380d00940341c003102695038201c0041c0c200383c020110b951480c0301c00444e07000440e03501c01d0007805c0740d040207000170305407500e01662034018a03202e40010296560400b0481d543c400070501550158060240b65409481192441e503203d60160183c0c4c94540644001034600d05c0030b9021200682c4038281e2030f2400b0f02e002c0d080d52089014810440c01741410114042c04c112818001d60007040490540c49026a54103000305142083d0640204507899420801103000b02c061265a40644540e40c1086401c5803803400d514100da13044580181482060345049515a00280a6410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 506844532 1250 506843282 506843291
    0x903060c021e0706030b04050f042312030106030b37030f080a1b0b0105060f13030501050106020f0a0b0601030209030f06070305040c0902072a0305060c0a142506 71
    0x5618200b0510500c0c2d020300d001400d44070301c1c0c124000c040e2407401068500903400c11060002000e003032920103070415482407a10210143e0411981120503400c0400b05040c03095a1200404c070200070000c50580f90181c2d4240182d844490600482542e015041a0484d645400c070561188aa01405000d0440140020303101c0b643c0713446178000440100f1040e07c0745540041c0c84003c42c0e03003000300c54890304c1c00191090001d80c101e44600011800c144903a90040d0fa000405200003a44d02c41101c6090415248101c0003070b0b02e85c1456402040c0901170078000d48039070320340c000c202c010004500c02d945900540b650398950790480114040d4210760030054162099040e10100400c1c103201d054440e001c2950f001801d480c1a00b044800480554410310f0518810000a80813455100e00d01e03855031901c115104400c02100c0000c04285040d40c03000e010381c0151014011203400c507a000307110251499846007078581c008075003605030b031003020b0142d403000008400d06e4032000d2142400040c000d004800009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 506845782 1250 506844532 506844553
    0xe09010905062d0408030708101d1504050a060602010b032a01090503100e070909080a0f140f03040204050c0309070e0603010609020a083903041403040b0703170402010903060c02 78
    0x3d01e8044c0c03021580c5030008004c01000703e904c403441c241d1041841c2000c40342c80d45007461f100d4040000b9991702650001c45c100240c0c1020f00f2201e0500007039405070040040d480c002d404200101038a001e444015402c000c01e0740d0091900080741c20282c10780d117a201c4024100b00441c843c2190040c0c4005050101105002680340d03028004203240c0903660b00301160301c9200110142c01d020f565004100001d2516041c00042059101a1250508141000e00860b18603510a582d51020310b11f5041c802d00000501007444018040618000c500c02e40e01440b003070315000d41c4095680400c5601c0035465000c440c0420912000c80d05880d0005805000003440c5621030005d003090740d2000300d4200200d001e6400307004011190f034001840702550400050000d030083e078000072881d0220b84d0840c25070580480481e0600950524125200300090100c030b546958a8214020980100304190b010408043d03804412440f000c80451185038165210200142140d4030003000b8005890203108602c5000c1c401d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 506847032 1250 506845782 506845861
    0x50a0b040203040b010f0e01120b090106030c120204050c120f070311120411010c11010c030e0406120c0b040803070212150f0612030f0f0901020a060203100e0901090506 74
    0x1c5014902131340881c405176050600c1816480744980c002c1003200740040040040189542c091903195600004850035130300d070301441502400c044e80002d80120842000083c00d10035440d0b0301500700d41700783e4091000f542d400103050f5090140362400000307800640b00040b00541b002101c680e1011a6040004a08041030901001c942010700e610324410552014403050100030045d034183d2000902c2d103540391900a070348000602071406041d0741880307400721405041601804070100031310409001048000d5a50301501204202000c080c1c81d0344e4010600442c0c40c0c003e68048a013078958100085280a0f040d509001014194a22b03c038010b0013030134443c40c428000e143d50140110008800c4e92050704010003001822043e2000b08007080c0c1c001c015509400e0020b00c00d6400c0240f444a111b0b4813600c0000040c0d090040070070004000c18400020804250f0b80703110f201080e50f034000c4240030f155446c0100a030894442c09030181040d07004a00260102841c00700700901a0135044003c443c581600024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 506848282 1250 506847032 506847037
    0x15120a021212130306050a0515010e0111010207080a080115020c091e093405060310030b190b22050a060902040905161b060504060209060705030c1203060a09050a0b0402 74
    0x801c540500b1401c3c08100f84096401869004000c0c3c0a003046a410421055a91030403101001814440306031240c0606a01a003440b00e1101c01c258000d40d07640880d458580c2541d44411000404110020004100d0007445411244254010780041003c1d0641c03008110044c400213007200400b0369801010240a446110014011003001009060020b0710b404080240c000c000d903c40003016002c5410b030f400b401901a500b04030380d01503803483c0d943c3d250010f1010b1366958980002d40442d4064050102e040a06803200564102ca030710100403441c06d4904004900011000c1c03a07640030311902001710610700b03d5001d590401009400020041d03610390546c4203a80050344400b114954403000c000510b040a600c85012506034a8050144901da5101c000200031000e0b019190558400005003003104a03812200d0010008103020303281c4a15141150341ca0f80489103000c101d0040b0b1810b00000510310061381c0c01100010941120107041c14128401490002d10b49100d46403202d01041054581d80300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 506849532 1250 506848282 506848297
    0x504140a17031e130e06042403030f03090b0a0b010909051e090c01020a1407031a09011406030c040c0c150615020a1208041407080615120a021212 64
    0x1842d141c014003d0f044542e0b00e0120241019000d08002c0c00c400c41d40500200ea003618504031040c501600c44001240090440b03884080c01000703c03290164202c2c42e01c0912000320303842a41e400443c0d000460046050b0f03900d15000901a21500d40803d489003015046900e040e001850700d4207506544807000360a0b2a001d030bd8460044854942024150301680601d03503000e000d80c0300612ba08426900001d69440c0300000140141c02040d030301e5013110f4130900012004541010500c1003210407010a260700190035943c41c0d00719807a0000803100000d400c1c0f4018410b0f48010050170f41841d0503001e010141100c0041d400410503a880e4880008000c0d8603282030042c0420b0f00090104d05003080344541000201c00e40e82554840c48400c070006520500070104207c82d481c0551941e280c7d4900514002200900421940207003100815000d0000600c548100800b412180050b400345082c002d12550a000d0301100d500408422005404d104000802d410b8404040b60300031140c4e0b1020000a80210a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 506850782 1250 506849532 506849579
    0xc0603020319020c060406230903030703050a140f07030609060e040302070b042709050d0c061503020a051504080a03021c080606120402010504080307050313060903030504140a 77
    0x80c090307a04401c050150301e42d08900002c5141c071218110340341ea03890000b0701c014101c90703c070003900d501c00045001c90301c2c4064080502c0421030030015041c9440b03030000c03240d5a00080c0780c403000802e075116900031441030b20400c40b8500b2590301d4003110030b0400d50000700b01c9000d042e00c03003600107900c0241d80300740002807201680d000d04a04242c5002400e10481d40d0080da103164007032009000f50400c40102c1680c000344200854208400d200c0c0240c05888a4070300035000d4000c458010512542200c580341c0f01502c03d0030100946000c000d1281c41660180c0006500f00040031001d2115082001c0c6219500e42c1c603540c228201030f40c51500c0c1d8607205111030103d0068010440480324400300c94160000041039003481d607103e01d08a00481e025011318040d034103070400c850012034290b90240741242c001e0000c000a0329030740c034110f0802980da03510040500d0441c9002c11000274800e0b00c1240c0c0c0c00160303070b0f05644062400b407a00d041c1c1d65680c480c1a032443d43c4a9400400003541c5500d460000070041000f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 506852032 1250 506850782 506850787
    0x3031b080c400f0b070b0a0b0117090c011404060f030504020301091e050d140a05130510090819020d08031b0d0c110106141c0b0a15121e0f0c060302 65
    0x70f0400c20070b0180030303489402c403040e090020800003810507684950141d404640007803d43e034080012180c1014208050841040c0c44092081d5100003160040369184280c88103441c054400041c4a801d11441c800c0e0000070b1a250807440c12070744a6040b0542060004002140c100d64546450a0f43c0010850111200c1e603512862020004140038501d10340d03055040c40708012a81c0c0c0c040800e9480340740310610410000161081801240400490103000050b21a9070039044908020700106254020780d00244201402c01d0070840300070a031002040d41c0503108000381182a40c0d07940d181e4001030040c0301d150b00116210f0804075450f40c0a0290064000c5000c21141840c00b0050048482036400c0032043c0d0401a0031301c40d45052540311540304000b5602c581c000c0c141456201c245e0300e101c03030004151452a0080c0000407440d500101040113032024020700e078655825118420250840c80180a411400c1d11603480c1e541c5400d0018400780640445c00d41c443c4941c4e2004134805094000d2004254003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 506853282 1250 506852032 506852039
    0x3020415170d0e060747064c090801020304050a02220903050306131a1203040902070c031703012907080706150b09060415050c030703031b080c40 64
    0x188811842c054115103100e1007039003402004580c0c2000f80c235003c000030007210b000e0241a40e124070744000d082650b00c02061820034031b180080c1591155405090300041c00c580c40030660701c00601c200c3e401143d00c07070004c1440200c60303030a011081c00c2103100c4c41d42400c8540c1500d115901c1a00850700308c2440b81e0343d456902d140c60410401c0da0501ca95034070600e2803070028541c081c140b1180403801c0c441d13800c071445915100c048a0191442c8a41d800c0102c0080c004a03002d0f0400c2107405054003664441c0508000082d4450702c400d01c0c2c0d0209100d84544000c2d0441c0c1017110786007520a80100c02c418441048c504101d40d2100601640105812240350340d036140c5d142d081141c0147e400340500404100e40e80b900040e0070010f0042c3c0201d005410b02d444a580b8a00318090007041102c2da071010140a0300d0301d80c802c2d410080c0090100b071007250000c081040d95070705854822140b080c800c20507203205a0415181c142c80c4000100c00c0a0b001420211901111400410030003d45e0a014400810030300710605 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 506854532 1250 506853282 506853383
    0x16090b0123071b060f12022106090f0906040f020303070605010b19050306010c0312091e0605060316090203070c0c230f03031b0703020415170d0e0607 66
    0x183c2110103401c00f004980213009442c3e01411000300d03185240780c84071a8600c2100c914001348214220b41d031402c0f44501861130b01c01c07004055144211012030380c10416a8481e00c04d404101d000302c55610707003a0040000500000c0c68443c40c144c80d0f500150840782040d00315555281200c03401c6e000480c440102141440184000075a27601400301c0d28078069095041c41c50000e410a840550010309000c0c0404000c070205607079034051030b14150440982ea5040404038085419002c00c8101985c002e41094002209400c002904141d0007008240c2c11034500c0c905080700e8001d403c090305203810002d4016041c00031500142900d0040c3c8150f0300750030518002c150550032030f16100801079025907007054680009681c04015140117950a00b11900a41080c05c4074504001694000950152401c05d810202a6400110b102981c12500c0141c84000c01c0c4001c1701e988485000941001a0200442162905240001d489200e106154101089144113601c880d01d03031402a400b03480a00401a140c264007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 506855782 1250 506854532 506854553
    0x20301031b031e081207030209031c142203050706021006031a0c160809280614090a080d0f111515060c070807060216090b012307 57
    0x105100c00001e6003a182d0340c0c8100d46298948011600c0b01640c00088040c070511008031803064500560340c295601c1d00c003030017030020f4010080c154000c0c454040690341300011080d112464007120303142c0201803956903009642d50b0380400280c2c1e950400e8025014200603c80795050b028500c102e001d440b07410b0620307038003e181441c140100c800081c144401040031450900309001c00d0098080704444907038400c44000030620452005000101e0f0280b02403082c4034050000d002c0e805021100132a10b07400b220562885600745030b00d00360446001c9041004950b01030090029040080c1d034416047c011000d0000d03080078410351040146400020402072807a03400000b42106503414145442d00c80c00485d240c035a41e240c00c0c5500701070b0110703080110b1400c46050b1103010300203000411081e91041030712400341d12945070b03108141c00c61159804c041001c900206aa07042c102010441c80c0c826450112640050608e11880505000e0110602c01000112500008080c0c3c804c0320010f40d100028a07080c440d2a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 506857032 1250 506855782 506855813
    0x506040309091b0509041a06040902130605091003090302010b031002030907061107060e01050d1a13020903190c050301020304030203040f050301020a171806010602010b21060f040602041802030103 86
    0x740100c81d1401c45003500003045d203503900000d5400040c916160302a512081030f030724600d1603018101260009103042940c0040c0b41200180000f0b0120300ea6035001a03446009804070f0301c5e40043c4603e100072101d1f20903885455901e00910021074038229260210741071490914003040305076000010018894800c008607401031505241070300d5068040d2601030344035440c5001311007c110710003902ca180c680c41501070f00e5070304c0c11500080100b90055030003031550308100d100c00d5016960700f004400c510780b07140c820f560bc0804050b01a10000040c002c8582c04418040c40890348891001c1002c1031988091003d184500d2003600107582d12410401c0119082c40b89500c0540300341e00410400d045154049000104854a000c1c0e0000c0c903151002071800b00c07440b0800d01c403003501c00d110000840070343c15080041000c2c01556a101501040c0c0c03421100e8219165400c900b540c0804085102c45264548540c0c2c40341c05550010309254a580f8265601c03900914100010f540101c0107006204840949041c01e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 506858282 1250 506857032 506857061
    0x4060f11121303170c0c030d06031202070b0d0e0703060e0a0218070f0509010507060f020a1704050d0806120706080411090906061003091e030315060203120a09050604030909 76
    0x10b401e56075004164640aa4040d038210400d030000c0307005c0c0c4a403042520f04001c250b50075261554200d0051100912151106882c002180842080d4642c0042109820341d0310280600d403138500310110090207080c4040c1024540d00c80c44600001050302e51003100721545003500038000c02245401000b4840100140040c00c119114080c88045500001d6200c0201845d080c01ea4030f9814070350060707410740542c81c0040e06040c1440d06141c8241e000c0d90080449000c03503143c41392844403c039500030a102c0d084400078084c0d404a840c5c1c0e80001e0003440da0701c3d884103008040c03000e548582c0041e035080c15074990001002c02d0300360703050100700010350075007880c00300041d2002e4641d0f150616649039281e5004c2c00850045400540e5451b41a00c02c5d0412094140c100c040d40c4082500c240c0040c3d0345810400050f400203281150b01d465412501c9524000c540c0140d0045081907c074545410364501d01030304035030707000303541d11040741c0021024042a440340b400f941756201d00c546020311340d605680250214045 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 506859532 1250 506858282 506858311
    0x2d06010e1e0403030b03100606120c020c061305061b061e06010c1712101208040312180b0c06060108160e0307030506011818020105030f04060f1112 65
    0x110341c0c0c403162514854107841001450161154141a001480c1040406406014039060340001d400c080e0400d0b82240d03e1035035203000c2203e00f0940101110040d1120800680000b03806030018600b00c00601030364001e41301140501981c4800040f581d80c011444c040d10303510907a41024080030188542940f040045031602156098413109840c2000000d20751130500600b403a0100c18004201c1110b0001c040d0181d407180d80d541541a500da40300c4044501c1510000c8400340440e0010350442105e228079401105a0300b0181185d989140e9038464401150402801e9084a8000300a01e00d8641c0105070407082d03a9a210302c0c0403043c606050000300100d040c03002d29814802d40c5c01204440116100c04e13450030201105103d00003030b042074440d90024210380301d9030340003054500c0d00701c0400c90510f50818007000001c0301c004407111b4030b900c502c0019011940500015805128000d4400e6000c2c0c400e88000804600030320302c41c000c80c1c200c840c0d58480c01e08003260444614000394619904403c11840c000c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 506860782 1250 506859532 506859541
    0x1b0a050d0212090109120609021905090606041203050f09060d050103061406060904090204020d0f061d070909050c090d0503040501200303040f03090f1202211b01022d06010e 76
    0x1700300d14003922410101000541e03282050100d0795001c0317407056500801800c40e05130b00c1c00000c41607208900a551041e81e540f00410020300d421030450b0103c415a840307040c2d0141450300c0540d29600440e45451400c0d0302004000c03601d5580200404692a4100340007801c1d50560421800700e6410407104800408840e06002e942d9031754805407804c0d20401c0f136000c1001ca17294804035002c0d014040e200310509092080694030b503503080c0c1000098804100301c107070342600d441e03660004a036001c0d64104045900300d0b0081c020a6520340040d036104909a81117460062030b81d02103503003500e001da400e81e019040800d003030090350380c060200c14000322800411f19640302810419a00d900c00500000c00200713801580104040c041c00c00c0400078034028005070b00c071541c0c418002c0390040f80908224421171514020013000040420603481004000005200100241c54003a19407603c0080240c103511450716414800802c0054210b402a11034000d20140e12300c02c0e084914000041e000100c2c01242c1800f0032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 506862032 1250 506860782 506860787
    0x50307020a060216060204030b0421080f100e0a051008120405060a03231603051e091c0302041509050d031b06180b07020615061b0a050d02120901 64
    0x21610380d030000c2c00182e640b280c22404400540c40c03c08000c0c80d403030000c03900005028683d42c18911076409016a00140810050000c02c00000c50b034000300801c106c2e0002c24a1005010195507101800e03941c0e80031401e4640b044c03a12661401c076080354026440b2020003810049031035505c00100700c3e0b44020f1400c6d0318044191140750146004680c0200c034082041a84a031180c0c10030f880c1204094110b01a40c001b86131059150002103a1024440c04500406140c481c07280c03140ea8401c98540c0d514190079402c603400080018409403060101d0700c5040d0041460700c6564201d00e40550090320016a51481c001c950381203c250483c410301030050b10b0804008649941056062136681881d00605460041c908403803100c0c1c50180140482d8075243c0d644261101248c0b1302c81a41d4010203000c02290f0300c2c0c0600300d0f03550408580300451702501e101d200040303041c180d01500d003928070b88060380c9038001480e9560785418030311042502d003688081400030071b107501406925040170610545030304e00f07400103001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 506863282 1250 506862032 506862043
    0x16110a1a03090c0604031203050601170a0f09080315010e1203091005040f06090915030c050105090402190c2001210b10050301080c060301080a03050310080a05030d0c05030702 77
    0x200c0301400001000840e10402404521102c12009015546607522400c251132941243e008400100f0703c0c21003c51036640c0550402e040089100894003410740c1c58080d803a0142c1904000b080c1201d8560004a0014043e00090f500c54512108000c1d860301c03000740018040100580800d0040c00c5c2c660141c1c2e042e072004001c44205500580714110340130b071800000c6910307120715070080502c0e840303c40000c54031541c8581802c0854124440031b02c400c4d00020344150580300c561000030010086c980d410040e5501920290094240080c00141420000c61f05141400030048011000500c44001082048603100310030038038003c513400c03100d803000350f0b4030020781001d220700e075180d04d20541c4000c5400c807600700e600101c071103480241142d8805144000c02804070740003800b545009014210b544251070030300302c0a4034101d4428200500786100c8a4a09440c03d520141c44d03815004907484020421502c02c000103c0c602d840b42c002542d0b00d0020310103210496218131025410050100180f00840b680084c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 506864532 1250 506863282 506863319
    0x41a010318210909060308090a05040c3002031801180b04020d0206070501021201030606060302090d06090c050909060702012a03050c1b0307050106050a030b191116110a 74
    0x100c840c820078030000c09031009000303503100000c3c071170078448013108000140000c1c0011180c291040d03102241c69500300400d641c0450845800100310010a00c490055500012014942c103d82e0b85250303403074003003454280d90080311109629030441c4402107501d00e09200c1d40c142c42d804041c803404602c0c126510b4001c20b1038050006071046400001000a559440c42290009580400210b41d2031644041c02410340c0030920082d1080da240030f01c00582da9009000f01d8543e640014074418980760786503103c0000700800c800540b06071000b440d02141588405c445075000e9810707a8024207151522400003401d44450103000d0014591121824080340d40004a10070301c003080b2308005c50036a580c031440c454980140070040e01141d55004000c103040d000400180f0000d80100000d02c04d81d9128024899580d0352440010212010800003a000c9014003421100e82c9108810206040f01600c80740000398208070000301040520740061810002010010510080c0540c1e10414413894a036514907813800051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 506865782 1250 506864532 506864573
    0x20f0604150f050d050403080f0f010f0515070807030c1502040e010603051306150503060f060306010b0706060905070905040b01030908251403130803041a0a020c041a010318 76
    0x42d0703800780c028012415143c81044031601008103285c40e04000788101c0301070381d24008c00d204000118100c1302152070b046060b602c181e420207440b00e1408003030140010002c2209625500c1c144150000100240c009011315402561742c000030383d999007403480c000454101d5405000344100b00401282400207411411540c0074140007032941d031400c9607503071540f105920090485240c807484184c8440c942d64440b041d22000e8084a103c3d40d00c46017030800051090360080d40c194041001004038001860084c038240f0320981001c83c01d15601c01e942010b40f1000d0f104400469030b1440140101d003050b00c2180354508091a043c00320600d10780b01c090343d0348201000501c0480c0b250340f5244252900341d64600381b460b40980a90071401d00c00c6041900c1e900300e14010921801c442c0301c0040c6540001083c0e4003524030130b00c0c1d240c00031600c5a048e40c0e030952000282c0000d500a4509048980da00c41c41440b4610f858510000c035544000e4000400701c030080140114032105030304402001c211129840803d0101d5070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 506867032 1250 506865782 506865797
    0x21061508070e100f0e09010e22081602040e0105040c0303030b040905100203090c120c10030b0402191e1707020a050d020f011a101805030d0804020f060415 68
    0x301c400c0302d480307050b9810941c02a00d0744422103260355103c19075515403402552032584040b0314004002c450402071040014094030b460100701200710340e580031240356a5800d810303000e005203030344d81000d40c1e003140980c500f00880090001c0c1c15802d29014128a0100500c002c000070319080e0f48100e0f1181650001500301035403142186400d031141e0b0300c0f008207990490f0480315181c109103014000795200300e402c079101b402103500c402c1c603a040c0380603800c1c1d5088190b400781c40701c180c1c0901403000e100100a00102050348840d60045107488078801050501e000c1c0b44036900444480001411501442c0c2150a010701040110103803168408a0700500c41c0300c0301346129058032258012031602d807040c100681315001d404090303056075030001050f6404901c058000c0c480341e24803404240d81c0c1c0418aa4003500030074441c13052030886110303030400e000c00f1540d4034008001c0c0fa182c40202c1d1521051180800210300384005000a501d003035981401d04010844044e0310742801e1503400050100b18100b11020b1000702d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 506868282 1250 506867032 506867041
    0x30e070b2a070b0d0f060923130b0c0306030d050406091a07021804121e0305090a0506090a1a0c1902150c0a120b0901050d0c0305010c21061508 63
    0xb481498001c0031914002902c5010340283c40000b460307418020f00082e07150002c00203a010407402001d424441c284218084044103200c0c9810081c0c00404550004800550041c0004d845884040c05803090050f403503100c0c43d0010925162604040c691414001c0031300080150540c0711803140241c841081c0c51413450303c003a41c54100c16000c2e040780250b20207140c190065140714001c00e494406d5025240b40240044100f0041c0ca03144102c0286028801140d40039130003c038040d4101a070400201c104a50001140e5160241403400a40b00400c00ea00140f90000922031501085203400341000100c1e40c2c0d0342405107a0b010544030b910205120182c030842e070b070442c0e28002d1005940e03840301450b180301586045d20440d04543d021541c1c40002ca00302c29415030750503405114000306d1900190034007800342d00300300810034008514a0304846011103890302000140b020f01644490700303110f40352414005400400c500c980f49007183e85203140e41c60b00400300250318801e00792058102c441d0030626019100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 506869532 1250 506868282 506868367
    0x40b011208190e10050a02060c0304150e0309012705090912032a1303022b05030318161806030602070f05280b0702150106030e070b 58
    0x2c1c030280d040e00314a42c80510780506400907500c1d4100c0f4800c854500111600f48000ea803030303001e17807040039005a022000044a19541200840c0c1040c0503541104a94000c4030390ba40950313040008115076908046405d0741c0558002c040000302d614070040b15540502c4940d01e07a08500c0681c800d25128660200114041c42c80c1803228620300505102100d5803460441419a540c0041400c04040102541a200d510a030140181c0700c007594140b4800380c82d145107408002d00d1601d00c042d444850007801d005041d81c221001030410361079104402650303e030329240c1c2000120900c0b204125040341c01c9481c5190045680e10312002c15140c040d8040343d0024805d03640c2078001c02c0c858000401080c8006144003e003c0381c0707404106007521403030484460100c4003505ca0a590142e15604c1c05140480c1211000500000040b0750300c049030b031040302e5070320400e18000e0000c074200782d1140c80400e5a030f0401c001041310506c14007004d001a03100d13003071401a19004816400d1504400101c100b000c8480a40e42b02a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 506870782 1250 506869532 506869537
    0x90311030f030f040f14060415060b190e0a062d02120a0e0604032001141b1501030b040c050f061219020a020d02060603071a0d0f06090e15040b011208 66
    0x1038006110046008450b0486c5550345002d840c26a2a0a90350030f0844581029008010a4a0010301180d0610000c400c0303038403c038600743c40f6510502c4000d02c5400401d0b2982800700004003042e98849521464000c00e01e03101030802da00120000c2c107400e03030f04030000c1c4d0001003000310800c3e4416196a14484032200722a02c480e4003c0782035110200103000014041c40d00150240000b00010b0400d080d00718070010b56141c0703402c5103600310400f800d2011813811000894100b42420324071007a1080c455294510311003011090b04101d504150030024003003880b00d00d10480d00640000e48245820344201e20000f081c40c000c800b215015410240700040300c3d1020b01c000542c024031203050a544420032514040e44481840954800500c603200000c0d110b0720b40003561004032090800300c40102c00500018079443c0e0700c1001c0f074101d8139031600b28901c501d010500c43c110040001440014600031012409410300d4288042c0310f2510300380f40b05010215005034040d5045030002260303101020524500700c0c2150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 506872032 1250 506870782 506870813
    0x10050301050412110106051507050f1c14040303051204020105070609030305060f010c02090c0f1b0c10050c0c061c0203010f261c0309060f090311030f030f04 69
    0x650822003440100030315009400442c03500742d1980103481404d07500c101c1c200e0b1568829140d0040e1462040413003505844010840d0354064001e0310250203282070658600b4040c01c421070056102e001e03600006941c096404504000811152468186991401443d0303000c2c24102c00102031130305000c1001c41e07020b8021140c1c1c20307030310503003d0040c080b290801400400302101c0c540e019500107450b1148641c03058081103144c990041909105803550b104444e00303904400103000910720b04001000074041842c4101c242010b40400400c1a803c0c03010a00882c1040a82e52400703118050210a20105000c6000c2c02112015940c0540b20800101124000c030102c4111076003141c8004002700303400c602c5084040648800d047c9580b080d003000034030b46841d00050522075106420103002e10711107580a05214550410500c0c0c0401d400d62551540030899003880d04824039030b951000c1c42020190400d81c10f11078106081d01031400e001d4000540003462100034409041c3ca41081c0c00101000704140413402c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 506873282 1250 506872032 506872039
    0x3040e04080904321e0406050a0e03280f120e031e0d05180a060b030c10271203140f0307020a110d020a0501050a03061802040f0b07020303040e1005 65
    0x16289104d20741c0c2d00d00010390604800140f45180000e10b001d96503031440f070541440046108095680b074070340e000200340c050030300501640c4070885103044500c00c1001e065071440070343c1c0c0c1000c9400400750303454115140413100402c0c800403002c5001245e82100c000c881e4800b20344004600c0e80c03003054446041d4414040035800f146031100050b0340300041d100140006d900f1008080006480c0c51204420025611500301d0f01c2c0d500020360040084c19582041c00180c0020703040743d10085e40e28000610344219045400000307924004000f102c0c1040e032040140e940301540078401d186080046402c4444104c1c6406418000c000b00001501d0340080c0c210b030030340c604100703525803a8201144000c0d00c440480704150b41000b102c481d800c00c1c41c42d1102d00026141c0d1700a00840c01c41d843c0c07000645d5141c006514030020300d90f440100140300c800f0110424040000d1480040e40c5a080c4041000d00d00c10b1a0030035400c103081032140c3d400607240001203d0565982d054082c1050703440031510407120f855600220341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 506874532 1250 506873282 506873321
    0x50103090c0b0a020703052103040213090f060b010201050f090d05160c140a06140703140702120c10030915050402220212010b0c0705040c0e04090c0801060803040e04080904 76
    0x103401d0f404582d03175090764490300642c0d13070400729254610f0104502200060644500300003040061a001344080c10322298002c000c210440c084d1940f22000d03046003425a00240c480c542c002413036a0a10990381d01082c40c03c80f840306402c2a10107140d90741150301d440401d0050008400085149a1031600307910342d40111000c041c95159000c00320042c8000d805d090141e1115403003c501107024100309045800881c1c08941820500d0710708448201010b00b0b11450a007041155802680741c0d1140900702620351070040c04603503164010700031070750004840b000c205840c003000d440000d0743d062640e03d08000c49600100d070307503187c900005603000c00b800b034904450304c040c240c42d211b03440c2d01e41c000e030442c110700e441e0303100041c1c4ea102c0c0456407620079002c1c0ca440503005503009000c1442c0640c0a4801202c00d481c20280107920761001c00c044941c0a00280c41364504180c080040c06001d0042c00050a12080a14107003031a00b22000301615002c1c0c00103144141c0401d2030700345900d076035209511000051600d8507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 506875782 1250 506874532 506874547
    0x3010608031b1c0203300a140a02091c0c080703030305061e0108130618050102091c032003070818010e010806030a020909070b1c060519050103090c0b 66
    0xc0110581e000d9440600038210505076228152043d14440d81280e0003640c03500e0206154034103c1101d00d0600c0c50141010b18810340300c050f01100d111700c01c0010445c00540a910720b51645000d032001420110081d0040000c04a56200c1d02c4a1900c2420301000108a02c0b83c180b07000940000140c100342c0c0d90f881125000424035500d60019400b480c000e5407210386580030184800740d8105032503c554045680c0c1c0010400c00c80c4640c41100c4190700036000000c24003498501d6030404142c400d02550683c0d004034407481249414524449520003040280c0c0f0443da460380c0c090110741c0c0a4000141d0060a10b20340c0500c04000e10407074107241e50040d040e542d103424079140407100c0c0b151414030500003050410051141c0d4002c90b4058010000140184400302107a0f080045118000304419030b140a100b10004110451002600300c0341c5101c1c0a0300c920f030329003000d1141110555840340384500c164412641a400700c40c0c2d407110aa900a280128003c001e0703040007408103202d58850f6900c000001a0708 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 506877032 1250 506875782 506875807
    0x3040b0106030b0d0201140309100c020d0206061c200a0f030b0609070203030a020a02031903021c0b090109230702060105030706030e03041e0308070b041a13020603060301060803 78
    0x10341641c4003500d04101032000d1105000d000001010001d01086094460b5800103090b58050340e8061040d070102c50300720104882d03070402e40c1e0b0078410380ca025a11501461400b00d406001d65a0710142c280c07080101440710400390510264129005040202a21043d0001a90302c01201d501c111001e803220040d95628440266015014401610b903581c2800100780710b46803803c5054011748032070b4003c50450722400d0100000f940100001000d62000700400c2a5601c00d800002002100c19200141c449003440b101100094000140c14070041c6003804a40c0d01340d85500c2d00314150b900a10700003802d0701300d401c117000c0c40f0035210320001c0c481160398007040042c030347c00100b003416180182c040c0c4221942c1d444096081c1d4220041c451110b400620040c008143d05070342c51840050050300c0c015540341d4940b40d95405600c41c200c140d550740883c004010610000b01c070107039203c5501e0070107640c0ea890310100321031f0b80281150000f80301d0100040440d859580940200d8003a02000c0192aa140c5509817030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 506878282 1250 506877032 506877053
    0xe01030b0106030e0328110f071e06050a030b040b03100b0f030c0f10052a150105030d032c0105040c0501020d0516050712080909061507060e01110304 66
    0x60b40000303414000c0890b864100403040d44c070310340e06d001611170400b940b99619041d8512040d491000300480000d08220180c001c1103120045240d8034042c0c40300301c0c24005241032461880c5810b002424041c441040802c1e489400c4404103030451500050109403500000d014144005403d40d0507c00d061401e082c03d07050b0b520010800d14115480303408440343d0704c141a2244045135105e903102c2c0302180d03d04818140751100c944040c68510748140780c06002ea41d540962905803010120750520300d0790300820b0f00410030459440e030784005138145041d894080004d55910310f00b0f0f000400c00d07803201207a0315044841c5205030b4202044942c01c240035401e6544081c002c14080b94166001802040000342c59400440e0340d0841c0e5215a41d0702d850000c0c10100980c1c18510078200319900c0c030800d800001e802030282c0102041e1842030141c2d0380d60300b140311f040207000c40000d08241d100b100040107840038240d03440120740026038441c5002c50030340c8103403414900400541500c080d040c40004100320801040c02070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 506879532 1250 506878282 506878289
    0x60102211201061b02040e0a0203010e0f0601050613090f0b030d0f090e130f140703080721080627130c0801021219151502070e090c01030b0303040e01030b01 69
    0x481d1486070ba9a001c129054200300218030780b10810518104050b04040d00b02ca6000030f0300300e0071074400510304d9010031f0844884400e092031507040381c07104c4800ca0038180a541c0c01003004441c0c0900b480e00b14400108114003034824501380e680d840c0c038000d008004540103500400340003401e513400c0592030390020b0244c81081c1000310001e503034000d0119142d00b8044015020300710412401c0c1c0703146407541c2d8031000c01d034841c64151b54808043d00302c03840d04032082200802942c07154071081d46400e11440c102c103000800900b0070900c07440c01c82c65003a500350302c80781075548541c0480e0416600450091807520038101940745a50030b1551008025564a20300c140c558080c4c8600044038900d9510500d9500304d024084030241000914404103075020000c03003486141401500380000c080040c941c000041d40c0c55603003c07600844000402c80300c010740502c208401400900312464891900a807456110a500c8201d18107040d5500000030442d00c0c1001500c02a1041690304021541c50741401c0c08040400d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 506880782 1250 506879532 506879557
    0x140105040605040905070302040b1212190509030d0503072001020a02070b0717180607061d0d050d0504030905030a06140c0a05030f06032109090702210306010221 71
    0x1e002550b0705140c42490102c54000000c3c009450640d400c000140c044200040d0f4090405c0f080707400c04520a00003407898a2900c050140d40b000130410070002146240200c400344a0148407041d095200441c85c1d015100e658a0015903075503410a043e42d00000340001c8041e140080380c1078070554181540200f0b0740b42040d8007103c800913550004036501c2e2182441c01840c00c44003c50f240e100d888500040d001c035903220300714000e014204001007102e94100540035074025485a5104070380d81e0080440380d14844030500900402c142c0721401500d0751052007230254100380e50348005824903108065a00c0a4000201a00c10355962818600d0141c2120550048002e00390800300d0b0a412848084030006600c6031640d40c01c43e6103c46040c000d00c0c2c0e0050030b841c3c240c018510b15001502d0f40c05c11110207032840810460b141c2d5000303401d1100c000001006041554040010072480c080300207405d01489043c1191a40d40c0d64540004034103041c211030382a440490a82d052000404c2c9440c040c03d0310a9584 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 506882032 1250 506880782 506880791
    0x6010302090c0304170d020f030f0708090d20151608010602150a0b0a051306140609090f100e071707030507090b090103020f1602130509060f040f0614010504 69
    0xa4600810903c01914024a0780140011500949200e80007810280084600050510440c03400c080516401285c0c85d04010604170104110f80360045031007501b000302ca100a0100b1440d40401501e8000d17850742d58010b081c92b5030707500e4406842c00c1100c0e107000c900700e10803403c440c100b80c032601c4c48074801071000d000810040d84c00411054800181d004602168011040154980b00360010040542030b142d2500800700c4880400d50703440d001d02c3c00c10b107038646000c0001d45a02c2c0070213a0540042e0460700e14405c580c100300c0080381da07507005203884d0003c90341e603500a5242c84003000e0780034500440c0e00083c001341c1484100103d43d500711408040c3e04da00c810842c540c50ba52820f0442c1164070032a03c842c0440c00d2404103200000303c00000d84080101070500614050741010700c00b8098001c50111402c02c041c0206010841c140032848140725040c1d40c0c03082c000b500b01110001d494940007005120710114480024003030085d00c0f05413095494203c0350800c40f110300300c0007070808020240542c90280741407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 506883282 1250 506882032 506882041
    0xb010e1510050f07060c090f1a040e130b04030c1e030207090f060e010f09061211061c1404020405060102070315150f080304140625080c0a03020601030209 68
    0x5010300e103800e220004104030710141e1407500a6482c1e401c0b0f61030303c0e80031183c14000036002032903500c9002e40468280d21410132485c42d181c0c42e83c0040e0201d4119415407c07410390b1401e518142c08080c2c0f019030303044014962b603039560840d042e814851503150207030248040500340424150468490455103028146900c00001094038902e40005011001001640144020015003034180d2100003180000c02d030210b0080e9903450f0b4040032a0080c5c00000d02c049411204100d0340e8018403d220040071300da607a540035190346842e429280528141d04500455001814046501040c00c051088400508040040050b600d901000c0100e003102c049003d1450100441c051350700001350642101c4d4080d0743c5001c0041c20882c21170280c1040e0058540d409072440c1d010034400144101c440107080188010764442d071a04007890051002440e02900850303041210010308042000092190410140c807407140002d00d181c0f2404030b100c0e46100d48454041d61030501c080581c0442c2c0c450480f03000302c4048155454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 506884532 1250 506883282 506883301
    0xb0a0903140c030703080903091e0301051605041404060b0d0b03070e19021b06010e100b03060a050108070e283008070506040303050a0e1b1c08070b010e 67
    0x80c031044042c0ca07a00600000001038402c0d4050340c1c0c0031010300c0c142d9041c514100003203400c0104c0c1e011842004c1640340c1c002caa03681004d00c20a607101303107180d003080c1419084c81c10140141c403681c09a000864200030b1841d0f03032a00c994200100a1480c402d950f0b9840e60100794520080c020404a244a80520040004d018a0122045000d40c42100441020741a07140d58000203600a02240b0326015040841c10718280c0144009402091a001664003a04e03100710b40000e0061150440c18009809205202440c0c442d04850301c15500c0a08000301c154072000380903030b0419403250000e58404800d4408010300e5000c02540304000014003400e030020303610760907064000041390201c41503011040c000f80520386000171219824600030f03c000ca142c1030749034581c5030034410212410740109440c1c1d0288608529180318450107a10000c015100d592500c0001401074194440020320845007000807903080c40c40980400207455005001c0c1c0d56500e02440c2107841d2210134402e0035001050803000840d40c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 506885782 1250 506884532 506884537
    0x10c08010602070506070606080d0f02060106021c080705090d05011b030b1c03120f0522020108010905072a060b06070b01050d0f050313050f060c12070503070b0a090314 74
    0x7807040e0007400286051009124890300643c0e81540e15070b480b654009601030042c8200c804401c1c0c240d0f02c3d0200128025806460002d06a11400071036200f450590071000300c4964146118070146480d00007a25079117400c0340c0b280925951158400c0140d225101040015445400f540c100e0403004410854824401d50403900162081900b00305181d4018181440031103540008910030f080915840055810000c11114040303015200140e640c410300520040c2c42e19030300b0212141c1402c00a00c0d6000c1c2d40000c007540410b21a503a40c3d00d40320004a0b4903e80100c8004616145e0a142d4411143c0c0c4408100c05459441c5c20645039a0303d800070150381810305070100d607222074100b13009200e240d19250030b008162812242c2a0740040c03d10b0303d6000090018001000c0280c80c6441c0403844609003010040c6d000074102c0458407400b02000f10040180e0081014404400c860300c0e81074951606080c424103504c9048402820740744e950003040b0031402281c3c05101013500a589265001611844450051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 506887032 1250 506885782 506885789
    0xd1e0207060801140d20090a020c0307120915020106030c0f0807030b0606040b040e0603011a180912040803041509060503040b06010c0506150f060a0e060a05041d09010c0801 76
    0x5a804001403007132001104803420525005403520003254055103d106e2500c1e90f100840c2c000000741c2d00d00308500d19008080320f40010300c1020461414520940f19541d030311071402c004180f10240381021344070500483d0a203005040400ac101d520280182009000300020b0204542c080943c83c000316a0a40381500e980507035244c040101081401c41e2a0b100c00c05900070301e00d55000d0f00401c804181c100c01800500002d203280c0e004404542040002c06080d00d0344107610010400b400000c00b002a60380c06481c205d802c0800356076110342c1d2601141c150400c59441440c044d40c1a000074001809800003008000700c0b100040f80c15440e00c0c0d8001d044079072140740c0c410b40340007032003e002044c0030a200e42d44190700494141020401c0d590569541418210103c0c0c1d4822010102041c1d1000740c2041e5031200e4132340104844503481e0031080303507010703200c0390101c92483d020f12004504084418040c10840d400750080c0c0c0e107595810703081514051205d04085662540315401e014100100c540100c0503141038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 506888282 1250 506887032 506887037
    0x11107060c0f0804050307060e040e010b06040b070303090f03080906070807020d0f03151806050f090a0209061201080a02010e090f0121080f040f1a0409090f050d1e020706 75
    0x40c2105498010445aa00200f0768118408000000d9556000c0020100620841d110100006600300410089494000c0005203e9040c01810412665184100d8060b91211003507a507c4900c282070490040c9240a0010201c82d140e0505205050700981094460201e40040307913029590204101c4050600782c0b1620090b0780500c00c00111180505441e0305140315528000070300345007404140700c4c504400d0348000701020200030a0701807480310340501c40140c58255031004484142a01280032a88000c00c016045c1c1d5010810000f26642c0c00300b1104240d1590918040307550b110071103683c503204141d40483c0442c0a4400d40116810100c401c00d126401c0f0302c004003544e81c81c0154103000c0603442400b000030428405001c0c07001030b0004000d419462041a051500c3d00d0a0200c41e000701c4025400202c0c00d0000300010803000b845410407501516096100130550050340e00d4040c0030702480280090a9008404018054680c840da880044049400820460218410703040c0d80314072160050200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 506889532 1250 506888282 506888297
    0x1104081b04111210050303131203140c0d02060112020d030c051e0c0909030405060d0c0504050604060203030a0c052505150f090c01050f040326040b0901110706 70
    0x14612002000303811018405032000c00c00001240c5100000d9014940705103120403100140441c1c0001008064040c01065000b1482c010070050b0401c2c035520305100d5062521088407540c400c05118400c004c2444599001c51512081405912134071104014012001441600000200310303120700c040310705594000d0943c0324407411546040390102c20300e190a0b6094854800f8921030000101040090030300c00d08082c00300e5407030050030040b4001001c0d1500700b20342d01c24031040c841c643c2e5980c12901d90501d81c42c00001c80d542011400c1d5a180920352000303074010008a030000b0305980101c02503110300c52951040000d40c2c1d4192054a4a000f00c01d4401142400200c41e00007003008200050038441c001d03811140d0034816a641c1d00064001160060540480e42c011f01c44040d10030010000100c4003400c116040034458100100c0da40500e200250035460038140380d01c1c0d001ca041a58400d0800500541030307455403550340b0391380c00740e0003120309a000a8844485280072000410407409075421a5915003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 506890782 1250 506889532 506889553
    0x623040612080c1e071a0705120c071802030603010b011e030c120603060b130501060203030f06010e040c0503220f0201030b03150702060610050306030d051c06090906110408 76
    0xb040780c000c800e08074140d210b000502a59600310595403a036440d001002080401c3c1031802070860940546011102070809014140004402080c001d80c1c1d0348450041c5920395119100d158544001607201c4c50400b012608a10480102a0002d43c805c8005034000d0040307a1b410001101c4a9405207225842e5045103047c81d04814860340085410001500d000000c1041c0442034500f03e4119900071119260768040c451081d00f007440c0c01d000640b101c400708002e1b940c90840065280d100050043c540b40150304000340080c3e0161035410900000079104000201c881e4501904a9000740c0b0b1492a01044583d00340407011520010300f0f10640c404411002c03c1403541c01500500902091145d16000d11803003a02c4094221594512231038166004000343d00b00702081c4017842c3e03c10001c2d101000410000c0000c1510f0028480e01d4081709843c0050740c581072040c100900c50301c0c260398104000d040c45000244540290003da6020340a400e040000300d410040c0140c45115074840e910b0303690004d01b03004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 506892032 1250 506890782 506890793
    0x70c0510030b04060f050406080d050703080402012006090708030913020f1603080406050c090d120210060603021e0915030402030a020907030212010509011202040518010623040612 79
    0x16402035181c28040380c03000c0c2d1000020141e03030254000e0414028102c0c0d08100d50314060040c40300511060000d00003501000304010168400d5100280501400001107030440e4402c0840da00b01c0c0003040ea01c0c55206191042c041d0300c1d900c00352a20040e502ca200b8001c14800408012901c082c2c070001d1550710301c400c200003214082e401c140c1c00c1900c0a0000c0c0b103911000441d61030b8080301d0b0380c800d40d5102a036152a01d004400c80e100a2304442e40d8800510400c1115203c6807100c040d80307604005a01c0d03000400c500200d2504000300314018046040c10000202982c06401030503811804080c200108420062203081602075100174030b6100c000e00c6100110840c00310001c1d908a400503041c2e405500c1141c01040703548105503522030000c0d038002030b028055800800918090a03040710054281e5140c0f00c040503a00c0304080740a032259035100003103421514840741074050240248028025696035424000c0006805101c8280980e108048441c4a01e071a21803402600c0018051000183c803580700c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 506893282 1250 506892032 506892049
    0x30901020727020c0307030f09050906041d011817030903040510030603051501090509010b0f040f060f030c0f0b030f071d032e0504020f0103270501140903070c05 71
    0x1c0b0480b0210040350b2200c0310355000a006010a1000450340e071215440c00400da0200d0f001c406082207003d10050000c4d070348060303055800c11307012140401c03600c42a8003000c0c0c603981eaa1004881d04d40c0303495103042d1201585009182007074040c4c00854510718006c0094001844103c6d2414031503001080305000d00e1070401c3c0c1c042031003555441c0004185031640d540350f00e0030145e0080d00441000e16070042001000c5800380543c0088410024448602850301181c03400704105045441943c80700d007060424240c80d84a00d00400202259140c841e42d6401c4c602c5030300c41c09009821160051140206080782c0c40c504903805040c05102c60512070b0b46044049451403241215100342d0ba401060030138641c0e80420001c80c101c60240e4003500c140041113520b41800c0703030309a2a03940c0e45040004100150341c901e0b61b4100080030070700340403800c0202c441d1302c0c244130800d2007425a042a100180b400c18081e0542c805082d82c104c0e00e250041c04e4031025145030352800b07a1200203040c10410b00b401d00c05070030081d0f072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 506894532 1250 506893282 506893319
    0xe010e03130509100305010e010609230a1e090b06091006090308090d0813090606020a050a14010e0304030506070f03060302030a03210f240303140306180405010b0a080309010207 78
    0x41a440c0162a80e0300c11f404e407a0310075181f4160740e45544040c8101c8074580310710401010041584036a009035005440d081c1c000c001c280c051100d0351112803c1070000078400502e0388118100c0d040100c000140391458440005a070040d0149500300001480b540d03884c4000c5041e85c00c1ca803500041c0519540c0c1c0c0354810745c403150410703070480e0300101c0c800002024a40038000c40980c0c00300c8041e0385400d14980c1c10440b82e0301d61144085610a2001d4000f0400100d000e42400d40c0001004442c0e041501c202405862211044038013440005400400d1110116010307020700410f650781a46010f041c9012402d84803640006540b6400030554000017034000d9804128280328040301c030013900410702c094421129050004000c1a4658403068514186480b102c0a03070311690300070008842c01d5860003000d403252031451062040c000408201e003580d5104400b00070b121b41c2c400c001c01e50b01d040d181450280c6070b0b0501c3c05000c0c608241d4003180e0311002100740c94240d8030603402001007078503001c000d01082580c41e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 506895782 1250 506894532 506894551
    0x3040e09010b040912180b0a1107030f1211060c120a29091e07050708040f0303030e16032001140a020604031b03090510051204060e010e03130509 64
    0xc0c0d052903585940c0541031605024180c08460041c0c0e0710b80181440c1b0920100004041300001c003441003c10040544021380c4041c9004800710014480e51480c3c418150005001425142c40f4441048040c41c900c0c00c82c4a00c070395480300c1c810800b1110395a101400d4a044050500c24840b500115800c900410b83c0058200808600b802c4100047d0380080c200b08002180041000c1c14464503007071018016410903103103c829500c80e00081e241e0203c440303001e00558208880007410f00c00344400791047e41c0152900090b81d0b1b103803a660b8038000e4000c10017034580c140140600c0911099402d0b20880310300850744c001c54101d50301102c41400031908803444460f00e05000c014050042d03102403038030251007406041d80040c103890502d4100070b0302101c21005915800b10b000240c4a0000e03910403a882d0440764240ca148403c5514620706440602504041c25400c0c0342c01da08100c00d0100c0340e040b205490b02028000c0000c0c40700030030b04a0300c91091540c40c0e541801c40041c100103500380360401ca60701074001d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 506897032 1250 506895782 506895791
    0x108120c0d030b0612181b0f220204060f1b030e0603220b060a0e0417030417030712060f0b0304121407060501060306050609010c030f030b1801030c0902090303040e0901 74
    0x17484a407001d000980301000e4500d0590140d00340e08108100b8201e10707402140003000c02c42c841c41c00007030f802104c0d0981c0d140246c03403030900c0140515121095407000000c9480954413240c8500000b0100c120f040c0d02c1b1400902030481c444a501540404102010307010381c0c1700071030400d0744400d01040d0f41c03000d40846144005100b030450358585501030000590f1181c0e00e402e040341011401c1111a0106801c00e005000d00c2c0410f00c40050905140b14000080700120795480e6075403800e2441000006101c06152004004108030025070711850100c1c1d0458501810800642c032030094815415150040510141e01040410013242d031020000c0316000040c9001007100c280300f200e031003694101d5030086403038984890040c000a60107000305070162070250340c1c41d42007022120000f410040c0d400740c05428803460400f003080045c4070ba00140b01410020302605030380c48404000e805501801d2209031914800b440002c08c202090f80219112940020019414981001c14170004140c0290800361199600d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 506898282 1250 506897032 506897047
    0x3080f07120207050102032a0307080903090a030f0506180a021915081e040f0b15120a0302010516050415121109010f140318070503060f0108120c0d030b06 68
    0x750b00082040364415800540c483c2002c80c0e911442446a4018407100104241090600f041c00015254488060b1410301c06c01d49030700742c50a09501c5030100203a00240c9800b0b000c028082c9403041c09034064491001c85a59a030781a59098680800388808200b41e0030540b0b048000d881c1070165106410b000144100c140782c0e4801d0a603100700e900345245000302d500c0e01c0820004002c0c0c0102c0f040d900172078050300c44c0703540303031a039104602400c52090007880c51400d40041040e0710829211039201c03140240c510b42404040e091510350b18006580e0840040d82003c000428440300384240c10b104a115441d824103041c01c002144403a01e000703110305402c000302030004861820050042100a401c084615a036800c1d40000040190700300c0703802a010b0105e03018070221060900c40c00c0b20340c485a010801c03400014103030006410040c5542c003c0e54940314607424400790001842a00d8100e4911001b21076044030110b0020515000d8448001402d4000321142020b00c0e00a401c4900031000043c03500b45401c0f10b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506899532 1250 506898282 506898317
    0x120507140106080d020f0109081b010e0f010b0310060503060126011a09060f0a09050c070206120a0c0c030c06020f160b01030330020a050f0a020c1c03080f07 69
    0x8041c0c1c0140c0a40d032062580c6130505405109001c21800694001e00920080b1745691565108110103a448a2002d80e401d5115900c2036000c860000c0045081d5803802c0c6c80308032028080c1100c090344512a00900480490f10b180c40d1280703000700d540c06005065203071318019092000041c0500080c0c0c0c00c440c20500c0d480c08110a1117466254000c800707012800c044150280040c6400c0140540d0040322544001c1c2e00fa50313120520601200c7e1840c8000c901945c4d60078861426004e40f4030000d4000c800854907414800140c03282c18840c0c00f0007001008180c10845d41141e40b003a02040190101d1054540341011404035001000f44280140c1618030b001c1040c03284079880380c0c01120903143e00c0c00b150014000c040d80b200c1005d40000c0207881110180045464650504400c559007845a40e40000c411079103501602c00c0c0c0d0310030071080c00666200d060110010b500e945e031482c041f9210740034001c805031105d6201c068004119800d80d032107604aa8589072040c450001c003400d088180142009034030901c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506900782 1250 506899532 506899541
    0x90a080a0c0e0106051c090602040f0303051236070e0403020d020c030106050303090409020418050717011e05101e060305090d0203090d0f0f0602090108131205071401 73
    0x2480707001d401102914280d085030403100181c1013401048000c01001c0210070000f000c5000880f92001d0000b10705d0914500400280700d5681305540c551200030000003410303001005131500104580424071155a40c1c0184e80942c00c0040781e1488a800071840c001665203280034040e13420b200e11045809240d121800d03114034400c101c1b000c40050f4019516110480e6062007002d260b40c3d41075009104081c2810f001907201d00070604000e0081c0d5903422103005550b2942c101107800d401120401c00c550b2450708003180c403007441d401b800514085483d140c0a441030140302d14065a500c0006d00081742e40c084804c031003d000c000d0120030200e000d5001c04980100c44121006101c0215440407015a14140020701036550042107403145030030954400b250030b81c0100c2280d4036002c04a071400f600344c0803803038800e071113020022000d046200e244481804100c1c0c641d004242c4d49200b41c9603240300307a9400030303440d0b1803120b2140e0080042a1250300b4034815030244001d0001e0a01c01c141c40c10a103010144400c1c00c64 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506902032 1250 506900782 506900803
    0x50408031503161703090a080109021503040f11041b03063b0702031c020702010e0405090706030b0f12210f0301050603060d060903170105031504020402090a08 70
    0x1900006000300c144212819904015041c0d016107594031811070190b0340301c031440c0b041c40b1200315000c42c401e9040d0414400c4401601009164800c03007038588800a00038060044220302032002c0c0d501c4841100c40b5007059070310039540011901c104410550711494442503041e03d1135000303611a407100d046a8034842189035184c02c1aa40011a2490134102c1601c00c0036105095900e6944040550a203403590764600d134980d40c0440c43d000050302c1e544402c9107113118800920240721042d42c44002840c0c2140c000b4400c0c14001d1340c5004606000c3e900b0041200c10981c0c13b6440790740188010001c40380650401c40301c0640040042d240440c54401061139418035625441003038000700351031584c20360100301803042404110b0180d428010010007a4125120600610380301d0b181c0440007400568440c2400000e40c0e5001e0003d0051020600d005008900c030307407150590391515480081854140001c20419040d070040c0000f2480d2100d400740710096003c0604141c0090740303400085060481000605400d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506903282 1250 506902032 506902043
    0xb0f060d05060907360f06030603061413060507120e0106030605070810060c05070f03030518040b130f02070206030106090602190f080c010f0c03150b03010f17030903010504 76
    0x940791020802c03c603000014102014850907000304030014a240846001c1000380084e020a014142e070500c440c141d62680c04240d04003542400850240c0e4140c000000726407098a003845042d42d07100308800c6000003140d000180301c41848072074020641582220350011203d04001039540c0702c100301c68054400f541c3c407100560f03444500410420446110f02035200380c1d00d14000c9038070304008010451881c100e105410030003c1c10424102804402c1c09080010503034580401c1e11681d49150180494203c4502c2e080e03084840b800c11012402c1034040c00c0d91004000b09005014100c00c49404000d045843d641403d8903802e110740d0700180c480c60002d501034000e640ba4003d140746001c100134500034202ca401d01c1c0001d490918140000d01e034940101070164004d9109440d640035025290060102841041d40a03040024508403071382c065010381c40c0c401e0f0305501c8030542c079101d940141c0d29100c203105440c800340160b60200818940e604e111441107201d5001d480c5001e140000090a651054905466 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506904532 1250 506903282 506903291
    0x1009080115080f01060e1b0f1b16180f0b04060803040807210b04021804060b180c090405060a0906090203060109080d0807030c03060305060903070605070212030601030b0f060d 77
    0x1041c030100843c504000941c0000e0082500340184082e01c0c41002e0501d0700c01a00f001440d015011703040c019201d12140c09090726440e01401c140c0b401d407800190a071200540111400a10310380d031455408010b45409486032503411344030074545001061a080c8141e43d80d9a03507142a406a560ba00484c8014800100250345441c00c1101305800c142285d8803100c06a4100ca6550200311030b072911107240940c02a0300c00e07000359603600103e40843e80c80185121144d03001c104000c1002a20741c821000083c065506a4403101c441d1803001403864240e41c8182c543d10305000e041c000d0310303190700604d60025000d08040310550f0340d002030105961903500480d000a401004000c66075030701c03190040c001c040810003003240c4041840e001d0401c0d880906528101f41c0c9400c024800c01e80203403c143c2c000e66101c02118003924242800d1500c0b80c00003001219000d007040c2c01b0540c420b10000340c411040c200340500504d55202c0e10019002800c055400540050341d000ca0707020b890f580e1a01900104c80c22520104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506905782 1250 506904532 506904539
    0xf030c03050f0a170a120f0606030501140906120a14060108011109010c02090406110f120f010e150a030b07050a1103160204051312050d0501061d1009080115 69
    0xa00700715906070000c02c164800f03007100012841c80c0b090220b09180d544045aa2688119000c40b18a020740d0500704006040045207001c0c4411076124404480c400d5030304201903600d60070300f1042c003641c03100c64540c0030025074046001483c1940c0764041d440f0010049400100c0349030389002214581e0308d01c0c1501c941100d0010030007442e0a001e2200181040c04149240c80c0800700003a04001c0d801c1e01c0a809828108005010003010ba0b101620500500036400d845151381e9021811940c0440001620482000003240301d040c0c07d43e44542c162101c9180090050b07544210700d4100711498201d4540c4000c0d455000000300307440100c401d025074038075a22540da400851070083e1101d0700000d000071003603004102d5900e07800441c1c140c2c03134500b590488020960383c171a40b000000406003007801401c600c14107407082c0c2d101030b0450300034101c0f0f0149500600070b9070ba1f00c0100b6075620300c000380340a1440c040410340102d0741c644800507801607081e5041000d00241c0b101007081c2107449070080006141640c60050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506907032 1250 506905782 506905793
    0x9020d0612050d11060c0d1a1f200c1018090911011103090111010b03010c0201241805060301020706060303050a1205012108040b0313020a0503010e1b0301060f030c03 73
    0x50340804940e01c01417280c1d080001c100c80a9200307281c40404c4c090743d201103804405402d94a01c3d00c100da401800c1c0f1600070406441510b200b00d080f01c2030300c0030a0740b42494124441c500d113503034001c400c59880a8200c1d01c0f071042c203110343c1c2c1e694004032404221030300020f10b0709c042c100301481014180b00b1f800001c1c0314485150411510068186080c10f0107610700c6990401c0703000101f203900c800002c1c41d226801d428460701480c05003030f2904005d0751550802082040080d4154003090303400c0b0410300c00740226015081301e03094070141802008800c00c44148004200461500055002100131f0001490140540c0b00c12301110b82d1508110001400026980701aa81c41810710060b60300c00c1c1d1041000354504000c3c0440c56800366071820000704108596000d2160000c195001000711003041c590324a40004002c450080d540300c202d1040744503040100c1c09040510400c0e8044946800400100047d812640304480d406020306900d0341d260100030503c000c6950030b41008620a20004c0406401c52400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506908282 1250 506907032 506907047
    0xd05090c0a0506070507030212121206030c1503040201140f070303050402030607030b03150a14010807260c19080d11060901150b0d0213080f0c060405010909020d0612050d 75
    0xc602c0f60b042031010502003807003c00d8800480358121080381140c03440340013041c103018040d1144038600c0400b08951300da02e0302200c0706500c240003c40c141c41200c2e4020741004242c15034920441c10044c01400018019409210140400a00f10036024140b07451002180c100b0b9201000450010307464806101c210300f4100001d94001d0700034101440800c00e50400b0a955000b1102d0190100041d00701260b5440c0c0658010000e12030b00300c80c090000d42c0c40b409115941c90491042015038488101e044660310a2040c0c08a040713043c102c080c001020280041050f01c018500000b035549034003071400a19000200f09020b0444000c0e21042d1100d0152144513043c84402464054141d04001c00d500444c6942e01415041d40d244184d95a20743c1170741175101000b80a0000e101c01d07211315028000c52030180001e03860ba00e0901d81d40c111550250b240081c4100c501032403090902107418964113008a6400da00078011a6044540004604c3d554420480b103180c9502000c1d00c0701e41000180c404141e610000307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506909532 1250 506908282 506908289
    0x3070528120b1215060d020402070b010f091a040525090e160807141921110f09011b030915020604050a030c021212042108040603020309030d05090c0a 66
    0xc0c522031029002602130380700c0000407000070403208600005941a42c4840079145850b4000e04115203425242c41c10030440c1d8003e0290441104c4580d200007054016401640d4100d030280c1d0070300506021000502015040203018000910500704a005000040200c4030030080510ba0356040d07511700d050301451200070040d12001a61078004406061540c01040090b08400103150069281c62240345206207409074201403d4110040c1444c2f040865004041c0007500b0940c1245540b00340ca60200c1700110350301c540540313501010920041c0d00241e205005800c801d90b042c10010300101805c8042000c0c285031000403008181400c2040c0491070701e000341244c1141043c0001c11035801c1c25200e00b6a604540c25000b0104146c4100c0e040c219126280a03040420303511044503000000ca00360122207422a0141140215858051981e5003071840000c424031504950070620301424540c048010b58030050200a4a00c02000b42401f032003031500c20640725a091034083c00445403000108100c0000c07e60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506910782 1250 506909532 506909539
    0x1215040b0a0503120a05070c0305070e06040203060d030e0a090e0616140d09020f120d030c03060605161403030702100c050f0d0515030102070c03110a06020303070528120b 75
    0xc070910894400103010091104040900c0d40c03144001041200c45118070300303008004181c04e8000000b001000111071080e101c01004a0303255985840a110480c0070844820382d203c85c00d0620360000c207000ea0102815004050801c080480d1919a441d003503510b405070700e51140e0b000c1d50402200c0c041b00d24007004c0307c00e0346103404981401c18000d2158203016130b0803a07509031690760b5840021076484a42c9090301d20005001c10210306949807200d51600d001c0751601c1c010a05007000c81c0d076414400d01ca84e00a07520315403a807134142032065204000000c8010800c446805400d8241e0110f49802c001075882201141c5c01005900b0342d0480417000d48615540000c2405010300c076800212060130182d510540c0f007040e0018403684d40c1030004a415100c100d9150b055440096800b05000381ea4442109807400f4584002810680c50180000ba282c076204905c01a0001d0000c5400544150020300030200380000394070040850446219002184500a40109401c442c021031169240e000c0c4420401086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506912032 1250 506910782 506910799
    0x20c090601082809060e03120108010c051b071a07200a050607020102010b040515030601051c020603100b0a0f170403140c100207081c05090709111215040b 68
    0x2102c1403150414102c0302c00b00100d01c0441411580f41c040c1d01071080c10790480005d1141841540c03506440c4d9018040f04007104485500200c0c00701014021201740394025a01d1625140c40c0440c0d1014142e51080a40c0740780c0105180058500c045440c240d509918030001e1640d5007400e440e100c42c0207191240350a8408400c0304642126580e60507510080740c10503102242d0340c0ca041d03c0103c1c0103151098205510500e03100900005030004804581c0703150084d41160a981d0303e807000c000d0407240c4c1c0c440e20160403c44c0244600141001c5003d560400c4140d0503440d242a21121a81d8803034108038582d800184034410015003c643c008420001507201680c03040540c1040d4070001c00c1d003104500414146580003c101c2c02604042120440e0f100294808540300c000e1840d141c0c000d507100340980501c00e0182c43c0c805509c00c03003c2c407490340603103442001008068030b88400ca202401c14801030030070801c0140039501c458601140c1e480d02c900081c1c2000006983c00000700812600e400c40c200740125040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506913282 1250 506912032 506912041
    0x1b0201150311121c030c030b151605030703050a03050a05040f082d040f0803040e010509060d05030a0f180501140c0705060a0807021915090809030d020c09060108 71
    0x21856100c05594115801050a4031118041000c040d1450740d515840d00c0380c01900b420400e00641c2030710028a4035034060200300301181d400c8042e41d1360700c2c18580c0e000001000501c40c3c201c0034801001807820141c1c0b00c5540d803943c0e440f0356003541c0280100341c000c40c00000303942640c039506105982d8880100c110421860078070351140b100000700e500000742030a0000a124007416900d0702c0c2e0003075420100412100c0a01f600c482c0d1035441e0042e2203006210400000c000c2081040031095400707a4107008110241a8642030420004a401520203900500e800d440e404c04100c0a0009010951a40d21220b43d40c079a0948010151360f40008410240702d174414044c0882d80c0d22170001101c201000d100c1545a00da0662413a04110142c1c0c80107070b00040c00a15890000d03008031200d8440e8400707809032220800d08812602e1030f00c0150754000c140c401c154403d851469103903485000c00034052030806007440117400c0401e02d0500410b20000c09607000d130140c4811031400000c0c450b4800002e10b04150541403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506914532 1250 506913282 506913311
    0x501050901030515040c15050d060905010803030a02130b031305070501050a1b06060807032105030103230109060e0a05010f0e1513060c0504060e0a050906010c020109050303030103061b0201 83
    0x501c0c101444d40c08001d04041010701a0012100c8040e20403884000181008a04081d0240c1d015601c2d00701498102100003c003000c0d94402d090489a0200140d81b5542c3c5e0040240e009502c0140f00072180800366a0204400c14010b024621810b001200d40031102154100b8a1510440c0d40c0801d0410904105143d0400d03031280455420701c1800c0c00b64040fa400314508100641810780058001c1e03c1040000001d100040303d000040c4082c480d0000c0a9003503000f030441d2140700900006d0481c85201c0e4003c030440c521401141a180320f140b000249441d002d0341e030041a100c56480001c49680310443c04024801c080c415051f03285920300003000140c05800c8a140c68050001c0fa00800904c01c0c4005200724003109014000b80341c1c4203e081056003034481001d00f040c1c00c280201c80015040b45a12140c905164601c0703019103400034040050b982c0d0303c000444480d12800300481c10441c14620000b2903890801c0514040c600c01c0030040382c101c851400440341e85c800120304500f1a0704240c0324500142 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506915782 1250 506914532 506914543
    0xf061401090e1b04020702130504060504140f0606060c1603060b030c0117010512071d010f0806040201020709020f07050f0c0907051c0507030e06040c0e010f080c061308070806060405010509010305 86
    0xa409513005a1165141d00014442c60340d28940c00c120181070208000402484d03a111070b12440c0311340c21040d00601c2d001429a0396040e180b098420560000b00400c00a150800140c9440c0c1106811280c0010601520b8507002c402c650003264102c0e00c4854500c154a418811030080040130302c0e009502c0c20b01540c20f85203410040c070807180205050040700300000c005109240152402c5909030f548109001c4003812241402d02c50a078051a8410000c15000404100ba07401190142c0c020b0660b981084c100b0030003980821440c0810318000c010381c0d070010b81d0078080c00341d10b105e01401800c5c0064108040c000344200c02410881044030801041520380244007640484651954000078960f8850034150014054000b20404500c0340d103081108200c1101340b1903059602d142400501d603640d079580390900d02401d0088004e150451210b039003950070040064658001510810080c0c6655024441e0a02e4182d41003091f0340d42001c002c208007403d1500030680100f806031107001e441e40c90758480c0c03910341d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506917032 1250 506915782 506915833
    0x150f0e07090f1404031101060504020c03120603010b18010806060d03090e0703060b07060203090f060c34050601060801080c0112020703110d05180301140402010503040f061401090e 79
    0xa544003001c0c2e803120b9040c3d0044100f50241210714800741854240548400b03004103a0301607a60038040085550304040c001d039413100c4407290045041c8501c020744104100401002c090f007541d0794902d420701558584800c2c0303440d0000d40003040610350400d400c00341040d9008000501400400b1282000264002103074011500c0540d02e0380900d4a8420048001d05400c0d400410021004030b241c1c02840b036030b0340c000c40c061010380d02211340058003203c90640314081101c500c4c5180f42c0500c0200324020011078414100c00c40c03071104070603851a0300c3c48424041c0b803044065405501c10390044c000300307400200550150801100600360b495500700020014040503a21801294022170a41c08150085448c034003a52040c0d01540d0360076130b4800000f85942c01c26030701107801d5428454502030504040c8220311000000c81e41c010340e2660785030015102580050400c0b03440c1c41c0302d5441c0f00045030b5681b180c8048500940c0c2580c806524203c9004180e801040507130925800c0344200e0340ba200c144121510b0710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506918282 1250 506917032 506917049
    0x20309060c010b0d0305090112091e15020708131a0a0f051b0d021209100e060f03010806070f1d04110c12040306110309030313020d0f150f0e07 63
    0x1940d24180401c0c2c0580070030b0fa2003d030410f43d40c003560340c10550043d000c1c0000e1130081e030719481c41e00045400321003502d1400c0c8010300f41c6e405002544150100d03840128910900078928140700c010b0241a4804a9000030740c15248400081040906a482030b608140105041c80c01c9450fa0512030022200c03500c41c02d5007000a0203810a0180345242c058000c1c0c550307581036101c0d809120701c0c1104090b512040b0001300d6400500a065680340782d58158030070b1300e0014502501000c48101c40c4042903400f048030400d0b199029006101c210140341810005501030301c0398001034480c904040c5030207002c0401d29107d61003803000c0c003001e2160050140401d45144030045501049980700e50342d00d44010301c1030301440c0c0924000c000b4200c0d80c516102d03009100302d9118420802200030071050245c1c80307000540702c0f40e9a503003007003020642138004081e078040341c2030005000000c102d0480e82e42480e05111101c00b220400c8400c00d4400c200ca01ca4810456440103e04081c010034034124006900c55100e0b000300c62a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506919532 1250 506918282 506918287
    0x120a0513050d0f091517091609091a0906041113060311090105030f1c12020721110c1306030c0f080c060403020a05010c0510060b0d05090a0302030906 66
    0x1100004010038001140c001040d03840d820751020b4000d11120201d00304030045030500b4030018a04040084004511140e60346201d01d420052001a85d4008090442d0705a48142a03107400d110300c44081c51030041207201c80c000380c02d90441c41c01c03011849903032034480c2c4041c03014000c2210420f001b003040d5911581c40a94600e0100207240081d5000c1d841d00e00d03004456240c144040100103c1d01d0803050240402c40e030004060f80e80d64201540e4a080081c0300b92107400001d43e1201540200383c2009030410746d41444500440440040403c0740c00442d015580b081c0ca8954003604103170100014580c0c000c6520b0465500401200c60340c3d5960300340403406014a140031341c50704043d1110362020000d10340c00415203108030390b00da45180d41101c160086200600030f10901c208140b03401c4040b1000c0341c5d8042c041c426401d107411300656050000704c1040c0c0b502e00074015042d81d2010548511406080700070403098850000741091000c0303840081021000c3e9200c0c403010300100b40c001054a844010442e480c66 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506920782 1250 506919532 506919541
    0x53301091503020f04060b0d0b010206090c03071806180c030c08160e0d1209180507090504020d0b1f170c090904020112060b0a0809031306051602090109060812120a05 73
    0xa004001329440031f5640c043c0030401e0311842900750003a8041d8502603085850680310114080d8a880d941c24a055146d40104030400201e8800e0320101100c3e01c450000040c440c0c3d9401c00103480398010081d0a1107566540c0003019029010310031040490b03a54135200200b46054407400010740d01c035016413400c1c0038000c600c0d040680e4030303442c0c2079410325400301a404c8020201000501034803401c2c00349941c2000c00701401d1100c000c1510501d4880c0000c5d58a032402c1c5464007041c032000f035010f07004040380030341c41e84c030306000e1a100c10030844c445c60726010505c1c580a50901d401080880d1466002c54002e00103028054802d002a007696050340040f070302940b40f03071070707038801694080301c048424100f0f5030030560002120000c2c075001d40201040c94031410308542c0c0ba02003445d1030b4407882ca15942c121034640710501902c0d200c1c40240501c400402c100d18200b1040d600080c2030080240d01c003409a90312108244951503080c010700c400c00e055100c0c0d181c100b4110700d140040a40f80104204a0030b6500e20004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506922032 1250 506920782 506920789
    0x180109150b031e19020403060203060307061107030b100e0f1f0b0319020910080915160818120405100201060e0708040f0f05010b040510060f0c053301091503020f 71
    0xc4c40c10401c604110341e1030740d46e440c16030042e400403681d05104e80181140011030f10301981054064000b02070107080c0c81415651041050080508440c25014800002040440c5090700311405049405940707806032404040401045558a40c0c02003010901c000c100441c05144081c4ca801c4400100da5140c3c50b042c0c100c20500130700138480620340c0b2040c6c54106406054000200601403c0003106a401e420b070902c5442e10800021355000c0d45404140c2d4007805020301c01c00c03404e600454120080000f031052403600324985a61241001001c9000050400140c42c24200d441c1c07015040380008e100c01072038400003070400200200044144900180028108507210600510141d4006818644000e50b818524028195844020b025038504804038505d40d841000050407695a50745e400c2c0000c014880c1119041700100741119184505850300101540700e0181c4008000103185e036605410b82d055810030140d40c1030344800007046c40d007044e1505201d8103042000030340c1d4040c2e41000d82e107155403022 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506923282 1250 506922032 506922061
    0x130e0a020904230c07020607060f09060e0f0c031c2105010303050a170606031803090a060f0906050f070201050a180b090a08011415180109150b031e 65
    0x25034810f10703140c14002c160048011503804040120601c0c0760503a904800c4050a116004000c1c1d400007050040100180c481c0d003085034454460000400d02c44600e0741c5800c260b03980e540c5260b9042c0c03c03c0200105090041010030b01c0c0c50b20407401013100ca07481c0001404940f5681d2054003c00c41d9040e0b84035100c4c82c00384410041c0c0f0903542c00c200015a524240202142c1084449000144009071a0500000e400c01e00c0703070103400010700142c596218031180c0f900916a031a24054140014003611002d6a02d22840c14001c0a042d201e038200d50200d65402080440d641c2c0205040c404148002d007004070f0404e0640308003560a0801a90b1100250801d6a10750299a001010000d00340400300d01041c100024298484040d58200410394440e8a072900f07071080c16440b240c013a44070000080e00c3d4405400c603501c0540e0082d01090304040d60000e0250a00701c00d0700103014444e101c510300030314038802c00248002440700e940030a04505107103c0c0c10021080c90144006506010b0010400e40d0341c2e111003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506924532 1250 506923282 506923297
    0x10213060c240c1b020a0e0714070c06030506060301140112020408010203250201020c1f060b030114090106110c0d030e0a090b030c040204030317040503090d1412130e0a02 75
    0xc0180807412044080301c0506200f02d21840050242013002d80d20b46000d4814545050f80141180111030070b000c141403400d00c0040c080c40422034028070441044882d00c0050907080d0140701c00460741400e00300d0142c10b584001d003c103800b65030100010410983c041429218140c0c0901c2e0200c61403004001e0040079006a801080e40d03035200000340940e4000030000340000171245092150000d10000f0b0a9080b801018112849604231070308402c0c00ca2500c8807040301c120319000001a80c251500c1c042e81e6103030001d800001d0b075000c08002100051030a4181c0d54010105490300700301c5004071a0180f9228801240f105001e588040c03555010980030300e00014011101070710303507000295580341b020064070080c00d080d4003078000c00034043d9241c10a402264250fa4064551545d0042203100f442e072000360007002030b5101e0009000748019542e445c4101d5219502a030303c080502c0c8044e22426060007190032044880074020084c0c603135030704140146c0108480c045180c0100b46e40e6041c0703072040607105214 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506925782 1250 506924532 506924573
    0xe1306020301230402040f05060c01090f0317011203090608040302100c0f20030f07170a030e0c09040b22050f032a0c1003021c0617010213060c 63
    0x801c40c05000a001082c40a210603843c8681c0381410030702049200740c0c06400f00f03c0c484940d06000c0c07428030344000d00c00603040300000108605180c56414610031901000c4002a24280c0c06940200c084202140940b01250103242e80b260286e40c040c05030f20b401e200f40d2081c4425040020180360090062046c2c80e602c0d0711061100804103a0010300410782454880c1c0450070b42d085450302c942105246603608480800103600e412012030401240343c100761070031031f41280107032503d40000c25110301418a4000a840c00704032613240d50582824004ca5000c2a402280d0300020040850514400d4682148041c032032421401c00342c0c140790842c00100c80300903006114400c03022204c42d00000c028004e03440304080f82100c00c9044c0262151400010741c01080a60068442426528020401c00d10114140c10018640014809075020310704080c40c07081c080907078810041010018040c101103513110f16034001c6207407080750062100010504e024020030020504425010480c83e441c5040c90f211005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506927032 1250 506925782 506925787
    0xa110402090910150804020307060c0f140304140916050d060f0b030901270605190e010b040e0a0f080309031204061a012607140d060f0e100e130602 65
    0x3100c040102c520248500c5510220441c00c0c2c2c00c440c1d100d10517560003207078028080e004d11740c600fa908440000b504402901c4c5034213410301d0f0b07000050400c80c051300b0608056001d1a201c6213003000d04446040c01c0903800303003e820346c030081081c50741444250313401500681c200203441750100b280301c5005041c103400c070301c14103219880082092071001c4040e5120710002c10080c0f01d90fa801c0c1c0342e1607410016084410040d0121000202c0c0001c0107500020790000c020ba80c0c0300d03d1500c4c000f100e0740c16901710203400000c0340d6581d910b800807070501d405908611380e001c134010005900303581d90300c0016040d03005d0098000c54000c07002c01c1114900344121206140070030717101112800c0030f06010004086140c0b5030b0042002030554034043c2c0d409020744282c81c020100000c100f20b01418a003010402c4003c0c4000d04028030700c028070012402c40f6020f02041c507064a00001c00c1e500f05a040c4240303408541041406071021410007004081c1a400c0740d09032030300b0003042209625401c0645031110420352000340382c1d0303001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506928282 1250 506927032 506927041
    0xc050f0a0b010302040f02040b0304110105190c05060702010e0d0e0406050315100815060402090a0b030c0705061b0f070602040302091504051506041401051201060f0f030c020a1104020909 82
    0x64038641d41c180d83c002c4404010349001030505c00c01f00c0c440c82c031898000703840c01e10014000c030f400882901c40c00380044c1000c40c41c00d081c4450010302d140c000003400000c105070841840501c941008002d900002d640000c2007081d98000c030712640c9602a500b40300c01c1084801c00180c00781c031142c103c00d005180160442d200030ba030070b5003961401c56044890b8054602c082d0f0000034142000581607000421112030310340c003600d0f44010301000c2d6001020264000f502d4040001c2c2140c0f044c0000c2d03100c0c90426905e152140001c0c40d181c1c4c201000a0140301000b03400b03c0c6803820049003041254404003c404406980325424544400640034940c0081e50200d42e420070024080300445900700c9440c401c440030040f0f507441014108510104498240e005070050206106483c81c1c040d5a01092005050040c02e06000c0361a030038000800b40c100300700181c10700741d101c102680c00100009401440e810240400303094100025640d111485000d040c00105403480c1030503843d150f048402d0300e40b001d401ca140602c2d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506929532 1250 506928282 506928293
    0x12250f0e2d1f030813150c030e090c120a02032a033d0f0923090a08070f050111120a0b0609042f040f12031b0b010608010611030a0c050f0a 61
    0x317140700313055898085c0d81c64030409038411400310303000940c1034803900d18066445003070040c07002c0002c00c41e1030a480c08010f6451403031414680c2501c10101c943c005a901e2419840c840c1c1d26600c059040e414a01c0300c09842d00420750f8036420740f5480000e048075444412200340c5120f43e000b18103007001e044030f010004112004019410540700307842031110a030034223a2743c1d1112902110b00384807104e107101d10500b803108198007035a00129049010300040b10403078602a1162030950740526001ca5111801c84544401c0000078000c1c1c00d6409605000c035030505011a0901c01070100082661504a80d0f0307405811041c0e4402055a2000001502c108078540007121000725000459200e4401d115036000800c592000020032a41a030740f8584940f400d440ca06120a001034040d41d0040b410300c500990002d42c140d4001041c100020f0056510010329450100060408101030300706004008499072001481140002111b00210607403500c81d400b1481800c1040c109030080c2d00300c039824040d140c0803400f0b204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506930782 1250 506929532 506929567
    0x30a0e0d0f0218240f010c0501020405031515120d03050405011515082d151203040f06030504080313050c13021812250f0e2d1f0308 58
    0xb01c103903071008420303c044c04201c038000110b01043d80441154070813210b039442074141800c440c1c461000542402d46910001b824107442010314216020603004125242c09003940c209000b0318169a004001d1001c000c200d5114000d100e2040300349a00c42c000b0408000c02548548480c090a41840c020300e80c49440341103442582c42d048000081c100004100507207850074a00c91582d40d90102d00d1040310000d06024607103140100701e07001d40c0c1881e0308410520b0f140c840300c0396100a400c034055a511030608100e4100350405400c0f03402014a400200000100c3c0f40c01105c2c0c1000201c60003d1701e201d503902d0004d00d0444072903129034120a500114007100c03c041c3d0050300c40740c8410034223a101a0411014400e03003030403020310380546170700112002003100b01209080b4000d0075440d205100381501d80c0000c88000700150320100203100724404005102e409070103881004202c7e4100c6031441100c5540f21802d100c1c0142c840241d040c2814004404400309441407402158028292912040400d01120601c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506932032 1250 506930782 506930791
    0x150804030e040e0d0f030b04020408240705070222140a0e0a05060708070c051c12050402100f0507050a0f030806030303010e1f0b031512030a0e0d0f0218 67
    0x6060900d46404510b0036000c3c0e21102c403200001805400c49404044641c0c03249404907606040c0e4490300c1d0704190b111070004002500d02d842c001d0110b1360a071f050488400481c660a50800f1b24503c0512040d01c5d40310045411030b64040b1028014014001000d03c2040c0001085103000c03482c15064103429540307220414410500b0b00e20821600b00c0480e015501c0c0d5280802c002d080c1d405c060300082d040c502032245160003950038070b00404001100c2e80d03605c2c60507152100500603000030079001540142d02c110b091054180e9100284040c1c103050740820000a03966140d0414000d40d1680c18242d144100e043d40c070210380004c1154192072581c100344c10740c920340300d20660000c1c40c1c0c000000d5642c1000004c0380d0480300f9030b60900800b0743d00c0f44414422084a65580142c5035003000001401040100c051130003440d11009100344100c41c0401c11424414004e160082c50300140080b801d5190444990720840300b0945003440412010300d0110300a5601d050001d52003841078801e2000e0302003c095030340c404c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506933282 1250 506932032 506932037
    0x30a08190f02070f0c06090503030d23100305100c0e09041e1b051507060b131a010906091a03061302030c030403020d03060509040f0317090a020a050901150507050715080403 76
    0x40c1506e03208111b80304c0240b8026240c240d80108450b10070701c9129404000b02c4019459102c4070540381d207140d8104e100d401d03184030350442d541180a10034403034180100c203210b456044023040600c109501c0078000060b00e1818038803890035400020140004149825646c204003040c20098490750324169000300c031901100c0307510101c1030b84040741d181403038418880c001d080300c0750302c90810302c0980e1500d014000415450303410100803800c03a1541d60380740c0505904c0e01404501101c5040c10304000602004c95984503008000c140c140030400d07440340240b035080700c5d52103440469032540c03203c02007030a4040000310036007110701c000108080d603070761440950f00892195017601c3e021504c01c42c089043c1c5480c0e018a55100e074840020a0000e00b00448485031036100342003030410f8860b85003a5041c0001c04461407080d03900004071500862a20f100e501c1c0141c10129aa80d045505003441c03404029540c4010b0001c1c000d00080a0382801420850340c03008011802000503d0310040c82c0c003c000c82800d071804c601 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506934532 1250 506933282 506933303
    0xa060905090a0b04020904080c0d05030618073c02010207033506030c040c03051506070c090c0219050c1206040b0705180405090d02060702030a08190f02070f 69
    0x403460201c2c00030249600800c1071aa181c8443c4c0800c81c00c1d000240049800150801101032940401c1c400546025980e4648907180d150200c140031000c40141160401002114200400701e070300700c2ca000449241d0309005650200b44000b1400800941060a1210021201c03030201003079415001041ca0034469500d190342c00c41034101c948012405a04202900700300c201394045200e0180403003603403040000303044451111042c4085822900040030a00c000f03500c4104000d021a4000c0001040d4402076500d1442d05460f0b403503a00141100d4001c1401c207544512580000c00c0c420031074a081c22038146928404901e05d4500103076200d1100d007030540615909503544111140c00315480d40301d40e0f0044248441c5584920003241c0ca94406c444840c03818000c0d28064510303403181e1103004c1c800d501110050a403d8501c40d000fa28220f002001c0c1c40455000b080a000d43c01d90001e840ca40000c40c0000556044ca06122103070b026201306680e2a51307051022614005004400d0401c01d000c0c2d0190740c101e00f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506935782 1250 506934532 506934541
    0x8070f0305070e01031a040f060e2107110906061c020307030b04060e0402150d3b0a03080604020706020a0e12030408030405010806130e0a030801080105012402070e0a060905 76
    0x111040f500b440090303c2c0100c03100d400ca0100c0b005511039a80030340308060884069015035a28800c42d45400e02201140c1e10070f4100528880300c6102e900e5120210090082c00c00c089561055075128507144494091540071000c00c849442c0c8000b690403038000d5550740307880c03021000e1000000b508100c0b0b8000c006410300c07034402c2c01400e041c0f0640b01920600c031a40801341d034540c3c00748404d1048080500c00400d00400c15103500304070342c1c4a0f040f03000e100e50031403400c810701c503001103100c50300c00d1404c1c0a24001803400140c0c0308000040c58001040d490b00f458802a07071003000080c000d00440300c01918140c000030300310704c07020f601100001072020211140e07281220103035403140da20700450255032001d600c2003209000941c0100b5110303901400051052940c801c42004071016215864031401041c5e003d12180300416030402d180034050078981008002c20761400b0b48040f00c003e103400c14680a140d041040003011482440003d002e403c500d0420708160a081403038000908491281c081c5192400c030204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506937032 1250 506935782 506935799
    0x806070c0308100f17071a180604260a05011a030609060114041a060703030b090f040c17150106090915050603182e060603090f120908070f030507 64
    0xba110741040c00ca103074a040c4030700600e0018016405d82c4141c4985a00003440000044c080814850340d03100036616456071110300b91081c0100e050452040c081880305010380a010070406081c0c0c900d075441c1d04200c0503140542c500300040d110016129508240d4a007e000c20711010300c40703c03100c2c1a001c80c0c4550703480c00c041c591907240078000d922a2504c5072040188030b181c542c1203100d86164071024070b400c030850000050920350003034030124080390721000b025a06180802c90b00d5400b0180409100e0603180c9580d43e031184010318000c0c3c125580c039030109540359103020002c4414844485400c40241c0d40c4601c0d018214810740d201b641d42d40d600b0030010940020890343e042085030001b400301821604c0720182c6e05507481e2001e1680d4224411010081c111080407400740d14001c4850490100b0400711a81d204141c825541200c41410308000c04000095024104d8101080d00034407229800418440200d950300c0d1554800e80e0700d03105204001c9928018001103808aa2080080b141420340d11842c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506938282 1250 506937032 506937061
    0x203040c171e0c0d12021515030601081603021c08070b010e06030703030c15020f0a0806040b0a060e0f03010b040906021314010c170d0204150906050327070806070c0308 74
    0x1010f4120303181c0d90f10240011601c10817000c00344000d0055405000039144032101409003200c028400d041c10b20380ea0741060506212007030242003140050261522004010035000310305d4400207004034101026040903160a03c030360005141e01c07035010ba40e41d0309241803008a0903800c0c0203a281800340354022134200e20703000031180200e80d4140c690103da13440c0e58861007242d0800100d0801403035000c20801170101502d00007024007071480e494480701424040c0501c4100d60000f841180074050380e0788280305a9421a080d1451924200e80302fa0122000390701180c00b520071624030b25085030030240c02004018441e00900a0041540228800c5c0703a0344208c243c0c4e18500c44c1105a0100351400e0b044030100c0c104a01d88507086200081c1c042c600b50280041c0ca00326407159108503600c408034126014000c3d407084589009203243c0c50024210f0408444060070100b02e0100c041d2942a0352500080815003446800000d100030b0003503030072038508001c003c1d050000c2c00740704800050594000454403814180c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506939532 1250 506938282 506938303
    0x210801050103230406020c0105090a0c0506040b0415020c10020d1b0209040201080a0b0a030c2309011502010902060a05120702030a0c02010c061b0f090b09060a030203040c171e 77
    0x559412803d100c1c142189404054400d0341c0b04c9400700a60a4000824012a4060303024040101031002450605082c0d910040d000203100b14020441009040e4180e0160340564490400600071100310361010703441c00c042040b4182e0440504003880f8081d603008142c08400c81c241d915003150300e14028014100b00804510025402690b200129015510617035450b507210000c0807000642001701800241a400141c1c411a04240c80741c505009040403005902209a2650103019035042910005040e40d2014040c55500203050711690324803501c00d4021901441c2c000c0d004070b0341c40d901c8403001000d580c00707040e40300c0da0390b0054404100e00d01e10000c102c842e403007880d80d03612903000115401101c00c0c0c4c0c941001915459218850707442c0901410003800b0000c1115110903110404210300600480c9642c3d1001202c03c0042c0b0035110185c41300c5089175030000031407070016900d54a503e0a410000c0040d00800a00b52015040c80e100c00030000341d40c1120654201c00d040071080e510110b56540c0c02481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506940782 1250 506939532 506939561
    0x21002041805040c081005011809050604080f0409050c0a0306050d120528020a02010801091401090c1701030302011a1005070b07030e0a06020d150f03120c210801050103 74
    0x1c06099031032842d500c519002403080f03148810341c903078400c03d00b464070450900c0300b40c4003030ba04e00040100c1e00b802e4015010048060b1014440d41010b6201c0644502e0000c10141030302030000307000c140003c01601158041c100c1864104094100f03440c4900503a0040565400401d15142001c02c1e240340c946504003075545c2c0003c0c810783c80d10300306808030fa05802040900c003200b008180d000c20001c0b84034103114a010702d00d038008c08000b01140001045900e040c0d120402081c42c01880b80181a461186181500c003102c50204d0380c01e8001c54107c1d207150401c20b40700c99440007030001004140c0e040d0045600443c05500c1c90002000030001c2000c040c11405032000410b10800213200060501811a84d001c00079090001c1d40d04142507805007050147c184c01c880c4030340d0000d88288400310b11300c00c01002c0f80c03020904100c0070f8100262000403410602010741817502c106101c942452080b02e80d80d038250340c043c80d041c071400d420480d1904a9101c03010b04001141c8040c0000c00e09512074452032089440c1c14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506942032 1250 506940782 506940809
    0x2060405120a03140103030201090209012103080c07020a032f0a0504360b09030414011d19261b0301090602070804180203070e150c0a0507050102100204 67
    0x4030700381409922004001061640301e540422807102c414010300e0007540a40c0000c100d20304240b0402c0017000050b00201d88490310030300811840c6201d030100c2e402180d4142804125030b12400340d13020481c01031000007940000c0c2c0310404000c00c110258940034089022401d443c81c07150000c0b82002c2100060b10f415040365580c43c082000d0300d02a04030008108141090142c03c203520070f444450203c0124048000301c08141c0310200700300312110707455809289032001e1810141800c0302d640516011321b492504101d8015902140d004140000c00714035003004003002501450107081e181e220549124940c120041c90002000342003850b607402c0d1500c026180645091410100308101032207800c0c0300c00d40c15658070038064000480350f2006203403c17400b885c0b61503100e5141400c003400d0b040c14281c200401078010b000b442206038010041c44811001140c90803441940e1081300b069500035100b84800c14484c0d0074801c4140400440c41e2801d840081c0d0a070344440904d4ac42c00000d07441640710340094411503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506943282 1250 506942032 506942053
    0x206040f022e0201021e041206051b18040b10210f11130f030803040605130b0a0c031104122a0605030a230f0c360102060405 55
    0x1900450320100c40080603502d0580c1000359800c00c1d04051510200542c2d4000f861410048100030f402d42c410030490f00c524581820700c24450128030300503130000c101e0b58445c8041890300b0701a411140c00240800c0c013041c4c49030f052040600b05400e42000f800e02a5103030004144143c1001d402084400c5080d031148000b41d581181101000b95401d40c0c0c80010030750311081c4006d48a004e00907403408600c6007500c65222100c0c490712030903c0003280d0010211a0448400700005044039090f80d50003904a24005825551101041c0d408900c808005000310b003000100070350440f00d60310580c12762119680400c2807811103031943e03400744558007032800c10102000700e41c4005080d40d042c1c01d01544031407086e51681342103038090190130074980d003100c0c1c00705002000300408403015120f5041184034218a000380c10340c0c0344c080035585c100094150800100c9450005d43e0101c0410308507032015a041140c040d681e499240c1e81911280c02d0504000070081d140411020303907200107007460003103400101604045a1307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506944532 1250 506943282 506943289
    0x3030f08070905031b042414180a0f050f090c040218060a020a0302010506031204060e0d080d020a121a010f02071d090610080d0f0e0306010b09100206040f02 69
    0x8014000300c10014241404600ba031000d0151400c609503448000c07920381c140004006c140d402c02c40605d0401050055400e80c40c5003108034803800c903001e504c0e4404680d001803000c10481c001c0e101d550400072184200b40001a2525800806c8440440d941085191a038a288c10481d850035141c40110350b020f60b1181c1c0e5185081d6004086040c0c2c3c0300d2841c5242c044220200d00140c10144108000d40c10902003001030540a0013250340c0b041044014107a048807102e854601c0e40103038054003080085001c0c800c040e540f100242c1542c0c41d038000b1004ca488616102d03c3c10042c0d40b180048000040c02c94001c1c14014145000d05900d200484813121034100d20f101c01100d054080c14001c84c11481010800100c0494030754000c008480205c800c40d540d1315108800303d18005000c1e2450003007400d07070340040240e240089050b074107150003440c200202380401303401180d124603400c0325203915000740e40001070002844da00804420b041510215580c128404050b0388404080394054400580104c2c0c4400519 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506945782 1250 506944532 506944547
    0x1612090f0911090301051602061302030d03050a0b090c1e1c380103110307170a0b0315040c0f030807030c03050f070507051c170901020a05030a020303060f0a03030f 72
    0x14200c003041801d050803140005d080d50410348100130400c0b681e6540d210440d5050210541c444c1894485401041c0d00c2d5010969659a90307841004260b5143d0100b42c400a40d42c020100c2203000401141903818001c8105151b60302400840008100903020460b00000b904107071098018560213040c591401aa6208042c0800080460030402c400c44007190100f6007812002c1508454191140949450000502180c0c0500910301d03421009004209100b07520000c00e04654001a11501c0300307840b4138070380c0809014548069585405440d800000100c0d105820521031030141e02007036021951071003c4540004203000103400c8103810000000424001e0f5001d4400a00c070307180062820034500300840786504007540844003038100802c2000341c0c0c034083c1c010080c0401d00360320741202c0040664403981401d15005048180400c04200300605038000e03c40c0d080940d0b00403041d81d40c0c503a5100303c0292a544102c0b040303803040c40011031200280c20a480004e040c0d0390f054445423a6100701c10801d80b8110f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506947032 1250 506945782 506945801
    0x3062d0606050403151107061410030f020d030e030a08070c0614040e040323180102010b0a1e1707080105090705011403100f081e06090a020d050709021612090f09 71
    0xd548484991b40d0994840000b411124000e40e00010301c0300000807640d030500c8000c1c001181900c443e401c00c0c408281c00d400c228001e55811148240c8010080c50166100910010340550500070b0303200020501803c0d01c010502688150348080031540ca4a07820b407050301344400071120510080c03105004c49a10034408941160007800d04191400744400c18403e03071440c0d840c800001070320201d080f9130394902c03640e141c5d140c05d4001d000910844010001140200480b8440c0250301d110b0300950b2045039400c00c0340840501050171080031204a081c4526950b4030a5215a1869620b490b00140d014240454000e0640b0016500e41c200301c62521140100c540024000d1258050302010004482c50b401450400529412018003046e0065222000701d4944030200b858040e00a90108030f52520042441c11020b641151081c51000103400e00c2c5150440f40c5d0000c100c214030000c4e00102481c0001c076584503044c4507942c1c87c054900740759800c03120b80320a8411206504a83c6a041c0031090b0f4079000b14208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506948282 1250 506947032 506947073
    0x92a08070c030e040204030c08010513171c09110a0e04050a06020919030308010518040506060d1502030901060f050301020a02100b0102100906020901350a0603062d0606050403 77
    0x403c0301c0000050200d904c55401159440c03841c480c2000712034028000e45500c25440b804c45000c6608070b44624140c008043c06100e4109000a8228002465815212002250080c1c20400f0303152924120b14407140c8061501d1045100600004d004114484100c1c805c81d40240035042c05d00301550303180065089100c42030350104508085583e0450005c460700000c501a0780c1c0c1d420203514020500c00d041049270440c00c4041010320401001c6180065002e8000000f660402c1608101d81000011400d0b5498040304080c00007050050040054008800f5200d10041e4040101d54403005c142c02c030b10580080c1c80c0940c0011651030704408843d805031401c90010300546803215178070111002161903446084414640c0810500d20301e50740000d9000f0034101d100c0d041c0031075150f80c00c0c41c80030a0260119000607808014000bc044c582d80380c21500065512010500440d20001d1480f5200c0780d1042e004c0c40310030b0100300f40c0070a0303140a00580303048401c3c0e910340b070303140504544800c81e007103900140c2c610b103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506949532 1250 506948282 506948297
    0x10090c0302030d08151c0b0703020f0c01022a0d0e0a1a1206061e03040f0b01030b060315070e060d0603051f0c090513020706060e01092a08070c03 64
    0x50386040c001034040d4440765941210f0380c606400c241d100190170740318080c028034603e20b041512030160150128110b8000b01c103040d4a80d14000c0840c0a0700c104001007000c1c0c0004641420201c5c0305402501c920622078010182241c040b0f00c64075018110700d40c500049038030060410080d41d024840340c800e54000a041e012680f03460b0421207240342d1a09170262100c6000040050072200c040c010580c00c40000c64429282250b50402d0040c1c0302c0440a2102450f40000086010080c41c003040108050b84811281155030792401d03c0031040fa41181c001d40280203104c14070140c14006c12440d031042d0080c0e140d41080095281c2480110780110030311040440c0c1d03400300880850800c00050094911000c0d107103800d250b10301a114142d480320f00f4482c0c203025031403605000d96561442040000441051f0050f2a076005041c088041d0409510504a82600c070f000414072030415000301e40c42018140c8020241008804130120b110310704201c0e00300041091021521052240f600d61180c14020300c0c0810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506950782 1250 506949532 506949539
    0xc0609040b030f33060a0e1f0e010603050717070c0204090b1f0602060408030a0c0e12070f0e0c04050907050d2c030a0e010f020106031b05150c10090c 66
    0x3c4c580f0703c10b9500c10040c1c06801890440f4401c80b50300f41d20b0b00c90360310811074030541008408151800054024220380c1400c1000080182c080740400001246001c01c805011650f02c400c206030b0b41c20f0a0182c1800a8108000100c01c40d001d0b5894110a040c1d9081d4992956900c00f001ca03421006c8500480e07000351201d0a03580800c00e481399041c0038035440400d840001c9560007450700746d540f03140e01120a542020381040302003103154050765070107040c2800100ba52030300d600003140c2e41c065900c040356004047c0c40d181c140c07501c00024550250791400b90200c0c8440c0c0c0301c60280709000707800c139810b542c1c05004001c180028100307005801d42110b9242003241c02d020010440c18252480701c4239400314100d09400e48071030341d807040101c01041503120010314039016601d400146040d000303000c0e442c14450300e4219045c24604c00d503c07150003940c001d491502c00422071b82070401c0030191032150f40c1c0700346804214170014172400c030120b1b0740c002c0c813080052100c20307454504000502070300d02007601c0c2c1d00078205001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506952032 1250 506950782 506950813
    0x30909021e0f030609070206040c0509180609101a0904080a0509062106040903170910060b0306040c0201050c0315190e060306092103180f0313080c0609040b03 70
    0x1029080484014503443c4d15140f400c1c0003507840010302c1402158419001e11011944d024401d00541c1c0d410b44880c043c507a41c3c1c560041c0c070000180c079034004910405081103180035002c540c941022401100a1143c0c4456012107a82242c1c06002207900007a56404140042c0c0000d0013407840740c402c2c2c1401c038280051500055010340122800a001c1645032015240306070314250b030243e214604403400c1225520580b40101094500480e40070811002c1d0007280207003008212084408464001c28800c882c1c480302e00c06c2c400d0b001602e03003c1c0168182400c592080c2d0040c0101440340a030600c1540c00c41e6100e9505d540e94948449026810540b008191102c0f00c1109280001030f02da4202e003141241000c805042c540900201000c44a4004019440740c0c0241061810040d01ca030f201010340725141c0c01010030104199980b1594548108411142c3c1440044017a1204820010794200c3c559a9040070a0b299200404299480103081001601070310381940405d100000160846100e0120710514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506953282 1250 506952032 506952037
    0x10b0a0e030f03071506050103020313140a050d0309110402210406090b0c09181504020d0b030a3206180313030308010f05030c0303070816081201031e030909021e 71
    0x180c41550240c101040a17402901502004101c01e28007185180351055000700d4070740030404024030b40300c21075404180a900802803041c08603080001e4600720090042c0190062401c1720007210303062030300d04026500b40740c51300c2950b0380b5054003040100000c0d0803101c5200c036114010000c94407550349000003008107070400c612074070607003d00048564840080c4104413244c2c003448810740c69441120104080341e07140c040c2001050409560250f1214072201000025103000380c034054252165050441c2071002070b007015103040b44001e0b42042c0f8014070340e014004d0519862200300c00b951100011074001000486c04150301d40e07149059038140403c480800d2803d8032194402e0703001404410060080a80f0148054000e14088000b0301e0801c1d440804a501c038042c90314040c1c070303104003c6114030301c059030032040c110825404000c10b903846040c4a8101150002800103481081c031080c400c00f900c070306c1e138581243c1c015015100c40c8179407454896038601a500542c25244010b101085000380c25214002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506954532 1250 506953282 506953297
    0x1e04150525050705060307090302040e03072102250312030b04061205060402120c10110105061021060503010c0c06110307211407020307030314010b0a0e030f03 70
    0x2a21691001c400c01405001500000103550080001030314a001a41c00146070044540030340340261290b658030002c0c2c802c14150341c4080c0d001418000c0800e001040400107004282c4144810340340d8545c03440703c04c06140781007500c00b0096480507140c0020b0512a5070707050002c40d841803a14400700c0d00c0e43c0d116402c44a4000c1c1000129442d40195000707840c080c001c250282c81c020420006142c599101c1c2c40e9034000142c0040e020781050b110744a10035000344060f121860380904050a41c0c03078443c00040c000c000d10f4000340240d5190802241403480c4c01e81100000f44240d80c0c900d07409842203902040e450484117501c5413020364840000665841c01e000e0a0418400ca13160300c1800019030400c001540e0202800a030321403020000c10006580068502002003400c000c0d4602402480030080014001c00c40401039449021003004041ca500200601c1d809201c5d950900c40061a80c81c2c8440d550310030700400d5080c0400307206010700203215860303403890a10f0080403030300154080c80080d420356001e402d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506955782 1250 506954532 506954537
    0x70f0b0c130e06090106020f030f0306030312010e0a0e0c0114090d06180b090d05070f0309030c14032b0c050c09180f0606030304120203010b090108010501180b061e0415 74
    0x800c0040510384036004d1401001a400641401110054400d03128442c040544a103100c010020513410b0314100203442002103000210786449d61190703040c40f02c0800c121070441c40d4504080d14106084408151809c03e202c041e1600c2c401d00e055003003d02d005401090380356811040da0a03c68002c56807a0240e10480018503843c038403214042e003001003203440000e020f1551544010203038440b4a601c40111400c90350461182400303020303e841e044031100d000e540098440d040300d60021075000140140c20000b40011411521a402103030381c0d90403151103403510234898843c55980098014040c464080801e8424001d4407001401d040015040c0d410544021101c00065500300c44040002c01000f040c5d10100002080a0b18200c0b0019a0740c1c07086004801401c0a56441c02c001c64809404c202200c0e14010705100700fa60316a015640281800d12401c1200e5885d281013100152280c451400d03084805442e0710300c1c0030328200c1c02843d01001c00800f0006c0c0c002c100030001c0c3d10780c8000d10211000c0b9096 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506957032 1250 506955782 506955809
    0x13030e090412121a0904050f120307030e0a0506010b090609061c050601090e190605100e0411070f0b1e15040501051f1d2e05070f0b0c13 60
    0x406042c618a4030350071503850b0000c4401c9414445040113840c40044444400d26a684c0c64520304000b2a1160040284150420072042c41c0d404e0003e103216040320341c1c08005180800300076942c0d4103c111806070140d08044014007a04140c83d00501400c00e01074022490900d18901240ea1a33100900000e103c02041c45401442d22080c090300781c02c25801d1078045515800c09840000c990b00c040c2500030705e80881403c1d1501c03005160410f00061100038081c0200c2500c03400041d0094070b0032411180b107989896820282070000b40f0540748174640180c05030359800456035803400c210201511001005420a030b03e007a03e8010242c2d1903104034000703d02401c03a10361007410720080d1003060704113511030310980452210030103c0710303484100e060052030300c01d0201d840050840c2c041d01c41c40071003e03000303051860741d8111146040113181c0d41c5049074030b00c42aa4115100100c81600890000803d0040510040f001241581180d960403142c0c80b8001c1d80351200380c3c004c507010321003d17520062420401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506958282 1250 506957032 506957063
    0x2150f041707050102030d020d15170609010c090b0c0705030718050705070f0201050d090b072006070203091201180f0b1b0306040c05120c041806080613030e0904 71
    0x41c1c124166030480440007000098104400030352207004000720110826400f144a1214080f2500450041120443e07020880340e100c994005020b45121001c0d8214411030010480881c0148075626151610f9078943d00703107500789503008407580c0c0f1582c1414510303c1810710120f0503903002c1c40300e4002020070b80100c409624240901070280c03040100111b0034440e041c400480404e04a24a900070141d09107050755581c1000c4084500030604690090503030009103042040194000201e80000071003005401c5078040704072001d0380d07514000c465620040e00140003000050501c50020760700c2d0b403580c2002048002c503600d252a4200c890032019181ea41c4100e1204081c81164a1455045844643c0c10320040c00c0e907100480081c80058030b41c50045d0b0780c0300c0b560300115200b181903840f02c1b00a07444004140c1842aa03080c1c3d0303604107000c0c0189011011128126903021403261000300c40d00310000d01aa07548480c1c00c80c460304000c2d40f055090203c0d8605061803561012046d500c51441820b051004004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506959532 1250 506958282 506958299
    0x1a040b0c06011505070510090501020c060f1f12030c2102030403021804020a0302120118050c04060803030115030515060c0a0303060f0b0403141f0516141602150f04 72
    0x40b240d020f07010f00804020100202e400401c0786481c81c691a0070120304400c4610b032032402485140c522040f18050300b02440841e4002c08502ca00400140c15400e1103103007010171880910180303102d6006c071507401210440001c1c2c0604042c500203400355486580c840ea0400c80f00c2c40c807084041c815001600000340600440c60200c1c44448465146014503a851500b46d0200d24078101074080a8070868100018004050017508002d4100000c0c040c60041e030040c2d4900582d44600ca82c030800d00c03513814030310041503640000094074121840a2000032a00071070610550081c80f02a00d1300c0c0d2041002c14850440da00c8590007401c17141c2d040001081b040d40e19040060444980380c0010755080e40c405020852801c081007540c0c180c07504a00b00305022a41407400c1e0340340c00c14262601c608044452000c0c40d01240952015110700c1254035a11909400680110b0766400d600a0859041074140700d055020040e40d400c0c2d020813403018103400c4081c01e0004840c8105d1300802e41d4118082000941405200c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506960782 1250 506959532 506959559
    0x5070504110f09040e01020f1c0c0203030609070309020102330108060702102f03070201050a05070816020c1e01020c0f0a0308031504060b121f1a040b0c0601 69
    0x40303a601e4168282810200800c8091140c04400344c03041c1c0d107440c122038041100394101c41c0500c2d99410207035a1407015a4900310300c00f10300d440d2a00001c0c03402942d00210340c0003000b100c1c400d00c0001d0220400da900c800d0180c1c002c3c00d41d4002070381140715444905d00085407019a42501c0c00115012141241d065142012441e805800406035a001002441f0f611a000500d440201da90482d0200b4000311040f0109420f50384580408500c1880310320046c600c440c4480254020440d0b5802070106950f01012001030f100d081d40c5200010b014180090210040c1c0c64120861003640d105440f80b0300310410004005000441341d66000713841e0070244820660f0100300300800104140da55488072030302d00000868012311071001030809100000003441d04500b41c0500185000000e000f00b05c040d8542c40c2c6480180c101103001150030480c00040f86201c401009100094809001441001c60500c40618410280e61180c00c16540c800d010219605400401a284090f0040014480780d854480d1143d5400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506962032 1250 506960782 506960801
    0x130b0705210306010c1b060c0b0907291909150813060e0708031c0621020103020d020705010207050d170c04060509010c02100806010e3a0b010305070504 67
    0x2040c118440382001d28501080d254000400d0901441508850902c0c1e039024603e0000c00001000038440130803e00d400c01c0c02d000030503004589128280e910040802e694140500480c02c4c1c00400310310389011501215555091f0000b8030240350704150020925901d2550a0007010003c124490002e11640d040da9283d0712003056186821401e0703091280d0b211049401908010785400d403100845503002d00300300310b05002484240c04590356848001540100042d808080400300b41c200140041c61081240b541903442d85210041c10b4852810350054000b5030100c0743d80c0903525001c0c00341030301060081c17001c1e03c00c8138021000380500300d90701700008101c0080e5002d0316040d51040d50601280ca2200d0090f201aa11541002640c402242005a50070884490025405620030700c215200540c070801c200e003d81c03409e07201c00000084030800c02c46a20002c0d1940e800818000050800385162591890000300c013112441010540341d0721060038040c4240c100b521141d211f0f8804009504085c403440040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506963282 1250 506962032 506962063
    0x903040501050d02030702070e04030327050c0d0c180e07060f0f030504030e090108010b040c1b150902210606040b0d0b0405070f0611100e030703050f130b0705 70
    0x201424480040d003140030340308020407402d40c0800016490b600810802000c2c1681910035201490585001400382c030462022003580e8202c100424269101c0030807200311564003c029100c00c0340000e00384401042280300c1920152980b2400107103101800c07c9142041d40050000703e8258010402c203403078000d542e40500304102c01c541402e055950f12151903c6400c1543c60302040f0b58446082c11140c42c1c801402d110b521840c2c01e1f000140f400740541c810222603070305480502107003001d41d405682000c840c0300342d840c1d400c0b491076001000640034034800d46001d510100c0080c6500107900803c00c14070240840340d50090b10801040840d01301000807a80c00702d03044806111128402022903c0f50b03004000c010142c482d5a004034003000028480c50f000707862440c5022000554918004180590905041801d40104000c5820107815400b6901c1d000e50140015840c0a80e10360f021035a0f0340c0000c4416031018400d00c20980c050800c40603800050260901d001d484503404c0c10600d0034070084840e140754 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506964532 1250 506963282 506963287
    0x1e020c1503040b0f150301020d0e010c09051f050c07060207180905032a010e010506010905031501051512010b040e0906060916020717030301061814060a0507050604060f050903 77
    0x19612070030544c2d00c00c001c600c4402039074030340c18440501d02c0e00d9001d030fa65045d400450784882519603584210031004401000388186154204250344064441c0521a00150f00704183c200c654900170060800a0161901501d00b140b000105800c105544d0800401030300900701c02c000165004100c0c04040700181c2040054840130303640c003a070701d215490740b2600250b2825040c03900382c081c914440d138100c2c402c40001d00c2807045642e0068000d01c002c498082c0030415007000410340c1d00f400a420104a4054600801d859003407008000c141d03006150301007200c41e0f0411043c001c0040741603034540288000c42e003560b101c2e0f0400c1c81f41c642400c802801c20310704c1d61201d402c0000c15642c20110340e400600c807481e15080340d48030020490820450380c009a101068068164040d9480000118104e4003075039110380d0310274030350f0f01a080d000c06c642c400d03004010b410140c20b42c840d1504034001d14a240d400e0818514000d070990340e4506110302140c090750030b559074103060303140c0d040c0a020322980901010f001e5813 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506965782 1250 506964532 506964541
    0x181205010e0f030c1b0a0302120a03020d02030f0915040b04030b01090c0c350c0a020f242d072303070f060608120d0c020105010b0306060a1e020c1503 66
    0x341c0d038003070070502d080e0858000c0516a040e46c859240344e402071600a401da0500f40744030a00c3d01d98510091008600501c40e0b540e41c00c1d1940c0c0b0100035100006040d90311079191403c07950070851545030100504191107010440010081c85820007040150711a941c10b008030361405203100b040b5440d0110000078441c1d101814000100c00700d100c81c04c03d4844e12440c0915010b54845140d425200c0384405080031400120115a2000091070a03141d5100320b480d0303820344484206010f04440806031a915a104241c401001c00009101070603a84c04024800f035032044080310b1724940f84081d030b0044201d07040002041d005004602071503480448082d0101f11103030f6010624150303a07114000300076160000c000d610300100100c940001c00280340074001c0381d1b481d105203e80c0590a5001e981002072051070005100103150042c003459040b541001081f42c00c540d40d580c01d200d06076000c02c044100b00040b07140342c2052294030317032048481820240e000345680010481031100c495821910301003499018001c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506967032 1250 506965782 506965807
    0x7020f1204090e010b1507060605061204031b080301150f0305040507060f05040f06050306131515030e1605040c020f0d0e0d0b0c0d0609140601181205010e0f03 70
    0x44040b10200080010f540380c44401150052101402a0703a00400340b107800110210820040e00c1868040c81d01081312a42d030b0000c000b400d20031249044101a00c40002802190044d14029203461340d0061181000c50160ba03030503030320381c401d81081040055064000003065032000345030040c092581410402402c060300c45954075a00741c854941005043e83c1c0301c009542c8104141d4004209041040700b000e900c030300c1c01501e40c0d0402c071030150003008086448585164280917a0703002403450784901040c02d00741450381c2d25a201004002007071580b643c071503405000040140c1100c0c1c6d2056400300e491141007000b00803e66102d81c403201c0455004402c040900b20004c140f44c4c4900c035103824820507154400010405c0e52190300c0011300707105112001c0001e140107807401458400e16925081142e15100c002c1c0008450511038028400c01c08900014900c0d401890304082c0b10b0608201480703496a2411802d4514140078403c4072680d45070031700aa200c100c100007503170400440b00051402c100c4001c3da90f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506968282 1250 506967032 506967037
    0x30f07020a051506131103060f0d030e060906040503030705010606110d3510030203010609110d090512180a2403090c1809150209010c0f02040204081507020f12 70
    0x4514186864001c13a4480d40c3e02c26212241908040c0140420b00a05810305404d40003162000e00503c9206411a070514082032a4007040382d00d42c07900441c2c5104201403047c260841443c840c0c00800801010031a580c2c03c00c05040030f184900700100e0442d0502d0703001026003e141e1107070411a4086a40801c180b600100aa05100d139003868120388107101000040e5030400c202d0380340c0030061060301445100c0185030701d80000d6034020f0b0002c0c00300075620440740d401c4640e81c42c50090040c1091020a443e00314940007060001d0154003145e04400500f8030386242544468410007201810131600000760400c07042100090200311203801c540d88000700c611070350766045803400d010580e0710341c2100300704002e40810030080d12004441401064000000302c0060603080815103103840c6010103000040c81e1402220410f0388181e590b003004416a5861a00880e420b0360300301da219801f8007000c202068100301c11207e041b0180c0001825080504010741861a00507500540f0b41000d5411001d02444008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506969532 1250 506968282 506968303
    0x101104051c0f020616050f0d05120402010c0501060609060e09224d060d0b0103060306151e05010c08090f1003020d0b040b0d021c06050a02030f07020a05 67
    0x2621000c00d182c0203400010022009600903004102c0280802e0081c104040e07803403251080750313050301d0909072980d66507a10865441c0024010800700014420300c20f5095040351041c10420310103480c66880c5801e494003500700d000001e04c260010000940c1c80603c100c8044016200c00c00e00d803e04d03e101520744800e01000100001d400400d40007002204a0058032101b400c60300c0080700703002644191203094144080c101c1610004800e07044058604400704000c07800240301c20310304942406040050001001352a0515903504000008103071035006400d901e442080d0510344590800c03801c0203450442e40c98050b0414003810007400b190b600f06a0700b008003038000000030f0f01c0b2823031203001886208a4151458200d4184407482411380d0301900500b10044a4500174071070342101034180710480e2400c5240c540c6c000f0740802c80304054245825103480d8889446040c007011020b0340c9603441968804d81e030359544580e001040103001014460703c1500400d4030300c0545075039603850301d5040e9150441c41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506970782 1250 506969532 506969569
    0x110c0c040207050d0f1b0501020306040e0303090a15110d060801060f0b04060c21080613230403020312150a050a24051b0c0f0a03020a0b0a0c02040e10110405 69
    0x21110303068a001b43c5c0030313062040035000c00001d51009407038181d0203074200742c6005010702d080c003001c1e10001b0000300c1035030b12485c1100c1c02003260809944500c01000303584070440150640d1410a038040342c000038010700030b641858101140043c540504142181c1c42c51340b01c44841041000140403000000381203030110350b00c0740f40ca0701003c16142061402229090f1940401c540c20f5034249520396008008548a02c0b01152000c0186038140ca9481c1034070020300c0d1280f204409104400c803000314804c0c03440d0300a0b010b4412a424035204946403040c0b42000d886204030f11b00d426190014a29042d40d03c40040d140c00d850607804036160414180d08161214501c1446d112032500c40c40b0000d01c03480942d03803207030a001c0c0d00c22074884040c6940e5403a1140403e1190061a0b141c0640784c080c100721030300360300b00e80c1d0141040c40c0b62881c1810000140d00700c214213004200704550301c0805aa12409409000400c0070080c00614104200010072101e805580c003118078010b0004000316550311081d01c00c50007055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506972032 1250 506970782 506970797
    0x50f15030304050901030302060709080d090e0a1b080a0e0d0e06090121021c091a04031b0305030f060f15160b04060c080906040b040204091104110c0c040207050d 71
    0x500000c0c1c1035000b560006604100741c28000806c0c1a80007440c5401180107440b8080d606866214180d2148a0104010b000c62020a000c108010320b103410309034062031781c000004d0b18101d0b96070303400018058802c4803400180040140204003005129603044426003900a1000b4050018050702207055400400c2c4035580102d4002d20903402501c2258140d001000842c90482c180c144080094018001040541d245481034a009204610940c04031982007041910480a14004131524440c020720403401c011182001c5400c103903d5055840019200b42c90b02d50f02d9140c240c5200b00d00c20340003402c0e24821464201e4130000c0e030b1030b44000f12482d900c0c1021000c7c2d480340f00700704c1e8120000d000c00c402407603190110104414807090782c2c00980038251b00e0303a807805642c6842150940d10f2506660182c4010042d002240051a00c0d45c440760096200d41c0c90750800c010b010002904440340100c007039029030400582d00d0342c800824003c102e101c1c42c08480440c201000c94407580c1c0e840c18041081424080301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506973282 1250 506972032 506972071
    0x3040b1008190f060606030e01061a0702060702030f0a0809040c0c0b0103140316050304090e031206040b0a03060207060c0206060d0b2205100204050f01032304020f1206040c09050f 79
    0xa54103e107002500403000303106040d40c03240000c00030585c0c51001945c0e5441e000703021440c03545001102c9800c003ca82551030420620b0380070402c05c0e0307201c0407007260705210f41407004e000c141051007902c51207402001c6440c0c03104140030600040d200f14041c024100040b6810700f20004107220041c138150398010007507130948609112500d2a41c40341c081c41d0700d01031840c501420100302e00040200156024440c040c400510707003c800303940d42d02800c50a0b2100b190210009036450500b41d200050100c801000501000d41c2c0e501c40324101d903c0201c060b18100c0d10f900c00c03810010b404225990b00944299458000d6110544034100c442d84060008005d0404a2103070500400300125904051901300c002d4400b04c1ca0100b032800000c0d4041d20030700d40a09080080b01c1d06035802803060501802d018091010403814001700c0303000301a0002c3c000c03030303101e22220081e0b111a200d1402010040c000a40101103a04080c18444130b1407801d40d20801480d410300d010030588990403021140c1140c07200000d220305005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506974532 1250 506973282 506973293
    0xa090c0f0503061b2203060e010209090103030e010309060f090507050f030a0b060a0302060f0408060a15060c0218011403011406030a1b030b07090501030b01030c0f0e0a0503030f03040b100819 84
    0x20303ca500405c400f6081e84042501e4024400b01e421a4031542c010040080d42614035420b0780a014620340e03000c0b000d20300400200740a8010380608020515000070760908642d0f4072802c6804400c48205180d03a04c20030a4100081001840d018040442e110343d0780700c0000c400241d0fa4a81e21000409030b10951020450b9900e07214140400303198010105034440350015604251a00070703214807101d81c4160000703d0610304652191106101203c0c040c118118100314082c0e5180b1805002240c0200d002d203100144004100c9405019004500303140e10320000e004201070070750704020b040c041041000014005c40e982c0020b01300c44225072210151000140c0c074480001c2c03001882e4009130240325440304120180d0750200e189420b8031000d0f241004146030b00d01c01181240c2c3c0301c9030400003050148112089040c055900d030001c4140c0100f20161054441011034219044070a10320b40c654004414881002010381070240c2c003c0080f0040101185462a42a500c001b00f4400281050038079012000303124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506975782 1250 506974532 506974537
    0x151503191203020f0d0606032703090b0f0c0601140406080102250515070314070c200406080a1103241b0c0307050c130c0203030f0a140a090c0f0503061b 67
    0x121704003410007a10b56669406006010100e0501d55103807540660000030481d240d100c8100150940e40e421070581c20590340350095880603d4608501c1c3d018405849a60380c2041001d020307214401a04a0b6984014184010313128940c0000100380d006004000b1004030346000c1441c0c000148081c040d041c1c0703c5060150805021a20102c5010300c403000f000340c41c58261704140901e10303c000071f040742a65141421214611080b000901c00c1c001103001f14440310300206854001e14004100040b5280e840f80c0070f5190a60080c41210381c40074260006407146400c0c41030103404a007008605243c0a40c00641851090009154943c0c40038002807103980c00c1c0c1c070381e0700f0b4a4020202400300c980c0d0700c40c0350408954a00080101900c10750300a600d04014011350301401c0308601c0181c00850071600c51407803000807510000c014004480e5920711541c851011881290f0190480c03400002d510440340c10141c2030f030a4140c0180724007030000b003002c0001d40c400059095004400c001103010b010440f0303e4078811407 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506977032 1250 506975782 506975797
    0xc12090303110d090215090904030c060e161a07020d0b040c0302130510150c03030908090a03030816030606051617042d03050c060c151503191203020f 66
    0x40c0c8000c40e00100f4020184d12240c02103000321142040d42c104c205801025210300c810040c2c00000c80380108000070b02032850714a84600c03c1c0750100b4202800105186824840101c3c02044480c0e02c000704200b0401c1c0851040c688020b00da01c0f494282c3c9900070070111840c82e14010682004003000909020700785243c2c50244d9070041020030002c00800084015140644180c10310b0300c24510300141641440404100c8242952103a001c210700c81d48060f0000c4c00031083c00c0c1d40321042044811540d0381c0d86a1641d001c2c40c420748038009d02703082001007042d080c501d652010741070614045060003101e0b080025142040008180c10000391071a103031556800c014041010740380d0348041804115074910740c01040c030305000781000403000303601140c04054243d01484080e003550445c420b03900b21801e09000500c8071081903400c60305043c0203542c84218032001201c81000841c0001810500341c541800805114001d05060011520b000d0310360b05a02000312042c0c605065000481d041c01020307420980e0f085 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506978282 1250 506977032 506977061
    0xd0b091614100804030e040c03090206030903130806010b2b14011503110714030f0703020a02090702011e32040b06060310030303050a09020d1202070602010c12090303 73
    0x4259565140e41c0202800780606104002141c5444401889280014801c50b09030b80da144280980c5810701c4001c24115141508058540e0344500160300c805000718040d0440100542d40c2d00e10032003030752442404a0f0030080003500701400400000300c2d0360050340d8141d041c040310340554440c0080c001401860018403a8812400c0000b011522500540b40f54101e070300c890f00c04c00d01900081411001c03078140000f105e880361024401400030032039040e10040c0c60b1045008072403500c22600300070320154119403001c40044c0e1001c1e20308011804d020804540155a9000070b01500100c102d010714040d401c00d000580450740ea020560300c01d20180310f920301e0704c503a025001c1503007000990306024240c0210340a03517004100d84085002740c182041200e1180745040701000700703141590340c101c003c3c02018225908241e125440f400160f9609003040e01100c4c4038a240d07171080d550b9a2406428410b040d803082c029645044001c006194004420364500c1860040008408189140940040010450042d031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506979532 1250 506978282 506978323
    0xf08042a1212110a3215060d0302030d18230106050405060906010804020303090a0e010e0907120b04260c01050a06050102071814090303040c08030304120c05010b09270604020d0b09 79
    0xc1101c4089016206d41e4080803c40310701e9520b40d801e0106142d844900140180e00030003150707600f8101c0750300070014001e00800b400e05032449a243c1d1802c0844241400e45a041c0380700001144040c2482100c004000954060000d45410f0000031181a4001c1c03040d4107000390400060215034051080740d10405004000240454585105068103042409141440d246401c00300304640780008010307045404400306410b40d408240c1d904080300d10050421194201c07441e0000103595841c01c014501040d1529403162186640e40103031382540d0001d0003201c0414a010005e011a0b40e001c140141a00c00207581450001e044840c454010054003a04a0f6412400401c0c0241000044011030144c0d010f402c035840c40f01d49501407180c8901c8107607001080007080440c0d00c030307000d4042e00f00754030f440d0b004500014040c41024040746101c0c1c4100c076040c2a604028045903002000f4551840c0f0002c407040042220381f801e07a01017042c1154241c0007502c40724210000034100402009000d04800c0361050000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506980782 1250 506979532 506979623
    0x80307050403060509070f0312050f210f012102011106011202270114030307060c02010c11070b0403080906040f03030804060c0f08042a1212110a 64
    0x1809500240403c40782d49040c00f000c80c00b890390000d40c10040e82d101124108680c0c1c91642c864001e840d030380c42450181300050085c0a09192031101030114601d07d008100c0e00e100c0907910500c144030f4020b10b000c141001e554014442c68116480c81c85010f15450400c03600f80c02c6030b00060390814102c0024000d0f80c89590004500b2440050a100c1d045109682d110801500c0400b240c040d00c0f211100b564001700000c0041022a00c01103001500210140560b8038001e01030300c50f05d040e81c20b11000c000150b03444000440c0d1080c1d0000c00030300c01006400c083c0c402c5a0a004070f9000911440c070000d080c0b0540403a5010065a490342124028030030b5001c3c54005950720314025015010864007541c8540c54582214a0580034080d004030242265441e4042c960712656102043c0315285201d5064482c2880c1e0398990204607030020020b05940015400d5002940c40c04003500030491030141d00b000741078600400ca19800264000c900c5070702c90420194410405480c0d00700d03417001160005400d9200c034092 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506982032 1250 506980782 506980787
    0x150c1104240b090907050c0d1b0212060f06040c0507060b0a0f1206150501170705041a030a06080c0d1103010207020409030e01020c030706140c1203040309090b0405070503011e03080307 81
    0x74a0b80c0b12054404c0b000c29170b034121301a18940241c41c002811ba400030146a2451441071034004000c150400407455619100d03000b0865428040c400d160007a84050300344480c010704401c07002e03440101110f090000005c0e81d40020501d00a90324024a1661a0819640d55907284a4007101500101e072950110320796428010b481c814049406641551408048181000d1340c1354141c41501c2060b110304124014a012034401c00070b00800e0481023041c148004908409042d030001d000b040c50785010b030344a060100c5000d003118140d600039259644501c491014035261401d00610b810740103845071340c4039950348022174003a01c202d4200075406440d180103c0101504000d41001d032903000e03402c540003e0b4950040c95a21142d500407000483c0f80300d000d0341c0440c7c10300170003404607403294401d41c0c40e040c40445001803903801c251411000b1441d26482400020890300c0354148035081220240a1414042d0010300284018011001042c6204210704d00c000c0c0041ca00034011039028400f6607882c680070400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506983282 1250 506982032 506982037
    0x122a0304270f020412030f02120c0a03020601170c0913020301020406092103021b0d05060c0a0f0203280e18090705030601300b010b04150c1104240b 65
    0x70500c425142c060b824445144074401d5600391606178119002d00c6407191406c1d110099441807580862084501544040766002d000d41105000303c3e008159a0201c4e1034041d00b0480140c00c0030205040300300001c00381c0500001d120780800c809444034078490705d6040700031041200005001e500f40d800042c00081913540300e2010070403500741e80180d0844880d0800080800c00d00014040c006900088084d8041c0014030225004d21000400040d245602c07641c0e0181044412a100d8000b8a804a4842c0d03070700d5040070f015228488036101a500d0030103d900405605c0c0342d010403e25000b4401c0d44010542c9004948504a4160080020101052181d1444015202100d08074007a005038040000d80c4e04000514505a0b42082e0404110901506403c1045a90543c450301545200000700d000b09500400d0b040c0070f840c983c15100e558504003001c19075051062440d99081003401d410380c0010482001c41000c14200484000c5400e494006030303415440c03580403810039400b1f0241c0000518101a400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506984532 1250 506983282 506983349
    0x3100e12120a050106020f0601050f060412120336020a24021902011d0f060a0201090201170708040f0615060e09070207180507051b030c122a0304 64
    0x605001603170300c42d401280c45901e0360f0b000000c50742c0040010f100304d2900c00342d0f000c25050003800450410355202102810a01104000e4540010b4030062010070781e0f050080812100d0180b40c8280d15050f0f400400710000f07030303c0118251080d941e100840441d61050480303401085606082287c068030401103040c4544090502c0e00503104881242414551420075000d02c6c58058444044404440e100b20303083c141807801d002e6005810400c2c0040305d40d00c200242950005035400042c15250b5807002401c2c41e1040c0c5d00c840b84041151080100850f801386840d80c1c810340c0543d0700faa41031014a4020060400107061304d4020302c410384042101a88408500510041181d050010b034030f4010050f605d03140d640c014072030110700300d803000a803043d1182c0140703401c000189003031843e003119010111441081304110500340c0d0800581d80240d1503003001644814002e07080c0c6ca900c2d221150100d4080071704c031040f9110b1081e2040d01740e031181240074000d9800a00e81016143e40e40000040e48031000c854150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506985782 1250 506984532 506984551
    0x90b0307060f090522060609030311030715090213051e100806040f08040302101d151b011b022a0618040921090602030903100e1212 58
    0x100091582c8210b010b03101c100c682c1d86501c0903141c04c001c140004003420b82c9800785640700c400b0200c000302c5090b209600085c107007641d402c01c0d41401c40c40e0003040b84e50001a40300d00d9500500c0000045151089042034088a14000207242000307440421103c41103001a116194603000801c04541c02280d02e2908201482d041b007902548d0f101c0d000040c001c01800b90030030692018000800040100b500c3e01001401800c0791401d2035900e1707001809440e0307603892480021310500c10401044080c003400c03800c0c02104a42d100c4442c10403880c040040e00481c80c441b03c0c4444405a006203401c403c0d0b2016114440b8101c00f1002081400f401a664501910b407080504400c8258100c10400d03041c100d40410b031000708068a8a80000818004203480450b965881551a413040300064008a03002c15110a04c141d1030501d08414000078120318255449107080d50801c000004055070082100a00711502030303400a44c1c0c81d44c6a40c9646094181006c99a000300d0000700040c006940d80482c511400a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506987032 1250 506985782 506985793
    0x130905011b02240405120a03150902160204111c090c1e03060507030e0604030e0f041503150905060f0609180312150d06050907050402030f0f1e01090b03 67
    0x1140490340c8144410160050301c00e00d24000c5002c09003220b00321341060240d000c80301c4080c5001d070400325079844610210046540c035142060700e9500f200c00702c00200040d28085080101c03680d043e20754640911402840f40e40d561080311003203c00d80c0180d40c194480c00c035803004d1603541c3c101c5080084c90b0085c819100124203420002e1015041c0c00016030034800f02c02c403080c5241c80d544c0c941014220143c070b4007051603142d103034a0401e25010020188618041da88920f1201c0c10441840300c042c03491140c0351f02030b60424000003c034106030020282282d6102d031010410340c000d6104040100700c2c20780004c1250181c0c4007801701210b000c00c0207900815003215070200d961241d00e81040f2802c80da07002c61b0481d030424010710f0305018000343d5490b4040b03900100a490703520740900052451100700f00444900741d890003072019000007004207101410050b0303401c500e5400c2c981c0b0980003500c4020315801b01503800a0008507030b411566101c2d58041e1f180291018256100c074000c00c060b0040f109118040d101d01d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506988282 1250 506987032 506987081
    0x10c051804020c120a0e090403260615090f1c060b0f2d03030d0c03180519030216320906010e0319030f11030f04090b13090501 56
    0xd44212080070301c1c41402800c4c45001e01180b84001c1e0400801c0c0c03002d1102000c20352507551600705017035101f00d1180d40d40440680802a003038141c15240c2da601000089058104240d9850f08100392031803900401d030351a15249440c00049442d5141d01c650740c1c01481c0815a60800689041440380082c42024280400071565081c400b01d2006810240ea102c4103a40c05c0c2020442e852000d1414031140030042206141e001010900e19448031071503007400d69680180e100c046e43c1c10310569100030b003842401d1800250603140c4603600c0908030780ea46a41c800ca401039a040500800c50400c041d0300c03107001410389660b50301000047c803a0081c3c22030b0054000c11040001c1d81c1003d80315217405074000785007540c542c8489004407814040302e014103070503104510001500408640031408140d10039036560880b17808442000705041b914488005450b403082c40285140200d20056409440640723400149290350000098000022100d2400350186403c1032a018042c040d0400d91581100300c0134008003800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506989532 1250 506988282 506988289
    0x109050d0804021c1a04151d070807050a0e0c0c01110706060e0f040b07090302151312050a030f0c1b0906050d0c030b04030201022a0c06030405061302040e010c0518 72
    0x4e0b200000703040340c42030b4036441c4072800c48040c040e41040c05102141d40d00719014070310300d04a038281c3c00c0c24100340356100b500400805081041c03801038404a0050251145040089000301010b8007584401d90000000901084541c0b4280c500c0c138600e00d8024442c036041600b881e0443ea20940c0240c40190409070080b5000f840960620f0166006c00428031141da03d82c2c82c0c410704030102404081c01c00603205000009691030310090f41c0491106101c450f600d00b0080d0000294400660014a000313048407601c40c08a01d01158510f00c6e0340c0c05051104c441c0e01c480303c080312032151409005002510700039085481c015890340b001c05a03580324804001251711107007000f0340f404082320010680122003c0500005143c4003609030441d109000241c20700749182c1042841ba000c00b00103044200741e610924080c050100036198003c00191049441c6007050b4071041e4803508000c05101700600c801c1301c1503045485580c8050f180c00c0c200c0e030080003203883c4000d0040c80d640c0028411030a00250500702c210074074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506990782 1250 506989532 506989579
    0xa03050712030c0c02040e0c04060929031005100b07080304050d140a1202040905091c08040809010f090308040b0c010f020a050a140f0f1b01090c050f030109050d080402 74
    0x21443e110644c0040c1e49a00301300141568000084050240401800315516140076000c041c1c581801c0c04201c10180c2048a004500005014240b98800840400c00b40c1c0300810905905800e461001ca601d80e541400c1000d0b40080b03030301c405040c500004a180034491100003450103140b00c0e000b95409141c2d858421200740d03030a080c105030103a004002c01080c19009203015924104000e4026050940d0f4020380b0342126011200440540c0060303552606202c11815092076400c1c45090100c05c0d400e240d00c8805c900c1c056044d82c1d41c14041c4d00134159005170b00078240d0500465103c86920b40d11501d43d10500c0d00c035081465030311603070742c03c20340000c2c0300001a0080c0c0f0754042c0143d440c58104040141c00312410300d100030b8130740c040c0c1c0010030002c2240a20b040040000c00742c150082035036500f083d146402c4070005144401100c1c0d00d0155580e0025004100c81c070110b4030125400c0d041425020006801400041d40c014503178402c64291168280e041001d19110307030b000700c42051001c1c14142c549400c92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506992032 1250 506990782 506990801
    0xa05071106092d0609030c0d0302030c0d0b0609031c170408120c07060603080a120e0d0509030c090921070b07140918041704030201080112050c030a0305071203 70
    0xa03048010a5810f48070003081d02e42c640200401007050800750b0104030343c100102600c2009041d00000344070700c01e019040004c208580b1325031074218558070300080d1600c040e010b03003018403c459884d503080b000c0e1903860a05071540202c00900755289001d4052200280b500c9107600078010880c445043c26520014140f02c0e445642c2102e00e07a40744c000302c942d0400e0441c02c0100714100f4080280404800309010780302e640b0242d80305465607552010020406400c101c0c00b0750381100403e0900200c80301d541004204403d88410a0815540b51034a00c00041c0c00c0083c041c3c40300380c00c0ec4038281004101c01c0002410b01e0904809400d00024001219411185d4030031201c0291503c00c03050085450a8407495020303003600c85c1078140c1818114004c0000c1c0c0300030f086080a034601052102444107128080202598400b8009407282c43c103440c42c0d0001e030160341c0520a000da5440c0c5145000300344407040c81504200f0100500359201c16405150150a54201440c280e44034044007007556503940c064492002030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506993282 1250 506992032 506992051
    0x70f0305030702060a0201090b09010504031202041d1009020705010906201b070905010e0610050918060d02040204080619020a0804110102070803040f06030e030702011b0804030503030a05071106 85
    0x4144483d024041e40c1d40c0007240803c1150b68030704003280803941000e40139004d4019500045040e00b42402d00900c0400c00900c4001090301c108400c0100302060324503810402c1c1a1511450300e607030740318080a0014065480340d80820300020701030080081c1948642141c3c0d01c110810001d00e40300c05914003010010b402c0b0706a00000400c040f02c0ea07003481c42a8a90a40742c0201211149600c420010058440a1303000c060300b003080505205444c5800954601005a5450f145051160040004e50494551000321400d070f4010300c041002a100c50581503220341c1c001e00107564840c0d0342c608040c0d0302c800850321010340070140e19408006603040e00880b200388459030384442c420703102c03902c0d2203410b242e40111081c154461008005441e070400d03c003a000403c008060000040c4c94508058195204200d1130f00c80390300200034440c0180e800c40580700d00907004d40d12101d0b040b070f414034240002d0320658102a1581c40301004002c200400764103d544990180d60b2074410005900359029624003050741c00058 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506994532 1250 506993282 506993287
    0xc090513150e04080918071106100b0c0a061d0d0903050c06090d0615080c0a0b0307050a05040b0c070f05090403090e070e040501030c1a0a0507020402070303090204051008070f030503 80
    0x1110000b40300c220f4000e0302444a440c5010b010500007030300380000c141c011013091100301c200103003250403201d1b03849003161700740c09002c00d440c203142c02d10340c1d14105010303911040c100400c0300c8520100c204691030342654050740c00c001889009500250080080001013480d215103c081c003101c502c60728000b412a544840202401c0703508208022498100c09400b5401410140070500841d4590081d142408595400d41202d2070404081509040044000340c0c05801142c20400c844000102141da11036040d207441620303070302c550004659038410755000780510302011425030f01c1c405001c50320784205c0790860860501d1550710380900042150495000d0081466032800300810000e00c8140d0741e0000c0b0920340442ca16524000150881d802a001550300503803212040c460300e0b916000c0d1012400480003490300303102d13100700c0090440c07181c150300901440e004100e00307003058004e070080175811f94000d10600a900d0b1141c0b80c8000341d1100d200e591014480c002000506c01e0034070001406030781d0014081c2d407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506995782 1250 506994532 506994539
    0xb010c05070e0a020906030a0e1b09060d02060c030d1b090506121f0603050417090904150204090227151b10020c0f0d1812050f010c09051315 62
    0x1603a00d0b03002004101d42d550204085038203540c56200a511901590000050700c02c9422109490706018001505002c1c040c0c908454050356000d807001c5d408101161140d22014440c030105015000340f01610109110100d00300320241c1043c0c12540c240c10b007404100b480815400000c40c3c0c011f400744520f41c2c01c08003c004144000c42c81070500740d80301c90402c1c544500c00028540814140d850750b848200025580c40c1807208000311040f03940b9015808252071410204d4240014000c028054401407651186a4400100d6903d6406035001070803401400c5441b821480244801081540000c148801006a246501713203010001400c400031080e81c1e4074103102c03d000c46003603681c06000982d0b42c030748510b0000d800103810070700040c5034010008010706109041c9001e001d1800c0302d00380d500700600c40e000c02ca0340f005501010b44401100c0000300c10a03003840550800c00d082c20385000881240f54203001001b82100d8000d0604c40803101d0075140890140e440281038011102008030f01030038101c440710b040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506997032 1250 506995782 506995799
    0x2061b030717061212091c021c0f05011a010e010804051c0908070f0501120b0906012a030f02100b030d0f020709050112110303071112120c07090b010c0507 68
    0x440c0d01032006003032203100800b071100291601e0b20f030804e101071114000414403007c2c00c00600419045d290442c1204c1d02425940c00568001d0107042d0b0800410b1030703940c00c60306001c00c058a110001c1d030050001c0100e9126030400d29807a2408592840c081000c10503e811254810410284039075004030140100c0e02c1d0318000790000310601240001003107020600814103400600020008010117144104001d00d001d002600088280381c01c40c81d00c078907002005a854641c02e000b280d0110091a2007500036041c3c000c84038041041c1205009029100350000003010380110116404007500c1c1c00f100c401281c82a00035003610381c5080d4160305a00415088071000f805119100c0940b4018015030714920744a1810030f0417540309070301581c28402c04514440a02921075100301090a0549c0070350318041068032a055035003242400e460040015200c1002d2095003409440c0701201c0420704903903240c1000c00c1c51a07540c94107004440c44507181035030611003903020301c03c0b25040c0c7d81d11002074070301c5510744480d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506998282 1250 506997032 506997077
    0x306050601170a1a1e01020105090a03081906170a050c0402040f03020d03230d0b060307020327060705060a1802031222120c0602160b0906160302061b0307 68
    0x40c82c680320107003820f901c1255070780001760300081d650403404505401804002802e5070000b81001049401407004000480d610008090307000842c401042e6041c800b06a044005102a9100d419102070380440703c08003140114140000ca4068001c4a03414410141008200c0c4120700c038844480404200800c0181403103c0320311109802803c040e00107022416902c045940700d080e034405280ca00040c264881e100071300c1441d000c214196107040c1186041100695030388603d801400706443d54001703210340d00040c0c69422072003c80c06042c1544a1011b4a4070b01e0b602c14064990440b10750420070a40c2d41b1000035006000d4264004006000b60a081c0909040c80d921030307680c02e4030044002180c003286040e0400640020200320132480b555034100d041c02550141035800407011034102c002c8800d0401000c0d4203000035101d200c0d500540c2e0b400310f0700005140d8890002c11040300c1c0c10602d045400e043e00407a100d80310f80380c2d03802d58007442c103d0843c03404207600c400c9034501c011416540385168a00d035007540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506999532 1250 506998282 506998301
    0xc1b0506060a0e09030403060b131812051903050402032a01030b090609010501270b07051b150c030403020907090503060702061e06010c050a060222120b2a040306050601170a 76
    0x14800c400c5140c84098400e454180301d0346003440c0345a60700d1403300704200f00d41e09180d84651070164109110310204082004441128508260f03c0384041400c3d581d0901540174141c0320400320000b0044026070401000c4501d20800d800f203450b140e10b11541d1306020407864031616008003506d18982c00d000064443d034840203140d6020759a44054014035004036015032020300a1119526200e60303492515520b010904510162407000d18142020f032515002612002e44c100086400d85484014065030701e540215400650301460200601c4803060304141110113541c4140c054411a036110b540c10399072030400703aa281c6265001e00c01200351050308074034169000801450715046688441c3c071554505025500c00381d880d10703030014404188000c0d8810800281d85032103411050f052a06001101c180c407417900c003070083c21848000810707500300306069100034405e0b4040d03900022301e0201280c0035500180400c42d034051500c0302007007542d03004461106010b120103c2a500a43d541c4420b000a441101e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507000782 1250 506999532 506999539
    0xf0f08040305010903082502150702030c010609060f0e1005060904140711011b023301060315090203040b160e03031809010b030403050a030c1b0506060a0e09030403060b 74
    0x840002c42c00e00600c0354072400795030f5156003801d00315243d140c5414212402d050300510b0100d41f0300042c1d00810400d04030a581c20042d403130740e40d035420141e05511440e03140302010b501c1c24030041143c1c41c2a91241059801c100a0919115107448403840002020b030b40840380d103074007000108424580100103040201c40500b02080001101408085000d0203503118801304840100004d2206402d00c00c0c8150766400080450724100750050284d01d940200000742481034503100100d11300b040458070640719903560b0449921030360b0744580080040181200d4110903a2560380d002404545600949001c0d81e0400390204075a2950023100c1d0041c5e41c80c4000302c007400704804102500341d40030701c05041d210160200f15000c0d460080100074940070160010084610140240f20200b1350060559016640a080024022411001c1901c510b142c60313181c040f40050806200b41042804a01c007401031000b695580403d9848500fa224048001c580c64403441c0c0c01407004001140d81a00074090000d00036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507002032 1250 507000782 507000787
    0x71a0c070504050705030406150f060e0316030c08070e1006031a0307121b060203070b09070f170f060106141606060801020318030901050304060c1b03020705030d0c0f0f08 75
    0x460102d402e40d00c046458002040c4040200403d0001c14040c052002040c0044040304c2400c09121030b0104045000b500d040098144200c05c0d180c9080201ca0081c000c0c40402050481d5079180c8280c420485000340ca80d035001c0c1301400950504c208213803501406255055141c0780341403100840080c8104c144443e10b0700f4040d42075201d181c4062100034054010405013034442c00090506141042d0104000e032510b221920080001e15408010b88040c140e02910010450710303034044080c07030201c07941c018810300c1d040c1100000343c0c0e8400383c4408450681c807a0a451541d04501010754130b0340750034132400d40131859442d0711003941e0401d040180880c2103442d4103003415214580300c0170116656a00411940d82d0b0001c14031005414254002948800c1c5100071450004154002822400080d10040c4031329116400d11040764022070310b02101c201942e1802c40040b40c01d0030000d561318243e1248500a000c0c020113282c0d1a4400c2282c101c201c2d03000340c4440141c2d402562840050200340100f0788204805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507003282 1250 507002032 507002039
    0xb03210d1a0103060509010302090c07050f010509030a0f020a0c09150e090114060a180c0c05030703090302040605060c060103080a0306080a0b0a060b12071d06160c08071a0c07 77
    0x641c8299006203407642880300940e07005a0000d82110b01c240c0080d4403400038072004100503038800c8031103039120500085c9661541d4491400602d0f2040c1100240d60550920302048407548000001d080c203107525546000440702d42c0c41050385c8980c547d510140c01140032144c00d204c9442c913600202c9800c0380c400d104170485591030300d091588400039201d51009035105c41c90040c85603480a411500315a084030910f090f80d19040810a088085421407001180c445006140307007802052132554542c1c014060700d40d281c10301d03e8014503140c0c0d5400101e10861502c0380c081a541003420035a0700c4000490014280399080d03440742d4840c0d80080c8541e00415440e408040349160f8203114003505c82d4400c089208d42401d20b40f2f5950241c1e0310540229030040300c20700c02c48110b410040600390b006152410088004c00203030480c44880300810a09503004000050000000078042c44500c41c99030188980030192500c41e0142d40d281e800a1041c9204141c18000b013000704004040144034800010f400c41e10340c03030754 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507004532 1250 507003282 507003307
    0x50d0b06120f03030f160207090905120d05060a06030c051b0703230111032211040516030e010e07150507050d0e0111010c120207060905030c0715030b0321 68
    0x1842c1d459480a8002009000032400c8215406800040c0404210b030301030803c100017541da0203640714802880e901c4075004c0d41480024840c0803148010000a55a1340d0044400b403070240c1010344800707024000070800041c1d41403180c403a0780700c0150181d0b1010302e00301da10190004080404d001c1e11115018143d800400648162030400328580101500d1000801440480303003100d5070000e030424002010002c2105030300f0003101e810032014440c0407500c44181c45003001c1c2c80c610607602280350054a44030510424440c6480c6100d800c0002d50b809114425005c2600c60907966480944c1e0565400404140000a1208031200842d031a900e051410031400d512114034000c00412040c01040d01083c10b0078103541c1c0728004200507003001c00280001d8a041c80001e211480c940000c820640d800b15015082203055004000ca058109044907207a4a004048949902c80f40c4198455121012102c8030250300074002c0402a100040150542002e0104848140c00c51444109908001040400020712 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507005782 1250 507004532 507004543
    0xf110f060112051c27050d0b0a02090306071d191214010207120806100f14090a0b09040b01090b040918150509060c070c120204091e06060b04050d0b0612 67
    0x10580c2d585520440b4032416041d6040181c4040c58840905030006d20030342d03c407201c803200e41d258002042e107011ba035120300c2c000090007241080c960500400d0140200c0d84e81c400580310160716000543d045070401e0301c0801030301c203402d05000f85440341d11000800201020403000c90940c0c1c056040d008903000c42002890072a804018200c8030600d510f900003410b01c1d0f100314010752014003542c00c4141071002d00740140c50708940304900320400c10f1901d10040c80040000903a62035103000760100300c0c0300791518281c00840c0c0041c0e24440c0102d241001d16242984500c0d26042203a03106581103203450b04014500025106a03240e00750803040303288c10240010346100900306175040c00100011141410142c640c00c161029121121a65090010102080c40009644101c2e054040d000350390a840e440440d01800038160081c195040a442c080020803014800d10045880b400b0300b000540c0c0c49440e06500c5010b01d000d140e0f00a03030708283d0940010b04040046800c0344005049020503800b003a650707880c21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507007032 1250 507005782 507005833
    0xb040303050408060106082e081f05090604120c0f08040806071403160c0f0210050c010605010914130618090303050a2f13060f110f06011205 62
    0x81c0001001c2104440510074180505414507066401e400c012035051555200c001d10f090003040c03028030510072082c3c0841540010440c001c20f548002d1718401e2904014405544c81c24601820320002609107180812468892584014200780c1c21044200480312801c0e40d1000304c850ba8400300040020841c2e02c00a04002c000b00c0008282a00d4410030040000d0040390f48014100340034014885012805024440d100307090f07140141e21590542040c91011361984000f941049061810214456100c002400020344005c001c3c840d080c0e4a13001101d644086100b68806c3e003603c15504942031404401c0e61b050300c45101c0020802e203407608214440e0b0705190340c14102c156502d2014004045d0507018460f4400f18130702c420003008504c1c3d140590111328680b200c07112043c860a5098540342d82209841301d80b450034202d91840754441c070015001c0300d8280c5802012400001246074000307000203070400245402400b8000302d0740380c901d03e0b00c035415044000b262203005180203d100c88100441c1003450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507008282 1250 507007032 507007037
    0x618072103020d090e0a022107030e06090c0303180f030d020609073015060312080a1b0819110703390c1203080603011118060c070b040303 61
    0x94825850040c1c41c000050310440c0901030384c03031010040002c2201190342c1c490640c0402507616045500891280082c1d0300c1990385140054041c00240c40d810b601106010580004a07904c03622004034840d96459054481c6905178420070213510a605089448151800040c080c018449004d0340040e00b4240360b002c0f402d0069214000b0840c0480d81000444020612844141400c18100800714180b014080e800d203d61020700d10440c081203541c01c1c03500b02c050000c00f401c128042d120310b803119440c01810406000140388a02180c13441805118041d610390424480384140c0b465036405445807c07008283c020054801c0a00c40320a8919002c4c0c03080d0046000c510507950300d83e07440d02a00340b20110445000442c540d41000c00714a078002e0410f0b080301c507400c2d043c415a08052425500c0c9400641060701043d24240d49181050341011115001d258101d0091200c99801114005103006441b0041c06030303105200c042c1440c1c10418000c120515030001524030042d201c11100390036920a0f0b104800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507009532 1250 507008282 507008339
    0x5130b0c0604170702061210050a0308030108120315041515090504060b0c07090b0d080d020a020c06090f0d05031902060a0b04020f0d0b121e010509060405061807 71
    0x4218500b0f9103800342042d016101c0c1d0502007643c02103101c1d405000e691504c21070300c1c940452031085041d40c84400401c80101301d0000181caa00c0c182246400a1241c00b20502c42e0343c8644403c3c90a41082c5c0781b00c0c40620b2118401c140244041101030030401c0181180c00e88480b00c041034022480c1c450752005235140d200c021003c1d2409040c4021a140c0380c0c0400b0300c0720011f2020481c0f01201142c0c840031550214400315054036030500047c501071105000130314100c0002400d000240480d0080c0044081940940d40400304901c14000c45125107070400c2d5109c140c807020f034101780c602030460100c03945c0924210b80c20180400c02c80003180300307000010009a8013100400090030304500480f408144265015420f08500440300e00c640e0041c0c0c0100407880d5203d00c4044041d0300e82e034070802002c802c80d0044982d0203032034491000018200b414000748039420140080da81e90030000d00d0354011781c0c0c480300500740e03660f410b041250703400751102d004221400341010010b007018050104840b40030703413410344c0c81 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507010782 1250 507009532 507009541
    0xd0f0f05010e010b1c03050406080903091e041503051c021203040606150c15090201030212010e010603060503070806070305040c2c07111c02070b0d06050a1a070305130b0c06 76
    0x10b0105c4444d40389090300300b18035100b01c001a0f40030050f42c040b2502c50a0805098450f20781e010b0441c020601c0d010707003181408850b4412811100c0c0d10901212059400f001500b00c0d180041c200c00445000c090001d90001c8200e6081403600e40c1000c015070070a2041d16082031010445401d240c0c019138059400325101c810902181e16455008540d4110600f030444c9403810640d00e215004405600d084146699271140b01d0640e40281c0458640c075404100800300b9607140d9103414040c180c00e0089000081ca046004507481c20005035140070b8583e410002c3c1055510810100d025040051080340d0b48521400c0021391a0b4141401c0194100c01c003040701d074041000044041c40c0d61004003808200400c901d41044080030201c2c11905060071041c07801054844160241e01c0c000075a8031001800000042e40621240b0307643c0020250b6100301c403808005940c4c0e14003003144100b216201100480c0801407040000e001c0c1005103c0c0800701c0302211481c0350396085441064001300360801c03481c0c00200800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507012032 1250 507010782 507010789
    0x15051c0b0306130f0f1703070906080702010207020303040b1b0d0206160c0f020f0114120a0c050702060a0e04060e15030105010e130201080a1d150f04020d0f0f05010e010b 75
    0x483c2e101d681104000c1c1510500c0d126820074440050300908146044081201800110b68180b0450362841501c141d803810b2000002341030720014401c00c0c0026008101242c12248103008130303460290000e000310b003802d040690401d89540460a20b0800c0c1e0200301c84116440360900520b08001a160081c00303070b61a0000c00b032000340741030b04088020886064030460014100e131812004668054031074000c81d03058000107036035480d0a08000750716410702180c440c0309148010452881012101014059620030000a8a49004028000b075010f00103201036403e491003400c006030300d080300400c0840c895581798500d440e02c2c1e00a5440760220020940000458207003401014010030301c0340a06c00c2a46004440e8410341c00400900038104807260b8042640c16010380c01546890884200d22038002c01d03d58032880d80c1360030700140c040b4001d400100141c0b15503107140d2414400d54014101900940355907a8070314000c46070003400c95071303101d005405c0ca0102c0d01c00d20854003194014000000d40c0346814042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507013282 1250 507012032 507012043
    0x3051812070303091406040605070611031f08150601052b1a0d150b040608010e03030105031501060e120f0706050c010b031b040504050a0f03080f010b031015051c0b03 73
    0x199460041e8240003580c5c64a0700c0302114211906072034000c0c1c459210740b8000010705810b0222021401d40802031294201e00f40359510311088a1061101c1e4a540d19050651690040d02e0155882c40305600090f07101d502441c02001602c101c044004400200c0810f0642043e078000550f000003660303003003404a840a20104204144002c881c0c0b0b901108103070f80d840880854040d800034503a0f8175840121016201d60300030b10b0240001c0790081c03022001d2425125640d400034820b01d4824451a103000396140040d40713010b0b0507600e2a035100c0343c3d402001c030144030448070b040c0084941c03071207950f2118102d50410b11603c0041e051640e107140e03545d010300f0103060948800d020994425000142c02d200503000102044603800300a8401048594490800034100854010040d01c681c20b6181650300b0141c4c4011442e1048100c04c03800d0100e80d1b00c5054000d0640002c03100345411000c2c8400911015100c0300e140da00b800d4040c9070440ca00108076a122200701c08540007280c545803511000c00782d5140034882c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507014388 1106 507013282 507013289
    0xf01080f120f0c06090a02011b121b140c030706030c0c140304030218100e01120f060b040f0204150e061b031213022103070305181207030309 62
    0x429140d54199008a00080548511f5042c27540f842c011500c0603a00b008000484815101c801e403032030181944141c4a0b99042d200c0c1800080c144844206048941c034041d24220713481109242ca00609600100181404e047d6510f04007588118180d07030700358201d894904502c0d0410f403854118030940e04041d4002c0302c00008081c1c05080700c0080c03800313088081d54141080380d5072604030700e00040c02e0040104102e031501507100450581c401c0003a6260003200006022a02c0340001811110400e1888911b5030300490304000d09080c8284105c08c80f00b250404002c80110760700011040c1c0b00c0c89030441c00f12703110800300101c19041002901c102d441d145140d005c4508086140c0e10351120a004101d12a400300e9030381030b036071074038484a070015a65044001e41c18420240e070152031980140301e4004404649941106c050307031b54442c98180f00f81c5030700d0250074198118200180260101e41 = true := by decide +kernel

theorem cover : BRFrame.Cov 506834532 507014388 := by
  have h0 := BRFrame.cov_init 506834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 506834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 506834532 ≤ n) (h2 : n < 507014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
