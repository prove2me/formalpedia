-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:03:15.650454+00:00
-- url     : https://prove2.me/submissions/928dfc6e-10c2-4d91-9ecd-d42f370fe333

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87230216 ≤ n < 87410072 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87231466 1250 87230216 87230219
    0x306120c090f2903012a030b0307050307060c1104140f04030c020603090f060105040507090902070f0209180106080102211803040902040509010807030215030718030303050a051003020a060c0302030403060e06040c 93
    0x742d518050413801801c001c1340c081c0019a5580d07c20303400001401d41c007070700720707642d030303521940040c0ca05000c40c1d001800050f160981641001507440e080c020a4005640c00d000600d06400c640642050091081030703058143d000050500d0310444460010030b801529442e40d07400c1030292903480d4500c20030000304510820780001401c0c103252080360700c80c689075500c4034519405c00e14442c0195200c40300680f5613030624440b09025903520300c403650141c40400300e442180d646c20014a401d641d001e9101841c264414807804a010201e188030340b044024042c0d80c1240c80d517074031141c40039241510186030114070000c60301080b03d5405500038010354200301c0d400e0a4581c0d032000b101c0d65500c114040250000e8400c80303c1040c1c4070004014682100b071a061010440d00c0c121202006004a5402900000d880303100784a0b4400c5140b02d840e8200425003182480c290441d0045071041040d481040100050b103011181031501c01d00070346024581c8900f0902c03810070381a6940e950b070501524282c0d40300d0f100e10f00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87232716 1250 87231466 87231491
    0xb06011d030304170106081002430201051c06051206101502030f0a0e040506090603120d02090306010e07090803031006050d0905010e0a030306120c090f290301 70
    0x2a03018100c80001c000714030f4036042840342c041c0b8002c980501c014940d00c426002c0f405a105000c100d0320300e0030081e130041e12551b01591140c00740005403961b0b086801c40e55070b00100c00c080c0003d035011281c82203400306140d003040d1004880504c181543d84140100840800304002c6282c0c10800840300300b25450500600c0310a02192244410307a4a400030701001682027004030381c4241c29042c821000e006407802c04000c03416100040d480740003e4800508180341000d110314040c41120380042090358450322078031303140c00460f070341d50040c41d6826241c0710042612a00c810b1280c0440d0300401000d410740e019541e465000982d0003005650b001c1c00319481c0701010481c003400100b520301c1804e40c038480b0504280780c04010f64080d40000042e4511540f02e0100c2804600240264101c0c3e492500080000d03107120706004045070941d070802c3c803807130001108440104044c51404000c3e600707250000211003004100150040111241152a0001c10f82c118031013104400760340f981c0044194000d00c4080100d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87233966 1250 87232716 87232757
    0x50d050414070503011a09040303060302030d0801181107020108190f0516030207020904031b02060a05191d01140d05042f0a0b09010c05030d0e16030308010611070308070b0601 77
    0x1125141c1b08158243d840080d1500c40c004070f40260003420700189568503a00400c3c10100086403600100342d1640041020a180c50304640071042080b2080241082d030404440c043e10619070080d040041e0314000c10007241d4032000c0481c01c4030282508002454a04501d00c0143c441228200d600080080440b10350364001d00884003c3c03035004200d02016911a87c0c140e40078a0301d50011002c1c441e41c03181c0c40c00143c460000030b10444005490703031900d0300386c89035440044004440004042204100c0300d581c49403003415001d00e100b88242060b040c5c0b1042c0302c410840c14040d86407200c04040c01d1005110a02c10702c044407005113206000104481f03c60144096061740244540c2600030040c400204014541d54000e84880401450010004200c0d03407034a901d56040400c481c401540c1d82c134420309103072008200c4001e400c44204d0811980c0ca1440d28058000079051148074280305d0554020b0000c81d0041c8503840245a2200c40d2544884150803d04440c60048070140e0102d20384281c07441031803000d00f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87235216 1250 87233966 87233981
    0x50a121b030c030f060f050a0203012c071d0607240e210909010305011a0103050f060108041b03110405181b06090a08060702150114060a050d05041407050301 69
    0x100301e44806078510354031041c020107018826600d003542d1b038180a04010840c041c5074002c0418800250b102e505000b140d0701010205226403041310301061500244458402c11a94801c4a50800090110283d030401d000d0700c11400d000342e4020743c001b4140e000c02000f174a0403002c00080383d14030000d00c0611480c141c100e40c86561034400300d9122480540d40c070b88400040d0501710725a114504c0c100020315000c0342040c44280c1084800365103c00c118034000002e0064482c4446e0246000c0c0150f003420400003190940151000781000000030000d002d0199802601c0b040142da600400d083c107640b4100044c00700d11031442c0700d10841c14903000c02c00707804154450031509600400a01540c100c8111110401c502e02c43c503c940210b0140820764217a030311182260024800c0402804c183e140c0800c0007410480603000481d4411603c10051180c0c103828050458118001d48031242c0d0307100c040d0401e45041c060340f85200d203d58241002c010400c0541450301441030130f50300441e50036544507400c041c2640e600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87236466 1250 87235216 87235223
    0xf05010923040204030f0b0933041112010b010305010909030806041a041103091903021507031b020c01110c060d0207020f030307120905220207050106050a121b03 71
    0x2800c1030003a005007004003454038a0004100600d4603940c0c1e0354030882c1c10b40c0c14009590014400e000c025440f1070a0081401c0501e111220554041c4101400d001840480030058070fa08002c0000404000c00c0f0320389124000e20040c91561503415806a00d80079041400010340001d04040000405003401c0c0150040c003036240d121001585d0f500c1c020b010082070b070700720400582c01d40c0044140d4980c80d14414104a01420810a5900c1c40d104403450320702402e80d40c80c41c3d494002d490140f4042680410302d42c0c1c4d41d0900c016860b81a842e0000102d0140402c646100b41c065802c1e2901203c2903000120519400360a0302c0c0d2a90603030324208a541c85c0c288034400641c00c2075080041c1e0740303d10599801840310f68801002c01c101c2c000e103200400d145822040080700c68100c00c031171443c103181c3c00812207401414111614900f190078010082c110300540001c0440054011030401e04001e0207400c01c8015080c0a0602648259a0f05485500e100281000d41d00c407a8116181e250001010302d0880a03640c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87237716 1250 87236466 87236489
    0x92105130e090a02060a0306050405061915030209040609050103110306040b160203130608041a01050109060e040b1f12060528080106140a0501030b01020604060c020a05030f040f050109 81
    0x980301c0c0219007050300401c03084190103400c0c0503000580d15100600004032240d58001003407410201880200da5001c1c0c20389120b140c40240640711020a085014141e60034901c42a40c03014580d40180c0280c0200a006075010341404804a00280207034403843c1268010320444554614034000d25850b1071090340d02034000c03001140080e468480d8600f0183c14480c0d2441264501070196880e00300c41c079070513001800014444010310051240c02c241d8148030840001000300954500400a07040040e98461202440f0b403038401202507695a500c02003040802800c007212036600d2042a007a42c004401000001c505092405004000d50b440340c6415108040c0c80d4404412100301c080456207a40760714440c4445400a01080040c020301800b030003007012840001003440444100980401a600544e040524202e100041681d002803550740144d00240d001443c41000407049041050013400985180700001d07100300c3c081c00d140001d00840e60b500d1504000251240011200c8a24510076508000d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87238966 1250 87237716 87237719
    0xe09040204111c0e0c0307080601052e0206040b150a05090903040314011a01030209030a06050907260c01031404060203090705090a020a090503030412080f0c0109210513 74
    0x8040e4014400218050007a030306040140e801c00c04841d8071041070660141e22003c44c265800e1041204200044044020f4002d0300c0c10045415920201482654420b41200303508203038072105074039034050000d80a0101e00415115183c0a9070347c07202520201d0304441a08002110210034250400700c11800503c2842d803107181c081040203013500078100d010a030204100c000005000014a03102c0700044400100700d1441c29404a0300d0442c010900314123140c010010305003542d4010440f481d006500050000c3d860b159001d8035460007105410820404075494114440c050000220454035031030907003280d51381c0124800440554440c064000d000008181c046400540c91341c0155a002c4006400c030f031a01c07540c0c2e80024500500c03e803100d20b0b030fa550001340342d0b019582c012000f40103070105030b0080d1315081c0352440c60790508007118805001c003200410300d040c8a0f90b50b03004840c08008a4402444000428101603002610031420f5081c400408101d05892601590980360141d10224007400043d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87240216 1250 87238966 87238969
    0x1501090b04030305090319030c11100807030c120c0905150a05070f0609060507050c010c0905032d060109020405100903020102101a2e020109080706020c0304030803010803031005010e090402 83
    0x15040400401e906014090300407020030b00407c982102180260f603803440d01c654030f0405509600103c9100ba00070050103074442d031115080790180b90050041e140c005101254070100719a61000100c40c03412a40c2440000007480390300c450039100f9103104a81d044008042105040340c03d100c0c0721003000201c3c1c01440b5a00220b50031002401c0d20a001ea800030070f4078010380d503502d401c4900c21108080031800c085017640385e054091160b8807480c0d10038103044044c9424800000d0341c50030101d5444444500da401c0242002c408a030815900d494448100d40c045e5845201900107500540a030900500d80c1c0c590150b10b20f44214058411030380c06030044d0850507680000103001c0c083c64030103407100f445826211007042e241c0702c0c6c8024501d042526031074158007001c0301c4001c81d0881c1030403207400c5a05050090000c81c000f0b50441d0040ea40c440001650380442d0300c034003811400b483d480503042481c007000000340342c84040011445100c0846541c0c030341daa1543c00540d402034400c08201c0d0800350718800503005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87241466 1250 87240216 87240227
    0x311031e0703020f0a0801050403080103060c02031206090603030f0c0102031510080601030f090807060f0c030903090b0a11071404050714340303020903070815041e15051501090b040303 81
    0x2138401c00740011540c036031603908aa0a41e10203840442c00070320500010401d002451241c0462000d181c400345107822072501d0940003501016150a21444000e030100704940c0c0c00b00211491061302c10070302074482210300042030003504201c4040841d00c0441d20408171518003030081c510318006e141c0350401d0311780300e50004400811000240300181c0f40d883e812100450780d544042c0001920a0303602140b90000c21803080c0503203110341c0406040c18240039219000036000302c022000d807401031039260b0b10780c8412542240c0c1001d4045402049005214000c00d00c161a560359046400c016107050101c0c2c0c030340c100201c0f04190500d900002101040c0304600001e01c0350050604805100a59030056100c451544203c82030f110300100c02181d40020100803505041c0940401040100040c0c01444803202c4105a940350040006255041c80d41c04040b1b10b04040e81c01f00c0055030468030001c0e4a07559490b110000f0130042c3e139105d250307160101e0728404c2517114a9115050325080074116051900d156070a60701c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87242716 1250 87241466 87241489
    0x308030f060310110d0609050610030e07030b07020303011d13060b0a0b031503060a0e06040209040c150309050f0f0715020102040302121617030406080618010311031e070302 76
    0x5040c0603030050340003e41107600a0b003640c03420800116964142ca40e800302d0440300260702c0b0005260901c000c000380c80e80d44144d60319044919040101e20a520b04011609101094000501055402c01401b01d4954000041c50603100e014480240d800c10819444260031021601d60020001c2c404c10800011a1030300003105c10500508005140c6480700019507460300b0490711803405002103d100c40092600b08403042c2c026440d10810040c40560b0080030740c035044000d10190281d0b00001c0402e00b080f59014222004080e0000c036000c12540e100360041c09000d40c8202641c42e17200e000c2d910403c4520104040c29030341001c1c0300802c011807620034404007003504a01d4003000d65600340000409038641400d207031800700d0b56030007524400011810851107c141e03500010040f84401d6800712a45070004201d80550307006042c0021280d40d07801c0041d41901000e04490040407800e000042008120148210092000c0381a20350000c01420580380944c8542c030742007200c1d40140410000742c02e0900300d081d0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87243966 1250 87242716 87242719
    0x1120207110114120a021c0b0901050f0604090501090203040c1409061302131403010c26060a15080403020706050a080c16140304060f03020408150a02091207030209010501090308030f06 81
    0x742031540a041c040c01c139036011941c02051303940024151000e2092043c070012003034018581002181e00740000300302a42030500400d4012801040030410556503642030b40c0082c000c400003480301d9a1103410450180d04243c2d070440340c82c0c00d46100803441e0503ea04502070800c0010340728101e03680d10345003000159402d203000c00020a0b8208100d04c49000d55080c1013015000c1d10036051450380d1038100b45030840d12520b40e031004001c50307805219201e48038520b0300789583c441304c4149100b640381c2400054032840a544551241404580c64a200a41140752244030b24040d030203440e211070b6164030994203446904007040002d800440012035482483d0060204505404041180900c06507102c920b0301c0300c40c4000301c5c01c0d0b60000ca800c10032943d00040d2154024003a282c00c0d42001d1034804042e0750381000d8091a84000000c03000030300c09040941c165280701c980249065040000d81803200d4036076146020903401400c0640000c24594010740c00d01c0116580303d020b140c42d69945200300c9041c04000391009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87245216 1250 87243966 87244007
    0xb0402010c020f0d0804081606090902070302190b06030c0105030106020c040e0f03070c03050f0102090f10020a080d0c17090715020304050a030606140a03080a03020906090901030b0105011202071101 87
    0x8010f490f00701e201d00160f441100700c40d51b25802c2002c0d0925058008142d48440b03003001c5014440345a02c440d245044510a00300076171a10442d1030180d0a011003603950160384425400070409000b81d081840380942c000f50b003620171801c0020011911071100340120380140e1311441c1014200c0c1001d9114a0615039800240c541d80c15031143c0d0a42541c0c810365060719012180041801800307010300400702809008030003140b42140c1040851a50b1103800381c4588a141004840b540c114000d0002e0810743c0d1380078164641e1484c89a10180041c0307100300d140c01c0011603800c404500e5980c0450424040c00c80f01300100209450100305a00f0300a40b44001c10440c00244400189911642c140364007851046001142c0c16007041205200044d0141109105405514003000410700f140c1c21181c1c0210755180c0942c1d9008071030b011500c9449040d2041343c219090200010a0003991003400b816141c00343e80341e042d81c40d2810200d00030390140c010080e01100c0c59403203034442c45d800307810016030140001250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87246466 1250 87245216 87245239
    0xb1902040b070311060106030b031504240204150c1e0819020616050a0c12051608190914041a030105070e01080c0f030f06040902090106020a060b0d0b0402010c02 71
    0x41c2100303038000342c030110301145071006010440b16040c001180901003070300c0d080140315018800a5030780c039452041c00500c40f2055010400303020f031141c1d03c0920756407020460f0f20308003c0b41400d103000390701070704c40c0702c80100300c41d01c00440d035610502d404107600c1e800c0070003051100508420360308542003000007203c011200300300c02c0c201881c01842000003159150064100c0c0d19240e0541e040308400301c10040204182000034041150700705446a1300d140d005010134080b405414801e0780c841c401e0214071111518081800c4c42008405401041c0074000d51089111450021006075903110450145480e045200c072683d9405050a074800031050382070340310307031904904a000864210354040e9008400921140070030007131541c0010382181c01403c241d0100c1d14000901100c1c900502010b81f0520355000381c413010030b2031a43c0781d800c040d04050b0020400d4215503500e18010b0b60b107000d1580c046841604100d8007052601d000d011210000d604450840d005035101da004441410008034100d0388903010001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87247716 1250 87246466 87246479
    0x110702040b24030912070f1506120606080717070e04020402040509010801050f06060f0912030c0d09080f030a0c0f1407080a0201020c060406090e04030c0503030a05060f030a0b190204 80
    0x3000342d5414010b18003036803401c2100100d41004c80600307901d020320300100400d400098200d40c0d0481043e400180040380155407048220103421154046458800b011040d901403061a501890403104c0030000c0b0f4005c0c43da210200540040c1101d0042c60316004914100040449485580c0d409440180018a0680c5500004038050f401381c101d818983e64a008114008400c0400c15411403c2152802d04101540d25a1906032040b201c0c4140115240903002c0c507481010002c0c0c400407403941c000e640804000c607000a1038146580b04081071482240c400c0c1d8200c2d000402140c21420142e5075443e000f84560b101c424860700103000c01c81d8034503038002d11081c203107000b44810400303001d1140181000d94801e000081c078003240c691780350b4842c002c100301c10018260000040400c9031380010f46295240e40f2401c068500f002c410780302401c00c6c0400400c04c50b03003403980d0384802c0c401c020071240c41e4404905142850f80d01d202d00c200050400b803074607000c01c80744083c855110340c04030070101c005480c4c03503190309 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87248966 1250 87247716 87247759
    0x130e06030a1b2102040b01030b0f0d1403181806060714100c030b03160e0703050603100501090c08090a03080123190302090603031806090105040909150c03110702040b 73
    0x221080c0703d900f9500114011860180641a500d501c00d103414410480618002046070020702030fa2840380d4400c4c40c0034810003500050b901444030002050700c5c1c42d8130b000c2034290100c9180248943c81a003450360a2031201c21510201406402c02800d80c900b003240ca0750301c00e40c903889180d40100041c41145074440c840110b0340140e100071041076078045480382405003031500d07000740b01460a003c5d01c0742c000c090250b003031410b000740ea2241c003d01c0c01091079217401005c213080c6400c03401c416100038204000030441e108160030a6040c0d01c4195649005555800042510351400150003000074019800400c020080c414421104080c4142d017502c1e03640c5100000b030b000d0030300c4102c200d00328041201c0c10000d6161442c01c20360b11540c15809185400c8540030320312007050980b1810343c4106000300711a0f0182e403050040d140039040b444420802000b060501c4006021700c1244001824280304010b96038a10a0040c226404450702c4403d0401c560346c0d007080064099015015048940d0b2583d11000c0c0d013814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87250216 1250 87248966 87248999
    0xa0309080a0c030917191a010b04050f040219140408030705150c19050a03060e0f0405060a0c0f0c02040e01021309060b030c0a080421020102130e06030a1b 68
    0x2515034074040161498054550782070366020b41030207a06400e000c0c0d516940440c6101701103490342c00e540b50072005072a04c84c7c1c01001f00040c00001c050f030400080742c2003103001e0003482039400803100c40c5001c1c0d00f0344081006030701c1040410041c5416002c45d85807014003034500b0342091184400c6650405480b045020702e19008043d050b262036001c610200280b04040442c0c5801c10890903030303103240c10305003d01d17214190155801d40302001000500741070202e101e40d000c0400340842d0108801a03051501c1c3c2d07144000025607003540c080c00740c100030403000300b0340348551502014a51a5412803d0300c80200380c03002c00642c48140d80080d160480c26060540a01c01018035a03a0315800c41642c03030400d4082c0d4101c80651300301c20700c002003c0090091000c56401a2040c0b032080e4a02890103a40d24900303c00441100041040d00c00c05104145042c140c06401030150f4844092030314818955400e154080b0b001c040d038803950182c004080000100b500310550490301c9001c042c4503a01c2507074501450100000d403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87251466 1250 87250216 87250237
    0x303041e02011112180f010f0503090c180708130b0604020c031903151502100b1201060305030915091f0507050d120f0c0906260c0309010b030f0309060a030908 70
    0xa42c0c017042c00825410303001c0d1120700b0349004010104600c00a441c451850712400203100000c40020500e182c10400040308107009844035080c20b000400c00381c10b03410180c2d4070b2404150001d0000305580303007a00160034030030b8001d012201d86849203810701c00294440c20340518103020820910007545034052000c130303006040d5540010303250001300d5101d1544000340c000c43c0d6240c40d110500028503900040c2c921154400402c0015514004c3d00094401c2c03021000c15181942481300000a018001c00078280b0b804054403401071a204841c4195440c0c4a0344407178540c48013801c40e280301d003010600d416641d448075030b043c03480c070f80150354a809190207142c1540c200041d440c0000d10100052a0049007030500304210140941c419521010300f0f43e11950003030381d04010040e085214000101c006174464501c009039140101d04080c043d0580a900803212524558244013143c0f40c0350400240c82400c10400700095400c020b11401040620323070007200407004268039400084003107882000141401900d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87252716 1250 87251466 87251503
    0x301080a0501061a12061f0210111219020708130602010f06031a31021203040609060c0206090a06020a0b1f03080304150608070303110303041e020111 66
    0x20a0724125007580d00e02d030010519803007418a00d0054207403500c251807804d00d092082d00d00d40c1c1d80301e10110340110090011240950800e41c0e21044880d0040341c846001302e03a182c006e0000d0304542108900c60b114042ca9240b40c3c940000010302c0c00808030154008814458a015107840c402e03855010352034002001c80c11440103100001c014242c2c0900c10040e200b51643c100380161441c607201c2d000809102509444010300380030019070804d01c1505840703803100e0003100400b030031000e620707800d1595044500d00724052982c0342450f1203021000010307181100c040e641c507420300178105031040761800007540c000c076004101480b2010456070f641448c103000d82802d600901c4410130908004840100c007820b42d00e2442400c1c00448080400c0008090581c0d400081c119500c0d103070307480c000d80c55064200c40950400d140c08404990b029001c100d6000b144c1c060b50b05c4101d25020703801603d8403440191802130400219855424890740310f0f4162204035401410900d2032001148106410581004c0b040406501d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87253966 1250 87252716 87252733
    0xc080d06090903081f0b27040c0903051204080717030405030109110405160509040b0a0807150906050a020304060f11010c03020c0f011a011808160905060409020307031b0308030108 79
    0x49440071540b44a100ca500565483e2616001d800c4911900c4201d501c07044180c40c0c51001d400c54aa0441d038021f8014200704814001c0c41e030014503000c81408121070a00601d0f4011080d0b05142c810b46041e170b0f81c032070003410300c1da8945001c4840001c03403c206181140006e000c00141035500b071260050a90044050043e9005a2000c0100b02d030402049418030504034416003600d59400420b0380d142402c141c400281c90030300c603400558500002d5010080c544201074012604182c01c80d80002001350755260b1130041511004159183d0003440b0303500c0010b0748240400c000c400d10032095030110044a05100000c5941d0511035400d5500e0008041c001c2500000c2c05902403508000c0000c01030070910081000c01c03080c02c030400c0091a40300007981042a2800314125114004103030714000c2c00c200d011141c10301c41c8140601d02e0604607224500c003440c03030807000a01e0360400380510310300664000c0190009604603510041c040c1c24411808406100001d0080700041e828002540a00803100040c48200d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87255216 1250 87253966 87253981
    0x1a010e1306080d080109020a08150d020306040807020108060d031b02040906020d0903140711040f150303020a0201080f041119170a06050c13180209060d0b0a06020601060c080d0609090308 82
    0x30801a1b03c03450000c2e204000e041000c551049890b6000242c0d003140c0b0610f4083e038400680601000c4030083d501d40550b8042c00204148000280041c40c404e885e14403065070b8500030800340b0044030001402140114000c2e000040c0d9154440c0f459500c0140002011401501e0b24400c9821001c1c0d20b04060b691280300005154224030301c500d41c1000701ca0524a0300d0f20a80d914238107011003602e403c0c09903031a241010b180090540004400e0000601085480750b0759060082d59030707840c030109034040350b01940880c00100120302220f00c5181c1001c80803144d1840e120502061000d151302e0702d180e6510042010072001001c4207800e0618610000404034001780d802c211084a41c090820a8800008c014100d040c50101d28180e04591598441040020141e80014003a2049180e0243d02c1180002c98158415060b4030040c860382d0280c59411074640c032500d003665610000e008040102e041203040d07000040000b801030880c59031244010424907642c4c1818030584910342012000325032094104600c0f03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87256466 1250 87255216 87255227
    0x110a06111b010e100501080705060c0f03030c120c0406050403030804050c1f020105011e360905010507030507050d0b0a05060a0c03110604020a09051f0308030108010f1a010e1306080d 80
    0x110360401d002c01041d4074060a480c8e41e000f09100d80350150001064158441d031003400200400d150400a40344e13245000c00d55030a072507104070b082442001040b00450900348024054805a4030a6182d4070728081c15500e06541c10100100220741501c9a10f0010f81c068440b460b214031166048110441c0c4840c02d800b01a00355101608a4050380301603001e1b113001010f030110344030202c8507168460000301105000070f483c4072800301048510194001a000081c400550211070000c0c0501d00800180e11521801c41c01c0d1002501d1442c0090001c1c443c5c0c0382502441d6200800702c48008000c400d90f0b42e174920214807250056824440440c0103010400d0915402a42c0781004c0c0a500e00940001d00d480d5002960000042c05820885551800040c10307940d14002d07041c01c0c0c0100450205480f030707503e262508140e4403d000301007032075007441008040c11544d40a80000e1150b0103964448074210400111256284170201c59846043c410076203010b06030030302c505400303440006d01400f10303c00f410001602 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87257716 1250 87256466 87256483
    0x3030105030f011b08070c0503040e0414030703080406050619080303070e0111030a0f050f1303030906050406080c0705011806090b060604050607030f02030c0706050304060b01110a06111b010e 84
    0x280d0400190b103a1440801d6420b104135000307810704c40b01c030341c42d0b510f03080350078604010000349944000103011426204e0824414413070380c80f642d00c48001c6100104213940364050641c009003ca0001804100003c04a82160b54080d0014242a403000c041c56206c001040559202e0003140d0000810301501c183c1c402580b0788030300e0080c00d00d000a4850b44503103039900d2291000d0441000041c03000808607510950403644070300301c4401031179101c5c600302c1803e40806200c0d1100300d000c50441000001d000340980c091310111642520b420b0b8503a5114080e2003001e070b1201d8022181550b03500710503a0b82046004a06504a0240390700059881e01440e081903902400307020707240320796018072040241b07940c1c44040300c81a03a03040c1380190020815139402d902d140100e000c003c0160041d51004508142c0c170038080c610480c0106001d0204444410054681d200210440a065040b00000b0004124250018041170080d100c0351840c000e812180c1021030b03c50801c0e40450b036510b034503c120006c0c2c000c00c900c95 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87258966 1250 87257716 87257743
    0x303090c08071a0f0702041a01030509010626102a0504050f04090c030b0a24051f020a080d0b01020606030f06150a03021503010806071d01080a18050303010503 70
    0x1402a0400c00110301801104802c10b0840e14001383c110b41042a036010380d4107142d4060000e01c00b0550190042c03803843d4841e240540080e10f0400003400d050414001c0900301c5000c4800c0c481c0410010344618080301100b84043d00340c0c0719280c60b00746015420304c00c0c880e1445c249948c0900c1a8007681407428995a10020700301040740600051180e66206a103650800710701f1600011041c1451426036102d039203507440900a03555040400c00200c030540c112807018400811f84113410511106551008a2030b07010f42500f18281000c00d0706120424800d00719903262900445079070b017036540d640a00681c0201ca13006070396502c0f003d1985040d6010800c142d00254200d018102000140a5043c0d550f080144102c801d5113101840078647c0c0c40d07114025000d550003a003056540300d001040128103030700030300c2809128418074000541292141c20404d9015010540c7d00000c1c0011100441c0c2803100130382200d6480d5036501c00168401c010309204c84c201407107240034589a40c903010405061210668408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87260216 1250 87258966 87258973
    0x313150f030204030209180c030a0302010c0210050c07230109050d0e0303090112110705060405060906070507030203040b0a030b032406060903070509310b06060a0f0309050102090d0303090c08 84
    0x140016501e04502617803161200c0000d100601487d90003902d022811000b0039014000d500d030741d400303050b0306404c90005610140c08880800300c0403001d85045810486182ca201d00003400207400241120b14400200f803641201c0c40503a140d103641003821100702c184d040303403d03502c01000051015000580302030007503800c030017850506200740006064403003110f180804c1d19a40744c406003a60382400d801c0e5840a0703001400c8800750b15091074000d170345240c2602c0c2c08200d885180005403080748101d045030750450b8998007450500740b8084030700d4143d8001d03901c030b01c0074580c68000d0b20010740c46c10046540080d480245032410100c00001611245a010f40a580282e00400180743c1c103442c001420740c100c8509131450900b560300c500320007070114880105410041000000c0d071404201400e40d180d0060302803d80c01c541602e52100301b03e01482415030307200100c0c9046c0d02c941c1c0b0950003a4070400c40c1c075001300000b42c6048181d800042030303842418401c0780443d9843c1070b80300a0140e240309100240036010003e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87261466 1250 87260216 87260219
    0xb0c030702030702040b24040f12030f0503090a0209040b0a0606050f07110a03020607240b09060d03020f0105010b0406080603030a05031f050d06020904050a0c0f050a020313150f030204 81
    0xa450f44580d0314060300894640700f0b8200d9648a00c0300609101050940e5030004030a0741002905c036610a05c5410034044941c200815640300145c0300380d81c42e540c90f840750748007100141c0094489800040c0f001c01240600090340c8056107070000709500c114480e070240700c0c6e549484c55106007100c106421034020004244150040e003407800c800c4940c1160003e0509083c0d030b46d0030001459151060b040250040d138041078401c10000f0f41c1d0683c03241c2d02d42b511420000030326190310103012580358410315584010010301181080c02e00d041051034443c0240306552a0951020241e03081da0310070703444080342400004007000a250f0000e0b81c0e0350440780440180d0b140c0b00d05908028024000640410a80c042101442c000710f00c1030341e809c0004150151500e0050740740750500074005c2d0021011607000f1800c0c68005215401c2c81d1103454640003160b100c900da000c01c9002c0407a016040b0a0040e4294032081000c0c010308041b0042ca24004c1c50b803054010030402c01d805009000d51280e100030300606005010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87262716 1250 87261466 87261481
    0x80f0601020c0111030c0304060e1212030f0411030a030509011b0b070806060d06060201050402090f1e06180103060501080f0f0607050904110c0a110f031002030603010204150c0b0c03 80
    0x844880d541000d03e02503020703039604c612440c114403a20703815034500c0c44009000100c0e103803c0220140c007088103c0d800011030441c00c041307a8564582030748c442c006a904000041d20304403004481500103000d0705040380340e020440c0109141061740501a801b054010495141d01c0d0303404520200c46d210b101141180e41c60540e130b07401d80c031508042c01000c01d01c411040060b4040d103c02058411210321800f06102065880f4400790080c4020707036040e0300602460000524a02e400e100c018000c10a801c1c04550030002c0d41c0d2481e09601c0040e080310ba01007440c9140c0c80c1c4c0c090150301403e0280d80a80c034005078035407510400f545086a4098a690310b41c20002c0b203000800360120310b00fa4880d5031341c1046569086c4030400140100301400e0340c1c0031514000b0071145c1c401c4100051003107405105140b20380150b902c2000300300c51a9490801c0a505501c028412451030b282c54000c0e5400180281c00981040c0d2603105000000107040c0054000412001c0c1c400140000b820307145400c5a488640785241d800c143c0c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87263966 1250 87262716 87262723
    0xc0f0302130903030e030d020a020c10051801210213090b0a090b0303070f080a030501050406050a06140c1f110a140702010c05060a0204060207090203161218030f080f060102 76
    0x8441007030320360b03030003049061500940110402d060800c0036a81d40d4845520030000075040342d9902d0f00140f090b164204154180110704000342c4144d0348603035007030942c01c0005081c104410340c0302d00c0c100001001e00314245203a5625a04400384960009600c030810000894209402e81e400541240d0500300700741c49070b440c1c454400c2c1c01d58040b114046000c00d54500820b00c1c1d4410040024140c0390002d80030700c00e00840c00302900f0b40c0300007030f5420306c002d90340c45003000b081d20301c98045c40c2e502004c000c20030480f40e400340300c03801e199501d00d41006007041070f800c00d941d080c20b100e0030440200e6848800340c0301c03424120380306200a901d8880e00302c0b801d110304610000d101c48810300c8040c003020000580d24083d03a0140c1c04102c5515409400c0306d0403442c0c0710030390b00d008e900684100d101501c01c100000c660a6a035000703480c42200104182c460410950300202c070f90100fa5040c41094950743e00161100c460300e00d07110811a802902c0e680d902c840241402880e0340d40041402e03011041420070701ca0307a83c1c4d010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87265216 1250 87263966 87263989
    0xd05030f04050a0b0403050409150602120d0605060a0e0a1a030103030c060f0e0d0f0306081002070c031401150905060924030601170106170303240613030c0f0302 71
    0x141004040c0e592207182051409254880c0501802149020401010750000041054401064003404201542c034411240c0c46054010350002d6000280c0d985000710042d0060099040d001e8008540507030703200301049181c0e100701c2444c030000e0740b490028801418580054170050400c00104c5241303a00806049410b4001804003c040001c20408141441120b0304461038000c501d103130400001c0c1190200b01e55400241c500200420321f194201f8100714060b108104c12244044e024008610380c80005000a61207042c045038800031000021020800051590726089043d20000036040c026420180e8a001c81c0e501949402d0700308002c02030162641628039030008141c1c00341c0c080b00841d0000c9a00103101940d11a5018130981c0c000140b50b1821030607100c4089060002003041c0d945828080b070f4071850a1400648a910400200303080040d240c840010505800c0c220001004c0c180001034110362080d81e007400c07481101d01d001d00c2030005000d050001840b07041e039210300080c590ba0210f200a10030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87266466 1250 87265216 87265231
    0x409090305040506030906040c050d020d02040c021c090e010906060c02100909020a09050f01020712290f1b0c0703020f0d0204020307110607031812030e030a021e0d0503 74
    0x11616044205801a415900901801132095480b40342c4509055640c1e00101c4064402c0f40411000003194180558440803994000e40702c0356045a268091001605800450904510545459100120401100000c441c1e00da54940807921310f03001044124070030680000707806d180740080402005070440c002d00511503040e1090b10101040000c00e40341000680d100400706400000d0721840d8960207035018040d85c5080f91440f1000c0c0408004907030b182c000f400307600c00c403441c040c41c02000b083c40c1c891032991020360002014501c01002c01d80148204069412640c080d03607100074012031090008003510107000c848071072070070036101ea15240d96030052440040e00414042601c0303681c0c0e0b22000020100745070050810f5540b802d021000030302c101a100c0d40601c09015540104014038417038003a061000d0030342441e246026045480318201804e80711082c805040d03848040405160342403016200322109500507100307803106041010a084c25040c618820f0b500001c1c000319a00340c02c54140d0790070668 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87267716 1250 87266466 87266471
    0x62d032d0a0c0e041803091205030f071103010212070e041a130204090504050d08010e04121202090301060605040f0608010b18370503010507080a0b18040804090606050c030409 77
    0x1030100306544098045070320310b0300b00d81005203d8003084034a140c903a90146c826035035030994554130038040e241901c111074020202d40081007002541c69400010707110710760041c600d000c5444002d00000f82281e01456130a100b01c03d001d41044403054004d5101488000103440610001088647e451405c401d0070055a1190500004040b080c90050381910003418002c88100560305007401d10b00e503904800c881d00400202030100110714140580c0820b809540e100c60060128104c1190649503109a95081c0c05541c0e0309016620b2250f03801d01811006107240d884107a034490170102c2880c103c90f5a50800f406001d2a440104030700340c1a00c049442e411780c1351f41c00301c05006042e0005403070466020a150101c0103154424902d4614006040f03d6625140d000b003112030ba5508240f50994001301c1360903000c14038a00c0012110503054001942d503080c0201b14003071070764016071704490030a4150340aa8505d6008107046c0041c071717043d229a002a103160f0030b1890030302601e00380707650790381c403e81c05a03031141c94 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87268966 1250 87267716 87267731
    0x13061503110918090f011104240516021201020a0c0605070905090606090109030507081f0501030b04030e030c0a09050402030106060e030613081303080702010215070e062d032d0a 78
    0xd0007440303080c402542c2c1500138450b16201c880c3d00303403980d0414011208900d01d00c411005075219020710f00035009c000ca480b1941801c0c5d0700240c54111480045099810801d0214143c1c81c4520038030003480000314941318010401080d003020811680001c20f039600f400300200003032125a84070311035940e000780c04488140e0b4a04a4000489002e013484d80001d0280c85000808513900e0743c007203030000d07000358100c100b20841c0f80913001040540e602880041c0071104000c0108012a12030101d000040d54007030221064428481c000c43e00500880d0f022290003560b5038203010844c0b80c2070082e20f005160301d01c1c0041c90703041584006916040f01505142c500d0701c0d214605810041c641042c5c442060110780c003160300541d41d0401c2c0100f540040401c0b8018060010100c0c1c1c2d142240417117038040c280d156a07940c0d1010005040c00002d9000041d049203200110314607006902411183d6031400320b403640c420303480f82012981c141100030b843c98860748006180c46452080e004515290741e00c041c0b45070307000c40d820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87270216 1250 87268966 87268981
    0x151e0e070e060310020a08040308060d11130605060d09170304170c0f060112050f0d0f050a030216030c0209070201050f0f070c02090103060e0f191113061503110918 72
    0x1540502081a400451a1107820787c01c1301c8a244a54066111015950355400400450303100c84500146907658440cc0c18410341088001c206582d84020000034059440d0000120795800031110500303410b4941407454100304d100040a0b07560443c0300061419410550748154504940080d054680c840208418018080400580310406804810b0398102d5031280040103160054103400c0c0c0d09031261929142d03070308900142842c01c0d1052980d480340001d6550000320780c0c581c0121003220805400b449041042580f00203001e4030780c0d200b51600c08405035148140610340e00010117160542e40350404100040409010301680088043d0004400b55141001600c0c00c15044401035004044007001108001c8954428050010200100c81101c7e1044103031540c4c0343c0f1140303056000020200c03602d10005102c00d0703800000d007100800710301c084044100601c044441503842442000c04400b40701020716010704c20101315451441c06a840d0814190100301d10440151840640c04821030008810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87271466 1250 87270216 87270223
    0x6110d030c0c0c08070501030e031206010806060d06090507030b0102070e01030828080f0604180b100b030a0209090703050618180a110f0613031e151e0e070e0603 71
    0x502e507201c055000c1864603110510354405880c0944e0b4041303883c01c0352440c240d680010a903021107c01c29407081280e901c2000441c3d1000c0e0245c481a00300809006035403401c004c03401001d015224a8000103040d142010703000f815104490310302815504030400a10450841c1c180b4981902d0b007240085941d620908403134000c030341d000325041c00180c2160119409165200000c0c2d402545041140c201648a800c00c03c8106c0b4009840507802e00e00510407000014181191580c0c461412000c5010346039a0303104d035a4003030b03004440c0b00d11540d030f0020340e584075031400303000c00d81c7c100003145410001840c010000c5070b0046150701d40c200790650444002808002c403900c83c1703010862214240d50031503600e4681003101108542c0018824507089041c0d0855042030f900b514003101c0220640c80c510352440e00d03240310f0f00b443c0380c02282c010030400c0c9002000c2078000d2020030b10740000d905c1c00a11a80813214541c285e5080741d0205505a08007a0031059010b40010769100359244042c00c0019130711010f001034035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87272716 1250 87271466 87271487
    0x804090203131716150222080d0306140d0501060519050a0909020102032a0a0b090114090318040f0608011d0604031b03051209010209040606110d030c 66
    0x404a0000003007104281040703003060001840b4503581e0411500c5408034608034010014602600c1c00c03107203441408070703198410105002000399801403400d60311001e00900d21000c5580340c1c54110b05541f081211241c1000b030945185410700c2e08000f80c0781400300c108000000ea10380b05211700501e03448241406420340c0485c004040c01410a107002e52800d110790314400c443e1103154490301000c0e00014010144e0b020b08951154140d01862a240d919900e90b0000c080f00300d8915050300e40c20b0500d074100c4004010500d6600d020790901e4400c2c0c0391901110b030a65000b00c002413466a0a0000d22120b05000000d91308644140c01c100b495017018540400e00900112a1000e10182003130070020302c01034194000c501c000060200300452220380e00c545503441340b090701c0c000c000400c0d5400d941c00207001300307905200320380c4245085403030b200801040c0c4614ac6810b485101075650300181c1c19034549401d200c0c24000b050f135403e004448810f508201364650301c140305006c1c00d0540711074202c003c141c130030607001c2c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87273966 1250 87272716 87272729
    0x804080c01021b06070e01020a0b1f0902071a07030e10021e1908060d030e06030c091801080f0a0209040b060301020412030203070201090b0f3403020a020f0d03090b070804 75
    0x20000c2c2483d0407542e80c41d9019129000420b00c40520074000e0f510100d42e02d08100e80000400c081a20303840c0d00010000782200c000d02072000225408100695a40001d0007170398000c040e40790f45101ca40038000c01e421006801c403400e00d45068840e00c1e00c030102090b94507002c4600c2e6001610380309032101030002d900c098080080c0540b00011440c2c410302c980250301c2110306450741c44011540d11703c01400210f04040d80098081007240c4900106480c0031002594010204141c250a102d900382c0070602d01d035054070342500e48041030703c018081410100803600ca4070241500601626000390080780081c1405840501400e00380b01c006212920250100d600030b0610b845034044040107410020344a4120100c01c0b030000c1c08007400000c1c90000d072003e840c0341c01d50040e40f01e8500300040d00c95420880702212614803010484104400211081d03400000300c078000d8014082c100301901c1000445103140e0083c40c0700d800c00e5180c1034080b13544080d9103001c1d150040201c2d580e800f442e050000c001d0041c2d5001d013 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87275216 1250 87273966 87273997
    0x3080f0c0c0d02061801062105010b040911030c03060618040218010b04090501060e0604150c081303030305010806070e3309011206031101120902060d020a1e0804080c0102 75
    0x102440e40040d61390f11514445030118490088171810a099503084c0c810ba1201952401850801d000c103001141d01c0644510000505503000c1d030045401e49814000607100c480d040d908007480d9041c240700d03583c3c480384120046e007410300d041c0000429070340c10390b602d441410718030038009000c43d05c1d005841120702c003c0c00c218581540e5221111042c59006010724280c1d2420400001501801b0754a89146090000c8c21142424109600103128580001042c02008010440b905c0030076903a000902c500c0349410306078061181103050207000d8400681c01100c4642c800c000700b00a0550200d04419000340c03c984a13845649000010b803000c008009050040c40355400b4401c007400c0201c0c00600741100700b80c940207810340a040114003183e543d0300c40544200d0812041d510190b1007040340000b00a10b50a0020f0a1025a0003107040c91704081540c5180c10f50000d20400240d8004040f552041411460265481a50b801c010400303200580000c110040c01708400d8000d0320207406840320f800725028003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87276466 1250 87275216 87275233
    0x2090d05100e0d020712020d05010b0a030309170309060f0309070e07020601060e09071d010201020d020408011a0d0f0f1703070807080a060b040b07020f03060a09031b03080f0c0c 78
    0x240c0c070060414542145030340c070841d07850440a60012903804112201c001d2080740702141902400b2580f101c021084805558512100c41d45681b03040b042d00103580a5aa40c6915905001050010088099184060354010f21044100d95600070803981e8030300303600d4a415141e446006105285c10303919080000d506429134100271619a00040c914100e4009541d2031040071002401d118541d0001e8078000000b9616400c0d0158107000039043d03185075081071000625060072a46c0e00c0c000c980082c1c01102d42c0d070b5103c00e02e00c88050b0380306061454030b5100300d80140501075665076014241001e00301c02418440906204004d103d401541503603003600c2d400e8800e6880c60101030080c801d1104840200c04210584041059180340d845903d055921080105107002d041c40380054164010607400c9910840070200b440454805000d818054100384201007034154103807074043c0010205448518030740c02c1549200d000302e50b002940c6504811015403888041d19216040b4147c0e01c601c007503850303162084130308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87277716 1250 87276466 87276493
    0xa080304060c05010c03050105030307061a0604090f0b0301050903191209080304031409030c1905030a2609010c0b040609051608010513120f120c0804050d02160902090d05 75
    0x36a10100d8482d4000b00f02000b4410740c140c041f1007082c001c2c035406d64418400b100008400b64409120310f20041c05a80581c0009800910700d50710603001490b4464645052040b201d0740c2e40104000780a04030000d04c01e600d054904241c1c0ca001d20080b01445107143d41d50a1a094019254590702190b034440501004185042142c0268410340c7d0072400100c1c149000c40c1c07407a001c0006e0740c41d0458001c026003580b12141080240c1c0040e10380e01d1004000310070310002000e6804001850300309106a507942510040900c035000007400c800c001504828040108061980c0d00c06070454020794041c4142200382c5550130706070002c10551500600520805c4586050710a601e111002101c00d80030081c0500e81d1a1b5a1074400d903c51404010400420b0030b0190308450300902d0020507201d941e1030000d506c8007083c0b0804003039907210001000442c20f004180010f00c08203024060319414140000e150f003511010750742c1a04100703403140c40569540452a090301d0b0352484080515030790081c0846060b050b2242 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87278966 1250 87277716 87277727
    0x150512180109030e09060108040809130e030711010f02060408340809130209060307110a15140109050405071403070b030109050f2d06060403020d030c060c020f0a110a08030406 77
    0x13a0b82501c0780301c4a200142103503115400310b61107650f008203000d0034556264140400035000e58410070382181c0700c000080c01c00c68204054420326000340b00000d00080084009440450701038590401c5400c03c1c002c100109034800c04503488800c0350040103000d00a5883d00440001c1000042001502c80d14000818032903490041c0028200c12100c1001d2000c1040044d0100e200b210038a0350007e8050001668241c0103c441c43c1e842404070068a08141003665100400f50048415001041d41c0702c094030b41101c1c48241c60303405000c0a6504121a05143d15440d6841000b44a010381204a0820f501403603101400322000500c10454031030b40785d5840342800c41c0942022a0071600c00a2020001030080e10a040215900741401d0241e482c140107105820486c2c0c0720042141f60003600c00c12000005031209982e4204040c0283e40e41c03010b030b860500d0700c402691944507181c0b085500101d4a0140700c50045804541694020890303c040c1f1000c0d030104400d1f0f0707495408584030b8000030400040707884c1c008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87280216 1250 87278966 87278987
    0x403030605041503060b0a030b0901060306050a05040b06120309060403031d0f13020a0314040302151812091201020309060a1803050f030907030c0603020c0715051218010903 76
    0x2a14248001511101480110740c05a0124140c0080422040000c2020b96001c09039018001d4a14610147c070b1352582e00706904242e4004016a40d904803c0051000d607208441e009950b114040c01541015111301500d0398003e02094461400c0203c0001104410400ca6002c400c0c054111a251540c0c1d090241280c0007015403c1d110641c01010000c540c50160b055800c81c4500511120f49100d0b580e5108009422004030a0145540c03000007600e0480303e4140703944610310942c0100540c0c50150f00c09681564050300d10510b2100c0c1e0050000318160200e28084103045d40364038681c071411428000703000078a24080c0d0491a501c00014006684004182d651044015100c1482440d071415401900b54400e6131010700042e9080c00102c0c0040310300002190000c0c0740d002202c007802e881352038032000c1c10704682c4140c010960020741e10403094000d202c030300c00405400d030740c550714090100c0c0d001d86244200703226212007101d0000080c501410f206c2c0713540180f81c600002000704040d20f1802a040c030940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 87281466 1250 87280216 87280223
    0xe0a030b090703050633030604080c010608120a1701080303070e0103110c0f0f060702070b03090109200a09060302060703050a0908060106180b03070e060d020702060d0506040b06030708070503250804 87
    0x41e901b100a030201c6c0348402503800c02c043d000308607640c0c83d61035103241c0b81c01540344002107540340c14000908800c00c0210858102400b0b100c155100703855040a080602e0080340101070150b00b200411544501005a90b0f02042030f01749178007588a017000480050440c11032581e0541b00100e844091a600001d92030168003503141194500c02024800c599a0b190449249005900082091007448214000395402601f00c0c4000b003101003a9070b03110303c04a0401000caa00b0243c1e20b000c1c3d41001d20340140341c000146400d0004100040c02c0d60081241481080400741c00c0c03003400564401e129208850080003843c02c103040c1e40c05940c40d600003c05c1e03000c1d90035940026941c40d84010448000071000c480c0500119215400e000021310140f042c26080b81c8200d0000581c2440740102507160f80c0b00401205d81d100c400003685190840800c012284210304540c024041401080b524540024550380c0103c142c0c00c02c43e8481d60b580380500019075411400c40b1203101144404850940c101d407007540a40e20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 87282716 1250 87281466 87281521
    0x904090206071b06020a050624040507020606010f030b090130050109020414061c03030608030a080108070f06050307050705010603080f0702090115090b1e03010b0408010605010e0a030b0907030506 86
    0x29101d40c202d80d100c24a10000c1c0c85600b250022618032081c90540814442c8108503201500740160001000c2f50070131030f102005a0801303403c0290a40e803054001039404c8003410104042c0c0c100501107503600c1c1c0140036403104010451100b50b0401d4150000010b140c410031403511001000e442c1c41070117001c3c00d65007280901d041a601c1090b0307098034003455118900180c04407060b8036118050480b05602c40401360103040d0303282004076040300148010100c05049407625145540350460251805a40b64403500400f41d42c03003420312900ba403200c03c50b80c00001614140780c864045003800f0b401043c04c3c1e03000405041c0002003c41c812031001024080c840e00840f407a0403107a90320b48040503907084e540040780c00103414060034020004400050704285017048846407100700100f0100d12107034401e1300300791480f10b03002c94108a41a82401024080c00080c80c04d009525111004508000c041d030200500f40c004003400030300500f02c100660310045401404807855424000e910402c11490700d000b50110b40c0d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 87283966 1250 87282716 87282719
    0x60a05040e0a09080702010309062a0801090c05120c090916080a06030b060111010204170a020306010b0406020709020a030905060a02090a0503070e0a0207050a1502180103200904090206071b 83
    0x5040c3c4100c2000da50000c680310716208180d0300450003460b040200300c4001c0c0d9114080d070303d00c507501203100350600b11001100101422140300075007000d01c1680304c0e89002e410502c5981000364860195841480e2400c1100340580b0340110803003042c000c00c25010f400070303010010040d00d0760100842092050280e2900c85083e1190390640090b100745000280c0a10300d00b40201e8503e500c503000c100c10344903450000604007a115851121108070981c00d0860756440a400002503150601800c2d004003440206280b80926040000e0f4a4000510600c0f0145a001c181000b0041c081d07041055800e9000098405515000940e10025040170070602d0107a042c031100450390741030020302e250683c0c500c1801c0d5161680c030114444007a501205044503507004100d0000002103c0e065070306018500790101513166015449000011410300003c81d0406007000a40450040b0803480a01c00b44884115280d5501640b004a0003610300e00c02c000707402c054009a045c00344481401d000c2c0600303000c100700c0a00503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 87285216 1250 87283966 87283981
    0x12030c130b16120c05010e010203090c090f040201050d0608010e01060305010c090f09021e04030b060f0114190e0a060306050301051f12020406090c0309062d0506030c060a05040e 78
    0x501401001030101c2c62050290310200d8060b441e081007209162a20740c030480d10a03540d442c00d4868110120711039070b4000c8144040d00300700307100b0f4042e80320094901072143e29142c2c44001c2c08040140c0060b040c000000380217011902540c000c900034100020090001003401c542c22402440c40e41f200303035142d5103031000c0e04c0f82c8284601844400c4070b0844504c00d42c2e55052505400c020b500031209020310101001c15030030002500406007006600420b500300e0340b49040c90900c050385c40e00040c2c10b4104104094625000300c007610035035501517141074400c189a410154250703003000180c01e5055022401030f100080440d80f507006002a00c10503070081c03101c1c3d201c0c40003103040c06e804001100c1c0e40b02d609500501c01d040880c80070546e03060000f80081280c5030303184080d8040f203401100b820b0003c0d0b222224001030100c103009804900c1405c54003141010051401c40c00c4080d02070301d1400000e52038030f01150076030b9000c0051800002c002410161343d180b6501028020394050320440310000ba032840080c011303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 87286466 1250 87285216 87285239
    0x906010306060203040e090f0703051509060c040b090d0203070b0d0f14040213060915030203150708130c08030a081009020a020d030c200c041109030c011112030c13 72
    0x403504503400a6003171a0801c1c1141c40075010060081001303108596000008070f508111401c000c0d401400034011344a000c1500d401c08038001842407456a0083c401d00400070b1110701203a085a403110f14142d00d82c5119400240c07403406a1030065458880e0100124400758448003c0901189140d0200032004407003e00c00256501890181c501c40c01c1c6500240160070320701003a00c4075000542000844e0342d2100f5889080742e001c010b5401e04c91254800500450504104041d1440841c03104281c1d60314001000400c2e121000f8550045050154500030170450f801e0207070000740c40b200d000d030303500d401d2801d1000b000b20300111a2036a190000540001c1d8a448910807130b00f10346855409042e20b94812a0306070060100e00514400304644040c00c400144846e01c040b41c204402200a080103aa4580800007030302d00c05070500c40b81220030001c00324642c1d0000341d4a1036400c0c0a09042d901d488110752000c2c2409403048202d40320b04070001c1005070804440006100220300301c451076900075280c240c20f685 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 87287716 1250 87286466 87286469
    0x307030c110a02060a1101020a030204093b0a06020c0a030207060f05030604021305040903020a020102011a0105271305060910060c03030527030414090c040e041a01030b060906010306 80
    0xc8a4229078001d03005404e200d0014030b101540c600300014006408a0041d08aa000541c0c020020742d010a040c0080303c0a40070f801c8003011740c0c0c19200002c88810700150740c202d6a1901d880848201000c1400d00b8140c2441403241b2282c11803070864803114440121a1a184040401c40060207a0b01b0007040c128003804103d03000c5c0d00340e580c501d401c66aa4401303000095105032500b8040c000710b580006503c5d5918015400180e11030340c050000980c0600c00a030a5408014404403181e9800782010400d90f80036040d600105401d00c00c00d4480e801c844140351000100725a541d82000780704c00c0e030003d81075080d04600d000b2442500c4e843c440741d542150514000109024440c00102d4a1041034007080c402c0d041182c10000d009444882101e4002d050b484c101241d4050b0300a0b07030404034007003155201328455542c0700301c0256080401890f141d101c41c2030901c518003441e01c3e80b000c0e107804501400455035003041c8100c0c00c001c8070380c40c81d61203040040860004842d940c0c0716088010021740554403c3c0607600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 87288966 1250 87287716 87287747
    0x14100504060806040602070c03020405090307060f0b1311190c051603081204060617010c080903091522030b090d0f0f14070f080a110304060c151d030307030c 69
    0x10f20348503941c07100080d5015907410780e442d6141d60800b00c0580d84a00c80c4502030320205008660b070302058942300e801c1c1d8005092862a440c0f50244228487e1079007038003810b098181c003078005900c000c801101d019501410003103d20344068001084451900301105102d907502890460b0b80d0b0380d21a5025551656550100503d02501408a90310032002e00703d8164000c1d11440020130a2900c0702032440024051003401c02d030382ea464640c0b00e06003030f4016914507041003c1c1e030040d600d000031000110f0240c06c0101e80c11074950b00c0004007459450116142c0c18540c0001d1021400c8495603801c211030100016501e40109005410300c00e04020300810b15521010000d460b11601865614401d44100705614543c0d00420010800b01d000100500704400845205000450b12400c0d80f1600500325040500840d45980c01004140500c940041d0b001d412a50701a500c0030014410b08811400382501111110340c100050340c420200d0721000c8090b40c4140b920f81d6040214550607141191030609404001c2d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 87290216 1250 87288966 87288973
    0x40804090203040503070212010b0a050103090f030804030909020a05090111031201050609010e06070f0501050603071a03070509040920041413030e0603010303110c0907050a0c0213141005040608 85
    0x400000e4829006150320500500c1500d081032119004030b0301c10300d81e8080700e4500b40d5640120f04840c2c6421180400900000e1804118680312175903000e040e10381000003e0280600503000800305807144010078060b0410311425504d400f003900c8003030142e4100d001c409010500300803200d9582280081030310003000c0d600a951500e40d01e010240280c0f0717403100c24500c0c1001400311208086450b40c0008200729071140303410340c0a0704400d05020b821588007424140c401d4200b84420400004001c0c8140d40c3c086401c03030407695a4841510981b510301c2800c012541103420042481c1c144114014802203600200c400325605000140c00c1000f150304103802c160f00d00d806800071940300710083d0901d030b5540b8882c1c1003883c04940c0d050f000926940090380100d00040c045090303038400d0320061220f551581d00a5a09140500b40b001014182e401060720709401c0004034103030f0741d0940d582c170150121043c41c041d000700460248e6040c482d20380b00084a07031500082d40f1200c005043d0605119030300465242c10080c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 87291466 1250 87290216 87290219
    0x306030c12010b0622080a1a0618070507150c0906030b0303070804030b10120f02010e03160807060206100305060730020a0e0a080601051201270201020f06040804 71
    0x4105241c1e5a018a000c0103668541c0e0f54121904c601d0024207450308000b0606000316019800c43c0c0c00d0860316045440c0542048154100003188002d0070355946c210484120f81c076507103000225488445180601c52400801014008141c0d0808010504140180e56010400190300c40200643e41c206c290700700010101103040142500c20ba009028825004040c0d03440d018568583c031b49290040d07001035904400641c00d102070304228640c10401005840050001c0c080c55807102d9000c80003002010781804034040348581165002d0052210340c101100c41891855191341e0b940d0303691586402030300b01510420000c50780e500c20950b011022280d01c81c1c010b12440c0c3e2558812038031402c4404a181c282100b502c0d41d81103c0b20415500821032503000001616840c00030ba006100c2d84003001c505020300c8081009102210740071803018150b0718180c03003c000980082c544a07005104441c50395542341c502c0d022890200d181e5107810500a4000d034211090140b101c00e5094444105440051040701d08100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 87292716 1250 87291466 87291469
    0x10030e03030703150801051509090a03140711030f06010f0e0402030717030403061406090a0203040c09021803011a0a0b0310120204060e0403080403090b0708120a200901030f020306030c 81
    0x41c0c1c40c03130054880c4400e02c06aa444441d0b081d03132000d5546007a03220010000031910306041c2c0d8216407002c5110010300c1d044074107440c0a80102d0b401c00050360003480000d000700070712010903020b4060102c0a002c98079440b17140140c0c2c03900c5880a00071081100081d84000072003c418190b0380d03002c0c03500180a05001c51410130000040d0b084407031154803d000900c40040030918601c20110078440100001c482850280100075019000500b645081413041c81804081a500d14a0406032030000500695803c0c8001442141c0e1840c0303607015505609000320012202c420898204843c03800350b50702240c154407a80c0540f418042214a6810075544990410004541d68544401d081c000381001440e80d1b112124207901c21011942900841c0d46d2600b440101070340a841c41e0024214148014200030780366031020000d04c00c42c4c2001d1119000c0307102107444d640d010f5202e0365900c0745408100380e000320405c0795000340790800351406001c00d1420250702c0805411b03008991240340010080d00c0715501000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 87293966 1250 87292716 87292721
    0x1e0a1a030c0a02071d04120c050c190f0b0903010b040b1f140a0e1306050303040b090a0b0307020a060b01180302060304060e010f09050c0f03030306010c05011808070210030e03030703 80
    0x90b990214070610f000002c03250512000c00c5000051171500b00b000e03250500300351081411940400041084005560703011800101c3c1b202200c0c0c0e4100c0311100f40b4840c011001070b06481e540c0007402101c0c5d4181c00083e0800c081001840c400d00d06030028007420701d032603042104855100040e0342d00324802c0d011513441b82c0110f01c040410305c40c03242403100c0318050003c0780700a00e400c503e00900200720107a100084516010090441001568800340710301c9003400c001c20b490340a01d00c9014000e840100b40b07124641d071124800c401800800c41207507264503000c4c0000303540e00610902522403520300300a459940d4415003e40b03018aa882210b011014655030038480305900c020400d0360259038401307512032256001e000e2440e51250198002c920080181000341c101541c0d00b407094031070b0075446101c080ba07072030100071703264072410900b00403841c0c1d00340741086405840986000022000e08090038010011244003a1210351700a80e0071502d43c041c9141d0a0b4111010000340b10080da00078000a46e00900c41d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 87295216 1250 87293966 87293977
    0x8010b01230418060315050601081501050423030102070501050103030f170408030915010303030606021501030c1505070c060201021c180210020a24050f100902070f021e0a1a030c 78
    0x4580029050769a458800d451b41e0060101200705445105010f002d680c8248080c0d042406142445502c181071000031b40103108521900108080c070083d0302803110f02c0181142780d03521015000359a10800780c900070f80280000d02048000c60b18000100c0c4000303100c1d407450b420302c801e01000302d8403949503500c510400c2e8100070105c0d00540301c1c00600000c1504d8400026000f5440f80d240410307a1b90401c1d60190400c88440c20309103d0511745401000030411811112040b944411810807903e241103d080b50703503126415015021580e04600000c03c9541507008188400030f425170703612403424103e0f441c4103454910745042c00030715a030032018026103094228000855024012101816683e69440420660444000356042c080600b501c00389000d90213034640c05107a0f0342010704240381c2030038501150b184500540000c40c0d400300d030380002c104202141000280e00140280c2c0c3c03180390450310011003440624501d000702003035078001401c401a001c0c284d90710303004c407500d10741907650741c000d2940c054010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 87296466 1250 87295216 87295259
    0x25030f2d0507180906150501030612150518060c0405040c050f0d0b06040f08060f0a05060307290d091101020c060409050a061203051209120304121808010b012304 71
    0x244d00f1907400003843c0c0c0c03003869003043d9000c02c2016a81e2410001404564a0380d12240b0800307440144200065500b411714094038041c032200280e10f89640c21032640d00604040e420000781b1490052000c03505961002d001194070844050001280c5a9401c69081c007480c00c0c0120418001d110311a50b02890750001d4801c0d460107005241406e07980c080301c1c2d12503078540d03201c01c03034941207e01401810360100000681c041c111810601c0713207003003a03008650354807005e01c00d502c04501040d0300e03002c9146902200c2c07204001c1514550b074852240c815000c1c000c00c8a0030040b0b43d0346003c5884800c9950020404905400f401811142098a00603c0b88050b010090414a1903951000301092310481c0212034101c0034020340c2d40f26103905000812441481000d8440300140d13200c0004100c2132044001200e42c041c2d40002d40f82d40120440000342c60088100c0c084191008001c1d0000c100c28805600019901100345d83d14196040482c0c40e071003041e050b1000d81d20030100e0400c001d0000d00b01460a1100750881d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 87297716 1250 87296466 87296471
    0x4140d02101d0f060901110312040b070f030509030912010b10050403200603150102010905120306010207060305010e040f14150f010e0925030f2d050718 67
    0x410350020350036401ca10340d160089030a00c140d1003020860744100441200041e189012008121800101940101804981040700460760404503007014000c0e0342c0f541d041d00c507440700d860500c0d19282d41340c240c0859030040018041c0114280c3d0510074003a05009850800207946048004000d0000d44400650354124564075a00010705c1512058022004500caa903519a00d9a0031890000e80740c9108156401d0b25141205800340c00d0b03524842104e800c5650b050351101c0e00580440103078094840b43c03d001d01140aa880c500c685980950001d501c503903001d03801d0354081511020706600310740080c0100101c102400d00002d00103103441e00500c10050040c0c40c0c050b2a0514441c2c040e2820701c43d0354806601000e014140b08070070000d450034601400b082c800a180a180070780e9410380d1076000c0c48a01e40001030000c00242120f08460007940070f5500903800040740e4446040405150960504140491928141c0d203480528080c00300745015501c03a02408403d440c4c100f04645000304504801c0d0700c1d9a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 87298966 1250 87297716 87297739
    0x180f070f020c0a0e01060e010c03020d050d06080d0309060b01020106270e0708070f050105071e06020c0f030702030c0319080d020f0a020c011205190203151206160507080414 76
    0x140c83e08664401030028200d481c000d98100f0400602c00d8091244650500a00401d1400026000f1440e202076005626259484810340041ca4000c0c0800741d000c090300d806000c040e40d0034681e060300304514090003008103001610703011004900300c176428410b60307c0e213484041c60003a9100441915400024207124045107a58045028904140c2c030359000c510303190300c070080c200b181145010840c00100803d003407480c1400c00c141c549510389965098213081900d6003419000410031294140c86100c44441d08542e030060941e255180d4980c8030300001c0e4030a20881c00c0c1d440b8107250006035058400d40b02441c0702080001c0d55900c4045420208640d03d4032034080c001100c1040d9079801810030040e4990080480030003000014000c04040380f11100610b08160402550458401003100c14040c09000140d80399134160303204060403140840740354480300b00b040705444040700180040c010070025107090089004024280c480f40304480c001030200000b404108600080102030340e01da031501800040006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 87300216 1250 87298966 87298969
    0x8010f210c1203090501092103110d0909050a0e0c010c030e090c0406121103060f06070602161203050f04020d060b030a0b1b0903100c020304030b15180f070f020c 71
    0x101d8403038002c4a100e40c0415082030a055102240a004143c00e01b4a41c0819007080d0021b200c41404a0103000f031051002500d804152040c01c480c5109110681943c0708080303501d00c020076008840c866101c9107400d10740401e288810912030724a138810110000c140460754907005560000301560241c0034000e252003001c4107911810001803060905c54074080d541d504100c00a05602e0a124003040000e141003640a0010745540489411003011103491100400c1c0200150951055200044c1058000300c2c550201b000424500c4040c42c0c8034001c4d118040c50000e42c201c0890340111440c10542a40a000c01d01500700380c080811501d020349000701f4805004004a890301e22030620880c0d500d020802013041f041c4071441c0d103129003c42c003601303c0d250502c924002a43c40100c0a80b9081d002c1c0da901d102d03250f05000b0000c07180155840003200d4114a400004030003c80c0c51694110300031a800300548910140c0200b501e417080c42c200b0002c4070b06448118048840041c1d64040348203500c030302c5a00c080ca6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 87301466 1250 87300216 87300233
    0x506011e020703021305040330020c03340803060409320706050f0c01060806040309030b0105090705120406181401061409220f030206060a050108010f21 67
    0xe94216001081c000e8035600c180400e0304031440400c443d040c90441840006540110f4080c2212561441d0441940402d41000e5000c03911718200d02e40240b0000f50a024510f003c030141540f0001c1c1e4a07040c1d11400c42c0740c2181684000d02d2401c4481d501c44400c2c0c4000500001c0145822282c050300c002505840343e502d40c05052100c070060f100545241d09503e079410300c16021a0b41441c480d4001d440071900c0d00c2800390080c01103490801d8205030110310000244425032111001b000380384101c030514181420f01030b00e0061140426108208800e0003c02e030740c10680c0300d10340101565943c0e80d241550310150385c3c0d21140e0141c0210340c02c0d51030b07407001208142c003007641d0024203000c1d40301c0b0028210340ca8a80c07421515194054080b09400b0002145665102011140c0c040402082e08040480c000a02c0c2660190340030010300791200d129540c0c05142d80003c6151050b041514107400103074495005442c90442442001e41d0003049140501c40d8007042138a10300c2298502041e0150f14096039600c804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 87302716 1250 87301466 87301517
    0xa080d05130602040b090a0f050102030a110a0506070c0c060203030f010302060705070f0605090405010e0115050c010b03071203030b010816030209030307061107020a12030503040b090f01060b18060c10050601 91
    0x8407100220300741c8407d240001d4a040109442da8401e9099481e140c0080c1d12405110f146005101e500000000c0390b5030148110b00a0903031083c2a03620134940140e02400c1140c800c0c034160303500c03034142c00c0202d40705000100701c2c0d0007500d800020040e5a880c541c00c01070302d540054000c039814081c0b03140006007209138500c41405890b2a45840b81c540701c0e1035003030204642c0b050303008c10603003801000100244000c803200351046c2c0e10030345403043c0d5801540399080d02402910840703640500c034081000503500201c2c5000403803284a56410700c4190981e030011141000140c504950302c0c12055181c520070390003a4002c0c01008409001d0303e0030034040780c842004481c1c0300321007540004800500321b011032078280720030320103484d9200d008491030401e07490007043c42c000200003d004c0344100000ca0f4110394104805422070740c0303000c028171050340c9079425042140c10685100c18481065281c0c011a86002c0341600c004a81c0e0b6001450200c076808000c1002d41000303400e250611158080c034924007069620083c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 87303966 1250 87302716 87302729
    0x2010c06060905070e06031515040807230306090d031524020d0215040f030909050907051207032105070213050702070f030f0f0809040c090f06020a080d0513060204 72
    0x5030b81d152111340607110164030060a0320810f4200104001d8001e440241003840b00240c1b0420000d802500240c0100d1103140c2007001d02e84522040010b103000d0405001014a1260112030341d158102400d0556410701610680c8058100d043c4010009100b644040000802e2800c02c407002035a0702d10034a080d1a41d54820740c5841ca511002c80c0c2c14030703010000b001c02513134a40700510700c0a1a1035044c02190301c015000030942100018400c05244c850181c01c0c0c05031102600401003414105402903079441c00384500f500504000c5c02003640c006000c107007441103c0d080a041c0e1490441e04000074443c003022011007007401002d10944000d625401c00c40c440c03400c2ca4000c0080c050411040103480d0000d03503408803a80c824400030038400651207011543e4070b640c1c407403841e082810040c5071810140c043c941400390000c0c984500c0d0850f06602110a404503a944080301400e107848a0040f612103141e1234000d0800b07070040100080e140300c0c680c083c1d50f01840320091941369001a9640303209030382c400d52062 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 87305216 1250 87303966 87303971
    0x10b1903061a0c070f0602060106140405150304023f011d060106030501050619080a0f1104170a02030307140703021003020c06070e09060d14070f0612020301030c1202010c060609 78
    0x5289400c3c08000300703005008000400c15074503140c424025a1081305000d0540bc2141402111114511400c166806020010044408203000c0c400b209842d8104550503171150490400303084003120902481103041406c440c01c140a951100a4440c036001081101079041d0750303d20401542100403080418004840745c0944940d502d0000020240d4006801540c4606c0d000c002803a00203441410084100165040100c429511b8003060402004401168250309007000002d00b60483d5410060065400c040d00300036000052502c03a50791040c078a03c009425620410601000c1211220000303480d003440300841d007100d502ca5000c9801c05181c40b4145c00800e4021801d030114de6414802258030080030f00d040400700341e0400001e40c8401c0d024050a010310740c0300914030140101c10541d5510020f80c01e0803a400259150034400781910030340306800c006160903020219110090080301c0c120303900051103510340ca040c15074444050340351042c103c0c1400100c60b0454005811409040300800814500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 87306466 1250 87305216 87305227
    0x3040305030f01060e03030405090a1d010b040609060b032212030b040b100c1412070c090c0516020906040e06070320210c1b0a02040f0203010b1903061a 67
    0x3030340d0041d0381130300584284411402c1001c0e00d610004152011100100c40c0141c01da1910950030004010f810040b50302a030903c1d00d20f06104805401520400e0801d42e0208580780c2d4526050003198940d02400d01c1954042022031170740074030810801d4411001d22348004d4120744940e21a6000d03005910400c01098450300002c415150074484e65424000940340c02d03250420071300004260784440100101900c54143d40420741c00020043c0c000c6251031004d0943d624034450500320500c060070b1103007921040c1415011007030715104006031f85080340d00d100c0d80d805001641d401c10403850801040c80383c100e84d9842404500f08001c102490041525403000a8030212081c00c0d80300d400b4110030503c1a4a00401c041d04142c0c81b6a40151105002003800b02c090343c640840b05446882143c80c11840e61940580030240c41c1d1000c0b800b01185c40c421101005008450f1204000341c0c0002d02c5542210308060004102c40a903802108000c01c104d45000503409840d0000d03030032100803140c02c91900d010302142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 87307716 1250 87306466 87306481
    0xd0b0105090f070507030f14040306020705011805100c050d020415030608120d090c0e04050318040c0503060103090c090f09110307031e050106030b07031a010903020a060c05030f0304030503 83
    0x200560040d8050000404503d001d600260413841298001810000961200341141c0d22030880002c8015032680c00581c1d07141e0300e0a0444c003039041040259071039460252420340c00c240c04245400c00c554440081c158880f0240007807c020030003086035005201c8100988501e01c1d107240700402c06440725107201c0b100036448030b000408850301c5070015840765000c00d03401124415000c0a5503408401180040369a44640c42c107205a15840d40c0711454141d004d40030300040120120242c4010030454840c2e00b502c072984410007094541a020742d1004c00c02c104085142d035482900884000e50051141900c170766520090a411039001d40010110680e50740001000c10035146c0c81406015000c60007040c1940c11502d030a4406d1481c0156400003a0303860045800708042904694000c640000590449203808a0060003410a07480702c0019015100701e40718840d03004c1d40302c41041c4c0750081d0400c56014205030040c2c030103240c0080c00391100d10042c000501c540e140070004600c128441c1e03444d10788030b050454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 87308966 1250 87307716 87307729
    0x10203040c1d0c040b090d050a0303091b060503010323070303080610080c03010902070f06020408010506150c070b03060402120c04031407060c030c02130c0c020306100509060411090d0b0105 83
    0x35100b00c5510902d909218441d44100203483c2550b000700c01250342c0b000c40e080010206080b110005081d400754a985078141a090f07840b16441a024001c00d0b41d103c0200c0282445038482c40c000e06010a83c10700060021804203440664969070402c1c40004014211a01c18540042d86d4001c0b0b00061480d81040003d04100c2091041d05025081544c02801e001c0441e1459000c140280b008142d07000c1601011301014900c003840460f040281150f4407502e40c818540603101c01c036403481c000c8944c5a44541514420022112890000300140c0881380c14841405e01d640c5c00601915842502400084544441d4214640c020242c000340155100d2852400c1c02c004000540c1c4980c0c5500001403c0180744d800100d00c41c2207503414a40311003403c42620010304080712490141142c285001c901208032a004214403070407a0007101100c441d5920701c01030002c000042d0040a4000c0d84150106280c1e007003d82091541400c40f080b900d04014074540444d850841c03002090fa00c500303203500100070303504229 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 87310216 1250 87308966 87308999
    0x4080d2301080c040b0315060d15020307030506010c1101110c2205061516081201060809010b030105091b030102071b14040204120b0405010605030f030d0510030230010203040c 77
    0x4c0e41c040c4403003000c1c02d0020b9102c044282c1d84800c2880e050000a9140d613035010751303018541c0c0c00000782160701140d11014000390402c40301c039800320789460045602513000b41e800d800c81507480181c42600a9034a401190640700e002850341c41c0c0c4c4201c3c44d85000c155035001000038000941c4098091010081e0081010b032400078100d140120007106034003500c628901c04480140c0310318810360029510a180452130340c4501090442d66101100c00440d81940c4603c42d10b0280745800d00034040300c480c2d84205400c0f10411b590b441410317800f12001801c0307050038003440c420a5000400041c2000480c0e2a0341200f040880e000741c241c81c0c50402c0c18070403551003641142884500fa1000c50800b800d2107100100c54040900290006881d04005000c00c082504a030303001e000042c068030300c082c50070001a5642d81000c00c0c0e6004a90800c800240c1c050070b10b102c0101103a40040020b80040d08245000700e040e00d05001c66000c031507481a60840380502400110301403442100e01c07042d1145032089140f0740c0c1c60131 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 87311466 1250 87310216 87310219
    0x60507020a1a01060507170906130602010510050604060c02010c020901090b101d060906091206011706090c041d061f0b1206040b030a150603140a050604080d2301080c 73
    0xb044018003d255100d4192010b042c1d124103075000c00c07442c40c28132003040e00401c5a080d03440400025a0540310f00c00020810407500d164000303024648030071f15029103042d06070154070713041402440104050b5105036400d00c0c0c030701d0060612859049480d00032500711102604400041030f200c001e02e4106040040c0e5143c111101c1c1c4c50b04962aa050703d00a19600228103201442410003040303002e5599a148100c500c00300c0c006052000064508035179035242d0409229071485c2d031001100742c421030600826818410407440000e0400304c140401008010b05900310702000842c002ea0300c0d4581d11904000e080d00804000300a100c418000c041004407a80c4150061500903000f44a6040441a40340340d0a4210070100ca000c01d82061050120b0b1034995030000103031052890700003060240301d0355800f40054034015800007007005600c0ca0754035941d848052008250303510200000e000b03d030110307002d00070304001c050000c00e0000a0030f05041e072003d00e180f00e01d803d44032603070700400081c1c13410013084864020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 87312716 1250 87311466 87311513
    0x6030c0415080f012709030207050102010510060c0b0705070807080c060a0e0a03082a092106130807020406030303050601080105100c0219090c021501060e0d0f0f060507020a 76
    0x4151a68080e88403042c81074043c5c640b060010300060f41c49038042c02400d40340303043c401c00c1400c5090500a58820f000c2c1309003405941707441c000c20182c440305103540703080e5a281d03100d007011b281555880400d45840200410100403080c130013100012400401403000b5405a04c100d43c8503540000742500b031940280046000f140b4240c01c6009002c00440c0b040102900350a1550700341e0344005044c030b403007229410a903104c401e00d4200d102a4803001c1014086000e4152800441d0381800d001141c8070743c00c02d011026482e8803120000d10804084440301725140d1080d4a824148a407690100d400d0341c10580084003c20303200c401300049540d101000500521045540ba08030001404000d0145c080064020313000b229010f0800e0103060714030f0242c10003454400c07000c010b060b0345014025283d401499205281c142407400005031103106002c11101c489008042c1d100301c46084c0d4840d040310202480c200c4040c520701e03000c0c0d0f000c910300307120341403203850150054030714010300c4e01e0301341e043c2c1203081c55040b1070b0017 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 87313966 1250 87312716 87312721
    0xc100b0406030f02010f18090617071d04060b04020a05090f0301110a030b01031404050c091b030106030b0d150501141203090607050a08070f06110a170a060506030c041508 75
    0x101043d203c905020b0b02070030049642410360307008448444004089660805022100203074540860b800041111141000b161040c0c0f000c9084a8a41c440340c807401c24000b6542c800c5d4000c00058042d0950851300c42c80000030300c40c4902010070240d80044401d003010440100b4a284213061071030350050707800011402049501624280d0410600580703220004160b60f540d44601288d00030b9001e4902d421500ca0030320024a0140340c8107036220300360b41180303006200c1e440104150405443c400d001101c5121324203030a41e03081078406c50080c01c5004407607510491800c50b01c0082154403621b05414802001c0c042959818070140404001200c840980106d039118034103051001c0c08020b4401c40f040407a0555a252240d043c41c51800e0000c8102414013500040c00c0d00400061030040e0f001d65110748001d2148202401c0c030000070380100c40b440400b00312120040c0042400005080744d02c614074071000101d054a0700c0205000e41c000720748420508070001000e006144982142080c40700c502d240112562 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 87315216 1250 87313966 87313973
    0x110705100c0f180b13081509010c0f0903080306010309080d1b020325140f010207110108040201230c0a0606140402030403200309120a0308070905180c0f0c100b040603 73
    0x944603442001000c0c0d80105e0310303c03034034020050428010034240c1e08507004640401c1950400e2501a10320b80c0f019841d080380d152046000d054008400c81803a2074040b649459030304c0d090f019500003401a41099030f2244418000340c0c04c01c010f8014a0f0744070700002840ca56010100b42c4c1401900b032540155401440164802403041300414404c4010038211904d001161800c00483d40c02c0300081e40030703402000c40b071041034181580600b54007401007000c4c000403d0446d005450b1461f042d43d000e03000800714051001c800e6841c620256045d031300207410303d00e401181091242884002a000ca44c101e48540341007100c00d00740514605009022502145181020780d030143c040440f84903c400012007500105403050010300c00e6980300900a06450203004210364016120fa80001046002c1880031000c144154414426201519405042c00c0281006040507180d03070360300100302004a4008200c070200c4120610080c00a4842c1d000050203072204500811041c0c8142c0c604c0c05024610345182040407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 87316466 1250 87315216 87315257
    0x40b06031e120708091518090105010f050c15010b0403030305010905070c031409100806030115030816020a080f030304051504030203040e0402060904090b01171c03110705100c0f 78
    0x116002c0341c0000d0768424407807400301154011514510703401011100000c400345000b01c0146400d090300d254001c0c0600300361080010740760b000e01400c2e0016103400355201510340a0300090074101102002c903011481c58000c02c000c1100309811001903400041000c00405404d07010710380c054015900c040c025444d1242c0000c104c0000c000707010b0104001040c040030704020010840f07100c2c2401070b2100704061403145010741010001d69400b4080d600e48500356000c0d04082e15030000b80c035400344201e0300e05485103010f00424006400160f9100b010064000f880e000104450440250010091030700d0385800d052450614800b01c10b0040008440020040001d50200c102c4003a1606100c05c05040e0b00d80707002059040c020110815007040c9002c001d0700510010008090480d81844005a241484017080580303411000074003190010341c0110001c0514000d401120483d0102c110540c249016170b15030703a103880c0500c00392824056546040d01309a540c032619101404089092102800c080d071481c0c0d012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87317716 1250 87316466 87316483
    0x10c0203031e071103030a0204030218070c0204110408150a0e0d050301030f03110a03090306050903120f0901111603090605090303030f06010e0d051b090912070f0803040b06031e 78
    0x9010040c000828944c0100074491041c604101169142e00c2d10402c144020740c0a400140d101d881d0003d03440284840141c240d81c8039260701d503101d4030003000c0c0ba401d0001401403103150700300c401c0c014040465a1f176003c0007008401c02c3c5040d030310540f600300011550f045030300c000a400044d4001c400200c0c40c40d900304046a04407640180891165915800e0446050351003144070009070040b0300100c3c0138164011076540950740189810029910744d0a1340c183d49104030320788504014a0100000c0300b04507201202a4003a40020001c01e0305d0020090000041d80300780c080004a0f940c01000740d00381607218809030050700ca641440c42c07401c800d820001e9503034080106010707000e80d1500e0016446911915502d03210b0400034068041700855440d1640d110710711041c190000460712098400c441c0340c030001e4180903181d074501601d03101451400107661a4028070060312126040241d00700040c1c01000114815400354014000c0c5003445010142480d4902c40403424101a00340c0551340c0e420003080161 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 87318966 1250 87317716 87317761
    0x4020f0604060921060606020d08150d020d0807020303030c0415050901080a0b040902090a0f05090a020a05090a060b0f0c0607020109051b0111010203010f06020f01060810050408070c0b0a02010c020303 88
    0x5134030341d54000071007400800c05000100214100303440050942e400055840300c0700881d8952880540d6000404c0000315913850300d15511410700707000d030300140c1020001d9505030350161880d540782c6035035500483d18550003601c41d844100c500050402c441040e120200c100c100e0503151082c82c01e0320080000b407802d4805800a9611503880c1d8100780f190345e455010a4041e0340c090100001440e040817480300501c4d1400a20000500300000503078030700404604002c84030780c01403c0302544e43c1894103101c0c0349400103006400300d9980301c0c00424003840702c0c0060b02d0b003880c4141271550744800d610101810150042d00203c00e41e070612030712a00282000c1b8070320151154461034070340010340000040b92007040001c8462900d500c000004a0a500603240798001e13500c1c1c503000c40700c0640c0c8002e9000c1c01ca4602d40303c1d503002c541003031014111400301a000310350400c2c020410390741130030140c1d03e84854880d22544158034820001940d2002541c082c01408100700250020b181507107804158000e03020f140c0040350 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 87320216 1250 87318966 87318989
    0x111010203070c0b0606090901170c040501030804030303020f040e010f050f0f0901051e06120f01050303070b01031101140a090503061315020f121006231606021b0604020f06040609 79
    0x285490315400187d03854090014100e280c1d95948d61100913400340c1c86038170b00c0094041c40107150581e05003401240c0c1202d80c40410a0301d03091030360310b0440094000f40c100b414600000c010004180c04c2c9902c9990182200c100b0580f00c080c41c040030000275001d813860041c0545410340ea600e0882d69074041d09411548251041d40d40e000155443d0501444407800b0564400d901007504120302e5100c405641c41041c0c17a24465107140d80f100e080659a00803030600809064001d801800082d0340081010001c01040c10188010b00c0303480866015900f0100310800000c403d480e00704501e14040040503046042041e110403030300f0341ca40307800c1c803451803e0f44140728041d000564004e4490107802141e680f10606030100440c2c0c18841e80e2013051030107d2281360000f0b4601202169084030312201c02c0051b4089003103041c80e058956004000344040750505036007541e401d1141e0403a00801d050807010f10035400c00603102500d420b1040140c4502440c1320315004040078401400340d00d41182c2c140303080d01c81c010900d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 87321466 1250 87320216 87320221
    0x31208060316060f111911030f060412050d110301120605060f2103090402130303020d0810050d0c05030303100503071e06140408010612050d410406020c0111010203070c0b 75
    0x1203846d03c1c14450b02c80c1121045607845100384045a240c1040030001182a18118010510310f95510071096501501c0f00c102c080300180d00340d018500900d64000b0f00407011a02031817081080710581c009a0002e01c64500c0701d4809820042548502d55004c0402c44440b48543d01c003401040b00715450b40501c03c018078161108440c12082041556208040180207540d01e02e540b6840720300108840c88120090300c02e8400038000b50380101c107040c0c400c90074090b98018a924000400440e065a081d042e178000903400340c040740645083c001907100d4103000c942c4d406528602814113181c250283c0c8160840b0141520b2003100862914000044070140d00d810502301201c03030882152881160300c9048990710b420f1000505d90855015051400e003e04280c803164074040405861001c0611100b01000300c01083c0711400203484440454034464002c2e40e40346203400358003031003119440b6802840c050303031020700102c441e982d1000079080e1401d0400021750035400c1007800031302002445400105400c195000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 87322716 1250 87321466 87321497
    0x30604090c05100e0306011215050712050c0a0905010e06030403050307020f0d0305010306060603020c1e010b120609061b03070806040f09030c02040605030a05060103021504031208060316060f 84
    0x500301c024103801080591400c044100140c101c40b408100075010313000b9070000140740c1d030700c82c0c402c1c0561a800018455580503036660700001000003c0001e41030101090140543c3d0809202e064801c055036680d4a5490a607034002030b2400d407070340c3c0c411810042003c030070303030290303202e140549030000c0e4981040ca4a03501d400300e00340d090000c1d10140c0303007e40c4503d504a241c0958542c01060403240911802c128403030315a5411002d0303100c4d8200182c059440080c6035100b400d1180c401c00041050400002156288140021b0b0041d00a1021940035448a4180501c040302030000e190006004000b030104040c0c4403548548501004150074288030000d40040c405858941190105402c240d00c01c01140040385000782000300283c0040c1d029620b410300110301810000b07408090150814014581680707507a00300000345100140200150400340710000004031110000342d0070559585402c0d03c070f0325042060514282080b403800da0008600182001541d4104203e07641d90111403a240800100004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 87323966 1250 87322716 87322733
    0xd0213030b0a0501031a071b02030115090911040504020315040201171905090d02100b06070507030f030305090c010e090901061505090411030c040e04050703060f1b0c050303060409 79
    0x18409041d400141c030070440c224800707510141c144c2e48515030142e1003424054041d460107504580c0300012407580c65210f244010410007081d28244010700116098030700101d854150000b0390f000d58804c5840d500c00c0001c00c0900500b88801c1c1074207171410000c51034150006a076071601d60058001e2090303820046425a48500100b001c20380340c1c034803075103001c3c2030160440c60000c065024410040389444080303a2125004034180501112580c001c18010305942160703401030246818003a80a0790420060000810034400500254000c05a19107410214200601a141c0080c0f0908494120101d1000140e130001280410100b003582e5021140d80c070300100d60300415103a0040c58034649408010341030a6405001801803c2d400d544c28002003208a50041090200b6128800041028801803094141c0404800e5009006104540c400c0c0c2da66101c42d0200d450744c54401554648580700d09071420305500740500891014540100d101044d602c81070307200c1c00023500143c411740d158070302c0c0e406000c5181c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 87325216 1250 87323966 87323969
    0x2060703120216050c100f051309180210050306030619092f0a03050309010309020105040b040815010b0c100c09050414070f021902010f1209060603060b060c030d0213 73
    0x2800c04542d520704400125082028284007101d0b240b00e00405c482c11810b05207800f03031864110713445000500300341030701c10787d02074002e59000c41c00b0300d9500300300045807500c40c09003008110080c0d00310700001a0030b0040c8003001c0780c007180ca503040c00030401c14048551400120306602c40041442440d201256034040000340000c100f015202070102c0241c800c1c4100800100f003c1d50424884904400d080322040c4196090f0500c0040c205030004d003d50f483c554000c2c0c11103264075205140c0f0602c0c19468030100e07841900715410041d01980070207c0304607503011061440d409070803040da980e410301d40a034600300c0d608d1441c503a50407000c603111b040c410702d00d5000f0098103001d07100c0208117201da942c0e0701030b0218400300c0480b10240061810038903500c51900110b44a10084d0001c0209030200c0c0700d50b001920401c08801484d0100030010288844160b44c500c2210b24261140380040b406034039604005081e80c0b18101d051780308800030050072141c43d1000041704d00721018840c02684034800440000b01581c0c07a0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 87326466 1250 87325216 87325247
    0x5070618021207050f15040e090a0b042609030c01030f1b0309050c04050603060c03061f02030306040b04181407050301060e160c080f0309010b0301020c0a05010b0f060702060703 78
    0x5003020b2164054040341503c1034a1090b1811010805994104104680c1020240005450070007046c07041c4410303240b1140d801180c2000f1100160303075680d1061000441140c0659041c030072003000505804004418a002c12144400541040c050800107901c49600281c510706141d510026546409a25002084124011811400000c2c3c2c03c0c0700140140040680c100d40d41c0c020805080e400d85410711542c0c0c015036000d4010081079446400e00001da82c8041c108540c0006100301001c5001200c00c0d01005e86031076a405580c0f2401d1080510040e1503403070683c640300304d0406490b548190012604071442ca9044510000c070070a1040c0c0440c101409a0090381d0594203110700441e4051010b0131060240410020101d11240c6081c012a4850540480101901001c101100c6c03020310620113950050590000010202e03841000a030132603200c60011178035600100e5245080c08000c1c401d200d4071110543e8140c2101041d038000401034410341d00028031036040072032001c0030b0500c80c40103504503034007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 87327716 1250 87326466 87326479
    0x10140301151512050c07030804030c050a0c171203150a050a030b04021201060f0b071509120201060806061c03140d02091203090f040e0c150409060b04060507061802 72
    0x86030380c000c0320340010a0140c2d0012075004520b0b04540d00003403103081d00c10560009030a0600040c2e5070100e502001c0a40b05030100300503440c078940495014040480b41038800c10b03044440c50b161200c45810320720080800d031221303007060280046c104040d00c01c030303644865141801c1d407800300300400040342000240c102c15001300381c0c21004010804e0f482855809207000f00c1d00e603108890a824454240c603490700980c81700b00c0110f002000618807000c06003811300d02c40c07030854061502060013030301121030b21801503c03a091055040a0003d8080c4586001780940070007800e91890b011011900c2082e9099010700b120ba0303441141c00070725101d104041e031840806603030705607100300c0f482c400300103508002d00403440383d2130a4443c100c140d1000001c4805d0890040c080d0b40b000100c407801c1000510b840300001029025440f071044407580c461101e14580c0701d54150194489003800c207004c00702c610359080080e1000e03007000306020703441e08441614291a400003001c07030b403a012801144400105048000e40005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 87328966 1250 87327716 87327719
    0x906091b0705030c070b0a021902130504050d12020a020715030204080303010e0415140417042705090a03090306020a02010b0a06050c0105060102030301051e0a120f030806091014030115 81
    0x4001441e043c01260221405c403501c0b00c0d4900007902c0b61b440000050707441002260481c05078000384a945a0000702803003a1418803c040c44140c8804a81c221b8081d000001d80040240c0c0018180c0304d200c0004104504042000d40d010b5a613400728001c58045100c4407010155061107901100e000d00b6600c0c080e80d88a50b07442e2020001000c09540880b4075400358004000003070310501c02d0701d00310104800090002d84581c4c0390b01240c4010b8103060301c01d01000300030210783c94041d0007850141058190a901280c40c0041300c940889902030051490b6421904104000c0f0380c1c070010080944c1d820140c01a80d40d08526010b03801080c10b20202500851500d60001e50705401002520350051050020302c080e5a581004a0300c3c2d100c24016542d00c00311004980c50f034110000c4003c03079003c601505480c2c0c582c0d240d0009038010703000000c044404c0545a603d040805034000d141e2034004000b6a01a49a810180781521151289001d401012a06002c88036090f581c00d40146441c0110041c50700c490b503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 87330216 1250 87328966 87328973
    0x9020711061204140109110603060307030c0f03150c02030307050c21040305060a110a110a0501050a020301051206010b0d24230a050d0206030603210301060305070804020906091b07 79
    0x250483c1c0648044a14018410340044180201c51009a1201d00742110250300b20800010303409c0074124540520609101100151840703100f04080d050070003141c80b10318610b2070820030700c4a04800c5049030b20b04040d4410b43c0c490300041503e41240b03903401d0103900e03010340300060b600d000b01006281181c0440d012094589241400c014425a40280140d800560b541d168a07420b0b035100300c01c440a0340600b04440c0801034403614800d03485e040c02d00240c0d1000322442d265282581c005856070340c08103a001004004510f0310100c040c84200e08100030b000b80b98900150558503010313444910344555120380301e0081c208103921000c80e4024110002035589511102d101c04804075280e00300880c00201111517065280589140c01107640060040581d41c200307500348051500042d1042d505445883c480c09d51002140204051140d901280c036a200c1d8907180c07000341a6580540b43d8014001c111062001507118503100e0765001c034040e510307001e45403550100300200d03940da41c0b40114511000b01c0c400041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 87331466 1250 87330216 87330247
    0x20117040c030201030f090f1707060e0c1f08070c0206120f0f0603120301090c11030d0209010207054e0a060501060207180e010209040c03020909010b0906040902071106 74
    0x5480c000c0c0d030100058a4541b01d82402ca82c4c070214040d14501c84a811f2400080780390351400b00445044008070b003070070040c1d505c0300240c80d5100108001500300c10520459410910b00d01d074820270300c44213101d440480307282000c1e03e060405403034941040341e810704d82d40039034842c2411503052400400480ca4146840c11000c04c20701000d45080c8441e81904000c50141d10300010b80d40e00340c44c03102d81114616440c00d041d4070010300c03920710701000380700203180494040d50b400c3c000f13095801c000c031802580e1141440002410b1a1180d04941d21403104828404c9500c80110810400000400c06540010200080360400100c0001c54203242c5010b41181da015554007041d43d240052003280180300c9070740c89031001e03a2a0500c600940094480700b2601e00301c804c1a44c3c12401a8501c404001441e241031171001c94199112640c04201094000420808904015003918010101025054141404080080d00fa0b100c1d0b48201c0003a0740d00450140207200c24800c0c003602281d00103052680d60b81140714420340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 87332716 1250 87331466 87331469
    0x306030b09151f171014040b09030307210e070b1b01200313050a030c050d080108121818010509090d050307201f0606050c03030a09020117040c 63
    0x1072140c0c0b428081803c988000e4031000c2841183e21040201d1070074801c0510a000d08403111462500c00c0c0014008070303482070312456265440641d060400303450f150510f0040c00001510800c0340ba8010010055256800040c60310f400043c0c2030728030030301e84d5880e00c0c81c005030690a2448805000c0d0b860000343d080c0d003140c0100340b86290064214111034007544881e08036180d0007400d40b070100c281440c000d040710700d08000715400114100b8100043c042d13611400d282640d190b038101c2c08601088645c0d0309001041150119001c0b061800384c10941c18101c00b1503d900b240b110007400c06a02142e044502d0307100300d040d0030f0f4059010f0840070142c0042180300b41805000c0c82500d024400314400305415884c0400c0302d682c400300c81d480d402e10310340714202c085880703080580407100b0085000c960740d001e41c00c0a0140700445503940c41403e803c200300901003011110303280d002d60140300040261992001000c0181c2c0c1d030042c41d4440002d115881d17800142c0700640352a284050114100c41040100100108400c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 87333966 1250 87332716 87332743
    0x12020609160b070609020d12020303040b010503160312051c0204090e1209061804090606031101020712080f0c03040303020703110904050c040c021e070510050406080a0c0306030b09 79
    0x1100300000740076200d088201c5000318120354004004003000b0601c0c60b040040030920242c0314042c4031b140c54072620012440109108010381002060005108000413520f014080440c0641009004010900c02c1502c6621006141d42840c0c501400454003a00c1034034655503000741c206881248665044000b50f0140c0a50702000749010040c0e03101c480001400f6142000441c0c2c8185049081c03070030001c03a40c00207045200c0e8840e84440350107594070b5034000c0340103280c45074001040d05800c502d09007480c802c51300d5045e030441d0b0094004100840102159865050b00209042c0d555140451a10894440c400c0c94089601c00020000304140e80042e2400c203c90007061220307009500e11040004484041c0c3d0003400302d0b8000801910145400d900120356400e00d40111240000d078030f50005082541000d800c042d58114800402440c00c041b001768000b02c0452401a00e010f04000c00038151400c040d01c1003110517a90841c020415019070300c0707000038607044000c1c079285250034030390030360344896921550307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 87335216 1250 87333966 87333973
    0x90e0604060e010209010504060c050118030c050606060f090f031c110f0303060a03030e0307050913020310150303080c09032a010e0f060d1d01091b0e0f04020102030712020609 77
    0x2c064150040c405e6071103441050f55011b00c2c0520780b80089076010010302d81980c0ba55a261014600c800180d12203480051198a608811210300e0802a090120003030805006040411400c08004451411075183c06001c4480200a00140010901d03103200b580c9460400d511a48900e865140c00c0a04001c681001100704c0b0341c0b64038000d5015031a80015980711b0741009c011032003400040e020ba00495007000000c3e0440da4055a1403000456081003591503d800b10810b02c50310040d8207040c40282d0010031141c00c10302036034096110407582d0380a1480090200306001d40882c0c0140014821500341200040450382c0210343c3d40d024403c1d44091807003e15000155240f2108154014045410301040c014161000d0414410a0280d213034040360110144564407a0303c2c01a082150642042540744c0d0000044c04032428580a5a07200003d07d0348940001001c00400ca4452030698150b440203800041d5407164983c2c0c0b00603859401182c10007401c01c0201180840081d900190f154031854004c81107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 87336466 1250 87335216 87335231
    0x140907060905030703060c0203090a0b04060f02030301030228030807061a010f09091817040501140415140f0c0c100c030206060d1a040c05090a1802041104090e060406 73
    0x1c1e41c00d8005441a1038141d00061001c0000c40c00960240203c0c00071401524a411803020004030716003015040070b803100790040b80038850a41d011a000360904000e00045156504540010700400b013001c1402034100d03900504503490f454052074800045510401303041d11003006161240c0542607000c1d4407074a0362400032050041c0c0d0711900703000244980c642c0310305026500300310402003d4820b41c41e551804580f24220000010341d04000200ea450301d480710345880310305003000140b00014000310766480002c10f0209120200710000d0300c1c0c0c400000c038180200208181c007100c050724005e00c560302e810301320003060612030703a04040381c04002d41800700c61003030f803100c0d0f509020750700d000b0000809401644040d00051440c104a0f0030560517900400140c0b002e9030700304084090b0204101c0d4100c9450910340c0c410011070030702c600802c4d0481c5650340b080c4002c8072500d030034145045003080080e101f5611054540e840c002010101e07030240a0100090008074003050069035a00c030706980407100d40341713800207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 87337716 1250 87336466 87336479
    0x1020f0f0414100804020f040e120304060e070b04061b1a0702120a0c020d02130c020f010c0507151e06060203090111030903072c070e100c02060307050d0906140907 72
    0x43c045001901600c4001007603da070f03024030038021504032115810a0759030311a4141144100308807010211a42165039aa140c0744c5450b0040c1c451101040398540c2c0400c00c1031048040b141c0a0320144c60640c03a0140034001544082e1283c0180c015000d4000c09032066040742c8808041c03103240c403601c2950222001002010100802841040006800500e00c01a0b81c001403404040700c400c5c2500040003406070260100400c0100c40e00d2803031039000350307220440c480c1240ca02805062444401400c2007402c200380342c0c5514007209885120141200d982c2c4110320904100c648a40d14180d180190070401e040d09c03208065a070781c0c00316105c0d50124003018001d0b042d0b081d001003100c54090018014220b068a0302c0c000750204801e888003c80c42000859081c003070340341c10740c0e420740c403d500b00e54950358062903007000d110300c498604121070f041008410f1010090b0321100e0483e50014424909150386540c2d001c010402440c450300001c000b20309101c2d14500c44205102c3c0c40e4000d00c0c0c42410f17030307801ca641d420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 87338966 1250 87337716 87337729
    0x1b061d0a08090402070503120c0c0d050c07030605060409150b0307090905030a2006070915020303280209030613021203030f0f04020f04150305010501151b030201020f0f0414 76
    0x1000400301c18007001981100d0510740c02030041750b840b0303038112400c224015110040302441160390104540006c1541ca1411008100e110500c1c50745007032080c5000100000c0603150f0919000c0a000c0c943c440c40441c0b1070342c40c1c0d03501a804040c3c220011848080403060100040d00c51100c40d01d00ca48141c51002c10288a076104072042ca1754414000c1d4500714890800303840e8294040075881c0c644200c0907240c450907005102d410300c12940382c0d840207881c904002c0d003400c64071008100341085600c00c2c020025900380c450309168615107004024114012524450b2005c0d201e0003209540502540b020302904424550140d8805413080b580c1c1c01c1d04d4a60903019680e01e000032200007409100d014045240c3d101c0d564201d9070024000313400026481c413410042001e07981360b100001c2c00c80344014820803d00000f07101d0f09016181c1240c00004144101c3c43c001c000d42c248000a40707101c4002d01c0e00c841058001d5045507603421603070f54401d446901c21082004260000d101e5990148041619900d291501d039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 87340216 1250 87338966 87338983
    0x33f0c0905100219020f180603100905100506060d0903080603060912040303050a0e09011215020a0c080d02190f0207090908030c030a0605120a110a0311060a1b061d 72
    0x254003c1c240000c0d1080b071306803010322044084e41c100d28400c208a00c141c0f980010701c0c0c0c0f04c2061580081d0207040110030326150240710001c3d40c402a02e04901c8a001a001080508501d111041c0118030740e152000001c500d8450b003501d07000d1107480c00300988101604040d03210f20481c012400d984dc20307699141103a480700040c10608440350300420003440028003c00c06810507400d07070302d050401d0078103000118034045420b070042800551034010410400448042d035215000d00b12600b0340c1031103158580135000e4241088010041d100c0825a103801d05125130655011054818010114441c0b203440178180b075050340c0390032005000d8844081609841c074001c0d18185907100d280c1502d0360f5940d40030648a600044c0842115984070100060142d0b16014000d00d07881101c80a003820542c00d15140325080c40000d00c050051f80300c09010404a1098034411103a800141c42e02643e81d0300b0907004542000407001d00850034100ac0c1d82d54414004c55030b2081d5044c1c4401520a2101c1044040103513840c00e44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 87341466 1250 87340216 87340249
    0x3140a020d140304050d140610030b060609010509030105130302070e0c040603020d090507030503030709090e0a0204050403110d0c02040c05120414070f170118033f0c0905 75
    0x242801c60000a1489940d95810301400e401d072402c0c1500c480024800781c002d5101078a542002450319040388005000c580e81000100c00c540f540d4900c1c550700c08942c22401007042d071244d50080707420390483e4016421100c2c2448028001c0210f031400c0ca0900c55241000341060b00144284500031940da5811240a4014001c2c09411402d00740341444c01c03000b0f0740c4a0490311003040c0d103440001d000142c00f0060341001d14440d6019503200d20b004000146880d02907884030106a003403040c41511907901061001e51150151000300c4d0664075800e0a44081400240702a40c52280e20760305502941e01558031042144203c80074020005110402c4640b8060040d01d640512092800702d40040c0d034141d4041520200c82098408503542d54243c0400c8216580c40480700c03100e980f00c0c1140120b0300307100c0d80a031443d114003480115034003520000c080210742400429880c140320045003144110f0303030000c540e40c1d4810f450800042c5500090502800610345014045a528080030400b850b00c090340301003840d403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 87342716 1250 87341466 87341479
    0x20c030a050604060510090528060f090c140d0f0b010e1c0309180515010207080d0e040f0e030903100b0102030d050406060e0103051c0212090f01030b03030a030603140a02 75
    0x65544500b0002c00d00a011500c030b032074813001d0000745501d41d8048d281c4220039064100e40c0076800050145d036101c41611510b013001e803810006001c0c5041801d2544250341001e4000984003c035800709944220322241c8000e150900032a8119a411094004942205261340144074a181c440015507034158548441503101100c9032420341d500c1c00c025106141039007e448c180400039595020110080f858a01d0084280d454104021880f199a10381c4030f42090280700a00c1c6223440c0001b00741d195403d5000c18010032043c0301e00381c1815a05d40d085401031081c0380404000e224820890a9980c1e404400c4050180c050071038806a01d2150b4410b18410f200181c002c0d41c0340c0050115418010f1200904c00c45515545000121302448490080b070701031031045008240444c00d211026403a03002c0d0307205650031584035840090746440300c9025110b4014007070321880b044000b8403005030050301c039090380c0b2500b42c4400301e050361006600d80c119034100e0740205000c1c402001e0400d00142c68060784903000e50882d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 87343966 1250 87342716 87342721
    0x1060e0402160b131202070e1602070501110c0907120f05060a05060901050d0c020601050a080601050618030a0609200a211b09150e070905010503090a021807020c030a0506 75
    0x10a03a544030356201c1c82c0c402e4540200720381c1743d40341380300d60544201000040e401110144020018a01055040051032102c000480c60152000b540c3d9102401528104501075041442c80e00c4200059801200d00401c902640d01c0e000c00700030010025044000b240b6400d041c05555002c019101e11405654040d018080c42400e010a1010307035403140c50841c2c10011b007002102e00382c207041c0c892440c180b50b00b0340c043c00305540b42c01c2c104603144443d604886040d070800c90040010741e4900040300c562400f81020048901c8000d000a8204459040b02401180c2814040020071400b0a40e401440d031301f0351807503481802850148104045613008094244051480f800b041c0041c03030070702c59000d40c030990f0681c007503d80d9003201e9000c0d01030130b80c4072180185d15641c00100c0400041902e801404007084105840d150042000300011540d105030f5040c81000404250183c10502000080310340103003425a28004007000ca070030b00324046407004010700410114220510713002c54540100c03900f01b401440584c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 87345216 1250 87343966 87343973
    0x8220506070302090d0b010306050f0705030907030b0403050408100906060b18060c010e0f0102070302071212081b0711101403011401091502100e060105030a030e131401060e040216 79
    0xb0350064030722560091060817000c000502d81c810031030103503100f00b00200c0e907810000e00f00181040701800100900c601030007040710310380000601d14200c0380c0061840449469505083d85e140c440d80c1c00c04400c5014000250300e4903c1c0980043d40203500c949801c01950b0760300d4071069041d00803501030201100380062112001e18006000d07160700342c3c4550000600c1c0d0715809030340f85000c8126040100c280d402142c40c3c8141501404000014102842d20410b50b004580c0e0301c5000e10b400f07103c0d00003841100008901010038192165004a074050001c994800c010305003100c03031002e584061489103510701091002c9910170500002d20f201c0301e61141d8110b9013013801c40d1040c0010300700d00d10b042100180e40060240106a1803e100c407150390041e2030a104084096410303100701c40c41001c1603501030030041010751000a0102100350300b5250000c440b0384c4800c0050f0a0a030450001c038441803d1900382046901d41c500154100e0351552a042d03100042c00303050200340c2c00380408901d150140c119555022 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 87346466 1250 87345216 87345221
    0xf02070501030516140c06070207090f061208030403030b031f0f1401120305070204050109060e07090308090f010306030b0a140a151401030209091911090d170f0703082205060703 78
    0x4a0b41212107250400555406c0705140039000c503181d2380164005202085003040c240b10f00d400350642c80b071081c001c0c01d00b0912b540030003001c080c3e8010701012000000034107240c4294003c40f200b07100142603541303044502022045600300c0070350301c504082c40d10414042d511928425403958040e07903281d80755142c1c40c03c2180c440c02b40c100720041d001d201f410024000169503a2150b0f038040c08080c02c0005480b1304212401c0d004e0b08008000c0310034408680030074800300d4400b20658003c140d045944000b400304070741c0100c01a01491340018400005075082c02514003840c0c20203c1c8103049441d081d00e135075940031049420f0b180e64502100c400030550005100d08608805188078060f01810050f00d40005400442c2100c5401c841415000714565840d03070b030410a600031a4a40b81e50481c0b29801d26a448002412411031160014945541030750007070414440c0d40103407040450800900d81c1c40306a94100074000650441d0640c2514510020041020341c903120241c1c94035030010000e184581c0c030094283c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 87347716 1250 87346466 87346487
    0x4060e030c1c0222050a0b03030a02070e0606040305030705010902030609071401080c040b030a15060c0804140d0f0305090103050c2701020c040606020c0f010c02032a100f02070501030516 82
    0x300401400c04101921013505075400380c0c03062a002c000780901e003210300c0d40201e40e68250440d110360810010400540c0e0300140300000c0d10340c00c2c030f200b40d41c1c0d03140c0100050703462003107600003042c13408041500e0003400700c10360000c55000d000760700303603080c5039540b903c1291100801c1c09036141010412511080c294072640540350300010f0300d41003603d000e40310174160929400840c5c0d009a0141c80d541c4c40030200090a419100400c0f0a013080f03c100e2080307580d00d130094050741c000c0c030302184180c61040038240d6a0720000c480f2150003400303401c400901e9080003805507021854040c0402c0c01d29001c2100c01c4441001c55102c654444071001000c40d6611400021016164240c0e0451080c140441030b40d075120302c187d8008081c40c1c0c0040c40341141001c1407001c03030204d0360321043c14001041d0318000903803804102000e0b000c0c031240c07110b94110100c0184c4501103d03903030540b54000c104501c801125640084101809944a0f002c45281c10b03581c000441c140c560880e5105000e444031a03000c2d8165000c1c610104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 87348966 1250 87347716 87347719
    0x307080a0e031204050a050106060203090d03050d09120504150f0e0103090201022e05090d17072606011e0e15070203150f0916060f0c061104060e030c1c02 68
    0xf441c02c2d019185003a4005001d80e0250b0303054209101c03143c10031a09100d410018112400603505000c1c604000411800401d94090240000000c3d01101c040495001c42e6000e68030108501049803e02402030240d0054001c94880f920f00c00b216002a9000f40c07030b401001d400c4d65032440d000e0510500110080e0012000407415886040c0003039801d03000f2007243c0c0b1450f504040c1803840910640c00082c00341e81e000340c554480d6421400c0610400c5034007030018400d0401c142580b803640d0729100400c48200e031841c04880010000d5001443c001d10314500d031107001e400241e030b5003803071240d04201c504001189070034603601040c4050043c10550500c108a81200c0c1316000c146401e01d03901c0e80109003037604040d200880c04d4a00020040e445482e4594607070440d00d20350040403811480703038802d0040034040c0102801d00030056101a886441a1244005642d001c10140303c580410314681e4102d400c035001b440c0204540c0d59144140d03007000200116614401041c02c5a112902e95210090416480702603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 87350216 1250 87348966 87348973
    0x6020f1207020d030b090105031203090f060114090108010c080a05070306030f0501050610050408060103080f07060e011b1b120e10081603050c030609070504051002070f0b0307080a0e 80
    0x40c29503100c5664818481d18254019001902e151440102200e40744600300f84541c07414001404140c900140b441c0440c0070750300c003c2d0303a6915141d05240c988005c00c2854481c42c8180800401c40c4580b5241ca01d004040942c0c21842c16604c2c1c845c0e403401c1e43d1620b0201c0000441100001d00c09039030940041e50040b5050400281264803511002c044000b080815600360303450b141440300320b06000001544499040c0390450806040950440c4c44100611002c0d042c00c501081ca510300800f0741007100d0741b95500140400940800c6d0741c8a0340a0455105074801b2075441c04a000040d03070103840420b100c1902600c11500c203501551f10300c40a130303404800c40003c0051f00400c03400300ea140c00c2c00820384070480d51982d2901d4a840100e000640c0401c3c4200000c0608290a102001c094801601d400040460310021940d42c1c0c0d00003110325000755482543d0200780c2100d40303c0f8654004c11440c0c16505010500490300d920f810b5181d40e903100c251030600020f510000040c28518180c0c0c8031000002006042d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 87351466 1250 87350216 87350227
    0xe161d070f0509010e010e04060905010503061602060a050405010b0603040f12110312090304030c08030c2103060120011a0f0a0303020303010308030406090c0f0612050609180a0c06030b010f03020c030706020f 91
    0x20404592707481c1c004000880c0c0d00c2c0c00601c490710701080010360207442111840c81c21401d2101c020b4481c0805000488019100c001080400400303400840c80f8520140400e9102d21786420000e90449410b03000340c918181510300030440601c650030303450807406c4c1c1400035442c01c40315003000c0b07000b035800811311400b5000600004c0005680c2c8441400100210001151a4000002400d00b8000352801c00d80081c2100020703000120343d22800c3c3c0354010000d00b4540440c003915100140c0344000f100070751010b5460211041d2284005070f45003070003a607041d40d03e80300a58282d024018400020700014015a005100400001c3c0e8020001c3d42e000d8895400410003803a0756448944541c644c1d00714480d40c0d00400c2040c4100e5a02280c0c4411508590500384141e0410001140c0300180241c14811407445400c0c3c081c0d0080010000c2ca06896404401404079584c0c0d404024020088135021034006020b401c3c1103121103100e4026a0240380701c19003d0741c645512030762040000c0d4441d4180b20b1380707000709000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 87352716 1250 87351466 87351469
    0x30601111005070918051003080a0219030809070e0f0c1b03040f05010e01030203131101110316020306070f0813030e130504020111031c0e161d070f0509010e010e 71
    0x480e80a0103094849034604d0f8200284800d04007001500b2065081c64481084100c0b0303030b02c4600c1007c03a80c101800540c0c84041010403814000519030440c1c1c40f8841c48224401c05a000c0c2c14184600c401c1c1c0250380d500b0742c070b42d500440000010340f94403802e1008040404c0b140303070903140140980070710b104400c01c41c0082500c001c0d0540c1c1040d8441c0042100c044020402540c011021303400083d02480d08514614001c1c00c1da42c0010108900a0000c160458403901907902440054103542050411240c9403880c43d1a03240b00102d903403004a000303000707083c0400c00050240318240300c0740381281c13a0040745035545141012480c4102e00c0aa003080030101a000c1c081e101c04d00c9a207441416031001044910b420f00015259149070356190b09c40d68400c0102c10600720f158022049210b000c103101140c0b841f2036142051806400407a039440c480c80d101c000140e00c09000b1102503451181c0e10740c03403489a80b101c2c0c055581d40c100c568a440440e030700700001c5000c0d611680828204002c141002c4201400180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 87353966 1250 87352716 87352721
    0x603050d0302070c060804030507151509020316030510121104060b09030d1409010e13020c060403030b0405070801060e030f010501060c0c0f03050a020118030b04080702040b0111030306011110 84
    0x40c40040800d6001030b0700011300c0111201040504000d0911a20504081da0014118428088083c00300181c80f0301107080030b546030b0404d0201d280300088510055441c3c5102c2d000a50007a502100c00f081000c034249440d60080c0502440740307080c42c10300d200080c645003403802101443c3d502200c210000d120208580d0751644105c1000d01140d28901d0307290700d214000e00d03160402407484038003070002c4000d100c03104820420842c1c400403002e290640014501101003141035031519040c015150003c122110701c0480000d001d88a14003a80c1c060250b41c608505101c21101c0540d02c1c6000205400c006100c00f40c001d04e4042103000c0094129030749445080c200608490003038021000140034000c071002807003040c2c42900040e0182e150b1201006265030b6566031345100100009060109100e480054070b511000050300840d040760958003140380500d0300034020b038010a030882c40385142c1140d8041651003085140d00180300d1400844c60b54890400540d0300c81c030008542036091040740000c0303005a201c1d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 87355216 1250 87353966 87353983
    0x80301290d05060f01021c03021b010608060402010f0504030209040605040f020a14010f02011406270c07140604020310050a02070f0c051014030a090345050d0206030a060305 76
    0x1810300242e02d05203901000080313000c003400c4030b04541c041d00c1402d0b22001d150346011101c41c810300f00160744d07070040302824a0b84445803441c05c041d5460014005001600403800382c2c49940300366110a8603000c281401c2d50b4600440c04061f4000080000040002d00b0641c00150014000c07417101c8a4810b003503001138008241070b00810b002c0e200c04106000c06503089224601d1660003030000340310142d00c482c80e414868800034501403103850070090004000c21b00d52005001701310f481660740d206246c5240490900e81c051070f01140d40420407200310040c0000411414001d980c0140640ba0340d050350401403014150160070b43c9071482e404c1003010300080c4a8201008402d10441c801c115030751901e010232000d280b80b200c88905200344020480d210303903500000c4a512030401c910000f4901c2460508480700920307101180c5a040c543d032414040e68280014504c5081038130f00889008602e82c001904240c5000d100d02508030010080035001483c019010355845114000c0001c0c1d0140d581d1100b40c40c04bc0b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 87356466 1250 87355216 87355237
    0x120f17090c0405010603020702060d0b0d0203030a090f0906050d0308040611070b0603010f020705070e040c03120c14071208090301020c060118060e0f060d150f020a020105100308030129 81
    0x981809059030401d409414010a0903080448c14a2019008140c40780f10703050444c421030f6500c0000413599a24a4940500c05e90040c0840c0d0311404170080150221074680a0261740c082441000a8015418003070401642d002408a0529814076034068542c1100900b04a07011510b95100c0c814912521014105443c01402a03000508020f070a01d8210b4900c544a103885074010400800271407c005411700440e2503950400340250385034105140c401034a60001401501424900c581d52507015803410689801203d4080c80e51050340301c41c40d901d0605114860540c00e000641101180c0c00c80c014245550001d0009880d00c860760b952103041c0304090b082100340044200b03040810805911403400030b0150f05040381d0041c20500f141c82e020910081c201c80c80f646038a540c50040000041c0c0301300740c0f40365518017030103100e12150144001e500190607820040d0f18000c0001c04d13006000c091402241e07000303c0102d10b036034203007510384005d510104082200030000c0144c1818440c00c00000300f62200d00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 87357716 1250 87356466 87356473
    0xb0a051e010813050a0b0a1104060e120f1b0409050f061f03031403070e041d210306010e030307081204150209010f030b12030c0109120804120f1709 65
    0x4003003001412a500190011503002c030403c20a0002a0300040c10316413032a040740051405035203041c000c0e0040c10f07030700c40410317800b00c004100050b80942084851488490480311a21100d003003030092550740051480e079003c5903100c100e0700c1c1d003100ca205410400301c2d803000c5c01c01f081d404d8440e00e44910b403100218403000990720403800c00080141842c03104171f08440c80e040b4400c6051440e00e00812104420350116800b880c0040801e01c0d203400340035003406001c00030b80144450000068115805019880d054100c1d0103003c0c1c2c12154440c0c980c000141100c1d64850140c1035485000c0111401000c0703c101c0e503003600c020480ca001090710360029000d160300e094500d5031540342601d840740c031112945102401150040c03158100c40c0e078104413058034014580c500001c0b56210503002550003040c0c0407014510b80000515080b200300107401c0008664013a01c0303c802c0400700b18604403486c00045601a0980341c2003d410440c03144510442512285545030400800b443c1000c62045c9610039290700c2210360 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 87358966 1250 87357716 87357769
    0x9150307050604030b0106030218131d01021e0906041e140d0f0204050c0904020a030203060a0611060f09070e130c0504061a0708040801020309060406060f06050d0b0a05 74
    0x60100480c038040c01c0107980c800c0c282440d5079141031503d0010b01481c824160007242c40c030000e00307898010040300940203004540701403004651030018803090200700070000d52074440c07000f90b000500840342248181c0c0006d01114020080390f00c02508030703078815684a02c04010000c1d010003005151240e280c1940c20001030540b40140340d0010701415052a40a4012020300c00040b074800d115452075184c064034003241c00c0da00d01c0b080c04603d100c0d111b0169030041c40803c1c1041c100b545640514450082500d01c1c49500c0e8640e2002e641c404400d1100800540c4108005035101424245150700081c1c40c1007115081ea4032020481542d101c2200e41582c0c0010840c2e50506200350b43e2000d10040100359010010b982c2014100036112041129641c0c8a00d0002081001c0040e402c04840060031210021916070604005180c2c9400301514140c890324200400400c00951488544007114000d0301d0707a41c5042c1c4652030401c00390003440c80c03c540c04000c0400015a40e220484a11643c007542c0c0349a56100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87360216 1250 87358966 87358969
    0x2702040e1e0d08102102060f04030c0f03080304080a1b290c18060405031605030d02120a0309030e03100e070e060a0501050903100f06090612020a0e13020915 69
    0x4018a100c003c001c0b0410601c4000c3e00d214000400341c0d14102030004543c85402c0c6000c4034600c1a0070020f4209000082612001500e00701900907644196108200c41350348098244228000740400f50001d40108003180000d4180c0006064007400c07030810160329440c09042040b46031510760305982c000751008102c0750000011030f58105500c41d0903c103241c1420010300168050003a6821140035100c0e4500c80710045e900c2100f41d5000348070050407200c1c540d4100141000051a40c40341078040c0c4100003064840324004200c918901c10010100d504204100104030701400c20800c0c2034003444921104451107032010301c4841c0c00503189030701c0420404812481c01f0f1400707456600c0418600b0f205014894103680b514002c40071600246062500c4910300c00021b0304040c44060068089031400c840506d0440382c0c2c1c0c000004841d148101040321647c3d07100450810904194001d62000c6480d030288540c0d0544d100c880c0d0444055917188540000c04d85c0894801442584c40c818405038002114015 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87361466 1250 87360216 87360223
    0xc0309090a091713030b360c0913060507020a0507051504030b0711061303090b091315090c050301080601060507170d091707020901092702040e1e 64
    0x20940381d4030200034290a0340c0f90190002101d60000720762150004042d40810907a0082d10040c40c1c1180000307829050819810340d10654070551896001030440b0800d41813281c02c1011040810400f029200c176098200802411004c01085040010904842e51001c9440d61203100d109098503001440301c44010304000d8580480d55114a10400d0065240c09100e20403200b55401c13079510103024401034840002c141d50100c071189490120f0320841041240010903c954161414065215681d00684134600341266108a001c1140c1007407285100c0d001c0014145d100e0100098000f1031450030301e0701c0700d40a43c1910030300e03400e280000310084018000c0070ba0a0020301c1c010402410701c5441c0218031395800c00581d455010801071250f0110750104014415003100d450345a11103511004142c815040a0050b040b91034140d0041046030300104040f1624402c2d4a55151910504c00d0318024426107040e038010300410490b08251182101d441e000004c0180302c0500107242d1003d11130340481a0011328 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87362716 1250 87361466 87361471
    0x302090f0f010903020d11030d0f1e0c020d02010e060a030b0f030312040f0c0806070906080601230c0703080c010c120b1f020a0b070305011403010e06010e040c03080c030909 76
    0x42011040800e1010380c2c1c120a904040f05c5c0e0595084171500f841703051486002140c64032140e014015960200b6900b1b0784803070703140011081c6482c1d41130b19a6600f030102d076102c010840e4003000306641c180c003140036203880d0414885003841458544400304800e0086246030f003000f1203040c04a0b44980801807103150040c25000d00c80d00680c019811b03c000c00d04800d040c00300c003400c0a80300504511850090200004c0002c028100b180c1c11100c1350b0800450040c54000940f058100103010503022411540c422561000310f4101c04140e0b00c0b00521017580200035502c24030ba044100d01c1040300010024503280050103100400740b00000f04018484005808600d144c4001d8007800d1501c58505010741c1e42030200c0d43e40032804849004503108150090f85080343d11400600b11000d04001c0152455154005506903014000302d40543d40707800043c035007600c2d281c14404049402500060006d2a1045200b40c0e1240c000d0841e010056903d8444034800e03071200101e4105a000000d0014a07400d01141e80398 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87363966 1250 87362716 87362719
    0x101401150305040221030c0708100f050601080403030c110111070c0b1303060504020f030a050703060606050406020a06200706140c07150b010203190c020a0605040b0f030718060302090f 81
    0x12070b519080d8000384c00b01303800d1740c070074507510540c08450f043c0400104141c0d0300700409413081300c46031500c0e14945565106440c41300340c0c006041c010008100c030003e00420380038181c1a103458281e9200c1d81c0e000d0340a4809200e80310300300000041e8400000070f09010f8a1940e00101d840e0980c0d440c43c3d8109105007031001d0f003006030451070811814400340542d02c1848100c07a00200c1c00030b056222440000c580030080011554103118540c2c04006100d004240c4104407807050b942045015590b0f00e080c3c60a0190344035203030168000b844450080782280c1c01014003041400c0038544e4404005040650341c0c1c000c400180c0c0d440341e803140b081480030040b64215030803c5040400702d00304900b581d6403030b4404580d00701c1d000c2c4298449083d984507900800680d03a69882070598031500450b5840000c0050007480c10981c4202106900000c015019204841c1501c0700100d446207010f0b01c03000700c01c1c034a51018092030100321841c0502c203408040c91404e00040c0a1a07580540d90301900006c004950287c1c00c1800d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87365216 1250 87363966 87363971
    0x11070609230a0902070501060317031f0501050a050904110a120e01060f0b09150d0b010306050405091c0504080706091502070605041503020c010608070509090303040f030806031014011503 82
    0x60816030b03100d6410904407594442c0159503030391a850054050141540003c01c0700c003c902003140708510680c0954406d0b1444000181400540020503143c421248210350100780304104190403d07204100921103001d0190000c0f60000074140c21200c258425804500002c540d140c1040700b2a0090003200006403141c0c000b441020f0400000080b00c0000b4840d01c203038070b5000180700c84243c40b81e40754103100031106007085841d071300c0c0e40a045000e0990a0400307400a071808801099034502803040d54000c1b07600710010000403412103441c84070403003c00e48030414454280400503800d42d040103080c01508140e41e071070001c84e24100c807107941210314503188025504070100c107110f420742c01001d032811103000f03110540d009942141c080e0028070a020f4214859424101d001c00d05c41000240c05049a0382a2030881a5642e200311803500e9010035940185001d903003401c40c00100b4800c035a1140c0040d00101038031652040c0070014811140706502295010700c0c500010003200e100c8410a5081e6004c0e030806 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87366466 1250 87365216 87365279
    0x140609060114010819150603181112190606062d030b0d02130c090501080115080c09041a030c0301020406090b0c0307020d030c0b0a02070302100c11070609 68
    0x118000303110b500c5440c9040084241c005600601d06506003081052006001c0013684026100c03084d407007815005000c0400d00348240500b00c071020801c2c0d62002d52704803022000d0780f90664200801c0e601005122402c5125031140c8880b818010803440007074a11880000540e50b01e4044041c2107a0400c084262091403040345100f610522031911080000c42441c0c00206040b180d000200807100e8054081c1d0031110058405082d102c00364005940100c05880e0240e40c1a41c4800450715058240200c0c070060760024804000c0328098080c55811548c8681805d08105200000c602126140701c178134080f21810a80062003804c0500440000040a0340298542070030103030301815101c250b01c01d120380644002100540c4100a20646214030b034000d04050710000ca0303040c020031151141400b50388270b010b1980440d000880c0c1340b00326101940e143c0c001e801d02901d4030540c48010101c0c0301d4002c0911020049030059540700307000b0032025001d50b88507883d4490500801001401143c1950429440310505 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87367716 1250 87366466 87366479
    0x708041d1e06090712110c060a0f0e0304030f080405130c031a0102030a08130b0c030a150e0f04020f0406080f060f13081303050613050f0a020604090f020f0301031406090601 76
    0x803401ea004a140c20b051261010071800f10000700060040d00d8800761001c5205481d10001088050243c080101c02b400042030960200c012034500d0310b02200396038401c200410010b4441d407203e11019004000050400c2d94500105030100c480d8451900400d9850003428180c42e018070900b049a5140d00802c141c0110000000c0d599100300070694040c0210361b03000030301481d40c407002240c0455000145039401d04001c0401c00b51074005680700000c85050900302d45c0580d150b4400003007240c8914078000500d40f50b28020140543c0050400c0e0780028007410400a2500d50380034602c010b10540300103014122800c80054200200070b044903210203e441d040c09410b48100c50b0513101241c100740d58980c0c88610002c1c50040781542d84c4010002e004a80c10032108545200c5020030890145082d1540c0d000c58050803070b2601100c850003135005c1410301040c01140000d038840841901000c0c401850101d040500301d6064000740d02c1110603800e004d020959000c02400803d400c542c5600040605504102 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87368966 1250 87367716 87367729
    0xc02010801050f03010e1603021018090507030902041e0c0c0b0403050313050a0b01050901080312010b1b03040b1305030a05100908041d090f0705060d020708041d1e06 73
    0x128661240102d05443c8225070390030350155403020b20035411a20302020700c20218050b101d55110a80c4207648c00c0e2200c12604c0d02031000d4101a0035021500c00c0480c0c141180f0800034203029006504059441135044010703101c078811001d41000210704c071030024600078159400d8500c206080c4017000310303030510040018800000903402c181d02d82409500c0f66104040c600e03c0081c60840030f0042d2144452200600c10006840b0b4180c85c41580e510100d80e8a81c180142c0e28807405c444000c043e1010401003005842190241c090700c440001c1c00400300c442a84070502e035820a80104401140009407128402d8202000400404042c1c01406d5215130b503031555a10b90062810f91a121500e13401940b0401c80b2480458000d418020940107414107910075034a1000001c41d0f0041e4036203c0c144c3d00155000300040c0c00c004031400181b0140c0750144400e131800c040c0d0052103046441840c00e22000c203c815240713050405610090b228041e29240c00c1424000d1440500103102c0c4101d154000d121540c0c4410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87370216 1250 87368966 87368969
    0x902070c0b070809061801080714090405041b0905010807060e030d0309060b0402041511030324030111040b070c0f03080f16050106080c040b0405010f05011202040506030115020d0c02010801 83
    0x61201c1a1601828100f01c0854480d06041660291000680c00c5030350341c04c038036040c0c0c0307041c0300781e81700042c65455103420313038501c4402846200500e005015502c980c5c68641c0099034030510985040c40d02917181f52280c1010303500f0b600a9030416072641c0051103401c008006002c0108910301d07007040780d82144000f0030b407184100c450000405845003800300078000307650059220164081c10866890b030ba15041154440400220340e400100300f405503490440e03000050341d02481480442a41d1041d8003081440c12100d00d091041d019502d0742d04140b680c101e010060001405e0380b004481d0348000c14684120304456540001794001410b440a20104601d0000e0315015100380c0b07061076032004112030324800880c1c912402001903081820200308404041400c5902120039601409a50319040400043c1c4200b4003400c200d07034040c00000c00456104000c91191403084c400014a400d40380c00c0854581c4e0300980028402280030310014400d1541000000c1400842c0e103080c00a0240d203500080185070103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87371466 1250 87370216 87370229
    0x20324160306150f020d09030b06010c140a1b0b04060e210f010c110303010e0708071209050a140f0a02060d2d050c04060c1203090b070201090b010902070c 68
    0xd01540d402a5020b5801071024001c520010100807038404070092034030001d00007000c014020342c04862500e40c051100314003a83d511240c0811103aa0f513200444400d0503000042c0c0e00c0011500c10040400c1051143c0000d1500902082c0160a50183c80d50100c10309070340f00c4c1e000204108001c00c601d07640f2032084401c10900712580507201d900e2500c80c6c04038001408081c00280109010040f510005600041d0310302a5911012845074101040c40d4683c0001d100e026510012900010912845903d280381d00a449080c0280308901501c000b0003107550b000002c640d00e0380103003241014020360201103040e00404500074140c540384414510707102ca00c1203a0090203400d02003221115480300380c015000c69a2051403842540b103a81d035040341d61000410f8224911460480403d860550a01c01c84041d60380f03e8451526000c401d0350703202103912020240704105650343c61244d0010766106010780c041d20b556400031424a44900b007110b14041c041c0c4c00b6500c0313288108062030000b0081d0b0020350807582c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87372716 1250 87371466 87371491
    0x10030605040f1208010503010c030b13050c04080a05030702010e0418020d0503040b1201050f1008130809131e0506010903030804050705030102030c0705060c0a08013f020324 76
    0x340d82c50700040d50b1820301002030070101022280381d0f840c1d600c0701c0c0c440d0494a04138024041480b00c0c05041c2c08550346490b01d0740c0c1003102c040c07007940c0910350758121680240d10441c0c4036140c03031303581c901003418081d44000444035038100040d50403c1d582c2c051003500d44050101d50130065400e000e443c0d150b07440d0100d04001e0203014503902d1041882030a2068800602100c6a1556100001c00d600c22105100740a0903210328902e500343c2d061030074050b04ca1594000d280e1503240d184c5d11110403205081ca40410b0881340c04030100300e03228403911906401e100381c50464502180c0b40c05144c4201080107070540003250340602c1e10041001030382c0d0001c0b420040700c0d00f6042040f0795031218240682000500e40007542c0640c00001440507480026009090050040c13042d01c41c15121040c4000c51407003039821a000240b884801070040f91000210b41342e0008500041040300c90443c2882240322518014619200c400908240150b04052088803050360003090b56000010040110050541000d007548020b1007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87373966 1250 87372716 87372721
    0x30b010309080a030b03060f09060612010b0a0905070e1e060703031b0e090c0415030209040e1f0f060b030a090201110307050303011502030a12050606040e0f040201020d020610030605 80
    0x90080d40300008140d00602c00640d2082840d4014016100b07071480c1034000e100b1480002c0740400d40c1072030f031401103207620050105500c940c01001061090400c901801d95070342d00001d4141c0c3c1d5040811002003818076001719643c600688090403050711000b80c6801051045510503443e0300c280900405000e0460303845803196141c2c01c00710020802c083c034143d1045402c05000c0d0754140c011910700210302045403200f500707a90700f500307440082c080d81c4039024202d0691640110070a000390054a101100980001540015803410507e04144850321204100102080352172018060255070100010b440090010900d0700311a00e07a80d102c000d1400e1310300c6694000c40b0085a00c00c0c0013409c0020540001c80c0e44903079845c24266141d80c000e00c543c0c000d8111441c400e02c8070600100a4540101c0c10ba00e81c81d43e400d00803040e0b40040d00f40240b10650220701013101107040c04454090038081c0c0040d0b03000d240741e450148000781c54114403c0701c1d4010340d4460010800441a0088020180c0e50b004c4804035017034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87375216 1250 87373966 87373969
    0x2060f09031602240d02030a0b0a030b16171312020102070f060509160b090109050907020c190503010c09030b0604060302060414030309060f19080c25080f070515060a06030b 76
    0x2840207502544165800145c012501425500510302482c0307100d100704401c0d03142c1c10410210b8070b40e074880204000e03100000600d03862130403c4d410300c03889814146803c0200000461882e0f2090407288010b61105910381c94080c07010340790b030180d1812101d0008514114458851481c42a01038400502c9035459000040c003c02d002d02003825441241500004a50780301d064500d1141c20000003140047c0030700303000142d03514250401c40e02074481030700980340c103103212000d00c082d048500c0b099541c40e0b0907a040004807520240b103140d60f0910159a02100303981503140041c5000009032806203d00e003405024400750b92100100c4c0c045856a800403c0c5019141e40400c3c294010312403201e500c0300000ca01402d5a0703564500608100c403200e4904800481116001d55441c50107888031040d0050174000034103003005d2450006068001c00c00351141c907404540d02c2d880903620400300006200c40205004041181c108003204007841002d1308100d1914011f00800c040805070f1048604160301c900013007549 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87376466 1250 87375216 87375259
    0x30d05040816030804170f0412020316180e030c06180111031510020105040b0a020a18080102040e0109060812091c061d031204030c020a120302060f09031602 69
    0xc0e202c5104482e01106407414050020101240d0580f007520381c00207001e504034090001c6944441d181252541007a040c800a81507211118901701d8140c418102c3d0319594100000d0500014040862405490200c1243c0042505d220f102c4030a0a80c7c001d11107886d415402182d01a807001500e54491480149421a039016041d281d0911001e0344000080c0a2424dc800c22091071414003641c507104101d1052030220700300c1e00111806440009210f0101d034980d02150000c10307180256241ca58500380020b0301540304003210f60300140040e0f5001030204045c00d0b002c00c00900401007101c1c100301803868952555186c41c150001008103420000c0c10307600c5a41c865185160071901c090999a083d2001e01d40400100803c80c242d545031136041200035204200081100c9160910701d5007a05213890388d85d0705444540c1c95400403a40300b80707034040104801900075000302d0354600a500804d114281204009880c203030280804003a604200f001220300c4051110108100d581618010100344200445048 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87377716 1250 87376466 87376477
    0xb0c07020a0b03162721080301080109120206091c03020c0634050d0c02030f0a0503040618020306340203030901060f050904081e220e09030d050408 65
    0x7031080401803043d00513945001800c100030a407030320380c034806000b1011301815102c2c481d915a1008141e4052150410100611a000110060044d614141e541d60150250800d030404080c5a54841081050041c2e24640c6c2c402c07400c1d0f50010382998101281101e45a80516042d80010b0312030f00c0b0350342c64080c4254120f41148602c80300f690410305010040c43c1050a401c00355508d400c81b20003101d20102610300e07600c036282441e511480e01d0903600e070309400041d0207082181c0065010600810011850440c028041c420b0755640d45981c03840e1a140060458212001c000c0c07441901086000050310005400c0313422070007144113a0b683d4480d11449040c50a1034400b0203c3c09050b8924881090f90000042c6015940307500c024040c507900c501e030000500101e8850710303501c1104030020a011505140c020908800e002d6440e40409000b503255480c07642c041804480d40340c12661a8040fa180c6603001d11000d04443d01c85428035042041550350b890060400e000c002c80e9407100031404000d4000100c55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87378966 1250 87377716 87377729
    0xa0807020703020a0605030a0c050f0412170f03040c230103051003020a06171506091c0c03080a08090d0e04110702120303010f08030c0a0303090206120906090f0601030b0c07020a 78
    0x1105e4680c540241190025a08c40c1c24a070b08000c2030340c02d01402001a200d0600080e041c0900305494000c1002c0c1410b00b06005480c068480b029900701008090010160880212001a5281094030700380b000e0040603404900780502d2240800d1035008054424161080309207400724031074451510542c11620180e00081d40403485280025080c0d8004c0d84050305032685000b421039680c0c900c541042c843c0c0b82c142205a00031000c00c100c10142c0307842c02d0b50300c0b112624016002c085084a41d07403642100740079041620300c00404111500550792081d04184e00c0500301d006805032020306e8601401845141e40d005201d5515000f02840388002c80e4103840c1141e8000f0040d5000166820480b0744a070310a005a442030039400101142185e40042124007460b070100041241c04180e03101107004080c1800c04a901c00300030011400d146000000b01405444c041c0d000e41141d041210300e040c80c103c11166020a5500b00000400100d0341c0040451343c400740d0440760550391405440094000c8000748c00c0351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87380216 1250 87378966 87378979
    0x10090e100903030b030d0c050c011103040e01060c0b06040c08040b150402030a02040609050607050307080d0e0307060b03070515070807080c0607031b0c0519030201020c010f050a0f0902060a080702070302 89
    0x201c00b4035a00d60041140b45074203609031108982d464000b120441000000a00303294070010740324902e5441904103244004844007a2400d090705c1c2c5180c0d06200d0401e0380a40b0000b60007035190014040c0c010141a002241201e080180074804c04c40a0400302e00100040c00f40354017500001c1c26900315400000b0400c0340100210b5807031502d44107071802504980038540004050340c0c4080b550313007480d900701c800403174010b40198144020fa5075480348542c45200b080c0801522417642461441c0108003604a0b90f103d00000700d03640480c8014189420050f0340024800c0f07401d00d090180740c6c0c07880800c0b00c0b000c42d041032400341e07070346803a0500d00e22911032040240303240c0c8190380421802c1a4075900c00218030029442401101025040460750080448005400b80d042450300280320b16080c0c0e07a02e03405910a000140c00c01450210050840c0c2982c10318000d0145c0781c0c8200074408585214004480802c5101046910f010341c01280c7e00740900c0d60403100380903003207000c519424020002d070802158001d02e030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87381466 1250 87380216 87380231
    0x6060d1104090b0f060301180b070c140109030206070503060d0308040609020d0f030906020d1205041406160e060a0e1e031c20060c1c050705030907080610090e10 71
    0x6182a0501104c0310360b260410007000c141a4641030054108110400b030740e81e0001481ea465005000798060b12080038821a440c50100059081c4011102c41d03262034000035a200503410082d00341171000b0404420800d080042000f070303039100d252410585802d0f14180c0000e40c0e40d860000014000040e02a40c000058464641007001041c20a01240d01c6941d5140c401961a0400e0f6500c00c02e5100c0c04010035088000d540161865600540e4001e009410400c511300c0c00003140340c18248283c032700c00283c005070584100d025407c800b0151100e20b059540d203140c501c840300700401c540d40d2444c90324031034090524500d003503410b126141c2200e00c40060940f204400b03000c20002220074075844200100c0c1040034070080e40345000703880481100306c00c00548400e6544d01010096540190306030384170811a2841c41c9000b031154070440e8070950594603150364074103180b4480c1e0314121142d801124168000d004020303241e00f592080d142120026500171800200c540c2401e4200090030040b014041d02e030154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87382716 1250 87381466 87381473
    0x150e030f0403050106080f010212040b13020d210c0206040e060d14010209011d0f0603070203160b0f09121e04052205091b0d05010b120304080601150206060d110409 72
    0x101c822036400c10b089882c40207d07416104d0913030140d2001005400c1c511400103001c40c280d4060141c0c084030404168100c0a03040d800150760f02034500c03041e42d9031150308400301e030003041071165190b00b12080d0511101c211000e034001041d0b03124a002d81c1540c060761501041d03058440b81c81ca00181548442c2204440442000c824002e40010905da4002452111450900030904040e0794040303401501c00c4581c10581f20903c01582d10150140046100c100074100c00209160700b45020301d8421610046242408041144880c7e070182040c4269000743c84401205544402101c00412003199100b100c00c0c1005241c400c58043c070781c0019000111040c55040c001c000c1c03518a20640440c8100b00083d45400f01603582d80c02d0545d001c03214100384500614198640250114902c0d03109030b00110b104422180401c0c5411020040312000381e101081c00d00001805109143c09440504440600011400d00007581daa0001e0120707400f9110a20083d402c4c0041e03080c02c042d41443c05031090000302050315 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87383966 1250 87382716 87382721
    0x150a080405060105040516180512010204030203010506030d0f030903020304050901080102030f07020102130308030a06031e0b0a150b0a0314090a150603050c1306080105011206050a0603150e030f04030501 89
    0x80d0120396500607000042501d24040c8a454081c4151310b000213555550864107031030500340803601034108000c03014005010740e600074005821410070b100140c0c0b22840e510600d030030b403400580700b2407003a004024508081e0340d0241d08030000310450b02d40841d560000d414180e0840c0b107507070025900480904004254a030054000354020009005008aa0340d2007031400c030708032302402d10041c5000040040230070104184c40b000d1504441c20841c0002d44950326900d4030407500300c001d1000348131400000d5803424844d0600030783c0c4c1d10007030a1030309220808800b102c241c160140c034000d101c00c010000c500142480e1195000109928140d0f00f485500d04010344515910904040210f940050303661506041240300d02556048a91010042002c0748281c030230400180c100c494610007855440c0b90000c0c150409001d500e0007422007080c411200d10850402070181c480040200d246103080c02030810010306200c14101c1c03500c10030080003a1000710b01440c0780c11840303070f140207000c01c0c040072801005002043d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87385216 1250 87383966 87383971
    0x30b070903030206090a0503030703110d02070609120806060d02220303110c01030e030d0b011403070c060b060306030c01082e05010305070f0203091905030d17010f0302031902150a08 80
    0xf81c08941c41c981d550081c1ca5507810008100600f560020700108480b02c0c06034101144410070550f499080039424034404007260019102030b1003403030f10b9488042c2449000c15400d04a00050301e41070782103180c48800300d40c8604c50008503200c2c0f00e90000b42001d15410101c5001142c0a9407620f41108550701d0600a000800e0350000094070b02540f0510340c880d40c000c3c460342c0d05040100c4050350920240d00340e038500905040d84000c0c14040824901d00c00c6a403200000c5116554a442e0000004018100403048520b000e1443c5d0081e4400c10501440e80d0380001c142100220900c0c20320b4043d034a601404854490004103001481081440540c801c004501c61030142c0e507080c0c0c0d00b007205958100003121503566284031140940c004210384800d9041c1108100028030281710a110503990ba480424a4804540c7c00e4200240e0381205c40039030101e40c59034003801450804e039005181401c503000642c071a42c224624486040b8817040220864540c0015940231484107015503841785400ea80240648404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87386466 1250 87385216 87385223
    0x90c0301050705070f232506030204081f1e200405090103080702060403200a080705030c090a060302040603080c01060806040305071202010f060b07020411091513030b070903 76
    0x920000500d0140b144040c1c0d00ba60780c0200a04080d000c2603150705a07108034026410840200c0c1c0a603d840f8018200300358011308002c51310385186212500b1303000747c40c4626504810101070042004020101000807618600700d08030b0140c42003d00c001000500804007841c4100e8a0394000d0300e0103000c480c060b48540058580c00244500d0030300c100802a0003031089003e182e038000559001480810880c1014103130301d52000c0c159900d0f198581e102c050a100003120502005400b24251501c41c0c2402e881900081c543c0700010b01841d810000066124490071014501800c1e00c80e00060032892190030000c001c5401400800025803241030600c490f45c00701400701340540c05d02030000f031002d40020740c40d407045415940e041d0070b02d8800d070b0321901c468030b03e49510001c41d034a8003907070b503107110307082c85520024030007e80d1342540c807849031041c030040d14039075000d0418802d002e002000c203903112504034003e014612003043d42c1d41d50204103181d484a03c550400b500d0031600d8403c0100c05a0440090f8060b41d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87387716 1250 87386466 87386471
    0xf01090507051801060c1a0a0501142b26041e0b18060903060117010c050f18180a09060509030702010f03020a090305060f10300812090c0301 62
    0x200d0b8000c1c04244409104585180d02d0300500401c10720340f041c044503a50921038610149101304401c3c0c22408480b042d10747e0000d01c1d43d500c00400015294150505114900740d64840d1000d03840d1205c207000c814002c03800c040500c40e00c24148100b00002029016910041c40030002680e0b80300010650740e0818000c00d859403080720000786001880c400e43c03504941c0407100383d514000028402000400780c4480c040d0b0808800d114200203580c05106280c041c20784051804841c0d083c1e070040d5800e40c0c164110301020b03c80d0800c122741d20306501401300c07681c0c0503036010034821884500717000c540503900030703204078213005060403d01c0150001500030b100100e010325030600440c3c4070022515200e1280d810300a0100b03c5d82441e040c0c8642c002d03005007404081c01c1c10004140d50341d949a046c01c20004580c041c410342000000c1000d060215410040503000f44d888250300750440f10680f18408258020250010000201c01d200300001c060444803103c0460303504d0f10160030076078500c99507856100c104d58460350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87388966 1250 87387716 87387719
    0x5040e0108100509120910050c010c020607030b04060e0609040f050607020d0905010503010e1803040f03082107091e050607050d02012702061309180605070c02010512060109080f01090507 82
    0x9000406080101704035104a24014001c400c01c51040080726082040c03000038440c200d0035400038030400d4003a54160b0040c1c44140760046c00102256a4804e01034412807610400340300a0103c0040c1517030000702515040e41325291414200095540c1400040c01c501c44c2800b0803681541c04a1150001e00c2d0b20b0701d8403003020fa11000152400e0000b401411413848401001507021071080009d820034400e0482580d2900752a005540f10340420fa80080c0ca00e01c90008103014a51000120151a0030300607407582c070f4034102120000c0120350319103d01d030303001001c641d00261045128400072006200040119588000b2071400540320b0045e0b680391805075180c4000042c000079170f14600001140c4d129a02e0140d04025402c01c000c50700410310703c40d2818404e00e0b010604007040d10071164005500244420b40c0720551500d00c0503910700904907010420036090580050740c104003619441c450501c0a070003a6a0303401d00403134a0088a510599946c0724180409080c0001075100078019402401501c8a0a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87390216 1250 87388966 87388981
    0xb0d0b071e02060c090d140f0106030213050103020637080105040c0f0509011b020607031106091b0d0f02030d18050103060b0409020307020a06020c0601140102011e050705040e01081005 81
    0x4820489146503008005c0040c80b490303281074081e00b0100e42c450b010100e40e6018119085203801c05415030b00000d40e6550105000b91300c5c04044c0c000d0b0890000c1d0701031105605641c041001c900400d41e082d095110808110400104034084d032a500410031400c050060000100040c0030150a100d8039000b40d260400b0051807c0c407403000c0d40d40f019100e4459a04e80001440111882c4054440001c082d402042c518030040c0e80341030040180d24001d42c0c5011030400c00803483d0b410300c0006803003210b40d9071041c4d0b500b0384100c150500d40e154041044428400e11a41400c20500e12040b00380002d5042c010100d0301a5801d42201d004c540800140b91580b04160321348005404482c0180100d1804800a000c2040480b003a90010760340181144155040260256541030590304050212042c1d50050b200502402c10706110f5441040800d10080c007111010728a400511680c0002c0c4120064495001807003441c0a001110020960b90003015025a0364811554a4030704900c1d050041c5410a40883c20f003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87391466 1250 87390216 87390223
    0x111905031501110a0201050306040e030f03041e0c05010516051c08090a0803010506031018090312110318031c0b15091819020f090301061e0501030b0d0b071e02 70
    0x2140c003c50024410740c14243c005450305e0300014513040d0301c00e854000c29100c6420030f002901c81020341039145a282e08040ca8660207135640f509202070504411540d000114411010480840c0c1b420b080243c1d8400510043c1c010400d0b6070030014040d80700b4000b01c040781800c0d08544504030240340d5200900382d00e5165000d510b07801074450180003501c0c01e00040c0b0941c505000150f81100702c0020803c0300d030b5030700c0c1802c4103000c85000b85048850381d102e101c0014540c00c00d069507556a91390804100d0411195840050390001030299035645c1c00d540500300b034080041046510b2014149201d98140351065103a901a0000e1a840c070300030b6803d030310160446500e101c2500d4903940018404541098410001518400300810711802d4810309a8000740c42d42c4207100500b120540c0d400015640c1c603404045c542541c0c43c942c00b420780043d1071001100009a4203100b10203564091802143c1400c42d00002800f4440e04007025160010f0300f02408000760f007000344000b06070400b500c45001d1240f410f0b4280c2e10b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87392716 1250 87391466 87391487
    0x20a0c15021209040f110301090c030501050a0902070c08061305070e0f040b07020c0d120e0109031709040f0204290c0a0b0405150403080106091a0904111905031501 72
    0x241c1d00404002000ea81d10501420451002400001d00c902c170340d14001007518901d81c1ea030400c002e030020061101440310700801604038407038102480300f9450000840c1d0120700622920300c0840d40880c1d0201000804408e000c0100f40c2c40d8111030307072418000c03a00e000c020315446089031207205415001505d900e040f5461441240400d080d000700380d03129164074a007002d0090100c411270140708400011356880c5481212501c1c0540c0d17a809840c00c1c1080b001c0e0020b0101d402e00e60602490842c02c00011f501401c248840c40410403007107403901d0140012030301501c402c03050b0015050000c41c0104400f00129072807424010700c00108884000051251603462064098640003a040f60510101044408101e1358006100d402144d505c4000d10030050018401907a0460004250f00010400250301004220281c404a441081260641090f0080a10413009858002e1343c6909040d0343c0a41c2090030340e1003801e110f03d01110109100da400805507841100c42c0c03450510a80c42500003035209501010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87393966 1250 87392716 87392759
    0xa06060c0503030601260901050403080702061501110102090a120b0c071a15032506020328031806090510050606030f060f0a080a1e05030a05070303060504020a020a0c 73
    0x10f240d51104001180c01c420b9204000f440d92885040c49034902c445020103510030445400002107600701071a00501130800501410119070100052200c443c0c10003007640d2112409081a54401d500911580d0190080c3c60300c4e150b00c00d40c1480000b40b802030254102000c13910a2685e003485075150b0162480600441d200502040000a040c49158152800580d00040c0e0001c0c40500c104000e80060301d46070440c0000045804284a1106103031640320100001c0c1c1007a002031810003690303076405902428110011006a01c0c641035481c1403500a601000004070090340c0180b00c88100c2c1842000b520100708200d8403442050400d0b04003210074407801d80078035002860301345152140c0d4840240b010000d40038030f0348034540c1c0c15182c0e11540da902c180c00042080e4005014400010f080085242c00403000014104201e101c05200080011048804080c10741c200551248042d0808400403d010780280b80c0192000502c100c1880c0c000400c481c0703507072240340301c2d03e41c454545a0703044040d00700a1000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87395216 1250 87393966 87393973
    0x1202030c0d030b030109150e07050103020a0203160638030304060c0209060103110c07080f03070b063304090c0908190305190507020907080103050c06030405031c050a06060c05 77
    0x1070505200307401c81c40c0180b1004001007400e5040761030301c1c80580c40d00c0b141c40059642d030b4000e404503c0c0082c484040101400d0908608010902d10042c0d00da1081010800e11760700703001500000c22030700754004000310600090150a00d4546400740004240706a50591070801626040043d13103000001c42e42a90941e584182411341c0f1a030030b1040034407014154034140b6855400b0740002c01444800790402e80c00c02d800426103d458103000504040401d1005c84c8107400402c003000108038410152900b002c425922700c0e820b0b0406242c2c148034600540034031812071304092040c1500818010142042d15600d41003000120600e08d01581c9810303440c8554001034001602a14880c00030b018001582c0e40282402c83c039004500705101c0742a0280318902c40400c002080c00300030b500b44400b025502481d2070401845c15411074903001e0303035005000c1d07072688140c50010000b405c1000c20f00c11354281c0780800603140380100801046401410007101d00c200301c94504171000035014403c40881c1d81c0c440d00306018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87396466 1250 87395216 87395233
    0x309090b150307021c0203090a060903021e210303061005090a060f031e020a020606090c1e07060504050c01021920031203041104050c09130b1c0506041202030c 70
    0x7900180c01c01400d82c0c00b540a1180201e0129192180858003032400358081d40d615404042042560001900700008102c00000c0138001600d03480b8048560216030a500408407410400007401c01d03039242240e03d00c24540c2c19074020b0281e0f000001d940100022580c1070110307110000e04440900402e89090b034060118030b42044181d0080b41c0e1410060310b589400702c0e1803c6140b024104810700c4d420034003012070303001034441481da606101c1c2e181c02c01421505803a00d030801c84080c24040c00346d0700c21081207504813482c0061030350100049404996005505101500d42824410344a0301c0c081c9405000d409203800b0340f150506d10440010074554009605000030103880c03959240c0b0441103002c1605449014034100851000390042e41c0300b103101e40314a0100e501c244040c0025903001511503d034a00302480320300131950340d02c0076001c42c0280280c80002c100030b240c00000c0b807184d012400040180e40804008052040100701544650b0048141301889408200120307504c0c4a005600000f64001030403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87397716 1250 87396466 87396499
    0x30c080601110c100215070c080403110301061d040b16020304090e070330030b0a0b030402041b02010f0e03030702190321090302010b0301050903091c0b0c070309090b 73
    0x40600c203000402e401c0314010701000700407550920000154401581c82900c0210740801c0720764045510225074640f21407451b8240d0345440460059020080500032000410f680d0703918254840001000301e400c03008144000c4684030255031a0a543c162160305416000400391604042d400d020480c0940c000c5190500e808010ba00818003001c600d0704500494400001040403144414844040138804807803044880c40d1001c1c016000080281c10304d81070030b4200700c1c02d5540c41d28400445090095580e50396481c1d2000400508108424121300c12903403502c4121150705500a9008010b40e030001c0144010680c0d803e5564007007101c0440c016881814007409021302c45078650203251203401c00c0440c50a010300d070502c4012891440c2580955a95404014150b09004810650405600030001c6040000d003507520303441a481c0c000d00074010401035180c2801c164810003100b90700f16241e01e80a0400304254442035200d10340560014040110100305071241b4880d94440c1c071001400340b03898800c28403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87398966 1250 87397716 87397727
    0x8010b2407020d0506040b06090112020a180207050d0e0a051c060b060c01020c010b10050a0f08090a06090f17040e06010f03090f0c05030607020106080a061505100507050d030c080601 80
    0x28400c9030003152920f0300000007041000054002c030310030b00309001b81e880e00c0c10512100b040e05034010b1801420580154001d41c98040380113080e507030401e07855484552136030f031000007038441c0c41030003071003131003503402810040d40d20040d4034000020468501404565810402401e40c0c00c4078002000030300f01c0304040c000641944d00000e0a40744c01343c0101c0c1881c00744205a400c980200d400540e442c1d464030700c0052a4500080044c003c05440e04146042c0000c40310001c100e030440c031110f0030500060b42d0110312a442c08001003190b50340c0c052418441d0b25400c0c64020351600d54003100722204031040701d61850099080701641c050350b5a00703120b40402c1c5d0ba00d00c01106c0140e5401028001c1c1a80e801003040410301c4440d210000c180036070b0f41071807070700d240c8410305207030001c001c0a4a0031a49030010500200d1008900f0604041e042032001c14001c686c1203040080080c1917001d103500c00d2003c007195194903040070241c45854000d074160748400320055000d50540d08500341c404009290000081c41c1580500b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87400216 1250 87398966 87398977
    0x50112020105040e1b040305030301090f0203040b061909091b05010507051009230a1103030a1d030f0102031303020d021513260706060918080c010f110408010b24 71
    0x5c082c0a40c001c0701c000b2403a203180d8403d42064070103420000c0144036200450040c1300714403035640300441c035500d040c0d21039440002000c0e040c14483c103020a00c01d0303540303a040b00c4028094042044100007244091508a0003682c070082000450030304404001050b40c01881580c480a4002014200030154919040d000f442c151000b1603070440140100e0314004070485140124504200c010843c0208a007400d4191000050700d2078030952040060790f910a60205802c02c000b03810540b02c50364101d10710700080c180b004035000300348103610120410030f1000b1807040c44034007580a5000e071008002d46141c02c076120380510380c503044074040b501d01068a1060035020311115a005029041d000c03100f14084100d00c0303507400aa1507143c40d003c1362807024000c0360300c0b50b1001056102810440c40f02c030200c02c600c1556407480060404240404e4440d0540740c29044483d01001c004010000c10b1012500350324550000d001e0b498066191004101c0c450416000014840b404e40480500c40d40b990001d01d0300c9948039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87401466 1250 87400216 87400231
    0x609060807090306092406030804060e040b040e07061b050d12021201030b180a1e020102071e1518091a0310140c04030b0403050a0306080f060901050112020105040e 72
    0x1100d400101290a03840b526001740c0c41110030b94034080c0101e004001c0603e03100c40c10185c5900e07020f07040000507071110440d01103c9060a21080c441c001100103001001d00000440e00b00c0e04084484090b840042502010f0310400e0b02c569580c0c0c02d00302e00c0003101e0082110003c182c0d80c0038501002c00030740540008214207060007405450300d01041f0541c0c01140f402e9004031224503410303051280d00d404503c240d0307400980503001003001d901c0c1501d96003018041d03604100708541e0300c66107800070b591090005201a0000201e134120510b03100512568080440c8544021015841ca25501c81c80c4501e90300c500c61503c00841601c0d42d4289120754008040303c042e601245a0400303005400b54800380f017034001c01d4060076000501701c141c00110308480c0720010310803810304804202c10b01c00a1408a035442d08a038252500c0354541c1c0c44401c0c10340c020041c40e000440341d44122050b10000f21400102a4828000395000703100d107907603c1c18001c07840a0a0300b00280810011301c0244140c0c140c0c121410340c010003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87402716 1250 87401466 87401477
    0xc0708180d061b020f0c131d1c030515180901022101090605010f020304060513050d0f03030e0f0709090510020310030c1d04150f1503020405010e010609060807 70
    0x59901c0b0811101c40c8159a550720b60050b0700310a5180e01400840364150b1171170040d000400ea41c1e00000d1280c5905650141020754801c0090110b01688000c140d00704410400c07541400500b61400c0a01c02d104d140c00d500081c1040d00191a51060000309801d0120140a41e400510100440459018005c3c5101d0391076509020000981c00c3e454200d02040c0a0854809c0c4294140790045040d90a580c0065042c440c2d4040100ea48a6000003100c040b104a07203072541c0c442900d0f000d01c139a070321034a42c085503100c4402d4010f4024001d620424004039442500c00704030314999044407946035191003186030f0b4141c10540e42081034100b00d8100c0a1403521403019180d00a25101c0d400049800035111405008100101032041014074143c40019103582c801c41d80d0700d1100440c6407000110b0040006061030301900d4500c905011030740040c040d081c0d490b04180709011070341115500034a600c0c401a4800e6003032200000e80c40d030344281d4030341c1601c0303d66981818181c00d01c2001d90300e010029060404105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87403966 1250 87402716 87402739
    0x4050f100e04061d01080102122205060106210902091b0c0a0b04050709052a370305150609011809020301140103020901021b01020106090906050a050c070818 69
    0x340c803481528060444e880011040d855110000c3d04944416004000d4a81c0b0400c00050300f0004040d45591003040380840c2c0385070340170016500221100030741d4014054410b83d800455016008074500050780e10000002650301c0c01d0600d090107542d010203000c0e40101400022401000506422511030501d80c41c0e40751a1180e419426442d01e8121031040d241c038a032030380a002c00c01a081c40341c140240165030b000c0c0900d09000f01c102c810041d5981c6001c0700c1440c001b0025090300f09681c1512a0500c081861042d203206035440f2070784600710880c0c60304a11304100d03410746a05019104d540c1c0550540d103808400362040c1014499641d22031440d850500c0805024030408074814400400a440c0c03160740541c9a52420b11500c07982500e901d5640c1c18180184030703410440e60300040c41d1240d422002e0704602d40280381d100607070040000e42c004440640c10f02403c2001d110445d007000b4002d80c00c19000300b116582c0c2075580300d554050b081005104180821400c07120440c400403200340480b00030300307100340741 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87405216 1250 87403966 87403969
    0x1012050901020909250f09120506010614070302060705030414010f0606030e070e0a0902040209060a02010b1f080a150b0c03070c06140d020306011407110a0e01050d14030904090503030a1104050f100e 87
    0x2208c10740f00407105944404014818a07502c00e50480c1c4680056914504103001903174080d4580100500c02010040040001004d2000880a10380c0040703ca40003040704100e843c2404020b45064080c20000c2810241c640700c0c480b000080190880300183c2a40381151100340032079010f0200703840140d90194084c801107800f643c0e25001050608400d4000280742c0d1030010a0060840c0348080040032070049410090410740c0101c112030b80400c4a6000040400c0c140b24800001d2026810a42032010f010504030009400000140903d41c080d1011101d407543c1c5031021110741030000f0030070003c80c40c24000d00d607680800d41c02443d00100141081d00d401e00c1c010050311104e4000303c00c10f40c0d80e8112514500c3c158200481c004020341030b241c2007640d0340d42c100300104e04040403a500080076001c41030710640b101c860610a4032205480100140450f80e40c070b09280e035403a08151581002940b80c0070142c0000d902c0081210100c890250012096a01101c1040325094280001000740903120315000c480c0e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87406466 1250 87405216 87405239
    0x30c0412050c2d0d0804170a06180b151c030c020d0303230405030f0a0201061a0c07060305010620010209090c041703181012050901020909250f09 64
    0x10f25044a15015080f07160143e10200d40102e030403441d000da40091680000f140d140701c02c0f01c080d1001c2c007a040d200c08081c805118a001d15061002d022645045610640c40c0c0182111000543c02402d1040c180c1d00c030895008008045d032a14154840460072000d0125402000035203c0300f4040d007881c071408a2990007095060f10a0101100025503401e4084244909186d40310075903091210421170510303207aa9a46d5036442074800100000d60040703091a6094400d41103c0d01500c0d80d401e0454680d02c040582c60226042440d0550240c024007002181c1c1c2e40c424841e241c1203940c255915898031400d05a070b6401070080012181d450354003046108119100c4085140c003440c02180c000741c0d80c92414840c41c5000c40d0101444240d03410401c601c01040c2c0c81280107204000046800c4450b80d81e58200c169141c04643c1a00900f003400c00c0c042182c058010341c042c204d0304100380c40303044061f44c0d03920468500304a8030030300c94680c214103014141c4551103040b00701d101c2100d81c14a840300c1e54495688011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87407716 1250 87406466 87406489
    0x30a05030c03091e090c0c010b031c020706300e0d020d0906091d0c040812030402030606010f0215070306080106140a1a180411030a050f010b030c0412050c 68
    0x1015800052407070b000e410010f8662000c048101c0c1a000d03008135910008400f0000a807841d0120040440c004406060a51001c46414401000c50310703001001c0300e051200c0d6860500704000360042c03130000615a80101c50312540610707004a2141392144c0030031b901a00304108528110b07202c0d07840340f0341c0c004107004202e403407001c85464000301030350107000360000c20b20310b104c0c0c2120b0108902c4601c01c0100e403011241d0401080440c02c2079041d03176591404c0b001c40d18010355018005500c0f90143c1c0f4401442e020000b540641e0007981562116612040156001d003415a40140140c0c04149004400d00f02c00c555142c01c00c00364903000c0f5080d642e44505509484058100c2038071841d03400a07003d005d24140b1841d000a2405004102e8120303c0301035000130314018114401e61300312914460342c4580c0d682da44084121148024410785909101d0681c10040108031a1111403c403500300101d044000c00782520300c00e0000c50a20b9203410708065404604140c40315044035248a00705408100760341d00b214080c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87408966 1250 87407716 87407737
    0x10905070e0907050d1109010c0212011523011b0308060a05030d2601050609090903040308040321030905030315010903080403030f02100e0d0c150c050c0d0306050306070e030a0503 79
    0x5455517030320780010085411041041c10b00784404c01030014a81d0300000c20704a02e540440300300c851242d074811032601406004000304400d4460207000b04003440c0c41210318a050180e201d4840d0707940c105034015509408110091803501d2142c4040000203442803000940c000006400010f10700ea440c0082898003801f0401e803070100c0e070f40e42c9150301c50000340e0321461b101540400c5003440d2540341c903001c121130748501c000c2c1c0d90141361080b001403e8103400300215401154000d07545030740e07030340d880c00c100141600514400c0310b50b00812198203803840c2f09009010b80700c3d400101562444e2601d82c1c41e881c1303c00404944038188109450008081203410015000441c040d4869441103081c040c4000d003001d5001d60022081864a07000019028001810820f0101e490801c0350715000c45040c03405516050100f81c81d6030600782400c58001c154030101030004903003410100c4110045201040c1c054403c540038980c1c040c3e02443c001a0b82d64450a8041644800507090360100c9406488250942d449804680c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87410072 1106 87408966 87408977
    0x50c071205270f0102030721090320030105060102210d06031401060906061d0d080c0a0c080d2105180d090509090304050306010905070e0907 62
    0x1d0759400400d59140924000080d81c2202c007200000c0c03041c0c0112480030406100b075000005030307125582c0c04441c600c01000a01c040b405070006c0b03219a4400c20100b4480000072980d107450f0054110445a540040321646100789400e580024101d02c0c11540f06c2c50425113181d40104c08101000300150f0055502c55444200e407026000d00d420140540c021008040409041503100508580034800700b0f12600d6038618081d184601ea60790f0031007801c806801c81e40c1d441d1420070703240c3c10940c1c4503295050a04244014580c40c084040c07034200d0f0484034550b011b004901040200112030041da02d01039244d1401c07864080c2c0101d481e0350301c190909484070081400c06060b00411845d86043c44c045602c2c0822541004003803583e11302ca000c2c0600815000710320b403107001100315020b9030380c05401088540d181144142c000c12005208404104800f418032507640d481200700d6002d40f0156844 = true := by decide +kernel

theorem cover : BRFrame.Cov 87230216 87410072 := by
  have h0 := BRFrame.cov_init 87230216
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87230216 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87230216 ≤ n) (h2 : n < 87410072) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
