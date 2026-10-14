-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1948
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:15:53.098781+00:00
-- url     : https://prove2.me/submissions/5bd2cf45-45eb-4d4f-88fe-53ca7076e5c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 350179856 ≤ n < 350359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 350181106 1250 350179856 350179859
    0xf0304080c130e06060d05161215110324040501090b030d03020301050a17240702070b040e07120b15091c0f03050706022208060f01060801120501061806 67
    0x30b0005041290300803428451070115203c654440203d443c0e500700008840b182092007650501c4e80c9082080400b4041d482011680010590100c0070f4541000c1d00c0755140500c40c0078440c4046044805402e001032029000300000f80444000d50041c0041901c2400013030300022668002c50b0489000760001c48040e55103803005c0000e8941003101d0b4150841c2468198650360400300400d201400b03070710421070b00034883d24500446410502c180c8004044894904800d101d264000009a16064074403401500070544003040505004080b5011780e5500ba0b404501c1e034031031000498030045120052141c0680e10140b080e2180d0365864014880000c00c0a1552280b20f440f0401c42e11000100d501450002d40c1c0c03801800017000312071550860303a051f0501030348448203418450064461049072900c00310950001d408452480501581612703c060111451991080c4100c015000207029800120700399038010070210b80ca281c21450400d10800000c90320351355a600320714440b841c4501040c1c000b134541c1c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 350182356 1250 350181106 350181109
    0x50a030801030636080705121306030204120f020d1a07031401050d0308040510141602010902010801050f01121b110703120503040f0807031d04091a090f0304080c 71
    0x81c1403426000404040c11412181c01010600780300c20f034000c000741001c903013803802c1c410030344150391701240c0201c00d03203042c0d218250b4044010f0344591503403207104811060100340c040c0b10740300b41d409880c444840c01d98800c0840e00c1d07131001000707880d0381281e011141c080c5500000300e844020042c101d407541c003501d02c1c5042000700a415540d0f5034031070000317480c0108010822543c9461045a5003509400d04041d01d443d00d044c01401d000c5074241401145003014450015a07a04050f010311400860a4a100c9a822075408a00fa14000200a8000740c00c010041c0841e10b04850101e00300794050400030607136180d48009200f5a2299448181c0d0030036a07a044a089582003000c411401d140e00f00900005425542c81d0034003807804040040c104103020000501b000303043c04521481039000840603854200b280380003000c0aa864640d60341031580d03555001c6903828a8041c000c640c980c41a90380002170300f01d0446170411a030051210100c0d103d00492120030031403d02c0100042d10300d44025043c1c2c4500e400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 350183606 1250 350182356 350182361
    0x6050301030f3f0e01030b030601030f0309121b0f050d02040b03010b10020a0b0106090e0a0b01050f120411041a06090315070c0c08070b091002010608071511070f120f050a0308010306 80
    0x150403414541400c81500440c1d07002704800341940c1e4008480590612142021940c840031a0040c032000d0045003406002d20600d90503035030f06403000001c0d91450301d4a91007034a030388801c284101a040006150080700510b040c0d00803080248000c0c0c000242000c581000420700300099200d0b1000d40c0103031750a4030900502c40440d0380900780341c3c04e01e20441c46c40e080c24010842002009801480e40d07070844404035a200f58116401c8840008500e6124a940540ca07214a9030a54084031a5601c803403442c41d9900f0315024411018410301181842c44045405006640d40580c0409c0e505010315101040030179600d04d05a40030308096a142e00110b80c451a010b55001c4c0b8541041c140c0c0d60080f001008258140d104580c2c084a0598800c16446540300301640503003a5a0020002c40c0615030020418041010f4104000711042d501c5003801d8047d0118207403560558082d98511004d084420301051010040c00351566105115950003440181c8885080410401045000444000c010030a010190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 350184856 1250 350183606 350183627
    0x307050706051803030f070c0b070306060314070509130f0905010203181209270106112103010e0c0f070b01051002150708090106090e010c0906050301030f3f 69
    0x43c030740460b0045045802e07590340001003e20492141040018420754410b040202c000e070361000034021541007142c0b024019160300d00a07940041d02d00224490300c1c0700c0d03402e903540c050034040c0c444074605040541480590f0030300401a445440c1c4840485444000078491001c2c42d40c05000010f03200d0800d440d00a0340c0c0342d02801c0b01c40d69584100f04c1514000e0591007200c0050504a4081001551080e03884c0ca0711800511130b001b107d01c400c070000a12a400c01c00303030303161031601c1c400340c4108030118800032442e048250300e20070501c901840144074810038000d4203038024004001c0300d81402c288441070015907000c6c00b406c58407400410010425401c0480d00a801d40d00d250014109420400c00034045010008010380d04000c102808594400c07000c2d031103d406003031000000d10250345816110390103000301c0806070002801007000082d10b14480c2c000da0b41a280c0c40706500302c4895058031085040c0d01c40c4000800c21064214155079601f00782111200fa82aa80d00c03c8505c10305441030240080126 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 350186106 1250 350184856 350184871
    0x4090b0f09070e04090317041a1b04090e0f0a08040302010e04020f09040c110d021f0903080c090a090218041b023a021f0c05040b09030111030705070605 67
    0x501d4180704001c0d81040201c000380200b940c0c0010f004119080465400e01502d6034604000d2141003400705015801b84212100b01918140011179181e82c1d031400301e200c0300901c0c0041d40200a11050107915200d4200749500c5201c074040380e0b03001e07001013803260038400300f180c044481075800038080045503003142c00410b42030340440e02142441304803110224648180389009114681d035203030424015006c0d5030303000c407010b0640f0100c0d0002c62001c1c101a41d10f80b2010081d440e01041410b42942c0305515004c1c613403003107074903603500c100d15120426910700e56009040c10380c0c0d2101c1c06440200342007105101805d00303c1d05400e00c5072052200c40c024401220104c64a40a40c0d0f0341e0b0361101140307660002544002c43c0088500d428541c1407000703d03140c050741000100c0030078002c02d04030030700c3c0c0030703800203510091000600181c1180f20072408490b04490100812801007001484100300702c0e001200500b050350760103000032a174540f0200d02d400f41a4800c850b500c1c003058010641c14180141c0344911a03200d0038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 350187356 1250 350186106 350186119
    0x50708060f0108010b060f07020a0308370f1d060a030606081008190f0602070c170705010c170c0d0206011703210c0d020a0f0f0c03090b130b04090b0f 66
    0x45e8030010602611410050706c80034180059200115180c2e010076400840d0006030f40e6480d0141e00c00e4858070100c2d2104d0b5076440111a03140b0401030880d07164114075088540e20340104030b03000d5842c252960204010300362071001d1085402c501646480008002511950b030300090107034200240070302200000343c4124030304144401d040c401200b0020b642105002407880340d0341820054600081035510f4000c0081c0b1343c50000c26540100030801d00840145c039001050b800d200c40302002d44603522420344c4242030000303010000c00c4000c60162801905200709100890386800c4c541c0d103109150154203403400e40181d10800042000c000700c0300512500d00a1500590f10341003441000d914420031035003560f02e01d01b05e800f01050703001d0b54000445095100c0100309646980d1a040e000e080b24646486034404204a1900c00030480d01c54680d581c955581525101044d605040c54483c46401081e0051140c00040c200800e9441c02100139100801240c1000315848140c54240701c0404410101c003402403d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 350188606 1250 350187356 350187371
    0x19030207021f17060d080409020706110c0601061409091501090605070b01171908071e030c06090c08010921050415230301140a0f0b070204050a09050708060f010801 72
    0x394049010358128107104182c56064413036000041c0703884500c1d900105250000100007031f4107582c1c1e401a00656002d10810800102c03001d440c04800c0c8122603c0304410b070007080041c01703042d0084000e104081c501e8052142401c82c1d080215103940f80c03e0b1210809003020020721b0f41990b80c4004a100a0100303403500600b0104660340b58a030120060007024051002d01d84d0300001c0041c100400480c11007080ca00741180d1605042581d45135201240c2a5507089034140c1482200407040c0b00030035000d07030607900c044000400d900c0700c10041800c01001c541496001e0000502c1c4a007d00540030458090203510b8904601d01c0005140350b69540c410600f8406c05000410040300440d8841d000203041e4105072200086440c004481003d0807542080c24100110020a00071203000d403901c00d455003a218520219214107424000a18034070039005050801c1044000504054101d107401c6201c1c0003011a024241d41c2d43e850410307115800640300d5900000030010300b0340042120a0050079544003c00055 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 350189856 1250 350188606 350188669
    0x130306020d1e090507271116030908010e0a2d051605040b030a02150307030f020f04080f06040b01170307020a0b070201081602030427060605090301060602011a151903020702 76
    0x39071180944903642e19610f4910328038699048400d28000044180c014140f10b240140c10aca2042c0a12145580b07010b000d00c0f405200050b50364038445d00010444035891140036080c0440101101d850f8030541c09039848170010b84200703c4144a02160700c0c0c4c00c0351607810b0800f400200c550543d01544240c1c844105140581c5034904252003000750181b58603030780e40d81c5480650180880c0f00c24000f800d407001642020301e000300d0002c0c0042d24607e40c141c411600040340e0081d0349100541d0f0160140441000402c402c13400c0308a00360007040b44d0000d40e0305011090700000e0b048403141e401000300c15070004010b0210740e44526400d0340502800e00d40c1c44282c0a41100943e2806203024064444000c8841010040c080ea182e407114594820401d00032142c503400d00501d03d401100b1064025801c1220110300c06006020340100e13600314030030600250040764208000c18880c107891102c0c0c00010081580881d80442c10003c600143c0d0318090ba44813842e105024103210081040401070b030401010740f409 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 350191106 1250 350189856 350189909
    0xc0806061e0d0605061c0f0b0a0c0f110f0708010501030611030c090f0f030f100c03061404090804030b100807050108060d030305152806020102130306020d1e090507 72
    0x1460740003c8000f850750b80300300c0440c440717490004442501c0410361309001c0401160103a0440b03503501c140780701504c5854070210403098521003681da10104004038640c895a0b489510216050040722003101d100e00354586109090141036004001c1594480d070050041c411030f8095540080c11500441d859894424a40015802504100d0f80728600f0340310700d102169580f072150f0700150001030589401e204444c09199130b82400e1091003002604007142c1921190092040c0c0003203400071515204407200200400c03000304007900b4201c45080c070a2001001043d040c00ca1a8815000200c0c50740b199403e00e0416490140c05a0006040002c00010003000e030b261000c100810329030504002c41c1039112160307000100f143c40c550854101041105140c4286900c0b518071100030340e41c0d41041102900c03050124213078401e80d541040c050000402c1000000c400b603009213191020024006280140c400144015980c84604100b407140c039284117009105090040350000c0c6002c90000c645581850f000c2c00780c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 350192356 1250 350191106 350191129
    0xd0605030c010e0a2d06080f070305220503040806071809050103020114031e1603061a04050d03020c0301050c18010c0309051003020f12010303020f0303040b1605070c0806061e 77
    0x2400c00355607140c180d001c0001c018000c0042d81171100d1800c4644800005240d02c8003107401c0801047e6100205940e64024031606000d0401e02d0000f0001441682154000401e1940211038070b220400c80010810030502c00c55000b807186959000d00081584000001e40c51503800ca2945140380c8401040141c0e00107000c0c0000490022030319403203a803580c0801c000201d11110460700c00f0f044a0411400d0082c4a041c0000c40c0000d0b28100b2005441c1d182c204107105160308003462462041000744101c1c035165012100803886841111a004018000700c0d0942c0d0059428480001001ca00e5032103c42c0707407881052486000386812100c111080d28005c11440d810700c601402403000305054440039100b90100c80c0d5414100030b1269442c4440588601c403407000740700c00d9005000d483c4071140c2140d0041b00b03c0380159042440d007009510b42460240305000c180c0704450030f2200c10801b080029981d616500010708200005d80202e11f00700017400f43e00039510610b641c030000f50502040c001d03131b103070200b142 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 350193606 1250 350192356 350192369
    0x50c190f050f1f0e19061e05011202010302071e0b0406061d150102030903070b040504060e0c0d15150305040302190305180a0f09060302101e140f0d0605030c010e0a 72
    0xf8030322205150207410415800580c07200b00c4100e040905c2031019503040045083d5403030100752076400141c202c440c2201c5080c0510a0180c84450901025620070340203498424028013003034070303071134888520f034000c0c003101441c1103070200742c0c0380104402c0c04014404c2c540241030601d000d92030702400c050701d8503036040700070401c109503424003e030320810703034804c20a541c001d5801074111004d564036141044d042ea0802c3c0f0406100d10300302039000c2040303640040c80707500942c0482c403400d003011520b800030710141002000a2030b2000010500150349608480030341d081e0365241d00d001032981880d0500908000302c041c203003041c407601d95141c0d20000c4e90110403101c03620b0f400c0c120f100c0b00144034000108030b200c8a0340143da0f44c40000f40040f400d1081ca03406039040340c1c4203c0da46042541003020a4071058140800e0b00a0341211071454100c81d0b00030744180c1e544400980f0403d1810807030824818468200b103040b42000c070303507a05040c081401c04100c00d401502090a00c2c01001420900050214040d8007801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 350194856 1250 350193606 350193611
    0x60c0c0f060307230d060602060103020a080c060f160c0311091b160501020405100f0207230415050303031006030605030c0a3003030b010e0406050907050c190f050f1f 73
    0x440d651580d140c142c1700700c2d00569030103108182d95000c00135582c00081c00142e00c9085903403000211540000f0321200c44110181c0741500700030f0000b05a020a411407a8889040e5661407010b0380003c00003401c0c000514490001c08041035031300b0303045c0f124041c4010507840c084804100c40c003002c4440e15007551011200120a04003400f418031300240640169030100350040480d810b4541c8598210800044d0054643c4c21280324a54a00c503441c03c082c0703000419411300e0040300300e00044c0d041a800844a1542d01603e91b0002603440003c42c5ca550710450784001c280e1601e08042c02840e82c540102c0005110480090001d083c4103400140b18070824420310941d1340c0340c2a00d16203940c105015041c69012142100030401c611800c2c0078028040c0c800071180020041c102d141e1581ca424803840043e91405032900c456039540c0c403c181c030190301c140880c9601c0d00c120104864045013404412010310700c00d00d00103810504c1407500700c0c074021154206928a4220320040b1038090014140c000c2c2070450504007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 350196106 1250 350194856 350194907
    0x51c020301020d050c27060d0e010905070303032304080a03181703100608100b0d060f1409090303090a03081302131e0b0904060f0b060c0c0f060307 65
    0x2030091056681e140040c40c04c100c200304004440b0700203803110400c401d900c0480c021406841001001a00003c00e9100d03005120144209502d684601d07a60550b02c000041d56030f040e03846152030551107a00c2240000c0c0c540e10020003501e043c04c00c0480c079039031404040446003081d5840b611a809801c00c600101079444c00c1c8c0c043c2018004445249190300320081200000d1108030070a525801260341a54940e040303400003442500c00c0108d0344c41404249e82c0034111340d08080c558046544440c458012044e00c0b944080f404940581143c2c0041c0b440c5403001034100c003039105001118100902c0c049182c3c0043c010084003c101061302d4030b0b040d5051601510b00e50311004a035501a842e114003039040040701d91900b00c0040079602c0315060f00c00301c4424034010150a0b0400b0282c034186429070350880500c07008180016010b400c041680640c4540100e4254141c1d0041109600040c0811980b544090030f09402401c1030040b50804039000c5e6070051a618081d0006010114005031005650066501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 350197356 1250 350196106 350196109
    0x1c05070302060703170615031b0c190611040f17030f070303020d06171002031504140f011d04020913081815070c0515090306010905041506051c02 64
    0x25200140d80d00404180c0c6900300303820028103000166100300c1d10315442c0000305105d0b16044002c5030141203030210141c59542c031903004000841a0000c0700e8041f110920102050030021300205002c00c0c0e0903043d1500700403160070620117440d20800d0380354181d10100300500803802505040009d58103080307207102404024800c02480d500c22004952084507006c42d5072010940d16800408000d5100a028805540c9407140740708440d803000e001496960040201b02000c0341c2c0394014561088030411034282007005000801c0c1550071081c44450417030040800c00c80c021440c029403901504241d045a2600c4000c0d038040724800320302500c0a4032034101c00e0f00244c0108580151881015031241907d501c078980d5084907810520b1425010340326640541ca9000000c0e0070b0790035107508581008054000d01e1900041c800c802c07a0f01c80c1444400c2e02c0410003000c09441c200441e034000c09114000044a04d040d04050b0341c1503880c0005808002d00f0b00500300400d40d40c5813007488508030400f10020040000c3e10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 350198606 1250 350197356 350197363
    0x7290f0405190b0a0306080c15090d0c030c08070303080f0103050d14070f0b06040c1d0d141f0c0f0e010e0103020c0f0c03060c03041e0201120219090609051c05 70
    0x1e20142d08080e0001c0c1ca41c11985c0d250700000d04a4804a044a212207155010040480c150000c07260f20290103001d00c000500c1c0030b908904906014900038503107603480c0d4071003400021094116580650041e8010020140d03c90649503000030100201712407941903940d07003a29a8080d0170100d0400c485d4240302c94070791990380300f1521070320f83c03150510405c801c581c0382c001c02a5000302c1e4614429031500c4a5207207402e009000c10b544c10b4a042212001c00c2c0d00e51820406844403190381500c2c0c280000702004080d501c00c001440c4801441e1030031107609035004545c03205a50b01220f0750700130440d03103d0311070451b41d8010007440004142401d00094502c41070b00124028043c4c068500d07854801c0b040840c41c1d00d0b03808034003035448000c15020394003556030385001d41e003603448181c1e00284a50304140060204691603645403007a0352051504c00c0142113480343c0b0801707136001b804021b040300e0701c074013082800640c00a0f54240140700600381402d00c03624120005550b01c0c0c0c006601700d0409107001294080006c00d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 350199856 1250 350198606 350198609
    0x7050d1112070302040c0215040f06020f0c03030103020405010506040806040b0c1903090209071701151205150a0e01150503040f061b0305130b01050d0204060807290f040519 76
    0x1d080140002044001c0558803400c9110590040d0310f00b8201e03400d44d0344089164a003064180713012610544460340c5000c99038903280c109880c9554280306950340f100300b0800a118400007400255220350460042200f01c5e00180d0182d40308003420030082190200100c0d005520503000105400c15695151400c451481504401e91800c2140602c58041c81e03090703070044a00a0084c0c032000b0281d620480e06656104100d030032802d0f4420290010020651008588089040c684c034051452a99025281c400e461003030321150720b80850b05d00101c00c1c43c03c100d480f0704020442240051401d524101c41c3c502c80c0c0f00d0b90081030b0100180000040c0a000840c1c0803059101d610041c204010310301802c842036005550605900040d0a000104200300441c0842c1c0311480c0d00200d96903c01e0346490200981082403290803a0446e81307600d4002007900044c8103903030007084c1100404003a202010310079181c0d640b016900c44042c40d4180621041c00148030160fa044d61010740310703050040d581c10400196003840307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 350201106 1250 350199856 350199859
    0x9051011150a020a120e1221040f061a01050a0f17010608180c060a05030601110106080d021204030b0f0403020a150c0e0301050f04020906130222061107050d11 70
    0x30303401801410030080e402070015000c5582e80c045e01180c0050f0032410343d8141503102c0890b522205d036103100419490001d041c840e0600c0c211140340c2a40040081034910103c4007a12030303046e510030003c10b104e910300031008034540403103c0c08080b00013500060b01c01c1c0211550041003010404044920901852070310782840b4412001601940c0e480d035004060210881da0018608424001c044d003030040041c100c460981c3c010811414800342080407540c0c2e4000a00766070401620144220403c42c003803181c036015101c200081d00a40c0f441d140081d00d082040d008a503002d031400c10081000c0b0300303880c10701504081211041c1089496908007245000b03405000541024102ca6241031a40b45a80c072443d00000e0b42c2c2c4510b5802c405030b80c1054200c0700115005030200421800140c01807400410310750348240c000701070030303144000305c104003040fa0854100800b40d0004600e0418008101105900c010012031401411854007a08880d03183d039210b1044c81d001d001040b842c5000c100300e400728200541e60 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 350202356 1250 350201106 350201143
    0x1170601030b0d23060108100506150d0911180a18050d02060405060c0a05090103050601030f020c1615050708090d1a0f0705130303110c04020307050301030605010609051011 76
    0x990401145481e20318044ea16001502811902500d03404504039040750f1021014242d1040300301d00602c040c240080c09194881e01444410303402e0500100940640651824009500c82c09460b119201003490304040d403003440405001c401d24807001d076400e5844580c04a0110b982c003020382d00c40004503e401c01c0206140101c0406a031500c0d0300150503807203940100100c40441d00d4a840c079003914498a948000010300400405006502a401817074000c0380c103240014070415581c1e4800200d8114040d00c0046800400104440300340800c20b0202500e10810346400061215102078514410403030008c0030080b000c1031030802036841045101c01c55401c002849100b406c03065609080c3c0303c04582d1040c0e42c81280011944140c40b40059801c450032400e400301e201821a28190f0b050100300c10301c0442407050708004049a142ca0000e1405203c980d03ca41d40c807541586003000540b1816005402000783c0c3d14810891030f0350f80030f0020350303111450400c0e03109083e1138840c15080006440756142540c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 350203606 1250 350202356 350202379
    0xc03030509030f1c200a0305070302130608040f02100f0305100807030f0809060f1b0106030b06240f09030708060708070e040f0606050c0c370e040c050112020901170601030b 76
    0x40100b0042c810720006d9603040049a8038140141d04031b02500c0c0c5141c0d00f44246440c1400200d004000305504a8002c440303240c005403142c1d0000b60030a40ca0a011400580381e0b28948400a8250159035000720450040d010814200b0b014181e88604a1102900000c00d00690304213000442c000c649414102030b0031160b9134001c0350003140706940000401c034031200d8154045803545c44107205510540e680014590f0f0140c4a007000c0050349505814070045111403810864640f502040083c42400300b000d5007503032108020b00030135051042590140c0c0054000e101081946540800841d50203940d03424030014030309100b0f000c20024065000c281c02c0c2e0601d0003102045860304000135100611204084491003214042484884040c1c1c0a4000c1c12040484502035200420f00449404075584c0c808600c0c415550581c1001c0e800003580e05071000eaa250205100c1c0b9603001c0d80000040050b40419031825041c903000820032040514068025040d034008a07200381c4c031a0300001c0f25420010700028601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 350204856 1250 350203606 350203661
    0x1030819050c0319090b031003020f040b0406030609030807300209061204151e02030a09050d0503040201090b0307210b0414011e03051e0118030c03030509030f1c 71
    0x7084c18440c0c001285903482c00150068848003228440c503280402018075178655424401c0120156541c1035100d03403201006801ca464520030032000358005c00c404034601d05282030240c850380303010300408100070f80407008038444c00c03201c0d207840510b8501d000c1801c41a020200010b0003030040381c00d415444840058202d01c01c544201002d80203c0c0078002c80741d40e001450843c0e000716034180c0b60188186500750304601c260b654560256520110200c0007058465542d074840703080c00d0005101a01166020081c0821740d40e0000c50030703016001800c456071075810700001c086c1c411454252800030b0403111038202e038032216040e042601600f501800601000b1103044072018946424010303a4a2092176018a14003c42c2040b4010100c982182c080e00c1b207016110010907c41400b00c0a8440540d2216210170203001d92400f41c43d04580251303a030305820007a9142c02419a00050690300060344140541c185018451003151075103116a5900d0303102e040c17800d0301036016140e603208401c45400c5c10620081c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 350206106 1250 350204856 350204887
    0x30915030e01060b0a0c110d080307050d0c170f07030e0d0e0102010b030a0201050909040501020405060415020c120c010f0210050a0c0f0f0507060e0f012f0301030819050c03 76
    0x7100400e0000380483d03034440c1c0440303106020ba0703104200051101d60181c0d010845040c044144000c1c0030340b00b44910300031034544115030f0b40184c1350705001940c0080e5900290003a0b05c01c481611000b803805ca54040e4035000018851075000d0211480341c0810008664610f004e54411043d4142000982d200d030b0f000d402000e006900d400c0c14107405942484a0400a442d011412581465058481a003418016800d011000c2d000800484682d9170070031010540c1e0340d0310750107000100101140b0846251013410000d00f0071041400721806691451512100d240c004244804080000e00e041c180d851802c2504910300340b42e40782c401d02d04914040034000001401d40090175a421951161200480042c008440301001210307000b00284041c00242e000400c1900440c03440403400b0120f514005052030744900310b4403d01c500254419190301507241002c81c03803015110084c10152000d0456140d5110000103106100101019450a4052150185c02103068800c0c468155080700e44810002511244 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 350207356 1250 350206106 350206121
    0x10902030601080c01090b04180506032109040b0306130206090604050d0b04060e06010b07110402070602030703090c0f0b070b0603010608030a0809060a09050a06092306041703060102030a0c03091503 87
    0x703144d00c0b1b02150301c6000c0310884046600d4030b60140039070b0043c019488020b102c040c0840d940350203405030a210b441c0b8000b80082c03010b01c0c000e0420b55601140010442241c1c0c1940300300f030181d080300080024106400306400491030701556a940d5a0340004009100d6118a802c000c4c3d00540b00341102e014025072000c9140300384c1c0320b90810002003281d03440131a503840d02441100045c19040001c0301c0040d065000c0128400d20180001d401c14505540380000c1e41c03c111540700001c0d07a40d4400c40140b06e400c0c80b03e08002c02c038000c41d0682c2c0d2420242c42d84010701c245100a4500035640340441c9140c0c600358080c0000b0003190080d2034944002c0308004280031030a0302c61811034071588011544800451050300c112030b500c0f00051005522661324240500301c080e400780c803071546280c011040d810301543c0d0968101c0c9000041d22052800b442c01c0b42010308030114040c100002441001031590f00042100e02c012890305014845c9085450708980b02007941e0000c403012010a0728601046030035400c20741 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 350208606 1250 350207356 350207359
    0x3071d0904061e110301231f020102040306050a0c02010c0e100e030f07060f03060f0b0720060406170c1201030803090a051006060f020a030906231303020a06081b0a02010902030601080c 81
    0x30b5140d0204911440d148100c44807d94007000004190004018445200c02c507a4001e0001500341581c03a240c0c08100c2d403085600c0b29426403a4130484010725420b01c02d09010411608080e02c0401042000c1038200b0b04507035641c414042170072466800ba81d002c010300c0180d03040e01000c40342d5464940c10300901a88100302d4007404681007000206405520000310002d841e00b903041c650802441d610368108030340030f01c403840c42151900c6c3d04200d01070b01d1f40b40c02840a01500c2d01c0f045408000480d004c50110f100070b0070804618000d000b031420070111b640c012070449400c2043c05441e901c8a08056003040d01c41003000300284100f148044a8090a030082c0d000c45c2e89603150800c115032040f40070f030707102c28031510002c0001c1c00720307030080c44000d000301683c4000030004000d0301d0025800c404c108009030710030745444c804008000d80130401c52403d20360040243c145441e29241a003480d00351190141102c0c95481d40c041c0c0d002c184c10823001c0c0701b50b0003490903507001170446140e942d40d809419210050707040000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 350209856 1250 350208606 350208629
    0x18030e09012414070f0c050a080105100b0a1b1a010504051e130507031506050d0c21081206090c0726090303030c03071d0904061e110301 60
    0x50382c80c080c1d251910304105401d22081c2e482024401101c1d48103401c20068180c42e4103000481c00b090303021a40d1036040384200700e142e00135810319082103283ea00592126009078105030400403c03040101ca0082117440861800c4e40300c0d6030840c07041d5009001c044142c1454856081020107011201d01c030200d5001154651001d5a40ca031402c1c001980e601326082c80e000c4036000c0c0801d04402420b0082503200008080444007481a969005d00b0891581d0054aa0340c807880076480b0980c204d803060741c009150032205400b2102d5299180600e840c0c10b03100d207275a25034000301e54031040d182c114500e402c0c095101055656814540380c0081454105070307072960040b07007401e00040d0641420030171280466003184440500c0001c0043c1c5920b03c005c41c895403a4015014046144181c07800c00c0914040c4c0c054145003903d901d04094018081e001010307000c058102070f80020581615503510a5811035009034000c40c01d00e107a072040003a0401c4a0410850032443c3c41801e100c2c1014071405103060f01e0000700396 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 350211106 1250 350209856 350209859
    0x71412060a020d0605092a0d0614090a05280204050607050a1209120605060a08060f070807020a0b01030b060301060b040603090308010b0723010f0204090912020601210618030e0901 79
    0x18000c0c1d00e1400c0b540303500340042c14410b8142c0720303507c3c07040c9980082c407041c0303400c0c6090308201140e015501150300414944221810000c0246084d0280c15800020504108500d02c3e0034640f07442c0309103860011044050079061503a12250164044901070080500078544d18116442e21954800401c00c080c0c3d01808050444082c0c9449505003004540350340c0c2d004c9007000000d4442200800000e00940e071703c050040000140c0960034010b0b40c0c4180740d03005031900c0c5171a200001070000103001f4034560454000c4a6a500000c83da92000b505403034210003111115681c9401107030041c0b842c0d40002d0707008200450000b5685038135403c00c0c207085109a4411f8400d0341e0b58023101003613020302c00f001000036045813554150401c00c0c0c006190b0080800c000400c05a02200244003264002e801100244d5110f50701d40d8203106141c0f0b54510040c2c4248004c140175072624003059074016550858500c03400120851030b0034400250031000d40b1410b1011140d800292620700501030341c014603806801080035200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 350212356 1250 350211106 350211109
    0x50d06080a0c18421e0906050108070e2103130b0c150c1303050705010e1c030324080c1f020d0305040305070803040c03060518071412060a020d0605 65
    0xd2541c0c04510440481c1e000d81c1136408204004916202c0c0382e00038100f804141003035200000101008040d1281c80500e01d1507514281d008800c015040020081d06100040040c1e0764030101c9641d00c102a4940281006c02d0080040c00d06e031104030940008581d13041180400c014017100401c4401050100e003503440d07a4071100c1c24558064004052501e070806000d1582411889040c00e1717203d008181040c1c50510107030a515601c100c0c0d0380080d113040c0d003d0310090016580000101070510021180090382e5004210140708415150800a0426403141c083c21082810070072031004641d04102e0700c203d41c60711810116a1070f44624140c500c1140ca40440344819a07881005d42e0085550360b000e8506d00052840503000b51802901c110204407040114002040704400554007a40c40390702e410303002a246044c02800d40f08054040207000c0c9240a5a48510000040041c00c41e000c1da54101e4256845200007000e1440400c45480e4138002ca1701000036115441d030041040e00d100700b40030403841d41c41e0310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 350213606 1250 350212356 350212361
    0x10050a140d0f05071724150c0d0302040f090b1c1e14070b03040c060f0e0d060e06010509011211060904020a020f1005040b0106030207060e030a02070e0906070f050d06080a0c18 77
    0x30311940c00181d401e0b0340b441b41e81055003940070f26080000c649440c044210000a00d410b00aa940c140002c7c1c0c04103041c00194014200d480041250b0788050007504100700004440103c11a183e090240101c0303428402c02c04c01c00e8004540180139500b0081038081400c1081000400303080c8103445018010011881c02d0340c5030107032401140c210030075411302230400f202510300c059443c001c04188080294801465640c958403289400c1c4111000b090000318070012501d04a41078200301e22411512005008403c8101c001418198000781840c2001800b84085800ca00c95081600c1d041400003e6810a0030340000d41e40c038518443c1c2c411568403564002d000011610165030007081245c01400401905110781c001e000d00074080c100000303050f081c00c1c21003851984190100300241e0019a02003100c0510541c0071903000ca80c3c100585541d1414a90040214144248407000c0c440049803555039203c5a030301501c00740192104641d82c244203401d100420802c1c612a07400f100385041e0105150208a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 350214856 1250 350213606 350213641
    0x30703020d0c03111e1c2a02040614120c0901090e0309040e0708010605060f070602072f0f01020c0108010612091b0510050a140d0f050717 61
    0x16405400740340e0311100112001c559101d029010404000000038010784240700c0c40f503450b0b0600030400c0710406801c18890034000c8004106100c0140c1c400010b0b420741c2c0025854090440488000c15080000001021400746c008006900103250840210390395403c000c01c041d801104484c091501e800007502241d944a54080c01600003443c000108005202600100e0202c210755041c0e070b00b0308002c00c2c007181c22603a8001e01541d8a920004042140242c280f03d40c00c003801e4152120f910b001c40e4070449012501c82d00800800c1c590b80080c3d26414002c204244000c0d07994404d80c8003142c0241005400c111012a51610744a01e103070304034000803136000040d4a00c15240c1a103924250780e00e4484241c03100c4003c4d90a1881140e11548005c0024040741a03107450030a00940104c1028185000e06c5800400c481c0c040082c06001c0014440d030642090105c0c22010038041025901c00003800140003412480e4a404142d60070103092003030301a004200010350701301006004a182c0d07500708030070483c3d1072079 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 350216106 1250 350214856 350214863
    0xc1803120d02030705040b03040605180a03021e070503120a121a01120209030312011802030910021303120f030e031c0b0619090303030e060609060103180b071106090307 74
    0x2040381e040320203095005540e001d803280c100582041d54916034583c103a0300031035003240c0c50b590741e02c00c2010912aa00b660144240850f0007401c1000f06550060340e80e51003080d11040080c8100e1401d4034bc11801c210a801400d000341c02d40350300f290210300c090b110781c00040e840800b156039a541416507907610302c0b40d800e40464607040301188120240041d1070f5500104a81113503aa02080b21540c10386003080103002c1c9204844209079a980342528000a00b0104821340c40c500b0b00410038046070690000321036a11880c05800142d40d00e59000803902241300070360004160700020401019202d401526283c4502034036141403201501301103e031622032180c03d02081020700e2040c24810010039940c044001c03944041e058903d4840003001040d11207210b10750010004083c1c40c13050082603854001c3c801d5082a0b500101124100103000070240900104401e040583e40c25441031b121100085031180c0c0e94102ca4080c101d400c0441c8010301d030448804085802e48581e001081c0031940c00030494410a41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 350217356 1250 350216106 350216143
    0x7030f03270803060109210c08060c071e0b0a050105130e07060c020a080f0105010515031b030601030f110c0d11070909020a03171c09030905011202120c1803 69
    0xc9641c0c800ca0503030801380c10a0304005400c080840c014451081862000c40807403e01079209215140803100228150081078180d04a501400003d40464003500c20781a03003c1003102a441a803d8080916041000c010700310041460031300c094144a544001d0585209844422000da41c1c0203c900c03c3d15140e0000012560005108210051049880d1800c0d10f1004003044a0680e82c1c0f504c562411480c40742a000d01d03550354004001c11314004000680d0103130004042c90440c0b80c0340d040c0443c1103002841c042042c140010000701c483c4c0c4a940030007081a01a0420000d10300d0f0281c0b4040680c01c040d14180503407040080041c00345000c0d0700d02444121403800100141ea0600d003404000c0c01d4120f0703040782c10a50030400800010501d100890183c02d000748000d403610401d009418004402101c490000340c6481e20b200042070380404600c0030364500703080002d40c00c850380c00703100020702c80c2ca09000705070507160040c800043d03562001800c0314450445008800e0410008258030795074200b00300c184661 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 350218606 1250 350217356 350217431
    0x60306030715030204031b0503011416080402011403100e06010207080606060705032104150212070f1b050703050105070801060912031b03051c20030901090807030f03 73
    0x282d410740345061144600d000340c2050368070741d2803001901c8241c60032072040c240d03c4024000380c04d01348074408044400e0102806141807140709023654a501440c0d842c20404014002402e69005281082c96484003001c044d80e070f40f808080d0600301c140e040c01411342034180500400c5540d0710008004080d243c03210054515500d0ba8010003c1681c4890300464007400180711221040040341c1004406801d0780903445940c0ca05440c00400c2c01c8403003107580f107a0910501c0001410303208414180e0780000d990034903080b10000c211003914094130170002400c5811180c0618020010007040c2081200d105170020301c030b151155442966148003d004060006022a030204041c10071002020360f814000d0030000c0300a91502c902e06403158040710160081040040d840441541c0004d802460000f403040c00c0050045010b0008900031004184407640c01002c0041008803c083d4000113481b0740c441031050b40e8440034178018258903100f55910001ca880d05d10104640c14502035520042c0c1c03a80d00d4482c0044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 350219856 1250 350218606 350218619
    0x15021c0e0d150203010f0e0a1413020112021606050a020301080d051b03030a020703020c03010605031b0301020c060a05040507120506070327050f210412081606060e060603060307 78
    0xc8070390100540b80e030760641c075000784030460900c010340c041c0540d40c60880116003401c1d4192005000078124924643c0f901c070690200702d40c101c0720140c2000d2040320300032030100240012203480590419150040e88001034541c0b14000301e80b40a08102c0c810042071007a5a62a89107000302d000c01d1040c142d094000a0504066902c18402081e0180807a04075001009012600703502d190800c581c000a4030b58001101010b0507010850781c180b014040f00248030b8076090002190b1101600c0d01c50200c032001e4003842072401e40e42901500c0107444075004449861070700500d400d014042c1914281c0300c03406203860202d29460a00180300d05150408000c260f079845000040f0014140c07030b0103016980c0e000f003804041822000c0c0303520700c045001c0c40c000c0901141d81c103440c0f404c0400e80310f40c0b84440321000840e44001c1002005903000c0382d101c05051510034626040a900510030303001080400241040c3c40c40800c1700f103901040540e01c0404407103965035564030510030a4072080e1519603050344101c60030403d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 350221106 1250 350219856 350219869
    0x91905030d020906120106030b01090803070c0644060d0804030b040f05150103050d090e060d021203030c0408162301091503021e04061704060902090115021c0e 70
    0xb0f100054249031500010b0f03016001e1001d02070b000000000c0d2074a034200307400c0d0790000c1c0580161036810050f620306800c56846d01030319040c42c031070801400043c134003400c0f62111120350900301071209584481480c0c0b8103808411106604220071a100d0008000718186041c42400400d00c264003504661070641592544040d4540040040700c0c0921851b490200107207050103120707210b45083c0484055541140740076400c08038079401140800c0f10610040003171903522482690404002e44e04122016260b00208001d100395105d885604d100000c24800b4080c0700800900843c0e041c3c00c00e8071080070303e001c0702d075040d121181709118a00b4a1251546102859112803c41e4804141050751000769200e00f1011885291840900407941c046040c04443e0070001003000480c0021001c0d0f80303407508137840584954203140c040d1040305000000242000f000e0340c8140b0302103400608401466940c0e80031007030b00c00c00311081c140c014055840c4c4d02d80011000f101e00c40300035145403140400c40d040e1034148503e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 350222356 1250 350221106 350221117
    0xc080702150406030516050c070515120708160203030c0435010c1d031c050c0615031b0a14040617030a08010e07020a080901120f05091905030d02 64
    0x3403114401008034000d074003541c002c00003001d003610007117128940192080e90383d14680401500b4848100704061480700d020030400c2c1501d804403480076003129501501840d6004450302e5030a903c01131b00c28045200d070409207680c803862140340c8540401000803000c80c3c0f00e010641e41c44162802c107001c01e10034008600c4081c00c003500b0001c80829074400c0c1810107840c442c0c165103625a00e0359191035544d001540a800021a9410f00c8154440400e640011940d11825108024162980444040e980321722850845121400300000c940c61400c0208040005074040710318036100707200c0c81c4d496600e03880080c117102c17a80c01c40c010440365840c1c2c0382c400d2020030307801c1144100e64010f54604011a1170302560643c076062442c507100441c0c031100782c6d01c405402c48206030411513400480c01300700803074103900290550107168014036417522503081c4001130340c0070710031550005403160814040815183c1c80ea40024440c41641d4101c601e42a014044148030355002c9002911a40003007103607842d1021150001c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 350223606 1250 350222356 350222359
    0xa09090c2303070603020306120105010311120f0601150807032009060717040311011106040305090d021008091608070e040c05090a02090a062105100b040303020c040509010c0c080702 80
    0x40030300340c100002418000c2681081d80480c6e4040107009960030030030303142902c034017842008000c00c1d4107689805c044003104610491040d40b004149007407181d028084403141c00407604c1101d0403940c44d4610168540351550600001030b0b100360005c5c817601d1080c02401c9140807104441e1100b030080c240003070000c1d844440c06a402c02d004100f000c0015140320100860202c0c0440b40c90307156406d520b040d202d0898110500c40c1000320f80c13401d65659a102250f82c60700039600d41000c6030344103554404240e500840c0301d0081d501903181030442c440340790010344603442400340406445c0303c1b00340701801c1409080c2074010303001d1541c008202840b18000c2c1910315900540500350003404c05075240c00242c501d000c120351102200ea008104080d0074101000300902400d481d003068210041d025012032404564884140c0b07406d0348410100b080716848000d10b4025042c24480036a4481d20b03820065500c07c5140d201d10f008518000014800600c18410129081d000d540e50162046072502c2d00301154100e1081607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 350224856 1250 350223606 350223659
    0xc162004331a040504140c040b0d110705030306120706022d01061e050f06032d07020f15010b0403080307050c010f051f03080906210a0b0a09090c 64
    0x1c10310010000101044684142ca1150f44508000501042da80c041c1340604206550f00c06124580c040801079600341c0301043c18060726400910000c2c0050f004c5074461703d0200f4000200340c4240000807008611505081c1d5006003510307844200c0315541c403860b125210058000c082a0101030080c0c4000c911810158401d10fa0700c1000060f1540c02c41d00b2540c010346413183c01c2e50b400341c16010500400001031408070f54540071200d02d90040b501a100080c4000152040e90400303000c01d6502020b95403503008000c0c06802d1910b41084003030352750511821311080b140b241804062011401d111068180c9544408160900b491517036003e071150070140c20103040c0301040c441001d0f000390900c14107145a40d02070001c6224144886000e4902d807482c54401000c2050f1001400455010400c03110007007402c0e2882691a600780751382c0002c0506407210108100f001000b0700100b12030070340004032907a43c111685101569100481c1c800c4078031040000b04090241c09081144c06c0c191200810402e080e071495 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 350226106 1250 350224856 350224859
    0x9020715050106110d0503060306040f05010e1b0a050d08180a0b030f0103030e010c1109061306030503090117040f0f02060705010518240a02030c16200433 68
    0x40c0016907400b60000c41c0040c00203d04403040020800140716280401d050881c6141814004a51504e00c01440902055205c107040c030308111007540300e40c1d9070032548001c1e14080d488212aa00140450b000380621420306550041520324001100c1d0b40580e40c00f20a652900c900c01f01d529014001d21031803660b000108000000f04044240011842402c0c040c80c1c2200035030440c034000e8184180c1e2104141000210050907000940342d0542c01d10b41103085072082c0442e510800007800a00c0f17410002c20429041c000004100701001000d4000b412003622510984040030032458030003182141d01401c24074280c1482008100030004114a103030010b0f1405107008040e03202c80c0e081d51015141001c512618030036408a04006010004540e51010403000d21000c3c21441c0058011020340780d80c03a455400000700388a098540111201d400504820082e0401507041c03030030008501e903120291860541070b9000c514606840b8400b4081c204481e00180540420003010a01c0c074203401030412107255010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 350227356 1250 350226106 350226143
    0xf05040f0e0907030c1203030c09050f24041211010e011205090c090c13050a0b12060a120804030b0705030c0703030c1103041512090305030f09070302041107031d0901090207 76
    0x4018102c0742c0c0d110546001c1e07d10f001821550010303c0c0600b0445030182c2840903603175420520f83d0b20b040403240b20780c0000e060021598028107007517071100510700c0050000780300c10424180548143c010098112806407400040d0340c140302074006280003544100d041d50f41404964080c43c1c015604000b01e590b400d1640020500505059540720125500425121402c48060600b0300c041c1c101610b144140703074500440c0a446000e22680403082103140f500240c820f03218041000001d11900c190701a003071000d800c0000096125020589200c8803120000c1c0509010700210b030700810f007541c2441d28250315510708030300030724604002c2c2003041000740800710f42d40303020400303800504035550383d0100510300c15901030041d0340c020000c0c410490800300080d0100360094281c0b81d10280d0041c940000b03648a5038640d017071444907000258007600d800c100c90541c180490240c8001c40c0300313864009903181321001d1501001c02021030540d0109403100180103e020980141c0305407481019540f40c0710383d0804 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 350228606 1250 350227356 350227373
    0x50d020c07030c332a060e0609030405060412050a0213020a09080c0a1a1e030106092301120209090108030d11040e01050f21010c0f05040f0e090703 65
    0x42c010790391003d00314401e00400366003490000c486800400f00c0c0400181d156420a41c4141d1140c0c01c00920440340079540c1600c0c03c40d50f0380d900307140065102c1900fa000034a0998002e0840d40e040c68040d1043d00d00207401440004104c400b6190b000382480c0c01c01c0d1a14500361022540003000700c0700f80c01401e188800503240c5403242100118800d074050b03141c041d0b40e031001b05407140e20703402107040350322404164000d070711107040c00030654400c0707840700002400042e10a94107100300ca11090081d00361140d02d40c0c030a041e480146058902d00e45e45d0a40c540c1d03980d0420749424000d040e14003902d040c2c0c0c001a40c4a5070040f46001d800602200e009410300f195080080d5100000340c1c0540410740000541c2081400240714142d1a510861078407820320741010410000507105010b4103010b814004501000c0d9510307000360341d0701c0b540c13040c00720701d0341034403036440a4083d2260b00c5200700881d2850305c0c20142d940c0128203840035548038401d018030552821408030034620014103c60b00354001d10b4800b10101da101d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 350229856 1250 350228606 350228609
    0x70503190605041802091003021c0303180c06021e060a0c0216030309090c0822050307150e0606271b0307080f0f040c1205010b03010c020d0201050a150303050d020c07 73
    0x1004d5802d680d01203401401004000103042d041b06003107145040c00103175540502c43c40441409058600c2d058031900d0180c0081410800300200700d00d415007003e00304109800075501341c0d2207590030f540a071400d28519005044683d1103011190300a0800104510325580c060914043d0030320485401070459000c3c41140d020760780040d0000349039100b091103003030104d019040c20075075589081195454036540d0f0340c14076012601000b070f03014003d010758400d2203810001c0e03e490a4100440c2e440e03043d0042101001480c0303009003130045029140000d40540f828140310070400c084003000360030041c0d00703076050700302024004c0403500e51005901c0d8813643c01c6e8807840650311640b03454440e5801418000d5005050f414000d0000d115800c8c0c0408000c0003400d81035410048401101040c0030b4448540340480c05400b101c2481c03a09517107000d00f5003003043c4c0c1c0010b0241981c2d240b60000c1013507440f40354015040d240000107014002d00c0c40780041001921903030003019040e858000050402d00118015420300303449 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 350231106 1250 350229856 350229881
    0x60203131415010f08120a09050a0e0603060609040b0112030504080d030203100b0708040608070309140709150317030603160f03030f170a1508070816080607050319060504 75
    0x2004001d044409802c2c1c0900111450408454581040c080d0740f45038500300c0d810043c501094840c841401785210314081c081c02800c0501c140d0315103104030095181151030034801e21814011864504200304401c2c041c0340c0004040305c15a080000003805084402c0049040100070000001c0d00d600902042108160503a00940d81c0e044c4440030b0311050489401620400004000e82c100142802007110304403219400c2c10031087c0e0720440f068004003001032028bc811402c522802d017903403a010465205403080c0c00003c000f9810034004641070a0f0090000409001141286041c601e00d00809903600160003000c4483c00b00b560509681d1128060b0300400c12001d8110050040540244982c00340c400c5030b1510101305420440c0000000e03078094540c01c55140c0d82d142900082280181c00d101410024048070400c940d65100030381d81d000c2c3c40d400342e005070300d0703104000c0b9200c4008600c0fa8000c94856030f460303085441d4011b070074252201480c0c2489041d5610384d80001c0585490040010003000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 350232356 1250 350231106 350231113
    0x60c0a05011107060501150f03050a0f0e010b1918050c071202070513020708090f030c040612150b03030a0e010302120106020c011e1b08040503060112060b0a030f0602031314 76
    0x83c1890803405468040c6c00a0703001c1250761240300015030b408542100001d015240101d0180c03650801c0c1c500420410074030310031050034641403010f00750054000e5044054145c90000c24894001c0d01c100c08240d050007a024030b01004055608941081e03001150802c0003031400600d040b140d680c8078018042c159440703001507040b02c0c00800c0689803201c41c03501001c2c580e0b0000d501d0031174583e030f41920600c00c181216206506d21411002182c4041220050000300a481000781d030380ca40e600e00b003c00650a008444a408800818500344000e01440d4009036001d0000d600b00303541c3c00c80139507151044d400c406040590902c0403001144003914510b0017001c05401410070440c600e000100392507900c158240c0b00e42507034640e1b034420650009055075260100000c2c00100e03210351511484610680e030043d030b0b01d44980c1001140081982c0c2c0b078503808922819003046200c0d000350920940044ca4800500403134044410140407c16076001540d2108990310000080640c03592006490b407880c8159808690 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 350233606 1250 350232356 350232367
    0x412080d05100e0a05040c21060f0b2b02060703031e0209041407020d0e060705100e0f01090c09021c05041b061407020103021e0c0309041b08010302060c0a050111 71
    0x70f981551241c00588041040c032161819440f89a072540d100c5c0702d100c1d61010840341030880c003c10312074003055407a4080d4041c040000740600c10703006040704684107407080c048e0000c4100303100005850742041001d450841c10b2a00c200b80c00301300b19600095815001e041e20740f058802c3e80b9001c00d21000091100040c01a1201152400e000444c0c141951403001e1481c500c0511040d150001010000440c052800400800c03182c40890307a18010f000009007103105580480402a4140c1c00c94181c0e021594101d036922140c1154050076140b8164000d0403580c0c406c40c040c040c01c4031a030000c0c41501e1042182c40701510501e054001141c2d01100c060320040145100e883c0c5020711955030100424a80c589407500b04003071503c80402d807161b448001d060540c000781d114940e20341da031074581820104c41c064a80752034294041c1512a032206401d9889989054003050f4a080c10000030700c071405030341c0c0c0d400126a08581c01e1003448d500800c090341281c0b041c0d44801000032000d000d00d42010600030040d603140c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 350234856 1250 350233606 350233619
    0x1e130603031d0103050f0103020f03030c10141f0b0921060403120b0901120c03050a05030304170c06061315120507050901050d08030406110f130e010b0412080d0510 72
    0x1042c900740441c10142030909000200441c00740146c107403501240c0c0f850744403200000003407962042d484c4074951809544501d103048480b0b54484219240c0d400d80d001d2040d82c070801d0940d40280f4424401c0000003020209004031b000090180082039409412074500503078020441202810f4845002000d6001408100406a01c01c001c03c0b4a041079400034072481203410001411080b050164038081d0384028028410710540c2c480c100c00545d04101968404012400c00c42d0320390b0b0040702c09031520b01c6003980e04038410002000300d40d0071032000d00c058001c6031654030800000c101c1900c44000d56540300c000705030f1183c0051100340300a104100100128170a02e1502170b08040d0039a104da485110710700c0040020b80c542400a0164a6215050302da40360b49038940140140341603100348040030000f2490342c100d0001d0400804c2c180303a80302c14005900d03541d030303403c5820440d0074040c2c400102400e0004011070048042e650805912440c40300b400c005140707042200321401251441c003172101c140c0040280 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 350236106 1250 350234856 350234897
    0x30809040b06090109060e061201080f0c03160e10030516060905040e031204050a05060115030f0e120d060b070305070b09030f0f090102100507030614010801051e13060303 75
    0x102507040d60303564204100700c00080e218000512a03013040c4606408034845903036a410440f0b020402050040b070716961200381c655a03d42601c41d030f10391244998201c17081185000146164500940e8858101d01c1d4284922980c150a011301a4103015a5002d800310000e0820300c01010714003460b00c103d00c1101c1c40d10710010010443d0741e100350b000d03070320b81180c00f00032200100454503e81000c1c001e811030b58485141103890b0854100010300035006400c004201c8c4107480000408030840c668080c011000d941070008104c40811440c0d24140c0c5c4280422400b00f2111030142c5000c40c400900000d40c0b9139684590f900a602c48241100001c8000030101e0410100a00b0b031a0000c0c5110300941c00e20703c40d454054000d2260300c0e45001c4401020612030300b1607200300019071582040c0d0000b07100c0c40c02d00b180050054942401081c0343c010007013000c0011540301d151081d04036000246442030031210703c1c0d46010001c4003110350307503040301c150040681060507074000c91005510036034a0f01303000204004003802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 350237356 1250 350236106 350236121
    0x61407090501030e0705042d050709140d0605130b0408090102010e031c0f061215060801021c15051f080708090307020f030102090a030b040b09030c150709090603080904 74
    0x14181392504559424030000307142c1d4155134007a94001101451244890400e0041880502c2c49100032448006d641e50550800343c0901c03d951142c3e0145c6840341c4c000f5007131000e815821500702d040340301000d01103050354001715003020340082d2010020038603844d0f42d8501c050841c3c0a807091500080da182c03c0d941c1c24424004006001d0b805141004203241d4000034140c1d048112886143d15403103409001501544444001c002100110440b140d9610b00a000061880000d412003807034908000f400020600031a00c03060383c00703540c0c049040881c0072441c00510051031100010400c0d0040841c00d44c440145031800c40004d01a41d01d00011030300001009481c006001c402002000403d002c1035080000980e0120356045a4182c9081c1c08840841d0090059240c0190307c114407440020030b10080c200440d000300c1c0103541c200d1702da98074040000e90b0b91103010303004011640105408001c440080b408550007050500c2c0c808040c0e540c903a4118140c0c0d4154100b40c554000c0020f00f00c10f5890705c0c0c800e422 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 350238606 1250 350237356 350237359
    0x301030203061312140d0606021015080a0b040c030203011e050702070302010c03050a0e09150a0e0c03061905030105070302090118030c06030e010207060204060c0506010e0c03040206090103090614070905 89
    0x142c1040399440b071228130400e041407400d100951020384104442c0d802510501c04240310104122683c918000703540303801c01e0581003130541c030741010a81407811030000202552016070007000c108949036920a031070400100190754410040e103020005035403c1c02561441c01c0307282d0715a44a400c1c41c0020200b280d90280c849419035011340d5007040144d8119609920403601810429119400341d4010784590030410481c6a00c50f10010400680082c010b02c1d1040084007500c1015481e42c9503030012202a0080d5840c10940c5001d2000508a1074000c1c104102e0303600c004051564240e0f00c00c04603080d01c03070684107a804603802003444061560b000d07541066a07030704440f2011942e0715544410340300707813018003d900425403240024000e80d02d0940444507065444801103640b2035a0b00d0005140042210301107505002c2c000c00050a0241400351a0080d2a840310003851a101c590070001d8a5000c800e00b541030688802c0c004000c81c26030b10500e0f1907424a2030b0942c805240034130f4000c01007101a00940e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 350239856 1250 350238606 350238631
    0x50706090206040f05151c0b0613030c061409030615030f03120a0b2403070207050d05060717010b09100903021903030806040c0503180322060801090c0f080a020c0a08030103020306 79
    0x74980c41d041400e4a002802c50500004423035104001003039051280100c14a61200b55030b2001040048990040088038143d0742e452018103403081c1c0c540d000e8411110581c1d407603444135002c182c3d2460801c140742c00b4500d0082c1100e000d804159190742c15600500075401440860500300046030507035005000c20350000326803098604c0c202890070f0480030100c0c0d0214041e14000301c0000c500600810001c1c028140013000c0c00031014491a1541da141000c036048000070b44080c1c0202d0482c10800e002a060759030440c209801c2c03560207001d0100580500030381074100089240c0000141e11412440c0d0000301d00742e01400e04050031400c01034004807014141c5406103160440810a0350ba0200982e908061824100000a1320400300a89076001c0d804098142d56030003440351040107002c820368403c8490584035004240ea030703090140d040b40d6604a80c1c001090b461008000c40c10711511280b6803003601e2160040c01c2c040000c3c01c00786007500204045401f0307240000180251314080010036030012044003603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 350241106 1250 350239856 350239867
    0xc070c180b0d03270906260d0801030305180901120309060e060d0f0204080105070f0f0203130603050603010e0f030409060504110a05070f021003091a0412050706090206040f0515 78
    0x50132450240c0d5003401c0c0c88003c0764600b40c28507140b45040c0c01403041807800e004843c2c8481260140e0340c0100f00c0180410007140d01c0e136840e180041015944100e2985415100742c1c0780d52000d540d5540f15803501d030b004001058403090700342d642c0104207002c1c04030400340c01d00001e090318001e0311030005a0010707428131030705480408907540c50b2001c0320304d000a071034004180000c6080c0e00034083e008030781156000703508110030085130175800080d50401c2d41455544150b040388101003642c40e0300c1148410511603150940500c00e882c0a6008550001e4006e0000140d28001e0780000d400d11490289040d80c0f80c0001a042000e81c0d01070003000c0103402c04071010821140315081000b49889280340900500c540801c1f910103018000c412400d0064014140c420103c88440000f03000b0581c16100b02d44240c910314007400840c4001e0b440c0303881254807800070703492002e00703130703010381e034540142c0750485d40d0b030380c68052910060721070743c016100802c050b0141141d04c50904d001c02085d0360302c4803061105480207110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 350242356 1250 350241106 350241113
    0x702180609100b0901050a03060305101b1d0f030c0306091c030605130c0210110a080109151e0308070809030111120f040303060b07051b0414010506030c070c180b0d 72
    0x2c60744c4030042420021354400703402c0030a45c094a05507001406900400c9002c9850002c990001c0200300351038010b00481d80d1a0a000750b03100e641e01800a001c88080e0240e08400d82007003201201010790040841e0080654100001d1400100701d89400344e940007609080c02c1e401000d06510402c480500b001e00c410350405000c540e925204481034981d1030b07250014414494002c0c010141804003103c010701c1030b81da0703501d14100f10794440716001000400510001030b00801e18490009a1959251515081494481034034550760aa594040d6a4026400300000084400c001008050b12070104036440340c4c0400101821034440d00039800040b44100242d950700035940420b40c0d40a00c42c0c1e1002c00722a201c40c1011401030400c0d402c03003c202000002c0c0502440400a80c80d85580c1c15004190b07084401c4030240701c292801c09060103010b081000041c000f40c0f0700103000d941d121801c0f0443c50305003c2940c490214024083e4402030280c0e000d04029510390a8501400b5104070050303509680050f071325076 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 350243606 1250 350242356 350242379
    0x90302010e0a030516033605060f2208100509060c090901033302220b07060e030d09030c050f010213060818010c030f1404020a031403070218060910 65
    0x2580345160101000c01c080800d4024220215003d190b8507d441520317485512440e143c030380701000455039200c070700800035071481c040d4201c4007807170001c0c080c59041604d00d142c100500d040c61010401515107020010a00d68000c21984c800010445000300b400e0518803140b60400340080d00c100e9890b4020016008103450f40f104d4581102d030b01903100000a46041c522408646c0d140d211101540c0c2e00d04092042c00b0380d241c000d0300c403807825000f841000010280b80c10b002c0010340e1042c4004150144a00d9010030000e03400310282d040310200352494030620190660031560090801c5000c00d125903400014003004001c6141c86841038030007103280c00341c2c21078241002c0401c2d120b54001c1040f05000590502c000d4822035114800c480028000604c541002070045c202c4908100101da2504070072000c18021580c0c000c0c002c13034001d071203070007010f046032200d10100400c1501d200240c80304110600c01a1515410041074060929500081c2e04102082100001c0c025080340b00051301c0c03420a104120561 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 350244856 1250 350243606 350243617
    0x20405060a2006040803090d0f0e04090213060306021905030f06100c0203060a020d150b04121a0f150108040b0c1e0f09010906050a0f081806040303090302010e0a0305 73
    0x1070500420401d803240d51003504441c0228030346070070f009010a100c101320264000d107000c1c81d60042074407114403101404442c10081540c101c800100841c00030b84031414251b0000e40c0e841c2c009441140fa044403030390903c0c10f8034200d92086480310350024807007070a40403100d4107030b40d2040585030081ca58181014a2a1010700152026104041c25000313280194010300c14002c1d040d501a0076140c0920b48500c10000a4014110000700c003801d00312034681071043c00b4441003e03600094006800e06041c8401c0b070305098605401180e002014041180c0d080308003e202902c45c1c07a12154190320340c5003002d6100110304000705524184580641800300141d1098640f50b4000d00d0b6040c0c481d00d454a00e000d16880058449180025000008001c04c2030720300e1b14000c0040c08001c0e00d0b603840113907039042d00f10b0b100e03c141c148a02c0014002070301c0c090f00c503208421498120b40003403e85032000c08003940003820b00600342c0742100841d40d1400d814081680a015003420081c014010f000400881d0301c0180040c03240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 350246106 1250 350244856 350244877
    0x807140315011406190807021606020604061808070c061b020303030402010305061914030d09030503031305010b100201021c020307090e0603010e07030f050709020f040b1b101e02040506 81
    0x50b034880c43c0c0141c94132401c4c1c99900d0034020880b03000700103100b8060441d51080d00e4500c01802048000061040c41c07442c51400c8800302d5008042c80c0d41c5a80b1654005d1903102409801c0380800d07801e00d001320b1119005030840b503000d200c0544860b850814041d01107007000000c940c2003100364a40300c0169a0100a490f84070750217003408901680c0780c000240041682c1c002a044200300ea0318041884800580503a291180c00d03001c03200a03600c8501d09584042da90310006049034010000203001046017900800e44030310036400840e802110302c001443c52125000101c0061394007003204030b40c03540914050b51400c0c0f49101d003117240d402d00c20401082c00c182e82c042c9005500c4000e0205007281c40c00d40c480e00030b14036450b050b12402512442d009035a00c2400d8000d4030584100900401d00005030310803900302040010307150745014507011a24940350008210408144006404808540000c2c00300340342c0815a9100040e122030004101c00d544400d50fa114842e03544140014092603e0304811075071000f25 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 350247356 1250 350246106 350246129
    0x19060504053a0f0f2f1e0a020a03030f0e040614030105070309050d050a05040e0901020405090c0310170f07090209130531080c1c020105040302120a021501080714031501 74
    0x120712100202c2c04002d800242c0c40900c20b050840c0c2c0c000d9000c12050401305465652200301b1540a04407542c48084c208040e60042c0c1d16501040043d016103840908074945051107901c010f4a40001801c954050b40150551443c0380c003214002e103020700c1101c0e07008480b410200904541a1a603980d102080703503039402444800101c000e00903000d44151001000a00c0c442091031074a0780260f4041c0d04544542d031701a0800d900032a281003001c400b941e108010b1400e80c1c01c20710b40b400c10300105445a004031000d4900403400d020040034821700191018042661300946e50313030050024007140c680041441175109140800380700d50350200440e4007900c00ea0240d031203000c00400b038030807000300c401e03584005004060006180c440c0030f2001c2000210762225005440000099120907401d980040702d0080041c1c1220500c40c28062401c805002040d48501c1250310b100c01c2120364030705011080c1c00c4207601d6406403004002904103040e1500505600790080c11100800d007294030782413281805144072462 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 350248606 1250 350247356 350247377
    0x6070806182a0f04031b080c0105030c0f120906090d080a020702180a050703060b040509362d030d09020f042c19060504053a0f0f 57
    0x20a07030240d0b60303862141024401d9488501e1102060076030302c01c0c40211183d40301800701002103198491034004640c94440940a000390010044401394801030036a00c85007003d0201000024084000c6d03c80c10308254985006030601884062810800070300a800310307886111000f2005910064581d00240241c00141e204c5ea0544000764003907802900c82d92880c10581c0400042d0b040507004140186032a813010011151500134110551046000f210b82000645000c5841400c41542c855203180c54021000b03040124800072007100041402a01140d50144000c00e1004940c0d0729002c42070484c80c0300a035807a402040946e500d0303002e42980b08060590341d405810964039211503c80c0c41160003481003008103d000e0702c100410015600d440310b404030031141c80000f1440003560140401c02141004801c1c841d0307a40c1c01d0054540200201d50170b00408200c4035080c4080e00d0307203004401a103075440b6022414510402d504802c00d14200d0100019900404409a002a40001069090b26007840c00b01c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 350249856 1250 350248606 350248651
    0x9050f030a170d15031a0a060f14090604020c2e020d0501170106030c090f0603020301060e0610090317030c12072615060c0708030c0607080618 63
    0x30240140107202032140740320049800c64010110882c41c074104101030710345560344040c121303201c3c00000c1c0f540c0801040449140314614005d640082281c20104619480f2050031558840340e030f102c52100c014044c541501860140403a91384000b00f554214185000f00c0340c1d540e52024200c0c445500d40f440801e0b00716003261050300000c00b10142d2007055561307914200000000f80000d10510341c1071b050710301403010021010700400d0122074201340241c01003030821020304018941c4803484002161307140c4000005031001c5c0269402400680c0700d01e8610714000040c88040c41601c0c809408000d510641400051445851a031903080210401510b0b547c602518945620800e00a100419020010801d00715400f0b501c0c41d02c90301c0c040d9020b24032203000e030451804401040e03504241c204030a8a6a44460515002030016600400304484400b56076103041401d5500404e000f01031900a4000c00a50b20b400c1942107030045019145840100d1540f4400d081d4000050000c4550001c1c004005456 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 350251106 1250 350249856 350249863
    0x50a020f03041512140a0b0303090a0801050103030306080d020714040e0a0f060c030b01140901090f0e0603010513050c040903020f03040801020408010509060408040603020c10020d050406110a09050f03 88
    0x6542100d000c482d5201d807180c00030391404600324a00c400003454031408a41010450181e08841d00115040200c1a10b42001e10b50241244000490301880701f0701021416644d6040c004004001020001a66505504004090380c0f51500f00c03403015404954041d400fa0340c001500c0c811141942c900c0c0300f2400754900000c0c060200c0d003800e840107120b001c60301c205000b482c0c2110701c0c1c101d03c0b408040000d15000e902c103606460000c2d444a0202d09080c0c00c03a14199024402068800c4051400e811804d07203500c00302e014145580c01c00d500c082c0141d0100030290400b40320f0240c0141c401026071400741007568425031385140b008070190240b070300e0380c0400003094000c02000c81d03a0500c100681c2e80351501c42210383e000390405d2203a00401c1d800c290225405000220b0306a000d02e41000c00700d40791030b04140099001e035004040e80c1c8071074803c882459094901a00c00344c442000050808620303810a0b05144003a02c0d841445142c44030070402620010b603420206072000c8400554a0109610b80500000d00707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 350252356 1250 350251106 350251123
    0x101202060a0c03170408270102121c0c0f02120301030c0506070515161b0308072007120201111f0b030c030607021501060e180a0902120c0102070b03040c06050a02 71
    0x45500c4c4030300c140000c000840e4064850751102c001c60045020b8120000c1c103001340c4070904280941c101828000d5001c44020040c135292034000307001d500c50304104003104211060140d20b031001801e1074034100b00c8268144401010685100241400c550540c0c98016641046100e0680304440000c0c03c0d004200c418004072a601c140a080792681c0e1601245d01803421103003110345000107c400700c90f0031034040812040004e06416a507000c2040e40e94060580b6414103036004e08800610441c243d00c03800030300b0041400035040e0094903490702c1030548009000c04624404d561160303000191003c545107268102a14411076032600440c0e8003003901d01003801e0024400409030140180c40c10051410340004010301800380c42032103102c43e83e9a4000481d100455203450a521144071045541001e81840b911900003a10306400144401340d42c8c0080d08180d02005403003070741d8004050400243d03806000b910020042c103002e5600c0c40c40c099a648254900c0e900514060180104d148246140b08220004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 350253606 1250 350252356 350252387
    0xc0209010f0b030c0714070803030130061e09080a171317041a0301050306061206040326041b08010c020a06091a090709060603020a0806040504021207090203101202060a0c03 76
    0x401450b2980e140c40d8038ad900c24011030005800e445a030401268900c0305d06c1d40304107610140d030034107061281d641c900580703281400b42c000c681560b0807400b000640c602c14801044d20907881d503640c80159510141c1070700709448604900141701004c11103406042c28143e1441c940c068840c2e030f000c841c042100400c5022790b4000f59042e54524070120700c0010602c008505075002141100e5442c1d55610420080414103200040305030411004075000038003c12040c0d601e19071604041c142516182c0303910744101c034200c5054502c2d8030b2000e4890400341c00c060403d03001d082c11700d0081c85a1220b940e0701940d15490b501000b001c450b03440e9007400501c000403417000303840741c4100c040038a141020390484d5075558144c00303082c5059140500029210340079200322030441ea41500c80d0200b640d05c40e010040108001001641c0107240444288000700042c00050701805400d940143c5904240814081d070384419008035680340c0801403820090faa6400c00e640c038080651400502c00303900343c54211021580ea60350f03003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 350254856 1250 350253606 350253613
    0x10c021003110c07050406051c0f230a021003060f06080903090303160611031005040f060e0a0e0c0307062102220518010f051e09070c0209010f0b030c0714 68
    0x1078030501d40454101c4c03c03510102d405000290300c0718200441443e4041200301034144141d0f10307400007244603120200c0c1a014040240c05190314292120440c5c080540d11306043c3c1002400c54114a001115411910b4513441d04004c10750421000130b41d02841030242c2c07c14807244400141c1800c50410071101c05200140039281c444da1f11820300750101208410480d00130b403c06a840d00961869001d492180e42c581580540c024540340034003008002b01304900960585910300441c2c1104000003260103603035442e400150111907812818100f0b440c0792199842a0030610003044203541c00f05403080400310f5007404a003860b101ca03d45200078404c3d00955545921107c0b1041e5810300040c030030000300c80d020b0340d00c650b8003a900068180303007900900070007084182c503803400c2c455802c10558001d00e602a055400d4580c020712400960b004104031446400191018040340031410034a401c58010502181004c0d00170382015209500b5000040806500b140c000c944030083c1b100040c0301c1010203a9200a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 350256106 1250 350254856 350254867
    0x402040305240a1103011203030f0501060e0a0f0302030a060b1f050414040e1005070309020a0308090f0d0b1f0b07060b0109080307111908030c01020705010c03050402010c02100311 79
    0x1405000640100e4070b000c00031000025141103a10b024082e04003100b880da2030302e1603007048203c17054850000780980406507a070b2103000e5040e0a80c460140a0a05911056519030243e001c02c08100c0d06a04003e800088501c02000103840004185580c0c5034840c402040800d10380d40440c54810390a07d040700c070f510050300c0c4a10351540100050080e20300d01d03540002000b51007801d1006440054041c505240e200038907500e015031043c5e000c036030085183d20b40401d6507540c580018540b24010f4100f0345180030002401e02c02c1e49400f200d91008048141c0b4006601c9016803206549500300070540c5201541402169030091071002161010b400c44000044d04e0720301a0400d01c000740101c010541c08602d030903101042c1944000300b5501420350216180001c0350818050119004a1203000c0305000442200401c080f00140094000100c0d4480016107808031401c2c15401d41c0e44208201d000c2c10301d03003424000580d0b84400e00d0070400b0b4041e10000301020100303101f06c0090481250386e05500001154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 350257356 1250 350256106 350256133
    0x612190c1e090c020a03230f1809010e060d06090501150306020c060a05010b0301090510090923030301050a090b040b120a030f03090f0303053411060906070f1107090b1f021b0402040305 81
    0x603182100102b5200c603c0301c0da80b00c202c01e2000c0b043c02d441e4254007500070000301002503040c4d0080950b0303510800000c00d0045413210344040d4040550070496151303401003401503a000f01003144940c8101d100d4003e0009514200511080b88018020209900d450350002034403220518068002800301d242d040100c1c0310ba40c01c1c1203414200c402144040c0c403900140350614050000282d03810b82e10001c010310384403880e2481c624010504040e4450700a9141c0c4407154036651103282030109075543c00050304041155240041071511002c03a210f0a151800300c7d0307900800d1404080884240e49402c000840f03481d90308070a90520154030500c07150f44444a0f0078401c90542049212210b90b19468080c00b12800b03107112610341c00111140d8003143c2c80f42001440261240313004410310282400c00401078600d070f1030b43c641031031441d4100541141e00d805000070542449250f6402c4601d6a0702c504c06003040411000351514010010340700d400050304107104403039880e40c0c110350041d0791201c203e40c1042d02280 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 350258606 1250 350257356 350257387
    0xc0705090f1501080c0904200310150c0c05090403030b0d08040914240607050604050d140a08011e050405100303080612190c1e090c020a03230f 63
    0x2200c001030b0402e84440394030154001d036a200c0c0141a282c15441c01c10740c1c0035040c0700c01003450942a0061694940c80800ca46c440c2800135030088030034141e4640c04a040c103003c8406032145500007420030000c02c10403070115498243c00000c0e208211042034031034446050490142400f032200e654411103040d403001c00c20000800034421103056503420b00c10b1201c901c1c00c07809401000c5500242e4841c0d0400758000a41464891a8007010001e010a04104854441c54035201c1d04840464240c1c0c0302c01c00361515280c01044c015008040e40c00050320703004c0947c400609400c010300c0713600c81140144110b0318107500e90780f00307400240801501c108250f1500445045003811984400d8011445c0c10011903010304100c4403021050f200d010060454481d4041400d81c0d045019006884c00c080e4500d0200b402c1c220107103040a1f0038824074881e010f1a0500c0079560444811022079070543d0301c82920500040d4101844071018441e884004840c040380761248130851041c2d80c01c0808c0b4180004841702c0031030011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 350259856 1250 350258606 350258611
    0x5040905070c2d230f01020a18081b01030f0207110f0d02180a11030f06010e010323041106040f060801050a0b1b070e010b0418140106050c0705090f 65
    0x6401c06642e1110885060003e10b900715140034801004150110100b0380d01004c1d1249058031a0f004004410707040c910714101403131540307071010594000400040c89540650202042c00c406600008054500144103a440200071890000e0845604079256140c0c001c0d0300607801c400c1c1940c0c083d0765818251419005290004031041d02c1510122030720102410011115200b080e03001d003550315001110001d424020740c0050100c43d0300740e00c4900d24040e07a00e200c3c015600542455103c0121414044005050f0807030032481181010314040c0d01c0981100f0559881044241990078005075407a1800c1088100b0303034200000750800c00000d40020400103040000c01113a03425500c10800da62640d08200c5001e1840c07050400c0e440040c000d49296102c0806510f101c070300c000c0203c40505940f003a030b515584000760f120850b04040414100a04941a0040042e4489131401004030b40c1b6814001c0c0003188060151008000c030100d03404d1804c00d420000d900140000070801522441c1003005a01c00030400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 350261106 1250 350259856 350259863
    0x20a02070b03090706080415140108061302210709063b24030f010c12050402031207051509100608030a02060601030e0304031707110d0b07050a05040905070c 69
    0x304600010303085250401e40b8042d044002c0901260f9241210803178074010042e0040d12502c0000c420401c1007480c84c495902c180d41941510603256160201d080d0400318002c4c0402480000c0801e040016500d9032010204040c0c0d00842c400c0440c148003007a4980680c1d5000884414a0202d022803140180b440d9075101c60001c0d02100c002100d8141b8040300000440b100e5402500850040703000ba6035522241c05021070310182d204841103070103002174540b0308024850202a5503440310749000e9940481c04a000000800d8103000c0c509040c0d0210b65107840700142e180705501c0c041380810401100341316110044e82c1c400742c032206a0402c507519a40310310041c0281d120303072417410301d00080e90140441070368902980c40c0c000e0b003455590000190701905440802083c2030100304804000245a450b000c500600302c40da0717941d04e505061500e41d5505d540c80540500c2103001040c1c00d400038082c030000583c85040e13480c06a4903840e8100c000d03651070089420940d40c01d4201002c1140b107603400303a10010541e02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 350262356 1250 350261106 350261113
    0x8010f0614030a12031805150115090311040b0607080a031e110a11010e010905010603020411040f03030f09031a0601120b0310090503040b1c06050109050f0f0f03030d020a02 76
    0x26404255803901c40c3d160060203841e5403403040c002640280c0c0281c40880070084511650351945d40c80c54100b0780c1c03008400c2d142008050050140c942ca04103500c0c520300450610980c09403d580743c10321038400304806681301c1c540b2b801c10100c10b52035120a0318081d40d88040d4082c1c40b1811700340094040c0c54402c0403000240b03601c00d81c642c11008035004410b4900800851145040c41000c003c58990551520206c019901c0d4041101c08038001d01c40c0720a01400361000181150943c4100700036202008111407035050240802d010310708103048500101d80c0c0c14107200c00001c400302000d681c10550f80c0d1000e0000e4981c100801850781d00b8108a9110ba030302603a41e0501c0450302c50125003160203005020350554810080038100d10a594003003100140513404580c1010b0f0385441c281e59940c13000058180440e007401c0f0459508085000304000780000b42001118581072102040340407892418892080004050504c02521581d032008000c94000e0f0a0301e59681e1600021400f035407206650320010720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 350263606 1250 350262356 350262389
    0x3140c030d0503012102030d0509152107030605130605030f0a051b01200307020a080c0108060915040c080601090611060c1b19060e1b04110408010f06 66
    0x60080703058916010340742c079940c2c10741c1d09044102c0c2e0320030040708449642c085440a01e80150303030704000c41507144020341e40300c6985a4502040c4400d11140b100014001c403014000c0d0150144010411804041101c5030801107985078401240507242d0341d4000780d00300c8c42500010741c1076120b0313810600c1590800e9084492503448110a5580c50700c4c00b242c0542a90415101248040c01c010030000c9050014034104948250702c803035014403200010b0320059143d000180910850a04442140c01040c0d5000500415181d000018007032100040015205843d8880066256070085000c9140359101034420845040c4196000c0c000e844255072440c00718800c500002286072060500007410701d4100054400394a515840395041e81140702c402c104001e01160300301002c41c0800480c0d005072004090f80d008111181002422a20300f00c0082e06681c1200340d00590001e104800006524030513140011b0103c0c0c0010040d9450059402000c425402e0000c40c403100b411a401c854180c88a100d222400c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 350264856 1250 350263606 350263609
    0x2030105041a0f0f0301020c010f0506010e06030f07050f1207090302090a060303140702010e0d080405010305010906150e030304050a0902070506090105040209071b12030c090b09030c090a1503140c 86
    0x1000071180090744458440701d408038070300f0300414040244d41c0180001d410441c1e2a00c681d403e5454802d041206150303a10200b008640e03114242c1c03420107409071101e42c07450901840c0d2020325003008100030242b00b40002e2803040c1125200444814601200f4010014204558028a5540140b000fa445520b04d8000300d0f400d40030a05c01c0c00200ca0f4503450301500c40004224182068020711026814000150300b10002511107900d88402c031441380400c1a542c500b8140094210313081070700114500703460f107402884842c9400488040c6483c031400c1501b0081302c0003000074510701c00e0744c03c4035030400f410000004008036560040c003000b81c8150151740041d564010f8580c00c0355000c9a010794000e0058000c19203190140d0021519095030f24a0441c030030110b500c48522050010f030360748000035914046565002c2d48100c0e840058004203c2840c070b17080e11b2400207031342c0700d0559885a201e000850007140c5424105d50294030f80000702403035800001e40c4c1342002c80006209900c222000e01880c9c0203a23606 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 350266106 1250 350264856 350264891
    0x30c060907050d1b0504060f03140d0c020d0638040e0a0f050a0807080901020f0a020609060a0905130b01080906070909020318060f060a0b0708030703020c100f0203010504 75
    0xb070b42e4028100300000c3c0015250810a08898181103101d10740f8420b0120701c1d9203503030142e4009001f00a246640e050302c0d40c901240b07448003e0807c011940c00150850000301da22960502c44990110b0300d0a154020301d081c294000c0156180340c45407200703202401124011103c0b540000000341c0180d510090f070045c0240419141c03e07038409009504242e0f408000101805070004002d402801240c005000999078020310340c0c00001e054600c0c0324041003101c95580d04000745000e00c3c1c040300152246900300d6000ca0740500403251103d110340300c04992101c1c02c1d8441d0410364000d0500501003203040ca5a0038042c4020b04501c130b1818000b500b2500013034a00b56000561900078602030781c620607960b1410031000f009400c064480c00ea80310200c507850045c035000f008454040c00c011000703a81c2c01c0c10f0410170403205c04c20070390150092032000d1081c0800710740000243c82d804034190034056a9500e440780c0960800d840c58050307150103882c15460610110455028506030703130b0191410800b1010011880ca01d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 350267356 1250 350266106 350266109
    0x130507110102070b070f170c1312021302031918050706110c0118030206030f061306032f030f010207121b060b06090a170c1008070c1a01030302030c060907 68
    0x204414480c04991024407846c809400011140303404000d00c030080c540500d00000540e00704008000114031860004880c1c40c1071002804061110441d5004682c08030b40c0c969030f00d00313542034241e501000203040c0c000b5040c2401140d0040003401c110700725000103203880038500050144d5542c42102c0002c10301f40e0003980700b0300b0828107210041002d407042800455022590850000d14803640510000041e11103801560140d848000d400d003403031400c0070510000b400c2510b000c0c58401d0403c0b00c2000807580c914002e01030075200500d005040d000302c40008050820003002c20381c061081e02c04065090030190701510151b80300d120182101d42e8009401c65039800c031140540e10717040c2070309100e40000710f81b540107020703046018001508001c9040d002a10107180c5910640803014507030b031041130100c0305100503000e401c001c80e05010140e000500c001c1280e10700174202014480317144420130500452400b000c01940e4000c030191303003940c1c50b0314009442e038008030050f41c6280f041e00003041081c43d000c80d1180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 350268606 1250 350267356 350267363
    0x90507020c0307030b1003060203480c0304051507050d020a03080105090403030b090a0906060b030103030c080a120c0309140a0825020d050708060a050907090e030913050711010207 79
    0x43e52070306540791420092806004008007200c1103e000002911a00265101c2c0c06003100e6111052540c886076091190200400a0708041c44141c00700245000c9943c680e0f410034680d445a1202c4414154a245105d5034121584c007480b0030000724220600e59000b806c91034400e800b658421445075030309070b071b9460714400003c2c04504003100501c83ca0420841159000740a0315002c1144070542c2c001c114811416a42013141548400004042c04464040d8400034008a41074519641c51520010310314150b9840090081c070000482202082c420252108140a04207041100c40b00d0084c01500a04204800b2a18010011442c013400e1f003002c42d5a041b070680203203089140240301a090201d00f84190480b210402d42c0d140100701503129a820b60340758920840040510764244031020b0f10b42800100700042c058108400c226a0b6000403400c0310031104e00902c0411741188011320a429405480c44060304011140c680700d00645945d04542d018081d1030700c541d0b00080c0d48400300ca00703038400d001029 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 350269856 1250 350268606 350268613
    0x7020a27062106090209070e01020d05040b07030c080c03030c070c090207030c150905150a05010e091903052803050601020109021c08070503040602010b090114100f0912050601090507020c03 83
    0x42488903980c00c9000b1200384101000100b0016950010b11001e0b0103442800005001c3c007088481540c0403c052401e001c2c0609011f401d2526040e054452403155190040070401d080482c0810000300005941c40d1a5608060782e84074640008640d20702c0e0000c0c00d0641d0380000080b00001c040c0118402c076132446030103580d688204541070b00d480343da80c0c1c0954a08076049564030080320118606100004002030a80c919a01e40c0c180300c0300d24415100c040c0c0000c06641c20000500000c40320001d4009015a40100115448007003230030165000d005058040103142000c0180c43c540c0b1050102218000c007003605c08000c1c60311100012401c80d140d00f18000d4020550f03820b5007504042d081341c0720b4103040c89442c201d032070702e600799036844c0c2160810341c040805031b0b450704000341040c50b0000095014016007880c60700340c100a0f10000d1840500c45a4500070701c43c420818401d0707148901d0a0401420751103450096411452030002d50b268024410002e4451401001c252860700c00706610301402d1005004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 350271106 1250 350269856 350269889
    0x21f020702040c030905031605070b040b030613230c0f03150a0905270109080703091409131506030203030406020708060c030603030a0f182414040b090607020a2706 72
    0x29030381c065408c0e00160790b81e1103219030024241516000400c00743c048840c042c0e0300c2e4200b035014008000300030410340b844142000701101750074443c4800e00c24502c4a0fa41688500d444601c0350400ca07214241c59101e1b1158004104030607101e5016410607103000580d4940c0d14191b451800400b00c031010713034086419281c0c41500e50f11020500b4840090519a030000080251341c40c0d9a041e1a5409803c1c200c1c04200da800302001a14030f0f42d50402d68000c0147d48118940c1f41c231842c000c140112075003008141031b4010341c03180c2034496180d2005000d03580c0034084030390b03882c2c542c500a550b44000d442815030700c0c800d090002e40c10307901440c02e8034050000940114280095440b0540c0d1012071523000340100114442098260062440400d00400c2a0600486643e010885a2840d1080142c1071002d100e1010504404941c0a2040760103c803200350f58107448aa160340000e20300d21403010043c0d800010f0300303c0414016840b0004611000e00501000006803a8030750301000e4a130284950100001800301c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 350272356 1250 350271106 350271127
    0x2010f0e06030a24090608121801200d0513050d15050c0d180b09030a1706130501080706031b050403030e010309080a0201061707030b1303021f020702040c03090503 72
    0x1100721000040384414130018130054101c0d00c2c20b082640074001068a031a400c011800090101c00900d4500e0780003d031820b40c0038198921810304090b080b40c10010070b800400000c803004040002d00e0603400007581d091010700c240c0107180340c01108083c0e0000d04074100c0003d152601c0c5146011280d8030500c000034011440c1984801084000c183d180400c0d4100090303201c00c81d6a00c1030307552062519007841d00040c0141031140781c1d4080107154081c2a4410007001d40020b40241310780c014504100980c0c10075540b0a008510344001600440c5051800c00c00003013204c00000c038121081d00c01d43e683c100300c0d4001c1c040c040e07a084206400c0c180085801040284003091040091403c0c51506040200e0a43e1103665000c036550f000340900350050b55114002e01c0500780e50801600b4000d004401040707914115114514800006010240b402035102100010180240300680f08200000d1020000604014541c00698403c00c4100d10030b504d801c0c02c045c2054000c0c440c121005401c040118280f24082c403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 350273606 1250 350272356 350272361
    0x60406020f161b0501080712050c0904020c061f150e010e1f030b06130605070f2109050301050f0a0c120e010c03050f040b0f070507020301061202010f0e06030a 70
    0x241c205000800308498102000d84122040d0902c0c0f040803800c5400c20a640700041800c010703040f00e41041005010b0050440d4881e00300481d42402c5980000e003500c409059203070074840d0754a200d030418004a118107004102113405840b4002044514580103202581203138101c405000311645414021421040d1078411072501e140b10780d041c10030000301900c1d0340009030740004c01840c1c8403040c10321300307904154164076001d0840e0702032055600d64200b540020411610b403241c0d008060070000d022681c24103101c43c10b00c0514031150000440071290303500140c0660445090b04038400454600c100018880c01c0520500784074184120b402d0005480d0200708501502100000104004160800104c2d2440700d1240d2081d510b444c0000141d00710b1002c00280503164001e01c4955510040300401000c04c0210352925072003182c1554103101c0b5600c410051310f4a00805c1d5010b900340d0b00e820b001060214249910010086c002d803101901c0700030310307841200c0e60305403882e503103400040600200c3d14000454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 350274856 1250 350273606 350273617
    0x7091104091508030f13030213050411240708040b0c01020301150f0207062106061d030703020a060c08130605070b1305071809060e0115080601080d05071a040b0a18020306040602 78
    0x140c6c4011480c42d80c0c1e40000740e0b0301022050002c1b5280e5110244002c10422241c00c00003003030180c1e19420a0203941003119003203004141544a401c030000750444c01c1118000031100075040c010119605e034040296401d000707420901540c0b2200500ca48140c000a020f02441014038480d0b170b00615945040c40d00859a0312a05a480240c404185c5014900714046019901c003820680c0c3d01d03011059189074a5441d0407500484482c0640c00041060015813140802141030f1141410120542d4070f180c0b03000b42e11403180d03046500038420303442004512a5403080048c4102e0740175440c108941e131120484200038440340c0000402c0356025940820041040c030b071103102c0d015044c00300064000c510ba01c1e0761088d654070042ca100ca50b50340e40003480020f041a1062000b40c07007003c0051166604001400345d442c14a02079040a01102141803410013080c8180d1015138021016003807403070300f02441e089c1080d80095440c4110117040c100024100e00c5001b1340c0d8100150000c00400c800d40301c41e11074900a5210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 350276106 1250 350274856 350274877
    0x20d02070203060403030b0a1a0304080f1b0a05061b070b04140106032301050420060d1a0a210f050c0a06050a02010f020f030103021207091104091508030f 68
    0xe024180150741d0074005107100300d0080d2000318120218004100400342070f45c00c441076162201c13941008080303a1605490340994003141a0b40ea03240407125540e41da01461040413042c005201000700d6541003c540e0b00c40301c43c41131044603a140c031284500c0094890803002050175403030901c000c0e004904a0721a00d90010b002d190310b200800d81c00100c25080d21001e0300180d4011000482c620080054042400508400c7d00e00810042c117040d0748001c1c120059541c40d0b01141100284c09810390b503a4030413038260010300c0c201044254840302c0c10608c4000c200410a10580549900003906414282050101c9050310a0000000c20542d04c010180102501c151034603c40c1d4800e40c04241c8520769603e0217004c0640359152a0707800907070001c1c20340316008583c0503414018041004100201340c2640e0540f81e04031407084001400014161808400e64040e2020742d00304014105100e140b44000c00949003940c100f440340305408a002d41d4440c410b48940240c651003000741e00151040d403030281014006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 350277356 1250 350276106 350276111
    0xf08040204090c0b0a021603020d083f06040e0c19090203010609330c030c02040207080301180b0906010f210f060b0c0a03030b060c030c33040308070504180f05011a0d020d 75
    0xc8048480403040d848c02c000030803180070147c1073343c02005a4281a5200700116028003080000c40011603d5801042c0c042d80281200e0041c000071700208901c10000d4a40554219129030f0341700e01c0100103480600c1213080ca08440c0c0519090718003280d1402c901900d60081480300041c08035012110b034654980d085d0b040020090b0904010307566400100402e40c0107010b0140c40794100246440c2140d2440000d402081c0380465020582d1101c00d00a507114000b42400d07144840354180984500540c000d04a801003d80310070421207644540c4949025540503004000d0b29440c3d1420010520036060410030030b0b446481700d000020722a80203003079840340c081c03c16414031102c8100c0510350740102c4a0300381c468201070a090400388030786058100281805804503944049007690720505540604040c0401c034a007000500c09a02030300840e8001d2100b2501c503a00011445408002840404d035421012400e02000041d52845c11030202002e0035400c00440c40c010440b1188402988480e482c42440b070b4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 350278606 1250 350277356 350277397
    0x50612010b0c030c030f0d11040311100e0d0506090d110c09090c130603061107080904110415050c07090b0604060309061103040303020c01110a0f08040204090c0b0a021603020d08 78
    0x8205001810240c075500201d03d4692031003d07084000d544c281c0ba22350365445401d02c02040442e41001c3c00217041d80c0d060766107001d868042241141d5108101c40c1003900150300fa010001040340c0045c0862040007241c01351030350b041e21604111094a80c0008919981c3d00890340144149084030089400100480845480c40080400300d1003001c076240b110a406c0341c1d200b41c20030034000b45020f1007440c40c805428581c40c1c071001380c2c0c44400f41e000c0d842049000b180c0c0c0c0d0b10100c1510340c01804440241080783c4c0744018801030408010701c1d0b54031040004d6014010858001041c1d02d2034000c42c10382c040002c040e1801c150400004400504040707609640305d070f45a4586000201250b0001c6000758026038000d030b506c0c00280010b0342514400540c43c500d2850420070148400e074030400c506c3c0301e0000382c50b1404460703c0c1c0340002009000030480207012081c40e0100042c0410f105c1c0c0040103440442d40a5411322107200083c5150308103036200c00b80d000640c08018200058030702004180b05481a924900c801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 350279856 1250 350278606 350278627
    0x60612060609030f030a02100b06030a0b0d05070906050f030102040e180a150603021008100902070c030503030f06100206010b070b0702011410062c0904031b0c0609050612010b0c03 79
    0x680c4c00031050070b400028442180590511805540c092054414058003414002082d01c5d8031004181810040c0e8071294903110350341c2e50404c40700f0150004210b509250700e48400c0c20080119128480c03240000d0011030841e0305040c02610101d60f0b02c03002c224407642da0001d12650703100d00f007241d00d001c600800c090306001806026800e240009203072400102142584103004545a00081c0c0c1420b10801004015013941d01c05115010342c1c041c08000341c0c4071000380c84c1104040361950001801404080100026024400c18440c0b040c20211500c03204d01606900c1a62141c10a00a03c80b14540030001c04001c81c8088a6584d0400c0c510f200008201c2d20300100c0c080200001c2d1661107400080c90f42c1080003075404074075401014000c00c40c0100b0950400030b20548e04002e101d94a006039400000942418010b07004083c0102400d88000f25040d40c4c1d161007034086030b41c1d0094070003094101d2070208242c02c05500f17aa1641c0700144032200346901b00b03c5840e015822030200c901e4188800c100e40f5030348 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 350281106 1250 350279856 350279863
    0x10090507170f0a0c051017160903050303010b0a0306050a030b0406150e040b100603020c030313030c080f1207030e1b0301112205060a120e100e1f0506061206060903 72
    0x250140103000c04d00c506000401c45464001104807003003050b400c010654110100c0740954020307500b000441c40424100c80300392100d14003503102400d14000030000260f0100b03100000d0200320810b82d804c01566480300f041022807490740c04082e2000c0c40b00400900050895444504030420742001e1003485603540741664510704007100c04039a008020800c2c0a00113803042c24600c09802541029410580201401036980c0401840c61a845140486010a0500608090042c1504520f031290b1b5091840d89038100d1750b00c601000c0710240c0c0703000001910544a4811140c0c80d68a401c0649120400584006140445208a240d041d542c5030101d480a2840c0801000c3c1402003400c9455400c080f05580c080c45e01855000a015500403c052030581d0741c014030310320000000c8100001c168450300801482c102d504558140014507154031004681c0f0009005458405032140c0a8221842d21210708240d8100361104e6401860901c40c0300420180026025030000c40540007605111220b0700185c81c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 350282356 1250 350281106 350281123
    0x509040507110115060c02090606040b0c0a11060708030a09050c0405012601061d100947060d0e0102070c0e07081e09031303050c0310090507170f 64
    0x1141d0350504400042800f80036114134180c80801c038124440c900403001e07200185e030100003480380e0400b0002410650326801601c000c4d148110f0600d440b2a98004904d07a110041c03e010359801302d404482d003503686001d80482d00302e40ea10420150441d101d8a1400000c0c0c02c0c06c0e04201c0c2c80e03020790a006a240c1d1110300c0b070540203144841a03d01c21710b2031055001c0d0000a0080d00505690501c0f0052003684c0c0c0402c1c601c1802204082003a4599036102e00780300000015400281d440d50811108210303101031038110200c1c10210b419620986840b41040c24044111401c04808580c61440300900f2803034118007a0014180892000ca428104130b008503089038000c680c202d51016016405003c80c088810341700368051100d00b8004950304103800315000c00404a06812000441c480006071f00e01001d0044d2404150840161440745440c2c1c606541c54084040d105400b900c584c1c21410900001c0c0d0140780a6150418064224182016002000c902046c0990b1100313101c0e0210061a1050400841e507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 350283606 1250 350282356 350282371
    0xd0e040e100218030f07030201112802090a0203090d050c0703050303190e0708030313030309120206010918081806070c14010e0108090d0e0111010603030207050907050703020a0b060105090405 84
    0x5a5841e442005441010f481014160003a413000e100240e044400143d01c00980e40c0900307080e24001c00302d1031880c0c0b40c0000320911002c041c50710802c2c00c021030512000032110314402c88058110f0750b64010150101d01081300c04142c0d41d0f004124449000340640001c0c11001c04100c1aa8401034881e2070716481e5500680340c0465065444c050141d031500140b040c0d09601e04000054000e25141c1040540d89000c094400b164058400060001b01400b80d030005841e40d078003007030f29a01d4941d41d42c0041e40702c160901c0352840c50713402c1056800c2e115100001030300c0e99903800148103081014880c4034003041103017075002e10303003000d070070040000441c410104000080042591703d00c1000c98800004040450326201c0f1818801d1540510020704000311710f031b20340d80c143d0b4a41b200340c100440c00105c03802144d00c0c8039040594039000001c42031560102b1241d003510f805130f0380380b1300d26110702504544070b01c681c0c10b0241c0180c1041c1000c10001c0c070702c1d1501c160480c03014940103080060754000101200c2041c0c0d03012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 350284856 1250 350283606 350283611
    0xd0804080d0614130605030a03050d0615114b0f0a05010c1b0f0c09021606060510050f03090a1e0303050f060603070c0302010e0109050618060403020d0e040e10 70
    0x30b00e0310b01e0030790b10608480d071071003009024071440c06c408242c0c3c2d04081c140c01414060041404100c00748258031841c010103041c4151116000810005480041341c146032481c41e00486020b4001c10055140100118186025a4142c20a9600c072006c80da9000b1860511000700050014103038038081114851007502d01c400f61030304040314548242103c0712140820244005003410902144001c0118101c1c20340000610141da00c007444c1840000b09250002190a8400300b08000c9042c0004d001201e8030703100f040104551510340007003000d03540903c9503000015904100c00d1118081900207190003920200c12070380703000401c0e40e6403015031080044101054014a0501003410703071600546420001e8480026071f64144038021401c1c40c840241000e050020041e1010304040c0700b503001c508500880700c002c00c24404a0720b481034449500352400142c42c188450000c42070a00841c201c0d0140d640354000f8030789a00c1c3d508041e2001c5050140450f400b566805410321038060520041c0212410b18000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 350286106 1250 350284856 350284889
    0x80d020d0801080604060b04091703060a08030909070315031203020a03060e07140f2205011e0c020f0f100206100602160b030a0908070b190b030d0804080d06 69
    0x24038010300c0c00d4000c020020729034010400b01c0c40120b6816001504000701203446d240020100b0098803880b00010203403500300d28499101030044001e980900421900803104c2661200d07d185d6038003d511606901000540210741124004e40c04a070302422442c0c80201070341d40c1c0c0d031150000741411000c80307400310b900040c40e408810342c90310924016115682c0c1da003d503400c0000d00180400000410400c51400c00100714951070f00b14001e461192840c06903200300d00110f80303c013075006170291044c2c50100303600700494820607400c8001c48202504035522840290304e107400304411110720360703000e54012000313902407500c507118000403c1e0083d94903001031585040100c0103d0f5820041da1004046410056521412061950004044584041d1080c2c0c603511a004501c00400d0264001402c0c0000020f60000304040074070290321500c000d4076826100e00c41c0004850035a100208210340c1a002801c55100150280588540040c080c000b0642400c5030045401c0c2180e4a54110300080c2d41d10004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 350287356 1250 350286106 350286133
    0x330108010b09010611030a03110c0313080106050103140f0403090b1216020c03030a031a04180606050105120c0c01150f0f09110405060a02010b0a1202011b02010e01140408010608 78
    0x1290f0040000340b07401c9402000f402c0b81580c8034090324100c04c040603242c0944a4080983c8070a6035000002401503941d54240c280b040f0007000740521450303000c0e50038a80001100e600910070b01ba00002d048502002540d2442d13150303008060300410440c284880d0500229403254004c1c06015134690700882c0685c0c50616491183d00740101c88060303003c5511580124100703032400700c150745c902c554500303010920800241d20348421005030889140c025107070101c20900352907034000e1041080c2c0075100c2044010f89900044605200d98600b00c0818424600813410b541685402081008000000010546042166907107201c919510824042a12401c00c2c413190284071401402098450300c108011489901a440e0340d020b01c0c481d80c4d1250001245030f0300e4150003074004407240341e40200038041180e20b810404507007007003142701640010000c1d1890101041c1d80003007254210740584580700c55220010044520702a0740101e040c2c400380600001031800401d0013290090400c002c00741151480b04c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 350288606 1250 350287356 350287369
    0x12260103110409020114070c03050d020a0b0106030b06040302010503060d0212010522120f020f060901020a0807030c0c150f110c1606081f080f0a15060503330108010b 73
    0x80409204034680500f4200503038000d007010b400340c0b4841c0703100d6845400d9802c5c41800c0803060b40c030181c080c0c05200c0800780c64990104441413040e1092502c290f031642c8030700c42201150803004080742c000c43c00304814009903014001440e4441402461040d010109a020600c0685420030b1404140c2d12a8248445030403c0d2901e07000030000400009001c800d80e8403417450208921880006000b200481405524070038030040030303c040c200d403c403042400e10800885c002d62000041e20009044100400c503050700c80e008800c03100c07015079108424005151907a461031180645160b25803507440107040b0a00241e0f00407a514052145580707030f00d0384400000c3c641001e10a041c2c81100d104040360522451307812000c1c00390444c4911100c041030401d450f00d1400181855080074443d441040140003078910009840d901c1588038080c100c403d606244c801d20181c401c4c0780110f90f85900020740908c0e11300e0030002c2810103109010044441c00c2c010b0190306172540801e0f04010400d94640d070400c0307098205103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 350289856 1250 350288606 350288633
    0x82502101409040b15030711070f180506060c0714040b0901030b040f05030f070506070e0901060909050408130b1e07020a03030509210705011e090312260103 69
    0x28140300d0040e00e52a0350414403031150b02e100a106954500c0031601684441001840c200d0300c0341d01540e541d040c80c90014004c03245000c13910040744101440420080d260f600c100d02204c00c600c2100c0306511a010001d0050000240764030340100c0c0900052000920400103440242944130300d00b614050713080288401e85000c506010300505844004100042c504403200c0c0e8042e400103079902c4c0008c141d02e40741341540300d40310074020054030124403a000d1200100e00c0c0d0b40924540d488865600021000b40f1480703403001d10581003c600026805c00155a49422156019201c1d86c40549070444054000c04040c001d60004460395901052145143c3c0c0e0681000a4880c105103c080c1403103010b900203503100185010007801c101c40403480c090651200070081c08119540c1010740881f00120502d03582c2c401a0740f0610f400035968a0710030701d201c601d46000d03102050065458100107811521a40184907200e04a0003c109c0116103032041c1e8541c585240c15400380034240300007d945036007043e50306442078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 350291106 1250 350289856 350289889
    0xf080901020702100c0c180c030c03090503030a0e0c0a0b1207090b090d1e03020105061302040503070b030601050c06100302010e010806010c11040207050604142a01030504082502 78
    0x10440034000d40c0e202c010104000041d4170300002d5654842c40c2c40034001086038007aa6400b0700c58500a28003000c142c002d44035144450351b041200d11001d00c1c0031800e40360780364005031040e00300700041124058613800c00541c0d005040c080702c0c5030b1940a40030400150807607001680d05034011401d140f800d81180005c0390081c0d0300d850f0081c1e00d20f08007410641e0b42d11a86041d1072003004156010403c1002d082c020481c0c00e9004400b8102e58804c81c2000f9028107405c58006118100030028072140074203078420b4409650f006001014041d003030503c1c0051682c4003602c02414400144241e503540082001501d115401024017004524954400542980c00100c40d40c1d040c41550703c104000b030790340b04074041308844d00708440468807a14500810000d00c02c51a000d0914000c00d4108818401403040044648010500302c0d10f800b01200920301010440a40390340040c10010310a1546612030381060750402c0c00f80105030714041d2400b03e51a10700000030080859a2a0720700790200b54a407012603644283c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 350292356 1250 350291106 350291111
    0x40f0501150f0b03190e0f250e060f0307060309110d120c08040807091418060f0a06090903020a06150b0702040f0b040204030c241b050a080a0f080901 66
    0x2002014004540c05014020000001100090020209010b01e007419910b17003004000e00d030a042080c64442640e00810040c034482c0b40c1040140e042003a00f040c01002840c404c4401d41828582e024084000140000341d014041c0d251951840da000e0042000804842c1c0b00010548020301d00040b40e00059005075100301540c21601010030a00c0c886000d80a03103910b00340303d8400e035525100f401c2d8021070b00a0101c40c0300d61000411840030b50f900017040b824120307180c1031059803500313800d02000d215903180c1829070b040540441c80d1100400903141c0c1009580c1c0001c40c0e1580c561010385c08aa00034001503005034400c0c41e600c01808082d2060b56081c6002a040304106070516400030303594460b80f14004c0c080c55950007200c809a40c21f90020070820002401035580700e0381ca080c130402e2410315000e86541d92080340e40b0902240d15030f549514406903682c84400840ca100301800c50650700e00d03281a0317050b0046004690000e98810010588528982c0342d02d101c1050003c40100910b000810300001c40e031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 350293606 1250 350292356 350292359
    0x603081207080a1b030c120203010b040e1f031203110a08060415030507050111150703021b0a0b0a020906070f030305090f01090f12120612060509011503060221040f050115 75
    0x140084c0700000303900c0c1c2d1030401007400031540104480728503045910f58800341c4088000309080d10031200070300031150110001459070300d071400904103503c1098038035901034121410400004900c5c48851035422003500340001c484d041400b41a006130f1010107131100044600c400c101e903a1400388900314110350903042e24820700d81540c1d5140d5035038296008aa05100c803230203001e00c0702d110400c003d41800808402109840c2040100503019400c00020703280e000080c0381940550b00c00c0090050305040d00500642010384032a104440203500010241e07800801c1000004007241000d459004440d100e50b50028061402446460410303540e89a0029180d042080c1c81c0e01154290140105003600f060b042130b41c00384600c1c010b0710b540e0140d107080c2c8086400c2440002da854074036000c511902d405003200340850350301c00c02002d00b2180c00c01a0705400102c88401403000c9102c036400342044070f02070300d00d03198010111100406103090860302240c0c002000c0c1c4000c000c01100b0302278000c1c04504c0d204101c036441d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 350294856 1250 350293606 350293631
    0x5040c14090703050901112107050304081801120e060a06050402040503101107020a170d03060b071202030c1207120206190504030207050604120c14061209010603081207080a 76
    0x34400b4082c0b00802d5250408205038000039030000c540d00e240c015146642c2c6480d801c0c0700e00f1050344242d251044000041c00500c4407402907086910580e80304030410701d402c1103600e12450000c0440b40040c1008480300d01c40e0a40381241c442d00a80300032030002068103103000d0303040ba030941d0030780d411440c015401031008018036140010021001c1541d180e01103002007035980c0001c0a4010250042d43c029115a000202e0240820700e05d00b0049003034042e600c0d002071282055007620160302c52184105820051603002c1690f41010342d070142e00503c162407074040341d451344a2400d12110b0001e0140080050700004009564010442c0c0c10b03040d00251450b031a003841c49222895205003080d21454950340000e0405100b4480540917020042046e1b458a407a8444000e12402e2000300303c1d90390118040200c1d030035000b008000410480117001601e01943d1050340600c0000c050072601d455900c6041c04800a04044090224a51300c40042121417401010003010040003a1045560b10708d03104590f642d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 350296106 1250 350294856 350294869
    0x60a050a0309020d0b07120509010204060f0e0d0503030702010b180c1b0a0b131a01030503270a0303021f02030403090509130f03120606050906030103060b010c120305040c14 76
    0x400c08500300010b003190340d800802c80e1402481c40050032848a02d04001160340c0000320200050340408080045035107503c2070900301d00c0340b030155501046c0219160707400d1354803598180c1090780010b440c1500d070b42c01c940d0b65107155400654503000943d440d80c0380100d440c20030b414403078a0040c06811803d590b040000c000c0a0901c40e054241090580026909a91000420900c41a50340c814001c122600e0005543e1140d20443e05048403c3c8030703401004916040941c03c3c0c503050760b0b0014080d615000b00380100005255401c0618000b032003101a800038155242c440c007400039406034015080400c0d000890380c6002118800080c1074520620600002c00d44c00502d01c0c043d1a02640d050046403180c02080c42c44404400f0010300d0010140d035417108150380030781ca4240c8440c510070240096919004180d416000303250155070414014001000852030300d0b0040b420303014046c10070403003651042d101c03045015108050030700071070f807a0010311040160110070a0002c102c403035400307903008010b140041c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 350297356 1250 350296106 350296117
    0x30207080c27060a0b071212140a1a1503040516061d0f032a03030c0615010e060a170a092604051309020a080d0c0f030c14100b060a05 59
    0x109039100140c3c89450302d012900103040e040010031b03120680c900d001b400c0c607542d19500400048044240140d0065140600d14042d002030405604c1c0c1d690b4800082c0042124640c01400d01139041c1007074103030f03454000318800c2800824a1300c81e0f80707150a0074407a1825030032101c40c1715403001c0c0110420800303511400c100c070030714103074034103120440914000240000c8202200075854062150100c00444410310500c0030095100c0c001045800c02204145d01d034002d0640440b042d4014000043d0300c41402c01515942d86014141519100740b0304021800d070781c0003002010003145410800d40d401c0e4000d201025489030348003506000d403e61a80e1804035051054007044017a1854120120510b03480707a00b40d03006010301411030301d0307010500516480609070580099019421500c000b050b03060002c00e90405c0c401c41903c03108400101e5170703101c54940f8103118007601008068005280040d1016440c48060400c15001703104540d0703440c0b00c0000300d45c07181e16101d03c1500d08002122915400005448 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 350298606 1250 350297356 350297419
    0x180307080a0809060d180507050102070602030f0c010207050d021f050615031506160303060f03030504120f0b0c030915101e091506120908090f06070b04030207080c 72
    0x94071403c100002c9a00b0b401849010706085090a1828480d2110345c1c003206001c500440407520340c140e4880059880d140ca501942d030060300104200440c00454100900c1150404ca00042c03030005a620f485080c101010800c0d40103801101e040c0351045150000c84c2c034503982604040026040c4040018a1303e030f0301d00703901032520b0313070201c00138044212600a02c1c00c0e40c503000d082251f1328222003112202c01c0e4056501200401e190500c003050710341d214105241604e0345600c42c1d52600e8108003c1605107180000e003281e0040140c3e55801c00a41440c0c989802800c1c041c0b00c1c15228180400e00300d00f00707500c1c0c401c003400500c441400c00c0103450310000c410046500c4500340c1d0b10841071174a0b0010340d034481508121407282c01c0444c0c0c06001155a0369071001c69103d0395030507030030001d03c014200588035030f200090f0100d001070190404070300d07112101814504004041030700d486425558145c1c0c01e0800c40d0150050b80040b141040300480520155482901c02c03034544412030780200f00031180342103411045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 350299856 1250 350298606 350298623
    0x1b09040c051c0225020f0a030c150206150622030305090a1d150409170a0f140703050a031d0106031e08040e0405150c09040c170402010e012102180307080a 68
    0x1300e055486200c44000404070261610404c60b4590400e072003001024465101c1c4610050031649501c3e04c0401c0741801144032400c503200c00e0300740070100440764005401250401d00aa4441c0c1c1c1c20300980320340d50780214429101c0a0302d2741744000810081015a90000a803030341081d40142c0c007200a0511a5800085c9040110461034403001107802800c0706d0314010104071a4005100e801c4100300c3c003030038518405130390b0a101c980340d032581192003605041c60f440843e10148078110000b800790005d058104d0b03e600d00090101601e0700d04580300591704503550b149075542c105c14024030600c0e159400350450b861240302402261035440c55110701c2603208030b0f00488c0a07840480e08000013030100084505000c0c0800c600c5092401410655a202c0c001702c0344154504440303444628003c0041c1003048003614520803043e9126001500c20304080b00111b41080308100040981e014680121001c0d81c00402c40180c60380c10080322140c0310244420050700c242e010900030070001d00009501c180199021421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 350301106 1250 350299856 350299927
    0x131a16140f100e0714010c03080903121302030106090209062208121305010804030915030e070801020702011409091b07020303070b04021c03081b09040c051c02 70
    0x1468107110040c440001c00d40100100400c05003400d82102842a8640f42500ca52580e1150700c1c0b950014107400d843d0200381e941d4400c00c08a40100c4125502c06206019203107001c2400340d14850080b0100d440c0103040411500b03800035420244a18170140040600461a0196490018416010b40c1210420540705542c1e0b2a0503809500001c0000381070000499020750910034400c5031540003038010b032004d40f082101c0040c05600c100c803030600880e0903860b41028241040382a015200305202e40d036092545911603134240142c100b040c0782c0201400000140c540b01c1c24800100399203640300354025104414010301c0300c50b9a40030708058101e09000b40c2c01000c40400003040c8076a0060344070181d45804003059035014481080401071003544201e80c40700500000210a40301d48140d11800782c0001c010100042030f103401c0c10981684070254901d541d0800d02a04002070648103992a0740d80010004030b6280c103507100444000460350089007017503080074148007881c60340603d4650b01d81950844043c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 350302356 1250 350301106 350301143
    0x90904210306271b2001050c09040203070c0b040c170c060910020a0803131a09060402040e0c120304050103051612112511040b0901120314131a16 64
    0xa152404d004c004000c03003450904002e01540402841005501a808183c0c4000901031040c1131103840c1c14581a03003030102d2503040c0002900f004105900f03000050b1f1080c408185968616840745100c1c8640d940000e0a000f5002e104680c1298000d582e54091032040340c036641c5030002da0b1045082036804003462400180101d2401c2c1d0700e410301503d1007800206018402000d8002d04404501a5014146038406180c09100000c01100d0483c8141c1040d40418010f2400c0d4015051500045040b90600e4070300100042c0c4248c24440801c40d41c1d880018104000c0d40c05008955000c0d0035034603010f00e44070380c001004e0300074101c900700289a40d41d150111036280080700c0075110701c0c1454989041c0000c27500040e9540c10003030288280c401c00300d50921412149031600840124000c05400c1d0b03243c0340d1800a1120091f80303c00021418000680020041c01000034050100c5103289281d640c0b5151401c507400c103410b2000d41800070340344d50400018031002d2041041c000890341c03200c0e905032207032100c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 350303606 1250 350302356 350302361
    0x70501060b0d0e06010501050a08040b1515071406040b0c0f040b0403030f120b0d0b091005092b1403060d0c0801060e010e07080103030503040809090421030627 70
    0x1c101c40d01101c0c01041c90700341c0e40101c0d03200d501c2070300405040f070311980d8844d001540c150044900700400212460002000200d24516454024004080c01000c940050002600e200140052200390700e101007101401e000003600150841001e44c4050302007414107840322648800b0050102207450400904051401c0f010130880d0000e001a0300324a440b03a0f00e03441d00400c50310345080300b0400101d02c030003040e650910601c43e115481ca1300400301c2d640c0c03041035074038400203071030040c00c560b1980207070544044a09403900442e4482c580500c094807500f5034001c2e28072100d0035049580107100a0000928489581042510f00c440c42035405081d100d50703803500020803202201c400141103840452000901c80e205412035801e0b2040da0094881c507a032580e00010013090100e640400150402004201090084000b1038005000c0d08625140c4080100401d6808205507022144580d02090f0702c00a200072000341c203180c4c50586001d00480e4a4480034509020701d010070443c202d0045801d544074a01541d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 350304856 1250 350303606 350303609
    0xb070645031704300305090c100c05160b0406090b120112022107080d020c030307020d031403040f03142d0d0f0e011b080c03061201050405012406120207050106 70
    0xe204c0500c04440c6901c001c6901074901000c20007280c01d080202c1d81000700403035102540c000241464149946040d000c40b80050340c0082910180070701100a20403c0501a0440c06065140d080a594924041d1300410034891a80415034143c0c00b40081b003148984041054111016a122000b80290600004828004c95000030410500c1c00b180010701c0580498160f08466540c8155800d203848594180d0b1140d030100a490741c513800402c28440180340240b000c1308540d000c0d2510b2071501204045181181d401a68151901ea070408525001c05910254090006002514290a0407151071b109180441c00d0f40307812281d403101002e8000003000010603603030519035244050240c102d0701040c0000800c0a12a2449907500b4010b03240d46800d05030101d810101c80c01e6690096503030360100400d4041d00003422996111402c0810500840c6c0e007401941c0c0185d029600006200c1810078203465541c12020441c070701d8241d8004100840790f00f002030840740074030b400c3c009a5104250701d002801030595 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 350306106 1250 350304856 350304893
    0xa2003010b030f060402042c070e1f020a0c08030304120e031b150a03150e0103033903021e190605090a0f080d0501060206100b070645031704 62
    0x103048101030a0303604101402d5440f0550901e00034546660000300c8ac00381c0301e000e416400c100001c26518010460100c040d1000c4e40381e2041c0d85641400d40c0d0b07826000042a442040564400700500c0300f403000380e15451054103d40d013002031403241106c0210740c4451992800407110040c550308000c4036100c0d41c0c401d05010001f29005545d408a10038040c0041005a40b0b103140b079804840c02003980410604840c0c140c80d05a01c03581000e044502c031903c511140000194524040b03189945902281101c540c602c061280d0042c01d02081c0460000202c03480580c100c8405520001101202c00c040030309404603035030071100101304c640c1c8030f140640c03030802c101e000209414071079403421042c44090f07400b41c216240c41d030005120a99803880c08076616241580d80c0040d542002c80d0802c14428100018201c3c039204880104456100144100101103e40c0c41208640940c40070b100700e80340e0618003815000b1800f41804540c5070140c400401c2021543c030030700007014054000c6428402b941c0b40c920002d144 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 350307356 1250 350306106 350306129
    0xd020f09190e070e010e06060304021e0a0b09030105100e06060a051207020a1b030302060f0a1407030510170d05091302040803130e15190504050a2003010b030f06040204 74
    0x890700007a43c0d03122030034803d88030060410030002c1506200740300300e1401031100910980c11626190204101c10300c0c10403c0c02411602802d4482c41d640700c1d42c680c20014100a640b103a250b01d08082454251480204000c00019001d4030600c40600744400c2079820000a940031a11613018140946d124424110401902c8080500f04007000d6400202440f10703900c503515000c00f242d03031030062015002840c04000c1c00341e00004001010700303501600050b440810702001003a141032013042004410340598230000065194020423000c180c0300d9000c0c40c000d02c1a01000401030b092081d03c1511018078584000c1000b5000480c40c4540d59000c20501054606100c21584c440e501c010031a501d03800510f50401807082c600700011894041502c080c40391481e81d0b40c0c2c4022aa11608112004140c18242004280300e000007041039141ca11419101d06011000000d465110070710b1081980016010903c0341c020401c010b024101042c800d40350800603441e120f503400d031034841c00900a4007035074001034140c05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 350308606 1250 350307356 350307371
    0xc04060905040c120c030b071b030f0906020f03040e0901020c16050103200a0e1c05240c07030311041805150f01051206120a05030d05060d020f0919 65
    0x60154051405503128a107201c0855642d0b00440010184d15a0045c19681c0455402c0001c20b485600e495800001441c1c12040403603020310085070100088d0f07060b000100100403020002d50231144120241c64180010014414407014096881c0328900540341512180360128100e98805d4041d1208082158160746070008514040000e41d40c440c4222400a4204408070640c10300f0041018001030f50701a400e440c0500100040e600800035044036600015461508600240683e03040800540f08802038a1078540e0910446054901c0307180c84048040184140859030850384119801c560303042c2400304d640100340c02c544400380215845001c8000c1460110b40f41100a40e000d40e20504040c0580e0b03044909450034800b4104003070102c103004c508200040d1900407540b41c443d40e0700c6080240110030b0040c2003e0058108a15100c040354250301c040303100c620604484c01501d900c04025181200e410b03059030001801c0c906410300c520f0040340450045045641181c0f89800a031010140c20300c001c1c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 350309856 1250 350308606 350308619
    0x2060304031107050a0b090607020d0203030c010b090a02180d06090b0c0901120b03121b070e091b0901060c110a0611010606050702090f09030c19020a0512070b0c0c0406 74
    0xc1c02480da0300002ca0040001c00f181500c0c14600c5a0b00f40c40280403410700f41303410b90052000c0d50348030010580c0d01148102140c001030342d04000915000384250004610b0003422424000c05400140481c2d01c80c9005014943d004c440c03040140c0c081c2101154285049029400c240c4020000140050018080c0004001c2da9041d040b0090564580030383c1e552a04141191880c1c00712100c00c06c3c0c0c20b80c1504000a6011b40200074030240104194400203029031010203040c16180c445180d10203210b01000b6020044030000030320606852480d036042480c8110086000601d10f40e4050044034103204e0351500071018040011031440307440001070031f060a002d803140c0c000790050385082017a011941c02e10001040382482031b0305844915034003505590003a290403182522900008142101d984400d0015503100c15040003101c161602d010700c440e1b41200702d40140101142c444c2c12540c0107002c150304491915400040000c21030b101c0c03000060705c501407591041d00b0a1040881c80d0351190500b40c010405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 350311106 1250 350309856 350309867
    0x5250b040b090615010e01050f180a050d11041812170711190f0b04060605030606040203012304150e011809030c0602090a0b03040b40020604030206030403 68
    0x3180506041892a82c0c0c100c4883d50f243d008403001e080500a14515850550107a1402140030005061180c282041d0a80494441e084590802c15072600002e03111450306006000a01802c000e03680103c0c1e00c501074807002e00f01c4a0340124603000790b0796402c09001d1065210461040140c0c0004200d213410b400d040020802101c100c08403a04400d40c0f80840d00050207280000d03140d606000180c002070b0700040d0305250074205c240c82601e48000c50041003000401c80b00d80e83d48214490540000c0140c101424586465002802c450003144100b00500c56401c048000128a500400e802580103181c480801c02401071003403101074141e1880c00100d461032181203000e05840032045520184a400391001017918441000035010905074030076000894815001066801409010750480c01c2d61600c0a01c074aa100715410f480402c0c03844240500c00040880e5240101e8a42c40007414400041e8819000c5103001d1210b002ea0048900d034007021520f030031041c5c800558000b4012030f2a803816050140c034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 350312356 1250 350311106 350311111
    0xb03090309090a0501080a030c06020403060e06070e0d020919090b0c0705190b13050c0a0605090f03061018060503030a0e0a06020a05032b0c0306140f0303090105250b 73
    0x2107094914001600c0c242e0720700c84c240c100c0f4a4030009213420740c01034406481400d61560241c410710b03000c020200100c3c00074060100100381110081a035071414a000a10050004030a180b140c000c0703401c40e0000d80c1d00c0804a40d00710511025284020441018070001410000c20041c100082d04040009203490349000c2c080d60390044003962225180d0031203038824079240080c0205a01501c80100c1c0c070042c001441000c206114804481130590920005050f4010382d1f030140c030004000240442c0113007490f00304003580c100194000e115509100450040c100c5941c001c1c26080d403044102c40700190042c0e0024001040c02606596455041040c0144a500d11aa119000f0b00f42d180001658510009224900c0381d0408080c60805841d40030110000c01d248031100910000e5201c0c541002629120f00e40c2072a845440c0000c030700d494141c3c0e44883e4a401041c00340700d518250482c41458401108660401909107001580d6002d02940524000321000c2100e00030f4402107106800c0183e005010b60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 350313606 1250 350312356 350312359
    0x8030a03020c1e2a0a15050d0501033903140109020a0314010509030c1506040603021c120c0510150308030a050108011107151505100519020f0a08030408040b03090309 73
    0x1131100046040c0950425250150300c2d0041840c800401c9500c2490101c0360901440f440c281e444d0074901a11401503460a0b00701f0740f11001400c0e48084100c000305a0204020001184540400264000c0c01c0700d10702036100140881e40d6048880e1003488082d401084d401e03900510161045480c5e0500b040d01c5600400203c10962826010404041000090303403200c00041c0d000b00307400360051100381c120f070134060071081c0c010783c8801001c00141d8034100c40950910350201100c190f000781d82016141040341d01c1c401d01c240190402840302007000413600d180e440b811046c000c2105001107545030541c80d103641c000350a506011003445120011504035504842010000340324100404e80007039190b01ca200340013860854920050980c1040582015038074035816818080720a6442020900041e11020644006000002c2602907032110820844011005100400c5501c401240e1555680440b000140055602000213010040c584d0215000340084240240e202c0c10540c00f500e07036a410520085 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 350314856 1250 350313606 350313643
    0xc1f0606080405030f0f12040602030f07080702070314100501120c0803032806030501020c0a0501050f0417130504140a0b12030306011b0f050a140708030a03020c1e 72
    0x441070301c40c915280c0110b4101015625125446160b9040395012060030001840300b404440069010703a091980301e10f00900007d03a5901d80144800c088040c01401c48050140c18414450072175800645181500d0740043e000d00e0211041114a182800b05010601c640d810100042040c4802001d1040720620a81008142e5510b60480d26140c3c001290302c0d0042e80741001030b098265944c0802048070700c1c500000041c40ca5103d4845500760383c000d100840c09030780108800e07070070400d09210b03095000400510003507490500b0fa8032030070814807485c084110680c001c501d05100075a0403140c04001c0130018010002a1310706e8140a96501040f90340780c41c241d01d03044d111242400c0c00e140207544102214055455a643e480055407041c2d004044e940354403030345202c5840050005691113004a000c0c000503c00b0102074604088001140000e0000c2d83d00301140c00c20100c0000015202c07000000c1c1009a01d402e6803644003880e048004c0c100c44000940c8203540000414041043c00c0d0b1510b50301001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 350316106 1250 350314856 350314859
    0x914031209010c020c01030902060702090a15050307030206071b0e0106090e0105030604050c090c07060e160812070201030c050906030403120e010c05040b0a0c2003010b011d090604020c1f06 83
    0x1014201c0f544503c2400150f003004500145070f40c0b01707a00c40300b5403e100070402820585d50340c0105580380f03000c0b0303010104681d4400030305a07100040810007009000803001841803900b0f50380480c02c0c5d0300a2100c02040940314542c1e240c1000000d400d0300001e0f10101c65460b04079a580c0000a04a044600c103444000402000116041c03e0118ee1248141d420000920b1811148001d1009804004044802540061054000296580c0102d80071182010700400d80301708a20019106800d050740040242d81c41020381041000118090714000307a024200095800b641000a462504c03800d0407465115100000304010190000110801105c0c507400c03c1044c2c680d0ba45401d0300b29006100d0800101e00144420000a588480102030541c3c003898007043d8500c45070340f0305070640c1603602c16006504175201c80011070b013000d1040c0b880e60182480d11503c881e404045e00110704800040b20f41c010329400300003501d43c0d2156011111350000040031607201120021289007000d8400c091080800d040010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 350317356 1250 350316106 350316121
    0x150215010f24031107030306080c010207030c03060c03060b0a0c060b0a06020312061f02030a1b0b0402010e040b09090a020306010e15090a1103010f0302130509030f070609140312 78
    0x990810b8800309000d20306500c1d0b018880e800b40c1241c0d400c61404142e1242001c9542450802c0904400c40c400c1e10701044003828505c3c00d0341000d07045c0092034115071207c2c50810201c3c210340034460850341c02401c0040c0b0101000b900318050241c40d04000748204000540c4c41c145035222541c0b8030b6850040508000d40e104c1c1c0ca040040300040307403041d01e0041c0c0c01808002804089552740c2d03034118400414022242c1e1801c40300005540d4210108005a000410360340301c3c2d9030308042e0100035600965040c0040141c0f81d51511034010015001904011850030b03628550b413202c0e84810060440104400c880385000300f81c103035961402800883c0a4007408000090041d00504050300880c041e040c4264402203003028840b040d20014441c03251141c650842442d0a4074250042d4080c0054000110090b4298010b00071b820300000310307140d070661401003000524880072040e2040d005000021541d29441b50401760f001d810158005080141e4000003c03a4040000000340108410003c01c81c00c15540d0300c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 350318606 1250 350317356 350317379
    0xe040b030a030203030c0a0201090f0303020c0708030a090303141204050601080c031506010f02100e0618151902090303040f031101020601080a030c02120d091a1e03090715021501 78
    0x15004003d68070510228103801000009014144072500c000134400400b510b600300086060b10003507010a03030008913244a41d20501010313000c0d010090056141c08030f88040204030b51183d02c0080c04100b03060320001500c00c50030007110220340c02a1008100c5081c03034108140c44020078410396406224200e80c160702ca0a01080800781800c02401c8094039a0700c00c8010b5458801100101086020b24001d504908030300d4400e40c0014500700c0024010392a024000d184030b80303c2141030f80300c6584860780c0d07640364510f0f003504d0a600a0ba00d070001c030000c0d42c078860800003a024004c01c040d49400049004200755090080c150100c90041c502945040016401640c85020a0150800a41000701e511011034004d43d8007072074041c40234200d40d007644404928542850b0f00d18500c2000a8030a60042061700f0226014121486000003881e14111441c0d516a600da281002000022000030000521200c8280410300080141d2200c08c25500c849240094513103c0d40b0300692800403261001041448600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 350319856 1250 350318606 350318623
    0x60c030806040f2009090609010e28090f1a0402030303181501091d0f0c01110703020904050d080c091302130504060b07030809010b210307120e040b03 66
    0x548404020351200c01c01c0c800607202c114030f01040c00d900c981404011418a101e040000320040511644811900c2e042006000010303203020b1007041441c005100c507640c1450019040301450403601a007000b002910205800c030020482c1c15945417103444018000b0309e10a00d0070992096000041d81030000134200c4100c0f6090314041c0d0141d20910000c0c840d903c1c100074000e030301b002d00d000b00c0d000344211104200c800034098100041940d212400300d0a0140d04005008070921810090312401d0188039405a03200740a80015040020396813a41c10707190024409070000c0d5401801601003484e1504100d0342c0e81c402450100005402074000800780b0303219109650409800901d1034203201c40340b503000c130003035040001d05580d102e80d444000946a61140f040100030031801d40700a0b1039056074140a00142802080b40040b039040000d400d03810350321031400f41080c00760031008240e0400c400720700038598010100c00070885050b4022280b0010341286004840520840b014089000d0760030078540c035450309 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 350321106 1250 350319856 350319863
    0xc1002031c090c0e0406020f04032d030518060f0403060c1e021f0219080a0b09060f0d17030f18030903070b090d020a030b0603160602060c0304030509120d0306060c 72
    0x940420b10401d0390103c41070360401c0c021500503023464100c03140e044603540103a104442c0c1c1242e41c8043d08900d90400444640420181c2d02c8149613902518060203510900d240d200001d041d036000440e182d610b04c000d483d070804010140540791030304c0e0b242c20740c000c00495420402141c0c6139911400700001a515040511410361701420a1403408910070007080590030300955565000d02c07040b42c5072840035610f200c2007021070352041c034141000c0c00f494040b55403c080150140340e20fa020056a41c0b0b8800b074482300b02c00d0549100300e240303a00c3c1c101100c000c00c03803110359401c1d0803000061281c911035100c03000d4015030400c1d42c0c60511600c02090b042c2c4d244103080d0040d8268000740820041034038124060b00001e40d0180072a5484112a0b00059149042e90400c40300008010203129040c10b0411040f40499180c1076103040e8a414510702030740d240d00042256601c00e0b0b00000041c00c00d441031060301d01c0d01201905c040c2c2041400803040b43c90b513002c00e40712400a45090f01c00141036204000c1790002640 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 350322356 1250 350321106 350321123
    0x609240106020304060305060d0503070606051e09010b03040618030f140c0c04050601120c0801090b0a0609030803060123090301051005131d16080105010b04030b0c0c0c1002031c09 79
    0xa07205c429030240038000c040c00c0e40080404286030101d5410f000401061f4482c54002500303c0c20641004020010764001d02412000024040801e445110344541510240040c1300e441c3d9655282400140080103181d51a018140c0b05600800d500014484040840742e201c003000e01e540908030362514000c00c80d010321b29502c5402e1f40304031030825502c80d50b04210185010010342d211310041600f51041e0740c041ca40040e1510700100032003003c074807451864441c120f030500c405601c0c0c0840142049190300002c0c0483c500040032911a80c044d4060415811603d0103100000c0c00c40c59014404e070300f0501d4103602035420b21000515010740802c6400a85100803d5104010101c400c0b6000070040011000c42280083d21110340750102009806c40e540c0720323951001d8602d03060150f958290381041c0d0110300522401d0005000013080030f83c1c1554045910400b45888408a00500385001d10040e082e82d040461070020000d420f80c0407001f88202c0c5445114a107920b080c0706c02d51000c450540d00007504262 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 350323606 1250 350322356 350322359
    0x10803071104092a050a050303040302060a2d12050f1b13030804090207021005071214070c08010f0b09060d0330091101020a0b06090a09050609240106020304 69
    0x80c1c00da00944030140a05001102ca4070043d00c0c10084440d90041341c070108202000800080c40c0505c0c907200034200940246042514542c00b207904c50058100700e0052040c021418440c1c0c00c08140791081c0e40100800c603441e0942d2105028100c05003c0414020060401002078600010142a240200d2a001448600d00400c0e51900101e4208048100c012030a041000000c5000030018001800c40200e00607680c03602c0d807040007c0504d60303054100521009210b41008070303a202c22048000049801c0407400c46110950440c550710070400d008203405030380403001c1781518055000b05001800c400c3c0c00c002407c02c070b0f2708204400104960309030b4400c188610b440d0010740b2a8078a00d40e011000c010181c400724401a0700407d01070b0413a051102240c2d0f884510081c895440c080c948403500038000380035080c109894a0001200087c03203e0b000c0e8007118003240c4007100303550003150010f800005a07119400c00780701458550f50341244141d580d09921584645e01503035000172604880180c0c00661405 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 350324856 1250 350323606 350323609
    0x120c0b06011b11030a020310060806060d0302060a09020f090702010606030609020f18061204030513060e0d020f06040504020d020405031c0f0c03091802030f010614040e0a090602040b120108030711 86
    0xc240003c2d1681c3c140c041c4554610046c0c404108500c424003aa10340460340794101640303e8905070004007064407a200d03146aa10103c0c1d00407403081d400402a0380007060649840c0045483e141d2200c5046422000c0d2801f00542c6541c19804402940c60325501881700359030b14030b118010f80c000c04e0000d40c20080e0030046c002103d09040e14040c40e004000e0b000c0b60030442044444c5c1c20000040f01e0581c00b01e00005562410369001641090140c0100c6c108110f03620b11040200d00d800701003200c020300400e0003002545c56503580b00140c40003004028000d5540c0c1140c0c0c100700019401038854940a44500c00b0160400301c40d4545000d10362000341e03a0236001c0a00390504548101500e84141d080c070071150360205a844041c07542410080100740c0c01f42e034905003201104082c03e8141d00c0f50b4104001c82c411b2074100400c0804460489012011011180d120303250781c0c400a00402000a007200d00c0010001020130034500549410301a40d105c200380e507a690380d03110b5140d00c907038400180318100081e106090b5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 350326106 1250 350324856 350324873
    0x2d060118050303041e0803130311011701032603011403070b0909132409150c1b05030c0322060c0f060f1d101104050d030e0607120c0b06011b 62
    0x9141780c1441c0c0d0301c43c00d43c2d522021343c1158804004114402032090091042c0035004141d8800c00c6020720b48104c0081c4030130200041000103000040c2421003981040c02d10300b40104607110840c0c0d200112903030700e5a4840d00d907a10f80e00031034400d40c0a405105000030f0303840c8030741c1c06a0301c00d0500640108125506c01c1c90209490074007520403140e002105252181c504603000300f00c0090321004000107a60020382c00d01c05100c152141c0468401824400190102c82c1e10241c4c1c43e0b045200780c1503a500704207151030b00b00c1c01c3d4007912060749003d10000c030302910001f111340c07208010352644040d0403052035100d6504585650075140003a00388100d807001d280c00183ea5900202c000d01d1854000030760015021684591b004e44250381500c01d03845252030982c003000c540324022907851446240c514141c54500400c21201312018054180401c412415142d92943e8048920340d030b5206035610b000720f05851000c0c02c001e006d9081541c0103104d1500240295009104003a000c050408906908819035907c03001ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 350327356 1250 350326106 350326139
    0x70c03020a050a0614160c0204020d090209040803011706011a0a0e062b060e0f0403140c030304061b0219060204091404050f031903052d06011805030304 67
    0x440c4601880c40012602c02e2102040c014440c1c0c0020030051401d605040007030b080505515040041c01c109510030a400c500005401d542c161005a1903030284d4000c000104618100030b90000034060420081059040c02075040e21100c40c0d15054801541c441c0300c0d0307515802d006001c0210702c4100044135415800d80501809002403508540000d86400852605d400001c642e403a2003141451070404c4911062000380c000303034500010030005103007400c00c1c01ca07020f0141c0740303400d20707668940410309051262846900078a1103107603166444800c824020346d683e00444041c0c0d00589408450803401050301001055056241e004240c03002c03006442d10100928040104d44050307080000181171120f60060807509001d43c0640c003c1d03454103003800c60602462103001c211a81042186091140c2205d80060a00503e45000103841e1b95210b52142e5844c000c898407841c0c1000030f0031000c80d14500c1d0342600d218100c282c1c0e031900300d850000060122028580503041e490742040c40b040c880701c2a800003265 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 350328606 1250 350327356 350327363
    0x8010b090a2312010c05071106070c06080a1a010f0323090a060b0d02090c03090724110606150a0201270b0c03010503060103020409050a0203010e0f0d090e070c 70
    0x311015502c0550518211860080c980c20807001090520180f50109040c580d06003a07400070b02c008107a11400910600c03c00e0001420410151031401060b102e0070184d801041d48081e0f4010143d4031078401514482003140c00007501030508070030703103100711458021400c01d003c10b848800580f401441c054002d846107500742c46c0385034131841d181320302c240700076001c6070089891802805140318036040c0396055603510340e4020b00981e0400d00d0480162941311400e503102401240d00d540784d03100c401289003044443c0c2d02c00c042031b54a091004035482142c0c1a03101a40310140c0b00c003450301c5050718030341e40c45007001ca81c2d03590f0000c10a007202019092040017054500001c3c030000882c02c540107501a80000144a11090284800c060200f003124070017140d600480d49804031811580750100190365407a0500000307010300d4035a4501010440e0410010035040d40c010001d2110402c0100c0c20382d5181034103050390f48030703202c1c20360301000c2c440c010f114030000d48901c1030103050300355070701101950150086e04048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 350329856 1250 350328606 350328619
    0xa08013215160309080d0203031527190515010f0f030e06040506090706020f07050d0c03080d0b0102370302160b040e0c0909070f050c010c03020d0510030308010b09 72
    0x42e0307001d041145041164030711a41320101210b05200c0720301d10700001c07004070070191352082051050318076800b6240740d80108101d404081c00101a54a8440c8602040700108000724180a0140c101da00c10030a036a4014640c8003009541d40d5002e64000321481d55082a0100740494071012a10f0b110380560003121000341008240607807614003081c60200d04450555054110300d0a10881d514144401401017060b4030050400c4036441003aa81ca820142c0305445c400c1c104010031f0360400401c03410322001590084842ea456103241c0c0b602c20701604145440341e005002d00c08070403a01c401900c2820052001304031420049804071030500d180e03045d08040a030150300c90b01d00130190245440c28024017400c4c0b40c0b0007550b1510715102000c01d900c1c40151a54001100070700140f40d0f591544211154000c5003403034000350341c0d00325413401d81e094450442140140d50a0114030070510741c03d60001c0800e03181c11001000180d883d180c45480480305d90200400051a40d001080b100000718081c1c0460b89008294 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 350331106 1250 350329856 350329867
    0xc0b1323100b0406050f2803080309070e010506030f0a060f0603020c010606020d1d0409060e0304061701151d1005071b0b0703080702010b06040306050601110a05060105040c0e04020a08013215 84
    0x7d100442c03142d40c07003254049800020800221380078480d44008184010303000c0b1495041000013080782c000100b00c4074072100c000001405025031500600001c058000c0c24520032600e80310014065071003040090380759802d000c0c0000700030348000341500f18242c807543d406000e17081d0070f030640c807031362000f1302c500790b40161107404420204100788100d02c81d00c000c040c01141c4c1c0e9441e0072000f030941003800004240d07614111004120458502100c0e4102d100980f910f02c500312840002011035030010006030740c0080040301c0002c41690820000c1c00d0590284855000080c00c0c561407683c4042781303000301c542c141000d03c450740002c0e018030700d0150004620300000c500002200d000c00c6017a080740d4404d8881319152000c3c000b10756084010050780030315080c09884080b0349a02c41d0740e07407100d06100b2180240d507651403841030b8a01c29982c00300d04c094010810b5644221400c4010130341c14007806540c241c0015000807030388030b008c2184503400824401101c40b284201410400c00d4a852800301000141d604000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 350332356 1250 350331106 350331169
    0x102040b0c06010807150507230304140a08030f13031a18010903092c0907150507032f1014070c0b1323100b0406050f 52
    0x6040502024801503840c0c00440400300c1c42c114040e4013881c032940090b8401d1142001000903d030403c041802c01581d20b00362490104c880c40624441840189642d07106065200c10100043c0201c1c0d048001c54405e840c1e0900800440180174458454070703900801501407800ba107440a006511030034a507046465542c3d03255a1100c41702c0c0610824814600c004001207694944190103014440380001c1007116200e030380180c00d00d08640180e910907400408151840c1446070740b01c020b40d01c9032400d085182e0414601003a1f545075030b406074040c0f620071100100c0001b1310a00548240581541d1014070b081c01d030741100300b0b42104905c00003c1c00c501c84986000711200c2045040e041707031541040043c49002c45901c2d1f003005100940800c04002c86800d851000c42e510142950700f01030a54612504d20415191602001c0901c81c0d03c803014050300c558900c0d2200d0041517017401c060940b00c1c14480701c94443c007000101c400b1402201c0d48040d4105100029090460030380d01da08050513030840c1b400d0039104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 350333606 1250 350332356 350332361
    0xc0604050d1a100612020a08040632041106161e23010f020918130b010f17210c1f0b01030e071a0a020106050d0311010e0f0c0f060c01 59
    0x20b4002903c0c03400414108804c03903114910b003502c800640801c50a002c090200100603c4026102500507070305c4914118006c1d8031206d81c1c9001c0a40882c00c1402d86c400d001c12141090412542980c1802c180003e1040d0f078200b40c02120b03e0b050304680000744502d03041e5664680c1005000907814007042c48101e00c0b00103205030b504c4848915003050356035801c04103040c0b142e096404400340c3c0080301e80140222841610303440d840d124860050410440c7c1070b6286c030001024114805800b0380215000320001400d007184200a505032004010368428010081e96110703920b00080c800b00e03040d2100c1d034095144004162004d080b20480900c10307101402d80807034696044408112a0104403562244100425a05442004103030303411400178015103840c01c0400c14800710440400015440000341c142c1c2070920030350000000c0d0500802d003c02c5a802410010206940301075070244d15031818204c2201d118001521103020803002000b0019021584c05000105101c0c7c0003154101409010004008900f0f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 350334856 1250 350333606 350333611
    0x31a091507080a15140d110a1e08030a1d0310090b060321040b0906070618031b050c1203120f0a06050904050a02010c0c05040207060903110c0604050d1a 67
    0x3690b039507202c0c2c180b003041c2c403080b034008a00e12091040d44440421040441d40144042e601c01103800e461044003e040150700800610746070b40c0d0280c0c80000c0464001d01d00c190090301c07203031403194450b030058032030f000250f4a204241400002c60041604815140390f10302506000c25405000d403207140056582c2c0d807050390a001001c49007020401d04014041c101000528829440f4640d4580b00002002c4200f456208900540d00080000200c8030360944500007143c2c847c1d076200f039040008135205600002180d6202000702d00090101c04007110a910f0f2404e85a085a004005003424000140412200e41e0300803000c03001900040c0050400304c40e20380100d0b4801c01c00e4200c045a0f078a0050b44010464007190800c0b4426504442440701083d03002401014480d42803c2000d2a140a03003841d181408159001071307409400011207400304406508007900d01442a190002050700403507042da0ac0c3d500d070b0350f111900820240000c220900e00300b20003099040c025070280c10300008000101d0300400c0704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 350336106 1250 350334856 350334871
    0x150405150108070c020a0b030606160605070206010909020915031213030c050907050414030a0b0a022212060902130501080304030b0915040312140709140a031a0915 72
    0x20410140303503003120000383e1001c00c1c1d19000c2c510200035400506c0c034007998000c2413010800840012882e0315a103044030314101e80f4440142002e032407490b040b00500802c80d4900c00602801c0000a450000e41c02643d19042d40103009042d01d6a8624268148800301a4055407500c6410000c04003894000c0041601c1c0002034021203075136081d0705000310120340b141e02050041d20301904000c90954400c050703a0a8410300000a24000401000a850400c22510181641140100b8002d503c540d41c1d006005900f1b5200e1517000500c1608842c0c013600003584150709000c04020b80090015100746d1110403060b2004259107400c01d90100001f0845500342c00c1910540c0c000501442848865244194003449240060140701a150384403861001c0160000303050103031170b941410452070b1941001d200380302041d180700e00516002100038410390301031081c100244040900c4600d581094090141529000920315032041ea400403803400410000300010040d00440410b0804128413030401d40c080d085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 350337356 1250 350336106 350336131
    0x803090a03030b06030c1b07031502030108100b01020d140d020703051c0b1e03100c09050103150503300c060f0a0903090902031008060103080705070f0f050603150405 73
    0x1128900075049810150f071280c4035280c103108000f034040d006070869110710300d400020a002120744c50b90f10318114841d08004c114203810b000702001602a035010314101c81d4000d0468483d031980c040d5100c1281d80d0038901e540140c006207503036042c640c05050031800307450031700494600d4114101ea514080b41c01c45101103001440005001312940d0000100d107243c03c035016002c000c0c8610480c002407040c030007400068981c5510380c006910aaa082c0002c0c401450052402e1114001c07000d40104004000d010b603601003803410100365542e5503000a071009941c40540141295964142900400724030b4015444048480c4061080448c81c0303c00507001d0100824014425810514a805500040141a00b84080c5000c0d400d0010035404038514080762584031006903651a0308401800300101c035040b5450174800d240c000404c100072040140002802003041e80d00c40c9444060484901036284158501703404984030600c0a40740c060300175034000b0f0600c01c4074141d80ba020b002050968000b10b460340003108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 350338606 1250 350337356 350337373
    0x906030507030b061203041a070501050f09060106030911040b06090a0f181116052107050f060f1b13030305030603010c0206092a030303090d030b01091d1003080309 72
    0x5030310108540c02c20812900702160007200c20340b06980740240d01c0b401c5608e8500c1c082000307200c106e45007150b1010390014002c1c00a4904044501458a415600384019200300000010181e00c28803900b00803aa20100c00c82c0178295903070810000c3d0080000c180e0b80003030100b1410a0a0351842e1248004141c14043d42d40000e1818103014034486c0000104140d1909000c4c40c60b81400c0f032401101d01c00c940c1c0c900219180302560400e00d00c0d100c000c01701001701c11103440084034900c1a6101401007688030b02d04980c0c202480301c060300e8035440c0584a0080090700e0700c1c0843e1301c080e2400d100304460010710103020b0500510151b505841c034415803099020400020078041e0504080c00745102102050000381800c1c00c105104070354499400d440d0910403494109150684820000004a02113000701126140c0c00c03c0f41c101c039222203900784514046407522160f442c6070f50007101c020088601503801808140035082007628040343c014003903911a2034103900840050b010202440c00780000740000c20800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 350339856 1250 350338606 350338613
    0x8092409010605010302130501050a090b0a09051203070c211e05010b040b22020702040e03030612010911040911030706091706060904240c03050411010f170709090603050703 76
    0x1035090783c0100307042500400107a94800c45100840003100c2c0c0070710344183d660454a40481d8503034000d40040440140002e120f5038040d0303020700c0d98410342d0340c03c55190380d4044d00d040089036207210301c5800501d020500750041081c21107040407101e403203070320260880d0704801581d50f102c508103c80d8000e0f000150940485401c0c01002d00c00c141e0202030507a4200300c91a4040e002603003c1d40703415003800b4202850303100300c0003411582e0143c500f03075035002d00107001020100782c0d503540740e030012100c007401036103080b043d4160100c1c14000d004805410403038030b4002241c0d000078000600300140c01074800c926038921210440d00c2c01c2000100501c2107507140c485080c00d01848450b407140f4084016545d5003c034050140346da450342c0007a508554421310290700700461030030181296074800900e0b0311881c540203c440d640e6030180c1099110703511480d00c0a03181c2014030015207154080050304000038803240d42180b9108001d9401a070042e85608000101d141e03100701d40b10548100d0342044540b5041180c0c20000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 350341106 1250 350339856 350339861
    0x1509051c020307030e1c0507330504142707030e0c060d0e0f0a03080603060a09050c130b0d060603060c050316030c0509060706050601090b0f09010809240901 69
    0x1640d90351000d1403078101252401011440e20316801c0c0d02c61002894041d051503c0340d10b800030728661181c00d80d000c1d00e6480c14007803c00480c1c015070101c81c1d41030500c040c0a01134401d08209401050b070700da4a00b040d04040000c1c181d54416480c01da00102d04140e5010368515110140b108202142c144407058a03101c0d4005055034180880e884559010950480c0c03d541c849050701d001810311040040d2001418500c1868a6803500c003094860042003500c00c10701d5480050303d0721581c4194116070441d1a0444510b045401014014100d9044014406818501280c0307000404c039001c113000c54040c4d08a0002841d4000c0c0413411203800356905000c204110707060003a110051710504001e821460112000a0f20010410300e65080580d034008070103040e0301175010344000210150540346c84e08210b03c2c0c0700e0000c160944903180810303840c0c44009650a08001160021034003580b00500700420f40c03006444203100904003142c540141301107043c5411614145c04000c00c194041e4240030b08245400b01d08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 350342356 1250 350341106 350341153
    0x30d02011808030613050117150c030a09050c0a080f010612020105030403120e0604140f060606160201030e0f06060a0f272004080706031512150905 65
    0x559040c0510080041d201d030151060a0303030841d00d0a03589948140005040e43c1009004d11241407078a0000f04100e20420300074580f20001c0d004a851215a01a24504111080750501c2060360204005600c29a40750000c3c1d514500c0781c0c00b2204882050800034495074070541040d00c042d1305c596045100a0000d0180d103000705816010b922170803c3c1500002e006210060006d0140401582d086803840000e50040d64504882c50540f0090304051408001041d00c1d9201a00e45104800c07048250300750100340340c0e0003130000803d0980350488030710682140c0f1034100f006905059445001400c62001442400304510200018168900e0300004004980b4180e0704100404c40200000707021040d01c15113401100101c100105132400c903840402401b070001c8440a0340a6a8042180280300003800f0151080d150b509095511164035500100d089805000201b00300c040110303410001d0712000c111340c0103000d00500001c012600c0303c06c8503000740d40500104070344030740c800c00f140e940d0b00211065203038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 350343606 1250 350342356 350342383
    0xf0306280506030a1704030f030e15090f01031a0d080304060509030a020a02040f270510021c050a1104080607090909050604140705100e24040b070213061403 69
    0x1141d4100721012950703504110000a00d840c1c0380303080381e5001c2080b1405a40085500440032a030072016454014032000404102c40d0255400710100400310130624103407603103504054180c2e103614071804011806030001c00070380d1300f180000e00609203a035150708444c42446800348491275900d0030240343c01812640e00902445080e0001c1c00f070400150360200340c0040c3c541d01102c01042e9901e80101040c010000342400b40d180004040c96048013100c144000c0e031516006030706030795060aa03203961005900c0f0b20103041c0c0b200d500c20040180e62521992203160800d030000c50000351452286143c0d60036a1040e006141181c0c8410200b1020550003c564005000c240d1802c1c444900159582d5030368101c050402004132040e54030131078280300e041042038020500105452f4440040c9500134042641883d0385a021b103d0b5180d640c10256001d05144040d000320705040751030540307008000003041d000725030104d13402075100200d9060170841340241c07005800c03095040d9403500c0d007030704c1014501908650940d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 350344856 1250 350343606 350343611
    0x2180406080d050c0c04020307020606040b0307061b0501060806010308251106090f03030a1701080c01051b0a02040912031503050c010e030114011409010602160b07020f030628 77
    0x240000380c40411250b421202605020b9112901c00c203c05003888805014190414400300801004a80c0024042e00031801541d01300001400311040c5500ca00c1240268008940700d14401d11010040840c1002081e0081d00001440c5c0d40b14104503081c0042a40103854541c80440c030529041d00d00b002000400d10581004900588a6075503a14412100391a1502c00d16000c05e00d52000d449815500402410060940e6900c0e120bc0402410039100146100e40d4955140000308080ca030010f107005d030304d900503103070b203428400e4404040700703c0d100d1070b601290fa5004400c0c02000688a5002d01c281031817050013003000c04110850300408507074120f44a50700d40c6201000c20000302c0c101191851801000386414606814403901007405407204603045180d191001e000021700c010340761055081d0440403211100141d980d10360490faa001000c3c0c0300b124601d4000410028421400010141c0500c00b910052103424030800281c1401400c0701c42e0344070300ca03007420040318000b5107282c0d0000740303143e41008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 350346106 1250 350344856 350344859
    0xc03110c030601030311010f0504030302130b04030218070215010603290f040c03140a0f05071d190b0a0f0912050a1b030f03120b0f010225150302180406 67
    0x2d65880e4180f101500b0301c0011000882980d10039000300c0300c000d4148505208500341031070b005000f1b5202020340e007120041c0c0040881c544002e00211003c60381c006142d10249846e55191000a46001d03100708203501c981e4000300c0e0303012400320215000f04800e450028800c0d12000740803481a8406c000601088480c0050b403500d50707103d0003070142189042d2800105400c1007401a00140306150003d240207904804005500c041a040384c41494100a000c0c02a5280c50390291049039140b04d20700c0c2440b156000415450410600c00c1c1480561a80d198008507641c2001c0411076200134284000106260b46107200ca40e00300d200f501c01031007003100b00d0304031040944419494551a0b01c000740411180c142d5075050040c2400f4840c0070356003000c1c9054903184075240183c4016107542c02565000d06280c18000d00b858010166404c08206270050400c410f018044c60f0205150f40480c04051200440c000c00d0790307400610410381120f9651401030713a5082c000c150341d4508841c410914404e41c2010f00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 350347356 1250 350346106 350346109
    0x1080703050c120727140603060918070302210601050a180b27040b101203030203041b06020d020606060307140703050c1b040e01050106020c10050c0703030c03110c 72
    0x448141d000a40c0350340c0b0054990900c11605c0589441295864a04212503c4004603514100d0804c480f01e1040700c00c00e401140741444400d020464000e0b900030f02c8980020b4495804000103022481d1260a42e4100e517201c4e40020000c0d0700c103001840a0b480742600d140c8414104108040c0546070490309000300d1031800d11202e516030140300307270b0701e640c941c407041e40c04501d44401c17418205801070040e50140042101012108529044a0540c2c40c07103103100c00300d030400315540401401d03a000403a04d01900032058030290b0180d8805003044481c001c40c41d100c1c0203004021124000901138039805483c0180001400924188014000764400c1c00c00300284004690408080301c902e00d0000041622044541001d5030180a00341820740c590180311001c2c44043d014400050701071504650030401c0c440440380940c00c03220240542e401503880110104540d1414018585250b5603a107000791a1a0b000480c0c6414244075034400c40102d04e40d9900c00c81015004510b043c840003c7c400201ba481c1f80e01d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 350348606 1250 350347356 350347381
    0xc04050411040222030605090d0f0210020a181404140609040b0c0408160e0705090108060f0a0807091a061318020f0a0c0c09060b0f090604030c080a020108070305 71
    0x41414811a0b000440303980503100c004561692110510982584c5961307810180d010703041c201c800d00709500030042140d000600a80010051407141d60050450f450890f1079800250b203c1c40c40720b42031081d9810444c103040300c6a207880001d000c1e0f80c074400c1120a03446041c84180d0703440703040c0c0020700b00c031031410031505881c1c1c046010f40c4560401c0896409440d03028140c007291040703410031070f41405458886c483d00440785c1400801c80320500840091a42d44840031202030040e18a81800111243d0105010389401040108516030042184015a68404c02c41e840d118455210503880d50725041c41d84084580c42840503001001603540900e043c500ca81611088100380c0110b00d8075015500f14415409030690686880d0740090f102c5568030b41c0c0880b809001c1040b088011206000c44490105145445e4000c0c03800b110140c04036107050100c8015420b04a0700300402c9590004414032002000c2124641c81500602040d00600118903850000400e40e070401046141850b040a0034024181040d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 350349856 1250 350348606 350348633
    0xe13030c02040b121e1507022a0d050715030207080403060e1002222312010207082d070b0f060102070509010f0509010e1618120609050c040504 63
    0x440d00096464050000145440260b403401c0a082c803c44172010950f02d0341e02c00348142c6800c00c2c4116050300e048040c1000154804a60391001600710f00300003624a8030b03401001000c440060210002500401c022881c1c2034400841502c2d070b035200310341c10040d448100140410003201d0f4a001e41c90718401e81c46240880c45035210080ca4103039104006100a102407150f0104080c0c1c0401c2035540c2c2e001c0c40c0d1060f500310141010507003419071000c0d0004072040030205580b08107801c40e840d00c1d1300490610400044440c5056210400c1d5000c0140a0001302c0b0000103111400c500f80241d50000603012441c43c01c2084a00c10b4055000b0411590780498400b0a820303503c00b448001080d01a0354900040341418119440720f41c01041140001c07900d40044840c0c4800d8400544040086c0ea0761040070600c925400e4a440b681c1d0040520350003003680c41440302c0c5085c06c0c0391124041a8036038402d1024454070386044207680c42d0303554040e0182004000d002e55030701c104c0102c40070300060405844210100100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 350351106 1250 350349856 350349859
    0x60f0225030212070c1401181403031b01050702060702120d0c0509040c030c170103110105030403090b03010602061b090f040b03011e09020316031502030a0204050d0501060e13030c02 80
    0x8102903041054400c00490b0000d00e07a40740b0311512034000f490b00d881c0702092801036802c80c0701c0c624a040010b52280c04164030f0900301d001c0c0b2901c50b17854280c0c0032502400815246130540003c000c900e051001c2100c492004e5100c040c00082d0360301d0000c1000b03080c038002030305c20800c54020580a40d2450b49200642d240803001c00e2000540f110100c03016109407041039080d9801a00309400f11082e140c041c0d000b00c40320940c5072501454003041144084016900340001490074004004c11481544075a0155030300070303c0390030200744013a01c0711038888603900243d11841c01640b2a20420000910420364107840040c4100d51500307051094000500f20407031190300d00e0080780e0741c4c002c00406660940000300c0071000301d9064200c44140c004c41b14054a61807000b64064030481a01001d08128016078200f180d4000a482e5003075010100313018040d610207001480d40b40d4003032002081580d1b82035030750786c0c54511410001940500d0080026002c1134018410300070380921190349008603403c0030b1404e0340f0b00e90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 350352356 1250 350351106 350351167
    0xc071514040e100909050616090b1222050601150504032f15030f0105090c0d020a05040509010b0901120606120e01111c0b06040b0d09031e0507060f02 66
    0x722281d86801104144e844440b82c0380c2010a40c009001021030075a0086540c0b0640402440c03a00506945d2520b4510422910300001c106c80300300c03890f29004007a0401c10420300c011442955200c0111811315208003a02c494106400400c804602c80c026011454500e0401e181081c0c510380320800703100c09100b00c1c180d01198400564664406c402100e200340c1800402008400c2840701070040703107400413070b0b8900d801c43c21000082201d18184148500c501081c00740107103404030850100000c1d400140e51103003409400e201c04541c1d82c4d81c91200078044d180241d002034036514000001071598865085c0c60104518055050202641c024401c111100042c07801007400030f44161968010400413440855000020609003d030040b840c00c0c2200e108a000d0060100b0351480d001c100d580d101750f100700c0ca0320030f0b01040000321451040d0480000c503800b81c186604c18049010030030340707019440900000001c500052001c1000b205206500360380481c40000c43c00c246000140259003107000700114010034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 350353606 1250 350352356 350352361
    0x9150d05070302041508012003060d0311010c0509490c080c15040e06041d060109020c160b120405030f0d0f0b370b0c071514040e 57
    0x401c120840c001c65000d08104029400101220ba8440c40381c000c1a6665080c41a003140001d0f80a400e0320040ba1001c1c031441c0381d072b11598100b20711140940307022800d00051040080920a080c0305100303c0501980311640e890b4000001c200018840b030b045c85002c070f0740d0700307540344080d0b00f507540305141110f9840900407520004103500020070360040c3d030050100f0094000821007100215050148840a4070803400301c0c1e103401d600103c0c078002c070f000c3c055190401500090f07561030250000341c0d40c40e080f0a2801d2410911880c5a030138110241c0061060710340014000380d01420070803994000321030303a504110405081848000b1684500690007507a400300c0e0011805000c4140300b01e4940741003410103d0380d12141c0307e400d040a000384900800e4028644202002a03040c20841224000e60180940c101c02502032040c2c2d401c04c00d076030310148040401c10800710740003034000010819030101000a0420307130725000b04041030300da850903407030100040c0c4501d100d1001040320546041e501c582d00004101da = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 350354856 1250 350353606 350353613
    0x1005101202031014011e14040b03090a0b0a021612030209030a1a01091109041e090b011502010b0618150a030207060c0e010c0204020c01020706091b0509150d 69
    0x5003158165080c0d1a1001007440706480080009904450089254554410840380150b4807180c0d40b070703528801030000b44100311a941c443d000300060084130018803030802c2d4941c007040c01150411a04895035a002d86404010f0050b0081c901d9445a41d000703081d442c200010902c180c450b0030302e24005081d030302c9207003100f8940c0d802074064850030000542110720114650a080500140c1c03062005014000e03c1d002246011442c050b43d80d00e095030341c0b41980380c050350806210003005000e0a1844202405330450380c4d4520703d01480d02800d00502d486182541000c4d007a611026501d8211000e680c54125a984241c503206c00f942d411240c412a42162520400f011561030309100d030300022480400200d0034201500756010f409081d00900003040800302815040d2282021a4500c030702103414850340c0e0005241c60f40080962061800000d41031100b2035803280141d8031880401ca541c036180c10010200608007440c0c000090104480d0034038541404000d0300c04015102c04a10301842c016101c01090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 350356106 1250 350354856 350354867
    0x9020f09012006090607320c0708010614030c03060f0f0c07020301050424060b03130809060c07080d03060501050909060105091203210f07030e120f0301060f08100510 73
    0x58005001c2c0d400f0391510411a585805040314817201080d8841c1104404004141480d80840f8403024441460170aa0701144e91030f411000d140300c0a403003980d030080792109082c001c943c01821000380604418038140304050614903050b1185005c1d60140080089072045036190715089045900c0700700507501c418801c0080e0303216081d80030350150b007400288400c1110000c8034a65140c11400c540c9440600d015441041d11102d00c110710403441d06001041d0354942c10b044041105114544d10f42c54685144082075068000c503501c24841d4210303040400c60244244078900c94030180e4901000b510303003040700280580c021060392500500e83c13440001d000d82d0180e0116150307404000e00b07010000e8020500c03180d40742c1c4400040717003046e18000c110400210581220341d00440c0380b0031540c2c40325038500c94106c0082c800c51000c40002c2c855000d8a041082d0000c0052000c420406003c990701e606003140a0503480c1e64400c107504001c45442000f511510804026007904d20403642036401c0309200c0c004640e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 350357356 1250 350356106 350356157
    0xc061407050307030e18040c03021207030f1b06050316050f090d0c080f1207060504022b03090f050607060f0213080a1e0203060a0b18070e040609020f0901 68
    0x1d8440081d00c0030a05800105134041c50508440d00342e25100100c82d400302c569003d80e0010040a01c501c0148018603040001c490000600c408440003940e580e103c40c2814210f280050b580c1c2c00c0c00c40b42640051408100c1c000140c100c43c1060b614500300200c541c2108203440a900c0d00700200811040041d442010840385c030300780018000038a00d000b90030301c038241460368031540f0591311400d6136105000304003250071506495034041d02d608160143c3c5500014001c004c0040741d22441210b01841416a22041c024114080391a40c03041b2003280e28001e0032000b0a41c01800401181d40300404c000d54815088030529580804040b400d242404502e0001e030040200d40d40344051006008a601c403000a901085580228400755007401c4881e900301440000d460081d41581019000070034952480d004180032000c050440010300742803d07040082c01009030707600310001e01c0c01c4041d8680f9191a00484001d001c0402c02140f0b00505090814414071450141c18142300c1911085060308124280107031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 350358606 1250 350357356 350357363
    0x1030506070509240d0b030f031e0403020301020a080f090703020a03022205070f02010f06240c080304060c110c01090611010b0414160315090f0f09050f0c0d0c061407 73
    0x30402c060010412142d00a8014104d52611b401c001c00305c40d140004102d01e00d0b8008001031883c00c2d00b441050640c141c40e88802c03e413a104100b00c0000140c40920003000c28030203d0380ea100d1141041c11080f07800307403405003c40105900c0300106001507135406102004503a4110b55039000800e1030006028045550f100e00794641345800e040040f80c6811101c40b2120300c100e0360080061403040c1d4801004c070340150165010106050f5100c40c000458070360905c05441803030600c010888199529520709034001c4504a8052351103122555105411000034080010350a0103004903518a00000706100c1061240e10708104041400840c4000d007944121010a030140040c801c0e00c1d0301c221003030750400b000d8518802d0002c0343c8540f0300034a84a4402d00d0b50000034406641520343c81c042082c0d0141003410710040c60300d596141220714032015481810902c61045001d404000400e2184904046900c1c1c280c40c003c1c1d03a0480440d000034204940e81c41034800e0343c1072802c0b0081001030b01032030074010440c005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350359712 1106 350358606 350358649
    0xf1401090b0307030b011e170606131d0f0f031c0f021c0b010f030b091609080d0905040f02070f03030504060209032a0901030506070509 60
    0x301d40180c00203046824440d101e40301c1c0c0741303001400e910142d081e003445141140c1501412442100501c80350441c4445851885881f9403100802407400384182c084082c00e200300c100e01d500ca012a2003c0781d02015000b240781c9580360b80d5415440c42c142940c8105040030b0102d1000208031803054140c0e101c00d101da44007420380300d1702401010143c1050139400748000603c0100301070181c030b80c4e4103520101041804078a07002402d2000d070700c0c000c0c100b050704010104d04251150b1180076007043e903041200b440d00c034500703a040343c141d80181c01c0000d05001e00d81c14020503940c441d003980c0544201b180d041101e4000d12001c3c0040344907600c0c00501204d0b400c40b6180c0400c0c042c0e8003d8cc1d01c94010030000d440c042c0103800207828401030385101400b490a0b444100d0740304c1c1c803010300030760340031001d4030582040d506645a2075922640107149004101c0001140301498503210700d00c0c40c0b0300908500c0c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 350179856 350359712 := by
  have h0 := BRFrame.cov_init 350179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 350179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 350179856 ≤ n) (h2 : n < 350359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
