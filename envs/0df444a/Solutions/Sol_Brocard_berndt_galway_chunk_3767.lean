-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3767
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:36:36.757574+00:00
-- url     : https://prove2.me/submissions/405eb7ec-9dcf-4aa7-a96f-9cc96c091307

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 677338129 ≤ n < 677517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 677339379 1250 677338129 677338171
    0x150207090905190c0b040e0a0b030c010503040f020a0306090303051e0121141207050f1209040509010b04180b0f012702220303180e16030603050102070606061403 71
    0x780c0d81c0903c0c2e080d1500e0800000000c1c8080c00e05004101510f610700c080b400f01d052290f40d1505441400100c148281c004c50b0a280c407590780b02c802d072503010741c200006011841c80c0340045512807480e500080d21450410303455005240d0550804c90150715041c1d05111641e508036940265203600303028508074008104421044041c548a4645c3d5803030003040742c001d40c412429002403401c003213481c00f890305140205039103081c41401e000d030700c01c540c4014014180f54584940c0c42e01d0203201e00f06a5074852503560000c1881c02d0025440341a40450240080001800100d004141040390311022a42100500001002c0b43d110001c030604942ca080f100301c0428100314201050002414807038100251309205207076203048180c8240300d40d40b1001e52003400c41402c42c01c006000301c0405807c01741034a83c100e401c200c21141520001c1c6c0c080c3c0c18001e80303808030302d0400040300a1300d020303403004e0502e45c0003140940a0000c10342c40401224400d403103454400121402080356030100326200856860301d102c020b09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 677340629 1250 677339379 677339413
    0x220b0105060c121306080a021305010311070506040b0a18110607081207050909011d01090b04060305010518070f060c11010c0b07030f0b011404090e0a0b01150207090905 74
    0x162074110041924003040784045400c0c11900044c441a506001402c000c006903600001c041e41c000b01003101c02d500c0c0140000080110b60308902c5500e04050b520350445600507101400d94070095484405d503411402c01341000b500281d070603039002d80d0540c500350201440c007000310b60400589038400050380303240f06803404000f031580280c1026038040780d0402002003400940b19006215103020b407206600c83d08080306008851005801644602075503003403010b00c1041c4516110304448121901091000d80f0381d000c00d01500d41640001c0c155820030040c02074030282442d605900207090383c104c07100250345031001c0300b00080921844002c00c2d82c0b15480e1010500e01140018801010704042e2450000c540c0d48060a22080702c03801c000a0761900d002243c25214010800309032400d107441e02d0141f69140f1000103d109610542e01c51640c2d800d0b003501c0420051000c0d40b036081c1c11540c20006581d5505000307074240781c0c000c0c0420041c000e0040c0840c06103c948160001c05400000a04546081ca40640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 677341879 1250 677340629 677340637
    0x1005030604060b06120c0a020c0a2612040b1b01060e0a020702030a0b1611011112090708060705071b0b042705070908010b0d03210b1305220b010506 65
    0x20742c00413401c03c85c1004030041d0354040381c007510305e54859a54071411000d0090624501d490b405103d03641c3d00104205a581920030404140100c00c803100408080c155140e203014940d00120341002d0004c01d002403800700c00f0010700a1100f0110b0700c1e43da0440158038030740c22500d00340079180c0c0c81ca0795100454019600c40d4042d05201e44050b0032a00640b0b042d44810049420480e0b180000c114448117101103194409001020140a84000c3c05001d41080d00000103024400e001520150142d001031b41c9200c00300320755002000441e090395401d00348280000c180e81e0000c00b003a18841c904814030103086100d4041d03101100d0b40030000c1c600f4107050040114000d14242100303001d0310140c0ca51429420014480d0724040d00c95500d802c81c1d01880e02c20081e0a584070706000702d1050103445012070109802401c560f1469000ad41d10034074a0008001030340045c582e0b440d00c3d5030000c100f044041e01e01c00b810ba0203140034000c81710700110a04018404180d0001c04030b64001c00100e00300d40104243d04209c4050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 677343129 1250 677341879 677341901
    0xb090a05161a1c06090506040f090b0c090109030b0906100b0c030403080f0d060f05040e060f3904033f020109080c060412110307020f0a08030a030f05100503060406 72
    0xc0303d81455180481c8084d2041c0e900070100d031a5070b580501415240920419041d00017105007400010301c261240c0c0003440d801451803135a07281c0010a01d0f0386030301c10003015010399441441410b084c01c000100d03d5071040101c41580409145400104928a415040e0b0f00180c07036250045181c9411952000460317003000f04500d001d00302c28041030100300c00d103001e0030010381980c1007003194047c5000e040006440300b44941c021702d50025414440030b0b040b070100503075100c10341001c407400d103405a035000e1044081c102d41007542280c140d24200721b198044001007044900035181522040603480b50711806856107540c01c6614908940113200081d0382102d042d0ac1e120185c000025124000d803a204d02c90303440081e510400750084002c110801107407413501d9011445515240f40001a6290000d6072840307801c20207482034100c006c41c405156206400400640103880a99448a22107035020303000c0e001c1001d0603d0340c03a00f440f00242c94050721005903811038000030010000f07034540d034807420000d1074030840c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 677344379 1250 677343129 677343157
    0x60c0d090b07080a060b0a09050d14030d0504050c0a0e06011409030d0201021909180906270201030c0203090607031404080a0f12090311040f090b090a05161a 69
    0x1900011410032901c0c0ca1140030b0399101c0c00501d1910190000413243c040d01312000c032910501220f41411f80c011480400e8031000d44800a200001e400c000040c8854000c12a481d440001100e0443c441141c00c030341d0180b0311480c1241c411280c66020099214000d0003000b0690310400005000e540c4152400c8070781e88651003400c1c0c03401d0190f8000c039090a00c4a189000943c1d000607041d40803510340c17a44040c89407000e02e09800610f00342643d81001070740003042c9407803840d1640b400f9000d101540d07101d034000101268110700702e46044001400a0b0504c04000c0e40444c1c0b4110104000038008000c40d111000001c0c101860b0200581c0c060741d4000c1205110300e0b4120f401e1002007400c00d42040285100d5019046006140740546031003002e0f82503a994036010060b0810381000000c50007001040550740c22640400c400860703602c003000400104030058003001554041c414142000b0880128942c00383c0142c81200e07030401d56420015850f0300c40c041d4400c80c11aa1326500b01d580602601c201c00d04102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 677345629 1250 677344379 677344391
    0xb090a0f0615090e09010501140d0821180a02060d0905211c060506041715010e010602150903030703110d24060e011d040e03070501020301060e030708060c0d 69
    0x10824420750a0030180b000300e54080018000c0949440565500c101d04d940284420360400328100e42e038042e08a034185c001d201c0d0100440800c002001a2845002c040c0c21810310400c0d084402d202144082c3e0f101194039100340c00300c0441040120f0100c1080350050b10080c5021100c0d00c0b1100142b03140c0e00140c400e0300400d01c0d0b08010034001e502c110fa131500300d11007440c0c40d40eaa049a0505040302d910fa0081c44503c1e0000400180e1503c10036582181e00c082c0702c03011a070b540c0000c5241401c0400b402080c00c203a54000100300e8208017050a8141c1c3c0c2181d00f2a000844020f0341d010001c441929041d4080d0302c1800040c032054071903002009680b00d032240580c1418004110281600c46500711742a01014011201c8285009a803140e4001c0086140054205404070000380c441740c4544611840a1503040d89880340d03440f036822052850000030200da5442e07006041c228000c0d0001e0045e840000c20285509180303260004800d4280e5200102429084e125190400c4240e03010f03c040000c40c0707031202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 677346879 1250 677345629 677345639
    0x30c02011101060308070b15010807020d080c040810060810150e13140607020d0503071d120d08100501090e070804060f022701030c020c01080c0c031c06090b090a0f06 73
    0x1011b88052481440090b6650516443c0492508050742200341001003540c1001049680050b541480107420b00741008203031560031000036a4499500808064820300e045000c00000c29031107401116040341c1a60004c14207080c81c5d500341c88005071010340100110400340042041c0d030844940000044900c0307100094190340301e8119011142e107101003900100b0404c10300a0f018000c000100b41e051a001f0301d1403406031805403880703040718845444549108003580310b0340c41e400e418603243c051410072100d00e42c000003802420200c0803a07400710710203002080000e065005404006c00c2c0c07100003849000c40d640340402140c0803039000b0420b49030141c0700c0d04040140200c0d40300408246140d05901c0d01110560701110790301440c16000e442c1007503d0300c205608800d5001c200003200c0035007482c0000540d1070340801c0190030b000b4101c038007800380000075002083d400320408904416000ea4000d0000f56625241e0f08100c50b040244c0360b030840030400006042e5043d0303920040a480071070fa000a002d80e00c803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 677348129 1250 677346879 677346893
    0x20c0c04050408030f01050a0303120216080c01060305010f110a1407080f09010e010807120c050c070608010608090c06040b0306191401021b0d1e080c0102090f030109030c020111010603 81
    0x1030b01c05581c00d03a0b0010034440d040c141c4d01542409000b09448001d40b89185030740051940729482c0d26041074542c041010510303c84c220342060f10035900302c900e15480b40441c004a41c000e0801c0d10044403507628103c00030418100c1c1c0d00598030a03811380d03484a1b040c01401002511162900035040220380d0080150b18001007813080544580480794643c2c5884070010b50001d402c6010340580103050003011800c01c80d065034003030001036100d0102d200c0896482c000940c01c1e2030a002e00c1154040307501426601185003030740880135030304030b400d140c0d211209919285481034940003503864080c0c0100d001c01082c4020301c03c01c0700844d007098028081c0e540d02b400000820380e0050300c6400c45070782401e0720b0840b01c481c3d69042100d1f800c0d100c84200301513803285030500000c0040044030070080440c9800c140204094641c0c001c2c00800a0b00700c404a41e0740d01c0710700050381c003e51000a225105402030780c44d24845041c1482100c0d202a456241d0540703002007500151172402c803101c45601c0715074a403900800000d2031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 677349379 1250 677348129 677348131
    0x90609061011070902040608091f0209030a05010519060b04080601140f030f01060612020903190f0507080d0207090e0312100b181302120c070507030c0608070906180306020c0c0405 79
    0x1301d0f10040c2c445080040003032030900d000d400e000c1e180d8070402c80056580c0d411026140526104180107030348001610119090105281000e0920351a1008018808442d0300d0603c000b9050450700b04007194450300120101c3c0142e0207019080c0c1e024030f00601000859240f00c265091000b4500300301e042000000a16203d0240104404c994581c0410007196030001084402c044d21401e0550401c80c0c080007080e5150380c0004814100c0a66202c464107100750034280b4040a42c114050714440c940f9074582036550142481710000602c130b02c0c040040c10710817134442c40d200c412030034014510f4400384403241104a000508505022800702d000003c205c1c03008802000200c400c01d0028680918074002c003c00004401810340480340104200394415618a0045500c01420241d0684509445c1001450481e264200030445200d55a020810a80000c04140f00351016601c6452664841100f00c500da4030201f0159410210b40400b880040d02e40e0300501291940101201d0000301103070300050640328 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 677350629 1250 677349379 677349389
    0x807060c02060a05090a0201080406110c06091c0c1211010f0b2e050310080d05121e0c0703030e01020a0f020d0f08010b16060c0f0e09060906101107 65
    0x140d1854405041501440015400440d261003000b00c0c0ca4420142601d40c040600d00a040000d90740c0041c00b0006c007980109000b29100c0342c002e40329115210915912482078410015078410210014002100b142c800e0788000d60696400d039902605e40d90f08a1071140807804841840241080204040301c00d11600b100b00240110100304100b03002e00340007810900c034001c42c620701c0c4500c400d140c1c0d40d80145d100400d8201d1134a0310075500d54825012150404460304001202c1c0076a4001c403001d9030b030000150441814442c2d42c00750036120b2400305500c1142c582c101e440c4402d0380c0000141c0102c80c8401520707d903030081c02c1c0800e442c0c0e2100140e9003264000101140801c0b03940c00e803021415410003080f100c280040c1807034035299a20201c080c0518070144908070000c180003a006640280c074140e010890f0344c0c085410300940528074009000c040c130315401400040d600d003500b8000381c40e1034510240608070103001068030382c0342c143c01d2007844c4074400c440c4800d11541c4803c4001e000c1003045410000c02c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 677351879 1250 677350629 677350631
    0x29180c1312020303070308062205010302041107170f120f01140603010308091005071a071e0e0d0323090103050a14060d0c1206200a0507030813080706 66
    0x1800c03010210a03060060308800400c03280100600010b071000003c60348402d81505000c80f039555080b0014825980740390901922011901c1c502200c1e6045800880c1624400c443c184150902c0d10301c3d19010b4000c0d108080d04a045c8410043c4200301c0b0314008150b441010640203103443c00a0705444041581a500c0c00c1c0441c900000401528507910300111080008650aa1440d4990744440120f4054424040d110f81c40000d0082c00240c090320071101000d6000280d094002c29140c030358103180c4c0081310782d00081000d8104501480b082818820740c0a8407903292014614030f20302c20303c03003400c20411782201400200c281190390007000190a101440308207030501d41d03441e148000141030700d0300544040c000500300440e5103040010703070b101294000b009032034541201c0c020742030040c03c0005a80c016480a03404c14540e90501046070444603812078448a10348603142c02e04500c64140c81489481c4000038010710840001a1240d44042d80101001681d1003041002c0e44854042e076200c0c890441c0d4403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 677353129 1250 677351879 677351887
    0xd140d1104030b01122003030909150f042708040506030f010801231302010201060321021e0c011b05060a020d0507031b03020705010608240a29180c 65
    0x144124891302500452140954200050340e03052040c2c404102c0b180e255603088480304540d5102001540c080f91b60050441c07001d81800f00f4030160700d4011120541c00340004242d01da080707007070a0041440400c03400c0c0c00e4586400c220412001d69000c60340b01101d0070202000001440c0d40e030440610700907200740000c0304003545040e420608403606d40e45070b0034142c1b070007500101c402501c48003070540c481c0b00c40551054171005803004078010680358000800340720189410600b148841807c954030a161502140e00500c000444804505000d42602c15154440740b03210103030b540710b80c1c100e240d40c0600144035040c0800c141d4916040c04000c48040304800e5001ca1300d030f031000000d8000c4a41003e541d040400554141001c192481c600340024002450780000380c6004000d802d511602c01481020140c841003009a01c06020815544484040c0b40d0721003000300b01000594450421280d501c00140318181d4a040d02c2c0c440e1100e03207403c0c3e180d4402a2840c102200d50b100d158110302c038092004000359a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 677354379 1250 677353129 677353133
    0x13030305250209040308090a0b04050c030d030e10270b06090c0304020d02060306010c0c030b0708011e050d060e0a140105010b16020f150a030504030e0108090d140d110403 75
    0x200c08000c00750341c46803940101c140300240e00c0307a180e8290401d80500c0d08501903622049000c7c0b0f032080202c001001c001c40102000f081c40700200d964400500103d041d19190f8451380b00407400c0e0f031131141080f400c0d44c00009a0100c02e094940c007080607070401c000c5132000910300d42680e2503140c0c00b0300016500541c844041000300c0ca0030700380582e070025940c01c100f811803d090b0045641c6000c40c1500030b02890001011800320380c061144043c000d0b60200c1d0051180d0b032070340f40c03d01078500c06580c1c0300701240d8140e00204e40d1070030000d452106010329880d0304a001d07151408001e01c144080e00182d036100c0e560342c0740d90340307081084c0314a810300c40c010040034091001c224203003801c40341705900c40740c002c00c000c0c854003880d558050720400145404444180b1107418001c00200078403202d80b03040c2000c10001a07400b808a404d40c02140c4078038006d03291400c84207480401514600e00c206e800d0780309030b041070041c180300500034001744c0340280b0203c90180c1040003d8207084201c404290101c40e07000008142081 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 677355629 1250 677354379 677354407
    0x90c100f080c0c100c030b1009080f190b0a140106020d09050f01120911040219031b05040e040c0801020d1509020f070206210a06051008010302060d020f13030305 71
    0x6000b04044044901c1d10503994400c68940008800041c0e0580d11075100000d0144650030442c01e000000b82002607005d201140075141d14003030301c070340c10b80d0b40600b98040050341c9010668142e0b12040032080104441c0c0d5075a1381160000060103100e040e41e64010b070300108403500c000c240c0a480f841d00106600e086144018001c0001d07540468443d0310b109600ca1603590f40321001c506040800c03440807544020b40c0c42c0580044809103146da400c80e00c0401c1003200891404200701244a058130200040e0b410810401c10429041c0031280c08150100001c203d007208099480da40b1600440c04083d80b5a00c0b1210305003a83d010340c841c3c0c801207448100d40b11542c80003641032401015922001c6103841240076442d0300502800300b01920a4402190b0808144440c800200220f000d000b26010b83c0c2c07801c1c00c801c2c0020a224002c8038000c22086075039010303060080c01500d041e00d800400302030801e4403811002d03000e503020354211070b10b045040c0000041e0f010b00e44c1c680c001842c0309440d04e6480d021040300c906 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 677356879 1250 677355629 677355631
    0xd150c031d12040504020d11070b0103020a0f150e04091a06010906020c0a09110c060f1503150a0507021e010212070503010f0e0a0b060304060c0e0103021c05090c100f08 74
    0x30320740ba00012401d030100442d81007180d040340d134107403800741e01c03225208125401003a00d000030030380c482000210001045400b490b00d5058902c2180d4485141d910b41016003103182c91802020b911490340318186000714010030480c101148010f002003500d07051035507000385e40140b40d0350f1032060100000c01e000c0f50790307017001444024010a1004040340601000002d0707000c6014400c4000c566655484140405140c404450002c000d5070210744060812004102d210502129140c2d021264482281141d1a000c44c403440c038594500c017018025203814400800400000c0c00d4001548281803142d020201e80011048240384072400041c0c5812000c0c0624000d00801040302007000b50420040c080303108610000c600b41c4a1111440c0125070342c910940d0010404d007078840381d111101004000800030580c20012040100b680c5c0c0c5c511003480f075801034099000d0900c0c078070445154412200d0100c1c413503920190f031100802046500000b00c080103c1c450241c3c02d41045c0020303241d00c0c04092019005000d40d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 677358129 1250 677356879 677356931
    0x131208060f0618090402041b08070315080c0108180703050a12020708060408030405010612110a0608100e090a0204090b090609030a05041413230a0207020f0d150c03 72
    0xe0701e4041c0400e4401ca0303155901d01210b2144d40c52038085001d6485c1c980c1b14010504404c6007520361540000c00240c40003400f1210100024201040d0b6044a8469001c850840e11000001c00307000d42c5000040d20341403001002d00910034051040840808030402c4084d0095009102820485072035050000c43c1820070240302081d540684002c1040440000d0000e6100341c010302e0341c80d200c1d2294038000d405085543d110310a0850342800580c10300c0200c100c3d00b0610001201c0038928141d46100946d203004085030317010301c0145105d4040203059000e107035003503002c00b1103015107501c014590700007001c441c1c0b000c601350f8100320200100a520b240402160348c1000c0030000039410501303180c0000b0700074072480c000c0e01c4944060145603d0a5115540e00c24500070445e0340900c40e04a000b604c440e4060b034118286025034020b480824000c03442842140c000360707000740c011a06e08041409000301d0721590001150b54101e0006643d8103200148500034142200c0c0e94045000050218035540d540199008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 677359379 1250 677358129 677358139
    0xe0417040b0a080f0105031504030201060509100509070f0806010320280c080f0705150a0e0106050609100e180103060b0909060609041b030204021911030403120305131208060f 77
    0x520242e90000707242d9121608c400c8540e20640c3c0e580c0b40c00c03805480c0641c4001d4201e0b03d6503040c0007031a081440c1c0b1800752041512200d810703030707241c0d113049680101c2101002d001c203100700c01140b1194032a402c40459500340748022801248041d4800e165580700c0140d620030b8102010703e81c0003010301c00d0600300d403058a070b107008001841e46460708400e0344110010030b205c50703c00040b5641080300601407000604a0010488150308c1c0001d10040a0214551902829441e00c1c00c08905031a001c420b854441402810b1454102903e10040d80e003894141c5015900a0403911402d1502d0002d00116008e14454100031800502031024040c40c3c1c0b0002d001c0e085c03550880800c01c01c2c60384809501d0760b031003508401c8200a840c03400e803514488040e81d17000a50460300024003a0b00807800580f481c02c0c80401da41c2c4a0741030910640c0c03501c0d1640a280070083c0700641030142c808a02d84aa00300c56080524a0b0515824007016950340c000340280d00043c0c40401d00301c40404c101441c00664209a4200543e2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677360629 1250 677359379 677359381
    0x20304021018051c020d0b1510170915090a0302070906030305030f040c05060c0303010f120804030321020d0e0105010e150d060f180c1a03010e0417040b0a080f 70
    0x10103503401d9850307003d040d02490110a08440c0a198085026900d503006428501840c4142c107100c18006012070311002c0c600b00b811020896420005002c400c2e001c590341c0c83d414024440c1c40c400d00302c8030b40030b80000c074603119004d0002900072100d1540350244d030790710f0004e000314042440d003c0e003000c0d038640c4410203e510f011f004101003600300c1d0440f0784c13082c6058800b201558603450320700d03814070f00780e080075800c0351012810007203014001008606031601903200118150765400320f46c1480080700d000500c6000107010400010340110b00381c01c4c1045555200000c031050041b05081260092071669a60603100c5400c00c50100082c890f0a024004520500320907190a164140080b803000624038081d820707000c00030090020b25400608100c904210a000143e400d1000a51205540806032504c040890000a003a804001c00d141d101c0d038921515820341c2e10b012420400705200420503160458106801c10700405982e00070806405d6a0f01a251501d01203940241603240003000c2c600c0500840c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677361879 1250 677360629 677360657
    0x6050f0c07060b0a030b2409041e0f081306110a021e01140d1e2702031c08090c0409020303040306200a0207090c020c0117130804090203040210 63
    0x110031107207207680056012454070302c80408143c440b080b581c000340c240b0980300140421091245c081da04019621a03e807140c418601b0204021a142517400505140301400c98682200d19000d00c03544c207602881007045480c0e000d40720500140d01034203000d940b1103880c7d0410712402d03400500d007010f070f841e040000707000c0c460440d030100f05419545800e031566494850703040d4590f03a01c85c00005190041c00907425484118100c4100d02404000c000d00c0d501c5410510400b64119140c480c40001042040ca6441844c2c5500d21101c0089440b007030a0ba01401860784c2810314041204000d038045255035903154140c0b8202044a00300401e024056100742c0c10110010302507507002041c0c406498010341d0012f2114001d507040791582241121342224640301089100c01c298012914004403400d0040502000004100c00c0b600e8070070b00c00381c150200d000400c0c0a1024200800016840f4030300382d0440c1188080f07038452290941103070b4020201d6603000001c2004508116060700d081c4055410a2220810b03a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677363129 1250 677361879 677361901
    0x70f0c15111b0109060605060a210204330e06190e0a03030e010305101d0703150f03050d02060f010b0d2003040c050f1503060301090210050706050f 65
    0x45420440c0c03140e12440d1455440720103004454018411a0000802c0640203222901130700d02408290742c0c880c600b403030002d26414003a08558141c8810b980740c103480c85280419000403507500d10800c4245609010106600c4866140100701c0000c0310016200c10841524001403c0700d60300d048003c2001045c698034030342c1c827450151610101d4144c010f049450001d40f0483d41540d0f03410700e081c0c0c0010b12410001c03c1c15004220140c0442c0d0a076001c3c00301d5920200550391031042c40c400c5c26400c540d06030f0034962443e903120002d60007001525001c600d030420241c00c0004401203420440a64904100401c2008400c100d4190018020b001030702052030195041e81268105104c2e21444040c002800c2120184581c4407100c42d601e6101141c2c2c06183e1a00000e805400882b000c8592900120000c10689010301c800342c3c618000030202c0c202c402c0e410000d020303150801707082c1a8066484044001c01a60f51072040038059070940c1e42c00d52240b80d2400c20030700f038640240c1406280d0303071320105002c1400300c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677364379 1250 677363129 677363153
    0x7121e0615060e18220f03081311090a09060f021b01110301260303070e03010b1503061c02030703060207030810060e1002030c0609030307090e0f010608040510020d05070f0c 76
    0x3030391000807159140c1394410200340c9285d0f529895981103100c0c10080000d102d185001542c001da507088800d903075605444072010712040c1c0180200b81d40101812403407610410b12580052260004184101d060760b4800a03074039280c0d24546203d4020031541c02001001c00110341d400c00e5800203124601201d00c0001d900c1c40180900004e03010105c101018000072040d401000300c4825084a0b500e00e404280200464400c1107454881d50a06032060700a11f00345006402d00c2d085200c03450b256403a0350b001c05c048040f42c0c0141c8a1200459107884026030303810300905000794050140541e458545160080032400007c080e85880c03142c5441c24082294041d510700c3d0741500c00d03614600b0b419022607082c1c2c50b42c00340000318044c61242c8070030480c2c2c3c8034002c406113006606985414801c0c035142c1d112581c000e8011980c0e80034000041004110304d0340300c1c001541e045030007002a180984042c00300306042e40d00510b04c40b40e071551184140600d559020a07603140c1104a03103420300180a15644480e0b0800b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677365629 1250 677364379 677364409
    0xf0601050607141e03091203030412030c0909091401051e07030b1c06090c0909110f04020f040e06130e06070c060605120a121107121e0615060e 63
    0x94000140f0764818410003203000d51502002c410301c49010304084141d40c0e90310114086d4022450000010422030700002a02d0049074032500c2045840c0302d0a0301280181140302d020f10030400c140b10001200701e490b208450200340181005100d0801424141e402d42c4e40140c10f141203e0311001402c0c00881b1403400d800d40001041c50045a25082c3e480018400c0c142111000c2d085c0c010400140d0030803019500040c01c082c80f0340f01381c0354015590721030841201d00300d00d005004144004008583c628004419443e9000020001414034140030441013407900903822815250b21700c00c050120501c0c000041503041446c1c0c05046c0300078507404040075243d183c054030400c144512031a140040291a42120000c3c05001e03150920b902181e1803000d968580c080c60030390701034062411780d58005216030064802401c0c0e02c00100005844c0060103642e580c901e000a64000120014000410401d006070752a1580220b1001c01d041400c0c00141b19001c00f654000c0080c050204000b000d0340e15101c4080703071410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677366879 1250 677365629 677365643
    0x91d010306060506031623030f041115070209091c020d02100219180b0c010c030b030312060d21080402011106013f030c03180305150c0d06031101020f0601050607 71
    0x100c00882d400f43c1030300141c0c07010003a2a004800c008a0034201827415100314020b20b805180035a0314024030404040c101050f400311103080102002600340303020041e40042c20a4121010400000d120640002054541e840182c001004216419604003c003031364011440703204500e44013a00a0081c18828005031581c06d204103402d00740341e500150034500f802400200000c6c0d60310500d1581c414000c04908000700e02003854134040341e0950a00100340c40e00c080c0c11450b643e14a03101d52040154650300701d00122400e02408440c42503450581242e240310070ba460701d90f101c207800c103440054004501c0904a1215034414070041040b104c42d84003502130490181c1411002296000d80803407840c0c800072854601042403503000c0105640841400d00740c40c000c1d52290b00740c002c00315002400440c2407001410700da100c45501000303234551516594014055070150fa10b0183e40c1d031040800d80d00c6030351041e41c030160103810240c01075030184250ba004c10382610107001c40750304050001d44117020b1240701402c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677368129 1250 677366879 677366897
    0x409050f040515060d1205070624060c020a03110d0c1401080618060f1309050303070908060f0c0d0e06041202070f050306041b03080d02130504050601080a0c091d0103060605060316 79
    0xe54050401c0722012500302400b4041320a072034207500c070102b40c2181003520b02500000000744040c4104032402100394000c10030071720945151145600d45800c00c44055100031a070500b080000e80c040c0040c001825240008048520130800142c0740c000c0042c4818014020015118604c07000040e042e58080c40464140d4514041c25000c6446c078090100c9900809143c011248184003000001e14807a40302035640460b80354035050341c3c41d21840180c0303285411078030081c045803500c01014040d1001c00f1008a0001e80c010700e01000d14502130040d2000c0d01d51500c0303102c00b1310b02c5903818030a8a01400d581403070b00300e0107440d040c080b9035140b00080c0060100c90358445018090624038060f00700554006074040c1c6c840d0150a4203034025032000002d03c82d1000310b10300005040c18903020b06403150740d050b101c040d8951349000f0108090503848000c04104485a0404110710030100c01250064948030324095040d0f041d843d2070021540d0642000d885107506104002d200316032070034040c011501f14a011303581 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677369379 1250 677368129 677368163
    0x3d15080402010818070b12010902071a0411040218031015060c1b060f0e180f04020d020604062c0906130f0f141303230409050f040515060d 61
    0x8403914407504c81d40310780a0b040d0005440140400603059400e88620400c010380d80e2908190300701c1c0316032680280325802c2e00081d580c940584517444c943c002d020f1f01000c20780c216184001400c982c0514034455452400c000b451541e42402c000341d4203200003d001c1040220411410b01c4043c00d0700e03100c0c034810040c0511200c0c0402c070344000c8a0b1106050044807000c19511040060601d0220003402e800041c42e00564000c2407400d1b940c142c040d81003245041a07140c9440e0842040030740020000d90b04a00034400d03090060711208001d200420003607640041c1e0920305200c190380700e2184030810904d002200c4895410b580da00900c5908a01c04440059400b40701c20012000b8140e0610700e000d541e440c014151401008580140782210032040001941d41e03102242c851f0070960700e14010f00094055222400522142000303100c1c007062101c2014105551140c0c102c041e0752048403000a4902800d00340310801c0001c11840040c5420943d4082803031419101007045040c080c40e02a051807000c000d4034070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677370629 1250 677369379 677369401
    0x27080d0b030307121709060103122f06070314090c01050c0f070303020717420a06050f06030c0f03071b0c060e03030f09093d150804020108 61
    0x808140d20661510900c4e154141c0a04281d814102c0640e2103002e440008030112008141d86043c1c1e680040c5469100e4400704017246d10003141071181c0c1c0503540d2800d5a11000342f5001611080c0c1c2c0e07040c40206264a411003006056400d1410030154080c1c1e0b10061005120740801c0b03d000c551020301c0d20315102c1c0c4020b9271840c0783c02c009041402c014000c02502005055000c1313080410b0350100740010b0f210b208080442a59000c80340c040142e240c007400d4605010860300c41010b00c401c9221309d0b03204a1840490030781130f0020300981da0300384900c0d5500c400300020705104141da07684000450f121421442d00c01d11134039072482048500071000c0800400910b41600640389a0980c40701c20800e003070400214a8800d0140c4894043e40700480c80003551640e03546000001c442520078000040c5040998000a1140110000d440324007160020f0701c1d0300c3c081120a4902c200c42d22008d40d000c1c0307a501c030030403c401c03070040c5a40c01641040500d400030144198000040715000f550a05e0404174a54075925445 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677371879 1250 677370629 677370637
    0x20c040b0409080a0306090b0a1410020f0d0302190201151809140307020f04060803160c05030609030a03140402061b0c0405070507111f0f030e01060927080d0b0303 72
    0x3c01c030500c04500710311260ba0542c00303113056840020040042440c3c400400c40c8458a52044800b03280c0e69440007001070504804a80600c84980100d941d15a0103503006400d0102d94142d0b480042c0d404a03040121483c09460b01c42000502c0c00204030320700909410100030141c50180c00c0c9010000d1000c00000c01c0d0740d0b8002507680e6040b03840c0c0405502d0b860b51503602c03076208030000c0c0e2007000700c000c010050345410320610044a00e03440c025440c0c401c282c1040e000710342e05640159a64065000b00042a86040c407461307102c1d03d00d410280d030f50744190403009000c9400b00382e04516840b1480042000588403402115800000c46a4081031a0203890546203813040c04242d140e0014200018018555004000381880c9840362060701d000e007088005000380510050340d2805844040800b010742c0da030007011032151120040c6070105001200d0315200d82519001d0740080000d903a600305031458003030b0844a141c002c0104803a0314254007416140c07004076009103d00ba4890950b10f01c61941c40381e9003003080b2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677373129 1250 677371879 677371883
    0x50403021e1002040312080f01060e0f03010f0510050112021801120b0d0b060a062303091513060f1518020d06180509030a1e0c05010f060f06020a03020c040b0409 71
    0x544d95641c40b49030035082881e60603c0d00740441c40750300108140000c00c036046c86c1039420a94559000240000130006454642410b040c1c06558560388280b100b1168060756109850b4140c8841a035807405000600900c0d5451000c58018410b00410107803043d1000c10190780c00007441c1074021200350484880080103080803007070380041440d460204200d244188588500022039049548541d0f03031300b040c2c40d84c05030444100703401c02d4036150b00785581500c503010f1a089900c0c01c080340d0340b11403a59030706141000705464550b110304007005c2172401c1005602560520086403007082c06865007400040d4a412660b014001104031141151000360380b4950645050001d01c0c0d9042c0407003070b41c075032524411b40c031000d2060039001d040030002600c5440000848010341c12076514454508140114030707410503860f500e02010000c007840480003050090142180038110000005074003450f00f103030b04082003420750080c0c00b1b6411212203400071130340128030301058403810350340850b06502c0707040010001c000ba8500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677374379 1250 677373129 677373131
    0x1f1b06060807170a170f04170706030e0c0604092a020f0d030e0307060c021c03020c0c04050f0f0606040b0703020309090603060105010c081e0714010506190902090f090a0915050403021e10 82
    0xa081001800905182141c809880c10041c2e0078a50cc07245413101481501240c011804020801065100b40d10440009c00306d110001c0c0201024030300c2e10005191800c2040c01644003c00c0208014400e008414400400b07090402908450042042e12801100170243c0903030341c0d86a8910b04c15001b40074140070119560030130602c0014500c0d019000b508410381082c0b180c4121007003240a410940304840c00350070400c0000e1110340e140000160301e55402030140f608800103000c00034400b406c076000b41c454540300c0c4d0003039900c1d030701c241d0f06100780d0034401001c0714072a51201004200698020306c4101740d035504069850b0ba68000308130000140d15004400072140c42d40040d00500f48a1245c0d9680c006041c04002071215440f00010001078034141e40280c0c9100981031300401514026600030320b0000030291003103160b0302030900003550001c01100d801d0009a110000d074810090922400700510140b108208540d00380398800030741d40c55140811aa00f400341c0c3c110b0034001c40b070800100d803070242007142c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677375629 1250 677374379 677374409
    0x6030b0f2502240c03160309150207050d0e09060f010201140f010618030201020c06370f08092d0d120b1f1b06060807170a170f04 57
    0x1074000d54454142d09070f1595910415581c042c3e11a03100320701401002c60302121401c54a840203035519160310101c02c1c0303083c56650a031740c100045401d080d8003406111040c006031207a0701424a103041c030043c1948000cc1200364400d40c052541c0f800035407a009002034444100e40c890000040c0c0c01010f40741c940544044144003007190781d4050074a4030703069848030343d01c54441451710340f41041e0001c01400300034050303009404141322505050380500045071502c0240b0a0b810000d24156000b86120380d91b414015a440d16000f40e11038004039514ac0781426490007c126181a200d803903200c20342003200e20142c1100c07a15008001c80068404a805006134080d42d28045c12054050324030036481809803003d030b0500700380784001d1620f200100d6045441c15050041102c40c100304540583c1c005500300400c1c58418110400701e00e69108020182c20028014030215091000c006c010720b0455008400b40c2d480200c1007000240c0301640880c40c03442c0c80d180e43d6100c0344603402941c61402103400c01150007100388 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677376879 1250 677375629 677375701
    0x150f0d0f0906060608090316082203120c020a050603040302010e160603051513050a0e0f0102130e0c072d0614060405091b03030906030103080a0e0406030b0f 69
    0x150040c1d80c50340c801c80c1c04010302952810142c45801d001c03a0b4031a4942c000380300c104e01c1c446101000150844c80740b840c90380b412a40e040d106105090302001c1e280c0c14030010714280100b11200698001c0010740e4140b80e030f6401d80903400200a40d4460007414007912020000c1001c0600035080002c159440b1007d4807010128181c0f2800d22200c0c91240c0d40002e41054046500ba815030301d80d40200510103010100300e80c02040700311000d0040940044840c543da020343d0b40901501340714240d6050204000980d03100f1b4070111612044042e44c01507210a4201014408404110001c40c0c403201d40c41018042e43c180509204400e4941c07980092720700f030319801550000c018565100810300d040078000c5150548070031040c041107c00c00c5852040c0c603440084281018810055046500d00c0014202c85c07130240c0d0304e00071402075042a8000c0342d241c1008034003150015042840c46044070030941c3c0810060745107841c0c603010304c0700140c0800342c2c0030a0600840c41d520341d112181d1510000681004071014151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677378129 1250 677376879 677376881
    0x21e0c150d02120a0c0302040b03040f0c1a0409060f05010f0f2604050609010c09090e0c1203040f0801090b0402090a0212010323070509012c0106080106030b0906150f0d0f 75
    0x1c035691300701c00c1d10308000004600d00910a94007076960803407a40b811580e440d62002c02412200304203840515240c1c6002a5191940e107a18a040c1d09056041d519146414038281c01d4a030315810100c8107800c29041400f1603603004580001c4810310303140a2203001e008450075036404103c800182c00300320b80c004110001490006101e0301503885481181c01f20341c0c038041840d08850031030307441d00d000900201040240e1261900007014140c101c0050342c6a440c08036000808002c4a140d0f001501c0e0400b040401c803041c800308034103006012540c0240a8046150b85090640b000108024400c0e0b00f100d0109107400410b606070341c1c18417044c041200030f070b585038140882144081a400281114051091940c4100c0412a0b0701100c1c8058120701017179007807910808030300100d0f006625032a413a00d80c0424681c51207a0a02e4004c202940311120254100400203007074034840c05420340107450b03070710a1120781c0c6c0320740340c2c034102e030620101c095a1600c0700c1c031000385182e200302080c445034a41000814581c80d41e035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677379379 1250 677378129 677378131
    0x604080f1b07140d114501080d05400f060315170a02031005010e07050304110910152d050f031905070f021e0c150d0212 53
    0x8803c6000c8440c09100040007080c003d10781c00104200e0300e0f81400841400d1485515420981442000d0006400303240c0c80d160128030303045440d101040b0ba60101e160015205041809004164090501502c1881020b0900c0c8a00d550071000014805d44014192481ca40c181000340590b05041e003003405071254a4005400c140030b0b11144584030305000403010300a2081620314000020070450903880c068211801c800064025600382c0141c940030001a5400d0082c00c141d40601200011554140503011040700c400403c0c84040c0201001400080384170344444821940c0b0071a42480326564600760100060341030b6100043e9807041d0180c20381c3c05500300b82d0901300724041c0e02c0051460031120300840c44100e2103184100100b1001c001485d90744100d0001554010103032080806040d4500f09988100c600403210a00020108201a20041c3d810b01c25501c04c3e40c1c5000032000300d0788400070300507280c0780000d82d0381d440b0710039045403201d0010b60340341581c614010341c1504540b100d1483c0148402c0e00741c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677380629 1250 677379379 677379389
    0x63310120509010e0a080f071a10140112050403020f0105091b03032506020c0d0905090a060302100c0c09020a031509050f0a0506030a061b11060103050604080f1b07 72
    0x4146000201c0c2c8810500c1400380c0820030400504480f082034841c108280e2089000042c4440108949000300d040c1e44210207400e401030309100e0b018600f5101640c0881c0b0584c06c06168004030210549050382c2c4503440c1803103400e60700d00c000346c19101d5280c10b0349006d00c810641c203900d50030a4200301e50110045a84540d04800c045000465a0104201a160f104000c1c55524010202070242c2c84c01d0001e01685400360300c0344000500c2d21404e11a0750385041c03064450007001a81821061000b400c0568005401080c40b690a0100c80d0a40c0c0c00541c1c0b003002d207800007003007001002c0101c09001034154120010701c0030300c204565a02240c2d00080c0600403a072007003c901d101100c000074201c403180c89024070482c150280343d215a11921b00c407101a05018003456410308c0364111101c041155407045102c3c031000c0f80b8a4910940c601040505000d051019005041e08000c2c01003012501c04208940e00c65484219159030707031681c00d03e031901401001c400e000488903a0700b607c1032480002640c1e4080e29 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677381879 1250 677380629 677380631
    0x604060507090f0b1213080f07020a120f02060921060601110a0b070e0a18050414030f16030507050d020706080114130c02010609020703090e070206331012 68
    0x551591001c80c43d8102c0c1d0704c11400c9a001c01c005103100f5030400000c0700e800c000f4010012440c400b240d180c002c070540003404405044600001d0f040308500c0c0a0042000070035154010442d00d44150315000d10070a2019006401030100148040d115034900c7c010720040d031031405d043c18114200e02e8035035a88a004480c0e10780450140d21860f00405000076044400b1980801e2154490391418412070300d1000f00c10125801c101c9080700481c1584880704d4100400c1071100c00042d50346481e0801800c800c01d00c20060050390000c02480d5088000b5004403101918600f0b8a198203040503e0112803610610b40050883d000300d489007407070390343d0100b51042140d90a5459003896600c4040301c41c020014919202e9204009030142a10401c003174000802c900240d000020b21a5500c940c02410780c0d1000004030001100b5100c180040e822071a14944c10112070300c010800d900d40145d1044a0102450030b0001507162412180d9240c0c1c40400c000d141c3c2c03140500302480d0f01c07410304009003e0040313401c0b0701c403030b02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677383129 1250 677381879 677381897
    0x50a060504081e090418200609060409020306010207090c0903021c0803010e0103050c0306160807110d020709150e01120f060f020a0f0c020a17010608030403050a120302090619030902030604060507 86
    0x10145100060441c0c1e007101e19182158000b02c40347c401c444051210b560454000e103c00ca0700c0d40c4d607c4010704014592040c0140c1e980c60108c0c002800c06010707800c5194130074503084103038408903484034080007681e9042e5901d4214101c0020044030340c5c0a0441c004090340000400480d030b170070404e0980c43c102c1748a001100d0f100d01c007110415890b00d000302e40ba40f259100820a040b0054822045103410640c1030a10303116000c1403840346800c0040903160100942d00c0042c04014034107071131003824000c0c19440421101e450600306161340842040c1f103010204030f0084026400d02101111482c01c0c650b2124080162200520340c0034040d4001c03c142030007280f001c10414100e41e000b144602d4550741c0c010328640750b803400c0136900d0b000f5a80f403030611180c43d9603603840420058000c20080c0003550250004140011040c98002040100b42c192001014010b00441245071148003e403a0302d1040700f5100c0382e4541c2d20410440c0107081018019605206103014001030003e40c0d0b1106000b00c0c00d59580c1040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677384379 1250 677383129 677383151
    0xc070902090303250c060e101d04020912010c030c080105030102031303140c07140415060903021c050303460e01060f0f0e0601030504050a060504081e0904 68
    0x8074081c07504075a401d6041000764005441da041c081c0d05141c503210300240c0082c0740b41d841d000142c000c41e40028000c2036025002490380c1c1b600302040440d030003641c030b03051282d12204041500e03910b17241d86042d03004540100d518055a6110580900b286202200030050020540303001009010b280e04004085034400c000800c8904040c0202d9200314048454a00c008801e646c2c11140081c0003070b408805e40005005032402500140544c50080034904100d48000f00e9035000c0200304c404003044070741c3d60b00f12068100b00c019041402582141e4040780c10703101c0241120b00e0740110600741030300108280000010443d411402da240c011110700c00740c45c0304170368101050486047e20310351907100ca010b00c201c20712491442400d03002039000045070300020445660380d1640c90401c00c2c03190807041d4038608548040c420449410f6040354402003d2030b0500403030406464298a9039220400a82000c0e02e550008060040c41c8080b603820b412008109901d07590101698882500715461252089003001c1c4a081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677385629 1250 677384379 677384381
    0x616050c0309130f020d05093708040f060807030608030915030c07020a180e06040b191e060603060803090a05130e100e010507211e060b0c0709 63
    0x9200d020080c000d518040442c81049000107020010a120715169003046004030310b01d00140945038080c0c80040b515082c000c0320a400d08002c1004c40810400e440d10003400549101401c860510941801d451010034608001c8140d02c100c0e00004201e900c1500d0004409138450380e00c604c0b074551a42d04014403607c07000d4450700c1e0711461080590045200c4c51805034417080c84010b6811020745440645400350580c042510744103d9442041a44800003107010a10294007840070050f9020340604180d2a03d5030b54009003000290424000c01560074920700700e00020350080743c62a80d15800d604000060301007d0380a45018010700001034180740e0006200c20000044d2209040020000751541d400d00050000701c0c482201401c4015440d100003541210091050350210103030030f240441d016010002050070740740047c0148d01004544242c110811082c2e83c2d0b03030000c1c64405040440c84080c51b50b8465845003d11142c840105d140490014003058000010304c00307034629a050354a8541d03642d04201c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677386879 1250 677385629 677385637
    0x4200d030914150f1c050a02030103150e07030b2d01090e070e061c17071a0702121b060c0711011107090216150b1f05041511060405061605 61
    0x1841640f000d00203900c20800040240a0900740c5805690a00000703000070810384400392200031603190b0020050040c002c1289140031000d1118000b44254070714040c182c0d41d50541381c40003a1040000c80b000c14441c044440c9506518040444500091040c01e10b440000003c04c2c0f003141300f0310745040d42d11f00c964180414a0011603010400807506540d0710028000003501280c03e130b080c00082c6200d00000a904001500302118002e0400d58545501d0319003d1814240c075044d0744082c01811081010441d40007900708c0d814843d80c92000e40362010100007070080f000d0360007450094000d0400300a02c001d85030019141550040801444060300000191145840780b0011200d58000306020712030f18070190000c0036540d4600070301c0f4842078440d85030000480f0030351041007c15915541c034400c2920300710190883d50180140e054a40b09040100a0001c4c0300da0301c5030350b5411720481c1d0708075200782c043c581c484041d01e007110988001d8646031a100e07403104804c50b136415081042c0c100c0260128481d0040c0c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677388129 1250 677386879 677386909
    0x1c08090c0f0d020a080f0a1703010b1e09030703110a06031107030f171608010801060b220510170907030c03060209031c02030c061e04200d030914 64
    0x2050710808a00900c03000a088038000d0380c1041c40c10000141d00041084000305952801001c0d169003140c030f14011020f18001e913004011118184014044a01400200c6443c0980c43c8001040105880300001441c082c0e055002da25002c0c401001042c440c003040d51482003841291404400ea172035a2003902182c0c0390003511410420b05010040000e07020f280380c20341010702801c2a50080b6901c080c2d04042e5007040302e10b0801c0441000301c40a00b507400c031139600e001d081048002d018450405550b29550f000e1103100d14450b10f0048003181c0c51b00c84000340744003c1d00f80074200000780701305201d0203007800e40039103014446403113420000f40e10307040c0100c0c100c410b49522111001c012455900c038180690840c0b0030140d8103015000c9018803500040d42d20203040d0485030095500c030703014101e0450404800521f060403010742a045030a4a03c10190305a134015801003030f00700d80308140d0001c9420051140c1c01d1940004c28120304009140d0003d246030226800424070594034803169080c490700d6485e000c55 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677389379 1250 677388129 677388139
    0xc0406080c1309090f051006050114070201090b0a0e1c03200c090f090106051c061503140a06060b0c0c010f0c1a071103071109070905031c08090c 64
    0x400c9000d40c0060040c041048051000742149031102100f000b03c40c45090101c841030a101c50a40130890103001d1300710070f07a0410108001c007c0c40c0500103082c00c40c103050340b0280d64800003031700b0703046a0080c01c080016144c0c000b4150703100c07040c480e0007500301c42100c110b1030f21170103980003000103420f01c0c800c562507400d078035a5841001c03101030ad04020820500c54407080749800b403800d8100b000d80798480c050707100f01031a114458050400310202821900550000c5000e91001c0900c2e991104101003202803080d4849800280c070450500c8105c0c81c0481c0ea00004c24051194a81d0040140000b581106282c09401c082108580e12004650309100741d0010110a400407600c0c04003640c0130703101200101c0300a0030842c0c00c200f85559000e40c0030502400602289240506100c11907a0003003050b50324040e0b0000451800c041c0d83c0760b06180a198910007031080d1751040005281500c42c000320801000090101c82000c20b40081e0840200c804141c10740c0080c1030400000d07407000002421400d00900948 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677390629 1250 677389379 677389381
    0x11070305070b2710050a060e010b03090309030607031b080f063003030103060b0114030f070c1208070807090b09040905011d1c18050d050a02060414090c040608 70
    0x692003000c030b0300081c03500550b44003030380700c2d442c18141e075007100031003000b41102414154410080000440b1009420b92407160700c0d1071020300640e410b5515040c195406201c040d5166070311800c41074594860079a0b115054001c11081c801c010790940c2200110f400421402c00304205491011106441c0841e4500c29548400011414030300340101c04100d8400d20f0003009480e2421003505a003913009a0300121101d5000100401c103002c5684079030b001c4118246061007140c030744d903540c00d400380c040a802200d0b804844d401248100e801294500e143d6030388896401d05155143c1c0740501300201c02c031030b210049001800051120351041c4461010303144445001c0d400c0003207500c01c0c0802414801e500325443c2d0740ea2030707401e1126600441d03039062110b520001844009101c0c0040407078210b4140d18182400300401a4020040f0700301c4082c01901c1040d90460901601410941cbc41c0589500c0e003c0e400000c0010081541d900c400c84040d0441410b07980d4001c10b8644e8101c2c2c1d49948200d00c074140005200170 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677391879 1250 677390629 677390633
    0x901051c090803070905190806060918120a0e1f0309050c090411100c050a1122050108010c090b0a03020708270f01020a050703020f13060b0304061107030507 69
    0x1180c14411040481000078500d0260b0740ca80071254030694081e00459600042000b8510300485003410009030782a042400900d098006a504c1c1c00281c4980d00c24100c20001031084050750a9104400c2d0500c81140c02c5190041d0044034660300070080c180000b40d8203c07680781c2d542804a408001d0300000030304013003580200c0e20110020503030400100c03a039020715003458400e0707a00c2c120301c01d0040340140b01c600e0030460454200412203482c40005824040d51490362408900e010401c010400d070420400d1401c0000301c030004029000006698603e00b4040d600060707054240e170b000714140c803070940082068030050b9006803195960341c81f8582000d4002c0203210b92452103500907100075441000f080d404c0c880440d03660300c0340c000c4104000b41d030080344001010403890600010125400e00b030001e45072628554403000c0c1c0355170640c007019014145008407074100d5150315400e1801a06001400c0111588500301c4c00c50942c801c4d682520100d050a1a00240d854400d0459901c90351548855182079495 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677393129 1250 677391879 677391907
    0xa0c020705030601030c0509160503040f0201031d060405281e05030a0e010914061b4315030c02010f050901020a140f04030609140f070812090105 64
    0x401441045028032900001e0310b0320304200450103140318001d1030201030b050038217204442c1001040004100202d00000480e5a04941225040364101c103a41c05015810300040e00038041d50244c0e80310b400c0152102407004900404d807580264443c80035260f420801078184829044030600307020303007800d0402000380052903007407040b0442d204101c08401482459100e041c21030b000307050030b070020444a00d1308a51542e031008849024bca20126a42080f0501c0404510940281460310000c40070b4952009100c0c2c1d020815024107a5a461b80844c3c01340300103512030b070f03510b01c02c02d83d01c007250f111007941c40135042034450b802c000d981c100303d0141200c0e60401c00450240c82081a01d000390f55139240e0310800000301d07002e09482880000c00142e5911902c250040000340000085404000207004940c81100c40703c0494040301e42200d000714250500c0d00b0b040301c40c07007a10241c1108034440c01d813a406841a010030b5200c101c5080409a880007881840d000300c6c98071403046054001641040905203540803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677394379 1250 677393129 677393141
    0x2d24091d0a090b04050f0609030703050901080703060512070603060503030c06160e0d0b190c05040504091704030b0f10060905090a020d110c07050103090f0803091009080d0b04050f0a 80
    0x509030703002c01c42d1445902c400340d8940303040c0e4044d6021b030003507a40740900c010308016480c3c10540c100019403034103071907460080c454001d6400c00380c1040720396008904454803903002440a8107000300420085a840541d103662800d0034401c40c80424102040016140f038084142d0f25803940040183c80315640d8500e0b561011040102c2c0d440600c03004229040403a01d51402e1021101c1c17085040e0100b9040101142d240b004400480c07003201d03414041c000c4050f42d844815982180c900755001304041e0040e02d041d00b5404200c401c09550901d002c40c000040c41001101d240c050040160002e1240d203a06440706441026402440f000c5546050104240d04001d2440c90340402c410400604100c00d000204042e14180000d41a0700c00c00420b10308030039101803000c00002c0c1024282041104680e690b04c0c443c20f0722880000d4060040400003035140d240511242007050005917082240711000d1034282c0554205200b048055840c1441c10700c07181c10244607040c010303504448410301e13681c2e41da5840406042c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677395629 1250 677394379 677394391
    0x5060d110607051203071409030a03182c0106090e070e0f0405070306060f020f060c1602120d0e06160b0702030903010c0509282d24091d 60
    0xb04218000b082040c012844000d85280e08036030340f82804240141200e0b0f030101c804800600c200030342d0016a4001848071841e80e03050820700c20140880d045042c0c51116039002100300040d40313038540e032100042040700400c0d03801e144000842d030b6255201145d83c0e804501800485003002030200c0c0c45140545c0390f803d80c904000b4550008103044030085400e030392050343d0190110b516201c0c140950b80d04a0203014046419100400c2076a00d92844540d40b000c1c007900e03040c1d001c0300002e80f491401000303e0400203015005050356803400300c180c1c1d00f90341c2c030703003010f44850700141c00000b100e121894601e04071248030402843c0c4801402c00350301d0740720a441000d044517065200412690b41191020b024640030740c64583c4909880349082000c0c8801e400c610381d0310614940d0903100d111440303d081c00180c0e0aa4a94604a424000002c05011030340b800000e452030f42c226032041d0000e400306400000c60030f8080ca08034280c00780b0b244504255140602800b44540004241010b0540041d2000d0001c0c0c0c005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677396879 1250 677395629 677395639
    0x1b030504261002220803030603010609020a0c02210307081309020403020f010503060a08190b060402130e0705360a05360403050a1805010507080c0313090b04060905060d11 75
    0x20113070300c2082c0c4554501da0702200300c2c0d402c04410081203203000e202e414020902d40034198a0050000300050126000c404001d1068010050000c0482442400c2000c81c24071a42220780ea2400383c2005a500e0304061b800540c203d81808011441d0401c1d4001e45003100d5020f0005281e001188006542a4200030708154204c910700340e0000380c41d10200010854208003100580b65014a400c18821f561801003c80d400390340100498481071145450060440c0c44c41e000d00709840d1107502c4104c90307a205807410020b82c926000a040c0c000140da10351700d0300e10764642c0c000078117240d4540d043c000103118074401c4681c03145822880b49041020312800c030321000701210102c24410b82010030682c540c9006c0e01c054002540201c0c2c20b25160385c20a120103404030701c9000300e442c400d01c0c000c0000c103248188400100b1112022840c4c01180f0020810761380d64030303400e020340b60341079444030b030360340000c016001001d0b100d03034201400050000340303520486008003400b03014404022403036182c5000801c40e1084142e080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677398129 1250 677396879 677396917
    0x90d0914060903010f020c120c060408090d0602030a0c0e09040b0a050c07080f0d060f0b090618030a14100b01021e2104030b07030b100f1b030504261002 67
    0x6030f40070705c60310304d010442c0800141c0b240190a40946840c080c16654652030b0402c00401132415000600c40d0f90141c1d20402260303030b50301040d001c99541c540c42c04008003c1030011050100501840d0000c0610125690f6010703400f140300002c0082d0f00c0070aa41c041c0c801d04c05c0d030001c02c00c0c800154003c1d5030300004112040b4602031495482507100ea210007400d484c2d905000c202c40d50b07050342c0f60003180020001c8903c2455030318200070b114045846141c0c6420300c0760303000251547e145081da40542c2e603030402c010203950701c9242e5804c2c41100d0025120341007005000f9114808413046007071054280070101070b030040800d06100f5600b03050494000782e210b0b0035842158881d0341d0300c0503601604058803040031a40c907203a501c0d40c94250741020014182c1c9051509000c010262074580441d812000c0e541d85c500a0000b5a00070015602e2001c0f2003060100300620050203000e01d80c0160003482107440307042d4100b0340340c030036400242027055090b03e03003403907540018001185040c0640c02130310050300345400c002d940c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677399379 1250 677398129 677398147
    0x209010f0c0804170102030609010909080301090213030c09090b160e0d020a15020a0c24121d01140a062603190c0629060a030b03160806090d091406 65
    0x6801e102c0490038645d0390000104000343c10007150355801001424414000c3c244960380708205400b050080381c40c0140c0c08138032240380141031800c40d0000d68004802d86031568842d407811016082d800c0301a1500c000f5040454400e0101d020020038403030f00da54609100c6500d04080002e2501e10740c43c142c0e4088174582011411405400d400c2d02500699001020380021924205105d00d11a82c0410101880041f1001c1c116045469004401142d40b5000e15034a404040b0b100c0142105540c42d820641c08895a0702a014150320110300c406801c40c0c0085030765500c8101000765409809081588442c116400c40c48641100005068030b000c44103170790826200304c0d0661910055600700e08001240c0900c548288401440340101e8180c040b5814041d00e02d0b00b0a040c445003403c0310109001d4040001c841a1031031080e4881000601c0042c1900c001503070b42c130603220004c001406048258012540460010000003686801000154980d01c0c074080ca403080c0c100f44226100705143d08580100303d541c81c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677400629 1250 677399379 677399399
    0x206090f01030f0c0f0816020303010b160c0f050a05240c030c010519050f060a0519030c0b07051c0c15060b13170309010e151b0303060906040209010f0c0804 69
    0x301d0a049982c0c8102e0030300c00c06002806c40303c024080b94070940000c0a5113010307581c00b0041380d05540d1008507440d1707070f1515400301ea50040c030541c00142280054803404141d10300d44034440c5048890846981800e16121010024001146500213610036040d41c01c018020602001920b00040742d0000c0d24141100040100c1c20345070111400766058003100c9007020002d00e140b01d04da4203c0302d0360280d07649624064004c00e24030f0348203004561086110414100b45801e0308890340c030180d580819604403072075881480342c0c1d0719003007000211641e0280440c00402c810103441c030100420540d585030042c42020392070f10b41200d0384015012100640724440864150f440c42d0040400401c80c020010815242c65200c0c0880601c1c0740c88070017240c0080015903010707030b030122007004001811103600917610f0b55084a000a4440d1510380c4880780c0b00030942081c105404000340d440380009844c04e04095441c20104005c81c81451040c501040c050600c1c4c8072070600c1501800d094034410300e80180340c103480343c2c5054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677401879 1250 677400629 677400641
    0x21305040b0423012402250f0b0310050d02011d06070c0803031504052a160312050601080c0d0e0a14010605040b060316050d0b100c030806010c0206090f01030f 70
    0x998965091001000b8403c1e2440c41004040700c941720718040303401d500c0f030025101c074a001240d001d2090500c0c1c1d00d00d003111024805030010031944807070342000d40c0d40c2c24040307032160001c60320381c0d180c50504400000d0030301f0020011640e440e8160365204078840010701d0051284001440a0b40101f400d0001000040000d9910300c00b03404e07248015620b07498200f02c081460f9414401d030501032418001030001000c200240001d0480034150fa29600080883d43c400c803a0084002c0702540d40040011a400c0c0768002c503512050381c2080b030003480180c0d50b61700195040b500c1a20071406031030b420047c041844903294000304007110720000303681c8264801d4860380c83e29000001b4260f00d695480004101516140c400d2404462003601e03110b0644c0352110f40e05444a001d44008802d0002c00a000720386410070b0352000f8403000b0010012140d81c080200e000340760a0211304120045255007000c01d08541c010b03198001070310b80c010b01c10f0b4900418030040c0100f0f00d212001550501d900c03082c18070f080c807101d40039003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677403129 1250 677401879 677401931
    0x2130605071103010603050c2b0f020a0605041202060c102c0105010b071e080d0507030c02030306220204030606081005010e090319090b1219021305040b04 68
    0xe252144000c1c00e041095801070704016109030f2501c04204009180802c012041c0041200d519203490801820003040c03802c520325040d10302108a2440003000344c1c0803007890429000f6564412410384420081c4c400b8407441c01a82220b02c0e040703001000503d4042c00500c946901740060b214002c6000c2d02400c1a0740120440184a6905d035004d072460115003840c0d40081e4030840000e100651401240d1100b620a00c64007500808488400080d0344090044800c007041e403260ba525a100c281c0080c24000308010f443c8040028204882a454940700000341c0b0f0180c840140204001109250f071701c01403002041aa01c0d000da028000000410420b10402c0c0090a0143c0540180c100e1142e00300e04641e0141c0181f030f11201010140700c0b24038000010343d10350304000001c9030002c462078201601d10300030395801191003031000241c0c9440c030b08180c0c00389401444507060804407407030f1100c2000d0590059010315582d06081d078004000520b802d40101d42c0300d01c000303000058000c215000d603025000d0b0011f04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677404379 1250 677403129 677403137
    0x130e070503010e070605030f0640050601080708100f0f08060709060503130609060504030509011404080d082518091503121808010c0212130e0a021306 66
    0x200240d050a010f2180303646955405004000d042c0b01c0090600e0001070322845509030114001101901c84013544030b03c621151031014502080d000d4001c40c01880d145070324600c41d50307000c408045160140540381c01010161518642a43c0384401190f00c100001c3c201450b01050ac3c40000b039002d0000c86100c0036000e040218481c0500703118041d450b2070340260003502000395480003000215030002c140e0b0b4100b550364078000400c01044c00c01902502e02c030100604880d10304414041015003010003082c51010a0300c0e00c0d107012a8032480c0346a24002c0d4130848144d904954600b041282c440c0032942d512498201c1190b05205428030742e1008400300c00d25210205464049115905002109030030050080c4407042c080e00903414118030752000e852000801d1860003102c0703006047d024040441c00300030030304031405c3d04559070035540c1e0190050384010000b5008002c0f4110203a642c200072030740b08607104210400c80e146400504910034400601c0100320550030b010f4001510306510141c001803101c1d13a1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677405629 1250 677404379 677404393
    0x90a17070501020114060d0f050f1002030a050f0103170c010e03030c0a090b0c101802040f05100e130f03050d0f050f0a0e1b0118090225030e0609130e 66
    0x70000e801c54a00c0e414400140c59040d0804c0703071341e646443c4280c690b03580c0b02e10984026910340c43c04515101c0f1400d2400c1650280307204451141b034580c0d010391b03c1010001410300079500d81410107042c00e0300c03e00029060f94007410010119007890b10081001020020000419115410115045400a880d030420018001404641b101d502103082d00c003602c0380400c4145030201440b4085e40d5460a806002038054980c980c108050175010880101c05401500610180802064000040c182180c4104c4031403215000800c968550380240742c840c0500c402544410b0010f6211003d00c4440081c00300c080000811a601c0f42c0c2500d8012500104c0a401d000310795424124011200c01000a140c02c159902c0c0428030b01d40841c1c0061420807041c09040c2c4001c07501d00310001215007501d902001c041c026100030001071001540d40c020010107003000d48130b03640100c5c0c070305411020019000d0051300096001928500b685000c0e0b00402c07507900300078061780c2d082030f0001d090416175040400d91480341c0c000d4a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677406879 1250 677405629 677405639
    0x6030b0403180f0e0c1204050f06090a17031003081303062a0e1201020c0a1a1006030c052a0c03160b0904090609050d0909050601080c090a1707 63
    0x46003a0314100c08036150b4050034102100c2030701c0b4000c148035420340444140302003081441c03950304640c1175034903c8085400518150801543d20b00c001c59140d1000d1003a48001109890049501101070303511006000ba103004c0300e1082d80e00ca400140990744050030503200040054175075401400902c58941c4004081460340c03d0075030445400d209041450a480c0d40129032003800300c002400540f01500b8800e02d02c2e8510004640031404491481e8625880091401d8003024000b441c070144038441c00c02e40d051602d004544490301d08040d1682000a4440c4000384008c0d4043d42084004100501d03000d8181802c22808100301d5540c40c05410b0100e0400a50301c00341c14043c041c003007084c4001d4004245216610341c105c03904564600c01c0c60001c2c02d000c00c102c0f4203541c90b500400340042c0c0024041c4455500c0c0c1c2441519003074030340c030400c3c0445d07410310002a04540900485101c0c5205844a000e0755a0b510704e01800359121000e8940c0c01220740a0102c0c90700484a035403401c03200c81900421105040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677408129 1250 677406879 677406887
    0xb04050111071a0405071701020421020312030915160f0c0c090902030a0b0c030610030c0906050708120a0209040e030c0714030f070b0307030f0c1403060604050406030b0403 76
    0x101c040d403448403104110305404038481c0325846800d81c1d8201425903883c1d40341c0c10600d09000442c0c20440080000c07a200103100c0d10150040d00035110f228400e2942040350700b510500d210180840250580c02a400800700c08504001031580181c910050322481405190003030010b030001c47c0c1d003c15801d841103d225919034010801402100306050290f140441c0d0345030408a0070440c0b2804501a07102c2800a08545003440408010341e44804401400d0902049100702c907001101c44034050a00030446000d0f1034801c2c01a8041060b494840e00225400c020003125180e10080040c2c0b4690020011a01000300c103401035031054060840040e140d0001c0400c100651300050700c101000e61007030043d10003800c00810314004848281d40c5003203003566a0b0001c40d0030515507401896050190300400514040c2070300085211390141da9040110303009040c1c0407002c07204515614000200a01142800e2001c1e079001140c00080c0184180d00b025138600008059902c580c100300e80f00080e0b1020b00c0101900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677409379 1250 677408129 677408141
    0x302060a09171506032b0507021c0201030e06070504090c0507020d0308060a171009030314010807060f05180d21090302040608010c080a0c090f12032c010c1407030b040501 75
    0x405c80203405441000564614020128090034461196245000032124007a02c2242d04043e40a80007001c40700180b260b640c0d1100500038107901190400d601d00b0120600881d000384500450344500b4146414039048000515016800c4000e00100700000c00242c0d6400030800e625610170b82c0c0d84112441c0000034860301141130b6100380c0c1c00040003000d4070450000411006c1c45003104580000d2074850a040840203032030390383c00c000d003080c1800001007065000030131031700c060f541c041e00e5021001448180807a0070303114100b0804c1c022100d60f490f8611030300e0441d0724064518014a9110501d1070a410800c44070b891141c400c102069443c1070810450a050250310010071070b400017040800f07a01100984003000003080e45514070303900e5001001300c074000d02941004e4004503c03105502d6480701d04004285110000a4000c211031584000002802d215540c203040c000060500111880d50300541e501d00000d182285c0150a402e000705001c0f404101150056004103021801030410b42441c3c0e0171100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677410629 1250 677409379 677409391
    0xb030303060d0209060a090501030f060c08060901050d0f02210f0703030c08031e01180f051623160c0b070b22050105150a0608100302060a091715 64
    0x424001c200d0641e446a1040e00c071181c040c0c0349a0700307556030900000c400e86815000250600c6c81d10340044180301d06c01c010a00040c0c82a07004201130310a5010942e031072030003142c2c00d5510000410040c0306508110002d494918400c1c14000283d140f154009080304091480020a94180a040200c0d01104001f005007070300750311010300416400c60301c00410018445c00060441040003002c900780c00c1040313440300c0420034a02c5e881080c42d40c4a11a00002c8441c2c00a207081e142d08101102c01000110b10450780100e2071602d0044502401c0581620582c071605e1150902d2281490001c15216829008003085060f4041c80c0c0340ea0043e519141100b1400c98201081c0d1381000d000380000a0b8150044641145030358039004039501c40e2200041c1001d905100c0101a94204018402e00c154110100e096032001103c0e0103070030741c0d283c0070221220902202c41d1244160140e400304050306024004100405240c602001c84e907440d562000c0c03101d040d00c1c24960b540c0e4445030784210001840202250421 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677411879 1250 677410629 677410633
    0x50918070906180902130f03260c0c0f0d060f0522110112061e05120f06060405040f1e060f05070c030338040e0703050a0b0a11030414010b03 62
    0xe440140780c860040f182c0d0084401050740040c0603c1c030303000403c01410082c141c040c3c0340c0403525243c0c0f0f005005c44e024a0140103440d0035503138154008000c41c00907110b01000400083ca8030190b0302003007100000014140701c0c1c1000c0303914600d402240a81c013400c20b000140102c007042c1303802c04000094225407940c12603150140010360120014055000c030ac00d04c46004d02e480502e0444202991000344243d6105000349000784071041c003040200c10b20031080f180c1c101c61021200c0800c8a000d83c44050b00a82080290090000541149031070b5008a81050242084104031150355860042c40074a040c1c17841e100c0c24101c003146007000498024445080900b0500340142e080092002e03150084203203005007031548030089140384030034900d80301c5207550340340d07034040d40101c5040c00041c062a41034806030301850030f041140d5a122000150002100c1c0e0104c010300300e100c0c2c16141c41c0d0aa45000e03000440740b80c1c4620991000b800c40d1409903000300e0042c269501d90007070140e055400c4440341c525003400380e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677413129 1250 677411879 677411897
    0x1c02040f0905060a060c110a080c0102010b04020405060708071a070801030b090c010f05090d0c06031d060603031c021606021206030f1e010e0607020325110d03050918070906 76
    0x30744031360359250304840d841d0030700c03c80a0f1000c1c81d004000101d01d190203500324091000c000340d503c50004070520b10450030b0b002001111040e41c2400181e12680c0112500f1820170803c0360005103c0c900103040c0d05009452010010080c10f0212503142d03019101103001a56500c0148280640030100302d42000d414001000f0801580c00060040300c041c0f90344078280308002c00c4001c429110010105840e6500c01e61000c81d0380c1c0c0350300f00a0024050100240640c0307551820300c0c041443c0008030345000d014001c0c010f5040c09609503400881c5440c8403c1710110980a00410000300600d000c283c1c0300074031403070025807103000020580c41c50340700080030b543c882d5203e4020400254400310700c00b1800810150382114079a00080087e01422100018015030311552080044d816400f2001d05102440d26096130840300c00140c0e80700c151092400058400c002d05030200c2110700d030400001f44040e200742041821b0018004c0012140d581d041d0021740400c590b4001c10035115031001c111406000b02e03040801c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677414379 1250 677413129 677413141
    0x809240103080901021507031d0a0c090c050c06011202010e031507110703170a140307020c0105090d0803100f060207030b150d23010605010f1b081c02040f0905 70
    0x4580041c031016114800000d1403060591080c08900e800d98000d103050701c810309200034000c004041d8400c0840a1045100b8080084640854200d507040d03000502c201e01181000340c1c50005005446100052040400c040d4800c41424400076000746082c0e091804110211300024040d43d0140360000d100b500904541d11521203902030564006030309160070154982000c12241c07504075250800f80c800030303041000341902d150500081100b01030b20741d1080c64068003d030107161140000c0d10000050303040315444141c694400c60140c101220300a210306030012030358491118507401540c03c0d400c4035100351001c0c03000c941c3d002c410000038030551006012051654581500b482406090b400340400078440110a940e24004001c0c2c00c5070300026400c248001c1012480c039400d03d12821682554200388000410358021040d60302561440d4954165607200104403260360300038041e00701c0d2500d00c241300b0340c0b03600c88070710840b11115020130034010390b59818080b01e01e044440302d90180300c04900705410004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677415629 1250 677414379 677414443
    0xb0310060b120c0d1103011502010e0a0b131a07030b010e0604090902060f160506090712080c100501080304030b2d150405070e0f0d030918020412030809 67
    0x845000d0007070b02000d6544901c00004080d03c9022943d041d01420000200d5020b00004003c50481c1e5120780c0702030040e040200160f0907107a01a8903c0041e4010701903640105000314007590340b01800303a00040018940307a031148454241030f02c0b1807030b54000398401c20064542600c40e0b0707401c40300d090818152040c49000040e400d8030450140c1c540040c0c07608052030864890f00156100c00e1030280700340d512880350701e006211407040340a095610788510b20100d04941ca000c039580d815180000490b519410540d00c81c040c02c0c0e80003031080e9a441c07144941200c8002a58860b00b80600558006140e071980386060050146802805d0b8041011151000d6011a507801c0c1042c010555201400900c607943c00a043d146007041010b259001030030310040102d410b61140e03251404100440704100400c80d10802d1102600c400c150043c040341c4145002d1042d4644401080707010303814240b016181c43d4540700c0b4030104c2c6080c01400c034080385004040c4203d10ba0306000c400010340009401e03404c1032100c401c4400d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677416879 1250 677415629 677415637
    0x1050f0a090303020c2401210303090f0605070908011a03060406150e01140a08010b15090d17031608070507080901030b061204030e0d03021005060f0a08010b0310060b 73
    0x84119035440a5040402d4000d03019668400c00c042c003a03403c40b82c4509a0003415408038417100955908107000415074204c03d910703c2c08012070303500c0c4912100342c2542d425402407069040998999845904040c002612800b40b0303803003070380c1d41c8d80d41c0484585040e8105003075609501c56040114042044031080d614000b44080c0c0c0a03402c00b0010900c855804030590b9000f085402040c3c440540c0c0c80003150152020200094a01c82607958115240c2d48844070381c03c80f0314420b140d541c0942d24000c50020700590030003414590b5401807030b1030004911980c4445e004428211059400c10003c01080142440031080400c00d580a0230546164500003600034441c4c443c5184c0109403c00c00316034400d01d40d210354004c2540301005021a82e44140c030740c9802c0031480f01204c0c114002003000507a41b0060402005410b80a40d16400520710080216120781c05410000d1101d50800044145030615580300c828041c02080203800003d650444881407509200300c54115021b41e82c14044c0403c50445000120303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677418129 1250 677416879 677416891
    0x61b1b0b13080c030a0f08060105070f0c051026011a070303020d1113091a1c0611190206060d0b0601021006180506091003081803062701050f 62
    0x40c645940c0e404440d001e910000410140c2410307004254509880d9000009011030446900da80b8044640d00104549101d8100ca50034000341047c0040310001d01e18499007858588070714440d40c4e03c80e4451000c07448495998503403100288000c42c0505000302c1c00c0c160b01203c045800c000f40d07101d604081900240c982074002d4100f420000007000400d042c80b83e41508c02c1c44580040903c10750413645100040c54002e401400b0341140d40d080d000607002882c0c4101051007080364180540100346904120600310701903904100348030010f6203400080e0240c403803601c0790201c40f4082c588a80d070205000364a140d0740d0300a101554805010b002803643c0b07002025009540c88108512540c0c1c0d4000100d04042510300b42007503150811402103007052840c10315a140b1104030703408220070b60360141017241541094801c020b40c641d40300001d0001ca2803140090602e00360440341484680b12110109240440450340400445c4400100e400d0074101d02c505800d9026003880240400c1c209030003581960b00d0f018040d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677419379 1250 677418129 677418143
    0x1413020d030e1f030f050609060402070302010905070f3228030506070f03180b101205010207060b0d03020c040b210601060e01020d02030a0f0e0904061b1b 68
    0x10280c1018401d0b0910a06001e020b089000c0e0b9140c00c240f100b0207426443e1445000c80d043c4035441c00b01c14114811644a450020441d01598458805200c0298841c0c8025021035403940f03015004943c0c1041680002d2000030030305d10140d40381c2040c40c40e81c41c40070010329117500952840807000b0400707202240c0300c0c0c550848104c180f401c0701c100080d0340300b40f0f92075204034099101c10b000001c0c0300c0f002c030f1654031921031a11180424a034000f000c904607581d0711804e29945424091160104488590071a4040e01d500b81c05907507561103c080940301c4903510001c5a0307681d000100182002541e00130303070003e1507003038407214100d81e40d80d0b030003039100d45000c14601d0090b50394501e030200e9a5280321141170740e070714080b100c04210000c0704400c9840d1070003401086e010510700280c081d80c5500c0010444e0180d100cad0b501860518092030f40890f40c1001c0d04071480100003404500c0490750395418201c1d40900e00c240c00000d02801580e42c2d90060a04120981c0d003800540f1002d914640151071400c80c599a100c10317 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677420629 1250 677419379 677419399
    0x50402091f030e1006050303040315020f2b0b1806130c03020c0601050a0509040b1f080c0f0105031012150c0c0510060605091002121309141302 63
    0x20407510101ca100740d220745501c1d03240030041140c040d0700c45000e101c01641641e400c03041c0200b1800c180c41a5100d080e0301540100010404070f1140701454416400ca072501501d41070290074004501d40040038158051980480012412450a140c1040070700240b90180004c100354800175020000c0303900300251419a80000030703100d94550500d4108800038010411103c556401d0040080d08078800020320f81c403030440007084c14030340b1030b190804540c40108841c50607a00d59481103c600360142650001500ca500c2c020f001c0030181503020041c2081340000c046400c00241000700460fa40d1903210706002080041c803852004114807941a1115400d6001070402d440c0350202d02e00c05440c9400514524200e0101c8405038880e1810000f076000e00204c811036a04801e021040755814810f0202003202080680600e00b4000c1c2d407140004c1c20b600603180c0e54001e60004558550260004108141001c40244050304c4a441112500185d455207041d50386001c4507000c000c3c0703002c2040039114200d050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677421879 1250 677420629 677420647
    0x12020106050301050a0e06060d080a1812080c19170a120207060203191406040c050d05040803070f050909010e10080307080403031706151e030f01060f0507050601050402 74
    0x14026800804018001300818502143c0340002000013a441510f1401504017140a900c0c08030550003003d90441121031504400a0f000d80d07510302000e05100710036621840002d400550101027003040740c0164401c3e591031840c0d00941d401c1c241103c0103000e02e030040340f07804c4c0040303039101c0042c0ca601000740f00d0b0290f89084050080d50700740305403034000384454000284601004a9900618003501c201d248100f0300d42e88600c114019a449002c8045041d50290002116441c194100020880040c1441071605c40b0003420402520700807503054540b10000001c1c854055030000d0360401c42829854128106406500081c04c200d07410b00c54410104860004601038040000544006280400480303179a448035251452064000d0311003a0b020a0144041c0070401d4080d01665205080c01890080d840a1900341c01072039400100080c3c0f48200c0000580008801820003107008165040059071a5032404038001c0c40100b007036020000b042014080800007400001d440b6054400c2150090b032104241 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677423129 1250 677421879 677421881
    0x30d02031905040507170f01020d0c020c010206040b1605390304030807151d070302040c050304120807120612020910030506070c05030f0d020d0b1c081b01050702030a09060912120201 80
    0x4105101030235440050b400c078030014981e00000d000040d907026200744880b00380042e81c440e8800c0300c000c2c04000c05a03000589104120060001e0340d042c9051140c2032092118001e5001c0c03401301c161140518000c05d2070b20701200d400410820f2000810000e51510303046648014490084050080842c400c100800010344255041415242609500030300c04402e480300389a0b49852603c0143e000701d24018070054024030070350440344a550440c2007010782501020703003141c0303440d40104140100181000702c8000c4810324001c0d140200010250380702060000c0c010444d002001070039054504040032000c100250010942300d510010b103050030a1500c038130b0b00f0310b242180316988841d04940d900054000c034124041d405070032510710000c0c0800074026280c00f41310000d440454071020541c0101218030004070302100520340c2d400322511426105544400041c01d40ba4180c3e01c01d00580c2020500d00301c0705a2003840b4400034081e40c500040c12034603102e0020b480000310140034000d01140e00c0302c04041030007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677424379 1250 677423129 677423143
    0x72d030c020411030906010609080115060e01030f06081006080c011718010903050a0e030f0c0d14120705060a0513030c0614090c240a031d030d0203190504050717 71
    0x70f101442d0303240f40092105846d80f1090145002103040720700e001c40c09850510640484103900340e040003210b400d00009803408018207680a04050300c0b0203141c90108130134080c1d10002d0072504014400c2d56070314541d26042d11308640196206034014407400e0a02d030303803146980c1c04201c4400ba0620190b22864849007001105255100362503013000302c00010141e02000601e442c00e429502c101259010204043c0c440c051186888140c6d400541c4501361807401c111001c016a108162014203046081e0825090250341c0c0f02542c460040401d042c0e00b8000c003403043c01d40c08082c032a020406458111740d401c81d1002241c0e130280030000c600d880c2804100301ca500c00390352804806440c0c03000c0d01c1e2a6000d190366212400240f801041c4041001945110300c2903902841102201c5544c100056560104d00030481303503140c2008102d0000c0840141c0c8000e2004080d0000d41c00c60250780d078130381412008846941c48600000075450076003000301040010590500b80d400c01c0c0140b100c0d07030005404692074442 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677425629 1250 677424379 677424401
    0x6031125060908071a06130c20010204080601050109081b0d0204020316020d0f02120a090b070f061107210306050301060b032a0a1b0b010605072d030c0204 68
    0x102d402d00d000c0a00030030102400755640314405040013400e051040401c0c403481990b00503001103d1a0302090484c1d01ca4001d44e0701e000c40c9281c040c015641c0d01032103101d042800000c1e4080381c3d50014060265200a00c90980905001c3c00c00203a400d2400c9802942e42d491010803001c81c0b000520b2292850b5140408643c1982e0000c000317640f00c0c2001c0c8803000c41d4180e60001d20001d4416034111300c0c1c0d514054a05641c20101c250007401e81308102207480c0000764419950401081249000442c511a103080034100c290700400039110480c055280c110110b403c41d04200c80104824480280081c90712410212200c080440c0200c42c80e41580090740640840c1d00100d501d9400d003180890303580c4080d800f43d4803401d240e041d04040c0d000408100003010248001c4201e50130307820000240b80c5030140c03841024035403002c800c80c0e41c010707003a407206c4096040c2030701b10300c0004000160303d8003801144200302d40c0202e40c810a95860110311100c07135a20082000000341031280000042d4155916980308100b034070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677426879 1250 677425629 677425631
    0x3070306060308032e17030409050106120501080304051003021b0709090b0a050402181f0b03180f030405011404050306010e1e060603060919090c08070603112506 71
    0x5a00d80c5410005a001210b240c60780010020f100807040424076110b9000604d0b484103038100b60700300700a008803403031161b501d815a440100b00010b1164018030425000b061150f031a800c2c4004441c001009031441a0300c0802c06920920007444240d0342d0800e506110196820016510003158062a6003503040c40401005130055a070005115456500242e841134852881e84102d6034036a6220303002c4840940300030b5004003866001d014100c804689880d0441141e03001c4024806c0090f002200c1c42d21250040341d40c82d100072060110003c06040c003d8030580c4060b0140181066040c80b842d905e00481c8511410010341194089582c0303202c1003140d0142c0005400c0d0750311980c40d007020702c1411809494100300c8031400b0740246585d840e2041a01d0180d04010442840e548480d81003040d4240b0140c00406000e01c04603090200c0304041c8600800244690282c519980c40d01d00041e09140c400d034803d00a1604014020344c0c4000d508044507900c0700300717250300740780c230014100da444101000f014020451 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677428129 1250 677426879 677426891
    0x30c0a0e120d14190806030f011503020f031c0e040902040e070f170c011d031c120b0d150207050a0305070c0b0408060403030b01111f06050916080603070306 69
    0x80240400d450b070035814551900355040d1500503d00c051842054070000742c0140c24001c0e04a030742c0c4a01241908000e0003800c950722100500007940c2140d000c903940f0408007441450400c00c50400c4003449a00000c1107010308454106400c03419400012120418200001044d00c4c04038be90300d540c0068040b40c0c0260080240480c022450383d0358074002c2c02400007070280a400064101035040c0694500103411000c0d240c900650401960400c90a4540303e8040d03003112003005243d1020808007800d8418000455450740306110045c00311001c4641c58140c06044c03070540550f030385510705800e40d452343c05030720045001d20f0801c00708020b014015000f440e034080da0141d2418107600c0005060694040c1a0302d4034902d66038501030140e40324a04c21000a5040b590014010a000340c0c01000c10f500706040c00b2034180f86c050282d9003004104a0342d101c2040d00c0070080200c0c810b0500c1070704080c0200b0342d100d10301400d040070141d204102d040c8100f02000302000001d0300380d40301845214000d41d0b0040061001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677429379 1250 677428129 677428159
    0x3030501051906020a0b0a09060203160f02070602120705030c062e05090103020409060b030d050d0e0a030503042405070f031404020a0b07060209150a090605040b030c0a0e 75
    0x509000c0c8101441549480d20405100d1020500c0380200c1d41c003600206440c00c1650784241180034001c0c509600b003507840740c2c01c07400b00d2041d000071841902200c0c000030301d41c540b601000d070a4405901405d021584400b405012f00c640000e001035402c10794044041c1c5507002442c04900e18441c0d01c641c00218002c95007408001c0c03008d00c0620404460408000c01d400055000c0b0140b405064803466034003010b0a8010009030806a100101c1c42c0d00558010840c1005800841d00c2c200b110240e1000041c0d00040c0070040751441c2c41088010052400074004400307151324020402c6c000074002516000d2810907030184540368540001d603404244206002c149031941028100316103049004010904000b000d0088101988100c0d01c05d60f4000c2a0020f0107081110300038103500710480c00c44007250308215004c82640c0340001ca121100043c1c40c500d94602c440440141f4a041c1ca07449002031001c1071009000101510341034030b901c68003407140c80d41c03200322142003160225624818a82c0240c0782c00d8140301c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677430629 1250 677429379 677429381
    0x605190819210e090f1501080601020a02041505011d1f020709110301030c0b121506090319110a14191205010e0d111203072a1a0c030615160303 63
    0x1503040044030441c2071380d503401200b07581d80d00d0119240c40c0c81c1003110248403003540c001c2200b80e81129061049038007003140d60b804201215114040c200c9140b68680e8200310661703100c001858410903001c02120021440c501081404420903101d0060105c0d642c590030300070f8030030011500100744d000401d1085814034440008654001e000a88204d81460404503491521341c0880707203060944151554070b691104440494640e0120005500c20410424201c41c1d40e41008000241360020345640b81c224443e18041c6c00c1c111b80d000741ca50040c0e03104501000091040e0040401081007591008000712284040682594807a0000500c00b0042d092035001d0107070540c89504841030f00c0040706d000303000078481910040e140c8181541923074448035081c16441c8100d4040c40c1c201d006400c148000d11103800008180320121072400707141201c500d40410a01c000984224000c0c0a00007401c0440d08060240c600340d44801010107002d40840215084c1e8800c03410300710b0b950444150400d406103191450014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677431879 1250 677430629 677430647
    0x6040216020a0e06150304020f0910410913151b0e011805010311190203190302031e060a1502100b1f080903040f0603060519081921 58
    0x5e000380c0049110104030a00241124040c0b030300140030b000528003d408001c0b00c1e200003088103103109580f8000040c5a26000071002582403001c04480740014115204110003d4150000000c0c00c0080822103454881c50002900029501349240c0f155442c0c0c01d1822a0301c044540e5250360904c1c003982000003441040c41c02c0312010484e03648050700ea070700600450780c1d0940b40010310442402044100941d41c000d80c08a0803034002c01e85824248120702d4141d450382e00074131100c0000340c0c00c006004040140100b05400091009080c11419070900c20107088889260380581c82c4211180c0b00841d5483e92103800c807030010100c070301d440c100080170248000e403500307149501d585075641004030081c0c0d107140a0f1078180c54403048580c1c1d11201104c1500c201d54651000d440b01c000350004000201d6071000390700031100549182e0b100400c95500d048107000380211740040003180401d441030288120b80e400b041010a03c00c143d040403001c42100c0c14591411804494149650b10045402440503a0481034013 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677433129 1250 677431879 677431891
    0x212131a0403021c0614040b01211a040302060c0f0301030809012c2d09180a030203280c02060a1704060e0f0f03190c0506070201050a050a0c0806040216020a0e 70
    0xc6c0400300c0400001d01074a4404d640c01480c160b2440c005200d50300701c400300d4079240c685420700d64a0a00042c0c44060884440403058810400700d2800c12090640401046400c552500520f40c40e2403c49011030130b8502040c00000d10701c00b400a5101c06070f0784036550300c06440c152242c6030b0549a602c150019040804080341d640a8050750312910196841c0e004d03010301c1c0504509c0c6c513003440b81242d410000d01d61401420600c040c410300500003440c00c020090369227400d1294004503035840c0600345103407810182c00040640020210f4580c0c116940c05042c0b0103e407a415150192915940481560300c0c0105440359000c2c07044010401045c0312490f045000c43c08450400e540761000c255140750b49503143c01c00d1410070393780100064015000040802c04003d07106140031000d071070030382e540e1900701b1000752040720061303440b00f0a20604100c00c0c03091542010f694031040004510000000d41160401000e2031300c0740b5401b10302d15400051144100381c280c1c1d0300500c42e1103182c1c3c0700c201011130b003003040c2e40d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677434379 1250 677433129 677433131
    0x61d0a240e1f0b0603010e09150405010522030e1002010e030a120e031e2d0a0807081303030f0905150109110310090903020a020406080c010212131a0403021c06 70
    0x42c441d036060584202000c402d00901480d00d160308103031144440070806003513180c0a200303440c8409440003900014a001d0746c49000081064203001c142448070f0050700110310036142c024103c01c40004d81041c2d01c0381c0f00c4141516024503100350403406034010015055221502d020008042c4006544502d082881102903c0304000c0c400c4101c00150b940d0107011603104000c02c00c3c1c0c0c3d054406106100c050319011340141844480d54009000c00001c14083d001c02c0d1070000790108803501c00702e8001440c81d900c204240b030000054649421032402c02d100c50007000d02859030321a020b0f1160f40300e5800400794103811408449000b06803103c1e4901c2020240b1a80036694a0100c030120700347c20181c22a0300407003515010303400560a00c4010320040c0000c0c1d204400350310661801d01d005880302d000700e000601a40000c0d28801107001c0004e03040080110000d020320300204290800314101c444e281064440441d002c640200b008080040544101d410180d030208890043c6901411100e0142e401d803842400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677435629 1250 677434379 677434423
    0x40902040c050d050f01142206060e120f0c12070f0609030506070504080c01030506010509130204090e0a120c0f14030316050c0a02010e2407061d0a240e 67
    0x5098111782c00c20b000d104038401c14407000d6601032a180c840401e468445004144039984051480070403103506610070000f05604003903000040c03610354131401100c1c0d0540007420401c0208044161a06070003a2502d204800c542003a00c503a480801500010700068803002c10140d4562001400c200c2461000301d40034440d05d80001c90b00d5208000361030844030440c0051408002e0320005401a003c0200700318100501404a000307243c2e2003c104004071981da49005a0303070707410701c0c0d4008182c3d411030450349440e62140c40b582c40000c0401c5115450000245447c500041003444d00911610850b1000750080c2143d00c00500b11000c04001140900b0f60607403180e04a00d06000b0542d194010142501c0440d04070200301005940980048455000001d10340c01c54012200341042e0414070120684111003000704000d01001590300c2041107104044001d5251884910035003aa500258000100644011010398046080826144040302c440300740600200c12011805540c60451044070220702020b10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677436879 1250 677435629 677435641
    0x170609060603070338040c031103030a0c0605150d0b0105100e01081f0812131e0909021908010506030709050c1b0309190e0c0a0504030b0402040902040c050d05 70
    0x9643c0080700e03884550703028140c40007140f65a6013091013542c82200c80b08641c0e482011218104060302c594401d8280c06d03c490b042d4249890300716011189a03000b60700070000b0424064000c0b40c1100c4482d4041004900755484542c00091801c0d81c0346640e8119001c14410001c02c80c10000c518103940c01a180f001c2c00a040c003000702c80d0000240e001c1c0d80411060030101d20000180c011403040c3c0384000034100b020700d940340181440c0c4812030519415951011030001e00382aa4090301d0001003074821030241d6240d281c0ca01c1c1c01a40c2c0c0d0340d0701c100b10a491340c0e5956a0215281c5d6000081141340c82070010902d1a9a41c6115010700400c0fa100c5200f0300440381e0115440101d0b10900e402601601700460900ea02005a503025140340c0301095103d100521900300284c0d940071840000c643d441001050b030f80d1a00c0074110710010040c1030032070141c2080c4101c00c1c0c4598040c0c20348040301d400c80d9051000d501ea900110b40144428800650080c1c101034149110039009402080ea203d407402c0e0400c0036664034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677438129 1250 677436879 677436883
    0x11410031101051920160305160b120a11031008060601030e03090409020307090914060106030c0e0f061b0705030d0e1f0215010609030c1e06030213170609060603 71
    0x80e101c00072004031007030441d6800ca200703200480c00150700c50000c25106503200070b0341b80b4021802207694401e41c0000014030400c03405012944140051150703a543c11402c2a0076101c1e40e00803415006017540c110400a501c01140350002c061200e04408015581e041c4040b00c8840c00c6160b010301907040c8540c1d004228154031a04c200c07140c0d0305a100265040592100400c005844640760699252044030408510300e80c5600c1100c002500c11005c051b071050341e5141003410414164004414180341a00b074403031080e0413a42c5070399103810441d003100b44a8000400900140152000b8851544001d205854007031800540002a00c0d0218201c0304180c5900300229a03255a0250290700200b815441c0c0d81031202070f042c4044103440600541e8000c034071a008403100309500b60300074000141c4240741001400800d100b030704060660004051204414111420042d003c24812401019400035079000c00b81080201c031000b40c4042c5684c102d6910004001c5076840c2c030f059071090350034094280400c43c24a80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677439379 1250 677438129 677438137
    0x911120312060603070e090f07020c18370605030106170309150f03161e0f0c03090503010614090f0622141e07020c06041701141003110105 61
    0x141101c1901c0702e07680e00701408039640001c2d2005007440280c0400c0d10841d41c5400c40c1318442e8004891141b844e25007244024500070a0741d8180e4040d48240f610800c01c0d1078255009640181082444204031210041200380118814400d40c44030340003032401c6411800f2500f02204a0304214000e009550300c8545c428000710039804804816801000900141d09144080005011411812604062030241444000d6004842500c102045507120002c92074001c0000e0041c0900543c071000d80c43c043d80c801800d2000040410814001241109410148903002c0140030340b80140092251558a041e20b02851680d02e9006200e00008000150544104020644580d100810000b002c82302229812014101591916a886c1c0c9400d090b1002c1d801a0141078001e001d81600c9213058041840701d00380c40c400103001d100464008a802c407825641c0c4d20203407402c0d503600f441021707820300800c10024014000725040a40c401d88200030446010401c403400710449000d01074044080303e00d0001102ea0f842 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677440629 1250 677439379 677439397
    0x2d030f110d0908090d050d080901140a053312030a0912060912080603060702011b050c100513050f1606050714060109150608010503060103060504051009111203 70
    0x80d00780101900c40015401100d0910b00030b04400d4a05500300f800314869080c0c8100540f140e41c0120300860566901c800916840300104d0003c01c02104411030091142c040604242001307900c800108001c0707100590610000341a84031220f00a01c0107140da0718144030f099280381d21444954a00c404004804412540c210080781d0b81c0c014801e0611100100318604510141e4845030350b20500b0380025810000c8401e100c01070344a07480c81c5e2404100701441d10500030308510441e410300c0c042c113050802101806036429110708295403510a00520140b0f444102c85001607410b081c80f05015020741c0c4408129416401003050320850360039031400c940da66031021245400070449450800c0654403940c05804a20b11801081c907900740c3c4c40e0361092a0050030b0b0000c0d00d09680d205021000d010002080d503000700010b0a01c1d42c010f6140000003611024140b0020300850344503400601000b5041c00301c98000340c220903080001d0382850030403015103d41421090300400c481c0612400e4100000203860710a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677441879 1250 677440629 677440661
    0x2011505150304061e020a171302090403080c07050303011d01052b062405010912030918090b0403090614042301021f020720030604060902012d030f 65
    0x510f0740d42d0342800a1843c07480a0381840480031400c1a180841c1c00249144240760781c80d42d410041268104131118009042103428850b0045400b0060703c80031f20199009806003004c074666541d012030343c14903214000000f40303107000010020541c0e0b50f2040e10304810300c00c207441d01c0081d40e0703c2d0030070f02c00c011140e40c0c440d2103000e000c1e0b200130f180d5141c404414800c041c41003a001c03030207085031280040c20b1a0462048002c50446c15028440355038001c800340020054204280d80500c2503480190820616015041c4212090040003510740c915402c0040310a1340103840800500d0302342002000010b0501030040010801400d601c00c189000040d50b060b1050980903401c0441449403585508020400a50544c011064410842d10781030039030b4800c21000e20b03c050b9541415240c100e01100200d5840c1c1d0500c0031088000b41c0d25200055102d500c164420000621400a8001a105900c0281c801d11690036078121a000010390071282805409054600b841a00c40030400380c03040d2101070080c01400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677443129 1250 677441879 677441881
    0x20c03180609040c021c2a0c2105010f0501031a0601030e01060807050f040501031109090114130201031b0e1513030501020717070309050d020301020d0c020115051503 73
    0xc85040244000000030007050389141800380e01c0400c2c00d0314406041180942c00440c000340d20451210050341581c140c80c9400400f2400001e513050850844034040c02850310700c40010710400108460203001740c440155441c040912400d008910148444811101942462842e4510007000d000d07440c16241d10400c000b0381615500f000e07200320b05000303009a0426481d40030041c8408001c2c0715400141050001a105990402052003c504d91403d1160300587c0342a0040001c140c0c250150720b40c0403030454001030341e925122582c5014000c020100b91040e403140b802c0c040528040c044000c1c0191007038030144080c0300762815600c030402071078081c3c80c00300315444120605032500d885070314041e001c81240c150508066100802034410b15800460b210380d80000d42c40140150304030811140744640624030f01d0084981c1d4001c0030454039100e00c078010f000c2480c0c007008540e4290156103403d03ca0300d07000c0190300b0514000a001e4451004000b80100405030040359504109920100c100b50030300c1f40c07900d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677444379 1250 677443129 677443147
    0x5030606010507110a08060117030711010e030f010c020d030b041407260c04080f0f03040303050f0d0207060b04050c0c1e0f2a0405010303020a02010f02011806091104020c03 76
    0x255070102c8400c581c407042c02c00030601c0c031745d60b61006070300500865401010300398140990321020b441a12528040d9a00c20300c20f841c0000c01d6400b0061401e0400c2c44d103421004010710229243c03400030002070b00c50354240307500d050350903600240c0d4146070700c5c590f50248940413018040c84110b41460003c4000020403d0025281c1ca0240f0030601590706801c1c030394814098410f03100314000c0804c0d140700e100300d5800201080011020808140810001d102604541035224074065491185110007801d116020400250030f03140741c0241d40d4501d010f81003e560320350043c6000342c010005002d00c2841203141c4404242c2042541055800e50301c0c3e406d0040c100a0000b1254410000b940f003c0f1004612035511212035204081c404581c0640c1c820440c2c28465412540a11101c8400380c00b05024038642401040030950001c1c0e141b00d050f0702030a2409084002c000e080740035040b03105a41002424011040040010542c4818089070003103a0b82e000c1c0343d880004002c1a886140b1600007294018000d50f48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677445629 1250 677444379 677444387
    0x60406060c020118092a05040819060f020a03150605090f060c07080307150b0315010314070e01140306010506030c03010320030a0f02030d0c02100f050f0c0309190503060601 76
    0x71840051010858815a503201c2480c01d1b0340802c8443d54505103801280400400d80c0800034040c010241400d500701810403e07100d40c2c460380410b030505501c0300c030380c0c800040c002998481c405029203a581036540f44400360300078000d04058030000da402d0112100018100e0b1089050b50a001c5008011701814400d5200700030060b000242e540015000320314001401007010001000818800c01550b44c481518100c0c6108403480d0046850080e006a02881c040184140c0601c0c10b4942c0a82c1c034441c41114141c0c000d1802e076081d041a240b102c000300010409940c445464400341004a0480b04140c4e210818020320340015204046070200900c01840010f103461041411441e0800c40d070014a0815400245020015031064030307954000220401036042c2840420240314650420038000c00e00d6a0101d015a4a0302c01c02c50100071641c04403c0451f0721401c12103091541c040000350f101c0103272041681e1a903004006051080619035010020240c040300d550089480050143c01d0f66560b07440192 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677446879 1250 677445629 677445647
    0x4200a0905040f0b18030a0f03020c060c03010807060509030a0201110f030307230a080a020a030b06040e0114010f1b06020d05040c08010605060909060d05120c010f05060406060c0201 80
    0x961181028501040c109041d00c501445140210307641035500e07a4605004640c0310700580441d5907000407010750700e40144004110b03590406d40346094174103440ba0b024220028001c80c000d1070b00c5030103040d09220394906c6000c05036068032040001d80d8070b859a038070400d40c0c0d02c2c85041c1740681c042d003051103040055030144020444102c1c07440282c40940b00401131060a61b031003181d180b004186150201c034100b25070f00302da0001a194415400b8030b0088101d50241004800401507110306400040c9802114800d07000f00e04048809080c1c1c645954940103501100b0740b0900070036104051200e10810951700ca000406940e8100b0f444a981007030500106020034682c110040d070b05c1640800009404100d14820301d841140070f1070700c01c1003180c1481001070030350b0219400640f10709400e10a0343d0051f52a0310150b80c12010448440c1d240384443e00d40182801c0c100c0e144d06058200110301100248019003040c2c1841e40ca140c0700300500d9540b0740801007203c943d40a14000034204900311401940610030b60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677448129 1250 677446879 677446943
    0x5070b07020a17010c0f0804030c020904110402070b090f0628060f06050915210603100c05180a030b040b09010b130906060b09091b0d061211030604 65
    0x41c0d84458481903500125000104103c07802d03959211460b000980c00366042038200044d2400381c2c89410942c400074003000e13032450068850403481c004030302040a01f0310807070f14546000e48295101d10b681e0820b0f004d140000c0343da01d8028010600910704100303010400602c41e4018407420078030f0125009045c0400f1a42c0d55034a071445942c3c00010820800801c041c00050405940b40e59032003032500140001800703071041c6802010000c2c401143c200f0454045070314800c3c01481140c190755107010003e89041c00c402400d42d21149031203030881c0515402001088214968060803c00e0342d102024020300c202d2510024080d05900c10100b40000d1045400a400c0144080007144d108400c00c0021b070071400680402c000645d40c0c0b240d013010401c4a004610007080703002180d5090103040804141c1b8a940104500c070310188110160324285034410a44402070074004042003030316102d654a10800204083c15161401c0001c02100b440c500081c00741d00c11640840000c001c15916071144200d01c0c0e2500030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677449379 1250 677448129 677448139
    0x20105031807030f2f0a140105070c0e180d0c120c050607050309011505030a24060f03030e030c0a03030305150613090e030c03030105060a030b04090c060e010203040305070b0702 78
    0x22031644014130310b6403030082507502083d2641402914140d030340c1c41c460b021a04a001410f01c0789a580c89602c0f41100c24140310303003054010388030040700c0500c102d032801090301c0e2007404081207803001500f03090b1080c500320800000714001d0f0409185d8030100c610031000003681039540000091580c811540d40c1c903101d4203016101903055a9a6414500c080380d84000040000c010403001c94805d01404281001a807030040741c403030502000c41d8440840701d0014001616000e40045007010180825080c0c024a0b82c0402c03032580c4072249069103810521043e4001241c02060311142e00c0d000ca4150300c000d0004002078160303855594190080c2c40020000c4459000e8210444240d03200d038002800c15915200700d002130b650030002100100c07540da121000155006114999103080000212415510102c409940780c492042044000e0705032200d2090b0010b0070030900e02c0c01c10440e0940d50058540c0d40d10b07410107081498004a03501e028610020b030065102c4481000f40c2000340004080c45400604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677450629 1250 677449379 677449393
    0x2070f06051b030a020f060615070b090f0a240b010507021516030504080d0509031f061206050402011425061b09150c030e010302030709080d0c03030609090201050318 73
    0xa810f40c0c000d0650000542c100401c2c96a03010300c24803c450f4031600445a12500f509004071038071107400b0310700e0001c060001d2507001c00d00c0c2c41c0041003174580d4004402c00304d410100180ca810000d141c00b90300030900021200d041d402c0c032800e89000f4180e0004040c0d4516091000b503408110f1141c111041d4800741040411440035208401d00c00c44664a0098450fa42c0e15450a417469103484034501c046c10401c00305000d00261650045003000301d0a4990002080419041d0b881d400140100e034400b603c0303110201410320411021743c01c0a4410740c002d8175083c03408041c12001255038443d8118172000384048000c180c400341042000c420780700e4000d00001900c1040e0360213103000c4550451060b000b0401907841004180703207203011660324800078640014440034070390340034100510706c0c45210306164011002a030303010722030000003000b00681400c0f00c1100041200241282071211b5040c0c001a007010004518800d842c090316161550680d13a0034a0f6030364800180c8074240c1c00408280c15802080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677451879 1250 677450629 677450677
    0x1151202181e09010b0903061015080a060f031208160e01110a0b100302130b0a060305130f060e212215030c0f020607020c09100b1c0c02070f0605 64
    0x4082130107030030004000380e41e0b52508400c041ca8200010060a00d2040d4240203118441202030034040c0001d95082810042d00c83d001c2d00c8000e48800d400070048148076030740000a01075450148912081a9154103c02e0349510301e0303c1c00f00c0c8001002c041e012a018071421445540f080207400f0350107881c101503840003502d594032000100c00039507401d09840350a035020300c06d40ca0170b81d90308910392902d254100806144107010444004140c480c2805140c3d80e000004c181d44c080c14903100080d948207180b4504147c1d5031920100501ca42000301a16100c1c035030b903c0f0700c42e03442226102d08450020410b142008420600e4035520021081031098019140c540026850000001c0300e004502c5918042400c441d02e40740104003d00c010112011540000240184181c01080d80e40070241c040d64841140e940d0030108a4465000e81e0212140300c1c0c1c00101001c0403c06a11546250f090300b8409001c5005214005c0b6a03644803402031007c2c0c0b000414041002501500003082d503500d01c0280c40303070380c01c1800c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677453129 1250 677451879 677451889
    0x21e03090d1a100e0a050c0c0f010f0b0307080a1101050424020606060316120e0a21020111030c0903070504020304060f050901060b1c02070b01151202181e 68
    0x42a000c44140b462840c8002c0002410541290701481c4014000c440d145006802600e01c200a890000300f169203102003030b42c02c60008111161503501c44211211100140780c42d50080000501c480701d80791500c1c1c03000c5654600400c1c000c0854040301c001340f03800003190301c54006101e01031700058144401040005249081c0c00d580e072501419102203010082d98000019050923402413005105080420422000700725622407c1790b02c02041c0b504559604094209400600083c454000c6522546152508009200c480c0d81072991094652860384000404181e09a544122000801c08018030002e000780049002401c0600700c020105e0382403564650220b8200e07071040d601900c1c0d817512100d01c405e40001074040c0d15013001c0f04100811905181803400009030040079100700006882e2a0480d071801000c0e0140d600c000d4001c1144506540d540080118699400c202c13070380480c0340c090429501080e54425a007040d8074401508000e4505c550410004200350040d07404500100300507400b4680314 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677454379 1250 677453129 677453149
    0xc12010b09090d08150a030605130c0f0f120209062e09140a06080c130504020a0503091606021506010c170c010605040605030304090908070f030e120d021e0309 70
    0xc1000781a003180c10f10802440e940d0010b0041c0d0b0000a844541113064480c1100d110489422080c00542a11420344148403446440350181c494000d460300070a00c0005000000126001d100740002840d54030307248020510314601010b0740c003182c0d00000800b40e00344050220b100c2c00b98074403070303003650765030750340340500307042c0102601070000320845000c3c807801c400b08a00500088080303404440b91494220300402000c8010184015001c0c003040440e9201d00c0112180b000c0c2000a0040d0344441b170352000144580c004031100210347c0302d80811465515280c0129806413245a400f80c000303091078410788101000054081c0741000704040035800442c031180f82001c03814035491031441d51000003d60050075100b264104a200340d00c6c00d00100070700e580c000110780898030b401c41c010544e02060f0034044c15601401c90083d018a005103099010141e01040210100c00e08075a10880b00001d02890750b682c500707142d80d80002d40d01651080b43c5100c208480da50001c0134410840b8508141c220106580300c2c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677455629 1250 677454379 677454391
    0x7020d12050112061107080c070e0711071701090c03060c030c050c0304090c1e0c0318210204020705060f060108100308030f040804120804080f031204080c0a0b18120c0c12010b09 78
    0x840c4e001407044c2c00d81503802cae94000700349181040301601c845401980300e100c1c500c1800a504400f030002c00d444d25003908442c86064110405c003074003c0c0c1e282809400340008490341c2001a10f0f1101c0400300502580540c2c920807400d400542c103042c101841d03a0010035450035040140501801c03110b030700424a506485050880d56034001ea850410324002c2c00201d0f080700412401007071807609000d840600300c5420b580c4032800410700388406090020134024400c01c0c4014189010303010802c03200c040b699400c64010102a1303500407043c0d440c10482c140b00a818040181362100400104050666940e00c0c2908036014601e11464940ea0701b04181c10080d0061007180d00e8480441e08016000c410311030892050a2080954600070341e0907071400d03000100400c01002c134100801d84420b0088104100001283c1c440e0001d41d0700c2c1844000300c0176003402c800ca1910765214450f023440324010380505640c00d003003150f0700514500c80ea807002c0103040440c80c6104095503694a803001d03115030300c4210303075030182d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677456879 1250 677455629 677455633
    0xf031b050c01121a040911030a1a060103090b04031d131410060806130608030310080d020106150e04022a150f01181407020d12050112061107080c 64
    0x14924000141078041c3c03c00e200b00400d450082010f060310414400307880d8100040340c00113041c4003e40b80038020f031552504500c0e058441d4040d40400c00c00883e004a4400b130301001640e0142d42d64000440c1561060310000301030b0240300c004540040d0092142030442c0110300c14500350000c100c008180e1403841d09001c02e90172500e03004d40c3c50000b407030030314080c3d0030505084020201d6070900ca0b02800b080405004580a0243d01c00e1455450302c49a0055001e00030740c07001c1d02d580c2c0c10148030440c210042c0313009503d4035024400481c001c40b07005101c0e5030708a49400000c0c080c6803005901c02d80c3c450303004a146c4c5411640800c000f030400c01040142c50341041e031140d0240030764031400030b065182c8400141c802909841031400d200b5000c0611042c9411500c1000d1822400c501c5076030100003406054190810800a050034401d841c0d40218151001a1644c0e548481402280c040042a90028400c1c00c00340c1c02d030105044080350042d003090403030004000b043e601e4a80300ea03680161680c08a4404072240d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677458129 1250 677456879 677456893
    0x100b1b0c12030a0e06040b07031125032a0b1605010f141e013003020f0d090f14060c070612060902030103051b030f071205010b0108010605070f031b05 66
    0x4580010045504d10380c240c603104e0406040403813844451142520180910124070b50010f07143c0002c008500c562803402002d4454240c3c00c80c4085802c603c1030100300e07002400d2442460070a0040740d400320f024010341064000d8240781c60107918441d84070441034482d074011710045001083d400d0044403842d03030048400049aa42c44e098003204840e0192528a10240e010007041000301014442ca0540f00340034580b07220340640f003030103c0000c281e0400040e4224130528081090540201e04000c669003110160707006601183c80840f020b1301c450090240c080c0c200f070310038000401c4100030002c00f80340182450745031044450128bc40d22075035034001c1d000148400c84064820506029a20003402d10b60030940c1954155500d091710b8246904240b0380106114000795520303179003000304210a510304001d803000c3c1e40d191168003401c0c3c55281380c103480700c0d070038a001d880c85948a94240307070480e00250749803400d0012641d950450160740c43c40903030400140ac6d501c90350009840070312003052032140c002803081d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677459379 1250 677458129 677458147
    0x50309090903040605042d0e04060c030213291902100501120b190f020d1407080402060315060a09082a0f0d050f06040b100b1b0c1203 59
    0x16100d401003540c40719801c180010061160040c0c1501d0a50301c014604507002025070804000054012600b03000c070324140080010503241c00304940d4000d5009241c00c4c400d0820640d01a0b0a903c1511904001c03681c0d031038410032407844040d501a404c00206809581c4006a41c0e007407841039003040504001d40a55400c421122a404001e6803003000e460210521440d8541460ba0b98188500000030303140e03d50040008001c03c0f1140100b00d440c01c11010304103c0a50016111402904180c41c0c103a0114580148411600b0500c0d01c45442400b042d80c81000350b80e100d40c20312000382c00143c082c05910900d41d804070303055034644004d0401d035802a03880000c0326103048812440e10038100c414080d0070307900d0705050482064106c1a5810004e040e14004c15030380f40440414460304100354050024022607074501d000c100c012984d64004d80c041d112017401c2d03444000540004000d0352041c11600941005440d400c81d0b840c4010040d800150b40c2540c00c2443d00c01d000c01c10340c0c608002101025000050b84500f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 677460629 1250 677459379 677459389
    0x307050606100807021b0f030a0302060a06090b030c060703050d11030402101e050a21051503150a0c032c1248070905060111030703200703050309 64
    0x1002c0a1501d4078595a042c8004043c0d111072442e600d05e001c6008074243c41035641c0303030003882d00e2000318050210f0790345200509009407140f00984001d107241e820f1180008c1d05410500401d04a108010060f00e95280c05d46c0070006c7c141e000780340481c107200c400d008061640f8001d201e400e07514622080f103070ba50303440c09104120301c080c4000303484414000c90318000c0040c8699180d080802d03047e01d0410a60300c5070300c2c01007650301002e421868800950141c0d002443c08545400a070b008080ca13007004407074000340c08105030708d0f0b1031101d5071001448100070010790799941a4000100075032003070400003007036050358005500d8100d1600642e01d08010070907641d4200b803010440400b020071400c41e0f6908040f105420b803401c6811110284081000c180e0440c0d03549462400549800402c034018089207900c1d04022035180c410b41e1080f10802e40c50580040c60315402410258442d480d502c0195140055030740d0140d50b000b041c40c115032040d100500c04508121000c00115000c0d5000e50010746e184c51034002041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 677461879 1250 677460629 677460649
    0x7030201020408122503091a1c020a050a050d1107240c0e06030c0c010615020c0a0302010c08030a060e0a06090612030c1e0c0f08190c05060d0e0307050606 68
    0x50b00c440801c0112613008848074600800c4071101c4040174030328119030304040f02c56400e19004001c0042c9000c060790140e20844004080c0500f001d00c03010440726404e81d40704104c0c0106184580031545c2004403400e250300c1200101103e4070340e880000780121103078a51304115000440100c4d80501c3c00400022080e000310755100c2d400026890510841444c0400240f2070184066000d00402c0003102240c282103040d0240c078049600740c0000c01841e656070448400108508442d90094000e007045050f15090000d9040113582e0181c407212800507107541d0300c00c09036100500103550256580c1c07000c03440c6085110f109000700d5a1110101c0d4140c02c003a20b0004039943c652010302500f94414502d0000b913000580d4134061604828411135181c1c2c64402581061204a001090311002da80042540c9807400c03400e10650356588100c3d941d81400072800c0b041c40001000c09801c0c0b1102103c104264601a0020083c00c0044500407440c1114210141d00d5a001004120307241c0d0400d030308220007418a00448 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 677463129 1250 677461879 677461903
    0x17010207150605010e19050402070305300a0c050f07051c030510240806180103030c140d021506030304050d0c090b09150d030512040c06111609021e07030201020408 72
    0x90f01d0a246c441562070400d1007d00c2954000c03500842d825003031600810981e1080b040d0041d0030f01d041850261201c58042c0c0c646480c030050741e0072030081b80f002d000c10701c601020004030383ca800b8648542c400d2410f013030750040d001c01ca4080c403d07007032510042c4a580d40c0309011903149407004140e80c1000c7d009031108040a402c00140c440003000385005900c00c2111000802c0c03424100790f40c0c00d40324540407a20115100b03101c2c1d403440442c4000007081580c060080c00700280140c0b08070b800409045c0c0425104c10003a50403000682c0600c8d9003a00004000c1c5075250001d800a040300d14003903030342c00440c24046020348240c07425074194000300324100d400e0250f4281503a044a01000c3c070701d01070035059450b00440f0841c0313000d2440000b00004040c020070840e0020b011070049849180742515003049029594000e502c0000c852030b10800c03e500c00050380a500c03031030f200000c008040c00c102c3c4200003504060214042d008140007001461a6081c000f04900ba009a00142e80c46c1d0600034400c1c5028051044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 677464379 1250 677463129 677463139
    0x110c010b10230c0a0f050d0e0a0b09040f20071e0c09020c031b0d0908030f07030315090608031201051804120c0605010914010b0c0717010207150605010e 67
    0x10034107801424a81040d03002c030310880c416124000b400a4620b070000e02c84004055800d0081400c0a105000039400c1c580945580c503030aa00d050034061082140141c0310700804400d080c8103c0d003003403620703802c1817250610000000401406401c09103c104480110800075002e000070941c06000905070b1100c10424120b030010124080c0d07a0b00d040e54500c0c40d02c02c1b07040340c941c00300340007015090500031100300c56208030034480c54100a55246841e90300c0002c0c0030f0702007010440000f8500c4004016640102400d80d400c03420003501e03440540251000203040b02e00b20980446c04101c542c030b54800c00010303007042c00c002c640b201d8180c60800354403801070300514410340c807020f00c0100d0100e401c6010b82e0300c154000700c1e102c0001894082901d1490800d50010038190400001051600c03460348101c482d480f0b5403a00c0007569036242400065032044149158154001800602080c006208141b4034241120001407520055495416030f44181141041e240e94032100d0800c0250ba011030911404501111b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 677465629 1250 677464379 677464397
    0x40518010b0f0d0f090c0e070c11040b0d05070902040e09010b030a0206092403070e040b0303030a1806231f031112010f020403020315040507120204110c010b10 70
    0x190000190081d402c1c4011100400070741c2515240d10394000c3c2000e241c42c0901400180c001d841d152070040244c2c00740c800d6030075080001581d907510071162048010b800881d018446c12040d800d11016104508040d41c01ca82a440c501000940c204804d0000781080300006840b42d09010203014440d10103080b0240c0d60b8144001c40206682c00304017009410b030704a034000d0707071048070401007580f0900c0809250f04030401c580c019030040c0160030080d03206400958504a44685810400044490540c1401c0d0180d00500004540b500717183d0044580130318104204498030500e070380b40d43c150360003074070120006e0082d0701009213040840680940c00c1402c070340703d0b103100010310703010803c0301c00f000e01c00030300310442c0c0300c418401e2500d0746001f0105141c00d00d002444890309083c80c202c0a54030501c4100e01a1184031008200300c401503101c2070241d0f9000e40500416450b09803021106943d084040e80d1040d52001280340843c3c100340103004900b5000004182240c0e81000c01031007a0305881c0700c0082c40700f007034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 677466879 1250 677465629 677465639
    0x12010222060806091005061309230117030f0307030f15051008060a0b0d0e1e060c0706150e1503030a0905060f0f03190b0612040f020d120504051801 65
    0x104656000c0002c0d11144d42560311015400d000141a0340070b05d811400016032240800f40b0908020181c52901e081403008586004812080c803480d04050240e10f1032400c018040701200031803811516191208881c148080030140303240c16401500c048001c00d645448440d05416030b8010620410700000b01c0b100101c4c07600020440c400e041524080400283e0300000d00b1659400250101814012132455191a9504800402089065100411072244411041080d034081401c010900555009082c0c10b88402603401300c01d07041071000310b420a803202c41000c00042001c10703507001030002d0322040185042080f883e00101c0c0b00030f10350f140603400070424008c4090f04000d46030202c8800350381042c1d0303074401c01e16072840c030340240c2c0c420183d04a40003050080342000ca40c08201c0401c44942d0801140400508010880c1320304000e207907a8a680900150102e596800d00c40c02450001d018070010503102d42d103400c1003104405004002c680c0114080c402824001c1101080b1030803c8503d1040394101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 677468129 1250 677466879 677466887
    0x81213050103020f090111010932030406270b160201170f060d0f020301090303020a021902010e100c0c1811120c030711060f011d04020d110f1201022206 67
    0x30300c689814007d08a00700340d000c0c2001d502c444401900300718200799000d049016010340221020002124410b0204142d5140f480841100c040b202c050b1140081c940040d10b02140314245e500bc0b000c4140800b80c000101c54041c1d03001840380900c51f1400b40150070091002504021801443c08507104003501001200002e403a0103c0d008401105e40618050035840c14001c50361844500a4265007015804030070150950013a01400c2511b800b030303842c004580000151445140503000c0c1c0064a944000c2c28103003010b00004030103241034941041000300940703c500000f24180d101c90344200d40c00b044101482c1c801c1c400d000c200c1410b1074a05251185040ea0303c030b04841c02401c1e80d00c45407000404580c003503000300031203605441401c01f03407103c51901d48200488407109108094196921340400046800600c1e130680c03180d5801070002d5000c900f00d071200da00101c00401516000b103000740d440c0c14103030380b5501c4a0102480c40c400159542c40e130b0880d0010400221204e15101160080083c0903c82d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 677469379 1250 677468129 677468137
    0x1306060b2d0f070803010e0610170a06080d08010602100e0304032310050106020606150a32090f1008010603020f0409141f05030c040207020604081213050103020f 71
    0x101e9000692122424501205a1207001c81d00b8481c4400041e046003082141e0003c3c60403030b549041008079564600c018840b48409003000d05000400d0040721400f880d00d88880d9940001040f10001882078540700e00034903085525a1120101d031034000108211a0b04106400040c024142d0034807020b400500b40701d0ba80d01980c0401481c410224a2500880512013910388046115200302c0720701c20103100d400303001080d0a006110050288030b002a143d4140442403a40c41502c0c4088180380c030000d0a4121030f400a90040b01241c81c0f100c211000100100d00314041c0e070700342008001e0759907009103820400703840741101880c0d0059028401045202d60021144c504441941c00e01580d9403810a220110b50711843d0080c1900034035001c40d00041e84001482c4901c00c0ca4031002c110081c181045000d0401c40c022301c50503a0591007803210015034106600900001071019250504050b1544603507810601c00060f29001900080f502e101c282a503403604a008080a0030b00310b1800403800200d44007407007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 677470629 1250 677469379 677469427
    0x304060c050c1c110303131418150102010b151c0b0603010315052a070501020403140105070224010504180204110910140904110c03031306060b 63
    0x44646031003018460140248200b810006201d501d941242181c06044005100000c2d21600a4101072101c1800d00100f01c2c0d15404001c00b80b070000700e180c040c1c81c03030000300340d00201034021a200540c0e001c210040c6600602801100c000741030b000c071070b40c0002400c44110300c413003030b02c50b1928130b0b01810003000c158104c0d004010143c072070030074880c00c005843c0050040c10120030b810410000000080c810910642c882418500209003e15181d0302c09044680303101944089002c142000c3c0c00e0501c00350f601c020980c0341e10800001d402e09507261102d076144054503119804c41c3e5112010406501d50600c50703c40342965200003a195030300600c60700074010105004941c040c59036841c0701002381080c00202d0044550040043c05401d403080c0e001402a0480d02031617010b040d80244c031a00c0b40e03010b0482c0c1c40c004c01c1c0440c2160304003c001001c02028160100d4038202e851030801003130034580c1040c40258810843c44541c11403111280c50603100303c1c1c06070b82c010f0700b01a005101d0018448296501c19410070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 677471879 1250 677470629 677470637
    0x318070f031209080f0a022701090f0b120d0f020a0b150409140109061a0f0409060b0909070f0b0f0d0c050409060e011401020a080d15050909030d0e010608030406 71
    0x8010740b070903070b40c00602c0d800500192040c010501d01c0f42c0340000b481c401e01c0380f01b41c0380c0c410b02401140710030050342e402c5007010802c1e9403060011701140d10954050164960840c001040d500744180c04178400e00c02102c90010304d40c204140608100750400c0300d81802c6a040d00c020310034814291180608844050700c0d040c10708a4000051503a03075180d404c00e00c4a15042a1408182004e2940e035500804100b60b040b03403074600308045004600040e40c41c1302000e841c050100b481034403100c8200802003010340c404880190f5039420300303200b54840081d02c920601045000700714a034103041866100d107481c6d6001703000b80b0004112204499045005441c0e990003070304008118100e500e0000e480034003e5070040b0002901e41800040c01050003143c00d8101e81c40c028290003604074413001240c94070804000039104450070060b120b41c0800e25448400324032880400451406c5e254400261030040507141900d407036201182494681c02c1c0c0f4401c403070b1b00803c103200030400246030100c566113038007507842414144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 677473129 1250 677471879 677471903
    0xb0a020d141309020a2d03021b12070303051303140c0f1b0a0806041109040809030d08040204050901200d111603090f030206030a0c031b03020318070f03 67
    0x55441c56058404a540d09034070300390859210151000250454684403000541d80050003c07003507904100b44072100c2c02c1302031849540e0000030b001d80107980300c20715404680210311603004a049007441170b1605244604001c1d075540702c45080040039030710054015603000b150010718000094105081c81d89030000861186c3c0ca54480d5001e40341058105d0641d90340e079005a00c02d10396600d8120060b10301c41d600490b01190341c02d441d1214140d0350307903084400030b061031f0f0340008241c01450701c510803aa11510541170070f0b2500a104010038144080c102c9520040361aa034240800c510b803038040c107644210204000c0011400441080800740442080706244038400500100800d8168208804000d48980e42035903a030300f5a030405240540d034003820313000506502000305414240c109050304a83d0010f081038110b84810010310001d01b4180042d0741456580d800b08644401610003011910741c941d180141c5926120791418039115261540c099160845070b03013407141d0311000d0000d1080d80d410003040454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 677474379 1250 677473129 677473157
    0x21509031c110703060b010f050c190f12030f05010b030f061302040302120334120c0b040c090c2105070c050f070603060909020102030711010e130b0306010b0a020d 72
    0x40828451115016000d403e5011051100715041040138010a99400c0138035406104115080d021780c5d110019260040010615034201c0e500c00001228040c81c050b2910700c1c45aa540c08004000d0218800801d0302c40094080440003441030394018401d408000340303180f901c10740882c0d1800e4010310755445414000c00b0503880c002594180c0f009140d02600010720054000c01c440c1c5c0d2074010314256402d040c2c403039088181c40e5520014003118500340b440b1040100400355074440d5001080b070400c41c1000500c2d0300f50390118800654150145000340c94007070065040030031010943e501004200244520080a0301c22401d1410b1b1f4880c02440032100011035855400b4125035881c1602000740c03103445040380c1078010355000700b104402c031a00c40e101004103590319619401902e0414202a0268000340038503c089002c040d6a141170740d40c145088509d0b030070200009003000c4c521710071070740c80c0eaa5204440d04c00b81c00c04100300c50148c14090081406c0c80d04161000b551100c00f1540d6400b003005010442203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677475629 1250 677474379 677474387
    0x50609090406110c0316050613390b1806090a03060e0c03060705030a140c040302060d1b051201091404261801031b02062205010207030903021509031c 66
    0x8200d2400000781c0b0351b510000c1ca031850480e600d0f84025143e90180304c0c04150a8501c41314201c4006901001c200b80d00600d064034a00f0001c8200ca107607450440c0c9241c12601c82c801050241c011303104520406840388015407150035100b001c0070344140a04000c00ca101242d42c1e4040003c01100da11210101f020036103070840508107030102040b207030140700d800d090288440d0800051442600d0000c4100213503090b50000c810340860680b202450702800700010300240c01d040008020030409900041100c0040400703540300c03142800c0700c07540001c00c041054800342d41e00c844898010300000340184800340301300710031080c0d03421b02820040901c0f80c1e442c402503102900510382c0c0c005204c48010fa0f5220003000742c186400d9101c40e107203580000d1074050b402250741700900c400404101d05038000c000d96681d98590750003030814280b081c01247c034042540c0700000c038240024114a882644c80440f01c91440c410311003413900000141c200644c00707120300c0c09180c500181030107459420881111031a030108800350703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 677476879 1250 677475629 677475637
    0x903050d090c1224020a0e04092108060103140f0633070b011d04081b07081e1216030c1a0601020606010f1706060f03040c0f05060909040611 62
    0x10f074502c0105891400c2c003603812440e00080f0800c43c070115020303102040d68800c0340304540400c00492600f2201300214101580030314420b62242070303007820042450000c0c400c000c0d0018200c10000324030808201965915002d0341e01103014202d448402030a01883c000c51668005111a01030308080d0440e4401d108003068440b080c40007208003142400c0034401c2c0c1c00381507000c1e00b0103544045c0c00c2c000014005110f404029a00000c41703c400e1000c1e281d43c1e4404000f82d2105540906981c07107103104100c0140c1c28031034000100084001048a805003020212604800400c400e030150044022001a0302c440d4003180c1c10083d17001c0c1c3c91103c042c12480c050b00e000c00032000c007a00035242c4009080440c581ca03400c1c90b0140038240c085940541d10b40740115201650480c4c16800210401c040880c83c03002c1d0149030360400340040c050360800c1c3c81d4141c01c1c0141d400840d400e503860354861804015404040301024003503c0b0a42c2c80390700c0c041e40d400c0072407002c1c0005000288a141d81b00c0500740d0380010201a5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 677478129 1250 677476879 677476889
    0xa060b120108070e0f04020405100801020c0a11150703051c0e031305040203010b04120203070e04030f0806030a0c180e0714090604060e0112170a030e100903050d090c 73
    0x110361548990824035008200c00d0140c0c0c0101c2c410580081030800810354000e108800307801142c02c955072940e090101811004d420807094100d1402c0205010781c0070b00240800c904100010702307011004d8149104a0801036040c1406401c0d419050410300100504a800c801c2d014100a980c50b10180da00604215403a0203010421b80342ca49004607404000c8001c109042c20f00035003450481d181d9040000320300c028490307241c0404040100300800e24840880c0380007540024242d5015681e192031080c2d1200707007141e003240040d4803c20002030f0f0b1034201d482c0030340002d001e6004005e0103003640c0e180f8154144a0140e4240d6814004440c80568240d030401201d040b680c07019941c96540c0c03000b44c02480e07121145c5140c030030585000010b9050401b44112030440300803008200c0140d2802c04070040b141e844490503212400304501103000840740000a148040e100d80d00000c0b0907030b1410b000d600300b0609050b02012542030030300c21b0000c0b95000e0b0a680c0003c03500d600020720f1901d01d20307040c02d510f5525840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 677479379 1250 677478129 677478149
    0x60f02160b15180103021e060301051003140403031b1e050d0e070e190e032d0c150c162012030903060106141213020910080c030d02150a06 61
    0x403400400f00c0d4444050f048070310075240800c29640100f0f0706000d04c58180015038004005000420007803514107840403404441e0704001039848034000f045030030040211401c4c4c02181e06d4010039100c100e0088424501d141c11840c1c002c281c20f61390f40e001d10300781c80844601b000304140440c074044120b0781c0e40c3c0640c4148014a044648499440d0b883c0f840b1860304503003000000d10605001c1c80910414043e2515003da60809180b620314011100c140500a82c0119030195802c45840c02e50990441c2c02010700c0543c05005054100400d0300d401c0c46008010036841c00c00100f401138108002d203180c503608031a90300070f03450f040c0360040b00307001c41012050f240501d070b001c1907060380c1ca120894044010101c3d00c20a0b01500c1880c2e0321200e044d20003070a0780c01c04142da00310402440070308614151382c080c2c1100500c800400e00c20610340000361502c10980f24100510841901000700c444200101c40005d1800d0340030346102c242000d4003946405440c3c1c4410818105140000d10042d00e03a40304c3c0c0040c05080d11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 677480629 1250 677479379 677479399
    0x702120f07030305130806180c0111070e0709050a0909020312090f1003020c030d0207050c0109030309140102010921030b0f060403060f0f180b07020102040e06121f09060f02160b15 79
    0x55800390031042c4408c00c443d0740c020140b00034020b501c11010803510a503040d000385121440d07d14444e4003254020300d07200421002c42004031300b503a10b14440b00018043e442c000708030030801c1d004141c10401c0c01080f170b1058803400c011070f41c0c42e40c660000110600004071584c40c0107030103400069010384107004001c00c290000107551800107a080e400341006c18001e5045030180c414400040d6010001070201501058400c00100403281f108220040001010702c000f0a00b11000d5442c901d142d03192150500800c1c10b0040058084c6616200d00c800e10a821180d20542c2550100490800d225500014010a443c0d0720141944022a045884120103600c4104641c5100500018446e0500c0d04201ca519080d00081140144140203840603907500c1303e401403294468030100716001101140007045400ba209109402c033000080810510203106000b240321145481d0510031103c4050f100c83d541481400800c0b007415903501001403446c0d01002414a40c0c03500204100c400740c642c6460f65000200318 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 677481879 1250 677480629 677480641
    0x320030d090f0b040614070f02030337120e1e1e010c0e0d02010c1203050a0f02040f121e030c03080a090f08030c0c120702120f07030305130806 63
    0x218900741100d4540c02030310920382c2c640600b050940300301c0c45103400042000c2c2040721349503043c400403d01d0902c10000c1205d945419800719046804c0342e5000381544194014886000f00310703031800c8840c4040c4498120300854030020150441c01c9403048501c03905d94035200a00009000c0102d8035550101016030350b003060100c0007150f0b42e1003d822031030091040e240941a40244140074007803d5000580f100b41c1003130300c10401d10020440f1000306a041204484100740445c4965021941c0183c10b0b03a0041058500350b9043c04c00d4501c0003424002952042100704041100b10b543e0a00f0740340e048581000712213072420701064490318105000d855428030b0004500f0180c01001180e20540710b51103540055580c0810401110b00b5108080c0040300c41c1d04080740080c03c0700d0000d5900c05407860340c280c14900d06031801b900d002e800d050700602048000030300c107080d480d141601000500100c0002c00140d80c1c40300ca05c9884d0030042c031004060104c08601c0c5103002c1820f131030001c06040007400f110315a160003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 677483129 1250 677481879 677481887
    0x303111615020d0503040f150b090709050316060203030c0a0c080408010b09010504050f1501050d060305070e0a1e0e0a0609031710050d08090a050d140105010b04050a0320030d 77
    0x1070101e100035125a54509043c03a004005891007950484051401c03020203072180701640c0c11104100762626620020b00000d0759410f0805401120309950b00700442d401d000516185c1115102c3d000c15126950b2001c2000d29400422254001c1803203d0f10740c0c40d44092842560391200b92070000f04212000300b8041040001540124a00c03e802c40d001c1c40141d81c3d43d401c0c0310444074252500c0a004110500060b42c1d404030003284043d1703110615009181401541d041801c031401d40d0400c4544d904290700c1000410058520340b40c1040c0c00407000c2190a02c28250cd9142d88580c4424242e0140c6407000b229440c5001d0041e800c5039600708406201e407000b98a0018000360002c912800743c01c000d0790101704018401841c49041d100e018103070410000d1140c0343c80d03156400840a10764494640b450204513520f80011401501e886500f00d501e0803130600d2241e5094034816000b94440303d009000411141c0c1d5481c45c003200f100d4001c44070340491808c0e442d00700706142c07050080c0b9815125144100c81d903142c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 677484379 1250 677483129 677483159
    0xf0302030705010c180b0c150a090b0108150f070936090c0506180d0302010b01140304030801170a051c0311131406130306020306040509061003031116 66
    0x31803402002500944c50301a40d400d80741e05083d48003203001e00c5007070000441c5400201003c1c8003010440326240250110000200c408a40c00d805003916000e0200821440303502d002e001d0039605024184914014448103001a0001e040caa45100c8102c0400e072072074000c0011401070840302150170207181e0100207a004081610034000c0886500e035003444901d80440c800d1044080d031202c2000561841c000400c0305c560030a6603d44a040c1c440c0c00e62030b011343e0301e03442d40308455031190700080f5100c0b50b28800549244410302444910000400070080000d41c802071840c150348040e104107240220122102d4507013010b039880200544181610a885040c0b240b407000c000c0c02d0655014004003410171a160090b000e210a41034a0014010b028008620030004074004035201a241d14141410100448400400369101341d90560b4000184041400d040c010b8981c4401142d00038078081c1440c0c042d4030b83c01182c0384009005c00021020034244c0b008244402c0d600828580c030b0140f841a1a40382030903001c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 677485629 1250 677484379 677484383
    0x603071b05032a0a0b060a0906080f010c05031920211024030b09040c0603060b0f180f150309011a09040609060f0c030504022110180f03020307 63
    0x6074040d0302501d001c3e48200a2541c8680d500241401460590300c0b40c00201c0d010b0310040d4071203021000450310328041d2103000001e0800341c00908074085520541c81c00c41d0401041030080000070420441350105131001a0065000e02200060345480c01009061880c50b03480f240300016000242d09210885ca03200c6d285101e41440c8214003d03032904c0340d84031601c10051050418102c0070001c0c008200103001d0a0650400082c240400c1348100440010b070359601c1200c01300d4221101c0c0109110311507042c440e00c405401c9640070507140c1003103000c5803000e6010340940d90000031300c49007081d08191640c003d45518000c000d40303440b0890740d101c6240c034003507001101c028990390701c0c0c08a085500a0360040c00100b549000d0116281c0e61a16141c10001c2e1000701025104240c481c82528840360044c80380e61200c880507540024a801c10b8410045104904c3c400180741c8494101c011503890804900d6a8510108400005003200c0c140c9190b4460141d0450150040001d280c0403418160044000d0114078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 677486879 1250 677485629 677485657
    0x80f070c0905130b150901080f0115030b01050d02040f050106020a060b062b1b030608100507200a08040314071211060a02012406090605090f0603071b0503 68
    0x40d4440c40c2000840b007007115140c0d001883c8880c2e5102041d00205000e401841002d10400d00e00300710740c0401d20050081c1c2c400c0e00c055100b0380031080081c40a00c2120348402c3d1110701250f51a02e192910740c08140c060090611911540c2255011566940c1c8541e45180c0a408144220343e56000040d46801d0007241c20364111b0304064181d001890844100c480079400c030313644041101703c45107010401c0514401020000c1d580e408a01103880001e00300b90440065903940454200c0c10500c1c2541880c0841e40d915802e1030a02e0241300c40c581d01b244d008801c05240005009280b0550358090349031800e01d40000c1d1403608005004401d000041031810700385503e610880e0b98840d541e24015904030300d107000c09000032841041c810854503010000704014121031001140740701d508806405d03e84000d0342d07040f00311001203104014a0303401140703202c0101540d050460038a14504d02150102107060000c40c8140d100000069025000b80d410900342c900352103414264054900c0c01e03a80c0c0e03622141144c4809 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 677488129 1250 677486879 677486903
    0x90605060109050f150306010c0501090f0c06020115090506030c0901030f11060a091806090507090905011e03110111240c0306030a03030c02012d06080105040f03050d09080f07 77
    0x500300038104e609103680141006200e01440300b9003402c1c540010345001e0410200000b1200403804c02d0248022643c0980d9602c00b80c0c41052400c0f0182020710f910840c190390501741980d030402900300101044828210004c106569040d001a003070003c038451555002c0342403400442030001890024464511455108409040400800074180114456040000c0111000307010049072200e1001415040400100301903858040d040141e840071a0200c0010f1401001040310482c1c5009480c01441100c43e08100c0c0401c1468441450542d400080c09010100450070650b034890000e00e9006014201654241c02c0381c1008550150100007041040366040d5010640c400d100c81c0c00c490007594001c008086000250360f081d4068207294094200755541d6195026040c0b686140e8080711080d1600000045902d090f00300c1c04a40e0140c000d00420b03072500080200061903040c6032480503070107050031a125400441e400c0080c00c40b1480061280c1f002003034041c000340d00c04010340f40c10b9214800c50004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 677489379 1250 677488129 677488139
    0xc041505130f0b030103080901030f0e100b0609011713060203070c1209050612040c03060c0c0618050d0c06060f03150b090f06040f0b040203090a0b070c030f03050910090605060109 79
    0x1e1202c0718018654020020401040042d050500400c00b440c018140415411501607140c1d0071911a41c48138031540c0c2011041e001c94019070b22980c141180216821400c242c5a440001c269480040900d804044140085812a0341c100030103505964000f00c00d41d940c1c0391020008107220b00d4840d0858081001c40303110040c51707010350f040341e050302c50103407050342891040c4e10340c0ca10340d82019000ba03822402c025008008603003c1d0042d04ea801d01c0b00c0d164010f156000303142c040304890900100154401e410048000041c6000c2081c0404812501d0500315281003828000001d000c164007401040d01500d400008000b0104c4c0c51a140d40101242000070000d42030510020400440e15012101440000070340149413680c0952410b4241c0380d000075584400c1e0011038106e901c00d0b030750312a140c1e0010380c0e540c0410010180090b0f00146604d04407450181d1030703601a180124000c40841410f807110b0004001140420030304000600e541d0701440700c00000d04001000309410b603030f0540042c030340300e0020034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 677490629 1250 677489379 677489399
    0x81501030819030b040903091a0c0c010e0117010609150318140a170304060e0a03050702060a110307120e030708150406091a06041a090f0c04150513 65
    0x4100c942007055a40352204920121184a459400850900d6500c068100b4075848912074840203d109441d201d404504280340410f0000b14200405102d820402c40e01e4003409000c00c10411041003802c0c028a500e00d13200050785d20104402070303401c003a281480002006540a9948001c5400041c41000c25000c400d100310195070221804401007191801e4a000080503003804603070700e884003c240c40340e42500f41d8500e4808001418040c50840010043c041070050601c10100d6410303200b0010000030915135000351442c0103056000c0d00c82c0501084490080e0302410880190400034002c0d83d03036500040c41d24074030160700c502a0038001105d80c0c407003400d02d09002a41400340c0c0c40e000c0062210700c0702c088030824900fa0040c4111410381c0c46848800020341e80c0e600051155403116003800301807400300300b40720454401d44810010f080e100c80c100384882d142c6008a923080702e4400c5030400340e6500d51001c0800c51007141c2c020501c41c091000030611281d80400030300350400111111210752503403030213110307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 677491879 1250 677490629 677490631
    0x180f05210427061502030d1802010c020f0103020f0c061f03021810030b07020a0b0a060506070f050f06040f1509080327031c061202030d081018020405010807080f0a0903030906150815 80
    0xb2b0118184000762030262402808624001d841490094a000719801103a0696009180d5182c41944003030140480070082290311908200d007890b0300903d091546d000251030321100340e2580008601c0101145903404803080a001071a001482c0403002d081c030490096031084c40039400c0c0d07070204007500850301d00c44490240c00120f86008040c941030010302e498007555019180d10848151182c4001005400c02c01d0011502c031310701a140c981c0b090305031401e000c03c0d440d4028202e0180140745c240014002070403034069035003124994048001c040380800c408c01d00c0c2121400607040e03510000c58000c1540c905a4040d24458407171900911855a5030b0441060703840d402c140080d40342d00310807010010140310b81546039200f2516000010800d07581e000303031089081d040d200781d000d003a0001414441940c00c409090b420003981c1c60700c45a203150500c240c803505800a85880d80c81c0b40c41c0c034000f6082c180b01e50040c411a907000b400800030031401d280f00301101501842a15141d000700340011500720041040c2e0303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 677493129 1250 677491879 677491883
    0x1d06040605030601060318020306010b28140702122e0207050606240406030504170705250f0b07021005070f06180f05210427061502030d18 61
    0x341003130707400c0410640190078002c1e07039500108100d034004800341e64200451402411600301d910707511031844c5c0302085010340e124100140c480400130004481541b040742501c00c0601c400f0200e849081520010b0011070b01c0307000f9030b00700744078180d400d4080c1006108202d0070070a1100318808840001b0359114280d01407060003400700d4000340001200e50800c85a210300d240c241401404c0c80311401e81c00c0c40141d410a401141c0044e984208210402040408861845c1c00c01a03a01d41800710300d0342c0e8950713a06106440c0d8002c01145c0f161811040110310180c10182041c40c115218864640001c20140d8200c000c00764840d0034084007c40149004408071a061500010011406412a00e41c58090180c41c046c2d110056941d02220010491351a224040d20784114058a80703008110311000500c0c4240b11000c250390707030400c0100b04100c440c0d00200d51075030503030011004481010041d00000c1c881a40051640700b1441940c3c00d5003035010004010101050034100144980002c440540c05004140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 677494379 1250 677493129 677493133
    0x60f1f0f0b03130804060206040615030b34030905010506010504060903060203150d06050702120c1e0a1a01090f022b0e16030212010e15040c030c1d0604060503 70
    0x510484425000441d40025142e4410b43d035040e0301c3c0e07100d034841da00039844400180c10100030301040000c40d01404d0130750581c0001410700542181c4a482c0b459401506040480c1d00034188051821a280280000380d55501003044200e000700c04064007400140c2000c46803546030400140c0c2960007002070f502030311100d580d240d91040c11660b80000a610280840c05510004444407085940c1c0c0484001702c85d01c56000800c56050a0001a2030400c8100345044c44490038011500300d0b000c0060300c0d1a480e1041135065489840c512011070038101c8141d00502824401c20388010107122400c0b030181280c01c4010108102c440100c01d480032802a002c80b02d10084d510742e20706518156141c0140001040110b0000300c841740000c6036450504c5201070b00a800184510400c01d603d8041c980030011041d1100a001d42020700c054a501c4029000303013040d03040940c9011400b80020390100b44055a0300007511618540c031402d5201031b05440300d101c410120b02403000039206050a0207004101d81000d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 677495629 1250 677494379 677494409
    0x140304051815060f0f0a030e1e030a0f1b03081807080c010305151f0306170d0305130b100e0601020c0d110d0807060e0c01110a02010f11060f1f 63
    0x304008541c2d00c00414113661560034800e00490400400090035403290648000032040b4001202e10700b0201d00d02041071103103444481c2001108408030803695440f8440c42c10690004011030151001507402a01b0041c400c20100c1a90070950841106802484074418022411201001242e99081207000d015019000022066280d5009400ca0743d00549a403101d081c03007001410105800c0c0510700101c0c0807008200c05400b806981500c0703010054000c0305242c0006103145010581e03280201d804401c10550f94400003102441052100000349901030f10240384d90038a03081507044c01c0028010290710600c0040400c03141d40c00021520344031640986034030071a00464403078950380107410700000c0d00103901c100a47c1c0060142c00080c04c0c002d202c1d130400503041600401035441c08400500c0b182c18081c420a070908200300009901815a90900c1c210b41000824907045400d04100301e901d55040c03091400344850005440c0a5500c9545c10b800c401074018851120048224507511844008000742031b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 677496879 1250 677495629 677495671
    0x9080616031a0418020f040606091701060513050702010c1b03080a060504020706050405060a0618021e1204020f190b030c16030f08161e020a1403040518 67
    0x10704041c0704078201e052142d080d00b1025002c10107907600300d00580700f0341c1c501d441d50f4811854058a06003440c40140c50405c6040d007071440282c50030660340681001c09004000d41c4d024058250060382c0130340310140100d0071100301c400c04040030744426590b0001550812881485c000d00c90a13010f040d00d8410385044090111588041d2120f0501030440e500450300d40d00046401d4485000401e1214410040001c1c42d18150034880c1c140741c006401d1200d041d00f01001040408001c443c1c04000c8915030200599650506100503c1c2c00000780340d06023141804250740452070560b019151140f8001d030344c0058805045000c101104081d8040701b8140e50001405001d00b40304c81d4040c541c8000d00e0111149054100c42c1c1e4130080201402044000404064020420030350100d8501d802090b22031480304200c0003544080c01c2400e86041c2649030440c4003610300c3e80c09100b04a400d600390741001000030f08803080c0c14a582c6039406809020701600e1881400c204084090804034031640c610445103020301241 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 677498129 1250 677496879 677496881
    0xd080f0f061c051204060c031d0a03021e041401080f06160c03020a05030c01060816030f03032a0206060f0a0f03020d0807062f0715020d1e0c0908061603 67
    0x200c90b09540c3d51254260380b1050128203401007029194644a00040d510149001403c141c444014030442c040004000206038075050302500a40b0760441d00c142c1c0f502104480c100d2102c1100345620fa119003000c52200001041c004880d050b034603108107032080d20158100b4503564170029607800000000c081240c1d101103108010b0284000c2c40f80c8165804008117840d00351030341d08040c200307528903513440030204460042006605101841c1205580d030312455602c442040c4045c8207405400d0588030008442051301d0f5040341c00ca6154000050f0013130320001003009694820403111140140c091a800c561310340790240c021001c640d52820095400750455003400749810714900300725200740042c0f207217600042c4c090107048258602c1c0005007080440c0a02107000d43e12400c1c500c80c6000c01c0402610000c03404d1903440c1aa65400c2480241c0c1e44c80c0000400c2c00285821403141d0b42c0061140342101e8052010703004481000e4880c0c0d80d100c0f03196104c07403010307443d008290b640b41d05c4a4140c44054031101e020b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 677499379 1250 677498129 677498179
    0x5041b1d030a05060a060f050108040804060f05091305010609050a0b090d05010b061603020d08010e070311040f080102070204060806070f120b0d1b170703020618030d080f0f06 77
    0x207019600001c0d103941c1d4803460003000b81c1d00443d80b1500c0c1c1e0800c1c4000c429403e40d03000103007401d01c3d01c0403c41c03e181d1a1001d50344520b00442e020008020002400107028408030343d000741d005842c5281c00081c01d5410401031a00f0b003c0c884c000760003d100040e143c580f4503000c1080c5d8410b80801c0e494010508200036103848496001c0b0340035500c80c4892001c5544030005860780080c40310019010b03112626000342000b03180004031050085a000503c5401003035201207510021605001a000d20a03407803050a2740641e81c4000b0f410446030b50081050641900075241462082e101070220341c0d254150a500c40341c2c111028000034035501b81c13015009110318a008006400381c0000900d200d40000032038401e071000300061310301c1440e120103984007045005908005142c3c10f1400e0900701012280e082e1030745840d10001c0c0c40343d0800705d4140404605404401441c080090444402882c01d59020300f0380310f02240d00241d9a010070002581d60b01e00c3c40c031034504c20388000381400956841d40c460300c3c0802c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 677500629 1250 677499379 677499437
    0xd050c010f02040f03030e0315071b08040611010539070503030a02270a060c0c1d190c0503060603180a06052d0112080f1305041b 57
    0x348a0101501054142c80200301030080d406841045034210308003d001c0c1c19580c13000b28004d511600d25500700414040304160000100c0c034012080f401d0007e44201100100d0101a00380340d0005400030b17020b03402541817040c18641034024801503407031400702c42c0d00c844412200091001650b0608030440180c3d6008500c442010036000d05043d03007500d80519507041160002801035002840c0050298041c403d520451400400c900350b01c0d4070400851401125445400c092103000e46d280020400c11914000141000e4100124809103220014100090a41c4c9070a60a403154007443d03c4001c40f80030381103100f90307076860701413854a07184240669035100801e031140007400d401890104c40030074032070301102da4000c00010485090030540a851003180c504101d4520b515001400800e0740c25940b01c03030464801e01d00480401c6000d0405070460700c154029890300e10400584110703201040038a00c01980d00c290360821150f0039991580c03030b00740160481c44000c103d00301c032003410802c00007545000e054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 677501879 1250 677500629 677500631
    0x506071404080a03050d1a030c04050601030e151f21021503070818010209010c02040b01300c03020c0c1002030d0603030c1a040b130512120420030d050c01 68
    0x5582d1004141004810142140010720000d44080c1c001c003180584a01e9984c0200000b6607403a03914002940c40349182d012500441e1100300243c01607010f0f601610341784424000b45c2c0c0e01001d80b0000b90081013800c0368147c84203102c00c46d40038071503016240031005a81d0007245041448003851102c0030320102001d822030b80040d208900090024065015500401c0300f6160614039003800c0c629640440380510004089070301c107004001c4141e0b4041aa84400c64050310005107640d00100102c43c0c01065601c43c203c19070801440c2c1e805074621100e0b45186e8481d9030ad04000c41c503003c4000b141a40704000c0314540d00d511000740424986171200c1c1066180301240112490714801e04149410f80d590b43e40240c4c04910302c860180b00384040340301d400403c0c0469665440c001d1500341d0320156054005800c010400009407460b1041110401954980a51901d1150b40f0307482c4410021502074802c4508607001d10340b81600150348a0121043d80c0c8903903005020b0f101c203588003441100d072900103518442c419 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 677503129 1250 677501879 677501887
    0x915060201050606161719020c01020c031f020d110a0e01020105010e0619090c020304090b060a02030403290c030a0c11070b0a05121e090c011b03021c0f02150405060714 74
    0x8000e400010f200a1131f000321500711000c1c0a907000b900307141030103810300e055402180c241020f664020800315070032040040c0550303514206098082c02800348200c0950b401d8913082aa03907171081034502410b5000d144c0e59030b120007035111000481c280e40c001e01c80c4015000152000c62003510303202c0007403401c40c2200d10700d402d45e0a5980f0169415280d00e98481805604002000c0c07182841c140200342c00c0c400305075219450f001181034005c1d3b49203e40d1201074608001144102600c0d000d00590035070201c1d00900d01c8010341040000210b6644c010742e500341180745844080540702c1c1c0610003030410903112001408401c0d10700040f00304241d101c604403004000c0200709540c940e94228001d54010b410319800c90707001413080c0940701a4070780f000d0001e104983c417074501051240e0740060b1060000040798210a45810380b440e0980c034001420160103815081490b000c224650b01611180e4903442d554210790340340504440c842ea14900651703010382990400320014180364007500c061100003103030380061450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 677504379 1250 677503129 677503163
    0x6060708160c0612140a020c070e01080d0e030c031b060d0908070b0708150d0311010515090a060308030402241611010801050d06050a0b0a091506020105060616 70
    0x7095255000c215415403100c04280329180d405604002c2442e10748108120140c3c5100440c403124100070824104650001045250318409004060052029030041445543c45000c0c8640321010004042c001400c2d03581c0e4403a0030f1600003026581490081d0140c01c585103c500101042900081c103d50480020080c03410310480c544204809680030307858017a1030384c40d13501c0c04080865001c0c20744001c00102c507052280c5850074401c0301e42c000300104c0b0224881c1d0307000e150540343c3e48442d200c44a020752800c020030524901e400400b450401040b02c0481050b40c46130110f90466159005c00740c10759105000080040c10010214807040400213100101018421865080c513400f8448106041d00320f07a494008001c2181022482083c01742850391443d030614002c903882520f0040c0140c0202d4540700800c104220036801017403e900040e0180ca141c0342c035086071030081c0558140701c2107600c01c0c0e20400540d091044c440c06028050080c007403450459408040c0b0101c40d6100415690a240724054800c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 677505629 1250 677504379 677504407
    0x20c010f1b061805060f0c5205010b100909050c040f03050d031b080c1e030109140903040302210f1614090702030a1817010207200906060708 62
    0x40100d00c00c0004240c42c1c0340c100c0010401107000b0b0814009558107001c0c0e002d030000ca00740b00e6501c4e21030b00ca44100e501c5640c000315004102000180b000354070100100230301480019558818050702440080c1b2626032443c00384811240400b840c04001880e412050082503480d402c450303040304010040310309042d128641a05e0b1444540d02c1100c0c07a50105819015468050080041402d01c1d01ca05034540a59500c3c054000040103042c128160300c0001c0041c14051140c442150040700303111210340f25a1110001c2008010703c403a41010070a4400001d11205030000494090301d60107050281c5011007454100500b43c03205940b5116030040c58080a42c05504220061821200204158481d46080c4140d000140c520f00c2c06402000c540c3e0401c0ba209400008480240590b0315040d009141e113504400c080d60207981140044400d05140c580f00480150094201d207801500a61142508861144601424030003000d80203100c03107001916500d80300020308541405448110700e0302d8142030070a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 677506879 1250 677505629 677505671
    0x2040f02030601180305100905010906060803090a170c010c030c080315040f0207020d12030608100e06070f020d080709030803040b0426040306050907030c060f020c010f1b06 76
    0x250240d010042014541c0c1c011108032a80c0c80d10413034003100c5030450721100c4e00c0e203803d4100c1008803612020b00a0030440254820400d21790020010046240c0310f02c02d50344c40b9404070f49168460141607031301181031094040c03031552101c0c0300c00041460310100b100640d2901c400c65410b50a010103641c524000c02c003845c0c001c61240701d65000070800824500100005c0340c204982e41500740348140711305030040e2a00c040801c00c40350040d00040f00b001d0301c41000c4001d002c40c0d42100c0054011003801c14803006050304010765110b018000d89002c4e40d00c0400c111075801080d884140141c0c0040101180c2c00e01982342c0503000786092070304941c06607c946801480303520030380b01169003403481c800300814085140810403000d2079040384482442000c107000f00c064090b500000d01926a1913001c18015032080143c080255444008501510f0b510500a401c1070010b140003030150080c0c0b44000619882001044560f84040e1690341c0c07011849038500501140b107541c202c41003940d600e090703802030090080340d07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 677508129 1250 677506879 677506901
    0xa09050d0311120703020d030b010f030b03010605040606021f0b3d0c0201020f01050709030803090304030b0415150f0e091f02210103050304060f0e0603240a08280204 73
    0x404c0d503d12407031a009280c41030300303901202054507280403034410f41c1e40450821800481ba1034041001100580024010409940b040c0c0d440b40c40c15100140c000d801040003408410708912000304c180740c0300240400d40f03180204040d030105c2c003580b07007c1c000c0b5000903032505900302c032070791041e4003045580d214002941c07042e101d400801c0807501c0180031582d041003500040d5081d10001c0c00203043c1344001402801d011300000f48142c0002c0001074a034a01003090b80d0007950008560009810a418166004000c041c0b1910307040d820004d81c441d034130150b0707568602103402115510108616000714150b6248000c2d0100300765004821900c4081032a215204552074080100141d50b0415500003e0041202240d081c14890711580100302241c0040240d808403007550034060684000030004a803c414900705a9500000100901880300e101c4281d1090b000d42511180c2c0c41e944580c0c0401540068030f2140405d5079209990610003204140b900e50700010301c8103aa140680207960000701594015001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 677509379 1250 677508129 677508163
    0x180e01030f1b180207051c090e15010e0609030f1606030606090302060703050a02191209050904111210020301380a081003050102120103021003020a09050d0311 70
    0x140c0240719492038803980880d100702c010703242d240c80c05501410f15002c804116805a07404580b980a0010a00c4481e100200d0741c07505002011071258090b001807094020030340154816400280711869502e400642568142c50700f0300b05001e12801c01138030b1381c000761001da0103000b0760002104500c8200300e4154200300c62151480c029081c20001800c9840340c0e8020b600f000b0000c142000940c9849044500d83c90309440e003030380c2d91034460a00303038544800d1040240c103180d00c4c46041828444942041c40d90000c0700d64034956025915410800380c40c50544002d4000881b4604002c00e034909110714142c1c0316082400c0d603085a119080b01c0c000ca8209030301820210002554004907001190442c3d14440c0704101d000040c5880b0003c814003a001d81e01c00c050074003640c04d012070b00400010010328001d6500ca0000c1d0354440c1000b00c4026861405e2008a001d803805803403070850140039001380c0c2d00144040d41c07800c03035040c83c1c02c0801c9140c040304d41c8103400740540068031040b01c1c0414000354040f10250340c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 677510629 1250 677509379 677509403
    0x3031e15130b04023708040f0305040503060c07150b01121d01090b0a0e060705030a0b010c02121c050f07060b120303090f0d0915030911041b0e090408040501180e0103 73
    0x6400301c5c1c030020b4240048000c00d910481040c594000000542103600640c070a2400d10f181d280c2903d00e84256084154144a00f00030080314000e40d030700070110b036881070341c112030a5951900864140c81600590502043d85c2c0d404c03070480312040390b110421941650310b071081c0e100f10705404a421941d00d03881c00e0700c03000e544804100350040f060150010038001d04005148502c1c0ca404003e000d8000a00b10651441c0c4804180c1e00580c400c80081c1c2d007040c0c0040680a070440c03500011a6505021701201220180004154400c14060001d03644002e401540c0285401c0550703985d0030081c000005440d03440a45100040310100e01080174511644500008000c04808040418a0b00959030152010840350003410300c213003044d440301680da07006a8100800c0054807494149032076500c1000d010f40040c5000d403502d5520b00700c56180040c00d41d09440700c4d21100c0070581446000079044801625008081000300800e500c102c068002e000190599030038041c1c1c941302c2105240c10300780d00545070078200320 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 677511879 1250 677510629 677510677
    0x10b07060f0f0212061509060c1c050714060103030f030207020303160f05070918030305180f0106050f0307051c080708040e011503022a0f01020c03031e15130b0402 72
    0xd8006411071002c54034074a050310f0008001c50346d0710a41c0314584c010341d0302181040b10482c0401248502200540c0c101103540b45000004225030425441943c4504040000700603299004c500e03a8181c90300360f034072040f02e200c1c085419006584480b108a07014401042204011010041d50100c0300d407080300d890182c00c0407814940c0c50092140c00c0ba2050030b103820b80c17504c60070600504031022681e050a02042640e1210010700c81060492414501401001c000826011040d440702080e01d208886042d41c45415500707160b502c2025000f00341c1c0028000c485181101140da1008960350300c28408640707080a940c0d102c045540060f802801c5541413240148400d894442214210240e60326085003030003001d84500240c0d101c841c3e907070071100f00301e41100a0300f44800e008230747d00417a4001c003c0d036984502b4010195650301c05c45060350000c1a0031500300e4400c07d880a10f500035054101c000380d501e4812410041c100000100c9040031030780c1e0f008008525110360010f0300606203c0040c807601d5448076 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 677513129 1250 677511879 677511907
    0xe041a0f090f060d080724050c0405060304060216021909050a0b0f10020f01090b0402090c4b03060a0807080709050405250305070b04050603010b07060f0f02 69
    0x1180c6003a101e10810010072040686482d80183d000904880861014007203040994003481844405010541d2500c1c041881885001c00c3e0719088840782e0081051340e48854005090f4042d0f80501c0d40e01640420200f004680c00d500607042040c00042c16080c50f816681c0020074030303030405001d110700200c0d40d0303c01c01c6486080d2080c42c0d4410b000c15424441e070400383d00016103000c0c503c04064410460150003c1104c0d00c200900301c4c102c05618000c0204201c03505240c07086042c1160200e01c101d02c1c03c0300040880d1011010340d00508404451740c8031080d07a1445038410704031519444940203901070780b41107140a8a0626260408584910759581c0c203005e028001d68a4a80d04050541d62103400108880f210014117401250f450f01070005498440c0d140240c24414100c180c10041002c047d490902012020400c0c4101c0c2e02c54000c0783c4005654404007029030080b07228565015005100410412802030010255a4401c1e01d00007100f0300701c03018081c221441d00010004a07580850907407440508 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 677514379 1250 677513129 677513149
    0x6153e01110a0e061e0c0a0506160504050918011e0c111207030e030307080a110601150804061e1a0105030c0304030e030304090c0f1d0d02100e041a 65
    0x541c00389032815103500d002400d44040c0c410240e018410000f00304001c424036079a1030410701115044036940e021030040c119500e100451041c0c500d40910301c0441e0350440003151085419001d5210075051610380800c0105030000202402841810501241c00b070810a06c100b0907407034540e40c3d81a540b60f0103440e04200f240d00301000300050110500700d05954000006510b0100d9601481040d070f034000d24a41151a0b840da022169098031000c01c05104010228003d880380d2a29942e0780880e003006280b80d5981c07502c0c2840398800d000c00391412407480d58402c60502d50710600800c80894210085041000031580301401d03c40d140e591181c00707504003a1388810400103c2000d181c031500b2360a10011103062884082d1008060006104450f00940c906000b554014003403004200725803510103901030f18030203203281a0b80c000f600d241c8080160344030701031207400991005404c8998200240d400d00c00f66480c007443c01024001082041b0440e82e8441c02040c00c8c006080c9001100701e490b03031041c4200307a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 677515629 1250 677514379 677514401
    0x5060a02030f0624160203011503020411030f0604051510020a021203070c0b03040c050604060c06060906150305091c0e09070212160303140c0c07060306153e01 70
    0x2d141c2c12403000401000084594007000f164403580c50192249140242c040c0081c000d400d9420445180f0080c9c10f0740400100300e9009880a11044a000c0040419480111065600c0a9071440841d20f42d04140e03001c2d9038800f0058210200b40c10894000030300d4000d8541c0c1090060340400481e5003117007864194a1141300483d0700440c03c200301c40c2e507100031441c114041e04420040c0480003800784041c20304180d004080c00303030000d81c0d80c54a03820006c2c507441d62801e05652042c2404000100206284200e004480c4034000d03210082540407421005400701400310380c0c0522a125000c0030b403500d10741000015020b5034a8285812680005015541400410000954020500e10010b0220710011101c0d40166104120300c1d00351146001d40c000c14407880d1044800c40440c0420030100c42680050107040c40800403598029903d1400300e0542c3c000d409405a140012421302e00e02c41d024000081003405100e00d0031414a08031b81031040701d41c3e020394181180d03440000c40d02c984982e0a100b2512808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 677516879 1250 677515629 677515639
    0xa09060f02070314120309030a022a040902012015060f100c0c0b03010f06031b050a0509060f0f131401020c09040303021b01020c0c092a0705060a02030f06 68
    0x390303500040d44607078151102070516003804090a032144014410356104a00481a030381d02d03400d1800d29580d60383c01c006000d10141c070a82e60320450754120703000c040c402e0011a42c3e0305251b10083c04140409070101c20422818040c0c01c040b8202d100070380e20900e8031074449002c01004005e80c0031f07407501c03407030400500010300581026119000c81e85aa1083c103909500724100440501c440d40361810074403005a205c00c01607900440003007590781c850189541150301c04d03a4140141c3c2c00c80c61040540320424032400700031550411442002c54089d4016114180f001808203060001088441c12076900031441c2f00346c443c00001e03044003842c1082400300d014101032a45c2b40f12110394040041d607a0400c810750a40700d0f039518000a02010b01c00d030101c8440821225224101d2802c1c048a24042d40001c865071105000b000c020325018100030121512550350007040850200c01c1c11119201203c0d820100c034914401044690040703502040f080f4001c8460050040e84c1e80741c015031300498940c01502d644e10071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 677517985 1106 677516879 677516897
    0xb071209060c0f1d090603010603080309030702150a091202041b02072c0105060a110703080d200714012414010804170702010203070602030c0a0906 65
    0x185186071680740140060343c40541d14804108292684141e9000701040c0a20f0910700031500083c0c00360001806030349a8580c0c239081d50045503020700785d600000314541182080c4a80260303004403451320900380284620010b010003510701c200b605140d40700321280c0565555a002d42d0540610922a08440c5118003019481e10315074450000a42c03144411001c51544031602d14910005640e500e545982c00d000401c0b1094001d1201a420401c000355559184541045180c014500400f00d02ea10741010f003141b9016103603503007404001000c88880d00d4100c621480196001f0b698069031083c880c0d264040e0042c01080c0312503450590a02c0420504081002c01a20009a80884a485a030040c2c1d02c0300560350420123031002402c0794200a100b2820500004c050841c0c1d91051040d02d10301640c03a141c07203041ea00107a405851141c0c0004560900d203810403180d00090030715040108003 = true := by decide +kernel

theorem cover : BRFrame.Cov 677338129 677517985 := by
  have h0 := BRFrame.cov_init 677338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 677338129 ≤ n) (h2 : n < 677517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
