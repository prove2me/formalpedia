-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:45:19.956251+00:00
-- url     : https://prove2.me/submissions/93566061-a527-4170-a9fa-17001372ac7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 917625899 ≤ n < 917805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 917627149 1250 917625899 917625913
    0xf090b030114041e1103070e15090f01060e01140726030c070204050604021e030712140402061b01090807060c0f02100e0a140a050d180e0c040e09 64
    0x8040c21030b51002091034050070703000305000116404c03c5460000403c83c0d0412051840f407400c1c100d282c05035032040d069052043c4000460441c62800d10306005100304800c6004041081c0b00f00305442800702d961100744040d080c010450184102c10342c1285002c18108222081540c168201060340641c1e006d03907070640145030402c404e10040c0440c17880c00360000da03a1415030030020500713401031044080103407055445402051441d652641141d801c0242e1000070184204030400020958004482d08404141c84250341309201c1402e000f210551541005000c0c026502d03542048481c0d04803a0f900038940c0c0c0722264000010209110b00d42e28030740100e94181e141d40c1e103890050b080e01c1c000d030012800c001548540051454001030798046103c00c00d10041740c420745e0445001c0c0341506102025000e0000c007503038214044d10125041254501510a0710301c22080140190741001180340d0b6030001c425400340c200138920040b070b00c041e00625135414103813500d07646a5100c074075518142c44011283c3c00002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 917628399 1250 917627149 917627171
    0x13110706020315032a01080408040b0d0606030b100903171318060f08030702040911270609010b0706021e0f0c0c012309041803090e01060c0b010b0d060f09 68
    0x1002910407021881280900381010004460115585c40b100d41030060000200342048181001d41d0060840e070450261941d034240c1e05100074145030300c51314000ca8607003622b0b00028145000300c2100414151a1074000510703503901d10034909a0b5900a040412043c4420300c401c0455000010003040d8202d01c1001d8005c043e4400380032180c035903103e95034000396040108854600841654101a0100c4000a42c0381c1a0f06007050042551070034254406402c0002400001c060f200c98480d9505070152000d46a41d00c070140402d1140078061328442e28828400c070310000f612a0010400c080e906425504070305005c1c88030300d41a400c030355510500e60101191981c13042c00100040c2c18454003d2070501101000d0541d400c1c0b03468100e000c00c0020b000e0000d00d544c2c287c0c1b83e90704031000340300000700018114603c1d42001404407040c0d01032060261282c42c0005005442180c1d5041003d4001074003622691070207a054610360b0210680314101d544031440054800703014114100108000c03940440d03803034102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 917629649 1250 917628399 917628403
    0x612150f080c100e091308041d1305151305060106170714040b0c0309060406030e0d090605030c0d0b0a0810062907020109121115091311070602031503 66
    0x84030026008401242d841010f0700c0c1d00c07803d80010700400780c1d400d1009881e02d400d0044140c1544d580946210030018002030750143c4500d0099074aa12510800c1c40c54440101964001c000702c2c4000d411640041e0b00200c10304046401c9a41048049440400d401c195559031414882d01340e129001160150001211039078840740030701d6010a42e45001c007406501800c1520300d038050750088494842c40032813023801c025410022149001c50007401320f51126910704004018000c00b10944405000305103258a82d507018210300b81c1a0340341c80d1a45da013169142060f640c0745070858081000c52944407840d141c5280c0302c000000020f04601d4000e000f60007038106001094070040d9104001d8803000900502c0d2071520b0a510100440e5002e81c1d040c1c1e20110707400100c1d0010b500b40c101c5c034001c2c0d8880050400b0842906180d4011a5003500d01014a43c00c006d01142ea40c051a81c20682022003070700301c070f10700812603440400181c078060b068504240658a5038400c0783c10803a04402c1d61802e010715407550b4030301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 917630899 1250 917629649 917629663
    0x180305061e090f0d0f02031e09030706020604110d08090d210c0f02090714040f050102010609110d090c120302010212090a080a14040302120d140906040612150f08 71
    0x5a002000c0010700411182d60754005901c481d810400310b849085120307031007402114036550780b4400b168100c0c9100400c1800527440070441c94420711481a00140e810700100b000340c401c903008107804044009050a011410410080807a03e0710300822020000f5070742e031b14025001d1070045150411200190034030079031140d00d034044001406900003a84000440ca641c0350620264142e0384040b113a241c1c1041a5150303c0b0010b80304a0075003012402081c00b030044200c98088480c240d0003402960b50712030a01d0100e0705500300600390140708200f4424048415000803140512a240300800550341d109424090003e401c81100113075000608418842c04612400d83c200035030001501c5190b959548003070451040b1051030342440b01405098016150850030740700256000b4001700442c1112201a03901c1c1c1664903040c5010521405081c00301d00385803c00d640d60840090181c03841c1c2801e10740305440c03074013400c180c4040c02521451204491007481d05000c0080000c8983c41c525a41014402410004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 917632149 1250 917630899 917630911
    0x180a0504020c1b1905040906020903010615030f0606050d090c0515120a0501060203030403200d08090609010606020c0f130f0221090d0c030e1e03010c09080303010303180305061e 78
    0x10840c0b040702e03c0f42400213850340454100700d0700000c040c0007901c0c1c841c000e40500020781c0d40c55442c029000414500008698002c1805079600300000030150640700200c90403400350034005a030500c607c20304441c0715031002c15410b000f00410080e065403900000c401b0440d0180d411081440071a2a818840504092a402c402513200034001ca604018000303540703000c010405030800820000072017025884410380907140c141d0707205440c2c01402080f0090842c2d482914200c00d01c2c4250b0000410260043c80789600b9140030740c0c00f900c800550340c81040a54600480580d0740402c007843c1001000e403852103844581024200b016841d0300e40310182c4100e01d06001107502c00725410300700300f01010f480850005203030407842c200000d0902e41400c04841013122100504e80081d104240c00d40c000d60329889041643c44110700a0010000d00901164500024071445035180c2c410300040c0300090140054030002c6500e24911803185a49071038180c90004151100b0300d2164504c0010b6000d80000340c107203640700c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 917633399 1250 917632149 917632159
    0x102060402030a031412010e04020a0501020f0a1b080f1606080c12070c080a0c050c190e07030207020a0b0904140405031b1f0b0315010b180a0504020c1b 67
    0x114203074000c01d8440035505001010007070b20220140b40386030a4020b50303e207140e286030741030341660b11480d61401c0c1000603501039200c0ea2106600040642c03000032034190b400040805401405010380d1a00c10100000c1c421084005d6221000300302c07d0810060b020102c5140ea000304000b194155001c00102d1aa4101008101c3d12904000380c0c101d64104035004403e0252088510703541d80207007240d00c400f00b039600410002c0b0001c1c1d0505020b9001da005022a4010826103d00d20080002c1048400c500c18801c44808003a05c000c0014140d0b04101e960301110b01e050162a150040c5d000444820054001561241021030f1300981c504140c81103440262200901d10603e0510b912030980e01e0245c4100c0d01c40e10300d914001100e400340c051203e0b42c02c40a00d07581d14100c488442038210003402c4800150350091040c004103502c034001d1501110f040310040703071101d03246c4199a1b840c1f14000041c4017403150051080e0b0301c00146500d581c401050f02246c0c600103004403121030000b500c00c2028600c4020710038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 917634649 1250 917633399 917633401
    0xc010c050405130b15070314030f061516061a060417010e1b090601090e27060f0612030c030a051824070609051c110a1a071101050a1a010206 62
    0x42c0d120f05050340f260b041c00441c0152034002c2ea00e0101d03a08c806005803d082c10b8000300c2032000312812907441c0e9000d030100300c3d03c8070784840c0100c0d84841c1d180580c94a014a2590701885480494103030341c445010200b00700c520080b908610004144158002d83c0185801c3c01007005070141910203118018440100700e0107020050460b100c8108204481c0c000c20f485002d40030003068181e800b42041a00500f090356001030385260040e880700340c400d149441e00b2a06c00f16403515a4520f180881c40381d11403084040340300c03020386450b410b021403005541035945642c4002c0002c40d0f400d10b410406400003c005540750340c1d0b01d01c65140300e14007035070720880d41d103010340c000c1e8080703c42c0015030206800600c0c804071207a0351200040d0600704003402c3c21007405000d5000c2c400c4000d041d8a220300c04c000c088601038841e03080001440c3e00c420317070790040703280080e00c1044440030440100700c0000304503800660030700d45a00c0c41d0024008480c04c469040d5200030909584183d62000c4111416000542010900150000b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 917635899 1250 917634649 917634671
    0x308070207081212072c04060b0f160f0b0f04030306080a150c1b050d141804020a030209090a1401050406180b0d0b1003170403050c04110c010c05040513 67
    0x20300c0c010403801300a80c5000300c000542d580e1003903100710308166128400444044584c00403410100d03040101c980a01c0c10300c107003c0381e5a408002141d000e00030080c002854501c01c00788c00083c040c0590300803540001504c082d4004a407058508502440c035100d02c8440e642000d20740603003102c030181d000c1c849a8000d80c49130701c0440e00c40340f0b4229903030300403035800710341985058801c03141345c4904c84000064402000c15402032001c00106160340c0b010326101d0110a48466861040034040c0f160f01e5a28420858034141c405d04003500500404d480c0760601501f07200e000c40008100080443c0c0d004442683d920388600319844240d00c1c20b004120652f000c100150070704d2040490440f5040007031070312304c0c0c80715580b06054403200c0e61002c4880c0c2010811645082200c4d240710b10380201d10003610100c0c040310442640c040504100e07002c6990045c000c3c040c044c030369002d01c00034103940721101d107040d507007440b2104584a00f80901c0c2103c844076a039960369582402c0812121842401e04a00c409140c030b540029 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 917637149 1250 917635899 917635933
    0xb0c101406040b12101b141e0d0207112103041a13031a072c01031b031e0c090b1608040b04170a020f060d0b0d030807020708 55
    0x1030491070544001caa004440c00104081a41e8803442d07486a1142c14a41550107465500005a1003000c082000b51421718007001c60b101d00b030460558182000800400607a520030515a41c82418010007207030900008031500d40480e0420f410941c1e81070355240f005400ca00d851a10520380394008084c220314840600d400307998030300480c0a480b0103c17600302583c450351000c10303090b42d0f620384814050030800f03500c03803a01580045c0c10021540000b9180b001044038580103910305d00041c5143c011403205020040400c6810110907030646050654546590000012140101c440c507a200c0d100031a0b61b80d82c080e00e08428011200e01400c80a14180001e400a50b120ba0070004903941c1c0130300700391203c00c441c0d09110405004900144100300004002808100082c040c008503010b1060109034680c40c1903500d034440800980c001e41c40500703400504002d16011300601600000c0d8800010030544007008a011054081c5041c0c1c00304541100704401903a040002d8009040d07800094240f1040802100f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 917638399 1250 917637149 917637151
    0xb011101050114041a040f090201020708070605030708070e12010506130207080301030b060102030d020a0306030b071e030e07050604121407230d050a11091506030a0207060b0a0b0c1014 81
    0x83c0718581702c04000d0b00d00031402c0c09804110000420402c1060134001e041c3c3c004200d8400124054040d42e400050188030101d0313007008840d01070712014074542c1c40c01001c4915202c011f000c1001d00038600603001e001c0c0c481000034003621101e074000140c40c1c205001008491180d46d9001090540100010000512400b060300e0441e0b074000d050214503121100141d0850040c0c041e2482c0441c40444c1401c40c45c3c4d819001601128007400c00c040040e125201e08a868103588100000d51120a800c0015010310a0780f0001e80e4003880400e958000c1c0d01c0c0c60000c4c40c90307440b660110302c0042d1480000c0c400d0118032040400007920f201c0c02482c00d10302e450304003118901045800311012005604030700003502e8451000c0c0e04e0590210554054403200e10300254090354080080740282c00280020321510891070248508800041c08103055035102d5070040c02941c0f251404540403600d40c041c0c44000c3c0c40788042c403070151846050141c0c95003603071700c582c0c0c0c54801140141c10101d410070000c0e0595a40e020001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 917639649 1250 917638399 917638439
    0x906011401020c060d090b0f06091b03161202120603010605030c1513050a1203030c0504120b27071802070305030106110c060a0c031704030f18050d060b0111010501 72
    0x850744609202e40c01030010021060081e08162400082090501240201510400046401d5294bd807940d064001520800d210b055440c10001c10105986402c1c01c0d00e920210b0000c2c0ca03000d481c0f02c02240541040e41c101ca03045120300600c0c8402c2c091186800c0c0950009000182c00401700c040c50540040c1d145010707850509007003240042c15240150741050240007410002d40749205c000c0d511516880802d0f10200c05a0020b4544650340701010b105400b15002c4610080d0102d00804d143e45405040203006001c6500c9040307480e04203c6528403404520200c0380681000d00380312840c040c46690340302d5a44903003015143c410400540020f801006590640340d25151075503071200e000301c100e440c1c10f040401d050b0b807110001c80c41c490500d5003c1c5004a020f4865910310807518200140321640300400d4a0007000704101c3c003415000648280d099030102911000301d0314425581d08082049400c4441003618895103031904200c2c3c95030041600c0f0000c85150008010309d42c9080c404001d12a804841c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 917640899 1250 917639649 917639659
    0x1020114060d0b100909080d0c092301020a0b0403080103150c120203060415080d0e0a05060f0a200618061b0a02070308121e0c07030305131203050906011401020c 71
    0x41400200c1e180704c030901130030b902d4104100c00c903d10700b0010701c80d41000f01700c080c8280c100341c101e904080c4035843c0041216101441c0c42d01090741c3d008080507005280c9030140c11489400d080e00082803402500e10b0181b801b0791914421941142400501d0541e104130300ca109a003862074a500d8160b104268685400d41d00c03400686039200c400015002c1d21685035840101604200301103500100840d19502030a03080d21600354031031b05001441800c954038403559500002c10702c5188500f1086030002c0c00b1407035007407601d41200f0141c01c60a06004404e00107602c800c2d0301000401c6039620b02124400c11a02c0c00c0c0e402090b580c5000c0d00c074801d104a41d103030b549803511008a94a00120300070001c4070b0241d80c1c03140da81502c88080d4040801115011111403035009000240900c03452800f00d042402a80351813902032421a00342c4047c0c02920703000e04000e480e20352110032500800da4051110002c1100c5a4002c101c40c101914445d00d801010b0b00901501e0210040c54450b5a0300022010309008d01928 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 917642149 1250 917640899 917640901
    0x2071202060712020607030c03090b0a0b040912091806051c08270a0e3c0a09020108010504050606071b050a03080d050c07020f0409060b030d0e01020114060d0b 70
    0x2020800310300a0310b100800d5a4840091009510703000b00b20140301c0c82c035643c0c007000b118803411011400d0350000c101c050001100f600c0441d0509100f40c200c144d400101400108041c41c05076542d101150040c1c010400203140342405200d40b00340d14071050202222024140304a41c20034001a1044150500040648191101c80c0040092020556030402001d6201c040203440740144a0851400960107500c20b81442030007041807010700c0c0744c00d0300074001c00450144030420078036010b402900c600b1441540d00c010360324122108040c41040c5209809c800c5000c075140401c1c1c80050450072060304071511031402d0804100300d03516250140c82c42d031034004600034a0202d001ca507034980107401e40c00c06500041881c80c08028460074100600350b51013078600070071007a981c0e0b03a000d562501903410b000358803901c103109900c40752415400801c601c500448002400030107080002c0d03c1c150010b007201e000f0a0740d080741d24a4035038082c410b2030105c0d221124110607034078000d000a8104100c29600408040051b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 917643399 1250 917642149 917642153
    0xc0a08072d230a02061305121506060304050a060c200c0321090306011e09020405090c070813030b0108010c0503041e170309031c0b130c0e04060b130602030a020712 72
    0x20441d03014071307005040580c2e10038108010074540c507428041c440c0102488502d80003440800580c40440d2110004c4030107007501c0d41410003140358000381096420303208210251340404d09a1068541003206525003035a24400403804c240600031906004000344c10080c1400440d80703000c03c0c071080300070f80142d0314408081c1c0e50442580601036803046640512806001143c407a403c02c803026003259452036030b00c4801c1c2d511030105043c0d100354090386410801034004a001502d031840640325451145550320f041c480d969140315015261680180d51488201004101e801028410710361190118070f4110301e940f401c2e4481d1015404500c400c02080420403c02d50309208100303c0c8078000710300c0701100655a04000c10310aa91380c1202c440610324181110050600125501c00c403219154098900c0040444034002000101081001c00c000d11100b0501c250755940d4500c41d400182241d200701d5510398114001c031001404040d00000195442004040112074000840d20f0454101e051040300c03640c1c045c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 917644649 1250 917643399 917643403
    0x5070f080f061203030907030b0c031018381813050c030a15140411130b1c060c020d0c060203060103060b07080703082a0c0a08072d23 59
    0x81220fa108500000c818840c40b03103030103e03461048034000e0000e10202d448480c2810340912060362840034481104504020380503840305c3d10000300c00310f69000500403000103034841e000003281015a1203980d104d4003c4601170052181029400d0042d200d00051521188115807c1031010707000349442d200310048182080f40800c0030366442c00b8040e00380c076824083c0d0314021a4588038a40e070424094241b944007506842d843c0070a51150b500581a01c040040c01b10500c00c1140f00c21051544564460030314186a0b2102410020384107400140c1c0200c03021030b0f00340720341142e40750b9241d0021500090320041000d0382c84055844403503084100103030349481e06030040c0c0c000c15995204499881c0d001c0f4800702406500c03009491240e0290b180e03110140e680079880c241c030b40d0805011007207130b512011b103800003052000013a060000c00041114512a550340f9049003542081508940f1102c40651310211070b82400d45080310b010303001042c58000c00c91682c480b04088010301c0021030003c07185114040e481c1007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 917645899 1250 917644649 917644669
    0x4140d0509041d070e1b1206132004030209011e060f050913090209060301050f13050f0a0c03150908040e0901230a140c0904051f0806010905070f080f06 67
    0x9114103c03130002e030380c0da881a2010b2104032410005030400082501084030b05004540d1030000742003a03610555070b880e040020740355240788003008a65031203083c184640c485001840c921109040d140b500c6901d944108440c0d403405803c400940c0c49440a00302c4c100c1c3c1c200c2c42242c151210760415600e5007010580c1180c050040d00340072544a640c00e041c0124242d000c1c1c1c03016134a113000380d5800300c682c2e55840034142030380c20a90781175072580c6c40d10703001070303080c2c00301c03a480201d41031244080d03904004d40d041c461858801288029074111402101c1001003001c1807410b20034980340c0007000e114260241d2a054094041e600c1900c00750264000040c0311000c003036200e95100120556038252545810a00415001089901c0703810b00d0b140603401d440441c0b000c03010a200f04070a52400c0d01e458070600a0001500020706a034019882929440e07252425240c5800007400c20800203100a40c9030019800c00e565001e45201c1c140030381c606118200b40c2d03200b00361079885041d440c040d07801516241e01017484400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 917647149 1250 917645899 917645951
    0x1212030603030c070609030204140402010923030a080d180b01030206070606081902090a02120a0207030302070807030c1208010521071a0408010b0109080d1d0d0b04140d050904 77
    0x144c01008600e207500003403144180d82c0280c1d4100a11104180040d0ba0711708141c401901041c07d018ac10004100b14002c40404100c3c07000c8952a400755860111349030000b82e0600311003110000c0f8010f5030038041c40c4101d00c01e80c800400314071491007244d1101d03101c011040c000a0f02402c000500a0140005034205800410011003103030941030300342c6c01c606424859100700701d200340c2e416408505d80c80f805000f030f521100e11182c201d2000380ca400400900940c40904120181030702801920301260040000d4101140a40c0b44c1d0074100c20546040040c600b03c1f09803500500c08050018801900c0d9004031510190504003541d07505003070040d2142c5040444c1d4071590020481454580c2c080d800d42000d48100c9030000000d01c5846010b00054801c0320150081078042c1e48071550300851148a801085101201000380014522180e004034500e86105030090b1202c01c9584280420021001b0b18440c0e1a00340c0c0020b40005561400001c00074880c0e074000d24440c54840522801c01c03400340c070904100311 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 917648399 1250 917647149 917647153
    0x3060315090f03120b1f020f03040819140303191b1215030c091d0d0219030c020415030b0708040203030a030908040e040b16031a060f07060e1b1212030603030c 70
    0x18103403491046c4490903951030003006000d48130164800910000544080e602e200b0b015204400d0910409861f501c5070a0050b200c20504072020781c012103091004501030707100095240b4107442550507071016139549100b05510b20032035124001c8203580c404e051032425840300001280103910b80281c12450906500060304000501e0340001d45d140c015031040d2007050500700100603040d881d0b10791a03203c80000b41d415025800c00c03442802ca5002c18410300305034520a0609801200c2c2c04e4000c501101c8072420340c4000200344000620901a42c0c1c0e640540c02892894004481e140680c00f1940b6401040d070030a0905882c2d9000400704034840050310058000300d584094546400e0910b0000e0480c142c416690101c00c014030284c00e40c0c071901440320486405e1568203000e444030700078000c40ea880440945021441030001c0c500140d03482c000e20855003000f40042c83c2c00c1d4440000e0807840300c481c00c40a441180015030f4440074031004100012956002600642c881c2e9500300070900b1445240d0201d0228 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 917649649 1250 917648399 917648419
    0x2a0c03010e01151211210105010609140418060507050c10020306190b030403050f0f19020601171507020316200d03020316110a030303060315090f03120b 67
    0x400150310880f015000600358104240d554a694200c5492200c0080d0001e80309448007406810007401072082e001024121004860a04644600f154000c2e00030700c1c0020b256510030003045641005d6038801000c00c88081241c0907013030801c120007940e4020b00800c11038695000030304441c0900c5c00d0300d0341008040140c40042c500e241e40c00c4025030040b110310317100d0780c201c80304800c050243c6490341003603680d0b01c11030f0761454642d13489c103070750701e40107261100c1c1d19440401440300507240e10005000c00740c541689801e068068034102a0401c0c00503041440c036070068a03410107880d04000f4880d8003a507494114400140c6595008904600c03400741c0603695580005202801c0080c0c108119151440e605007901c10445810b0400600d80b07010715014005030700900010403000000c0950000040c0b080100c3c0004441040c045641c1081c10b51050b0007013542e558081045c082000c550036008680d852041000b2807107a500e030208501d036242d0240401019501c0d4620b4007200d03611840484500a10f21805 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 917650899 1250 917649649 917649671
    0xb03151c03050306030f010e1024031a0a020c03040909110d050d02150c040618171e0102040308040b07080d0516021009210504030812060a06052a0c0301 67
    0x642c0c810f5030114001e10078604e640700c51b10340600c98114201d000a0103800d0700c6480321030340000f40c660194145018118800641410703105041000021440f9080f001e1030300301042c11a0007481c80040140d000d4074010840040c00c1c1c0e50220131102550390802c40043e10801d1400c066014034011400c0e19001024104008107005001500240c40e9185608031030301072481c0c0134070082c03d140a840c800d000e00e90a02041c01001d000d011032441d49a00c407c0e060032280c1c0e440100c10b4042000f108900441e410032314482c0890074407980f40c81420a160340080d468145160360349000d0348110312034850002c002040606c00c0000000450724010305020007401a0b05110041c0e5100c450f43c4802000944602d4441160340f0806001d2418202d03000f100d00d941c6040c22803180403034100d04110360700801000f00301c040f00080c002e5004d05030000c07410036050254030b000e609100e0500b0090304400c09000060003918201c80841000010004c0020101561103410401440c500301e800c00d0071a606508019008403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 917652149 1250 917650899 917650907
    0xb1806040f171f09021201140601030606080f010905090f01020705010c080f060d020f0d06020408060411010815060f0d1e0b1903110f1f030f060b03151c03 68
    0x140c50b2108007003a440c000d02d1240c107564030340203100090b030726581c0140380403200650b0340b158003a180040d003122410415400f4450845001c803a03000d203001c1c5003000340f250f1543d06210f0607015081900b80703d03a9034188981c2c404403000d414443c40d011948c0701da0001c2c100b100144803a41c40300d0b88070ba0081d900c4880074a0024060600101001d0014010340001032503003088111240c090b0002402c2c0d01e030340f20019000d002e600207010b4000741e0030890816007000024013510042c001084040050019800c040ca09500031440d40c04020b41001401c1c028800c02c102800301003804600202d60165803031061044440d0b142c000c00c6003031201b242c40c001465180007810440c0304041c0c001c030241086800c0d89101000000d840f544011928500c0d03603603050001495010030340c117030f1000041031640d10078144000207001a1031030f890415500b150100180c5699013602920894080205062100604240c00188035000042c0180c00008003010741d801c2e1503c58442006d541d15018000001d0407040341001740c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 917653399 1250 917652149 917652179
    0x418020303210601050702061204050c0d0b0109050c1903200a2f03120c0f071401050903040e0c0904090b0106021e010c090e1803030a140702160b180604 67
    0x600024200b070000701590303c1601205c03a03a9600500e414140400d444071882c504800070012540f611505110b40804da030358010480c1e416108440c01c42071581804418815107801503c40e40040c1c1003407000a040500b020212682908180340000741200364505800c04e4284100600503145c0002a00fa10166800301034074904000c800000c840080485c040002030441c42d0078901c5580d0001d20003560380014095500742c00030750b0385d1003450030600d44002011441d07101d420120380071000c404e642d16803184203000700c65008030060059414986012001d030b031915801040b0911356000001c0310a9560b031580d001caa001c0b5003003100e0807180e4bc0c56140103551842199944181281400b2102c10702d201c050040c140c100c0c403030359510030119141c0301c1040c0000402500b15007501c0d420809035610303000c040001c0d51003014201d40100b030711007000005000c0f6a0707020300301104540210b180d10b00f6040441078101c044503100c4107031594a21103404049401a40e18890a40c80000024000750a402c001c0b100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 917654649 1250 917653399 917653447
    0xc15090303200d0e060415020705130501030803010e06210c030c0a0f0603181a0f010815010303081005040e0a14070f05210a06060f0602010b01020c0418020303 70
    0x14000b90150400c80c8038840c0d5048030002d9644200000e200e464070807410700c000d040d40030386040d04003515540c0d408440d0300c0d03d0300200016070200c5000c100c030303141c010304c428400c00018404202d654116103403030320701d803205004070304810f00f5040105186484100403001700003404610410030f8618501c02d251590030710440c5612078440c121501c00b42c0d1038000360000403a1550094020200c1c80c00d442a00504000c451184c00901c9800702c00010400c10000c001019554503034603100c82c86e00e02c140700a01c4a040e089191241d001015a401c1c101d612540d02d030540e0b030142044c100039030b140b45c001131103040d10390000c540041c20828001c0c0030190008018120510070702c107460f0300110050f4240ea9540035407242e01c1d080d071460a070401c06030515004c412601a80c1c0c80d070316856401d09545140c6420901c0038202c4290342c2d60030080260002000003030003c2c1c8100d01c020300c405030724140000d5803141c5103101076208647d42e07400c0185407164001c1d10241140d016054a0711640c2c600303031100500000c02c04d2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 917655899 1250 917654649 917654657
    0x10c0219090e0c180403090305060a0b09070c02030309150412032307030915030213080606031b0a03020f06160f0308100f062601090c02010f0501050f06070c15090303 73
    0x1c416600d0202082c3c00514100140038051000e02c0c1681c3c540400a0191094080c00a000004400f00d50180308551159859040119803910b5220910001210041203541044001904040103075030210803074412190880d4a43c00b0a1074100c11490240b007aa442020b80308401d940d48070405402072640340d02c401150200410140c02940360488a120300007008002510000081c841284280c0303407215040d00e04c1c6401810701e9401c000082144016400c814826401071041041c2803a0800130070a075100a094441c40c000b942201180c0d0112060000901c034912a03114005946c0b2154140c984541131200800404002800c2c00c403c0140d4070300c4103034000f030040c000050400c00814030b1082294a03030094880058a000000c6951110002040d04200a1100c50102401121138032034064036032441d00054401c0d024a02a0844113030031a41100213050000410440e80c482a42081036201916013a07964107162a01c0c5001e1030550304481481c5500b0105135a80c00c4d44803207241d0a5906c2074035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 917657149 1250 917655899 917655911
    0x801030813151107090504020907110c180906090f030a030902011809020a1e0c11040e1e3f04080303100504141b0c07050a0b07060c1e0c02010c021909 66
    0x1103000c06c0d56012a0081d40000760000481c4505101d9070200000c1840801560105805003000928014491008640e100b613481c1c20300070100c609002c482d41020b02400107228810744040056100d0240c0d508810501d80d60304a40300070f590003050302550b03052078a0710312204130b5164201300c0020340016188000007103080f20380b0a45030113601c0e00101ca80c640d40c1c84080781400c03183c2c1d4206000c110302000a400c19101c14a001d038104003040b03030300e03920b0322a48000500c1040420301d4502c1c0020080d1b00038848541c0165400c0501c3d134032840b50084413070740042c3e03039a07000e152000745815106a0b40102e0341480000100407041641120341c000340e81080318280488180c140f90707030114402c01d03200700382c1c000240b1109810008406006104450010080c1c485c02541d800c000b9800340c00c60b81c41400d4022001502004018003440790b9400000749007032501405100e07071100c55102d086a900502800b00e1014840196801140c0c5109100c1d402440282e988070065803a150625840c841c001e07103030341008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 917658399 1250 917657149 917657159
    0x603050709030c0308070c031505010512012c01060305100c0e04091a0603011b050c070927060f110a090b04060c24050c22060801030813151107 63
    0x59806001c4a41207140f01d01890f081d03403225030a030f60102c0b40c125012034003244000001240302100c2c6d10328035a9070200040b82d41c508414032080445012004915034505185115502d10360940c07115051407140107200c0c59510040c0050040c0b006401c082e149100e09001c0c8031996010350800c0c1903c283c1603640702c0c9281a90414003044d1611004010308860180500d240308185800c4541da100500038004140302d0001d0a00d00d500030000440b000c00143c0001740c10381900c10402c602070041000030001c01c244000119960701036505a40038002083c0c14510b80814000540c000880c2403283d00310802100700880c2820b4007035800350b4440d501003607003050001040d40a80041c2c82c07c94050351504c50f46140c8030b580d040b20262542045180c081518414800346030b22911851748990f607441d5003103640c0c0d01d548807400a90740b0710015941003c3e01030401804956404986030381100d0740000d11548407012002e061000c02070940001075103a80040c045d480d440d034000c509184040850051380d9482e502e413 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 917659649 1250 917658399 917658407
    0x10e210a080f0a1518050112020306060d030507050d0f03051005030c0105130801060608011a030108100203220303050a0608030414060f0f0409140a020a120b060c010603060606030507 80
    0xc0858000324035500c0000c0c401c044800c050560000000000052900c1d20b411404071100140d0840c801440c0b00340440d9180c0442403140c103015081b0215991000c15140e400607075103100042c40240101200c0011200b0107009000f9642055880030540c1c2e03a111000500a2140d6046840d44000a007050b012400c51079224007448240d540150181400c801c01038019900c99001c40c0c9032080c0901ea404001034280000c2c4030320000351110799188452035240015890140400421070031280c4010001003140c2c0f6400204040010240040503881baa15900c4a81c0c04264006100d480b603200703a018041015495800035100350782080042210755211001181da074021400b6038a04a04a0300020800340750120240c0894482440c074185030008603040e00e07400c0d400540c84220300e5900e4521056420080c1ca00540d80301000d85d5086041001c0c5500043c07201800c540b514440ca0b0b80c525000103641c071614129900c1c0301c0e1a000030300c00c0035900d00d00f0000814051290304d00003440c08010071011f9100d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 917660899 1250 917659649 917659657
    0x62212021008062b06061401170c0301061419020c040608120f34033e030f0c060414060609150109120308150f03030d0203040f05010e21 60
    0x2010f04004c03412103514a54009240c10003050040c000202c200580010745180a40e0b000750090300d11415042c0100d82c00505202c2c0001d11022440005504000e218200842503074116045c42ca4600e0520340d510b40030410b1403248252082c0fa01c04400c01d510009900055003541400040e01c080102d00e03a20a445902d8040c80210708400e00700400c00005a541d0210103002c500c02a5040c441d050002e4103c0c08050404004072079000e1007070220b0b0001410b03040140400400302000000748280c3ca182c094400703a580c80c00740c44842c49441002d111581354200190382d440c0007011244c41d92080c05401541d42d404007168212212020300d6010a1401c401082d030038042c4c04054000301702900c50080b42c482000b4040603a0303041004000000456814103601b01e030609010391580103881c10810803518101c00741c03800b02406516210309032030468900001302c91510300700c40f000580b03a40f228078190000c1520203201520750341c00d0010b0040d4184010130442d55000c61481e07680064040c0712022401401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 917662149 1250 917660899 917660911
    0x203100b0a0e0603040c050d0308041518020409050a02130204030b01080c030d052206050c0c300a14011509050c03181e01020a0f05040806010302062212021008 70
    0x146540c00e0410030f0030a4006150801c0c42220780141c505d84401c041141050001000d41c00201104207000c140044d1200014800c01e00c0d0500f44401e040855010104003840350000340165510707401401805818840e00004c1c0d0f40c01083c48820760207610b8082c001c0d400c98001034545e20b401100000da02e0030005586041b0b8500603016002e50f800c40d25003030b25542c1004d6040882460142901c80c44070a92140d10000341c400f42e25815210100105010700c0c090200050301e001c1c0c0b84200c0c80c12504105400d84504180c8006003440030801d44030001170a00c000c1000044c211122000f02034502503064102100660a1034048141d8569450302e03035040e9141680c40500031041080490440e070100c52980003020141d00840c3c0c0410309140107101114204141240140d60110711002140e5104624003550001407a03c64140750070948030700d88401301840020303c0703007000180d0442906881d1440e0b5615000506604100d907585048050840b142000101d200702c15121454a29070300443c0b1180c0511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 917663399 1250 917662149 917662157
    0x60f050a03080f1b01021c051e0a0b090117120703080f1302030307030f03050c07152c07030b0c030f070c140106140307080307030f0507030318060203100b0a 69
    0x41e1440d215901250300c5280400700414042009260f65070800303003030402c2c10b44140001030f62500d01040d0041100b150740f00c40314096043c0741c18005880240703030101d03551000d0307403105090a490b045550340041c03125200c400d030011440800040e0140e42c1c1c00c0b40b202e955403510240e640e120265084080301c3e200741c220050215140c40b0118602000b03035100264001c000312485000503449800291458000c2d030b904030000b5650342030000d1019814010740c3c1d040101b8002c0c003420901103503200109507452105182031295100500254220440c61b051a1942e00c14130965461450100480c0c94542c01d000545484110002107403981d440441101d20464000c182c0285648a00c10112401103080341e00340c0e014206079041e044080000e11894000b00f00080800c85440d01c88800d06050542d0303a4041c4900da0030500000b404a80c01581c40c40700d4044a14215a40342a28603059009040301103e0288006101000342c04200c00d45e801076005501c01095540001d40c0e560007101c061081c0000d4400007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 917664649 1250 917663399 917663419
    0x2d0512090f030403030c15050a02070614010503280c12170319050405010b0a0b0c1203090d081f0b03070e030c0a0b130302060a0503010e0c07050601120f14060109060f05 74
    0x301c0c6c4501400c0c0740b101d00c5011851300c0300054005400070744e00160744111105600007503800c02c1083d548640080e401007600031a14942c5040c0010f83c89208a1740b0302141c9542d180700340760484a101c4c0b40b08500e664003040c400d021079280c0a4061400c0c108040451303036440003402d540c0111039640162481a569100504210038000c0c0e0703140060600540100e403d503403203112942140e0741c0c4609407405805880e41131515110f500803030f5407400a840c41d9000885404000f80041c200011070f0301c1096141604042c1d1b010340301c1c00c00d081d5184120b50040040c14420314404501c043d42d03030001710f001d03400799507414480190240030140c441d1041301445034031110b040c0e410404c0004002c05402004000d0904102c20380d80ca80200d186507101001e070b0301c001100080184030303014020302040d070404800e1882c1810041a40c0e2138030350f05c6506000300c654001001d2480420810b84804034039800307510405c0c489030180202c1c04036590300300038014040707032a00b84503002c44d0b2000d541c6401802c45000400e18848 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 917665899 1250 917664649 917664653
    0x70308090c062a07090e070501050f030411060c010e0a20241c050610183c2d0b03070212030f0109060f060c032d0512090f030403 57
    0x10000080151020f51100c1c40300c41d201840303040c031003000141441000803405514450400b8289807058204038103000c010b21000b1410300d071107029698043c0d80100d101208401c40000a6150b01a800100c3c01e10343c01c4c82400c03404660f0118003045424030507044480d40c0c00c121410b00a0103640a6a404c0d049552510203e02031300307003200c0702035807020300c0e241d01460080c55803001080f03503004044800846466006100242c00c0541c140c2c44000c1c003a140083c0004809504058580c50328030038000604241821b0886444c0d03895803000110411800041d45040c241c0484c182c0c8103130300c2c400d03144a41c0101640701c00c10510130380003c00168003c42ca41c9070142c00d04c605100b07542c00140c402d400310b01c100d80641d007404036540001c0d4050100c8844840d8958502045001541d115400c0003d0418a2210801060f50011031030039106501d420910f010a0b80c904001445080003100440410307410703200e480d02c0310b4006004024058842c004000140c0e222881e0300e87d104000e46484e1607a0344100706c1080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 917667149 1250 917665899 917665927
    0x70309020f0d06061d04120305270a0c08010516260915011212050304060b0306070c020118031707030207180c18030203061b120705070308090c06 64
    0x1400920041604900780d140c40c010402401c50071208031001582c425007800301c2c048a6004005a60200d1040802440e00366111550040040c04d2801456101d0010404d25000f10460700c69500d800484150070b918001104e03580c540e80100d0507514002c0400300404c2e040c8041c09074600c2090a1f0700706c50100350318200210f40c0e0400031851101c442503c03017800e40300716407070b8202e1a0042c51148010803141800a40003d11000e041e8004118003000080120020b1000389038019600c0d01c904219849550340d00b440b201402c050f5440351b0349802454104000ea50b0081c0d000360b02c65000b030b42c1c0c10b806007000310032006595402d40000b600702141440f0403a10120510014070302d03140709206841c5903e54482204900d50b0514603201c0034140c8a502949109601c907110940040440c020407048a1950f00440c1d00c03214043d107206c200f0080001d2614115031114100c0b0b14080e500a0300d58124501110010801c0e0080802100055a450086481d8400006030a014040028401480c01c460011402 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 917668399 1250 917667149 917667161
    0x5010e150c0102070c05010f05040807060509030f0a061a010809060a180b040b1608070e04020c0106051c0209010f0311040504020a091407030606091217070203070b0408060c0a02060703 81
    0x380c0044081186990281007030024002d40c41c8680c0c00e6000d900d0030b01c000900345281d0040d804040040c00c0c0420002150005400700c126aa1820b105a4070810900880d042906807444159544a10114a010071099501c02c664450310080c3c00800c481a1000440303600000303544000301035124201286503440e0301d5201c0110030f600641004406682ea5070f5462140c03104a800343c498070201c0040003800502c4c00094002e03030b0301764500900b180c0342c8010003400d48150015642c3c041c0b58041154110700e5000d5029601910004141c03081600c0083c100c0c00018150142c100c0c0219583c4000054121081414100ba6a4030040b224a40003000c02400020500204181e9114006600000c0c6180061294442c0a000645444030f1850080c401600b5100d003070b801b5104020740c9040401040364001c111140407540648114107040c50100300b98280e00403a44040c2d0315015016001440540d8980140115030032841a15141e50794040c103014140a6940c0d00800b41e0884800103108038442d034001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 917669649 1250 917668399 917668429
    0x80108070f180f02161109010914270a05061503030406080403081513020d05060328050a06050903031504060302010e1c06020324041107030c11030118060f0605010e 72
    0x14145980c03040c48117902d03c140c1380180c034895000d510400d12800d20708207460140011400c103001d041114081703681e01c900d00411079500c1c583d10305c181328540000f4a0b104103c0703542c5038040300e44a544034181680c581200740c8041c0c041c0d0784014190b50250070003005407000c40706a6101c1240907590f9480907200b00900501c2d00c82072000c0c44c6941000da569840ca692440c0240304001604d9000840d03210048560140100d80300b0b1344408031000f4038881c0d02c885503c0c180134000c20050f2743c4500703140c1180b130800e030b0078401407025041c4010800d00d90000009984603036a07030010101d421440d4414481181d4a41c04080c0c0000d6407005190f42c0c60500f100a005030a528110040d1450700640301d40080b07810a0f2100b140029101d8036a14945079515410b03004c0110440c4c040100000c14040242284580e40e0020b050144810b072900520000f11910b925001c0301a0090021548042c0b8064601c003815004952003486c1011400016442c0d20920058500c10b0f10390041c0400c1290400444440d11520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 917670899 1250 917669649 917669651
    0x53d02030403080a0507060f11090d050c10020a0201021009150c0e090412090806060a0611070f080604030306080f060613020705120c070b0a120f1b080108070f180f 72
    0x2c00507076400300401c0d001e20316540329919000c00d8034016040c2c0e10403954101c070790307410300702c2048480e404141283e082c90720403a80c85149400510382035003017050041c5032541c0b090b001c110f503441003500401c8a8090030b1007682a01e4001120440640880e150548050b003400e642c2202e40720b502c10603503c05030022009080980790340c0c60540005000090440307040710340d802c00f0800403010703d4000c0c0005010b00083c00150005240500c04030b00c1c4000c45105a070100b11142d49203034a1030b081880b07210080c00a040603030011f140c88a5000390b65500a5408600107440e000000800540100d40400ca014128018089688a12041040c6071030081c1104520310303801c004820015800f084580d540c00c00b4a102c054958404d0004e85051040d25844200114010840440156802001d80c4400c810a2000081e403040191240c0001c00115002820044c0d10701c1020240c90b401804840c122810802202c5005450300c03400045413011f0701c01d01038070780e802c01e103003080c0842e071030300710301c00390140514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 917672149 1250 917670899 917670907
    0x31c081302012114070507021c03050903030f090112061508270a060b0a050a0b03190501060509040608070b1b10060f0e071706060313080f04053d0203 66
    0x448030300f0303006010742e00040d5030f5990303800022a1242911254000903d003070113800c0c116103401044140c009000c9281e8000402d403505800c0500940958241c80005000c8030707103510841000e140c166100c0001c1c1c43c0400c2c1414224146000e5078051a0305a070011030545c03500070f451030415500c1c02c6014000040c0c914050081c15168600d520201055240020007000c0400d1582818400c541601c5442c1d0b0088a4101c03040c0110703140c080004007125844e1104550380ea8454050b006014002400c80d41e25905100000031910340c804080c040502d1300326000c100c201d0f543da88460351000c0c0380c03003005160309051040307a8602c08548003500d50009508150740700390400c0422507044804075004174504407501d0b0784c14800e4414120406c1d501810a007002a900b48515480b002d602c0c1e4010100340c4980d070004002140503410751196203100d03912400040d11281d08900e00d187d6504a401442d0081c0c0c401980554564801c0c17250b841a025090002c03034400c1080000ca80c1c0402c9008542019480208 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 917673399 1250 917672149 917672177
    0x305180f070f080601080606010c0321020702040b03011a010f031b0215103c06050408241518090703200f0402250b0402031c08130201 59
    0x448224804020300e40a04651400d240c8040c6095080380c00038111640304100502c24032a000488982003002401e044602c1081c515040750b400c900300c26035801c1d4089166824850034040c0c1c014200481c0b00325800d001800209050501f22403181040d022003007200c8004070aa940950441440c4400a140125081070030145400c4004410340d80380005030b00180b00c9404c0480300e41d0b0060f800c003610745d00c0d40c8540351911000302c03080c0105180100213106054002c0c031140c9100011000240c0d4200303040c1210b1a615400a0709581040c46000caa6014a01d000040000d100b40160b4000a00c04003000e03080d101c50000320b400300c2c90400b219401034202040481181c030312407000b511510144004010345400c6203007600004c90428002c441d807401034000705100740da07181d401c00c00c0e1944c25100161503001e850110384152100d14070032506145900d1601d003d20280c0300742e0030312850090703044070121840002034854103e0300b00000b50014001c1004034a21204807601024028014503040f1078145201d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 917674649 1250 917673399 917673403
    0x10e0334080a03150807091b020627010f06080d020309012c28050406150c060b040f090611120109020a05040b16050c190303030e0f0d2c10030518 64
    0x5034000345170f80e920510007040712082c180917050154884441e6405402c0c0c2c0e07450b000c0d50318200a00003680303140141d02e00b04010510307080072a185a4001000b444045020f5015400411050088440d0f078040c0110250100d8000403c486040f40d069440c40c40c03165000b07081c6c0c40d040e084059030303081d02d003400d0003006040d659103050710241551201c6d4104401d8510328901038800420b502950245082c0002001400300c10f13411050320792904d06100da20700541d03290401c0140804040540d000d494581880c00a41169200c94003492141c0400c0102310484024001580181101c08605616010040c4080041c0b5005412030010314100182400d491310000d5610350444a40380c1d050303015441000090010802581ca0b00d00c405803010203907031180c0810791044140600000d000d242e12401a56250304003000f03019101c0c8100000e0314030b11044413000916510002d440a054a400115481c1012205030244000c42500503c1c0c021074210928054015000c0101a282c05040d54212001e8a841c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 917675899 1250 917674649 917674691
    0x131a0d020403031d040b01080106050918090309091b041a120c12070806030303220c030501020c1002030717060402090d0c08120f03180708010e0334080a03 68
    0x800d4440020821600310f580b07003800c000c0d2082e54030503821b2018110907070340c1008029054444a03e01243d0703490304200411455480d048440602d900020108100c0d81d1002c0054802d203141141c0210742500c030104c41c4034012004800c0070744084d800300000c000c0000f10032007011004c02a4009603080c0189459040000202103994020540c000520303130000040c000404c5610a01600301050542017107004640e07213000050820100d035542d0206e2850102d200d000700030105034070028400401c0d40300d29000d03020b504001d5036520f81d4829002800351200320b5000351f901c00c1486513101350b03024110341804005218090140f5400580c200000e8125407502d840c00380d1400d0003010051031451414541c2031610201c1d2150030203005090041c0e4664070802030484e60411610000070f6a0717540c40c43c9425050441a9201c03c009610b00303498000003030070100142c113040b100d400304884000c0d20340c0b00480b001103610a09002405070001100e000480b000007400c0c070300d050b0b442c00280c42c600c0064524a1045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 917677149 1250 917675899 917675903
    0x904060623330426160303122910110c091b0c0f0f0106121506120b160801060507061104150201050603160317070807020d030309030206010605131a0d020403 69
    0x400c40d84001a00c41403012401e14a03520b002c000c00d80e00c0c0030000c103c1c10545d018007000781004100d00060000368116042600362660300001c035518201203405401c0310890240035a80900c4410005944160103180a41126180b00c005070007100801000c1100e00b038801030050024007a112001c40e030350b8001d0000341505c0c40c84d20b0700130041004c840e03000c00d14143d081c50442e4901d85c1000e5003804070482050344003223031980c048100c00d00003c410720741a0142400341c1001e1600c10614140f4414000319008240c015001d40c144004070b800b60f00e60445542c0320900600001c28400c0001e0000640c03264004105d00c15500c0e069820f05884a0660803601da82ea030780000142c1d11101444402c0c51709010004804207200c01c01030325280345981e150205245c00c2c82031080004041400000d06ca50101254000c1d80e005164101d00780081c40d0240040c10100c10560042c07091400204145002da8121342c8114010b09100313510301d207020b0079600b43d43d409030060291040b041c0040000700c8031314005800654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 917678399 1250 917677149 917677169
    0xf241e21140f0f2a04020d051e0114100507032a110402040f050d03090e0c0703020606040e1009020f1509010f02070e04061a09040606233304 62
    0x40702d54200741d8586240f0340c030b1030040d40d0005261082c03541e4030b0100d5000440c0c1e4080d900b1a0002242c80002c0081c05030036007000035035040c88104144050041c0212070018a61040074a1690701c9500c0e00c0c0a0411180d4103540005003981c0d0342080ea400f60303000c5d007000c510902e04013a0490000009084044c0c01640c40a5040c0d4444060350800055010405e05a00c0503039045051a18000c0b000e00c13103050034840c03140581030342202102454403c0c603c101c06003480c0c0b80310882d035080c07030407111303220b0385c030006054006000b002c01044481c54a401a40d08002a0800070500c01110303040394030040854a10490344040c03441c1800d04c06450302c129181c0040715281103144c860803404005001e00340d20800c00c0c0f0454101c02c0742401b001e040100c0c07440c0c00035044040042c44003941c4604904182031003000f82c0e40001c0d50000c00082001e9504410300b80c504c05440f03590610069040110b0425406c1c58107640004c4140143e016060342c81d14003208241c1d810070841c50300410352000001c56220390050700c089 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 917679649 1250 917678399 917678413
    0x20a09030f11120f072403050c0c030a0f0f0f0804080d0f090506010f05120d05090d1b090609060b0415180905100e070503060f040f241e2114 62
    0x201c901800040001c0007100f0301803046075005440303801c8030b0818040003001d06540e0000310b82160a480d0507903080015203c116503551a203384080d0000103404070340d00000300c00140c4401c1c1c0c0d900c501008054410141c6982055803690340c0c4502054020710070059001c1d40da40401058014980500c03152503001d100504159410030400440c1d080d000d81056003d01d0b807111310001e10350000079209200c1c43c114034010361564000e00005003030401c03200300906081c052050018440c04003460311001c44803596020009540e4440c00002954414410305c045814180000c101c100c0e4030000c048c403c20072516104000b5001c0b0328030f070020110260880c134460b503034803c1088018a1702040c8140234264450b003561403841d025400400c144002841c9c1030080680030011100703505d03140c016107003a19000c0400e01803090400010340081d940d0075950060720040c0000020b14941d0303040c42040391034222102d030f41098204124a030130003030030405c064422000c40d00790401040444141240c0001268094110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 917680899 1250 917679649 917679673
    0x30e01031116120215040f05070b030c1903060b0a0c1b1806121101030b010c02041d0606041503030503130210170915070f210b030d0201020a09030f1112 67
    0x402c0d103400d41c103c080d58031404407001013611004000b42c0c00b41e80105801d00ca5440d0786001414901c055000301e14481001c03080c040c00102803006050420108a4850a480c00c011421810303201244070301080f440c000c0103c200361611444200740e00c54083c030300d0000b04000050102441103950307840b10540f4a0510b03590560401280104002400e010009100070984e54980708400c540d000b181e01d05050740d40440d1400c50340504492071105800800c20080c0d001e802030003503403040905c40c0c0c400e0a4001c0f48d000034014500380c42100b48100c1504c4410382002c4c11550161510361018002040e1244810075035401a511400c2444054030a0396030036024080707a4034000603007407015241076100c0d08030b0240114021155000182e00c041c0514012440c0091010107807000c0b0a4400004280940e4070f2444152104941200707511000a40484200304600d0000303d08030302421174102d0024507a600100049081c10130046c151300c0c09501b0610b991070a46001500404510b03000403247e4000c20803d4207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 917682149 1250 917680899 917680913
    0x40c0303021c090b0c10110306010201270b0709090207050c0a06030b0d11190815010506040303170c0903060906060a08030c0c0402070615030c0510050c0a030e01031116 74
    0x1101842610407040c001e030028060309407056805044c59920021038049580d050030031031030f0355a210040003003000c00030f00308103800545e100725011400f41d800c18105004541240b010500441418450700480361810343c0d5400e814240500154200080304102040100040c030051500d10b10840061156211050034000c003140302c3ea005505051824420300b8154488400103094140d0000a98480d5040b41c00000c80382401a81002e25201c0400340c042451a400a62040381142d00c11140311542c7c1d07104100503841c401ca000040020f0b0280014003560908400300603007225545040c0b5041c92030a0010030300d80002194180c913103a00010a000c1c003824809606030103030506101552800700c5900100b961013104506550180340e00141c80400c1c01015849003484036156811180040d9603814003603181d0015000d080d11641c2400e03c0485980e00a404441d008601b01010b4014002c0684090b10507850f00c041190515854682d2462680071080003044400c3c0a041003d030181e420f400c01301 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 917683399 1250 917682149 917682163
    0x62a17070b0a05091b04150b0d112a0304122001020705010c0f020f0a0b0301090f1404140106082e0b09040213090501060e090d090311150c06040c030302 67
    0x11810320303010500c1002c0401040ca031040d09070440c5c040c10328414400100b0000c05000d0b48210107158800f00120305500146c00402c03402c40c0024040c07001c42982c881c8140e0911801203011241c440c21501c0b40ca82d02c024640302c039410500f1030141da090603960382c01c110461091007800c4603031283c2c6078100d141c40c2c1d207485280f0804100a00c001e00c1214141000a00074800e0343c003000e001c920400c4440303001c56a402c8040390a44401800c1c6034825a55030072880640d810070300030303a0300f1b142c10034503044031000407403081c1c00c0c80c2001440e001005450341d40300c9070b580044042c4040a15500e82c1c1011031100420045a281d204d6420307942114801100c40040e51524007480080d2090704064138000c4690340c440c40707143c0003601150040302200030100810014040444e00601550900074001350450000c103240e4441c0c070540781601d440101e8000112040699400001c1c0610264000030883d400d04041c1c0704084250800b6042c41c02d0b00c0300200b6450301da011201141c1550200e4010b10803d40c0c184204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 917684649 1250 917683399 917683411
    0x815060919050927061b0c1207050c0307090504020a0b090d0c06080114090115082505130e06030604080d09020306341e1b060b030601050a062a17070b 66
    0x608854201002001e40341e006c0e100d100c08072500080f88003000e594090040c000510910928503640b0762061800c21b4484940c01e080c0361007405410340001d8132842d2070150702d01c52a4003c00301d8150703030704108040c4125003040720f04541044c58008400c000488807002c0c1c00180c00591202e03a042d600d0b1400da1036000d28002c0d000703030084070113000420880f007032144030340003e02c0e081c2040303040c50381c0d0038a5405508541ca010b0a8916200301c40480103143c000001b0541242c01c413644c0b0b134840d502d61000103c10f10041c1d0b40540c1560010001801040d0034201a0042c4400010041140916600040c0c0b800030146c520b80d88010a9407503c3d03841c4007a00100304644001608520141071030000040d260a075985010220340209482c11000e05d48541c1400485000c41c0481070610900c9041c0701009003902601c60380039200b9440041820f25100c9248800c50b00241e8400100c0810101d2610700c8501c000030381040303656004507003070016491000c1e00e603a203810448219181c0d6500d04010700410805481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 917685899 1250 917684649 917684653
    0xb0307060c1505071103030109020309160303020c041a030a081c09050a0f081c05040c06090f051e090c030403020c0f091609050405090d0815060919050927 68
    0x8090004001c0c000b01190700072421000550780d641d156095424000003d01445980000400401e888000764003560007621000c04890b81d0b5034a802214000c00e03000d000c0500941d2140c441074040746441c2e0080c4144031410060283c00180103c08686003640011044a20f6107000c01c4810106001c1c00e0913514a140c2c220091180014a459040c2c0325109400c0140c248a50701e071449041c0030b030007021561400405088902d0042d0240c2c0c41600400007682e044940540300440000c103984901d0f040000c1d14140c10340d0f50070300c03443c050410110f140000800984900c1260510101d561918001480b1300d88010a02d592860b144c90020b04014145088030720501c803841111030141c440d449169404106e69100c400b0280207010242d800d040e0a9108a62040c142000c000c041140803644980c017605544440a5a0b01d45042c2d42000740c6907049055003183d400e201c010082d14000d40d21b0b001140d681000881d000f034032a0701048a40d00100c8814400410001008419010b90383c40210048072400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 917687149 1250 917685899 917685917
    0x90f02040f0e07020a0506180607020106060f1b0c0b030117010c050306010f230405100e0609040c2a151a010525060606084b09010b030706 61
    0x700c400080c0014081c650039410000300080400e030007080500344442c0c01008403007040c03404512014150449082d000114040e990200e940315005008140640e00c0075100d00c0b00a60000a04540d0b4882500b09404582c3e4203d48602c00700c0d506454001c041e11000d01d400d0b66135810903102c0350b10641d050030b0142d216031406000d0244194000300340d0703410540901e880d408142e018001103400c2025800304268a00b06c031b40030917a40c0441c880003001101c1c4190740e03d031000060064299680b001080313086030002d004008082c124a82a80040c0100303060341860443c1860071100701481500e106201400034480005038000c0c01074050880e182d0441141d0140180001c192008051072100045603040c0300003c1406009120008121050444d8038040351105900301e041038005007400e440b0b0740b40800c9402e008154540501072110004090800510b00908c40050349120240118081b01c41e2009116228010501c018064580500803000011900c803168500301402c060280e405403060012000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 917688399 1250 917687149 917687159
    0x9030405040506061c021b031c0c1106011401030204080610031a1e04020f030d180e100e041509141506130509030d1506031103040f0803060406030203030a0306090f0204 74
    0x30445c81045200003001350300c90700c441485401e01a2500003084c680d000c045038503802d0410b40c00e507000c3c3c81000f8650030700c881c2540303210540c6e1440c06905280055000b01d001481000034040d85820800c1062500520300307681c03540740a040c010162900030b03904413201010400c1c015520070060a0008440e20480765040c80404c00e050313003a1160f0020007030740f8801c00160556071076071006408010083d0030756846c52668800140201d000c1e2006100d80c002c07060b400f0403d1041450000d100300050842c13012101d0070030356a40301c0d20b0802030048512445250100005400303600070020b080e0710070700424100300300c0e500240d401c1440b218941801d9400400c00c012082c0e0381c00c80d8006400c40441302c005000c0c1c60390141c281c254440c40da90080a50306020000c5d042181d20b00420081305c81c40ea80c1005040c013021040d208511007660080c01c1666143d502d030010401350b030011500298001c00020303242c2ea480d40800d00b542c110800440210ba6110420440c1c17000600070034403800350064003140740c94206 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 917689649 1250 917688399 917688427
    0x70f06050a1805040507180f0b0715150e0a1b02060604180b0f090d08010803070b090a021917010501030510180c120c05010302030906040b1506030903040504050606 72
    0x1041e0781c01c210802100c500b00e0a074801d075a001408001d001130045107031020005d055104454860a01c0702804072000601002c02e240190582d0402039480d403400945450b8481c1c0c001803280780c40485079541e01d417070b100014507800c410020070400300c500141c1d14007036100004980050107090b010b40340d0b441c80800410360201d000359000000b2200000d8580580e140c900281801e0070004201a00c480e043c800c0301c0d80c250001030720880740407040302e100c120f400a080f22500401c0c0f04040c0e1076802445000d0000c6c401403c141d5001c080201143c10305161078001070000b40c54007101c601c20007004c5106104008090f00341240140d190742c0207002a514658480d41d54483c071500846641d5506c3c26016941d2400b07591071082190400b403800ca005407180c0e21100d1034449071a00311103504200c240040c0343e5000c0d000386c0384a400034002524541c1c2c1c494a80c40d0100400400300c148501ca0b421a0b04241d41d00d540165020f101460f0040d52030780d041c0f00a1000b160b901900880c4511010b00c0703074401d040c1c0701c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 917690899 1250 917689649 917689657
    0x1050a0609052d090703080f030114190909110d0b0402040c030b030307290405010b0301050a0b130c030f090507080705031f0c0504052d01091202010e1c14070f0605 72
    0x710402d035644003113040c0c0c1040c0c280d420040c4020344c00500501c1c50241103002e1030507104900815180341c11420100061481001c040170840303980301104100040c055403081c0c17130042c020100003650f40c800e880060f08040304c000b800c80b5401038100c280410350415109403044040700d41030400281c1303800f1000079568092070030024070200110041e20202d031050140d8050460f886a4403807810b04080c90f201c0d01820f000890503009610b003070700241607103107070707000b000311003000904040c2c2c0c502095081c20000d03043c4091840203040e00c54504000c01e600034815a51030300c0c02200540a41ca0400e00d9240c181074841c0d00051203548285407100f082d070b410842103c0d141c4e100313440010745034102d0701050728580941d80c403190307100c1e0812503104401c1e411083c100d0150440d125508005c808894015030b00319405009000d66401150030b41030065001c1d400c04030341407400030002e800c106d00020a5001001082500b00c03040d010011039402c41040800170f01028040c8605075a8020342000301c0103040b806 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 917692149 1250 917690899 917690971
    0x106170c090f12011b021507020715050a021c111b090708180a140c1012020c01092a212a06050a110307020a030b1801050a060905 57
    0xb9044030401c20f40509500100d514580e450b07070312602c00081c81c0d002c0c0d140c101c9071402d001120075400024114a06c0400c021b81603a1500701c1901c0c4201d8120030444070b9811102070301040d4418282081000184401d80038075203105a41c454441d1518400e640d420103480c1132448201c00018202c0c0000b95907545d05e000d901140c01d20300310403d592440c440301100b0304442058286030189051840600585e42d040100d01d00e800d204131038134595400244641c8090000d4030500148107058480300401481d0000c1103100030300c00020554013400d448609000c401c00030419210010496032100540e10528884010945d040c0006000188140d203440b03401c00720340004282819100348000d881d07514161050400d82e0428210706116100c50008c0d0240d0300501540000c111000d4050396402c5001080b1840f0b65406008107004602c0d580d01c00e1003421003e854088220120303611144180c1c401d10400d4440c18400340046a40b0b4078100e00c900459030042c029003010800b110241c15041c89009141c84055 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 917693399 1250 917692149 917692159
    0x90513090f0c090b120a0b01030212070b0d020a1b0b010315060308032e0302060d0e0102040b07030512010f03050c010804032015090d0207140102150106170c090f 71
    0xa545281c01d00c918a00c0490042801112010200350f041066101e5020404c080d02e0022481416030b40319644d8401c0d1800007020035540c00010300c01070500080412810825000300d604142c0c41d10030800d400e0f000003440c90046940032503000022a808944003110700049020000946240d8444002d00742c4140006003058285822184505405902c000300568101405588034149055460b6005074042c0d0640303030040c10380401035071200089031200e08407035000f00500d140100c0000d00030054505485c01c1d40c04d5541c280000581d0000b90001008143d1181c0d4606680780030307404042000c2c09040e0000751030040340d542d00344002080081c5941c02010242003c01e8156030314038003203c1810b81e03210b0382c001581c5803c011500800d03001030100802c1e41e1000b074550899803400b000c1592840b2064803080184e001c2c100c2001315420205502c620f0382d00600c1544c50300900384040201010080c0d12140000300f0480051120443d05420607401c44004910585082091000100d82c3c20078149064820303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 917694649 1250 917693399 917693411
    0x10f05031b0f0907180b190815120a0506010e040305040b092107050102061e01051e040501150206241009080106080109031205040507060e131a040c090513 68
    0x42c1e42e9081c10408103010060520740d0700d01c0e120030000c2c0f038041c0c0380d510f110510300c0c01707400855144c1514058070342c181d21002e0302e440c0c00c0300e40b00ca00321034080c80076261038014035a82524407181e41701c0c00d600701d248070807400003804164200d1528500d0500e0580c4140310a04028040c000001e512034101ca044542036400c49894020000c0001d5907034408809003220f03188940c0c040c02d6804008241d0204403202602034030300ca5500d441c900118184d0502c810585400844014042071400c00030719a05048070f4402e1198000e241c20110b400c80e002a0043d203034542e00784401c00c0c1c02c113a040002d10760166540b50b10b8136400c0c3c0d01101c00e40044403819441885070501d0b00107240360314400c1010078010f115034802481041e0340d41e40041d0081c10519415000124001401c8403100c4d858025a130190394040000c20600d0700d8241c0c01c8134003142101c2190741c4003442e0746803183c600340c1d00d004000b16030a1495a031070084030b00d242003000315480d581c0040300b84280044100a01d607580c9400540c7e40840b000e0100714 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 917695899 1250 917694649 917694703
    0xc010504060c050f010608070609060305010b1b121602041a031b0d0807080405040c14040308090103021c0b09091f05040c0302030601060302030a05011a0a14041715010f0503 76
    0x5081302c0c401070030b1a1350b00c1c0c40e0b80011580000205181100c6141d2145c0000ea134446004034107440c000d004400d884c600401402941f520170392000c00d030101300340e030585c0e01446402207418516804440c000994400ca9040b40d03056160610408840d0308415604900c0a8259804030383c0f221194100c1e90780c100c04081d04540309407606c440a042603540481703035960310101894100c0454001c2c1c01031900552604640800240c001d86146101442540d501400c00b8559610840702c3d030b0100350420b0401d9001e1002890208514031a1815030380c40c800d010609108002c2400381c1d2a00c0104440d0460f13024144d080d5903100304030000b1800a07a0340401040036503443c14800d01d00303001544002e4052140c5800043c00c20360560295004110060041c000c0ea6a2a070010003940d0080c0110303400258100450102c160145e00f400395003261a41500d0f04055440e5403103211414a5a00c107403950300005000b01e500c500c1c158100d40901900040d42d0000743c2090302081d45d45a15112000c00304075041c0120007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 917697149 1250 917695899 917695903
    0xc031b0621060503150901060e060612040f02060c0607030f051302010c17030403080709150503190f0507020109020f03031e0a021c091d0c09040207060204080a050102030708090c010504060c05 84
    0x10103803e000c0c1c101c6050304410040d004029904441d1820340c1d528000001c0b80940a14520354001c58004188904001119410fa10b85040c05881200d0342d120300500c4800603245c8501410110b000741015100c10700d4489805030544840c510315406003407600b010444804090102005143d0b02880e0507100042c091030145e001d64031904034581004404070420080507409200075106020594402c4a0382c2d94440f40d162b035142030180b401011440500009200f803100280c09071403c2c00005020905a80b40b800403070485200342c42d0040141d440c0c1c80c880c425410301301d05500c14103005400540c50404000b065068180300519245140d2100180307407083c0c42c2c82080919440243c2c03289505003001c02c440042d0035101d49106042c4103541500c0c5124143d0030340f0507060300c1602c62010052a014008041000a603c03580c0b085031055403d11012900300002c2040c0b2417020306c0b6030001643c1e818030b2800545480c000030030790b100c01c1d400400385003810b036441425681110180d091003105560f5a1803c14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 917698399 1250 917697149 917697161
    0x50c19140f1f02070f06090605090409020a0f290307030c051c0506090a090308010603181e0b1006050a1b2a0906050f210304030c031b0621 61
    0x80e40c054401100c0080b02c8014007144078010030203408890032190788540c03405904440e48034060110f081c18108024640c002c0e001840e800c0d4004000260301c91035540054040074003038211900c4010180c4003402280141503a4814541a0181903130b801d0003604440701c45840010425010540c803407001c00c104034082e0003a9200c1360312001c4095500071391a03403c1c600401d8212001c1d4800e40d100f03c04140440a2480342ca01450381541d00e1400316030070107000794003500c5041c40315106011800011008205c1c0a0b0306980c1481801003070500c094040e0070051103107200546aa80ca5441e801c500f0400e8540080484503403080b24200a1040120b0369203580c0803114200d00a00005040c0c02503070080d80001798003050001d205640a07400d00e4881c1d0003102141c030030303026140d000304007442010a17526201c0c40350400705860492900500a40010060843d0002da108442310a80f00ca03090042100580c04030608419803e00720041c18904000100120b1050105500d22001040c080003c04020b030040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 917699649 1250 917698399 917698429
    0xd020402090f060c010b040f050f0a0c0210020f120105012a0807020d030e0316051e03160f030302010c030c080a020912030c0c011101111902010608070f03050c1914 72
    0x4030303844911208141c2d002c2c000c454101b5105a1a0001c0042e0000c02e610406011f040f410410301d400c0c0ea100c0c1350700c400500d40c0e03900c12800d5119840850007035920718001040d00c2241408100e4951500b5000c0c62407801060304150f06000113100306044c6852134011510204001252004000c00c03d03003040c4107648200c4e04080d401c621a21502018543c104040861440d0150101e6601194011520302e00f40f44c1d90052583c410310164000c2c2401c041e41200f040b4840c401801e61780082c4c94044a401c00c80707a40e602064605815250070018180c0a219080510004c0e04041c0040c4c040100010641c0d14014110311728180d01064883e819280e401815403d0784071501265036405d03222843c80d40e42d4038103200346400076035000c0d039081c040038040c09010683c01282d00c00c6420041640407030041c030090801c4002c1159601c60340018020f0040003400000d20000350541e02250075820554100904144c425015039a110030100e00800810090320446d03080c4514400b03000041400510003140301840 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 917700899 1250 917699649 917699659
    0x3150a0e0d030b0f040b0f1324050307060908070b0c030d0507020105220c33170c0a08010918050303040b01080d0c08030c03070c020628020c0d020402090f 68
    0x240c801d6010740c040f4040d0001182c2c5207001601200030041514a20300b00346401403280900c540c06403c0403010803085511812010071040f41c600031070318680300989901c4c096045054230801c42410b040c0a508050402c614150751a07074240100c060380c4030b40354440c1c3d46202400107940c810262042c0155600031850440501c4030f4141080024081c100595006607507403d0350103070943d9080f405105851603a4004082c1c4a0036103824000300b80840007010400050b140012940c400c02c1d0310031400d004070700d2039481b0400c490100103103901552b44014000303400944200817500c011904051054110b13141c1c01000304103460542d444840400c0b0300071004155110220501042140c5280124103950b40e000440705010b094406c1110400404400501614010801f1440c0c4680400c000c5601858500b001000c0d4050340c1d0100c0e030541e20a001c150307d811401c038440c410071803941c09031350a2081d8038801890304819240000e4100746216038024840c030740c00104e246160700e90000d050309030800141 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 917702149 1250 917700899 917700913
    0x10f110304061416060e0106090917030703060e070503040b060a21020316060504180c080a1104030804240f0f03360b0f07170a090210050a0e0f03150a0e 67
    0x2405e0000303030135400e80c03030745055003071200205183c1000d2040342d10864002002c8103504c00d603088109010381c8040c01480826450355004124840181d000394024101541c40c103a0364078141c24040c01d03c0700c01405032480f4641e031103400c01183c046c1102540311041b01000042d4600101c0c40001c0c86c1000d070240401c00c4401e294000a0b919422101030412140c01c48003807840141c1e0502100d0071031346469510380210311020701040d03109886500040060415000091070035450340c8070424150003c5d40a41c1c000c0d26140d40940079072400780d1305440d100541e41032103418590111405481017554800000400d651042240e6884000140d42011140c25001c1e4910f0782c8800d801076400000a61010f039152040c4602181036100324180c003910520786a9682c8900d9802d015803d02c40f610083c1400949544030100d02000d6510320f03002c03103001c1d0542d0310b50035901ca45da00700291409007000b100d2485016400c00d04002034601140f014990302100034207110355519540304c81c00170011034004c2e8805114200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 917703399 1250 917702149 917702153
    0xf0c020a0c050315190b03030409050a0b09040b010506090303071e1709210c03012d02030c0a051e070305070c052202180d060506010f110304061416 65
    0x1003041030344180515a030000740da46903010b0642c1c800d01c400440d62962400d900190319213017510344061006000c0719002c1920300c82c90001910f150000e400071781c400c5035250140818050188540d0054440540d289251454642c0700e61b070794800305218031405001d002030b2003511780c0d5043c03046500e220351100a0740210450030103c40e40c050791109003100c064140109a500101e900000d0b6150600e008208603035800310065004c2031950b0601c3e0004461140e1102141e007550280103860107038610b04201e400c85140d17141c0e5240d4641181007140b809a2041040c840c1d40c43c5072004598441d17415003881507640c06050b0a0340c003186105100103056002c04110301c0101580940181201805840310300101910350040200d04c000d61050342803201d1a034510102040e038144c01a05510381c1c0318405000c8041c446000c1850b912445400b103882c03030743d41e1301006019a044150860441c8d01072600d40e40914030401d250341d03248918041c50003030201401e00185071070b01c0b4004a40b611401002c442c01c162802d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 917704649 1250 917703399 917703403
    0x117190e0c010311041203050d0f05070c12090614030606070203070611151303030504150f061706060604030803220303021801080c0d0f0e0d0c15021801030f0f0c02 72
    0x4001c540e001034188186803019026020030369040d034404400e44505542141c1e4240c03031542c00042001c1d02107407500360411118180784502480345250391543c400501e0640380420801008150750018461003000c2480516170020000c034101480310301740c9a6079110713600052128060240002c0d814490302001042c16540045004c0851943d24119076182800306011610424120b078180c20403000c140d801c2c130200e4401d402c0580c01c9402280c884d01c02c51028120002030301c00460b454081c207503c50a00f003100c07450005280454079001400f50805081000002e401803082e44800b908200011000c15041450011407211080711400c484580341c0c42d51801030040d41002c480c081d9102e0320403035152080c0d4042c6021a00c2052401c80b4039160401031000d0350000c0500764907041030650385401094140740104840810998075445400500703d06140c120b886900f80c2c1c11300e2096500501650340030201400d41c2e02c102010074240411400d18010140c4003c200d1b82c4018490b141c24000c00900c01500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 917705899 1250 917704649 917704663
    0x90f06030b04241a0f24130e01050d0f05070e040c08010b1035010308120108070501050405090702032a07061106070c03120c0807030507020c0117190e 66
    0x101e40041c035100d0207244101e003c5807213150041c003601c400102040071920740400b0030742d01804020201040b040300c40c01e500c01c0b8109003c280400944000400c0500311140502c094000e1103070011280056040a000c01c0700a02c82950040002e03000f428020100001880000301419880301000c0b42d40c506414030f50b81c0c504003841041540e501c0c1c4070b4044900d06040100d00410165030312410170700034a112040740b01c691080042c7c074041c40c7d1800066007506040700081e009500403424140ca030240a101d80d080210103070722140c0c440d40141d0f400c0160380d030070030103807000c9480c221900308042d0388842c0203031304510034201b400c40440749140f19202d07601d80100d03040701520b140d0803c40303038102d07101c0c0300c02d5401f481c5564034900b003548284001003049104003120603c0c640b091900132002c66a034203c5a060311566900c00002c52100d90409c41c10580c180704591344007103070341700801c501c80340100043c0208034100681c01084240100050500845403a009000d10300ba0a080203000410b80ca0540c403445 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 917707149 1250 917705899 917705933
    0x50103060501110d050f270108160c2013060f1d01090e0c10020703030e060306011e03110c01020c120306031b030a2307090c0504090f06030b04 63
    0x200c0d0003004609544243ca260710454000001402e044005902c1a00e1540020000c8001e0860401c0318111501032558061101d183c00d00b00c0b1074001403400d0001d030013850010081041444003400c070301440c0b5440740c03920261390b4100303980d0204402550700e491000c8c0c10090600790020701e40720300600d504034541c1c40881111607206080e0b180b0354990302e550044800c0c14070050411100100103000c0b02d07569906c62804d0303480c01d50850b00d555001c03601003085c040780d1032034190158004150400505800420039104585c1c1100d030300f4558034040c0c00113480381c4500040401400800c0f00c0c0140154003c0e4030002c0701c2c90b03441c0d91702034945001007604c0340070f0343c400d0264422501840903940d00c51052102628000c410080251082000164200307001c1c0c00c92201c000d9151145500c0d0101041032681e10550f50300744203a0741e04062810b40382541c03800b002640310740816441e0030f9a00031810382c07001c19142521001c20b00410110206000030018060542020704030301d15040030302c801c001c407130051340c0007000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 917708399 1250 917707149 917707151
    0x302131116050307240e01110901110307060501060c12030903270b0c030c0f121207230c2103060d23030c28020108040303091406150a03170304260301050103 69
    0xe0410706c11802d80f0750b51200b0000044003400b8084041d070240e047c040c2c41b000d03c01c0840b41041d0251f111101031324070a07405a804190003031450810320950b403035600c0c03c031036107828140140310303041d07070002d01d610100c0e000031244240743c2c543c21045045040d9050001d00800c9600d64540550b9a850b42d2658001c1c0003910680c0304078166005440d0700841c081c0110341e8250840350500c030350681c2d04845140d00810038001c0043c600c940f18111180c102d80b003d055000e50084035150700804034a2882c03c0e070301e4158086020051004200490428002c50354800420f944a042c00300140c54030b001401c1015000020240c184100300f9000e0302c00001070004000e1480c21900f100304006501405000488950340d52014820340d40030255001d00d0b010b42d00244a440d0020b81c031292621520048850384514007540d81080091000c51081640c1006021104858000351240303507a690a41942c4242511001d85401100113070a21008a00a00d02c00031031610708600c145440040e800a54801d001d414042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 917709649 1250 917708399 917708411
    0xf1101020c03010e030d0908040b030109150509040b01210213140606040303090303030c200c030c180f060303090307090c090e010303080612010f090c030213111605030724 75
    0x1502c0d050007010602c01c0f803a8061880d2246e40d05039500644a4140250344142c8108400940729908600450081503050300004082503000e172103100c21181d40d80a00d00c180c0c0540700340000315110106060464281032000001c0c811031031208000e410343d40070b0180d80241103e118907071005068000401d140740d110301c1302940d603072000100b00d42030050b8040031b00020300000003800000d0003a07010800c10704103410320711103001303080120341135005901c04c1ca40e11540100005000600b17041028003d051411102850300110079444c00001070300003025040c6042480c2c000c1640c9072000e204403044404040d081d68805034640034a8406011122003038800100394100006000403004400d40c10b8a501d03948403100c43c3c41d5402001420040005880d40c1956900b040b03940e921401e10603120300354400c04035100214a5401007040740c0301000380d600082d44c240800f0040709a210340c00c42c0c1c0c1d0140c42c054051545802030404c60300e903000f0090024040440c50b02e030b005048030000001040014120320500c45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 917710899 1250 917709649 917709673
    0x91d01050c03040510090c03080c0d09080606030d391205030402100806010e0603150406090606020606100309080f0304060c0c02030c0d030201090b0703020a12050f060904020402070f110102 83
    0x500c01103a018105170003500c1c40104504050b000114264080d00720041001c1d101d45600a0356030100d00140215405880c3c0c0d90303801e5412942103c020007200c40541150300e0300f0400b082e10f405460391280304107c003842c41603c1d0748050060700a280c500e0500385001030030700d10b03030042e8240e072800740d080d02c00c082200e241c584514881c0d022244125400340c0400025140d907201594900300142c00d0b0341c1802403248194a542e26901e019501c10804108410341c41c0c0c1000040c4000c898280c0c00c80b030381850400d40244445600000d4141e040709042d00c0411410200f14401c4000740000b41004108034800a510702d40d001c140c0c80618000c0d80201d00030019400744180070781d22400318120080d0180c00030009000c09140868002e64024041d00011038900841e585000c030465048403240c01103a404950513024951000c40c0d0204984034102c1004a4206010240400d00d00100b5aa104a41202c0010119207d9406540751942e20460511801b820380c0707030808584a024469500500c262a1a141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 917712149 1250 917710899 917710921
    0x50111011b090305101811010e040504060203150a0305060f06030a060603031d120607030b030f01021315110715031b0e1c0f080c030417030a03050f01150c0c091d0105 73
    0x18603003e22120014010030682d47e11094002264461030602050505c1d0b188070307403924054180300d0391151800503900c0c508000c0c16024684900d203018010a48040180b000600c005640f5400580241002c0c000369a01c100181c6000410314005000500b0030301c0c000105030b040105074444c0c03507e1100c009810310307110f400c0c840301121240700700d10030754001004148218020703404880c1002c4090241c51000190980755402c0e41c0c060301d09095060310381e6000b001201c0c0d82c4020008844035502c0c1c444c03220300c0310b241c140d5071394102405074812501152000304203207802076020403510354400906442208404002800c41000c941e55a4000d11036040302c2c0110928810760200403e602ca607031141c00c080d0310740f69039405400c000207482407480100000300e070f40c2000140c8140e421070f0ba0030095507513907100304c0c004080d0b44028298019030304034000140811842e844c3c1500b510910761030b0140c92080c003401c2c04410325016600c00c84040f40303081d1b420644000c1c6e126800356022800e400038000c0303840383c000c00130f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 917713399 1250 917712149 917712161
    0xd02042105100504080f04181a010c031d0a060f030c0302130608100317030a0e010b011b170f04050f0316061b0206120a05100609050111011b09030510 66
    0x1c2207500701e038400a0200b1a00c2d481543c00c14058110b01d0304080f001000d046250380580c00510080b0642c062403800b402e484e005004011451004280565100c0d00021f0320401c06203900070309208400f0b404643d8004417140407410020024400341c11160381d42409042c0c40010300c40680040d0405c01d188050500030300884844c0000209210411403a042c41101c0650f8080c00e4144400d138086400400701d0072603240b0b6202010740010b01944c90070040c2e4804210758030034107160120b904159115003a0780e0030606200528000c20111000c54540f0f1812007540c200312803040f9400c050114020300305110510207042610425100c1403003001d29070007010f50312a11240b01e4403001c0414442440a54801e61a40010151840104030085001e41c0000c180350050095035807c4000780f020400d050341e4502030140c1003120f0290701c0c90500d06118005010241034021141804800c0b801461030344006d60000100d030340c04100b030700e0502c0d42400d0700520310540c038070003a60b480c4110650b00d440c0c03031118030500d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 917714649 1250 917713399 917713403
    0x60b031b06030c0c011805012c03120606070b25050c12070f0803090a0215282604030908062404020d02031e07030b1305060a0b0d020421 60
    0xc24116501d50381440404d41c0000d004104070354030b810101c00700d0240490702d0b5403207034411000401c050f041c24808400f070036850017181500d00e0521500d0200c0c42d0010044070001d031b40e07001141c0c889546400100e1150b02ca00764008211b401c4100400081740c091141d054501c5034194281417000180400440d818040e224040410740c1100c00e004841500101c02411124850700181001c0c00141d190b0032040d40084429403055008400c0090031454681075041500309902c08217030a00da200c2c120320341d03180101081e03000451008146c80341400c2c011030f41d1692400f50703944001102c101380300000d88180e00070790341100401e00c100004200c880c0d020503041d10504502108180400a2400d41c0b4103044000c943c3c1078109074204040040f0100b60300055210744001840728400304000f0004000460008182c00101460040404840d50320301042406100744040040380da0744070303140003401c0811907501000072140001940120003c1d00c0d00640211605803000e60040c240f0005600da00440c40100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 917715899 1250 917714649 917714659
    0xc011401081203010e22030306180204080309040c11010e030711040204060c0803040c26210d0b0406150f120c0c0f03030e101e02091822060b031b 64
    0x5000c1c0720f141d0950140e1181c1140112090a02d1b4840d5030144103125560540c0003c1c0c8034241840208030701c0588060b501460581145814545600e458aa000b00703c03003039100c1d5841d440190300d5544159103185514198500800a0010180711340355641e001e200200d40101040c1c0340c2103a5840c0501c00d48007215103035200c113040319000741d940090030380c402803040300d10b034000020102c2d10b5841f01c5143d243d801e9422501602265402c10010302d8034000026135140041c9624030301003009440415100d000c1c07603440c1701180443c80c0d000098050441c5400031420440103c0071902d400c0e80c80000304400f944517032218a1402c1d0500b8088003a21041d00f03800c8003080180d8200000600c00c031070310549560080c0b400141003080004c45e107003000b00c00c001000c1080d4941c07100501401503409540159543c10004502e03000301c0c40003140142d50500054041005200001101521301c3c101c0948a0034804801810210316440e0500040c969101014000c2c0710303030800c001e6803540c0140500e101a00c0205 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 917717149 1250 917715899 917715901
    0x7061409060f07170f011e0f0b070201111006030b1b16020117040507061403130f080f030406090b06060c1e070506040905070206061c120507080c011401081203 70
    0x12601482c0c00141440d0304101c1020100c0720050800102d15014400d24136602106500d40820803d1220103003081d0300c50211391130300800c80e044250780d21400702e80c80710042c41c0d11107504d4001640c400117401510303000b078000c0c0e8001c04115a400d81c001c806481c800c04400d02141c5a0f5640c82d6010401d00c040c00d540104100064910044504040b02c0e01030b20503d04440d00c00c800c61000c0d80340b43c405440071102d95215080a000040c2c0248000311008040c459807800c40c40d01103088440000441c4024105040141102042c80000802c5511030031040d08a141c0d282000d141a030020000c00c04180c803c2010a0041412884d10404030740040c03ca1500500030180b9848200290213856a80151a44100000050682c440e40082c00041c4505070b400603803407400840282c140380004100c5d51041c464444800751aa19641c08100c009070070a0741c42c1400d22400c0300a4925100c0c80d94040d08440f0b0115203445d14010540180290441131541e0f10300e0380e6602d069441d501c5c251040402e02c0440288 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 917718399 1250 917717149 917717161
    0xe15181905070b091513080d0f0917120309060702070504060305030306090a02090d06020912071a0a0314010b07021905010c0b06030102070605130b07090b0403060e010902060c01020706140906 84
    0x440542400c130002032002c804c070301a80d4840c41c180d0744100841080d245503108200004582800740407003080b2070b4140200007410b44c0000a0004c11180500c06a2000807502d80300054801c1100099480fa500c0d07629580b41410030b00f50760b441e02e0407a90b03c0f0040c8507419010546040500400003182e0307101c0e0003142141c82d0001048060040100080c030ae1640c02c2c45a5041540c89000c9150094010000180d07140034841c02d0081002c03003800d00020550042c00c08200032045250041c002030000704911b51584404202200644900c9007100d065040010021615035040001080414401c95140100100010507003e405000b48030751030104448250220114000030b42140c3d018000a000524001081d0749020443d0001c1e984805c010050034508400c20607240401600940303d802e0a5a0b928580203003402584a075001c010400340c0c603203185206881094009074405036000740f03620b03100c00c040c001c207a00035001000f0903101d850620b0003100c513000184d410716029002f101c024200d5507071030b5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 917719649 1250 917718399 917718419
    0x109150804020d060c0c150204030201050a110304080d0504050102010e28050a02030709050f0c16140a170307020c150d0e240711010507020706030e1518190507 70
    0x1007060760400c02900b10200010418443c1503032200d100e403255007004210f810321000072041c2c4030f10b0b100c0d19881080705002513a00501034641c001664600ba0800c5420840000c0c00c600813507224049070b00c02c500550040d80c3c0c020b0068810380707000381d00130003e00d410880829070300c94141c0f450b45001001d00d00000c1d030201e00c101d000300a0328044c10849250710016401310380352564036070002800a40e03500a0040e0b1100740c00c9626000200300f80d1680c1040002211600390810803203004088016100050b00704502c14008204090b130803c40003003100721040b24080a0707500440344407005000e03030401a0800e01e005064115600d4203e10180d0618600c88040401450144100003051089111940c0f400480c00e12007840f60000b81c103400ea103400e280c80007601044000560450b16410a0101700b8095400104441202c11a24010036034201e4440c109007000074004084400d64004800c00441c0b4410356500360101110808484242501c0c2c2452500e260035040024026040724508015600300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 917720899 1250 917719649 917719651
    0xc0f0906141e010e04110409020c0c01021b0103092d0501060504060b160515040812060f0639070329010b09010207150807090608010b070204051f0608040c0501091508 73
    0x780001644c1c2000706c0800644d60003550011090a80010b031040004005000101c0f070440c00b070000b400015900c3d802d4405d403002015115041550b40c06442040c440040d90000d00300155201912480b8a00d56032080c3d400c10440e4242c1d529806c6c5107001881e400e05224501c200d661007080b0314100402000c00c0b60b41c0c410000f200752075a01c2138000a0b80b002044070b0b15980520b20454105955003564025400589d40091840d8801c40c07020b8065071064440c001207849201c0704c5582c1120252368403045911a1010702103020203240c044102c0c0078039110015003002503034052010820480c0e000800d0805034402216014032240e80d00004010304040400601603000050064500c11611000f26a42c40c0c0849105000003c0b0f4038414030114a0304410b01c00d014001c2490406010342c14610154074900c2040c00080c0500e540c0c0c030000e840c1c04801001724141c104920809030300607540784e40040404d403084d581610411603480000883d076000c0c5031200304503242ca11a80c92081c599190954000d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 917722149 1250 917720899 917720927
    0x3040b07020d050f030409050a062610110c07080307030e13140408031f08071a041e05121605120a050a0c0f060302090f09040c0f0906141e01 62
    0x30700c4a002c540094000d002c02032020310640015911503150007440000d80f400909008009480d2000c20f2203c0e03c0c11918480360f001011080c18035543c882d030000b0707180a44504000f04110324040c030307a5280d40c2c141e500401c84c1060000894010640b200c0b00b01d41c0380d10a8071070080204201c03210b50340316802c001c0c001d1030804500500020b0841061540303840c0c0315038225021580044000100041e8640944940c004541d0100900c100f031030410341e0880d079800c0c07180a203210b04102c004e10064039019a00449018000b980c41c1d841e83d041c1c0301101010125032078050300384159484101ca4001000c000782c0b038100340c0807003030b18141118540014080b0040c03040005041600518000c03d02141c01080101811449103940035400c03803518080d244e0469554003c0700c2014010800910700b03030b64003400000c860408460703120094840d0f00d0040c0c545015584180844000840c00040d160b04a0b48044100d8a00070b480c1481c103052441040385510b20040942c44150180e00a2003695116600c000c813448 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 917723399 1250 917722149 917722159
    0x30d05091c0212010e06073002030a11040312020f150a05040f02060a0f0201060b0a050f1b0703080706110c03030a0f0b040905010506120d0503070f031b0201140f060303040b0702 78
    0x6180f05031103405e403a0b0760b0781046196071041c2d09026a195016010700f01036004207a0a901d84403140c507c001d072126000385c070900d4668010001c40d44207105035005142000b00d5801c016075a503070300d00c1c240c50300c1e200c840b40c058054040e114542903031070000314880c82d03510501c1711050b4041e1f4500a40134000c0c50040c1096410041c015100340058032050000d09048015840d000c15041307441c2002420364a468002d8a010308081c0000c10300d03260000d040d80c86850f00400342d00c3d1a181d0307103140f510001c56006d48006140c4100384000060180f148020959280541820711084482d039180c0441c621a951225002d603200308001002c5000c0c980c071081d9094035098000c90130a0640c0009400e941f1940000d03075243c2d56600c11312800f880d00d82d48188030010040040c101e26504481c3c094402e0100070714000c103000d03141001c583d98030f100342d01c040048031560002d1035403004c10600085c02803450059003e040180700d004500c0b0556100446481102d000300158586030601d443d803030301340e000308000700d03002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 917724649 1250 917723399 917723419
    0x114091b040527070302191d0a0612060501050306010c02040c120510060201051311120a020301110a0815031009030507020a08060402011e09120f0501050c09030d05091c02 75
    0xaa849400114015881507030308000f00c254800320000f00341c400340c050018140304104d40380c500e00300c1c44900c0701c3e201030343d00308001c3d2110050f80b0702d8a6204411403055001c4c0400101052854000c100316203091590f110030480d0648a070b0054074280b0082e100d05003c90807000b0841d0045c500ba41101c01e81221514201680291841555040e10380549010105802035079040c00400d1707092040c582d100040c8214844090129101e42110954240c000c80c0a210500381d070350540e40003004550708140c1e010b8000c001c49100b017550a5a03d0304244080400074450301c02240b0b2081c0020f40464000f00000c01601144401d0300b0020007c00c080e07801102844810b000794809607690745402d00c018800d5a000d400c0798a42480014400c451b0582c070420300d000c10840e01405594050344030b805503050007188800207061828501036502c5600c3c0002d0056090a041281c00d0f034100000d0041c501044d021181d0f80c25240e60b056036280102006690041d000200c6520040403400c80342d0072650003d01200e41c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 917725899 1250 917724649 917724659
    0x10e27060604020c16060f0e2215410114030907170f07060c08070f020f0904030c02010e0604031e0c0512031e040b090909072c0114091b04 61
    0x5004103c2e40481b010800101050340c0064001d0303100004014102d654460702c101d1901c45444514140480c030000c140d4501070300243c80464503403140a8514141c121507103600c0102c0700b40c0080403032a0f405100024024070b100f41d5109081d1010622031050311081d00b00c9403000030000742a040103020105a01c140e400000301c031100b54280e00d10300c0303800e54041c010381204109141e2500c90190311042c10400c544140f07602040a86069400150344a0003c8040c4c001e9800041c81004240440d0f035400b400f00b000303005c10143c00c40c1040501a200ba00d0b11403a10151004100703441c010381c440905604100740000101d1901c0d0341520380300c1403081c440042480c0d00d5501042c41c1c1070424220107403da1001905240d445c0d050b050420441011a42ca1860141080342c80e4299010302c4071850701600342040840e00c1120188030523409080303c03480c1810440d45490861800301040781c04040440c0c14200040f900350341c90480e8065440700030717041c0455a117070f007107040c042c0c42c01035082d404441c0004d101c0414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 917727149 1250 917725899 917725933
    0x110d0f12090b07140c010c030f0c060221090d0503060a030f15020c030d06122f0616141504022205010f180516030b060403020603010e27060604020c 65
    0xc414003904d0030b01203158406401c01e14107100607400c141440140c0d181c1d18002a8460391420040085180211051a09151501c003034040e88022000000001401c080700900040c0d13a0f0f41b250320301ca03044030502e20150401356814070060359041c2d0030807040113040c00440d12020301603880701d1140641198211000946004a070440000e43c811b82d04005100d9100f400d0074000c1c940600300c1c00c0c00342a034401c51982e0340d190556000906011545100307102001c08000d01c96100ca070201c0150885642380701c0d8104291705200302c2c80044a501608894205407144002040e03040b4540304649440151115000c00c03490316a00030780003003c40c0d42d00c60307030821442c45409100d00174034200b141041580d00317003009a2a141c01814802d103d0300c0ca804204610302d409075181c201e05c440130307060000317440390400c020620620035070304040d421003030010001a04040d9a04014440c0403280303029204100542c03500041d0038800c0072192401e6002801081007031034540e00030710060605404035454203000341c0a500d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 917728399 1250 917727149 917727157
    0x150603081b0c18061f0f14070213061d1323010c0f0e010c0b0a0f331703041509080a03020f010c03020a0219030201140f04110d0f12090b 60
    0xa40901d0380d040c00a2401c0c0b0030001d0070310b030a00001c900030b445201100140000501ca09220400c8008502201e01f4000e2104403540d41d600070b041949041c4100070340c038002d020b00e07204074458403483e28440814074554280a90103501d045014078981d60310764580b00e02100800d4960803480d2881000459080e009104083c0d052440c1e441d0106070b07045d01030024080c41e01110165050140c0c00b005840040d080c2c00b01c0a6009a002d280020081c90322140d10005085000000300000c0a1125919070000d001e491555041e07840c1c1c00c07450f00940c48400d1140341218800041903660702c1400140413903c0200c1c09001c00102c03330710308492070903550002d207880c15030b0b40c56099000da00b2030350200b40048020300601050000d0b40c1002d41c901020320400030360758028801c0c4201182c2020a00c1e4042510039004800c1c0803101c900c4060040c1804107121480e91825201140d025140741140041e500b8202d48002c000c2e50490b80d1901151490b07200e0082d2208450030b55810040c00500114803000800050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 917729649 1250 917728399 917728429
    0xe09010603030212121f09020d020405090a0b06030721050703051f05010c02150415200a0b22020406080a030215060616210309150603081b0c 62
    0x400c0c0c6518600307003c0d060005000081c40700b100e082004204081c10f100f261034001c0d46c1400c405039100c0d070482c4400042e40d220703000300c3c0c840c50002804117900d000c10f40160007a14001c5a4407291511214048000c031002940d4842d003100e01400007a0320540116110030200741d0000c0b54650307030502d0550100031100d04540b02404656244103020408500c42050030b0b83d4512200d20140303160414001800c543d68074000244690620401c0380380316090300703059400410520311500d400342513144000c1c01c04c0c841c21000120039880b011f000e05000c0000100101006d070040701e501c1c030507210054110b4174012000c150120181d01e0000c50401130b1a80e03c074200090801c00c0c007605842c0b42034540203090108480c50790443d1040382c014000180d41d00c20480c1da42c0c810380004a044011203203005049099103110142d04500085c881d07120058041d003040c140a8031418a946180060184640844480340005403c40100703000c4201188003a0300c07406c2e10300d8054003c4a0344400d00c3d400040c0314200500711 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 917730899 1250 917729649 917729651
    0x80a020708040306051501111902030c03010603030c140313091a0a030503032d06040b130c080a05010b430606030209130b060613080d0804111509090a060e0901 70
    0x400c026501b10307020b80e065952091030320786440c2408c584020780d141c00e100c4e07203010301d506e0004c584800c654040100d5a00d00340003800030b02c0016030307a090140501506003000ea070300300001250398035405008822a445600030180d900c0c101810026114000c1403001040e81e541518801c0c103000c0d90743d4402034440114410760003160750340f819012200355950310005070b4004d00100408800c81c0c11a080301d0961100040c0c6000902c0c2c11484000b8000140c02180b1000c80ca1404842d041d260354401800c0340b244194410a1010340d0341d03034000054034840c0b000104040e0615030f02c4070300d0410010681e02d800064000341b282400c3e100b49404000c0300c001c2807046811595480c3e041045040210b43c1d80d80c007000c0591140034910245e2500c01241038014410382c4601000a0125000e100c50341c901806042603008450a001d03078002c01416420007690240e80e1051004e1440407641340c84e040c1039140242004a49042c50703150030034044075540140880b010f0f940c80c0e06010070240164203405100d0441900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 917732149 1250 917730899 917730901
    0x1a1f090b06120f0702010b01022e06031e030206061e4b01020607020d0318060c0809100c2f06090d14180910090c02031e030f07080a02070804030605 65
    0x1302c083c0c02c5400180610b41075421000980c01f84240422240c0703c1002004a00c8e608a901500340b540101065000148111690446030103098200b0501810091280c0c084502c5501e41204100c100ca442c0000c1500310002108081c0050920031301560a10003480c0039090b5120001030010440c0c44501081d200c1c0e02610481d12103006c104400e015480e100a0000c1c0040342400c0900949802410961400b41034441d04c07070000300a85005200c0d01d041e0410b00c2081000b049100040c04404252440285845030110003094424284681c501100f090b413103902c3c01c0c0342c0320381d862180380007503802d0391140c038a21840424200f0024403016214525280182015840e010009001c0c2c000d8013800c540105020700040c50360b003e0300d40e22800803001c1200c102d65a0b554181410300c03001d0b2140c110946590800410451030b039000806002521265801c02c0340c40c400000e01a06507020855460400c41004404548445c1c050221540c04c00c8840302e01500c0c080041c0c44140c41580030b03910071904e142e5100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 917733399 1250 917732149 917732161
    0x1203090512030403020325060f050109051608010513021201061e09050d02060c0c130203060a05041a06030402011803320d05030709121a1f090b06120f 66
    0x1c021034001000720078072030b800c40c203007510001c1d176a0241800c5043d10810301b038981035940c0810760328400342c5e5500c20340500c020b2007103072041c8019010030b00c00c0e0052503041c940814010901844114280c544a99032904c240e880c00b0304000c56a50250014042c15500704540302c01441e20400e8035001e0403842d169000d9032401d00440300c201410f04031201d0100704020500b03000d640c1c0c0d01d510207401d0f10340448119807110b149180e45420042d11600003540050f039405201180784c80760700503520842c0d00715100c440d9159900d00b40001ea841c4181b064400010654103500da903d0305a0165802c24010301d010540c80840092102c0c6014690b00f05803109007045d0200407814800e8182c00c0f901e0101c0c10b201e60f80310810740800302d549408001401051210110000340c48612401c8544001c0201e5080c20004a140d420a00360000d800800c8116240079040002d150310301810844050110104038041802c1c50b05805100400e141451654410800c12042c510622400308840c041d90380c5e08116030450900c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 917734649 1250 917733399 917733403
    0x90c031703010f121a0708040203011d03070213020f030a0b03100c120507032007020405070c0b0a022104061d2e0207020406030c0e100b09011b12030905 67
    0x9480c09100300104010b00c00c0028142c0c1071030854132030580f42aa9040c00c0d10303100f108450240c020441d9041000104020a94041e859a000c0c80c001c2d0001c100c00d00294050008002c480f132206d0856500c01c200400040c200708035000303801c4880890041c200190304120210070750040d40c442101c161144120155490148040c0d414003038000300030005001c69100140861b0b203080700c00c4074016a91000171304514080d41290100c001ca1000b4645800394035040072600360082ca00607405546000001510a0b0241c052120b51542240004050350746040880d0040d5000c0001c80500261030b1000d086e50b01044a4100d015500c201d2000c5409210184031403039100a90300c0d01181d541c0080741d40d8000c0702d9940321801b00440c42c0030340c0d21400280c410017040a4440d00038000d411501c1c0010010511039162040f400703441c091601307401c040c4c84114412010803418003070004114410002403030150301800420740c40400d0500300d00c80d1130065444a000b1000c0c0280f00300d01181d162041c05d8200181 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 917735899 1250 917734649 917734673
    0xd0507030e03070501080a05042d0c0e060a0b0a020703060212010815061309031130030105311409190b010303030c020f0d0f0323070503150301090c03 66
    0x70b0b4001e0001500d850002440c03040040e1850030700d55559000f040c14003414903c21410700e1300c840381c18050607041065845400b611341105451800c03803100f001c01c5100c1511040c2e400341a00426030b20b5045d040003280a074560040600700d056100d00600000016400e0010f0034040e02c0040d00d0182c1589000e4503913042000c49041c64043c464207504001c226038a00c40c620b103a803580c0903000104a1043d10b4160342d000d02d90f0031043d0a91149102c40040c00901d240c0c40d4100300c40070702c0800514102c0721410060380c0028050294404003901c1751500007050140c00e0015244440c040340c071001d04030860074044031900a51034881c0390741c0d441088282c4904001c0c64040c0f80720410781d6134034000552a04140450180001010140c03192a5450068030800490190010020a442d002124220090016135a504001c00800e0900084616000d18426a903840501d042c190300866990034004540d69417008201c9c0e41403101104900810380c03824450140c01c944602e06a00e8514214142070b151406 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 917737149 1250 917735899 917735927
    0x703112107080d0906080f0718050d140c0306092a040e010b010f0c020d1b030813152607021204060207081006121401090213050712020f1204020a080d050703 69
    0x440c00c0c0151f500440d412645d01c903082d80741548034000c0c4c1e0003819030182d01d00d900c00c0394010a9042c004040c1300c3c9001c4802004031031101190441c0040c0e505050b20746404031003074925134000418400701031540081d00ca2444800000076444100c59100141c04c40b200d00d0041040f03a9541e83d4050119600207203000003001160401440e0340c00c440e030004000c042d25080051030060030f06409030314400d82072140030285a028002980310000030180c9403482c0c1481c4244c103000010002840f5403e405171a11944000960400718040048983e80454440c400ba00310320071845140f0042c3c813080c924030b0280c0007409075507001c0d0048500d84006d1034a020400c1103402041443c0040802c200c000c02c1000504917039000c461800c0b03414102000500400c040180a07411060056400e0302c0310180d0703405284174100715240c0d240500d1001503414228002d040c01400e005804010180d0404045228194054402000c2aa1450700d640c00d5034100078403030a0310346c089907010440500300b542107660680440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 917738399 1250 917737149 917737157
    0x40b010e0c04050114120129040617040c170a0b090f0309010c0f021806120a03120911030307080310060c121d0901060f110703112107080d0906 63
    0x704040c1900c448501c03852180070b05102c013071240403600c11024402d50f110360145044800d0150307900c00c00c2c4140c070414114034038402c0c4c0c4074059039800d0940c4002a103090b1389180d50ba50301c42c401416200590810040c2055503414110000025411484089000746901003400380c00d0082141c0341064240c1c0002c1c1c1b185165810010130001c0c0c1c040f00005407a42c4070002d10700000f120351941050400c081c1c44100207900b01c921204901140d201440d0340c68050b86003640c1e01a60b40c40043c03065500c500400500600064800c5241003581030940c00a13094140954014840c0359003c0c0c0020b869a40448402c840502010040202c0c00c1c000c010284000c000500f06a0321507020b40e5500b041d030f2240e1450703074402c0c400c82100348092003144c4044080400c9018040200c2c40d42c4968000c0c0c03690450300d22400004004400242c40154003003000021241e015100c50701e0703143d5030300401c00d00c1000c41495501207072080f203620ec0541000c11180c0d0040c5026009011b05186650b402440d140c4540c000038244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 917739649 1250 917738399 917738401
    0x3030209030f1b061b0a061e02031027180c0501083102040e0708010b0a080a020d0501090f11100503070807030b22050a05100b0703031a18040b010e 65
    0xe80a00c0300340c62120f26040781d045654a030820302e110740e0380d0308468004440348984c1e00e80c0010094a58840603490040540030048034600811680030b9120031500c0d0303580c40c00d40d1402045220f00700e00c51642e50003580101c14105c0c104c1c422100044035600c0b005003140250400c40d03030080c44089210302c00500070a01e48200c1c0b52600c82c0c149070240c5a0b5a81101c810254024120a40c00d80a10b40210f455070080c81484011004032120340d0300e000314001c420082d444c180c200e8102d8940704050004440441015101c00c3c0441d4003000082c50900d281600c8a54a4a01500000e5182d002c04040140b01e891074003ca025100d040c00604040c041c0900c041c4401041032242c03407600401090760001403483c0c04168424014080b61603109030200b00008035070112194452a000c030f4104078802c003480c003000c001654a2503039000348241244101141644100098000302e44070350410b142c0c0e81c0c1c0300b03031888074620404400f0a40c030404070640d1200c0040140c0030700c010000e1894041c3d00401c0007031207000003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 917740899 1250 917739649 917739673
    0x2031b040506030411150c01021b012f0706050108060103140105070c02090618092b1707032a0f020a11101806091a070309060e040e0a03030209030f 65
    0x780f8440644081c000720101d0240345071580e10030346d00c40c01e80c0c00c0341403c143e02c4449442205000c1d4001c0441480d00d130081e100c01004225051040d200c010350160044a0759542e03140c00c9064186549050250b40c2a003000000080348060140e68001c3c40b1420003130655600d141080c03007650b0408071b04500a41d0408091000c820f500c5070460a0040c0c0460703c06015440707100005500040745501c0c05d0248a241013000f07410300c0b011402407140c82c0c10380184445411400c40e015664550129810003003414000690703908a020f41030b06900502e0f03410002041c001c22920f4680303240304002c205400504c081b00b100343e9141c0c8091009182c030864001032003251515035401010030004d1182a003e042c4440040041902c81c80440000e0950f03901c070104d0b400e4480b04004c081c601503002c0c003a0186000d05441c061030100c04110303031000e90540d031a00c0c030b10341c01d02c0411180800329443e00c0c1c0d8000d80741d000a0041002c140500840c05110f0f8500503a103100d004d0a02d41044010714010000d42c11142c05c0902c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 917742149 1250 917740899 917740909
    0xb010b0a0e1c0b0412090503031306030b0a0f1e050f090403030c0314090f1509060a0b060f1c0501050d05150921040501090b0a1b1103030d02031b0405 66
    0x103803141c82102e148003000d01c031070b10200d14160ba580e03024040c201c031901400140b00712080b01803200c0103070f552450304144c2c49005240c0c0e40d1086104902c00100c07440b0040014901c0399004101400d0000e200901c0d11355910760414030441d06030810300f1485102190300440c56070760103a16008103c00c3e103200205019910014611403001000034003131644440142000500c80da1090900780d442140d002c040b030401c100c185656803030341c2500c6d089910446407540c80800400001c07602c05c0d041503000f00840d0b61a50201c00c0980b6100b10340705c1d0404020303c2100034022010018004900c0450726151200d02140c04030750554006031f100b18003c060116850f004590007080c0c044420840c180c0b09151034650340452850651201d165000040006a540c0101c045c04001001190000d90703032500180c0c0c64201d03c68183c85040020740200d0b12068801450035a6041615104c0340517502c06030514544c480400c0c110750041c20b100103550350010800415140740744003100c0d11480c0100081c20507003850b000c54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 917743399 1250 917742149 917742167
    0x903180130020f041404050a0920010e130209090c0a1b0c0b0a0503150f09162a05100b0603040201050f0d061203030e060c030a1508010e07030b010b0a 66
    0x48101d101481c1104201c00181d01114102848a4152641c580d982d80010360040000c5c41c41510590406010a1a084240c0078658001d80c021070034803858007039000c0342c01e0143c41c0c43c03130301d5418404800c2c0400080e6a40c072449010b00094188050f81d9002c0c82c008000750044010030404c4094070a221182606601c15030074240e074003c502e01e00750182c80505003042c0b40b00706613010094581c400984e41c4695a4044003660041184480e800103051b140420499801c0c40e0750740c03441c0c20088920008080b0324490a244035540c1d03d50909144080303007065201d100314800076046003003401584a21003003140c200010716170840c0c008810010301503140f000400c071b48000b41010b410414013140722180f03031002c042160b0b01c50500203801c2003415545d2811582c2040ea085066010a00d800740000c0000f2000c51154414282c03601c2962466031100a0340006100d822144404c4010046010402c86024810201011034040081070101c0ca10b14210701c400005811519000800784548190140c1107003480e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 917744649 1250 917743399 917743457
    0x80319030506010c331b090b0f030705030408090415080c09101403150103240527071208070615080d03020d02121f0f080a0b04020111030309031801 65
    0x100841c1c03004009424002c12105442c00c07403524102c4030120541e0310102d1151b44524546900c03000554603030b40c04e0450b018189031595544c40030000120710078460300080da07101e48590011810451204080742c110f400700e1000058089451009124000b030800c164503241104a401007190714014184040c6410540304500519820180102d00359405009041c80c2808039807981d1129030b900e05041503090050081004c003981c2c58114988004e4543c014140b0841d04007600c001c2e901003c00800c1c6a950b00401499260301949101040301640403242002d04ac1c00303940c0300b07910b0740c1081c201101290507000c0c03140e0350768046c11401c01a00f4000301c0c2c1c00401d810307a4140180c0320f14149000c000030740700300013602c2000d40e8000108107001d99840d46051540e21103080c000358194030f8030250b07040c04850b070013000d80da43d00900300c980010720200c400562051040c908009121603503003101d031854009461244064102240003d4001340603101c0d0509400c00340307400401e02d28610410a543c0c4402440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 917745899 1250 917744649 917744693
    0x61205100b010e090a05150f060711150a031a0d12050f070c090c030b030727020f0703080a143603040f06031103060f06030709080319030506010c 64
    0x2288203a0040302c6500c3d5042001e072000b511860700c0601000148401c0f510020310000001c1040c4540c01c00c460754030204031002d880546000700e0740d220000075920a100d4160b0050b903040205d6810000d803c054030310500c1d29280816082602d150f00441d03452032070929802080e4080709000031540c00e001c03101100a00d41022f81d50341030651140000d61003000d00141c0441c1800400240b0060f80b80e204070b4a000d00c503a010072400c020702040544032465841800c2002c042d5800440d002102c000404282e40d00f5080d00628000000c1d48504042e0007200007500440d80c0201004016000790048c4400c950f4010030351583c0f4901030900000c290803046521812011080341600444180c20320b50390304415600840e03865a94861a0003c0c0ba1030901a0500080c103085002c4000700f010700c1078902038000141800032090940c001e000e200c3e0002044202006212613000500d80000d100a1600d43c10381c0030071320404402c1d440b000d002d441c0c0c09041c071410040304520a102003021115800c0c156459200d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 917747149 1250 917745899 917745911
    0x1803040e1302100806031501031101030f06120305041d040807030c0f05060c0309100e070306110d051003020429090a09140607030e0a050a080a090b03040b040606120510 74
    0x5540d00d011001040003d401291180303448121580050b51103109aa0071000c40b00042907007102c020583d0820b12004006c00c1c0316100e198000d6000744c024140c2485102c800040490fa03800829280c07141140094001c944000303020f001100000c500c03500c416000030281d500b982041d40e0744190a104140000d810000b20716001c0c0108082a41e0031303000c45400c601241d0050404101654144d44240c0d648840d038411610070440a02090090102c40d0000070098907104d80b540c1c0b141000741c41090258075180c0010048120f914403580310b2030380202032844440c0760880c15803060108a804008880900c80450b20240171859012a0f45080c19070007581c40c15050f03100c250014000e840c0c00003004200e40c400d00d0b10709085e040000380d0a88508041e55051282c00f42c00e83d8507680791440c009019085410a1000401103010300004060b403041c1d80c6008800c00d035580200c3c6245420030350f411602d04028100b4041440f425010b2807019180b0524a100d8546990f0350701a900d0391801890004251101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 917748399 1250 917747149 917747161
    0x1a0406021209041811040e0d2f03030907081b0f0111070f090504052e052a0a0f050322051c09031704030b0703021e130303081803040e 59
    0x14000c0d422444e84140403030b00c04440307031800480494078280c8040c002c901c3c111041000702d40c00160111100425120090710260903c52403039042c040301048a005c6000d0340404e005078500304002c5108008400107441003a042c50035050038070a9403601c18911006030f111254143d81d1707004141c000b40c202400e081d21000070200c1c15078103054443e408005081c4540500080c3c050050300000e100d00d1090b400ea400349445444d007031804003003001480c6545045080c07840003580c0c259000e00c2c0c0000380c941480302d2050896401800c0a41c3d61080f0004800012501d0b49040c2d07004070140c0d890000c40d05213642140382160b403200402e861a8032404214403041c0d103000c2800700a10440240c8602c0301520084800c04c08009000d40308588007c940b845050303880381000c0000d1a040e0341c00c0d03d91100c8018110b45074954110041d4029607424030f80152000700c080030707500801c0c0c010169858003108529401d0310310305001c1c00b4444028000d0003043c10b040780c814103208002c4211001d0382c40100700803031161114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 917749649 1250 917748399 917748401
    0xd02031503030d0218040504081e0d0612050105100b0a030b0117070305180606030c04020a02010b0a0f06020706090812030403180807051c051005071403010b041a040602120904 77
    0x102840d5014000050b02400350501d68009140c45003c86640780480d00c0030b0024001107420448000d040d039201407040d400803229440c03440b14a84c40380151141010300b02d2508104560f00c81e40030005610420404030100542801180da11030041820300504a180c40b00f0782c4440d10035503d01c0003c01d0758400900040380e020f10f44030b0a400d501107200342410311300004003900510040c1c5510541e460901c0c0813072034114000451521448020b0042d100c8600144140406504100454000e5540300c1d151405c00740c0b2079042440c008c240e600a100034151800e01c0107820f000c181d40040c4100040800c041c4444400003820320400b2400d680c4c3c41e039803581c8900b000c45140708020340e50200203000940000342d109000860000342c80d0116014540c501c40032100f4800441035074030013070241e00b1a4a01c015004110b51250741d11030580d00300f810511380802524421032780700341c201c850f11942c08102403150202c0c2c0b4880d80842c800460301c040ca81414000c01075030b900b100c913000d0042d89200180160040c1c8403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 917750899 1250 917749649 917749681
    0xc070512030a0e0312040516030503180a03060f09060614030304120302070f031208010e221419050d050c030304080d061a0a020c190608150a2303120d0203 68
    0x43c140c1640d0b110b600c041d101c07422071602954156014490102040c4c420100307080000d088035031100040d0706d13040c08005194403519400c040164844007291000011070068000c140200e00140e8002840d041c0600d081030880700103821000c0380700154540c46000e40c400000b1203050b241140d2102c0384442c01480e08910303003c181d0b0414000343c012440004100b200c03c0d284445444010b45484180d41c0c2c8940881e031010800315442c2409011407003130311010041c101000624240600104003c840414250a1400d103403000303841420750709485081c1c284901400401e401c041c440c640540703031014001d4415500d00002e4030290a0b8070b00000c0c500c07401c041c190b20101c0104002107129030550030456060f82d041d0480481c650150040f02812840303490a840c0c06c04101e0205400c01d01c0081c01d1040c11030b0a0300000b41069580041c044071a1040c0d0f03580c002e42c00081480595620a80303ea140310000444001c68942e8040d500c41000031101010400a0380c0b0390705030b100320058a907a1911100700d11951 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 917752149 1250 917750899 917750921
    0x3020613091b0201140601050403060b0f03160e220308070c020907121b0f050c0c040f060f0b0a0503040f2603150303090d0b19230c070512030a 63
    0x21034160240412a02c4100c1c0362192035003a0000c1042490005071089481c0d070864101c0c2c001a010401480010265401852001406810440300d05d54610200e40741c008284019903600c4405442006030f00c2456094552248003112040110400740100c02e0903910030b048020180080d00002404140c8a469035410842d00104400c0050a02031006080303001c1c15500744441a0034032400000c003a4915081e0000041c042e61030a01041c000c440444154200c400041c600c1c1c003ea1490310055a02c900070340340b00c071104203000a00d03145403800140240005d80d0211a001c0000e0280840e030079001400c0c2ca03401a046000700c5400220744ca80344c0120a20407044101c4008414041c1080d0070351100035500c54140110750707002403551070702007503a03034050740c0b5216500654507094840018019a01c081c2c1040341e0754072500c82400071440354000d840c00d450361071105926002c44004050b503c0380b0700075000440c4181d460701e01005030716001d88417882004442d04007140080800c1c00d0864940c40720301c640d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 917753399 1250 917752149 917752151
    0x1b04110427110702040e1c0305150604080705090112210c0b0f04050106060219151b031b1d01030c120903030902090f0702031b16030b0402090108160302061309 70
    0x2003904070b0144003981051100764001c0b85020000107100c0320004002503100c030729200d0303940282038840f003c40240c54000c007001a495244200c581c241c2c0c5444000d00040c0800c0c00c09014014100001d0000c82c00c4141e10200c50050340c0340f0a000400c10704810024044070742200d81d4180440c0032800d41d83c0700c0c41c00c03200800c0300a010003001400c405900a084c0154420002401030b281c0d2904101d03a40c6c0b59a15038502040c1d1780d504004006124180191071482d040d000c08200700e40c2d401401d0144081d081c0c1e50340003103922080d04030341c1600e000842d0030071812641886d01c0c000303084101810203508a525041e040c15510b10a03075002c24058180e030302c0d040384440000d0142d010325107030007070180c484030b20100c1c0900c041c44040f60748040701c0d01e40548210410350003142000480030300605400078882c00e0b4a020b000d100c0d40da44500c091202a0b1015500820380c855880c00c1505c1072010194050303001012980010b640d020107180740e40080c4040700e03012039290b07848200b4501e00c0c190318403003a03100d01002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 917754649 1250 917753399 917753411
    0x3030e0a0b2101080106050f13060b070c08060f040321150801020c061303020606090403111c110a0809010509010e030109060b09150d170c010501081b04110427 70
    0x100c01c20b009046201012844a20035a640e40c845030742600d031a17000b2290310100c0001e401301142850107450136842111900851501c0c1e4a82030151a0380c40100c0590300107500c41d009200d00b2004122203600300c105139071038184500c0d1a4400401e01d0101811040e01141c1c41030340c08065640c1358200c5119a12080a8190f89681e1800b00358000c4d44100503080560188000041c000301000165011032038058014001c0303030b80d42d0000c00490f0280107204406120060300803851602d01000b007440c24100480d407500d02c1006a01d0081c3c01d18449500511050b4084400480080d4880c02610708420b0203080140e11004c040740140d5050040040e026099072038410010b09000c2d150300311481030fa406441401d00d9031101c404c54420704d03800c0c2c01c610350001c034003010450024021300000c501d40300c03c0e0000d003401c02500498813429600280d0105156510071054600b4001006c0d0b003004104c94126000c010014818038000b2280c042d600c121500c3c0651030703139110144503aa000350071051815000800038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 917755899 1250 917754649 917754667
    0x2415050f0c0d110f1b0f010212030c07020406080606010c03030e070b0c07151805091803070f02330c07031502120105040501140d050f010c08040210030b0a03030e0a0b 73
    0x58500100c3c86114900c10b8040140000ba0f010039900010702c0300c00901307040e20004109000c503041c40f4100e000d046102e96101405241d02d1000a10300803c8010f040b540d507207296004000590700103401031a4907400c048107105850b0b82080700600e0300c03940b508001c140311005100c068180506a8020b0194000001e014204110301142c44010b0302d100441da54848008404110354850b505c40324901500701d01e8409009610b031100e419940034108e20445420400c00d50561130844c0c03c80d001c00c5500c06041c501000441c90082c405d01d520110354030311080025440300c40c4402516021b440c145001034002040500c42d0400c3c4242c0c006560044164203041d13140740c11400082d48a0292030b401542480000b044c18607290066a0484050807121401e000c0180c08020b20351596813000c039024400c000405c40071000a000e20341c0c82c2c52864817020094034060040c0145804164261010107142440d101300c81d940b001c282d54240c079098a4180d40c0498140f010490600142d04041c1c442540440d40000d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 917757149 1250 917755899 917755907
    0x80906060d0303150609090e030c030a0513050a030f02010f2c0a050901080607080a0911010f0e1012110309060f0a06031a0603100605100e04060b0a032415050f0c0d 72
    0x41180c0c2c3e0004100250100342c0744240d04d90007012031a02b0301d80c100300f004403a454800d80250100815591150036100c1e518400035003041555401103c0085540205030155a00300d40f00000c100b1050038030386c2e101d01004a90f81d03119210308848591084040f000d0345e0041d00ca1003094000340ca80900b030310100f561034800301aa96181210000000317254a000107036005800d005000c3c034250b105000024910f01000195500c81001445200b0032151114070bc4003a900c84001c0e400c50070f290307103e410148000d03030851015950160100700d0112030800500c40e000c040061b01c0ba034440003602020f0166218410f00001070007a90384054190310f00c1d0b07a1003045245400050501a40c000c4045556a104510f40201521490b100d01030784251051070502803140229004450200c00a0000402c1c0e522207450403c0c9401140d04440040e94441852235020783c4881d000005030703070740f40303200b116285402001d071802040d4810300400c128010810300b440e80781c1c1205440503071024074290751183c0302801000f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 917758399 1250 917757149 917757167
    0x30d0305040b0903070b01091116060b0301061d0f070c140c0a06031b0e03010204081f110412111305150a06050a020601050f0a030c06110d080906060d03031506 70
    0x1640348030944000c124112400401c070745c08075a06c40e4040c160713a8a004602001444030134050f2403184400c02c0b42001c03183d0031055040c2110700c559400207015080d1018107086481c81c0e0401c4500440005400a0101c1c01c04040c03030307009072913803840400780d510000111b4038110040b1004185034441c1181c014020408159041150230643c0e2040035195034507011001e80e07042c0b0b0305070700107005108070702001c032845000b07510b070818409000035283c2903550840502c1e1682c0c03042c1c00541c0c20580c0c500d100d0103a09501400910b91002a696070605052406189009048900040010743c03285614041c50f21450b140501c801a06c102c00c100510380084070050010045041903c200760880011035102d000340156081c01c101d030f5008118903800d00060101a211006600798032100c43d420000c002244454801e02074122a5501c5070388001200080e40351910302040c1a0503c1030140c2000510a40041d0381680008119450205165107080507001004c0d0038402e000780c400303200004036020b40c00014603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 917759649 1250 917758399 917758403
    0x403060902061b24070522050d05010509010c0f050f07020414010b0702120f2113060207150504031104051e010b090127060507150204090b040b0a03230705030d030504 73
    0x8440341081c07404c0800000000c5800c0d2010400c28011003421300c1f5100c1101100304009200920b56940f5400043c40100c80c1d0300c801c40d1269110010013074540720a0091032141501420b1114840c0c0b1540b030058002d004800c01c100000c031000c1005070556440341c0020100848090300e034407895850700303c114400e62204405030300031b00c01c01c41c0d180d11303c000001d07040d0000b1500b0301c064152400d42d15040362400016100c1441a001d043c0710203400c441012001c80024100e540007480018501040c0b450120046a031440500800344020800701d41031040301030f841101180c000445035100d84011047c40030503000c102d603d00310000045182c11011008000e000d4090703e07135040c0b9140c01800123080306102c804501d00040390403410420355005101070120b99200c0c5484030307800d8011030502c0d001c0340c01070703404030f0030341a224000e00400d0b05140c1300343c2a0b480415500064203e081d907c41002421000451400880000500780080755062081602404004040e00d01e48400c14100034050542a181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 917760899 1250 917759649 917759683
    0x31030f0e010c05030d1e0203010906082a060d02070b0f0604060b04140906060c0f0c1305160e010e04020409060e220609020d0b090109060e120403060902061b 69
    0x4038000c00d41c0180208203066602400542c6007000c03403500309010f4420300300400440840150108411078507400914041d0040c1c04001804034542108a442c0c811b03010110325601178074180081c00500e10b007245200d214400d451081d134411003a00840002d00c14401c0107400d40750083c003888a00c112000c40140280380c101d800748001034552030030724034512036841110604c01c1e041903c1406d5040c941205640104000d002034141091140002e050030014205d0410319000f0400519083c82d0200503043d00d40fa403144100000e2600c001000307c2d8a2025101c1000c0c40f400b950000b107560712424444280b900007400554580359665560f10107003005020f500c0c002040302d0000b880340189039255a6070b0707400c00711142c0d02c00300d100e4580303030300070440c9038800e0341c00c40c80502814011420f043c00081c02501044000140784519003016012201c0305d0740245020f40141c1c000d0224824000c050301d051360b80280380011498024400600c0c5442240c6e40e6504107203035044406501c44011a0b0f400800e010500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 917762149 1250 917760899 917760917
    0x1217121602030c0a021018030501020a0807170718180f0f091211190b04050d180509150d140706030203060627040510170a030831030f 59
    0x10341a41c4038000e204284159034000c0942c90054074004516501a07602800c001401012201c00c100c0000d0050b0800c0d1201e039000034450750501d920034103d65100310b440c40d01a051111100e0140114071002c5c004404124064418040c0e541e02c2e074118100612805d02074021901d03075501c0100c0030b801228841c82c82d40785000d83d01e40c034a141c240603c00a26510000121900516520a56480c020f040c2014024070030707500040c4482c2405001803d11902540c0e21008502c1c0c1031071714520380402c00740d07044100b014041007a80041040b0341c103d019a041140e80d0221540c2e00b1400c00194810a0451382d4003451629501e02401280000c030320704d1007d88415641c01e10340300d02e016001da22050b5011a0012010042d00307508094403840710304010b103c03103806135028044800007070503141c0c00d9603220240c4010030410000c0060742c20031401c080c4c486c0009001f4030320007078034017403ca41b00040c14280e846144c00c9040000080d200c01100c240c0900d00703000d40b003a02140c01e0007814040042030440111b43c04403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 917763399 1250 917762149 917762191
    0x506090112390f0f1a360a0501020304090f0902030d0e031c021207020103150e0a0c080405100905160914280b01120e0d030b150301121712 61
    0x801080c0c00d40300d103100442c0030640385c8646102405020401c054401314140400f801c3e01c280000039000901e1081c101c1245040c1101a8803030700e10020506900c6685d81c5030003002280d0300441501c003124021400007508a500402c03820140955501c020360501038a50002c0c0c402c1c0e0000180303150030409038201c50042417202c1c080178010603034015107005a0f2060040600c095501c00041550710710616010234249265940c600070010250032440d03210641c5004c00010003c86e20078030420901524041c0041d0074a6101c0d907858116201e068461252030300100743c1446000c00c482c02440c0240c2c2d1f08003a2890703442003204000d04a0000e07815212910201141d202d006d01002080006d5094641041003108691032200818480032014148400641031490b401f80b1445000e105e40c4401020b81141139503030300010101d800c08014a4815040807a01a41c03030b40008060f44d06440f0b10198401d0703203183c2d60500f044d610b50042e06025100e000022440024039a21803400e000c1c440c01c81c03035030720a0700d02c0ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 917764649 1250 917763399 917763419
    0x60603051602060f07030617060711191b050907111501031212060519050907020a2006090603040f140f121303140a030f03050609011239 60
    0x700c1c1a440041e8041400324581e00244503010fa00320a40307040024001d43d4609031031400d030711690300421407a006041080301c00b580248450516106000281011803102e14618001341c00400c00680711740c80040000e994041151341e0a07024000007003141500f440d150070010007074112040ea1402c1800f90813605130054400c884030a043c1c1e0360110410380c070304030491000c81c1c0c60000e074142514840d480300000070b201d455440c9006020b00ca154040c824040c01c103000c0c0100c041000e010318046600000940c00810014030110340014401c0c0180002ca514143c0010a00c0c040c00444541c40540001070004100e80e0b160780c1101e16219088034044843d8a46515896904000800c000b50704110f040701c10100c9004000c02604a22840550025850b0b031501185c0b00d100c684405015406460350b00c09164105190f9840320585141c14004c0d8604903003c00c00c952010300c504ca54000030b0f03064490070881403210541616003241418500d25164200c1c14054000b4040421003038841c812000c105440c3d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 917765899 1250 917764649 917764681
    0x20705030301032109050f031615020f070b0a0513150305010806070c031b17030c0406082805070201142401080c1603020a050f030415031a15071506060305 68
    0x90b42c4904054501c6c0006008803040521980c66140c0500742e00040da4080c04094400a050410b90b401e40c48a8504800380c9807401ca075035440e0b19070303003e0389041014905900458185c000180380c06a00c6402e0308441c815a0f544c0c0d500300703095400c180040d21401542c03582c412130480d9109800c07100952500d1000341c89a5050000283c0001c120104441400308020142d0316914481c4a03174034170300100c400cac440c080c0350400e403041301d01d4020010b410400c40b5403100e510358000394021005d108460310418400100c4110a040310121030b158000560001e0007903008111003140d01000c0e10701d0345020349510160404e41001c8207100c84101703600c8549540718041d01032044000d82c01e1603152205414500004600b01c02c011000c511500e080031001907018482e0009000b0400011600e850405805a54210565441004040c9032101ca00a9140b0304980c60407000070540351080c49207071491403c1c0d182d104581014221400c0c00340b00d80740d4a038641e17001400300d40469508110743d45a2074a12008004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 917767149 1250 917765899 917765963
    0xc211509030215090705030109110901270f0e01021902060903124209010e060102060412051303030c11060708190e0a060e0a240c0204090602070503030103 68
    0x211072000440f4101081d00159000320000c000c549540d1b646200003401c3d1802103004031503601d4107040218050810140390783c0500340e20b07e84248100240e54161960000a030484030302e95489130302c080c1c07880115500c60104608440b00030355540c0c0c02d4149051701100880b504200502c11080003d28841002c81551400e80092241015649500e280904055808402141d280380315100b10406088002c0c503140300c11060312103010101190b1010090015030582c41104994811400c0051603a404a155139106d50302c82c110781500070500b0310131280c1e405800c042c0d0000415a540110515422140da104151301c100c51074074490740c0344c9003400024000ca80005020b040c00b0f2003050408400700c1d486892030501c0d4501282d1080308800007614480715580101c01203210f409040d019410950840c4001d40300f10a00740700c40c070246801340701c02d10303045454040410032200c0b9458210741c4c80f40c01c4100c00542181080d500c8802900300680c43c3c1e4828403040b2450042c001602c04044480358100100b11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 917768399 1250 917767149 917767153
    0x3050f070b0408120c010f020403031709030a0f0f020115081e0106050303040b0a030b09010b0a030e0a02092202091503100b0105090d03031404050606130e07060c0c2115090302 77
    0x7113003100e082013a000548846441c3d501e42c1e810000040030362003d00700640c000d0341c5240340050455804520428058442c41c0c007500b0402a000351107400049000c0d0030341203403401035541c41000780101d00401503050000410304e000c0340d000420781c0303000401c8006022a001e0a550071030701000c0c0305080314202d200701e079059001880200b188540c9000039004540c041e0078045007460740700c400190b180c0003d03080340030401c030040b03076107401e99074103100b410107944076240101001907007600002d403401c40041c01502c9664000c013440b4501071b0b41010080245034003405210350b41c00c0a41c203415000c840000d10074064403c3d400c084040c2002402030f2081668180c444d81d1070201030600340045540042004e03000c1c180c5601e1981c45442c026032075184114002e202410107418440c08000070214102c500340442410410700c20703011000400c1e02d100301e17038090400044881c03003880c040e0480512036000844d440296242003a0300361540040c5900030b80300e58014040c10b5180300500f400c0381e44c2507801900503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 917769649 1250 917768399 917768413
    0x50c031b0a0302060a12060305031c0203040b0a2c010f1b0906030b012c010e01030b0a050904110909060910112a01180c15080417040e0103050f070b0408 67
    0xf60401000902a145d410303d0b1440316041105201c00c01d4502c0c9520480f40da40c000100c1c5c4110b10b40300100703100c1045003040d056280d0308064585200b40f25025000e0190342c3d030b8440c1c1004a1300e001d5002c02d921101410800c582e6812032629050003000f8000040d602d40e4100300c20364102e54980703e0104500b00e5151274515120313040c040e0880007007114403011070501001d0a0150181c10869441010007482051030703001040411000401c40504010038905240c200900605039079600c0e1824001d4a00a480400981d03a0b141045503807112100307940c0d43c210340c013141403003a011000f0034082d00c10268441100d041400c080e401e802144c601e45415428002c09220095907904403428000075100200f092039191311104510a0841d86000394401000c0398500c3c02c0350403c50314405c140f005000107042d03510100204180601038000040c030043c005003014240000b08548001a02c029280110a4607441c1da103d01c1c0996503003045081d4a02288507450740003074400f8030142201c0c2035400100180101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 917770899 1250 917769649 917769653
    0x30a03050703141603030e2a0307030f0c06081308030a15090e070501030e010b03120d06080d0801090e012a110111040618140f030316050c031b0a03 65
    0x285070032488007141000030941c0b11042961000b0060400000c00ea5400c400d842c01d2482c019048a0074050611443d42003148180f1046003034402e5041e0203080405403407400000c110001c3d04003480d6400003400101c42d03940b00024010002040403e9510640f106080350b1031304c3e080c103400c888001038000c003845410400903000490035002414402d0402e4040210700e9100d40ba5801a26a0550941000e0b0300050381001290783c14000c1c0c1c03810002000c0200484041c60000c00d4542e00c0440040d90185400544141681121ba01a000600c0e071401a1040c0065100c0e0040c500a002c0c42806503050070030448501a01042c814a1000c0c5012244041e00380e00c440217018440969040107000d200580e042000200c2c0203000d0f0f04085100004440c4e6038600b098009480440c02003128440503078940c00c14048100b9048520b5603d05040b910303100802001c0001a1941c4070301c840000301e5404290003d420030a00244074494039030100c090b14031144110101c000310f000f89003038041e4480380456003040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 917772149 1250 917770899 917770907
    0x80712030b120c040c052a07080708030a091d0f1305010f0506031606020c04090618111507020306011a130605031b120412050c1b1e030a03 61
    0x1408062608021850441e0302001566070549141c0340d0299802040003890145070a115084444d002c600b8880e0804138040d140c6440881003c44021641c00003007a207800c01c000c10400440240700e006d01321103c0b1500c5980c0d03e074072030300f000c6604000303d0b12100022841740e80314180c0d01c2810a10041140c8660340703400d1149410800600b043e06040b0012500d0030100f072080c000d69541180940003c03e05082c0038041c98034088007100b20305880640c3d0902400701da9400314103010314803400c58004c13030100300c5e80c18213078000c260000341000c00c20b44018504007040380728001c81c0d90103801121445225031889a80d801a8828039400960580000b401132000c03c0c0d1008611f00f80c884a014447e0170114217100032424003040d40c02c2030011410200402411110f40700004520108000c11300e07007001c407041c1e070f0b03080e011501a00013442c01000c840603001c2035100b082900e94014000084130101c4042151880480803503195041c020800d0101e160b956685081070400e903c1c50242c01080b1042a40d18215 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 917773399 1250 917772149 917772173
    0xb031009020f0409050a140c130b01051201380a12060f030507090e0304030b0126010612050c030a030806012318090709060e120f010606020f0607020601030807 70
    0x90b4480d0722254915466202e900c80c1441c00341c0b00320003c014244003410721030300142d0360600c0005190311080c0902c82d942c07501604180c0c070a20500e00450b100102e480166551b0260f641518940039281000185140740702c800c150901100103800f0513040c001d41511312111480f2031003400a0300c020410751121501c12017074925088a80000040e02c2d503140c81e000549a400c60703000351000e40c45808244a11801403107000100311500004500d00780c6181d8030307001c160005210754082107000310640b10b84114807000d10b02005610300000c000c10b645800c60820301c1c550116081d0307503a10560420710031a040019143d04910341603142c10107103030f070b40400450394005920036038045001c1e0481d081021401c244c010300505048598040c0500711000d091108111000705010100102080b04010a81e044829921241004e85404021224045172a803030408011441d10403503203000c0000580d01d901080e4150801b00a10a444940c0c5070f00404170b0782c2303000a00016141c043c04204280c00182101101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 917774649 1250 917773399 917773403
    0x4031b24020304090f14101203050c0c0406080706021002280507060203040b042907080c0927011703030106181d0a0501050d170705071503090302100b031009 69
    0x80e8902900ca1654030103564400c500070038069160002c03038419500891540342d1208200320747d11302003417410b00031a2091001000103014030100041c51007500d9000d04c402c14148070044d106010840e034441006950300340c01d114100c014002c1030011082540030b4000c0310441411007021407014100342406803030025023517000c40203006082140100040050016502c0341d030248403203031268507203400d040c0d5003c0e030500c00c0110f0030070440f00c2400201c9101c0003d90b80100c0107281495a0b56914100e4131124441c0302c2165034041032060583c2543c241741c0d8124180c0b09100d40c095940345e6610000d140d1602071102c29032555820910052110070304c1008441c100f2440f02035400d0019994070003001e00e07521000700000b900e8610f141006a1058180284c40c010003050703e06c2014450f0303945408650203003840050001c82e00024246041c080304014107405003030311a0701120b185103040c101074020200004210058000c140750720410000b58800c0d03078004000a80900b0203000158500401003041c1e00e01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 917775899 1250 917774649 917774653
    0xa02100b06120901050108070501090608150f040603061a0604051f090b360a1202041103071d01020a0f1211012c0303071e02070504020f04031b2402 65
    0x2200e054024200c4103004103c1c00000081c6541841d1186040c240d860308500c0c18000080b104020056001e09084e5101300000800020507200d0400644503000d00343e159a845401d10380d000c01840305d29480115000381ca00110b100c802c24410074800720380218800e02d0b5003c40a00e8507892082c1070104040c140030660b180c01250283c4501c01a006604284103008003d203520101f03a01602d2080100090082d0105106000211060015010003681c2c001c2032001c0e00516407180864580c0c3c0c00c680c80c0b9200c8603002503240e150440008000540d450300c3c01e40700810201c0609015400030030342c625030315041a05c1000c03000023a11400101c004141c00d04041000c6403a0501c1080000c1c410440076084000940c103130460081207821641d120003044054642007001404483e60704100d039500e440350b20048002800d804e105059040428960180d034215000140400c1c2c2984414000e00c2a0391003a0100ba4107041040024210046103028041510014030b030024001200503000c03549034001881 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 917777149 1250 917775899 917775907
    0x1101050a1413111e0f04060f050114091f090e061f0509040507020633190902120a1407021e0c0d060e0d02030a0c060f0f020c060610050a02100b06 64
    0x40480c10030307081000704000d000c100000580c05450f040083c01541c45044806101513420301e102318102c1121840b4503418060300e00c9031401a44803020a8500e0f04000410030320000b0b0f1900c4000c0c00d0079440d250900c00103070654a0200714250020314180c000c000160407a03003800c1e1003031782e40c01c4c44400100500042c0b02040c000c00325203a886001d4148601265030180407242014107250f083e07000080515040341941c4003082c00d0b0b446030041e8a0050810803254501c02840407500002400d505804c60030045000013801c07091145d0840150b4020040058200200d1045c0c0385144a020000d40c0c13160010b81003021212882d916940450f940c00c83c0d04000d850542113801d00089003a80140002c80c1c1d4191140c411060141040c0b1001140380860b0000e140760a40420000f88122040754000b00b01c540d64002a00c20380f0001d40c4a0100510720040440d0703100c241c0308401e0340c0d440044605078800c40c1e0305d0340343c2200305120300150f81c040611900201142039001104d41d02508070000b6007504040c00b44 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 917778399 1250 917777149 917777183
    0x30f160618051506040902150d15090b0117010501050a0c0c17011b1e0c03030b040f150f0f0306090510020f1206030303010f0b031302101101050a1413 66
    0x402121440e511640050164040c03000c10140a4003000b0300e045c0c03245103400000c001617140c00d010000060441c990310350f603680c10214944024658140e0344040701c0c141c0603011603104016401501ba601c401d0302c0741282403944404403079406109000c2d05000400a1103e410342034010781490050a01c2901c003982c0145d290040140105203000101a803030791a540c0c040c011125880c0464058240c13460907140303203042ca071030001d0561074000852003007041d61035148043c94441d42c80410384000c02007003800380b000f100d0300c2c0d02c01900c00a0365604400a2115000842c01e0219640208480f160482c919240b031035030f01e8190080c6100303801915a4000c07145030040f202600c1c801400a504403d40460b10758000705071100c480200180214082e600070001401941c1012801b48121207101d4250b079903d039519140209104075485009422100c640407a0701600d40150031103060b03c0c240740081200c0c0c2e507060200002d54001c40c441001a01d0550b0202d91004003110541d5549802800c198030841516 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 917779649 1250 917778399 917778431
    0x60c050111030a091502090a03081c140103020306251202071e05100207020102190302210301181a0f150304121d090a051b03040c090e030f1606 63
    0xc584600c111613440a0351000c100e030119012442d4107100804500b040810004200486540d000180075030b031000c40c80182400c40b020164000541d1034909005405045c000352500d50420300040340301c0e0040d680001d00e18a1203100061841d0340008004141441290056401d500c102c0581000c09408028a0700403510450002c400f903600d040d100002032a8038140241014a842c0d24801c030140104641c20160307a00007004d00c2900449000078011208900c1d040c1e01d8018042090800540d80c88851520660710340c0145040324000d40c10001d1020034005810704071101d429404c41d020b203024075680304a061442a0601d2824060b100d00001048501c0d1030105800450303046866035071090803074000c907910515035038243d00035500c0900041443c01c000707480624014000c410050b610750002d01c03443c240d109864100301c80d41d505103a80742010305122081001c0f9024117140c0b03904040070920342d5038000048070b5079824210840b81c01c04400381d034064045006100245c0e10305031190b90130440f440807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 917780899 1250 917779649 917779651
    0x30f2a030f04140303090703060216060c03090b07030b060f0f090607050a11010c1e05010b0d1505100302010512060105070c12020f011803080304050a051c081609060c05011103 77
    0x70072604005529140c40d000c903909411034030340c0805400c14014001000800503440307080d241e004e000035031245000102c1010040c60920060076450a01000c03083d1650964480c0075000e000b07403624003007666006d0042e4151442c00d00099005501005071901e002c80000c0500080d080c0c005100d4903014488000035060b8001d4481501d45800280c3c261082240c4401d06081c0e081083c01c3c9903800040d140c480b43c58800d41c00712106c040a50b01c81019003005000c3d40f000e01e0507000100541c00008150804c1002e0306040004070341103e03d40800301c0c1c5040c000300090703022070340c2c141d40e501d2800101c40040451081d0103807410341840018403102e80002c1042e0083e0021344905546081680958010441d580300081c042c2c2e41400070a0f80d48840d4103106400800135280c000c2825075480d140c42c5001450701c1c103081c0c80a000c80c000e4103c2c402004107804504201c0004541d501c3c40380b51030f4181d80309041c4904440b46408a0340d03a000400080713014901040825006000004648c0e0b2a00448002544 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 917782149 1250 917780899 917780911
    0x2030a0308090706030519150506030114090a0603170a03061d0a0f0624050403140f060703020319091e03050903011104030203032d040303030c080903030f2a03 70
    0x94110200302000408004403c000c218a00d018860fa051980680c4001c1c40b6580d0704c00c507140d40f034882844061400100d988001d00d0003402840d90707982c0d03c102c8480e0b800301104540d44110284404102c070b201e441e0090304e0540790405145c04101c0c0a180d0200d9003644182d800006068440c200081c04121100c840560859030203009211460215101400c41d4642000e120302103142c0132050100d9400310304581982c140340c40801c030b41115180c3d0b003602c49000340d900082803c400f01705031064110004c0b075000030b0829094101d03101d50b140d81d4025400c0e80411107200300c01c1c5259002e48480d0104a400024034503004ac0d50701d1180044c9202c0c59842d0700b1048505034045500091060010b007030034851050303c2108003100505042c21540042e4aa02c00ca51480307600c15080c854101c61481440142d001000c03090381041d40d01c2d0f0340c0b4035010300030b03060880003000802e105400050584001008a030303c0b81803a001d40d5081c41e03461300d2051070980c8209808a54982074964001a030b1a016001540558 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 917783399 1250 917782149 917782157
    0x10f170d1b29060907090e34030e15040b181b19120b09030408070609080105010b0f2a10140108010c050301060c110603150a08030a02030d1802030a03 66
    0x6000c0079404000c5006000f180c05072904404021010358071600303400540302151542c00950700c42d00c20703085544202800520400346c0300d50701c24000180e0f8a40004a04c840c0c2d032820301800d94103038082521020702801107044d900c25040060001501c0e0f150035a401070b0510700804240c0090074500e450b05548008076454200c0c20003401040f490711810444e400495101081344442c102890381c883c42d6400e020003802c03c5001d0010550b4400b0a005580191510b08101c0e81c9540d52044020030b10920b0744541d01e030f19460302c1c00106180c0201d00840d8520f1510803d00ca00d04003084a00b002c0040307880a409005100c0600310b5440d01e4800c1c800b0f01c050300c0102502250380c80c1d49580f07558580304181c0c0180840c1c1e1404003140c00542c2c00406490440316a41449201c046042c107050000c1000c1c4a91250310078400410480800090301c0c1e030b4012001c040c2e0348214071540b1110215568400d45400c20b01683c005d0019215200c110f130400917003210140030052920026034040382c030340601414110041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 917784649 1250 917783399 917783453
    0x5040b160c0e0106020a0609050a1e0b0601020604080a08090703080f0915161205120109062105060c0a051c0c140313020609120f06010f170d1b 63
    0x4002007120341d41c090031144106840c19490248042e65030f4482800007001c15448504e04024440180100040c15422140c80c001c07003103000c1080904409d042c801110910102d101140a5510004005210b103030710440d02072900840c503009a40140d00206919200e100344040440004c800002600d406e03140d080000303841d450958200064004e80c8001c0034000c610034407a01141040d0201c0c144c03091600b0039242108400024401c94462043d407040f045485111800085c0a11030b5030311050031206000300c902c051811010340c9150031080b000c0d01411942c00032005c540c0311416600109400f0744681011407030141107694011020b070290f152441c0d407a80c1d482e511000190003150f031440e44240d16041d00d1440c0b42a1200c5140c07540410700290040201140f1003100f03403038101d242c1c001501290219001c584860000603918a000d020341c16204982c140d00081c502c2950800102034414200544542c00c1031003811117080486240c00291840314040e060040386540ca02c0c0054141e40b91020054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 917785899 1250 917784649 917784653
    0x1a09010e0714031207020612040f050d050910020a02130f02070c1401020705010c170d110705210f1903090212030a090e0415110405030d0206010e0903090603070f05040b16 75
    0xd01c510b480c9441450041000348170b006070f42d0541100c4a85201c42c101000580701e41c2824113903d4601100206544540e500030006580c01001810034000f0885560b03101e840303d0482241c032001b60341c9000b17411000c10600181d40201e690042a40050362213001030901004da11000c2211203c3d62081c4080b0031000c650f00310300d503414006040074020a0030004021540ca549142d5007805040100c21079100101d08000841030582110515040e40000c05845c0d010900706030340c89441c2203d140c2c40d03030f03440d41c54a01440a2070390155000100228003a60900740c50042001585c1101074001040682d41c1510400681c0d4520a005d80e0b040d8150065854031610b20002e400d0a80350f4200300031071203042e000c0000248825549024440704a400031501d062060300d404c406001d29009160306006040c0d8041c1041c1d400100e03103040351300d62701406650340c5a42d0725144e100d1141010064100c0c60410004201074000c503442c2c640c10249103042464075954160900054003d600344d40101c0e040006001c1c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 917787149 1250 917785899 917785903
    0x12190305130602030c030d09020609041d06091906050603160303120c05040509010605130e0a02071a2710020a030e0c044a010c0f0801031a09010e071403 67
    0x1002d40701c1d500041d81340181c6928030a0345e07400303110f0146040c1500c41e50800708540310318003a10400040508280461002410701840020380c600340c1c810584981400a41d100500041410002581907402c0724054078507143e9401504005001075054031441c0044a0000d025240c0c0d88000c600a030b0b5000c000c40300c80c07003041d82a10f4155141d18100042070105003c10303516058414111019800c089954103904104400c00306d10f65400310151019800030081b220035542c0062952a2041814501110340080c00c0e824010b42607956005008101034803a80e620a00303041c00c410300111204807020500c60b4040c3c074040ea48803400c032000007030b100e1010b8003481c1001c02030710b14001001ca801740700c0e101210301070101d6000790440f00b50b0030754040031002c0d80c240090b80d03c40703459141140e012528408a086c045020b0144590100b000920b00903d8905080c8a251824162540400c0da4a1302c9452141c10301103280f800342621009550b0b541c07400c2c0081100700400e000402c0d00f1900c024403c0d03410300800d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 917788399 1250 917787149 917787187
    0x13050c090f1f261e0d0e040914010e10050112140f060a140c0a411b0303010b040e041109040506010f210807060b030d031e1a12190305 59
    0x1240740c03020702031310404900000c0756140050105207407604180440300d0000e00a080382da180a0845400c0c0544459000e4040d000744002401c5401120815040070301d5000c100e603024415144203410341d050181c002003100b28950a83c800c1002200d0894402804060030194150303105903200b0b9917140350b04403007103c10135415404014540450708295900074040c2405944114964488a101c240c50a103810544c440c0b13141c400040d4500450b608000724444055409243d209411400c50b000940107204008100c07810f031451580380c1030500c6c0ca020f03900d00e892030b00604200c1d20070f40c110b030708408191580903800b031080c0d006200411a651621900b182411f903036400603802c1c07600448131900b42c000701d000d206a0041d48a01015921031060902c80c00038130490250a9240c081c01c200c10310300300c0e032640100d00c00c04280c0801d407410095a1070400c1c00c40c0c0308030740990703106404100c0c02c598500e400c2c80d50348090b6440d41c4c192901c000c04c01c80228180d08801408074041040440c0d03440b62080d501c0320362 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 917789649 1250 917788399 917788423
    0xf06030b1e070e0f24040308030603060c07030203121905090c040e0102090f15130803221a030424090b060a03020901150e040513050c090f1f26 63
    0x1800c00002150f002c201d040302202c40050181c03800681003844450008201184180640300c12a12076440c0d283c109160760065411300e00c42e12411300801c510422000c122100e09505400851400c0781102d100c0320003603c0140102d10384441d1001e9500100d0582c01174900c1290310202600d5034240031800c12088175045a02145140e10510642d47d06480301103195401d04403c890345680c00e8540c2d4241d01d05485841d40100c0000c104000002d00790390b00001400e0a03504002c0e10081e410303010b0030108084034603481000c01800b07401703440f1800300030020020742d041f60061144050f8403264400404038034645840d0701e0205a59100c0345018001c18135021074102804484810316645960002078900314180100e07680c1643d480c0f00406803d0181036020352b0418041c005004a250600b00310400500b4104141e40a000b8000c0e200f900e80b60030900d07a84034202c1046c541c076a6841c0c44003543c9480c080d880c45990714071110b442c08200780d558031002d5001000d40002c15803171801c0e0301610a04100b002c13501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 917790899 1250 917789649 917789657
    0xb1218121c05100e130f050d0e0907031b1b050f071d040c06050c2a01080114010f0e04150f03020a1a0909070332070f020c040f06030b1e07 61
    0x10a01c0301035031600c00250421182c45e04c6a081c1445c1d410708200c00d1156400c02400d6215403120480504d0b0401c01f41c2403414400c45042d10703141c0c0d0303086056007a00c1124040c440807419500030f00c002103008000aa01100e81c508000c10104c103141c2e1200e25044451048401c658441d2300f040000041c09829400c954440c03481c1607825041c695140034401e60180034000901c800455800a6200c003009a24401000c1c1c00d03000303400d400620f12000c041c0b1454030001e4005481c03a000482e88540c111403030b500c68031040c3d4520001e8211b941c022102d80b8081d8803c01d9000f91030301d04821409504c15411000750101c0013419403880e146204200d141c1070030740d118005441e18013089a20010300d200584d04030a4084d10354424079a0f61010850081003c0b524030f183c10381081c4d01e44011000f480390440c54030f0441101c0100e142d117680780b055034249030058100006074844241444941015003007902d4202e8164004104d05d5266614040c8500c03045a840c40c0ca61001c00015074022480409582c104801d424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 917792149 1250 917790899 917790931
    0x1515040302030f1615120506040e030a09060e012a0305130b280212131d0403030c031a06071412120604060311041d01050711070b1218121c05 62
    0x4009406c0e04030754085200002e507958006a40e40e107403600003100c1e01000c0000e5943c4c8000c202800b0740312009030301076140010341d04401c403d26035000f54154140e19804141d022400382d10061b003101041c0c190388e4100c003000014440441c14898400c40c0a002c1c0503288003043e102d580c280f240c1e0300c0025298407005071000c2000c20320254186c001c1040481d14111302602c0d030b40c0304244018043d04107280d41c80400e40c0344458042c02403001c60390318014050346c82070b07400340614034809500f1815122015469100034080300600301e400d1400a00400d0034a100d00909200a01c8143c94070341008041800310358004c0d8002611174100d0344141c0c1c003d0703011404840c200503913811078403406c0c1501c014000240c0150760b907014400961500c42004560510613000038005440d00ca0340c000c2034440030490094643c072481501080566032002a5101071441d614100126a1140101140e0f402016041c048601404030600c3c043c410300701c014905001c130300481701070a5048000e89400c840c80200000c1501c00b10301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 917793399 1250 917792149 917792189
    0x30b090a090c05060d02090619170f061210050c22122a0311030c040203090d030903140307090e07081302130f05010806040b06091515040302030f16 65
    0x1002e103040e2a015200992075000f0f18401800910810030002c1c0c0c0000e0110b066125003004e003000c2160140e942e5512210a82054040816030741c0503108202005641c0340010942e040c030400f0300594400c00011103a00343c0e189804041101c005a44140c0701c1c00c0001500801e060301c441441140c40e903140307103c001007840e02d05541c801e121500b000038003500381108280841105103e8120a1041d00b142501419961f440c2c054803801010340d801e07009000309548990380b40380602c2540c1c450032210000d0400110000d900300d0040c03d50076011828003040700440d030800405100510300c240e40c180c075200e00340b50400754404504003000380020b08118441d02080000001d9031400244540d06031511901c50050820a0b0007800001703900410592500c4000914036600296143c02207000d480e004030191508807d0100000084a07080e41d0300c0650010f00010742400528840704c40101070126081a88035400a0b08045e4038005442c100e40c8205005214078440c170454000401003d411501d04140c03170 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 917794649 1250 917793399 917793413
    0x1080607050f0d0507020f01060510080109021308030d0510150f081504090309030b1003030504170109170903010c111015030f030203031005090606070807020f030d030b090a09 77
    0x2015502000000b050600050810300300341c9100100c00340c0180182c3c600003c0003559100d07003070429034196090120000d02801c0c203000c8480d81c01015907900405070f007440c036494084d51200712030407141200340c88001034241301407020340780f04510380d507000c5001d05103000300060a0143e5000307100001c0b8189494082c081d00901500181e0350350b030402191a41c0c1e040d8400c01d4101c00ca014040e0014240313140c540815038000503000a83c0d100b01d91340d0669444594140c41948100e00006011800c10001801f000d0005403910603035440300c40002c80d0448450390340e1880ca4041d644540742074000071499101c07a107070a001d8050030303030b03158075000c0ca2080f094840503a64a82400c8113a402c10340c0e83c071410340044002d00304040503681129002c1c00d14401071070001c0d500d5000711004100121101c81c04207040c5000300545000d04002000e0307a040003100d80f50341880c0c0e840000103d0b400351046403030b5022610180204068008141c0300041d00814101c14800d0111000b070240f0110380c036205041001400d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 917795899 1250 917794649 917794651
    0x1103060106090504090c050307080d18050102030a110f0d12290d050a020619080109020406050d0c0c140d020c0609060d05060321030105010f03090c09050703020d050a0b041103010806 80
    0x3c110342c0030032442c1940c20314000a40305074000ba5014000c0b8840496441030009039a00c80d0b80b65940c035100714422081d2844218200c030300403540160020403256007460712031048882d408003102c0549003510440000e85261003100060030300412100048072228030428421950602800d0401c030036501260135040c2c034505d829511a82c031407a200d111a00502100300008400158050407450740e0f5803019000c105021070007040c000003e0b08100012a00c0c003018000c0c0d404945040c3c507118148000302c00000060b00202350140304100c151184034001c551451600d0184aa040c0c01910354003144190090070510350082e158042c00c01008040000d4a07120304640c40321178001c00024054a41c48002414082d03006000382260141d40c1a1041c90101c83d40198100c400c2601c50910165224400303506944000030007801c0711011080400c00003455401141d40482c0d1413070010703d0120400183c10844034161030404020796684100340d0320341403030310a084450b055a810f10341190314260b07000d662544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 917797149 1250 917795899 917795909
    0x609060f0336150a110403060207120908030a050a0e030d030c030608030909010512010605100206090d0c020603040b0604060b040b0304051009081c0f060621230606040302031504110306010609 84
    0x684400061800c010945c05640c20350000c5004c29651a40c909000010b03400682080d0744145150f1200d80c0740c01c1c058207400d022150848059800c220100d20299055000002000d01740710303144032501d06d15a020320035040050580e880000310604000c1c030040c1112400d03049642160301c100414081a6101e2607401e044039811510701442d0302039114114050300880e0300c0700f5003203918543c070021469004581c061080c200e44040340c11200c0d5600c401c40c2c40203620381c0080e4000c4000c0000c00c3c08a45020f450a40c82480608003081040d91900100c41c154019805128250790104c1440700b0044107110400c4031a0000c0740a005000c03054070744101c60302c20101e51040c0c00c0d500d0301c3c01100d0b00840c0d80004801800c6200b041014640c2c8401c0174005240400b800080e407995401d1042e00e040080c8100d000190344061100c1160bc24018880c100c1c02000d0035455001100340070000043c0d408110180d9048040045603000d03040034070f8001381c3c041c034015103140700c1c0d001000107000550784440b82d40221a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 917798399 1250 917797149 917797183
    0x1005010503101a0a12060e0613030e0d0804060201020d0e010204030320070308040b04140102010903020705011b02040501150212070b0f04060f09030503090c011704020609060f0336 79
    0x3d190200221205001003045030412440c020000d09501400200c648060294405001220441803102c0c3c07544802c90390380c60106004140140030a100b01c40d44008040003904c200e1031482940c4824045401550000d00180e40000700c140c482d800c140540c4001c4e400d40402581080e00b540da0140c1030482004146001d0060000c404c0a000e1080224a000319084202e10b50f803981c40d07065a000a44c0a0300a030012840d02d4030900045510511901400a41541c041c0205c50b040c4001142e41142808191701000344c0c0b41100300140e40c1e13910a080c001c141960303815a010040c12006401e00e074140200d1100c114050040d8800300d02d882e00641c2d40258540162407c80e84c407864058001d00e04185140c00d01c0c0d2800d421350080540003801107010b908544101c1d50700c400d102d4011180780c00c00c02030405148140802040040c01c101d8094245140020489400c2c08450400e04407590400c9070136030f1000c8e0300d05c0c02c150304490300101480f9034140c904011180d01c0f40080714a9130b032084400e0b581c0d0700d02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 917799649 1250 917798399 917798411
    0x282429130b0301081b010e010806130f020d02041a0f04061b060212060103061a04051203070f050c1302042d05030d08011a03040f03260f09100501050310 67
    0x62041600c0ca500640035407003400c0c0e225611030300200e664070031810030318100c44040d8500f10140d40c02200408108007050391030702d6260b5690401d203c0752211901001030050307110300b242d400c00d4241e40040c108441d003000c4016151454141c050710404289801c14110b80400c03c44c00e90080002011241580c80f90b052002c0e40c210583c1c49010009584030001d051a4804a080e0000712802500c0038052130099a05000454441201d00350312280c01481d500610810401004507042021181c0541c412800549040c840c0d0790701c90801d02213801808a4041c3c002442079001450101c03c148604030243d41d08600f444d082500300100b20310701c464420300d90945482c0c0034003081c40f1445c44201400b4040c0564400b181100c02c040c1c80da510070300540840450318640f00e036003c44640252485150031214286407000652000e40d4425903442072301c80c111aa02201004a00280203820b0007035520604003020342c68411400c60500300191002c800c0a8105001003000da03400040e98050901c503a1400580303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 917800899 1250 917799649 917799667
    0x6022a03072901080d0e030106151b080c2404150b0a0b0d0b13020a080103021c02041404050d02062a040e0906061206040b282429 57
    0xc07551034100241e4010a5503001184c0f803040810384500080b11078030750046141d01c0004060903200d00703002d2001d66032a41080b8031112031299448041d020610202d101002c141d0343c413044d40c6540700c11100301c0c4540c0021000480d0941400c00c15000e0365501600000a04059458031400d801000c4081041529141280d20079616242e0b04001012160071440d6180c03080c1e810b030809042c42454207489810300340c1400517500b0042c02110104080c542d181500c50b0300790b50800034444c005201d0400c480d40e50b03980c01c100503202c91181010102440e140d0000b81c5c68946003051401051450180854001105102291569105c404500044800400d021350f14989003110107018540c450b04002c0314100038032450200207c1d049000d001d088e24030284094291900302c1c1d4171f200a0b24024031000155000410702080015100c885112100d1440b08800c0203003104001e40b24000b007012401c148069a0300c400c0c003004d07d0b1120080144213a50b508090392141d45200392961800180d925150000d6072140f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 917802149 1250 917800899 917800943
    0x30f0f0e0906010e031b0a06091a0a2001020405040c0507051b030312040f110603071e09032901153606050408010f140a1e0906022a0307 60
    0x1100c58000b90403070b150070321b111900c0d1441161540c2c0060107161070b010007165480c030a4003840182d4040c1810306003160008445d480040d80000d00410400c0340c104e10307440c000215000f04001002095002584a0341032400308070803a18400c01d040700340b00c13081010b100003900100b00000c0c3d58181660307208070040c8007c0481e007948940c00d030fa1501c52200074100420000d400b00d0340c41804e40a00e01210000c50007005001c0c0c3c0e40b001f9078200011418410113812070300d102e10780c12180345105160a8541c075035603075503c0448803400c03a2081039070740c0c8910b1400803500301241020b004115103281103d01e45c4140801030840786a0402c90300e481c41c4403801900a41c1c00410b0107101c0700544114080703039199075a50051064004c3e000d0201c042d402d10340249419607040c00340700c4c421030344011425541c0d102c02540070010b082003820101b91000310816684200b6540c451411018014040942d892264800c242640801c444241402101a034000c1460030800401c3d107850540c003046841e14003883c0d070701c440b07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 917803399 1250 917802149 917802167
    0xc030506040b1b031e1b0705070e0a05090a171e09040c0302040b18040e030c032710120603080a0302040812070f03050c030c01060b0702041a091303090e070c030f0f0e090601 76
    0x20414003800180300e0704011000270b400b802c44010920007012525540c0080d810354205603031190035544000c0400001c2449980071010f00c481d4120b44070300c0c0103940709000042c0b40480401d010f1803400442d0403034160519008040000080d40380c03c510300350410340c0030560340c05a00c0c02003403824600340c51960359484503405030246001c0002201c2e140c440c0d548960381d41e9806a0002c0e01d9120342c190044c410100500803000c071080008000c101aa915003004481c4000b01c1d0024900740740d03c480300003011a4011006110044060b40c0241ea01c0707041c100d8951800b1071210821416080801c41000840d011150080500340e140c0f0300656100202100e4602d503001300030350045c4551030500d002840203200401028240e2080c2c400344222205081c0c2040354443d048902034001600384002200d603002101c8524100380700c2c1c105a9585510f41d9200404000d0855100b004501d07a860a14189900315962104007503891401c3c1c00220318102004124810358802240200c030603c020440781c1c1c1c00b644501c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 917804649 1250 917803399 917803441
    0xc0221090325030516030b0604020901170106032c1203100b03072d02070e0a02160c05120313050d02120105071d0604050d0803040c030506040b1b031e 66
    0x15184002040c1c82501e0140a40f20450b840c0c421031841140140f404021002101e8105041204695034841480003940c4032808845c104920383e441804199206520180079148507a40021100c050310301006128000074541c1400403225641883c00c0703000056400b9441c202d1307030301140d120f882e8119802c0354050241c1250000520100c20441010350200100c0000300c201800c02140010402c2142022a480c00307501c0d00507000300d0781c18814040c0e0a460079810241151006240c0801e2014641c0014106d550031110020f80000810403860007409070a03a0b00450000b440c80c4c030003c0496a051190184a154000c02d9100611000c0d9510440012404070100b8002e018514095100070014107000d403003000c1c0c0000f103842d4000c903810030390f003600e041d0707000503241e0343d2540c03850345900e03503541c200800c200c174440c140410210000380f00323200c03003070040d0311814899240c0d0511460304e00b603100c010822100c6145081c4204142080d211416820080c4040e07000e20150b1154282d141a0901e00c07555 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 917805755 1106 917804649 917804683
    0xe0d0305060f0307060309110f0d11010207090203270601050a050f061303080c0f06060603011502010f0216060609110702060313150203010302040c02210903 69
    0x20035904040700600115811040a0001e450200c554201c440000d8880c0441800c1140d0844250314010084401c403a0401c0000049003261021842c09070000c1d0600f800c82486074001d109900107050340020541d903a291200b0b40c1c00c4034120840c0088140f00806551540121001c03030700078142c1d1402001507040e40c1c81c0c0b01c20031000803c81c14074954403540801011410a100c4880d034002544035411a0b52541c142402d07140c201108100f407031480da04814104005591807008980c10f5483e0f800b12050700d901000c00803801881580206409a44001422807510010740c040c260814410034080c17020310f40f03c1ca240c50985404182c006003400040c8100c800620708000550b5211652600d0100007810345d480c0c00780050009201c003110303140d000005009600346401016804011400100301d44124241402c40a520350141c0c07246500001c903081d11107a07018428032210f00c0210344 = true := by decide +kernel

theorem cover : BRFrame.Cov 917625899 917805755 := by
  have h0 := BRFrame.cov_init 917625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 917625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 917625899 ≤ n) (h2 : n < 917805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
