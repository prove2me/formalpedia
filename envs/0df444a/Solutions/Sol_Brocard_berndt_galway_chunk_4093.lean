-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:03.420864+00:00
-- url     : https://prove2.me/submissions/584710a9-4087-4ecf-8059-7d9f44f8205d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735971223 ≤ n < 736151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735972473 1250 735971223 735971311
    0xb10090f090f1203140112021914011d060d06030c08030705061305071203020a15020f1905040b0d0f0e0c031011090a03030810060e030c010302070f0803 67
    0x180c0c0780d0303075224000180010318122001c3c0e902c05281d0300c40e0b0418560348011500010f03065039107407445002c0901c03108049000b2070b03a806204404240940c40c0c0c4003141c4c025140d61144074100401140d6074821080915003150a074903005199450307000281401503038409001a10a04504001644607010341c0005100e6008100031f000040740452400d400108038140c03415001454030340941081c07020b0b000611076880da031104c1c01c10315500040c0204c01501518020110354010020304060f031094281d0342465680030003080c041d44501480300ca401e12450b00c0c0460901d501c0d4204281164000e03000c0d20642500c0301c0542e02855003911403a025911914010041001d0a202007521407802420b0442070b10f927149030f20b0070b80d1886501121041c0c1001029808065124940a0002e40040c0da900e0105e45000401041c1c2500406981c407200c1e000034020100c80c003585004601030351107400c3c2203800c9104000b00800250074500658011008042010b890002d61803a800c0001c1c44007081c2d140301410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735973723 1250 735972473 735972491
    0xa0503041502130311180c120a0b060a05030a0f06090b0306010e01140915061b0d080601140903070302030703030e01080f0609161709010b01090b191b0b10090f 70
    0x110100700400c07254480c0707010721004117020000d890722003a00121207103a42e02c0703020002190581c05c02403034800352485500b0016190b40d904141160210320b17a00350850020440c0c0c0480034003603005958841420080070440074100d029180a0b10610b43c054441603490f031811840d50300e01401201d014148280b03ca2100e0b6141500301d03e20302600031481c40c0240240300101e000c0c0150203400f0f07140c1c2403025000d035176140c582a18035600c0203144007800c0d40d0707400b80045921095110300d18860080303005039a402020000c00481c600180d00070302e41d40790305124640000006131414410100114025100e00d52201118000500078100003008248071481100420031301e0342d03070139800c96003002401400d050340141103401a40d1041550349800e1551401e6030401240f110150041c02c1d8181c401e0b61343e901010740c0c9a5201500d401801143c030081c102c0c58040300c0009101e040b4020140d0008030f20100040450380391004400d0702900e9000c50002101401d1140781418040c81e5294542c5070300401140003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735974973 1250 735973723 735973747
    0x91b091103150402070807050111040311030f1222030501020415020601030302100504020609040510090f272303030106091a07171c050a050606030702060411060f0a0503041502 77
    0x181100e00c0f486658081401c030240007400080d0350216620100801809114a02c032800a800c517104c11281c44c01820780d4444c2900f00440c3c04201840003400901c41d18002c601c0380302d41c50700281e0782140e80420511500310021820b120b00e0005500601c00141d44a040c24071910001c405a00081c043d03500900040002903400604103244124080000031309488910000741284034441d00310b9072150901c01440807148000c0c194008549a10000300034020501c6c844c038043d103400306409002400e81c0100c0110348002c507a810003041e0b100e0903d5002c880c01d070b00301900c0b5054200a4480700c550021005118150300540e50710007034a110312040c4988050783c20011a076100d201801000701d2045c41c501200801444c060307807035220a03a480e58510001105140307009180884048450a0400b004a800c1e401c14a00302d03401942c2550107000c0070b1f65291141c1d400c0341840d141d4146c00c01c4c000c11040b50741c81d6501000d824540003964900340c0e607041038104100c401d1042107269050500c100003000340b9027 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735976223 1250 735974973 735975001
    0x22203080a030c1418030c090c07020607020a1d010f0e0c0403060f06080316051005041a180d11060618070e01090f0305010209010908012d091b091103 66
    0x303082d10700440c8108948204885501c000c442d0032410020200355100490140d01d0b2010034003000741e0450b80554085802c0000c0b00c941a28030b084558070402c606805810240010b114242c00904100d5032241e6070402a06c2c582440b901034000949148011700041c2c0001c030803d0018402d052070f101c041e0415039030100591080348001081c05607500d000800c2540300c1e801410003042040156501e130000e41d105030b070440442000440e540d0040c0b040c0c50161540c1c44c4105400b407500261492035100d0310140405c540c510142005407200300c3d25100100c1d0074020801500c0c03901d4203583c0c60702040c1040001903d80f0b40b000d089180b1034030796054a14103201808242541c0a803592030004052620500143c450328940e8000c14030402000c0004014000c2c15001006031220a81c2d400130703520740d40c80030700b400c0b038900580d503918000e900881004c2c51000586403140e05c59a18400080c0600ca550304c8506d0110b8814a4501d140305d110020400707160b49100700c52000c0020318100d0318615098603402449 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735977473 1250 735976223 735976237
    0x30c0607050702030a020d35040e0c040902030130030206040201180504060305011a0a03050d0f0e040e1e0c010e0d1b0602030319060b1e130902220308 66
    0x1c80d0204003201595010424a036125801030491007440986080c20000180580c81c160103090b03070b04510398402d03441c3c203d074042101c204a1115040c503062140705840c0f0307403004c1d0030f44446803000c1c00041400300341ea100850080818400b941e982503200307082403244566041001c00c40452114220000c283c010070019803190742440c001c07407001c0d07440f040c51b9070015454112a03081403074840084100841544513440c694400603040303411040c084200304609000c1e010080158211030074003503005e03004075600e2541c0500d50601545945070390012030101d81e00c40400c04400d03800200b4007000010f0381c0c00030420340014000602626a929400a0061740d40104460301030b844466401c0240300d02c2a8005219a0403500000c1e200f580d1000000d599070819100c2d441c440190407405e0142d10300f5442017000719100500001c2c10482210a040c070784001018a420720103008109101d440c40460220f000686024240180c81c0c0b5401000c002114410180c2141320001c11401440891078201c00d94100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735978723 1250 735977473 735977477
    0xf0305010f0b07110102071205010501080105010e0403020d03020d022b0501060e030304030b0613050429010e0a0207060f15060905180103080a050712080703140c04140a1d0612030c0607 81
    0x1550030711310040380303025444d50140901c81d0342c22001300c04000041d04a94100c1d0b07100002400140d0300e84c84009011007054a004015901013021048114042c2c0c0240c804009900710050526502603046610501c0039802c0d0080540821075802101d0711610841d80980010f203010110040c0c2c0b180825664400c500000d4549005000041d5059490703a07542c000c02c140c2c01d0803d008604052801070081c03100580e503140c0580351308621001071000030014904072400e5040e101d2480c0c070ba201d47c900c0298041d107416034901e51203d1020250300b03c1405540014518440c039000c2103403400704018104030b02504054031840940c1c2d0103100350b605c44060141966081b480c40d540ea980c1c2e011050703078036203d128401072140c1c03e0b0303a83d1034050a81000c003c03446084d0544060011004c0d840f00700101080807036902c440400b00b40000c5c40500b07402c07041114084005050305801c0c80c3c40d00e013400c103041c0500e01d03100720f82c1000c601000000d061504500890880201c025401d21242440e4152141401807132581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735979973 1250 735978723 735978743
    0x91505150d08090414250207050405090f0f0c0f0307030807080a110708031b0307020d1403040806090609010b1903020d020a120b0a1508060402040e0115060f0305010f0b07 75
    0xd200042c41154960003004104001d0440101800f80c04801704039251400c030308150301400490b410f5640200403c00f140ea0152603610f043c2802c200017410301408040862185000118080700200036107191031281c5401440000b84110130440e0383d095a0148a000340c00551040000800700b10944000710b5000e10308079181d00382d40300200d8868241c0030008002d031280640025030440084000d05400851660aa140c07005c107010b0b5a54a1040c0d500094009007071312100c4002ca150346610b241c2120740c2e0001d4a00e00b603941c401892610806036501e10365070b0030250600412200034850f402d1400401c3d40c4826060310440e8410944122903c0040c0c0980f81c200701a808642e200c90418001d4420980c081901582d84d0a0585610000321840c0c50014a040f582d05082c90607648104111001d00008010a03074555080c040505080c05c10400d036992036156510b00130180c1d501040c0540710701e40c0c55428558903480b0041c217840d0182e200000048820409115011502086070b21454200c98011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735981223 1250 735979973 735979999
    0x10b0f120c0c0d090e1005060a12020f04060e0901050442060c0b0603010b2103090a060503100911190207031b0806010806060105030412030902100309150515 69
    0xa01140310b064040801c0c1d01510241101c26a0007403440c1e02698a4461861280c0e681d619141d51104818000c0030780c802030512401002d2441001c2958400c881024058148011a40d2071440d5800603001100416600b5684030b4003030401a441c42d00400b41240e080c030444003804000054501c840da03e1200140b88202451401105948100c1c40d01044052061500350381d84d9005000c600c441504985100e800e0001c1340161070140030706000d11000400c044180c403840c80e01c010401200780907002d0302d808207000300d01450740ca001b4544e0041240342c48061780c03440d005000c400c01c06202c2e080110741342e00c1c017010780402c1d016035019680c22081607403d8003014481c8900603407401c100c5074401000389407240d03c20685004008100421501070074101c5007266200c2c0401d5488500460300140001d9080c8006404140307006002c00308007241d4100052890940e402140200c0301c000d503000040b0341c0f54928102000075070602c1d0311114481d910200124140002108008000030919034450744030980c607c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735982473 1250 735981223 735981241
    0x3090901120f15020a0e0315011214060403090501080a0c020c150c0d0e0a090b060702060f0c070e04030f080412080a11040906030302010612081e042705010b0f12 71
    0x803200d07681c02943d04000d034154000030354041e51101002c1030000701c005070b01a50320300700080c40e190b03120240020440d03160709000d0b0000300c0c1d100081c07040ea044004e0750a581c055600c00e11001e40928040d50310345203420706100001d070000d600540400c0d6881e1070000000102035003c03803009007124003103922030a5004014000c40c114050400a10244d01540c0f220030201c41d000540c036080d0400980f8600d0f449a500c0a004044400702e0384206c0e0014070410041c001894503200070100c1000c1000e0003400c04c0d800e820b4041c03038560690090085281540c06020500d50001100c1d0404c1a142c903201c03426251030366500701031203202502d200511403030300041055940b058011194840c01c010609440315074070000343e0f028081521080d00594601705000c91050070103070607080800c1d000300c030141c0307440188120070080179a0110710400010041c00089680c0010107954130382c0312039142c0b50443c4070750b10b00d20400446406900102c415031040011900504460007070f80c1c2d200382c07040043d85280c0d41d48440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735983723 1250 735982473 735982493
    0x51e04080a0f0c06020309010e0c0103090302060604050c0c0609060703060b030c0a0809010609150f06020601150e031005040803060f1e040e070b0a0203120601030903120905010f0e0102090405090309090112 90
    0x20013840301e4004410080301001c1540b142c0c0509120404131b80001f0310700740040d03045521983d800360058200790700040590600b80c00c959000b0040001691504610110007814118113a4016569811003401c3c46074041d0b041c01000090407103401054a941014a4054100d02c40c09001c03a09009049001880145007907201d18014800d00740f0900c03506030a1060814481840c1c0126204549440004030b070541c4001140e074143c611500c1c4401c2c01201c05d680035030740030100c0c4641c99030510648800d80c4500b10207000302070145124491107512418080c041200704140a52242d0265060400d001c8030030382c004920b20981072080c0e400081e009041190303142001100d400412440c803001580b941c0b0294004014000c00190000da6080c1e92520001142aaa80c0f44070240c0020280a400d0050149650040b60040c1c4a900001041042c001403203040d030781b10f40654400c1b03960210354506a81401d0103600c0e0300c203864202440c41d2140e80c0780081c89070b1b101806181d507240480200e40080242c414a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735984973 1250 735983723 735983747
    0x30b0a2402061003121b060c120b090403050a031a09161815050307021e0d0f0e0603041b0e090616050307020a1e060906051e04080a0f 59
    0xc01100c0c4100e11106405242a80e45a520041c4a0180001c01c1190401555000d580c0c0c0403611000251201d071046400949605400e16169510000c203000203080741300d04c15000e002515000c480200110640040312102081e0751700074041d0314200b000003580001145c440640c107040c0040d111240c00d8100030700c003098034002600b281c007031070500c84601c490380c0d03014142d01c204c1c0d5111202c0840000014030032007440e105501d00d2101c807170f4081c12268080d20145d50305c180d840c412207100201c0c2052560129280051040c4190400d682e045095640119100780c0b1464500300600e02940345801300342d00d484010b0018001881d07043c001a40180104034040040c0801c01101050b0300340001c800340c6500c42510b080f629205103551102041e800381043d6445165190050805140151030b00007903088504105650302c081d42c0707030708000181c1500c40e02e0002c074020a00001c0c41c1ca845604d00c0c00c0404900c0070055007032040010000090f480c5411100d099003589030540c0a2210010305035103a1540c06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735986223 1250 735984973 735984989
    0x6140717070204200307030b2e020601060212030a0c030e1509190b0601030c0201180614130c1203050d110c0c06090a030b04050f0a030801060e060a0f030b0a 69
    0x240c0005810040328000e01031550080b6000c001c503d0092020360321000e2a071a000c28082000d10004011600036070125101c4807024020030130010041c283d20564010714120804245072410b50f039090980c0c1000709601501d0540000c2a1000020044d000d090000902c0701d8161500e03210314000c041d121741c2103640080c1c10138046800f205200d0b03010040c08203007107805d00ca2070300c60301550080d0000040d4030b2049680d0001c8041109498520044000c5c2c8059100341c0255900d42841203500c062240340d44c0391481c0075160008014401120403290744101130711b44441480841c14410119400902c12400c0310f80d022042c0f07486010074030301035503140120591559524902041c580111340854000c11480780307003030148d030b1103103c0d564104100c80c0201c40e001504480ca1020038400501010344041e009402132040303401c120040f042540c07801c80e007440e00700e0020700780310010800981c0110884075408011201c680c1840790012000b031400b0407524445003010b86030b425503501030700e400011b0409072035a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735987473 1250 735986223 735986243
    0xf0b1017060607080a1e0806090f0411060c030702030c0a0503070b0318010f022508040902210403090f0819060203150409081804020306091611060f0708010506030f01061407 76
    0x200f1000b41c03010548181c605c00303030f046e104003545880780305045a5220321030080c130703000040d12035035001c2516400c02801100c51441c9200d6410a0750303503410182000c56182d01c001d5584011601c1454106801c0d0b440d040d0040b6032184080c8101d030782c007081001c141c40001035910b0700c0b0b0340e84541d41000203a2051155006501c0c002100b0a0b070185500102401401000c0c3d0b0800c00745035900d65003540ca0035034000341c01008140000c3c4805042174006225280310300c201d0400030580f00341000e40000090740c0031804076010340d0003000581101000780c1c00070000800035208520788510791082480850000a00c1d082e400030018001100401600c80c100074058000c10400a052034500321603030251424180100c1441c550f44440d24142c02224450100541010b0b16034440602c1c08840313166180c0e1000030310001c0700480309190303020068a8401ca840500c0148a401d0a4002a121400680105001d45010010490350070052200c0c0380c110b4000d440d0001c040303070f41c05000d045039003c1c40c0001884118a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735988723 1250 735987473 735987487
    0x103120203130e040c0b0a08010302310207020301060f12030818150103030219030e0d0228030201030c05120f100902070602091003091208060604030b0a0f0b101706060708 75
    0x43c18280c0c0348034a100380e0040201548540c4d00e070205005006200c030000340b00b10014001410070741c24881ca1880d40790190307905000081d01c510703415030b0b9a410441000364041584400c0d860f090150200400c0c10a9902903ca41805071200c0c3c0e0a0407000e01034184000040810781c003c08144444010f00e0503402614081400e800540004030400e00c0181c00502c5445454400845401d009035840795040c2c69085070f00c0008000c2c000b21a03c610810f0f88e10903100c0080f0380d0811000c40742c080e85101c20803992007000e070540c0b002404030780450900e90b080220500c000105c070084203840541003c501c1c041c404150781d13a40b00c140584441a007209040c01c1c00820340a0070000690060119480700329442c0d1440c1d16200c1c4100e045074100403010b0a101c1c3d80c04030180c0020701411083d0f0b086403010388411300d800d4480d190a139428006a031801e81417541c402058400b9481c034441c180c640141100c03100b8400340f46030401014101418441c4040c1c95070350000c50040d0707588030b0440e00140c0d8082041501c4202d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735989973 1250 735988723 735988739
    0x8091801060f02150c22050303030c1c06050d060e070302030f010b0a051f0f020102070c03030e1003090c050f030a020a090603140a26400509010312020313 68
    0x2040201c50026100701500b9050501181000e0392251380096030060802c403000c140815061035401300f040c08103101220121f61620b041c001148161006d030b46881d600e040030109450a4040300656030541403030301905000c10b5840240300701031030340c20500200304070b090140e60074140304180e0f0009506110740c0d01c5482804078190416003010204482ca4400311399503000740100c80703408640c41c2d18002554184414120f006d03404904501c41d2070301c00141030040d030b580c2d02240356245400c1076002c5900c6400c03054a86c80c0c10b14810302c20250341e241c03c2c000e125103a65401c601507401d00840d4480c080701c2403a01300c030761010000d0000c126002403c01c8401030340c1b0a5541c0082c06640025100c0c2400c04180001c0c0010008207a580c041d44602c08604150a00078031076000c6550008000d1031010401c0306002e0400c41e500d000071004840d2145c60704409000c07641c80d200680c040f40041200d034a00a007041190350b0f050350a0304403a002508180c5600302d0307850890071481444251000f010340d80001107001d80f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735991223 1250 735989973 735989987
    0x405100e040c09080714030a060225052a030a0b090a0b0f090c01020f031e040306020d0506010f020106030213020f0c070b0d1512120504211e0b01030809180106 70
    0x2d205207065914175620341c0ea0302d030308046405403081e4141e400058104001203140e40200500c1c0c4205008060075440100c035004140f11011060342e85500c80d40d01d40c240865100b40036154121494418a6001da00320046611604401c602038080d030040c000082845406009580d0a140d20421821103450002641c004040c016241e4161510075030280b01c40d503500029584c061160300d08000c0d8204810780d0303191000c504042c1c40180080400b4800007001402c103001a04691030100408543d81c540100014800c4203800000c40071681050780420160f01c84401e5000941d010b010b001d6550b2101c07842e080006c3c8a08207040100744541080066051644c0e0040c0003180d180341400d01200b555001100c22045a9000b180c0d02e03010105002d0000411a00016400e55100d09040342419552001c2e8a1801400c0d54400b2803066100803080030007055582158126420030705401c5440c2186e10b900d011014140001801c0c0341b4001445895640c0340d060440c0c0d81e851000341c4020540e12500010401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735992473 1250 735991223 735991229
    0xb030307060e01060b030f0103080a12050c030a050603060601140c0118050307030f0801151d100c0b0c040f0512010b0409060605011101060537080f1509030405100e040c09 75
    0x40d40381c0b41020403011003500c200c9020305d4840c01c0a0003582d0279a03d86c010640c0c0400101000c0c40000080e49840024030b00032944500f00d2146c4060b20307490995109010385000070080707403003038100004003c0c90761382000b034103055086035401c83c43c2c5030302600460034010715241806e40000c2015544403c01c000c00040140810703403081c5d41d0309194076155002921000300070b0003400c1300400204490300803144103801e04190003030003500e002507400b031b40300124403640580d00550001400030101c1d203062004645100d03411a8065003041d1421b45010280c1c050300d0f6003406400c1c400c124400c9042c0107440c00350002c1d610554024407c000c01c10071407a00f100281030f540301e210302240c40f5aa00e40c028900c18825001180e00203885048070304101e18401c02008003801000400e90239808070500c0c0740310300e90448006131581000414100c92071140251a010590740c080e400b95000508000241c500402074038100c80090320311030a0417203100c4095a5584903000c0f003a8000b0b00d410b10040d1169442030600d021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735993723 1250 735992473 735992501
    0x50a0f0918061e03020a03030302071a0a0c0e010e0901091509240801021c051b0f07031119032613060c030c020c090a0b101d010f0f120b03030706 64
    0x8000f208442000b081c800c180310180d8400000481040440d00035001000c40c140301d050214160200f02c070041c01001819100002c502e40e9400d0840d01c121381201d10b031001348609003001040c1d0400440002c42e2450f0500800806607100d0410030408505240380c100649084001070040443d0318403c001458442e28660204020110300010700e0034040c1b0807aa61441d0542e159900c000c6c0901c2c020002d444043e000c440341c081031050703034030900420303001800c9003070f440400c01e03980e030320741414024201e040720b601c1da102940006815029004405000d4030700d465140c103122101c01a2405000300d1101100f4075920041004010003c240003e91102d412080c0b0810080110700c072804000c5089411101c444001f61b0300c5105100617038508100c0c0c140e4012840107001c51482040004528030302d110041034408204007a00c100c4880340c1e034400c4131040301420705c0d06040f031200a00c802071180f12401d00e44402e00c8201d141c80003403090580c00c0070540c58406012203640c0d8205251020091400400303c2c0a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735994973 1250 735993723 735993749
    0x705011803080d06083a05121911070203060106050c0a0609020303130618080f120c240703050108010b130216050607090305150c04152303011d040201050a0f091806 72
    0x10107050301d01451201b121079450368207040c85548100f040d9480a03060f10649100d441d48402e140c00d060040d20a081d13601070403162100450302c141890310380103070014414000c042c0541021b080000441030111034020f80701250051290000c241540704220806e41180d80340180490842d401c542c16004449100d0174019507030f95030f882242d45800c0c822003030f403a49805c580c40440031420700701c0107450340a201c281515034804040d42280760102902c040300c09808480400c000900b90903105241c0140b992000134800c2c90302d10b4001034180780890541340100d55002c0358490302d03000c0c0d50650202c030541c00001c8582c0c60401c100040e016101900c0300300c030b1900c00c400c41c06581e00c0c841501c890042401c0344086042c41d00b012010181054038680c4002000100103401d1002c00300541012000102d100c4074503034035414010301a0340c0310320421a28450100344828440180da011044504121083c81c1c00f59030348030510302c102c41e03644050340305043e120343c44412400151250b03032260048460110f81c0403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735996223 1250 735994973 735995053
    0x1a0901110606330c010c1b030f05030c0702040c08061e0d0b06130f0b0f0913021908340b1204080d1a01020705011803080d0608 56
    0x1d56404048a003160408080c07107400d00180c0012403584110300c0b00300d01c0441d2814840a03001d1441d004546201d20b1a034603030b424013030040e0708080c0445001c010035035801c4a0903201c0e02e002d0041c04d050482c220812000100042090400c0002c0d00d03c8194020014000000c403003000a003030a0081d9101132007031814000507460041021214444140e025044030850b805c01d407190210394000070000d036040101e14000c02c490381000d02c91241201c07034a20000954680080500014114070a0f01c03a00450f003040501c290800c4008881350519030482e0354484100e1240400e581b525550340c80302590703119141504100103841504a454141c503088514400d448203100700741f4042c2e4034072803000b00e604100000d0303880215034100980e01c103014519030307450042810850000c49103054a80b206000a151481c0a40d40e81803101d03500a00003407801041d40241c1c403001000d6034a103844020b10900c1c1c00608084a06004e82000c0e00404004040d1a00100b20740b0071a403442d05104201340002070b210040c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735997473 1250 735996223 735996257
    0xc030c09181504140a050705090a150e06030f13240221041a060604170f0f0106261c0c0b0708011a0c0c0303030106020d1202070515040c1a0901 63
    0x30503103690203c160135102c0c0ca902c07081c000146000ba01c1c41e010448100700c80940307034503000c0420009001fa10303140c078828a03013444014901e100402ca90743c496201041030011004411090541101100000c42e44000b000d01d1300100c1c078004034030502c50341c04440741911200005640a0400d01095107003902c414407881d116200c0402040303d0040030300c00d61840603011185242c808680c815000f910030f61500c0e07111441c4d5181907050b160b8885107540140828482482c090000d0500da00403140244001d40c00e214910484c02e00c0d1070510030031480451009030f0002800c01990a0703070f25402e280240303a04150700004001000100d8103640f515603040104016900c43d0320740d14100c4984c0c06080426172810300c010b000b1a03101c88464149403040700201c0c061540c0500095008001c00c0d0001c1410120521000e4040c28240d048244d02034418040310011500210b00514107006000c0c0d41c020315a11442c1414508140d60060b2210f0100f030024103501c041c600c4000c08960100f622160202c1004c0c943c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735998723 1250 735997473 735997481
    0x21090f030c03080a050403080403060204080c0301090b07181a0301080d050a050313050a1203051009060807060c1a0108150a090c3b100b0406080c030c09181504 70
    0x742a600e041c1c00420115110b00b0162200c1c00c91031810b42e1605590b0744404002e83c00c02c5c2c00650b5040d50016080041d00410003010425081c198000c2c000c0d610319448040764400c0040c400820f105059600759160681c0c070604501400c85000c02201400207280741c1c49094009003d841036911690303a48050040c068801d59811541c035030b89962859443d01d42030600c6056220007241c0a20440c40074000040c0311700b41c00740f6510702664001a0302c1c41c01500c108007a8501d43e106802aa2404405200250300418808183ca445060440e0000c0c07241c9840d0304450911901140d241c041c07900042801d034800300d159075012480003c5081c2d261500420f001c00c4a1503500d0041c1348402440c010030600c000c044001045c0300e480c1605002051024400c0d1800001080180c5080c400c1841003082c0414552002c40150011105003410030381800e20150204070701407d010001e54002c0005622020810100c0344070040282c80c0117813505282036600141d500c103684051243c110399808080030b0401d88a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735999973 1250 735998723 735998729
    0x619020c0306040c05010e0105090301180c120302070e070e09010e1b0901080a09050f0a0b0906011a032a1207170c0a03090f1703090606040b010c06051321090f 70
    0x69075181c001c1c40c0100540e041503001d0887d03418080c0034400511a41e03000e01c00c08041d5960000702d41c04c8010f491500b01080386054004124184403060310002199000414030b0659005032454003c0d900c80800c02d64501840e9444c1507800300802e0004556001c01e60307102c9024062400310584000d14161502d5868000c0d8911680020a0080013030802c081c1d42c2c0061980d0340c081ea0030b41c0d203004500b418450404c0510003059414207840000e10400e40c204008050040c5003403000419403000d803403580c00701480082c21641030900d16400c0500002e421007218090401d101c440a5034a890b03132040f0aa003084111500000310380d45050b40901211140f24103849004c006400c5803602ea4040c80a400802441100b620703411501d40060307000409407030000c0f000300b0b610030b0040c1c1c03286400301088c1d2804200821042c012070504603850b9107642c00107681b2001a910000109a50380d41824200c441d5445441c05440d13200500151440d0050803a0b00b2240b100c076a031781d803e000c2c1e52a082d41405a900701c0c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736001223 1250 735999973 735999983
    0x20d02010902100507140105010b0a0212180d06020c0303010306140604090506072001051015140d0c0e0907050904060b07050714030f030c031c05091002030a0b0619020c030604 77
    0xa00a0f5140d51155006003000c81c03280c03551280d4201d10014050845000741c1007181d0b07407900003e00c4a9000d4040240d001c445200c1c0b40b640b8506141a4582c2c2e041030a0342541600038455082030701304101d001d0301945d1194001408070b81c1c0300d41c0e6a0a00e0030182020382c1040d410885000c02040f001d04050082144441e0000c4c0108810344540404950034040c2d401d00c403540704a05204d40a16500a018440c014424001d040000c81c0c00c160420503801c805019400604c42e5800e400310031030003801c05403031502d1134140d400282030860804c00c0d01d8030745d40c8208407a0300c10520001c20007020382060207003150358816542004001d07218030790341060b403207001c10140c010341c0310501c1001200100d424a0302911130103401c3c2d840b800b1305080903e00d160046e42c40a511380c0c01c0402c04c0320312001c100c01960b040b2103240c0c000b4016400c0500702191544240c06c9884046d540001c005a071080c00d5801050084c01d01410036580c030101c400c9015005807030b030080600140540d003c50702c0302e8030700055110701030350300302c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736002473 1250 736001223 736001239
    0x4110c070e0a2703080c040807031221050f0901060303050f0a030e0a0c080d0e0609090a021e04050411030c0a110705060304061a0411041404020706090302030a020d02010902 76
    0x40405100304001c000e00312407031580c5401c640c89000a0307040c1002000b541d4003103201010080ca14001d02401317001406c00a41c80c4041c0400c10900b0000600101100d810460480b10540b20860448426200301d18580341c000540740a00d212184590041d4450303420340009815075101c039081c0c41d0981d4554070000d030010b4414081038030010900c8009101800c5103080024001420700031190400e5015481640d405054038020060b0360000e02590309980083c0c0f910f00404000c900005040c5d01a0760511805050840002001051541d04803041c88011202c001c00d51100048203034000d6010780200b42c02079080c602c85900b8511494152400b5500b01c41c025410840048012103000021034020703c001c0c0300d442c030001916201c010086001d1030080c00045100c0343c240b04903014142910310168000c40c54502042104041201a5400e46074203900216034070ae061000500031740143e0310302412003480c1031056002c05400000400500c10603030240d4810f103131281c1c401e03801c94842d1311000c0c0d008858 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736003723 1250 736002473 736002479
    0x10c0303050c0c06010e09060906040201080a150f0b0703020f0a0201201c0806030c01020f07061209021c17210a020d0c021b04020f1209101a04110c07 66
    0x303504402e80c0029458040390620140c00798140c507021086e440f401d00350010000303000301c007a41400b99030361001203000140290304059000030142007000b44004003003a0741d6000000e61a03482d02c4904000c180704c1c001c802e005a25086040080c5d4400a800ca0240c400c4850150340c0301d0001c903101d482540c05840d032441071045401200315800c01003051020500500074007a5210080f0700071708a500c0b9060703858001c1480c1ca03406162809001c0f0b003102d03040d507004131000300d0b203035000240040584660340340210840d1940c0d100c1c8805440300c50402540f00042e02500f003120b40c05400410300d000e00510414605010320340c24608544208121210910244005602d100110880c4070b90007602c0203800620b004004040401201e80c02a08000140c0140720180c0001c3c000403c050b030b00e05000c450441c0b4104034481111058401c1f880b124184410000c0003415455040c4041b2170900816541401b040070000f010b108400a070444080c4241d00c1d04040354070b8901c15000752091220700c00020100541 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736004973 1250 736003723 736003727
    0x3081e090c060906070506040305090f01110c100c080c0d0314090c091003021305010e06010212030610050405060d02040e070903080a0c0c18020c06092a06070c0b0c0714010c03 77
    0x40801c40c01e0344c00500030028100001d2003040300314400d6000340d0b221911890654100004586c6400c1514104803001003880541440458003500c0d80d042268a20350000f01014142c2e21031002c02000303030070030030081203140803484003150001d44801e0565042042402d20051284080d41c1510a92070b43c1e07020b40c41e00c00c030354204024115080301c408004012616529400201d17440c0b016400f035401a03845000400c0410f84041c10280c00800c00d0000d08904a07107408122410300000301098401c2005110f4800000d0198040300e015043c050112540c4640307014940d00a0340c07041c03213140d502c801c0c81300000d00d0040c442c00b40302c8107070380c0d000140c3d520305641074a04403030110b104441034aa17045c5030940000d01e00f100482030000c9d402913a0003d6182c00380c2d0b4840c0c40c00e2120080c100c00c556000000109441e10482c0c0c410004010740703002005c0400d540402007130a174056803030024810461750728049080e0140c400900661020710341100c18140d11031080741010360b008202d0314041a0f0600d0b120001134 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736006223 1250 736004973 736004977
    0x1a09010c1b03050d0c0203070b0a0c0c152a09120c0e331e030c092220040c0503010501050c01022808090307020a17010e070303081e090c06 61
    0xb4040d150203410184201290350480f5901290b92001d13034800260703c000c200004115075070043d004070082015481d00c8070090700c09900000700030410b84105400021200441e8001d03918901c0e41928011404000c1e09016240f0140341c02c40d80210b060741d03d00042e075506040c0e94201182d4808002c1002e1480d01120045080000e4039140303081008003601d140c210425640f000001c001140030f41d100c0d100d5076061001040540142c80100111201030508a8500080740c00f0110b5041c1e40b401c001366141c007003083e41041e05520014a054030f91203410113000e41403ea00b603940d1001c8005d03000c0c0c000201c08101c11600c620000304003254044c0010086580a00d01a0002e0b121400c009450301105142180030034110120f4248110484508110516801110903500c0340210005500d04940740d00041c0c00c03400e442c49146004c00244103982116002034004240b54a825000c49441c2901c034940a040d080045808520101c861440400a40034030000c450007960010090b00480c1030300c0c001c2c0203040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736007473 1250 736006223 736006277
    0x1802180105032208130b0f04290d0f06090c080411120102190f05130e040309091b08060a060c11031c0306051806090609060a0801091a09010c 62
    0x40030443e548446600b07034400701e4840901c1148115560074241281109002058000500e1107a0034406c115644240b4800c407425904103c20854185480c13100c86045140300d92001415410007282c1e400c90780c0c01d2380c2c02a9096400c5c0039004e0284c1c0740c80380c1218040341c1110012400007805840400e01080b0002c01c80001c844026003030000003581c0c2101c80342680c1c815501001c000028200302062075600515208810072146031103403a020f005c102045c0381d040c1c2070183c03118001c0d4110114042500640c608402026055400c4c07080c000d001000403c2c0c1025a140c08000c00d2a400024550b8941010390000791103954540c68011851500c81880034240840071981510460703441c080c03081701480d84004940c6403070382c020400a0801003807100d0403800c0c1d040c0400785030006040c0507050752042851588810299040f9100340e5480000a04c20b02e0180e01000c8a5440d041403101030001c002624160a04418036500064445c40401800c840c0c02500400c0010206030303000c0f21107000c00000e1004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736008723 1250 736007473 736007491
    0xb04050726060c0703300c0c1e030903080d09140a060b06041809110301050f010f2c270102040504050f1611010209031603051e0d11030f0d06180218010503 68
    0x94256040c0c0c01003147e0345422a400412801203804080103500c80003100103610010f0b00c095802e00d01d54001d844a0018003006040401c041450342c107090903544409007450304084904e04660403d80e0700c1e5250100042e0aa9400c2e0810800801c41d080c800704450803908090304803555450b0301c0c141c65008246820301150040324000400483e9502406501d0040003000420030307043d4900980c2d9041081941d00520403440c52512080384981e0750400c9454516066000002d40c0d80c6100020000b0410040d14480500d490030380c11203032070815806401036400030b480400c0309490354401003454040880794442101440311103001494400e220702c2e0f0009545200240c00c000602e400079081c00480b0060340c0071054012410030500200b048501380c03001c0310a80180c041c217881015140c03905800c10f40780050102040b152550361100708100c401402c2e01080ca2621060f002500c440030300340c03e1041541d8180d00d42c1c0c0e40e0b40d00aa0b2842101c41c60a203a1207410310018202c001982c1c0f64200902c44d102d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736009973 1250 736008723 736008797
    0x1504080414010504050a0905100e04121d030106030c08010e0f0c01231c110a02120307110715020f070b0a0e04111b061f030b04050726060c0703 63
    0x52685800c4072210203030031f0034032003c1058034080b00100100000d5a210304120105201408080703076411144c3d080b880c80e03902e00140120002800c0c1c4a064850440b600d41541c680a4004140880e07054400c05560058009100914802c0074903560707103803200c84209103500064006621503015468040b265040351658031406540d1600308801501720307910b041c43d0440400c03070103c90f05c08948035094440c0100705880f8140301c030500c0025030350040b803030040381440070002c041003000e130003812030010030b4200e402180c1540341c035100034211200d60a00c100c0e0151064640c040c4100101003036410603984200f040c1814002252001c440c40d00c2e0f0300001c244c2066584802c400c2100c0303210001c103990080c2d1602a6000c3c00e000d109586012001803015102c0110b04008070300e4900d0710300e81c80085a4000c0300b01022600c0741d081050078410282e0204100400103011501c40c4001c04840802d4004d9003005d4485c40d66030002020304078403808100800280f800241c0300448100d002c554001d003604058121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736011223 1250 736009973 736009979
    0x120a0b0903121f080f06070f080114010f030f0e0a0c1a030a0203040f0c030f0c08120913181b080105060f0103150902030c071e03020a26040e0403021504080414010504 73
    0x1504080c24031700d01204c5034004004100c1c40e81c0c1c00141c1409110060b03e407c44140d0300d0800080c5a1105112215040080c0b07142c800b40307000d101c1c0d0020f0700c481c00005c2c0104140f61020031201c0d5508003072801121307000345503200001d60342e80b040320030700318038501d64462403440c3d5038800c2540003940020030485848071100c80884c04901c15011590185100c3c001003e604e0b4018202210000520f6102d000d040c4d202100b0110895240c1017540c8401406554103110003007020100e1011300001075240c01e40d017032024030034010310142d2048888905e03000c6556208944e1034134666820384008440c40c0d500005004001c4907294429848144880710395000c005ca03c07a107484490041e0303031096544036241600452000f0134400800d00901481c910000350103448481030741e01940700c00355402d014048606513401c24404c500c03060900070100c0f0000c04e801da40e841e282c2c41854101442510305070300500ca40580112141070f000e035501c0c05240c001900d18142440c2c1003440c0781914038010407a0400c08148000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736012473 1250 736011223 736011239
    0xb041a0a02060f13080304030801090e010b100e150a0302030f160c021003090b010b090307060207080d0c140a050a060507210509010e10090b061e06070204060302120a0b0903121f 78
    0x558087c610039503801c900e40d49042441401c3e07900d0381d94800400d034903082000000740c4d00c0444645d114174150800c01780c1000b80c400084c007803400314100070a601d03000160b031084c0c182d03045d03008600c030302c114100303070074041e21035008114903010b00c01c02c41c10108041d40b06683c05890a440d40501940b0340b0b140c080b031282025980c1c02c02d114001c0e802440c00680204080e0081e140034060b60002c1c000c20b200801243d4a03050940740d0382c0c8000400e5005000200031142c00748420900002685400041290845d8403a40b030010303035030300c40780d0015580a45810049002980f1400c0b50b88000003580701503000e1640030000034001001c01401c4407981c0c0d0f41e980c4407281007110034414618031030507841001480200c3c1d0309000302d401e000200303035500c604100858104d110541e160072201c5500300f80c402f96240e58680c8040750051529400103940014074000040443e09c0000301030500a102c1d60700c01c016a2a40c003e000e0750b0b8081d10082965040e210400603600d003000c2140758060305102c4c14040c40d000d03030312544 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736013723 1250 736012473 736012477
    0x19020d020705010c21020703080606070201090f080718020f0306040509030405030708060402040e0105010b04170a0602030a050411041a09061804050312090604110409020f06040b041a0a02060f1308 86
    0x1001c010130141401001c40d00e0b117000070310340701a41c90041175107001c26503540100396100080103148600360119068042da4410b000d460b028282101d0300700d0300241c80f00445c81c2c5e500c2c0c4610615640d071102004c80740005c1824001d942135446824601c0b82103485800420016180042c0500b040d4401404002000d503410094040203210b038002429090409006000c151307040707248000f1203681080e0040140e101400d0460b001c5070003c600c0402c40c9400200c000c0d0070401c00c040084e29150000c0180008480594400c0b4015803040416004044558040c0001d85851864904003a074a4900c4e0904c3c1d401c00c99855a4400c1d00189842007035031000154030a081d10554080e0380341d40c40424030304003404e581d108a981010814004021710300c0c150f0780e0039414444c1c1017950340c0284d4a454000d021911081e01410690500500300c0c1c0d2035544039001000785030410302c40c0c59000b01c400200807480d4540d03d0304071008081a075000e8031440e0fa81150015001002a095260000d800c0c2d095001003030311000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736014973 1250 736013723 736013741
    0x9030c1e05010b0f010c02011125080d210f0e2e060f03082104030e0a0905040218090a06051014090702100c050d0f05060102120319020d02070501 64
    0x245400c01044642420750071950601d052502422074241003c4043e078009804044842d42440c01c4d0515212000d041c27820001d40c070038000c034103442c50821528090f140d00d91410907900b045080701c500480c0c010b001c4600f5204419180c1c1a5000680c0e40d05035042203420007680700c0103148001c01c144000d0303080c07180303881c5d500101a41101c0400c1900168214101d2611400d4134400b10180651400c10102a948608500c0020f00c5001c0005892001562803102444020b1150290318a50f240c20300b8064400b00b25030790405c0c4203e18500e00071807218410310800c1c1c0a0364000d0905111480195503508081c00042c100c812248100f4815100182040c0500ca1040c07003440c0016030740b02c3c6000f5110305490460303d14180306500d0307282040300d41c0790700007032070204054800000b22b103c00b60b41c84156003510030910500d0074541030245d5000c1070490f941185004610030381c01c842e1401e642c810500d0f2240025074000040c0e07030908400c2c40740403000742c0140582c25a1000014a400d00c1c3d5078400d82100e410031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736016223 1250 736014973 736015013
    0x28051908190b0f010303050a08060103141504060603020406023301090b03010b0a140907031107050f120a020d030504030306210308010605031501081b030f010f050303041809030c 78
    0x5141c0340c204408400400c0d0800450b400c000040e50442e94050b202e402100c12810400607048001102c503842a08840700e2159905d000045a0900c00c0300007884640078540540101d04180c1d0000781d06220303100b11011154250701900b46020024201c1c41d4a461a41070540e810f4042c80c280d00400000c09080ca00070600c115000030407401d080141400c1d5441c00466501c280c2007007808020310007000002d168000d204580d00882a0758200e403d030002d142c40c0e0b885030040d200106246013048800608940e640c3d407000f0440e0307003204030400300c09914440d036000500143c00034451447c004d8000d40040d6002071007404d0115400703490300010840040003d0072403881501000c454014541c00c40f002d1805440701c3c0c589540740d0302c1e1408800e034291024a05a0f03041002c8034001900b40c015039a0014200c0c45d640c0020340e642d00b001005000001030a004402100d1821080010207107000002c0b50221444100c42001c0701c46461001001000c5a0206600380b1200c10040d80000e0550031090728090440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736017473 1250 736016223 736016263
    0x80c040b030c0307030b01051e0d0e1b03060105240f0405030a030905090f010e010b071113020c0d020a050a1401330f1818080c070528051908 62
    0xc1200207041c6d03108015414140001040310b00101400e400184000e80d00c0a81300136951840d035490580245001c00c91541d4030300503842c4001c0309030305000c60701111200880481d040e99032103500b0000d15854400c000c0c0305000000345849601072542006d41808410750300301c0c03401e01d41d8401c0424100440b0003801c400003281c5000c02e004502c0c019030300a401c40b01c031070761401c204d40c107002484e0b07007100e018014403c1101012608070200150700c14405500c2d0000f40440c0a60b0451010403000703908103594810943c0144641883c0341c5100003204044150884020284000140c0325400100c415020300315540d5203a240031102e41040104a43c00d2915400801410382240014882d108a0b03c2c1c1144c2c81c003100101080202c0040145030203c0401c03200800501066440046141d81c11840d40c0208101d2021500100342030000c181d41c6c040301e0054070b21200344c48880c40e01d4001d42400d07072610b1441f070700113000510450400e0410708a40360a032107040407007191a010024074220b0003191031b044413046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736018723 1250 736017473 736017481
    0x40612020f0a081b181003080904090602040f0f05180406091106030f040302060601050f0d111201080703020406140d0f030219052d0303040822060f03050f1006080c040b030c03 77
    0x1103262006400305d8811041c0351400c24010589104143c0e100140910070042145504c0781c2c0c86520481302d5603130100d0704540d110307078800014034075480c144078001d00c5400710000000c103410550300c0300d0584511800001e102d0750712952a0307401008030810030365050031400700c902c1003503c41c0340055010b00c0501800070306030700d40b03843c0080c50940001c14140c1080410f2000740d54091164043c4c405014140d1404220740a804005c440140110462100145500d40000421706800b154100079030b8000d075810701a464030f0744004085d0006280080c1d80002c52241040c0108000040300308211744280306817114800c10344054613603c04031820907034071508480c40340600141950909110303428056040b91800e4804070407640c60f400014000342000c0400243d098041c0207011848a440e1166281c40c5c1130162140350050808a0304a110700c0440e1410020609400c03810b40031038825003250295104443c245078045820f030f240900041e1005a040c04049248001c02000d188556007041202c2e4030b80c94 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736019973 1250 736018723 736018729
    0x10b03031c020f12060316080a26040f03050105100b071e120e04050f0c040b03090a080a0503040516030533090a1209080303070c031101050405060105040b040612020f0a081b 76
    0x1140400c47c5541c1c000e442080140c89008144e00102c2038201c0e2544054510b00408180003a0981d0100c0404071800580420400110710041d01501d006d0340003040384e5507420801c8455083e040c06042c044000502241000540e0208011621007491013001000981c0d5603400d05403503595021140401c20300b042c602c00d00c0c2414807509034441003490601c5141e0610700c4800c0e8043c425030140001c13030000003001031301821040004480300747c1d0104207540d484130a003000400a03041580c0c00c59480c042c0303285019600703503841255001e4a420101034180468000b00600f810b0208511400000458040b43c000f00307080c1e81c40309c41c0708010320b401401d51030a1500d4105544c82d1603aa480051203041c00c0e0a03c1509000010381c0d901c401e29081c8043c10720200c1c1400e0b100c4694000c0c0c520b034650700700b0040001700035002c20100d0485406480a101c00c10301c007010041910618002c1d142201c00000c3c6040240c6085001905154005802040c0c401d4a4100c0182020941e411000f400703890703007409907501d00b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736021223 1250 736019973 736019983
    0x5191d03030708070305130b040e040c0e06030c01081b03010f050102151306180516050f030a03050304060c1b0308040512040e04150f020c0c030d02010b03031c020f120603 75
    0x2081100910326101440d03541d80650b005081d00a0100917021403078290000704012050003903d1554489525142d4903e1584078040341103504540703008a070000090401c42c218100c90080c10f00074041c0c607400b00d143e001145c03000d00c024100c84800c5070840c003000310388180b94010f42c003800b54100031043d4076040c007001900d054410340c1340821140c02407082003050000c03521040702c2140e0180303000c40c41d002c003410300005918040001a0850207801411031a2041c10040c1004542d010b48102080703038120350405440e01107000014010401c10800940040c403140d0002407e8155410710310b1083c0112104070402c5c2d10382100c1100850901c40911041c00020008002030403a4071a0944c80c1504105265000300c0010f00700502c0c20302c4000340070351800d285802c45503515144003001c54440d0405a0415521080c0031040743c001d000341d40382807442a01c107005030804100068000d40c0351051050118180051001950085580c01e01c038015031100c40c1e40003060130324069411603905041007000c05d800c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736022473 1250 736021223 736021277
    0x3040f05010206042102241e070c23030f0307020105100f0324051003020a0b07050705010c060b0d12030509011b0c020d050a05070f17030405040b010519 67
    0x90f60010b402c00000814407980c0078101c03640818001140104028181e1070b00c884501c5100000301c0455820403219448001680318094651040300009080340c45641ea0000c240e984600098401246030040750700920b1048a20020001d2680d1260154a80a013141c00940410051131800403c1c04040c0e5424020260095012003109144624000381e4180c1074025110040c541d80460124188405501c00c03044d4842c5603120040c0810326202003024103010704c5006c105c0c030540d207005020400e20f03501c00540d04995446802810060309010042d5036156000404444a40c7c441001000a44071140d43d022081e108005456004260905c0076068680007085640d4980c500390241402c020350780440001050301d802d20102100150021440303000d10700c100500f60303114940e150b50400c000007960400b11819003149002d81c81d00e4101c00340e4140e04040c8188044e90040c4001e200324646507000180c4000c050410b145000b040d01c0207031641c5c0030f0f22047e02d004211b59030641c6040c030300398800c02006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736023723 1250 736022473 736022477
    0x5040602032b050103140d0810050f03030d020708120c0c070e0a0b030601080c15030f0c0a0903120201150605040e0a15030f20010c0209060d030210060803040f0501 72
    0x101410440025600d0041014124000291840e9000803030000780e0100d060300720341d00c8140419a101c0c2040640308503003900080782ca12414000142403442842220301901480300055102440c180c2001803688140031915850700003001407d508002030720007800240c1c0300c3d4a002c0d480d58600742d00211880307001480385a80703203410420000400004143c0c5010b44d0003240150304a43c4a06100d0b030010310003501880d405209000002c10f08100c0015018000c4100b01da01c0034440c1c04d1601281d229020903175202d0700150006000c140c0c8250120701514142e821442e243e500c05076603031144402c0000b00c3c024080980d40d07400d0201c00340003202d003540d006080d00741071443c40e00b4030704082d04201500003048000425504c3c01211040b52482d00750a0007503070004a110f41c4002103081034071000345000301c2034031034415180d080d48655000c0c2e10044903103074004116001603920f68083c026401441c000807000c40c040c01031031a60141d500d102e040064516200115111810320402d00e0314441d9680003141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736024973 1250 736023723 736023727
    0x5090408030406110c011a040507030608150702190615060503090d12020705060106120b04060f0b030907030c08030904050f09190c0e0112060f05390406030203010e010605 75
    0x300341040c08a9400c20b510901c00650611042e02401c3c0ca4001d650703107100207508089000b00e00b44019200f418021780104d0302041543c40b1064268222549171083c0704150304501d0b00880303605190314003107034402c019005803100924909074103400c8080501e01120b80b140e80391007100204008100081c050705850130b11528504141620715035841c4052840d9040160051041200c11036640594421951040031500556102e143c05421400e60203580340502c1e151070103068903460103004000481e1148504080ac40d820f180c91200d00c1d03440285400700900c82d40500000040344a50030b08001c100740700145465058400401095807000361030746c25450f0010041c03001c181c0c40482c0d41070b0500c40c0080491040461071410b0742e1403400960261800b00b40c110000140e07103880401c8110594801d510070020540300d540701104851003924a0811500c140c4000c000d000800b100016100280c08881c0e250750301e10b511020040e6010360010400660088010007141010340c081a000d0481414001c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736026223 1250 736024973 736024981
    0x80a0e0f06190e060c0c12010603030f032301031146031a040611031519081b040606170f0a0b040906090b0c0f0f03060307051008100509 60
    0x140c01c03400389880c02801e0310403004206049900401006800801c05030213507444001000400f03481d0719104841c2ca001c2d40046624071481941031141c801501d034503440c0c0b118200c0301c0e00404c4006117a0000e004001c60305141c0645055408000c0c41e50080d840340031034041d0002c1c00014410f82c6c0302d1006141c1b03642c440c03003d0104002d08111030070b0b4900a02c15008201162130140f02044809220307400076010810408010141aa4010350144a18001c410034001e00d00e40c240d2070101440115459031190080c11064411460600725078800c1c620307003010385090b0580303640780303a810701d002da006026801036400c0048050342070501031100100301d141004415500750314074035848950024009820f000076000007070000c0e5401d91003040c0705030000c1c0040203000c0492400340d0051103078001c15a2040b00041c0003480030000c401c200d881c05003840398030350300389000b4151b420801d8102602e42d0703a050040c80e1010582d521240094000707528565a08509030401c001c44407483c000b940c010a00a011110401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736027473 1250 736026223 736026229
    0xe01060302042313050c060304050601030c061e080613020c0703150b010903241a0406090209030d05131a0d060609050d020f040603020a1706060301020301060221040f03080a0e0f 78
    0xc0d806016030640c1d0b0303132801c0f051401509124541c00300c6940300c480131050200303000d00080c0d91410381f4800e201022040c3d0301d0382402d50f40507000c1d100d26840441d10f42c18000c011841a01180c3c1c0240014010141c05040d900840c01030340c200501d401c10300c6d4084041002031107d07901c0005d1044801a604004005004000070f11700c51250001406011425040400c4480404895000c9903c40c0c3d00c00c004194a9109201015035031684562045050070008240c0c1225442280d4100d140140104600901180c1c180c03030a0f0452441d003141031310398940004004840031194842c2c52a500c0541b65250108e07511241190780301d82002c001c00c00408803d00a07929101300c00302080341c04075407030583c4820581c001800703000b65400007074104501c420000340d2051a802510700c0100071a00351078803940d9007c01c0c54200c1c0408d104c0d240050344002c03400c1700350362020039503554a182200510351516468030309402c403606969004a4501c0d00c0014503d0b00150302c2554030306000760484200f42c840f4a00400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736028723 1250 736027473 736027541
    0x60f010206040f0305250b060f0a120303090c060801030c060801030206070b0411040e010506011b05060424020f250c0b25050105060901050306010803040e10090e0106030204 76
    0x8001d040d20364440907030f02072501440c04d454003a400300c6051003402c913050380c4801e010751920000705c1e200203003640407031064a001070701118060401303407040822900e4550f0060254003544000c1e800d050341c0d1041c4202240c0d07510a100088c0189403a50919540b546c54074140421440e030044003006901c400500c0140d130b076001200d80d85a044042c0700e120381c845041607848010f0300d420440e0300600d800c1c034400d0b0000042d04200c0c0710700c2c0243c807080540136610f6401d49040078444401007050300424000b800080403410314542410b03c0c1e00780b4802d000c004100000c202d070b10002d80c0f03022040d808121a15444904110840b07a900a1506855104407550324540845000e0190094801000c2660800c20345164140a091942140e00c0f480d291283c0c10814002c02064032828010100000045040c1c00c000520074103e4080b20015450030385041c010028102d00a08076860070151000d000404038232a018030100a4002800040d48501d584104011640c0f10703038400444012170b1101040b036000e5100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736029973 1250 736028723 736028731
    0x50610050d050c04230f06150901050d0504060e07080a0c0603020c06070f050f0f09040c020309090a0e0703120809010615171b070c03050708010b0d0201030b0a080304060e09060f010206 81
    0x80c04541d0b014060441714400160b01e0f4803031342c02c840300300401031048021a4082d01034403003651200d0010b03000300b862205030320408007902e022450401120500d246258081d40c0e01a006500006400f2621510340e810000e41c0e5104041c203a01c04164201840300c0801c0010040101c0d0504500d000300c444010f030b4440704000c10407824090789030310f01d1000b01d019204403000341000002403542c40e000161001e03003641201002e6401685030610201016000004541c101ca1008207a002203655940001014020a80314403850f401102c03400030014602d1200e03030044040c1c50701c03844205d141606c40d007400c4a00c1a8400e103000301546400c0801c894014a44810103100d0300e1041009076a80d146100540d51618801032600c40300050080900100060a105491180381034422241d5141d40403803c0c0c0d821841466400542d070341c1003600560007644a00c140b64006003292103150740e103180c42411600294020004603070105461411481d10281845e4480422100c0002000c07402c80001d5607a08024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736031223 1250 736029973 736029979
    0x9031305010c0c030c060201092d0f242a141e04060c05060109050f180a020301092006070c15111f06060c020306040305180a03050610050d050c 63
    0x9040c4000e0184555903000a95000b0703004200c00c5a1b203803002402000c0056003510802104030a529003010342d2030103000403c0b010007584103106500d1312650581041050110b40311840d104098015817181103400e04a600c103004001900702c10703d000c002120510030118a103040e4201c0810f12240d810001d07050740d14007040d50807030f164412800c0005c46850315580d49081c10070041000a102c95008003110809881030080d43c4082e40e0758604103050b5101a600340042c11071180000b00f10b204030181c0e9400c040303118400c48600090a4000c607003111a0702e101503901340c440714400d100c40010304034484820101600c455107010004e0720f9103c20350410717028451082100e43c80c55400c0500c10079022070600401d01c159484500100e4548401115a01403030900c64101100020840d02516414411640141c058010751799256021946a400b5130f94540d00c2d4014410440503544405586d030018500c50001092070303003030245c0f4900740c3c400c0650021b8461095083c101000403004903000b6910310b02a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736032473 1250 736031223 736031237
    0xf03060106120b030a080c01230a09061e27020114130b030109060f2103120f0608070518041505070c06020d0b0f19121e0b0a050903130501 61
    0xd140d500701909209401644c14819224000309100c01d60303004000221000000300310350080d2241c0440c1499185040c0d5150134000400200c66404a410003550381e4414540041c4140e0440a0301c40305c09440484000ea25135681c6000500080740b090305141100781700481e204080640c0c2c0005d00d01c0405960303003c003c89020980c16045954807411401803e2244021601c81d030b15031404070002c1c800ea00c1081084442d050001417815000d8452010f80c01d4400c40c02c1d008070956444c00e65175440c0b458884800035a5810806400c81090300c207d002510550001d4031200385041d007000b08090b00c200358041846018003d100c00100c0130b05820002d070501c242c1c04546942ca022054a0351b661031b02025001078000034541c282c0c08941e40c0824501101210a49401281002401001c02c80500d14400100a1040030b000b8203050346025007000c4e1040132041c1003074003402611a4416028a0103c0302c04002d42d0600a6555260041070341c071010210043d403c1c1454148190501e070543c0c840c3c1411b01c241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736033723 1250 736032473 736032497
    0x121605180f12030f070c0608100302280b04031403181002071a09041518020d0209060c030702010f1d0114090306071d060f090114070f030504140f03060106 68
    0x2400c0404000c100c02d14103498958044010b05011a400800112405660070b07101260031401044190b0090741041070482040b4150f90034046c0d40001c020035408280034144020f00c695003101c2001014004000800b03403100d165181000d210070900491641680003440401c10040c40d018000340340600468a1046095219800b03904001040c2c01441d11070040c484a00c0c60701c00518014005040e013503800f00300060141c008940031420700e002c3c40360342c820307503c0c94008083c040342c028005075460007000510342040d040c001b038000e50005c010180d1640010803403a00303540c0c01002410b4030002da81001c4c0e4000141d00d000001c212603403500c06043c0111554039080c07078441351044e1079030503001400300c5d4002e050408000c2c042205009007041c055001c1c3e25184a64280501a1a206d0041048031810f01032120015245a1503074a42508941410b000d1440499412032061724000c0c0a608c80c01d986d64200807100b203031b44404040c454021a03441c8501c60150f10001840e90460f01c42d8130340144149c5d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736034973 1250 736033723 736033729
    0xa0e010c080a1e0503090c040b19080601060810060909110412050615010201022106060c071410090303050d090206090a0605041805060a140a0b121605180f 68
    0x2160100103030414201040d920342c0a50410980c0f807101c0c500140c00e241c40040400211500d10040b0b480b080c040d0481c0c4903010301810305401c020b0007400d0043c510b204541c2004c0c0c102d038079440c00380c1c411015a407040004000c4c00390044416074201602e0b100f4596810304000e00900149103512402c0400350b030340e40d4200c1c1d1100052090300c015016400031840c460034103040ca944d444c038060700c1c0303ca400c0c180080320f0708040d801442182e4240d90304200403040411a21a642c954039002450346401c441b082014038200d05060282a000d4107503403418003200d15100050101c2e154001081d9420f101c41c000c0280003084d081425130700d030a0450720021411406501c0440c03c82c0c051440700d540c0021100f940801c4498006000c0c00a584002402075082c0038628801d40680c0d40985903941c2005100c48140102c054006421813001406451080031a9480140a550382d00c050411022801c442d801d10003440300110350b41340d90306420310b13000341442103000d00c0c00301040304640b4842c89401c1050311051303952 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736036223 1250 736034973 736034987
    0x201181704051f090f05151c0e1006050a0f0e1f0611060a050c040b1809011203020d02010c0f051e04060c1a0f0c0c0c0a15180b0a0e01 59
    0x400c020f401d2060f2100099486036070f0382500100d14000c078443c070001103002c100f002c1143d01201d5000300000c100d00d0140b41d400c00c80790b108851300c21040a07000f41005c040b54042c0a4648090b5441c4001d00048180041d1182100c041d40c01c854410006800200b0815900e0f245000c1528020b1131a60030325100c440b1002c8242c160403021659601c5200e50005200d50400c0c0c2002c10201001d059894983d0750f0750034070040351030455408101010070b201c02e001c0c5010603006003141a414104c20307002100c800c80010400c2409078480f58901011030216010558107200401603c00d503400240804c521001c000f5000b041400c00d0310042010100c0e40050140302041c0200e4600100c900066030b850310344400502444d0074000658194680c01d0403070820341304507a020740c0308418141444495445031804080281e11507041c1508a1254030442c0c41d150780c9880740d00004003400c0403160003000304500e02810340819004030241c4100d07600710811100050760b084416003011031924502d001070003401a110700d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736037473 1250 736036223 736036229
    0x1504050d0818100e0f0c150307020a0f080d18031706130207260705030d021c0c09060f0905091b27010e060c0c011815020604120201181704 61
    0x2d40300f004041d0800940d2680890101d460b460140c41c54015620440b0f99075000c0740b00c01c29046060f818003251003048240240d80c2000881c03040e10310310b030020346034841d50401c1080300781c41a03140041d101e10110001d101e910054107a10708002c03a800035680700174141c01340c00602110080803000000383c01c0c0d603030b12002c1c41d00c1322a910011912602d090510170401d020520142d62031001c40358030200c6440c001826144000e60040003036150a40e2554450043e400400b8042d90081e400d0013002410340050003440002403069850070700552a2110040841d04000404810301240540500c00d03600d504003c65402100d07070150030041202130115a03154891040b02e0f480150802030703095030304105250102d403411402d0b030fa00341c0360262020400240d4450112a0011580700862070849075014188041300c0558503011b02060b540e841c335109441100180b07607040160860400c00081050340800d03102400d030948001c224071072552401c046003510749034024124203031907403103030308489402c60450303001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736038723 1250 736037473 736037521
    0x9120b1b1804050903070c090b030102040506040e09010f06081011070614090c090c0d15090f0c140406020a03181a030f2802070609021e031504050d08 66
    0x18031240e101c8400640403003035100c244503c0c1440e000c03500d07561001007603500164110070484c078180d00e0325042e400100900c80b000b6405540a0000103010f98411010b003006200c0c0c140c6080e85c0c0d20346050b1607402c403070140c01400042842c01c5001d01c40c100c000944024040c808450001d43d0704501486026076014480c8014802c50400910b51180e80301e900400f03006410140c21561440c4c04002004030b403000c00c82d1003500102d001d00000d007140e051604101408800036080580d407503250b0910200384c40006074410441ca4550709000c0750a9030103010020640d26204c3d415017400c0c203210f030003521155a0040901041000d4140c62203d03400882214010442007a6041004c031a4041d92072003600112100d0750000c02180001e820170703034041411115560f41c81610080180440c51301700080d0400d5606446240e603601c8541d0041e11548a44035058084045d000c0301507254404062401822591401038560b00d24140000140001140c4170714103d182003100c81030361624226400602d1050324402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736039973 1250 736038723 736038727
    0x203090a080d110a0503250f050f07051906210c1205061804170f042303030c120702040902040515040e0f0a02060a110a030302040602010c09120b1b 65
    0x1654000016888180302d54a480d4840c20a441101c0b450300c07801e01c0b0201514941040100d54080c0e0262107a40c0c000b9210519052112103950b01c2d9112551001041140e00358800194000341890800082c001030504450039501528032817400000a0701c83d03c203100500100c1c1d2045036099807100c01c41c03880404250410802c103503c50000626902d1204425001e0910340f60100301c8130701780644400b10264010f01012810b40b129964180c501c010744840c50b050040510141c000d8881d644024001046c0f010100c40c550b8503415285000d403004c0d8019140310380d000300301c00e00f004900400c04d001c20219022000c1d0b11280300c1d00100300501010b02d8025803040c9010f007003107220080c0d62201c1006540c2a581080440881d00da00381e40c6484802203c20f4503444902c68000503e8480c0003000300c0c02c11840e045102c0003034100b0513490f00c1c85a036005c501203a0049024080640c0c24800c0d014a81582d150143d442441c02c2180484001c0c2c03190060201d03465480000c0c80820351a011148100c00042c0d02a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736041223 1250 736039973 736039979
    0x1403010e0d08040b010504050c090f12010f0e0d02012304020a1503020a0e0603010605070b0c0c01050f241c0f02090c07050615031c02010b0901150e01031a100203090a 73
    0x70b2254400311012209800e06400209850510303105107403182c04062252351034040508208210181481d03459603001c1c8090301c00c17020f003c0081c01840d4800c02c800e6400b00e600105c0340e17451410207c000c078803a021a8501001000041c44010200080c08120408581e141c0c0740c60010500105d0540c21900c80440000c020301482a85540140154502960381601c840030020800482c1c1c40288103e130001380703083c0114004a18550a41c90304013a07240011441c01c41c01d99841429031382c080700d070440392100d10310404c4011408440b42050b110414007524480c81780290000d202411507410410000ea85a4640001c00c069204140342c0c95030000d000384a01d04d04115031044a40c80a002141c00c1e01843d400704685000c24007448585510040c041d161684070820010401d2082c41c181d1000c6648807400d48080742c8506d2030701c2d4060003203561020401c0040d2074015040400711560f1504140c5800c0d00d050984800e408801c0c00d0780c20455200d0a00c0c80a000102d1840c0654184c07158017801d282c01c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736042473 1250 736041223 736041227
    0x2180921090306070e0901090b062203150c080f130c080c040b060415050918010303022406010806190905090c0306010807030b0f0c071b030b06191403010e0d 69
    0x50941c006044080354080c4d5294041100c0c420100382c001d81d08860000018401c2030010b4001c5100d5850203458182000ca1813010302c110200c00203c40b0061841e040c0d01070043c029040d00303803541641c08171400d001d108038000340201b4000c0f00400801c41b84500c1d074046500d41d101c543c48204890b8000301840e00450b2500000b94a9030303190841c0ea480f951400481030070600301802500c0c00c441e22088800f8a5480d009010344d0103502c0b60f0740c82ca6000c2c041c00c0d08803c42100751110140a14040c1c0d006003024110501c0c00c481d108078445031060713145010400c00490307aa210f004940c0c054410b84001d4542c0404607200e070020030150300030b001c28900305810808100000603419071510011004c80c3c11690741c0301c600503100c069500028106800850000d840740c00074201c0c0781d0304007402108480c07070319040b5118900501000141c0d5525a006940308001744042d96003030540106c012110ba00310480341c019400354241c0188544040f01d0780e205000c150030341c0e00f9402240110850340075100b202c0204000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736043723 1250 736042473 736042477
    0x203060f0114030106060207090f02040305030d32041b0914042003030301150e09010308070c0515070609020a080d2303060607060f110415030b030a02180921 69
    0x2c20703800c4403002200c103005240500401c011100d40750068051981408510380240125040d1030086070f40812000000580c200018680c0d0313041018005011145a0851054401210020f60050407480041001c103c10000310301c0e042039010300142803561810300c0101900b4001da00640103070f490421314107050928410b1040c42648103156400300071207a25034800d41805800089034040d48140010b2190101c4145242e40061403070400170246040d000000307a400f03000340c00c100c1d4450000f2603820208041098a000500347c21a42d0403240414156400c080b4029010003516040e00e4003e49015910341c15800806040aa401c0c1c1d1680b5100c541c002d8516840517180e14290415600050500620842a81c0c0200002002103280c522543c0311040503100906205414030b03601d00c0340104a4000c0d400800060030704140d000d103224803054002c0e04443c01c0580080c020381000c000c94005946003910780002452140e6482c400783c6614505a140100040000f100c00550b080034006c0c405c00000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736044973 1250 736043723 736043729
    0x306060504060f0c1e0201081003170d020d06092301030201020318060705060f060a0e010503070b031e0420060f03010902070c170c1e030607051606090f020906181b070203060f01 78
    0xc81e00b046846270014500030054a12000e031059910349402c42002c0f16480040091000700c0748050f041070256110b50701121165880f101101c1c1e51110703030a088410400c6040d080c54045240c041c041e41c91500040c0d202e1003011082e420051000503009460381d40c101c2030b90b40645d00f120840c1c0091800d8000d001c03d500741516041e2042c4804c43c000503400c4000452b05060b00c401401a10559150231546e122a0b00081d158a2100040f81403240c1c07218240818288254050044030481000c1003086044400b6030361005806050104500b43d500050802120704681240d0030041c2d45482c01d081005069810750084640c8098004020b0001c840006072414a0042125980c484034000080b60045039052454130b50590810780001d4140e50060001c0d00c0800c0071008000038448003540ca040803203241c0001212082d041320760030002d6040403095030380e0002c2d003520b0800080404009241040b84020034078094240c0f2210041c40c3d940303000059030309560b80517040361440d0600c24140381c42c2c440240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736046223 1250 736044973 736044977
    0x2805040605010510050a0f051908060a1d0103120e060d14150d3305040c0f0f030602211e070e0f0d050a0f08190306060504060f0c1e0201 60
    0x34000f003000e140130b1030b002030300c02e00c651100c1c0d1070800d0058094072000040319414040c0a41804000c10540361908041015185548c512071289845000c120900c03000d5085403249080c0c081d00441d200d41c015803010b0549400c80d54600001000440c00c80b48078810020603900410082621407000748a500954a10b6417090344101d0183c0d620400405200761425041768030581464515000c1208032280346442400c04408075540740285082d40355600c05511214019a600c0d000c01c07080c00000a1041c01030f007640981044d9071450a10009030040803404040c00e003d0703002581826528024114507813000710318042002c1468900c1482000e960018004400c900c4041c0026009a2043d5240d203208007000b08510b1302c035860002400148031030448212040c0c8620031082e8040340302c0c2c2d109814494444c1403003582d105003142520b414810006c009505050624405011b6141c010b41036400b80c86040c903107107401081c3c8500c1255103190f030200c06003406014000e100c40801e184010040014000e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736047473 1250 736046223 736046231
    0xe06012405030403080615031603061a0703110f0d05041404141911031008070b1303111329062503050f1305010801120c0501050328050406 61
    0x2000340440d00c00c034054032100c00240100000390000740240d0f02e83e034002e20054110640e4216580b6484003aa0060716082180c6030f0710a09201036950500a4101034903055840d0302200d04000c40008280c003400c0401410b1110304074440e10403142c03c00c6140f549203000c0003100d0148407016400b41c0140c0c0140100c2205903030054039554142014081e0030b51841c1c402140c4421542c40d11102d08202d001100d004440548502d05c0d08081c49404003e540160848003091042c0f0346068005c80c0303081d11644c0700c0261000300f4802c0021030b1043c415840100da800c00050050f01820f4000036007034004071034810100c2c0b4503004200e0010581d1154843d0007030320f0907461202141b0444100f0415008031200940305401e0215840f5544010001c0e0b560700b1440b9003801410550b47c113901495507044401503501515030070500f041103603809200240140080320840070303032090710346519078041c00d075000c0c00e8180240007000c41c00c07040800300d4810844202c214081b04000a0111101c0581820b640c16680c035818 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736048723 1250 736047473 736047509
    0x613030f14010c09050f0316030606050f1f0507060e0604030306030b0c160609020a0b031501080a0504080306010c050c0a0305210a051602012105061302040501020d1b060e0601 77
    0x4140f01c0d940321070040303072120035001d40790408000400c08020707800b0780c25005d22003184c469142001c2d0940051480307032402050440c01c02060110943c080f0428900c16400081c2c4800e0705c0071450406400e00c04586001b03580c40b0200e040104c090050b0303403010009440303054200014507074194001002c2c2d0f88242c05154032500c0c0c64072000140d0150382c0c80181d044e000591040c00255943e031001501500c060410342150ba6a1080b40b07025820803142402d070010080c86401080d039120704181e5101811308420071103403c064440b401c00e4000200802d05004c41000300d0810710008000901c1c40c0390004100c528440d859152640d2602d142c15003ca075021070400c450080806820150b800b00800d507a1400c1c2082c000100c0041003c54801c02070341440440741340944001ca51784444020b1910681c408201d60410b1002c2c08510701494001d04119441480240281e070f90204110664000e50b290042d42141c0000b14601c0c2d842548034000c115614100710785002900c0070032014100c807591100b002c8010300b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736049973 1250 736048723 736048763
    0x40b07060911040b100309060605031f0e030a05070818030d050901090f05150a05130b0a0206060d12050702010509030106062003041d07020a05100501230d02010503060613030f 77
    0x4912013840b07902201c0c40350381c040014072035480482030601a005c0810210303500e001190078881c00002c903032140307900321025903140f8003140240f81c42e0f44040c5004501d42501e940e0001c2c858028010003c100c4c850028032489000324100802d8014030b0003c040c0c82450b03200380805045070348800700311030200e8690400020005c04680f1400121540035144104100d16041030981da41d21202255090060501120030300181032080c440151030f008008230307034501e0780d00341c01392034508000c2003c1e1290b4030f901c40e1580010130080e501445d40030740d41862a21210f19100580c2d8074081c1d200784d0b0340c0561074610006031450348580340e4241110444254a08101c1c645d550b030342c03244150f004101079101c2d082d950103c1c2500c00c4464a0f031007a203a2064500307003443c030750b100d0f8100940c00c5144600c3c141c80780c0052000320041420310103880020141d00d05169070800101e00f901e010200d029040c000e010001486540b078074411034400c04c03162041c0c8000ca0361245410412003209110a903601e0009481d403130402c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736051223 1250 736049973 736049981
    0x91b0509060a0503090a050601031506150f12110f07061b1b290901050604020703080f0406201c180b04020a0b0d1a040203010e07080c040b0706091104 66
    0x240c0381a182c0103034400151440d0f803000d81a5a51031180485031404100c0c240001ca010307612400b0b25003021580308a030113040e1140c2e60045086101403c848403105a0080e4022042881d40c1c24a4010a009030302983c008161940248030f242034000744d2048500c0c0000018003141380308010030415808150441512220008041c04c041382030b54401d089c3d00858001c103898200c1c440c048460b4007029000032010301c014500f99481c031001220b000e01c08450000e005065200340151411418800141c030010503040c80a17180b0080f105040021605021550708085c10780600c0000d1030040070207c480f405003950140c4120b2510041d014201c500d4502e0300c3c041c5101d40c0c5083c0040c0031110819031980400b03800054005ca138003581100d80000d02006070800f0304400740004900041c505400c0d4a030441e40c024428089110b14030400c01481070400d25200940c0141c803510300081a540c580b4014a40b030b02c10f41c3c020240f6001c3c080341c3d103020000590002c4011520404680e10350100079001d01003a5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736052473 1250 736051223 736051237
    0x50c091e0406051512060a0506031c03050603030f220501080f040605090109060e0c1503010e0c070807050102070c17070303021b01120606020c030d08060901140105070c091b05 77
    0x5000c400104000c980b10707801c4250000b012044031844980003070005042d844402e030100507250010170030000301803080d12030241e0210056000d0000600070090340c400104d02d00741128281aa1000800c10a031030400594400c02030001c0c0007640c0d0312690b29030002e40001c18841c00c5803411680d0000c200c551280030860b010b00c3d5003c0c40050551200e9541c08050702005002d01d04e075650310303404100402d1550080d1500450304c2405450b451054200703100e00005907030000c03262800b0400c01080045503103500c3c580c1c0038035401d03100c5454107503501d041d060138464200c001e40158008a0b0b00b44c00d004080d03403030004035000069004100b140c0c0d1001e17039494060718030010380503070000410508603440d01d44044400703200500d03002e03450031041000401100c1207500709100503405201200170b1400c04020361420340d00790381001d40346450200b0004480840501901182c0b102d59001d4100d264010b4055034043c03680100c0003151a9200e200c4180285492618808841c02002944200700d014800719400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736053723 1250 736052473 736052521
    0x60e070f0903031407020d0b010501030f090c031205040b04090c0306081c0e2e020105070503040b0403050912101505040c1b020607120201091a1909030e0a03050c09 72
    0x2801d265843c00d07070344440c2e42d1100e0340c0000c2c001c0205500503a2a80f5800c140584241e04680c0035505003000101150515220380101904c2c02c140070300440d910400080440794403141c8100ea19417181411500360250350b014685c21100480e02050156464022108c4a240355408103c07140e501c3c40410750703d000b07941c2000c04294a003025440010700c90304e100c2c80c1a10000e070100700d010240c001c00140064501c041100700102e00c0740f00c03c07181039080c0200d40d080390141c80c2c0b09007035003040d40301d12440d002c1c043e000a040c0100011a10440d0700c0d4419441d00e1554100181c400e8104200c5012028000c05220301e00c1c550341032100421603141c284101d500500c801d648071030701600c4040d2074901030350701003000780c0c0e100000780030751800201c40c500c040c00302070502e90010400340740a00c0e022206080c0000518100c050640401009103002084100d0000e00c040c1c001c200e41205060a99000e82d41c0c15441c1d800c4480c007480030060201c006609a16000103031080050ba6450707640d014450840e14601c260 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736054973 1250 736053723 736053737
    0x209040c0806012c030a0803011503020c07090513061b1206080c0d0c03020607050304140913110f030105010f080615100f09080607030501030b060d2301060506030a060e070f 76
    0x144d0101d066580308003129040414000d60f1020000030300d086e00b0284100d0300800e0020041c8034082d2000c3e0030710b9100c030711410190708101c8840900c2d0b4580e00c10340240384140e40e0b5140041e0f41212001e060780c170f4050f00075000b0070204101d040c492076130f160106002c4000c01c0d81e4003061040441c092103001e08072520a03001d80310354044841080640103c107a400c3c0d51702c0c0b20a100210244e900c08000b40b2080740b007030000356580c1e440d000070411075841141c195031150084804200c0c00303202601348055065032204141045090010014030056a1040c0140d09586040000304206000041804c240c031110002c40385141d9404000517558a4160b9001740c00c0121a14400c00c0e00e80034100013000c0460a090902801e5110f0f1040c620704001210301c2d0002a8446004000f4007044070060743d0040701c1610a46560026910703003c00380790011424070320142d00112840c0383c1000070350014012340801004299a82042688480a080b46001e04101041d00202051f16030740650b0841c0e80e030a43c2515202c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736056223 1250 736054973 736054997
    0x804150c0c1410080405190c05040c030b012c01121503050f1603050c0105030601090306020a2a0201090e0c0c010914014b020d0f05011217030703110d0209040c080601 73
    0x6e2909640c82422148c448002c00c01085a5850f402480040042507500055403102e0740001410411004c0c02840003140041c803200c620011340c4d07001c00000c4e501b800c01a0800b14010001401000c40d0500c0030107246010101000f0400041020303000c050002080754940c0007181e54078084101039100c014255400600000130550003400550303800881410201c074a95502c0d210a0166130100005100140002c00b918080315860810303014440144900c100c3c02d0511940042c000d034605018485405846000180c603045182045904030001603000b0321a141c0182780c084d5a40c00c000b11158010350805200c401031002241c680c102d20507012842c2072545d1000c1c080100541540403900c0f00401c51040d40e0881130074240010407103800d00210018108901003819400c940041c1c02a04c04d82c0012001f5034040361281c1e0448c2090950500c01550300c0c0c5682c442a002828a4500c084404501259208488029034007422518005413800c0c0b003e5840030340d084802e00003c44106020444400da00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736057473 1250 736056223 736056253
    0xb0604030f0602070506150a0609151817010f0f0504031b02270f0a1803030e150103031101050609011508060d15020d0e010204030804150c0c1410080405 67
    0xc05042c01818010f16094668172402d0500300304a840768000c001001322000c2c03504143c00314030003d042a03d0100c0f800c60806106494a40c2c05c0101c5400b0410f105128a99070504170565070000c1c08007940099069200e901d07014040c103412750b100078070070349800d12280d40341c00a0700942e0b100b1030341617844010240d1582c1003050104a0608241c4e080341c0d0501000480c03000640c0808040340009900c0c20a07458001180c4103888002440200202d0401d500d1682d001c561020800515034542004151088002055031412580440c18202001040700000c2859008080c08271038114942c028050f9588800600000220078400e01d640442d2000307610040a120311001500f26100400303c0c0c02200c4603441d05584182820b0780d0b1000d85600043c8048691103070f11a1100c20751514009508140c0b0315290b8a02d180218842c0c07014599140f9000341520344502c2e00354025503405a00c03c2c1400d61140c00740c4040a00e07100000b1302400c140110407007940d000c0d450561195521000801180f0003100d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736058723 1250 736057473 736057493
    0x161e050913050a0b06040c0215010510110706111014010911070501111803060408070609030918060906141f022119050703021b01050415020c0102060106030b060403 72
    0xa0308110140000c200700c001030080c00600704150080c003c1c5450b81c2070070310800c0201c40e1801704000540d807008696a00081040708000c3c110707030301140c01040300b40100d48103503503094103600c40c0d00781406080c0001c55040c0d000950b841c600c0f0f0034402190401c83c01001c626040302d100501c40450300c90440c0040103099042d8021840f14410b041d10642031000a598207425120103400c0f18510301404107100b1842c43c6c0c4455000d02d840c0c8114020406410310ba150002e45108070b00001d8200d507100c060410615014550040041041c040200c1c0769080a1145000602940c09501007003800c0030b00014040341807224209103018010721081188100c251401c004130b001d08441402c1d4000e540c16004120070000c140c0c50441400152556111503001e80d0b03003820004444041d061160520103080400e030300180328a1400303540d140000080702c40e0001a0b60502440d4130180a0340300440340c44821603400704a096401000780c00f1940340ba41c8070081034090720180110107400c2442400100045215401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736059973 1250 736058723 736058731
    0x1d220206070812010306051e0f040c030c0f030210111b040b0d060501031110020a15060b04032001020c01020c0607080f0301031b0b0f0d1d0f161e0509 66
    0x20080e807800c6410360b00c0c40095000510303c9203085503108010020700030907001e0b43c0d13031082010410254400341118110818036024000098100354040000d00b00000701c0c0401001d075400c081303070200701a1780391503071400c0c607981d40006c03402040500b44070101e1a006d86003403154046614080e21030183c0c5880c500c9907003e4090000c66010791074000441d42600c1d48d0702a640c8042c01000045181c1d03040d03085c0b00c0114a210030741e45000e17a4400424810b407560208504440581c80708108030800403445184010b0000d0790042e002e15180001e000007003201d8075810400107440085907070400f04040005980300c841c144520781c0941c10041005240f481c0c1000200f070040c0c403500b081c074100000c1062a5680390001d80040700e00380782410141a5000d140c04090f001451241482490318550900440b440c1c020b404589903c00e403110081013034078420241500b1134106400440301c0c7c600043c084103566540011850020103030030703103012841c220b60446500b0020a44200841c006107040103000d08080003c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736061223 1250 736059973 736059979
    0xc180115031e0902040b03060c1b010b04050a02120702010b060a03022107030902030f010c1b031b0305091009030515091e030304020108010b120118020d0203101d2202 73
    0x24944811007072803002c50b00c40ba40c1c5103500080742d128a1050108031036241c4c2c1d40b148070368045010001d00280358400c590b0511b408600024624030403000b42da01404c0412003503a4003905103003c101c03030802140e02400080ca10007036400266140c1c1d003800d9088484c404440e640114082041d600428040c1d0000c103110f44c1d0613400a00100041c0181401840040d261000001c0e2036008040079842c0400094082c0e0154100070000d05200000181081607061595020804107450b40380034140940106030070100f10840701c3c500f0492910b0001c00303503409010058420138858428680c168400c8008205583d4450020034203410380d801c2087c070100c00145044502e11812100035014000081c0c0070035007034042c8004548030b040501c0003406010050300b1100d001101880300c01130504880002504461485039903000703000c504990074001e03105464032404400d00001c140f051401d01100e01004403aa40064905500c04040c03c3c9500c0e0002500c84d00c11840c95007091072420052001030603407940c401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736062473 1250 736061223 736061231
    0x20030606190906030b160215040213090b0a05040606080703050a060917040602030c070b03161116030b0604050105010e030307120e0904050c0111030c12090f1807020c18011503 77
    0x1d207852803d44001d0740080303a60550340000e002c09181c082c0e049107040302e250700280c0304c04940c0380c0c042000e2040080010784a10740c3c41c1c80d00e00c00211560300c83e580441d005410001d0ba45007545818020740b500303903011a00545008c1000904480200c0e05070185ea610101420312130f1001d446410140105910507200107a100c00c0701c0b2215071994008000410858026580740c2d4282c4116505002003980410b809080c10010000307403045c0c00849052011680c204000c0c16110b4008580c508002d00500c41c2c0d005280c01030100601040b2640540300343c504550500050380c80d0401141c00301d008003800c07a0554010b02080f0f0000d074940c40c0d0602003030000d1400f040040f00500008813401c8050b84c095865801c0f14441d54040d50b0700c48400c95010f102d0000452820046804480da12065034070104080c0a000c00d45d80c40c9580c2d001035031012810002d06009841c03c0c00403034a000790304161392141c05449080704540c464200290510882c0c070410346a88000d80ca054070110b4042030b01c100800801d135071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736063723 1250 736062473 736062479
    0x51201020909011e050415060f18230411120705070611030103030806030705011413090204030827030d0e0334060c0c120503070f03020a2003060619 65
    0x2c0100d128001d150360810141410400d011503992280c158010380d00a034109900e01076460901841501280c1da646480340c26801036000440b42880d1080c2522040c80c041d400006441910b1903071102005590803c103440b0031081003c03c0216550108415217060040c0626544518400b5101e0307031014403420000d1030040240d459100f124000000e4182601b4044010b100307046d03010601c0c5500450070740041040c0c904110028085240c08000e5084e40c000000d030101c4039081c0400145c0c0107000458040d9240d54403450107110359000f0506468142c042e9183c244000c40c03101d0b403544030070f04014010300708208032036008880010028008035003610882c0c68142840c900035407218806105602c80c0c65011140304d4903a181a2070030b50066080014401e4104080340001100e40b0031601c510410b103040ca0454a0564214001c1c6c00001d00650441e510013414145c012031540c1c03a0f584101c20141d00380340154819403040c4d038528805ea0f09584000b00040442c1055000c0c454101440d01c2d81c2e15809503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736064973 1250 736063723 736063729
    0x1e01170703140705070201120e01180507151d012303040c0f1a040e040f0c03030f02010506060c0604060b0112110408010c230a05041a0711030d090512010209 69
    0x9450a5000030b0341d0b00c00303224100210010181d0440400e01d0030034901021600002d1030100c0d00000c6a8440d982e4060111000500354000c240080d0000c1c00c00103050003504010b600c400740741c456215045440140c048849204000c030906c00d0b030020610042551070203004686808a0102401c3c101b03040304140c10a2544d0880503512562080000d48440d60a003488049494039507070286d0b190301d030320144000054001c0d030155010345048001100c9039507520304000381242e040c06005442e41d0340c4a8000f0080c03542c0320f0602921000ca9400a03c01600c410051140e40e21030030006001030340046020600090803a00300082003001403426180c0c0031910401d030380849010000b120441c04002a080001803000c4c040c81071402c1490400c00c412400c03601504400c00a40c485d0042c182d080003d441841a00071011354003d00420300c40111101e51199400d4405e0f40f03d200192406151a104502c5500e0f00240c0c00422140c140d503045041890032081c4441201d1030170b51086595000d01054031191 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736066223 1250 736064973 736065017
    0x31a07020705090a0f06151209050319050d11031308090102070b1c0b120307080a0c050105010e011806181805120304032c060904020c01050c271e01 65
    0x3900c1302c0000a60110004001044941690210001100c0301d80101c07076181c1c200500d1030751a030480348080b85524040c58980c2c1148120400c0ea100c0c0d1400d22480850a0b50000c046e10090000349001c01000303489c0390071030000d40001c50b034102200301c000405800046002c0c000d0020000f060049841e03081e21200a813a141d00305c6001c1c615001c40203501c41ca02c855880c041c0343c00c0c07440103440011040300701c401d00d66124428500c01400d200c4c2e0000301c03c007040384030761940f140031364010000300f0042d6150070280004945c01e03c2703020429a1904100144500e040c0b180d03a04841200e0b02550104a5407410070010700313030280380c0104443d0302001c58804900240020400e00d902a403809a891030545800740586120f03a848031122821030308443c0c0958450094404200e40860b00a6181c544407070004010b4883d01402d025154207003030511113022000e02c05010401320946c04c9181c0451f1800c0700721126251703200d66a0303010940c800c41c000f80b1842c180c94118072180616208600090364102c2d94021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736067473 1250 736066223 736066231
    0xc19050c0c0904060c02120424140403050303040b250e010504120b090d02030c0c0d1103010905010e24012903010b040501030f090201171008010906050f01080601031a0702070509 78
    0x2562a009202205d070350512050f1608108142d8003814075003000042050004042c84a000e214403400641010301e0003554070140d41d00140c1c20300781d9940d8503480c00c1d649940054400b1210094907001054946080711a009d000c144404a58107111b4803400f000c90341c0104410700310707050200401000c160300e0000c4000c0c0c120180030f1a860f9843d030030008030561030b2000d4000c1c1201190018840040031040225041c00c25000c00c880f82c812810146c201030b0303014014207100d154558a809550000c104043d0040340806441d0000d5032540e08140b5107c095901d0303010000d03a43c4000090050007a071610080d005a25209200413041501e083d0110020302d50003a04900454070001c9410042507074140101c00142007048010701c04480194006400f01e03440580391008040d80000291040030404c0440b00105a600000c0c4143d10850425500401d402d46101c0a0304161a001040c00c100004416040302d500104140c0340c1c071070b850210a85414082c08004c214041c200b0001910703a91503c1076405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736068723 1250 736067473 736067483
    0x10e0117130212030f180d050307030e030309180420062502103203011214010612030e040c0203071b0302090f160f0e010c0609050a0605010e0c19050c0c0904 69
    0x30710190700000782e00c52100c642601d40304504030303001c0c11f000410100c251280d050b8141400f030303a211009000030782507004400c5402d4100005040c0150341e1201c1c0380c09680030b035014000c1201603001002010303a040701c0c595140744d0008001c020000d00c1e8500c42d0b0301d4007000c010f501e0846112071825030016881680b14031501001511131702c8000f20004094100000c582d04d40100461114032400d4006e146001c1481b544090043c1c0c40007440a1003100300416085c0c207103c2c0b00030807a207910351b00035161070070700070000f07900050b1203088042d070354241841080100317440764004501b0a0f80c140d5441c4546178444410003c03400d040303540000143c49102040c0e004001c420032106c824a450f440059803000e200c00900108070801c84094101500700400a10251007032030910602041414244040c04501000803c1c0e48110442201441001d03440103058400001c0001c2107511414501d500c14081c1082a0717800e01c0d05030f4000e002d0140580000d08016030302d5000e441c41c0c0c01015000504a80007114160380f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736069973 1250 736068723 736068727
    0x9011701090b090117100b180711070504020c03030a05040201180f09050a0209090c03060d150b01090f36050405010b1f09090c09080a030e010e0117130212030f 70
    0x1441c506001070340c0c0174102d600040c1d000b4240c0640e583e565807521810407403000303940d01d2640480303441d000900d0748000341c0c10945209a041280005150040380f002c04492806841070119607440c09000700c0e880480341200440c1940c031505140307002000058030807810700070541f100000561443d0411002482c0c1d0140d0f0320219840c003000c0070142d880050030720a42074810030490226a40302100c054002170000080c0380c4907030700d0002003110134151420291180094904102d501803036600240c42d0000c0030390314640603542e1851125a1000300b802501c03d408040118044020a00b0141c941c2d05210b44020a240f4515006520101c2d0020380303007981c0594485515128900706482410500c1040040d250070080d21000300602e804002c3c046c80348182e483d000c0242109210308480d4000c1d111080640d03880504070700e8060100c2c03400c0d054060104242c504000e02d550701416003406400d50159005000e0b6559994030b1210f8042d44a00f00d138800301c4141d040480c154204040c040c103240300c5a0041d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736071223 1250 736069973 736069991
    0x30a06020a09050607020d030809011508061b0310090906231b031b0c0304170f0d17180a05070f08010e0d020c06071a0403050703110706090b0901170109 67
    0x180300c1a0b01e0b0300658062607040107200b00584031007203c1010a03406251040042d01c4440ca0103007d0038038a0f044a0040c003065a02040108001c14214040c1110714a54a071000083d9580e980c1404122828007003921540407c009180b0282c001c1c001592145000203100c2d0701d100c5007010070084d0840300111911103103003003007012a0380391040c06080400035202401c500d44102d5065055016030039901c01c03141c021981d8101c0769000c205550140111031741d516060301002130442e650301e2035140d03140d100e4850300341c41400803030080a040a0000150000089540d00e90f60020022041e8406c0e80c4040d214040d0802c0100e6014401c5001030704069283c0302c2e1144c0340081031820f48100380c8a00442e5044201c9000c18684c000408400222054920326120810342c10708803054408100c82c202508007807004c00040582c0301004085041c420f46943d11000e08408045580c2d01c003038041c802c08104d0140c1c1c180003104104c40a01070109051500440604010101c0f190000d0281d002014880e1584000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736072473 1250 736071223 736071227
    0x22020f090f0103140604020d060803120402090a15030f080706050c04150206061c0206041706041218030b0919080c01050705130b16020306070c060e0f100c030b030a06020a 75
    0x7065200780034038090044410308030014207070710320262256111340d9001486480c40402a0001c01c02440c80809480e264000443c0d0f00d4640c1c4c00c200e8080344200010300c0068156522449001c0740c2625024202070f22b5030841ea03d00c15491748010050780c00303490500c0316a0024149014103481241c2c401e44d15501d951a11062400ca07900082030001590850800c0108540300c0702003100801c1c0d09820200e0516040d800803440070310540e0044038041d401e95108000d071000000e82a030246200d00c450780c00544089004503100ca0711807a000300500ca41c500c040004c07842401d6400e42201041d0140d5040320441602a801c80d40c01c1c070000c44042c4408a820003000c242842031a0307102909082880c94905840110b480d01d00190042c0f22840c500400c07041d000c07070000d41c04031002c0c070b034042c0c11a5003c1c1004c0d88044d084070a02a8125111410030701401c501030000300d201114500000d008220244c403003884031001c3d01c03000400350304042da5410088000d81c1e04004100702e6500230900103a0b176048030a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736073723 1250 736072473 736072489
    0x150504060c09122a18060612050402010503160908150f1008100f0212010603050603100605010c030c02030a17071109010b0405190b0c0c0a050409030203040522020f09 73
    0x220640140700f9862008a40700003040c03401d40121565100600588020b140b941c07031829000041601c2c2400243c0043c3c0500e80c1c4100150707007081d126800c40d07690a08152054903012100240020400d1012803051050b40d200c17580c1408445c14401c03070709521100340500d4031808004403118601c00384284050140031050f0682c1006403958040c1503a4109401d00342d8940101459841180c1d440c1581e0b0b50114050b07060b5581c080600d14894840c0d60340b0140200542020340e400707882406001c14450703007078000d841076104480301071b103484c0880c02c0b05d6101581c1d00603001c8400d07a058001c10b105600094800349000c41c042001201c03c907119540381c00d08201c826081d400d46401138440c1001031080700d0301c28cc00e803801c942c41199610004580007444440e113514590040c8044800402c40010715040411034030720802c1d082d030368100150758840c00c100944c0c010752406000360700100014480c0e4207010040080c8100a48402d034821540d1389103020482c2d20405050740c04503000b0501480314604084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736074973 1250 736073723 736073729
    0x309010f1406010c140703060213051c0c05060f0d02041e060906080402060a05090d293612040608061f0305060d0212010506030c0d08090d150504060c09 67
    0x1001c0050340c079040c00003a203543c00c0300c0700180c80c0d402c00804044507050b08000d1480038590100065403586401c0c000302600c280c05000307251203080c5001f1602c42c1c0d0001086407540454100c02c1e5084441d10382003e020860780034402400000d0003c009030f042507050b9000900040580e1210007061600d45184646059010f8000d141004501c11033040041d0b0310410150700603804443c900c0c1e45214006095400d8814070b040c4a410080c6603100c2030500029140300b00b018500135040c0b0303100d00b000f881100340d02102140d0741400444c100d00c908444615120450120340d481c50203400c0d03002c612169951a2091020b544143c1042c00201803001c030354442a0107402036015980b200000228200c484d003600b2441b0f22031010540d4400000b115070741d801403000b4030550003500340f00b074072a208070032240030300021681a4001d00c0b449600c480741e82412200018010b402c14112420082040b040042d8601617600c180c86100c41d030480701000c4525807142d280a18030896000404411054019103480f1241d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736076223 1250 736074973 736075001
    0x130b0307030908041424040b0a120e07080105280e0a020612041e121d0a17012d1e0e01050403020609010b0607020f0d0501020c1005100609090b0a0302060309010f 71
    0x2c0d502c088840a46c1600c094901003802c00c1d4031070422640448119224000702e21603d401c11003003040c6da6801052240a8030744220090080707540b44440704444c0303102c84810109606403441d1400c01041c04d0f0b400002c9c80d000000942d07664025070f400194094014501403100000301c0f5040c0810400204500041d5030324034819141d601004d51640d10a244407090840c5c01c0c0280101003a00c0c0134a200110720210100412400c2c41c1ca4840520400410301c0000c04ce000e50301e0007000111100f000c50504c0c00340c0300d0302540401030009607200c000c094004a46040c580c2c400c0d500f5511500301b024021400850003a1000144500d0a818000d18105002d4140b0b20700b42d150950002c450384a54085484940e0142e0b150007039078480c840801c05035162030714050943d510101c1c1c1b000d010311002c00c48091050a10340c3c00c0c48141c0380e000c030640700c120352803040c04046440e20000b0441c600080d0803111030141d00a0a110030306550380c000c078844d60700458521680e079664088680501030f0501c40c1106505600d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736077473 1250 736076223 736076269
    0xa0e010603080f070c053708060106120e060a0c0f030507093c05151c050a0b1201020a0f08010509040f0f05012f130b03070309080414 59
    0x952260400ca00c21148000c03c0c222000601c5824041e8000c500b400601000d40b203003241c0326842003100c91020300b04415807852070490817115940c1400040744001e0390f1199000e8491a46054800d8031b958000380c200142058461007943e569a0b0f05000041c821010b080c004285c5900c1240000c048452040c3d5440905141c10240143c2c40c0e8071510729020b565030022052003201d030340c000324040e01c0001b03602100c0c44144010b650341e84c0040700c0e80300c2088034000e95042130304156515910085d40510b03507251035075205500c9144191912a00560780000180e20001001258400444c01030501402180e815030340016403410800c4e403000c0c400a010071285480025541054000b540c80800604090400c00c420468032040c0502c48034501071540c0d00c04001c020f0b000000140b2414a4078047c000e080340c3e0050f1900c46c94900042c0c048682004031060030035145030812010503900c2d080900301308101503640842c00d00003031090009201034500951404c1114015008004a45155a401240042075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736078723 1250 736077473 736077479
    0x50c21040f15092606011409090a030503060d0c080a0318050f010212090117040c14180420030a032d050315060d0204030b0414190305030612150a0e0106 67
    0x1101c10082d0a6840e406141561130b241484000035414080f9a210700c94010a000080c0f81070a6180c100c20403c001e541065159845031907940d102c40a0900107030200c2d904100055803031810103542c0302007038891812800352580714220385140c000c40c02011004078010000c40c904050b074044d861001004104c680c00324100079640000d4441250300c400c00f00d4490041146030050707000f191a0750300c0c0c205c2d600c104501480c0034248440880440e1180700001c0040000c00641c90600c003040000d424a1051b000c02151150307950009440700003042c0e01c0c140000b10b81603960742e03035040c462411258065071720012000c803031003c08001c51003515081c03031916008042000741650040240c9501000e0340b82e120059140c2000030613010301c0303100c1a02258520005020082205000d04280214000d0000811122003400c816590380503034200c008000300e04c1c0020000182c403a0307000b19400342010f00541c1c0400f0110f45034924120441c0c044242080c4101c00f005420780440c800d801520101c01c0081c0541c0745 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736079973 1250 736078723 736078727
    0x80c01020a08372618212802120d0608070e071214150102010b0604061e180e091e01020a030e010e030901050c21040f15 53
    0x5940350052100a010500e000c96444440c0c0500740440140704402e04121020039040d98444048040b030007103194481c4c0c4c040340900c40107125044015152040034030b500c85d034884a003d006a00b583c4800c52050528003002c01641c180303c40711004140522540368916501114181c800840d49000040ca9502c1a03440c071660011f41e80c4a07551062104603950307550f00a000c000f034042d90704081610300c90308000003000420030a095200f945c01da42d440740e0030006140b0140c03d466003000d11000040004000c14012080307040c4075904e1550500002489103071000c04208150401e40c08840802c4403c01124802c0149408282e6404250329100460340c130503803141c110320011406000c00e02c03200080000e003201403c108000e04254000c100d95078520a0032141070103507001412000000b4288a18001d4030901401b4455584402401840c10700604a00440c0e50703401852641f074440c40b40d0341040d06240500e107110240104900041c1d56034a0810025a07034200e4550b10013000c000e100304542038a00d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736081223 1250 736079973 736079983
    0x106051203120403090f080607030c02061911090915010e01180603180b090f07050a0302010203041a0f04060305060f180f0714040b09240414130507020a020307080c0102 74
    0x2402d950b18000281c5540c02d0440f8a407a0365040a50040035840000c80c80c9140010380d40d01c10002d540e0b0a10800e005030000f262601ca041d40d0507001c18403c80020707000703154a070f082407044840b03e117000341c1440c0c2948001400b101303054900641104024003c007000c0c1d6845011541c00d4002030810030030042030256540054070440c480c00c0200340e40c030740c80200d07800104d084540c403442c0c000e500650242000c115403034882d0080ca130411340d0b80c0b01d04040059907040410040d0700b140e8058000e107080034500146001046561248c1041200d400c208040000c81c45078060406409203a400080d2450102c003842100280940818072842c00c110101c0d54060100b40a41d5002c4600c1c1035080b02a101c891098403500d052440b201c5c0704810105000c02c00e2041c0401070140c4810894805100c2401018451600e507141701c113140148030100000d00803182e0500c1c3c0705030844000307010a075040c0140e1000b01d0441d1000c0da80c150050304040074403000d524040080c040900b209402810b401ea10001c0003135626 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736082473 1250 736081223 736081237
    0x60609040b040201030b1e01020d08070c11030c1c1104140c1e180307050a030c0b0c0312010906061d1e010c02090106200105070f0c020f0d11030106051203 68
    0x4400d181c0002001c59200740c0111141c403c000d40307402a65415044c40120340c0e041624618010302c24849480d070200d101d038850314001e00e216110404011550b031a20008580d0004519400d8803030100701c04229203c4a121622001c0c408c0e4000c10b45010a00d006002d0054400071103100b81e0902c08144984140d0040c411381006d481100f0a5a8148040500c01c0112510030061030400c0041032200c01c1c0c0382412a00c4005840842c02d1705c1d40c03562a0410085051103a0002621007806114207004006910f0010506003120b082140e0815035500603420100c0402d0308a0504607444030380401c1a25041511920043c1401d803200842403242d10102b43d0790440903000781103095806203640d84507400b0b10307a01c0c0d10090b00504510102c0d070b10380e000030304604c0c2da40310762200d101c61445404034440418815180644000d60301d00d5000c00d1440c03400c03039480540381e200703aa00500300082c0e24803560310486d003400340c18890346005151514800404d821545103501c100e000d1511124807580c0e104010003102c0d41 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736083723 1250 736082473 736082483
    0x1b05070c0506030702160b0c0f06040503070b10030c15120b010e10090e132f10030608151014030601170f030a0315060e03100504150c1206050306060904 67
    0xc030742e500c2900324035021ba062200d01165000100100d0005a00c0005200442404040380d446080315214140d8403a0101e801414940061100500003150720424076003040542121803007990b00ca07261009a13050603841160015402130a00c50810b4201d0781000548207900801c000ca0400d5400103000e0601000405201d035842005210704280035080c8040540700d80445030308107207070825002c0b48401d91400242d030709100c0d2041307171001c004154441c00e0a00a4002d0365141ca030302400c1c00c0c000104902000c03030b0705142d02c41c000812044800c001900f811968402485540e0a20640d152200e192542008210343c0340c144038200c079a1400181c1c07504407a01070207505403016282101c1ca0800c0c2c0306000881c0e4a00000420a04683e4160800d1034503110030b00c000b600c11503642c2c400380e918051544000c3d4154108092030080c000303940e4009039205004414030005140c81d180c81c0402c441958400c80040752072048500045001441200064034065000b0115402c22a0020b281c048008000501e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736084973 1250 736083723 736083727
    0x2104020103061203080a2d062904091e092001050a0f08090a120804034817120108010605030a17041e150c03080c1e070302011b05070c0506 61
    0x24041201581d030764154201c0c071f4030340980e00ca00d41c1c0008060100c43c41800703401c88000d0302c0c510244807206005043e10350010307030740c61a1a18058100b005031080d154866101c902008001c00f8407017041c0a19840c842c0f0584100114000d440a8070301107c14200d020307810883e0a02c130038134425810181c9508039003003904010132aa40c88225082c503007264208002c2c0910710041e10304000d10740103142240210300c00d4452104c82c0d211840b042d40c0000031a004818001c1182100001040e802c2660b091200121103840d00c07030158985418030007102035101c0501c00c030000a0114000000d414519015000c200004d02541d031030540080e507070b1505108050b000f529000924403101c3c10040171074004203034074ac400c3d8804501c038000069620780a4445c00165100181100003140c0c403030030740c040c42907525898210072034923050403484e425042191411070411024140342d030507140710f01c00340808901c01d41c00411014210f140b894192140d40c06008144031040c0030310070005407400042e03001d0b518181e821903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736086223 1250 736084973 736084991
    0x1505010c0c030f030e030717190305120907050f060909150a150309120206040f081e04090f0c0206090c060a030609020d0906051f1a2104020103061203080a 68
    0x3461074040c9500080001d890650f03041e0030160000000d030f18030441117081c0c0d02150b17900c81c14007130030750803000000906420200646122a02e8141c070346030514000d141007403c02c090050aa4100d0034151402049a0302c41c4004228a02d031020640116500944505081c683d59a001c01d1002c41c01a150200d15054030521800c2521144000d000904158490001d117003e5004040e0051440f40c03001d40d00c3c08407052010704920700000382680215400400b40500d2092503c401d20f9036004691b0151000011082403220f442d6014045d2010b018400e2000881d2400c025003682110200b5802d04150b420003000c04c20b540707001150311082002c0c140c0300142e90389483c1c0780880007080d95411000d1014404208072226184552003d947c00348122010009615524842000b24202c603140c0e082e1051204003d00c04055400d00581d001d5652111b00c5044c10700d21a1144c0b0004280f03480d0508a1540d041004199a0701d80070700300044c1180c00d950480c1000f2900c00600c0410003c6c6891a9207071140c000c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736087473 1250 736086223 736086233
    0x1809070c0803011d250e0102011b03020d140c04030f08070b04030c02010f140f0711040504140c0904020915030a0b1314030906041203030b06130e0a1505010c 69
    0x151100c0d65112030107907969a1900c0041402e8048009003004904c580400101560710404030b183c1e0100044456000c00e00c0b00140845a640b180d4514604554031507079007018030728080c015420440ca035a1005a120016030190400700c5118043c980001280e40e410301000042101c2250150303500020487d00c511000c0c00d0403903107449184070003860700740d42c9400c01043c180e000f501c5010b410f200741e903411070f0b880214408a036450200d50103c070345402c00300403900b291013100c8003c1440390f120724140b00c01c1600410004041b200200d5068403608412445400d2490003072200d2000d040045400b1612418160081407800a00401d034641804110b610082984d07820080c03404020b5010381d0100c0180741080b41349002d03c0110303408484e40f54491184548800000c025940d4880c0050005820103141403810625804a01426014195035054000e61615024002c007241c41c900100c02c459585403c0000c240944010007050080b850704080310120118016039104a03142443d2400c618642410300c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736088723 1250 736087473 736087487
    0x3030c110307060509030c1806100c05030f22080a021e0a08030d0c031e02030c0d0c090512010b0d06051b0d06060207050306011217070203150603070902180907 70
    0x291079458425100002260703684080103000240094084d242d03a841c0c11000e2000c4010a0304003070300d00c100850005030b00ca0500c0403081d04804950700e01904900c282c0e03101c6a0650307000e94402d021021000a0482c458603901214914004000741c850690030315050002303484808100300217100303c030f550004544440c105203a250358590020300c0c0c208481e41d1441311590302d41c17003642800070709801e02c24070b0400103000c3d229145002249984c510302c9000030041090003544010150003411f10203004d0b21203084820300c2640c030300050540340e54400e14107040c10008461401034421940ea03052080001054803038143d00c0c0112503110101065139264002c810032841d2416142c1d2000800100c3d0341c0014003800d4110b0030458625400b5220703003035100d0003459140c1e0024043ca413100084c540d040300c00610035000308190906180010703410b040050380080d00300390b0320307444c1504a0b07650182440030134502400001d00502850304110700e003036a42021403504000a840c80c034820f14a18000501c403e000d03c034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736089973 1250 736088723 736088753
    0x906051b0609011d01060503070302040b03150c0702090f06030c04091410020904050702010b18041704030b040b0c0a0905060f0922050705090d0605061203270a0e0103030c 75
    0x40e2100380c641892000c0c024041c401409400309481380c501068500e061091070280c035000b86c0540602401e580900c0040c059810655804d0322940340c21310394820041401a014580035440d0599890550041058541000d00840f101d04484014008640e40c0007402d008106425107000c5442c801e42d0401100c0d64101080403422401aa00f60b6450161264020000440d0450342081143c40d0070b01e0403401c8075161f04005810101070a582c42c8000000342e02158898860710500c85600b0310281b43c82000d4000758400c84100d14004240820031140b016595071000c1c0c40a0124204000d4480080c441c688601c1403500030200024001002e078079060464100500180144442072081080c1c10250380103a0b50251040c0c1c40c0c40d021884051007807007140c045250081071540324042580702d41004180c00f808855000b0b00c003c182428102062001d09009528800705409a10b0f24030365424803101400205441140e107a10240b205620b0440c180e419240c00d85800550004185000d03403501c00851 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736091223 1250 736089973 736090027
    0x1e071101050109020705070f030201020307140109050a060b01030e01050c1611040e0c0a0e06090f06130c02060a0c3e010218040b0d170c0a1b06090b030106090605 71
    0x1400120f540344541d001004490b2042d02111812551400c400c040800e00c0c1c08000d0060300304000d500c004c503001d0840d42954104020001842c4181030ba1018901519404c02b141ca2a44600c0b104851350b030140b2520282540c40c0000384014070300030760090264841e4042202083c0440010482480708000c14010b4084002e0030030064501c1120103030703644a0522240b244070300010600403550405d540521801410054500c0c81c664407101c601012601c4010055034010300b260700d0403160001e05000b480349080c0150003429050a10032119807c1e9400c01c042002031064540c154041c418003031348104c11586801000d54400000d14400f00b0064080c0c1480003120760020030411504151321000c1c040d03904044404000005034201030207aa075504040113030504501c0d8401420240f01c080040034280ac1520035100c0e40050382d5a8402500385442070340d0212080420309210786504103003810013802c01c48442d070b82150b1407d00002d200b0911070041001300030011030020f220000c0100310103440f00f002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736092473 1250 736091223 736091231
    0x150d05010e1b0a020703030309110607031808030702180601031b020610060c11010c0528020f0913111305090f010c090b090f060c07031410051e071101 66
    0xc0d00c1c8101c49020a82e01081e4565040c804204040c02e004225540300c505a00038040700c41c075545090b030061011120684021110111105c2c1039610b0034020804103100c1c2d1111a0360b504c103110401e0341c481c025000b4000320750040003c44096503d8105107004080d10180303403001940c03100012400f40040c920501e5032500708055048440342c003c25980d1280714040860728000f5500c244c101c80100002401801d03018019030012555489814001c16980c00346003140e041d2a00405512420444024000240c001642c40c40b0114504414400a0064110f0704c40c0e41c1802e00d240d019a501501c0703800107107501d510084c2c160f0152141858211b80e443d04102c04c010354600680e01ca03858000b042000c0708207510300181c1400850043ca1284181c2c0d10360b00c00c0f182000d240300203205c0180b0001d000075500100520002074000820044480503511910341050b84200d648402850200d0031084000150b04200c10000c0805261105400342c403c1800b56401c80d45454200b59941d003100603040301d031355080c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736093723 1250 736092473 736092479
    0x301021213032a1b0b030a0213080703031b060608060406020a030c0207030b010b090105090d050a0203100627020c0a0501050106020708030c06060906030304150e01120203040c0302150d0501 83
    0x4080007165018020b4441c3c60f914501405400d4010304001d54000c401e008061008010a1854a040b024144c04116244e920342d00d440078841c003a0000c80b4002c00c40c60b0005020f240b91010550004010201000108a903030304503900603081d01c500074902c45040504844203028011550091402418640e0585519041504000001c8c0d80715040342c07800709007004403086c01d0500c001140c400312600900140456420206200400c0c2c0c003c405d11030401005126000321a41c07060042095680304030024040103600b4030605081101c4d0024004407140340003c00c005103d10741c1800b2033103680381c0c40c0c24031050b4403422562000f4000c101c00d00a4600c1059a00001c00c54150301031416114507808542000d17648074100b950364415241e08003011340050000c15610f00b0822942c98101c08001c1c1603a040a84803040b0001000e0420344e24400101d15a0700c2c80440c3d60014909200146079206c1540b8524003034490246a80c00d40c40b009000324107001110010065001c00d50f1110721032001c0c07d01c01940c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736094973 1250 736093723 736093741
    0x20a0203040902030420030f0a03051602120f06010b07170a031d0f07120804030219080f012a0815040e100609110702030607051612050a0201060504020c1002070203010212 75
    0x34600766003146086d000070015607a4a00011b80c5149104848010100300340280d80442c0c0c1900301c15045482001e1548070007005948200d4100b40c000b01d504000c110048000c048640361000603403040c40480020440000410b49858017007180690120710b4030750354106680200c0080031150300303910040b486c00c42c140d08a042e0101d1821907003881c000c00c503840f0980720b01c804e0658032074030030700101441002c101c01c00060070f100d0104455500880440d07408a03076160b0403542010084020464141d5460401c50254580f00c0c1c5220300c410900440500c250340e60920150030741d480038001494211311740380503134100d544980242025a1510702941c00e03903502560700c2c102802c1c0707034029134410504203041c85503145000f03404d940c0c09a400500400c0e258503040d805035007036072248034581388900d00000c81c1c401180c003008282c0d048811580d035a070342d1824038641c000e08454940c0c00051055004101e41c9480410008010031280340c10034005980310000c2c07002034024841c9000e5850b05021101c03c0000d14a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736096223 1250 736094973 736094993
    0x507030512041101080c041409060f03030a080906220605091609020706052d0a02072310050411040c020a021e090f01050105070305030a1d03040602070807120204020a02030409020304 80
    0x40c80a88030945e564481014031407950056002e0300079065208042403441d031815442e0540c00510103803428241c90b01c420041781c20345d4801c4c28500003040710307102030021072a002c0003201c1d0300c00b0800c0c86004100348440402c4054140120000c0c0c9095102d0010030103080080c00b0404050306920416a025680d4804102c0071350441442a0764007460000007842d80c640001c03451042c50300072075909810481d038080154524801400030303423030183d00b48003501c00a10105200350002d004004124011241d0354080c518040003103070140c2040d0b080c0401e000010782c0070400c00404680c12100415201000c06049107020b0030144042c0d442810104e95a680f400d00b4448075071550710944404040d543c40380d04034403454400b0702c20301c0c0c001a4100700c1074001c64840c5028642041ca54640440e6600d0003e9460f88103c0e103d08480303800c1c0d00005001c1000c2a0100400c00c01058030344084c200062030024000c0c1000d0304d0810203401290001060030000d40f0030b0080b1405001070a00840d143e081030308000c2007207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736097473 1250 736096223 736096253
    0x11070608091b060d09030504030803040b060f01020c1f05070203070905220309181107030801210506011701021210060212030f04141f1a01030c02070303050703051204 73
    0x150040d21941007282c41021050300320440064007840c0f0304045410603500910040c4419010002d06000c048001046c22004600443c001c041d00350355070912200300700c81c0410802d00c845c191352200c0307801202a01d80d61101700201c80700d418000754105695505031408d10a42100943c14003c102021540c00101d600043c055409540a80f610b150419000c10010344560805004581d050f00c0400c0740c603448405070004440c10110204482022010038000c0c0d4006031012404070301d49000511480a040c012a1075410090104d54482980307511159251300040c000d49940f125801105101c40900f5011691240c141c0364159441c0e01c0c1404009043c003030070b4024100180034510380c8040c42c114110130b586c010400241900001c1e1299560910b80d440340081014dc0d0380590404880300780003807603440c10700480d181000310344c485504410300085403100c5d5019041c1440c1011a5170400c0c4d0002d401c0d070640c2e80c182402569041c0500b000e4500d40280c5010030072007150030781000200003004000ca920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736098723 1250 736097473 736097491
    0x60e0f150d0608300a1e08040b061909050a0e07081f020a080601051e22120506010e04030c021507020117070e0d060e01021315030e060a02030711070608 67
    0x200034281c014107101000f1039110034035074034032240713041c101c51200c010503d44400e0308041445070000385a1800600601882c040829950f10401c41844000f05400750b210804640c200a000c8012200321101341e030600502d80d400d55074400007009503240e9484800c44400e100c01b00e0703500340c0d50f440c1d138265142c14100307013040400e01c40031034000c00c0703807190082d14840300107600c58214660715a401106e503074000c803850000d4107190842c0d080c05400e0f0b480c0240508400d011702c010178441e0101c00441e9400480c0d028501c2c8050101540f00490400300340381d070541e01c0d40c51031420141c5070360600302e1781c8045900340070758400d01c4007107003074081d0200c40000e0251500c01e0325424124402109079084100048030103401140c01c442c1c40701d04916250307280400441c4101c800180105035000e400c0d00320381002140025406c03640a003881040c2603400c0908000e20302c1c0c039041c4580004206010b440c0c48019040d503000640110124009a008001500c0c403100900100c80d49a60b4902d0002d0401c0c40640709046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736099973 1250 736098723 736098733
    0x303110a0503030406091b031101090f080715121103010e0603030c0d0e130e1b03060411040b120a12030b0a061e05040e09101401060e0f150d0608 64
    0x8040802041a2104503042405141151340301d03203030351020344882c0c0000c0f50140c2c49007880d525103a042c0304194003d10f000d11a2980c115a90307200240c04d01e105600034080243d04100c00f00850400003800780c080d0341660303000c00020300b40712001762100302c115942035461a0812092030440301e102800703123040740c880712440c4d1059119001415200c0c0708641c510305003508141c90207940315005104104066102500a00190f04c00c0d8409604942c0040d00484240d001a0044a6481c01c083d036848000c0800b00c02422050030b280da0f07414151900d500089000307948a800d00590b0380c0e2020320303203c074060b507890994540c01414079141b803440740c2c0f0b11141e8020a1500d078074030405040c00c0089405840007a102e117980c0411007801d0005000b400400355040100410020505101002d0000c0c01100400d00400c14141102c83c80350580b02000340d11201200d554004004540d031102d45244416002d841c4580b42c100003e000c41e43c61100e80e042c004c3c00c40e0740041c8202c554802e0b507100200310351414007a98 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 736101223 1250 736099973 736099997
    0x120509060f181221041d0411040903021b06120a15090f0207140607020a03050d09120c03090b090f0d03020109020301020f180306011203050d060e1003050f060603030d0e0a08040f0303 80
    0x1040c207000714004e400d100218403190003201c80b00041102e8007d40a446050b000ba042c0c100058103650b01c0d03080440041c6c003c480d900780c40300060100f00405032002c40301c0c0c5040c92104884484406401031004040c2030315552842500d0b240c041081000d0072414100340854582d003e03500c0d01035071182c50100d48040078003105d0300301040007203405405003405070b0145c6800305040e1401c49840d044071041016036a038030920000054850010601d044880c0e0301d0300489192141400390011034658050514004100301e121816036400544445952007111414031010880c2400c9004011f22003000707415610010700c0c4900c40d0003070000b518591810200c088400040b180c24941c03590340030b01c60006040c07170041d01d2100207030180010348459042d006001504542d00c0d1010f03092180c0c00d4a050315540c0d802d803418001e015007032186079148901200204041c1c102000401c0c0e0368401c116025945071781e42c0e4401104020140009150550001c01842d00d0b5500c0b02200d5241010324841240410b051406003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 736102473 1250 736101223 736101283
    0xf080c0409021302091309050f0607030614090705120106030e0f0a0c0e06180f04021c0f12090e090709050f0c03040210210504120509060f1812 63
    0x40d000d5074080c000d251200b1041c0f4a61010350045045541d110840040e080c01d000c8039481346d4200306000e8002881c0d580130303c2c03070b0040c14040007510801c02c01d42042006e00030200140080340c1031980540d050f0195075103130722080301e982c0904d40c00d04102c2482e902c000120039605070000400803c1c00d4090321301c0a4411f4091641e136001c00040105001070081c403c024490040d04010f6020401030b0441c103800c03440841149901c94203c0c2c0c50710001002030180b100750300700034075485114948540c0c4021041c86644410400c0300c01550010150001c5150f8024042d105588040060540308001c0c40c060401800041d19010140a40500345113000300085c001d60001110394003e06022030024070350b495503024482c3d031016441c00407051080c40a0700c1110486c1c01044140c2102c0641c60014803820149007402449140e0740c0c0701c0301045800e00c881c00c43c5036100c204a0301c0c03072075454050a0741c4800c0c46a51b8541d4a1104c401907500c0222140404101e9101107280840c02d03c2035120182004034260030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 736103723 1250 736102473 736102481
    0x3041a070228141501140904030203070b090f0a240615030b03030415030f06060504080c1c02060c0f250e0603280c051002061b040305070f080c04 64
    0x2c4110024005101000452964460381100c14054010550b50b001010010b0b881c00300d641150000c0303551050010080456a1210604101d80440700b10710707281400e0318025507070b01170500b0203840e260003440410340001081116000740d0701e09001f900c100c3c11040c20040c1d207115032181c00d107594001c1003d41d1050340f500da11691041d107114030325042e002445c0c00c000310020040c0b0400585c140c8030411000c04c2c0b42c100e49034100e216030003d42d0049060040c0c101d004041e03621550081c1d05200040c041448200c00108584121040545000481c81d2029112808203050040040c0d0810000240500c50050200740d404d0202c801d03008880d020012502100031441c007080c1c50300c440c01032004040c05000f8100f4402c6070000300040494600c071900c80800658030f042031509201082c41084c0790000c10030124038000042204441e0030522281e409006500e400008100050b01c00311044079940780e1a1290546e0007a6400908035030846440c0c0c107400d00d43d0720550041c0c141c14811014403400703514023401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 736104973 1250 736103723 736103743
    0xf0f110301120f0812010e0402032e020d02040b03040503130f060f030c170a020a0e01020a020604120320060f010b0903280215040306230411040f0203041a0702 70
    0x2c0107151000c500c2d1252514040a44021161000200039810b0100820200c1c94040d14007405a581181002d02c1010318110100c501d000d04004c40030804500d030219001040711880072801d016a0b20754000388400024411034011820b003400c0070051105003e00000035001d02e203005e10101000640341d500340018035299200f07460002d00e410b0004001c20340300c1e40148903608440e080407613125200d0022014801c00c111088076466130b010501c5480c195202620101c45403080c0098120a141500840d80500c0b460086d00c11724101e50311450201441580c02501d2406400308a40000810386141d9840d080e040c0c1d052b00b1203120b07400001c0b5076620160308071000c44400030020a241d040512000580c072062403108035610fa00e00c07440c1c0000d41c80b03c81022100c01c00540c40103907528118981030040700d00d00b006c02206400c0c2e608000a1a81003110340e141c009404c0201c04150000c0040020094030000303114000c894000b0051004002c0c440150442101c100500075085607034a1400300c1e81c036034000c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 736106223 1250 736104973 736104989
    0xc111b0f0a080c0d150903170c0a02100209061204030302070c170c240a020a05060f040503071b09110309010c0f0c2607140d050702010905090601120f0f110301 70
    0x142c841021441c1c40c1c04502010782c840d1381170500071101201a0360403920301050a40100e13500240c460070406c00c3c8101c80d40c0c0701d0001e6030314908152400d2002942d44c10382c42001d50000b9400101030401e941c0d02c80668078981210502d4010b20f180c14030b4010080d4010150480b0125a011004260038403080b0340405d442e60603130001c04000c40c640003040340044071200e41260700d80401c0151001250301c00000d20007100c050700103082c40075042c43d003140791000040c03480c641c0c2c0d2528400c0c000041e801008440e0040e0f0403501420052001c050341e5502c110b10b55005008140c030b0203800d0b1070250039640195100341c100d50020002c3c0741031031206859410307070b25480e4000a02d00150000000b81c1c03110090351502038503c0140b07004010800c484031180d10001e02650140108009581c1c80f0108005030107040c4005c3c546582000700316800640156100d008140c42005c0020008800d64451a148400c0780c04502c828024440361030303920001000e0042141092a08009070410302180d080708a9048500030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 736107473 1250 736106223 736106233
    0x4030807020402031305010204090905100c05040303050d150f170a0b0c0c0304030813081c02030418291c020901031106070804032301140105040c111b0f0a08 69
    0x2907003080000c0d80001e003600c440100e02c2103020089182403019102034034013000b0003d4071f040030b42029450801d04d5201c0008607810264481140c681c80000ea80c21254503003001500d40c9140d00c1c10038080e0106e141e01d003842d131260310b20004040d6a10070140003210081d00e20310042c03000b500242602ca004c80c10f4082c2104d40c040000c84d0707109445a0060040031007540070f8904160726903a6120540e40042e0651400c401a10410700102c3d800740161011a00710030100d840140134480080d440c3d0151b0311951909502c4000a004d8403140d5402071401440403060040f9403019242c0c600c0d07517020403003038810b016880c494146480d078203407901e03180d03012500100f100304140c1c61661045191040725018a40040c01409200700085180015202451089140040040d04001c901c41c00c46c0c1c1d4504080d500f6810301200c1c811458404440c0ca055910a40d40031501c00c0d00720100391079201c2d000010007001d1080d81484240340541d2000c0780020041281e03042403a000c0c0504100204209002c3c2c02e40b248c0003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 736108723 1250 736107473 736107487
    0x10e070801061d0301050a140609010e0406090303090b160329120304270507030504080d0c0e120102130602070e280212070206100602071403010f150807050105040308 73
    0x25096554221034402c0216001450f160301107070a556065908189843c1c891300f424641380d01c0c00e0b110a91140066907450511343c134107210320911405c0580041d007929512001202454820f0700030344038a60b0841162440ca00340062244003240240800c400064581050013204041181d81c07005000d40c81e820b640440885d000c10000c80c0760342543c0305000d07031208020008405000c0609a14103000300c04041a40041c122550415070b00c009142104142c5840c04000000d8070100075500082c54103000007841d045510025039244110050383d940c450801d030384400348005d0540040625013801e2031203900301a542c10090383d031511a8010100703054500400900e188010104220100d081d1b402c0024488000ea0001400c0b607000b80c050041c0c0c0c0969604020005d901007000a411042c3c41130040c07030040c43c5c104029224082c60280c0c1c0d20402880042c001640d40c00d4000703110301c0400d1003003000394a0038054081c6080c8a04d2007811a503018601c00021590702840035102200d030418042841d200e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 736109973 1250 736108723 736108727
    0x9061b0610061403090304090e030408060a0c051b0c030115091d070326120f18030306040b030f0f0105010e070f082e0801021c090c05060708040905040c0509010e07080106 75
    0x1805c00000d40700c140000524001c3d00e0003818281445500607581c0c0320f0408540e0b40c100b150042c449141075040040c001d03036007079000088410a1213840308100031054200c030014106032000700440c0d890340c03d1914615404648440351000c0700c00c03910003003004070415105088170202040e9080450342000c8002c03c082501c0c0c001400d1441801924410900c6464034140d80a130800380c50316411883c20300812401c5c00c3d8100885070044d4038074540140c030b2005400c4140c3e43e4031000b8030307540c0100d48032500300c81161420001113042080080541c0d000407104800e20b8000c0209105071007100140c00c010400c0c01d40210004045040c2903990000203a0b2400124002c2c043d203591440ea03ca022009aa2004007500a0000280c48504005030f07813080c201ca415040718148a0b555900c0c00d162601e0000060850b0440742c080310400d84040761244130906110446020f29400052000c0c02d0004100401011010324400c0c2d40044629640a03600d800706500411011100b43d00440ca40d100144240340c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 736111223 1250 736109973 736109977
    0xa1a0108061318050f06070e030a020d031404051e041409070e040f0f030306091b0206040227040305090114161b08010e010f0b0315070305060609061b06100614 70
    0x207400206400f80c40e010590740c4600d0400440b2010401e0340090041c0708420381c2c01072403504c2a02045008141f81c4142e80c0009070494503102005061090900411000400d980c090384d00600008006440c0600d901140c55285000a40076911442c074126071000300c0c0581100071030280310300400821401c2d003802c0c150360a640001d0000d0f24105120303c6c0940002d0800520400082e00c03990b804a4101d01d0508584140c0f01e032401c6103200f080c0702d034803c1c92015600141d9141e0180c0c04803031280414030b41700c503443d9111054070300c04002e10131060104010305030800014480c0c11003ea0301ca45c169407401045105030302500124800300422000007401060801c02040322490443c1c920352415555881304a007155004d6500c160103075141c608400703010100d4030900001034400d4010f05150380d040046050244070080036842071550310000704915403600c0040d500080c1002c1c03d45580d4415a41c40200500c880d951a0b103598416200013450603095481d14600700c6505450b04045071644040c1c0c1403682e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 736112473 1250 736111223 736111241
    0x6090312111f060f0e0106050d0506041b030c0306170a03200f15010e0f040f060e0105010620010603110105030a02090603070903060f0e03030c0702132d020c070b0904140a1a01080613 80
    0x252511000c0007370350031301318005c1da400311f0325200014200c09001002c1e0955072517034802038420020b0402190030400c0801c1990886502d46460808001d0322281c200001070a000d205d2403c0c4504d03003441041e80300018100401d80488a0000880d81e42c4004c400b55820f01200c4c140d1038070b11070101143c00070340000c0503480d10600c1164049596410801801e0841e80309070b01007800a01c90014280350a0ba0000400c07446d07106040003404002e0554460381c00e40b0180304905410402c00000080c0000c205174103541105400401071a6a810b152400410110780c6020a841c0a860503c0460358407007d0300c03403a004100c400c2d001c1e6080d5a500e038001c04240e041008240e81014081c3c068258210ba00d03ca04100d0340306d600003112411400012407100300807001c01d0b02819900c104200c4103c4100054003d0031100740c101a03555500e10100418040c10307403000d1a220010b0241e085c00204209a0000540310b4520507024a0b83c40541e001100e4003802034a1107500040039070040c5e002d08409400550704 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 736113723 1250 736112473 736112479
    0x1401020c0409060b09040503040f0b03130b0615040b0306150a09060302090a0503060112033b04230415090209040809120307060506090106090312111f060f0e0106050d0506 75
    0x19005400c020070b00c9800c4c00c0f1b80440d5036800014050109280c00ba04060282918050003030031403800001d40d905130302c01048040c003c5c030300e500000342c1d903a07135a081044414601440083d48075691018080b115400c10b50303025100741d0007400b841179022074003000d0342c0841d400342e075920ba14103281c6001540298041d030040da8000c848001c001c80d2680f4104540c5c0c1c02484038000d510700c6039840c0d003801000f4a15038a41800b41c01411010003000c540700490744032030070800a100505402280c00020004e01c040141040c5402146c08017061402e49654854401d502401140d001861020140300481e0107045000f5070100e40b0001003804214404080d003c0294094091014065011141451a0803295040340e405448404024050038803141072401020b00381001c05c00e45040d80c0d40e05110954018a0108025200e48000d03120542001850041603005046903126080f40d186400500014010450303003281203c40000c402c414007503050304842c44e559400c1d003048030400c03148010b01006894164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 736114973 1250 736113723 736113731
    0x807080402031e12121b090306161223010905190203040602040b030903180603070525240e0c01020601061107030b01090501030204200f1e071b1401020c040906 70
    0x1040ca44d03600041662840e4080d8507403103803800203101d141450701d0694200c031400b002d011022203920000f58082e0403040b1f0008101501d840c5050445a00f01040301d0004a00d007810428581c2942112030f60070304100601101034140e0700d44e610213050300e00030b4409901c00141c2401d01c009900e100c1d80a16000343c80b601000d4a8035a55840c040d00320340081d140d0401c1600000740e030a062003022948d01c4022403096a060303055191116010b0b2090003448291000384031040000441200d441481c030f0315155014400c000c0c1200000911442c2084d080301c0078440c28602090301d20031381d0001442c41d0001205900a1010340c1c2000300465403901c0e0401442481c0c403d90034003000107008541c1c441d01800e428040001e503580b4500401080e180d00c618215020014021744c10404c000c1e000480c0d2000f54495840caa45011242c210349002d141030071503d00c182004104201040150301885000000800803030700b030151a4403000400301c8141039030394003603400740321001c0c91420581c000b034a0742d078081c0d10001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 736116223 1250 736114973 736114993
    0x6060901050d24020322050a0f032d020f01060819171207030f150b0f07140307060c110c09070e0316092009040506040b120109030807080402031e 64
    0x41c1a051a50f00c500c150150007104001c921805807404103546030302884044400401500d500b621104003040260a04c01c2d126094030a250190700d400f06001d10503994014031803e105c82541504000c41490401400341030303c1c000038a14140614400e03201010041c001d0340300e42d188241c1c030714506400210744208207030b01d180c080000000c01801404041800d41c040394503010b54010101c0b0f000e8241c890b9071500e0700c42a400b800840181362410b84503080d880541e1240c00c200c1c03180c01401550001044040f0302140e0703150111010014020303c43c41104203001d05074130404240c56150a50f03801c0b4580e980010007100300313454031280e240c0c1c204400b4145007882c200c1d10030109080110310800c04a5542240504000b001c500d440380c00d070540401510b1701420b00c0329502c00310140c1304050450740308644510103d040c0d0b5840b42d100519114001308803242001c4c4000b5010301a040e603510540125141c02c0000e08242c1c02614018407955004003d04007202811041c15060003907654030b00070621501c00c4103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 736117473 1250 736116223 736116263
    0xe120c09061215091501031e080d020d0f060f0b0a0503070504050a06020c0901060311041e150903120807051b010605090a0911030304150f052808070206060901050d 72
    0x91000148520380f030003528940f401e001ca2402c00380301494500b40341c031800104041042c5244240f2801804000c60a0080040c100320a45005000080511520000f0701001400e0550b20405a4103010b1a0a0000b19624100702d4240715107031040d0046080c0c00c10070b40c48664031820003513078170242c14100716060584810216081c602540c11900160344041d29844c0c15280140f042401082d0900d400d00603458040101003413070259214444003007641c00b40038040c2220218222010301601051072200400521004116401c00c3c8801d41e80c0061402c01070040e244554a84d900c94103094540c3c505d0080c42611404070f410346480441065583e84a010849580da00c036500d000300841d00011401d10b0140c144042080714840c9014801ea000f00810001c0c03950791224841c102c00300b4200494941e134840b13800d07a50741c030481e80881742c4c10307143d41c0a051fa0300081481c1c00308083e4103943d884c0203d580e55002665507000c00d503a8160300c6030042004000ba85000c44440340c445110346180c2c03121000300d01f10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 736118723 1250 736117473 736117483
    0x1b022503170702041b1409040608120304030906050703020316060f091209050f100f02150c0409060b16110a0b0313060522060c0504050607120e120c090612 68
    0x82102200c0002d0081c0075854640038a00359955501c010340050a064000981042c0b0007400f904840071020955070503075551613210300010606a0141c803107942401c0452205070b48226401c40c081440a500410510f10400503690003540c1038004500d40b44c03a1101d40b56041c1e4080000301c0c2e009485d41d411050703007503440c01101840ca118002d0141c01081c044c40113820004550000d0b4050714804d00850b550f90740c1c0c007000c0200c0c08014100b00c0307030344030341c100301203041c0031080815842c039183e00b0091000039000400104200d4072030f03a104120940e211842240399108440c0c4110000043d1020200030031842010041c041c40024180d05040b0f5458400c1c2c4035a400460744114040043d21218090000b00e000b030641c848100e206150b604481041084510010018041c0040f03949424940a403401001208c1c0509002468a900d844451034003608080d54150108000390b02c0b06001809400c107080d510680403000c0015000c030b90844401d0107080100108200d5203c1c00420034a8020902480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 736119973 1250 736118723 736118753
    0x81905100203060d21120c020c04090203030733020301060c021905041a09010b0301050d1b121415072304050d08250201080f040c080708030d1b022503 66
    0x107840c140b0171080410140090003c5410601d1160070080d0910f410340d4081100b0f0b10150301154001007400c690300100f4075500440301d0060014880d52003054a1708000c802d007000d4920040d0300c00c0a85c00409074498280c1c0428810480803410a194803401403038664888001c82c150314554011f0036545200080585c0c00390f1915481c1d680d950070100751345003009c9986601400700b50300d40c10f10f1940b5290108111013030191000e001000b40c421480b1020b03050303a80550041000400300060500f072820b00e42c4031402c01c1a03106200b84155503581c40f0440444498520605041c0c031030039100c5020b80c02524140d40000070185003820100000314183d5a2000610000c07406007800c00d84906290b0105d40600303012000c0c901071420a000e00c2c1d00140ea0007651141d0213a820003442d0b8040c1c4507460b12003070400650304040007901034950049013109c030000c040d2601254080080c803548030107070f801c80b101303000d00c5420740016000750a0458142018042454943c41901c1040390f095a0382e490b070b202d2000840c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 736121223 1250 736119973 736120013
    0x2130f060303110307020f01080c090301052d060109090e010b060a0207050a080316320c010905060f070605090f070909151503021201021201030b01081905100203060d 73
    0xe0014001d01d988101202031095444005500c0d12806400280100c061107103514100000b903000911504080404d86040c0d4801030b009100c1405c028410728000800302c2c8414200210303130316880d07003201442c4501360702407481030316546034890130070741d00502800d91403205010a649070004404180c54040007003210f1441ca501921195060a08002905a080d4001c480942c0f0900000381c0010008014256850b030110b407400443c031291141e005092103141c1c100c09078150715440c0050401000c2034411140400342c0e03e008005071100100000c50085600b00c0325144014045e28000884940c405900903820400b01e541c81414484a5490042c0c0760308401d0f000d030386403100314042108100021210601120702400300500508100c921000e09101c0030b80724004c62000c4841c2184294121001003d107269a00714542e100d007044680c5050a1182c628144505000300048440700184840080d81c040d021303100441d07003000c21101942019009551080c044050440041c901d100c09252203d204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 736122473 1250 736121223 736121231
    0x15090f0e0a110120030d0b1512181f150b0409060303030b2205100909080918061e030c060a1d150706150e13060c0215040b0402130f 58
    0x50b000101340d040d651030b090b0055030031013081515041000c802d0382c042d1841c4810005118030741d60006020000341c4500800065000101210303d450a1131405105030341c00901380c0116400030706029a0790321600d6003507548a041c4d102c1502407007010b8000360340c855140003107260040c5d251120316103a98400d5002d0050613517611001c004043c0c2500a40c1c0045c0701c11201401101f444007807a042c001e0310900003440309640d900004454404601d0594081d12590f0000c00c0500038500d011201540500f03041440358812010703c0064070242880240701b0300d40a0050711003009101020001440c50210859142c0100303000452591120b102800b80405242d039051500c400c0442162001c080a02613036000306010040c071001400d4030300844503200c0c4e010388000342078081d2203600102c1c964180c009003864a0054184550031405581c8521054020b4404002c803c0401c00141d035030314084000031303009146610000303011541d180e42c5994483d001516404140345903c0e042000c9441e00000c10318174070f9031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 736123723 1250 736122473 736122503
    0x70210050108010c0801180f24080a1a0907030b070e0906010c12050a0903060f0501060801060c050d1101091406070f080907050913060f1e15090f0e0a 66
    0x11030082500504810b8020071804a0000d00108060014040c80d102c0344400040542401020b40c04407000c40742140c010022406025407025030f10341807040c031106850281c3e00200302c038040481c43d08201a40840ca0102c0c02c0d0440250a100a000511101140c0650500040440c680d103010a205940300c1d640c80c88540c04600400c143c84001a04c9039041001c1c0c00507080000d182c0a03007071404400782e410003c0e01e810859400b1186911725400041850f410561503440d0283c003600454141e540503118480642e0700c0c1c120071106526140b00140c400d60105508072540c9004220421030240848008680c0241e503458100d078614419000b092164440c60400041c1a404520301408000e140750240072810a40042d6076200603c1c06030f280302d00410701c040781d4140c0154410805045d4060820301070750070000f949100a0080045d0001540e9a49000c1100c0325482c3c49043c02e4400103e0701c120741c8508000c0f9500051891005219405171341d03142e41c0340d802c40200310000005104004103059101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 736124973 1250 736123723 736123753
    0x90f15060c1e0f020901120b042d2003030703020a0209062b0201140711120f1b1302040509190e0a080d0f02040e0f04020d0b07050309010e060903120615030702 70
    0x51344851f90312a6408507041c00901d103008040d0300244c12a464919002e450482d0303030101044020100c2c07401c0c0c40c03141d00d07500700100185540c0360707140b0ba0441000108000400d1680340d104e81000240142c002ca002000145050b46a154000324003802021108006014040d8000b181c515841c1007440c2000307802d401c541c0d11401d00f2201c05400c400e0741f03003404501d645101c0c0c0c41380b85503c0c0ca4400c0c010600035400581c010408071800d24000c10480d007824001c2c2d003c2006145101c0c00060240f0303150001d03403000c4030f018000c4904039000542510650b950f500d000190120001d10105019500d540250f0b106820410046581500814415030340b0070031a5030480442d4032034928180d075180148030803c0740300c00400a10f6800541d044200e5070551312440003a49100402c2d10040064455206100141c1d51200246100d034450308020040000c00c007030016510701044590245983c0208110305046d000b0b501c041d81c00c00c02c0580b400c40c1c005031842e00e100d043c1d0401c42c4c0220040e0300201c0d40c2d0024107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 736126223 1250 736124973 736124989
    0x3031805061c050405030d1407080609040b070f0c0203070b040519030803011505120a060e070c0c1406090301020304030c03091707090207080702030f0304090f15060c1e0f02 76
    0x6000c581c02450400403500c1055204804039820036481d0361100060180300e420700848019203070b908030402c000d402da203100c443c0b1103100741d03415400920f00c0000507446007405450a0b000341e030405841d881c15580c801c0112180740440545130100400220740c00c1c0140c41c2001020301611119240c1a200c5040505004c10b40708012035212401180f42c10400205009400b02e1741516929201d200760b40c00448410364040c41080c1407034503460210340030007040462982c4108191895420000119100e40c4004c0b2210160010040c05269800e841004801c00049810381c0324030015000504101c0a60300003400c98004403410b0300800c002e000d01d501050f50240b6018040c100d03102112070350030b19207209190748030918090b04a880f41d00003545024003800000b500c240300d90040846011001c803401881d20780d0007034410b884901d420003105075040d486a0007030100c1100e0102c02102e1061400384e04844171140035070f06803401c0c80100c4483c0000c104010340301c0c2d86d442c003441c2100c84214451051155030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 736127473 1250 736126223 736126229
    0xd08160804080a032c0a0b07021f1805060a270c03060903090312120b0a1a03070c14030406090e1302010c050106081504060614030a0b100f030318 64
    0x481500100700018500c081a994050300c01e10700011103071000d40590100b0706440002c04003440c84981120003140002650307541051140341030804a48030760805076600c00c400d603100d1030003805880301d40f00c40207910b9000f803200c98030000000d2040b1903151121030810406603090321419449160101d120380040c038240c0140000389060101a28494480c102e12441d0b41c00000c01a50721000c22005251042c469040030715045404102c0c4041e0b4a20060a240701c11000280381c0d90a05c0c02103800d07440c1100c1a401150b590b07045080301c04100c441282c0c415840200504c003800645d132010404582071207560701880c42110011541d584c141000a0302400c50b45c3e025100725017051040000b24481408404040d80c0c0c2030034010701691492602e03070301401b000d8100300c4052040c541100000e03031202071414000e5008100801a06840f440c01001400039408041d42541c850804800000c034120807941d4015401c00b2901081610b40c1c04203a18220749234404c0d400110110310303141d07060038107420030402 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 736128723 1250 736127473 736127477
    0x3030213270e1c030e010b0105090a05040509161512020307350a02220f15031b0c0515250207050d1b09050403051215030d0816 56
    0x1030a40c8026854214a14002640100a44840002c00d8840d01084400014807074070348144800600003800030010401c0e40160a11503003405070300d6000b54011400c444900c01d000e0091a11075040809120140c50040c0034440e01d442140114505009031403890303001f404d641c540b02a503003403988000806500765014000c0407584104141714045400041c0541120101a0542c0c12240c140e0708410b03081c515400c0030f880c2c41075001c04204403100c85600034040c8500201c041c4880f160101e1107075074654000d000f13030300c1c444070078900a110002c0c0a5000398280c160a15021070700f842010014007415403e03400071000303d00e0240f070510030007a0034440c2440c504000d1b680da080e80d14000d403018802c4214030082c04121002210f1030390b8410301c2803100d00080d05020b0401600c1f1619480c00c00c40d2604080340d103100541c2c0354400415042e0726400303a04c2c012a0581d98680c14000b01140d22400d80b04081c101c8464000c422003c10411b031424050445005a6901e0f00d503031601d403035404e402820115450b8202 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 736129973 1250 736128723 736128749
    0xb0109020c03030a0b060c06100614430309090f0b01080609180f070302010f050a0c030e0402040e180c150d0905010b030f0d0306060905090402040e070b0703030213 72
    0x3440741c0e00041038a5200d10184400310302c0c1c4032190007199440c802c600021800703000d64000c10000d028494610000c41e2000d0380c4461200202c4a8001c01500603001c1640c0382c2483d070b1550041009804154030710441000904c541e094003013080c0b010021140f0036086020524240003001180d280c2e129031800598030501c1407141d071818400003400c0c520010266803003541c1c0d18000c88d01c0700d0310054400350140420401c036104000f2a007522690350044d0f110403030001d036140700c8091030140310b0404d4030031120603521291060101940c0644030a0b00c0c0b003484a81103a421300000641118640b4103602840b140007006240e0070088420604200801da106070061044c4446403101c024007000300d0780b0081752041c0005644406141280c090b0825010301a41881100b540702d402c0040400c0911165035151020020a0368580082c1c0e500300e0306200d215400140c0000007009420950407030020200321206442c4025207900109403590007014050300000c0c2d012034091881146514103c02500304465801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 736131223 1250 736129973 736129987
    0xc0f07141f09020924101812170c0303070e0310060608060a0504060b0d050a0e01050c0c0714100c0203420603032a122203030e1903020a120b010902 65
    0x2100705560160260007104020900800f45100c0c7c00486a1070714a4241c1d00c8000e5510303850001e410f0310054040d038903440742a1a810380071200908540e01d40790803070065815540d413840c0c241da004120584503601802000f170148a41d251611400380545082d4440407058100581070100e58640d03900400c1c02030707107030190506c00c8802076410b03264810803446020550760340d0344a20101a06c0c130041012440d600341030610241030344a001078802c005800040380e204a40d1644515450310384007000030b41003a2402505880c05126105e100c10440c009001c0f6529142803044a148200c6104220084100740e2600e501d45a0b00849034420f0ba0401c4c049160440e0034407100180d140c0c4130744120040d00192803203c20814540841c3c50070600500710054030441e8503e074207584042c0c0d00c070001c808410746000140c1c0c4030000d48a101c0b0416a80c1550702c10100c4800a410302242014448142c0d4000c0691400000141e90b01011500030b8451503404000c01c880c81d1400b28050303403040c1c002c8800c690051042d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 736132473 1250 736131223 736131271
    0xa0606020d0e030c1309060228020304060c03050703020a1202010b040f0213061808011a09010503060720010b0d1505010609030b041211030c150c0f07141f090209 71
    0xe41c40704c420131907000d030340c0d0400349101724002c0040e00801002c290010030b1000041c684201d91035040c0c881200079840800802d68101d88030322450203001c020803601507101005c2072180c0003404445100c1c0c011126040d115031160740422003001c14001c01030791507106850040c105801000050300c04030f01c1c10340c2082c14183c00a040703083c2c6030042d0400c00c00c10300350118528000135400c4e0001c2030100c008208040800c4602c105409900225074081c4030b03904000a010700300090502e120340303940e40c0c03241c0003542c1141706041000034014052080e0364075074101c40e409a40d040e07580c1c510544940d6062008160b459040400d85405034052401d000801c41c00308041a901e002003075010342d10503800d480310320f050702040d02c2082c07200007084118440031842c3c0400d580f0004091050558800d1034003410340d0f80e811500c29601c03440310b4001d0030301c009000090026200d00319100c031040c41c0d0310a98480801c0c0410403100501c18500e54500035071582001015802c0112105801010108030710284900d280c0e80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 736133723 1250 736132473 736132483
    0x5120d08010b18100309110f06030f0621030409060f210303020d1a0f04020a0203090d1a09030a030c030204140d05070b040f0f050613030f08120a0606020d0e03 70
    0x10380501d04100003000d0400200c0900f0640c0c988030014a44500d14011900090041186c0030044a04068a007410070741480c1c10110315006400003040c42c0d1840d5201145107409003000750000c1c0e00580000800034880c850a123108414144680c000c5488610300105070301a02c946c0d078000c6804210f580301c01c0c0101c0c1680040000000c41144050081c2c001d249000c500070302c1081c0e01e0200941c40c0200048401011503440104a28111207405052500c6420407040b80b02c0c0c42e00640240e80104034084250400c20412203079103010380d42c1c180c0e084030440c0c040400035400701e480d0386542d040010b800c1d04154051082040303144240c6001c40c10681020a0301d90b41c2d048140301c8510420001000c241001002c01120000d020781c400700e01d0300c49995041008945906001e541c103240345028000c83c107400e090381a500302c5180c12480c0a212465502e541050392480c81050b07500d0101080240741c0d01010386100c50042c0003284002521924042000341420202d5400004000100410868940e00050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 736134973 1250 736133723 736133729
    0xb0604030f030804080d02160203010c110606010309050c030607051c0b0303031b2236020a09170303010617100303050306060421021c150c0e041505120d0801 69
    0x40115490320349003001c94140c0200402290113a000180c5d803490f82d45d502880b10005440ad4000f405290408502607401140c20203049090b5485440002d03040e620070b0b0090b4aa0314024021344421500c0000824140b01e000c81e8483c011400004a4001c14030a03e0080c0901ca40d80001c00c010000751000081c0e12844058449403480c80c0b160100100c00b43c03041c04031941e00054022013090310920f8501d1a01407241c0b481000f0181413012381c4207010200c1703c44191403c00003100080f200b02129107407039000b50089a65141009000c0a0108000000d9070f4540c036a0180c420040d070300ca40c5403220091200f075501c5c072400350900c403001c148580c650391041004180d81d031508149840365510ba0120301d15001e9503000321000c0d0804501260582c0c0c4840c1d00e07a0445000340c40d08404456000300d0700b0100315075030714010401441c803050440c26a6040d4407000c514000c6150010104d04450001400e035655901d81c0301ca402c03803880c000c0100b0300d0b085480c801b41808507009005030841c8000c0143c441c000501c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 736136223 1250 736134973 736134977
    0xf0708070f09050d0302060103020102010f180f0302010219090e0604061203080402030c0d0312060803211012060b030105010503060c0406081e09070e0c041a0d0914030a030b0604030f03 81
    0x19001e805100c0c040c100030005000040c110030001100d42c10025580c440078070083e030165191a80c046d030030b840280190700f00c130050300c5035908100c2c226980c8c1d03400d204c140748019000c55609210b07034048810000100190030304140d0b20040c3d46410715200c42403500001c0d0106100c1c600d803200802804a0000410720b600f50141004025540ca50012900701100b00d51200d40c4041c1900d0800c0c20150000640d030881541c28401708100c03600d0b10745c0690f50380714505041000a44207819401007664904a05600c0f81400703a0307001c91169207180403100c2031819141283d26546134103500086050034440d450040c00d046000700000d007080414076006e48110300660040085a00c0001d20482d106070308401c0380c0690806406046c640110020f071200541e000e00c00c1c040100c000401c00080e010001c1d01c0c199a000c40402e500280c3c0781448181c0f5504c560740307003843c1c5500c41340703030001140350b040d00351400380c00b56006190344801701c000c0141102c000b0100071748038a1050000b0320201d800c40c901005125414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 736137473 1250 736136223 736136237
    0xe01050913020406050c0f010e0307022101181407030255060f120e10110903120403080315060f0c0d0801083903010f0606080f070807 59
    0x50408940401110822000450300015000500b61703848002080702c80446d20a46041c5900d4005890a8821084502c1402c3d84107011001c050b103828250300080e40208002d0403000c3d56098885400c0d02d01c4140842032510356080c07505e007032000c0c9080000d007201131030000d40368850441c2d00080c1450000e094400c00c2094000c030130041401c2090000940f000d166001d070413030b21800c8030b440100c0e81440c8101003070310b00c0c210700001b490350181085080c0b81860380c83d04814008d261403500b004109604a9681c42d1066040301c81c0309200c0d80c4540d1200038005000c2966520355002454071b0207003c3c15070016802030400c000c102144420003034036000300c661100305801022100000d0100d001c2c0e0306c052400f4000004404012000009160710790300314688400c80d06a0340c81c510300b0f40f983c0b403250284401035066090751980da0308d180c880c4000958900c2200400c1c056a0010030f003107520110b02c20850a5540a007800100e0304840015400401280e810343d092520a46c0200100bc0c050094030500084c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 736138723 1250 736137473 736137487
    0x101d04110112020304080c16030b04020906010912120f09080a0b06060403170d05070507030e190909060501080c0604150f0516050a0308090d143a0c030b010e0105 71
    0x11401404011407402c1c0425902c908050a00307030300a80c000014404d003842003c00d034241100342442c488040300d0300314501002d1903845400b44641c4110040040f0704021003004e020a250075442d6900d41c80d40d000d0340140080006415001e031804a40c83c110200303115051604000e042c030700184050b070b075640c482c1501c480c1d9220400860111301850f00010089a0841c4141802e41c020001900f01d00740020b00602c4240c41d0342c0001c0e0769500c1018006000603540d45014809801e11041d182d12b016080324002d0441c507076890105040ba40d4001c401c0340d06d1522440100704e00d49080002c0134002404640700da00d001d15200072115110901d4004105214610a5030484c1901801c00c2d02e0707481c0030902043c1d01c161411301e00a901c0301042c400c1100420510004030781e0304040021285205c48031038071800300b003007442c6942c1c8410b9000280001940b00e501140f28580b0b408186d04a59003440310001039030045000d2036100103541c84981100201032400103440c50503070348803202e22107020080c00d1269550700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 736139973 1250 736138723 736138727
    0x5010b07030c15050c07060b0a05090a05091c0f03060f080a0b10050d0f0203010f061a18030a0b0403020f060c04050402070602070c0e1012050d0810080a0803101d041101 74
    0x800250310f000c80c1803074a0100100048510300130b0103143d10942d020480403c002d0100400c88005000b070701d070000505c81c001865107240358403c50701f012000c81140c6c8c0d02500f00b620b0345045001d8400b0500011842d000d141249601030007071074080c0c00d48138500031006003081c00d41e50362902e036818068081e030322400c0882c00d181078261001002d41000f508075440b495203414421105103581904900070742c81c0070702c40280d440d900e01c104010303115070018162105450a100e07507400c0d080002c0111140b6031030b0352102c889607810410621424460b58105180e450a4140603041000c40314040c1e965410410400c240b1480d12001c540c1a103d003164018ac980b0404e0420030300a004040005040410080b00411540343e01114280f203504176454616140361106910301c200d01c0e851100074110340c4010021828503004410340d603400054001c459400c0c0c0d07511140707075291800c910010f0761124030010078800e2490301c1050b000003030300d080000260ba04414486ea00480000140060041100b860140c0c03d20780c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 736141223 1250 736139973 736139993
    0x10e1903140d15090e0c01050c1006090c0201061e0e15040507030b0a090903050304081b030d0e0c090721020d143c0a0b06030408030403030c0305010b07030c 69
    0x6166101041d224590b04055000030000306140c41c03090319040d600050f1141950080041207814030026010304500c01c401560540c101c40007100c100d0240c0000c0c0c050365104c40c42400024140324802103101c400040029003140c0f4540c010b1040701d440880543d0b40760311031407856000c4946429018581d0744c2d40340103003102c0c07051107442039230b01a05000c18456803542c540c2080758403c40886001d00740a66405521003220244100100850700038000540400d071f00c1c03400350282c2e15440c0c0a01c1002890301d01c40b181154002c145c1c200c1c080f41d880403030581c01070040000414a01044d03800c40c0e840e092021020b031248410381c0c10041154016410300111499a805803040b00404180600520020414001e6201c2c0221032501e4510ba91007461041000100149900c52406240071032500780744200004603a80020f0400c400310741ca44c8030740aa507444400c01036214174000c107011a01d07400c15250040c103445241e1100010141084014803481d0624801c498050341d160601103d00f000d01d10b46400f0755 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 736142473 1250 736141223 736141247
    0xc0c06080c07151b200304300812010e150d0609060e1b0f060a170c04030f030f1d01140702180f0402030d021501060f03150b040f08010e1903 62
    0x140c42d0141310080c0ca811035070085501001c103515105022006110b00d41d240640c1c03040c4a41d1152080b551115480a1100280e101c40d640d86452455407654a4506850b0b0055002c612840c8445004001300d0321801401500054041e0f902c40b0000c0c18600011520010000082d02082c0d03152a68400c106956000680301c0d15980b0588401540c225000c4500d900080ca00500900ca80421920700d031074407074120760028071a034076846c42d12012041812140c0f04010326030420a181004080041220f00d40303504d41891181e95180c440002860000341180c501e00c8403519003130100e50421000341e030468000f003828601038990585a1049000068511480442e400000e461090600030031540a02c9001c0c8103034000d50840300700509014080383e903000a681d150341c010704103500611459204001a8489584600d40410303055051007201041d0f94980c3c1c00084282c5002404100c0c03028010360100090003810000c105241050704070300e0310707a000e06c140c081e0841f0031a249041014001c490050780 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 736143723 1250 736142473 736142501
    0x6081302010e062b110304051c0c0510021801020f0a0b15060c070e0c04030c030312020f0a0201090606061106130f08120709051c150b060a0c0c06080c0715 68
    0x510a440d90707118560118650f224138906007040700d03814200f005442201d006561007002000f00710007401d2a0744401c2040340058041290300d90604010032010400222003103101800140e580340a10a064512040c02c1020382c103541041036002c26803680070617007a80b80c540000d645081e17556145c0c20350903010020240c0742d40c03143c40030900c02156480041c8610a440c040c00c08108503482e000715101c00d43c01030384001040340031808000e0000074454404540a810f03550f03400350600b800049139074015046809500010313035440c00e9010610003640607800003882c140c2403107410911411441500e074080101141c00841e52070500d1010003c0d07c0010341450303500248003036180d84104103102d2000c8400d031075403030003d81c625401280a15040c4441c0308040c0400e0882d095041c0d5a0355100340c0c01d84501d030400946542e90942c001d03140c8030400104814942c40d030310441c881c81203140c01d41e0004d17260b07085034041003034601c00c11441242940850306056044201d01c0c20052412517503002034405450070b412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 736144973 1250 736143723 736143757
    0xa0617072f0a11090c0d02070206090604030506090d050315190509010617011a07030c0515090c120d0c1e0812010302030c0904020616050a1a1006081302010e06 70
    0x1600700700030854090551007000004042e195050030031010110545007072110003020400f802c100746040e4000d0001901c044d02c0c003030903c10050006140c50f0040d034030590351904540d0402c1b20811041c424030b8000705040c04e000d800c509010100c0302d500d80d941c07003525008032810003a14a00c144c1c102c40c103100070070000300214500c3d82c4854004001f03c085055060341010103030300100c1c03200008510725072580d000401440c00c100043d14100c03031001c10f800b03055900f8050090f809400c4081084041c1c800c04066009050200100051200f1b001080c0c481040a0b0041480f803081283e102c07921840240e0000c0301c141c07849084640d4240c03944516500100000d5002540441e41c1403c120618126030084090b1402c4245400902408000494000b58000c4d020403e070f036082a007400101c0c902a010b20100c5514113600e03a186070318140410310b203090304040e002c01c111500c01004506000317001c40d441c2091550900c1c1c92103075582510082c0082c1840111801602903855030801d44140200000b1416 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 736146223 1250 736144973 736145057
    0x504092a051002030405031b060d0903030501170c0d1101021f1e0203100b0f1b0c03060610020c010309141603051002090a090b040b12010b0a061707 65
    0x20020701c0358500034010b195031094a54000300581c0c1c104c0d07001601814070050400300544002c6440b03201e80e90300c81c50a00c6403c10303000c8144030748101c0d20304caa2000100f80d410005402c01145401030204c68942c4002803922064494001951000380d00092140d5a40503070070050741001d00310006100d000030406103820840c803d50300440303080a84903d050581d132031000f05290507407204491140c0784140001041051000f03a900400344145002ca0300c9013401c10315007040400240414041d84183e1104081c012585800e110300354002c1001c0303803a070038240c610302c00203522010544041410306580c0c0c02c05034103110070105040c200f48008800d07603506050004004a4240850000340c61522484203c418800d01034421610300700402084541e2051802e8070f03000c00303002c0800705c10f90800d0312102c198840e40c4070202010426410300001140200d10b04040c081c402410754059000c00030449800e01e0354283d12012190402c280380303403548a9200403030001c00c01c000c00d164818111841d03d203040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 736147473 1250 736146223 736146293
    0x510060f0b0a05162009091c0306050315040b060409050604060c050403120f14040602100e03040306020f1902070e0414120a0527150304030c080301031505060405090304050409 77
    0x2102c4450b5445d00145504200050200410b0101c0d00010f469011000718021b01580910b0103108185034a0040303605525900420300300340c00d0741034940e14800a40300b480300700103400003402d9210005490801500c80a42c4403d03944004c00380c000303030005690b50070109060344600f04072030181d6080010509050a1604000c019148140400000a00c040561070041d10329404540c00c42e4850341c010441e060420480b440100000c0c3c904110713500c41040000001141d0340082e00b68840d016507121b403640303080b550740220844108601811074014a500b8440003502c00031403500203402c00c4001e000031244000f04d41ca00b89038110084085a00401c10407100355020300281008040001d0121000c00c0c0c1c100030f02d00034a074881806500a5003001d2650703814094101641d400740c028600004105030540f19800c01d50300a80060790a40b801c07880c01da500b041d041c000d49406c50001d913020001450000d1805d901e81c09103015181c404c07a141c03804601400100348070344256240c018201d4003500302c41030032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 736148723 1250 736147473 736147493
    0x150426030c1b0106050f190314010b10020d020d0c060e0601180b0a03050a0602130f0f06090b0909011e03060e0604030e01020f1b28030510060f0b0a0516 67
    0x1d8102e240380420000e035400e5030601418088440262448091842103402c0081c5501600340007102c1c01421200080496203a11b902c54508401e28000540c02c48594107010400000000d03003010b65008000381200590300194402c1c191400d841c2c10561888149040005062030110380442c900c2140d0001c10903200c002c1c40400413400840c02007154103028024001000940e200107441a009004c001002c14905e4005001a00729440903100841d11807405410610a5030000c400708844c0160a0100a030002c0c2ea036805040101003190030005241d0005020328414091402002032000c1c0c001c2c0103503510b10650002d0369101c50180042029030000c1d55542d82c04650550010b00300d121070b18007950001c90400c0b98000b15101410341c1d40c10410410a48003ea050b041e81c20912920300c103504440b00c40000e80d1074075500c80c0e0514209286041082c41c2c09458071101014600d007000410401c080b0350b0402084580e40c0c0383c00d50721044042d1040d41d103405803e0104e5103203569403a00c1400c004080c04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 736149973 1250 736148723 736148737
    0x80114121006050a12020618010e0d080409060902040b090f03210702031203070c11010e0a12060524010809031317010c1404060e030705040c030e0f150426030c 70
    0x80714441181d81d072035600001740d12100c02035001101001070a000d41071509a0b90b52501c0f06040c5a03c0d052020800314050310b02d088020380345044007003418001e1429078010310004092815056080500342900070b4117512641a015105080c0c02005041c0c540f41404407421040e0240c0318201c01941d0140c00203041d0b40060300c200d1190244501c030314407400d5180141c030700030f02842c2d42e0240ca4210541e2280e41210703c0302d8400c1c2c10702c12034001c201c000d65540d080480140c2242d5007020040ca44c60302d011015a98040e103d0307444000e01e4080314504011500702c041c079424007464034020716141d2065080c254402c501c80c0b61149589440b01060611421a2041c504103070000204407c07052410308494820740440b0705941810308001c2040198820b13294403000d00342c020151800c855480300098115002c016116021a49038004420070380018482c1e0038018507103001424030541180c100c100c5040006200401c0052102e4406a000702030785003203c5c0004030008256071347e0400d09507540094000c0c03c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 736151079 1106 736149973 736149979
    0xa0e0c0c1006180b01080712150905090a1203110415020f1c0201060e0103121b050d020a0605130c0504050712150e0f0708011412100605 60
    0x110580000705412510505404280b910f003906031801e1140a5040c440c2c10801c0000c480d40081e00369540b400f000000041d10280d0803013442192a19400010390036182c0810411710300c1000801c04011401000002101c038010b44c021415180786000b842104403060004001404540034103240c10281c038015924600410400e2901d0400c034402414003010010354030010640d028840c07140504061b0100c22404d41c11900e400440c800e20803a800c00700108656420512001550340d06416980300f4107039002c00c42d00940080d580c8449038020b0b41c0b0140b4100100c1c0b96500b03008214100541c1c440c0815003920b1811081100800000703148006100d20700380400d0a1050922600b01280190040507404500b4a920005c1c442c00c020409160464103c060200c0d030741e00001ca050440c0d5040c16104014008400891100486010a0381051148031120095400c031034110400f40e81040d = true := by decide +kernel

theorem cover : BRFrame.Cov 735971223 736151079 := by
  have h0 := BRFrame.cov_init 735971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735971223 ≤ n) (h2 : n < 736151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
