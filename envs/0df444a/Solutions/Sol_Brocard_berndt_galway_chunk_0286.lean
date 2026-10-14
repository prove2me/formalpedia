-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:58:12.982236+00:00
-- url     : https://prove2.me/submissions/4bb530b5-af34-4c02-a0ff-623bec5e3ea3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51258996 ≤ n < 51438852 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51260246 1250 51258996 51259007
    0x60d020a050d06140703020f031f09021804050a06080a03180b0d0b0f0306150d050c03060403050a02070f060c03031e0c02030405030c030303070c2301090f1a01032001 73
    0x1c0c01150720000d000280402c001a680080209031010803100c2041c0d2143d45c8240c2c10b074052104c0e203c403e540240005400d4182114205240d804480300c90004180c464080400ba83d00008004858034990041200e031414140300c0c4640c4614460002c1004c0c0c0c0c20101d519031a9805030402600700000c41d40141142400442da910003481101c0c0c00b507541d444d0300e100040240140004982c4a5400d21700812114140859564031a81c3c040f10402d44d002d6490b0100b182ca0319207050251228070816020140d652000c00170b50f80114001e482d00b41c3c0f103042d5410003d1411205401c907019022010000708040b94000019085480d4076080c04541006450200b050400300240b4030354200d400c14003071401c20381d000b10052051b0340d0240c00743da0030340954009155880c441502c070710001135001c1d244c03940400d8142909411141d024281c41c8840c4200e0303441607094895030700e0191031440600400e9400c004c4013241400b1160b9054031021100d42c55030701c0354428481d000076172402c055150585141e4a070f00c82c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51261496 1250 51260246 51260249
    0x901080c0d050f190c091701090602071b0b040b04050904020d0b04030e030d090807050103090312020301030b0f0f0601020a1509020607060f06081606050a03110c06040c12030503060d020a 82
    0x5410409483c1038070145030081d03416600c0113034100b1011841e4110021034080c0004000707030b0ba161041141c0c54444941caa03000c1c50707001024a5542c071901600041c4940c0003d120203402911300c2141c024000d03105101c803013403da01c03207403c07224200400c0241d4803103607098404807101242d070901d06540d40c3c00072400760920584000d0a04100c80204000c01d41c0240c4160a681c8041d0112011000381c4681514000c42a0141c01c149500200f81080203621a4220701140c134031a10b070a80c46103a60340d0002c01640c2081c0c0085561012001c2007026581c1c6510b50705600510030100c01896044c8200080c1d114031000c84050284011581004510300883e003201c09056070103002e06598041c18240300c0c00411035071b4240b010705418a600003444240c0080c0f0780c04050390304d03400200f016240c4001503500e540201e58600c2816151800d0188100d5845e000e898425051005081c0e545401d2818010010707143d04803001402d80117140300301003503012007074030740c0300200340d03201e500c02541400000c0007200325 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51262746 1250 51261496 51261517
    0x10906090e01090507050712030507110a0c0b070302070f090b15040308180307050a0e09061006050a03090c05060c0c090615092209050d09080d08040b06040b03030c0c0307090e030901080c 82
    0x10601d000c0488c95045c1d00461080c0065543c448489000803c041c0d141c100c000406454564011403d01c81640038800402c0c1491180c0112400d13250f4994858681c41c1d60740d0b02004617030780d0f5116003030701c94200031044a1210510314400ea14007810f540d10812580030b40440e1218041071070401800c252001c028040262400800d600c0c100f0382da03140382800100c000c584cc00018007500300880d01050848200e48180d17801502e03000d040a0740900d08500070900c11a0955216400c41000119500c2e040c0081110700404000340c03c42c1103024091107000000909110701800452401360030708858141a64206172044410341d15100c50a4200302214003070f4190030160754a0418550704210001a40b2142d90310b00b525581641a501c01c01103446400e0360710b407076002c0f504100000d0002044541a15800003000f00005591007881c404a0314640001040e0141a84000b460794620324007000704800401106500303001881c2210b1700c00d9103d0054666407814020081c01050b00121042c0070b84444066 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51263996 1250 51262746 51262763
    0x703020307120c08370b0f040209070e030c010e03010603060c09030b01140102060f090f06010608070311091003151e0f06050c1e1002040e0105010906090e010905070507 74
    0x4491059141e0000d101c501200c00034101c190020f408880030526041708180c040040300d41a0702d1882c1d00d06801c209101c49580c0604c01c210b80340001e01c103440007600400185203140c00e02c0c5494414010310304005480c0701c09000c0560040c2e0010345c2e0006064034440700c2845c2c00303c040007a6102113401b400e41d40d00010056400e100c1c040705200c4e8030a00280c00c40f40a003080081c070341d81e00c45074510b40024a6074a1030040c0c00020006540600c5180800e40205100d000c486141552071466424010203810641c001703004c80041c0802079515025015002a0501c2142d250501800003e0f241c00c41d4800c0c0407043c9515440d04080359081d04044034001d04a104002010410078500c140050300d0742e002d0342c4d5400c91020004900c85206a080d558203c0304403000340084074052070041c51464040890380000e10482500d0048480755002900082c4060a849003041d41802d00260450342075401940400901c100c0030808007440400050445401d05000541900c910b50304a465209071034000c3c001c0c58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51265246 1250 51263996 51263999
    0x60a0b090d06020d020304020f010804050703060506060409050a0f0f110306100e0a090221070e0d0c051002010911090402060a050309031e070201120618050c0d0509060f090d1b050703020307 83
    0x70130a80055204602c2140c0d54030010303801070019100c5880658010301503901000080c400103186600458020100600c82e5003041c3e9120701007000d50b40c04461441c0c1d142c2d201c10004003604101c0c02002a0681c0700c078010310111801070855440381c040142401d200c1c1401030b20480e0120b024074000a204000940162070498648580c0c0000c0e50100003142c200c0940f413424a10004002030030b8501074480799231801c0d151181d03c000c2018202c040c80041ea1300c00003282d0700003240e0750b0340038681039003001c50340020510704210b042c50380903038121440e494000e07002d803c104401a036401080761880040c9061040d10790310b40d5a0030a155010720f10030030103007102c1c002d00b02000d117102d940500a8903100b6030768607c030345410b00c03420419540c583c4038103030854481509078000035006400c0240e001d0f01050900d8100410070340690180c0c4d00940d0748282d150845800d1089880d80c911f44190720a00a5000740ba40b4141c10f50700601d00c0449410218640c1030402590040000500c0008010764005041b2008036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51266496 1250 51265246 51265267
    0x1050708071403010509040303330504050a0b010c030f0311040b030406050a0e0309040903051201090902030d050702060301050f0621090d02011416090801050c0307080708060a0b090d0602 82
    0xc0c000e03901800800c400700810140800e200d0b04907416248042c103000c2490f19540e82c260b0250640704050f01d5001c042262841004500c091a8408450200d51400e1580d107410140011100e014007004851801c002c550440303641c00040404030140d244c038001003006480803003140140307400d0381c0f43c0300300e008001000500303584140041c0d40102d00480c010072003500e661542104803a100000f40a05801c240514981c0346056400401124000e00f001c5180005c03125000f241ca410907000000c03219074818046041d402c007002401041c01c1642441032400359290000f070803d010522820780f1480015440075403e03250b10303082c0c030707854507410194414880440c500d00507040c41c00c40316080c0e144158444260028030502495155500c1110400e840f9215001800540f034120090b03c020b014507880d0000300403000740b04c0d9a1040f03140014283e10380c20420340007407400b0030151034401001512000e1124036510622490f01b00c030701402c002a0b64000c000007181d512028820084e05051011039074203c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51267746 1250 51266496 51266507
    0x705030d080c0d063506190f02030c1b070e040f02010c06050403030b010e0609060301090209031e0a0204050601030b03030d2004060c15091703090c0d0614010906060c0f02040608010507 81
    0x102d1400e4030300c0c600500700303a05c81c07100704440f120516200c0c0ea1088020581301c20009400e01241e005001c40802e0510030707001004184e9006980c80c04a01800003140521408082440801c29183d1000340c41141d2401d0b14840d0070090240c03000d4407804c3c40062900843e8003c808516074035a1142040c0154942402c01600600a03042203a0215043c00007075074807894408201c4800a200928060640c0d0170019280d000b90094203001e0b4140c400c4410007061a60038146074072100781c2a20061030359640078030500c82941e00107040541494100082d150590360b01200f6100e0b40f4111041c0003580c20042042c0451941d40f10f000190f21841c0003030049001c1d035210300207624007401058080e1803918240002411561180380240a40912125000ca115002c0c4015600080c0c4c81c01180c2040d90171a00042600000d42c500316602a611240c6403400e020115600b401442c0e401020484180b400c2c0020f03017480e0350305d08001d0205a40c074004400f1540c0f00e6000c1400f43c031601c0000c101918003400040c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51268996 1250 51267746 51267779
    0x10f0606030b130c020d0c14030408160504060312031a1905090f040b060907111218010c050c060a050f19020f060403140715110405120705030d080c0d06 67
    0xe00501c18003c5400744042c0030b01101008640e0003840e100c02e2032041114003443c454411902d0541038011021108403c2025001808140020704100020b04815807074800d1513030b0060b80224144841000882d8090142c003410041c03609012444912041d05922240c5010340010345c8411129017860b2401d102d00b4420059070f4042d550524240c80b204000301030711008880080851402c0740019016040580e02103412142c0d5040990034040d0407510141800405203624503102c0020810340041c031084d08070b031454550207080000c601a6541c03203442d113945545031000d000d07800c00181e80d000148103000b25042c00810703452a54a8443c44203d03244000d101484030801403044071940c031100a400306c0c40b039008540c10344680104144540e64080c403500040c0083d1503048114070041c03100b14081c01051006152001c04a07a56418001040700603030f2002d5041040340d201c3c5105016688000810800001843c1040300255403021550004c5104060b01d42c5074050902c180001c80d0081e61781040d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51270246 1250 51268996 51268999
    0x804050f06030402150703090801090602070b0c0a0807050a12090605010302010206010e1501120e1c08010902120114030c030a06020a030516050703030f060f03050303040b2206020903010f0606030b 86
    0x42140e0001001c105203400290303800b952000100f030200a21210040081c50818400e0500340005035907500c01e83d003120421003050307404540020b4208100802034644a50064002d40501e0030700b10b00d40340041510710f006200c1c5050207400a8150b46a9000f15a1600d0a162144041c0308403241e5103001d81c0584000e11040b40075208150011030400701800b01584208422010501c0c1c04060a00440c0c041c00a9181c0c68050783d500c0c0b07040e40c00e004c0d09008040d01000026030840245d00103420052424005a021221540c814803104000050058010f411a06036181d00c03614000340b032000a0500000c0800d20394103225a003001010440740781c0160801c040d0f541c8040001da6240001c0080d1000c3d5500c0410005100b0802c401c0040d0090740440702440c0741003800182d02d915601c0080300c004132500151807692003c002c0200b003214004c8025408032103404c01d5600311544190151070303030451031740003085070303402241c0325280341c900f540204070038001076100707000c00741d520540980140200740105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51271496 1250 51270246 51270259
    0x30406020f0f060903070605060109050604030b100b16060b0307080d1e05120f0403030603120210050a060f030b04080f0d0221091e0106080312160e03030f071a0103080405 75
    0x101c0d89058040f801c14030485a050203986003142543c1ea52006050081040303041c0010860041000d446003005040518426040e0106a0030720100e034083c10318040e032020015040403c050812010214686280e082d4031030000704055600324000b900b070101507000710059102d001018079441d54802c03100b4594940e040c214440400d0510011240340c07003240c0300306800500d03510100b00426442c44080317501c00e01a140000d40710b61241c0d1246645c402880503840168001c580001c100e07640b5104443d003181401004201c0a40340c01d01c4650b5441321807001500d840d01041c0002c00340040c00d411284000a440a01543c035403101c14580000e4005910700101c0c001d4a07850b984501407c9507860780910b20140050004034401c9280307510540b0b103032644c25155520744000041b030321401c001815041e0485120a129480d1811a04840e05030031b070003034400c02c96903005c0b1a4260702c3c040112a01c00e00f025450316543c0b0340300c1c200340084130103500744000825a0800000140040e0b64050303c19194100c410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51272746 1250 51271496 51271513
    0x10b01080106021c08091c0509030d08010f050405040203160f14040509150c070206040b030615070f031815120c0e0a140f1c02040b04020c0309010305100503030406020f 74
    0xf01da8611144010341c0364900101e02c2c500107640507482e40c95000c0d41000490310343c0140803400303d10010202c010742c00840c40c00f00d90111146020700c50403404005c00d01e4041031035813500c009041c0241c0e56105103400f465843c3c010500b51344081c016200010030044e0034940ba035580e0f441040c8506030394422203c49060715400c071000f524080c02514051a24117008104240091220801000018100c031000840400400c80140c031200d01500c0100200c40700c154983c904a13040c459240d01020000c40019070410080c00010010a10b0040c900c0c0c040c601448610106c03c90003400d2249500600c406110303d054408000307602841254101e078000780c05201120400e074042d2091110101003aa002040000a1002d040e900102c03815807100101101e031540010340c04500c03031454440c00b10710b00381720030541c00701542400d00841140b41402d076402c500e0401d00840a944a004120b6501e0415880d4404558209464100300c1701620006050381c1c0d817550350b904080d607036501500500c0860301500c0b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51273996 1250 51272746 51272759
    0x120506040b01060c080d0b0109050a0e01050901060306082104050909010902030c1e0603310302070e04080706020711030106140a0e010e011e08060106090801050a0504030516020f040c02010b010801 86
    0x39203159a03640110046c1c2013001000d002c02c0540400034045041044800b0005555559490310360001c0c0381400504080e0750500d010f200120740141c00c508107240c10b00c5020040c661001460741d0480000004103801c103105420000740512135548134590105041e0284040c03442c0643c042070005100300d04036010141d0401c10f2104050361050f0750a92030380e065226074918100b42004503070021120048951000c4003a0051400c0c0d40c85030210000f0003c4401110109074042000074040c2ca0300d40c81c101171501c0c080d91040910301c1012001007080d50003060341e03006c100175500c4000c80c07900001c0007070002d6034443c2d003448410740102200b18400c0760043c80018541941c00900c0b8184e4151107046412a801e00901e00c42010b0340c9106111070741d501ca40001081030091000f18041d01040e6076142c0701e02e01e00480107003036a80c06009650b250346800144400203400800f1540b01c090700504002540d150b5000183d40f10101d826660381160030004854200d642c1940310034885e03003098031108616601c0301c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51275246 1250 51273996 51274007
    0x31f140105100309030309050109030c05070b03190c17240a03020603040f02031e0303100803030601120c050909040b010306050903030108030340030201110a02070b090307120506040b0106 82
    0x810240c000810015101240703200e5081254082d00030300300401c011f402581d0fa01d00310307139000304180c00044603c141d510030840184050001041c1000005041d0b04100445d14104001d9100191402ea03862a051805500640031010304d12804100343c003003483d168140050f0b20f501c3d40c071204c14044076031441841c140741c00145441035030f8010b0f20b42800c581e0341b42e8032802e5000d00c004007070360703d84074007a4400c100159000090f00c0070500003000e1500c2c0e00f4100d50003448950030380c001461a800a108002950341c3c8100201c101442600012980c941c1500c400e644a00c00d0300c200c540c02029100030030040c0300c01207440e00e040b85c0c40368004206c160348582200e500c81c0000c1c05803074502d810070000310b000c0700d002c0150003a104000c0801d804140310320754150003070004d40e60942c403803074154a01503070181602803080e040c0c050400d1400c14a400c40000300203488081e6806010201d81011508420310b803020050342020f4a0b140d00c1d840716610040c100295541001c13282121403582a100100e80d071032045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51276496 1250 51275246 51275249
    0x60a0b040e070f050402070c05150403050105070e1014040b0c03070c0509090304030f060f0c080405060f070210020d020d0501170d03090f020d05010908030703020d0e070b07120e031f1401 82
    0x1281d12040044c20300040001039401400d007614410900040403a141d13072904060503012012201043c0d41c4c41c0f851400300c0c01d41c0e000501e1202400880b0302c0100450704c0350703041c030709a44003145441c0a0412310220503041c2402560031555008a022841030314600c000401042074a0041030302c040440e6840041222441003142d14265580090008100203402052034200052041801040340060030b1414021a04884c0a5100080300f6006010500900b030010541004003a2003800141c0740101c1c020f940e542020756901e0b80740e82d000030b4540b40780b10680d040d1043d052108070244900d59449811003280904c03040d402e2564042c011203191054001e1203151f0039240d0000280c400804140c081044000500303800760748135500c0e4914040043d02d0ba10007144510841d0b200180c55003050f204001c100d40302400b108046a00c41c907000c1c402c04c00741c0c0303050b43e607981e41c000e00001c4046102101200c0552500014a41500c1641e0440c02201e200349031903115402c00310020081c84500701d400e820307034490a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51277746 1250 51276496 51276509
    0xc140408030a0f050405030307060f0e012702010e0d030c0b0c03150d03050c151617040b09150a02040303030b190314120c06010e01120c050118030203060a0b040e07 72
    0x4102c0303019110f000352448040c80103581482800e05581b440403034107690000500300d076501c0e600c49840c5a4180107201d203d0310f8248100c020023501c0f800c200c0c0c84079080d607005071003590502e05542034401c41e0701c2429400c0080c0c00c080e00c049070400c0b55203406800e11019180454400150b200000c2c05d0106d5074051301d10844243c0542c0182290407014000c4001c45900d0503420020100010800d202c010803002e042003e080554000030f240520000d01c050222118240c100807114101440c05070000303440d1a042608900381c030400d9216808618540020b00304800c03016540c20b800c03c0300c200d10719030240084134081e032024014211481d082140841040721000c141c0b403440382081c4081740e400c8035482412400301c0101c0d0400e0380c40f2042598140c0024410b9400ba52000006121464030008100d00400e100c00f615202803140c0da5035801403218070300030070741008121f0010810000321441100003c540180075903040f41400807500340603250f00c50040d4061428050000e10101000404504a425 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51278996 1250 51277746 51277753
    0x3072d030c0b10030b090601150306030b010e180a030807121e0c0201022502040c09030819020a0204050f040c0b09030a1506051207030309060e06250c090c140408 71
    0x1080c2d0b903079144200082c105200d00401c00c00b000c000610307880034031400346c0304801c0284030390b62405402402000040c502e0030105400e14500f08001400b010a217419601000f421040035951180d4003140f001345542c0064007803103000343c144181608040070700e0040f80703155200071011106212900907030780c1a5481c003816015801e80c5079040315403030b488030303d00c40101c1c0300262508481800c0803111403465280d0134800960001e0300001c40c50039124900318407800f0304105007081d1940d02c541c1d4650091088002e400450307156135001103442442408121360b0300600421003820482001002031034100c40444804042c03c4000c141d0000180980ba0210f00c020300415400101d541e51300e40302d80010300d0010307905854403804103259030b4060b03808621110b0a0000c0a090b440c5040081002c44517a01c80b00c10310143e03014940c02a00c840d81210411900c41d01569254030b800d1240d9130b41c03402c071818040d103160440d11b00401da81d809500400d03a1520196250302d030030018039582d56000d1040b80f050302100e50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51280246 1250 51278996 51279017
    0xf0f0e04150b03100c050d1b02030301030f060b0a03060608010c0309050c012d030c18050109030f050a0f05030414060306060301030303050606070506010b131409040308060f0303072d03 81
    0x4100d070050000604003809035050483c2c81c04c040400c2d600181200408600f0200d1b96151055040c8190a0200401034080950303804484019403248810301003d4a0700080e12074240a00900c0e030040702a249001c0c01201e0580d54a00b403030170040070305024120080d401c144181c4c0c1c41c24800d004080e42c00c1d070864080c08140f03040350010b54410010f284006000b40320a42820703150074018901130354600701c03030314041005001d00c200180301d04184100d440d841101844148141d99101481c502581e6200044c01503255150a1030b030314141c45444c004000d211004041e5080000120241040301c2071045a00f01d984005c0f01048541d000807540305400c40700600040002c24803e82083d0740050b4050300c40f5203005442c3d22501d06055098100780300d0300328006501d88101c145241c0d050002e0101800301241160104005a2045000740c009010000303020003040d1141d07280c5202610314280201181e0b0b0b190300c02d07e0b0101c541c011902440c503c07010328010a8518441041a00f4041c83c0e16564410061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 51281496 1250 51280246 51280283
    0x120b0c03090a02090a0902010e011403130809030303040c15020a080706050c0408060408040e0f2502010b030703050601030204050f090607110c060406030506120115050402070501090602040f0f0e04 86
    0x240c000900720300d01ca01c00c40d6542009601ca03501000e010f840584030109080300c040c00050308121003481d4040c1000a10200e45103400000400c1c0c84e00080d001c40c3c1101c6640480c01c0203022401003081c0f15505000c00000c3c00300304042c07414034004440302680440a1002ca0041c26610b03407d2940c07001d071240341c2c20002040065a1a03002561061100c15441d09142d00c61074190301e040c20480d000c40380b01c100014107020801c1074292856000503060610301451900410050003500c00490a14442407109040040706000390411052500f0107130888803819600d050040d0303115400c3c4010783c0124a0300700418001103080680328072844001004000c15280c0c0207040707551504505c00310046000c0d510b5040403682da030000902c010070ba55030b000314460170120208080100c1c5907400f5003e0b42c8c0350200658000d080380010101b212001c95005884e2440780c00c0850240c0b01500340107101c2071002601003826000144604c081d01d0f0313100c0715a01c0302c540700d80005851203025030b005456840c2119011161 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 51282746 1250 51281496 51281521
    0x30507051b01110726041406090a03080d0c090b040302060a050a02150f0a0b040504120c1104060321020c09040816060509060108010f1b111f0c0306120b 67
    0x7200450000080381c43c0100c1020640c2e4102180c1180e160100040c040240d0815412144400400d034100b01d185c94505281e107400041d141040038058480414004d069598841c414002107800c240d00641e6011240d910340001c0030401943c0002c01e020760030101c1c6100801090700c0540c0c1d4054010b61903c200c0000591301354118103c0481140700d840c1031001c0c0256440d050301d0040c06480c0300d903511820003c2c1040241c403e04074005004500d030100b040302060b0514000205484c01d81050700205100e03041c090300c0b0026906810342c20a0030f100c3c0000403c000c40003039054a40a114500c500c021080c10100c0c0c90304030180690768050481004180030649400c02403101400380264055128081e5075900103945080b03070f034110a6000040100b1031803100f8000e02c490039034082c800f040314041001099138442d0f41040f2003c10040e82040071011642c007000840600511501d04482201c0c8154a4002a0000400c401e00084c00c1075400540b8103d03455031000c401354000048041c0d5a02c003410b5200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 51283996 1250 51282746 51282787
    0x9052a0901051b07081b030102070f020907020a020d0b07080708040c061b0f0606080105011a03010b0a03111216030c080711010f020c0105010504051006020304030f0515010b0307090603050705 84
    0x1c040d2040348101c03e01101c00c0103c0b5009001050180c28403102c0083e40d10044c542489140340603034010845200041d24229903184400da04030303600d0307042c0c3d200c602d001c034580f0642900003508021142030000502100e0826180300b0016075a4107056961141c2c02151078400948005040c030006050900815004980344000680000110804001c55850f00f107160138080400341ca1203680c40b00b042c0804803084c05060702601c901d00d6601d9503c0a0014290002d1205224101049202007a200d07a56032080d0414001300007400c03230003074580000d070261210031502030b56020511801e680034850315600901805144c408141c81d08221940e410704140d40710048004011001e560341d0280c6183c0c00c0340c5201a102e0029010f00005540d0305040a000c1103d40c041d00b91600c04402c80010465135034000215825241d011862131424403a0b46805c40ca016050b10051006001c030f2800800c2891400b0003540c81070007165221000c05940c3d44041e0121030b0150344100004070300304031210a81c01044048039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 51285246 1250 51283996 51284017
    0xf030e0123092a1c0f030e0f030304060804050c0405010f140108070903060b1210150b0702090606160206072904170a050f040f0f14030c01081f09052a090105 69
    0x105240003030703200281c40044c09082200c0105100045074103265000007100d44a0307200380ea1220034002c0190010f9504d01442c45000100804103000030300b042010f1101d2000e074000070300244042d50b100c05007034107954848d000d68030300060b01c0c9810802d25031041c26650b018400300c0e11581d803918150b03240c1001922039001c00580001c111801c0e000c0007041004010b151015220b000660b0703800b1460440c2c840d18056000400141c01404082c000d40c1d0303100d00c0950000000c80b86140d841e080b2015080300c0c1c21001d10041c1d40900c010076400c003441036050828034107182c45a404584044403010a800b00c05040c0c82c0079188400412001e20740500d03040c0100390b0600ca03420b10710b0034040d01c0c8880740a294442c2d04403400e2407400110030094491100c0c0004007516209000c29407104900c0c0c00700e65a841e119441504000d00b00e004036464201c812200c001070140f400d6a11407d43d240c4500300c000e804151001d48050b140082d44411103007662490655180c0d2103648103180c4108440115110742182c864074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 51286496 1250 51285246 51285259
    0x40c12050102091305010f08030403080f0319020d0209010905090f06062b09050c03060403020c0607111c030909020f030a0e15040c090614010503070f030e0123092a 72
    0x84915a0710130111440d88510210042007540c10440107105002e01035000071280d82c802c2c0300074800200346c80127403000060000c255503220342e10710880b00030200f41c00700201c200c41d02c0002d000c60441d0300780d0000c200b060fa0070780b20884411342e20b406001c060102105d00310301c0301c2040d00c04030341f8501d4100001c09000034180c0d403070b203802d15010101d113014641440796050030302c2da215004000c01c9014030090002641c102c0141409140a89005e52501c8000600500c69000020201c082103002c404001c1c040c40301034410301001e55150590b034a040c0d140c02d015408910140030001d00c015244c000c8420b0102642195411501c0308000c400250041010b21162401446183c151b1800e05458091085000d4a401e220451030040240c3c100d41c160341008000710b00380d04003e107060360004200c0307420010601d8141d91460466208400414408800d40c2e540e50900042c40e04100035210240000d0b00104c0711109545c0350350303070f071141d40b040101e41c5138a400345c8000310a01d4602e00f40d800c0080c02c21014000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 51287746 1250 51286496 51286507
    0x605060a12060f020d0f050a0b031f0506010903140105070201060506041a03060d021801170705090609250e0f10080f0a110f031603050103150c020f121908040c12050102 74
    0x40e0a0700d9920b880700501d5a41c810400003412158009c86515480950240050b5610951520b8401d5290070a4140254075000452440c0c0d2180545000541d00310b06070740d2605a00200f80c0d0302030b0505a90f801c00540c01c101002c6017514058044034121017003103803102c100005816220002d60401000d2660104c106a480800368484003602000c10300d01000b000000c2d81060b208402c11940b03020b662001d603006000a2100781c4030300340c2032034203c84226032022403691002c128010741580c0800d10382411890003130500b400c40c5c01c03079050842e901c1e04449110300101407030b0503c01021007900700e44000440b9040811418942100c4482c0c0211880c0c0d0b001c03500300e441d0403003141c080c0e002d244000042d4200000300285403140d54200c034280389603840c0902595245456034083c50180341100c5002c503076280c00300d0b070015008112070400c2003004c1040e80c4401014002680407030304864506c6440f02c10041405860a206030314462040754000d0019405078200b464002405080711404c988030340d420002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 51288996 1250 51287746 51287767
    0x20403050d03020a0813020306010302010e120f011b110303061207030f030f03110c07140127030311060705030c0a050d0f1a01020a1109100506040b0301030605060a12060f02 76
    0x68440c400b07031800760380c0c0d00030724500914504008120004850500d08150300603600426140d044035024640400b008040d0070008417010341d00030054040b072081e07020464480106420080b442c44900e40e05412070705003050103070381340036517280110300030b410405c000390143c43e0410f21814003810681c100c03220380741ca9940b80c00300c40000520a80200300303030038000e07140c541e894010038100d2401061002c1c00e05800280460b90760542e80240300342954141000030303259101b55810001c03001d081c003500c1301c0001802c2e003401200b042c80c0016000140740d040c01044482e000102d090184000390b40751851170303480503c61a000c0d0442c5000704200102000b80301c0740c00140340515600e0100d011800036203a211900d864442e00d035141c4049040d90070041484011a80400204e007201d0b000792181140d0f0f5035021440108136210307402c415446071003c2008940c000c42d810145058a1150b5400c011548030741c000c000d5956071620030014030030b5460f500c85000034400d0f041200f40a08020300542030800455 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 51290246 1250 51288996 51289003
    0x903030703020304090506040606080621030d0209090702030a09030b06041d0d02010c0206150904140a1b060c020901090e07150203180907051b0703020924010e03031b0102040305 78
    0x203420781c0140c0c408502402160307080d110721500028100d0303042204030310301000504401001440c0a119a000010016640303c400481ca91308550301000e40c0c0d0340d900450120720080d040192201d000e0725028001524a500002c101c1e40c00c0300ca035480b09001c1034915500c4580c8190010100c03900541c4840264229810b0302c1ca0306064080c1d1a00940002244420000d0031142e081c2540011035120030180003260a04001c2c28244810903501c007103c0f80d40d1400e1901c80901e110402e6403880c480d034602c40c030910102c42d5010385183d100060194106644180460300298400c0d4003a50040e00305004115103002580044408000c013025980e00550312244401e0180280c4040340c0981c100242040303103581d001c010403d902c0001c66211216051001004200c1c0c02603e81d20030b10b0200001e101301003030108020368801503900501c4142c0d146001c14400c14210703805090060a003c03806411090380d800380b140b0301020031000e0000c500301402c2c00e4900c2c0440d1458844e100780da560030840400070440c1807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 51291496 1250 51290246 51290257
    0xa0204080c0907051603200714010c0602130902040303113c0a080c07060302040f09020703020a061e0b0907020604060203060a0314010507090f14010f0318060615030902091605090303 80
    0x80c7c68407000c4241d65111480d0342490440301020940000c0014000048001d9010712200c0f020301c0c0103801503400f031400000902c66241c02c0807411009410001d0122a40d800a00640c2d109980301c85c2c0c00290f480c0c10740d6844150021940d880c02c0c013040c015012050f913000b0461038614070004c00401d07210500322541014130011040e92120781c0011549440c4504004075801001c00d403404524045c41c251159810f41c05c10b0007501c1c015500081c0030010701d84208500050740744c0049c41040303464200750401d0500300b040340f2002d841909200c0b01000c2880d01402041c8030362103940142415642d250f4032440258801080c640d4004007020004c40890720105d140600c0d00b07052000003071582080440500500c3d099031107200c00035500c4605111020890b034032503440250a00308803e0003041e4a5040d80600480e089841280000a0300c0005000207500310340b0032180011003401181c6280c0504900380c4140c020b01a405c40c0e01c1e440030070402e1850f800030504201584c5001c0f406c0c2140a00002c1c11503000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 51292746 1250 51291496 51291503
    0x130b0402180f0607020109120f05070801020705010b04060b07030c14030a03020c060105030a0807060903020319020a020a05010320070204022a0c03031903051b04060c030201050a0204080c09070516 86
    0x20318403200c90030030504240039844119800780c04c01d03500342e00080101d040c1d800340340c0690785103403400403c02c0b4603503191a0005a2140503070700c1c1c0c941c40d0f40115000f500800419583e942c20015034000030700b0144102820365848000b0a0701c0c0459948055419030707004402101d901d2008000303015070000500181c000801c0742e58002d665808051140351602c90103800461003030b08a50300080c0080c00c503004640c2d015500010104644000381426411401a41031032048443e0700582d401d041c0368041000c250151080b500300403040d8950340118103e526014040c002c0e1100c44000d106044050b1000e030160620082000d442c0c00d04400349229246e6083d0f21100100d1110180c448452600303111802400d402a0300075800c160001c09003c1d50300e8501d03600c020600d81d85030042008118070000325602200d207442d40a82c0c40c4c2c0c0d1580010140070f56250250015440d04010903d00754580c000c450450380a02e00400300482504c00300046044050300c11018400308101094030304d2504143c18010501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 51293996 1250 51292746 51292777
    0x20903070e07090608061905090a06050a0303090320030c0103020c030403020a0308040e091516030e0a03020f010e1207060b010504030f0606050a05180a110c01050103050715021506130b0402 83
    0xe0b100028010307401c05810079205581c2189001c4941d1490701f00003044890441e8086019224103013144000e00e01508020b4002d41c81500110603d500036000c00102c03480f858080283d036018402c6003d000103083c0140c0d905800008510015611070340140410800f208150791501d0307030f40e0703001550707883c1036610407110f03035001050402c440d426014000d80e01184001c054584c40411809084c909100105a0510000c1107e80000002e01c241d2203200d400f40070508813120b12003a410043c0d40d0341d4001900054641c2029009d603229100410303020000820344604505040d016036496015140c0c28241a0400a0a120010106010000d05a0210b00400d4009603150402050001c0c4400319008140105a105090645100155510317075108480e03442c0000e249040800d8200030b885000c414101c150300b05800032040c00340120300b183c1250b40c2c07d8001400c84408200030f81e150f0500000f841503046090001400d28182a0f10340c03001303078164150000740c41c40368100240407038020b40c07000300c6500c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 51295246 1250 51293996 51293999
    0x402100924110304141e040e0c030622020405040303140c070b0105100503150604090c03060806130312050613060b0304060b01080c0a0e030a0b040506091006030b0a020903070e0709 79
    0x182c00488030b00c011151040518a81801d08503c107009000d180602c0340210150303c0d18140303502180d485da21500a00520922818071440c2100781d0b145016640c080c440c0c02030101065422845149403124458929168000e1442d15000c000007000d0083c01a400d00da101c0d8191035001c41d190300042d110f2a511380d5403031340381c240303505040c14540d405800c881d0003008005d0100c4841b0342c200003a00d40c807644d240c9a110422003c0d6000c00d0541c0215802903130202d007030a1001000302d4168000340d0a81e1210760445100b03943d07584050840b854540c0c0060b01040150703480680800558004540c05903001c0c11303241d03a0313091440070141100d81d103074414800001c021083c441000701e14040d4034002c29003440d04030301e1401e044000e103d45200d40c617800c00601c900100b110b03103a42c400f0300c1128540d43e0401c3c1035040c245424100162155400c891600c0e1030300511541411366820f501c1402c0649030060b4294030b0580c0c5491201009500980c00f6951500c180c00d40003503440f10744014140300d8043c40c0c1e0b40d0410306 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 51296496 1250 51295246 51295319
    0xb010e010603060b030610020f03031e0a052502070308030a020c0f01060b19020c06030423030f04061d031c02010b15120c07050601150e030c01020604021009 69
    0x2006802440c105420840104683c40048003565080302048886038628100c00328164030b002c00000c00401580804000c200340d81b4405403000c3c02000c480c1120b80c0c041d0740d410004a080310300840750001c1d03480e140c245004521146018110000000b40101e5504136103a89400032a80c00803241001019000503aa0700d0303000c3c050040020100c4e04900070b02601c0e04001d81c100060090305512000f0502c02c080200f1018400c0004520a038800380c000e5a5908082c1014542c0003940301c6800c0c000c48580301e4400c0c6110001080b0380c0401c51802d502410541040b00484641c11441c0014442851201440d41181c0d0700740546002103200d02015001380030980d0000c3e007520142e4000611440b000c81d403946c650407428007103640104424106180b15600d0309070f820154081d045003d44248524400494a04068803a16030340300386c241c03509200300e10402d042550341c0109440c141e005800c4030010500600300b20080b0b1f035041100c0e051000400e900d50b010210342c031303407079000c0300b20034010040424902 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 51297746 1250 51296496 51296519
    0x1909090c080d0f0311040f1202090709060509130219030b040501120f06020a090b0a180b0421060b030d020a020f0105070305031b0d05010303021e060709050118050d0b01 74
    0x10801c4001405086280b039002501100d001248102415159884588860b968800301c0d405021072042d06400c05466003c4486c54042020381240201ea00da00071130b2603180915080d104079007050395450f180c10007410502110305000761103240615024445079a10380c040c010041c030484080c1e079001a842190340c0404c81500e1061384045080301184190f4801b182400001a898681041d80565500c2e0341400031103243c1c0c10340c0e0025444003c082007031801103900c01c145a07a0590b800015401c2c00d0748450020034244118030480301c012020003008850343e5681c28450402d94018000000c4850b07a510110342000480707124500181c0040c0070340f10440c50054048481c1c080280303019400c09613a964041d240e44006052410f040300319808031201c85050800302c986e0041c00000074001c03541d41c3d1601a58807031032144410110194035044440b503400000b11640720300300070b60f1031001441c0703840010744a0f00360480c0700c5030035280c0d107080100306900c6407143d04031998401e5800c80002d40c9040c0c45000b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 51298996 1250 51297746 51297749
    0x11e0504020a15020d030203180303040804030501050906060105160c0902040f050424030b1b040303090e06031606030207020d0602040602060f09011406120f070f06020c06030603070b091909090c 85
    0xf148a0300712802d1990004032001c000d11182001a0340c3e0315045103468500040b00c4030a9050300c4000700300030401034110094412603200340024809611802819a00c0e000229071160002d442400008c1c000b0404203a000100b9001d000d11001150700c030b142402c02d81e07205403c0380b50f44003a801c0007000181400e21511542e403c0d1903443c090715005500301c810701c601d8180310140c09075200d000440c54441342c00d0714400c3e1080b00440c4c21950f450f542c1c40e000e8a410713480c1c400c00012240c41400100c440c1004201804456994402640b0035410b00c00160000d400c20101660407003807102c00000064a03a10051020342200d130010b10041c075003a1050103400c18002c040c03c85e9641000c20401402840302082e90704080e04445090450103598102c0e0701d44140c48580282c6071003400c100080d540c0b19101c052098403a03660a960b0131f420b00605101c0c040c0b00554500d6010b034490700f07040210f4502d0001400014000600d84840e1007010132120108540541080040c907694200c0d031000c12003190103000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 51300246 1250 51298996 51299009
    0xc1403120a030b040f060527060405091c020a11010807080c030a090203010204090603060b060c0a02060d020c0d0324030b0f040201020319030f06170607080613090302030408150c0a11011e0504020a 86
    0x11104070046501088d03803c0040c01180c062621440490064070702841017008110300c0c11844400d5400511000b591a4100745050710205132070b0004a0301940300c0c0069078811519034503501c0460300c6d104010082544020181483c55503140110380050381c0a000034002449409000f152850543c14000102c40f950702d8450701c01c1604001807281e6882c0422054003d0340c040710440c0e2540315900e0000060300c20480092624010310a14407545501907000310403100701146480362001d01002c1c07814601207603002c0540b0046003000000c1010b10409501e03580180b040c03054a040c452100040c082c2e413003003518442d000c42d032210100f40700b035040340c810f41d002401000c444d0304000c403001c0d41c81500c491010341241d0801000c0700c0003c003161500129400500501d0300204101c003e1410000d4480c3c000303010b2407949004016000204202c0c2c0750940d405480c010034401e01d040c8404400791916500d20601030601d5403159500e0800b55040c0d608086201c0380c0301c81c00304103440d283c4100101c1c002580c00a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 51301496 1250 51300246 51300289
    0x606310e010c1112030406140915062d0303211f0f0605090a0e151e010215090a0c0b0405040e010903020c01050706060f030303090c1403120a030b040f0605 68
    0x843c41c0076400201c0400f03000c048180e503a80d9850b40d04203900a410320709403000c04241c0c060144002c400000911004400310041092000c2d2244001c00851200701c8660150a034180e4031104140710b51030603015008000182164500303925071101c580303585600010910b4075035440e020482c0e00c05003504171281c2d2002d03814000301c5460904159600014050048400f08034000c504400162241c4000d0301c0a0300303240e0034121280c42d0042022004504224149010310b1034562414280d80c1040686010b07164140c0140007480403c2001c1c0440c000c00600c1d010031031241d80305038008070305540c440401400c2d44030549580c90781881e0520054401c0c09542e03001c46c4e8904450000400e034081041c4c560300c002403801d60b982d04d00b60b00300b49001c3c0c1000d8000b1000310074050345c008100744d095445070340c525200700032014001381e44a40108034000c00c6240107825410617503d518025401400034203c044d02414009022010607011a04440c2100140c1006540e81c8c0c5041c400d514255081d02d40145820045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 51302746 1250 51301496 51301517
    0x21009080604080a0507020d050c0310021305010f020a06020304060b090c030907140310050901050a0510031203091406071106010b25080715050402040507050307020606310e010c 78
    0x100d41c0d0320280108050500341001c01d0441c4120300c03c50895400a80003401d518400040e401e0241d00e03503e9100c01d00d0700c030703110300003c80c140c2e0169402580c00a030101d4411141c0180f5040054903105100905803085020300014100051010b00c0179600a6004403c00159a20b142c8180210180003400c18000c1041c14420848060800101101030722804005030407081115801b291510281c5004642590309000401130408c0055100c0c900c01c8050341c0e4107003c241c4600d045103101c20030038000a07029007022242d00c2e8007a8004e030080500c541c400c0c010030710b03060310b81844513040280c1514404005020503100b08407210040000c24098801445641c0c170f0300c80020000d11030720b800d28054440402c8080f804034180108039040e01d00310358104400b0071400c8808442c4100516089070101d1045103014046400e080c801d07001d8900c44c070625002000d40340ca444041041f800360b041c400c0400203640446a26038000d015012030070040300104007188441402800c05d00791001d80030440b0801141804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 51303996 1250 51302746 51302759
    0x2090c0c0a0f1b06030f0c0509060f160606030f0b06120a0209040204090602040b250c0303050c0f1c030605040b090f040501142424091206040f021009 66
    0x1e00702021988800e04200d06055460a041d103030350601d1142c01002e408100c0001c9198158000400c4040300d204100940c005041c41030f103140c003481c03030215004501407058006a00b501401440d60044034004141d201482d6500d600607501c064100311200f1030a5208041049030300200703142c001c0c0c8100c9400318140b214000e40c2d81e854040e0800688900c01e0b14000c0b9055441d41d900030b0180da40c105509654668450364401e0142d40007428400100c1c44020340310003000c3e0346a0711983d40543c8403e4000701c86140d610115215080101040d001d80160fa4003101d2041c0100a0209400d156006010039031400e01000380c01c4400030b03800603000360b04116102e8400d5546a00e1613903ca00301c8200e03849107449078142540180301881103460714108032014040d500951040d80015040f40900d00444601e1b80c0703041c4205c08a040880040390301a9101031b95180c0c4a0070302620310108040e0001d4801e082596019190103410798066031990b107d5100601542030841e500040c02c0518184031840901d400d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 51305246 1250 51303996 51304003
    0x80601140a140d0f0603170f0f03190903020c0a0f03020922062408010b01080a0e0a0206030406020409050f090c010815031519090f02060a0309020a09050402090c0c 72
    0x384030000c016040b0100081d020300382041c0c0c0d0300d016a42208205014440130800001d140b18002502e0300f011504200c0b511143c070804450700e41010701440c506042c17044211444036040642820030503008a84060426100c81c8140321249000750300a001407004003092009500b40c80e00040315400030340b0014400744e00c0c3c03440c5c00e0340c0180744001100900008440044046000d0340401840f4038200710049884100503038010801c810781005e201e00c41507031040b0321030883c5c0c0b41c40b00c003502052800f0001002111254040032441c0c1c035039000d07903450381c186500083d51a03104644c1201c4079540400c00381710030580c42c458540c1c000e80d0070500c020203090140c40c0a03038500d400c4012504208801000030110780e50850890a4100089c1c12902c030346184009030140381d2812616130321444411181d0300d1400c1514001c040506410004094120083da024005581c0c00f104000c03080c192126445801a100c2600e03070340c01403041100000307660a140c410480850406004404403a4041c40740703120610300070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 51306496 1250 51305246 51305257
    0xc0501090506090a05060a0903050303040602120705030708070e06041502160510020a0f0602120c070302010b01030c12050a0e03040305070602060c0703080c090409061a09130309150c0f03030b0108060114 89
    0x6c0b500310b038880d9040c01003159a50015000200b45000220a010812102c1d801600c90b0701100342d100199507a50410031038241c081102c0300000203030010f0103e607000b400707040340d000ca002c0050006c5141a40b03032540038070b11074807040107880160300c4005800703586108031403000701410741241d48240243d001840251355024002c1c01612210f4114012010042d0302d5040310540c501460031032581d450102030540341d03034001c400254095424464015450340c444c0c03081c2046481247c46500307040310002c100300010400200204556581c80d6990030005030208058001148544001c10a203802c1c080c0082c282007028018224403503052108100003070300710a410b91b01c55040303a1078540324120000000c0280600280c003070416890809562100412110b0144810100790780704012a120f80c100c0318a64680b03000084c00180c0c0e00700c400d10980e48000300c921404c0000c0d01e0404401c0026496407001780054060440201c2d80e5038483d002c043d41c101403020303484102400c0000070051030030012095441030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 51307746 1250 51306496 51306499
    0x318130905031902010e0607080a0b03010b09150105091203070302250611010b0d080301050a0f0803071103070b130303030506010810030213140f0912070302030412110d0c0501090506090a05 83
    0x40c0351111481c1d403017540301d00c8011640c039041f81c840b0f0610b603e029011100030f60b03080c004c240c04d1500450850505001c3d00184000c0540120380564900c684010310320012824617042082c10042c10700c4c60381d100b00c11100800101c001460780d031152440c001c0d1500b20321540c8852046074191441c200600440b0b801c0e42220914200307441c504114001140c0140b110100345039102d4522070305c0c0010b20100602441c1aa00103803611146680c0301c10002026071028481d0308070710b42c000c103e5000001c032020b0f543c00600030060207c0e0241a1910070b403180f95042102009101c0ca842903040082c580d16000b1603800c081d080c00e0250260401140024541441d800040c2c02035440207060411001180d000002c640c4202c440303a041401c00124072a101c0106030340c4030807244142c4c807041000c90200e00c100c0d2005641500218030f41071802d200388500c00521726041e680d403103584020114039120042e11669a0740704043e80c60545090000260451503181c211038080c0200f4072807240c1d552210400ba1b02135800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 51308996 1250 51307746 51307777
    0x1060c020d0501020a02100c090305031b15040f060c0e0609090907180204050307060e0904121205161823040b0604031a010506070b060105030414031813090503 70
    0x50300106103448060480100598800190102aa9070124a50081e9207442000380a1441c070508100c44602c4039000c003420035001006a1400c0c41b02c0003030300e1040b0742180300645400103429001202c0c0648102c0d0305441c021680a00102040080c1c45074071141c40240c00c01107d98401c9001160303003401070a85d560b0003192100d010501640c0c0c10400030b001001401051180100010703044e9029420a2003014040d1007200c1022a40d207009440e04d41a0b440f010341070b2907842d69181c55138400c0c0c6401e21064014013502840c25032008000f806254072401c01c00d0010900c40c605080700034115030600070900c403400c020489c10f000008524002c1100c04501c3c0107680f0700418410009001060b041580070341c094400103000040014403c0b04507041e10700e00c4a104410b81e40d503020f1000c0c51040b6480145100c40340d40004010b580100051600140550000d40556403803c0f0280c2c90340c1d11040d45020785c0160381c10102c60f285444442d15928a10486040c400700c403131607449969a014003803000c100c0d00d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51310246 1250 51308996 51309017
    0x9140f15030f0a06150503060c0f0c0d030603050d030b0108070e04060e0403090806010801020307020706050a0302071704170c060d09050f07090506010906020a020a060806060d0e030a0e0a0e0106 85
    0x111a54910541504001c050320004108a9601655443d011008541345810301c00d0b404846961006503c00b25000580600442d9036008600b078540d40c052845101e8542051015049044c02048103002d15a81920f0000d9001d0850400c149000c00300040c500070503003000c00c0160310f40d0348129010b42010890500c018201c40040c001009402190440d00c030980180040200385a0300c94400400c4541c04426241540d8881d03480900341d210407208000581d2214004210300382c420002403c44600320314005003043c0c01d135034400b103024011790706840405801090600080d041d42c00f10301c500c0c003124001070581d40c10b810301113401400748102030003100b076940501c1801e010f8180f00d4005c2240118050b503180540311124000180810b43d80f9030300082480e100400c10b00d00019202c120f094008200d003034900d15145041340c003030f0401001ca6400820502007080d8074400c900410b014400d004005c0d5413110f03075410005100401250600744204244c45040003d80440700800c0c0c1526102d251004484 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 51311496 1250 51310246 51310261
    0x42709030f1202070f06140106020a0c05010804060b120c0112021312021804050303040c0e07120509030c01060e0108150606030408030a15030506100b0309070519030b0c0d0609140f 79
    0x90040c64006880c5100001a2178200a031756031010b181c05200c07a0041c43c0030390320340380126500c0d00010802001c001c0f051400348620b40c025115607600c90b12401001c5648a00d000c0800c011046598500341c4c40d602041c07481c1300f19a0031240390080748120103c11402d00c110300244022602c0700d485010f20454564411100355290044001d900b5905d01854840e1803d003840c0048d41c90f84222016101d0b00451040030800c40c843c1036040e80a002c1c960780d040c9550351504a5200148800b40800e4220b00c820821341005c02000e010700801030082a001c03c42641c5081d16490400c808904544092a110310411003141d81c1c40c5c0603240c20a800019003512580c40142d044014980c20785c450460501a400000030410001002803207600c580d43d444000f2503450342c0f461030b1400240e84c00000c60300300717030b10611080c1040c074004041e40c6800d50542d90601d5a980ba45a00704c0300946d285803614100180400d008911406039200410301c540d010000301070182d0b0010191400038101458000081c00402d91f40e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 51312746 1250 51311496 51311501
    0xc090a18020903030307050d050109020a0c02060d1b05180904051908040e0f040312110a0e0307030602030a050106081303020304030b060d0501050106021b030c0d030e0d0602042709030f12 82
    0x80040107001c43c5d603a4203080001409603009100c072400c46908240000c6640703c080d000381d4040911a4036541da03a04225401c10009401c524984c4800e582e0710710144442203110209484e250343e09072151070340c0e104c04450440d088001641020b000d4072300701e001c0c000020030004d28001500c13500b08142c809500075160080152095030300c240d0f06e81589400703103d880c0880f1188280218402c0c1c84980344030441804110030385054030383c81c0300421414001200318034041d24901e95039800050540d4121034581c0d0b210030480c3c0051395140c0c02c032070f07542e0014002c0c0c07900410029000111403181c024075084a82e0000d6580c4510300000300b000c000000407940171348a0a14159034560311000a1105603103d1500a603616003a0410024165098440380c3c40c0e07003808109040441d001516941088240352400e640445408100b0f0750480850700c800c40118805101400150211003aa0b00d0300081030b04a0201c0d8400f6500f504401e9481c2104040000e60004011000360065042c8801a13003800c1c000c1500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 51313996 1250 51312746 51312757
    0x8070510020a09140102061302090c0403060e030703030c1b03030b04020d09120201050a0e03040b0702010c0203060403181508060904050c1017180a0609020a0f080d03050c090a1802 79
    0x1150010814a1490f90408080000d0b15003251340750121407a104012a41d0306000ea070040e4420704246040030150501c4894164801443d5600070300e055503a80d6070008594111460102942000c0707503d80400d5803600404c05078446074900900d5959051000800d03144c4911002001d065450540000c40c0e00c030340c0c05460080aa00700c04104903400b5081c6820801c0d0030000b03660040d440d2000082110100d807040070010f05410000b10f0030142001394010003503100c64810b9051046a80c156001603604114907840785100b40d468414180190f00903031922896070304403111641c00c2e8018603203050384c442e0441c1d0f44410101d030341881544603820228140032500c403050b50402d041c0803030b04036040d40000307424407334991224684010365600c1000750ba2103141030003901842d40101e03403000302041032a040141c03e54001468080142d80d0342001e408031880643c418101900134180b04403040e6007602c640790f44880c500310158604a0740303400241d21010396000380940408040034070003640d82d0580c150745 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 51315246 1250 51313996 51314023
    0x150809011b05071716020105070f0b160201140c090925050a020c241305042d09030219030c05030406051c0902030307030c020310050408090f030105060d080705 70
    0x30300891801000400c0b40c0c0c00008142c962440c2500c1c0b08134030300100300894044500c2e02d45c40c5403d40340c15074011240c652124000f0340b54165003004e020049607140c1d146a00844c810340480c60070441008010f801e403110591584141c80c4a41d00308081c2010540895111200c111600c9a2a98407006004914107075082c0f150405050b6408842c8150781060003042603100540032034801e6981041001044801e00405864107001803010150340d10301c0001810300c80268500c98081c07240c030313000420100e0300f03030342014500c0c50600320050850004810a0a0a01d01143c43c2440410601d40303001c2e42d607620410103090a06a070303e20710360a2500c145103d4038003d5202041c2c0e039681d07075566030003001c80c0c110100383c02011042c01a103204024191140c5c048660b8064060b50816400c0e4030240d0760005a100182e800d40540384400c02041110b2240034481d91080b500191110200c606000c02c1c0c130300e01e01105000c1c0e854101800700c02c0d0389148000c40c180364081080f9696004600d040c81c2050324440b0090b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 51316496 1250 51315246 51315281
    0x307021507061b020304080c030601080d03020a2106090609090f080309010207020a080a020306010f03030e010509180f15060703020a0209130b010303090305210d0b06040f06030e06010f15080901 85
    0x1210f030f0950110080040f0fa10709011035414081c4d1340c0070180c40703c03000c1c41040d4440c0d10015180d01000d0281c0c0140c0700c101140d04050800d45d0b0000d08084200c80708001d540c42c0903507200c0e0140700000480c414007001d0f001002d0708200c0441d181e5140940d04000d14000380160102000180c4400403d40444c0c074815800380155403983c3d5500c0710716a032800706210803803003030186500106038001000e103120308503a05507580388120111540103440315403196080351f82207941e082010000050701001580103d5002142c2da04501d0090b059210a440030021280f00315010000200401d0f800502007158580450b060790076030b2204003040d409021503000062248800303030000400d2541008151003100d0040003915204084411184155a80403806c0110b1042c10300c94a031a80f4143c0d44032904070800075107818585920f500c4051202440741d0b0060002031348910000c1002002440300d13070f0042030030071040f070703042d41c10700c0c191204c000c00c00820740003003280d0303003000955003042500220900001901c11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 51317746 1250 51316496 51316541
    0xe1909020c0709050106030c0804110a03210e01020106150815040518011410031119090c02070902030708040b1003080403120e01111f0b0301062402030702150706 71
    0x400d034840280c0e2040d00401c1d450f210000551601070700078907200c2305480d0750301c40716551741d42c1d60b00303902c041421452500103140980200010b0401000500000e50740508018058045600188400160103010b41164144041044201000f0066614001c038a0610062540e40c1b14001c8a10f5100210300c960300c141844180040e02d07594200b64101e10f002200203002d4951280e10300b0030b440c6015200580714185400080000c212540106881c0c3c0300c3c000c4c48400500800000c00144003142c0d000141c150355141000d504041e010001f0500801c0800c1d0207500714039108801800080f0000c1010f400c01e0288000140c1d400302034240f08025603400f00709207440350f8807414602c3e50102b901c048400462050b0000c0d04c03041d070240b50b044080c0101440180003614400c507c103607001d070f07404c404420170a4498200a046503400e0290300d0140c2403815181c048184003580314080745d82c208141c4415500704000000158031141d400454030702c44d0951303583da00c5034546860300c01000400f00c11240710105000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 51318996 1250 51317746 51317767
    0x10c05030105031501030b07030b030a06050103050705180405190302121309061220010c02150702040c080903030a0903050405030109030c14070602060a0f140106080f0a02030402010e190902 83
    0x303181641d10540448110307292400040e60030180038000030340007803c0d21000408040c400c1e00302c8140f06001405135082d506440d03440600340e90003038000b01c0b0a6001b81100384810b05110201c107034550b61032025106103060076182c403a152010300e6903d0b030422000041e1802418000c10502000800303881000b0340c1c40c0000004540304001500880c0c14035130900100003418103051001d40206900104880c08030f4095a0700d4160090302280d900d0b041c08039007100c8101580d1000c2c648a20340100c159410707595030503441044110340311030361038005005040003806135159002055962010308480005003104090906036618016a030042e0350660078040000c00705513100c6030050314944124581c654035404400c1c01c83d225652805400c0041c0e0109001410038200d41c3c20941c0d24000e4103000003541794149403141c003803d10981003400441c40c03401c10f1140b4072039180d18589d030040c0d5443c001c40c15402c2030344c0000c00a02154212910072064008085540d001e03200036a0001c0602c9502196a00800a07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 51320246 1250 51318996 51319007
    0x60106050405010f030603030210050403140f030103140f0a0f030c0804090b0a080105071d04020405180403120908070206030709090f0c030b090103031b1a040804030210020d02121b010c 81
    0x81c2d00e000824452054003101e0103030003030b081565495000b50010181000240000f448010700540c2008011106918552030b404010000e4400070007801c1c0d0749605500b440e0441d010038281502807580b010041c00024070020556001e01c0d50300a1059103416035a040c100c40c490140312001c4c000e504d0005000400e020390740c1c0100e9085105680c0c04012071754441c1750030b0890700100c07840c2000c24000d200241101803404000411044020720041c141900e58000c542d10040c09605042c540303503000248003d158200440202408881c07905011000c5290b480310401d0141e040b000b4010100807002c00d1800d0700030a03252003c1d094100e82000718500300d081090182001d0006103002ca441c2c84030b40403030f0341440c2a60314141e980580340c0001240e0112101444441000000d4030290484400500d01001c26a101d0f8091402440300d02c0e1242d041d4010003a900c004056401d0030f66200c000113140e082c0d004034024130300004c5544601c0d201e000342120030305070202005c0c017002030307520b00201c8940d0645c02c41c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 51321496 1250 51320246 51320249
    0xd05010e060f0a0e0a0902040e100504020111030313030c02060d1b12021305010e0a1e050f01110d080901090c08070608010f062304030206031302010305090109110409050c030601060504 81
    0xb240e603040485001014040030034058011080792424000000307040c02c402e80c0040c01701c0c0d072026100140c070326450b01c10642454507032021203420f251204180030540d03030f00851020b0403403a4038002c0d502e54104001d51226244204070000c0602904a51341d109541d2210180c4803ca01001c10620032424200c0fa11804103d0354003090000c03c80c120010b450310721240c42645d0f400c1c040c0e00701c1c50080d141040c005480e455a103041003680000c40d400c0c00300d084c168001c00c980c2a4000e000c0f0110599041c901080320341031955130864108240030388643c0c000c8400207490120301c3c2e6682030806198447c503e0300c5016140c80400a00128004600017907160000a0a88111445543d03094090398840c0b42900e440000c0f48500340028803171800e14039010030162112220705800700d000516181c1d6a0f0f01050f007540044400c00500106600f0f0700c01035581501030240d03c00c1092008000703004d4241c2d80c0c1c202c401c44800030b00d8002c0c3c2c0d45a84240030050200320704107d050004049600d9503035244801003259125 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 51322746 1250 51321496 51321499
    0xd080c06012c1b040b0c010614090403020c1203090303040b09090619030b07020319230405060414030f0a0506180a020108010b13031403070c0f030503040b030a020d05010e06 76
    0x104941042036200311040c1144045201c00442c15540760696a69100c00e00340382000003443d0200800902403c0000c02007024050f20800030440b5481c0501c2100e031460910a903501458100c0f04100000380d011407d0340d003043c000c070350080b03800c0040307442c01b8a5400340445482e05444006004a40138118501400c503514085501e84580c0d519242030040106d40302c0c1540e1390b41602c03c0005d00016509180c0381c2e074400014070440e0704001c0d40000011091088403094004919101540c811b1005e000f590003c900d03040301c1d4960f29091411010035450311072071107440440c080840b0380321079982c0c040c084901e00855640c2100c0105c3c95508105403103107002e03a0351003418004040642c00009000c030380c030381105405854480d0241c0c60912825560391000705480c1d0b09d030b40300440101c006441c0911b0300310700c50704800c0110b450300442d283c1301d0072640303c0b0b030080c44400030714000170030000e0303000011072b4150b0b41c0384d000c1582c4a8503400d0804010380a418421440f0a00f014000701c2c0042420212740d109040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 51323996 1250 51322746 51322769
    0x9070311060a050f0705030903011103041208060102101a09040308090d020a0b0a0f0b030a0c170313030305090319050604020112020a0806091512030309120a050403030c020d080c0601 80
    0x64010411201e4403420000710b0101d9400d00c015030313074241c1c000302410045018400781d82c40c200d00d02d8006400c607009000120790904003c03081c402800440c0341a401c4c00c0c4441d06011509061290001c0d549000c15035081214549815428141c07210a000c60300040e40c02420502c0641821700d40600745141c2101c50700b4082c4604c00019403614400580e116501d6046400204181c0b242c1e203510000e8400060404c000310385401d441d0000341c070104040e811080c0030341e50b040f03042402d0849003903c0200c0711000110551007800041c03900082240c10008580d807505045a90790314100209080c81c0d0180c1c00708842d420020400f605002010a40c50310a074400d913030f2000020001b1195001b24041d1102000010f04024005141414003448039900f140c1104001c02c2004280320000da0303207410040c0c40ca00590008400d100380448104082242c410241c40c80c1400c040c101c4800404501540c4005010480944a24415500c0f40d51040316855005515140c0c3d0f601c20304401540c889003072240032030341c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 51325246 1250 51323996 51324023
    0x18010504030b0606030a06030209090a03021603020f040f0b09010f0302010906030203240f030f07030c05090103020919061511060a0204080d0c06020c010c0903030207050103140f0702010b09090703 86
    0x612a10031901034079400120300120342c540000b445002c0d00010841504160f58102c044056520104d0392441281210300600359581c40e0700e0000d0a0003518080e0b55a215000282800107a0300d514505003101c609030b4002500501d1076103540007030400040c03c20342050305180041a082c03010404042528001e1301c0b120080e0fa42e880c0101e003280f00c1110340181600c840d8180d01d40c1c80101007008410420020614050700841c1c1c00061b06043c0c00494806003680a89406c104205120301480028202101c06a06542c91034001c12403860005126480b11200808060303503401c3d065201c40050124801142c6210403d164060324003c01c410301803e0a106450004a461845008850a59000fa0013501d54850034605c181c0b00540342c1d40c0112052502804240c5640c0401d204003030350000170369955411603186050290a100658000e02d04150030f0481220580705946600d60b081a00034035800c020f076450140890043c4a00c0070070340d42c400829800d1040c040c0e4001180d100b501c0c0240000500304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 51326496 1250 51325246 51325249
    0xc030609140f1b120109060203010b0405030601050f01020303181903080103140c150a090e04050604021e06070f0f0203060c0405040f060f0b090109120b0708090a05060118060314010218 81
    0x25600203c45214008600c480240c0c941030466110142c1113994002041c0070300151f48a0080c3e0f00260070000580401003000c100703600e401c01a45004150948000c1110820400000c1d01d03071200a04100307400c1d62021034400640000c0000045007031030402c4416a00f40a460002c0c0131213002e00c0144c5551400f81c04802c100f0700c000c121200c03800710042585502800b10500b01c100c94100c11402004d00429a60001d1104c401040d0207100c0c52250024150306e2406104006400300c440d400e04804400000c0040001e40320300d802c95010036049201b50025031a240f800c0211a03111007c025054054a03080c010750115640c06401a40d03011070702480044244907040040b0b540e14801c60903400035001c010419865814000c0072009018900130410546407510074001401c0c41000b00c0c0c243d001c040800c10480e51041c580354011030218060301014000d901d51319034400043c010800600010181e445101e5660390100c001540e001c5c0503440700b81d0740ea0100c54000d412601003c01e8030500010364030400e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 51327746 1250 51326496 51326503
    0xf100e040825060f0f2406030c090e04060b01020f0d080c03060d021009060e010c03120203070e0a080604050c06120f1510020109020f04090c15050403061e060509070c08070c030609140f 81
    0x100c80809007501002d516007c021405428070020b441d00f4405401000b0800d080301c54481c0e44110301400c008a04420ba039000203141441007140041c5540000d000c1002499102c0d2942d40c00c8000f450015850f41c0f01c0100151600c43c0490000354090b01c0d01881401d0540c00029520072281145c0f02c0d81c0203041800f00640340f07805105801400203c0030710203c2402d0f44d80368080c54018149141500c03000ba207000c08120611540e0300700b40c1e402c0d4425010001040310030090f01c000300905460603810200001c0741150441006425582128200000210280d200300c0b040c0310300e128010324001d8403080865000c3c1c002d021803c416409500e42046c170329001d04090040052030383d030042120a0003480c0c021000440c241c0041c4031020880100300001c0800c543c4d004035001c180682c03201c80500195800d01c20f084950320351100340100364040400c080b0341c0d0044500080e4540280280341c1c1e4080c1444c0ca0003001c200d036040100518545420380082c091100ea2100300b924411046600c1201c00003031183c3d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 51328996 1250 51327746 51327791
    0x30301080a020910030807050a120c0c05130b060315040506040c02030306090c0c06010e010e070207081009031701060c0312090b060112140f100e040825060f0f 70
    0x11140e000181000041c03c01801c0030754007900009000780c1058903a5182e514542c011a800e80d040d03804000944240502c042d02c0740050604c2e81052480c00c02a581d07200104800c40c0b14036807140c82c0091f0b0b400c0b40e50485804c003028104000700010f40e00e00d001e9022524140342c2000040c0903500c0d00300020000c0c1460b1098141815081e0003d50071552014100322941c1d000038402e400c60781051000e4103444500b00095406000b81501c01000b40d070502d410f01d80b512400625410441d40300344010491100c0129a842100d0441e06021074a00c4180c1030549040030860314808a47c2c00490001030300fa0340c0030010f0460544240c0d140344203004000c40c490301782e23500c4070005404040310710045441903010390840781e845518000089041504140602c102c45030482d411000354103c88101f0503131024007007000d0050490b01d501c402c4582495100c80c3e045000d5009036442c18010303500140c1d81b100c0502c080088180e4403103424412540d400345c0e000c02400c40030610110355401e295441540c3c0d0321407800d40e207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 51330246 1250 51328996 51329009
    0xc1f090b0708180102030c0105040f02041406090c0c0c120d0801050607050706200f01060e070306030320010207080f0423030c0d08040f1706100614070c0906030b04050f030301 77
    0x3e042c00c2c41c4401c6045034030098241c050540c4001c1084140551080c05818440e9018014400c0081c10310b00501040d154024901c1d1410a42d0300c0c00c02c1207594038810400d403c01d2030304841c87c4d101c048001d0014a8500d0075003ea50380804502105022804002148540c00000740d580440c0c6990b40c0050288034001c0305070007030080d00704400a01c071151252000c0b12200018a80364003461044144546c00e0900203450421940d45130300040c021b514566040d6600840c9030b142c10090980341d030714010b02d290041050750921131000e8000e16141807007501502c0d026500840031507992400f011155200740d00520070789003020740c1c2030f036410250354400b44050604c9902802401d603503112001008460081d5140403500c070300381404041180078003480c0d802d0241c03050700c000544800da00000145021001019102d0000440b0030034800300d030380050110030200180c0c000d55101e03103076890700b003c1d03002e610340041c64407928200b0000700b480040b038855030195026400f43c0714000c003c80700d16602c4e44000d00692 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 51331496 1250 51330246 51330263
    0x3051e07090207020f06030a0f050c250203070305070f06031112060910030803100806060603060102120d0f1107021c200420030601080a05070c060203090c1f090b07 72
    0x200602031580c2c009001c075600c000d00c44030025003c103001031290341003541c40b85241651048401d03844e116520039075806c9107514420341d003002c6400c1c20601c00c42a88a0850300c1040b02200c80d802152030400031200238592003811350300c130355840700e1000d01001e502e072190344002418a0700700110003590301d0071503184010310b6488c07680c140d4800060017085200900300420140c1c0300900003001c5400c000146000c1c11600705003562540c90030641da4038142c006004640b01d0f85082050020a030307000030340001e181d0080c90103e03445881030480e1800800c41540e80550060416407901c40a01030b210042c000c0502c00c4600b0034401031000c440142c60b40c0c620750000d00009200840c0700c2449136503c0319001940e4010008104502d030344103030503000c031041400d0102000b8084117211196802074200d40d40402d0700742d410012071411003002806004101d80180030341d54008007040075514288094407444402400003503000719003410400c10614500d80c6000042c0f1a15008502c6000e03100448001c80c1c0c01000c0c0c2c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 51332746 1250 51331496 51331499
    0x70e04030507031b0204091b060314131707030c030909020c071e030215031005090c0f0901030617100f0608070b0c010207170408060705032502070512060103051e07 72
    0x943d42c0040c402d00d0f021301180b58041050069585005031506a0f2140d400445607040603800d0101e9090140c2224040c1410000755448114102007160351113641003440600d403100a0801d0800d881175020491121072001070040305060b001500543c0240c0f1a980d40b5915503502c401e420224000c1040c0701c00e41c0c0e007107160100b000c09aa040f030010503140c10811161056507950000e600300c0710102d4201400480401008031541014a00b1b9000385016030720401c0b00c1c501144608814450301603113120040b404a4240180e0f4880da100b41d024022040700200890810741c1165510300942c0f600108507403d12201c0c0a0450850007180f0440e050791001b00311941c28401051155041354044004079982442448080b403403a81140781c0c01c982d203284850f551401c040a440c14814010b0089040c8032041061004000d041c0910121200480c401740c002c140310030201300e00f41005507002c4c65001800091402c111100440c4841c100c0b849103040b1881700f204001054080150049140656040083d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 51333996 1250 51332746 51332753
    0x60f09040f031101020408060a0501080307030503042004060303020303061203090f1c23010f0605010504060302130f06020d020714010f11010605150403050607030b0906210a14070e04030507 83
    0x4100c41c6407840303401c0084085803e08962400c80c1c100343d0007125254041d80920402c2e061904c03c0c0c50151003a24065072424565480c094168400500010070740104201880c2504481401692204100410501130701d81c3da230400079178a0304161640c80c45809401e803a0940340100004540c4004030161500c0081e041e02c0b01001030241c0e1301062082885003003403003000081d0001c1c41d0070740328990303205000b040b10b101c40b41144d0848000840c0c02c0411843d004003440b80daa00001030b182151517914015a991200c0820032000d81c1059200c4100e03040550004151940c0200703100c580d002c2c20f075003120301741541c03888084c010b00040d03091540070072128400304007240e11901456452820101c004141650764102103205814404030342600c0c2a00480c040c020040c050003559001a402c0ca014004240c450300026808403014101e20f1085a80c030308041050241c1450482a40404006503840110315081042c030000c2078003035104190054850200e8100e0006050a01850701552224203015140d035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 51335246 1250 51333996 51334013
    0xc0d050c0c09010e16110307030206091e06180a02150901180b0307050309030c150a0c020115140406050303041707080304080a082119110403020d0605041a130209060f0904 75
    0x179241c0400610000d17585056108000070841c0b03521990080c90186009040f59080c614084414500039840081782ca03488035001030203d4204503602c1d1140e0103500b51400c02c0b89480451580203400c100c0118590a0105281c406000c24890a89806406415116280c0c01c1c50340c541c000c07a41d103180709001240c0c615100b14042d6038402c0c04142101e190110b018213031481c000c0407900c004e46400c1007104100708075040d802001041d01e0107000900011020007030304000340410740501448040aa880140e441e50380e500418002c1101a007901d82c0e554492580344082e60b5078000743c02c00c5104404000a00e510004100e0b0b04a800301c2014141603035041e540e011890b4865042d048200c000003c050140a41d9950014010451203a0300580e0032424550b10040d07445510210040060512003000940c43d400d5a580740c080c0e1260303000fd0340e42e807641360181d00c00201c00c4860000702101c81c100205130711130385602d407401c40c000c40b1808090b41d10309080203070350512031026940141d003000100340010f07081c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 51336496 1250 51335246 51335281
    0x906081216080301030507090f18030f2606121513060b130c030c0f0e0d06060803030106110f010209060909070e130b09090601081c050c0d050c0c09010e 67
    0x21880da1040c10198850352903d030002c0e0000d81d5280c1007050204100c0c038a92240741500d400050060102c0c074400c005c004000745a20001070244880781c0d40c4645220300c907041c0c01180010003c200c03080380e007045540004aa4003151041d0140700d20100f02681034100040b07500c0d0110102c50011038980d070b07000c003140311480c0d1142d0480b0000d8a500b200000c90341e0300a50200d400030010000100380e54070343d00040581e030201c000c40051255510303008000075400303010001c00000c16144596150b0035441c4c40d200030034180d400007080e40808000440c036140d002e4000b0a030030035044d04580c000440d4842c001c1c200d220b60310300036a00c0f070b0b001c0140c001181008054558817119500f4038014604240700814100c495580402c0001c603035515500300c0d00d14002c200313540c01804182c01421958113003c51195124640703500b1100000e200003200d486030344194102c3c0c80080c2290113a5a074107000350405866904084004850742c01a41c84401031741c180754003010b04982e010640c00b030107501c07482d03850b41e6080c41381c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 51337746 1250 51336496 51336517
    0x80c0c0d12020705030301060309020112050403140a020a05150f160203030a11090904030519020604110d020d080403030f1407050a1e0606030f2a030b06011707080105040609060812 79
    0x34803e883c040b803000e0010398024031a0303480100b145d0600c2e1000502401c04619090021450003003440b000c20b81c485001a5031076500007401d41ea845410340280d141c95054500205284a20450009840540d00110340910300f0000302c0707101501d4000c0c80000c910a81142040160300600020346801e02070382100b451038640032419460f12140700f001c2a0500320840c1c0035004039900080024500407001d8002440c01d0b0240302030103190425607511a0362a01d4203001c40c0c86041c40030240d00075036a8459010700d45d1680081040d0780c0f50307580d14010300700801000b003490100314002501d44944602d40c3c100c400155018020704440c0d2155503800c44a2071402c15020400382911001038002809846450007460140c0369400081c1158035158020301032140d034400b000c02d032900c0c0e002c92180f200c654640039a540a8002c000360ba0b5500d00490700207030742014038540c1c030061905114546030004070940c140d402c155402e100301901d803d00c1000b42c0d0401c2c030441c3ca00c1d40c04075281c0b4040c04104000340c00c0d103141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 51338996 1250 51337746 51337751
    0x312050c0d180b03070207150504060203090f040204080307050607020d0306030f0b07030b03010c02030904060501030c0c06020c031207030b030d050309030711060705010c080a0605041109060a030b04021603080c0c0d12 95
    0x4840c42c0c1282d01382c2044414001590041b00140644e2a012460780c040010034a0591719190800f031009440740101c025190150b6030700940321401d0b65a44c3c05840c042e1031401d088a0315204a404c0c1183d4450047d238682d400760043c20504000b0b50f200340a40343c1542e03007011b1003500c440e0030b0b560740114404008140400b003517035800814003660307801c3c012513840c000103034029500d0f91380e99003c00080b1107860b4412814540341011008a19800241c1240d842e60050303401603c628941102e03508500c01c1c8500402d58140403010050066095440034480d60700540480e00c0310b040c0c071902628207110a40d02011aa8010320590000441216148080b1803001e80740d81e080001136a903041c2036818808064011a03903820421884500910402009050480303060101c0700a000c0340c0039841c403031210b1f1280583d80000e1800045800781c1c1214004410107001195100c807074059505030783c24060400c4000a17000c40c04100c52500394415120004002c40143c80c0542c0503e00c26500c07461074200500f805034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 51340246 1250 51338996 51338999
    0x1a041e03020a06020a0204060e01051507080409052701050103201c0302061b09010e04050705120f0603010e1605010c17030906010e011d060f130906060312050c0d18 72
    0xb29038014000042105800800c8803411070f1040000b51010750b001000209029030041006550b4071101d000500000c0040070b03521007a600f4012403510540e04803129942c1004180690407030310140054174081503102818071541541d50881c242d542c207120140c0410503401d0482c00314518445501c050b120018602c140d4600b6001e1458000d004201c01600035030040020402241200000521024000d400307140c030b040c0071540040c06561007500a5801a41e0b12000a180d440c0124119407046070700145600641c41c1c5403800b48c00030320040b41c585009500704140c0d01043d48000034046114000ca1000d04100c5040600444510400b44411381e0812100303502d00100c0b001c990021402180d50f0000380c1483d41c10320a00c00c0071003106070b00254503886079201e03e140b0301401000d0300d0b400080865021521a101600180880070940110051a842c0400d4101000050740c0910b00710303803051094412150361880159000c1c06018005403058101c9460390241a12480300c150319005980f5691200e00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 51341496 1250 51340246 51340249
    0x70201020a0209060f0405130309050102071503091103010906151a0409020a0306030f060b0a06080c03040308060f0406080304090507050301030b0a0b060d060603200f0904050a0929011a041e0302 85
    0x20b401c00d80b0010858230b0700c3d4001000f0316034050381c08009030100780010a400c0e40f80c004101d050004803074491040590300e01c4590100321040c6c0040c1c0650380000d0090011007943e0a20400420801e03180780f09132200c050b40001c4003200244120703841c00703803080010306003490840014060f520502181c020160703501004000070780e44180405046000e420001a140e019505000b44010150084003d0184000800150199800443c0d5004e5031612f8840c500e61541030104901105031075038281c0c480c0c10241c01091485002010300119501000c1c1840b00f0344407050140d43c00e110a00001d00340f03011250002d009060309030458107440c01c020700708038900350b0085003450807140c468214000103515106012a00110466918049403d0412052070b2110002044240348950342030680240e031a00001149080c0603400b07400840d4004c0d40c0d080e0000d0703070004244031603a5007041c0c0381e0000d00340d40c2c000f1032207a54100d8807040346100d11b07415518150030000c4155043c041c031400d16007007615071200030005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 51342746 1250 51341496 51341501
    0xa03030b060d02160b0f060d150e0d03020c01050a05161812060b040b03120d110405030601030c0501020601090b060a031109030d020c010e0306160507030c0602030c0a090b070201020a0209060f04 85
    0xb100d8442c3c00c4c0e80301c552051400764070400d00170300f1107200ca082c001c1c10310502d42e0714540054000703607000c40c002600c82c0788695002d0142064410040d518042e044078040c0b85905500145042c0717400e41c0081200d03940f510b100700112134055440901000d5840034800c06640292100012601903030750b520100f607620a07580f000003182400403105651112444100c0b81003601440c0391241c0d007240070b090440d05d030100d000c8540c003034100c18200d070540b100c48004002500104503809000d010b02901c81c60740e12810005088130b00d600c1114014882c0d04000138a1410324802d031001854001c1c242460b01420910890150a1181000c25403c008000303182c400c0da81003280d072003130300055000b4004400d480c0f400035043d068074000040c02038009808005070585400c03261030000700341e820141d0300c441d80c0f801c0846a0b03244040700140304078400414003038900c00000c050305000302240c0e154603000d521001c1d100002d025407000240503a1181c0040c0d001840c0a03401c2c554011000303029042c42d82c1651000605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 51343996 1250 51342746 51342757
    0x9120703030b0f0108071e0504120b0f0105091e07030b10020601052115090c1008101505030a0c0e03070f0f0e06010203030a1802150306041d0a03030b060d02 69
    0x7281c0d0382d003510411410030614007041e0802c2400c10642c4c914005501078510b00e001c00011010307500c0121400d02c82130003081a9000362074218031010700303890f540c600350700e424000340c929501210500c000001ca034504102074510480010b40040c1c1e07201050081c40101328005043c09081c1600c0340d000c40a151100e84910311074550342d90042c0b1440d4034040500011903003000c4009103107007003040100f68440001031816038490300b01081709030940e543c101c0790703007040003210b609a88030076144810540c2c0390344071581900401c182e26028030b6099480c048400008080007280010520610000b44202101c0e4007090f1458010700380000f10181d90b0380064103001e12504445600000c401052050455504105018000240170340d00c2d00d050010011f552404002d146881158642d800e03e0b10301000b100d040d0740c220798060401c40010180f10404142500115001402103244c51001f080c100e25800c0040d040c0c0100304050000d07140c3c140c404802410b6070b402202d402801c2040f600ea01601c80380b00821 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 51345246 1250 51343996 51344003
    0xf070309030218150f0604030b0c13080607020c010503040b0103020405090a02040618050a020405011b110307060302030406050a052e150306030302120c10020904140a0506040f06150305091207 84
    0x80f0b140303441001e480c802c25500740c0035805600d1a00c048a101d4031500201c0701640e410640c0c1c4141651455a00342c041c0c810b061080ca00d00e00c021000141e1039000080d11401001e440d001d1303c146440c1c540044609000441c0c0251081c0d042e0001040981407030b0307201641002c0d2131801d4076003903a020b40114040e2a4503a00104920740d91112119511002d84103250f0804064903080d8501840c100000f00b4801072040c2c400c0210710700109030003c00c40d1603140d0402620001d01030310303c841d54402011f130080d0004c64003614101d040c0b200140c0400c400e485554800c4801c2c2c0103541142c150b00d4070090a1302001944c079240503030914804502e4060340300d0160b40c4810203940102d282e908504c1d009082100d16550b901205409002507005501c010a01e0b040f40c100401005840f501886c00090203080541e20307116519205400b400f1000c1c070680c10840c82581c081d02e0a10500307817902d03020802c03030b00f141c4038120490366000c02104440f4402d400141d00440e820048070600e119048100480f07600500c0300301c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 51346496 1250 51345246 51345289
    0x80f03180d0504080d08040f08090604080703060203040c05010c02030a060b011403130c050901081906110711010912020a140612180706050405030a0f06110711030601050f060f0703090302 82
    0x7040400c2d0b080118600440442c582401181010f98460440000d080802011202c003c00d0ae4001c54541d5401c0da0000c144031340441e02c04540d2420507100a50003603500f5645882401d4001c160365010700085062a98054024101d20402e610754800030301c05014407a04001001c2a403203c1690400042c0d4040c410468044090b40d08500d02081803d80c3c560100c0d0140b00c00034010018250040f032a0080c04040442c9294041d0003031420400030039848081d81300c44c480200700b500a2040300d450030704011f88280c03079000c003454540762a45210520a207009510074002c00080c4070240c900c0390300e020740046c0a8030007824400d10380c0c054148074034100c1e0f0031b001401c41da000174095500208260780090000741060b510b410305040120b034490218600140140c1780d400018402c01080e64400d900c400c1c0451b03003e60b152866850a501d10f02205c8030308900c00e21071800041030b14907211020440d13045004059901e082c401110001154118020640134440c8041001025882c3c402e040500c19030f454100c1d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 51347746 1250 51346496 51346499
    0x30f07051509010e07090e070e01170c010905060901030b0f12061608040c05060a1403010602030c070f050f0d05070305060a02030405012004330e0a090207080f03180d0504 75
    0x81e0100100003411210340b82c1c105800000841c1d804034098050f105848801f140c489450703400e0620b0102160322000061000400014130312401c41e04e080101c11402d000d0311100d80140004646012035406807941c030000c2004184000d60295200c642c0610001c0c3c141d00c0003106400000d45550011503041c0e04a41108007080700c1940c03400d0200c0d51080e243e080007800c80c101900d03031101c01d40c11070107000d0082e5000600314203014094442546000c4900504980e65038584400a407250801a6101418810000041800405003501c9401d6850140c803240c802c640c100104600d522250b1410b48081c0500c0202202240040c000580f15840c034450142e076900305403070705e282101c000c403400b01220b0b1100042e001000521400316400c41c0d85c5d840510f450f07065000240002180c803901100c3c0e070f030034210004440454100d403105070248821940c0c0380c0c00d99904c880391801c0e403184440090440400b004081e1003264400007841d048940a44200300c0d810b401c41d80103260003d0405c159021401c00f190 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 51348996 1250 51347746 51347773
    0x5070306140c070507060c02030f061513020708090d031808160803030403080403080c120405060603160e0423150109050603010e06040209040f0b01030c0e0a020f1b030f0705 76
    0xc809800000120300b407843c3c80000d0321216150401e500a440c03c100414201d40d00755a010403010070720b20007603c180c450314140340400b03030201c0a40600050240301c2041ea42e80003003130b0a1098800d40c6400801d1107103094910f008104100c5003c40e02102070180900e184c1c044441000e1002c0c0250a400300140050058a440b140010040b544040507587c4108200b20020340c1c0584920f800ca503050a1076900e50f2038410f101c0043d07020384960015aa60b180042000b4050001100c601500b0240e05581c41910003d081c0d03540a0494040c06060401301001304000501d081c4500c0d242060001c0301003007299003c4603042c102105d0003880c00600781d0f4500140041d110f544205504010120020000c1038100b92006403114001070010340302d00e03072000c0041c0601070030000200105900078230600340d41d030316454000c00303c51440c01910308ac005c0c0f420000b442503000b4800c80d031203007822a03000e504080300d0b80c44114a81c01140c030403858a0000340600c203601a01c4030b01030840c43e40708401038554000e0207034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 51350246 1250 51348996 51349031
    0x4020405041a0c18040605100c1403070503030105040b040207050d0c060f0f0902010905040507090501030b0d020909060403030e0105040201050301051905030105090a110f0a050907030207120c0203060601020c0a170a05070306 98
    0x4113103520032031078202c041042e83c0d280031280708486c03000c0c05d1100c580102800e20141010309a8282400e41c08009402c00800c900403000f141620012102048021101d4090008901070000d00034215400802548005030080d1442d1050354851840411500100b01c284003e8030907820203040840d0710b9102c180d003150303040480348024107400d032401c01c050325110314000e055142500c40c1505141d601d4a00784042d8035140322a003521a00130340703421090700301460081c1d5a1081140c042d000070f440d0804141c1c1000c010b0154500a60f0140d442e1410740e4207020403c000350b0505c80b45490181c80e54000000c10b92070038010a442140004007030200760802d420104608680d8220302841605002c0640845940d84242a800e0342d00998041c8150303507504030709500912070840080c14200700683d202e511958041c802140c1d2610075402d403082500c0c0d0000681e40d40c0e042018441e4000807414040c442ca5002404a40c405140da000b220000c2442c3c0d1115400c1c11110781003920803540b103c6000070000c6105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 51351496 1250 51350246 51350287
    0x902010e010206070806010e06090603013506010b0a1806020c10111b13020304060207060f09021302030601020124080105010e0705070209071422060309030804020405041a0c 76
    0x2c1c005800300d0f141c041c0c001004454001c1c000b40c103003e40240c034400941c840302e00f030307500f0800c2c017900030390740c03540c407516042908080e0954180103103100c0480960b141d0300310b1860b0005080c052004003540d900b004107a0841e80c100d070001b0010009440c0010080070700d01e109020050003180c019151001400c4140501c2e00ca0320490f030310510920f000301d980902c00028650420400c3d08464142506140002079003c0c0714190310b9204040c008824017081c00304541c014840140700e50f108000044c0324610190560700c000c031020b54043e4106544e2080601d0350780007554440c2c014400090042604500c2281d5500121107600d50500408800e100b95030092107658003400801c030341c0340036920b00034500030311500c03035554002d004040d0b51b804544c00c80d00500b603021541c9682c00d4510341318071000720b4501d100c2107401d180c10513030542c64500181c2280039201d11000c65816513100242983c0e03a40034880a400003070300445440f4112406a643ca012030701c4858000d0706c0c030a1800356524031180da594801e2501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 51352746 1250 51351496 51351499
    0x9061d0c010314041707240b0906010e010c05071802031e01030203070b070c0506030a0911091e04050a080304030f020610150e010306050411090429060c19060902010e 73
    0x8002400b0100b8100c4a0500e42c0203070b001605c031401101c80801c1d101680a080d400601e4880320802c80502c0f202c9101410f1036400c02c1d02010802407840034100001c0400584101d808503580c0010b20341c10b5442402d400b2080d038040c004132000346a1b180c0440e03121944600124018607808001c1c025a02d009030540500c8000703105400e6859411600083d13203461951107952000304000510804000e501d454650003000d00030501c644920b041d00700304000c3e0180c3c2e0003c42e050014205170301d8003480c01c680e03428000c00c0e401e480112400e0315240c803101845030107401500c586c403c50410b40b0001d0321342001184641e1090369134401c02d50500a000e80392404c0500348a101803401c1d201400190300b0025076080070507961600211199401c40103030300034103190300200e40041c10700000001d424603040041a41c158251010089415241d0540030614440c00c500040541d840192161a10b091006440302200c408203481c0d501110041d0300541070320f07079107045400726103403840b802c15036810900b4007444800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 51353996 1250 51352746 51352751
    0x1407030503010b0a031418010c17010b0a050d0515090a05060d02010c0201180b04060e0f03030a0309051005011d07050304020d140a051203010806010f0803030402040f09061d0c0103 79
    0x116a005003460005010340c1c2c42041021400d940c10600c00d41000e044502500406452030a010186d00c1544031035515642c100d43c04d103407030030b4403083c401e12a198082d1781003400003000b81d082030600c01d290303400120340600300102800300e8001e000d0b4500c18a8082d14045205010015014040c05900d420040c50214494030701800c2100c80d8584d050041a81a424030b0075150700f505510041c1c0e05841c2001301c54059052201c40072900314007a0004000b900d640d500c540c01d10300982c01c100311819080d0712640e901034000b44001d15005000342c0240580c14480c5017a2040042d013420040d003207410903031140d000000707010300e0000340051100e1501c0d00803405180040c55850300340c003c0762003581900001000700b45011002c0703420800900003004c9042c2e0140580c2d142c0c00d0000030a40e000c0e04207000b90340b228050300c8000206001d0784d00718442151400740107141195255020400100040c00040080c0c58443c0d004100040692081045801e4100808201c0340043c0500c04d1800e41e40d4520300b4181403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 51355246 1250 51353996 51354007
    0x606090e0408030c1b011b030b10020c09041707050c1507020904020f01112d0a0b0a110912011406041a0d05150103030f140301030c12030905090703090314 68
    0xb240380c01225803200b541900c0b5952900e19403c141c107141ea030704400300b18a51070440140040c1d0380d11503140c1e1380201240c0e004c3c402c401401080148540c0d8000e141c0700580d1100100d91030900340009102e5016004a5011303240c40e08104507046590300925040b84e0030f800100307004032589003501240000313100010049007069207030ba020400405c80900301920030508000c080c079040c0c1c482c002186190144005680c220102c928564580607402c11300205c800344051100e00d865080011120ad110303411021030121500d030b0360108030040c4610008000180c2c020003d011854540d0b414200b07200c00c0141c00080c2c0c22a20f5041c240d002500942002c0c070813424003440300000c1c081c241d00c0040481d030490303018483c018107152803807030003424509105001c0311034000002815006015901d00801584660600a004510380340840c030090000402c010318005040c01001605800d0501180c400c0c1001841162203c0010b0b51800040740c2e00400a82c64914040815030b208a58a05c00301d2800c84503070904 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 51356496 1250 51355246 51355253
    0x5070e0604050d051f0609061a030c031305031303050105070c111302040302040504110a060c030504030b04050312090c0a0807080c091f080106060e030d08011e08010f0606090e04 78
    0x41c400c070300c2014072a0a00d4030480c0c0034480b080c007241075071000405480d100c2001c030f030700150050580ca01c03c0b5100305113004c0300000c40818040c0c10341010109800054a940d84414440e810307500003900c2c000140d888010201d00086080009207525161b000320340010713038a5840c0641c20b5500040040e41000b0441603007500088840441e445160f108962006d03c034040230070380a000303009550019510078104024041403040000054241d00c2d41a61404111034442c9001d80d400b41c200c0c07000400003401044100080740030802d81a030400d1141d002d0768500303101000d0306481910140d510305129080103080e04a00c1c40e004014000a01400e4040c0c082c6074030f400c02032070b119031440d91201d02a500c0c880000f07030041804c1113008082d20186001d50111515034a0041c0204018019600856035284850603107290000d1601421174003503840002d81e80c00c040b01c0c00070010704d41008800c01d034807507080450509004c1c000c1101e0300b0080100010481d2401d0740040c002c0400343d001d450550544030520010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 51357746 1250 51356496 51356509
    0x624090403050d0e07030f120f0804110103060315060501030c0212030a02030a090f03020d0e01051606110c100504020906040e07090b060910050d0e030406020705011b050105041505070e 81
    0x54041c18080d88400a9003c0e441c00b5000240200125000300c0c5404000c20901c4009000d4250040518050103140c105094924440010700c0c00c1c0031601240010f000580301500d0414481418507000c150a42d0b00e640d81a070106140109030b40b050b4603148144403659262040c0401c40d40c8a1005041c00e21800c0e55418103803001034450418103400000040c1d0820564120002450f40301d804002c46042a08009460750f40c0004030a000400c150064032071580b00e00156a07144650014900e1950384995800c8002c00c4a44402110002c4c24000c00031005030078031202000212040000c1410320b068410400d04030402404c440c400d5260a083d80c03102c1c00000358000c19506104070016039081c180002400c40c0c000c0518469000d032218100829059110000e00152054620180078560b030300014a034070ad00990007410010307400000b040015604c10794043c2484884044031021486281d01c406003034910498083d507240d0340501070460318a04511600760310880c0307894116007c440403400540c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 51358996 1250 51357746 51357751
    0x509040203041412030405060a020301060905040915050115020f060c03010302091f06050901080703060602210705011107051b0d0b0402011205070801090609091101030213090e062409 80
    0x6698080300003001c0242c2c514050011280600c125000350801e001c0107112640101c504071850f010740404104424194004e40e030603210f00b515484600c43c10702e024003000308044001918214291811000000341030300c1860f018008640c0708007640f9a1091002c2d117000405200c60303040703070322240c208000700c0964400d0f01c3c1900e604594240b52500d03040c4414551440c1440c2c2c00d00040124607001500070b03048002445c016400380c030b42e4a081e82e28520254111840c034410900560031000c402208403000600038041c020b0a1081d40c2e042207110f032926802c4400328540c0480700a0f0004000040c08410000307030354419495648000c2d0a418a00803d00b051114170000304501f041c000400c0071a80901240e009455000c1c004014510303142170000c10201082c410200b60510b020004a01c1043d60f00480d030a41e50042c00c1402140041c0e40110700a501261002c1c0f800c036060071000c2014245c034001c40895600d0000148107a081c5a112607075028980b1038109040c0c0b584031100125911006880c0d42d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51360246 1250 51358996 51358999
    0x30c090507020a080d021201140907030b0301060306020f040816080706140910080f010816051c02030a0623090c010309060b04090b01150f0212090609091302031203070509 75
    0x1155164894103074030301a03c0700001004000003095a64030b6800b03070360207045c544003e04000ca0182c0d995400405403034240000300e6801c801c85100103802c01c0e000f604080686034010b000010440d540352691422a089403882146210700064100040c800800c1940300b08070640d00da00c0c08061034181030968828851160b0010300c44a6201b40c1804104881a140c003000b029114010981801c00b00030003d19007150012036090355030380003040001e40041c0c0501c1c1c0135035484c001501c040c100000c00c01504111300714904840102c0b0301d08001a101804102500c91054201040d804168182401411038141072000050301d00000c000390240c00142d081d900c41c200f8240010440c0140c02c004010300102010079420038103000b8010100201244468126011011050104031041004943c0c42101050070b0005910842d0b10700c00c0050880024110900000c00091404000748007207051040c0488846404c41000c003a10f1084d0305090043d13700480c410b001903441c51400c200d0141031401411001c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51361496 1250 51360246 51360251
    0x60e0102030d050402030106120503031006020d020c0f030a0507030b09010606020c1302160501020301080309030c0402040302090f0907030c06092102060a110307060204030b04020a06020c01020d0f05190504060e030601030c09 98
    0x4c2c0035500c0c290b1001024203404d0301300c1e032000e40841c18455582e1f4419a00c1c01a68112024002000303807012416200c44002603000d4501960300000308803070303ca000c2c4a016890b0007412800740002e401001000001e511039148800700f803030302003d12801c50f542c40c0d000c0c2055401024ac01c600c19a0350103d031500a6107800380050f1101803e04803000080d81240004060350301c00400480d003040c00101602010001703c040304c04407003071242840140d00880c4002900001d0207800b05100a4101d0302c180e0340b05541c08200c481041d41c9484280c40e92415521400219010400901042010003424074003e482003555120150349540450b01d144180310750300080150f000d9503605803500a004803030000f90130010540d181c070f459003401d101c52441501c00f203100b007402900014945001140c41c00e44020705801800350401d04040568104035540c00010822500f0480c041080310b003880300c0c182209050742c4464541d800c040c800b500140b65051a148681d01c480300400c0001c4541401a080e1010031101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51362746 1250 51361496 51361501
    0x10b0301030c15020a06060311130b0a030f030c060c030c0f02031207030506060705150105040b03060709060e0607020d03202b020114010618120302031617040e0f01060e0102030d05 79
    0x417810314000c00001005035040803000420300407041802c13500c42c001110440800020300d020345080b5144400d00310b0300b00b241e407102003011480c2081801c1800e800303030600301c1c480041a9184805c40f0186000580403907aa01009181903602020000074030384103000842c5880b070441c4d180b01304c10000a0205040644400000d00b0a40320316082e59a41a03000f41182c00b40d01c100d91080c40707061000d015042c0540d282c90382400c4c081c540010780c50b020340d01d581c44440d40c2509000381165281c4160082c542c005008001d40130068950b450703d4101140603581e4900060201d80e201e40300030b00740b01d5810030740e40e00c0544200050340140c1840e240410482500400c400c0203048182d0140014090b2040c3c040070080001a41c16001000c00d5030609115001200540d00c0e5004040d900c0740740d14018006902c2808010401c0d40070000940056000307000007030700c44600d05c0c041c0c2855485600440c16010001d400d021a00101130f0110f40980010b0405024540103000000e41d240102840400da1310303102c001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51363996 1250 51362746 51362789
    0x105030612070b1b0c06280302120f16021c1206090501080a060b0103050c0a081b03011e0806040209070c06110307030b01020d0201060605040b09030f0303041a010b0301030c 76
    0xb0440040040a01060700c1d006008044849103a4089140b4075502409803012058a40401150f0764180849641c0a410410520f00340c40203416880c5801451b90030041f400c2950080d190740743c42110070f0f000700b554500d450402e6041d1030700880040000d640c4800c0080811800d0040180c6007040180340c511000e00c0350101c2038015007203561080136a186000c002042c041c0d404a01806281d010703140c00e0211564a000440845800b111700c8025500203200b10000284150312680d0030030392014180800c070700410300000c9240d100ba44000211500340d80542c40790140003921400801900d800f420583c40c2640110302210b100400c0002080410880241003010700e030b0140d044802c414481c2c81e1a40307860203014006102c0760314079602601c070b4450380095581c814020756082e25010ba41d814101884c00031850895040580307056454040c1250f01c035101c0c8c2003000038510460040604d02c000440140585c20b4210060b000003400490810051011446450f0084100d410b004014005900c0315007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51365246 1250 51363996 51364003
    0x7060506270105040f140a05040209010b0f180d0b0f010f0806060a12150504030c0b0132040b0d08090f0a0317070606081507030506060705120d090b09030a080105010804020105030612 80
    0xc1d4903000412110071f1082c8400141c5c480c2d403255200766070f081e200c3d90301c0348004025401242c119103c4a0000c0140c1c10091b550720281e40c11406001d0002448080700d95103204543d1405c4511050082e04100100283e80341092202c3c01090b48502502090038040c0c08107107062000d01802090a140c00e080d181003010485480503000050300d010800e509051500400f489140741003642c80010b084e00204094000c1998400b015000b403240c0d800d074011500c51001802000e80070140e205130f55903200a05501c40300307a0031001910074480306030f85034034190401c00b5808041c035016014650a1405000186016698072041000c20701e800b0346910040c40e041010384a581c00035001070180f0740c06da0001d504000002030142480d03880502c1a40d841c801804040e0043c2c0c000603055501030551048103a08035402000c40d003013012808100260300c1e4541c050f4500c025217074514a03900c000780317401c4c070386601400117805842c0918042000b8201600001d0203800064070091003554404403140c4117502c00c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51366496 1250 51365246 51365261
    0x1206060e0f061c0203091b3106060302040518040b04030806031207060906061a07030c050309040e030a020d020102070206070204021602130e060c090d140f0307060506270105040f 78
    0x40001107100e40c200ca00032002e1740003902e0240e094415a4401c1460001c1411859900300c000b814401003480204451204119807801c1103295a540000681421001e40214002b81816032070141e03589181400f40718040e20070301e6201e81c2c2c40f8404024000003810410328540c02070341501d0207a1726038a6880001e424208030040018a45500003252002c120840d0450900c039801600100607041c0c1c2e450308a0780d805200c161603580c00d00c0c10030084000034054002601998091411039080440102c0814100d801a10b248020341c1d00100320505495810445c0307401c0d1440500c000d5080401950100d880d0f4014920300a11039500400d02014001c2c80440143c2c1241c3c00500030340e14400d418050400500340e602010405001c2d9000044a40304400708581c410700d0080c0c902100e0280366140d210003151100c0c5800c506000b408076622181c00208042e0070603d018001c0082d075070401c0e07c100300114808020b0140c20300c080c1d1604103407030340b1070400d4681160f806680100f84d00c0c0100f2450740003400103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51367746 1250 51366496 51366517
    0xc030c04080105040c030b06040c0e0112020903011d0d02150703090305070b0f1006020f0c01080405070308040b040609050108090d180302090a0c020c15030402100c0b070806011206060e0f06 83
    0x2c010804c4203000c3d090141e035003103070701400000c01140c44a8003804180d40540701480d01003042e00300190b00702e5124102c4000b000c1d83c40b200050a1800321000070707080d030f1100280714015010305182143c54903400c6c858a10501c0e180d000038080d00e060104c080401d071900030040024075580d41800411b00d4001c00031901400e41c010350a400d10324100804a00c1004203035000780c400c0b1780d420b01c0824a540002041103d40c040075004003070502445004685190008104072020b000e2600d00100107031160020384058101907111319141c0f410044001c154114540c04031b4104000745003804280800420691004041131900f944480c1038101d001c030b00f10f00342d680000c0d0000c21030020412424425407140d9078003d810340c02d9582081954082104400007558a0303c58142d0070400f203001841c000650641030000381c14034111040c40d41d110510209802c58103040840e4150023002990340e40944408024020100104225820910f008020010424a46006800c1003c1e951000d503540c03801d036104101c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51368996 1250 51367746 51367751
    0x903110a0b030906040c05010201110405040203041718040f0902060304020405041713150203091f02010908070303020901080609011215200d0c030902060a030203070c020a0f18140c030c040801 84
    0x40060a0f80d40c2d070981210250f46088520b00080ba00358410701882106180f50540d0382c3c18141000c08200080d8800340c8101c072084d01c211240303000403501c50040c00b5842024402d18a04805c84003d00007030b28181313418296070030315181103000141d03602002d0b2900203030140d50004003a541c51400180190820ac0c220143c108045001d22442c50160441e40507220100e51441c041502d0b4001a60b0b203004000d1020b40c020b801c418007595000f40c92044184400151001040a1174151900006030f88080026000290000b03540201c03940c10680180d00250240c4160999600d41b40b140540d42c8600640141800220b00001081060b00d4002e1041c4054024400c1120581e16520480ea54000706034211458184201c807000c15000348141d0580c01e0b0003600e00f9180890b2068110000e40c0021700e040c0502110100d49009a241e0020050143c9a4080800089800d080d4094941040040615080b6042a211740105031024424681010b42c240400780c682c1c48198584005004507041004c10b0361 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51370246 1250 51368996 51369001
    0xb0a0e120a02010608070501050a1115040b060f030601033807020d08090303060a151b0b07030e03030c0d09081605010b040513022803020d0b061504060903110a0b03 72
    0x2580030300500590001d5002046844d903208105611040c0510840c0c0c0845d20a2003101000e0b405014803400c1c1c02050000d507041001000020080c5080585040d121548a13204020050400010380c69a122081b0028a070a40c556a1107100c5040043c0d0100c2c000884444248203954521406d4189010440780070340041c64280802541e50240382c03540c3c0000740d0b0440101d1403285020084901580c4080c1900c03400324104101c50520075000c1006100300410740c8a0000b01d00304440c5a8a42207100c0d40c00c1007614180500b004094a03800310107030015801c00c105201c110341c000800c813211100b42600214800c806401c00f80d907d405813007a40220201c010b43c1803020030206600041c8507010458040105441e14208040c0401e1880030003500501040041d00142d0300e100091038074184030b00f0f062110030307850783e0101c1c4945166160072503c2085210034403000b07151480c0d6030200ca01c003100c007650400f407030300c20002c040300c10510015114422043c0360060544402007100c0180c140000296940d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51371496 1250 51370246 51370273
    0x1501110705030619050f1303031104080303040c0f0b12010302040b0604170106030302010617030318010f020f090a051212090627030d02070b0f0d0213150e0415030b0a0e 74
    0x4030040b03413580c4602440d00c8002000d0a0503000b44902805907281a000c2c112100d0341c040d0000c003c075041001d4032220074040001d40030410801588964071030082c4224407450148455101002504501110141030140904800070171030302e281103d804075804202044201c1c080f480710310503500a481003441c540f0107000900c405400601c100da10a9000304145540c412080c806583e0140031a550350300200040f540c10254030103d80b20040ba040000a58881c0308200700c0c04076070010200c820340100c0416003010a01e000341103040200000c0e600000c00c1110424811307160704100b504191581c0000c034a801080d182e8405072240107450101d041244016141c25175803064410001074841d03c110211201200d2001c54034a08a48800d84072a0034159141e402c00280d40141d81f401c4039035036080c0a80c1141c2641c03c02240e00400b081080001d1465601074000c00340d1a03e07485803070003681030480308514400030307207440e00450350065560400390b1281300110340541a600e01943d028440d010030403104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51372746 1250 51371496 51371521
    0x60301030807110d0f0201032003070c0317040221160306050103111503070c17040906060906090e04020607060f05070201050601030b03060912030415180c050915011107050306 77
    0x12038000c03084940b43d00f0700c0704200a25808001c00040003540d191000c031005500941042d400d50072032409101c1c001200c04103242d820340007101c2100000320304089100606400c070040c403450510b203031803c0260345410707000b0030600f000f900342c540204803042288895020040c04040c1c9445000d01d20006c00b03590340d0402c2805043c0a02082d1106100c06030800340134a0441e9501d000c5002295900e030640d910b014058071041d1005400f0754980500302c0e15807565801400041001d0480c085000030f0250400708002c00f05111070f0015000c0c854003801c00e01c03819600c00c03052a40035504a40103681c800c0725281003000303800d460101040c95030400040c0071006806400c001d10032078003aa81000804071070410195504015190303802d8030740010080c007500444040046500c14001d074810346800c1c40041c07024088907010010408108001144807040104a1400030000c01080310304c1042410702d414010080308540c01c0c40d03030612500c903204000000c420301c8000c001b824020156a40d81c81c040f00030201e0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51373996 1250 51372746 51372757
    0x30703030902011d09010b0c0c04050a020403030905011418040b03031603022509020901050c070305010905070504020a0f0c140a0503130e0c0307030b01020a0215120901020306030a0314090603010308 87
    0x130031025210b02003107502183c1280c60012005203075410030b03403800d100419150706c540001c0348a0b006075159440140c0741c83c02454000d403a16000182c3e20303860341c24000d2022080303422007810007404038a0120b2140076402500c1d0750002002440a81700040000a8001e04100005a4040c000800c046411021600c10030314030381e00a80a950a120011b12009111800380d00341d1011406000000d1080090a501800c010342060602c51b2414060501e9036140030300f2540300b01c605070b440f050360908000d400d0040000616080e10705505040c1c2d15207001d082c01220b540140100140c231500102407000c8402ca440302c580d00401560a844040d040183d1030b54095020f4601c80c0450a000154880c1d01d070031520300c00d08070342014500710f80380d515080b80600400490380303046200e0b03414442c0c0136070340322002ea03984443c07003a0031141e440a0070701072094010f2000b4140d2825910500400c5501c1d107000c54404840d90741441d290780292003070050042c0a0186130a1a034000c04080004410030020030010720 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51375246 1250 51373996 51373999
    0x60305040611090114030c0409090f03030e0615010804151e050c09061917010b030405010c0315120201111b1305010f0302040203040204020702031f0e0f030712050c030703030902 78
    0x11107014542c8419010307110f21000341c2d0008081010300b0401c0303840ca002440c1c02484d4481c00a1521341e88103800400d44140c0c1c40152131246079505880308140d014851110000c1080010b49050f103450860030b017449003181034060501003128005010044460b07512411410b068404201d029281c084020a00c0180301810080d1413400c2d0204412b009140241c51164000030040340c07511180030b81c0700321120701010119060050103200c030000d00b10b9103e0744d540a07024000d4040e84900d86403d1603425902204036010905162408024415101456038025603a170310441200d10316181c8012110034024002140307803400350f00f004416a5400c1581f0301e0040d41c080f036680821404404c0350008859080c81280020803800d40100010304041c2c01a65015000400040c1050042d0700460300304200c41b4001c0700d0000201c084520002c00c03502c2001710f80c04000c40104140d96036010041d0f0343c0d1050340406440c2c01c2c1e151b0200d4024620030400c65150a1070b40b025281c5400d0580740140c05004000c1040303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51376496 1250 51375246 51375251
    0x20303060f03070b040902160c080312070e090402040b062101080d09060f0e040209060c1f0e06010302090603071502070e01090e0a150608011a04050a050903070b0703060f0603050406 80
    0x603041d8500042e25400b6582c0040c1c1661610740f40100d904003d5100244c1d0380c00d1450304081c040d0100d2825001800100350030360256a40d1200b10407030960380710000381084280711100b14822801c0e05d4101225a02c10ba06407800070301c0e2004580018001d00842400c0d004000c5516040ca980740c031507a11103412140800c0890700c0700041e03440705486241c1070f030064000180046002c401030500c5401d401c007000001a10040c54980c0f041c2c0411900d600c51201607016a2108580c16498000c01c0050000241d0300c0000300f0000700e04c4882c2686428041c070000e80f0982d081c902048044e075042c0200030050030446800501c40440140181d2130300b41c54491881d801400c0f00002812029600480c651811001e000e007002c520f1039920100b4041c0700b0050180503ea44a0002c11211400d105052004910528806100400808020640e44002c010206040c10402800f201040c008160380f0990751010280b502661108000c034024480756105110b00e4200d04000103c20ba05a03000701c0c0664000c0c40305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51377746 1250 51376496 51376519
    0x50708010e031606050717090c030706050a0c02060304020a050901120b0a0218010c0303060806070201090203120403020901061b080f07030e04050402010f120b031c0210050403121d01050702030306 86
    0x301c645070b000e4000030103800e11120040300e0010340150702c441d511036003900f04840094242400d84ca00b40d0011206000b4660120140d401c0303500e0100010002410341d490024070f000c244910040c4400c400b040001d000c2e00010000c1800c65503002c080342c001e81000303000f8900c190307500d240c00c03031014070451415a4074084410204027103100340d00885040d500c8401d40034822030300352801154200c0c01035030240c0c00c0664401000c942010705205090107201d01d40d00104e101403d5004060500b8081d4520381000d0008100403c010380303603080050f04446503424032150002070100503c0141e00149001020100c0004100c0900c07524000500441d0f0300951344e01c4500c0c20f609051204503001600c0203404205d044109460007885212442404500d0803c04218600805c0c082403400e0f140640c0440580c090090303003c1e000e0760412482c15200c880072024096407c10791400b41c02c204400410141481e216006105204100e80c8042e58200d61392008201038640010000d40300d0b0010340d800c91080c1e404031034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51378996 1250 51377746 51377771
    0xc030307062f03060f130e0d020c0a03050d0c0c080102041206050603010b0306061002010b0a030515220201050708040513140106050403152703080702010501050607080703030905030f0705070801 85
    0x403002c503a8400746030b40520715200c0000700555020301814460f408030804802880300103c6006110444410360020316420100d8800603043c20b5071744006a0180c200100c00704086000041c4012001c41c044c10a03c1d08110a03040008000300d0755000100950300004001810320b080b2416104c610380500c1c82000b060b01c03000c04060030781d1026484107078142d1106000c00e5091a10b0030003c13440003800c0c0000140c0d400b8001c04038041d08041d0f441522542c204d505003005003181070790480e904c00000701e0405400106410624011600b030750001e070401402140940420490f58100e4000d4071008042100d0307403200302425805060001382c2c12016450f10b000004201d401034003554146d1368442800c0526081a201580060400041d0407000c08a4180c0d1b203a4106500c0500e204e00c0d5009a031480c035140340c00c910113400c0d2001a0300003409500c0411504010034a00f00a407129079926190220f040120344c2081450750060b6071000ba1030364000940601003007030000f050340c11902c102d0028440c0081400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51380246 1250 51378996 51379061
    0xf1502090a1e050622050a081b06040513020d0b01090302030d1412010902090103060504020406020d0503060d0c0806040b010e04110103020a120c020106091505010818010f02030705040e0f0601050414030c03030706 93
    0x42130b02070b0b50f480320005410a190980c051076489001a084a060bd60741c0c00c00281110049588044c0240d40041d5458089000340205002c8103001e0070242109803640d40840e5550381220740c1002000f107221100d07401c03407200380200c40d440c0b014040310a44550b1590840d2009500c4001b000d40070034035005002601742000e0007650100c07406500640884940520152910381c0000c1006621225030744035540003035000c204000140a0101c0101241d00e00342c07402c032040c2801a00108035a8005500f08000200f044201c56051a82840d002da00e03030050040503904640c502034440c2d411810000c000d40240d0b8154014000c6a01e0158144a81880c440049100241e14001d050010b10404006007000440b4554040411030010000440300000801001284c06c103071840000140001070400c04d004007903c1c40c0e9000081c075800c1c0042403d0010000c0d240c0d2089101d0a0f40d02004010803140c65903081c02031402400020301525a00d03070903842c20400038100c0c041038640c13111920645114001514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51381496 1250 51380246 51380249
    0x507050d0f0216030c0510140c01020a1107051003020a05130e070212031003060b0d0c030b0105090708070c020f0a1a0a080c1303030c080f070f1502090a1e050622050a 73
    0xc1042915800d1009000e420f20948507000103000c100d200c05188148c0c08401800006840f100041e1a6900740d200107201a040a5440c0866406886c0c1400301c1e0f940d1122001405072035060040e0786030540340055509008174036020800721103070000003c3c165004c0000c42d2242c3d4450303007079031041880c086200b140c601080d03071402c0780c0c0c01c40e0981c28000690a0307401800100001090b140c0b4582040e42c1d0002c40c0e034480c1c3c000b10341c00d80503030340100210b0400c1111250022000e003030800d9145030a00c0010100c5107503940c003a100e6000001e800d1740303a032a0700b25048043c2101100c1d0b0014050721150510090f445041a800040c00000c0055065440741090b50121032540f008410003a01d1503c0840e41c1c0840d540781075580072000c200c00d10302482400000c0940c41d114080f90080d0000c1c1c0d04041c2c601c00c0a42c0c681d4031125004110080c00c0fa070b1840e41c89002d0712841445116001d10a0102050b02c62460f001241c20400000303074052800c01e54100140801906114044c3c0940c5513014400d181800f0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51382746 1250 51381496 51381503
    0xc03021b0d050303090a0309050a0602100f110708130504060e01090c090b0a0c0201030609020307170c0403020405040f0b060a060503071d06040618050f09040b070507050d0f021603 79
    0x6480d00101102803089a20315403002040010542400d4a0b010304642c4191500005603100301100d10400d40c0109200001300b07821541000c405203008400b07910340f280001c60243d62a175900b0364244205082c0c1c088040c0c10036407070480780c46130050703c0d00f11215406080c04c0c007000340b41e46100082500d032a014010542e00d844849035036503441c0a041c0c0e0081c02007010001c0070712880752804140c9a08010203400084007903500c0618001d401c1c0005400c8a01c9600410040d0380100f042090090700011804581c0640300d0207010b503503840c13a0386c1d00103031300a580000f50f1160518003031000b8001001d58100704140104d409a4490302e60000304189101d46100c0d60300400d9051001849182c000d441000302480c040044480c44c1c04450005510f941c0300b0341040c80445c100c00220b8280325a20305003000604070585135000c0a2a900d4006070b440c0d0750050004081994810004500c0f61044041ea42c989600008890540d100784102801500100032004e00510501d040a01a80e502c40c070303110100d941 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51383996 1250 51382746 51382753
    0x504080703080405010603020409080301031a0c030610120f05011a030601020c090a0b0a0303120b12030904020915040806040b07080402010804031b0b01080c0a060f080114011106040507080d0c0302 86
    0x201d980c103035aa09001030040d01d0035542d881c1d0000141c0c0715406001050b40c030a07040142e0300d6040d80303401d0181e940f25562002618810000b0499044000b0b0201d83d040354040b11103c01007a003108045503951071422100700b0302030038074890a5000000360003a0b4141d034000e224000c1404040c00114000e400b046499500607440302e0301103006820b003640300b260021051280400c40c00c400c00b0200e100355001d80d0086002921f2001900f01c088028401d1800b040c000b02ca110130800a401d616681d640211284a4802c0f60b0000d110084c81d91a100307251075622405400340d4403240e0b958681a00c800b0110340507920102c0000000e11140d205070845445660705844440e02512503450803541c02031558840040d58403101956004503181c40d000350700a01012004041d805212030510041e945070781d01420a01c000c591030201159080f00013103040d98104070000650f1100480121540549040841128000c000502c4148035011034800c0a4405100450702c40e049640c000701c07810942d000300980181c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51385246 1250 51383996 51384007
    0x15020106240806060909070f0e0103060b040504020310080607030207031805011d040209060c0a020307050907050d0b0d020d08090a0e010b0702150c03130312020303040b01050d0201030e0105011512050408 89
    0x50042c208281c1294000d13042a0078074200c800450401c000c16034403d4003081c0e03103a0310360000f50f41c4400c0180c2d6203007081c41c06205103860b190350707020140554011a84680e0700800065240b40c5064101c400500c8030504440990818010190003940308520950000303040c2d4801603a2100b071041e0303000450700113070b45041e12440d0b4011140e0b01802d0311101c3c5a07002c2d400b04083c0c1e0543c1d4525003d031554914050190201a845204051802c0281d070300950086503681d080292990300001034466501b294000840d8260b540400134414240c00000250304c8549905000d00307100e109005482d580e20203a42101da00354a54116081c0041c09108a49400804104070700040c101464406002204900340f54101000600c6107415a0064116220b0300039098070100148042c10640a4401403180059451402c1c140c0365a035100718140540380c0120060f0303002c0821a440796101e45040c412110081149507111010008900b000d508080c0c005070518000c103042001c1482058012640141000d03e0310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51386496 1250 51385246 51385319
    0x501050706020903010623120607080609040c0e0a0c030c08010b16020a030204050c030603070b03070503070c0809090103050c0109090b06030a0b0d05010f05040308070201050403020d141315020106 86
    0xc2d40f010003c20b82554840c84002240c2c280e241d138480700499000e2002071014051801e000d604101c20005640030340c03003034091203051604500c03000e80150090740e19030655a5142024840c2030030540c0442d014107450310810105170f2180c3e01800c0c5034103c1d990188403682e00c01c1c0c02200c0c038600c20302401ca801c1328100055070101c0c0f00000e00d100440d00c003400d140001d951b01d80006003140d4045682c1030156000008101d410b103002c3c054100035100140d2041d041d8104110014402d00006001d0f000b8441150000420b0200d058141e03160090000c0c0040d0080da10707072501903210340c001c4000d140803408e11306001c40d141449000764040f440015003030500307560340d850b00100542151110250000040e00b802c101041081c0190352924003c5072021400d41040e24008140b10340041041045916207400e100000b170303010803002414680742c036100b00840700d000b201d000544560801d22030890f000d04d10024400000d001c06c010001200d4008005c05980c030b80b9004580302d0000504c0c40102c5820241081c803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51387746 1250 51386496 51386501
    0x41415090a0e010f06030b090d0c120302043807050a060c0c12030203041b080a0201030e0313090603020307060f0206010b031306181b0b0703050304020d0c0b03011d010501050706 78
    0x1110300400003140e624640c0b116a42141e60384205085040c0c3c5600d03081c0180070721400c0c8583c102c1c083c18021300c184100c00e40d000b005480d0b0b03260010b02c607002100c0d070507807091710907019113014080204580307888011042100d02541820010369402c10420707498200c81c2c08031441551506608000505142d160940c0d914009040b1880840144100071a0100c003045449094035100001a2070050743e03400d0a00341804014440c1d03040c081e0b00030700084240800040402e010100c20360a09000c5040b810200354a421030049580f107601c000003500002662903026040041128001c1e03058400440d00e4a0b01115100c901802c8400564807240040108810301001560b0002c800003503c00441e505a4540003640d006240b0b00111200342c60459081c8000e80111042d1408801c03030104603070745080c51000e264020b850026050100102c00070b425512500d1031080c1d4581d102031049081c82d2202101c1c1c1d00c0360020700604015401d40f0041e075003403a01c901c0c00c881c1a03071016120365003080341c00e83d2008003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51388996 1250 51387746 51387751
    0x90c07030309050a050d0503090601051f120f0f06170c06070b18070b0d0b030d090b0d02040b0a020a050d0201090f0b0a020d0f0b030d0305011d0402061603080604141509 74
    0xc140c800d00108030007007901801b0041c00348059a50395680c80c10840c2509140c5081a080244075060000d2400960603223540046402a62410f142c030b04504400d07410300003481e0018030810001d09003800580755000076402101030300c101076050650a120b0101140d40d0303012821103160481c400304000004240c4d0000030302e51000440c07e4a005103001c1c01c0c001c41c2461440e500851a48078003056080c22100203014811a0800c03c1d0018000190701e280f00501d06140d40c03042c81849080029481c0c401c1d070f4250100c60251144200c150795440c0320b070070006d5451140b50360547d43d900440031f10103c0c061060261440b520703004040c01420a2032610f481e000300710007410b0814910b908102c051041c1045000d4240c000c4d004000000c0c3d0103429209250400d21012003034000c1504c3c110060000103a01c0c26080c250600011210000f66a0382c80454940d104001441100842d030011601c101540012028800c1d201618180721440040442c002e22000948048071211028500381e0106d0030300d50784480e03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51390246 1250 51388996 51389003
    0xf04080304150f020304060c0e0904060506010c140f240105010e01030b030a03030506030606150415030e0a08040515071a100f0b0c06010602150a09020105070c0b120105090c07030309 80
    0xd1100400700545046030f019800c06403540f030b00401088180050380c41041000d092904118500c101074800003044070000501c0240440e94ad0b1020480301d03480b5610f811010342c3c0c03105010364402c40c054182c1d65641442003514140381b0482d036542a107440008400915900c501620300066400c0c0310041d504500c5204d807841c1015a1032a00d400150f40c10001c45480071b000c1d4034006000c0c10014185410008014696805003900901040c14403904034102c90480f02c64803609031080d82c81c08421800303094040f03108480344c410b50b40302009001454005008482084808000ba00030210191606015085010f028071032640250f201660100d9001a8428920412248900c0e21107035a51142181a0020203940b940403031100011030003040124054651400108240352220307202105114000380b41029070b94071010300e1000c590207041541e004640c800401d03448180c80300c1c007280880c0c0185404556044440300001002d0514030340c40c0303000d24101089245002c8a03905d090f0003600c5840000c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51391496 1250 51390246 51390263
    0x702030d020415031103070906030902130e06010e011e030803060d06020a0c1b26100c0809011401050102030a030e070e01060f020744010603050309010906080f04080304 74
    0x2030004032207032009101900358140d001c0c511074100c0400908a40440f1420540e4000400a2251141d00041c01008a45c05440c002c1001c05141c0701265079403807140404402c040c100f0544000090b0302048150603241302070100300151703a9454589003045104180d0f0340111641036000d20201c2c2803d001194001c00113030540c2c0380c0c03144542e203885c101d92069008400007003d6010000400120711800304002e03209016003809641085161401200c0c89030842107038908c1c1d0304202d9918001030203054075003601508200140302c40001c019000c503070110350522441d4a454042c60400b1811041a4166201030b4021800c102e00100154020698041c08804520030380c2e10000d0440c2d5900d14560291295130783c1c1c4200c6914442d8041e15040864000d00b8524000c20060402c00310751015180291074100e0642070b034004141380b0307605100a1440307480140e500f041008001d100b800001480070345c0080e40e508284565803a811a1042000c0d108070240f02d080902040c040707240d410255030054050f403101c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51392746 1250 51391496 51391507
    0x3091003050903070c030809040b0f2b05010c020706080105011e0315080a05070e060603040b04030302031008061003020a062d02070b04030311010f0c08071805060d050f0109021908070203 82
    0x17124084482c4d03600803100d004e00060702961038140760084060140c0241c52219082000c10000b440b440100b9090004001040085c400c920400c1d0710f413036801b00e401c1070003040a04902007000351603403458003544001c10f0b040400001c06501c51490340c42c00e10072160804482651401c4102c0181c15407500303803015a076421201180240d41480141c1e521b03032040c4000c1c0341241c5410130368821200e00405261160005000300004101900144d40d44140d05207001607032a9110240c0138400441508408441d1050b181004a102c5a8401c40b100b903e0088903030310380c8030ba0ba425046a082d240d03802042d1000c203104800c007200c00c0c4c560f01e01400640c07450056030300098490102c0c01c9141c0040c0d0042d000281491614100103c00f0b10801c00901000e90050002411201e0042e005004c00f83c882c104200c4224011078450b1003051555015080081000f03550700c50034000140508070071b9500170b0040f0301d45c40000032a5007680c401c560150720321000e5282c03c42c202e0031098503c410024106419404108003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51393996 1250 51392746 51392753
    0xf020d0f0519090f080106080d120609090303050402040b060a0c0305130305012a020a020901050105090a050306010b07060f090c15050405041803020f0a03080a0207081b0f0f0309100305090307 84
    0x80d1030000301d01942c40300e46076460950f00c06080b4201d17030300407036069140c450203006006001c980d01040803003e00b07010420482070391111006007843da02503e00185040000d004040d40760300f201d4000c5008840c02d100c00200c80c401c0000501c10701c003100c0003180041203c0c02c00240150080c1100854000c54100d659a83e62101400e5038440c1010825003000c03410f00e50025005444140f5002c41684024030322902c0d6640400c6d240481805680e06001021030040784641e42c01c8444006010042c003944c1203541d58820020f01504031250445229003800d0181d11003960300d10a01d10010303041040052418075104c091050405069011020054100000701c4d003071301c0303900030786000c2d0448200c42c0318001c0c41814000d04140b2880c079000b0580d0001542c903008640e000952582100a40350010b0b5900c0c0d0614142c10300c0d104801c10400507007500c01100401940c045442030403c03080c01e00303490007170805541c2036881e0f10846c40a194402800400018150b1280d07002c1c82d07101070464100c91801c02181c0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51395246 1250 51393996 51394027
    0x1101140412111614040f06060201060f050f0906040504031b030824010804030e0301020403050a11120304030b040f0c03050a0c08120901090308030915010312030c0f020d0f05 76
    0x124180c070412080c01481d44000d5019010b00d803846000c0002c0c0464032060000d200412280703100c0c1685a00e4015528601aa582e038171409510360200b004110f82a0b460780040d019002034410060602c0c084440024207060564110491010040845150b41e89100c01c01c0010302000e00260100b001000c003556180b00e41c04001c070320203030007501c61003614648130742160080d400c00d4940d0880303075040d007400300510b98021080c260410f515040080f405c8280101203030081c05590301c00742a0380f00e9098080e040c0b15940003051030341d030f600341d0754075001050000016540b846a0310000303045400100004010510108840307034081c1c1310fa101c0d404c0082da81d40b9040e14021f00100190750b0044005420041d19004100308400c1d603156030215400c20001030000b0380005464880039000d22000400110b1100080c00725502c04152454600c0c5156141c0c18104281240e03840c02c00e020034500645c06030207901403503000c403000c0c215a005245102101e40b0442d81213020446000500c0818000900407c8441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51396496 1250 51395246 51395251
    0x516060b030a0f06180b070c14070f0311010804020a17030f0406050d1a031009150504080c010507020a11130605040e010b0a050a080a03080c0c0d170a050f07110114 72
    0x192400070b200c03030710307402c1820444005c0f091000340b511903200c0e8140003a0b02000110380c03022407030429031012000c6040c00310342d10402c551582d0540c000c452000c501c180c00c40e46954242c0f8020b90114002c540303507900540701014140c801951108440a00b00b003441c18070303158081110354400560342003107080004401117420a070441d00110704003080308010440d882c821011804000d6154030f224281d648042a110000140108174007910349442400740844280060342458903500700700020729103810400203d81040d140f5411950814000c43d00280c400030f0743c0c41e41c041c0c02c400005454401c0c5410400383d40c0b02d038464042c110792a82d40000d5a0b6880d8030a5400c02c1c24580f0000c1103840184080144600054004511419180e03030b050110507400940c0b08030081d03050504422644914003101d0113406450190720f410b10480c4590101c559010340c120038051a0404440510b840d010200001d88400301e61030f800428100e00020300041c403416459640c03401c95800002d10305680c01e241807610108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51397746 1250 51396496 51396503
    0x1b0115030c06110c0f040b010309050d0e0112050105031b03010e250605071101030221010605120a0513110f06030103080304030206010510020714060c0102030403020f0c01030204060516060b030a 85
    0x307010702002610381004140300d01070603c8024150100c00d0800142c00d50000180081c020ba59401411440764007e0744402c0c0c2c0d50360400c00b100c1d22819682001003640034041e10850001b4040c03c101100d484042c02002c0c1079490050140050122445000034a101442ca4855040d901d520084403414021b200c00ba405c03060005a41d0002103070100d075560f00404551100b400c010703040241001003480d01d543c0c02c0d00e10300d00b481d01695a100951013070200e64220400503050503010800064081d4000d40102801c0701ea903c1c054109503122200942281c00480d4481c0c482e01c1c02e146007a0000d0741c1150600350345100100882c41c041410030128802d604244c10403919540d001040c0302c285601001032a0041c0740854151088080116009480c1c100c0c81c41000c501c19100d0600c1c01e1250f4800c42500c1c05240100c000b1503ea15060078001d51f20b010107a54880c29001da0191180300c1c0d403190003100c041d00c185494417850840d4214400348580764131142a10026a00c00c0603201d00d96040c008130140074003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51398996 1250 51397746 51397763
    0x309080a03060f0b0f040e06030c030d03020904050604050103020f0127030c0306060e01050109090906090210020c010e0a0510080903040503120406030606170c03040f12020106080f0102070302031b011503 89
    0x801010607220800343d080b4102c00007041c0100d251403c0820203e0f0161076841c4004241f680b0f5410100e850070356413a06103a414064000c201c144594980d020f050205030841d41848103407254010b02c1f084500a0102139040b4851180803000355024098540081540c01d400c00c0d10b60401007100c1c0c201c0d00484d01304075040e02103580b0400502c00c0030300500c400340603180541c0105526000020308450030314030420280c0798450030240700748415984514100742c0c0286c50b408215503001002900c0d60515654140829501c4400003210f0070503800007026240050f00310340b8000c107a144261003043d001413164090388010071010502d81c40901c0702e00031000440070255240c078108840503080d145907800002c10403014404000d0b007260304203c01604a4030181c03c2c10f659450701d080c098415801024060f10f04010390214214607a415030207501181e824205035540c0e41610403419090b07208491020340168810700010b03080f00c0d01490b061030756504510000458a00c000e9608607042801d51040d0341150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51400246 1250 51398996 51398999
    0x711030f0a06061a04120302010f060e010302130b13090c03020d0605010611010e1b03150f0907120c090b010c050f010605101e050313022d060a14030402010309080a0306 74
    0x4440d00510018049413008a20f4004441407415414012441048001309082111209040c003c0d4440e540c0d4a0121006110a50b245c10040161031000c0c031049004420080c5441440c860317074403c20104130b100070a1540c0e11401500340c0b0010308885e00b81070315040c800c0303c00000141d440c00f400394100ca1060b00b01142540c50400040c02640d07006070044180c2c0d0500540d40354809000c500c02d8a541c1c51181502040380082001c01c0c50186d1000502103035550b10000d020003a18110506403140084804985640c2d0719004880c03c000080c6000400c444001c40b000d2002d040b454005100700c1c0810b00d0700c07140c440090380300c243c80d019030445c1300740300b60355984814400703401c4c0340324120541203060400d10729542204840e103c22212802002d1300300b04000c00464110295081c02003480c0703030001c2c03208034050240c1c80d00d41c8500da551b009003042c0c0500a01c0d80c80c001e05101050322201205910382c9038032080c0c0254a0601c503803000f44100d04050741c41e84000006006132016000f80302c0943d40009019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51401496 1250 51400246 51400253
    0x9270604030f0906020a020405040602090d050a020a05010c03090902030604180f03020c10120c050c010c0302040503061807170313090c0807030203150123030f040606090519020711030f0a 82
    0x914403104001000291035044c05929000202c9210075503044d600043d643d680c0c2e00b0000000d0203039031310781a40400c1100c21182807020000e0180302c024021200d00160383d41c0d03400195515480382c0310003408180d012008100707055059019617800303800600003060703c45030660a14001211880300300c0342c0c044200c102c08103169040240d10580d56003920b5000c014540120003402040c0d0084103030010075201c01c3c0600e00c0920500c00d880505191720000e200d001d2100034090040c0d0414043d450081c0f189800140ca03c0b6041c28031a452864540c1c05005080d003005107555012090400c04201031004100b151810043c0031643d0b801070100d803c1c0000d8050140400402c811000341580041600610505c410795071040301843c1000c1090900001c1c0700c3c046454100308003845094951203502c04010005805215400e00c0c1c4641e1046004101c01500c8a50520454800b07551140c401e820325510700300d88403200c0d4001d01e419401000c00316a0614550006442c00c201c103d40031a607034002c45084000c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51402746 1250 51401496 51401507
    0x504080d05030106080a020d111605010f090f02100e0a0f06080601030b03101d03490209010c0b040503040501021504111011010c0203130605031003020927060403 71
    0x2015801e180007407442d4503103900140b0a14000e00b58201d4940c3c0021401b06111042d40a218510b049a0215841d41c901c200366880480c01100183c41d00d50070002d1903c0900c9003407064103041c1c0d80c01034071800d14100ea9000e000d40442c80800f42018402c0800ca80040c50b52282c03003850040c818003442404007814a0801080c000300901020705042c1400c0c10980303950342c013040c4807000c29910640000c003c186881845207440c02452410464040003c46e5200c0300c41c100444822518002d21410f010741007003c895100c1040403c0e001600d07c84041754100400680d001010100700501d4494060000c40d2521a540c5000383c5c0c0c00c9074281d0001034100704552701848490b00300804000050094a055292540814010340400d442184030341d901e02102070013039881c487c186030088000c000520604001030740d0795020b502145910440070703e000aa40348514100c034810f2141e9520108000d19541c280883c07020082d041100c1540c80c920f5400c0d0162070b12048200745400c020003800305007403d0401800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51403996 1250 51402746 51402763
    0x906081f05040b04060b060d140103140312011a090402210c0403050309041d0601030b1509040503091002210d110306010503070c110916022e09050a05010903050408 72
    0x248a00307100c00c20001c25410b102081e809500240041298442840000c089120b0410b484044c68680302034204400208102c02d41660710400740311a0b488815210b40b0340d00d0060032041c030019a15100184200c8528100354419010740c120340728100351548000405036040312640d02d071001c25540304541c1e8a030042c0b040c584c000c0d0310003a001345482e05585449403280706115001c2d000350340751850340544010054604500000c40416070f0003558582c9003480c1c1c2404259011401c0404003102c2d440c04d450100d44043c041e40d4040011860440290b041c4601403140f410011309500803a00c14852908002c0355500004140b1055280c3d104070344001072089900120309a5422041030040010590f080800c0365002102800d000c00c03289114a0130141d4500c00001280d08a03250000b48007141514260b00e9180c1602502900d003600b000202c02c4a07610120510010700e085084100e64041d849a0301034201d0074024800d46407103141545605080d204810012000140005420001c0c14414807800b40e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51405246 1250 51403996 51404053
    0x82101050a06050f1c0516020c100504060e03120c0d14040501140d0905030a03021b010c020705010e0102030c070b040f0b030f0a0f0b0a060807090f030206041e090608 73
    0x107810608051004003d40164811200c08031000240d511080d048940b034104c41a00c2000140000e150a1400c824900075000000c00907100344481c00328240b601d03101c503800b900001d03500e940c1001d21b400c40c02c0324204c00b541c00c415010b00411071001040d07180500101003903228400103000060130104018640c647d2001c074096605028001400180e1f40901c1403141d0322070f00300030b4540b51600500b84000501ca2540c0081151100144114141e0b07003503009000348485464208101c2d0018420140c02e982d080c40c5d04800503040035800303101c1c640c000d11070500070b008180b0450f410000d100c004180b41c91001e030005821002d022900300816180c82c080c1001034188009110300f14100210160080f010203013100010035195001c03110050644d9100e805103500003013000e0500345d03485070058a80c51040d10341c200080c5483c8404600300090800040c00c9a41c0a07089510341840e1800c0d030341008508603c0d5400000036543d00160111460060202801c8910043c101940084181402d00c001241505 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51406496 1250 51405246 51405259
    0x9080a0e09240604080706020706090501030b21010209060d1425080403050c0d090f080109032102040e010e06041b0c020f0105130603020403020a081903030e0a08210105 74
    0xc400c00500d0007403400b144000065000c003648100040c0c0500a83e008504548284800000c440745d00107200741c00c591072070719000801c5856a004406482100541c40c0c0c100e802a150110030410203411300883e41100b800050034042c0300c0c0c001940b01c0d0300c08003180c2e5403a616688205554103210681036003100e454491110701d40c440c5003944541761450f41560f02030006860001c3c00f414010800c4803940300300780f407c1d50300420076403002a2002c8294080d25885856804000c0380c02d250521401e2400740d01900d40d8602001c800710a0001d015460405142c0d49409110005101c00c112404034007030300c41c4403c0c150031807800c001804121592103580003c11854056031000c0c0903000b802804031a50107a455a0390a442900140c0302481020001a20320701c584000040c2e141c0e00d40c2c00340c81564400c81d144901d640d41d96944d241d540b090007403809012411028031500113030081d0b1088074a040c202c800e03284e1a1445881710882900200c40d008000e0820502d1076a00300c6040200d00e01600c0b00b110403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51407746 1250 51406496 51406501
    0xd0c0902070c0807080303042a030206040803030f15010507061a0907110c0904020108010e04030207031e1106030c09010c0c03080304150f0608060a0207060e010e01140a0204030201080609071209080a0e09 89
    0x342109c41c1184000c4104c2240c4c0820390007134810b0050144000f450700a44210b907a21b549030001941da50080714240a029050310105050300c1c0420820b884011050390356606000d410f40710000106505c00400301d0711090003492001541720304003a1407103600c0c20386505010003505014941407000d0568080e220b01c4120b4104001030b030300600c03e14152000e820001050f03079100e10f000e91404800780c202074000301d95500c0c80c1608808244c00c0c03015903803103000c80f42004c400c0c040034802180010341c0c5c1410100400d11640c40d05501c07800c10070034083c2c09100c040040e0760752600e80404951003524240c40f00c0d541c0400d00140803625024030128001c02480402002c1e01d044115525080040c1940c0c800704d400080e40020312403281c02c2440c82810380d500030004010480000350081203086e20704650300b85044002101d00c0e11920035242183c0d010b03120807000f966035108101711000014501c0e001d024001d010034240340c80510074940079901c0b0b90301c203a81d07909404802810818480306418880c0009004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51408996 1250 51407746 51407753
    0x190b03010303080408090d0b15010203190810030c09020403021e01020a0b0903092215060909021e12040b010807050d02060304050c06030a02070605010e010605090d0c0902070c080708030304 83
    0x4503411a601464400c2003900c0d145003800c0c8a2080c080000e6118040074019014800482e80c1a80074000b44001c0000c405076290059032a8011b003114030a5000081d41c10000343c0d4002c40d040d40e031140c10f00354503100d5540c0b0380e0365660a000c059003011651075408641442181403000d5056031a40c00d02c80c044161195001c0004c0d83c1d01c480c01002070103c4d00d803601003011907074200103135004000018510018100f14007041c00041c0003001780281030b40c0c1085c0350f03800d011101c40c5481c0162480c1d59100f903002070800562101a40c402d40c0308194445180b003c1e1080e50004901400e41c3c00b900c2c0d42a2150fa003000d0421440c0e811040c0c1182e819034004100421840c1d4a40e01b10600c4154150b5040b80c07250b40b1400c11500708400302807220f07009100001003080030f00c0c1981c000c11129221f000c1c03c2103241d8903580c0b4410013500900402003ca50708128041580c1717420b5904040e558447c95032110020740f1280440283e0300b0610046800000f504014803858801740540c00290424000550861400b6103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51410246 1250 51408996 51409019
    0x50d05070c05250801020a050c0d051e0702031e0d090b090102071707050d050d031808030a0207060b031002040801060905040c17010b030a0b0901180512160f0302060619 74
    0x10b070303d030750316002c50b00280c545004504660f001043d58000841d00c5002520019109610002d9494401d0081c009150f036000e014200341d400141c5542000c0d4400400400300310200da00c0080d060703a06114015960320304010340c140c84803006822001504001c1403a45014091100c42d03001024980c005200c40c8446981c00078407170b0100d421b0106c62070080610a0b007440d04203c042d80201d0340103002e004588081c0500080c00044211255a040022458114104241c1180403500401e00c40381000030031101c0d14950040c04185018a40c009850382179840021b2502002c1c1207101c0b022900132a0402607040c007841078000918400300180000d10707044e61030180e110030750700680c4c080c084485c201d022035060035800104500d0b0082c0842d82003002505040b2011581102c165066608016040b4001441110380b0520142c1c890018004c00c2800c00c144606038102030305c01180342c0030340340c0340002080f180018502d100340250050311180c1412030601507408071310603142c0c20303510754078808200c4440790f0f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51411496 1250 51410246 51410263
    0xc01030c05220302060403060506150f0304020d1406012d0b07060c05070c030c05130b0f010f021516081305030d020703090b031005040506031603170c0d050d05070c05 73
    0x40c2c0000e201d00708410407600c4440396000650080000704000c400c02410340d1141d802000304480310f40c185c00492107050002d12685240303200042d402d2000c2001070401e180c510854501c20620341c080110305441291500304240d001298411850b070103d0f110000071103400a0b00500c44007084201f0f801d00300001c0c2284521000101b105669580c40c07848284560190b80d01541d20200d00c0940719075038105038405071254041d0300e2040480006140c4001054410182e0f0340f0dd02404120316130300c5100056604005200071103095000d1154480319210445680c070744508d01c440c1e20172000c1008040d00a0100310001c201082d01ca10382c602c10408141c0010580710f03080150200981c3d10300403840d048401c0784203a4001d4100c940040107103c0100700115000c0180c4005130f508104e95960a0201603a0722901260889140025074084c0007040d80c10f9540214070440c00d41140c40c240c1c0381048103241105c0e0b050b4402c00510f01003000c03001c040450084030f8011455140c0b50102c0d8040d5280c0689502c002d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51412746 1250 51411496 51411517
    0x605070e0a1214030c1002070201180302010f0c02130c0309060507020604261201090c0e0303030c0f030a140906010f08150708060a0314010209010206060d120f020a0f0c05030c01030c05 81
    0x101450a03460b100130011140c440c0410020ba50000c109a900c01c0e0103074002401c200e000c40c00b0300c0d0b985400350141501c08008c0701d4050b500d40c041aa10500c095a92441e9420241c0e048190343c08007820441c04c2d0300843c411042e056400244114150425000b1500058000011500150240404541700110f0104401ea040b00075414862540c00d1302d02041c03149280c06003281c200c020002440341020f40c09403900561a448202410100100f016100e11045a070392224181c1072041c20307640b1700e00c600951b5009046131400a05403505601b008a030300011100362034154030200c01400080707030b0118201d0003460b841006143d800d6040b140010854402015a02005018070014006a48020300c42008540201000c11500c8041da20ba5000c0d502101e6454090312075440442c03118100301300040462500b007801c1e00d2180600c104102d0301344085074950030440c0301d20b0245101003400311080d80075561094003e000114540014141001c4280d113509050518200300650165045022900728016 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51413996 1250 51412746 51412763
    0x40f0303051c0c11010509010507020d031505031002040512060c0313030309020a080708160513090f0b010e0402150a080f060604030501090b0a0501080706120f020d05040605070e0a12 80
    0x202c021490022035041918403060b0f041540d5405850b0300160000c0703e2a0081c03000f44400d03136600c01510300341c40c0d0542e0500010fa00281d05c0000c11446136000d00c0c118442c81e41c19003040c0740e8650003c1d00c4d10301c5040361500e44903400902005240303401c00b00c943c5100d517403102420982c6801d120a000f1800010446c802060000103c1e00805100b40d105c07070031940d801010150042d07183c103c1c00341c2c0c81c011806100e242e486550b0801ca6921213021811040f01c000400b800003095079050450098083d032401180c2011513070f40300500103890300e844203000c0c03c2c601351288050b01d0140104081d042e0110500c218080e01048900d021a03804100580e0111950500c05070544400c8003056540c070659201516a500c0c1c684144100100c00c2c2c0c07801c0c010102d1023800c0c40b541e41c0301d004042d2600510f100c2c0001045010017906032200d80c07074100c84003030b403e0342c100141882c204049440c01c0e501c0440d070845009698004010812f0380200e1038600d00a07041d218403c5440c28609481c0344e41718450405070030b912 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51415246 1250 51413996 51414007
    0x222051f08150f0303030403020f0705120316080f030721060506030f100b07050609150903070b0615220905060a09020c010902030102040611060a14060f0f0418021203040f030305 78
    0x80f140c401c1c01c10350381ca001e01225036038a02410000e44800841c00d10b0300242c000e60400050901e0105481d03282001c60b20040c40c030b0b2607140790011480303d8400300102e407802d806110300e82c160007030312028502c1009240c803030303001005900c40c0b401c02240d10188040c0c005403a01000b03103c203072904020b07258070541c05082041180c4603144d07080c003000132583c0080c0418034005142c40c01c00500ac10154016030450301120010400748814103811501190328a060790300c20312000340815030700039125400210282080c2c445100303800005407154000b018002c00c040c40300c000316042e4083c1c0c0c031007000180030410342080207040003c0007412002452060b043c440c6d8001c034600090880a42c45400f11950040c000c660311907440340060500144195059100d00030180060100c0010f8045d800841c000f884082200345e1341c110421000e0311210740500d4000c42c0c6801741c0410358072203108810301c0189045040c1c070080414810412845115a606002c6070020700080112221140006007030741d5260800a4840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51416496 1250 51415246 51415249
    0x909051006060903230606010c03030e03040f080c090c041707170f060708070804030305091014150103060f030f02060d0f020301030b07020a050a02060a030222051f0815 74
    0x103200841840c04462404800084854000c0304030011648a05000070a490f0444805045081014000c80c004c1c0c103e2000a01c0c1c661103090155491031207418009400b18214201d14956005034001c54600c0d54076900c00c1c0220041001580c1d12401c04071100c2c0410b10b0028040350880c0100d00c103d606c1c1c504880e030300740d003100c20500118019102005003205501c4101c0f02c51a540d034010480074900d0701888001c2400e0901c0761103098410181d94035405030360f40322a5411401030400501780c0d035848c016441c829941d0840c80c084c41242600c01642c8010340e040c1003440f450040b00da03903255418945008401c015400c4203840032011290484090b01c40c850580c004140c9503c1020f101040485c40c2c0800400c841d05aa805541680d0042d141800300341d40d0b411060381c6e105403001c4007030210352103200703800c0052600318000c0110180a103005410410b01407940e040c481e2882003110408075105005118600704003110080300c100710701440a00112a01002e41064000b1300b100381d0350f141900c42040c09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51417746 1250 51416496 51416503
    0x50c120a050c1203040b070602040f150c110105090402030a050a0e0a021806060f12040302060a020c0319020f0d0c053007030c0209070c0c091e090606050a030804030b09030310090905 80
    0x200f10030421071f503442181c0d14080000790f1146c090030610315084100804c41014410b03004461065948500c202d452494403001c00050115405d1030412504000003015a01c0c0d0f800514003481c5004804119800c042072000c00713603082c04103141c2e070550115040c1741c05a9643c0b20540c01905460340d80b011591160f03000b0034424401c0e6000d810303440d03000094590f030084401040d2840303a800380d401c0d01c40503103400301040241c0c4a204144076903a4011700c1101860007440c10400002a241d004850b2201141c0c106a400c010034510542c0200306000700c08001e204003485259030310b00c0d50000c40c200c140f00880c491403010303040c04000f248460010030700c01c0c20175002c1e003c231050341e80d0020503c503513a20384004d00410310344410404544914040000107003909190140010b4a10b1000e12000001a0425103e0041c03070022030540703101d034440c040000c098a40603803180c00755006440059880f405d50402c590104806030403c00d95034800c004000403c0010700c890000d6a52810000c00c00d01000d0412524 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51418996 1250 51417746 51417749
    0x120605092406190806090f0601060e0603070c15020c07090c020a0f03050c060f0a1d1b011806031d031201050d0f060606030203060102010605030a050303070c080c0604050c120a050c120304 82
    0x78454034400042031413072001a51a200d5100c0800301c0344641d003d428501e444000a114000205801075022070880c81c3c0140a55072000b180e280c52030051500f42c0720005004000c60100c664641d00240c51034005030300b0301002c001703015000c20038003196041010095491484001c05084100e40e00d21100403d131080048034510310000044880d0760409518181c0c030454182d4082801c60300c2c0140a056400118024070600c0f0301b044081d01c00e074050360b5144a059003400c5012410808a032407401c0a00000c2000300700600784c44d64000880f041c1031200c040001c0305a001c0310f10b00368414840c59481e14282d0380018155001510010342140551900d504441c0f4840c03401040182801000314031940e00d9800346210f200240d00031b00500d644c41c41896180c4101d0700b4040e095400400c005455140030b022001c8400d407052201e0340c075000284c044641442d00986084034290171196000c419458141e1210f1003c0b4000c001400c40c031500d07942c1c2c035552036640707403940d502803908801101d030116014010f070390 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51420246 1250 51418996 51419029
    0x6060304031407110a0608060a0605091504080304030605130f03030b040f0203090a0302061006170402010509100302090f040c050a03050c090a1d0906060303030c180a120605092406 79
    0x107480c0c00c0d83d864161107003001200394500a40600e400028254881c003800780c01039501400011245051090441d00d950216101c6600000854008402503004034020300041c40000d028603103442c1546001c00c00e64401400704c03070340c103415210a1000300f0081034800a14681c035042c005500c44051000c02c01900300d00e04881131480c80401000f02481d4049684034040e44a07600b500ea640d41c421a039000d000c29580900d00c00101388c40262003048202000458109005040407418203414100040b00a100356651000003a004aa0320300e040c00c10518a0030b032860110b40521110040fa072005001d030181c50190402c0544400c0814021003891080340c401550280c4030903852034a40340007140003640101d1900310300241078006110101e02080640c000e00008002d14a5501c9074244030600743c110007000700c07044401802d400e1b02aa550842d0800400000f68005000b5419041510844400400c9440c3c19001000b166801d1040400c031814502c040180000c169128080402c1d8500150030888 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51421496 1250 51420246 51420287
    0xf0c02040603050a02010906051801081003050a0c0f06020a020603060d0f060509010207150207021c05070902030a0e1605090c0c010e0102040b09130b03060103030804050f07030c061202030c030606030403 89
    0x40b00f40704010901e507003058000c0e21005400b07541c0d410102c986204d00d0141c0707801540500c00c400300940c8140d800a402c00015400e051030661280c865074140a2030107812580d0081c418020400340700c00c42d400d80010f102e1800038040c080d03a2900401c400f0300c002004940b01d43c003000701c05d01c02c2007001212403400e107800080800c810f00e0001c85085c000c0d808030320195a44134983c400301034030b10054000c8030b0400347e02800c20740302e5641c0400e20032a003112003102160a40601c081c0495011940d00c040e510031019210081030300407002001e0750525003443c10404028681d140140615102d40e1075a5070010070074070070f140e42e4030542210b06006000290042c44a5400010700140c400132540c0500300700c001c110f9808800260141c40700003151000422150190080001000804d00516900380d00a02440540b840b544d000c040311804c103c9107400840b1032a031ba22a05020180d81b042d04515140c02540c011451342c2000140740c01e82e03000041c040343c0300b0800000000d04052188a20890055091401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51422746 1250 51421496 51421499
    0x304140a0f06020a090b090f06031e0405150601030c0806060f0403060906051b03090c040f0e010507231213030c05030a08090105160e10030b030a08130501020109020307060f0c020406 80
    0xb0302a40c060b6204400103541c0d00c20200e24280900202c0c0c1c0d483d0b078010807003c00314030201c0c14448107070401004001b40000c0e48500c5500b18890120162045101d0340141210003290408020306400c060312042c105490459030f120f5260300090000e03001402281c0c40f640b1050003040440483c400c80e0401005241800d4008003082407035040720740195440e88000b5a0030581584414450008442040f0030358007508548030141400c0d0f11014074580c2288010407000303502207a03c0d003511801e039591000181d401c840c611240000180112140810445481c0350500490200100b010058564400100307000c00020405000d1740e040c9404c503a1003000d40741c4440d5184005400703400308580304045542880001400c900c21030503050b013194050340b106800c3d88000c01c1800190a25808004141540c03013004031045c0c0e4081040b0782a4a2180d004a581d88962040c810540c049540c0800c0c1968109944a00180e50105070340d41650220b1030003116144064808650020710420701030b4209192240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51423996 1250 51422746 51422753
    0x2a030304061106010503010e0a110414040809030f06010815060307090c0915020316060209030109140c0102010b090c070206130f0b18150919050411210603030304140a0f 74
    0x1d0b54a901e070300d6801618a80d81e0b80f00245401d07140b15001c60b00a81e0440d854400001f0028040c040031410007420004001240101500d05008240c0c0e040d00c0030180070075941c031240b4040003c03071040c083c4000503005039407420034a50755628168061140e160913610000d0000d80b410004c0740700501e00700f0000c0c000c00200600103088081035008022107a170900400ba442c00340004200c40154a180380c0000215456403074080087d0008801240c0c59500d411001e07001c40e00142480c00b0703013805100a070600380c8042e4006400c42e0382d07206ca141d002d05044010080300018400a4450407074058400903079a20030014100b00010f0305801140c1001840200481c005a140340a000a200d0f407000e0b00f42448015000c000d03c02100c14460400c01a00f04041d083e03505043ca01d8401d5101c0c01148104001d480d80d000070143c5110380030f0704035241000300300c41e0031107011040c2c05074030380200c3c0014100600b80000803035245c1c800144040c15202c1c0e102484240d4010801c08607207a01c0e0429100c51024030a4034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51425246 1250 51423996 51424007
    0x30a0f020111150106140705060f1008010504020607030f02030408010e03040513050f010303110a0209130b13050604300305070e040204080307120e0a090605090f092a03030406 77
    0x5a000920038a00c0e50742c01c24001441e00101d098411101d14180e2816400701c9072412491102200303034400703100c9a4001241004010f010340380e44204c0361440d2a1040302402180b0855001402c00d80c1004180005078a82d8400ca914094151174000902205a641a441d62181da03012042a41c60328455500034000403001d40700707460044a03801020b80e10726941d5400d031601910f80200c0c2e001d00c88010030002380240c1a0319441003021090719820013003a00055100c0e4400c80b40c4c80b00203c00c402940f070400040b000f403964000a0070251040341d00040e180e41d030755003000510040903c01c840d144003a84107141d000310310030070080360120500214204001005490161904004038141d6070182e000e80c038060082d1400c1d0342008000314142403480d00c2d94905144101844c00501614402c0c40140d034540b151441e01602880d5004070f80c1a1400c3d00388015440010703c1198407025a0060000003400810005d289031820484c00d140c21240e0b50b060030340c545203050420313498400003500094054000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51426496 1250 51425246 51425273
    0xa0b041106070308150a15030b04060f0e010306050a02070803040f02030d0206070f1d03071d0a0b090a0b030c06030703060501080f0f010b031f060c06050711100207060b030a 76
    0x2120500d818000ca03809000203409030400c020081856000011003003d01d0341d040310340f50035000b40311030341a5030750f01c806850710050600303001c00003904c0b04001e02d1036007014068a8020020740c1d81c1000f54601c0d24000d4200000180401442c2a131100041820320207950161503103d500180c038540d807030405181c65440c8a804001c104d0082c010550f10012160000c10664403500c032540320303e83c0b4006c0c0c00d107080310b8803615601d00109041e1001c1c002d541d203031003c114450142074640c90845402d003548100020780030b401031040205604019803107444d511100c1c401500048013440100b081c0c48802c000900303b08046051942040d4040104000c0c640d150b000601221000c1e2100641a2694201e118800f4000ca030034050721444000104004000500119400707003020540d5540d107142c000c41b400448509922440000e003411411a041c00340c0c610540e904015982492403002628885281e21406844c1d40103040c0303903022459605011241d0007402441034010306490a580741860101082c11a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51427746 1250 51426496 51426503
    0x8030a050f0d06150809070806011403030c0703050703020a081209040f020c0d0e1003060803090111070b0705030711031c080601030b0d05060901060e0c0306090709090f060e0604060e0a110403050a0b04 88
    0x182d2002c1b400c600d4001c9080019070745100003402840e800d00c40c00c0d0070220a80710249070944404c00c0300d480c440b04140040f00103144901e02030000a855401000340c1d00704140c00201e4550404a01003404100c210200c8030124015540410340141e040c100200a001c1c0c2c019070b1025010790b00e030041070540c1c094840124020100c0740c43d559108400c00c201d08030303520382c010041e00390b204003c9803105600807400404031041307841c203d410b20ba803144010005500603040844840d800403035004104850041c894088010a40003000342d82d85d0f0445040c0d10b90120f407010f90500100724086881070344260403620f140078018080c0e0300c61061a243c42a59504200d441c002c055203405400316030103091709102800b500c540300d0368130706503192542081400034000c7c115105104164030009100030340c1c1d00850b01031903048040015004e2410380540741d8540003c18444c440c1b0b01d044c1040c0300090b0104c039034039002101c8107030000d604100390255601501c901d40000c0c003035208200d0140c0c01c014011000620440c0b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51428996 1250 51427746 51427757
    0x30306171e010b1810080a03020c010909090519061803090806151305070e040908030604050105060307050a18081204080c0103090c03060b01030b060a090e0105090108030a050f0d0615 80
    0xd041d06440d08841036a61030603449001410300300b0860542d01d480c55000394104c050032000301daa9a1281740b0b0070000c00c40c21400341c2c00c080f01281c01507801c01348490007002d08050901c92070200756145500d43c203250707018010000741c007480c3d681401001d0f8440803110300c6d42d40c1d641600209a04000c0c1041e102c0d4850600c042c4170f01c00000d800e8821101400b40e09410140c0448421440800000c015244c0106444104003095007000100e584a000704a4180e000b5480c040d900d0600034140800d81d10160001350143c0d50170828441034642c04002c507558440c0740c1c600002032280d600711001e04a4800c0c1d00c40401c52040700c0f2150102003801c0b0051048a03000780840300b80b0350130b01d030040d800d8540700c14001c0e10482c0100002c0020400d035401c40401250149000689003401100107402c58010841240c0002c40c3e1000910441041010040c090700c0c0071200425558908824950340740b01d0303100c46000b040004904444070500d110140c0340c1c614202c20003802410384484600c1d050200d03000c0128005603 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51430246 1250 51428996 51429043
    0x70f06090e0c0c06061e040c0305150a03030206070507050c090c130f050a06030c051c0507020c0103050f010302040b0604091a040c05090a05091009020408010f0c02030a170403030617 80
    0x224a101100c3c40000350201a00c01503803110100070038002d0358142107841026620450095a0b6184100e40d0b40034a652000201030804141e5250030885010b00503024007019001030010980000d05540c0c041c01500d4075550702e10b114541305051170428080ca0350403100d2403040c00f01da4802100501600c216212480c80e40b02d40e100814000c80d1158030809401465048060150303078480d030040704080c02e0606200b4504800107440c4055840c1c00d015424005603100203100340306a06000062280000740303070030701003802d01c1c0d0f4030100b10303807818800248103564400703825041c0d40710381064500070815900704008180c46e8000198013042d0002029128618040744001c0d181d000d0001c0d071f110500c002c0c080d404c1141c00c10040c00301c2c04402038505690401c3c0d4035000610000703d80018005400006d00210f0591030309204002a18545030030a4103540092181d0038074140c1c8940c88080704101c040460b502d9490f641002d8004004581000d00303001407414100300b030050700240524154085005080105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51431496 1250 51430246 51430261
    0x70c112115060312040306110405030307110111070b04120c030803040b1005150a03051801090c03050705010305010503030d020307032c0d050a02120306061306090611150103020402070302070f06090e 87
    0x31513000d41c90340340580052209201060150344400031a02201e40300f01e02d456110800a451a0000d140844411104010400c400d507800713001d6661840b0900020100141060040c07035046c01540103070883d13009519a20070034440c121122000564000000c29030342d040c40d080440501d14210358803000400c4d202030005560509009001c5031188864502c1d00308816501c08030051300d8081c14a0300101404a1180038246003072080b0403902e4402d10981c0e20340b03461480c0450400109a20050502d8541001008039480c0442110000b0703810000040e41e03555140403d80040011000010340c285113001c20b0100f41c012043d03c400e072240d28100302e9500000c252011106803040424400050304810180904049054040d54002400034070090030854111092001564281d02010004400400421916070080301c12070f8804803440151107820200b02580480c00018032000b80603540c0080c00c01c09162080c0301040180c654200c10410440d40c402004002c0c2155004080803c3e5400f000720fa0380c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51432746 1250 51431496 51431503
    0x1603020c030f2d091005030405070803041806050402130510030906140406180213090f0206070b180a051203070c050609240f04020d0203150123030303070c1121150603 73
    0x4d41c44000c2040b203c0340b041900c2103580f50800307001110b0302d21401201082c40c2c0c034144041e02c090001c40c2e26402400305000800c105a495507804a401544100b02c590703880138906141405443c42580d4150300c0c410000012402410240030150070b483c40c3c03540d20304941c1202c0c1c0d00a40a18041d00040c040c0340400103141e4992038501500030341c07000d003a01f11000c07103040e25003003114904d010718540350061406402141da55481140111900c81d0000104400b41d80c451000f40d003100080f03402002c10280503502c00c0c1e51165202c1d5802700f4504080001a045071040c0c034800407403540300c0290b555070700300140e01070f544204900b200c5010110084038440e50503c034500c07443c4111541c200c4000c0c2a01d903034083c400b600000400c1a40c06000303002c00107015100c0c2c0e5551034001d000a000c980300882d411280d042c5c00740c0001007114400e030820010b0080b20b56000364860b09035504403040480303401c440700010380c414103100c011501c559203d90310b00a02c02e60205405841c8811204500484e6a0302e6041644 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51433996 1250 51432746 51432757
    0x27080405011d0922020d0506070305090601060504090213050319060506041a041a06030709050316080c010305070221031f060f1101060e090c03010f051603020c030f2d 73
    0x801543c00000112095400d0149034031410019501020b0840c42d0f40220743c05000a180c252032a43c0150284262036515106582d4004a801d01414a5506180d0010310070b03c01c0d44545190150003040040030141002091002050028200c0303641882c519000a00d03058006015a0710901d040005000c0b401c00340100e0700960f03070341084691101d51042c100402092207100f2403058000d0501c6107040d40e00d41800860050240c0d498280c070284c548800c0501d0541d21800c3c03114401d420382c504024800000840b0219076400b420046003071782e40c0e207030100e04e0240c1141e007100351442d003009a03007511804d80d0010741c00354044038807044090650507002464000345100300b400041c5184080007115100c0c1e001050040c070f440001040d019951041c009181e04140c50200f03a58000540c50802441d09100b1101300c14032000c13042c002840e00c02910300300201c0440c0040280740d00005c02d07a40f2084240121a401c00d81c0611303098a076524808220038040424644008008408035603c1c03604600700242d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51435246 1250 51433996 51433999
    0x7020706020a0b0405010609050f0109050106020a0f060b1810050112060b0301060c0f0f110108060904020f013506120102073c080c010c0e0307050427080405011d 71
    0x488098a5840b00f030b103030b50010010b541d40c2d541da10340440c0048443c0600b03401000d8404880a0a5041a031703000200c41c01070b8010400d640c406065000060700040152100319000080000d0004607080858024801655000300c194000010016076020084600042d908207981d81c3d420414426001c008880d854040d05042050520040000a206800003e030036441101c16000c40489940c1d45d0008685001045807841c4402181000715680034060581c0324008660120103402d1a8001c0762168090341130380750400c10f070048940c015886400c0040c5421020200b0000c02c071380910700d11161410280c44242c4074480101c20014401814000ea0318840d410a100c080b03025070f01d60300c02d1440c50341020341a5100015003051104900c110b17024442d024024029540d5482c6011203803400c6a8039800c4940601c100200c00c8940348e01c0004409054403429100000c81d030f410b0b1414008521414481c3c196680140d004440030003060f9000703001129000c1c0c0320340d020340006a20384550003074240c1b00c09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51436496 1250 51435246 51435253
    0x5130b070206071e0807081c05060a0e0a14180f1501050607110303031302040f0c0519050909010b07050616052d041e06030c050f0c070506210702070602 67
    0x1070b800f24404e41081c45a402148031035500641c20b913550b01c030031034100d50401d035801c0e140854a00d007051108009641812010031003040706103881c03c002010f980d000c2c02041010b1040c0800290202421307030080002c0143c2200c401e1861a11a08a220f00081040174580900480002d840c016800040c5540414007659141c009a801c10050000f203401c6800701791507000c9140c1004020f91401d100031030048800400700031800440d4014002510000e0105e05041c43c54414203c034090b900c00240e03001030110b0504242510001a030440c0e00703014800180e0b070301210300d1000007201c5000340014035046216038162081e507981c00c1030b50390f08070011841000120340308008800b0100342d00d031b8510800d06001040c0407c4d1901d0f50280e00b80f1500305800140301d120444441c0b0001203501c2d01c5010051495103428070009103410310050240c0200740c192131140c0004600002c05400c2440f06c20041c000251410342c480d000555920820484440201e04c050500e03808241041d00c00b103a85010b03540b054008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51437746 1250 51436496 51436507
    0x1d060706020d2d1109090412021b0a05010806061326240403110610061202090f01050f09040c03020304021c02010e01140d050103050703021906090b030a0f050705130b070206 76
    0x1a0006805210081d00d00c0c40c90070450817850f40d413500c01517070040c0e000c2e0040f000010820030010b803610f51a14203025056442021542c0c1030355480d10000140c2d50f00386001c0100e0303147d22011590501a181e40e42c1d140c4005440e002c80c1002c0084860f158040c17210040e03412000902802c980c0310208001d218954110070040c0c960005440c09070182c2040c801e1818400e00702c0c0d5596410301344182940ca04001c095980c078100011540302da456060000d00d013004501c2c082542000894506031441d505050040111307800031480160400c0e40e21514000d001813148a400e024014000c0d0b01c03c6a08034403612500c002c1c680c50300c4c0340d810b40c400c0e00c69041c1c69082d6440c00744001562007002000030552140010446202001018040d0750b00951040d0014001d40b0706600c10811580c2a440200d45040e07008402003104c207a00c6035545040754100c40b40c8544e2601e49610600c0a8195840c40481e4281080280302e8200c0d8000020815903003240500012251110026202480f5656000e540004288070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51438852 1106 51437746 51437831
    0x1050a06080d050f030a09030207030f0602040905180606011209060e030909160203040b09010e1008150d03080a0b0102010605100804030201050a020304020d031d060706020d 76
    0x10f010707081c000300355030740040750200030490301c0116110291182414001d100c6980515044017403400300c0c1c0c40600f0010040c0d8814414002210702c0c0c10002081060b400328282c10a12400e001b8202c1916010011285407412440340b2298545e907441d880001011441000c03806955280615101c550001c104000030400030130011600d00800104000541d01004032401d0700e1041190b141c4070700a9200403104410050042500b26209403000007480d500070003028840c480082c0c0c1e5040022a0000b40300030620b07682c00060114840902064039a41103800c4011410418400056115502ca00198100c600340e1031140104800c071050005050b4280500340d4002a40b41055240d810198007140742000e000038003408000044c1c200c605210a08a040492490014440c40d103035215810420004d520060175210b00c41c0c80e24040020b54050600800d1003620420420070310404000f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 51258996 51438852 := by
  have h0 := BRFrame.cov_init 51258996
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51258996 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51258996 ≤ n) (h2 : n < 51438852) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
