-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2680
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:25:19.604813+00:00
-- url     : https://prove2.me/submissions/17473c50-5d81-4dfb-bac6-5982a31f627b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 481834532 ≤ n < 482014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 481835782 1250 481834532 481834541
    0x40b2502030306100309112407051f0903080103080c070b0d05040515010605030f10050603090a0302190c0b0711150406021b010c1203020d0e0a1704080709020c011d01 73
    0x70700894140300213291440301282541c01c6100040d00c0e64008602ea00701c90f01c2c0001410004402005041c41415940302d00314040d03400009042e01e2581010340b00451a1300070304c07440780001c1c2c461041086030b00c000d6113000300188014007000f04042000202c500004008002c564001c0c20840c2010703a94448003102080600400d031411555032040c1c0440260728014030620300e06032822036850a0844d500c030303222540c02090141040012600f59200030440b0b071202c800a41c41120008014020071250340f0f8002d1600c0c0e122000c0d084038000624582002800c404420000c8500c41c90b00e454031025a401c02d80d4142403035402155000204607090b0483e608060081c00c2111a81d40030b8640304404503000d841045041c4894a000170320072542140041c81501c06a242262a441c0060400381201084012a49512039150040d03000d40d00150401c180c64850560f5501404510750905152100c40c9944100600031a0403c58005c038460740d01c1c1d1401d40c00941c03200d101d141740d42c03407070440d01a2290080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 481837032 1250 481835782 481835791
    0x5010815100e12070e010f0312080c160b1506040620010b040e0d0210020a05030612100f060305211b0a0209040609120306050a0504020a0c0f0b1914040b25020303 71
    0x445d420b100000d691804842c10104036500080280040351888a0842c1e24190042c42050040800d003e0419241c9004404000d0301d40310704100804d078200b030b0f41c1d0710401c01800b4500c00e00c55a070410090003a1072b40594105000c0c0000041060380c1c0b001a9010350140c403241044681052811005041c0c7c06400180340100180700e40070b54810105a001400c160312420f444400821020408203005003818144001402a4007050b1480d080c00c121040b426035400440b2903406540344c03082401804001d00270141104170b60040c2815000d0107241c03000710f501900840b03010180c034507900c582226038240728501c4c0e8298000c24000d550702d40f41c07818030010403040c1c4081e200c0b152480340c0782030054024480c000988100a110303060403031500c030401c80a584501100000c01610708922400284030310740d0030300280d00c229081c0749079142607482c940c1542c0c1219103880455040c1100044120004007003240c1107a080a0842415a120300e0714030000e0383d24990001018041c0c0421514869010001d18000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 481838282 1250 481837032 481837049
    0xa050402100c03080c0c0102071211070b0405030a030806130903020a03090608041122050c040e091501090213080303070806010305010503030c0601090b0102071503060302040605010815100e1207 85
    0x7030448800c01128600b410710b500801280540c00400c180622003400792141c106148005480c0c01d1701580d4048107018004401d502286450702c0300c40075000c0500420002d0041510301504091030000020b503201c10f000f00180501600c200801d0581d21002110000d06801250030b028100351445c00940d250340d044015000100d40c4032010907403903c01d403100340c001d5070084034407a24451004100060b08003072210040d561854080c2c0021807480d6809080d10443c080c402d056211490034103025604000104244860342040742c01465090070840c1c040e0649081000041c1c1301c440e00740c20705003c4801c54000804038030001c01040300041c3d0140700c09219007420313038060000781d03070b07850916940f40500b8001c040b5039003000006000400c290780c0800040841441241e890587d69501c40e024000821000400a41c84410500070f50901e0700403000284828a40700029140c601d022005601c00c01c55002d10509000c28802016842040184440f0703e006046c6910020b1052405540c0d200c40d01c41c4509 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 481839532 1250 481838282 481838299
    0x150613030c140f01120e0c031605090703052202060702131d0102091c021c140d0516022403010b04050109090e0c0d141c200c01030c11060a050402 64
    0x1041e060516600d003c00c101038481c00103614940c2c1c1c021010f00200d00e0164072170310650f0040b407150707542001014444200036042c04402800d100070301c411048018114004c1c10305140620916850000803c0d60301c4060214440034140f0520009026206482006c0e60040402c4002528103c55078494980501b40b403400400b41340c03401c03446509034080c82034002c0d0710840703c11403600030882c10032480400c0c5200801c00180c00300034000c80d54240710820000d4640c40040342e0300e100320403001c1050b0b0700b07416603609110382040110f02d036004419024900c000c2c01140016184c00c24101e000c500d41a40c1c050444000b40c480d0f03103030b400e16035081d0094031456000411310040000d498980d80b240c00d22034850000a00314000041d81482850100b113001203d4070805a002d8100f41841404151507948240381c802c2404040d6101c01003003401c100006078814200704034000a4040700096a140c0004282000300361840e00d5142501c0a07101c0c5800e00d0b1036170180704104030715402c0759400700703100314801c540700d91 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 481840782 1250 481839532 481839569
    0xa0305220206040501050d061502061f030b04031412191a0904080309070305030c030306010f05120103320304050118120335010501021c08150613030c 66
    0x5005146200d0007a410200802c0305000d1540300c1c90090161011001d804521560340b111945c5090302d072034000c500160800f50602504507040702c43c0d41003e00c0000c88242c1040e0540c0c48010b10020041d00040a1016811150015001d14002e036103a821003017201401d603151503a4502d1540081100700d08502d40b03099100040400d2248042030340c1e10020301449070030780d21a580c045140c3d0001d40325010038840c40304000000f580400c028000542030002071526030422800251100d00c241880d1014000284070380d801d5180c6500c205411290420189001c0142c06403d40c6c80c001d043c00c030004440e40d1282038030041d5480000080c42115000c0e03a800445018644410604045038000c2d2010351200d01c3d00b007c0428400c0d90b003a4250620545d414414490503010100c0c803012318410049005d0024004003c0f9603014064010b104604c2070300c60440081140c402000100000c22441680180003003139086501d0f030405613034115899029000009440741051021110381d845140000c50a21000c5c0703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 481842032 1250 481840782 481840831
    0x1903060c0906080115200a0b250801061d01140d0515010e0109030627050f010509010e070614091002161a030708040f0c060309060506031b10020a05030a0305 69
    0x81c000b007070170f40d591043c210704204920132900c078010303d400030503226440c0304601040080c038070035020314502004101c00d6101e211555003200c15030f08440c01400880d00c010050540c11450100140c8456441242110520740050760005040c110340100c844000c100c0307001e035040b00e13072040340208400380351038014000a100450f07498074000789490024500766410400104607400c0340c4101c02c8140d03000c3c0c80841041349010144032080341d0644a039800300050074010442841401e810106500080c003036143c00f800724540d148031500c507507020094403101e41070441208a00b95203d038100100301420b04804c002000303644508188200c031800c404d0302e00001e500700314252800c2c180035418542d20706590ba0380e04203440d034910081007940d4064080c100704000400c0b411114019000a88000890900c42c0c01e00c0c0302152401401280203912109070b0060204824410984e0356408541c0c5c0020781541450481c1440e404d040c008210b8800400c00184807605500403074030920007a8000301751441c108421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 481843282 1250 481842032 481842059
    0xc0e0307140d0305030711060a0c110c010801050f12150405061303080c0307030912180603020408070311010210020706091104090b010b0a0302070f0b15030d08061903060c09060801 79
    0x105910582007016840004d01a0b406194040e8180c100f01415000e60300965091000444005450641c0e0300103030032040340c2190819404815820003004850a80c00000c0c00101041c09810f10440c80440c0c010013555a071a403591111400f441038540181c81026441e04203801a181264a801843c0c0003501c14031114060f243c1e60f6405954104160f101e00118410b244c0c00903007030b201010384605407940401c1000b200280003100c00e684501d003a8814a4012254210a4110600700b500400042200f5003000903040296a0081d00c03440c881030700880140d141648900082c5001400410a0010320066034082c00c541c030701540650804100300e80c1040b04484000700020b040c100034100610040c282c0f034015000f8442203040c010315010680e2200c1d0904200c580003114000c22400421a1092444c4c60180d12008154024280801d5400000c0c0c01ca0000a241c0390041c5a03141420240003440d9160074011500800d00f0082c61030407500080c40c9020078000c0300003244c0048000076000d07601d80c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 481844532 1250 481843282 481843319
    0x2090d3518010e0a1d01030303050903071515050d111f0c0b07020c0301090b010f0f0f0608220f02092a07082a010c0912031209060c0e0307 61
    0x4500004000c010056940d035103c03988840d04110300e0000452004032081d00c4003a00b884007803403102035601d180380003010350314020040d8180340c00500c1454002403051076640344602c12a8000300d0010319040040742c2400b982c0d40401d50154140c0041d00034402420400028501c041c1c90414064038980980c00241296658881c0010340e05100342001c1a01c3c100d5058100340d4520584603c40b8001001900b5140b0341030040c9e8082c04541c00400920080c010110010020600c42084162070107800c100d284580f48144014032400f10005240303092440c200c00d030039400501da50b510510711401c01c40e2044d1400c6c001240565000c00100354401200c03c0c03061102c0030140d102041c44c5100f8041d008242d088260301300c951040600c02102040c1200001c2402cbc00c04801c05a110585003050300c0f82510b02154021041c04901002072040201d8000d9020003150903040c00c004103c0a505d000004004041000d8501494040986c01d5244c0c0702c00c0d1503a080c04124112400c0c2516070008100c01c061110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 481845782 1250 481844532 481844557
    0xc030a180501030b010819092109050a050d031101020918010521060c070f06020a0c0506070f02030d0b130c0e010e06190807050c160510050c07060302090d35 69
    0x10002000010140c2c0c4003170360b0300301d070140120759101e441c0d4509ca40135402c8690004843c3c0302c41e4031006041e5021030824001c0404507181014540b600740495081110048040c040000702070f85051801c000b5011035000d041c019140941400498507440320308602801114031410340070a00c0390340354480302512032180740c443d009020b04c0d0310744640c8040ea03607204c1d00007103031401030b00715400d030104203944040e160f00d00c01c50f12400da9a40f0305150890914900a007080b042c8040314003054042a40001514600c170100c0d100010301184220005440f07035080c00c4003041207410294807010b0551720069080881100703884040b41008144208200d90152800d60501400624040301c500e40c42499450707008040350402919080c0e606082a0810b0303058440c1500a4031010800c0000f414543d44401040301d0b20300e030940c20081000c0e1000c1d1519043d20034102050740105100c0000e0741c403a200d48845a501a50004040103103030b2104040c100500c0110040c00d480303a02d10303100030b912030b0200c030134440168 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 481847032 1250 481845782 481845797
    0xa03030515130b150f0304030305070c050a300201140703060e1b04030209010902450105040f14030d02010b010c0305030a06090603080306240d020706020c030a180501030b01 76
    0x1640480010f101644203a68000303440b108a460401e00f035401850307451991514a036491901d41009000e446001d09103200b04030381c4444030004100702040d00103600343e024030440080c0030280d03400c0e07071040200d2400b0f20f050300b401c04400d2034041d0150b1090020303002410340590903a54102090307003290498821160300310032840c001500c5400740d00b81000755030705100803d400c00e900c0f5000b058000c40260007406030240c4c00038038010801d1000b03c070300d9403c0c96401600c044079030360f9400303580c101d91159000360b4201d80070700c0403038203582e005074190f4015058246040070b910743e49421102208040f111a00d0003801880513581c110340c81030180400c1c161041e10790320020010781c3e070210780c10360004140641b116510500490401c0c5e49025a0340194012051503403241000010030411002580f43c400760503d443c4440a030244a810507030b107520303c80c6400181c640019041c0500680700d0100d5001050100142d0508005d410002c5040c4400c2c501400408107a2260019011030b850390100c00e0119108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 481848282 1250 481847032 481847059
    0x4050a02121803250f0308040c2c0a090818090a06030503120403050d020f0304031b1104020906090301062603130b09010e1504140d170c1507020a03030515 68
    0x201c024003e0004c655a400c04003800e015103e22404d0b000c00c0070120002024a000d000c1408600349241009d00008041d43d10100600c014a101c81036440ca00c0101d081d04407000500c3c100744a03848000640d03084591155074403100014040065424191544990003100115601e110301e445403409895000d0011850460030300a00120024010320480c2000802c100414146c3c1c2540045c01c0c1c42c0e0700d1203468036100e041a25002c6c02d912081d141d21490000b40390340304c102085121b901e4042145c3c0598005982c1c02e07a01c800f1614034400e070710100c0e1b090340c2031003000203c14000350000702044d100446051a0010301030115600c0340b0807120703810101c80d48040244850074903400204450801414500300c20711203400403400000c0f10003805011180085410030001c401030040707012030a41190038003080e090903645e031900b00034071810200c0d050002203500b04080500f044000c030030700030741200301e0f0040c50040c2000b561003a80b07203000c4002034108004145100c408840401d0690300040203401075040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 481849532 1250 481848282 481848307
    0x504061e05060a091812020c120a020306010524040b03040b090706140d06030605090106050a08011404080f04170a05160501021c052710020a0b0a180204050a02121803 73
    0xc2e010095100b0855a640d08800a0b880354070034542c90b0711580243c0000c5040a082050702714580f0019102600200b00d0f00d001a40d0116006041d108215061030110481907400c0c1000e440f5103036604c25108000034007080d007202d41c40103944260f00c500d0382c490355903035903412081d150400c91040502048055104071701d030010f100080c10701e04000600028945a4a0f1561000d07100c0988880c103044e513541100b40400d0612400c000080e081040090045c000c00c404a0000c280780100080e220701c001040380084084600101c40c0180003407020a1030842494a480e5200c8440d01c030201da0500c903141d0820071050680c031240c02201e42c143c01400702034540404000c1024062045a0b0070040100304207144c1c914004208400f100744584003074000c21601051001d41c07040b02850900390744c0104e50920004800c45c0c07131140d1103661410080f846004100542c1416401c0320f100941c891b042804008a4a80c2907014100c00e041070b210b803506503200e03070420751110000c506e294041034004202c2c0c0060402d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 481850782 1250 481849532 481849541
    0x2612040203011d12180901090c021e03090402160605090d0318120318140c18010b0306100306090203181908032a0f0c0d020c0a030f0302010f0504061e05060a09 70
    0xc6054004500d011703107580003d070400000b60054980e0981ea003401c20f0203e85d04201c903c030100020a281c04800540d208d6032584ca001d1100454801c680001d41404900c0b5540090181194019401c3c032040c2800030340c050311003c08203880400a4039100718141c13284515007040b101d00d03070440028110709030000f001304c0203002d031014603c1e030309044c803002c02c07000440c402030641c28024400c01500340c1d0410342d000c200b00c46c54140700280038050454018440c80041c5401c40b038000300120340701c0441c11340d100800c3c0e001c2c100a9202c82007240c07002c0104110b10380ca261032409060201f4080e54403100303070802448590701c04c0d41005095168188000344054a0f810752010142442d05011400e40001519020907640002041c040904001c1803c06803c2010403404140c05968006400e42076007001c080380c141e03070382884060240100e4000140070f05000f9481445501d0103a90144030900e040d00b0301c00c0c05020b01d0070419071361072240345881d0141c0c002c038411280540401000400d02d1458105000c0160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 481852032 1250 481850782 481850797
    0x9131b0e1f091d1b030601020f0607020604170a09090b0a080109060c0e1e060706020408011b08070c0c03060b030c100306050103140708042612040203011d12 69
    0x5000861044000200581ea402900525a80d14444281001c203a0f12203211a105014110041941485882400f4a00c0d1080c8040030300081c41e2a81d890500407407038440c0388200f03031080d40a04428401d0003503012400510880c003a02800709803c42c00031400002d8401c54880340c0000345118824060814280c2008880030f00c020444d00180d03454448140c2103800b00c1ca4101e894903510031401e546240c2042113841c1081c421520354102207405212211000c0020720503c1c4a04000210b840c00c2044030740c1038a0240035107030b00030440211501c90b0101e903e0000c24107a03020580c1c8a000904240c424144a54516800500008620b14540d01c01018081c405c1e03909516000703e41d007040341d80c0c980724650b1540001c03e41e07000c20054540000942180d080c0552003269603020b000b000303d01d80d0040f1116401c680d0120007051401d000e044049100c42d1500300381890f00f100060032003480d032407481c1c1d00c6003d48d0084008220507000c1c92000c18000121507210042500b00c404d0181e40315500c24084c140d03e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 481853282 1250 481852032 481852039
    0x6050f0f15131d060a0b0307051302030606040f1404290111030c0105070c0c050102010b01050f0a021612061109030c1909020d1a0315150d0b0403020309131b0e 70
    0x318806074038002e49404041c43c03000510fa101004000e81e00e000b9000d0113801c10020341c00341142900f09404070f03403d0600751152001280c2c00001081c032039154141224000d2420421448a080e1204c80314460b282d10a10320910072420240e81b2215280d60480d0400b020b800d96403807030144803081005440000d02041030701c5403400148075030b21610b8801c1c02110321034130050381c40d82c0f01107a9520344111458080d800090440e0724001c201c081598001c412914a58442040a6243e440c0810100e151003031843c00c078250395188000000f6541c0081d540303441c2c002d105541c2840414a0403010b40900d02541035040d0781940200410b2009090901400344041c51910a00c292103484801c04000ea070700503010000070300c1c0d5511041070341441c00356030602100b0301280034000515181b80041e02c400400b8060a0104158102420580c2e40b10780b10020301c1035001400e02120f241a0034040c1d00e903004120031710b0050110400c0e0030032401c850b03c96031020900c0f81c400340307141c0e62030390340121500c0b032892409941 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 481854532 1250 481853282 481853291
    0x30204030516030507060c05030301090b12150a0e121e0f040f1703070b041b030f080a020d0801060c0308062101270503040302090c070f06050f0f1513 66
    0x11400c14080c0319990744489a07000300c2d140ca50f2606a2408a10358451020001c3e40014140011400f104490444d10043c0c0301103810b2100d400080d010280c1a42d889040740310390110817000003106660548602c00e0302c06c00300100701812120f291644000c04018109840400200100010b41c02d1485400030350326968a01304034800302c090390540e1054000414005050310300b000142040c004102d03d0882e40e13800355050075610768a0150110025000034410402c0b800d030780c506183c5c00c07104100295000b4038580509021800d0051311035010b0034002d8014003485515806941c0200b00082c1260003c0e5a02e0201d42000d45080300d40c0103003c3c00032070707220441030f0206009c1b10810100601042482000040c1800c0d038500f20b60034401d681c10a040145803040080c000b0407008000d95085a80640310149141e0300d26841e15498814004010900100201079800780001c2d41e004600c14800700c4200f50098079912a84041c6a000300c80000034400031510585060030001c8100c400c0c0c030300d51031340440d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 481855782 1250 481854532 481854539
    0x90618030616031b05070b18150f070306080a02040905101a031506030a200a061d2b15050f01080105010803130510020c0909010c0816090608041704060c02040e0d0801060c03030204 79
    0x40c100381c0c18800b000c9c1d1200c10213040c041e0010002400700d4000400c0d00b402c00403140340000003900c0707485640f0041d12070380da1030841c0340600500303010741c000d1400860f0b4100800c541e4940000214080074410b54003d12401050072a8000c003842d41601550005006180600030ba59520380c014020052000300304004000180840d15171140080103800c032925105221216141d4030480d00c0d440300070b203a00c5040300c03151392071103160701d4110310300b050303072840c04400e8136441500704108441070b070f030118025940c07030a030403c101220501d010034143e0340c034035000f8400c60740d0b0303500611380d40e0191003500740741c3c1c0311035a00400c428a03150003890350400d81401034a00c00300c82e400014020203402c60700843e06035180d54000c0f41d51588990480d5000000848014251406c00740c01000100a1b018000a111000c400304042c880020f207068107440c900f4805030358680d2202030091075203603da1012806a8244200ca000c81c0c0808680c00c07202c10a1507a9581c031580ca4040102d484052114041e01807503420030012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 481857032 1250 481855782 481855831
    0x7150504030806220204060e04150b0a11070b0406050c16051e0d120906030b2e1806091d04020321070606030c1e0605090618030616031b05070b 63
    0xa00c0101070980710808d21480e40d02c180001d9405107040c03420034500b03044061240038007003000e4030210082440e01030711641525045614015554104031a5044085400503145511500401c2e40182040985d00041107080c0344000d002020b002e115404401946018103604100c0e400c000d481400608487d000c41c003231f840c1c9050403215440d032040040d50307000f814009540c060003000d50200c4207941003128030503944d4408010090381301d1602d058204010320301c016144600b49201850301d000074005031165039018013500102851041c440090310315540c440c2c00108203c0380c40e1003160082d001d001d161107090422000101440001c10036408140585004510030341706410241d44200a2000b0341410039110a4104000d43d51006110701080014003440d60b000050300e000b01e5098600c80c0d1603c2d0300512030341010095041d1075806204403410482d6003119183c500d104861291001c202440001c1c440408080e1695000c00100f0410800b02000030360300012983d003c050811002c0407030203000c255 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 481858282 1250 481857032 481857037
    0x12090d0b15092202040e070b210f0103030219051f06030b1b04060c11040c021006150509060310080a03050a020f16050d031211071505040308062202 65
    0x8001d10909904022410381000c0d9101500581c07202c015a05520701c0084400350540c81c020001c0c001c6445652217240071204018640c09007034034031185900c3d5100049103410784038818800500e203082c0b040220b0004040076002c1170580e50545e000e41882040c14650b03000030a40c4c0b2800312014404c0002065584c500940d0301c4002100d110f00c0030801d13910f1420f20a03a03c2c1400b4240380c5404150034502018a40e0070400c030760842d505410305101800d00b03400c14444880c0d54000142c0c000341420314042c00c035a0b0101f8401005844958200074030b03a11041401c0d0f03018040c120080c0801c4040020349080d240500c081e40d03000314a02031085000340c0300c4401905188010703504030b001c1180415100341082c1c0501c8110080700ca880000c1c004158102c40d00079500ba068400c850041d44004155002d06100d000922182410400103210321207512680541a900088040d2030403910140c120382288800c1c06801e0103960180e60310340301030b00d850041148034900503250008203c804c40249130f071180d09002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 481859532 1250 481858282 481858291
    0x9150e040c0906120b1804052401090c02070b030a15030807061e0e10091103060f06210d0f0513120c1203020a06020c0102040f08030318030c12090d0b 66
    0x40380080310b403034844054031103140903003c013440ba410f0008141440d1910004144c0b650340e11048806c2940340c1d03060943c00c051328868030500c03024140b01800c1250400e04180340c101c520b40c540030011100c003040103e0701c0d02c01030701944c107000710300f0400310301e1410154210440c0c0c03000e91403400c400196669100d1903640d200041c125999038a50b04000e141c140c00c55140b40c1c01c0b4412000c240400d507886142507072244540b0980200c00c0350f4030b41041c1c09200c544030303402d0301d040390203412180c0305d041042600700c1c400822a0803d00c40c0d4020599494580011400c4041d0009010300400c851104030303405171511461001840c080140a01219045100d005680380051401c06541e80c0c1c1c1d09218113205e0714410540e00200a0050046012030000f80c0c00204045842e40000300181c545a0750001d950292080c3e40c85084c840410781cbc00819411000300c01940102c101207024005c1c06580380c60a6144d0041d2058881c094000704140c00003080400c00410f1201001440c0d03022000300d42e9140300940a080e203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 481860782 1250 481859532 481859537
    0x31b03041505010f06020c040f021606061503090f020f0f0a032a0e131112030c100e120a0909020c1b0603010503030f0714010203010e04060c0305060109150e040c 71
    0x30751400e0761a540c0d100c0c45000d031003050101c113403140c10004043d6403180d800c80c1c001e0040f542d42c504404420003e034192000e03142110800d07155108142000005041c1c24014003010661119031404010300034440c1c0e0054991000d1403a00c40072541e0200661281c0819403e5001042913075030b20000c0d50341c9440307003000c2e5118003020314111040f01c04150102d503580503610034142d23030070b80d00f07000051b652001268843c40c182c0080d405200c90340707071180f11071511000392500503456075061184040007101420400c00e00004540583d540d00d07810100340d40c0d14034200c3c0ba5a8000c460700e111030807401d00082200b000d03d8140004043e81d13900c0244100e070f208950381f240f0750704140291140803100702030b01415588120b81c058210f50500c00000d480c0d100309403000b080410001145e0701040141009074001c001400002c5440307603500c416204440c0c0e012202202c81030b20f4803030881c2c40c16009128040c09150180c0d5849545c50034020041c40020f0390984c0d0609020745000f582d0107a83c1d0b0b074021100c14411a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 481862032 1250 481860782 481860803
    0x3060f040c08070302090f0a0f0c09050103050a020f07030c17042303070614210406241d0619060504090c1e050f040317040e01120b040206031b0304 65
    0x1d0600d4100d901c0d1903040021250040442003016941d4954007c1d0003143c00c441020464840510600007400400855103c1c04e080412422903e48c01c41c42d80c40460b80c0c00c0c0c8080c0801d80d0384071561000c0340300748246003551210074000c0c0c0300803d100d1140b45141d00e00c9041e031114001e0030304c46c8082664000341c0c0700143c1c10041c01143c0d4070941904180386031504040d0000d100f090b00b0b184010301007046074003200b5051040805c6054094402c424032040031448000079020b90b040c2424104041c00000107840032100428040700c5004000501c1e00080b41e2010381c148984800e43d000300c09210303101800550b4400c1e04c000c1c128000d0100c030360000d40205101d440d0b01e41e03100e00d03003040e01d02560400020fa00030f00c0100c1034844219182e2019074460f40e601858009d54491000e024150300e8082d5402c058100c8840320581142036402400a2081d1459081109500daaa46118100c01d81c0007a9005104c4103d00c00400c005003800340c041c0d5000300b4648054160600030075100d4102e90000c460658011011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 481863282 1250 481862032 481862041
    0x30d060b040f06080f220204020c030c0106050a0b070f02060909090706022503080307110f0106080106091b0e030f031206041b091203090e0a0b01080924090102040503060f 75
    0x20040b0400030111400c010032107162181c841e05142c036004060317681c00f6180140040410030365a4410040c1036008208549442040c4040381d92608416010001d961801c034001c80c0030328042820000302d50350702076a0341c502800d41d40c460026414250b0101d800c05800d10480d444d950b5040445032140607020011b02d90541740070b0000746071401c80c10303030720303900010304101c01d110350b006501c0c10703400c0d00d400101c7e1070368a49603210300700d841054002c15500d1901450314802e05640c01900200d04596459000b8071510752264908000c945040420500c0b462020740010440c80c0142d052000589004041c0c2d00180d1900c1e10207421680301801c0300380c411031940100622807405203d03800e0f01442c0b400444008509041001c2c0c505521402401a02d0711004114400c05116030399120203072000b810200010300304a02d6100180415030340c110f011544802c0000e0f6001c030002401c401d0100302c03002001e810b442d000c504070000345024002d129155000c000104154030f0801c6400e010703001010041143d841e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 481864532 1250 481863282 481863299
    0xa0c0915030807051507081e0619060c120f0906081806010b0a090e010b0418090f0b06010818190c0e04080c0f0a0209060603070c050708030d0e06091e030d060b04 71
    0x5e00030004000e0204020034490344601c641c01c40b00b2051010020508aa01c030400021040d6031801d1b00001c8022041c003002c681c007603104600c0c20f041031161950000a8000e84d01c25504640c000340507100041c2c20340e104005051044682c15003118041e0910040c0d100c000c45003504090303090b0032807a40b5000020355400c1d034a07401a000c0001b88400c05035152654185a40125244194460303040403102c030280400c5400510fa01206d0280d03842100c0d00306030501844e010b02003401c11640140414401c0c070001c2c84030880724441c40c910030301e031300040d003140d0119480314075880034003550903200640303924000700304501e050101e03a0140d40a240f1a0351186c08810140c0e1805d00ca034444901c3d95040500c4040c01a01e600030150f812180c01c441c044d0b142d81c2d45000c00c443e41001c1c003801500382c3c0f01c3c1050000e4181d001000615003841030b004140b00c98001c1400301603940005689001c401c2d8000210040001e614000c01c091010011080da032400746404800b20581d686600074400101e4001820845101d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 481865782 1250 481864532 481864573
    0x60e010503060d140a0c060f0c0c0608191803030e0303131401150f140a0f03020609060904021603020c040903020a06050405070e070201020a0f08010e15150703080907080a0c091503080705 82
    0x210038501102c5545150703460282c0c03004c41d40f089500b332103d8000495442510204d000700700c030112000800c01c00341c602000d1000507120301030580102c0d00c0c1c00b5903000c4c3c240011049134030590b00450300600171191540d40c51a0380d40d03071100c5080e803550307590920b1032800c00b4451014001c1c54016a1581d0386800c001600120391614030180d1b100b140021810001c201d42102441d04503601140c40d40d0311500c043d000f0808912035900d91030762103440019100004400e0441107401745000b03600300c034608101d1406110844030709040c0600944d114042c000001029500010360252151054520740c0d603440b0f00c0f07005511402d4a942e00580d40205484510030762043c1d0030b0101c900c452800d03034482d500d40300c02039076481800781c00c000180c401182845905d4407003006070807114000f04802590741c07200e418003d22805060f070380b8025500900d54005024540090781078105608061050f84184c03070426940020701c02d417905200340c8910f00c140000810200400307084050b0180740501790321a0301c0b8014006c5803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 481867032 1250 481865782 481865807
    0x100801320a30051020210c13260d050403060f060501080a0b040608030f07060b031c0c1109070f021519090503070f0c050109060e010503060d140a0c06 66
    0x2242c401e609807003c2000010006608180c0b06000220300c2100a54614030141d14282e0300507014000039102030084a00e00c103109510042440c030003040e00c070720b0300014091190094410080c4041c41060003107107000c1d2032001c01150011504488824002c0d142d40c00d000e800c60307191000c034401080030000c0c44843d02403040fa1603c1030b001000700504220010344040409800500e003942e17a20b511f03902076101c42d40305c070000d0f1002d5812030361941090010107551754021502101c03642c0c2003542e400d8440c1130020726041c00c484007449800c8030742c145810480f1301c0709114400342e90700c1d02c54040001403512466011405500c0e9a51101c0c0d0709402480084e141c20a039102c4c1e0502040444208038204600600c0e15040d10114030002c00c602d85182025407450061020240c1480c1e6810314010402512008c1c5408891082c1c071a07840059480001341d80428403401110b000c50420400031391945000035400d105107100d2448125410541e800e501d10300103110300c084400c08c031020f0341031200d20380018041400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 481868282 1250 481867032 481867109
    0x91c03110309090c0a050d0f06051207050306040311150f0a0c0809060c0a02010608030c0f12070b160306031202160506040501090312050403050d050306100801320a 72
    0x1c2410b20400300b5005800100048000c080100701400d456100b5011200d4021002c4d0003031001c242074084501c014581c600c60248500c51506100600c1c0c0400f150807001c54100030b014200c0f541d00c0d504e060304c4942041c0300c400310b94000c000c515050f221043e403503280145880c000100b41403908001003022101022032080a00004400700060110006a010340c032100d1411718644400c82181c042c0d0242c143d94002c04582d010119001000e49400213424080d008198111a001001e80415110301e1288410140400007000e00046e001d400000c000d088269052400080c074a81e41e844a40026440b200c0710070040e00300d5100f064000034482c0b40f5001504007102c050b0715042c6440c0029081c20f805200c01820f0500100e0a425101e00880c00e44000b5508a02521402031703400000614a920840700c0034880c00401f01c032598014482c01000b810788006003550109505114610314400406140b22030030b010391030090081d15104e10b14510001c0c00c000c1d0840401c0f280302c2c2c0c199180c00c1c14500c0c01584 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 481869532 1250 481868282 481868287
    0xe060708060f12060a11040f0e040506010e16030b2b0209180d080a110403052506140315041509060512150709030c03030e0906032a0402091c031103 65
    0x101c5001c40c80a4012010102c00206c80b00c4407511030416010b44d0703010013241c0782d250400081c0c1404aa654a2040c0e04c10001c0d600942c0e00ca440070700c0170380e01c280c0d001554022824842003140340642d21940700041c006280b00f40480d104c003000441e20040d1020316400b414005101c104504008072415000034080c203660031440003800542e60f40d00b60800c0e40d04100140c600218004202c258420003148107090200d55070350b07840741007150b55a0740101024020388081d8490038400402414040d00b03461071592480d1010041d0001c0b008203400140840c000d0002e40c030300d00c04c2150350b24403c96614020007030b07003c0c0e80c040c03501c5030b1101100d400d40c0c4070602a80340b880550028080204590b0402010100380c00344541301e008044410700b54a410081c40194011404000d0540005207108007803000c803100c106c6a5624007d15441c5c00300c4505000c090b1034a43d4003404542c161080002404001502c01410080d10400007051201d034801c1c0c05606621102c2c0703400900d944507480b600208682d000440c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 481870782 1250 481869532 481869559
    0x102010509250308040b070312061410051303051e03070c09090c0e0712050601020a35180a0b03010312120e030c010608060117060a0507030e060708060f 67
    0x152a248036404401088405004248114001002c80700265410070401a103894503040324030659070140600381c020400325a1000f03d910414012101940c04403022842150b0304441400f035503030080c644841c1808010f2203201c01414030280002d004600441c0200310441e071981b4003041c0404240e0701c060080d00304101a00106902880481c00c5601503a000101c1c0d03529030130411404e400a41092090303045440c14446082e0b8404010250b0700c200d05010000d9403242001661f03510313807031343e0006c241d003590058034002d030310f1001428545844800301141051103e400c82032600d600c440503a080124000580d80344a0030181042000b4040310369886280d94115150f81107102c4090f552141040003410b65000440c6080d0005036040d90007500300c07a1078181c403000c0e440c041c000d0ba000d00c5c407081c03103a00000280d00c50080380c0300b0b20740c2102c50050f011640326011170501400d0b0003482031007070588070007099180c6041002094400c2e04c881c1c1d50251a401c1040c200711030781000381c84452140c01500c0940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 481872032 1250 481870782 481870801
    0x10090924020c0303041401230a0b060414010809120705060f0f09030708030403020c04060e061305060d110a051027050616021f030905060f040302070317120a0c0e01020105 75
    0x9941158005206d660f440003001c9000c0c1c05400800800741c00401e5040d90084507030b410f14000ca0180c1042caa00f4000340c0b40003c180300840c025031140c1c1400c422480c441803129401203102580100a13a0143c0f0b4910911001c00001988411001c40c2c2aa00410401c1750046815031000c2e0000b21200340450141086031010fa40c902400501402081000002c1400c141c000c0110082080c2c000d8000e100780c95a4026088006100f1181c9500540940c011907010300760921840c0d1040e0401442c5801600d0140c580c1c0840b406002da445401a02c942e0700410565590003030403010441d0703903031a0484034040091a0031b01ca00d18111a9081105090341070206503141001e4440790300c540c034030760b044c0c1c94020700001d001c4420070714400820340e0b485404404e4059254001d010100d00a40454072035451f41340049001c9030b0111000340045c0c10079541840001d90312182d04a10030140010603041c1081c00352040b100480c16240040340315514200000c40c85c1d0411107847e01030000f40000c100c10b2a000c01070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 481873282 1250 481872032 481872037
    0x607110c0a0807180e1b0102060609071407080f030a0b0a060504030f0308070e040e010506100e0d12200a30030513170a090503071a0310090924020c03 66
    0x7607010510202812001d2040158440708515079445d046800d1260820410a00450410481030040c01410006186c03418094985401991a80e031854206850350400d40047d4200e54412a4190b04c00c010000b400c0d00c2d040003130350203065990800120000d040c420845111030a0f80700f141404130a010400c04209560340f4800110b4150a0884559490801c12512400c00c850029030151074071101ca808902c0541c0942c0c810401501c0c0b0701424081c515040c3c404640031100a98040c0c004035000c0009940c16417100a42c0c0c1490920b10400300c2290391881404121444515155001080200034441ca44201407a051001110b20568206054420440c00c0d492801d40701810b80340c902103840c80050038220101d80390400504d442104490748040000e03844045604006581024085800e16011400c90111429400341030303c1003000c0300100c010350304001d04000980350715050000d17250744640078100229100d4241c03005070498071000008074441c58a203c9458500c10b000301c0c0d01c5030100204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 481874532 1250 481873282 481873289
    0x11090f0f040f0611120405070902090a05060c0c0a03110306070804030e0d11060c0c0a081207151d01090b07020304050f0f0d1b060906080c090d140607110c0a0807 71
    0x10100c0b0760b81c000d8203012010300f80e280d25803015810001000000781050b0208240250b1048007030b21019541d4000d01c1080e0700445c1111988405600000c1110380307460801091000c0d40b4000390786070520300c0c5000803070a60140e4019610028030041c60016450248041d035030089180c2000764090509483c01020b480011425901031030b0f002840f5000d000b90420320000c1110002c0880340d03214121011031f6200d011800305d0b28060f0071102000724800c04049508040c6a03070141d05d80341001503d4488800d403081e604a00003040d5950401640c00310400a40c0c03510005458001240140103881d062041210080c1414115001884144071650341d24070ba6100750075084551170071440c13181001480074280c035400181648038103065034202e0303082049490112103007a01c40f411a180c0d502000d490ba11000c44040c410018200100061840c250024a4046000d002d80366103607404c0750011441c01c80140d4800e00850900505c10807078440401070f0364540c1405a4000c0a076603d0b101406664100902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 481875782 1250 481874532 481874543
    0x3150509070c1b03140a0305030c1c090305032d01090c1103030403080f011508010e090a02040c1d0a0b0f280503180c01020a02130608070311090f0f04 66
    0x1022502091188440003000c2da00540c400309082c040e03464501894a89120031150301c8452003140b0085c00d804600c1040007034040d101e040c9159580e4140c1c810650188407038914292010a18030061a014807840341705520a0700c44955a0a03c0300d210b140318030304040d101900c4260400c1a030207000e100c4208504603100c0e200b011a026650003c10b40300d000d416821000c042c4004002c20043c544e00c490000e01807428546002c0300380e600c40540d80490300c144c4c1c0e0f46a01003441200104213428144031141d0b4410410002e65440c0442d980c0003800f9204500c41e080c0000340420051011140c9407465020a05001c0b01c0200c01c50b0318010035803000c0c0c00707900000c46041c030000c40c0703201d881254021528484824540484842415a44041e18980064a500f0101401c0c8903e642002c080010400202d000580092007801c0087d402c0003109075210350340640301c54480320001140001001900e01551207002c44a050545a0081c00040f200083c035250b0701c0720303440d814800c2c0564481151070300140c100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 481877032 1250 481875782 481875799
    0xa1a090d0e061210030b07020f19030507052a060a0e04050a020c0a1203051501020a2310020c0c011704260304080306010314101e0b0703110607031505 66
    0x19000192680900c15104801d4540c0b881003200341c102202e00030b405e59109a8010200d40c55240049964400019101c03080341c0c41a195400312074a03618003214414403a16240d403808802d9a140750600100c0548502200c01c80840d0780d452025441d55965040030035a10702c0c1c104081502c0c000c1284c0d505418040c082d0f540e074008038502c2806030301220745a0b803002d8200c3e01041001d00c2c1036800b401c00c100765000003d20301400f0495100c422181103005110503801002c1c0074400da10fa28410b4582d2003c0c050f04c0381d060007200342a50a040c8815018000326140058542c41581096030030101c411a085040000351300984905421036941d4640298000342a1b0760001c0c0c44000d542415000040741c0000079101008000c00c11070030701c00451149100baa010300c0b0070141c101c2148003440342035072184180c413204a0b0a0102c4c0c4051220690346907040003600d0b01d096600c6982460540c41080242d00203028a10700341e1801c1c1c403c0080c03070740040f0305150800510b0300041d28042102e01034003c3da0303c1480710 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 481878282 1250 481877032 481877057
    0x31b02060405041416140a121b0f14040308040320120a02120303040812040c030b130311060105030c01111015031403090a0303030c053105040e03030403031d030c0a1a090d 75
    0x101d610070040901a09204210359080d601c029110124011781d5200007175000d1110310240007912f00703a90450b5032100001b800d01307045582d0160440035041d4103c070742e60035001050240380d0700c00c010080154015000b8000655890050002c155a080b60000083d80100207202c0040c440e1400c480346c8690422410341e207510b8a151030f426104a80d8030182c5040080030034041145820000141c5152082d110071481d50109007a09490701001d116199064101e03020142c010350080c821303030511080b1075042d604040913104660302245c20354811990304a81c20340007441003110404c6a04031010304c850044d410644036200040703040509000040816490301c484044c0d96000d0b8050b1010b0b19014072400c00c092040040c056042c01600c1e02826019141000014582c1884d1058000140d6050040c51840e541d070f444c2a009401c1c00c214460320070401c0b4414040c00c42c4203001804c080050320000d0300e991701060070304402c0500d54500303040c8851100d1050200380c050004226880d54042d06059118040d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 481879532 1250 481878282 481878317
    0x3190605060d0602040602060a0b040903020d051803060a0207021203071e081b010f18030504050613080f030c100e03120a06090c09091107031b02060405041416140a 72
    0x3842c6004150700d00109010920726000710300b4501c9661050000c02000385140100300603504450350240140e0045103660741782502c01c00044c20000001c80034000028840300200303103090b01c00c41d4103000803903000c5400000c502c3d00404042103c02c4c08401907051208684036a08031040c0107085900025000300e801080016071025524009510404015004030564007940600a0b6141e00a9101d00d40b208a0600e0010342c0960029103400da520f8a080904110900c890f07540042c210a00a0045100020341d4600420030300c809804150080c41d00e50104985452070440741c1425015641e05000f82800c40c141c0c0001510441c80e04541d41c0e1500ba02c8600c518070041c501a0000f0030b0341c44c01c0c10404880c031074020340301400720317800000700f0441500311190901079400788120040000381005034a601100d0806200c2043c0d600041c80649410b5035032000404803085136000d618060314682c100560701061500127407184a40d400c1105160f00701954070030492280c06100f9081c0181d410b2140928003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 481880782 1250 481879532 481879549
    0x506070e0d08030406050f1f1e0302040504030f12021216030b0316030c080f0601060c0302030d0203010303030618060503030904020a09051908070b04060c0b060310090b0108010b0319060506 83
    0x1030300b10340c80c250b40e03060034201300700500320440c1c042c00303e262100082800d07928448400003284504203002841c1358180030000340c3c15603400045062125883c1c0b004801b50f07039903201d1240101c0c42501c3d102016a030032640030784851469903c003c513003807051200000c072a010100e890740c0100c0b45040007801000301e00041d80101164075004d905440350240c2c041c0090f0f1720b0488403003500d028100070410a0743d10245207980340c3c000f03240a10300b03800410042144c0d070300490405081622900642c0c1c104103814140e84102d1f002684281c00084d26107004022401c000070b040703801070440600c20300940703040c040825500c1c402c0c0c0c004503000340e600143e40f404080c03241d03c1c000c5c09130100034042011140148410900d4080da0700500c10316004032000003074115440c004641c104d90300e986030b018590b082d50311000710f502e60050001d0381601860030241c01c0342407144a09182c26214088d080d2455051600d0301c0d08403041c8000c0c02e4001d50001006041c11441e06020940243e4440000300d07040c0c0d9400041500b19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 481882032 1250 481880782 481880809
    0xe18100507021002031b03060a0e0c07170a0804021c060e010c090f08060601030903090b072f0f0409030201060305100606030c212408061e040506070e 66
    0xa00821019158808003a00010701a044680c00c0780e907920300b00003c40007207100c180c030810000350344c4004140840d11500040c41c0c2c0442c0c010070004c0d003142d482030740c3d8141c04c004590501c4206800900c01e01004448035101105e000920607103814100301c0b01d0040c0407100043e0019114241d0420708050745010f8043d11070340154840818820b902141034400e0180070700d1002180800d00802c004140103660000f010300b1282c40703600a003101e40364480150000c01221078150b04012002401241294000005050542c426404468065001a040455800ca41c2c51400c03480030008008225a921703104140900e00b011500029076103d94601a401007280d540010128001c1c4003807180b003001594014803c85030a502c09101e004100c060450f0652003809035400d44240660880004551b0340e80002500d802c0c11192450ba07520400903a400b21035075500540e40c0d54480000c0046400306501d01c65145150315404100034245580c4e040d407600d2008011000300000c004611a80d9030b00e049105018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 481883282 1250 481882032 481882081
    0x80d080c0f0414040f02030f0a0c0e04110901030f150506090a08010518120906030a0f1103010b0406120e0a17070602040909050c030a05030d11070b010617010f0e010e 73
    0x1900e0303580c0741c540d5011911403180f40c0718a14051243d001d4031320b540202c0b44600c05804943d5140e641e150811002084403089140c01c00c02085124180b60b1103900c83e21008812101500381c072804480700040940300c81a4039052803a06004408007003040410300d060942d1411a4002d455080e8240886e507160800d51141c0f03000e40c02c001c28440e851a0302c50643e01c6594000c0706540c0c4502c030400000d54240325450020b60090000c0000500c5404568840301c00194030510104401e101c00c400c080c0c040e0400c0c1c0103080c60350000181000096000008251790301e445d44812301c004807a2501303007611a601c513403024203080d401c0705e00c2451103251041200d1403117912000c110340715038951200c80001c200c1168121540d100d0100c0540041c40c000139010041588000214a4098002c0b1064054040e881000c0300d800800c1c800c05002075401400355010340000d0742d03142e2542c884040321020488040c0e01901c1c002100c0b00c0c091200070010710803d0b065800c000360384070301d6032039003060102c00782c0005450004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 481884532 1250 481883282 481883287
    0x1060f1401180e07020f07030c030209040f05060c0a020c010801030203030901030905100207050d1403060915150d0b0306060904080d020f190f020c2d0301390504080d080c0f 76
    0x40390000f15440394050300c02e6a00302ca996110104445079207034028040941a1a0704c1e19041005140c106d41c4035500a2107079034002d094803e903079078061800c00c081c2c0300103501346004603c403884242e04003c1a00e12400903c2c000059501d1900803a84a20034442181c1c10151140380300c1c0144102004a5800b03010b040b28119513031950707428171648800c0560031110000703d90a83c0c0050701514101540c2c09417100a0090b0129258511100b18980c440401e140e00181e078102c0d42920015640040d003007500050300081905100d860030582096401400240b250700a0014000400d02c3c140644440038a665401640c0d5142d41200d54401e00550700b49200041440480c513180652200c2c0100f20200b0759021181108c07030840822039610b010300480c4903100b000c007401c0c0803c60512840c242c0d075440c0140000881040c841001c8140c184e1600000f1911180f4108940210007540b28580c40030b1000d28003a07091604001c1c1e0b25481e2101a0100c1c03003006410b601044000384603800326140460340c41d15043d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 481885782 1250 481884532 481884539
    0x5010905061305070f0602100902040f0207060b0a211b0f060c1a06180c070204050c040602070e0f160e0a061106100602030702011b02030102030c040302040e01060f140118 75
    0x102c0b14501110b044410b03000d4150002031038821410640d0a0342c080303030043c0005480021189000f00b030802410381e841a26641d000b02c24601c64401016658054080841d170188820203101d490440d035488800c0d0215119031800d03900d1030a44009240943c008284c0c182030703000c6821001400c0040d048018001c40290000880d16044100b210045124046030640b41c1d840b07045c4000b88030000c507841c80c2c11405c2080f07039540d6003810000155025440c000b000c2d007400480c0d000719086400448075021103810000d030a000b21034040010360300403d00c8060b480c101d480d0041d0011a00360000d45080780c00740d0381d40150307c155800307501c4954a0320005407102d2107150351507000034071000ca44c6400440c140075510200303d06103604045a0141c81c03494000390f01e0181240d00440e0b104582d60720519480754410100001030ba000e00055008401c0000e142da00c0700d0541c010401103421140d80284283c0c07602004000221002c4041d40c12203e80e4180300d107081c0440340c01039070f4003034894a0707a082c504491807010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 481887032 1250 481885782 481885801
    0xc2a0a0311100203072a0203060a0c02011b050405030601080c0f09042405070f0206160e06040f090501030209070e031005090c0a090921080604180609200406030c030f0501090506 78
    0x7100e04140e0001c080d0900d04400ca69030000340c01b44074020f501900101c0000f190454039401026010000d40300005540c0e250031420000c650084042400145000600304041c0ca0201b1480380500007110240604040c030034005540e0f406400c2d46203004114650002c4c0501c006204005000050728000c04241c90815804400400040f210703000490350512800c18400d10000d2000c0c46107070300e40c281d0940071005d03040665441151031a96680300c801080086528a211841c105c0246407110011402d54107500c10440e440c1401002d6a080254440c0e2903510780c0d0300050300c607800a41840002a207900c03a12511400d000a0a40c00b50f00200111800150100030b5400ad003103a40c0a0010400343c04600c021000f0750082c4d41c80e103040094000404603001d0301c1c040c4d00c14005500c400c106031700c0304a401c0d03881c0c6042c0c03180c8000540380c207005140c0404640b0500c035a80001180b085804004040c150741d04d41d001c407900d502001c1c01c0340300d002c0f0002003004825400400304540140898001d850400e104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 481888282 1250 481887032 481887047
    0xc0c020616120e011202090301060b0d0501080723010c030201060b070b1b07080a030c02030d0501140f0a061b32100b0a03020603060103140c2a0a031110020307 70
    0x210b030b058010b4030110b10b2061080941d00709081c8142d490000c0350000c001100d020b034214a1640da803556070b900000503038443c410014010b115190b403001c10951324241d01982011210303440300e410310021086501d80b9031560541c8507000c15003420f00081c2c030903050a08a006020503040743c000050b00052240a000c14865003c0c89515081c0428412542da60340000d4a03000c0d030100200765001c1403100d4208540240c1000410701a5407045900702012000c1c00c2040d600c0c01c1e80800c2c50210702c07211f800d0407420000b6640c08500c009952140d50180352490040c00e180303204162040c1280b0041200c0301300484130030b440308406504480001c2a0a840c07020841c0c01d01c01c06080307030842c8136a810320710a81c81c0d5401102c1d10243c00800041044d8516002e001e01d95100031301702410503a58070030707140c0d8000c40c0004441c0211080c5000703a80f1448803400c01d860705024580442c00144110424081d0108001001506290b16162940c0e000a03d541d5442c03a040b6050b48002c0842e0022040001e91544000b0303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 481889532 1250 481888282 481888327
    0x801090c2c0108010228050301031401230103060b010e030304150c06150e070806030606220e0c011107080c061b010203010e06040b060702031216050a0f0218090c040c0c0206 76
    0x17140c14820761b4112821640350440d5804030042003081c001000030641d8954285014045d8100108007900f680c8466413840450f178008030020034041c0014402d001780c611a00b4080d01082c28003a81410480307001903035901461140d142c160040503d005c00300d61080d211035543c07030381c00002403014401460300c00c40d02c01564010306010502c1040001c460610032203581c0c0c007403100500549900d81311101440401010b107030207802c0d13500d00061408408051849600c0c0b104904001600380c4c41c05c41ea00062000da06900c947d02541e100490601c250704020604408200e0120782c583d540d5070010070300070b1003034950002070310107544040b00000d00505024040746c8140c00c00c41c0d042140d6887e5000b007103168040e0343d00213509a0b0090842c000080420070080c039200245541d0181600c40c1ea40d190307458441003030b404560042100801d2011824088100041803036038215045d00340c40d105000a503640c05004110344070b19100c0003c120305602805201c41d42c144c000c3e0080d1340d41c0c3c40740d07805505082c40408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 481890782 1250 481889532 481889557
    0x403080603060408040605070c18141e0105040518100e0106050a03030518220f0b01170c030402010513060c140303090c0114040b031f0801090c2c01080102 68
    0x100040e545103400709200b485030703600c00341081c185420517000701d40640064104403644e000c0b000c408500740303d4042c4100700c0010000030109816002d189422001c11010b040726410078440d03008062a51800e42465054410540300045d590380d40007040b4058410b000170025490060a0440180030101e0b00301c0c101c0c2900402c002d200f0300b695075041c842d5402007440088c0002d4018000d04401c41903410042e00506030050a9007000000307401046880c131084104511925500c01512101d880c0ca8050480c00e0324003400c0c40b20071142c0700100040c80a034000c003001e40e002c0c00000040d085a0052007a5180c00404184c2d034102c2c0707030325900d0282409034040d0064070341017107aa4800400010010441c0e1040052001038600d50441000540d00c2c0c03107070796002900840013444003140740c21020340558413900204454030b50400f00150001c0b0b000d800342c1c2100f036040c2d04101041d004280d21200c081c0032188d1100442689044a09070f6140700d81c10540c43c0c1c1c210349110800096850b1054000d45103030031100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 481892032 1250 481890782 481890797
    0x20604060b1f0807020a020312120f040b06011b06020301170f061519051e1201050f060d08130b0a11061b0703020313030b1005030c0306150a0b030a02030403 69
    0x29010000d2000808240c20325202d61041855440c602c9082c201d030304440320340100c0c4c8084410790f00090a001c01d22241581c05030001c14100a007400140c903554000c0548040d1004a060541300c6501c2e20b80024101410302c1321170130641c0c0001c07685800034400c03150050402c42d10780d61030f418252040c440a81c0b00154510403582c400c8904da038045840707402070300031620000401400750b05010600c207401c0b200300840c0000020008103500d8001940e1200d1300d40d9103410408241d4842080100b01c40000489401c0c1c5c90f003010400f0010703000900c0c58010a0403117403000300c1595840c00310164811200720044002019100080501c800c00241000e8a410b455803000d40702200c1c2440c2d030301d040480c0c240c00781c0c902c0c0e0940b84a0550010b00100b02860081c13040d03d10b0b100c8560380e18010b51440e0f50007110801e07400f00400140c5c020460a80d405450120080e0a0054070500002c0d0344010240c440c4103a0381c4078000260596481343e5000c8000c025800b40182c4038030707000008a0003900100e4080d0007140d0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 481893282 1250 481892032 481892051
    0x706022d2814010f0e033a2412050604032115140117010e060d0c08160603020703051b2d0d09030312050c040f09020d0c0806060f0705031902060406 65
    0x88241c4444647d81c0c240385980d100300160b060305412195401c03c40e10400001d140b0601000d90048044c0b20901800c0d013640076801d032400c03004410141e800f1081840c6a02580c00c0041c2001c03078019041354141c51300600b00551001d0482c80000081c2d00d2010301490607408002c484402c3d99514125005070b4800c0300072441e91030066540035414084d280e00401260014003a50221003961604004041d207403c0d031400c0310b552088400007150700080860361000742010248034000d5440806490b5602d0190f08003800d556024042e4060400c0c04040c81c009018103c01c900000c010084e00a41d05001140041003492402c030300049044449251038081c840f040311040d40985160002c4030f40c5982c60b40101000c0d0000301c2e000304809041c4400d403000070040040d242c541c0104500103001400300c0103a94418502e803500858150724041c006101c1040200403290b960103050b10f0a04085111881d42c2d4440d524000342188181d004502ca040444c44074883c02c950300003100c500c118071900081011146 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 481894532 1250 481893282 481893311
    0xb06010225030b09010207022d03070605040620070603020d05130c0b0304141e060f0f0604092d02090a0504051e0a050706022d2814010f 60
    0x85200325040240765104040000415450056500c00381c6840010305007070260703000440d4004140c0078020354003200c00d2500e128510f400e1210102000403401081c0240c50b0180141c8940918401c1a040c891400701415246508010003e40b0345008004d844d6a1500d80802400a4010004042459140c0340014420640c1c020900d040140c015000d5000c00e0310b05521030483d81d000500858010105451407c0000400c0042c00003100c41103070100a1880c41c480c00f2840c2175401407a641101c2052401d02030b0810300444096048041610301160710440c908000801c3c260342458030240c0c00a40c4030140c00000050862143c8030f200b22203214503912840b40101c195142503138050560741207200010440c96542c0081400da80c50340e410307101d42030403036142d2500f443e0301d82c0d002c000503800c004000082a0070510f0403290710942d026031140220300707507004660b5609085100d603e14505201c0f030070309240150180044030550000701c82040e401c04091850281c914904d040c5003090401d03102000343c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 481895782 1250 481894532 481894573
    0x1e06050d1109100306021c0b01260702011e0b0109081c05090d02060307030f050106020d02060414030f130302010327020d08041226030601120b04020f070b060102 71
    0xd822052465100c8441c808110b000b180c040c100d9840410a031100100081180c00a4040700c00d8110502c3c0b90803125540d2401600c40350608907040003911224a83c92102840c2c2983c07044140707001580c0503a5441000782c0c010562040340c0c0b61640207201e11342d5003840c11a000700c003607040c0a0740e070080000e64800380c8540e80d40904502e100101c01d0a9400740d54140320344043c01003280010510802807206801244003640b041e1542c80000391100014020a00c2500406004000c3c6200820b6260030f640b100070b4444034003810060250883c1301c51000c111000304140e0343c102c440300b0b9140d952100a00301c0f0440c12003492004901103030603e6040319110340c600e1141c24034000340450b550b800808a44c00c0040d501d280080c01c5980000611003c18000c020620803000c0c540b05800383c80307410740c8250341e25244400710b840100c4104010070400c410303070341e012010307080480e91441c01041003241100080c020b802000c03005081c2800c00301b5503601b40114a40c01c940a6013080e02139500410308058107034040b2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 481897032 1250 481895782 481895809
    0xa0c0201021f1a040522080d060e0403030b060a020a290c03090601061e0f1e031e0207020102030a0c11060d06210c1503061706090d020f10050403121e0605 68
    0x208000a08164460603401c031b944c3e43c1e44501c501a18044d0b959180700200c40e0070b82c2240348002e50b4070042004160701441650140d10040303a10382e0900b0b21130b0f03200941e076500c01d541c008c0144003160312000031224603101c2c501e00d0a5a40c01c004507e480c26000a1200c0c1d04125181051849007500000e02503025080702e40004108043c0c1e0f070350b9900c0811090351004084440711003000400c00b048032074850106030540210369196030110b4841046117000c00c035810880480d4000c0d610412240b00142c1e00001107600c400c3e0323242003e600020341800c0c03d0004180e02c0702c000307400ca40e000814403082d1940d03603c030005a0310314000710848030550b0140307089403d0038004004c22104400b903043c003001c240440300804172000c500d004110b00d40c0b1102e4105003203800d140a000141e1000007405082ca0051003150000a040e00c0201456080411181d07503481d4858076000c10241d454001c00c00f0300d07204080e001e074848100c41090003029120381c00c5401040a94610207060791404401203000d1802800a032001e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 481898282 1250 481897032 481897051
    0xc011d031b060c0706030b0312090607020f030f010f0209121903050310050a0f0e060303070b040204090218130b10050105030a0203270102040602010b12030a0c0201021f1a0405 77
    0x42903007641105414145071220194407031814452500c41e00f0f01041281c02518190f030300480c1155500041c5490407544104000c402241840a12841c1e00e40f00c0a0781d650030b070100d030480c4800001801080c00e081a00d029004a5401c102000b9000410394000b40107600c000e440280404200c2c0511540b2400d40740218140c80c85050014030109101e40061908080800354450103640e94200080c41c92003030354130510390030003000004c100340c02d03401070810703403001d021b43c003440c60710040c0d56800342d040382d000304000e2040e41d03100c1f0b540041d9100c4142c1895009406407134803035182007034800c00d034075450f0407841101c2400500b8002441140c800310843c1c21103078103840e250b0440d1650030305c050180d00014952510305503a4a0081d29000343e15190440b1580d041300010703912030500400a094401c0c200110340600e1050700a1800c401d0b001080341d034414402c3c54005816045440101c2c282448413091660320740c815000d0b42c0140d0700640c080c55071485070300c3d0301101100007071003840283d850880f0490907 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481899532 1250 481898282 481898293
    0x1142a0a0915180e01030f0b07050c070e010801060e06030d050c2805060606090d030c050c09010e070915050702010f030f06091505030d0f080411040504081902150606070201110307050c011d03 84
    0xf42302d40f8103840e000385607418a14141595a0075503858103120b60310040ca4482c0c42720040040c06801e10400c80501280360350403e0714600741c804643d81d6501131082000308800003c20360f50b00ba40c14021903c000141c1400030b5104081d81d01c401c030807010141401c1d119405000d000c582d5924260381128401d03e070142260107129450340701911221852203060741d080c012000c800d5825543c0d0064180a07104003481d685050034040001007a2001d41d41240000d8800c42d40c0c82e017401604001a90300081d42440c24490000700d5810403009040c0310072039a01c080741002c20106820103250450102d0845020007148150744d034204041d03844038085d060501103050f060b09140c0e42d6115618640d80700b40104c0d90300007440f529601080854000b00e80c29160100f002c25114510b040c0909940e01d542050310080c0075070100d2001d42c40d04014083c150900c80c1d900029034808690040c40310030103019108085d242c80303190700d042540e10b518060b0040c5000494a0340503060800c021841c640c16800d0141c0140b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481900782 1250 481899532 481899563
    0x11010614010507020d0501060303020303180606180c090a03050d03110f09040e0f0604030302030f060d15021b01110d111303060c0c060504030201142a0a0915180e0103 73
    0x5810f5030000c841070f82c110340c2c1d00a000002c84d0f000d000344030003103229a004503520b113002d01030f140400581c0f104408454108000b070100c10356502c00c200c0d280b1200c034804900300c0e480b502840b4035103228005078180c000b21048400014000c0114402c01c6002464405000c1813940c0c4180c20042d20905602c800c03042000e00941400e400d003a07010b100c072000140d0458440007070700320501c2d00d00842107070201c0003e82c0020070860441a0000e0b219008036003070300ca07a2070303844440d40c0c2c003101601300280c5154086c0d0f000c100c40900d41903480d03902503c080743c040204081300e2070300300c20700da5079000c0381c0040c6503641800311801600c1c0c5200304a03201114941c400086081c00c0d80d43d03000c05811591a20800c20481c08240c4020402a20a050040e48241c00005011400000074900340d0300007403010700d82c01c41c2810340a403c4602402c40003104c65074200466a11010351400780c48044a03a00700300161840d5241000c00d1a8001c0b03120780319a4000e041401e4040e5840e44440107800090100800c07003054104180d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481902032 1250 481900782 481900787
    0x20c0a090f150f050f0105090319231e0a030909180611120106050c030405042004030b01061103070c14041d0a0201030b0a051c060917040302011101061401 68
    0x70703089006410004034030404001c10040b01070708180c11400b2442661901004185081c2c500b05800340c0003030801c14201151500003030b44403416007000ca80c84211105120007040310301d605944503500303000544010000800d940607501d4403001040301030003501c90f0030000002000a456005690315640311241c607810100243d0280c0040880340410050399510400003c81c0b900a007008010244901625080ca20043d2082134006030322280a202c410060744403640c8000c1300b04c406840702943c020403202c00d80c040342040b82460b090070340f0001d900480c001c01000701c0300802d00d04a030701c140c0d01d8103914100380d10780c56201d101703224006191746261003081082505141c00401c40c003100600000301003104100002140900c04210800c035042203e4110841d030b01845400140e21044d5410303034141d403d080c0070540b00039400e40300200c45c00a0014500400c4a140c101010055100c402d400043c400c8501003000f039042404102e0224441c0d017101250680144101c81c11220b559113040f5a1040c0c00005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481903282 1250 481902032 481902041
    0x305060402060c0724030c08013005030a0309020a172a04061e0b0f0315060d0e010b1302030702060a1e14040c08030403050705130207060c0c060606020c0a09 69
    0x11880b03180513145001400d051038010410311009444008850002401c800034121a40c845403281440784030801844209051146e1405503071042d600b0344003042c014803110011200324a40201280b000050440a880d8540c00c034101c1d1074403d959042d80c041e10f911051203400050452144241c0c480d044c2c0c3c10b0001640260f882c1080081205e2100c6140210042000c0d500320741c1200e21505488411b154184480c0c0c08403400a0041e92207180c14a441e8800810712440094005820565170f0300e0902000d6071031000315605500038103801c00c0703021036946115010780300b014a8684034509002040d0365200b25402102e22481050b03014082e5036665600c840000c0c07900301c0d000ba0092004903a8504000704512a40355103d0511640718000c4c40d1903e040c100041003600300b041540c0040c0010800180300003100b41c20f54108450b000d142d04940c0360004001d014022000d88000d003041218100c840e041103a50100300d02442d0140602c1d43c650100340d07a103440c80801d903034201d804501d003044041c40700d511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481904532 1250 481903282 481903297
    0xa0c0b070e1915020106080c090423010c080c03060306060d0c09020406230c070b03070311031509070801140f030a0615080115030f06050a150b0c1501030506040206 72
    0x602240e1244210007056010207408012864400d0040c824044802c0302c00c02c003d01d00210340b009004035820500391070b40300d0604c885601d009440c040007160800c903401942c8404103000000741702c1860303039099400d406400c00740c403136401144030080410baa10710321500320f0384603c070040c00401058560300244035000e40c51002c259403c484a40000c503440015000520007002c040da120b65180003100c49140c1050390000346401c41e46810405440d010b0400b0854504484011400d01e407656907603e811f0300649201c0c0240711981c4000801c02484080c259200c0030280f2040e10710301d8607070740d9000058032041c0080c056090300304030011441a4074a446422121a240042c0a66045450320340d40c40056680705008520642c0f0502000d1048001c00d2044003c101d64070550010361914688410500820708240581040d807184e002402d80311a54000254ae0401026104461940c820310482d01c0d422102c01e200c15400b40055054010340c8404981341641e41110282000c4e840d20741c02c1103a503500004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481905782 1250 481904532 481904537
    0x10c05191b02090603280302152505091012050711070b0d140708220b2e060305010f08011b21050702060609011d010b0a050c03041205120a0c0b07 64
    0x4006ca102c0c0c007240c1d140c07485030600c1303101c0d00144170300c1c0107400c02c00020b0554603840005030401c200700001c6a00440b82d09d8240c603420151101c003e004560500c545818079030800440c0c3c540010060703100045c1c020780c000000081080d915103501c00ca6205848241520450b4032080c004d0009450500040c80b20401c040d0002070a80398401c40e4880e841c00483d00078002c103e16208010000714042410030b034010401800d5864a002981d440403540009030941642540c0c1454440c414030a8100b044071189800c0c01200920b542d03000001c4c0989024080c2c43d10345000e0420020b04e40d81e050107031803003403d0404840b240244803103404590418040c000c0d04400600d04c9141c0c01c0404a600c2041c0c09480b1507400383c1500c0c80c28009004c02034006a0000700301c512804408001903090126560540c0d1440040f03940d50003070150304a0302030040d00040100b5000c00100061982c0b10070125840b4a4030407025507090f41c01d4000341c1c69403809050f0917400459652400b80c4006600403c20951100150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481907032 1250 481905782 481905793
    0x1501270504050108370f170318010609140c070201050403080703030207120e031906020c01020c0304031104020c060f0402061e03040620040b07050708010c05191b02090603 75
    0x240c0000d01a41c100381d115540682004144406004240752000042c290140011400e01401034114a10781107071000540544e50000c41c110410007110501d160410340481d100da26414020544c640d03292201520148a600e040400070301d43c6424094600c440c0b00980034144190b6440200310f640b981b102a040f0304000301048040000350004026000c401e01a81d001616102c0a281c4134000e80c4849122000380880590340c9659558002200d10942c0c0484000f40100840c0703143c140081d020715041c0e80c0b115400032030700c41190701c40003020303104072801100100d0b00ac1100c181400100d01c5000203065213030700a40c0008035403003803030031015410610181251703250842d01150306058540504944000c8000001030109021081c081c0f41640b600c0944107542001c02080c0ca440d86116600c07589001c4100402da0800b4010184a030380001c1440c0d070000c4c09221240300c402026540506100901448041d104505840c0719540322a0440d100100112180e54030303408000744030400801507a410b1284 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481908282 1250 481907032 481907039
    0x90d080c09120f01200904020d0905012d0c090e040c120807060f060f0519170a120302040f031106160b060f09060d020402090102071505030f150127 65
    0x8049514410b099604060b0094821035001d060a40b04000003004139001c400400103c0da0311302c1c0f403c5030f4991008440044c1e8072000205840050440c05038054007e510f4451411800d0030310002505007106551040c000d80c801c03155680d82110b007544a554001040740506101d00081c090a282e041030142e80e8806032166a14502e05401112041c101d0345050085200c504102d0030b0f02901ca800d40740d64409210440c100414921a211035106070792041891843c1d11224055020003c80034182d400403038404448044001581d40d520f20b08201d405003a0721141349a000c2c801d100395001e07a076442040c82017aa1541d21340183c144940c0701d450360f01840c00c005401510110001c4060454807451901420b0f107090410801c0382c05034005840e000c1d079882c07010000b41e6030354270200b00ba000364100d500603144c01000700100d1600d0065082800384484a480328070038581c00c20080c507c01e02e40c0d01c6c0014020303602c0000d060490728803d0f000d5404284c0800114a4400c07202c2c5070340000156444114203070541d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481909532 1250 481908282 481908289
    0xc010e0d061b09080a120311071502120c13030308070504170a0302210706050a1b0e040b100c0f210c050d050703090311030c0402030f0a0e06090d080c09 67
    0x803282d04a00c441c80091001441590022890001040104003400e041c2c4003940394248401c21507800c0c0c0c01010f9880e10350034059020b03201a00c04a54200c1901d62681c102202550029403102c415006e014101d000000c000d450500122000c081d01f0029540b0900e28683d001d682d006000740880007400750030b20000c100c041407004d440e12150411401001e00314828100a81800c50807441340300305086607101c00080920340811244070a85c0007000150701e54452550f440104128049801000031907403081e58500d0340000c426a10b903504440401ca800c19070740c00c1180500c0c07040010404901d800c0c129001044e1071960200b00c0500034441e14080245021607400c004420b4040400440c000000100034440c041140c001c9849050070014a0b01c11583c401800340c07401448010a0764181154054031510300384030b591031584014209640b43c0c2483e04c00051040da086030a41e19661030300000b489901d20010300a80510304207406088041101ca00072075407003c000b450041030340010003000c40b4545 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481910782 1250 481909532 481909541
    0x6020906091c020a090c020304120611040b0406080a02071205161e060e120306100c0f14011505150a0905060406020f1519020d09060509010f06050108090c010e0d06 72
    0xb002c00c0b90041d0080b000c0c410030054140070782101c03180e546000d060480503500003084800750340030350120541c071003002d140c00e5002d080d18124041c44260049000509110020007500c181e52440d01c3e0740310240e561110a07030881c0241407016296071a8917865088250141e401803551006051030103107a0300c030313944820642d0480454008040100b9003401c3c0207010b401c5c8102d6030362001d1030010f01508900301c80d0545450001429151040c0480e09101244030b000d015156042588169440380000342d83c20110060b2043d948190059420070b840e0000900a02c06c280080e00c2008000380409242d080b40359116410440040d811320042c441301203855610744000c2c2c001042640d008000104281c809103040071a0201c10804911015040c0b03c03050400440c0303058008102c00c40145c8075100c282c400d0001e409000c201600d25850001400560207040d000b00d1591185040103116495031580111001941120400c40c260480018a102588a0640c401d10341500405003244100c45849040448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481912032 1250 481910782 481910809
    0x20c0f0f0a150f110c010807020f01110a0e180a1509141e0f0a0c12091101030b0d02090609041a130309060c020d0308071b0f050c04180602090609 64
    0x70410715201c02207540e200000c3d0b01e408000e0300c2c14011180b0b40780d00316584d40c406040d045050101c070000080b00e45100700108086d612400000380310a0729080b40900c204c1e40301d900283c000502e003071030035146400d22410b00341006500c0d103150b00320b03a0b0321002090020901180312412200e00342c0d00000d42da2980d030103140b503800001c04a0755a81d0a10820184c01e84110418500d00003600c101000340c03102201e040142c1c048050342011810305a00c42d421554ad002800300381722030700c0c40c1540150500603030204902c0050400e8030100404000d000400041030942c10000303600c1041200091918100051400d401522070503400510000c0141900b2010000b1070700790040c44001040c090a2560100d0740e0350007001c017401c22110704504c2e500458a07020b140c032000f030240303d0101c5c0841c183d54271801d0220184881402c0300401c203d884d190100403980c0303015041c0c80b0380c070441c4100c0c1000c1c5054456011466071200c040300307680d031007a07607158041e401c62010941c1c012006e00100e409901c0b911501802c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481913282 1250 481912032 481912049
    0x90f030d060905180604060f1518150b070201030e07120f0b060d08030601050a020a080c030d0506030606210c0d0c091404020901060c080403020307030605180d020c0f0f0a 75
    0x10707070420b070b000c4040703d40041100f40c810101583e20500c42c1c0011a00c40d40198004d00c2c080b60440c5c8c0040040c0151403100b801c4020f25142a00008040c1350410540d10040d009034003d102c101000040580c46c08601c0c001d46908620412909006600135401000d407080ca04060b81d01141d5120300a040340740d100740c3c0595042001880007020004c07151034881d07101d00c0469429a20b0b4000751155440740c0001014241840030010f04611402c1c000c001002c0400e034000013050b0b03501981d80b40c05c2e45a400129201e116542004c020030164030340480d40380e102d00009051080080003039460614540807105510620b40544040400c1079112a008180c04074002c4460701c0c80e091900c3c2e108022940c006400e020080c1040b0280030040e61440c1010703044030807030310780310040f030740d807070405080310310031544001d5051007105030010410803a074200c075204501e0b04200c81240180300300c8582d11075200f5012400140c11005aa883c01c5c41c0c131280c201701042d0b01820000700c8e504c0c0b0b040441e0b56511341c0d401101d003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481914532 1250 481913282 481913291
    0x1519090b07031b09061704020f040e01020d0b040e030906031906060e0a0b0a140901121b0806010c030203030f100302101805040603020303121506130302090604060e0f090f030d 77
    0x14003201c0358885200f001000c1c60001059403800a0042c0035840c20310341d102d200c40042c07010900b5942c440540c606203c0008004200e0083e0844407903001b0b501904080e21240d061501182c52484c1c01e02c51010445210300c01385241c0440b01c02000070b03170340c070080020f441c85401d6002400c0044040c0b0560028105039140c0c000140c00c03c0c1c00700302d0102c40682c4103281e040400c21000e52600c1e4401c0c2181c0ca1000c201e0320061720b85412500580d01c02c07081e210302101440c43c2c4000310680060301c01c0d10341d03006070a43d02da000d26601ca15004682c0414421409405a0700401c0400c201407101e00c02c140d44201d4500c0f41d12382e01900c0e40d0008240303000308503890740003c103c070710f00e030b6160b0f030808146034000e20040760704215240c03840d404241c8a01414404101c4a64500005680c0d292030601c1d0050190000f409542c2d654011000d06500b000c0c1804180d028294a00000d036450a01d4032514003560a400329403142c6a550f00d4032400380c0030008298404d030340203421520b8807144003040540303250b1510a0000c41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481915782 1250 481914532 481914551
    0xc02120703023d0216110418030e04150e13061b121109010c030c0204090206040b030103140a210c15020901030b03030703050403260d06090c021519090b0703 69
    0x2c3c0d4622100c25071042c011301c10480707070184821000c0d20300382c0d195022044c4040302c22003d0004d00104101c880046a07060175201980405134801111070703151600726820848092414440c220320607080c0130300e0104036000744c0400da118106e0124000b4051045030027003000c0c07400421a14258002002000101c0d00c164050310042d2540d01594801d40c01c1d23180c12070304000b540000201040300d046409414850500481c00a64449402018889801500050752a60340f0600100550320900c01500c1384080300a850310f20300300c04141d840c0200d400c4600d0240744404502c8210048021341e255000b0310420f0000c100001e403829496400555a0004c01a1100400360024003030300e00004646201c2c0c1c008215070300010b074114044d6402c3d2600b00420b01c4010084117803034004c0c0a0390000c010f81008000c51580000001504140141c0c2c07882041440441d07040ca031705aa8910b0414411401e24402100085910102010140d03100d154035002040016140d00c400606000945902d00069152513500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481917032 1250 481915782 481915873
    0x20f030405150c0d0e12160b0c04061d0102030c06180c010903050304061421011d190509250e0f010f0e10170a02040b040c0212070302 59
    0x280c80742e00503010501c425141c0f1051000c0c044c820240700010403555044040b10040c02040b418004003800740b03085070756000f54030402441280c40c2c0c204607442c0300014000380ea0240010247c8084175150f803070700304900f040365095012106035100c826045100c01c4c81a040010f008014540c01800644141d200d5022003c0d589810140305004540c148480d80340104000365000048504071200342c9424010301c28076085c6088503128500d05910b400c001e88011003403030821051224100e40107500e800700722110b5480055030000044074800c6001c0c9440030300c8030491059401c09a800032240081e16410010a641e220045407112032100321302ea001001889a004d8a0307080c1c0e03800c0b8112800b2000c1c9985450310f200ba59465a0240150300004400400ca224180c01603810160004400c41143c030b540c44d0b5201960f8420001c8203a128608207882221a0704142c801c00026011036805804004c01d90000c0340d109034030140c002c03002c5115150f03005030032042c201c00c541c51814a41e2110803804501c2c4421 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481918282 1250 481917032 481917043
    0xd0b1509010605120a0f1e0e1b0d0f110a120c1d010603090816141b36010305060415050f06100908030c071e050609091306020f030405 59
    0x220003030000400240c14044104102c0b550b11810102011991050681000c00a460710030640601c04600c0c0c807613161003d1031f40d0008004200d01c1004c441a4203280090411084500407909811014090100c004100da8003c24070b4414080c0c05c0d011041070031748c004a411844d05520181c0d907416501c2080c41005084100480180030412900f08a0030000c80e0040040d041803141200349580e41c1ca66030104400002510550250514200d48007030a5040180d086a00043c41d01a54010001811002400a00b180030703100b902a0000c0100e42407a01184805c005405689102c1030481008000b007104220806002e144180082e1606042c185842c425a0302140c00d1300b182c03541028104800c0ba040ba1845980c0940100d0745848856036441c8280c03091101604001a40d00001071580d0f1074990000e03401c3c08482110803805025402c003844192510514001c85900080401925425103010b07021941c02010726102d000b02101d650703550720b040b640321842400840310080108428000103114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481919532 1250 481918282 481918289
    0x100f1e0c021617060a1505130603240b09190b010207180e06250302070f060501030b0105010e150f07030203041205010902090916050108130209040f0203240705090d0b150901 76
    0x4090011686c407408004000015024090003107906011003d5840d40c241c020311300a40d0400c0302e9440186140594040641c0b100125420300f6080c1444490903003890001c0520031011411010174a00f180d60050b405001c141ca180703811489203c1c3c020131400100410907010300c05801000820200380e40301c003410a00010b2010307040400d6966004040f040346c00070a14a801245030059072080c1e540b521400d00e1151104c0079190030f10f0040040300300b20b044e5032100d058030801d132034014424103843c00b04104d1400d808410041c0420501c5951884801000035045032482401504d007015140d1092000450201034151240c1e91124491300560070301001c00c68000110f0000f03041e0b00c400790220740310b4105417441418100042030740060b102030303860780401120b40c1d401170110748030b414a0704000c400175001c240309070321900505101c03880c2086481e9507650300e043c0800300b25074255a00d840070350300c80d001800360741c2e00020401e10300710018141c3c00580e0b2282c800c40041001c4450990113100d03804030142c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481920782 1250 481919532 481919551
    0x7030b090c0909040305040e09070f090b0303070209060d080d0c0315051c0305091512070203030907060f03020708030c030a0606021204050f040603080a02100f1e0c02161706 76
    0x9090150070070061044540b002e606507100d01c260349581c503017110580b00700e6004c0401c2d0641181482505000494020111584120051403103500c031400c18048540c0002c0e00c3da0305034010840c1000608003219901d506c81c07402031030b1200b402090b4607252a60707480300090342c00d513595414901d1402d0350144a0071440040380e12049100508000204091800160f441c1400b003441c150b16a0401d48200111200c240014109400c5861200f50040143c1c02044040030550f0f003250000b01c084d480001503a21420009004010f8540307819003e0302c50f0303001070215004040d000c001d00c03000300e8106001540515403801d00250b0b0791620f8000c4c4001c40b03015030000e200319004008608030022042083d0350907a201220040c00c0528940300040050001d6070005202d11000f080b103150054002c1900c04091482c48401e11071102300f00d0015040311880d641106422120034105051110554012202a41d603401191454038445034220f8507071441e0381c42003c400ca0f8200341c031201820140080c540040542 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481922032 1250 481920782 481920799
    0x110f0307080406030e010f06060504140d020d02150c0a030c150e2805060c031b0703020712080903060c090312040f1e150503240d060f1d0607030b 64
    0x1540c03210902d2140380702d0700e0704058445500360540700081d40070040180d1705140c10401c640c5c2d80c4401916503001442060780704441150300044c982002d1113031000050b070080900402200303503420030000d07079800812000481814001403d003500100840000d00d802a00c41c0d11390075074940f0349400e03201032242050181d141002a4120300d1359000640085081405400d288148001c41c84c5030014104000c0180240c403d80d02408900320300340c0002e500404104000144000d1003084c0440e052041100047c0181e00c040820040a600c5c1c100308103240d0b1054a0107850091171600003442e095041d2210f241c8000000f8690426240410018441c0b4803001d448600346882c02000e40401603662240d28015828120301c0d090704081915810081c111592150b00381a01c1b0440080243c0c000b103515043c0910b05c90b0103035244203180341d20941c41c2c100080070110403004c55620127002c1d00701c05800080c040c0e11750100c0d83d003990714990b8202c11488000d00038042450086e0000302524800c0c500a400b80489 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481923282 1250 481922032 481922047
    0x30c09060c2517151617041101020d0c0f030804020a1805060103051006090302061b10060501030b09040b070c0212030c0f19080d1a0a170106060518150904050403110f03 74
    0x2204156544103000851004032808440802d43d42512110200092108000204401c008882c8c000400395034003a400c40f290080010810f0b6480c401c03c1c0030144c11103010b030f8150000288100e40c150360061010340201070280c0d43d02800401c1d501c044041220700c0d504c170b0003003001c40d503414420154454240c14070354a40720314081003e441c0b24401d00010b8000c200016801011814a86100e90382e446c58034121003011040c401c03040014442c0d4042c03140002c0c14014000c8a624000204502a42e00444084030310f46403220180c40204108504a81140c00c00100762140cae1814800f900305055400040c0540d4017032031001034109889001c50499020064503076902048002d020344688400c40c40001500b007044942c0781190554110004d58850900d507000b083c100844e603201800074051074000d1080ca40c41d140c0582c1c55001d00c4a5480c012a00c10461000920381a0b110400d10440d072801325182110718000304099800860b4158042503481101c440485410040c0801d5190312201071401c0c07415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481924532 1250 481923282 481923313
    0x5040606080405060f01052d030703030c110301050403051c0e1911060408060f0903090405040f0615080606100e040f0203240d02012f21030c09060c2517 67
    0x6860b400e023036141050b40c030343c079030710308202000210031000f41200c5031165240b0303008120303440600c4110345800013100440c07401e080500809016650545821741003a85000d030001c0c81c280700380c12488805441d05400c116500c002c0c89410b8030b50380039400303100c50010360741000440b0800828443c0e0050b001000304021120000c02d1141d0007004034208080b01e61104480e141c9503004052545520502e000144810444011074601c070007071052100703021904800ba80ea420042081c4030345100307508180f0015025241400e0004510585801e044e80c101701e814022a0880304c9485000511550000904c052280500820400c1280f000380e01d00040c0c4144001c03401a00350508000d062140c003500d80f1500340041c0394180d03003044000320310000c010076401d50030b59107241070700b10000012541c1103030030346138030108041741d20a600c2d40018628150250051140c0c0d40d02c10300c7d0420a41c01b9106032000003000c00c02041400e5a20503005201c110700b80141460f00002031030f1001700a0380f002004824410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481925782 1250 481924532 481924549
    0xa0803030108160e010915030b10090f0203060307052815030e0d020a081b0607030912022d07051507051605010e0f040b1909050106140403080d0605040606080405060f0105 75
    0x48040001045405152031a1020800320b88c00081c9081d89000402002c2243c00854800311240c041060240d4800910020b080340300503521250140c0054605200d2406c5c690708141400031142c4145007881070f44404001301ca41c05030450984d9590000f55018400d50502a800c05082c04401902c504c11a10001950f110141c0f9030083c01d0410200c0c060b15079151500c484c1c0803440c1c4c5c407800d0300c007a840d00c03401c01070080c03100b0001100c0f16210381c0c101810342c51001070307080100d4910700c40f140312000e0100d4451080080b220b42c4c0c00c174280326200010403140c031342d80102c015203e401c1c19690313122500362074601c1c18001504400b140070606e200301000203a07072000c8500f403c6507094030008001003088012402501842d403440ba0003028924204824510010012040f01e40818007001a079032501011140b1549000026014010501c024004901040d00412108241c001c000904680c5c40000c00c050703582d56030000b030104000d03404100034402c05120065000003441340080c601e40c14880000c3d03401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481927032 1250 481925782 481925789
    0x50c030a0c020705042c030306060417010209191d220c0b1b01050109200c010e0601030b04050d020703020102071701021b03090a1202060304120c020a0803030108160e01 74
    0x2a1100a14200580280080f0004e80000340c414400400324030703d04800920420403008a5106010740402410300100c1070b21f015002c01801146031500d404600000500c0200303410340195400c00c200a0707955500300b480800c031702d00d951114030b02c07610309030402080c2c00395000822044102d42d01007002d40011015450307075804000246640d100010b0502700412101070b00450202c00c000600800e595100450400d05d03003080780c000744031982e21116803905681c5a20310410481c0b01e031078629000300084c203019141c9400b181000007207002c03800b84800c0c13512a003a0700c03d560604170700003440140071040c007140e0782540803400201050707485e55000035a110b03102d20803035441c0c040701984141062420b40442d080c00342c80c501d41410600e0b02150554580d0300190b00180700d03508040000410b00d000c981c16805954004005608540c0d82d51580183ca03001081d1007420000741110727407070040c1d940c1c550702c201400400000f1a00ca41c10410324a2a150014200c035036001d00e000c10130031414180d8060103064 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481928282 1250 481927032 481927051
    0x15070504050d2301111e070f02041d060a020a090e1512010b03010237080f060a08060f011a040305060a11040305030a0206070905060301030b041202251404050c03 71
    0x5191120f5000900c200c09482c26555420505594000c4151030040c00c0e100f070007100606520b44051040b04060710030030b080101210002409800507181c41e50000882501c409003d12050020301501c90502108a848201159001c1143e00d42c9540c8148200007508480803942210300384414082c2540941501c0c092103489541442c4019101c00e411055848002500039906c80500700c4082012022141c032000f40742110344415079201440b003001c00e88919503919a0407103516900030241c3d075a41e0044c64a50001501c1c28002400c040401030b00744107003d242d102001c0365040c00a07001d81000259180c02c0c1201c4180300501c045031000c10304a400031012000040c040703030704c040f40e52aa40243c4d84094203c2c0408121400f01c1034010070824413031341c560703900c43c100316803a5010087e140c0807e010141c244050140010000f488904100d4940c881900490341e10007400844103550307011003003049002d031642c20f41c208001102d80260a52079801220148102d25295081c0026030100030083c5c401c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481929532 1250 481928282 481928303
    0x10b030105061e090415090f060e072724090b0f070524070201053304060905010906050909010903021507090801060306050910061503020d110c15070504050d 69
    0x140d80702e03500c2110101c00014105100c44044000405824080da20521100b10b007031280300f01842020740f08a500f91360740c0b60000d0900c1cbc5c03110743c0c0480b0b01045202001410720701c1c0030641d80c8002c4164403040001c041c0008907896402103824a686410800341d01c000c20300c44128811f00007492144141e40549101904003512403010b814032603c1c1401d00c0081b40346030f101c60400841c00400404a15106881030340003804030743c4605020f40d0f80b203070308607601c001100b00c141c00320724080829059001501c803000300041105a12400c08408403002a88050a01c03543d80c801000282056240b41d644141c1042c0204003800c3d2544000e502c81418800c0140c6d00302e03000d800038107100d001d41540d40103801e07200006c1100544900d0a50028074080c0c401400720320401058101c003501038040c075400c4d60740408900a81d803e4840059019400c00b54001092503224030f40c12403039040500151101c002d0000c0140f8902d50603450840c904207018150750104902080240b02c2030b1548180f001215920035203400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481930782 1250 481929532 481929577
    0x6030b0a050924041406030f062a28091e09020c0f0a0606050a24050a092c1b04050603040312020a0314010807030506220b0a0c08010b03010506 63
    0x1042c0200e44502164401e14046485d0080300c101035460780700c0d01e410340858a020341540c9615070f540c10101c8201400142114681c0c0000015a160400d1180005281c1d8144401c040e442c20219103035002c1303880702000440c80f5184a9030701c112008014102e04d42c40854004034042d030302c00314110034010041c00d40c2d000146076001c4034042041805e415445010380300c070250b0615008000d044248240e0340b054036040c0c0d0104001c4808a100d906c5ca407043d01c21000100e5007032905603203035004020848288407100303400049801d054803001c07440b80c40344103d02a104008441014501c807000e0502d240548000a41024444a10f400c65040d510120f03072881d202d5450746811992a00c0362828981e0303540c004030380160341c0b58244d005850980b10000540700c83d6a00c8403005a9100118880a489030380001e000c80e00140c90849001a0740032050000d100ea4405030b20fa40c80010801c0e6822a80e060381c0c0c4007145000382c1e104100b140505603a84065140d945800002041405000d8000310242481c60380038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481932032 1250 481930782 481930831
    0x60e060d0b0f13050a15060c1b081509160b0706050a021b0a020a08160905090a020a0e15040b0d030807090e010b09040b03010501050901030f08070c0e0106030b0a0509 73
    0xb00c140001072080d0844003400b64050060442510a01d11071401c140c00c1c6d080700b48203080b1031400e44030582c1e11110640c48649869050100d11400044011011030300820300b00f00a0162040d407100c5110303400541d00f48000b1207807401405114550620501c1c0c0420f0040460301d200f1a020305810034400b0407992549030411009220754010b2134400001e031043c030022001c0100c0c6121140340201c1c1c40c0728030656511030b8142c643c1d80811600045d806c1f12a42440328440c550300c41c9402076218400c03115144401c0d4082005504a03401c04041c2210a030304115480d074240019940d0f0040036907081c4075004d99500450a0002d01110082c148504800081c00b80d610500c105401801020b8401c030b140d5a44159a099552100f50854001c5040c000501800e007814094a4101c3d90040d207203007080da103940c4800380340004000003114055010054000428a5000d06a02602000f50028910752502a018085421039082140500f0a0b00801c110a50341c0f0300c0902d0740304d215020214026070607007240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481933282 1250 481932032 481932049
    0x6080403050c100b090906010e1603020d020c0307051c0804200a090b0102010b01090f03030e0607080c1b01110d050a0207090203040501060617040b07200105070216060e060d0b 77
    0x1000d0510803010b03031003040348054000c0784c0244415100c4425503203a07848004d0f1180e009000c0e440503204c2143c0803c00c00002c1d00404d11255105140050420548036036a2050340d00c142c880400c554404140300301448024450440318030030000c840c804242d0440da01604d2030400034002341540281a464410805803203219161422005208080203a202d564460045c51600d505900540c41c0c181110304550180c03040d101600e10101120b14200c2c995035080303407000303402c804442d000082400980e0000d040c09002e03040d0710304203001619011103114200210f1015001c2c2c00b604000464251110360403011404001d00740386480d0255540701403040580c5081126400442c40e28400000c20003405010740c8032005a464942d01c500410312b03003144400201d80c081d80c028001c0303118600411400d03806910412214407921a0410001020040888c2150021030741c00c80981c00c040500702c1c2c42c0002c03d9158000e00618204013407084101004500503000ba0f20407070781607990b00c480d880300c150364441e00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481934532 1250 481933282 481933297
    0x340b0a1d06070306060810030515060105091201060305010507051207110304170114070207051309030c080703020d080a05151c0b10030c050604050105070f1407090c1d0a0608040305 79
    0x456101d81850740e40240140014807580000428100100344041d2041e00044c0489400c1401000e035110389202110070400003401050521100f0401d402941d2220307180074480c4540d05000180103861414101e0968400514540c2007100c20452401c4d0750b0000c001d1160880003a282041112047c49001480d40c89a45c10895400001200f81e0341c440e14150400c0138038615a201400d101d0300c4410003071f41d075030b005030080990004130769081c455030a05a41c0303d0f40f8500e000f841d200120200d507880d000c80c141d000050580c01601702000340910141c12511403a000025244100250315102e44100c0d201c3c058075402e544501140c89549400441c0d54440d81c54132604804003503402d04084450011040544c4000c80c0c0000e5038040024281c03802500f510304941040c0c4416240c803c0e03a9542400494800008854103503410704140c0790003000300701c0c0101404100c10005491407000c035000d00a4046d01c2000703c0100c890040c00c45540d2242c0042c9800c882c90f41c248008251161714056a0901903602e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481935782 1250 481934532 481934591
    0x200306010608180705190f1a0a081b0a0f02061305060610030e0d03150602031e090409050a1113060506040e101a04090f14041b050303340b0a 62
    0x308404410400706d1411022160800022140c4580e500108206455840160100c6903008d0206480c00c50180e282990301c500200724400a0a03620380509190b5001515540c000a4020314404402c45d0100900d6070040c0b48040449001d840c42e075200b44da03500380145002c0c0985074502803861460f000b5040398610b5081e50060b501400d00c400c20043c0200300707580240070601e240f02c00c0004c002c0d00200844078449144110751305450083c48410041c0e50041c0a01d03604240d03503643ea5030100d0000c1c0b12007509203104000803442035030b291040050700b1245030a40c1d2401490942c0802156883e00c08480440706040050030884c1e8444010300e54010341507200e48110300c20611f8880300c1810320b50040080d1014150204100101103c1c490211903100450305c071025240f0b401f00c0d02041b8079800c00e8500c030125010341c510207615080808c1c103580000079118464580045000442c259101e401c0424000410183d0030310402c68845000f12140506043d00580c0c1c2d510003201ea411007222079120042480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481937032 1250 481935782 481935799
    0x10809100f0b0a153009080d0e010c03050603030a0e090c04050a03030306180203070e010e0a15030e0c0105070c06050d090206070f06050601090b0a0513080a200306010608180705 78
    0xc000e541c40490001c001c60001a0100201d0320102c600d005188000d188590003840c0f0134100201711100a2040810075156048140b0007110107802501500d00b840c0900400031620052140b40581582d83c00780041d4403d0300207000750042c4a030302c0036450341c03080d400300d4200903a9118109080110b100e5504025049090305402100307040d01a081102283d40c141c00c403400010341d8810b100201d001c1642c8020020f404100d00381c00c0366104000c5a2580207000f03050b06d00c4503a6403940c88601596005452002c40d8a40359288040d410030302c0f00303508901082c240203240070007960341c445d25807421340109818001c0104c2c89071100310072075002c1c04400e0f602400d1f0366662003060a240709201c0b1080300803a82503040000281d000d51040d2205411188401c08030350074044c02c03100941d1950032449154504a014140015203000b08002c4150054000c1c42c01800000683c2140403910300800036040c043e03801000104000c952103801c05611051a10007110481340504080341810341c40e0307120907403000c2d82 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481938282 1250 481937032 481937039
    0xc130b0304030e0103020909070e1f02151b160c081006031103010b13270809010801060905012c0d031e03090503070305071403030f01060905010809100f0b0a 69
    0x16200460040340651603070340700900c01c440110141d01c54010095040744c01e580118030041e00805e40407400100041002841c010483d01c00c143c42640402040c0043e4400d1200154041d10441c03a00c0c0c020802000050143c004888544c0301c80c41070090f9042100a510081c3c020b1010142d201c002030b003808020b40c2d0070080111010f00c007a0202d40030959008120f82250003c41c6814881c80e1891080980b10b140d000c0c0250346210000c02c1600c121701854a040b04940b1705500f000311502e44150700c10440c80743c88034000000188401d205030000ba00780044000d007804660380003200380f2003500721040c420781c0d94a1134400104504030341c0481c0541000c17441501c0c0c800c144e00b1000051000342d040900500404407140d0441c00c1d07407c0708502400a4008003ca100428070404c01011100e004800b100c00203007410000915590046914405c1880d0700c0d4010f02407954031400480c010700b002d1130031880c2d508140701210340b00d48000d490300180135524800e185400c2e40542000b02c01d00c000600003c00c1e01e80c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481939532 1250 481938282 481938299
    0x60c0301050f03010e0a1220060906130b0c03040303020408031813020a090e2508060405060f03031909050a09061502150c1c05070e0103050108030406170c13 69
    0x400e0103194800e070420b0004080d607041c14458480184440d00c002c0806010381d80742c189450300101585005c0146001105102d05081c4040015014071200200401d182000565085c048050440360b82c42d2f0804064001050301c0c0c164090300884d54403101c660783e0712a898180c00074032403035006e40c0c0c2500000c0f4400140c01040c00c68135000303203416918031058222968040041344151141400481c80c1c140b02884411101c042c3e080d4040001d95902c04001d00c01d220650521281b08400800995144208610b40c00d19000f000c1d00800300f50341d40c14600d00c031000000d48a0240b41032920300d40d1112600d002d16540301e101000000c09020b401040b1858451024801038116402a652018101c0c008189411310004650f2030300b20001c2c204c2a41c80d26117091003107143d40310700d002080710b401e0f5805161120166101b420b00402040d2500689030a45070000340c01d40300140c1c040c00c1c00e60002d0204100e03854020940013050340b1200341841540c0c0d1205208003403801082c20103425619a03040202c0d0015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481940782 1250 481939532 481939537
    0x31009030c1502310504021c1404030c02040216021e090c0307090605070f050102042c0103050d03020a1b030c03120203060a05010e031509060613020702090601080711060c 75
    0x5010304522482610321108010582c41074001590113526600380042810501410750100d1200240090b00c0040d6613030006400da803c40c6081401181a035018650407040074480d42c004405c02aa03954564a4030382c030040c0501c01e640002a000340d0300022071400c0c5c1024280e000307110a90003030003004000800340c0b00101d007080440341107004409403404203024030a88410b83e80704080b50360b903021000d0f08105084038107800000c400c83c2d0b10903100b21198000b820a00281000d401c00348006418180700750b03520f00c4114032200580c0307800c126880c0140003040c0049180c0c1400e06407810f01503920390100d80101c441da407215a0300001d007121040034208065000c442e0001740c600035138407032004085182482d800c070710064880300c1e0b01510115080003a940603070b4000034207600003003c1d58410100cc000a496090381261885d10a400c048104022441d11140d0a604241000b80441c01c0580d035501088800c9400b4000701d06204d604800074040b641b00d418908103614003402550002c0c141801c0b071150b0754 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481942032 1250 481940782 481940807
    0x30705030c0909240105121f08060a09020f100c02060c030c010608150708090c01030939080102070b010902030c0906070c050102070617071107080313051320030603100903 75
    0x158451130465004d40c400c005039615000d09402c2d20841c0e44034104201c03000041d0000a040c0c0d050309810005c1e40d14018011180314042b01440404c0400b8140304102c030401c0050100da10400c00c040520701429030102d030744140c4a42c15a00c86d5901d41000165034a540100400c0755800d41c280744002c00c540348046030b100340000015140f0b006544072214191800e2200b112100825030015400035a2507109802c55013016000e9000700b48004050040701d1498510440f23214001c0403a240100c1080d100558100c0051000000031030031b01e4819624221040010b12403040c150f0380101c02700d02e1420100d800c49450200080015941d45014509070700f40c50150f108482c003600415100051003806071540e107680e83c54907101312015665587c802c0d1820400128254428400c002c0c0100380c44c503040004041c401130304c5074000744036440c20003000f03a0411414840e138440c03414191140803941c120201140962011240700d6201c0e1350b500042858032a0580c4110070007400c0c03c0028092581003601d0039542c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481943282 1250 481942032 481942081
    0xf080102040905090d0f05090103140c280906030905070f030b40060b060309030c010e120f0a1b06020c011407080a0908070221070603060605030705030c0909 69
    0xf07a5682c03218036440710403400300040812010364001004a2083e0f0041403001c0050500151309545250000303100c650072a20b01c21050f01c00581090045400090b01104001ca13002c021190a01e02c60010700c0c0c40e4043c490300f824981c80b0b400390401c001e800d0008901a14000c03014146c06907603030a01601c564002e40e00000c550034035a04415001e00d00c60420092100190318800340c2c1c6084042411100c002b008081c5c071195500c0031a11381e2030740d50038020b60140030114000c540301c00140300f00380d003115480c0112090036845803d11584060040703003540c5c08450340c100440d844a00707003902030b06c8100090484040b4050082450b47c00c12946a02410300d8800a600800c500840c2c141c40c0212142c0035070b1a0710220301d5600c00280100c2054211403c001d00c02c50405081c02003d6010504c822003425010348680c813a580385d104148000c014031001805145001d20000b032a01d44c018140344000350070340080020020024401d2a52a030448140001c0548003a03000d02c3c0404082a60f000e407845203108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481944532 1250 481943282 481943291
    0x1a0c01020715150b0307090b0315040606080603011a0a12150207050a110d150e0316060b04150f031e050a0f111203030a02091206010e04031727070f0801020409 70
    0x3039181440c0b080d45d06c124850385a200c5800c1c1044081c0783c0c2e5030001006403445800729910300c901c1d520f40d401a007004042580740e40c681402c181003051b080d1100c046801c1c0c00704802414111003503665600003001c64000c00408401e0348034900f845110266072000c03070079060b400000c0075004c0020002e411001c07140070322800c1d0040b40c1013200304a41c0000168002e0300d100c0032074802a5081c013503944118540c00e07080c003c41c0d282c11122850a501e40012100507907540d69552a102c4c03150400e40030b0717a070851a200c050082d505080041e0340c0800f80b034034000907003c40000709c054041c00e00c411000755030300d40d0401c0865500640310301d0804588010500c0480d0020080311800b04d03542080544265000100b4010b5401d5540c2d00c03000d43d00070340042402c250b00618a140e8520707102c00034444a8040d10782480d40c1d03501e5241c1414083c0a140c07101e001c080c4410004c1c002c1101940600a19510183e44c80c0702d00c1610310b17600f2403442c0ca003034920f40200d601c44001c1c080c0010704010540c010f000303c0785200310511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481945782 1250 481944532 481944539
    0xa060f020d05090f041505030d0504031e0302030307121503120f2f120c030c010b01020c09180703080a0e010806120604120306120804080609071a0c0102071515 70
    0x41e07650140090007500202000c4400044d481d00b07030801c07281d1420840d040c6030081d075039500082c50422a0004040462000a000e1092101001f160355501c8400c401d0f607110766485650081d580e01c40140303900108040d11100c4184824280c01c41c3ea440130200a074681480c1d11390408010450b00c41c516100820382e004201c00d0f07485d000341c48200580384e159900c1200b06144c0315800e202c092044518101078054060018407100518000c1c001052030000119180e0322890545401c50b114019424190344c44641c01c65010f5694610b850b500000e070707003116690910980103191805ca81d40c2c000608114010680300b40781a846400401070084c242c2e034055050300c8035400c0c080940b8883d00005040c2d00004001800700f050325241d00f00d0b0505074540080c1c01175403586480c2000c00000411600481c00150401503a00c0401c800e54001c0c400307134007928400e40380408030030351084a0030003e0b040410110360442502400e505480000d904541c04c01d00201c030407104500100000400c40d00350360107144020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481947032 1250 481945782 481945787
    0x4031707090e0a09110d050a0c0807030b04020f0315041b141302090a0807091b03020c07090e150906060319050d0507060f180201080105100522050a060f020d 69
    0x200115400c1c0003901c18603071282010385001e88113000080d00c4c0c44519510b00c004944418008140035806040648240095407404288103102680540310680c429034040c0040f44502c001140c01036811101076100795481404282404000b200e01c003254000c0c08200018044405440803081848400340075510b601d4100c4940c800030840002500100701d00074140d40c00b031295006007582034000700404100395813803400300d00e40f10180d04078203003440e2101440c2280380360507840c2d001030200c1803c0c10340c1088008180b040c1d803008580b09480026031285040c030310741c040c00d00041200341d91701c1c540c001007403900c040e50355510081660090302038480c180f5196a40c0b03500340c0004c0107841e17004002c2c200f400301407a0300300c3c0e01c3d40101c441501c103103a031510710313020040d818030861408048002ca040c4258413940005040a0310592042d80508a201002c0089030b50100403111200555480c200d007094034101c0c2c04403480450b8103c240c20080381980131407001c1c0c2000e03a1100c0f410a503800c8070388405000804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481948282 1250 481947032 481947047
    0x2124071407060203070309051c1b111311040b13060311070b07120c020d0801060e010207030f2102030c060a0605010905241b0f0304030b0105090c0d0504031707 70
    0x10346050140d040061400d8005540020262402043c20502a101c46082c0503546030b00500850780310030702050064102c40318100d400e03986429008824070701d8440002d211507100465100b951149030604601441e640700e01c10300640c6070342c0551219240c0581c582c00780e01040c11441c040100907000205588a03010f6094040100440b03c0e080040c940c1d620842000090949020704c2031a00b42360361707904c666106a900e101001d40c000e085010950201404666042e00440d081013104540d0000340d03600014108110ba501659000c0b20800a041502074840e000c000c0144400c400c002500c050f59000020300554000ca00941d0031549480740c14508503405446094013151450760100002d10308602c44942e007800c02d00400030881101c254003c0340364804c1212107915444c201c441d0741400c90170880101d0201c1030320b0080d446c15042d51a034000d40d0505206080c401d4843c1400101044910b40544d01c40701ca8011041c0300718141854007800850900c58641c400d45a1040041e119900c140070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481949532 1250 481948282 481948307
    0xc1c0e090a0c0905220f0605010e3c0d0f1b030506040602030c1201091b03090512090a0e07080f0a090308041202030c0a050601050405010b1305212407 66
    0x7100c10300e030340c40c140c21720108807488400d880c0c0f03200321071342c0e094404c4441e402400409844541c0004041b82018005007000a0a600d802d0046024164185800a500c01680c019601c99039601c21107500303040300c0760007034500c00d002950440c0340e2400c2c3c901000b42c117a40780410544103c0c901d42e2b04018550300c0b00390782da15500c0003615031351291002c1303400304406600071501b10301780707050141c50000300b890030b82d11a01081c0d01c0303e48c0d960b50b100c0c400e15024100c22012071050306503140038030143d01682c513181c0c5c0e02e407403000009000c1c090000b80c0160540e99502981c00038841e0010301d80c0b2610b4020b4001d4240e10081312401141c840810005019580c03c2c46849200c1d50305440f41f000b15141c6490710f1000f00c005500841c2940f10402a09840300c00411a80100c648a000140346560402c07050105032103041c2e1003070419400612946c1c201c02d050040c1038080c3c0304203540c1c0100c81c0c031b200c0d6802d07020520526985900d6004d816041400488000c6500c0e0346100303001501c090a860700501107400c4c3d01d0008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481950782 1250 481949532 481949537
    0xa171509120a0302071e0b0114010509010e15041205010c080a230601140403080315030f06071815050304022412040c0306050906180d050406050c1c0e090a0c 69
    0x21101041c10b001340c4c060074481d400b803888000709003038010790082592409103064a044003200f004110100d0b6405038030124131428640241000c4103d40064110010494411b00c80c01034052440ca04800c074109030b07001044140d2146080e0034850600714002d0005103044000640c0200000712900f03414000d00c0c454018071400d901035510300908144840c000906040c0c100700c000c03403503d0220300c3e2081c06000514040c41c29150f0320705000c2421640004100e445e24007c0c3c04c01d98400b0403070440491130550104060500081d0400500c40c108048007560700b18500d000154910700c03203041d60110280d0300c070350700c04e84030000d0500303400301090000468041000a508020800c014090404405694103d4410b00c4031413a01510380c0d44101c150f41080340c40042e281d101008100c00301e64103131840141c0d0031100c170103400040d01c00c2000500e41e1250b4003510703060080014450044420030080c45010340c68030500307994030031031900c8000c0c01880c02c1c03003142e0300c51000c1d030000c14510346291040b489e9809454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481952032 1250 481950782 481950787
    0x20708070c15091503020c0f010c020309190f0e04030e090406050108060f10150c06020a0f1e050714030c0111030106020706020304140d050307050a030305060405130b040803060a17150912 82
    0x880195004440d0747c0560f00448001c808008801d004402e131100303050700519216403c080c14440031121000060808450821003080b05040d51100781c019500341004101c81e0340d840341400d842d029203041c8003c0d00719803410204404e0103d00d5000034140e40c144804c1d00d02540b203500758000503440c1507414134041d40c9149001c01840c2500d00b6040700707002443c2000320010140c2d071901703801c03604240001c60205540b43d42c607141c95584100c2c000120000746140b0880e616000200030443e01a104000b0141d1390300341d40c0c40400c0401003040c0c4031071411000091103c00785034036943ca4660400e10880000d0710440307170041605030001c0203803003d54580034011408084803100300200076158030001c1d00c541c0002c002c1030700810001e20104060b14040c0d2000710b03071400e00e1820322044030401070200420387c5200f401c00c8001207150b0f00040e0465040444d46450382c03220701c00614400d101c2c1c0d02c44100d40c0d40f2420300584040000ca0200b282c10042000c107080d84e6568100c4039161a091604c80c0b140343c104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481953282 1250 481952032 481952069
    0x1b010c020d0f0e03030403060e0c01050c0304090c05091e120d0e06070303060314032107020c12010b0d050a021c12030e1e0f01050907121401020708070c1509 69
    0x2410020b0b407000c0707640c40c0162240c404003000c40d0541c4d20980080c0c41d03030758680040b60302c000c80030880c1510a403020f10b8260724000119105c99100d01550090902003a101c85a50700c81920503401d80f544c41d44014180e609903070700c8100a006201404078902d0240b913210385101003240010800c442422240d40f1411710000d906001c002d15a405110214141660f6602c08000700750440403013a03100761090001d40d076403160880c0140d898030010008880d801d85c00301c00c001c0119400725071082d07101b0702a2010700860a0003500280036007850445c0540005281c00f004042c80000075200410303034002e5414000b2140d003041014101024600064200d00090040c690258803da00c0004010100d0003619429505218002112000501440010350113a040304200c03072000c1c40fa064006d26598000c02d6020710302510b1800806807030002904000413580340c070b5a40b98083d0122400150320882665840f074961915810000c094006e20200b104c4040c00b401c0f147d03000351100d2040c0d43c580b54004030081603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481954532 1250 481953282 481953287
    0x10b0f1c080306040e0102070506090601090507090b130509161b020f190905070e1207060e04021b060703321504241d060a1415030405031b010c020d 65
    0x1d041d080d0003640d10441700040280a01c0600103031840f5001030421828a000a10b28000c0103030400c1b01641d24040500464039003110306d8000b166201190640c859008041c601a1062107601075508a85a44100b1440c101400c005980b42c09054660f10643c1508074051120340c000340e00029003000a8540400c03c0d481e1980400c03a960103e0000c2a003100d803030304280c6007607845c207680000108010700000a46890700300220144940b0002c020804a071400c0002468500c070542101d008642c005441002543d00010004125041c44121840b50502c0d4038010000c14031480d003654881c02c170203460700321032072a03202e00f614043c0d0700001c9403a181c64452040c0001c0d0101c104090340a503880540c40b121034091280080045281c1c012581600d2610005001001d4042c1c0703608030203d81c0e40100b01560351481c1c040350a482ea8100d0500c5420700d1040411402410b1804a40742040302002704010408000010440801083d140c2e6031a0007800c01413500380e9440c4400080540c10601110300c0c4540b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481955782 1250 481954532 481954537
    0x507091b020f032a160e0a0203040f1104020f03150a0f0e04150912020606100c030801170c0307030c050a060e2d060d0902040e0309130e1608010b0f1c08 67
    0x260b0340c2400d801d8018480001c2031505c0030318441ca100c2070300080810011002504c0c111a1f00079400d03034040d41340d8078090b6180842c1018400000f040756211030700344c50f403640383e0781e0542d400640038821999680c10900f48840c02c3c000d8000500d41704010310100404c0303070800d0590680447e245001c102c0c0b243e854590b03402051042031007424100c1c03075980d0200c10224402d09414502d643d103580290896050500a00c555500c54849590a00c0324120380766000a52110301c040c1100d00e42c44404049514680e201824114250811a8144a01c007004000d10a03461085800c840c03084480310021f07681e50300151032007a203003000c85174032600298914500201000610210a0030035034040c0c1d42aa40d180041e101e130f08180c83c0410015610801c00c011403e00c4d1042c10307500c03417641c001581000c400c0030014801030300b540c00c0740050f0764994000e090801c804020b8a40e107104500c580e800302a844603000b0f4000d000c1c0700240c03403040381c410030030301d480d8241003410041a411100c0060481c207140e03120400b242c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481957032 1250 481955782 481955827
    0xf03170724050601120b1822030f11061b0d0e010f09050106050a0b2505060708040308060a1a07020d06020d02071a061f0c0507091b020f03 61
    0x10094200e126181140768001c4518008031050001103908208000403c10b42488044940482c94100c0d020559030702c0401c00d2504990180054100341c3d02c9403440b021012000009800300091003208404040d00208840d0300003c40355240301d101180c465070300f030f511001500d480c401100d1894601d40c101c071041c3d000345034070104a02d02083c02c64030080010b0071950380c08490000e003503580c8001c504000d4203001e1751000307010880700c0345011818050f40070781c1403292030191100c8000000041d884224007200c0c1d0a0484d822005039409850101409420154121012000504820300141c01440c018185c0303002d458480000d810f002c000c1000760705d12940404c1060303034090030a030104000074070540010448a002d0300307400740c1c6403401e81c030382b0b40c030300400e0a89154041030031001040020740f584071707411710084000200c0130002001182c003510308016115002d080c600901c00d001c40c8107402c903003160516001e00c4503101220003041c1c90498840b1045218030029800c204410031035540001928101e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481958282 1250 481957032 481957043
    0x90705071704180218120a0f061d0a0b040b070e0411120f010e0a0f060e041103070f121202010e10150f05030a03030507020c0a03050a0c0f031707 64
    0x1448000d844070448422030100340050303500300040600044001000d00503e802d000002542814100c0117100001c032a80c03c3c800d401221464505a038841c8100312444403660403003c05114074000d800d0034009030103883c0240f00c1740c2c0d104100840c008000042c410707900c80c2c6c104054040b10340315507642410703c035000361400c000c00040740d04804055845d44074140942955244203580c5603202c0d1303200d0400c0000105003500b2100c2d81c10040082c25084082a9400b1031303038010024001c0807070340e0050020311a1b03070003c00c1c402c1e403200c04020800c042c4150fa000021421000ca840c142e07643c03207405040c11918041c195021941040304000214120b490b500010841d000101d4500502019280780880c0301c4107800119445401021440d0014040d60340948196251505014103202c0446d80c0c407420300d0402000c255139000002c8070b0074400d200ca100010002054040c8541d40c3c0d0401c1c558070080c5000559658215030400035411900041803401c0340d9111025100784060304600c0851038122a00030350300c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481959532 1250 481958282 481958287
    0x40e060f062104170903061819140105010e06031e12070f060f06051507030c08030a06030507141f0e03030a090806130c1404020409020d060509071d090705 68
    0xc001406444900038844a0038440c905260a08022138049a09000040044010013007505907403070110300b407640150701c10b5a034520380190500551800e15031000b00e00506540e600d1080c1000100b024111008003000b0007800644d8940d580c113030320100c0954405900d0391040c0b00c40308900240b40e0a0400350318514007a01d030000100109075609034041c10b070403a1010702c21034400c01000090307c11800343e101c2c036500c2082000d052102003015000799100200c095540403a8040030035104a62603015540e101c903840c0d483e4100175201c0c070003400c4a800111140e004500000c180c0482134038003102d0340000200320f03042034031501a4113042c003880e60f00380008001030f50352010b010740c8040000b0964080380d952080046441d1991403400d0000150011207001d114005600c0410514056402610304400a0b000e8a10000001500a210300e03441a841a4000308840356131a0b141d52001c402c80d0001d890794150307592030020890356844202e03502c02d0002d01d9017201d01a80e062108400c0c0c1d2080d95420181d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481960782 1250 481959532 481959547
    0x12020d0807032315130c090303120b0409210507080f1c05041208090a020102071412011b140309061303030f180c0801020c0c0409020f06070501061a040e060f06 70
    0x8100c40400c41da00540e413408141d0a8156040521500d003814031120020807001c18030a40c0141003494070700c0013800300301110032408000700b480c2e0301c10f4102c1c21004204010300c901c5881c0a0615001d00c1c05412035181e5206e02e50a40d190040003220015039000c60315501d0700c83d5444481e812504515aa1131029001b1201f60410146602c503481c0994041e503207500300c94082000003403102c0d000404400498100300a4840181d80014146055820810b907400c9d0000400010484100000729400c0080d804c0c0030f21032102012a01c80b0711118205a80e50404240d61074101641a2005030f6544000758007000004541400e00351503024031078403900d40810854101c410020994048409650328020740080041c104403201610600400c2100001e50500c41000181c40d100c07612120a0b501894030341c020101150b8a016135005482c800400c0503440c3d01e040d09016000305024000c2400903001c0c1c04010481440c12026582228001d507131780c0c41c09980d40418080c0d030500c4148025003064052003040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481962032 1250 481960782 481960841
    0x1092c070e04080d0c09140f040b0a030614060906100e0604180e0d08070f030e0a12051213081c09080c030d110403110105211312020d080703 62
    0x242c0654011140b064542036070058000031150325203825801d22604500410400814041114041e1001c0780d42d0481404441d002c45c01500d5080910b41d80911070f100c0101c1006440d074407210a0018080504003252b68020034082c032040150b8030150b203c0c2c1d160303030b00c0c3e24403503c40c20503981250b01c064202803c259440d40d01085080300c5c201c2c25002944c13a03034981c1c5c400d8401040300f001d403c0302a02d81001d16050002d0041c2c41c8400d182240020140c4910062005207810044000b119a2181065001c45544031009150390040846000c840001a010400085174a241d403600903410035820742c40c2c450702c94a08642e012a50003581c1c09542c48400c0b540100d4140c2c0007600300301c4855000786940351840c0e981d100488070a070498000c1070205000900100300b40303a104490b60300003801d003103035a250f10841004409803100b00494070030b0103600400c0020400b180002c280c00f4451a28170380c1e00020b100081c0c0e00d9400d10310400c00002c0703007040003610481c445d801c00502125a801510402603204800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481963282 1250 481962032 481962059
    0x7080c0a0c050f0406052d06030c0a080903120a1a031c18030f0f03120501031b0503031c0c090806011409090a0c090c052a0601092c07 59
    0x141c9070108030903420840350620001806106030111410440c80b410100001e6494007002c03030304461300034500c2c141d5124002508800c198200e0051041c0d0301c07407074001d043d003003144c0c41141c164000810745800316444001c000140d85100002c10700001d0349550342401d9038004c2200b040c103490300407520302c1c0468168034103109c99456907161481000120149810107808059000700c0c0d1050341520307680030408034100740510221281d2000400e150b000c3c15042c1110010800c19500c0d110030314010000080059003034200d59428604607030781c030301260307150201901c0f8084d4480b101c44400d00001c594030504071543c0190b8401c103450801c50170540d11445201c1c9450400d8005000e40b81c06034148400620b05281c16640c03050b81c1400a0108003129074075901205540d1050840781611614900304140c0540c05840400d604441440003040c0704810807502c25031003050103405802507030004074503e100d6000d64004003110200c0240200148205000c80c444151004000740c014080081000c00354000d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481964532 1250 481963282 481963303
    0x6051c02090a14270a020a05060c0a1e1217040201030e070906082a030703120e10030507120c090308030a0f020a0906031104060f210e030d15030803040807080c 70
    0x48420000011600070b15500d9408404d030843c60b0310450202005a88038000b60091303030010303104191a0002d107450300303117030100d51003000f00700300c52518541001d041041901c40305240140403401c6004c03040d060641e541004d0703070008070014203170500283c0994029080300e4075050040342102e407865911540c8400300c0b4802e41042130700760801e056500c65000d80c0580703030818280c54030b010070100050034000380d40c1d0b00c030921004040902d8284041300705130040a02d04101c0002505112210030811001030040c40121a00f00c04a0954003045a0603400f81c0316007001c4110355207441c1d03001d50858881c500303607420040220344025107586841045000700d0000c3c004010b40c58590418450800c1c1c0041c098441c40c24076508510003e02042040a51044030b2101003082424204540c407800281c0d08600c0400202c80340949040640d444103c2900000400b07001244a80c00c100c900f0203511801010b0310303140b1010340402c205001040c080380f02c0788003c00c1035910450105e1714141035020603d0802d200200c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481965782 1250 481964532 481964551
    0x8160c02030d030204050306061009060818030f0408010515100e03032101030c090c0e04020c010e0706020c012303071107081f051501120e071d090106051c02090a14 72
    0x5c4c01c001a040420120340c10000c02c60700150661860758000305854030b030340f1402c401c210080003c07a042880031500005040220f0054940d188051410740c00b0b140e000c0e100740d8140f58079150000e4076070510081d04102d02100203061346170140520f9400c643c44529035040c00d0b410300040140785040703048844a020202d07001c80403002e2075032541c00c0440c80c61140c2e912502100e424140c0c0150500d501c05001e544c4180300715001a102c4084a1880340144101c2150720071910032001c1c049402074001607a18400c0400740d0b00c03083e010f8905044d85006034000d078060701040324144081082d140c090a494040303941c00c501255049507841e0303911880c1001021005000d060f481d594182140c610b03000b050341c00041c80c0c00700503095441500091881c032100e0a076900c51039031044842c0b207104050185100804060015502c5d8002d02020000818402d95011815601e0240001070a0070b100313010008071162010b14258040b43c0f5020300414100c020092684d05658484084a13098144040e038050803020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481967032 1250 481965782 481965787
    0x71101020106060f0c20040911190302030703120519120f020702010c1b093201030804030611090d060b090106031b0c08091026040308160c02030d0302 66
    0x5001900b100c03159001801040b40140149840e9500304c101c1815150b84948804850460740001103014406095026403150428840b4428040300721044040604215140b1180d031038044052400d18200d880005d4054210030400c1010a0914070f81500c42c240c14103101c0d2810b222031690003200d0240716001c0000c80c20410a03241034140e64840c0e420f28000819045250100540018107251180341000309081d156010502404218041010050803140c034127105040d00756614944a801d00c10000b424103007003020b00800103260b04080d0341260f4000e50030614090550b2140406028202c0404c3ca4003071042000e40c1403034440030800c0307100d680506000100005181c080026858069002804041c18080030030001045003000c50502d00c035605026080c50319518000f07440c0c0c0210800782d54403441d40d05100701c50b590405201206104100b0f480400400042d4140074001c1003a91301500141000c8001042c01c00001c0d40c214000341c05017011040d41d00c16500091424010040410010707402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481968282 1250 481967032 481967063
    0x602071202100204030b0f091509011a03070b030c0315030a060204140405220201030b041d10050702060103032d18061d0402070c03080415090803030412121107 70
    0x40c0b11868099001c024258a0203146440b076a542c04405040400321200e10b40c0403900f9564200301712403d03030709070400d1004285001c00305180203020348904004814240000310f6000d180c040782440603070b03ca0045031415a03c1e002000c140130742005003800c860a62031419418603940801c24030300c2c120b226410142e960350814401404500c0002500d50142c0d0405003030084500c020400008071440354100c2852400781030004801400715282c10542080c904100b600c1e2903a240107400e24080c883c4001c80d03140006040240381250000c41c2c1d85d00068002100600010744100c6a910407c0180c800c01c000c400c916225a480700c0c0402c922a070045240344d14070414001c464040d01000300114204001d400c1582c03a5401c42078101c150300103110b0356000032840c040115510400015540280f00c10b9125600c40c1c000010015a1900d08804142d0b180300c001281480042120301c00c80d07014015485900b2102c1e004c2d0b900000340c030701403603e2a848955084840c0d1804c800b4101080c040d06050302006038 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481969532 1250 481968282 481968287
    0x40308070c091d1f090816060e0d09030305280e10090f0512011b03050403020c0f130c020709180212071a0c070504090503030609060a0602210706020712 67
    0x1200741089900030b91207419007683c0001c580460002100c03071400d8070040d01c9085800007060b900300001c0150130003003440c0c0000c84240e8000b07034129205480c104000b1190304c15891741c400d07001401e400051158803081c030001e48190042c0044000406185a038403440c0880b640d20310480b4814280003480c059000c13401c604c0c01d60248410800c2030304140c010982803c8140c12803041070b0040d18025420682411440c4174250b00c88502b2a0101035840307a081441c500003009010142e070103400501c54140f414400d45404d601400400000400460b601c0d025125070f40080d0032002012401d60141400020b420044c40c010801401010070907900050100e104101c607408201d515800c00358420b16041c490040080026002c15403d0030406882d1244910310390b24048564111503082170407e000030082180c000040d50080000b01d43c0c100260f0b84500c188030b0703280294821800168008422440e10509017407104a41e5141c0c0b00346a4a0322042d03444a6003070b40d020000454460402c00c0031540c1c0d055 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481970782 1250 481969532 481969541
    0x10c140c031219050c0f0f100e030f09041d0f0d090e0c031902130905091b060a0e1c050f10060f0e07201b06030f0403030b0303040308070c09 62
    0x64441000d00d04094031036910075101c60383c480052041c41320003c1c541c221803400300100b8181c0440c1104841011100f403181e030b1340300d1900103103620b007560a10801c595a80c0010081d02c140c07213151002581040000750420018043c20082c0322140d1080341010001d2600030301145081a03106d500605108500030f0f00241080115404108001c00c043d0501c610486000f04a0b90806c00c1400801c0c0810101800f00000344200908602c010f054500700154105240c0c001d10702c1401c9800c1a2020070b400850103100007001230840a611a41c10059044903038010300a20401c818054449070010350808108a00160b03508401d6500d980003010704010b0380e01c1000b4440c003824a120050140c81e01e4080c1c142c1d8000c00c680200c03e034488030040040c100328441d88064009107240400d801c803820001407411788410080000445104180080d1703c2d59080c03510403240994210b00580300d4582c0c89460460060210340c0c3e040764540000c00c00000414904006413403054055249103541910b800b0030300c01101c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481972032 1250 481970782 481970803
    0x213020a1d0a0531060609060216030b09070306090b101203090b0a03020c0d09050906060702060d0b0418080409050106080609071809020f07021503060a1202010c140c03 74
    0x980030341d1400e0728a500c4194a0350101d4070305130762108001941c01c00d060903050300c004481d111010860307070080b030010315500440700302c4406c1e0701c54030209526500200c0e11042d80140d51210503945880400009022a0800c5c1e802000c1e14103488a00c1e8490f6078400642d10300350016111107081da070134006200c030020f840e1001440c14003d080106a06036801600c0c00543d481000303001c003004280026102c2c081e80445801c0c2140c44107a03205a14080d901400400450013080d02030040700000800d241050350072524201d070002c00c01d030b007024201c0d12160b020309240c0742d0760f039009919a080c0800550042598103101403040d44030f2030f1924101a02c0d0411150168080300c1001054018000740c4c0d111010041d400c0480e80c40d01c0c441181480050a402d41242d1b44441c04103403000440360307203175a0104e000d03100241c421540c80d0351694100b81c04180c40e00082d40c0700c0c0d9102080403000c010461104010a02051045c1000c6107200030f240c4852803c2c1206a042945541120600030401c1ca01800382d2485c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481973282 1250 481972032 481972067
    0x604060602100203070e09070f0801060806220b0303030c070605070206070e0103020702041d07090b1212030403030f09060f1407050405040b01090801022b09050a06020f070213020a 79
    0x80614098000795690310002d144030360760b940000420300103446155a82d0102a019107a015a07080041d40184402c400d01302e40c0c1c0c005442d202c0040f4140b840342d040e0030b00440c0010408208454100348400b01e02e0b8101005020650759800c1c41c6840361800d0000e544150044001281c0380ca46504000d015106c008120b03604641000081105454005020035200352084c0380040c0c42d401c0610125000b044880301300d11540006420460b0300020001d1600166001d02c0c50030b1016044034028419040700a514101154101403e03124451901c1c10145500501a24001ca032035000540c0040445001d00700a480c02922100300d406102128002c00500305040c0c0b44400d101e2400310001822405203005840c400c0752541040c20719684a101c40c1c201800301e82c0021550794440050150004a030031504407480d406601c003000c580c0800e4130075a04d00b5030300140548a5074620b65100c2009501c850382c0b2149500c0103000784c1015840b41181c400d041082c0c1d6200594400445401404d8000c00c0e4030b40c801c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481974532 1250 481973282 481973291
    0x20f011b1b02060d1a03010603151a0603131713050405060f0f150408062401050406050403151b1d120a02040509030c0d0c020a090e2109060a02010906050604 69
    0x183c807050200d900101c00d90b5000112003c20f4101d41850080c0030400641c550b080c60004014000d801d800030104142c00344040007031100321106080882690750801e03034000d00c00e10015001440c440c0f91281850f1243c601c2e03c860165100c9000060341150000c2081495030203414030150906214458204504030345440d1000180000102c04011103848103008400e40c0380c014440d41c40a800751006800440c00b03540baa0310b03041e41401c20b011442d252004d9001e8103560316003501e501031000c6a0641c0c04951b01e0364030706400c1d1f4a40511104180903541c17101e554841044008200442c4d0408014450795104c2d600d008031407400c01c0240355842d5910b841817100080051131084001040c0410aa064501140540d28a80c10700d045000d4291401410f0155544108507194090000c0e08400c0c070032244110011b0702e0300002c4040304c2103140e072064250300411009442c17030ba8000301d900816020054582c40c14441802240642d086600a0320144c0c2d16122000100852401256030091003a2010071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481975782 1250 481974532 481974587
    0x1c150312140c0c010c11100804050c01050309030a18120b090709060609030212030f0f030f0108150a1d0d031406100804080708041203050c060a060321020f011b 70
    0x141c550803d00e415505004003180b01a0400100c1c440700940003400400010840d412400040e00902d0708071002c54480c01004a41c81e902d45c00b0b2000d0f01e00500034400194100000c0c40320540701c520509850103000c24409000044902902a2364292903205000203903150401101c80c0707160007010b40119142605040c0c041c000720380e000b0b00c624200c0750122492002010440300c0035066105080300c00d0528600014400c482c812400c00850003545000142505a039884442946441900540c82d0a880c03841c4045002c021254002c451401d11402d104065408221070141c5040709840c4207602003900e0700500354002c204120041e43c060001d80e21003100a04025004140d124020f100805007217022a000702070041d88000d0b0341c0504a00a2025440c501c0c030704000d0f10035040130640c034541d071003108000717054580140240f200701d952116071902d0340d810303100340a010310b4404551803045201d0800001c1481c40240650107071f00881d04080c074908d0020080041a0061040c0c40c0c0200310f5840c060301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481977032 1250 481975782 481975807
    0x9060c03060d1502030903040e2a030618070305090d17010e070c050106060e0a12021807030f0f05090c0105030405060610050715060f1a1c15031214 65
    0x220791104003155002d94a9a1a141c036840310b05100381000c105904c00700811a40380000001001914070440036846181d440c600c0c1c0c0304442e0082c00350413401c1d00d24010a19045941d61002c0c580000740201202840402d0020030708030800d00310380e0000000c1c0c5032002d200c0c03000400e000d81d11300b13000145000c051078007c0d0104404052018070900d207204e444c01000034503442c400c04541c0c244a070f00100030300045903900d030024140784100b00902e1080d03214400c002144450316660071100d83d03001d0a000c03452031403d0311003506004000c011a080c5030700c131614421014064401e071382200d25100030000e000d041a411581c50006240b182a060200400611020900001d18140d004504407440350061070408003c551901401100a1100c80c1800c011001c00c1400e4110f0816148842403464010740d0382c03244064040203011500c0d0543c0800c01000300b0f03042c1c0380c008442c0034801c044804950507400a90942d900010703940251040c0d0851807444c0003c2d607100841f41c0c070b40b0182d035071700c10304050003901c82 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481978282 1250 481977032 481977037
    0x8070c0f08010204121b030206030a020307020c06360d060504120f050301090e030f03041a0a0218040207020432090a023d02070914070503040201080405071a0a0809060c 74
    0x781109428414021b246100c070203400b0059640070344290b880742003a81e200400381d001515048050b0007141e852084a09101081d120500d40d9000700c0c6c01a41c40524018503031215404161440211810100e0320540f030320190f0107030040c030544e00003a841c540f608192403c800000080420040c1c03104c1c00402683e0b001e0241c0b41500c020402c00240151054280d51451051803080c1c0120a00882000207001003414400c050b42c50822068990350745a60782c0c94101d104003039146106030001d110020301c6080642c064038503244090400074540740303030903400e030038400881105556142c030f08158505684201d108003600000c0c14002842c6920140d17000911840c4242c28448030602504001051500c0440080100340310044281b121807110b440002d4079080203008062009050075039424403130703803a25085403107140381d65202e600b5900d81d40d00458200e540a4020742d003034819000d001c101c00c0c2e0700461464121541401003651010780440280c00080024144c881c1504100104001e00403601c08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481979532 1250 481978282 481978319
    0x702010c0b090f0d080105120a03050f090d0203070e07020d08040f080d0209040f05011502031314130203090304050a1e0923010e0405120a020706030c090308070c0f08010204 76
    0x110900542da4a4841500d407443e40702040205101d1810503000c5603070803200043c1070312010b503800c0028100000300c1039661303070342241d0007000140304201d140c9884182c0d0b00074000d261002003202c041c500494000910b400300360b400840000e146901440211601000040c3c102aa10f00300342c0c0e1580b8081c0c403130b02c44583d00003c000d06010300000c0c0c2680d120328140c0c11901e40140061040020700c2c214088100200024000e040d40d15400a0090308098000429104503030700c048049112a0b080086401ca2005401501500118412050340d45400c01d40003031803103015003900460f1104c1c6000200b00e154031043c0c0c014030040c25001c041c44140300b40781b000c42c2c050715144e000120b65000144984401a466001480e5070b0140000000c6510900c20603070502a0b4000c9003100c1480c410f150340c0c1000c5205601c010b03800341e40b0103c0200080c034040d4001e181e20002500340408040c0d0340ba01c640e0007603070100c8012900c0b038103210824000082ca1101c020040e010305070086013081d06002c0340d01c00c403010192 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481980782 1250 481979532 481979543
    0x6170a02010c020a0506070f030206090f190203070305060103110a0501050c100b0a0803040e01050f03010510030b0604060b0412061103090d08060f03010e0609012306040c110303070c0303050a020702010c 89
    0x2c0b140654880140c13840040401502e0156075070220308200d14011084001100140210701c0401e040c3c0c640001c410303010300c0c24000601698a034029082e13007144c8000608a030580508a00040810001e225503802140194400d68550321000104084000150007460501400340008060070400199225110012100000d14501e107603001403550081548075085031321000802042009210000ca81221810360344600c0703e0070a2010182607500c1151108001454001c040011501c00c06003503401c00c0c005040044d9490300c0e080b060916a02a03041040c0d40c01c5030140c80c50401010b0701c90165440001d1400500f0340c10180126919001d5448900e02009014008074005684210700200d44100c02002044141d030740d40c01d00d40c0c0354441250300300883c1d4078040c070101c0c01d007051401d103045020200160b1229580ca4504200045c01401c03144800c002c2d0b81c542540d4000c83c100020743c0902c2141e02c0e1441020424a001010394400809820740180180100c00050b6040305106640d240c0c0311 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481982032 1250 481980782 481980797
    0x6040b12190c0201020c0105010f050f010f030915050601020f160909060f060807050117040c0e040602070f03050d0f0212071b0510050a05010602010902030606041508071806170a0201 80
    0x104501403101040809801c07506150064100741030350154006d01080c014013000340510307a42d1702d100c81c2ca6151305100301c5030400303002151252650710640d03281800c0e580c42d040014105ca09a103901d104420f040d00760394501c542e0b44043c48000c1da010080c501030080c1900042c0780c00c2c910705c07400c82d0681d5a1071007414031982d1205a4003081082c03d0f009100d001d0b48285040241e26a620f102a580b00c80b039105842c041070b03012034280700402440e807850b0310841c0c000714180750b900c2c90300c220204d09281c0104144d480070750034041d42c0300150050320200c0d082e60203682c03403581702c0e940c0001c041c0031903060103040c5044038410425081c03400d00c0520541c0d400300940c2032a0305541e440d030191900003086010b00038814010100110035400c09a8003580c011007807410200042e80e21403001781d080340c210000280d81603209100150132441d083c1c102c0b082c03030350543d4111001c0b690b40b001100d25010298000c04440c00251000c0418141c0510a02004203808100740e89141942242e554458101c01006410000714 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481983282 1250 481982032 481982041
    0xc031306052205030909061008070e0f0613180e15070c050f250308070f170a03140a110409020d1d030a08100614070c0e0f040b0606040b12 61
    0x1030b000c0003035000c201c04240c00510015240641d181d61000d480203200302c40c10350124443d401d00d0700000c0d03004080381d1200c1441d034440c444180c0b0074202e0418000d6100219140c080c03029201e84020f05030818040141381e19150400b00d032a00c000454100c1c154001d8541981000403800c00074072940305403a185007049564039120000c640c0d100200364050190b1044210115240c200007030080d02690030906003800b02100d850001303900b059541310151810384c043c428140401c00d60200401014032490002d411030400e42c4203465148c0051080002181c0d4809000c43e200303808800c5282e001c070040b5400c000b41d5240318440c2c2040d005502510081e203601140003000c69a59601c1941c00103e100800f044110004111036a41d60100746c181c0005204840812452103007009014240c44007502d85d448020444886001a03030440002030b15004c555100002c2c0401521601c1070040c2480c0303010784a50300d02418a0702c0c19010140005014500c1007004100c0d0028680c00c0c1c403100c51440d03140d000c0540340c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481984532 1250 481983282 481983301
    0xf120606130512011b09083310030203010f090b0c071a040c030203010501030f0323040b0d020405130603021509030a080d1e0f0c09050f0405060303040b0f0409050c03130605 76
    0x280d688042003111100007100717900c50b402411300d10484d0310315400c490070302d6041500d2000c012620076042800020100a90680070030307001d192503100c0d80004403c0d800554a070002401c0d220000b101032019591040c840092050244915501c0216500c03d00d203407203503599601000101e2415402c001e410254085401c00091980d8400250707002070081c4403650f140c0c18800601901144101d011072000c03072601301441c071a0545404000f0b20200712606081c5070850b0300c81a40d000c11030012a0660811022800741c1e2241c1d490100d4071041d001c0054401d04500c10301000c002104881059004140443e2556950015101c4003890b4002c031b44648032480d00c07078010064201500c420034102145000001000343d550300040750300000040c24031100b081120181d03a01c8100c0c0c00342d80e81202c1c7c0204154003c1c180f0340c10003904411b0103001c80307240a54880ca9a186504003000003018854000307001c0100d440c072401981c1d0442c4030403a0b481e10b5800d11280c040da0441d03010a0040609840c0d4000079880ca4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481985782 1250 481984532 481984541
    0x411030a050c1b0106180506030a082d09040c05073f030c09090b0f0d08090a090605010e01170610021c0809060f091b150f12060613051201 61
    0x50000d038084907895480312049005c0c0ca91400f038030001044100034255000003600845010b082c029029244040c01c0c0d459032403540e8080403800b031140560a246014406510070030040840700c16500d141c40f0f00d4a142004240d4408000d0001004028803100c2d02040181584160b8446240b084141101c05803041450b85420303045000030100c4011621241690150081207020040340d4886103c1a25100303000115010318040395040520845000d0003030404550040155000703200803800c0195840005020f0f4007190040071a05484210801081d60400340031b22111400742048540304a15941d0780e00a603c000b44050f1080260701d882242d01070003403141149006400c501e00b0406641201d000c2c0451000303a500d2045849000b00003907840254205c1d0500801c0100040e001d083c000c00014400302420100150384040038400b0301d01c540350314400400f8034050031071803252202150b034001128480010400c038010201000140c0f046580010400250303a0100e071030050191003c1c1e1208e0050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481987032 1250 481985782 481985797
    0x1090c0608070315090213080d0249081006120b010905060d02071a0c0702091e0709080607020705060d020f0d0504080c0613020a21050604200411030a050c 68
    0xc261344004202c004c00c4c0d07002416641c040b00300580d442031b030740c161556079803205410840051700301401e40304445d9003800c4140c045100005030036041005c030854482d203419103070703001500b10207410040e00780b165044941903078456500c2d02d42101a610300003000d41041d1404500d00320a0340d55001d9810300340e005001c0000074000142c03c10fa04d400090740c80600a5000c1c80c01518209034030102c06405590818a46108684400c51181000d080350300340114800c000d4002510100711711000c03501008046181481444980d44141c20f903854424000d05014000d0056011908515000e1101d902d8403000c50381280c410a000607550b5000e50b80d1143e99000704484a21514100f10610050105940250259003140010303200c2c1a12488071100d0362100b40c04000350450460881040001d007400c0018032441541e0b40d540c03210034000e54400d4100041203e080700c0308107030340c11440c2018141001c90518600142e604001d10088a18640340d1408020702c411001511400040e11550141d81540d130034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481988282 1250 481987032 481987061
    0x18150c010510050f0a0803070305070503040803030c130608100302221a270c07020d0203060a060303080117070b0307020a080403110f06030c161b03060b100201090c06080703 76
    0x10307801d01c408022020300b0144503541c420613502e0f501d40b0951400b05404021150031000440c6018010781c3c09651f1a00540010790300b03808280800252203c1c180700461241d402b04604036504c1811640c201a000703280d4020703000b081900d40c200811090700b42d0b400c0c010703650103d8401505c0741014200c1441407101c1c06000750f8540c142058003040744102078501241500403076400c100e82c0b10760340d104880c9000304148aa0f800302400045000d014642c001014083c0c00903000041001d4034bc4c002c01c2c0307422420348044074000d660b00c070100103050b03000803100c3c05880c8450b00f01042c4005542d40c20340e00c004070300507150310300000808101d08600030440c80f03440c4c562241202da15255241001e01010b40c240c149180554005003003181ea80c030340042240c3c402c400c0d401199041100280c885000e2020016045074200c243d102c6261f40b040c3c00d000d5000065200d1100880c94000050502c042c82d4041c102c1c1006681c10034501e072000030b03c510b942d0801c0d2925440e08242c03a580701c100c00c5010749146020740ca00b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481989532 1250 481988282 481988291
    0x1090c080604110d06080703150c0c061e02072603070c03081503070e0f010801020412030503040c0b04090f0e0109050a020d030507060204090b0102160608070507060902041406130218150c01 83
    0x440c1e00340422100d0880b40109d0300c6540c030241d071104c2c1a00b03071148042a0800a0582110a0b000520a6100c083c500c0c5003461304c1d621101140000c6000c03a44814130030b031051b0940007981c5100b00720304040244020107619005045040c0880701400c00085024014144561140001c0d049803c070b845080081000a08441d441030352a402001500000d43c0c21110070f80c0785000103d640710b414000c42c0c003145c034480001403028000d610300f1130305078001501c211000102c1210024094205078064400b8028102e80060000c8801c0c182600319943d002004485905201100012038004200f880d035490b016034002070308886510341200d1768498628000c000701d20114020a184003a9444030700b40030000e8007150140d1342d610141e0004401e00d4450f13000090003081c0020000340c0301308090700415100d8030300460501c08035800201500c081c4a00c6100c081410004c0201a140010005902002e008011481c120300581ca0944080c030960903d0f0144268804412200d288030088500130000c540c001c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481990782 1250 481989532 481989539
    0x1030b031209030c04110705070f05030706050a031e06090b01080618040f060e0102030403090806060a090f0209030307050102090f0d0b01050d03050702040e0c010f020d051b0705060301060206070801090c080604110d06 95
    0x86c066001680c00340c8080c031986a005c00c210790503d0710a010340f00020700405820389080021540c030303801640150105600e40840000f07041c9007210182d20490300c0c0b0030100710b40f030801c0d80c054210b07604041454108807082041c04160785500c0200c03283c00802222840c510365890400120845031088024166860085d0b1406038800c1940654080ca100e07a4400385210703030360f02c040d640d80c04041c0c413542c0d030180918000300941107059004818808094a01509240b959000a03003580c0103280281c0c0c86940000d400052483c010403400b00c19801100e21480300707a51512030070b02c001d405002e2140111051200507041c14068016a40c00d10ba0007001400001007100d041c0340c5640c0010109030101cad000031100d00040d400440c2030485041c0301c0e0346180c144100f074580b154076068411200009801103003070100c4e080d15414000c0d8041c00d0b01e074004204034288800c006051100581c4040c03049840c000340d90b80c105a000003c650002012100810441c0300140762540341d02c1150800503444c4d145c0300e4000f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481992032 1250 481990782 481990811
    0x7050303130e0601080106020c041a12070914010b0703120b13090c06050f0909042a08060c1204020f0a090204090c080604020408060c0c121c0b01030b031209030c04 72
    0x1419140b1100010142d512004010340b000c110a01455002d40c1200c42e000060703007001e90004020140801d0105001001c0d0b0010990040e0709416200f410340044009000240c03403801030092005941c40c4040482d0325041c1144000e00484130010304025141d82e4040b12520b1640051540b414010018a421141c107440c08000b0320001000b100c80d142c4030480040d00c2801801034814501200840500c4c00c59954104482038500030300031038500200001000080041c40210303c021815a208aa041802c0c207100614041c0020501b2408610810a1440100c07410160340d411aa05444800300c5502d2040000c20402c0780341c100e0611148082030008003a40c1c01c0d0010340a07007880b92148000f40e00c81d24240401e80c8110700503405150b00900102e05201c60800007029070700002000d80b10901030488000e8a00d5000340742c2c0d1740003601e01500005c2030380c0583c400c5001040090a04000d29401070011070780782e0914001d0b041e8580c0c404200f510310345d2024400c5a0000314001c204102144203411103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481993282 1250 481992032 481992067
    0x4080f0a0f0f0309020604051003091e020a14220b2206050108040f08030601050d02180a06020a0c0e090f0601080a11090108030904021b0604050601092d0c0207050303 73
    0x8810020b100c2c8966001c8140c081d01c5841da070540c010b00070307030314203401c00c0140310541c0c0520541d001015551034030b1801141e04000030034907612940078000b400c20f074180101304c66007446402000c0503100c5c01e04440d441c3d80c0ca07602c80d20314150440b010400c03400c06507410740340140030305611680c00900b00e8109003061214900d01e818101d15030482008503c1c0c07900011034400307070115401016800c0345500e410100b0180c40c013540d80b00d0014900316180050040001042c0d81200c42c20414442011502241d5858500384590207024688004c0c400024541c681c0718046c00b4900c28003145150480c003040c1420400c0c0108401040918200c0b0181d5940c0c2d001255600c001c49000d81c1c0c1c81d4070b40558076000e8900001d089040f901100001d500380030f4607004204c001e40c4014104659541503001c0004070040038030031207208501031005440e456240c0407071034054900010b441180c0b2140b41c406010540b45080c003074007488900303941c0001c610307985c20070981c50106030741c10003a814440495220310360310b0341001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481994532 1250 481993282 481993307
    0xa050d0f03030e031303060203150604090504020108010b07020616020f04060f081207030f050322140114070f050f071406070f18050d1506170f0601030b040b04080f0a 73
    0xc00f08420041180e1180c0c980c014100301c0390080b000039000300082103094003d550041000c40f03007000ea140051000411590241d4420101c00d625103003040250743c3c11400c2c040c01000312144081c600303641e0f07034001401441460120802802c00d0041c21096440e08070010310300c042d01610402400e900d50040301d4101a9030b2250512620a142e40140d11102c0041580c00d101d80c1502e0f120090078940707506443e203400007460900c680c01485e52004001c1810301c0500075040c040d00c260b4205400000e601403e545031079200c40209070904041c0900c21764064a000c00000c00d500c0d089496030105541403945101d070f250068009070f0340d03906d100003c2c1c501040980c041e8100780c45484058080c0c18058600c01f03840c24900346503510b49202001039003030910014000740e00c150104922035a1049a034422218142c01c00000c081f00500175052240c401c001c2810401d44000051403103616613a111111402c004000038180b1400b130f00882d0420594000f40c84c6a0031182500360344946a410004040c490a1304 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481995782 1250 481994532 481994537
    0x9020c0109051605150d090206070308010801050f090d2007080c190e0a0209061309061706040f020103181e020103051e0c0f070b0a020d11040803180a050d0f03 70
    0x10f403c0070031000f501d40100202c0780060a1000c50f01c58140100005421603c4251405611a0413800069030340400414517244aa15540b0080d41010b040908584000701004c0c0441c442c00203011a610b40000c15010500052801c0500e242d06c5444603400d506d5443c1d81150144100c0c50007080c0240d0206025241d410140d50f24400c96241c0c1003200010607a41c860340c1180100000030440200ba01c0c0c00401500704080d122600e02340132990300c00088400c41e40b06508203555040140461240c14440116001910004140e181070a484005000002c810300038103140d80d5442c84c02c0030040811400420540126545084000c0800603800901281004900180c58880002c0f0b410000c10b84c02e9003240d03000307082c6a019a903039002d0001e407580301d40007601a084083c003103140007035000311100348607a10020002d03031034403490440d1109a900004070380c09803100902043c0502d6100205039840362080746800710009541e0700110700800303466000719801a409149003000c0c0407800802103280c600c02d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481997032 1250 481995782 481995793
    0x9151e181b0304080702011409130f050108010614090604150602031c0c0e211e07060839040311010f0219080c070503010603050a0c06230a030609020c010905 69
    0x80e0003400c0d01c2c4801c0790010291030b02400300c81c000d54402c0e007024510844640460b460001c43d0800a442c81050030029105182c89070007200c2501114001e00380140781840090022500308032000d494a107030024601e00500c01000010725a0b500c9400010700418140210449280c1f5000000c5d26940410840480070305400c0c00718000e0030003481041c1c1603003a0740e40c501459445142c1008010302030090704a50702a0382040c040d40102003407003042c81c042c408124050000c840e10007002c1c00c104007688404140609207082000c0d40f07180c005040c50f19507600103c1e04800010003000703481410402c102c88040d0380041004402c1224890344083c0020090300c59100352420785604990320205e8200c6a800f40c1e0700138044c2c900003528880500040c100b181c040d00e41254480000c6402c50760690300581d980d5009280c0b640c2400701c248858005402e4038500040c0202601200148001c2400360503848a40c2c0090000c800501c60342c000030192120182c155600c2c401c0b032494502800d010780e07080d2150b0040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481998282 1250 481997032 481997071
    0xa050d050709110f070b15090a060611010e072c012705060a05010311040510090f15021b04090b070302040504111207032a02010203040b0609151e18 65
    0x20101511561140c0010042c50300801342d030307400c4121b10090000b8901e41c101e0001c00e1490f03a280b01e81284a820f10500019247e0314203040200f008031000400380e4644d151400100c0c02d5000424040142c2d1100e0184003001900410300200c072091204000c0d411000100001c642042c0c0c2e4420110860100c440595960a044041e40100c81066032442d42c841c02c541001c0100d0750198201e03c04c840d02d04c0004600701565071340450428001d007011308000440708101440034100f0b24201d04084c00c9815803550b038841151714065079912110070540240f85108007050080c0d501d54101d0103200341d00c8869000141021240079000e50020b02032544030b0b50400034844080404001650700601c1141203100681c1c0b80c4060640040581e03104540d000c001c4d0060311410304021181040f01580366a0006940b03107028281807291940140c0347c1481804103c05200050701240da04c101c030740c10125140c403591107038411a0700a520555030600c1e004142c04100d9404100780c240228841c201007001001034208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481999532 1250 481998282 481998311
    0xe010f0b0f0d02090705070c182f0f0403060e0606030f010b030a0204090206090d0b07180b0a0f090510180e010f090f02040b0f0304030228030e0a050d050709 69
    0x1d60181c0a900000720007400d00251600300d4200f5000241424050700d0304c0d4054541c042c90405a40006c0041602d60841c80b200d100d06210f007100100b00c1c90b205641c5000360141d1102c40c2d81c04e0501c1d500004101190071010340042100722002554070110400204884041c1107880c1e0f00101e40e440c0c03081c043d407403010f0080101030040550304d1310b00a020300041c00c03a503401c100003400d8240b01680c21000a12045c02151038850341d151840740120405000380c500300d10001c0400d011403420b1114203e60050422420112000b81d4480d48090b0500345010612a0411075803142d007584120348c442030104101050750b800c00c41d50004c03810400000e014a545410b58032941450a10038490156400c0301c040214201551010855000e0780001610f4980e8450242c01541c002d03250203040d2250000c24071041517010803c401014100076030451f00d4440710382c040340e03844400040160a000410354483d4217507940e14820307006018010880c030107150f540c2c20129a80c003000d0060170805032400034110341c0d002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 482000782 1250 481999532 481999549
    0x708070203090616020406230604030c03110420040302030105090c01051b07180b030d0e13022802071a1303030e0616110414060a050904050a060e010f0b 67
    0x906940040d0300d041c00d84070501c0041d501c94424503043e8050f60032054010394490003064010700d10110481214915a5444d050101321040c42d24864101040100b0018203014050000c0300e401041c4a40c4034540130020401400b12598111a9080040e0340344051044030b00240080e01d0098008100d00c1e0340b8849919950b24840c50014041441880309140c45405203500c805042055005d8450855a40a07a038501b000030000a0300700fa500c0e0364505005040822980202140920340800403201c000007050020408070401c0642d00d4001642c4078850002c0c0c1d00c020136a541c0b449084400720101e20000352110b403680034450030301c801140800740041c07224003921100c21081194081c107500d140e40a03120003c1041e4100c0e081b940a11140c0c0807407218100a50b001402144541c1506208004000450311000502c0c41c070540d0010621040b616104a28829070300d050f15070703404a8555007050303442c0000074036000385002d08001c1840341300041900500d91405c0c1c40c00c0d0910401c03109200300b10014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 482002032 1250 482000782 482000791
    0x40e06040b0a0e2b090f060f11060f0403110123041101020a1a1009020313020111161401030e0303040609060b12060f18070b07020a050a030b0a110d0e0a0b0708 70
    0x40c0303203034a041c1d4000000060450041c0702d03400c11405e19583c600340324400d0016a817207400800c0c420508a80c0c07547e0440000081514464090b00c0300d458208a03445041c10050005410000410540211010258000d105112503c4881000e00812890008200c84225803c5410070007501585c0307070a50001071a0300703200e503100700e03009103071004060340364121440180f41410708814001c0001eaa0b142a20045005203c4510910386044c0e041c00003402c0c4070010081c241c0369074054240095401004545881503551818500e0f1030307a50341c800120060a001d40c03501500e03000020a000410209a0044003402e120308000e03c00d40c4604001c04c00c29040300a00051160022000500060503000019a100f8500c08025400c046c49556841c5400d440350450700310804000f804c5c00c103600d0035403680001400c00f1110741c2c2005042d60341d4945a4000a00344240c0300d81c54058075204481030f181074a040700601c1c4030070040d07a4596100c1036510320803c042580c107c2c0b82d00020502191013007030064401c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 482003282 1250 482002032 482002063
    0x3132603030609180106031410050708100306020d0207020a06050301031401020406171008030f0a120605010c03050703050f031017010506030715050405030106060206010609091404030806040e06040b0a0e 89
    0xf0703569010a40c0d840c1410032242c0c0311895503600404800504100200b104550051008040d020b061030024400c640003d0400000d1001e800304206080c04a680d4400c20740754400f20160301d44030311041840c068060b510000b5404201a0030203d240e80c1e000c000354ac1264020340c0402ca1051108451038200e125a004000001e05404440b14420480c62109608422000ca031420915a1940c4071401c641003031142c0ba80302f22000482196203a84000d12041c84a440c3c8000c00c60035113480d0001c1c0c00000c9050000701813010116000e01818020400d880418110724221503407440e20030180d02e0050170a0140d8492848407100701c40e415481441050311800c0040e0050050501740800d8801c040c10064010381044000c00c0085503030740742070048100500d1290014042541890380c05131003456950072122420b8500810310302c03004810440c45401c41d41504100100d0b80300c4401003030103020301e0341040d58240300d420240000c028810019a1103661680020094500c0d48401c00d40c9400144140c00355 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 482004532 1250 482003282 482003299
    0x8040b0c1c0801121e11030d080910051f030c05011d010804110307170a1205070b0f060d0516230f040e1f0e070e0f13020102031326030306 61
    0x81c555441c044000e041c5d00942c14030440601d401d152100340c10b01c14200f20382e042598803164219003010820b62015915a0508103494507000c1c5005030741700950300c40e400406840303401181c80000210700801a900c05402e050b403000f0348130304000241c000c540c4500da00148171003401d440704080d04036404a003014141d60341c02d11504d540d114055902e0403100440e505001d40900000e040d6400b540d1102480005005001c44400ca400c1944080d1020203140c004c0c01030808c41540040c0d101b4030000d512000780c0c1d692112588600c40401c9440640c02001069441000f1501c10440081030f011070403210b11200751800c5094004c0942c117503070005e0140d1074015032000c40800d500c1c034181d00b01000b2001010f044034100c1d000d921040b900e40750305000c611030840d554156800c81000600c4074002425201c40750070141c1c200040340311010b0f80028201444c2800c205160411a0b10900403100010803030300d105003085841d06030400f1400c1e400b80c0c1c00c050340c0200030710303c0b90303860f0011056034030620005140c1e16 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 482005782 1250 482004532 482004539
    0x91a1e06061803280c0603020c0325020904030203070b0705040f1205010b091e0a09150c02070803040f050310060305071509050a060509010f080402150a02010908040b0c1c0801 77
    0xc00c807903550b1580c40c1d05016401c80f81c1000940d94420710705030b484040f11100031034100d0800d0642012944c0050040500400c20030012950010454034030305540006860031000141d00103440c03a080000003584551420144400e0540c00000340480b1401058203147c0c0341c035010004e035254800c0d480703102585440030b00d0401903407442085a00a03103000c0c030004140c04580d030300080d00c11203003210f00c1c0181071101002c49171a8190742254990054106804104803541c0d5102c038440c98650340b040144081c1c9654445402d030307100740302c000000c7c03200c5003c4980b2180c540050841c07018550142c14007a200b81061040a01014003504046a070480c01415201e07041c110a40c3e0440c81708900501400808400011a0348400a081c0e005041ca030b40c0c0e040d2039080c92400184150210307510501003000003018000076950b01d20b0350400929207022081c1d80c0301200c0005078090803844501a29003032022400040c0c3d49079100091202c80e00020598904442c1d142e520036483c1c1c074000c1c2040c002840b810050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 482007032 1250 482005782 482005807
    0x60a05011b06020d0c031b180b03091c112e020f0c03070501060f0905040c06120f02070b010806010608040519020105070b0415150302031b0103091a1e0606 68
    0x20541c00e024a80251a10843c01e60000964031100380b0b003800a0f941e902e043d5010b640010711100b030b80359149840208103101d41d1103010514254025049089070000c04a4503110007000307520912059008544440100b080c030244c000c5440850074002801603410462581c02501e40704007440d41a503c2c5503480c02c1d01c0040e200001c0d00a00341c40220030104100c00d0181d11020009006114450400400d40609160759800b483c1170540c00700414604160034040042c80c0341a149055880510300703042a85420000400a00003007541d45c19071510000b1258140304c2c8403581e941c113880340c080450f0380c030742d03a2000c044880c2401100c0c0641250003501051110010a008030031061340145060760820790f0b507407511a03001400f51811580001040e019150381102c2e8000c04002001d007800b0544c50900e16000f19440d00d0141c0d10900b5003007042c0c07080f1140e0340e0281d80020410b5403c0340d82c00040310795003050ba103020b1b10152507002e00180a1603c0c1c440c58941c03a0740c00d600c101005801c0c5030401303c0080e0344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 482008282 1250 482007032 482007077
    0x90c0c1b060c0b09011107060504031b030e04091b08070e01050d0f060c050702040c08190605060405190e040f0605060604031101050c0a080a1817031e04051305060405060a0501 77
    0x103650795480300c6d288610008207101034140c0d6402800c0c0090f250419140c00f9000d440203820220b80b4003464608c1d0300c0441c0d00404807070f500342000d4034017240c00c0000d842d0200188881d00103040c50301410032030200c1c543e1400206101a54007014000b801c036600d500420050340203540c40240701e0f109151030000069482d4020340b20712105400c003e4200022580003400b03840319003403600c1c002014581000444111280d5030460924401e00c208403e070b0405011031454030442c0680c500469041c40c01305000000002c4410007000c2d5090b004505041034078003807a2541c071045051f0750241c2482c0201d0024500b65044a04880d4040602c0c442d00f040d0a005540b142c0101d07400704018000c035034803880440c40802c01407160942036030b240200308a00c00b0109204803459007014044174109003403403518520010450302144688c1103c50355140c980da10031852403191740c00130780e008402c4043e02110140960019401540304880520130f503501e403401d220100803940301c1c030782c0040c10f402020203078410401c0c10f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 482009532 1250 482008282 482008291
    0xe0405060f19030203010507050a020105070e0307060e2115010608060609011103091009080f060907090e0a0c080105040c1502120d0906061404050705040f03030f09090c0c1b060c0b 79
    0x34148410b54130340009007140e00c200c1e07801021690000f1806d415950a100341c0f41d02c0817240c24025620001c08010942d9808a17000e48424400c4505280300c0300d0347c8041804003201d402030507401400c000320307000c0354840c62816070100b404100d520002c9034041c01891013511511015050703a05041c0c549004590401c510755031900c85001c20461a0000c0e2a51203100700300c1c403040c0d19540456450704200d03a14091002c6803c101d240c010b1002d1050701e45000c10a201151305008002c1080800304c0000c1d814002030a00c01801448080e0001500358419040b40740f00714015042c40e81c030720b40e85403004520301d400320b641c5000580020240700004130f140b202030074560b03099400c009526441d03036440c0d000f00c520382c1e006501d500d03800d4a2500c403a46054003a05900090030b2402e941054507049404d5440c0045000090034070100c0e025070403240d4495800e43c401800d054000303206041d03900e0130140c1041d004481c10b654981004041000307030081d49801108079000d03903131110824001501c504e000d25401a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 482010782 1250 482009532 482009569
    0xc19110a0b22050109170c0705100203090a0807080d300e03040308030412321201090b0f030f0d110114040503180f0f0103050a110c0d0e0405060f 64
    0x110728241c0c6140084494030b0900c07030800000e84080b1424039a010b206026802e8600400401c00c0c1d02c000c02020581408031201070700e82c1450012444400c2e8218000c118025070000781940e00080c004c44006580c0342115100070588041662170394088031021250880e0080034014480000c924100c42c0040e29481c0030100c2c0006000600d10003801c1c01c1d58000d5006803040c180200620007032003103100c180e000201003070405c00201030345050b052061b81109144929481c40031160303021030032803000880c1c0400820800014141d038407445900000c0403c409500c2c0902d82c0707024a4a4242000144903010500c240000d0030745000059040b92018061b104003400e55403128541804510301c0d0151502070740c4120065515014440300081c080c041c002503603442000906901f940c26159000b0307000c540740c401e280c041203555454140c00c000c3e19503800440540c003000641100d5120010405407400c8070640d4030310011504180400003520010385d01650700807040d5803503c001d40741031b0030244010141c18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 482012032 1250 482010782 482010811
    0x13060f180e100b0a09090b1804030c0326092a0402070f05030703030606080f150f012309120c06042106140f0a140c0903150c19110a0b 59
    0x10102c050568004150410204a8255052001b41e00b030780501c0c105500c082d00c81040000310088c0e42180d8141c05480641030041540c0010700f414410180e2200000303a41c614240101050440c04a03000002c850040300b0b401444400d545101007408100c02e49000405001c0c501d0034030404200096111000450310078840e0132041d030004100340060009140640c4001401070329101019001c1c03800240450101c4203101d04100400d00746a400481d64101503a244c680c2c58014401a81c0c00948030b045a0120184484801a5051508000e0484510684121a4948184003800c1d65882d0000c0640c1c0d0008041c0803d00000300f08155072503c1c11600518042c0e040500e4445208030341003024900c40e1507520034200704505059000654205000c01400c0020b1104440d01000021026129032440783c400071b149806070342c003002454030070800201c02c0002400c1540d0160403541c8139080d40300785000b0540000e07640b540100a00000051302001424008149a039482d20000008201e8159003018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 482013282 1250 482012032 482012039
    0x40e0d020c1c05011a040b030d02030406050723100e2b05190c110a030b04020904020a05040204260106080a0f320111090a0b030c0702030313060f180e10 67
    0x900030b10700000f49030090411621703070180a21068403e00741c80140039030b100c05407403110039a0001c03c48048401c45e00c1d045440e80054901101190501540d61a0500e8a022504043c0801040100c10f083c05560100503142001584c0e0341c644600c50240781440c800492900c403100026010305c405480545442441d0040219460781c0f03425400d20807800040e510350f9103004210700c560300121600c20850304a221245155107150340c407000140002c0c00390840c0800308045480d003101e0701d0040c2000600554940e03484000c10b4241c01d1042c010802e1402c0d001118018040e0184281001d44801d480609502e5080c0d0b10f800c80395848007101114101c085020b0744908144e80090901500c00310a003620203036004041c02c07030079158010900300103524104680c0c001680d440c90f1003811901c1c0c181c034003600c80d030f600d92a0701924041e1600294060100240c025810310009490b07400391082c1e40c544000c40507005408880c1010301000313200c06061601810b102c0b5101c5c074003103103512148a84001446584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 482014388 1106 482013282 482013293
    0x30f080411060a111b09011d0c31050102100e06130f0510050f07030605010503040807020f10052d09190f080309040e0d020c1c 56
    0xa200303c000c501407808a070491a60b03030240c1e000c16080104144010011085813441110341000224108900100014915440f034031300e0700300c40d544c0011031111b99100d0020680701060004010000d0310406101c811126414040c84181514050000e86071901000700710f802d40b8104046101d00442c001a581d0740b02d4819003140c00314420702c3c14500d201c40000c0c000a0300d9070042c00d9a25040f0b50441d00039500410580c2030004035030b5503258045040744d1a0380160790019004202007404610030001902c2c425000030108244000c1c0000000c04424034103429101085010403a20542140d04c103c90005800c5e13807540128003e00c0101060003846a010400e1003900000c0c0c049046400b0000706130007802e800020b179040640c61f0404a5640d41204c1c400038841c50411076082c42d8120080f44001058441d9001080c804d0385910407c1240c1c441c1406e2030080c614400c003001d001c200b = true := by decide +kernel

theorem cover : BRFrame.Cov 481834532 482014388 := by
  have h0 := BRFrame.cov_init 481834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 481834532 ≤ n) (h2 : n < 482014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
