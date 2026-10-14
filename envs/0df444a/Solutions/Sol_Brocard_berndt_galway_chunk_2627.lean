-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2627
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:06.894487+00:00
-- url     : https://prove2.me/submissions/a7e0a6bc-fec5-4045-892d-bc2cf8469c29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 472302158 ≤ n < 472482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 472303408 1250 472302158 472302161
    0x1106010e060112090819050d110913150807080a0308060a031e030e06030a0614030105070926060702032d03040f0206280f0903020312031008010e010f0c03 68
    0x55a60600080b004201e24103a18040d0340013411141c41106450f18101081c445200d40d0314101e04985c002c5480810790b40e071001128017070750f51038002803130081d4642040030b00002c1c00e207014190003420b0582d95030241000c0e1251240010007a00484040740c0d8000ea941580b42c3d81c815042404130001003840d4040b40c3c0034208116404280d82e800700f01c56888405d490002402d808058074240c0c104a40014911060b44800000b18055130b00344e200415082e0804801e2035007101510307403040c041d82c5484c0400c1010b07a4440e400ca001d951024602001f503c111032540c02c87d9480007020341a60380515001d102506070000001d29290a10008001400c1751950030304002c1542011010888842080003e000485140310804c9140c0f00802c403030309200410440c3e000030035102c0301010036100d0300c05441401607009402280d10f0078691410407082c900f035071f01280c2c035134131100d0a80c440b2210100c0813494031040d040101c406043d400c8002c004840f20030325400d01900c2040c0d40b8421051074020b0305030308588203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 472304658 1250 472303408 472303411
    0x30a14010b01091514040f061218020f060309030d050a020d2a030203130807030806191d0403020a0b0a05040b1308120a1b0822020102070b16121106010e 67
    0x10b04100d60041413810b4140c46441d648520210185001c01000c038000c0c9040041e20050803150f61610400c101e00e100c60411106482414602d1800018030b184c016a14144400c283c80d00550b44030740c813625020b883c24030703501811442045450400c1c0401014403001c3e0301600018401030070a105090000c02c21400d41809141d11740901080c061034851420300a40044d50010307040c0200c1400c0410503100c01985030084002100051294810300c146d510704080c1585c007205030490a40d96591a080344144045542014500c00c804036000083c2410300030f02842103182c0d0008071a140300d182440c10348004040440f01100c5100c24a40804d908016144940c0d600c0c44e40904107510300750781003074544a0f0300e10042a80c2c01803506c440550703110f840151075802d600e41040c0c4a1200b60305081038054000b805070f60b10031a07500c1e06501403e0250b07a002480c441120441c0d10042c1e41c400c0340e02d00b4100b24035a10304000d071051400343e0001e62080c0d0712000495114480c4420b54055988a090f8007141a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 472305908 1250 472304658 472304669
    0xb03010b1804150509120309120408011e2304020d02120706110606010507020405090c03070f0509011e03030819020406080601021b1e031f020309120a0f0c05010b030a14010b0109 78
    0x210f9000101483e400b001f190403190110498504610320084244142e01c540c101d90400d0751220360904030803035003034010300603408081c10500c10285c2400079054050420402010741c485034a0105080d500c0394900d640c0d01d160050710514148015503032890f0703140f810707204600004174450703112402c2d801c0210714140100f03030503500c0358a062066000c00c00503140180111400d80034000d03c0031050b603403c008003002002c24000c2850b15615100401c41c46900507448007142d140034820700e20581c0c941700540d80a9a81c507060800c41c036100d280301491800c50503c03048141c5440082c0200c0d0068001e4a0144213031700907801c884404648100302000e40301c9039881d85401071540700d2000d042d8100b01c20744170312140d00501111810b00010304040780b03001041c0f02c1d181042d5400000d1001d03c850500ca45106000404d011600d0507400c058001c01e201709211100040204031500c3c0380c10402c003900550060307600101100e596440604184400d144010b0102801e5031912688005650141290004540c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 472307158 1250 472305908 472305913
    0xb0904030f141201090b010f17010e090f011a012709110408030f070629060f162102030403050319030b0402071104050108010603020603130507030b1303090f1401030b03010b1804150509 81
    0x920700b003105410000083c2c405338890280401540c00c1c4402440764400c44483e15407000f0405040c0703800980002142e60341601c0344039100034411031201280c502c480c200e59105000061100525441200c64000d0b0b420802041c000080c14400c044001d00150407c0d03405048100001541c81c1c02000c1c543c0c80e011000052501d800c0340f501c045140c04c02c050600317801c0c13011200e8680701c0c9030011b01d444942480411a4040d400881101007246100d004242c80d80050008501e81750a40c0c880300d54a01072104880d008200f40d40d00400310a12a400070140e40e54003400c00e544400d401e10b00700d030038081c42c800d5240c0281d180400008080805018020840350040e141c00d15684407802006e4a810800000707a82d1031007050340c0000000c6c0030038030f034512946c164081d2400c0c240d0180340088c85141598064501c0b420207101c280000c40403039903c0c205400302420001045000308002c0303405012488020343d481028040022050900f60024070320071403040b410403000c10084c484100448805844811040d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 472308408 1250 472307158 472307161
    0xb010f03060b0405160c03030b0402041d0f090715020a02040615020f011a041a15071205090114090a0801060609030c09050106052508040b0d0b0904030f141201090b010f17 75
    0x3c0d01414a20203031b03a00915010440b403000e0808602a0390156206000411085080c01c60044100b50113603080f40035030041142600308951180d030349000c103008028412216540d03c0b4003450003004240c0744551301400621100c0d95902405041c0e10300c15a5600242c080e1460181c041c42040c42055210f02017000f1015400c000d0406100c002c0080d4a002598038440c0040300d412541c965681c04c5115030105105a0fa518440c680941160035840441060240500290080340c0e040003c03004034499601d41e880c1c03140d07a000c0024101d64800e40c807200740ca51800e40c02188031540f08003600e0689000784812400c0a594408035001c6490901c0f5440001e08180400341c41c110190000700c01004508420700103505c6141c407005503681c8140e00030031030356600240e40e06801c403480c002c030551500202c4800b4080e18154601030080e540000b880810408207002d07440f41c05002a01740ca0414100c0c1608980a68540ca1842c000b0418402c0722404211056401c0800610424100380503811040d1505100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 472309658 1250 472308408 472308451
    0xd050d051b0d0b0d061b091d0109050916060306140102030f0d020c240717071d18130203011d0c06130506070b040b090d0e090901090b010f03060b0405 66
    0x704454191598041c4001c0c20140205d28680169088803144110400c031b040c000400140c602205035210794030844c101c148d0040399403000c0b04000e046500c0c071000413402d40d40d4030070f00905000c3c81d40301d41200c022502001240c0e690381076100c002955100f40c0c001110842802c010382c0d0360b00400c00faa450442e01007000d044102920f030050202c00c2070000444041350040d000c081e264004140480240d181c600003000a042d50111244928a01945031403495003084240180100a06480d008451400030308026140d1150030b00e80000301035007901c5004d54140f1000c2c2910101180c0e41c103134803a40c240132070302801a140510407424480510b009011003860300e014443c2035040400344080c003101141000541d52280c500502e6241d00c14048400746113054505a074100728050700c40c0103170f90300c100c2d40078001903000b034104002c0329022130359880b480c0c3d542d440709405080d08510090152810400004010760384075054401d49100e01d074184180c036038040610084510031204901d6424043c10007600c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 472310908 1250 472309658 472309661
    0x23010608061806150604080d0302030a060605190e19180f060503060f0703060b03010909030f0203130501050c010608120a030501060c0b0a02030a0e010501080a0b1b1b01020702030d050d051b0d 84
    0x400242c003801d558180380d5101001e42c01c2c000405c231000003194000040000002940c882c1001408e1141491400c2522401702c0004007050400e82809010350f04c031200c525942c80c0c04500409403800c56225580c2501d0b854141c40074079040a031000c01d20700b08881985404114040c070401c0d954054028403941c0d40e0140d0401e034449001d4551420f0568968001c200a0340c100b004501034030b0200c001040412180c074000307100d00b020480103402c6420071b1100a05042840c503415080b28002d10f8a2501d620351150103900404075075100e40200e01c5414840e945e809090b40c09048000c8042c5c030201308580e0b95100946090001c150f005040140c5000003e440f102c0130381c0030b140c01c08081500020a00c060f00d01c0c0d182111310a800000443d4000c810840401a40070384069001d00448020360300b60503140e00c0000b85000c1c0000916010b401101242e0030300c00250705403952039400604454419541950180c52039100407401f04400c0d06090000b012040303c0262818402c40c60f6403442d1500061240200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 472312158 1250 472310908 472310941
    0x80606060307050d092312040b0901090902180a0b0307050a03020c0a0c030c080d090f03060e030d060b1306020c01020607180323070e0705120423010608061806 70
    0x502005025513035986100380301c5c0f01d0b0340d03038400c00c0e1250910905400c0324400d0140014018096408903040801031130b0803406590403107000d054440e0700e40c48024010b0b41c4c0004540c0206034445e1002c02c80d0b035141c10a0360729080081c08151000c041e5141c44502c0ca03d494482150340314007048007000751302e040c54070980c018010141e44109484080810303a807581c15202c080c1c0d005640d20040d6031814803815405100c00c0c200c03a40282001d10321b4034038206140c070b2407050034400608400c0d9124030300d0f607100105000319000300584d620100005e0f511a5081c80d00c07a0801b26148034200721000f4045190350000825165440c0160010410355a446504484410040760400c00201c07160a00100107909020300080d800c1895082001030304000700d082c0e00d000364580c00480c0e4804010184507003c0d03000011030b905034203007030140015940d4a080904403500788005511b901c0030300c072020819003201036004400f503407038040c00c1c1d84694540741c2c0c12008105a1003803109043c0c1007078000c600c41090702000031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 472313408 1250 472312158 472312171
    0x51603050d0207050d08010603050c13050f010903050d02070f050a0b16020a05120309090a050121031e020a050706050315060d24030308130305120a0b04021b12040806060603 76
    0x241c0f91090030b83d501418200341888103808186004010f200f44c0d43c140c051140c1c01b4444174446414640038481c06490400f0a1041c6400391800350f10110040c2d1044c103003080a50340000440c0c0010b00e00020080d40c0d04154410780300e81104e90032020800d85004c4a080e001c5030483c07185581082c039201c082c20a4402d81d4a822a4042c154120000302d541701c640da440d840c044408042d5071070703550307840c00e0021440d8000d0042003600d2800b030060104501002c2280c4000003000da00010360300080c9800e907402100b070f40c5003280e045032003044140060f500107049415144200d040e240415590b400540300f038081601c4036603c1026a1a04c040c080c2040e0780034007400a502c450100e05602101009000d909003400d203019254041e020520916401c180040d0700015035442035030300c0d04082d4a0041540c06a070041c0a410304c0000d000c40c1d444c00e0b003600202c402c2c3c60001c0045640b103c04259000080700001100301041c0107055030440041c5249082d24200c424440140c9a20781d990700c1040913030b0388002e00c0e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 472314658 1250 472313408 472313411
    0x1060e040621020a171e010207021806130c092706030303020705060f0112020d1b0608190e150c0d1b08060409020f010e01020c03100b0a0501051603050d 67
    0x510ba00401910310603200e0061611121942c00340140314242c403181e000000da00e003080c82c0001500000181403142c04c800000c05881d8021440307405406442900300195205079604041c0d9940c8072a4881c01c2e00400d0304480c00c510241910031501d040d01d40c00200c403008079114103405c000e8880d01184448190301c0c01c0240300303002112240c51504a42d4140c00a83c0003030707408900c58082060070071020b41c01188072040380d1103541c9841e00c140c58402494200a00070b00da0880c0308410403c40160100c000c8241a000b8588952906c4004141c414201d4242c2100092200c07400c20840e00c0c0e11541d05503084800190080c903118400000e420761000e0700c5084145002c0000e8a0011603038405d0b8955810100c3c140c0580d000741c0da10003480d2440162260340b2407440c080d1004010b90ba03030783d80c1c149054000e00300518003008150040c2c3c24900c406900d150540142c910540c1d103549207500000403003400300d500f03403012616040116400e004020841189503035600d50740d00802c2c000d001404805400510 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 472315908 1250 472314658 472314671
    0x30708060a02070302070509041203110d0516180f09020708040f030303020a09050603011409040809130b041104080a030813061409071e052403130b0105090f01060e04 73
    0x114586803140032a16980050390102e006030801d6070501503076000b031104071510501c030f04007500c07403e80440c2c941405206040e070359541c600141101c201aa8042c4002400030041071418444641501c0c000c0ca4810700064581c0f0a00c00301c8040000a2800390744800300240851802c054081d00250720003c0c06440000061000140706000f5070450000745229640c00f50304ca070012031019100b0000c1c4d4012a11511080c0011710403048038140000c1000b10840d0000c1d0141c4450030401c00c3c6200c2c2d041010741002d880440514600340f00d801c09080c1d9007003540d0420205155003c440064011402100d049810001401e00442c0c03281d002c540d0020305d26901d0301035554081c1e407214120b40080c507981e10b071a100201007201500090040320028601c03101c0f0790544030f2900d10440140c80b40e42c0030391841202071508107642c01c241d815800b0039005c50001c0480c3c1d00d0404100c411020311162408070307001000b09001003943d043c003007180d50042a40002c1d0840c0c5908102c1d06a80d00c43c1103842c80d40e00302c0c0d5601d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 472317158 1250 472315908 472315919
    0x22080306030c03070807090510051e042018150723060a141027020d06141e18070507020306010e07030b010509090609040c180c030c0f02070e060307 65
    0x300c404e008040c0c42c0001c005c480c1c40d15030208269a00184481c490750180c0104100725110710501500308150041d5824000b070000002600400e00c1c034031000500d185c141c2001c00e035000448020400c0c24880d01000c0d410603110410029a001ea69100c0d00c1254401c0c000280055031840c120500312103558940d94030100080703011071074040100d8280e101143c4036900d801d280f44410814503046281a9596402203082803107015148c49090400c00c0f0700791210400c8004003803154195028803141400c00e2100c250750702c1003220f10202c1c598031035114081c07400c0f034080300d404214010300183c0405480d01840d4040d29000f8140d0135801820741c1c040c0001003025000580e0309010141c080c10561030b060903241071074a00101150302480405040c04010040c0c82001d90322a0303241c0e83d020300c08543d4262182d0340c61401841d2400980e0088032a200c82c00903000030b0195a03002003050281981e010050390001800498a008441c4a6000541c104100c24000384e4103c0c20110351158001e003c5424055039803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 472318408 1250 472317158 472317163
    0xd02090a090f0504031b0b07050d0e0a08070204050609010e1308041d071b0317090c03070b0a02060c0702061c0213030c031a070819150b09010822080306030c03 70
    0x400410103e60740c20811040640200390107000d10a441c5001d010600c082d41c0c4c0e406400b2028054005222011480404c10785043d00100a180802010b441e00d000311071030041510b07003007804200c0c41642000d00040d05410710b081058101c0b0448155419039071141c0c05001d000024112060f03032a640200008159200003000d611960035406511042d54076000340d0040581c03049520030000ea840d802070031808030340c0c080f21444041301410209201900c0c1d2130b070300340d26002c40140580e070540116840001c5c5284000701410520b0001e4080d220290756064180f18948207020000394081018800c12071304c0d172154440c1020f45001c403400145407001c7c0c0103485544000c2580100c8912a4004092040240414081d160b10032503a40c7c01d102030816050213003e90000034a4103104c801d412512102c1e400790360b0070100045102d00d00c944900d80d220900001c03a070388140f5029000c01c8540d804111304249002c3c0c04140c01d4000345004c0d01a8519030755004aa5101070700042d032501c914006801d80c0d5906 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 472319658 1250 472318408 472318421
    0x1009150b0403032c0105221e080705030304060f080601030902090a02070302120306011e0c0f080d23070e06090a08070e09030328020d060603050a06080c060d02090a09 73
    0x944500c40010b151307259000542c00075422401c24012400132210150340c02c903054a00444118001721140c207110507256149039010740c031080c0301c101c2000742200c400310307000094826030f481241075940094441c0f082c142d680c0310701d11a0f030380014903940c198022030b072052540d0340d0020414500494248078a40002e51154001e03104000002e500050600c02c1540400081e4508120208840d04603e003401c0013800355414400079505505403240003246031446045d842c1d03104c3d075100445000d1682c840c10100703055000440c031450f03150b19000710a48459134030b40d00901c061100300c00388082aa41c1c181e0454a03107180c448070a0304054144100d45007a0f4442c1ca0740f80c05090010002c0c050036140c80d03e0455036800c0500701961341e820030030911100500708004c80d414180111180c0403039900b104e07140c0780244101034203015032515109000c0b804541c03642005018501c0501c00303002890301e414509881d080c0010311a54451410032421501080700d401400101c08010040e0820543c1c84608000340c0b0720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 472320908 1250 472319658 472319663
    0x30e0d030e090709050a050103090f080723010b040605010c23011518110705030403020d03050705030c0f0c011d0f0f060429090102061f1502060901050109051009150b0403 75
    0x444130410301181c1001e102400080c2001d107428414080e45469142c030038140314801070a48240000c4080900121800b41114500f0700b030035000c0311042c1002054000c0071080510b03803040d82001d10001e8698490b070784001c030140d0000401d808401c881d0070154100c0071100d41c054915500c4041c400d2140b40c01c150700c3d2000307008900140400344803090601040b901c54007081c040c040c0707041c0031741d101050002082d80c0a4070303410344106071081c4540c10141c0b4107000342c200081080c400015880c49a860100e11103946184071003c0724401d081800040d5200450210b41400d580d036492007041091915141c140b0f4100d01c040c203a010003241d072401003946580f10750450509070380027801c0d007500c1808041000c05880d1407000745c10300303190440000039201d03100a00048400000031000d420400401700c13024006144000225220341c6901c4000303506c4e1002190041015440c03d000010059660b00030b15106401140c40751030380c2c03400c1050010091030000c81000c0408894480440d4000030f45000304061030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 472322158 1250 472320908 472320917
    0x90f031f050916060c081e0f0910020111120613061d15090609180105070905040f0e070501230f1801090515071401060e041509030e0d030e0907 63
    0x24040035040d03e091022803088005600c8400c0c10040c841d0b0002c81c107038071117500180f0380d0381d510810040c01d0600c10b0340466500a0383c03000160107003e88a902e00400074800292104182c259840500f80d0881d001c04401c0c2d51140c80c20014056400d80c00c45cac44507032025000306441c290045001c00311044813000d0300100b12001c640b4003c02c5102200c04110341c0d00c4100f400b402d10481651130003043c00580c0c00b50070580111645004511070015091701240e058100c0d4008002910b003042008255048601c98180503a19103030241c803d5140a01a04868103900c1c0014000d040c074110045038002071642e9a00c400544440c010558403001038010801000090301e00c0791244950280e0712041145d500390a0305000040008000d503440c0c0d40030400141101048550700c41d4014101030601e6011700b00c03040095403074803101141e030210441106000328010310403076802e150f114010b04102c40a5107009408142d070007106c071400d85070900d0008680c0d80700740b9002c455010040d010940083c1e007501d0600215 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 472323408 1250 472322158 472322161
    0x1815031407061d0a062a08090a0e01051005090310050a15051e01030f0b04021204060b180c0d061e051005040e0a0e03071505010e0709030305090f031f05 67
    0x4540c80540c603d8070322203040208151800000000d04030f41454480c0e0000c0c840010b09840d414620344000d1540b00030310700a2080c500c0d18070301d0f0608055001d80c4c0924441e00b10940045181001010440c0c1600c0000c1c050f003140d85101c1c0c02c10744041d040b120780745526115201c0c1040402c2403a0240900407460850040744c0700d440b407041d8444156a680119001e503d00a1041c0140d12807406000010003080c2000944a14004031801c007901c180aa00c9800c40d0000403e412050801640c96100b82c2c01030004009081030141007002c480c40c08501c2c1401da02440010450103000c00c001454031900c402000035840780d860b46154080000a03a8080705000b0745541003000341080c80806020080702e18040d8036007030404424544140019002c0000550303245062046101c081003249e1510303802079407101c04851021007110150409001e410580b001000100b090113000b81948015242e260300ca4a081a40400910907040e102d0641281e0610824001001d0084a0052000c2352091200080f1341c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 472324658 1250 472323408 472323419
    0xf061206031009050c040c120207051011161212060305010504060509030c1e031b0a060c080f040303051302041109010e0a050d0f05030c0706050c10061815031407 71
    0x1048042104090b01d6400c0c03410500c0044c02c0031031035140000d0201d80008a0318030402d402c860020780c22080c01c00182c13001460780180403001403900281c040440e070038400800307686801c04003402981e00c051408408405c044000601362901101041c5152070500b40d8010101d01c2c00e020303901c01d94000c3c1d805941d03441c04d000a002e254020700e40e001e14900d00032f41c50540416540e0707680b017181d1104102c032400c001e101d04c66403000c00c6c0704449001d920036045010805d008901180c5030503080c2d804a4a40c3d28005030300055074010310049108000d14800c01c1500c0c0d4694405034041e02005103075042c0c9401d590348510044c1d68070321134101200c208900c1c1c691211649000035205000000d02a440307041210002c100c0e940d2050a0380001d55880306a10304501050300e0207620310300841103020b2081c0110700c1d002c00c0d20b961210107400c41c0d040503401c46a05154140d0010100c65560003210401401c1240b140c21000e4543c008140601400b0804500103540b0b8441c0705401c1c41810030000140c2040c2d07420041d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 472325908 1250 472324658 472324663
    0x1e210606170c0f090105011209080c1c030903020d20011505010905040e06011a04031403030f22020f011206140a0e01060c020108060f13090c09020f07020607020f06120603 75
    0x2c07401a58819510101800003a2405505204050411906c46030f094004000c0c1e030407034040b06a00118182d04c503044900c00a881c0d81c00100d001d055860080c5c248480306200340140c1d03040d40c0d0075401034003440c4841c202c01c035560002c44090385a080345036400c0f031481c3c0c2405d200e0030001800402c640351101c2c0c1020001800c0c0240c42c5e11042c8514140700300c0906101001c15800e0454481ea084880640c130411f5002280703018030382c0060066941141c0741800306401200641c460b0700301c1036640c85c065a6813510000801d403500c41035041109441440c000506100072007035400f100504000012200704808081511201c0e00200079000c1c101109117002d0070600c002c10017030100c811140c146581884001050041c19420203130400400e1800300310180c6814184049090002d40001042c10300c003803283c0064a440141156503160030800000e84521610982d10011450700400c0d24004644c0c00304507481e000101706070386c404820320700501d85a0f00c0f00001c0120300b041d000da0410070b2406c4003c150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 472327158 1250 472325908 472325923
    0x41e0509060a0b04230303070606050103050610020606130608010c0509040c052104080409180b071b14120c0a051002040501120e01290a1e21060617 65
    0x42c010807918106110460104041d98103544c401e660010740c440c84251480e904030501c117181a01804001461b6040c4062604001d0984800381c800f44081d4841d0700038800341102d10003681c0c006801c4400403070264038024501078800e036a4450041540c603100c10b4100c0c216218242401c000c83c10018210240c2c0c10075014100d148021030501c1030401d0581d003000d4060300103905407401c80402d81000101000300081c10390f13028010455080107850b030840c0034880c210b902c2c044243e50000d840c01c0025580c5104821403a94101c00501e0324050500c96601c4122002502c05144414000e68042e50701250140f0040c2c480301a000c001020ba580241c00d00303e062640001d1940119030041005002c0c50340c0158800c5c1410400c102c2c001441c02d402a0f20600409031000400610400d0b5000c0d400144400542101419400c5908400b0150b903001568400c2000c444d02c0c104509a008041000f940c400202d662040b501948411101034a035580c1c42c11074007281c104100c040b08180468031091000c10402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 472328408 1250 472327158 472327171
    0x12110a0e01120525050403150207140708030d020a0c050d020619021602100c0b0a1506080f06120f0303090601090507050c100b030102070609050c120a0f02090705041e0509 75
    0x403c410f061016481d80e405020300c202100302c000101c41410070701d00c10070840d002550460081c09080b01c1c0d51142d02c010394044070b03068032403103aa40c10b41402c80703001142e0001120a800c0081d85027802d01c001c203102a4000e5000d075818001485501c1001c540e050045151072070041c0d003d040f203172404e841e2003c0380c80525006400d00314030600c020f03203a62030540c031445010780d01100c01035496020103608a403c0001440010200901c1c02d0500c0441061500910368540144416418454840c10100c4c0e0318074046a03502410000320b808642181020000c442808420009480c241a401104949503030300a1f14019265448600104203402103481080d80051441c5806483c002c111600d0a940d100c0c0c00032842005995084210102d54096045a0140b6404070040c44040c40c581080d0b501c80d441c2d641c6041c010841a940d101c04608003003015043c2960203100501c6000054080c40340c3d95600812140601c2410080480d0180d50030880010f010a0f40c14999403140c10007041c08070051024044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 472329658 1250 472328408 472328411
    0x2090913030c0b04020d1401060302120a0b0a1a060304030e01120603050a1b15020102070c0603050408070b0c0702130902040b010503010f03030e0604030606062601031212110a0e0112 80
    0x2840000ba0300003803042000b034200c000f55415840d5400080c081c0381c20520014010421003600440b1282c064001d94100e0303000310340880d90710701e03011200c5440710f51580c00100b001c50101300080d0301c0002903204605d5840001c5541800b203200340c021403c4c0c0e61064900742c0c041666a01290702d25a8085a403510400842c1d9043c42403c1c507680c0d4450fa81c03408884000e055142c1602039111180b08191100010300c3c508403160448100584060f000b075200400542e000b890410001c59000c3c0240a03d90017154060703801c40c5801d40b1a2100743c0b00c90340181c0705017401501000401c01584d502840794000400013200000d048107903204002c212074086541030f041c081c06000411a803a1030b01101da0481e23816045c10719a40340244002400d40c403880e04000d1440e49071a001045241c2e202c0300c0d05081d005581a001c0d444c116404003051409400d21008007041c1104d030700c200c1054841c000030031342c00c140140c0100ba079049801002c0c10703e8201083e0500002c05858000707842d580e210b0202d01c440d9a90490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 472330908 1250 472329658 472329691
    0xd1e020a18140906060706150f03020909010c02030f1b10050108061608070c020102070830040312030b24030a0c260403020f01051f0506090a0e0a09020a09020909 71
    0x100343d403914010801882224080742c2c4d802444505e80000c904480184250300c1565142c2800010544940c04140c0c05081d09400082c0000720501c504003e001c80d0703030021814581d0900489940d07a00944283d4181744401c40c140100700f80811000900c90365404c00401c1e13960500c90264035020340105180003650616020715102a00100c0c281d03007021441c0f901c2d80f01511a0300050b860010641e0003030b04030348a200126400e00504000c0040e000701400c07084000d1341c1c4821903680550156000250040c40c4489200c41543d019030f205155809015144811412004e62580f10a05c41c0c1000a2050701c0e0000030049a00561b108600c0703c074816043c006440c824804903d81c4440080050a0984c68807501107001d2500801c11050881c030760318000e00442c58034030307005801e803e03070200c0003926444c00c02c1c408103452414005442c041c407809041400803900c0c203c28540b030702401600240056959648640268071001440130281020303240141e941c40b4a034051000c200b070000e0000355403400112 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 472332158 1250 472330908 472330949
    0xb0f042a150c020f1c0c0305030307030e06100504050a06080607020c010329210303100e0705070201020a060c030204120b0f01050a180f02090a260102040b0d1e020a18 73
    0x21213011585106640c0002c01c401440510440c41400001c0030f000c03a04040400010441300000941c030a0507159070a0054030003040715190b0b550000e40b0b4164100480c8103091180d810b207079001680c4000100030100d62180d40e4140320b801d240303059890340c00581004c0d80c00c00c05541c0600906404180c01c41481c42510403040d411340c042c201e0a0b050360b114102d030311046510700c41404410340c841170140381607a6a904181710090f1031b883c12440386000c58074a9000081c4414011030544003640d8060700a481101c8540d81c41c0c00c010034110202c1014142e0901020440400d40189103010300c0c0b160110202d2818504034849a00205a2149124070700b141c3e814000c5001c801215010000310300c00200310466440d461002038010340f000300e40c004a0040c0006000c405c41d101180d9460750440c8420404220804414280d20440c0240101d08000300100c60390600c035a400807044802195030b80346074501c0c040070b65040c0d030f01070320040000462802103011580080307140c2c90010221849003614248960 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 472333408 1250 472332158 472332169
    0x8191505070c06140624071b0e07090338091b0d030f081306050f07030c0c051c051e040e0106031518140708150103090b0f042a150c02 59
    0x70241034020348000031280e1034106c00600f9920703444d40c885540d9a41040350a21010031070105e10500d0720028403900824030391405003032584103480e001900c071494005590010b4009541801b035022003480200c0c51446d240442c99001741c000c540707510160843ca00304c03414054070351042065003803144c1c5050300c170b4800003600100c41c0300d80700724a414200e1079961407903c400100302045002038012410002001400005c61515a1150075562000c000e071041004007211400300c4600c004025611413181c2411100c00500303079210f01c0d122031600514100e0103a40c20b40b0107544e20768110903208800b0805000000c40003001c980940307a0361404120b800c01d0402d21140010582c4540c00c039441202e8101100d225264000b8000e03844101000c52090401c420010040e02c4212640f10b8640d1004411201541c42406101c0c0d01a0304444080c0d02c54807904500c103954440540120781c0a102c10b20840c1840100482c580c40c415098004035284c0b92070200221410b0070320580440800c400c12806200590301c6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 472334658 1250 472333408 472333429
    0x9050901061e12031b03051308190605130807120e270a060312020a121b12110a03080403201b060f0f07170408191505070c061406 57
    0x461001d041c11010b0304085c3c030480c84c0c0c0b80d003041da80741844d1446005c1c160000c00900141028424481c1c00c940e480050580320200f8040e00c604100e900111540482d4040d04000d40040780d0710b0300c1c51101207042c1d66000003903101c01000c440300c48401051030303000c2da0092911448110700b80ca080c5452038454101807000a1403140100c00c10614001156503802c0d141d01c0000607591180c20940d90358080c08000e03513a20302d84c1ea411034055811300c008071500c40c4103d03400c50700601c0d400703110315140c14980c0d6510b058407c007254490800c1030035214070142c01001c000034903045019880340b03081070810b070600504d60303143c1c0551035003d081c0420f0640304c507860002d840360689805100d4822010209000500c56101d49040e075280e104010942407a01a484401070141c9032080501c0d00000c81707030b02c0400150780903a1240714a207401102d210b40040c422072510600280c4107a02c171542024440d1001c40c1200d005030b891800045803003541d181005603c2c411030301c5000c0d00d1213040141d4a440800500384400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 472335908 1250 472334658 472334669
    0xc08010b0f0c071205031e130b07021314100b030f0a0518070602010e1903080f191107060f05090d05090a030c090c090905010e040206090f0a09050901061e 68
    0xc005000541e14005000c00f07800b61540003140c0207004c078a41803040d0359800c0302c2c8007040c40c115030413240c510f101001c3c400c4407440c10700780460051007450b103640d54525800903001070307801c0720302d28030915041c0c3e4540c03044921080c10b4410a4040c3d0404483d0152250341c26005000303403200402c14010083c1d9140c0f1255448001c103400418170f962440d50f40640c0300da000c04040d000d4031a41d48082801c03074043d0007242023000a5402c031000581c0741c4504c401081210b070300290100340400d010410042112203426030140c500110245e0740890340000104448407070216650301007001c0355040400c0264080d400100794000750901c8941441385040d52104107661900c0103006001860040340e40340d1044000007141c101c0207400d00c82d5592200d40d0007406118841100040a80c88013082101d006d2040754161240b040310300b58161ba5590074410a0f03170010540350340c00308200560040c26600c0240c010701a006020012a8605040155034255a80c1e034001c2c0d6511001c1c0c03048514000d20304500c150031501d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 472337158 1250 472335908 472335937
    0x12020c090103060b041b11010b1f030203060604030c090501050a05011706211009051203010609050f060910020a150905100203070903121106070f0e010309020f1e040c08010b 76
    0xa130340400040041504d26a070129101c00c200b20504c58036046140100c5812070b078030003803000ca19070004209224012401c0f520021001007840071003144030342e01955000710040c1c950f0f0301d801c1c4c030f036100c0000008a6600c40c0001d02c1e03e440c018481c6040003003100c0000c00080c2807080c0d4100290344415442407000305070764061403120290f61034100310700400300d210a080c501901d2880800e561144007400e0030031000d40c2c0318462441c960381000c0780c0c1c1c82103d04039101592411822030401040050020402080c0c1d9032054061190406581ea50401240200c03d41c0c1c00a0801840510b01203280100440d030b000f00d200d14198242e03020034008a143d403c1c0c18941c0e078006a5a0384e6402003942c58494641003d800321200d42ca6a01489400101c10000001401d003213400a41d00c210084589196001c50b042c0041e144211034442540a034021100d1107100a0496150300f41c2e42000c1180c000000b150041ba03a00c503c11141d0003420107125410b031000071407500d40745640c104021038109100b22200800b420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 472338408 1250 472337158 472337171
    0x20c010f0e0616051b031b0a05090901021c230604060305010203100e15011704021513030204180b011a0705030d0203160c150f060e011212020c09010306 67
    0xd01c19210040e40c004020025038075100c19405004480300201000c95485c4100c0340c24440841000f1117800700702100078000e20001000d4101000c1c00002541202d40018207124080340940c0c1b04c0301068814682040016100c0104036003916204203c1100c400f0600d00c0d00f0500c1443c2e590462011034a40502502025561642d40108000300302c9036002505a510201c1800040b04840003050107c0d82444c851810544400310490404130300302000502141400c52070740e010044c42d06246a109000a100340603180881c1c8280d02c16900c074950005040140741c03000d10440c609440303211061411401428074103080c5941d140d1154030107014a40c42100d00c40c0d2044020101082220f11140d408410740751901581440e2034040c0d0030036150401d8070070420340034041c0c0610403894800040d401201c4040c1e03d858200c60306005248040390f0720404d580716400440c00d0388106041a0091890000c1c640e1a003c140c1010000d03070843d004083c045400015040000e96a048074241c1900c0c3c0201000509 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 472339658 1250 472338408 472338437
    0x702091f090c11010e0703022418030109020d0c17070305120304021f050306120309091b04030b13020102010e0d020304051302160c081002090d15090203161a0901020c01 74
    0x10400d400118251582000b45c4403003848404141d00040341d10035a8810b044000c0c000c41d0280000c00c01c0303007000e0b91800c24403d142c041c1c84d07404402c004096000d400001d00f4540c54000c03446044c00c294041c1c90f0a104d41104200c085c40b140000f40c8400504800f4200039030540d9a103071b481d03103620000c1c003001000110115065541d9010a00c003030285090015100440b03090b400b130620380081320031a01c1068500054440500007008640d4030790300041c1403c1c4140e450f0844001254200c5c00003151103034040c4000310010f00c0d02440940a482007800d07680003079640348002800c3d00c51300c501806c0e00b038000c1903005070000d03000800d44080c3c1d0b900300c4503c181e0100d43d0030580001d000c0e4001e80010700017442550401e01007625421401c3d207891006840e0701203402c011540582c45503584154008182005040101c0c50725110700c2003402000d2400300b107542603a00040d1400804405000080c00b03016400c02241e800080c11050f01c201002c1c6c80303410300c0301d0200040e4840b8121154141805041c1d49100308 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 472340908 1250 472339658 472339667
    0x1109040c0b03090c010905010504030b040201081f060207091b0917010f14070e0406060f030921020d02010506150a05071a070329090105100207080a080702091f090c 72
    0x141041440c0d141d00c91600c4021684d4481c103207851140452020302001c140b6510501c21501940d40144c0d52000c1c6072656070046662802c018000380060b21000065140882600710b030b1f1000386901e5000f0140103041240c480b049403051681051601d920021121207540c0105956080301c2092500c0c001c2800c00500441c017405041c905409280e143c0752a01d518a208040e20302d014020581d40c5403a0b0120880030320045524900401c0086442d2414400b01588290481680c0074443d5004d0808618680007041109051100c0c020158002c0c0c21092a2907909200f06680443c049501900d0381c01800c412600520401e038203442004400145402031202c0b032410341101c110042d0b013000c1180380c003038030050041100c0c245440f91408070300c0c02c4107180c02c11200c0c2c1d184003450040c03807581e559203003500300b02143c02850340143c20340c0201000051051010311281503424000c503d003c0e0340c0c2613544104911180e0042240004a02030301c0100c50504807022a074043e10100f800003d19442c0340300d400e94 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 472342158 1250 472340908 472340933
    0x2030c120309131b020610090e030c01060b0418020301030b04030804080702030d18080c1f0c081c0609140414010b030303040c03230a02010503060604030209160801050409110904 78
    0x40c1c02c05940001005900b0041d0310820032821184800502c040c10407504a8840786c1c150340d081c0980705802400e0144603034030350000403142303000c904403890101110565400d540280d482803440703800115042120080b00402500268403150b011807035581159280e6044076005070001e01001b034540d000404102e420401c6800e07554000302100d01d519016040100102000b03c9000c11045001000003840d030000101c000b41c4070700040251400c62000c0ca605e03d0300c03c0403200c1c030100700020305d030441d0b000c507818900510070360110081e1004c00381d454172100001d6070b0041d882000594039040c848810100041d8900740c00a9008500c64050100401c1042c0074046401000358107000000c1844200b21881e03094400322481003e006101400300ca51144807060180c007031050b5030b04030142050040d8840e2004541c445001020305091503100d8000c103075807110071101c070221030740000c445019094202c0b02490050008075400d00840c0e02c81e5a681c1a503caa00b9001400340306900302107000c0040c600b0641 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 472343408 1250 472342158 472342177
    0xb0a020403140c010f020f0a020d020105040b0a03020301030501142202031f05090114130f150f02070302010b060307090311061e071407030b0f09012c01061202030c1203 74
    0x41c00440c00c0c060429203c41d40104002d02140f1010700c20160507001164000c40c9500b50800340c03050061741d40a010301c03807000300d600302c0c1002820072021507605030080107000040300a0360016129811740c81d00f1030031940541c1540112510900130045c584615031140100020404804800e4228601c04646003956118201c0340c00200e1001c0803005c64415440315118040b613074000c1c02010444505d4079261982624228120002d161140c4003064007000c2001089106c1c140c0d01401c18000d070b82213412500c082000e1542d40360001403100501d54240101001c08000716201807450600038000b5088030600d2000030900745620314103454030395800c3d00340c0f100a41c403245911200f00301500100d04a9000083c01c5802101180080340b04c42c10008000d402d9070b60254079201d0a03219101013240b201401031040c1002d64840220800c008d0040c0d01604414084c00380360a2042c0c5100034050940744d42d80c016084c0701c408511201c005d654000b624424258040d035a8014400d43c2a00c02400e502c1085140b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 472344658 1250 472343408 472343423
    0x17160605071d0d12140c010911032a040c02010e01020706021b0a0f150b0d0302010c030c082509091a1003090201090306050c1303050f0c0303160b0a020403 68
    0x401086681290000009401e81040c544040d00d522041100812490f0805032000314003c8030035161500443c9182c4c0c80d181c4415038141005400c035280c80c20b480707100307000700c400e0743c0040c1b980c01040c00c04004203031401c40030002104100510190680a203051980f00d070b0b105680710034014807542d000707510691200c1c04030720084d991080c440c10040040d5200c11320034244c1c81042801503059100224000c03404a0740403210122000350b6450f611081981165000c403120b65810510655680340303140030305824400d40012490b0505501d01070102da0450340020140b1408904108003501c50324418a079114a4030402c0143c280100000c640200298000c060306529150f59658040c01001540c000c13079408890341c07401e200c0d485404400340ca8103500000d0202c2c1c89a60f01340009070381e5821965001c9860b0f8541410300480c0480c01001e00c41c40da0040e5200c1d007020324074860741304082c8003001403400c0a8008601c0d05070ba0807150301c4000544180586082d881c000880e08600c0141c0481d4011a0002c06 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 472345908 1250 472344658 472344661
    0x11060708060907050d05090a030f140a180909051c0905061603030e06191503150911030d030b040501060509130b060f04090b03010b0906150c01021b07061b17160605 72
    0x4403d0307500c10f030008c03003900451004400e100e0118420340061180301c2e0304048039030a00d120204256000e12020f814913511044940002c6050349a900c10b000340c0c54040c2004005010081c07a1309842850800030070010000c154a050240d9110ba5045038803101e0b40942003400720056081c04c800034000403415004030700035030b000e02102c80c0304c0740128846101c1c85041001542000e0748a40303e10001480002c20102012600540b04903035a07104456240c090954050084001000641003040d6820028003095440c014040e0b1400c2911907140540101c0c100189050003640020301040361499003250015282c0c0e450210503240d44007a1044960080400c6444030307112a03c08005d800701c602018007035841d096443c406403501001290055801620141100d2054003c01610b503204442008496408100e030050f03007125416132580c140341c0c01001c5c0c580c06041c00c0c0018044114404150b41c80800d00c1d4105011440c2429400c18048001d034403965201e11100d0f8809103880c281d2005042c041c913103030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 472347158 1250 472345908 472345921
    0x702040906050f01170724020a060c050c1018080a02150f150405101a040b0408010506150f03070c03020f060405030901030c181511010501140111060708060907050d05 73
    0x401c05060301e503a56070545000200745c0c60150b4540c0356100e00054400072024103511110440c0c44207035001070901c169134101d042a2125415603080c580b0b02c10000d90001400064408244005608140c00a1707090180000c0204403098402c145003025100320800a04405d545000308100c0d500e6903400c01d8003204602d0400c082c01081e41040f2039400f001000001858054030b024440c0714883d034501e4502c0c011090a01902841081e01002880300042c02080302050b4401d060001d040206030180002c12a031802105020480510360303444403d905090114811070144902aa0b60000603440e007000800520708040385401c00d8040400380300e000e0102440203018000c001444148402e88003481009030b8460200ca40440800c0d101d490104118800e1040f80b5500c0040a0441c0003803412420b4008600c8185003107071401c0e803000c0d240002581c1c00d12641c1d6000507000c03869025000c050039072490100c1d0f002c0d01d460002408039124261000006041500a80c10340e07003e00c015030307000c122a16092 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 472348408 1250 472347158 472347181
    0x606040e07080f0604051017120418060f0f05040c03140a0906060f050d0b061203160303060506042306131403070b0705031608090d110f0301020a0212070204090605 72
    0x607222070b5200343d25580001c1d039906042c05124094913011141c8185180b81c040181480300440184104da03000b10724001c41110700b410040c0000d010f00910349000703100404924001c5505c542c1c4044140d80d0a000100040b00246807003008032181030794040f600105184d03045008207000e9581e0f40c5000184030502c00c204a25601c950b1005110b080e0030070141d602c0e40852000c503010391141e258001c0d950300c03885c000208210310b80740d003248004d00307502d1845100050b05410764000c0401082c480702004001d400b41581401040001c040541d0090f180600307110201005141403079100b45002c50f60001400b071500c078201103ca0911043c0105000280c4889403540a05501e084032271103449030f0040030134168261422550035640c400011440e00d02000d0304001c2840c14020243c0300300d0f0040c48003285a40710302040402413413203280c1c031600820051007002400c0525800780b40c080c3e0310520502c0e5003940c0004a00c1e44248401101c2034407100107100040141209050041000d42423109000840059 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 472349658 1250 472348408 472348411
    0x709081902241e0f0a20060108100c030504080d0507090b0f07060e0606030606010c03020a060c0807030c030c02060604090f0f050c01200703080306040f05180c04110a080606040e0708 80
    0x3a40803c8980c01004840407034a0207082e0600030740da84100030480e40d01c1c1c050003c908041c20340f00072043c4d02507102c0080303d0030300a09a0000b40b140e0424604003850101034492b20690b10020708003040141015222030303020380030340001e0302c1c0c2241c0d8840c0410280c4e80500781c2d802c0201140722440350796142504e506071943d00608412640e0a0405592031400000421a01c1c03260001900400c1c040d03990800448001000c101701b0340a40c010440d8840200f991801803281d540c0d559144c2d05280d0402d940d004048901e603c2c0b100007007500c0c2c8010f0510165020a5003904400f00f1200424001480e040c007001c1039060040c0100141c001c2d100600c100701000c110120203200c2620303406003410028800e0445420504902e024641021100748001070f08003025542040028200040407460010107504807481900c0ca41700d60105541162000c21007004150b0509100303031014000c00c0549014400c0303a00403503503030b60103015044001a01945030030303081e20001e10f2440ca01000c0ca0900f4070028004410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 472350908 1250 472349658 472349677
    0x120f0b03010b15160c1a0a0f0f0903151d0f0d170601120f02160b0105190b09060702090a050f010b0a08060d02040f0c0e09070908190224 60
    0x9242d004911440d01c0d055050040a4040d2120701e008242a07250481911064040b00c005050307040101d002c40d041c8880f8052082100c1040d40c1d203d4118801502c80c107200c040c0c50003001519411041d00a9110254004890303100340548020103182e08001d018200c03070702c0240208200072a2064501c180000c6411481c6005370940301803000c03141707040b5000aa8040d800908080d00c001040895114041e44c070f5031607251180c000703184500f01c40c130300301070380d0007216442d42c07901d404011001405003403c00c240c0180001c031a20081d5540d81c401c0c8520626482c85007001003c800b14003801c03c3c2d103030f0404541d0f400b9030007803c0720403503d8031a545400030b140681d803698003100441c1c008a082a801701c102c074a040d0395a00c60310700035540d06042207a4111940700032038100d5220a54509802194001d0064081064507a4100c1148980510118080c014800f904000b4200f00822034035002107051450310130801005900c42c29680003080502d064800141c0c201d20001c0c2c00400700100c031344d02030300740b060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 472352158 1250 472350908 472350911
    0xf0b1c140313033c06110304050d0306060318060b030c040908180406030f0f0312020f07020306060f091b070c15030e010b0f0d0f0501020403030302091207030804090507120f0b0301 79
    0xb0104020300800486100103420b1400113900490107103082c2c54034050051081d030000c0f400f525010054055600140d804442661101e814401c0305034050003480c02616480c5010040c00703024654000d480300c802600500f905944101c003402b5500c040c0000c00c804030000c0c00901041401d0f20341f900f015070103030081d5190b920a44514190f24034041c000e190880b9040360715050b0480d899101e0540441c0c05180c2141804012035544031320715040e00213410305109510000d41c07a0580340c0185800c02800030101072050340c02120081d00303555088040758010742031400c2642036440c0408031440700e224908015001c071082407000103040301440303000c1000100f1030741d0074051580d0030b03001c01d42621200c204c1c05900000c500b5080e00241842b006000c089805102030801c1c400e81c45e101c00e401c9038801c1c4c000b0350001790002414005800c0c10311001281404620041080c58a103403141d8040d0f000354001c407140f454695000c140024481d8603107203440340b41e6040800503800d410000000528034107a0f0a8005d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 472353408 1250 472352158 472352183
    0x2060309031e040303050d111b07060e010503011a0c150f040c091407141b030304020a240e01121812030c320a08010503010f0b1c14031303 61
    0xb10303091030a540803641d140c0c54441c148440d1a41780005000410001080c0d12428040b40a0007120100004105c200300c00107080d8480c01c040004008070443c15036241448020001000b001440e074440e1180841c6120103140c681325134411640c20070800b200c10048a448140a1007600070b501901580030b44e205580d80040a659030782c00a040d10300590a00e1a400c4903180003e010074080c07008450760122a150080c9003058004130000460400403541e90b80d80d001104010460615030641009050b10480310305c0c41001e41c01414544100e0340d02007008011089240800720303405030041c84200d00302ca001c02e2000c003005c80e018207041c4410b010f00303950911100700070402c900c0c00791080888034034140e518102a4200c0070340040e0004000e14021001a0010004001c40310112003d01502c544554817005a0f5140c08101401c1d41c003c040b40d00c041d2894541c0e90862a91000180140500d807001401c6e001c504505282920110038011011540000030f0711008010980c0b42071800e482c46504030006c403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 472354658 1250 472353408 472353457
    0x32328050a08061311041703190c020402070606030501020c01050a0b030727050906071d0906011b021c0203210301030b0a0e07090606030f05150f0d0206030903 70
    0x2004000610500400c00c20000508210312a01e511540520003801c4184800c0d103801c0c00c00c0071100e1007403841c0d0980c080810280289a810180d00c44504441d50003981003000545032420088003002981051140340703000340c4119121601038840c01a08608200410f541d44d003846400f07940301741405031240d4a00303000035071103195500c40c8100419002c1e00038040c850402500d29110011a0b4195581e2540e00c05442560185400788501c1840a040039001a00303040c4c3e800360040303140c01e148401503c071141c441c102c9500e41500c9140d100501b4a03202207500008d0304c1d904900d0701c446501942000340c044921414105080c0151500b45c03013034088620341360320269034400045440e00780d016149810001040800c6c01c0b068010b4204014540c001954000304980034a45922684900c45007500c5030030400c8025058032420f0b01b41c2c0000e8074140032501e070403070700b280501c1149015107120f2980700c010b01415843e41d401000700340364003404442d5030b4202160410703070f250891400d4080030b84115100900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 472355908 1250 472354658 472354717
    0x71206081f0c0801510f090e0a02161b0512010212061002070f03151d0a060c020709021c150815061210061a0a09050d0323 54
    0x40710f003070140119241506017203d000e18103403800015010071514022000c41c40d24031010904010b42580003003844081c030800505010060b02855040c0038100c0c40c00c000324056502031603403140d9006801a41c660074000d80e1103c0301510758024248049d1020305076425014048000d043d41c80888212031206030b0040294241d120fa003004500e0100184c000c02c0c41c9040c046440c0d10040414015101426161100034000003080d9005407451004c00505480e1600c0a11508046080c440d100100070005140f09594400100c14010021599040030101d00c3d8030034403a0b2006011100c5040d0340c1d940c5219000d40003561314080e181065442e200e10074810010301c052001c1120503400150901c682610002190800300406058000b22045250140c80e00180f00d10100c4001005d00007a80d04e0501e20b4441c48031356134400c08650204c0421400c175841c0c1d00070400d0f0b41203d804030781c1c048601401e491304650340662540b900c140310b000420180300401a07100a80226561455690361000305007981c2030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 472357158 1250 472355908 472355911
    0x60501110a24061701020a0305060d0209160302040b0409020702041113170312013f08030c0c0604120e0307060e100e06030a0e1b010206071206081f0c08 67
    0x804000e20a000d818185041d150328514044240b14000364055a840c880f04080c40c600308480d0b500d940c009000203010f500740c0700c0c203a04040184d644d562900038a6010454250010307142c0000084d00e4100400c5c4c052203901128080e081d801030032601c0d00d942d002d00001940000e4400c038862414448240c820580302e0703041d11000c004507000800d096107448050036044030784040f03d0b5158007082060400322030103681c10b180240000c1e00c2d2500c0c00754092180003807001500b05005c800b4203030640307100302e164a150030450385503400020050740e03a00e80d00c0390b0346400e101f0090f202c005802000104800d0080c504918210062a610b51600203000b0104064403560315010310404a00406c180744c006080020700401032078100d051540d100601d802c0002e806130800c0340c4901409495140102e840481400001c1242807030001c606c183c4041d100c0040d4880700c004000104120180d80d14101c4440a0b0b040040244141c1081d85c588048a040c4072540d0031848508014040c01c019016041e90312074211507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 472358408 1250 472357158 472357163
    0xf030f09010c08161a0901061a0f2715120c090d061125020607022403070f0905030610090c14040e0a060e0403121d10060501110a 57
    0x16140159000c019210308807840c030162034001c1c0510910041d03e00c03039104402070a02030242003440c103c512480810055008040d01002d9050210401440d400c21070007080c500c40310354446450301400c0394403e002c0e00880401d42502c8500c4c0d43e10130314204503207001c0b0207100d00036140a800041e040c4030f442d41d10b200702e0300c00d07070a21030a580000300742201c07480180900c400b008040e40c100819030f803200002e86a000c60441c02c0030000240102c01c1007004000b040e40549880040c079038100741d80d000600107000da604064001c40d0780550540c130400c12020320b040b08004519043e074072810300780e80c004c06401c0e0b03450300d503070104405110100d03c0b850001441da01c0390b4102903001450383e04095442d005000f076612004240000c101c419511008110050006004100e507000e101e40307450785503601555099071007040140030031414000400d40c040c0c51050070007900340011514a0f035400a14410041016080d030b01c0e80a1100840b6940c0307034541200040313440990f81d0f4110003140c4588207446071803a1400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 472359658 1250 472358408 472358437
    0x60a060c0b06040207080c0c0f0409020d020d020303040f1d07031b1d0607030e0a0605090a03060213030602031302040b0604080a1401060f060809190c0303030914071401020f03 77
    0xc400020301c42041c1180c1c0301d84003900150525031036a0310303540c6a0308529420000d0350042d07540b8900506140318103081210040301c080c448540941c000c0381001241c1800640110203203440c01c015503c0810072200181198807000181030350742c07150880c03901e1202482c44404064403012910302c0d8440c4c0501400040c102c038419410200210080d9950030b030388443c00403411740840140c2c1e041d035126400b41c0682d500a8407051088200f03c4204100043c071508250180304c0b0500803116940c4400b110682502c0d800240141d81d00c202c0030b00d0b60343d0154140d2004000078000001c00020b0408904080c00103842503500788041841c03081048041e000d0f0780680001c960140b10701c54042000440304180200f00640001820b5840e0a02c1140448190b040000421420000e200d04140c08000d9419050041d100300e07c0208a40e40c1d403090161180d10001e8205078440c14120203108034100f80080705104901240c036040d80d9030100c5c1c042803051503403560250244140000703801c40d01000700d91039210708021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472360908 1250 472359658 472359677
    0x30402041104450905010b120309031c0c140c06040b0702040e0105071d0f100f0f020c1530091915090330060503030c0d0509040b030105100e060a06 65
    0x41d0003010540c130181c40f5903485881442030394462140e195803401c626400342d03940c0d5603c00f06140ca440c15a84140180f01d4400c106480f010794070820840c100345c1d018459070403100d2500185442c0040450546510440004000072304122a9004043c42d901c01c0d01c1c10300c00362040c1d805180c201d8004541e4280420002d403042a0808042140325606020040c041c43c00040c011000c9070490010641c0030700828109000300c030030b4682120f43d40c05940c40c144001d180d0303805041c000c900f07031560710000c101ca10400414182841808141d41d100035100601c072800c0c01310401086654036413401e50300d107240350117880c1c1c01c03e5010100a22040c0c8260f01304688c201d4104141e46140000c04802c00b040c1c040100502020603450484600803a01ca0801c420110708a1849800c1034105c1d02160f000300d200b94010803c003029480c2c0450045804622401d0840d120b00504020801918010340c80c40c1e41946000b0400007041401b00321034003504d800381d44881e0036690344414049030300c2d518043d0f04c01144d10300c0e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472362158 1250 472360908 472361039
    0x901140306030f07120501050907060504030f061803021609090f110d050f07050301140601080f0c090406030309141903080a021f05041a010b090402030402041104 71
    0x1141c0110001e4215038184840d0a121400c2c944d0f02c0c0c010b01d0021a031000e03083c084c450309000f00ca41001d03466014040043c944400a05540b007180b00040079010070200e03080601c50310764484c041d5040c00440c1301305210741c01c0c40c000707464203446203254650709103810010034072802d28030402c1c18042d400750640000e03540b140c48074190714204c070001c240d00410178107209000a6051006170100301c01e0500a06150703082004060954507070316600d8400c1aa002c0410003181c0c0d00c4802d098000607200080d110545421382030216500c944540745401074140075000042542c0480d03003208071a0b4180000da00740d03500c00200b050742074682c422010b55a26500c82440800c8203c0001c0c0b25580707407401141d5500c0c0c10001d022080728078224036940190307514400c00040c400860b0481141d0264000f000040758101500c82140f8081da544660117154040001b07821510750f9440b65041440b0310940340d46480c0d0b0750007400c00300c0801d5440c1c1c0c00441c07256920311034510004c5020310949000415012140d80044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472363408 1250 472362158 472362197
    0xa0c110a02060f1e0c060106020102032e080316050c0306091e0a1b05010e03010b0a14010e030609060601120908030f0606121017071a090105040e010f15050901 70
    0xa12010f2040a0100403640010200b5040d01c00300c62980c6070705070b44030749260501d1400c3c03850580c050015a401001000942c2d078050103144088201071103140301c030340407407502421051f040e40c005401d188070020300d080415400f001d28010b0341303200750200c034015a2100f00f410349940040d02c0c1d805140d0b210085c034150745045d400c0c084219141801c100c41c103401c03d0351600128001c500807500c4050581240500195070300081c007100d800070a81c001e0002c02e5000020550400302807040c80d0f011819042650700e07903803180705805000b80c0010229101420028442901d414040d641d0b50b0201e0300300144803a41030041d005490440360044500d43c11960f0303011414076a1400200f4055109000700003288001181850071801001000511079a0714144050050307000c44540300140d0580c400c640401440c1540300340d00c40c541c01000405911480c6143c010388280c0613942181810301c507010004110103141c80c1c10340086900712031011110314075203039060755648940b40d10b0340c0c001050202a445001d500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472364658 1250 472363408 472363417
    0x305070e0711060c070c1217091305040c06030507020a0506010308031308161704080c060703050909010303030c02120a0e011805030f060406051501170601021e03030a0c110a0206 78
    0x160030a01d0212040c15602c0d802c0c50001c40341404480d0000c906403080c0b2550a00c1a00640b91500380c80d002403400d62641c0f011002040b03c40c0d5500f280004820307456032100f419000c400d41c0b00100038000c43c209131070030a40c1c16825000e0b81c00081d14110018400502c0012011175a640050284c202070342541c8564105920003020040d07200c050201400003d4030344c4004010755124032045003007401d050b1400560180581d003443c211020103210600256001146c44034841804450080e610740d21441d054905001d5602c500d5802150400000285601a0444030ba4441103a0903a581a2100d4520303641c5c074020200d040c4001007400c4255040c55028010149050719a4100007068a40d5000000c1c60b1400399014500c03150007141c01d0000b04400c13030040b140c026410348a0014582603d00001303080c0d02e41c01603851801910880170800c83c0e4000e10895602007403185101101040000c0c1541e031740e92040c0c0e482c040036450030041c80d0381b040c4207800c41665401c031000034042c8044180c00700300c1c46400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472365908 1250 472364658 472364671
    0x1003170901091205010c1e0e0904060f05101802030f01050d030c060f060905010f0308030408160c0b03090c1806240307020c011d240d06080609070503070305070e 71
    0x40b01400400c01d08600010711003024820000030070b0503452000000c0c00c29100056102d60440d820200b2040c01e600901001e03c4000305a4200080d03a5550a1040142c07050307400301c03640645084280004c0c2e42d0071045402c250354540d14042294510b081e0082c040744400c803851052942000b0050140f890300b400c20403101402444c183c408c1c00302c192200f0080314100740118100c2a42c0760300400c094852401160300501034240318005103461a20b402c0500d05c0000c0c0024005000010310103080c00305602d1008803035402801c41e401c4142c440403101515030080c0ca851501d0f104508004929260010380900b2003ca00388822540343c0380c500074402c00c0089000480001c44004e078410012560250107140704200382c0d8001e000300e001100015040714000d400305500030802d01c0c890303159034442110b6a1030350b01a084054019000d802c004030198043d070b00308a2001800c0940c00907226400040880c00f0b41001000e58849075078520800d83d41c0c000c5c910000702a81c2120604200c18200440c2660384040d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472367158 1250 472365908 472365917
    0x191808191e0b0c040f05030f030f1c021201031a04050c0f0f03060a150602031801120209190906080c01081b04080613151e0908040909060b03061003170901 68
    0xc855030b81d00651910848141d1014000414108500d8020402c50340040005070080c22060b01d90400d0740e41c82e0310480c40825085040000c0c42c040c600d180300079404c407242c03940d503045450703500c4c0386103044400c0d90030f10040e6990b000e902e607644030391009611845e001c2c541c440c0041141d03203000c800b0b200d284141c9a00903940011003203004952a10203205640c42507e070780b98005012a0f407281500107200c0f164110700f00315442030203615a0b40942080807520741809003401361b8000440e07880c81c8086e2007101005034000c8210100303041050f1528040c40d05aa800b01d4041c84056150181d081d521022901814002007180300840c12402a11700e9580006071280152491703c0d45a8007030724070b08103040c0c81000301c950000440c0303020701c9245040ca09150316204018030600340d01030300020a1505141588040f030383d0b07480c40e40080113001e00848008003400f603400c0c85080c0c0981480f5006007007032401d0034000d00445001504000c1070700e04400669600800c0e03440107a42c0c091001c01c56402c013000490522 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472368408 1250 472367158 472367213
    0x120e01020f0412150b0d0b091204080105090105010512070e130f0819030203060a0e34030f06050616140102040308030601032f0c010219180819 63
    0x7908110001c1019046201000d119103000b880c04442280c550041401000d04d0304407000350f50f50300c43c0c0100840c1c50b049019252151101400d0030b04144001c02600701c0740b0000200040c00302419003040f4401c00049000b0411683da60f03052124034800304903e180c0c0d070b410030b140a1220308201380b246600245d98400401d117035143c0741e0341c4042c08000110241c0e0304000c041102501c55014101c40e51040b02603250960031410043d02003407804d01385000703040c0170040c5800010320710500d14410440814048808a02e0742071101358150032880d2074a01c80d40001e04102c0800c06455030347c040c8070704480c0080d01075480e08910500d44820068a004100c46030b0410b002c8d4611456424000f4001650203000b0340c03652802d00c13a00141c1220001c0d121401c21440d100c0d10b15807801c20364031840e80d90300184000c81d42e50385440c0407041d00904c1800c0741245042c0100c207100640b194400c03c00034030716102c41c0d03007051960303242e0901980da03104000c0d03446c102503141c3c400b0f07500096072a0b9820203100d00043c40380000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472369658 1250 472368408 472368427
    0xd02060f13210b220b150301050718170d0305070c1401050a05090a0c2711070c0f0e160c061404050d0906020a020d0c12050f0706050a120e0102 63
    0x30b441005019282041c801c0758030103019841000640100200c0d0f8108070500565054404244c1c003500e01410202e20400051910b14445041c0030780301c0e000030000c00607840c0244000e0803a80c048400051602c1d04803c01081c403901820b000c1c085072100c0801409032107840d40040b000740c18010301c04410416030001450000714100410481010000000b280034540f41c0760390303001c81e00000d189186983c4002001030100d81c103114510180d40e112194170440d400c0210003400c2a08100001e044140d140003114200101d510003d002010700ca140c1c880c80389035407200c000241c2c90542c061104000394000200d002c070007403126034104c21522070a08250010182d01d40760112900030601e6080004000100402c11409004450b0580520708009981c503003410300080d9034000300c810081c01091180340410501c060300b1140c038010f02c0301701221038041481d0b03e0709544810405100e44690300c1000d002151607401a000d03603147c0e000c181d440508a881030103040c005400010680d080d0f956081000f0f600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472370908 1250 472369658 472369679
    0x9150803031e0c07150f06050a030501051501030504120c032d020d0503070509090a09082704061a07030e10050a120c0507080703030e1b030c0d02060f13 67
    0x1140800300041e80c2c8242c40c01c01032442c0524010103000c080d000030461803000800030f4801036000380e010780700007038566010b640c0f80004200d103801603036220613500340000c204101500000d109503d400380e42c0c24198588001501a00e105540041444007610069190300340f041074580040c500a290502ea662400d01e140d607903107031011072080102c0f002078031213012650301000030300d901c4001840d11034914581203a004000e40540401c8178860190302003c503603c14425007040305500d0708040407594072884029400f0325211a41c01c2d01d186140c0300a00500b00f4a414400c0400b103c07100b001090240718500701d10102d41e444034800b203050240401204c1001c0e00e490700d4481142140d510b41c1541d031148040080c2071520764800b501c00081c01c1410a990741c80c3e0001c15103c1d1558072150258951410749400e401078499080c4a01c91031240d0701c0c0c00b045080a1091000ca4544150250340c849683c0f6400e200c0e2414042401940000003001104100800c0c80c004116014072082c402c00030350b494031207604 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472372158 1250 472370908 472370911
    0x71d04060f140d03050a0e0301060b030f25050706020903150403091e0812070c0e040b0613090201020604020f040605121006080a050a060203041a1807080312010915080303 75
    0x615000c00c850600040c0181c02080b4030000086032410100b034070603034008082d032094101050400034076100f2001c0c2074400750001400740007401c0d043d030f0b200d140c4410000750b0810100c60064060403907902d10740c8a903d0800c401e8049070742c070340c0c0c480780303440105d46444010b0741c0101034590f0540f01d4031103031400420a640ea03841c05244250707101d00c042d07498002c01c21a00542c101c54000d544c00d0421040205da6400900c41d0809a2040085616210a81441d0240b4011540a20042043d039000c100030012140e40750361040008850300400c0040300c0d10b011003100c1c0c0f1800000e0140e0f1241c070200f0090310300341c2d40d14100d04500600c045040d070346034030105400c00240354400c50594441c20f4447c16041c61800b504014144440060541c52029140d0940e00c20302e1840282041d5030000204003031158081181140ca07183c00420006410a5050700000c50000d0b01c41d03481078000d18402107107107a40801100c042d0400d6200b042c0c040e07420800742e800106284862031498000105000924081c2400510b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472373408 1250 472372158 472372169
    0x41106190e010f030b0a0e040f05031602030d08060f010c020a090c030e0706080405060a0f0b0603011509090c0e120c040903050d05010f060c110f03071205011d06071d0406 75
    0x184401c280d50000d8507072095082c5200901d81030880d030400035100d0051290886d10303400030039011030311203080000c060340008030081d0040c04000341d426000c0a10701d03411208030b80300b82c0480d0071080c0800d4080315a00fa082d501981d012140010300043c0f98070440d40400f440b0300040003940c1e0556203414110031981e501c00b02401091f103031200002a04428800c04c8014555820180d03501d1415a51301511020010200704419942e0b0320710784d10183d115130200c0c540100103000182c0c0d03961070700c100500603a5004901c40015010841c00300d42c0e29018083d00075031181940710075084004d941d0420541d0851055168a41c1c8103001894084e55164003c0c04940d50094403615620103000641c502a81c505030001043c00c10980340c20401e260703004100d07105641d0403800e000008448503002402c2020300c0007010350700d40300d0020003184541c034004604039090701c03a000130006c0c1030340350f03c901c9140d00220720820510340218000411319409000740445200c0141003909910a000e00020110317603568206 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472374658 1250 472373408 472373417
    0x1006060801090b211e0a0c06080a0204031a06090a060b0a050a0c170304020909011103060103090f0507060305180601120609020102070909060506010f020102120a0b06090d0501020901031b050304110619 88
    0x250321009082d601c17040c8a5001d010090111204551641d0702001c1c513034412002000303035210000e14000299819200a56404180401d0400c5214100d114034003083c0e49032449282e200c408500324103103030b100d2081114156650982000d035151019210303904860f28030000e000400c4c1d00b072000180c0404801e510040d003441034a4490500b0700500c80308000c01054100a80e15241150304030a0792541030300e0b4004002d103000314004845c0d1034402a5520000d80041492040000c0800e5154041e0003040c425800c3e200c0044d40b07402c0510b0007540d00d81d02803040070340c4003101c100200c0104010350050480d417401030040f2035030190780742c01070750490300519004c4d10019603880902c4050344e8002d04110103e0340a02c025410801040c071a82c1c035100f400f4080d1071076190345907405210f030f40307490007500c40c41580200950304072081800e14074040d61220001d64006840e1540000c48c948411150851000f800e6a4590441c2d40e2070340c0d0090341c1805403003140c0d07104100340800e1070361100111050f0240001d503640c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472375908 1250 472374658 472374673
    0xe0a02030703200706180206070b040615050901090e010e0f030406020d09031a2206021801082e0906061e080105030a0f020f030303090f1006060801090b21 68
    0x8085440c070040001e1000c2c1c0c60340380210701d9940c5009032281545c1083e00000c0c0030382e185102c04031304030b070034840290024004104c100902043e274540c207100350300a5505024040590340c4c480440d0043d8003940350f0101d804001441400e6050b404103108004160000580d8416540c5a900d403042d0981240440d0340000381c00d00c00a03a0500c054544428035013003129a05046554010102c40411032455440c015100094501c0c1c2006e00460710802c510540407094081600b010f80182d404000381180c0404140000861035115030116031013141030180c080c00904500c40b039100150780031440600b42e210004e4010035440408d21908000f48819111b040c84c1d421003a048d101890b900c01105001e20203404010801c40e01d02240b400406540401c0c4e500c3e40d20950320000c2c0c02885144811030b0148004402c20680080000b03810a40d084140d084903002012601480e0030f45080c0d000e00000034014500411000d40c05802c04020407000404a40d90600d1854509103030400009030b99000c1e81c8801d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472377158 1250 472375908 472375921
    0xf0303090605031306020903120d0e19050c130b0a0b0316020f0d11100603080301080712150c11011a190b03070f0c050f0d0305090d14030606040e0a0203 67
    0xc400900612031800d100d421450b18107201d200309058614007034111034000448441710b540c14403480364543d0b04003400b42c0d100c4004d000382c94024103010010034170743e11a40c10a14100241110b44001d01d9611200805055025006000d240306006080c440b6468840302e0030085541c1e80565080940542d486140e22483e003607034081100c03c804500b143c2590401224883c2d55100400d9006d141c9440e802c001e52a904803180040c40c00ca0a1100c03c95803d141240200420803505c0045040781c6821040b00c0405454001d11040c4e0b1800c80c50080c1120178074040e4060042168100031031660030703402e01c0100051600d40d0305080d2030303100407406544c00d0301c00b00c80740040c5051205401114400f014140038035040c060311000e2440007030176001c18010340c41c181008080c403882d405c107411030748031041c5c0340d44041004005070340d02d074007500c46000720b03051800081100d1000584401c0c24807450f6994148000c41d845041955407002c1d00160300006c017084081600e0b000e4030310761030240c0610000141d50707140c0301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472378408 1250 472377158 472377167
    0x2040c030506031510080304030809030c10090909080c011b080702150a050901020f1305010f030207111e060a180f0308030106080603030d0513060f0501080718150f0303 74
    0x81024000d1500e803100380400d6880004000f00d04050b10000f08000761504403012000560f60b034052015071100280c00700c20031140e00d0140541480617001c81d8002c0800c03030204403018482142440020700c0300b0070101700704802900101001402074494910b42101e0301c82d05420744200c50045503c1c9014402d00525007548030000e90340c041590700c003415043e640b242a415881c0c501a0060912603182c00228084000c2035040358540441c5142140d40c403a003410700880713018068403030f09000c284412007a1002d170303001f4000c0f54103140d80600000e805e003118500b0800e0003042c3d011054400c00842c4094005515584010204000141c0742c0d8541c401080c41880c0740380700715801c41c0448130f107000750810005c1c0040095905540040c2040403c503600c040c042072450041942c18645103041400740205041c045e45400070890144d84d0a1042e60000c04696090b6031080c442c18079a0742c0007070003c01c41c0d080d40c01c2e200301508107d0301d008203400c0c0309030303420300040072043e00150981c1485020400802d07800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472379658 1250 472378408 472378421
    0x50603120a020a020613080d021506030c011b060b0a090b03060c0a0c020909150f0f070f050a0e27220c0605070221030903070b03040803040813030b010905040204 71
    0x800c0c0300c240c40c0c008030220003034882010600003409000086180101100005074510242c0f110310b0888610100380b09000f5662541c1150f050580c2e0041008982d050401043e4850441d1042e103e82000d05080700c0e000b2019400040242c9185558010170502d56a4035180e1034010140450081020b10704101003505000c006050040c0585042081e8540c3d00d8114022240d4940c041381e440416980340d040050500c004002a6400015101c0410a0f40103000c1c0f07546001d0041b0b0300100041d03540780c2c40151580d050900420020070303402d004040b03002e84078102c421402c0c44041c01e1044140000031200e069a8104040711904002c044c040cc001080140e103405440b09030f01c15140888070103512444010210742c040c50041002c000380070800e6440711a452001e41403084c88502c2400105031201e500d942001071114400d0082d5040015903103203000640b070007241c00090440c0356484943d25a291540304031140c1c00d00300500760300040400c109001d03036402040e940101007110714040c410007049420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472380908 1250 472379658 472379683
    0x905030c0406030f080702130510090e1501030b07020304050d050c1815060a0c02180103050606040204061707030e06040c03030e060a0f08040201030b190302150405090a020d180303050603 82
    0x25006003000400c1610306921100d035084840aa51b601460000c10701420062030714035002414082400b008407110780c02ca00850781d50240c208620384015031802e4486411900c0c4030300380c0d98010700500104640100d8240c02036481d004032480c00d60b9407000301d51602e201c1c52003500c45410103402c003c8581408040e100400000182601c0c0501d0030b004202007a0340c151290500420b0042003030034149014a50f0340029a40003071102d045a500507185840901c424002120180200300101d02513007014001d81e0300344d905e6034075032103000f0844402a1400e410700400c010205510b403230702480c1054080c441240100c0c01205444091420344c10003500305000010558081d9804110030100d03a80d02c00380507401da0b8200d11744503c15442d1400106c010b4854001c11603800762a000b4600103101c20590b6030b008983c03083c3d0f82281c00040d0a1400c80f401e00640c4500c50700400240d0000d0000302d0654001c00340b041950030002031828114884160010603ca41200425a036809100041c40c04011080300b004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472382158 1250 472380908 472380911
    0x30b090d05071205130e3d09090f080310170a0201050405191a0a030b030c091303030908030c07140c010e04020c0c2e0806180901020c0d0905030c04 65
    0xd4595960642844041c0c4403d030030000e01080c0c242c002030b00030310750b90010300041075141d0032400c04004e40040d040700c0070300200340c45c00d41652200540c02c0d079414240300d180e81007400c1e0914602e4800d054025000440007184c01c1d003621402c2c200040c4000025501403100024020200390903c03911241003c500364407140306074060100540182c0e07021080701d017903400940341030b446405480307000c5100700e40c10341081d0f035440d00f1004290342c031158050141071b038000c00e50380600800c004501415140c0e0b1000030000c0d0003441d0300e07000941407030784007041c0c0a55604ca03150014015049444840282d0815a41c140d1454400240700c01407111041d5504201d646503c0034000c00030900001170321180f0185c01c054047c1da0042620301c0300c080188003124105d0400b92415074007180d1088840170340703844110380300ba4040c40d600100501c0e0f071050421511914001d01450a249051207118000350002010b6060b0f541d02009400202d200502c14041085941c0c0c0352108030701d0800c0c0805090070442e004490159 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472383408 1250 472382158 472382167
    0x9110a0e040206040320040c032003150105030403050c0703201206180a0602030108030904060f0602030d110c0d0f021c1b030c050d05041a0a080402101107030b090d05 73
    0x583d01d250485045a901602d50076805e40f20801c2943c400c6000841b15511500c2c0500206d0b0380750b0160800956001c803001500162440b00c4812419400184c4000c0310a0352074000e194038950140d001550024020f0815508002440c80780c40d00d4013002c0e8004580040c0494200001141d880c250f915456004a400034544400c10100035030741e05006184064101e6000c09034030034070405210456086810032015540c0390b0f15106100c0d904d078084100305000354513203a00055101d0040f286581074079480c3e030182d813504221452050140049014400707107204c00300154100c440b000c0100c18038170806034698002900480340e01034200b282c400c0001040a85100b10001116401585501e038400c0715050310080400a080031595001c5c00600200240b04880701d1444258118010b042240c8480590b81424070505c3c000343c1c03183c0180d010f030002113000b42c004540146031500d400420b8a410b450800f54aa1012100c0d81c900f001540c02640d00d00382c40400d000c544842400b100a51210b6400d040c0c1c0350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472384658 1250 472383408 472383413
    0x31020c06180615060c0109110f0102012a0306090903030c031a031504060e03040609080f0c01050406050d09060203070309061406010215100b131e050f150d09110a0e04 73
    0x191000203102e00d004802c032144042d080c1e51810207941404585d800208541c185c0c6243c907440000365612001d00c201e0f58141d04001e1584140198418021104800716a034211004009510703003000004a05043e1200d0300407032104240c0c4a0301184602954021030103410b0b2200250407260002d50051a2600380005e81045440006009211040c24180280d0036070350360601c1d80041000d0a42c201c00c90000140008111f64001e00340c6040e64074072000e07141075010f40d1480300c2d40c40c0b030a80c0c080350101e44280003c00805002d4000ba00c140820000c02040d20b8105588031003c03a0710483e546030119039104503001c140016845911541b12003800e40004605017800043e40d58a01081840284909803002408048403403002100501c0d25092082c1c98082d4801c1c50119402d070740c029180300b402c1940c500030411400f0101201110300280c0341d03080d1003100009002a2641031481d180303011108120402d031500f8184603120440c0d00800d0f2a034004207000701006260501940100300c81120101030102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472385908 1250 472384658 472384663
    0xd0c180611030f0304050c0907020106060f050304150c2303040503030609220809010329060c07030b0c0d0e030f03060f04111303030315120231020c0618 67
    0x40d11100d0030145650350424160510b1071007000341c202d00451010081c40208800060385045412007102d5284841d07950742c20403070807142c1e28401d50340011886074107100d0f268000d000468006001d4018001e03469683c507041da080d501011030702000502c40e2031450095050383c2907007145180380c1400041c990306180d20358075900e010103014248500341003c0800c0040b445c5c9940b440a110b190510a02040b281c2d04100d07400b6040301e01d255020030f041c0003055030425444040ba8003079100038100c3c4414141d00d4020f01c1000e402080c180b552921071214040041017003650300d41d101e52040264035950b0384105501c041600c80c016a6042c0a40c018000082c40c0c40d810019694003000a54124010488210005010740a404120409a0000034414a40c03403601c00784502501e0080c0c40174491400d4209526880d1040307403152004d5904d2030900076005103452840c80151680034840d107200c16500c250600d00c415260036407441c1050f40041c00d44a080014021107034041540c0506201c8090b1100d103094 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472387158 1250 472385908 472385957
    0x60f031002090118030c06020111070b270f01020d06080d09091104090903030203071d060904020d060e0c04030314090a0e071215030309080d050a1110110d0c 69
    0x380c80540105210300b159100b08200f80d00c0b9140340303d1400c003295803400d00d90f4122800b4081c980041d400d290441d40d5903060202141c0d02140c2c0802c03881d0700c9030356034440700003440410740100410104040040c0c0303400804101c0e001200c901c040005a13a89076204a90085403c1a40b0440150304014202080725801410035001c40704403601c00700e00c1c01c1d00152401d015210340c1e00140010b43c540b00b10350090640c541d01461003542d164039003003c0c0c0d0411000062012040f03940ca40c0d48480308002c1079515003800c1e00641503c4504a1380899801c0e203403040036079440300480c1e0341c124000d00130500b0010301d17031301c886140c80340d20010382c99034a440c880e42c0214400b031040d030145a14a0114602040ca4244a000c10786c0000c0150307801000340070480300c3e40e586e00041c184810380000b1160303c80441c8191010810310410015912800c0c0b80498646040d200c81c540c4950000e1240078071003060114103064014030441e00f14089c44e4680e00c0003002100f400b00d5a07031a00200400990030554000b001801c0b9041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472388408 1250 472387158 472387183
    0xd0507081f1a1002030424031812141b160f05060712111f06050604050d0b06030a120c030305010b0c120f07060204030b10050108070e0f010509030102070309050405060f03 75
    0x54143c085002c0a07803941c840c03644902e402c240c0d83d428540b400f101008070784250101640d400d20180c10005a0b5041d006503481c80a8105507001056442c818003030f0044525201c0558102401c01c041c00e0345d40c2c0e14084a1001c0703e41c00e40c0101410b1120b01d507031003001401030b164a4640481d850700f0080800d845016240004100350366940d18140710501903107150111502090032a0802c008a04000300c0c1246000d02100c2494144031021841d03103401c8080c1e03020350b13030054540d008181c503d440d00c400307484c800340086070980034602008000c41e01c44038001f41c001c021a01d036011001250715000f01201c0c8140c0c0841120310041c050701c45580c00c0490980d0715844c010b20724076103410302c10709030203c0c612910a00a00552000800000b048004140726224501486c058050543d450005545021007140c80030001180c601d03e040711031400307a0004000d540306141c070034141210728010908990041e0020340124401e240100182d241034040c0582c40001500d840031050031503c01709a2340c8036460302c1d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472389658 1250 472388408 472388419
    0x308070c0807060c09081204050904150b0a14130c02030a0c0314070f020a060203040302240d050a1d0d02030d1a0a0b0703081308030f04020d0507081f1a 67
    0x4603800d010300d0340c06480c1c90540040c0100841c0f440c242c800360445059214800d1140a20b101c540120604001a90201c603000382959616654a030740312544a049905000f44207a55991005881c0e00c07605a48005070080400c181da07516080c1d02000900c000400e9030b80c00c141d043c52603800400343e02106841c0110b001c0c1c01d081a0903003662400751040310580a0814100d4004a021014400240c2101503954002e944c07190400b9202c1e18100d0309c1c4d220380d000103074202000440288003140c0354148111203501c0d40400c1801c1200c0303082c0700303070580740250381b40000f6946659424095070a603841031340c0801d0000303005010300c404203807002e52a401400a81043d03540d641c400c0ba0000754804155000c0e08000812030182e082d202d4104c0304d21a00702c00d4050b000138400100140b80981006045030010b5042008141140c1d2448120300600e1001081240c0290340320001000040c01000700070b0282822002801c0145111041e81100c0404200755075450fa051a8402d405180c00101440701188207503075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472390908 1250 472389658 472389677
    0x50c0310030f1a130b01080c1c14010c05030f060301092f030304060201060e0a02030712180606080c010e031b0d290615070210030507031d0a110a03030807 68
    0xc03d03d01d030b14403040d502c00070b002800040001d01600114020000317031244800c0707105a621640d403203640700e20243d2441c1c3c110740c01c04011154050384406a503c6184150381c58199428135003200d90030f4441c554610008100c002c41400700111961008940c000425002040590080d88a04003000420344075091200c0304030204051200700c45010103074000e030240c00c40303030354503500e1200034003c00b224405d2035404040c06000c62141025802121701581d020380d241d071001c204d18444900203218100c0e10310500c0010b401c05500094aa000b02c4006001d504058030070104444005000900d5001c543d85c480d41203107045801e00300c4208000c01d504401a030702c64100c42202c0c039120241d600102044143c070107600449000c84840c040d001d620610b41540c002c0e94481d000c081c0c02510340035812000394003801b01c658182c01203100c2e80c0817075404449031901107031b0041a111105d5007080700300310900301c0e0f42041880300c05004c0050200b8204460640d02c04030201d02e151001880c101004d403048013001003d24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472392158 1250 472390908 472390913
    0xa0c03120605040e030703090e0705040302061b160807350a0f05030409140420030106150e1e0604030b0403261905100e060d060c080703050c0310030f 66
    0x14024805802c001e4010401110000c01103a070301d0704120700450002d240e00501251603840428114010a060b44800d8141070655082200e40d8101e4000b91100c5002d0204010850318101310780800342207419500e500c0c85081c83c601c2d0b0f0812500d0340142c2480206512a89007403c4425500d169070550705070b031a001803d16030700490804101c03600180161215400000900002000070400c40b04099010030401445010741040c2c140300300c5011704882c4842e000c4074018000c0b00342c000d40081c8020000100c0726220140213002c9411082010000350740c11100b601b003804c5c04071081403000c00c1044610021124040096004d100760700000f40b8412030740000c5420580a002407030110405902c4926000011412a006404040380c01041c0ca803001d004000d00481140b0502c0d000c2c0200313142108429040500d174000c0c00300c02070401d1350002d1a100341031001c50007600c1800054416039031230010b94200400f000b42540ea010382400001c42d420070a2001034640900f4803402c90f503002440c8495107a03c0e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472393408 1250 472392158 472392161
    0x1d060d0e1207081804050105010e0405100503030a0c0606090207050705120a2315040809010e0f04091202060703020a02030720030604050606030d033e0408060402150a0c0312 76
    0x41e203041c2003080451940100308422000c0e09504018480d8050410351007010442525000e100f2107001c200d03540413040050910383c21199114075003c80384004a96a030300030a01e90381c0101c41e80302c001400d400d203031070400c00c084c0112402000e5401065040c114103449464440409100d040d110301210700c15514500001e005101c49a40c010030a01116030716a0001c0002c0409a254400ca078002c0e24103c00540134034451395406580c0204901d42880d1522006540f41c440015000d41e012070f109200b280075a40d030380180150f240c82401004140341000402a01d0400301038003803070a01d4014807503007456560020589803d15000180c90b4100c48080c0741d24101400c07014402505802401e00f00024054001011805420b0903400c40d84500f81d0340104038212041842c8801003441d034010f600650311001b505401c0000110110032405040103111642c45074030a85c0541c0c415004a000c02c0190f1130498410303450043c24425051411012190041040341c0300364000301448518011481ca1483c075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472394658 1250 472393408 472393423
    0x5191509080703030504050111010213090b0f030307060c03140123010e12010606081b0f07230c0a0605182e080121030f03050a140c0702011d060d0e 65
    0x34402e0301c050315200d00740102103030f00034062103003c1410f0039120b000410052085a500c2d44543d940202c2c082e0030100708070040c02020b203046d82d01c000700b0030350480c15a500340010000039200300e800150300c5694480103019a003248100c805034401c850010040c00c0c800c13030307c4d081c800114880e000a0120b5850011b98105220000341c2d0b40085014155613900501584120107440c03558841c140d0030b03901c9070080d0721040040d00d25400c070b04409010009501034584050f1201030302c14040004241d0507120b541400c0c0c030741c0d10408421a4003040012042c2e0400440800c00341402c2d26010745040000c8041064058110390400d0186207060031a403038220340c490740d10254a07540c2c00c40f030380340183c1024018039200342070043c101900d14101c1005034048541c81030000099254485220045403414103800804c002081040e86644030035010507d00c0440d00407a20500300780703080d982c90340c043e0b000041c440700d42188031948280c11603034060050f6481000352203540401481c003181017080003c185040030788 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472395908 1250 472394658 472394669
    0x7080a090b190b03010509150405240406050a020322030909020a111002070b0f04060608032701230c010204030c06050703111606050315130b030705191509 68
    0x110100303101c91284100326100480701d02e00010b1088441040405088480139101100254401d200e80f4070b484250810859105015400303590000005400c5290700e10b088205400080703242c04200800c06c0950f12541d60400d00107142103040d80307894100282032012110b003081e4140b4955440300101481169014060142d1803020340d22030300c0810000d840c1940055034180c2500441c9100012003c8520035107035003a0b0404450b0700e81d074032880c40705240034a020b001a600d103038642d400807070556801c10040914041c1a2081400d000c41042c0c01000c0e0b103030b041283e034100700c00c080103083c0c1442c500d000c2050312502030381d280e90380f0110f20650302d00900c41c42d0701c002c24a03003100d20001070b460781010141c142c4600a850b0b0184042c4043e8141e501c03540004905641200e4240d42404604d00c01c001031584010b485c210180700184580c002141000d44150340078011343c5441d4111901d007824000c0600401c815500c1c0412014018012411001140520b1342e14484100040e402a4407070a9028000c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472397158 1250 472395908 472395923
    0x80f030c190f1409090703020901050c0706020a02090114030a0605060f0a0906030c0510080106050d0204090e0c130b030318040b0d121701181e020d06090b010206010e07080a09 77
    0x210701c0d9202502840a107981c20b00403850b0b40d180b20310840180d030100c411100000740b030400d0035070b1101700c1a4020b41001014030b040040621940340158000c05c0302201901041d0000c0c0b020b00c1c210301c108103140f40c0580080700c8800006c0c0d0012060340b00081c0207000c5552081000c22243d5a030b00c0441e8401c51030103e25980441040c0d000160300c011a031191041d41d000e280c101d00c04644880600c10525500c4160b20009919000104401413040340a031042c0d409020026203815601c0c48440d09440f0402000201600700c15640d040303c1c9801892800c0950703181e0380611030100108002034580c00b0340e105181580f544180c10000c0c65541e80d004201a42c0c004005160108090a02602100142480307101250018002079014841901200d04848140043c0070f841c1042d05407580103001d0075000e01c1101080c6006003403402005001400c403044a00000007226031070008040c003070f10b000ca0941410b41d004540140b01c007403802c204c0f050f4095018200300700c0d56201c801589004002030007020340080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472398408 1250 472397158 472397197
    0xb0a0c030e010315140a080102070c090509070e011503060614040e0a0212040b0a0b0108060906281215110a081008030f1908160f111204031a04080f030c 67
    0x414684c030750030740045d819121000515100c0450038200c0c85407860140c541c003105d0324100904a1550030090380b2105005c16641029500c44001d1854107080e008a040483d05c00c0081d980c0d20750501c6948001d10b100d15215600e6503848443c140c5034031407402021858107010002507403403640d42c3c045840800075500090590301d003c0c1000c2d4058101942c40300c50150500480905c590300c94000c01d401510018120401619190204010490580a0120041d20720102190b04400c0035284d10b004040e80c4c00901c083d1812841c0520300440c6485450880900e000e9071800c040d00204183e841c0c05045040800c0991170702052005012141d60100c107440c8400107004a0a411a0003e0901d94840d05684c0d502da0031401802d03211440c0884008400100d224152504e8510842c0342c00c441010904220710b0308548441014203001c1c0d003641e000e0a1800001c1c0030000c000501c00250701c60201c00c0e85411031ba0610f80c1c0c1d50307100b80c4210303140385140c1c04011000c601c500d0112811507000205182409044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472399658 1250 472398408 472398419
    0xf09021c020102100b030606040c1b051e1b1012020c0c0a09021207050f0903011d0f030307050403120e040f090606080a0816060b031002130b0a0c030e010315 69
    0x200e0401000803401402003203040404003a140c0600c14003d84020043c00181e962242840000d22500c0304400410150191402820784650346103080d4500038000b50001202c0c0c05c1e488001c1d81d81c60060129540d00c08031303441c141003620031440c489004003100c075622103c4480d102261440141010391040610006030100c0c454000141e41c81402c005840380c5401c1e030b50352200c1004a001e68158542c0001d00303040040e04240c490801401c00110007a4000d00300000c4402007421a100c229561210a00d241942c40501e1410070a460a0042d214011441c5d4905500c00030440e01035848010701c040b04050003000c865000700135400744041d0280c01040740c3c5000c11030300b002600302c0303210a07240c1c10300d071040c0803401541c086229100540c01188292030005035403d964020300400701d0980b8a0750b56007106207000da4090003500c09105211801584421004200c5a010452030740089001d01c07082040c10040343d04070b40c01080058050900800450b003210040c3c01600100d41250241600c84101040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472400908 1250 472399658 472399699
    0x19020a051302091e0102060a0f06090213030b0a0606090b0c03070b070e2e05030603032b15030b07050307031b02160806070507081303050d030504060b03060f0a0f0902 73
    0x403040111020201310700c4915684a54094000c480d50050b0004400540b520342030742c00003030121140174400200940c0d902980c10498000c805500b49030200c0c0340040090082c40c0203502c1d001a03090350304205003498a80081c000e02c2007413081c100e0081001c6581004805d0a0040d40c0c1a00c0d0015035164541c44c01810040042c01e810180c544584c101c0404011100344040c07103001d440d100421078200034400b10505031010f8000920403941031104220b01e440030310550420980c2a442000c00481d405d4196801e441036480c1c03421500611044500b04202060404c0e00b459080549130404a40e0303030715000720413805400703e4110600b440814031440700d80300750300148420001d10101843c002c4113841c0d40d08151900740076521000096002e108e10400f2030381a000400024000d01d060030308241e500c2e603445062850403920480071030358034400c2109100341030081c0c3d003008000b00d02030301c92450015925074540b4000b0b09006045562001014450201540102c0c901c81e0010440d03a04280604111034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472402158 1250 472400908 472400917
    0x40510020a05061303020d0f080a020711120634120219051b03390607120b0d05060403120b06030c03071e0e0613031e0501110c19020a051302 62
    0x40041c0f180b05400c403201c0344900641c20440480c1c9e80c56504603129442d4039000382d0010042620010b4003c0030b4100d803a5500f000395400c81d400d40002d01180e1400e08031100c2540c208d103810340800484154034103089088891005c2d44981141007041405441458000017409801c540e40c0c0b440b00040e045601d126000b6024100503441c00a01d48503124081c01202d841e8000c034008440c01c242840c0040c20b244000c02c0c90f140005824907440030f20a142d80d20100d14180081d00e10001150440d0141468810a0f000e40742c400c007025900c014400e9500e13502c1c103070713502c40040c13004c3c2c201b00c100d4044071103541090300a400c0c40c071002850603845e81080381c814410790b40269078000c0840c0c1c2482d079038401c0d1542c1c0c1021591103001a01e449501e101d1240900031150b00080804000c2508400d01200141404902d00d146a0710310079001188070b401c0c503206007140c00c88010015200018000b4501c1c14000003643d503018210b11180018201c0284080340c2c6604864002c62351061503100c0600301400b4a60261 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472403408 1250 472402158 472402163
    0x1b01020705210a080103020f040912030b040b120c04050a0209040c1101050108010c080c0f1c20030123040608011d010605061216140f0408071a040510020a050613 71
    0x181c0041409440b444040d1062001c80400f013151040104003618044807000040c400c041c102190756005541d40207040c510389520315004c280e94000e160030904052044500c111020790716042c0000d8010b035415500e041007c0c107079100d5038036080002c884a0380342d01602c082230006001441100c01c2d030306000c3c1011a900040d050103610304400000c1c0341d141405940c80146641d2034078040f503110300d00103560660000380d01144001c3c0400c4071040940c01002c4050305410b044d0f000244c01411140400c00c00d104071091f00b088004140300502140c18008890100c045452112004168031000440c010f0700d203236841807071194a03180d0950389401c0104221030501170070340020031120303403a601000400e00580c150071030100d103100c0004400d0b08104940320791085490610000d04902d01400001c070798084a40c10084d010082010014244200802406040048240788800d00c41c20801c1d10507000da0302c242c0e44140e03107014044003424000d03c50083d9140e0841d0590f040b40c60310230300a14002c07105c0d42d400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472404658 1250 472403408 472403443
    0x30a060f0603061107030906080c070c0308120901051b0903011e0608120f03070f2f070602061e040807080c070f05060307020c01081509180d231b01020705 68
    0x25013455124680807920000e6041c1c0780d6a88407401c1503001c841c40c400c0100190004041040528080350109882c600118407441040b80d442e00b440c100710842480c00341501c1e00682c10582402a810001103003034120392544010b980c4c032141c0c0c2c600068058a0400c1440c02d92041449446038500300d15009501030340d11003130031070725191040d40000c042d5209503c881c1c51100001d1004c210594030400340076100c580603280c4250601e03000d43e5000c0740002e04040c4040c1550150036081030a0f201071006200429513400508800d02e8924540d02440300284000380c1407a4441e4006010850f220051760340303442d08410b45a1310354100022a0341d64911034001d80180a00c3d00c0e100191600d0458103c0c0d2190425602600c0081341c40300044d01e40c6d11016180c9500d880310000b5041003038403403000e1740780f15048cc84550551b240c11148000c1c1420807046811040020808655112805611150840240000c4181c0c1d0300d101d52003003403551200d40351030000d0030350000500d103040c040c1c0082d101125501000a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472405908 1250 472404658 472404671
    0x30207050307150e0a030b090f060604110706021b0604060e0105010b0315040b01020c0402160605060d050d2d0314010f051e040b090906010602100908031302030a060f060306 76
    0x42690b11505480b618410300400210b28441d14459040c1d41c080705400307400c402c142501daa440c00c020b0041120300395603d9000540300218000308200c0160001020384d400c2201a1503c00704086038031800c400503007880d8002441702c615500f64150450102189420381d071003401c10345840c0003e400b10090700c0c88591b0800b0004191459840300310f9005181f04e55161050f4149035091101802940c110b8034194015038001e02c00645450000b0b05070702c0d240010300c84c0d40124034a011021524060038041c054014500c81000250001602c03006404040c24039518162244a80244240e4079540e00a004201c0c66004c54109030141c02811892140031078049460381c035002d01c40d1700a2098802c00c0d0348441440c0c4021101000d461442200140103400402e14032080c0011540e0340e038098901e0045a80150010803103030344e050003480c960140302d0209000701d10564842103240d02001d0003010503240160450811550100601c00500d030b4010300c203221980031229418020402840144da00506111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472407158 1250 472405908 472405919
    0x5030f06070f0e0d2a0b07020307080102030f130f050a0b012d0b0c12040e1806090a1113110d0e150106050a051b031b0309100e0328030207 61
    0x110020343c2d4880a04030010141e01d5403a010301c02d6006121521808034810544032030710200500c008003034601044916540c41c031510605240c008507610158040e4418001e102410450b24146a0802d062003081c3c40400017505080d440304551030340087c01486150040300c104000b45e100e0b0782c101e400c00401e003001941801c0d0005102c0180c10f0001c0000582224244900812400079002c00481d4100700d0350750701001c140042c107030b0707006400003601f421802c010400c5400d01c1e00c002c0f941c0d400542001d041c090404d101c1d050780e26404090002c100e100300c40c1401780b82c0d843e4410760102e12030043c0824088100e21488100581c1e00c071905629101d0304000e6103c2210200150300c522001c1d01030070750140342c0e290400480d00f60300010208401c10500300624003100351415400e804007000c6601560f43c0709801e100100c0c0e0704104d0f21449101da0003d010350145a0340c2c141d000b2807942e4550070403100500c080c40001e400d1045100c01c1c4060840041c0c4000f0140da003584070b202c680c1e0720070303000c03900241d8449 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472408408 1250 472407158 472407167
    0x120836030c01090320040f060503120f030c03060f04050406050901110403020d0b0c21010501090f05060703031d0a050a02030d0305010308030118090c080303040c0f05010c0204021305030f06070f 85
    0x31840e07940402c04000341000003d8602000408004100e014240c6400303204001a041d105d88410010f030f8162a03440511584c5401e200c40c210801f030720249146030068125a528580c00000c01a500c242c1000c000151940c40754010b012220500400800c407070310301031801c040101001c0c0c0f198001586000316050b0503071102e204070307002e0fa41c00601c8954000d1050f030302c00f65041d01c018002080500c0c144100c40c4003d01030041c5005080d42010720007655814078000402000513a4400400400301ca10100040e89449044901e00b540500e4040b030400740041070222208508411a2658410405480c040c4080410030740801f071b200301e0a45506400c0c0400c110203640302030001502405003000100000000030001c4070403441500c034041103800e86512203502c0800f80d5484174103103420000c10082008504584074019061440c0055105414040002e260f129071a8000380281e0340007a03071409152007400c40c0d10040000504403201269044141a25aa030544142c404030300c40c240d0314030119004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472409658 1250 472408408 472408423
    0xf010f06120e01060b0a120b04090f14120c01020a110c010219140a060b120f070b0d0f11071a0108120d0222171612083603 54
    0xc9507244041da040901e5141c00510484001550325981e551002070310b090040050001404191103040e001c504d102c0f80001999044c50080707226a00d0240c0820014140604003103040360042141c40310100f110070000d252807071a600c6115200c0303000c02e0204840b0b00540081405030215070300d8000c01e5805a01c10f035680c0c00301c2400980981c11040b80c2d010490388203141c81c001903008004669400401030203a90901301e80c10420780304a51101030398034060070004a01d40c403100d60800100850740c50101c80b50b03118030040c06481103d410010381101d5241c6160010815150741c400304200c206040028000164000d040480700c00030440d0100c0c0080100c404618129001d0401815420351404030000180d484069105c02d9280c0c01d022000030107110645242001e2912030180c0c2006040100b2281a00d1081c40c0c403d129601070b42426141c03503500d8261404031464200304591200e50740c6404140381c020301070500e01106844040b800c003201e030131003845d40c2d0400c50100615500803501c2030540701c800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472410908 1250 472409658 472409669
    0x309190c090c0e13020304020319030302031e040309031113020f0c060c03130b0402120105090d020f0d0905060c0309120304030b0c040b120a0b0301091506060207050108010b0706090209010e0f010f 86
    0x90b08280e04c18407015400031a40284010705881c507401c40b100964681c1542d0a8040c3e0019501104000c1a40225801c80415412401c441d12047c505a03400818040d0a408000d00440b00005045040d48a01d0341c481002c03206a00b080d501c41400d0400b410040c0c1001100c4502846108042066400c0084c104ca0041c0c002100e11441414a61101124110050705c200c0e0008190003590f01012400e204140c00f400710007000d82000200004003e240c04c5280c00c2002243c0c21a00b182c1000a80140c01102160010740c0c0d02c46e00c03a0481d42d00036007540a4030b040290001d0b0740d100502c18050000c40108103580c4a54100407440d160a84070700b0443c0650301421115080420181a20484603000681e00408082002c6040c4220b140804e0950b40c503c0700840d0007000c00c219030041c18145000b8007000d090a440101205858880000c182500610480410000018030394013800201e03000325030f505402500081305d0b5651042c404150400448900400c0e102442c0003080030050450010101c03003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472412158 1250 472410908 472410919
    0x1e070207030609051f090506010b0f0a03091b03080a020d1404061b120f030f02030f0601051e0a11010f09031d0406030f03031506081009020309190c090c0e 68
    0x741969036060003008400000c0d03441d44905c0784c4000310300007902000c6003102404031021501d03031503074504240b40c0358040c3c110b060244010b02c5000d01100c4488260b0760211114900480c0050540c24006981c00b66903078080c0c00d00051a10110034000c00200916180d109a401c030b81040403500e00c11950700c50281020100c0a00c200001c21519214200101d60078113100f15038007021720725035500300011843c2e15000020400341009044a00c1d0540324040c80e817002d801040d8658039040900341c281c6000105a9818440c01040f00b102007100503c1c40114001d01e03c200e190342d901180c4002d004104000800c0d20250300b0220494840040f40c05021075056142e2100448050003952101c025090010703013541040c1c0c2e540001004c03585425821071501c6c040d460003c5c0d112029481000000c1150f00700d202801654030501c1486138544c05c00608445c0c0000005032203881c1c035400740f070800f007540c41914101c0c03c2d0b0486083c06d20070511a8a0111222402c0c100700e49140c000c41640c010b560044000c1c0d100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472413408 1250 472412158 472412173
    0x9060e1b10181a210709060e03030301090c0c050a06091106120a050a1103010f0e090f0d1b12090e0a1a12031e03040203070609050f1311040e1e0702 65
    0x6525142d5401103800148032603414107042c912084c07010140004020b55500c030b45400d111500760040d07210000740100e45000c41d901008000480d5680c8418415103540b10303982e030098401c035031045404507400d40e4404240e032100d60407406c207200035003001e078025514141d9400086c41d080c41c0401c101c49501e61030102402d1143d40e5508204000c00300242512a10354031200a60803c1030352030015406040000c10003840c1c42e0804181d1000c0b41e600400c01c2000c0c0d40190090701c0c010000141240c0700030301c1442c003015401503c04040d18090342c3d800700140b072602c0303040c00500c119400c050540d081e1540900320314890790307415903071500703460b00346070816400c0b46052200b00c024240f140b0940a0844450100c81ca0f007070304001000c40c40c0403456406111840080280001c614080c0040c0b8003c005d1881d00c101c01d2402d00c40000c42c00c00a041030640b2400702e16002c00c2c04d01c1c0703d58100e1034400c4a044029611156641c1c241c0284e03420445900d40c014038290412100410050203440c0940455402001d09 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472414658 1250 472413408 472413419
    0x70f1104090b07140c0106030c080705060f0d0906021207031b23030907030c2423030a060302040509030705010b03121204050c030111040302180403080a09060e1b1018 73
    0x2c00120045440b107100d0b00300480004c8520900641f0000d61103400300600051402a0003403c01c00c568010600c40c4c1001c1100024111400041e2902c002c0240000981c40055241c460001c0c401e12520900c1c1c458000208440f035034141e0311213000300104400005c006041010204c4c0e0031009507002c085e030b040c1025490754080c1c1010b80a194421703443c42c1102c46d0780751651a80380000f0403540c4840809901e5817003c0da00001205050b42c1c41241030b04290701035481c981d042c007542c5804003820704100e00d00400041c140c0035054205200658014000b00071a0030620941520380c0d00641056078036600307250820303165040000d00c618281280084030360408100300005101400050026a000d1158840c44141540c00780308803050b110bc0c8041c0e0641d994074501c14040509000050282143e161008000109800031012076009503940000110303800c1526054000302100da101c0000c0313200d540c0d135454841c81032a088414000703040f5a45410005820005c8a1103413800c070f111005c0140c1c02c14100308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472415908 1250 472414658 472414667
    0x503030406030c020c060403050606031507090603180b0702010b180103080304030807020f010e060103150e070302040c020313090209030f06070c0204090f0209130606050301150b031b070f1104090b07 87
    0x1443c14070650b281da541e4100080c18581050700290380542100c020700085140c00c226818000da03003200103813030910b40040d0240c070300480c5202e504c0a05440c4c42c1d803400b2a83e80031f81c41c01182ca5010200e10820700f00088024000c111240c122802040d0f501c050390343d01d24411684604895000d0200d51840c0d6403a5401c0700c403544054152404d5204124041d03049540a0041d40060851000104195031640c00d083c0d891303070f0310b020000500034540b401e008010710300030803000700f941d40540d0003250345070491004070729521606600d144012032204001c200307903e190300100504132044007240c0042d100c00c8829510f905040c1d444c2008100903206600050030701e80c00050320309014140c0d0080c031018039000308040da0701c102c402d101c4194050705040f0821500340300d5480034181c180e000300140080003c00c0c1283c10031034040c01103000b401000245400800311400c80c0740b58a001b2045032141e80510744458400754545c0111001c8498400b9034805051900c2640348003500500b04201503260880142e6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472417158 1250 472415908 472415921
    0x20a0807060c0c0b010e0f06060c0615010207090216050c030105070f0c02040b0d0809101d1504080316060e0c06070605091c17060603070503160e0301060f0e10050303040603 76
    0x40500005072511404a100400c94500814071405800354901d410030305081d13064001440c8c207120321001d120204099200180455114904500c4520300180300e0f4010b07464840389500180f8010300005006d41c180c400c00c0ca0b400d04061164040724448074030102058280e810440340c2000054040809000d4a40b0940088011a002510026015241e42c0105040e10b48404040d0390102c40000d0845880c1090424a55480c04924140c4900034022006c50050002e00b13100c1031165265000000c0e19561090480b4002d0415004681e541c03044c0c60024900c0200c44942034800d14640030280d5010980810b41c0c0f00d1000001b0992898001544e1b1881c4c01040d002c0c14105013485025a2854400310610b400342e1641000e44820340311180f810605845042d004102c18011401842440091034100b0300752038100c0740c90302c1440007100c0c03030600840b04800c014400a03410742c00c3c4107001070f0036946403402009841d604030801103070740d90300031410328580c0c481e10880343c05030b100b04400c1000505c240d1140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472418408 1250 472417158 472417181
    0x3020d05031b07060b120d02190c050a0806061f080112110907050c07060e0603150d082212020d0219090e07141203040e040f050105040b0f0106020a080706 68
    0x8801e06880d0310b51425035400c80c8100721851a5101c5600000d444d001c0041810207011000408041001500083d1510140301c041d00400d203030426280d0811003e0603034000900005413070796800da95642000380d03980000345c0e08140641402c2c00c034264110300d2003481c503031004007985829090703074a491400000003004017010b540c0e4114405901020782d6504810078041c4c2d8090317680710340780d80d81c51517007a0916003503611480600c010003035503c405445072819203a2260b0010f859188511084002c5030b00a103d610f001000c1e00800283e90f0380c4a50000410b11510340c1e04000c00012584481e10010010520080658401c40c0903070010018501004000040c0300b105035291221566a5503035000d580303c1000303082140d0007900d4207102e030200c885070014044004880c0021100b450f100ca0546030b1007070b130041620410740c03140040c09002042c1d82c1000d080c0d9001c4000c111a14140c208180320301d41c140c80741c0303802d641a4400061140d1002490401d01500107030711902e0041c06030b4a0700e00070030118014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472419658 1250 472418408 472418431
    0x60e12060609060d0515191a0909070e04083016050c1b030f060714030a020403150207030905010908030406110a06060303022116080c100507030608071203020d0503 72
    0x10b0780010310140000c56101c20300402c84104c2d41402d100491000005041854049260003c11000070006c1064102c1c23000b01520f001450fa150703882d14504101064100030383c400341c51010302081141d404001c002d0445140e40070800e8502212140700d503c002c5003060b080303968180b80840c400340b0400b104040402c9040c00e0092404480449603824485070f1500c0c0c0300e0324901900c4654640c1003d0000009401c0b540c00070304441d2400c3d45006d012080e030180d44410310340011002074a040125030444002c0c44c1c00103a1403c410005400d410081e500000040740000c0c2c208400040701e50140709400190751602e80a142086e08100b41126045400180108603102c0d20420002151992041802950081c3e02910045c00101c1800d91200202005450b108604004050505403036042030350300c069100c40394540d642407111480d80351000041080b1840ba14040912904981642c0260100c03070300030040c1c0305403590700c0c0c04581c0e5404180c640a805a00142039007503540b44030700011607002030100003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472420908 1250 472419658 472419679
    0x307030902030601060504080f120a1b06110301050f0904080306060705150703021e0703020309010e21100c050c06040f1704060f03050105063609040606060e1206060906 74
    0x1030700d8010b00717070710034008201c00040500c103075074081c407a0f145005c2d0000c0c0241110b04802d456690f8078401c0318107050422a041008481400f6500200030486070402024480e6042150308020260700c28441d15210f011040d81e10810390030034040715403089401c840c00d00d0840c1d84450031f02280d0740c000d203c1264503000700341c0c02c9042d00a18401450003080359550050f00c0d28452908007006a035480400020078609004200005e84c1c00012501026028a020010221070348007103428041e0381e0220507a542070318030107040c0b40c840c0010300300e118815208040c80700c220544000d6402d80318064401c0310f0360700044005000708011000c00016544a0b00031480c0505e20140941010741050f0000c03c006985510907480301907141c06054090701d01102d04616216a10790800300c00d02402c0007111502110304c1600f022010726401024641c0c5000d41001180e01c1c29241c02030003000d0a014500204101e500c041d4502c0c04e041260185082c40c82004218545500041044007000281580d600003103055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472422158 1250 472420908 472420913
    0x1d01180b010e0f271005120709020d06320a060903080f07020607060209100f0f030b0a050301020406021c0306080714040902060712080106030e03040e0a14040b041b03080306010503070309 82
    0x4204c1e18000240d800b0381110709005445030404051640703ca031003190501c000a04400022550104561621100580d0340c100010031701c0181c4030b40c1d03002e045020010002405000c807003001701007060f00b590f800b040049240c08100180345000d07005100005e64503003410302c00680380300014400d030a20781c000350741049403d81c00905d40717501004c011151190085014801d0f410440c02e51104c91549050803000005c0300300d030040c070342851581601c04041e00c54908050584a010298014000c0034000f90360352034459a010f0342d102030818054103100780050790b04101c40d100b13100d20f070709032103142025240c114984168206520144222558003903a10f01a1a0050350f1740001046454031810f44040303082c03250b20015000542c1640140309042c10651281d10801000c800c0300c0a0b10300717070000000c2039141c250461004003101c4a80f1129081150180000e21654025091140e03100e0b0f44015600c0c03860040031f0510465510000f002044103001080f9198025400341d42d10403050320b00020041740a8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472423408 1250 472422158 472422199
    0x70c030c0f06020d0c121e030204170307170f2502040c0f1b080d050106020304170109020607151838070807091d01180b010e0f 56
    0x154422161000842030410500402800c28001081c0341d0000d40b450664040c80904400400781d8010900e411b00f06410040a01541c4141e07140345826440c80030425401001070b00035403041c05900218000c01020024401c0000304036405036900c1803285000c80401c1c0041582d0343c024000703404d0010418400b2800386034610a43e00f2610400c00c1c0b9248544800e070050004403996080c2d00400c00131450500c4038141e4004001100048490016070315100c101d0400040074094600300c2c85d503940c2440c00009940e0350000283c0180c54000c0c070f03144950365010900d01e00f20b88030450000d4201006214030404103203e11008445041c3c13160001c0b4a0700400880f2121490b11008100d911508104e011110402011b0900b546100012804141c4600c0c81140c4480d150b0300411160801c4082c04c0012042445004038000400c10590342c000c1402e10f64a20b8040f03400e09005035019041c609442003100032090103000d43c0300d4130685910b009808075405202d08410b084411ba900007440902540c5500b146 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472424658 1250 472423408 472423433
    0x7080f03070201020a2c060307030b180411060a0c15020409020c07140429030a02100809060717060d030203160b180f0d03020304020d0b1f0906060f11010207 69
    0x11070b800140c0c2c0e12540b140140446500341318065448640c0124000300b0841038116105039842264103584940d14610b007200603011501107141c00034002a1044180c4803900719090003640b0810740594070b0400907051000038040c0001c3e40000401ea0f1030181c0100740d0030742c0e86c406071400c05c203c05841c0070b444040d008141d85c000e9001c90166406404100020440d4898945070407500f1102480944400c62841d03028a5003007110503a9010303010281c1c107096808114030382107103902900c079003849503100c031002d0400c1c401100c00342424000d00c00001c3d04940705440741000395010420388440307501c03a01c0900020b011083d1084003544002c00941c102d8400d4149000342142c4168814015450100040010a12000c2c804d10f62507000740301c118070115000c2400321007803001e450016101d81c8c8500026000042c00d007006401010300409001594070751000e86d01d10a10405c1c01c05441c0c9903140ca000c011541607100360340c0000c00d104082c080c454810441041064210000541410810341715141c030b9106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472425908 1250 472424658 472424671
    0x5041a07020a03020c010203030105010f0503060303070b18060a0219110a152a0c260d0501090b010903030206010b070c08060c090312120705031914092a0607080f03 72
    0x80305460b01c2c101581000700000080f001c2c80914119490500042d009001044104c41407042c080700181c4140c50030000c0e10955600190f80301c020b0b06102000400304064400120038a004006c0041c0240f1070a000700c8021125120081681d28a14241190406c0350305842c00700b1070250381d14a20100b0f401d02c006409890010500003a2000c01d00662501d001320107040034003110700050007061a81c0c00450540150342c21048a03410300c2c00231101550000c0b42d80c00300210654003c6800e8038180425805503040e9903840c0b0040002448403401541d10940500c402401070340480300522594125101400f141c030b21661501c914503441e108060f080c8002101c82009403600821a403020345020003203040404015a01d4901d8450400700c0c0100c000401403401c014070400201099401c2c1c20b010208025001080f8100090407440780c15980458090310035445a22954162041c114040001309928403000340651038090f50071014040c482c1c0100005643c40307102842119135141c3e191005611410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472427158 1250 472425908 472425913
    0x303020406091d070e01050f04090c08150907050a020f01061e1215090c0503030c010504020a0519030204110c061501021c0c0f02030309060d020702040f0905060a05041a0702 76
    0x341003420040c00880c1562000c61003c0540e5084403180010418491304214145400501c40d00150016aa03078441d036424040101c80020b400201c18000741e0008007050070a64500d940340d01d54203540e80015548803541c5600100001c00310341050300860040180d212a4010f440130810401e854500311102daa0000070011048088000c2a4180e00c111802802003140a03040b0201039071986003402da151240810340e82d80e00c96249090005400c5180001c060040c100c030f590b402000d00c03c0340079141c1038a04074000c4003011404a518078000703085400c0b80e000440fa81129a01e03540802c00541503058840302446800c00031010032000078022a8070825040c10656107400014000a107440e00c98488a03419680d41c0c101001c44661150740480c030541c209800300ca02c0c24042c00042d0440c41048a219481003002800021001d41500900345080c000c88003042004500000c24081c2c1d8405200244644c10000000e062042d2507840706811030b015400ca8108050031025250414006a880f9400350303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472428408 1250 472427158 472427167
    0xe040507080a050304091503020a0305011a0a0810090609050a05030307180e04080d3309140c18041d0105071706010f03020c060c0a0206010609050a030212030c0a030302 74
    0x2010000c11008284400003460400e03901e072100d54480c0200e01681901036103c50030f113240030b00801c0d2030700c010b16002000040c4017a03030b0303291540c02460741c4e8a402d0100c1c3e4020341c0580c404d2401125031000c4400d400042c0440140c0081d40e98001c016024080714480e40d90181c60011030400c10040d0385551090004694030308003000060600380f40c066003d068000c0c000010b020185d000307038500f6005075201950649481000010f2030241c0404082c0703400d002c8080c03a181c6500000084d0690030520501040d859040e22840c0c0c400c1542e02d05c80360325810b4048800820603200b801c10051400800e150075030344c0546908000202a01c4020094001c20b0840c00c3c522850020f0a1190b1908210300f42000c4000b0030f00e100c00c4041d40701009104505010840190240c032a02a0301110355914800007030720040e00d0140421b41e00390300030b9075050005100c2c0000205450317018880840550740e000340345a030058038503400c0140a1084040d030b201d0074001404507110308602001460f501501c60380b40941c85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472429658 1250 472428408 472428413
    0x1090c180912110f0a0606060f0207030803281a01080c09150c03040e0414060f130615050303160b0610050702040b0d0803040602120a0c021509010f060e04 68
    0x45030a03044950350100c1c58080504006041d58003101c59100c42030418200d141000b4000500702404451003d00a014040440c8100310041e8442402d5078a40d4880c984c5040034860100ea0b190341c5400001c00961007000030450a83e6644030f0004032001812009444c41080c804250603140a880c0c06805085041c81d600360940e001312a0961051030f4000c1c003802d08002e04002a030f100a001c49a50a83e0400100307030200401c2882160042d20881d0120006421715283c0900700340720500c9008110b01800000c03502010580c207003030b130280b0030024042c0c03440c2c98075440c3c000003040344907100c5007500c04500b0005500d0301c1c1880a000e803414008000c42c60003c0a041c60200d01070300070a998869140e80540400c565000020380d114240c05a400080c40209500452001d000105024190010120030441080a1900180304046001135a42246c0c1c4a05040c007082e00e640f4820a00941c0003e500b10512201c040d05a0340d002200a001240081d0140c4030030044850075006107046034008806c1009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472430908 1250 472429658 472429679
    0x1506060f14160c23280303050c1614040b03010c120f06080105010e0a0c0206060a0506130519031103032a1c03020304020f031c12090501090c 62
    0x1180aa2410101408030903400701841510520441070401e07007801401c0000d1264100504018041c11642070003103100d04104c084e2182401c0415911414070b08410862031803005140b0407960030741481c940711a600710b0b03900b524241c018014004480c4503502d8050038840b00c540c5000000c000500368160742000080501083d210600300090084c0c0c1803400d0080c0d0f065018210301030a0001c082e0005400440842e030070080e04455200880c2036080c00004151181420a011300602d81c0403000c01c800c9102c80c0c02a61100c1007280d10a6004240c10340801050070600c00600400c1e9144240a64154941c000220780041c01845004040440081801041078a44008403100800c070029414182d480c0d61000e070341810764001000d803460100744140750080c100a940354109c42e80d03540c03004d1840d04510040080d001214107078401c50700014441800d04021500c1d4400f07a480e0704a158240700c0c01c234010758110700c0070300040c00701581e260440c5021131002c1c420205141d00c10564212400c1ca800c000c1203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472432158 1250 472430908 472430927
    0x90103060608060a0608030a0c0303090602041509080604320a05062406040b0a12021606050601050c10230c0301030b0c0309030d0b040204031401150b0901020c0d050307150606 77
    0x5008a24000081c03028140000607144070350012715010321000c010b4501180981000c900050000380086008540045040009a040e0744d80f03030b0340c800b1480c3d0b0f96840d183d40c86000740c030b02034201c95a0301c600352042d9540e0300140c003940307850724109060341d505001d449140c804606415505600280f040c000d030540700e0390412500d040c0210304042051060070008085116a2080048000c0e000811000a5004006000592655000842d107900c100f0f52285200c08100500300c0d0b0b418602000200c1a40c05803040c0d40c001c01d111130040460602d0382c0340b0b0f40001e00e000200c02c030032a104400070003800b10104103100d11501c40d081610343c40354510f2804403c43c0001a0505140b80c50a0041029030200001520001100402c001c1202c48541c004540288074681010340403181e1100480d190a50540140740d409800c40880341c56680c2d5004000807034000c3c25a8103006030411140d203001450840c490142da180190203070307490a0b04580c1d60802c7c04400307415030070007191a11002c1146581000102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472433408 1250 472432158 472432171
    0x703120e07030308010e04021f0804120809030304170c0703060f050901050c03040f0c0b0d0b0a09060506090402031b0a0f110a230c030339030405091509010306060806 73
    0x104952410b641c0c000c0c1280505000d241c2c0c8402800000800f95501e24071410f170b044543c040c00e098526046100102000130803103054a041e0b550400d0403416500c84c0032424410041c81e0003071400c680702e07965456800c0d908070b41400e40c030980c144080c413482e140910584008500c616000a8895200102c2000340c5070010400c1b0801d9161a0030403402c0d010030004c90ba8440d40c41405c84000d4170107460030300154201d40d004960301d21404900406460790907800501d4002c1c08440f100b0905960b00805000c0d20194001c6540101c4d003400102818103140e0060750300840100017070304050302400c01700c0750f05400c05c3c480c29000a08031a0301004e515005000150411440800380250600707030389540c0071001015442c1c1000000c545020158080c060007074003d50080101502d0717980c040480704500a24100c42c410515000322031030694821030f010034480709040844043c6062a01d007104005182500500055460800440c0464281c0c0c420078054041c500c074150020b046424003815a18145004010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472434658 1250 472433408 472433413
    0x1309091a09010f14060901060f02190b042303040504020d060803181509010212210406060f120c0b0c0a06180c15090915050306160e030706090b03040f080703120e 71
    0x10301205d078954002c054103564850508086402400344101d213049107814004c42c111501d4001c15040101c80003a05014034056610094400010880030203180c079112040922580108020000d130b00380381d005006801100c46001485130303078036800c80b801d69015103540010034881e050140c00c0da02e0f1200311009020010b584d52810260044000307540c2d0710720740072041c0380b40001080e0000320824954040c1130840007110400010300741071405401074980345c0a10a038001c0c4258010030368002c1074184031050b54000647ea1441c5180c000d80d222107520840004095003da071400201283d0036000b1440b1042001c00140340d0034402e42000c181c3c00e1215005031544003003540300c082c04690f0105400d02038401d4200d0000360422904c83e8071011165a07400103405001c1c4604000f81440800c03103985041150381c0340c61841803000c02c101602d5070014043d81001c0b69a84109014014024018540c0702c0d20400400d0f10740b4203940c4460f00150080071080f00000c5100e210120305c0500c9024400324050040b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472435908 1250 472434658 472434661
    0x130b03090709021312030206062b020d0606080a1406010506031e070306081b040b030f060f07090306020c0d0e010e0d0609050c040923031309091a09010f14 68
    0x1903540c540030644104064141c0105100d800c98a800350050000c0120b1600e04000940c0c6141c040c2d19084125030f41880743e5100c04c1c0b908003081c03190008007910b90507030b81421108182582041003624000794244c0d4043d0751241c0100e81500204139001e41c09010349414184203005420b51841d041c0c0503084207000701d406105202d86041e00750f41000205694601c401007a40d5a81400c40042c4401e90000c4000e10908564000d0140101c00780c5101d054142d506111124442040c03641d510204851104664803081c00100d81100003403080d90802c3d01c81c0f5204024a940c0e0b20782006a81124a104146804c4540d105409a400032918001b000703080c00c2c84c11600101100050b20110071020140109445031040020083c0500055002810080040146860a0400500c1d291b603d944088003103c0704581215040400025903000743c0c10810604030480c2411030580182002c501d0032608581000010014008904081c500c14041e410002886160354504502694011b11401061006080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472437158 1250 472435908 472435921
    0xd1712070c140c0a0510020a0c06050403140109170a181d0f0c090d0305070c0308070213090519020315091006060c111c1a061008090618070812130b03 66
    0x460b13801140c00c21111170003040c1d43c00c4030503070400d070052000408004007840e01140d016048000382090341c0c092111200c2d12200b07083c100d070032a820010090030030b44518240b181005841d070018000c0d64418a46014201c0400700c806030700002581180b8107401012000460251001c10035030350210b600304240020f41400040c4070182c5c030400c03c0050107000420060014940904101d501701688481340002c01941c904010b4041d40025800f00e12680c0ba506030b20034074032994010f035030f12503070044041d1080c805c0e01345c2c0c07024480000340340c101e0301805824050742096151a04d200d1041c03000d43c01900c003c5c0202849130b41180c1d015040328050042c944600c030302155001d010301445500a441c0000c0c02000700383d0502000d1000080141990108001c00ca200e50041c0c00590150784243d4000090200f81e8000303460706d085c1103502c0078442d8402000200300035051514a01102010003e86a0031600d5540c0076007000340710182c03031550a8001030005408440500302c03800401000b1045811030a049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472438408 1250 472437158 472437169
    0x60f01051314010801020d0e1225081206090709030b010b0306030f0d030b0102010b180a0b21060f0a020705151b0313020a05040b0d1712070c140c 64
    0x180201401210612080c824007107075540400000c01000c00c1c1c02102d50303500c0407664040d5011b0b000520310141050030042040b00001100c402d04244200020b04190046420044110441c401c40500d00352240c0c0d4440800d13680801040800c0135400658504d141c0354050005050b0b02500040070800003000400114102d001c0380c5040d200e080203840c1e5651540341c000381c6090035865507040280600d0526800303072034141e400707070950031001c0c1c009110340c078410400c00c44c89801d2203000118880281c80042d03803454040d48a00f40d143e030300502c1005d00b1694640c8400c1c81410508074440d40e42d001d0024010100040c203100781d48601910000c1d4904590707503441984600e4801306a07516070601802045803017000748041100708050043d1551a890001c011010302e84580100340e008903c4000c012500341454000e622441c840904024581c41099483e404101800c91604820a205110451140400d481c005000e010940e45400f00c1403500d041c60028000b5407840304102d5880000c1521407602e60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472439658 1250 472438408 472438411
    0x71a2d0703051605030c0a2d0f020d060528051509044b02150901050f030403031e0203070215072d0e030604020303180a090906091202060f 61
    0x50300e406a26124034103c881c192010102c0003c1c41804041489452240d002420340000c0e80511510310b0503c9403403800c00300c41c46841400010740c01c50355001d40c0100c2d00c0380ca2040b048038809402202c08400300e807281011101e0a4890950324920980818092500101c00414600034440100002c2c01c107407940911502c1d00c224100d002d20420030000342881031149000c1010008800d40e5040c2410182c110801840508841c06281007150241440c02c40c452a0400140741d01428400001c500d01c2d41051154201030402810041c1c100f00103200140740070050f500076403203500d011810502c600c0c640c885440b0b0706244c4060583c4184100310110383e0018103244045c2e1584901000ca480f82c0804450440d0001071440031079450413064000c0c0513007901a40b8420031744e03946a007407444072001016240d000548002e07501d42d005010081410042c48004103050700010030001580e6038900158040d100300b040e090350219a120f42903414010002e5040c90844000d00c05002140750404144040c08030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472440908 1250 472439658 472439663
    0x504050607060905030c0f0601030c06020d080a02250c030302151006051b010c090e011e090203070905130603020f0a05100e0303090d1515060801090e071a2d07 70
    0xf124000b031000d000080c401c43e640003584106803007030070610104132941c942082c131040780d0b4500c0c454400181c1d5440482c1d034034004281c66441641c607488a21040c0069000310a03440703000810341800a00384414401c400b501d0601c520300300300070a80303075041c06414045500b10141d2680e0030041007199100b1480d106900b81d41050401e9602d0740f0800c0402460444000d4100103658078000a02c401c43c0c1c0c01030801401c80c0d604402c02c030b41c660f88488095001305a000514080c400d80303d1001c3c0000b100a402543d8400a0380c5070202070309079613000140c07002280440d0144440e0361458140254200070103c94002041900c14000c0b141c68070740400c0d0004d03600740811041145004d46920999803e1040710a0428000c3c025101604582000091140d040f80290400c03440c00204a0503c5020300a1708200d401d00d072100c14842e8a0203c141015142e05a84c0300824010580c02040314000000c0c44d481c91000603d40b030b600d410381e610f9210141030024603a180801d09000c0042c1060010a04030f0310328030b6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472442158 1250 472440908 472440911
    0x7120c03020102070b01081b100f110c100f020c0a03030906180902210f060d03081b04090204080c03060903030a0b19081501170616210c0e01050405060706 68
    0x9030400701e00a0140a20041024002d0000051012400656800b0725441c08080b0b801d641c182c08100244888501c9040c0c002c03d24007030941402c43e024054043d200310500c02968150921080000e90503800c80c1c50074070102d8820400b409801da410800140000e0007514408001804c54402030f01000c0c403803080c14100070144c0042034640c16100b441200400c107115041d5180d041450500c00c02c02c07140c02d10031100300d51300c40024101103d02c54a00f40038010140c119600f2540549003105c143c00300a00e211000b52014142d110340ca003082c801400201004880182c58508103c0040e04182d0701d4403001d40700790b1011084c06400140071080701e8002007a524005244641c0c0b40203c1d10030190850300d20a10900150001001030b80440c0d0110f6201018010750346680e2540421180440c0180c1841c0d515400f0400081d80441000003036001c07648141005101e05403e004444500c1c5d001442c3e050001d81c9802c03130940316a400914a000c0c020f400d003006400e180c1440c01040303042c09001e50150009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472443408 1250 472442158 472442177
    0x40605040e0705070516050f090f0606070f05030c1c0302181311030c0a080f0705040605090d021c03090b0f030606181504080706050304110d06060b12040c09020712 72
    0x3034001c1c0102c5140302c0c5d000064901c81101d803001808403001602c580c6004a600390044072580c07400f054502c4c440c0442c01d400808039101c05050142540029030101e800000b8a1458800300f0300c01c1018180900380100240f41c0084070449104841004015040074140180311001401140c1070100d41100810350349415020361401b003d5000c0c11500000402d10b9400100740001c00c5000f000030124403100b03481d02d0314140c4030f02c8003410700d0301c2040300c6038000200d0a100510a051180004081782c000c01410701541c0e540d190005219000d407000c04032101d00e90131805c1005c058101e488a401014120042c90406a0f050303102403540c0b200400040c0b01c1c1c40300040c00c5100700c0d01d9540314a900c8101420601c1d140201d03042460b00e66105000d1100e2520070a1000142280301e07108580c41280d1241200b014498003909002c2d0791007851004a400c01d031070360f60110324100c1c07010144c03081000710702c0d03240d0240c00e2908041703000080740c1c0c0020101900400100d07012a40c00a816081b0006501e0312403100d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472444658 1250 472443408 472443421
    0x3020c0d0b1f05101812050a0f29060405391201080a1a04020604050d060905100c0305060a0b07230105070f030f050f01140f04050c040e0705040605040e 67
    0x40d08116002241d00c003010b44131201c0340304c0d4003010341001d040301030000074591500c400400c5040c4202c4a0020101c2c2e111120810000f8242c8600f44240d40c443e4400385d0052200b448952000321900444898050300e10040240c185068012260003002d103006d060307a1700d1155083e6006250005076980d1180703001c1d81d00d403d8504c07986003c40318540c400031020311465031203409881d12150242e006a419400d403205c0011025a2401400d018690086c2950f03c0c0925002c1881000b0b1905c0740c05172503107641d03100c8a4000c00e005008100c0007c24540c4005040c11039210090108c0310b018200d207015a8070444280b25400c0821704440042e40c000d54070401a6484000307160500840f407150f00c089500740004d000c2d89030340048072004120450f481c148561812420204220344c0b044a0040914007690010040c00100801c510082003001c2e00316085481da03100420141d500988420340502d0001408100f80701074040f40c1500300384d00c5d20740240b07400e140800c000c103240214011032414404100c0454003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472445908 1250 472444658 472444711
    0x306042a030e1014160206010e0a0b01020a02040f020417010216023a031707021b011b0b0f0c03010305151e07020f12041d040507030212010903020c0d0b 67
    0xc0701007014080c0071242c031300080f5044040c01510f131864203651480105009600101c0c255040e80c00c410802141a0b42d00e0201c00d000d0140c2036801415070084050f2840561105d001d01d03841c2c0100b103072015903290726040c4240c26801c01e9141004061b4418000b042c142c403440628292419012070f03005182c030011035a0301d041d00081035030184465800880000c5000807803503290149900944428840409915002004d20002c07961000180c1110400c81c03c800111381545490141c10315002100824504c40341d20350390741d40002502c0c0c0c160600b003005414003d4041d1298801c01108445056514596030107640d5082089105000d89a01f030004299040505151b1094142d4209001e01ea0805040194950503428a07442280c050351000305402c0c1d101d28101e904882d04c08258280c007990181031030b50031403c0980120341c00d006003c2c0000169668881e400c94800d41e007000001e8441981c40c01030b10740496001e07068040c8011544081c042110741c101560300150721814189900300e503d04080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472447158 1250 472445908 472445923
    0x10b0f090a0605060c0715032f0f0f030103050f070308030403110c180a1d0307030518030106080d0908160e06040b040c0e21061906030204020403080306042a030e 71
    0x4d07000780002c83e40d00c04c20500001e000003107441441d00c42c3c0100200390411026a29501084054030310001c1e0302d4010700418551800b409050008001d04000d4110106010b0790710495040900c184080014002d110703040c000d003031b44038100e9401081c0b064910741e1440c0c207901000340041d06012031658824440581403000050b015001801800c42c030702c00c403100ea1010746042c0d0700041c0041c40d008888074051181950b4140a90103540154100051960100d800d64000031207020300030100b07401322240d91401d01441014101c00300c00750820340240da60007403200509620414107644500401c0790301c4101c25003200c0a5440418030500540d4964010501030081d110318550030914212100e65034503403280805440a070100e0703402600035244101c0001d0103000350712203000b03900840042000032006180488080c0d50716803020410a9481d00002c04a8205600036211907030f00104004039842d180c440d4600700c0c40c41d138400c00f02512b842c404220110b24440c0f04a014075030b81e1040880550404c10500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472448408 1250 472447158 472447169
    0x3091e1606030603150e03040902090406031a0105100203030709060c0305211f210227010617070e04020d06030f050a0c150507020405040213150611010b0f090a06 71
    0x10351200d6540c0d04020001c1542c0c1c030050355120101d40f8503515800300345c016100d0600030100118103207030a10341400d0096020a00055000e0768400300080090410003e000c45200003008400303035507260009000145a164a40500319001041044100da4120039200b003601d0040ca4005c2c00c04503503240580e554803030302008080c0c2071002801502c803550a65002d81c805d40c00d800080d0211a902110b5088007070301802140c540107540c135a4800c00606030480c7d200014002410a900c1d6020000c2900528201040e09070161320010010300070740d03070010b10002400c0d004054022261802c0364000f404191a42e050a10864000602e4000c0d070032140c121202864202404078038100c10340c5082c60780c8280d10401100c001010207000070726030300200442c05200c0f00c40c0d06e4042c40c02910b82c3c01c000040400400c101c2e44141c041c0440f106c4c620407807150f59a42007407250800400303414003001409040c06940326000980c1000d2482c502512213650503e2012002c1c0d44d044007546451107240041c00054010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472449658 1250 472448408 472448443
    0x312010e040c0b220b071a09160308090a050109080a03080a0f020408010911030706120c0507080f0c070e010b0409110408030c0d1b0b071209061b0e0603091e 69
    0x1134402040440e54004a4102c5242100441c41c0e441d020210180a2000c0c050f1003c0145d04d5050000640c01ca01254019084020ba55032042180864040d8028a4000359544400031400701c0003070520100e148050b003400d08ac1150300510301489141d681501800090401a00e6801300b4544c201640010043c25002c1c10309544072602c4043c03050081803446806d488107007007442c411246041c046000401e03503d103641c0b04620041035034802c1001e0b1200b002c00200700281000000c02050350f080c044d105002d854084507560398880e104c80e81c9131440f40d0700b21280400b04903004212142c42081101c3c00c0f5021030f1004680c0c14659055065140110b501c58000d0707000c00185102d41003408a44000c011040361210351400041001d507210049041e0001032641110700c1c0400c0d903190046200382e002c54190310002c100701c1250b641c5c00b07060b0b401c0c1100c81007254184522440300340f5001206030703000c1c66040c1e45071810361800d40001c0f03960340200501741100d26080c6800c0c10310140244000e800c0e031910b0810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472450908 1250 472449658 472449667
    0x301090b191a040213090513020102010f11031807050a0f08011505010806010e0114040e0106020f0a080d050c07060f0b040c030203060603010e072303160c0302061f080a061d0312010e040c0b 83
    0x4580030107523168800b2401035281c1000c41c54201818401c0c02c2c1c0c40104a5100c40c02c40d038850300803500245c0c0320322802c5181e2052001c00941643c50344811f01c0905501d40300080000d181a00349802d545003d40b503420f180c20303884420f1007641d902c20300140d4061000d00c1c0c01c112001c202d41c01601e445004940035440c10f02c00140100d14081c06062050403240703203a08480000c1c0d051f80f18152213148556000300b0402e400c20980840080c02c3d004580c0003040101401d1404a03e0303a0b800085074611850240304c40e49604100c88103190174480c1c0743d03440c0011708003585107140c0b07400004c0480c401405003601240903500454074a9115200100070a6400001c60708240101400c001003900300702c2d0a081e207003110b05c24404c0e1040c4034861401d005a0726400914150722001502000a540f01600350020100303904001a0921700b08000030900340241e10000e0700a07983c811800d24100c0c040c41c0d15080d90b1040281804038502c52158504403088103940e0040c54603a4901303c0f0390030b036182e0702c94070f4803076400308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472452158 1250 472450908 472450921
    0xb040501170f06011512381c0807061808041a0f070b0712150e010f0e010308072117010806240409020301090b191a0402130905 56
    0x20503104000c8090750495011410044441d0740d140024091015200110171021041c00c2c010b1040540070740c80900701103074030f680e074508001d6101c0d070f81600010542894a851804224000020040814250f512a440703070400c60b895031b00800840d00080000c5c000291300020700c070580d4882030f8030044e69034965170f40c00c000d4108178100b034005000f091007481200140305844e0b95040100c85103140d17902c58181c200030313081e140c014020703800030703c22402d201a2034a166220705880c4a8080b00141c20b41d15920700030f00b000e41c5500760b040b05800643e200c440d00e8800b48030786407110102c2811030354032103140382d910303400c500c0d01e00c80c8148541f4001030103d42c007002400180d0380143c042a1222714045000c60705c1e070b90350f002c0180d49444c01c0d41e080310030341e541507201c002c010002c0b450110840c01c0a0300c0418200d00a50109085030092401900c031052020b00744102e48100b50301b0b8101c1010031a900740982101a1004820b101020100c01d200f540c0c005109003d540d08002000c00034142620204031502c5c020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472453408 1250 472452158 472452179
    0x11030109140705010804240b0307060201091e231203010329040206031506040e010e0f010801060b030a0c030b041e0c080112110102120a090504140402030a0b0a0b040501 74
    0x202001c40a0300900b8070115003544645000e03845140c210b41045e81c01e1600d4a61081e0340c007000d0014841d8a910b0b0001c2e14001d8504100920062401e540001103490041c1044001090100c0907c2c00c600019019040814031103e019080c0d03e984007503443e00345905030344151074132002050112a101000c0000402d010b1031410508a0650312800c55188110005403c040c8800c2142c00070361115003070010031a2402103114508144102030907151510361140000c040b46542680084440b10314441000350b040d601c0780c0038030b005011050003884005d0924540d0802400000d2102c80901c0d43e404111203054130a82000140c00c902500c10000020f9030602800c01d00707048025000744a0611440e408800d1065845038121401550900c10f81050760380e401d1414408031083d10304512400d060704000741d030800000c01d44540c031501d48582c03c0f4035000c20310090b649c0542c54a40442c401c1d40810026840101c3d4100c0601d500400e01c50003279540303c513990002c00d003070f4841980040c600740010840f103405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472454658 1250 472453408 472453433
    0x406140d0e030a090b0a090b0a0215090105060414041716140106050102070b070506040b1e360c0906120d0302131203050d020a0c0f24020306030a0f11030109 69
    0x1666608200940c51702019400c0c0d11690000c0c0340001c0c42144104002241d41d0064911081544103a40d10300c84071081d10016207209494501d130740d940d19001d1083c945002e1143e5804140070450801541c03400d519001040c040110b1421107400f00003881d40305603032842290b20300041d48428445400c0c0440b403580c1d4024001ea004040c054402d00601141d0641d59905441506a103c001803002d40e889135076030108401d000d4244500c80c1a6503146403505100100d0036072041894128192320282c502c91041101c030301d41c901d407015801464044035680040490109080007040d6060344003511030743c0100c4d4a4441c5000360100318002e00444011641d41070300202542c40d0441081981e04d80c0f0754020b924140c85459000b000f080040100d8002c50740e09030058201902c141c2804200b070140780e100d020302c445201d881251042c1100300c110224103403494030200f0b01b0010321000c60035482c11101290796440335180103405018601031190401010b0910f1580d40e0340060b000380954502d5107030920b41c2c0c18a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472455908 1250 472454658 472454677
    0xa05030a06050109080d0302161e0c1508150a031b0e0a0e0a0f0c030c060f080a05010602071806080102180a0806070801090203040f0c0312230406140d0e03 68
    0x28090002001d6201302094401c0c1d032446006001542e6030450300b54000d600c84a1040791070403180c11103101181d02880a000461070480382070f0f604907164036103481c283c00702e82c1009407050204254026a90303442a4030383d0340000b0000045910039900d00006000d0903040d400100703481c0d60381038103143c036007401e0301a142142d02114407511280c80d101d080d101640d00805a50326558030a030210408a20740490035944503005500148205407a51100c480c0c201c0c036500031300c0100d1009123541072065400b558903503106000707140402903541010802515240c0c14840c1c002c5044c040a0b030050360b85500da110b20002d2403000004c640d5984446280a03500d50450101c40c4684215040081d0040f00410840d00c80d00f4255100c2078140c0c00e10701c28070000e400c080c2c015904c542004080750b0018028003400c070043c1d1302a0ba00601c2d8138024901c018094030881c041204d03528507040750700c044200b8640035603040c1c903858105800440c6401c0d903d5201c90280c14103040c80c250900f04c0a10040034003000403c401e06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472457158 1250 472455908 472455911
    0xd050c0103060b09150322050a11010810150e06030907080d02061513090b0906010e130b162307171c1a032a040c0c030e150a05030a 58
    0x19962125240f0714020011041e1300810064034440094190030000c59009011f001d180300100c00b0301d4001040d100694004407442d074405c0101d481440f100720f0010420820900e451320080c039264654481100e261b10490010340440c0741403199940c002d81c486406668044c00294407071408042042d40c03a404c0b03100b130034000d0081110780c8103001c0c40800c8203441081d00d0300d401807000c1c5900051140c2044400d00900708584d4a950741030026410a01c00341c000c05030000180f4155042c049594240c0e40040d16070400c01300e00190b4040002d003a41c044a500c600b2000391040090f240f50800d844400484101c1034000400822505d01003900d0705c040d04505000c0c280d0030f02c128101241040e0703213200741c201e641da040d1244190141070000759040281c608540c0d901c01400440c00c00301080ca094840203c60b42c10b4252280d91000512214203c07030603d8004407000e00901c44409409440d920b410b40000c3c013008000039481480382c40d00c0450100140c2090301895507004102c000030030b550130544000300c205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472458408 1250 472457158 472457171
    0x5121f1d01051b030f1f150302090307080d0e010c0224031b1201050904050a0b010602011a0a06090315230609090109020913060e0f0114010b030f0f040503090d050c0103 74
    0x2038061802d50344617858441039201340e500d4005040d0090040850401d040754140c3c1004641c20000034800d41030840b03161000740c1c403000d0300710800d82880081c0e04541c415512144880025980c45070b40120003400030b00304404e0a0802d070011420790035000c00d400c0c03200c080d800c020070800b03070580d401148a101007232a11342c40503000c81450401e40c80f981c0c095010081700140140100d1810100144d00a4410803c840307a031086070b91745480c280800d03406100546d641d0b000340410644000020140300408807040c800300790400f4409001d41103c1d001c083c0c2038078082c060070486078501394480b0038441e500e011050340c80c020781c1c0b9101c582044112605400341c21440041a540389050142c004c800e907004003401c4c0550341d0405044000200b41c1000e4626545a110b03610b200d13282404040c000c05140800070580001008491900340c40c1a032043c02003440030402c000382615412002c07508440c10300702015003629542010340c0b130b60086004299001c03180400c9281004400107480c0450340003a2010b2040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472459658 1250 472458408 472458451
    0x60f03170903060a0509010f050901150f0807060309050f0609031e0a17090109020a15030c021b01031518050108060601020a051b0312070609050705121f1d0105 70
    0x41d005105000780c140e4800804140c0b180119000b035603028105100020f414100146a80141c98050710550303003030303590341c81d64403000d080480b04071f0f000e000d01e580c20b200e409181070041035917642188501000c0558900d00c01d07041010900c8840e00d00018001150702d24142551003a44a90048200c99100300010912101d100103000c16a10b0000e26074481c2c5911010340860b00d400030400030828100c9560b64070a120069546480e00d20140250f40c01d80014400d0811010702180c26104405041d944440d05240c801c4580c0c0e0881e503915402842c0215504403200c808000034559030b04402e84440b40d02c49070850a076590b501190403030350950101d41c16600c4041c010ba032140c0034003130003030070a4000300720794544089402103078100c1c80c00c09004c07640d4080c41d4000d0705a2981102004440d0991680c2034001031000c20411700e009003008460301442d054a03100b210f99200819403080b190b80d4183e0b000301c0441815076109130310b1800070540c607020a420007080c0354000d182c00c0722008000c0c240c0081a00c2c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 472460908 1250 472459658 472459703
    0x40605010c02060a08060a1503050108010f200a02011b03020307030b1005180a090507020f101505010f140a020f2112040c03060f0207030e1203030106050c030d060f03 73
    0x81254000d8002c628101076048105c0384044011301a68008660510008410910f202d1400503000e4035030300040c642d410091100c0c2034940c12f08054402c00c0c201241070300100744c80d00080b9500380e4103c40c00da03500c402112060b405050992144114101a2028003c49a801d0b4004500c10b8265540801c04c000b0034404100a45480001c9840081c0040c02160f44800d1001019001c0c400000c12151042d03540d040c0300d40507603000319078000c0103800040290410403002c1041c0c5941c26014002480ba0307903288410001d048209100360741c10860300407080c2039218080c8560f810704011101b0419656407001700043e5036003800144041c800d100ba034202c02c0f802e050441409020305a401040b0345018030b100c0e001066808060402d0760101e20000c000030004030b40380700d01400006580030142e120f03201424043c00c0030410300900380c00b8400c0607040400310240801182e05440040c2401902c64800550b890305c0c6014801005184516040001c1007440380803501d00f084902c5041114800c00801a0702a03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 472462158 1250 472460908 472460927
    0x5060910180b01020a050106141c20010e040926040b19020708070609030b0f13020127090e0c1504090b0112050a060e0a0903090302101b060b04060501 66
    0x780100301d00d1030645252000390704101c00c5444144100c075641100c5448031405c4030f805920500c0c502c186014020060304100c1d003085664150002400000e15003615120401e41e81c401c80402000c2c4541581621680140103848510b0000340040140b0385840c030307041040503201c01030540e09100749000380c401c550002040f901507030712058195007001d0961410f0a5900b100d078242c88158018614041000341c03040242c0c00040a01d5a6410551440d50415401e42076010b01503a8002e107101c410001012041c43c401011981e081c60440344e1040400c80144004424085030f41c240c011040300010782110035040178034903404030810744100d0740d10a4104404042554580c82c04000103000030484e48699600950244d101030420fa04101c3c640c02200d000c4500032900800c1d804e9580b041841102d08101e0020b90044003018208010412a100981035809612000340304002c0e85000d08521803040400c004900050001e0480d038126516208014040100c01c41d07001c0c0b0f140c0040080d040d03201704c07a000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 472463408 1250 472462158 472462169
    0xe0609010915030222060f0824060c03070b0a0f06050a1a190309060c02010c0507080f0f0a0f020f0c060415020c1c03030501090203060a060f030b040504030305060910 73
    0x2541510b01190320080500c54005081415401c0c001c860400c100c4691040380049003604059081342403910180080c00041401c500700100c0004200100c0300398640790301780c0c40d8902440d0303c2c80007010000482e18868200345048902001c80da000421000041050107490a040103011140c40b600152040302e03500d1240691080c00b000082100d101c50402801c0720741440c8084500d8419000498800300d01c10140800000ea6198214401e1040300c0c0b20311600307059584024003008000510051a90145d4035019100181c00203403000440300040403200402000b4140c180c488050100141c051441815110003500030b2251850303665030041859034080d84001c0250342041d050400e104806508103550806501c074403c2101d0a5075119002030008060362000000302c0b00303451030001c00381d82c03040e400084800e00500600515580d00618407041e940c840c80d00f44003000c146031085010740440301c401034010745040700340024140d043d045140f2540c4160b800450a860328541d084c02910280700b074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 472464658 1250 472463408 472463417
    0x209090604141603150314160b04050616060c0305100906081b04090b090d12020301050607020603041b0f0614030411041e0608030310051f0806010908030c010c0e060901 74
    0x183c2003803905111a025000500c1c000414048812018a4503c5250020740740041c4403a86074a010400f00483c568060b00008002401d528140001456004600800f442450080344000c502d0300a0180c449940f42c001c0014060306200c2e0304060300404045e14041035800a03140081560080380c0101c2e41100d21715402001c4400f407003160781c01082c0300d1040b0f03580c3c400d450700b0911000c40c000090103809940740c800600344a42a0301000340543c0c2c01c1d1800319107600c0c010300040062380e540c04240d4400c86c1e010b44182d9500c1d561450580000c0180204900351142e402c6030200b40460040c1d082c20a40f0446d840c1c0c10440c00f030010711881c840c041100e0040c028601500740101a080c03d0308488500840c0248084000a8680d080405e4614a800540690740040100610a0510084107004180c103582404241003d0a011200c1c030400c100044240705408000c181107912440e0240024508401601e844029082503580600300a90340d040006400d01780c102c18510380342c000c0341c0b40d07420161139 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 472465908 1250 472464658 472464661
    0x412050a120f06051e031c0804150e030301060203040f0504090209040609080408010c0201151e030314160f021305090a062003010602060108101a010302092101020909060414 76
    0xd000c09402d031240c1c140e910a0300c50360001400d03210311035070f401107851098280880340c88800c00d143c60b10b40c9110b4070b8055170410514103e05250811001a00280c20900324800d05403c58006009080c04154031030091100000008080e903012000c4c20585003040029011940e40d20104010b413200c1d04400f95102c4414008076002078800d43c400844a40b042001a06113a0303240700144c21501d17040400c0001d070351503600406600c98080301030310103064001c9500b004000d00c8821031f00b80342014040181030000040f074515000c0a10010b0f54510100040314204506039031070140401c5003454000c0b4003503040c0b00b603400112610b80c080c05200301010702c01400410042c4c1c4516000e00030400c0744840401d0400825010250500001c41c040c24036078004200651501e0f1082d882c0c0035102c007848070010718181d00e100f4040e00c0401080640002484c01580351001200000c00911200d4111404a6441b41648000f650190080e0840b040c007265540010352722041070000b83e55042c80c045035100c401c80b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 472467158 1250 472465908 472465937
    0x1080a0c0c02190f050d030f0c170415020c030a020303180d06090c080601080625111015050105090d080a09080a0515070e09070503130c0b030412050a 66
    0x140026010030107840c0910048080b5008200e100c03010403814000e070112440306228211800c0010b0000703201c1940c42d40060b1900780c900600304e100e002d081208204400000780240102442d800c24106014403510340d80740d59030f0300820142a00c2940841c0540580b038032500f11490b0100701b0034152a001b402551038200410305100c03602074080070712035020701200c039000041100d40c03161000540c40b51150003079950a01800ca46000030580c0600840e500060410172600c0b00a200180d4410002c1d00305101040761110982ea00c1c5207484507941144909541803001d05070581007881c01c051500da0031030384d007616200115114032642420541180300c01f240d40000032041002826040450301c3c1c043c01c0d95480d0004281070462030340341603503c0d9028550808040e4000441e444d00900d003814144a481524000314124010081c01141400710101c001390607880d0441c0c5036a03505a1101c020321420782c0f200d2010081c3e400a071003d84081900e03400c000940340c0200100c1e180c0d110340740c4407440100c0010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 472468408 1250 472467158 472467161
    0xc0603020a2a2603010915080d09031104021917060a0609035604051b01030e01092a2103030f050a1a041e05040507030b040b040605010602060601080a 66
    0x80380381c0e59250059128140703203d200c0c03c0070310b0281c44240c0006c2082c0106800c14a46503030540c11000c4690400d0951801d0282c100540c841100d9002c07892130202080007000900a01500c200320100701004141c4250141c0e0200b03820010b140c80c50366064960b02c5400501c14030358801c4c02080c01040c242e410600201d0b00d8010103410490401c030400300e9041005a40d81c032000d2403003080002d1a8929003091100076807c0d41841c8006202c055a011705107000d03207035140d0b03903c10002143c9030030107250a5013040340d01c00d400005070100008000d100c0003034540b802444055940c101c80400984c0201c4400d480d011780240e10085581404c0704000030350340d600104090b460f0105044040c143e84101d030054456250041a1184410701000501e2901740e2904441010840c3c60080c455844d128480c80d6414851500c0d01040011020004003551580ba240d131404803035030406480790840700c0400013040110201e10b44201c0c441c2e2402d01640c2da8580081e07a0f0750b01c0c15903e60340810492030002e1031080c081d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 472469658 1250 472468408 472468433
    0x60e01020f12101a070312110a050d1508071d1005011d03060f07030e0c092a0c0109021206100509070507120201020301060e011b0204020f04030c0603020a2a 69
    0x140f103001104140e5441040200043c904082221010003080b564141074019070f000803c814500341c00e01c44000e40802c190558815403100400f4840007148171410b103d81a800309000741c40340744034520a940c60b092850b96400c00e51003490850351550520140ba00140341c0c00c076008100f01820300c103099091000644556403009011981c0e0010b0309111019583c0c2040441d00500c892440e01e141410f11180050503503034168a044e80c0c0d03a00c0001134640e582c4803024466880840c120b007039002d4294501182440c507400c0025050722038004183d4280c80c8c00e0651280074201e1088400302c150b9000c1c0da4603584c4441c012600786601c410112000c0115080c030042d0700e58001c58520b082841c00340566103400c00102e00191441c0141e5000c40103105a9420225414881000742400c00d0041032003491080c0e81040c00700c000340200c0e00401d002d110590000141c401540e0301441f0705814980341c54004000350402c1381d00c3d800041410031540e5040080300c0c00703e0001d0018031101305c8111a191611502401d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 472470908 1250 472469658 472469671
    0x60a0c0501091b0b03040312270c1e0f0b070201030b03030309062d01050411040503030a0e13020408030313110406080a0606090b011b060212070c060e01020f12 70
    0x1110000100000c00078440c280d5828490342015080c0358106000c1240300040b9048801c40c400200188400b2035007080d080d8418007210200414200001400f403640030400c040c000745144094405281085900c03540601594014420340c4000e0040201a000d0480c0178400c4045c3e0a401300780501200348680010030700d550044c10089159400c460209103990310403120308240d90000c10502c001c3c44103001c01045110510b107180c4941413071004013442c003030030f06100700e40c8101d0391501050440403010342503031300a00000b015a5255226201d01800e05032403a03000910498111200718000742c07281c400da40a40c0c112070000e5081d0707965032a1951601d80034180680d414568000000040e030b40d0350240c000988182c034080c0580020720301e424030503101190080c0c01078900340600c2c4411664015138040f80c0300d400c50f2255800742d00c02d01340300e0004c2c0306114a200204450030108079500b0740055905c071095104034802c009641f50794585074200e0044105200001000308040010503e00405203600042e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 472472158 1250 472470908 472470917
    0x11031306020d0237020c062a2401210221060702030711041a100908030315031b0604060c0c080109050a051501080a0210030209130608100b0906060a 65
    0x80d420052590307882249002240e0000791180070010741d144c1080c2c0c1004d400b0b00380018092011842e00103070060040b5203c5a0103800d034112a04008a04400e9800103501c11200351000e42001e212503141d48100e020383c581d002070490b4000207209a11326480d80e00450300203180c080c0c860aa508010050b020f18144000003e12042ca1b1211803c040c0046801201c1c10f8008642e607546914003498541f03c0c03220381070311562034414004c070040184006003000d8402150308110142005109440c806400d03000818940320100c204500300034100b0440c1444031045044958101e2070b03a81203120600c800303603001d03005041400300704003143c02482079030002846043c40c1a88240c0f504011401c50b146c00c50300759071940c04078050509000f003d11151024040d42c0c841b0814540c104401c01e0781d075070540400240190002444075412600c240e06a440e41440207204034000e000540d0a000076150718080c82c103503801030b000365403003038020792180c4040f551001c0c008840c1a940e0004000c50364201490010510 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 472473408 1250 472472158 472472167
    0x110406180f0317090307230f0a09051f03060c0e031b01080c0c03070807020108010b071a0c220e09010b010e04020f09150304060606030204030f02090405161811031306020d02 76
    0xd540034005040640ba04042540c00100e911f00544c641c948841e9180d401240500b1140e21580c03240d4045030181c486901022a560310386139107800d000f040c094151001e8807000d401c00300c1001aaa00820804911581e500d0031032030104041584074540340c00c0d040c4481007030500a41507540110030082c0e0040e4400400f0341041c24400340d543c1541d08c42c400444000c2000a4100115a0404101c501405540d014a414401d140e45e602c000c3c49112800d1003d8440301d07400040044290030100d640000420700004841c030b035541102c1c003c091081c05205500c20f0801c00007050316030f051250b549540416902e00d0801703940ca00a1000a500070f4141d641e4200080220721385a89806c0d0321043d4841424041c07a07900d24290130f0040488199410038020140100300810115058080d01e84540303804031080710441d25145032403480e103204034031071804000e50703408001002c03400d00d01ca920703542c034081000f400440100c0d15029403500c8116408ac2212002150607030200d101d603030141c4040c0d6014040145003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 472474658 1250 472473408 472473427
    0x120b09040f03120c111b01020d120f0903120c0e0f090606070602030907060f05041a0c0c130207060b0a031e0303020c060c0702010f0918090302070306110406180f0317 73
    0x9070b50801825502042c1c40244212905d4000c100080e60742918000c084214202080001c0d00c48200d0803d44042140944081c1c40305180c0c0e80c401845c0894840381041050910f00c2c018008005050710302055502c2c00c10000419409000c0c25103404400401080100300d40034200100240f01406864004000303200440c0058410304c011030055100c40c1c0203000300c91415400070140c221041b500420070000b404204000c00e0091844140a807082e4002612220321110851410088104c03442c1c1c070682c0c1e81d14079207048090742c0c01022040d02801c820b000103203040050002c42249407000400301001c6080c0c0c1ca49003075695104441452007071402502c0c0c11426080b091401c541612509188100010300034110b42c0c001111503901c1d02c160074004225848c0601d415804030181d082ea0358a2a16030182504051007484400c0c081d55100404208a034015840c0c6c0c207044c0c000e8010080495540c410390031100f084c07695260102d0342d5103a05080100d045568840d04050401c035944000c00f0140489001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 472475908 1250 472474658 472474661
    0xd1b0b010620030c070b0f090a0e01050a0b04150e0a09090b060a060305090705041d01020f09150c031911030a11120c1510030c0e07120b09040f0312 65
    0x1c01c03255654aa02c54541c0c040040480030320144802e0301d52080140b1444148046542c4048505c071400c41606e50b04540f00604052107003184203a4803191002c0040740784400c249515040c1c2d0b5054820300400354941c01c943c0214811800380864840741e14a1810a80b8461130f00b0800c40c03440504030b54692681c0d41e10b144181c03000e0160459074554001c04001a50801c00400e4005200b1403034140124106582c03402e403a00124000c0902694039038000001060307101c140c10081c01c0005000315520380e18841520451380102d441e240c8649100301200c9405a02c003000c0d6041d500941001d507150044103440710300b05034080603a00e42840580400d2144801e4240090840f0240380d03210442c08101c10034034181001a500c0700c44e03040c1d000c180848140840006045208603445200400107500c030007011080107642d80d03200801940c403211002c00d1000d041a4103e00805076034440e1a611840300359444140e8400c5080b403600300d201403001401044401d5054000240607040940d8802c4010b03e2100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 472477158 1250 472475908 472475911
    0x201050a060302090103120519260f0f0c0c100603061112010e090a020402040603020304380c120408120903180f0f0301020d061a09010c080c0f0703030c050607030501080d1b0b 77
    0x49c00f00c3d8006115007207051141c502400e900c6014502c402c400d2400300c10100d020403018105081000c1c00000040800101908076016200d10400302c1e06405141d00070500906040d0004941d1581002c50a80c0200c28000950700684900503035042c42d60f0078440e4545411500038080d9115108200240707000d03072164030003403015101642d405696441c01c1e0800f14800326090403d10082203d998000380e45812000c8480ca010400000c400c5907078458500c85001ba00070011030305442e40703890060008005070b01d0002d01c48500c86c060f98210694030b54540b240c40380030308800c501103050909a071786003030314290f501c81e80003203401407407401390070f43c00c0000c21f0880c0c00041f130b4900c80a80e244024000302c21041801400e1748005100c0c10315107080100004c10607050950000e180d80c2010904261954082c40209680c81d004401c07100c0b00c950381d0070002c0140c0c40c54002a40c240c041da00114151a200c0c3c080d03d8141c80030b43c3e0052030940e21000007103a1426545c11808290f544d54940400020f1300c142505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 472478408 1250 472477158 472477207
    0x3080115090b070b0402090f07080a0b0409060507090f0801052703070b011403010e1c0f0c050f0109060605040203131101090902040902040602280b06210d0201050a0603020901031205 80
    0x203000c0b85058030500ca5907c4016000f2460300500d801003001c500d42c080685a40809030140110380110701e00080b17000340004107802081c0d1420001000001c650001041080350b0300e4107581102e070341c1c1c0c0d00c45240c22250203640f1240030001c881c00054480500c00c0354a03060050b034204491400d440c0d03840300b4030920000c2e001003001e40306040c0440d500b842e0034010b0320b41c0b10354400090017600e034032044425404400355664030144000200454005402109940341c1c8541120a840d00414115500c41c004d001d001d80c00c8441074034001c40480c050030701d442580e00c10245a04040a151803d17120358419140b500d1440d41000f4041101160540e55400540000d000d03080015071a58101407000c7d06040c0340d100041018800301460082c165600c40841d00483d41041c207110741034a4038004518843c0c0350301c01006407549510f15a1550310700000e41d00d220351010b580208402d44800081109a4030070b407102960000c5008018004102c0841500200c660142000f500c4d089d00603004500d00380c60340048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 472479658 1250 472478408 472478423
    0x1d0a080115140105040807050d0f02100c120c020f012f0c0907030b01050d1e0e15150a0b0c0a0227070c0b070f0c08132103080115090b07 60
    0x1042280c2e512100000001824203095050508002c5400d541382c40c50b00c102c0f40314120380302d1040e090054800030349100076000f41c14a8030340c90325100d0251920101d04401c85280b01c480c1070034010a8441c814280c2c950354001d0030410003040300c40045a0040300d65010092070400c1038030303171285101c1c450141c120811000c0054070710181d11000300241d270307140140324070149414009886141c0e85d2110450380340802c08000000c04080c0c0d0242420128502d40348020344034a05103041e181d0000c000380c0584e48400d019804c00207603a4403107514030065020803140c0d4025001c4e00003405070305581c001400250a100d0f0841d000102c1035000a11034501010000c802c42c070440e4036640060f200c5000041c0c0c07044d254100040000ba80b0760300d11840c68001061b480c03c00044502004a80f40714001c0e1315006500304114a841c3d0070000040c5c0c1880a1034412281ca1943d4010084903035103903503444100d82c3d5015241c2c011036030300e03041c208004d0100c0325010303200301302013400c0218007000504080c200d03481c003480340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 472480908 1250 472479658 472479701
    0x302010617070608090111040314010b03070f080105180607110a0f060905060106110c01080a29042712111b01080705090306010506090d060504080c060f071d0a0801 72
    0x34084c0160602404003111a410141601e401171900310450b0210303030b0b01c03c2a00b0030600c04601d20a004020300d14826600d8040e030140043d10000c1b9500c1c0d0000d441607503008116070f440f081d07072800c40000d01c4012009142c01c07041c00101d5550080c0c20300300703a6200010640d109120b007a9244d40240f80328080489090f0365841c40d0303105012041040074050015130405118850b01168400d03610017000e1843c0f41000041d6000400700400d40c1c12410718848401000781c001054883c602e8005140d4000144c0101d00d0040503010080c0d9a409040c42082c00628402850300e5075103e1003c030541c040122800d00c20a0100000c89020401ca10301e03a46825a8041e0401c41c6000300051180c14081e161070100310040c4000d007400c3d41c01040e41070458204852641e078443c456070109104034000702e0040c0c62140b0b00402c12003030180c40801042d060641005071040703070380c45508100e07503e001503d40c00001540f546c0320300301441e40c0428a0303400308001400d04011907500c401803401d4404174960707400031010300308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 472482014 1106 472480908 472480919
    0x1f0f0f0c021908060405010c020d0302210717161407080a030f0b0303121006080408030a020309010209090a0b150a21021201060918090209060d030201061707 69
    0xd0561320f0300d1a05081083c020881e000f824000b5001f010071410b0418402c0c03089521100f6065505040307038048440c0403160090082030401405102d145400c8024044a8014070541e114810030049400e0020020305009042c209008800c00c240803510016031900c050301d21015461900082c0c044480003000c0180c0f0507006da1903014000040c022200d0f84e4212400341c8140c030591903000c070b4203503102d0040760012011a0003822188050010075071256075600111b410005490004d400c0403d0701c0f00258a41c2d506850700e101d466900d0302d01030300b6820400c0349001d6825a040a841c20000c500c00c002d001340340c0c20140e0721074020383e1480c001c0d2468220380c19241480041c403501e24856848000141c9801c9003401908618500740d042c02c0e080c4500c5000b201c0d411a0f01507c1284203450310012b105412010940440a42d503d6034400308a10300040c07840581c0d44544802091900e2400 = true := by decide +kernel

theorem cover : BRFrame.Cov 472302158 472482014 := by
  have h0 := BRFrame.cov_init 472302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 472302158 ≤ n) (h2 : n < 472482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
