-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1704
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:22:13.011785+00:00
-- url     : https://prove2.me/submissions/f2542474-eff6-4e0d-929e-193035155c08

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 306294964 ≤ n < 306474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 306296214 1250 306294964 306294997
    0x3080903121602040b1009260d030606030b0105212208030402030c01050a1e1b06020903060609040f080901050f03071d04020a0f030b0604090c080f0a11030c 69
    0x8107828401805080700c0c1260381c501c0b550302400b41c010b000545420780041ca00c28151075810200b107640014040060344c0c10808440008144401c008000c491040b041c0141803095050240003990b2503008102910701640d002d100d04071140e270054869004d8a4410b00b980d1900c40340080c40d244200050705c1d807243c48254040102101c03403c030b09043d00c02138103081c0c0d0003032400030401095080401282c4201142840c0062030306440800042400d40402c0309290203040a800d121070452142d20308040e16152181c03084503d184030700e8884004e510a0100500078011640050030f2441c03d01c003582d11540d0803032644141c3da2115a5204078542c800d201d0a81808010322881316410700a4000d0351244c256a00c07205c48240314203200401c11000107014910442c0108500c01c500e503400300f00742c0350710320060030007103010641880014181d000d10303081400340074070b0440031020450340504050300401a00008070140c0d00c2e01d080e500203031900010070b44105581000442c0140d89400001c0c0b440e005000d4166 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 306297464 1250 306296214 306296233
    0x190501021603110d0c020f0103050411030708010c0206010819030804080f0d050a0f0e0705010c05031c0209090c0405010e010e0f031b0102010e0a05060412020f1203072703080903 78
    0x5000c1d4403108082540001c0d1441c00302d5a40c0001000074035035000c0d0f02c0c00c1180910700c05c0c0d8006040c03218400b003043e04054032900402c04108468204010a09000741920f400325102c24101d4006c05915120500510441000144108010031101004081041000505807490b241500d0322040a8000c481c4d9500420007140174030000405400a10301080020031a418100822000d43d00441031030a800d40c034000d2a244104e40006450048a8080c2042207904009040c07443c00c500440340e4010072100d140030000000710690340104000c8000300c41c20076458690b04600d20450080b0300034240414890381d841c4140d9130040050f4034103600024080131981012102203810000c9400c814105502c0c40142c0c8401e96070203006040000014800a103160602030316803507922503003d0009031060601180c1454034610a01180600b1003920003210843c1d840000526102d0340304485040004501508a14481c0c441070560070080c50880781b541c2c2c2c1641117031200781c1c3c0c2d540000d90303107549032103070301102c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 306298714 1250 306297464 306297487
    0x70804080d050d0608061e070c0203120a090602070b030f0c07140109050106120b0112050a0c170c010903050d1404050406140901090b1c020609040615090e0919050102 73
    0x18035a1604082c1d5405855407541e03034000003600c949400105042d04141d080001840095001030010781c442544944240c852050a8070310104034400030390540a03404622250040741d038000c00305e0520950f42c207500340f0b6071108100e8441d5112700038648031a0080010170105200c50080c9a00507100d5040e0a250001c00d9940c400c0426940c02c8284460b511005100c040c80000e00c45c600080c4483c00c010329042e4043d40c0c0c3c03141801014011000c0b02e4110081d03010512404001081120f6400000c150340c0c07031307100c07401c0044194070140001028491034000c0e20a651140b80307044200ca074040c00030505640002c00548030a81080c0200d40862028440007600381c0d66070064034000e0001540c0c184900b002d1030248401400140c1140d840541000641500c90b00d45c10a12a9000c0040303540104146031440022203a01ca031b01d501550007420700c000402c0035050b407001801c07120450f8584485040d901d406481c0d10010441d16103a254210f40c040c4481c0c1c410031112400102c0c0302d100018908024400c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 306299964 1250 306298714 306298723
    0x201110a0314010905070e01030e07030c0e01030c09021314012309011209031b06060504020403060203010e0a1b2f0601031511031302190602030315090907030807080408 74
    0x140c04001035103585015034a01040480d050240803008014451440c2010b4060084007140c940c0504255a0b0b541202240000340003060195521035240c3e01c10580c3c8800c202d4464030f00780401d8617402131412000501611500c04c40e10480541c81c0d098030002d00d0709002e401e01d207241c003200d2b905100b44051444000f84a0099460380e1840d480340300c0c1d488212240c0010070711542a041c24032218940300d240300c00300350004401c004035844800c60310712500080c5080d90140c00d04d07907c079540041c004200481004107903009941a150042841d9a43d907a0340d03c2c0003001d032109108040029000c000901000d244900c40842005204c400840c440107801e641c2c4183c40311220070301d0065500494014420000c4040741c1c2105000680c0060008800d804040c12280c88003411814031000070016540031034484200c510302203468200709070480c40e92260041d4807a80212020b80c015004a07840702c5285c940168801d00a651060080820a00f5540d07944030f141e12080068540305414480062480700400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 306301214 1250 306299964 306299977
    0x130f050709080d08010b19050d0e0601060e040203150f030f06250206360a030f140a020c090601030e06101a090303070201180f0b18030d021507020111 66
    0x192419000780ca0040200c2c102040505002c0402590b80010046d40c01c6280507140790a1940c401c920030710120342801d65492007880b018040e5175040a0b031140c48018081235050480d00da0340c45030400e106401b4100012444100e0f00c0d000c00c2c01070710794422894141444041c0540c080941220303c07880c1c11030221440c1000403900401c071424407066042102c1440e20f220011445203000500c01800d18441c0003982c1903141c403600c5803001490b40c004601140c0e4a030302d010200986006d560b162425810000d000001c40c00d042008500400084948903036990304555841c40705034054442c201c010400c0000a42001d4500e504040d103a06031129203460520109000d1515041c1104406180c000b010042d82200c03c0d640300c2ccc2c80814480000141c4000c070489000d5542440e010608140d40c0340c6162071081241c1046000301c18100020980010110080001c0340c058411410041c40e03000070150390b04407081d000c500580100030002050420071628603002495030001044205641d28241e00310380090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 306302464 1250 306301214 306301217
    0x9060b040f05150d0506010e060d02040501030602090406080c1c0204140108031c0b091f09050a0f0e0a02030d0c06090614060f04050103021507081e070b0106080103020a05130f0507 79
    0x30b0041c00903c01c00103942203852541681c00d000f440703885072100b54803040c05200721401d540302e40c8009002540d90001c0142c10aa00800c1004113503100c4c03c00000940041c20040d0140e868100c002c16040c1d80080c2e4641e51000c000c2005c110300c3e40d8644143d40c1c481480d0800ca8001d52581c9401010100102c0300601a00000f0001c41d104c16044c1c0c1074045043c0c00e607404225003898042d641c3c039561503441c00a035010603c140161864201c1c0e40482c826461580d0241c00060310300340900140f007006070480b40b040d01c1010b00c14400b0340d2505055a80700c40e142c1e10002e40c03552140301003071320749c3d07000345a145601401803500007080d0420380ca6a405480b80101c2817452207009100b0000e051804811025150000b038600700f050350706550106001100b0703100101079503c0c012401804200d41841243c55080070300c01c0e801d0302440c02601402c1c0e503401074281110301110380400811242e1103640d0980c1200d40041901c155686031030140441e240740e21408040385a01c900b40c1c0403500342640120350150700319 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 306303714 1250 306302464 306302471
    0x20a0e01080c04080a0803220302010b0a0e0f0112051006120201110610030305130f03050a051e120f090904030e09070c020d02060a17010305151003120309060b040f 72
    0x12000510124000b441c4103a1103505200a00030344000140d052052580581c2850b5641c071900f50001c51b0784481c080000d040000303100c0c044101036043d084503911450941d650300c2402c2cbc9400101c0c150600c11283d204001d00601c00401a183e44d4400740e1850034098810f0300d4441094403130080035103d407078004158a4000103a0078086503400700400880d08011000341260b81448d0380d802401d44820312024042010108078000c5008124000d04000e040c2900c822642039501e182c10b544422105805a4003030240a00c0000302020960700c0c018807101180140c00b41101081a10686810004107190480d0047c011078046031201c50189004038021b4503030a40701d00342c0d80c081004a00b4000d200d20704001805582c003005172520b8801965955044a407140c89110b0642d080311034982e05040e00c1655110440000305006010510300002c1c584d07901d00781c00c1655840c51000310712000d84801040c1b508007561486409100303611154059116210100341041140005000c2d035200010021690b0358 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 306304964 1250 306303714 306303737
    0xb0406051f08011b14090f131806050f16140d020c0105150103020c0304060309021305071106010e011214070f0f05040605090c030103080d140c071e050d050d0609020a 73
    0x19080d1302c0c1c000740505031601d84103c030f49009400c6070500420380c070240a4081005444402d50f90900c44801034030301000d007004201003e0304410f85848091406a070030928003004902075025440040d40302d20030300081e64000101d4110f0031100c0c50341d100403415512400b840001d040d034080d80010030381d40c20148004035560800d80444580000380c01c440e0381c141841048003102840c0040107403800c59116040001c0d001c4058000700e880080482031b02504d0034a068204511030350020303008184040d40208030348103aa01c4403c2c00246020a006001343d601c00c00c0c440c1c40004078141d14454210040b5002c1c5c5240c559600360340b464075a85608043c0701d6802e00d21040c4000d050610500c00100b50071030b03518202c0d007450b4101003241c0c80706001c06030144078002a00c0400072007a801004039042140740c55465807400032800356036074000304030483e42c0c100e1030010103620144110001d40802c0d00600a0a41500240c10075640e0340c1c80011003e000075220100024150054406890003c680740c443c6010401d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 306306214 1250 306304964 306304991
    0xc13090f0f1109070f030e0106030209010602150a05040b0f0a15060f0210060e010302010f0c050a0b0f0106020607170a0617010207060e21030a02040b27030a0b0406051f0801 76
    0x15440c41d0ba54061003581e01004521a400300c1c62000343c0055080006041010804031405043d0641000e50859010b40000070000d9000070000380e100d42444103e0307040d8443e00c843d00151103046e903002d015088002c0c0032846940402c50019040200c452001030020300080b400d40c11011150301080c0400d01b80615000c0c210340501a068085541a4042010700c0c2803513003480c04071006010103410450b1075121081140d0140b00f2941103d0b4020701110006901440d00400c4a0300448192400503c031100009149000280140c050001910381044081000312090340860005042405440d1220070001c0c3c1050003003044000d500c410000981c0d5000c203030034074400b550003035401000c080d4840362840342e0040700c01039121040f091401c01e181d038985904882c040a4012604003108040000880020707100c240f2102d99841c40302024001d00710720b079020416803161482d08015002031a0040014000303032541c1d12942e840000036103401c2c19403807222059076004210b81c1011501c0c0e03544000004504 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 306307464 1250 306306214 306306233
    0x50a0b070f02190b18030f130f051c052e0e0a08040b0a140a020109123905240c040b0f0c010f2409020403050c13090f0f 53
    0x760414001402d80030303280d48020b25400000d4902070b11003107103200815401c03078200c0d20b00c06240c24034004072512180010b15440e0303ea4030074040290b13241c400d03000c001201c044c03c1941e681116002080c400c892030380814482212850058112240c0c0104111280305031200d551071320b241c042182541d914621241005011114450b000089560104048030000fa003810129000d4074841d007202616950591026644000c402525080381c02d4041a071200c0c040c0c1c154040c0145502500c5060b000030980c00c0c055a00409190003801038001900d070500000c400715030400d10000c08401d0001e44980b013a11281d05010444101143c16445036040e11009121008496003082107190440c0c585450310b0361a500300e10402c0710a402441c000310394011320359001e600c40b05541513a80700512104002c8070702d030055103550201010112084078000b0850580c18400d8406996102c030041105041030303001c110b154100f09540340011900e8051072400240c442c0d038080349661148031000701d10100c624103200403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 306308714 1250 306307464 306307487
    0x20a02090a0624020f011803080f0c0306041e05010b03041403030c030a0b0d050f0f0d0302090f011809020c0a0b150d1b0e010f050301052d13050a0b07 66
    0x109810070009100305a0f524003210403101c810081000385003040041a410f100c56440840703219403800c0480c0041490700310040e2044ca21a595034101da50321110b0090301c1d1981511804000365040c4005510360400fa48507024071b40070302021125500c9002d4a100035600241c100c01003030303c408800c2c0010002282400024811440055070440c42e00c044082c0082c00000c0210860075142d03400e01003075458000400d21110b070854151440c0c2a03070140417940e905212982c544461081400f90f040710341c801d200b03032800c1420044c000109003103408011502d02d4108d12466034440020180090707070340b44920007000c005008401034140c00c40581042000400028408141e0b035404080d0031800e03070b0303d201550820941c840008910082081c0c010f1507140303511782140300c51155400020a00f014490044000c68200b28024066030b5a86505200c0782820407001041042c100101c6028012800301c0e103d904c8039040c00c440100038041e071600d500e046031000f000e0f0744131900401404000c0e03901030369450a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 306309964 1250 306308714 306308731
    0x109080a0b0c090a0b03180d030e0309040c140a02010603020f04020301050f21031803010501080a0b070f031104090905010c090b070807110d05060114041406100e10020a0209 76
    0x260003800e61100e20040da0020a60b94914400081d034600c0fa0351201e2806000d0060f04500546078500311400320000c003403a030200190b6201e1040d80f0300c0d16501c031340600f0343c0341c01100d0081c5040618880a1002800b418013646080c01004601000150b01c0d01c40941301c1c4014560010075141c0c6140140310314141121016030213140100b00500c0f02c0d484076070200f098000241c072480030184030000d50004c65a409034040707c460000003603020204d441811b002880803c120001c2003141d913140e80e40c5555000015000341020141c00000b04401d000700343c81014080e95080c003141c8402c4084400c40c03241d010b500141c5150f995201220b0a00001340310305c1035519440e062105203d41002c07850f210f1344c060200010041e100c00212401005910050854948800b40c900c82c8551094034040340c44450900480700c080d5441314a12655140c070340960b40005c800151003143c191a15414840d2040c1005400020700030504042e002035100c41c004114000c0c400d03805420000028030402150080103041c0340f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 306311214 1250 306309964 306309973
    0x406060b1204030507020f0a090f0e1c0f031107084303051b01020403020102150609010306090219090605030d02010e0607030c090306050702031903140402010e040623010908 76
    0x5180c0051035101d10703046509070400301d80741c515030b01c00249146604403001e904224546400115050315402101c6212500042070000d6a42c080c29180d98040c0c0d100045000d000d843c144081d0980100d81c042e903c10800e00e008505840c4031650200140d024400484122500047d02000403042c2129984002c610b890100c184142c06400c0c1031741158500f2840d480e4101d0310380807800f0103000b10200c13550901c5800000a100000c00c84060003900544400d90250007a08044c404051b003070400c00340704003001081c617500359095072140e100074401032100300d81002c001058400080c1d0580108070040c0b64904000c02d0700c9052030181800d000ca00325880c410744e1704150716800190030201744180e1020041c03500280e4840b00b1401264983c0c01c3c2e034000751002d0324280c148998281d0200041c5580c80c043e056008100303200041c11003c0b50310148406404070b520300085001503201d84103000f400c1c40c000b04042445502c0b00043c84185003d042245c0c0440d40011400500d941c10040884c010a041300181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 306312464 1250 306311214 306311227
    0x31704050606100203120108030a02070503030406080a0903050702031510050102030a0801140102010b060d02070c0e040206070605040501271b03050303010e04051c0e0901050406150e0a0510080406060b 88
    0x60381d0707982002d03240ca88160350001a6000540c420425100c03540200140b0113041d59486401c140c0701d5010b48074620040c010440042540e04000088504507031080d0354480265440c18081002081e8049040701000010003007100582d404020a2044410744183c644181c10864880c11040340542d00050564005021060540350840b0016045a240744007002c135410f032660041b8014503207000d84644c03288010803152a008415030191242c00c0c4120308408016440d412105012001150020750120080200400250485d00516005441a00041010b40c0d030b1007104034020610a03100300c3c03801010409441401620103101003440401940c840f4440d05503200c1a4680c401401410442d54003a000300c0d0800904005055900d1801c04c0e8032050b4146501004008000c5911350501c03491b400e0f8004100361816102d00e40c100c13800c05810100036807440109071000309042c501640c0c004a1008001680e8440e04143e0f0030030784080e540e20000e841e040c030b03051007241e00c1130700400580d10b01030104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 306313714 1250 306312464 306312473
    0x3120e03210904090f12020d0905010207121b03290a050405030301120f02040c050306040c1d0103090c09060b030906090d08010b03130611270d021c0b070c031704 71
    0x2141c050b000203076804910f143e01410115002d0034940d200030a03400d000c0349074221050b40030070510035883c0306036608a00b0941d41c07030049aa803052409449200c2c10410b540380001203504c00752040c954040204030f9150b56480e12541d180701001d042c081500d038141481000c41c11007000000da031080d80c40c04200030a09080c1c56407079907130105000314501d01c1c2c41071004605202056005140403503000b00301740402000184010003541080d92041d00990400316150354103400390515403080441316100c06004088580114050301d0308003410b80b0b88450003080410000780500412b006461450405541e070304019110520340030000703114012035042400006400c643c0003180c039046982c0040c006031203464000404a854601c03030401061945410b05281c88100213401400614542890040d65000b104404480116484a0f1035a10003441181c5400501d000b034092080c00061035551a0304101c0c0b5a10030a46580980300b403030101d410320185004041e8010a0031003104119090440142441d980303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 306314964 1250 306313714 306313717
    0x102070530120a121b0f120f060e010503070b0301080a030c14060f0412180509071715040506060a0509090c13030f02120706050d0e0703120e0321 64
    0x624160340d40d44149240e11400e0810058001c0b106039075440b40d94900901c070292124090031107a420060500661440d0164901d40b004811001501c4e6400b0660700e039582100d070188000410009990b80e00302460190905101c0c2c4030140100340d214130b507194100400c051034045542e001c0c0503201c204100500000201040000101d540760030203a090604500c4d000c607403868650101041340c03158604004030003171400c522030701450041c0100e510104404500711001800c0340c0d038802420202150400c003504000c540d030703a84007a5610340088201c240764082d2400c100e05a903444a601e503850400d680c3ea1400d0f01c141a001071045a880d45492081c10b00540303070340101000280300e54408400101000c9910b012200360361a10820303988c45641f68508106191045042603005204800102d0b200da003000903904151040b41c0c17650340c20b09060341301c8803026003031320000402140524540040058480c61420250340342e1603d1b582d0182002c01d090610303020f0841e407543e020780889005450028a00300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 306316214 1250 306314964 306315019
    0xb060a0f12140d050d09060b1e0a0803131205100c020d02060106050a0e040b04060b1611030714060c0a0503040e150a03260405060307030903090e0609070f0e1e01020705 74
    0x40c04604824203040ca94000c0408e1011140c20441000040e40303c502c91501203c4004800c80365400403540b03130741c070259882c050701522100c55166001c0c24885101d003c2240c00200b40310300b080311407a0711081c0b01c2c031082c0c40c40c503100000580c0c003d2004070201c58040c080c59000d099a80740c090b09110340c906005081000241000d80a16070f5040e14801c107803140d420200181200104c030540c0c55540d007440148555440c041a5040b03541c105040b00c80b442c010400c081141c048118640041a42508004041d400603400307040d90300c04d602441c40042c000b8406080200340c000b0b40076880d80361001440000c02490b1100c0c510888a52a0074400280301c074a40340000b07100703040c942000d07403011100c1d2003081c41140c000581c04240070042140c0f0310380c183c0201007024440e030344070017071070b80d81e4031010300f0926040c1c8006900940746c00006400510841c40c0310100a86458400280c20055010030072403c50070f91440205082c0c90400032841d43c0410640c801080181c4000e03901c1442c12141440004120 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 306317464 1250 306316214 306316237
    0x10030b09010b03040b1618060206160801050a21060c0e0906030a0b0c0903010204030803040c14030f0a03050901030605090910201c020903031b1005040305070b060a0f12140d05 77
    0x75407084c0d8298070131099111f91130800d1200054582d00c441c006036a03031000301c545824440031a1980c2c0c988034816507441e4100c480183c202100d29042c0701d120f42c09a5014092950072405124820340441d920b402200d4a0369015201c07001c4541285060001004d402860f0134001e6028030f2070b003000955001d01072940a80c0450207241c503400d56600190280c4180c0c1d102400181e000f0007400148000d00c1c0c03d00c4101c62143d8148010300f0f0260061680b10b0b1031140c124019608404404004a80600c00418000605250000301c42d5141d1001a042d09400d8400c01e0440e4040404092880c4c5940724510610003203190491902050f00c5610075070748502d43d4100c5554050b00c52041d803505a640650300301203401026603440350860208101d608a80b011009214425960038100798040da100c0c450090760941d490f24600403241d1180c0081c582c0107082c5541254003040c00044010030084020f015180030b40012000d003c05003001e60210201d0145801d2941150208920083e0004100c0c1d05d801c059 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 306318714 1250 306317464 306317491
    0x6130203032205030d11011a0303190c02121f0b15130323010c050307090e1005040c050711031c0c15091a09010504020603060d050c10030b09010b03040b 67
    0x151480c1c880b100482d480107400d481000245055650065810040072003e2002042801420b40d4040341c45003d020741a5016001005003440640c0e44584400c01540741c0d05103444031366201d9010840c8180c182d42c5c109190341112410054448544844a440440c00c1c04207100c100680c0001860641d6560215842103000107459030684115500c001c004580200008805403142d0040703903043c000c0040b440c00d2039481c20441240e400e0003402686e01615403640d0b0050f1080c00c0486102c401907001d00039115410f0007110000346c80d07485004810741715030940d44a41e25092070b031506410300784a9110307942c400d802142110f11507108051462200086d13500e8a4500304170715042c038001a0214001118100341045540000e102c05400e03860a05400c81c01200400d50320700d0b20007400c0340e40c00d4030003d610a4080010030814a03102500a09090048003681c00002d040e00004121502d00040303140480d0f1140003886040c0381c101c40075401414062000c80c034518042d954201c90b84001420a490070340c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 306319964 1250 306318714 306318757
    0xa170603030a051602060a020105090715081504020c07030302030a030b09090312100f0b03010f060201020c0d051803030301091d060432030a030f0b0406031113140c0702030613020303 80
    0x20210001003101790064034460341c0349041a4024040c0000701c50040b80c500c10b125002803d082c0502e4800c11190719562000704070b0b1103101d0902c60500c405018581d00c550280100303546481e0501c4040000c42c0300b07070001d55030b8282c0c1900c040c00b9612030700c91452103402c194080240c415008000c403030051060300c0c040049513442502d06c44090010f03401c240e00401d150400410010046001181a01c42c418002500c02e5600d0404909030700c21001e400816400c92481c0204550003000500040300e652000c2502c4020003102191840d0400d03403005034800c0d00d443c56080d502c1b9800900c4000070540c10042c203003c1c40d0a40301d880c800d01741c041302c421030b10380f1400746000070703802086420003030448010170b5990300d015892004014103a03481c008615107181084421715441c081c483c00d81181d034094040c0b1414070049d010010b081e40940f030790310b065503208c00c08022910401d240d0584130f40300818a054a41c0b8060040c10304d0f00200500c0210b0b0343d102000b0380405a680042502e0511307050340c00c01300754000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 306321214 1250 306319964 306319987
    0x4050405070525050c040504120804020619020303041e080418060306060303030218040e070306020309190317070903080708031003050d11060c0f0415050f040b0a170603030a05 77
    0x80b0340310310000c18507010f1144588983d20102c0d03986000c0c3c0603008580d6000d85a108120403a44140c9006081401104a00f80928080c0c02d00d554080c1c0010446420040f078502c1c03200d082c0c1d040f46000d0300140c0000041108102c0e044990802c42c10b0b80a240c1c0c1e51080c800d83e101d4080b446a40100c1030140443d182201d04044c0580240d80655803289040c014190b4070303d000350107500b040c2d03981e0803c0b40605164640504140c842c100704611104000c0806c00e20f10b0301c421000b03500140050f0a64055400201060b00860b00031002d014420f07a121140c0001c1e4503402c0c544085c0c0079040f6010807101450810100c0c0f000d0007644c9240790003018465480e29505040c42094105500040860185200080303451741c22855082c0c04541300d9065403045c0d99508100301d81441411280c068201040c4824480410104010202d2400508044d4035100e6003580c0074403260080d62107240c4417680021084015644050300040e102c02d1113180c4891403c005d8000b03a201e000d0450200100103003c6203240c40b01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 306322464 1250 306321214 306321217
    0xe071107031e0201110109020a0603090c08010e0f0715090b16020a0f05030705040b0303030408031b070602070309050102010c02070603051906080a0b0702030309072c15010206100506040504050705 86
    0x6561140e000d010540d803410b2040b1403400d12880c00e0f80840d815155068072484180600205030b68000c00d1040c03150b05000d01074009000c03082d42070354210541d1502240c804824441c035040d54903110300034400325401002007850000c29800c10402c2060001c1108032860f00a00902d0584405a00f42d517115000c0000030646044040d43c060340c421525800019000c8000f41c06406842c030035815220071903120010b100980b040560309a8165204100040104d01100051900844c90b444030300c22606000c01a0342d01900700c0402035406030f070b0014400d410150000b1600c07000344801e0000b481301c0001c204000c2d4440100341b1400040c03646a20015030701d5154000c0d0ba03004180810002c000c0305840354022665940315000442e000086280418946400002520b2003034100718000d10f085c6050a1210400b5a49402d41c0c0700b4402da5a110465100c804c20141845010020804884690110002032070b00d130010b00380902c001418101409207860b640102c0d000d40e901039a01089644602030101e07401d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 306323714 1250 306322464 306322469
    0x180c05060a050c031801030c0903030207050904022202030a0b09090604060c09150c020a06050306060d0c1202030f040501050132270412050f0414130c021e0105010e071107 75
    0x200d00000528142c0d9120305d0f060044c40314400e0340c0c1081440c000c4501694101c00034003029025034801c0004000c1ca2600d6500c495001c2d1018025140800005890100103074402490540c1640c001c020020071100501c62600d00c0282181c00800c1030816190030782c0c85000c040c0c4086c1400d5150a919800b09010300d500070000c0c042041240b04880c1d203000001d01d22090711340104d12403003039108006002481b61003a02d016034001455180341450000307803000100307081c04188041c42201c00030b0184045281c80a107108040c4403e8200040c5400d00e001f90850754144c00c40340c49180801c050107241c14131140a0840304040001945400d0210f6001416100c00080340e800802c8a0f07030001403001040980440c00b541c450074100d08409000402a945805191010320000300c0c00c0c001042455610041501801805840d0315041040e11103590705076010741d00d4100151380415403003152140100300300801c048805008100d903504011300011800350241501c0f042011800303c500d894141400300500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 306324964 1250 306323714 306323737
    0x7080604240b04090f020f0306120c061605010b010207180c0215010f0303140301061418040504120912050a030807180f060905030d0c08031008010e060a180c05060a05 73
    0x1000d82c1e01c07881c1c0c1c0501c2e4044d025500006040c6511107010a5a50090340c2c1044c441c40340c540d0860395041d040c85038041010040c82400d105c0c81002d407115407246030013802145d00100700f0451001d418200316003501d9030114028110b5200d280304000901c650301043e00c10242c02b0710042504048400101e18000151794485074001c0c0b5400000b500005010600301103901c87c0d03d40e20010300350740f00c40c0001d6000910a01001c9030340c6281d8206213500a40c005e154004080185010a114001c08170742200c0f01250201e03130141410039040f000b15005984000200201c80400100800329030711103031075040307485005084c840044040fa80e03140c000e044850802005c0e00240c80d9159403110141c4080e11070f4442c20012541c1030501051908000c104241c100d841b0b46c40d00345a00016540300503a560005128005005140501103080c401c00c0c01115400f5170584000d0007c0c0c204000710340116890030541d41c0c0c0c44003540150706c3c0005c2484007510115030084070441e442e284660402c1d2418440ca054200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 306326214 1250 306324964 306325031
    0xc010e130b121506010206040305040513141005010207050f0a1809050f01020901030c051215040e07081c080609070c031404030b041202031c02180402032d07080604 72
    0xc1844400a0b1011a0800c000c40f0850962130b0600166180c0f502581c018000500c100401e02c91400d00322010f030540e91400000041c0c1e0881c9180007070702103106850344103001455082c00c00407580c0c100908000b0b000215042c04c044034102c000503c40316000c1c07240d4001e40e010010300804196040e400035020303a4104040c1c41503400c2800300350f8002e5202c1000b0502091900001c10a1b05101d0000d4800400351009200c106440e04015445c12090304013030154000e894901500010380c06102500003414404010f0000704601556641d800c8094604602001050070400400c1d540300340c40b50360007a540307041040c102144ca0504440c0c410b85002044142c4400040000c1040070f040c3c0da01d4400c900880b44402e20f0000c100041380c032849220110520780281c402130340b400300e525500400900c2e90110032108003d4298000c101070360012a800207180d100c80800f09850752000805c010040300040b0075640c580f40a0201604030303d0040c3c0180e000b6555103160700b4450705004c0088800340480c00e00380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 306327464 1250 306326214 306326239
    0xb0d02150f0f0319060509060d061b03060801050a18080c0c0418051009080316050d0e010b01090b130e1e040804170601030f0b071403100f05030c010e130b 68
    0x90300d641c816141e05042c2031401300300042400241c0b003154141d4070020160901c82e01c9100c100450032031040700940d0490703540c0340540021582400d200c4825002900c0100710240703800040d5086540042000355010308000288034210800c4004a424030781c042d4401343c44144d920307041e0b89171121500b4801d07000b901c0d010502c5d04c9400310003a02c0034494440d904540120f40c6e292000d40c25241900401007e0b9003007440495400015130480d034080b00c8503132074401d08040c040c8100d002a0307030f0101c07021000d5941d0350300410503650b03221001c24041e1481c1480d10707240c10582c01c0b180400c100c1902c6904542406280816100508a003528205980e0f4101da007600d4202030034018003651042c41894440050100d14485020012910f24100c0ba0000c15002400040c2d441d052442e07800140600f003001700c4420003009140e40700b40a58080e42c0c2810000c1c0c09982030600c2c040e074030113840c3c100714800c0d0720942401056a90100001c29030850607507414510b00f46203031138003000e461040c0780d1039032009022004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 306328714 1250 306327464 306327487
    0x718030606030c06020d0c1403160605150d0305030c03180109030207091805150c0705161d090631050309150909070305060d0c06020a0b0a0b0d02150f 66
    0x1070015280070300c1005200954800e0281c2c0d40e40652840304010500c400801d2001c40c1c02500b40e046038030140800d807813400110410342e01c6145030f1010201c50107540c0d1070070301c800c0d82002d0300540225902a280b12480204684015202d4000200444d07914800000092940da030f1641088034036400e404001d1041100c1c43c50041e44a81160290340160742c98403041ca0f00307000c10040000c0c2403d400001400494510304550090550000c191402c01c010801c080720003c0c5040107040c01d041e281c007120064a81c14030f0545d283c80c000104c0080611310210090048501e0085145a08080080301030110000a01c041c00415618402038854040600700c0d070009002000c401052601c0045402c803601120468004002d8010310240c1398015000c0300000b004640244d0080703030442c0340241031450304409030384e46448000741a004000103810061100d030810442205090308415400005d1007984002e9001c41e1b0711030101c0a000e03124850b8104520fa001e10307000c007224001c1404041540c6c3da2540b8100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 306329964 1250 306328714 306328721
    0x40b0f06010201142503110711190803040305010506061c0504111e01080c0c0304120303180c05090709230d1202011b020616050c010b100f09230907180306 68
    0x100441780c1000d144030b050b82e5501c644210340c085c14118496508020168444100078001c0e50107046c0c20a0703000160551030f480d01480d4034000c2c110000103651f00ca013545011401e4810140445000744002d0000325460b98244000346110982c10800044554031818001a07206d040da2030a070304444003820441d159500c1410203202440f003a251001d564944039a02c1d00e00e4403814810b401103400501c0148a0303500c2003451440300a01134900030030304c9140100558410115864103c074001c034120410002420b00748031041d801080b0b82810305100e40380102011101e00404442899a88448034114480c0c0d5801c44252500d038000c81c0c480d0912114841c003900801aa940085440c3c03080310051840900c001071007449030034130300000e903040c08030300358240c0d040d0700301007508103c84d52030710b03610103840c1c60b00a000c84240b1010740c0e5601d02402d0992011b02070100c540c200e08400404c21129000d2030340c034417aa00d8a4444255400040c0d907695031130848400304c4901c04103650022015000007449030030382 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 306331214 1250 306329964 306330001
    0xf120c0301050a120203121605011e0b120604030509060c010207060507090803070c14121506090a0204060c08070303060e04050a0309060504051011160303180806040b0f0601020114 79
    0x243c20000890301d40030152000025900b00940c19401000840f000400391000380503401c0d071081594610001e00d40d41c460954030307100340c01020002800c03d42174500c0d549000d0404c0307085007501c004c074402c5a00101c050b1603040090018090004c0015088106d4032000112420010108000c544550f500d00d0700501416007550b80c1c000086000b2008a2400408000c80e03641503442800082020710f000d80d440071445c0c0d104c01459002a0a40c0e42040c41d403402d0106c1c2c001d003d4105d485811300e150000070080200000ba2250341018030600061204941040c0614202c13a002140d0907101c040d685030842c06028260442055800c0d07680c10301003040800580c030411244681c0302c1e81d020300d8965008071b525014521034240d1003924006880c0c0128010150100711f00042c1040c2e0b0101042e040392920555800c1d84104d001991040d2440607080008260402411020000e0001401c0a0b210007900400240c000803015051102190050707000350701c81d0ba009191201c201101c0e281483c07a0044201215 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 306332464 1250 306331214 306331219
    0x71e090c0509031005101d09010507051c0f09050d0903110414060d02030a05030f0a0e04060b03040b1003050a03050702130504080313050304051908070803120109020f120c030105 78
    0x304504590088040c1e88490001400503d207030b0407031403405000b520025002200740e100850000c103407450040c00926552032890075410789030501c4800c0e10700312540109614100007061000d5040c080303140340d420b038189120140108014208845801c000c102c2c0b2200180a48100089040f14070b4000e140c040413a170183c9600d01000840300207002c01c0c0c0c0d02d5040c03405441d40c2c1000005005e03103429028020210b0000d4115a018001662040e103590301c84901000d03030a10104051010395404900c0c005001d0040d0740900c802031170482c0314400f80c00040d10043c170140b0070b00001070100303d04141650007540c100c8100c4240081c103040c040e001e61f10048013070340a0002d01c0b08003584040540111401581d22400b050714650b15110014603a4001c042d04a4590008000000726942c50568644814003070380d0303003454094607115000b407605c0d0345a0b1109840b600140007400c250444100200c0c1118801c0e400541d4031215150f010400744501c0b030410080a20782c8041c400710004890103136050f44e000f03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 306333714 1250 306332464 306332471
    0x306011710090c06140304020609120307020904050615010c1101031d060106030c09092904290109080708060610050f0328020f030408070507120b0a0b15091002071e09 73
    0x407060702400306e21041717a01942142c820800c86495080c008105460030700010b043d80c0c1400d190381d000406120f400c1c1c8041d41e155002100780000c0b480c8013004041d00041c00d091a503903248040e950b0b074a4107000c0c00c894605142d501d080301c40f00d10641c0250301c509011902c0a440013582c40d000d0203801480c12480c81e00000fa0404804200c02840e88945180b002407060080444400c09034102d482980300d0074000e401540b40c052690200c1e10640c0307003038180c407422500040c0650041c4001803280301d283c0d2103206c03613520500042101410102d816a0400c00903034400440e0b8020a00c251464404c06030150254440041000306400e1440c4644524619044410b500004130000600c04e80c0154404002c81d02c00c200b000c240050340310002490420700c580c2c261120700b95282c0e1004420b604809090300c451400c00c0c10002c40c003c5a1003001c4080004a50b424402c10040d90110503601030440da55001e69403441213061501d0080184c1002000c0e2130030031071080c0c8103a900421901c0b00d5840340800303040c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 306334964 1250 306333714 306333737
    0xf0105010512030711041d030705241f030b070302070501060e07020d0302031801020c060a0e0d1403090717011a0d02010e1003021e0304050d020c0306011710090c06 72
    0x802d42041400d00c041c000041d820214142c64004084170301401d040e901c1a59210515280540320100309140042507001d1900c0d02d03e1410168100a65141a0102610b602c0c402c1540d8107000f2041036000740c040380c402d00ba40c0c510b0194000c0003403c50740020b8506400b01c0100a00715525800401e00c191044000740b0059540b412203008001050303a6100150300410b04900b40d40d07100741c0c06940c2c0304000300041d8501c2010100d00d9803c9a110101d104099007005082000003c02d42c019040a8a144001807140301c3c81da040007044c00c80d001c20a0211500c001010411310041000f104d4044c1801c05100e0024481d40c0101c10b008020710f100d100700d8001c2114017500306240120309404100e4044e15821880740b000020044000d00502c10042403507400e1104c0082011050080303400000b181c4980c55603828607044c101d18040a008920301158852000104130b6100803428504590024040f184003c0d0405410b80c100000e00035600081c0d81707490340240600c62159450f1003200c13015216040d4118 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 306336214 1250 306334964 306334969
    0x30c24060305150c04090209010903080409020403020a0b0f0a03050a24080d0801050306060f03160f030c050d1106130512030d05010608010807030318050418060f02130905040206040b0301080f01050105 88
    0x1d0110b0382a60300207410701041001a40d1b64004051180d0f05140035a03603142c507591600c94982141e001032510744e502050603c03c50400300802c401406030801d03003c3c140301049186200138071480390b07c00c04140d01c0702c020030541d200503000b40344100b03c40f6038420b2940c1d42d2851141500000c5103e0070355039125a050104045002d505c0c490306989015000d46000c1d41e030728050040500c0c12030096a094490b030b580c9404200103004600000d0700441d00c061200510394100802c04181c2c0c2c3d002070b40b24030426120400000e0922600650220059650796221030807a001c840794400c084e844641c010140584114003000040000c0a44403135400b4100020b90b01ca41e41200c00380d409004841007540a05410701c0428001d903054000342c4003040310003074101d880700e02090944041c00c16200c040d4030500303000001c1003ca80154402e1200e103000840c10075580d0000c0d0b0aa1401c0d501c100381003156248003203015900c40d10200da010f0401c29000550781d507034800740c140d0742c0d074640b40350070185518006c004036251 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 306337464 1250 306336214 306336253
    0x1b040c0509030c1005040e15010e0405010e06091503011e1401050d03030e1e01020c010c05160b0606070203151008060105060703030f060f06020c010e06090d030c24060305 75
    0x1c10098020b08440045506100131110354910040602009000020b80c1004603a100c91080109100348034509801c0d80c0094014600e40c1c01c42403286003424018440c0d00c554030345040e8003590895032034040b070b182c1076402400ca5464076003142e050b509184604c0302c90b4806015650000d01000030170030204c8a50036600b00c1c644800e000b41540441d10490f40d0f00403e101e030b08504030030342d000010303502c4844401101058a03803071890a41c0d000d035004540408180e40c20b1017410490003007030a0152070012803002c00342e0070a002e0503005215091010104c2c0342601d428054444003a07000d0300b101c541e9980d000e200e0126400c2210002103c0e00c00d014045441400882c03168103d9601078001802e02d4607079507041c0d000d441c1c50034424011a03500e401c00100340360580c02c0b807401080580c0140001d042d901c40010220f81c05040024005c880c10824250142c46258641c2a22a0549050703448845545001100d0380940c0c00f04011703600708419407070106003059000c84201c0e03201d803086502c2e030f038004044415030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 306338714 1250 306337464 306337477
    0xa0f0908061509060f0906190e01170609010b011e1107030c030b07020d020c060a03090b24010c080f0708040b03010b0310060215150d02030106140a05010207030503042102031b040c05 80
    0x401c903071401099031f80c03d0000303005590340004007446407081c0c3c0300c80c44540b1100c0260306c0b040d00c640b9500760141d04c2c0d68080c0100b030341019084e0028040280b501c40003a0000d20501e54441c0c0b041186000e10300004d03c40c440030340c840d4940009803241942d403404c0c4400d0309500d60005681c240364101c0858140c0b40006210b000050302d94001e00842200c1c0f20400405421154590040c161120015030004006020780d40c800d901581007800300c2c070b2030290010301c4298070001e258140322840010002040c4080140d40e42110380d03800c041d54445d56440c000119024652011a036544044008201441c1c8040614440d6117a601c0c82e4424070798951080380d88400c556642032501400388003156462071808503210b01c181026124070b051025590200b401c490380ea900041074400d9064050840f86044820035000f0602480240469070544c2c582507228801c2d88262449684c41342d56001c0e084001c6201c588003650018203860540741e1840c85108107400c95120345108070719114881c40d0140c01401035519 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 306339964 1250 306338714 306338719
    0xa0f0509031513050102160c0e0f150a030f03020a030807030b0f120724081b07060905010204170601050a0f050a0b030901090206040909052e1107020402070c0806090a03050a0f0908061509060f 84
    0x120bd441c1c00c0e5085418a40c134010a039009040c415002c400b044868005104c1345100e503000380b144006906004040e44406080041014103140040b1090303940d1030703103e401035207040360740f101d1030700f6071a010900c1d181c0b40e45d200000252a244880c902c2c440b4a501c0001004081d4854103d240d469050380300103140f03031079031081c14680c0522101020608640c03040700c54502ca00d00040c03815484000d11051408520304c0c08006502c0100107001c0c5007400d500300c4000700080c1e80d408001318100b4001031401215405426041200440056051102500952807068010f02450381e1642c55244000261003100000e0b90030344a90b144054601c0880d032445140d19028040c40441844c0420fa6103014100203801c00c07240080901c40c003409a40c5610090070100d1051503008280d0b454900b2581c2480340c000e202141d150007024041e004a500030b02101e24018551908030240c0140c20000d55486400d0380091240f80303c0c05003040302014903810000d211b46012900011580d544004001d0810740c4000981e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 306341214 1250 306339964 306339991
    0x1809070507171606090609021e13050601020c010c030c021c12020724050d0f020306090f04050705100c050f210408030d0504080c0a05030a0f0509031513050102160c0e 73
    0x100491101d0740178402080c480c0e10701180304c005c0b5800044641c800000000003049401d0220940351600741c000440d654105c00c0284428030301400080d45503480c00c00c0050610031410090002c2502c0f4000c0c0c918050350080c85001d05546030006600542030b42d000c100d0706504d110b1034030f0b4000e0f40000783e88422103086592010446041c500030f0407040d8200c1c06800c0070300c0402c0c88120319080007030040d1800c0308510280140c03285004020840301d0342010749a2071a83c4501c2051101241e00460308405662081e0741212101341c2c03000085900f07452110300a46603000d007281442c816000410706c05045200b10040c81c60134160010301490b180301381c2c4100b1219034000c000e41500752249800407540705004112081c14141710809041c1011100c21044443d50000280e403211240c01041c100c0e850956454118140902c0c0000309a945146444011607500e4010001d04181c10903064040c4040d0301c00020754892015a2542d034042c0d1030410129196002402e005c2003241c1c44000d2603211303414140050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 306342464 1250 306341214 306341257
    0x6090d05070b0d0e0105040c030201030c0905040f020909070914060306300105071b062d150603050903030703050603100905010b03060c030709140f0406080322050105040506180907050717 82
    0x10760040c60123703180c5042c44441d00f8000340c542e0356881094091001540301603502c0368440c0070020041001401070317040c0280c034070040c0407400c110f0900301d140e0407060782c0e403556039111000047c0c0c07000b486200700407110710122092901c90100d4071400c1c2d642580b5000130300c115100d140e82030b5645c190045030804040c200c00180b202184890b0400300c401040149a1000744103c103401e1403501071504c403078000058a865180d03000010b000000c100078010b0345010001800d1450299480784000f4009004240c2c4540100c1d006039000d010016041d450000c0c100040c02291034414080c0800c2d404081c440c0c024500018985901203045920410080d51151400741c00c1035540c50006642110392500905c0f455804449500c82d4454a0701800c040c1c3c000f03503110600101849802100c0840e207014184c0c104400f0003481c0d8000040e102030302e0046178074580390f007100031190080e84103e05d2920b6000420100b409001c0f60800028a17a0030f0047e00e0110103c04001b90b0314906105400c00305101c20012507a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 306343714 1250 306342464 306342467
    0x708070506062205180609030403110102060709090b0a0f0f0801060b070c12050f030a110d03060b19050d0609020304031404080606060f120c0a020708010b060906090d05070b0d0e0105040c030201 85
    0x881d5010705c81202c1e207960483d102d1a01c038980f541c02c0f01c44158540c4005010b00501114804080041100348000c0412345040c4c00d004100d500280720b6044100d840d5010003513650340343c100398405410040c0c03070740c44181c0c4c0e10f24540855142c03c2c45030070401d510b0920040749400198084034805900f08000000240c6003c0d810030302c1c000d10010070303505800741c40150405002e040c402400345a040303a031400301d21918511418200040c1b0600c29007031501e040402c114608010781924008240001d0004954942d40405e0f903003032140345002c1132098031b0700c2800714078440240d01840c09640655500243d07910040400358182c8158003a0307030410f41c05480096854900313800144004035076803003010304141033070509101d154815500e0641c41c48001c01d002c0a040ea0422000f8001c4c20200000d000400420000c2140c5201d0024010700034200010001c0070742e11600680c06200c0d41c403000319455107030341e0f21075129160840d01a00703a200e8200280920307650b030b05002e40c030300450f00002d0b10706403149903030700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 306344964 1250 306343714 306343721
    0x91c0f08070c12110406080a03080f06060c0f060103060b12030d0522030207030b0604110f0c070f031b12030816030b10080109140705030103060f09020607080705060622 74
    0x81240d00c510482c0740030524000031240c05065511034407401404120300020041079400d0364002c007080350f01c440320300004070394040510345d008404c1741d8103a000f03521602c0c0400c00c14441c032030380e02000d8450340a0103440700800040980c12607003d01010091002c0290030080703a07100c03801710342c01c03164024440c880e1002001d5012a0704030b0440311402c3c19198a43c0700021200401e008150096040078030308200348003220049592080049600700140944425032201501a0041403030010501042002030090100003941c0501408104081101d9480c5022548010342c40140da0408010540000d0404c0203207086507071040d81034840022640d201d00e61131807442d006244080406885034841c2c0b666407100c5151140078031855645280e1581080750301e00a84895150140750700b80c90904102e1041e41c0403043c0d0f03040d031341d12180c08280c102440140c02e0280c001280065441400081ea4104000550340205410783c4240107650995407213a04000d88000e24121a51401407408152041204d5560 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 306346214 1250 306344964 306344977
    0xc04032303160516060816030902031501080f1006030b01031e14010606030b0d33020a080115030506060301050103110f04031b1403030a0f0e15091c0f08 67
    0x10120782c100607241c10340d150816142e200a4555400ca081e04501e41000104241d01420070b9040c5200e01382011b07140d8042403e00c0c60b00582c20555121103a400315513007800f40e8660a8801e0304200d50f40e58443c010641c6503c104460344006105041602042c41d00314042c0d8030889401400e5010070382c3c656210350400c180c06054154003190b4009540700000ca04a00102c200703202000000380032420300d14090101d0310418a558030400420240340001060b0116080208000b088000da400e42c40c0c0c80e026015180a01c101e510702d60021460b412403d074020300c1c0c24100c81c0e641c20000d005900301740c015800c99106580701500010104010700040d4001d40001107402c1055030020324082d1956070000c8660000c1d0030444c0c42c02d04000124581c541d10541400c060400c4100303800c1d50000c0721002a0740e03481071084920502107901d1800302148d001d00380540e4201000703040c0504005082c203c0d146903900807a070180c0f00300d844003046e0382c1d250080700c4210012503008071100034030300440d03c1d6102c4681050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 306347464 1250 306346214 306346283
    0x140c0a0f0f09210f0b0a1508060a0c020f19110103050702060f06120a0c03021f020703110a1d060901080c03070513020f04030b0406140402030a060b1203070503030f0c0403 75
    0x401c00180e410500c034100c1c0350103014030b90703c141030482c40382e015585081e0542190680487d000d100300d08002c688280c028911100c005444500510142e041600c0540000010f008450404030140c0501406254542c45041000700002920006400301c840503a001e000503403080000030341c0004030408132500300c14024003144819003080304203403800052000c12107209403050020030031410b100b4002d01c8038015900c4400c20040c0641c00c029940d003036a1001409141007a00c0f0340d003054552118034005050028182180008440b505001d18034060b03035043d0181414500004400502140d400d8203101c0041c0a007409620300720400c1790403968090211441c5a00304078240e649081c0600510003148a00142e07007991074a424003a04903450007032200181c84049042200503507001c1103000c0300702e5002d000041d1440c0503030003060000704d05011840c8680b000050201c10300a00001071340c17007044148200c0380786589042e5841e4450056100c010711800f041d145148042001101481600310030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 306348714 1250 306347464 306347519
    0x21903090b04030819020f2505060309060411040b01090b1e0c100e061005041e02030c1305101704141603060b190b07030201140c0a0f0f09 61
    0xc658824041c0c1c2e1083d8412914140001100344403100415050318020221380041c0c00500b01110100703440341400c58070810803c040e00500716280a1400428000d0580544041d899103041c9010396a2403409490659100105802c2c1d0040ac0c07030b00b80240c020008041e5210307100c10b8504500a83c290300031b0038020185412101420754410713099005444148026070061601c0d84404a0140889c0d070314214181d02a08120b04201c0741002c16004a0304682c4252000120001c1100d8981c0400249005081c3c899000000740030300c1d81301e2903028000c41112403900003c66580c4030204005411340340b1421000c15600c4c0c90440c001d0382a480e085a201c1d01400001c5400c4084101c05800c0900d203500000240b0444002402803010034800c0c6850f0a50a4982814107101c0001c1da11060b0818030441d054030307800282c03480415100390000031f120b810075140c0d5881814510924420b68000203140c1000488500040e511544503060381d4144808544880604506010071140c200b9110b2070b010440c180c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 306349964 1250 306348714 306348719
    0xf0324090902031c020d0809010606080615130603020a2a0201030c050c010507052701080415020708070c050411040b03191e051503120d020c070b030a06050906060a02190309 76
    0x126141c4c075084070720b082d03025001d02c501603c4050204c4902504800c510b1780b500b8000c1c003034590031141582d009035040742c044208040f110540b101a1180464405110915403000a1900d030550090084203102d522a101e0a160484181912640548a000d10324a102c0d10f100c002d540a94019011200a450140c0c90880e0b000f043c20b0a48506860308400078200203070f014418070305003e1004102502e048100072440e45030700006d046500181019002c1c003080b1501c00e101130703100d904a038101d0760700195440e102e4803c0d080c209141011403040c0c9001d2403c04807481c4404065000316019540d020340b4041c1103031244040308106071442ca0080c5045a600d0714018001c80d07141d5105024000d40480105072884d00d9501c014170f5801180c80035010398003c00c00034041c005440c0540c0d05a00d4414401030301c0d80c0c4c100e24014600a5941d0026803a000e0000c148400442e550f000202590820740d05542d45071181018170220307110740c02d034090040e006010102245d0481c1d50315621a14020b2421104840c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 306351214 1250 306349964 306349993
    0x20d0809040603050717060c0301030218070519030e0f0a02060301031502040f03140c120a0303090c0e071e020d050403080702122a030708120a02011b0f032409090203 73
    0x28442d0041440d4500c5081c241401c80340811140d0350008d9072a90003410740d403550780130030f11a06010715245240c0001d0400503115034805c1d010784600380c1d041c0156000e02205284054010722041d103809009010300324400180030400503116020301d5002e0202883c5038a140c80b80d1404240c2d06050b030171050b4081000060205010401002450040601a2007900c855290500c0c080446030038038012007001e400a07031200c0300410020703501341e0541400725068150b840d00d1641c0c880d06030050001090441d080c40038007036002c000301c8041c03041d05e004105007600d1010241d90300c0d010b0032180000a030007004180000340c1e8400261203030520141c203d0316004511800d042c04c18500d080340c0d403044110ba030a00c150030309016015150382c01c8160050015503050040c80e6480e0480040c00c00454000003810120311032003507024003000c0300d8488002c207600e609540001e15414481c800307040000c3c20200380010403c24408001403401d50000320070311003403411180c0300c00340081210680e0715004a441c9184c188 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 306352464 1250 306351214 306351223
    0x2070803071104050f0c160602041d0702120301050d0807020f04051503010605011d19030803040b0a0605040b100f0513031211032104020a0305100c03050601020a020d080904060305 79
    0x258481e500031400d811180040c00115130f8010700365a5440030030300a000501e000c6c078040715100c4001d543d0440d2048050304000c4080e1090364804002010703841d40060314800d401026078083c101540c256108030380054540d600c240401c3c000c1c5580b0004494140700021141c00050200c070344003500c007c43c103080c0342002a0494904031001e034a40d031920f0051580070301c0d007845520f02400003401c0082c038100410f54900005507504c02c0303031400740c00300e900304414a000007540e440046a01c0205555203103898079043d00e905405030784140855050a0001c2581d241c640604048200d0241c0425420fa00d50202154207212200010081c4034082041c8000402928201d4014502a42c121480052413810007001c0100c594141d0805030801e105008500342c0c858001c010203404c00c5114071403602c9900002d05209100d520041c05032140340b480c074080c00d00c5030b00700044081080e101003100d560303650010784c2c44900800b0000c1d1700003001b0181c5400a9192800740c01d0400b0040d20008806480c4da0321985070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 306353714 1250 306352464 306352477
    0x100501051b0313050a08030a08190e0a08071505040f0f140d0507050c01020a15020304030e09191a01020d2f031c02070b06090613050a090209010f0303021c02070803 72
    0x114010b000b03101da4240420301400801c054001076241080e0132340c00402c0d001c0082c0400c080b03104090302c03400c00192150002d440d2039100d2016658030105a14107500710340c3c4004422900035081006070100841c0504c01c80f4070076504044003800982e42030340c611400740c2c4898030864480c00103106404014070f040090b42d5080407d0384505540360601d00701145070141458030a41150b200d0288140040c501c040c904840440c40c032009070b1a40c81e1444c040c0d91320101c0d40c0240b80c111602c03500f00040300344000201d008001d003010040000c114101842c1c1015040142084d003d6800321358008840c41c460601c140343c030704115038102e9180e01550030760910310758024010081580041641c80c07403212032800381c46200700c080b40210700c1c01d6190307078640602a40090200703200300c4080780010010340341c501c441601007003190410003161424001038802441190800d0340110110070002c40c00c1a01c2c6100902035a805400070001c038699200c1c034081ba00341121100d4218001d9040009140310200301a000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 306354964 1250 306353714 306353737
    0x71202090a1a07020a0b03060d02100509042d0c0e131b02010905060f010f03080a05130f080f240402011b150c0c0b0109050604020702130e0c010503100501051b03 71
    0x380c903e040d004000784404c164012000e414020024003103181d80f11640c0c2c5040d80ea0540c2c010b07103021a01c4605440750301030001200e070000d040c28650340c80d00304040c02495000700d001d120b45645400300702e030b45e501300d42080c40c0480106901203100305151600007048500300400c0040482c40200404d85404540c035801e01c2040584e44520b440c1e01006424060a584001c1e004001e62240d8500040c0050450741031001810b00400041d003044018070410846406007507a00382d64100d02d07550150b00070ad982a9100d101c480c0d0141124001d81c805010451040c001c05c1603000354a10b05c1d040003404051140075000301e050240425070081041d09e400c0ba40c00b5001d0048010720560302100d50b02005441050441104002d40e981019002800303a043d618152030340803078001442d954840110b002441a040d001e544a01005582200c07048a0342050110400789820b8805d130040d03400040d20716000a8034040306000700e244062000d5445000901903445c40d540d410b403481c02480c8030540c2141e02001c940c0a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 306356214 1250 306354964 306354967
    0x1080c0412061b0f05120a0e01150302031b01080a0b0409120504090c1b140f010915240e0402040b06042301050a120905070b2205030303071202090a1a 66
    0x880c074003040c06122402007481d0070040500580391000400e0b602c0341000d101406e006107800300784660101d60112100c03130300d500000c015101020704006503503001480304a210b480b41841141007903c4400f000141c008060b12400c1054551101c1d44000c0c199180324030b41c02a6031424000003181c80c0100300300400c0115102d1550b1035050607824015990128040d009000700420b02d05481010101441c09807034101010300c3c1c4612441800070300340400502c595150398203088440060241c44400040c030025044020810b07405648140b850581004110300d02d006550041000802c8000340c03c181d10600c003d20005030200b07001d000a8035038000f074102c08088448500d9004c6a10060040025250000d080280c10030707115120003072950805145401ca0b042d101e0001c40c08104041080d48045c0080c400300719219588100c1140b0100408a02e22102d140140d0000856003400b1003200e01598656903500a9a6410fa0f07018000e58800c41e801341e00881e034a10005092005021240c0000304c2030410300d07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 306357464 1250 306356214 306356231
    0x70b040b0415061406030403020c060d1505090405070512030706051303120b0f1c060e0f06100b0a0c1103060a0e1005130308060a0e0f2508040201080c041206 69
    0x1008100e401036809102d0500d4038a05011011054031020320002d41200c60641d2941c03540780407030805400d141206e0f00b052002c6641d406240c1107411103403142a0111001881d03654442c20440303146000e42e03010f40940c000b88024822400c201281d444c50741e0015080701d2030094543c0d10b03001203030400c55061080760444405581010750040e5105c5442d03510460030f00c640540c00e00010225141d40003601d02c05c4003c107c0340300381000100074440125030400400c00050316007c4149442d0001414aa540d90080800042c43c0b0003800d40b100d815036010030b020900b80f0004800c2a03c84620094003610b0303624000420b081240c2c2c04125903481200e590102003620b03100c00d1030151030310b0103c41400e409282400e0400c80c0c21103610000b10540c940502c2d0a03040c60f08c4a8021414000ba03a400603004120360404225070380d0103880301030b4042e00d0440c114540e58841301104034403c90103146101c00154110022801561091006130b0b08460661003031440d06659045400d182c26100c07104032001904c41069 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 306358714 1250 306357464 306357473
    0x15140403150b030a0209240301020c010c090e01060903170405130c18140405060f090a0c0f0302250c091a0a17064506180304051302070b040b04 63
    0x110105010b040e0000c00c0d0706401980046d862410003032145621029200406805500e414980d4070310b12005002150394042021042e40605040624403000c144507c01c00502d07500170042c2d86040302c185503500e04030541103642c0c203100c60211065a40c1c582c6000d01022400d9a5030f0b02044803401002100080e0b0744a1059020b051400c0d000941031080700000c4003040040d07420030b1a1a01c80380102e130000740b1543c0d1640022214804810881d03000455402041200700540d840b8a4082140752511554400e032074004809a128406c554468191300c0c00400050000180300520268400c41c06c2c0c080740c5031900031031004c40790100c000703844148101e48401150b092901d881e4000d041da403d9002c131480c074140951561440e015203407000019600c0b010107074403000c401e24507500c40151401004e031f088511000e01c10b0b01c2c8046950040900900c8045024030541c5c3c1ea42c1600300c0544400382d41020729060030800c15150b814140c070409030b020004000001c0754012a00d200c1c41c8214103070350460a01703061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306359964 1250 306358714 306358721
    0x20618010209010f1101060b0c06100e060109030210020a06020a091809111c02130204050111011a0d050a05100207031206060813080702120607030b0301050609011514040315 76
    0x2500364810410400a0f036848100401103001c01c1c00c0010094012400d194018004e6a12209416138041042c0650900201d00303c4d0007010b0007113202c0040398a030300d00d901d00000300b40c031582e0100303003107510400040c14981c01070090480c2c117006482c0f03a000c2e6600d0b40320980c0d12166802c0001440400c00b030100069000784140c1c041c00c4028208031074412030b518810500032141c2c9162081c0005c00000c104180202504c030f84031a80580540c1101424481c4076029400c81d00415000c034841d189024003440c2d0500c12030303c51254900280c41403010701d80034003a66550268094449004d120603020115004003c1c4904a000394003005a684d06a070400928185215a0f5801070a007080001c00250744e00c850415000342d615500c1d420100a240b800545a2140c000000e40115502004002d908008600d140c4103d009803002d20074847c005040600700e94088503881d07070080040e001070200c0280d0390000b084d9100c1c1030800b50186a00e071155500150400c0d441118102e1411201410340d400900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306361214 1250 306359964 306360001
    0x607080106030e0f0d180306060b040302090703091205030603010f0203010f1a070b070806060904090501090b01270f1d06161d04270c03120507020603070503040c150206 74
    0x20044c1c610803003c503c8090700c50140090304020041c0216030010341c0092060b080c00256031210342000038565500e2100e005802c14031050f4072606e8017100054005010b802002e40c030079841609c00c03001205240007030703030300350005098250159a50200494107030014401140648031081090b80c0f00352500e8402000c03031030b201d03104015145050010038001a03c50704100e82003200340c280040940da0b058089078050044804059009041c1074070300b01407107019404031803401d0040e001000c141c0c0c1c07240c0c90740d0800d200103c418001e9004443c001d03902003680f90311031100ca40a8000200b02641e1825521f408405804c0710000503421090038800600d50800122000c800a41440d00e8400c0924030150114080d42c09800c0c00386da03c42249180d42c16400404581103805100840c6980c205420718124442072408100c0b03c4503000000440c0301c0b801030703003924412503009000500c0c41e43c072102c08540580020b0000c03208003819a6010580c5250106c541c0700148003503000b42654a060b54101c000c0e8440e02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306362464 1250 306361214 306361241
    0x1009120803040618020616080f030123220b06040306051603050a090b01050f0a09020406020a050c030307021011150c070219080705010f0e0301020c03040e010609050105070b18060708010603 83
    0x1c4610400585420061f50350b071100900b8405080411414468414402c80c6100c9520010001c00807421070f400c5200c4c80030004e011040c0c804002a480c0c1404220701d1501c003a21900c018001032107131018169001001c0952001e4106800d05a4a94690055500c00ea440c0380b040c00203503209200095161052580c443c80c1d5103070a02064072141c4840c071031380c4818018540220303000384030500291103800440c8020300000394110364403603032544001e464004210b01218140a070041030f20051a0000c2582c03801500107250008074504100291004035418044804a00032960540ca0305414091214818125940541da4030821481040195092980d40300c0020508080c148280c5030001001d106540b402c0c01e244201070000e0030203846100c2615482941507000107401034a01c28007001800844a01100f6403011741d80360541540c01d502d0740d0040900190051002c1004100f40e040207a4004c0312000c00c200300c081101d50340ca03040031000c541c20004a40c4110040280642c11702c92140c081801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306363714 1250 306362464 306362501
    0x4090b1b071a060303070b090606010e0d0506061c0c0617060301150303030209190b0c06010e0c191110060f08071a0c07080d081e1510091208030406 65
    0x1039680d941e4a0460240100d402c40e000200192080d241001100d00103030300407005c441503181c0301c8030240d0307103100c100c40b16400960105215031250815001000440744e000c4040d18032590b81c0000e0041c428500c0030011945d181021590f00414000040000a00600d03136071980c0c505050f21217180074440260169000380c0c5072002440c000c0c142c100c0d80c10250380e414a130150380c030501c0c0c1c0002800050280202e070743d03280303858100007604c1a503407009000010191051ba0f080b682d0b07442000d82c60990403501a444040200101240d9168518516400c01181c1c00e1860030203810b24540c5290001c051051b03c11180c0d20b07041401408404100d50700181503030b8008142c2e003400c1c9410703030400b018512803240d041400840c0070841604244810006844400100c0b10f01030030b44007004146400560740381ca4904900f4220ba0354180c0c42208080c0304031402c105080a0048034401d0aca0044841000c0c201003282e4803001081240554081c0c419060040c100320380caa050a041610032907000f0304961541101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306364964 1250 306363714 306363727
    0x20f061018090606051801050310021603050c120301170705040b01120e010e1c0f020d080105060a0e04020c0d0207080c0a0513090615090e0f10020a020c04090b1b 71
    0x50203030000100710540720118040a90b442c100000e00342c140c10043c3d100c88007050500d034800e800e81b0543d0494100300c0c100c9194080d00380c050002c07407080a01d849514a00740c811080440d00800040c80801e180c1c0d011a22075846111400c0e03140c0d00280c100454910010b8030b0014003284c1001140003414044a0401c1003809520000e0a000110841c0390003d0f42c0318100303100150820f6000c0d04000d0000029540c00801066200a0122800c141c0c2004034180c00d5906012900c0081c8208188840e41ca41c1001a402c0800300700032a00200040002c100c0a000c031056036840e14000b40c1144101e0308008d10302030003805070187c1043c801d90050361f01e9920038080d0814644e210264a412074809955100c8041c580140c9100501000741001c0d0480c0c2c10404880400c580d409135100448038901e004102e130443d007617145511740444504040300c40e481841e92981c42a8aa40203007105081801181c0354040c1510206083c1e507140382043c0c0d080c54160040000482c200f05e07285c2c00c00b480001c0c581d842c024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306366214 1250 306364964 306364979
    0x6030c040e0c0f06090301180c080111030105060d0f060f1d09060c16201003020c06070e04140f04030912050d03090303090807050706030c0e0f10090510020f0610 71
    0x2d041c0c44851107200c070000c0454058480f041120318000c0c025000b80300002d940310924079040000c80045a40840c010710014503d98184240038901d42c0302d1088a145da442d2000300245034208089554405903a805403c12a0b00c803440344400904503408118211032034401240d04045e03180112081c1810304000308012100c0110305981d006694104407900c1d60740c03005281500c0485c10340020140c4100d01429800d50b00c0704c1514682d819030468141810242e80744084059009c0c02d0900b9405502080100d6400e5004002c038020345000076000050309100817000301305501c01610340d01203004194051106141c3d0108101003e131440d20052008080903903916661055030401610400d5603504e461410988280c21409010790401d500b25121846030600a41300e00640c4105030100349017040181096016408d00440303040000d151243e002040703010b000c0211504030001041092003a00424541e988909103038443e4030319801401c01c08000c0e40494944a005040c071252501c0ca08c400300001e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306367464 1250 306366214 306366223
    0x90f030806100c0f241e1404020f0310020d0f0b010201090b0f09030f0c0102130510210609050f101d0a0b010e060c030a0206010b0c060103030c03022406030c040e 71
    0x99032040d840300d213040c600d0074169201c50f02010780030207800115502c01982c48060300404180680b0380ea064000001e42030b0a08211024041d0900e1902c1303a140c0081c2c05490b12890f61b0a110202405035284c0b20003c0000344100e80c05000b18a02007541d602440341421014410702036000800e0008004102d42a102d5202405004104085141c003180000b9444003042c41900c6010804460702a141c8840400c1c523400703500310a01e150b0701103206103000201c51506401d1070074414200d840e9900180a0070b00d4524800c0d0120350790740c10302d54681c900000c1100e110720400f4071450b03400600000301c3c1004103042503d402203600c00b4140d800d2054528130909040010550050045000055440c1c201d100507240030b200c0040300381d448240404c4a03080380708003000415140141d5801daa909a80790583c00e0303128091041c50003150361181e4010310019014840c42c4500500178011191041c10780c8149103221031103e03d0040180581c01c1c14494141410044042d603a00116428022001c0881409503038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306368714 1250 306367464 306367487
    0x20150c040b09190f0b04090f0507140a0509090103031e0c0803150d020901091a0901030804120215280e010815011101050a02180a060c0803060a09090f03080610 70
    0x25020144001101d001000007500108820300e1843c0784c4c2c84d41c0e0b4040c44800d80082c4180c001d5141800d0324000c0401c007600c5014468405034444080c91840c001c18040140c05c07400114003409800c0102c102182c1c1d0b0219218020741c445d5844c082e6038560b207101b100390300d182881d0f094140540e06c80c0840020f0344003c1030b26441180013000c20900441e1070001000503003500006034000303c0510010031806100d81040d10318010a180b90212218031005001500500b44030107054000140b009000e503141400c0751501e1b450004150754800100d003180f5078881e40c8641020248006501c1080e90340c40300f000301910100300241072003d144005800060500c0310024015034003031300502c2e8801074a80c002c0a01000440d04400200500d1030150440b4000f0340c071082c003085d084d145817801c584047c50f01c0032007681a102070740d03511903072105c165585200300d410184c0f600e50701c5140b2803400b0886070118480e4058881c0036103610052030303000703041c09800701c10040e02060050801054800480c0d0700b045400740d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306369964 1250 306368714 306368719
    0x10e36160f030b1005060a03050609090a02280b03070203090a0501050a17190c050912060402010c060c0c15090309060e0a031e05030c0d30050720150c040b09 69
    0x52a500d50b20300b0081c01925805c00e951000e0f0101d04443c006516034081445800f0a0b21403443c1d40d01c4040070309a4601c090316000754405070704400c041c06000001c03d40e00780700c0c560102010000e900c4040324200e0707800c21103103100140d2003c00c1440c503900e01a21804010002820070620388500031200400f0110b034a110300c0c000c00190804200000100e0050b2060610142c40802c01c6070303d5407000403d10760044250612844007086000b509410100c2c00a010310f605031030700801001c455448601034070f20b13440140140402c40b840003001c02c440c2003281074882c0e001c03a400074968416240103480320030150410410400c1c451a08045a00c500d0074203003d5030782110722100c0401c08840c0f540302c00380310100003c01c54040400d40050310301c17000a004004a41d19100e010320305070442c035480c040030303c01d00e9120a035880c042e000d20101105d5a100c0b540021503807401148000e00103a00781c0c0300115500d02c81d00c2940c820151984107078503210000350003c0015501c030346058600f81b059021400f96460061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306371214 1250 306369964 306369983
    0x90e01020d1e232e14030c0a060f18120b0405160b0f09031608060f0a09050d0f0507050d0503090d0c021f050d05010f05100f08010e36160f03 62
    0x10035090303015000b5000508012024444d450b11001e42c1c0352100350315800329000744280040d0a050386803914504091301d2a903030300d006443e02c02400880729084031070f076914514007400c00d022600e01a1a800000c00b0784c040c41d8140d06c0d50403e854030f03074508502041f6854618451350380510131000010101d8800d41950300d9510780300c0305061b000908089035410b0124044030181c0e0002079180740400d540303100d2600844031040a58811141e4026541110f00c000c013942c102c00901902c560044291040182c4039141580c00c00d00180e858502d040c6030039000303001184005c400c00003141d20400915900094502e080c1703c0170180303680420041c7d040440340000100f1280600220b09100b60240c0d515030284070000d0003a940e440151a0400100e80617070b41c012810128030280080c000e00040300c50880594070f09440e80e1031700300690506040a080c4c1e4803441c0b440d0002481c102c10b0200c0700c2042030429a4607040d541c1c0d81e40c0c40706181108100c506c001c0071720b00740801c1140d0403180c4a202c0807280c2085021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306372464 1250 306371214 306371251
    0xa02010f050c010f1b0512040b0a060801020703170c0a020303010b03090a020a0e04051203060d021210090308091020090316140a0f050307090e01020d1e23 68
    0x295414052031416031200d40c40c240c51384408403801c0d04900a401040700000948010705d120480300c61007000745c14103030100b503000814000340e4584c000641c0710f814598005021911030040700d007640d0100e070082d000a041200c140c520000c1140c402500804042c07000c42c9003035505200691640030500c90f0040c0316001100041d403804081c4044c2c08107507070040400715a503403070781c801d40410601030340c0036580c074481c805803449160550710441e4000d41d0010b2618101c004554200700320817940a0100d2458000d6a840e08486072590203681c0300140b0a48900d15940b4011004a10b030107a40714141d83d4960812840990810100c6c200c200c01c1d620848200e0750314421321001c40d1400c02d1614038074085812556000a01582c0804581001503049854008503941c45810555500e00350007848e6054000340c1080040355078540c00b190344050460005801c080d5054085000c90329a0a40000c141c0100d207000180b07101c4134800d21641e20040780e4545541c5008400000600e43c0003810300d140d03070326614070380d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306373714 1250 306372464 306372467
    0xa0204020d140907060306090207030507110d0b090325020f091b03010906090c03090503030601050d09020303030c07140604030c110315160e0a1a090d0804080115080a050a02010f 78
    0xc1c00c4a28105070070204039003005003c10340c3d0f414083c814000000d01d008800308040e9218000c442140760169941400c040b0f440d1900f00ba14180e00c150700303038841d54042035100010b5a0494151164103c00051038443e1220030214401004c1c0c04840801d84201140140050765000c070000d01c010002e03249001036a807810010881c030841c500240e0b00364070011000040340c202c1508104203840c038104060040604052081c0c06036007522500401ea6001400010025489a0701170500c00c0b4841002040b1718465130042411a40156244a04900c0008098080c00343c3d134005d00b5a44c1030024006d101c5450709031030040c02e110803103000804110760b030b089030f90b0030b5941048480141000c1001d00c1000c1e0824045c1301c0c1c0364569031020700c0c01241c10318030740c46254504106d0b45000c94a003042e494608003454000360125034098103001d0b070710003400007071070300860b402401030300141174128000107904000103403d61100da07407030740104495805440381100040300810140200fa0307081c01c1401c9108840c540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306374964 1250 306373714 306373721
    0x603061507081606020406141c020a0210020f0a0f140304020d030e1009031205040303090504020d1805070303030605060403030e12030c0f03030f1605040b070512280f020a0204020d 79
    0x494120f01c208101d808014000d45500030001c0300c0258640400f80300d0504d41c03080003070144400202c1c0c8010714240c2154405006c0d001031880f0861441a103c01c1c0030808030100c22600030984a046038000030502121147e000a071b0b146c9a080c0034149081e4482034140400040e201c0208001c0c0564401031403c0101800b500102c0d48165005000d4074045028100040803065a4130040c0c030b00e221091843c607035582c000e504650680e901a6070784649a410030b000c2c400a54840b040201c0c0e130b1503076040501c42c40074004500202a6100344090032605255040040650f410385d008140f1440c020801080041d0b0048282005541c040e10f41130b0220450010441c10340c003a541d5042c00e20f002c4c04a00740e614200200c0290b216480b0013001044580751240e001c0c001d145001c100d82c0100e101000103225030442d903800f0705a0140f04504880010031071450051643d081100f0300340035505040c1313005102c5003428500901c85070310f505e000e8045007040f80b4002c1d40c61520b184080e02503513000445042da08110741 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306376214 1250 306374964 306374977
    0x8030a180306020c0a06060506030c0d11041706241c03090305060c1c230c13060801031104052215091407080d02070e0711070603020a020705060306150708 68
    0xc1c03045440d511086203185c2c41d841d44520446609180103008503040c80d103032054900448883d00d8a500f810301d240c200c0300041100d42203d400c0c95205100002d960890703210f040b04ea2610711006001103042021070010003000c440300c502040100003a06d41d500d071700d448000105240822850035084d030500d040a40d20f201d4280c1024020b80100410041d4941d1044000d01c0306255411022052103811320070300301140d41d00720f00c5030070714a4401a80c00e81c045001346000d070020112150985800c8140342c054103c500994012404240c19000400c2880b03c419100c281c2000142c805015501c1c0c8100355112482c9400c031007910205900c482d070300c00c3c00100400e1413a468250a020010742040c0d081c4850344010600d4903030700c4d030b103d031103404190040080b48610f05400a80c00400425090a45d044c1b0400c100178203000411031a401010702c08c801c00c0044400411943d1001070b40c94810003402420221550461070281004009000c00d58a6402a110002075800c04058841d41a031401c46c0881c803810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306377464 1250 306376214 306376223
    0x6010315050619030822050d020103020f1207080117010e07060f0c1406040b0907030510020304060219180b0a0e0d03020322140d0503070605060f030a1505060a08030a1803 75
    0x310380210170000da04000740070441100101d80e8000c00307004140d8080c14031034016a5007140384c2040810055004e0307000351072482540a2040d0030048000c241c07100b2010100c54020024503510010454862985803800004d203201009002107158409000c2c1d861019210703000800070707075484400100c0d00c20b40820140c02d902c006550102c400009401c1d595036800e40701a15a418104085480b101d400103460f4112580030300500510711100741b03824029040100700340c4a9680820025034105050244081405a262500240d0305102c002c0d00702d0084098100000d491020070140c182c1542110544007a404111480185070700e103850b0490a60140f4852904920244081c130780110140200300000c0e150440700a014507030742c039403c201c11441d20000103000c40d0020440040450210303040654480000b50051540710307940e40200349403810401007a912022800c0008550b20001c1c0101d541040c1d040701c07440c40d00783c14014880d480744180d0302000280641025290140b60752401c81030000d5821 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306378714 1250 306377464 306377509
    0x30c0106030809120a05060703021c020a0c06141e2d01030312020a09091a120102090118060801050d110402070c141504140315150111060103150506 65
    0x320b10305592503400c0202664031a07100c032014545894000036500000d5a04600205440c0c0c0f107000d0160b00942c040701031001000c058154419080e009800107050602d1540e807a604103121a0820500315500d0150440e18400501e0510a54200826030450300c428410720500c0c0d95210409080c28810014418500d0000c5007100f41004859050305c04e4102c80c00707602d135801250388141c50517080703214900c0d5150108003042001d0081da101a400340d100c4082e0b04038002d40c0300d0801c1000880e4041c103174241c0e01051390001601401d650744030001d0204d0a03244025031401c01d0600c213015007402014040d090042d091900c0b43c000303001c0e81d05a80c980e03006016008642e142d42905280c0401d050500075905040f020340342002c01c1341842c5001182a0703010100c41350901e03003480c0040303200400080c00f00e80e05100b6840100c03070b00f03125126603501506d80d00019481c604050800074101c600c007141c181015400540040005c150314a1140c0702c80d4502c16400a45660b482002a03043d000e001d0306800714401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306379964 1250 306378714 306378719
    0x10621110d051c120e011b0807020d050a271e05060414011214010312170a0c03150b040807050603070c0609020409150e01060506090d14032203020a0e2502030c0106 72
    0x42d441140c100302487c50391119001c3c07222094483d1a801c0e07070504010390118104181c2e080c425030203820100c042d40f0301800b40003010404180340300001c41d4032488220400300b003045840d0007020480f41c1e440c0750218040e00c00d440c140015042d40120310131900710009111042015a200340c5907800c814105070810010358034082d40100c2c01301d0b0701b40001c03544020550740d400400d600400c0c5060303409425180ba81e20681c5c07044070500141424515407814161180c45080c40b0740101c01c100c1c0040d00428038110f444610b0721320b82c1c0745480d00c0c03540b14500940023001030000041d8410007401619801000200c0c0100740c9101040003400d02d40809440c50340041c0c41c04401440d590400d03520303d41c2c2c12000307012141e280c20420215114101d40603502c942072421140025820804542c000c1030410103503401c1c900b85041c1c07002d04181e0300340340f44032450b00d101c024800c614104628038041c0c60160050003040c43c0180e2500d49180b61019140d001c945018107280066200304111111006c19500034400541d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306381214 1250 306379964 306379991
    0x30b070503061e1c0201050408030c0a05010b04050103020d0305130f060e1008010b04050904140d020319030603110f0a0302210f03090108010b0309010621110d051c12 73
    0x30419070300c0c10301c2030440c010600121031070300c00c0e011110a4010101d84880b1060130850000c280e4441080381400030a01000418410500140c840010000e001c0c08040f045494034a0031120700f50303c0e05210f1403a040051001d6200e420001501d03550504001e6a24440544003440d000015409640d4241c100c0d040454880e900101c40880e0800039204501e40641c183d10584110780c003402002d046070014441040a4500058034640060040703450041d00722411502e0790601401c0409100941d2000034040c0802602d03440c02d000e03105c0075180801c401400d55907510003c652201515201d2440350703075003004650350030381d0b800000d5a0061014103801c0200080d6544190701003241581070140c84008445480040111401100c05179a4041180c0c00e0192140684d0000383c90990035650b900c80100d26109039804e040c1a0749240b0988510020107480c100d20440384200c81e0f10f009680341040c020020300000356920302c610008001c1c800030140d1030760440b02c02618181e01c03c030b403e06140084d400380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306382464 1250 306381214 306381217
    0x12121306060303090918120f050d0905070e090f070501030f02090406060315080105010510050310031202011b1d0603090c090103060c1103070803070c0f2010030c0c02040510030b0705 80
    0x10317800d0076020700001c0c40401d0000081c0b4102035010340a103030b00c568541c00c0c5a104103203020000600b81801418160302c4020304085640001d0300f10380e2035014840c180074402941c0c41956108100b14024403002030303800040e03500e0308004d00c03410381403688904804558244079010340e4000340015004004203691440010040e0401080894000d07426000c0490300035418080d0605842e40502501c4641c0c00380ea8084549030310042c44642103c40d60308010000456100c0ca11044195a600100e07904030014091410800c00403014018810340059110307000c1040041414141812201c081e242c0d994915003500302060100354943c410741d4a000071081010580c422442750456549048a110020510650302e2003003030b0010b060000d040c400112920702c11610340c4165446500c1d90b047c071303a503035a60b9042c03409d9034281c070464904200702c042280b03410040e07100c082241301450140000040c0c00c01c054141da16000c0060b00454466001031000f00010f00040000e66000e07a4075000c0c0c1c507105d88020100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306383714 1250 306382464 306382469
    0x80a0609020307020615012a0204180503190c050613030905151206010e0a1a070213020a03150b120c0c070308120105040b0a090903030b03060a1d1212130606030309 72
    0x149507800c00e07400625440323210400c044881c03182421500000703281d202c1030010301a1204a034026100c1c0d8940e002d801d00c0b000f4240245208500464071444414861446090010402400c002e04003020703101150300028546d4220108040d40c4482d0030700c6040c122881c84e0b480d009140c006009540c41c0d0745205180000b8a0701e1624a24811096151500115031a14860044544c0104000c80600501c200003010f9000340c2c0c202c01c4c89030714208495010030000c070300b121540e802c07040d4003085021049825004014452083c1440310200c2d50600404880d51700030701003882c03560800b0500040907204a042216180c0e0015003c458003c1e58911348105564071009450b0580ca09110000506050500601810160003000b20300d01d2810060b021000300f8420301c2c10703410103407038034242c0c20103880901206004201c02640450344d00c0e11600d00d82000110101d20121550202c0a40e82014902c502500c011a444909540d0940c0b076289039418412520000900a00c0c07800000008041d08400d59508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306384964 1250 306383714 306383731
    0x60e0a020306090705010c140712060527190201020106050307030506090d0e0607021203071407061106060303091c050f030a0f0c020108010e07030f090b04061b0f080a06090203070206 80
    0x91641d0f16840c0716101d841038400c150104280301e02110014003c0c0f20007e0000d800c1c1c50884004541c0c8103c0c1e400305447d00c4000390760302039584052251002d00d0400003c454401411540100350303c040140ea610b41041011400340d9854000d4901160b100390010350041c00010210354030940c0700d003070907515010252030310f200d90300c01c0390303c031682050103500031007035190008010034205009038081c04514400d844890020b8001001441c001a44588201030501c100c40020602c407030400f140a4850070005046075410b910600800900f80d400004a851151050718501807140b000c0300b405a06103c0800c0042443c003a450b00c28050090000c040e026030402590355036010141c0400950314481810300c01382c00641000010b2088402500c0102d0b000129842c0c00030302000f00003000b00849a60030001c031509a66501030009001359030080000ca0100d0030384841c003400c1c808134080c01240c0d0071010042230141007000201391168507404079000b8215648159504e161008009465030011502c120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306386214 1250 306384964 306384973
    0x31a360a2111060712020d091203060503010204030c030204110c0f03120f01080d0806060c0d05070b010e0f07030c02010f0c02061006030204060e06250c060e031605011209060e0a0203 80
    0x140082c0c40350b0112101a0040d0015202d030340c0b11110304840d040404515207106607001c10030b02d640418107110b0b0380c541d00c0c040c3d5a002807440480400070195142030f4800d0b0710aa0050100780080360502d0310034003c41b03070b0441e4002586041005141c0c910f015044214126009001101800c60302c007000030300c455034180c1c0508a60380e0f0b5652400712000828002d12000340c1c400b94100442d03600031801d85800c001c0061100f801d0030400003030a0301c0d1258010840d0700007000801e0740c8007005003140300c89000d0201107403509000d160000380808412402401c0c86c04158544041d031080da8001c3d441048001840c0c0818441c6070942d40c000b1b503840384203485072000012011030015815220b0301c01c0c1c4d82a03804580e01c1c44101c084410400015411040f118180c0704040a41440d91001d907410701002c0300d10441c8202c0720140780010140841e250100c2403030013908203004202005140309006802c0d910242403145a80310390b10800801090014401050710f403070117480c0e410541c40001d170145d9042c400c60846 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306387464 1250 306386214 306386273
    0x241c0308011a070b1603320606160305070c180203190b061b0c030d08070207120309030f030302190905040b0613030f140102030a06031a360a 62
    0x204582c8a80310028042404080205901040045004071900385030319000c1420f90500300720200315441996000c0c7d0800d114052040c0340700a4400311580004201c1e44941403081c203400600030410015030050030070000090900801444c0c5500307101801c10858080c1418034900100300007944142d40c03104016418076403518004074240070785003450070050714181c1071030482c08009010021058076010381e0b020b040070b143c02e143c03010005590300072034a039a20310050905110180c248842504196018498400d142c000f080c0c110130000200c982c4a03d140c482d800300d41c101200240134600b40715050790350301d41110340c50b07903070041e083c2c02661402c07141003009110b441d04005035442662212040261340480400104000c0b2840600a900403140054540c507a0403003e400c90340110303a028600c40d0340d05030034014400303005c51440220b08010001007060406212080351141410480341d03144041c0c42c030f407084a940b403142d000004001d04088440710100c80c5050f140429559180c0b100059209040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306388714 1250 306387464 306387509
    0x2011412040c062a080c031204050a020a06050a050a180306150501020c0a0806061203160b01030506130503120703060b0d02220b0301060c031b0b06010201050f241c030801 75
    0x80ca00a2003910a802ea004d002e40d180c0e01113400111801c01140008c0c042d200c20400310070200c7e840f661052001d01540215441084008443c94002c401040018041324040c41d4102c400c03101010043d00340b0300101400c0c040b0081401216800080c0303900c0c2401c9001c61803901c0980720209982c801d809842d944172808007031001200b00380c071a141055010b10085092400d021820154800e011360980f45440414111603c0901c0c04560880300d55010300010070901c501413080b5908481007401c1000300b20250b0b10354660304e005200303588005082e4a004161158000d920040041520340001611220f00001180c0250805d0309041c040503540006010001140100c12040e00c070b559006506507400c0c04d008440d0440a16011400d11201960000850b03090034410790301d240c460080c5c101189054000242500c00c0541545455182c0c0b41c2444203021460f40401e20200507405c043c0d80340c1d52041c4c002001584a04c0a4040d040e240000c5841410381c081035050613584104070b0810601c000f13585 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306389964 1250 306388714 306388757
    0x203030a270b0d050604051b0c070b040e0405071a03180f0106090609050a020c191a0c07120905010813061b02070602120f070b040f0c080c01020114040b0402011412040c06 75
    0x350b552082d124101f401142d40ca0420140080c900038104a44ae06a00c03010300541651054124030700c2c03680c1e40e00401040210400048010340600c01c54901c110f4a8500024047e020107021011001c480148d80040000c003084440e0840100300c0c003d0246913525030b405d00041426000700100b4500381800981790903400e00803500c4810a44008214401e000041d41400d11040c0c02c0440f520814840080c15420300e43c40c00030701962280d9035903543e507040e92610200c102e0307040c8114021311540030000c210580e00100800c0d8050103011004240745164a13015008285030b83c520780300503003001140412a540080e503201954626003c0f580b500c480e0015003101400340c00b16040580d0300c2000b015000482c0034024a402901ca170703145d0503200c02c0035501d20081980c243c0108000383e11103c01c40d8910b43e0b090007002c0024080c0d00001c2041c7c181512140ba014400400c080d043c0302d07103c01c90206d51b803511003c071141175404443c2c02d52070b0300300340c03805181121407845940000303961302c00c1440040d8180c50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306391214 1250 306389964 306389971
    0x51b0418051c1101060905240a170a02040e0a02090906040809060703090e04110a1202010212070311070612062102040902031213090501060c0203030a270b0d05060405 73
    0x40040001044201155107082000250442040000324104a0f108000d02813070014280841c00810315181c00a41e4461084c00310140d40307144a030a03803030561207480f0300400000b5035400c10070114180c4200c115061800c44400d0f0002c2d00103240210114541d140806c180610a20858005130145c444c144140d0ba144000c0d100035140302e0082001c00900d03e0003d0080038640d00ca41040e40145545414035450564201d8080e22000309104500c041071030032100a20261403007581c0d1f012181e03280d0300001e50300d421f01c1100c001c048200060700820f06001d900d5441015004030201c40000c1d0329410000e08046010140e1910a41418400b1841c00740103450034401c200d40d00d002450340c0300a034007080041c15070600207a8140c01003001d01c000c1002140c0041402e0100100c03030381e0070b4500c3d03c80800111407050b1b00201c1044403d841c1080140e8000c01240c0c00c503001854074482d9001f0007011000015100c10348136007030041d21a0001002c0c8440400f50950b005000f6040156941c0e98040c0301c1544e1085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306392464 1250 306391214 306391223
    0x1d0a050726060d0b090f010b10020c010c020607020603070903050c1e01050a03060801051602150106081317072a0308030604020c1606021c030c080f0403020109051b0418 74
    0x1061100c1c404036018016039031004000b48541c03062842500c8800108405403100300494115007003901802c9000d004240c0380d007800741c5144036003900c4d4060094403540e07059201810090b171621500290b44e208010707212020740052200380c3d2418002e50291004030b0901c000c56043c0940c09403080c00d49402d81202620000d142c688051440c00c0e40c00450b0503511101c0f40c1d5041c55030b5200c01081c81d840c00d100e141d100740c03411880c0503d0f03580b640c400a4034000c100000d2010404c4071a005001c01d541c80b0100b1508051034588000d00007030945011605a814400703da00e480a010450300213000301054400b440c9805100680c9004c41c0242501451001c540005800300c11300304081a40d60400758001e003074259031241562401e103503038045018102d11503844540143e00890034149980c2a20050fa0b4515000341001c22100c80542c00c003034031501c001801c080c5800083c40004040c98000e411415001c0e41c0801503400050b054454141d243c4203071082c03540200d02d091003504259541308008441290007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306393714 1250 306392464 306392507
    0x102100e030c123906100513061d0403020307080d060303092903070507020a1404050f19020f04080102031306050717040b040201031401090221151302041d0a0507 71
    0xc55600d040c3c0d03041c40c0c405003e0886081c03580c03401d03824803d0140700e000d8200400400400303131810301081008001045a21062460700e1000c0094100d45a81c041c3d8ae034900c5c081000150b40d5a00341030f0b081d40588200a002d002c4002001004907016501120903a0720030340703c91810a4488003042100d0034041d83c034034170008803100240c490083c03c2000e55408295450a40d1070701e115a8013180b40742c101d40d4040d40941205600d02e000034a418000e4640c010001e489003540c03454004032003201110041940041c803940000c0500e074043c00d5800301d0300070b40350300c100a41d030313900345403c40d880242003000303081c0c807404d1400010402003441404484840d880421001946c2d0b1502d48501201200c0038000324141079a030005c0842000e0440180384c000c06584c000181c07120b0720580402036210b101c4400a40c144120401c00509400d20508103090100c20303210884070b084000100c1000384602e80110844042c02d104201f11b03400d9902103030388120309240c004e0003203417540c1d1411f42e00b41c41d00001810482c0c0c1c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306394964 1250 306393714 306393757
    0x1407080304260c0619020a080115090f06020c030106091505011404050405040f030f03050c030a020c0f0303010801150803070305090d030201020909070c110d120e0102100e030c12 78
    0x42d4400c0a40424000c4207420a4940aa00c00b40040d0362022044503183d41240080064a07003144150100d420741100d410351038004071070780081244405004141201c1c0340e42391003504091061800102a0009071340484500d619400069590018031148511a40c00e1800c04120a8100c4c0203000e0103043d400c000c980d18a04000054468000702c0c2000e0040000510000030036540d00e014582c080d038007408660501b1403160a0090018001e00c0400381407604000a00040c4015041100d91000540900580310ba02c0d00c01c1d02420303c1c0c014800034406200110001c42c5491042d8851031603d0b14280344d460151380d541c041280c0380d00400344094003007401032001c40c5190404000b075184062292000520f082c100070005801d00d1402d5484500080001c034001003004049140401c0d1a1000c0350354004058680c1d8450301703d41c1a84800a00304500c031504199564001c000204010010160a204070030f0b028144594a07041800440481e110f402550071801002c074007118245078a0031211144c200c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306396214 1250 306394964 306394973
    0xf1c0302070501090501092604030f060b010c202106070516080307050d0b0d0b0c090103090f050d020d0903080702100507061406210712030504050a0e01061407080304 73
    0x420014040c0d6083d500c802840e00014021b21404034440e200c0e03192640c0c0b40074030101c8016100c055000401c0c8a400c10007043c0702146120740030180f0b40e580444d0110f103500c0128012248140501401000030134240310300074008511101c40791012000381c900e0013008202660010710400b500340007212a0700843d02080328184510010070340c8226100c0c0110300c215044d03880307c1c60307a0300c100c0e00e280000740081041d0701c00b03290b00e0152800b0071104845440106000b52030313a40e44040050002c6070072034030020301c0344483d90098100b140c48076001109002081903a0070300545440c004804807005020741e0311840b682c03c1c0118401815aa00a0480d9003130040325804e105186166214550900100380540b0000410f60f0054120303156880c2d032196843e0401405200528100340c0c1201800c119210625078050350014040d002c40d40c0740040c401510055041c02c0e01d59200e240c001c55040001c8080101c0c42c082c2d080001d5048810b1070341c035160410000c4a20044c035000e040340c0248658010004036001c42c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306397464 1250 306396214 306396217
    0xc140a0813050a140106090b04050603250503100209030c0301230c04050901140102101107020d1106070305120601050a141308070f0e010b0c1507030905060103030309050f1c0302 78
    0x224450310880d400b0f0301d0180c81c2c080c035a0710030428201c03140e03465031005c0c0041aa07600440031071200940f403e02081c02d2000009403a54400c2481c09282c1d1074482c403d00d4034051044c510f20007800041c0c1950811006002d60001030750021b13030164040d10031000d4000180c1814402c6085c407140c2040350240498500e290400190000340941501e848144404070301903076030b585118000c01d95030a140f0800b44840001a052081c54210360503903501e41007143c1c0781e000310001100e084950449103203100d60060300d08040742001d410100c0c0c0d04140e003c1501402c042e0002d00500384100352500d40c0881d6920b43c3c0c011540d6100c0c0c40c40120010701282003940c2d654400c180a8031801038406c425000340340e03c98030030700d140050690225001100019040240301c3c200a006405414a09012454085480980d540d1a02084c00280b0032252100002d40000d119a0100c001c503540801036408031b50703403401e0050103403090303c9080c1d5046c0984102414041c400180b50110076041c441c0b04d651074459014150001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306398714 1250 306397464 306397501
    0x305030403080c0309041109010818030306060a0908031b070b07030c02270a06090b0303071109040516080a03030605090f072708070e06010f020c0402090d06020a030c140a08 76
    0x8621085c44008502d03a554025203040300b030501955900d40352000001440488040e0034400a00d0010180c07110301e41c2c01000701c80d4010f0041c0d8803990b440b18540030071582c410490344420114003010501c8030344e504066121480d800c040008a0b440d107621048100321a2098480003030100d42c808044400509000080005500da5a40340c001c071032412220100c0500302c101d582060895035208188003403034182c401c80005e404207400840c21700c123107a61210681d848034580148198445400601081410409032020294114801303110941e43c1e0115175840712094011004241042008125030a220380158415046004418a2502c0741e1005450801c91452146150650704400909440045440a00030328800c0001c1120328a0154003030704411029011a041000043c24048520350025640001074002c48005a07a10075402c001200004425030040c1920300101d2004d44042d0113501c00740d401405078030341c00ea950342844807030b511910500441038041020b40c1e000c1010700340c959000c00d29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306399964 1250 306398714 306398737
    0xa0e09060d061d07080c011b14030f120606030c0d1515020f010518060a0506030102130801020306030d05090d1e080310080705030601060f180e0a020d0501050a030503040308 76
    0x641907894840700240e4458000310101d03502e180c500d41034030040400694004000d03400103080ba101010000805a000325045a1106508044683c044c000f04e01010042c1b0004801201c0d038500324910342000603004000d001e0b105980da480002e1050070320200703d80c8994075110429140c20a602d0004004050408442d40540d9800e04007081c2e5140084d00c01c0b44007034690f0000c2c091078400c890380d41e0a481c6c0c01840704d65400040400400203038000124182c20403a0032401003550381d01c00011034028019a00c014040c00d000400004a8034030660041d4081c5d0b6003503081d02c08001d10504240e51a20031503403d6600441c1c2c004480002c50b660100003132030114582030300250141a9140c9001c203802c151001600c1c600205800c1240b0002000000000c00c401e402420f41580340801c080d01503580c1103114400c0c0400e10091503042d4510304c0410000c0c0500204481e07450030101d030520000d421105c240c1c62010724040004c07071145414140341c0222070340480114503090443d03807003c0b410f4000521222 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306401214 1250 306399964 306399979
    0x13020a020a02090703021b0106030f0b091f020301060e040902101b0602070501060f0614070f020d12020606100c12210504030e040c0507030207060e0a0b04120c06050a0e0906 76
    0x60b030b503c02800c0e0003a81e40e540e0258a40141d90030400c0d41a0400c02c0741e0206238035103041040002d5030a13003038141003034110b03001000c180d44400d100c508011480040d1500c0140201c0c103989080c12960141d4103850455468070f122644410a010031512103000c0039512400c0c680c400320300c5a00c43d480360b44904080c02c1041c402c914490350340d031059800c00c0d041192141d4440302d05200f04541c604840300102400d01d0f1645180c07100968811241c4180076000d004200816040410742d00c50450180885a004090b00000810314400a48801c0c09581d4544124480e111268000e80318410401165800441e2a000348429800a0b41c03c80303400745101d52642c003080b5079400c102d031040c460580f02c0c038066181c04031106862000c001c200c5503112126424800180090760109500080c594162070082c00c1c118404001c0c3c000141c0265010f03401600340240026012807002014442c6000701c61040b949105841c1e2588011303030b1b1900404542000282d100312a081c40ba181883c0030f80c0d0040400361154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306402464 1250 306401214 306401233
    0x100504060b0c01112104020a0305031809010b0a05180307080f01050f13080304060c0e040606021e0708280609050d3f02090913061a13020a02 62
    0x10140c410590050315040008602980c801c41c2c01c0c02a1003460380e11010750b030b1074044440d03800c2c8024034050b4219520307009000005005c5489084104014503040002c23252030340c60449a080301c1d0002402c1c4c1c503000d5141c52000149400a0005540c2d80d1403180d190507043c5540b52403001d1a224040031210b0785449060340000b42108203000c010f91004a800012030329240c04214407208007409000c80840d0105c00c4040e80101700600e00781d81c1c000341c0c02400482c0c3d401d0746001c2211507080140c0401d0b4041d1819800241d06500050382040c405101c418501d46140c0c050f5074103071180c10302c0c814010250490040740111010740d41c81c1c05200c802680c0c00c0b42d4546150340380d800454079404c03412a055031050541e48600f03a00a8150600500c03840c01c100d00711782400b41c0d8040c0c94091011040d81541c0303105a0504545800c4d010b42c1d040c00d0010b058100c07a858001c0c400140c1801c01041a42c88915012082e4001210360180207030a003005016070a018030340744502c00082d800f0b40e40e1001180956200ea = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306403714 1250 306402464 306402469
    0x12090618061603030c0e010c140a06051810091109100306060303030605120a15110d0908120c070b0c03041b060801170c10031e0606080730051005 64
    0x54494100c2c031407038084452560340f50190450345c0d0300c00c0c4a0240320040c6da80203501d81c4e0088a04003030941c4183c1c100360003400c4e00e10f079a2400da104c9000421441c01d103810090b0007660855049909440541154082200b15203154100c81c451500900f5000360b4504865450504680154002c114807031813440c210340e00d84076441191072582080700000e40304d0000b0403051070001e650306541440b45001d48013002e1980d480340c9500e10f50005c0794503090f071900c607600101100103007a1014520b9141d003d0024000514007070a0a601042c0319101c0140b443d4086150b0684400070348107042ea0141506007107840d10300e8482c004d0b4100800c00c6440001100040000101d4040c079480144419103e511065040150419410002d05006c1c40e0303a0740814210512503596900d0a9140c000904000440000c0c0b10b5140e00b5180c0d02c01d2903240500c2c203000c0c00054450b403000d0b072984240c0d015500c40e4001101009a0411610019841d02560060516451050302c6990005420040500204d40420340d0b40c0c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306404964 1250 306403714 306403717
    0x10b01082a04180f0e0d02061503011d01020403030305010608010305070e06040f0c0201090209280b011413050f0405240102010b030d08010e010e190c020102070807060e0d021209061806 81
    0x45005040e1300c072407510140700b90b2409414403168a0030080c02da407041925009540d8840201780500c4800c1c1940054505d490a510140e081c1000c0c00c12080c0d90b441e0800c100303010b9807151100b100040c3c6890000030302c1500c29102e0b00c3c16680d02002400340301e8030f0b000c8991a07260000d00021f0303020f640d03020f1402c4252580d00c40c2c0ca190200b40d030004521458240100031082c00010895a403210301011501421200c90b01c804423064808040050708048642c0100c40e02c2c0712804014495120000794042807681d85040d640c11680700301d4284109010600600064480a8520986048410000026400036030540010464040c800081c0c0d0b24542c02c0000d1800c0c011000701d501142d50b5600501c915012102403e01509109080008504000c2c24201c1484800d080200400d81d660700e4001605200390126444550044000c94841c121030800b10000c1c080c0c03800785e60083c411a415130f65401c2c004a51001c149010381c3c04903007000f0310b56040c41072940c002806600c0b51300c40740040389904c2d540c410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306406214 1250 306404964 306404999
    0x140a050c1603140607020d020c120f25060c15090201140406050417060f0112060f2a090e0615070c2607050a1701020c060106050903010b01082a04 64
    0xe00c9035160310030f000c24a00b003010103000e010440d004258448450b50300064200743e800001d03a1a0060f141c01c8403151800d106246085044030300a0f10305902c2072004840d0380d400f84407049000d4040c066500c40d8140c41140003906c00802c0e4280a0142500c4041144e020007139aa006040181c035034a0540003041c84c0c0d9001e5080071011940108040c040328141010300c0d400c551a0f0300040100b401c045810040c110014890b10f080e941d07800b0349080402115412500e41039140c020309000c8100c004c94400520306002c0110401e221614072000c90303a603c20010203017180c4d2035212900003910b0300018410000c51148040103402c000f0002c0e5030000c1c40910440000b004104d00c0c3c1c20f000c81c2554101401d40e00411b01c100f02680c0012001d00055440740440d00442d071070046038a511088214025019000700c0004280034052180002401074120b401802800e0048000b0002c0c680401c0c015219034a066a00c3c41e512941e036084180740e80e4218024681d0b51950402c8241496510007100340c40c8500c20 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306407464 1250 306406214 306406223
    0x190201090605250b011a04180207021c060b09090318150913061a0a0f0507020a120f0507080f0604080906040513020c010b01050702030a153306140a050c1603 69
    0x240010008041d1700b00b004031041c00c601c00c0e1241f070545030a0b0803115003103c1170038078013085500280c0d0710215501d80c0301d80895100b44801c00d4a40c0d880c14101003009108040009016400c40302c00079402540120854a00344c406005034a481d20101c000c0c08a150b404905400c106002040300440556a811881e44042103c16002c2041e60400c4034038007070130031001c810b41c1820b0028800a1040b03038100030f8008104c82c4910702161240e8403400043c3d114080c0340d00c0f02c0241c4407148001400c0c13240212041c0c3c4010b00810447d2142c69aa0103415a1000d401c0d151200d190401808900058070602c0203241c110002004141019110000180100c0340030f40303441d42aa40c0002d80d0003414600380505525201c090821500740020340c1c001c2070b240d4007012801020b06000300501076031000141d204207515250344144100d0001611010210031204268517030000142c0b0000180840c0310b6411040b011400203241828a20403c20070b4a860b08036074113080e46c40c0900f01d405101c40d041410400c0056024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306408714 1250 306407464 306407483
    0x7020c12031903060602030a0c03090320040b0901050a0605090612280504030905040f060801020a030e010b090603030a05030702120304110f01030c1e02070e100819020109060525 78
    0x70b0701080e01c842810000091600304007003000300c1c50300030056030120002e50030001c2180f003480c58122014215a04001e040007464805510f8070400307000180f14a8400395801c00c40c89201d0340030414444402d118103035000009500a004030361052020b8501d41c0d070040c200c0f90806446010400441d002225209401c010a0720524040282c0c2000700e2401001d046042001c1e08298030001d145092600845015903207410415003c044c90b80c0c004002480c140d00215103801d022b1324010082d11103450030b50301544c2030502401841c60b00d80421400f45400900452601122000c00d440c02e0700003d20302c00540c010206040603a0a0800045105500c1044101c100e4039004040040b15240011424100341c540454050130f6a00608034402e56100c5903082900d0243c0c0c00c03000c80c50000c843d00010341d1241e020050000180000091b00140c0305020113555022501848251003041464070180c000f42c260740080124034010001030a8014841c2414207100c000050343d0084c200341400c00302c0c1c2c074640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306409964 1250 306408714 306408727
    0x1103090d1407060302180f0102031e0a0e0f090601181215050c1602040e0c0a0f0f1d06090411091f06021218040b12010510060305090d030507020c1203 66
    0x4041c0400009000b6031309086092940441e680701003a4204402a07000725202080351115a0003003050b10b02140c1d000c13050808030f01c00d103869054260040c00d5450b02190022107440305614008100524a00002d4282e4010f580c80c40d004507140055100203548e100d83d0841c0200d6402c04074910a88814058075003100864100c40390101240d8004192030f1540c4824000c951880e48103441560b00e4940441c5d000c00c8400210800f0340c04c0480302c65485070301c241c01003030000780c10302a083c00000300c0d80703061103126100c3d9443c04281f0b90410100080680311420341c00007012868410403458006020b113052030b01310b25101000c522542c0c02a504410702408241c207240b41d401e00000d08202412044c0301030b28001200d0354120f4000e01888440c68844d1a0009120241b9101c50b402401c1d0640000e10707074040d100c46a00708900900b020703250030180845161001c01c03828040d000d101c0c060544c2074014a00095848000c81c02800080c20020841c01860a000e9140d40e40d0f1343c1000c007070044c00b000b4682c4c0d441d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306411214 1250 306409964 306410003
    0x406030b090a091208060a0b0a1d01020102040302030a0308100f061106060307150c1a041208060603060904150624180602070608071b0f031803050606011103090d 71
    0x140200810b04007800d12501500240c02c1071081c240c0d2000354285404151550f03000580215100d40001004101c082441039103564004044101c11000621503102440350200490903403040e03010294050f80301083d014002031040c603640c4d41c00040e000080c00702c0c0380c03100c180d03c0344021650300a40010fa01040340310510f0780280709098102c2001c60040020a2800c5800c418200303c46d00714a0500c141c442248080c40380a0b2416983c6d0040f12401440ad49480d1412644030202c000f00c1c20000307080d0740300103805414600d085a000e120010941c144c83d07a104d0340c84803900201048010102a16428001150003070303805018140c40840e400704070b1401c080c00004104100a041403040340026500c10002690003084920035241319144c2500f8596442c1c200b40c5100000d410000c8112020840c210b0600000081d40f001c000c0c42907445104000c02c15091441d80d00207408081d15a80003600820700960044104420a0b007540d42601e040c03035400400030307665681c00c0340243e41c0704840044c0380100c070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306412464 1250 306411214 306411229
    0x3120a0b1e0f090405120c07030b041a07110613020103180b011e0b03070f0207030804060507030e040c020c131e05060a0b0f0a030c0504080a050c040f02090310050c07080406030b 78
    0xd40b84007001340361a48500361b0743c0b1030580840600010008924200b030340c0078804080a550071075001d940a0500c0c2c6000703144240d05c0185c0e01c02841004020582007446202c007c14130500c150000e0109848a40180c845200341140403414150396080c00000b806042d080c0c07a13801c80c05850400a41e41c5001c1c0e03244007c0c008040f035162108003c1c00103001c9210b84001780c0390040801d01d040504040c410f0310503880d08019400c05414402d02040c0020a1035000009002d118865503408405214400600083e13900c021a100c0c0960001701c0d5503042410201480d05c0000c1c41014003162241c10007003242c0c3d08000807064460155143d00400c00c1e24140500d44038020301c007881c412840c01d000251402c03030601500c0700c2c0d20300f010384406466100c14415400e80740a441180107403810510986881c40d03407030b0020303109540203034100a03031409810a6031098610800c2d018002d40f0a01c546a000200240702c0240300402a4209011100104602030060000780c0302540700010200004020440031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306413714 1250 306412464 306412489
    0x19030e0103090804031118091605040c08070f030f06030819020a0309090f020403140a020f060c0a080d06030503130602070905010312210c0c030e1203120a0b1e 70
    0x41c1428686014001040402210304681c1c124079400e6031002103c00090b0000400150b9800101d0100d0500c10040c43c08620000e1902c58500d0390801c007070380c0d601803000303940e5032185102c04a8442e40000d1b05203400781c11703002209100e5207000548e28010032400021500160810f640e541c1c0f01040d000030801c10b030008807140d01450700050401c0505e82e0b9008020100380c3c010300c0b00031030300c440345001c103007590350107840284d684589650008001401015500c13801100103038400d110702d12030352403542403c00880d5114650304c0040c203c0003089031509030050b400b4591034000b05a5a5500102084050000c2d280f03986c490b400d840c021a1504800034602070f250340100d6001071810004000144a05c445100b80c025141048102001501260034034100540c1c05807030702c0e03800c0035941d0304036940c0111a000428400d03224980100454400d020101d0034044800c11203a1080004031f02407400c1d40c58950b0b001410403008070711241c14801281c1ea01d01a100c40c4d80a03005181c0e0f6401e96032034580f200b200c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306414964 1250 306413714 306413717
    0x1120b100e04120203040b04090f0516050307030b120307030801030c0608090c0108060103140a020910080f0708040821100b0711060a051315020c01081b0a0c0519030e01 74
    0x1850782052501001403102a1008000020b152103d1102038000d100b0344e00208080b1071001e0300c85940d448200094242d2101c8180f203289400005403a11254a0540480403080c0d910b1600319a684801980101081c10106603c03501c0c80c20811803c000030001480c00c1131090359a503203554514501501e040459401c640b0038003503480104010740700c0010701d641c00d4003002d20f030100d140d813100d00058004041c0084200c1a40c81c4802c108a6078802c10f40007001d0032101031f954808420b44030802190091004e80c6d0f039029199695010807441c4c1e06c078100c0b1a82143c0207200b070500d400c10301514200d07076a46000c50520a40310b41010448015900c4148000420304400c01d02e19000c92503450101c08441c00035140e01c02d1001040340b8043c0342c41001a0384d03d02c5207111090107032a40381c0c0800d5940c0e0011031590303030040c071502100c0b080c1c95124016003400742c14120851122900002140009901300c40c074441d0400c40040b9444001c40d80401040b41e002200307078400100303981a400c1c0200264040c100e81d90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306416214 1250 306414964 306414991
    0x60503092d16140d060209090406061401020c0619050c0d08060a05010e03060a15170102030f0105060712140f0a180503060c0409150b1903140f04060c09050901120b 72
    0x34849070000c80c0d80300410700300c13840c40640044e407410400a015503c590b90308200080100b0081201d40c4e07000b68103645540b01c403000a5034244004990303900e00d650761a030f00088107000e0fa07035440d5040180d80c00300000398207100f030070308006921840c581150070340014001a070100601c400703030034518841e0010301400c0ca803152240c40c103038010980e2400302801c1c15041c2c03540c6684151f0324412410102e406009a0134448810002c000d00c924041c2d081602c000780e20f001d64400004240c60300d08203d881c4244d1284a0342008030364003000380c3c0e0001b071803045070890001c100010582c401048004042030070258a40740c20102c02c0740440c140c3d602c441d8205c640643e10140501513403030030960548048401e001c1c00442e202c881044540d11044195014a81c0b54034041659982440138800b0442c100c082d56a0802c400c03214141003406980e000c0c3c40b1006903091240104000c5445500000003070300c814104502c2890b550008a000c04100740d00c041c28412201d0405801c1189407011a0b406c29003040145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306417464 1250 306416214 306416219
    0x2e0506071e0f1505071d0d0f050d05040608090a0f02060309070b1c0b0d022b05030d0204051009150305041112030903010f090506221719050c07060503092d16 69
    0x20043e01d0405161b5610030000311095008008015200007402c81c0e01c4001d941910072405d0028055421600030600071441c020001010b200e000903400060540080c021000741301e441c3c081c8026030348042e0403a40c0900410101150f5800202c000f0091a00000c8080c540320345c2d4000003408888000c00c91610800c410402130740940d9030103c1c00e00c0c2110348080741e03440503c0861010f00d001c2c03a090500034070700d00010860300e420383d0b0686c0c00340c4100c4009a0381101c82a00952040350780b14828000d556141d2803017107440441511950207298054820600358281c0300600000828040442542490784d91000840c0b10840c10207018062804040c080305201d105990360b00c494031144003d0040c1d8400002d50021148603040210101c0482d40010039250026141c620b051020f0b88100201802983c5403030403924418032440841c1c071410000c0300604206401c1180484440c0e0000d41a03154a101e07522200755042041a855003411101544002c440c01c0b92410311400c00c0c10b0342aa030340240300402000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306418714 1250 306417464 306417497
    0x1e0a0b0604020d0209030f070501080f0907090b0f12010e0d0e0a0b07050102090d0b0405070b0703050d11091305040b010b03060a0e06182e0506071e0f150507 69
    0x202a0000e10484001d03880d020503001c103900a00401c1c503000d40c14071450007040c520482c0443d06506451081c0da440030281d1b6221003006504209451840007540030240c100444c01e520303400800401b2008108500407421500051351010300c140da4500c07280d54403000d8800c01401006501035039086410301d480381000c03020006500d00e2a42c801c1070070b01e800000701402000380a504590002e54000c1c10011002d1050814a40b503110890b403c441c288624100803407985010b40980e03102541c96640c0514000303c01020754044c021035015911a9641130101c14640d40e200c5101204907041401e0001d060316050605400d02c10040c1d12036030314034808005002003600c600324000c042d2228011600115100e01010500170716200003035145102c2c104041c880c14440e103408a500440d1032141907030088540d1074040007068910700c5141d520100c20089d640c0090139030310401001c09003e5407059060029500c1c0c03081391b0f491800c4122951005009400710108062051a8000001d4609024940ba540d4103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306419964 1250 306418714 306418733
    0x501060e0f01080402030c0a0b031602030f070f110306070509270f0c040803190807030507020c130e01240605091c110406090507020c0301180b040317091e0a 69
    0x11410400c5007000130b000e540b41044280305002024080c103541d9651072454601c10340081e10310b90fa503807040c180da01c030102c0d00c00401d5900c419070801c25185000465030b82c00342c000240080440c0c0c11142d2208500d01c6941c18030030f031441030b0120303151282c1c0d90f0001c20801424016801c200c42e9038060a070a0340d200583c03040c0e01d20340e10040c0610b0042c1540c036404401511801030350b0282109100000d001c081400c18450040303075400240d122140652900341059080e29002c40c0d81c500103038420103034a03031300e890041480751703103504820b000084906880d030100d425580f041d0201440b00d83c4800700f48104038500d0508500600991520a044c03960060004120720300e0904841038682206480c2d0040c451403c2c04c4d0301404a0080040001c1a5140020703400350208032131000150103407518004840c20180111112007104c41c030007401d4070755103644101c4814400b4000794100041e8600401c00c010001c0c1c101801604910700038400c1c00c1070000d80070b0745980c00e083c000700c00340c000000c21030015040c01d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306421214 1250 306419964 306419989
    0x806010308040e34142106220603050f0f0312040c17010b091e0115020a120528020a020111010f0f0608010506040501030b0a0905010b13020d0501060e 66
    0x200442c1d030f6100e00c1010b05200914042c0c442e403090810748440813580c100c16903580044100e0b10b41160841c0203040e4403d2038041d140c0605880c80612115000d00890005070a50056000305031b440041880c064002c1e152003071a400c80d420540d1444144107100c07041090554070003040d0010418035450214a54580c01850840c00ea00b15030880800c042003003409055010f010342044a401551441e820180604003000c4101e006250400c0442c088241c0541114406481644c68030101c0e4613040c1c08025500781e41c2480002c50081d40c11120000f0360b0080c844c0321066039991890749807460996190300c5c004031180041c10090061500a03030f1241c001c07880c03c1c4a00d809090800003c52200b0000707002d0034400d01c00614a6140007100703070000c4101d50040d82680c601030003c2284d0340c0e0345818001110001e02001c2d20801c0414002180e0385e5650f040300c0c07842d510800004c603c10310004042881c00501600094601e500407442811281a911071540104043c0c5084018510260082402003a452 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306422464 1250 306421214 306421229
    0x1509020a14061603050a090605090a120812100303030507021c0e1f020a061404081b121b060906060105040611071a0a08130b0a05062701060306080601030804 69
    0x440c28407100d0b0b519001070302d08100d00380a0710a20030120740f4006120b40e1160030080003007501b4010100d2a03510030410781d01c2a0300d0103040c404102e404d000900384003140c000720840d046503041008140144101d480e041c020701307808007061880b50840c9400f80907188020848030131584413440084044400306050241d01c1c156040070346c0d070f0402c510041075200700c80340d94070280100c207100c0c0c031500b003540080d40c2d45104e802183c08004c1c2502d20342c1000210351080c2d5029001c243c0c240f200c01c44150000b00507110540308a004c52340304400842004203907400003102400d61400b281050105c001c01801400d80c000c4100001c0e0025190010020304980564002c4e0020040807450b4540b40348410020f5101034840d21290141d05c926042d03004502e680002005000688510f0105819001098000601c280d1240004040e40c2d00c00d042c80c80104001004181c0c4152441605600d071103228018072201003c40c07180c041103604100c00070f01916000c3d407103084580c0c00b500041000c0b446801c1070340c081c0d8440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306423714 1250 306422464 306422489
    0x80c0a020312031b070609051b0312030405070e09070f0308120109090b0a0c0302040f141206090c0409150218030f0c0105030c0304020109030510020a0e0603090318190f031509020a 79
    0x5030414400a1041d104018441c1c07058009d041e0015400020351200030004a0071a04126650980704205010a4a008055900c40c1c0e000b40b1144107402c07001030703001d40f002c011901140e0b600ca91018868001d41d1085c0c42c84080060760035072240c00c3d64026809001c50400c1484050344a0380c0788000200c004010755055980c59030500e01052103501120010503032140e10131915600c0d9106880240c040b80c041038814803210720b40b181d410402042d60740c030901c414009011220044000d010190101a40890f002e80f1071101c400e00e90501c91000d0000c007400b4030360b00781c3c0d94141d190515207003c110200906c90340d8003c4e02c1030304842c3c1c0d204007220f034040440500075450340c40d94030042e41c100d00190801041405440205003200040d5030140120020a668201041110320b00340b010a01c016190503c59400412413464103414482650400074000f6150441540e8440c030301034030707400154100185101c000081003042c070205800204100310941d004003d103800c15400203401c2c0740644607080800c8135 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306424964 1250 306423714 306423727
    0x41e0c0e01050618150d0e06013f1502040605030601020f0304150e030f060106080916030206070602031009050907030b0a020a05030105100207082b02070b0f0d09080c0a020312031b 79
    0x170700b141517900c0030380000e40c1803159903803030f03e8010740b81e840c00d02030032400e0350f030405011180c003c2a18903025500542c2e20040c14800325503005040072041c1e084103030361001c0154204a1445005d100801c01000300d940c4954603410050002410a03900c1280d00ca80c1380d1080c8001e00101031203401031440f41d802414030f403c1803050b42c0042802c2048000b03400e0260300030790000041480c2c221200610440042d011b6501603201c2110820003111280406500100144203000005020364002d54202070708041406550750780303404071015910200e034501e4031a080140c0400130800100207a0b90800005031080d400c01421403802843da0105102c1d80384180110049031008a00034040c42c005001d20300e0903121048450790046000c109286420707203d01c005440404185403011503224161000542403a26000401e100d594a54002c02c00741c03400306a88104000009003c00300030080442c9802c06095402071900405040c0100c561f0070041202041042004040c0c41e00b000202418881d0011611080c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306426214 1250 306424964 306424999
    0xa05191103060112090c0b0703080c040305030a08131410150b0a0e06040b0a030614030d020a03030b1804061406060a0905010c0f062c010905030d05041e0c0e01050618 73
    0x17041900180074080303c0c11021030803030006001059000d000c0e4850b000c1c1502c40849080c0a8800c922000c0e04580080c81403481790b034800d803203594000301c07110031034100e141a035202c8410015180100201c107502c00d1300504031046450090305a00001c03d548110300a01d0240d43c0e49161013140e80b0f440c1006580c802ca90203543d9024103076009040180d081c40d845902c642c1380074000300220f00940c24800c041d8040ca038914980010a80d0b6200d40542c003a1500b081e00e80d070240d0140603591240355201c4151100340b4107004040500f0b83c8a1400f0340008204545001c4043d0002e09020300084c0c041c00041224000c0c50f40c00034180800c40f0020f1a060404809030300700b070345141314445801044113080c491032600b0010700a031181c500c000c031507407058117840302c01361403d00b00d800c070401c0100182c005000c080e1501c081644116800740c05090f9000c801500d051100c8103014150380d0803140c400718200700f40998404424103d000d800150b900b14a480b46070354000745038007081b0311158882c2510b0f488018004d07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306427464 1250 306426214 306426221
    0xc021005040308030118060905070e0d02030f010207060506040f0506010801031218091a06040f031e060203040b011a0301051f030f0e070503010b04020f0901081503060a05191103060112 81
    0x42d03400c4001e26031a0350319206140442250b03911801e070940d0038208082000b03000381c070a170781c000d010a07292142000e076101d040c411000f05091069038980909454460450000e0000f000740030f22482000400c2c0c40d2000404c03003146e03e4100d8000302c50749400200301041c0d811420850540750003001c8410f01c489942c1c421900c00d01d148901c081c0f0641010360005940d030542d0002a4120b00360310181205200500510100e8052480307a00b0a0340c070140b034108045001d1200b00b105200c561064080e008415464200503a80142c0b800c5901c101c8400041000c01c3c607210345240e0100503040c080385154503200002c3c0c80e030515544c458240103444a4207a25041c06035011920364030180a003409078030b200d4000e01d0344a030007500c80e00b0300035424690710440518043c400c0340c00100007030800380d09210f5080e00446210340e0003008000c1c80b11100f0072000031940d003085500c0c855801c00b800800d1903e0322282440d500d9410100c104142070405214008940f00b41083d00d038400307000e00c1d00f034920405407000480034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306428714 1250 306427464 306427469
    0x10204050d0f0203010507110c060d0e03030f0f0114011d270114010302041514070606080d030c021c0e0d0206040e0106031b080613061805010303120c0c02100504 71
    0x1050000340c01104004540b5180030809000700c00070821951000d0301681c210a02c588010400d0300106229001454030002801504042a0740003c002501c01d032403a285d0b62013580c4491a0344541810846413208840c03081d8050042141c84864a100141c00607000e22082c40c0d880420070041054940d4070f444072204030400c0344038088a04c80350784484402d01d20031442806000107107100c0c003a00380d0741940a402103500b107400e10880d031002101e080c1c40c00c696101e101c688000c80014104414004034a141c0120740c00b4050381e0000e07004510300124094121421041d008080d5004a4210404001940c4c0f8140141d43d2608106140d12020000500c02d1701c850b01000394094008280802d00c10003c0340751f035042c0ca4080d1010070041c100f909800508000c00c03028400080e070110006910342c1000c14000060345132002002c20700944521381244640c4440190300e420f140c0d035400400615510000355030070220460000c05c664035150b80001c00d889000207020b40111036001189581912802c1143d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306429964 1250 306428714 306428719
    0x1501020a110904060f24050a0f092a021b09150d02060405040f09051b060d18020d030c1106040b040b070503090a08070f0b0322020a0305010f02070b090607050a1101020405 75
    0xb1003000c070107179400107603074407180b1b042c420503002c00410a81080300c142c60031368a01d80b200b549a1481c1c405814007401c0da80c10b24584110500c1c40340380080e8070008001181c0c1c141900504030003513040102660010390182060b01c10702146c1d0500c240d1030100c0b032080010000a40740c0c0690140a030010030701c94429644250782007031408003034a4159032175600041d49a40300e001501c2d15031007012004204225560b00c1c1640c40001000a0141521aa40042241000280f9000c24000ca40c0c0000d19a600f640600740c0c0801c259480241c100244071030f107002014400c49605090501344802c1100900550240c04c40307051f0000348030010701504000f5920034000007000b14050740d8465a481d5141c00c00b0744240500646196000310703012100d00c080c1d1348203410440200c010000320b445e4550700030142d030301c0698000c900e00c640400030490a01500f1b000424072000136030b03a10304924010801250050040c002908807c1c00e010202e5440011a111480a4904100c0c9040c60805950080c440e40c0c0c04180d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306431214 1250 306429964 306429971
    0x160311041214013209010b031c02070b030f0108060a06030804150c02190501090801020702010206060f120a0506060f0609130b061902010f0c0203031b0f211501020a110904060f 77
    0x6055118050030904c2c98080900c19242c0d4465050719426036004005d45a8035030490140c0705d46804600c8203104008070f00344111106107640d039000c40416403064405005462242c40141b1209008020094200302d440b18200442e80c0345071680c1c51240540e01444c01d0f640700d500b5100d40d2441c41801000c1c907140d00104000301000c5400e98010041803d0f208040c0403c5400c07400107a030368018800e403032400c0d8041c3c000e021241d4881c2c0410800c4030b00050701660041c034690318080d50340d001b000b41078103151048000303207210704120003001301101e203820351240720f28030400000005440f0b51485589440941e038010504c000b900000813640d0098010705e0340d100614502003004180d0540101c0c0c2c603203052141c100700350b0300e8a2500b01c0c0c0368402201c11040c4603800d007004280d8209204001d100398017a110360540ac04482c12907900107800852031000341262407409102d001031600c494004114024002450362150070340c0c81c0300406c9942e03100c1d288140518000641402035903001600e45200e00304040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306432464 1250 306431214 306431261
    0x140304080304140a0b0a1e050f0a120b031603060b03010b1201060306150b2a010e0a1b061409130e06270a020d1a16031104121401 57
    0x11200400140402c2c4101300350070300040c460f90404125103601d0407560764128144541c0c400415014141864a010400c00b0403a041d03400a00e000649101c100582d140700c2b10000b00c890400c11303140342000131032007600900e190425075200340f0300900480f40d0285010a5440c2c04c0c00010340100b904c29039840d00030440711028040501c0650080d41964070032901040300e510001c8007140c4445090281e640080300401c604105900352000030041050141080c0307190520108c016402d450005541c1d40c9a41d01900c1d1001c100101000b5000c55601c040b40405802450314900600c0303207000381140e005400c000680c8a401d034035020459a181074000c2c1e002c1c4010810840c400c1c0c0da401c0c1c00c980c0c103900d030790303509080304c3e400b5a140b00005002c05484c0000e00d00000250204008c0c412002822103d00700300b01850740300c0c0010014202c0c0318154554495810007801e000141c15580c5014000e0782c0c10300104003d00900d10303904002c2c03078002e4002c040d02c20250441c1040e14018030260040841030004492503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306433714 1250 306432464 306432479
    0x30703020303010e150d030e04060b040b04050a0816051002120a08160f020303011503020c0a03050306031015030305091311040501030c02280825020a050108070c140304080304 77
    0x3035040714001404c582484d03030303040508000741c0c4e21019500c0d8070160411340c0b00e0100c2c0c850503010000b800001c100240d06540d4000708a41035201d079001c00b461540210301002146030010310340005001d4180502100c1d400e1a42c401e45d0300982740907161195840e40d10607072a4510810041c07941014946106d030f6600442c030006415660100e407110310060000c4a800c0a0071700c40c0c120314004114a80096086034208118099461000030441080503424080100c1d003480802000d1085406a1503156907030805030185401d06882449000308981824070036140851022600c4080341e81614259440c5d02481d00007400c03052844620b08111400c000448a414080b41b005208840090301c04000040e08a403043c0e899204149119110a05203400d0350007503da881341501c2c0261041e2519403801e00c81841c1060f551704140b4030401505005c1c8810001c500300400b4243c00740c002428064070038900031400410700309202d540107221414120341d07200700400800560b40607209800940e600c0310340360381c2c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306434964 1250 306433714 306433717
    0x307060504031821080c030c07090203042306010303050a1103130509011508010e15090c120f060f19050a0b03060316050102120a0c0b040f0203010b03060606090108180307030203 78
    0x140041c124140d49000030303444c1c240301d100d2450103040448000f03085500d440309103d13030700034002c05016800304104440c031120080c00300070b011b0203900100580b641018104802141c090170310480444c3d204c1681050b170541c0c0020080d04580e03043c42c102e0354581020208550720b040d030242e481300a1201145c040c1044412814080a4400540b031900041c0c0c0d0f50140700b070540180c078400c0c0700440c11400040c0b0035034800045140c0d000c401441c5420b0307110603140100b442403004484140000c1c030041840030342d602140a825410049050007182c6a08004002960b4961140310343c922403c0c1d00b0154440440c04065400c00030000142101015651000c07582055401154114070074000c0d16168000541c00c05800c00555406034010002c10690915048096000b02810400e20840201c1c200c0080e05408a8910648c0310f01d100758481002351040c182507a20044d82c540c880c6d0030070b808100c04c0380c07500c20031f8407444402442c025180b519007410000c4950783d5240c000b101d9020018422003450380000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306436214 1250 306434964 306434987
    0xc06070f0209070503070e1212030709080606010e060f0702040f020a0905040b101b060f0c1214060f0607141c091d04020409080c070f080d0206011a0c030706050403 72
    0x440d400b8040d661041c04441511007180c461000c03c1220602c0f4030981812000e016024035410101c400544403201343d03000e03d4204a600303800182d030f011400e120408051006940100003820818501000000003c0f99802a01004510f445001c203c11b002c0d5500c0350001340c1c081c04890f5045507201102d4400812011135401740e2030050b801c0110000d01818900c192029201c2d030f03030340d4040381c1911840e11800401c0c080d10040d80c6054480d00d880c0102d008a10503000036840941b524584405d02c490302d0b0043e1591040761000c014040d00402c86a44c82e5444000c111080894425a8522070380c50561000311204400b480306218409081400c5184d8680e040d0720000d0544540002d690f0702d01d205040301d00c1404007130580040c02c0c40440c0042c10160000e00565200d852140e061410110890b07140041039402a20b100c000c5c01c2041142d00c02c00c1c0226900c5284a1028044560400788010201894107130090306420000500103640c81c000c0c015201c1c0c15a00103414003480c205030600500704541c51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306437464 1250 306436214 306436219
    0x6012102040f0213060e090f0c12011511011a01050a0c1e14030403080d0f0b120703061505010c1104061503140c0c0c1014040810060603110712020c06070f02 69
    0x40e01d0200b1020701135103146030140c0d8010040c520507230b504a80781c604210090110180c44c00103018480b51101140f0107a03001e0034070391501e03001d10089030100900e4014041c5a03500c0c940d00d00a95a020303a007005070f51640303449081c00c00c556203228000c41110b403590314a0001e8580d0360b40c3c81981c1040c071400b1416074246802040b800c540780380001070342c0ba22845a80300042405504110002800c07190b0340240d400342c026082c0c0003804805074008502d400185040c850b400b03411500c1d091040040710301c00d400c00c0c4400c80040d180312901705000a0004040d0a2000c1c0c0310000c0c031110800b43c0d41e940d030010000381080701e40d920300311400c99030044c0c00707020300d1040c0141003a0540005007030800c41d6400d40e02c0600003030008143c024140e40c20b06c018000b608880c8020041a03080000c144402240280021301182e4003c104c603c6081d4040750441e225074003c5001c050400c2d0211064030510350a5455860704907000394140c003009072003030303240841c20200e85400c01d4002c5140c01c14060b1100d0340c402028000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306438714 1250 306437464 306437497
    0x3040e0a0e0307030c020613060203030a1b020a020112020c2d120403030309020a0527130309060807031b030b12010b06160f0f05011b08060306012102040f02 69
    0x40000e0300c01030303030a10401d00c0d0041c1e106116001c003180c45140d46905150010b0411880c2002403120340c070620045412040160f84004240a40544a40b01d0344001c3d41c0c0c1d00c031104c41e041c038141000940700c0124030300c0030307040191141c1c0d40000b2260342c0c2d04649154854000b12000d00554400554070100d030022180c0d404170031040041034030b42d07003c105004002084031243c0e01d03060541d030b0154020901040d040c3e030401424440400ca648620324000164503400301020141041c0c071a081e070341080b00078911110f5a2000c1403020000750000b50300c030141c41284c01c00d011b03130f5515030104500a043d02d42c4100704081500c042c0303411444d0141d1240868180c140e5440e502c1c050010003403802c0c1d410202006800400c10800c50006030340c034400c21034074030344919000ca4001d0140d480345440c6c100140c10a54035a5902d4034064500115100b003030b103840e082d9003000c500a16048002070303200c000500c100c1c003e503584003406209180b241202800c0d2658014000c0204000c05082e410080d009074040c01d208084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306439964 1250 306438714 306438721
    0x903081006210b131a0301020f0304060b030a1704030c0905060d03051b060f0105030106050a0828021f2703140c1507170304050d0f09050a060203040e 66
    0x4501406405440306616010492071030008505414031180e4040020700b907440e40e50f000d2079620b60322880c1103035400070004144000c08030710030b10110150b5040103200360f1040050342e2503140340e0000d0307a5009810080000311202c2c094042410040240d400a0412100b41c504250f4000e00c1c40180c41035174010014824400c0d00c4100e402e00700c5606072080ca034000c04110000c00040c0c45170300113088600722807441811518080c43d090340360020682d459001d40a00320014032190409200718002441c0c126040e60506142004044e20f0f1032200c00b4601201480c4014602c192031151144120581d018040c080d0051403114040400041c1132030f21000078015907464280700541ea098501c0054010240301c20161455450304440e074400c6100000070300540e000036109680d5464160004042111180c1d654451442c15000c100e60001c48000041030500920010410010380801141d8103400c260f000b030400c00300d040d00d00349003a0384800d50048461601084030750740840039100f11244021841c480741c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306441214 1250 306439964 306439981
    0xa050705030603190819021c02030306060a11070f080303060108070f120f0b0406080714010804210314270706020a17040510080423030910180801090308 67
    0x80152005a0f2550207001100700400d00c5024000c1007910540c16186442a1011902000c4e000a64103c0150b000480f085082141400e0201c1c0198a544095469458201c0006030b0601414110604000b4400310020a042040080001820b03e40000604190703445580941d0b03a4021100107001030407100103c3d00c0d10303000310f81d6014402155180d424003244a00034410081c0060f0142d14402a2260914520354070346101d0301c0050950302e0003814256041c15400c6403201d02c1c09131940d0400860314200310202d141c00310741d0042c0210360a49070074500100e1204401425041d82680074900000d810b10541c030401c071707202c04907503400341e58403246a5102c000c1e1251195410f100d01c80150b00310420f44000a251a081d00451083c007a141904142d03d130000b10f100d000f9030b84199000309100e0707014001400348040048a0075032102000141c0c0703906980c2e48503103a0051082041c001d0860550a0007a40d001c2d07100400d641d680c460400c5ca0480e5502c20290180c20318007415000f061601700403a0211 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306442464 1250 306441214 306441217
    0x106120c02060a180605130209070504180e0a062406030204080c060c070305060a022710030c12090c05090f040f0f0809030d20030703080402091807060302030a050705 73
    0x21019801400c09a41c8841021004e0900c05140c0b400c0038806001c0c1d140000c0d041e104517800745148001c2c050300840c05105120010b60050995014000280000c000f0100341c100101102542010040748103c09554118034088610303000508190030007100088980380c44c00c4107031030031481c000c03420840d640e540c0042d4120b1085004040b080e0b04407485080e501d0070010024000c003031918003202d03030640d980e803102400d1820a9030101d40154001400300d100d603188410f4480045c8503c1c0c101a071801c01c0e000081c04038580d66800c54145602c0e8507418800c2030260844004404881d60180041d104070f01c1e11413120891805000d00c5450a400400c4582090a02491080303038044c3c0000c0d0502c401d40c035042e003068080d8074215402c0c0300401420f510358800348015003002000b0b4030b0700b10421240c801c0c4404c51920030000c80c1040d0b80700344400030100340d00c80c0d1034942054055406200b26140d101e5200320401e00b86500150324414100e002440a50550082d0300c41d066883c0b0411040d1550f50040716103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306443714 1250 306442464 306442481
    0xc0306091802060c0c030f0a02031005010806161418040e0604020915030c04022a0f0a0305030901200307020606010e09040816022d19180e100203010612 67
    0xc408620301d500006042c400300815542207140304030b602000c202c0d80000d1800b0400c3c5c01420285e0404a110021400c00b00806440e00300d080005101640c10880081c0d510b0310000c0c08060b40e10f82c51005c00341b02074000c0c1c1c10301c0a130034916070160b50340b900640101c11544040344030036801989005195000c031280460f04a0103164024203a88032a258840009140315051346101d6050042005004060b500c40c402048031048451629094801042d030104107171713100703010001080d0001d00696101440c00b14100d140d01754142044ea890307807500c28940d401003610443d0b200300d03107075200c1c07040e24014440070285108504590031207086940310801190740410307140045407c90701060200d800100340300060000502c40c50340b80c6648540907000501070312608400e00c00c680004c00900c900e000e2201c8507480c038082d010784440503195003c00240c1d020424521824800e5140c0c29110200c00206400041d44a020102160078205a402d6000001e43c400c1c841c80303010420125040b00908000e01603a8071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306444964 1250 306443714 306443741
    0x170c040302060d0e032803110927071133040323180f060901030c021905100c0f0c03120e030c0102030a110424210c030609 54
    0x141031a560920165801240e0801819521138911503007100c03007000682200b07070305011814281b5441d682c0e551700c03050038042c0000030141044100208036144400711220b410003601c00d6001017804c065480c1c1c2030301c032003c13100d01c1071624802486103c1b0380c0518001e00501c410000c0d0b03131806a0040d00300c42c041c5103c0b0440c42d1407424440302100700d10003013098141c2c024003a007050021038640307a003460056a00942c188038580310202d9070b00b0522510b40851407580106484005410b80c1042c0040d100340034015403a410540c8a0102210851007480320303c1c2e40c6028003143c4c091886592411603101c000c0400e40d020280d15191030040355a1051401400400b01c603200c0803e0030b1025101160425201d10011010f140c030b65100c1000351004200509080c03c45e04001038981c1040a40d60b0140c0701d0020141e11441818003092054600d40c0ca80820f00680030940090961100781099405080440364001003030440c0c4000c5c2d41603219504507001000704d65400300300c00c1d900e03060b0b4403007191301990b080d01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306446214 1250 306444964 306444967
    0x80a030f1d030307060c080106031509050405150405010b18010b1e1c05011a0403240f0c020d1707120f02090303071506140607030810030b010b0406170c 67
    0x4603403070280190000a80d2286192081e41c040304010030f16560101100b2140581c1d80e04c5200700035a4070418403030151209140521800740c2c0040d00b15a840040e01a10510a6640c40410100306080100442050408a403014189014141030b4020301544d00a207000c1c1c10000c824405c000503041125059076100c0c5012070030320035110076055034111101c46036040800100503004c1c1540031050881c241085403400132485606242d00c24000d85001c545000c0000401d120500c0003440c80628540314020f07148600303400b0100003040e000900301200800102c00d20300561130041d59804200081c0364003241c2ca030030080e44001c4180214a02c01182d4400020b080d00c904928031145940011090b001c02103809810011014002030865200c2d9200301d0702039080210702d414840181c0180801003950030200c0c004a08640003040301403047e401c0003000c010f000400038038202d40080c0307450007840d0030800004056841e590466150740c40b03400780a000c688034564442524600b071100174403c00f040c207030a5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306447464 1250 306446214 306446237
    0x31e0c141309170c0304030507080a0809062203080903012a030b010905060a030506030607030b01091203121407031404020a14031002030708041e0201090b030a0e010603080901030501080a03 83
    0x100001c0070102c60441d074908404400c08850719a107405059581e0030030014603920740c80d40c07400c0d500c4e00040d0b91101d251a002440c1c01030101d80c0c1c0505441e0010310944101da5900b28901442440580c0344540c500d20b00c00d00e40b408024091003001030007403500300b03070300030843c154901001e00c1006641d01d00740c280764410400c00d100d1a61080d0441c84601c401814071042c15525900052895004550390781c000aa40e0010000140303070401456400c5404d40c01e08116407108800000c10910f4140106104202131004240415115040c60030140440060402514100d41e036115082c04050b0782d41c600090410048040300540710600c0da00541d8014442c0107900d103001a1110321805110070507070300d170180303910104800c00180000c1d40301c4c143c40d0759603103000c4c0341c5458800000007120a8000c0302900f07807180100140d80051454080c2e82c0c011880d507449a03101c5064101620010b0b80124865007000030000800400d140681001d0303209032000d202c26a00d601c0440ea070740b54892009000918140c401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306448714 1250 306447464 306447499
    0x916081606170a020d06030b040b1608011508060d06090f1b05180c0c0d02010c180e0609040c080708240402030d0e180c0a030e0105060d030513031e0c14 67
    0x3441c9454400c00d021451980d81d03150042444822602a035240d40b002b81044208040d41c01d01404140d03103800c0c4000d80d0f5050170304000720ba44540310302000f8081540082800c41d0340700788d0500b255690100d0280003030511880c0107840c113000390310111108031505a41d000140c0321416540e05442d0040c029038041c08845c003141d140030801511000054034108104941d0010905c040005200d10f50008a000070b00f4000080c80004000c903404c4d41c4400c41c0d4410b0000d0980704a44a030010b104075107040803502ca500349502c811915130311602c0e691003408000070b5250030101c0d29204192420000159156803181151421801220025455003002c12502c5049001c5d0380001200b2001520018543c0302c01c1d98140301244060700c0e4003c0d0008081345413252140d150041103240c001f50002440303a401c0a202140d000e00c80307018000c06100c07011440103800e420b034044d40300007903030044403000c02290314417104407581d441d900c1c0c203940c00d4252581c041094048103030403400402d0040c1c510507101400c10003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306449964 1250 306448714 306448717
    0x909050c030c0102100911151c02030c07020904170a030614030d0203030402060f0d090c0503061303020615030115121401090507060305180d08092406010302030916081606170a02 78
    0x701100c0079040011120b40c584c07540110b0244920123000ea541c1c4e504d2540c02201d04400c0340324010f4200750300400403c001740c01640166121240c1c15517100003d5251850300714000c00264044641d03500c00807556800140e41a0424000c4505420400c070300d2800b0351040c5034031004100c42103405640208080350045c03c29034002c00380214005449820003000281000a446504000b9185140414400d00083c9428000d154115a039080340c812260800d55003c4e4807900020b10360b01200000b0f00d0207640c9614290081241d0b445601c07072141906855a1002090340c00c10101a140964001150308c2c41d044148100031040307800000402403a80750075011405040000c2042004101d02c111928140504200640c2d089c045030300c920006d4502912224505070103071110680a8902c01c0c045003446200c0d0780000e800000038640903a803a0b54810089280840c00c103524002c081d0407640c0000c0120b0081040f10004410040c1c0d0152942e840404486003d02c06102072030b0449000040b4001e80340a50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306451214 1250 306449964 306449981
    0x2060112110109030501020a05120c1801120b0301090b041202030403080d0c0c080d09020103230c09030312040c06030c14190e03100605120a05030d05100506040909050c030c010210 79
    0xf614080080d220790301c01d401c2e40c001269860100f80c0101e820064204001c16041c0c0c8024261001420100c007103201c44602c3d1207209440f81804003008940b078029403950030040d50260082e00a00c4101494a020031494001311010351340f07564401d1180c04130702d1000c0121021282c20118580c10302950b44803100082241c0340502080c40b6880301d281000404500c081c00c40001c002d80001108000c40c0000340a0762007003ca038002040c1c40c807540c43e94020030407030303607d41001c02a40c0b02c6445403000b0000c40c2c0f81d4400c06000c8180c1e0300f51030b400c20042008080b20f540c01d940ca50766060099038208102503903c2c41904050b030030169024002c07043d0b0310f02d0407414244811314918124441c0f990440202e0f041c0001c907125000007580300c110a01c11400c081d204010518004c40081c20080b42c0d94407107545034003448100a02c1d250711038010566500c4650760880240c800200700d82e03661503442d01c61200074041030004035194014054503e0322442d002c0b0755008440e006030054a5a19041d003058030003049101e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306452464 1250 306451214 306451217
    0x14030411010e04060b0c06010b040b07111201050108060115030902100f020a12020d0e090402060f1c0501090903031406010f03020a020f0d050408100b0d08070f050f160501020601121101 81
    0xd09a040c90f07501c0e0b024141c001d01514044643d60500d4065040c00c0c000c058200d00d210081c100300412085140300111034010740c0000c1501c0000a68030001060580100800400c80d03003131200100318002d02041d22070481c1c0c60707442144a905180d04c0264151418036101070741c4090150080c0207054000c00490200d030680d03205450380d000c10380e56511000c2164502440040e8880fa064143e60364215900c0e50390000d0450b100c07000f61419600207040c500c555194a1f028100c00b1610300c0ca03241c00100000e8503e603440c4020701556840391110070040c40028001d80c002410075945d030f801b5200808455000320f90680d00c0c41d03a0841800030542c0698000d20f0110210300c550344019848100a0000060685d0305030b48003a501c524050005203049045d0038154006480c041001445075a00d55940c1c42503580b003176055845110300e06020141d0504028040c25600903818012110030340820b00c5004902c410b80740d801c84c5c2d43c890300120796806003400f40c4003415040303400c03c10102d030003483c0d0a14042c405 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306453714 1250 306452464 306452477
    0x4060b180114030601031112120c01290f0f19030803010e09030c0601150c020d03080f07170f09121207030515031c09120f0b071403041101 61
    0x156408580d24030000e030510201003030031500501c03088680740d40200c403000c2c048009104650440d16400740092000e000d443c8078032600655501018410b09c000300000002e1058103803500001d20031b25010f0700e41007041406400c100b9040c032104903000000c6a2246001414140784810b00c002441000c024001130703d540038201c1a9a00c1800d14412000005944641c80c003503180e51501603514024080500001d00c00e4006101d00c084141c030006905c1d045801034001000701c0c5600c4403082e9000340031401c010350001c81c921061814944c210075400d000c1d500c40041040c866450700e408880111401d01c03140b181106000115100001c180e80c840e800a0b8100c1c140d500300706522105c101c40f039200e002200102c45448080104032600361060b00c2e841542030318600d017900070400000352240799040d000100424004c11803041144030f50360070700280c2005445c009146a4604020440c0018200111107060041700042e090520492851044982b40a6210f0031903c0300c0d9200002c1e03420311140107042060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306454964 1250 306453714 306453731
    0x50703020c010f0218030309010f05161202010c0e031609110903030a0c05072102040504140d09091128020c0315161e1b1203051f05060d050406 63
    0x284590f0400e1884140e0042e030781c09110030701078884c44450102070311a400c1400a468203176000382c14425105a0303440c021f540c810041031800d441c4181c101c00a0403001c444c42811540540552140c0003814403a00c84081d07440e810350401d42d607802c19000c5040c0043d910135042144d21034640010511034201c02c02c0c4c0b4100505500800c0c6980c00482600e40001c06008030001408400d02000c00600207001400410050048040180e4484028001d00565846000038240000e1004511400c15440107641e00c4a04d40b1034010a2150680148901d05140403080c908012201040f6040d0742d0180d041d44280101c101c0b028000b803c242b584510940c02044c840ba034141e60240265204e00500480865660808506104206800444000c01d00c8000b14a005511401007807800040c2c54510f03042040f143d5512039140c20f141c0b10500103001d4071290008600c0250140c1207103206a4100100500b12200301c00e03900720340c0c0343c144910764010320200303e188120941900619440340c050790010400f01c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306456214 1250 306454964 306454987
    0x61209050102210919120302070b01081606110a0204090c120309090c0f0e0603070201110304050a03031b0e0906010302160b06120c0a051212070503030702060604060e060405070302 79
    0x1e00c50040311100f102d030640208801c1d0700e0303c11544e030480c2a0000503d00c00062058a4100150a0f0405003005c140310b80411883c0c0e2003501183c03135244d440b0382e13650415603440110b42d581d12000c05401b1a2103480301c01c0481c65a00c10f40d010500b43c42c0300740041456950680130301000f003503001d405484042ca2513001103011586481c0050b60b107803281e9240d040085c6400c41800450b40390a00000411002c1c82e540904030760301ca001155009412503800d652034580d501c059005142c24001004229808401c11081c00000710b40100054000d88062010168035004a2069540c1101d40400b28401c11100800e5080030341c00c0301e5004006040062601041c2c41915003c10400c81b0100c9802c03a0600c20004281480d1213140000742a042c01440035030719620009400000500459006403114484840128800c00c0b6280c0151050710035503039514414144151654001c4909202500c95070002c0fa01904080c03191034105e40c00541c0c40500c40e21000100005000003901604c100350b000d20100c0c0015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306457464 1250 306456214 306456217
    0x20f060c1608160602150a0f11030619081e0c130209030f060c1204050c18010e070f0c030f120e071e0b1629060306090115061209050102 60
    0x700c10308900008040e00d062012403910f41c0b2014854159a408a020041a500061600858030000d090350b180c175a0380c682c0b214010424050707016403050810301812150203203080114002c08080e124401905030341e661010100c000c500c035940c2e89510440c0024400314400900243c1030754a40709945940c140d48000404000305910340507042940010880502e150800440c1d0084400c8c101905e5945000c002c8200c0c50300880b5141c28070100c404000400300f00d0188602c600c030920050840318252461840d03040045001d010304030f010303540100801d64107809580c00020014080d03844070095145c0e680d044518442c03002c103440a0001041c100c805061240c040c20b041c00103400d000741603492030219010726041d40c00d1840c02030442004000d000180c0d0700400c0b6140110381091845480c030151178541c1012904418982c07504001c902040c0008400c140c006018401c100c04691464079900c4150342241c0b10455603006000100b0400c01c419030103404401d213005501d1070005103507103143e00e805007039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306458714 1250 306457464 306457483
    0x702060c07080c011b1d100e060903100203041203050405030d0902010309021005191b0615030602030c0405010e03010b0a0621060801020d110a05070809040e0a0c050102060c07020d020f060c 83
    0x50496055140e6903489910700504240703a82a560401b4003030b0740031940100e4209241010800d10f451800d01c940c5440048031101040036046071061500741085034000d40059170121590303544500c5120000e8882c0c01000c0c01183c100d0040c6240100009210004142c00407040341407586801c0200c1c0941e035204091100000e854507a50f549100008400100981882c400b0090000b60494400d010840c0d1040c4402546d000d2030024411010b0f0b0240500b030140f47d400240801c2c0000308100820345054050001c41d042a2204003541280e00d04040c203071960341c07601e1908111908001c21015211760300759483c0f040c1308880000081005e00c1c224042c0c5807260130881140e9000203c0c070240c80c0c414410303aa50403e50b05005800c082e0104801002c911a0f4407014120f04800300b0750209903038690380003080310a80704044682c0c2c080c403850b1035580b5040902c00c0502600078940010b82c009490760446900e00e07401009080a1807050b030030414500c1310410b0950304050140700c84070492900700302d90182d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306459964 1250 306458714 306458741
    0x240a21170a0315050a260322050109050a060c0b04020411070309140906060f13090c0e090a0b03030720030d081816050409060b0a121a0702060c07080c01 67
    0x301d10211441003440f091969000d14000d82c070040b410081104103160000c00c92408000d43c0300340528242800c1c0c036600540d984c0994000304283c1c001440a0090280c000b20741e000e03201d04aa0681c0e074000c2141c02005481030308040384076182c88000095480310820303400792008000040d40055040d594400b90801a4100c01042d19a10180419071091050b0289908200d40b0004a880e10070302062841c0200034007241d49400c04115250240407104900f0080c24001e0b004004031007034890001d02410b10049140c3c000d0301000e0125441962501640c2440c9801600651074490350b5595210081d1281c403544401c28000e20846290b95070501c4020b000200075520003901e41000400c02c07640711000314403141c4a07400b07031405840340c0000100d200d0880d503080b540015400010b041c02c0c80900001c0c4600c0c0c0e440603c00c0380100b0a01610314030001180e000d00c0880001400401e00c0c48031044080d29000d0150340200c000420400d642c0c001802c2d181d2003100c1c51414410359502c4030b425034051520100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 306461214 1250 306459964 306459971
    0x230916150216090f061505090613050306190b04090507060e010e041401080708150711030904060608010f050411030115050403050a0503370e06040806240a21170a03 72
    0x143d05485c0145c8000d017040c4e400e61500c004030500c0250051107924001401036502045011402001d20880001820050f0a0711106e181076031040c00030305550040112081e181504820803410948140c24a950784800100b88a07800c2030b1085c0c03070000400e8001c1e41048002c0e9a801e810762102d004401c0403203180c810134891b80d410700990504003105a0060341107a4002c89000100d65601f003002500800541841d28181c07a00c0031002c5e045220315038507590072909010740051100c1d88010350034120b49000b02030800300d5454a00700426aa44181040300841c024401840b101c0480c1c0c0d08031480c444641403003890280d803582c0d0a400e021500d4002c2d10190400310f00065505014082c040d403050702d60069810780c01c00020401d1029180822040422140b402e100340280c43d52021100a403040904840c15454459104440c050010390402101400300c200d40e0700034140008500c0503030783c41c14143c048030030013400c000c100742181d040c040d580032208210301c0303c0f1b016200b002051481c6075030340e021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 306462464 1250 306461214 306461231
    0x6150503070801020c0d05030c121e040c0303080108070e040b060402070c08031c021c090203100e0604050c060f041505040504020c0d0e06090303070b0c0d23091615021609 75
    0xc0f411b00204010420030b0100802c1040051580710301102e102016100242c070140c3c444e4a25011801d4100110380941c10782c1d5000e0005100b00032400104483c030907a0b0b0040c1c0c0d47e0300e0700c603056140c00d081c2c400c581071234602c1000705000441e900c90407640840c0c09440141800c02684a02400005d1070344a48440d4000142031240c00c0812800d0000340000103000b540b600700c0e08035506507010307405000c0540c1c0550307954070102150303010300a00381d4041038010103000c442c0311440c0b015191842a201110540310340c2c018203030b5508105045d180e107282074105c501e0505280450f00b01c0b288071a014100104901044080b81d40c0d81d881c8090140000180001c00001350a050043c1c0b04140c50522103104160501c45030021390307400412240015444180b10b0902e0701c900c1e00c402950f0280000810840341820040e000710100b80100d080c15000b009448800394072166007042d04c4062080c1168005140b488090200c07030200c01a9502ea0403046c030490745400d400c06842c1c142d054541d0420300030740d902d8a189 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 306463714 1250 306462464 306462487
    0x3070308071101030605011d15180102060109140105091e0408031f05030715051306030e0607090321021c030618020f1219091a1609030615050307080102 67
    0x102c4442000a013002c020040c18400041c2c8150010460030086e00346003540002c0c02d844400840d041540464400341d2245c00e122809441d0b1030340c0c19026401032045000025410700c89004900c82038080344c130201c0c100d03400d0000303202207610000e000d001c08000d200700c0c07821600c4400840600c0f071805641415142c1c2001d00d442d2001008846845045442014003400361b680c001c10a0b404842400c0c00442c440070031000150f41381c0c0034906250303000d440b07145800100d860301f42c0c1040d2800400141612075984d59044262034403c01804064405400b5428444044504000002c8942d1043c01215101da02d00c1da07503400402c480c45000c4001a0300d0303001c10000c0f903110f01310386a40b451140c20107504180070200781080340d02428200450300c032911400301e4404410042035000381880303610280b00e41c2c581c6052240d0031410b4a420a1002c407030202c0042d064a03543c040c005000c20380ca89d90b2001d05232541d294000034103801c1140140e40c10146400051565003013000303400600780e00c000942c640704c101c43c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 306464964 1250 306463714 306463733
    0xb310204050c03060307091508070f03030306050d050307082116140408150403031514090c16020103050c19020604200108041b050406031b061b110f0307030807 70
    0x20b241c9500800c0c018040c2542d40440c2903010b991880000007403001009110040010850f0302803040e40c0500320020039548070f009000c60a03240252010700c0720596410502030011140b02c0050300300d0300103018140c0001c0b2168020000034955008103802c0604007440c40b044110192040c1c95114400f21010b024183c0280c0030381d049285032a50030707042c280703000922515442920300c00e4041000c0c210001e410180254000301c2c030035264a020180b400c2e10303450100f00e900040500d0303603c00d00d094800280c00115040440303488050004142040350819030041d4080d010140841d021a4428880c1805503040c41020400c140c0c640ea008140d01c0c00c042c10318004000020305c1c0382d010a4611522282582d0f0400a040d4106600c1205850304c1d010521308003406e106150460f65000382441400003e0100e0541c3c10800d501000640c00a059981c5c5401d8461115070010322540c0c10b00c810b080b1020502000c0b08820300a0090130180c140b4041c2c00000c5d04161081c0c000300c4800d82c001c07400070140800d00d00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 306466214 1250 306464964 306464971
    0x10b0f2502090f310209040c09051609050d0213020d140903120603010204060c02010c05010204030b0a061401030b0a180b0303041d0f040b01050411090409052103040f0b31020405 78
    0x204e00b140003450381c1004041d018100c50064081c80000f8003240812000990840c01011108c00c1000a0f040c1148510502d00740c0c400d0318000210292804900c0b03190451130341d65055801800c04602d04d0f12000f0440c080c0d0001d0419009107a44c5580d2107e009283d0301d401d9100310002405195a003819035000800004080d00c0301e4003983c81800140704c4240c0040e0700001154090910012004007440d00070702900c529003006000c02a1481800b061a607103800003c20369802d84504040440010011805c4a0580c40f0965010a01c0c800400c090000d0300c0504503e100c55070404940d0707020780d0300030924541c1300b90300804420b40340404140807905022132603504902401e031035a07041d0400d501cce900c038000010f008542c461035032080ca04803100c003040122401200003400901c80e0310749a04000c0e44800c0f086010708440c200d820150322074148850212403040384e1003c1c05004c049180e444d00940a0710042c4448017003007803402d400c5407c1c0c588051000050381041410800c8940c284180310940e94080d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 306467464 1250 306466214 306466261
    0x240d060b0310050907050d140f150601050703170c160506060a081501030209181605030601080d021c14030a0603050c0f0f28030c0905010b0f2502090f 66
    0x141c10301c20302c4c1d4408184a0201d0342c084a441400d10b0590034910000301c5400701d0b1600314402e8080050520f8008114040000c403407004501c1182d60300401500c0a1003400001000504030740c50446048115001c01500040544040c034100440250b0b03032700b50440301100580b490b6203c88204119450300001030360141882002500e802c200c4161000c00d02e54043c00000e1180c401040014442c507448071000c41c084042c81e00b02c440024004050306505011401040d019010300000403072210000512040d0381d6220354005c0004e11400c001d0b548844141221007000c00c074072050304c00412031859011f980164820f103400a1200d00d50f1400070710b0721001c581503038041c504201c5a82d0303c9560303002c040c01600600766082c0d42d0083c40740307101c1560341c400c90418014034240182c0110500584106c031405440b064141000180d132a00104001401445685110031504110a2403646103852203844140d2a100c00ca02c0c901d24a40c0c00507107840821100003d103080c02604120024102403907550307401c4500e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 306468714 1250 306467464 306467471
    0x106090608070513020906120720072711040f0f09050c0414040e01020d0e0c030a02060702010f02070b0703050a030b010f1202070203190b100e010509240d060b0310 72
    0x700f00c0429100320001100030140d9074042800145525154100d40754050700d079035101a10310301940082c1800156544a0140200d000c1400d51780a00c0050f08a0644140b0154448001c43c11500074000d400e02c0101040e11503211040600046481c030064405460004030106207c0c0c200a60668020b80c240e2001d5492814007090040c0358545608850644903420300310702414032001e01040c00303003000d000d00070025840058400e43c410459481304031030000705800d0b10041c1103000205a69109100c00c081d502a004000c5000198041e0b04101514112401030f2400a81d03100340c801001e820800703094010580006e041d8069551501c03820300c84504c2401c0012000e03040c02e40091800003254081c1e000968005030400a47da0100050b40445c1d80715070703014980d0303140341c07500007442c00040c2c42d050b056110145010442545007145035050f5400540908007560b41c3c24071040b14800c01c40e0002d202154500091050307502d407840078203c180c0c010340c400704008107880181468600c0c65180000c40f14034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 306469964 1250 306468714 306468719
    0x315011b030914011106070810050306010f12020a09060609051503090607120b0a0308091503040b040b070c080706050f01082803050f03090106060305010b1204020909030912010609060807 82
    0x108402d01809841203924140e580e8454440180c03414104084000450710a4074100125a9444840305120f1001020380e1200c541d516424107580311000c0c081c2d040000c1081d1401d200803280c041900c06100d0004100041c1c0e1a81c50480c1e10031903820741c0187d00040c003250018012410031016204100d1141101145185031181e00311781c80d101c000c1e2220040010049a0000c1c0301000d8101c1c00007200000c5c000a4582d40e00e1900036090781c000d046640c09901c0c2040300d40d20740a00b440c181c0748100c2d00416003030443d40e90782d80c4100450304e0082c030450a00862403624004600448080c120f8244540c0300091a400e205c01c1c00540001305900c118040d520140055096032000e04c5a040c903d0b000c0d10041203030300707040c0c40d09036214094091800100d24001c41009050345054010b08112070300c1d0384041100b641c85405010a0b80701d07d128200c0ea01081401042c010308191112561212a40742139034246180040044c2d2960300182e448907440e9101c1c90140004503641c418200286000d0004004061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 306471214 1250 306469964 306469967
    0x60f060108040b04020102030d0e0c0307060807080103080319090305070b100f1a22090f020405060306121507020708070503060402101409040207030503041203050103080f0a0302070501020315011b03 87
    0x80018001003400f80388001060440e4004c1013610483c480d001411f0081d1845d0301125aa00d002210020340b00c4c1c880c24200042c9180210781550103094035681e411140da00b19142d290701903001505000300c86e0b52541c1d45030358003d0544103000d5203d01ca50355850307546550b82442c00600402400052411003400c0c01000340c000000d02c4d250071a01c01c0381308462038120360035109105010382c00d40442003540036001d20040c0380054003240256911075034100004c943c2400740d02e040340510301a00b50013190402c0410400d14100310b440b01843c4044080700c500182d4800c1c0f210401c841034460301d000da41b1243c0700b4800d0410900c807100c040c0c90150300900840c40c05400180000340b03920510818400e070034070241c12a50404084507400000030708250364420315860001d00c2503100301c40c10340b00c0d81a080003074000c1512900455040700e81003a0214145003081c101c1100c1a84000b4451090580c20085080040d00a00280d4894002301a40d05080b480300c2c0c001400302c00202101031484045088240c0003c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 306472464 1250 306471214 306471227
    0x71d0f0a0515190305011d2a04020c010902030a2001030b06161a0103050601030c08060403020705011d09040803060a06050309031909050405090d031109010905060a051204030504030203060f0601 85
    0x1d0b42d08072806200b50701c0303034910311025070190b030000391640d428088005043d07074000c029003038140880e104032200c00107141c401140c2c0e039414001d4036840700c059070400c81d0a850250080d10a03241d00c00700005524240e680045e16081a41004848802ca00003464030f102d441c0e03040f080d04a100070300f000d0142d844108002022441000ca00e54250410006400140801e074a02000e030220507072008062717075849041980d65180300344070032102084180c40100d001311002c510729006c0d6a25800820419040c98010b40d58800801e40d02d400080c01c0504199040d44c5200d5010b000d107010708940c0369241400810301c00c168502d600b140d000d010081090003607400d80081240c85a0150b007850305000500c203d03084401c1c1c103903540035039401400d00040c0450b02c41b02041c2820600d8151700e08000b2144441c06643c110b0040038081404920010b1041003c0e0902c2d0000b03003081040b91501a00d0a244070340c105000c140c040d101034000880209c0c0510441c28100666600000c031181c180754180361040000f00403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 306473714 1250 306472464 306472501
    0x5040308071b030212030c0d0c08091e0a0b091002010b01090909020d08030702010209040c09050102150c0f040806010e060916110a0204062304140612071d0f0a05 71
    0x42d094580010101805126900d00034650040c4205401006206801c1d641e0300020000001402050b0020381514010040c004410790721142050a00c0000300401021015428415060350385c0c44581056a40d5507000300340113000c04140450300c404428040c003117901d0340310b5000b4095a2401c4070b400107903a08040000200c400840d00828806100e00c0800d03155483c43e503004015020210030301079026010340241603101740603241002840c40400c6c086650721954442d460241e0400318504500c0040c02900985c0806075003030562034000c5441e008001d0380d100354031101071070700a5401440340062580001b40c200c04d040300c10601c02d003488a01000d40c82d010218100c24007081200d4000d0a880c02c1c0b0030740038001d400400400000e0743d44c0811a400d50800f00e81d1003021b680114100c3e26034a014802e006000c4000ca44026050351600280141d0f2040341407852802d02c00d04100260b4000c01c014080701c060348490481c5540e06004203864480403000d0301d802005402d200421070ba000c1c291010703040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 306474820 1106 306473714 306473723
    0xe0601090b120c0603071d15070c0b040b040b0702130504110315040b01061412070306060f170718080f010504140703122607020109050d0504030807 65
    0x11603c8020039032580c4410240080b501c51446000383ca000c1020700c2d0082c0b03408454800028105002e40341000da4180c80c0020808204280b4404080c000c0c045032501604050400c15803400d0390082d8090611088030114060003550358400f803130749000500c3c41c001c11040c103060400b640d00901e440041da000e48a0204610010149031040c0c51140350030003010716259082010440b002d404404640a40754018050440e49420006160340140b125840000700c03603180100141008102070100e101f800b40f000010782400c40c0c0340b0f0945c0d60005644c9450444101d03a00c0101848010740e4110140c00e108603100c4001111056002c00d0045018807141c800c00280b105295640f02d00c180002000700c01a801c64044c01400b4211841800a0500320540d00070400c503204201402c0454400c80142e4480d9000014000140030304500c2c680c40c0d18000e480c0608640700c48601d4880c002e070041 = true := by decide +kernel

theorem cover : BRFrame.Cov 306294964 306474820 := by
  have h0 := BRFrame.cov_init 306294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 306294964 ≤ n) (h2 : n < 306474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
