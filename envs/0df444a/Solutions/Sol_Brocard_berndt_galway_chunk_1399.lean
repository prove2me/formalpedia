-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:47:08.480281+00:00
-- url     : https://prove2.me/submissions/6a42afed-c8ac-4d87-af06-697fe6768250

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251438848 ≤ n < 251618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251440098 1250 251438848 251438867
    0x1509030f03080a0624120209060705010207060506010504030b01120206120108010e070905100501050304080d060b0a0224010519051201020a020f0d05030f0a0b0613140d0803011707081e060106 84
    0x20b03030202500440074000c1246e124003c1c04a403a05141c08005a490541341e00d1700811100740075900068540f01c5a00e0040140c039000350500b410130005020500104850030b1949044802410f901901d035a5030340b011600500591120b80c284100720000054000d10642040c60040d81040a0700c8005854044000880b5810b0ba0b01414130a481c01003400b05500400055400902891b003c03801d011241c0022030503039115412044070302d4404907103111a50b404021024a1003149002c6603c5501903106c0340740c202c0d2051213a144500403004020080c414107a00c4c1d90042d1102a1034040f006000c00710290203980102d13008030040c03180781107040c901d4a0104403008003040341d070b854074a0340d191039602010840001e400d4008055403000706010550b6510000c2500703440b490a8412210302d8450956980900e11740d50702e000b040d40100140c00501310703200b10b82c1980c0e1030700b0705010740001074410715141004a40014003580b04045002104c40c42400c0c08400419491003101c129030f0300d6100c1199150304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251441348 1250 251440098 251440139
    0xc0b06010f020d030b030f0a1109010e04052d07060906021005060a090b1512010f06050702152a010e01050c040b160602090d0605040b06010512011509030f03080a06 72
    0x12003520300f60311500c2034001c5402d051000f0b04841e403c1c01c000c10103604040610b0812980101c1c5460000080e0801c1491a401070032415030103030951925884198a50491040800580050078100c01d03c0d502c03001081030800441c6421a44102d03259400039040058900030701004d40308a81811141c03024130f0007540c0c410b02014041c00e503080e140101220103031920038841d580c0420024041c0624000c403601500107500c9010340c1d0052035241103449942c203112034000e01d04114040007501c006d61124140808120410141150b0310a2040307078810a003c41c0d8680042260242c0c078911180700c0054100271a81d6074894000c01c07268481d0b001c842c90741e214510401c80d10301001e01c0910040001c103010400e44d00d020308409031800c0c02c004006000200006000c07030300c0b96600c4003800140064182c1596100c8401e0074807a280050030288500103100501c200d0015070415010760002500c5684a08000d6a01101150031940103240c00740c003014003207a8040505142c482c2c0010790002c411030101c039125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251442598 1250 251441348 251441353
    0x1303150b030a02270906010f090501030305120c0c0a03020307021c350304060e06090c01090b070204140f04060b0a03021305060d1403071a0609070f0c0609030c0b06010f02 75
    0x14426424014440f1985812109400003d1103c0200580c6410701600c02c007171280140c140c40d0b040030204a441d401941000fa88507240400500020b41c010007143e40035101d0300100803295840c0d080d101194801c8408805150040c00c0d2404101600080a814501d100321884406403804801b00d60408804e10f03809005856030402c0d06280401e504854a200803124288062807281907211b801c0c0c4c1d41c0b003960301701c030601c1d034401c2004201da90501100d50080d0a220251601030341e00741c00204001383d940100c6509200c001f44c00421580c990380401a541600040b540c0c6910740303a00f0468403031740300700c40030389005041c221104d5243ca0440201d0058030707401060029007018503108000100383c0201a83e4208401030072800100744003408002d80282d0860046a07103203050b01d0300360136004203a428410104518018481140d84880d501e40d0b02105500d40341140c4413840e0b804071281c61104401806091030601e8001c18076620001498a00340502040c41440c0c66010044503074030019454500140c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251443848 1250 251442598 251442613
    0x5150a051009050904030f030510061211090a060503100e01120602030901140109020a031406310f050f0f040c06033308010c020f0a0314040b1303150b03 67
    0x245015000c0d2101c44056190058903142c507180424900c80007030310103a000c55501906404401e900d80546a0302190f5040e60075080c52408c0405422510400c4506400a0710340078400544801c6005540c0d9038a002084542e0050b0307108406005035000750303407501259620501c045600010f21541d0341c100d034000620540c13a191107868490003500040c3c841d4046540380c10030800c565000820540c003030400214016902c1a804070090304984524650804e91101034042244580c3d800589001c0341400501c0701103c085040309214080b880d9919141da01803612400c0d411945041d13020510a21140b08241200e4459440c403c0f040710049070300404a48101070103000407842a0003020800c2d00070000722188040350000c460f0414000b00e02d000c9040148a0208000b0a00b40502020402540054500209482c03081912507040041c060203008101c1503101e903108400f01110000d02041c0c1780c0d251900300c52510074032856154481030b207244040c08800d540b03ca580d4841c3d580704100040c02441c48 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251445098 1250 251443848 251443859
    0x60c0906131820031b0c0d020d02010b030c0f04050901060b0310090b0604180e030d020c01090b060f060a0f020309040c02010e0d0828020d0e0a0c06030c0f0e030a080409090605150a 79
    0x5d80303403c0c0c012221101024044801c0c00b60040001d00e015003001e4001c1d0918403004000242100c040b154154881d90042c1c01180c1c2d02e072121403203001190340070764010451fa90b41074941d501400c1203501140340b45000100b08001d12400b504d455054840c41ea105000c8201040100285409140a80f411f468441c4c001603400c00c403d9031045805000750b1050343e0618500a80030400c0740c00c000c0641136240d44500030007081015810784c0c150300402c110362641100c00301001041407805080c00d0402409880c441200c04180200280c0d01d44c000700178014090140b64000c028044d018000503221144900e0110041060043c40035a1041c4080131403121111161404018600504410350306429802c00c41540c810702c0b1806851040a1000c0c02011009034610300800c1901c03490344044109850000514a8194000307000020b020281c41c2c0900c80d0700c414000a0304014407004c0082604400042c00105000b1a030001a0018042c40b000c05c071a03607400d4906501064264100c5a00142d40d0909204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251446348 1250 251445098 251445121
    0x507380a1a0127060c0b01051c120215070306080d030c050a05070c090609060f12080301140619021e01180305070c120602071106070203060c090613182003 68
    0xf950450a050840901d0304004807291010140d0098400107241c1000e000c2031144203035001e03004000544040394440e0524030340404200c2e0750a40200b0280003041d0400c00d140c420054030010200d07511105420381410407000d4002e00c154481e12545003c1c0035401200035010f841034201c032820640740c540c07074180c0070141101c00f03030310516044070509410007000c500308601d4424400545046c02d000904541000690303590701ca541e62107110a40300040c054070024541c0300c103480c1162194200640d81501c8070001840ca800b441c001280050031854182046690014401c1440443d20340150344108604992900ba90000c0e0607010040030003240300c2d40001d2007000108280c43c0517405001482e40c80e0100b5584a8081c01e4003914a1a0042050003d12000030325180c40d200d811281d02c1c1c90a03c440d40429210706d40146000c00c050f80200d07c8011030f40b00c61080f02c04c50f002021408401545a000f071000c81140e0b0308031104924507041c580086000990604015036010003052800c0d695151070520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251447598 1250 251446348 251446367
    0x21201060b1b0d083d03030809030703050909130f030c030e0a080a110105090d1a0f13060e120d0603150207080d2f09010e040515010507380a1a01 64
    0x2e004042074120002e20795000d80313422417828025480483c0030b861818000c084810107000d602c250313081080100c000a8002d0200c8009a90075185103850b0b980b4500203aa03240c03075004026007080401e52001c4d0405a00824a00c00107221f42c030f602002543da0001d01c41c52104902858489030f1140c5102c501144c0201c92481501740c05243c480e01d00240d02c400b00f0f480c46801d51049810001d01c80038403084101610f030095002d0b104251008042c5491034010320814100c2502a19980d610085210350381030030b0100e2a41c3d025100545641c60040800250060005100c02e0740c01188081030700441071784d5402143e281d150031507031103820501010390350801002a40807482071040d00c80c0340c0b18415041e40b225448020aa50b00070f41d110141c2d40e00140c02c0401c40c40c10381d48254500810031110100324980d406010200307103001a12100f4524200400c0c1003031010b0510f042c12050051000c0d6070480b02c08640e2203912982410b090385450440200780e0349420000305840c0b8000c0600b0911354810f68580 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251448848 1250 251447598 251447641
    0x5010602060702100515100c0618021003050405070e0c040807050909032a0114060405062407030306050a0b0301060f08040f0209040305120c031006140d0207021201060b1b0d08 77
    0x144941b01e000190340c4200003d842008220b8012034002030200b6440f56a800c0001025580408601540080c1107075914000440034550782d2404641032060800080307000d402c004200c20f00303606240b07480c4007458100f84201486441003017400b007101d04107080d2a81c050849040194103160b118590203190400281151012140c04490090003e10034000c2d0310408100c0031201c1c2142c1031201c01e000a458004150a001e02c40d500d26003c000c0606a5000e001d03080000540f50f1112a80c0c40d0840140c405a0721069100408003404920035120b440114121451501d030703030400c1451840c040d29010011100a0f081242ca650b4040140c01c11071182540203110b8a051481c05c009101842e60805043d200d450781c5101c003008000300c4100301c60941010b00000d060450101d03100510307100c6240700d1600b550004503008505a011915a02d17400a41c0309d030344000074000d203602c400c0190843d4204000e40341a12040e9061010306100200e80c084102c4603641e240003039651403110401c0704540181c0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251450098 1250 251448848 251448871
    0x110c0709060f0531050f060102031309152606100305120a0c06020a0e03071a040b0706141f051f080405030d0c0203040801050f0c041203020715080a050106020607021005 74
    0x20182003407044841301c14068041c54000500303041c2128805d11034140181410f0540d0310801c42441d0080201181104403194440c0c0850800030000c103510284203141d01c0301c515480c0724504503851540003a6106400002041141c01170754a5400d83c0e01d6800341844064155002042c600c1d0712002c14030004c0c12305407801e00b000550240c0540d00c040403648501d041e40e0002c6c061403c440c1c410319040c01b01d00000c18034001c2c04500010340a416540394482d070f114020703900d032001404104106003500100607160442c0d00080891500c0903a5502c4846d14980403150441110720100c0c241c50010325456415034100e00c8070400c00102c200035948140f01600a45081c0b20501c11a2040e2606002e00090304e01d181c0e001d9500c80346803640c0c00c0d09580c0050206030b0a580e42900708220900300d0000e450488000024256a02a9a06003070342040207a4000e50700c0f400842004d02e6080da00000414020b403142203007080f042e03a1301d0008036180d0750150b440d40300603040394002031101042c0d50091030300091409603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251451348 1250 251450098 251450149
    0x70807020f090901090201030b03010c050d05091c12050a110403061505030d030606110703120c03051c0507201e031201060c0311190b0405030d110c0709060f05 70
    0x2c0d805010480d0414210b80d1989403803004c41d6807601a0810034031050f0003d101091000a000d800d601414200c40c40403a51500002e2001408101c001050071440005000c0481603d4009100e0001400c4400c1050b00b0000031800c2c110440c41134119100604103001e04103070031076851340b01602e440004000c005c022007a002c5056501401103580720000c43e20001585803405102a281e400b0b1421241a00d0f0855501080890501801e4079000c11580c0380c54100d80c801840d00341c0b00782c0941110880c8030007260a00c041821100da000c540034208649440444031a981d0044030300790006101c545c1d864206d0016908810b03a4040501d4015a02009480c00c15200208403101801e0990150f000920020140024541c0001100490002803000b411080081a0044000754411700e0000c2c01c08042000080c00e10400b80103581d01c004540d02e0a01c081681031440703807125040003003c0714541c0900d0b030002840c200644981801c8400703400041d10407902c0d05041240c043d042600304c2c081e244550b81c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251452598 1250 251451348 251451379
    0xc0306030c041d1b03060406021c0501080106061704110402030c040b07050a14060114060d02091e0a06050c0c06070303140a0905010605010c02090402210a08030f10050607080702 78
    0x41d4610181400414240500d96400704a01d00030900b840f0f0f01c40d4070300000d50b003800360714040341c6da81c0c0c041d40240c030269441502e0711702060400210100c0c840c402d860000041681d990640003c000c941031503440148c90a00b504859a4010701a10000d154154403622801c0314100354024540c00a070300c02c031442c00d1540e10000f041d9664444d4200b225a5041003203400d00f0040490002c02c0d0031408080140650760500c81c0c074a51000c420142c25110b01008192000c1c150a01d170101c84403100090704c0d021920a5410101480034200342041d481446400c2c00400e83c50f101d141501d0700b003810071000381a07034508030041c405540c2c01208103404040e03d401c443c08040c1001c500c02c03801911540c0000807003105a041c42401c540603a00103504000210440740090390b42d850314a90090740403201080c0803054811003210440030907428088074052040d500d000c1c000c0f40c0c409503200c3d040c1070806800b50b80e101d10650032100c20a0080903071140c400e110303101c00700781ea40024005551001d03000407108803144c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251453848 1250 251452598 251452601
    0x1d0703030302030f010f0e0a0b0a0f060201360305030a0609020c061603020702010f030e0106082d0c010c0b0403020708070f150c0b1321090509010b030601080c0306030c04 75
    0x25001a80425000003e128610412101c41c42c010503086044090741403d01403d035041420103008030030181e03107444820700c446d0b85114a038002846d1b2102601030040d90b60707802a019082d11501c009140d11050080216a40c00d41c0900208c0e400d90384214500b00172540e4140c030320360400380c41038981681d134a0000c00c40c00d00700c3c070080200e01140c800925151400340607514003852040c02070b004050040c014500140d8210354401c101c000c0c1401e000c41c480c1d610b24902c1b030040100d980a51302e10300c030300e070706000d080c403408101001d81d001860010108540d0100440d90b03030748801c080c400e0001c0e8004007648046558503210b10b0300300384248180c8010640d2911a580703459286e0700320500c60300c04d0400c10415480761010310215a0b101e42000d030041c10154070380c808031000091015900702980c860400400000c100008002e80d919003c90130042c44011006003030404a0080c140201700f00c800100300d540602c000c0c0e030b101c0c0005a4990b852655410000c1d00d941c1c001510158042c8039081c092221666103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251455098 1250 251453848 251453863
    0x30905030714060609011e0504021b060c090f030c060409021b0607020d030e010b011e03060306050a020403050d08091b1c060509010b0a05030a08160f051516121d 71
    0x42802803815003059001c01c00d6011060380f0140c403401404d003134040030310a51110741307023100e404860040c1c82d950a4600d0401c2c1c1c501e81c3d05903c16500a40c01001004031080006d8800c0441c10740381d0b0001031810005140d540d41c140d0340001d50100b810b0104120241d43c903001040000644a14104106a051310b558a0031800341c0381600035800070030b8144202a0306200c1c600801c20304900074030004407102e001134038141c0a0b9031440c07034034050341440c141c10354020b400050046a019004002c54980109080000e4001d4001100c20380102c0d400203482c0752044003520b00618081c0041d00c001003d116211800012900804d5041a86010b0300700501d00e0000c1423090b01c3d0b0042d54040b91914220181508490381c9030007040c4200f00302c01c0248a15100003810307000700f07030f4004882652003003ca207400031200a030303d03402840c586003151454204400420440500d9010075244112502c1d61880d01c815940074082820000714180081c1082c08c60541109451030706d040c2d01c8004440d9010b2007541480d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251456348 1250 251455098 251455133
    0xe0403020303160302190f11120d0e0304060503010902030406150801020910030e030915090d080705060a060506030402100309050303090318030c010c080c0f19030f1404060309050307 80
    0x1c0401000980d504040000c80050307040c1c90110f140020481d94982104c0c1c0e50030b04101000700722541010721038001d10f90003030211241002c40d008900340d0480260b441d44907500b0f032021035007000c40c500c401102c0001540d003601d0003502c03407034150b03070805e072010b00290001070003500c1d01512050816103d00300c0e600380380f010300b4004001580e2144840f06100c101c3e050802e4050805240022030810254003009032080042e00311285e005002c078020682c2903601804034900d43c0305003805448010480d640b80100207440c402c40c01e07a0700d07642c3c0303000d0108200c68a074491241c000c0300c1000011b0040c85c11448000e46071083c3d0a0004958010303031500ca01e5904210340c603d80640c00000d0f05004100118012030010804900400400b00380c4400200f01188034840288609408600070740c00c0c000c01d018001c42e404030081110401d40c40341720a1009030030141c4060b00815010f28501081500c42c2c00900b48110130075603194030f42850450128014005500107681500050121400140061040b00c0e80d890 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251457598 1250 251456348 251456353
    0x1403040807020d081810050d0c1e18210f030513030b0a0b060301050d0f1e030915020f0d1116030c060905030a03020601030b100905040c0e01050402040308030606130e040302 76
    0x101041402007821021454071b2283e030315030304081c0080c0e90000c111001ca0607846404142d40d5444032040d110809002d0b030f01ca0705081c2004800c50010b07400940d504d0154803c0031248500755aa50035951840001d010b8100c81c403081800000129030750490042641d84245017040c90182040034036600042c01d50070446081c401c643c1444120180c0d40140c10302c0040440c3d600d8515450b00380095440a6003007001088034001c0d030013620500400428800c644029444000302d0030321107140c004c1009110b80103600c5500201e084040c3c1e514400511845035240010003481013403000701d400c0d20b0031030034052160094400c0d80480b40003051040038803002584249605500f40d03040c40000340910b005504801c0c000d030301502d44d1102090b4002080c5045075040240301c207658039894601d4200e14000c0c1c12882e03649080506010401c030016010364121808000c2c042126603c0e501004240c1c4254400644808402c0c00801d6007860854020007503031550100703a09043e59110354402c1c61000071142600583c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251458848 1250 251457598 251457607
    0x1906080c072907180b040513110f03040308070c23010b0d03030f05060102240a021209060f0106140403030311090a0e07030b040603020a090b010e06040915080a031403040807020d08 79
    0x390009003607035804c2d12040c0041d480718203040058140c0e005038402d061054080841f01412040d555014141d00124507500d02e41d201c00890038440a035006480407000200030800003004207100d444211800c65001d40d28000e4070007a22200312103806e903000b1840361035588070114110383d9240200d403078109101742c0780498001c142e07a003040300300c0b5030003080d071415500030200c410317000c0040c0046025070b694020000c13003140c0c503000c460600a00601104c08950304250092020381c06002401c0c601c654200a11018107a0300d0315403c03075a0ba945202e10920f02d060921090002074080c6d00a202920600008242070003031140001d511481c903036015010031800402404110f9905000300040003d0507a010300c10f40d07107158003083c025403030b07881040140d0741da81c80c00c4401c41c0c2c800e0308506090b000c0188499200c544400c00b8100812008040400a00c282d907000602e181d00490a200000c1c3c240e150109007802c03000f0740e030361a603000500899014404004040c0181e0300e004411042c030b8059440c1c961207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251460098 1250 251458848 251458861
    0x4030503150316030c090b0102060402060706091b150f050306063f09210d0f11030910050903090405180604050c090106021f0b010c0203070308091906080c0729 70
    0x4900c060b00300c3c2c00941d047c070a0001c881d0341c00182030768001e641510665501c024034140701000308203140c402459071451004d080494030348003581c4015a101d0311000b2001100c4584217031100c501c480c1c0044042101440001d0861030030001070811412020311001c0301400050b00e840301801441c4401659000e180d040c140c1c800d070300070492540024050024074030b040008510b190000785e00d181015000d44000303040201a11690840070500910550600c0710541580c012440d40d00101c404000901c10000c002d00315001c1d5000315402800c44d00095490070751a40c061001408008206400281140b4802d401c01d06041141510a5008038050030f60f000c00360040000b07080040c2e0151045503c070801041800b61019030183c14180307a00400035080c03e140c00180e4031241540070107035042c02911030000c2440760301d10042140040072038078821100a881c85e0345407401014043c1c540040c2c89080001e602041040041501c1402180a9924540800c9072030140040d08044441e9041403201800f4a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 251461348 1250 251460098 251460113
    0x60203041a0415050415090f05060a0b09041106040b0f0301050411040602102a0e09060105070c0603200c0d09150e06090411040602030307260403050315031603 70
    0x500e44914a490841d9040c6074a80ea007201c441001e401806540c1c1e180420b04010f910802070082c070700464002d100140480c106a05c00d444503040590b000d0040000084806009206011a81d80300800884060b1100e8a860002200031003086070807400c02c22002c01c0241945020b4010a407400c0030095507981040240800d8401030840100304090510062040c0390b00814417681501000c0c00010b0745946184100003503021240039444010460000c4403075566100748004000c0300b058072000700c10740b06d02004455521070301d10041d010700c041c40c406100b06442908400400b034400b40684030f40c5100030a07a0711980c1e1007000002c2d09580316103058042a42c2042004000b881104128000000030f10000791080c02803003916031103841c001652070600c0e652540f0881c01200d00001c19a16151182e80207962a03100b9200b2401242c46061084c0c1d030200c4050901a001810000069050301c4641e020f07201d60304040c124460340b020b080201503072030703c040003c50b8490400d50442c03650740d0b165007009030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 251462598 1250 251461348 251461373
    0x2040b031009231303020c09070f080f040c060c17030c0c0c0f060a11030f030114150c0a0f081909091a03070e04030c0b070807090602030a0212030a0e0a06020304 71
    0x1410f00f002e58502e5480101d0054001d540203141d00300458145040e0300d0304a00b0f000c5004507580d880880c1c5000e10420690000022842d046140c50341d44032030301d505d0b0041503280011100100f030022b9181091254500c14020410058480d07680e1008815420351007160a41003240c20102254011801240e100c800b040314801c20380c016505003591100c040b010880b80d104032044c8909104041a104800c05000c20840b01881d1051502c0d5403203586a0403c138440d02d0031a500540306490004c004c1c40c606000a00b241c40d00402000102084881c0382c0e6a4214400d540c83d0070350300c52009100010180e007404064400308071882d91401c2d03a407400c2040320000c84103d40c240341482003c1880080841d140028240283c1c0c281c2e54103801c80382d54034541154207400e41c10000b4007021f4201d05006100d50081a4140520020349501c010681c650380102d90742e00500d1a41c400680c002001c2040c01d4181d09e00940e003024103e500810a00d038400070561500d0302450045440c0c44d0f001003000140304514103441e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 251463848 1250 251462598 251462621
    0x803090a05040c12020a090302030111032505030f061302071214040803070f061803110c040905031602130c080105150301060503010905101214070806090d0c02030102040b031009 78
    0x200902003c4010092020608002e84c1030640e0340068a1200d40340100448402154010300904c803e170703600e9030301000d1900151102d00740021881c0742c5500c1d842c3c40710700c090796000d01a5074940c25940c0c1c0120301441880054002a0000c1c055030b04001c201c0340b80d0000705110340c00341845400d90400c10400406c00300300003170501306094007071100b0322070084003200700e800158120200100d050f40f14100342c1c009240340382c080d0380d40101c5018030800309a045408003001122050a03a1100001c1400388010740300700302c000401c10f810800080c195002c8110b0801449400940f0381903401011400300811204c00e0270104021401a00041083c0d1910035a480707aa2000c1c80f00a501759454208040c1c00e074017044c020103500c00c0d202d0b0005640200103071407400c01003c0000f5240841002801d0828440e04031000c200711320b024520006c40d00030800159203005044040041411b100e0b02501140d00c50b0710580308a9065400308000030303d00e09070102440c042c148106505d0304c16032800304040304036080c04101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 251465098 1250 251463848 251463851
    0x609060606040e04111801230108071b02130b030106080307080a1b0203010c030507031d0616090905010f2d061214070201020c0d18030212160803090a0504 68
    0x300a03890321540290340031280d01da01d00b02c280c0d4689103002d541800c50655100c4d0011011100344010040c0032001c0c03412911801c8440c0c05240c03d4110f00c4100f0102807680031b000c146510040340c1c1e0b2500c01c1c0881005190f22503c610081407003a400200c20800025080102580701d4000c0c07003c602d001c0c81500d0003880498000c500e810b03031554544400d806400c12010a1000821040b803400c14141c060414569008008101200700740c48058020581644c41c1030010b85040c4070407256031301a40203a4403514243e070042c4032a9a84103000d88030710141015207010004800c0c00000c000c0f0a50041e117000e0141c2c07888251810b030404d62410300140020680c0300d48505000c00c4e00141c0c0b096100c561341591160725080d1804444c0d10f03210005004160100307941d04509108201565074194050540345e80d404040d82c0303070194040400c03508140031107400001c03101107800030001450005000600d1720300f00000e98501c0d60030558121851030840d03105420b6030704005207001c060714114031402e0252404450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 251466348 1250 251465098 251465101
    0xc0f234f1505030907120b22050703021003020c01020d06060206100b03010e130b04051b0d0209130f020d030c15020f03070f090b18030c010e060d09030c08040b0a02060906 75
    0x1e003003803214507a0706010520030000081840d00b5414000c1d00041d00070064101c41414a5191840c4445001c5601c0481c0101032100180c0c0301e041c0d400e00401594004006203031450864007004000d10104500c40c0915600b00900b41c2c00c100c082c005491001e00200c070005070180780010190070043d0041158682c2c8180c4030007400b0792030800d01600d042d100d0604030100d142d5699160203036041505400038201f03040550400c02001000070b620034201403a070315841390200503c414000f4801204500039840034901e000605804c1242044c150364600816440481d18800c0c0c001c03848520700c14030150009040b9094420920030078468051080c41240070461034006043c22501c0c50340005081f4004004550312402807143c411401c070703005001403460b82580c851000300c4528a081490359003601038055101c0c080301ca9801114407080e21303180a803c05281c00d034105004c5c00100032a0108500380030040c07907554040b80c1c48d00c002d80040c0521100b4299100607400c4040d1030800002c00035002a0310810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 251467598 1250 251466348 251466359
    0x30c0901030611040315051f050a05130906020403030504030b1f0509060103090818040e01020307020a0803094204020a0b07150e010c0f234f 62
    0x1022504481d00300200180c060b03924401c07a0b0642c81240c2c800b50841c0040300c3d60f03c44040003544500d010b0a0350008200c0065409041d18860340d07a148a0940d018050003030800140c2084d0100210241e010f501c00100b000455580b03508030380141d00b00b030300001d03400f080a00400c01c001b540760b60042c00007113240faa00c0c095601e0846031200e1030b001d000d00440d4018040752059000e9002240c1d032a0348110700503103450900003840361444c0c414410030300c00e900744150356542110604c2142d0041c24240d0250206412944680c4056807000d412021035103e40f80c0141c806002d9461350001030794410340d0050210410300f60000a9228030405514001c6201091000580c2c44070710241c11100c90303500813919502c85041680707401d0160010080000d007001c0d0041900041940810402c150548504038919860f800880d41d11020811141a9082400f06110f010407402c0c042c042e100b02c1141c100b100b8026803130310580c0380585480060b500c004045002048000291441204504036050361441d140c50710 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 251468848 1250 251467598 251467609
    0x10c020d1e0c050109120e0310091a07090e0403020102040306060506030708070f030f06330e0402070c08240a0e03070f02010207030506010b18010302180906040f0905100b030c 77
    0x1810341c20500000ca410602000000c2d08042125500100d4201040502e030300040c0000c0c2c41c40700c20622a0081811030903211040340303d0a44c41c00c0c3c0007010b40e2a50629234a42080d510000b4007200180441400002080009151514840d921960000d03031601d156240440613212642c0005202e0304051040004040d4070a0015034001010314007146a43c0c2c000b0030030750081c40001d81c040c03695424102c0c0451806500d09003542020400741c4803019035801007803911600074102d030f11800000c0f6030070072140d001d00d800e4024149450242e400c40000a90b07500327407030b40ba02504044107446140070300043c42101c10421035099000520030000c1c460358007102d00d0350b0b40300e10806800420882e4090142c03015a4400c0140740c2c003465014045800c1540c41c0d000c0c0c46481d41128031150200000900a02100d512a00a03030718141c4a032015059040413907420403041d814010070450304180d881c41300c14019101401000d1145008070054035600c20300ca0084000c0e2860034030698060382c000c000301d81281d12803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 251470098 1250 251468848 251468897
    0x209030712080d110d0c0207140402161202030d0501080a1112030d02130e07020604110a0e010303230d0f0f2a050c010504110f01080603030f090a0b040305010c020d 72
    0x3c1e08000440c040c50901c002e11600581c152150602c0c034002030400c0d2290000b41d041d0a40700490300303490300000e0640411041c3d108170f4102c40c400da010502680d000441d40b410311103942d9001d00651f410101c0c903030f15100440d8001d03400b003d0250722800003c800d0090b24001003c0070201903c98606c04081044030a07500d206481c101844590b00050b00640c040342d860803800a802c26100c841c4050920440c0290f075542d041d00c0030381d000700c1300c801070f10454905024001d04a520414900c0050703031070360314140c40e40601c7d0700442c23407000d6400d10388602c0c85c40740c20010981808204400920400c51943c201d04640b803001e139010b080fa1400000160f007017031020308028501b00644204842c03a5444130700301d0b2907008030000804590308243c24001000104d0520903501c031f4095880d107030081c60b82801160300e50390070b0b204070f60981c00402940343d81d000c5040040901000180c642013400742d4407101d40c02e25503c80c1d401550580d654500198950b039051040c040c1300003640c0380c000014242945005003c00c01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 251471348 1250 251470098 251470117
    0x30c0e01021c141b010606080a0603030e01080601030212010b0a0f1106040204090c0305070e040209060607170904060807170d0207150815040203090a0203010f0c0e090c070213020903071208 83
    0x18442002d440704a8400c890080c50b000100030003800d0b0404209000c2c0025020b1f241c0403600d2140040ea85403070314840c00c81125090b54801104490030f00040d15010000341101d03040580800001210b45008101c0a0091200301c0c400c6640c2c6040785402424000465290001c008055040426468000480b00d411580468000800041626160510603005d600042c024080c144000521591108101744164020740d0648004c0d42c60104002940c4658000200182e07010741030b080c403512210000d8002c0c0d40c4080d01c0011059180e040240c5800b0483e03000810f0780560307416580d2903850500a10358150f102d4002045007608103010141c40307000039060002040411400284052090401c881442001801c11981c90501980300c584410420b2000e074003e40c2070002171040e01d403080c881c6c1c0c0400512543c5000c0072042c81c0d4204040c04402500382030381440140400400350781c6243c2040750342c0245241c01a581c2c00210141030511200d41c6c010011845c0311400c43d0b001c5031503141121803840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 251472598 1250 251471348 251471357
    0x6020f0c0d1202070f080a02040605090f040f0206040503070308070203070603090f03030f02090a03050a06060f1206020f09120303040605060607080307030b1f020109061104150c03020319030c0e01021c 88
    0x1c0350460104c0c501042d50344140d03c0814070302d0001920001c040341c1c40c1c0900780250750070300005071220705200d45c4d0304065070f07108042c7c3c1604001a01003103017034061980c0c1a1006100d5032405540d000000e00d0010141c0064400354000290f620451804000b210018102c5041c2031250a078540c41c0d0701c0d40c04050328005420f16450714840c4072011520b0b4101c0c1c0ea80c00c070040440c00440d4903802e0041c4d544507195007c48030b06203402c3c4046000c42e445034581d000c88050200d000b44000491b0b885c08060340020095a01d07a4000703102295007036680c02e1f440d0004961707110040d1b8032440c02d0308020041c6c501c0900054000d5404004c0907010844000803071b64010942c0c140411041500130114600050031616131601c000e1400c10b5080d440c0c0d040d005080000c0c0241e500307105255003c05012940c0c81588550001102c01ca0b1030740c235015004036916401c56000b401964103003c440e84444002c1010b94846100103039550381404000394025a180844039070a1004290b860322030148501c401c21400c001d5014071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 251473848 1250 251472598 251472623
    0xf05100315020c0105010e011707180e01020c0604030c051b010c122123010807051507141e0c010806040e2508010c050c1c050903010c0906020f0c0d 65
    0x1c09141c040391126080280200059a9250383c2801c00100038007851083d00740c072205950301742000084100c160384100420140f0a01d007a00d2200081c40400030980c001d540074403540300440020300201d48182d011f900c4080300b07181203140550070110744080340304140c20010300d0b000007139a2100da10183c080d404452404140032002040d1811030b00407910b48003061007c00400503030030f01e907001f0394003903000011000910a80d4402d03c21030002c0034003402c2c026500040c0b04101c103180200c0800041d0140b4880e15180c82d03c19280ca582c104000f891114980d0f0001d0315030341e41596004c1900c03005004200140940d00e6510380002c080b40030107889580300c2c40d202e005250405e2000d01c815000c0707071aa80c8a00d40c0070301d141c400055968900740710750612946002e00304009240035408584946501802a000d00c8a554584241984000c640d100030054180401e4200da2402d1103002c0640b4030baa20f444d903000e45000ca00a10741030064490200c5038125140141c3c0d07076213030100f526058541c4240501201c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 251475098 1250 251473848 251473883
    0x21f051206060c0f0a060b04060302032109060301030309030b0106140706050c04171b01020705241606050f01050a0b0a0518030d180905100e09101a040f051003 70
    0x443c0076110000d44140078803a004048080c0004443d14551320501c0240114562681000100c4195101c0070750580c001c0c03041d840d0b5241007801d100e480c4032010392b9030b5800e083c0140c0114107207400903001117010416880e0140b007030250a011050042c241c0b8940801381c0c0d00000e00b05040b034003681c44001c014940b18070202e60103102c03045c140c6001c0c1c85d00c081842d4070707103c00c040c950b50f5440300007001d440742d005a20f450301c1044d40702081034015141c02134600d002d80d100c001640740d41041e48210408155909210803011380242009040c6403d0149001003031a041210160000b91010b07404540b00702401c80c4104003540300c10341911026122420080d4440454134a20b10340684000512603140c040d0000411380c1607040701c0001100303031071492140240f07a1551484800c944003513640c0700d0b994150314010800480f45c114881c0d804030b50581601c485102512000c03094450001d842c5000029542c41000b0b1418070340310300c2c0c009024220080c8094201448100302502040c000030300b0b02d09000c2c1c0c24000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 251476348 1250 251475098 251475109
    0x3040f0501051804020a050d0516050a081b0316020d020c01020c100201150f030b0705090f042703030506011b0b15060f2a06040b0606090a0b0c010207021f051206 71
    0x80f80c680240c010343d560038150b04001c0c065801011075400d42072620001c0f40901c0032201c2d400000350001e880c2e1500d00318444200b5648154010400701a5419a0400004a80182c2c0280d405181c41941c00f20303140c14003004c00703802e10309010100c1d400c55010440c60b030440c0ea030002d8442c81c850019226480e0800170040202c0c0500007100002c00062400c40d4006190501c079500074040743c3c051905a405a03c2d40c0381d044683d485140d8005612070f2150400c12646c0c17a06a00401089003004059100d0b6981316100e0540401c41c424140d0103e5541c800b08585c658221000098004c109645050498543e5807440c1011074080c2005001c804a050110f600b40c0301d0104031000300e8203040c446507c070310103010b2014103002c03041c4803d01c411024060722044144006a102d00643e13225036100340c5a5a44002d000498002d070b0055035016034440c42c0002c0c1118014000d00416495600241c2d031120350740180a4150b0440044015000b40403586660403903014065501c02c0c0141e4042c208140c441900007907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 251477598 1250 251476348 251476387
    0xf080d060e271908090307050109121e02120703020a1e15021905030c010b04060b030a050402150c1b030a17070614070807030b221508011409070803040f050105 70
    0xc210040c03d0306550700748240b083c0a05a02401103084800032601d40c0c004450a15040c454129892015001d0000040741c2001400f24409044035507914110301d80c00203400308507001002e0700b082c0c11040741401503080201c01d950143c140d8140107441ca120000001c50740446620840d1290001d9482d200a071038401d100e1160145041d0280210440040c1060340d26980103540008a56113040400000d608041c00380340c5c02c581075941c3c0503003565a5240a440a40401001268442014022090400f080d280034003814200c800c010714050105141100c000d1030304000f1103100e6407202e0100c80002d004220b02d428801d103042806611a1210300c1c0103070203440500515002208094104118240e110000360300c40c09035a03500f1b00c08180c0c10418019020140402044a8031400e0140c2c000c0b04541d4010805001090442c06030142e643c442880c00c440405482c0c400030075580051003003021082041e03102030900030024510b01071800b031405a0003002841002d05201d8042007004c0c6609a104122 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 251478848 1250 251477598 251477623
    0xb0429010c0f050a14060901180807020a090e030414030f0d141303030503070f090e010501050a12060303030615081003021201091a061804050c0f030a0f080d060e27 72
    0x3d41200b90301d171501c1d2050100103514058103209190014032541e0341401040c0c0b48021068642c1c0080710340d521641581d504c030000c140d8018013095800146114180b280400c0340c04804061a00d55090070502482024031402039842588100318041c0c042d030021419140c2000107082071a40c101c03c55800d95058000e1112014904240940000902d500301000790301c10301440e59280919420803805480005141c011480b40c4244900140955405000109188542e81c20844082c0c1e5100800f10150b41041e081200081e440703600c2000101c00c000180f02503100e60742064180351903c290301d064031890920001e8031851100c4083d5502c06001e5012140c1650894144030404030b011484031801142525007601484201424484a140381b0003901d01683d4000080c08004000000300601026240030050345805591030010000b8904ea1072800a039129400d0143c0703c2c1d050b1182c01c0211a199440b90503035204550410915520090030000e400c4104a101041c008000e80c800d031a000450201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 251480098 1250 251478848 251478853
    0x19020c0f091909110907050c071e0801090501150b190503040326040506070201090c051002010204051003061409070e010804060615020c120706022e0501090b0429010c0f05 75
    0x3a5018009104d08140c410601076506051a850b4084c0403201c40c0b007105038015640d04842014010315124090300101c01d006c00d4a0700c150740c1d450b06442c3d4212000c10790200c6151b0741d11028040c001051000480007800103441450038a40c04020908040c4042d015010400000200250070076010341d80081110407400c0e03520001c095240102030551100b500d00351964400d02c0009560540b050260604003070f805a48070f82941d01e09400d0103001019001000259502800003184503200d00c01510181c030015039001c16070074a082401200380c041411060700520303040040110040c0c1000e000550048203181c480c2c595566810000000c00d1b40740c210041d0352040d552681c18131540010b50662554041769446040060801015552140d030710909000d608880712104000e41c505e001c0714200c001144400c412075610200d9a81186c4090300991001d923a900d20708051030409100f10700000f98006100c5140340c01c80b00c04085070f0301a8554581c100010b96071000d0030080002240300e41594003108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 251481348 1250 251480098 251480111
    0x20408100615030209010c061d01060e07092c0412080112030c02060325053c160606061e020c0303160f020a03080a080901090305040909050f0f0319020c0f0919 70
    0x48603881227420f90b02205c540c280741d008503c240c1e200e11000d0089256445018143d46412105503d10741d1100f100d00000c5000350780151500511840c55109900ca150817150201c441030016000c00f10682019441c030801c1743c0c0d0b0300002604803d1007240e541d01160020f840382e45e2040107800d544c5004000d00c0082507580c6503030500c00c0c1c0210103406c5480b00d480108198075241c885500002e480c442e00d13208041c2003d03a2303840302c11450200800c4c001100c0d4180f82100c1081d500c4a0042c0c0b04070758440300c00141c01400e440141001d500b0030031807000d058405031040001d1540001e54038003915526840c81464504200100860019402a10b40e8040d1160480940d213050101d011307000303030f8a40c40116000300005901e2410611a101d0070036490b0310381a0500c0e0400074024010300044008446038030a910301144000000c208144002d680c401c002c5680b01c9000001d140c424072035075141c8055602c5008200e07540d5454140e400e135002c10580d086140d03036480303042500b00c10841c04803c070315840c900381d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 251482598 1250 251481348 251481371
    0x403020f15010608280204050a1a03040201030902010c1e020f060a0e01050a0e040f060302180108030409020d021209060106030c03020408031e04030b040605090c0a050d151b03020408100615030209010c06 89
    0x10043c00c225801150189c50141c0d07505010f04030101000410501e03482c04000180056001c1e501c0703981c500d4010300d0f01c215035407101d5640042c0d030400c030401c5501031800d80d10b40703404611b080e00390400d264409441007414856641c0d0041c01c04c94034503940605201c404188090890b10070f888044605d01c008005002c0d002c020200a0b00902c05804141d00444041c5e01440d0b104001d010740c1030484046e90021864030f407801c07151100942240c045081c2c20317030b001c20034000520a565205800307003480b44090300b200d516141001c0c04540480714140305050050104015006020059a060f0a9040050301c92502c031800d01011902c10340e0001403205183c0c80c01d1100380314080d40305a114001e000d0441e040707181d6600070000701c40003a104040d031101080c424400000c08442c8403000d070300300c070010104030b50162002080700a618181203c0001781d000c502005003000421000c03944940b0400104002030400c5a109038110282001c01c0c24950009076000380d070b0b4854044ea4101c1500701c80b04010482481 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 251483848 1250 251482598 251482601
    0x70f03020c031e0105070207060503070807030207020414160216060e13060b071a06090408070c0807060c050c0409030804021e04020d02070213050709090e01060b0705060403020f1501060828 83
    0x40f001090300b58030303050000f40c510f400015810141c03010354480c05d04581e00c40a0032640c0c441c00518000c201070b002c1c420500142c45502075580401d602c52007503031062410410302c256660083c0f0034001150b005010a5500e50b56082804082c3c41e29441c0c01c108090a903404902a42c41c0d0260b080b02c3c0500e04200059205028005040c585205031000d00008000000000380e528055401941c001e02e41000f00d00058590002040c490b4465400c490342e65a858810a040807020f40c02640400c00300c000d10400c000e4140442c0c1008d880c00c6404201c83c45081d10300801461003b8402070044640088100a20041400c1034000c410010029541c90901c0c407000000380d040240103d0040011441c500b00410b410701415114940b1540c070214001e00e4400d814001e441c2030050300ca000d5580d2600460342c41007200c02040c0c0b00b8040e2005014a04141c80c000340351104544101e45141c0040403204400a101c1c1c00301d81c1107aa551030031f1903445c3c42d9509001c20100014010380c03000044041c0f0070750422002d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 251485098 1250 251483848 251483893
    0x90e07031d1b030d09030510050603160605090a08010207170703021c0f080f13080a090906030c1d09030f18101d0609030a0821010305010207150b0303070f03020c03 72
    0x3d60554040a5114030709a03140071481c00005d0440d0004400303500300346002d60000e640190018111131880980c041c014040301026000640090f20002d2070000340c4c140b00c8403030070081510200071881d0800d01d40f1080c800d014080b400c01220040000c0000901d071080002c5880d0200150300e009603014201307400303040b80b00380b0722052003c684640d000be0204001481c1841c0300b44070341402172000a946503504111030b4001155142804101c02000c9403841161246401440c481c3c0c5801071070030b00344820814a202c501c4a0301d8000141141002501100402600d642c005103220711600c40c44000d403003880001041e9405904113541c1d4160100342a0301a0750065180c094100c0c07914180015014006540700c1d001101380c0641c0301c0c0038841c0010340440000d0803040c0c4580410f054003060506031051031b900a034000e2b107950790007103411818480b060f520040902409001004000f10380300100e503d0b4040d491001d403800308100090b00900d8001d02c080020b6020060958a60820030000581400b01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 251486348 1250 251485098 251485153
    0x60b030a02040303030c08091e0f010f06232107090f0b010806030d021905070806010b0c010506010f0c2613030c0f050607120c0f080702090601090e07031d 68
    0x1000701b00c07000701e4051403082c0d001b8042000500030240d000007840c101c4d046d80a0741c010043c4a90703845000420740a2085d20301c16980300c00041415841c0002003c00426004440758200c0f140001008580e07036800c40c44100320180d054142e45058654280d00e003004040d5000020041c1000c081444c00c400940c01080c040400742c89110140c0c444500f85559521202ca404016a201000b48003a60013055001d8018500c00d100321883c403511403d0550034201c080e41300038282000820b8030100c0d040d0a0181a2f401042840c158181d280300c03010040142035010005480b64010034112030001c040c04006804406040c000340c2d507201c19413011032820224078842607846040300c44010811148100c4d07100c08a800051a850903c102c80c0c4505200c0046002240b05012504210303800003010003140d0940c1a0003450860b86031380c82d41c01030001c8810002c1c441410405104420300c1080114090039803c052070b40b40004800320381c08109030113960b05c0355018185214592030814440c1d0911a01d200184 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 251487598 1250 251486348 251486351
    0x818010911040e070b0405010c0212010e06011805070503060f0f09070e0a060302031510020a0b0405030a030f0e0a030f0c1a091213060f0e0402120601021903020a02040f060b030a0204030303 83
    0x84100700c0e204d8440c2c540d400741d40da404404001c1041258441c405010000c0e0005050712540541c101c1003508480e42c4000c071140d00d03001301c0300420520816410811885e080c480c0e042c451490291b60051407488000e040b04d21500c483c0040114584a500030b000c1c031680e02402000e09800e02c03810140040c090680b0350b5204000220010410798402c0c000d4a0091030b4034800c8001d080498000c000c4030203c0740c00c04004503c80c114945021a0000051f0b43c015400343c2c0c051a0b8a0003800b40040c1901c40003402d11242c94240748440086030800141d01d0245900342c581080e150740c8004046030b1090040030041d2905a000c4081407102100142c1d59000380201c0080361301c264000224003c15014580c0300890700300040504006c06030040d440e10508146e18580030030514880f10010742240c00412200640414040c2000020350301004007140340000703200c13164800310681d40d00035680c81964100a0056031280d0a1190b05050b603042100a492004022502d0b03142c0902d40c00001d4000744016030009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 251488848 1250 251487598 251487611
    0x30603050f1c0e0f130908070f050709141f0803040f0e130c12050129040c0e15090f030a050319050708040b1b0102040f030311010e0d081801091104 65
    0x50180c480082d507800c016056004650003030741000180401002401d00c01c5d611400c801c000030780c00e54001d284581c410302c1400350031007003420150b1808100b5008000e4407450508005d05c0e00c002c6400465010a4130040b1020301c14a0b0107001c2c540b031700790b40e0001107548000f05010810900c071451400c1a984030b602010b2083d030390310784400070580035541d000d01960202030052000c072010701400545907020b8000440e846001c00b0000314041d120035050443e03244243c1100306136180c40d020307040c0140c1084c5400d01d0340313407080c00004112031030400703440500e1800025001c50b203071210074500310f89034401416100340c030f603c0b03007003075a00c0303600c484001103904203e440c00d503100502541c142c60303480c2c1c0c024258900340780c104001540f260740310401c05107003400d0001c01031358004001d000900150440c4002159054518079000d4824410000c103285541d05000d4a4280c0c07410000c0e990096200e14a07001c040c0da2100d230050208d0002c1030032880340e95400e0007920002d000c1c100f00c0c4181172150984080194 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 251490098 1250 251488848 251488903
    0x1801121104170c1f020c06040f03061a010f0309030216060309170f1e070c081e0105160f091a1c090203070302010e061308060612031315030603050f 65
    0x40f02d01107400e65a0200c410080c050304241650701c000c0309109580111594110040e002508541056000c08e2034402ca81d0320520030040c5034020b00a83c0c22040701005004007440c0d0000e0140c0c0c0d0200f034950101503440c220b040c24107208100042e9000c0120080c141116102e0800a025003107480d030a45d00c2c4011020a021500d210004444040c5010a6458108401214038510110394020030310008a012710140003c54168001d8800501d88c1000030724005039040d499110001c0071070b03d02c00f000d9160100704054807804120307008594a02c2d1804406a008052040d9145500c6800214044803220300003070481c1c2000c1c00400c442d03041c0c04c01d9110b0700351070b000031b48050355203070440250180c002100c20401035024010281d03c4180c004d00c01810031082c000c40e80c41030403003a4407408159002e1014000b184c103000040b210824144009503180c8420040c0110344030300288a0150720000c4c15150103039051080c0e01560103940e000042d294540a0707040807990303407400124803810707000132440f00e21407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 251491348 1250 251490098 251490103
    0x8090a05030306090a0b130603060606020c0616020103090506161d01120e01020405030d08010e0f0610080604090c080a0201090501260a09240e01050705180112110417 73
    0x9140d5200004500e03564420083c0304240002a003420300307607034a42d0606a8265074213410703040282407070a80054040d00c1c50500006075502540140195004101c01e21540d40394041110400c0b04407c03d000c1c042041880128020000340e007001d02a4002d903010b00060300c03107a170301205c030042003076a0720b802140f00c82c04082581c4010b031000d103001c00d810603c0c00d00102c103039410060b00e403442000010f00345035071980440d061190301440c041c0001c16100050040506100754190480e080b42c008010903e804c102060000c0b10007400c039001c2c040c10000141442e0b840b0307041a9a001d034800c09004d41c0b10703074840c0880e41c3c51652001c01c81c0411181c1102150a521403190030401c0310907104002c0c01405000fa220a070344001900c40300c98940c0700c1e002040403c1d5983c007021805c0805140d220410030941ea140011036004c41f0b464183e0782d0400c018024400e51000640d10003500d0740b1825070014900e00c0040c0c522480c0d1112200b6a941800e5100009035203100c041e1049820301c00d1103c04e01514000500d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 251492598 1250 251491348 251491363
    0xe18030a0503071b0c12140703021c0c120c0504050a0e0309040903050c030708270102060606031503060a050610030905071505040e0a050403031b09090f060302090114010809 76
    0x8000071800c1c4000b42e96280301d10380320b245032031154070281c80242c0c1d1074035411721300c203216000342140c0145016084c08000311080c60568002c0384070080e1450f00e06590004036203041003a4400e060680b80107603c0c0510202020410050032100c2d81d1150f840c0051805008881c480c0c42564071417890100041c40411301401410004044400a540b0304100c9004002c02407060b4070003a003c1040034012498180803c1004140b050b020742c408640340e684070442000406018880381e2440701c0e0184181120b640c0008001e0b420050842d01d40342c0360fa4418554103020400b201c60940d040c40b901e81406501ea05a500c81c902514080e9003050903030b0342d121400d6040d14036500f070050982e0b001043c100324214080c1c84110000700e6a1820920f03065803030400800c00c140580e0308003a40c6564406100070140c00d840303280c5140b5204804041102c0721254090a40d400ba407282150254544640f407800f003086a00040185500600c0c03560366584805c2081c44480143d4002404203031004080713081c0c240c2c00100d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 251493848 1250 251492598 251492617
    0x603021206100e100e0c0301091503030f080a0b13060503011a150706090b0406140115050910140f03040c0b040305060109091b0b03070f03020301051c02031002040e1803 74
    0x585140e03e0040110121a0002c0c0b4000c0c40d00810440400c1da0701108441a0113051401d503416201e50400c1c0d01001207494003002469422015002000003a4200c0a00c10096845090030003582d1703540112040540b145000080e8811140303406002140c0343c9520a1058030800c0c0c008220010642558280c002d981c1106a6030050401040c0011501d44000a203d00c5114045c0820858040d40c0d0301e00308401c007a54226200c5841d802103400d1000030071107403801005564003242c03079036600030006005841035410081c0508000c06214180c01d0094010041e2041340c09425a65891048442407840e0000c0e90f0880340500488000160400d4900a882c02d5a400c88090301c0964607003d038107402042003401c00c890f8070070381124842009104600030401801e043c2d0f41d2960b686042d503c01040e41d201c10790302c101810301c1440140a191035800c1d07902c200c0034505100c16603004050002a24000700802c2c140100340c0005800704944150840c442d010f1151b540d103402403d11041e081035264020510382 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 251495098 1250 251493848 251493871
    0x2071103010605220b04050c0a03050606030f27060108011401050d11060d1401090c030c0327020301110d0e070611060c07060e010525210507090e0a0603021206 70
    0x24844141c22649001ca0134000c0d00d00300103504c40061002c034007035460071101b8a040d000042813900282d50103009090784480d08031122846c500d4440030003c00c902000d051a14000c048464440780d58100c10301c2d00707420058030701c100c541035030307481c05954003070400746a1801100c4641d0340000345070b04188200145007503102c40310100710180a42030100641146c90120000c50725182883e180001d1243d503980078080c0148003250f1042c101d0710103000c1c0c40129404004041c9402800c010b6400c840304030410815400001c002d503040c07a03000107405400c80c0580c1280609000510400c0048264488880e580c81c610569502c680e5585041c2c0b0f010750f07190700540d503a03008030b40002c80700610030008040562040000003140c81050340503e00712a41240c4045408400400c0c000300188260b0b0b000e584002140f07095803100c001f540071108106250b0700422500b580310008110498054090f110160018084084161401c0c80501024182e02d1000707034003802c100e075052420100003107919841003011002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 251496348 1250 251495098 251495119
    0x415111b15070e030709241d06040231050a08240c040306020c2a0f04110702090c210606030402010e010912030c0c050f0d0f020a03120302071103010605 67
    0x18141c42524410240c59130501038082c0110341220300b03215248461860500600c02d504031010004001d80a42c0c125003c000c145e0030083e05180d000001c100d40c0304030107444c00743e01c4040010f03a6214440e0b10081d0140d0700189840c81c000d40c90b00c2200038a04884084516840940c0d40d03404580cec03104080d103803400042814a60b040c42268030001e10540203c200300405261507606c0c0c07035030802c0b604800701c1580c0903000341045054912030081c00d100850300048541481804820020310404800042140950348850540742c500e0140d4080c0c3d004190050910103107464100e807008020b82c032070a90401a01404001ca0910803075400605110350409050589941c031a5001500c00003603042d1098100421410040381d01e00d4030205024030b05103c0c5d101d119550300f082ca011100e0b550b00f6041a4050b1242000151141c0d940003403850781c258000c0800c680450340d50012881c0f030006500003070b0001083e403003a4910140e041e80200081e40c0118a0992040304150815013a2005e500c60075a1280c0d040c0c0c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 251497598 1250 251496348 251496361
    0x114030d080601021f05150102120a121803080403030c0906210617030d06120c0302150903030f03071205040b0c0f091e01080106170f0415111b15 64
    0x1c80107411100c140101c50108200c01c84c1442014140035045120a40381c41c00d00c05041914044440020401d0003d00007ca1424403140000d01546000b00e04201e050311920b05544519800401c03408005e000f90161030380b0301e05002e0b02c1940b040d50304400182c03030400c03050302852041c02d81c0810744042d41e4805000c40c10744205020741d42c09001401801c0d0b561045c0000d0217860036224414101d00321009107481c3e140807980038080380d0341caa205e01080e05410004d00001803252201100b500c4d41100c400c0203080c200d1a03001020300901403542d8251000103111070b070202d00000030b10300c01c8900e507171803540050807201c070030741038540580d00100340c4100c000c00304282c0082c0c01d01500900d021030f5a0a4206041d1800007882d041c4003001450342140b558003204101c1d60b02001c80c5000d00202d003030052042c0031903003c01402c1c44004281603445c3c90a030010034108150400d214a0350092107405103e0380103010070a22195009580d490b8140c00d059150020409001c1032880145c000100b9002e26a503594 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 251498848 1250 251497598 251497607
    0x1a090403030e0f0f0d09032105040b03010b09040f09020102060402010503070c1e1a01080601051c05011401171902040c200106060311040b09040903020c060f120114030d 74
    0x281084090584400500207980410400c0d5407560b54200020550f0107455150507081c202c03200c072864208501d545040c404980c600350b1500300004222302c0344504c1c0c07200110440e00e0f1f00071134020001c40c0100200008901d40c130100603180d4008221001c0010f14000000a402c90b034030040028096005880001d0256000d00040c0da03002c40d550400c0303a0740000c0395562440000e2184121048a410150200309008016000c200b08a501c814010f54135410304403c40e544a90520803507102e0800c000300100051809070303000d0200c550200081c4108242c0e1604028915030900603140346802514070310501880000740b00c1307980400c1003c8007100c0c5d42c958081c4805089150074200c00d00c600c01000c0602c042d8440c102d911119131071000040c403141424801000d40384031003464015144144030600c8190284c0c000c950090004030340020360002135240c164140520b603244140c1c049004500b14007003401c41001040c03210210722803840240c0c7c03160300e0360400800b0130400c10b401d6030022a41e041d0403800b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 251500098 1250 251498848 251498851
    0x90504021c090305130906090f06062111040b0319061a0310080f0604030f180506130923100f0b0d180c081501050603071b020307030f0b0a1a09 63
    0x41c3c41e0003850000817580209020646038848111641d4600b01000101428820410041c0170018207012061501a00030082c8001030124500c021034501d00301c4200c11540e002c484010390540207940c5540e030380c2100c034006030800c40d08a00149000c0c6121413484103d03110b800d06a40071a001d112200700d944141d41465003000b003400c400101200c81c04a124078042002602380c030034450040c0f010b803070689002842d04682211640c140902c2c0141d54150f216103651000690b103042d00d4032900c6401210200304000100d9000321266898081780700c4101d562010640440b41b0a40a503a0680e256603085079080c8005100701e440c041c9130050240000900fa50041c100c9503200c05c004240c03082008803002c5c0c0390041c807104456191044004018840c001c0c00206803480701c810704c445030307903240c440416490305c0010408003c00c0804001e12010151000340f888410350050100c80d0010b44030310300b42080081d01c02042d0f070300c0028840081c1200c01c1e0380c00f92100e528055848858503075090810311150100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 251501348 1250 251500098 251500103
    0x13050f070c140a050c1f02072c0702070603110c06041103030705070906050a0509041101051308150103050c03060103030c03052109010b091b0403200d080a090504021c09 74
    0x144248101481181040242e030610300404c0500601c580110070000d42c1540d4800d015021481545800412174000c50300c034080300e6401d02c4003800745441001e600f18040380440c8510751420403500744176110382d000480c1c0013502c416880403c440940000740b55010f0117000560340c1190710683c0020001100c0802c1e80b81c0c551409001c0740c2c1000f002d5910103040c40c4654100e45042c03070b0307034003804c000c4c80c61305e4581a0000c00041c0d0302d29440d4101520360220740d1240e85070f000d05000c0c0004540f001c4000762210700b001807000d0301c00d4907030301070002410100f014020310007a58203100f05259910189008610745048030303850b881e04182c08855030780648003a0882c24118540369680200301d0940890502080e115a400d20000103555004004120028002510520380a840002c400d85841140c504a0301580d030001c00c0000d040301400900d80d29081c04003801500300004c64002ca0801c0780c0d83c3d000e410b01c2d680f01d80700c24060b40d842d8409e000403030040e62605140089406007010411200d9844584450b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 251502598 1250 251501348 251501363
    0x70c150c05120a200102030703060e0105030318060d1a0f040c05120403020c04050106020f060a020405011d150c210f07110406030501110c070b070f02120114070e13050f070c 76
    0xa48201c01c00c1c4d01d00c050800031a56500001000303403882e170620502c0042c03c0c215440c009107505110101c3e550b4041d1440c010000c0c660410018080c0d91140305540c0d8020000d40300380300106141c0542e4403a40d12480c1d00074001c880c1022044400e10f444e00800c2a040c585954090a25001c024070414000002d00140d09501400c0003180d140c2d1642d0080a000e8040343d001407580150440e105403a0250040c02526031300c0c07052006100036a0300090769500d0455191000c2c1c111900000003036040c566122540c091f2060003e80008220700100d5020302d000001d01d180040c044000e56031303003100d11440e0400ca4810388100043c500055491341c25021400c40076000042c16a22551103030f00312584e483d0380d11882803011828040b80d00003000b040300508031081e40e02c0e05101e110303a50702014400012000344240e41d2003640c80c2c031150003540441d00c802c2d420002c551060520307000141074080c0865503a401601c00c41c00c0c80301042c40394059140a4031002032840e0460340d903541e044805052142e011034118 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 251503848 1250 251502598 251502617
    0x6170403030f090803091c020c010e0111070321020309090712140705030114041b0516060f09021008040c05010f170405010609060512150406060803070c150c05120a 72
    0x44000744a2002c20922505420f90f1724100345440900c2c01040c8003800d05c1d400c1181d14012801903000c181c10181600c2820003d40701c40318140169807242010040d4040c41c41000000010300403d5130b000c0102c4868103a00049914080307000302d88070305c0391403001a005504040803428603440f90441c03030040343c420074001070492802c1c2c054410003941504e0680c00075401100505c01001c1d02001030040300021102000070004101c214080c0c008060350090500101103030070302e81e071901a4142032100da4803480400c41c0d055101c000030014440c4040c10b0780103911200301c0702e0364a0b01401032035008a030850000116070f40340c10011180060b40403001c204003d140b500039245008500344090190748980d0001c14803a04145401c2c0890308207602ca940b14081076503000d0108040030842103c41001c070f1b40c0607042c0f5035850500c140035002d00e601002d0b091100103500705c140900e4410140075030f00c40380c404510580419804460b07084202c200503102e604144c80c20141e014440000300720780303880c85c10800b455 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 251505098 1250 251503848 251503871
    0x11a0403050102120a05100e0a050703021308210a0c06050702010219080105120a1a0c1608180a08070b070510090506181c081b030c120c040617040303 66
    0x3d83e0441040e0030081c09103502802143c40d858050260320141c0072021603005880c1c030560903446c403009024130607039540e1440070402880c4203804460044101e143c00740c0d2140d540380c0c1440d0361000303000601118011a07008586100c2104000c031035440580b5138414119103800d0b16001c000300b50251800c1c1c150340d03081001e070b40200400758034500e100c01d4945550641e50714010600c194680a49036522a542101c846600040c0010416183c8101324001444031591502d10141d244c0c400e00c1c00c4640014035a03040002040982001803d0703842001c28406c41d0f0000d108180001c01050b8058040c803500070510500070310308007201030200d0901070f00444561680e0010000c0c11100715210030383d400c2d0842e03c01c0003003600130310b0f1100102c0741d40b510080800070b07021a40c040740030701040c407142c040007a40030100c0c04031005c0e841459a0240300704000e5a60303040061050055030b01c1048420350045448c00020b40e01e80d0501c0944007140c000751103000e411174030709280704050f071002002102403503030302c0d522081d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 251506348 1250 251505098 251505101
    0x20903011b090509010911030c0a0306030c17010f06030203030d0b0d02040603060b210601050103110c0f060108010b01050414010c03050c030408010605041b02250b0c0115050a0b03011a04030501 85
    0x980444030748449101d03d0600302030048241c016004000c54a0070705a9544c81c444a540440351b000d0821400d0f986c55034444501200542820b0740042c191000005021507000582c0448040c07924044008000540c440c50034002964000c2c4006941504284101062491150031084902800825580c002005507002804484c1039401c103407031440e6074103611401170401901441002420715a50422050f98404507542c82c81c050003568109030f120010401e40208038810313a02c4220015040d10150100b5180c1550707919024407405000e5800d000f00c400301c2d5400b80342100c05503007505032182005064840191090f2261032811010810b003004640c401c020184040c10181c80100d0010403507030316080802050300d42c041d100090000c64013886585082d000240e41d540c401d22034129a41150b4001081c41d1100d074168400d0380a10300006402e06540d80640c00f0310603041c629401000726686403002c0c042e08030740c240595051480100014841103118468500d0086225183c00d80b8140d1a561100d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 251507598 1250 251506348 251506391
    0x15010206010b03190f0c090b040b09040c03020412140c010f05070803060316080129101116080703170c0d08250c2d021507021504081501050d020402090301 68
    0x1e1517160785181e480c01880d442100750000b40440110141001d0401a10b60150300c02c54501c0341c81260340e15442e00425000b40c0580303008000300040ba6004003101d091251040700a83c0e001c07031b480e00030206040c58a60060059030b5184c900b07680c4203401c007051a629a01c01d40e0003c3c140743d82c184603c5519207500020818043d01030306680002041c18100c1c821110b000c440c00c0e0415034104042c0c0854040c0c1c5440b50f041c07426003862240b6004404010a104241c00d0011840a07000b08108180001c01d039010300040034403c0707900c0b0302c46003041409400031440c1c0a0042071400d0342d05401600306d1140c100e10030340c60740f9008182c480207040b040c40d52503080c000e40b583c80012000456480208a810703c80100381120380203000d003104c481314080200303204400c1d0030700300c3d002031243c1c03400030340c62400e140140140c440f055400b27001c3c031211916101821145400c42d20500720148500d03110943d88044200040c0d0403281d01401407501d0509984c20000a500800a0107402d590f0320349010b00328440c100b0400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 251508848 1250 251507598 251507621
    0x70203010603080c07180501140d0201030605061b060603010209060328020304030e1915031a0306090f0f030a08060d060f1d0d09030816170705010b040515010206010b0319 75
    0x10400321b40b8080c858401d42c800408800d49092802c00100007003039141502d2741c075148080321210041c20245c40143c0c0200f00607080079402c070b0303008a00f81c007131008091003c1000c0c883c10700c212681c1ea0303980e00030503082c0c2c4541384000303401c10410b001041403002181000c00204011200e4425041301e90f0704441d04a80045030f040c1c000030102103c0c0545030505221400b0780c2a120100002610308020303001d4020140554007604160340c6960103000442a26240c80031550014190b4038070741058064146d6842d525025a40f16004a1407440e4054800100b10340303030740019889030100355450404000004c035000c042904c4140e00c801407482d4060b0310384500c41c51003101c10600b0075807401c0c00b441d16180030611a00c80c41480b000c5201403010603407802c00d0b200c02c145e440304602c00c800380f24a802403158065400e42c0310883c40100d10041004419044200c0300030055400304596030724134000c0000c1560000302d503405a0003030001804581d2810000b10752100074084045000700c00c13000c80200b203901c2003011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251510098 1250 251508848 251508853
    0x70b070b100312050d05060603090d080c090a0e06030d1701120f0803070804170a05030606160b070e0f0414070c03091706010302030717030a03020c15190608030a0c08070203010603080c 81
    0xf8005c11114a1084542000c82650030a003503142500c0301c10f0b6221141750f0100700344581d80c0700251030146050211014000301402c90a0560350314088420245015250300303200b030003100924010a4498910b5802c020307070700105105240d20f01044c02a80d42c6402340c040d181d143d1906490804681c15400950140e0354603a42c658040c640750a00010a04501491224110040044450701030384001525000341049864565038403000c20401e01030080306d10b000740045d0440c2c04000400c0d0300300f00343d00c407501d01c19525400e0251407038040108845001c0d0000051901c107001280c1d0461060400c1c0c10b51900c00e007021900d49449500c221119200c101d80e0304180c0d40301d100107008500301403102078000c02c04803d0311407000400c10881920381c0540414201010f9020580000750003040050080002588404011500303201e0b0503c841440307034511100d0000e00b480000120810000304481e140d0b00980d4401004c808a07644500950b4002841680d0540d200c4ea0b0210215115500400454290000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 251511348 1250 251510098 251510107
    0xa030506060f091302150904110a02010f09021806040b1302180406080c1005070b010f03050f1204061103040902040603020a110f060a0e031b07050102070503070b070b10031205 77
    0x400c100c119942e68014041c0700d0403001d004041a0340c03c2c021800700c0d0304403000207049602c210b0f504040d000c0c1c41c54590380141840c2c0c0040700403a0040c000c2130141c0c1590b00038024070480d40000300640d685140e0094004010054680460786503503141900000000c0c000320345031041030002682d8810902004034041d030300169000003020601200c0c110301c08140e906004140c641540c8584800360f1458845c0240313280e29a211040c1d101c1e030121006140d002c2800926561180f203800c0540c1c445000883d882d1254607110f1541c100e0001d10b00521410514100d80341a0800d4812540c0503140c0300c0500d80e42c80701740804140301e1114000f0340045c0c07505036401a00d884420800810142c0c480091a200da0003400c0c4402c902d0b840423079095440202c848000c501d54101c2d0708d00e2441c0d8841c1441140040780b040c10b044481c0c08002c122081117030002d07401c8500b629210360405854901c00c0c40741012803c000c01c0f04000003004005019481403440320001300517035807510384003226072801d07c0c25000030f4000603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 251512598 1250 251511348 251511361
    0x906050a0f180b12060708040314072105040b0739140604052101150e040611070b040b011802090108071101060f090504110103020f07030c030e0a030506 67
    0x140303040040c00640064141185403515540c5a6030854150410040d141c61900d03000342c895645840380001c810b01220310610b4513030001050313014183d07070031400030341040c203c0c2c44101c2048080c2c40200c1d82041c0d80d0100784a84030000b9600308007200c2c0c01c0090250030320002440c070035100c01918040c1d0042400301c06088a88441c0c03d0300d101d010540d0940d2480441400b600c02038280030b0078081d1010707a2541851034801d940007030b03560300031a4003541e400300c40d8561010030391a0000848030394480601c000d120220a00806610070200c03409214284500c030070003c2e0120304660800c846201004100c035240040c1c0e900c810b130484a04440c00d860308503145004000040510020024160801004508202c5d00741d000818034140585980100054900d2031082d168081d40401d0041592842001c0540d42d00d024000281c4411201a108040785102d5003507554080c0c0200da480c04091001c02c0d18100c820307601030341c41c01c08a031030503400c00c60b14251503103d544500a0f20702c0554051401015680f6106 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 251513848 1250 251512598 251512609
    0x9100f090e060901090b0106030506010905040204080a05060705030105010c02220e0f0706020d090501050711041a0f0d020604030b040602040801020301121407031e0f0819090f05030604150207020a090605 89
    0x500f1640e61070b031405410390040f07025558044c0c1520918540890280c0301e01c070048440500c6908260f600c18800a00014182c00000e040024144a03c054901c60754a01d02d0645440c0000d2040d58045140d200f200401460204d0990700d4000790381400140304980c00c1c41c804110b50340e0b018010104c0e408101c401107148030401030800207000c0e0344014107041c003108100403c60701c9140b0a0328107011000c614181004514070507075001e943c0103802008100040d8042954002d412150140601c500d240e50300c485042118031560030310340162005151914680e104000309a00600a60718240e00380400300f0040707030030300003140200200e4406680482e003608022800d000015641d1070a540f02c03060400c0001c5171400000c0540c16419a80301e0040080d081100f1241c03c035280040250800241c8640c0b00c0d604404800c20408980c0d95070001e440c2c465a080b200c406030380c0900c6074540c0c030520018ac00203072076400040c1c45441b1150054249030f031071790104007086081e0704040c1c1038585031201444942041d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 251515098 1250 251513848 251513851
    0x30160507080303070e010c2a0603060e0f04030f020f06190501090506240c070b070b01060c0b060405100510030e10060b180d0c080a02031b0f09100f090e06 68
    0x801c00342d4950300340f40034081c0551200690403414080c11300510802e0000c44560f050307002101142c0401d820100c0291500c8030600e83c01202d000c03914101d804079000c10300305981132240014540f4025643c07036a44040c0c40175400f82041d1421846141c0c00d06900c41002e0180c940144c0380d1205c0451007580a00399041a580c050708100080d03440c101c1004850396403800e0400300d4075071408080584510303c8001120342c2c4100005801113104071580003800c80740b01c400500d1800d00940018043d030342c881d0400c4945100c2c070342001c0e081205000100c2c6443c9400d50100d81c1004040401000340c0d0354a801141060b030341c105001020940d91000c4032401d2000b44061090110b05007001c2240e20b017004031000990064141070010090074040c403009585235070541d04422500401014111a034410203169118821b4008901a01803074104000c4035640c10070030030050500610402e5035210f80001d0000841008107801082000840001031410501c19820701802c2c0d000300205400e41d0006005150040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 251516348 1250 251515098 251515109
    0x1b0f0f120c0a0f0f12060f03150507050a031a13140a05010f03140102040e2806050906120717030d110a0f050d06050a0f030302060a050930160507 64
    0x81080041c01e0240e10400d8000400f0b014100340d002411818130855082072510f0244410307900d458004144180400c4400007243d104040913a40c900007244420152803003690a00e011602c144880d800d080c0c060f80011041e40c003004401c0040c200c0f42000622612244418440301e55510005100440009804076504c07212000341070101c1e5240410842030202c05200142c89040c80441130b08401310290112002018880389503542d904140c0c440c007400c540524940c07032004001318902400c40b101409010102d60006000c1c1ea87c540d1000248085001c6100d914a5140903141020130383d490303091251242c03120280b000b10345600710200b000084895a005640c1315440600400001550080d0510007440842c50f041d42c031100206000c401400b03c41e04103a40c490300310800071504058029002003264080d600b10741064171004200412500117580c4100150401d60400c401d00c0240c1c401c0448048410f0b0883c800c080039030f143d00401e0f4100c2000b0400c05418000404240031041005d07502925 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 251517598 1250 251516348 251516371
    0x6030b0316051201060f060f020f0106080712030e03010f06080114190c0219081e0703090509060324070908150406050711010207060c090603020406081b0f0f12 70
    0x102500d00c1d516a80205100300e900c0780440440d0004416400c0d0000c0004181c1807000442c1580c9549010386204081402240140706825044c0c0d101c2c0c405029086c00c44215401902440382042c100c0984004510340560900800d203450741c0081d102480b9105006919940000c4c0b180c1c180404a800d550300040c42ca458407100320300b44800d9204403c2c00000c05941640300160712006400103030b09018044040f91509114480719000303100981008252041510282000d59115100d80b808140903500020b40051110907050103182000e00360fa80e04804010100c07160004441c150b225180344d0300b2202c072400803401d014480c0868105148001400024014011041c0b41180f8422188001040a80490b444ea408901102e0040c0030b28032000107071030003c0d9a00d90450400384080c04070741e40d1500001b0180c007400545644240300741d4007940c035155a950010380701c2500c24080504805840c10600d4020000e50f00101c12600040c200d18440449490721010908481040881e00400003000340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 251518848 1250 251517598 251517613
    0xc0f020a0503030a1805030304060f05060405010311040f1506020708060f060904081606050a0b0111030406050f0c0c120708010f15030209070215101a0a090b18180106030b03 76
    0x150002c070550b03911400807000080d183d10a03c800701c0c0b4404ca800c01c09000303404008140000d004039030704003046241c10000184125200c01e4240000c80b0400d200c050210941c8e00003a010700e140ca03401203c1042c0c003074100800c0c100b07180c4040120344100d0760700210140c1c0c00120b0404c0381c00001c2c45059406071034020018402d01d0700302e0218800c00f0300103200030410a40001d04402150440049005094002008009601d4020049401011054002400b0a4014a00304140c2e82c000049809596150f50b600e030800c1c44581102900d43c00559055449002d031581c18106603c84c115208803103401c3e180108090ba03e00200d09003120942d400d054161418076085c1c041030442c0f81c040c081101d0f815030384c081540e03941c080e0881c20031312180c901c03210700d0583c1c200380444410b1a090000685020007000301c0d01241200b2544002d00c02c010708000801c414000030000305074418040d0460740c480c3c581402440003080e00203521003031480c1400607240151001071001c15854030a01c0e150b550141c0051000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 251520098 1250 251518848 251518853
    0x150b04170d0e0d030c0b0103080306090f0903180109080a0803040b0108070b041202010c0c092003060a050405041a07051242060309010902150301060804111f030c0f020a 74
    0x441180c00070580541c1c82d80c0000e40030103214010500c030540d04010300c006d03103586900c1d202d0781c0c1d54002d0362494401c40782c00012944150310034003414002da00d91401140741c401695100000c03050010b446a0500c2245000056186030500500c640c492081c1c03403003503a0789005d1500107480d45060f0848089544002004c1c840f03842d40740e0803181074441180e070100f1030401a20040b24000042040140040b015140000780480305401040e034030300d0107442c0800308045449000d203103804100d03003981e488104050304026504050380241e4016000c1d400b040d60f8410030300d48000745640c0994601c00050703000204102c450100c03c070b02c1c58014494071685451028011440c07450080110020b040d0100b9038501203c0b4070101001d4010030b08006050107031a40b41408555001f0503a02105a000360503400380801c0180b10102140d050342c04c1c64860103107a40717603070301c07a181d002c1412216039401003450f207158070582c0340704028100c602c205076030080348c40301e16280000e0005985d20603100555001c000038000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 251521348 1250 251520098 251520107
    0x30c011d0604061505040c03060302090a1439030402031e15090c1003020319020403050a1104091a060a06090819020f0a060507031103030c0913150b04170d 68
    0x10043e4002c500418140681900d10a00c180c040c3e00059106d0315080b4081c0c0c1301d40c0c0540100301224002c95801c03400d551081e03020300070345111940f0031452090880019028440c03296a00e01035100b04a021400c0f030a82c01c407881485404401a0398030340c4008030410045103020000d03094002c040d0b00204590802c41d1009680c0e40010a43c80141c2c3c0f5080d10000d0103409040080e0612014020409460700c040d24001800070b610070f50b4401a4480c0e88042d40500001030b0084030100da81c4100141095040d50300d41c1d9210141d00d0400d00e500c42d44680b44440842ca4074030f82041442e42d40d81d140040750600d50100721310b40455520840900a40900401880300040386064a1071005000602301d0440c62000448442200082c2640451262004204207920601a00c0d015120707440c0c20364400b411881c1c40e5968003040303038050243c0c00e04000d40f0f4081d0502100510090402d0000400c940c50003103038407640d26a81da089001100404071b4204805042c0c20040c8010b00c0641c0c0c040c0c03078429060f9030002c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 251522598 1250 251521348 251521351
    0x100c0b0c091c14030d0c0210110f2b0c0f0201110a0f02030c01020309010204080d111c03091a0714040e0c030c0d1401030309051e040b0307030204050108030c011d06 72
    0x200e03103a40d5460040c008010020080750140c90f0130780369103010320050b0000810b01446500010301c24105891058821031007508401e05419940d1070504030582c000901e030b58454005404145211482a0580300c0749528880c1300c0310040c6004103103e1840c0000900316074034030f00f0740030841e8103120b00d440c00084000304944003104107161183c0b101e810058281d1640c840c00e4549903440d88000200b0060510660140060704d1150b03040e180a0704001104035060001c9140d1406950840c031501e000341c1840c0f22039104040d680d0300740451603007a40d03159088082071040c2305110030100c00341007100e01544044040b10002c13065810341d080608080240c003060328001c02541c80840e001005c00c485882c103200742c4071070041d40b402c2800321030b40c0c1d036905054041d8280301c120042540e1603808200b91504044c1c10044000300e24066420b501d4890800c4045e05280300c030b0b0382c8c00d802078030303004009070f04c45001c1c05004e010b2420003590b503003c0603208035007103518420881208841074808821100b0300807030f002c2e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 251523848 1250 251522598 251522629
    0xc1f02031b0d091b0906050d0507180609090f0308060114120a15030c030b0601080f151201020c030711040b0913061b18092c0c100c0b0c09 61
    0x16a107a10742c1004160042488540c0a0903000080108440c4c000211002030195a64600700f0720030590384505100c3c1d2005080c50007802500038410134040444c19107a44e109a10200c000410f0460366007041070219042c072841562120300746480071040c03640040c100c9401c40420b203402c11019004602c19000e90082c01d045100c4403d01401040300d031002034100d01107064641c1c0603103031010f0703480c5820044d1031121f110481d00c7e41d40c40360008000398002d10b4440c0c841c080c0f0301c0401105550b2451040c0c4500c0c4200c001076888071026800a0306c621091014203100043c41c001035994902e20b050100c010641d800c2003d02c501e0826240d05160385411040d590050002d049002010b0039510f00308001d415500000324071a90040d111919041c1c1c04085c4038080424031600207a8aa140d41808042d90340c0c02c00c000c041070444105200c079500c8a40170307492052115030252029408100e00180c10005c60029450024022451101c10300200301c002c40d400111003080315280500d02004244040c9000505 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 251525098 1250 251523848 251523901
    0x30112030e13060f03030305060402030f01030b0417040b0904050a0c020c101704081206040c022d100905160302090403050d0b18190e06040b1801020c1f0203 69
    0x40c441e06495000d00c00390090030b00d07002480031588a00d10000b1012103407000390002406d090110b03100f0b013404e10840303015a0f03c0020440d40c5d6030031900d03000304202000d0710860f00030020b02004404901c0b42409000a0044080c1d201c0e85c9256400c20002500c03800b0300744005151410b00c101e001d031f907000036182d00c410f4810381e40f0000365074a042c02600c181144d50541745280340c0d00401c02003040302003c0105240c114200c440c031301c01d0300c40e001031204a0f654948400c02684c0031000c2001003949054110113101d2100d00b610b070713801003003928107820300481c2e00400d10502d840302c16410400c402400602003400d138021030319061528540008010f04d0000e08050701f4070800054a4100c0c20320b54005002c0c00001500c00854400e0003e00a211035030120340e0021519600b01c110410900c2d00e00401000e10348030310041a15407556202c0b150310090180c650b0308a0101c403000007038120001c0c0050003a825110001e02a0b9440d009070145202c14420180c000c00d41c810030400001203e00840c0307603011030340000e2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 251526348 1250 251525098 251525117
    0x702100e1608370c0b1306051303140102072909030304050309010e1c0f060f0903050f0309010b0d08040617010501020604060e010b0301060f0302041a010f030506041107030215060603011203 83
    0x101d044031070821040c040c01c600203001300403d0312503c12008140780098250864071182d03030b843c0100c07082d000320009015852002d641c1000801c0c0003d10071100c6007100000145450500c0d52854110700c00684c00c04045e2144030b0920300018030001d0a2503002d01709001441c51460903554072034680c4200101c00e4103102007220003261a0b00c03224449100c207940913070310310711a40403410001c4d440b42280b035088450f1800e1203040804500d09006020250350706458041c200040d82007048270035000201000c41d10741d40c40c640b2052507512004480c0009020300c440568079810180700510900010154a0615080b54010026641c2c0001e00a910540004000962201c1c1001843c090817445503140d81c150b00b06500402c00111100001045901c01c45080100c0e200415040c0001d00800d401d89011442d0741034082440b501a0f04410b510060040000401d40496501400541c00280007500164040310b91120464620342e04290031900459030326082d90f1600c0604450b4088021008041150482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 251527598 1250 251526348 251526433
    0x140d0f050412031b060e0c03010c0e041d070e090d0306141c051605010905041b21110d0c0c230705270a090b0a050702100e1608 56
    0x140c1001421113090984810315a8140030010341070b06040e0000a02888a0310042c4d80780520881510000d503880b1844032100c3c00302040000d1142c1d9500300b8207001c120240950445082c03010101505c0c820b4411806070a0407040246885212000d110505251082c103000036054101e008003a808100c441300700f20410184000740d60b812140d0024a20300c6034440950f99015140070020039940203076071b401d080d00d0b926001c00c0195651065140300701f940440800303c23451302c65086522807000058207a020100c1d000f0303d840482d14280817210003036001003821210107026000c1c03019001860b02d0440445010b031740300c00200d0244518440c1c1907007810507000075113241c10700528004100040c08520700b82c03203488046a0003251454621002100c0b5000214002114840d903558584c00410072096903072900c404500600000d0f103150194460400903003920400b50142d04500d900d20070181c915200c0b11904140b4000c401c2d00b01d98216042141176004459071300c558600340030b8500d20035003040c0700100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 251528848 1250 251527598 251527607
    0x9020a050913050d1e1d101701030602040302090c0319050621030a02010510060c03030c12020a090e0a09050a020405060a080607081b030103120c06020412140d0f05041203 75
    0x48400500303c1c050314000e00044c60b00545081c0900300680207040c6011100d1100321854200180d140016280c003800748102030600704007a51901e1924100903d05c200c5a40714410100300c264812104641c0001d41030045062400c215030700101c0d1000c0705402c6091030007641c104884888104a80d455503100010306a580f0103e80110349800300340000b40340707803030f01048545a603c442401d0015608040c0402d08144080003007008031005607a0780c41035826075950803000740c01001500760401c20341d002c1554140c00301d44010200c6202c2a00d034400303118604200b681d10070a0003000985002e01d899202c00109a003c00c001500039411280000c80b0f0383c400001490b031107407c1d00010300c41e01ca500c0c1084042d54000034505c0c01a07003007a04044000000303440c00300b40da100c00d000040c400d030f00d0100c1000015000300d81004005104142c05828652180300d01054403682800031b845142854204200c01d0f0010305c044120013007103140440980341401c9014019214510501c0450201031400f4028180b0a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 251530098 1250 251528848 251528881
    0x309071806030f200d06091101020606030a080c0a06050117120a020a0b0405030f0c0609011a0a05010503100e0a02090a0510050418061d04021e0901060e01050f040303020a05060a09020a0509 83
    0x40c0402d10f03404486c2400001001c02440850360046441e0784854190300004855109200c01001441c0da051150f445038201e8010300d07041c0c140e40c8500350108000461071b010740c1d400f0305400041c00340e0390529421080c0c030b0400280020010001c040222041055022a1040c000f41d0404210342c05034480d4907005107107101f0708d84d0385440e14201054503060000c0218100f070180e0a220000d01801e81c03c903440340880c01244644642c010350a11040000f0f5000300c000d1076100e9000d0201100b03669555a01d80c5035484111540c1441d03550004a0303140034a0080c038020054081940c01003010440c034a000b40007031150340610b070800c00c0e07000d428400000b11500280007602c13100d00c840320200071100c020300070b840054408074490103080c5d01c0300c04000190401d144200c80700808241c0264608601a9130705604404000d0400504214072080941c03424001c0006510a41c0186030b80992401c040b07082100280280081e50b00740030081c40540d4070205000c0a968086901c20480d40740c0001d0060318034607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 251531348 1250 251530098 251530163
    0x60903070806070203091f050a08040501090b270111031302061e0403021c0209071b02281a0f162108011d0a18080309071806030f 57
    0x82e52040000c1c0541c0400a07046550b001d80b8003440041181d0380e015241c0e181c015031113001800620010028601c03075001c40c1d421500810000803040b0007500c03910018101140d40901c815030b070b88880c000a10b020110b0030702185e19440200000ca04842e62500d0300c0c84054a04442c0c012451003400565650030308880600790038642580351214402950229600300c1d1100781d01c0340d03454403c80f015145020341c0500c001c0742e0040c034901c0181c2e0745200c240c034444007154510b40009110014080140c0703903100750031080300c003010641d4400411044100f201d0070300e6410402d88440c0d041c0445606003408001d980c1c4030100c2c10308803510f0304002280e00c0080400360794054030b009a080c0001020f4501c01410f45240000e540c2c2d400650383c1c071002c503c21001d00744011107049185260014164403450340c492070760104d03c0803070b10041c8030b05501d9902960b00140c61100403504014800c004204450424075440a54404148141445d41c0c42d02c4a03e10450800507110700c129007410384034402083c9a0000702c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 251532598 1250 251531348 251531353
    0x3030f041202030c09010b270a030f1515061d150d0c0e0f0f370f03030f120914070f090608191103101a010c110609030708 54
    0x75a201c00040301000d5100d4164042e000c1d1312130000c00d504294045078161009040c005190042c00e60302041c450810180700140400b0048040761a6a0b40312840c10007540220503808440c400c9060142001c41e400a100d40d049180108031981d000909040748101c0d092814486d422070014100e4500000480e442603921050340d128108407120040e0140c100d40c40178500401c0248400034042d100da001102c051507105181c10242030403883c202d107034220b2541020380740d241c000718041210345000030400d06030441c0f0b810035144030448010b4094254010180600f0b512a120f10310b440c041c080325075511184c020040707403040300301541030140c000e403550300e5101285500ca0610340c54100e480c1c1c05903001d641c0b19003041800000358240f090082030141c60010020b0110280e81040100c58000211802c072001200e0a80341c669554040c0190340400c5840d100206400003105070351b4030b818201021580c1030204520009004c9582001941d07820300d4140c03046079aa0070716400107440d1500d80d03403102c000e62 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 251533848 1250 251532598 251532607
    0x31b0506010e040317010821040308030408030f1302100f030b03060a020a0e060913050709120506040b01060302070b040201200106172e0c030f0c0206090c0a08190203030f 75
    0x502001c0403861046000b035031002d03c0c0800c84940640a80020710415400d5440b15050301c04d42000040180123040207400b0591070559a80c1d1185180d4000f25003d41d00c0ca1740c0842001101200d0b6010300d584003500c4c001a1442d10042e50029506103a2a4174060403c200a0b0000301854001c0d072100604450040c1110725914203010044003a504c9130055200241001c0039058803414200c2c10f490744044028031080300d03441140000301c02828001c160408115200c480041c1007c2141d0315a080070f40510054507051425003080d4410080682c820310806204005917004034404010346a042642440c2039070042004a0f021800c1661403410060301d54a4404002840f261201303042004024a50a80c2c0701510001c82a1544800f002c1c00380d9064034804100f110040705561044070840070364100011880420105103017150400b512640143c1e10140c00d00c1245d400401000800007030860707e41848074241f144191b100d6041c500100c0c034000340d1204210441d607041c025034841c080401c0c580ca444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 251535098 1250 251533848 251533859
    0x3050609011b0f050904050915010603060f0f2421050405070f0506041e0f0e07020c120309010c11040903020a1a010b09100216260303040f031b050601 66
    0x30625075681d085004032804800c402d40d4040c880c401075818a0340c42e45420803162a0a120251100900040703850180c502c8824421f1805101e85001c2c1c80941d500047c014240100440d620321030360000070f42407038000e40c00c0048003041c40e403407600c6011000a4081c0790101130006e40d0400d0483c04481212049030300c1030703802013a00784d000c14881e9010702c040b280341c2642d49920306c1c1141030b607004007a04801c0c20001400078144c00c03040803401c40400392003081c01a03aa14203194120401e0741028408030034640900008941c100031000c00410201c0d00311711182d10329000b1503a2446821201414081c5e0294070b0020300c2408800c60446203c00740050044850524000307444500a0f10110b0780003607409508021001c042858506842008114030310704010310f42048019266081801c0440c0711f2a008c41c2c41c0d1000c841ca850b0014040d000782500030031080111350207044081680f890030780c0e1042c0304000c00300f243c00035070684260301401c140810061100b130841140a09007005440d9108407800081d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 251536348 1250 251535098 251535101
    0x20d05010501170f03030c0f09011101050118110a1b05120f0315040b010f1d040f05060123040e04081e0405040e0a0c0504020708070b0106020a030806040b0a0303050a03020c011404050d0906050a050304020a0305060901 95
    0x224101c01c1d2020044d0040040d0450ca040c02900321403c00500c4107140001c5551580981200c0355004000301d41100c100e01102a94640c003001003071001c14800310074010881311070402c026880c0c5088809024071107221000810034910441c081013040300c0f9804c4500c240d044000007001215000d00240301201c2c1013641d40d005028152030361800940c240380342d22600d82e10000103a908000780d0b01070314585460600100140700015005030b410000820a1140d00c0c2e2600700103c501c140c1400c80d880e183c61801041000322029010b240c2003582140781c040300007644d0300810030181c410481d1b0051300c40f0400e081001c03960058200c02068001c0520001c61116000100c00b0100e62190340d5042c50380d540c000500040d58614080d854100d40c20303010610009000c0d1005e08070151840c0742c01420140810540d50035112650240510029804140400d000051110342c680020605203010302030701d0030f007008000740300701c0a110042120201c0404d0441d42c1d00c0822100a60f04034040f0707541800c24075607950 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 251537598 1250 251536348 251536379
    0x3031d010e01060312050304030801030210140c010e010e0304080a060c0207050310020304150e03030a11160c03050705010207061704050705100216080c0a030201030504020d05010501170f03030c0f090111010501 92
    0x19105030a0262a00c415441ba10899200740c1e030694641603164607583c02d00c01c1e880000807014003408404d01210040c500d4331130241159540e07043c00404c2c80401000400d0840701c801006c01280d0b00100018004650000703a180c00351584803000080091403440103c1c1080b060750040c5a0500901d580317000424171503006103000b035000302515001c00a040e1440e000700d840ba0291b00a864106000013940c1541075400700c3c0e42c1a03400340565140045029504a24681c03180c03040b0385e0b000d807501d000e0080c4002081507001410080c002080a1410200060100812102c800c50441c405e40d0004040080500040008040c0139240c1c240400c6000c1e000f80d00c4102500d4464040284048000388408001848507164403000e030460301e00f503045800440180c00020010380e00050303035401e104009482445114003d03d032000d110b503200e11900d2000d40c1413405c1030400502580c030500600c1050804401152090300304403030f0540d40d0f003000f91b006a582944250480800c4e501e40000001c0034021182c1d60b8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 251538848 1250 251537598 251537603
    0xc15221a0901050613020a230c070e06060915090907170a09030e06160206070506040201080901020c060135030408010c0201050103110415030c06020c04140405060403031d010e010603 80
    0x18907074520300d40c2030803203404031a0181c0c00000301241100300005030380248a104e1552421400e414070301805500014000050510b80c1100090300000c0301c5001d00103080036000303421300c0c0d03107190400e10001403a60240b0b00d4000d1046c2d421006544040d6441c104031900c0084c0a86416030a02d0a844058a2561650003560040400c0780001e025000319224100d001945503c44801c043c07440300602007039030026088542c0685c0c4030324190025927030b23007400b411812780310700001c1c11140713071501c00144140000740165245a00501c03406c2380100f80410034505446075000c03c1500e2456900110b030054032098981d142d564050301605413000400f0005009403920a4000d00080f04020300c1203007207680910020700f81203040442c5030340900e4290000304c08040f05c00d0440385825140d48409980d50306952180c00540c2c400c0510051a0400d8000c1d401196100403100045180a131640c40c0c4400780280000c08040d03550021000543c807860480103018041e40081108821913241c2c54001e00d21030005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251540098 1250 251538848 251538893
    0xb131d01141017060a08030f071a0405060a0c050906070b040311031305151902010b2704060c1206080c2b0609050a120302070c0504020c1522 62
    0x702940d05100c510031040c0705482e510305044185040c50004a000090030940d40000348840c00a06003404002510008a5028100d5984c100c103113408160450400c0705041d1f0340daa0b010402c00860004217046500c82c81d5034901181c1c13080070610448141c8a905801d5601c03600100c2c0183c1403022449460b07104034401d0300c2d01940390015030040c9030340c1e028117428010145840903041c44142003445028240203900f01000d0f003440c1f030b20360802c01007002c40d4040c00d005030765a41c00800c00d0b14260414504d0740b041c00541d620310359100950051915002003010300f040c0e44072940c0481040c4602d1100f86584100d8000f0440d00d6203c003540760301d5007500d400e05841807002100c0c85461405e8403621000f40c406440200c42c407015148c1c3d40c000a000c43c220705403840d002e41e610280108100f10001c0c010000103030707401a0744010914042c0021103054010b00e00643c41444041c60303140001440d1210046031038842d5105940d055a035028400d4126a14529240e070085820b04020409002032000d5001018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251541348 1250 251540098 251540129
    0x70503090d20030318010c0c1a0a0801050a030c0603020702130c09090506030106080a14010906020d02030601030f05090d0c0606080a08090918100203090c1207050102010b190b131d01 80
    0x81580da80107800840b00130017140d0381c40d00513543c01a20300d0450184264142d04407a60b40e042091145042841d035422002e20000340356000342c1e440900c40e4094541210481d00448c1552203070148949940a10720625074001140d03000d648d207c0c1c250047c07002402505100203544810020000d001c540f289021070307070034000070807220316041c06441c1c10389820000400d240a9076891700894401c0d500d0300042036550342e80d0380c1c10100d6000d000910098401b0301e0003590301d0510380001400ca0301c4401c43d111186261400b48a8a0100803d81210b001590b10700761420740510b041480041001d540455520300c200d82181c000c0020003000780c400c40c4c0c000c4520602964480d5880b07080344c0c0024182d070200d41c000303d8025000e8000c69000e180c100c480d04084030281c50060300400c0800440c000c1c11051680051420803c1350703824007c0c0207e0002c01d40d10304105840c4210200c204a03170901855a4a00001ca40b1a8407004441c0d0440000c2c901111480c120032003085a1866002080c010200180340001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251542598 1250 251541348 251541413
    0xf12270615140d080a140408061008060702120901030204120b010504060b07030e060a091203020c0a06020f1b030a020d06091e020d120306050307032a06020d05070503090d 75
    0xb08003040910103801c000c1440c2c40c40c0e4450899902c0201140d0500601c0800d64032140d045070041d002402009005000304c0c00c040d4074140c000319080c0d02c08c1c449a4000710802401c3c9601064082c0d0f160511b41c021030311b500e00500160060300640d004203071481c0a49051006002c40503000394100c032001e80d0300f0010b8548a03000c250b418811403e000e400b0603400725407001d181c20654000c0a0314241490142815a00ca04e41070f01900c108041c160010f84c800010391010b0301d0302d80c144c41c00a005030300080c1503142c080d0b00b1142d26862460f004070082e1603000c44002c0284c40620003030400c1c60f8020030364100003196140c140024040c20000f1303680c0229060030120b1303208041501159198005288100310244c541d035800c0708052004280041684880e40050952020003224010718440c2c1d104860f42143e1904c0011035241039408900c20413024401000890303000700b000c2e0078018052a0990380c0c1c11031410040e1035481030182300707074001c1440c4891100744021a5148042d0040c01a00d840440c40f001c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251543848 1250 251542598 251542619
    0x12150501210b100504050c0c0d05040501020d0804050708010501181407080a020d0b0a0603020c060a050609070503041b030c05030606030607080105040c0221190f12270615 75
    0x1404801020041d5103001c10070740c803112a8001072049605001c1d541340c1d00800e003910000c0da540c551148000c01c825203450b80c01d0000c0c11950910b85407150a042c0741c580002e6a42d240c03c54079509004400000c2410b2081c00d0040d10003801200000740401c0d41e48001c0c0000440b02c501050100515064901000c1544004032074001d4107035548840c195202e040d4a480203500c0f800d2540350007a07031802c2c01c100c143c4805010390001c104a44005803950007030a0550f04003400202003094440c80c06040155035601c2120080c0c10200b00e20b8082c0d240d0f034035454660040d00320400080080e90400b0700c008100100005401c00b540c0c000c0e41a6521078840310145541c402e802d03904480811958070041c0300c00d051079402242d0441643c81100c6d111040342c1410320003164041c486649461000445a40c4900511310b2420901c40c0707494035070820300e510a4028020206682402e454589855614042c0030781042e00f8a003620941e828001d2101c420b00c0c4c24402020603001042d488007040000140c15000c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251545098 1250 251543848 251543879
    0xd14040602120d020c06010803090112050c120705070c0807050a06080601020a03140904022106061c051503100e120705070911040b04091406060903030a031512150501 73
    0x341d0300241403094241e18065050740110609000c20f0b542071044070042c400400c6414020654a000745507248407820005111110044026816078204024000e26598000071608820f0380c206c040300050300c8400c022a11031103115409800d14845c060041082d000208502044403c2224000700c050b98421041d0ba050b64111040744c0541c000c4080800440e00400068010100c3c1c0c10b5100c4c0750003100d1000904a80041e00f0340133752aa0065540600d41c2010502c541d04030030704840c01030510010b140800300c0e240d50340c0108240b264403200810319040f1483c0d001141c2110080540d00129800302d82c9000401c2e00e12201c645910455043c10300d01e05508045a01c025080310150207542d040038910300160101554100c1868401c000c0088c10790b00c10741c0a070010303105601c0042680c13244039040d40110800036247c07603c00c0008010031803060394004219140101c1c141804130f2948040c0301c1071090b03a80309501642d464207050008200b0400074a0072100c030042d00802c101308a0740c0ba821902140c124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251546348 1250 251545098 251545109
    0x510050a1209020d0212071a030a060501090305030307051c050106080f0a0e0c01030518010c02071401180312030f02030901021b06011505180a0b1c1e0b040b0301020304050d1404 78
    0x8a000d00781002d4200442041c071b1900b000c0c030485103055580e100d03a040c907140f8141a2050108007100340100303c003003802001c009003824601203c126082d9151aa01c0344000b500700c00074080c0014000d0807090303800b8500000301154203010886580e443e40d001e003105a085800b803203000250400a0b0200c0e00307521031700c4101e10250700180300110020300154003c3c800a4a14416900e00d002d1103041d000f800d001d40d000d1801c4a40c060704516142400c00000074080120150500030b010003452002070352410b0050403203030000c112562290031658150003c00f0340501c04c2c0d00013070000007000799a01c030540050081001c8000b0702d80c400c80c480b10310141c82c0d000c203008868802004082d00103503d403103040904254100180745000d0040c400002455003481d13540203c07104080443c1c0368202c0c0384003880400d078988620009000e41d160030b03484426030782c0143c05680303013090380c5007807241c855100d0ba4003000caa0030025000b15543d0a250800b980d49103030494042c40040c10360f199600d2252036501c261011600b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251547598 1250 251546348 251546359
    0xd0503010909030306050a080d0801080c010c061a0d0818040504020d030302071e03030c03060b030709051302070602070807021f09211a0f06010306080304030f020a0510050a120902 79
    0x1d0810250034090841d0000540030141c5464000c906561100c0c44d2a001f85040c40080402c0401c546002d005814142e000301030a0300000200b0103540d0700b01031120703107580d440800082c2950520700d1000d0b8408407c1906c83e0400207054010003040310b08001425021420490380344110240c01c03c000a442044070020340040449010b070002a000b50050302070316200781140740d10280705511820040b0421403083c0c0000384c592a1110070755402d44a010007510440782d1051941c1381030f240107058001c00d48140c901880080309810f0041c85144d054684059012038155074402031030514032001c0e046008241e00c00e41507014040e2074000c80002c06140c902c03603501d806024501d000c4840035240d0111554006074084448030a00248010300c07460541c0340c0c101900d4446080c0f20a88800c000c20042031581407500d800d00a120703003400001502c0803268010155a06148180f0100e0299290342c0e21480c0c004901040d8102c0721504400907028840c134594030401031140c4810300c0d0b01a10707241c1038040e4201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251548848 1250 251547598 251547601
    0x3051b040b040608120306060702060a030c03150e13110d0c0906060201200c0c04020f03040c21150605100f030c0315050904030309080a020d080f090606010503040c0b1306110d0503 79
    0x405d4034014660000d402461182815465004607410b90300101c0c0f05000650303222200c1d28425018840d103071500d241c0031200705840382060040007400c50040c015480d0821b00c07408030002c12030401d91900c403605025150880f040f24520b054501841e1502a48104604014001c070740c8038030500c14140403134841414418002c1044115400560001c001c02407a4001d03e203080003a502c80d4002002e41144001a041e924a05400c00d8000c412040e00040304a02403000303009201c0000700c51480d5038682000041026070120350f6420000d1a20341d0204d500404011880501690466290004260301e500c06010400701c0b540c0440844401e03a04583c1c1e014003c079000c0c000c505000c0007480c0d100303129003000078071201c20b034540030619000392144034016480740440740c1019030b0002c0195003061015140d2503090402c80c41c9a619440300600c1d8604110300480000d05000d403281c030b0740703000f070140586140e0307140c4c041029989404124050b850201d4104815501160000110300390001d04583e12207045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251550098 1250 251548848 251548873
    0x919020607030e0406030b0f0a202104031106070903150509030d06030b010807080a0b07030504020102071d060a2c1801020d0b10180e1003051b040b040608 68
    0x180e4101e4070099040002c020311050550321148215409107000b1403c090051821041d06040482c008100e8180c80c1c0c14002c040c03144030900c0c0c0b1000d0090361a0300d151a182c007002b020040d081c180d194028942918141c05100a048d0044034100e500704111042e11295038803040c0c10344040102d448000c2500045040800d501003903540402d40201000303050b83c1c80c100381340314464150b4072960010f81e43d1800000042050074030801441c070040c108040a86010a440c5c2c6074115410300c0100703440103064039100082c08580c424420322002e0141032100100119582805103070f03900044807040d02170782e10040c1c0403035480c00c03801d220100311581100b04ca6080f00510016040e241e0042c06014645001081040f01c0b49402c0c000303012000d8403840d0025403c1385010070080c0d85202141e41e1814000d80d40007150107103401003000c00a1f13a207088147d030440e864404119005220a41c00988280240001683d05c410b800404580000d4105c0c0d0134000203106104100440d81c040c802c2900b9a4000c1c64a40300b17 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251551348 1250 251550098 251550109
    0xa060804080306090a0204170f06090c13020f070203100b010e060304081c020d09080310060305131713031b05010203180405040812011203090906060c02060928050306091902 76
    0x1404500c103035001d8146551034102c03100d8005040c01c0c1c20721a420040c27a080c02407600300314065001400d400200310000c860800314402e40042000c9540715600021046d603040404411201300c0d03a4060103c801c0320b9030041d8218005d249150b42140014142101c4041078900030742664040c0303030001c00c0c05261680001050308490244505181d10580034000c101914803640319503107040c0c1c02130f0441d550300d00c4c2c0401e00301d5030280b00d5041603052500d020144500c8901109c58110459030144000c420b0a51341c004941150144084190b0030070401a40401003098003650084c180e0300c2e6000c80040c0d561200d005984a0064a01a29121490b00039000c0d0a28040d001590054081d07182985444049640c0d080e00507401d0308a20310810203a08003104040e44210803900421100d9808c0298500700a40145080510b1102910521011803441d803541e8514042000d0400020409084040d400d680031b944007250f44901442805100f001035400c3c500450345907410801c07000d07001c8234860203608100c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251552598 1250 251551348 251551351
    0x9060109030506010b0d1407090b130f120303180209131506030c08060705070201020d030527010507110105040507060546050a020714040b03011107020a06080408030609 74
    0x504118140300000080340040c0265801380c655555039965505001d503007a4282c8000e030b0400500d0311005000c128906a012105009442c0a42005680d4282044400e0442c2e0000d0f0003402c00540d50300c0002458012410396080d01d6440f07a2000c0c000d0411100c1086141c2c887da0f00c020390452181c0b000030b40081c0030200d998184c10300c0f400480e00801c0c11800803400712074040d0000c881c0414000030a01c10402c08203c403c7d840026441c0291415010750300003501d603007160f034195050685410110700d1584a198004218070f805d1445541c15416261005001c0c050694041c0b0120b902138000c074001d0401030040c180306641280c001e003440c0c0c1c9000001c0381e04d0b500229403490280c510541840003800107822052642a580030420040c000c04400740300500d000f4071918090003400c1200b0b407201c1d0f40101b130660844000501c80c44481d241000481c0c0500000000c0740e0345075107000f0707802d0a800580b00c080c1c01100d000f0346842540035181c46007501c211a0a81300545011020720000341d5500e025400351f07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251553848 1250 251552598 251552611
    0x30106120e061003060c031d01060608060604080d0e010908010903021c0507050307080d092f060a2709020d021c09080414010201020d0c170a0b0a050f04020708040605030108011b0e09 80
    0x540c1c88030480030041d808c001000d021003a651100e41c1004080d138840b41d800d0301304604035521840c080c41c100c0c0095503026240d05880922000c0101075810380e00404014008100041c02400008160f00d4000e49518011603240c403211100340e00000001e2140096034582603000008501d0070303180d62170380340b0310780c00440f400002542c890b60440d00180029080f512110312881c541c4c0c4044c20124015140d89880b051101e00174501440030030001580205100e50f0703030b25401941c402048032020394090400240e046102d026000290ba50320440b1147d004140811185900090303814841b100d450035030b051000d000d80850030500050100702003802001c6560401400010303c1d220010070f6203001e898094040701d01180a12040c400c11070448c4010300d6102c4040d4800b008400c1ca008009180c80a00c0d0180fa40038082c00070b9041c0da15222036048803181c6030800c4c2c031152100c0e621400203000e0340c001d004601030b1354246044e00c407a080408002034114480d684032201403001503014030a00e4480203011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251555098 1250 251553848 251553851
    0x501050406140702210607080c04090915020a09090f0605060703080a140403030e0607030b36100303170903070201050c031c050907080f0c09040512030106120e061003060c03 76
    0x160b0059854003505c02000262154400b0142030748002d890508000600d00f209002c1044c04010300c640ba66400c960a9805150300000d400030b090030003540351141d04840101e4035200040e03042103140c0222017103041b15121300041c86141e0362400030708113440300c91041d141c100c8030030300c085d8000078007136008030b54014a010340000d40543c2c99120304108407000e513400d60221b507a802d1a0520031806010880c0d12030424181880070205090106500301000e0440007020f4500105c4409000f11035000ca0b229114902e40315650343c09c01302080024501c0c035200c00ca0100b410b04206c007074a0a0b542740303810b00c142d5900026609140309600150b03601c0d03001880e03541003808104001604007084881d40c1142840108001880c2c0c45d00c08045407034072020b504081d00d00d40c0500040d04603035100080e51a601007050383c6038210717038a55160540c90081e001c01d501e200c40c1e00100c008a4143e038005a4440c10310019602404007000502d442529078805031a428511302118800303001103003480c1c1109642008070300c4c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251556348 1250 251555098 251555107
    0xb1b031309020409061e03020f040e070905070f020a1a100510090303090b1317070f03050a06050c0c0c011d1314060102060f070e210307031701050105040614 69
    0x280202501120342109041c540c0c045400c1c00011400c1c0308000141841001e0000604803d0340300074005001480001e1142d80c285c500003c0984030340e0403c40280884d24129000d250720f55107000007500c03044030848000303038201998a074a180b0000c0c4003290b15400904900e45804209040c03196084003c1400300a8455910001115240d2629011b80d0300596556103040c1e030309502c2c0090809104e0b900001d8044020f00c0740c8c01c0c0400340f00140400b19400a2819003854640002c4903080c06135580c400381d00300010035030010a102c1e0108014026a10400341003082d5503940003c82c9240c015458100601c0c2d000d000c01c08203070350003902283e1500c41003028858a00841c0d0000401030b1202d110b40c00c00b480d4032084c045d1180020b14180903004102400601540c0c039003865403440c0740c14020455000c111a00c4042140b94813011028011000b40381e00004240451107091640c0b80c2c42000d04600044080c440c90092204c0640194180c03079050755160316061601c0000c4540b02143e80c0d01d15154002080f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251557598 1250 251556348 251556367
    0x40c060c0503090a06021b15090904060b04021b0c01090f1509180605011d0f1314010605030601020f0705010e28090e10090f0605040317040b010515040b1b03 69
    0x21450020440340d40200a03040c400c41c80c550391500c0b07047c49240105000400000303043c10034030582e01503010503101042c01e80c0d0355081c0b00000d01188070303070183c0040c8001101000200c041000701071154010342201d94283c48000119003524492140310000e0740485010f0005007d02109100c000d1030a00c0c0c803200c409d4544446905071030804080d1088541c0e0b80d4010089075800280181c0c540124240920750050803d020401241d9404003891103007482c2607904110038030035401800244803161000c0840c0d0307150240a000c03a481920203034050300c40c000c108810030b10001030b003100f640c106030354401c11014214240003009113544041c3c4404006d0042e0f4203000d940710b801d803400400e60341d440454025400ea1480d0b04011110b132017680040c0c103064008011880c5091128a2141e06c10b0340010280d80310308040710341032a50b2804001e107210300c100f8007081c016402c0725141616002c40c2c4100c011030445203810024800e0f0320503107041c5030050100c481d2924807140da181d0041100c2e000d40b4a01309408 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251558848 1250 251557598 251557609
    0x20c010e1f05010b090108131208040204050609090703020105030925030b0108060c03040314040312030b090a020c1b0103060503030301030602040e0f090309040b040b0a0311030c010206040c060c050309 88
    0x20403804a500c104400d4011215060107611001d900480c200042e504020003620180700310b039007560501141d01c02203111210b040c040a1081c80c0c0005075410b12407800d001c010091030058405920a6042c10080395503440c1203084036004007280c2d802005c80c68595401034500740c00061401c10b0340d0161080d07407015100d0b00798079003036814460364180051034150b02d4042004441a08034002c694400c404102d00c000c4030780300310381e00190141400c500c0c0c0088040342c41300a1049800c010008140d402202a1054042d005080300442c01c03140da0132580c0d201d880660032401402c001d500d85134020b020414404118240c0b20009903418503010442545130b40220f40386030300a0380125511503000400308415100b1618140d00841c08501a020600b41090a26600c0c02000d1945d8401e0f0341e10300603c002c941d66540f00c0d101462000d4180c020070760f0350b814503540c1080e4030003120b0701900510b106401e180d0302c0418101e00c41d0768403c0a030810907045c4081254003004418048840d0b1004101131007030341d90341 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251560098 1250 251558848 251558861
    0x22512023a02101704080304170409020309010f021801050309070902030c070506010909030909050a0b03010c0e0a09020307081303090302190501020c010212031906170a0b010e101503020c01 83
    0x1007107140c07103401071648140100c2a0400011204008820740803401e940348445440b6002a080061180c0f681caa600b0001510805009003185c0107030009400034500d109070300654802d0000700000c1011b04002c184041c00c0c0c0c42005184045400040d1900c01e41e50b000d4405181c122400300215042a81c80e207454104a80c0b00380e034441c1e0112008034081041020801132107014214040c014881030680350740180c42841c0c0750241c00582ca8407540040d611040590085245410080091000e141d103258045d007044405202d0354041c60f1f250401080ea60881c1c000c603806401241c0e80c0ca401c3e035071090640e001411a0f40c0d001c4040203614800080580e0701c0518182c1c03003d042c0080d4035111031524001a24161740710b260541513401001c0c0c203040503019502075942c010b5603040c7d000441d08001e61100010400ca0300200340354200c0a0341c400040070001100f1100d14458031034000303580d0300c6108464505038211784c803140307042103031000340a035400c000c0340180888071500700581403821500100c1d027503590 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251561348 1250 251560098 251560189
    0x120311060705271f1b03090504061409040215070501020a0503010927060e190c15051303030c020406030614061c0201022503050d02251202 61
    0xb00410034120014074010612110b4102181e110409204180030400c003102c040c04400c020400d01c0c0740114824081c1e020a9401d0035100c5503120300e14114a00078101d000d980c0141030140703250107400310f080002c20b402084200001410311550390345a908100020452029041801d182400728000140c02400a00050346240d03c8040e107960401104e00200c83c0000c803900c1d200184043e500540c02c940f4040d880f0072580107240812104100c80b92280341900c6420252540c4100e9180785042c420400187c0083e1111000c0302c3ca030032048140c0889880c080c551182064407030300b400410000b03014030804428284007800110355150b40b9118801154000b070306104d500c004410800903540351404000b14240100109403881c0c0c035603500000e60303508441c0c04051091480c402d58100780d00c1c1d200d642d4030080d0342c0842101c0200038080d600a403188880c2000d28211004082c2500d03042200100c90b609690164024008a8425400b0402d400d00c3c1c0000503c41e2541d00c045650a50072400e001640e000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251562598 1250 251561348 251561357
    0x70c08030a050a110313030c0203011b03050f0609190504170a0203070b090105011a0d200d050105100c06050a0615030603021804171806120f060a0f1203110607 70
    0x40c1070011031042d140f4044c20309500d100200104554604440908600c00f6010b103406981142103201190040040f5580c5280b000d03001c1c3e42800200d03600d6004144a120007401000e4103031140814040528400e85501c0c0382c510744401b08030a800a03650002343e0050145443ca032100c0c0c0364248401300d50b803042c407138800140c00020f14001030080021840d03030001100d00081020758984042034820741310514a07428035100002c0d2020070890303180c01445c0090b6022268140160f01401c0c81c030f816921043d10203e0550a20000280501c1d002e42800801c194a444442410b195551040c0050100030120042c5a40c1d07201c0104400e80d40b640b40814900b5141c0b00001d929045004200780204082d41d044500790410040000065051241d83c02c0000024519a00d8080d115409048400c9413004075400070320100d98050030808c46400305015880c14000c40c234641c0c071a602400707000202c9000300340c6001c50600c800c1000300404802205c01d1802481c04081000c400c48055041542c155144030029 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251563848 1250 251562598 251562601
    0x30f050d15051908121305041107020324070305060117010308130e010510050a0212030c03060f010e0d1707080705071a130603050a0b0d0b1501030b0d0803070c08030a05 74
    0x2401c0070340003c45842c90b0704805030102d6251801041e6986901440316400300310103d10b01080729669184c090240c00014428480c00f4000760140c00d10f608841385c142c1c441e11840c080a04044290840200501400340b01d04650b0755904109501500000e0306860410140c0c0450342a004c40d00d4003034038082d40c4141029070340c5076803000d05d01044500343d0300103203051005440100425901c54100c480c0480180c102039880d440b20100590a020041142100e0071700000104114400910011880b07060201c0e180700d10159003034011038100750850f03403141d0414400303503909000c40d245003c00012082040401d500d000800d5072140c0c065000a0400c903482d0380415014000401e83c0e50341a02e110340801095414031100302c1c1c02c1303841c22182c1c0c42800c0a01d41d9403400b00b06051041d800869116402130080c60f038202c03485c58407040e55a01220340b0200d00300c071100141325540c400d0040c240074000c010400d00340b0005030303160520558006072900d13061028240341c600010352080060f41c8641c006410002c0c86 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251565098 1250 251563848 251563859
    0x61c060f05100f05210f0706020a0303050f0411152704060819080f0f070f0308060a080a03081801152c01060e03100f091e050604030f050d15 62
    0x81190f040441070314000c100c01d0289450b114120000c2402d981808605000e001741404c2c01c040055010310702c0c034000d001010890580007d140c15065210b0340e401c00490b07071000d000160451058900819804401a0266a925000407561000a03412006d14900180400815070245020062102007103002c2024051031034140701e03403401001001d002e045050750f0040d181005080782e0034000c03c585400300d00e41026102c10400d468042444900d01c40e514035480c1003a0088060310141100060741c0d040000f001c07414200d540c0803c0b149a200103041184a50390191921030004020000e00714031008098000482402120300d4503216496502c1c503141410323070368440e90000e8484a6400c0500c0e90200c4100021000e00c0e0b0b0440f0b8040c07815a07048001540001d04007103401001d80004d43c10050500410405648003441040c441d80342d83d10614490542e0001c200100301d0301515680181d00003402007401280080780d0706d101840c1244c90803070000c55907001c90340a29415110a01c0845042c440d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251566348 1250 251565098 251565121
    0x12020a090515060307030612210201061a0f130906150206090703020f011b0506070201150513090201050409150306050903121501090b1803010b0117061c060f05 70
    0x54008034a080c0030600d0b0102ca000928800503405038041e401c00400a02070511952003080508040c03029500c04401e2070030b100ba9800401d1a107400c44c010502030144079140144038010459415086c01c110496038018403c037190001c0d4508941c200381041110440c6410800725000707441600c000148141c28152160100000c06079a40107542c0007001344030000d80e0020700301b07088a0341240e41d054a410b030880121044210300b07000d518280d50b421054010448040750051284c4515030080006005041000004048500c03a4603000700c10340c81c5210310131010b078010f00d44003801814294a095a120760701c0044030441501403034410080300003442000040e018403030b0400800700095081a01d02202c0c82d081d000e014010620341c180c038804000169000d5040c00001704004100c09455003000c0124000c4004950b840600c42c1d4603160099009600580e0403c3c01ea1888400d86003441e40d0b504c080c013030441440c12508a10000c00340813100000c40d80d000c4c1034140800d145000c40c590800c00390904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251567598 1250 251566348 251566369
    0x15052e08210405060a171e09070b07060b031c08100e06030c01120b03010c020f100207030503011403120a17010902030624090d0516060216060c17041202 67
    0x100140445420960700030704003034038155030044a0641d034440310b00c0d00c1613500080012100f4480b0003170724200424405802041c000c01c08400b00e40741419500d881aa42d21150203020302001410300f0f101d0a40822420f912032126941c000d411102000d546015110b0030381100b152440020700544100710310342000c42042c030700030401d2040300f100c1030601200084d151001c1c600090304000f64021103100c020042d0f0008401141d0280c020025034030f80d200025180d4034203442c0014140308164a022440d032481c802c807941d80e901550b0b513a003964200320302900d5220480f00207035814803c400f0441060300c070301e0004200d08605c0b515464204201803034000c00481c03050f402040840d1040c4200702007501c070340b04480c0d00c07010b070001c901d0a001803141400801340110044190413010301c80c3c0c0c1104104001912080b5070144264a0030655698142240d0b0b034050110074480150325141c04014150140211201c054840d501180c00c003201000c6124082d0019401400342c104500440400d5040084424 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251568848 1250 251567598 251567623
    0x30b1b03070e0909010b21010608061003020d0809030106090c021920120d02010b01020f0c010f30020d061d0105060304020d0501060303121815052e08 66
    0x240c118908000c000e03042940d00744609015140120020380f1030709083d8411043d0010060014070f00c0d030100c83d101d171454220100c004500b07605e00035001c110f860b000981a0312811440c15150041411682403148446a070281191103d506001030001da5800780104405003580344400140202c641100030304d0035100150135001644180603100100b1501915601001e050116030691108010f021614610704044525028014074090861559042d000341c16181c20036403c42d6404041c051605840d00c0740818840d02044001d404c03542e16a00480402a50724486002c880101140c000c19038240d0020950080005500003120642802c1c41e11a08001d0140d82110180c000044505c2c00306050060065a101e100702000013403c554890035400c44182c3d100009000e000d07660b00c0c0140000040561b0b01c140742e8242107064042034000a01c2c0b6004542104a00d900796204074080c50082001405508407245030010500c8880703007406e41d450b0090071018600c0f10703103490085820300300300a19021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251570098 1250 251568848 251568901
    0xa050f160c0501050a0206010b0c120c0604060c110c0405060402070203161806060e0607140709050f010e04020102060f0a06051c050f0303090a060209010c0209041a011401020a0b100f030b 82
    0x2015206540001d87c41c1c10745020600240c0d8500c0306071000c5107041618a0710300140000054000005900071480381d001c2c40c402c440501c07914101401c1903824110200b45c0352030583c0a0340320800c1901d890b0300150341240020740300520b012410b40111b414000c01d004e64615440c140f0004100c100169140401850707000c0d40204206818590000d021001020f00305208140202c2c0003010300c140461901045d4014030115007a1039030720340801307024150440700d010b42c0e1000403000007040252803a40c40d1186178140c0c00b030100c650b00d40101d040306107400f504070016195038113008512911080e5410b6251101c02c4500000f20034145003030780c901800329074038411b40c0c1c001340709020301c901d400500307082c50b140d0005001d0b855984c0003004a9140521810295000144c44103000c140b0001c12a0080e0b00c3c5204e40b0084020fa0321141a00d0340c2e14071a0300c460307006078010066030001c1400320503e40d42100d02103000c00c144941c1c44c0394200c1900055001500d0122000007442a030b2010240701036042c8100a20 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251571348 1250 251570098 251570107
    0x201080702160e100e010314060c09131503050105090304051912020d06023a09111203042c0f0105030c0111010b0a06031d06010506030c0a050f160c050105 68
    0x149840c09550701c00e5003d1401e1103c0840d40c40025406040c001c1c100722022107540750ba5a040503a00c160480203003003101d0040c03c000c203505440c40001c81d511003c0260511203203103110041a401802812503055007102d4000d400300000d002801106c5c01490707803400843d11103003408100800c610a000d800b82c140c28140404010b1742c42481c000e148410f8041b1001d01403940302e81411400b034401d95520320007105404040f1045c0c1406d0880460b030941011805070804200500c880044072549000501809200001412680b0b8007001009160840d00f0a607420259181c4a80b14403004040210480028003442040302040100706c6550100c900c003184072003945440b01003901d41026000345810408a4083c09030785020942080d0700c80c0320098261031400382d452400074010801c0c180d80c1e40d2005015a0007540010000038401e0517910010421403654580340f610401e01d5200d142c0f41014454248000c000840d0108047c100c0c4010790300d001d400c028101e10f00181000a1070300500e040c40018007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251572598 1250 251571348 251571373
    0xf04060807120201020f060106090e0702010e0717160f0518011212110d02060103021509090105061b0a08091f0c120912051005010909260d0f02070201080702 69
    0x228a000c942c070059445010010500040b41412050000c8882d148980703000004c0c00c81e0302030004030842c0c1c001c401d907010949030b100d4102d0a0b28002950341c4000d40c00701000340045d00c18212030b12064442c603401c80d0440c84100d4409008084181d0002007072488140c0200503a00b4400c802c43b000310b030128040c0c801507040c5041484010351505003c4c05044d0041c41c4c0410190241032005c3c40e00313080a0444440d0241444000d40d591001d010072405101400414585030300705070159042100d00402c1200d07103030300b80814440b0325040000610a0000030004c003043e410424042030301130a01910003190785500b02c109100c08207003801802d190100d51804000b002a0b4040303007051203264050486410441200c0741240c0003849508040c00c0080b07800782e1681002000075521032041c100344802d104c680c5e603a070b0048003200d1460b50b002e4030b0446111020001944180440701302210251192400d040150700036800b04c450303442241d440d02c0e0b4000b9160040d0340c0c000d01c0d11503002e03040d48000e100c1c508042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251573848 1250 251572598 251572603
    0x60406020304090f020417010c0f110c06070609081c060506030402010c11040b130906140f010b070c1509060314010f12140d0504060807110616120c0203090f040608 72
    0xa00c030b0082c40035074480b03042140b1310700d076011600140758204d160700402c20440d0401d402043c803400b140c404268006031200c8032074003804d032400712030081c18050001e030b00ca88004d00c01554030800e02200c48031359544941b000211104050a0f10170b00186e11003108202e0740d104c8404503000b542043e031042c4030501c20040107030ba010780b407003001e207a01110442150070090301040c050000c0b00d048503403000d0710a249602c1161280e00560340140a00e0b82400001c2070b040401c03a540c1d0040c0d034110f03050060b0360014455100d001c3d004000309032150b60b600784c10b681d41c0c1607040584001c40100000043c00032408001407a031501500403070000440308450194581484805e000f11203106603401d505565181c1000d000e00740060034050680b0303005072104038040718001003160303025025400c0401c0f50b61010030700c098881d031184803286018200800c15615544103092094651310302d040b04200440b840400e60001e0f5025984070840c00d90029502c1d004000c041100040c070070340c0c4103070289242200030032590070700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251575098 1250 251573848 251573857
    0x60c0c0d110c040501061d06070803070e031015061101020a0c020118120f020918030f03060d050d020a061b0212031e090c090714090906130603031d0604060203 70
    0x681c00c2400c40c00500d4003859050030b03503142c0e60561182c508000015580e8004204624501d50000d000d20a80ca04808212440c002c0c81000f5040e62010300005180c14054954201042d400808403142c100d08880400c05881001c80384001942450104011a40c0c020f0751b03450030b0780400402942840c40d44070004202da02c49800290407c001c0c1039441007200417510340000030b0301070340301d0307030781c0e5103180c1c0d0034481e04000c28003404030b0080b56034400186101034840100c3c441a074213200036610300040044200d01a800c00f44c40264014903c2140d00c0005500b048000034100081e00604604450b90400408588411400b0380c0705100c04c1d518120855808246d086d88803100a50f03480c6c40e41ca91070b0208003900ca680f04584408000c00003400035444001500c64015034045521840990b01c90100320340986039558046640c280521420708c062600c445041c0d40407002502c040400000242000195003041d4810390128840b20303045480c44105804900ba6140261441c610b000c0c03415a00a58901c60f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251576348 1250 251575098 251575123
    0x2030111030f1303050c0d0203040314010b0307060302090301110d0e0105010618180f020307090915030f0b060f030111040303080c28020102210a0b041a1003021b0609060c0c 76
    0xf85030800d1820103001d0020389085110f00401c48108042d0200040e659500c0342c00103507180843c0c0041454112414010b408480c5c1c4003070040d014043c5003800c181c000c1d400c040c02c00783d07255407102d004052280080d4098042c94500200c00305555190f02075132800c503081a00850100000e418a00c00480f0309641208115400c00c03601c00c49038008124080001c0803000041d440301400082031003000f03540034083c0015649100001c010340d46400d130782034406039001d100003020a0858101e500210301e002d41d180d82e200c900580008081d0b1082c1c00024211b030b1028484041501000c9000c1c030034154000883d40e805100c5104240ca0724480054000b00142c2d8461940305a486218032800301a00c03c1d01a20514281c5000034044c907901960031040030901100c8001007a4070300901c8051a15207405404540720170018000d803414425030502107541020041403003403580800030140300740d0100075804608401b49000d02928103200c1209403d0240c050044590746000707124024186002280c00d0340e8a12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251577598 1250 251576348 251576371
    0x6080a090506060609120a030c1b05090105040c0314010f0801060602012003040f1b09110a21060b042c070813030905130c030608010e1510030203030706020702030111030f 75
    0x25260360010f40c0c03607401c031615000540646401d1f032003050340011310204200c0c0714260201d101d0b20b140210742400e090303520489901503991801007055007420352003610302c0402460301103422510041032500c6000207a000346948140040100268042031041e88042c00091000703108030080310113901d0a844070b203910074500010002c0410b04101c000d10000e040158400b03c44401203a007018003841d0014148500e208080c28281c3c1091010b5030b0b00b08480c1c00281c5a165019004001801e03a41b001c0340107800b10041c10f60b00c1002061001b0010054801001050140c0788488420308004114111014000c1c1d0707a150981c0a000d070141d0800318503039100b690092071418a080707074101100c44d001036501558104070300d0108030000201940243c4000286601d0031300295945030b031070500b00d0b141091400712030740118903c0e0740740040014010b81c00c0701c040003021709407580f241c0029055a010081c115051a03000801c0000c600b400c0c05100c031011404840c0724158508081800e030038140c0100f4498006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251578848 1250 251577598 251577607
    0x2a190207080d170c0c0d020309040b0a06020d030c20010e16030c12060603020405090604020f013603061401060f08040c0506070501110301080a02280b0f160c06080a0905060606 77
    0x2d0302581c090310b4084405d001107a203940341c00000a502c903480040c0c19030149080446181850404410810841e0301e80e500520344c481005400f01d006101d1349c400c01042010085212980701c09181c10a1000c010802c000604a41424001440d0162004000050b6880020100f01103040805500c08032000e640c1c00e450010a1480c18200504103504001d600c14940414840c16200018015116910030f40c2c100000780c041e04019103041d000320080c1104800900d05103c500c40c803000460140110701074201d00c00a8a0b99100030603032320903825441d4000005001009601da10a540041304110b50034108002e080c1600d0395184d1a101e4050940502c90014001c400c06c8000d40c0701c0c844408103011440d0b16940c40ba08000e4980d880d182d800e0340724001d038120003164100701160b0300e01c42002c40d51a1250f014523050113484980c100517010b1801810a10400d6414000603650070308461262000e00b00103030030004c0141c9118400f0b0418008545000c1d141000550001407040d000790b812962a81c98 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251580098 1250 251578848 251578861
    0x9010c03091a0d0f09080a200d022a0a0e1e16030b1207051207030b0403030c0311090f0f0406080102040e0609090a0b2a190207080d17 59
    0x1034818950212240c10b41d0303035a40008801c482c202801e266007a8803403d0100078818001c030401c1e51113101014142100070060100c00a020701ca81c9945601802141d05090fa0f4000319242810342510001d005a000b541d41c6c4034210440d40402c03581d00b9070341440b41c0c45d10001071011421a1019028040700328100c0800300d2030101c46054a800e40ca1440e00100d4598507044014042c11090440c901003c01d007840031022040c9481c8442030440a0090024052146080b040043c4081c410100d03441502500c0381c0400410310881c20b0700d226038080c1e103010031700c0c590410000701282e4003030008810142060150100079503c0c641801030944048801820113528100050b00800355a030001000358800140001c01b454a044030900c10201101d50301000d6854041d07207500e400011600170110703041400000e60708554900e0320307044805100d00b4450300c0103103080c00b020700d40e01c107140301000d40390140d41a60109504120140160140344050f0507001c40001000e010b000400a540d40c1280301c400000d0345 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251581348 1250 251580098 251580107
    0x706020a030204080105070f090609050d0b060a05090a020703020706080402130f060902070c1a03010e0f04050c0d0311060c0a14160f0804030b0127020c07030b0907061805010509010c03 81
    0x1e4100301000b04907d080070840540080104600c002c0440c0010707400058081c0110004412602c0103080728050001640d1103200018000705001c3c2d0204d11040007003401e885042265204003842c580044e56031506040c068540348803035000c40200500c0794204001621803602000c1150441031000c68090800c90050780a0092a0484240300d803000c641c5201344464440400c007224926034a41002e4a001c21140e801440240252195242060b01090041002c014030a42c4940503009030b8100d0f4001400164900c40700000640006164004c140711020042c081240c01249000901c0c0c68071002120207060440c21030142000008080fa00150105004109401072a400015030450030080e141558480e0002e002c142d40c10040b0b4000400c000c440c4040c01d03554403101d01140000400070b521740202039800800d034007810f801406c60000004440101e000d0040501034003a007a01814000b00402e118601c410803050301300100000c101d10798001045030910340080c030b8242c5900c100e600b41600d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251582598 1250 251581348 251581357
    0x1080712021c0b070201020714010501051f020c19141f032307031b0c050a11060d0e0606040b060405150901090305030406031d060601021203180105010e0a1d030706020a0302 76
    0x14103d104140804c1102a81903005001d124410300c1050b40301c0c11700e121040d00300c0c0c409028040c1c0042005128110240b9040e006451200c107900c11500f5807810380e03020504a0ba055105100d1a8401d003c082c409001f403141b070f0b040079901c140c601c4c1c5c40d04482840078945414400104a00f85541c1d8510800840030031201083c00c400c091800744000e0030900700050040481400304040c58604040c90301d0510b21900c40165101c0d0004e0003400841c0c156100c0318200d84142070056813110007001109c0740310700c82d4001e601100350404040d00c000c0c5880411710003071340c600c85c10052141c6803c00044c0700355514517414a08030818000c001c0e85a00005005890040640d0809000340c4004a00042e800303070315412040c07047e404034000c1e0154003007030070803207948180544a240c00760b0171001c20619041400d030090b584c07101000304a4504000d0015a450031910281c0100030030161400c10440f4015a40c0100d0025400c200d2070100f9440b10541580c2c2c41c4d0098410042c42641c0029079255010311a405a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251583848 1250 251582598 251582603
    0x50313081e16140f0319050f16090513210e010c051b061b0f101103070c050c0d0506011a0910030f09170a030c1b030c060e0a03090e01080712021c 64
    0x8a00012964080c02030998035406d04440d2445084011141080045008401001881c401d151201c1c20428880043c280041805150030034051929010440064914079403088803180c0340c40d03d2400748801030410300254402818852000c0f0f0f80f1300000c0002a8128100282240e01210112400300107441441801c0400940009400b0007041c1103901207070014520412a04850642400c02000d2040d82c1d101034a01c0c0343c0100074400541c0c803500403e90010745921403025268150841400508035140c40a0182d600358040d40041c421555081c2c0f092a801410410b00c03410640040c000400328880c070240c030000c164545641c50303003c41807900304140c2d50354072120280c0065540c20b02c2c10010341000001d240000d017880303903200f080e40c015840010a017000040c00302c40c4180d20b0f2420742d099208883c0c1102e556a42e5001000225024401d80b1051403003643c84904103882d18034030780010103060704021a9a040b5541c1082900104900314080d01d030b0540304501c188124012400303c012010002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251585098 1250 251583848 251583853
    0x7060b0d0b040b0a1b05030f040218070f091707030210030b270609010f050d08251401020415140705060103030203030603010608011e09050313081e16140f03 69
    0x40c0001c010f10050000d10400c2c004c0000c001402d850304400301100000290700d03001ca0002c201003040603004041140d031050010303080508001d00c403180031920450440b000000980800180ca02081d804888503000f0403001e096581084e0764407080e55110b580910000384580002d101642ca01d9002e0703046448842e070010044400486007113004140e03807032103e203034101c17845c03030300c80050700c0c0c0e01d0216203150503551b0841402d0390042c1800244049a0070010042d1040325050080d0048a51624070040c400e005e0b21000c11020352580c0741030084c03090700300d4004140d0b0340144170901c00c2e00300c007245c0d022141026240c100709202c045080404c1501c6018400b4182c0e001c1c19001201b41500040194000c90064000704045a0b03030742041402c8501c500f95400a0042056004840e0382c015001048a070b801102500d18100e541c1900c403501e03690700d90000315070b42c000c003002c1c191400c440700c1d994541c150310030041c0109060015210021440c03d000f100440c2180d1708030f01c0031030b4a0f915042002e00c4d201404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251586348 1250 251585098 251585101
    0xf100b130f23040b040201050d0209120a02150f0a0c021201020a02010501141509090c0c0a050a03020615030607030e1009030c0b150108070503061504060c0c050306070507060b0d0b 79
    0x120712000e449003400000d000ba01032945049200886070040b84510703008107451526480d03942c01101c583c2e014840c120003068007404024541e56900e0035401c0c0701e0710303100300070102100030b841481052100c02040038200c1c40103100798500b80b000c8900711917900c02c081c42c10002c0703e0141e1000a4100030403d06c150300c950720208101c0181501584542c0c1030310070050380442c01c060032750f0401140301c1c2080118510484180142c1886040030b0074240d4020380c03182c59007420580c002c078078645800a1194103503569481082070509040d0180030307040d041448456240317040d04031400440c1d991513018160008160f41c1e0038000702810400c0c402d0440e140c4120310180121842400e00030b229030b1880e001602c0c408151004100802142010454104410b855801d102d41c0d50000648603600001c0916800c150440c07840001d011074100204090900c079200e0511003200d44c100300c02081d4943c5c01c40d0b8000da00500038490705580103410f58440c95404500402c0c1e0101c0d0740d0100e031005000311401029101d80300f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251587598 1250 251586348 251586371
    0x81e0403080409021206120d0309140607021b040c17090f060c07030905030118290c071406010803161106040602070501080c0a08010b0703020118030906030e0f100b13 73
    0x1001000140507810b070800c080d4448404000004115844600b107548c0300700c1c105c030142800fa0b00a6003603540540110840310b041d07040f04c141004c408130748960068201841e60040c031043d5042d12500c8640036941040351095022000d007184400d401c00d407244e42c1a250005101c1c000400c0f09440c030301c81d204265640c1e42841800003115822000c000ca0200c1c100c020041124141441411151082642e0f10300000d01691a0301c03001070041005c2d64224145050800c400b9034900d0403840c0207c00d061012581c84003203003019140703001c03000e0704c4841d80c0c2c000c0001045040d9001083e10203000f00100c4c0950541510700c2c0600d04400a08410364222002140c005221500482c1e254220303142a01c92422540e00c8806440f4130f03124003e8080301041c8010018001141c49102030f10b8058402e00001407140c0800c9010009120361900850004124103c284521079160240030180f0000400420104840090950321341142440d52101c080d42c41c01c1500c1141d9030702d0301a030884800c0c3c4908000343ea2a19 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251588848 1250 251587598 251587601
    0x405060d211b0503030a0504020a080a080405090612070b0f04121a090d020d0c020a050607060b030f0d0e040209150f0c12030403050a0f051308070806010909081e0403080409 76
    0x4250410115140208054840007944900780c1e50983c800044c0d4a1544c03006540c8008000241040c2d8205504140225a92404224074038006008107205900d0300d1418080040200300140018005c414060001c5084000040d442e0161a0741c0c4001e5610f942c4000020501d034002c0307a1142d41d042c4402068070040c40881454003404181a07070084100703544151400741d030349001e42d06043c01617000e098280121442000a0503100d031000f4440443e107552500082c2c01038000e00c0040d103520381d8500c05217220740740811240401d482664081c083d40040c0c04805880080848140390045400045110859135a4102d0310500e101302c0c1e5205480d180c000d5062203040c0c103d0f07142c58115200715617081c0c0f6040c50700c0080d81c0c0304642c9551a58a80007400b4011218010044480b0051100903c14080024210419400541450740040a1641c030b03150741e0303510303150046e400f144017075240c00b84c604003142181007210702d00711031015040c5d00e03140303000c4000034148100c0e0b0010b032001ca0003240129246205 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251590098 1250 251588848 251588903
    0x3030b13020f03150409120e01030f110c0106080601050a06110a050303190506031f021b0706020a06050c120f04050a02040507050a3f200712090806060405060d 70
    0x65a4101c003035444444e05200031503132000c034003030200c00c54926030502c0c0d10700c83c0e082c03041d440506140108001d0690b06480050718103004100c12200d0001c1003607500700a00748904402064450000c021701d5140c80d000c90400c1e03402d80120010885030071000c3d210070000b0000e0402c4141c1c04811a6500d140c15480440494030204401d01501d044c40c01080340c034640065030242601c0317a0904029614560120b000080d84141c2150303411041c41404421900400d001c200000c1c40150080e1000417020b140850456200401070200108280684042001124482a4080303810081c00c010f54440f4101545010310030320009502605050800c0a0f159025000e041c2c41445a02c0740981500d0b40c049415602000e14100103a00703036070343d800041e415402c400700721880395440c0c030000d011040500c03030315100c40d802d14000a0100f000070340e0008008010740e110a0302e0100340f619040031418815086e07203582d40603103d14030483d180c00201c0c140d039880c0518502c0d140c0d8400d0380840e00341d000b80c44440d00d9092 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251591348 1250 251590098 251590111
    0xc0a03050703140306011b02030a02040e0303160923060f0a03020714030306010f1b021305071403042402090607110103050601050c03030f0403020c09010e09011b050703030b13020f03 80
    0x40345000b10f516100c18000d50b805040c058503098043c8804000000100c03804240c141d902d80308640204000da1035920940940b045d9940166507640b4081c0112180d1200c51040c1c6001c0000c03401d020442d00b69407040004040020203c2404000701107400115207014007000260807800018883c101103405500409070244604000318640251210305a1079000c02c0b030702c0502040f840032031540440e201f01414006c907401c882e100314a040342d940104100c409110b8a114216035244203101c20540c0003005406011003c18143d89945010354503014a0004003030b803400140010a450f03e94038080380c0544415180141419858540c9402d00c1c403201e51000070260b01282c54100400c08552003501103807a1810000011032a54a03030148150381300070010f000ba4114010303800002c0c8281d0300e01c2c88040c000c1c0000c00c14a505030414080c040e085695680e1100084568602a4940990810b058541e8190141000035244c1070510214405461251076009030354400580710b501e443c4440b000d94000c48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251592598 1250 251591348 251591357
    0xa0206044809020406080f2a070c14060415020c0d0302010b0a0902030721020408031b010c0c0b0f13050304090903031116080304140a0c0503190c09020a03020c0a03050703 75
    0x2907984003a0022446039009034400503004000107200003968040f65500100d200e48401d820002e001c48c004c108010031100b100c00703d5800549a82070250f0104502c0c06007002e80c801c03450f041032500010b00c807403003a03100301e0780040c56400c03c007581607000384000c120342f40000d04422814582450001d000300700310700045210318040240800c403030b07000e8030036a4400c2410740c65001d110b000301c1b018201d181200160724403039560200000f0400480600181c440110f030254448121030086220a0139106402010000c010610401c4004030ba403100d022900511074a80846a48c0c9440c00d2011500010420203050341c80001400113004c0190b0384031015841c0281d400300200456100d2540d8144690307000b2014080c0c5080e44c44002c104080c000f50381091080700c0004611844480c02828006145410303509001e010381d041055040920103c000e4100da4404aa0305084d140d17905840c0c540d05000e4410242d0740412034228280c00780d0704076180c3d0708102045484420882c03030010034952104000b1800203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251593848 1250 251592598 251592743
    0x302031504060f050925030515092803050702030c0a0e070e0603010305070303030b0315161101020306010804030318080d02040503070f03110402070309090c110f030a020604 76
    0x3d1180d214080c040c0350341c2000f070315807040000c840c2001d4045a100d00942c10f01d15207000000030300e0070044269055080e07003038008030f40703400201c4c241400341e04600c1c0781921a1002000c0c0304411403540c10721446515082442d101e021500101c2e14052416500300c6d00031581045c00708401400c03040b068440c44803550b03412003002440050200c0e44c08288401005a8031600302400000d001e9048051040e401030100d510300301866262030517065041c0e503810190640ac0c1041d003505c692010900c440c80644030f0013540b0798103040e00020060440144050200f5543d00e10700c41481015149000d245500035080d99103c8003500302d484029400781c400c0e14440d110f200300c009620300c401c00850702102c0d000314650012010502c14000a94080b180407410050741c12070214a68909100d0610700b07030120380c0c4030743c2034501840586150400340668848550310600070141421b900181d96940301e0751068595030010300b00e032080c3c01c00c0300040d6a80c1080b004140e18280c51908030040b4030040004408111511 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251595098 1250 251593848 251593871
    0x605070806030715091a09150702040507030504030c060e03160605100609050604060f0915020109260d0b0d02060c16051f03150306020f0a081807170304030203150406 73
    0x104440501032130100e07001603c1001659913010b0241440c0c8100d0081a15001c44900010b1004e2081080303101992000303e000c000b541042c1c0305140c1d00a02a08041100d418075440107040c03020405001071000f6240d030f5070050403c0e42407050311040c028074040c1942e240028a00031007e45411a48a81400d019180004010740314844850032030700003502903881e0608190341120520030518920080c401d40520002d0010f4110038075650204050b4000100f110f80c1345441c41141501d40e4103200c0402c0404220100c1248200440d03200391020400091005900700106068824a10b03010f540054041844d000c101000b00d11820502007034014000015210000c00c100a5021030040205541022401490300d010b40d03c20100c010324000e400d00d145a40766602d00507644000400d000107c404905082c80507003004945411101c0040c0d050003285214484c26568401071241a050829500100d0300c0b00a00344111001f030754000c1c054800041c01c00c052410b0145042d9030844200b0700e00404101d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251596348 1250 251595098 251595119
    0x60905030f12070b04050c0a03060e010b030a030e0f011803080712020604030219020f09011811070506060609061308010203011815060e01180810240506070f06050708060307 76
    0x80c009072986006040c03106980781c1130103518004204581901c41c00e16201540e6079070b10044001180b165202140c0c2c44020f6105a0a46030b501041600913230103401030000090304005651000c50007074401d410f0b00940100100c520314103c10295081406807900441403003e03400c01801c00f40d01800e090303180c28003a03500c202d07640e1108540103401600b14060018010208040340314240340002e26000a800c2804009408003a080e441005a19000603d562500303a0074058044400c4401c01c03014204919601d80e151107036401420360744200e00000e400c0100c3d943d1181a18100c00007426020000fa803140001ea000303610130b0089004445940900d0307015500a40282140070b0240514140c0d0146403010075540c0c02c8003100c14a05003c069510710b10308086444121008021850007401903042444c0304000303c50344c5000300741c600c400b501c0740180880b140584407011182c058401d0b556a54a500708262040340007080240401d080500b030011242e8007108840c0120f10131429100b03030b90390700c40d610030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251597598 1250 251596348 251596363
    0xd0504260f04090b0103020f0c07030b150a14030307050a03091d012402010e010c180f080d05030702011b0206060f09130b0402030106050406030308010810020315210106060905030f 79
    0x7452040d0030481840303c80e0315a04051120801030402500340b41e45c0440b141626007160707544010b070340d00c100760820603c210038040a40084000c808948485403180c0414000f807001d004a000c626a0b102215045450070130840c0c2c080d80c2c004064860289036441d00a040c0d01a0703208d00c0c00320640403108810301c1d40c16a145070b81220104100c4194041d0b00c0144250804031003010788065568940c0c5112210a0a00070707100300c040c042da1407018035081e0f1405612003c18130340011856000c00001405a03440024071500c4405132030034000d44039501d0a100b01e01500da030120100a10302c0c00d6804032007950300081d8140c011103084401c1080c840d00c401c00e0008245c400c4449079024014061a60049102c84581139007142c0090004590b01d51200007060039036190b54000c800046500004200c004d1082c050f20500e000c4612083d45103082c0508552680903030b04c15950700c1a450f038040f507040d44104030400000343c00341200903c0b000b0340e24070018000c08194484c550090140e46d041004803440441c031349 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251598848 1250 251597598 251597617
    0x61805040209010e0d030c02122a0f010c050c0a03030e040e0c15070312020f0316030623010c0c090501082b08043909050405071503020d050426 63
    0x1440040094100155220a01425014007142c40c1040d03003d41c4a2202c2854a03c3c0e20b0001000403080e900140c100810b8ad403582940f40d0304841d840302d00281c1d142000d2a00d40c1100340790014011809040a82c01d01c122000005d6106403903403000820035400c0048607002200440e4100259100301800b01c1d11864500d00784d551200b0300d4921200011400000750034158060314011030428804040041268080705001c1e4400001104026407044604d145a0340c0500b0382c40c0134400186003100002d100285405102c10900d00400407042691007032140e50303200c50708090f5440f08aa6520078000c0281000c2c06501894002da4088402007030721485180c0c03003c180c0416964140c2034114044500c924003070b004940d02d4142601300700900402c2030107141440c1c011002d0700b45080452400441c02c4d5102d034450411141881c0030080418000715800080300d00d01313800c0d076444901c0402c046009104549100100a140c82c0c140403e018180c1100a04151101d9544614003030100345013032a402588002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251600098 1250 251598848 251598857
    0xa05070603051e04140708010906050a050c070803070e2701150207030305030604150308070605010501080a0c080601030b0f0d030c02030d08010f03120905091509160e091b030106180504020901 84
    0x70400182c5c5075103417007103200501d100741d40d801c41d180c0c0641c509640b2000c1c01a51480d80b14010f200300702d021403007229000b03020410303400d240c941103a44081c61400024486c0061003500e0f40c88007441e8440c2070500c85e5040c074404504002006d10b0200011100007030084441c0940c030001c0080c000c90000500c4015030b6016100c0f20300f1951042d00300000b8008c088000b9a83c0407039950700000003a00e00014000d4a4130802c0003041c0356060000040c1a0320004000030340302406c0803800051990054816500140280f0300400c14440c1c84001c11070801d00c80c03007029005551000301d04107042c0e01c6240400b07070910840c02e8034200b81d41c00c1d00c00c48100c807080c041d14410151100081000a410382420400c10311103003800c80c6155900c03000200160310481c0ca2180010410400403583d28019507100d6000e600d45c2c0c04019444080078005010307840e11651a800341003410301107890848030220782450301116038105503a03580c4840004015560340c00a482190a080201140c286028000d85d049040d041e5103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251601348 1250 251600098 251600101
    0x6030c04120203030c070303112118010e0907090e1302101b060213031103060415020705030405100509090708090a0204020d1e060f0504020306091b0c0a05070603051e 73
    0x24007410240c0d018034103da0500c030401042803107000920000004501917100e020f0300b1182c0c624140d04110320b849441e14552035402000070100b01d035000351001c400c451341040002002400042c1c0703107071444c6c501c1c0310762114864081106948d80400301c50203a411140d007411494483c04909202140f440000940c0b0000d000f002000c264402c020500d20784080c0180e40c405c50400c0e032201c800303c1e1b0107941900200052640d00b88103101080005440607101034008003560303d804c0d1104901b20010b41c106a2905400081090034441d041094078081d0200070810380c4072441d2880050001e82c41020010f0007011140c00207400305e4019030301e4510601e0100050403010200b5400c10000303501080640d5440e03980c0e841403154000e07000e068109400012000003511908141d00603030035240c01d50145102d24010010000e0030784668001641080342c0d5880d00c041203c0c84416407030240158000c10030b580c031031810000280203000902000712071803070300c04002ca42c6400c000312400e0f5080601103030190f8005d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251602598 1250 251601348 251601359
    0x3020904060b03160c231203070201090b010806040c1e030218040201030b0d0302060703020d180b0702061b1b12071b050405090c130e100501090510050a0905040303090f050d030b06030c04 82
    0x150b0369468030001e07411f0f00c818200d0200c21804503041640c1010041c2e550b140c80e102000124007420b400740c0001c1d001800a460240e60f1041c0f10307440d9009580c0701311507c0014950824ec51a102e8000d55401010441000815803040034207010448060b40020708100f44003060313050101d03075844202d8065003c0c0c001503542e0101a400383d400071001c02c3c42c480c7d84070103041d40d903901000d280100c00e20688405c0a41c0c10013120082c0303441006042611154622620084c0e841c0c5010115030906454484d060342e8145088003080c00c0c50400c0c62411000500007800b9000c20a0800a60b80c81014030800341c240c4948980c1484100c82040380c102403130394002082c540c8240713090204284203150010000c55000f02d5002510304000311148034447c8103403690014458a8164014a40d1101d0180440c3e0350345c51410b4006a5041c0e03140c03188580503503886002c030342454030941051424940201c1e5000c60304100d4603103103640b2040c0301164030004e8500b41c0c0c051414900712013200d00420b4a4a946802c0c00d0a02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251603848 1250 251602598 251602643
    0x501050f0d120903170702120d021504020a0905010b1b0304061403090a060c030b01020c0d02090105012318100f12020903010906050a061d040503070b0703020904060b03160c 76
    0xb103001e0b001d00c903211100000050f00916041c1c00105046911901c84003a88180300030b44601c1300c0c00c150317a070300510005242141e0026524a946220094242c000d885500101c2c03455060f03078000d95105400c0200115a6100c200d009144040896180314803440302d01e1101912401a03010300400941c013010108030303e8507424080d54000300c1c0d06040d210401748940d103000899400441c403d011a03160035440040d50b030144410130000380117a0381c40040b040319a001402e0b020050055906100041d00300d05001840021408854106194003685d140e0842048201c0404070b240000e20841008650925aa204d130b005542c001d20345890328000e810200313401d18003075007042c0384068066507906413000c041081d5000d40c034001c288600740050680c2c1080410160044492442e0b0006000a024840040e0340001261400c1d9084903480f0845d0303c5031042180648039801d05245d202e420306001240500e450750040d805004084c61901d50350171103407401d9508150502000e00500c9a800c2c1e40780300e90803403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251605098 1250 251603848 251603873
    0x20c0907020f2505040b031c0c052506020115090e01110d0609060803030403080402060a031103071d03010e03120c12090f06010b16060c0212070501020c010501050f0d 73
    0xa0054880108500100c0ca25085003d0541c01c20400c0c442226070704101060214000380205540078488000000c010903591000d600f804510305807001030001710b0034829842210200d9220044d22240c100f015009180500410111a21520081e2001880b5401489821a82005008101c034024504a00c40c8002c2010041c00c05c140d540b034a0881592980110081000d9808034270001011428082c0b80000c0700e40320b0b00318801c2070b8030030001e01004c25080381d4500d074440e5044400507a241ea0480c01100508284a8110450080442480b101c0317900001d0400354244d0041004032070400813410142610003240d41401e031a00300704001c810904040c800c1d6071341300010201a5280c04416060002d034040b040702d047e40035400650346100c103501c00f400054010076260041c541002088100010000c0c050103000301503944d10710791000b00c41d009112001140380039282c0540c0329965420464041d500c06c034515400341d484c010021a0a15000c2c1c420040b86d5009002c291007050a80c1da4412071005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251606348 1250 251605098 251605111
    0x405031b03031306180e0702030f030907090501030501091202010c050403150b03060c070c0603060302060d0515030d0e03010e030705030a1202090301290901050603070e12010203090f0f010507020c09 87
    0x402c02c40e00340000b074068440802807113035a441c500801c5074044011120103a503040000d60403d6802407048259001040d00d5600020180e10f41e6a9192000310525009455004a0040e800d00000109112065000c00b0350a4000c504000450070800000c03800c03108504603c10116105100034404038200d031500e0312842d42c9002d00095040044c0d000245440340454100c0f80b08c0341c1c00100901007000e000d10f50001055141405c0c061542152700244580c003030201d031204c03056580c00c0022882c03100a11102c0240c2d0001d001d5504c043c44c910300c01807481104031503480c003d40c200214140d0107840042103c08040c2c00501450608404050440d0690b0000d501000c60507024018111290380a01c5003540440c001400846008555000381300b440c0c03085c488041c4102d440c24010001910345804580c0e001e15149010025800003a0000300c0c081900b1150000c550701c00300030400d8400d00003403a4101e402c41c2c0341c02c0303035810b40c1c00c240d0702d5007030300c00445511005800a102d00b8490341001040310b9080360 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251607598 1250 251606348 251606353
    0x80703090206070606080604031d130b010309020a091b140f1b060106031e090c050105030a14090a020a23010311120a0605010e031209060d1401030602120a020405031b03 74
    0x38444e1100800d50340c40d50007070030480d044002440101600810002c150701c01808461810541c0071001910400980c440099031503140d0300d41020301d2b8865440008110360040c07400c1141c58840c20203000900c06c1140203002d640010030614401e40c007804421607a40d10005c4c12524040c2d0585000140f03410566a11050074642c0311007002a503070502030507001c4e042950b00003900c4101c0195183c140c0b941300311200411840c24a9100124800c00408802e1b50820b007803907580e94031000344000050080c04501c00c1241d54038024440014408130703440c043d840c0205c404030304440d140c0c081680a04049014180701681c00203604902c0e501a400440540e900740c2c5100e07040540c000150401204111208000703565a541d09002c15030704091201c1c142d8030181c004040e038501919561001e8455400c80901c03a80c004240504024103c1d0442e20401d182020240690750352840c102020390401d031a00f42030b1001304070000c0e03101440c0d4400e40342180c00041c020b19920740c142900c5c000344618019800d0300350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251608848 1250 251607598 251607607
    0xb13030e2b0609170307020607090e04020d03020f0109051501090b0a09050601090902030c070302010c0504080a031d03070608010e010e06060f0c150709180908040e220308041a07080703090206 84
    0x512880c0302800110318131031580c0d5246040c0c01d001b81084401007050f024401001d805005e44e4415000d841d03030065064500c60030f10300850400b03900c1c1854032003c840c500d43c20802c0d039004010700842c0002241d106a0f444442d0307a601c4100100030b0b6014410160b0f044141c0344c108101450843e0440c981101c01810b140003003507142c1c1c031000e0590780b088a60011402000624200301982485684030a00842c50180d007480c0c00c04600301c0d15501540f4010301080041c5488110411009041e0306000100400f121541a0b882c1006040c061003440340c03443d0400140d000080b0100c01e01d603468494100200000d10f00f42c03a580407614903801c50b5040d85860707c183c0b01a1281c40320350888840c000e0a2517192008801d20349a0340c1a51009030909140c012803c00d520000003400e07000680341039990f103220030602075490610364804260007c00314076a03030465817058800c2c9900601d4507070140780145070201a2020450030300c1d4009805490040009004000003903184d80700303910102a2910003041503292 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251610098 1250 251608848 251608853
    0x203091309120914011103030606130e0403020105090609031305060a121a040e0a0b2a040906061b0b0606030a0605040908030105031606020a0308130b13030e2b0609 72
    0x6800c2d2803032408085620702d28140014204124040503494007440c1480c04050100c01d555120300001d45141c1c0075000100c0e0000c007414065201a001d040c0c0215107119502d800c0c10024068401907840c0d032158042d0102061003440040101c610041000003002a0580b0b440d040c0304a650050500c0c0c0704020003114005041001030191507a0218071080803001e150080080100b260050084c403030040d40404150000510b000755280e9218065841980d5095000065400118500c50b0040c9039500d0010f80499501c5003903009800b0b5940310382c2c40001ca020b0030320001a840044103405058501e807072002514916001d0000c5600030308900000c10415694804030301954503c05080b0340181c400720051205042c104030702401d0782d4100303151800442c582200a0f40762a0049005010016501b0003d6170940f900b9400f03d40c3c81d5401502801e240c50300740311084500c190010200c0003c0d00070300000b02c461801c615040380d00b14110000b016a489503030070071007001001041c1180d10b9078803010007001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251611348 1250 251610098 251610113
    0x150510090608040606050d2a06090b0a14070305042318060f040207030e030c0109120303051f03030206060f01050c15130228091401060503060102150c2106010203091309 74
    0x400323100e00f090010210f030101011212800b048003241c2d0300102e9000c1040401c0c1d0100c03070314088800d4549030a580342c440e000100d5000c0c6280b07056084911000413840101548140100100c69448000855420400340c0c2c0c80608080f2034020396122000d5031020401801038031809030481c8000740800c14214001010905a80003c4070690128103800c4845005042c10300c80d03401c244d10240b9100200c00d0403c240c0d4441c0080004020f810940e0302c40010f001e03d081e404012004050303000e00e0362040c942d68035000b036030f42004440c0030340284844100c9003125400756060320010052800a030840042000b848809035030b000b008002c014010002110158507815a540c0c00000e65040415584445007091000000391703501803500607260403030001c000250310140c07506580032450b04a540e1380703070503004074074004850360802c1c0d4075030807a000d02c9404814440100303030303050845072075001c1102e24a004000340c91007152130a025800401c034a40305481e140050191070100081d0002c1c051400b41c07101c45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251612598 1250 251611348 251611369
    0x12180c0b04060306051009030f0303020403170d0b0d03020303011505090d0605013201140c010f0606020c121c1125090e070303030b040902030a0615051009060804060605 74
    0x4950300001000e0000d10781c180500d0000d04001d8604000e41e40300c010004052110328131000d4425007041101c802018441e40440c2c00031500800c01c003002d00850380301c0260b43c0c0d0004411007c402e103800b0030140395040054000340c103960150061411a0319205c41000588580590b41d02003103410416000f07a6500c00c002850494050000041e5640c1494600c09030494240124103020303400c04418070049070301c1003440703501802c00c1c40d103071f0031a0034a004001100d00908038500b01550030651204021402d03980000102d401d86d500b01c90520002d10144410380035480c40f000b6654114840c11540c081d07018480c07000f04601481c0004c0d040e065844000e060040d120700304c01214101030362807110b8050007440d03480035050421040045408941d103669960300f1354400102850380700c0501d6009a50703158819803503590042c0a54120b41082c0c40c08200502c1002000b03000064514400704140c14903481c440607110180e1200b0b568141070540039980501c0040c003c449868861901181e50385135010f120 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251613848 1250 251612598 251612609
    0x10c0816030603050609062a04140111030c0a02040f06051c050f06042111030a0c061805060402040609050c0304080304061b0503190c0e012303070809070806040312180c 74
    0x100704038204000b10811020b102c4441e40c0c000a4123211a00310722040108a804941c554140352aa4410303040060300e400c60b90f504400c90300d020118600e205004045000c40481d44200c40400030140d00d0041e01c0119030840c020542c01c20420301405c85c100d01d482400d15605c6000b5030440b00811102c00b490b0340341907070440341140c06141010b01c14443c8541000003002206044c2441c0f100b14071800e010b00c0d50b0740201c1d01408104100740c00a942070041c90760100d0b111040341d41d80c0004404a40c2030043c0c1d2030708155800c9000764a40780c00019000c0f554844c180c081d40100344020b241d5121a120034085410142c01503c20030f41ea0141d00801090340c00c08070081c06411780b151034480c80e01403040200c000b014501d80c9807440c1003403c41315420740c0c030400d404c141000074284540c80350b00c00c0805003040c500ba000480a804400014810490b0300f0940252158003100125000305484480940d221300e4242d800a000c28444c0211401202c03894011450450441200000718039003907c50085040c5c480c0e012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251615098 1250 251613848 251613853
    0x40501031208090307021e0f210c0d020d021e030703111206100506070f052b14040506030c0720120a0809010309080d0c030c080108010c0816030603050609 68
    0x2190090b400012a9038004030790800365013007103610740115040ea8580e140780700e480000006000ba907950307006a03c1c2c02d0041c0c094103244051a4112294640359143d0551002e244100101007a451621017845020740ea400740407441c0c00840b650911900982e015000c030340719440000c82541c9a01c00b045000000c40c040e218070801001000d05000d81e400c0036020742c411a8004e0010050505440c5410200b1144192646030741ea14084c01c0c10651110500b10051960107034a00c40703d1840b00750048240480083d642205585c151401c0c00e0f50314000d8400702c80d2400d101804104040d01d04840075651018005c03c0140c68007059a450f6083c81c4101c980022602075101d01c0114242040824100c001002c04010035414100da250ba125038003540e0300c11030405843c1c04500d400c0003003603170583d030401e241d0340307014440040307400000b80280108048040002d0511000003030014814001c11000c0941c07501c4880058035050103c1c80440c4402d000203040c1034407480008001034040203407030b20480c80f0300d02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251616348 1250 251615098 251615123
    0x90c09090c08070e0619050a0c02040207051506030304140402090105040806091b22091103120703080f19110c030d0209040c021f020c07050d0b0405070515040b0c0102070204050103 79
    0x401034030201300c00000c03a0040790141b1100c03030700324440580b220003200d2908009456601c14a8220b40e1504403040c000d401c10b00209801080100016810407440301038142c1c103113680c0c0d4000c10705549000303034801c0c5074401040c44100950b0307040c5607008001c0588107140013490076480d01c0155141410982d03403040315500618840904400410415100c0702c003c45000c600041c1d1003041e0041d0341c0300700c032441581079500e0020070200030680120110803c000350603585204081d0354034144540110138240c01155038000000c1544c400081d01e02d100f40c07268490307951640341001d401e000800500801100280040042c03038035004041021349045141920091b07607401c00c840501c4143c2d0702d0076a031041954031031001c8940e6014402000740111008180050302c842480c1260703482c0410f541d20494004400c820550180701942c06843c1c440c600a008903000306950300280f2025032688076074503880c1d0106000501085070300c1e40040640c4040c0c1800981000110b80008085490070f034401c594044000c82d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251617598 1250 251616348 251616361
    0xf030708090c030c0105040329040803090f0d0903030c03030e030f0d060b030c120a09020d062304051e010615020f06010e0c0702090402041803020304051801030c090c09090c08 77
    0x50002d03050702038001e811100204000600140982d000007012071144468540131003101d581b2030242c194001c0c900800d20705050030100b40b83ea0055500500f00d0241d807981146003000051484041801030780c86c4d500e07052658074211452403410270201c040540781d501c0011a20010400340601ca03101289582d0b80e0000a1a01c82c112181c6503c102c440807070038020020304122500c180c8030b12440c940c2c003802c526070b92600b000c0024048010001c2d8000414000e2200740125a40b00d800b091005810300610511310000c00b098044040f24010410f0748049a00381c2c184200064040001c1c02d40400441e0441d16125007007200201a01c204005a01510127100102001c010007801000d00c0701c04100c030307414020103801c50341c81000c4000c3d0041c04000e01240841d22151300c40d4400d5000001d128081e510b01c6e00d402500c03a406071207424891300c0d076034900b01c840c2100c82c80303080d040369882152481104e1500000c0c0002c2c0444c90380d00001c0c449401000610b01d9401d00454000840c150703514030a618104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251618705 1107 251617598 251617603
    0x114011202070309050405130c1a120c030a05010b0c0a0809150a08090c040b012c060d060305010606080c0a0e0f0d05011d010c0207060e060f03070809 66
    0x6440814540c0c481380020030354100311401d100e6074581070381056118107600005045400503040030481c08107111260b40403126011021814103032000d0728082c035040c0454880c00a03000010070081d00d0002442440e02501d441c0680e5800c140004001a42c3c072028400010080100068090300c80d580701d100180010701454203566230b810190400908800c01684c1c415550302c101c03d42a42d0070318250003102401681a9611f050b15003904c54030081010b510050b00c213200c8100c00141400b41c036050001c0040107001c1c0c030041460751079843e0031821107126521440c2045800414407c6e1072014a00f200c45809051030310703034540990800014820200c0f2500340380e0151b01c4200b40400c001041d00305205604540c440e00c410710141c0315489098450740881e120051700181c1052221500031050440c00b08000742032141848a0b07051100308540c01502c000012030b907020704000003201c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 251438848 251618705 := by
  have h0 := BRFrame.cov_init 251438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251438848 ≤ n) (h2 : n < 251618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
