-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2705
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:46.792642+00:00
-- url     : https://prove2.me/submissions/832d26cc-ae98-4756-9367-1ddc0f4c6292

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 486330935 ≤ n < 486510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 486332185 1250 486330935 486330941
    0x2161a22140a230607030c050a080c0c03041d09010506010c02010e21010209040e0f0a03050706140f06030f0c010e040c0e1201150812040b031515180d0b0406 69
    0xd486184121040c0c494503543e5891908403022042ca0a00c3c01080b001c0608241001981d410000700c1c20140100c0d41c5219009000e4050304c0000020004100003068802000718115030b81c440c0082d0a03250b032151502c280b070401d00c2d0045138501c06041c07420000b849201c010f21403035000d14016901e500809000e5001151503685211600307500c0301140e10905681000708981d02d018440348400541c5030781c0351404010481d0915480382007586c2081d500288844e03404900b50220302d40c54200f482d281c55460811b1001000003072150880004005c091005082d024000280304110440071910a1000403c903140c8412184048501160000410b016030b40382c55080b40943c1501407511020301314900c0c00144440201d500b9110080e551024901c00009400c590f44000e07010f0000200711030b0110600d003489038400e61240140b41240800031841d12584d40080c60042c6034014100d040034211102184800d034443c00040e1411040302944a249040c403280302800c05070050411340982d03581e0344440c005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 486333435 1250 486332185 486332213
    0x3121b090321090a03060606020c010c1a090a12080a06051e150c0111031008031305130b040f06091503020f0f031e07030312060b090d020402161a22 65
    0x48800d00b444403c00300c0d128a03441000950003040d0108020745001c40c003a05011112070503e040001c01c00151011401c2455072216034085404101c0e2540e030369400c0300b420300e214014000c01c217604001c66560f040303a00005c2c9500a413000f1404020a50307496080261912004407a0400380c078450341d80d14400c1c9001f4030040034018000f0401480c00018488142c01c50f04000050724800d03001000340308408030803018010140c40140010340c600b001c031400303010004900348210f0341b00b01f0030200d0400350a96140c00c86400140c000e03009000c1c00504d0385900d800707810b80d401180b024501d06955000e03290b11003d10a42140d4002d4203041c040a03d40b4180b0500841001d461a0144120701d940003000280000c10502e440021700a062640d08626004003140004914100d8103400d040d01030000d00310a034221281504111500700e01ca52242c40803a01a00500c42400219072040c4210024043d030125110b295103020040c408260390f88035000701820220380600c40014502c181d000740001d0f40600f07000c0e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 486334685 1250 486333435 486333493
    0x150403050a2a0602011b03060806010e060301020f0d0504060b0f0a09201b0c0a140d0c2c0609011a0d06091508190314160503121b0903 59
    0x503400c035240e031a11000e400d043d03000c00010b0b0340d00c0e1003888000c0c0840340041985440c1d440c0c10310580c0c0ca00307000c1c02c0d6250018000d0f01892410781e070100d91240c3e070942c1202d02003000226660f03100c170408a6a1001414100c0d02640c03070904000340715a05242040340e44180030001230144240604041c8090020901443d010719801c071540341c05400281e8200180404e0300001109207510312469282c6400c02540318101409902811380038000d240307030440503035100041598001151200c5050600038003071240d000700c203403080c1186040c0d803614018042c00e650161610b40341c0002d4031410b081c0301038402c0074419041c0120340d0f03203052081e801d110701c020803224501c0840861402d03281c41002c002c0740e6500c95000c5006126040410803800c081c072003064101030284504960610688005c3c00302e00e6418410581d0000006104031041401070644400f0b030741080840e42c80f01d015418a41e811101580d02c4a1415540c07407031107882ca00341a00f00ea02c00700d0040c000d0081c580b20850203028519610302c20403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 486335935 1250 486334685 486334733
    0x25120503040909050c1504080706050a03150e0907060503060d06110d05070509040513030f0e0102070815040302010510030507050607021c0b06011d0108060910050d0b06150403050a 79
    0x15020418060101528091380c0948102c00481d410003d4105c00c0a1b00c0c3c28180c2014003080084c248003007045021100d9500340340e5501d49a0301c0044005014441101000d200c40c8003020968881c403148071440b806e4807100300c0d10302c6034031070b102607440340000c88400707510464801e981c400051207504041c0900c81c6180955082c0700b140e07448d40094501c2101c0030400070b200402e445040c1e24160080c0c58003c200504640703241046514000d1110401c043ca04040c000e0005990020707034400c100c1000201075550a45080c4280560f880c1d59089040d20150300540c20507003c9582e03c0c040415400449034007200130210b4600d40030600c281a08042c1701641d00004074080075040404589120040d1840b50b00000103601d4a10700142040c0010f09901d075a02a107940140541d0343c1088079140c2041045503130008030303600c2440280d80a0350503042150040c0050380d055003009030a4027801c9c00394808456400d0a60400f2301c02c0e10030350190348401b40041d40817903800350104910100d0030f1a0f80b904400c8007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 486337185 1250 486335935 486335939
    0x106080a081308060703050403091203122a0203180102150a0f06230301050708130b0423030409050c1321061b020105010b0301050a060f0528022512050304 68
    0x15404c02c40c080b903d00300442c0c5c442040200f0140c0c00130210006d000c00c40d04011404510340ca000303000c154004603d11030183c4d90328480003284e80c00c49884055100341d903c4c0020b032802100c4025284c3e007002400410450002c1c050101542c00854605030003030700720000050b40da6035100d400300600003040003400712a907038450103c0c20f0440d950742840500f0401b410010405a408241401c413080205680200f101010a11980408948810300025002600c940702921207060209401020b480c401c0c003100c2c407021421b44e02e488044050310840307203440c0c0c04004039030742c070040c5050034070840140241c41e00904c00d042c881e0310046041d000c10142a402c041011100302c2d6655400c65084808400140e40b010481c04c1c0c61a82c24041c15000d082d110000c41d0030340d4501400718600c40440e0148409020004261014652295040c2c5602d442d41c0707150341429185920044410726076500c0d4110050180c03004622061050003461003165520301c41100c0450f150207030100703042002c2942103603c0c2c0020000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 486338435 1250 486337185 486337199
    0xa0204060e070f201207022e03020705280203061803091314010b0c011d03070809010c0c0905041109090601030b070207080105010f2909010503060604350106080a0813 73
    0x510039070a800d031071a83da903422240100109008c1c13611440341100c0c1d4044e86040028454088081c03002c400e0304003d030715480e5910340103050045101c3c100032103c80c03070a80c01a001610f08801d02c850b038000c1d02954444e4565140365143c960ba015280c0d6400c2d8000c101c2c0c8106800d0405591549450b024030010b84031041035403501c0c080340700b80c1c0101c22451001c114940c1624081c4500c84450b01d4403015003030381601c803601480d12400380c15405411000045644030719a40242841c0101c0c41e404084048031944603d0343d10010a800d5505503165122183d51800c1d601b0702551083c09460030100500140c2e11355602c02c5005d101c002e0810b021070007038a00c00681e49409000d0305001c1c004c01c0c00700c0c0c42038a0600300804401080d20591043c2d6591000240781000407d0040320103c14080c6007850b620f50311000428141e2089a000091016051111440f41e400208851003a260180c00c0f00a04c0080701d0070351800daa000b8003d80c4060b8000448210000729448000c001c03406145540d05840d903038600d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 486339685 1250 486338435 486338443
    0x1140f060c06040201020705040e0c04020f0c030a020109060f0527030c03070c03050c01050703080f0603030712030906060902040510051e0313030807170708130209090a0204060e070f20 81
    0xa4807039a580c800c0d403d0100315a0140008009407400740c0d01003141d043d000d00b80c0307035079440c1584103503008541c00101d411070b1488000803140a6507105080342e0356407030742140007402010310450640d0340750325001402901915034020301d13020301441d040b940c0a001c0000c2c40e007502440d1628524201d84800c2116400031201070010b400903501a99069030054607608020381030074054404107041000c00c20422001a812207181c54000d450b2004400244c1e5561010902d144a0a075026001e00e101e0000301c2480b55140d008090110310649061000035501c001020980c01680102c5030300000650300150040c0c0715402514189104400c86102030802406204065100751225052200400501010700da002500c06401412916146404035604103030381a5903000503024204020030800890100b01c1e000c0800c3c01d046400804289940c100f03801c80300c3c0e03101502c00c0c04034096420400000f9030b4030f204103041c074810b00c2d060302d8510b00c0007540311084803504100d07881c00040c0c0394181c004200d600b07400c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 486340935 1250 486339685 486339697
    0xc040606030608100b0d080c0106080a0b0403120b0f0409020118030b061e061905070611031014030a02040207020a0b04091a030303130305130305160f08070e01140f06 73
    0x5140003405600307003181e45041c075414204e840d1005041544c0c4001c940c4843c2c00401d402900008043d031201c1004d962107001d04002d0f841041c0342e109008603117040c48180a50340e40510b10a4550b002c8414132a00008295122985040c6d0b001e103104009240a02700340d00305c2e2019034030516104c428214504950a50082c4580090350282050000c101140c01d0040405400400b11261110040b2071400014801d01c1207010805804400c407540d503404500843c00d9418066000b101070081000504107a07816402c222901d01000e803200c50001015000700c901d040804801501500003502e181d000c0c00080e40c00040203d0300551451400141e444148000d40040e007440c0c8008503c0c80c210040c500444c103040c5003c5440780d0820824442d44a00d81c03840c0620300d55050801a8131480061000b9070480004c1d4070103080360141400070351001d044882d01c0f43c02c0c0d90403030511032111929105070550b00d0503140900c0141461200050101c041c1d1041a214201001400c9440c400c0380130000c50401d403c90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 486342185 1250 486340935 486340937
    0x180a020f1e073509060405061b010c17040b060d020a03050102070501050a050112020909330702030712050906040909052d0a060e0c0301092105040b0d020901020c040606 74
    0xc50034408029102c0303989000e010146601407111030450002c4020140b01100d0f5a45580002800440c540c480e01d0550b0000e2074028155a1120b94120145000da81c07040c079040342e5940380c2115080368a001d600402c007040a9616076180f07660301c030b44c0c1e00c841d04036000d040284e2010700304004500503920038030280c011314442d00c0056120301d401e2401c6030035620041c10b80c0010608280041c030000b040c1d03003407001402d0340450f05c400c2c454840544884c20b0005040d0048141407020803214040ca64691040075100e081600407003290f520024220b84a01035904020501807069034403a0780b80307102d14050407494100420302440c183d030b14103c1c0c10440d0010001251982c00076003110458540108864410328041c440303060b4615004c0c18400d44900104e800107201e60340d0f030035051940100c10030408446906c0500200400b00c0740d41080700b003103200000d100200245d020802c02660384544c0036241103843d01c1444c00d09081c09859540c01a40151102e1411489044030703190a940e1032f405540004c0c012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 486343435 1250 486342185 486342187
    0x30a090905010b041401030507090b0c01060302011b11090405030c06041a1e010b0f09030706090312030c0801050d061514010320070303110c070b09010e180a020f1e 72
    0x180c00400340559005030311090b2440301c144020031541c040c000c202d2103105030900e0300060300e9075180e80030727031f15551940c00c6428080702c0841c04078602001544120180c0c3c3c003d0f2141a0800000140b01210002003040184038080c542c0e00280d003030501e84038154003d4411001e4909200c8085a0710381303403104c111000e40f807100c02c100c024180660088040c43c1c01c00044d501d00c030007101583c41c2d05112600103100340144101c0007d8140140e0a02e5426500d610300020700384c4044035529030f0020681e20084c0001e07035804064215a03904039001c0e10620500100702d0301c1c1c0500303d03032800b010403104100969082e94215251b0114110240b107400901c00648200103400b6107000ba8034000408a603092030282502074052442d5031801c01e0304078166589294176240202c0c00d201c4070715881566004503040400b042c410b210012684980b80c00c040c0186400aa0f5548181e03140301781000640241000003a01c3e00b05554042031706500280c0041c40c1e84800d00301c1003440e1035109090755940d40011900316141c100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 486344685 1250 486343435 486343439
    0x9030301090501050d030c14030d1104061b110f0d14011b0306210602090306010f061b1a2a0c0f12031f0906030f0b1810090204060305030a09 62
    0x21540700b11800b400e000d85507000680050790b00900700c0c101c1010058070b03614540b0b80551168004204407980307200c03e88414010622404c21420030b9410070f002da2404a140c000b89140f8003001a44924016900b101c59103004504200034450b600e90764801041c2c00c80c41d0342c01108045034241c10480740741d00e000400000d100c1c06510080c0140300541d01004101760510300100714822001e10a42d400880880000070b0521551a15900901c03440d0841c0e501401072600024074046010018011107005071100d40c0c482002124a41e8041c801041c014001443c0d41b00040c0c83c0180000300344d50102145119a5290303808180e4011060700c03204414142200000300e1070000381c010304ca082c0301008a0300050441c00b05030845c1c80c03507178000140200784554200707051070301c3c101c0d548404000900e881c5c10200940c94907801d140c04540720255054a24000241c0440e440e599841c4142d040704a180002c1e0203c42804101c40001d416481d5059a02039203464000c8081401031004080c0706130541c581c0c81c0b00d18 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 486345935 1250 486344685 486344699
    0xb0402030f07030b1f270303200d050301120f150204210c05090717011203030c0905101b0c0b0318070602031903020c0105012612090d051509030301 65
    0x200c5548131075010303c4880790f0004841c282c5150060203100641002c40504072450201d05103c00c0000007074440c159449400001e06401c03000164000802e10800009070900703200803070f40c8890b40410200000d0003080100300703041c90890081c642c107129078581c00141c411512025810304407104170300d4001c1e0740024108010a9102c4c5050350b44413081c0700750003100400e83ca800d4840310711841044d010701c50200015240030710030701901102010401420b2903c2d611003402c00234240c3c205000701d01007403400030403680050255030f0301d030100e820050410544a406510031600404007112001402260303174009130004440764a003201410519094035103900d000c052029000700a440c105010741c00a0b2810b0080d1540403040350f0200c2c1d141c10814034400034030f8008030001d1040103003107610b95180c130001003030b255030428040070104502e0700301fa0150010402c2894650200301080d540d1315100b00201c0ea442c0c02c115071628041405401039400e22070b649201d022030075100b1103000c100c503003000005203c25 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 486347185 1250 486345935 486345941
    0x20f0d06240c02030303060409080c01050f1501021b120709110a260406050c040509070c030216060c060e010216030e130902030a0b180d03050103110303030c0a05030a0b0402030f0703 80
    0x70500030320380310b40b103a0324980100c0c0d280e12001d04658016a1105911400e12028200721284200369034020400c1d883c20032154515400152042003c00161141842a540c0300059146882040d214070211000041c020840c02d984940b00c18802d6000300880000c904488d441500d00c400484155140d6600c1040c50003083c9905107020300e2210f07103007002c0072041914030300f031401c1e4000c0d8400e00c00500b03600c612203140658091a4007032644519040200220076030311000c503104040c07080d0210340350005822440000400709c0e018400010b0302e02c05c2c40c040881c0168200c0121002c22000040c80c000c02034a408001c48003c501c19004074001059074074079420300c4650b0f00c060341d003c106e08000544140d40002d4540b1070516002d0802d00d28080403510b0119021040315840362100b023150502c240d07800d000b40240109100c15520842e468140c8220b1b8240402103e124501840056180c9a180c9070142d400b50405400744012a41c0c3c0c83c1c04103050389a52005502480e40850100610311340100d00a0503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 486348435 1250 486347185 486347249
    0x3060910080a06090201030b04020703022512030c060f060e0702070902030f010605090a1809150504110618060d0912030b0901050d0305070204140906100302060d020f0d06 75
    0x4828424400c1210075400304000480c2c1e0380c001400705040000780012405000c002ca03855a00034400240c42e02010307000100301401b840c0306e200ca91308507043c1407480320501156215401c040c25680c13114100092141e5001903105201d54000a8043ca40c0c050340e601711401a0001c0d040d00050005116400380c041060301c4c010192401c0c10361451034070080c80c240940d4180f060b203041c03000114504100c0d6882d40214030180c071034400700f0000a80400006400f0389805402904c10900d00d141d8400e20a0340350052503c1550040044160840224244a0f0740e0388021000a44201c0c60f0b801c01c003165071118001c040c0343da40441c002c58100c10b58107200500c8070031a1000d100340f5141c84c40d0b440c01d6880d03800f41c141c1110f50803180c0c0040100c4500b800c0d1100c0c1315443c002903001d03162000030007901020040c03d0780240e080100300e0b00603581d003213511904540c103400060343c44079003840140205092078004220301d4a4071069079007031400c51443c800990f04035400280300741d50b9103400e2540c2d0f1a803003400740b42 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 486349685 1250 486348435 486348451
    0x40303260103080405090a020c0d08010f0b040807060806060c060906010314151512070f0e0106050f03040204090c0815070f030c050f0304020409170c060a23060a0911030609 76
    0x110794519522082c0901c81c91203001e0050a10400080c003503089a410359021010b80300598180090905d0003c0840809000e40004911240b0010842152150035502551140d00051940c5400c104040c0c48802c001001d03d540680e0420100124071024403905020703000b000001d01d4654194600b150a00303600300c3c02c00740182e106148000140c810103860350340240c446407000407401c40810110b040401d000800020700e120301240000c1c0ca070300420a142c1143c0c150301640c4e08a0340c0398101203915105d5542d100041401c240041000742c50260311100c40b40c0c0c82500c516540580e2215018103200c1104061004105200c08202c8a60b4100c0d801d000b12075868078007080030306140305001c1c20360b01404e070501c0b41015000c4001021074442d40d218442194011001e55400c18498000d81380d01d60100200c0b0500f400b410b0003050010416000d8009030100580c802d21140ba0042061500703284001c08050340007411034800034a0100502c0750020300c11080c60403959914180301803002c400c1c2d02520004d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 486350935 1250 486349685 486349757
    0x1a070c0b03220b0f0402040e0f0303060a140102070614120c070507050a060c0308093a0c020a03020607111002150108070f060f03090213050a0f050f0604020901030f02040303 76
    0x2d4000303920401801d500803481a600780540c0c1303550010400a007289044015613128403544840f0070040000070b94407a820850340e400342c0c0d07904c4080d146050500180204d001da44200402e006941c02441c0304480c4030003901c107182c20500020505004080b042d2007450b0503400020314a02408014084003010305026103460b4890382c034001c1c0080185a00303c502600b00441e50001c03541c0c50f5000d1040d440c501d65104252601094407126036500103510355100700c540d190b14015000b1280c000e0f49862000740d0000c10600d10a8556001e000240d48141e41c1240c00c007540d018000d6160340c0c2d41c246c40005040d10350050407500c00085182c4004003040c1c01c20310b020340c40395100308001000c117441502038410b030b40740080c111700446009501070651140c0081d031289032041980c08100c0164007542c0326101303400303040c820484020308031400c680060b41c0035a000d10652000940c0d81c00d10350000d00b00208103140005014031082340040c1283c11a800031000110002c101440d128070140030f40d03110385405e4001f1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 486352185 1250 486350935 486351001
    0x30c061d0102070614040305061510020606100c050a050735032208120d0c030c0903030e0d02090103082115040b061b061f0509011a070c0b03 62
    0x80c0d81d44840c4d21500d000c11840441402c1d012a01d20155002940e000048540d18100309070414510041900b00318040c190600c04202c0180c4001550b6004950207405403480901c00d060880b06074003040e0060f9080d1040380d0410300003400400c80749005013030611031030070b0781d140c20b5184046640e42c0e070303c0308000c9603030000c240c03c009000841210031122a070150500c2d01a00c2003000000c800b03540d403108030140914804050784c0d00744003004002c182e2080c0d000304609902c440c020b808442d039541030301c0006049201d050000a0150200030540d0800400c1c0441142c070b180d0004000c2c0f40260000c031010038002c111440c6103412044182484070911840414034070303240004031000d0200303c0e81180703d1521038401040d07980320101180d12101a030300d45203800c5210040c4855941505580100c115524070401130040100d039800e190549400800c3d10440d03902e481c807138599074200c000d858210050f0400c80c81d40020f2039010680000c1c4201d41d01c0c140c89240803070307410008119900428400503070311040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 486353435 1250 486352185 486352187
    0xc0f0706020a0201052502060414130c020a03140f1c0c051606020a050f030405060411030712061512030f1b11010804031205090a1511040b031f030c061d01 68
    0x242d40c02519903680205030385903a80350b0769078030880a10029402234800035000c00c421504a0b050710300d0031000c0e60b04800d01581d901800d02191415015800180c020b441ca080002e88600c0c0e003e40c42d02034a4262900b04600c0c6910080d080d8084144e8480c400c0c64001c1030079150700a0f0103001c12007200ca003441d50604020032030f001e841802440d03004020681c0012510003490045081d121190b040c074010b162285014507015030ba4041c103075426580b00c180f25280d02079510300040c080007030380d40080422150019076603a2601414480452408040c0e49000108207550190202c900a502a07580d0301001d408140002d4503070000316001c500c41d2000044c1c4040824200705401c86850380a18100c04c503980c40303013800ca540c0800700914620b2a820441480784400d000034000000b0740c054581c002050000c41e44040407141c501c2d03445c03400700d007046c00104110f541d0400510303413002c09180d44180c60440200c4d40407d10031144c008450311800f401080c40010f0740b0030b1584074580720340060005100c18601c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 486354685 1250 486353435 486353437
    0xa1d011104170606031e10092d0302031903142809051e0a020a0905010f08011a300d0906020a0b0613290102010c260703110c0f0706020a020105 63
    0x403510744c02c0e000400310286c1c1c0e42020407400680c0b003c04002001000c05620f45000101c2c0f00c0800c0b2038100f50740c2a0f00c3c62600c40030702070100615505400843c0303001d4002d00c1c011525010040400300b41030b581d6071503910f03103140e41d5000c5200d010b50001400504c40361500740048680300c005028603083c50800750720005040010303070062582504a4001780c140061501c0d510b49030074201c1c02500078244100004103000e00f600114103940b0184070008607146c030340c000d45088404114029440e501c518040d144181860000200125180e4100c8943c030030014080d0300d5070403000002500e00358044000c21082c0e0f54002840d03400307442c20340b001d0903041078a500e503111050710280005100e03640121000305484c0b01544a24122a8501222801c681c0d6244803047d40145490003203015500f000d025940051152180c0490145103612152030080c0047e4017400e4010002c1400060550b1b446000d52a28102006460500100f400404503400755880e01401e20105501110a40d840540c47e000142c0e0400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 486355935 1250 486354685 486354703
    0x204061706130b04241d010b030a2102010e0d0512013c0f08061b120103030804020607080724060812180a18050606040b030a1d01110417060603 63
    0x26003005200e0408010095003540f8a8130b4030610321b0302d030a04807404201440581c002c0c0d1704000800401020109040d101c451681c0c004055281e14028010200c08403000407200079828070000035a20820b2512515001130707d5841350105902184030941c100c154446640034010f11000d660107208030021042c0307030301e070011060611105c40c00a910b000b0100f03e10700307000420451901003022551010b44940394802070700e82f00c02c040c0f0300c3c041554440500200b100c038048078009440350aa0f103551400c440040c006801281e100204000000c046204000a4540540250300e51600244810701d03c1700c9e8003050104c00c1d5803103030424000f00190a004a64440d40d01c0c00500016070b10036a40034026003d4243c90003032580300c03913100f8010880070b10b405800c00d001544028200003503100d00d410013140340910b22407508901d2003000080d080f0016a0802d111071000c91100061916070401e00d40c0c00d4842c050080d0b052002d01060800c1103100d4500401701880403c0007424907402c1c401c02007900c43e4056 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 486357185 1250 486355935 486355943
    0xb010f080603012a020c0306040f0f060f0203010312021b10030c02070b0a08072601090b1206150102160509010e0c1b01020315011115060307030204061706130b04 71
    0x2120000c0c01d5602c00f0b4001100c4240e001c81e4144880303008154030800c9024080d900b1005101e11240c101d4182000211a0302030b0740c0020340740c0e5410549079075200760714500890440780b41d911030281002410040c00650302940c428443c0003d1919520030091500c1106e42070302c0f22100602401040301d448901c8120011100d918010a071255080d000f64503195075036001c503184031000203805441d250f022030143c0c010610b0b603a070058144401000783d20201d9484080c001c101051000400c00c2e122180e100019441c00a440306920300000e104203418071200b10360ba0341c103080445640180759a81803121015520003192608031841c24540403981c5068140038100740b0008880c0460490185072050f607030051440004042c4011140c404507020750000da40300510703005a00b580c08803a40c024040c4072a4000944001d002c1004040c00e5034604050250041e90503001d036040110240e00c07a130140308050032036013490076821a80d0315030442c0b034201c0007800e50703140c101001c0840e000103459641d015006500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 486358435 1250 486357185 486357197
    0x1080709230303030901150b0f030f1008190203100207170706020903030c070f320613090203010315060305060f0402061603020f21070201030e010204030f1a09010b010f 74
    0x903808800c1c1140035005942c144804003c0240000054000c0c1c040f4030040a0041e070768540e2460380e4072a9014140c455446124113100154504c1c89900c0810346c0001d00c44c0305003011036940c1c040c903810a90441200f00003620005482d0082d130400300044110040c17603810840c03400272503850b094000c50100f46001c0940c030002071000d01307000c09601580d103c141c000782502d0f42c03031000c150760654800040c800d00045248040000904003054a48402604e21140b41d40e0503031851020f2096036405054046680004240100c0d03042c009500401005001d18201c010303560b5041d8144625034a02c0750203241696030400106000044010402e1500461419080c0805440c0c502c00981640210110f6004044404510809050740040c44a1200342c2c010b060302c02a80d44215025040d440900c1001c1c081401003041700c0055110342c0c0000541048000010704007502da80d15405100e8080d001682e08807145884140c00840c240703c5160082400030080101050010000e0007924107001c440c014052 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 486359685 1250 486358435 486358469
    0x90601051917031e0705010c0507030e04151a040e0c19050a11030304120f09080c0d0302030d050a090c0b1c05250f020f07031707050f0106030f060b01080709 69
    0x801c00c04c0c0c58a45811440304841d004c1e02002100c0c20ba04201010794481d8203103071105a220b4020301c100c0e203002e034060382e0f400d1140d10701c0028803020b040301e202c8110b1000c1035000000b9041c00201c0c0c5461000c84c849941a5480b890315426200040d40507000030320300f00c01004881d40c1903062002110145000d0308002d621200c024105454101c0411507801040c000007080004110558016196220b01500c0e5824140800c05d41241c005020b80200c1c2e040e0782c00030075424076134640140b00007615442441140e182c000049020360603240c06a0b10004855241e50304081040141d0031031001500a440c3c5450520f44072a012901041580c60301e406003507925804120b02045030100c200003c100d4640000c000192b042e401001c44c00303602c0c10040140901c0706400da880c0d8003caa4001240e41005a8131900100811301d0aa40d900002003214648030310403042080038400e0048200460081c1c000001d501d000b801c040c0165260f4a10700746c1081410001c100c150380c1c0000c0e82c1c2c41511250000040402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486360935 1250 486359685 486359729
    0xa0608190c0f17061516020d11010f050a0f0f090806040b04060e0708070905060303130e0f0f0f13031404140316030b04030309030c1a0906010519 64
    0x440c00011411299040c03901c40d68400c2c1e004981e031055200c2580d9001e943c00c03890700c41508800e6058803020b92000e458201441c0c090404800340841e00c003005c4602e1031000441d40010507203100c00304200d42e202501c3e0030000381582c000d24014203040d02410414908034003114010301c1b5600701d02c40c18080c4904041c042140c6849117608801511500c01294058107090800506c0c40d2800c0b14200c0d1a00c1c1403104c05124114003050380c0080341c1c1004010050b40d030524117040c3c09804010700c0d042d0180300500c040340600110a4980000702925007001d006820720340102130132284018480384141c00c0c54402d02c5402c2c040030b1125544494841d44c0b5080c01081441c044034140800b0300d5200184101040c08141345100170004807205100b00c08450750204900350030652490a44006000504172a002502107402604901c0c5070503c00d1401d01c840d01580d40c1c8241210302c8401b044501090598104085100b04120050151004694281c40001000c101d1404940c503401040fa08203025440c0060348 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486362185 1250 486360935 486360961
    0x1605010b0a150f08090a14030c0d020c0a0506030a2703021903141e0a0e03070e15011b08031e0601180512010e060106020f0d0e1c1e0803070306080303060a0608 70
    0x265401044074070004034147d5603503074940000e40003080500840c00080001800018031402c1d440f4007400e0014450710b0101001840d42005042d21502a2541c03100d10300e400d01142c02c40d485800300b85414005501c130f401e000741b0b8041005407000c0c40902d0b80c6048404030340c00c10b90841602c24540d14450340d03103c00128444a04030403000480c6442000706d401c01c60260442c580c04a02d81041d0201c1d000c1d250b460310240306940b01580d61504980d02800c082c4035951042d00000d8108070000c003150010245641c0d800025442202c42c080e00340f07810742c9507100501c030300f151440c0c00400900e005d08889080303880b9804180342900c100c61041c2566484129280307000e40111042c00c002c88213541066a4800000c1d483d511103a4802e05940502d200401141307014041c090f541ca2405000d0102d40c02c01c20306d140c8841540444250780141044050341c0c0c9035809522030b078010b10321902d24191a81403614000c4c054030095000081705800038001c01420b40c07100051201110b4003480c01d00f14036129014040c0750 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486363435 1250 486362185 486362203
    0x3130b06011e020106170304300c03050706030e01020c06062716020f03120103060f020c0102180901060309080d0f09080f130609050d0b0a021605010b0a150f0809 71
    0x108610014042e42e42580640c08581102d488203100400c2030381c181032241e240d201d90b020f4412103400524003c0040b2025007056400c4c0701d050340d103103183d02089842d0b0b05040321959000b2070381540568020301001d9450700038480791080c0c100c002c4d0305000c0308a075860b840d145d00a10150045454400d0813043c0c450000d603a0580c4079014400041905001c0503907035201e00491740840140c89440300ca40c104010010849018801500c0c5c5080b403a421a60703048050000135041281385a0280f00c4c0c02c12612080c4020a40103d0328841e040c4a080e0300d200b807121690059000d2002c1c1031914000c000841e905a0448400b03868000f80041c00035036044c2a90001d0030b50307030809080c095000c5070041151000c980200071000d0316406035201e8035900c1e0001c841c0b10314140200c81c1c0059a61a0f1100040d0b5081c405a402014142025090110900001030f042c0d16000c0150b62580d16260b0044175414004400b5000e0400f48280d03460440c54088017410010045055108100038000000c8083c5c40c180700c2106 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486364685 1250 486363435 486363467
    0x4140d03122901090305070b030a09200f0402030709030605060a17060708090619021c020d0b0a08060606072004020a03050103020915090703020912030403050703031403130b0601 78
    0x40b00d0804400c4010120510039001c0c0107030701451081c0c145560140a050040317aa00800800c00c070f90400e036086501c0e810140031581c100751544c08400c0050320703016880c16500a420346091840e40484100a02c800c1c101c09560300992041050050a55124030f2403020789400038008a034585900c0045610a040c0b03920030805880e100044281c0c0000100e00b090245880d643c0c0c1901e41e8803101180d0352140c0098031020782c0c0c21001c1015800030051500904002a0b4040310301c0150381c480b00076101071f6840b1448a4400300d50355070400c980d81c41d00c107440c8005050868020845403038081c010900c0d601c542200500702c1c58214030486800050101c080942000c064400c0d9201c60080c903014001d8502070100303c3c031809842c07000500240340d50704181710301c1708002d01a00e0380343c441e00016002940000c09480d000040c051104c00a12020001040214420b41c0101000c0d403440c240142004410440000c400c4010418841104201c82040c1800341d00400c82c85c1032500d07040c0050300c0000003941414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486365935 1250 486364685 486364691
    0x624050906040e1f05060715090b19381906080117011b081819030f09080c0f0a120f0606050f061801050705060f07030b010504140d0312 60
    0x3c100d0000105200e401203090229440b00306107885103103020000d06004090308071005110000105138010514046856072180c0010141050388480d91284011110103400202610081140c0d50440c4a42d921104000081148034240b480d900ba042402041414804c041440c070040d410f03644440010b1100c040145140106a98036900034161701024498034450150172100400d8403081806500d01c642e0740c540d0418030000e420001500c1c108006003031440c017000c0300d500403061100c080095080110845c8500c0d010903105140c001c14100400031a8420803c03084e0082000c2d40c00042e485240c0d50302203506103007001101c004101c550640d40e200388200380c030360003c00040c400340d0380300962918082d000500540352544140040d03454260080c540005c41000142e010300a0081c0840e051501403400c00d103402040d0b1a1750349010800d80f008007000729008144804a0340611903a052540b003030914608044c0381100810040c004003080602842c0480c40580405206040212031050041c03010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486367185 1250 486365935 486365939
    0x130b0613151215140601180f03140601050d0803040b1f240203180f031e07080708070510030c11010e070608010905100303051602130519062405090604 66
    0x201e070b9081c60001c810f503440d56403507200b01084402c80c00f5104070540051003008150300d6190045501d42c1c000e00c4804100c4040010125404005855440c021401003240c03081302003000c03503200d007800c5041e480350340f180d10000e00000005500d101642d600541210202c0056540c10505031000b45200c600c0351000444464046080888440c44000c84c1f4004c4510007a004048081a681c900c201000f5004070b02000000c401c181c5060904041d007114080c05842030218102c00405540c521540c0d50766040d000714000f400504001c204420003440404000d2032041d02e0400400c9110482801d05020107494000b443e80d40e0f4054449180311180040c0200902c1c42c0d11102161190502e002c0c410000d03941c1400025500c9007400303094082d0201a0f40c24142e6440c0d60f805441300e90206081500900428070310b9009651014810021081144d10116091510284007a641c0254603104801545003d1090101c80101c41784a929001030002c442001c0104001c207440a010790388e15258089400030300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486368435 1250 486367185 486367199
    0xe1f0203220317010e0a0507020c03030301120c08030703030e1009020d06050703090b07090f061e030e0a08160b0c07030e040b030c1504060207060f0c0b0a0b03030307020a0506130b061315 82
    0x907101b500c21302e030108025100c008080b0b03200c200036a40140d050780280300600030031000f074008140c0c0701d1061034803020381e603a2401158215003010005030040303603481403c12000b40d400e120445c1100300c17040701080100102e900051082140e8000036101c903503101d00048001e0700a503c03120744240c020020b02e0b154a4400e0004100006900501007002d00704400054428001c80c0061010400e461094851004401c0e0032001170401403401070740c80c810010345501149014005203090740c0001844640b03107006003002043d507207015003844a50343c0100030301000700b64410407185c040305048501203224030401c1c000910385030b0b103081040c0d48004a400c4442042c0c0d0054014021a0199020740d207941c1d58815050700d40104088054010074004025000010079440200b54026400d80c0d000441800d0300020034607523001200c442015a00211509051003005c01050354003002c0280801413000b6a540c4083c04840d02a110a004240241ea4402580b216400545080301c501100c1c5010aa580071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486369685 1250 486368435 486368459
    0xe0f1810050a0b03011703091002010f060e1e0a1d06090c03030a050d020310170607031a0303120411030604031e05040e0f0402040902040e1f020322031701 68
    0x508100c520030030000c0080c4604082600700200c40544498a045a280c0b141341c0620844407049842d440c00100090a4a980d80e05141c0c140300e40c0540c00041c004d01103a40e4a4104c2d04103820901c2400061020800c1e2840241410040042c44148006440e1641c0c1074100140410102c409e80381441c54090340561507001851034800c0903910708a8812013804000d01d900c0f07103e4001c0b6100001d004020b040c01403e8160000c58028070880c5102d000b09550701030540480f40100352803210340c2c201c1410f0100a5515008400c40004201000d076009001c0c0c0380060fa0b244101c1d24000724240e4000005000e0120041c2c00098548c8050191400b518040c40c00810303003c0021480e01341079610b00422000385100f01c0603031b0180e40381e40b24444042d48807102030040c1c40c00005e0040303a005441d030280d1070060325070380a038202d0703445120000c0903080b42d0300800c1d10f90a50350581e1202c50620600421030141500702c924640607030744001000b07106416007001c031803442071011040302440062000103501d0b91065 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486370935 1250 486369685 486369691
    0x8011e090606052d0f181807030f1a01060f030b040204050d0503041703030f04062c031801030e030d0213120b0103060f09020906060a0309060f020901020705030a0f030e0f18 76
    0x41415407a1304403040400003074541d140c042d00c0d001700e0510065503d021010450076000646020b20040b011142040c5514041c07003604211110800320401c0c60400c032942c00c000b01030202c6481226003d40c1025002419040e5800d450380c10140c98015050726038a40c0e80c126009031801a01e02880030f0101d0501c0c0741d61303a0151180a401003100c1403034103109070340030080d0ba0007242804843c1165480e85d803151400b40840200c00d80c582ea600c410032114600d11100c45050700c03545031015586030341d86002e003024140c600c01400c0703040c54240aa41c0f850b0300400b004541d007d0441740c400503151a40c603a200d03000c51400e40c001081040e2010b03200410310128000c100d048a10484060260410303045a007010341e10040c034000c4d0048a24008141d80745802d41c06010102c0c100c0c078002440d001e80d5180c0e041903495803041001110b6001a0007941c0d5681804004042e10007940244030201ca00e80d210324451000c01d030040d0800040130b14200e655a540d940d8406000702c0100300202c996040c24034200d4091003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486372185 1250 486370935 486370999
    0x711090601020303330415150509030a12050c10050f130803070c02130c0905030606030114010603020f1c0f05010e090a0609060204210b0108011e09060605 68
    0x2400900290301c000101c0748508514200050a00d00701202a44010180c4504d102e011020780d0404d203d54942d88900c4600124017904910410300d000030711601300e444074400008025042205441d03e031030014103d030302d480d0310151200d5030003103180c800c6130580603041d4100c2c03d5020301100f00d00d0522081e00014001c1c580c0c0b42c00101542c441c210511410b0049a0000340905010710000f02d01701e00518800106074000340115020822101c6940c007110300426141e4042207440c4028011420200720499000405900800c0754101004a03000b81400520850040640000344280c6030014081555050502c1401b0544107400b565480c4019003d500500d40204c1d241a00000c0c9400d07009e00175030300900d0801d0140603598825100c03600949030000702aa101342d0200000210704c0342c0ca40064a12000820740100303403040714508203c0e0f0301410b038012586a81044001c5510710701d010550384903a40b02c503000041c0481c146ca4000042c0025502c0b065006580800c004150b0006880c400d120f0110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486373435 1250 486372185 486372199
    0x10e190807030c150c0605060301060512070306180308010509100902030705032d01150e060403060209010f05030603150703290406060c0506011703070804080d08150312030712020711 80
    0x11104201c0700b148140913200c0000c4d840a0404000c500240d100540206018001081c00c0340c0f984007260f042c448200245c400ea0f84041c10030000c0c48068821050280f0380d404222010506c43d4800516600c0c0c107000d510f10030310070403004c90302e04044c4004520040c6000e03103042d900d0b464080406800d6405c21212001c510035103c0a44904107288058804103000c02050300301180d0900081942800340f0320306880a0202e441c1d50020b8503070718003000e04002c502c584000b40c0d03103403d034900040c400d0b10359580301030a010b800c2c01804201d42c0e001c6603910201a6500202400e540c50001c21809807403404103107a0b456004140c4490400484144840c44801c16203042c00344960f1550101d8005074119005007443e04500014003030800d110601c0104060104101e0342017142030b884004444c0c2c40303948441c226900c451001a055a040003045a1042c020400c0e101c5003980c0c04042a124030307000044500c1c0e070400100140c602801102190710340c0113003030800c40d1142100d140c0310f402e14000028207807280324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486374685 1250 486373435 486373439
    0x60209010c17071e050d23070804090b010507050d0e010e041503031103070305090603040f0218010306150b0a11070812040e220602070602071e061d0c010e190807030c 73
    0x1300079000e0390b000d55214005110301c1d040d001c0200c50000c807941c004050303482d0000d19510041c9048001c1d142890190441903944e6240070f02c40005c40d07054095107810300c1024060000401c80103e81c020401090b824000c14101c007440040391044902e00c10264002c3c586910034228403079040204059905c02e031520244010401d004035030340d008600c0014002030007080400c440e41085d50155070418480d50087d546007945500190a103c03401a2010708c1000f21001001400128003030b0301d51145100e0f01083d02d250405400b0300c203d110b80e2003c10180f069840e00020821010010980109040e5041e14081380607014800c2d100e510074803036504c0030300d107038400b04519455114141880b440c0c0c8501500b41c8182543d10302000c0d41000c0740a40c0c060307500b1700495022650050008000c20f190840800c0b442c0224a80346d4112003226824100841610681401429000440c0011b100b42402d00c040c842610b500021450295910307900001d40303840d07000180c6e80d076002840e08160303841400d41e68107a0ba = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486375935 1250 486374685 486374723
    0x2503020409110411031618050603240a0e01050103092604090b0603102106112511010e040902281e06080705090a03030f2a060209010c1707 61
    0x4042502c9802c00c981d1b024821405550155182d05940300c904040b10800c04e50340c8002620315081107031000c10348286200d800428414164100300c0700542202d610a815017000c4a0401c1d80c481401080c0c1850350b9040c004061103460340c800450211035803040e8180c101e2204090049400610030600c0c0b0301d003070030300444980c907010050300c0c4185442845842c89500e024003225050210300401ca8039048032030340400108034a03005200041c0c591a004560794260030001c44080d0b001d44030760041402400724480d0003c0c4101c1074154641030240703001c6952a41c50b000180c000d2450000003517100031854662225504042c4207c404020303807401030900c65503100e60300742c098940062903a45000035a0b000f441058000d40c540d54110f07110b4a011410000e43d5070120b1070f0030304150000c2d000304036401c2c0c8001c40d10760700c01440300540c0c0030b501ca10703800c2c589403100201c80000c043c04010306858022880f010381da441008190009a00003080d800207800006c403113901d5038442c80080d40e4030141007a80c2c142d28 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486377185 1250 486375935 486375937
    0x90b03092515170411010c05060106091d1e07020f0303010f030218071b0f12080f0a02040602061302190e09060a0b01050d050601031104030803090106050d052503020409110411 77
    0x4404107440c04001991a17a443e0308210049849150500c202500070b007010610400c940e034040c000c2922030400742400d0400f0a031410f03101e5001c2d1501c00a02da000c200750400c03050002e41c02001500e0300c005440c2c5513000141e05000383d8803203901480c4130100000401c220b2103003420040768000c0d5aa2240000a55040e00b14024215580804501903000003101c2290517071240000c40e0280544182030f01c89a60351104801c1c103485071900141c0d0140c01c0c49159804032607825008410f0440c11858640783c000003948070300005101030001480c516500e000c2d5150002c890307540c900000703004140b0340d4031144842d60982d425034001d01244680000a00d10321a02c3c0315138110024161034050510a0f81d0102a001d048000c18603410544c840c4420308203205446d01070009103102e604215180c0c5000e440c0c003404c64000c0e03400103200348122501000440c4012494001c0b8000700c1c040307107814400c51601d19038a051581d2000350014035040e03046007401811082000e400348100c8040c004000441e61403000703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486378435 1250 486377185 486377207
    0x1014060f030d2613060510051c050102042607060e09060d0510050a0f05130f020d030201020f19020d0201150b090d0501050a020c060c030106090b03092515 68
    0x55002281581500d4041d464048400d6150404009040d00c03c0c801c606208200703907014180e05000395000401c201a500406a1001c504a444801c1d0b80c40d080001d00003142e11001507114072500e0305c01a080c404c00307404031409018003403046d07290301907c0103d600e554000360498038824010351001007102d41c414010f0142440004040c0f90041c0c883c88100309000080c10740480781846100c07901850b251040c05024802c00c00c0c2e0500241d0307000c1006651040c1d40d4001d012100a0310241040c50000d80c20b84c00f9240080c1d015200450340c00c006107001e074020301c140039080e03804840119218001e1501c0801906009400c1d40c2914481800c1450a03401c0c0c1d40c81e0b00800d219008118824810042c1c41d03005401c1c01c900041140c1c0380241161507090842d03005075900451280c0008041d41a203904225494100c29010841451507250400c0281810b243e03016030005d80b1400404516841e0040001c14101200f080304400480e080703507c8142070340b05c28403d104294058441d540c446501030404155 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486379685 1250 486378435 486378439
    0x26060103030e1005090301060303021b0f030d0302130306090c0315020a09090b2b0b010f031a100806090d020607020703080d020d1404050c0f04020f0a0c141014060f 72
    0x400602c0080040b4100c2c14442103040150030700c044185680c2c03d020703030401540650007500c802c054074102c1d10511981e40a0280c01281c99180855054a000650030f034a4034480c90016100c20001e0998085000c85500141903141801d04200a100300015604100d0b44907a0010032500fa003049441d0a9005081800022079541c0000b04525281600321070900e03500144008041c1d1000300740c01c03078404d0710400009001250710003c0d00410030610396190240650000800009185a603070a0100c0c14002d01c05007602c140c00045101181c0ea60210005046c014081e640140f0b01043c042d503440f1080e194190061050001244040d80046500b4003900c0e0014599441d104032a6031000280d80102c0701d0100007036541d5880300410f18102c04580c020f03032095000e4590300202c0010031044000304c2079141d00c900d01c104034040b4860103034800c0312895146424024001503280c181001a604524170010050150841000c100000b035488421280040200c48040d42c031410180040c4100a000c903907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486380935 1250 486379685 486379697
    0xe0106080f131e02151204050d0e100e03011e090c060e030d2001091407060305011809050a050f0102040501090806060102120d062102030c09190b0d0c2606010303 71
    0x80300074040c01e040003014000b80c015105c9034554070600082ea4440d24603000c0100c0f0a84c140410000c0520002e035601c106860304120040d035080c0096075006900c120b16040c00212080c05880c1c3c4c0f020f400c500c1d42c0a05840325400121f0f42d0320220005004908000c40d540240b048001c103005020720074940980b400a401401e00e20842d00060f43c803200c820b4903140c8407030f64901006502e91002d0152007107035446020380d4405502101c00041c540a1242c104005140c1044014001c040320b4803135240158028040c00b080440a6081042c00c6c014000380c06003060140d101c0c0a583c02c10150018402c964081c2d80c0c0300c0300035903035192044d165001699502d0041c1c2041009074460f502e298041d11000c4404000081c49070303540c407640c00e0707103e2181c4041000c0c00c4c100d6024006500d400c0c0000544002e00380c0754201a4540800c5c1440d254001000081d106aa10400d8110540310800020000d035840742c1980030a5407103101c88210000f11111601206c440700e1000a8000c8010403604c0c1203d50503201e40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486382185 1250 486380935 486380963
    0x150103080a031b02120d02120907060906110c0d0204020705010c18051c03080603120c1506010804030c08030c070b0103050106030204051b120c07050a060b03010c020304060503011a040e0106080f13 86
    0x201061b8440341c8940042c680030300c01c070301c820202d0780325180c010500d02c4001c040051818101074183c10301a40a01c0500000c03001882e8440b81c042448100c2e22801c40703840c005003c1c1440000c0c0240150710010b001586000c01d070b00200340d0809220f40a088501c0c000030a45a81c1d50104640c09001007140c9242040c1001c00e02c0c0000e0080d40b000340c00440050a4482e0a07030382c400c0d00f07125500541c00729151984600d81501003450410000740d0044000c3c030b0054010b190a44001d0034080c02d245008000910001c0004d07040701040d806c0d5004503500280001c0a9696030074000c5c0a0302890005030b125500c1c0c00003141000c0704240c1101c0c14030380c07039183e01c500741301c00d01c84110040a001015410400320401c6088000b4030244203c1b410103121708000142c2c0704c034200c1450308540c041c3d01d0310000d6520400003484400c1c1c1210a0341d04440e404146442000b01d21401ea01aa0080307a00001c8030a4036080041003581e040305010b4494242d180300803c2507a15640b103900e01e00000302000d000101d150080c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486383435 1250 486382185 486382213
    0x6010e16090905070c0c050f150d0e06070804060c080601080630030c010b060a120b0102190f0b06220e0109080f03150103050f0a0f09051603151517150103080a031b02 73
    0x20741310424ac01c070360002c2c500c5c0008150300e00741041101d044000540381d004000070030281303201e1182280031520300303202a840c2060002e419010042d20080c4220b1110004000f0024407030948201c280c420102881c00c0c1c0c4810500603920b400600d200c507140e50a05820a22608158080d00e0300354880d5035540c510345100e842440014083d280c44181140602c1c1001c01944004611101b040b0788590910403a041e450300780540342d050301810003445540144209048c20781500d81d4810f0030b2800060008031f14203194007403401040014001048410085030b44403000a018010754030420035040c0780507101c040701c00110304945040320003002008202020070160700703440e8004102d903200c000d000030301c40865403641407514001c5820100424030060052081102852184110018203442800b80f5990750543e14401c509900030b08d0842441c10510050300042080800400c0c80c0140ca042a0f6503124217040c00f080e4021808007021a0910105d011034403d540d8000301545003640c040c10400340076045e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486384685 1250 486383435 486383437
    0x1603020114180d030e040c08150d03020d0e0301060e0103050303040506070c080415200705030705030105100e0408041508150d1a07051e120906010e16090905070c0c050f15 75
    0xf0241d040080a00d00c0071042c0c0c569124001c0b0000e41130701d4002d114a814041c091307020b40d101c03075505e000711429911f075000640c000403801c983c401c180c18200710706241c90001c60b0050005501c004030382c204290000081c0480400114060f40c060f405940d850780ea41201581c0340183d580f0300070709030309040204120781c10f96150004041d45d0645404101700902d5410358010884c903000307601c420b03080351800f0400d501e0100290303c01400c050f0000c1c41079241042c0c011510011600c81c03a004043c01d00c00007001c00103d030007140c0c0030300b032800e0410405c4160000c004042090440c0c0012800c0c4c0800080b1906240c902c0c0ba54600d554030043e45400c541c084905c1d25400c1102a0409041c4142800300d03244400d07403424280303000d40e0081701c0300d40c03140c11040000109480140040310700c1c1d080f40006024419200c0510381c2c0c80410f820359610341c0e51400e08101d0755818141e200b820240d240c4803d019981350301494040301c181c0580688910301c0d48650800004c0400c42040035404040c2440303801c444940340c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486385935 1250 486384685 486384709
    0x303050c09030f0706030c02010b061602030111130911190e060415050706180f08180a080105090c06030907060318020a080706090e0f01060c060e160302011418 70
    0x1040c003400c04140d580481e02e4003106000d8426a50003184c401d0080b280c1c1171040644d0700326107100074480344a440c00420b0061040c0707014224512025100d44055480941011014041c440c00b21a581d048000c45426030f90503601565820740e040c610205410784c02e01c0c2c191140300c00b07540404551341807c06416100c00400005003600f04105000000e000002001c1100d0140c442ea2121a900d01180c82c051080f01d0031084202001031425048c17802091034010b00640d1650b0040289a5841d91030248094002c103004400782d022000d8100800c6450b01034100902174546d2504985c64215028100509070104a9000381d03103511052040224501ca41c201d090541a0300e4100310401c102074000c502e0300005500300880e581e000035804c00c40c0c10344c009042001428443c0d1a1001424094907a031130303460341031092008010795080c4407400e00207030b54440c0d41c2c1c000719002140e50b40c02d11041c8120707150043d03100c01d0340880c0e002c1c0740e110740c100c96100072541c010400701c041101260400c020032426031000d0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486387185 1250 486385935 486385951
    0x503070b1f03031d040b1c11041505101b23060f1b0c010e0706090909030507080714073b06011b1209090c020c0d020111030903030d020d050f010e04030305 68
    0x42d180c40c0a02d500e0700651f0617070b03d202209088044441d1820401c200850200840d0300640c0b4001007440c098503005040030545404480c14800e503035402e8422660b030000caaa501d690f503d01200c0179001c10002c5007403d441c00c42c001401d00d005140d08280151103a004558800d20a008400007070011180a66261901403081034902d003040e0000c3d040d0340c00c4a07150360000030b10713900c444c00901156410a081900400d42044103104201c42ea41c5c00801500a402c40208802c0001c6801020444034040380d404008140e01101d06055a0b2140014110056222404400c0c00b100400040c030051010382525040c502d00c07210743e5622400d0044505011590b801807528807000e031040c3c0081c0100f01c025450900c0c60743d03101410750400803868103c504c03140e00c1d501994001035414420340c1714012841e071019024200800b8107040c264455056103e108030310f070781c5070000080648040029501902881e8810300d42008241e4072101114403040e002e0150507400035034030300000d0000384241c000c19484920 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486388435 1250 486387185 486387191
    0xf0e06010806130e031201030c0806071d0109080d0e0103050a09020a0b0f070803011508100305060703110408010221130b010b180a0605030615030705180604030503070b1f03031d04 79
    0xc2e82d225a0840d00910740c0210381c0c6c0420030040042c8068115000040c00c103a10180855080a582c094058004c02e145a00f1841c100b11000700244e010310700110040c43d0020545184c10700d051001004107803822001d0b4003103440d02000c1040021288185603038070758081e00c04d414060030000f4400341ca030004c0c183c0c43e04009040080400098000300614000c107001104a96220f0301e8403005080c2490040820391031123543c1100300041040000d070756400a0450400080c0d402001480d54a940700300d4000d808698000a20340c1840807160345000c890300750302d440c002c8142d240c0c07072401c00a03088540d2001d0b0100400000501810b1950030061640c2412078020703880c1740510001040d040301c41940180c5c080b610100400c45c0e01d0502c480b40e07202c020340607881185107160089000c1c1c15030290740c06071078800d0046456014203444040848002d1a0890101d039110401d510304a940e4500444d5000352400c915640c1c1c0020350561010041a00c7d459100c0d2110000002154018001300b00c9000d0740c0151 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486389685 1250 486388435 486388451
    0x10c0f06090f03020705190e04050a06050702070509010b130b130f030605010503010f0c09060507060204031a070f18031119081608210c150a060f0e0601080613 70
    0x4524890051080d1140760b5074a0000c810341030180c1049010761000740900b00052940c804085405000b00585112014a4480340c59609240380341041c0724000601040c80c040500000c10340000d07111045480c116144501c41c1e0702c40e0b040c01d40754001c50000d52512151404107105102c0400060f14030518414101510b4a95a41c800f107030080031035000740c40740c80d919401449142001e029141c0381100858003031048075240e040060a00302c4501c601000c10002051101c10880d03a501200c0c000e5402c0b01000005910015201c0f424907010f441040104002200501c991750144801e5012401907500e54101d1030f01c0c5407204007105c0022407440b43d2083d81d00d81c080306089520300000d0043d11908000301030312000f0901044080312280c000090036844102200018580314910742191484000348070b440b0100f44902910b0203038255040c60150f81c8080802800c01100c1d4410030480380c030340702810002681d8859050502809882541c0001c068200103451070414070070850300301d00039140000b540310b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486390935 1250 486389685 486389693
    0x1180e07110a0305090a0b09090402010f0309020604090b011808071a04211401090c0909030203070c0617070813060c02160321021912211401081209010c0f 68
    0x103602d00400c40215802080e002c2590038900001c401a294101000e49800240b400040a1700d400800007070412140800c201080d41c880d0308402103981c2c0c003420729a2942c0c1c65170a5880034102c44103000d40042e00801e02c00d070b404900003100500b01c585280103415620309040805c0d0401d12031403401c04e251340081100081c40e00c80808404190101000080344801043c07410017164140d000d0003407443d0303040000c039102140c008135041c4121003243d00c00292814843c90240d003580100c480c080d040c00da00d80400621560450480d950320f075024400800386035244941a121040141c45110180301703940440400207480798084481003829004841d031058804024038205980ca41080b0749118000c50b014011a0b4100d11201d25100302c0e0001d041c40d810200340000a014403c000075280703039840040e505e00b160042c10030350821441c100d070010001c0c0030b052811001c0c1110b8142c1812007021400000f43d00318001c02c0100f010150041e01514240c3d4a90045034480b910b00010340744c500b202c42c1448002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486392185 1250 486390935 486390943
    0x3010e0303100e04052113051f080a09080f040e1312200d090602010b040c0e0112021303141e0c041d03071103070f0e1305030c0a060203090c01180e0711 67
    0x9524075100503940c071f5240c00c80c44403009a40b98002c9029500e20003500a545400c1e85082070826428901a0300740c2d40d44d844010098810428040d044442c0020201c1202d10380200500581e0414038034011f050311020106a4402004074001e040c40b0702c00e4150a000e644203441045d002901d02d401e240424a0341380c8010b09041100800501040b004401084066020301584001c45402c8400b082101c10f68417001e03002c614010341e140e0401600c0007690032105003c6c0e040d208030240c041d0f00e005289840e842d0043c00c180341181109824401e0341d148000d15805a9440702541c80081c015140d000c1080080c040641540071800418032400481a05800400c001030800300e8022500ca40c4c40400c11803c1c9404d100460308040350303000b58a407003031052403001101590002c1100c03000411144407418130b14154040c1e030080958038040d0200c01b0b418400326402640c00b071360b2002d00b0744240102c4000152007280b04c00e0321415168941c8801000018000320040368048032074240014202500c01d0843d0030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486393435 1250 486392185 486392233
    0x90b010e0115030501030c05040b13051e090c1008100302030f0a03030501060215073506030d030b0d02120a0510020c0c01030207020105070b042f03010e0303100e0405 73
    0xe80850004101d08880c51903560501c0030703982010032895040d51500080716500b4020b86004503100d003619452921a42d0f1491710404101e0b40c2040b803403d04c4000f048081007402003285014818901003050b521000c5031a00d05a43e0041c80c100c000713a81e6031030941c4c80e194004e100048030042d0031b00010150300d05020700c100d10304207603018040241d400d20380502210750680104003154480f50130880c1088143c00b84070740000203410408c00b004520310400c1d903440043c1038054003001e0104000a10501c2d00c0b81c01034082e0340220161001d00401020841c204d5035225851940204104007010150800c0005400040315078070680d101c80c501c5440f400d243c40071030051002581e0340022906c400307020900c410b0f0a1000d091030294503004c22070b00020514010860050941044400840c04015940f038548c800740064640c0a2b220b41c481e0700d86800340600d000d0300c00c1d000394288020840c0080020080700d00c01c413070460411002c541000c100c0101924020720444a501c07030100da4100a2115a81445d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486394685 1250 486393435 486393449
    0x60708071509020913241b052a0109060c020a1101020c010e0907030b031b0102011406060415050403050316031e1202091c0b041a04210201090b01 64
    0x5900c065600d000d440d00004011448607840c035010719000103076164240250800300c91241d003c01c036034860400560034000b114100980d0951072002c040000d0060300030a10a000082400f130380b00c1070280041d5514460302c66665240400403a00001c4104042c0f42803030040e426000028040300c155460508507030841403200e015034052b8903900e04021003090300d1030000c0401e01c05000e00024140001c1c00c52284500c5030303481601480001655207109500814490100a007180c1810780541c00d503064418440000303074019401d103600f86842c2a456001a400780c400035282510b064500300750b00c000e00c40d54112500810104200000124904001810701c0f541c4030800c441ca600114a4040c09080d80d241c480318a0b1344425031031405440d04034600301c030700300340081d00980e030317140c00c0c1000640602d08040b100c1d48440142405d0b4061112882440d0f00c6980702d42865845815007088140c0080b0040320003c000d00b0343c032200954402102c060b405601c00140c000490304908035a140a402c48090304904c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486395935 1250 486394685 486394687
    0x10b060313020a1509030816231209060306060a090b07030314070201140601081512011b09030c12061d010c08011208031501170903190306050f01030b040b060708 71
    0xc1d00398035080550f000104115040005407000c00c0341c000d05429645e100180c64030b1000718200320f0035540c20301d010184aa2140b581c040070104402c800510103240a0300d14814400e28420703601ca150071004640c1461401402203042d5903862080007165400a8141f40400000704d400150314186000038040701e0b4070a0300d0200e180c180c0d80004000d081da0040c200e104580c107040e03081403503c041801d40d0307401ca01c081c640311065568003207040704480c9041035115046020601d100058600641c095005401da40800900d003800c820350444883d00e45010140264038070722004c01c039450403c400d4078103680c4603031404513000241030580041020300c004030400c182d45404142c2a02c560086600b03000d010040600c9201c00b0090300d400080d80001407011740030360400000300e01941c0c02890300c0440c10b002441d1000c181e280c2810055140d40007000c0c4010500c2c552032000550600070b000320003c1d0703038003d001002c00f00c1c0c440d8011400303010206141745d00715036903038400d12168907030b0070043c000c082c0150809 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486397185 1250 486395935 486395971
    0x8070f050f010305010e07120209060a1805010212030a05100509040609021201202a030a02010606210c0908070609030302060a02030907170c030a110316081905010b0603 74
    0x40700280d00c44980041c1010311302401032180c8480c40034410342041d000e182c00c0c0490361003002c0d900000e20905101079070200d03002c1020f00806500c00380500d25002c40036219040f40341d580380160707903a00038065500c81070607090000529510741c56000683c00740e64041500c540c1c0c0d80d2040404c0c007c40c01914142c030001c5d1201c0c2c0040c15820003410642d481410040200b00080340840e00034000c0004e2207d02a101e5000240750b21502905088500e840f218a22650540700310441d6240e503944c070034010300000d075007000c44c000307a0380d80a000d04a100f0301c0001420100c3c4940e03114420300618002401c80d061290804001c584030804218041c0505082d4569111303890842c00d000c1e1801d00300070414102c503030040040081c80035000c103000c012a000b43d0841d5840c41c84210446041460003516a80c00d449075600c0308051010710407a810840304d05800341d94410300540c45140310100d042c0500c52071503000b230540000c2c1c880c0c210b040707800307850241000081c10080c030000140c05901c21341d10f03051703450510041c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486398435 1250 486397185 486397189
    0x40212010f092a05030303130204020702040501121a15040f090b070f1404050f01050702032b0912050615010e04060803180a0f12030c050102031311030a0314030702030408070f05 78
    0x803800d68030040060f100f0070300d1400e40025524407000f480e6404050040130414115140c07501503450b4564003d005000c95a101d03001c40504400300070b01030b203001c141d950b40c0ba142c0000c40004e850042420300c12080110068105110141040311003588100d039464040300c003c41c61100329240203105a68482401941f04400240440f680c0c20068102d1542004104072650b19000d5460f9100b200b0300300b6540702c0c80c40b0300009051034420244100e814403040c8400d1140109a002ca00c0d074402d00b515509100c540752000360b4440c4a40c550018199030100010842c5800450136044040c0414034052526900080214041e1989a4480860b550005c00da0600c1950421115041d07818140c0e01407002606d4840c2002c03c0001e90300c41c03082030071341149409040c1441449440085504007000703550341d003403603020b881c10005280000d40d114000030300540d07858500444c2e020002c5806a03074400a81c0720b0030525881c03d91010b481581544003c000024080405200c041c0041c82d84040b20300000e8034cc442 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486399685 1250 486398435 486398483
    0xe1008150a0605031b10050f03070905030d0f120b04021608091206040308070e04020405041e0606050c07261e060a050c0315040b1315120209040212010f09 68
    0x511039085171a0740d42c05185001400241240c04803031203602d5121056043e030740c1d07204040c240d41400c00e0010800090b50b0700081d21108580c3c055041364940d5400d07010495030205280c6549001642403e514001c00342c0d5900a40080704c0000c0c00145848032a070344407000b4100102003142c003403101150030741c9589880310104d01c240031030302c000d404c0c01d1425650042464200401e02802c9c801186038045182e10355a050741c01030240600b08000c050302c0010114515101c040000106074101030740411020f100c2c00a6440c80806100200315242c1424110f40701c0b04501000340008510290404080103000c008602000101c00c0c2c2e44c502180c0b81051850401d0001004001520304000c148413406c0900320850b84e01101c2c00a02510020210300010080c0c220095000c0d8020003200c10741130303050900d0703120b905000035042803400c5855580a255090040119019620500d110b00050140c100f0030f5000c540d40707480000008414181e030007580204c8807a07036000e6030f20040740d0340c0c04e0300728600e054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486400935 1250 486399685 486399689
    0x601060c0c080703050619090c24030b2b02060f030f0114090103030e06070b0405030d0617070b07080f070c0504050a02030f04110105130e0403031103070203040e1008150a06 76
    0x5014183c810300710f07110b0326a0f03074101034840c818800001e0410f04c0301d01600e901c80844141d010345d5521140390744510b4062284004804150500000c601c400c0000d0701038400d03190b0050003d01086030340549242d0803495141d20300d003103250800c0fa103080c0a005a41b100e006000840003100001d80380d0401281c02d03540180b050300b0901640e541458450010b075111115541125490700c0d144c1003200d11306020030042d00074030b4801803000030802e090204009001c000303007400e003c0703901d810425591740d054446011169107145464903081088140001006038008001c154000c0c20300c0392a00a04501d140c1d40c0b90321003441610782003400c400900480c8ac0c1400303000e80000d00d80b10103500307504165030049074181020340700400e84d803021030881c0d00c244d0081c01560f80d048100a0b60051199807220001c0d24148104c0741240000d280100c2c44d544e08500409590048821b07500a41c01c060410040a04502000d00400000c030103013100050440360030480d08080c12402d10210312503052024801040c0d45050f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486402185 1250 486400935 486400949
    0x20f0706050105060a080c13080d0f320903070503100b040605091504090203120406020c1801060f0c0c1502031b0304080307110604050301090507150201051012050f0601060c0c 77
    0x700300702410f15034850b440e145c00c001042d218940d980c2079010031b0b0f118182d239944043c600c0e010b41d40f1402ca07825000744040310f100802d9181c6245410300701428007544690740e0480c04e0034070080303038103410030b0741030440603050071000541240d8815480c0c200291601c03501450700c020b03042c1c0301c1d00d418207036013018021580100825071743c881e414282030310000d01021407031100d80d0250fa03a40801105543e010096108040c42d400030040c2e40315120300000b510383c8101c07050381d0b00035410710040c407820301c0313020440358102d465542c2c0d40b030308052085074100c0b020341c0c50200642d0400030300c000208001403200c2c0240854081d50f001190764590844060405400c1495541c1e90703500140b00c10440810f000c0104c0e000b2079400000c2001c4c1741c05c0320000540c9802240c1001d505136180c2901d490410200042520650b242d00e050002d602c20090012426640203c90002c050010000104024240034500059407417003141581c1000e501310f0b072a60704d00030090303000c500021003400401061103251450207000c1c0c290 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486403435 1250 486402185 486402187
    0x9033f090724050304030c02060d020a030e0c010c140c041d190201021b011e0807020f06070903080309011d1b33070c03030c020111010507080a1e020f070605010506 72
    0x64007140034440442c4803601010300c24000005402c05101e40d01d0521140e5004040e00d4a42140303040c00703002908581d0208010a1404500c40c118102c00110710502e81d80582d81c2ca0030b88550350b034441a8806000030240345900c20304210000307541e5180140965214400c031642c102e162081030310380c60a09000100b1900c000c98580784000350340d0125038500c924104030b80d00310705080e410340101d8400c0b0500d10076a03900303140d80a141c0300d0143d014560314000c681f140e00311000c403030020301403e440c1c5500740c41710008241c21100c20070016120502039544100100d00001d010303840c90704401c2c030004151403807000e80d81144c000d48590b0010301e401c4000c000410341d451404403c513003c410362540038001c1e0355000c161107903030300482e11007004048514850788140f80c0402c181d903914000e8003001c1650012404141091844070b0300c00300511600d80715214a54841c041a01c07080d0b01c074001401644510f1100346156400e03051060540e00050941c032070700d103075500e80d6450b0301d00b13241c0102c4506811403442881c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486404685 1250 486403435 486403469
    0x30e10080f13350f030415090614041202030705060a0e070f060203120c0702030606090601020118081902010513080c0703021003020c0c030609033f0907 67
    0xd88032108960104019030341c04010740707941c820600681102640142150300c1001494602c60502100410605002008811110010040306010301403090081d060f040184000343c0400c20b26080001140e840110004841c10036840f41b0056410340c13007040a6100258061200308005120700c060400701703601c061410029140e440d2911407801404810020f91200b2031032401e2031042c000600104407840c04141d4055039014065103a400182241801c9142c00d00028041c05481c07044400c5140c0c000d01a10441c1e54520411800c048050301441c1103640c1c40300728041e1500100c0d007960800d0302503250252a50000d541440030749007941c820100b1641070a05200305641d000344080c1841d540b01e801c458403020420703802494040c480d40040e50107107000ca0001c007000e41540c010840341c0691415078801080190515540d55401d0310740b40001d0303104001c03825000c0860190f948410940f4420342c11419034500f150410170000e0034820f0030311740054003444115142048600c008110824030708034891 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486405935 1250 486404685 486404687
    0x3061b1404090b030c121b03070312030213092c0f06040f080d062301080105130b060702060d1e0b010206010e0a0e0717010b06090906061c18030e10 65
    0x4001c61055400b129207070140940966414803a0f4508000007608440d004102d02201c00d554001c50808914250700d2100c0e00d580500f80403c4400c15242c020a8252a82440f820128025402201c0ea49505801008081003101c060b000f002d000d6010090b41503d040064188103001440e01c007960040341e840070780d00b5900d60b400807904583c0950810b4181e04d00940a04050307185d40f2400700e102c54002d00d440e20208015141e070f1284c00100700c04000c0c0300c086c8c1c2203100c0191080b21003800b4440d8415101028a5581e21850b0440403030b141014009505200042c0d0100b4151340001004020361a203e1230300320301c40144c00109015884e400c80c0c0600c1300c0b00c00000043c0d116501030164020035026032000075000c0784240c04c81c4010600c038508446203183e8400c1c59880c0303410303081018010f41d401c201846100b450080150b0700d00c0c00e8000d01040ca83c0c1c5448081109035841030741d5400c180401d4036081640a10396204560100a0740c810842141c6458039008050580b01d00020380304403103884200e500d0b1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486407185 1250 486405935 486405937
    0x190f080d0e0a060c030c0b09060f0703090302250f030b06091f060309031b0b0f1609180e0d030603050709060e0a05042a1e0605070813030b0103061b14 66
    0x121a241400c1ea1100135504040f500c07001c013a0005400c10102005208900c400003e0032885104912440e90980d02c41c1c1c1c02c00c0307098400121020b401a406682e11100e40c6074500224001500180c134850550b507511b0039604074440090f401541c8500c40c1070100801406d04a14160380000d001e0f45030000b40090800e00d12004200c0d006200070541d4030f080703200815005c0c05041104601381034045075000000d290000102c4421640307024408610804900c3c4000300540301c001381e03070468a07150790007420214001c6601c48070743c0c000c071125a1100e0030420250f405201041003000d45540100380141141402403400704564002015285021400c0103da004d1f082d22942200358101d000c036085d1034a00707100010503001000501d5070812518400a500c10341c2482504032031180c50900882c4036400c0300360107101810b11030b04010600070880800080c03007950061520316920039040a02e99100d8450100200c402d800c12101c0c1e07991003040150803c14510004000491880c0058490b4080c408034840c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486408435 1250 486407185 486407189
    0x30603060a0908301611031312050a081308070e011d060d2009090105071b05070b04180f1a0409020307080d2606060414190f080d0e0a 59
    0x3400110f1000600f801d081404543c1d0403400b801134041041c14080601e01002d460b00b40d00b80c01180040c60022440c21b004016914120140e115120040e481d00c01d4040d0480c0d2000030440d0540140c610120000e40003402400388100f40c0f01010760b5031401c00c48080c0c80d0100c070750011501c150031a401000500180e12142c07890003130242c009010390b19a14085180100407290003400b1074074280000404209202042c03050705400c8ae4403403240d03116005c0c058200c6609449040025040b11b004014640c0404015207800b803060044814441d5184010095500a9040f00240a10704040c580202c8900c1c003805a51007502c000030400b84005440a940e014140c5500500840e100c100010542d60240303c440010b00700e440039074a0166110000501c1c6050f9400300e28144d24030708000e5240c82408005951003000040c0001d851306090524007031001c0040c2e00015845a40984031001d040e06648070f0708024050104003203091418240b00e50700f4085940f2032401040310046628a01d992480c480c007003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486409685 1250 486408435 486408457
    0xe0702010608120a051605100f0204030f0f0503070f030e0a060e010c0201110304030b042d050a0206160f030306210309030b04060b180613050603030712110f0102030603060a0908 78
    0x41d41c0d013010501560240121708100d6100134510088509005000c07500a45100d86640c04110040d51340d1501800ca000d5804003404954250041200080c000c8481c102c40034003513000c0341d05005459490b003100ca00c495400700c0c0010f4010180741d603541841c121380809001c2e60306151a102c1c0d40800005c2072203000d2a80070703040106a083e1a1b0b5544d0007402103501550b0000301018042c03070f06040c03c0d08018404074400c94130b0000d9604042a0541d21107062610f07683c0500500302803902c68003004001c3e042a0071904a03140d4450402c0002030740014031081c1103100e610080b034111f180c4030000c0c60028a200350100213000102c58600001c0d8440e040b9010b582d80243c41d8041c40e21281003450051240710400358220b0401c0030480010401c1c001518491802120b0168000ca54914180d06a078410b9070280e402d9402030041c02c0c0012003a00d20000d498116103004040c81c800b80340410325085015041c0c42169500205110081c10203002c81030f40005800010b10440c0110b6989044900c10b903c1c8401d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486410935 1250 486409685 486409687
    0x60a1508040213060902190206331c0b150a1205070f06050c0c0105040f0302040c02010b04020a0e01031109150d090f030e011706060a14090406060201060e070201060812 74
    0x10115622000b00f0b001090504000b048441d845101100095002d18402c44011240a8210a00d071f84005503061182c11000e9a2030004030a0a0b00e0100c094050350894403069004c141c6421544c88015402d070005640d290042410301131410041c80c0c524028010710154200b1007005039640e01c88a80c100d00329009035100c441310480b5818443e042030042d400c440d10400400700c00090317482c3c0c04005031400e00ea031001035600703940381c01d801035039030b807003140700705415840c030900c04201510b003035071140040c0781c0540000b0506040c1d410004d0104e1344111156004a00c6000e0410782c03650b454821090016090818a843e00c4030318400242c0c9861280f1880d004000700088100c0c0740f54450b000041c03115030020b0140e101e9445440c002d030500c102c28406d540000c000d4601e10041190031000680940c401a00d600d243c4082041c0c100c608100040c483c00e00382c2d004000e41b584588640c8224070051159a0002801908100785030742588005456101103a042080610100e0008180014400d003244115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486412185 1250 486410935 486410941
    0x18050c0f090102190317010e070927050f0a0e150a0903090f0609171b1e0909060105010e011d04090c09140106080a140a15080303091005060a1508 64
    0x101c1c81c1051440300d410608141603d0f44c02015001039610404860301c0f0f40d0001a6a02e60200861a800c11125031001505c03003841000030010705155130b801500d1103100c00c42401813111020040d21820f40700e01061011050800100f00a43d1180101114101c40a080003141c059140c100034180035003181c0010307a48100c805c0070140100b0035403004019042030456016600c12002e40519101c0c0b02e81c0325941703090380c840860600089441c10070b40c502c904204406940c568184602090001e0300030190001040c000c0141d96a00710b111440703285441d000700500c0d0f042500060100903100941414003208880d140340203041d4285180d07011030150383c0004c100b0001d091a0b41c1500181c2d00035031149152044000000c0716007440207050b209a074440d030040341c0f180c80f40041250040c025140c40315030280c0110f0182180b0b078020051050351294003151282d250a05d46095900c261055000c2d039102c1c00301485071001c41d0150580c440c00899281132071901c0c07d5002510403500746040c01c2044031035000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486413435 1250 486412185 486412187
    0x2041d100e0703111c020307030b0a0501060804032309030a0f1e08040e0606040b03040602130812040b0d0609020a020d0e0f100f030f0c020c1c030f0804080409020f030118050c0f0901 80
    0x11004035031b0000e08032540c02c0d80d039040074038002101f5500c02c0440360400c40040b03090b0307011b10b0982c0d000780e5040e80c41c60302c0b150507861000310700d140390440070302d4021040106078800d950402441d43c070607010300e00e0f0303901c803034403501c3d00c40894203028440c03051900c1c070740245901258008040c0e078210b40c0c0d00e40340300c481981c5041c009040381c0324a4110708802e000100c1400b0600100c0c1d806030000050701d061035005503803107170201a84d80a0101282e000c90320300308000c1c0000c55403003029200204030f02c0008980341d0340b5185120283e1f080282404010380c0024012000158040c0c05207040f11002e075107400c00c524083c008940350f44448224030f020300c0342055500030b049109611808d0500f044e81e00030001c0300b006e42c1009481d04248604c852040140d000c0610000c080190001c00c10f950580f501c20f101800c140051f119403000030420749511105110006c2c6500f0940014040c440b003241c10190b40b9810084111450b00040041ba01039520b80781c200001807020108503001e4102000e00e440c4c4804030b41d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486414685 1250 486413435 486413479
    0xf08150f0c030126060f01030b06010903200406080601060201200406020d030506010e0909010c090b0f031602150708061e03120d06080316060b0306090a0f02041d100e070311 76
    0x2131656440390104000d004107040d802241038034403803220780400740c4841004640015650002030810710004555010114030403000d80501c03140a040820350341e031340d1541103041030401d0b402000036035165850608003c03507107042501c2400007010414201820400020359a080e00d0008500b819601c0c8080707191a805040341c54140c0704010300713501203894400c0c4c105010304038000c40c01000c00c0b000c0c0e41c042061801101581c40748903481034040d0541e50341404900107004910b240c101980114411f00f440b801002182920610003a201d0030400e06000080c0501c50000440410445900982d00c1c5015540070510501d818541c07040e00e91542044070600006200d9584810741c24480094006940c0344500340c40c101c4039010305002c1180442010500d0703103500e070071621104503401840101c00081c0e81c071903d4208582c0060800031300b004d003903841d01c00300c680d84612142d00c0b41d0001d507072a400006140103070501c200d000c0d0040c090040c5107544440100b030340003c9007886220300c5250620703040c41e124 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486415935 1250 486414685 486414749
    0x90301060e0f060904320610050d120c020904060b0315090a120e0d030201051006031413060f020c1c090b0a0311090315010f1505090105130f08150f0c0301 68
    0x1c040303d500c4a05400d8030041462560b031406151f00842c40020f403c402c44040130422184080c0610b10031000640c3c5540c01d042c03560050005200403000d40b18056181c50030200d00c59441500700150101c444810149000308a4103c541c2003903244041125006000c00c0e00c5459980c01070441011550022050307410242c40c2030b90b079030000700300103010707081c1a41500054040c82082d1011044581c4481d411002d40744003641e0780c1900840140460300954612005440660140c03000103030840c0d4008a00090740c1c044072000c1020307880101c0c040480081c104c00740c00e504916082c0004401c1c6003181254981c041d074600c0340d003072554544020074a208000111409010000d05035030b6000a40c1220900382c000030b0280071440e191401c8041000302e411075070800d1009035900d5203030400761480011505640100c3d00190512185080080c40f00c3c1140203200241500c080a44056042004440e4038030b400100007903d240094414800c50064031412241036400c0382d20310b4402103c80c06c2d00703d00310701d80712 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486417185 1250 486415935 486415973
    0x1030b01030e16031403040302151c110d0b01020a0c090902030a0b010b042405030a02030613050703060810150302190806070504050a08010e0c09090f030d02090301060e0f060904 78
    0x103807183d22007086800f01005032441941da01c440d50611049055803805079000003500018803200503400500e409025081450b120fa6918044401261020003901c107403c1140b48101004181003c0a000c41d005140c4400c07002e10081400300490b45030200202118400c15040c181e07100769200940d00d01380304200c2466005031555901e0b503500d802030284c1d0341c0030740f05032015080d02a820072450340c0d407118240c0f1013104a955450071030311518403120095001400860340301a0000503250401054016a4440c1410ba1800541c0070315100c1c0041c146080311581c24003081c904003c4100c80075075060071200392501615505540c2c40c229070070480e0403103203411145142c0704410400c031000d540b107402032099800680700b4107109039645c0c0c841d90030380b0002d0207c0f2405800c1400c03010f80300d05201c44d155500413220300072184402c001000c91400d562005650180003500054052070710306090041e08010a8000b21a04940c90851010f501c1d10030041c294502c13941c8d0307071004117050048580c0c049629002c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486418435 1250 486417185 486417193
    0x1602060f12090312010e01030b0106080c090d0323040e04230f0a030905060c060a0902010e12070f120b0a0506010e040c08100608010b07150e01060e011d041101030b01030e 75
    0x2100aa0aa40c1c4d044050100c0030a400000082480030b20b07800d40c02d0480380d000c00400800d9080c01d0f000e070f80d0401700402202c1c02601c01c2c00203d0080e520143c0600020b8040c1e02c3c0c0c0ba0703076030540001324111010744240000a1000400040040c803102e03038001e0f6440b42e00034440000b03a40c440e60020b10001159041c03480e452242d03016500c071030400800c803a64440d21030785a41400c55581c4050008501692401c105550481000a64410070036046414024030501d08044124800c100244000640030030b49201c55100a10500101d8425411000030340b50400c0c202c82000b495640d4001842c41c0141391111aa49502c04900070383d0280e01030700700300d08006006004004000300001c00b0002c086075804051821131f41e000441a0180104505903042500003500c0c0c40100e407184182d04181040d03420486540314030400403401d00f0321504005e000300400351046c2e03500d480d94041113132035080032455240b00c03d88180f1002494443d0f440701c01100c01c0c2000301f9100d401d440143c000b8607501468101c1d90003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486419685 1250 486418435 486418441
    0x602180603040b0f060d03090303200d020d0809010e03030105060d11030705070317010e010b07290402030d031b080a0f1103070314060603180709060b0406080603031602060f12 77
    0x5400aa514856100320808615650f03818081181c1c6c407901c4803020f0081845810103002191150045047c00c158444d140b020003901c2d801c5070352038241c1808440e00103030003085007000d50a500040a607008074200001303000000c81501c00a450f48010701c18144510380019403031071a15401d400c540000c49002070f01030b4072440c10f82406850f50b88024400c40001e80108429a400b16001d000e248c16907140c0c081e0040300e40e00f00360304198a988652400d1700c00220b1000c06190307660300107150090107000390f16034500904241c410b040c034001e14601c4c000207150070400c0c40c0a90168240e91054800b40c0c500d0441466115101040010309034042140204c90a003040348280307891a20080d402401187c0d4208505180c070103079100a00f4090368015401801007000c10311940c02800c48a184402010903501e82e0341ea10140001250781a44c1705030b904410110342009030582143c030b05680300000b0b40c0603510700182c20040340300100311080001c2c8603440102c7d548040b031500101341c1c3c1e0441c10803065100241 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486420935 1250 486419685 486419693
    0x5031b030613060b1206010521180601030f210518040609020c010b24040306150e090a0b0c0a05072604030308060a05030106061e17040b07110705010c060218060304 72
    0x340c090245c881c8040a85004540340d5441a411141e00400c034078045400c90034550701c00b02c0c1c080c00181c100c081030580c0c82c05010400700103110183c0210320800148000d80110314002c01e616a541d90162540303041c54200200a9803c182100c0341052007685075a40c4c0314200e400100100103c0e00030070030061010886c61384420f8150f2242c085080110350b1044820354414061041038890403040a0142c401c2c4410000560035800c805410000c0001130300b041a00d41503910210b40e402c8442601ca03030320000c0508140013464220b65000327600c4140c554580038107400c0c090203e2003100b8001740ba030035000e8140e0600c11741d09506000d01015408980340da813680c0c2e05000340400829101184211507103c00040c1d075180c1489110104c8801d900e44c084501c002000400c1460203240716101480090703c1000421609511050300c0340d44640d81d1052a81003880d0018022500303000851410380c0440d030280003c0ea00300010303002496201c0c5025984400169440900c0b107a02c1100d16000080882400100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486422185 1250 486420935 486420937
    0xa0b04150501082a0a05011407020907080106110a0f021c17041d0603060403050d0b10031a0907091514070606030215030c0d050a023705031b030613060b 67
    0x550464802e0716a506205800b02043c2c842a411a517440320782070100b000994010740c0300d0002400c4200c6e10b20304112003500403910305082150a000005d4041d801070010036001541c02c00102e02000042c4411507072650740d01d503148000030010744506140070b598010f409a14000e074900c26441018068002180407070700d1150340081c003921440f42c0210644040000c1c02c401d80c5441203d0003001440d290b00c2d95241962258004921010000c0e119a40000980c80f00303103a9078550441d0340c0c0c0c001403040842c40d5651421035a00d0002c0d11501c444002c0c4403006a02c00043e8085d298160720a2550002110040d00d0f845034000c44589000008079015090001592018013202d000740c0740ea1107070b0203160307420402c1440100c80440003d4800c0c000308001d040c9540c00780d1762100000500503e4940d0b1004d440c4004822000c6103110401010300c5014000b120b0341c41c842c41003400d13003807842c103500741601040f01742187c1c0c1801d19990701e004000146190b551310803102125415030340030848107032221070510503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486423435 1250 486422185 486422203
    0x303144015090603090b0c090a0e0c07021c0209041103031e1201080d08070e0d050a0b04020406060914130902090a0e1501060509040f020f18090105060c0a0b0415050108 74
    0x700d440b500c00016003d00078080d41910a40c080700c155039a035030300d100450b0150450700d44940c01504007040482d127801d004075840d000d94101344950f5142c4030580704000546003004460030040d6035a800f0a80161905280682c1160780640e05043d00868000481d1850280055111034000b001c21b089010000a1004141c4141140d500050907a2a00d41c1700e81c0e58030b0040c40500026525000240c4035601c07a000c0a40030a0b0b009004441c0381c540f580b81c9610304080380005840d0b01d4081c81c144402c6140900c1024010481801c10b090414900401d03650b0340355541000074021140340104019004283c3c2c0120141c0b40e00804080090038000d43d010000e2003c1c10454131076100c0d42880d11034510124100c18105c915981e14a031900e04c0d42004d2102410300c0d134400244d5641c0a2100840001c030fa0b00c05000040e41021501c2e00199500007045242e22040c0d101e1400783c03030300b0007405103002004269604020380250f0030704403c1e1601c1c541003030304501c1400c4050100f4501030001c10042004590144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486424685 1250 486423435 486423437
    0x501031109070212070201120507050a02011515050c120301030f03090906050a0b0c0c041b12061d0c0702031005070314070503013003090303144015 65
    0x1840304020140400080140c03500000f6038842c2d20041e00c1c41e40c0c10f40c0249009441032402c1c404c20424480b182c01030b200f0544051000c106d000c035141c04815424491400032034048480c400344503243c2810100c5070f90700300c0e00c41030030400c0000d000c402c895420491281c1e8040041e04656480da564102744144c071034000c40c100e0014102440c0001c185d0303514080d00b810f440008103e24015450017600071480d40c401010111540190300d140311850b525031140448000400107294446000e0700380050507103501100703842c002c5280c00c01c1403002d140641e4191445180140700802aa200c041e003600080c012443c9c02549841882507403414800c0b103801c0b40e030280d8100d80302171042c6140c00740036020911003154881d00151091004001031003100000740d699140b00f00d1140e40354100d506041502440708070b410b8020902d6140308008041d03201010381c4258005140040c02c05d0012007c5001185100b050351042c50001c1c05400d00c021001c00343c0510801c4000042c80e2090f0b510000078248402c1a04154 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486425935 1250 486424685 486424703
    0x80a0503010e0903041404020c3c010e19080d02032401080f06130b0310240b0406050d0b060c0705090a0b010915020a08030a051b0a0c020d170409050103 67
    0x314260b6000042e01d003aa034800034480c0c2950503071410712000f07400c043c031400030900c50221b488482c0d034000140d90000040142c0c24942016040700aa41c0d111050801c800d0660b1611001c1c1d0039201c03021a140e00141c2c06d103710b6901c85416403d144001d40164400061010308c00424040c143c80c1840104003420304d03a101d40469001410015541d0400403034841c01c0c0c541c26240062081d140c541a020000c159a40001a00608200c013081c9042428400c80052a50b2840c0071944081504420700070130140b48a030700d407014101484012940254422a030a011020400e440700d0405038010b59034800d0302600c029115400c5a0846648035454803a550059158001240b51001179004001c0d10702d0040c3c55400502d498010145d080419407003e42c802c500400203420300042c03960300158002c0040e140003003034a00304030002c0001c0a0400f000030070000400c000c0001441c0d044084907501d00d4040700c411304000340c5424100d50007040794401d03904140c0001404a072100701c1e9848241602c0c0160080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486427185 1250 486425935 486425941
    0x10050307090e0c010e04021b0a0506060d02030d120609050903071106180d0c0806040302031306020a0b010e1503010c0f080a06030804052e080106110703150c020307080a0503010e 78
    0x90710032070351015440710b01e40e0842c60a42c00c8650007440b503400b050304050300c014500b0132035400710340441c91501c200c50317001d40051080d0b03010302c0020001c1d550880c008076021032420040380e00280da6415101c15010910800c412b401942081d25480800103181f5094240041e1078031080b40c41e2698000d41040741e1500d105108020b00b428400d040c0c41481c1500489500c2c504280800c00000300701244040390b0165041c000401c1c101c2c01449901d0240340300345c00454032034000c5005091740550300c2d0410310031580020310304070204510045044c115945658400360548a000211998204c02c69a4070340540c20920032500382640700001c810030841980e1040341c0c81c2c0301d0110700c80948256110142a100c0284030901c03080c80d2101c06400f600b80c002d14254154050031002c05128080000e8035004a481030b0010004160409a00791040344c0c0c89000c2d0000707034299a15800f02d04804002c170241d580d40c0e00100441c00d40200200c40f0551741003039030b081e11074a00413002086640709003d2038400111070004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486428435 1250 486427185 486427199
    0x3230402030d031103010b0705010e0102040605040e1605071101020c030a08030115050c0d0324090b04060b0a080403030b13020c030c0c1008040305090a0509040c0501031a01020601180207080310050307 88
    0x681c04800c9003180c40605d56403800c00b51082c11b030404001514155a01c18080400003003d05c0180300526003921410b8850b8900f00c0c41c0305000c035008210314055001000f00b40c00301036101c000c40e2001d035400001c1003040703940b5100403403400050500c40c03a0948200c83c821402d00039440c001c1d40c102c074402284140e070000b06040490300303070188a24001e2542d00c05032046071554040e81203050701c984d004d904149824103886410b41c0b5800c0940c41210390707036640c001807406810300d030007072001821011b81210316210035400c00611381c0b2401800034041541c4e401414405a071000410300d90b510740c01209544541290301001e1703c0380d00c0321090103e1031059106403020382c2414480e07101b4840c15611600c40c159615202580d640c3c0c000526568030001020021940795159843d041c000e034090b203c610f0700c090034500058200c03059400c01c4a1440f0b60100260020303030b40010540c3c159401c0003050700c0c541200c2503901000c0c1c01880d10090610342c022080218005130110701134225102281151205c641c1c2d103079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486429685 1250 486428435 486428441
    0x14010e1f140c0d02220801050709032303090d060209090114031e03190c050c15091212031312091d180601060509040b0301141603230402030d03 63
    0x816000030000c1030000e0210040d54028083e151841c0002500e0524140c420502d0268501c008160a4654480500264409110380b9520000320304200810301d0a640361089115010810081017a00c020820030185006000351101034101510b8150010302c40c4c64030310041e402881d800c034040c80072500002100c0010144801c00f0070000790203001074602014100d5840d4001a540c407260303110821903094507010903500c1100b1006140e80300740a1580c01d1030158105003501c101c0307a120f00c4120545031100d0780c054040300c0c0c90440c200c03020458450103e07001410040d0b038101d1170700c4940c00801000506032400030f4111100748117805000713030040454002c1e2403690b55070040f4190396110010100300014400070b660b03002490703007445604126030290310b0361625600360495000102d02240c05070b00303418113000c0c0c1c040c12075003107000784820300b01c01d04500d040a00c001d001c031201c1010302c0c900c00c51090007580410040c29039540382040c4a0b4460490188110341660124082c0c4508000240207512030301c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486430935 1250 486429685 486429701
    0x7080712060e0a02012a0c090207060b010914042304050303190908070b130203060c0c190b040b1905091c1b030807020f060108010504020102070b04030c05090414010e1f 74
    0x186030030f0001c03121038400b170100c0f00d2050100c00602c2a481c00706c101080300e2540d07020090400580c0565112254039101c1d0a64003000136207418411881002d1203040d540e0b40003060820000d860000710030103070003003600030710360090140b0301c1c0d103414a000d100a200012000750300c26001c90355080c0c00c450a403504c48044030710854000c0e1500005001210008040c0030350140c1203001444204031540e116000a8240f030000d6a0801100c040021442c49603041480020b4203000ca50410016034801070300c400100c6c1500030300007440041210b00083d65a99114124484040340d031004000741e00d803258141e42c0e55070000400e90554001c103101b4002440c880c0e001c012408159100c0d4441aa0403070f036060700c16210291619040d400b90074403025500c001002080e00900f0814008189800d040c000a42004881e4001281c01c62040105002107020f01e1142e0b022200705680c14203d0760b03030300d00f490044480d0b0144001519401e00415000030a07002803a00b601e0648100007002002c02032000a00301d603c98 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486432185 1250 486430935 486430937
    0xc090f0f06110718020d060305030c0f3d060f0f0305060a0b030a0b0405031c1a090403230f0c01050402040506031902010c06020403020d0503030a0e0303010e0c090307080712060e0a0201 81
    0x8140049113180c003d801500e90f0803008480829015105da0b40d041c10b6400c08d40e064640307a03208821802c181042005510f201d0406804080d01c6045408013100b10741c5013520003099498074032220080c5110344c9a021300010212808000b040544a03600e002e00112a48000d80d50751107040081f0304150b40034403400b00c6001c8000d004215005282d5a081000c0d04001d209523a580821320812500c560840c909000302e2034003100000d5880500c550307440da00003030340e003005008004090030480003d400c020360b0703014910300340c2280c60300301008410b02d40313248140010180241c002050020400c00b05401041c0200d208540c18411951414145075a52029050204000244d564500090b500403411004200e028200240c64070341c80780c0211b40042d03a08241212180d00002c10051036014074403400d40030080c0e147c05140346501d032424034010032038045c040c0850b15100080c040c0142c3c0c9c007042800300130016031056601e041da499482030319201c4804001d5075203d041804170150110041202c0c1c581c1641 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486433435 1250 486432185 486432209
    0xa0504051003110417070b1918030c0f0e07021c0309030507020612180c0a1401020a0c081006060e06030f0603120d0f18020a090c090f0f061107 63
    0x40d0500300300030310344203a03100001d06a4482c9884103001c1c50714010000703402c1c11101050380c1d10100040320300d03160690b4800001400b052165003c40c1c08400030041d04141145032041c2e044110362905034400340c00c0e0340001c001d4804d2000c002400a03904003030700210781a106900c0025501d1120a076103580d40c1c50400c031128007110141910395800b981c000c3c213a55002c4d142c0302d070230110030342e001c142142d2100f041e080c1c0c074610340000c0100480d40c01c0101e28a0b031017400040d0004840c3e4101007101103131140603240103000e134002880d072164402c00000030b1154000d01e207202d80350341d9480041e413500c54484150b04036604000c1d011500754020380c508114a030025042918554801c055115548000b400349640b50084d40c1490088102c140042c0a4001c4610310002e103400c1d071840d00000b210610000003251000745d01803100903030b070f40d120030200f2200b103424041501c40d480e02d0216841030b82a0003012009418071004200301c03d00c2010b403019035140383c5800c40d0240b12480384542e00d00003440ba01e601040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486434685 1250 486433435 486433439
    0x80403090b130302031006050321030a051e0403090501120905100e01181208060901060c02090718120203100e0a080c0a02060301090b03061b090105090307170619020a0504 75
    0x1030380500401d80d0300c2c0840c5952560719200da0000742030010a603140040140c443c60240013614003800103490032900c298407440b0b03a60450b41095600d0000421740c03560103907128001664800c905107801c4c1c044946010b003504524091034040c0290049000341400034209941d4070700242c80034821a410540c00c480285000c0c02c4802a5001400c4203000384180c079502d560ba40b03681c00000c1054208064801e00e8410805200d50350010803140c0001c103680d1144c440070004004e110381000c249080940c068079440c0103955490001e803400d1160100001460004150001300b52240c0d20350080e000307208030150344560704442450819503000200108058002031b10220008204900504150b003c000940c0c05451385600007403c41d41090380188802071b2940300c80f20042c0360520029600103501030800044540d060380c03408450083c0082c040c1849800038008045903400c2040130014201d245040c40e00b2032034030301e070280c894030143d404123910b80542013201c40021260017524400082a0f541500707145c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486435935 1250 486434685 486434699
    0x306240918140307020a0321031103150a082d010c0816120501060906020f0d0f0c08040503030a020d0801080604030e06070618060e0c0a0308030a0c121e0c08040309 72
    0x25414568481c0e10081001c1801030b100d20000c1b000950182004e281c5219945440d00c44140a18804004240c1752030882c00d07030034040e81d042d650419200000690600d009901292018086402801c00d901c55212840b0050b46100848500230700b0580c40414110b040e00103540c03e841c020aa40000703d001347d40003a0000c6200d000e44103502c851031030007001034506244464215142a000940045d4594406020300d0740c040000040a000c544000e0080d64a215030041c50b0032841c0c5422003c000345404c1150520440c101071707070060080142900d80d550050080a907544171010034032400704040000002e648500841c1c0c0c03900c250b4243c0c49544c01c400200c001c000d01a481544115441d6590303c2d6540d0100310440802c81106104100018194040c6070b60341d0301c4c2c94401820184984c803204800d00004d01d502094a030070071082c4502142890b030050080c0e4840da910026985450300d440100c0300c202000d50031481a94142c41c00800204180a80c103c418000c11900038010030910f01c000c118a0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486437185 1250 486435935 486435953
    0x1e10060e0c091c0b0a090b06310e07090606030b0303120109090c15020601091a030a020d0c0b03130b01050a05090610091d16030504020d0b04020a0306240918 69
    0x121090140320a10203451303540c0c0c0302c0c1c3c0b40f0055603280001d0f541d0307031b9000c402c1200700b5581c660424012a43c5002082c1c9420311500b03442078003080b43c0e210403d00d030500c0c800c1240e41c0d0048aa44000c500a5541407502e81c3c40e044010a0607114881c000b078240000d00b8001d0802004440400e00c080c1000c01c01070b03003064a1200604180325086490b440c41003000510a40f600017041d9405c2503d0380076100c1540340910f003200f03540d18400031140745284038a0561107035600244941c0700d01d5042d1115a0703101c125040c880c40400d401d80c007100c0d12070347c00030810003101c3d980307110044071a105101c40c0c1c0d00b507620307081800550a014061150400f91503400700d401807610000b4a8003007021480c04070075a5031103544c4524070650001d444650b80d11440140f110140c840c00e401c3d101500795140420091420f81c0002d2040c0301000000380854070300c80042030a645440f00e03000040c541141c02800030040d01c416888012907800d80e2004007101d0a08040303404100d030300611a480102561440030641c40740c44446030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486438435 1250 486437185 486437209
    0x605070206040b04030f1a070215270d030e0304050d0b09010b1c02210d20070605120f010e161e171006050403141e10060e0c09 56
    0x1000780148800034190221400600140d481550400751070382941c58411501205400080c040303040e01000c00c05210790006000d1070407800c50701032a000d81c072001c0d10a002025400c3c0140c0c0c1014a011840f84003000016100d068520550b03010404c02c0400d1941c0ca4580c0036038024154801040c0c44203a02288030510001d8103c40200c0c00090840c0c81d4400240524440d50303107039000700e0041488241540b808140702c00d134080c46082910058440b8141d0141c8410b2940845000d109012034001d00700c91090440c0700f4440c4081044a030303402d0310b035440075141e5001104601c074002c616600060312242281e058034122559036043d000d554035092140c210041140d030300d420403c00641d030340b0a080c850000d178082111140d52200c580c65420082c04101d0914000d040c0c2c049918142c0301001140e6000044404490300701130a143c0302440341c1c0c0014140b90080c03d0800c1248900d0300828101c40f0046101c8400c1043d16504100e016603079201d0901640d0215482c4903003a0044c820800d043c02c040296100e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486439685 1250 486438435 486438439
    0xa050c0c0d02160503030c071509081b040c0527040230010602210307030b03100608010c0309080f070c0e0901090c050612070e0f131a0a03020a06050702 67
    0x4100354408030060300e0210307854040030050b4040000000c200c404900c110b4050002030b0b001e5854410103640b103c0c0e44e50350034821003000b101c41e40c401c0050188556440c10140540303c0c140c03682d05007240300240b0798681c8101d1080c07099180c00b4046800600900407550020030035041c2a51100f010340c00030381c0e8180d200b0b80541c3c003c6d8007000f80d18048000c05203003d201a64252110f924a03044180d100b209850507000b500543d40403c42e00750580000b84101034018500b1000c1698aa559a0085001d0841100400d4251050b0403a815154859410000075100443c00070000a0383c05c1c081141070355280d01d00544050300c01c0018222401c203800080c011139000b212140d1149584902c04c52040f14101c56030100760355101c90700303400c010030070505030014541201c0c821704140065200d208103c0c00981803905201c40399070881e68545030100a04c2410100038403c2d0b014403010040c103005044900404c41c0d54034143d4041c2101d902c0d02c0c5803d0010349401500c104c0b101805e0010540d0250311042040e6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486440935 1250 486439685 486439687
    0x10c03020f01020c2401060c08070f020a0b0c160b1218030c0a0c06050405090a0f140709030201110f0a0b0a0906091a0a050105130c05120f10090e060a050c 68
    0x41d40d050240000c1900c4061100101030f0040c6001e400080320348000303442d018000a1900400616501240100d0403540002100742e44500d01d15144144a0140c1802904442040f00000d00c1081490252440e40b402030f0944402e10300c1c03000d528444040a009484d41c41406110801010549000c3d09500024400d60500ca01ca101d00d10b440c6950030442c5503011a0b4804a0b242c41003008046a01000342441d0404a00301b6060a00013401c402000340100805540c4902d2051280320607009000b844c0383d0360700b0801c60340c00d01190082c500c82841c0410ba011038580302540c49499800101d0500c0c1e05092805003003c501c55603a100c0ca10f1001400e444180790716009240c1c0411070f148980c11040d0302c40c01ca00e485000e41e4407010304a10394010081c0c60f2040c038190040140e61100140c00b4a02c20f00c080000600d0100756006517294000c2803004410b50120400300305c6504105808039014200c80541c0b000340c9503503a0306100659072201003200300f036040359010410301c6409400850300103010103103013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486442185 1250 486440935 486440953
    0x7030c020102091807120c1b030e0a03060203090f120a0509030f071508090c03100509070b03010323030c03041e170c0f0d0206042102030f060603060f1302010c0302 72
    0x74854070b103501314415200400b805004105030850b0b662110784000d005c041c0030301030940001418800a80b186580e42c20140c95003001018803075020044a09801002c0700852900da09080000303420444403074032380b48074034042c41202550004200400302c01d100c40c002d1a007210309a040301c0c15004090280c0e014410303010b00051000c014812034003d000012000d501010030320340b005200300e0b0007030428101901300c0f08110409450201e842104c85440382d502044944482d10094034200c00380d0700c1661051000700000c01040b40e511000da0b8444101031307609000c0055510391075100e214100000113160b1040108020541c2500129140402000c419151590340e41d20f086446510b0702540e1011078208100e400e0301d6160001c110340f55034001b81e0b2440030502070390340810082e224034080d0752541102c4081c0a054820007442159000b035002d41070325416080c04503110764440064900d28400d0003960001640d05041c401210f214902101c50303191a00f076150015100004848420ba04600480b01d003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486443435 1250 486442185 486442189
    0xd060b03030d0c300c050c10020405040e03090d1b09020c0a020901060203040f0b0f1b060a050609060604030f0311191104020708041a09030a0804060e030c010807030c02010209 77
    0x2402c100d42080c00041448546204010107421112500d03c0701001c2100034a0041801e900c151090602c0c0b4880028810601d803409603454061080c00605a216905414070144003540141c4120380050760140400340400d03500c2d0382c82c1d02500c0460b41c1c012800340e096501040e2402201d015140004030706502d469256200304003668800012460382e075100851040841c2450104540108614400756003000d051150490404a085c821800d484e0000301d80f60307210b00241411500d420701c0105484400b03030a9242003c2d10340700102c0d2109800d6107820b00191441c18541c1d4094450780008060034039007815130396008112901c506090b8100000d01d4981e13500b540007003115903610340008003024442c0c000303450100082c641301c10020340554014841c200000745400c007600c064071081c1c0b42c3e0120543c811081c2d002c80d8001d43c088140c0c5031182c00f504009201143d00104203031a0f09540e51038903500b00300c081c0341c0c0c1c0d0741c1180141400944590001074049111360b110484d41000740c400135262405001c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486444685 1250 486443435 486443437
    0xc200f1e09240117180c09040b0108060a05010803070209131a0907053a0602040b09100c120f050c160504140403020d0f090b030a050109150302030c0d060b0303 70
    0x4200d80da10711041e0b03142c80003401c41c400ea001185000d01c0d1042c498240c190924121450160030340c800c00e42a015a014000010300c04042c0d07425014000900718901410710425620081c881c015a5020306c0000c00d00e20510742c00348a0584d182d000c01180781480e56030034441020001090700c034180228030318680c00122002d00d254110440000d0300c68590400b2090305040403110fa00040c400d46c2182d802c1c080104041c1007005a00700d03454001d0305840c0d4080f55510140d0306020b40200303103078400100070076810100406002900020359886003191009141501c580605880240041c8514001030f101075210741814000d0100c6403a02500301406e451103141740880042e004941c150640905115030b05081c03140c015810607030101041030f402c0584020b9100c206041e1108100905001000041030103000390384014000d0140341a62450b121413030000500c02030003096003450814802c1642c8400110001d01a0f90b0014081c001005520042100d907000311007041300d07000d03240d4200b0019035400340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486445935 1250 486444685 486444691
    0xb06070302100e0712060209060c030d0504060612200a0f030f0b07091a0f13081c03021306050c0c0402040807060e0607030509100c0507060c200f1e09 66
    0x500108180c84442c40e42000392580580054180e0b44080c40c100b15010000344c625464903004200141c0c0e031041031022541500c07682d1042500780c8030001b500030446585501040c8682d01500040000c962903e100e0040d01c40084000f82c45101500401020325040002030310312000010682001a0b5a4449004592107640c3c010f9500e0010084000c00348232040900c95841303c0b8600d48440d400b41480c0d03030002580404c14014000c02d44c0880d007407000c008000122000445c3c00c07041c01145a68403107401d40d840e0f07001100e220040446188140625002e4002e03107007101988840c0d41c450a09045003124540c1044000c18075502c9440c1d41e5000b152a01d100800140411002801040d402c02c200074000c0071085400d00d0140b041001030901190b0b001c1c040e288983c0088801c0d04c081c2e88121011034500d580c4007800b8003e8040c0c008002881900440345419413072040c90034105042d03880310b6001d04104078290040c0c1003100440d01172400d00d000c00c005802042c8903045a05103d0100c4080b500e1902c080b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486447185 1250 486445935 486445937
    0x60e06070e30160e04212601090b151803030403020405070e0307141f11070b04080d0305100e280b0a09090321091e020f0a080703030c060b060703 64
    0x40354003c00e4a240c802c1c0c04001400450900c12900c0c1415500d02c01301d0420b41c2d000c4c11500040032601142c0380d00c20722490414440c90383c2030f0342c29130101003408001c08500b0f10500b202c0c545003940702800c5091542e10b0300d2415020100e01f0741003585d40c182c4001c00740c40c00384003140c0c9404108000b10041c0e55501c150b50050200755184135003610403006040ca40301d03043e00078103002d280191075140ca070750b03449007030814103410704c60380751411600d42d40e094880c150801002d61442c01a00c1c000700d8010380d61005401110106011942e8042c803443c4264103d40c403ea44448110790004418480c1480c00c110300c03500f04000d4102640485c405400c00c10b107004103404401c0c1c900c1c0d251010504c451400500204c05020f19020800200341079075405001d1004181e00c0c00d141c0b42c404a0002284442c1e91b11103124550045801102d03280e90151290304101005400c0744610418941ca500d0703400d00c11254816620ba82e0020f221003802c58070240c800a07480f24007118100c0d2240c2d004000e40d01c1c1c03030300502055403017 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486448435 1250 486447185 486447193
    0xc1b020918060907060e0117190603060e0a0606090632060703080105010212030f130c3503040e0417090409030e12010506030c130204090204030b04060e06070e30 71
    0x10110010111080c0c3c2e031380b003410824001c0f500123108100700c1241d500142c001003000307840c0b0b80264924004d04880e0b031014100714603005500020100100302100c69511903042042202c0c2c4030f0001c001265a6800740881150002c0c0314451580c1140441002c42003070415002501d41101c000180d607584801c1c801c40000300710100403c89940c0400101114005e40c8084504514210850188400000703122030000c1000076034240c01d00c0941d005280180170700d01e8804040c65074060304040b01a04207050f10140300d481810f400b0b04130a002c003e42e020350f00c20034030190840d103442d00c4000da480d5003140100050902006400c01a0780e891060b500001d100b6194000901d080108011412100084610040c1d0400003046801d940100f1440c0d044102210b0f07403545042241000802402107410402d8001e1000a01009015043c16100c4c41580b259400303000c62460407000c1e40e1203000540d410b1002c40c18280031486146003401c4990200f0031124960308065010001140528400c0c18005101e508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486449685 1250 486448435 486448439
    0x304030204090c030b2502060c07060902150c0c01260106080a0f050114091501091701020421021203131208070204141501080906010302010c1b180c1b020918060907 72
    0x42e060700d100f02081a140044c042358544002440c00922034a0301c010310380d6a0b190a00c07130842d034845601103002503414111130f4032076801003c01340e070f03c185082e60729000c0303803a0a003035009945220340c990381c0d1090a00711002040e403078000240d404480140c030b02c402c01078444c100b00390612000e10070715009180d81d42614104441100c148407134400d0240200001c1c859048503e03000e03980040c0020201e40070603100164960307100440350300901039508801680e440b010300103005846180c404800549c021030344582c046441c6508259039211f54202c8082000040104010040382c0d5552000d1241c018001c46103441d6040d8006001c5a04284d105150041504144498010000d680e0021200c0030300301402e490034038940d07965803110140300080c10400030144440070400306d0f01b84043e00e54100b0741103841726500c1c0d0100b09104042c01c29000802460710032500c204030b1150110300030f0720302c1000c9542203001480c0c003800300181000300003a4507100302c4425000c17280e80030440c0c0b500c0b8603142405010068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486450935 1250 486449685 486449731
    0x7090c121b030c0e030c010f02031201090506011803031e21140603010b0f041107050609030d150e06011d0d0c140108090d050703020a080417010b09090304030204090c030b 75
    0x1140382c0f8018042180304c8515039550740300007500010030202420000c400d1060705074201e00e50300c0f44240301c00200c0b200800026000b11f107504100c1c00340348242c9074850b0360404645980310082c443e11000c0d0010b060644240201d104500000034031000e186001c0c0311900b8640f12003052006103c010f801045c0d591080c410103592076113805604950118002c1c0141c0c040c1170b0028400c0c03444880f42134842c950700d980d94900c2c00d400b41c0480b022641c1c40425603015151204c00c1a0300c2e42c00c100141990309085c040d4540d0094168401c1c40191021110b071076581d902c1c2d813001111140c0510b2011406480810264030b01682c3d400d00c164413462140c0102000d06040c0b08500d00017400190300d89041c0501d03c01804421140400c100d01010403900c0c090b6254107550a08920701035001c54060314650000a000c55000f1441000108603015800240000300420041c0402d0240c21a00e11b48a0b8000b40700c184010303c0c0c182c0110a8850041c3c014548054494545884080b000d9404e003c001c2c80300c00c1400019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486452185 1250 486450935 486450941
    0x106080106050607060203060406030c1508090a02011b060f050a0b040f050f0103141204030b0601022122090204120210020a0b0c070807050a1103120c07090c121b03 72
    0x2801001000740107075860000420440d0060b20f600505040d0044005000c41c1c649034012401103400c10000c5401564514403148484180c026160000741d024000805a040021721324402641c1a944c484800708100c81100c4184000402150510f4a810550b48449080e01510780030304038500e8006040c00400d81003004690700360100c005154100010004000510142241146d403c1a60f9282840048a00c02c0c20001d101d924528924004907012080c030104150b0035105210a8003194041d040f40032480e52401410032a80040d031034100502e800d0588401d0320440840254241c545c440c0f6284c030410020398201d504030403c4405801e241d00d007580ba04040c911401c010b2800034252482964544d62403010b070050160580a400082e001c08112030074044070300d01034009040d1824a000c3d45400c070340d801084640030348640300e800d0309022480303c200111a0001074240003820301500d00343c541e501910000004500307001c0111104187e01c0703a00d00900311080007010b00200c000141e260040c0072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486453435 1250 486452185 486452189
    0x20d030e180907060f110a030e0f061914040e01031103010c09080c0d0305120a090b09070b070210030b1009030303060603020a0c03081017010605090c09030d141612020106 75
    0x54000c12402c0c410300c0400401e041d402e860691500c1800c44114080c1954079001c103850400c59485004112414150b028208035840c8504880344403002000c001040000e020303c1d40b040150f494260202e0116901803000210090385913588182801d54611110841d486d00360301c162203c40d81080201c405103020720400041c00d81301d0403c0c03802139060001c01c580d1601e0034030388580203031440074504003810301500c06d4501000700e01000d4045850701c1480c00001d040c42403001c90b0801c04100100b02c05080c007140e80010b5070130701848203040c40c00940800a4000d0414800380a05a58a080c00d4094441c03403c0c1c1e890008a0340c6452210354503500e001001c48400d944001e04142c818072080c20401d41c0f200001a002740c2528040b190b540b00c80400418010840d4008000e240035004610315003681034101400b1940202c44a10407503035055029241c503c50300b566503605420200040c422980180060206514078414190803d80c100704520041307100000151802150b041a44200035424010040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486454685 1250 486453435 486453469
    0x50415060312080702030f0c030c15130b1503010603080a110a02090610030f0e0706080108010203071e0e09040f060509070f09110c2506030e060c07060207020d030e 72
    0x118451031912561200040031400b80c041008000102d8089882003058031015800b1120082da038500b0070403640d640740c0c8980710035040c0e806041e00080f0011207000d021803207000419111a9140d18580d034261a0050042509e1a5900b20783d50320091a1000d11900340030f1482004a507a4645610702c1c003401e045a005c16204560f03002c1080d0742c0040c3c4507800320680100007a1001d03030700740c41c0355a400c1d00030b4548a1444070100d80b42201e40020824000781080469085c0d855810041e601c0b07101181c02d03480100c0c0ea52001c5401e41d41142c0d404004a501c006024000f0b28210120700c0d070f150001414200c080d5030503503454903c0301d0607806029007031064581003420b9200900d0700070f20700860280c0301003852080a07130443d591409440750200b00422140303040401c40585141035800050850403456907100d03100c01e480824400f092290003031082c903003520802c034018109542e400d04080500d51117984120f841035000d0201130016243c41d85983c0038144a9280c11b000f102c1100207018000b5007072101a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486455935 1250 486454685 486454691
    0x1309030e09090105070e01032a0801061103040e180a120504031a04020f042c060a0528020d18060501090e0c210c0904050606031c0837050415 62
    0x4409590000403025101c2e02c2824040394060016a04000c000c0d8038618035004807102c01c9c904006640e020441034180d03030352900d426083c44000015160b4074055405403100800c184808601000500c6040e100e060a4a104607048000349643e15409192070303c10001c089000800d042c0200209859941000100c5400070311081c986a00041e0b82e0304288141c09000715031b03c40c0010030310300700400901d14071502c51b41c03000c8010802014541d912202200d115100918010204031a290b43e24100003060355034103e007000f0203604890810003540441040d42c41c09a90b184a103511103184920040c1c0c007070203041d00080303544c50000a50705649612007151090341282c845030078180d075040004105080380c4503080e110030746100c01c01483c000002c40c82350390103181031081004100c00020390b180314010a40684001220b88032030955100368060340703180480c0c003400c0043c0600c08260403811200380103401c1c0440c0043c440c001c060410117000800c241e025150070411091104240f180c84c20314003d20010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486457185 1250 486455935 486455941
    0x402090d140c10020a02040b010c08040b030a1515140307090911040503011503060627050601121d0601050603011d040609051e0c15181309030e09090105 67
    0x5048114100d802401c9480088098451080402000b460b9941c00703442240010030401c00a036454003a804200d10480c1081005141944141c414058880e403049600342443d0402c0c0300360446d41c100810b24250640d0740c02d90034500d1803e600803c402800c0f20440b480045810240042c01406100280d01660304204240704010b030380314906100712010904002166003050b880c1001505c079551007241c1c958203080c15001d030342c0c60a452003000c5a2044c801004002d580d580c42e552001498000e820356030b2104c0d91444550301c200c0d004154403146c1454040c5140d105032000c1401c40711151220340c1c1c007440e09011003061403002c2000b035024240c102c422a045624015521459420281031181020107006c0404d00708007a82d0443d4001a6010080d0345002c0025a50f02d02c40030300311844d04c0c10501c1100c001100d14140f140324800d0860f210710b00396250400d906e05456072040c5541c00c4642042c00c1101c042c3c6901740301d21410701c015102c0d80d00c2c1c3c221804800f08120380303081d004cbd041c040035074507003018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486458435 1250 486457185 486457189
    0x1e100602030f0706060f0f2121021e0619021e0708281205040c03032006090601080c120a0b07030b060d0507030c1115040609050304061d040209 63
    0x40e281e100b0320000e1119542c00903450501c1c09090f5035440003800d141d5510b00814100401901407060f242d01c006c05141100c0c06425480040310b0342000908507614020f100065590140c0c3d184854178a180111440f0000702140e60840150015040003690030401c01d1061002114601c120f0300450f0140660a1000c1103031015020400759070000c2d2401400549081004911000c1d5074800d81904601100384100740d042e031400c01e04e8001d42500007209070907a09214121072180e54003c540154014840500f10355003036444218240800c8032400e4106500002844200301d1144908031a201504180d49403ca03668500801210390501c24411074103914120301c0d00041c144a41a008042c2080c16200c2085c29070041c05100316140d0415400100e142820300c031078108a01031700d440c0d41c040110701d14488049800d285460700c1070229070444196aa00f080c80200d0181d0400d000e4100002c80a40c1c1e0303a90586164880e038231800100c3d10440300905108201c11840144040c2a6800d41c42e02001c040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486459685 1250 486458435 486458437
    0x150c06180314250c031a01030b060d02150a020c040c0f050f090a030602040308090306010f0b0405040b030c0306010e0f0606041404020d15060509040f090c051210051e10060203 77
    0x2c04030b041e210b00030602d10f00c050340d02e810318103402c2d4403150503a20419242c140790020000d05d000565200c40072102555880038128281030407aa003000c80e24030075407900400c000c44c400c0d0b40303001a03900000001981803500ca0410003031010294680007400c2203c0d2040034070050300c48807090030050100c0c0412701e100c40798000c021a005464211441e40e90346968034000b41000c00560005000d041c808074001c4100a1240010030b02c00a04508855aa0381d8441d503908111150b400362988140d014001000030341490740022100480080540701084298000301e0300c1c1c22000d9010071100e211003c20f02c8221818110324640045c01500d49920389401c241007807a071452184000e40c0910740c00103000302191001d0703000800e20048080b103c0c1441c2d5903180700401a800c1045007070b110f54600b5095094904d034610640d04160360007500b00c0010380c948820020310780540d0800940d1400b80e02507262100b041d61080078407900d42c07072116203942e0a881c1c2140e5105040280300095090610b08103010300340e0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 486460935 1250 486459685 486459707
    0xc06290603060d1401090b04030c030305060a0602030d0b01030617060105010f051908090c031b010921020f120601030f12051201030803060301020c010e1e06040f060203060604150c061803 82
    0x3024101c1c64406140d80354010b000b1824060001d2107264123220825038811008295903000e6a41481144c0f50700c004c00c039000d82503216070405070740100000c8000e41159040303c0030700c0605040c0002c80f19614002c3e0b80700d440700f411410480d0b802000040c0318541c0c004000365040701d07403803500504016101c11048800c940c1c218482040c00010350010303840000030450400c1c9900003900b551b2079000d0056207452801040110780b40429690003010641e4540c413260807409040e0751680f40d03440c06c01c540901c0080c980c2400e0b00b940080403200d080d40e2416080180600851090070b02da1060596400c1c40075509107000c3c001c100b003240401c14076919602c421101030541340c2101d2041e03601e0b191b82000900911402945010550074110010740c0b420000c10b8000d03803403881c004590441c0c544410102d0720307950301320b40007054910444074480c0030561036806180d02400c003070500c601d0640c0718900444403d0711900242d002030301c0241d00300100203650080b82422260312944080114299074003911101040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 486462185 1250 486460935 486460943
    0x801050c030103030914120307050604060501051c0b0705040f0609150e0906041d070e09070911030714070204060b0304140d0c14011b08040611030709090c0c06290603060d 75
    0xc83e00306d00695280c94810000d802510b08980d6107040c46d141541d1690021a0151038032480c100000507a4181a00145215030354005003900d403042035541e004840d800074080004100044c40041004a610071b45000500307081d0716642d010524140b020091904454200020001135036a40d01e030030b46850800d690000011100030480f07401502c0845242e610800f038180035072182800c0050311806102c1c4150050071021300b0707240d049403614004000d85014080219107100f0030400a030005200d40004d01069072100790079840e01047d900042c00383c1c0e105400100c14140008144410000c05810a04006000314082d21464501c0320010384448013600c400391414414820300030350307100203502080052001040c00030760380c4100e41c1c004144280c00ca4044540507d004076410445403280c003500c3c0b00c0c41c520740d40c1a40075410b00d0659009400c0b4686071105201904543c0300000e5450b0140c0706c490002e06000c240d0159080901e12081d101c110782642c040c201c00c20a0000076254005d1304174280f604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 486463435 1250 486462185 486462209
    0x9140a0b040b07240b03060f04080415090305010603080d051503070501030213091103180c0f12030d0f0b0307090504020607020616060c02010219110d120209060f040801050c0301030309 81
    0x580c109050300c2c594010111201018460356013805000507405080c4205064084501950b0b81051143c0c200805503405068020188001c00c003410200d01e014105090074600007020315541d58815082d0344454008881401003c01c1d0b90f14060310910a03e0b6000c1e04c4040c41a00300744564020a443da030440c0100c50400d0303000210110701610000a1500034110003004100c0c2144802c000c0400c3d401c151841035040740e562a241c10842c0c00000c48491100c001000303058085032000c20080481c4200c0d2031514140030500081e0000030191081006440c0480c1e8007086042d914000c042c1840030755000100001e15010600c009600d40c00103a0f41200d60558515a80e1003102107420500d401d201401880c19080001c3d4440c00c544c19009000c020051100018000300104400e40c1d9500030500910004e9114050b0384c440c181c4071b42100d0940f00312a030381c01803801d010f4401140071944013585203074002c1d2000030100a190001d10401d544410310207600d60455046550007400420076204010032008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 486464685 1250 486463435 486463447
    0x1a07030f11010b0316050103110f0301060302160807030c02010e040e060f0402040905030703120f0506090609101a09030706020601060906050c01060b030403030b09010f0614070f1209140a0b040b 85
    0x4070950200084820060850700b0346092501c140d030604616000301070003c0d040c003041000f41055001a0f40a0299462041d429a800c0c00c504400a41000c0b4641065409020000300403910450042681e1030003035881d50311307400c02c0e4000540300d21910400c4a01a40c40c00041d03210000000c5495a00914005680000358890340000340240140303136006092804005103860405800c10404008010fa00e6001d102e0b8007494135a080480e002260030719040310803000010103514000d941e407540401070b19200e42085890307404902c48a0581c40c80400824000904040303245010000b400040415100070400c5c3e6042c1000200441c200d4810002406004100c21680060a410200141c11034207542d03034591516050050103420203034509405003694000108400d00a4840341c001c0e1002c9485000240100200301900303540650300170340f007401015042c08000f8160403e0030107460302c5561072021040c2050025001a2034848446110f4400180200b00c114580410f450440302c0b01049507498070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 486465935 1250 486464685 486464717
    0x60901062a081e03010e0c04050904020607030908010e0f0613022815090501030b032e0b031e07061b031125181e020a020a0b0c041a07030f 61
    0xb014241408a24030b00c01544491080c1d43d0001441c100c1d0b5001d81c920344251515070300240c9a00c901d000b41d640103110040081c005d820300340010705240b4820300c0c1000c1c00540e80e1170404c0c01c41e0340c080c0c05d16910740c00100191001802c1044255041600c0b003452082e108041d90004459140320155001c59034403803407040e0200c1130b030045207100034403811440b0001e1610780341c2c0007010241326006031804203241c80446011403c5c0000d54880503121805604064078220b03111241c100d4100f81c081c001c071a11100704140c02e840034441910304161410720001a242070320001d03030424001d60001010490902041c075146295100e0907201c0075010b0030040c2e40511540a02824030324514410f07106111070500060240c0503c014801c112400030150b0400c2843c1c2c1140720080d5001c00b81261848005205842d2a001c5594001c0210704614011591884101e40c0d450703c1d50441110003648405001c101081401c1300020b9407465010503180482c600062641d01400d681150388c070260400c5118a9603181030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 486467185 1250 486465935 486465937
    0xa1106070605041b0b070c05010503060301060f032d200609040903121104060815030102070b0408070506060103020705060f0a330905100611030708040905060901062a08 74
    0x941c0d040300e400c2c031691070303c1e040c80141400400c0c01c86415100078280068100c08080c1074446880c0e0149505950b10300c0d04d401110303103400252503503034155a58040068040c600750fa80c403000354401c8007001c0850b0f10030701003640c00c100c002206a40e054001420000029003200f5202c001c1c02012400c1050f40c180c0301c0200304640220126039421a103418005400e154000300c9181c5101d42d00781003032080d4004c03500040200e008600c508004551a007000c1009042c80000c00018403a0240005091843c9602c644c00708a000b0381d0b0684402c0b900194030020312005000d001d60110081c2800d62811035548da9103603079070310b005041e407000d1f2110202060b4a240c0b160000b8503903045000ca060104000340c2d2220300e0000152500c10428042c8080000f040d4089000f403901c0f4003500f0041c00c41c1140b50801c280c400b4003030440110600d00007004003034001415800a04060b002508001445140c82400d1009114042e000070040c4072200f160031914400c0102d2551072480d0308070400001c5007071842e0044031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 486468435 1250 486467185 486467197
    0x6150f0c060212150109051c050102070b0c0a09060c02090408070c0f081b0a0e010b0d0b0d140f0115090c090e0411010206150604090e0c03010c030b030706050c0a1106 73
    0x41c0900010300c001004060403e40d60081c0a10150203007000007500055804001c10310565410911003030110002c0c000c507a00c920002d9000380009841e000c0bd90342c0d00d000c4030804451030200751201185110085600c0107020000e000c0c03d04200c259500703c2d8002444080004000610b48540040d140d0100020012030f04000c010355040e4442c4941c0752140c440d209c1c6803e41e45608407100c0300c4c620f40c0c1c061810445220840e0344d806181c035100e909048070303e002c66000b510200120f6460300c10703881850722080030b1401105e0050000803188201c86807c50b0509180d031901c0c5001c0c1c0e06041f0580c003810000064041100c00c04c00e400251208204000c1d02c400d2010b43c03040001402480820017484480202c40004480c01d034240c500c0382d560560788503c0501c40400d2190410002c0c00b0510400300b4940c007540c074081e62042140e502c1414000003070300750ba0841081e040007e4a6140c01c000c4c60804001650142001c0c0c20414140b60001c0c030b5840c0c1d5180f4100c80504401d07810205c80d022616034408581c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 486469685 1250 486468435 486468443
    0x1409070c12021b0a0302060a0c03170408030a060806102304110c0c03030a0c0813080a062004030203031e041e0e060105070f060b03030c0a061b020106150f0c 69
    0x401076108034006501e90340150409100707400740050140507803409a20b0342c402d40354010051400c040c1250002c581c4a00c0b000b4084007400100f000c0d802109000c0120b00303224500c02c010b450703664075100d500c3c0340a881e034941c402e024a6001c80144000c3d11581d0181c0da0998042d61000e4030204c48440a80801d0a000800f085e002850325040708000358503100140000394000080380d1000340001c00b8590b8904c20340d000c0710005007010708040000b550540080c0b40017042403a4095149444041031810484048003c4030010740c1d50891080c5c00c00381203080481040d0a004a6082600d1900444e4907441240c0e001810f11901d500500c011030b82d00c4041d43d01400d200245400344400080c0710045013005070090502d0940d100000a01a6100b0021200c00b140d0028040b800641c20796a00300c06814201c01242e49804244007081d034100c01007003e2520b0b24058403001c11858400c40c10300b504480c94180680469050502c284902c0d07026254140c0f4445117860300003000850000d04680d04441306d0380c020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 486470935 1250 486469685 486469703
    0xf020316230408010e2506030b060909090606010e0a1802030c040902040305030a080c1c0e0c1002030406080903071211010902040c2a024c020f06011409070c 69
    0x4903240c40305504c00c0001c0c07148102103c80b0140c1b04880e60a10392000200b1801d840d0302c2c0c503018042c003442a084486c03410b40140800b400d0804000c0007640500080b01c541e00268480b000700700c0c0741c1d03034403080300854080d05540c4140010300785100800325020381c41c9030003000d540000214600000c1041103a0040c6030380081103458030703241d1500988070750041045070009242000429204680750003114004000302401144600482103014003505819500b41a1409552007014441c3c950054000076000c41e98003239540c640c1000005090010054215a82580107021034000200882103100383d400003800c201040b0489000442d014142142d0003d410074180480301d0400c603000805100145181222607850b40c0c4090b0420034a441c4405010f540540407091000310303110000c0210101128030360000480c0e00c0c0562000011000725000a81c00c02000a03405071a41c0d4140700d010520440d9030050b1440754500710140d61010340d41c544031441050044046103034140210100405103500a40311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 486472185 1250 486470935 486470939
    0x10903061a0114090603150f032b0207080a0b1308071a010806090703030f0e0901030809010801150804060c05090d11040605040903021908041806090f0203162304 71
    0x306a0a0505108007804034081031807050f001800302080c0c40090801401031421603071603400c0000e071030400c0b8000700e4011205a404115584041c0146854034644e210f41ca4070100b00300005c10880d6000c156154215000920103110424012030689141500b0540300c5099440e010226503403005051002021590001014400c1040d03074040c1d040e20b03407644588000541e91318138102c0d4961404071200505600038481c01d00009014503860100c600941c0740043c0c160208002041d01e20354280c0041c0c48142c408a40e8070055070388042c4450240810840100d0341c070a142d080502004005403004208a4507940000d06251203101a108130100081105180102a0900300b00c181d5480046c42d000e01e0400c2804941410705003d41503d181d071540c01000041c1c0516150010010030030411900e03040708000c001042320102d48250101d002900700000c0e4980b52100b550201d5004001c1400554014400c0114030003000e0a41170b200c3d0710a0070005034140c0704602400c940a544015148000300c04900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 486473435 1250 486472185 486472211
    0x2100b0303120108010e061e0f0408040504020a090e070c0807081e0a11010e030a0f110703060c11060f040f060203060f0a090603110402042103020106080a11090a0911010302070201090306 82
    0x403840750003000f0661f07078151284417506807002081000c032140705050700046445030640111940e440b40c0944585405c2544410024090303034091151840040c04001c400d105541c00c10484c1a00710001c0d0800030345d1030050381d55810250040080107081c1110115a00f04001965000301d01407106034403201c5d98030120700d5405007070303158841050a140d6280c440b498038a01800011241c41d000c050700c40b03184d400b01500088403c11030230b4488103030318050400d0020001d80749000c4d110601d50117803190110b100c0c802000d2450301100601c0108110f01103001e101c00b0440d00341e5511003031500024056665030703d0780301194002a0b540c2546410250500340060303203c00b190301000c1036a1144954980219030f020412051340104e0180c4020100f0141c58150500c00000051306814400d000109070580d03105546411f1600d051702c282c4459016549088540c07420440159022480c07032810000d18205480d280754248050030000e060513030008510f419607000748540d200440d4444010b01000803080c00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 486474685 1250 486473435 486473441
    0x305010504150b0a060509131d0105040318060c031d090910060e150405071b0c0e06040e0c04051f0909050c0105030405060c130320031c02100b030312010801 69
    0x6450142c203242c0107a4100c2c80c5040400181210f400c0e558a50804045004100c40d0444459118030300550343c2950080d03007000301031543c180b10501c20000171035103001d040c0a000040c00d43d552008c41c81e655030701408140e4010880c610250780602d003060690741030034406856100c8404035941d208545a0811032400c80001d500d074200c1244130400d000031a40c6010182c5443d41c191206070123200d090101c815141015030000d40d0042c10341c0f428200c40348094521040800117001c01740d03413100a1300001e02c07280d85440080ca81219050740d0400a0010400106403500141102140b00c0c0d503c51002c180301c501d050680b007401890208201890560340d4000e20028000004110751500034500880125030082c030540384219041406841503656160280030954401d40d841208240f40e040040702042e4003008050010f2039010ba4020a01c0100080624144848015030041084c01d4491502c2543c00b01d4035400381c12041c100412500700190000741580940c030103018a03d044000001010303d0150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 486475935 1250 486474685 486474713
    0x30e190f05010f0c08071e06090218010e0a0e0708070e04170c07181b03090c050619050906070f12030e15040b04050c032e0e1c0201060305010504 64
    0x41250304005039a500150b6110030068401c0c00450f82d100000350108100300010010948205040022200c40000c0340b2440940720b101a0340096844801104504000504076940c6103100b4480a42d50301d040c261700d1105200525442c00303203841c2c281c812140a410410f80c4040c0c8014010707505082e031502541c0c0d586020440e02070b00c2d00a01c011000c403c10031070104a4083c481c04c4005400c440d420000c040c200d00b009011200152030355802015000d22482c164000d280d580740d41e0100b400c03142414403c840ca0f00300e4001511440081162420031400101100980c080c0d5040c15a140c04100000415034010150080d100d078003103ea11004004a420404003680b020b80c030104601c280050001d0760791507220b420088c01021a0000c10b01084555042540c028850307400c5440c15122107010a040481800c6031082d094101304407100c03103400406200c1c0403d070308401c04220084075000341030782d2484030b4507043c040001d40070000c1190600c01e41115018581040c0240013070306103460400c040d52816 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 486477185 1250 486475935 486475949
    0x111b15190914210f0702011b150c0816050301051c050604050708060c040f0311041509060501031d0714010207090507080a110c1b120a0f0302010608060903040e04030e19 74
    0x740c9515031002003e10969003d50309a40055007443c003036500540f84144e01400754102030070ba021038103001480e0406a00c212107070500780458501e03501c0d140030703005a5003d0310440741c01c120707e0185610503500005a90448104850a696031010301c110714108600d4010b025200740508002c00c82440400100c0008031880c0400b195101c2e6940f02ca50350460056015000140d42c20013400c00116920754110740e10710000810010f1410148420070304000000c1e8441f20358643c80f103008110941c0c162040d0350044034020b0304800c2d056038510505461b4100c0d805403c01d41d4440d442c201800345d108200c1d04c000740c24880c8082040f030410350030103010300310300311811a60070303003052694210000100d040d40c1148055000400a00060041058010350782c10000c0d81c000380c00d10f4000301a03240421600711014091031030b07031080b00c0003818000e0070b4030401c1d00701a030385038400c07c28003800810000840d404c0711200d142181d11a1203901d02146d26845600896602c807800d140d001180391a0107080c1030880c2c0079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 486478435 1250 486477185 486477223
    0xf01060302012d140c0a0609060501120c09050a02090904030305160f0e040c180e100503060103170304111f030e1b010c15111b15190914 60
    0x2868140c00c062499403c0c01164000801503001d40c000e010310b007100720844400460b00d04005e0100c00c1c0510b80070703103401c0c2681c200352507030400410b00a03940701301409130000c44151140c000c020b0b292000c0c080c0aa205010080343d075500002ca129031b00b0f41c15100316040042c50142325003010306008003d46003d5030111319124518640c046001d0145080c8000f601590300c548028030950403c02c80141006100039090010200c15403e003048103540301c1e000b03030041110841e040d04107944110340c20101c541045000340d002c0401800400d803100b12144134110031640b8999203030b441e071416110341c14203114581c1c0c014601d40d89442d00c05004410408100d02250740400487d01d071910015582c54030071500108240a9005a44055104150319680c5500501e5084d600200400c0801c1c1111001c03102c1d01c0c00410f02041403940c0d0240c0c0700070601201da801004107040c0b8100400904000c070054400101c0282046640d51802c074550800d014241c1c000541e00642c903419104681c4405040c04070b117036130401d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 486479685 1250 486478435 486478457
    0x6040e190b010503161110061503050105040c020604080d06080615011d09161808031903050402061803100e01020c101112041a0412090602010b1e01050c0f0106030201 73
    0x11060b804c1d6841095040c5c84055004010031082c0c44903000a03c64103803601804402c00110741c014040e10005009004002030b560f11400401401c0340c0f41070300250b10550500584c1c00040e5400680c09800c035801c01d41e40c0d640c0d10701c0d50b052039004118562100025003e27400800107001884050b07850000c0c0c00b0788841403c40c1c030032840048203103150300f00540c1c002c08080128503081c6940203500d5101c80c0a0820200c0c10749800c5258051800b16802001d80e54000070700499100c2450030102142410b504042c0a04e040a034001082c1d0b01811319a01501501c03911281515501004600d042d44000241040b0201c0300c0c10700d460203944180c001000d148508040b22007038407014031541602d20041d12030141071801d000600350800201900644601c802c114a06da901d1100111481c000c40c0b140100d690b243e50041d8025200d448180d2054065904d4070740303840803517140c50007918035040c40055540400c080c03074001a1810b000b120701229541c0314003015007080400c15402841928000d0b21045081c0c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 486480935 1250 486479685 486479687
    0x50a0f02030613051e010305010501080f070f0e1308030f0601200a0605130b090a02090f0c0901030b03030415050306150a0212030402040605270f010815040206040e190b01 75
    0x403000b80c4045400102041d0000d02212882d88115044030b1640340b04044100d036451284824070084e00103075a40d955132001040964410040401c014005902400d01c80d031600710130a04014041c0714440c514400315000551004500205109444c0e001c9001c0307490707090114152040050859006010940c8522230095244003080c04104801e2400e00801c5030144907501e0070080e0801414000c1c0e0302d04030003400c1c80007400b0420500e1189030340d030f00240584030050040042c080c0018000024044000042c03008205031841281c103001001c1c03c000c903580d02500e0100c0d2440c0315540c002d80c0c00400d0343c1190520b19030b1040046001700000c41c0d000600200500400745117225054012000d64820840101070b040048e02465000380000c10000c0d240d590341000c180503c0c480031204400c410038020444058844819454100e290300c401c03004150305001c0c4160396007041468104170351540c200043c1c110340d1020105c802500680c0c2440f04982049104090303030350114032030203034a5400d20f038002c1415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 486482185 1250 486480935 486480937
    0x151a0405071d03030f2d0a080a0c0509090402010f02070b160309090b0a0314070e070f020610140105070819181d010302061b0f060115020a12080c1903050a0f02 70
    0x80442040403458102290410481b1103036070031820043c210f00c0d50f06403005881200c081c010001850b11050700034902807040800f2600c01c07003102c3c070600005102100319078940500b40d03513010364282403ca00d01b1117041c80c1a854040d640d4840b00e100303032000400c480601120709010075403920030389505a041ea161207600f4181c44110300d5058104c05100010000308070801e0807106100d0520b81600c8145858860481008000b121090701207a081f81c40c00c140c1075410400c0342c0d031150111054000c0d29041c9a00364a0b050101060a810844003007400ba00744035425048806000752070294400f0081c900f42c0141040070f4941044000f106a40d400060100c01081064101041a00103810036800c580c2000800d4004016a40291741740c2002d01e801c041007003002240c160001801010190325100007100c10f8000e03c90300c5070854000c0c00000d400141000c0c002d1010341841e04040354140d540c1c9060351001e000700b41a5417983c90188805028158066001500801c0c080300103200c0c05c05200242816 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 486483435 1250 486482185 486482197
    0x130c4415190903090b0301080318060c0c1e0a120203070812030a020a0c050627010605010212090d0210050c0c04052205010204120605060a12151a0405071d0303 70
    0x800000c5006a4070300e80c0190300582c42caa01c80e0904481507a00c8062100b81a00260840505503000044e20041e2546001210103051002c54515181003e20345107079498002d42d0b83c03142e00549080e451070b0152803a81070f04098111000e080c100321160b8034042c1c00c5801c4070403642a4000e0284900200c0c901c0004900602052841009589140ca5048089c0c4c001c0d80720090781420081da01180c01d0000fa0144411030003201880496500048103054200c1c0e207070700464245801e41e142280030441039070042032001a00303071030320300c2583c03039102c40c901003240c14020100c0254800780b090358040030250080302402500d40030104454100c2d101005100459605132402440440d041c8640901007200d40c0c041811035214800143c201036883d001c040381101c0c4006c0884004da00c43c410800303a802c0c002ea0410080c400e942e0401d8100c001c6844107900700002220b5100c0581d201c81e1300b40f90100c0300145034102180003400c10081c44c9010407004240c884c01d140300072903005440c4121320041c6800820340b42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 486484685 1250 486483435 486483451
    0x1501050a020604030f05041d16030506010e06070203191a0703060311060a0207080f0c01080915191b030509011b0914150d060806130c4415 61
    0xb0540c5464909440c3e03490000f80500801000b0040842e0541c4032644091441c4c0c075881b5281001d0400141090003011160354802c101454081007080681e80120304a02280b030a039022a91843c103400440e042400600c144030800d1402154101041142403007140d030414000c144041c1c0c1d455070841103003680d200340b01c05006c81e84042c40104051400c00d0040142d122a401100c064990f81e190250610000807540740003038029002d040000e50300070503000e90009036000074004100a01450802400c0064624080d16081c0809a07600c01041d0b409082d03040742042803d10a09036461000300506800c80382c1020a5003840d91426007018002100c98604103252110786000c1c0c01d11341c03045401c5005894969010700710261072030390b00000070000c2640c004107034000b040c07044c18032000c1450005d02404071800e03580000c0785800880c6180d410003040e034800000501c10f1420407010054003070856403032022040c498009482c02001d5202c0712058810b4400196011240245200b00301820200e07240b02e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 486485935 1250 486484685 486484693
    0x12051002210f040c05010f1701080c0102010c080c040308090a0e1302130905060406051b040308130e010b0909060a1e0f060219022e090503060a0204051c03030b03010908031501050a02 80
    0x40170541c00350b1803603281d001e100d15009910902e1b85102c001c403400280e011804c20340021580901c9075a0a00400c1c0302a1202d04114000303044c801c6d5424468442c600c07003e4950315000ca142829a51810610300050040e24505409424082803c1a59883d82c00c0300728031404980450b040b01d88443c2c0110703400c1c150000041e100035516a1076050140c5401002c00303003003c0d08000001b003202c2201d4041d10145010360740854031950200305071900030410f030b00b0550341501d4950040101c881403004942c2a624140d800715116124040071400b115500c0d002141602c012804045030000056000d80840351308041d090307103040c8d88080580c2c071020f061341c07820802e0740400b03800c0b8050b00f09810700811000941c40b030065401c0c004030a8034200b42003400f078500002d500740c900700103902e41007000c5c40d00300404000440c9810326110014000303503042022402c40c058000c0101051601a078000880340d6001f4000f030100c02d5092a1250080c0c1c0100c03828100d4100e60100407085510810544d0b8148030660014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 486487185 1250 486485935 486485939
    0x90e03070b19060603050f0907051c060612050309040b1909021c050c0a03052d1812090109090e030702011128031e080112051002210f040c 61
    0x200d064004001c0c203400c6842c406056242c00d06000748540402001c09660004180c1030031801c09152110280600c8941c0d0b106d082c091041d42d50740c00c001019412007109400344502e02d85041000390100e5840080c1c6d984041042905010010000f440045d5049808001c081c02c82c0080040d0b044903e950742d410b03990003903020720601250707030b00034030003203280c0940d04400c14104c1c2e154009440044417010040781011844141140e010300405410a0340c80b0702180040d000d4503482e0b940c850462001c102d07c0550310002c100c8022400004141e03040102050794070721102d07103603900c00541c070420380d10340010700c0c0740d5000440d141e01b0300c6040440000c01380a54540724442e0011500e60f1a50701c030a8602d40240ca0410084003c18490200d03181101619000b002240e1704020341a06000301700b01034004100318100503070a034040c61712815201c2c080c1d038007000070066003801403a01d5034180601228901c00142c0503406541c4004401e07010109070901205590f401c94003031101c2e4002c2d038000300508034182007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 486488435 1250 486487185 486487193
    0x26060f0a0905100f02040f06030c051204021801030b1603060b0906130909110906120a12020307050102040b0415020f0a12050c0109151a0a051302041e0609090e0307 72
    0x1c8190640510704a41d15011050290001c075001030310094402c3e41d001070100728100300120014018071481c2800c004011041c003003e001c80c41885104003800c00d00070001000c55070782480c82180340e000e50b844041c807503850f071900c00d51242d015907030101d0381507480061840c054440d000b07003c25100060002410108100c0c18405d25411224806c500319004000101c1c0642c0d1038480d90f43d600380511801e00c031020b40d41c400d00004441c0544401d000303001414160013003100c0011291006a4030402204000d2900c1f1000c9096000d80b0000174040c3d4000078000800c0c1c0c0d6488050f00c1504c0000940d5000780304103c406986d0303450462a01d00c0f03541c0107400303036401190014040d48904406820840d00d002c06040e1030314215283d042d001c0300e965034160740a0070400d84a102d402056010030200403100c184000000d2440c2e025481041c0c0b145040031800c04085060f078040d01c004040b035404403054444170b5084d000c0030100d54001e200000742400070020740c0b502c05000b00c4441100001c0614500b03140c41c0c071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 486489685 1250 486488435 486488441
    0x21e0a0c0507050307121217070306090c0309110d0303240e06030303070f05030604110a02010e0c120a022701031a060105030c0d02030a0e0d02070303180303021e10050126060f0a 78
    0x30110301445145048800c00034081d184c0a4803270540d070380d8006009418141104101c1c0c034640d8504003014a00b000000c001201e10b405c40c041c00c0011507100c58003615514003180079041c000c003032202c070b80410310030604107040303041086090300c444400c2c41d40d803560380b5030603d43c0d00d0204860110004140341222442c141c081e10045800140c09800851502d4102c0c5110142e680803541c0840181e64508070b40b940a4410b000e00c007206501221506240a460715950350b40c0c400ca00006442208a0400d054820061040d000c41004d040b040020300c560756401c003c46018076141c3d101280e00d0f4800002800d940c0f2400c2140d12510003629040d00b0035003040ca000c4000d40000344140c4120b030f51100440285a400c11040d00d0040c015402030100d03a0542c0303001410329260880341c0c80004d9030030343d003440001c0d00424000181d0046503c51079208105400701481e10051910f8044218900400480e00c040100d4141c1d60030505034054444207000300041c59907c00742125001c10101c80000030843c03920042d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 486490935 1250 486489685 486489713
    0x80606030907030515160f0e010e0a0e0108150c071a1503010f0e0d11070603021e040602030909162f120901030c0f090504021e0a0c050705030712 64
    0x14007110740c4a43c0303c0d50741074509080000100c04040c134080411450000385240c6140341d819070726001b0360b14200c194015150b2046021014144510146070300626102d5080400003400c004213100d1640d6914412980c8541c00c0c1c11a01c850004608000394041442c0c1c821100c0f0b40398413004001a600380c0302e0030300c4880030018050003000300c041a080c1115036000d00030010b41c4040d941c80050b6610b81e14248929280036400d010301400185040b48080d61004984042110198140580d0381e03c0100c0035802c1c0d42c6031600c82c0d512010303004103000c86c1c010703400000b41012050030f175148c925580712040c9014010100c5401d800008100d80c20040001152521103e80140040c000e900a5404480d1040c24416082d09000490101080905a035a494010340c031004000e1b00380ba0000c44081800144642418054640a01e8000a085203205801b80d002c00e00010003c515907220288002d004040054094050300c55100384d0b500490356150128244007100c7c005180481c43c4c80d0565140f041d50000b030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 486492185 1250 486490935 486490951
    0xf1b020d06090b0105031b011707020a050f06100504090f110112061211301c120f0c0c02010e0325030b1506071104090501060f030c120308060603 64
    0x20102400000300c00340900b4500c14450a6010340d15810070040c146845400f0111210240d84c8907105044ca903000303c03403541145489050301c603040d03543c003005070300d040352442000344a8030600c40c1151107941d010a4944c060000c80c040f001240b503070313202040190761207240040d0180120110303c00000d510040f080601c40018182808103002e401412822162240e0148004000b101510300030821058ad0350360082008855a4000511071b056549007100060411040d000e024182c03101c101d02d04000e8103004d91041454044400416140242225a15001400800c0c00c00c11483c2c04d0450314018180203103069a503001281c0d00c1c0303400459440341403082c56509801003401003d41c1060b0601a6a640d200c0e020180c2c40c0503186240c2821440001440c052405808089580d40c90b502c05003152030382e80d00a44854444001c2000140007071210880c014060b603e070513000110704542d801e8000880f40100c0b40c80c001d603039450306400000d00a150000780020070400024a05140140c0503507001100e07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 486493435 1250 486492185 486492199
    0xf070302010f020c1b06031003030f050415050c0f0703050c040c1205090d02240133020d1403040206070206071b09020d0b0f0d02010807030b13060302040c0f1b02 71
    0xd010b0701c0802c99000e2507140c1480d4029030658610f03004030480440350003000b41e40451841c80c10b0309804000703041602000381040060210b0601c1e03503100300c0607200079040b80000003290014828001d40035600148240c800c5001d0300d1078554406c100402c4500450b0741000241101603004c40c204001071601810710b20a211070310803445180f10440c030445214940d200300030070140700d00e1000a490141c10a680c99110711200d0800921901d449030224111a511100d042900d840c642e0b052824580c03d03080d111540e2145042c045e181d550010304000c840c811611090b00128145c580410103103c00c480180d0441c004002000043c01c00000802501d8058180804000f00143c4401409452030b40401107480d00440c1d40d40f2844074520900a00410407240580348501c0e50000c02d6494074542c0c0c3c00b030f041c0480b142c00540140d0090b0030141a03c48010f10810851605118601c020040c80c08164021490241c1005910b40902c054410003640e507200d191142003449002d450781441120100d0304200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 486494685 1250 486493435 486493451
    0x90308090f060703050702011e05060a050d0f0204091e0c0f15080f13080301150e04050105030a0b3d0e012108071709040e01061404020706140903030f011203050f07030201 75
    0x81080e81481070200070b02000c0354ac0d080c682d04100074a80716422a40c490b00700c001c041000a584000108103480c3c0c15607001c140107285003801d140000e0940d550450b82a501a9034000304003001245009880045050a032450303111303030004051202100002c40820298000b00300710059400c24140c1c041c801200058038400550b41ea004075400070380c807128030903015000040c0710542164406d40c420b4802c0c0da04101d070358500b900003596610310140240c03081d4181d501260300007000741032144502c4c12400c26640740e40d03010500880c0b00165450542c0b040c80f0b035480003007110b03c100e10000b8101c030f000f02c0d40c407070310b11840003c10b503d600d01880c011100140c00f0050500050f40038103069030b0040301680303070a4a0301c468900380425543c001d0074550070303a45031180602903202d5401c50300c540c40c1c1d80dd45006031600000e28005000304421a5000082001d1108014501d1000002103104030050b0b01a09050b0b60b94403e8408802d81041d0002e01240042c0400e14811404c43c01900010b4000d01c00465801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 486495935 1250 486494685 486494711
    0xb030c0415050406060503011505070201080105060304030e06043c0e0907081009020f1002070b09030c0405130201020d020c060702090406021c020a02070f0f0504050c040315090308090f06070305070201 88
    0x30131540c4800c022403008401000070844000c24500c141e021800c005140c4505540020303d290300502955202c0c3c5004000700c1c081c1403056050f4442400007601c200d13a0356440750040340504000c404000c8481100440e0900b041003a0449464001e01c8003e581150a092941101c80c4c00002003604c500b0303109244000940e4041000b201000b802d000b60002a17841c420f006000b0801d4a03a45c40b140944c0010390a001a43c0d400506207080303170912001c050f26088034200003400c1107011400c1039405070400c01880303902c0c0100c103044c540c218800d03001ca6a001001c5801643c1700c8030103850807a44900288002405420400840d07a40244200c200620b0003042001c1280c101b400c0c0480c1c9038009034041484906580c040100201600e0205078020041c0e05c1c1403052800c5082034003900d40942c1d00d45000c81c424174003071001c1d1005598400c1501005040c5e1a902c20014005a4410b90000302c444000c83c0104d4400b00f4202e420034800c40250034035540302c1506501821014141c40b08666803848610450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 486497185 1250 486495935 486495941
    0x20f03031e0a05070f0f140c0105070e0306010e13030905190f0f0e01031b0e04060207020301060e0f04030e01020c03030c071401030209030a14012306010801090b030c04150504 77
    0x2034101140c45114003000300c070940038001d1000749100c140d40e2078407050001c81d0341c100e400c1c0c141020840c07400520b48a01801c040300c03040d84105244103003440105503d000044190040c9200701225038401094034841420155540c8080c410551040055804525243d4036490548035107802410441c100503078400101b100c1c4440c00684200c070155401003400320300d090603104c10080454207540f40c0703550704004004001c114107100040c07203a5002c4040400085684054500520642d03484151030f2601c0d040800c003079880b000049100c0c0d4a0150042084e2814060180c003401561800d2801951240d400791880146d405c4041e05611548035084090342d800c01c000c0c10b1040f4204043c0c810980352070a41882a035400000605040c01480045025100020120380c07840e0004999450b880200c01a140100100c41e400c0c41c001c44504648010341140804044c0900e034280d8521155070703a102904001c94000201d1310740c1c1070300070148800441ca000e4002024205250b8030310072090796150300040c11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 486498435 1250 486497185 486497191
    0xf031116030203090f030f122a0703060609140703091103010507050d0f0b0f01120b10050909060108040b0118020423103b120715170402060901020f0303 67
    0x50f8000243d507100c0d402d140c8040c1c480d410301680107110711a4100e0009031110401d507003221a004011400ca002ea403601880c071a00503000040b4860810814050300740c0b286140c3c00b0a81e0303041d081c01c0c00000e414601d80318030342004066105600700c07901daa102c202d01510800300705807441c0030316000c0407000e55405c3c0b0509020340c402c0d4507402d548016000400058803c910803503547c1034a415078061468580c16280c03a0301d8542442c02403201e0303182c081844020580f80348040d802103072005880b20240d4112004201e4104d003202c104155640c0e40300111384480e02200c2c02003164924400400413000011500c180000c94140f01500701f545525400c1d004205010140403030014a04101006007002241182071071000d00c1c1503040c1141c5056803450040c1341107201030345004100004459840309040310013030000010700340b210780440401b107181da4407682d0040c00c3c6c2c07480d0f141c2600204c2900813a0294031004002c500801c05a9481c0c0030080142c2000e6039190640c003c3d6103000b45104010700013144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 486499685 1250 486498435 486498437
    0x10060c02011e0509040b060403020a090207080c1f142a3c0f070b0a09050f0106030309062d090f03051b0f130506031c08060f010f0f03111603 62
    0x207160301307199080009071846900b00034010070b0b04210510150715856070040a84007600b4015030389503918540b0403428495071a1168845c0507444516000e07180d140501d9140b0011b042080c000e4031114201c0d280780314410754070062101c581e00c2c0b85801c140358042c003100003e10b04024131400c0c654071003107c14085485a860400d044100107422411011440c160341d0417804000499044ca804c84d1005411442a28006442d046100c070001e00d59000503000000042e43c008261010500ca01407614043e048900080f0045595468007107a801e02c1a82030750b0800c185c05480c0000b000120a102101c841c800401e407042021098000c100410264905070056110b440240f0295004010084030741328141b60488c8155842003211005076139611b60403040d00f91030440010140c4403200000d140c14203254070100c850381c07400540241d0350b0300181180d1140c0701c151052508115a0001100c501c4107284015000c102c95400f5814414400d034401004d0001400800386000301006000ca60104a480214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 486500935 1250 486499685 486499687
    0x10b09072f19060f4d031e070c08070c0504020c030a02010b01030507170601030b040c1706060c0303070809030d110702030d08060a0b0c0a0f05070807060810060c02011e05 75
    0x2041045520440c3c03501000e03030104010100c2030f6401005c61500d04689004501440780550302500b8050351144410b4102c00b1002c00d00c540511260740c3d40d50401c4603024110580c1e0f40d9000100b80000d82030714803400055503503041000d07982d90307199400e13001404240ca16030f620f1100420750b61994030003484400c0c4d220700190346403042d00c400242510107030611071b8101420101030048242e00842c20710311f84034410001c41125560180124018031503664265845420300d0103003100c06411a8103440090380158200c1c0c83c0356541400c0c000e46100701d09000000398410000603440f603216800542d08442103000380ea10b072403c410311080c1507591030b22021810701d0f00040c03090110b01d8100401000c0c00704074201401c0525045002460607840d078841d81800d560f0004801030b401c0e500744020180f00e580030341d0506c0c007a201800e01c19a1802d0b18000d40d00e20780306600000c00c00d540030304000b611030442d0000b60300301326040100480301410300f54401c074107020500c0c3c1e111165008103c030031080308110360703551 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 486502185 1250 486500935 486500983
    0x606210e07051e0d1a100e06010e130903050310080a02060a030e07080601060201050f0f040507060806060706050a021209060f042004020a0e0405070525080405090403030608010b09072f 81
    0x20040e000c000d092591b060400076070402c040c0d0b44104000f81d000409090400491002e80b0200700c40741034220001000d54a040d03031190406400c180a0360140212801c02c1514a44031910756680314580c100c01303540311000b40160040d5601c02d07004941100444003d42e40122780d1038190b40e182200a07041a0007603512a0b003005084114030340c240780c0c40b440322017008035142031a03292a0744404040c0984020400740d240054000c0e212541165038041d44140c04100350715140d50150000d400002000d4160300400000c0381c03010100040c145d000b240d451a840600d62181d60316a581c00003104030786070f00b0245e0390294400c20780c0c1c2c510140403540c42c1502c40350a4208007408110803140002c2c00c2c0406e21000340500c41c2d0303616201c00100040d010101c0c0c4040354103c1401c11518500481e40850340c00940b0034100420542d060b041a0308480e490170081c0840407960b8200411045d00f00c07000300c001012010000c14520800001c003584490503115903000403280b801d22401c2c0040780712560f2240000c0708075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 486503435 1250 486502185 486502223
    0x12030408010905190b04260d060806010e1b0a140c0f010509030c0d080a09082110150507020d021f110a1101080403020f010606210e07051e0d 62
    0x1325500300318050500703401030840d9036840a48107005070001d007200a64903ca9041c003010b40010301800c9450701d807120340341c0c502249100d020306a10300a20505001d21000040c0070758485500e14080c50071070094200b80e607000000b41c03100d078000b841008104801d0304074402c501c0414000514003400200080c0580000b000c01d45425200043c05450480d031040005001d8070001249a4112103020f2522081c1501c504c00c00d44080c010420010700203100c005070f596200c0055078481c9914254004100c80b440e0b441c04004291aa1684205060601c039400e0200415202c1c2005124551004100c008142308580101e0001c82c1c031a0114000c80392188884070324160405003c4440c2c0c480e810040c018410250303944441d00007010249418050b0640115040500030300c40e0340c01d19000e01000300601c942e5540c004110511070510b501c001c2201c0c05c1c0c0d2010425a40c0180081c0e035500714002d000d9907203448203004160013400c10311594403064040c113440796a05c4042c803550300350090342401c3d051400828 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 486504685 1250 486503435 486503443
    0x17040c03050c01092d030c0b041806050303070305030a18060c031a0307060f090305030c0706030501080a021e01050714010203160903050706120212160e04151412030408010905 77
    0x1011410700060308020005640211804800407004100f44070040300e0f44030171207413500c1450300000d041009140c00802d01c1d4214502900c2215200701d45a00708040c1a4440c108072070301400343c00d170150000c00080010034010401903070442d02c0c201c000100c0c290710101b03912004c00c440904562850312020405000e5605001d40c00038007400403800120000c5540009658010030300c07944090200b003140c030714004c40c003429400c030080d9042130640c0d6945001042050300d641d140e02429011038504030001c181108001009400709a01401001110744c0d41d02c0610802030703480030f660f4100701d0b003085100c0002d100f441019204030140c03000540c072410400f202d0002c00b40d0500b500800c21411400c100003080c0000742e242e0403901182040f9181c80c00700708008004e84100358113071381070200c102c00344100e1302444008c3c050302501668401d100d21454034200420703503140d0450b00f0152552444148960741c2400e40c10046014000c01946041c2e4895010701c2c15600154480350469548031419405c1c004244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 486505935 1250 486504685 486504703
    0xf0d18060e090c040302060307020c01091a070311070f06031401060305040b070509010c0209042105180909010f050f1b2a15180111030601020304030f0317040c0305 72
    0x12100450050416000504444000105500c24454400840c242c0394808045801864019010f20b99901d40581c0c00380d42d5450b4100000d00203070031400d00241d0710850144520010040d0f04580789007201c3d40e101111240100101c00c1960b00400d000002e240c1903024600300105a40d460102c0d8081e01d0181449084205920000078941804101310001d11101562540106242081900c401c40c1f140102c0d244800308000940005120b01800144001580c1e02800d44010106001801c0d00d82501164180241d020442d036000000c8081589440d05030340f680d900c4154417000050341c00e201e0b0300020545ea010355902c640f00c0c02840c24000307080404600d0311700c24494522a203245c80310164840c00624a00f044800032900c2c011803185042506104059408103000e0202009041070b03004020f0300150084244030541c0b815284903050300c3c0503419640315020503005035040a00e940c452304890b04c141e1100f00e04005003c0841a442180090380c04d001d14043c505155581d0306520b070103481d1280b00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 486507185 1250 486505935 486505967
    0xf210903090b030603030a12090b040f140c0102030429070804050102070902070809010302090402120f1e0f01050d030212032d040b01050112110d020901090611030702010c030e030f0d 80
    0x1c00c20441c4e543c4000040b00c5003c06203192918020321010380e424014045030030001c00c41d0f5603440074801444282c809640c45680201c0c00b450390004000c1241d0b40d950a500020f1b03015800c288420001d05445010f5020201d044c0000480f1001880d512500c40342e00104045072030810104080c0b00c070356410416100075040700b20085261a046459021142c0201915281011b0f0000b0b440700c0142c0f6140c040d00c040701e040c0758203d203945c145032070381100b07908007110701e00d9560511900041d02043c00344d10460043c560400564090b9080c4001d100103814841c0003581135208980d2440016800709000b188504410848000d200715142400401645a9078500012607844414400800c0d40400105c0c11240300f42440034400c900c44450300007030804403426440c03819000c00d400c0706040d940e070001d007501c0c1d800341d90341200c448d21000150303040a00240b03552480c5d0700074040d120040d40696910b80086001e07091150b114031658000034a01300c803405811804da040484050800303900a01408908408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 486508435 1250 486507185 486507187
    0x206250e040f0c03060e1003060506040f14090c01140405040903260708160516020307080f0303180a05070303030902031606120e01110a0e1f0c0b1005100f210903090b 73
    0x4100710303c81f5814031500010381a41c1e680d2020035103e50f01d0394086100b00c0c03014a01402464074080c41000c2400d4225002440c0e801001e940062942c4119400440b4200c040d1450b41030504007018032000300b80c03184044041c4050001d0f044442c014403090701d400c07584202c0d000c0600d458242d200604240740900011351001000380c020102c990404182c0718040100b2202d1528143c0d5400020318000340ca503c40c110b180074848a10b8445a8048000c40c420b101408480c0b00c0c84420006640c1c3d1251a440c000e032180d08481c1c801c1c00004e229410582c905400141100c0d040318a0031451100703000d0030f0b840355011580d5030860a0300703566240642e0b440080d072100208846914440200c00e90720400c0c1c5810704002021583c0740030360741c0382e030b01d4445003090840008400310780c0040f0142511803404000d8503100d0074840001c2c01c611501c041d070000e0b29030103000500c0ea0178a5110964103170707850484d1882030040d40700c2c22080641c80080c001a00403111040442c404409003805401d10060707030005070031401c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 486509685 1250 486508435 486508441
    0x10b280b04152606041802090c12060a030b07180308031501112a04110a0905030f0a020303181f1e09051c03090e010815070206250e040f0c03060e 64
    0xd828060b64800f80517900880e05142811001054030b03096103000350301140c3c03036048c0600b0340c400c03001070500602c860340c4410664803900e003000007050360307403100600c41107076000020300043c819103a800d440040603c04840c0a6200e81d200301c4940c100700c0d03a01904540310f0504501725039011201e10000741e4000040c01800010030400b03105010003400c1da18580720301442413105130319140d01c6910038003d102401902c40905250007400c006440c03044034880e01c6100e1b14120103d001203042104103034003c00561a0900d0080c0241442603840b03030301130b801100c0c006500c0100110016000c004400b650b50224052000d2801017046008460740d10100428884188219151801101001002c0004412010070580750844412102e43c01c00380e42c4004100001a05e0403001a851400c0c400712100c99480e40c1d22488104d0390780c40100c81688041c1160b1000400184c443d84a041511516103000703d041c60b00000480d00740c4480200070f002c041d03520f90745411140d501d4417440d0090440b03610580310741d003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 486510791 1106 486509685 486509747
    0xe07030209010501090f0612091e03091d0402060310050307030803060a0b0307050d1505040216020a0509071d0d12080a0509010b280b0415 61
    0x40c4a07980082019070044c0840800c1d543c0385880c01e0351440c0351a40c00c4484080310086031078801d640308160000704e2199401184401144200700c0304450b040e2800904801039540011a0703c1410302e45012403510308a01c984c0c1198041700c00c0f54490f00c6281111a85011035030115525100300c039000010005044060b622428089901c079003500d644a201610500c811902200001c5040088141c03440180e4088110010b00b6149850318079150804502280d0150a1940c3c0c003000150005045143c13034542c0720047c010540b140741032828002e030044d00140d0003104c04107220110710080314042e03e406081041140d0414452601140f007480042e0003a082614a04421410000083c04408050151003000100070f49503050100f01250301c00202c1c20500b108c1e0075003815000001600511042c0038201900d00310040000441e0005001382c80707442c0c0c00b0845000d02c40e9900c203041d032b01 = true := by decide +kernel

theorem cover : BRFrame.Cov 486330935 486510791 := by
  have h0 := BRFrame.cov_init 486330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 486330935 ≤ n) (h2 : n < 486510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
