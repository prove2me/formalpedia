-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:10.554379+00:00
-- url     : https://prove2.me/submissions/75febe9a-1ac5-429d-b876-06dd46420c0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 406294964 ≤ n < 406474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 406296214 1250 406294964 406294969
    0x1140339060c101805060112020406060c0c06080a0e010f0c0905060418051e0a0e060f041a090708030a0806190f0b161202010e0f030a090e04060f020304150b 69
    0x14852080700b0359008403108140701c8040ea406040610465020080300b00d40a49466040080a8000c0e40b00502c0205c0807006609081c02448024401480d240c1c1140e030a646901280d428140502c8040081d4800810940340160702300207030000d08100208851200f401800d0000d2032284000340109069080015240c035020064500f11180c4518509140418030250310007054018190002c4241654100354078150300075006200e010103420024240c0c84500c01c3c94540000203105024683d01c1c2410800010107030b800c0ca540704d810104042c0d01949034031320418107140c090342041007548400700b94401d8155021901e5030096100303030b404845030109240100302c0d491150095244041c1c0040c01000500d0034480101035012500700d03030082c081c07a1a0f45a00248110414190050f9100c2c20100b41800341440408805048080114a405048a4080c0040807103226030100400d409000900740105a0000c044400c1e50040131596440c0c1454011050818030f09804100d42c5422800c42c07150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 406297464 1250 406296214 406296217
    0x1b150f0207080d0f03150308030c12010b0315010e030114090a060509010e0705060f040f0f080606040b030c010c030c020402070605070f0e030712030507050a0302010b0f030303010e0114033906 84
    0x20816a6858a43c0c54a401e410b4000d0303c4144101401c1b50f41700c000000c0440c40c0b02002e91f00a040310b1041c6551038a40e08625962104180c10445645504100340300300c01c02070303020b06603900c502824166000c1e411480020300400c0300c22081825003580c881008104200441d0741114948290800c002a03200c1ea180c55080f5015240c3c81080c0c0d500c145020301081c5440c41c00b800c134000043c20000c1c9056102c4518903e40a030550080040e9034041c2d60600040d02e040c4241a408601514108200c9048600003555001c4040c4400d040c07280e10000201032601c503080701803100f50050230940d030311091807038007d0041c042200c0b0080000d0419848865261007110307202d440c1c01004004180031801c0802c110005e40043c0c108505100b0f04204e00c8000620070f000b80901c640c025000083e00d0001082407052102d40d00c80123a2090300f003080140700110000f8103181c11354a1000309840503486030750110386052520706000d001e803045074071041c2c024803004075400101150401006040c600390020700455 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 406298714 1250 406297464 406297483
    0x60f071b020d030302070c090e03041401230306300601050a08030f0d02071a09070b07080d020306040212090d020d03020f030711100c0c06061d041b150f020708 70
    0xa1003000c40401180c0b280c0c010f0080d25024081c003d441f681e8440404040b100500442400d9400110f0104101489a070b02d00900b00340a01f032011001d400c20012800840c2160034034154003002101250f000d4030f542608178400085082448a40c1240d0b13541355200e1003035080b6003401072090b54004501810410320407012602c40340000c50030300002e00b84441d040c2e080308190040c107503402e000407400314840002240e00c85200400465203420000041c03424507009803c0b41002002c10821540001d642c00e00320b8108000f10400140c032a1561400140603200700060341d60342044200610901203c0030480c0c4050144c0c0e034086402448400009900342e015841c007898051000740002481c040c0590001104101080c007038070f071481e40d48131590f81110344080c0c0400c005000940940200a40340c1320b00c4002d4000f8200592800020500c501a040c600400003071907494801c20714041d45407040d081e10301130b001c0c41046661414245400820709000c000c804401840748040010f4410b4020600c0c0a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 406299964 1250 406298714 406298719
    0x20417070b07120c0c0e07110309010509010507050307020d080a02010e01090c05010c03020c12030901022a010c06021204030e011d010813140708061e01081518060f071b02 75
    0x30b20400c1d03102c40801d080e09140a10a10642c1d510760f000040c2c0d0950075902814410761301d02d10170708201900030301000c00d2480340415a80100007a00040ea000801c0c4d134440c1ca0f0034600140d494059281180c11070291140094210799204500c2d0304000401018080b030b94640d81c020054101d001c00d609080c0d9000074005000601d00b0641808154425100d40c1e0031140a4011503400d2500200801c07501018440c0051803904041041181503030b0610140016140c008a81c41d8505011307400014001043e2070a54103000420a5040400845070140d88250310300e81d20600c00303841c0c6400c001e40030403120300440740000e80b850580340e9444030b0481c0b0107124003010b9554030620f82e03400042c03c800f0006240c00391504140b43c481c0001540007040120041c0003c80098540c0c1d003802c51101f80d6440c004010035090201e441e00508c400c1078000385031218002165000c8036941c42e420907080750741422851a05c00360080904200c44042c04002d183d02078903d680d5409040e401090240b01d6000542e44001c0d0f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 406301214 1250 406299964 406299967
    0x15040201090905040f0f0c1406120f1308040806011503180204020a0e0915010e09010303020d050f0c0d03051008030705030405100201020903160303030c14030a1505060d020417070b 79
    0x452602107501040c1d2141c4541141c00c010710042d119683c1950042408447c00005d032002444140380c0a001e06600d20030940340070b418265001c0d001c13003c0a000900741c503618103150000800003e02d40d0f01d0098187d801c04905542c0d240c84442c00f64032203c007401050440302d00d6040c806e01d003502c684648540a42c00e009900c0702031802d54204000b95012031407900030490903407070420f007542c0d6040e00c044c003908180e00460686400b0700c0c00905034010445165205110b0320b001080445d8003c034055412603481d181844e80c035003007041c030300496000300302440c901441060b83c10f001e0990590700c11340c0100036050f0400b840c0380d0389920f2644c5d00d12a650b0020000d030800d01041120707003018220021008004d00026040c82c81040c0400e142880447c02e56064402402c000c0041c1901880783e002c400b8002c0c034149000c003c8200d010000d40c0703c0501a18001603480003807142d0190019004000b8050080140d2b650b40c035805107070380180d0800e014030b10f42c80c100020110040710740050140c045400848549 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 406302464 1250 406301214 406301219
    0x140103120c0804090e071503020a02070e131202010b04060504020a020307020105030a090b070c031107030b060f04110a020330010e0a0b0301060b27031e0106051c051504020109 77
    0x101c0d540c1c40118011904440300340301c01319211040b4001c0e140324800c1c10004094107032034186400e4503c12600d500c041414030400408180980c007207030340e6050300d0f2428507168031900c1c7d03160780301400641d444001d40f11072000400b012031943d040d041301ca075002e4100c0c0e0a01c68151100e0420003203110381d40115025a000f0400c0c040154041da0156602c9515101c00040b508100c0e12408907010301202c2e038a00050a4960700000c01d41c120b900188003e00d0301001305245403c40e03440800d1410040d01031445120300c400d00d003160fa0b4894202e501040d00c2819000e4841c06000320196407034212001c108074080d4032104a0071445020811040060b07403070341d00d00c080707a46001214194504082e2a0710f40c402d44821840308030361005d010f040001c0c0725190500b0342d80c405049071400c1c403071403000601144c40354500702004c0c10b9400103510700408000c1c5440340451007200500740d004182030b60100381c000f111100008403a010080d84c9840c214003071400e0701e00d08541072860301e1030307a44200c500034045040391605 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 406303714 1250 406302464 406302467
    0x50c0f09011403010605030106030302011e1401030605093d051608060312030403050403030e0d240216050c0a060813060c1b06150b040b0f07051204090f14010312 71
    0x100c142e0b801015000180054464000c642500c1c0c06400503800b50b912202110f80c07982d03800000d200c1d4109088000c00c5005100843c000c03001c501844003400381c50f00c03140454443c00d03041c0070908040c0c107641c41c00c251142000c61980c40c0d80c0700c9a0043d59550100204c102c000c1a0240a4544644656411390340301510748032040d43ca1200c09800c0703a0309486112500751102d0048401180902c0c00b988403d40c40351b2441c58010810615103001600940300340038083c000034a00744041c110305250004e004050405040340301c2c000d000c0e900341580358100030b00b004414048082400c00d5010000d85e8482c00c20782c0c0300c02d0150f0310440160740c40c01c01444102c00d002e000c0382c03896120a0001e001498105110441300ea4417000c1000d03402c1e01030303415540d81d09070140c1c501a0f90000400501011040070b04003441e2140c80d122a00802d450031403500700001c0d0741c1c020410140001c11300300b503100119945842e00c03048035900401408103815480e92900a42100941e01041168120382c0d000380f45212400f0001c60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 406304964 1250 406303714 406303739
    0x81012140f01111b070506040303030209040605061602281814040506070c03140f090102010609061824120605130b0115030e0f030c01060b1810050d021204050c0f0901 73
    0x138030905004480c40404d1543d50700004100660180d41c3c0540c03904142c4003003104a45065014500c00c0004100c8100e1a0217403405520003142c048401c00c030710300f001d44109840101f03c181105098086418041581d2100d00417502c2c42d140d044004010100c02515441127143e0180c42c00b4016500c0100010700c25131160100b00300c010310074544845031503145e600d0381ca2a50080c0142c04044c0402140d540f180d03590910601e00141301d082d005109a5141500003041c105802d88000c24464a921030042503200442280c0021011614040b040b01c0d80d43c480040b0001c1c203c0ea0480381035092030003060b14901e00190031039510750003c0841134242d00c2c0010415035071303400781d000703034281511140c126920b01c005110801c9105201c00145079108031302e0070388508440082e005451404004d00403000b840e200f01174428260142a18149603107503a80c9000e80f4540282100200700a0001900300010f00100c4211402540314000300d40201c41210b0405c4250019100f10580010000004028040302e814 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 406306214 1250 406304964 406305007
    0x5060f070206030718090e19110f0a080601080a15020408060703090f060501080607030c140405010e010c0b040c031101030e1209010905031203010311091501081012140f0111 76
    0x300000c440c2c100e070801521310701d115800302d040255911801f040b01001801100d0078052040e248007184210b81e580c1c00481e00d05019400e000300c2000000c3e5046850702040600a0100c0d81e0480d4040d6039a401c031036907a00040320080758031000c1d0142c12004d2222500a803429140644041c040343d03690250704400070007028a0649200d550145c0c0346000c10803038825107010f003d07250017030316580c40e1261010741038480030158002080000315a90440e625014240c030280e070424a004190b110203000120750321400b401c000303084a02c00e80d09000812981041c014100c82c41440c0d0b10401c00a81c40044d41201c1140a0040040d007201d51420104403402e401407c0346841410442c0106072070b800400d260140c0b10b07400c07e1202030000010b2092160710100900058011501213440b1319203a144aa41c404e95440b125041c0030707e0002090369140c813420301001900c205071a82100483e10300f00030020101122000b400f1340501242183d21103411301400301c40032410b4198078502990001194141e09085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 406307464 1250 406306214 406306217
    0xc050720010509040203090715020a0f080c01091b03020f09060105070b0603031c090209090f0d080a02090d0f1203050c070f05011d03030a0515100320040803040f05060f0702060307 79
    0xf04250b2100c0c0d5a10b1019600910300000144031480c206810a0841c801d031000a205550044801c007000a40999054201c0c03980b007036000e80c4400c009a030050250034580300040c013995500300c0051482c2c036290f01c1d4000710790003110351128411048051040c00402640c00c00d000400c00c00201021804da0b150481d00b244003e421079180c55900340c0343c0c8014000d01610490203070780715810001503182046680f81c03c45442c0010b030154800d6415180d030b999201d01030110600420000045004030702d64166651070a000d40008001c107614a840c40c929a0400e504403052017100140c03000d828440e02c9890305c45c00c25101000d241c40341a8a90b920b1750000034030202c81564032414031991862502a950303c862400600464407410942d1300102680d5000f00004270002441083c1c0701d440d40c0303101e0702403030000d454180002e84c09424092606000c1c80d201c2e05245040f0000b90005c4e40c003078008014402c40d44070806150b40991642e041000601c00e121090314078007801c0c02803c002d483c0450007183c014515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 406308714 1250 406307464 406307467
    0x10510090902040f090f021213050f06010b0919060e24070c170303310b0f0108010c0509030d180f03050106090501080a05071a0d110307030c0507200105 67
    0x41d5510001682d12941011079544044107040142c00490b009400f07691107008020350400d540403030b000c0c1040c0c80040c10480810500001482405028481c1d0001000382c28240c174000e68581020315556840804114050440c01582c0b04bc600510301205040d2040b990300c1a80b0710600d04100055450583d400c1c03605001e01905400d42c108000d801485464030564003400300c2450210681c140c50040445c8059582040041009000b140b408215100301e0f6036a1540050105a071660403107a0b9546005041c01828402d002d250b6005180140c1220000740084c004400170134400c40b210301a1284060f0503034020400d00c540c140c002e40b0800c0a98020540104100c1d68824a0024500140d8015034059558010a0002ca0042d0181a005d0101c0c140107001001155540c00d42d510054420341e0504685086010f01882c4140c048548003078041e4014082c562005582520982c410303500d101c003086c94085180c0741c00d401074040c0d0300c0345908400c680807104204084100100c000c1c00e401e5040010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 406309964 1250 406308714 406308719
    0x6060304030c030f2006180d1209140f060f0601020d080103080c1f09050129040e24100f08060a020306131a030d18050609030a0204020a08160504060801051009 70
    0x60b411401c040c004420005040714203000c50703507041031034800c00c1c09403e84d04811000d50148c2d80260241c0560445240002081d000c54113200f102c0542e02802080107004881c0405181d2100192030750144510444030701c0c9980340d40b0300580c4d8610129102202041d2200c004002241124002c0c02d50142c00c00196545540c0848190003c94484c6200c2c00845544500c6035040c41003d1003140c481c24200003444a4070203502d0044c041e80051072100d148999202d0b40c101d1660402401071102001c4a000300c0324450719555200076190354111400307000c200d9440700000d9006014400881125003c0d401b410080d154aa080c501a42c001412a50440c00004c010b03105170401d0700c035181501d0501c040c14038160810a00309414656529540c0f02003001450140c1c1c1a100c01410b08821a04226600e5685114544c04241840050310010390301510109903e1142c07a040701070503214245400d682c07a01c0c40c140e4282681c00340a180100070001d8405c50041c0014104040f02d0007500c103c1d81800d100103136 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 406311214 1250 406309964 406309997
    0x4060801060b0705010501091e0c021c0504050f0409080304030c1403040308120f010f09150b0c060105130507020c0d030507020415090b0406140907051603021506060304030c030f 78
    0x4101d6401400075000008040c2c3c14060288a99400340002e448248010301e80c0031200c50310049022a00c1c46019030321072044c03141134002c01c806c101c203414a64603c056001441e50217000b40d00188150f600030509903402240520f46403007401c844030703070001c8020b096884588049603542408002107440f02a00004c01010007002c0018000540c4036186641e6140a10300345000b80e100043c02102d40640300e20010b1040b07000c07501d861001d9600c10580001e15541e0040711003601815a800212291000201c074410000007056190507500300f940c05555009040c81582c6c100d80c0110b8148006030002d80c5c1e000418581519898181c50003490704a0030318110b9000902181d0400d07050000700307503010300c081181e07004034002c3d0203882c6800c541c100419442e0101458003040120451440307000c3c0180026800ea0058059410104100e4408017814445240103560b0354042e0340703900c840141c504005000f0b03141210442e8416035056490740105000c641d01903c45600680c0782c0024804401d181c3c2140c0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 406312464 1250 406311214 406311221
    0x3070f050105190b0109092004090c03050f040c0e04031403130615081f09150903020118020f0d03020118110906010921050109020a08010b09010b0313060b04060801 72
    0x15004400004860800c61840302c0c801503000400080e040c01c4c030001c0034a580e045030303c10b01103941c004400714002880b180403004180390710041660220000ca0007081c000e800c0c1c0d002070b4461540e074600300b086407120281c00040f00030403500100f01e001c40440501070100c05013411a0401e20905004080c002d41c106000d2141c0c0040321001400000e0450b0302040c0100b90046401c451041c8221140c0c10b0f00b01841030780c07543d803044480c44510b0780b02e04040441e840c0c4d60b80034420084e000388d200400c2148070407030710018114200043c2c0056003000c07107030a5000c0c1000400045a80c4c000c00c50350a8040080500003180d103082015015950f803440107107454400b1010300120306104800c2c5241412504041020761940540301ca81004140f103030900040c1e22031880c02080801c40f01d800c00161a10f4500702d03000d006040c2c402500110500d03800907480405405c00410340404130b442d013200b0380e03c44c0d40e41c01803030100b01c450f99550240c0a0468001c0744056009091680300900003041441d1103a00850070b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 406313714 1250 406312464 406312493
    0x9030111041805070504140105032509180b010e010f030618090b160f0804050a06110301090b03150a020d020d020f030912190e060c121305190b0702030307 68
    0x100d180c02100342c41d01e0315092191a0b8010001d0902e00c0c102820300a81840c02d10020b07490306e043c0900080450011138185e2403c000708a0b2460000404003500800100400600d21507444103101b0305803c0c91145004c0e01400c049032506955409102416000440e1042c0d03030030100e8018542d5441001c9902d110f4031801f0090a581040c0119007030409140c54190400700600001d0410700e02101c0c0c0102070ba104003c0d040c414200d280016858441d0b0810500b44803074006c000301110b1038410350446d54940e031000355040318a5882c041010348400c405140d12a1187c004104100c900c00000070300e9100c00f0b502401f40642c2c560b4005042018410700c10341203a0182ca5084d01042c0003004215400d481045806240c104014605003840c0315203101c4181807183c05440018040c25102940702c0740c4400090f1107100318010304941041c42c80c00c0c89240705a00554074148000c010a10108090604000a414420081c040300c40d41030b20b4410100c05540003040101e90600040116001007100c00c8440342e01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 406314964 1250 406313714 406313729
    0x150901030507050f0a050d060207050f0607032304120311071a0901060522050a0209040f060303020d02071a03182509090336120213021e0903011104 65
    0x48007401c020400c1210254013100902c07900003030806002d40e440c0d819101d60103662106015845001d00d10f0200c0c189100d04c81800440d00c0f41c18100126941c0c10740203000c1c501c184907030ba0740c143d20304581c04500721b280498001c0c01e90403122840d01080c0340f003503000841500c0700300342050520030f243d60781b18000d17480d0f0030958401002c0f20061060041b0280300b08002040304075401c203d940c003907000020720f1882c015241c004a941e40e600143c10006250100e440500000304200001404144120000c20303107800141c0051240c05c4040e40c80600000b000c0003600c10485030b180e181d080f40804006903502c004c100e822020040080840140340c100041800a581650064040c000402c00c60511aa02e9409882c510382040840070100c0e0704040301441e1030400c128141d035017035018030a80704920340a00c25030000800700e200000d82c0d49140001540340c64400c581c0b4482080b0640306420a070300031080d0300c8076000e02e0007103001b00d0818144000d100301c910190000c01d0b11001c8490049a0340c025030300048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 406316214 1250 406314964 406314973
    0x1202101103040b1c0e0a060b0105070609050f0709110403020f031207080a08090d050a05030414070b09090a090c05190b0d05070e030d020c04090503040f060c1a0705070b1509010305 79
    0x909400120003091355480300a20070000241d1003a41d2964400c03a0050181500d41c3e10700089025902c180e0841300010b4200c42c1c28071001140e454540c1c1d80f0402018450f25a0040d5600811001c45a0140000452050b20700c00e040600316003c010a880d50745142d50303070600c035044451190303e101501402e0224050319020341c40e000000000fa00204008181070b00c140c0000d508a50810f4000c010b480707074404180b41454032a03869140980159010342c0488000c3d1082c0c1c440000d0b06115040148a007543c160390143e12911003120620690304031242c0208100d158050a1000303040543c0f5000c1c3c0c500903c0004c01d120f81e52001d10480503403000381c2d44843c803615402000705581d0441d050a0030f14106a0041c0851250042d001b0344444209038807503c50380e1902c2c000c8042c08010402c0d100a0700c0d20201c04158030b030b51810098024502003400b1900d0030244039400383c0800620305140e00c100b1654403194034103240707566800511040101820036114101640c42c2050315011290350103544900001d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 406317464 1250 406316214 406316227
    0xb042a0f05040609091e0f0605040c1d220608070501110303042a05060c03030106080105100c020105070201050706090c0315020406091e030f030305150a1202101103040b 74
    0x51000200300349680c2480801c100400007554403404490032115000b100040700c5002c40b0010b81e9007858104800800c0e81403008980b40345030680e1102084940448003044902e0640d20141e4030700241303e0702004c4406080b4180c140900b0b20113001d81c6010200380341d052004500c2c000c0c5000b203409980150010360301840040c095941c00c059424829a030b144c0c020b508510345070f80c8100c2c51020b2441081311180c0a100240700302e1a4424500c0b02a2900800c0c160b10b81e00b49007000c3d40e072900244122070004400740d0001900d4240002d5080c04101a40d6078011040103d80056405030302060089041083c00c00120300464180e21884080c1c03441b400130401c2103480c50600868038404410039207200b500c100030070000d190308807902c54104da0960503502a06446584020100340341544081c1c40742d20f103c0b0140c4101903150b8025481340e1210480381d842484140140080c100150103503222004400541d20050303e050400e40a2044881c81c0070020342424040c1c1e6429600145d1000401c1ea4020504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 406318714 1250 406317464 406317467
    0x73e1504151119110705121b0a05030604061104090f02030a050f012607030b1003120306050d0209090109120309030e1005040303112d010e06040804090b042a 69
    0x9800002c50300002041c01e00052101c800d000c00200a603101c288084c1c241c0810a60109000800007440700401e0b41066442d41042192208101443d010340140d100b10030348031030301d0803003161000da8074040e0040034241e56640c2ca0f400101081050b507250317048144400501082d00d0301801e803540b6949100941c50341040360900d0152907001d4240d4403810441c0d0700601c0041c0000c840c405041211440b0300303512041c918221424100d030fa41020f061403001c0b1040002200813280c2d20011203118403040501d0340e41401c0b046003100e615000d681c2e80103111060318400340c540440c606800c1280480006580c3c1e40955841451101d8115004003007621056460103041c0c00142d5000114001d0700c52005030482260010554441d902005041c05580703142d82800e69400c10124542c0400880b01c07480210700303104516440c1da10042d071501c40e5820b03c841d48a4004004c24040c1c0920340c04501c840c00c2508099251024040e141c000c260440d43d240d404240d03080104544800703040a0134030804c2000c416500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 406319964 1250 406318714 406318721
    0x13060c0918090503030a020a030e07030b0f0a0e0615040b1e041103010b0a05030c0408060103050715030b03061519090209040b060412020d030e09090105073e150415 72
    0x19000e05a03841e0282c4600424004402c0f280c1c031640c4001c0051b90340c1c3c441d0303105500070403074500f8007046849034400c00700421000641940c000ca50b050450b12a56031541550740903504100080c1205030060008907038100704040f101d0f00d0805c801800899a10a05408034204840740480324490b504030125040c0ca504191081000c44440510510f107190306048403403044c1d1059011b007804000c0c000001039019807400c01640d000d0840c00046d20401c0d6543e007000703030356443c450050000d01400202c80f901400d0082c400c880c14040040e0280c101903440d44c90011008421507000750f0007110401c000d4a14400c070102d50310140421900058885003848c0502c002c0f40d60030141da502440d0100010b101040110b0000a045941150029071040803854112404100405002e420100140034031000f210190000c62050025583e030711000f800020030440390901c260050b480703e14111a910044490710914440740f03542ca80102e40a03003a6040d000d403198a412101624405c56240d0008440c054501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 406321214 1250 406319964 406319999
    0x111030a0806040c050f03061903050703030504080c0a030f0b04080d020a08010906061b06020c0309040c0f020c090c0a2703030f14040e06120c04230903070302060403050313060c09 79
    0x944a811b20f258018460000e210107002903110704e000040203a018540d441140300a9640601030b902c00316030307d01c0c0140c0641c002d40580040c50003442ca03000030500f4040d0440040f66042120b452110b80c594849004003c4042c1086c1c0e501d003410020841e200107180010301c1d111080c4d6488032020762504100008a44060700300390308000300c0720545a592894070343e0541216421500040ea681e861001d02889c40c46414042d580003030030326940c84a919000701880040d900b554098841e00c008000800c0031f0000122003500081d01e090040124041c031402c401c141c0c81c44c4001d1042110598a40600440100e82d40220000740030b011000b0751040d80702185401c0d250002d12883c0c142410402156502c880c001c220074040d148280141000200801c4084e0b00640c019104100c100418502d9920640c1480c0e88200c0036402080850005400003084600098041d80a80440d49a90340d04442c0c942c07000c0c15044000160122900c0800e26030b2003a803041da8140c1c2c460582c59032500f00600050742a52 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 406322464 1250 406321214 406321217
    0xc0b10140a0806070f02010213030b15310f060b090a0603020a210b210d02070509060108100b28020c1f09090e07090b060a090e04020111030a0806040c 66
    0x100c0108884540061180d8003c04c02e4100b09008400b4898100d0080c028480d00000e00305075890008140240310107200d00500d031021060303418009440610142050410104045500c0f80d4400d142c4d40e03461428003500e007140310801240611403140000e007900c1c1103811010010b103001821420902c1d041c1030b0800140322500f000d505001c0050006400c01c0341d00d10703060300c41d940c4080000311750311455403004000d03000092111011034003c0f2806030f259070452020400501ca030320307110511280002076400c102d480050a0b5281c03550303003500454000c41c000d04218010300b6007140210b0303001c0604010700900306000c035814248201c100602c031200718550300e200d02990400c0a00c0380b21502c80c14030603900504050b4100c03070031581c05c28088078a05100d900c9044142d150040c40203040c6004614501140c01c122400d200e0100e03100104029482800440340204007003c10420051480d5405a0703440784c01414440ca00c944078000150456100342c4d1140f0028078207104202e07031803400e4414151181400e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 406323714 1250 406322464 406322479
    0x305011d1b300109121403041713090c02060a05010602100e03040b041202030c1801030f032d110601050d080c0c0d030c060b0103050411100c0b1014 65
    0x9801071658424018249500441c00303030003880b008912040e5040b00081070545107807081d0401146860080c1a528030855140e01000306030f4820501c91545c1c0494102c8000c2d52906d5922940d880504140c42d12031211741030001400740e114202d0798a0100002007070305410200f091540808024180a002040d01410310b143c0300c0103020b0907034000303004280541803c1c0700140c02151000030610318007c90348500c00c00c10000901003444514035a02c0100f00e84258122102c84e03603400704200d6103d420110340c1410051410041021585100f01c5695650207400d20a40c00006c42201080c004a02c0803204030748881d401092405c0c0b9880f000401c880c91001004e00525414080060b90000b01940058100c0c00b005c02c4040c0c104009018121400c14020a094001102860042d0000388000350684e1218941000d5603001d5000f40182841554132987c28800c10700c01404211003507065201180c104072105506e00c0000c5d104660b120301485c0074401040f0201d14220b1003942851030722801c0f600074200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 406324964 1250 406323714 406323733
    0x3110102040b031906081e01112d09150304110f0310020703020c090103060c110706021903030f060f050310020f04030f02060d02040b12070c12030c05090a0305011d 72
    0x1865002e070f981090409000f0500c5808007404078000d480540c2104907107010707804410300202882c03050303005221040c5001707100711544503000312810302491240000070f0440d000488000704d82040844005403070080f0380b42c203000105010480c001c500705c4880f045500e0000071300c000e02001c550b680e46604011a032070340040c02080c0c003003a224101035805000240c0c0110762001098003d00880303207402405070035817400790b13503c1c1080006003a80c4128180421a201804410714401003040b01c00c0d1074558004007500310110615038055518101c4c15010156900e00f04900c022803401418001c200c00040340303d840e8280010141490300c0e1684e10540c181c8100101d10304c20160300b00340d804690b088501c07450300f02400e0000c155648110594103400910000d000320741d011400011304600c100401c120360283d40ca00c00e05441021841402030701842100e40c400b03002911039041511441e0851410754101403900300450002001c40d0400c41e0182d4441000c000000380c1b11040702c034061041e000030442c401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 406326214 1250 406324964 406324979
    0x121e200d021b06040b030a05180d050a050f040b1321020d06051b03130303060b040302032d07090501090b0a0f03030804020409021c030f03150603020c07031e0311010204 74
    0x2802448000d404203048401070480ea40f08000d5030001d040b00124a0740c0ca1400349441d400600046803000c0d49546150503448000d00c000880707035540e80060301c0d0f00d07290402081058074280c03c03204100000346001c000c0441c07032040c8134002d000c099a2040c50904c0707007414048141b20300c030151001020b480ca100c00001d805a40c400402520540c1c2065000405495480c2030362401004800f20741c80c0c02000100f4448042010084254818000c0d80c041082c07644400940a4a22844c880694103522106107040c4444c01100114004d0b14002101103a0f140d103030b000d01d42090030543c00041500d40d2a4010170100e000ca0140e0220100104e442c03043c3d480c00d18240c00c0624402e400042c1c01c024881d4002401c6440d50760108000c280c00a2009400c0a0302031306c00c20f00700348000012000200100c070300111513030280c06159101d03c1c3d18840c3c0e818603410b05000301c0007500704201d0300e01c80e40300d10b11000000c50115005a15a00260847c2d000b4810083c103001e0400389280e004030500786e104100400002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 406327464 1250 406326214 406326223
    0xd090b03060f0d081306080c1611031516050405150306030c130c0305090a0503120a0908030f012c22140102120112021008280c020f0f0a121e200d02 65
    0xc2108a0010b0a40b0504102b0400300ca180c203000c0c1c061050316050249403090214252144104410462050802403000c031200e0245219040e040725503a40205c1c60903500201655100c84090101c070282403443e400140b103a45040b42e0300c442590365051007045103506004051380308050350000c28041039150f5419070760713204009008804100c0c501c049085d1000c10380181081070f0300100302c50b03201c1c2450b5040401c1084284141d0039885900c010f008401c05070031a05032050886400010200e54807148005981700840344907001509110541e00006800c1e0002070030802408400140c8450f03496500d80ba1010b810b802000240a180c01c80400696412801080c882000d25080415031070301090490045c4000e0711081d4169282c1c0d4031003c6d4900300340e116050104030b42c0d0880f00d048441c1014162035201c1c048910002d40c00108203003000c155607a100c1c900102007482c10100c10a8801940c21349400e99800c607a000a00100011984018601e0203910388003000380541504070329441c1c042c1d0748 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 406328714 1250 406327464 406327477
    0x50a0f0e091603061a0108240d0209040c080c151e04050301021903060909080711120601080601031a0f06010c0201020f010207060b120d090b03060f0d081306080c 71
    0x24000c0820008800240074000d400364820303200540a501912440c04a0140c1116400003c82c2d2289104c802c401d0361050010500231100e8080c2c22000700c90a40040a00f0000c0340c0b8800d4010074048001001612042d0ba610b128a010300360b40c016a6081480403420181204075051107400078a24000c4040300d010202c4080c814810704c0d500b0210070302a00c0c21454001d13503200315419440400c0d80011048518a0940030030000e80c2e0401510391a085d400c000c54078282c0d40070307180010900000b4005011004150b041c02c0000385240100000c1c0c1442604d040026004203030300d03802400c0100700700149030240c0b0b12707520340f03800000d10702d0b00d00411078800b400d000400c5117040101500e2040c003503900038042c0c40c0815924100035503030380c00981041c5010303090f111000d43c010011086010102c040c00f049203282e458540c3c1d0303101d82d52442c1c007103100000d8001a2030507610500c00b004006c003580d6481c1e0151314041c403c0455a0319820340d0341032000e0f90101940002d0600c101c02040104511008085900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 406329964 1250 406328714 406328729
    0x201e09221401032d0b070c03030c0801060207090f020405060c030a1112091c02090705090f150f031005040f0f0b01030903020c10051b1c0c030801171908090a050a0f 72
    0x12401481c40709442c1c0d00d844d102038111340b0804207014034598001c2c4107819080c001e40f002d00008401240840700e065091250f000182c000340e9050202001d590040f0a5215400102600b095281c0001948a5104c0c0e0601800d584c00003d4490915130061680c20b03034003508170042d104924084426484500c40c21140c107104441341e00034035115822840b100c203070355600501106005d1800380009007a0b58800d0600520a0130260b6050ce16403801400d17410208451215181c10000c840c00d19086030b40000d0710403482d41840300008541d07600c1e548101c0c3c0c010607680b00042000d0140351500e40440d140e55425604050401c034044000c65000260064080420303500903c0d1103104000456283c006d0034400701c802c007842c0802186c0d0540014905001e03100c02d00012110255043e41540e5007510404020003207950500100718001c4004006451402c40e401a5100e140d003044c0a074527a07604200049403005000700300c82c8034070705000c190000a018140c0310fa8107060708145d0000a07054140c4034010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 406331214 1250 406329964 406330013
    0x2060309010e0d0905030c0a0b12060d060f0b1003020903070314150108010912090f0e25031d01061410021509060901201e0922140103 59
    0x500d605802d6000401c14900d400a403000d03c0116a0000e04602c1e05109041c0f1920800310300b00c03c0383c5040c044030b4040300c1501f030300c907441d00070b620b0070031807202400402c7e403a03001010690002c085050b60280703102445200700005200401c00f000c01000741c99904081c42014418425819030345c80c0081c084094a03046100b030300c480043c400c109031502291030300500c0290311480000517883c00540040003010b10800d20f02c0c9d6110704a200441c3c05180504c201d103102254024204905104003d010340c101007056000e40840c6000201c01d00c00004100c000000281c0d5009034842944003c0c04062412003500020f02481d45001c0d4080041110022014420f9a8202c500000240200b01208844107030701030104491520810164441030200d840c80c03029401c01c00f81202e11600030440701c450b06040750001e03040421000f202001c2202c1082c4d00c80c41c0750000c0201510342e40c0c0b160700340000028180c0180c0003101c591000300d01a2000e100252407590012001800024640d1110000c104507058001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 406332464 1250 406331214 406331221
    0x150e041a0c0417010b13110d0c050405060703120b0f130b06280f05090913050f1204090b030102040303050a08090c0d150e0601050a0b07050114150114030606030103020603 75
    0x103000520490f8411107000c0036800c0418103080301904000310042e002c0792801c40c0751070809800402e0f264544a000d898980801c012601030803d90721000051150340b4101d814145c44070003040c665440500240c01145c0026035400480740d45010342e103100802600d1020410800c00d000c1101c0411100b01ca4408a8031100348640580300d00b429640810140e003618190140141c41c01829200e40d030f1001000070301200c13858000035010300100e03101180081e045014941d908071900304584910001210680070704146850305100400c4203a13804400c2c012030701c3d6183e01d04144601210103441015000b41d0040c1f00410201e43c000f01900c3e10401c5604200aa9a548445550a14035800a100da0023025103078090103008071010112001901c0140030040402d0b8503070400e985140174420701d03a12061081d41802030208a5000d001e03a85c2c416000800e0700301e031003022500d05800031108050b8031201401144060f683c4040b2485050b0452407801d883c50408101169891005020203405030380b001020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 406333714 1250 406332464 406332481
    0x180603020c24091603230c0301330f090b0a09020705010606091215110d050f0f0f0702030304110a0b131401020106050306040f11060d150e041a 63
    0x44090b030300c080c0c00000c04034041840c030303262181c25112000e0500c12010007007074020340200720130141c903007041d00000b040c46000c80000d404820300c1d00d480164002c8a81c0c40c861520240a4200c5c2d0541c44010525480c9428100c1c4000d1600700205100c0b0301004141040030210301e0b54030b0030650381c0701580410380e8403089000c03424030607142e4002e83c259440002c2075806e01c20194410810340b209981c40b610010b50b2480c01004140b400c180290460712207a05011180c56554003070510401064400c608180b07000e00c4110442d68103e840c4a03400107041300300881000c0080030729038130803c2c1030044203ca09007100020740d203000c0100000c100c8004d107d80c030903a640d50049041c0c0100624980c00c0d564120b9240802180c80d506c0c03150a01d00c00b03800881e01000d45c01070140600392503003e4001c00c0d03190307199220854044000102590149a01b2030305601c140c490300014800e411601d00007040c0041107800c1054501c246074480000c038034415080c00002070307056041f40001d030000c0032442c8654644020303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 406334964 1250 406333714 406333723
    0x15020309030d09050406050609060a0305040c08120d0506010201021201060806010504030b0a0906151413060e010305161a040302090703110c1e010b180702010603020616020907180603020c 82
    0xa015070500c00c2c8111128502d6000e00e04800b0348206540910505683e035040c04118050800c5160b40100b0070301c02d0154040c8070b1742c007095103d8061041c4140301a980c1d0342190903c401e104032a402540002101c1c1940e09143c001c8682001080c40218500a428030b0344081c2030340306000754820003071054041940d60b841072095402031600b003c00b0714400d04102c00303520014070800108561141c03c01d10660540324840c0c0030441120500700d400303801d4440e404208660182c00200c800041a503404001c2040210301483c0390280d031145c0f0050030000c91141c0c507400920710030780c032000780060120000c4da00741c440b42040c0d804903581074541c54401c1d00c5544050f0060000103c5031000075601203905000c10100243d02090740c550316000c0e81004400b038039603900b0b030761030891920b4001e004030103011203c940c04200c170b95011900c1e10000801d191268009040382c0d100700b6100031064035014a24065107050718500307811038101c0c03d00d4035a118070610404039080c554400e0b8010715078041303000d83e9540780170301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 406336214 1250 406334964 406334977
    0x20309060a0801080f010c050405040903050403140102090a080601030f0201051602030f070f0807260304080a030309120503060108070323010f060e030609070b070206090409060902100c0b01150203 86
    0x51100740c0740d41c25520001c081c840240f068030018441c0291050012a040c45211050002c60703071400c0c50300c0c0c203080601020381814102101000010800040441d10407403000d00c0c0100a4400941c0e150008400c02c02c044505030050341d41b40d000344d00108009202301c180300003925030a0a01e9601d4080341100d1340d1507003403c0c0e500650075020303651505030082c10100e03c0209445030040e41204440c0c451500700d41c1c80d00f450184102e181c010790b0400b0a100403055035400300c90000d600302ca19103500c1d05855400d10800001c21808651140030840c00c001140814580f05841031a000d0309620342500000d00c070300b00203030850042c1039855140728211141c00d01ea09a03c031903200500442e40d40c1d18400c40466102510403040003400000111005190104103070303000d0031600c4000c000d1181004407140c1d4a81c80101c003264480803c001e02c18254071540100d00c01c55004803030018040d1454018852402d600d8400c1c00200300742001804001800401c025054808492800961031629030040c0d244d842040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 406337464 1250 406336214 406336219
    0x3040612020403121e1d0603101a0904181e020a120302030912010b0a0b1315050a0e101403150d0803150a05011e090b0c010c0933020309 60
    0x1944d40741241c44e0000045d00b40b80383d100c0c2c008000c003030401c00c5c110384060040100c1c061803402d000c0440018078104c0d003c4e45d00b0000007040880d601b992075003c1031030a910380e4198840042d02040c49929454944640c1d0440c50442c004061034002955030444100310f0200c400030718480d14420002036440b0b10020002821524200d16503003041418041c5d601e0300f222428620070911496030300c070464018000c00c116020003070540c1c0000d5041045003203880c3c00503103402c50140c0010a0006800a28860300c0c180101c09850341c542c0d540210383d00401c42e144e031520248c042c001d200701c000c4040c2d40c8940070f07410701601d0040003a02c94030361341030b900303000c006003500d040d13001c10000c0004050100e10320003036010b8445510f00142e414500802d0113604074403486200d0100c0e0751003d025450705e840381c0c00054036040a01e004240c558440221120607040300200320380a80d5140d05200c41542c006010710090082c2c404c10350340c0001c0c9248118443d81e00018294503c813541c0400424003130082003500d0042100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 406338714 1250 406337464 406337483
    0x3010e100504091205280207030209090c0f01260106080a0f0b1c08090d0b0609090d05160f0209090105090d02030405360a05161e080c0403150e0601150203040612020403 74
    0x710f1b80003582c0e11180e000036886440078101180d40e6000001e080862094090003442c40ac000c05e070015103543c54540c031b80205040060143d48254100340031124003801c4103480d0700100b41030180400048036030354444a8001d601e85890b20003d0342c0d03003294280381112030122200441c001407516410a00841080340d0b049000e0208880422000d413001a01c183d1056038170652603a00d2403020350b6070303a41c0c0c10342220200d0801c1101003500c1940310307010b8803102d029405c50b0740221040d501081051001f210381d40c40d240d5694080c0b06003440700344414106518648011420076080200040c08000c420004282c83d181e0141030340e1160019043c030400d907070100900c0c02500d2500506010140100b182e003402014100070207508000e00075203490b801c4455005d45803541060700b010a8442071000303042a618200140700000c00a80360680d0066030720307211b0030045152507240d80704600c7d0440680090401e000e08000f00c2da41d03181e0000c265400c50b4850b25158510b0000010082e000f1300c950382014002400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 406339964 1250 406338714 406338787
    0xf070903060204080d1e0c2306090a0c050a08190606080a03170c12040b040212030d0b030f030405130b0a0b07110306071b02040504150203010e100504091205 69
    0x4a0743c5525030480740c560004007114002182d44494082c3c1904e1b010480130b102c5e034000310702480002180c4040000251030715846440c14585041c074103d5007010194041e510780d0082043c140f60b41801801e05032405080242070003001c940315030700006640c8100308072841d0901484416008140103216501c1a60785401c440d0400400d0140d08180d03030000c0348407960104181c001c002044400b501203228011101c2c0d19aa80d1340300e40058050000c0c0c2c2e000130f100c103902e03190407420300c0144001c0404070400a49418000140760503d00700c40c0b4003a5498006100401403503c918200160300103d2000004400746882c002030b020010941041000240c003083d400d0030807030501d0740b003054400304604652013a0348a54045071240c405070400c00c1c4041107182450018141604484d4016100d40c420808805101101600301c0c0c000340c0c00390610002a0050018883c28030407214042c3c034040d00e06001101150b16900501000d820100c0100580012001c41c452050240030051000f0115003404282 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 406341214 1250 406339964 406339979
    0x325031403070528080c010905061005190e0c1b0d030617010c02121303020402070807030f02011404110d05070305031305030a0c0603200a051c020a080f070903060204 73
    0x104001c0b0102c54510441038040c0c3e111640702e5502c4045030f644940d80c1582d510070f45d1292015040740021000940d02c881e20031000610074442c0030f00c1000b0100440a000c3d240c44208074803000c445070100d50745001c890b0203120740340011010503848280406619a200141c1007810110819840c070440d00b8010105410032040c2d064100d1811070b0304411000c0406203491a04600701ea14480c84040540d000c04c41711040c80031045d001d0b2201c1c801e0420754030011966a0081804c0c0d80c0454021103a1110024010301056000b000c4005840d40c5807000b00314443c2b07150039444012801400103010140d810f003859030039507204e5460815051380241580c4c0000c0e681d103800c5541750020840004182c913607880100ea0342c10001171003040d554002c2d092040062400c03909500804c0c04624018804102000c1445031a4101006000003411551100e5071811204110b40802c000d090701c0c400c2c80d50040050307000d035551091006810454030740d06080c058441901c10b0300d092041d684020302250004c0741c002281c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 406342464 1250 406341214 406341217
    0x80f0c21090a08012d060b0c1011131415070302010510080d120c0908070e06041401030b0601141902061608010305030f07060209090f06040605030c0325031403 70
    0x10078040c0c1d055a206500d54035030500340c0d69843d680e004040d05d00c10031100884003584c403000059041500c002903440e1901c1c4080e003154000b6168000c150700c4071300e8201d0b20136003a100b42c4004441c0940d01504180740f050000c422582940308508420042003002c2c043c030754801a848080c0c20143d081d0503541c00461034040d000e018100d40001e640941c4910010707000102045103a400342040d41c441c2420070b000e01c2410000e044402c20141044a9504045018070080010700b01900c00303c210864149002d000f00410344007403601c1d00010101c0130004000080d0314840b140e8000c1b4007420820340040c07102140035101e029007032401000340c040c6111422410f4010980b64092003055100501c130440c501015034100201707200060003648204a00304035086264003070030b030041c803441c070141c84d04241c84002090f0b143c06440f0440045010710500c8920b240600c90540217100680242c03554400c42e5000a0700c0e40014000015103004407081000d845503030040d01005981d0040081c001d8402071220140c9c6c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 406343714 1250 406342464 406342477
    0x90909030e040501120b0114101232010f03020f0103020c0a02060d0204060e03010b0105042c0c0c0139031b02010903170112141c030507020712080f0c21 67
    0xc524064004101030200400c00c0c2211140508440c02d40c4400c445c0c102d524030b910000c02d0480c1ca540d100d030be0180720005100b0002040e40b22010800005150224150324070701a8001d04a0246600741000180c48030310000000303036004d0800503110000d080b001030800300b6003c402507114a00090740e120064042d0b01a00c207440031540c030306400d0010341c000c4c103080f40d00c0700c0c04c15404a0320034031041289030050b04845440342d08203a000c0e500c038104d42052030556502038038210356022000c507455011020910540c840c5103080301c4100020488010005d442d803041365601142042000f41f030081a50103078112407180c40c0650303121340342e128800388000d000700440502100026000000700c1d81070b40301002414140c600030b002092201c022a0385490000300701c0f602d80c0409004202610b03030040c01c030b100048962009500c0105444c038099000900b02480d076040400a5500040c108000c01c0160096441d01d030013055a5680c8c51803d00101454190301c90075034404801d04524a03204041000c019024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 406344964 1250 406343714 406343723
    0x201050f0d110d0612080405040e0307060e030421210306120b09120f0a08071214010e090f0319020106050306040821090c09060111010908070c0603020a090909030e04050112 76
    0x1101d860f060394140c4181001d10103001306d6400d0105104d90f1829501200049542c8001c886c600f0303540c0e41d03502c1c090702c810740e4202d4181d810210781000490380048017082070751f00304640340c078031070307000c0d540c0d003001041d001e0451642c0318100d1a8110000b8001c1d401140a003001680010320060107140242c5845411200b00b0410b010303000800e0302d5245c1c6202540c110811844c44a8100104c40100711031840300106608100009058071000e940401e201d5a9030051300c040b4021001c1d81070800c42d020700070f00a40303356401d03409103c55083c40381010058502c001c040342c801c1c1c42182a4000c01b24050f0101d900311541c14000c2500307000c10040c4507401003c900070f03500030098a107060b0280040302080100c805140d41c0d000300178401d61502d403298a01381d119070f0504004c040c86100514442c2141c08100e03040320b42d0100050b0a2050045a50304000105010b01d410740c5011048072001b13007840c1003849041c07103050300d40c6c0409013014024501c510441502810030422503a545044000d0b4030a240c0040d00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 406346214 1250 406344964 406344971
    0x3120c07150c120503060301090609060b0922020f0604150f03150303090330020d0206060f0f10020f01110a0e01090602030901050c0c15070525030201050f0d110d 71
    0x70a020340980c15200e80c103e943c40c140d03140826030645243e0300003043d00da459503035020802300040440c400e081d041401410001240048002400f04044000e4005110080c000c1c500c070b071210b207602c1241840c441e81913440e1010a46100e000c9000d40c0550b422500c9440c2503008600c403100e902c02846401b802a136601403014281d4058003805070380039070001500044103000d003400070615128017400709609400b0107204031241c10850003980c0108404010058105502192807160b04103c001d41081c81103690b88050041d0100003250059900500342c01000c4200d60007025500074041e201c000d961a8000b070000155804110450340e02c20100240411411451310400303521908140064440c0782c2c008500d861403010040d034081d0058003203d429446100142d4109840c0e41200080c1140d0004d400342d00d50549103005801c00f6000510420900c0820b2002c040300300d1070341903c0e002c03260203080950356940b503411100c0311032080710081c4e4003e6017044100601c032200f0900501e241c0300c1008042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 406347464 1250 406346214 406346249
    0x20f030a030503160e0114220b1c020c0a1e05060405210a021e01111603110d0e090c0903060403020a05010f0b030c060f040f060302130608070210050603120c07 70
    0x40d05c0003421002c030540015078000d6a9400c10596000a00c0400400501d4200e2005c5401a2844030303d4660020761041401092406079110001c0e0b25181c000580401541401c400d1903004e0350f0b03102d240c01d02501602c1c0703140710501c44070461508044490b8000090742c000389420b04280c1c0c0d8071142c540614403c03035408030300490003070740e4032054a066400325405801c1c5440c036900400b0810030a0500d0182c2c40d580c502030400c3c22014140100114040b02d507000c1401e401500b0041d16034801c5040e1091141c2001c480c8452050b131085d0707540440d003002c4650018648808400ea0b1841c060356420f04e405114400502c404c0c1a00000c22502c0544104000d002d080003544203503007900d806420054159001010302e945034130f4120041c020815000c40402c0c2060307500d0031200100c0d00503a02140200346e0000f0028048100c039403d58001d01080c3c141742ca1a800d1a82e0002d544103e00d0650402c22543c540204419070b400340041400442c1c1d05801503240c8190241107511622244140c102d030040c2c04440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 406348714 1250 406347464 406347467
    0x12060d0c1409060d1e08040902120906010510020307082203080c0c040e1905030f040e041e030801030305030a0e0601090c120603020d0308090c0904060902010f02150112020f030a03050316 82
    0x44144143d014480ca005d03803454040b25160200240e100700c41c010414400231413402501e1000c0c0c001459400840d4017135040c4045681e0030210180c103e0340c0034840c01c1040d03c0040740c00208a61540781d04c00341c81d42d9201c080320b21000401056100307013802401d241300d0000070f00010b240a42903040d0b4000549107250526801c001c11500395540102041d0052007654075101c44550440d00558016000d0380d15044540500b4079941d402500a00000b0a4400901090000350702d04a08001c0b0200c400180c28280394901030120081448010304201c0000700044004007503800c1022500003d6044510030350b1074211000c0a03048420a080019500c2d02c062105010f039130007610112a0058041148481251411281c2075001842d40b0304500c51040c8002d480d466904646e481180210170000b05100d03244001446000e0303a10340c1800310361050f404038010f501c14803c214115000c3c1076031041028003d00c041503c08081060860703250007040940000c0c55003200c0158840c030300c0000c2181c4560001e500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 406349964 1250 406348714 406348729
    0x30d02040503010c031b0509120304030303090b090a050c090903070b040327050f01030c0512070906031a10030c0e0306041a10031203020304062c0601060504030812060d0c140906 78
    0x12108800c8803076591a90082c001c00023004451406022039255500130030100e451a84290300072400680e039103424034103103c009403400ba040201c0d9806000c15025030b440b000c2c2d6030b40148042e035100e801c2401c04110092401c20032502c0d12a4000c8481c0710510b80780c01c01410702607d40c000a0010350701300707000300800c903a1044141c0030380328010704610305070310300100440c0103041c118990360600004004130320344030010000013446900c80e0368520503050304140c0010184d41500c40002c42074640c1c00c00d90a41540d9906800916415600d070002d159914400d048070024660b51109070180100c20600062048901d0310004551004e801c0c4a903e0311a200340c060541801d20001e8001801346240c5098103200360020764125015840200d0a24144100381500100922424520750031181c005484010188501c0d401080542441d9092500e10307121441e19200713082e944122501880c00192696407640390036452560003900004616881d03c908407581d80e04200041d11403451680015080c1c5003414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 406351214 1250 406349964 406349981
    0x31701080106060203030121021f030f02031e0406020d0606090f060c170c03090a091a15040306021c051305010e01060b12040c05060a0302090a05060304080723030d02040503010c03 79
    0x31300461544c0c6c6489038041c40d10108105003203101289480e0f4001503070b40c4118105c5400c01284160359114440000601240c070400741141e65607005000300003e0295080745030700d00401d040c042d081a547c0328039102c0000e12840e4a4009060f00e0b1008c0030800c5ca51011034001130311103600da610030503901c54004bd108000e03828001060890070b01c4000c0780201e0000c000d0305440500c503003141c1c1002c034201c000401251b4581c000c00f081a9480d0500d2460030307005c00702c044519100784e07a6048860102e009540081c4540d02002d0201ca800148801d00140904151048140080010002d905021001c59616000d5950a079999070801c0040b07140e469040c85800211110300103070f90700e054916100d002c17018600500a540200322540c00040c2c90b190500140b0501031503076001640c4150520401c0705051083d042180542001d01c00c02002548201c22280b445410002c01d4100207012500d4030403c0201c1204010b09001c003103821317803040300160058405d54200702d0083c8107000c0503100c00c40c112001e65 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 406352464 1250 406351214 406351217
    0x90e0f01110a0c0309030f0305070b06040908030a02070519081207050c030403121101050114030d0c050a03050c070f0f091803090b25150606051303022b03170108010606 74
    0x104030b100280d42c0078080426620780303e82440100300b0b5607502c618502904980040c2d02064001540c40204400020a02d9120b42c0440d020031082c02540c039000c0160000404600c08903074000b6240701406410802503650f0b0306d1036161010341146502e09080e140d040314060114003850320020030205400340e41542d208118a03001581046c1c6140c44400c0503290050140c814801441c90b4842605030a0040c3d0b0b0182039080342041050400c8800d052400608a215600300712500c49402c0005002040e29075603c1e40518246884000c44c207003090510302258081800d451544c2c200007400c5071000304500448581b030f6410410032a0307490290341042c4400c10000c0014021001c148560f150034406406000342503452104e8442e82500d035407105400381401560300c4041540f151341d0160366400303458040c05407480c3c054200f00e548600e02c24880bc1502000744100b2100c4a0000504d01e022401429840541d40b00c00f00805103040142c1550030300d485034001c803101500041a500d005000e0a030448416 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 406353714 1250 406352464 406352467
    0x100b0109030515132f0303120411040b0904050c03070501030507020a06050910020a090f0902090a0905070302190c03090f180b040906020a05120604050f0f130606090e0f0111 76
    0x150b80c0040702840340100300c4007244000554890100f0102001140e00107800c6910003103100139241c20710302290740340b12028426801041812040820391a107280c10a80c45942030403032b400c4100c0020040c10303043c00344507081002c060030002480780000310444a824154244c80e405900c0b10011000e4030021100400964000c0c04002e00051083e0b0003203074454000c00c00d43c2d1030361280c00000c000b680c1c031002d1103900040c6066000d0003601c2d0542882c200401d03003107104600c0d00c0d4500c40070a02c03802c0144142034003603a4030000a900e45000350111103004c03481d4001e0707003003024850070050131901c1d008400b40c00103155442d0124619550340e402c001500d2014100458400c940785420000c1d000d14200d01e5005512806840c001074558006000f200480d0703103c0342e440320007100500130044e0005080070320690810040c4041e0380064040c454101507204211030301540c1e01d0030440907180038204024541d03446c0c1070000505100c658823038994440c07048152030350310506d005603500b6180101010b0410540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 406354964 1250 406353714 406353733
    0x1090803072d050a03060b03151c1a1f050f211e0f0a081921020a0e01022a03070e0721090c0315140405100b01090305 52
    0x1e1041403620402d80c10042c000140c908140e8502c0c06020907151011640105661a846405005000103081040300d02ea055142c2022984074a10f03015910340c1c01800c228202760701d036507142c0e0400c03000305400000309507040051007020841e00d2022a5505a0340c800c00d401a10200c640003100d50840b40010135076040ca480c1d400c20844402e884080c4008681102c80c00000580000c2c0507080f0710300790010b1500031040d515441036041590001c00c00b0100c0d0081c452290000e0241001d4030300c0e410304001510500d601141d81035900780b28501e4103a020720a04016542030080c90707001461944081e55611021150000040e6076842d40f050204010b19003030521486a442203107a1034020340740080032900295a00c074283d0030b40c2d807800d440031b00015400d9a0305094150350f0b41c80e110b50981c00d015040080190b00d07103075145061070760f010081c440011440802040c81da0307a00041540842800700e42554213141c0f030310300e584000340d00c424003903e810444102010740c01000c0031001c407600711014000032030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 406356214 1250 406354964 406354967
    0x80c090a0e01180b0403031404031205072c01020f0309090112050102040e0f09010501050a0b0d0c21150e0f0f0603100501060c0203120a09060507080705010c090906080109080307 78
    0x100701d112000c140e6580d0b003116050700399151242c215950180324043c280c2d0400303040040c240d801c04402200d4041340d280a003c0000d0340515036911103e941200003a46e0740b90803000301c1e840100142403000120340320072255012402582d40c80c1c40d0200176000c0340c03400d000b80d900194890084a0002d91720102020040101001c02c860b0444a0340c0b0800006103025108c00021804120990b1100c0e09600c12000300403e040007481070502611040302d40c203030b00340d14140e11140c0a1181d101030343d090584803408280994000e0704100c1410341e241e9191016540c0300d00b1301500601d5070010280c40c06013905400609000342411080c040c1e0000900103c082e40c61b000303014642d00014001582510a0b8060001c803030143c1e214641c00b0303020b00e41e00c0e81000800780c0105441c19040c0c0240808000c001c0180c104149d0f0000540e40403541581041a102c607400d0800c41710328000c07110061b203654207044580a2031035101481e4403d45904000c1005000c1d2140e0300d075822181a544001c086980801c0841e803581e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 406357464 1250 406356214 406356221
    0x60f010b0a110c030d0804050c0105040b07060c0320070605010509060a17190f02040b010206060a050409030e270705090d030509040b03010606050903010b091e0c19020d09080c090a 79
    0x402c0c4100407501c507286024042071070004440111800241003d0601c0308102084c004242c0c002c5003481c01908281c10300c0240d180e98460325200030201d55603401d0b01581c00cac0c000d0b002200301c3c40004460601c100b03403961981d50103a0154508031741e140d00c4c0000228080c94032403e9180140340103000e903031402d41401d8149140b529554081e00c4c0d03134418401103989040480750000701d083d04c500e50303451110358a0b1040c0000d480c2c5200300c407419500304108100e100c0e02d90091007421284211000310700e0030140d05094900c0c0390130a82054000300060840400d010101e0390141607403407003000403105543c1d5030303804660f1801000d400f9a40001150303140d20100e842440034094100d001040020b5070029000040d0842d0415445a4007180001c03520b03080e185030070300c58044030031001c0e41d94402924044400d0a4090010b504103000200c038100414600060002920100c00c4a01220748454a5824002c0e42c0c4014140c80c9600085042034081003083c400b00c6e100089500140c00303c141c83e100c90700d178007018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 406358714 1250 406357464 406357487
    0x1f140f0702030f0a030b120a0f120e1c05070e2509180b1306030c05090a0b0d05070807061e0e0102010b0301090c031b05091302031006060f02060f010b0a 67
    0x1140300501c52a2107441c2201c000b003a160101e5200010b10a109400f4003001c2c401f130707109608142d0407910101000c2044821400c010b02d900071480701030301031040c50590740c5002e05031046810041120500700243ca461100c01e84450044044600b400d9403507403070180e420070480300c1c0302100510b075510800b0603103480150f50038030a20b03081000620342c54484034006040701d80105160b5645072140141d032800c0c201608000503850403c01d002d40c60440e16040d204113441e104c1d0b1030244180c0000100101555801403011100040c4221403025450401e1580c6e1a010b029048184c0620f45d000240c9502504c196001c41c3d140d498248041b03802b8180a0310060041d0107580d0643d502d8801c0c5540d07980e001c0c0b0134400b141d803095a404203444e041d8180400058003c0348208100040700d40144116540c0c0705005500240c604800d48181040388003081c141448040d40c1340065080000104401c1d811844c91059003e00d0f600700c411550b40c515981091000a00c10041081001c204402e18248910003240c0e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 406359964 1250 406358714 406358717
    0x1104060825020d0813120f03150f0b03061306080d14190e1f0f020f010b0a120c0e10060e0a140105091801090606120504050312180f1f140f07 62
    0x2c5800086c2c8a4408110301070303404600240c1c150010203042e03900761003061110a59001c880070018101088201100010701038524140c602100003851583d540c5a0301e041140c0c541410f2240070340d1030305001e50b02d400d40e454280c0401d0580c3c06601d032500380d0034243c43d10515000200c2c06c004c0c40808041d50800754540c54941c11041445a02c2e045184e103201060307000c038045d65001c2c41300c4402e000081c01c244041060500720790605600d10310319601c007081941983c102502d00b2034100254608419000c04682c000c0b526100c00381c0422400905021a00301100e8190301c0c0c5101048604041111100c4a400fa4900001e0601a10100c42d4860300107055035440103400d0000380c0c240c8402d40c00710f0102c240c0c040c601054031030205000d80c1e40d1107030030200322104082c0d0600aa080c80c0d501c031500d0b0b004200400e01894080c0c1d0000c4c01190030203890b940e028441c00183c80000f1131180c00252640004680790f1000c501d0b48072200c0e005066441010304205526035a031900740c0355016043c1c000308001c5c044a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 406361214 1250 406359964 406359991
    0x31302030a050609160e0609070f12110301140d05070e090328090b0a080c0a0302070210082401021203040c030b130204060f0b0a030c031104060825020d08 68
    0x340c8200710040c02200e50000170810241c0c180c0300c2c49100445074000700c10301107182050003070584882c1e92007030304000642080c5200640100c41200c0303650850b0a15802c0341d08003418000c48055810041d4166080c4480ba40402219030041c03100c0c50840c05c4000789580d004500411101c4641c880407600049240d05503860070600c0c0709803170b07548519204912840d0555241c1041459004094880209100a48103003031120550029102d581c0051084400d52000603885101d18441d5040f18081603004003044001055154018411901103a1f1500300c40310241590703101c1c018048100310320003016801801419000c2c00f286109070009002224501882a0040005041d83c051035200f000c484800d5203a07441d0354010403050b501640d100400210101c9014410000098120341c0004000d0401080e00145d4a0049000b07081010214040c01c101050119280d588990114021800301004280408910104082a0205034081d102581c041503011501350b024080c80c550041d88011000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 406362464 1250 406361214 406361233
    0x303051c060b160503040f17010609050601050a0804030203160303051f0f2309250c02150310030602031501120203010f18020c030307120e060411061305030703060b120d0503130203 79
    0x4600c7c0c196150824000070703000500004983c00c0c248100801402408801e00407800c1c00070010741103104980c3c80604015080c40000e080c140204203c402010707204207a100c06040c9030600400400f820341e00c144c043d039401c2d0541002d170481e4404042c144c2d020781154a942c180341c0351007071401240803a400060a4101d002c1c2d02290385e244801c4511a4010b50114400760304640710502042e510000078406002c500c410220258440620a8010100c040385082e0340c1e84812541585001841e803001700170134000070400c030590b02a00d05598400c03600fa26403280c0051282502000d03400309001e11002d00c211001c040214071620810380b1000d001c018001403034060b600782030504641c402c075905408924005600300d1800c0d01c502c01c4142c042c005002420b045d0500340d0380c0d01070b281d01c902103951265002141e80081c000c040d0403000b00600d802411150301075581d2510402810462410343d101e00303d01d1019600d51180031444030360100450348c07078500d1640c807442c4c1c5641c0b01e004410240e03050300c0340041c207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 406363714 1250 406362464 406362479
    0x305150a260f0a0c0f030b0705070201020c03010903110c0d0b07080403051306080415150b0f09040e07050108070503011832060a06020a020306040602031305070303051c060b16050304 80
    0x80c44402e41d40030302514244405084c460348103009680403103c40c1c03019800070000701b500f201d140c80c1c00405520f40b69646d415103000407071a08079406401940355107041d0900c02007580203980b1008070023103031040e6003102880f03100b00714102140120142900340a2070008603480c1c4200082688180310b07061450420450400c141468102e540080e8041520203040c4814842204082000a0b030b2540d01888100d00302402202d01d4061071180061141010401898400c1c241080c1c076064440500708102e5801c2080a00c3d580e4a00e501c01d103400300d0241000300c5c0c0410700c6141228140d0740f110f03082e05488400350551200902402c13418450b10b9440c481890030300bc124440c2c400b07114218480f100d4130340c02d0050400c07419441e0340d80f00c0d070b0540d481200b0140c010b89000c91f8566000d6007202d00140c907662441a0310510b840f107418028141d0184060100c101500f040142984808a020750a40d2040d0358410000b210450700a205004c00140015117260440b021621080c501c6107080e81d050071340c1c6800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 406364964 1250 406363714 406363723
    0x303060427080a080c07150c0e12010f0f0204060f0c0c03150203060118050d030e1804050d02102c1509010c12020717030c0415030203070305150a26 65
    0x10115102c0d01d00080c850b0400340e10040041d0002a03280c0d00c1072415481c0e90300d050600c40c3c04135100754140c1d11030500101c440d00035000c40003d204050b01c1450400c01203592640241460a0541021450b1400342240c0c0c800c01d20940307040d07501549070880c0c60300c1000c0c010703101554107100840d80039140060110001d040f410a9220382400c4650258690800c24005801c1491504401c46000000d05007002a44e80c1c0b140e26400b42d58260510f90301f43c000c0c030f501056646100d2121940b00d201507e082c8000c1110010b2a550800390715401d4503c103189013190101650891180e9902006600450722a0854100304a14442400c94109c560070000e804405800000445e0018040d95540041e010311301d03005400905070341c24282045103094159030300d8904149501100000c2070320040000b42e41428801e04440150081c0c46400884200700013000f070180d401186c2c00c8001031705040100e400700000300c585038040c4100401001000e130406110203014250907008500b294031419040c2c0290b4804d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 406366214 1250 406364964 406365041
    0x100513140609153a09050304060e030a050a03091802040503030414060c0a0c17120a0e0d06050109050a06050603190506150c06010915060504050d0c2402011a0303030604 74
    0x1440196590910f140781c40042502a40e14a4217003000680400940d010040701c0a4483d076052000310080da0340040f9241014030304005016100342c40401040c10341003082102202e1042080b03c0d40403a80508500c203a014134800c96805a10a03c400e104441c406034180d80c404074041c120714149004881c1c0d071443c06003541c03001c4e6518506403a060000c00300c403240c0159400c1650000341400301c20703030740c0a02035403061158010400c03180c070320315213010781d1070b081d0300e02e400e54208000b80000d5866250303601c01040252500d48180e4600600001c043c1844d0060b248241000100210710540138005e02c000b80200402095000400381c815204030b03c2182c0192041803c0c48004251940c103160f09601111002d8050008907595050b0030008641e100c0c086806a0b4015100d014114085280c4800b0118054110400880d50f080101000c0000c4100b14030010150354001c0c4940320a110110400c841c049906035055002000026201d0400d50003c81000d400b899042000100c03184201d0320120354070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 406367464 1250 406366214 406366267
    0x207020907030903020f03071e0303022206020c090402030a020f130207060f05060901030803040f03201506040203011a0f07020d0818150a08090c10051314060915 71
    0x503183c05040c554104000034031541d40c41c0085141c0507280d00e580790000300c041c054040ba95040c03500c0c3d0b010144070307405032070090414984048a40d840e4002c17030409410305014590041c4581c000003105071410003045030140e50082c0c003401c5841d0854003030008a0100000c1340307401c4070b9001c1f500d8452882c18401011083c0c0a0500080c1c01980e07113580d035003550400340080e0300c1020607030f00501c00b00d240300c02141e401942c410700c6800e044110785001d031001c01c102925082440c04071203143ea03000d240424614101407100326840740c180d907040b0800080740000c0c0500d0140d01c85420366042d07000c41040080441e04000f01800e400c10845900040d18a1074098048940b04004908428520301c03200c4d800f411824111013509986000c4500355200c0e01481b0f00c020108001031000c0f80ca2500d003484001144400581406041050b40328083c000c0c0d48000b0000d0580003c0e08000101035004141001c181c01c40105024a0960410100300410b2114580900ba880040044030b050314007100b000317a9070210710f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 406368714 1250 406367464 406367471
    0xf0303161a24031b1e191a030106021e07030b010b0a080f09061f150309050f0c100309020f0d0b010807050411071101090909060914060f01030b481e0904020702090703 73
    0x18000b030545480800424034113107d20520041c0725240d004140c810705001c5400380349e00c44061540d501031030010f0561020303045281100002c500f80c0240c100614014440751220324a584801d046040b003800c0490f041c60755038000d0004a80c091041c00710743c050141800024550702900e901c410f50360840c1d00c002da840801d94039030f00c2608101e028003040d07040480c0c02016090132541c810120702030004000c440308c01c0552780e05000c421035031080e05d4040409005003441a06043d9440c00d184115420301030f18046206209001170140b40602820b102d42c800e044049040990541e2007002c550701c4104100e041c031030714200204041c03100c8d01c503040310540142c80c0803500141c40d08198800c50050503500c044d0307410507401c01c1400a002036000741100e0b03018049920955592200d00941104004499100030702d050112040300c0c0e9942890552882444580e506030102c2140e261840c4205024081c0c1c1d0303080c440c0807804480c1c414014104101c00a0005031030211550700007072035a18200c030020042a40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 406369964 1250 406368714 406368719
    0x9060b030402030c0d15021b060a1d2d032506060506030403080417091207080f0c010207031221020c010b0f0303161a24031b1e19 57
    0x1c04010743c800e001c4c81600c000e240c51203030343c954039a1404040304200342d95400040c0710f5403c0400d03040451886440501341c84041c00c0c480840c00103007648104803a1070703411540581580c4400890600c242d1007280e1030400103025408140340e140290a100c03042107000621407029106103015000012802c1030080c0028102d240c900403080315100d40040b40130703001c14800c00c400243c0051400381c0181d041510600042803540e1500c0c140d21800c0e0080b03802c841462034401d0001000240742045d01c1c2100c1c15920a008100c125503070300c040c1c0d50041801607110b00000c00110340c156548001420061501d520552012040e40050186d490280c0002541c00529911485400c0c82624584034045071903003540d0000000080d40c81c010040e8240903038040400f090304005405112201d68007a241704080b003071600600d208188000400074100107141c601208202d890301140c2c4000034141c426411300401c1040003800b1002904c608000e600030712441c048401c1d40c0d5002840f074003188190404103040360 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 406371214 1250 406369964 406369969
    0x120d170106050901081906030203071806052b030e0306010e04061503050c040c210204030c0905130f050307050106090e1e030904020702010504090c09030b1807030b06040609060b030402 81
    0x60164081e2042020510442159a90020380030380c0060b154540c0d001036065001189005001c5030707000139894401c00c4000110a030310052003404e1403810340340030003020344d880c41449003a8000ba019802c254a14071400503020000b480340d0f134149030191800100c2a1510000300c1e240103001c2c1c0064154000c0c0c4002c0001704101c40c0107100c10940d110038a01c2d840740c41c40c2c0d107840c0e8522f048040548120340703410810081e140303e1280c0015403d061940b1464181e5204180c2d402544180820340b0311020454011429003802e0280b07a0045a0788030b1444402441626012108a802442113070035010401c0702c280416801d00611000e85042e03440060895082c0d0740041c5451203510615904104041e07807616107000220075201b6880e001d5a001da500c072403601c0101c50078807070381d0041d0010303d18001c00903640b540d21482e03400c15207200300c800069980392040603071090700c00c02c2c150001e5544042000d00008400b0b550098001d000640045410b584034240401501e4441c0c000d40d034400c0c4080100020351 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 406372464 1250 406371214 406371257
    0x31e0510020714010c090e0c0c03030408070b06030a03050306040207020406080610090c0c0206031504090203031b06071704110310020c060f060a1a160f0f02130615080402120d 77
    0x140306180080000c40d424017001741c021111392281d00100340400002035943c4428030211441d000f2610300ba299280782625180c1c1c0b6a412408050394440395042c0044d25a08001a80c501c1d0541c1680366070781166100020000039602964080340c0094440500003a001000c0001c01d0040b004103480d0b40c14141803075001412036a45040480400410b503245601507100e21089a801c807000b020b422603503044020214000e4410316900075018480025940d50748030440c661a003100a4480a0320074603102c501045420b10211080c0c00540080000420002000740010b900c4c1d601c0041d060ba840f9011000c2c1e8030080703030060036044c08180c01107401c0158942c8014681e83d405842110305105e01c07410910032014a26030050000783c20200001c0354400c0d41d040200500205500104000781400103242c002004e40004500708d009100c0c030000420601098020340f01a03442129840d070b0100da04090444103913201910503a0010300e44200c1c2c0b07800c8002844000c00e5000c1a031240b0b0b80c040082901a400d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 406373714 1250 406372464 406372493
    0x6180927110f010e010507030806030a0b0c0a09080a0804091e0f0b1215010303210504140c0a05090610110f0c010f030b0a0b0a200c120703020a031e05100207 69
    0x400c9842c40303a42c0085e03038012041d904800d8042c80c1080c01552400046407809110320400780c2100880c9040001d40311900c1c00038846000103545000716030b641c1d8030000b40c0c2da51511305c3c0144140000c0c041030020303018a500001c241d5010020602001054852050843e2840e840100c562900c2e4847e01031141170203404c0c8410911143c004211481c401001070482c2401800018100003c240306c031610014410000f948070604004104400d007428500b940d10451500308010b0303240202c405d140784601e000041101213400207412505695122001c10100144042e09071081c003203070709141d2110105c1003044508600c0103000408035a40720200240c050410300351032038101810702c2040d801310b49403095070804646029000c907848649000060301c1d5424481c1800791002000c81d003090741c0500c002440d03441224180c901141c03288da49000c01e920f900b518003010b50094003000040002170368402004a142e0402141c11003031007529031300c1e6401c0c0518422008201500401e182051003c002c102c241c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 406374964 1250 406373714 406373717
    0x301030201050f12042117130311060709050a05064f090605060c10050c0f0307030c0e01020d0206061c0b150108060d0b07080919030203040f06180927110f01 69
    0x48200100c802c2101c0c44000d1841c08e25100c296080c0302098056650301c0031014200b42920b6071032070803a0004110b040c9901c5000c2c840e24110b180000c89052040403a40300030214000d50303030045003584103071840c0300e1080c80d450f01d14203414185c03c0c24000c00030040314111384240090700803a4901083d80b015200c440c1c211603c034001c100300300ea0000d400050011411480b040e00400c42e940c401900003854080d10b1301a9444440000802151070792641c4130440703002d42a102d140c0c1904014004aa55088690b9a90090b03070140020a44515000d1040768800c080079050b840d807036403d65904035000e0700c1038640046500c1098103101241d1303089a41d40398009000c1e1400c6c500c0c5102619a222940e070041c140100340082e072004503c0080d01400300314091608521660944140361400075a40c2c2d0080c41985e41109000c1c00100d4007901c50800b2000000741e40e04402911170410210390010100d40e0900319404402c034560304207079001003196144032405100300080c150140400d009808180c0c682450 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 406376214 1250 406374964 406374977
    0x121503121308060622150b07020a06140a0c0c030203010c0207211707020103060b030135120d0e07150e0102070510030b13050405030903071205030301030201050f120421 74
    0x40070307110740c6503081d002d4968420303840f900c0c440c070b600b41ca00600c10740c600d00210401b0f02c000412108008002031640300c0c82914064502aa40c0b2011516801c03918020104004c0401c42940094412104100103c2c01035807441d4405590384d0000703085030846411b4a015030000032081040b004204406c192000440d004405a500e2558514004060072504c11079606000f0490209691103607010760b025040010707009650356151101d04900707006c5c8815540314003032445032000048400440010180a2501c0280026810005080a550000ca071808041d41d540c0e200c46034210410010304004164211b09001079005201006008040151405065620207202000581c86031101039840603001e160000701c4400c42000600f04c2d9115405401800c0c0c280b0007807105000010000f00380e00d1104804403100b50307955480480e441c5140c91400b0300076804c280010005940107030010064410716840545c5041003640054810346004d0301c0035216000078562144c400d03011000009205011403c105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 406377464 1250 406376214 406376221
    0xb01060903030503010918060920010504050604270f091104091203050702100603121107030c03060915140105030601061701030609020102030f0301090b0406140612150312130806 78
    0xd0f01a210601c54502659983d00200120300c903658004815680d1242050100d180c40d400c1c86041c0c0c0021030043c1c0c54020b4803004902580d03001b8003c07101102c0c405808142494030308460504070748880c001d141a0840580041112507400703120382602450032408c0024a583c0900f81040700e0b14102d22498040ca207007184140114900d400c42c01032407141480c01151030783d00d440c000c03400c000d0a2100e1961082c00d212002c01000320240e600034183c00c80796500001885102d40d02c40e51180140320151110741d8101052003ca045500020013580c0a110200d4408120344602403c40c0d52405a81a51189050040c082450148045401840c880c900f03401e142d0395400030b06100c40310600c4010056580d1f030460308211b90080c000c0d101180b203403000068072581d60320700b003001500f11604218401c518008010460520618a103d800c22020b4005400c00d0f2011002c00f44004014203110800e0700008070150791070b503040006055801d5107800843e1601e2074000e01140c000f10301e030880304c1182c0056040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 406378714 1250 406377464 406377467
    0x31b060f0f02180d0809061c0509071a0a05040b04090504230d05030a11032409010303050f1c02030a0f0513030e2e090302010806030c0108150102010f0212040b0106090303 75
    0x402020400c4501e02d60740a494500f4030851b1044c0701003980c00800c0407a802031054022882c0b4599010001400d00003681d44c5101151180000e02841580711265000c05189807030643c044d007034080150078420f02c0d05d62940c4010020380c0090b40a801c915485808200811180850144640b0041208046410241441552aa00c80103c1d1000b0018044009070392646580c210002c58503064031400d42ea03090104448809450200c0205008501039518030042d003807000505040341e030165161400e0240084e84030031282d120046510075002d00540b00000c1c800c8500c0254040d0518000009080700e180381e9400680790700505d11005210360403400d601080d00b00000f0840309104591840f10442404451481401c02c45e02c21501d481441d80e4442ca810b030800ca0100640b07000740c0710f41074070340d4503002010303918005000f000f40001c101c0340c00708020b04101110320000400c14000820340d0011510030070100d8100d1400c0c0c003943c54082040c00180703c81404454054903140c5010048607045880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 406379964 1250 406378714 406378747
    0x6020d0c020a060f0311040306150b0a0207050603070507050f0619061d090307140c01030f0c0c120507050a0c0f050a0b07110a170f0708190b04031b060f0f02 69
    0x3e0030081c072590781e0006035124400d40c0812070035801c0315240340e1180d8403820202c000f001b15040d40006802c0b8500302082030610907090303422504081e40240102c90030002400b803280c00c040c1c40c100510000307001640006000707000c0c5c2e240c00c0300303214020704551074064260690004d81c80c3e00c0c00705a6141500c103006040701c0301c060340d40c0039501000680d065150715a0301451803041c4103000d0070020210000ca0320210307012541140c2c0c82c50036030b0244080590342004108540083c2d8510b00440c1c00c3c0c4101d6400605030302080b4046820340d0a0060811020303488690802c44034000496651101d8102440050079260a0b01c0180c02c1c141c40e204001418200c000c0c500e03200c0d100001d0300c0003100c0b0310ba440242c0d5546201d540500000d80101c1c10012003200440d45d03d00041c80d4140e405e0154540c085841c407400560100c0b031510f10500b122020415071196071a5030005001039081200c0d0301c500b00304072080d000149030028401e100000e030b00052030703061a0458148003c000f0910380104810b8280400c14071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 406381214 1250 406379964 406379969
    0x12060409030e030d0203030601080a020c0c0108270a21080103060504020301060b0d0507020c010e01090501081b0316020c01080103030c12020f01050a0e01052a0f2206020d0c020a 78
    0x550000d030082007400c0a403800d008a160090749403084100140100b54080b020b14082e4a080c0c88520040d258550303c0e0f016130003203014212442d0b100380543c0ca19580710320306894200d061540390100104446480700180e01001e010b298071a80980c2c41201048035034400c0d00c8038030840880500c240c8140c424010102c400610001e40301a072a80301103819543e00398044002008412807035941c0d0342d08204410041c00048407090090700410042500b154000c81741e000014074141e483c169000e04040042d112085c018009080c051003040c0d074000000f2032007000318000c0d050303200804103c40c01c1800091512203a0101c184c104844c03007004000080c0c00c8000150810b500c131408802011441d0720407407034081040114140c40d800c4c84184240c5c0340ca1540400c0b5407000390002400203039030350220403400041c01359081581c420500403020584500501508280343d15820444c42c003485d90b442038661034080c9260245c0120703101020081c07550100501650741595040543e000c0e481500000d07059491403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 406382464 1250 406381214 406381219
    0x408071802070b0f0405120a0f0e181303020c0a0609050a060f1407050a0b01090509010e1902010503100e010906091b02070302040f0b0a0815061806012109050f01060b1206 75
    0x1139000c01c04000c401d01c5a1454040e4000301c40e80c0b81c00284c4402003850050400c820b0204104180e003c8141c244014040d003102e05140c1c141702103071a04c2c42e50041640941e40103078214054904a072040f6916110600010041e6544440256003460204030100f07015601c200c05020000e0451525250400c114907992000c0d2011140c0b1175070a41890723810407030130600003080e48401200201c0c0004595001b103003d000c090000304510408201c030290f42d200d1680c10902076a08450706200158415002503a0240030750001c4044c240d950064130580710030a0b0865500f00d0703110301e0103021120320751144480c2e0740482c440f01130a1841803000070f52250300d070f8000603000e1034581c9540025100e06800103002d082d006040b40500070b641e4100c458907844103000e44030108001c0008120140341603210400c0303c292940050b00c05494980043d10440d0380202010192186da40c90140c2c007545503c102e801e035900640191403280300704080c040c00c441c3c03681c200c1402d6550620511203604000741036180d02060071b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 406383714 1250 406382464 406382491
    0x3120a0801050607020604030b190c030b06160f050a030c031812330207110402091528050703090608130b090a0c0b040303260a020706110408071802070b 67
    0x1c4d400800e42d1072003250000717084001d421007031140c01c107107420b0814800c030700108042002e0164548101e0980b108000042d074802c1c0140f007041d07016001d0018602c0074503ca034541009240c01581e415040920143c02a0082081781c59801c0a168225004c140702151b0500300c814024204054800d20f1180c000010740050031410702035183c80b1018540e82d40381311395010081441d000545c5040081e5000c1c0c5000c494520038403900c3d00c514106402550014140101113615950350755000380a948c004110901c141e56000e070b503d820028035a002c00d910050340b0381c0c50a5842d0098107010744040040c0e401031080280942c1003141c02c80305c46200104103940108807002c1034551984107403500307860000250044106c500000f48150454000f80704484c0300340c450f0445c2c65007903050011070026041c04600b802c3c2884000411085242d4000c2c8140740c401e80d00001c072010001c85020b903d4001d90401c0c111988031000c02e1044842e8241b440c910115022400d40c5002c58564072030403c5807020f000c4001c03a022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 406384964 1250 406383714 406383727
    0xe01020a050f0a021306210309182322111c03080702030702130926040503010b0d05100e07150e010e0d0f1b08010609020903120a08010506 61
    0x42031020340c5400c1d03003000403580d20710740d06891a07403607a000340340032031107042e07203099500368852140a514110b0740c07880180c40710803e135152100100c110030503041b81082001003000c10911030449520804126039100003461400b007070b4000045640b43c1c4400f081ea4100c0c6d208001c040c0b485058a1000400b02d80c60701920004a490071201039480240b206501049141010320300d82c00c000c880c8800705001c0ea484040c035844494084e6140c0c40f94001c0a500400d08a0341d8041d00826a001005698420000714a81100003201d028950b20139003c4c440f141440040d0410080c0b82c24016114801ca0441d0000d50700b280c250785240c0c0d915090a400d090517516161b0702400030b1401c1c80000010481d030f2415841d58106104020303c48406a403030603011450040920721700b070400100004600d50310030010b00d1665110348450300c0000d444d41e0500ba141c03011820220709410207021300402071402c01d401586400740b0108060400c05009900004100241715a43c1103a03440007072141102e00076150f45070f9411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 406386214 1250 406384964 406384967
    0x105090d0218040605011a070201141207030605040c14190203070803090a050616020d03200406121d0a060c052809350f0d180b03160e01 60
    0x9440c014041d500505102a000c5102e50002c0e001c1c0c442c134420b81e010403841c0c1c1c035001c0d42c00400410b840c002c070916005024910055000318000e1059101c200d58030342c10002d020088031150786088490200007615050100041d0400d40603400f4902018185680075030002c0408003981c1c02401d40740e0100d04803070308a0841982c004d004890351076400c940c0701b5951740751405410303541d0017241501310b0b0184952000110400b070b81c42e03102618242941d0240030801c1d01000110040d10703158190119001c64409003101a0316110001d2004100a465401c0680649a15481202d0285004a50310650900c004103c00d00c0410380410840d8090000291368900180850b000c1c082c003440d00c0c048488128903228040c402c40d10084080b603a0740d449848064454649080055a0100054001c200315070b104042c5100102c410300b000001d401141ca2112114941b40d00e0903050403080c8000c1094454071065007402e03194050040d000d07803032915185050855141c404400c0b84004001007000209c1105400da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 406387464 1250 406386214 406386229
    0x20106052214041a06090c0304060509010b09072628090c0b0702122a1f0504170d020d0309110907020606101704030f0c0b010806010906090e0a02010509 67
    0x2541107002d00d1459143c50314007460030001e400b090703e04084010001030200d240955030396104500703041440f0700b5a201d9507200d0001d0b01c030140c09100c16540b05e40d9095015150302e000644140500d9a03504484120054242c0d5401d00b00900004030040d07140c10801440e1044043c4a9240c940c01c8101035810050740418008050000005041c008110800242400f540703001d000c0c03850088640b0800718159400c0d0959801d0112107191640141d01b4114200c41140012620300f2207000d000300e1403284409076011b090a001c0030002c8003140000c94180403007110700d003e440c10742403001e00420303400c0c80107803001e5a1204c039000048105a2284100002c00c102e10039903045d0b2030005440c0c0005801c19110294890508841d00ba01603a5500060304850703100b8040582c48015640d44200a6142d82e181100c8405000c00d0000501034005001c000188442d040c1d00d00809581000e0704865042c00d144809550096108090081c10000c1401180c60086001e980042d424244140e50f140c2110100303d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 406388714 1250 406387464 406387481
    0x8070312020f09040e03070f021e060304080706060815280c03140c070c050f180a0b0108070807050d050406180b01030b0108010e0304031203062c070201060522 70
    0xc203800842c01000540ea900c0150160440444043c003080e507845000c15900d018000380a054030103015803c074007600740303002d5410750302c401e422010b4034108041021a105074000d981c11682800300103202000c0c8519131207020080c1103140d004d0714414085480b4885140030140581c18000041403480261007941140c00040d4510038405004415500710040d0041030303180401da81c241c101d48000780c5580b454130102c80406500c5080c48050324100014807092480c985640c541000860071180f0503401405c03082c6104203c000c002281c81c0c01d40340700042005e140a040e02e400d201104050282036078000050316400c440388500090996220b0070b020002c1d00944014086034944c4800703c0c004e10041001e80c0c1d059a0003840f01c0e61583e682c3c2e001a500301c41c200102d20f0f2464009003c280001440c01c2c0381d0002c071a5542c5800b041d420f460790720003041c10382d107a04280d03580c492014001800c00d5207070b4000d0764009180e0008100c614980008034801400001d0000501041d40141210f0001c513603020844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 406389964 1250 406388714 406388747
    0x3090e06150f0a172401020d021b04060f08060114010e0108070c0c0e090f011104080601150509040213060f030b100513030b0f040507150c0b22031d0405040f080703 72
    0x1103810200304407540030803600755040d9201a480a01d42c107079400050064236a52182d030040c141e030b00200c2e0803140449110301c81a5802034440d900060240d08240f0030401400a1502800c403551502c0d441c0c0d0051407801302c01c4c44c1031003000884110540e0f0031845550348201d06003003c03100d5201030300c0c0840c207445041e0041c0000101840604c0703003408000903c0106c040c0c0f088001c00a0711201c454106c114080c91140e558582cac041c0c0018480e4802c10501c820001c891800e066090080c04000241643c1014294000c4010480b07410000140e0200703d40c4040080d81c2001c101207414070b0046450183c208107c00c0c02e00800168180c10340d01607103c0d120080d5044004014982002a04d03500c07140c4007a141030360703070388a0360300c01151280c0120980c030050641030b02c84040b000003681d922429110700801c9061903807007002e814800f84d4000b2140d0f2000c2440f0396200904c4507600f42c2c1e10b5035480194043c80e0f000c1e91900c3c080100080c00d002500000580054841d5191462460300719104500101c0100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 406391214 1250 406389964 406390007
    0x5060906190302030603210a03021c060b0d0c11100c0c05070815071d091003080715050c120109050a020403051b01021b06090d0305130303090e06150f0a 67
    0x41e90070364107501850003800700b2019240300d41a4016105c0a011200b0301c14040210204415000107010340e0041a074401501d07180c007603031421070342c84070308032007065001051210000a407001040e40d61f208030110304925080856607041c020180a540b0444400b03054a55030340c502c00340240c90b0150b071720304030300030307030040469003510b45400c013031078441c48880c0510b4446078205011400c80f030300925020603115411b58002a07080303a00e40c00c0102e4200050726110942e459040c010010640510080491601400d4400c1075410102c81c040205c0300c0c010000381c3c3c05401071007038010000041110b181100c020020100301515220ba081c0000e105661004059120740000449032440d44a00380050180c240c00f6141c04480d82c0c00038070981105d1a48455100f041005881c2591900005002d20345009150050501804049001d9050740c103400603130110340e03a8401008000b03c03100a1640c044000d40385154220604110070001d802405400544440081251070340f0b140b141a403290740340c146101e483c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 406392464 1250 406391214 406391257
    0x110f041104030c0e07020c010f0c030e0d030e010207080c030c1314070f0212210712060803070c080304060e091305060411011b080a031a0a0b0910021605060906 70
    0x8103c503d18400ca052242c2110002003100d030010841e54161081a10717021801c1120b4402240c00d00e44018007217041c80400c81c0300e00750301c0e10703a81550021640329031116680c1100036400640350203070a0b03002c0641a401302101c0455914013003060b00704001c1c1504c0c94000010940d0783d4001400e41c10a0401181070f902c0f04000c00c040d44202038006040003502660300920508181400ba4450000000c0c40101d50740c0f1721912003401c13190520350040760341ca01405a400401981c2060315511303448183c159002044c0c500921a644180f14002c1032140c0003146803c1c54001c3c0980000c0c1a900031070303c20300e40c1000241e44000035444000c240c40d44641901c0c1e00c3c5c0707442d00d040400344c83d0203445640052000810040555010840004856040b500c00350505220075812409000010280d903a08580307941700f8005500ca031841f80e40984142c034240c68a032040c41080c403d0360b544020240c2d0856101c440d80c902e8001001444c0d006451040c0e482c0d030354130040b0a010072084e00c20124906955034122420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 406393714 1250 406392464 406392473
    0x1202030a0605044a1603030f0318020907050c0105090106060f050304051902030a0b01080d090e09061f1e0911040e0c09060c0a1104050a060b03160c0f030207060e010309110f04110403 80
    0x14017040da842034459a1540700034010031021079070401c004031812001d60440c1409460262401540490342c0d1821a14103031801340c500782036507030130344000900e69100c840910020750000f14001420005107049800c525103a00c03020755072940018100c0089051070818825914144004100e20340c21150034101541d42d5611642d880c0d01c100310040025a014030040758507044611641d0140355400c0090035203440e4405001c03c12201d106a002d0942aa0900010003000d20003100862206014601c60745906e001a942d0940d138508400034071a8200304814000040c503840641d410481d0f40c0d0301242c58407400310202d50b981c490f041054607540700703008060040008a081c840c00003101035409020b03540b03c0da01600c082d5030745800b4000b85403d0610000e0502d016058413850740c1c0b550b030715204141d1402611648a80030100000b680140c211800c28808242c104140105924003883c04000b422520340780c036081c00c90981302e030510a03020b031f000c102c0c029926a0405d2980f0102942001d554aa49280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 406394964 1250 406393714 406393753
    0xb042109050108060103020a050706110c010f0504140c01020a260d05040c060801050a05010c06060302120610080601050904150617030702031203010b12071202030a0605044a 76
    0x78450008001d1800900c1c99403281c0240e845050b625203d0301d04004a55030380c0c6010381000005e151002c402840107a4000c1001d0140c00c0f0403040c0300c40005418109410070302c41d60961850100050742c03201c00041c1164340d00140c541003003604928030b5401c040040030103203004941c8840307501d607401020402200031562580300f02d0007248200c1002803095610700e8180c40b455801d1186c181d00142c2c8010401965002d6035442c01d000344140c000048564807940098894014201c0000321503000c84200042c004940c11040d018000040092195600d1728002405201d00144010010301842000304440c0c8529040f4030040d2101540403c04d91032030651584e613a8105200c1688a0f10801901c55169404141282c3c183c0780343c0888940750410307140b18040300c103001804840400802031100101203410780b002d10f00070503030038402041c035034500410402503803108075040c880c030b40400202419560300444203040040d80301a100c0500e00700d50709448101483c1041c400d5090050b000d6100082405c003d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 406396214 1250 406394964 406394969
    0x60618131b1d0f0403020c010e0126070801081b0402090609120303100e06030a06020a02150c03040c05032a030c0a0b03091c1b0f060f091e08070b042109 67
    0x18030003240c0f5950b2090001c0044030a94000c0c0c00740e0803d400440791944103e1310320f0142c2d03d060502a024281c140451104114241158030416070762074140285d842e0700408882c01407800000601e1985d03200400c086907940205083c0d40b1495000072080c03060344810007a1094244000c103007003a010000e030145074903580221b40c005036901d81d82d000491003803020b181c00c90154001a00501043e403243d50391100a42c007078441d000075882842c40020396400d0385984203108100b00b0440603103a041500e0904120300c002c1e00310034403e40103849119050b4200303501a08007083d007803524458170700408001c2170612102d002410703003110103c00086094015070000710300940c1c81d2000c0b10554440c5030010201125a52101c8001510005190381910070720034600c002d041c000c003035008144040b6541d10003102c1401440890450701c502c06001401056950307100c5c003640f610b4403160000030302d5560740b030030344504040140b4401440300898107006403501e100c0e00e14040c1c00400114150101400740404a192 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 406397464 1250 406396214 406396259
    0xc0910030f210f0e10050f0c0304060909050f06010e040605130504210c1401061511010e011a1203091005030a0e0304030f1124040503060618131b 64
    0x21241e00d0b58a80c803404100b0342c1d550035980c48682c0a40b446003009130300140140356608204040c0410180e87e481e000c000c2c10000e640000841d599032070400080c20031101d55005155192920b020003690001c0d840a150b400f503400d2034201e818401c240c0c0040c00038415a00b105800c08200e9112040e04a0a540510300407030248411402074000c941e40742c100152088068800100100c440b200041ca204c2c1d03c00760176143c00d0340003040003502c5040c810382e0400c0d425200c80028001c00101c4107026407c2c41480050601c44000f070142c05400407000c041107000080309406079210f84644000b4071002d0080d6044c0e101c00400e04441482809401090b54105650f421512860315100f0018a44004100c504480c0d000185501e00d6103a034541140940d00d64503003035080600f8083c84048605a604c07204080000c014003543c0359802d25003031500d4143d00500f0140107100000c0007030340d0680441080c55020408841032424850716103080d000c0b101200d102d03203501489400b00030078011031503000f03c125100385 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 406398714 1250 406397464 406397513
    0x151026100e1b030102030601140f120411010f02071445010e0405060406180b09010e0c150403020904030909060b0d05070f0e011d0307080606030c010f020c0910030f 72
    0x2c0c541098201c3c4000e9640314082405001c000c951941140040e01610403035401d01405c0554000703002c207140c00c0c110f80031034641d108504c003030540d980c02011212140358180f00403d816420f00910503402d408070201d040c802e002000910441c4642102c4051030300c244c00300e40c80c11744503c0059102d40300c01d140300354048000c2a4000490717100303c408645881603802c07900800003a16517446050061003255a8217122040031403455021072616103040703000d0700540f400021901c1801e4449414030b41d84041342d51050300800700510f041580801074600340d0303804460440c841d4540345020f031501540ba80c004100c4504014001803114a44c030040d00174601c03150b40900180c0e072415002c80d004612128144081103007055070117284e5200391000b92003500d0240000f80003081c0c0c1c0c40002e10b4001960701403c0c1d030b584044200a02d0b03013814400c0e0161500d01f801c144980251101e806500c410350003140500410945001503203007003070310140a004541110282110b0040383c140071007004500440c0700c005071003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 406399964 1250 406398714 406398763
    0x1b0316061d0303191b0c060c020a03020705040f1814070b04030201231c0509010608030405220209040608060402150405130e030d020c151026100e 64
    0x765404a0408500c08001541c42c5075509061401c001030b81001001000d6035694484481d881140c0000442a071583c4820741425a1071600d80181d07200c00a0010440d0400000000040d07000034070301d004e5171070031113000c00c602003415401e80007415030b20070340e02088018291b403506018a10403080c022905040547d046c658440c5030741a00b034400d03840003d000407889903c9010500a020065400c019000c42a51500640e0207040c03281d6141c0c02d001d140010f6556080c0030340c0303680910414000f051080081c60810b4680800601728070411000301c20306901241c0f565080009503411180303c103000501c10001503480d280d107a5521a02150203d0041d20b141c045120031038101c0054030101e6a0003000c030100301203400114009000d500e20303468210312050210141c0d0090300d001404049008074001c1c410a41145140e01d2503550203400d103000c511110300280000950070040c44c241c48500c12800c9911320080400318580b41d402800440b006141001100410b10301051845101c00031840f00400d408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 406401214 1250 406399964 406399991
    0x10e01110307021b01050301090b040f050a06140a0302061c0905060c03040303051513020a02070b0c061e040b01090b010509030d08010816120605040c080102131a03060a0b1b031606 79
    0x40c1030801d44c0d03002c10410f1004020000c455041020101405000422034070140c940306070a544003520301c1501039450714802d12003902002c0404006d020120b90707140c103840c035680206243d4854004104440c031002d0310903a0081d00a81c003d80b4001d135000d000ca699514160f041907490303410a440460000e4104008503842141850b0740d001070250050108a448800311480c100950280300c0714025030080040020700e00c0100310150484407100d07009040c0c54600703440c051520912147e0303901c1c0c0e060709600611010980d02c60005054440c0300c0d00010b074225014005a0303043c0591040160300d4410102e41c43c80a542c0281068104d480c12400c60f024207200c152840c50041e00c0d8011100c504c00181451404a0001d400aa4105014aa0f003040301ba0300e5180b070b9401da0340308a031403a00008034400204290107045c0015000300540b820314504504103100090321440c0903104800d4410f01c003088540c0070100440340a0440e06841085035510450f08000307204c0e0180c9444146c40e4185490211800340 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 406402464 1250 406401214 406401253
    0xf0e0105090c0405092d010e060c032a030405010b0306091504120c0804030302030403051b030307110105130905011401050f0f0f070605090624150c010e0111030702 72
    0x2010000d01900a040380b85080c04002d200c0148001c1d89031007a0107203101c42c3c081422070400c210b4040343c282c0314900c8850014074252410605070101c998018020401003104803015030343c12000781a4010b021040c2c004003054550303584c1884040d107070000414030040240540c04001c01c1c6000340d090354403603a652080140c4841c0401c10680300c2c0025040014000368032102030031722001c203608044100d0130301d50311800080d030032a4200310050703800014180184041046500d4840e414514080d0305070143c0d401107601e0380104036001b0181058240458056800380d8281c039129075214147d501d10711ba40306c090f040070f01400e00c600c0c000c110080c10301c0b2259504ca002100c4544114960107840e085001c00c03007030f0541c2c4c000460842c030103005010360f000082081c09441c0c000c415220084c4000e0034102c5415085000e154914400011b17000d150039140c3e15206a80b18a200344a00c100d0744485180490341c0c0548010344e44990a5441c008510110003405005940140500d900715103200d0004d80c0010440c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 406403714 1250 406402464 406402471
    0x21207050909010e060d0602070507030b0c04060806101704030c140c1f090e04030e0a0312020c030c0a0b0d1401240c050c1002031306030c14131a0c030705010f0e0105 73
    0x140e01006d02c030010a6854005110451003042161200f42d0b80e0346030b010889206507940304094900050400050794804503aa070040d00c11100c48800c1c1341894005031906600c00c042c1d62149000f84001010b242c011200074510036048011001c4000caa208110f840c2c803501b9061078400d415620007604551542c1a400380c8400381c03600c0c0d103000d550a0001c03002a05600800031001c10560300142e864a84684500d80015841a0142103252100c00ca02078102000c00c64424000c0e8001c803414026075a464404004445195111603542c00000642e00040c10350300c00039603911820480001444030880142c01c6000400c002040a100001c0c10222004204600060141e44c070402210700703203107000300a24886043c1801240d15060450510064080095100343d0110342d4502484180c0ea41100c40468401e9001c04180d00d0700360455041c06080c8914094130001c41c0b80d545004138a51032110445a04000791011a5290600c030714180340a07040300030f101c2d42d0303150a21560003a803010501a0602 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 406404964 1250 406403714 406403719
    0x51602011401030804140a0909030e010e120a08030a0b0301022706040305060606300402010f02210703021203040602040f0b04080607180f0e090d020f030418021207050909010e06 78
    0x80c2c945407145e0001031140f01070703000380d1105840c00b0000c0c0341c01d014270400000a10940340c00100030610300000d0440170101a540b8082c10542c1045040003802017061418940d1003420903071203455024046000300262112903400d5840090fa00d02c40551007003510400440300d40d07203529088240e10910120b4003451100810990204011910300d1411401500b54401020041c03c0e86a800594a4124070652002d10b0140030054080c08195680007100c0146485a4002815080e00302142c0000a403a0141009001a0042002c01c1094420301007400c0250403405450348a0800707081c2031000394001e101c0c1d407008480001000442c030110b0000d0310212501880078111031b80c0d9004054403800840c1081400710b4540c14408610745070080c2c0b6220140c80e00c400f4190b41840c3c00c841c002e103420152180c1100f0765200040000b49403000000704e5080c0c503c00c22513985580c00c0c12280c0390103409040315521040d00c84408000340180d200d030217801403540407a040b404a0f680d801e030314842114282e96294 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 406406214 1250 406404964 406404967
    0x5180f0d031407021c0c06031817040f1706060301110403030e18190b040b0a06110114010e0405150c04051c08070303051015051b100516020114010308 66
    0x100401c2c000c00011200c80d038a03001c90707454a6000d50001e0500002100341103140b66050b441c0c803081c41080e03003103000a8000c40c00d04018501070340c50100025600b801c0002e2005002c3d90412110b410345205480040c04551103c081ca1520b404071111018503008040d14944139590004007a45014004e4500394a4040d21051800b4150b440032034109010030300709034200280b07013151b88028a9405c0c035940724581d0761009100811200d88100c040d02d03500003200b0b03c02e82c2070080c0d021160760341d404020210751060414900c0c42c2e20400c0c8150241000489204505e9141c2c000010b0b60b410341030000307112b140f02c0e07000d0b01d21000e0a83c20450101c6410740343c483d004034043c0804e2149041c004e003000d00711761070248492103c649544d0360341030319400000110006a01c590620035041c0e00000390300040c09000d03e4403040c0d40801c050041543c05a0500d2003250000314a15550700f0000740403200e11560404418072091600d220114001e50f019281c0c000190b2034000703161943d40e501c494480c1a0b070b03402101c3c5c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 406407464 1250 406406214 406406239
    0x608090d2001090f050f01060e010e0a0b18040f02010f0201020327030c03040306150806070e22092a050a0302120102041508010f050f0d02040507030e0d05180f 70
    0x182854141c0074049a40d80d0b50701c1d81107001160200b08104031481c8102d00922110442e440746500356802940b001c04210203c00051000028000034180c0c400f116000010380040648002a00c0c20070080c0c10070b8080795008240000d0100f00010501494000c2c9c89244da0001000001c901702e2004884144052071942e0705c02d51801c843e44244011105000b003280c0c107240d5540038041c01c540c85944210b0741396070303a5481524007103000540c7c100100307104c4010700314500e49000d025101ca9031007621648940d0009410700c03504480004103090048440c40104940c019a00d046260b403081c0203da83c2c0d2014194002c4056641510030700815958050f180c0c0c20060300e15800d101d5205080012920380d075400344004180030891501c40400d440b025920542c4030b514141c407119000034aa04031501403440b0802c2d140f401e0700c4417000081c1c415415a400180d81d42d8071341088005000c010741982c1e1720702502c1c6841c3c5001c0e03800070140001840c409508e2580290007420807000e0203114004c2e0350003001000c0c59 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 406408714 1250 406407464 406407497
    0x40324140f040b1f06020f06010b04030c0b03040201230304061b141606020a020a170306100c0c0e011404050f090d0f050f0d09031b03050d0f0609150608090d 69
    0x10720b60090031039400e20701d82c9140c131070b2202c8514819410000040e408004915012002045003500500b1008060f81c83e041c11a112008290204d01842018160000202d021640f10701c1c3c110408401e40c0043d956942c00000900c5816071096605903503d60400490840408031102454810700c1252180009208006800800c070b40110040c0e1070300f40030b0310402034049507242c001418400c5950740038000380d8400e4a007210070701501c02c04e203150b01001481080055110340316568032110141c207000341040ca6a250000e91286150800d0a40d060301c0c00001a00c0b4600420301e4810480c115800e000541c0d8044845a0300d12046a06074000d0344181e0480c24040d0040c88030882148041c648107141200c2c02d89246410307400342d50030031800c60f6645d5222051560203200002107107142a075803686621103807401030140c0142d04000c00c1003030380c4a481d10300341040c582c4840003c10000b03a040c03090b440e01500786180c02d05035215030b0300490201d00001e03482c4600400c528900c9400c0742ca400a004e0000c13201c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 406409964 1250 406408714 406408733
    0x903240b0a03020d0305032517370209030601060e03070f06050d0e0c0a061d030a0f0f02060c0601030308070314070807050d0209090103080702040b060f1801090b03130c060306050102120f040324140f04 88
    0x201a030552f0030080040291010f21085020b03203074070b445118410020406051802d4141e0303025141c0300c090720034184940c1d507114088031400148044c002c100112982c1419040c03d03003a080e0700380c0c0140c00c4040043d00580081a41e03c1c04416410020030400340c03841031681ba603450000c010700765000341c400e680010302c5060f0000e0f075050010309082c2c18510110342951070010203070429004529079104000cac0c0c03e581800f420008884000b20f000050a101c14058500c190203081720003481000304502070109010350541d045c100d0002d00100c52541c1d28203246145601034001a8000c0341421449181814041c0450b4004050490b007070345424075000e1100640001c010859041122a03a000584403100501541c06806090b00030950400d5524000ba007610541d40200e00b0725052034802c00407681c0209000d0707000c405a4441650b944140c0c003580d03c0a00c1107410040c01c0f4040c2c40c01d44e4407180d5456600c0b5102a540794001c22801001c014004c07034213141207411301c0000500600007400140c0040d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 406411214 1250 406409964 406410061
    0x50706110408030c0601080c040b01020d0c140d05090f03010203010b1b012909010e010501090314031315020c09040b13030903240b0a03020d0305032517 67
    0x1540c1814652516426415584480721400e41d0741e202d4401481150418099039041c1030341150201300400510300013030345a4034901c41e040e06200b018800300e07080c00705c1c029800c00903c200c1001c1da10000c840c10f90241181c1c02a0014a014603249040d840e0a801d0501c00c884c141d804282c0d0003400c0c407030700a080c00403656451054009954a6070484141d071b4000441041e03140d155060000300c204802e40521a40310416845000308000b090b00411a60760071480c02c4007130320742080040d0205039205c0d85091961140846070260204903880005594082c401c044418541c6079081e903400100300780400586040075227005d42001c2041d00412000603002441150591181c2409560551b4030f4940f68810314244c600d18000c95001c507600030410000c0d1040d00c001c3d0604a50403000700d0304640100d49403e0950320000c2c1804800000b1401d181e09440fa4a8850000b010500c800004000f40090210b130560f6058a00e90000341c000c00c0c04d01d01c290b8420001c01e9050420360f986042100072a500200e01c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 406412464 1250 406411214 406411241
    0x1306110a0b190f0213092f071b0602030405120706080105012106060302090a23040b010c050304030c170604020f13181103211602061b0c01030b10050706 67
    0x151071030000501140068114401c0c58189841c071541b030180300209a50340710000c2c3c1842040c2e018003091400c1c4c00580304001e0420486080d40b036040300d140c9000304604110700d0104040030104009a240d41c000010802d661064a0750440c00c5003d0740f0b85541c0340094020301002c00c8485006000ca075105140078000d211020428441d1785101003880d41c1180c4480d08603100103900096414898100206000c00500019151900d50f040790368010040405d4081118816030326840307080d8990703100b194001c0d1600d0308641980d55980d50384c0713030a044481543c07041d01c41841d0720440c4518400c4000c1400791149401600c1d100c0c000d0030003000c125844403038102c44210756940c0c0101148504040c000540124840c0c0c541c002102d0750001010b1401082c0000c00c400300c810755402000722204441542d0f103607582068210b608170054400038550b0301400040c0c244031032a6002c00410007030700150701c03841c2030703001c3c1c80400c04d0340004003c0c00b0003218840000d4002c28070410203480011600d0380004060300c4070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 406413714 1250 406412464 406412471
    0xb01020d02070308091807020c0f01110a080304080c0d020f06060a1202010804060f0f0603350304030c0b0405010b0411040b040b030a180311010c0c0b01050402090d05031306110a0b19 80
    0x101e0418001850081e200c110069001000400327190400f140d803100b01c03000c00d08005000014900c003540d614081110002c10004010020804210512007541c050a241b1411f4541110300c00d18000e643d00245050003149200700740100348a070400c01202c1040c0c682c82000d401c0a02c0481c1c0065076480d40151080301e9596039641044500d1000d072040f040075209111700880c80d54030b1400c00d003680b00088098230745480c03506100c54501040c0d12180304c00c0d4000c000607564895403941000e07604001c050002900f14001c03241040104032041d03201e400c46510071507040040b1440c1c0900130025000301e00031001501c1c0e0411080c803021800c800516889006800c000c02c1c24201010300120007034050000714041206105c044540d14400e015100142c19540360144a00240340c403580035450040c82094000c6900042484441d2030300300c00e561032150800304032540d8448401c01421541c185100d040c1c0002d1000800e450100004205100b50a8015500100d245c031020503420380d004c8480307000201561b9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 406414964 1250 406413714 406413739
    0x18030c020a1a070b090c030705150d0606051c0504050619061206020307020609010e0309062109070807141008060d1a0105091e070e0d05120d0b01020d0207030809 71
    0x1c1c0500c0c407440e01a0418070302502e860613490034030f01c03425010340008119003101862010a031000922581121800c940380c1e4205410803d80c101c080c8100004000c41c1d608204001c103000342c20000814900d8141404d429045401c0c41251040390700c151801082604104040380300c0b074110720166424009113040006607599580c0e004c405035010100304480c0076802004000409805100c0745900c40c00d410000d002041666240503160711407070f401c0b14840d640204880d8014801396403144108255201c07040c1440c24070600d0a03030b0300d54245c411032440340b08441004c07526010802041c07055007005400b8000912014400b940d11040040920780c0003402c0113083d10224055440303042c00410907a00040e45541018103006d4150300040114581c800c0d0202201158114215202c0d0300c00511315101010348100c0c4000f844000c0d8000d8050628031a0700b002c04030042902c40100000d40210030300b0400c11554400680c4c4030004a000c840168000300000c201041184005020440c80205400b803180d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 406416214 1250 406414964 406414979
    0xa090605090a0f0305060906130c051e04020711090601050a09091a15090a06050c03070b061201110315010e030714190608090c0603010b0417030c010203160e0418030c020a 75
    0x2500d543c13040c2d400c1d40c00301d0705000000005000c101d410458580c40c1411100003510340303258441e007500c64240145910320140010001e0000c01040f10540103009650300c001c103003807512074060041780c041d108038601004620558000d004840c1d415500307880301140e052501082000903c0c0801095002001c1c80000d0041d55890f80300007484c00010a90381602d4160040600c40280420b4100005002003000032070500f900000c2500c00482e40600440080d685602c04030f40c0b94200d201100e51150f0070803001c40366400c40c010207503115410358080071f680c1e040084011260710280115954054000d020184040002004200b007003030400361a9400c0103d91111019103a116540004c0001d000758040c014600414410031541800444401d4119410240388550f04c2c81103204d46900b410902d8130305600c80000740300380c55070b07081e4480c002c640324603003040810000d5010440160000342c09044440ea20b2601340300d1024086540c8961012130040d170341d0140c0d650440c052090303078004004000080c844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 406417464 1250 406416214 406416239
    0x4090f060204120506090d12020304060b06030709170714060c121204020f0907050301091508030a0e150a09120f150605040e010e0c011815051c020a090605090a 70
    0x500042510340c04040250804c00d0400b8009020310341d02c2d800020590b40c542d58005c1c1100740c40c1c5102880182da0342c0321460101c000705011350300c140c1c00241c088208070702c00d40c00060000c00c0301d00300c1010210512030403081035102c010900810344240702900448245003072881c080c2206804031022140845641c80d00700c038590b00945510005480710808000860420b449140859030054410705045d050002000d0b00c50300050040100c1c05a842217041403481c2403290000c020b05100007503a5482101080c002c08408084842e00d02818003d852800c600d200b510807070f400e03200640d80340100141003011200d00020315107015141d03031520341c040001013010350030101c020206004002544a24281c144025200140d031071b54841d900d0090710304269030010600400e040e0007442c090b115204e118407074602824081e0401c00c804400e035540c001b58641c0000c01080d44419008178501096001c1010078280d204413140500040d144080c1004140d00480c003a0810040007030078038001d1500d400008540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 406418714 1250 406417464 406417469
    0x90f0b040e03040e181614010e01120f090f0503040303091a0711040b040f060905070c0803061002011b0309031205010311130b151222030503220f120809070504090f060204 75
    0xc40b885990f007001f8140c0d06a5030400070603401c2c00c00b96007032040200060543c102e0040c02c201102d80b030354008145902d0395880305000c0c0e42e0040194103c68002d04066503203802c0741c0400c8000ca1142e5101103256181d55490201e5205410314261601080781e48002c1c1d40d4102071403a41d0083c1d00c400c500300c281c0d9107900458040c10311000300086d0301450000c1c05001d89001408040034402080c1144020a0042c001c5a81c04481075601d103e0b001d486501c100e005000c03111009881c1d06040b1100015260b00d0f13080600c03000e01907030350817620308201081c0e41d0032140d0070700c0010f000c9820841020068184084044110202900b0005200c0c0282c2d011500c00d40000e00c4050303203a1000a902d0b502d101140b074000d508400703c2080540300568078407005c5941b09140394064207102c000b02c0028075070342c0d203044a0000c8510310035103c101d141e540e00d498040a80009401c40f0032008500c0341da204580b14441d010f2180301e9050042a00074504001e101c003e01d9070b0403041d1090b400500110001c2450b50009200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 406419964 1250 406418714 406418743
    0x19020a0e0c0a0207060315030b1b0301030f290f040c0803030109020c1209010e1306052e02010b0108060d05010905010212040c0f1d0c0c0601090f0b040e03040e18 71
    0x40d00d0308110b40090a080494001400749807402610340b090340c03080a54041500c0c5d111031950401c4e203420404117a0103647da00c130b01c03804860010012041009034403040080d14810b04204049504402804e00020b040c1006440010003100000300e040c22083e00030340c0c01600482407581220303112510541140d03c00d03000301d101c0d540c0000705000140700070095400c100220580c00381c1000b544100091000352031410051040340440c003940315105482d40010024000100320703556a400030750042901c41c403036004603003081d0200d120201c08540180610080480305940e5216150740d1b1030200180400710040035103d41d980d4242820002c3e000344002c000303071412502d6006480c6082e01c1c20702e0407680f00e604404000f01894000308801c400b074900007005410340401000e11a61940d4000245001e04038042600c0d00c640c60002030817960340c0d84502c00040201206011540106090100361610fa0100002c0ca500403c020814112032074080d6805c56000c4215200a90401d01c0c0c2d180f40003130500f9000e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 406421214 1250 406419964 406419967
    0x40206090d0c2c07052b0b131a060f0c030c390904080702040c23092d0d0b0a1b020604230d090305010f05040519020a0e0c 54
    0xc41c3c084549001c0e00c4a485901c41d090324007811808100841101a11020900c039000c61200e0702c0816040729540c1400259244511441d14588181c0141401c500c1d094060515218012154450742c002d40000c0c48968000c00e00020050781070008a0344074542c8903541050502180d24000c0040c0010b105403c4988010445446c1044408800184044440c8220351034140816107028502000c10031754482240c040c0322660300c0e81030945491043c03540096025251469084103250070800050050008202d21244a43c00700340f5480380c0c0c4144910780e0fa2100c2200b603c8840381c1c400081070482da1600c660800300222142000c0703040303134911140c1207402202006c200030045c1c20906c81c06a07598505200ea0b0300454407200042d4903103401501c003a03c900403010152044404100303040340c6c20700c0f41e4021a500a07545280040001e4041c0c0001c8504e9420300124010b1011940905406190480050a41a650b4440100080240300e008a800224a049c0002d48106a503c00d51042e01c02c4110113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 406422464 1250 406421214 406421219
    0x204210606060e0319030207091409010f060b0f0d0b1807110102070309060f020f060c04030c08030309071707030b071205090111090d05030d091a150d0b040206090d0c 73
    0xc038140d805035001a01080745242e000b15450780c000800c90303c0c4200b80a0001c4d80b04243c0c0c2002c900b8030b0002d4100e082c410b400c0c04c11282c22002c12008640c03080100c0c05c000c0080c08101038240c010360f500c80c401c08028050070301043ca4041140b800406101e42d40907000211018101d012034034282c2d1030310b0680c034050010b50401c141d454201d61203201105102e4005c61400b9107946d40600302403040d011760000c201c1001a00c20f6400e00801c0307008900d0014000300c030010f02d0101003e03219548140012075051001141c00a0880c1c8000180c0740034000e8000a440c1d02c0c0e0034007000c060404c414400c0d94190b071240d01c50020104000c29070007801011076036030f1802c2e02e0302c0e044903680a030f030b03005021000c0a80c50a58001c07103a8400d1020384080c01e030126081c1d0300f0a0701c84e0600c80c1c9140600000c5500385440c003425802005006420911000c10402000d40e80707a03600c2e41071000741d00386a440300380c01c48528821000019106041d1950092008041314109501140850544192070004403001800e04000303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 406423714 1250 406422464 406422473
    0x109050601060215040206070818040501030516050a03120e03031902160e06010e0f01090503160f0f12020105070f0501090c0906090605180a0908213106020421 70
    0x6a41303081c40d03000074000c0300e007002e5010442e41d01c02c043d00600115008580001e03082003408522402610040c82880f140d61241001c82e2108103c02481c42c0c2e03065024400261820324200320022030790050310150341d012502c10f082d500b4000440d201c0d981030000708510450740000365204602880158005d004100d40015601035154283d0401c2102881071001c020040ea88080d082008001c02c1c1c41d4035100460701d0005890310501078000c240e041c05904840c0710a4042d640780c2200b1542120403509001c0c0c0c0c0c411943d15030900d640540289000904200405540920300419056100c0c1d0b042d1003100d115500c80340d084400306a0211400740c1003100400000125010701c20140c02007117010040c031841c140000325000206089816112403007800505c9004c003541c014a4481d4101c00076a54408443c4443e002d035120401004040e6092400840c84203170044480291801205128021600d190b96402c0e50205c1121307005c0300e80e40c4c0c00b00400f18110507050314010300f210000144001420b0189030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 406424964 1250 406423714 406423723
    0x901090204150c080c0307030c050111090a270606050a030608061e060f06030f0f012c150303160b010503151311040207080a080603060c0d02160501090506010602 71
    0x265044a00500051051a41c214420396140d0b00300c0c01c00200d040424a07110505010f8544513528030f0101094100038907401110403030312144540004c2241e50f02030382103e8094002d145a40c2d070028515402448001002d0301507900c03040f004040f04003582c0c500900201914280c2d040800010008950310300000d0301800344102518144000e80785a1800c07424070140454541e00703100840c1c14080c003158043e112071019141c6410080d015036642d10b000021030710550b100341c50074440443c040000003140f0084418a80e00d09404005142138081080701518035034601034800c0001580c207442c01d02d00c41d94100010a0300480014910f04414120300702108003d60580c0304034081e8002200c0000031541ca058580c4d03211856055805062000c0e085c8851200c46c65880c440e080741c40041d5210030300c01c604010b4100b030788036641c1c5c0205595900091507290b440a51742d510340f0000521110f100400280c000d45501b9200c0300c03042030071520a84500d420b542c030b9107109803501d4008000600400340d0600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 406426214 1250 406424964 406424969
    0x16030e0409030e060703050904090c06120e1c1101150810020c10020c0a0c14040506030d02060a1805060f01030c0e151005090d050c101107050d14060c04050901 70
    0x503000c01810100740c50190600b41d007070b00f91038410200018214205030154040c3d070a0808041d208111090b032500d89020b5404141c0035410100e18250414803c088250003040003480350b0001500040802c0c480400e46110205084020701101c4c00c0c0940900209206030135a26118010b51042c0071325007001c075030908401c0350800041c80d00402c4170100c0c902c000141c28400c0840e02c24016130340e4100d86141c50500f00b150740018080302c044140020300150850084440321821201007040792296000c1595580c11040c0e044050380203200040c2c00e00340700e9400f40d50300061000e100b520300c100ba0355441e401c120045503103d445908000041c4148410100b100e406400040354580b114201580e09a2180c2c88031003403584a144040707074117901a4410001e0321190040a0644404124180b0341117446100a058143c099511600e481e22510700c95880c107624004104050244241810300b071051000204500380c03210385500e102d40c04440000c02c981c903c501d00001c42951a54100410040343c1c0340185d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 406427464 1250 406426214 406426219
    0x201080702030a1403040f0c06121406010f080405010b10031401050d02090a23040812060f01200c0d05070306141006031a0307081501170a150e0316030e 67
    0x80c00b0048030365400481448140c034511101c4d035140e40d41d600c1c141e0705d400142d000c000c0c9100e028400000390b0315013260040702c1b1903807440703c02e03c85024554603000740300c0700c21624540050300355010340311010301490300560401c1c09003001280d55281d01e008264000180501c002c0001d560700440400d20b108103101c14050b110450707400510403404e400140d519100980381100c001c1e510300c0000e100170100c0d0b18071801c04040785004411890581070940c2580c02070f003410035803007503d5000100c1e54900301c40c40c404c0f1184141c5590b25840c0c016190708035100782c02d0880100394818441d5620080d922110203002c4644164014138800d410b501d8908182c03180d5020b00d20901c02c1040620117020303080b018040030784006240001381c01540040c80d03a0700f00d054004481c1c25004100d400b042c8441d0104601e10044183c50320508a42d80c2c40c1840a1303002840c480c1102140c10100440c400a03a040403500040e0015070390202e200416400150f080d90f20810074008501404c0d900081056006a61580c2c0039404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 406428714 1250 406427464 406427467
    0x912051513060617070b0c0c1017101a070227061c03020307031d0901090c020c19140a0e0c0d06060807120506011101050a0e16061205040204110d0603020108070203 72
    0x43c142541d4400c0d0900806c0c0700703a0f41c0850210041801040050400c28000301381386400448010f0140004058000a1021a014000194082060240540403035420346101000100b40b456081c00c282c00c1030340c0480c2e020848840110280542e011950b89945007403a2008007800c0410400003940c01c12452055071021b041e211001103900401620700f070a40508110303a0440d641c1c901100c101d111120302503400321400c400031031801c1d80c503405403926110720303000c07111045134003010044031200d02051191441307100380050102d0701490100c076403000c8010303250403821a1541d158640d681011100380d0030300b600100340380c070f051030103802070038018506410f05120606004100a18041d14018050390541d15600401c90a920078041d03411640d0040c00208241d003001c4200e0000380c170a501d291501d41c411040c08a04444c406101031040350b2003602c1e103011a08942484201a05000348141c1c1e01ca99290f402c14941da15800060100c0125103c000440908600c00500459805040340045600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 406429964 1250 406428714 406428749
    0xc11030f18010c02100f120f240608010b0304060b0d0b0906060307050a0315020c061303180b031f051009090e0c03030a030b01120e0a060c0e0607021311160308010b030709120515130606 81
    0x4120880038117691101d0dd040da540c0d65141002405408200141c6030000204d07403006003804183e100c010301804401050f0b4049440700340030140c0d42c1810740246c0d5846151623104000144880050b022052450440542060b103080070032400c21008032078030050344001c00008403c16501800316266400d0850f6602da00c541800285d003040e01008140025806004100766046000421410001c0c00000d00c0c11a03d41802c42c0c008004c1480d6125444841d8204540040c0040001c1070f0040c400601800860130018840780482c00b810803881064140102f4070800800c050300303400741c000111f0260004002e20240361400a00f120f810062003020048961401c1d41c45644210890fa103180d0101c4da124403a07500c1e814008003c0c004c004542c510194001920882c02c1201c0070b650005a009407201e0500385e98503405450103200448422000504088090040d0861100011145401360303040750741c8042c0b140240300c18241c05071402c0c131030794040500c07031000c00026001d400054003011220300c06039003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 406431214 1250 406429964 406429967
    0x1e0c120108060c19030e030a03021201150203090d1103100204060e0a0f0909110612010e071409091f06020102091306180c11030f18010c02100f120f2406 67
    0x15902c0718032141c030108021310a12903c00c0c0c004108a80b002000d8a603184410b1078080c00950068040110080c0d03204000143d80314640403a0520701920f402079440c02104104009004800040c00c40f07051058042c0e224941d20b080040d24101c48120000582d15410800090000036031500d41500c980905d5200340300b541c0140014501b00c80840c180410408007910f0900b038a0040015466002500404c01c901c2207108204054103c030100c0c02840055110190219020030f403815900490680802003004542890188642c1c0400c0100003400410500c6040803c4842154403500060390045800c2c1e00501e80900060b845c2c200b0b80d82b08020b014a49188480d0040200b184000c0d0503968811805010b402040c5403200580e03140305403540c50f0b540318002c2c207658110140b0900003900340316000c101540142c81c01d00f14990004c0c082500d04110ba01d003150700300e0300c0071007841c1040051380d43c0002d03a4001d03002d41d400c0712544650125032020100020041e04001120044082110707000030020345 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 406432464 1250 406431214 406431217
    0x12100f1e0e07051003020f071a071704080708040302120109061a03060406020c0708030a090e070309020607060c0e060406080412030921050f0403050a03082406031e0c120108060c 78
    0x44800b41c40c0951150f1304900243c0083c0210307245900c00540000b1802e04000c0e8000801200b00c00c50042d9107896140c140c021280300020341034561140b58030310042004601210f0151101a12035007a2074078050304d981c0031406a941040805907669101d08207541042007900035246401c820750030700d42d030b1016044000b950b240c3c0040c0002e800ca55001481046407041402a54060300c442c80032265104000d450080140c02139203d444c8550400e40082001144680160746a20f0340007403080d801c0c00800e03112000104001e01c951010310803c9030f09141140c96110280c00204041c0e12142c00740c0c9414140724085000d40c140c8642018a00012000000c40c2e86030801045047d2261041940c80c46000c184d4051040c2c0340c8482100c3c0380031500004102d4000740f00410980710b0f5480550507100c1c0c003500b040700184489980d45040c04114807100c1418007001956002c540c4d4582843e041e040300c002c000444400756001100c0340c10001e201c00b42c8402d69014180104501401041140303850550341d20705 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 406433714 1250 406432464 406432469
    0x60e1f020d1107050604030b190b01050f09030709061502010509060708041b080a12030f06081f1409060603060c070b130501020d0608030d0b04050c030612100f1e0e07 73
    0x90040d075124101c2c440703604002640160402501080c1d549440381015609040107c0ba900d204805610b0301900b1554907028081244606071145400c1c000d04100030a4540c125810315034062090300d81c0010711030014002c40c401040c141c0000c0d040e0403020400203007503d10080160050760300c210140446030b6401031030717203a0160f003003070042102c00010b803002c401191782070b40444580d03c60303150010103001040c00010300c45205074804114a1541911038030517502c1c02c0c4165401501b00300c0300402d10200f1001d0848002c0c4620038002010031141c0040392052400303983c21062984010f041010b6410b04001651300201548065420200c0f956508181000002c060501c4550f200950000b000b100750140c5041440c01e00b1b0500c0400c0e210b00c5155aa07401803d100c0c00c4550415096032020700703191061030701848440c20312a117990b540c0c074140440c8251240f50000c452045204c41d0310329140610507a90305203000300c008110700e0000c800120076805050304c29010f0364542445000c15200008a4408 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 406434964 1250 406433714 406433717
    0x1022503020d05030f030c0a08060306060a2601091b05010507080d0207030c390f05091f090209010e0406050f0103050603070f0b070213050108030301120206070804060e1f020d 77
    0x10782c00d0701454440d00b54050740c0800c1012110110030b000080100d407002c0d2200724041d9540b01015540e100402d45d07140350a4445542080c00c0541c148002d050303c1c101c50072100708110600d20381204203000542118201d0354150b0701c849011004e400b0484840c4001401010240303025414001c0c161940c076403922071a212030032008e071b0020b0761a0070103016042410740345070040c19420307181801a050048841d01106a600c00d0b140b09003503110018094440d29080e5448040501c01c40c07402c0205100c0703000c1014021204c1044a94003400201d0351400760a4007030248070b000980c5401c0311200160844207041d4003544250b0130440b00b8080c0f030b1070b14a44514820000d00e03000ca001d0700c0380c402090414081790040f0050340a040700c00b1401018034401408814801e98910900c0f0306040841c0040b01d10a004d20365580d0410001003208a845414005029000801d118903007401940c3d1440e03540c1c040d80c8038a01180503944245001e08d040b1480e02040d282003582d6610709508034600941720000700c0303e0f100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 406436214 1250 406434964 406434979
    0xf1d0a060503120c1216230c150c0f030a02010e0318060d0902040c030903020f010203090607080c0408060a0f1b0905010309060209040c18091a0622140102250302 71
    0x19070030010007450484c108105c01c4a50780e4012000f005000e0303800913200350303001c1d07801c4906642c01d2101e1880141d00800984041c01001c040e0301c04108170f401c0798014841d5001c8080c0080d80c600702041c4040400d03004114021a9a40c902041c06400c0d500800621003060300300740200034541840d0030b41d140d1401c10494515580d50741004c01c0783c1c014982c40101a400c246043c40d00d178240d03905580b14040c0d460090302107401c01366030a10824281e01c02106d5a0201d50010000b2882c800c0c0952140b41c5c1107031600c403809081c01d4507841c115141210880c0d044011507190713018900d40303071103910600300c68180c40c4d40310b0360301200c48030406090000035104481c10140d55100035010b00481d41e05585c0150801003003032005070007008000f01400c139401048000090000350000700f0460301d108039541845804101d1084c40903150070091160050304d01901140c00c82d16042c40015030b01011840a484800514061168200300080c980b4200c11880007900c9070001003d072070986586a44411640c1c120760a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 406437464 1250 406436214 406436227
    0x14070b040e0a0f092a05030a020108250806010906020f060609060409050f010f0b12190606081509010614090a020a02010612080309010b01050a12050a060f1d0a06050312 74
    0x50003070110028074001286004120b1040205400c0d1810500403075040220317207400c84500c0d0003241d482a00c40c0e903a059004115140041d406803410507800755041c402d17480440702c00e207807414003c01c10488400000c1c440314200601c96820181290140019200501c2410008141c20303607541c1d0040c00f001d209005910000799550340e5030f0800c4492542c00400c0c0c1c0d0301d010900880354043c02c01c050011040b5420501034942c1c03420725a008001e9017070010000c0040201e02104180300080d07281041d2000d035151280421605e004014000c020081c0045850551501d845100d08403405900080c6020f042c2c1a4000200c1ea20100d0ba95002039102c9401682c0b0050000c099004000540c48200150786402455041c003080d070000c0d521038000000203000800003200110340300d100310100f02001c50f41f00004048403201a07844142c0c012038000b00014100d413030b030300c402e2030b488203e03840340060302c454504c0d849410740140000c9821038140c00c02885500e081400103920b810300b541da43d8203200360200b1311 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 406438714 1250 406437464 406437481
    0xb07021e13020a020601050405070c020307150c0b1e060f0a06140c01110a0e030613031b3903030e01210f0212070c020f0f040e0609070314070b040e 65
    0x1c010071800c07002800c565501c003081000c0d4940000744160761042c0d1500380043e8800e0f014190800e0700f1680280901182c9080c100680200d403116403d0108015280c1e0b480e000003011500414080d05540f01080b42c00303045ca10314a041c050001701410f01802e061005806d068456020f130a00b500d41034240762030036110302d503407120f0139001d0096240000c0d828a541481e2004002c0003e19a60203075130340c1d426550031440141030b41c5080c1030f14010310031615050040301091003078035078682200341000840d0311411240c4070002000d2825541d100d07112010f1400c03200c03031180f0249085032070f00c541c100300c8400d901d980c030082e10016007052494103210141e01c02c00d40722040034800801129400f00100100c45003031104034000e40200300b110306548101340c00305075442d0143c5000521141d00030440c2103000340c04024010842c480325200c0c0e40081d15000b1025180400744012842612031400510b00145182000e690950590141100d0303600099002e00401114008035015200700001c4401c0503104da030712 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 406439964 1250 406438714 406438729
    0x9110f120102030103060605010f020f0d030b010e030d090612060b04050910081506010305010602013602030a061a1c03050304020d0209040309030308010b400308070506010b07021e 79
    0x3055801548004000b004000c0694480419100280c0ea81c10400c1203141050b6038810311050102440c0d8007000ca0700180c5842504200345142041c5004d1046d40a140e01003454031a1566412001c00c0313801c801407010030b5210040e11000030a040c81400850b00d01101c0715428031943c05103e00507540d80740000c0480c410340c500d0400800150049032202c4041244e40d0021007825194240001e00b03050000a05500c14050039003a6000c1d040d0b00e0310050717a034514100140207080b00440d402003122151201598090101c0840e90b805440080f80c1b01503d240010600151000c44c54403403500c900309105680d08515854842a03810304001c0e5032a1218000a110403a1094000f035001051108110400d644400c0346421a4880d8854101030303600c030380c2c1c8014603000741e9000007810f92200443e0740390035035074258542c1618001d40b01408515120720704641040c032581c04c02e58212500288079010801c0802c83c2e103004001c08030b00b09040a10365400590ba840034004018017000b00c2c0e5000e812203503030b680c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 406441214 1250 406439964 406439989
    0x140a170705070803250e011b020310020c0703022404090f0603170912060105031f0b030307051e03040e0a020a030e01051008010e0303010b03010b03070c0c06081909110f 74
    0x100284d26890300c46959442d1070103502c0e580505081c80034002240034014648140d05c2c003016166242c407811011010f00b204074500100f641c2c140728004e0030380b4401c1c40d41c0c4010029109600b001d0a20b281c00c40c01403100342c5800c1c528031500e10604244000c449079142043c1c50545150850208508244005800c0a17080030342000d1710141142e10b800409142c524010703c00701805032690014aa105100e09840b10f00901c11682c0540084d06560310341c00541c1c1c0000b12801c401e40c0d00007001800280401d20356000120225490f610081c0750550502c44c241024540110f0180110302d00382c14241d0190061102a0200c0d09140e0045843d84a060090300320000241c4910000c01c4140b80440c0e4052003640c8a1040c0001540780c201e0301102000d01008490699003030300440c3e85036903e0801d0600190380002c003190708100c20707140c0c07441c009080b110649005000307550f104002800d080708171900d80d501e800c000c0d8189a140031504000603099a11641c0d05140c1110600c240c8581180854214860746 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 406442464 1250 406441214 406441223
    0x50a0908030f0702091308040b0a05132c160f020c130609180807020f0a0f060206010f170a06020a020a0218091203100909020d021906140a17070507 65
    0x2c16604030001060780940700060003140c20910544a0600541e2003039081a0081c00460080205210b0b82d01034070003c05401c0107618085140034900940281403685a41081800004010f6020144220140503940d28151a5018100c50414145940f80f41c81d41c48419030074000402503c0002ca8002d00500c4138a9202034500c0d0410692011110010b0009004000d070041ca4101080e10210860030032030071142e442000306140410035000c015030034a0800c3c080764054021000828898400300c52a8020500c030b40040c5460350502c420440440c2d0305412003541c41d0400c010041c1c441070000b410610b540d0b040000147c0d038240d16101242400c10b440d4010390030540e1b00787d80701c00303542c03012803600e100d80c00d002c007075a01c0e080c21034144441602c0306035184d1032000603103242488032106a03480203590b41d00c003d1404a230b03c91141c0c0400d18020804001d04c552050140d030030040c440c2c01c14551680340f070b190203400d441c01c031782124042d1050b038922010785105645031b000611190301807412501d280c1d400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 406443714 1250 406442464 406442467
    0x6090703020409050f041205070b040b04020a122d05031e04090c05120a0203041a0703061a1306050301080312060f220b0a05090f0402031c020a020a050303120601050a090803 76
    0x83c5d4158050810640b012200341050b1481c40d0482c034852800d0b9003c0561144404c0150b072925129550a81c0c000742003079901030104800000c08210325010b000b10148180d07039041d542d0f40403c000023202420b802da02a503a00003411140300056001c02207811588800070600c0f8240c00c00b5011855034002e81d001500035502e001070002e00142c201010b040d04c001c419035001099a50360030640143d01040c1c03401406124000384000307046145103001a800212841c1c00070386103681e01110003400c003c00c482030401502c0001c8030306803071f56256041c0c00605030300c1c00c001e071965242110f207995034030441c2485003545a00c10b000c03506a5891000859031508001c02c01c00d00d80441c0d03005ca0402d042e288840c1604145050030201da1802d0036040c010072154018030240c403a98401c02c055035004030091040381c1c0750142d1003400b020942204070804015100b13900170200c08169105002d440d020b0344d004184654014441d450200b08026107081c1e10007800c2ca081c40d107809100d030b0103951240c40d075000790055000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 406444964 1250 406443714 406443721
    0xe010c0501091b03020a15020304031203020c031b060a050127060b040e0910061401050f070b01030c0f09020f1911010204081006090216080a05090301140a0b01170609070302040905 79
    0x40c0301a0b00350940c2c1c001c607170112945a40c7c00551004002980e0301c8000350304180010000300744111f0221005148604000d8540b2601408030341c20341d401201542c02046090a44192822080020700d500001c503810401c81c070b50401d00c0300c1c0c4c0e00e840902c080340d542e85c99030026a00d081000d0f400c984005d00300300f54a151519241c0c003083e0400401201e003602288641506582d078254a8081d00d0200c0e400109036500d0910340500448256201d482c0700c920020007000620001040483c1e000d0007540140148407040c0d04010000c031446110b60b1045007014014005840c024038408121581500c3c5a076080c03085420341c0e2801d031103003482c0015000c0320b544040f0300040d038803101103050701c0040044501002540d803540c1301c140c01c90080c25044e589040b0817190120015240100504030b8400506200d400e00c0d400f032000070300391180184960110400c1d0410311419009c00d00440e000c0b0b40003404d0008184030100b0012074181c0005051354416000b440100f90400d02940c1241d010300075500e024803080c03031b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 406446214 1250 406444964 406445003
    0x60209032d0f060f04082107031a0303130b0c120a050903120301060f0f12090309090b090c0a030908280f1d011808012c0d0e010c050109 60
    0x100341a01c1000a0040750184000d080700071030740a10558000b003001010b62925190700c00c02d90070079094140310300c02c9251080801c1780d16085007841454159008541c1900e044154031184901e0417080340603078818070030381c072401081d00d106c14181d4141182c000e484000c4104003c0c0b0b40500a1500c0c00c00010014010340900e61000040200c0c2005400301c0e80f0141031002a221070b44024444c80b00015000b0b0030f03a00c02103100c0c1c10290380c40c0009103070a0445400c100000c00c115400c403001100890b005800c10020003410740034958440b042254003e0440c54040d00c3c0c2d010a03c00d08024200701036580ca4000c0401c008801601e645200c0307184007950000c0951030700552000445100030220305105800c0032214454080101517050403200c071047c480c0342d00019140c2c1091000102c0c81c1c0c1034a40b80215014400f44070343c4e56243e0782e034100c1517417201085d021144160640c100c11900d40e08180e0b54140ca9640012580c5444402031a02d10381d4140581411801010080c4c0001c14000b090700f18500d03980d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 406447464 1250 406446214 406446283
    0x6150e0c04090e0a080a030213080706180803160f05190807030e040e0304090e030904111e040e04031b0213020307110304120b0907031707060b04150306020903 70
    0x9880c0c800e802c00c0110f00c9115425902d100481009001e403204018041499109402400c146040f21203055505600c0391801ea042a40f550001030000e004105290741ca9810026800014200d884c080c47ca011040715484000b02040c11000e4503c22242c0030203000c000c410806110500d0344000300025008183c94801b00075480400c06030001150502c1e00071484c5020700c102034022001c43c4c01180ba2514000079100030b8044004103440c24007092044400d661110300645100402c2d540c40d459668414808204030030207690086503944600740300600c214049507031050b406c16014105019503000d10360700540401c170700c028001d40000c00c2c10000c00300f1850359000342d802a18262070342040f01e01e641c0345682d902d000303500ca454080c01044410704081103499004a40000840b4152021035449480f40c0214003140500700c0f8042c030000a089050201a210340344030a0030441d8203222420802c441035000c4100c5010103040d8550001d48254190780c10001c03100250038030240d0041d443c01044070303603e81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 406448714 1250 406447464 406447469
    0x305090f06071205060415030b0c0906190306150f031107150b0f0d0b04060902010c0b070e0a0f060221091009090f021608160f11030f01050601090306150e0c04 70
    0x700f904101c0070819901d098014032510710080803064100624584820f45a002c01900c4a4802601000b00c000301d61940402001160072035080c91b0f03082001c46000804480503940a01b00111500d00015075407a409045c071100d07201c00d4075001c2020308603111110302030312901c032004120103490f840030f51902c40340d90042c2d008030390201d036032090286842050140c00e00c401880200703000c202d1000600020026840240c00900605d814000200e143e41d1f40058081e00b42d880c00c2c0800d841c58500c1a4600c2c00600309009800c200c15584030b55850300d0806941c9428152200b400620780151010043c1d403868180c0d00c85100091181032a0707480c9200141c09034040c2c6c042e000c0765500348102e581c071015850007100d0008000caa4411410611030f169001d260b0004003080ba522440c05406c3c20201d900000304020183c0180e5000740e803190104101072034000e400030500c0c1d241e4109002c00030725a03000560712007165000200032882d400c0c000d050801d03e41c0c1503004100d1121075801405000046103018000703 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 406449964 1250 406448714 406448747
    0x50d060509070f0306090b0619120c0b12011502030906070b071206151409030718020f19020d0815130e01020a02031c0b0901140418060e010b1206070305090f0607 71
    0x629108e04041c0000c1824583c2c1c0700c83e0403c41140d040046505520928840c03600405039003050648500c400c0401d58089621011910703841700050222462401880400c410780340010f52070711101c400807684600540300c001d00040c660000043c0010b00540040030001e0510500704515510b44240d40c042c07403241130300300000031a8520b01a04800e2107104580b214a0001d00500650f860400d4070400f00e04103500400c1c55030307000e02524121345425809040e0602200300014203403511204000d01d40158144080100320785041844207040750f00842e40c140300303003d54203211600c0e08401d003000982080d4403020390561000401d04c2d80b46a000c400362010101040078030303010801c250a60000c0e0f44480785510361040155004114003a4441e03030401608001510208840e108100005c035101082401550b410385c568800040c00c0301c0030712844c0c40d6681c0c200d41c100500300700c07404001d554040003400441030540d1400801e0942d01c04104015803540d0b020101d0b100d83c500060000c0a07030202c2c0011a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 406451214 1250 406449964 406449983
    0x702031305061c050c130801020405102f010b120c2706101403040506010303120903090504090305120907030c170319030b0402130305070f050d060509070f030609 71
    0x5a1480c200040f505541400301c0140f01d21040c002d8400001e000141c07075102401c100700912203800a1881d4910000c1243c8400161160318000501121010501d40781041181c1ea000d20840c0301c140441038880030001d050508100400c0344030740b60040042050644c2c5c032410070080e1204031200011200040b80080e0346110980035110f100d4080211000109488603003810700044450030b2605400400340c0d62854113880380340c0c1c0c1103068074141d401990141e0f2290003071070040c8149a0080c0220f90001c0c035010301006401565180189230410070b02503540324503140d11085041c184030710242c9511184107050200c05080902c825541c65440d40700c1181d145010131400607124240d4403a18181c3d440784070107076140440803602480261706901c0008141991892681400c1e12544007405e09042d400d0019005103065040c510f280044503400b2100c0810260f03003e00c00c82e04c1d11010340e00300700e41c41407000c501c0f500e4803000d0340d04000043d00803104184180c1000814015a40c10401d5503501403100007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 406452464 1250 406451214 406451219
    0x71511130f0803160605060321280c0b0c0714060f0a0614010e0a0801020a0201091103010903022e050f16080603120a050f072d030e21010507020313 65
    0x56144e019005200711240f5220038000080395850f003050744e000c04004c0036030f00c9150400710f8600c124181c0034107013a104280441d00040d580e21109080908565010b101e040301c3c8121407000f08000320102005145021503c0429800b44144080d0b0b5501584034003d07403580701c440a03581e0b0f034401c8111074025580c031100e00443d00c0d00c0c200d84900d41c00e40c1c030b00f240800b140c9400103005480c0100380740509600215821000152102d0a20103095602015030003c21072004608015800124030080d40b0710a0740741004d07800010f0b40001d100429102e419a84000681424910080400c01100c0c2d0a0b043c9040c0810000109111081284254010186100002e082100032940c03a0320071294aa01a400840c1100505081e50050f1840880c070746007142c545a400150761034103802041085404040d0b510181c807890070340340c40d80c009070000300440d03074800484c54038001c05100b400025980036942400c6400d03400111a03801040112440b4000e100e2401c3c10200295298441540940c8080440c00c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 406453714 1250 406452464 406452479
    0xd1d03190c053003060f1002031204110f0301022523010c09120c140613030804050109080f100207062d050c121503012d0b0d0206071511130f 62
    0x2030b41e0007180c000d422046040400c009107c3d0340c0c0d161404010551200340400042500040710641c402e0340b10f58107480c0340c80c40782428003d0012903401024400c1e40140300c04a217100948140041c8000d0f401c1d03456004403580e0405500c0b01e40384041018070480c100d0711401a010054101416032400755844ca0622540d988100940d8643c060300104108400a070130442e00000c051112003c0400404071454001103411600c0c084925074412181603070040b034208451341e04154448014805000030b040d0704030150082a890300421840c5084643e404140702c002c2c010070340c0c411501900142c43c4007640f078481034001e0a103d50030b8050300940900301301c0000c441c02d12050603191009848042c00416071160680e404221091540701a0999a06c0100440c0e035000c900760001140e420001032100d81c00c040000000340c41d0064200d42c0155a000c40ea00d005880b543e044400f81500120600e0301c1da9940f0303941f80003504110391149035501d4041140080e0b0082402e41004840d1420000014255940304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 406454964 1250 406453714 406453717
    0x10b0405090114060a0c02040b030a030c11010503071b0f080a08100915060305310302060106020c1f0207050915010e0a0e0c070c1a0d1d03190c0530 65
    0x40f026000707481407054901c1540114a501080c0e07200400c007084080100740800c1ca007442c1c185c42640042c588090b90020b019050034485010300080c6012442e51804010160411982d8089205002e80b4020110140300d68208540d440d540d00240309543c8036080400145881425a038007009404145d40c000b07005403840c800c0000c1d0300583c10a10200707502e0a40150028500100700d0b85d01244600c29045a0702e10803a02c840d54110784c903c4081c9e10803400c1c00c00900e0450705800c440155404010002c0069072411603041020410461142e170742c24030310030124100305c110740c0f025400c03d06034002c0c0a2080409031301102044000c3e03a0b010300c40910a82081000da0003071081c80302003145d80011030280c4040318010410180142e2441411550b544024040c095155285680500011400020319845c4e4011a101900f480c50401c411902c1d070007415440b8422660a0300001c07040c0543e0880742e5000310000c0700400e8000342555481004d032146d0a64095005045480400c40355020404d450499030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 406456214 1250 406454964 406454999
    0x1201060305010501121b030e0705060d1509060b030402040b03030c0f0d1403060f0f150313020a120510020901230a08160906030203130227072109021206010b04050901 73
    0xb06e062102d20348803241070b030040c00c40309441000c03401404400f080e15224400100901c202040b800640c001103194264400070090300005999800c03d8020411200c1220650b5082901183d00141044030140082c2c42c0d4440c2e5880d0799101d0041c045901c0d1104c40204d000c8401e58456100c0e0300c000c41f8001044c0c102c510048454a0b44200d81e017101e45402c4c18607101804454801030175038078544400405890440d017040791104181c181001c2e40c2000c40c102118200e00030008440c2c580b60110155070303090384510700c40c500710089a902040000d02603204231104c00b590800280602c01a08444442000d2940000000380c0854009000300b886003000310151f0300e90410396a18681340605042003107010b5800a0014660080944062000759490005c1004440950700480c21603039028520100b582900074424424080048403c00701103542c02203201c1941c814400000f921142840000d6804030220170105803407003004004141015494028425940122002b003116070f6582000034020040c0c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 406457464 1250 406456214 406456241
    0x1406010c051b040e030c01050106020c010804050606090a110a03020706140c07060f06170a0b0604051902090303070605040c030302072106050901060503240619031403120106030501050112 82
    0x10b0342d40141c1c060310080b08107080c00040010401c4c4414070412403441d0003064240030265501ca00400005404014080c0c20321300c00e0070203000901e0079480d500e4407040c000b04181d01801e44e60001174040c800c59481844051791601d4031540b2680c800c00c00030001d400180342111114681402c42c442e00001e0f42c903240c4540514807406180847d141c0d00c0f6006021258a94014103031628004a00c45030990a80c0d10104100c2c001020901040c3c10109030070709016007080d005900c1e280602841d0f02e41c000110f03144c0440130101681e01c01d41540428694401d03864058442481e007011310040080111840080364001d900711038a440d104c955a030b040307111400340000782124040c40c03030300080c06542203036a101d10139000010314a41d4403008241811528240e05254a100c1c110100d05611407802c100d4110750141c80720842319041c01441c081c5400c85000c082c080c000c1d550140c0100c0b0804104071080a1541500010b0301e503074411001c1c001c0c040c00e006050100d2400308020b44403080300d1083c070b454115075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 406458714 1250 406457464 406457473
    0x2040c02011a041428050403120507030b01020c12120a0c0c0b030c0306090a1e02030109060906050f04240806041104020a020d080709030f0503040f081603031d131406010c05 76
    0x54070201401041e80e80178002100005041180d02029580301c1c0314850f5010761158082a242c2c0745091007100c0d4000c01c49401c0c07500c3e1030192045664009600c04010742d054031806090480c0780102032520320184106292240c1c0025003080559202140c80a07003803052100c40034803901c0d000f451640780011294034000d1142400060168901082165003000110200051900031490710411103500601c0402d1503c0e0000010048003560348107090003410005420050306050000040346501d030344d006640b0468803800300d01c203110569a12000d40e01320b60500424055940c4032040e46800084405803220f2600240c100c015050500032151003c02590240420083e0001c05550100c80644507408003c10440c1c080001001c90305500c40c0c980c0100001c0d502d462401c00280c2c1d0640140d04020b802d0b8100c862a2100d060700151002c080c1d070360508010390072011010340d2840310b10350310104c40d600880f4200e40400c1d48809500c04c2903030390600d144d49010b50b07a9510041d6107090070307c940148690302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 406459964 1250 406458714 406458721
    0x2021030f0a09081b010506010206130305120c1b071d010608130302070519030605130201050f0d180609110a0f06080c0d020415080901060b0f030a060302040c02011a0414 74
    0x190b480024a540700780101400c1901050804c05010042c00391180d072690b48a050112071741e010030400da4840ca40c022103554070010b03540c004000d4080c02217000e5204805502288c1c3c0440a00281c84104540b041c03040100201080e14a03510041d03032241070f1900c280c04185c2c0c14031608402d1018141d40290300c07a56141d40701c180003203041e00503400e000d40c02c50099031400b140702d84d18551286000000c03107a8400c1c803981103003000710071035001402c000646140360340300c180141d0f0407403341c0b81483d00c008002900c500c0001c00e0600a00329268820713524950a40d068010481d442e40004a030350b0040a80c2401c044980742031100445003406a65200d25198804103c10b034440c0c0c08450b4070009120140e810404012010340580e00a600584c60b944130319038102c0c5c0c2c2c5940c00455142e0024504009000692408446007410322a440080c0069000080000d88000355070b000480150303800b030030400911100700d80007402040d40c0701c0c41d00c1c254210021140030074541401500c561200410f81b402058a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 406461214 1250 406459964 406459981
    0x62a0c0a29060f130e0303010b1b07060e010807030902191d19090510180203060c03071707020f0a11010e12060112031101050c09041d1c2021030f 64
    0xc84d90748240c28503034503445108010300c0b0a1014600030204540e03040d880da0f0194442d10312100701d420400c401644011010000300d41d20181300b407a403100c00c0c280010b180e2280309044003d003e40c0840a502b1114000207114110719501402080300c000f11800c01320840348045841094400f0f65100d24105141001d00140c03400301e034888a0003600c180101c602c0300f001001540c0c00d03148001e0031031041c5a230401784042541418001c0590058a601c80b20b4907600c0c0500f405443c4503181c0251030401d0b10390300c000492081c02004690b010806d15070448100c000b003891303c1401c0c0c506810085001401d11030090023b8101000302c40e9a09000d00f01814507a802e000c118104100b00d80ca09404004c11841000a07a18007845180d0142c114890321543d940d0140c0b0604c4140e5102200384101e80d07040301188145843c011643d034054440001b040b070070390070841400b144c07074001c419030308920302020035020b903031017500064942859a412203151041c803205c119154481d010031509100c038200300d44000b4020a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 406462464 1250 406461214 406461229
    0x709060201180312021605010605040b061611040902040509010605031b0105030f070903080f090f0109031a0403050f123403020a090f030f020909062a0c0a29060f 71
    0x818130740c1c03c01801d0003541c50f0240020001c0110944003a55251014080c904050040168600c0161001490098407080010034001c05030700c0901201000f050744a61642d541e04400141c40d00104140031a08040c0c050074000d00340352003598841d104010401c203400484001504422205031601811540c5da03c41c800540c1c540202072000700711141c0400320014981e2405040c1d2282c200189079160681c207824030080b01d040f68002814040d02c503c00300b0010b150f00d02d500b07a100390240280f0030240c03154a000d840e02d004141142c00f6901d004a83c0b1070303607004001b4405102d28030452520340c40318074021012003200c00034118400c102010f001040c105034042d40003865080303c2442e20344103075690b8982d50207003101507410498540002c2d107407070415440c00320405034002079400050161760404100d2286501184240d40c004007100510040d104013600b0251a8010211810366540c0c04491405010a044070188120090890340d10b03164000000807100d40300d200c0282c90324001181200400003031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 406463714 1250 406462464 406462487
    0x15020a1112030a0801030611031003021216140406120305030609040309050d060e0c0103140703240305010204050325060e13060807080d0302120109051e0108030307090602011803 78
    0x1c00c10844216010728410001054810407075503c21419506500d402000d4403080036410007400320030700c00e006c100a501c241000440347d0440e204407400c51440d44507401e14003107503000485294114800038103904030080400340e02c00204c80c1000702946811416596050750400500020803d000161690a12400e1030390410b000782085101160b80d6030000b107840b031941e07100300d414940343e540c098440d003810800c40440c40d030709080c1408844840c903104441c2d084010042c41c105a2500c0c40d440c85505482102003a10401021203040c0d10340700d00382030707003c1c2d4405d1082e10301900c184010910144508001e1140d41981e50040341062481d0179011142e04600e070440586c0001c50360030340300c00d40d41c13a84507120041c2244409000310300e1511031f512b0700300640c16001805141c010850910f8254942c508541502c100000c0056a91241190800c115600324180300c042c03907220303001050320b54000000d98851010703903071140da0554a80034101e083e104101003c0883c000e4550f010ad000a000c0c2060300716 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 406464964 1250 406463714 406463719
    0xc07050307180b150f0d18020108070e04110f0429041a0c030a0306050a05031f0903110303070c020f04060506030f1f06230306010504030807020f0a0603020306040615020a11 76
    0x30407900040c01032050794003280d40d5802d00c100004d418400d140503030140c4400781f000144a181c4001c900d40000e003202c20002c1044d820804215681d000030358403648102001141d01100d1500d40c52017000e0480294040e004401e02601245d045001c40c25182d46010494032140c03070014101441c1c801903a84d195011500d03da00898240700d8210b07448001c101070082100580da0100320280f03003005122580483e500118000d40100000408900304101c141d00c6c0041c0400f000241031400e8181110040c140c00c00b9581240800002d00400c03550000340700d1516802200c0c41c1c504031540c0400c20040b100c80388901c035081305003070000810003070781c00c00c0340c551011100c0c44540906580310b640c01c060030003541107100414111140444001100d509011030104c0c00c1d1610b620f18100900060014003403840018100180003640740c00310f444070401c2c214401c00c00740030a070520f51911030160194100f1120140501e2810800041020b10030350310f410600d042c3e8025011020541d01c43e0060742040305200c64 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 406466214 1250 406464964 406464979
    0x7090603170d09080309160e1e040c0519090b011d0f040b090c0c010e0606010c240203010e0403320d110304380705181002030c07050307180b 62
    0x2400300d02641e005510800b6507202402c00303c0c80840410280c0040742e000440c07140303023400401c80300c0c8094130f0101c659000c00d1031500356160354520b0800e030f0b030030034681005400001c491003c1031818415a90032069482000c4240f06000c480320046890101381c0f410503c0190704402180503c0c20700605d00484c1c030340c0140000c15011048008141100419035800e41c0b49d20000403070403002a0203200b20b021240204000d001c2504164000a00c80e2a11510203080151014501222a002072986042400c1580790954880d0f070354189108850804881c185d004c1064202c001045109100d8000c0349400b0315071701d08402040b1014081595080801c140001c15601c0c29000102a16000618071443c4540409038a42e4040c0d0846000c80b09a4144c00b0310008815441000c01c102d161032055002c40c05140480d01c8140301c00c0070000c24208455510742055283d0003281e142d0f9800300041070304060840445401c56076610030301d41e42e0040e070b00c02c4500740c100100381e0900c00d0740c46030448101403100800d4038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 406467464 1250 406466214 406466231
    0x302090307180605010e211501080105040201080601210216050102030906180a11010c060b19050a1a19020307020307061d0a060c0b1017070807090603170d 68
    0x64a0300d8001d030010742d07040c52110480403400aa078001d52001e00002c5c070f000350500700b2400100d000041c80b80f121015044408007c010107160800140b05036105030000035500b540c3d01d48400340201400c0e98143c0c0055044000100c96500510205011580011a03240d00d00d811018240081d01f105100c52880340d0b486600c240810800d0001e980500c11041c007a024a04250442c20002041d0100f0003120341c01050080c001708460100e44042c7c00000e0800d220281c44902d070450040c8031180b540ca40c01841c5541043c0d984000302500001c3d120183c40710540b582d00c80d580d40320450502c0c03141859002082107200001005c1884066450718640112030428000e90700107414031845800c480006000c1440c80e80701d41c000c8480d50423000d00d0584030646021f0820200920725078139000c01030405a00500891a45280a1042c1c402800700c00b142803480a4400151034031002c50340f082400501c10f440c8042500011485241c003100c1c0d00c280c5110703014045058100c5103801c600c60f0103200030b03510101c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 406468714 1250 406467464 406467469
    0x90302031b0f010506030106030206070b0c0904020c03030610020304140613150c150506181305010203070c050f0712030c03020f1204090509010b1309021f08060a0621050601030209 79
    0x7096009405406000960041e034a01d6084610081c2014840d0307040810420241c0c0341c020484c0c2815400c0201c64486035942000d80f62107104500c00550480e20004400900c001301002440c01400102e80081c0940362004e01240d4a0055000c0c0c21546c00a10070310003810b00d0b08100808100c0740c1c403040c44070032a41d148880581d85054955801c0401d450541d0b440400c42051400004210804400c1102d8149240810014100c01500001143c0b00b034004c510b84083c80c00101079503a80c4600255500e00e8144c00c02401002e030040100e80c24862154050b005880200b02e500c15122005944000001030b920304407a00703180e039002a030540c02844160b40c00740500b0b104821715604002c03002e540d581c3c43d140050044a400a0072003001e42d240661443d41ca07a110706100c0e40004000d04085003541e0fa90002424100302000004100d00120b22003c1c00b054011446500c42c0d442100e01800c4603544000039612a1070a89021000d00c0c507448001c4251280d40d40040d40002042c0340044c00d00041a01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 406469964 1250 406468714 406468747
    0x2011d061c09120c0c0801090b070e011709010b0f0405090a0201050f1908041a0f0705181305090d140f0d06080624043e1303050705060c0d0309030203 66
    0x4000000380d8003541413000c0c4500d083e0400000d1076004000c10013501030381c41d29451140081c16410401280320080c0d50182e200d1560400c0d03043c0c10356480781480c203100e09428000c080d401c0303500380140e09940141409e80345c284209441005400d02804131400e5950044a440d440a0320081310064240004031070b0b400d419502d00e400301e0b05c64646243d1030425092004000720610584101400c003481002030040f50000c003240c0010050500c291544101178080039694a00700e107031038210700c846484814400c0725030455030140b1b81a80a07101c1604020b0700c1180c10140004081070803600c100144101514828010020540500d8000418a40b100060703401d241c81540c2001ca0110344100c00e0510030b1300a030310a0b60301c4004803020816003031801440440c3e0880684a4203480c840380d24201114010004101c80a0a0721001140d5034105c1701c1c082c078440e10150109035118482c030b600103e211f0038401c0844070034158100043c00042011101113000d0407094030103c0460005102010a00305902c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 406471214 1250 406469964 406469993
    0x41701050402031c0c0f17161e120e0f0418020907180e1506130618030206070b07031d03090f090c07030f0507021c02011d061c09 57
    0xc106820180101440e0005804c40e04031560006146000302c4d41e003091400d045c441d400095200c107003134241003683d840300c400016404000400a2515442001b20280090080c85601c0002e5000d40c03503a1250003034800040001d000450150b0030040c0307140128030701000c506004010706948102d07000803d0547e42840b0081c1401080c4588000441c83c100003a203a1040c1c0d68071f00a40143d640945900c0c0c1c4541c1c1e84a2a1080c49800d8046203044407140701e009590f18024000c6507031449041107aa002161910680300003c8000781c4500759070000d20b005030101ca40090900381881100d844144507c0310241000c418141d9501040c0b0462000c652140d0b486001d2201464846800c501403004403801060000e104083c0c0c401005501501d000551318010f800d8500130a020b41d421006852900c100d0324041e600c0481c2d41442d2200041344015882403501c01c1e600c42c2031142c5041180444908a08901c5034007400501c480f0300007544440c046181ea00745c00710b010030a11080d480e52480c1c0504407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 406472464 1250 406471214 406471259
    0x302040c03020d0b04090302070b0d0f050f090f01060503100c02030c011a040e0304180905070e090303041a090c0f0406031b090c050c060726150102010c0509030601090f0204 76
    0x208542e805005581300b000300840c002d03201407107078001540e4005c1d1a03605500802c20108000b050718494108564000d024500380b903030382004070342080c3c0580010103804131442c0d40c4c43d1143ca00c004140c0c0300c1c18040d81c0200c034005402040e1448040c603500e8054216800c85004500c001c0c050440d01d600d00b4015400d00c4100304807a5201d01040300240004d469000c6a00e81c4aa441000304000d0710f40c2c1613040710204e500d10880043c40c89020701d04281040384544c03151300203031034080a2104040d00400254015442105019070030240c4012145c403d0800325442ca203d600b101500c904d0303508004c1405100a8801000000c19a4407030b41c8107144502c41c0396031040c9814400c4014400080381c0d119400d003040d000d00b040ca003400f5180800341da4490300244820100100300c1c2e81c0d031241d0244000c1b410303280c584911049540d494820400170520045420484c01517007441030300007503070780911304031102c0d208060041c01d2241e0071318212102800e2500c210741d0016600700301c0014206514421110b000510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 406473714 1250 406472464 406472467
    0x90e010605030414010518010b0d0201051b03091305070e04094103130806040b04260d020d0b01080106020a08090f030d11070b031e130c2706031109100302040c0302 72
    0xa00b61a4211427610710928064508800c8200150380c00400fa2205802040c1c00001c0b101c1c4844111070071402a207a8444d00300d17411055803644800310381c0009101300c4850755001403880e103140802c4250781d08210041c4c50385c0c0c640c144448500410000f20804c0c0040000340c500100c0c1104030481c4d0981c0030b58194002c0d0380001c1680c4043d004600a03000090161038014551070901d511603000301240900024640e02036070000c0103d1101c1142e50b601080e02409100ba200e0f8014241e41000c3c1d40081c003003c0302240ba05241c4461503000d103140310b050707603543e5000b000d44c502c90740e0703c4044503403000c401540e1000c0c00c40e010860f60364082240c005002803603a24601c2500a8020944c5000043c0d002076141e900b06004029407500b100800360f4844081451548454685541c000302d0030105181c040c0c0110142c180100d842e80f40b03030252100841041140f6411280020013a10403544140401400e80a48030040d001610301010400d801107003454111141e65900c1d4001000c4a810004203004030f0740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 406474820 1106 406473714 406473751
    0x321050301230d32030306011b0804060903120807020309010804060212090309010e0603060a0302010c050f100b090a09030c1b03021908010c090e0106050304140105 72
    0x20308443c0308950181064001c0c041c10816488000080340300c5010310030b118240d00d0752031100c0d04c0055820364840b1001158180d410040174100340d10b40f410444041480faa000340020700c283d8442040c202e26514064454494050f0200c1c240003014041000b880e03000310840300c2e031071002d1810340502e42d503e240180003405442c240c50080c3d0420ba003040200d4000000600220000340ca6482c600c12065040001c0ea2204483c0b46030450003000707003080194001c040c50b00301644501c2c180c0c2d1181d401004c0d0305280658103442e40090a8407a01d008042d8101022682c0d00a4040740c0d0900c1410120b45010b044421102d00007000741030030380c00280050180f000030401565000345035182641407200c00b146c00b0042801404003a5282402548400f80108190400c44002c102c5006250b0b1034400180c401ea080200b0036160700304408445a4001d1083c41040c0c481c54110505031200a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 406294964 406474820 := by
  have h0 := BRFrame.cov_init 406294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 406294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 406294964 ≤ n) (h2 : n < 406474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
