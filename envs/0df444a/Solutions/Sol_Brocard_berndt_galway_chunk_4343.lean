-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:18:53.357173+00:00
-- url     : https://prove2.me/submissions/232d868c-0050-45af-bcd7-ac14b25a9eb2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 780935251 ≤ n < 781115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 780936501 1250 780935251 780935279
    0x3020a09050402160b0601021906110409051006020f0c0303040e07030e0d02010c0e010e0d140f10090506010b03010f06111612030314071409060904060b07030201050a02030c090f0a 79
    0xd0300200713860f055442e0f400c0490300c41801a1031039065400c0000740980440e880c503031072049035070000d80100b07600191f1686141a03220b2540102009032a0500303100181c91102c0c22481100c109070300301c178041074240d214235858401200d035241d49544100020044410b0b100040c50b8402914200080c01c141000011400e28800105040041c1d6680b006604c070340f50401103002125100303103812040c081e1064046500100031203c003030420f680200190308441000c009000841180b4000e407010445a1400f11000c0c0c402c0c05411515402803200124110500c88192412140058403440149150420030b445052200c10300701c40070300940a004210324004201c4c4801401d40c110040d0590109050090807600702140010300143c1040074002025404440309194000842810b0f950b080c0450002c6c00074401d141c21540c00a0030300400098075880780010b00040d5000760002c3c01180d864001c00300c101e04c402c84d0701c1d01c070710001400754442a040544408195030170281c481c030318040e203698021030088 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 780937751 1250 780936501 780936517
    0xc0e0f03120426070f09020c120c01060e06090c27030106141201140613090213090209090304030b011202060c01060f06090b041508040f0b0c0a0906020a021003020a09050402 76
    0x151514000c42501d0f0551400700e200000c404000d0f103189403c0c06401103600050b40b10350240c142c1c001c075510464840a02540209000da590000d80c0e5002011a46003e841035100340030703001e100c10000035410300b8100c1c01c0324482c00c1d0b40ea203900d140c05050141e01c0203400708145140402d210319a1f0320b00c25034030248120b101030000c0c40d50681d0303405180b204000b08004460102c40c500d90400040718001c400b88015940c02c01401c50b40e00b000729219030724070030052810381000b03584162420802288600c81d640000c202078000e503104085951840c6900707603248287e100c0181251400c600421a80d001030701806212880200780230b00e4031041c0e03005607080d600c1030341041114000c072500802c051034222211500919000407000d0600c1c1c944800030740070040041e501802e00c440380000604002070045003000050f070089030551181000341701c038110b82d084100c030940442d1281d10f010640a00000b500141aa8002c2400c652400c0041c000c03070103500b0002411080c40f919500208003a5100d00140c01e1032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 780939001 1250 780937751 780937769
    0x102070308151c150b0301110c0706110c151c060f0f14040510080d03020306090a060e040212030c01062d080a0602070c05041e0605040c0e0f031204 65
    0x5040c141d8203588150b40c48070480d4890b40000c600e60101da110164800141500310384400b800d1100450356201422210810b5580341d4600310844404001010251501541210031103803020b131110419103151441c140e0b00601e941c400000e40300b251038117012110303080100e108524140404001070038504100b80c540440712a1b128203007070081150b0016040010709040601161031494103020038040e9030003851a9000340e84510015031a884805810801811010115203124240e200001c0003074005840d114401c20b000004241200e04d140140c1c1e090b40d008840d4241c0c543c646900300b00b602e003820606000f4038001405105240103007842a40c005088220444001300005181603c1e12a811003d07903121703034480081403001c5c020010301c00162540c0000b0050ba00c042600b44a40003038041d030720041d84141011610642003032003c0145030602507a0400744041d549031410441600e1205c803401001840700d01042c03a42c1d14050b03185520f03018010301030b20444078a203c40b41107a41d005801200e40d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 780940251 1250 780939001 780939017
    0x1a0c0d051e0c160f23070603051609150e03030a02031c02070c060c030203040918060f05090606010e060f0c0c01020706030615080c120106120c05031009110c01020703 73
    0x919a5000e0341907440003954182c649850301c90b00c2407451040003400702401485422102504100c80c0b10401c070f41d8450250450540188035203180c940e9200300e40201400641000c001c10f10f0400600031103400c10202d40c80d404085404d00224a10340b9038012450703000c000d0049150300c66500c0c11700040c455002968051940c07240d0603034941e406401c07034402d124100c601c100a45800706170040007805c2607800501c2d14004110315410101c0c40c1d4002c64020607880d600d0610b000000755410340c0380100d00742c414034090000d0f400070003544d012114115a040122382040f00041d6041d80300703015001d642e910041074641045945500400715030803034450303180d0341c5d031003074003800c80568040011304002e1201d03207001d002c0d0034240394540c50342c441a400c01c0300a0210740030205152599100c2a60000e0125051f11202e030341c0d6655006045820041c0f907500000c0c80c241e9240f48075441401106e01c2600d103000b041200300d1808208038000c040c04902d54040c00e1061080e00d50003042030004050303407406980d030100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 780941501 1250 780940251 780940291
    0x80d060b09030a020609120607030506010801080f1b0d08070b010915030519020a030b090d0f021204050607050c031218090708240d0c170102071a0c0d05 67
    0x496605030000d50403a44144180d0610350340010b02800919419240a0748410800c4081151403216031400790842c0104810880f004c1c0d495070001d84241002d98810350070f40d81e285c00307080c0c442d010500700381d00f80c0e040714410402031600001020306502d40905036140c00407594944400030380084600300c516040500042102c41d403039000b89810011800c1d20311074050314660b64165100d04201b580d04505180144440655807190300c03441c000c54101089441502c0c004004546075800101c0f13090208003410b6041c500d00c2c1c40000c46085200c242e094031440c050034172041010700d4102400071034961240c0041032106490500c40b542101610001064840058010340e482889001c4500e5008000b28010400740586c88102241c1210007a0f412038481c110034401c40c0300d0440340303401d01030b0049800c40d0301e1070070014541c0d50724044400500c00c012210b10081505401d07032080d0080038045015200030300d28480c644410306034201c0101c0a001e0b00c1c0c9808209030006482d000c55080d007196060300f042c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 780942751 1250 780941501 780941527
    0x40f0303120b030c0a06030f090f080d0e0601120b09100c080403020106060e0f01030b030a0b160207050f061c15150810030c09020711030604060603031106070c060509100908 76
    0x8480300f24050310400050902164454100303210360b808054076590358100c40881e0744d01c4100a150401e60b51741a0386903604004e401c0d94092180300028915201c1650102d034804600181070310403500c02d4000c0e44066441d40c03101420042d080720200d008420b00d0241446052007829050f400c2c980f9107806910f001d041c06421915142d0000052103803041582505541358001c49004140909000410680d0040440c0c070b0710700043e00c0100201007420900c00307021034801240c44150056800c0b1500b40f610380b07061001d048807490032503821210034841c50801140c03ca00181c8041941440043c5103201303e0b01e801482004c6900481d07500078111500b01c0010342c00f0703140c190301810b161a10300c01a0314507590304800d020b091050404040c0c1c0840c1110810042c139440e0381d002400101101c0d40c5051904000c4014030441c0b00443c04158010b0130b9091a40c0c010541910824098071a903110000300e4a03901e01907e0010100c5035603003e0700c0c44902030900b051007040d1a85000e915030b1038803800740010304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 780944001 1250 780942751 780942761
    0x1b10300e070324060b0d090501020c0f0606040b03010e0d110f070b0304020a08210a0504030c09060e01080a0b06190506131503021e1e0301181d06041106040f030312 72
    0x441d0420701380141071090402c0c0710110303035040e211940001819243c50400328020700880c02043c08030b0055003072052103068005006401148211000c00c858003100c030401d4202c8101010a0300303650081810200f069004250300614080d500c000e441da0203113641e00550070720000e50411031105001101748425424400c080c01c018045074001800d00324000300c501110b00c0c0302d020100e401002d0000b4561500d070b1040c03080d03d0040d90720400754408a0740315403071540a0803103400703400540395050000080c0c8240020b440740101d600511241c003251103980a200004600051000715000c003000d002a0a031151002000900715410f0302c0750103181060410310304c5159070608413007018018840491500d1841c01c8040443c840407031115035911060700342c3e414240d03005c40b29006000780400001064400707240322500c080c0f40c400c010804854070b40745104603800142001002235100380005000181420107080030546c0040113641000e60f01ca201e190025900d400c01c500180718040802140382071400780d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 780945251 1250 780944001 780944063
    0x1116230319061b021915020a0c02040c050702010c0303180b0901090203060106090614031911120c0a1d01210b01080919150902031b10300e0703 63
    0x2614400f00040b1002035031642510b86814004260800e06001c006221445000c001c842210070354564a101c1c0d00500743d843d00e10000c0c1d01960904910b102014071940c1128802c0740d058540300000381c0c080e2400c5008202d640200400407401c1400c1e0310214043d58035181c41445400004509c15903144103040c24002c040c0d0001e811302401000c00d02085400c04d82e110a0543c484038020344a950764070a040c01e411014000204440c5071088070b59003074000500a00f801c02c80c260480105071a0100043e100d44184010900001d030840c0c4035012502d04903040c1000804140340c007402ca1421004c00d400d039150751500501c0050350b200c2c0700a00301c0d600401440e41c45040c5401800321040d84120383c081b90300840301c00800000700031041c2c4806000c150300018003e9005821900015032504002000301401c5030650704c103404130001040c190f84602030b1401e9540901801ca83e804400b6014440502051a0740d00c80d61a01c40341000711214040200800650142c5100c031884c461301c0d40b507140c0030018214 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 780946501 1250 780945251 780945281
    0x1030b0a0602061501091508041a0f1803072406122003070b070308010603060e06030c061606180c0816030f0809100807111623031906 59
    0x8000c00c0200c0d0007041c016845140118074501505213a00101e030050055044001241c514a41d004462544004140d1090744181c5e500074a1f140b4004107208444030456440014000d2440003d80e450304c5200d055a0385000310381220304050032682c91a10180021714003003010324400c2c102180101c4103019841c0240660f07182c010300a034454649543c100c440e610806030b49030310f00c081d1014a88041040fa40200b81034860281c907031000340b600170117084c001c1c481c40000034188540804d0403020590b019000d140024010301c070500e00c5005104041d0003140c2d0703400008242084080114090b40140c50f44181038240030084000c2600d805013081030142c10502c5036500c0010b508603812102090801a25005030b11900682214609080240b180c1003800d41c10150301b01ea082c881c2500079a003035000d44a48c0c4c88541c2000b00401941da503449105141081c0c04074403901c10440172403410b003000120795141c010760700c0c0259808042844c0c01040703c2e0754405001030501c3c44083c081c461154a14409180d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 780947751 1250 780946501 780946519
    0x10c06060e15040f0605030c040203040f1707021f020c040903030b0a0807030b09190b0603120d14072309030703050316060b0904020a170c0405162d0804060e12040501030b 75
    0x6c00b1a50b14800e0005c024002d0380e00101007402e007c2c0c5900340708501d551040d042d9070311007004040d85100e80c000c500c00700e000e82400684411043c0b811070721001c8012a82d8001c103000c04c08101004050320090005034140344c0d0310000c0e565161a110918400f52501c40e001f810b46915619100300c64a10040001180d504403282401503503c1d07105000203416007111441e0030030348440c00000c1c2006c00760208081ca4600000394040c0045064000100714080d901003240990b440c0c801c00c1d1003200002040c00b100e80900a03168006041000151003014006421614000d40703e944140c030755440850b20740d03500d24001c2c061808002032030246900c02041600c4904260401d64045180031807980980d84500c00801d000c0030380740800300098203040e030009000b0320a50928000c8180185a070ba11548005036000100301c1075140200154841601100100c90704400c02000403140ca48015100b04c0300e0989a40608030740d40c0d03080109060405515424607a500d02c0d01b8005000c541072001040d001d4203104c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 780949001 1250 780947751 780947759
    0x510020a0203070201050c030c010906091202010903020322051c0c061e05220e0702070501020115170f0303040302280c030b061c0501061d011202010c06060e15040f06 73
    0xb00a0310b590550a0a100303842d015500806c5042d0f000d07c80220076603610301010740c0b003441010341021030958011001d50519a0314100102e00340d445951019001d070740100803040d01c034002030142003041440200c0042500340c81d580010048041c0616040340d0416910824003405440600400202028100868004400440718525021411000060010125001c0ea03c540e4105440f10241c00503405040816160b1100c411030758802d8aa040052040e9840800c42d94014481e10030031040703503043e80743e5851500d140221a00c004120119982c040e62050003201441040518080c41c800c0d000307006100f43c02e203403041801d40c0c0f408881d00b00144401c40500440c600441000590b904200c4258903951950003285d541c42540702a485405800c18581c0705000d01980804180e45000a00d1603490401d41f0440e88101400c0c00f80ca40c0c0d0030351000302e030801513001d1080d0300403c03441124081141940c5000301d0072414021200070444491041807450a445c192054030480380c1c940c9020080e01d0b040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 780950251 1250 780949001 780949003
    0xb0405010c2d0512040309030c050a05090103170705030a02010507080c09010c0312110f040504060506190509010e0a12050c03030c070909140102041d15090f06041b0504030510020a02 80
    0x8900c40c0e14a61070b200805259001d84034004030380301c2c55038070442c444050406160042108105100c1596003034280360001c5040d107000740800d41180d10082035080b03546d01b15201c0340c5030180380c04401404c4540801040340020800c2c009401081c500b034000107400c0c036014102915101000348102116101003058403407582e0080e1690f00055003610300f4000c2d01c0726035030110000308130806001c0390903100800c00c207a60705400c6c070051080d14415542405025a90300038042e0f58000c100c41c020a20310382c42400d0503420321800240c59401c00501d0301c1d4105a403600c0108140e03410303541025102201040020050240070807400e5807150b41503008514217040c40b01000d0311058071740110800b4544402d518414092510821581445810001c640d03c42d0b03104110070642c02030380e05015885102d0b000040b06c0d1010201030311003c000c05400701c002d5135114102c190249000505080d4032650b1004440e280b00542d03018000082441c0e00c0c0d840da01c41c11030034900e1803d00d481180314032050040011003c440e0b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 780951501 1250 780950251 780950297
    0x60506030408030a1e090620070b100504020d020702122d16080706020d0302090d0803060111010f060603140103020d080705150a0606030b0402210912070b0405010c 72
    0x140004125480e41c441507107513405000b40031603000c03421283d02c10a1002020613400101c840744640070400106c441c1662201140556143c3d07000c0f1401c0500021000c1890300a007140c3c0900d07816907441000e51220b00181c22038005081c0d284070180e000c142102103041207102648003010f00750040c106090f000104c4e034a50511501c40150610015080c181440410030000340c1e094420113120b464552100303002da5881142e88036240042c851724403091034840c001e00c02c9800005010703100340c0d445079003030300d554010b075001404241c100700e510700000800c028280300c0d079000e0501810020501914190008041e41d50b010320080b101e084134130042006a6440c0c19407582d1a52003003649490341064104542070031346054003410500c0c60304c802c2101c034040070b901c0078040d1601a102040325228820070312080740518030b43c00c60312031001c1d800500c8401c40c13050f0482c0c0c050908002c030ba1501c2c44030f100d50303003142d000200100d5040c220a8140401c00c40c080c050750b4840203881c85e000e82c03640750f40b4245a601c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 780952751 1250 780951501 780951503
    0x30114011b0c140609030f0d020d0c03090308090d060e0d140c19021c051c03060b0913020f0703020c1333030c03030c05060c0301080c2701180c030605060304 69
    0x40c43c000306240c1d691101e8041c1d03401403000406807090007449500f0142c0b40d04840d030100700140a2501030303400c054010204e10415580682d645050b050440e5110290341d44000b451640c4900701160365000142c0c54051200d0142000029000c00c4009900c040c101c442c141c071400345c0f546418040d5640d40900050020700c1469100700b4000055098004148400711540e180c03110000300c2d411300018404001410601c20480082c03505603185402c50440446407140a01c0c03400ca1820010b28002e840c00a42e0b41443c03021445005141880c00320060701e075a0321011084001d41c00407100c0d22402c4c0740c100c0035800c0354520210f0503c08400030900e01003508402d201d0030064000030035407002003101000740400155070300c004000c201c0390b12814064420324242c902210720307100710f00004404041420540f4100ca000a006041c03000350101044900342d6104980d901808094201c5140540701c0308009009004041603d840c002504801c20140c1d104100c2801c00d05040503000c00c40e54a07480103c039131203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 780954001 1250 780952751 780952769
    0x2041211040609091b050d0b07030510091d01050a0b060304031b02031911030a030f140f2d03042004021b06090d0c050703121103030114011b0c 63
    0x800c80280008009045507002044640e00d4001180300b04110b80c090290f455010002400910756100108040380d5041000145059107034800700b1421406a0031068000031058400c190240e100c80c840804c490b46041e04502038104903401001412081c41400e80140c2c8040d070074444862584081541480050801801c0003400480075041030009000284e50f50707401025074851140e003010351f0030074400d0034409071524007204011042c545000101855680c0d4183c44000c031880e000c1c04140c883e400c514a03c86c0001c0c404004000c00d80c0390010060803018034141c0d025000a0a805101609034820101d501d4030082c2081480007080750650810800c6003000c00c4460b00083c0704002c50041e000c1c0d460003405080c0d5a04c0b6444601c0d20110300c8512903c0c0901c2100ca0718604003208075280c0702d1050014100e0342001d58184082032082608440a40310b9080855400a144142502d140d209134001e020515003504a40303215a07000c60200a240d0758484800c032a0480c07900e0f030210901e0f03180300310080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 780955251 1250 780954001 780954023
    0x2022060f0f4a01120c03110103090b01091b17010b0a050d020c010515031f020a0516030c0201090b0c060601030b04110d0504020a09050705030c0a030908030c07030210020412 76
    0x4100b58820040341c4040c480341603000300982503005102046440e400c0400500030010011070f04e00c8000040c6980d1039007003000b40340b2451035034443c4c9590b000d41c0c04099040545a60248012030348402050b40209680d03c00092003585149000700029004904442000b00070381c1c01c0c102c5400c80310035590640b4000305840d69102c108440582d22441104c0d400e407a41800812085100791065021510034800f80c80c03480d10b00103440b02016155003604e00f8188080c0521040b400c00e00003242d02074080d9104d03500348146014480c21541c2d41040c00780d58200c0c0020002c0d901c260440d41d01c5210800104410b8104a08010705480c2c4c20346c0317594008151604056968600389004d039600d40000150728050858030b80e90300940300168014140482d003c0e0b02540c0e107468001030790760306c92160500c900080d5903514199181c1c11140d482582c007403d900c400301078444942002040011008500441052210340d5a8002900d0044d05020502c2c05d100982481030004200911821a100400550058107911 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 780956501 1250 780955251 780955289
    0x3150f1f181401020c04020901090905100f0314010c03140f040f1407061103030105060a0804050307020a14010f091503150e070201020c060f06010c2022060f0f 70
    0x5460003207a00203045948a6900002e0507110309000705100e141d080e400d440320f8940f4402404142c1c424610b42c1400a50101c1003048048180e07841035800021302d15082160a43e150604006d1190603001541e48010303201c0405202002442581d100190741d08082c41960b910030030150308500010500f404035048400040c04114503100070090302e0f44d003d001000215080361140d9075031210303400f0740c1010030407446440803c214000b09681c105c5038010609440d0090514003202e484002038001c039224801270111030b0040c0d80d80b0305c10314090642203804505d1014200001015120484456014403a01c00c0f0180314403140c82d20300400c504003604020981d6400010110b4080c0d0f01c40c0c0c000c6c60000740e1030050001d1a03906400510a020800c012198261580c5007000f1030140140c0b40180414440302c4034100259400d828840ca040c803044c80c0e010040c81140c04905c80e11101804056621100d429504060f000c81c41554050116090b424031010300b48015000403000e40e0040880354624000e03048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 780957751 1250 780956501 780956507
    0x1113020706060e100b040b030106181205061509040c17030c19030201052809030e0306040605010e0a020f1b1f020403031209080d0c0207120803150f1f 66
    0x261a4a6200e0010001c040d90b582510b000f224059490302e0600000c0e075000034060b0007a02c1036070181c0f0380c52105240307141d20700403040e216160840003050764892407074000186082404c0784c0c455002d010300085e2034285015105529104825481c0c00d100726018014400400d42d800c1400c402d4507641c0354000c3c8045d114090851860140550191051045a140009801e07008000ca90400d100350020702070354450041c240059001918007605ca85040b4543c00794800345500000c18090003403e01d00000004140440c1c200042264280c400304d4840d00100f061010030008a0707407110b0b6200b011403c0c440d800b84107800d5071003060b45070903101641d90080081c081090043d0340304007007200d6082c038801c41c41e003031200003a400501c0164045000c09444d0b810040d40b60050880c00d0341d004c0046843c02040440c8500104101903140c0118171406070085285802406a0100f25018491181e01c9180c00d044a4401180a45241c0d01034a00b05041c07e0040c0c542003d000c8440603d001800a203071880310080b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 780959001 1250 780957751 780957757
    0x20127030c0b15030709091e0302060c0708040e07021c1b030c021504030b04031805010813140f210708040512030d021305040b01091a0c03070f05010b100903111302 72
    0x10f41d500d800340e40740008003903002c0d5000b00c1e5000e100b101450182c5804c05489006c44118a00c0603015070014800104040d103144001c0940500c11240181855114103855400c00804c40303200300540c0c04001c1e101c00030280c81000100b0315030700b4500010701080c0480340c1510080700400c01400d012113840302900315942c44481d03410407d840c0c048143c41d0365030703030406001d1100151010380205440c1540c030216162890240d00c1600c4042c0c490300c40907140c000c6103280104001c1419500740d035034062500c0b0010700501200311056010402801c200c014041c500c0ca0303001000c5680c40d095001001800b00099507031084d81d085880442c2c0c005651481c406607075056110350030300744c540d03e8400148041d01c80600c010364010307514196010404240804010b480c0000f41d40102c00c580301000e04000800f00c0050300500c4020466805c0e00d040910f05c0c1d036080034031410802d00700c03002c4e51201c56140300c90424484854842e00c0074a00300d12010302d5615540b003003408682001c0d026031084910801005429011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 780960251 1250 780959001 780959041
    0x606140c250e1f141f020303060103150e060409050f070e0a140906040b090a0c0b040e0601090b12041a15031c0e100915020127030c0b 59
    0x440e640301c192000d044044040e240515188048420041903800220b0f00707400740c11806100f1408001810064602000003400b41407951112610300d80d08000100003410500b5a240740d002541c80c2c5c100040050f0603aa05803a1001c800120741c04104484000ac2e051590404070a440001e02044182080c904020341e050740006540304402e4000703201088e9a030721905c204c3d50744004100c90418044804040e0009807210901c0d5803000d000300300812004400c6030b80007140700302100c4a006603680c3e084910030040c1c0c0003a0150b0000301c0d04008800d4040400c07644a102440d107038100b1410420a02078030700650006117040b40c00d1400040c01c10014042001008003210345524051038181e40c40082c900c40303ca0031034024041e281141c000d0703036043e40c4551200000c82d03c990f105418001c0620001814a1071031108110310408001100e214003006e05100c3c0800364000b0500f40ca0704841c092075202d1020100000c000050720070004a60f110551580d52544203036588040e4480d109910105022000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 780961501 1250 780960251 780960283
    0x10512010e040204060b03012303100606020a060c03140109110906070f030306081b09090a081603031a090c0d27021503160804080f030703050f06040606140c 69
    0x1041d05030403018900e20407403088034144000c031b840d00180909408203104400c060400604003100e08a40c03994481d03088440035044541115403090140151103042d03112001507001140800184010383c094031500182c80d080031b1001c0358054041c2046000e05102c0e1004840d42c0c1c81a0130b0000310070764122816907030020121600d5042600700380500d91800d000860100c1d2500b00000780344140810f0104280d00c41d020710f00c0d004800e9400344002034800a100c0011809000c1480340040d402e9070103010090b0040c0b0103c4424541c500d001360071036128040f40e800c025200c800108041d9034155040d544042e40702215503e40301e10035090030141441e44000c0c2036021041168040101080c9a502c103442e00807261205a514a950740c441d0611003500c480089425003c901c48025001e0000c003070300203100e0541c0502d40700142002040750341043e601317040040c1d140c40511134484003003034099400400448040080c5854184040d003904041e00c180710b40c54002103181c0c04082c40034001129424030143e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 780962751 1250 780961501 780961537
    0x207060c0807021b0a090b010302070b04030309120305060f04020d0e15071d0f0904020a0e0c030402040e0118230304090c09080f070b0715020a0801030201110a051b0105 74
    0x3030340c0604114021184031005108802c3c1c0d40c6000b40c01c1c1d0b20310b44600034005d460103400d5414041c080000d000c120165905142c3c081240000180240c60000c2c4558040c4d500003c607640c0500c1c00c1c0c4159040018840700701b604040038004039034bc40305010452954200c800613070310012020703904040c04d0a2501d1072800d000d0180000d81c00b4180c1890340c1c0c1310b409180e88902c550100440d080c120400c14101254006403054800300b181c0c00d209162a80250000303011058a42d030f00c00078032015110445121540c020088140001c505060048009460721580217100040030b8160b0140300e0fa0714980040d0200b02120300a46850707034113691481d01c000c070407030590f690760340c59240a40213080d9802280c03002031120440001c02035404940204030158060240c030303240d4035000044101ea00812400c0e501100507180c034125040852000700b0500e4503e80300c01c0e5840d0701d14000034100a00c2184e1408480d00000b610ba40001c802044400080000550300545107a4000c0121240d0050000400300c00b1444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 780964001 1250 780962751 780962771
    0x2403220602160c0f08070b0304030e060c07140105071509060209040e07080f0604030f1d0a24140a050c160f1701020403030e0103051509013215030901020706 69
    0xa0062900d003070040e00c9004030155a040381390620f407002e00c22080907030410712051051503050f000454005000e031030010640781101c07000030019401505200300c190b02482c8208000c803032002030780742400007d003011030420701c254407035868a00c0b031919038441441e5507004501c104160382e070580360f030444050b10070003400c0186c0058a555030060f01231075880f032150305c0840e580710704009016481564036a50704000d1070100351058078100280004a92941500b00c1e190781d56859681d020001000014514500344e90000ca50840d41c0440403072403001c1042161129400042d9502100c40c03484143c507117540d6031a0504c51690520403040d041d501c070007041d2000064550440850700050380c4c1d2280301d0400903100c0f40d4040b400c1b80314070b200045c089250360200804660096000d00c0c0d1009042d00041e00e030b1004140040c0b6043c500740c00400c40e40003034203804002e01c016120030b00d244184c04a50902c2d400800c500146008442151407445c81c040040082c08464003034040d24502c950201381800b0000c44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 780965251 1250 780964001 780964027
    0xf0304060522081f0605061602010503180a0821061c020103060519030309090911010f0e180702070503070b1e0c01020a02030a0f17041b170106052403220602 69
    0x180350915084c1504290010609180c52811200c805000101441c50031506900560395900001c115862180e405904410044c400780f016101c180d20526900e0399812130400c40e410704100b5101d182000001d40020046c3c80c2d1961003ea1503003004c142820350000e191440100e028214a0708a160041c1c41101d4941c448c0234900c1d040c8050302e10030f48808000c00d456400c00412503160502c0940105206c080420a43d409400c294590700c0c0300340f070454002d401010200b204034402409607660505103008110203a0740c180b00c2880940812409040181e20b0048205840e01440b5107901282d09282841ca040200c42011114a080b4940082d503ca0081400c060340304c1e041220350602140e5030300c50f130540140c400d02d03490b1211021010140030a4556840b007084d50105014800036113000010042414608100c01c1d00360203005a0010840c2409c082c1445510035400e419084001d000710b043e036110780100000e40303520075619003695100c0010171500341c01807a000b02002d020544001007800d01582 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 780966501 1250 780965251 780965293
    0x212030409022206050f18130e0706020712030206011703040f060c0c0501082a0c0f01051609030b0f0a0605040c030b010e091b160506180f030406052208 67
    0x2490145100654515040e1170320b22882c2158500030508004074003d04c0d02d03025410480c0c410180800303180d4101e0011660413560f421641c25450382c440d4800700400c07541009000c000e00111114081d0072101380d54082e60340c0c84180143e13440d14400c54010742c3d402400300306850081591119000620f640d03014050034070035044006503504000d200c0c0100b09540142c5002c0d0085c0c90710f0310303ca400008682c200510703003034070b03860020b9105808118030300d44c0400400403c103c1d035024400000e0141041d41044005881c030060800901001e91810004144010082980032108003c0c00c5a1561131489440c020840c50b0085640719103461428488180d060b803246e52100c1e000e0701c902410200f0748081210744442150100c0910806030100c03224400e405c0040d0802c0c05404403070b600341c0551a5070b001c0c10804200c940141d0595100c11041c0065001c118140040c40030304042c6103840d040007001030072485224207003050403d50003500d0b00342d910080f207120001c0c08100152090700d50304404240402c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 780967751 1250 780966501 780966547
    0x40314010c020109020a030809010905062b09031b05070b1215180c0f0903060406020c10090f02221401060e03030c2d0a03050a170f04021203040902 65
    0x58039164400308180d00501c1005001a0006d2410340158516907801e03c6d41c1c3d010650490400461760f40004150711000c0280c070815130020b0321349440b50a2076840340611400b0f01f85402031541040001ca000c83c3d0443d600800c0d0700b9840200070002082d50800c02c0c03070134070694000651010000b8040c6203580303904400c1c600400d00c01c03003045851401e01007045030080340910300c0c01c40e168842c40412004641417000f04000240145201e0a1001c810000390600108403030956040e07800080700c00a9100c24850704000f040b45203010444480c0580302c02010070f000b848000c1c019200713040d500480340411070b084150700003042010b0020740158101812007080c2889550013194030418400154900403064800d08500c80c8010711041c00c40d9500f02c94280301000c16000494810000e0303e90700300090120b9444180079031207140c0e8466200030000d00303010507500311400a07400c68090000700018200b40c10b03041034040710302203542c2e42601c82c81c1e400c5100b9a031080645602c0010721020b452242403e0520017 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 780969001 1250 780967751 780967753
    0xa0305160f120b3108030601030c1409060f091f112b0e09070309031d0105030a0f020910020705040509010e070303140f030403051c0605011b1403040314 67
    0x2641d038034203680199020b07a02c2c00420700304140001a0000303402e684400ea403046060345103811803540550089401c54810320a40d00c442c03002080113455600340c06820310031032051400b00c1c40303800050803008550242045003440342c0b0000a00025800003241602c007400d1004041c03149480042c1346041803081150700d01c4000c180800c01c0c51658120100301004a21030307440c1d002c01e070502d148290708000c01c810607c050034040340b292803480300d44510514a100300c10640340040c0869050601070f200c403943c0c1c40d0b01d0841034541c4c640e200b00d80c0d900606481d000300402001184004400b00c0e2800039000c2d405229410003c3c200048548550000b507000131a9004c1d03504000f145c43d901220344c00d0b1030464480c4a015800300c641040081d10610352110046442c0510358200003010000340c529a00031745068000807804598420102e0402042000111b98038008105881c501301c0082c16001003600d40300c1d031440d0700500d40f0341480025100301036800750400540c0d90b00c3c3c0e101d2412400c94554102500c0b51 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 780970251 1250 780969001 780969029
    0xe010f0f05060d030327031d030a210903061109010e0d020d080f070506010b09100c050d110703021005030f1b040b0a020f0a150b15040b0304020a030516 67
    0x605458480c46000c0d020141c1015012203075038400754054041504d006c0080500d4039443c001c12000000700403c0746100395103114003016943c0b9460000c401c0e20315010310a801c4541020001100684000c600b82d040c00e50780003442c85414000d6030300310f2a41d0700240c003e40c01c021122480444100003400001801d032145050241e1035000d00030100c3ca04c102c000c2d000310001600e4008908840701402c001c1c03014200007468020250346003420f1035420f078072641d102c000208814030320340f400c80f060100071509843c1c07600c00403016483c0c4075650346400103140c4c00e10500150030b55210400748101405140c0160145400c210241002070160744202c4844c00c9101e10034001c6440401d030342948502e15003c0b90061401d1030304007012011142d02c01c2c3c507440194452440f46014400040c840703c11100c0c040d410342050042c162010009581660b45900c0c401e542108550070703420020001d03582907542c18040c0b41d48942d901e02c0030548401c1d5030380015103603100780000d110341c003c040c1d801c000560701c4162031049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 780971501 1250 780970251 780970271
    0x190c061a04060f210f0c0807031a0405150601050702091302090606040303020a061a030f060a11092407020d0b011d04120822050f0d02060c0a18090e010f 67
    0x81c0300900b60203900110443c0034281000c100300d4003d0407501d00c3c0100c0c1e500396a84140c2c1d03114850010243d00c1180c42d41c020365800c00500410ac0d00e0007001c9040d1010200d4a4500b40c0ea03500d1720340d00c0701d403035256110056602080e0b030799100b1002d031001c0507030181c03180c020382c2001c940052003020003440c00c0b4864080d19001811f07a0402c0c1084c0d4044951640040190000c560f0303444003d03014010348103003c4410408090501d40c0c080101103496400d41014141e0750510382070000c00e0710882d4114030108401040075031b03000d40301c940854100541c0800514228007038840382130094414071001950000380c5614640520842a1071581211805c08029200240e0b15113101d40b0940102d9014210b83c400e8003200342d02c0350080345686e50000e950f03c807800307055000b103114074248030342501c0c10313100e83d0301031803900711042d000f007003d024200541d000800c11443c0880000500d842408030100c100005a00b82c00680f03a1200820005000085005c1c403c80e00c200030504d0003000468100001c0c00e0174803180e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 780972751 1250 780971501 780971519
    0xb03060a0b0a0206150612010e07020c060306010e01050c240907061b02060c101107021201050402100c081c0f1503031b17070303020306030f0f03190c061a0406 70
    0x3490449180c2c02401065a03001c0c100314176080d50314040c680007002004440800841d14142901a003100b80036411641080e110007441d10b180160f029003d403600700b0902411341e0b0001c060300702c40d5800f468043d9485240074405414201545030881d0f018a55001d0b0044030005c025540b44100c60000c202c50005a80300000c854941500301c1150404e940700140c1005424210021722082c0c04000450f070300c90b410b00030007078121290807101e030b401084c020030801c2c21450b207001440c04c3d8650f180d001b8007603402c258001400c41c00800c580e5105004800c42002d040061380e00c2600d0092564000444003150722003070800240c0140c8008001c030a1800c0480005070f402c0310039140540e60180c0e03840c0980311100da09107084040001c0140d4160303004070039885211a03010010081644039980140e22420301d0810f243c504040010513130b02c00d40000c11240f016000010644000704080c0700c5062460340c0307189050340c03c1c42d65418043d14240c1400c1c5d8038580390281c0b00c2c2c002404002030718200314281e031365a494 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 780974001 1250 780972751 780972757
    0x120215011404050601021603030201020d0b06180607020310150923070e0d0c0308130f0608040206180d052107020a05152a010615020606010c030909060b03060a0b 71
    0x210541d8107691990344540c2041c3d402039600074018011101140c01d44124644000c150345d04c201e005030740009030742e0302c0500c0302d0040c040f59510035100c040c1828000000030340d0150000440e180295408500c003410340d942000660399050301e85404100315202c2c101983d240d602a400340d640440d04106091840c8001a00f54038010490802c2d945070f140ca4400c0120341e0b8036142020f841c0d10000304081d91001c00d2140071032600562241203180c1d42c03002c501000d458240e619510043c5d40e11285841080340d2034214072a01d5100c0d504550700e0365a07490200d80705441c48004040c3da03400000c0c000100040000000f64409904041040c00340480640c85c034800b128172a400c0004d4001030031100030001e60502c20f10004090407038080060030b0040b81c1c61451000441d8800e4917020041444150b580000280300d100d015006842000d2800c05140700041e50310f80020380740a04010601d104001410712031801d51018100d030701d0302400040d036201146600703500280e51061040414020005020703200c1411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 780975251 1250 780974001 780974009
    0x20903010b010c1a060a091a03120301060203120c190f02060a0507020a02010809010f110a080c03070903080702040605100c0c050306070c0308090a05031306030533130912021501 78
    0xf1944d10201c10000c0616402c03c058001ca0304840c400340080f070300100d035006a150401c1311008103211714440342c3c1054900258903119a0704280b04000600070070703501004440064030407801040d980d4480c19000403070b52180410ba50385900c044000358158940c03080b1402d22034505c030740c00c42c1c17115190150360408407102600d4100142c0c3c813181500c00194003c010841e40083d1074000011300040c01c1c02c1d80405e8070940100d01c1030386c1000003102003040390804646904010390280c190b04510304a80090f06480d03107030002411a14002c5004001c41d5500d400407000303008040c2402c258410703400d80191115140501c100c03030f0000913000c046182d05000807850f10500b401d65840780309942540303040c1d0b040368002c0c10f41c203064000d00e90301c0808140704200810036040c1a21800c22200e141484c003e0880c0c4006d8001701c040030b0100701c0d0250000940302d86600000c542e103c603943d40301841d03000a400350085212000054100100c00302846260081d61400711042c1c0c090f1540a411000110104042402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 780976501 1250 780975251 780975263
    0xc0307031118151207030515160302040e01210f060e010f090b130f08120709060c11120309271e3705090705120a0f0201140d020903010b010c 62
    0x3030b2002a1401c6590001544a002c05440c4170540743c0c1c0340d40f81841d0881040c1d84401409400307018001a0310000e074a81d22200386030440c01c06040410b016145507040c494109080c0307862000c00d002d41038414840d41d0050f40300c140480c9013841071501101070a221640003401303500e0b040014289141ca8018456225401414031800e607440e94248256400440c0091354035940d800e030510300041018000300510b0380050b515220302d28142400810010003500590708011001c50041c1c0028a0701c150600700503403c8035174411900c03000382054a0340c001c0c0140d040d40070b07410400c41c101e103c2c29440f8502e031001c00703a40c002525a41c3c40010030111400d030354005900607900000074021400e10030800d8400d013000200213680d800c500a200451500071048213019542c0c9005100301c6201c2000564000e240076900340c001d42c041c0c01e201b55125541d090000e00100b209038907640c04c580c42249544030001007102040d403906203412090340250042c0c6119030296181c02481807079076001c0d40322a280554030107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 780977751 1250 780976501 780976531
    0xf01051f03021305040512040e061c0503071205130909060f0501050105040b1806030702010212070e0d031404080708150f01050d0201030923011e0615110c0307031118 73
    0x2400f40b20040030b0041007603030240515130303020140f103401d00000c200030301001c1801802030900e207041107015030304030120740c140f0a1a09045000500080b0540e41c1654002160302c41182240d00140c5040c4210a520707540701d4001c0101080c00310660348490002402105d042040c0700c444210001142c5080c0501400300e60140810414841100c004001d4040c0110702c00300c0c06401480403d05541047d60700402507500030031a682c1d00707103071501c0180d881402031030500d458090080c0810329034040031030050704001c10a030443c08445840f03400c5400400c01c10046170b10036075035001e0054440414102a0030448403090200b00961482c050580c10394400400341c601c101d042d94010f40040144001c2250b026051403807103c01d100c8480183d0350b40842000011441ca42007408400501002e040e009041500e00704090100d01038945c0d80070412b03181801d25094064180c5011860003284400256040c8a070540100410900841200810302c003501d10781d2443c0520313522042c402e030b41100d000315016021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 780979001 1250 780977751 780977779
    0x62d020724051e041e050f03060103020609100e0616140303070518010e130506030709052401021203100905060f33041202030f07031a04060e0f01051f0302 68
    0x48441d054943c20b0805924a829599500b80e6045071880d5a40c848181c1c64140802c01400d14010345219804220b02400d815811940003038184e0040801d6035008000c3c01001050030b40c0659550350104034024620358940c80c0510f141c030690034042904440d18084031030914800d07200041600d004107520344900307080281610300c81069000412140d0b04115940c00d000b81542c0b9500c031148000342c10810046030601c8c0c00d030141441c04010f50f00520750b031407800007000105003d510a2086c001c0b20501503211801e450b0004030303e81284103180ea00703510f50020a00c0982d0481040290444001000c10f00850703030b4280c100090000f0030410160420900707140d640314251908440404c0f8007940b04440045d605442d0303085820b4205401c412440c8a0401e0400c040d4541044140c4c101c581c5000140242da0642c0c0d6180200541c54209505906400700800d0410103d40c100003010a104d408483c0801c412010040c00b0713200507945842e8180f4107c1800811000c008011002e5035005410380c0305d903400d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 780980251 1250 780979001 780979027
    0x6090602030d152601052d06010e13140606030606030a0c030e0a0b01180b0a0b181f18060f050d060f1d0a02070309062d02072405 57
    0x90015a2118291070120100d500d02104d80b040044101000944684103902075049084960103010348900340703001006c03643c010310084103204000340f44c0c3d0440f4080b07459a000694061001e07113034a980c041e56404403c2031510b00b40c2e12080c8014a01e580c880c08a480310b4050251a01c0b058944a0308694100002002c0b105244c0140c02d5007649403900080210101100c0c0d420400f8402c011079039000d00c1001000b071035400c040c4c0004c28065203d01004450409400125500341c3c51141d08400c01d0080784003080d000300c000400c60042030151482c0c2c03080713006001c40d1010046080025010800614642005a2545da4410300b07403041510b4a0592200709001680ca58104156078104140c58240224071140441049402030150a461042c803184024410b082041d00a001140841c41880400042076105040b4800c852803401d001103c5800300081009205107410000d03e043c42c1c0549110105a0028084045401241c1c100c06c030309001300059a8040d050038407110004030180995041400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 780981501 1250 780980251 780980261
    0x5010f14090d05060a020d14060d03140d15030605071103030a2c0f0f0d080408030c0702150405030d030603050d11070e070201090c08060601120203092a0a06090602030d 74
    0x10001d40e00c281c0b07260b0b105803800380111208144550045040c0303a92070032601a085003644d15407040602403134098045002d94140640c06001c220030451440440f00c40401156060460190309110340c1c03000e0405071400c00b64074802120410700c0c0100007200d282c0303e448081d40d2a200b500c003442c0b55844211640700074103070b00b100f4408800459040f06003040c20464801c82d1070300549000e40100f02903220f4480c200405109502c00ca81c00503007103540103e03400140107500c5a80310b0071807078594840342560340190003070800003034000d4250b06602408107017103000707041299001c408070795003840701c3d0500310295a81440020101d41c010414580b28034020880900000120f4003100c0000d6035a5840e072415080a60761500543d41d01d007000c5040c40f184200a4020381081c4004017201d040000000b000c10080c0400100521f901001265044006200120041801124007500500e00242c0c410b100040c002e00e40348500c444100005400303003d04501e1007104c445030003460403e1002415500508 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 780982751 1250 780981501 780981517
    0x91a2e0306051207060306050303120f0a09050f2d0a060209030f060403030605090f07020d0c020411130f1221050702040603030f0306060509030a0f020604092405010f14 74
    0x16120000810941c4403d4045204080e100005041c0d061810001804580003604540d00070341040040340400100d51401c0c68124070460803034201990f80c05180c80040c80c03404402000c1340580c0d0090141a18001521803265220020b49100c22545184410014003014420082c90300004d81980c003042c0740e50b0107010a144050250340000349036072056818924212000c502095a409060015050040140d40e00007402c4403861014249500043d64680042d408c0804210200d21103108640350758110110722100011400d40b224210115010040c11754018140860090480000c891800b011208203003a044105581d6081310740000000b2158411080810300000308a80710050300c440c860800210301030359848c07018030342c2140d0042c1520150390191082000902c00f420003540c2c0030a50500965200c80612100d440d60f2020030b2682c002c40d80b00100003490b00e04507a91024144106d6140b582110240d21025925080150303000042a48102c000407a851910070f900310355400101145 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 780984001 1250 780982751 780982757
    0x140109080301030b011a070209010312110f0705190311100309200f1008160c080408010923060105270702030c1605060a1413091a2e 58
    0x21094984411445600c00c0c0e0045524001d15001080552100c42c070025021a151903102d00d01040c42e00081c8a246060001070404807009112400b01b0340141018401c031100b5505541514840414440d150300162240302e004400260208541c055260f0b108002d607503200c0d11410100d9980014040711041c1907006809042e510108040030030a9026031030556004445040e12400d1201c09104a44a500c0039407401000250103441240380c0000304154401300300445000c12180c14207040fa2004d11580011701651400a00800e200c5019041110703010b00800d00b02c0c84418844114584070140e140d80c6068a4010a005101e24030300320105c0c1004038600f24643c0c011485201900800c1c14040d00c150016a0002410440c030f02c1042c4244440182c10212070700917a071405000c03540c07e12621040e10204041061110700812902c000e4400f000c0d621800a840c01d62645141002080d01018840c0007040e0102c080d0014a4a40f100c80303c03d00f1003007031a0b0000b00c03c1880050203100c02000c00828 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 780985251 1250 780984001 780984011
    0xa080a1209060207031b020f0603060d0b0901050106020f070f0501030b0621010e100e0f060d2004050c040b07030c06110a0302090a05031908090411040b341401 70
    0x90384585000719440c0600071100103954030760600d0050542c5031050944001e141502c0030040240c0d481c03500c904803100090f584641e4aa0b640400125001c00416004003007517904000c0c40109081580014141c601030703000c44182c1c000c0c0c030b04181d03552400c0e407081e02e20b09410600240310340e503c203812080064502070005803c0c5030003455111045614040c443e1030024070000108014000c03c02c01d6600611001010b2500c1400c01c0018041c44000401e000d0401403107001146a40d2a0b00d456409103503000400404040500c102803003010604840c5d0510503410000481c0510381d0120841e0212000b0414851521400ba81e0075a1680039144040e10220398a0720f0030104990312200805c01c00358242c0d80140d598502c00104142c1c0c46980e0480750095001444240b10f1100801d5512074460f0001c00c1c05844442d5580001d0182550a1060f00001e45c0420002401800a00a0104101f120700c1021850b01c85014044a81c0300e802e00c0405030f0345451004401041d4100c580b00181d004440c00450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 780986501 1250 780985251 780985277
    0x21090d030c0e0a0308031f0501120207020a05042f0a0f0c0311030a090602100213050d050708100f05060121020c0c060a09150309020d110f03060709061107080a080a 72
    0x3c080300661007502d038000c0000c10011000c840e8200501045035000300c1d42206805d080000340745140c00028a4075641c1e00040701c0041d5581c500d100d900520000f0024810005a07030803100e800342c1185070112141400d24071411800030b1810945525080c80d641303024190201b01c0e02111012011314041d01485090340d820402480c061000340b403011000d44440c044c0c580303801c1d0f009142105031504441c54a1050000021410301d2801c044125101156030302e60080560910900700350040c0d11401c070f1407282c9110599480c00c00d40100b2100c0044c04801c10107981c8a000640d200852f1107030310300c481070560001c0c083c1070603282c1c0909402d823039842c00c07643c0c0c0c1e1715070001013601761340f0000484002c644040c0041204001c042c9103542071012038501405001910382c0030581ea1464106c004101000d282400040c076150490f8100000030028100d130306900380304002501d24074281c020f80002641c2000d54805200340040d03404201c8808000030503001c02a03445140080d040184800100310211000d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 780987751 1250 780986501 780986509
    0xa0c1e092a17070f02070515180a0e01120606090b130213031a01080115060203030c0901030912030506030c0102030405011710030b0414211b010b0a0b21090d030c0e 72
    0xf8400c10250f1144071203070795200c40103850001e8681c003091146413010119014110b8503010b480040e100850071800c03155006000031510700c01c40d040784080d0041c250000030400c1684480c6c0044500800c42085140d8441c0b0000080e1a0b10118040d046a0b00300350132010700c02a0340c002c06c55516010301e1000c4140c3c41e41c0e2507030320b200a9200c4000d40400d018005201d044004e1041342400325603401e8030f0003ca481e124000e03449000040150141050110303c004890740a900700301d140301e82c00302e00303101c0800d0241e0740900240310035031f1094020311603005104815400001110f060310b60586400d074100c50b468118034443c036402012010450300c02400080055030400c0103901483c810598008550b40300c030421890f0298482c007811030001c3c18040c045a401d040d80c2103400d280c548410180c600303900d85040c9800340800d1988590072450304880040c5503440d44000d0000c108906a00304c607075042c078810b060302c002000c0e10f0a070a0b6812204000c0d006900a40c04480d00b503445003441314a20f40e21034009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 780989001 1250 780987751 780987797
    0x15031803140d0c05030108010f151716170c0613050603090f011103071106010e0c03100b13050f0604032a1214010c0215180a0c1e092a 59
    0x110301044010005201d820428000d080b00000127030740400c6411a03816210b40310b60410301c18100c8207d070380891800350050a00410134518000d05498891580d1110010403840c06045040c0850003804800d40340c515060080b6100c101c0381c0b0700090703c00c43c1800c003082080d0340054460183c2c1d1045240c0c0000d0100c0a002d4601a01100701c105902ca141244015008441d4201004003a8110500500007000f104242580080344504150340341d07034990700c0f85c50980640d0782242d410b1b01e030080b616450a291070070b200b01c1501c10640b04035100150100a201450180d0700000b08803881c600d41c01c50103214030030300344e8070038101c6c5401d41c415070366482d842c03400d030600a960141c4101c4151007202c01400c50900402d401c2581c0703480100750001c9951362011002601400c04940d54003c20b8103050481810803120380b4032074105c940c65490580e16115513003e0075100302081c0040d480c4c04c200103800000340c8035a2650005490300340c110710318800a02003910603118806400e02504c5103801c241c0011910780 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 780990251 1250 780989001 780989021
    0x1209060a2601030318030519030201090605040b2a0403060b0a0b041818050c042f0307080c0c0703060903140d0603030206181b0604050d05060115031803140d 69
    0x101c8485541141001044c08401d004c44a48400e400030040000510001c6c102580c90407221942c500c1464924080b80940b07581d0034013a100504000c10700007402403241820340140d02c23000e41ca108041d0490000208003d600c458101010020310042002c50650f13003003e0004031006103100403040c0ca6040001d100d42154000301c07a100c0c0700c2c00d40305403162100e1040c0c1c2000c2018845204060300e40d5542e5a07500c1464112250066459441c1e00d107005d40b0761114803290045000c8041c00241c03010b00e00801c681c10864504000a19a802251028152408444500082d1b02c00303452480c0c2076071241005041001e00c110101704202e03000350b80c100c3c0180044c0c80014400c000205840e465401c0c0280380241c058215040c420040c4e1541000020000350200d0144409442d588a5000000000d0329401542d00c03864100307948400e804100300300031030840d06079007031001c0000e402c0190400482c101c4904242c0b010721081403541031f001281c02010b80650281740a03107aa4030b000c62490400054942c81c0700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 780991501 1250 780990251 780990317
    0x3040b0d020a09050a0b07020f0307120305120609011d040809040221060f010e040e10090b16180315150b070317101503140f0105030f1209060a 63
    0x880480c10b90303222a140006107400c9030510740c50743c2016041c2c0694030511000901c5002010b024420341e4606005050080100d4400e1400300f5000e800c0c0907049600801c01801c2404a0000043e85840d10310344407416220b09203082500b401411121111140010b0b2090701c00500a00c10703106980d0303c40c00201500401d04900480a2004d402d50340100d031400b401407489403424860041d00c60340d0010b6003400045040745d0214081542080d0182000001e41c0400c0406003042e41400c280070748144003170f0141c465203146502000c000007003215070004945012075181b1400c2c00c200042018000c1040c62181c64000c001034078610a550340e183c00c0710743c2d4071160314610003048138006c0c10b0b0480c400c0d80803907170032802081041c585600c401e900705540d409600f16491140c0660594035110b64451100c045003410034404604045c620300c148110244121482445403104401056101007070b180c8011010444050802480c1c40405c2000e1304005c106800b00100c504c0510814003101c090050070000b070036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 780992751 1250 780991501 780991507
    0x50d2403060507020c060315010c0203060c090a0801021e0304110306010611070b031605030415020408030d06150e24071a0106020a0c061b210f0e0d0b040503040b0d02 73
    0x114110081e950024050380945d0815040d5140c0350f100e2130116a4000e204aa850035000f00d171100507610ae03411400007075003610070307042081075042c0340780e0040890000498008500503901c02d038150a078400e050340111041000420f040f45d08a8040c05160828803541d0507601107034051012038036103c0264401e2000900010065044020078006800601a107010262941c80c10b1001143e4038992000c080d003c212000000400384a0400c16040841d00ad080303056640396560800e865813a0080302e18110800d02d0600e001501984446840e10303c1c035403a444017070601c1c1100701005000d07500d09040c50600415110341d0f5106140d0750740108815840380c07001c410080d5100c92000071004050704000705543c043d5004501007070503400100c00301c40e000d25004890304140000301100441a10700140031201907004541c0291034085000328400507a40c41001a490282c012902e168200b907015810011210004000c5548103604640c0180034108407440c0036611500205550321000903d1540b82c0d001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 780994001 1250 780992751 780992753
    0x918050a0f060c020d05220803042304140a0509030409151a0c120f13091e020301180b040e150103030e090f0f0a0b040c020a140303070f050d2403 64
    0x180308800c9490040e00c01400d4604000c00050264440c22840c00c40001443c1f1081176145455480c82020b055181c041c1d80e03c03103669141109085017540c002d004480c03074034138500307904d07041c40d106158003d243d211041900c1d859112280c401401c016000c034242c0c1c042040b000c5100308060040c10444101e034124007242510305613260b148952461030381d0001c02c2c030402c2990341e88140041c0c41c0000c2d0a05455440d41e96130003410340c07140c51003502100340a100139139500062a040a6000000c0d88000c50400340a0500d505d800c10102d101c00d0050318410400403a010003038404540c400c40c182a00900005569060b03404070b20b00d458100c1c00254008075041c4014000c0680c080c002d40f605c003100780c505500f542400d01a00740c01c180001c214400d242c8003e80003a040007100c5d00824803114020304100004101d44070000d482d50b2203450190f130f00c45c40604261403014000402c0324401e040b039035036851042c800d45000300c4466100c400d4085050ba12640d145c2080442c40460070401400443ca01003100e140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 780995251 1250 780994001 780994013
    0x2100c0c1415101d1e131a0411030c031e0109060f2702010e040903231e04030203030d020304030c08030702102301050603090109060e060603150c040918050a0f 70
    0x180c20745485503101010601008200b01d40b070b4040110b40340c040701c1080c0d40d0b0705206c40080c1c02200320041c19464000808055040c2141e4016005501402c4110001880001410703a6011204022030f0140d1200c41d000181142c03104050341024101070011440705036a4842d101501c02142000d2555070303170354114000d0464000c64150450140c844405101201d039000a4642c1002c58006c90065450344c2c994010903120304130030403c00038001020300c0d1207080620403c03016000708441d01d55020042101240c80012071050724200d0b07034020000c501e020b2080b164080039400160007181400038542c03607040001c184101440c8a81d03002c0d401002c0ca010440610f030700390340300c1c0110154a500b01c1c40008803183c1d08954054159401030b02c1d8595283c44110400303004180c8528080c100c03614100d108050602c0203e0200d0060400303e040703444840b410006001000c20940e142c03503c1540411003001031050540183d02031124994014162103441d40302c16041420035401211242c40710841d010411035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780996501 1250 780995251 780995279
    0x3200a0e2e09120602131e05091b0301031e0203070b091528020c1e091e010909030203190c06050c0418020309030c0f030a02100c0c141510 61
    0x62500e008a00b96142c120b980501516250015242c0350700080c80140388096a0f0188008020410310359000c80300340c2c0d04021601c28035024442c403564185011549042c1100401d240c0c1034800810a07195034616907403010700000c4540e0301219641e0340925440981c0e020300400f0001c0c0a081d078055500d11286042200c5441c2403140c400180704140544058804201148502d00c0c1104000129800e01003c00764940781c003804a155102c5038414454540095010000c282c00100342c0b040203043d100c0310645030411018103c4107460325600c8004100943c85600710b03010040c064016030303103018102e444084c8050b1440817254003260b07504540c0743c20000780e441341d113611045000c682ca00302410014083c481c4003135040c0c0c0b40425070b00480890109401441124003400c1031070201d441d00100c94604035142e8000c204508090301035030140d01c0820425005580c0c01141c075a89000f60450160340e61142920104a064031600ca801034403040c640e89070041c2c41c0908000c84000301c1c81c4e403610350183c81c080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 780997751 1250 780996501 780996589
    0x414070e09010c08040c03110103140c070303201e0c071716030302030a0c0201050f0c010506090a020703091a070b0106020313080102160b04020d0b0408030406050703200a0e 76
    0x1191301010000070a003848801c00607a0703448415a140c0311100c500490280c00010350300310050340d44005000041c100640105200d9220361014031034104850f40d0106284990412000360810800c004030030425000b81e11080b841691044034184601c0222040c644a0a0303080303011400707000301e55800380300010030203c04d900d041c80400f020740c01e055a4009499009140b0705c0303014051080503400c00c585c014401d84001d2802190b40d180c4503440c080340280601001e65071180981d0340c01d404210400700074003c5490180d00350729070110301843c00079110300740d14000154507a90542400b4082c00601c0e12114a8020505da038002d6450706200d19240d020124190700c645840e80c070400c403074000e00c440c05100701901ca8000d40300e0803a03a512400403c030040840b0000a118170b1104080000300002d88020f18010340c0504000c11480e5a5140260102c6240b40c1d00c441165003104104802d00400e00c0050882c0002e500e44221001d00722400f007580032002030358007811050040301c1400c03100d1441d0700c08070510b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 780999001 1250 780997751 780997757
    0xf050a0f0c0e1305100b0a080f2d03040b0d1b17010b04030302151803040801061e0506031311041a13050601050301060f0504030804030803060901080c0f090414070e09010c 75
    0x80b88640c1c2c1d085c2e5484404111140054803014181c00d25a20660308200400420041e10108014194074544540e815000c81c0035412981c240c5001c5401c01c1410484800c2540004603d410304001c41210039803c07000c41040c02980b02c108480345040007030f040001ca1400c90321000da0201c80d110200806c503005030044c20f0070710001c0c00b0400c0842d0b40040c4140d1300030a00140d20003a91194100740d2510440b0000c0b424080c0f00001d00081c60712015400b10b01120721a40d10780c01c00c0c21200c059607022400621034168020310502c081000480c0055021581382d01c120312890450304c156000c2416140d034400700008501d0001d13003520321f5041c000c1d03029190742c60a401c2048a440c080002030003502040c0205e00800581950300c8100601910445020f9a0002055902c442c1d0720b107851903565104030349031401b80540400020f03400c100050000c1c108036004003d4900403940d4818400c02c110010004d4940c86064140d8490006043c410000900340c0380c6003d03100c5150800b51a400d442c8251100010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781000251 1250 780999001 780999031
    0x2805040515060a05010804050309030a080406020c041b0815030615011101020a0215040602041e080f2107050312010e16020a1e03120f0605011116030f050a0f0c0e 71
    0x401d5070741c4081c0c01d0035507409007044440347d2170341d0030520300c0c5000e40540c036034040c03040c51020740510000c0c0001d0011030724940d0031200058085030900003a1a60180042d00401c004040840300c01d01030380760715a00c0341c0344d0703d1550f410b5522100000e16200303040e150344201c200d212050b14243e50344103d82c0004800721500030751405c41c40003c001e41d03804440001182c000c40900120b010049503070111340050403110040360341e0b48100303000300c171541d903032881403540c03d2141402c1c2c0d9000807008070700080e480a03040e0403491101c65142280986500c0316400712018002080805050110f11810b0350203088801d5403203401e443c2c000e40c580102c01040e107188003994004a030610001d4000c50824000c5290740c0e45201c0b00300d80500e000e5a400807120016125581481d90b01a41442e00b03611940442c1d000340e07544015620310000154031204130340c10350640921681030601c04100782000403c500e5200302c04440c0c0c4151300d920794203214441940700310f0715201860340c1007180c08007200440790401718000359148 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781001501 1250 781000251 781000261
    0x21b03070608090a0b040b101e0b13080a080301090617060c180904052109090402060702030f030315150408030d0902040e0706030f06080604020d0b2805040515 70
    0x19403038000384a5503081080360400038201c103005010b900c01c01c540c000032803841410589040400031408541005e00807040d81d900041c4a02d010101c441d41a154400381ca14441c1425044c8065a105d04008550159140b500045500c1c1c1000f1184d901030240450507125410003ca14059922651200c034400500600800c0c0c1c0003c00b0607402e400500600019544248118005900c0c0c80e400c0095640121600e08000034454040740345001140d003402d0041d0f903034801d40215480c0e80a10040a50403009040006005003003000081154134001400c0b2055058800c1d002891a40704545401d92600c000200701c0301c90038108003805204100d005820f007041d0400820f903640340075081c152460746898451410a40d15a0703840685001002800d4980b1641c6070400500a8810203001c9805a4034008001601c0e10005c143d050049500802d848008006a290a2034110780548080000900e05503c0034408406100d035040c03881180d030002c20140340c41d0401e2400e2140c05051020701e105540c017004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781002751 1250 781001501 781001503
    0xc0e0c070b0a0b041112160203030108120f04031e03020c01031a0402090f0913031b050705121c35010b0f0705010c0215160f0e01030b100f021b03 64
    0x2d40c404a02e150010b00209608001005840f65650f801203d1100056000d070050000c0d41c40c500c40d01400c0c0500b40e5809003d0812642c0f48024403982c3c00542000d00c00140b5481c03034000508035403511400640c18641c0b07a8850300840703c10121642c4030301c140e030400501015018007000301c0800090070b00f0008038081803100e0b050381e240d02414911556001640b22500c0c1d4820b103210300d24031000b40211010b8a0004c5007400158030803903080d80484d4030b000c0300046681a0a640c2c4006650080107171055510300070a02010742d91411480c0c5960003503400240120314219494414100c25a48180410810942c00030a94828140356002003842404c0c4076041c00036a01454110780355140c1c0309642d04101d500d00c40c41405001d000420035428031003c9461660300040e00303d0500003250200482c2e441d140e01030b0100c0300e44500d2181c08500d107080c0c2807007024080c100c01200354006040200300080400001800f0010100481d07000c20b2130003070200d90055041021030640001c1c85403059074801404002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781004001 1250 781002751 781002773
    0x150e01030c020f060c0a0314040c0e220302030a030c030e0a1104020906030109050a0c0f080609060a0b0d24030c05151201080105040209060105031302090c160c0e0c07 73
    0x58145925959007011440c420843c001c2012580001c1e2443d41c20200d0454001c1d81c45030300000c001074209050402c0e0800d50001c0b1034016503000d600c0c10555440d1568802c90400002c081c00042da0400f003196194000c00b001c030a410610907409140da0310010500036003140c68100c1e400c070030145040d00ca0070280e100000c03598460b0781c11440c9680e000116800050181c4a0707001d01c03940014020000180700c60850b00214024036035031105000071003074054102c580755000d940a6000404103408540030341000030410b0307088903018090103445611a03ca075003141c2d000582500030076a5034002d4200100407107080c1200160042418441149140c50f180040364080c0203061244080440020002c9040011580307841000c9980308070960f0756440040c000d01c02150160300402400001803071359031194040301e105000702d401d80910245a6000d00170030220013007400c10402410011590201ca00300084070b40d152180c203542211906000304002c1c500b0f400b8080d0b111161051207054000f1750340310b0036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781005251 1250 781004001 781004027
    0xc0d0f05160c06150f0812070f030815060a020f06070201060b0d021b120a26010b0d0902030118170a2012040f032306060103020714030c1615 62
    0x1540d00014981040e0703000700b004d8960008044080703407001402ca4000341e01c1d8411070707800e00182da68154031705020f5981d51160800082280b00e0340b07400480000e0050180d1504081110705030680d5551110201d2526440101c1c0c03400035030f00c07060896011940812005510520500c0240006441d02c14644d01078025200c10181313041e000b00311401525205882c0010754104401110b04103c96407a0060041d40040f440c0310002d480b1400c5000c0c0400d1500070300e00152640e00909829a182a5122800d030700101104c00407607442d078182c80c0240c1d9090003500c0380c08900d00d8949800700c1f26480d001c00180020070711104034000c02e10082a0ba250003485181c400681c2c02c14001e6500031507500a82056241007101490740340105012900c1a000d20b0708106a03841240100007100c442d840124182c07414900b407000031750094000540700e500c02e402600030640718407441240c8041c41c071500d03821074000e410b00b02000c2c2d1000b1405d00307600c0000c886603002062058030301e80d6003051100f4018024440703200c2c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781006501 1250 781005251 781005257
    0x30403031d0d1d04020d05101e05060306040f1803050309070504050108030d0e0a1a04140307050c041509020435100b010c08070303060f05040c0804290c0d0f0516 71
    0x3d940881e6032a40c0c0c0441d003040e1a010750070040c51910107002200010750b80120b265220f91110079a85040088118000761280200100d082d070399404200302c0034105400f054140c650300d680744a04c1c203003000c0700c8664219103e40c68407502e070702c0d00a40192800203950b01843c450303030400d00100140280401241c29031521104003040802800c03200e03a107031000c88000200f9040d10b40704406115001081c03114012807003218503401520280c83c005940f4001c9100140268001c22010100c519050784100f0300020345126030306c0d015a695000204903045940505070180c40239600d0300e00d0441046041c192140585200383c0120840c989103a994003109407440c0e01c1d103a42f40c8a90550368090100c4401443d48080c100d81d84800901e0f0040c003410b03281c031400c1d8000d411594045824602402400340904080c0d403075a03881d0b078031a00c0b0085001c01300c003048a910649400c160040c451080a642d2244011504803582d035546078000000301c0355003040d030f4024071303103041c0074008401d681e44c0700300c01c0c1b040d0645 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781007751 1250 781006501 781006547
    0x50714010209030706021f05090c1021020702030106050d0b15010306150201090b1027020c0d020609060c03060f1012020a0e030c09090d140906030403031d0d 69
    0x4501402480b0701075030168944281c28000690960004010030389030005440741c5100715151004005441e8152894030841c1c201211112142c140b80d20002c581c6071a078030740705601103140c140d44001112940c204c42c050940004201d42541024003a842c000e1005455440300303030368240c6030b89211490150252407480c940c0c410f049502e0388690030060141c05c4100c1d060080d19005607006c2d0080004042c01c85400103e54001606040b8045018048841200c500800f440001200f44070282e60b40c45204982507080c85080c1c8201400c01980042c50705a8005204505008200514000b802041c81c09090020802c000068480b0070301000400004d403480580154103400a481c075014803034200d80054808104201050790158021001804c10f4041d201301394442801d000f02d08104445041840e03124030300402c0b11911482c4110514040a0311242c10a103081d80010b40da03070300c2618250300180d2500f600c000d002c80c2c2c0c500901c108500ca100102801040140090900d824140184402c00c3c829 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781009001 1250 781007751 781007783
    0xc0603010501141e04180603020105030a150e0412120e070e040f06110a0306080c09151903120f0f0e04050c04090204032102071202091305010f0b120a02010507 70
    0x26041c0c0360350031144d0080811010041141a840d608584100d040c444641001d401c40340c6824411030003500d0301070303403614550f40d90041c542019021806400e00c0007110120001030321500d643d20540524483d0f40c000c50982070004000f00100718580c40151410318107080b1280001e0700042c0703030341298960303010a01c5581d26800d1501d00e0504401019182509150310710504001060040c0017099541c6c400304080c680303c000f059036982d101c81050341c001860301d010031015005215200060200203109510040001100d48170b000c285620465400c280c03d05203095a58201d01002c40005ca00d02e000c5180014243d0b004000c40314003684a40a00c0e075030004628140c2c6000f08a40c05400312030015991241d0b02d00e07100320f001595010b1007900490b0707041795150940c03022039040f040f613648652000790000b20b6020001e90303030350281c41000c10b41111859900060402c0c05050101e02c0848800584003c030f600a01c0452400d03420800c21030f40145103628010703a00841610744441e040038400c02d20101e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781010251 1250 781009001 781009037
    0x605101e03032d030c18050108041707080c0307031b02060723010c05181c030f051201031202100203093c1e070b090441090c0603010501 60
    0x4561501c0c0200c01d43c080140c5001609500a106000c0165540c4441c40c000c030040865030704843e008444c0000d03010004140452050b070b55180c0c0441c0050f154a2030619540c9c0d400d0003a40c041c07804080f0039080030172507a0615411062082040c031030306110406080382513001031114412220300074001e92050b50580c41e0007a9000d00c82203d040c00314020010030004540150064201050321121541050700640141c107040014001e004060002c0031046002c03507a0945495481111800c2007010034441699002180840c3c64000c41c00f401000d030000e03030f650200030309140c1e00a4049990070b004009101a200700002c1003080c1d6a03160102c00092025107210003200c0f030f840440340d11020780141c0c14042030070011504204040c1015580d5048484c40030f8602d1300d4580a01c1660000300050280b840c0504241c1c021840d130f4404040c4400c0c49082c2c80c41d000305c018801c0700d840c00c98403000210703e008480e006d071340042d042001c590080c015200e54000040e0700d440305002e62410000c40081e1071b81e21400d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781011501 1250 781010251 781010297
    0x12060d06060f0902181203070f170d020415080c1608120901020909090c0604051c2f01020105090d0c17040e15010806010e012a0605101e0303 62
    0x320424080364903030f502c140d404040c3d0011041e0005c1d03808601c000325400c0c80d05029160b480314800010f1801c005268594183c00900c0480949044100d59440810100848020040d1541b401c030016207071030910a0b4440c2e00740b09890390406000003e8140101c1e642000140c62031003911b100900c0740d00701c031490300c5c003d58060020513080c2a042c8105208030000c045d005090b603004180c60804d4a9a1040d120554a40b9141400b503049001000140900c0c10801d00b0121204821034026004000e50307641c030600c140000201c03014084000c045529000500d1141c01c8100400344000d10181c1001d212160310b03175141d0b0580d10180080c1d08511010412869011151201034194454445503110b40c00c1c071241004951443ea1020741b80039036403566000d10f05d001d015600c1a522140e423a0600001034030000c00444036030f5422810591403001c2c00110142001c0d44600c04d1002083d03d0403d161043e01c1160303103402c00001803d014950f01c0001d40a201000100ca41502d81410b56054070f80382c0c2da10b07001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781012751 1250 781011501 781011509
    0x1302030a02070503070b07110a17030a0915090b0606042709020d0309080601060c030e0d06110723010e030d05040602091206060a0609080d14040e240612060d0606 71
    0x3000100e03245040c81b51b4001000d210301000d40f40ca01c1322485000c000c5858182502d002407251010703024451000b10480081d540c00109684001801078007a02c6902c28002081c40705841507883d25400420003034071507110b0b6084003082e00c60605281c2490074000c14000c04002c0b290500c0001101c000030700c4e440713420003c010368000e05492110412801c00800404850283c4d446500c989000020f0707141c0300b0401115083d8140e514a1200c00c1200208102c4040740041a241c0c1034441e001d04403607c03400030041c00740c0b5108014003148541c2d190010349e900030f655083d6044130b0b490701038440c0d5601c1000c011960040c141e00d100080036034981ca04803000b80600c4421940080d010080e030308a4080002c0c00701d020302004c030780c0100450380c4e41e0800c5640c00c07003a01900b28290017403141294581c0c040d141c400811a00942c500d410a40c40b082008001d1408441c404122107480c801004402d525001d400301c01213064455510341038491401302d0103074001808090048a07242403034010710015502904c060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781014001 1250 781012751 781012753
    0x22b110f03040302070b0a05090409032705040501050d020a0303050a270305012a0f050706020f0304021804050a030c110904120e03060435131a091302030a020705 71
    0x55840c0c040d46203a103400840e000c401601c251480030442045c1c0c08242c5085081c0c664456190207069402d001c09411800c0e011800d004132114240500f08100005140d004211b20310640c006103040e080005450041e40898090580464004c025803111003000080d00e8050501d244d40f01c241034422034405d0360100e200c0e0319a1500031240c4902c19081006201168041e1000b801910f550612a2540c0d034140302041504080c42100c215225018034131464a10b038042c10300c203041100680f01c0c1da0680c3d02c15445c400781854000104011454558020080804190b01c00160345c0b40c13581c0c9007642d8200380300014090185640051301001080c0d54000c441200140141d401404c0c0362812880c000700103084240403030403841c090181418005503461095400c5900c0c040c5e420f0180741e9500c050745032000c2900d80840418041646414190000d10210f4012000d1100942c43d1040c00704a140d1030007011040514100b03d41c100030782d141068144602070300807005a0329190500f50400900c10400700900c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781015251 1250 781014001 781014007
    0x124020a14060f0606030f150103020927100303050a1d040c021e0c0105180102010b030f0f01060e090c19080d030b030c0f01080a0209030703240f022b11 67
    0x5070080821201e0107440b03441c03260b0800b0780761501088014002110892002044803002995200441d49140104101030500516091200012821000c00d194001c480c04000e20805500281c1d04500d044c6c0c00b2540b006604100c0d821641c00804510414103c0000c0040144000351002c039107103080001c0242c01001001809130586001c1d45850343d121880201d500d080d80d904204990104d078143d01d95005942c2c580c900107800b05107241c648000c004440c11590780e003443c088961404c201548001540f8030003000c1883c0300415660035a0a0b0b508943d444c400f07079000344007202c5000600c0c8402c03048200c0704c4001d003040180880078002c1c0c0c0c0358050035603032140703512040180750103038805084020706506580341e640d02c0100307000b1011004c1c0c81041c00101284002011075100d5809401e80c0c11006060b40c640300d68a4586103e0340410074802c80120a0f04503c00c0010000ca110b01c511010302c4400030f42c180302e03c598100000700c9444c449584c07000c00303500721040405c02c01d07806000015130b026202e9132 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781016501 1250 781015251 781015283
    0xc03050a031a10081015090b1b0a0812150a0b0d0e03030709030203010f0c02070509090313260a05030318070503030a050c060108070e0a020a030209030105090102090102010b01080124020a 82
    0x807030b240041d42c140c9a8140760a2006c5203503a13045070401c140450645442c12500d180c500000c00307551203543d50301c8000c121a04141c03030f0301c502807000161090080140a0300c4102541c1003c000c4840035203c03620301c1210b410f420f2142c0c1c94004440040300c0c440c580154507940003000c00350192254245007000750000104000703003142c119045406a078000c0d4001c0044c1d01040e0000812100320756201b4015a2040d04100801d140c0f1a84050b44407120900341c0b418900048903042c2c1e508003d030003108240251000300c90300003080034900f42a940101008002803c0e1940b24241c491101401c01e15007c242d45e00d03032103d281001c2200000603d0040d04036543e80e1480b54004113160801c000844031406142c0001580f000c0010300700c030655541d403c4900f156140c0a485800942c4000c3c09d14081c541c0034010070b949a41c00388550342c4180584000941c0e515985000242114454082241400407040050000b00c3c0f03440503045400341c0410001184c02c49481050b45011202a0010500187c03103005031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781017751 1250 781016501 781016507
    0x60a09030c150c0f0305090606060906040909060504060e010b1f091a04080111180d03141c0b03190618021324060e0f1c0515070c03050a031a10 63
    0x1030040c00c2c0c0e948480c0344d8900b0b004100e0588009039035214040e40312030041511860040000c2c8420200100790501c0c250751ba041d03a50136540708c0c82c01601e15617612020401440051300501d002009450000c128901d102400546c01205004214601560681d009508907000d54414405000080d00120155428021079a0a54030500400344a5420003401d170310032401c5501503c1c9201c5141a440181200310024040c461140800941c2049845c4a00c000349200a800400e0f180c40d44100003001d020001c0c0400c0203413a480c482090080d0b01250030b0224250380d245d4040586075200001103414000500c1400b1a244a135001035400401d51443e00d041101c0e60384410400340141c500902000c032107038a411803032506441100003094900341c00319401d141c1196850304040c1c0043c0341115039044100c2129090344120000c481e542c1c040c10031281e081c0150b141440c3d00108a14042c4100c0d031141c0e80052260141d0240c1100345625001e26000380012001080e000c40e50142c9102000200a0001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781019001 1250 781017751 781017761
    0x30f04260315010c03090612060b03070e041103090a110f180f010f030c090c02010f110403110910030b0a0b0409030305073b01030e250611060a09030c15 67
    0x502c140501c0d9041c4125030354003c0f108010083e4154035500d1b2101d290007425070300107410300e500034016035941d18085007a0b048440514015656a50b07401d07000c00742502440121480e00300c21482298050040200182c0700044140c0803d50022518180c4000c4c6404500151450050a50310030f03100882d5104080d000d0008230b115200d601c1e45c1600d40c0e641c0d86106010341c9800e001c060120305801c03500f030040640a80050403400c841d0f02c000035250946d0341c8500c1c00c440d2801d209191384000040d040050119000c1c08103110f542c200d4040065091035404502041c0780c500c801000c1e07200c50f00004402004684c495401c0000181050100051500d401001401d0071120400811580b82e910001024020a003c0b4260740d400c40c8101c580c010808040351b50104091401d0400d51141c100c60036110041c010340f030b1000703500004400c981202d6200140b4245040d0081000c04c001e40c03071030740508080000c41640092444c00001501d00550400b140e400041c000007429006021204000d109165440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781020251 1250 781019001 781019011
    0x702040608013207051815090114040b04050f03030706050a06170c0108061e130509070608130602070201050f0c1516080f060f130e0c0406060203030f042603 69
    0xc81e0f20161081e20707000003408032129031000802140003e25980c0144000c3c030303510491389003400f288100c00300020b1050005011144150710049000744079035070000402441c80c0d002c4c450725403c02c0d00740074518103207000e0391042074030034103103000281400d4a00b40102c030260741c3c00c40d105010602d8604440006048544260690000d030030310112040034000c14400c1c40020165505400c4c0e841c1c843c10084414050440c2c0e0900f9124409007203410b80e0740450075100640712030300104503443c0041419007030014603817102003440540c170b0802041150300840291150760200c0c00503240c01e4107000403542d03405a040c3c1c201e20724000040544020100017480040340c0d0780b80700ca005080d43e858215900c200d09640741100071825240129145451103001691f00c400058925101654050000340d0405024000c050003e552041210310009007072100da280b0b038405943c00c0c441c8500d0b1510081d0b41c1d100040049004400c0302000c1001c00240000703882c0c1442403448504122030000210540c15402513030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781021501 1250 781020251 781020281
    0x606090d05060c18010e09040f170a0305100509061507060b06070602070b0901020906040504091e1a0c03060907110f1606090906140907020109021c0506100e0105040e03070204060801 80
    0x5004c40407988035002c040c03014038001e411010035407655a9074072080c0503800c404484003004140420030800c1c03c43c0c00f80c408002c49031703004100d80c2054000c0302c81031901a00228000c4810808100c11a180c446216840d1190356454075a110801d0401000510f444a180c1d5403203070340000c10302e0510002c0d80142981d18003407103980206445a00f0014200c0c81100d40b05500300c00705101c104403e142585c8504105401404c0b50030020004501d0742c404560a003c0c1242c080241c4d80650b0074101007031608640c000024440140b4505209000894041c4010602000c000c0203011041c070885090040e08950382c503080440308450004401c0c4000840d490280d000098038050380042c00801794045d000480301070303003c4007003060440d0050020010300104448195901c0c0c40c10000140c440001031141044088501640308107140303012400c0c18000b620514030241c0026082c8404501d030040390741180d5046800040c10180115164250b005101001e54080c0c40c080d0001085441034100c090500c1c0d14072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781022751 1250 781021501 781021537
    0x1b03060528050906011401050c01150f08060c03180c0a080d031401050f010e1c121e02070611070324050106050a0206010e060a17150901020c060606090d05060c 70
    0x5000102182d00442e00b00d14264400300040004246051000190002c18500f66140081e0080c409003996840d810b000c820b400054410800d140c0591410000b429038040500154101241c220401e404060034001820040864241c41118204104800400040d260f02c00f501c1d92941200e807070302035100c10342c5c0105e414010b40305105c48010160505175000106141c0d84044180f0044860031900c494541d004001c51a260800701e07551500203802620032a04000b2540b00403030000e02030090304480000f24044841c1d0382c51300c0c41e00811410140ca6480c540604020b0210001601d030021992024002c1d250b0103083c2d40001140000030340f0100c01c61202803200c1c0c1d0340c483d000c503418442c0829050068020b00014000ca203060407615030429401010914080d840f1208458054043c10240030541e01c104070390502403e00400803070340141d07840021414010aa40e03800e495200060440f4440c000008100701e559442c600441200d582102c01c2f18040d1802503001c0007540d00c1780c40c81c040800d040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781024001 1250 781022751 781022821
    0x6060801111e1c1b0903030c0204050a110a090801050106110615010207260c0f1302031902130e1b04060806030a0b090c0a140109031b030605 62
    0x140640d110300400c26890502c0e0902e035111a40207000070340440071001804101c40c0c1e00142c0380d6004140014507145000461000020f1036210303030381d070200512003400201041080801d4010352484942c0342c05460101381caa544441c088020308241282c500c02500205030081d070759130700610180c01e03242c90100030001d69803503200c250354640031035200d0111130703110b4000962510860b000d01601d5080600403604110b03210300803c1070404050345413048254080c000031082980400412004d800c0c10f96080107014151340c003140000000a40e010300254001001c1000c041052011014080364054119140d60a0140c0b41c910f803841e074490780d2240c0034140046000401d00c16000060380011062003403a00e886d014044d0b440301001840c20380e00d406080c114501088000c40c2e0240304803040d4000d481400070400030004810040d800010f03000b081c4e1260300c0e0035a42c00c400420306a98124403c514504c0c000484060035003080e40006103064208001d01c21404807086030a410a440e00c25107076464051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781025251 1250 781024001 781024003
    0x46150513020304020d02060a0e03030d1a120d0c021504031101080a022703030706050a020306040f09080901181d0f06060306100f110105131716080d18030309060608 72
    0x140d030003a511024405891780145000c4c40101003048003400c01d1030300052040b00090447d08880c02c0c0c0581c40d40c440000c6e090b0707103a1150325607043e450116421030000c0000005580d13540500c440c2103040c03003800c140007815035a0740403100803410039008045a030f8648a02d000b041c600c00e03000303500e40071030f15003404a01c242040f4001d0b00c410490b004038001400c0415a03054800e001405105a01808200414008503040340511440703200581400350782ca0426105000840e0b000b4643d61101500e003003003c0000400950403108521024a0040c0b030101803007138815001d0449900040e020364110111103001384090007204c0c4505440b0580c0481d5a58042c103101440c8400c03600c1c181d0180311600301030a694001d041180300c0501c0381c074040030440040c000003401c4400994018000c254501c01610030007011080e400e07944940302000324203020389401900d011981d65840108100000f00d012140c4025070f070321480980c2d02a142da09406045820060000d1161107020703644c19052200104540e20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781026501 1250 781025251 781025257
    0x241b0a0602040e090312040809210c280e07030e0312040201020d0806100f110a1a0c0427090f060c0905030c031011040521064615051302 60
    0x1100050722520381d119910305140e6801400066440900c0820403450314ac50041038040d0700001d40020452400c42d2000c020403007400030440d000e11410408041d003a80807860301d0030110b481d662030034101034854480035000782c44650100c42c0306110101c0c00c1204800c188000601580c002e809441c01c0c800680000c07182c01100300c80603132f08240d02c1d40380e0f00c00251107010b49501c2c0d10400d150800344101207420303013410305d141d003101519501e49003401c4d109448040121903410401c504005840c0c02d14204a03048072803821a50888502030301c2410300c1c01c003482c50304090800e1f94820090701e4070801c0c91410900800032001883c0001e03040e2031021815042c0000c440000e600300030004c0c014103069002c84406880a0b20300c0d0000c03401c09100000341515001d100c40d6803101c00c007010310012100c2044251034020014400c160020481110b1005001d5921800c8807038081942444e00d802440d00244078010841c0c24105031142c58070755000c07100380c0e4180da003030203441d0101c4040c4014171050080178140c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781027751 1250 781026501 781026517
    0x50f0c1e2106070e0d031e2a0c09090b0609130b2509030312020702040b0a0f1e0e07050f0c060702011b0c080405040228020a11241b0a0602040e0903 65
    0x16440291030004851f00c801012080d0510785810310840c441901c0d44d0782d08400c415490303192607800100300e030304100e20201d1a1028041b183c5080090b1400d540380d800700c50402800d428014604800881c004112a110340c00c04650407000040c81414210700b801025140c02024002d00c01221218201c95131144d5400e80480350503640d01d207006614418034500a40c00354074102d9000d40ea40710896110b0f00c1f4442003d0080030302d40400f4680c2441c107411a0f40a010340f00705250046410802404040c003421200e5070850542d1400907110b9540c1005280b442c454001160242e22411080020640d4150844039451505210072140300d41d10110507100307030220220080a5403802d020a00c540d0030540e000c4c140f9051101460641110304000b1b00c00c0c45451089040b0050300b00c10801e00034003054403003220f41e0400c151f5100c08044201e5080300c07400c5a41c070380c01011150303000502652400c3c004100c4001c0b240c40c0d400307449403007401e807415000940c024458641d03984483e100003415003001000780d800b26 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781029001 1250 781027751 781027757
    0x70c082d030a081902210406110f191106100503101e0f06050d1505010b190c140d090333020702030102040e01030807050f0c1e2106070e0d03 62
    0x603445500c13401032420003030540c4802ca035909114289042818a249648071441c00d00f4600d02c609203400c01c00c05a0301000c41741521510200f0506040c1c401050407503462215260700f800c10a201c403901192011078602d00c135945407050300c040c00120308005800c0c00403203030101c007260280460150014295005244504590192122042d583c1da0303154000b80425001c10200003070f00c139211fa0028402583c05034040e01e00c044440c0c00391001d10003d01c80c82d4003419002c1405ca0a1098030f035000c499000a140c0311400300110000024200110781d03070000c1c52101004252444403071000b1000b450302000d03200a0f51402800c41c585003112f8000d44080c03040c11002c100b550525544900b141000c0d44c01742c04103d0b01036508110025182d02100c50b440e000c0c5120f8880c1e641e46103c80d0400901d003951407180b4007080d411285891806641e01701e890841d40011900c00240002c51100194200c0700b6444001c40090703ca134150100f2403004a600d600c14801911494020b4031424180300c0800c000746002004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781030251 1250 781029001 781029017
    0x20d060b030a060203010e09071a12040f0501020a051e0f18010c0602040b0d0f1a061b010c080105030c0f01020c0114281805130509030d060b090a0e040b0606070c082d030a 75
    0x500c42002486533100d03005501c1103803c0049551a1402ca900456840c40041c41c0410248043c000300681012611540030741c0a003003800090208506208489804240311020b0128084690081101c1c0c000c032900b00c00115226652003140c101190f10206003011454500200403100746054400d041c1c44600c403407001c64035240000144242940040100c030750004c20501040d650410074028011007659030b0b0788000007545003074281803070700d80c40c0c2c284036104160144038880b20f80d0b0f0018002140000900e01100b440760704a019402c03e00c01c001d010342055003140c0c00e441818100c07004c5060403140998460410701c4000c00b201da0640e00b9800340d242d0108200022801c50384041d000f49811680070405c4d64681000c0707049120444034550320a0a56003008228030715140380000c40c032402420365950001c09442e290380c4080500c08010000e910904012601c1c0c07040c004040358001c0507100000c00c5a11150350440200c01c0d80304091845038042040b1100d001000401006070b4080e460300b034480c022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781031501 1250 781030251 781030267
    0xa05070f05120a0803091002031f120314031b1204021c0f0b1e040c05040e0d02120d1104060e040f110706051803040b070c080703020d060b030a060203010e09071a 71
    0x1013503a0000e0300f654181c4c8a03503003429000344c84510044d8062002981002d299404ca44049002d00342c1c42c2e8800b10045040747c22510102c1e81060b004010009003010003541d0f99108480301600841e1440b100508600100b9503000c480b482441c0c40f80228001c99604080902040031a80a40d1444000a02003074100342d040c0b00041081c5040c3d500100c00020200e50307111054121150b000c0203c4060310f03007500271602003003942003910a0710700c14182140608021030852001a50311081200d000c02e5041e00060159a500f08a51140030b2142c5d50b280800d03a0350b5038400c0014905885104dc0a20139440c10b001c0105800142c864a2032081c0008801401d100c0356403940750040c90b00400340c0c0840c0304c00b50711044030780c4404e0000300003500d900203400d920f81000d41032107044500d090300b116405500000091025a4400c0a81c40c01c4541c01000859600401e01c003090400c00c8049009000c50300120011a4903506900e28030301c105991001c640e002a6201d8a803e04500f0f01d0104c08064a01001405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781032751 1250 781031501 781031513
    0x170c011410060c1b17010c0f0f1d061213140102030f0408090a090c0c15200d11040320090402010e100e0904060603031103070c0b18030a05070f05120a 66
    0x2c15010420320710340e4030450b540d0122a112022000c5ca41065035034802c1c880b00c03400c0d00303d240019495450305e81001c0c20a501d580c0504805400304503d05500f2460701c1942d0143c0d150400ca401c2c90124107424882400c1c0074422044403017030b4100407100340729000c43c00c000100052090700c3c810034111080c400c2c41c0d04c81e5250601c490384024941908948000408035000000c4d00507400201c00035036030309901c5e00d00c0307062200c140303803483c0310000125042c100d40c5442d041c1192905400c5010400c5e485035112031108140c0d004000c1500c032400e5000740070030000244100c4440c003201c55a0900084070700742d42241c080244d201d0b404c030f80090105034040114800f60030808480301c41d0307003102e007030071020054002e0002d18040c500702c8049586940b034070302c244200350303004203a00340d088103003401103081c140301c0d03610301a203c00180541c00c040c10f80402c508007241882e5452202400c1c0103025641030700020b0402d03d807640310354002d03000081c10b1080b0000b0503041043c801581079801c40040d0105080d903540700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781034001 1250 781032751 781032773
    0x6080411150d050c04140d050307120c1a1602030a0c031d0301060b131208030a0b0d1b030318030201120e010209150705060a05040305070f170c011410060c 68
    0x1c100260030510888114401c40e10480740940d6000c41d4913501d9618042c0124441950361034100c0c062020a1030b43c000240000082e990420350042e43c0c0c08000100c81003c80da500401a005405010780845184500c0d19043e81a4025001894064450300d4212001d0b0781e60301c0780c141d9401c0042c2c4c150307070001d010078884c110703051481401500325800502108002400d555194206d80e4180b1000200c240c0900481106200200050b1209030105031407a22011414040100004211600e85a031241f007680d60b810b84081c1645d1248482c02c288410701518500500180400c5000c92000240803c20301d0880c00c4000c1102e030305949003202030510000b1710307000e0300c10071800540b030b0340d001c0c0104c005503540d0704101c910090a081d002502c2e004142410740c034154001d4035001c4070500d0002480040780d0f0040454921540142c0046158501d501c1d00d0168001404030f0084c9144001c203a81c40f02a00c10742080840c5078562001c1c15664039540201c030704140c01441002c000c90156000c00c400650407480b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781035251 1250 781034001 781034029
    0x703061d0604060f060201050a06080a0c0b0705030f0403050618012c0102040b1621090b09010e03060a020a0206090f3f0408100b03030405040f0e10051006080411 71
    0x1040741550b4403e403c01c0104c1c01d40082c00940d440300c041040c074222900c41c00000f8030604000b400341242944072509a03007010302030242060720000b280c509020702001203504918000c0042ea079603680ea420602d0700c0c0c200503101044281020641c407019400140624401c0e003411001c37000340410541042238940c000c00b0704070403003035400744030000c0c0d4861808003400e8040012011542d020ba00c601c0d1186146030038044107207a01180180340c1c540c072a4020007c500340c07000d02035401c1d40c502c0b02c000107a942810303200d00c00fa4035102d114200000b10b105a0050502861260200c5020341c4a0240c140d07100e20000003030300d41542c03005106100c02c04081541200040924460212547c0f00103610081c10002088541c64100d0000d8100a5031b5010400c00c0007540031084200b258032480c0000a03100c0c8203e105d110b00c03594030b0f4001262b040c4400d900080000005504a8007800300c0c500400b4064481100c82c416071440410380020624002c3c0b070418402c0d6072000d41507002400a0041200031505521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781036501 1250 781035251 781035259
    0x110a020306150d02030604081e040f0b091206010906080c01030e0606010810030503070f0b0702030c100506180907030c08060708160504031a01080d0e0f13020705030a0f0201050703061d06 82
    0x6801c0c80561030912106005a0051400c180d1702c00d0f20721100b80400102703c804d01c3c1000c8041004102585500c2c1094041da8444150030340d59446082c00980340301052180d0503280d0040b640005001d02e1180d0260003110007034000d44803007206000041d1300322040070b0902140c50300b1443c0001c140b5881a44075030f60142881c51442102c1d0388946910b459038014400440d10074143c14a0306092010156076113900c110a4401140742540c001e02075030321080018000380c00c240c0c50701d000c619141d8030117050011040001025052526007e1080340d0381726103d12060701c0003002c1c1c09003c80d0000303021a280b80b00c0c00c15a01d42400700e0701d030120680a4414082442020410103010100000301c0c405c1c4030b9a0040d1420700d0f4580309504040c40c0340c1c1170841e001e80410512686500810007902e030000404c0d2820400c9680700a06200303000024040d20402e503004160f030000141d40343d80b054100400445580141d40208116610003005500720ba42da4060001e05500c00c0c661140780c00345000c5040d505c120098 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781037751 1250 781036501 781036519
    0x903150617010e06310602040504020f3004081c1a1509102f0d020606010e0d151407030e0f0628090b0c030601110a02030615 55
    0x110400514a4000111021a5114561260610320400c80542c100290394442d20002c03607010340040c0e183e418a050017003001958119074060000540c1520000d08001e00155130b50070b08070066060582c0003000c800a40030030300c5149031402d8045c0d41e040e08103d00c2c42d200d001061310f0305c2e10364540603040300c40305c60403420800448044415143c0210840c5402c0c00c0070000d8010a0345c07040142400310032002e42e40403002400341144980da05122544801c405040c082c00d4866295102411f60116003c18007001001d808a95071a1034000703030002d0481520380c29156980c984400445030005411001540106004000008902c0c46065201c015800c800b002a40c0340824605c401c403490100d130700d0004a5610b41c40c80201d564240031016680c000d010260003070b450078041803803c01c00c60380c0d242010b105131414055240c80e0b060f070001d03a58503080340c80341344940b40c145011115503000310ba016001a0341d804034335034110000210f807034445500030040d010319959664000d15011442501d035500542030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781039001 1250 781037751 781037759
    0x1504080a0305071208071409010219030c0b0f040c050f0d0c090218030a0b0f0402032407030615020607030b0d150b010e0901030506010608040606090c0903050d0203040609031506 78
    0x2009080c080314800d84a940d2541d120781408010716a201d0f03020303000c0c0150b180400042a5025004400400c524800241c0317a0284000407840d2012130318580d45060080008403042c1900100140301c95445180780820f05c2e641c405270303141c0d24081540d0082400c00380719000d2000c0e103400d100386030150001506401004003241c4032000400500ea102400c1a42d0000d05181142c0c2800d44d0404401d000398001d00103140c81707031344940394890000d20102ea005150000f2134115501400083e591100128164845003030007540203162040a4070403201003441c5c12070000383c032005020101d410381c07031a4015142c159034055023980035243e01c17980320f6070041408a45034001608403100c01710148640c600080e805588800142c440103400c1551307849150480010400240e0000d001415240c103450009000d03111440e2000191000750003000030b02c3e05000340c0c0b00d080c5911040712011a40201c084401043d0710540176030701ca2245015030000112600790038404101c4059aa20354100e800100040c030580ea = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781040251 1250 781039001 781039003
    0x180106050d0212041407080c01050d02130b07060c03051008100b0f1503100f05060d0e0a02130b01181404020c0a08031e0f1303030f1b0216080f0309150408 68
    0x304c40494030600401d9401400c0f41c2c040000c0005840c15400034079050808400203050342c080d0944400d5070399000030300210a8803000c290507000740f11420b05947c95100d28540729003d0550440003d0000b454074000401c0a0500641c43e803c40e0b40c04d502601c0140700d034031110406040c2817403003a50080d080380010725954466258442d92140404c02d01600c0b0b0520b01c0d210160320650750702c01704014820b04000d00465480e5030445140e140c1416002502007400e05800e801d022090328042c0d805165151000c007441c0003604200e2840f02d09903100d819100e5047c1007900280980e0040c185a9000e03800c0180c3c5a08080c0d00800125400700115511182650b0300d4807540e83c41201e1404031158800e0ba40001c0d01030318a002504005a0001060686803100303a000302044012030103010142c03034009140744030019034800c400071030565100c5440d03158042c0c1c01035510500c4e1402e50006201404000405000114040c50311034a01c1d00554a01098081002110964124222807820041000040c003c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781041501 1250 781040251 781040287
    0xe0402180a0b12010f06021e070b040e04140a0c091e023c0d020901030b040c0f1715010c0302100501080a030905040b0901050618091302030c180106050d02 68
    0x180002d06a42d6480074000005010352040c2d101000a581c0c07801c044c4149a004a48103030a44004d5290701e00380781040300024602211b5901c00000d00c680000e020610b41c9414118a00c91030140000d80c00d101d8550f9150307039950f8082c0e64040c1154441d04070074080161b190f000700e2010a8541281ca901d0901118a601282c0c00340c140c0100104e00c2403c446009010100100784207820580b10344c1c104c05c030b00461740165104160768154102e5000400c50400ea00030381c0050402100904104186140804040d1035032003010501008245000d601c020412a2421602d1142c600c07058114108000d2000544444c1115031045040d4010026034069001141c401d850003002064002c008074040d40c10042e010001c960850341c040e03428407a483c507081e1950202641142c2c0309490a503a40c050140c080080d2184a003031180d800b40344101807050600c2c494502005440c003c41c142c410707414942e0708100e030311103142184142101c40c40004108842c0200c025040d0041820801340c03511540c4000904020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781042751 1250 781041501 781041509
    0x6111303120c0b0f1605070f062a0c051603020d0204021b0d09150504260c040f1e0b0d0602070c0f0e07080919170d0c08010914070e0402180a 62
    0xb036098100060302c0c43c2404020b88685d03140c20140c0c6850341540320000549400341010f04226120640d0f5160381c18002d44030702d03120f581c40c21210900d0388150401800108503c50030b80d554410010300d8603000309110280300880e5802001c004503007a00b41d00b40800ba410140401941074814070300c690429030180035030062a20f10f95104c0e10141e00303040031801800710018880080180c180024001d800307032039201c840404140c581521030240711043c0d05140c148901c2d180c642280c100084c40c3d0034035960381c004800c10b107400d905222109280c814820100d800440c1d01507804944003043c08042030301c4d64000c201850145000312822504c803a80c07440708403c280c0c055415504100d00300200f01d070340711100035004082d05003c1c1400c0c061a00c120080204000009400341032140c01216120b40d0f844111511913880300420300c4a00ca45590103000c041c42407241d010900e0512014000445c050b00a0034441c0b601070f2900d0490920000510000b5085402160032246c090a4444100d0382d490710321038024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781044001 1250 781042751 781042771
    0x8190809040608240f24190e01081c080a0e070b030703050703050f01150504080111041d0c12041109190e1c081009090f06111303120c0b 60
    0xb0803005000004c10628000300c5200a03807101c0038000064003042136640c2124113505d0341c00b54142d05881c0313a03c143d2502200c40c0d60061307190b05070310002c148005403c81298107100301030314076a036903910603030b01d03010302592203210484100a0800c88500403209960444041580000e00c0600d40404c10318000700350700080c0c40e001020040100307507a454040c103684040d0902d42806141040f810003080030314180034100e90b041500041c200118801c105840062040310001c1c00b0b11454a80a4038180d40103016540000b404202c4541d10310001c88501e9010f02d0312100c4080c541600b096645120003000380c000c075060b20404114502da541c403070190f175008812a40024410000d40002d0000310385007150213518a070400102003c0c903050a903041041003841d401c2440d49e903603991118416020407a081040c05034501882d10061104a5a4148840f8440c44041021449411801103140544400343c0c20f041e804003c00c0c0300050352403100b80140006414007010344c20040d030722a500c10f80200c1b622480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781045251 1250 781044001 781044013
    0x31f080a1a06120607032409062c010510120e010c1d010206010b07020103020412110306010b040e150103022106030d0f14072301090b0a02030108190809040608 70
    0x2403500c105101c0c6400c0407085600504944110100f04d40f14400208503506041d80c80e00a104101e181c89800e02102d1464070204000a8480001c0f40c0202200d010380c0c109038501c0001c0c020a1900882c00400745108490403003e245c2ca45010082002e03604800441001001004190000c0440c044c2115191418001141644040f40024004400415409490132005c860f04485907000b00e191415240716030b1406c1d0f07079000e4600041e4081d105039402030b9051250395400e6000e1060340c2844405103002103081e50301690303844520070000e016034021a00b034084008081051103d00e20f00902c3d40715010b04025040080e107100040c00d007002c004c2e46040240c4140108200f500d030622600e41c10711341c2814080307128512140700420000008180c101c0503640021032034144100804001c802c0c1100700f01303240d0300c04138490140d406800c00800c101c0b130518011000c200800ba650094034161503280004150b01039000310250f10360a0654401e591204d000c0051510540f01c0e800b42d0704c0a130248030000c00c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781046501 1250 781045251 781045283
    0x1031118090d0e0f06040e061801060c03120c1709070e1603060f03030e15120124080402091311030706020c031501050f04020d0b031b01020111040803031f080a 70
    0x844061200c0b184200c036544080c03d89070351001d05480603901f03218034824090b079501000c2084003007500420103291115100004105511442564080e1700c25030321030354002045040e40056454624078500880c2e1440c517000252030300b504003154030403080012900c14598030146c4a9510b08162000c0c4c6c3c0c1841c0d40c0c142080c98507010f0003040300801044108419503481c50303c4c0101070070001c0200c54414041460000003804010701545c008105400da4414a035a60760603440200340c03121090040d80b2840030742144c06501952455200d16009020344e0170325a62020413030044510b801c42150b110200c1d010302040c40c0c500300030710400340c80c05800900c2404041d00400d032034039800e1610b5401e030300440401440247c40301c00d150030411078155000750702d070044521a5000741ca4000c0001e134140c490200046040e00c03802e142c0024200e400e8000b0041501e000100a80c0351003180104482c3d903004202084081c66070310020b1071001c404102c1d940080f5100d0500b0b5003081ca86160039242802a41c0d4907503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781047751 1250 781046501 781046507
    0x1021606020c01111f021e03090703030905041e0c02010608070f031a07050a0e0604120b1005030a082a12070507050603090c102703050606010c020901031118090d 71
    0xf618031402500140011210349000742c068170700404990101540100c1e00f420380d921041c3e459812011019020740c2c90f071502080b102c0d5a40000c0c442a80010250180050242050300c40d02c41d860340700100c88500000c480320b0702d00c040d02d89108100c1c1150350380d190010300ea1a00740a4507000d840242c3c1c01011403461410092082600f0510319a49010f0400074000040c0e00181103d4020301c4904004000c080c01c800069190701956001c0003015012100d14401c110840e2103861181420b5910452807035101d4050555411900c40000c1c14054200700c3e00c50508100849640c1e01c860420410a01000070080c183c02c200c102c1c95403000141c00070400c042003040a0096401800c0701380c80f03503825841c160942e83d0380d80c2e403141012801260f4240f6001c8246115064050030210782941c500c000c5d11611041d44141140c0d03103c19915405004080707030096108114803009181c000300403071204d07400c0d515980700025003500c0c8241e20030440580200f420f03510101a911442031000600104000d010006d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781049001 1250 781047751 781047767
    0x409050105090703020c06040f03122a091d0903130315050604110405040507121118030c010e0603070c02092d013006060f18050f01120201021606020c01 67
    0x24501341801072042858008000540306d9119402c20251501c404c80341c1010780303440359a100106030f000d00b00455540d00d80100468080e2020240c181d000860803054000c903002c01942c00b4529804900380958014000d014204c0380d00300a00030f05603860a0b402000004143d8030b5030703008480440310842c8001c00140280b01c0c407644402c0545050020540103004608a4452030040620486c0d4900c0801c0b0101d2140000e0b185526040c181001070116001100c0415002a001d696582550300700c80d148506001c100b186407440e06840b0405000e07000000c010003500010100e00401242003407120169031a007944c203014451202c404170103588650490916000344440140c08004410b00400a0010096512800300130700100d03620340c50801180d00c254000094005403c103030424002140100590b214401221030440510f018004a000d40c0d00a488040350071111f0a01c1c04e01c01003000c90b540c401044003040c4140f06880c11070b030f4200080d403800e030844c1e001600180e00030b0a200c0c48558101d044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781050251 1250 781049001 781049011
    0x2001050a09230a060203130b0705092103040603023019020306031b150403080a030e07060221040b03040c0501030e1615020c0d0b060411040b270402040905010509 71
    0xa00c0c04a200809440d9600d05420600400341c950000007c0c4000100780d510b583c9681c1d1108520b20035040080c801003043e0003910100c0e00c1021905411151101445c0024403104105005541040d152107030940081d0055000d81e8500480801e81040c40301013a0050781d010007040c624040d46081c05a1007400b1078841c81e550800c05441001031000d0342d0340020784884900a070b41c11507032a101c9010085032000300c1c2d8003050b042401000c13801204200c030050141500c404941d03000c2018010b648401503541c15070340700309000360300314045c035000740401c5042d271000300c00c07240201c01c0c40d05542d072981214540c41250243c40203000004184015a0f05000700107001c0c1c0780c003008041c0707001020083c10001d00300b0710803a400f00c000303101c4c1d00f1303460350003030141d4400c50400502130f03505000607050100c07810740704880e038074032651030141d070390007085a114180c46c10390390520500e509000024403c08661204030750074112202d0306c20180381d02a40e5a000810242111890109a552404c0b0031700c0030059010702 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781051501 1250 781050251 781050293
    0x10612090209180f01022109060714070c0b0a020c0f041109190b0a0903050601080a120e030a140a020414010b090607080d18050c0d0b072001050a09 65
    0x42400580d0382c9050858004010000c00c0d858103008050051410f09880c201264650003c915900704020100c001c1c42c400307417440741c02d80180c0d9a46c18201d0700c5000403905034021807012800b950032213000902038421a44224101d2107491b446103403441540d004142c030030740180d0250144401d142010702038642d1128060f602402019084001c400c0c03035000e9625141c0c02406050603c40828500411110041212011043d0351300f1541400402c5400b040c0000c2d519445104000118018009014103206400c100344880f210030448084821440826030194948201d051810108641540710011202100004d0110000078414881610802401d00100181c00c034010082441c8010480ea80c901e01100d000d07a46002600e0071a54901641480071320300c4d4982400c1010b0034000b00280b920460203001201c1c0407000080411031600b1520300300a104450070f90118486500503503140000880c0140104888100c40240310b007103c8040711520442e6031680012014402241c82351000201184 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781052751 1250 781051501 781051511
    0xf1b061b030e0c130c020120042108090127090e0f070506040605030c04030606090c11010207030c030e030307050102071b050a2304020c06041a06040614060d1112010612 74
    0x760005108004040d130801405849190700d19245200390f215905044600c1000840402c19006c030f0031140c1c10900604070080c8001c42c03109a20310500910080300c0d580b20545600c2c005041004542151602108003084c5074a0301e4107400d0030201e40c1511014000030000020714007200d5a82610b0714004603c500b0700c3e5000340d5028011515082e0440d4165681c1e424025601d40728040e4252441c812a4409000c0c40d24003600820611200d4000e1516815581e80742c654000f800c18440b0308034410341d0402000304409988c1600020300910010b14000700060a03242042a40d455160a99004017000c448074035401d100780e06407000b080600742c05000266101400316007005401060444040c403941d2031643c000107003030125601c0350110b412001006054130154201803915a00010314910f000501a980400061080c00c21b0f1152a0031280710035840300c840c04050f07040c48000d0303114080000006031510303010260303034500c000142075501d02503015260542c50300384010a402515043c1c5c841560800c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781054001 1250 781052751 781052773
    0xd0f1d0703121704080415090b1902030c030d02040806010e01050d0308100f060c022404090b0d0209070c031b030f120b0a0801090c14010f1b061b030e 66
    0x9011016240d0009400c070250054450594000e82030514140f03482448100700000c200d982e034043e03c00c4813034540f2144803491540105448410940c064540300700d07c10700a01d0429030b15441452000c240e2070060303a15004d000e0003041d086502c5100d11005950700081c0070012440704100e0036005004203800d03074080d5410b000c00680050b0320f00b02d0140410081c2d4000c10310720b4445015441c000d0a4211034640e64070741e503900c050585080302a00360b01c01c601c81e4007640c003c070b0840c420b11a4442c0f04050042c0c0346c00e0400340450020540002a40e4014422001040044e110402003d001e009507403250404c0c0c00341460f00902000440d080b5100303d1000e05030290020703800110b41034102c40c090400684000165030000d0060250f07031000d59118a29140001e10401c065200c1060075001d94040c0240e540c540d02c8820007240c1c880003a60011740032402409000b44a107407421950444030300107889e06560390b141e079003d454100850030882c41800c00c043d4005901441b96243c0c1c0f84403200030380703c03800c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781055251 1250 781054001 781054003
    0x10302030c060c0c090403030609150311010f03090206070501020c0607020c010504030b15131d01060b12040c0906030b071707170601020a0503130906291308030d0f1d 73
    0x1c4075000034012140400d401088480500aa8880c0e42e00548542c249160a0400801814013031050003506440c00c01d0891714080e000c082c010541e0340148200b681511751703000454a00e00c0b504034050415507a003900000503982e0200030a003050150001680b14411583c1c09410941e0250815095500000c000701407640c010b010b480c126a003040b4007403055a2480b104001042c0c0c0302030f01a50000c035010704464000900c0e40000b905200e1040e5000029420f011f0403400c880741c42c0102e29905105210282e0714000c0c6418065002d4400e00110f0362487e9544440810740b110354108403140c0151004005065912412200c088034000c44000c1081c148200f010b40800301c01121600071402c10b10010380a46d0080107a03844440d8000700700d998401c0307220a4503031601b15174010040d501d82001000115070302c02000c03140644200006840116204840488880d40000c0340e01c1203807851103d00050481050003d01651082403d002c40c1c00e0307224040f803000302c41e030a00780c821514210003100383e28900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781056501 1250 781055251 781055263
    0x6050601020d090510050d09150b0a0e01090209060403020d030203030601180e0441060f01061d0411180906030d050a1101061707060906230901030b131e0501030203 72
    0x41aa030380b46401030059001c41e450321031300d1481d03600c0c641006908c00402254a04804112420b1081006010344603c2004500303401403051164418000c0c00600094141d5801071610460062010385010341d41da0114a41800410003940560404030400c031255800590105c0100301500c850065182070419172540740c100688042e188030283c0f0482441060044920b9440760305816960040c4a0b188aa2580f402c01104444185004a90106d000080398800742410307554181c0740c038640341c02d0a40088078003107408030906a200d030321174461100f070100e032400a08402c4603103c503030620140400700b802400140505038501030307400740940c1d080295000f015107210038420b16000c80003000e0510170318050312460f00140200000e1080013580c200c400076030402111003549030300c1005641d036441070703d0001c4c50804440c440e51039940d520b039500c4c604400a10304100d050600064015080000c00c10b4855826000c240301c036500c802400c0020034100c0080100c50f100b00c0140217541c11503010a440300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781057751 1250 781056501 781056509
    0x10e07030b1e190c091a0d060b03060108011a0405060f0c06130b01060c210f080f01241115060103110304051b0a0305010c050702090a050403020c060a030b1c06050601020d09 76
    0x11366078024101114440e200c40c4006021080196211038264a050350184c2c0c08615001449860b0000c00140c894914007547e12444058603401c4091b07103440305a813070425110241042c151810400800c2907902e410240000c6d140540029132201c02c0906220310f04000a01003800200e1a04500000504040b107254152911850070140ca0000ba1034523003101c02c070070341c0140d4540c003800c06800c202d50760246100034450000d9551003c0d0341c40d54031340314840c06404c0c003500c1d10741030301c016080300704240d101082c0c0805041c529040d4441001940070b142003c0900b0325240dc40041d90090040c0c83d03034903025440144040324842851420540c1e100c5070744903140c100003410a40702d44c0c00501c0507610791540034000c640002c020b11949007420801041c075400400708921501d00d5101140003106584034007481070358182c000300094100a41001038a400030f5919404042e01c1395030111b07841d210944820045c0d40031101101818502d0f10300b00c001c0d00c0d401007580b07046502a00403241e5445e8080c000400715 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781059001 1250 781057751 781057801
    0x105010c0c1a04030204020f19180303050306010522060f140313051504030f090b030106020c040506190e0105040e0d020d110106050409110a050105090105120603010e07030b1e 77
    0x15503020310b02048107010340d6001940c0079101047c420451480000180a600f0003c0c3c143d520103000d5a0301512581105802550040d40282e02400013034018801503401c0481414181c0c102080c40111599920514403460820301000380c0c05c00c541a0081c0c508920040d05051162100c14a81394070550b03800001c001046180e0b901d46841c0034010180810700d2046a0b8482c090000e2805040107046040001c10366000100c15100021302c01c40c502041e03a050310141e90203424440c1c03c800410000d01400341c41184e006541800b8508031400440600d4014a030303400d0121020762501040008564001c001c014845d0003034041c0c4001d090b40401c0003040e010b0f084c1444000704a042081c180104016041036400c103103401a0303c403c0c02012148810341180032181e040d0500d80394401158213010b14242280403880c1032180c1d0161040780c0d02d005911410240c000610410304542075484e00d055135200ba540410444188111504070050403c840790340d0303194186442c2032083d040d0300000b440c09890121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781060251 1250 781059001 781059029
    0xa02100b0112091e050607081e040305090f04020d0f14040f0b07030e010f020403020f12030f16021c0308220303050c13060203040602191a0c040e070305010e0105010c0c 74
    0x81021505044e05005004c0c2018540c0c1030181c60000d80d207007419208200402d1813400040e1035024144154806264160030124590316241d40c01c0e20a50812520194000c0810385071942549980c4082d2980340d40c2d41c10040354000000d030b00d09003190300c0444800c1c402c40c1200c0410001c43c1494404594160340254180d025079541c8400724010001e0f01c00348005942041000b06030100c064000c0c3c401d80e40210740d5a18943d0b46034003044502400b0155002c03050b0030900c440d070b414038208000b0700b0000c0100101e014400b510741c0c1c0011b030980c0a442c0d0102ca418816060071041c140d20415465000990030070100d0141c0e403010307100442448007440101011303124400640302000c203006031244071180c0c1000d403c441d030300c841004e92640c00034000c02c4014480c8103282e420140c40041c4803c00550800860810444454858900d00e80010b080186a00c010030001507041d20080ca000d10417400e654000405504243c944609054181e00c900d040181407244500801d00c000116002c031802c041071412 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781061501 1250 781060251 781060253
    0xa1a030c150705030d060e1f1505120903130803070f021e1c0b09030f0322020d03030b13020a0f0305040302190501090b060118120302150406020a02100b011209 70
    0x1c00d10941e00018010702004c40e6460141e54a41c0100b4141d803184a201c4145580f048010011040440c010811003240c800c000c014111505004040c802482e240075858001e54038141101e000080d680c00307403168000100955807002c4844440050822540550300d0080790b0748894800564581019100b031480282400b0484603181444c005402c000d400e8000380c0302e00149458800c0034105e826688000e2042c009545094003004481405c00d01c200003504607128070040c02104800f0030700c5e1240f010b20341454038002da581c882042c80b12511030343e0003080940401041c089680700300c0300c40c1c0e90340e940180050480c998200070b111440c2c01452500090343d5550f8241280b030101080aa159840050001c2c03106014040d0845190b1a0251850888584800004503034444980d5600c1141ca40c96040900001c0511011001c0481c00ba104940700c7d040340c4030031b0040910b0700341d604585e200c0d0700066181c10320f50140852091200464010004807004400290140c00803a6500c0303e101d42d5156010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781062751 1250 781061501 781061539
    0x6010507060e060702060a0e150c070827060301060f030905101d0f070e0105060a0e0303030c070510110d0c0c1a1806040309091d01140a1a030c 63
    0x34910315004282480050748950032a926008182c407414014002d4100044084c00710303000305a01003040364001e214000e40140c10b1642c0c4240501490b00501c01082001d010590714400b600381e954400d071072880c47d40c1401c900740070b06a0074a1051780c0034100c14030040202c00d0704600041c10600b518100800c0c03110a40c6800c030306003001211403114040c9800c054100c04000e041d06849505000c1c011a03128181d0b80004590350001c910906c1e00d41c6269800501190400c3c401420350740809040001002030070400181c00d40d001103e205118040114100b400c1c00004c00c0340d03840c5403c0b25101044042c800c2c0414101c1442001034902d0348544600c3c12460092103020740c0c048007600100c2019146e110800c040341c2042041c3c1d00715109043c00b491418902c10081106030042c0d030b042d00c490908500c2c040882024044189036003410700b04591f07410007150000c1c0150f5038081481309104409140c4203020703104031070400e10030745d404180d8514016201d8400043c0c1c0c031640d07001151400785140d40005a9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781064001 1250 781062751 781062757
    0xa0806060d1b0905030105040809280305060a06060e0a060f0e0a0b1b061509070e03100c08070f12020304051603051b0d050307020909071703030907060302040b0d05060105 75
    0x1500708107241510001085501d0902100d041c5416502c1c00e500a9444007003509940b030a6401900004007003210042601d8007580d0100046450300509486000d00c00300c00d0300042c280d90040d1203039008041001403004680c880d5001902250410406a01c00e61000c11110f1001e07020380428881622001c5c20404e0003440e8600d80880c00625405006480d004480ca16411403520701280900e0020140d0100b034012480511881007104002a02d003501d804000009401400110500442d03d590045c161820b00c1201420125010045041c405107007004001080091062081045a080002c1c41592000124100003581034001d038070781e101c50904a080c00c0840204440c50501160000704000002c42c44480183c49025001e43c00803075001480070500800c0c40050040d00100000c0e4010302d8504100341c0c20040003811245801d80300c03510152401c880040580b02ca40c030100812038101030402c1355502502140c0750a50406142c00d1111155000740f214000f06e00c0e031242e0005010ba4403170016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781065251 1250 781064001 781064017
    0x3030f0903081f0915050f04050402060313170309030a09050f0a050d060f0507320714010f110403170c031c09020a0603091101030506151e070b010501020715050a080606 74
    0x200300404269002e0445401c3d0f05c0344101070080c0580016600c00d89800d116041c0300da60094501d610310b6407041900c0001009003071088607025003101c0008014105000550720907140031f4011541e030b40c080c0601400c2d80c04168000b078030404117000e500307449031518a1240704883d0f0a8500000244182c5003030005481490f40038580207180030200808254031400130000d85180200011007141c03800f003201501411184400c40e000710412030762000451091b030000e45400640000075162002010440c10b94813202d00e150308070500841e0a00030b1041e0f01071180410442c0314019442c0c81034400680d42c40380a15640302c44062143d50308490a4074032038100355103469000b0508040d031516158050001c048980e0142c3e4042c420102d00b01c219402446060b001d160001e10002c10740050b108803404546c00021009454a151031000742e6495840c4003422840d44500b66405c9158185030009240c5403480e4800d40100884000f200f00d05504501151581d99a92400380f4aaa49503070200d260b9208e0408 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781066501 1250 781065251 781065269
    0x702030c0414071d03061801150b0301151e110f0f0a1106070f26030f06040e060709031b0803180f0d020f091003050a080703030f0903081f 61
    0x1100d4100080c140d002c05100700e610f510741090884884d9030030000101c0a0310400d8060b804003011580e452106221054040c0c1c20f1000480c0580307031f000d402e002c4180564421000c5c6500480188503900c0d071000e41910480e00c61170b00c0c2c5081d148011150405070114a0b41c003052000c1c519261510a00621042e0303059581e000454a142c81c46035225036446098503002c1d90490a085000780181ca0300504170b61402d504070300c034034070701403200e4450f000311031880e0035805c48060510107442c3c5007000c2c040143d40701e8503110450070031740e02e070103801c1c401510681e9083d901c40d13400c110104164203800c40c0662041c1c03504400089082154480e80c0482100d03281c000d45161310002c500c01d0315400c3d12f160200c220010658016424440080901100c0d00301000d000f98809145098078030b0600b044001c06901c520655040441c0d95940d031981400d24035010b8054889040004031401851740500070034541c80301d00c16081041c48081d4800a02c615800781c88004e040040c12a1080c035000f041c40703c030000c2c02e5a18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781067751 1250 781066501 781066511
    0x312090309101e0314040b0c0c100b04060803070f0b04020f060c0d090f150827070812120f04050a0804090b03060907060207062604060c03050f100b0702030c04 70
    0x10340d01900d0301481081e0000c3d924007000305160228868050310019458141050f84152510395426108503001421009101400d210019013882e04014a07900891488000604c0341e06810030302098a403550040f07200759008001102c0042c03000390181c0065500000000d407991140d100146452000c198525400304011915003040e10012070940d00c03220070f0b030319600e007180e5440e00c0032301350010b40340300e403030300c0c0301c0598449284e02d43c001d01901e60310502c004045000b110654030000d9100c0f5036214000c2445d0f103d040184800ca40400904c040780e41c0806446061900c80701c03000c0f000080040c40c0300e0481c491540880c0c204807041222084d46c0d94003000c010f440702d45031048030b0014945010030920901c0766001180800c44041402030039900b80c4c3d1301424240c2d023026400e4984000c010f100c180c11405c14075001c0c4c11020b48405030343c0624401c40010074000701c4464000c007502c10203844403070f40003c02028403080d0982c5010940849111580450b2103d403e800040e080119a2010a410074204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781069001 1250 781067751 781067779
    0x60804120314010303050918191d0706020a050609060405030901030e163803150d050106091e020a081512162d0308030a091b050f01020f0312090309 65
    0x20802909000303a0072340f01d1402840040985c070740403040030380e1003001c2e0181422003c0d1440c9c40c40c0e00034121300c001014025681c2c440c40c14003079141414913440b20005801c02040002009020300174240c10414000c010401420075807aa10303281d11030f03074007410306060343c070a8a0003070803800344958440c100c00b40c07488030b40c1d2644d603840c031310014020003030401c003d090407040302c00c1c041188600b05a030416008500c141940d41d4902c006d01d420810450f156030210f050105100060000d000d807601400c3c281202045428406004907014441c140c40d21031a13034010300500000302da0010005174041c160104084040441e4808650100c2000008014a0080c0ba070310702c5160132440c42c4103088074081c40389c0114080410403c5100c0700c100c2810100380c5203025904001003902040515044071003c10001290301840d90342d00364010010300e02481c3c800c1813070001c01c21032404d051400d6a01d4420f002a15101203541001600c9106200c0b882c42c00064540200b5044242041501d2038000b001c1c200d50400481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781070251 1250 781069001 781069007
    0x1200d09090b010f050301142b0b10030f03140d020417060a090804030803060f060d05060f091b0c160e0a05010f0506160f02041e060f060804120314010303 68
    0x2541c0114442a4103007071002c401540f1480004010a03407980d074039030071642403a010381030b40c040703402d0003680c4044100152074042c0c08030b4460300c1000f844041400301100482c580300307550a10043c40c82400c455000780c10008030301c1440d209500c080e80b502c4c180d81503180306889005640112411000b001d440450007040d4850284c12030718009140b101110100e9459142e20340039503640c842c0091903040203200c104002080c1c40091604240d00400b001403200700900400c1c4250842c050388100503444105000003800d01e0081000d61180a9032462545d1500107045131034400780d403042c11801200000c0d2142d01d51000d2060f80c6405a0345131080b0582d594513500a40d0551040e04d07400713141e81c50304e0000640d4100d0351140c00f00719000600801d003401210404140307822401e0b9400d841c5651600c101100594035480307040f02c00421501c07815100070482071500211607007504030b4080001e0451042c00f403d504008010b03442a8000102d05d196660000d040f80602201d1507100021980100003004142e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781071501 1250 781070251 781070267
    0x1503050f0a1b0f060503070c0206030f04060506090919020d0b07091503021821010606120c0905150c0a05031204210c0602090a0f030803090105010f060e01200d 70
    0xc01155140d01c44070140c50b10520040d414424009000e4006004020003405400a598050210f042041c2046119004203003140d1084a403001e001403400c0800c410804944203440d000398003510310401034500b02605540da0003c01030903204201a250503181150769504803a49090b62007451503103181000d0402402d0b01c4600e0060202c400074a149854105100e442078640003100826030300d0740b014440c03040c0202c2141000785401541c0c107103480b0010745070090240000400d0340399580d240c1d9405070203001d000c55202c20409400c01c08100d4003040f00f5030310b00e08078010404400d0070761035540d8080c1211910748810100001c120f40004940f140015980b0300a80f44124043c088403505a01100318000c41340040c5000800032401c01a6204040b50160380508070100c800760002070032507241e0741e8a0003005d8090b80116155400002000342d06c034000e001d0035004001c002061a9417130308184003d480030068000c000d04001254032090800c0704603038120000160700c0420b0700d01c0c19050680051140e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781072751 1250 781071501 781071503
    0x402192303061308030c1b0a0b060a0b04030c09110705190b0109050f0a050912040f03210507030c050a0c0602030a080108061501030f090206030f1f14041503050f0a 72
    0x3005840004690840c07407100c1c00f2180341c2c0000c00914640c1c444c2810350103600803030302e02a200c00000843c0480d030380c420010840c07501e00030400b00c1c6c0306141100820401c00d0058208000c6c1c804144410070006000343c0301c41e425071349902008503510000c400002d1460085010140140c4512035018585036410048120340300d000d2520058a6a2a03040401c2035030b0081d100032444620010004460082c260300c083d030024000d00a4500102c0c1e00d00304060300d904140c1080112100b070078420001c01000c001c2c0c5011584441c000300c0b54480b400e010181c014003911501a040c0072403001060100402817185850080d40009103840240d15036070700075035076007104074800003207202c0c80008070b00703000e0028400f84034208880c110310b40d0046040044020b0080c200c015000240c460715468010386e078480c05544205491034100403107240c0108058030000c8003c40040c0d144a40b80e04c10b00441d8120360400301c0c0e4000a46e4045803507103411008010101050303001034118000c001d803221042c000480e001e80d050b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781074001 1250 781072751 781072753
    0xf101b1a19020a05070201030c02151810060819151406030105150901060e0a030b0c0c1006080706030218031509010605150d2301090f0501120201080402192303 70
    0x1c11103400800c102e200d04903142c000719005105030710056100c3d40100c41902181d10554000d041c0044c900c2c4000b410550300302d0740c0000c444ca010b030284141009201c9104000c00c0051207101c0c5041e203510b8498034050302c03051810b8520000c440500c0340c01c2c645484840d50040040241d51480011001c8404080e03400702e100c0c1d4240b9000c20030140c2c40240c65403d55000408807103032646400402d40c0d12002ca4541d403500001141c41c0000030404a03e03682c0d00c1110500d00950392030342e100100ba81400fa200641da0741040c6080f80601802500060b810103403540760600594a400f6000003400c0e42a030050305076814414008001a14814909024060001d0744000d100e00c9445904100404800c13030341200c41103109010120b02e01160fa045244410b440c9600030108171004001c01c02111026000710340150b8442d40030501c020503074031072f40f0f00500e038840d0b1090950016a0000f00300150240021303216030b401c117101010303403035410600400a080201e250910b605500b40d210b0a900e01480000788a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781075251 1250 781074001 781074031
    0x30513080a031532030c041d241308040b03090709061512021b06011205060c0405033d05041209080a032a200f101b1a 52
    0x1c0c07403d0729400403480043c12000050f0111132809038900d03040400b24025414420390002c20055102c0d84a142c3c09101800d6220900c41d4586d002d20349044041da159a130300c40c281c1440031000201d100f81d15600511092809030105640e0b0034000c5a6006076003180300383c14030000c01d20028450020b1101d040b41c0c0112003c0c41526580c0c4803c1e0119500c2828181c0404c0030000100001d2039554001d0840007440124840c3c2010801035191400030b09030403071038045020420407400d0107070800516034420740303250102d46414100700c04a0b45601042020810044c290221510060072400550300e883c0c8089110700350418403001440041d18054506440b1310400c10051400341d44544070810039500042c0040042c0d00c1142d034100c030003440d040035034170003401d4602030703c0c01c801d000f80e00c801c0c1a1806034211000494020314685a1682c04c40c10203449108580001503031502c8059804190003107a09059003590012030360b070b00c40142405401010400c9003401c1e075215000380c50a40f80125010700300421 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781076501 1250 781075251 781075259
    0x13050c0a0f0e010f0503100f170c03010c0c12120f1d06060105120406060801060b09180609061e0a0b07030906090302060415020a1505010602150606040303030513080a0315 75
    0xc003111200b0226000464200d0300d550864080e80055400040f440c281c855025a140c41400044065402001c100091000340c000d00a004101030203004600324000c100c149107125010f0044041e2641c010190140b096032035081e540280c450022101c00d011040c02041c0900f1104401006861040d684a04404600044401300007500c944644030603100c1c01e2070640c26900780750001000420807184640c9405021406500030302400c0000c1000210264681198004214031100d40107642c010aa034101d013007062941d10b0781e1000350410030076510700e1380c0d0400140702024054a03e0401c16004000007400040310038803407000b440014029030b18a110152517580850b4989400d11010303510490501060000d1140742192406200c580d004480200c4029540c8101c48c10042c541c5401560703450004000d0282c052100c00c9480003007022030540d80c60700000042441c0540d00018041540d1500004c02c03802100412514854010441507221815000c0c010090440b0b05080b0a604049002c005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781077751 1250 781076501 781076507
    0x905010b03010504020702241308030c0d08101a0c1e030301060e0a0e070c020a0503030a120b01180e010f0603051e040204020d1401030506070804050303041113050c0a0f 74
    0xa05a0300069151861a4605400c0001940141c038003640c1c441c690590036540031140c1c5d0034107050100d40103e031756250100760000703440c214075951041d101b60b00100f29400b00000c001c6544200c44880d800d058607130f07446040b20702c01e4910392502f201e8110207004445075102c40e941405018203c4045d003c807916001520659004c11440b00c1d071307601c5c00703520900041c00002d006507003166109602601c04005140e40781401110312105803514004220511044825400e10340005005050150007c619207480c40c5401041600811200c4040c5a80c484405580d80e01c07400043d088214401d21155140c2d07112200c3c400303407030400e101e665603603070000c1000034020703010317001c0e0300e1140c600b00380070304404100d4015504110300010400c07a8840d03420042c0020381100c0d485500580c281440018942d0340c107601c2c145280074005040341d030a11050008000004400000301c031740c07066210f44490341c4905484045210b107840c0c4102c4407402410039003009803a001e61809407460307100a42c0c40321000c0b00c4e00f203001c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781079001 1250 781077751 781077761
    0x3050a180c150302191e03110d1d010615020d030605130903090e1801051506091c080a0f0e0f10030e071d102103031820010909 56
    0x5040608580e4100304803040c00e460031040401c1400e001d85055002c2c6a440d070254144116900841d8110001c09000c0c400500b060b19082d60707d06007000f100b29a0020362280e4000c2103240804652512480c90100c0094821840c000305010001e200058a03101c400744041c0040c807150005110f4821f0540300c06211f40224030840300c02600008105940052a00150034100e07000d90511403000710006500b4130707407520140302d03480c100492101c80340700360350303c0d42510340c041d0503010b003021914025425940c801c001c13500d031a02c0c00c43c2c1c0d050400b10351b103404804845010f03070050480d070408038403405c4d0642c02c86038450b001e180980d607110581082408204070300c60304d1103070980c00a18038408803a00030b0003540000500564001150304036aa1a681014142e00740c40f40091940f18400c184000824003c0e0050040d1500254030280c2c180d1940901c941c00c03204000181c100754940140c03056030183d000c0100c140c0e41e00b21855143d42d003162045000020140711115000a03240100081d01400394461 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781080251 1250 781079001 781079003
    0x806061f080f0403020f0601030803100b0c0c060c1207030e0f0907020c040518100f0b0603011508130206070c0f120209061009050a0e01180e0d12061503050a18 70
    0x40d81441c1c1d2500303039440c2d0301408003d004905604c00c000880322112410011103000314498a15503079240b8059220303100b503255a40c82401e03490340610070001c00900114504101000c00d4684c0c98481d078201050070301d014031141c842440054000343c1802419407000101282020a46034103010f03c040d181800509603007118041e0040e04507245d45603280c54903401c207542042c41c2008040b001c1d000e0314507541c20119800c024081081c0c3da01c41c64a0242c0c014020010216421101c1d241550315120f0100d5001442001c06410000707a113000409144c80c244500340c5064018141c9502e605143c80c000c419000b4038040c6643e007580e0ad1f0800140702174198181602c440d800f400600a40c5c0703421301440034608100894001384000c10358041141d03264052640000e0600e5205c0060651400b40202c1020b40040304061079181040f00b1403900820000d2030280c0800d5030702e403c9410043e00d076a400010300d0b1070f40108103041c0074101081c00382c2e40d150300080d028104001041225028600220801145001c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781081501 1250 781080251 781080257
    0x1020c120a120b1203040e1f0e011a1902011e0c0c1b05030114010e07020c0d0336090f02070507050909010e010f0e0f0706140a030b09010806061f 64
    0x140790900b0b40e1904009200d40b000f514100e180781500704080d0030358029802040480b04500d007080513140c80390711642c03002016484401e5800e400c000126540020501980040c0007000303000d804406042001c403907580e54409070070315036812030140007400f8109000d0704140001d122000c2d1101d28a16103d0b556224480346c88082070803081355034580c10740003012040310710030040c2030001415441c00e000e074044121355403c071000c1e19814150321100280010f40204115401900d40040b0764445408902c035103078040c01c040c0e902c892080c04d11014040c1e42000f1103910880300800503c00c585104141c81038900340d000070300c000e00c00c0402c0e100480c0203544000c0c103a540610000c004900b4010140d54006041d030b00080f070144407044010307080d2040001490b044990f1508101101d220520002e084207900c2c801038150180f0301280201500c09200c09600100c20000e80300c1c0006000754080450310001800302d03410703903035203051803502c50804803031407409452901f18501440e440340c1d1126150070340c2130b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781082751 1250 781081501 781081517
    0x31a0906070e120c0a0e1b03060105030a050a09050a080409060803250c0f0803091516030e0f030a0506070f110712060e01050f0414071a0307090f060201020c120a 71
    0x1100b000b220b0094060709043e60f024021421209458140100c4050a0f0440d00111107040c0240b00e20313008458007070201e80000040c018490103aa12034220790b0000b0003d4400728160722160009801010036a80060451040d0943d40c070410aa1401820407501031070320410000340d80d80d08442d105d11881b8942c00700b109681d208800701c441180750301c2581a004d03402d030300c1c1c11a44911100d8120300203500801c0d840e40c0301084260f40c91414081094528481c80c88240c00d11a080308891850b0048100003002d001004000d00d8660301c0780c14030b0030f01c0ca40b0300404686452009080503601c500c5c06852120026603100007550425004e4a40703c200041e0b60802804500d01c2c24003040c90501494404a030300640310301c0c00c41a0020240101c9001c0c900031048000b0500780740c40c21469024400742102e0642d00b26103001c01000810207600044000c480d0510f41e90f941c1c0f10207003140c801c0030640001c076055400883c003040a0340c0c15409004040310820881c3d080564107031000001e4040c9400c9000000c40344 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781084001 1250 781082751 781082777
    0x604050409060e16030c051005031305012013080a12082d06041d0c0d060b091f0603051b0d0b10020313090513080a09050a031a090607 59
    0x55010914032400742d14000b40003084a000340d4248604400c42081c03d003400c01d820700138041d620044e440105000c03110400c0760300c8014800341c441e00000f4842c40034030882c0705984060010a401a0705001000f0340d03012480c4140751204402c40e04500c1000028480015000c00e01c41000900204d801e50441601917014400c540101c072984002022250091420801050803e16003528000c03008260940c05810749001024081211040480486518054484a800321001040d560034240007610204500c0006003031900141c03e036100481c0c1c100350304c9020081e680e110301910342d0010110010081e611030791040c04a040d91000e880c85040450306d4803a020304041e010005081c482010100403803803c155100041c0036600c01d483c0304026820000e20601544e41511048024016228041180d42881014510401141c1c640141103a03000111040c0340b50040d12442c00a20004141051080d2240b03805803003250043e080d20040c1c10101c0c0824850707000890001d101d800c1c16914200c0000075 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781085251 1250 781084001 781084009
    0x209060f0a020c0307031a0916120323120a110d0504030e0a0627080c0609010c060e0304030b16020c13021b010207030e0a0b090f04020d0c0e120a02060405 68
    0x1420405003507200301150f014440d102400020000c6000e01c00750302c4070500c4d4000320f01140400400c115200e4010328040c0c000d01c11b40307402210540710b22096007400038480b03103400d94250300d4482c17985074034010b01c100e19219441c030300c0010810500403142140054880c1c1342038105450403141444012f02d0203000c64615402940d02281d0b10500a2070a24840e0224101184d5102c41a0300144009041d81401c1c24824900b00794107000007442c1c0004007082c610341a4415107415828003490310070b100014540045a00c100c15005080d500628100711003030000c2140d076070f41c1d03005105c1159207402040c0058070043d86800004401c1c2c1c0560050080c07402d8250401c540314038108680c03c06560709100341c9aa504204c100b000100d60700000043c1d4a080030b00303001d0036000032078801500c40e20807003100307100342c0c0c80380400e80f8407064003610802a1510807c00203400b07406022a0b02000d14603140b810b00f64994401d02c109403400c415a132030740200344490704440d100c0d46a1100650001c0c030800040241d410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781086501 1250 781085251 781085257
    0x308040f020103090b0a06032604090e0703170415090b0901030b011407031d1203250f050a0308010503010e1b06070c03050d02060717010506071704060309060b03010209060f 76
    0x12051400080224595440d80080d4a056030101c1565a4441c8180104024096403141d501018601484a40d60300c4400b8000c9d8441d500513000801d403510901403820b1800c00c840c1d00030f1988040700341601c1c10112015001a00144110400c008907500401d40b110301400d04032041e81d841000e00d0f482c00c0300b42c50055000e400b2410606040003480c4180c25244602c0001a00d8124442d0b5200b8454103600d408000d8a440140421384c400c1201020040310090700104540e40001e0551910218052004101d0b1101030300050241108aa0b10b50b84420014003013a203100c2c40d071003500d0302c4601d0b980f501c0c01e050881c1c48003902005e45034040090140c40307849241c0650b80141d401016145001400c0d03841c081e885d9816807080b9441d6001804200016406010700369022300301c0d2a1002148100c4010a00088018466031740168000100c07403090040955284c16000441600c1a90701c0e903896800400500c5202c4041ea03085240211006661030107000701d4085a000900346801c0004402c3ca0a01c01c7d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781087751 1250 781086501 781086503
    0x613030605190608010b0f030c0d1b03120909150b030c090a050604090e06180a14010f1a030f0f0a020906060714010f06090c170717090d0315030308040f 67
    0x110015041c2105005020f1070018040c180c0012503411031a80510160200c062090b61181e04440e02640c1c072916085180c10034260000e84007142241180c11403c40b0342d003203400c05420b401c09020840403070b640001c1c41c0c008881404004000540ba01082c030302a41d0058044c034655003c003000868a0340701e00c603000e8100c00d2030080c508117056503500c00003405540641d00940c1510348450518090120a200a50348420100307007024440d800380c041d0903212417100d01e000740ba60064802c101d4201400b50702945c0c1c600040501000301c90b56000c11440d112a045445500c030b072081a00000d5250000300c2c04000c0350344c150740100180c2c0d03295030800c64021801010075410900500402c0c0218039040c40c801c240d1020345000044d0004920041d00603550380360000e14803141000c18000d8000d6002e44488104c00090700a0300e0030791240c2e8801c80d4810010702c4070000303291841c070a01030f00100c085030340c00940f651610100591400208801c0403900305202c050085041c403c0006c0101d42c03080c103503145071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781089001 1250 781087751 781087771
    0xb03070807030f0225060b01050f0405010f050d050405070f062a260301050418080d0e030903010c0206060a08010c0801140f042c19290103051b0613030605 68
    0x407a100e0340c0140e20f104000049038403100d8104004601b4408640704101c241070003861f0487c64010010340000c00d603c140d1144070704000ea10701e140029580724034282c0e0002040084280030a08090800795580c2146010f801d144c52558003001030800c0c014030103139030205021303802c08400a10022058074910121081910a8060200380c8200d24000c6002409650030250b8280e4503541450103210440740c001c8481c0b10362440e01174554001c2605e0100342c402e003410000300401d1810100b04001d06602484100582540c24070019014564010850034030822046d070708480066a18442c2500341c3c0d01c0005a4030110780700350014000c0509507440d03c964180041c203200092001e0f180400c04030784c2502c0010345c0310342140305c2c00d08184070514900c41e03150039408000d040b1003e02a110450652038400b0003400b16002c90385801041401d020101c580c40901c40d0400229070f52400d2043d283d071010b0b0301e44441e41c44a6610101c462504c101514000c186a68114010a09665070381c0c0040501034280031312 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781090251 1250 781089001 781089007
    0xc0203091c050c090c0307020709141314030f0901080c040e0c1303050712050c0a0509061309020402070303020a02550c05040614091f0e04030e0a0b03070807030f02 72
    0x141c4441d400139014144080c1c0f41c642c0c1c0d18000c00c0003403c1100f240c0160031510f040208401401350002e500d190001284408400c2001c1946030a003d1440c1c6640c00f00325501022030380d95442000c031800360041d050203032102076103541c600d810075825120f1401034540051075036000c280890100d10103400c0f0075807480303801258103803a521910700c0d0841c55030042c608021089a407170204001803181c50400c03001640c0c0080003034140000075458032402450140141c2942d01229400d400c0f540141098540182045603a40c4c041d08004003c0c0d40200d42c20000b5124801d54076160484051550400702c940c101801e0318003c20900c0445228a40d5407600000018069a04801c0084040c00342c10284100d4080d9011854a014071050340c981340c0c4400c89500d1a0842d0186035114004003641c00703ca41d1012045481a14002c2404480d240d00103134801464070040204141c0c0021039900104021200c40450740d03036888a010780f40c40f044030294005a10440841c0c4400d011350420550b86042480144c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781091501 1250 781090251 781090273
    0x12191b081c150b0f07151a0103091119030b010e04031b030e060f040504051e01210206070c0e01060e04060b0403051e19031e090609031514090d02010c0203091c05 71
    0x405240a0103000e8415590341c581c00308000122006841f4041d020300301405034041a880d40200740c00900c1126005104007104a104051031f480201e018692003100030f621941c4409981070320683c11a070031804241404040505450510103140f070255160303541c0340c0c40316040820300800b90000043c541038000180400b0038156034500550f0300c98481050071000d01c9800c115202d112041c1a072190000b02000d01ca41d0304d804000fa0b010010761074054078496950003491034440301c0200a40d00c0410141803440011940640c00302008455000c00c542c02d00100c0c0d01c4039050b182522a030301c0000d00c81e81c0041420400300c01201d012440e218550000e0300c2e513a144011082801410054080300002e03a44050145000c000d190305055000d4281f810701c0358542400c00280c280700c85804040c1803d000501c42021a400c1c541100007030244544001a00d420500041e6684154100788a009542045070a040b0383d8400001c1c0e8011110041501100c803260441402c1d10860a1b00300740c8050050300782e400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781092751 1250 781091501 781091513
    0x908040f150215130f150203100303020c3708060106050912060112020904110402160312050415020c0a0501021303050f12191b081c150b0f07 62
    0x4115540c00481c40c1c0d092810020f04000384403c08918101c00079091282092060f03403000302240d802001d410707140c0c400341000e07240001210b46a5100d02e00000401c441c8403110242e4000b124840d4084641145d0000204100005951150468000b0207c107940100d00002d240c8258003003216030305840301da10341c0780050500d1402d0b081440418400904150b040c24041401d04941480c0c001901095040130300c50882d1001001e40a4415034800f0040307001d01155a050044880d80200115990840c1e601044601e0030100b90590100792104440d108004243c0140d41c03140c0c0d8003038052911b80104c0700d0b010000350407500110074184034254240700011000d20081003249209079403080003625519249103400e003005041245d981000a160000d003000030150345240c000900800e080901c07505040302c0d0180042020485422241344140074428014028148100c00300810340d11828072408007405e4039030f612920b19200082510400182c80d418024000c460560141e252900354640c0f212 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781094001 1250 781092751 781092779
    0x60e1c08060906040f0f0506180c09040c02100903120c0806210c03010218040e0a030f0c02150a0c050c2d01020307170405041a060a0c14010f0f06080312010603090804 73
    0x51b02e0001d540b00d043c4101072400c18014089016800c0c1401203e25185006c06214022004036038011611031a0500840380240901e414400341c00d98100500d05003400c000b0242500c915241096031302d0800d01c4000c0e640329810041c49400050000080304519105140000039103841a004074000d003014044169820300050030b41d42c1c26441056800106481000111040c001141c80307240e020602000000381c01004904181c240303810901045400d50000c1200390704040d1902465140010b0b40b1303800581c024404800450040c2e040b90a0494000700780520340142080201e5519043c8244580c0c14824080b000000301061064900342401c40c0e980142500701d440c459100040041070500c242e0505114024820038030440c0c45001c080340741c02042c007510640001c007041110818100c0284400b0340c03c1085600e402c0402046001914107401004010402081d400e41e401d1070000111a1000000d1701c1c28404c0c21401564075034a03051003600140388150302228040414480082c03150800071303035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781095251 1250 781094001 781094021
    0xc080f0f041b12061a010f03090503070f0f06200730170901201e0309010b0301050c090a1502010b0604060f080f1506160b04060e1c08060906040f 64
    0x90520f0810b1402109035104040b1405411042d80c50740409607034000d0b003881070794038103080001d109072941c01c00305e08600c10b01c20f014290201000030081000300d000e003240030702c50280004000341c00000344000407843d800003024124500901929011038100704458040481c403150b11455210800802680804600031580100d003107490740f0b40ca01c0c000d501081d544000510004c00c01180200800c03041c0180c4902720f440003050100b40c1060343c1001c2c2240c0c43c030506002100544a03d41001d1180c064400403a41c18000d5082c4800300b40361600382c000351540980f004102d1001c8034200742302000306400500d081b10440d074945030303d08200e40714400240003621b103550781e041500b00e442801410300040a000110000590820030064061301b10000e0407078002120802c1e65001c0000c138103030007956500c50140407400e4090502c0204a83c0e030b803000c2c003250b144600342c0c1e030f044020b4002c4003407044603415800003050302c140c0001c040303180068240f68049001007002075907020f10342d04941101c01c0456 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781096501 1250 781095251 781095269
    0x110f0a0e040e07031502040f060c0204021606150e040f02270703020711010804030e0105090429010e030a1a04020d0f060b01140f16081902010209040c080f0f041b 71
    0x2421300501100710003ca480103560304095240c6460480c0004240402d07104400402152004c40000c44d5500d03012030381c0c01020f940c2001180c5400e81452401031a0004504074205208400020f030000c4040d8258419500300942010301e1055400303101103841c40c4110300004d640105004907860207603c50040c0545241d82d40142c88071500c0c03a20b40c519807985091541400021030411002940c090201444e0030703000e1030095200c1e11048003040190006410f20040200340780c0c00ca19008402212215503483c090303959400c6480c04109140d00e45101c5200980b1340ea5400580c0352820301c7d8200c070a60003a1002e401031401682070703194041c0d4160458400c56450342c41d6484200765689c8400841a04101c0e00034003072078060402c8001800b8400c00c0407039a08200306d03407002014810020b054880030403428841e07081da41c9032502d00900039032028107881d01c0b9610309610800b01e5842440c0041c4981d0f017103244002661a00485030500300d1008100300c2e00041010300b4488500450602c10008000b801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781097751 1250 781096501 781096513
    0x150906061801050609040c030b03070602030c010b181b04031e0303050108030f0a030e160f030c0902030112020d020f03100603150903020303061908030a0918110f0a0e040e 75
    0x420060007000003a2000400a4448010b00c8159520821030f02d0000c01141c0028181d0b0080c0030a6002d0115580a02e40c58040d12b140082c081c2e801000400a400c0d0a100030000d400440d010085004a40e03500201c03000d44100000364140143c0481a0316403c80510083c2800d03501e542d007101c24248001210824804000c001c020540c042c0a0700d400742c29a0400366040480c00940c242090081d56681000c0603194049058101c9040c4405800c0d49500c418807680541c4031740c0041450b1020b44000c4425a070f4801c00020a07146c030388241ca0684d202d43c540d181810505808022000e049800e0a903844200201c03a84c6296404002e00c1c031482010680100f4428614142003064480c601e0f0741c0e160f1241031407140b40009901000b207a074800000c407811000841904240c03140220b240e08062458407002402d4042950050307050303c2154801e81d101c1c06100012070b460f200356481c00c180c103520360100707200c25006210072002070000d88410b4a496000c0c5845040020183c50a811803010350750080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781099001 1250 781097751 781097761
    0x307050c03130b071b1a0a0c020306250203070201090302041a0a1401020c0d050706081902040806010e060d020102070306050c0d09060b031510060503060d0b0702010501060207060c020609060705150906 88
    0x8152084581c1d410440300318880c910301041002c6c030002604e62400c84020001c2c080a42038041c0072014805a0064212411072902200d4200403158041050035851000c44416042520000442c0d1500313a047e512052014655802c1c400909486c040c500040700ca00e44000d10706485503140500203003050f03c0c464000d6011200064100305a46000c00c0c000ca480c800d0480200d0800680c803400c842e803600e001c00c031582d22058240f841141251001801500020b80004ca51030f000555034140c414401a01005440d500708010072143d00c1c000081c00358104402c1080401d0459000c698400300c140030941c0b50030920b90908040f0341110008860b1560f603040e90382e0280c1420400c0e030142c0e248522984949044c0540e0028128100d4403500c010442c0000001320355888000003480740307940c42103a680c0346090001000c1d0103420b090103041c0052007000b40000e0520321070000b440c0c03219005080503281c108580140502a4860f2605441501c40e59901e0b8031890003c40c0440c1c8100e5440000c4e0001d4100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781100251 1250 781099001 781099013
    0x1609150e0a0f0f021315090519030302150105090a0f0e0d180501030203060a030b07021c030b090903040b090103021b0a0b101e0501030504050a0606080307060e120307050c03130b07 79
    0x6644480e109240c0705000303070048510032403084004d40b00744c0f40d04010102c1150358103d62403600c80e00112741000c1c81c2c0000e04010b40d86410000306503442902954044000c02107007021030a0244100ca512803070303c501040c40b080792544103c41d1020300307040104256202d070703070040c1c85e01500150322400112100250b4140a5070403640030042e00b424038055141d41400000220080105e00005d40716680766030100703141500030070907030503042004460004000b40090014000340b0b141c81c01540030740d180c00006190100c000c0125003e8440c03980ca6a0705040c9a040114025004171f92a40c100300714005041182070000c001c000700d801d02c2150120994a800714203400103100b00c0e4840e016003075078401c542000d9284400c580f81520001e1800003155680c600309145040940040030b01040d01c1c0c0100465114008802414803a001e20b0040c880d103a182040a65140301b910001c84049000303201184c8014460300080030381d01012000c403410188403d0340340900d20001c0d03101d0310304907a0010700e030010404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 781101501 1250 781100251 781100261
    0x70b0406090c031202031c05131e0609150b010e0a1509030204090c0f0b09090109020a12140601140304020312090a0801020c0703060e0105090607120e010608030711031609150e0a0f 79
    0x10303041c0904c01411b182114024000309d1070401045041602c032251240408a004507803450781090042c00812864204181d9001d80803000a045908040c1020120f50050354040c001280161110b1034051424030001c0c240c02c0c00d400b1240c100800d002002003da03a85000c0c0c00341403801100e83c9121185045880120000c040c0c3c00351003080d40500012029681c1c0011203411910f410201680e00e90403024111451004104118246450314180860040902140c02d1003a0001e07210484a0200d9107070f07501240c001254000d40c1a4001c141e074020680401000d00f949a02c040c00c5c1034055502c403405142645c20020154800364404842041840458082c004070201c86c400208524104903050b29201d2800030403910a00044060b0b0300e40f2074500364030004910412a008000c469100c1c0c201c60b85035846801c081d50100c510300541000d0b850086043c0404854120f0410b003c0e40c682074440c005420340d210403000c1110500e20000300031954400d0980f04600d440c100082920884c2d5030103080b14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 781102751 1250 781101501 781101547
    0x90102030a0b0a06051912020a0c0506180c042304030f020607080f06090907050a080313050a05010f0e0a3b070905040f181406010605070b0406090c03120203 69
    0xf803004101003040a82003800c640d07040c0a030703240000c502c00590909681c44074607445459180c074800106950f040d0b51069030400302503c20800c0e5400d503103550b200d140c11001034280d8945d2603002820307110b040340b0f4664804014a01500a440340c080760070000142070b504200c0b4264081040d035015025a00d505000c02c60788092141025041c0b4102000000280030380201500d005d95048004038004400820440d0000c1c40010a41e0799196100c00e0310684a81002c010724091a40400002c50a850800d44c00301c2502c070103943c3e0080302c05508904840071103a4074461500b040c680e19000c0344402c0c0d5442c4020b0100a48205841c591003008202c1000c0355a03040e441088204040a10045941c016914021078800711004600300105c40c1c1c41c5c0000b010444095540100d100c080003080045a0395401d010300341d02c40960308240c0e0b0b0341311300381c60512841d00010071040b03159000500081e1140e002c0c41450b0302541079103c00f192640d03100041c0580300d1308102c000d0f901c0400c50b81c4103488050390742641c0e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 781104001 1250 781102751 781102759
    0xb01050102060c0406260a0b01080c09061c0f02030a141501020601120302011d211827181b06091002030d090f02010306080d170a09050105090102030a0b 67
    0x1d14100401c000d0501840c0102c03000c0000c602c0d14032041b200d90025906002071160241002418200b026500900c0c01051503030100d8481000174078446110000d03a43c80c007201a000900d080c400c251214400c81039504900c130010707a40d000c03103468050148041c42c85451040b400040c4601941c042c5110984000d290041164085500d190b10740d9001c00c03924115107942c100c1c91840012440c1c00d901400d070706640600e8284c00c2103420140c2400c0020300740f419101c0b481d5042ca29129039510701a19129018400c2c02030380c0d40560000c030a0800d80614904000b40c0c031060301404151500d800080310060340c03c00b600c440703610b60001070900e050010f40d6042041c0850055031407900380100e102400751058483c441c1070620170b0324910b94028400c0359217509141104000075565450b200410102c910810790000340b500e0f8012a04c0f1200080710910018542c8850310304c10380c2c003c02070031000c1005024191042d10b03800072200003007090003001d02030102d000001d61039280210014080310440c507101c07449 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 781105251 1250 781104001 781104013
    0x1101022404150b1008130b09010b150c030a21050901090606080a0c15050903070308030703060906180c05040f0f08010c02070b03160219050610080304050616061113030b01050102 78
    0x10340c0c1d0381d03140800d0110404c2c0c181459240e07101e8440c4000200006805030103d10f5040411404c80d50640c404044820102c0360307030b1303d841d028140c503034000c0c090350100a005038410011050010b008028900e00840340c680f403515103c006040b440180c51064402c0205030391110721440c100a0705008002c041d054520060002c8403441c0c890041d02201072103032552000307114101c250024230800486180d00809030848000350758900c1d001c007080d441103603c10002468810081a90300b168001c2a0840f5a0070800105003607400d0403204c01009651246400c0c41800c03c40028401e152940c1c01d00104800c01340d403420145014001425504103446180854101081c01e0008000050a90340c101c850107a14090000501704145c0c6041c000e05d041c0c64541011400c5401001000140d10b44240d0b07612000d42d00e9942d5682125940703005500035140c1c405030a1044110500308591076244080c050303000800d0080d41e06d82c42d66819030100c0c1039003010341421a014001d0103580b1130810b004220138801483c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 781106501 1250 781105251 781105271
    0xa180b072f0f09060409020307080307030813020d080d0e1903020c10020303240409060203150a08030901030f0f020703051905070206090f061c020c190b0103110102240415 75
    0x482c41c2e94604980e0710890b44440030440603111a4021074081c0c1d80501100d44050301c0300c403003541d2038100410880c00985402c00040d40e2040c507030041c60030706901030288400d0298607a101c00c12504182c0323800c41c6841c1d070b60450102c42e00d01000510130002c2c05031140b00110f2154103000b428201005030040c040c2040c40780914020350700004803507002d0300d10109510040c42031240b91041156410a5a80c002c2c10103c03040140070765a8011402180f806201d40f542070303081000d01603034000b1440746280303540060040001c40d5019800c21203500725a070000040a20f030501c0c3c80e0b0200d801c08101a40090004182961300c40b024000701820384045c1e04000c0e050488950004030184980880d0714021a107070008039109442c2c040c20b9481100d422481400b02400402d03020009420480507052140304107920441d40310840300081c401c3e1508030007190016820340e108c0c043e12070002000341d4114860303100841d1003004140d02c0d8200701e0410000c90000c2c3c0c1054200b02a80304006a10b4003801c0340f40040004d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 781107751 1250 781106501 781106509
    0x140304050c010e0d05070803210618070504031b0302151204061d1e06010f06050d021315030e2b0e1c06020306091501050a180b072f 58
    0x540d11001d2820070f0340c80308604040b455015074500001c10b5482000700210300d0a8010020381000c5414070340711070f26214078088100d417001003501e4003030300020801d1a1018000305140002d03440f41080c20010701d00ba42d03d58603480e00c0c00d510b480c41034202050034014030841c03178406003014140500d0600f890034031240164912512001401c018452552154200000388180011840300882c0c8401c0d904500c01400c8604000142a00460f22074080c0c3c00010844020854000013a60455541d4a0400141d03500090003940100355800942e091110001414805d5048030b4004846941c0d0101d034804261074041d180c5148403020a01055000340e03001c01e207041d4011124a101501d151501560010001051a5500189240c511161000c2540050042c240c00860003080c0039580e540d140d0b5510f0540341c41e04600e02400a00003402082900e0310360744510030b40071b0407441d003441d40401ba60341c2d1005607411360300221084030100030f03054140780c4d40e0b140c03503540c940d01585030b4200304240e1500c84005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 781109001 1250 781107751 781107763
    0x30b0f0a0e01270203010902070203010b060a05040504020702040905060711010e0706171017160801060e010b0307030e060412030c09030201080a0e100e1c0e030309011b0501061514030405 82
    0x80340030181a400401c1e0343c2c0344041c1d04607007540c0f40c1c910215a2945c4524240f40603601c40c4509a010750b00b03007408051203043c01400c0ba4100b2095a645505281c1403a0400029610540082e030380305444a40140c0403c0051100e00d000da00b40c0c7d11001c040c0898180d8039420340e05542ca14080a07007040c0d82c00c02c0003036040071180561401c51403940741c0b141d13036400003103070040681d4120180700041803100f11100b9800003240c0c008014480001c0b0400ea5441f40d82d01c2c00e0391700c1801109820380000004110748420403000c2c5400400a050200704250628511854000c04503800d4a40a1491070341440c11601445880071040403458051810381c11030700007a0900d4006002d40d450075565440c80c0d6a100c40174009104800b240307240c02e10022031140001030303661540060b0001e00440c20b038050b50b80c25005108100350101d024029500f03006900c80199015141841840c14112035000c40c00001074080c42002c028001c0a001c2da9a010501d420007005602540d40e1207160310001c209104c0854030001e51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 781110251 1250 781109001 781109009
    0xb0306160908210d18030806030f0615060a0c0f030c17090919090f0506010303020c3c1809010c18030b13080712021c05120c04080d030b0f0a0e01 64
    0x500b0383c1da41d0505141a00a0440031704c1d6104800e4000606401c1585c0144541d004e240e04034200ca0381c0d030340c0c001000c580707032881a907000f44001d0020225001c0c60510102a240304221420140005c40158a5032038041814200032400280703043c81c0e440030843d041c000307260604510980c440c1001c5900003c2505050054580140400024180312104005070001400c80707604c100d0100e40041c2e030b85807883d035684003800100c000d8006c804510b005414401c400110b1200c62041c45c1a640e146003441d00c602e00300100c0108d861100701c2901c40f200340c0b0b83e401c9810411040180c5058a481d010400c20308681110b01d03420708000f0b0188402c480d00c1d440000030004d0341e8024a07140d906440d03058020145011002000300404800308080302030001901b0390307202c040ca294090340e6850480c100c0c21170344001c4030105035012031800e010500404d2502c15110b544401e8500c1c0d0949001e44a1080c1450004030207080340019884154040d560300300528017600081c0151131200c00907050040b240e45144c1e050103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 781111501 1250 781110251 781110313
    0xa0c020d060e03040e1006080c0301060f1707110f0c010e15070f030203070b0906040c0303120b03070f0812091f0e06120f18030405040207060b0306160908 68
    0x149100500100b9403245454007002d8080b40c0c1e403655241c04c040001c2c0800c440b800c030226000d038130000c1d400c1d0040945600c0b850403031034114950ba08003441030b1683c08604a0640410201d04021600c00f5103541c1400d00550507903c0d0403188080b4071820b18500090b03403289a0147e000350f501e04e1102e0760800c2660030840d808a40c02c00c80700c41d4115808280780107501024100c1ea0842d4080740a150700400205000f60240740c00b000035a03207078035034560394150a81300188101026101000400e1265915045a0502410200f56660301a0000c4d140c400390f60000014261030000030840c100e0b040240c08080c2e03e00d6504281407444480000e00340d0701080222a003c034100c03400d1031340ca980c4140716555400310700070301340c54460000c9903008201440c201d540141c00300c1c01802007445541080c3d2140c500c840d0100c0110300c4d15083c00181700113500404000c454898503070034035510343c2e5014082c1520401c0c0d01505604044045a002000c26101d039000d6010364014540020b013082d0740000788000124100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 781112751 1250 781111501 781111519
    0xd020d0e120102030f0906070c12030b0414010e010f27020705150c0a0f0c120f020703080d0c080105060f0d150302030105040c0302011409010801051005191e050a0c02 73
    0x40440d1008805000c014242d500c0007081100e04540d0200c15801a8044400c4400c203584540055a080e01030030000760a0014100650303103414070a4000211a01c4040e0011a0000c5c04289412a854081e00711004207400107006012090701c1c00b034040c0040501d06104464004c000c3d0b6040c07000440d41ca0070f14803068000442405000c02080007800f00000c1c00007882c1d40c0c1c549a8054203043c0c0101c1c0100300040c6040340707012407251250302007040d415006440e002c0240340d102c00c107036100f94844041704254060b03c50000040340c030540141460040b031100100710b1050305200202520816000640304420030303c02e080242e514101554138500e407400703000486100350300c52026025442c0c0d0009500d5801c0c10100020465858503600459100380c8640000e1488080f90080d20b0041904a50010700307850700411507854040d2060b161910b040c1021460000341061031030782c2d1b4010801510106003102401c803804841040f081c1f0320200c030303858060f081101040c0d0090001c45003200107885103801c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 781114001 1250 781112751 781112777
    0x110f1002090f03060a0920280e1f050904112116050a0b0307080c18061803060c090d080702060705010c0906080c1905130806190506060403051e010605091003140d020d 73
    0x114400340249c50f103005c90450901d8215251220440014400154a807201400041c241003a81d841c2c1d00643d0301211440300c4110314424010030754070b02c2c001c1c0c4400e4007103c2c1500100f40010302c048400b940410803000381140c104130034032600b80b9465015200c1100c0c20010024007691042c006504550848440c0f540c841b130f030b840d07030750a207013031504035103030300050005210100100030301c070f003074047d60003903050b05d42641d1183c940881030b001d20360740c29401c07551070955840014003400080c00c480b440103100b1810201140ca0b0542110340016903200840d1440005200c0c01d034100803260707407210ba28464039141041c08201812100b206900001c14000082200e0075151480c0d00ca01c40a0300e20b020442d28586070000009040490844040c10490300d440041030150401c0b1003210241c0341c008009104c1c010000741754041d045680404406070f0355903140081000d640d9049400d01a104029140c9102d60550414240e0641c1104403505194090400800b0f602c0d008164403a031b101c01414001c0e544504 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 781115107 1106 781114001 781114069
    0x1f1d01150c031b020102010609020d020417191118190b012c0604030b0f0a0e06060f01080601020a080f0703110f1002090f03060a0920 59
    0xc10f4840c500c02d400240741c145090340c418800090120b6607401d41c14100d82105c4401c000f803980000e410031030082c21045406002030f280c005400340c0c94028101c1080b160b44080e00920400822124140c2c607501c41060010110000ca84441140f41c244034004000c41000b044401d11450b009401d40c055120f803070240240429503403402001000c400c140c0324803a2103a490b0540c401030422000c00000e40b5489101c3c001ca040300806d11040c01e101c03140e00c0649464588034415640a401003007490703a180120062040e1003800e1140c000d03181c2000403401c1c0100a540500880c0c000580b2003001a2103000800c01240030756280c0c512030248500640d101d0803180c00042d0309522100c0107080694496008010000000707251800040440d008641007907003c845001440f61795001d00d83c148a00804c80524245030804175502340d800380d4001864050442030841074010801e01d440f50710b6a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 780935251 781115107 := by
  have h0 := BRFrame.cov_init 780935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 780935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 780935251 ≤ n) (h2 : n < 781115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
