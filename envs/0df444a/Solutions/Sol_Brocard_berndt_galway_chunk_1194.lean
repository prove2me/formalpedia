-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:41:52.92032+00:00
-- url     : https://prove2.me/submissions/72a38a95-e9d1-45cd-9be1-75edcb7af97c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214568345 ≤ n < 214748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214569595 1250 214568345 214568369
    0x903120e06060607110d0210030605120a170a1407031215031e020105250302071202100c15050c0a09050607020607023a060f0203070e27010906 63
    0x25003000d1511410112075032540a0014040e00c1c0200b8600c01880040311405040200c43c0380068000500010380050504006034480106011504140c08104620a4070a0041161502c0d0780c1d034000c58803200e01d200107611100841c0d51781c40d503032280350b1300180c50090310441646d441c0c813805c0c000e00d002c0311210300c042c000781030050b8000754140d030146400c1100e403c1031002c02d8070804e0000411040a8903982a07040103810701c40c0140d05040328000c5500c890040d980f45c2c40c0f21040b407074040d007040220f511042ca00c28081c1070840143c1c0b10035951802040d82c900c0e0511081005290000c41c3c0641203070400e81d403a144c1420060209078040040c21403112a03194400305507921810880c1c3c070700c207030000250488001c3c0718490040c00c19402d5000ca0108241c8050760402c1c0341e03c1001c00b07002d00d075581d240030265803000e18018025140300309130412126817400d61440c40e0012000d0400001c40000c0e9004040b10403105003005c0030805052003466820301c000c40903513034502124026020a003c0c1c103140c10780c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214570845 1250 214569595 214569611
    0x4030503101a03100e1b1e040f080d0906230403050a12020610030f061109030f150c040b03190b03100510060f0f1101090807120e0a180203130501090312 67
    0x380c0c014041c46034603900300c2104444405d051800054007e00254100ba14a00c40041d00c107218120142c00a040150b124140a070300d4200710740e1030008140e00d18414004c1e081001d001640d4070007070320345200c0c0d0b082c3c000c2850050500e80d680001d12659102030300711300030404030604000004a01c8400551598200c40d43c40d00c607440780081d0a240d40c80020500c240340c07001100051440d4008030200c0b072481e000305081502c0d180210742000407000c0500d25540081401c0561031034100e08494000100503000d85c04c05051103c051901c0c0310250442107918800703850510002c00710341000302c544001405407100c0a1001030480301810302544c500138a6001c20002141544c42080d5010440d40c440c2d40309074465900c007a060f100310181204516881d5281d090590100e03a03082c00800301c080c030401102e81c2c071907007044008000114420421780728078003014041102c4524104c00c0c084a40c101540181e072071302e0700e40a8801c4d17000c03a464010004d5080c45a90340078160410003d10300358018200602c4611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214572095 1250 214570845 214570859
    0x51c02030c0703030510031a040312020a0e06071b090c200601050108090f0111031504060605030a0c0c0506010b030402091f030b06030114010801020318060f04030503101a0310 77
    0x40000c070703040464000300303024a5001c030f8800c0e00240e42020320030000b50b030030585948808070701c503154580b440d40a024000a2004240e405000112842c0c05a481142050030413180103000c00b0607803003511312400c80801d060050218403241d02114500401c03030001110740c0d4131040406094035100c078074041400001c08001619100400040c0b9404400150002e07030f00b41801541c140c0009040c6080314072400b168580e89140912626044a600c40c8500e03849180c00c080c0800c01c0000285402d004905010341001903a410005998000301c43d004082040900741d401140d414046001c090114810740c8000200e0134019001140034a00903544884c1ca507a4000b028034103051101103101c102c17a046041000450540021246c00820007000403e0303120b20a21112103583d801c4c1c10039110b42e5400010300c0140b203610090300f03d80040340c1015140c1c44c0f030b040d140944a1a00208040c080c000000001091031446c1004540584408278400200140080207a5085c0d082160314a28815000380085a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214573345 1250 214572095 214572097
    0x705040c031b21200a02030403121701060f140f160c08010b060c06061003020906030f07020c01110304091a090f100b030609041403090307081006140a090c02030405040606051c02 78
    0x30700c680130400c0b8060880c2c5071000c69118401c11801c60209010100028100b0102c80c101d00c0c08507030300c2c40d8040200c14040890300006070710050a008100031321509041d00200c40002c003d0b1400d0446d0740f01c1482c1100c1c1c030741600c59401d601c1084a12404c40408005020110500780c6045900030084000b4210901074648540c60390094a54080c00029038030745414890794081804038500542040e9081c0c001c148250000c2d03c115241d00303050b00401890319810070865042500c24a0701b15a4050340a195a440b8441c6010703091803507031102658922210f0700200c014403020041d002806030b01c2c05078000d0031580015a684101d4080c10040001e070321610304240d0b030042100400c09070703050b161995855651b5014901396500d03808180529030013564188180801402c10101070031501d90582400000c58606800080100b400d108814005859540240c03003910700060000a08442d500d0050303203540610307032015602500f00840400d070280d00101900d19013040072401a11510045402c80907 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214574595 1250 214573345 214573361
    0x1302331207050307091509030804091406030309010c1b0506120106110c0109060c0c03020405010602030c1606020a14010e03030c0405040b0a05060d0b0d050303130c0e06030705040c031b21 82
    0x39460b00024460411506d80303c8001200d1800c100b441c13070723949136a210344540055100c004025a540c940a04210104032075039840f40c01200a186488001070000c0c140d44804000a4881d5104000c4c840c03182200d00c410001902004081a0716521000074012020000b405040002034002603210820b00000034064207462b0140c50f6510070030b0030482c088414000c021030580704040d1403c0000301680311031141d14041c003072030350145990340a0740029506e8208001107900b0060303613141d03040006aa020070041304599012442c403088119000c03509001d0000ea210540700e5000001c00e020440315520028011110141d606000b06007c0070200500d00e006441101e0b0040b10070800b42e81450078590140000e031000400301c4580309019164140b42da0030480351000d41c03412820141092200704900080202150800c0c07e6180c6801c4d00403989811240c0f007801c0c0120389513160518014042d402240b6452003804480001110300da10091903200c1414a2407101c514040010001003042d009000e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214575845 1250 214574595 214574597
    0x301030206031504020d0e1b09010f1418070c020108090f0607030e010603170403060b0a0305070510051b06041401110306120c19050a0902031302331207050307 70
    0x10960f40c8214025100701d482c5030415502a508020240c0f80f5a0603105e1030b05100000c00007040c114503411103402d1000e80050389107209166032030040288640304038046080d65452200983c1d00c6404402260b000d100202c181d24210046004001c142540040b180304024000d0340c40c0040381d200c0480c52501c4485002c940c40e5140c006000003280380d8081c0d0000c502850f422000080c40560faa115818015683d07107143d00480d100013010414130606000b8030007100003c035100d1100c545955100c554070f15030f512689004900344084560340078020b500391982a1440d24229003204131500348181c69440c12101122040021440070340345010510500303510507070761102c1e1813958030784d04200b180ca6007002080310118480c071110002103484422900c03500040c102c103c050b00c03c0c241010031000b008075030481100c462040c41081589000f940080c008250162881c803c0070518540c036050050f0304411300540b2804030031074900506121401044c070320480340c009100503224a40c0450b92444152641d01c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214577095 1250 214575845 214575847
    0x7020d150219110d0c02010e04020a0306090e030405060304060903120603060c08330406081903030f020f040e04060b0307140f190b0c070807060518030607080c0a02030c0a0807170301030206 83
    0x11100307001324101e980300d46c014100540c240e0442c00002c0d0503644480070580000340c50701c02c204940a5a03002d500c1e00040d208002c4d505040c2454041001400300500180007180c451500c0828140101c408810201401800f88186c2e9102e0800d01d000d850320481500c0002e0b44140010700d03454184c0030a00c1180c507120000c64009007010204109000c1910115601c107584840c00120088100704001d400281c11040b2506c51100707080140456200c5040349106500401010310940e040100b11025254010203d88864859061000c002c04a035101150140b29001e008512240f84c5503000c0b0b60f2850881d4100c0f0807002130401d0110b24980c0140d202a40c4004480600001da2200068201c0b00c40c030070211038066540d014207a28108983e4880800304070002440d83c0c80c2d0180c40105080404142e00410060800d1280248908030082801114100c08907004440900c01d0045801c180f0308130044424003900c40c1810241e40d40812821244c00114800b4030452040c03400c10303a0304881e0010025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214578345 1250 214577095 214577113
    0xd0b011d01030818030c0303040f08060108060103030816230d0f020f03040204090311120307030f020a020706110106030501230105030a08251407060e0a05030a0807020d15021911 78
    0x104c1c072111160740400380c2c180210555454280c03810400342c002000d11300e42c4018541d1900d95a2410440c040c1c00441e95038115000620110b90070000c080d07040340824405142d06910020200c42c510000b80e1404051105c000d1117000e42c400080180c00d001c1ca40900c100040000c040c0b824089100351416074a00034402d00000d4090715044c2d1012030585d00900300016a21040d84c800d90a20800d401420080b000c04403d102801d81c0c9813244424202c4154421403520f100e0b008040d588201034422a403c00c180f400501c507a0120a422800007541c0c042c0090100307500210324004400c000c01d004e01d00032581e050001540c2d1800040c1d105029400810301d502d8603a500c05044846510101c17890301c09100400300d900000c06012034040c8030081200905152424450300500080c0b8520f8094400c90b1600014803969402203040c86803da8046140b070303510081c610204010303140381017002d800c0e01c00c1d0f5604031842c405660000e084403044004101c071800030455084c0d401860708107a500141e400b50f425 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214579595 1250 214578345 214578367
    0x50c100902010c02090108060114041a13061512181e0f021002030c0c01030b010e1315030f0c1203080c0d06080303070203040f05090403020a150204050d0b011d010308 73
    0x4540902401031403c5000760403540c0204403085c6080c7d02c81d601390750140c1c0040040f0070b40c0c45a07844648604641c28080000c0c9900c203000070200e4009601c2c03040668030403025200d08240d00203c028240c80590040704108600060102d1541c50000652541090f1a51088034000c3c42060055944070407a04030306020030142601ca000f031910110b9600100186030303c0565940700e080307000004541d00455944141d202c000d401c0000c8401041d0626090803140d440326030f00441030603a480d07070654000e03001c1e8510640541c058280c8443d071503003191207130101105200d4020794800f5010f00031441400300a0741d0721184158038014560184c0000c01c0305d0701058200d51a0401021044903a40000c984940c5420300b85040d68402d4414101503172000030100302400710081901c000b00b00886840c800e40c685600d020b0f444691541c00241004203200c24910b101e50315a040d1742c00361401620010f0b0210783c2c1e1424142c400c0c0b081c0101401e5900c522642d03981d280d0280115816a68001e4120b41490b045044c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214580845 1250 214579595 214579601
    0x50a0807082e060b0a030b09040308060d0320070518090607030207032c03010b040b03100e0f0607020d12091703070c0b040f0b0c13050d020f0603070207080607050c10 73
    0x40b1101c4454a42c61414540c00c2640c001c0c00043c054040c0301c1c0b43d940030301c0c40c406001c41c2c2c2d1030410f00d8060041e100400001c6900030403503a03132140b01580c0103140d03024585000c4403105271780400007100b0500340300702400116000a004c410b1743c0702035982c0c0148001e485180080760f00119095a016404040010703401d03031081e005400c629201c1d0500d038a0f8007031955101c0032508105001c3c03e544002d075440100d9949824004d20401d824192406c1003103000c1c00000c03d07280c0c640c001590000c281c45940c1c5c810113480810030070359005991402d445260602e9103009444269419800001642c0c8000d515031300c1c080c61140c14074295012200c601307050908504a01d02d0b4200511038020f20074004c0460020901e051100e0748582d11031000380c40206550303d421000d024014111054000050244101c8003500000c000e041e60400c0318820500b44140c0f000411002011011542081011091106464000404a00340c0e400300041e9012991840c030b08544034002c0d40c0c404000b0b0303400440014551615a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214582095 1250 214580845 214580893
    0xa080a20032803140a0206041119030b1302030d08070801060f02030a081f030809130203100b0f0706020d0203090f0313090203090102160b10120218061810050a080708 73
    0x4213103042ca01000d0340035030030140c202c44c840d0009a0000020042004070b0445003810040c400c840c020600002100300200000305400000c007012194004100b265040c444d2038904694014200c9907120324480b070080850b0010768141c0d000c100580004240640640f040f03a001031540c1d030041d41405070b01741c0c1c11101001f002e04105480180c447c449444403500f0a601e5010b1401030130a00e5850302c03075034203000d188492800716035aa6032051041c4004000c803101c1c500200d442005505480b1000b07400fa200c1c9a214201c4000c200c50320010300d01503940c10b40e4025500c1030302c810301603c0c0e1002d01d00c0362064903489109005034882c3c5403150240261045903000d95000410340000504105c1d01210000d00c04802e4841540c207040b081c0f0410169040b215006c2000e0844c0d42000450151142d021a104d0b10b101c4006240da003601e040015003640302d01c03c0703840c00e8901c204040c81c0241030030841818a41500c0c00b890b0b014450315000810889400980304046034948001130141c1d02c0f400040542240600c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214583345 1250 214582095 214582097
    0x509060d0b10020c0909060f0105130e03030f01031a0114011209080a0c0b090a050a030509061303150b010318030311070f0303060e06030a050a110a080a20032803 71
    0x2035024007880d91210102920461002e4005003a00b80305103040104100004041c3c40140d4414010403030081c1a4101050450b07405a400c101d6591101e6020702c05041c040e60440e034644800f10400c0402d0781c1003c40c1c039048034050b414511401051414140f6a15402d00501300750640340b240300005540b24140e00c0c140a0307000200010b440485503500e46003540302e65112000161040505820305c2071b251842034100241c200148860b031196a503154445448a0000d002c1c00070200b002c44140c3c40f407070100c0e0400402040c01500d4603449280c07520550b9000e4204072440c13480c001d01000700f54042d06c620240110150305080f0f000d01183c0d4118003034408200900e00035102030054600207074031203401d0b21400d8820386010440c6410004039900c5910b00a11592003548003000c000013007500800d103082d41ea03802020610204841001140b10490039500c10a46440741d140342c2000c1c01903042c1d040010f02da41c035010310035004c50704c010075039140d0860611030a00e0b645e12101008503051810303070341252446 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214584595 1250 214583345 214583351
    0x70c1b0503010e01020a17040f0303150e0a0e1204140906010207032003012a08090304121a0a060f061101090c0816082a0411270906010509060d 63
    0x19500402c0c252080c0c2400394140e6900450981407494100440c81c240b6980000e9031a034030b00c0c058443c03201100303030384034003a00f81640c3e501581203034120f400300500a8003103c220b0055600f46500c0050003042481c4c0d120280c0d0107542e84d4006060100b1040b682224021004041141c21400400c0008080940380300c2c158418400700100003410540c07007500500d5402a910000d002c01801d042c2542d07043c505d0341482c00303004015a1762640003000105038141d001d1030a01026610369041ca803541c840c541154901e01c007500c485008001900829580d501810f44001d09251665001103080c0c1d410f50081c0b400e01941d140c4180301d0540304164540034551224008105403042d601c171242074000c075410565213500055542580106c440c81000010050000109403419405580a000240e43e0141030007203001200c801d020740d511a0030120001030400b4015984640c40b600481c1050064000c003522a101e080c03501245281c6927200b54407078031060b102c4510f40b421010402215030320106c4018005a6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214585845 1250 214584595 214584599
    0x2041d1606021606051b12040f12081b01060e010807032006070206070602040b0d02030702010c08090c01180906060e190e0f13060501080304140405010311060a090e070c1109070c1b 79
    0xf00411000b03200408081900380d0751400c00d0b2045182721031303540208c4501046001050b0004041c4022148900d5800c044104d0a41181c040e01e409072203540d0007248038000c02c8001140c2d845002c10b001040307078414050b00d0b074481074440403440d8400405445607071004045c49910094100030b0020450b291040400500e05610380400f000540c0003204204625a401300401004640910400390b580d40325040028451902d000c9880d0364100102d2181d0401c4800c000c5d400c12281c6112444d005042d60800c00c1c819680c03501001003212070141c42046c4660001d06900c003000c0300711039030341c4203480c245401ca0780c56642d11643c4512401c0094030300c00c00000b920005030b000c00d185100751806040303203401555442e031420088c40c80810a035860148584c0c40c00c001040000c060411880180e00b003a02d04585482e000c01c2c094800c5506507200742096a1340710100440240d01050020f42d1b03912400011039130000300d2040c04040b113400c90319600422600440000400d513240c10a4038030800b8800b010744015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214587095 1250 214585845 214585897
    0xa12020f0610050405060103181212050f06090601110601030809061611040522020906030c1801180614040504020a08010f060e090a05070603020702041d160602160605 73
    0x1003400c4078a041c0400720a03900344003a20345402029040542448c0620030b54103a4aa1071a216a02d01402003d1200e51025110000e00030780507406800300c151010045440c0001021030350103c101d030003511650007107000400c19070080004041c3d810411000301220380c00c55451440a40c00340c0042e5a000809004182007000000102c01420f84215a043c00e0a40440248000d0b1a0041c1c5007010048030990040003c014180e001c1ca48a5012100b1481c0c0342c039010003203401c0c403240240050f0001100414000e0701c800712121b05049945108501e001c00828041b190120f6a0382e0150b001d11545c0c90008282c079141c580c100075000b50004102e600c1c03840c3d462110508403280d0000702c0e42000e4072410701700315402601524951103552400680070b031101c43d40d03030301e9100c01c9603004000906501040204c19500c644d440010000d00e407104804c006c665141c03509640d12000b080c202e0189005207804a0100d201103255070b5803808840625404c00e0504d202500d06400c2208482250b00c0d0b450740101d411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214588345 1250 214587095 214587103
    0x50a090e06070309030903170a0f02121c0207380c030a1e06080106061202040b071e0209040807060c1106190e0102031303090801050f0a02030a020c0708010b03010f0b030a12020f 78
    0x26a08c0c0c0c0413050341c0e13081049805400200c0c81c440900541d0018010b0f03400d0200c0b680b0072038a00700d0405070480454203814101034000d020381c5002401503d038400c01114450612207032500301c50001c4066a0507200210031402c1c410008680c0c07443d440d10b00b84041604401c1ea50071205603c1258200300500c07805280340401140d0030303a44011200d07916950f0400481d42c00c08044041001a2603003545804e042c11081000c07440744000c024180c0301e80c9800c0c00c0c9106051203940c003489a0042800b00142400d0420941c19084801c00b40ca901d0f1070f00101c0c0d40698025449501d80e83c0105000e00000e541c1c0e140d00829282d00101c80124480c0c9640702c075141c0d00400e2000710301c91190f500500f818100681401042e6164581040d1032903807425091001607118540090386c0100058001342c0d41e0350355256000064042d02c10410040e10480101055034101034120440590f0203500030060086a04810019200d50303154860b0141c10010304800410403c1c0d000c081ca107695401102e540e8513103e10700c0d03450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214589595 1250 214588345 214588373
    0x807300503070f0905090c161202070f05120c040c030908030112050d0c0302060c0f09030a030905040e07030804050d06060e04080d060605090906040b0a050406030c050a090e06070309030903 83
    0x15000010003194941200f0304881045451402200b100e04040c0490407071076010f45110350442d40400c40c800056054852004000e6000c03800f41d0600060070f00103940c031800c50140c40e00c00d104004003c90035003000c030f001200c203a0450000704100020202448018003080105000f09500c0d403400e000403900d107100840c000c08034514503018800c058200182001d11031000f803410401940e0400c0040fa034001126a0818001102141e4925400e1490b044911600d2070040d018010035114a0905400c041641d04842c02030ba401d10100c40a076441c02c1e02c4140070300000b884030205110900660804060169200d403241c1b00004d0b0441c0c031004a00100401180c04031503800c00043c0052006885001d17044c02465141070041c14207880c51f0011340310400c001c20590259940c0d20309c3e0b040d140e5540544100500e13019004010307058507400d00010600300c81c061240100c802d4040040e8844503441602e5240c03c05501030000b61f154054218060411500180d04108a510010020402c400300b5000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214590845 1250 214589595 214589597
    0x20d11030f130f06440408130b0c030406031a040501030b0106020f03070221010906050108072d03030c05010204080d0309030f0906051603021f0209031504080730 71
    0x2095203000d043c0c1e0b5a036141504800e040040300a180d082d4001c40c4400244480004403c143d1400c00300d07003500e0f40c011105103428a05100701c0c0140320501440600400d0041012500e1088454440c107210220348540100c18007070b94070802007004090320035030020301e4030248550200f54405030400080e083c0c81c4c0070782050f126800308100401210381c040101d044994020b0001d5400c00c02030b90001403082d4854141b00c1e50303500e42e026101088900a502010605a000350104111358440e008075a80340b40c00d00800440e0f45040c88041c90a100d510b040e40c1c1c0d0703505030000f0a0012401e40e60101d90035508030b007048840e0342d001d100100f813580090104101c5140319030344c00210b9032040c2c00c1c010413164110b46034a0501582400a000166205c01140c00710403201e0260b0000c5100792404038501010081c0720108956103801c2d8960303441d82da400812803440c1c00c400326140320031840d032001001181034a0050486804200000004140c0f010700c40a0669460f170000b2030244c40003c02607240340350410b44d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214592095 1250 214590845 214590877
    0xe0c09040e34050a0e090f01050411100201020301080309010302070f050708100605040212071b05011103040b0702070e040609080c030703080a0c0e0607140106051003020a120c020d11030f 82
    0x2401c007079403009000d5a00038800d02c80030401850080450141e6225004004448076400c0008581e40005c0203200000010003000b04118901410300110030801c1e216079038030421000c500a05402c2c41402900d058803003543c0594600350754500150025072046ca012a4000108900007012030804e0110308003c007203650180030742c0c131004494103044500d1600607a124601c1031104054000c040d0b001240d00100c3d81c284121001a80d100c205412038403030342e00410643c201241e01c01107025807006180110b108007039041c0f03140c8401100fa80c9603c850701440000024040004011807500c3d00702c585081d0060103014a0700f03d072071030580d055074410542580442c400e1002c2c40440e0402d481401c20a420034a0040301c9045604c00040b683e201e0f0300c101601003561101070800400f001e60003100103010060840400701508500540a50410b1960030b001c1415040c12380d40045090103111a21070080d800b800461090220542e04016402010340b074511041c844903420807070200040004507a040500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214593345 1250 214592095 214592143
    0xa050f0303150a03030f1d1903050607020a02030a0b060a0f1e050a05060409231f05040c08010603050a15090e0f0111042619050c0a0e0c09040e 63
    0x303000050254007250180c80b4440007040886d500c410715080d9a0207134600520201c64113070302e41b100081e00000e2641d200340014464005c44481141a10813284070b46c0540d11180d440c10816030b00d1341107205c00a134068010a441400142101c0021544400d000f054038170602d44520384a8112200c5030040d943c05030a80b4a8140c010702d03070040c890011b02d012640c1c002043d050001003182402140300b108030580d100c4201002194480d09102c1d1800310410600a0b18685a009040c00d1004e44900c0340800358000008150740c103150088801d03000c0707181c60303e5119928081088006280c001c1091104a964801042c0d03211001c2d58a42c00821054501180352010792440da8284a0003040d161450382c500414036460000d05000d8600702c03100b4590080d151000483c11080700b0008805110090042e520030420a0a60300320900360345000300c0031520040050814032010800d02e0042d0082202c40800284c4c0f41c45590b40140155000540042185080400c403949880111007008000c02814030013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214594595 1250 214593345 214593361
    0x303040f020f1002120c0307021008010512030f03010509040302101b031406130b010207090609050114060a0e10020a0206070f0512031003030309082107020d0c0b180a050f0303 77
    0x2d0a04002c0c01222090b040540501d0081d689000c429141e102980380410310b40020802481640c1c4c0325078024002d40700800107200010f040d91001d005a521550a54450b17241d441c1c800829540074410800140b40b40d42d09110030000c503048010011030441c85112103820711201d040c00381c6a61001e180c2400641c4070303980803003d401c4d07a48010500304421200700c100440c41d41c41c4030340881d42801c00e00c1c0000c0c900100900403410704510750400c0d194141030020009100e80181d000a040300c200c0411a26007500120801c000d611410405000141c40b150800b01c40780b402c02081d41d08034240e4011034441c5e5100741d0100c3c0158100d5403094481e14800c8131004188042400090642a0b090070380398030718a081d0f07101c110b072840240005410035a5a0300b40d00d08100c40c0c40300b150041c007800000e11103020300342c03038000c50b078500111581001405041141403516008074125005990b0040000e07410b642c81810014801c402541000018031855181c1c00104038140002074406182201071650f9241900c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214595845 1250 214594595 214594609
    0x4091509020f030a03090302060d060f06020a050c0117270a05061006080702190c170a02040605030105060a12170307120b09060105030f0a09060e01020403020f1509090a09050303040f02 81
    0x4415021340c010491600c00aa8810111400c0e250704413129900d03601200f048200a041d2504020244010820b010078525000126010075900c00c0084540741030b2080011146008a282200441000c02e03000c00c68084408101034103107116402c441d90284e00642080c1d140020f45001561a030700030500340095207008154500140902d0308040714103041c510002956a4840c0d944410805c607006198030400c42040f040d00018080c0000f280018421400341131b4607180c0201080b403185240003800a014103040c0140343c811400148a40070301454a02c404900d0013103034404903800c00140c98143d441031301035400345008502d03503522006421420120300040b43c090302c950511480f62202040100d0303038480102c80d0b0107012194110b100f51915001d0f000070303000050b4020002410b08174071600118055016000301d900071034440f9811b00c150003d00040c01080c7c0c20020010104010007a0b5904200008542003d4009400034400c502c0762511411608103071011690902c3c491840d0040d403400003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214597095 1250 214595845 214595869
    0x31609050108150103080f09180f0a0507140c010b04020a081902091e0409050d030c0f03050103110603041e1a0c0c06070305090f010e0c0a0b070b06060304020409150902 74
    0x1c04400344000100d02c100c0005200040c014103000030502680c03203424048e164001c40107880c00c1c0e1000f9442028120502040300c0c60002903549400144001c20180502400b80c0c5507a2240e640c070040700c02e400340c401c0c7d0140160a1596494035038600454607180300800c0d600515541d24001da041030b00c2080480c04000182c003080c1d40c014408946107680b911540144926055502410080c001c0c002c24090a00303a00090054090340412205154254200c40c140b42d1090fa24040341424100d0141c04a80f400c3c00003030312400102c0300a0f256818004c00458019014080c0a641c0307001c0d03207118402e9403115140031145840c4580015849010b03040d4400d400c4116100054103200268040b141c0e103010050601080640740c0e40483c0780341302c0074404654050320000007404190400703400e0707c1d1f803403200058041c06402c220f480001c1d903003c2030096449040d0302403201001c40c2c031076208201440d00094011707680180d51303c41c440002289441c140340c004103a00b00c086814441c900402c000e81281c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214598345 1250 214597095 214597109
    0xc1a06030d11030a03090c0e1e1006050d0905120403061509050c09040b011202070305040806010e0402030706030e0102040b0a0e0102010c05030603191403040e0907050a061407050c0316090501 84
    0x2d0218584414010041e60580007440c40d00080100940c2018814034821b0303802491009000c10522444c180c0c0d2409413041e0b814800b100c0300c400d0b2181d00900340d00561610400c00050030922840c0140c1c81160040c5c2d42c42d07409902206d041c0c648090341c1000c1ca038082c0e0320031268203541e2285c2110304c09443e1083c0004244290081100c0d19000c0000b0145204651841c1d21499480780360241d60782c09104806c401e00800c00c0210340300c1c18240b8010b442c650281c0144860707032290704c00000300d54400000300c40c40740e517001d400746c141c0b20310305002a805003c05000706d013400e540034800400e08a1115028043c0301034213607500422015101e00190840710740c07101290401c0300403c20410541ca00082440568104c401c071003c0f81070351420000e00b03041d16a45120094000003900082e1034401400c101e018101f07080a0b1030106680d4010000224458401c290102e6030402c40ca0000480900c05042c01901940607a80d65007400d40c0064101440414a15603041c2184c030207225440716841a03034090504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214599595 1250 214598345 214598357
    0x182e0c11091e09032502030f0601060509090604021806030a06030b0a020d0b030705031213050a12120e09040b090316060203070f020f06060f01050c060703091419120c1a06030d 77
    0x241141400d201d86171000580740401080542c1c0c001c40d102080482c1000f2803410036507a05586428000384550b01c51040244590401800f20b00c5503d02482121481d07000d95250291100303c40c0180023540c0c0000f00903c2c1032076914000007021807401a4040d2040442e04001607036000400000c1c2c00310382c0301c104080e02030752007040184215100000c14800c80e84124450644a2217440746124151010342c0046402402e4040001070311040e03000740e580002d218580380d950080c010081218103480044440b0f0b4401101c10106001c01c000c0029203400c801c049042d0bd03e01072031030804000540821030b045500c26400010000102c0d4810805000640a8405000e4864440344003030741d00c910141c02c1d20710418200c010034142c0e81c0035100311800c1d0407809069983c185841f00015004101e075000941c2c04680c25007130800340c0d01e004200c0f244180012015100b101015440304441101d800d030b0007206120701141e0101c0840c0011074281e1207403614200804040c6040d01c10706003485142154035082c402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214600845 1250 214599595 214599607
    0x12040609030921020402220801020a17130f0c051e09090a081c02070f05010605010f050c06070f020f100e0c040c05030106050c010207020402182e0c11091e0903 70
    0x70304101c0700f07600315011038001d41c841d81000f00000405615001203546c100d100240000c0703641042d005404000a540c03100d200c41c6604400341818000202c41c100a059550aa80e0300041d0340c0c0c40001000c24081c0780d041d0806510761020805800000c0d8103490b140c2403844c6c40503503034600403110650100c0982c0160840c486035640e6110355015800c1503a000000500d031000c4004041d506071901030b07400c0f11a405c2d0384051400d105008082c24002e250000d03105c2059018400d01407006c5500c20000074004204680e29810120fa4100d400102c4c8400c502606081c43c8042c842001a5150344010410000e5820a500d81f498070700030700403894902445c1070480d20311440c1c0c2c000082d81d04503626401d14075a1741c8000e01c0c00c1e174024801c1180003580903201180010355407101c1c4111a000550031f4810f0483d607102100360041144002500003007141d484040d84101070710a03186000c0316841403c4003881d4043d8100041c0e80d05200700c40e0712000d00c8100c9092007001c0b9202040a8001181c0c0000d545080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214602095 1250 214600845 214600889
    0x15050a1407020f0c0f0d080703050703120b10050c1e0304090506100c03080c04080706081915090903050d0c080601021203010521031c0c09060e0a1703120406090309 72
    0x160000c80ca0300c40d1008411702441600d80a1030b90758061f50254811ba524102c3d850040c0081c4c000410540001d070741c000d20300103414003038801c0c60341c40400100461528408801c0442c0e0980c00415844081c1c001c1c1c1449062040c2a00f000c0c3e50007030004130103151154102a1301070101e9000800b0309104580c00c0305429074454010038564195500740c030301503100b566040c043c3e448603c107a622a000da0301c12804001400e507800300c02e4074000c0c1414200c029403980100301003000c0d26500c02641c0348c1c4c0c1c4400e860070000010385501554185200f4109a070909806940407011074481c0c220041c0411648001c001a5603418041c9550349884c6100c1241154100b9000c5026030305850510074a40c2401403094000c40d5042058526034402c01112942c2941c44c1d4401d80c020309900d0070380c040402d01b40c29010070124000d5503030240c4d12101074000b1b81c09514110700010b00e420440401483c40c0400c115048242e20030900b400d105038060000840d9280341840c1c010803094455203c0d202000152468107401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214603345 1250 214602095 214602103
    0xd051b01050f0403080310080312010f0b030f010605090102072301170408030a050c1b010e0706050a230403020d0503040e1003032007050301090f12030b0108010603020715050a1407020f 81
    0x1998018808580347d03503075500394103107403a081e80108440b0311001c41c06036100c15a54078081d06071001c105914605070f035a04401141d83c042556400540e02041005020452181c009042990414411506980d580740c410700402400d00c4e541c80c00b15204c2c40507402055030080b01000c16591a888801e51601c2e1913111142103001c050405c90387d03203448001049030b0140070020b998000c50041100810151000d01304c6e80240501c1109101c03501588000140745801023050b508412030702d8490200440d1280c400c40054140c11030b00b801c6440c410f01c00840541c603030103021403a661050700116580d604002c0d48005104000b04180d400400d03904007400043c0c3c2c0491020074103160400c200d640c0980040c9a20b00309111904400c1c0c256207810840000d000c02c2c0c200032116a8081c603044010601407036403c5042c0c0300030f40c00407404a0102401003080c14440c0c0d0040c40305900403444c4520b801d01401e600c509491080c5c0310050314a446410900d01c80349100e034950380021046c00103002c103041500d500c90307e1b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214604595 1250 214603345 214603349
    0xb072d060902010e09090a06050a0b0d02190f0e0709080109030e0d0c05040e010f0b0603040b0601110106030c060e01020d021605040b13020406030905060115020c041a0d051b01050f04 80
    0x302a450315203031021039000d20214040f44030010800c0303000c0e29210400c55917070304203900103448107401c00011814140561007007040c0c0b480301804080700b03140c2c0c640900c2801082401d52403100c08189400140c1a0980820800030f4046403868030740740d00780540002c00013800745c0c00c270000341c0e4542101000040c6d00051605060541030f5100a02004036080c015145070495200c0740d007041c01c10142492008040d0301030035003400d030442d0801140080c64284045c6010489000b0001c2c4d01c1c90b4003080c0e440d0b0080d50500e101e2070001c0f002042d000d071a5940c11215030040c2d80305001186141440909035070f010b000000781c405591004100d401d038101004404d281261107001e008660301c0041c0c0c10281c03201603859403030340d501c0503046d566550f580703c0040040984040982d441d0041c4c03c0080f0b0090640e118140d0340c90308d950f0040450720390104c01c12005105000091b4038071010603640401d1034403600e441c64406401140a800340301d4801806601c895400d50f50075042150411211010311509400c0d641 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214605845 1250 214604595 214604603
    0x8030405061b1e010c030609050103112101092102010e0601151103181219030e01090509130b09030a0203180a0e0c030a0b060f0904240b072d 62
    0x410740b030141d0460400449a480d10940e00452100d03020500c81500941c0540501e03070303401c01900c3e9450482100301c070b000380401840020520200d15a43c5450130050150784014505107042050304103c0707a0841c0e640e81811551001d403405403249004601c0c00b84051981c0e207000038401d0500000d803c07074a500d014050303600300200d2552448d8240d0711030349108e043c0307a00c108110703a9240c9210b014069903030f0100e2581846041000190002c07060085011801074100c0c00c110520415540d07000c0d1440303400c010303406040250ac1000010030307943c2e20b454075020300e404601c51105440c0508020340d042c88010210940b9620401c4000c40c4580d00104842080c00003d00e64045150440300240364200c290340303c540d04540c5075040c40081c2c40c180e0011405160010400c1104e07814107400d1060f82d0003013030f4000f41028000c3c400ca00c41400c0c6a000340721180004444441d01032404034545a041c00c25400107401340c0c9000c2441000c04c036415502e1540c40c03420041f0008c2880442005004070a40080020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214607095 1250 214605845 214605877
    0x501030b030c040e030409230a1e05060103020738072709050108060915010f2102130c02010f05010e061003020408031b0c09061c031b0b0403090803040506 68
    0x4d40d2080c82402030b20040d2214000c180030503002241c40000d245040000d007020840100080f03051081c042c494194030800c1c2c1d1b940d5900c14000750004c01c00501000304a14103268080143c3d000040350703401d40801e4408a41411440c80081c103020390980440c0e910400310040315502400300352600312104948184400482002d81e8042407074400c0340d0a1103038401c98500c2d0500001203032801d404103605214002c4a4110350040300e10030315014201e1401e12030b9820418000509000c03181e0300c00e40c44480200c025590144070200b0781e0206c0c0b40ca2690244446000d035039848080e01c2283d0a0060041844c030010b001c0c41254104a8003800140c000f4081ca486045031a050010160190f0162001401282c003070700c0d190386a1510807121070440b0250100203002c3e8a10400b03941c0b40c1140c00c0340c041d120240c10545034680c03900c012102500310314429404d2000c3d4102250144125400300ba00091040e0019141c40c01e152a02400e13031050307a00038106a4205210078040740d100c06041e111a000140108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214608345 1250 214607095 214607111
    0x14150d0303231b040608010e060d020d05030307120b1e010c05070b03181b0f03030c01110405040507050c06041104091406190e10020d1113050a0501030b030c04 70
    0x5800400404059141d112070620b80d00d814918210700c0d061044000008048a54010002d000c10920482c040c2c44007150070040144903550104600702e40c0040007803d0b0030a20300c1301d0740020700550303e4804210b805030700000410101607132001b98510602c4020105105815200c0000740e8000e00f14922174881001000e542c0c2c580e42e205202100070107402c40151880581c032a103200700c150340100c070f0b0610550700c0084405080840001d15180440400e4054400da8005004010864524001e815450702c0706124500d040d0310203128121600350840752243c0d80301d00d84418082990802007050052000601820742c4403034000c900c4940c07103980044000785039500b400016008010220029042f0701c501001948204000603a160044e4000155601042d0790103d6900507075500039820344140d003100740d401c15150a82d801034180e80101810101c0c1da11000c00d280000d41c0c005036040d007410021010104400d04100314204080c00081c40c0c05e1090b140d2207801300c0c1e40c803001c0031840d501982e0341e07a8403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214609595 1250 214608345 214608347
    0x40f0e120706061a21010302030c0d020123030a060503150106080901021204030512010e061507080412050709050a111603032405030f0606010c12030b0607060c020114150d03 76
    0x400000381c0700740a0b4409040801001c00c928070780010034841c04105d8101d03192560300101d00285412650700400908583c1c150b14280070301400c41150481c1400400c80b01c0f401d4400d0010f802c0b0300081840320070340d516440c00203103404c184c0d08203a111350b00075040750261f10040302c15588405c3c1501c1e69824030112640b500c8405038024403400c041295454040c4051100700345d030100082c4000700030301701d9007001662200c0d880614101c3c01d642c5203900600d0480c9007010f08104c20043d05100340111081c0e410540e844880e0f008040c41604100c6841c0c21a040a101301101d5200d441e81010f0141403c00240078000c03ca03041500c1090103050a10f55411201341c1054441d4220300303441580f00312552540c4580d210f44070109a20b0f401914401c1c0501443c6446241c0d00088052103480144d40300760441a80e901c9202078107501519160030541c56580c1c02c4180d80b143c800800c1c0c00d07445803100040030508218004d00f10f400003990503800c04584003c3c00a0740700c07081c01d06a4481d0b0708850b440384102c06c5d850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214610845 1250 214609595 214609601
    0x105100e01210212040218071b0501060e0c071b05060a0525030918050c03040b040c0806071206122d0b0406150605251509050705040f0e120706 63
    0xc5039864107000144c0b01051040d41028240901d1003902c08440001aa6094002c4000d00b200e0110000b2403000c050900040403400c0ca5400900940001441544844d107035681c1a104030382030781401500007a46c0d1304010040b141e0801800302407030b400c0d00e510300340030000b8842d105120030002000400f064031004109807401103101c103900c03d1030708841444d01d440c025044440f148900302c1180b000780024569a0414040c1c2d9105907565805c403840c41c0d84030f940f04cca500b40064004c0d203c48100c581301240d00ba00400016008422540f141d54001704d80030b466400303a5000c0e4010f9280340303411080c000c0000e04450b8100e10500d0704002d11941452580c414513004100c0050040e100240d4501800107000310b60b40040d046aa200c074221013403580b104010360f65441561b600783c10300481418039241d500143d040790aa0940f00d5100f0300c0745180c1900c070103015a81c14080c190b500d50131146042140e03150501c80c2d1140c1c648800c005111030703200c9030a03a54445040018481e42050f0003d00041009030b40d034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214612095 1250 214610845 214610897
    0x13120201051c0509010e0703020a050402030a06210c05010c030c0201080411130e0610030201090e040203010908070b0a1407050d0e07081212150901140d06061d0105100e01 75
    0x10411101140d480c6800b5010f0300c0e0035101c640640d40780c2600c4240443d80420700c0016690042e200301c2c051440c000c1844000e6100a141100c0340c0c1c1e070b40c0d00104408000c032885000c200b0800c0e031000c1351000c06050081d0880500c0e44543d06016a01c659000001c0c2c2000505d40d0050302400d184d01c40f90f8903410503004180300000400e40c0411405862403040020340e006503401a0441e0031600c681d43c1c0d19944407694806030101901160790001d04020019064881a500c948003400118100c500341e41c9002640d044040d00301d0302800d40e001009800301040c807481001d407440300010249030a04440240640c0f003001070002249403149002c2c03045c20420090719009000c0c280880e0140a101c41e602c5a00b90843c1000c02134410352280812049140d84044400700c0d200103090300300740e900e41124804590642c40b011038008601c0c40820020078100d114803002000c0340781c2c504021005c0704502c50b4801c00b05802445c81200c0320300003200c02c00e5009120f0600c00d50b0a080425100e03a80c4402c504e0320010701 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214613345 1250 214612095 214612117
    0x12020d0f11040e0c03070c120c0506040602030105090a0c08130c050306090303010314010c02030417010b090c0a030605032a01050c030f13090209010c030516020306040f0b0c1312020105 81
    0x4420258100c8282400a02c03c54100c540c4041c071135121a0b1854640e4441a140c1d03100140d0b0700d40b109000b260030300050341c2146907103082610b042540340c0d403840d0801c04100c40545030240c0c0400100510300f4206070440d4401e03a58401048400c41315480a0301090010340916620255500064200300100d030010004e00710060844566151500b0500e65030b6000f40001c44000c640c8003060705074500140116140100540c019500702810005103407508540f00c0d00b420020340d20b44201240700c0d15110907081c0204611340c8203981d20050070300050f05071034481d03202071b0003540030000c034580c45070724403030300040009d10f0300110b041110b52040100c81d01c0c0184650030b0124000043c032400503a02090041000410b400728421029541d000d01e00124041c201c02d203808260140b0000002900c540300500408031422a5040b2011035a000f1070f00c3c1c03100c00c0b541160f585804e401d846060002004c50507900030011030055150408031202250020b00511990100c03c4106c40d81c030342107a0040b415642c840b030b41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214614595 1250 214613345 214613351
    0x100b04080303040615030302071802120a0902100c020604050f0102031b03030f0f01030b07030f0f06030302010b03070b0918041e0609020901050114120402120105010f0303090906030312020d0f 84
    0x840040d03640742d0b8810346040341c69914109007602c90300b507010201d0044a0301600038040d91450030000c0c4801810012aa01d2510b03802c11400349113a1600340030074000c1e07201050006070b041440c030502c00030004017031503481404551001000141d40b650103c50984e50241c490380440700540005034a1405032401c04582c0b010003025040d540d06000000d1481584010400192912a4460241c0080081c013014101c4030907040000d000c00e0090304406842490b20100040500401000e01e045038500d42003240143d4464100030b01503c2c3c1040810080c00070801d480cad19142c00480010b08501e041258074200710399483c0014140a24041d0f1140003c589000040d07000d40130707207000002070540100c224401d40103140041110b521940c06403090341c00640146e03141c10504141d5000041c0e0003002207034000a031000d00c031720500c0c0a0043c9402003e46660307280d549421b502d4050095a15504a00d1500f46488400c00200358044120544d5403540780b80103035565260138500c0060048800b40c000b07100e007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214615845 1250 214614595 214614599
    0x2040b180f0c071a061216031704050a05010c03021204120308070e0a06140702060c0c0108090c06070206030a020702100809010b0d050604020906010504030c0905011d0403080f100b04 80
    0x9120600c24070a14060041035816a00d05520621034000c03020081c1c8102000509503403020728114107607070402030060011650308200350000b49400d44282c500318121904070010002c204103003800344c0100710400c00d064102811315002c9140c00105114440c100003040400005060003440428101d011224982d9995a10b607080403c00e00a40c0000318000b8004100044003548075942e0390300d80d50720003015030307020740d1421204843d2230305854240710f00308904003c260016900c2c0e200402402007800301520091283c1c00003d002e40d8001403040e142c940004c40c41006565560b021941c0d891750413151140c90b5243ca000740c00082c020f002c0002e40140ca03142c4011246a081001540b04806c000000c0c03140d0207548040c000902a4580c000349140d10140100340146002c040407036000006140403030420b0341d2501d40000c2208150b102842e040d54510052100011041c03070450280d1030a055503007075041c1903400914000005210402189060002c0740c4a400320344002001010503070181c0e078842c0e0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214617095 1250 214615845 214615879
    0x31104022b0204140f15180402031302010e030f0a06020f0c0f0c0f0409050604060c05070b011d0f01060813110d0602030a0e0106030c09020f070b0c0702030f030906040b0702040b 78
    0x241c0a4081c01018100b40c00e04c200c041c2c0b400c601d080604020146c0074035054803004482d0391058104203904c0c01040302c903e030500110788451028506c03c00b406c030501d01c07070700d84580005422224412032080c001e03004844c0350702c3c8a42d0300154014009500080040c1d039001d40f0901c1c3c074000d000380842502640580042000003440001e100c1711b601e0740444851402000500400c4211107a0300401081a004000000c0200d20304d50702140d044651810513701d40384403595400340c010401d0b0003042c00c580c1c81c02c126240030003a1841407a444102c841071003603a541040c00140800d40018101150500300064a004000a00110021004010b40000d03100d40040c6042d40194100b2030760721106901c0e02510940600c01400390000700d94200c400d2603215410190072501950003e222051581800c011038000a074520b040c0c54410054856100e4848440c0c1c8105400c041d1440d004e02c809034010b01842c6c02031360302d0800b12001c8600c1000502d030f4558803803010070060000c0c12160b5901c010003065041d007003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214618345 1250 214617095 214617097
    0x60307051f02010c081b0d02040e010e040b010605070c0e090703050f0c010e180f0a0b03120910030c090b09030709020c07180204030c050d210f0e0a031104022b02 71
    0x400e0860b0024402000c0b48041101c1c0800100c0c0c103801d0007050341202c0280340f94500010460365803d44030244c941502c44643c040140000e80c061fa002503404010402445090140180504100d203003c5140c40826100e0720001e18803806552014902140459900e810800c0103070300a503407040c00d035070b00a01c00305105a12a5008075807640415a80144903000303241147c8009181075845000010680320280c1b008200398004240c4c09216940b400200c0e000e590410070001c044002494007030ba81c8003107900307000800c1961545102414140b9005030812034211107107905980f00740c1c92003500c41c041000043e150100941c01004c1803440041c0340c0c0a010004222071043d40c82c044003040841307100d5012003003240300e2440f0103070080701c5602d81481640742281c00d04450794010070540e80d101c40d0902101c44503000318005c90021658a140e030707540803500040b1142d494242182c608000601e99151034800211158034584150341c0007038125202c00300303545011001d00344542250940d9844c607260b0300003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214619595 1250 214618345 214618399
    0x2040503010e1615020f0f07090605060711060a0302090a030f05060c0c0706050306060d020a0c110f0d110105130308030723180609041404060b0102010e1506030705 72
    0x1e508180c00e40c0c20079000000c07031909200d0500001c1a40c10302d89100709101041a0b464081107008855500c60040810403140406041480207040840e01d040c4c2c0b40d0044840d19803040b03009040c188401c2003c074443c100d4201e02e08000b41c818035511100c01c0012402842107542c880e900c03550000011091160001101680b603205508848081c3c0b1400350b100c101703000d09503c0f0f0b5182d90114106101c0248100b01450700200090145400c02e01242d009405a0304141e040200080200003640c0c1482015280d070b980c4890151042100700d81c20740081800a00c601002034190644000c0404085c0d2042040741c070340c1000152454445901c80c90004443c0d4819240f81001884003044540501e002c020342c04201004510360910340485140507024407110b80303850a6024009100d008150344690284d1040c03032403042c8800d01030703282502e0010100c44900e4951411a0300d0310000462444002440e859a00b00030944a80a03a031403100091512109801c0b10382c1100700d0b00182220b400d05980700c910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214620845 1250 214619595 214619599
    0xe010203090601050603061c020f18060103061410140d0504030807080a05011409061504120c0803040b03130c031509051b0604090f0f020c151e0a0b0607020310020405 73
    0x407260b60307141c4c108180d80c00107848403540000082d070030340c5042c10900240d544e0b00c0e20240c00d445440b0354110001351880301001d0318032404200c850401805682c58400c10015141000e41c001e418080d541c0030904643c00c000c01c04041c4071010014400c001e02107020303207101500780d0f07409212071b20706440c002341880015214240811006004168001d105010b0181a120130308401420b51252000700501c80d9070141c0320540040c495846100041003000007032002d0002c8444000d031122945c42d1901e00e054103588010103d800c240b005001d84c0603070b60102d1381c208486207404403508102e4107007030104550aa100070f09041120203000304503d01d58000c00c4940b40140241e03284032820842044000100301002640711030104414018610142e2007801b804454403400124580c68212200407a80079910b624095404210040503140c0c11586041d0302807442c0820b821070a400c1131000e64001d41c080c0c01c01080c0d58660031842c0b0f035501c4141c00c1c1c49885800904844074100c1481800e0000d500500440d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214622095 1250 214620845 214620853
    0x90c030b13111e0405090f0c010216050f03120307020706080a020901020703021002030d0e03130f0b07061d01090c05030d09060e0f12060412020d030c020d08040302100e01020309 78
    0x907031039581d800401c2241034000d10218042c00c038510400c529a85203102205410401c030540d00700d56112071144030300c00c5520f2001094007483c20f03c0128603007442d400311541150701604000011000a0362220100c4905030b600090071101400041d0602c144d452201400ba2400300821900560000b200011903070640c68110290702d42c001c40f0f2059219203030245001d64882032041005081072444941002c01601c10341c0d003000d40c0040c0e0f00303040d00c540100511003540080b840c1d5007207c8059030b4510081103841008075002c0e142c8040311002c6c0c05400d0b07011307007010781c0c27070201c030701c0a101d503442d00014103a01800800c800d07410f40c540303e010780d10b0038002c0314000e00c5290380e00a82140144201000c1d596991900100d1032110005c0040101004000d907800010083d9081d11240040010306e010b030703101310300c414200b110080d0002d10300030b070f1122403004060410701c10003400c0d40c01140e60b08900b500744c900207241e6035031030500b03a251004202601c40600c1c6083c8203500b00070410350103180101103020580b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214623345 1250 214622095 214622101
    0xa0b06090603040b0718030f021905090714120108010e0c01030b0d0602090f04020403080c0609160312031113030611041a0d1107030c0201030e0d080a0b030307020301090c030b 77
    0x120509014103000c0e550403010400224011030508440180d0107140791600a840d4881030440507003428165008032442c5d94028041011860071360550600b0440c00030912606528240008008510180c260be062103c400300001c0703403031188812520180224030700481c040d42c3d280c0d0101c0c000c010321001c13500c56000761721191a807984a07000d04151000d00510003490b80e1500e456080080d840281c09035404078041000d4030f40b945407400500021402101200e80740e8021488241c2012002000444c07141c21110441c20510041c00c0b07a0001d994102c8048044070440c2d02094000b0040482c95103038040300400c102200180c950864004d03244915810301090320703046400c00240c042c5000c0c846d038188600c038440004040d00e80180c020b05510160100f8164850005000030713a02c03120040d40080c0030141c2c070000f90758142c0102c4001c800300340020140d42d40e9851000b400c660b005000c4001c40c507218000b00413640d40400517281c4540d0028020230001101d440c020034107000324401100c2c105500704c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214624595 1250 214623345 214623349
    0xb0d0309080f0105070806010e0d150504031b02010203040e0c0d05010f231003020a09030c14090c071502160507091d0a110d0204090b0a0c021b130504050a0206120a0b 73
    0x9102e01451751500d46260940780c070401501c01000103000705811045820102010036a000128010865150000103c0341031900740101a0309104448030103c0c04040103020040c0d03400000c07202101c8442a401e1b150340c40c0c000c002895403040c02400c0c0c4409050030008a841d8054100e03000448000b040700b0150044600d40036841030300c8143e0f14607444500d00c0d941c10f00b6140250014041100c0a1034040d14840c2c41766201640c5074081d421160b0f0f03110601101900b9810646031003600290310480550900400b0750301c0b101009240741008030300c0381e0089404440383c6014100490b48a9100c02914044c0d521611003100030540e0b4289120b0422104051030059040800c049409a4020005038581400d01043c4040404180c0080b030f0869500c1994001182d00414000c1c0980915800815108440c1e50001d1800060031181c0641c00441807800c040c1c1c0d52240303c132a1400959100115440c5d035681040d40c1440c055030750294000c5e50000e111000c280c24440254426615440704012004070641 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214625845 1250 214624595 214624601
    0x30102070605190c080f090a080a0206060a050406080d0e03100e030706201e041502031b011505190918031b0f03080603120f0408120f03040f03030b0d0309080f01 71
    0x8030304d10115440c080460b400780a244541070740020341c60200c6401001c1643d0f03c0400d940034404900058018105021311443c2004684008020031901880034038103212009407201e030400c1c610810311415098010b425201841301d8421118404010420310880d500040d40701d500c44203044824034a03000b82d010b1804260100c02c0c1d820500c5e9144c00d414000c100c030f8012034000c18030071901d003003141c2407100042c020b00c2d4048800140c45150302954039040440c0e081c254004101e0310048140c0d052000304d00182c013682030800201c074411142e03842c22402d00d00c52030b044401241c011003d13050805280b2520a024200d850340e0140c0b0035a100d40403d80001c06c09070800c00340c000300904074240314a061002c41d205000c801d41010000f429540c044000c81105070043d400900762042030440803400300b00004041c00300070001d0b8202071100e40b802e0008520a14284002031008041d241d0b8603c0035000c2c075101e94040c0320b5489001d020f00410082d0b505000c2c00504462103109070520421071200d45000c8180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214627095 1250 214625845 214625861
    0xb190e0601150f02030c061501081e06060f0909040812070503130f050c030d02010e0c030105130b0702120418050603030c0d0e030c0301020304150608030703020a0f080903010207060519 81
    0x500141c003280c1c50040212424154031407603c045200502072616a0320050014a01400700c02010b0780b8602e0700500090443c05009140c04c0820b5213052158402c0b03048410350503030000084940c01c1d03840c2404d5a05c1e41c91405446a07054104100034104010000040002c00821030000815000ca640380401156103110442e2003c0480710505080300c00144890040c0b5070940c86401a200c8100501d400b2a2518140f000c071140140e449000da95001081030000001c40ca80c1500203118078502a42c14590360040840020410181d8000040c2194820300894901e9841d02c280250703155a0303619420752006030001d51580c20362034100820914600002141e031200c45a00107400800214a02a42c00346036220748140c00d8028684e0801d06035800303100441c0b00e18070030900e100c04041d40007000b00884149800400b0a60700402c981008603170001200c5041543c03000400d0364188080c44d0200e080e0048210194066002040c064208510b43c1c10880c840c0034864649101c120502140e2000d8075501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214628345 1250 214627095 214627109
    0x1b0705030901030b04020d1a09070e01141b06150307090911100306080a202713170705010f060b070201110c09010e01060f0c03050a0c03020a0b190e0601 67
    0xc000c501d0065000b5088410780e094028001410900350110300000d50701c8022650700c034000c5da241800c1d1301d4a001d00d00c940d041400d0b89016030b07503c400b403130010300500304030700034030014240209070300c041441749011980002c40c42074141c0e142414490420041e42c9400c0c0846482070140c05000b003600340d024030400c1c20b203680241d400c4583d60119400d000000c14032400c00003c06458010100d80c10f0810081000014030545c030078400d0b01003c908484100c419080e13070520401d541e98100065800d00d06087c12562464120790300a5115403a80628100c15010001e10040c46027007444441d840c0c1ca0007038070115010700000d01c2030401906481c022550f0601a08400d070406005540c05544200300a0f070300102460100c0d01142400340020b290003c09a000c0800400e6480052000302e80c0000c00380004242c034184514407030301a81d0003411038000c0d01030900800030a80c1042e400d041c820020070000d6038000140b060030341806506540c40400b01c4001041090400b450303641e52200002c3d00030304075211 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214629595 1250 214628345 214628347
    0x15060225060e150310030c0504111210030c17010506030718110d05040b090f0109050304093309060f0b032a0d060e0601082802070503121b070503 64
    0xa100742a224080c0030700c090b0760050400364090030b40c52030300310003103026a034a00940c500181c81c40c44c206d407038003102d504100c0c02181854010038085040e0010394102141c0c07082d403100b00381d4910a6141121029900140c00d042010740001900c1620b02c3c0b4449854581d00000e005980d100028196240d000b403044044081c0340c4203000c0203400a680c04078200c80090f0094600d03009030110b04800b40d80083d2401e8501c40c0c0c0c550180601d827082001060134000700c0900900400c2050303143d160702d0b80918454030300b015071104291030703c28100f0800d0004400500b01d072404102c0c1581002c40c07880c103690064603103003468650046030200004121004072100c0d104007614603520310311508030b55480351814852802551200307a250441401c054203071148a51400900c0c0c520b0800d0000c6c8002d40500910b042c81808018441d1161440d0020703d0104242004155410300c00c0350850001d109040e0f02a00380d02001c038101000a2140300050701814109001d142c0300c1840303110f059402d208403800246680c0c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214630845 1250 214629595 214629599
    0xb100309170a02030d052401021501030b0a0603020603040f060b30030f0d1e0506100309110a0e010f1a18030307060603030503060a0b040f05040b03070915060225 71
    0x401c000145030109140c4143c03420004402c126000f558401e8030581e140d80d6010300c0c070a000040d20300c20040c0700d1100340f0041a20b0791010318090f182650601026041d003500310b0009144c0000c43d04400005e40d8041c080c503a80b4603103820314180568040404882090901004500e41e20b45101c0325581240b422000d111580484006040410f4180d421108a408144082003505060300701500a4100480c8082052a04040c00d030008c890304111a280640c81e11060085945a5500d0756a8000a40c1400181c1c3c140b035040040350a400003941c203074080005003022681010901c10300d412551150941901c3d9a164111500290303040241c105000f0000c0c410b00b003d814103400540c541c0d03807000d400d5a10303094445c0c9840d0f0070f0700e03640e42040d404507034004103000c8dc41c2402841c01d8000c09250305214101428601036008541c0b0505c6000d10644c4c4444030f81c05551307070a10407540100a1100300304582040340079a01c42e00603c0d03110b802d016010f12b40c60b4149134941454000003100910741ca801d14a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214632095 1250 214630845 214630883
    0x507061d0607050106031a04050607180608070909020f04050307090207020306060d11030328090b032e14011701080718021902071403030f070803060d0b0a0b100309 72
    0x34002c0d00007a07942d5920390300000301141030481a191448194183c103900d42c81d1070f0804a02e00800034001c8002c000c9000341d450100d10149101509681003850031900310703280e805044901d4152608010401d902c00a003a96854445400a00c11140c090b800e6900507503603065850308178060440065095006200095074030324210b41e65042040c03040c201540d446040c980860b146410125004079a8006900c100782400008506000c0c5070441d4540048201c0c01c050320303c0010700015040c0b032034482440005410380442100d5400c0700c00101e0b10000029075a41074107e0340d21112120445c045100920400600d00c407166406058406860080c8000d528140c1055105d940107841250b44070742c01d00080c03840011303400e10280203000c9540101012402c11402510780711078440301ca4842c0d031082000003800c22180041e680487c0d0407600c1c01e62a80d80b1600450200701666100034403401402c410005070290303c3c0e000e084041030640c2c500242e96003803003003581151482403020b80706180f0401c3c1c2034050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214633345 1250 214632095 214632097
    0x2030a240812071e14010f1a0d12080601022401052e08040201050c0a060b09160207090c020f060901050708150609041a21060c09010c1203061a03040507061d06 70
    0x140710b00c000280c00217000c0c0705682110f000244004515490b0312888003226401e40c0c0c118540c1070215541c00f0b203000c1d42c2c1c0c0c50100002d59607242d1401e00c5940c0c0b0005d590350b802130011130700c10a0b080285844c680c54150409900b0b039402d01130144181411030b10304a60050307884643c1045a4a101c100e0404414090155488817000f082241041000c1014607440c4205020a0540e02d101d8000402e0401c040da040240d8000c000b041d5040101140c1c50074501246c0c002101d01c1181c400302800525100c0c2420101c0c180041a00001c00c14072a250a001501d0415400184031349003079510701070030b6120b04540a40000b041d481150380a001405140030030301d840da00c54142208000c02c0f260300c280107403010a002c0351000896044080c0b80900382c200c04a8144a0107500c0148101c2d09486c10200d0000a4491426903c2c041c01c00fa540711500c40509020b90700100c0900000b11f1120107480442d00403001035801160700319028000c0b6500000d906004100d520305804000350700f0070941000d41b00348109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214634595 1250 214633345 214633403
    0x403021b04020904020c1006050f0310150e0106091a09060415030621060506090103050d0c08121003020f10021f091202010e07060c02010206010902030a24081207 71
    0x101c503908201d0310481e56181e20060643c240d200c005010000050b038802812500c890340954014080c02040e0611030341d000ca860f0500c501101800605841c00e06486510a25160400740d410041c8c64000b00c0c5a941148d2894101c1d00c84426036004480034500a0320305000d1400743c1604040140b00c103001c1541d10b070802141c41034a07840c000a107030b55984990151a50702a4150240305034951200f02801072500446602020039154013070315515503520580d9811744980d5401c1002660011001002098011240d521400c28100c40b6070f410414143d11030700c50b561104a20444031401064210306200481b1906540660003404802c4011560702c00102410702503604c000340d407028010f0009110294030081c4c169958000900c0030400402c0c14038010740d030303005401400106040c460050783c2c002031113415500300444c056126110710541402410b40e0154003004c4e400031043c010203000490341d1040131541c80c0400c5402c0c0d90240c48040c481d602c1044006000010492034407150403000b200d022007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214635845 1250 214634595 214634599
    0xb01060f1d1201090305030717010302090606210717060d0b01140310091a0c030907030f06060e070206040605150d17071e0507051f0c1119090f050403021b 68
    0x114082c0088640e402c4440b1402c04038040f400100500c01d590b68002656180c20404440c204003550442d000901105001440c05206440001da0200300032001028645141e02421000b40c0a042000010300706c0544141010342504403800002c0c61450200e80f0420101d40202c0c0688803a400c0c9044440002c0010f00c843d509403107041c0042000800341c3c80740200781800b9020701c1c6d004070001c03003030045030500c058001002203409000788540d482021030614200ea50003011104034030325518000025250b20f611001800200c0740403c45415001301c0c03000c2c490340c41403a0412250b0f0700c041c1e02c1500d60382511440c80c1c004403005c407040300107424040c50b00800c3d03450045203070030702002fa0381d44900c40d080c04004124502c01140300c10200202041403901406048885c0c1590389801e6103500f0881e03042240d41401c00c48909990010300c294185255a4180058145030f00340201c1c80ca0042c105900d03200360703580a80750201d0b4407086520703441024082c81d81030303000d000e000348480782d804880b4608c040802e07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214637095 1250 214635845 214635859
    0xf0f090201080a05061914090601020a03050a0f0e04090501020c0c120d0c021201060821030606071104090c141215040f0c08070f06021b09011703070b040f0b01060f1d 73
    0x1013030311031008159400400c1c0c20b1f9101c03990760780150280072000b400a0400c50543d03100015101c0000d80040c25075440364030030324003045070701c0040c8401c0b21200c24407950660000d180c81a003005110042d0000d01d03000c1c0780784040320444000c003803d001c408402d100c0005195007005a05140f4188a00700034080d03075000401d240c8808441506803401c5800c254803028040d48480302900c0301484e404800c80c05400c084c0341e540d08616291010902c188907641c0014a49464141c00d40781d1070303035070758048801c007070708100045039050325100ca15828000308032440b8440d51002c025070302010000155250f0070210101100e069407682c0c2e4480c4856100624201e8000c41c0c508000b080e845001c00c1403000030690482c0c008021868440d0290820611040c84142000c6050004d100d079103545c3c0e10346044803a00c450300151169821a024250b0040c1c1d41c005002c14101030030f0105208844180c40002d40c00740d0104165641e82d4641510040148414240405c0d03901e00415a0040212041104600080c2c609 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214638345 1250 214637095 214637119
    0x1003090203010c02070302090c0a02060c0705010e010501080601090e1b010e030304091104151107050f0301140a06031205040e0403080402010c1e060507030e10020a0309080408010f0f090201080a0506 87
    0x60b00352110038821000503484440d041040d4a03000c0d0420b50000100f80b24a440c1c813141c994000d4699400404400c1c402400283c031038104002588034244404d07000000f041030356150141c0680b14030003031140460440c11b092050507140c1c00403545030903e60950704509603024020005407100d1003401c02d01940740c041404006500d58990003038071450f580070198580d8035401c1419140013101001d00c10400c01c105480c800f0000d1034001a84400d03114111561000b15810300002030140005540d4514003040c8103040c00310050315a08064260781c0304102078007001451031400c59660245200f182c1c050003a46001c980032a0258692642207030042c90f00c580116400c0e00c41c480107103452411027046042e6821000c0600030103108464005e0118581400410380b045c41e200c2c0c1e41d00d141700021000c00d600250300d418190180d03101d0784107070380d000340d0464840d66a406528020b102c0540050240760904a420300e05041c10b02c02d0200790f540c161201a516161107003943c0040000a207055004841840e903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214639595 1250 214638345 214638349
    0x6141903080c0c1e10111e0703020f010305040b0f0c1b031c050606041a0c070b0a091a030412090515090a050303030106090308031506040905091b06040510030902 71
    0x3012140c0d0b0342d030003c00701e040002040c1301d0359203400604032440d106031380640f4070103680c0c8492000502089203480744400011105890802c0c180a0860603000c0d000c640c2660154030206030365003201d000711041c410507407902005406444040304c1c002c21488030800000c6091103c954943d4110340301c0e030089428908204c549440807888900014550f50011130729036a00d00740442804007201510310113100900b44000414114091405900f07002204141c0c82a041110304080e01da2500c040000c840b180359031440a03000d00c1d402804204009142d0f000c0120745030051785210f49140000b4800c2d50b155540f5519000480a080880c0800304846250700240701d96a58420804003c0c0b2002d034150b44010240802c0752030801f50340318034002d810238401000000d030480c00940c101d0b504a0141c564039034400344205c1200f11031005c56a4041c4020502207001080e980c800c0b80310f40307a0f04040382c0da1844005000c0d450030345512402d40d07100c001003009009030b0614002e045e240c15464180811110007980c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 214640845 1250 214639595 214639597
    0x8130311040506040c022e0c232b020c0703061b020f0a2d0602040303080a09020a090b012003030618041505040c08012901030614190308 60
    0x801914400085214204246000d104103504207104450400881003200d02c0a5240c0c1d801c410040030039410045c115800e049041c1280c80e0240000e40c00f00004111360f036019080c0460302144282850107c9060305540d034514040702d4000751602209045840b000e20841c4006004012100529400723103c507400c4034404124240103140309190100b02960341d1b610129554100c010b08804551103038130000001c000c041040e1540d190021040745000c0d144010070a004109441d0300c00781e07961607000c04814030a40c0c0d07000d0801d4a01c0f0381d40380003013504c0c2c813203449041c0e80c50700ea8041e40c070002d4007504026911007940050740e000410b042c080421548400840c900542da0342041d900e0760000820400b0b2840c00c000003450301c40c02040300780e400d410551948083c513104440210281da5980300800c0034041d0b040081002403100d44024020801e04d2501110903807240c0c0040e40840c0701c4031070300580c0e03903010b401400c0554109003500d01c0c1c1d95840700f08026403211000303400c059007030710248080003240c2264 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 214642095 1250 214640845 214640849
    0x12070525031a150307030309050402071103030c060403030605040e0303060405040c051302040326031305010f0203190b120318040b04020a09080d050702180405011407030b090603060906010b03040813 87
    0x1010311400d403404075440c0040290070b1035842d2181e0040d45d0b0901c0081d0b040642e0f801038440a68005885516614005440040c808800c5615100200768010b401c40300080c1240700d64820380d024402a0f80d40e005001c203a0380a4030205115400c244000340c654141030340003541c401d001c2c02009030340e0740c0c0e2800420401c040201c021940d96030000360a00a010355a9005102031043e40c0da44101641e105400a04030700000d80040b0400c50201400401d005003500010341604005104540d2402c1074507000e03201030a03500c1c1c0c0f070b605142001168a01031134040425903440c26100055071038070001e041e10103182c41c454000580d016903a03100243e41c0307448610240070300d2411078543c040004d0415003003034540038940544108110b401c01c08540141c070390204a0040d22888421400b0a85031850000c1c050a2070000301c1c0c512401c1c20081001c56507041c0c100130b205c0c2c0d8055410400e6a11544181a1038800844080500d980840e00400086100200840d4424016010141001c01007502102082816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 214643345 1250 214642095 214642133
    0x6010e010c0b130b090706080c0f04031208090d0207080309100c1401020a120c0c0201050a020102091305150d0b0103022404030305030105090a0b0d120306030807050d021207052503 79
    0x1250300305040161350b444440d002a001c1000703020952401d08020103100c1c0041844080300004110560710701a902c040d0307405143c0c46030300480a20000000105448000c84818200384a2214110403c07800881d0030000d0301c0c00e107000f0b10710f4120300c2414414401500140e010400410030840c4000c2800140c2511502c5441310025aa440c2d2081004120689050140034201c1c0b8003c850b02c001d0380c1042172301c082c4550a0a20503114041d461b8164024003400000d1034101c0210b840c44089000558031a5200310300e03403441031807203a40b140300b0301014005160700205107018007401840586051307906000c18102d04040005c050320409019001c0b50020703401100801d00110040c041d40c908074524135800340040004000c0d030b04a5400289016100b29400b0303040340d440c4e4212040c21840b84c0c1003040038640006810b03a07184207600e000c2c2d9491a4111003c0010f01880d5042c40680809008884517640c0000041a41348c0940c8005042964029a1400240000c1c0d00c00000212004003100f400455 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 214644595 1250 214643345 214643371
    0x103020f0904020d1406193f03091203120906090f0f0209060607150e07080f0f010b0f0a030303020c030d0c0c0b09030a05040b0306060d1e0b0303040b0306010e010c0b 73
    0xa20003040445c56014250754441d40d80515a2000200c80b590018100d82a000000420400c0401405892860600d0710600c80c6100e0500301c0040e02807268841c449842135480c000e1b441d80d6402c5480031041031000080024100d0040803103e00101d4000303915640c01403c4c0061074084541e110041c205030003d0449910310250004819407814090306903004500340c44952a0442a64840c00c44034003903032184860301d40d5622260100902002100080d1120100305c030601c0648840c4965240b480c207402100c15801c02100c0010750a1060312501d00349400f40c24818000d01316034003070307010307411025411040e072106008200740041140600a4440c0140d207540c0a8000f41e0b06040e030034400c00a0981110f54010400c0d0240359038400c0443d0200c459405141d51030351181d000041d02072060513001c081c918102140403403810783c00f01380e82501c0c503000b81080003101d4070f91041c1520f900440c404d01c501e41406200140f51540500c1e1650304880c41494200460400f5a0710384180d51010b903000710301212 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 214645845 1250 214644595 214644611
    0x304030b0415050127090b07050c011104080c100513030b090f01110313020303040f0801020322020a05060a05130b03070f050c071a040801021210090b0a050103020f0904020d 76
    0x142500e1402d12030300c6848401c0c8101c1d8140003070791580c0c0c440d81c90345007001703110318850b003a0b035a110394003034003110341d0001c885401c90503c0b110003042504844910801035180c945800034149580084404540241d0058200380c8000070400202007081d00010041c041d0030800e0006492082c6040400755110700c0100c50a41417011902d494100c0000d1a04401c0c1c1c5480d41704003480800900362a801502d8007a00b0a0134000752000c2411801540d102e05400358000c0c1020914050640107140b05554441e00c000071424000c054540b250300700c00d8080d40012444a0a028908100004140f142064140310f45041d180752001c0b040341c2d03410f51102c88035000200034040d5950b4405480c4480740342502d40f4500301184000002e4a0b00f54a10482d0b00e01c0074181c0e0604080d550b039a0a940080c0074000085481c2c903908040b01003d03e00071034814000001c16000840d691906c1e11603403d2000019008014243c20000150025406040c5030b1151a40c20301503824180d03242e00050039081308061010843c01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 214647095 1250 214645845 214645853
    0x80703080703090b06040b180a0515030a030c03050d111204020301111206091b0a030501081905030d0f0b060c0a061409060403050a030212090d02060f07050912010e0304030b04 77
    0x304000d440c8000301820421500045100d202c10a174019808031800500704085500154034610311515070b0107000c5896040200e8091680c0c071441c890000000902c1000b202c5104040d100c9111200040120b040f0200c2040424030030341c013610781002c0310031700040c0c0a60b02d81080300c40d5800101c1d60b1010380402c5800c01c011404e081c00b51280f10000e0605142c20950782c48016a141c400c01858180160f0f80000015001160080404003d64450702615507684c3e2242c4014041d020034040c0c813480d4451a6401d036100ca4071014680310058001d8003075400d0554800c08600507010021090052036200d030104006c0f82e46403801460140c07507090017410b8220142c40e24409603111812074850318680c4804000c42c990012510a501540c1494050350b00c06101c0804d070028015440078804000800c4201f100c0500700180d01c1189042c150211041561402d400e80d09200f0b048425000190003070201c0030380350400c003d403007001840007800072890020640e6003501d9034202e0361007900e0307420031482448148 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 214648345 1250 214647095 214647107
    0xe09040f030201110319020d0605120307061b1e0905030f010e0106150801031704030506040804051e0a052101110403030f020606090613090c06020309120115090903090b0403080703 79
    0x50b9020244d031400d40c40c0040f00f07840c48814107840b0003a12500000c108807010030580c041409408000c00c06024840c51900300f039680d80086004954061425000e07d5480038520031601000c90141c5e6020784403007481170220105100007031a0814059070307031400b00d01b90b80e050001c202c07080c040d0743c0001414451140410b003500c116a02285c02c0c1c40c081e0a40c80d003910750000e07000c0d06407900940c2007280d1078040014a9881c1c4200e0380050043e019110a1004004003a40108112003086501014181c1c030413140b00c03802000702821300c3c0d0203028201c08111504013270b82452400004203030321041d48a2901505402d4480180f000a0f0422001805004042d0002036182004281d0f2005214514100780400c1d44a50080e04080c4584104060b18035040c04940100c04c20544c040c0c1303c14019581d482020355aa000140c1003889015807850074400b0b048140b0801180840c840702d40b0102c0703454080030074001c041255042c2c00704a620000820030a646500500040d80700f0b0400661b28041803c0040074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 214649595 1250 214648345 214648361
    0x14011407170609151302040602101116110105090d050d090f0602060105090a0f0c0e0f1203070605150306010e061306060e013e07060e09040605070e09040f030201 71
    0x150030380400a00c9026207440d02c0456000031318030294010400c00c000020207590141c811260303486d00000f000305049a01055454400c06121000d01c40541146075214040c001c0340c6200c61030606506055000c40c3c054204c400303228106040c064a03140c0b0340c2c004603000f8405600f050f28180e00131b0000041040d80224000000d1030a400035416880c1440c000a40746c01041c401d80348a0302219022410045d1161310144400d03840d01c008100321a1a001c0203002144602c1d1014800c0c40c0e081002101414007852800782146010091890b1034050740d24580201005400000304035441c0d1040700b5a40c9081005d00c0c041d000c860499110361400404221058013646034500d91641085001c101c3d82d6040788035071601e06401d0900780340964401d599140f560040e44044440c16001c1016020941e00e03250000742c171510100250f400f01920b80c0c509a0b650b030510000540c011461000044c0421560b0b03100c1c41c0c1090f05860002c04130704031100003031308000c0d06517019a401e00302030310038501301902481031100d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 214650845 1250 214649595 214649627
    0xd020a210e010612050a2a0b18030d0503041407121b0b041d150a0602060405010b0a06090608060d0602031302040e0102070305040e0901060306050705180108040b160e060406022a060304080714011407 87
    0x14800c005081d005205001c080d00080c03101a2100c0d001400840600010010340b009103030811d510b0105080042400781d00300348204c990200d00704080382511410048a0688000c00d016042c031810740740c614040050700411450145415401d40c0031142e442c203603200002e010b0f660040c803060800d41409401c44031030b0100c0310f107d2012501c1c01c00c2040d41103484c0d42c04440301810a0f015554554010480100c088040181f01c144000100001030300d49145418440b4000c0e5401c2096404405215080748100034025021400a1100300718008c003070148940e02001072400400c8035592036640b10103540c1d069580c00085003000c82d490700d55201c0b174000054440c5003483e207042a41001d4440100c000d1011380009400010700a140e00700c60b00034032149140020242c0101e5441d40e403810b0081d00c83c05280340e03002d550062a030030940c211200300140545c803100140007500d980c4642c0e81d240d0319a800840304980200d102d60310080500428442d440c0c003051100c0b2214a41d16000c00b000705a1428019014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 214652095 1250 214650845 214650853
    0x1060807031407110102070f1b0501020a11040c0507150207031106061302030c0c0601080f010c182102090f0f0108070b0d020a210e010612050a2a0b1803 67
    0x2034141d82c2d000340c04640084503814095a044849003c0038007a1103203075006445103000358400380801c0b044504260011980450384125561070340300482e200d00d0a0703000541100d01c0d0212071421407519900000c2303114141c0c28a2403400d8010f691350b058050305078a09400c8180d01144540038150404051413881c0003400c054a484d04d0b01c20002441d9040010350030720307a1940480090011549803013101d0007030a02000302d6440d50b0b5159075065813081d01a610502139400d0401e0814840d006888a4681c3c40145045010113820b041d0903400786849400b50b01c0010410610040c050f0f1a1402424000c0100d42d540d01000d18140096000d000810b92007144503a00030402001015242c030240d6542d850040740250340c401c0b850100310380d9201e4110081040112000d8240b6000040713a0041e800101444020b0180c140d44020304492100943e030040d0190b000941401d001400b03041c0f02040c1c680d124507100c4282803140e4104803004e415a00030b4480d101c1e000440c5084040c4424401c0301e000c808034028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 214653345 1250 214652095 214652111
    0x220b0702030301092d05060f04020408062418060103090b01140a0609050d1b030b130c0e0c03070c0c08030301140108090a0f080f0702030102070602070b070f020d050901050403020a0e0106080703 85
    0x405d01e10b40f0810b02c00400300d95180042900f0780d4604601c0c2200c008000d00640d20b541e120040c49494000507110890411492a107481001c0c84510743c0c051a1b510007052508403280d119482001144001d00030b50403d07036514081ca00142c41d010301320703003e00749402040964042c0390060040040c2c0680040701400782c0d846c010006035980a521605c42c82d44950517481c2040c9e03003542014801480e8100030091501001000070001c4200d200c0d4040501900184044641e0f45c1900120787d10f05a40840300404c3c200300007000c9034050704104a000d841440f401e0651951120450f0640d0000c2e040450b448040f009071041569101d0f2469405c045d41c0f60180044000960710044a010142c00c0102031034400f1489850540001081d00c9250760050020740d0388030401d15203403009511208007220b2070500240851034040c41604030702e4605c18035130001d0680e40c0120106031025003140f109241041010480400140c450801400007441ba0421200d6a541050070140160320700808000416140a41c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 214654595 1250 214653345 214653401
    0xa03030306080d08160c060908180a0b03101419060e01031d030a0c0804030c030309030614090606040e2107060c0f120b01092c01090e06220b070203030109 68
    0x10100c0c503440709040031086c200003031500d07070302528000303002034120302c80031640750055a44094071260414088400210032600d844403420700d40015a0880b1000c2c408200c00d101e4505201242003610718001c1000c03100d112201d030606402c1c08140c200600080e4424414222960075000700c0ca820804002d0700c08240c4065084c0d181c2e01c4c003238699158100035020b40c42005210309841158061508030040601040d04c1f42130240400300e442c402120b5091900b6504403030480507810b1280a4585100902038540700c10080102401c41300140d540f007401281c01c131182c0c0c680e400e20321380001d02510010076101c6590b410641c04a4140c4522107081c030003007a8030f480c01e5583c811404010b81c03001c2d0500280800301000121540c000a801001c2c031501c60250002c240061070140c0302c01c1c101e05e195140750781d030380b50744410054071100102901d181d842940840c0989070240700212a0907a020400c1107008a1a1680c541240054a6440243e04000014003d180759070007403480c1c0c00d808224051382140a402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 214655845 1250 214654595 214654621
    0xf071a24010f14210a020a0e04090327260601050906060304140c040606050d150f09020c01111317030304320304090b01080109060b09010c110a03030306080d08 70
    0x83e441d2000385000841141403005082c218401caa0384141d0740000303141c4050404020350110312044c011490b005100e8085140134010381c0d55060380740e625089040c0c00a84c80c60040c0c4282400e1203041d46481d50b0120b508203501700300791488a040100b901e20403040311541410304074181c104900804121041020707a80b44c940407240c1243d8400580e608640040d42d8017407d00c0300d8180d00a40c0b082c1000c00000c2c0c3c0035400030240404260303802e010807195080fa6a1089040130398803134201a07400115003045404e00c03e50152000c0d8284400220b6240c0c80c2c40c0d80c2ea80c10344d1110182c915001da9849013400808030720001c0c0620055040015455410a5150303459044e00100070b1815400c0c0200d040410780c001744400140f80c204c52801c69888a490742400340142198604050005d4074000c00041c42c54841e006a1007110401000103180a0b5070000445161001e5074003550b0a07c51000e001406460705080c400c000d500941c0e000443c107041a00250408400c003140004000030001800b5407090072035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 214657095 1250 214655845 214655867
    0x19081c081005030d0804050c0301050f0a2d020702010903150204080601080a03020a0f020f0d0501050702210d020901170109150801090302060604051f2301090b0f071a24010f 76
    0x20810071165640e0346805071510b8400380c0c239070750035500706000c0c030007815000720401d8002c120424082c05400282580c6a004203444070320f4080d40d18600809807a4140d4550080c520a801850180c03c102c6d2217443c0e84641407220f5485106865002404016005062003024058400300003c0c04400c055528001d54403d0405c1001e06111090541306003103541d0840e9001d40f10700064031b0b030314031101941082c50080500301d0351a800340c01015084202e401e03294605d22116201e804c1842e00b00110905000000d41180315144c7c14464807800c0d103060580c941c2d841a00034003032503d01143d0003418003888840380340c4d80c0c1e216403196030610203640c000a0300420f035541c2c040b0040d035001415944044030b044140d09149103c0e14032012145001c01d005540721444c044d45106041240c01c0d04054100445011a1031310451159280600148a286034030303600808640340196807010048403c0e209070360042d00140c5000e4180c5504403030030590510100842c03020041c007403c00c08404041401c0103080c003240d01d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 214658345 1250 214657095 214657097
    0x2604031e141b01030522051005060a06120203280e12070305090f03071211040c08010b0a0f0207181b050c07140612040f05060603030f0919081c081005030d 68
    0x207000060302800c81c0c06428401c01b0301a14030f054803241d0390400030348801c03020003056082e504003000070350a424440c1c0024210b400d030b95100303844124a130080900075013000c1c22460320100300d1030403003100c05600e030081141e206140743c00140d525420072a0b90f140c082402403017020b0903820302046d000b182d0403e00703884100c6019183d044000c90003100090a150468005401c0101c81380402000e010f80c0174822062203006503000c0015075210401500c031000c00b4400c010600000f0060826902e01c910031003810813120340101c0340125255519034604250075180c8541860b80c5080e81350b03121944680800595a40b81421498000c81030596a143c840b036000303100003464043c85940380da443e00340446807020190301001c855400c09107010307032504c0d2941e841542d261007030001180952030040200d0750790305224503e140c41d02483d0b1080c880600761140001210745442000042c03225010700c01e4034415002030010801d1512851380140000c1006880040c022480010510ac10344002a55801405203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 214659595 1250 214658345 214658351
    0x5010e0702071d0403120906050a020714030301050d23120d0507080c0a0309030c0b090d26070806030c03010c02010209030d03060806070509060714010501050414042604031e141b0103 80
    0x80140d410080c140e02d10005112324546400c00c40d0703012003540a44600ea105103003550303101c8000c0e00029a240800c3c0900c0d40d110b80b80310400400289059110500804d40660104005020076140f9091202d400070f507118000000980603111501031041c2c9601c00c142d424200218106090141030b14051324041809041e07959404000303150103400c1a11071250f002451540514101c10b40c103032250042d000c28004182c8682c840744584d1010280444ca40c186400346414039a5a01011103c105000e001140c03d802228181401d640b002c2c000e00d10000e42135000540d0710b00700807051518103558481190300301403030110103002401000c03400580111aa16010f0f4403404400005500c07446152030050074070110030080c0c0c00c4c07048103412650490710201c604000c6419414580314101c082181c0080c101d5105d124800c58600807aa5024401858850801e0406403290f940c9070707010103184101100b03014500070f0901040b96454280095000301e00c0901150008640345510320003041c1c0303041b8107141d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 214660845 1250 214659595 214659617
    0x60309170f040905010b0a080108061b0f0c0d030510050f032104150201050604150b0703120b060403051c030c091a070f08070201090503010b0a0b0f070605010e0702071d0403 76
    0x78640e00b554050100c43c0e0013042156500d16000189901186114022030035a00000072080804030341c8a1289110302800440041450702c2080558021002e000745282c0031b015150058a003003100d0082007041d41c500003418200409540c0182450358481c600c40c1c03180050200240c0c80c041114040e0200003540e0720281281c0407000120703801550401111801c4240541c00050341c150449401803e00b5101001083d490f00e503d00e1402c5e00c02d004001d00e0400802060340000e05c6282c800d003000ca00c0c49800102e44080c4d10009078940e106500c1914140d0010705101c401028040071014071048a0408000e10001d203040608184600d02c03e503909100b921a5500d444100f000c1102c0d40e50b80e004d03060115410440c075095103203400c0031000740d00040c0c0d18240881d00c1d04051103010210040104030040305450440c80380c4440d07001081d45140c40105101c1403000410a0003034501800b51280401040d14200c18000c2c40d048040e80501440020704030b0464401702008003180e00181c241c5003401da408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 214662095 1250 214660845 214660867
    0x509010b0607110d1b0f120201050901050c070e13110f0109061d040c050307020c04090c1401140c06010e07170c0721030203071205240a030c1d0106030917 68
    0x111810017415001d08039400380700c003001c0d1048010589541d100a2404191504c041c402101c08498000b4041384e0304110b4800c4540c003070800b504d0010082e408585c0382c940c40c0c55001c2d50462090300c9030400e40d40e41d18a44810001d881e61022044e11041c0c440314800311420000038a0f904451064806000700000044079110300c8101c50015030001600034800b449400ea40101554400c403040c200600074800c00d5496440c01e40140c241085d00f1482e20080d46042c1144880c1001c00c44c40c2440c140405446d05c001543c221030040c0991400c9000a40344943c50001c0404605800408110030084e403511307680c00706032094034026003000e680320842c0d854002a117425540d4920b1704501d4003450041860201c034055154000750f1186905540daa01400c280e10486d00507964140e0b4506203213001401203500b800d1010000990303a417001001c10ba8541d40c4da854043c19088650004404080e01c5555031002c1c1e140810046c0c01001e140c5801c003c85d101d81d44404d420f1032048080500c0450001444c20010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 214663345 1250 214662095 214662109
    0x210225030c05030f27090403050a030605030f0c1513060c0212010e0105070216080c0d0203010603440703080403091505070501050a0c020307060c020703080a030506040509010b060711 80
    0x119500800300c0c4d558191041182e1000e4210180d410551210864203400d0304e0b44200344240c00c0c0300c0162500b160b94465aa054541740c01c070100e118100340d03480d500080e55139030402c020300c0e40e54072510140402d05006010702c0094107000200b0b14030020200000c0c1d641c0c0055024000443c1c0071407901c1c081c44a02c1d40b000a90101c040c03040c411480d0f0030407040c01201e580640c0041d01070000d40d001c171440c0e10003802d10b4820a040f1445001c0003074000c580d1480043c10820003406842c0d200800005003c2d840380c3c0d40500d0914460354200c13111801c82d66031034a10580b500388900140024644e40e1403034500c031850800d94071a41e0001810000c2c02000300c0e0405000701d090201a22200b01c0c51204a050608003c006801c074080984503982400701003509005144038048600340c45602440c40c00000e0741f940c00c09400c2e0245103004602c141318000020410030707009440803000e40e40d070120f014100102040290b80006d0069070741e6900d00b0807a4910340d944c0108640841d1740c0b10004501402c0500001070322 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 214664595 1250 214663345 214663367
    0x506100c05011107050f060106020f07092a0203040f2405091305010801020705060604020c07051012332d1a0c070608010b090d060209040c21022503 65
    0x45940204d040c000b004004940c03481006e400e002191201c0e031303980f802282c0d15800d1481c00da02da030b04224010310007058140c20419200b40c1406a2201e582c1c0995510240c50900c0c43c80130006800100302400b01d0822021214001c100241c001d415407690204c54600780c03003454006000380b0000068510071520f490044844003004900b040009683d503101c01c5002c1d50000400300c505004000000d040f91920f4420b8444c5c0c10b8464000748076540c01c2405101d95124615141014032200295020310b8101c0c1d4050348000e0800c903507031030b50200022181c0d4001d8514400c40c210100d011030320144140240c0350031041c141d84010840700d0308900c1e01c01080b04038100f250072036040744d0440280034014240d10802003480c4100b410031103080c1c559501d821603044a080c050791850791030030025212545010340c1860600b50040714010314106040380001c01b00d030942900d0ba40802c1040c41c400146800d5017455403800441200c0a510341a0b6081101c0350380200006102072040c2d01100f42c00c14580b0489190340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 214665845 1250 214664595 214664621
    0x150a020a12080714030c0301031112030307030c0f03021806030601030f11030f100311060304030318030206060109080d0e120a02060706090c0909080313032708010f0506100c0501 78
    0x803022020640041c0b108008071442c1004c68030103018031108a149100b141e1081e6400d525050450342155110308080541245540c1d00410400c214624900c0c20300043d406094181c0f80000c00c0700301c410000d00020604010342c0145441400742d4200540518070015201100f112440d036030380c2e0342600503401042c914402c1c00f0a1450900341080c01d4038501c00960041510504a20850341e03003803075a00d44080b6500008010f5051a14003d0745404c012028580292080c01c000c07800c00062001034400329036148046c0c0060703210703100380f0240707503001100c0e84041c02c07070840a0314161040c0781c00074000d00d2600744007038040c0e8110520680d580c2401d10500c881c0a5008181c82c1e560421814500c014040c900d03070698100a0120b400640c0620901c910059654801c94890456660248036030b00080301030340550030310044006502c1a0900c01750324500c40742c0a1218201540c0c1401646800c4601c200e000b814000d140c281880b8407907075620410404ca0351903207400a100c20071880c0c0a40907200d8181ca142c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 214667095 1250 214665845 214665863
    0x209041b0609080c030309030721060e0a060f063b0108030d0b010f080103110a0905130501050603013809070309120e0a1505040302150c0609060105150a020a 69
    0x20940e07507480080c03001210490001c48060604d00d01c10540c0340e12070031641551683c000b5004020383c61401070703240450040000c81444000c8680c4440d401d50b6010600d40a440c5c1091054900300450782c400c011005401a000300031090401c403039101c208854500c20009800e66200101c48154607181944c070700c4e42901480d103895656001c04ea03a90380c00c64411100c405050a035903003003a502ca45d5482c10610050780d208400d07039186440c4d41a000391752451058004003113071400318214045001d03d50140299910240c3d40345818184142190400340015101341d06010a4400d00403011151503002080c201d201640d43d0280014000702e19000c1c0c484a400c64541d03402c00c4595034150b0310041409000e84603050000f0b40c50710048805010b842081540951101c0301030003070325000f00d03001c04503c6850601501d0304e80c4030b40005840304840c1c0b800c0c68100c10f0001d0140380c1c11006001c410742041c49400103009a504083c00607400304d4641c004008585800301d240392005101700035400641d0b4104a583c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 214668345 1250 214667095 214667099
    0x527030901031a040c080f090d120b030a1b05040b04060f0924151e092304020f0903120a140d0605122805030403020d0629040605010c0206070209041b 66
    0x151001c002107c40642459005000480390140840d007440201407a658296411250014220040219084241c2c1500c500340c445400611003001c0d0503031404141500d146514542000c00060f540b4901c03560380500e01b090710801440b40c8401c0d544003900d101d6903003c1f609a0703ca03110400081d4680258555118a07501c0002c0d61071510500001c4100b4580d035520b109184062140701c441c0c040406080000f40e4100d000c2081c501514802c60a4060008902150007041d80000742613810102080200070800501d80c80545020807800c0441070203265040d08200b003c200c0946100801102c990300708800080048128655510500241034024080c07928695604241c40d9200010600e034000240d0074151156440d2104881420940d4080019843e00b425682403210351043c09d1400c5425540322184030001c44051202102c114290500b5680c01c0082d04041005603110303684840d061110701405500540c54410448a5003a01500c001c00d10362568603141d03650902c411b051900d900500940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 214669595 1250 214668345 214668347
    0x5160b1308030709060e0901060c14030f0c060105030712080403150b040f0221012105070503012406080106140309100507050d06080d0c12030b0d03030527030901031a040c 75
    0xc1e680075201e150399402d400320146c0c3c0500646010078016240442c460440080c0003400c4462548190400380d0f0680b0f080000740f03600c01c99160800d15018449402c520010300c03040c00d04000c0c1400400a0014129968201e078aa007060b038400e030700014103a250607030719a03c14a0041d4003d8802c0c04000784c8200020089003889034020b401c8104480e0743d000c03120b031681001099045000381a40d100940c0040c1c03c80c0780c4107080041d81e6071000d00711014007445600062541c2c081c800e00300480b40c4500c10039003400c8a00100200440c0e590054000d204201c001070000030745c8a1003011004110100c1700b662601c4009a039468500d0141d1001225402c3c4020800a2a400405040b003000b100b2001d014240d110580541c5034000f030780301c0e100092042d90002c0c010075101d5912888403500381c1000a0700c0c030000c0002c500d80044210041c0c0229441d0400d0285003045161140340031204080040d403420282890303540c807032042102c040c0c1090303221628035200f02c0a903d41400d404400400c204590020404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 214670845 1250 214669595 214669607
    0x19020c030d031a032a01090f060504080709020c0c0111010f0501140a050906030307020103180b130b07020102031b0903010b120a03020705030303070c06090f12030e0c0105160b13080307 81
    0xa400c2006002c074200310080c0d0800103845410340032105401c0b04501c21001605c2024507114a202d4100a10803100180500c144c0070850041e01032a40d40c1750340c0354188140c040c50903940303911407441a0310400c03440c3c800010200721115248800d11f0108541d44003410b1550240041c40d041b0101549031a000195100100d110158a00410740f503214019036103408009031000300b19950358064204000110041d03102b07a100e644080c402d02c201100520b040c0d00c440d0810300013100d02c611040c05c24401c031000d00071504201a4007030342903c0254518945840401d0005c20310803480d490498001c03807041d0641c2d50030740000307404130409456440c0140c3c1140106550b654068019009401101404a41da06000c030480e41310700240e841d900c1d24401b445e80c0b40001000840010b541290311804c07080700003006034150205014050b5008903403903840c851143c0c00c0082e001c407604e06000f01080b1030180d01d00c0501040d00041c1c1c1041c16000c082c2d9803600388a444518030200209044000801c02980e10b030400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 214672095 1250 214670845 214670861
    0x1d010303020120030a150f03060504031205060f010c060f0903020309090901060303140f0403080705030c06090c01090611010e0d18090b09060409110a080106210819020c030d03 77
    0x41d000b401215803916260041d0680e03500c44040314101000042c41d00d94454021a1008401984040015550b10001200c900c0c44da00202d030031903211000d02050642c00090041c00c0840c090040166042042c00104000a004110341c10b0104c00103025084c040320344d10400395041da0488c00d01241819203030081d00c2c1d0707012060b480d100e0791046001c10314856051003204203036a80b5844104423034034640e000d03804541107100201d8400b4000c0002000080a40001c1c064142c0310384011612170004081c41410040010302240507948006c0c5000382980e841040001100c001e4140b40700300030075032143c15024044110f80d0324041d00c90601c8501826601168205020354a607005025050721002401f081d1011a44c00340d40c403d16103008035503540b40c17a42c421000d03148501004610040300350041000540c4607482481140d554a0b01044442c064061241d00002e03110700802c1b520210799502100c50013410404d140d280802111241018000c220f007151502004088a0041e01d2203507004010b001c030f071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 214673345 1250 214672095 214672097
    0x20d05010c0908070b030f06130b04022116021e0a08030106110f0f1011090a090b040e030c031801180312090b120c030621030d1503030801050114041d010303 69
    0x131980000e8000740381010b40380035500141004515450310420495414021002015903951f90f1417528000d5440707100405088080e003a04c908088182c034823580707503404010b101032200c001d1201c00014080d40030590580e204030750800c0a42314500e068819141411a400051a01c003000002190325034114822542d200c183e20300f00c800e050010300c01c40b40c03900c02d50b00c91070b20154005031100900c2074050700000740301105042a181040180d00010303405000d5075008502896541110300300728141401020900c0c8101c81c01145010302d0600d00325074070710a04000500c50402d505448040d40c3c03140003610794450388000580c0849480341010112007401c942c9042c040b03190140c0010f4108900c2042e42c41c0007001c00300c0310010341d0302d0320031140c1c08d980000c20441c3d110700e000b40009085400c04216002e10803201006680300d14851211200f00c49000b28210810600d45400308000303680540b0240c15250286402d40b20032000d0701c07a0501d1400f80e41c00c008a400c5403c20900d9203222102011812a406 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 214674595 1250 214673345 214673353
    0x7080d05010602070305060f04110303030a0b13060f0b0f071b050102011505012106050301060b0d0b090c030a0b06070b0115140c101503020303210f070503040609020d05010c0908 78
    0x42e03001c0981c0d0381c00480c030009102d500404000b840401d1010382990780706008902c4039503814801030010382190310446039800150b40e150048403090a0065440f044d101c2e100e242001407500301601d03000010300c98810100f414800107840c08004083c0402e40340010f6002000e0311403464800101e1031548458081d0a00540c43d041d5100000031100c2c048104a98040c0c4038512061412009010a0041803d04030b500700e07114000015151403d00c0791500510504100c140c40e240001c5c00d03403080d2000410a580724002c0d120a01c00c0410408080f660055031600002840302c10a001041e00f0f805a00d80203040300840d5000050f12104202c203400001c1401d542e60000840d48a01045490181010003119580700b51525501103116a01c29801c1e92070b50b016040d9413a40d039500181c51503210202003101503551b80001c01d070398945056030a80141d011100e084081c07500890003006d50100600203040152185403c20554944a0f0303480c888a030804004d102540a005018001e142e0502c22600b2502c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 214675845 1250 214674595 214674599
    0x302071415180319060531030e12010903021c050f03090c090a090210020105330904061d0102120403120213060305090f01150b03040201090815010914130213020403060207080d0501 79
    0x40518102c0390500e9000c510b418181b0b241c005d0300c42c3c03c5080f085003801191800b1b2749282e9101041c14043d032aa60f0000b00d591001c0c4e1800070b04200c00904404100400314104034446501b003410b030b0340c1c4440003442841c1c4a03070f1154030381f0345400200d040f5135400c50005014010080240d4210f081d400c0d000f664204c050500e50b250032800c8510840c2c3d0b0000d20805c2c4148091040400300c0c1c1c0c070324000e0744038441e800d800b05018001100e061050710125800c07030f40c803940d80c0f211040409203003003540800002103090500d0b445002c4180389008000908006017410340540540c416816260f807002241107140352079880f43c1025008010951b1a00310500c075044459000101c140561000201c0e140118010140740407030806c035a4101400481c10b01a09010101c0c040e501080b24400141003107483c8661940351036204c0341104c008440090041000d201086200c0e00c40b030141c48480c0b6810341e02d560502642c010044003d010b250801450280002046014040554041c1551115140080240d66 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 214677095 1250 214675845 214675861
    0x1506030605030c1e0a0315020d0605091603110c0a0309050102100e19050f0a030c120809032a10060905280506010e09090a03020714151803190605 64
    0x2164100d50030b54091402e0703901030100301404591320314002004c1c210380d03991500d030b58804040001c1c4010741c4508a50101e01b0169242170b034041d07000208010f40700c0e4031160a08042c0c910385007465520000502d0340352039551007a50342030070481b41d130304042e40c0940e000185240740040090401d8840e0b140148a403c032400c41d811802c3c401d81c0010041c480080c03282030058100380d0a00c646d51501611740e03019001041d60113043c2401404045842a075890120301004d00d89480c045201e600143d040101f4902040040c1800000312195452240c429140703440c407407402c51000c40c401c002c100f026030041040d20040d21105400c80403d80305007180c18007440d41d0790680c14562154040d8600020803035143e0394403104140d0b070702090708504185412040601200302280340500b080da8808140d5201e42500024145d042c0001c0003d007071003000c095005e007840d000260415210079482c1d4a692000550380d00e81c11141d401c0d49220842c0a001d40e441000da0f0160108480381448042c4c510343d0034003000403480 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 214678345 1250 214677095 214677103
    0x12040326040f0608060607060204170609010b0a0e0405120d0c080c0f0301031707020a0b041701050601020706051c1b020d0306050d0f02060714160504050c0d1e150603060503 76
    0xe50b0140b4821800c4501c2c01c07108668112000d8045500910704105c40c0c000715401d80010f101410103400d01d070403000003035001c0303500c1c18800520344016079241c2229040c49990b000c2100041b210a00e0010740c0c4c64030342e0b04005041c00820380040e02d00031030004402240c5183c40e00824140340f01a00e51b0360f065540e0000300000792284e80211211460700304014000205013130210000000c1140c0000d003044d61940c00304620703850b0f07038103c1030186102003030405c64012290701c0c480d00303010b00d00c000340620304104001071b541e03c1083c09032000384500170920031001e060701d4030340981c3c0c0e00003031505015465034503a9107000c1144900c2e909006000d070700301d01d0000c140030703000b110304603a000352400004605c2c0d40c851845000c0600c0080fa409541000614045440f04a496610080c5840070307100d13040004001101483c890b078007640c052400c02c41000781010580d010368074005064203001c40c003141c01d03c0c46800308802510398071b40120301d031500ca021080040c1d8464802e4a03403a0b1000c1003115100c608050f59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 214679595 1250 214678345 214678349
    0x301140912030907092a180b0702130c0e0303130311150301150516110415030203030304060905070f0e04150b090402100201060f0e06030d090605030c07051204032604 73
    0x3c0c541c041d41041100ba400d6621001c4681075280c0c0c15202011280d46100400a00740f11200008400312481240442e40786014802042984541c80ca008640c1d4041030385512020005100c2d0b40c3c2d00e50383c0f044030b180100480c003003843e4010280ca42d11a040182644000448e000903144d828003c40321207000c2c00d1440c0000c420f07042018030f02c0c0c15686455200c1400c1c50004882004204040c400c9600040e0501c4003200210310880d510b800c00c84000040c4002c64100014100c0708103040c560400250320f002c4110303a001034104101040c602801e0034810703c0c04810b03511034482a6440c1d0400291300f4154140075001d13501c5002250011808450810f0170795000c6220150300c40c21030f001003401443d210b5141c826a88050001080250f45c80c8110207054005030f1020381c1480d448010881c1300e1806105101c004a41e40c20301082450610f04020280c0c00004d10801078001d0010351103090010820401c03822009000106584a85902d03012841210b0b40d800052061034040f60344504404240586003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 214680845 1250 214679595 214679611
    0xc020a05042901080415110403080301230a0b090f060906120405120910050313050706020a03030f0c0c0308090c1c060c02010b030607320909010801050c07080a030209030114091203 79
    0x91a410408817005042c10a011207c96004000000004903148055802000807005141c844003940c4460742100400c88142885400c42441c148080e018000964004140030340d60701000d0805800421094481d4041d420783c804000308949542c4041050602c1c461840364040d02c006210b841e0100304580075880e000f070b41c00500490a405150701c42d00255900021007900214074815a440e95400c1c00c1c0c05810038030058200145d03e505046c0c03d4000d6840b1107105c00c0080150903a103010080c03541042280050400c40701c0070200b245e80344100201ca0310703018002c000d491519500141039800310084041114680d04180700c44140702e0061160000011010f0040c02d0907035100341023280c100000b42504240c43c011008058000c081090407080a21542001c3c0307503607400600208510900d05074080300c103580c140f00c1000050b041100544441640c050b00050b1604842e59081d40680a20615550950b01c0c0c140c000c030b184041140d0140c01000020141c030709520318604080614482165410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 214682095 1250 214680845 214680863
    0x50d031107060504080d0609051605120105040507050403060e07181a0108060307120807020a0b03071202072118050d0206090d050a02030a2d11010c020a050429010804 73
    0x103000c0ba1070b64100e15806032260380c505162140c0c80d494030341203500c070703820881d00f16940d90100400d8074468144803441910509080342440c0c841d960003503458005004090040391918007080d421401a07080c3d5002d503502c4242804480c2980c13814550710400c070b00c41d5401d0002a5069011920380c9403041014000500c080f01c910084004015039841001500b16505803160500000d800c40302e031840420b049100d0711181d80d60b1612070042140052a54004216203002001403280c00c64100c6000300340f6411000025071074100c40d0800a00000340081d004c01c0c41d2410044000c0304580c0408141071b5090407840f0000281c3d2500c0500040e00c503c1e440003508840d00300300500c80d6240c0f0b21212849030b8800c0044843c0d501941e0701280c1402c1c0038040c100c810030240e400006000f54243c880d82205212440c0341d80741c03103007640c079403e1004441750f9485052240a245001c02d54440701e1882c006414003402c144218445600d141e100c4080b017800c1000d03072082c16a0b528041d5031080001034001d503003202d001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 214683345 1250 214682095 214682107
    0x4061410030b0609040612060b060301061709010908040e040323040603150b0406050d05090d0c030c03180824010308030f10030605040b0f070c03051c0f090f050d0311 73
    0x141c0c02401000045688042c0500544c4400d94841c007808024040d8151074400b001068504101610610381c1c05512400c4240010b100c51507001e480d03140041c1d00040700300302d140c90740960a8010b01c01240e016008400c00a8042560b904036a031107401144255030b400d001e201025001e00d664050045182824401080200800d503c40e13009002e41e8541d001140761001e65a0b401506958003d80c03142001c21008115201c549150b0f1194030361210654003c0d10100c00d1045000701031180401006051000042c0c0580505100d913080c010354014200c401d408140d03c810301d15980d0080c0c1c0248040d4034010f1051204c84d102003030403050490350301070040c42c00c0d13031942c080794a10b865000b80b07010f8000d108840008007140460082c0760090303004058001280c10060b282006c0b64ac0e005103035105001c03a07050304400080c1d02030219445c484500110508002c0c407604104090084002c500c1c00840c180000103050003205407400000c10310560072200c0c1070500e1101502660618540803070518414450 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 214684595 1250 214683345 214683347
    0x110a050a120212180c0604030206071a0709080f030903070504090311010f0207060b040e0d0807022d0f16140f12010c080106020a080301121403071104061410 69
    0x58010280a400d20500d00081424480100c1c0c0181c401400240601028400c88940301803c0c03a0503024104c02030010007241c1c0003c00c58910407031000a0286600180c1d4500340280010181040010620b01c42842e0400200007010309045014041d640d010349484075401640000482c0e05000014000d00160740c03030300e010000184070b0400250140040591501440c490078030034400d904d40014001030b00c92143d810080102d900e590001c1e805589011000301d005035000074102e080d8211403400509a550b82d001c228144100950040c168254030005801c2c401c8140220b840c140c5551001c0743c0c100d2400401f0540c1d03a403006400000481e00e1520309109080c3d000c4001c2d008901c020f00b651b5648101d0401141400c0b4140901c84100d0b55501c4240781e08981c0400854010310041c801080c00040d01d88525078544018800c10034074960199002d001c101481110120300351410080d60788800c0f9605204545030599808240300324680300e004600d40550413030740c3da41103101410405c007032201a00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 214685845 1250 214684595 214684597
    0x81b03070b030a020f0409061e080309120f010207030509041505060d0203100b03070e04150b090f030c10080702060606030f0109020a0c060c0309110402040b0f0307050f03070e0f04110a05 82
    0xf1442d4115001c1010104100040700144014a51103e000441c103180c088401e05213245508401c0d805600036004000740c0c0c2d0300105480c84010700f12000408080c0002d4001c0c9080042a0b0b61091940046640414903800002030312020809071414081c1a20141d16190506014001c007a4801424007412040c050154003030340e88401c012101c440c42e00e44401d00440075030002c5800000003111442c009616040034080d00c0720365580c20750151b90685c01c0000b0715409000e006074103409800ea46c41907100340e942c04c001c0726000c4000680380091094400e10010b0222030205c0c0c031000980f1420010503100c4c24602c044034403403001d8448a04d00e1303909000002001e1f46c01003c00c2d00c01c0003c440c0001c00803801612403559022015280003400c61294a405101d8200301130a0a20451044c00300b0000480c038a4122528111100310481c0e582c0c0c0d43c400190360b18020390400e141c4c000742c08020004c2d1650003211a8a6034141114981d4a281002d01004161419850050000e000c02c3c0451000a40508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 214687095 1250 214685845 214685851
    0xe190b06040b06220302031203010501110c030c120c060325020a03020c060901021501080102130902030114010f050706060305030702090109050420010c060e0c010e01020a0305090108060a050910081b03070b03 91
    0x86543c0844d40d0701c1d00043d20300030304012054000d140020040020f581c204070805001c00005015115603032012001070340b941d10300c0241c0c41c003890100c907146400541c18406042d0404000345034030389a044c01034008011414541805a445100940f403120715400010b0740c90360541e06034028108070000f14248038080d041500e10506601c44c495540d118458201880c0e0b02030034950000503252180d600c0c2c1c00000c05441d50040c048a40304000612030180e000d80901444942070a200407180d00d001400c95103031107a0200a08118580040402000404001000310030b0003100d07501c0b081e07621545460201c48064800620303421040b42d140031004e1840041c800a0103050601814011150700e50100f40c420400340d20235180c000c11301c0d004240da0070240c1c011782e4103420f100409100c9215a00a0214442c154005050284513000207020b80d03501c8003070f43c000e00400b038554400740c00c03c11050160140c090040380007a01840003048068006046400e19001c002401405140d01d480030031100340d400a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 214688345 1250 214687095 214687147
    0x30309030406050d02070602071104231b090901080c09060402090603130c1502031b07060801061b140a051203190e030c07080d020609010c0906030b03010e190b06040b06 74
    0xa004a001040580c4040d100540c01203001c0d6002d003901504000464642c03468450cd055401060225078070002d0100b42d90140002d6240000075502c004120840c0c02a01145540301e0090400820f07490350115000d51004000d0b02c0400d142d84031031040100f80c0c05214101500901c0074400900035080c08028200014050000091880d865500c800e2120184110440140e400020011038410302d102901601d612948060300e002c5003080760041181c00180b20b401c3c00c00c003105000080010501ca041c040181d0b000c8040d0125812a070304040d1520081c80003a281c50296042d80c0c1015003040c0222441400c2c48501522500c0d5103003424801086060107145d0039120520008014000c10440c00e0f010380402c100521440010500003860123400401500c1580d043c001c0f143c4139550080f030760000340d440300c0c1408540164039034082030050801c0340524100340300d0000d80320884480d4010100d140b038061030070114141c2d2170b5410f00c01070b904441001604140b04000c1d0310103002420340100140403070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 214689595 1250 214688345 214688347
    0x9010c02040603151a06070803040311240f07020d140703180f150c02010f0e030a0507060f0210090c0b03063c0d0302210c06090102040f0602030309030406050d02 71
    0xda4844c1036132014401161081070f03649a10303030340c2d0803c5848200800d80e402100e240b8a031007140c0d540e0408602002c1c3c802014000b2050314500000c3c8244810a840300903c02104104c548010103d5034414050701c029014186007408200714900c00b040f1070185403d02e85904290461808d11504258444030003541002202c1e10040d86480402c0c0c01e0074014841c1001c1d82c2c0c8903030305160f0050b540c80b900c10900018482140407200050b6009000c2d485080410b0401040b5012a10702190804981e64001442da00460300c0101d04150803802490a1041d01d6003200c1c07159404070358904c2119580e1201030805186840100101407482e2300030b5500c070002808138036044004603007140b20501100004001d40b01300c01c130b8027084d250000d407502038020000c9403100b08074209a01e01a4a80046405100703501502c220047e056040c18000c5032003c032600c0044801521b000ba10090007500140949810091002400a4070a1000041d00e006200f203a001c4d51a0514091040d42d05030301000d100024150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 214690845 1250 214689595 214689599
    0x1e100503100503030c2b080f06040b1009030507061103180111070e06040c05180907051303061d0312010603050601180e0414030a020706210504030f020f0105070509010c020406 77
    0x9040c0094000301c00d070203004207100f4082c0d00303000220202c0354202049060700c490510301d06035889518560050404103401c030300349e1114404500a40610300e20310303401c003200c0d0000b114203561020160040368003600584002d5a00c5010031280c04402290000c0c09600921a22005a07851200324080c00014106640605908040c00e81402d0031781d8499004405000c0410030f00c3e0400d8001d07240e4274081443e0840c90704061804c4c6803a02480041c0075809031401743c0000382440e0060044440b10b401e004d105002c075980d03a03d0300002400070b08102a250145180145808035400002d40300440b1060500010b0b41c0e082074022001880018001410040a00d002030b11042d80e104803680501044442c0482500d03060070a891402c1c1d0342e030100c18131075000b002100380a0340c0c080740f1101640c8013460070320400407c843c940109039040c2541c01460a182c401800700305604000c4910314480b454083e90175803050107040d00d080705e0b41202c0c036001258bc10400c10300c032984610403922896100900c0000c11036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 214692095 1250 214690845 214690849
    0x1308030a180b0a0f0b01140a0306050916120b0612100e2401020c0306070509120106060906020d0c0c030b13060c080106030b0301050c0702010809070e0c091e1005031005 74
    0x10128106075602610b62041c0040a080c5000b0500280c2e0b40e80c0e402c1c00024000000240301043c2c440801c403030b4600c0070451004961080d0813082c0141002861003040d403c00c0d03640e024080c1c0b07201e102400842c81c20702408051078180d000e000500b0f440203024074100340d0b405846410100004000c3c906036000c00b2404a0343d0b00924084074021f10702e14810000010303d00c0c04000980520b03490603170656001a100c40c000f684d00180d00e5030300c04001c0c40c0071500c2707035091008101c0003c2e441021060a5017807a80c013040d6140e00409003c01c0350003c0d400c50303808404800381980c40b440c1c40500507040d0303c2c4c2e044040c00418a00c2442582004c1604c01400d425181e5846100c201c1d0043d00603240003508100042003855414010106008402c50082202e4240141c003e2400e1003001802410f00c4000d0b400941101c41c18000c000040200c0d40a09004d0b00d4a00103400c40c944c403e2000502c0b80104074281c0d0a10040282050a01e0f10040c00300744030320350144801d13110b07500010103004002154207004034040d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 214693345 1250 214692095 214692131
    0x609010519050406081810020c010f020c0102120112050601090b06071505040b010f08060a15030b090a060f0605010f111009030e100e1012090f1104141308030a 70
    0xc0d040c02c1d69a29142c0f414000b00400c3e5030009002c001603444c041c01c04c1c0d807600708046000405008200c40041e991180d00d01205e0141c11414160380c421440030a2034442808190000d00e110840320071041c1d000c0c0c0e01c0d500102940480303010701a0166200d04014080c0c202c096100b500d550500421581c2050001e513a180744d1980ba180c041d400441c0c95400340400c02c54041c80700e42c00340003100392021607581450119507071602c0c0200303401e10703440d1500c3c3d2031410651000c1e400009150401e549080740e180c04000f8560312225160103c4d50585842d410f1100b8401c0c43c4181030540300160754203401c0844408040741d0200817270031102e034030340915a004c41014115209601d40c40c1d01ca07844030340100240c0020441200e4426450b88240b017200201580503940d86d2440c81d1802200e4100306240d8007042108000a10410304000d00b5400d5003c40c5406010282c0e2806030503075030072035040c001d108103041891400c210a0300c0498140a0912a00c0c000403c1d40b800303182d021104400000380440b624001c059a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 214694595 1250 214693345 214693387
    0x6020d020412051f0c02030a1d030303040c0806010504020702220b100309030210020301030201020d08040c090c031b021f0207020301020903100902011805090708071b0c15080c040506090105 83
    0x4944c0c824884450341d0340a44a8500300014015010042d01100e05006500d9204007085032003081402d11030b02443e46240021300e4070301513024048a45900d0107180906071000580685002071007070800000d481c2c42d0500031a20610f502801a00c54035002c000e100102c050740700307905440c103600c0b18440082a01c2c0c2e0a00c003001c0910b11382c0c01080e1075550f4180a03041c0240802c0f40320460380100014400741c0d0300010403107650400fa142c061000c1c2d8540c02c00f0380140a0b190840b040301820300b10140851a85500701c14450240c078142989802c011000a80c1e8422a5100703c410503266101c2011070072402c2d6000c1c100d202d0005d4005403408110b5000641080062480005042d54a030050f20075540d0100c280308000e00c0c10350706011100c0c1020002420190001e02c2d0a041124040c001807000d44140001700403803501051300c0100580c40d1034031158410311b600402c10001900ca4550750760310301c5440c410b0702400e0900c02c07551800741011f00b07104c071640c805000070b4103100e000c00414209030103454042c09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 214695845 1250 214694595 214694603
    0x70c150c1406060109050103060b07170c0a120e0103091109180f0a0308100602061512010e060402040c020d08040602070501020c030319060b03010e0f040204060503030f0d06090603080706020d020412 87
    0x1540c43c191001510540780341d0403040c101860840e06020300150501120103c0d07410895030400088101003141c00361050f038202c40040d009403103442080003012134614490074010b4840b40f01d001c0100004500326500001e01030718007500980c41c40c106003000d508640c2c0040035070b80014403002c0300510840c60302d81c0200440d2025480a4840e034145039000e540e80340c101d061005010140d030b02c2c154000355210310191403c03020900c4162200c07040c0d0742e014951040070f520100240050700c5d81c090065203e031011101a4011403c3c44000b2520030b2002ca005080b242440d25404010f0300d0b141c9800000303402180d0116030543d130800105200500030000340d4469082d4901e00c1d002c202a40400a090b20490703030101101c2d03a02800184000c0001c0d10f041540300880d00400060307544c03540009005000b03150300650301808000365040132002040c0040000c04000e20707080c00421b039101c03c0c403c100e80c1940310142c0300300014400e00002800d1600104900c4510117005810252280e941c170301034546d000011a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 214697095 1250 214695845 214695853
    0x1090804050a050316060305151e04110c1e071e0602010b0a0b0f13090606050c07050907080c030703150b040e07081005040b0301020c01050a0b090c070c150c14 70
    0x34a00300c49660050b100c160007404d100d44120001041c4017109019100c113064a60000641010b0580d180713080c0d42000a05140d08010130342204442d42604a03000b03030140303040c0742c0500884c4600380c003200d5501500000070700d00040d000c0c000d087c503c0b101e515400428061008000b44100d040b01e1310b2200c00c1882a40881201e14005000c0e084940e240401c500803140803104000c83c0440390152005103400010150352680740000c111140e04860304580c81c241d01c1d0100101e0340991100160038461100c8003201c10741a110410040c1d0340c0f00480f107a90008242c0c200144081c0e012030041c5402820504002c0f03000e207014501c50030011840e03040101d582c1030104040040840602c481504038003d814419800d08085480c450000000c1c02124080c03600e486045006880035070407191038802c040020441400c1508660000d40000b8410610510904006c0360318101c0c844110b622299020159510683c9400c803c80300d170341086502c04c01070141110090010509078104c114442c01000050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 214698345 1250 214697095 214697099
    0xf0f040f1d011b0e0d060e0c0420071b0f03051c050a020601060e0303040308030a050a15080a1b08030d0903021b011b02061e0403060f0216200301090804 67
    0x64814031406880451982c10720050600380710a854038007002542c18500300b1044030800300440c400c2c503540c175002070a491605510160f03040000c100c42001310400c580500c18228041c4240d40001108800c03044524401c00050000071155610140380c01021040702c003030703560350342d40e06019846154016501c581280c00260070390740900851381018130341802c1150810085030310096580d8014040d107001e1001c010003038841c940c1c00b002501c1c02568060001e5a480c60200020b034041d200944d139039903100d414242d0300040800c400070250309840810000b400f518515443c0c4080c1d1000d42c540c0c0e00100010041c022130340440074002003150300b8003003d002c074490041e4a0001c1c82c080013010141d4506e0001c413079010f40d5a80c451500c0400c040184805000c0301c8083c00022158421003455201806081c820b60001e404680086d004403401984100443c84840e2030030800e9210f500d0b0408540282c814100c4c0001c0c900034110f05824000c80d00c84501303500d034030740400d0840ba1803030f03820b0761070702c07030120701 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 214699595 1250 214698345 214698371
    0x711060f0610030507020a0201230d0905070506090319020d02090108030a1e050d0515060408071d190207110301050903180d050307170d020a0504030302060a0e0303060f0f040f 77
    0x102c01d00001c0e919041060345000d42000352541600c400003410440303200400191541c80340030030202030131145c0b6016660030705a80204002c0202c3c4404403160b004013840020035103031480c25500c1007040a0003030600f00001e00c0024990320360051003240d20a0588041d140907813292410345020300780c884000c59855214010107401e50a040668030f85014150031a2000790b03a000e0299203850720030000102d260707150b4201c00011106901c00031030b00302001007000103102d040000d0520403100e00c2e0b603c602121907103516071500c2c1c903000c8541500c00f10380c80305000c200c001c45500401d0890300030840200c01e01c090700002801c0d10025111500380340d00120388180480091010310a0000c0100e80c0903031f9441f16036807010b032a4043c010380503005003003500011550507000000c90319215901c460440da500f442c0e07503000d01240c02900003540144240070000c1d0240905105000031b88182100442c1550350301c0c0104540180c0828080b500a840340f641c0201c5078803940244641c0d0369180c0e00c00720b50321070b010607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 214700845 1250 214699595 214699609
    0x40b041b03031209080c1617010507020a02060901050d050117100513020105090d08070b010e010b0c150604020f04030803010303112406010c14160b0901080f0711060f06 74
    0xd880000000d00c42040040e41080303c58056003260748002c11034800904101546000b001e11421490160000007c0446883c80c01e14042d140070642c924400c00b01195139a00f2598111901809640440c0b00c030130252030018040c108606d014504a4500f003d800c0855090751000c1e40724540d04903140ba40c081c05179000b4001c1581402e42058100418500607890400104400c100039050103400145c02e4084c0c0c4130014400d5003550808461a42c0e0811880d1804000409218145014101c3c030008140399020704101c80c2c0804050300101014410000a0300041401400e159400740d803c1084540390100d80b405080114080d130141c544940c5181000741c1400030043c1c0c140c440380c0003414550302015890b20b05030800742107041d0820729030703650f000144e400d403c1514000c0d00c07114440c0c4203440f003090001858071151118458401c4141d940d00058007190040340700180c017040b20000000d00c00c0b010b001c40150300c42000c3c9416059603080031001c034104131003610400000b031440f9040050341d0905c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 214702095 1250 214700845 214700873
    0xd14070510270201090e101d0a0501050d02030319020118080417030f030a0e0a0206120702071a0a0513030618060b09040c0302040b220b01020c1e0607060e010203040b04 74
    0x1580340540c0c0300b40e0000f1700d91380060182c20503120701c80000c2107215900d41e040a010f013007002e2099002c0c09104809064456088070031007449401c4c01c0000c25541440440411803a90141c02581003031082c0040f100e0f09040c41c18460115940c070301c10a2518145021140b03481400303103081c5503503a414111001b19085c05a80c0e903c1d010f030300030021840300b850f000c8201c1c0d03840b80b8095000145001c44051560038040c1c0c019020354010300c0030032594400c201c3e40c10070b14083c0c403040e001c42d40c400781e60305802c1044401c2d04140351080382c4244180c4074803502900003072a20001c004850020313203403240e591008035035640013020a5841e2003604942007240520440b4800c96040707620980625103075450b601100000d00000313000395141c7c050303102207071180152141341a00c180900d00084141c1c903131200042012030b119038018465600c2c0100281002c01401741d000a90412951504003814203001190b0b201440490784140d8480c03e10b13500303040038070103076005520950b49617245040038102107203110740b05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 214703345 1250 214702095 214702151
    0x190306060f151d04020d240b09010f09050310090b0108160506070206120a0209010207060c02060d090515040809010806033d1406040c020601080d14070510 68
    0x14140900001e054402d2000c1003502d185800c0440980c00114490201000a02039802c240040b81c103044010064124200b09110754000e15407010071074030b03040c4a1003014440e0203500d4404208102c003551003100c0c86044001d4030b080071912160303601c0100f03180170001481d081c0c80980d01c03800d04080000541c29907004001800081040b007544c80c0c0000400c90440c8166403150800180600440d2281029160002c0c0b8225000c0305030310f0304290800c040d41c0126001d0340140160540450050300807000c0c800a0fa4006e4509410482000e030072038020302c8428000e8030103200300624540c0c100c2d01080060f100e40d1107003009684521500300090007141c006400c0500c260803401c586140c0810541d0b16248580400308644e01c52402d142c843d4008c40ca0080862850307604200d14070400a100304045401114151401c110640301c95034120384628082c09510f0031a0000b420715880d0520628020954042c8844510f18011603a035410381b078502030848000550361a44494102c2d60004404400e01c070800d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 214704595 1250 214703345 214703369
    0xf060501081606030911040c02070305060603030f0304060f02070f0302070608010b0705210c070311090a09020603010605071e030c031e0e090a0609020301030b011e03080307080604090219030606 85
    0x5220600018902ca40c041da00030141d4502c14403090101252008602140c068070400c4140c2c0140d0000b5128401c0d40000e0b20244240d20100e482c906000080f034007880c0540b218142581c89a80c0c50314050b001080500300d06c581c081c446100420000540841014880d80051906900c1c106000c0d00c021416448600040000c0c4040008520045070404400c11110900c608070a00c0c140b500c101c42c01640f1442480d03101e0144c0220801040700c611440c2c1040464403580c1503070b5240344080540c0c4004030000d41011003440100140c50140e00901200c0740b1805514004140440352603624541c0308005500246414046000307240c0c00900c0c0f44400c154242000c0d01140c2c00030006801028807030012401800342800040c40b03010541d006401034104504255980c0d6035a0800320580e02082c0100300481002c0910300f8000c0c28a45040401caa074084119401d6540303081068030882c01c006c0445070059211503800b401a80d81e80308900c2259800b5501d45045421410201c0480c0e816130400006001c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 214705845 1250 214704595 214704613
    0x60b040b041706061e1206090d180f03021003060302220b0d020303040510020f160e090c0a090c0e0a030b01090c0201140103020613090507050301091a01090e090309030a0f06050108 79
    0x2d030501d540a810101c1059005200c0040011030f103046c00070065001035008078004d1003030b556804034400a003080141c0e141c00040349158109002c0f0300e018840c110340016001d04c200b0042c00c002e82c000c9001d82842c01c0000d102e5560783c0108580601c9080785450300f80c02e40c0e40300300c0800e44601c80c15602d4482a100d5928404050713001c40d0340c074891130003050700c5102c020010014052003000030144400c420002d5401c500100a00c0608c08082401480303e09807140380000c03440e9500148180b0300b41c8000f054400034924080c80e01000f0329014042c3e20030080c03400e000247c10340760300702e444008501c2800380640541c0340004040840300d00c41c0e01c1c8011a4180740c640b80d050801045801c1c1520780444405580d40c15150700490240c6582e032000000300d0402013001200c642101c083d40c100c030030f000790a0001c0c1c2c47c01a22a150700c1010040300d07002c6221890103110624120149990080340001100d00e004240400207280c0b04050b82d040341e100f288024800100040c43c01052700500341040200b4040c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 214707095 1250 214705845 214705849
    0x10b010906031802120c1503010326041802220602100e0a080c0109021c0203190317040303062315091003110403060c17070504060507020f0301060b040b04170606 71
    0x122004001901c100d442031746840c0c654405000341d030804140240301c6007900c1c08160080000350800d22094526120301401d200b0707155109045400d801655900552400c5d0500d0101c901d151142c0b0b00c2034034100c4c0d00b4002c0e00202c04d10044c4040d08050030304580c1b800180303403040081c540300302441e581c5042c90614044401e0140d0006520713000380e910407100d5440c0c00d05031900500500395032801a40c0403600d00400040c0c842754803e16607d40c3d0095003a140b140c141c7d250030b030701d02c40544a001000156488441c949111440d140aa0494480d140220300c860369201021018030410b07203003084810540010017a04d18048006684082d4045903031418181000c1c00582d1031244991980300f451f864028036520b0788000801c40c0d01a5a111004025134640b4403401041040f000350704100040d00f03a0003049919002d241500d0403103909030340f091314015040d03092010141d040c4150035090741d02e8440100d80ca588880142001d81090288107848521b00540d0303280d4a2200102d0641c00c0e000441070040e69 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 214708345 1250 214707095 214707131
    0x5040b030a0f2604060f0804110f01020c0a090209010908070b0316050c0703200d0b22060e0c031002070c0605160c0b0d0f0b101110020705010b01090603 67
    0x19a8020603000b480120b1070600c8450b40390340f03107826404294a01590545265072201400545055035108030313840711000300a8a038400e080c1c6000e080b447c014a929003a41c0381205920014840600c10340d54801021030101d0002c040fa500410700194000c200b0a006591286158005094400c000c0c0101031034100081c03081d100c090172a0100103c2040c116041502070005ca41e0342d100c22a08940360142d4074107144441410500d5851481507519890b9481c03480d245d1595240c081d00800340c1001034855a203010440c4651480c6141200c0c00d84100401041892181c4000010350300003504103c00d2000c1010b080c944044548010284180b20b400b000c1036030707030400300300703681e083c1c14001d64030182120035061480802c4402403028440300e00210b0402c1e500b501410f25040240d00902180a0120104007580c00d654a0107820031642c09005034444c1c803a0400602504e000000d45a0020115131008240c0c1d02a41054449a4480585240950b0300014100c0205020700c1d04001c03030101001c4603603103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 214709595 1250 214708345 214708363
    0x1150e04080313081903050114100f030e06090a05070501050f0405040c030b0d1101110312060603040c0305160302130c08041b0506210105090712091b060809060105040b03 75
    0x101c004040005a0100144000000d055400c00980b5403500c442014607070060340a90b910b200028100400015211024486020000300051001e580418610811950113051014800030035171913010112440d81c0038490140105440805000c0f108140d0500e0b40c40d10701a5407085041003010403c01719112084401c0d03a040e20011a004280a541c01000300e000d404400302c1564000010b0418200300f08181107080d07244882a225004a6014080c0898413401040d00c0ca000d6030296100180b600c1c0b42200065601900c034004820000ea00c9032a4145000032030600c1d00d0400c02c0062090055162018900c40080040c4000b400080800180103004035000341c4010501400c800c0508119819080780d00301511014041e02c1d11241e203410510b505035042030409046612810004c00c290800e02d12045c803845e41d0380c481145400c14000290000d10302e1714410740c0d1010301c40030700620406401d880d4800400c115030380d5142ca82041c1103201e050142c107034007041c4139610380040f045690b1000b1a1070f0361 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 214710845 1250 214709595 214709603
    0x20a080301150c0c15080105101202070c0e0f0109050a02040f06050a200709060f05010c141f051503070e0109020d0608010905010c1706150c03090d120201150e04 71
    0xa030b814503054481d5080084000c1c06052080d20214000c2e40442d00d14204000b0f0343d07105015640c4c3c80003030181600c0760040e13000c00208207141000e81811640c00800c52030703110713085403a002c960b200c4010354610001c5d2543c002840f030400042040000c24001c1d25040348000d0340031440c140ca800410030072101d0034803500060040214000b003015008401200341e14114141d030002101e0107002e800d864141502030340e62682e10301040416411144180341040c0d950603110411018100e0300c50b01464850390b40507441034410515814100140c440c8140030f140490900440c5c9030415401804010601e0448603010781e21407034080022181c10746081c3c2c1110301c50301e00145e552141240083c044c00480d08951800c0d803c0066030002c1000550103840003a900380d03034103100300130205c0f565440c01c44252a5198071901c106000007590058a0050001000c0481101c0c41d001401000c50289801d15038192041c900c0c4104102e6141e40a006a00302d034164100d0307e544050905822000b01d160151000d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 214712095 1250 214710845 214710869
    0x20108010902032206140f07020f120915160503130e0709060302091201090f030908060705040b180319170406020613050f060405100b010f0f0c2d050c01020a080301 72
    0x20092141590100500c80c201c8690346d5020300d40300041c0c040c0381400769401401442002ca80b00014030011954298000ca040081450074803c40100a03502c03024210201400d80100801d03e205001b0300d64100310940f251000d9601e03000300d00d2403848843e84940c007410301c01c0701d10010402202d600524200950351103060041c2c540040740d0218070460920000d081c0076620b09000c0c0c0061081d280401c01e2002e04c0395903040c2003a81c0760f5060319141e403000e0f210300d808944180400d000312800c01001c1e02e081000002107081d10b0301481c0000c6d1511b6400541c410324616203034500001d01c0002c2800032203014190075200d11301498288020343e1a10014140b80350340d8012460001040740500c400a40050300c24101d40c40c504050503c65103c900d100640c421403468800b00390b0480d4018040285031b07200c961110311454520080540c0d484501108c122810a040590060610030850b030400c04d50550007002000d0940c40e00d0f0561401e01c1c00740380c203815580140d12a40001c2c1c803500490307043d103800308955 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 214713345 1250 214712095 214712161
    0xe1302070b1306020c0102040b0304050d0e0102120304060f1a01030b040510090906060305060c0a02060106080f01030308090f0115030201140702060306060d1b05180909030415090b0703090302010801090203 90
    0x10f2009000c3c403a2200c25075400001c0c00100300181001850203203000c1c609035071055448010503207042c0c0000b102103025070400848402c41c1d1401d42c001c2d43d0700600a100c0440d03208810b0400001f26044040c450707946118400e2101c0f402c1d40c2c5442082d240c010140c500704181e0400080f06040c0200750b204d03403034006495078041400c001c41904a007009541c03010071140a81041110f00705141c1000702c132100144221000014064800e0702e00c140100203042c80300000341d0a5880c115080030008042c50042d124110b000d08030f40000744502c0c010000303400d003000111410f51000400d1249424035800c1c040c001401130f4400360391958110f9070094000c0360815a82d0200c050320a01030400d00f501d01c00c51001c4000c2c030030b401c40d400000408028441710400d9101d5100c101c01c03c9000c00068804581c070354000e12040c00304850310001c621a800d990704182188941d1900700380007650146404600240250508004650f049541180034050a0000b98110b28280031001400441c540001a0a801d12000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 214714595 1250 214713345 214713353
    0xf05030612030f04080102030105011404150f03091406091005060a06050a120504030c020f0405070e1905060c1005090d020c0607020d0605040b180133050306070e1302070b13 76
    0x319451014144043e40d21965584c1e0010b000303410910a05001c6013054626081da11060300071101074440050305c0661140d000c24040b1040e880d40d180000504d60f8910100d0b020a0064a00f60700402d100e800070b02861610703150081c20304140300e50350401503080605100041e5200c030704540a5034136a24085442c5c01500c881128031510014200803e6880e0906100c2450360200c0a04010742c001e0700e5000001140e042400304680086504100180180140c2046841c04601408055040500d1841e03000c0e00c84000801d66404100040d229500c10b5611010405c024021240c0c002c205001030220749440150280d202c0340e505500c0b40c0300d200001450381c06c554803a1414001c81d60032038030401c102e20345490038542510007940d903d01b8011205880e100c0d0020140108204250104201d100111210100130a072040106080110350241c0d500819179403000c0000300d11901d96940d90f03071442c0c111001170007040d0500c600040d0140d4010001103004c1402030001030740000380e4084e480048981410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 214715845 1250 214714595 214714597
    0x306011205011506020a030e01052a01060906140a050108010308040e041b0b070302060906061e061905030a050907030201080106110a020a090204090f09051903020a050601240f0503061203 82
    0x2100328286140f00c98042841680021480000d0380b0079103070304400301c440d44010344d01d900070340c0346030805c420f040c20070900d51a6070b104101d07200301300000003c241640c5a04c0340605503041500121030020b804101d103202e0f0310b000700300c08004080c2804c1180c41541140c0701e600c294031407402899003580511001c5010130100e282040880101c5101030440203407610100091903125140c01d40040c840d20010610b05038000c12494041e06006284860345c81c03020340c04fc4114803120022a5105d001441921841e01041c00009501f010723550391655240350540d03104003122000740c84a02c05900c10309040c401071b40c2200d242e5064800341d0414503603200c110340c100c3c0d14007a404c010094000c2089200002e0201c5503070098819140c3d02c80d010701c403d0840b030141e2011074203a8200500240d01401c03400310301100070300848840c07900070b2054a007900181c2e00d0b001e00d00803080e44801941050706906000d03940300c02c0700e000480c0180c1d113030904405030a002c0083c52400007420541c480c0469120100c3d48900c100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 214717095 1250 214715845 214715861
    0x5060f0c1204170f060711160b190306030b07030e0c0a0f14222003010f140301092006070501050f0a05011d010b250f030f0509030601120501 62
    0x10308440e40041615040d507000c0d0850b204125400ca1202c9125038443c1e8082801020861050010030036992000401c46240d24900c0d0b0510b024080e482d006c49004d01d5070104034000d4816001c00c19030720924070000003203503550035080108061505c0d00034400076422282c2d81d46c00120910740410141c060580039810f00491034905030340b000d000c50b070003d80a182903102d10211031034041140324001c2c001082c800340d603521100017030345041400048609020541d00c007001c0d49a41c03865500c200c000344000d103d00d5078002c7c0c000a1010500f268104590011180c00199800081c1e0083c801400542c0d2031403140c070801d405040041d58140d49602a07510b59600b0340380345c03130340160080c04281080c507000c0384420015112413072420305000010402084a08402e503040c0383c00d401c1c00d4016132910301000e03642c0e0440c1c4102103880700c0c84c41444841103940e000303158074540901404105aa45881c1c003a002e0030020352100103100050000600603580072406a04440803180010b0084500e0310b03149004219213 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 214718345 1250 214717095 214717117
    0x6090608061c0f02030f0d09030b0a06050d0c03060c0c03050d0506040f090b2d0103200604090b03010f180f050c040e1c09151b0501020c150f0c0405060f 67
    0x54142c4006104140403801507490003501030f00d4203494845e0703426840310401c0c00c00001081c240507080000811101144d944002402c2c0b0004000351944002180c1904810091350201081c0e4814004c0c82128400c281a124240c01c04904008843c2c0d0007a2030b502a41c003a440c9000d0342c1740000f03442600c86400103a40e007441c8034010881402c00346400d00c45400281c61060f080381c0403400b41c031425521907502080e84000300c103810100d40c1c40c56850090300350060b202c001c0d0701e191007400d204030340d120b00007d040a0800448086184400355081c1400c4504e2491441251802c1052180c01208044401d246113900089218150441414410f2902403045400340c1c005140040f01d005900d8041040200e56001d07142c400d01d00e2070b040c1403c1358131211500900201d0310610109510560240d2401d000b02300f280d000b906040e00b491348030300e42280c101c4094400e0a0b0401c091a80c06100e295050b1f603805101c0c0c0c0c0380c401450506d0028400980101d028a90003460300245030000c2c1480349043c5d50400c001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214719595 1250 214718345 214718389
    0xd02030709090b06060a05030c07060b0d12020f060420060708040b0301050a0614090103090515010b0c010b030304080d0318080c07090b030a030c24020c010b0111070609060806 77
    0x81c885688004005000082d901c1c48003010214400b0f250500850b41c1c5c0016940c0d48505680310145000b40e146e03c5a07004880c2d250b902d03030401056441e503900010700c1a00814800ea500f25405001a01b40315184824401c2a00400100000288203c0d4650303441ea00300c0442010081198001c034185100310f00d009050b0f1003011034000343c02182e90000318161541a541c80003030a40e01c41060b03c0408081c20241b1100006010301e40155210ba8044c480d080d009004490100000303405d520503c51080c0c01081403088000b07480e8410000c24000d4071f4203194190015450603142c0b81c6115142d80c0003084810800d80c9030300182804004c1d61415208545d000f003c80ba07900d141c1038034002ea88003154800c009909050a4005010789404900c146240340c15480d00607034075030555070f100d64150650800901c0340500c18840148072281e8030240c042138400500004804803042c001400b240a4150511115806000103010469006e04400100c0e01c86080c06001a140c00c00007400742e0029880c00700102507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214720845 1250 214719595 214719599
    0x9060c1c020d09140a030c06020a050d050405010501030507080d0818120408100507111903031e1401080a030f180e0c07060501051221120f04033207020d020307 70
    0xd000d9000d404203a10809441c0130380000f1049498a0300540600038020904200074040072035501d80041c401c1d00c80a2901c2850940710740c00c18022180e068601f42d070960f550340018420000d08200c058040c0c41c40d40c0051801c0078801600400c0c124006107150008140c45440150094081040c0c0020111030721401c0e46454507050ba0301d43d81d0340840300707500089050002140d4030901804034403070101da00780040e1a801c407403003005a60143d6007440884c10180d55003c0b03480e40302c1c156122565210000440411550304c89001101c08003410b821100c0700b90000c041d0100004e4101000c0c00c0c002d070131820704804003208415034005000d21580801c4002101004111248540310001e0500d58400d00c01040b6030398803501800f560400c820500b90381d40e480034115030003490012108101728807008482c3e83c504640b03001c02c007425000940e02c00d0213828040b01800201070f00101c5004110030707403401030743d0000c00344060401c1c050307541c5101c13420003800002d0350410340d125800c080700c0c115000390441c0c1041c0d07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214722095 1250 214720845 214720867
    0xf0103020c0c100f0210060f0b0309070e090a050105061c140703020a06030209041a06041e0305120301150305040b01150c060606110c0a0803030c0f04030609110901090509060c1c02 79
    0x44c1136016004018094100c04645011541c440c1900350f480c1107110074145400c0504820080e840946010014400c981000444030710301c105062140541c0c0e0050400c9400d03e24020342035034005801c1c10301c5400c0e1003a06c454001c9420014000c8660060461075114000300f01490a1250541019401c990804804502d150f0150020807004c1c00550301000b10315001e18900442d8612104101e900c0182000208894545c20600c035140143c40f003005100540d80355101407a00b0031401c001e0590900210040044080c101c0c54030146c0003441c01c0c144110b28280d80e89046ca0b007014020140d000e015100e90b01c801d00d102c0e2207403400740c80c0e1003441040f190303803921405003000d1400c00104026114070303120003489040034800c6404442c0c4c1a03000f141141c0302c9100440d490b802030f41800459110600000021500600440013442c0c02040d0103003161720f0b02d00a010104d03005030040701200341404140305603444006101d03903100d5400e1110b00d4131410000d104e0140707000303006642d4494a00120302481d180b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214723345 1250 214722095 214722107
    0x41d03070318080a1a0c0c010e0106060315120b0a0b030d03140117030f0912060703020a030501170312061309030905040510060f0c0302100504060203090105060f0f0103020c0c10 78
    0x211207510301d1241e0096540c002659107500c58a4010558800790355517a5080c01001262074200d2200c1d01800e081860b481c00007400c659071402036280e0750b07450b183c0c00c000442d0544602161a01c0c9401d0fa00e40fa9400c020780b103507584102d00e1000f0408003200d4001011044150301c070300c01a103c002c00b9580044400e64008000d805000484044050302d0400000c41c1d19510003190b920102c2800035504010920701c401c3d4a642124079a2904008080d01e100040d020a00140d4481da616480060700c0d044290b20083c00c640058209004d800111084e070596202c00005540351400403075180c181d01c0e56000d020030540c00c217080d034000000e0b08080c582010140c124448e0001c1c0c94050f101000303982d58001515405015a11407400400c0b81c1d4488407523060301c00c40c4005001d034000e00458011291802e01e103811940101d40c1960b1180e404030501040090a0207100d4011204030f400c0200239004500094075a03000c4400c0f14141680081c80e50004074040c401d1400f52000203000400d042c505003005800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214724595 1250 214723345 214723367
    0x120a0b1b040b09030609030c190203070b0a0807080a14011e03060203010906061202030403140d0e031602040c0e0108070e040b030a0b0f0f07050301050d03020124061103070f02041d030703 82
    0x11a01503880018095503000094034900d440d424010003400b240049c00080e80002501d050382c05000b40c0d00c0120f1400c0c00c030300007000e0503811591001028549450018403240e07024180000303841c1420302d000b02c075011540c0f440303042d2210050061791a80318010784007182a0254401040d040c000700001910008682c003840840b4001e441e044441010345e6003007812071200f149e0050220300c002d900720003800e031103070060300450600d030300300041e05407441c0c8080d441c60704455103505800c0d002c3c050140c00c50030070303002e1044c0001c024104030074851805030004c0d09031a00200790f1820080f1198501170a6600c0341c200c61603005010b030583d44100064100544803c42c100d0345040f9150240d80410806100c0c420308030b03c14042c60351303981c1c11a420001002814034040c102075045640359100b071200000146450000423941036200c1b41c16a00e0304074042d110f800c0c0c1d009442a903400034002c0c80c0110380148151550326504450010b94245110048074450002e03ca00804030310010508604241e007120700e10701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214725845 1250 214724595 214724599
    0x1020c0d2a0215090625150c080c0a0909050906011e0305100525020f0106090e030712180e0f060a05010f030506040e03210105120a0b1b040b09 63
    0x2a484000d0450761070015140d0038029049080c1100300110003103040041c0501500050945141032070110b6002c1c0c903104042c2250502c080c00c0c104007020042d40715039450f9202010350087c4803c16104d400500041c400400360440300d00001030820b005480b5800c50009403180007010020b50409003141a50f0b290309000d000d10813003e03102100d0541c06100420b40440740c3c000300038610f5240c4400c0c01c1c006800d01800d00c540c1c0e00e28a0580c480400c0c0b15440c0d0341051040c0ea4001c00030301c121100c0c0f841c00c0d40d0003503011102032440c20b100c0310a2840080121100741d034103c402c40c040329200001c200c8003912161890215010000004520603000c006007030b020350481900c0c00b8540c4c840c241048000c0b01030b4883c050105814240c02405240a0b400c003580c4004001d000181c1c005220388040c0c256804042080109a0b8619108241e04002d000d66809410103986007002000c5140c1d071180d4500a020020f45980050030016181e04034100a599400105108031034032a550f030641c40c4c1498000045041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214727095 1250 214725845 214725887
    0x5030d020d0501140a080a0f1106030a090b0a0b03190c0b031003141f0e010b060307020a060e0d050a11070f03060204090506100905130b030607020706080f01062001020c0d 75
    0x1011307900e0041089402d44421138040d1134110482c0d90341800f100c840070307800c5400e04035144030444c82d40e4903003001d9845007034080c0002c1192901c5150601c0400c00c01880c403420649042d80c0307514151400101b0049401c00104001562800c034107090480c1c2c60554410311101000204011003500c161200204891040004900c1c0580049580d525000400070341140c24018542c0e6460400150300100c40d0032120030700000c1c001c03000b40040b5480c0d5000b20307910b4001d80d0048800b0400c105075480f40086002000c6c0191619404141c0010301074810b103807600003000700b103146a01101409002500040030317520340c00c40b0500d0341e330714084005c1c7d08980b0400180b540740c034002540504044a803c80c203d4291b9507a0054641000e0810100d0400385640d10800c6594507407058880d20304000740340c040d440742d4008200280c5000c500034400b07a00204026884c000f1200100714054101d614410032084900d001030500a05603031040c020b006140f8010034511070001041c807026005500d2500c04800c072900c0c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214728345 1250 214727095 214727129
    0x21501060e0a0603050c0a0c0602090d080307090b09060301060503060111010911010324150e090109090204061a0a0309030c0b040b01030507060e010c14010b090a0b04061203020c040905030d020d0501 87
    0x81d811210100d41802c2210010001d400c01e441c2324a0441c0b5000e446620300508180c3c0748004510ba03000c14600840300841d0000500900c2c42d0062205c00080010340912440c011214000c1180c900042c032034007041c0f0001201281840c1e0145c94801c0044021100070460303c2d600d03040045001c001e8100c00ca000c2450404070400300b41e20581c0c106000d40c000e1700c3d4004420b180200703051804055440c40410805003008202c080da0310401014000d200c107040c08102054140100800c136011940070356401c038202600d42d81400320038001c1e28020f800500300083c988500b828159103a2001d007800400842c5d40504000400c01100786141c103890290741199500b5840301c500340c90241c7c011281c980071170303205155800020400192400000c3c6143d0002c0b4007805008086000c00c1403e82d0035880e4180c9603800c402c624106446040018030402e075140d118101181c8010f03441c1c1f414050214080c41d20b604954007800410411140340b034058080c215615002098010002c000a00810041c0e020990720 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214729595 1250 214728345 214728347
    0x703020a0f051213050f010e1f0504030f0509041b0c050708190803152d010914040e07180e01110903061f080703031d120d0f021501060e0a06 62
    0x2e64501e01036840208005403541031400c0d011942d40d44040302d40c0e1064041c8801c181c14207000340c482c0501c0d0b40c001000e504103040507005410300d00e40840e94209e40342c842041b0210b42d0080384400c0c00b94240c140f45540e040748102242c06040ba03000e841c02c11840031030132000141e0b40000c0300c4812a020304184e450468981c0c0c80540c8401c201848280303401c1d81601030714040380b0b066004580001804545100090958010811000100004581c83c1070403003e42460100d0034204804418000d10b0b000d040c0d1400c3c40710401b94503082c84180d42c001e590b21070056440400c1080700401070100c2c40011107071000f150140750041c140d6020711842a500b0805034454801e168800d03116040c3c8002c011b4107242c0c1e5140c0b403040722908080d850700c0346800800c0000072070040910071034004d1802655022042caa0005204060b50411090f4034050744c8441c8590090b860003040b01c0700701a1303051030048088003900358101e1400f0b00c0c0e42c2000301d20384c0078034000080180e00190100d00c50790096034600091561110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214730845 1250 214729595 214729597
    0x203041d0f0f161d09090601030302070905160e030a0204110c0d2604020a030b0901201e0c1f0b040b01050c031905040305030a0801140303161b0e0703020a0f05 70
    0x1d01c401000d480c43d46082c055801007651130380780604088a05545200c00c40000c407400801d4904281c260403403401402070660600044001d0b000c00c13007091002d400c100c802200360020312a000030400c032000580f001c0a99050005071240c0da0000d000303224298071110513048a42c080c0941c05c00500c81d4009a00119001d080c202c0d6081900340102d8003046440e861014003040d00400803a0302902758007002c00060400d60a540c0242c0002e0000248051803080100340c4407403040100780500e0301404840021904040343c2d04051200f540029241c007078a40f0312510307007440651000347c1c1d04864100f4201700c2505901c0403003001e400315014840d003074503400151070300d21690301c01c0d0300e203500200708505000c6c802c00490080c004281c50031610741590707900e40604603005914410009941e1900401c03855113043c1d0300703107450b6000300c0c040d601c3c2c50780c0c1201d00155042000001030244070850002d140daa40c001e241003004045a491411503849d000c00c0050082d44a192040040792200d0309040250744a10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214732095 1250 214730845 214730851
    0x5101e09020a03020d080c070902090306010501030902061c020d1d01140705041205070302060304030215070203040503100506060c0102040f030606060504050f1309080a091701200a0203041d0f0f 85
    0x74042c0120b4038155000c0c8001174040080680f42c80c00e00308510a0080410440f07503000344010000140c0310003660040604240042e80319604250910003020007680c0d80b041200c1a1002c40c40c90301c1445501c00c00a100030740280e1000d1030f5800d00d4004520300031084180c0c513081815051000300202401c40944179425542aa90383e0000b0700180300c01d10001d0321200003008880c0c00f4004030746540e9681d40c001806940101c03400c0f40146c100310b00340001444404030894010000c1c4c00550f04180c103120203e0f0340d821440d041d8840d560f88400c08a40151215000c403281b054204000355038940c0c64883d07505031840b1300e100c11030740c0c103260500c0003540f544941c05031025918010311886400c14010208000201c107002d0a1b110070b9078a60884002483c08001440004026160204600d140644d203044e5412140582c030074590402030074608400886024007090544454443c0c2c40b0044140c089255000300d410075070300602141c512500440c0a14605072241d045000e09203d80d80d5040c061020801040e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214733345 1250 214732095 214732099
    0x20103062103050705070b070c031b0302090a200a030203100e070e0f031f0c020706030e0304060c050a060f0203060f031f02091306030f0209090d020607120905101e0902 74
    0x803041e290010340300c0d10042000500401c01c451030103448105501c2146c3c000d600071515000407080800810010b1518191101042e400c0002e080e40b0b15004209160401052050f126070340f00e9281701006c1d80c4004100e901c01030075011540300c0001c0c0101800075030003648c4d2148903104188002506101030501c0c14811251580c2c0d040c0501500020300000115000700158107014404c403590011032204082c140321110001e000c100c030440d840c006801c214080e04144101070411000014090300002111704440d6a0f01d0710181c052403d08105043c500141c2008103c00d04001489034040c02c185c001d0f43c00707050119459010510540109595000c84d51541d040040850740d1640c0d1110681d4091b16004001516601c114035002c10400c003103540c41d402c125440c40700411450254100011101e9010101000030244801c94060203036440b000100441e0402c241c4d20404035244105410488103958003074100e41c00481c408000501401c00115040c0c2c16a03201e05502c0440f00440c000c184c3c0d200c1d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214734595 1250 214733345 214733399
    0x901020c090c07060903052b060807031707020a05090a05090c0109030f0b060a08010c020a050c01051e030c13060c03020606091608040807020603010f030c140603010510020a06051302010306 83
    0x213542c81d070b03000e04103086044e8107012060003104038045500e010641c2d0115807140785512810803010a4040b6030f519005100740340c1c0542d1060000030000144405c45505001040791202400d100295a010700d980005410510786001d110350181c0f250803ca001c0c603210700942e6a1524044e00440300d081d0b0743d10003d0404030b03102c00c110000c85c411214068118030301510740300a0076100c611907403d50308910031350f400581c8110a0401800300610024411840900e841480d01e100100369420521201d044956290380010125242d1f03e1800111202040c9203680c0d05a5240c0e560400341c000400b07031805401600410380020b415240c40d0f054544503817020301e2905a0400c0b000001c540b650300050040340c02510801080d40940c0c0e401010314001d00602e012000362070305619200b6540d203051761000000c0901800381c142c02e56035200075a41964015038803402080c1711010128588550503001030031162801041c003c000a1020031084464000c0e02c05102882e500c20346400b01303411100005060902c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214735845 1250 214734595 214734607
    0xf09010807030e0d110714060702061c05040c0305060f16143901090b0402010f030b151b070e01051c0c0b0a030b0402130e0a02040e0c0901020c090c 65
    0x805004000c0d00500780c2c0c81e0014a080410004034a4440030080050103d900c1c3c84000e40c46140c00c004c0c400c06000d00250240c8a901c4a00200c2c107103000700d0100030701c03561000c035900e1441c00c0440044403007003812203014030103810541014600c00543e8041910703103008840005201c1c44034000b206000e980103020040507a030b40035204545458142e10b183c0d0b05884100003410071210607400d04c220714200091f0003100440c2051802031140d140c00326011240c0d042504245c04252040c0090341d11640a0030701d06588070284008400411082e8140340d403040191001e4003028032020050038402a86030645e0b8542800f00030381a41d104158891250403550740801441141004004691005810075000d170019141d039507910404c08454104241166004c1885046550700d4080d403425454180d504516048040d850001e5000c4640191540407154030042004e00c0000d40c100c600a0808200b90354031418800054942c42e803007060700e2030051094104802c43c82ca00031104500400b0103d8039549451 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214737095 1250 214735845 214735847
    0x5030a0f06020c03040b070c050103051003150203060a050301020d0c090f030b04120c0b041a0c0f0915040f09020306041d100510170604020909010605010905010c080d151a0f0901 78
    0xd84008003921180c081808005025a44140980580c038070908c980712000d402e14000604a6100a245003c458446a81080407511004038a408102080d5001d43d4a0303403003d0104550110b01c2d03111540dd0342c4002002c1e407025030b540d0310107202200151383d104030f0980e076280303948081c0009000c040c0c01000b44802040026500c001d82150304c48403401c007580985215100e02c1c8180c0012a401e660402e42445441003204030300580c0d681c4031803100c00450402c11003a403820380c079000f600b19850242a60510f614502039410040e6002041080c045060340b40e00c43c03017101e001e9041959070310b000e503081c42800e4681c441c2d402a8001c0b2030442000405501c0310040419020700405405070880516000c4080b8500c01032000c80c9401d1508100107001904042c8180000214020008080f81c0d00d000014071081c1e1740000200100d81342482c01205060702130510542031720074000145c08051a0035260030000029001010841c0d061406c80c04015070030080144080c443ca104194440c88100880f1110b9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214738345 1250 214737095 214737097
    0x31509050c04062718050714180d020a08010b1f1b030302070203060f01030b090c100e01021c0806010f0315170a051f06090e0703030809250303030605030a0f0602 71
    0xa4451300c806078096481c1500000140c01a8122840041080c00c1c0c030034404209001d215004601403614003014095105a4006030103a040c0b0b903207003000c455040180b02d5940b00891001260010800e05149998101c414024070080c68954010200c0100c9100101d9500f24070016944064503280c107200c04403020302c00ca4940059046051603400c1c030045001d61030402c00d45202e10366104106040c1c0d411814030101c140c00c01854030141b98803210581c102521045820031030320000c2d052452500a654006070b00389440d001002000300c1c0c1003c0b002030340741d5019042500504d404e8a980c0d1100c030b6244001c4081d10342101c1c03e00b03140c0c81011800c0145495aa61243c0d13641102400d031181c80c59550744260070413a001c2d0000404100302e2600d402c82d410f2030f1040c140244913407602006811180d9612a441d1f416500c4003506002c940d50005e41c2402d02807018030721641c2038108c4403043c00f8501600060302e50040c0000c0e00041e01c2c04101140303d04000402c059583e4001c00c8180301c0c0b079103550702c40e80a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214739595 1250 214738345 214738367
    0xe0d060b0a090f050411120a0b06120f1c0c080412080702100806090105040606120507051201060906020709020309061305011e050a0c030902060d0f0908030403031509050c0406 77
    0x201050000081040c001d100da0003141c00903e070045440e041c00d05003e050321030101d00051040048602c0e00c1c600d1800003450650990303224000001a60b22640021180854008509010301403c1402c00740b00101041c3d48030a945d00381244241c0180030b942c101c81402c3c822200034a5400c04001c1400a08a5800d42c0c490552103141140d14111213940440c0c000c004103036031140410020000d0040615141110f07501510b400d407010003440d894501d0041422482c03144100200d0764640100710042d1259040324403045120a003c0040d5a4514000380300c0085c0d0300c62a40140904000402c082256008484c0520002c07001003e15442d2003118010901c7c426204443c1d665841d400304241c0c04041500c45040c02d019440003031145090f1000505850581c00c45004140c50000700c0390060b541d443c01d9030445030f4403660014210300010000e40c01040e0042d0007400d2084084100820194160006041815643c0c0984082680c5141030416030b00c1c00c2e1102907080b00140403c0c003440e4894114804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214740845 1250 214739595 214739599
    0x80c10050702191b062c030d0c0f02040204030309180b010e010f0908010f020901021507091206140a1d01060b030c0a02120d0c1407110409080910020309040b010e0d060b 74
    0x21600d8034800da0745013660307042d4001000308202c0c0c00780070310300505d02108160360b240440e4040205140030000984546d08200c100d02485842107c14003400b4188150310046580030700308642d0303243c0720700b400f0344058010311551007400309072202d860052580d0b00486984407010b84420358618901401960740c500500110801c000b410480050800024002c0c4040d4411401005907540071007000241401c044241d9405000440001c1c891810350050320841115100403415401141518140c006000158441000355107000103012500d002944081042001e4050020100c3c3e00ba032031030b42c241e8100e8803036500594428070005149030181002401803908603c155000e001d8600f150a1580d0041540c40086680c3c607954209181c1e00000113080c4c08612031f840908060361603850130045000c10807031078041c68440d000300040084803011365444000040500082d513408820080d42c0784c00a000d545d114500f0900c20b640d140d40280300309055840f0203069102c040446d522070201410340100c40c59 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214742095 1250 214740845 214740863
    0x311040f09030801060f0207030b070804030912032006040b0601050c101e0c050f0403020f0103111b0105060103060b120414030f04060305060604121419080c1005070219 74
    0x251181400d100345090079110751240380155040c600014089025035010009660040c1800d0000c1030051080c1540038a40d03141401841e0313541c0c0741c1140d8140550b030002c0c11901c01106003d0405070850080070400068a610a400d104541031060f0740d020300340d03005051140351501241855200b10010401caa038850100c41c403241d13807001c00004860004a1034501c0c5402c48017041e005d00024080c0f00d1441545203005420500c0700c0d03000020354444c1d4403009110701400205040715902175003104c244514000b01c019120810000300a03681414410450040c0d4030340000102c01d0740c000d1168400ba1000a107503107003441c005121030085008c018100341c420311a40039035010003003c108001d000b02d48445d05000c3d110340c42d20002a00781c0300080c01c070610801c0144814410f02040d04040b034001c5404c00403516040f40740f82d55940c284145400258800710f10f40c25400c040c80031880c014024041c056049510000c0400c82010841d101550301c0340058000c4500401111722a51800300d1007800f8000403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214743345 1250 214742095 214742111
    0xf0302210c040510030608160e07110a06020c01090c0506040803220e07020f062410030f33050904170d0f0605180c0307050c01060f060216060e0307031104 68
    0x58828010013040c0e800194460505000310b00c010701408000540d9440005001030512180c030000f2000208101c0400203000c500a11341c4000300403865901d9000b400456523081c420044178043d05c0c070781c00c041d0b41e81c42e419000003c560820000b100c0890344030001450030015005030b04440d01e04001001c4290821820703022621060041da41070198010390000d01060407443c10703103030409400a00c854042510030200c0041c00310401101101014215040c00c40030b2405042607004281c4d03140000303410340c1382c2650000003071014038180b40694448808071241c582c641240300c4500b07885010740d5810103495000300d4002a641d0400340c00d8050100802810010f0030b13021001140d1510040195113600e41004018a0800c100d1a0300a0341d1011070070f001c0c91400428101891102500f540c0c20083d0000340034206042c00e6101d10081c144503080d640724140d079100025502d441ca1203161201040300d01d0001503c5005d0714006e030880c00041c1c080c0034081e1440e11092855200b48189907000b6460b4444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214744595 1250 214743345 214743349
    0x110c07080109020a1509120503132601151415070803010312030209010e0f0102071205011505100906050d0216050a031137020315070f0302210c0405 65
    0x102400303802000e00000719041140108000040c0726440006010a503080640620350301003209400e80c0c091484d5a440c4e04110701d81185141300c2e01c4030780005100c00c40400304d003048000f0161110000c00c503640c07410081004d0071240c01c0303e02d07207840b4010303e075040d09080100c002780b100c4445491000404501c0c0e04044903034a04400d50052100700c1e8200c4d00000103100300950580141d001c54182d00e021401c0503040000a09502d0401c80c03218420154486412190380c801c100d01030103450b024540c0c0c1000b60961034070390b01900010b2410f03501c070a040705002c2018104500c01e00e41d41b01266a418074564685001614240d00036400102420380030050130101341c002040c20500140b18100824a500c0d990800620824206415942a40060030550b498003000004c0404c2e2400740c40f50200c0045031341840b0003550540500c02501030180c21608182102c12050b103078414011a21110016078070042d048080b07210f5203c500c917010054904001c82600240049a0f2210a078036000d0701d09078031140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214745845 1250 214744595 214744603
    0xe04050708061317070206181504080309040f0e030a050c010b0907050a030c0e01170903070b040f030908030f071e150e010b04060e0103021309020d030e03210d110c 72
    0x5503640098010f00c0824082000310b81c1d51503680795400155034100a1030f44d00144480c891882240108101003280f10390540c2c2e8035500103104501d0b10241962259a041a961a504007680044c803a0707107468050b03a0021800e00901820b0700c03052003d0740c60252581810381c0eaa810002c1c40707050642d650207000110f0380b40c5201d034030f008140c0342d00c8040e2140d40e01c3c44020184c0b1a1824a40d040103058096484641d03004003040d2070f0030321000f0816211755035204000307207140030303004015282400e46401e0005000b00c0d480014601030199440c1c08030381d91945440342c1c1d00d00c900c8119040494040200002113020702c4450300c18007414031504c84c2c01d07140303989900c940c80080704080302500350b541e610030126920922076000e0380308084d282805076a143c4440b0524100052001070301070140c0c0c010105d05e04030740741d04c80403c09500825109a140e16818024061001510614002d2240300280700d0f0000007100c6e2421458890500c161411010203030550241421740c04600c1000750601000340c0e2900280 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214747095 1250 214745845 214745851
    0x10020a0f08030f070906020601061b0203070e010e0903041a0309010b12161202030307021002190c06090905040b01060f0e090a1a0a060509010f050f0309060105040f020408070e0405070806 82
    0x540c0d038a904041c03108068180c3c1c00750820061204803c001c014040d000715007203044540c2814030051600c014420160004881040290316014070780c00824807003650b02c841410798505450321a15543c903aa13503555a03104601910003141c003052101440098800021540006c0b4480003082c0e148038800461603006901e205285180c10000d212070603a0820401b41d402010f98921518070a0700716008030784c0b41e01c070302c80f0041c0c0241c03000c0c046598980c0c001c00018071030700d8043e090440ca00554ac00c004076940078031f001d4040060f400b40d80c0040c40d480ea034040d40c0c0c0241d4200400a2981c1d103080f6091b00c401c41c00715016000e10041401c042c02540d00c268410b0300c141d00200010828107003000e0490503100480424a10407240400c05200070f903440010b13110425030038208100c2d070a40e005800c1d01e00f4011604200c1d2003200010400c250444040354090480b0810380d400d000da0080c0c2181c42080c0d004030f0040503101d5204020030010b002c4d01c0081c440e000b50280301a2002140c43e80f1045041440803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214748201 1106 214747095 214747103
    0x20606100212120417040b19050301051c0c1707050f060a0f08061c15050a021603030b060f1207020c0102060f0c0912030c010b0a05030303130210020a0f 67
    0x81117a074101d1030100756409071203690755a02c00310b0940c040700c070403140d000d400560504410f00032416030b81652001022000e4514400d015007446081c9a10240e50b44414100000350314120030856510541c101400342c0045410301080c000b00600720300e4018022002001407441c0580d1015486000c00c1301d500d8622a69229000090720b039406003100140b00742281c01401d4104031009100d5174503024268020b0000e540c8540c1d4200881c010035201d40711101e03500b05e0100c0028802c1c0d00008500c0380040c078850a0006404006042d07400c001c10240d80c0d1000c030414007030969010003001e40402000d00c01080f00389411040140102c00150ad0f90041241c0465100c8140d501d8450011001900804407500d030720300300c0c0300580a0060344411500440151501041600f4044104c910485007454186405071580d170a2141c2200e200b46507204600444441c0400074080c00272001070107000b = true := by decide +kernel

theorem cover : BRFrame.Cov 214568345 214748201 := by
  have h0 := BRFrame.cov_init 214568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214568345 ≤ n) (h2 : n < 214748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
