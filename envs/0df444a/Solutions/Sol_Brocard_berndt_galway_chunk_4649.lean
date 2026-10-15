-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4649
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:17:39.908193+00:00
-- url     : https://prove2.me/submissions/5c391713-3a5f-4b23-8beb-d153e50316db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835971223 ≤ n < 836151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835972473 1250 835971223 835971259
    0xf3007021f051e070309030308060414010e0f0f10120305191e050408120a0e0a121709030a12090f090b040b030a03020d2123010b180f 59
    0xa00014035981e11490758815404100c8000c00c00fa1000500140343c0410401000036405240001100ea02d4100b5031500d03101c0307500050150034190702e02130b505603803140000b5440d400a07190f81d0243e01c1d003901207040c68035017540000c0c41c501c007181c400c0460010400200000e800700007012201e14040c2c502203040840c86880ba1403220484940341000400c08502c401c4c002c0044d0002c100100e906042a0b40b52134600030610340c440c0188214002c02c0c400101d0903607031039800707402c12402c4075900400e0400003070b407100c3d100b5000c184080800d440e45a03c0b081c1c4442d604071a501103030010f802c0140101841c11449d580c0c040d07501c010a100500b0001c01210016025070034006034000342004400204407403e403441404222040120018803c0d4824403060b408039401141d28803212000341740110000c00000b034095200d940c0c400f030030142c1070302d40603100e60b04009001700000e0035050714004c000c084e6610f50034a6024000c503100e03184a100b52518103251860400601803031a40c0c05000c80718804100008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835973723 1250 835972473 835972519
    0x130213060e040303060906180902040204090c11010c1d0603311a100b13050910090c090b0d15030c030b090613080409020702030c0907020f300702 64
    0xc007003941020802403004064241c068800504400c00341000444c0c902440401c43e420801070a07080315a40356082c40c2951111303012103010f054400420b014408819000501d41e02d40741d12440d9041d4a001c0b520b01550788230b02c020080d4021240050002c0200090401035181e20280c0462340c1c20b542003109500410980340400003000342506003a001080506240c4141182000010150503d0b9001c10110840b0b4185250941e02600000d0b80c4490138401d02615038486604a140c1c0488070001700021502c501c00b0303071420398158120602000c8100002514a00690f0007000402802803107941a541d226911011001c0000340c0c0d2440e04aa590f12503e80e150025003003035840610a10410402d002d0070005541c109000304000040a0202d40300c6d00c41074000c9005880301941c0000c4c281e02075540801480d120303800c004003200030509186c680655141e21b10300e400c500f030703019200c1600c4220020402c51906c50034521448854608a0900b01d0400c1e40304090403640006044c0d00c2e681c04c0c59400b10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835974973 1250 835973723 835973729
    0x110d020a030e04230a0e03130611240a0b0402090f01030507140403050304030309050102070b040614040b1c0e031314180406051b070302030901080c0903030a031b050c0613021306 78
    0x4d142c0000381060300301a002d681c105001e04030154001c102d0131185108410b03181d02141c00c43c2c50000d80000c11100042d08107049500040300701004ac100340c81d20390850b401494051041260200710130001c0c2000e00059000310412036520241031030b21010300303500a4121950100351843c02031a42520303400107010ba5007103500282d400d40c1c0086024410581c0001040024150900041c00e08510384040c0c0c003c144501c0c041d0303008222410181c909070604200582d000352040004017a00c0c0c8030724850f030000700c020489c048003186060941c410000a00401100e8201c92203c0c0524040c90500b507498000314100c00f005030f0804000d0f402c044510001703c544902882c425003000c100ca0420112000382c0f68050350ba4103409032810840c91000940010848a040b0340c203003848012555085420b6825004108000790940000107105692541c1640501e4000340104050381c443c805212048640e400b450351400b031160321040c0403c0b400f0702c100358841c40b00d87c40185443c2232207084042c0881965943c0e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835976223 1250 835974973 835975031
    0x305100b1b0706080c0301031212020a0e0a062c13090b07020d05030f042406090b0a09090c180e16060807020a0503030601050a05070f050d110d020a030e04 68
    0x1400041d001e45050103003000821451600507601d050075184102c4512040c4030040840e00000d6000b403c4900410405009007580e420440d19000720340c0c006000540c01d00346844c070403d04403601242641c001c00510404180c10026440b40c50205030000725050980440c071540200c0c0e5030365201006402c1c0c0952030702688141400002d505180300301900d04600072800d481070140038020004003880e040d15844d400f0303812281022508580414a4406000605405d003220f400c04001143c0d07803005400110b4000001c0d01d001c031030103558030710180c112500d5480042000029131420440c2800d070b0400300101c140e03800c400050040c161407243e4134000240c1d501c1c003d48002c4643c1088040d40043c0184e6000c0b2a90024101e205035650300d0030340b203200060070941400004161b080300030f44a041030740c001541c0140c2492400c029401c10b507130f070b40b11030054540001e0124440c003900980d0110380c0b0217070210503400610f46044030340d40584103415030900305030f00182c2c0d6220041484406401c038000005904c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835977473 1250 835976223 835976257
    0xf17070c140d0c0b22050f160b0403020f0622061407030c060510030f050f01051803030a0f090602071101140a080103080c01140708060f010305160305100b 68
    0x2072510807500d480750011010a50044505840019000400c5000c1035502c89540320f22030313503107401200b4031004040240b18006207603a504410800002919044c0c0345d0392804641c424a4010205841888240103003246180203000c10030050519014110324803400030700050402e01c010310000481d001103c9003030f00441140d40e003041840d410092111020080c1c80c0d180385444210384000d4003200428000900803507a800001750704c5075071112040c01656011468001034013050500f01e940e40845900c6250075464400441c0d510081d80f1a040c42049508002e103095070746206001d402081501d0940100b079885805920020300c5a1006040c2913100b88195035800001d40c0006286001c1034490f00d01000041110b115030700e81000071715044950000704c1d035541c4d107044052035000d0f10340c980c81c10500c003083e1400e01400f00e802c0740546110381c00030380e240c580c1c0302d030048011400d0701c0c002c0d03e41c5010b800190242c103040324440e420040d1711030030039062400125038410315507620750f1060310319440c65580 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835978723 1250 835977473 835977497
    0x6020d0c080402010819020d11120c031006030506030c150c062202120f06070f12330f061d030604080a050319050c03041a010602030a0f1707 62
    0x286108403003600d0118074000409140c55400079010384c502800755040c070b541140100400c02c03066011034091011480c000e0142c030101c107185452640101385520981130905c0002071003c0509402c0d68031410202a882012514040069004000c05405580c250250003044491034076180d507051144c0640201440d69085440c01c03103410140c014140400c40781c080c0c0104220f101c02c03400c0202c502c035012100031140b03960020aa9140040c1c4500b0300c0c0c2c5034010b1a0070024001e803c4140101c0660407900c0f030303501d407114110001084861a900264000803207081501117408001350b0000280d00306080c040380356480c0e2011828108041d844034001807802100001c0c40c021329038001d0301d0142c09a0080156007000d03a14a001070055441140130840007000050b42403961800b500f80035980c506080013141400d1888442507441141c0603030f100c0d1802044400506400e002c80c0d070403a00683e010b1070401c440204200c402d00703c01c034003075010465008030503003060928031a410b0041d00203840d0310100941c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835979973 1250 835978723 835978747
    0xf131509080c121b030106091802101106010e041e082703030a0f1206030b15010c0f1112150604060b04031101030f0e030304050607021c0e0402070309050d0602 70
    0x30a1141c09441d048803041a01240081d4903005104c090250006445620011a004000603400200c1490905c1d00b0304d106a83c0e0b4a00c002c40c85e50080d0b800044a0f02c4018050f90b40d8a02003220f85103a5221000421060514100c0340360441e22030403c81c42c4408204e40345040c03c0f42d0162040c1c900c03540001e5008503900541c050b040c90070b5440c9040b00b0440c6010f900203900e03030054551271001e0140c04802c100b400d1740f04200b28104c139014001c04119070342e01c0742000314210000303d41c40550f2810703042c07001c0b00c55802541504142c5501c14204031451800355200e03900800c00b00f0034640c0090300032034099102e00080c440081d103064017011100c40c40ca070940801c420303210345600401c5440d100b0002400032510920f0580c0f664142070801081f0421182030316070080603d11034803804da02010045c0001c0040c0401d040c0d018048070360859648800009416007008150403524000c1000c020a82505040a070040c0000c1802801c0c040d060030343c1c6a01040f0340403c0e07040115025580041c804070450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835981223 1250 835979973 835979983
    0xc030a062727080a030b0a0303110d0c020d030e04181a010509010308040e07051308030318060c073002100f020418020d06090c090906050d02060f13150908 68
    0x240c606030540c010b10780d00160b907100703405000380142802c2800580310640c0ba0180d003204401c2c8801809801e001c40d40c074240149080750425803204039009401403402d003e44100c151692030b42d002400030250b0011030f60182c0e0720044204210750000d032654008031034441c0d1035000c8180307103004008101440105410400000005130046d61103002104018030100b000c44d000d55050303034860098201c0039181d61400355030600400301c0d07072900c1480c000404158100c0210207180101c00b860040310034441a03070741d120307282c00b0201d43c07450031441d0030f01c01d200c00f24036025100d05988801c1501044030040b40b40d0102c1c410140c00301d142000d03a100440c10001c06100d441101c1c1d82515030881181018103200f401075466800c00d1102c42d103d50082044031141019502900040540d004100941a1001c4028040350510f10900d465280392110005607420408040c16006500401c0d5500d0031060606030444c0350807024240d16984100200860703c6616a040d015151400e5200c1e509100e10b00074045142c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835982473 1250 835981223 835981241
    0x30c060c05210723030306011d0a09021b010c050d0f020d05010f0e0a05150d06023907051c0c030b13020f03010c021e120d0c090602060f0c030a0627 65
    0x501c0d822244044c8440d0040140c9401080910f030043c0a44110085008003911046840e5841030380c0b81c4c40010781c02c045a000b00f54284641c0f86209181000850460880e221880301c0404a80c0410050a90f040c19910250712010400801820329142c00004800c541c002d80240c902c4503500f45c82408402c41c41e48840740d02405e088030500581c0f829076209128142c3c0c6200c030a020364104d040308402c00000d501558009000750802c0c8400c0195055110840d800c0000040c020750411105203410105c0840e9550035500060701c2c5c09024018601082c071a0008490162000c0321a5580403000401055042e4019814480d90f80e030001e50600400081950246502d44268500f0b100d4440903600400c00105c190035190300300003039080803888603041c2080842071540c075100000701100403450301c0d48403c2d480700451356081101500e6000599407894240c0f070801034081c4100015054829504c0290351107000014007090440e950303100032800f40c000100b408058580c010004413070f606580301700e07456 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835983723 1250 835982473 835982513
    0x50105062e05120405010c182405090d05070911090108060405100801110d14010b04140301060320031002040513050406090c0303110c01020304030c060c052107 70
    0x100c141000e030480d0050440e140560381c146401c06046007a00d0061040e142c00c00c0c014444031046242c00d05c1d000c0c0c002d081c440341c0e20010881030141e0107400c10b545548c0c00182e400d4036802501115a0b15022100246004403c9041100401120a503511084801003505100301c1c014011036041c0410801600c020b07041c0e4006400b0240440c107807603a4424800b94221038143c80000c0c0e43e80700e2510b001c1c16803019400a980a600b044030341c8660354005001860f103810004010820504000101005501d00780300c0c1c003800c0001400107000c00c500c001c9034008019070080000410359500c2c0d50b01c071600c4c000060701356100000061110a80c1c1070a04c80681c020010744421840e280c28400015a4003010210000c4102c3c0c0e02c40c00942000404da1005c0c1946400c5400b0121490340c070b140080c80c0840326290121305014154400d8041e50002043c3e07020769501074081e0980500f041c0c0100c4514441c40f009840f1403207805207120151000c01d58490744424002410b668440352410304015401b40340b204000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835984973 1250 835983723 835983739
    0x4180b01051207270f090b0f010c03050d06080d090501020d1e0507020d050102070b1012020f0105030744040804030b060a1a090f06030402010807081009150305010506 73
    0x401c407000003800b03950042c12400c022040300a401c0c0c0d4000b5030034442e92400d049642e10300d80403914081210000040f900d150005101104030b9000f4440b1003400030801034041030b1461800c1e00040d000b6000b40402c0d045081c1d00048150740d40210031b1410000c2e65405002c01c114080901495a0504c90003141c0c960b60f0808040d2120f4681c00032010710100e0070084200f02012582e81c045588442104100a40040003592103400f241081445040c01380e510490348000034400041c0800c1c0d5010074540907800400d4111228400001505c1950005044d00d0400c412810407011004072500c1c14055825407161100840c690340d0340e841119050314000f0341d08401d00d00c2c01c000004105204550969070310000384246501c1e040082038641c00141c11501c0a0404201781118036841d41703002d05210082100c1070380c000c000c0c1c4400c2c000c162005540c080d0001d641940054400780c0100c40994124503482c0b03a00503035998070b4600d44c0481e164030780c00d50314545002c8010820321209009403078000008a80100d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835986223 1250 835984973 835984987
    0x6090c0f131a03151c020409080406030b100c0807060603050a1b09021303150605090705031609060f0825030501081027030201060e04082d1e09030304180b0105 70
    0x214081e040901151003108001d9128805c0354010300b10254241d8043c00502041041e4905043d45030420700074403001914001540e125071502d042d50000e1201140c880c0181001c8a44640075158082c107000c2d1001510f40d800000003920401c580e41500d4040c101080c1c020035500c26a100900c200d174051403805005001e1074070f100b40202c940c8c01c220f9038808201c045090880ba60480a050580c2c0160750004002701045141900200110311801d9181064030380303c0c1d10350a05940c0d2500038010320000030205200d060809018040070360300320301c2640440b6500c58000440040c00c0c1d2801c59000c0000c4d0311840104101c12003003042ea214040c080e01c0074400ca2003000c240f200c944110071403581c00c0c402c0d0f21890f002454001c0d808000506181100c10315141380500b04280291b02054203045048d02c003151120a0741c05643c0180404c4060006240c40c2941008049060301790030b022010306000100186501507404000420080c80210a51840d50501202d00b0046860001659052007010000d00b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835987473 1250 835986223 835986241
    0xb0301022505011d06071e050d1d0f0c1314041514010308040302130b0603010506280e10050304030f200717101406090c0f131a03 57
    0x70400c91150114561503400c56051090140241c1012030038100350507803801d020854085601c5118120741d81340c1c0311340c074045080d480c000303140304440383c20006400780880111032455401c1440b00e5220360305202c40b2911a83d8540b42007070207209590845078448100f81c402c508092130340d91f0740824403500400900242e12042d2800820060008042c035402110180c480d509070380c4400ca03000d200b0141d01042e5a141e1070021507550003070200b6842815140c48010829405010f42002c401c0f014054a040d40d18090500c08640c001c01c0512200d1491800c40521208030b030031510000d0710700d60b03940d1225101000180080000005164820402c0070410040404e0f00800c04140341c41003481e101d01c00311031490b1368400b900745088812502e03000e0540d000452001190084010008520030f4a03604141e6440e400110380c025203440c00716880c0880020410703c0c0040c0c0d103544c004007030941c0034500705941041403400d80c00754070b403584603140746041404146800c2482e8074034078101c111003070f00d5400e00c8418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835988723 1250 835987473 835987507
    0xe121014090604032007080c1807141c182609010e01110604050d0f0c0f06020906091203040806010b0703120b361b04060c08040f060509040b030102 65
    0x9020f0000480c01703003194000355000d41101c02d01080c1510301c59500c449845448034003900c852485424862131110219250305040c900031a007545440b04840e684084440440d0040902030310a06e1907590304580c05c095a000314525034020350820307100d4102238034020003c50030880c0417402d01e2080e0340c1500140c2510741c08413148040e003403c2031403003d0b0100004075846180020081c00c28003540b0144000c1181c0023500c2d400010382c2d51121203801400803c03c4034912180040600215140103810003c565560b00034003840c14060007061070580110702040e260071841100881d903a000150801000714144001c40c05002041072942c50f10000c3e80b401002da0282c1c00c08216125501d0b0742010446e0307681d1410b003e040c443c402c941042c00b140b001880780c84492003040e540c1d4a00813040014aa4802005115500c10541c46441d007004c0c105442201c10100e8180304858a91040101065540202110744010801c0e80d440c25560781c0000d060100360394840311264081e030300500c050140d40d40031042c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835989973 1250 835988723 835988731
    0x7030201020613240506030106170d08100b0a0c0c1202060712121b09080613081b010612050c0a030c090c021009050109050f12030a020306010e1210140906 68
    0x43c04040003582003003118490750300c00110700d95080701040c0ba01020150441803007842c04400801507075680f285072407200e5412907841146608820818811a0301648040d81c21660300d11201504035161140e0819990110140700c000c111200d090400b0040e10043d010003a02c0044101164034502d03a000c12854061420014000003441d01002c40e00c2d0f1003441d15001501c040401841a804035086040303c20220740d40c0c500015500c2580400c1201000a200d4000c205880f005021010642c440305405e400980c140440ba2031700c0f0079240403e038424095000070f4840540922807052a03850401e1600003003848582c0500c410b6071042012031700e210041001c80318158000b2505a00001041381440340603030759211002e10301040c280a209055001c00320503071040c07080b5540000d81c80f500540d00c1c6118a01800340c002e08100142119000c0c1c0c001d15044807043c10b0115101c3c81d8040043d4002440c9001660154050740443c0044480c83c046d200500002040729415030805150351500d982c0020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835991223 1250 835989973 835989991
    0x1109031504210504031e020901090203011d090d0c332f0d02072f1807031802120f060c0a090b0304080712050c01230612010f020406031508070302010206 67
    0x2031144602903203090b0900e031f0760080c440c1802e5a11100c240c8005d400a002d080c083e9a90704640804206000e9825800741101d08002c1186132110031040318940301004003200d0000c80701418180b4031001c4070701c0c0720705211801c4c0d2006400c000038004c44100c40010031900b0740380210101101c1c032500800c070701c3c910801208800c40c4d580c3c3d80000c6180043d10480400601d15403d1101c03588942c488500190004001801100060a1030b0410040740018280038440100010f90200314418002d034404103100c440b5415100d1148010f400058001840170708503100e540104011844581040c4032403a8040c1940c07401904161101800600f86025070107400a4604000080f405224803201540c0c3c94a505c019800155001610024403541180710700101035800c14101d5280c14800000b0500f003200e007107010103013603940c401c1042a00c0440800d8104203550340e20f81241a901c0b2400100094110790f200402c12208054800c4a0242a603106140d540c006030020700040c0ea000c541250008048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835992473 1250 835991223 835991243
    0x3040b060f0136120501060509060405072a0807321509030409060b0406030506220c0e0303030106030c02160f060f050c0a06051f03080a03110903150421050403 70
    0x110310300d800c2c0f0740544e080780351310780c1c4240d02d000c04221054006100f62003054640b0075403900c030f4405010940d2800c5d030311a0003050507006408080ea12003c0c00ea040340d02c00088026007800c850721030198aa200440541e02d50002d0381020880d064602050241005070919101014500549443d02d8610380d990f02030b801210030780410300c149410025503002e0008000104401913840c0000c0460ba8410701c14100460b041000003946440c1002c000c075100445050041420b03050a24514001c002d0682c107a41032121f0045603031065182080076502801054400007400100c080020b454002400ca20f401120480b4205010340b03458410200300f100c40782d050007d0350458800c420b03903850142c18603400c803d20130f640c0c0d400240314040e0412801290100b2250040090a40450800d1101400080e0155000300000c030105480b0754803d41030060030309880b604142c5003800080c204699036030080200d030361071000e00041c01141041031083c000003d55140010501d104003034030a006610020b0320b10050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835993723 1250 835992473 835992557
    0x203190201020c03030307020d1d1f051c021b0307050c150706090b06040501050619052b050406050c13050d080c030c010e010c0c030206010512010e0303040b060f01 72
    0x2c1081e003e1107000113040c2c0c1e40300d14211000a580d170707501702001b80002d0514488a040c0444070781b4000101c6101401c074954050a41c201040203001030b1b1040383c03c1020401000c448050404c01c02c111200c00100e01603a82c03011318042e1004401821802101508108400b50002d000001e48842076041502c0c1041180404080e8a120b0b024000014004506002a0b40c0420040c405494800c40302218208a181d80342c805025480c000d451207042d990380c1501005003654040d0b006480001c0034500030000b148001072031058056a04070300c10b0019600c8000744010090700d0f002340f0354044182045581403088600401060500a2154902808035080c0040610410f1421551090310403030803240c0e10741c071112495008003585d03030180e4025441d04100040b0b0510840304050b8503601640108101e908000c1007048031a220482007406658402c111601c1c4242131000d035100340c1c010031200b41e07a4030705035062000e000e80390404541001031a45001248014094103c0c00e00d200900982c418811 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835994973 1250 835993723 835993727
    0xe1005010801150c05030d05070201050709061d120106030503070b0a1509050a110a0c020108010f18050a1b090f0e0f13020f09010b28020309010c03050405060d0608190203190201 78
    0x684c0750002d4003501000840d48940507054001f0760241105a000b04115510f0f08400c079210f101a004080c0065452105071004003550080d00f210b4000003400b640310882140445400c40c0c2c020b0340110b4060304045110403c3c021443c40711584103a161605110406200600040410b82d0380561080c02e6903400c04940b03d180541e00450311000341c100341d19500c1610190103000c00341038002c12800920740100104203e5005901c14080340c81e41c2c0324541d0b109041401c0c0c03201070003009103030b9080f1070707594036043d4251903140d60b080850075640d890b403c15042c01c12801452048a54110300c034144614000c0c000788c02e003802c0f407c95000700d01c07901418001105200003a0701c0c00b8441c180d10781c041d00c000008141100224010621a010740b03a01120840d01c610f5042690f10000d00c02c2e00141c0c10503c00f545c1c40f540684c1c160303100c542c0f1a00e81503142a440e40e000625640002c0c00c020b10b000da40b00414001c40404200c50299072044034600601c0c500540e000a50340c0c01c107106000c0607981d901c290001164 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835996223 1250 835994973 835994987
    0x5060c07031e08030c0909090c0913020114130f0b040f12020d021e0f01022a0307030b27010e0703030323010b0304020414040309060804080910090e100501080115 71
    0x55203c1d89165490500f03a800210039040001d80130b1203501d200b004600320320341c00502003074043c0001d45a00d5260b5178500006001134500700c001d070306202440170301440110f50390000706200c501c20403004c40d020341081c08600b240300c8942c100a00c02042017009101003054000050200c0c5c0740920843e021451600c0850750001d02660025041125101d251031a541c0e050f4008821440584921550305106d0004a80c0c94001d1703010391a5000c035041222801203808680c101c60501d001c1c1c1120000b03960799540803400a000c807045241d400b503122040c1c48010041c00341100b0280c60400a108481000b6a025100c0003079210007418950740c0c0c520350071000d6110030440407403900c200c030542040d82e50700706404180e403044508078452031400c81c609114010407104d40340210741654441a60034289401034400e9807020f003043e90403c1061090024660361804048500302c400e603940d400c150b192000001c900300f03003d05038130244480b003241030040d40d9000c0c01180c1101d45c49415690401c000d228227035840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835997473 1250 835996223 835996283
    0x1080312060f10030b0411040b070f02030a120225270e0307050a1403030f1803040e0112140601060c06240b030114040507120f110a02011505060c0703 66
    0x240c281280f81400e503010b61007465409016038080c0030b4070041c49010300c200d104a000303460b4626000d01042011481901e07496003018805011102c0010543d2180980958171b0f403078100c010791001c0700b40e414203141c01d1403506850340c1810100000701d0500008000e0205585030038258034001e459840c002420540062441340341c1403041d640c1e5600c590800030745503601103505643c11002034244285140000044901c0380b041c41d26074282a89608007103184620b458050942d00e0300c0309210200d4010400c0002038000c04040940102904c071510707180c645a0448200012503402560041141a400560f021156035000078000b4001608102c50f05600c1c2155154079051840507102249440c00e031320096058484c5080d000600c003c04500304400c7d1501103940d04002913100301c880c002c1d806560044a07280d954540c02082c0c10790b00044800b181c1c0c0142c840c04d030060391900000d441540d0b002e10008046c080c1a41c0062824450582c0240c0d1030500780700c01014161894018a1038a4049a0031065 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835998723 1250 835997473 835997479
    0x5220902010216060215100303090302090408040f0f0e09010c081803120720070602030414030a0f05100b04230c1e042120040605031f1401080312060f 66
    0x441c5449040003907980c040041d800004021b0100440c0c0350451003401001200d6055440b000c05a040d54207001040740040c008a0740342d5030602020038543c22141c415005072004000e43c1c0003007071804802044031400540030162617454004043d0025034052105039003c00d200d0140d00203480b425040c20303d507104900c415004801503106201d1100c4d84012135035000021220044c1c505061200000e8490405210790005644108400c06c2100e80300c404207090603a0003000c0d10318601ca151034500d8204890365003103d054004201050f0303000c0d043c3c4211104030905480c01c0000302100702040940c9201c00010141540b01c101c0003840d4100340b2400c0311404544c0001c400d022905114a10400d900640944240403c002c1448540140f02020480740c2c5a0042c50001606014001301c5025030003134440d4075042902da400109442d20100f0407549940c0d03000300c0034548480e4440c8100e0031120380d486d081d42400e40440040261800c00000c0e81c02001c0304084070010754540c0350029960221503a01203030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835999973 1250 835998723 835998763
    0x313080a0c052d0312011202010e04020a03060509011208040b03062d150a0804030c0204270209060111120901030b13020307300f0b0406170106052209020102 69
    0x1200948010500f5424011680b408a10149181c18644034012040c0d41145d050a0000420440c7d2038003407022201c500605202804007540400714090ba1b00c00c118001c04240c40e00000c000a080c0800c10f50b005040301c40082c4100c0900d5540c8603028401c1c0d21406507908030200104017266604003040d0307458214050400c0c124000d44040ba0985001d40c40d0346842124841080a640b2001c1011640c0841d21030361018525a5141d6080c0c034180804241681c010707540329000780340140300700c07041042100104000540f0a1031351040014281004162604002c01040070302c441507070005001c00c01481440e1996180c1e01c05200407402401201c050941c0305407000d003c1400201640e0045000f0340d05a900d00304440f03240c0c0000866403d0980601d000038101c0c10100c8510869503004040c82e1001010200300e101c5c0410004060310b406401c03801c0300c5900384010724000d00c1c0034441c1200420059840b910701071000c170341d00c884511000b200c400100d178941540700216171003404124091585c5240f184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 836001223 1250 835999973 835999993
    0xf03180f0a0b0a05130201050307030603060c02011d0d051204210314060904030e1908030c160e06010905042a02030c1227060d0615030b060313080a0c05 67
    0x140d5252488201507844002c21400300d403000030540509032280d01d1215980e800c94000364011103995000030985c0d81016a903540110000e03400340140d220300b00351940042028440c02503000c84900c000340c0c00302e5084d40225041d0b80701c10307044000da8505550950031030382c0917a61810200e007085018001d440380700000d030030350400858041c5d00841240d0200b103d080025944c0406110400c04161805400b0602000c1c1540e014604010620380f0b00e020781c0d05000200381d41d0310740c003071468100d07240419090300b1040d01074520070f13982c066040090031700c40c0c06580d06040038000038040c8031460082c00d016030340360f10071400002c0c1c01200180000f0044121143c2c0d1014591009450780c2280180d8519400b801c850701c1342036507084e01501c0038070081c0e1420348958043c00b003c1000c440c10171910a0340040d000d01040e203800803144244001448410510348019501d60001001c0340c0c0103503ca83d10440c0e0a10900c0b404542c500800c00000d94050180381d80c90a0320041034450140e000d00c000d186102c1c0080b80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 836002473 1250 836001223 836001253
    0x907050f0d051506070b0103060b0d170c010e07150e0d020d0b0105040c02030a0503060409140604080c0d051c0b0321091e01021c05041a12011a0f0318 66
    0x1c0d0301c100510106119a0301c100310400400348174051001d4154a80040140f02088603a880800d004e0350003481002074517041d80c3c0b0345400c1d8610424809600e0400300d210145400207000c0c0c826600422005000038600b00200f11520000c2d84800408000c0481041d182c5a15140c2c1c88a002c0e035001440c000624009251100500c3c07424043c4901a03070604080e02907450000054409510407500e81c02d05641d41c45051100412441c5c4095071583e49080345a1030301c0c1d6040c0b04590207a030081d103880c2e541c4d80400c28418941000c0300706500c02c11204021101d8003c412181c619188444840d02258410040002900d003040000f521110340ca80c50f809014052400001449640b03010785200d035a61040c2289036060f910030910250258004a0003880100607030645400c180c81a41000c03401c00d80c5828203000ea0004141a00c90401c000051030064655504d81042c01854400f1a100c1d0004024000140c41e0040d003000074421726010000ca4902d40c1da135100702a001c04910300b200d103041610030f40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 836003723 1250 836002473 836002481
    0x7020d0b010902130806070516020d0b07050a031401030b07210509010204050f0301050f0105151207090501021b0618010201060308282a030e09010618050409110907050f0d 75
    0x4284d6607112288000940300d007001c03c1652160308079440d100c1c00c0c28401c11504514a0049800301c0c1e020b4505c0400c000081c1d064040c46000303085a03564241c880c50900400b0342103841141d00306681225403001080001c500e8003002d94000010324007180144561042500001c1e00c9004126030b0038105020003103881c10560180040301c3c1d04590102c2e41480143c20b040c00c07a081543c028403001a500010b10060070b2600c170007403150000c12000f51411140000e6100f401000341c42680018000301803c112560741000010418000712908a1003421010001001c6100385030f03070b0f008411403a242040d0540e00070b6215070000c503000140903640394201c903883c2d12060382d11401d500c001d1028250741800c191250300b160754406111800c480b10340840720345220a451049000f2010130400c0c488800d10368503504807003030080c41c0300c0d00c40c01d0b028071480d00304054905c0680c00ca00e006603c0c1800c0e441c00700e41110035072502e1345400c0d03c0003011512500c000300c07410b21802e03517a600c1d01180000c07504900310721030780 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 836004973 1250 836003723 836003737
    0x1e0e1504240e1e03122a0901022a03030723120a0e27040b060d020a03020f0d05120c160501020c150c2b0305071407020d0b010902 57
    0x18442030501c2909803030034200e44566480442c141d0044a00704044907003240340c005840000c1080780c1c200100c8140b0300b4a80c090499003843c400c0d14100001681c102880401c1d032417280401c2e11542011103d0b00004d50b2401142008240c1600441400c800022100001c156488020f002d49607244002e0a0803c2c80050243c040d00108a5071052a10144404200c21007a128041005445c0030121401100c9040004603419071207031743d510009503c400b0890507080ea1740b40700728042c0c103140303080d00b00301c281013900a00311406103106c40c61140042e0748e4400c3d15002e8036411078030f8480100f640d00c040384d000d0150500007085071061074464581c500c005000b40c001c1041160845da03111881d024510030040c690700c41c80d1f0159010892241143c40c068206100340600b114a070313802e20048804d482e1410300d807a0341c1c10300c60780f00805580e1003211121194009044160500b4091360811240c000c060000d040c0c2e0000c41e014000c10703510215a10502400748154015460081c156140c130707041002540001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 836006223 1250 836004973 836005013
    0x8031915060525031b060f020c0a06050609060d0611070f03080a0b06040e0109050a0b100f020712050303060d2a05030d0206010b160c0302060a0c0b0a1e0e1504 70
    0x500040b83c4001000560b035040e81d25554a041c420070541c101c40101072054000c90305c0c0b6841d004480c08104151001e00f6208440340700500304800203040c0758007100c1c00582494000c2d04003208000440d11480494203400750700010006541564400c8800f580c000c3d060028907000fa07d050101c1419070014034103001d261042d80400100c454081000603d1081b441800360130b000f000c2c01041502d05070790000d03500c607102502c0030940c401c84000103800c48645c1c81e00d20000c18104080340758a241c0c1040301d0009030000c0d40f80d030500151342ea1250340d40c0303001c02000540703e0f10001c0b07440c3c4100b100c402c0110703111031002c2044480011014203450200c0b03095010b028021f10032507101b640e1043c070018059040700c00c40082c00e072924007411041e81d44041003000c16034038a0a00c10740000141c640708000c140300d401c5541c0d01026080d00380f422828050004e05071002250411182c481800d41c0c0c0f80185504103420280002e0000c00502ca860a10701c007070004081c00c0d802d0601300424414034401c8038443c60141 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 836007473 1250 836006223 836006257
    0x305061302030a020105072306180105060607241e051f1509080f070512030c030a050a1715040516080103080c16060f09060c080319150605 61
    0x6080c044030180e00580042e6255020b0408000903500907401800c2d00c074000c2540e013084401d0b1105003005200090184003035071340b00000f0440000a0341720000b1a210401000703100703d04211001a18074040c0c407101401c05241542c130510340344c607400c0301c21042000c1144c081c0045940b4260300048101420360b200209030501c800500c03220b000c407030f85032100c0001c6d0f502090902d0a041c0d624044403c0c45c4108014410600e402140d01c2c0d00030044000d02405800c01048400d0a00060020015022010b5000e5074400c1c40001040b150200c1074030710503a114a0842d440d10300311901120f00030114400040d1101e0480d0130f03c143d0a541c1104803610301426a03040c001070302c0307407a0007500c000303e410803d60000c0d11100044c0700080014009001500c1017400302d40040504070311810803003406610003001b04100046d01101e0507000b144d4600102010f0038000305204454a84070400e00c0003c044190145001c0000c03840724100768000340300f409003440c07443c0065846c0c12000c1d241d944001030305001d00f080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 836008723 1250 836007473 836007481
    0x1e0408040311010e091602030d15030507050f090c3a050705030c0702010e12012a050a0e0f122e06031a04030e090c0703030e0c01021c022104030506 65
    0x3d52041c00604d0009480602555500c0310305081e100260040101140410030011410000c04d00460101d0321301c00110321443c1d490751415600c1d09480d036004601030045441155240e0795420301c3d81d40c3c4201840f1450307035148066940001240c1900c19054609401c0111001d1034003000c0c440e007a501d17005000704000c55252540705885a0200320b40724295540c0030442680154420013882d404190064012104074000301030340c50a489542006200c503c0304603014090342c003684004030b64000704500340544bc01c80481801000203250080c0140910600540844d03a44c4074218100302c510078a6058610017880e103003407030411003082480f52210382401058030303191581c1d600c602402c40c1da02204c01c038182e4042e00c202c91881600100160140102010320740030580b54400e9240c4101100e1500960f40c21180c500602180c5000d81000710a82c099143d055490f42c0004400030001c2020341c440031100c442110480c90807401060748841e4040e00000300c1210041c1c0d4001c1c000340e070320520580320a692 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 836009973 1250 836008723 836008727
    0xb0a05060f04020c0703020904060b0901060804051009050c1905012010110d060303081b1e03090106032406170304050f0d0b0f190e060a02031e040804031101 69
    0x18054911607030040d2102024022860315a004000445003807083e038961300e41d030740c00040d10602c049505840309601c0b0568103106180c0f400e0791501610036410301c01d096042c9600c4650b034400382400310281031562100b5050503c03404001079088141e0091038401183c1d400d259140f56140b0910859003c15200c000100c2d51a0301818054040885480101b0210b0138115003000030740700c408029104c1c00410070008244c1c2446020301000b03140240c40c0d00708a8140f007240281c14096007200102c182205220103000681409104170200c1e000700034542d100c0d1103c44803e4010031260303100804804040141c0000d0b40c84c0c1c105400e08800076184100441aa5441100000c2d413038a1241030792500200014400b902e0620750320400c40101070902081da486590b00c0100003442030f2004090810b1203010007007036074980341030718405c0a103800b0140090b0062019443d9904c00181c50000069004800200603035044da620310341c019034140c408440c50409080c122041e502501080d01d00344182d0129000d654 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 836011223 1250 836009973 836009981
    0x2012d0f020312270f06010305060f0c03040209192901020a1e0c151d15040501200109080307080106030213050f0a03060213140301060803032703030a090b0a 69
    0x898861443c0d11a41e82d5030300040c011403141c103900042020708100c1d00884031030800a0072280ea40200050000b54114200240703000002442001006003280070802008060410703070f908103070b0549114200b501d40703581c000c6081014055818501e460f00f00d007620404503445449141360f6110781740800002440004a84590580902a02c042442c2c0c1300e180e248040311011501c201d00450b0380c940d0603910b81c0703540760003040600c0f96100020b50714400d081130189420754007001820102d40030480500c80888000c0d181c0118402c10f0305100041c500ca80c90407010001a0081d00704880c007c102448451411419640041d103410000034002000032481500a1085580e201c402c0303250071003450b01d81020801c404d07840b1590a500a582c241c400400030710702e03001400c090628039003a40f00c0c85007801c07103444c0718611841155110b86c0c1840c604120880c808811a40c004520000da0551a02145407146003032240c03891440d494800082003062122065101c1c4601c03910401401180f9119210002c05a13 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 836012473 1250 836011223 836011237
    0xb0325032006040e15100302030f13030e01140412050708062d0a0915020306040b0603131112060f06010f231c050103060b0102060610140702012d0f0203 67
    0x4a5420441130200703c01c03036240d1550018440407642c0c1c0c001e006501056961400c1845603020a03004414481d034080d022508541c8800002d54855030580c0c0b44d00c0052070fa2502c1112141070100c0f05006440e41c50b0140100e901800070400408100b2a00e4540702d561512148922000f501411010440c402e03083d10140ba460080e2004101d00c06031100c1c2d4a2280e824054000322240365905003080029900b0240b0015074819104016202c0c0b0b02081880103650701260740301e104d10002c0007044103e540c141081a0255040304c000201c00760352001081054440c0080059148610000c1080c00d4160400f441d104d01020b03079424916550030300c000d5440703444059414142d500725080400300ca090781400780c1054000702c0d403000941194600c224080312001e0700309558441d2285448185960100038440d0801000d0742d03140c0a10b44188001404040404802048980001031040941e8031600d100e00c490700d20140356000c0501c1072208928200712040640e000300f11345004003401c04d03001106503007039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 836013723 1250 836012473 836012479
    0x1110403111011031c0e0f0c030c041103150d0c0e040201091a0702090403020c120c03150105010207090c0309060204121704300503120a0605090103030c060b03250320 73
    0xd08658864403917400e01c04030405003100d5900c812811840004000050103100c55030054042c4118901c00e1504010b0400c00840c061414800101016482c440403280d00c0f0788004001c9250704400c2000482400c0c4170b050241c0f4028440801180a04049003440c1c010f9100b40c845e00c090696503840240c034141401403010010b1010b01246000d0b04203aa41070b82e12034828415140392101850000e00e00e00d00310604801e9641c01840c02401d40c0c01c0820801440c142c108103200d00e0396241200007583d41c0418003c5003407181c2c80306524149039020760880e50384d10794862000e5445588903610340203401c41165050780c0400b40302c00c028a54800d0b0303a044601b03451000120f0704030148043c50025074802552031110a00703140e503260304c01040061024254070620329403440840e0400d0300080040d12203503003015220382c540d04010000070790041d50010b5810750001000c1503d0758113000207400c2c4024285146051004039114490f0b04441c2400c03181541e200d440103801e0680030420502c0308042407101550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 836014973 1250 836013723 836013727
    0x290a06050109140a170f01111201260105160f0c41032107050703030e010f060801021c05040804170a0807050c1206190e0111040311101103 61
    0x88150f00303c2c149070034a00140080303031403503075442c94510392000751801181d142d0082141c0786e124034002e00981c05480070020700307181804080404144072003030610400d40350040f00d0941d1101218081c1800a418210320020009481c080843c4541c4182e08000100011030500d001c1c1560380c020070110043c0354102407003505100c41c01245064000c01c41190031030806118070f03401c0b0490560180b84501e8074800003e075840b0340f05501c5801c440e085401f800d54940600c401003010041d402000e403515560180340c0030031180b01000496005014111a2000d81d0f8103007207010940d40815001490144200000c0305054000c044c494421588141d40040481e8000c0004000b400855400c1c054850580c0c07081c0e8294032031644e07c1445c2e551040108440903004909170140c1031a0078404404800f003403001505251030030128291555010407440010590f41760708445240000b548174050745000503418540d501d440c0c0c00d2150004001d00441361007580032841543d005445244016442034078000118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 836016223 1250 836014973 836014979
    0xf121c08330603100321031103071403040f02040c08010608090c030a020f0301021323120613210527030709020c010b0d060c09080105070f0c0c03290a06050109 70
    0x7505a0025000507121207410101001054032080c11110440c4140c9801d140010300d000c011f8180d41c4e510f55a5100f810b014010404c60b140c02124020706010460942e680da40e503035142010705001040c038060340041c5032411a43d180ca030025100341c1a00c41035281d0714043d50b1110f81780d6540b030340d88081c82034040d00030f440c0320001400c01041903130f03501000030009420058081e9200ca414031241d40048461401c12403040d4000207090446920500c0c1522108000c05034500000e54400002d090b01d0072210000031710000303000e080392095080b048440e51880d142c03c1030010080054101040d210310404242d04c2c110240f00b03944090824486000d009040c0191078000d14100a4100c02c0d041030655480d1010a65959581c070401c0041301d21413007001803403480000d03009141c841c842e007010005030315290522030303200d40040d0180d02500c0c142ca005041c0400510f001480728005034401410700e910940500c1d1a403110100e0f07500e40c0c3c05000c880c0101aa02e0095400540744a0310426012901044083c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 836017473 1250 836016223 836016229
    0x10b030a03080c04150c030306060212030705070c0e13020f0d050a140c09010314061302060f0c031902031b030a0c080a180303091a0301050f121c0833 66
    0x40781e40f000031040c0440c00c10303030384226160032440c070881004c0004a103105500c04158151140c0409000640700400d9003c0038280d00c02d5680c0310190000c0305001000c02c00808006444c06504050201d07188001907908205400e41a00780440200324499074291040401d00e04043c0c0c00307600400d40100081a031501c541e02d4400f640881c0010030015406210f030362000320b84031176010f2402144502c0d00c0301740c1140e40a82003800c1c120f020f04040058a602007031f41c40565141410394195404014806603250aa040c000d40345129880b0804500038001e2124001d154021000e000021206020328110f012841d071809c0e100e108040b84074011070000e1114001083c2040b001d840d4280c03c509242d15040d10003244081c1103901a402240021803411090000c14514491541d0300e5001c400d03c2402d650516000962001001c2250340c0129081c50f05d03000d001c03104000900340d51048010201d442240703880010f00020b01140c150313400c00f5180a40c0c0046000d90036440e01c03c0394000081c0d200b0601c4c2d2400b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 836018723 1250 836017473 836017487
    0x1a06120c100c0201111f050a050613110412080304120c03051c0626010b2205130b1e01060c1115041508010f080c031c050d0c02060702060603010b030a03 67
    0x209a0400180454000d015070040125020306d071240710350100b281d030105043c003040c0c0e41e00801e040141070418040c04480e0301d42417081c0d082040300e5680418000c0109a45a0300ca01a0f43d100e5024446526005070a00282d140114003941c00b91800c1c450b49902e892003a80c4198082200400141d010400001894004003c55000f085900c0c00852800d6031114100c03541c02d01040103140c3c0b062203400c4408400e030f09210f04460f01d034003602d100d190101c40140b50070300e0412007241c034a54561600700040003c480d519907c002e050380444195400d0500c03441c2224111034004245801c003c00c41c0000c107080b0f00800e000d50880780e002d00c4401041200400340405440e4685022071401400e100204141210490700e4004600c503076140d100030f41c50407000d100318110503404498550131510801d0364980b0040351859103515a1041c2119644000350101c03124407400c051541c20b149171000010071682e01081e80e6001d00030603801c440310381d158001010b00300c6084980c1c2d00d07455400716200c94002802068 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 836019973 1250 836018723 836018747
    0x10b030a110d09050d021005011a0f0c0109030507050606010e060d1a12030702010306120f2d0602040302090609060307060e0409050a060603021005040305030a08060402071a06120c10 80
    0xc00241414042c001000c01c1d2118a6421201d580082ca490030b4619810010340e1250314480a05014a52400203041040c01300310181444180000409000a81120080301c855011080c002c0000100d181801451a00030680484486c0078580c0030401541c851501001507080042c0154070b1300080b50b0980c0c005118662003940d0720f2241d2030742107020795542419010181c020401565641c8101c1c80014205d403d640c100101c8500c40c40b160102051800c15240003c0c1c0e80a1005030501c280c02c0a150583c0c0c582c498420f104074801c40030301080002680103402180d1080d0703001c20750b60721020104050381d2070480d90311380c266110786810000c403441a14007500080010b0800103100a054940700d0610a242400351105030315010b003041181492a4040f40c504201e1500a04050469450700c0e103034400c1c04462810400c040c808a401a90303154102d521007035000d041415900d000c81d9500070105000c0304c19520803616000050403060700425500640c4100800484400e54000c40c103503040b207860341d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 836021223 1250 836019973 836020001
    0x20706120e060f0105030706110d08060d080a0f030c0e100503150a03060c1103030708011e05100909060b04080c060d0e0607030509010c05070b16030e01060e0603070e010b030a 77
    0x1442250780aa05020090144a82058541c2598188010305140c1010795000d0f81c100318401018581d165400f003600c618809251920024a0700d860000640b55030300c0000c0504151400200c0b0501d96410400d010034040d42c41e1070606c01c1c00c1c803030349060341c951110803821034200040e05100c04905226030004e5a110710600c140382501c007800000f040a064050700304607a003550725805813500320b400400404210714a480110300d90316011400500002e070610902001c0170804150001644a1520000c082c09001c1c00325559050f100c80010440301c4588623083c4003910303009004c121005010111030a0b65400c0c001072481e11542000e02855034482e424101c0d480e07580d18281050680e05020041c01815540c2c0c011031365061071940b9608560290410009000e02000b0200016604054480d401b40101700100d40b820094541a40509280c3c8001c0c840703546040c001044040080030028050201581100c07901038440e520480c00c0d0a080c06081076004040c400106d200d0026001044140956 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 836022473 1250 836021223 836021231
    0x60c031e0c03020f070503090306161b0c050603091b0a05030304030b06040b0a08030a260a18020901060f0e06070b0606131a040905090718090c051f080a0c02070612 72
    0x400b5130000d1603000440125042d400000d0340421b14035082081075001050f003c0c0031002c445981e140a40354603000c0c840710b5194180c14408030705000c801e40421000f00406400c1075900d00c3c0010754991241a04000c0d000002d030b03090090079542c01d100000ca419580003a00540c40c041c00c64490840b1210000e1500c1e1780030b51110319180058491840110043c4807c4005503142c003066100a00f59061480b40743d4861090009544000c0d00366212068102014040000c3c9c164001001c510307950710790080182d0440c002c0da00028410f81e101c2e07100c10a090641d5a126600845402040340901c41c2c0140a01000403000200c0c040e817900301c008103420141d070982058480e03510b0003034502d50011010340c00c0720b00d41c010230700700819940c0f03004403988004440094550582410300d10354003d001c0e180e40c174208c03e980ea610801040079a08503d40504801805071b20070100c1211810810341400d9240d02c001002c000100d0301d110454012805071510030380103054a642048001c580150900d11040714483d1a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 836023723 1250 836022473 836022487
    0x3150403080a020c01180606080f28020d02180603070e10031704080105010e060108090a02010c06020d0b04180302010e03071a0c0f191b02010504090504260304060c031e0c0302 77
    0x1e40721011480d44107c001150852a122046003007681c0100e288481360040380100f0301ca860b0042c4070040640700403c145801444030300120b4208401014005c0d0000d400c1080302d10021701c1d13480440d120362000c03000c450341291200180781c0c000b101a90f400c0240d80005409000280075407500da55010032002200742803a40d1181e030142510000e90001c0300f003564007030078490a235034800b0a5a0380310740c0c018010074180e58147d0000f0f000345843d070000f41042c1d60105c0c000b00f04a0f4950002881600014400d110784000361217003c116a07c480d030202c02561800503807480302400807066444803600704006100c810705140808004240013000c1c50603691081000c00303600a03041c4080c0c65041c92003076901c0e0301c0d9066104040c0a41925040709226000140240d00050303038808126402e44901d0040418242c0310740c41c1c4802d0b40c800710844001042402c0e800c00c1c00e408041000b46104030b000701014484106003003402c0c0c080345c20641c41158214008545510310300e0840d00180c80f01300d8945001450049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 836024973 1250 836023723 836023751
    0x12041104200f0d0b220c0c0b070807020c13060906061704030c020d0b071e030e191106120f0a0b0114070201110105010b1e040f0314030c0307080903150403080a020c01 73
    0x148081e002c0c1807802d090710b111800c040341c4031b402c030b140d061420074107403501d8136840b1000451001000f8004008820300010003291080c400c60104603005003a0300c04008a141422001d01303514082c04078240d1505100081441c81000480051504805034041d41d80721601e0860385482050f4042c1c1c1c00c05c1400040c0740014594444140c403c04003955948044224400d0b60031643c004464008101800c1500e60540705502190f4820b00c16260401c48814842c18504a0040401404402d61040700421000c050900000c00d20b4400d058103c0d40040c0b0b40d40c2c2a04150840c5d00e21601d090029406100f5a045810140014040da5005041c201c1d0310111100581d801c0d0740c0241c000c007172200d0000c1060440c2c1128051a165602c0074180d80c3c83c203140c240440142c0701c080522020b040100f07444086c0c2c04900041c81200c910b4610f46017580d9980070582040c10300c41d8032042983d40a40b1a500007007018803804a9810b010b560b040c2d032000c106032503034141e01e0040c1d0010f105544095503119040a4440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 836026223 1250 836024973 836024989
    0x70f11030909041a0a0b012a0812060901060201021206090a1503150f090530040608040c0806090606040e010f1e0b100e1512041104200f0d0b 62
    0x782c414490b02104800b061015112850b0207003855094a0410510b206160f820190310108c000f44003a00600c0c1c844048800b080b0744600e030381d000d0070402c070001c4d070707000c18595850110b0710075001039800030b000d030741c1e02e8404034201c0c42900305002d0b81c606400081441c034a042c01035144c114900340c2000c40c1d13101640001d84a05007403548101c07030503000003071000f510f03c0190046034620341c0e400b1401c12002c2d91944409480300311000803401035485100401d8103810300c0c2c1c90441c3c032a450500d036041d16103480c0d400141c4510800d440a44900c0c10025002134000c00010303d1074851981400604410344408091001030300c0000102d1000b5501d647c089a42c00343d0701d120725880c0c03081448048001c104051072401c00c42c0e000c865024011030200496042c500d800c035003070300304441007a1601e183c025101d01f10503085009440c2d070000980c60050500043c0001c0c041298507041e000c03a010416011181407089502d5820402507620070001d204204208150740003a0510030f5404d000031031141803603400078441c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 836027473 1250 836026223 836026231
    0x10c0305040b130c030f03021608010606020c09150d060b03011503021809030406080408040e09100c210f20460c05070f080c09070f11030909 62
    0x65920010032040c0901c2d4041190030482c0000c88284042c3d1a80b070340c0c02c1a04131030001804100c0b8815012042500c2041941030301030182c0c0900c1111502d40c80303294080d00413840345000511815030611001d00d0800c0d0642e018800b502101c50014018800740107003400440419074205a03110221402ca403002e015541c11454101070301c1183e94150320420416107400303c04407803042d010310108001001e0000c100c5040d01c001d802e22040c65566071a0400e043d2041d90002d4070300700303600c01c14081c0051000690381c00544107844140004417a0042c11108044c60a0811001c8503080498151074421a480408500c1e808400480c40d00c07500001900030710744c2c0d9501502e050b0400a404615002c404201181030045807400250610b4820400710b002542c00f042415403542c940040a40d05003d190ac5035483c5030b1000035600300558510035140c03262400e114040c00c41c026101400c040e4986040c880d44201010307150584041c05007d4100c42c81700c06031a500310184400c10000881c6c0d92691a5503100d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 836028723 1250 836027473 836027477
    0xd0f080415030501080706052b0f0504030e030c011d01120e0616030204080a030509030a05010504030509190503060406110c0f010606030c0201090c030212030403170702043812010c 79
    0x20001070341d10003812580d0503804400c242e042890305010f510750140450780c4150103003d03008040c4000506a5152980c0075500341e10941c40e200c1d015250b542c8030382040b485103001c0e0b160740d2501d424807400d243e00e03282224040d074000f03000c0740703480305070081520003140d2000410301d410025000004049400c132185198800c00b00d903c103504000c21225204c2141e41c11807250302d015402c040c0740ca0100350b07885d45a5200142070290100340c402e81074804203c0d0035041a0484000d0040f4202410050301a40c000207025018120b0540b01d0000b4140d0b040d410b0044a40260040825903955103818000f00b8291502212a080c03c00c48030344070729800c0210301580d0707074840000510740c0e00d8075070302408032007140c006c0c2420b59040045c40b2000c0b4581c480384808694056500440d00510a80041d0552241d0b8100400000182d00303103400000078100038180e4140b0039141040650003008214401e000c50b29511411032030b594201c3e030a1340782401c1c0a06e007201e0016180e00314404c401944030b829507500f42c6075040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 836029973 1250 836028723 836028749
    0xe0111030a05061207180c1103030703140a23071707050903150c07030c030e15070b0a180f0f0c0e04050715020322050a180b100e0d0f0804 61
    0x346805101102c1130700000000f45074a0b80703810a20342d070407103410014198071741d0768840c2800c40b0350141840080480164055980d68600100050010254400b08400240020300024540101c0b48030383c10041d02140e804180100114601691a8000620490811091045581240141c4844180145150303200d6a440748200c800b0b06147c00700349803101e900b1016082c02c1c8941740180d1803c40380e007160189403032850031000d0306082d40c0d886526003c07280c00c5409901010360316070000b006030410380e10071800d04e01355440c1e0b0121003080d64070304401d000300064024814000140d80b200200d81d41131007101d4501c0303802c2e696250344484015961054004120707070401c00080000a0140740046c243e0034804054000340303184c00035942c0c06120745442126200240c2441005008040c4500401c40104130340d2585032548080e90240100c41d040d0000103080c581703a650145401c002c1011440c480e0350300d601500e0722540c108001e500d0850300c103980201542e4180390100d05040d008002412125038605 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 836031223 1250 836029973 836029981
    0x3040b0705060c0325090b0c0d1b0506011215021606180809010315080d0513060c08070b180105070e0f0307030507090e0709090c0f050103140a0e0111030a05 69
    0x500b4228000c001065810040041003400c1d039005004802108008010150340c0c40140c03800d640200c3c0d140c01a1040c81008a00c5961042c00010031010200031a55482042030070b40d10070307054a184030a001421600117000600021201c2c07441c40d0740c12402100d03074007940040ba940d2602240d120150b0600c00e101a02c10749400e00c103090261148501c6585003500c1c4541c281c1d107c034a81d5000e69940d031410140c90300003030721000c0300400c1900050018603050f240c0b0580003040290423035220007585442c018001c5070002c0c0c8075000d0302079141e00740d822203801441c00b0000e50310b10881c0c44006010031940e40d000e100060f1801024407440d80702c5d503500e0302c403440300c1c6281d40200a400b0b58509409031084d0f11104003800061b50108401049030081d0001140c031416071440e03141051095005409298601684a018080d148089100300c9404884080c1e24903110001101960011500d0f25085807408001c103410508650280b0050024007000041800c1c98032503180c101e500c1540d4144034291244240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 836032473 1250 836031223 836031233
    0x220809220615112b0e0301050f040b16080c0a1403100305010f0902030c0d11060d02030106080703062d05041a030607050909040b10030c1d0c0a0c02040f020c03040b07 73
    0x100f0102c0724881c000702002e1482c100e04c044210300595401e00100c40d0342c0310b4156000e02900c040b8040090003802880381c1c2c03821219a0390304020458041c2d506050210101e0100d1802c1d000b40f56588103940c1d14a2020740d2545130b00350159001004010400c0502584040340529031000b9500680d180065400350500d981043d6080d20407064000d40b007503240581e460010b82cae00154000c0c01010a54014110660301c0c00c1400840c1080f0b0072040d000003001503031400044407070340103505858050300c400300036880d659022000c84d585801085203858581911002800000c0e081a041e10710351350310105925169000b04050302c45819003000d1402c88184414000d18043c440541e014599241c00ca0602d4440b0b00041d0301108050b10290450b00300e440492003941542034000c000d1a0880d00b402002599104154405804008600100c3e1890360100701e481801030704440120303403681e503140080c4915408000c02000c00e014103455060b030802070380754090700070310280001300900c0f080c0b56140d480c1c5080c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 836033723 1250 836032473 836032487
    0x807080c030720060405040b0303120c120906131401320a0510050d060209100e040c0f20010e0f010509151003080307050c06040b220809220615 63
    0x401c9440019455009a444c0c0f2680103850440b00100c1d000300b1034142280120b403e6100304c0d0b0303203041c4007001c680c10001c0d5500c1000c01003001d2041d070030380e25000795900910161a01c10513600b0b019a00820188203012071000c1c0404020400c459000060515002c80b40d60034001c4900000c0309003ca01405000464200c800340795401034141109104601d001a204080c0e400343d80079851190f0304202c00c1c9804d0054590544c1e0f030001c40900000c00b0b820303842c40c0c06004196042a40340c80383d82402c540303003032191041c0c4116944000d03507101c5401042182d4504285400d07400b528181070f640c1c5451000444d4410000b2003a40c2401000019087c10271b1020785045c62800300700702440c05030580c03c0c845007081e407100308001c60742c0000d01a5100d458000d0111046c1c4210001c3d468507101d020f0500c0240400502d80b180140f4a42000039000402442008540c00d0b02d82400740c00040305000f0360a503414046201c0c40c0c0d8a804002e16503401c0e100030b4400c070850380f954110444010440c90880711003070300a10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 836034973 1250 836033723 836033753
    0x103030e01140f0301060c03020a0b010e010509150114210a05040309050306130303050a02090402070c240e040b0607080a1d2b23100b06070506010b070807080c0307 72
    0x84185420308003100340c2440d00c0b0603c01e09003000111f02e00441407610034480d942100398014902c240306e50b501c41d1180c200382002e00900c1d1098200d10082280341c1469000b0a042800c180c50742c0e003480145021088294001161441d0013109800c000c103040c06110703c00c103100781888d150004090401d0308006200d540c9075048140645d102d44144178000c92501a0500c2c0c00398145130110b007075901c0900e910081d018590240f500540040345000c104186000d10109450810b0303013043c134150f1003140318400103418500c0b035004070780f02e079030440c01e9400c168000c0803034000c001d001545094465960681180d2051214100180540c0c1800e004076849200c42010110100e440d06c0410740221400f02861108400001e1840c02141c40c00702044900380d092515400792942c0000054000501c03da04e89080d030a00f00001440e1030b81c1e00265182100c00e4560ae207802c070006082c5603003401223208090340001c8007a50030007010310040d0002030740e800c01080f101032404085d54072542140380000e07054210710 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 836036223 1250 836034973 836035007
    0x3121e0603070e04150207030e10020d1403040f052a400606230412030c030e04020304030e0111010e03030a020a030e0a080928060c03170103030e01 65
    0x1051261079900051074070140d41c0c0103552050316840d80c2c9001c2c000d44036000742c0d201c00a80046000c41c24141c0014801c003001200350b9050040b0030703581ca000c81e04c03a41003007440d00126052a6070350700f510203284051540a4800c51060842c42026160319190a0345030303080a592240000003a00032421240400c4841c45041d9014030030400010000641101200c1801e070860502c2041e81000274417408480d500d480e100300c400c10080346c407400300415050f84031081c00009203000c42c0392032000031103008840440c0d1680d5130007002d0070403e550031140c0700032000080c2d04101a80c11075900c2c650320f03440118040c52080c1c8641c0d41c02c40c440b40c0050845100c0d00b82010107039142250b90b454400c40402140d6011907840300040e078491482c4801c1e0020000c6180620303141c0b007034040c2d6804024070800200703500e580881e0308040c1c050740100d08030403a5104409090703114800b96010014140101e800e101000d1003030a00811080119001401c508400d03807081c0c0009400e8204160b555800c0030444081c64060b13 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 836037473 1250 836036223 836036281
    0x60e011e03020117040609020a1e1208040506090604030b090304030b0f0402030d0806060706091a10030309030803040303090203010905011407090311061b0613050c0609031b120312 79
    0x1540000c1c00840d034105644131210710090002e810021164041e6400c285d0041c070550800b07848400070030b10303030141c0f601841e5104003903000441c240c3d41040340d800401d0307407040103e8a014201424421160000100d064100c1001c2c0008800981c43c1d00183e44102d4060000390303181c91075030400804041001e001a9001540141030001581f00822402803d810700d0030409407585600002c50031600c540a40036212a140900c010100081206e2510246240c103021490980310480c0112080046110043c041401c0c92002c000043c1050702955001e40a03060004082c076131500400d003076403905642243c0c1d030f075511071042e625414400340d0590004414a4802d00c0c182c195590345e40d14243d0501d070144a1240850316042e07190402c3e0807001c0324441c01080d91803a007405554004104419001100c440c0100300c0781c6121820080c0658003000d40050007071078181c0b00701d00414403a12100d0035858001d91000004000c1c0607007080106004a1003420711360284c9002010035001991500841d0008001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 836038723 1250 836037473 836037479
    0x12706052d06060405030a0b0402040b0907050307030b060403020a03060203090615241b0f06011211121519050c0a0816030e0703030f0807090e07050a0909060e011e 72
    0x24010300c9200841d4100da440c050b520354000041440c05550300c4103615220703126400040180c2a094540110303c00e41d010300c1050140ca04100042a00310b4610000403400c1c40060752142c801e4000c5005410701900d9149003540b02d0f00410301d09006600240d4280f5000010309c489240100151070b40420484082140240c403200007540c242c01540c0e2111019400c0707542481450f00c03000c11a2401c0e82418440340403e28800055600c5036048414a01c0c0c90050500024000640304034080c00306c0d03071103820410008041c0080100c940c200940758829441070503203c0010f904680c4005000700c0d0408654808440d0104803003040d194010620700844a082c442c1510385038021a1440d00140ea64198820340d040304030044004202c007100000f17240c814000d000007410b030098880a15034210760fa40700417a07950b201041d61580c410b0b20a03248001d508400150743c00c0e104201070719881c3c5981c948410306c00c0d40c9a402505840300ea801c1003e0401d2007200402c0004c031051403107689420260420100742d45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 836039973 1250 836038723 836038771
    0x1050102030405060904110c07080f030307090501030c05070506040803011404112a07090b090f060a1502100e03181c0605060a08012a0c0503030a0c0201270605 70
    0x620f1080078000c00c0c0c042802200c80d995504288200740c00f0380255a207400c00300c86800e503a09007501c0b511030507004060002010990100031a44101c405880d4210071625040046004150704140300c0c007003100070310400002800511815021394080c1404949950406800449503c60031402920a600d00207043c401d440080d01074504420b11820f24402c03038032604500c01042840c290070b50915009900011464003881c0d0f0203201204020703034400055075500c0310b080b81901d40940e03c840e445004090208a0f000084100070101e0000344151140600038092a10940d40e018401700042d07000810380010a800c912003402d40e8007002c039280b1b03a0345e101c0c860815080140c0407002402461b107a00024520b91100b80c40d0000910f0113500030803a04e00305510a2021080e0707815035a4400f081c1e200e8400c3d0880c440c1003200242030b008405107141d6114102e610300180803041c0d05505654a80503590709050001e4580820600700c40448a0b0411017440d12030111000146070042c1d820304581582d01c050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 836041223 1250 836039973 836039977
    0x60f1a1c0507440c0607021e03032712150f0901110a0c0b060909030a080a14040b0a0c0302030c07020105070201022a09010e162303040305120a050105010203 69
    0x58203442003000350300034800c0681400b1411082c072409003203030b610400f0765003240100043c4140c0005410b80300d4003128101004040d1080c2c19010750700260f4a002480c219610014940d4a403070001c007164900085002c95000114144074000c030f641d5650803141c01e040c1400780041210080d2000540310704008803580c0140024007520f92407102208100050480b5025400302081000c1641c4454031807a0302240105040401d040031140940240c0201d501d0f0300b800d01d1018000c40e2000090350400f0840c0c0000c0b1214100144103211150b100c60f0111080c854140105005a003d06101e10082c50035001040513074102489c0e1000705441041003001914006c02568040d5030f0919010380c0c0c5201900040746000501c066280c680862800b09501c1492140724400140900b514103001ca0b83c1e0b10200307040f000c1e80489070039450303009040c59006014401c44104030300c211a20303110748405041d9800704182d50012a021000300e0310004a034910000c07000d0b6015488028114140840e40c1070400003034a81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 836042473 1250 836041223 836041229
    0x1320040b0f061e130b04051f050d09020a0e072f0d0c140d08010906050103020c03090111031611010306140a050103050a1118090906040f020904060f1a1c0507 69
    0x3c4800d1481c0c0418010300008681000252010b84030070140c68a03a0844c680e40248a080d00c42c0e40d0b145184c4000000c0e03c4880c201e413180c2c80d140c0c1420038409441002c098200301d1001ca070302240c0ca01340450b1520080d40c0e11030203924540d450f00c09400c80a40402d40b00081c113007030704038542d0300c120801092038400184400e0280042c6040c103400901c519011001150003072205040d406010010031030b050740002c0d0310707040380d200e8001440343c0d03580d6400540c124851418080c1d255001000941010750260011003a0040b00c20212032a00034071301c0e16400000f41690003210702381489910140b1569141c0a5203020740901035007440c201c0011300c00100c006019201d100d051645800c0000c2c1403400b5580b2903411494038242081e9640304c1024902d52807074042602e144a03518440c0402c039000d00018103240315940c4401e481c266500b5603000c1000120f4010012106a1340350000c141d5103000a002c0c1c07009501c00d0368034030f9091944c50005c12800071042c881c0e01516840720b5030028089200000d480c421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 836043723 1250 836042473 836042497
    0x606040b0f031b03150d021c0b1b120a0207020f150301240f031e060b0301030b0f06030a0314090604090b1509010f05070f1703090606150a081320040b0f06 68
    0x46d0395100c1c17000c19070380c5034604540c8084412a1010b00c0500c0003102040d1f21403503058000080c20000a00c03406458003c0d03000b5003048904030800104d640005a00609100d030000b800064204030343d40000300c050308420510403140700c001c4010130050403001003d50380e104000c00212580100901c00400404200c500341080680314104025a0b43c810020303070a900810501c14000103840300000162580280720440300035a010300000d0300c140004440c5c40c05404002c026000c01c04d0710782c50032100c0414508a000300a9001c209102c419992240100001c20002c500420f00030601010000c3d50404290170114440f810000004941c1e03101d840441180c240f400c00741d840da452418400440102c0c05802808a12030b408080c2100d0882c1001c0c500c5441d0301c100316190b90361040c0600c070b64007040f50300030603803008240049a28179000f141d4aa03070000214038032002481440e16094650140d055140b00c0707812007003828240c142014016100000d0301a1503030900742041c00042640341c4a4490402c43c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 836044973 1250 836043723 836043739
    0x8071208070201030c121b0206130b04080a120c09090e060103050c011b1707140d0e040203091f06151809020a200303060405062202030606040b0f031b0315 68
    0x11701c0c40e0042c0c5040d000314980d20300c02c101c034040f920398a02002c2c11622002003d4854400040c420002070032682d410107500800101c41c0384c403030b5641d8500d12341060341c40781c0502100c44103901c0e10503c1c2d0300c6800040b1000360f440100407441c040b180c0040714918851802c15400140061003c40e00010700c0340c0c40c0c08020f103000c400c0c0e12162000c545030b065162030010031441801d0f420307004e1050000050002c65019181c44281078812070341031940ca90654100350046035a0080100040c6015030145500031110000d8814003626480001150a4411001c03031000e0390301c1505000c1c1e004c400c15040081034490400103c202100040074140060600c141c0f80e506400148034042c0c54131883c05040344040884028001c0000c00304130741c0e142d8100b195103038001c03441e02c8005982403a00340600b1452501e00f841340c05510303000c10005030203540010040303a0032250400c000503207107000f080200031070031407890400e84900b0810740c1400c08841c00f100203981580b06109005801070100903159905100b1200c1314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 836046223 1250 836044973 836044991
    0x1202150106140c060c0406140c10051e16080702030406022802090109090b0a1407030c180b030a0c08010302130509010f020304050c1f0f1b0204020c070807120807020103 74
    0x400340e4455519260114000c0f44240015078501700b0182054171881c3c1ca45401c0800c007449810864015036410a00b031790300100020307040034020b600c03280d0020240c0c2503940405201c0100040d1901d01907480000411203842403401195000c00800d4008840b407003d9854603107001c00c003e60300d201d543c1115800f202c00c3c003104403400750303e2440760021603400740aa40056945805481c018a540c000641d0015054400222502c0c0684a001d41100c2103c1a26401351942d5104174001c004201e000c4051100c2c003032071710740d0381d240300c41e6528000c14503890001d5991030001c0da59010354084031844418008030000500050342c400c510280d070b28180c1d41c0c000032241d45203240c2ea80503200c0c2219250307a1510001c280700c2400000b246aa40c4c044041c0ca4802c1c1101105100701881c4404095440028000300c00d64444184201060020303480c8404a03078040303120580010b4100da00158040c45030354042c08042103d150240002d00003000c0e8510385508800554461407068840c040d4000d0401d0b50f580c00710 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 836047473 1250 836046223 836046257
    0x1d1002070e1008071701060906030b041104060e01080109050c10020c0607261b070e01170106030602031f080d080a0b010201020714030901030f0207021e01050c0f0a1202150106 77
    0x440b00030b0407070004031103145507600c2e10400501d0068105031400c1d400c081020441146074001d9100710380e400358500d11165950340782c5e4090111101c0481c5c1e071290b15550700103200c2c55001519400780c01c407040001010103c91422515041c024986940078200a203810301d000782e000f040e580c00f0034405450b0150786004615083c0c4588481d000040c00c0d540d202d2501c1d01202c80020040c0c64404440c1d0928029020826405965440b040c0b1a08641050f01401440f034035040000181c441004900041082d0713032aa034a50059030400c1398030b454201200800d1101c6001c1040d0100000e24201c805044601c5044034024000480200307501c1c5032503180c0d84e048100744d100750304071008640c00c04081000006c150321015107070303405495214002402c045110341c4112151007210803041c1d00425201800c103404810144221540e03c07481c0c18003400340414620b81d21f041c0540c004000300034020700b0b480e5800d071408031650000849200c08652015070340080442c2d1541c00030741582d9003030520881c80300c208844 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 836048723 1250 836047473 836047501
    0x703050a06022a07030317060d03030b010918390e0a0509040f03022a15070b040f0c0b07020315100906170d171f05060304031d1002070e 60
    0x2584100b500441c000c0f600c0414041849030540b40303c0c0d5100010030050103400301e0100000c0e03c00a41c040386a241da400024060307800584030240604110f0086079543c090b0b80e8080300030303c014040d0262a443c10303410b41c0c1690540d042a04110044400c212610715000e00b951607100001c0c8001d12100c503103640182d80d581203024008040051103808549040e00d410130560402c07543c02c0300035116900303007581040203044040010300d104c0c14662036000300c040308004214a1080c2c45500001c010004940452201d44000340b14a0080c016461903803124038140101c000c0c280d209101000050144c0001640e0101c1c61800c06296010802080d45071151404000c01440d48180c8015203406030000f020070100c1c4078140c49a00b100166507900c4004038042c1d8800080b00c0c6a220340c92103100c000340c04601e0f100507400035402014001191682c550300402e80aa00a48003a40801d2080034965100040a0046030310302006a4804415610030000030756181000d01900041e04100c0000038002c540350b0b04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 836049973 1250 836048723 836048767
    0x616060911040f09110901051c23030a1107120b07030e0303130b1605030403050307092606061914010e0303130503060c0403110f03030c06011401030b030703050a0602 73
    0x2c200001025082c0040051403901d50440308400c4001d66025240f0300400994101c131800790128402000c9035802d4408544910030446001d4801c50f9480b219020b0030080d482c00c424400011581d48002600240040d140701c4012a9a640f14080c240503224441b1144450f2662080c410180360300c45440540140401c00100d40c0320344404001c010b14582010120781043e0301460b062103442e01c4056441d4140050000c03240c0100c0c01c104003140010f446100159031007000d614040d41070390348441016607041d403030081c81c400700700440c5c40501c16210305102c044e812800c22100a03440c1d0590221503d682900c0d8454100b030380326040c1704007401da400340940d0008103400400345c1c4e03580c5448400c2455038500502070359011744116030007c1c01d220078800c100c4007620b400c0408055801c82e500c08100200c8a80f801c4550903020a05ca5451018400c2001c5030180040d1449804004c414000050445030400301c1c0901c280c2c0100c000b0000b050000c21841c00d0701341c0000300941d40c2d2b0f841d40039455080f44021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 836051223 1250 836049973 836049979
    0x11b02010203120718060c05060402061e0f250203120d150314010b0d0302060105090408071202010506010e041a0d1704081f0204031e020a080102040f03110616060911 73
    0xf410040d645034000d0f2280156200d00720081c10b0240c40b40411546150390307420040c44d030f074080400324004d460504041cac8a503100c03050094100c81949003240710203402c1710b00e00e80c4040801044c00c00c0845082444035100a014541607007000c1c4880c0c0019a0329586c003040e503944514005500c41580009822001b030444200c2ca04907051540c0e407900c1100e00740b0001c2201519480c00d400e0841a02d8003001600c1c105825a001380300366401d1200300002d1381006813040320000010000c50b0f00003409003810607664242600000345c80e1030040c0000d0802d003d18003100e48240d180400c24202c10022100048a03202d050300c0000e001c1c2d419107070102d845000018001401b410110f0000f600b0703000007490302c0400074030111050b03d01c80c103c86810180c0c0a103000081c000350464044d14041e4801881d65020540014072071152183c0ea03c0506003203a21a8009100d0404000780510511100e00d0903000103160a5510381d02e800d0036040c0c054940346c00c820000b050700c0c0d1668485014483c0d100d040600c0081c0007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 836052473 1250 836051223 836051257
    0x3091b2d06070809031b0a0902090d0212010f05011509031b0902040f0602010609020f030a020304031e030605012c0d0602070b0f010311040b10050a050c1506011805011b02010203 78
    0x10f41403102464108440d034030301c80e11501c00f90b4040c036641c09108030120b240240118051500f4002c02c40f0117504107158954100c0d10300388291015948075a0003040d00d0302144000100d03c14803014100c2030710310503003007910900c410000c00e25146034800100401c03284c00451030f4907448643c14110015280a40c0100343c0c081c004075000c036007079a00102c41da088448a400030012140d43d0140707170301a405540000e0b011742c0c1007440003e01c5030201c0d030002c65010b4401e180080000c02030602c001400000300e041040001c0d554202441a56044802d05880c0180f010441c0c04100c0d440030521007079032118280500940c403220750303c010062a0f40544030410342c802004200e6140100400003503642c00d00c401d54080180c003182c58880d0506215a07000e0034006082c20610340b008207016034080d40000401d808000302000740c20108902840126494824418480c20740c1c200302000401c0e0901c840c1c444031f115000401c0030043d0b6a000300d001080700c0c4c600c0c811007980c2e0a490006038111300500100d1540e400744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 836053723 1250 836052473 836052487
    0x9140f01020a08070c080a0e061b010c02010b0d0b0a11190201140a15051c08040b0c06060105131418070306032f130204031703091b2d06 60
    0x1040d0050480c44545a590407044d076a0110100c41990302040041c0c06030354200301070f00780c45106010680050a006d0604c0340b60000500741060401c0c03c040789442585d40d11045840c0060b428064400e10000485400700a6246611b03115401d650207010200c02503a12100008a002c0d40c2d420b0346c0207441070009004c0c4104500c400680a02840c0300845240003100001400b20412442181c0e03000d01000c0c691942c4905000c2403103060307414070051911100c04000d109000585800050003d00860101c0316210003a24203c585003400240c00981440320a00c8104040c0c03004000c00340407104102c000c2451002c8810110740140398000c0000800c0d14400200325001d6099007040d001c881c0724100c04a10384101306030000d10001d881d90a6821450340110400780ca180c4a800700711000200100145003942d40d0340c03101e11001c4000400c15a400002c810446440d0080c030003196007078100030703942041418034000580c1305104140f03c40e0810323000c01007034140702ca0703c100450080240500001d66841c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 836054973 1250 836053723 836053753
    0x20102120f181e1606080a0f020408030d060f09061802030a020904050106110d02011b11100e0a0c050301090b063708160501020d0f020c060403080d0c020f100914 71
    0xf000c4420b4a01c1850040000d0b480c0c800b003d44100c400300e030380b9554607841d400e003140003402442d03585890b210340074400030608000034002070140400e51080040d12070718040c0d11041d449020761008046d80d00d405001c000204600c04060490082c0a000583d6580e80030540380080c0550215035801c00d18080001c601c0c150807480700b80c540d8144900b01d540d0a25900002ca00741c43c0b030485402503c0c44c090102e040020300501812072595903110030f60702c00b5825071000b4400c45201100491080d030010314502d080c4964410001c002c2d20080d402400071303800d56100c0001d26140038002c030340204101e01c54200080a2603ca001145c00315000104c00c000f200c40c540e01184895002d80c58039030107000350702c04078129540c22182c00c9030720680281c0310382078440e501558010310140c0c6007820350040f48140d010f01c0e95888020310103503216143ca291528000c180300700444441d2401c40c000e43d80907006840a403007002424008101c04104046658400380ca41103415846800407104240b10748030700b1000f102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 836056223 1250 836054973 836055013
    0x4030803072102041419060c03261605070308060d140d020106050114090d0f03050c030d0f0c020105040f1103280203010e1609020724090302010c020102120f18 70
    0x400022000b0074003200b170010841d2112200400c1c0100501c040010003045000341c2180240d18040d04140c80041e518070744250041c014090004605d0b215038042003c03040c130020390581b45920901d0801e00745030f070b217a4001e8152180584003502c108040c3c040c020410110090858004020501f51412440c1009000c0d010786002d010b80380c0071409883c2e0b1901c0072003000307090309c1c0c00c1100104050445405503d6000040d440c5c80419070800504110084071440200000c1080e00c1d06100000f0f215400c0344d51a00856a4284005003164180320a00001c540c00303140080e9201e8024000596200110001a103060791a20041c10001c2c0102d591200c0382c03100070f0840c0d0307500380245d009000b040002410191183c20450703810541320400780b0240700d4414181c0c05070003024403827001d1652440c1808026203102440300e0310400f69946500d0100c1c201036080c01260f280240500003981441d045060546820780c0003007913410482c0d955400122091900480d042521480b0416104801d40c0c2c81c4203c00c0b1a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 836057473 1250 836056223 836056229
    0x513060e15011403030306060c031201030515010905070206160e030718110a02030a030f1814010f0522020402040308041217090603180a0b0a0f0e0c03030403080307210204 75
    0x4842001c00000c840d010000805081c440c000c01451859440c0001c0100b2a04600c05a06444c07006000714000c120ba804100d030f000e50300a00c010103200900107084109400140c21034070016042c0001d00803040d400088840d04146500c05000392501964412207042e01e4440060742e05210349400081d1800150119180c0448283d80a0055046d0030550740002e20491804034010fa10070400070240300d00c00e502c030001d040d01d0f5980214031000d0455024440992010054600f15046a801c11807000b0034800c070080c02a40030f105000a103400c10f10400d1440a54400c080c6c2c18089200d5201103540d076504950255601c114030544650319021842c2d01018001c4017140c00d19070a04800010510500548400500080c40f541c60755861005020610031005141c5005105100d8148005880580c5042c0300d241c005800055140e092000c21040d10000080f603d0f281e005400ca00e407181d14040122415660004401580c91710b4001d0102c0710342c0450040840c202d440304240d4a01e28120380c00910031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 836058723 1250 836057473 836057503
    0x10806281e031a190501090c020f06041e0c1a190309020924031b1008010518041506030807030f0f080118021b0606010315180513060e 59
    0x3080032a0281c00daa4503107000191103040312100480310320307076003036030070f41d4420601415000c6440c0b0818140e81580d40c282c00c40d069180d2501810315035550b04129120a034500d0000800150500e1344584210b1000380c071505102e004a001d045003400b07140e80f0020300a02480104580c064490340228a140e004104090107002410340042d01c2148680a4034a1542d0010030755000c03601c1d0912002c17070918440c400c10f402420001d00201c01075400340110702e403c0500d10000580b007180d41c01000502e1010003010360078131003c0b50041c07226840e07040072020815030506810109413224241409030303030490100001c1a608021011041103140c0c406000050b03ca42c03626203406030859025181100314401c400d00040740758004004043c01c076000104041c56040b001440c2c00039914040e2112010795a41000c1540b02409200c20740d68103210f80e80407480d000402c054440d0410081c00344a0b00641c3c3c100c290700d0f07141e1000c1410f0b12604111103071a254810000c10400325140c8143e0f49075079020801c154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 836059973 1250 836058723 836058749
    0x403050c1005070515040303110a0f080603010c020703020427081215030d0311130905060f060403030c060207031407030f0905010f02070306050408070b0907081c050901080628 77
    0x29140b4041c0b416601810b90040140c03005810f0603c0c000214070005000703400301611841601c1008816900811841e00c00e075580c1d4603100003107171010b41042c1d0701803c80c501aa01d0044441c404a6000c940001921313411200420f140382064000810040108540c40382280060307543c41c1040262401400b80390480007642d44180e503000f1881e00340908070007060340c040e00066001d1170524440d501c10b150380303122b00740400c0c10012100c0b805151480320740c02c04910b195136003090110a181000c80c00d507800c601165030300d15207800c580e001002d282c1031a0b40141215004a45202094040c51480d010180714001040d21a240790030002c03e00049800440085000c5220104095220703c0e83d140342003080c0d800510f0441c0c1340d039031040c0080000501c2503800d04802d10582d00010050101c0390b004060460040040c14101691142002100c50918a80f010203180720f10000c2d030081c0c00d0740da40a03001d00b0510042da0b2840013203450218000e200c6141e040c3c020644500c1c02407145860750076205280d202c15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 836061223 1250 836059973 836059999
    0x15021b010b04061a03070c0b0106020c0f04111c140f07030f0507050a0f0509060d0c02071409011503140a0c0e06040b070b18030706140604150e0c0f0403050c 69
    0x3104030f84650261051a0200c2603d1090581802c0000c40d0000014034005c00203900a40700c00030815400c0e0041c03401038200240601c2c00d490050844003c1c00811541044440e84c08101c8440500c107103862700c80c011061050541030f252140d80710fa44244100c0c5202e40761481e1855408440f202c080b150320010a14240c0c0038540707500d0912545204080c1b03902e80a1908643e0641518000381360404101045020401e002c0c407500c4a27009801b91820014010950b030040510190810b00150041d0518802240302c3c04290383e12510780780c0c112025403c1d51003109030340800480c007034081000401802c0303400ca401d000ba0000c81d03901020a500c0696200681c040348941005018451032092020300da5082c4503c0000c1400d1174265500985200009245d00110300f41c46410b42c0c01903541526100d80c1c0303100031424480b240008540c0050129800c000d8650200c9054101525500800d10880044d40c00110340310804021104210300341d500300350702c0756980e1406079910f104503040c046c06035107460800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 836062473 1250 836061223 836061229
    0xe01020d290108101a070b1e0403140403050d0c020909070536010f0e010e281805060a06060822020307030210030b011107050607060915021b010b 64
    0x16452001030180892041c594150044403503010140501d00841100040051022803108050b1078420903600240d864000d01e09000700364100061001032020490002c0c624001032548030158015418100341190050710300901020303010b9500010150320404012030900388d0000201c50402c2c1c803c50385c0c24000d5a8449145444106074414180c00900d15120320505a45661502c1c19002000508030200340b41800740101501082e4022200c20403400f00c00c0c8201c3e580b07040102e000d040c0403c2c041b18203003400e10f150181103084a19110305014051110b18200c00541c00c244420041616000281c43d041d04060340c48050998104841c00e2814400244250041441900c190348514207560385000e04130107000c4d2000b20010480c2c1c1401201d2003c801a6900c00c1c600c9198401d03903900042c0422190000742590298004469039079000f96010005070b9610400c8502a951050021030308000ca490039042043d88110100c404a002040c3c80c01002c00092a00c0c4540e40c100c00240f15001a060074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 836063723 1250 836062473 836062511
    0x4180f0b0109031509020913050c040b06040312020708030d0c0e0307050109151407060501090c020c0907140702060a050703090b070b010501080712150602071a1605030d0e01020d 78
    0x600e0301091080e00200081180203134583e000006403c00483e00000560001e81103402c204d07105c1070002c2030441c0d4501403100c200070001c0c8148c0c00b0b4500f0444054050000352050180d8800103140c0310003141544101c0e07100b849a84002d240000849886402c60012031028041c091a188001402145490581e00e0b00044144c1210810b84440104504050010301190b002000710001d10000f110300b100d548110741e00411003c0e000304c1d0002410f505201100058820329105882103500402c00100170f03546806503640c1005050902481000d07800d41c10092502a811000e5404000802e0079201e568100b0001d04555100303a40304411980c4890a204035402031441c05450103400200500540d4054420303d504002c04e410221108104900b0305402c2d50440f8a412948010003d810000c3c0c0380c04000490144c81c61000d01c0e80782400300700c95407040c1d000d07111003116403401c0c142800d418400e09208841d40010f410409001e20b10303000100c0341c040d51119882c024447c0c07034114002010cc80c034801d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 836064973 1250 836063723 836063741
    0x60c0503160503151009231f020d030f09081c050105031c0503060d080706060312030b030c0d11030f03030115050a050a0309080f070f050c0f0d080d0204030804180f 72
    0x4c000003001040741e052100c084a181000c406110401c000402c0c50005c1840d5080381509003500c87c20002180000e2103180484600c0050182008a2030541c015401142a101c45901e610340000e060a14000324400742030440c44c05080e0356800180c5841c0b615540c0b1010041e1819207605221036642c0d1414543d072221240b5201c09821040314880945d41d104200943c4c00000040449520100036110811107a022510403109156035a4007001001003006550020340e8540c1001c110300e0300080c1c0484c2c0c0700c201102145108041c01203c07401089240300c070342105844090100c0c0c040c0d5003650541c913a280c0c000e0240410f00049074040c04403451203841103844030915503603100c3c10025040015406814542d504030781e01e00d0140980e0144403003c1010b0004103009084620754a0424108141000071540c3d80d2805214958862542911a214032005440c0d01c175106564450f209010700d4024056504001d02c1c07190005000603280c00a082304918200c0101c40030400c034444e500755002115a804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 836066223 1250 836064973 836064991
    0xf100c050f0f0a0311070e0106020102071b0513180b07020a0606050a03080a180b1827011203020c062106010306080c040b01020a02090f071b0c05060a0c060c0503160503 74
    0x18114400648030344082c1c885ca45501c81101c4416841d40004511920260021001030b03601040d4081407124900f07182c105540940c00784e1003405c1c00c0c2800b081e5074500c1000004410354651582c501c40800d011620b042c815007024aa14141c2803e1400030349951100e03078241c44103820100c000c035191401c04203001c100d1358481910740c5400d05100d000d079841440c000000d20184201070002502c1c2d400203008010034100c5081e40501e0680b980c0400004884801c1503080a4130301084111046d464610000e055681c04611010044417501c0c00700c0c907045820710301030f400030310100e039200c200c02c820303800151740c0904200c080c2200e40d90200118100c41480c8119034186d03102141c900760038102540255005241072040d600150501c0d000300d080301d00300b61010784864500700304000c2181c1d03210314440c80c290651422050072403010740300e820800f41140600c9206000019903041c10b94010300c021340d41a540101d0034400c0e804069405440c9820480d00d0300d000c5000e0405401d40e42d4401e00407284555951 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 836067473 1250 836066223 836066233
    0x5070e0108060a0e0a0b0108010f14013f0b01090b010804020d02041e060b0d06080a08040b180904060522030815031e2a060304060b0f100c050f0f 64
    0x42c4483c000a0300802045108a01507030107036601240300c407122980030b0040303c000480c4640d01002c081c000c0351141c0303002a0062241d04014400c0c800300266524105a969028100c268036121745103610f0f0002c01034807540c3e842c19000d0001000b061a521a049a881103410042050b4440040d00c40080890f4001c1d4841002d80d614001490140e1011442c0c3c1008800c2c020b05842260980c000c40d200c50304440424400806c507141c0b07000c01805100040d1840b4405020413604070ba0b1051164091401540c410600c0813440c81000f103008440c94102c0900100307820f4150800d81131800042100b42d0302d00c800c82c44070603909160160780c0d09480180a6150707440608659071884040d041000c3c4100b040d0f41030041e4410b16584c110060b071062884009000500080300c0a100a040ea24203280040085203800d500140301e55070711380b01900c6d4000e41041c0049491100040001da41c0b0804071030855010b0000710040307902c950b1002659001d184244112880d8a29681c185695090550844c071a66400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 836068723 1250 836067473 836067481
    0x909050a12022b080c0f2b020d05091209150a140414011805060409180609140c010309150c0228060501080606090105130b041419051512070e1305070e010806 69
    0x41c095070549041f4a920b0782c55240901101c1d074000e03079100c031490450300e503120b00c1800084a8180160855081000c42c000d10b0240c802002c0742c00d044004030801190000483c400e480540100144101b80310b601241556854440f82c0101c62504800b07511800250003d2441d00d40c2c5130321407100c1096030001000107003400c0c07800c4000d00c00352004000c2c4c4168003465412040c00113143d40118404030740701e8055992103102e048840c9281188000b50241014144240360b400b02d09001641d03d80908915808507203508400d40907445c05038040742d074000e420160011603442401d101c20b242c0b8094071641080c04540d98440c1240d99501c1c05480881d0f000d40326030010031582c41c0c131507078150310f8003031a001c0499010001000a42142c0201d1001d074800283d1008000c90f40c181c180d15400d0f600400c19003000b507800c00200b0209098104003507540601915111004414402c100601c0180f40071300c852040d900d0305202545c04901e59002c225a9489031242c0070500c03c4541e0000c905903800708009140944e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 836069973 1250 836068723 836068747
    0x7060e12041815050d03140c15090604030806040e15071e090b0909060a0e1003110319030f0909050903040302010f0807021207020a26070909050a12022b080c0f 70
    0x2002140c00c901f441a2044103070540c0c850a40600030302000c00b00605514540c0c000d810b040d401005180c0b0b03010781c015408210000c1c0e08000403a80041041e01e0014a00b80b401800d14540a00142c07030242082038401008481c0340e01042c0d90441c41c040120b14104c000390000151b9a01d0014001c201c9004020b001d881140c1c03c004c04c0140d84142e0042881120aa4840c0100f0075100f0640381d810042c503070500180140850603066440c500c41c00e800038080009401c2e0044122824030f00c0080400030815001d19815200d03100071405018400410040390902074034656aa5210344002c82c00300d44140000c00c03185000d544000d22a14454000d060344a0190000044a52204504030f91003920304902080301d440125400b401d0310344105401d1080500f481c2601d16100f003e50000302c06a00348149880083c2000c600799042d00d602400c40388580b0030000040e41844600900804603107614114280c0b2500d140010741341d8280e064841d50700540728000340784801c2c4030306803010b0b030324203070030400c020120b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 836071223 1250 836069973 836069989
    0x30a150f05060414011e1715180408090a0602150901020a140a0201060e010306050a1d0c130204031e030909180f020f03070b0702090c09100507060e1204181505 70
    0x101490071706c2480d1040359030050085010600500003900114030004c42e100126185900f000300c440c161840d071080000060b60000e02502e48020f0006170402250402c03540070b00b034511200c3c00a041d09822615080000c2d0b882118010840c10711880701d0204401c03690600c202d1f500c2182a5455501c4039003415030426043c3d000b10121401c642d170b03070f5100044035286069058065842908086024201050b030780c4199000c0d8540c08071034244c2c0924440c6500d4002030319044540060311101121003204005400a0023158405402c1c10504000352060034804279490300400c2c420303259400c07003a45800002040755441e6803030344102c0908446001c0030230714507884100241d00c004c010400202140e00402c0c100612039111245068001c150300d021803030100040c41d842840d00c280541044201c0c000100c080022031100d60622a00103039040a00c01107030001d1034504590000c0b038400c030300d1100700d806184e0f00030320a400c4440c07007031011040e40242e9401441c01640100c1c0000b800f0505000402c1524 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 836072473 1250 836071223 836071259
    0x3270c0e1e09030c030a0e1e0102030301050d0c090507020f16050306040b18070e06040b0105030c1b0f03070302060f01060f0e0910050306040c0e0c0a0c12050c03030a150f050604 78
    0x621044c845451585001c00c0100700f80320090b5501c09124000d24240010041700c0302c0711986007101e02c04000b0069a000050780e0440d10122000070b50340c4594102002032410b5500041044c03070511301002103058001440040075004a0200c480b217000015031131b0062401c900955506401c114007040c049078201b0b01c69600012590700f100020803000c02c03030751324010003640016900c9003140204065807131700340f040c40c0c0142000e0a22628520740321081051510842e00c6000356040b4650007218508000c00c4040503106142046030783d01c4020b810041d6403502c2c00c4890344464032540c2c002145251090302005522005512542c500b581840100038035054002d104204210f031803000010107682c00c1140a00803030042c3c078a0300300c55041150030b210a8074014011400007000300b00c0c242841c2c1d0300c1414243c44a0708510000690006030384215076910520480b411544404000d120716250144c1c4424840505426000d0181b5031b1010945d00c9a28184105580601c05000400040c0f00c0240d4041b20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 836073723 1250 836072473 836072491
    0x70f06021b030a0305060f041a04050703111602042016051006030b010503010c080108030301030f020609042301090605060d1829092a0103270c0e1e 65
    0x4038400c0348808500d183c00c8444800000b80c0c8410078043e440c10b20000c8003181d480203507428020704c503160b0710f51401c00300d04110450046a03928005440c00303120740c0c8407411229a201c15281d035801c092034407030811804180240e10651608032240a0000542e02a941e00e5040050722410712848948500304107892240c10b8429009104031707200ca840240c8690005140318480100255040c003060600311a51004540c013480110001400702c1d40000045c1d1b41101c1e400300c1440c403000300a2000c501d8a0086221840d00315040c0324100d180c03a2000c2d4204904814000c42e080801e03079903020702c4020b0718520b20070a45c100000708240801a8410340004558414a83c43d4a40203955542c0b01d80e0f40e95020307101130300b2842998400c14248250141c449810543c180010410884040690000c45e44c3c5209140f40c1980f444051800c0d036400394000d01103e000314240480318286415440cc1c40b400d0141c0211008500f003540400c240e0103150800d4040c1f0182c80d41700c2c42003006203050020100d4040e008c094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 836074973 1250 836073723 836073757
    0x3090c060c030c08031611070501080f090a170304031211090609040608060108010b0901090b13020703030e070f050a08150a02030910050423030307021c1101020408160b070f0602 78
    0x410b01300c0d03004600842282595100507000c5600042c40e80c10000d030305c4405500903000400c80d41e07900a07a07032a0006804141e003803107515540c0340780e03183c40301d07440c4010a0000380c4280d1004c03c120040c0a188900d000e6118001c0e50a28560808102e980c00808401c03014410311141005003070020242601c1c10010744001411602d0300501840c08070300b64002c0b04280e4680d07c110f2150304245001d035005151400b4240181d101c8a00080c2c004103008403040d080541c00700d42d1405140c408c0c1c01c1252042c0241095450964640e219049440200d000700f90242c5d410690000b000c150010394500c17080d01c0c0110385603013606da00c00302402a600180002503c1d200d01101002071100c544622130099201d13500f00c2600405200c0303000540d0710440c5c94412650418000c00004680100310503030202800d807d44035515400480c2a128001c8216002c1d64a61003c140401c80300d00000300700714164400740c00c00c0e1000b6510745402806100d110310041040d0b03400c3c074600c00000d01580180c029240d11882c420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 836076223 1250 836074973 836074997
    0x1030906091b0506030907030807210816020f1b27060f1c020405040c0f0b03150306041218030812060f0303030c160c0503010516090603090c060c03 65
    0x15099440c04501500c00725152042e14541c0711000a0102c020502500c8850840c500083c030507440310f5440c4805040358600180f0714003003140040d0110b591419100c8100003a41405000901425003110100d0a20000b00e05150500e40000380c42900030900e00018480d404400da440c5054402c80c91400c0c1c2c000040000d140f40c0b41100310408c400403001c600b0340000b43c2c80c02c0b804101c072003100b10b400e26026801e419035880c55555240c0e5988003044d01541c010138207032124500700c41000c11943c031003080b000711000b000c00c08821039001075004200c004a00d151900f41e40f07003055194481502e0040014100c107000220540c01100512602c0c01c00191070740106a80e6107400c9116481500d010399400c801d01c0c10028a4601003004260000080d0000e500790b14040c4c1081c1c2183c403500240490200700300724504200100c04c454500600f20140c024092418003404086000c0860f101090119aa00c20b004c5049846440388046403504418486411792504a099411201b058410703002c00945501c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 836077473 1250 836076223 836076233
    0x9051e12030f0a030b0a05181b0309150108010507052d1305090a1e27050a050d020604150e160f0f05060f04030822081b0301051006030b010309 63
    0x5404000100040d150f956070203290014200ca844294451003107120382400d0220362212480d08048030354141c0e0540240d102d1542445100d520841c80c029070070b00000800c11001400b0175000100d8840581207181e41c7d880d214000d080c0c4000f100c504001480501400364a01c0d04107006844540e040996503800710003144d41d10607964080d070010350b180d004041c010445420030012640c0e0000c028042048584621840008142e4070490010360580e103941140300841100780c0401003a401d40241c0a60607012403410725210a1b40d03140c2601d03580125035140504500104c0e00da0b100316448200107000320100e007907001c0100074020000c4064400d10441c1140148441c2c180340c090003541074160901440c0000c00105001c01e60071680c0140e800b0700c03581c20f00e01c004806442c00d40794403980c03007610744603002c540c50404440748054600c04190400300040b80c0d0380c04a055054408440c207000f4030840080f040c1401e0300d6003594a88400e40e881001000400c0c800e03800b20042110524021a00c040a6218 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 836078723 1250 836077473 836077477
    0x304060b0621010612140106030b0f0306130501060608010b09010c0303090812010f090204320a09090303051608040b04080f210108010c08070c060213060309060c09051e1203 76
    0x5060701042e6160010b006060300803c80070300c04088002c1c2442a459080030319010090180b242109045c2c442c114001c0b6540c611000d4103000c0409011245240782c4008144040031031604207030340700e51074a0004a400b41c42025000d060b9028803d01c5450b0411010044500d4140c036030b015020540d94146540c0040c10110040c14010f60710401c80503554100071504d07100350308c15404150000d104100401120f807841407400383d014154100c80d030010040a03144e29080d0b000d106035550141d9002c1c00030840c907000e5071061210034020360b02008a6910200034000c4030042039404400b0404d2100000c00156418400507401071054400c5401e01d400d154080b2000d4110400d0b60132070301801b11002180c00c003d200020300509500c4000d119031036591a01070080c1d007000c0c01e880c00f00a101c1846505000780c40c1c04a40007103403503401a9030303920703599440240142001441201c5041c246400b1100d224803c0c0011070680d1801005c00700807100d0303050721800d1765559107415500214107649200340301d042800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 836079973 1250 836078723 836078767
    0xc02090117030409020f070b1f0e19061e050603010302090c03090f0615010206090a0210051b12090103180b010b0d0e0303070c02150f0a120f091b090905030304060b06 73
    0x141d01e41321605890a10400b01c401082c0c03800309c0305468207601c007039100c084e241c3c02110070019603140b0b0f03522070b4000440e00343c4008070050304050034600000759200c00d04001078083c0e010400b00722102034540d0104203a0b4402807201962002150b0701140c0c2981c042c1d0015500814003030f00b11a083c8010b20109420300000b180c51144851940d1020413155070140013142d23001e00a9030280c549008503900003074181c20841c015100700320011440d0b1018030403101d108110194100c0484441c01d03040e058803c01503004501c114006030800740c499240e99080c064101c819a0b0104034448103a0030030380b1408140d084090510046a1107644003e4040000d000541c0a00340a82d0307450240c001900510045020490240e0312a540c204142c00010b0780d00710a03243e040d2514034103110444040000d000c060444681c02c441c08518141c062010462809000a48a1844000c0f8407406580303440c00000c55030f850074040c010350000c000003400190641d005a410365801490b0a0405043c0040c000e40c19140322 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 836081223 1250 836079973 836079997
    0x1020c1e0a030602192604020102070b0f0403121b0b060f060c0a1716023607020d0906090b2203030503040203011d0a260f190c0209011703040902 64
    0x3104400a43c1801c9003074a012203505020000d0341070007a00000980306803c80c0301b41e48072540b020900310383c0b0a115801c004d142c2d8901a03601d170340d0220040c8400f60700c584021615031881d4a00036514034015805520011201124040301414584034000c103044028004c81d8071440e0106c2c42c10040d83c84d18040c01180c0103e0006010459062a0070041c0c011340410a20054030240302d4106021003040c100e040044d4151565150f101034031000b800414400c0001041c18002c60805e500001c0085818a00c504615403ca035000109004195204452406a9000038800600a01a00c42c1d59002480c0d0750340034148000f125070407080b0142d003100c41500100c0c00a00000284800c1d86824054403283c0e18010509408c12800000120340d5403e4140d03006102d156401d6010f120401d0411000052750321050394265201034510800300701d58000c00e880301030a14072821000d14248038160820505501400b041d90316401d04041c01542060080001054842048082004410760000d810091015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 836082473 1250 836081223 836081227
    0x515030f040827041401030b13081c023103140a05010612060f2901020f0123100305071a0c0a0309060e091614090a0f03020909060601020c1e0a030602 66
    0x30100300401d40c1d605c1c22004003003031100f40040c40415840010150403e032040780006a00c03220749400d50030f03402038101c908850623000140ca5107130303c09030b00100b002d03496084503081c02d41c1440c030f510591800c980c400391240d06c1d640b0714144000303000c40201402c0c541803c000c696041e29117035a29800d454141c0c014200f62100034061000700003040c043e0780d60607092804240320400440c1d4080030000300e204440c900c1204151346041103a4000d010300649100c04c0c0c1c2c001d01104501803c104002141080300b84410303107040340040c0e0f021941c124200b0542e0781c028049e29005103084d41d07034940440d4002010321104070401400c003a240c02004429151440307a02c59100652034003101030000c2d400e480768280544601420004c2003502c904603009405030900304031884520589a000f200e0007004100c0d0b0304003503609004900c2640c841d901d80200c1348200e440301ca23155940c0201d40d03101d442c01d446443c0540c0c005100c0c0e021504d0801031286528900313119105400401c0400a4210000d50b48180d03480c40c0c1c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 836083723 1250 836082473 836082547
    0x11d1c2a140d1d2b1515050414150102030c0a110a0506090a0501050a031503060e06071d0f011e0e01030e0f03030606070204110301030803100515030f0408 68
    0x9030034203095004006002500d4416004c10a4009162220403242c10482c50354000d0002c3d0001040031590800030503c880c07091034500074020001a41c12110581c10540006924030307060144240c07440401460303107804d40319400401d960620140c52203056000c00d22400900c8401000b0f00c141507409603010900c220420030038030010349613030341040e030007402c04200d0310b4a83d80301d180386074088030820b10f807031551814525412002081119018030609560080000c1404401e03000200c1001c110000d503038803500c407590300b0348100c201c480300401001628214411140b820303242c810403954042c1007200d502600070414928030440454102c000c5411080084001d580c9171040140580700000100068030240c0421a682d010041c60360703204460024144007103441e590015401500e540741d43c6c5481c1e58481c42c3c200c400e50000c8a01c01410301e0b41e41000074051030200b445041d0300b0900b002503851130f02c5040d40d03160902c1c0c2c01801a100114100b18003202c2c00843e041c0700c4000c0203000345009082030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 836084973 1250 836083723 836083727
    0x504033207172b0b060313030e031f050115030504050d050c010f05040f03020d0203030714030c0f0f0414031204031b0816091506050a110708011d1c2a140d 68
    0x103d00784c0200c3c081e020034070820504105070b03500c98541d980c06007007601110342d840c80000d1502042a40e042c419840c400300344100040c0640046041c2e030141c0a04120503000720313200b01d08646080b170340506950300090010401c02c0c010801000e01130b010300b0002c0703841d80865030840e0580c1c405603030481e00802014400c0d0145a4140948403030506644003440c51802c00c014010b04840e440407041080140001c00304184200c60070445821203000f44070745494100b944090f958580003440741040c5840304d0100108907140203c0d10309002c03c218481c8904050440d101c0000c0c401e8845c0101c030310b4020461012500c0b060800410030f504040d07510707c240b0b135810074444405a928040280c1150094541d092008940100a60301c00010515100c0003811486114500d4007402e40d01088503540b80c1030391144170f034504240700521a101070040701c0d481506003021008208515002c000003840c1190b407841103903104484085102c1c20030942d8039420380c19440d400320050b0107810002607644443d00f002c000c3d603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 836086223 1250 836084973 836084981
    0x112b0c03030f0c02010503220605011403071a070f0609061514010201020c06130f0c0609092405040b0307180902030c010c0512030c0d0504033207172b 66
    0x1640302e00d0943c2e494605a1300282441c000035009204441e0355200c04d03070386401910081c0030308a800c0075082c441540c0d03686620115981544c1c40500a002e0f4403000300744064603203c8a04454040c020302e41c9801441d0710b9501901e40b100e03504850b580e03290303070403000402c00c40d02600300c0b80403040380c0c0700150a280c110f04208591102c254181564014403006240d1400482c1c10f6a029055142c2421018024a40b680c0c1c400501c0e10000e201e81d10404020904940c0034104005581083e241000385000c4130b1005c50625058900c2d5456889003000248100c0c102508400d0001700041e08075800b2070744411007400c080200316246031b800c42e40c0c0d00950055107030800c810b00c410402800c09144010550b104d058a400b284000385180364000000300c7d0420085404407101e031401d0803c10021424070786002440c660004100748a80b60046901c600c0350725903007004203105010307081107924000d80c0c0e9440142c01e03a08808802d000f6001802880420300b00c101d00710041c00024100321900d125981a400115 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 836087473 1250 836086223 836086247
    0x4080d260601051606050f060a0b030f0c0f1201060801170c040b0a120318050405040c060804030903020411090301050c03090703060e0f01020f1201080c1008090c0307060216090504112b0c0303 84
    0x20404d03504108012b407140d10840760494036001c450065562070341c040304414801c03900341072450a0005205403002c4600b81210341a250341e60340d5941c850340e03901c0c02800c4450102e5561040741d000100900c0461030b05a00c0f64106441c00742001c036445a84184000901046580079404101c001c804c1c82044901c82c1401d4002d02421902005142819225084403280d81d016040034004180c000c28140360041c1c02e090015a8000d0041c403065000503030404094121034111802076003400d0214095410582c10360380324889903401455041d14580750140a0306e4900c030a44550f015000c50000791404c00e0004003408000b2040f250b40e0360142c0a050402118140d20400c1c468222041104195481061034401d41080c0c0c98846600d8840c2207049082821110403180d05200d15407000441039000300e40540100303103035030068ec0540d40e6a20001d0503600b044900410050701d95015110700d04d04000f100180c040402105203248500c1c80081045a1070503800f41d0300202c20280030410594005051400c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836088723 1250 836087473 836087479
    0xe060f360126010c0507030c0f0503030a09060b1f0e061215010f0807020706051b010515010f09030b01090e031303080403200d11031207060204080d260601051606050f06 74
    0x28040002c84c000c0076409000001800c00c401c154081080c0200482214010340d080000d4039501e04010560030010b1684003000c0302d155041a84501c018680048218038400e000710940210340d804080840c0c40c00b948814881d4084801c1c000103580c080c807105124450036507920b2141c0d200150b0780003d001307854502d1050741005000002c001c01c0a6010815000711012814083c3c1c503001d044a030345586503500b088041c420342c40c5c0420000480c4601c882d0071f00105080e00d44101d401c825030030407110403003d030201400703480c1a074004110311203c60703019103503840c050300035039061003a0100b02c40014000c2d070f031084d1860308002c1018000d1001c1411941d60700001804014803003250030000c02c1000c0e50442c000342601d100400b485160752001c2c46854107030301ca41580302d40e4402840c5031082c02900240101091441100074050714180102130714807400c00035282680800581000c00041da501c01003003241004014010010101c0d0000c1c026052944144408599450583c522a095610040140c0c2c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 836089973 1250 836088723 836088731
    0x3050a0b090f0309040f0207051609060815011707030f0b1609120212030c10090c1512020901020a1a0f0f010b090d0611070c0e060f36012601 62
    0x410b000000703e41c04910141c50100303400c17549580c00e800070f000b00e12016140340104061014031003000840201514881141044002d45544ca187ea0303802c45081c000300410b050f0001417011950a1f800f10070400c251400b100d000980720f56407059010f5500e041101d026543d00140038100545102c0740d0100034082c602008401c3ca44580d45240d08240f10300a0702804001841c0403103258184100da0b8107042c410120b42d40e9240411411004049440d4180c1d85514441030120b982c01107118940744030b5025988a03078200c8521650341d8003c0d808105080d040d0f11031803072560001000d00304e2952105131501c245401c40d14000241d0f00d54698002c18201c0d880d00380500501040721440c040e141748000c04c0c1c42d944400841d03480c182c802030210300000c0038002d001103941420401c0c1c0101031815994240b01240c05a1213140622081130249900594011032102c0c080323020302d00c0703d0f0300c064101c0a05606040400350100030225004030a801c0080d0500341c0300c0648003e030800d000d2060541d4a0034000300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 836091223 1250 836089973 836089993
    0xa060f0504031d030f0f070512010504020105040513091e02120c01020d030e1203090c0a0906051c020d02040929040b1f0312081006230c01140103050a0b09 68
    0x403e4040361140e61041407804440446042d141001890380c10550442203498038044d03507103003580d680720038450b881c0304032680d248018911070180510b500496042e1a0942001d0818081280c1d0094043c2c4c031100141e034a021410100e00303541060f00e0044084c503520f80c00c101260061028070702d8a021800c3c8540c0c0105216005039900003203c6001e0a4145000100021721401590500da080081c0407008007010080c0711560b500421012000c45040b0394071444030780e540081c0c000341c40030740c86510351200300c007484d20794840d04100600134410702c02800744242c40a0741d8009011251451001c1d255015414400c090108a030b9005540d40301c40708002400c01e1800780e940300c085100003445040340c407114003203001041d07072210010350146902c03e500310401c0e80c42c0c6800411100c0c0c200c40140300f00c1d000742e03400180e0501809038415510380340908050300060202d00f007401988400180d4080c1d650720590320034480e04c002d031200c0c0a58805c0c1e000e80282921400d210200d03110103130040100750081ca1041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 836092473 1250 836091223 836091227
    0x70e0306060d14010e16060207150804031206120303060806060d08030a0c02011506050c16030f020f010e04020c0705090c030f0403030c050706050f0603010509070b0d021606020c0a060f050403 84
    0x203202c0d02a40710034a10492a0942a05400f4181d80d88050910f4403e400304d001161002d14031480640d2202d60880e40025510340503481e10600441168000c0f989020200303000c04d10405031404035220032318001c12001e50b54064041c50610001041c0d00103076840c1400d015214041c02280c1d0401d004a848003003507072540c0c586400300c1c030010b0001100703640d443c140e504416000b0740084980340504011200c102d56221005072681d03010070134424850141c00300216112019150f10010303131f5001011600b68080b15800e1064051002c09030074180a0700390b07011501652140000c00054036000041d00351280b4000c140489001c0181050401d45414400c00c0f120390010b80c1c80710b0f4003a80524000c034942d40300030780554151040f0310f80580070328202400c101107903a00701c0159014032030607002084180e40d0300c0c007056203800c070500480780310301810032000ba074060b4140c0140101800703140d81801c0b0355805540c2c14089a0004007021021740141040800341301c02407007803c0000c0041c807010700c01858603540c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 836093723 1250 836092473 836092489
    0x150f050f01080a090b011d0106090b270a0603090510060e130c03121e020d14090406050d0c03120302070f150b1206010816080712080705030a08070e030606 68
    0x2440381004103040c00188261500d41100300c2454000010a09a507101c00c044201f2030f5003106c051174003081e128000551140720b1350414044a80701d02a1b20300b0719400e011030441091000e49c001c4804c8142070813500c2280e071a036070601d008140d03030348000880306000d1400a0400201d042c83c02c98040c5402c0041160340e81154926900420f443c03080e150042c26858101d085204a0308064240003c03003241c400c040340c000711404589520034010705c0706000741e00401c907a143c95440c001e400041216a0f40c1460300795040107010000320007440896034035125004240745041c8040309803109a40010100284100c403521b00b0401040d03480c040d40b070310400f6110041c0d084402180100300102c40c8000c6802e01c0c41d41c0e0704c00440200010501d0041c0e2880b9090b00b5a2a903081c040c2a8440c0100d0442c118241c4000319281c0444807818041d0154078a02030100d442480300080641d010301c0200418000128107100030704201100d616101c055081c01c0c00001d10741d400e0090700e58007a0f840707a0103002c505e54888203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 836094973 1250 836093723 836093749
    0x6151706091302010507080406050318030304120305060d0b0a020403030e0307031e020d1e060e1504061508060705030712060501080a09060b03031305030d05160314070b0901150f05 79
    0x452102d0030115440100d41c00d10500c2c001500c0e8080200d000300d075507580080194090701c01d1040c011880d04540e2055a180c3c8015500140b03025600d40324020b00d50b000b90030641e1312080003402ca8480d1406502d9100c16020100e50b5640c650b03500150510415402c0740300100b80d41029401030003540d00315030369019810324103400104020003036058001150307201900f10b0b0300154810681c40d000301840004080001e0300c058115400303401c044003103103406c2c4001003c0f80c59490b00f0b0503280c841e8440e074a030134008115071460501c1000c03c001000c01c0b41c880411105018500580d202d590364a41240001c16606c100c80c6035104090410904100aa90210400c0d82210700001c00189040035898054014034004125903007500002c01c0320514402106501000c507030303098080e104040b0600704111810322070f00400741c0404d0458003072580840d00c140318085400550140061402d442034980740b0894400b15101d0301a43c3d100c6000c3e001c0c00c01040c040a0050070583c0392056030b00e080000080c1190030780780d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 836096223 1250 836094973 836094991
    0x905010c02070509181e030913020f040b0f04030609420e0c19080606040b03070b0705030706090b160809030d0b0604090f060512030715020c100615170609 68
    0x1c0034a10000c40078003013031616900c82c00700100355001710b41b4070360f0b180c0c0c02c50000766100342400d092110100c010750086411030840b0b2023060b80380908003800d4401c160480450a408400300348000301c00a1071500c140415940103c41c0c1c030340900c0c07030709151032001c1c0440c60803050150305080e4590701009200410a840411a82011491501e00c0c0101781c503050000c0100d507407121003048040003000040c0c5010054805a800361805a03541d20284410765014000050b0194003408017003051850a40c0075118407489001580d14100c141d03218070301500c2110005442d0010b04c40140281c0c0a451000f0f2100200c1c00e08208600749012001c803901d0b4001d06400d00441d80d00c8010285295845804403805031038400c1e4104803d581494514000b000c40303008090062040607802c81041d02e0000950320300343d40c807103a1a0000c1c064200c01d000a90030030f940f2a4030038032501d08095000a010300615014203803810014281414147c8001c20000c69002200540c8660f10240111910780184041d0301c0040d103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 836097473 1250 836096223 836096251
    0xd020603151008010f12080a2708010c0905010309320a0506150a0311210607120f06291e070606050108060303030a0f0209130905010c02070509 63
    0x4008040c00140e000310307400e507101e005802e50100c91034101c0d900d40d05840c94002c001d09503a84461009803442068540501400414807151003a640b092800000c1c0c1e88040000303c3d103140c015003070f220014546402ca00300c181d45802c0c1941e019035115540c1002482c007440c040c002e4240b29102e84a0281000308200100322081c0d03034400b401d0040c00020340c1e004000b007044501d00361807410107a0700d400041e10141c504680318030028105180840c0d1f01d5058035004035807800c120b4000420400a500c0c0341000660dc0354080c1411100d50343c0c00d0103d01d100708500c1d11000b2002c80e400b40c0030700459100c518103410252603c02c091100b86840141c07640f29241d07401060304c0841e6450101341d5540100000e860104c2912660701908140f0ba202030054a03224610a0140316164001941c8404048400a03003662007400045c040301100d4010031260305d1854801850004001c0c0850300700d540c035144800c03010352552480c404121092282c2050f0344032074409000c400341032000184203944080c001781050101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 836098723 1250 836097473 836097481
    0x10081302130216150e0304060504060f031506080901050601091404110702040c200a1505040c0b0309010603020a0504020406020a02132702100806030309060a1107120506010909020d020603 82
    0x10300d80c110f0b00c1e04444200d00203d07051081c80d2034804071206100701e030115070500c8580315151800005031404d464040d01c5842c245070824004650700344c824088101019105c18203442e10b8202c040140c809044c01e981d4101103441c1030100d060954002429050400c12240340c2080f00360481607114412030b0048401142600500009a5050144d0240a503000f45424507640844c3d40040e2100d550700c5008001c68900d105c00041d103925820507000141014040c9161605020403543c84180c0c0030b8880c400c1c07a05266240da4411409400171115000140e649550500540c031b00003407480b00600046a0540c580741c00c04000a444107600e240003805403944544c00041440c4641020f40300c4009400c82114084110080700100003105900740c1c002c04014400d0203586224030411485648054010740c540744042d018410941e1004c11010200800401c1641d8082400d000c03400c0105648404440504081c0c00c2c85030800f0010f90128000d540342c00c08420060b12a03886459a8540459880307482ea50303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 836099973 1250 836098723 836098759
    0x21060d0203250b0c062205030316110a08030a06050303190e01050415031a060309060121230c0d170d0204050d12030e0c0a0306022109030910081302 65
    0x594018a80c03d00c00442c3e180407201c40010359511030640102d004010044c844040408031010460243c06074000b000052207507180c10540144001d01031400c00c9050b1114008907003007422151080381c082c1400410b0040c0d040407406040040c4c0001c402851803e02c80001001810112200620038400d070200c11504603030181e000d80d0028035080d03051105c1c4001030303c802001041c4541030400b00f00c094206504c42070802c901035074450261800240030766400c21202c5010780034607400840c14055130b00300c8480011506907420b400726070301020400d96a410030100b02d080900c41e0b0300d100d0166403540d0700310000c44c1d001e810b9906074414180045689868544000c000b910070383c0c000603004404040c1180030001c4620380190f0300c40d00c3e03075002c0000140d0b00103180d41b40c903000c0d50aa94481108103090001c920244c0c0240f2031001c0e940150070500d54420044502d02d80200d07070701c2515400c040382d043c9040c1006807154406080605e0002d046280101550680080701400640503217102c12039890881 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 836101223 1250 836099973 836100043
    0x10360b060702060d1509051e06030c060409050612011b0503102121050f0919080601031a06130e07050910031103030306010c03051e21060d0203 63
    0x2034010b00090f03500d000e00c907113103030181880f240340030640880000d0024104a0301d1082d0340c000c0070040f103911075020744100640c0d601c2201400301d940c540101844500140d85050042004011040c4042080d02e025401c100c4210400c9010804990400d02a03c180c01d0b41d20710030300c0c401e140e2410030f9512a1664908102d03a9890354100003001c1402c0c426015039003240140341e00380b45104038014455651201c543c80304a1101040d50400305d01d041c42111135582c0010302808180c1e0f000b91000320407071030302003d000118990358828115a0040401402444032180c804400304801d030f2403032111814090b001c10740c0e4809000200751040e41e201d2400030036210a200c80070044c00d0007004505503082180f03541c0c08010952008842c0849040304080242c10b011056034401c800c144c55018100140d91010b8415921070b921400c24040c4e020507540b540c401140241480c4084901c0013070841e8032034000d80062880c09009a441405a8204500144e40000c1d8003c0810300c2d90140c200081c5031381520403800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 836102473 1250 836101223 836101237
    0x7060c1401060311033a0507020402040605070516030b0609340207120c09050916030b070305070c261b0a0c0b040f0302040c11010510360b06 62
    0x507508082e000014044020004042c030001142515150a40101070244030b94a8600300d030404009090b28425103491101c6801c1e005001e0f00b030241c54005958000b604a070310503005040401c00c04641c64003400360410444409207036021031840e18500390348501c20000001000c0d14403c184846c00a84405040c820801d40d4007086100342903841a10a0f07200301e04044282220014410b960380041c04061500508020303d40001d8002020307401c1064400241400800c0d03040b00703105216110724025113284916008601070042031480d814140b4004043e180b0180c140f408000380004807601080903000e40001c1c9800c0c900c030507001040705458903400c5010b8031102d4210384007200400001c28402007142c0800c00d118415041d0000e8460b04c685200c4c1c0914040c04144040042d03042c00142425489545200d00340d0400c00c11140c5003080a5007998000c0703a0804100403400340400041405803802080c145c00500f41000e620401d000c0d601501c442c402c0380241181e100c080c00c01c050b0712600200c0710a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 836103723 1250 836102473 836102513
    0x507061b080603010614060a0302130f031a010302100305061c080405090c0c0738091003020f070303151508040b07020c01090b030403030b040501090915090507060c 72
    0x140c000024550385800285030304003003020140001d00503d0107210307040540b00400404104107404a0034441c141e082a064142416803c0050302c1c1480058014400100076018119500604501d08000248100c0c490044940540300061006980358115414949c403c0c0c0f400080d550745140000f120180030030001d02c03034412400061002c0c010810000e00544400761070dc820603884503554000c1c10710984805005da500801c0040c4480134828544c241e40f06d4038811080b55000c48400801e083e46200401c00c907201c040042c064250703081a4180b0031007424079040450074510b4504200d102803041d12001001c144d500d04080c80906203112400000d800e80c4c000803602442950700c09420044151401d6500f411110300141d0014800120305943d0a0107070740368446a441c0c000040103681000e8001c41c181030700e40095030820b0311944160b600a0405680120f02c2d813210741010308811411110761012541005e01c51000f0070750004a0360110f680301c2c0b500c10008943c2e802d0840f0003d0006a03c00d41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 836104973 1250 836103723 836103731
    0x105031009050a021206030c15030a090501150810050118180609051608060103020a12030314070519080f040b071403090102270310180c03051501120b16050706 70
    0x9101c90306139018001c00c404020072218076403513020805030344a180c0c0e8101a400686c07600b1800b00c03907450101031504040141c02c0803c1f81012030359581e09488100c40009002052100c003000b0203407007006014040c905a03d400c112079414014000000719464045040140d2243c4000b2500d000c0d0b444106a01c030f41105042001d00f805150450710b50384c82842690210b41c00740e001095080d0003181c1e042c100c80d4010a8058182d1030b2020180e501d03442100140c06041e0754000b1500002080d038102e40c4038040d01d07990982d0350000d210103000c03201da1204085040145070b001b003040c10511081c03629003003500201004426074400e841101c28188140703024000321030110a0088003101500902a03405281c4103411040340c1c511200040c140d0001d01c2240c1c5903120684520340d140003907000b0920740c1c051240f20440545107440d00c0301d400605e0f500445140c5e22803501181c2484100d041745000d440101040c4009240c5074a612195410181803400102d0b00e000c6c24280315801142129090341d40403100384 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 836106223 1250 836104973 836104981
    0xc20030906031608160207050103051806040302070306060b0408060a0f090804032004020711130b03031c05010b1c0b01090f260105070f0e0a0506030c0a1814010503100905 75
    0x440200f12207507460085028580824202d03068403140c2001d8a00540c01850090b140800441c090040030342081740380181e01e03051302400507007030102900c50b0303010381c00801c9940c0c40c41ca800b0045841a44c0803180010046c070050020020229980c0d4005c00c0003400072819026070342c0410010310b2601d03030040c0003981c0003a001080000100b0081480d01104584500a80c2c00034184000da20070b07010020f00d8010480382002d958540200707240305241c1c15800001e90040d01c8404280b460381b006040000c060128490485001000d004150142c640c0041003420155500309204002045600c81480e840d190124107003241d20036103081c0c0083c0031034400001d1241d40d03001d00c1402100029001001c14000c1d082c80d881c40c440c1402818010f003030700e85e42c00300c40c10000541124031214003104203a101c03246080c0047e1517565040035501624501d1790450b5281d1003480c0141081002c000c0d4401001c0102078104442511400b42154044003030a0040c0d40790384066034410070b00e10b00c2d0001114145400c00348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 836107473 1250 836106223 836106241
    0x5060705151006030b030a03050a111e0a021903030516061104061d1e0f040605150a20030d0e0c040905030903070501110607110a14011407030c2003090603 68
    0x40b2044802c540c40070011305e400c0505043d01d034103072010003401169003005511981489021411030f064a0001601e00d52411410508541507d0540d82c00c0c060b8001c40c0b040302540391481c81c29079421300d003c1c41111000c1c42c42e030b8040c0c103600030300700414082001c400f002c00074001380d80c002d00d140c0c001c080d0545951381e88400018103484002904003180c808459000202410000a298482c0928031045042c1001000821415080d907420740c0e60481d443d00000605a00c4448400c1e4031051000555038540110f240d0080080b500d200320080c2d828500114140c403141c020080300c03440d107040c4201051000354182210728224400c085250014507140100061000c040041e107820032046043d520f00caa0703038100440c0c2401085a81042c503400101c003260006010342811404031500f041074900d21400e6403175092848070245040b51030360351281c65022001d11520405a88580c2c2424200f02210385400000c2081002004a900400c8002c44980c00440104103447c41107a00501041d41e81c030b40100c02e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 836108723 1250 836107473 836107501
    0xe301603081602030c0a02240f04080c03070627030510091b06021c03110d0f060b0703051b10110c01050108030406021c200c0111160506070515 63
    0x242c092801000529012010320104c1241c21507003404004000d128010340070050950459044541841007140c0007d03080042035020b0726200d4104041d8031b0b2242d00e000c68503801c203e511340640c0d102e504400d9042c8540758001940841c1c000b4aa41825010b203409204002c54030750340e410240807440b8103080da59048001fa0020f410151059902c0c0000d049814110b1040b2045400391201603004aa00800708100640c064155880f05180100d0707044410005880b041d030108224440f140d40342e0361040340740355180c01100010f02410701302c1460b0204a4800501c18080c0190030100584218281103003010308000c96205029003030810003829500e0f0b250400316074480c8d045420294200000000c0718600401680c1c211101900a40918002ea908904003901840d9080d010300c040c44403904d0038228250210b001c0315090500600c0305c100d1041c005040c00041c40104081c03036209032050755210020506160466405031942a200e20152406d1418140081c0407841d041c45100d040040f0f105070360329 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 836109973 1250 836108723 836108731
    0x40216050f0d030e0a030804050312011d012918120106030201080105030724030207213b01120f060302010f02031327090c05040e30160308 61
    0x104a40072160403030b205400352981c0508071407090300110070400111b80560f040c1c5a00c18841c00540c0c0c40d01429021840910900f80c000e034512010703400fa4051035200c00c80c00365000d0103200d070990303c0002100310f141254038000c0c20f8440c0380400200313840911403100c4000c0202060024004605609212111402050700d031000340c2c0042c1c40030b03000080300c0c01c0101c0c540069855040d80d401c0726000f074051012000d0307002c480d9481015404c100240110b800303605a09140c0711814040c0130038038283c141c01409481012411654004030f01c252683c102060840c140d0f2518140b6100c9400a54250040c1d5005101c407080031801821320640740141d000590280055074400d0320740441484154000b01d03036901514940c40045c0d00050010f001100c0c5242e031030186401c041c0401c02c04c003810106002c0542e210312400302d071040b2080f031043c07080d4070303050080c0030307040e0040f6009050b40300e5030341b601000142d40040ba1000d00340e031034048180030054503002c4034441d000a00814a241e00140350080910307104803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 836111223 1250 836109973 836110003
    0x9061201141504030203100e0f0a03050403060522060f0216060209040c020d0206011e090219020d02030702130b1206041a22020f030304211202010516080604021605 72
    0x1c40341808100c1041c0c280c3e4140c9070003500400481c02c01c001041d0040032808124800c1e4890079584155505c001c21207240034074440e075503464072149945441000d885000d0f00608094616031005000303001990b141a4207260001c0010607100752041c6000c0082c070500d0300d24900c0108403480e50301403210640080042203800da4040024658500c01240c03900e1400180c9001604210b004110843c1550701c5011b10040e0110904007050b0348165070400c9030701c401c0851150342a800b4800300d2280d018042041c402441e40043c3d0b06e0300702d555001a2300c040c4006291402c4a0703913034450140a8035418131541c0c4840f5202d0440b8003500300b0303003015010120a4600741840d0420000002c03a41c6412504200340c1c04c801d48004d28a9940710381c01c000120055200b003c1c0c1500c400d0000198111a15090341444d59410352505203405036820545803030b6070310b20840804c0d68104070910951401812000d20701c07008a142102058a803200014060300c14404441c40242c083c3d41c951081c0800032801064a6850b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 836112473 1250 836111223 836111239
    0x60305060f0403200304090504050a0c060f09062001090305070c0504060b0306040507171f1208090607050a0602040b0418060311130603230706180306020906120114 72
    0x307140006075845003101e0003000188411100e48100d8904139a928280701c20405903030074a0745400000301240d4003143c050300d5a501005001050050140d0440054512807500d0f480b80c01803140d02411004092044504004910360440b6541030441042d4001a411000a120740340040c14028001e402c024020307140c0041000000529203412b1040c501203441d00000746086990310b108000c01040014480320901011101c1c01c1011203101c074805104400030207400f8130880385620203c81410b01070300100c0d800c00350151900081403100003560740e6054103d4000d1703030b15402d0385130840c101490410001c00990000c100800e03441403450280c016180b042200f00c5208400e20045820b56515100142811205110b003641701c0c18041003411103198000360100d03010b5520b913100c000180e00310200e464048012f5814502e0394000b80710503402000c40b40b800d4120321f504044030046880852000034071a9a001a1588e095203600041d502c03110785101e00d05a29603961050b1003181048000514852800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 836113723 1250 836112473 836112481
    0xa020d090e0610030509031b0706031406030a0210051e090405390915030117070f0521030a0e131a06090d20030c0409030e01030914010603030306030506 67
    0x90100180b2440c002040e00c41503c0518005400030302001d42801c01034002048110b4400d84503004148a242440c2c0040174140d143c100300804545402104004c005082c00510074142d40000f403401100383c045556610701ca020741c609444034415021410f0741c1541d8045c0309444440004040c240180041c3d5040c0550b9682060002311203451445580300c4d80d1000c4041d4000f800380b10346021100c4c80d480303900c52030003459100199640100e0010000000c80010051200700d044070354480c4a21104c20041040ca82408443d80c400e030020f004142c0100d0f030307109800701c8500c0f082c84080c010f0300c13281003600d41d50703a2000f5000f801948200012401251080101d802c054041d1141c040c22000c0150355003810301c10b140402100740d01c0b000745a076114500c00c800d407011410359000d1108401103082420200c2c28040241410040d010440505c194a406c07400000f183e0414640321044030b091034001003003a5646001a512a4022200007032980b0740040441015010752040e41503030300440c21900d4aaa03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 836114973 1250 836113723 836113739
    0xa03170c16110105130306090210080c0a0f120e06040309290f070618060b24090307030c080a0507080615010c080c06040303020405040506010c0209130302010e030a020d09 75
    0x104510541142070341c800d5003200410311142c1c010152400500d422440c004c1a100d0306140314240750015254140d950120004520b0002c001c20501c1d401410b18034a5442c1804410043e0700540700c60801784084d50310030110030381c4640410031003042c0030030341000a4000302264030380e1504201c504034049000c00b40c0105d50505441c07040e1125020100c52840d0240c00269105c0c081e40007203581c41c046803000c2c096440042c10740c0c00780742e101c180010b800301c0040c0c2c00d1303041100940f40454100c9001d80448151900c0d940e0300303807190a460725504440b8543e2040c409003c41d00d05095a071001e041613500c9039000c0303241d16000c03c0320001139002c3e50488040c0c5455500c696151300d0191880360344401620302c1c181c0320b54003810003403d9140c0100001341c24a65000c1c0c915003800c404480840009a0020b02848140b0380b500c10103411040a1900340d0480b041c82d03005c2805064046c0010900205282c01c9604041c0b00350842441c248100c4180ca45a0117444d102a581c1d01c3c0b5060400c0129120b007102181c0741d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 836116223 1250 836114973 836114977
    0xf0f090e1203060d11130c02100606090504090816030f11010b0f220f06050a08010c090b0f160602031509071205040309081f0e031e13080a03170c 64
    0x4901c0300d0054a50303258202000b22102007100e048400422180b4201001d54402252101d40f541c40c0e14081419140c03090024182142811061200c0d840d00000384540d030350082101003680c00c1078600256180c0e15082140340c41c052203240d1102ea0b070001c0581010154003201c15080607255886030380c0300000900303005081e03c500710000f58125044807525003240c6030020960540340b003001514032001d0513585490341510004140f115040751241c900f0012070030180510720041009100802205c88000f8004080041c14456031541c036a002c143d0004048500e002c9501050380712440301401d14551600300e01a404c1241c21441c040391040b401c070300b141400e180c0d040c85180a9620b5042c2c0b0136046413280000c18001d8401e6080001000700031511010410004e0102070f0311810f009408600c1216a0307042e0b407080c0046c0601138200f8015400b600f0310b5683c5040104041460040d00d4541510200c0c64040895004008034422a070040c401e1582111030841041c4c240407880d182541d440c02c070b482c094 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 836117473 1250 836116223 836116243
    0x60601030b150d0902061305131b0e0307150909110f0301120c0f03030c0606060509060f210103210c0b0403030b030c0303040b120609041205130f0f090e 67
    0x2034540d110205140c1c001009000840150b2000034520300a45c000c154030350002003002c10f018944440c180007900c0c00505401103080e5860083c000c1d005003c0103d50343c2ca14540540702480325101c1210080e0b6400e100300c5024041824100d4046c02c00c01c00c009020300703410700c2414036036482d0030788070340d10310000c2011100003a44000d14645141d18003210302103045e0b07003860309680d4983c21403070105084004500303500003180207a8139043c50011a0401d281110841d0303000f00d040c007404008007103d507260350044d40c200320440260341e5101c070700b03030000b0b03c0348007035040341d07018404903003500120030010300c40c1b0482c1070524404a840321780550200306036a10424400050402101d00c000503001900c40d401035096050007409954140a012020074030310f0b000f030340020319004804503061804500340c4400d44c0d40b25500f243c0fa04400c0c10191644480e600101444030108500007840300d04624580c4900c0b4010b00555403030b0180c05a445074002c14245803070040c83d80d00381c100f075500c1001c01c2002440b0003407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 836118723 1250 836117473 836117479
    0x2f03031501121103010506130e0c0d0c020c1c060609110a1d13090501090209160e0102060f060103051b1c050705093f0a03090609060203040303121d0109020102060601030b 75
    0x342d031b400c100420005410136020b0480c4a0707941c07070010501907a40c03846140262540005691550000c034007500586401c05940750865009204500040d40c840c0800114161005551102c0d07015a0600c1d0b00501942d800100c055400c01c00044544c40e803090040c208491169034900308103080030711145000204800096101b003080c00142024002580100c0c099403045000140301022075000c10210101250725000261853f40b000300f0b0550403400403245d066007403016181d10f01d0311665124038020702801c040e040541d9800080c940c149003203252601030780e841980d1512540c0c11040100d28134090f90400c2d01c082c4c180000b140d203007801081901d004540081000162801c89450020f5038400d010943c89169181101c09030342e1400d41c0002c05035015010043d19465140d4200500760528550002c0200a4500700070403001d41d020094074140c81c0c2c5803500807400f0340d078810400060081c1c0d210582c1c5d14958845c0b60810200158400301c00940300781c00755030711aa21800150102d4240e241b0f40f5030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 836119973 1250 836118723 836118727
    0xa0b03010902030601030e010c0210051006050711030717060610050315010c0516030c03050705010207030b0c210703050f0604050114122d0105010b07032f030315011211 74
    0x541241c0340c000d1941310b1810f2600041e849a03034400182074485a03810071000d600a100000400101030040c0c642c0304201c0303404091180d00c0c01c1c0c0000c14a00c54500082c6c5001099000442a0741d001c7c81100014080000d035181c0303d803008500141c41e070790160b400900c901c01d601c04034031840b40034105481c420000300c414801c280321000015241c00350301a0302260107014241c100b10b0007141080081c0c0156004a442e07181090461500c0780c83d00f191a0485410b55001e003500300001602075150035400740e0f4008450740c844d0307141c6e541200d140084101643c10380c0c002c4c03030402144c1c561550205200d5200500c01442c15216803062000b225000e001e002042da80040c60413045090032058110325810b10f43c1125810281c401000c141c0d005d404115007906480001c0d00840500240641070151500358102442d000541c0d40103040544d50000804074038049d10030728035140c00c520000e0403104040c102501c0c2d4070314100003402d40c08002a00c0c4c444c017085451a046484174a0b52003803010110a020080d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 836121223 1250 836119973 836119979
    0x40c0e0d0501060306020313051e060601050d0207021512060901082d101d010510030b0403020c03010903030203070315051509060c0f160608091c0c061404020307050a0b0301 76
    0x82164950004107460039900c80e9400800940e2a200652256a41c90b1158641c0080c5181c01401d002d44032801011140700c041000300c210801190310f90300441c00b42403480c0c4d10706e80383c04018040e00030354201a62107628426800007044d01080144161440300f444100c0e50350303e100400c48412030071f0250308003680c030000c01c5080908041114991507001c0403598442290344c40c4506142c41e00000c00407851586504428480c178000303040070b03124031005000034030103490014412240c3c16100d1001070075115501c800714041c18000d2101055981d800f400a0015454900740a0083c0d88142d0b01c2100192602007601510000c071071082c1e040e900018808040d403810120740043e190043d072942584044100702c8498051420031040446960a40280411081981f560035100da072580c800d409100100040101c401c9000c284403068035103808284030717000d188040c11581c3d02e500c104024a19440d110f240820704003440c041c00d00c03c610072812900e600d6156001e00c00caa040900c1180c407145803d00041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 836122473 1250 836121223 836121229
    0x1b07030e040b04020417030d050c190f0311071b080106080c090406061e0602010605060316080a20030a05010b0c060a0c0509130209100905030d03090c03050609060702010b040c0e 78
    0x70b600300002030000d400c068980e0b4408005041d20044e0f202035a000103a982100c000380d01982e6445842002100d040c005180081500741100b041d62000b08400c40700c011882a0081c0e004035598610140700640746c03041440d05101f141d09444404018400110000542c04414000c4070103691064001c1c08041c4022000e0080c0c034000904112011521100007040301107858075071000000b603141c0c12009840c50080c010342110025000350740034001c1001004086004212071210602070351520b075103640d80d540b807400b004010301011641d01083c441d002c0301da4000d0100285000c0c00701c8200c10000381c3d070385400c03050491041c105000c1c415008400065520412540035610810860401514180c0d8100001c1c103d00c0502c44d0344100e540d401310f00c840c49418001d422240c3d842841c2410801a0b0178600000d64414142c5281010180c9804441c0308014080c51828000c5502808440035810040c20180d01c80310202d030540d00541c0b8042480c44549003e00840501c070a02d0345608014142c0b60b014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 836123723 1250 836122473 836122481
    0x1140316270b04090503280e13150f06030608030301030b010b0c031204031d030a02030303191803020105011505090603070302090111070602280c050418080c01051b07030e04 76
    0x60301d46042c0e514460300c0c01da503d544c01204076507489600550360b00da0110304018540031141d031071308a900025080d2840c0c2e894108100403001070040310464503d00000c4000d8000d8214041c52040121008200251900766450100240d0741c0c1602c0c10f005003030b2a500101c0d900d000034400642155100001044140c3c005c0d001040d842180d4400e0700e14184e503c0800740f650303050940e01280011914601840001c0001e4919880c81c803040b0042d0190010030380000e40d903404013608a0202031320f201030b20300011029a024104646003080034012255190070081c0c02030600348202e602032030802500c220580d02c600308441c0b403004001c3c091403c41d15141d40c00c40094000b42d100c20306000c2c00b480011a002c000700842c000a01407603000b80b00704003580c1048004070210240706c1c2d4403054031030904c000141d101000070341900d07410355002410030750344400040c4505c42301c40060072450700040c00150f0711806410a510441e410f0281d03400e4040080c80302c91032407207018005000245824984003813071810b45c01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 836124973 1250 836123723 836123789
    0xc030c070f08040b12060d030f12061214010b1c03030b0607082d1c0c1412070207060f08060405100b18040b0607050a0b071701140316 59
    0x4454640c4590359034008050344284c01c080544000491041000710b080240b40340d0212080d5a03c0c1e84110303c541c0c000e081585107402d030780140600000e9440e1030314400c0d40003500400304c0c0e80005030300448a040030410004e03070704081400355003022240c100504061040c0d101c00620312a02507081c150039117085005000840e00e00783e210701c08124400110307568901620107061013940450908102e1030b0004448561803180101516043c0801881e5402e8880c100000c60340c540004070f01030200e540e04a800b5140454030410720007010420700300d150a2100441c1c070864035902240c60241d00c0320400d5417080400e210480000324501c0000f03400d41030581100b5000302805079252040c07912007054480070b40005151483c4160310a440c0c0c911490540030b8690041400e942052403d82140c032066182c843c2c0510141140c40c590b80403501c018420100700058005000c0d4403500742d61115070b2403218081c106e682610a2246000020ba12403902e031001e030485036003000e0b01d8410700100d40c00141a00c8208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 836126223 1250 836124973 836124983
    0x1806020f0d0207060e0c0108060a0302090a09170406030c020c0922140a02190812030414031b0c09101a0f120402090f06010509062a030a030e01050c030c07 68
    0x101011104410380c1c0007804103c0d1148101280d440701d0250340074a4a5031120f01030341000b405106020031601e440a64000b0b03a601a00c03c10016580c01c042c1001801c0034020017040188106544104d85007400c002c1c0c402c1e42c1d0740740d80600203d4840c0c00c0c102d80d54800d0240740c65000b114280454041e01c044814094021020302d074011120a140c0c40e544650300e1205042c1c0800e40002c4c1203030f0114034082c2c4800120783c44800050220506014640d0342c4c90030240913040030154000089814481c070030898200c00465001103c1c0c3c0c43c14903036003441c1101c42801c1403000314030850030342a4003803a082102512600039100d1a580c15481c1a0594103455a94106000c00f140100092040c3c1c038002001011600c0740f41410185604041c4148400008004c168103035400c03005082c0031007a03030301c8411155800390455140b40c076603440d001c2448200b8100c00c2000700840c81e122140f1804100400a030650240d81c0c0c50400c801340311a013090b826203030308564500d2100802c20001e031012540b01c000d85801402a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 836127473 1250 836126223 836126227
    0x122f031e010e150108010c051e030c0708031005041103070c02010f0509060c010203070206092b09080105090f0d03231e0a1505010302040b12061f0509090a1806020f 72
    0x8070b14542c00e024031031819101ca0300b44080140903a41090140342c9103c0214602289000142140c00300084600c1c02c0d1041403180c008082400c07861020162601903070441d000c0c59807400c105071105042010307441480e004c3c504000012900c00c10000a81c4d106408986400f01c903100d00c0d900440b041a507420884040c48402d1010400644801014200e8440c04000050b170b28202400302928064000b08200000c0d80508498440c0c407a07080c60103c00000c0c0e04581e04c2c030307104505078241c070b001801343c100f141550b180a00704451103200040c20340401c510342080e907004d14030042e821800c0c0e945902000c00c0c80402e010f030441e8594001d00005a100015901e05500706041203040c0c020020181e0713182c4000b945032a41107084000030400c0000400302401d08610b407a20700b11640f001402840580e16255401c60000307005038503448e6001600000346018651356510340c4d100134145402500c442d038001d041500000c2c0d151406841482034020100c5035402c0803c4d61552144040d41c408103150032441e82c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 836128723 1250 836127473 836127491
    0x10110301180b040e030d0522050322051210050609010b04051212031003050c030303010e0f0a0b03010f0906151d100f0f0302090f19090309122f031e01 66
    0x13085c4043e1070b401c144200049040d04000205e1076802c8600380b40e0790b00080c00f0130705203000101c0010032074071801ca503810482014400159195501c0c007141d4000342d00020741c12004125000c01103040f8408650056041145e601d501d401d02c00408000d0252181014003040b05019520b010803140c040c6810040c1258110142018000c0c0305030025190504440e03000c0f4000e00401109000750000300000740c00179421989420104600346501415030400e40c1c042401080000119420007030240101a00910610b07007155404c10081a042005440440c6440012242044102c00b0001244c40d08440407d80315403000c080181e541c40a8083c4403886118200020b804018200c45801028030160420801c0d00d580140520704500400311581059803100f0001d042860581c03803404600025030001d00707040b1610782560a03100c3c0d904544018451000030108204400c101e0030320b00c041c43c40718912803500404d00340d105403d40d241410343c107400108811b00c0007501c241c0201114a80c405c0042141e1034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 836129973 1250 836128723 836128751
    0x102100b03011107060204060909050c0a082d1b040b0306011b0510050612011803181701020d0e07060c0b040c03151a01020a0c17010b100210110301180b04 68
    0x4c4841822621150041010000b59800440c940c0c002c01d09000c09204524000c0b032641010b10540a9440601c100c2d0404180e80f013440005400d41d1404002d02d59031503540e8010744040703012007100c0c10340340e0000442901032940c0b040c01c141c504440082c2c00060864649000540301200201c2d102034180544845007004900d082004c2d885500803010700041c14113118050010880e01c0c04002c421580c1480030f03800c100102140140712450300740c500321051a00c10881c0070403030380e01c903030059180d44000300b40221641e42c103500030078400d600084200410100c003103081d134031925103100d00d00c00318880400b941e01044080780f4459020b40328800d2807007400d440f80d13581000070502c5400c1041413540c4481c0c0b9051212000b030041d041d054240010315050f41c4943d12000d4000e114018004010100c00d420031101c1425001412283c00003000301260944801000356034000510303201444500303242d0744174403044002c01240e040c1c904d542181c1040d4500540440d0140030203031855a0080c3d40c8000010800b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 836131223 1250 836129973 836129977
    0x90e03210106080c070809010c06111b0d2a0f0605040302160b13030212010225031206140d02030c1302120c040605030711120a0903140a020102100b030111 68
    0x56164111180c0c0d5040c42c00c000c240801c014072a8101c00c9007042640041011081941d412030400d223090503c00c40301d894104080d005501c19800c0c445400b1404400c41006403c2000c91041c040c0111440c455030b84c202110101403c0381440040c081c0d00d4103a0900c000c481c80070000c03040c0151320302d080130f000542d10842101c6003114240c005811040c041042180d01e50592001061428603080c02c080c2e1400c0148148041c5100003481403042c5000c010300b0103401c0d0152105948010284618070071040ac03910315010903548201c0024007041b040007901c00d90303032080320181c0b14081c880300c180c80000402e00c202405007400c26a89403080030440645503403a07000f441c0c0c81c2c11418101685a60340e042507091101f078064000b030a40d0a0a11083c01003550220a4a0380b160f040e10709200c0e96040b5900303240c02e200a650120009003030001c0d80c0145a90040d0560046900c07460140340800b00384140c413611129079910003401a04000880b14001c45590820016000b00400024034140c60034003070040c80e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 836132473 1250 836131223 836131267
    0x241911030415031b08060d0c1a03010302100206010602071502010e0609030c100509150414010212040b0601030e0c060c0129010e01090e0a11270f0607050601090e03 72
    0x38802d01c215212240c1e0b8103020f0445010507002c0c210000c01026940a042c41c00c000b00700d103000d6158031f4240414403c01c1e0303201000410160002400400c0b1001c0c464840c0d03402400305a0090711124040008140700042250403503030240c0c0680811400c10002d0303800c2480134814102150348807031055401103002c1c4040c50003500141c0c0210368561150010780d042c050a000404401c3e440c0004000d007600012440a4624914030101a502e80d920304e0300d40070a1480000004196102188180e0406c02c0940c00c540110b002c0d2801a201d5500d0000450503945024407c0705d032500108003903041410542e009d42071541500001050703081070f00f0052041c2104e2840d001795114400b004100e19540c100c07543c02c040328000c3c41c09038003050074006030070708648010349201c1e000b956400e07010141c090207409850f00e021900002050340000f150041c010132405810b950f10440d8210310f008001d152240440d02c1499104014003803503840c4c00e0140300104180d409500130303804200720413080c541c07411200701c0074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 836133723 1250 836132473 836132489
    0x31a04082d120f07020a15021605030f04050f04180b040804080118350f07080307030b040e010204080d0c06140403080a0e0309150a03090c080a022419110304 69
    0x80c3c905216242040355010740742200355005030442d4008506580003041d001c08403140702680e10f010142000703c108440ca500540940800f042300641c42c8020002807003152021200071041000b01010041250650400c1c05075009101000c18000358480b07da86500078083e03288c2c6400c02d9500c5c031000d0b003903800001d8180c20700a80e4505840400c0114021700600d034100035080c180340d18401080444501603142c40040c0c40c100410322201e56800e840444000940c08050292a41441c020203406040c400c0f007483c4c170071420401010200c80051080c1c03000c54000000400e40703064504010b6804040303103003060317070070701d8607041c1c00440394000801c620f002d188640e40d0540e851811081c014105c5082c41e0040300035400070060b0320001c1d42c520002050722001001c120341d442038940410750003400210002070044180010000e0070485c0401c001305030034000d9559100d9031601c0c0300e84032241d21a109078200e589000340509503c0e0380e044900940a070b0014103100d8001c520400038680746801c264007000ba = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 836134973 1250 836133723 836133757
    0x72d020f0609030903060f18012c060405030a110f071707080a241508030c070801060b0d05040c0909080306150304050d0302030c0702120106031a04082d 67
    0x12100030100205580240a40061030910549100007521035a000d0103c3c40b81140724800300340d1030131800441e02641c940001c02002406141000d501c00f11070540e03011510210005c0a074940c50b00081a00381c895680f08002c0c2d440c0c10709022081c0c0341c4e486606c1d240100382c411541110407010081050078007410600c0317075004031802e4004000b0300d07014480c0c000700b101c3e8110950400c0003174003d0b1000c02006850319100c2c40040c1401840320010115440707041c4030500c03507910005410702c0100040c140c0011841c203460240d40c48d88107a03800d0b503015228660034101d0400588011140642c0000e81281c820301c00403100e15590240c40d4207648a4040130b03606010000284030803481d091800c41000d070b207000006411480c042d240d59844240203642c84050580000014400c284044110b440250f801070900e5581c00132403e9244c001c050030b000460750301d05400d0f00e226441c4e41031448184900d500c41d0220b40740450601d0760b501c819060a2901d0780c2c0e42208800c0507601d11240001c0c060204092500344 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 836136223 1250 836134973 836134993
    0x30603050a0c0f080706020c0103021b15071d010c2a030b10050901270e0331050a060c17030408180906130911030102040609090b1008072d02 62
    0x2420705241d100c0984c0d5441072008003c42c540109240103c0042400c0042e00e840d40c4034211101d000c1ca165451030311380070700c841202110071906d8486010300201c0e41c3c0c8064195800740e2a100ba8445840024041035401750802c0008881d54041c19600004020305010608030b03e48074a24a1020b80007120302c0807146080048c0d04915815400042500312019004c40d45480c00680d0b03882c4213400003010a007880480815030840c03a4200b00da4503960303070040780c0d035410384213190000403030b41e03000380c0051484801200d07155031307031111229410389000070540c0c2005031601d001600c10459041045408540c090b1918210b02c2140001d0740c1310303d014890250355a8030241c074603480d0032070300c603d51840740d18a142480440d403036003044141c0a141c0207400095018450800340e242102e078058095140d8000540850283e40c0007003050111061140280481e004460030441482e40c1d4680d42c0c800500800001207540f4841e5049509108010f102d451880200e4583d0f48041c2542011203000343c2d0202100e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 836137473 1250 836136223 836136239
    0x3020603090f07081c0e090703020702040b0a06020d030501080f1f0f11040509061e100c05060705091912060218120607120b091515190807080f0a020a030603050a0c 72
    0x101c0b0300e0840352034a8281b80300143e0005080ea10080e000004040c1c0c00f00d020000c54072030b41d004203441400100050752280c0d603901c00035070310010010590002814800006a4440c00080d1000340045c940c000c1c0064482d0360380c04403084046540c0300084035444a450b61900c0c8401d01c40c0b01491070204149503030b202d0624007442803121000e0001c5005007009400f18007200980034000c4800d8000700c43d10072043c900b4034000c07a0103000240c030181960061002707000b1582c3d0850010441d0110982e5490307028204101c0c00002000f00c1d2049184420403c8112400101158002c0c40c0403011620166124001e080224000881001c6014005d030b00c84c406000710346802410000200121030740600840303d10701d000c2100480b001c0c0103640b401c460030041c82065a02c0c44840304100c1c403581d01c06078846284804a2203078441021180021071240c8020840c468071501a05104500f404030803041902c034000010025030202d5000d4040695600e0080b0001e4000e0001d81c0301c1c14040c061302c924944c100000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 836138723 1250 836137473 836137513
    0xd15090318060e03121b060a060e0912220e040b070e10050403020d030212030405010615050306010c030809031306030228210902040f1a010f0903020603090f0708 71
    0x405010048403c8125690002140c3c3c08020801c1030080c0c0782c90f07034000d101e0680455404032000d203018400c10011901c000b0390080c800c81e10428a4818691188140561680300781c0c480c2c2d1114500400003c042036440648030341e410348084980e85036190b03596481258240040d50102e03104041402802080c59000452100d0035030201c40390700000d003216102505034895440002d02400c050484407040c50b0007800b0600d94481e00030700c0390f550381c41c00303280150080466000d6000200c01c50010f41291030303c9882130320300c203000607124804154810b4500f51946180181012202e210400c48464100e200842c0d000007003041b91400341c2c5910b000d0210290003146503040402c4a1690f46684080c2c0350302002500b00901d41c0046407803250603078444140909080140650801d081828004d40c02015901044a990424030361081240c100c1004482080c2030003070010024011110600251030000300440c0c00c403c0d510221000340403010051801c184be250f20800f0a5084001d0300754848114100d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 836139973 1250 836138723 836138729
    0x803060f040509070e0a0f0203100602011823071e05011416080a030207020a0f0501030f09121b12020d110127050f0604050706090905060f0d15090318 66
    0x7014040d41c035107891034540d200d400380b08501401413010041a407082032030b844099028815a8150342c0c0e85801020080d43d8030031481101d005601e00048100072403460340450000f25841650411049000c5802d4520203c0414204910780607070b403000644240c1c4100442002c0c00754243e910040b6240c1400580340205007003d080000008020013000d4100380512525456400355043c2d441d649840800c40080c01020030094009c60700a401140c10031030f407003041040728002d076810700082042d0f0341003c084c0d030505500144010b51001c400c030f850a024542036074080c52503080c0c5807146015606c4451074403c1812840303002da0000c0302c0c40315681e80e105444090b030b004118000d000e4a061076041d641d400c085030030302e00c59240c1e14407081010403405002c1c0c40303091040303802210f00509240c100961502801d11400b40170840000300052000c5036406014410540140541c0240554200340715500041c43c0342204e540c0e8440541c00c41a1a29200c3e03848403d000b0394580300d0112102c101c940d60300c02260 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 836141223 1250 836139973 836139979
    0x50c10061806120209090a0b0103060204260a03050904240f060203130e19020c1b010e01020a02061b030f1812060403200706030b1e09010e060f06070803060f 69
    0x107141444410020760311160342c944d0603101030f00550340c0c40030786d18249550100010010200c0340000018044641c0142c002c0e42d19050307600d07030103034a5510310250f08080748140e140d02c1e4000010010119010380301030031540002400104401c900100f81c0c21804202c50340c0548084912502403105512503601034029080e140000c1d031400081c0820980303d00c000344100304c07241c5040c400095150b69086c43c8120801e250313500a64654401d0b04000740c5514a10f10a400c203100080c10703900705584101508803094106070042c080c2011650288001603000383e980200950201c40c1041404000300000d14840c3c0010030303210345400a2905000c40c040214410380d20483d0f20080c2c014102c42c000c1005c3d0b130440e43c5428800c0d1a90310302c9490754042001c0143c0f011a500410000040150705a041f036a01c408007202c41e03142c420502d821401c0c03c2040c0c4052244c00c00381c03030300c01488103443d43c4041c1b0750082401480720551101c038000040715540404070441b0912408404d11005007800d10140340103800c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 836142473 1250 836141223 836141231
    0xb010201110409020d2c0d0839070506071205040218330906061305010c030201180c0e100503060a1a0a0b0702030f03030f060103020901050c100618 65
    0x10240030100360207030340500c10340760b0390001311005d00c0034180d440f041d501e002410520504400c00040e5045101e01100c41018600400395450181d03803150740814802d49410442c1c0c0039594202030f0504007458108088009844843c80341c5480c03031000306c0a0001e0511410003060315142c9064000c290402c032010790750f0307624100310038000165980808507000062001d9aa400303039584032441060000c00d00c10b20f10b440034030703039140b1170b146c801404c41d072b41d400e4409a551118980b0303144144000c902c540c12030304d4401c0d030380300106024644c410746c58507901500920002c620126201120300004003448011181c0500044080003484400c03040c06620031002d140c2e81018074a0540425101c0300000d0071911a02e5880001d44500c1ca92404441886a0064284050151996030700c6565500c02081070f0b20a10038503e20042c0600b002080368407500d0340c074460840b151141b10054010350072804031581444801e001240c500781d02040150a45500b40d00081202860125002d10304003d2201d9044032500f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 836143723 1250 836142473 836142491
    0x30b160906051207180806060a080307150b13020a120c05070302060106030c05160b0618151020060a060518060609040608070e09060703050103020319140a0501020d0b010201 76
    0xc50251295407140c282c0d60300d0f444d40c44107000c0b0b410203120441c2c000c0e09040c11201243e110b200007a11780c841c030003d0700c40c0c9000d1521400800c1d0759005d0718100600c0829205041091501d0ba0b4211506c00350014129103a6021900b056100341d07040706410b00c00154010030030410901581c016202e0144003424024a0710040d030314000e480b00d405004d15020300d62140080c1009520440c07c44440022505e201030103640340740303001d003942802030310300381d01c12015903402011491409010500411a6201d03015210305010140000b200d42c0c0f43c101d405002002001400000729403030309884c80c02450780038010038646134001c10200d0341c06422250140c1c10305880c83c0101c5260312000d60700884100d9155440c1e00c002070021700030b070215400c0360209004864002800d440810146405034920b001620302941d1141ea0071030440b2401d00c8081d5055001003211403000d00c0380440940101d000344800c0d603000c0030440c4003a01d4508000811240d581d03001402c202c0c07075102803040b07040c440000d01c024018000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 836144973 1250 836143723 836143727
    0x2060c0301150e03030d0e0105040605010501050c1506010203090a03060e0d140405150904061e080a02060403081614030a093501060315050405010506040902031c18030b160906 77
    0xc8190141018090f15002e09481030ba03040059404406641c8801d0000012150030a40a0701050b201100c82c1810300c4004900c42d0f028400f56100c21000750001c0041d83c0c0e0141a80716101806880e490540c0010001c00d140c40d00c500c1d146001035409410040382c21440a0701403460400e9003004942000303c151100725000700518105d80454a007100d00c0130803800c0111940b0301c5131241c0e00046501915040b80050a0b1381c80c00c5c0e5031101d072001c0b0f0040d00617841e40c9401040d1160000c840c001d600010402052001507000070190612071482c0b90485c2c66880180d0303507500b0003824580f01601580c4046500b80100c0c0d444041e00340030b0070640b040b02c0b00c00095102c1030030741a080348600902580c12561030001105096011800440d001540713403005011200c0c0a00c0113080c181c4060380c140d42844006217903828580a140b600c07a5018000340031103413040341980303400c9030005050000c000115001d01c010081c04038110015601882c008480d0342894003002031120b03003091041c410322580601c200001c035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 836146223 1250 836144973 836144999
    0xa02250305031303050d0203270304050d0b0415050109020417010212010e04020102032101030c09020702010206010303081803040e33010f03060b13030302012702040903021c020a0302060c0301 84
    0x10300c20b4060b00710301c0d03540f5240a54860044c40041b0700224404420004a40144045800650f101248150074000411061600e07840749000e41604084c036540b10030001640301d00e0b1980e002c0d020740c005104007444c040c02c07a4140c071001ea119a111980114091014039080805854181d200303800843c41c05050301011f001c00d400501c039803a8010044400a02564000d100f100c1225194a030240303e460a15040807414a8082c04144c0c0e000d4008200800c100e0070780c0c821101c0998050300148016861035170100c074a844000c045107110003030321498001c445400c0000d03002500c9001d84400d01e0b071500f40c401400c001840814489124804101c0402e0180741002c400c0f0100300070b18180c290b41081300ca050300600f06c688e004042d40d1000190804480d140c40d00c0741010360b40319600074440b80d08000849900489030581640b041c49c01000400010700d001c2e8884000c440c440c0c015119000001c0070f80c0340540801c0194140580c0140c00781904043d8140901540a0174a04486086504010703850b1150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 836147473 1250 836146223 836146231
    0x21100b040f0506030402032b020709050903030f0709050a06030203060f10050d0207020f1c02030f1606031d060c03040620030601030207030c051606082505130e0a0225030503 76
    0xf603030b002011a0954030305200744a04081c214031080300502c9142ca14803074642d420405800103010b170010114060085014041c064030000d0025815a220410141300d1584003400308401d001c444200003d003501c801c88000010a8191001608c9151607003d00619040401e922485441c0c13450850741e003190040b06507181c901b4440303401030b15a402c40c40414491000501c8456104200001000000706580c200641061003603040c0c440034a05002c903556105e2280c0030b00a2244840941400710340c1c460b601849004000904606502114070325a600f84503013560001e10480b0000200000e00500303000380d00d200e48244250700428061510002950b001c050003050405800223001c00505208403d4403410980103810b403078541d440c500c030010300b802d428850308001c106a840011090181c1c85407100248044094001d11f45040840444447c0e2060210140320455510041404e400c0300c0c00c584e1007201094001030b07032034070758030131042104466445400480003c01ca86274002507100c802c0daa00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 836148723 1250 836147473 836147479
    0x408070303050a0c0501020304061a0301091205090d1205040f0b03090604031b05010e011a19030f051509070e0a020a09050f0312030c041706040503040b0d0221100b040f05 75
    0x8076070f200c01040f2281c00c21200301428030341c004024001803054503800481600385010100d20000f000905242c242ea2030f48402a101c001c1040035241518010790041c030401c1381c0102402194801a503800c1300b41c1c0500340b407a10000e0804242401200240c030315000240c41c6610500d4150f1a04c80d24840d42c9000040c002010003040c0e642c01e10700d0f114214031080c58039501c0300c001d2150070ba410b0700d018002c0c006514800925000d0200a01d01b82c14100f1401d1004181205001d00e05425911561601100c6d003904403202d100e09099142c19101c1007140500601002e03001e00f48036403405882d02910030016080b07080242c810444810040e400a103002d045610643c1c642c4819901640064105804030b5480c8070310440000400c808110b00c0710003030007a50500100011070300140c00da4a55a200125030050096004010034011820803c014040c0b40509020140c60080d604000441c0c008000c030852460800140911041c00c11600b490405845100081030030140b0700098000220014807400d80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 836149973 1250 836148723 836148727
    0x703110d02040f0c02010f050a0c09052b08090907050f09120102040807030305040504051509371b030e0a031407020d150b0105070c062f070f0b040807030305 69
    0x10854455411820060020f80e804121054000c40d01a01804030301460700b842524000000e034042075548510103401869560b40d040640c00c010034031403550040350070103000703282040240e54103000405045043c2c610a10300f0f66100c0700c1c444140891010060000c0c1c05001e000e01c1800c800c5041c0c0410b5031600d1504549900d06081400e00180c02480340d9040818940290480401410703000300003001243c0056908002940e200041250301d5848140340e141e100c070800c004540055284100d140c440c90909490080c8503900c0c214103460001d043c3c1a19001640315012900b9058070040c0050000c1005d08040c0032501602404e07544032045010300130700340302c07541140c5007020300004191200c0075400f609543c41a909410300b134a0b00d90f000c041c410089420301070361203c10352142e001d40d104690f02c100000e00c0303641852425030f48203010050503c20019801410980c4104030458054441040360181a0860801d2103045081485402010b0020020041040200000101001200e4052502ea5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 836151079 1106 836149973 836149999
    0x311191a0402060f1c05011403010c020f030919050a171c0e060f120f0901060609050901090c110a030f080f0f06100c05030c01060e09070311 62
    0xd421a01c10b2280b440c0c00c5075a130001e8203100340022000307082a181011000204c9000340c0c06814940b54040c984111410300b841400c000d0740c0f07180b0103030010f4010804c41d20b0352071080c20b0766180600107188040719550022070014004c1c04008000042665640600005000000282441700c1c020042c0fa500603d40c22030003d8555000350b100c80c03a02c10005400c20106070414880015001d2007001004400e0210f9105103114131455000d0300003a050401c841400c68140340c11031400d1107042c2d00c0030310440c2e4400c0300d450b044906c441400f20b000218070008581e400c3c0395015100c7c2c2849070001d40c004140c0c01c80e084003010755042e0741b120000e0356800d60300d10070808140c0d41100e1141e0b550740480c2540c201440c1405032044242040c2801d404141d541c03a186622542e14207000c0e035528001880103c500d158003030b8000f025103000304507a070b055407a521640c8101001892042100340504 = true := by decide +kernel

theorem cover : BRFrame.Cov 835971223 836151079 := by
  have h0 := BRFrame.cov_init 835971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835971223 ≤ n) (h2 : n < 836151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
