-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4620
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:12:07.248744+00:00
-- url     : https://prove2.me/submissions/dc006c06-0565-417c-bd18-5c6ab3f23e5f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830755395 ≤ n < 830935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830756645 1250 830755395 830755447
    0xf0f0c091d0f0601141c0305030a140f011a09150c010e24040c03080c0f07060906170903270a0603060b070201110309040e0105010e010f0335 62
    0x2030294489016950302e20030a000070003904030100500070b40342e030b501c00000c0b030036002070046906050f204026000036605200960008400208003e00d0617918014001c000d1076030703148040c0d00e152031290741d0400c40060149410040d00c0b80030a0306103901c02019039284550042c80025a03400c18040b039441d50348040071000c010350074000d041d4a680c5c0003003000000e12900c40103100402c060b00418103071200c002842103a0054200001001166445001e8244d960b241c100501d01080041020740c03a040c010761141040208010381440419030240c0100d004505a4034035543c02d4480b0082542075000f000308a4800401642441101c5c031090070050500b900c0549201140c6600c5800440985015005401444800700168401540b0428084108406c0c09060360304180e00500043c00340c456410040d0100c1e919000180305c540100481030380184089a5260502c5117569115032007602c00685402d141c211036850024143d1903038400824158040d007040f6941c01260101603420904119000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830757895 1250 830756645 830756681
    0x1404050601080304050604090c0201180609020f0603071233031b0b09010e180c0c010b03030a1e110d0921020a050607020d0203030f071e02010c0f0f0c09 67
    0x42e5202001c8122816500041d040324502810000b044025009400c0e000c000c5650324109415040180405d082446128441c04161040b990040180041001004510421040044c000500c0d000800c0c1125484615008100300003900001d00c0c0b5441120200e90000780e250041109014900e00024140c030303c13840411400700910410304d43e21320864040c074002c1075020021400658050b40b2040c2c80e0b03007030007000ca2400c03883c807020110403400203583d144078501000c0740d0781145200078020800410700c16802982001c0c0c1001c00203205004110098000143e085031343d50075a44a0b42040903240c1d2404100c40c245151010b0042c00b10460f4814036884211103001c51000503104803402841c03540082c00e00d900c15081000f0825658003444049a02c90445030491006803014400340104000a5005586408a0b8101040038070b0300305144c144180110304003440140e8110052400598006000c680400d2040c6840082d41c601d0740d60241070080c81410004000d6855007040c00708980c40c21050b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830759145 1250 830757895 830757899
    0x141516090f032019090f02030408070803060102070305010e1c020f1c0c0219080105060d120f2c0312040b1b0c0a0e0403080c0301030b15040e011404050601 68
    0x11100c00805004441000504150410208a00110f901c1d40c07104811a200b1098200400080400c082d40c000c84150101d01502084541070350f1064002e015001081540f940ca030655800407039104080e00108840f03008004500c0d00d034402c00030724010319807250007080030080308401c0703035500c507500d003c10029000c1c0180e0b1308120610205024810708075189c000c00094018000041c907001c2c0c444040400c11190490300000341c0d80c3c02c5c00d540d61038121491340070700d22400c1035841d80c2910001840e690080f08000e02d0b203c00203198000580a4040605e4a502c00825504049030801c0503031845440d0500055403004040c00c0d40f030000810700c00e08604a82841e0000720040341d030760160303205038200030b401405981d135800920b1500400d810300a1040d1092039003d500016401040368004114001c0407030200000c05d0741142c0c0d0b00e50400d25a011040c110761540c0e83d46400c862005011401c0101e0b8081d200c24207071920b420880200241c0d1009000c42000e420030b803050302c0c3c03040b1400e4803140b00360800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830760395 1250 830759145 830759147
    0x40503010f0209030d080406110a051314010c15150315320c0408010501060206070212090a1211090702030705190f170f162913141516 59
    0xf29210001c024001e0464544c400e08180c410780d600030310070355410740c031103043c0030054018030028542c8014503140d6071341754003080700030501c84042030300506d40200781810900c032240c0e0031000c450000707680406031311084103040f150a00504218000304108400f2500d0100801c002c8000c1105200540e10041140c0c1c82082203555080c5040c0b02d201e201c03041608401c0313100c00d8280181a500241e002500c918044d03444a030a400c440d005d0344803500503000740041c41842681440805130080d10043c10900301003a00001603e00b203883d2150180605012140e00c3c1000610064120714141c001d05c402031610b0101f01c00303500d0b68030a403401c0355a4001d0707030155001d44800200082423a03400040007140004a0ba40340316586042c4052080502c506001104280d02d0420080266054210380b00d42000c4840c585050882c100c251000600d076014402007800107040c8003043da00048103480c030589800e090424400441c0d00d000703406510300075458080300300c80c0f100c546070340074403403086020707640d080f1150f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830761645 1250 830760395 830760397
    0x1e040507113c0a0f030c03091401050f091906021b1206060402032212120c02121309020d090b010f08060c0310080d11060114030303010b0c070806010902040503010f02 73
    0x40752282c42440300b503050001462120316001c01c54524000ca41c01004142c03505600c1d804a80800c40c005000409080109640070a201e00101b0180384170010a0300814006041405a50070b1003921500c003181c3c0058940d59086050b290113011890003a4030754844500a4641c5200d0b81c404e100140104d801d00302c1030402000e5111080e021001a240c0c949804041101a606c081e1a884c45c240400e4040201c00458801500040c0c0c4120740800c00400e00200c080c00c40126504002119403825002a01240d004680c00c0e041d12400114103941d2520310340158407a0589800c9120780d075101040b0400c00c140c030365102015085c040e00046100e41c0c1c0e585115141c3d50324034007810041c0e0f00f05401203030b841e90000000c0c5420100032010302c0c40c43c90722030810610380003042005500040d00030200c41e0001d001031240c01c7c0034002034042c58a0410344803000c01d0b5248410700c01c010000500240042d000c01d024020140a451403000740e450b596591410707400650014010346200b94030b0f102c8039940d009070500c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830762895 1250 830761645 830761693
    0x6090308090c1e0613090606020705010806030a0f020a0b07030207080c0301060803070314040302090c0904052211040e030310061b0c1e09021605060603060903091e04050711 76
    0x180420428103c422007403101c298000c083e640c220600740308100c5580038042c0300c20080c0529010000d00d4a140c100c000b86030178416071000c0d0520107e2802c0c490030382c90102d04458103980040140821203420710100717440302120b50101d0305003400800e402d010541e02190540817280c007082100e6841c240c0004041c01c0754814805c100c4a5482008803000007801840000341c1d80070690720f140c0c20241c0c0c940101c1d4400b00c00320342d110344003100028a9071003807516100c0c2d070341c00041e1002c002c5821150701d40101103036411400d01410343c9240440c0350400f607545800c038000d21000441903030340701e040840d10311080301c609010f520080380d9407804903003503d0100b240d00114207800882e1815910b00d0701142c00c124035840f005042860034025000729080e441c40c0014514072190304202c1500c406507040c00384c24440c018050b2880703600300509103c400000001540c803020000c07a01d55541a4582d40d000f00f02d0104501101d810034100f408005040ba003000d80c0c44401079200080e150042151010941c0c13800000b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830764145 1250 830762895 830762899
    0x321091523090a0b090c21011e0623060a1b06060311030607080c030f0603010b040501080c1504030b0408130e04030e040f15090f091b03120212030a0c03140406090308090c 75
    0x1c400300a80034086072010021390008540000f034a41c100444240113030981d0140c818489c2e032120400c1103610341c800100070b190340740866200d0011484200203802d074410540352004001da403d030351684658500080800b1164081810015203503a440d08812481280e409240700c0d0241d04002032055028140191060382503182240c43e643d110364680e02540d102800c490380565030b94407072a8950f1213603c6518007030701c1c000f0003c1003029105400c10189116641071804e0030380041c40108002035108071a107410550001420f07848440c4160410708582c0203030711070640b0703801d00d0003804245500311051030880c1a06440500620b10259211020382c0c1140c605901000b2809008010b06042c81c0c0c020110382c1e00d545d2010465141310f4844200079078401c0d0803143c0c00403440e002041001445140001010a103002034101406001c00e0240203000c01040c03615259221090b182003644070754484901003c10420205860505041810062a403020202c0201d81c0f03030700206041410000c4c94101708000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830765395 1250 830764145 830764159
    0x18020307050d03021c09090911030d0e010c02040207020103150902040618030b07080a0f060b0c0705010804030507030e03070515030402040b121009080f03040321091523090a0b090c 79
    0x18900741d4100145e014100350412815060209030404c0c9806000c0d6458043c0d465030900c015075400301400c1102d080c480d0024882480d1205903a07982000c8030401054040702c00588a40030f600050b4040e00f003035040304118003c07615000c11105030b0740d40034100751250751356044c0184041400003a8600c05502010340f10340300e250000b40e4001e00c9185001c1d440080c0300404a02106c100c5001825102c864110f10b0103c0c901180c4075400c035104010a00c0100400d10f04102e080c141520702404a20031403901400700400c4000c12402c42c8c408000035001403001078890054102c40030707034008581d003040d2800c910541c10310141c8075040c60721030200c100c5061000098810086882140c0700284443d40c0212554101400303e900c0f4854900061885603020b0389804922041e1310030742c8060807801a140d00c171040d00c1c0030746d060041034454502106031940400000f410143e51801d0501c4500504c0c0c0381c04003021010108000c002d40482d61f82e181d0f46c4114119026a200c80841c1a113680104d0b1400da0001c40d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830766645 1250 830765395 830765413
    0x150b0c01060e0c18180108071a03042415090603061b0e010e040e1b0907030615031d01050132031c09030b01030b040309210201030e1018020307050d0302 67
    0x14604c0c0c0340d41c0c0480c8005c0918184070305007040e617149000d0903070040c1c5085d00100c90801c05401c6614400c5056650701c4401c900d149020707600d10301840d0240038007080021000300c0c00c500c2c0487c01c0e840708584241c071000c1000c0f01551031500030060580c0c0e0008491031810690501605405411200c420101d1078803507403c072104542c011200200031030001c0c1d5000c0e445039040030139000180f01034a10110b030303011410308021415051142412020f4030003420140380407010480c0e034486080c0404101c04a20700803801040e0080102a02c10b00e400a071901275180200020b014403450b140100d94003030640404c442100e11030080d0405e0010b1341603990b055084011061503021a081e032562480416040108880d80c0342c2d2994600301d2400d03001103804503100c400f031000b403542068101d0f00800c4884030000581e400d000001c00e1440700d0b8030f4000e043c1a01c0d0170803004442402c0c0900020700300c00e60010010340e040603003039002c842590b0609034042d0080e45400b00300f80c00c05034441560107401d81c00500310b82c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830767895 1250 830766645 830766667
    0x161b0929060a0e0603070909060306050411270406020403142802030307080702040207050604050127030c0b091009050a060605012d0504120305030a0c05030622150b0c01060e0c 77
    0x54401021ba40401c10000000306003800140714040c003450040100246501d01450a01c0c02000308840b064440c0d0b241e20007814068401492405c2c015503000c1c2c0d0a451503c42e4070b0100003030301960300001e084050501c3c0081d0380d40400610b26441e403080f10608800607020b2003030110034001500b00690540c000700a903030040307128600284207861000c4c0c401407800c20b0940f1400d06119040e54203c603681d4407102007840d564142c505041c121700700d407c0e010301c3c101c84d10f907800741c60104103001c02001200d0f04400906000707018080ca40c0001e103848001d1200b04d445140081e114611081e0888420b85002801b003601c0d449004102900700300c0007101d46002ea02d60710050b1040c55144000400c04c4010800845c2c003c1c0340840121009129481c1c054403070401642d00e0f801c2e9980303d0b400380d0401c101441000b003241d981118589800382040d1500740c5c0b800000f02044081e01101100d0490140303200300014040d0300d041c00800090381000004c000d10354454003034000046040e03d504c494070301d091250903000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830769145 1250 830767895 830767897
    0x609100c320a0f140301051f020c100c0201021501050d2411030a050901050f070e04111b070b031e2d07030f02161b0929060a0e06 57
    0x220381079040c40101c00114904888042d0b000640810000e400c50940c2c8051540001d5501582e1441c00030050542d0305000100300c05685c00d018500106440fa100346c1c40250003032000c071841c8040580705201c5402c0040015160320000501203006100303080406140d041da82406905841c4010312209100c400c60f2203c0031000050000c10542018400c2c980513041024400c0300030202c840c0011035106d15090710b519040314001000e41103580d0509041000c10594200310550101050910b00e0342001420b000c40c008216100c441840404001264a248501e60b04418081c200710b0085550f10b586521580010313000030340300c8814041040920300001e90b05140c0840d40200545c194040b103200c0080b4080c0001d04004006080007400b00501c00025818040e1451000003600d096252003094601200003064a0b680605100f14140091030154100c4140c10000c00c10300101b0320400785803100c207e05019104640c0c15000a800d0012a0300c1c1c100502a1100c58101e0f8640440d004986c0040c4025 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830770395 1250 830769145 830769197
    0x50711010225080423150a17190905060610020a050604060c120f0c0801140108040f0c08030a08010519080607031a060d020d060605190e0613080609100c 67
    0x3c0c504140008144800c0d4901900a12000718060990005200040c8a0034464000500b180000100f02c0580042d03042101d2140c843c0b0400548100c82d92200320401c00c7c89004500c040c3d0b00340c1000d011006012001a5903070103080c0488011042c4100d020040c0da03540c0c40800e004115030081030000703000c281654031008084c2d040d41000180c400681c1c41230700031600d241400310038039a515003c41c0225540b004009000d8000c59501011014410b4000303030601000600003004085102001d9040000811041000b4101030044984071254000040c00100c401d001d400c0c0504041e0001150002c502d0802a0071981c042026204540f5503075070407009030000e540320400d003a500f140043e080340c96410040921504000740140c413440510203802c10769240b49d100804000d0180020312140104480c0001c0d46041410441c1200341d00030040760440c051000c9159641c28118000254400d000c80c100d44114800420358022000950000342101c00086280d00003607104010300c150191080c08000e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830771645 1250 830770395 830770403
    0xf01020706050c1c0221041a070201020c071703070519051903050901080402040b03030a090f0504060501020d05210103080301061101090b070e12060106170907080c2205010306050711010225 83
    0xe00c6c0102003022802c0c0c01e02c141c8040751801c401201c1e1a208a2003880b18075000161440254602080340e590300e0b03a00c4805010b0a03103004840c0443e0100b60b01c040085885003075000e0305507800102c00302c171010000000c2d100709031030358018032800ca5001c2500c8465052100c2c0c0c5500c032179041c03a110100454841c1c8006000300d030416598041c10704142d0b0108050070160559650300c0c2d44003805c11042a02c5100d80794811802507040c014140400d07078002c00c48c1e003849a00740c074110340c461b864410321074400c2c894900700c0080490305c00c0002c4140300f41400214145e55080d2600410396135900c0f01d0b030382203c0b00940050051800800404c5980744075452030001c00100400824001c080c1408c402d04001c420392010003c10450391100c4050400e070403402c0d900250040107800d002d8541404241c60741c0c240f0280510038088220090381c11001c40301c0a0121080f6280304022135a181c0c9001c4d40205000d841c0c51010801c84031000581403c1402219060042401d80c0b0040c0d169030100c09040c500d40c100126 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830772895 1250 830771645 830771677
    0x7150801261e0d110a0f05030f0706091e0c050f060f1207080115020a171b0a0308010b0702060405120111071209050d0818030f0f01020706050c1c02 65
    0x80d1a01c1c00700800c0c0c4102d1400c10502801800500059150500030070035001030100040102000c120003103007545125400000001446c14146882415480b981049451204001c500d410500c078582e441086414811211201040d44000107c40c1030301c0031100003440000c404000f4819418082001c0500340d80140040742003000081c06110325400178005013407446185420001c505c0c3c0d0081030540107060a022509180c41c150000940f112040c110181111100c111000e00c001c0005049840381c81007130b40341c0c4010803014020191a1b0040c0041640010000800854122014001c440e1941d40c003c3c00d0610b06441c2c0024002042030103150560203541c1d400604028103c1c2d40004e0080034400d580c0d50319045503600703003c0d02c00d2685410850194003003400c03500c001203000d000c881044410b960786084940c000c1e400645812800307a8901003d02a0444c044c080f07030030540140c21031500c18601841640e86034a0184100d005402181600c8400815a130080d60002e5000b421880700d90048a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830774145 1250 830772895 830772959
    0x12060b04020c0a03080613020301050303030708040f12020d0206090708150901090f0c06030606020d0503222301050112110910030503031302040b0111070b0a0908120c07150801 77
    0x11a0510f88a202e040d03000c40c0b26942040b00c03511303124120451a181c44c0741d0850542d4140700100b0f07524000105507000f8030103140082400e001108014000c07140e4450505d9080894020f4003c0d1a10120307030480b0007510640780410000c030303800314028058640e858010b0074061410000390003031103000313400d041843d5070b204c1c42c01002c11103904103003560300e0160100311400c40c90000001c1c100d8006d0b074048003c5401186d11240301a510034100c9800021034139447c1c168411424030400350b81e03042da60041110000c00801c210365803cae10140202d112200c0003c000e140c0e070344c001014407950301400042528162039003900c1c107440c0040030b5a403c4038003400010306103512569007030320316802503d80540c0d20100703496250852070507015100002c3c1e028070f800c1054a400040da00c6d62200030b40a0740082003004a09001800d12030300e141001400100c0c00c5400200116910135819407202c003251489004014010504c0342440c0c5910b40011800e503114001a07103030403500c40071000c00400d01500c00100d0012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830775395 1250 830774145 830774167
    0xc0c0108010305032a0706050a12023f04230705130225060501030b01050d0b04060b0f040213030209061f0e060909040c05130603030c0803041a0405031e0412060b0402 73
    0x1b80c0d001d01034507280c240da141200c01c0007604491401d1403465450740100207002010041356414241000b014103c140c10710381c4031074943c0010351030300b1102000c1c03411041040144402c4000324a03038140040310103c50300d4a4801c00c02c2c3c48240c18021540c01413510554072107603d1055004112614448030014480106450204528002048151806502d0380014014040d080b40380c640101070482d1416501c44881c0c1d0b9000c450340e00100081d2841d9515800340380c964503202903101000344001e1046540d016200030707145600000340400d07405440c030740000401c00d080038008070028103901d04400f0a82201c81104580142500e0034039504110103012100031384d01c468154500403445046d81d014500c0c20107007400600e02022a009120b241090803c10209411250513052a41c200320000d07581c0d41c441c1007644031408440035030400010240704100600070044050041d003010800359400d554440e0a500d500b90186000c4c1c088121080d594aa00040b0507030310110080c3d8014001508207a00040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830776645 1250 830775395 830775403
    0xd0506040f050c0a1e090b1f14041d01060201050408030112020a05040624030b062a190302011b0e2112070201030b1c031b080d020c0c0108010305032a 66
    0x400246584003182c0303800020043d45e08403002526040c0002c0107a41380c280c0c00a009540907503100c40340e80402c0350400c008184520001074196024107400c0760b03219039804500c80407048d1032488540d4011010004560241b060090501582d00094880d065900384a482c010001080b40d0403a4400700e107800c00501d40d2154050f850050555554080c20701c606164060300b20101501e201041601c1c202c850780301503580000303458118245525a18845d0840504e1b85440140000032038558400c00300e01c0002c2c1785503a0004001c013480b0383d000b0700c81e007130307803294801a00131b00c0841100c0811a00c80d442041418400c01c00440341c91000108241c5403504450b50303062072507150442c100b003440012120299600f502945400700001e5520b1540714089000c22001d00302203440081c200f00004555901c3c54800100300304407542c01034052a680c0005468a5000b944482840c072041c0c06940da000d49650701809078141282d130813001131031820204030681e5480f0300112852800c9020034051078150004204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830777895 1250 830776645 830776649
    0xe1302061c0e100e010b030607050d0c050403020a09023007030216300c0809090405070e0f010e090105040c27110408070b03130201030c050702040203041505060d0506040f050c0a 78
    0x5003001c111380b185030a40340980d1039140a58883c00a202c41c4079401012902e646046590024951b1a41d080884061140d640003035800407540e4800b0645003201e0f40108644000ba800806c07a4010035032200724040840c00761103104415100001d8450780c0a82c00401c00c405000103a003030040c1155603401607528401c6d20100720030a0205036040d0845d8104500c04400d1080e0078590046c003015640e040852180c0d1801e1402006000086410003030308100f5540030304025000480c0515000013241c220702000d200300c01101400e08041090404107205240c000c0c0d401c0681c1c207882a04010523006e5401b9074889640c00480c1d60320454025070300034442e0260b0080c0889446507a00d14245130a03203007206d550041c1d00400002c00a11a00e00d407103020754218542c0c2130902081e155400b54042e6000d002d00d001c080d401a000004000400c10302c00a1204104009001080f441d101c440900042c06159000102a503001c1c01c081008210100c0c11848001c2c455000c031020251802c004c03450712070007a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830779145 1250 830777895 830777923
    0x40804140607200f041a190e0c09240315060415020312061002150c0f18130509070e061f052110050603101e0e1302061c0e 54
    0xc00d280150745011340100440f518104d4041c45a0291001c1c1c415686ea03020110f148900c20001c1800250058221840b0041c41950f01c1c048007407400e4602da0301c4581c0030700e03204c9104d00c0da040103003c0c0000c90003040325084591441164211b5580c0404450140302d0000310542c001c1e03042c000014401e03900c02d0b01182d92150799010310b860311744200305500c40d088041c04217881007902c682c40c4200c00341d002030104010040c48a0311003181e00ca50441d248179101d4489204000d00d40090180400d921410300c44000b100305030751001f401d80150810030704840007506d0480317060704450010010a07004510309034100b9001081d0700750100364008100d04548503a55500e010503c04110070340261181360b10ac9170303088060107242043c0d14281d40c81c039100031107601400d0310910002c03010038414101900ba00025140d030100b0040c075080100c0d0640095640c0c0d12503115148034202c0001c0140194014001e031996024080604200c00d89802a011100103403900054640d281180182c42070100303c00c84944201c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830780395 1250 830779145 830779193
    0x21602030c0f1005030705070803010f2d0614090a120c081513080c120c01150b09101107030b060a15020c040e011103090f070806040804140607 63
    0x5584181420101c001d079201d4801c0903042201100758031018880d1001803010701e002d03981c0343d07650b020580381d030f005212015140b03040100000c9a08030894941c01d06a403045c28481e00600c440c041a003140020003a0a0f003807060802c0010000c140c025049240b22030f2080300e10030b08218242c0041030941140d9405555103181540941041c440c0c111417003405051440e001c2e10401c1c0c04007502c0601c000380030f440c88041d040201c0010090000c004146d4007001c0000c2c0507500b17030f00c0c00d000341d0300c415800c450010180c039441c000d05040c00ca040c1750040c90407541400781c00350400e00901c0421100c0c002204501050200f145c004020342d0310180440b0000d184550803100a50030300505101c811340c640c1e001601150407242c0386034400c540000d000c600042040b00c0c0820000320300907072039014061505007101d450341c01205010500c5008506c0780030f400c0c11a4210703032a01e03030707500203140d6120001d407000f41040b6801c02c000d00107410b2200126030a0b490180c001403828441e9501c1c0c080b160b04a002500d04100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830781645 1250 830780395 830780437
    0x6020309102003060607030c14060f07050c06060603130b0c190305010602061b1908090607030504020112020706060b0324060406053c0d06050d0b161202 67
    0x100e101d80212100101502d55884a001c04080c210340320244c121846560041240030030988038008062045034000d20f00c01c0e620441640c503550f11030080d1144412043c0201c0003074660741c441ca013500c2e4650386000040080780c0343d000c03e10850b584003404004a0f00c0503800460041180700001c41d0080201c0608140d0710450031221691180c0d001a80b08109410000100103030341d400a4141c2d000f810509a0b0f004920215000e8000307441102840440310300710740c8a13541115003142c54544501d2040054688507500c203003040703089600454000340440c50b9500380d0341b40e100c0164003415031540300e003d0000307032143c5400b501d021781c5d00100c41e100c170142d03210f0100e00000c00c814510f460704108141c80503401c250503c03002070014041c3c0303400c402c08410340081200710201840388941d00521408488402c42828441441440d40310050083c80030381850070000b4242070409060480d1500b0074241103054032101d40d00c4441c4030200b44160104803000e00f0f646000120b0388011324004134050003182102c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830782895 1250 830781645 830781673
    0xc060a0c110d080406300b090108070605030c1c050f0103050f0d09060e0f040f0209101b080c0f0d0f1101090f0609020a0b0c151602070905060a0306020309 68
    0x81001e51006005412403195000000c50b66819541580c00740d00380242030500040a01414010031889682c242d405095030301a403201070360160706040410f0b14086116a01c580d400765942005100700000a40d041000a03041500700c0090f182c0d0309400140c82c40b007050400c0d40c0409440054483c0c00010141a0040042100c02c000e88200e044201014250030700340b01c40301924460b403510500d0180081e02140130600d9486892807071308524010020004500c0d8201c0910080d0407480c1854040d03110342e0544280280501145000d10026011010300f4000503a41d045140e000140664124032030200210361650301440390a0010103203545124403101503c7c00100480815072001e42d040e4584140400810f0485042125041d0410800703c1e4090051001c600096001d62119480030004910003040d0800881c007121800782e0048805243c1e00c03140308840002c4000d60703698015030b1042030104500406500013540c0481c00610401c8255600e4555400707a0b84200d800b1003054000d403040709510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830784145 1250 830782895 830782913
    0x2040b06120705040905070e100e1201021305031e07060c0606080109030c0605100501140f132306030c0d0504051002071b140604033f09060e10050c0c060a0c 69
    0x21000ea8500107039851123403800705560f0302107501100f040040c01c058141c0c0071b850f603100f4800070807071590003150b46001c1c0c1d4000300c400d18400e016051081c050308045045400c040c95890b140c40590350050441c0500d420780640300c1e40802241200d190303444075400030300c4040030f108010206000303803141c6d200242146000b500f110740c02420004800404201408130303984c000718004503100d4643c94155158088850a1054041e03000824000802d1043c0132586801200c1c012544005034411400c0c060360007070070040140001c4a80d0705101d0070034000071111040c0b50700100d4000340140f06643c290b40c0500040c8090380d008400075a402c000f0380c442d507100c00c80c5d400022402405660b103041085010400040c02070b00c99480050a6810340c0c1c8440e407414040c0e10b505e2055080304180c804000b81c4003c210411030f031010561900800c440316000180d0310700420380c075852207900600c0843c20044550040c0c41e09c2c3c00407898151140b00b403880000035515028002c08904551f40c07154040302200707103080340d00c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830785395 1250 830784145 830784151
    0x120c0102070b0a05151c21080109140c070212101a0306061807111006060e04090512070318080c09150d201503070306050607050a02040b06120705040905 67
    0x9a460702c000c03c40d01011030042c940e200d00303040301c2e0750903406c0c01666140480d64480002504504001c1001d540c000104046ca4201d4200c940b1803440603230361000745208407040c000304482080c070410000b83c022041000100f5201d40700825003609000d50b01c001c14900003c090308900710795591a45d8011024400101c3c004000c0100d00401107440c01d070012941105498031311103092044200420140c50050401c214507103441030450705480780700031840740607246034881c0700c0220300c02407000034481c00d05001310110351750030000a0250b42d1104a40400c2c903440b170507040c3e08010342d040c031848007420300426410007481114000c00c00d0b840b40304c04001040c04007800e00d064824104080d0450754880d221803481013508040c4d01c00540d03c20707820041080c080480d4059221144143e000310071095030303020318080c0e0780c03598040040c0c517241c40c14070855229008000d003031a400160460018a4681c006505156020706058201b03000304071040d040060549495010450106092180c07000f54890154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830786645 1250 830785395 830785411
    0x20c0d050c0721020f0319050307060f14040b0c0408030c010b030105100303091a1b0601090b0a050d14010902120601090b010918050a020c10051005030d021b0102120c0102070b 77
    0x40c042140b210034008100d440328028000d501c03030040210240d40038041c10b001030b201e01d0030b800c0810b0018a40227450740d02c182000c03140c0c0e80c039002c0b1042522847d8420541c101840c03010301b901c80e1701c0303d07222918400802011450122010840451a904144050710205034107100200e6100e107084101420340d4402800c000b035111103083c040001c40d5200d981c4600302c80b101c02d0710b003415001040324080c1c1d9106410020042002c03011a420001c400050514103ea98450040159410b64000c0000c8440e0b140b296951005c0710300394200c0803c0e0b219090210303240d25000002111a0b80740d0100c0d070f03054100c41071100c240d044140100b05000541c00780300080c45013460702c8a0745d18140480180d090058142c10402641c2c0c5800082080d0304980c1120204030001b012030b030b59181c083d4038180c00342400310fa044072805440200007540341030000311015018081e4014160200a01d03589680303400400c08050304621480000c080907070040e0004110303081410001580d40d55031810300c0000c504018024507 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830787895 1250 830786645 830786669
    0x20a080c03030313110907051c1e0b03010e0f03210103080d1e021b0c030303270a0c0f0501030b01231602060d0905060f01051005030406020c0d050c07 66
    0x990141c1c0c02000700c070f80c00340480b805000507058a003031264841c1281c90788642c00100301030901840c00d07000320103030110003450301084501c1d458010424055540303600001d2541d841c0784400c2e04c00c00001e42c2181e144034501030000240d04003808111441e2200899051000b41c0000607071120418121400d49402c132009a1400400e515541c0d07402468850b45030015075003907450b0003121911410341043c0204011002003992164088014a905e410410791585681d1150401241e0b5a00307002c8180c4c1d01c00c1c00b20110060f6101411050465000c0403425992045d0042000e640d000424040300c0c5805807440d40d03250240103081c8030014040380d200c41351448c1480340009640b1281c0700156034611038000c00461040d10303480e851500b0f944401c4450302c002d500040114030440f0010040d4080003405028800310341d0541c40340111036100c1c03c002c0c0034198218000083c142e00300c9000308010354209100729001072a000d140c1028a00700351401e1f2020000450001e0981e00750320341008440c000d4103c25801d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830789145 1250 830787895 830787913
    0x260d0e10020a08072003010e0325110d02130c051207021603031b060905010c0207170c040c200d02101103060411041502031e040510080a0f1503020a08 66
    0x141e0701d6005108005000c00c0f20180c02c00b00c4900c02c840c8810340c8170b4018000780700e1820b0400525849410280708100c0c201c041d00c3c080074080c1c0800000710010350304880070b00348c4100104244100e10b00302501c240d0b040030f02d503505905a14220301c03d0800f012070503904c0d191540b50f00d6410803c1754001030b144504541c4110741c106424003901c0303407450807641e16040015480f254494150082c515401e00600714600e0008007006014041d0000c1190b90b0f50b56007614442621000800c010144032460086c03254400c2d41c1d21a2075017400c1c6d00c02d09100c1c00506052040c5000040c101700302d01c0c404042002c0c0c0d50400c030030481480e074042154510700d04080320b05201412010307400006c240002800d00e4403490303d030720000740303511700c81c40032140a000040d802c0722152800301030284d600c0e4000c020050b403108c0404a40c103804001c40003954141c0780001d12040e864003a00100f01e505550140c1900070041d41d800f0307024125107080c8111070820440003001c029040c40d6004020080020384c7c40107849800c44410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830790395 1250 830789145 830789153
    0x91512032007080d0302190f140c030d090f06050603030f0904090f060c05030f07090f0b0a0e091302040b0f090127050a05190c09260d0e10020a 63
    0x1100880c10211200203490400d148403140ca00b600992140d19076002e04031802e15059890b030014000c000c2c200d4952a10040311690803910b22070312103501000954000440c00f1004a10001000407460320b1003100d0030b001a140c00c00c8103d6290440c2202e09542c0b100d0728004000d07440c05403a5001400300c000e541000300503483c4001a10074981d6041c425696140008200320190b408540040e40040040249150752180a003181e071082d240f074034644142c00000b4001c00c1c40340c1c4070b4100f0346455405150401c0e11340310b01e850040e000440c0139010300c07061803690005078075024103a502c01e0314200141d105801c40d07801800700721004045400c0c055650f42402270450b0f142c1403001350450381e001d00314150300a600002d0351010390101e82da10702c1d2141018184403180c641904454000c040c0002e40360901c0091aa0b4001111966042000800c141f14810820140910000d0030090748000c04031208100c80380b05207050600307006407800400ca0340010120302d8200510708407040c1c1581e000420504096480e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830791645 1250 830790395 830790407
    0x806010510020313320f0d0305070b040606233d2705090610050d0e1b0102010203090c0402030c0405030a060c08091f0b06070b15040c020c0108041104060f09151203 72
    0x14480c028047c1007003180c00c00d44035801304c41d4820341100290040d414903140c0307400540014804d0100101c2c90b14052a5a40110f2031072a100c0513000300081e00c02c0c603080038002c0f402c000c05038641c0d07041500d00603009207c040814800d40002c0540d5141591402031402cbd510300c0e4003864822890f1280511001e0102da100c1c1d130011900500129007440c120f00f804071080380d0501c10140c083c140681000700c2e1801000c2e000504070541861070038810382140c800c4004900300c0c04100e800820540c03120f4910065800c10780e000307582190b5401c4d9814542a2100042031900c840103508035090341d07031551262354640e8071108003500040d00c54041c02401e4299490f6042c40c40c510500074038601d95400900c0c01940c1c50000702c8507499401804c048076407406040300d6402845000302240a1070510000401c01b0b813001c00d90981c8841c0507160000c00e03464a44551075080c04990074075030825550500880c0130003010424078014002c040d00031500181c0001d0894100d1010703800703c0005009030340c3d07000000350005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830792895 1250 830791645 830791669
    0x190b070b24031b030a0c09050906010504050906040b071202071b090c2c0a091d0319080a1d0a03030e0109021302130515090a0f080601051002031332 65
    0x108103140c882003d000040e041c107010b20001441e00c4c4840b200040c4102c001c0e000301e441101d00d2000d4448030382c0e8910030f200c19034100f1100c078059508200001000100d40390201504516076141c119004032101301003108076485030009985111155070108004010391740580041c020781e4600f8803510340a04c00107052130001041142c0529401444000d965500b010000f894070310007804030b5000d40d51070400500070b01428581c4090000b000c10030b1510101d000040325640d04407400c42100b04141c0200c00c81725403202a10206904e074803003c003400009224020704071b175603140d0000381c2294001b5150140880e400700b550510564141040741c00542d90701425a94400510304016903a400792800410800c003817a0440d0750700460030480302c02102d0684020317016401060760ba140d411500c8510342d0a20080c50b1140c843d0135030212005202c1402c0003081c69503241c040b4012641851505954220100c02d2a04407203e030444074480018010300c0c04803244001c03c070400a660b03010303035242c0114101200ca0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830794145 1250 830792895 830792923
    0xc061314060c0d120f1508060f06030714040b0d051518100207080c0f0709110f0301030f050a050a051609050708010306020f0c012a020d0e190b070b2403 67
    0x130182c0146007070303a41141001202c038040410669203940c8403130a064209000e4030031280700d4400014282001900002d002d240018024802c1c2032400080d541100070344840c0030b407c87c0c0c854114017502e031038511800e103045110b000a41714101c161100c034040c01c140108840d00103010f00d0041c4221500101d85101c007006184001b50380d030503e908ac000464403820810760030320b12580d220048000c0010640406a40d0240d6045c421840580c540c2c0c1c81c0ca00642540c030186403010001000058150380951350002e11540c01d03618900700b00e868660400740101c0382555150080c6407824528030000c100035000d061201010001c500f04030304000e2001005000c02016a80d0024500c40400c146205480608409600900c2083c00c1c0308038480c404884e80040900500005100c1000180040f8070340460783c00955030020038007010000c01c0709900d10030084044c2184140404144000000001c0c100940a500e00240d2414000301e42914410b22020615500c82001e07800c001c140c0c0d000c40c80250205203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830795395 1250 830794145 830794157
    0x9090a1202031c421401121d07030b010306140411010f05040f0b071403160f0c0e090d081b0d020c010b0a030534030b04050c061314060c0d 61
    0x150301c08102007049600100710510068956580360144003032420f005000e400944c104025584501000c844201d0107401800300350640486101407485078444c1c0d9451f0a0304003e40440168802443e0400c265034002342c6030110303100c00510034801c1d28011107400c1402c128404c409850507454003008909800705035410400000e0a1039000d9200310240c1d40945413450031101c0d1150342d003802090b0383d44540c004480f110381c4001100c40c2030b440402602d81400c10610311500e80d4025960f54140400c00890803102e44007111008200c0e40d0021202a1003034502c10010009000200b070044c050000003000d0035a403414085884100340401c06c1611440c100d142005605c80a8041c040307405402044180303500f08200e072a0000500100288500360403091018400d85088444510021858040b8034040e03400032028003000041ea81046040e8030a00502c1078881c83c201c2000000d005a1202c0705c00212002d05040c28800c0603452003d159051908440c0d02c0c0c40c02d2588003001d61580b00c50301419044c818 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830796645 1250 830795395 830795411
    0x22107060c0519410301060c0c0504090c0b0c010e06010909020f0d081602131404020a06080903090607050309030106030b2418040302150f07080c030712180209090a1202031c 76
    0x14004d240a2142403003204000e480c1c2d82c40300c070010923000d0b03400026180b2004a20740043c00d0304052094682583d08415280c484d20305204e400301155020059044140d940d501030b1039450a001c1c80120302a00000342c000c25088841d004019070003c0070700e203c070700c1036681605100c000b403019030884040d0100100f034590880c25500000304a600303600c4000081074180048103141000d12680c580c0b0079403080352071920b610340790181210441c03411500240d0780c0c4c0c4204840701d05890315101502c07816200d4403c9a02c0c0c000d011004c6403e4541c1c51340100c0e000f8602000f0f0103040742d030300240e8950320521040102059480d0710700058882c0c07070204609500f10309c548085000d1610912005856041055021600e401c014013121403801084034600000f030514008545400b00907030440c1d00400c00c1d55180780305640c400101200910180d10503541c200300c1054000700580340c244a541c855020103020307114801050400c550310054101d007920031500100195589458106a1640c0b0b22920040c00034641e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830797895 1250 830796645 830796737
    0x30a08040b0a15030b09010c050a2304091b020717120304110d1103330702010213080c0a0b0301051e0f061801020d0f022107060c0519 59
    0x1001141e43d00080c0440003c02802800d254040c010b10380840200070075580900d04450a0150044000008071031502c590f040f071700c0b801c0c4c045844810001c0031901e8684c0d54460340080361100990003000c1060303240c10764035a50301844080c0061220035540b041941c900a0305030b40315400300b1060700c0c8031000800131505011000001e0030112002400007044240a030a122410740d1010740040e11078401e601b070291004480c1528007007501c2494071032000407000d003088042c0421b002000c14045640c00d10800080654035002c07440104074000140140404610a006040c61150886003560070200010046511040f107810303880824007602410701280c482c00260304802035540c1c25800392001c150001051260464916105026021110070030510101074545500f0510b030100960810000701003160400c400540d80b03000307a02101840c3c03038015602c0701c0445000b0b070510000254080390350031135043e0040711481c58000c81d0509564000070808905034005010301140515111a20071010013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830799145 1250 830797895 830797901
    0xe010623070219140307051c030c0203121321020d03050f030f06120a080f0a03090206031807062c030307020411030a1d0c010f0c0819030c02030a08040b0a 68
    0x5998010a88600c2500c0b00c1c3c600c00c0c00f020350b4010840c8041c50110241807500e0006200390031580050b000b41015407201001c130f5091882c00d50160140120080e04400595061001406588010200c65100c0c00b1a200700c042ea111960024240140030103841c0c290311821840e101c1d012581101c80c408850352500d011182d6004040e414034060038080300b4444034070b01004000d4030941c429114a811413201000d215078500d101480600321000411100d12007440341e50082c00d03102c00034180492000003036804948a1345c000c07070781c1e800d510540c0014842c0104060081000500d101d1600303480c0e015004091710000500c079940b0303000c60401011340090a490a00c1518907441c0c000304200301007008088807142c3c0b80c0c4111044241280346c41c007168081c80801c2c0d40700110514070001003081c0602c00c001075400b00140800c5000340b040030701c031610008031a01c000f000400603103c0c0c00880d03040b0560014040c0c0700d500540c1c46c1503401c00d014483e680da41c0003d03000d80c402e400c00f4020815444098a00c0e0007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830800395 1250 830799145 830799157
    0x270f010f06060f0201182006040902030402091f0b030703060b0706060302030709060b040902030a06180e010506010c0206030f150d240513030c15050a09020306010e010623 75
    0x10550a08000303031158445a44000100e41007922206007403072070010200e0884024440214600d482d014081c004908030707424400c210b45028864510200b0301200160060b003065100214443d000003c020071424980425600700d5a00202c02007501c41c40140304100c100c9900071588041d801100103030341c5c24440e80103100180b2845c0c0e0b0081d682d440f641044400342070180000d9009200c0d6100000341d82e40d0a00c181412160f401484508007802c21310040301a500213800303802d03255100d0070007040b5070b00360311060407424000d0300c40060101075190307013182075400040855041c000c80002c504096151507045a0b8404000b0701660440c1d52005098481d8040d6044a0f07508644440400780c10410303805008901c0d14000401c2100211500c49d00030142c800840ea004807680b01c0c150024000380c010708100074540e1041a641182403100103841d4203ca00880740c0549164640c003050040d07060130320299002d400c01e0b80740028a03604180024294022603200140369010808001181e0200ca02c15601 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830801645 1250 830800395 830800423
    0x6020904140405030717030112080c0c0303030f0a0501050f090c0901090b0f0c0c19421d0f1017100501110d0804060b1309060c020c030627 61
    0x180318105820141d1341c0f0f0304001e6048032502c5020285024555200f01528101c49011041c661741008a50784d4280d03d40041d160b071b05c8203210b0301c1512040e030340d002d0010390310640c10f614500b0003034a8290420403c0e00c50681c801d900400042034001d11540303d07107144079030010b440c88955568007102e100490380742155a001c155448408182a448041d42600a01188030040215015440b0560801c4511071010f14410a07503c0192401c108105294424101154606202c0342c10014107001d404040b03c3c500303031310466000e500600d0054568200c0b0b00c1510368501841c1680210000d40040b4485240f180c0c503da110315811703c030811841e4402e640c1d000740300d0464500b1100a00706111210103018003800740c140450705d8011400000c00000445d1640b491141d55102071680b19610b07039000400703454070f4250b00107107404c0300d04c010a0828042c00400324454180080c0d951945840282045440740000b4404c0e0800010311110103a110540c0791a076003415058200c0a0009041500e0a401d00001103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830802895 1250 830801645 830801681
    0x203060106050a0905010905060d1113080a03030c0c170c101a09070507050d08060a0302041404110103090c03230f01051504090b0f0601141c151206020904 68
    0x32076032950010240c040001079440ba43c20b075640b18801036401d40c607503004440d00300005100d0000e44a550b0b8101010348800d82424500e405845103451209003069001800148e02c20110721040640c148500d4041d15114504001c801196540356051140441f034180d0710f00d100820605492941072104c0402e030a0941e0302000880904200c0310240462846241c0c8165442070000e40c002d4040d5007100e01559104001e000d4a814038002175030050000f61043d0b41080d0301070004001030b00c40348107420722040d580c10b42d41c855107802e203003100400031805440346c10142001081000103071540780040c140e990001030a1464100f1a07088a41d1700041e0504000354485c070146800c2240741035001c00d010721401e490400040da295810301080e1001c440000340350741500300010f85800c550b10760850704102d0500d024120401140c00404a5800c03c0419414500c001e0200c0d81101149219518a0150024600e11300e60f00c2c0540c0201c50003803c80b07014116940002d45088169555804410701410300c90f08a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830804145 1250 830802895 830802899
    0x3060d032d090504060e040b0c0304031b060212070f02070b0c0a0f14010c0509010804060c021507030209090a15030b0a0f0504030e0415050a17010f020307051c0216030804050a02030601 81
    0x103068851900c0f4503030090380350103004039100010310f03402d030701c02c81d0056041c88103508d41c0000d215141c0d000074426810080310700342c26985038a9260095818901401d0007503203c80c001640c80b000ca000c040e040805000311001c9080c00709801161200441d100d9200b01c9881d1101c02d61054140f010409004096070800c5056000308052186401c020520540081002001410007030f0362030f114500c1503901103002480000c00141854025462081d42481a9030009110342180c0d00107403c1542d80c84042038010500c180c00c4e0901110302d9921001e2000c0a00030140440e045034542040707800090111009140010250482500040c0c00041c41035400c100629160070300900401a02d50124400c6007044c0e84c6240341d444102e610015944000d020b101c01d0352070100c0000c0181b003c0c01c0b40c1c0d029552a40c0785209050040c0c07001c0d5200310481c0d21559a60b120300d02d041610208546020600b02e03106000907007040e80711441c000849a454100b41c6541d46a50800d0351505c506004000e506124103000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830805395 1250 830804145 830804147
    0x21b120c100504030b0a110f090103020705120c010b0a05091b040b0414130b0a09020a0309060212041103060106020d0c020f09040f020411070203120d230105130203060d032d 76
    0x384104c03801814444000d4442c08003000030340e10620200c8000348004c8c0286880036802200400c80d000c414180141303425140d50720681484901100c0302d91240010030440c1d0350210030300a1000701d00b400c503964000759080c180041c010b603601504403060300310481507a0014a003042e0460300542400da8006890716510780c151701602103e0051140900c0f01c41c1001001c0c041140211210140c00504c00340c0c5a0b42001c0341280290410b0040d1b1041544820459001c40c140e4801410341c2100c0502a82d003d190508000325000c0c011549507002c5d41c810b10042254580c00320b449810169249480d49183d01a4000150301c0030ba035070070300c40d80b1812210600c0200f01031484981103043c4280c5050002030b24685141c8810302508801030b425800c440100790481d20448003d0102400002000550b0000840704509110411000500b0041c4501c010300044c58403110030005690880750a40c0b9501d0f10001150758104a0803004041c41054022800d210b043c3c46408080c42070694940b250441010768 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830806645 1250 830805395 830805397
    0x408101a0303120a0f06051c051e03070c0b070b0f130606080328050a05130e040302070e0906040f0305070f0501151a03160c0602090603070f0f021b120c1005 69
    0x64580e074994580f036103242e4004454002d180450304001e080116400c4c441e0750310b00d001c01c154801144d040c0030700000103004d504101d5807032b09000b10701c00085448140c50310340020301ca816500200d803605c209008034000245600748d4142d000c590a030700040f10b5100c60480c407448200300b0800820241c03c002c8041205403002000e0300400b001f034610f440d00251035030303003039406070380f0821840001840c00c200301c491f581d02903801071494484003180d03100e802c1c0e0f03074100c50080c0901c00d80b4110b0068104501c20011104000c04017604962088041c1440e41000d0380c54954174100307200c0080521101040600500c280404080c2000d82c0110007440000208540300549440034081d40c071000a034000c03195035a0340c0074004d60b4440ca003880c03805901d0b41146642a582034541c00c0d030490703001e902007000d80c40940310403010314018405d6483e1400344210208024008aa5680d40b603411503000c032810b0001c91085500c02083c5900544400550821410009080c00040c40015820031131801c21031400d281d01030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830807895 1250 830806645 830806651
    0x31e060f0218010e1005040b091906020a0c091b08130b010321021f1806150303140a09060f0309140303040b0108060f0402011416061407050408101a030312 68
    0x113a28100e03034169031001c0002e04120003401030001030040c4818040e1145940060486c850002c15041c1101c10300b901001c00446a034001c0b10041c3c00c40660502004903851044000d46032034003043c409039010311580c4450039458500300e020031084001088200f10b00d0b4088000507900b20011407480d607181e041840046c8054045050302003420035038044410301c08101c0c2843d00d50a4040c084403100c0c0381600741c016002011500c0311461108114000040d514803a101c1111550740b21128068510f040c0a440351200d2148020501420044c10429a5000486c4001e1326064200001400260342080b4020301100800030042d0380248805999120b00001442c45244601e012800d5030f038803440d280e901e40006031125603216280c40302240c0190302840e40038250002001401e424214001d249400c1075601c80000d03501651f444480300348108400402d55405802401c203d86400d161620550f55110b6040e41d02c03440a980e14590701c2e2010203110540c0d200c4034000c0840303482e074a40310300c001c030342410035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830809145 1250 830807895 830807897
    0xe1003030219020609040509031c0b010318020d030c2f1e030706270e0402180c04050105091201020406120606080606270306010b0403051501031e060f021801 69
    0x150301c0c8031142c10541036403041250740c080e20305414507a4031020300004e0035020b0b205050ba0701040c040c8a601d200b9611001c20041c58103240071400100e070b180003404481c240490030b05443e103e9001a0050b03240e000b00030f28010b0345441e1002c001d101c2428521041c448e0342880003403510301214801c031141d0701443c94071144035045030b80601d0340c3e241c0100b0954a80d040c5c1e6603030750076030081981082803e0050030003030b0b0151038a01528454020f034898002441d080ca030008244446d001c1c042c0015828100120074821000100200107410868080703000341c015032207a1810403e001070401d1245c0c481c0c100001042034010005e6444036203892015000d0000314458040301490250000380079031262aa280c00340c40094a414504490b07900030407000142000204440c5800c0302d03da02050f1410008140241034150200b07072660f046182042c03d0443c00c2d980070410a05240061011400c1281030382000303603c22010f0518041070b443c005c00903001d82c91001840c1403002c1100700321100340a00322052003400b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830810395 1250 830809145 830809153
    0xc1e040b0903010b09040b130602070f0605010806070306060e061b030307080f0c12010504020304020409050d0809120c03030c1b0106030305180306090616020712080d06062a0c0e10030302 82
    0x114105200d1000b80c119401f41c01d5000010100704901c10280c0c40d04407842c01548003526001c140d44a141d070540c10020212604c95950f001004074280502096402c640103280c1441490f03e4540d00800550400320018410340c1d0005104600000a80c2089070f069a810242c940383c3c81c05c0d50003d00880400c41d00d500386202000d0001e03ca200601d001c0f500e25041501034000c1a90038141400001d400040c01282c20558409140300030a00810800019a0031396682000e249084070449040c045040c0081d42806030922001c100d284010040d44e031300c00e0f280600c1b00d4803a0741205500c040d2482c4501c000800b5460031802205044d48540100305000309101003a0814140b04145641d0f40310481c0d01004581154000c11a0000f4487c16207642c40b4446c4101d580b200d40b20034513525a80c0c00900111414040050004540300c010b001e81c00c000d001030309100c0a030030704150400c00c1144e908801030400584460120041002d084107040c00340c4448650983c4500d0050001120901c10340015009442 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830811645 1250 830810395 830810411
    0x170103110102011b0c0b0612060f06031204140910210606171e100f1a010305010503030f031b0a020f0f2409070e07180e0105090c1e040b090301 63
    0x1444142800c404004d5075240d03031000d116034481c10740e06040501810b078080d41c4031f001c1110308401001010b000b0360406174070885600b001800c1502c2c02c2c10300401800c071560140000c015015442038982d400280c02c2d606003405580d032081c0415403d01540000561b42c5103843c43c140440c0c80c00e18002046071050310100401516081e810000000340002c08000b58091090f2030052082518140c003005002c0048800c212807121220302981c030a00328800120366100061984c0e160b045d121000410428207040166504040c00700c2d85a1080c48006012010000003042c0c42104c10400c003603e0440c82040940c40f0950004025203c4205a03100000d62081d00e440110146020611904044210380c06600c01850701c03100c0700203414000e01c010381600440d200020400300f84401144521259a2460a200505112140120342c1070300034843d0b18501100510658030350401c1290452099401e0030784503060902080c002003c2c0441c090400b040c0814000386000b500800707040c0211084000784640d00e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830812895 1250 830811645 830811671
    0x230c0310050d050f061612090201050a0f1e11010f0b09060d02040e01020a0e100509010c0807020415030516060c050706030b03070f0f030b01090c0f030c17010311010201 74
    0x4002910020514050a001001140b40407820303400390620a00a5070440c005061140e07051590844120818a040800c0c9840359a80011103800d01089800c04100e80030581d0002003090044981900c18410710131302c042c80c0c19000b0b800500003126070112140c400d21482c07000070905107080707035514800d60900d0003075840340a00c0d0140c0150400d0140400546650b00c07000c100c8007030401e80b01030360840d507500b1824201c14400c4c001031814196640360040d45d0040c00d41401080c103441c42170b00c402c002041c0301003280c1c0e07a404038244100503000060507881e0340041c00040d000f8082410443e585c10581c81c400410054085810340d2225140a51003003a01e82d00e8405a03124483c0b50001000c40e0000e00085c85090b000e948020a003000240884410f0303600d400400071a01e42c0f40d004407819000b201c80800400800c0095540500403080061100508085001d4075000081c07000f4801d05880d2104039842c28420300504001e00310540e20802213507034905007001c554003005042d5006500b00400e0f80114 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830814145 1250 830812895 830812897
    0x314060402180c040f121209030803010501030518010f0e0610080604140708030a020a0c0501050a05090405040303180b060307060c050d080a0f11090a060306050d0f0204020d230c 78
    0x9a41c0107403040112019002002074aa00d0040040310000c20500001c61801280b40e001c07006455105c4400381e442e02c45013400c41d4040c1802c88168100b012208051002480007010340341169001e08011a103500c9250204c180c80c0d892500c1c4071869803030301641c1c069104207504040b40e910000001d580c0c45031601140721036141c480740100d02203a0f010380b002c500000c442580490201041c0c000391001c41b0b4645c00c81ca0b00716030000c10081c0042e404108484140f02d40d080e6010001c240c2401e2151400e0313440c40001d070280c080c100b01244261741e11030010301814020340200e050401c80aaa071121203105141c01540000b041d2240e42c06403040400205040c0d000b45c100c00c1e00d40d500f01d0014100c02d40414070803100504001e105103d10b944401c0703c4e401c0c48280340120b041c9400c0920b0072540303504e80502403198940d4994440003c0604003030341040f15031108401c00c3c2c1156000840816405040d00202c2c01074490b2101c03540d24246808009044c54001d0344054140207105601e440c0c5540340d4040070401c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830815395 1250 830814145 830814151
    0x8071e0311011a01050906040906080a12020325031701120c350f07030803040311060408160f14030304150c1205090c130c0917071e03080d0204031406 66
    0x160280d000782940f903540c02200504000003004084901e0303d901d40d8401015682c1c40d40c4003030080d52006104401f0407014100104d415543d6100030341c10148442803c101c44100d40071429144100c000d4102d090601c92005c2e54042058000b05204075696450342c0c5210305500c078801c0e14040b0a811010a840070340d10303011031602d02402d082c00458810703204090340014030f0310400c2d03601d0311400c80403841c2c1410510080300214000c10401e501d07450075080c06461190018158002900903034200000540040d05460a02b6419001915444038500d006c80c901c4800e001b01034015a45c0710740c4000145000001584201d20400208500d80c184619440c15a01881c540c103001c6495044c1501c0388440542c00b8950044581080301e2207810300314046800c170100e0390050760090381c035008143c00710b0350808811401091b12080803e8400d007605411742c0c41d02007901594450f14280d001d045074105405030044040d5801c01a059607500864400400070b500611080703c00403401e51070390440b1200800d820388 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830816645 1250 830815395 830815421
    0x80c0c1e0c01081308092202030a0509160611210408010c02031809061503040308090105010b12010905070203040f1d010f15032403230607090902030408071e031101 72
    0x2401e480c3c2c980c2d4010141d0020b000071034216a245139281f144919030781c5141303404030881c94010703520f0519a4500090f200014030b5107074281e101c441d049034000510000c2d10212041490801d00120388500e040c4d081c52140c658141c1c0800808005c50000c40d03415000344102d4218074002c00c44070201d01c500340c0c0c40c0c0c01040c00300079200204040300034940c1000d00b05180d0040000b04110041307070859400f45101c0d00f06540c00e8000410318420040140024400c440c09826081c0400c1e04100c01c4100c04034044005000d01c640d106e8580d07000c985118000c10907240645015640c0b10981d9840300d80c00300c88408421020445440414000500180c0804100c803d071800151410601902c060043e00a82014030303400d6401c4808814040341015030f21000c102444c4a07000501c0c910b144030103050714100d050f070105c13880d030b80010081c8220590001e8403101102e2001d03402680300d5845040c02105402a00009000c030300510905890600741e0a18540e1f0340c030301c00c0d01d0f0706440c42945011a4222010b02c0840304e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830817895 1250 830816645 830816671
    0xf091506050711030a080304200109080c12071d1b1c0b0a03330c080106180e1501031506090b13081203011a0712080c0c1e0c0108 57
    0x141c00b040c3e0202400c50b140740040c0c211540c0160070798807410294001c0f602981d02000b40400e0807160520014888803420003407070070203c00e508004189480d000140300b01880f8070060140404502003d02680005203140305900301034240b202d0070300308040011034200a09840c85000d00c809000750505440c0002c00002210042c080c101c84580000c1501c44d56080e48094644800000500da045d881070070700030148400900c084a407040b03148918a4680d1030b807132290400c29218511a030044402d41180c480d80360407045600300b40300c0381d007034030525070448140246d440080100244010f48110440142a40d08102038180c402c0b8401c030104090140034001451030604020060b0080d02030b000b00c040703000c4401c03c0c6680d07641415181c250901840310b0b03849408401001400000c02a0303c12a400340c8044030b02d0091256101811018410300e50710038450301710f0102d8009002c290507100c11015800c212005a5220713040c4804071786503091030000603c6460303071107000d0703503c110040c40c00350b0201442c503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830819145 1250 830817895 830817907
    0x1611130c1710150e090114010306121a100e04030203130b03040b0a020a0e030319020c0915010804060f0c020109020319080915090307060306090b2d03070f0f09150605 73
    0x100c005081c907083c3c42e408200302e00140f0300c51641d03003003e014020305e00202000c2c3c0b0000100000b5007600e49640c08070ae0300d80352481d20348000c00c04103220303031215810098000c109583c0f1b030605076560399000c0c1c100d00750750201102080304154000004190010410f4010b840d9141e9814078507242d444121401010000c0b15004a202004980c026000c1d654030b80c180381110001c83c03c0802e20b160002c1c0075854501c0d02e03029900c0328035034060050005094058820200300d281c04a0320f504000c045030602e904220105000070180045a0701c050110100c034030090003c3c0303500100090191101000507840303402a44c225289540b00301c0201042550303c01c1c2910b017801d103401d0411101c1858079400c55078842d02001818020354041c010f88005d0105501c0000303509007440c01e0441254410b0202a01801d21854400304591340000c00c84003070a140024000c1107002d0101207403c00d401a401908569610040826201444035804c0b00b0f0f5040c14104000c17800746060100f46920a034411940487c40421070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 830820395 1250 830819145 830819159
    0x9031209030e06070309090b010203072d060504111e0a030f0524010e070f1718010e1b06041508040c030b0a0c0f020c061611130c1710 59
    0x1001500c00e010742000c2550000c10004a000342c0d00c013140407800130740741c01c0042c0020a864070501004050a200035820700d581030b40c51074540d00440540301c460740300a01380d51401510a10008a185600034018400c1d428145007040d0102c5207814400e209207001c401c03210b40455888900341d60400010075142c503803440c545445010084110003640e6600402c04420026011201401c0c400c13400b0f001043d00f950714002444007a1070001e0a4074003003100360340c0050100d942c030041003e0284403151014a05403a001540140301060034140c0b1001d5080000d0000c0442c000f1809807507044540d2805080001c07004200b200d20700c20742c0642880e00c4140208030f020307180b007200340304d82c41481910940c0c60542c5039200c44c82810340c225860003181c0d403942544007100381d11490400e00c8030740d0b500051800880d0031000030501c0c00350002d1000100070580380c040c1800203006100343d2842d00035140049550301d40540c04007408520703c080300807401451a42c1000c010300c02900c0e104440c0c1c185000f090303a04002d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 830821645 1250 830820395 830820401
    0x120804260708070308070207061404031113110c10050c0406030905030c16050f01031a0f030a02060f0d050c0a020607050d06050919050c04050913170f07020a0504090312 74
    0x210000030381080c40071000007200807000f000598041c3d21003044a00d0100707002440d005d2103400a03810041d25a035280c910100d41c5060743e066a90191200f10415100000300d040300f5044501905110b0801140000a0f19104002c2903c45c0c5040240c40c3c84d21101c15080d01900d50540da03644001c4420042002483d02c80d50010000c5445882941d1820035070780341642c0340086000000d113003030710300c00300400c110714024031403400300d2030203080038007880c0c03403032141c2405516200401c0750040c1d00403c40f6408540c0c0a10440e8805580103088584400f011200484560800c00307100d07000c1c610381000714440568402c1684c4c0c03010f9217540100141d581301c50f41105e242d000b03000100c1d01c5c19111180400c1a07641c0d008440d00c2200e203603400d0001a12010000410f4510240a500030707400200130038483c40e2606030f01264400c00c0c00ca0070114103051842e0007044000070410381801548007003585449620700c1002881e0341802115140c0717001d9152820401200c1018000a0201d48100502c1220342c4c0c0a030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 830822895 1250 830821645 830821703
    0x30803040602040e090105060307240c051f06093e0409060b1909060f0e12010e16140604031103010603060204120209090703051509030405100c120804 66
    0x81c10250500b513691240580b0301c9000c0c0d407428881c1c0d4540040080d14281004010020070f20310005030840710590320001000c1440840300001c0040b020900d13000d1000800c42c024072490780b640020051104c0d400401c004100c1c078008c2600040c01c240b0301d080c00440340401ca141404260804440c072442900c4544010812201206001ca0050000180c01d034118440c1c8d50040c50040c40242d65003c440c4c0c0081b0b628a100c16180e400d100f40c009090080c150f004c0c0c640c80f140446410040c10b00b04540000501d0f842264140460755824600c0842200c1d202165500d0b0101c44400e40d181c080380c450120b045031002600c90550040c400340b004001241e00325040d0500c0708000350000514507100c0d2100360690b40540c00c01618502240b401604508007510308031b40c08140a0060204c9500315035400d40c40c4d00406044070302e0700b1072000119030080d00510481300204001000300c4850120000080d0520340395040c25a10811300c5245940160700880c0e07118841e9230310500c01d80712110100c0036400e02000d44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 830824145 1250 830822895 830822903
    0x4050319030b04020a0e0117040503162a060f090602150c0903010f1a030c0a0308071a16080f0603060a151206020405030c1c030e010309020603130309081603080304 72
    0x1403075261202d41ca407403005058070b850b950703903050b02c0d9010680003402c40712400f41c2034114001c5402c10030001c15004819201c05015460300c0e41d801519608040030304021041180c903c030242007000001c455500d4501e01c04946090720b505501003950b01e020b940350b0300d240c800e040142c2c200b050b0402c2614070010300349503c403c650006a08000c0c20101281c00c58540303104020b006a680d01081902c061241c40301f0000c480100d00070f14445045001080c10b91400e880f0017008440301003800c44c100040050003c00742c1e400c40611103a0740c42c28280c14003a505100329104013040421001c5490311340041c600512889000d0002c1c03085440da19000801402d014007151403c0c82e40c0709000c208480c0302000c54424500a040268441e42000b041500340f00341500183c0c822400007c84413800214112500509500b5040040307190103440c0044c2c018003040b0000950005001003044250400c608101c503129020b96500303295540c94120b042d03a182007006036502502500070007000092103c9000b0b50784140300d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 830825395 1250 830824145 830824151
    0x110c060103061523280b090d0b091f02040e060906060f0f2206140f07020a09051005010e010909051e072604080301051002010e1209040e060405031903 66
    0x7446014003843e140103103002c40ca04440c3e840780031461a0800760110f1030a85407100c8170043c035800d030515034241c3c00380c450f140d03c0c8080801c0b000c10550380e66100c50084e980042d4101d0b500d240c101011612044104149941307445282041758503403107288280c0d000c0d40d840c4415411103488040401c041d015004200f0b507030003c81000400f003410480000313040c445502c0044180ca03220070080d0200090101d4494001c40c02c0d418500b00076299006081801800000070202c2e6507548100e03617400780703200785107019400c00e64058000442aa00c2d9000c1c3c2c0c494a01c07011841000340e180e80045840706c1c0d5031300340f150004030640d2083c802c0110b264003960f005110700894403400b14500a00035644901101c21320302040c1c05008810310305508818200d045d00e100c0d9040003c0e0324140e5109a26400107025850081102015207000c2c24001d622240d000c10709503007128032a141000000c001c2e94000c07482c186c001d50621640112a02d00000c2d2140503e522801842c02d10701c06542c141c220300480c018000030107803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 830826645 1250 830825395 830825399
    0x3010e010c0f0e032b0e0d0c0e090a11060f0706060b03090601150f0f051c23090607080720160e07120f0914070603110c0601030615 58
    0x92041441c1a0000d40b1091401e641042016210402c180040b9000fa0440402c52202c180243d031018024085130f0341070030314010048012610740100040190308030011111850038000700c2d12551040301c10001400c0c00640d10400181c1d241c5041510080ca465004010000c45180010140c001900246100e0b4146030b1940c442c4016900140d0000c1c0042c40000701344101e1490030700c440d40c050a9064440c20b10041c484000912022071401c0d020704004407020303e0000c00b1711802c1120b0b00c4105c40550030f5008002501503000500042c0349142001c402010b180c20600c03280002148141d8002002d07158590311400c050300da009004158004001c0c0d0760111038002c80070390640b8246005403034010814031082d1652100c100703590b500704032541f10010b001c202c0d0140e481100518104440140401d0b4502c041411348080d1400340b00091464100182120800d2800190081101e0041d6028003c41ca000b0500c1e032070501c0b03030f1100002c40e900013100500124516805c02e03c06400541d0010510503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 830827895 1250 830826645 830826671
    0xb0a1701090207170a12050f0403080717010e10030b0f09010b0a05280b030c0304050c0a080d1404080a080702190302060712020c12010903090f050117100b1303120503060a0b07020301 80
    0x180100c8d842c00d1010103010030b010030700d54072022141c0d0103102c1c0c6c10540018985201c040c1004001440780540102e17400c8002103400e4150007026000b19445118000c50341004501640600b5007240ca90200e5031a18059606902c1c2581c1d0740802c80d2409030080c0c4504501186826020f6200450103401041c406c5002400090030401944035501c041c01c0d00380c8a061a29002e81484000c01d8190710801d44500140001440402c807074a96241c04d00f00461441c0c1c01420b01c04950203191300c80c01042c0100c0342c0d920b083c0008807004148541c400c94022400c00782c1c0c0c00c1600c1a030b081600002e0340082050240b01e001816600f1448070204441c0103e40e5000220300c00a400f011050040c016165100c0c1e99807800c043d00040d150016022190700d022035503049c100020203c012110044000300400004600c2240c803411000000c0c1c07010039017407607640304d04510700e001110452208942c11142c2250411109218809070390007074034000c0c0080c5031a0b10349180c1c040250000340c0f00f0b0307038155a600c940320241 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 830829145 1250 830827895 830827901
    0x103020c1903051b0105310507141203031302010c050703150608010c0908120a1808030c0708060c07020d0602120f090706030b030d03150b0a1701090207170a12 70
    0x75100341d40303081ea81c901020103038001c4040240d618520340e04000c24080b00000c169506040d1140f0003482c0c8140302c074081c0868103d0010150003070014015000e0115404520b400c040105060a80314081c0c158107808510343c0d00d01c01110403101c0c40401d00c08000056110381c1d00314448a00a0088845040d203984541004500300b0300c0300c003021992110100a4500280a00301084c99281802520a031426183c1d61321040c4c86086e6090748c010014540c103000e80150904603164051b94100410f0a813680c1a490b0741b540103071601e01551144d000700043e80400050b13203511580c1e101307a2150a00740c050f42032103040c0c0488982120496001d20041865128142c5d405104400d161901c03116814050b90541c1440d000e40c0200040604140804805880000700300380c150090340750003d00101f042003200680703000e90b0024110414002484000198081249050392001806044842e42d0703c004110403449460001081030007009100c180b000e900304091b02c480e5003a810308400a02c05400c10b038041b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 830830395 1250 830829145 830829193
    0x2010c170c03090f01020a050706050313060509010f1b020a1514090703030e030114180a050a03050706050f0618060406080d03090516080615030a150b011206060e0103020c 75
    0x1c568004901000640707019111034030b410100b0f0014112440da10340302c481e2140700c2c501a2109201000012543c3e0391201319105100ca034101408000e14109500720502804940c910800da071800c040d640c03255a404103105828200440d001012410041e42e42c5002031682c0600d8808800c1e034410000300408a00860f15200710002d4000d411101d0842c030300038003403400801455010340e1522080c1e0880c00c034020714154002408500b0168030842c0744100e10b242200c08403008060b4014011818101034002c00540f82c4076100c0c403001d200c181c0d0760720507401c05100c01322440740d80030301c9410f00861083c01c4803080a8001c640a040031074440e48607141c66141c80c0042c1c0e8084006683c600e440b0040c020b0901c9429129440091880102071500c4503040d581d100150000840000c05904c5110a81c2c081101201f21a07201101990180e080704120b030003041e151201d240480d620342c8882c000455a4414001a1341c259225807021014007401180250404060a64148545500c0b00301d88040c3d8455070203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 830831645 1250 830830395 830830417
    0x209010305030a030f051612060506070305120a0504021302160c0f0602010f0903090e0a0b0a030c06120c05031807050307030c05010f031a04020a12050709060f08010e0402010c17 78
    0x50740b0044814020101c1d5021a02c003181c080c07801041c08696003103031000f050301007a03501e000c00408c1c01b4038004c0310040000e41e01072903202c14000b90b44020107030000d0182800c0608040d020402c0c0d45e81c1d100d20710640b04210f40082d80240903104280c1c01c0d902c280e02812a407c080a020300069566503a03410000815801030108a41c00000c10024941c0c240508610102009024403e6051550300901121064040c85404600365000211030b610340d544040586400201070410503956801d18041c0720700907000d040c000a40a80300e00c06038a271207028002d1841890b039a903610f587c0c6c4100c581841d004008628a0441c0202d00c030000d900c0d80c1c1001100c024500640030807105514210000d4182d45140c4518020f060800081080c030761049001201d800105840c0581e85144104045a104048029003010709103804203000c0d00f0356010b4100004e45070742e80c5401400305c01100341642c0c045001d1180b135000e118030500142c01035214105085220788124039405000e8200c1d600c800c0e10743c2003c0d441c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 830832895 1250 830831645 830831647
    0x60e09091e030d06051f081b04060c0c060314010b090f0918010b0d0506010603110d02220b0c120a1106040b090712030206270106080615061c050402010903020901030503 74
    0x300d0a00f03914401c050003000f00700d031071002042d54503240111144c0b001a490040c04504d40000d864808004105850a103502c50544d903502d85440740548034114143c021b48400e42100404201640240310b0580d02d80c6140b9488045a072130000c10349a244c0c04607d40e40d030001d8000306820003980311803034464007802150340e0810965488002803421240610038176417091480316071110101d0300c08a03a05065034514074010450b2003240003041118410b10080700080c900c002280d42290114032013401d40c3c902c61036441c4941c281d9a045200142c00395030000c0b00140c22024515124411400046c21a5081410100d01d035400c491740c03087c248641240c084e642807200e43e04004400c0c038103003c14006061003074121400380001c1e0b18000d50702c0c00010849480c17105d4072032010a16104906c0044004040c030002131201c0d54503012813a80b100d905807160465240c04202e00403280c03400c1815a03540042040d135003e811041841150007801c1e003c1d000340e0610030009004005600d0703a6250703d0203580500015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 830834145 1250 830832895 830832907
    0x703330f0b04091104031a060a0e0711010e071412100e07030512030f070e010c021009050f060c0d050d060e0c0301080d0e1e0604081605120601060e09091e03 69
    0x3c003082e50807641d0b0b00d00d02c2c4c9404200500000d0701244c1004140c1301d003010807048644e6400c0115560011603044903100b102e900d2304215145501400c050781041240340244a02c0e0704464629507600110300a00710380c203046014202c02070404141d0086806410811903ca4643e03280ca100308a48804100c3c260a4110000074824003070200051940155903400f19172551030440811030305058003401403401c004003c0d500000980c404c00500300040c0c0c000b03004100080003410040c0019002d4414580103407041c62601c0341510701300c8203807140e0f038101d50040d0110780303200c02b0100e03480e40c49a0310000301180d5822001ca1140e4070205001c0c4240e02030715030141e4030350400c0b0716145000880b400c4a005c1121011401c21a41c5945402c0c2d04000c074105205449400d200001a0642c0603507004403040344504800100c4001d001401e4030200c6105840d000540e0418006654980300d090080728042511034644410506203507810070350010304101a00e18a800340e04103401d0240c0310f8020504542d00200d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 830835395 1250 830834145 830834159
    0xd1212060b04240c020a05060904020c0f0309011d030d110f150703060e060d021309140106170a1e031403070806040509010c0e09040323070b0703330f0b04 68
    0x1408036803d16040c20811030f80d00c1d0b4000740d42c602080c05014060320002c80c50b0070f00398807650160ba402100540645841080c000700031a0342e904610010741c0002c003920f0320102405082d0180c018841d5000d009010325825500b001d03140360124400014651007005001080c01100740200c18000004001900203410560310050582d00c44d60003030103021000301c0c1845400d0703468044026042d40d055403585a0403045034500301c010312100a025001105046402d144044107600c0390081e0b0300440d54804942e24a210310319a03549100c4001071014101900460f820032000f000a60360510034600483d20507420304051700c8a03007056403010081031460007405214581401600c2d0b20802d040020810074400090040000b400118998000c1030b500000c90245032103080500c40d42401c0814040000c0011304080c1440d0b4800c03603043d07821070ba00c080495419846401030308400e00d1052612043c3c5540030541031100341c6c5000c40d01e12024440c68000514802d120712090003400c03c40000c640300d501e0068 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 830836645 1250 830835395 830835449
    0x60607020d121707031410050102210912010501052803142119050c0a032105011d0c04030309030201050d060e13021c24060906090504030e0d1212060b04 67
    0x74402d1f1240410310240b12a03680012140360305105001c03e01c0d49032049060340c01d410700c192105240c1241d00144c14001a0350150003890403580103460464083c00384440142e01c4681c89401d06101c0c1641c00403c0004c6820803800140045110060390b010088511a1100d05066514811660f405c082003203c0d407a0900301c407090641e07a0504007d45002d0380055096100c0071082c100900b404001c0d60010344140300d50340444e44520641c102044a035840708045007217045651854904c4030038180001c1c91034020340d03054908480d03240d00c4040582d41507900548080d0060740381d191f800c660340c1d8400108000c000d000980140c04908526000c03040704d0040c030801031840c0f041409400d248222120020f09901d4a40740c98401681031440c49081400ca244050001a0300041c000b038281341c4007084158a80d0710150080388030f5101d000007001d00d5001c0c0100380b94200320123007020003030004401140b4002c23000c070015240071050008010341c07180c0c84080c2a40164200142c0804001c000c0b543c1031060321 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 830837895 1250 830836645 830836651
    0x608030304060f0c210e0c04020c031e0f0301270f051b12130f0b0c0a080115090303030c05040807120b0c030f04020d020f0310050906060607020d1217070314 69
    0x118240da48500c3d00064010701d600752145d0f9080c0035540350003043c2c10030b009024140c41032000038800c2d9030f2a095140c140740c2d0382d0015a0501a454048100c1c40900a903400817108009160b0665904580c41c00990102d80f020a5801103443c42d40440025031402e0306100300c0b8408085440300090714140321745001d600700120002481c40001c100821030a01058602c0d595001e03011400c1c4500c0d101440c0307445c0300482c03800c0c1e0008200b049940184540070b22041d0190551054a90b07816041e40e0365030140e00c4c0d0f102c1d0100c00c801c0100303a4055090001c40d200350000000d4448030309001c0e16056550745d000340352185941c480311007180340c03030001410071005502e00e54000800d13107074150030360615a421110148018000070f2040e210042c4140c11512074a00200740396000405849088500a13031071805010201c40b00f5440d03004017400aa20340c40c040c8180e8501c660040c1c820307854030003203650b1280444000c0e40542c0070300ca8100007003101c0c00703145141c00b886149550340105079070392240000c8000e04c8000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 830839145 1250 830837895 830837897
    0x3050a03084212060f13020901030804050f0604060509010f03060b0d061d04020918100c08040606081b040207060204090216060b090c16110613080705031902130608030304060f0c 78
    0x1620f00300740001c0010b401034100324a04107040d90b03911040044c0e900b103a600c0c00006e4020124800000a0144603c060300481d4003d0310503007141548801000654841c40c02201c020400074002e00e54503501c144c48045900016041c0001d2654480001060981294041d2400c190721401d041c0468008900c202140c51a017080451007400d040c0d0020b245050014114041c0b051403035501d818888041003e0900303802034540402c880e41542400502122045a003560164140b0200192596000031054540840c12800070b5210b1070740420000694400c2c101664032640a00000c14002c1c0e4610082412031080242020b800f00c0d0781c90144103039010103106500c200e00031420850030640d010100e036860f5520013100c02c01c40081e880c1c164a000141300c485138000c0d00115040c03501d8543d400411050711740907800c942560340c2c2d8004250f81e50800580e8003d00c8401c0c3c1081a0060404d2404c1c000040342e0800081031450700d038801d941c616001114241d07612900c80d280c0c0e00c000a070034401c078011071607e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 830840395 1250 830839145 830839159
    0x11090a0f0b07030f05091e091e01060c020d02040c0807080f040b15030f0f0f0f01060f0512030c0a03050d0b0f100e0a0f0f06081003050a030842 63
    0x24008424405004001020b01032110010a521545210b030044540301d001c001e091b87e8448080060001e00c1808100b1941d02511101d000300d0b250886080102e62401600024800ea0743c0c209074003140e007010009001c030f8120007107024080050303445014018512407103981707018141c81d000c50001c2c49004040c0280008480402c203100c0812007003203040d03034403640d501c400c280c00c1d00b07062003c20700c0c2041e41c0f0905c070094060001a00742800c00460306585445006003141c0f101e01d005290320342203880c5842441c102400e0750340d040110b030800f81c0140451403288030640341441288815142030401300e10341140001c40c0020b5800c00b600f941d10440c0300710403080e103035901144407400208904058590310a01440039074600039549170f44811040c0b0251124110f502166980c0301c0c594040d000c0d40d0b0142d0404a0529000200d605003500081011284c00c00e0040040c1d60036501e043c0e0b0060320141910000d11910400d03124a02030f160000304003c42810010048003a5214000a00650060100d482004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 830841645 1250 830840395 830840399
    0x212060f100e070c0807050f0615030304060c11010c1203050106020706050f0313140109050c0306011d0f04110d050f1005010f0b0f1218120304030f111011090a0f 71
    0x260075248140d100f221420401a90f1403241455441030207021002015132007500d01c00c4922040c003180040c095400c1201550484a1f02c0d0209a168000c0d80580b0b4006800015245c0c041000614810710010042c100340c01080c4568681c82c41c010315554403075010a031610010010720307504001c110f00a116034640b0500703050441c41c070f2000e18070006e000220400c0c00c2107111414002c450000c0e1501e00441c0c0020010a0007501d0300c1a00d500748080100d00c60302401000040421841031056000c0e18820004d1081c0e9450141d109603d8038003400a8481c41c640030b02000d165214000c00341a128061801003007008480202589840103e103082071442e8180401040000c51090759402035846c40040a03403036501741c1c889012140a0040541443c05541050003c10b06120010040c61804802900d140410083c8080c07100d10003980c2c010001100c4900103803a00b4480c4202540c0020341d207040e100804802184d48042d140c28004000000340c000456010a1400041003402007040e01c0032240380c68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 830842895 1250 830841645 830841659
    0xc0603090b01063b010e0d050d050307020c15070209160203160305120c040f08010516320d060609050a0302310912020c03060a0c09030212060f10 64
    0x210180700741c0d4140110350201100490000304e0030420328008141d035a007415441d564080040071600d80c618003003000001d0140c3d5900b44840146010343d0854020700e4102900c40d0304071b0345640003d080a04500551042500f140d80d111000100d510900b03655130b846a40b01e0040054250014294074150301c0d01642401460743c010041d60f40c5a014000307681c03500c2805041c03c0d22148200c0c441a01f200ca072880c03c008401cad10135805841a65140740c0e2800b900c07a10340410301d0032900240c07011030081c0e101000c048440b6105003a0010842841200420911050ba00780c50f010000211608007029002c40c900da1002414400e03000200440d140000685240402180001d0451300010b8000c030161a18510340e201090401e01140041c0c08407070120150380f0f04240020101260100e4040d00050004c0f00c02c140f0008074400103100040c003500710307519651402c10050038241560004d2021a07080000565616040048140400d9015100c5071800015020340d0460041850f1115058080140020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 830844145 1250 830842895 830842913
    0x3020703020a03080604020d0510030606060503011d3705101409041a070c0309090b1e011110021210080a110307050406090b03060a0e0307020d060f1401030c060309 72
    0xc0768240c04e10034500d44400011402a200350400d003980f650820003884404500074422030b04407805850200141512408111103a20080c8540c6150302c00d08640c01301e01071030300108582c0081e021201345c4c1e5003440341c02c0038014510354984a100c0041e48d8548a00c40d200060040684c086202884020341034104000c51404001c0c031071900c0d01401074080050300700204d2030701c0c0050300034112000380c40c07915219100411b003100300501140091540c0c18002050041c42c004c0a074500300c018002d101d1601700940002c640320041c1d100c00d040210300d0b0f24508240c60188650119003402c60800740e6501e5440d80324100190307000d042c017400b00f080a030040080c000c0c041074884506034411001180d500080b80040e1404000d504404c0d0720500c0c0000c00641c849855000001c081800d43c240ca1150f07603203e810b081200c14110041031190020405807005291541891803014810200020105a409a01d008031900702c0501c88507030b24210010b00502031b0600700c0e040101920303e17081c00302141c0750f5510003003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 830845395 1250 830844145 830844163
    0x1180503070b07050a0b0408070c0605030613020c150112020906101e02070f0902030a0f05060109060e0d1a040b0903161403070203010c0509150412030509061308010504030f0302070302 81
    0xc0b80300c0810880c003008800d0000c21422a0040d10807051810282010906a0311804040f14464080ca4001074000d00174015203110720b10003045e580309100b018003120065401010000c0b0540182040080503401e850b4080d8081c040d18010200382e00c9640c030511001c00e0b00680300c5441342050110b64800c0300d81c4138142e501c1a45032155440c00703008444a00741c0c60400c451b00010710200f030560f0081000900e65018510880940b4024000c1d02d2011143d8001c440d000d80c4c10380d002501c880400c1c0078050180003550b640d148060302160340002151107807528204403420428582004400307010501c07420550301500503170400c02a40c40d1601020600b4184178000f5801400d40c151900b58a5503044c081c000e40f003900e85c01800912202d00d03410001483d0354000007600388951301c0510500c00d10302d0540306070f400340c41c29914540748007507442e00d00360707255003040e8140380c2e02101c00c00020135200c03403800c1c0300e5000303000c1d00d0004107140c289454041e16581c1034a80305800c1500c1030080b400400d80c00910046 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 830846645 1250 830845395 830845409
    0x54b07081602061902150114090622090503040609150801151205131205090d0b06060c070f0e07051207080402041104080a170a14091f020105060118050307 68
    0x828810544080303681401110015140403080c4e000c4400c002c0d0b000701d24202c2d841c0300320b883c06c240f076a2100c181c4010894030404941e0000c1c0b103580054160700b0001115121000a4030002100704030328900c803000e031942004101c40e103800114040151603048011203029007400e60500b00203544102000b80403504c144199410b440ea564908041c003405498410004881e06000b44158039024907002c440001030801281c140700c0a40440520500c6002982d1540c1c0000b0860320003070f0615103500854403006400964406810401d012544a007003146000810240002042e024941701100381c69240c014030110910404103c40c15100032058080c076400f20460070801980d4440d4000b040050150f10108984040c00080101307581d60000380300350701c00d80301ba1003541c50b80d0048240c03060103005042034030022030900c14180c2d0060160300d0250840c48000b07000c28002c01103c9200c04004101149580c0241c0d5450051000c2941c1c4503000608440e8850029480c042ca0030380401c0c1d840015100b060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 830847895 1250 830846645 830846677
    0x203120f010b0d020a092309180d0c110916030506030313060c17030a02130824090f030711030c153403080117060f040201054b0708 58
    0x5c04090003000c00c0405004000c004807030b0a8034022005d4000c1c0c007002e1440b40326001c40700005461142162080080c018420b005e0510f15034040010384003003641e030004440c01000a10701e58020345442c0b44a81c4030f80b40031001c031098207043c2c0001608448002d04503078080c2e0030800150000001c500101c2c012600c1c180f8126200e8502414140e250024102c40d000c6060000030a2042000080d0058500c0760040381280e60610b035540d20bc82d07550101da03512a20880146010720b43c140500c020407550010b080350548540f2400b16480d60309584c0006421140d24891401e0810141820072001d402214240e41b000c10141c04041b40f500c09000d5001c01034003401c502c45c251181034601001e041000354240d90f1190b480440c520300600000c200f4040d091611201c4284910594800034a16000e0a0000c0341c201c0301d03403101d17001101c0035403124003580560a4a1040c1c44500485a0202c0401c0d58468181240c0011022411804404c20003c4a8407840081c00601c000c10001422a40c0720300c1040901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 830849145 1250 830847895 830847907
    0x210e0a0308070620090a06030b1c0302072c0702030a080f060d15060e0c07150c05090306181218210a0c050405060d0b040f020a0f03030203120f010b0d02 67
    0x40f00180c810300c1c5a0f4214034041c804c1c044501c2004001620b41c004044030850001ca490304011030480d0b1412005945c040c0d5211529030304883c100340c0e19840c890082c4180e9000c551181564501700f0062905801c940c0c10004003032004d179045a182e0754004001c1e00c083c5250101c1903000910384000501201d41690001d004600c1076960404039000719580605440c114009130400800244030b50701c40c001340c1604140c0000d10114210040b07034841c6510101e0007031b041c814461840d0007031049907400e00a2003c208550f6006580c104003040c424505c101c8901700100c5140110b500b802c029007909032440e0400c0c802d07141d007030011080d011045041070b5100500200d62140d081110081e02100903024001c541c030f0fa005001c101e04400b4141c0f0310580c1c052106841d000140f00f14007a002002400703480d4804046000900c44c603800c004207a000904855a080e04d462032801d04007029402107025a1000403038442481c0e6143c101503000705260040d000da580b520308030354600d220700c402c0e41c100344c1d40c0002d103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 830850395 1250 830849145 830849153
    0xa06090815150d0c03060c0804050a140a1e050c100e0910030c170c0f0901030b0a0b09010807080c0a030b0f0a0f0203010902041e081f1107210e0a030807 67
    0xb07070590307104000e200e1628482e49041c4500d486690340019a0711078201140c100007107003d40c0071307a400b640e030002c000d00a0f00c2050310350000500e49030384c4400750740c0034a00f42070011070391400075110b010f074401803a1040380e0481d00c0c1c25071400d12543e00d5103001da0b000d207136040c10550308124114007d290503100064650344403160300520f010307181c0000f40380310305c1038102140c07074201ca4800005080d41d641c12290250480010810395020400c00d10364084031100040c40000c44015696411200c1503c0200d007034180304000078251107013601701a040b94441101044100400c121030044500261070403900c690841c1c407240c02c10200241343c42d440507200d001003541e04480b58014000c4402c0c03910215104e58403208224040d5200b8442c00203c0d40c0d2000360b20281448090038a030407921110300a007a0203007941b0001d01003006e07098510a41a40e200c100c1c103900d41c5190002e0442c0b03031240c564054102409141406524603400a1504201040008001d00d40300c00c82400c0903230f50410241c0f5120003562030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 830851645 1250 830850395 830850421
    0x60a0b0a120f02090711060108120307030b190e100e04050d030902060d0203070c0c05030607020d140c0703060f110c0d0311190207032a1a091903020a06090815 70
    0xb4000d421a15440402880c9940300b0060309544146c041920016680c9007070030791352524283c001c41d8030010200041001ea9020fa400030070084400740005100c044041100b40c60b8040703a0780705601444000080219040f20709102c0d03009000003000d491190f0800ea01c4160741c402c41c07030050030300741640c81000b0001e565584041d18468222401c0a6607285814040201852403a001c100c030400d11103000460280350204119214000b075600419800414420885030030050522502030098200048800d0700c1041c003120000e580210b8001c213620030800798032411101e24119000400c036080c46800030780c120200c1c0e1f46132005510f01c0d0201d007103032600c1401d00c83d52150301c085203c60b64010394801049030300420060308403406600c11140c0c00001c91000302c0003005c10104914055282607040c41308903081e100d022440c140038010070b41840307080c2c004105046001461492a10b007846000c100b10b2504c4001000909507920f042c20300146411003007560340c880301904000703522064001811074110a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 830852895 1250 830851645 830851673
    0x40506104e060b030114060102063c06120102090a0603050705040b070f1401022a030d02032401180302060d0e0304181b1b03020f01020d0608060a0b0a12 67
    0x1001ca01c4003401a14000004040d0401020300035400d202245c0004010b0010003442448185c0280040303540b600021100c8030202b0b402c7d800102c02c06e0168480c00714010b41c01c0340d8035400402c080380c00b0742001c2081043e11962015010490303030041151103016118612b00d030080300c48a003004181501da88106482ca4012a0440040d20101084101c107010000c0140752169006221400443d100d14800909030700c91601020000100c3d40280108561542e0b030001c40715825000303880c03c0c0f2214000343c4099a03c2603500417111a860345240b50104040801500e6540c0c090a080c0451003030030002601c24016848068450000402c2e54900001590080d02614040c20b00340d03955a51612048100e4011604402d040c5600c1c00c68610500301c16514501c0802a050f114600c104690311240010541100720440c02c5016a030100c01c2640024006459034450369080802c20398249001b035854043c0041c00501c4c101c2c1400000f9440d0f489551044054800518512030001c0d001d05103609018212 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 830854145 1250 830852895 830853029
    0xb04030b07030b04091a0a060b041a0c0609010c110106230d0606090515060909040b09030d0903050712080f04030f02010b030a0b0603010b090705180a0e04050610 71
    0x21101100304880030410280c004507049604521f61182996602210305900454840d50f004001c00e0001148a0056415807032161004514051003c9a000d0400001703640592a583d1541d501d08452600145030030409005400204a1070b8500840c011711341d600b141c8420b403e0349441010700340c10b454800e0781502c8107810103828012603981e001100002d00040b03541c020b400311403119041071454000c0031221801802007112940d030f1038a482c0c001c00007d0160019000744800c00c8000c40c130340c0150041000047c0641c460729200c0e040d50401c0c0c40f40d00001c541032010004d011042182c41d078208500d280e04141c0500d490f0b840c004c441d900030b0740141904110a81d05204507181e21040120300d03000c00388982030540090011400100c180110401c080d034030407021400c1031006440ca280c061000d400c110100a142e6160180d0b0707600320031000d040c2624240c541d6008103040000b07e90080c1200c0c0010528103290038a40180003862451540071140500001200321007141c1c1c0c4c0b0140b031b04000481c0e800c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 830855395 1250 830854145 830854151
    0xe06040909051606210f061a070b07080121050123150d0c0317040f030b04050609061501030f060e090a060507020c01080406050402151c0b0303040b04030b07030b04 72
    0x207400d2040e40c0301001a442001492003078400300c2e91a00c20224016461031245039a940040801905c10140941840340c80400d55291400141d10050010740180a000548419600c01d602d04114981460007407404041c400f03044010030206186110100b800300c800422211071900d1440c0890150110140c507460307009400707280c0c080102901d171549000304c030201c0c8080095400001800032501c04c152018046c61040070b0100086906d00115407000342c407400070149031036103810010700502840e40050b0f5420025508200c02c0005c00c02000b50000c088000030309031490580101c007404040ca500c401e04040c0c88104d50720304083c0d00d41055000d0407507814016901d02c0d041f0305440c1d03591181002913514604200101d8078260000c504c0032074046040e50788034625516900d5003005410003800172600900c0046151070054190030280c4003143c021b50700c0321006d01440701c0403001d4540c1001e1140c401d4004100070000720a05401700c03030031a80c0c410205a96035540c035406400604165a1041d0040e007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 830856645 1250 830855395 830855411
    0x2303040f110f0a0f0608160f0507141c11070b19030e01050106050310060509090610050d051807060302030f13020a0e0c040612090c170c041b080c0708030105010e060409 74
    0xd1039080d0096507015607404445942d2034487e2055104000a55000b060884c10142c403124450700c001c0401034001c4003006007002100c80780074648a0b031081450640184043e0013440554000c035002004040e00c0020081e950400c5441122071141d45181512032004031003601846009400ca0344191204000030002580d607460081d0081d4012140d81002c15003064001c21014091000d580d1151405020785207103039121010307c60701c4e01449149100344142441004e02001d140c4c0182c62040107a1844100c20420400100d40f0340f0301103800c200185401070042260700200820f910b07078004501400e05801d41294004540707d403000360429080d0f001c004080001d9421014010030850b48280d43c0d500980c49a6151002161408240181071000303100b82001403004600c900c145503545070041d10075210010b800601280c0710744d440307401d1400c0c031400d000c10050781090f00c89600005000b10707103240c62540e656841c114441401980d041c1f1401910b0290340f03446100556014050440c0708000d071003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 830857895 1250 830856645 830856659
    0xa170612060109050a1b0f0507061b090305070f1217090a081c031a0121020a020f070605040506031f030605090a21051c021303032303040f110f0a 64
    0x101301220700d0082d003420701c02c65115026800c0ca00a5003d9101c0d610b6031000071a813002250580e10003a416100309840b040e10101fa88021240004c00c1c0e03046403620b642075403035803030050300307107002a0b2002150602c0310324108000c001d00d074421070a20360311103007800303260003e100848414050070000d5500b16546601c0410030240018101082c0026180c444c040c0301c000501c21000d6404d802030640d03c15000440f00070040d4010503001031000c1e9000282694075200c010a01c089030000c0c100000141d01c49062011046d034240b0142d8082e08803803500034a06070030700010a0041c48080c0c806440c08034410250400b04000d80e0003034000d954800003c0c000c40c208102210b6803211003440c00e5524011400f6202c406050607079504141105d5901e540b8200321350202c6c8241c07a0700c400e124005100f9000c0081c82d4a4034140e01440010314402d40395445078017100054526140071a101403031010710700b00203000110b05000d054801a9a00080201e608800f00011035440348003400f4440c0c0000128401049103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 830859145 1250 830857895 830857901
    0x1305012d170c04030804030201030504060b1512010b0327030702090406020904050604060503121303211d0607060209030c190501020c010311090f03030c0a06050a0608030a170612060109 81
    0xc0c5000049403a41526802100d0b2018402c5210082a21104210400065019070010b581c424014a40014200381c00700100304045c0c8500003445211b1400a10202c0360107841d01168054905626003904600c0c028440c01d1741603c08401d0105000b40f14820b98084040820032185903a501030100e007000e00f42890300768040d40144c4000c81c0304a0600f80000c4540c00c0500c60002140c500400503c0000d0b4856480001c0380d005803840c50030440c4090000c80411030401e00b0f1805200e60300800c18001a00810081001e503260f03441d0086116803000390b888039554901611103c03034010900694408507200000d180920240803550049242c0498410308000e60b002c1074212882a000e0703d04001c0450011812030307202660a888180c4c00388400303070040c10055401c0d02056000740841e444d00e030005001d6441e000c9180ca04441440c4c48004010b60502d460103100300030b0210358001d40c10504035200c003912021940c103628441c0160040014200c1c5d541007101c12102d50860203440a03035854909003c0030f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 830860395 1250 830859145 830859167
    0x60507020406050d0201020c0f06090a18060608040317071b060c030509010618020f120c09040b060406020607030e03091206150d080316020a08030a0b1003021305012d 73
    0x1c618503240c000581810704864151035190f050b80940b00703403041e500800a03101000704106400040500403500c49484140c0f00301c02501151b94105140241c140d00c5c04183c8003a90084002c000b095002d000c00280c015903910041c00d41861140b01c50343e180f070801c88441c12442c080c215541c489605000a00041d9405480550190343c0d0502403a990740c511282a901c040c4103d91510b6400013003020508080d5001c0c0000100d0100400d10302503525441c80c500082c2950f0042010f44005084051481d06110f903265121003035598134107080c58090040d4440a000701100d06140d16140790382884d040c144101d6214102c01802c10000e241e204298503901d02c0c044500c1d17500c400c080c0c41d00c483c2c140307060400c070f1400950101d811880c2d0360b1008581000304c000c268010042d4402d0020a00c00520643d018601c03410300d070301000900d51458400c01240e00644a0010185841040301c1101c1d4910b0356194001c3d54403c1c05c10b225900b00361801c98a20a0144130240f08a043c60414240702a50080400007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 830861645 1250 830860395 830860399
    0x90203162408090706030209120106030c24051207110d031e0908091017040f03031b2304170102031603140a053411071a0f07050706050702 61
    0x454079040d6825580302000341c40030074060b80f1298041104510a030010911800e0141c4152100c0d07504500c158256002d40c4c00490b03020f91018410f100c0034000c1008840c440c1c0c1c85402d500b6180741d0428003e0481c0c496807130300000314a110f20004d00c0150103440c0000950b00742e0421910300d4411200c00500030501401151000c0c00040d42c0964641e9880c0118000f268005405502c0c0c9107146007041140000041c40c1c4042c00140e003000854401031041c201c0c4201d0145000048610307581c5001000c85000c0031605c006200300320890280725a00070022101035040b015010440c0c605010400e140d4001c0c0e602055086c4440091b404103040e06401a5004501d00146051442c0c110a42a0280c8030b07c4003002080c1640355000404281c0190000c1d600309071a80700300b0b41d41c02e00b8009c1c00070030300c030b44481c0e480151101e11016001d40345c3d200b020403c0141511010380110340c2026410402000d0850740d074224030301c020a5444400e16400119030005500c101120403ca03034645000d0000d0300804010380c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 830862895 1250 830861645 830861699
    0xb0307141305010e0c21091b27150303130807170a0303150b070c080d030e120c0111270d03120515040204060903020f2209020316 57
    0x1607030589801554182d80c40c400c107442d410381c1ca540c81c440240d00010740240300160022040716030a101421035500880001c005410840284074154482e48488540640500c4902101148191280e110150f0141d10380c44244240d480e4000d86050019070a00016498040010b8200c40c02030311524440803034000720203031000c0695500380f0b003161400c102e80080c0160060000000041d20a80c08500140c071611400400c0c00d445004d801065004024102c4411a4041040c0100641041000d00003031f810b04e81031094164200748540c98141d0803003031801419000c40c1581d036015003900505500c680000a0686440560750744403940c020411000c40c4064140341a8030481c207000404295007505502c3d020040c41e001c0544030300070800144001152510701c407020200d951580014401040580e0710700000d02d0840c010065000e0440626038890081d0302c04000540401c88032040c3d01d011b10800014407401240046410002591104410f001c0f84100c0803448100e00c4182c1c624240c09a000c0c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 830864145 1250 830862895 830862919
    0x303180604080d080f091203130f0f03030f150f0303030902030c061201061101090b0f15120c040501291806070609110a06081b0c07240e0607030c060b030714 69
    0x410345a180112041035118820000170f0031044000b207080140c240701e0704403008000700544bd001d05180707074460f0840019850344510684002c0c940210ba0001d03900242e1000b003146000e0b550b61441c2d81c0352000805241d11207200c0d6040d9076060001d0381200c1c002812132540c41c203070610401c020314024054030003c9500304103803001c2c4d070805100e000b950300c0c1e06c507a20740c020340c80b4103510b86c030601c200905d0000050101071043c1c072541ca5004511420903040c030010700c6142c01480411040e660160050075010201800c0c5140c0003030480120107861078124605640d03000072016519480d00d204044541000c0c0000d8401c080224581c0f02c03003d0f450203000260605000310040006416a6100704000500008080f50746e004604080300d00d00024803140f2403600000549442c10304540c1d030302044402e1940311480b4000290003560a03001c10143c940242900c103003000088090150440280030001c00840410801140da800103803400d000404494089583c1d0824441051400801c02e000300408521 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 830865395 1250 830864145 830864161
    0xc0305071a0708030603011e0501061706030601061b08040b1804021c020309010b131a060a27050409060c120c05043003110610050303180604080d080f 66
    0x182001035a40c1c0d1007550302d060b0258031540da090b00040c1035107a16560f1088586000400b4560b401c40c1009050404a803940c50064050704d10501c840d5504050801c4408000f000d030307804246141940c10504080703100c00704103c801c04003202d0911006015540c00100400c4080b488409421120f0b01101c04000c060b02030001d11007a4001c280c000390361801d200303031200b41641e0180c010f19401002d1000000e09400d032a40010000c4101e00d002d2940d00769074450a6201e28180401d2510300d200507903000e0f250004210000301b200c245078441421640305491900c41c070708041c2c0c1c18000100070041061140070040d0074920028031001a040020a14170004800580100e0207004190406500c80d2424107280c0b00d01300e9808271010f14a01c01c110403040c5840340c40003090005040c51802580c82c000700e4501c0056651a01d00003600801c0b110707030740d41010040e40c0d03000001c48102d6003a069074410901d4140e00411105d008a030404505801000c1030820741c0d9500c03600c22803003404000c3d4030203c8c40e00c580748 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830866645 1250 830865395 830865419
    0x11030903030a0b040e1b010201020f13030b0906070503040f030504090c08071101150e13060e0307050c03010204051012090b01090c031d030f0c0a050d1d0f0a090c020102090306040c030507 82
    0x1507001120b4200d05062880e00780d84074401044800180009842c01003945102402f80d801241c4113105020122002d20a104140d20500d038014000c0700146184d061035030000e482c600009000411141031a007003801014400d4095030000c0c0840c01c010704c801c04030100041c00507402100c400c0300060200f4040e01615105004110542d40c01c95600c08100b814680c2464078003c0040c8002d000c01c607414902c0c1e000031814442c04008001c07000143d03841d550f092502e141410344050768a446a03005100c14801a91481d440075000c900c03604040c10098030b10b450100c00f608075003201801100d20400000750050090300075801000c01030390100425194081d924410ba0108864101664401d001540c014405180245150b900000440300c0c4070002e0b43e2100d03d00541070320110001001c4030801c4180307944e00c0d0012405030b4422100100c86965480100342205046d21408030b01540762705010745650b000303604a940c10704026051741d419240c1802c0482120842e403000320b40780d200d2040300140340d0304194 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 830867895 1250 830866645 830866661
    0x703081510050a031503080705100603020307121406180d0c080a0c080417070e091c081306050c090114040b03012619060e0708030d02070611030903030a0b04 69
    0x207040d0140590a5801100c56411a2050105055032580412503c84006003400d000714800c0f4515640c900f15407400c103007090455040d20074030a05140081c0016034000c983c00c019118014101c90241e42c075410207010300450740324905070900030002800031038501d07030390706442c089001d008480c402400c1e51801c40d210038450f00c000c1c05254060000d001083e200340c030074001640c00307840c0d401d040c5a1a94014140e80540041c0c0c1000c0d540014820854410110380403907200c924803010b0200b0080c0c900082c9031103241054104204200301e0005140440792010201204d50400020041e604d44058410000c0d402145054082407100296180c04800f66003201d091391042a00d003411a440c2c05032003400700417014a000d254412074030300015180c0d0100984450281c4006850003000c080d41460011500ba150107a80c00360880641804090f10000403650015a010350060b603481441c1800c00050506001c551100d001c004140070f00d1040c00401384d8000c410004041160ba000700e810001116485 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 830869145 1250 830867895 830867899
    0xc05010905010e010e1c080f0a0318031d01050c07080c0f090405070e090a0b0c270a0b030907090912030510030b24030607090e0c0909010e040f021507030815 69
    0x1007140e58440d410200e0f46d0100c121104a4004d056944c04c0c1d5551809800101142c10307180d03001b041c900030850f414003c65400d12051b1100304c1c2510000c0d10300810411507130340c0103868107132404a075480396441007049500c6031031294240c94403240c031860f9181e01e90300110100d41c0f150301800d02c000320b0b51400d0050300340101d0380b210040125600d0300e800300e205081c0040400000d401842110004104000f403218030460b0b01c039102d260b981429071708440d0f090200f0140c0031000c2203c1021640785440b01c0c12204199201906016200d0f600e4040076490407202c2d400100c070446c02d05100a00f049600040c00b045c0404c1502c0521580c0c0d14000c07a61404a0144000b419946c6500c000c60f080f1110000e8034040300d04010003607c50f402141011074942507059454100181282008200d0f00034505401c980140c80b220b2194901180c042c002800540e040c007550078078401000100c0c0c2000541d5082c080801e6010b40420745d41d880b900e4240b2201c0d042903405501044480703002842e03032840d0781d03000040c00f180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 830870395 1250 830869145 830869157
    0x5010210050c1b01150f18110a120b060c03072d142b031a030606041119030501030605180a060209030c1210140c0d090c0b070c05010905010e01 63
    0x100006825036000301440e294465581c0320501d174064003403c00440040c00010480d80c8042d450980c5030078800340692100c1440524281c1d10075040c0b034801d1308507005c041076490480142607030103e4007001050101102c1d41e04c644002600c0c44142400700241481c01e008441e2213041103440802c82c055007503000100a07905600001c04c1c0000343d007400c410449419600c2c1114000f5400c614112511b8503040269101c03201089684090a47c2c5805840610b44043e140b0800d2900360b60042580c0e02c0000e0032052040d611823030b0480040e0320500c2a00c12260721180395804144003848094000c1c9801c0c00190303140c070300303000000e2040e10310f14280064100c03241004001c020055201c00e402904014071255041c0903c007580102990303012410004054200c014180c0c1d05080d940c601d045036503800040d9100b0609004000d0301c84d00d03031802d0f14402d816013040410141d58030714000c030106010350000c58414402042c80410720441d043c5c0c840a840d801c0c0c840d545481d88400055070000010480d01d400101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 830871645 1250 830870395 830870407
    0x30c0d24141b071130010b011412240d0b0a05090c0d140307150e0d0816110c12100c080702061612090809040501090204051c0c1203020d080c1222170405010210050c 72
    0x420305400d112f03032102003010304005907141c0000e064004841c00590741c40150703106100c50765003103204441c0c0010300c40004000c80c14107280419a040c5002c000038085c0c481c04040e600c0525001e20403182010392181029640c07010860080c002003052150003070041c072907030a00416180c001d0082d1800399060902025242000c400112001c0c02d892448102601920b4a0a100e60300d4040030000d4100144c805440d803001e15022403022500302c080c01104101d1103809102000b074020503007641000003164049503130440404d00750b03179180341002641a054035041446091101c000090b0548000495080c0080e9990345c3d085c205034001ca004450307000e9406aa119481a0080f603c140c0c054032881084440d1540c41c0c101d051a103510400550140e000b034464010b01f00e5100c80c025a111060b0001c007410a0041c40c285101d03100010b01d254100d44040850100091b900d82030726101c1540015040260b0402c40c00c00016504107100c2e50f800f501c59809a4030040e022030107400e03c078005e040b011a042003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 830872895 1250 830871645 830871661
    0x50a050d0b0d0203030c011d06070f0503040501200415030e030f0c0c090408090316062114180c030c0d24141b071130010b011412 57
    0x116050760015400020300c1e09140c0140c0301030014203085840c0d40000200e130085560031492500341580840500e400c00410001900d03000031041c0020292891b25540325074492401c0d50041810070b207440740c0460414001401200b0581c01841030b1004806c24001c007070220042a401c0d68001080c0e10a250024001d00c0c1100c450700000d0003150780140d0444881c00200700115074426070646080c0c0ea07440e000154207205040c1007080e01440000302d501090000d00d811001005600d040c28050400704000d45103044080d03840d0805403291030328080040032404c24014004a1051428803141a03001d405010360749850049501880404e0140282c1d01080c0ba41c1e0b50780f030450144080c3c6049940240341c04542c501524440d0b03040c070142080001d080d070f00300540c1020f0740301d9010501c011b01480402c0300500003000c1c1d40610b6000f4034242c0d0002610230410301c84969001410928000c2c01099000b0340a4203a415000901c141c4c0007a220510154118042842184615510410681d00c010080783c10b030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 830874145 1250 830872895 830872901
    0x3081918140105041a100f240206010b0a080c0702030615030d0c03081f08060c041a0313060903090b0a05031501021606121b020d090e061c06150815010501050a050d 72
    0x100f11400c05030715030342e150040180112400c8c4c100c0ca9140d03c05032078000005980341c110701c00c01010341c0003c201640c50700021072494410707d10403004000c003500c0810300c041800c00595121315070040036a102c07032811903528614405c800d441c8038420710950110026490242500c05919034140e03854842643c1c030446c070854170308062004d001000808401c00208800c0c20302115005035201c15485545a2500d544032012900c4103030101244603003041401001c5040040ca414020303400000800c06118034102a0303160403565004c880103c40016820300259807110041d4450700081004600500e1098012682d400244403070070703e034042c2158207108040c0078203081601c0d5509510082151040307140181d80c2081c3d50501c00d00540d00880100b040c4540040c80f18015103140c02928009141070310006581084007804020b440c0c407090020b10500410390043c60030f05800c900400301c1c0c0c03940c90400d59034880e0501ea0031030001508031700104056116504940380304286e0b5503424103042d0a50403407401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 830875395 1250 830874145 830874151
    0x2030603070e0403020601170d20010902040609090506010f05010c230d080411040c12020705070b03040506040506010b07050a1707150b0103150e0403081918140105041a 74
    0x105214900c400a40b010822261610991095000d07010f19454a0303084940c0c000032072840d512030b0300000031800050364000e403000c124819602944035543d03620344016004044070340020b50440d04005010480105a40180c0c03c0c80b07100f50100e410036039803201c0c0e0004280d601e002e014001090309030340801140c540c84030000803151808415445140d42c0782c40d10710307210650060401240e481340030042030000a065000807088196820301c00c40c200c000c0e004050701c45c0b10070b240c400c090b03000c150002440030401c03c05001c0d0075040807240da03904007800c0c06a51103a080f10b00300c90b2449880000b080500d07080040c0d07881164003070000c00142c2200e5031010001c650f61400e240c00c42030240445004205030383c02c034007181d40314042e000907200e000c03078001400d4910310401601802c10000c0c041081c1c0d881c41d41140c3d8003c0c0c15213840400c640390784006d440d00c0d40c103441c1095182d40c18881403050301c1344001464a83ca0784512203400b0300c0e014041d82142640e0301190090412040511142c940c408041041a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 830876645 1250 830875395 830875399
    0x10207050d030e16090c0f0e030604060213082d1501090b010e030114150f01050706050a1b0512130b06041116061512151a18040b0609070909020306 65
    0x181d0a04003020b80300d000783d04da440728070000d484142642c1c2298101100701412805032814561403001c940200303a907210040c00042c9030075800115100f07004604180f003806030141c2001c1d24014401c81c0c2a20480e0ba000400501c1e030f440c07800000640c401340020358400d000700c115a4176541681780c60181d07002030100c2d20625051203111605480c666030288030b0b410080c500c1c80c82980250a16803000e00c103505800074060301610b8100f014003100ea8110b000d0750300b0300b64400404200c0380c0d600e4400c40b02415034042d541d03e251142d4000b4181c51030300000540428448030b100649250307034031050701004040103003014041240b0400856403509180d00f284400801c040d0341c0a00e801c4111224188001e070819003900c0380c540c3ca81c101200301009103e140024104000005100c02c036903203400c4509009019000d10090b69400700c1004034624050200f02140c0041440c40c41c181130b0b68010304165421581156420346020000f4441e1801c6a011030240d11103503549c40d2550b06102e00d130710003540042e06083e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 830877895 1250 830876645 830876653
    0x1508100e2514030a0e1b030a021306031a0103030216060912050703170c2b1b2405061f0e0112020f0a140c0c0d030c05120405010e03010207050d030e 65
    0x300a04442c100843c09800c40242c001102c0045400c12810001004420390044000304101e018607036000603901f14140d01100e200354800f0300404131038010402a400109540025402c1d01103000d001030340745048a001e03800340c0c0c1640701c0b10342c044001e82c000740c00740c0310124880d00400d00900c5406c1541c213842030321407001c46240d1901c03504c404249080d001d61012090000094200404c4001e002e441b10800a200c200da00416a100320000841d00314010b020070440140c0250792a0220740150400180e0458107603960981c07100712800c50042c0c80c0b02c03c41d02d0349042401144007420b10003450b007454030340728000303044644c4641e41c00c40740b2440b003400319070405c00d00d4210444d1329038140c0700404240000412890340c8946442025096440d2100e2007101d2103024810b84010680100341d1105a1304c0c201c5800700e00c601d0600d002d881c4441e2214001e44240b05801001d183ca0780507000800584d40d00341c88412000d143d503000c041c2030f4440d0041c0140340b90420009065001e000390030500040c280c4000391 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 830879145 1250 830877895 830877917
    0x804080c010b13060f051507020d03120f05010510020c13020c01020702190816080307080f0d0507090305210906030406230a1b0c030f091508100e25 65
    0xd0640c0d100c81100f0303074034250380310703010030160b0003000303540c401800185e6403140d20610748614060b0700d002e903003000303405481d620805408041c4117154020100f00d41040800007140755012003001000d023409045d0261000002c09030540d400011107440b04500140080140443c5415500280d04419280390346503409002080060340c50112a01e014090010110b17803007450642010314224441010608100d00c0c00d20038050181e010003200c010704d41150020323a60b2880d107240e40c1d07064443c83c2c24064416182009001c095680030f1003c1049a020b10304a59148402a2030000c1c1e41250b6494034001500402c00d1401900f8000040d5074864001d070030016074125940d03500c5140d1031702e0300d03404c00b201c007108010010380300300c0d40c8502030410342d0382c0c1e551515140304090060104000414082c2c248500313900c107181841e101da2100e001802d004240b400d80c40c4580040600a604141d91a8401e10303032844c8041040c8070020702d000e1140e0b44c0c45565002c0b01160381d010011803017080c0441c500301710142050f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 830880395 1250 830879145 830879149
    0x507090503031b1e0a0b0c16030f02100204090213380408060117071d0106051b0712060f0e0c0d06020c011406040b09010e1521010207140d0804080c010b 67
    0xc1129118001130203006540400d00c0c0c403172401180202038800241741840400c515003180d0231481c250300e50505240c41102014401a8034203400c030301e109020a03000103408510340074036030003401e10040700b030b0510040251206400f10b1880815250070f0b074800b04514441c0c0100c03030a107080c1c180c8580e50307000c65880d0644400e12030b404c268003600101c001c07004039901140c1d404400c0141000900104981c00d001c18404090b0f103150004c10300c58034040003004100442506441207042c006420700d1421608096596515000c030285120029601140b4003061901401c51034003032501c041c81d43e9406026070304101c004000c2801c0a20b907003620415800d00c04031030200d50034400c2c42c00043c0b20b01c01d00741052a280003000142d618400606008003d500010050680c400540640100d003c00d80b540740e102c802c0001c40d040845d0f0750803012000e1118410800c0d01b070300c10350003410b0751406200710384c1d040c001c071021840d51101641c600d6000600c0f9038001a012446070302c00b416042200c0301c000f00c1c0c0c030014880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 830881645 1250 830880395 830880433
    0x913020a0510020d090f0b0327070e061809100914250b0c0c0103111210030611030405030d0209060409140109060602070608060f030a12120507090503031b 68
    0x42810090390051503242d00c1190800f8441c03000380b480c1b10340c444800e41040d0f5200160b00002c0c01c40050a1118840701082c120b05640d002000c011140440700a6a5140c0c440c1c803034601d0540b80c0500039005031042c800c4270302916586a1081c040e1400600c6140e0b139100d1a60002d140607a4141c505090030501081c69850500c462640c505c140f6120741d40301a800c440b51103460410781d1240f150400108413141110602040c640b0000b002400d000415420a10680b801b40c821140c807140440b845030100101310071a211000b0549005500800000502440100040c44241ca01a109610600800b04415402e80080480c90070182600e41007503920103070002991041c00442c41d006024100500808010b4800c8000030300c110b10090414030314007074001c1c0110038050219401b4004000040f030440e101041080da185a001205440703228014000074100c00208500381015030a20011400c914070598003001aa90010040c514120003135002004d8415a0304d540307040b5020342101070100d000450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 830882895 1250 830881645 830881669
    0x6030a02150913090201120c021c032004030803041704170604060b0102010b0f0f0411120711210d090606080c030601050312041509080601120b150913020a05 69
    0x21244580350682c1e4803c0180869001e46191501d070f182c4100800580c0e40242003182c0100d800300000b82c20001094100d04114a6589245a02640c0000700e84055455440814141000601c3d8420407960440701030b0310344210721000d03000c0c02051010901285e06480518040d0380310081e014a4036075104040c8030b1a01b6510440c80035034010004120912445014180a041c1d00f48020002c02a610300001d003400240041d41d409024040b4110506403074507480902c15600000400761503803c1d00329064050b06080b13440c200091a54040000803220005080000c216044103480c42d501240380c203503410b50803803203944800075100c00660002c42c02d07911806028003000409007a22040c900e081c540740c80d02c1a44454029800b100c40c451010302900c0030b030303019245840c0c451b03000f00711068021140d111141c1c000c01c9450180400029034500b0f0300c0324010b2807600c0360b81c0300341d4581c0e1060441d8a03042c80743c0100a4014001c000001e060300c4030740c01c841d440340340300034000003000b5150004a41024005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 830884145 1250 830882895 830882929
    0x91a07170906030c0f0d2a08101401121805190803280911010e030c0915030a2109140a09020c0a0807112d010e0414040510151d06030a02 60
    0x7812400c180001c44541130b0580d6100e0411850724203101d0b41a8000c401a8030610f440d600081940350740c4bda100340c90004d12060014000d20036101420300c40720041403503610499040c070441004220a44800904103400761b04180e40c0d03402d5603100010307001420040e40c216050160001c100c5041203106204010341d090084041c5000c0882036000540010107201800344a0350000800c0d6400ba40d50b08200c036407004092032085c0d9a0072200d0082850807544503002015010400d8418010156607400c0401e0180700b9655040d03250359402a40c0c8011244400080d0807500d112024040c02880c0e80003000103482e048202d0310804101c2c1c86540880d00b0072001240d60b01d084d80c0451000f407501c03080c0840c540c100003142e0700b107060400209261380d0840484042c10300070140c901441c15071b43c562112406899203030880940345854500f444c2c50300d04041c003000006240610343d24411b500d0b0012281518000220113290200001490003000c4c00101100d6262261500000058958141c007a90302516 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 830885395 1250 830884145 830884181
    0x1806030903110d2304050904020f0103060b120a0507110c09040302100218030d02010e031806160602210618151527150307091a07170906030c0f0d 64
    0x16013a100d00d00c40920b442c003064a240140020700285d500c0e200c1407a00994129100422800c4030001030300500203c0d801500c290001064801c110788108000c02d10031008404204807540e1214410344052a00b200402850352240c61020b01c28140b1040458205000e80103c40c0b6403114040d030300c1c05990104590905401403880f40909504003000348041034013285c0001d0000d01c000341c000540d2402070002025001c10114946203a9407501403c80d440391000c4100b41000c0c03120750810344041e50142e050031501c0c988140c00750700b00803101c0e4005405000000c04808010450612501e417102000e4000c00c1d0b080700c60007507200ca0b40e0f40c0e10188444115005440350300c82c002c00d401c018a40000b4101f500320800140d07900700e1035030358107003c5a088001c3c01e0b480b00d44a4480000403030381c9541c0c80d0403080e2444009102c074482141c030701024100c1c040c800d1085814025103490340003258050050420342101050020506029220004d8010680d0a0162500780b003200352154058402c880c0100b10b048503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 830886645 1250 830885395 830885417
    0xb01140a03051b190e0a240c170a2316050709090c0609080d1b1506090e010c05211b0a080411030a051510030c0f14011806030903110d 59
    0x241040300b20045c101d003140e007582101c1c545110071402110064400f01c000e0301d030700c0c0c000000303502401d0081c00036a00308540c00b00ca0010058440d1150b440a030356080441c01002c404445400c100c113024a00c20140307100c66050403501c5a20b01e0380034055040843d1140100c9001103007000061061245441c02601d10303c480c0c0d4503244016010340d1480c2c01542c003d03084600d0f039807081908003242d8140004440074440022881d400c09100c81e10000301d4883c00141010400201e4142070b401c440c5e0b9212681d03000b00b00c1001401c0083c0c3d03280c46958400001d14008400c41c9440075202050710b58404101044074400d4868041410400c4e403007900b50701e010500c82c40510051000600600c600032005030000c080703852140c3c48003580c640b43c5140320042d405828001401c0c040e02012403100843e404024113446a491b8880003041d03240c14082c1c5131005d001c00424900030f40c03080b180100c40c0546203000000003410032100b10080e000b840e0b025400c2c8001262074941c8000d0810a0b0405841e591ba208510300c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 830887895 1250 830886645 830886647
    0x200f010c030c05040303020601140406091d0c03012906280f08040b061002010b1504170601050114071109091006060f12050a0e12030a0b01140a03051b19 67
    0x686001c2d110003007080c00d01091000a03000190141510050001d0358402c030a4080081c1c0a40340c150050a15542000304205132000881020042c802c0000c0c140c0d00003c401d50103250032204040503048100031f802c2e4098019810b07042d00004200f4015113024a03200110b88912140c1d4030320214001c010a52100d42800190311000e40c45244d00340703203450745003801d045c1c441c40305000c0040c0103603104020b01c141101c8000c0c000d500400b001d22001e4200003c0718410181d4560310340081c45a0a0122000c08203c044103102140ba03074180c400584038000c40801c2003d05184a820881049540c01d0002d58494005d5481101c8a4071409522000b06120825a00392105440b926840381051006d2880742c11700c42d40c0c1000150b03000c2c400c90900050307d5510a0602d9000e046400c100d0b10144c010881c10b00544a10704c80214801e18002d4003e04c84c2d1362078800119038070440d03818081c44085040c0b00c05694170703100f03820054201c6820b01b031004103200300c17682c1c0410546c80410001d03217200104080040c0d103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 830889145 1250 830887895 830887901
    0x5120f0102030412180b030f060109031b0305060a05090a120c0203100219021b13110d0203040516050123091801090b040225050709020414130e0c01200f010c03 70
    0x1105c02008802c0c149029540791050102030074060780c42121b000000d0450744120101d41c0199080401c81c18852403540700461000c0703180c0015101800b4003400140810600d0140d01c0c000d11400000f04408480b43c0c84071802729200012703d03801c00004001e000090ba82c10031698200440c8080016946d19840c0d18807203d404407a0001c0003036400149075440d1300004010300081c0c40c042038403482d0802441c042c003040200241c890301060f41d00c000c1090540c451403580078521851040d022980ea00d0b00340001c419103120380303100d04c50005072100a010030500d000f500c0000d0300c07000040000d04124000c000206195001d03450400f0f1407403204010001c0014a004600c100781d4195401c614040c0301001d8807601d801c804440818441d0142c42d40710401504001c00001080030b15070031915180c9621440d81c451044c031410500c541c0200e045907614014621440090b00201070007025103440c50001902c03801c0c02622104102c0001d1614140d0100c4107204081c94110540e00000f50908403590107411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 830890395 1250 830889145 830889167
    0x3060a050f030a26180108011e1206110a2d12020f0702030a0302010b100503070503310606080105360307120309151505120f0102030412 60
    0x3007141102403103035440c0c4001c62070b400071580194006041c608039407408500058800000241c80c0b000103440805055146040120340302d0980c2c50750160b980e038054184082c1451103501911031403400e400c0003c01a040030100f0814451000801c01d20103580e120301560f0070455415000c1f41c00040036544040e10f600c40300041518883c1c030f2403140c0f84000c3c001440000d0551240810355400950341c20b04170b4121040d100481e50040442d55250381d07a24009000c0c2040c006924020710721000546201401107094900c50121643e031642140e81e450042440414a800b001c0d4800c0e0701c22504a03117042c440046600ca05014000200d43c4901d0480c02d1400c441009000c0c1320302c4154800c8801d080d9014480c0341c8000d40c403c19a4201001c4941c035101e05500c60341000070000040503480c481c8240c0c1503040303e080c190007007a0340300c00c85003151601415100036825071014801c508800f401079140c05d040d0601146000302c00c4800742d00154202c1422684143c8041c2d4140719041c1028020540c08543c0d524 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 830891645 1250 830890395 830890399
    0x3010f060b0a05090427060501050d080306061b030c030c12040303050a08090102091306140108060307090e030f07051609020c06070302070303090506010f080c0d050c240f03060a05 79
    0x121451405610705418014030500d00c0030010002401203960f660340d01b0589203000a0041c01151500d5291032070b415003e60081102c2a50510000103158074142d903a0490b40e641010b8003625650302c0008104540e4400c4071010030361083d44030b92010000042000d410704102c80001550350701001701400345005991840070440c010104000c2c400281d100c81603428042d000c1c10450007035100c803003455000e80540548a600032502031041072115a00d500100c0c200e52021034501030108044004440e000b07000c642d07040d0075921507801080400704d5a0b10400d01ca80c481d00c15a8140542d4903c00c0c8201e038010350702a074560b80070540000880d10031268a00040c07548403411440c0c03051500c409500e40100500c2c1d101130580c0440c602c0f00f414060340001440340c2d03101003a40c03000c0da104d070002070f80850f05018101c1c07148503481c00d9600c5030a0040d1203c25840e00b25008040c10381c081010403074040703072400c15480000c2c180d00c03401b075030000c865011300b40d4450384504c00d079200e03d00301090018540e203640c4018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 830892895 1250 830891645 830891651
    0x3030718030c09020309030f0c0717010c170615070620160308130501091b0f032315010e040312052203090b1201050406080a0309271a03010f 62
    0x200340b00101c1e42240c0c00b05402584a07030710b4183e040e0641c0626a9402c801450005403510510004202a400d0392122092051018a0020311a0803100311003903140c0440c49403448040d02e03610540d02d075540a2001010b03010120008507141200e5082103034221199500c4400c880101c00300000e001000c980e8280c0304a0404591440801480101031400360a106050012400300c41c450a92403c6260300040244030b041d803589004640c0c40020205003011080000001c11303002c50300d8840e030044a03080f548040c1e503090030f00c400845081c902c036082240b501c030b4410510600018a0f00c80d40c000d001040d280e00662510f8240500750100c6220401c00840c50700081044e40320000b2040c0320a16281100381c1d074524081c0c5426a440b84c400e40049000030000300e540020903c2e84900d4070705071403094405001c150390f92007005980c0d0685a0000f00826a11f0780c090106241903da40242d1008540030382804551007134207081144c000f044d17640b6000b1820000b80d49141000d002d6114202842c030030030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 830894145 1250 830892895 830892899
    0x2104120b040b0901051315090f0305120919030518191a2502030a0605180705030a030801031203022205040c090f1509150905130204060f0503090a0b04030203030718 72
    0x2030f03003001200d09008142004051194090564235400103500560100100108a02904028040b42c0115202217525001540042c8950101080700c51041629002d520281015a90180c449030000c980c40c25200910100c0594503586081245104100c0d14007040c5c0c4060500c4030a1500030400c003400a103040c03081284042503200c5603802640d00c000c0d603011101c08221440007a080c21000100500482d052000b070202051002e420200e031001c0340d40c226400e540d502c07024161201590b00010303000c00e46040040000c51002905c1204045a501e00140380920369000c083c0203c040c0c202004081031600002c2c0b085007803510600d880300042d4100b4603e56881c080b40040b125030540222552481800c00c0202e030745010707080350801303004035021844004400b80341c01800c20b07016100d000d10904200280601915543c402c48080c4c03845581c80c40d0b51450b007117105650070f90015113510400c0c030407a070286011564214541d070080d0300c281d001e103660b42030560380180b450241290114642000c1181 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 830895395 1250 830894145 830894161
    0x312090816050f010c0e0a060c0b1825050109050d150b01170f07080105060a09091814010c120b06120a0621020102010c09082104120b040b090105 64
    0x7a5221209800d03a20a01c121040c03400c0d50a140a0107681c007031a60800501d0401d00e90054040c046421081d030b40c034000299200012201d6002400c0003415074010322001c906004413141202500c0e02070a41124400c0d812803108448260307084501c1190030300d022405200940c0d115a80a0003000c00715200e404030480c4c2c0d103c074000c4c000000e03145245690340320507090540c0d00035164011076a80002907649039103810003051541c00d2040340c5090015590301d001090b40c0c6440d8007500c100200b43e0b5500ea04007400c00804000510740c0209010281201c84940c50010301c041014003100b51820002203105010002c01074014400020301c42446402c2203111072854071284c0944081c41815410910240c403440395890040c0035940050302003038103829401e14084885601405001c0c400e0b8000c000d4402819403c070381c910080d0040311080d8000c1d95880c40805503401a900e581c20030b54001e80d1600c2c4c0d030758104252801c0300d02030403070f0b40f043e100081000380301d0b640d01503075809007601c0001d00040c030f01034072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 830896645 1250 830895395 830895397
    0x318030e04050a11180319051e100905030a08101401140c060c0301181401291309060e0c030414070b03010e0a05100b030109020a030b040603060903120908 68
    0x600500903556800002d0200d683c03900032100341000e071010786568850f4107029150120400d041c05000c0d02c240104408609021252086d402c0e0300708010301550b8038404003105502440d050b44420900c02c601c002c4440140c1d51180031486071007070b0000c5645ea800580041c003a04070080c0b41102560301c0140c100f1411201c08080140c400091038441a2103446440d03020103401400c11001c0244030711402c0101c4440383c0c88c015816610550302035503a030300c3c044200505594444000784000c0c03041100400512a501c044240d5001400e6800001207030301c25049a082c7c0c0104004c042d8140551600b003003004020300c100d10191540039842c000c0e038a070200f44100743d0720001e031004100d0300704984040d00c940c0050108070042c2096082c29940c1c1d503901c1080b201d04040540d50110914038082c0807034043c2082c496050300301d0340c0c9611200d003160f2900007004000d400c508040c9091548a102c02c0c00f40346d940d445884003561054200084032324107030800a0143d4001070701402c0c000c0c80d001c0c0b128045004c0d10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 830897895 1250 830896645 830896667
    0x1c050610181104030818150306030309010c030e030a06150506040f060e011b050a230705061c0e0f061b0f0a050c0118050d0203041404240b0a031803 65
    0x40003044901c0080e218900512490b800580040b02c04038410782c0c40d000c0302c110900700c2c410480c0d021f01c40350925507101c09280b0058850540c10b40c42002040001e50082c002003034030781d004e800c09600c5800c0d8903000c03070300f440c185040440345250b9840c030407135603801c002d521a0003600c826100320b403c04c1d092030500c0320029011300400080c05071240151105a100d800240c0350b241140d01c07040d807030b01e9080c6492540c80940c14011982100148031803101c010811a0402c0c04801c80e04c020145246004203114541c0d02401c03103035807c2460012200b00c0862a40181420480d902c4002c0c04031400d000c017602e04006000d480045400510303254110070140313110503134034100c140000d4250742e04420841030720b040c03140d074042030310550915142100380020200120801c44c060707c15100d804551310f000300c2e03ca125074001c952010301628880102ca081c160b11550500000c13034003604000072200d210b80b03102e01b034030350052032080f100040000d00070394907003e20704501c2c0140ea02500c54044640e03002c0e060b48580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 830899145 1250 830897895 830897939
    0xb0609040f02130e100218040515042310031a0901090c270204080703061e050108030322030e010c050c19030201080108060c0708030a06051c050610 65
    0x19404503080c0100844645800d55000740381da0079107225603c000c0c0151007a91443c250f43e0103815490719174000340e03008940340510007440168200c0981070410009141c09080125582040c0e403006920703403514403520b10001c0c8001d1034a0441055500f40315800c1c8401002482d41e14a050b600300001a044840441c40f20100380094040340d9400d00000d00503d000c40000d00008882000042e90601e20740500c0c104241420103903114980c0f03884200203911031341c07080500071b6020701d01c00c00c0032a400750302907190840c0d441400e00016030310030f0b4000159982a000304e00550400400d10560350302a0394a092900d650960b0040314842545001d400c1c005d541880506100e2181941401c00805001c6041e030407200401d035581b83c40f590040700062410f50300049020490b9080082000540003c18a20598091903281c4c5010203a581d0001140c01c090900b141243d183e00c030100d43c6a403200b80d035482148403142000400c1c1d48034107203035160140141a0000002c1030b504107101001404441045403854 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830900395 1250 830899145 830899159
    0x1503020a02280501270f110a150206100b0306040b04061715090c09072706020d020d0e0303040902090105040b0d1e02120a02160c26070f03021e09090a05190b06 70
    0x210306284504007807011100392300140100c4080740c660196101007280440503401c80b204ca903200d40c141805c450071405481c10302d281c1417000940310f00d0260842007114001820110f209035888514141d20321218055020337503089503000410001c07000403e02e0f840340501d001400480020804102040d1000c1d20b0f000c1046202c46460701e00c0002540880c2132848900d100304c001c03031355442d0300030344903d1208110350060050301481602c052007400707802c0300058020091450075140185100003984070101d00ca05111017440001102c8441c0806007202000100c0081041d402c065140c1d08561011804010450710500003440040d0b15103085550001d840d5400580d11703500d010080d230401c0346844004000c170000c224041a007941d0b144410566000c0e5840c4e500d00300515404450325030031640694000701080e0302081026141440402c1c200e0141e4481d00340c0040071800c045030440404079010340d0303154407410013002044070401c1442c420303660040400c2d040d40030300d80d1000305180001e0001c13480b69403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830901645 1250 830900395 830900423
    0xc210f07051303060c03110706140c12010e0402031c020d02100c0c021905151c060501140a091212020f0706090509090f030c071e1503020a0228050127 66
    0x10007a8010010345004880503515400c48e0310301034000d072800041c0b4003c2c1485c0c90001c00d251007007810680d49400c3e010321100035240e0030203458035601d40b03000700140d034036200b42c0d0003028002000c050480022040e40d070103481f00c149010380180c070b005a42e000310342e00c107460a80d2101c1200d40c415110b0403013960449810000c5907400701d04184007070040e0031030f6a100702c50801020304014550000c01e4003011104410f101c0c4d80305400c0c0c03101201d008ac803a140c0861b100452042c01c03901414010032201c0154107080c0c1e40161610540940002c0720b803000c540099513429140003464040000c00c418811840061114500f8100c00a0409126214440c061200f02c4041210348209202c00c51841c0d469008490726107802d640f255541341103034401e44c2c0000c90070108200c408009802110242c40383c156075000300d1800340030100d00941c046e9030400c003103001c1d109445d035005801a2003221901202141040280740c2400e0182c02c517621181e501803d0805c0d41c1400c01c2d0a000421f000c1d90898111000d0b0100070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830902895 1250 830901645 830901647
    0x40c0501110120071a06090610051207050307020f0c03030d0906061a1306030c1b03020114040615050102070f03080a020a141014060307030b0c210f07051303060c 71
    0x4090107a507120700501d5405100c0200d00f8420292a00c0b0340110030b418011816100e801d0700001c0156203258201d42108005059810031444803042c08030f5a240991038204000c0e5541174540080d200d44001400010a001900340c0c100021800c040400024001850241c40001e070303030340308803002c0700c10040d21141d0440034015a0b40c000c030b0091844d501207a40281c5074213100180c41c1c1c41a901e29883d00300022011981c18441d03c280560030b2411345805102d102e0040503418000c2440c00c040301190b403580c3c0d0300e007540b00b070981001f80103074401c060108002c4460109541c5105407070708001c0c1154010401084040030005c1000100ca4000480e03941e0345846070801c9041c2001c01c1e0028100c0c501e820002403000700001100790560808003410054a1418080800441010389855905901001081c0080f45801c42c0c02504000611030b00d81c40c00070002c501110030061003901151b841c0c1c0402c10410769003000901150301881902d8198503003d400320032041440c0d0180405070142c2d55411a00c0445 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830904145 1250 830902895 830902901
    0x90a14030721030306081f0b0a03050f0c01030f0908030612070b030c0d0c050a0e0f0103062d0f1508150406140f041125060c020d020d0206040c05011101 67
    0x54803041e080d800841c405a80360941d404070b40041180064944240080c034a940454506110380e00c0811507805000c640789800083e000359041e00750b10403a001320000006004000e0200003804c102c000c0d0400e20412000981100c0403404018144c1d414541a00c0000f6540c204880e8854012505216140d41203840b07203180c070701c45812210b0124000000e0006165460001c0e204055580c0307003e000a2004981c100d41c07901400b2240008640c0300354500c1044d15025400205462040c9800558650390f8500c00a5030041065003d18461032151401c01e40100711015030081c00340d0704000710740b03035142c4008004000d0b6083d02c00020044140b0100c1c24949003d001c0708003a4030b0082080c04101d0f01c0d07104c58040c4d07001c4c50141d01c0c0b08480000c03520009061030300a08140f071440c07441e0303582001d0303010382c104001d0414418007a014910320344001c40000e40600c0303000803d1a00340d00400b070b4941740200282c60712241c60b111509640c888020403002640d64000030382511400c0c80c0040b648135102e0199405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830905395 1250 830904145 830904149
    0x604120611090306040503041e0f03080903152d060102120d14010608180c220603020d11281211030d050a14070b0c0306060724050a02090a140307 64
    0x40b6004d50014081441b40c0040a4030580e5a0703c0362850b0017824601c1824001c18051007000f1910101c01c504101003006030f0064080c0311806010b50f0581c900407451855210411034041841e80e0310540c9003065a00000d50964802410300c01d00e18050238203800103542c2d51005840a0400140007946100a404581180100b8000b001d022911540c441e000582045000c8914848015804003042c0f4003001c001132000708040c02130160f180d074141a24440c41c1d034462041e1140030440c1c8171140000140c440400558009028540480d40c2c88034040401241e020659520505660810205c08941034900c0814003100d40c502a51100c241c00c92912402d0082900d00d4503505000700b10b94007021035004001890546040e54450040b803592005000003401400c4001d0300000b0701400045101400800441c2c21403401800c060800300c095071400490841d42d140d90900b501c6c2d1605402e03101d1030318000c4a4001201c5007042d4140340c03038400481c0320001c0300e200301140c803e4545040f5484c3e85007032060b100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830906645 1250 830905395 830905399
    0x402030c0c030c100c0206040c05090702010b12011a03120d0b010e060a03050402010f0203040b2a24100b2d12061503090607051c0e060411060412061109 67
    0x746620a03828034540f03039240140b030b48120b5818100c85105e0688042451032040b80d01c843c240c407550b802c0a040c880540401854070041d9981c80220320340300d5441600c018181d6401c81d00215026214100442d82c0205800c02d503070081d0b101840000000c01c0300c23000d5a82d4411600f90004131404c5490048030804a40c03410180c00010010f8490b402035815000244114002ccc1c031010b2140710034103022640c0307118900c42c15540400c00d0140c030b0000304445200e20813a10030740c000f40c00c0100e11480000d0030b0840e121009211662030100000c0c2400289100c1540403010111072201d4624081c0c5904061003008001a00111002216400c0041d0031072a03803c40c0f030300400c121303884003502e40041401c001c0640d501c511420800780d210303e10942e45003c681c85201444054800d90301c2d036040c266000d8100f0308a1801003641d5030080c5841e0040741c45880186000700000f00213a0a045c180007584200400900d4041e0303008000502240c2d029955080341d0300d0380074000140010a100301c1080600803000925 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830907895 1250 830906645 830906647
    0x204110706091a060d03050d0e031902070902070804090203090a0b010810050c07032705040c03051609080c06160503030103080903060709050a031e0b0a0501090c050f04050402030c0c03 81
    0xc06014090b030000400c103201e003030f03010b58080021080c803407410b0302260450b500071141c604a40c006445070000d81110040303a000807440c01002c000d070070b0854208001100507440d5403103c0540311341e4100b104400522000c5811458072035607072611000362040313000d0400701d26000004a08002c07810440303426441e420041051710b40d44c4650455885881d0078261000341da0600001c5402c4011950444600350b0303044c1c031456101541c0140c555401003504a20300d111401840300080e003511940150000310445d03990004513864401c40084800030100aa40e04200301030b842400103450024066910513401c44000c0d441d18240602e88410000c4448000c2803800702000000801a40c81c0161005000440c162400e5654240085400e03030598130840b54000152001080032507000d034a420302440c012030840248030407035240c01303034080340035140540035990340c0c2c00400c542580c2e0300c0b03110000483c6141c854070b031445001007200c0c01c0c043c81c0220340c8181d600001154940d44020b00b142e02d4403100206076 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830909145 1250 830907895 830907907
    0x10909480915090e04020415090516080f0f0f0606040801090620120f0c070503190f2f1f0507031109100c03050409150302150c0712020411 61
    0x1030502641d8460850240c0c541010600a140a1a2030009440c4180c0c0300d40c015644039020070002e000310f10301d02c01c90003000306004201c10b070141c06468410b00440844040520885030000c2170380400034800100010700d801400090425084804d400c400301049200b460f8440b540002e01a12072541700401c01d40c0b80c600080200109504448020b0301480420080c00c007060b401c0c0b024600c038440c1ca90002c41050000504044907a6120603000303c249505a4185032403aa1001d180d5070003071402c4029003584040540810364031100084441e40b043c40d00c607011040f854444010700d1201c00c48942c0f1400b103100325588480e810090841c1d40503240d82400d820207403000d4040000c00e0196104c000003070601c2c20025482d04580220785120f4405060219814003400b003c503000c0303503041c1c4102c040100810000901e491740380200d80b80c40d07410548000009241d4410000107144c03080c80343c10b8202040c04840360000740841c034841160110161344d00c1400c0980b00080040c1a6410405c00440021030b407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830910395 1250 830909145 830909147
    0x1e040303150807030b0106080417070501021309051b0a020a0209090a05030a110d050702010903061a1207060e0307030b060d050f01110c0f060108030a0309020d0b09060601090948 78
    0xf6641241d004244001c1580d80320081111a0b640441d40540440685131040104040844c01084506c1c003550005081c080c0102401c4660040741e440200541d880d40300380071000c0c1700e102e940303030a804034026107a2030b1441c1080081c1d1164041200030b0720070780190001802801041c0103428640e40e2050550f9500c0c0380099014242001c5c3c01580401880f8400c1c00e4501c40340624200c85005405860b20496a86140d0351030300500b400c40050b61013000b40e2000d1a811b61150500050481e0004000d4014103007070000041ca0000d035484010303c281d2001d901000817440c0c5104060f003003502520200c007100841d0a00360719200501590099a602c0c22040313410b11039401d800b41041f190b0080585465100c15048203981c0d400030f001e0038090307030070402405148900036031200264a2000c0c01e0059500c1e09600e4070700880ca001c55452005411440801c200740da4040c0c000d1001e442c42741400c00c5291501c140a0760300d440810011604d4166903c14919014505551000311049100e041415901b800e94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830911645 1250 830910395 830910403
    0x201020304170f07151706011e0509190f0b0912030a0207060f030515061b071811040b0d05060f0d05150109060e06150403051b0907081e0403031508 65
    0x258080407802a402e011a001000248504005c0071566982203076400008003d00b0003100548000e040c042c01c1400c040d000c2c0c588400b10b4039081000d4591030340f075044c0d0b40c0500c19581452038030800318040c0d0000600c000700c40340d004c1000380c0d6030b41e9940940fa803049001190710414803d070320b644c1501c00070400b81c1c6c6070f03071340041d10106580c0382c0d5071604401805001c0540a41f00152500081001c48140c0311100f42401e4001e444841d61030791408040003030400c035480c186200394110640303400b9070080c40c8040440364001c1d24038821703c0d0050344c0d00c6c00307252500b4150310740107200110400c6a103580114485a1ba002c0001c074900d440102050711030f084528003965595070171110320854004900000603034940c9403040d40211101c0700c1410415903118001c00545881501039000940406d010120102c0d408105142e22403980b0f1100b5065903a03400e040191001f4000c150204026000301041803100784440d4503d150442900d0362000b5454602d0140e0141820400301e01c500480c140c000101000005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830912895 1250 830911645 830911663
    0x10204270f020307020a0609110a0f171903030b0d080f180306091203040c0b0327061b090301140a1a120726010501030f05060a0506010e0d020102030417 67
    0x400200204103005120381c0990004441c181c016806c14a000c1004c82c405400c00c082071403103008003d20345400c034000100a0b00729908402c0c0754200250082c03140b5000303408182c00404019005004200005e100c541c1801141c09005081540311901c507402c41d21a038a00d0140c0039401504c06403074039003082c088401074021008034080c02070039240d0701081c3e040210b1118020083c1c00c006e00014041d4582005180d8000741040307802000b00c500000b55036007402e0285014079a8504000c181c0741226550340115603400b224149260030200510002034000c4407040395032014000c0d0a40c441007600b00180c01083c1d400c030820102200d0b0400c001502251b0b9100e445c09680101c00380390b0210100c418003000343d0358254440c40c10b502450090111200754141c2600c00c40702120144480b1110400550940d802030740100e4006e080010b070324003009014090507070700841c081410006450103400007812039001c4e03419503000303804110b012010340e403007401282c0c0a07050000c108910b0310700003070302965546090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830914145 1250 830912895 830912969
    0x30409182d1203090b0604060803180d02060a080910110405040f0912030f0e060103020904110d1a040b1e0105060919030b0a0b180c03070c02101106010b07050a0b0702010204 76
    0x848001800c0c0d140074842c0303230250380c900c9008500301401514403042c42c2083c400c81e00d500c003030340f924244016500c1500070002e800c2e00b9610300c00c250030400480d9250281300c0b035091203294103116080301c0a072034901c00e0351304aa800710b80100f05010f0050b01e08004103d06a4043e01450640302d0550419070160081e00c3c151100790420002c01f40d86084083d151507003804000d500110400226000c92138550b44035800d000004d013000780c04100d07607541102590340171420702480003d003000c120a0220020302c80d64410000e01d96a00021414015452041c0381401400d104420208090a030b81d21241080904503095220180c0304548078103207040c21040071603409032800d04102c0040701a0821100182c02100411143c020584800301030018071f4000900307940c00c00403058030800250307940c1040080400d4454607968150f04480450310704000c1c0507040103c03102010044c0000143d400249080215007240002131543c80c0d40c1e404a002e0b1003160f004100052a10859181c001124400c039104070303040b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830915395 1250 830914145 830914163
    0x3150105190f090801020403150506120706090303080c090d02121e0a02041b0801031115040303120e190303020c0312040c0914190207020d02060c030409182d120309 72
    0x44d60149600b40e20480c00000d058000881a65410265030307000b03103410a034000d2503c0300e00010028218a0302e0082c1c3d0254002501c0e01008205141d040f41d400358200c896034080c01e10704010403012a071801c0c01c15200074050032010103107405190091008245a0f9060741e0705403406404100700320703601c04104405a11440c0b0701440781e41e00201c0391a40000c00c2c041d51705d90465980c619200d000c1c00e240032102d0540c00002003600c00c0c40d50280b060060010318400d4440c56000c85002ca809811508011001501c5130311404c41c0405029001919032945075141c40c0c090f07a600044100241580144400e81c1c24148440d01804108403100c2d01e41030075242c04010400882c84c01050200409106031000c4403405003603c000c07515801103400034000740703002a02c0301034800415070109440b540f1a28241d0b40c0c540000c1020b215040c403d0140c2c40362011011103098502c0010b44900f041000310280c504e50aa00c881e04020628074892110702c00705410022920451100003005006016804822511850 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830916645 1250 830915395 830915399
    0xa15030f151a03070e060307140d0203040b0f0402060f2a15090102030c0307031a030a030e040b030615010305180304091d030a0f0315030f060f0c021203150105190f09 73
    0x684001d90348144181e5443c0e02032021240301b0300650b944068001010131041a80702200d1104003c01401c240c180300780c00503920728090030b10312a00c1d003000d002009694800814007001d650380c40151008404000c911076035407113101d001411907815030610740650380341c403038500f0074002d90100e42c98428034041001d661007a980c1321445c0d4209d2108544000c1c051000748045502c0c02e2203580701500720448082100c10010000b0002881c11000d050210000f5002c0c02c0c007082c2d9400d16002d004100902500107150605101245d080741007080c00c0c0301381c101580c0340002044403511400785d02c0f04004440950f0394070381e00c400304c060240101d07110114890b242c1c0c003401020b01e1400811a030024042e5564824840ea29030302c1140a4100c003501a410400c0320480800456003000d41c410189100da80c1c005480d1044201c040b040e1002c00030b100d000d6400071004000712603080000c8030341c007507100100912860700f40b90041c2e51038040d49140d8403480c0d003406003c0c024640c019115a980b21000d44030401615 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830917895 1250 830916645 830916689
    0x30f06030a052e0203090f1c020705060711060c03070b060901060c060f021b030d110a08040b070c20040b06090d080904270c060302090a15030f15 64
    0x81d003500c034001d0140d40032010001c0644882002c0ca81c5040c507015492000e055401041800c0e60070696000e00250000000d41e80c24800400052240c600c442c00d02c2d40000e4501d50029480d50002e10a0a0041070005a0441081001400303505c000000401c000d4407602e400c61116540d4201c548200da8030402000441c915140200c0445e04851290f505c241d0041c4c282c1d80c4102c041c0400c16100d07000d0b40e400b0321901e24682d5107040e1198000380c0041c015600c41603000e222034140c2c1c41841c5c900c80c03c08004c0103080005940310782c0d4994000d800101c03000b070740e880301d0b8411154140030842c003034003810101e00058407203a08a0031404088808450602810141c3e60821591740320316204d1590200d180c1c03440500150381280502220b840041001440b00141c045036048440b44620027549c1c090010403940030030204010440c0906100e1034114180503007403002c10b52064080c040d0600a00d8010300004d40c8070301c0f035006640e8510300148144858000c020081680d41c6040c0500e042c5034480440f07003c010303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830919145 1250 830917895 830917903
    0x20a0f06090e0f06060c0f071404140105010c030c03050d090303023604330f0801050c0405011101021c02030601030e0a11090618010b04062601050112090c080102030f0603 75
    0x507001c0f0b0300102c20310f500c3e00000c100f9940c0c444200099180200f00140141c02d034144442d00c0140300b061400300c5840c039401c1c01c10040742c0d0514100c4445c6d010810060000e81da001d00300c154a80d5041c20b08500341a070764101501d00d4000c2103a07902c101d50808420008155040e00079084494500e00c1904054400703400120402c4110030b51145000380c4401500240d142c1134000007600f58075804010340303022032458105185e08640030b4107021440844e40401c0030700148483c01d0f00a1036000001c00c1607041030b40e204042486603105840c1000015404445a10720a5040717030500c10007400303c40c0f80010410040300c06034108991940c04a490800200b00001c004210041d08a90048240e00381c202800c042100341039000d00300d035801160441d146964118103038442400b0703042c01c80115441d541b44c060003e080e0060710140c0d004401640a84030307100640704005c54195042401d10190300b80203240010002c11155801504001c0705500000b6000340c19801507014115400f01d06120f5602e4038203155035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830920395 1250 830919145 830919151
    0x3b120703090501080717100b160b0108061b070611070c0609050117040618050609031207050c030d0e03090301020d1407050705030301060806010e120f100c050d0506030a020a0f06090e 80
    0x3c60081c6d515a203112603041507195200219920407404d00351200b4030341089401c4844201e04041c8048107103020722050482090040100f50010442c41c40c200394a4a0301e41c40c0c3c0704d54280040004100802080215003100c1cce1118801d2058940b41c8215040c0034040d00d5080c0704540114280007004540d55100b080050810300009002184607101c0da6102c5009001e000283c0b80c1c900300d429088000510103120007801451010025512440c1e940b031180740a50380949800d090160800014072003074408020703105004c1003140300044c0065140d0540d420b5101d41d184042c0d01d940300048020a5078090b81c0030441c41c0654405580c0140c0d90f115007074410b171090b100003400355402880108160303842140c90f164418018500602c03e0f41c05a0080746113856501e10120301a0410303629200c04103402c000100003040c508000b8820403901c2d07035000d8028490085003810540d114030003e03445450030041e001c00164064124280c1030358030104406913140c0e5000768000038040b400c0000d40d002a075600a80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830921645 1250 830920395 830920397
    0x1a0f1f0302010e0a1a18010c0f03050a3e190b0a06030609080309010c0c03090924061116030203072607030506193b1207030905010807 59
    0x9855425a0019181606404980d03a444615500040b400c42c484090301140c40c4560350300c1070f03151035407150b90049070300441c00120f04020750700340d640d4040b030b031925001d01440c0e0b0181030040e0f840c9807a00080701d00d01040e0044541c2030300c505180110408803000c1403c83c02082c070580c1d08d11a24298003950b00c881c500c00580404100311003200300840c03031002146030407907541e082c0082e8540e038a40d16102a901f41620955010b82e020007000880d02c828003880d0750014040ca07013074400391401da501070301060050140783d81d00d5070748030080710702c040300002d0841040c002412210089541d45800500300003164640c0c003038a019124940300d1070034005100200b505e50040103044001c0c100201800d21102d00006230700c400d14041070241104030188054001b0794080c8020704180d2502540021340411152188501c640c501030a041c240201c4280d0035901241040390b40b240b0800c1003d604048412280d4440c05502a405040c80c0f0011010000c2c5545803007074651146041d511360056440c1c02c001c99481c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830922895 1250 830921645 830921701
    0xf160e01050d03030c05160318051801180204120f06141015140d0b0f0d0b0408030603011512020112020a0e120f0a0507050f0a1503181a0f 61
    0xb034006030080e040412204010324000b8208409211070f071500348407400041e004074000c0300d030190154600b03c912002a0000392084240910642c6800800c5c8005220b4211014050b48a003041c0c89141d40480d801040e0002000100b001c6030704104244100d1100c0460b11640340a4000c1d50014800384d0b0300d44540204d0000c50001c9141071806550070100904000401900b0ba00030605100c0400c0505054154460000b52645d48002444445018a55064420410342d030303c0500080056918661007548030004548984510000c00d024005030205103550184002c00824260b080c44440c0e40128001d07a40c00350005034100440c0d01300d00c20105c03a80f001400a601c069842d042540442b062541c01a0442c0d54980c2040724150030081550002c4039240c0141408000c2441c0c050b04180822a00315030000c6881e1408040900c1d410900360300c401815103400349150142c444951500280b600900304d01400e42c0038400255a0000485e0041000300c3d40401240d010007802e1424280000090610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830924145 1250 830922895 830922919
    0xa050d03021c03060b0a050a090602030f0a05130b03010816150c140f011104091b05190513180c032f040b1902150603060c030405030c0f160e0105 64
    0x3021140c09650b80c19002d041d2200c10004010b0619030040c402c25425a48542d101c2c007807001c3c001c00c104444d07888002194402c0c01041048094070048480d01d034101e08202c4c1d078071105490b5180312110250b1103030b82803050120000441300350202d480f4003442050f08101d011980c4900710316000c02d420104980c00180d683e1000c000140421107030780f58222203d41100e200e4280c0c0f00610742540e101ca2008090301201060800280e0414001c0c210181c26105800c0341346030b02e4090007031841c091011098500700092044490460040d811542407206501c0c24130541a05c0d89101c01b1500080080c0d0104940b400d14840100c601c43e00ca00600c0025100c904e01000054406440c010071648522a0b002002000002442190074000741103003418191000c410040c89030010f0300b44900d2490894542071800c08120940d5004210386511035840c06a1070344940725402d1580ca10301405000203843c1c42040c010048141c00041ca246548247d507000344841500c61086802a09080c41119040f01d0303d2000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830925395 1250 830924145 830924173
    0x4030c0e0709171009120e0612280c0804110609090408030601031d06070219050c040f0603020d05070e01140108010506090f0a0609061709030a180b180a050d0302 71
    0x3d504403074407140485104d0142c0303110540460300c540404580580d41107200510094000d030010000d03040c02c0310250308002303044c3c030b222800010003803c0142d064802030040e0303401355140b80f030050080a244010004994440300182110105440c25182c0c1d810022420072689001703000c4480035080685089041d4650740d44004103604060300441c18183c48001b40c00e4911140e00b2454130b10420180101070500b003091000c1e0a0181880c90340f07a829200081d09004240b0004801c14072460680300098040e2042444030002d1070300b0b42000307611011050880b0180000010f0b114180c0d411054404401c2c0d980c0e18208202d101d0b0300c9a01c07404200c100c0e004011034500000649000d000140400c440d0b0b00d042800149426000e402520219000501c1400391640c0541c500d411040c075021101018280380355500c1c0d03a405540d40388410462880303e1442d8404008001c0c600606c0e800000903141c9205080424041c80300802d00744c0a420740f084009514901810b2060b48540c040d0080c1c00510750402d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830926645 1250 830925395 830925419
    0x1109030a12050405063c030714120a0507022802190e0103030c030314270106170703020415030c0b03130506011d090c0603010b0a11030c0304030c0e0709 67
    0x1518001d10105000010713180e01c40c0d90080a0060082c140e00741418600303040340c2d144010408840c03c3d0003000040c070002c5821040304981c1c2190700b90500080441001d030113a00c1c644200009550098448028400e581c4071541201d409010355030281e0b4107500f0902d0b0310036031440203804641030060340c4a42034005400c0003101110390403e60086900352640355500d00c0140704007a40201c00150740040d50209041c1c0c5032003828981d0107180c0c24107145081c00d00c600021181c00301404140342c1d0b02e000202c0c0d8200300950044c0024280b645400b55003001c02908030742ca4545911043e070065040c01c1c1ca0100c4140c41203a100141d950143c1c50301405410200340700201d0b00028603513500100d202325448003080c4100242e5000303044014408070322520400c101c0451140c00fa10b81c1c140ca43c0b00c00000c0c00d1b00d0751100c0546e41502ca00031080d503103940c01c1e0102280c50301c6003040801014000000d24080c40100800204140d9010304148203500e0790301e21351060200402c9461100041030b501e1b0510420b05001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830927895 1250 830926645 830926673
    0x1505030d08090d2714030706080f0f13061b02100212070503040503071e0606080607080703020d0b040509060f01080f03093708010f020906190c050a080a031109030a 72
    0x10855135250b0903515101c2090b00000d0f00b080040c110500480700c850300d410408174002d0106071a243d065402c1c08801d4001c0000080e00309c0042044000c00a8000c902001d9900840c0f500326206201040b407480d207503030000b520740c50508014015980100600c15150084440752403a900d0040c042d90b94602040b64543c0014108032850b0004104c0180400c0c000701c102520101d9a810f0706c60f002c41c0034503085c0d0440d80ca41d800030542d5003200007004040358001c01d41c964001079030f04015070789094181d002c80041c00c1c52140550f02c145040e091003e0321000103103e81c07044600300341c680c1c01071341c0741c150740c0750f50710020304079404541d1082050800c035040420f0f0007210300016460b040c0c0181180b10700f80740c01c0104900200381c00102940e003009100c1c0b007401451054110b804d130442ca0545050041082c2d44101000e104000014400710f440b01ca2296105103116070300700d82903c040090340d24000c50140d03c0300b040c040000341010001000340703d42e0701c2150b070703012001401800ca02c00c442d034991101c06021 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830929145 1250 830927895 830927927
    0xc0207031406010501030621020919090803180703024509100606021b120111030f0603010c0504091a030f010902150f040302130f1505030d08090d 64
    0x9010000000d52185804081c007074120010300455030404000508036407440d80300465219510251001740300c64540c0544920307406903108503280c1d580c1c0d80d00c01696056000481380c0070b4501522002030082c11000f540c0565025a601d02d00900c490b803801c0e07924a02400043d5000c2c02210120301c40700b2554074001512441c1100d40101a02100a4002a5440d5409107003002c03036000c0800000e10010f0251144c0d4030702d940c0e4200071107800d11400960f940154030056140828180c2000303060740d41c0c050a27401c080500d1000f4040d407418003050145a4000303072080201c0d4084000440c281d8035040c0101c04842d2000d54400741000d10301000040034141c0080c0103030040c40c403030b1241142a10705020325058042d2010002c1101350240c41840426900e40200030941b136000d01a80d12030300c800034100c5080760303012074541c0b1080d80487e82d020018411072008003001c44c40c1034030400403460392288400442d42704038143c0d20b200d8001e11080c4c6000c0011100755902da000041403040c51402800c00002d40544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830930395 1250 830929145 830929153
    0x1030c06110c040c0918090803060f0604050901060201060608090127062913020c0705010e01020f011404021c030c080d110408030408010b03030c070509060402090402031513020a0c060c02 82
    0x2070b040103e03007161300c13009904000601c04c800500046d104019900c0a1606842c02001401460389074018130f800082c0c03a45105031100d0351019210b50b1003c003030343e01621000b0803451895030f554034060b0083c9900d2003141c000c40c5000000810140040c400c01544a6820110484c82c1010501c0001648896401154000e03951030324110103036076a44602110070301c0c031b0403403903044c0780044100034100000180ea410220300401c8809414640810410200c030030038200f4510002e05440181e0a000c02ca1070102500d6103009032810b00780c804941118000ca0003a00d01246411018002100f004a808ca000d40410089010b000c00185079031b00600c10175041200001d20b048203003030144c0300e80e03019074442c281c0c40d0720210741840100713004e204004940d0310403401107203801690f20a49440342180d1242c9481401600f0004603262580d40460b2400c1070000c0045689240c110150f80085900515050040010111031000c0700d0980c0300f121081c44003030f250040007004d540da03980041d1501c04408811406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830931645 1250 830930395 830930413
    0x111c0f020d05040606050102300304030c0b1321080f040c0906121a070206130c120302030a02010f1a0d080d0203040b071806050a030c020106051203070b010e01030c0611 74
    0x841c0d07108081c01203100300760106005142800080c9004000f294001200c0040820204441000484001d60401c00401551a07030341d80c7c10300381c8041d070700c00502070a841c4101081229440c0d1319a44202c1d100d100e40d0410140445c0d1041803250082116842404190348802284800742003c9800e98000c3c41951000109500c5240d440140c0d001c1341d00031300510380800341c46401c20034410300800f90445946a60f030840e1404e62002036a841c005402c000700240350440c801d050241c2c107030644003d05018500d41088a0103450000e540354001c104990040d40f920107d00c01c0910740d0701882e5006048241d198803209045000c004041188041c21507902904010951103440d450000d14440d0f4002c0341d81d5042890140790160403424504096440001e1071001800926041400d41c1e5004030ba03481c00080307540201d0700c180e006080c542c01170355000c5c1440302c1c00500410000001c0180c20300c220408003c0d83d0ba40d9070341c1c0340000400c3c000200754281150b000c0c8005403294210502d84e044100490318608 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830932895 1250 830931645 830931667
    0x12042a06031e0615140f030f0405010624110616030b1912021905010804080c0a0c03050601061101020403020d03030c020304090f0204050f190e07050904060b0d111c0f02 74
    0x2002e940c0121503001c0404201213106800100422030306210081c2149407400c480e8098081d0300c002003060242e40b800102140500c4001d45c00a0051320304640880f050101490f00424104241480d09000402600c083c2e0140503011a9140c00360015617072100c07805541801c154060300008184070740095075501590011100011070000400910251b24840c1e03980d030041c0b2036900c003030700003e00301121031103c200700387c0e40d101d101d5650040c0c00c20708a940300e0b02c803290007505001411501078a8044081d001000740040852060304880c0240c49803014041d034002402d080c0c2c003075488080e40c49451552032501090280d00038588a46491055a1a01d515080300340c0071a6603d0084034405540801c0500260808071049001c0441c01c0701d07080d01a0110343c1e103444c2051110701840c000191101e000c258240c3c00380090340c003145c500401c2403200a850305c001028903001400f103980e46500b0036240744a0300609030115560707441c20744e241190400d11015008060010702407522026982000800000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830934145 1250 830932895 830932901
    0xc09280203100f0e01060f080a091a0f07021605040c0e090901060806060117042607030c0b071e08070905040f0c0f1e0c140312042a06031e 61
    0x50324a0100c6012a14184030150160096503007014041c1d081303400051004540040c0c01048110407440c1c00b08880e0382e060040030250000c440d00805804020611a0b0b182040e0384203248985c0040080000964640d0001c0382d5880e084221280419001e131414080750409811142300350605041254000e0b07101c2001c0303806181d0464681c0690795592000f07003c1e0701d078244030b00c9400c20300900e81419401141e040742030003144040c0c00100003802c004840100c207424801c115100040b00101c464944155080180406040701d504481c0301a80c103001034102c44c0200640c40080060300c0d11440c00001da60025910300704007500c80b40c00d002da4484006901d941c0c41c0560f0002c3c0c5821100400c0404594101030441d06043c2e40c5901805980e10f14001e00041d680340c0340001894074a0306050b00700c528103040740c0360003d20310b00759081d0000140903007142405003d094040e034031881c200855000c050086001e03080b200c007401540460604010441e0320f209800106001c0c5801148885030740c50402c0c44011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830935251 1106 830934145 830934151
    0x60e06150a11010510080610060c1b050604060c0308070914040906090204060e0105150703080f0c13030b150d050a0204051b0f09040e0c09280203 64
    0x7094801d1100382041082180204003d044c5004001650f42c940e000700e00152043e24003044042c855501c010307040b12081c1c3d90310002500d240d6200303100c0610100a942c0d04030503851011a0320f40e80d4000500c0141951780300c422000c0c107586400340100d0310052640c028442e040c101000005d52401005260b080d085034000390480d940d25001000b401c00e40c034040d4005113808008101490750701da28505844017100c00f540724402c100c42c00c620600c141440100062a0340c000300f4100310020846503044020085d1060800c624030080c1040b50351542d00959841d040317142801b83c4082d1040a105416909940b000d02c0d0700815180e555903101c811500902480c1c2c0c6d14005100d04080ca012120803812401d40d407a6500c0c40745c0080075880c2c11401d020f41c4503c0c0b401c84003200101c2e001942c01030040d4090130303102d010b40c0d4011002d0213400f04c05070a0310907174401c03000400380c011051006600c = true := by decide +kernel

theorem cover : BRFrame.Cov 830755395 830935251 := by
  have h0 := BRFrame.cov_init 830755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830755395 ≤ n) (h2 : n < 830935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
