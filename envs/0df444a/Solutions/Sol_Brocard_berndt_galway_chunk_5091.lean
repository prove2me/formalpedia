-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:43:28.200771+00:00
-- url     : https://prove2.me/submissions/26974dfe-6e6a-40bb-a7c9-fb681564d4c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 915467625 ≤ n < 915647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 915468875 1250 915467625 915467627
    0x70302090a0513050106060f030e012c101401080c0a0e0a0b060d0905010b1c080403080706110415091a030a0b0f0301090803160e0a03031d0a031103120f0a 68
    0x50342c0e01c69034407102142c8100c80e44d55805d0841e40c06402030004142c244911f5850260f0501c9400c100f414414020040340c22014501c0403203401901541c103080c5c2c20031031002c948400510001441329820307001031080c1c0c0440346260000040074010902c1511484039022403e107028407040c400c581091300008020749801008101a10740b0514542e00722404024201c9400101d00c1a803548074094000001c044109004002c1c103051072080c4005089011100304003c02c40410482d0126648105031a0f0382e5409442c180003d042d40014402c001000402d00180c000803c980105009603d9916031103000e4440d04000384485040d0303000281414280006800740c04150300414003e0b0005198041209201d000070382907840340c2104031a42d50001c000d1103103002d04041000e0f584500790401078420340501001c5654951244006401c10800d21490000d030840b0102c4030004100242905010381d40700d062202c40c160030500c1d00c034003c0c400c40600740c101c0c680304030a88a41103da004620700d00700c01c0c494 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 915470125 1250 915468875 915468881
    0x30f030a0f0f0c1e140303060a23190312171603060b2106090402030604080a140412050c15040b070611071a0106180e07170705030612070302090a 64
    0xc414000c0c0400743c004500850014460740e207000c1800724002031002c40d02c4c0750080700051070200c00065a4014418000d00b0795500b15040242c3d407076901e0360154038400c02406000100d41c443e4494001d65200e0301c0300001407912803030780140e900425484a400f6240e6500f210078540c0101481913003845075010580b00c04d11021005c0b503545462502003207051326903c4003100c607800150741844842d1200d08244c0083c0701c04030002c0d807140c021120a0902d28164006c03a403212002040100102e07000035001036900d0207003149140c2c01e4180f8245a4590791138200c6a41e40007400d20f416a0750b44202c2d00340c0384d40fa28014000c41403a81c40b0b001c209041c1131410b000c1400303d4002d210100c50464848050300410300c0359102078080e4a00894001480c142c10f002c2d40b610704141030b00901c0030018140c0c01201881c1c507103104801215084914410155646802143c9070390b4004824604a41c9004c1400141c030b500c100914010ba03030032150118442404245166550350310301c0008e4020001400044603010380d54 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 915471375 1250 915470125 915470147
    0x2150919020d02181006020706170a02090604080a12030513021011150a0c0e030a030c150e0a0615051c060f110f0a030b040b060d0504030e1e030f030a0f 67
    0x44c1442c0311206980510241101c0100d40034402e040c0494810030290754100400b90041041d414400e80b40b00003141c0445041070000c00c0210300032740006814030b16485d40c50031200201000310613a00790a0051402040000e1900c40040c0000d041001023060144a0b5601c000c240d41c3c0240900c0c2ca021802c01c0543c1c5c10036240764000c589000da500e1000d55260b504c8015841000e4481c1300080c121003821016003900600700419000c4d601248035040020303004055848030b9500160b1048041c0d902d054100c014241c2888860458061041d0410401200c2e400c86004030a581000010381900c440c00c0c00380940b0510309140110722a01c910342c002c506580d111100c0084000d501003a011007581d842c682c81d51120f414454605800518400120750621981159800c1210240325801e0030b50f0008507d4000c1c10303442c00c4115a110003081c105030060310411603184000d0880680700e1600a0540c942c00c9101540e10b000380940e203401c4100304000710842d00c01049030b45400c1180c40c0d101e0411901014a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 915472625 1250 915471375 915471379
    0x51f1109030a0f0303150e0907090e071211060f1c020a2c0307030506010e0703050402060d0b0d0b100303030e03090904030c050a0c180e0f0607140904050702150919020d02 75
    0x303800700d451441b40d0364008002038507024002212605002d202c4614203c120742c07004181600c1c09242040c03801000c0349100c03c9031066403080f0701e0305115041011014100c4520594031400010307002c040c669280c0c01500c08003c8507045846007040000c40041684100c07440324001441d08945200340c8110710f00005160144100c0200041241601280c0740ca119500103840b01d9018000421442086d15842c82d48030505150601c81c9040c00e0703010561500071103120034250b44c1c4440e4101c03c644c80d84006e0100c0d80707802c0705000a403420050b60140740c0010f90b00080d40080c0c100354048503407801c004116000014081e0169080742d9803510107ca89483c480022a01c0380200c0030520003250004070960042d02c1c25000510203d07000d541007000311b854843c00d40f01c140c0c0002480f080e00003004180c040e03002143d400c0c0310003241c010303a054421601c5504c0003543c0c03052030301003400540c940c0003c8914038280444245a12900c92940003035884164079081e80c130405a5000c03000041c102032003882107003480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 915473875 1250 915472625 915472631
    0xa03200a08070b0402130c0c0b090c0a030c060315050d1e1a061e1f0903170c0601052b17030915010b0f04090e0703051f1109030a0f0303 60
    0x14654071051558403201d410ba6400c101082844154a45030100c00100180800100305403030b03003031b0000340c4405641c600c060100404040003413407201c4240100303e100c1c1d00060850004e25220318110700c58a4050040d100040c0c0303041e200120709601c2e80d02c0751058410080c901986e80c10b40340e550f403418038554a81c82c8414642c244031180024000e1a40d124494000040d607201460b20b441840f03211034500441005042c01c201c4200c1c04c2c0d803904410a01031056064002400003a12041901c0b083c003190310040040c11103480409180c0160806440c03d0480c0c0c10681e80142d99907020010000d50384480015403554511100d0f20081d80c803440c03542014440c8055443c07505020044554a800460340c180c0a0b07004440003080e43d007010034040d80941281010320f42007803000140c40c40c0a0260b40280440b85590b2418210140010024000219032200c1200e4445400061141124074a80070301c3e001e03c0e00700040403004a01c80015500d03040d0000e0300400c45020207480d00b0500c1c440d444419000e05035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 915475125 1250 915473875 915473893
    0x1e0b03010615032f120402030f030a1e090828021e030f010e07090b060f0a27060f080a2903120301060e01140f1b0f0a0320 54
    0x30031818031190801c89440c0010218030703190b0004210120f4815441c103c2c0c08803603480180700c2084d02901c0d190311754a071400c00c0680da94030101e40303000810100c140f03d81c4404991403081c0b6a00058040000600b042c11109004032500165180605400303203001c13517040110b030946202030340a010340c2010340140c00c0d140680703400c0d000b181c10451450910042d050b1500b92042c06410200600390301089003200800c0b5101c02055007075103411703243c01040981c3e45c43e1181d00d9820f80c5c852050303e90f0381010020b495690684141d000e010b0f0003010b4025080c1c5910b80700c800310b64443c0f92150350211040c54803907001e44507005a040300c403200003c04d9039444d01d90f9141d00c001e0380f0400021402c00e01446c4c042a92010041c1030802d440d00b42d8004030b0b02c3c201681000184501a072094284000400038240f00d0405203110000d09180d0180b281e41481c00c503400b0440350301c40034a0038011984509180c05a03903411018031101902c4151040c006000314910101d001c03078035004d50380280340c40740200c02905c040390 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 915476375 1250 915475125 915475139
    0x91306121b09020a0323060f0d0c090e0a1214030c0901051e09030124210807050601061b1101050307021504050303041a100b0f07050f1c02011e0b030106 67
    0x42c0044c0b0f01040000c1d60707600031341c84a050341246004559111a00e04000d8505400024002d18030100014046c03040880e0207020002d01403013030300103000314071018044459581041c964540c0100c40070350700c000e01703003004940240c010001d242100c4000c4901c03900d1982c0b030300690790b400e40c0b0590b5124100701d41040402c0d80c29494060604409003c000302507540c800300b00425007900c0084080c9014005400c000a00507441020b2200c03c42d50086c540f032286060100014101051090010301940d000007021420400c0c00f090403816500e054984007288803006120034101102100000c01c10481d601034419290f004901940d440061841101d200314601d03210301240d804107603000c54865001005020410501d1902c10301000c40003003c80d42949407003d01d00b070440d00c0c0380c854040e030b280c00050b44240c81e04400d001c0303a1000c0d8000d01207521418103c20010b940f4420010a6800ca041c51541c600507a403060041c01c4030a0741c3c0b250798488800d0405e45500081c044040072a038150b6a0f100001141 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 915477625 1250 915476375 915476377
    0x120a09030c0b071d0f010903021c0c09060305011407020a020409050708010c0e040c0309050303070516080301030b070806040209031f150806010819021806180c091306121b0902 77
    0x201050759444201482c5003407204e90080111154910400c00340005504590b401072150341201d404540c80301049851280c280c0f07542c01c40800240c10b031074202501141174401d6420150441c0d110f04000c01008505910090412605456000058100c40c61280140c0782c660480003102e406001034030001d640d23501d682800c42d2141c020b46008a52200c501c052545041d00c1480180600d5003014004548590b0b58140c481c4001400304050120105120904103510034080e1003055010200d1656941c490400916024044541c03900240c0c1e07610014002e418503000b95500010050001c2c01400006003848281c540181d4840c0c00d120780d104048060191208038600c01020428080c200a5041103060b5003801c44001d110000038900c41c1e0300034016150190f2140c105000b01c8060007050300c84000068150050f0800e07110100d0500382440307640040704005040d826804c541500190071002d4410080d22054440e040303031400c80070b040801155205100c007180f00180d440382a440b0352292040000c0f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 915478875 1250 915477625 915477631
    0xf1e020f1006140306100e070302070f080d05072c0102010b040f2a35010e01170a0c0302121507050d141b1b060a090b0c120a09030c0b 59
    0x2074682c0700c2c00200004000c481880802c0036064000c1c1c401072600f160544241a034a00c0b90442c40c0005400043d03160348a0340c1550505079000032104013a0702503003400056a0004c01c5842d803602d02e0240440c00c2c9500a00b4805400910340d45c051801c01d0303102c40b0750b21100c440da90065040d5501c40c000c01c00503a8491160100880e402000040c0c0032110b084400c0c40d9410500d052000d102183c040002c0c50f9070172161603040240215210b02c10811000201e030043d907030020b40c20720712140000c008203201806038240c60507224105640b0b00c0c082481021255070702c030495400b400c1206440e5080c005820a811180041c9102c4030803252072880100c0b008507105411503850340055004120001840d1440c0218403600c07608a55866242c10034200c5280e0110300066103d1145a001a2090b890038507070000490050182c001d0365154500031030303100d01400032400121000390b0b00d800022112405101038500143c80d448003400749036920036244005100e5528150f05109104142d0000100c500940901c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 915480125 1250 915478875 915478903
    0x905060918041b15021c050408031207032301150c020d110301050703020403050c130608010614030f06010b0d05040501110a0c022e05070c09020304050a0c05010f1e020f 74
    0x3030100c9043c040b854010f405038221070051000f501681210941c00582d1443e0446203081d0201c52401050003640c05214940c8803171a5400042000ca80946001040318448c0c41c6d1610305101002c2d0081800a1900d500300480c0082a08600144880c20b2149105600e000d5241840e242e455500d40000306041e2006404a40c00c80401840554600702030217829003144150500f5400c0070304540d501510b894200306d0443c050305642e0300f0306d80c2101c450b401c140000c1c12100020003d154450b808540c9140003210030078000d10031080703050304440e40000c110341200c203500d40c06030504100401e00c1007d01700260046e41d403076480b451403608003a8448003c0c03e00d040b030703900c1341e0230f52182900c14070088054007445200240603801c01221003184d8030503480464100c0303203401a40c441ca00c0c034145500d400d0582054150910100402c4100600014140c000c140a2020394070110381da080110740e410100c408120000b000410419405894103041e03a160180c070340150f4400841c1d82110624050380200320036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 915481375 1250 915480125 915480143
    0xf0c19050c0105030f0103020d020f0418051c091203020307050706090603050a1e09020d12090e09010501080c04021602090f01180b1e011803030306180c090506091804 73
    0x4004040001c11555503081c24442d0840c81d011901c10f550103c1480064003e00540d03a00c0011076498403062190442c0040c010000c0c00480029401c6401d800007084410b845211094031140d588110f074041c0f0148107541302040b050402c044289120034000e0101c0941c8024042c400002c3c4007032040002604507644c800c1160b030700e0801e008083d105c0c042c0105281900e0008540d12070781041c00303158200140d0719004134850300e0510124503030010420026110785008146a010641e000d14200200d410717509940010b9203031041c0d030b9400c0351030070710480c0e040c1d40c44406d0150b09030809402800140c0902e20702584400c40340e070007081c00d2107800c8941da6031008540006008070780c1441c1d1840c11042a07400c2c10041400103c02149035122000c5500d520041c0e5840c0310f10716684204242000043e11000d1028002e55078640600a0441d80c00380402180c02d030460742c00d030300720341e881010004955561080d49192400c800c0c05a103030301218107680c00211080e40384072003010ba2800380340994450207001e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 915482625 1250 915481375 915481423
    0xc0b0c01023a1505030105100303020d08150906210c01020706090b041e080a0f02040c140d0e01111c0c0206040b0103060209032b140306060f0f0c 64
    0x1040100c1c8a00c0886001c50b03410382d20107180724400c0085501c01400290001d07100c10760043e0410701c05a0b981c8410b07030540c00c01080054050b00303401c442d03007243c0c420b4003241d42a020000003510341d060111154004542c44481100d42c1d49804c840d140d401c228081c00080541e803200721101d5140b03815000c01e405540c00442c0041d055681080303400c3c020002071500c143c2c180d04003090052a81309500c59581312914212542c103003c002001c0b804c00402201080f6401d40945241c00c4107000390703130300b41030b4402d03450318a40d110b62a003c3d02440c2046800349140b03505d4003441410703030001440140320240507903581e0650291401d290ba001031420010700701a50072604500c11080e415646410902000c5421030024000050728050001e815207a01c04000358403150407070301003407030400d05403e81020403602031809104c021085500c45c01ca00c207140c0d1000c00d049071001c1051160300c401e4450703640000003040720b400104070305005810700c0e5a0007600149828007081d9141d140c9003000034421050000720345c3d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 915483875 1250 915482625 915482647
    0x71e150e060907060504060c0503040806040c090615140c010608121201090204050a05100c02040204030f110d0201120209041b021e06061f0216141302070f06090c0b0c0102 75
    0x101642c40309401004140032814600014064080c0d4440c2205122040c1105000c0040a0096401401188017240c0785803074182412408151144100320440340f8044000c1071550071041c090340240000d803503200f04070840c800c00d40d909138000d08160745103560380c0b1408210010280710709544081e80d68205910740c2002c500b202200171040e8414000c0610402c001c1000b074586403890002c8800031901c1a25581e07103a541951030780600e55000b1741c06440003401004000c1000d100580c07e0f0b00440c11100d00b0301c40401030245e903420104000e40440c42207403810040703040540062110110262012070b89a00180745e0000f0581a44401009030304071424501e450304210010031414055031005040301d05284002c14404075141c610b142c0da800000d00540c081d24000c000c144851800d801400400301e546200c4400b62002d40b420080c4a0b54400104412500b007500070b5403112500a4041051941c20740d481070f0081009090498012081c1480080e00100701d8000d0709201101c1000940e0718614540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 915485125 1250 915483875 915483883
    0x90512040911090d03051c11040906140f04020903010e2a03071401030507090b0d0b040b0d150b030a02030d030b012d11160f0920071e150e 61
    0x1e0b00c0750040c00600c90180300ea640e400950030481d4142c00c103155151030701e4550460610507582880d090754180780700e12842c0303c040c9000f0001ca03494414200992916040703015444c03030300c00d039400740e00c03071031603400c42400b1b03e40740d402041c41c698014000907500e84640903082c00e1907190403d22242400030800c0309a43d07210110003c19000045000e401070b1400c145d0306e84080301c030300c01c8403504060b81c401c0010080c0c1d0050f0f05141c0075000b030428140c5c6a42480c3d0841d8003030b03d18a8007080c00740381031850b10012400c14807040d41c0c6140d4031060410744200e003000c840d00140036110382140e140c4904400c400251b00c3c01d000108900c45190b40106070307029040005040006070080d400c8071102d4810f81004044900b50820307a13082002d140080300702042d4030649203031120319030100071100d24800c1c00154940003103420000701d8010718410300c0039031002d000d038068050400030860355100f420480c49000941d004034000d244511048614040030b03198481c03901881402d4440c00d940f03a9141ea259003e160108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 915486375 1250 915485125 915485141
    0x705041407020a0f020109030605091f060b1b07030803010e1005010503060f011805092406031b07080403080f04060818030d0c020a0b04210e03120703030905120409 72
    0x4403036580c00e400c100303000035a590f0184501030f240451304403103030013160f2288424000454200c442031003241400e60320640c035060058100142d056106d507003e0120705003401941c003101c00c079204170303401c200d042e42c50300003034a680201c620b001d8043c20801100044269000d98042d08055400031114034020f90003980b13001660308950f0502c1414010080c0954a618040c02c00410a10b00320b00b204403400807070f00200b80780741c2086a11024042c1080940b0051140001c0c1012400c1d40d10401a9800070030b1145030320040c0d03008034a040100040d180c440c0b41c0d01c00140400313842810158542681c135110800580c10848019400c0b120000381005050f600000007500203c01801d80c00720115800161031782e078440c116031032035100c0e00c070301015080038020300030031641c42d8000d240e079481840e092410304441000c10b4083d0a41034488919003500710b01c02c00707109001c40d50281c000c1c01c000003802a00e00c41ea410080d000c03810107031122000f100054050000807420a002c0702400d840350f04141c01c08069031000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 915487625 1250 915486375 915486401
    0x8030c09030d0e090106030b03010e011a2b020111030c030d02040f051009030204110903011b1107081519090f0c0b090d1502070b0403020606031e03030a0527070504 72
    0x442020180f65580402e44d81110860300340042c805001c100800d014002229440400754682803500502001c02141c1111002e0103c5038070343c8400070580621181071662800024035a51822103900550042040d00d841383c42d4601128100102030503132a1440d4008210503080310340109040255540c4504204050001281d80c1c00d11a2041d260051440700c1900c0003030310403501e490303103809011000d000300ea44407540a0000d0281c900d2007201f8203040074a912010300010385910500c4039201c40881e460082d61711210141006807482005001660f001401c034100000d02122044035046540c41000344440c0b1030481c0c0c40b068240c2d4203145420184652000c41c4401d4200700c010110f64542001402cec2c51782c449186500b1509084184009015008000b41000d00510611040c1500040c0080c03091900300d08440011064490241f0400003001c10303d01298010703c0441d00c0c04407150029603002d25090641d10705c500c6010038800001900d140b52501c130307800051080c0103a08007802800820640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 915488875 1250 915487625 915487637
    0x160f08150f150a050a0f150e010f0e030106051324261608030c01050133110d03060503010f0e0d0f0c17030105041401052b08030c09030d 60
    0x104800380d04070820002c2421a00341d50203490300c0402d07981c0802d204040c00002d0702c000200c986036035059549000703500030381210180002c05100424403903000c0d034580d0391040e5681c0010003808013081c5c485180d42d05507540e05540fa90b001043c2034641800071032800c0000c01c0d010503a0f5640071000d80f000c0c1d001d00c01e2010380107505c980522103611200c0610710b03150026064400d01c604481d07402c030705252220746200f0200e200c008001035902c4001020b441d0701030102d002045580d907101108188c800550012846c004500c0c0c100310312010618071400000c0f415420841d400d42c40c0c1920f6130341003010200c2c0300300110b903035103009000178182485241030943c1c01d9441006140302c251000d603036400e10000c5c88020450f108c070340c01180030b211311035078000d140c1d01060080e8455519500501250000d0181d540030340d18040044400741c18014410f8100c0307602920000540071540168aa00c40f0100a040c00c60392030700703000c0c90020f98504011449490003a65036070b110201c01d0201403d24031100c03242010004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 915490125 1250 915488875 915488881
    0xc071a01080d050717030c09030d05090f04051e09010518061b0c0304030606090203160c0f060f090f050c01090608162a050a11060408030714160f0815 66
    0x10000344000b2004103820070b01e40702c44141c034142492403c1d55002040300340010007448603100d49980541740c031480841c01c0d034110317600200080703615010721052141d2040000100c807003941000d5022607000b01c04003000303009800c074141006002300026039018200ba07540d207040240544d40110500100302440d8064100c3c1e040905414880701039117042d10380c0784040024650344010302041160b006503400340044c840160f0328030080009410443d0344440040610045429607841303100400d980c0c9521012014a9481070b840300d01c0140b02c1e40c45003425160b9110300c450042440e2850082005104100401c903200f6250001000e200150344035000f4450b001701408031400f404292291090303070b186071041031541510140380580c5206014002c050424800c079205104003c84c8000143e4051070440d86110f00603010b10a941c4114861f038029030f0400d12960300022840c0c9a0044007251003c115503510100100075070001203035038014000340c20320700c504200419040c040b6205240d070161000d0b0440c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 915491375 1250 915490125 915490139
    0xb040b0a0510030f02040e150709030308010906050d030e13090f12170a0b03030d0c080f0c130306050a0212070807020f06040f0809130501090903030b09040503120c120c071a01 77
    0x203002003c0c000e1003152103036801f107425a020000130b0900c5060089000c40c60400101c050400c0c5e107580001d40000e0200c100220702c082d0303e406000100c65014140c5080b0040300d48040b00d404100034481580982c000c030060b200405180600213055015140b00300c4035951502d4040700d0381000a0f800418007044000012045500750002d940c440e0303c08801003004042500040c5c110300c1440001030741c5030300d070555007002154450b9800d4801c1c11000c882c1029030b04d5a030f81170400390048407081d8001d551032110030f100080c05a007180d50004030846025003814104100d1080c3c00c842226144001035003442088402c6504100c0340502441c0d41e8041c100c80d09250b16400d4140d05000c1014040040c0052415056155003007e051001a840000c201c0707075031210000b9001e04130f40707201a0006810081085c50714600b1500850185074464000d40c40c01c1c2031b02e0718900ca40704006001442c0c0318414003069124070960901203100f071044800e9240c0e2181d061400d5200b107540860030350880009403005101031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 915492625 1250 915491375 915491393
    0x28090c090e070c0f060501090507080907140d0206180a090b13020a0e040f06140303120609060d0f060902011202070c0504021305030f06040c081203060114070b040b0a051003 76
    0x10310706a45441200e03950708801503680100c5504010b200039525510741041c08120383c02681602c4c0c0511050005071075601c0121080e010a5620031030540000c1c908005a01c801850b40b12180e10207049051100607540014056401090890801034502481d945451600454040c06820b607484c080280b056920003041200c03c091a10345d040c5580010905c1c800c078003482c41c010348900002c10074001344c42d100a01801030320b641d100d0320100d620030703c5072035540b450040706803132071507141143c151210b0b07860b8401c03c10505000f400c0e25030882e130f12100c100c2c04141c0e00741c1000c0115004500c00307d41c80d5203500c001010080c04600c542c40c407520600c135403070006140800c14001c88400702c80c090784130b81e0028000e00858046500050b4580b0407044010000703000401c2d4144036034001e21591419540d00c01d5403941ba10342c4811a21407072813041000411781d40c021030142040400070245241481d409a450410680c4140c8064420040007020041c4402e1280a0103502c03055558416610b80d2841d9540e40390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 915493875 1250 915492625 915492629
    0x150603010305031c1103100512030f09100c02030a05032a03071502040f080105181504031b12110d05040501090e0c0c0d110606090103020609130b28090c09 68
    0x803070880304040040e24142c2059202c040c1035904946d917400e0015240d0150030403440b500b80240c0124058441260011040e2041050401509480e00303158908004003006003102410610090454030030250300e00704a42e031420303407055000f5a517507000c800e01004102091560021006091510b02c50760702804030648004560103541c000380c070318400b5145400b900880d0814100703d803c0600000780c0300c8054201c28052064030070f45841c600c60854002d6206ca100f50b00010440ca0030304046000a40f180d00c3c0c030201040703441c01440203203140740ea461051450030102640080c0b001c42d035441d6041400d2007448003008050a003c1d191900d424000b07410b0781c1d0741d845440042065980002e4032044001e0449142c00762000544040540400300500401700c10a01c08810f4070a500c0011002d003000003455040e00d40042007030781004100da08101c8201800900002003e07150b48054045407520b80d00d502c040003840c511084154580401c024072a100f650010308458205010301025541003000c00b82 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 915495125 1250 915493875 915493897
    0xa060317180d082215050a0305060a0b0702010804060906020406032a12203103110d02040e0601080f10060510030207020a0e041b150f110f070b0315060301030503 71
    0x651031184d80503a05088055031100310080740304440003428a6105005003511407040d1000c101a8a0320000d01010504500402c0b00100c4204a0701e400345d070042d007000b94000e01c0342101094840440ea500020ba81095100ea40481d4484a0008545250003c4820714a0700300c0128600da45024600614130386070700390303000d12650359211000001184081e81030310f00c24002980d143d860182c10050244c100b81d1000f42a1840345843c0c001143c845d916050000322500060074211850440b1f00b003145081c1751403070882e0311581e0390141001c0d2481c1801054000c01220b80980b05640440300d0183c03c0c03d00b181825608103203050414421a690310700c4007403c5403030514006031203080f5440818501a1550418801c1d0414982003000308007102000d8922802403500c80f181e06c41c0d4400c1c229594220990007200411600d208121802d48a00c00f5504911032200480b000c003075825008034106107590700241c240e114004100525a0300c80c0c40c55005001d0103450240c81c44d031454403040d8480c041c0d110050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 915496375 1250 915495125 915495157
    0x506120a0b100e0408040e090f03030c090f09130b0a02071a070c15020913020306030c0f0f060c0a02041d120a17011205060a11070b0a060317180d08 65
    0x2022120030a82c400082e100d0303861036076040d04160400c003603d504240f195112650501c000903841e0400490341e11501c00400e40150305540720403d00225030741102c044290492482c070b0034808075503103a000b224003800305980f480c0807812036810304180b0050b0003003101c03c01500411090700042d00001800c0040c0140b42421140750710796504c1240c0c03840510b5000b174021400f000e200c00d24185194020a82c1400c01c40d681038007069a0103014007030380070850320198150004404074095051094900300080e0b40145082803140b0400001542c071340240448103403d900070032102086003098400d4010300310b402069801b442141c1c00340c180e600c641500c04542e22200115076196010b005218440810100a02100c00303503131500042417034005586c0c0c095803503104290100d6510750442c466080500d40e03102c03285103410b0304c60321982e07400340340502030b003203516501d03140040480c61020045400e0711010b481c80c0c7ea2440d0b8a11402405660700c0e0300c007031154085946240c00110314608440700014036400d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 915497625 1250 915496375 915496381
    0x60d0b061201060320150f0702010903050d0306051306080319020a17090108070e1509360a061202040e010b181b0c0d0c1e0c030201030506120a0b 64
    0x4512007841000e00e04a296003021404020001500281280204004003d510054080081008401203110792005006040200303d0110003018010544a80181400d0007480d07a02c0e0742e01783c41e040b514241000066610042400249000850803e41510280c03090000d6410940102c1e268418000e03114219086a100818241d000f80481c100058004451801904002038491701e0369000189440c0019241c000040116005103a42e500b510300142810845400380c4408100d10f6124030400c50348440c1c1030f2032401900c61120030f0404124940c11802007110b200d0405803102a01c0502100c644034100030781404210007034020301615035011100071405800e1005940d004050707040c04980c100c0740c1c43c80c88103201c0c3d81009800380105241546880070444441c000c0103940250742000f441a0400c0d5018803a0502c03521403024014080c15103000348030703030380e200040170003462120854403083d8200c4100150368052180f5075020b6000d03500744002600080350292148c515500052282d0400e0b008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 915498875 1250 915497625 915497629
    0x605030703081602210a15140f09150c0406020c0a031707060902060c0105060a05332a0d08011212022103010f0b040f0306020c01150314060a0203060d0b06 68
    0x1d050480c039905d0280aa1350350500796143c50303a00100343c9281c485140c405003800a2441f4500410450891503980e544a03540040d003030500c040c21020052161403610389400b101174001074000c0350882815541c4034907080000c2d0030108070b03070300c036512802d8007810810206041c078800480c2000200c0015580f070789586040c2c2d0051269640103500300c040401c101d94410384c1540314030f00601d0105d50b01b050703041d81d0301c08001c1155229070a003144210b0540d40c42d101c10424800c4450040a08980b603403e20030907540c0c3c46882503944a41040b04c038101641003e9242052007003002c2e0819a243c108619030400c04291010000940000c0c0038a00c2200710407443d51090001c032120200c1c3e2541b2101034420300e6054202600280910187d01c1161200066000800000c440440e9000c0b49a949010725603101d0600941047c002c15072a075491340d105e01d0f1130340c98111140b40030750f12480002a18141c40c0c6002443c0010040900b24110710405c24010155144084030b8080e03035000504a103180d803a580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 915500125 1250 915498875 915498889
    0x1706070f0e01091a0706050f0c0405060304060b150a0f05031b09010306030c0f080c030a031704052107060507031109040209130f0221151c020d06020405040605030703081602 76
    0x120000c3c5542c810b0700c50158a80c0c92074010001c05c0d0046d4070501198940c014075901d9100140c40c0b000304000c0c200700030010380c203005019561060040d140001d006062030b02041e001242113110032910480018810031460300a40943c0c25440c580c58840e0552034030703428046c1303044485404049171500101d0301000720781c0b294000c130300550b502440303034100c40f81c0d40c012407400d0f40614020210179018580700d58005050020b0352102994050741c030b141c00d200041c00b021303210010160040d506400344910580542840005400d145108280740a6403003003141441c20031207201500c008c2c105030070f200e0074041000000c1c040d01e002c114106c47c0141ea61444000003280b440c40703a04003410542c1049034620311944594041d00b48044440e0f880c2550840c2c03540c1e5000850412602035460030941094089a41404507040c22403c41200d8561081c07409500028a40501c41204841c03080c1c0006080c059410070340102c00040200794001c1050b0303411941c03040502e02440b603c002284144807000b200b5582c90f41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 915501375 1250 915500125 915500129
    0xc06040837020d1403011e080f2b170a060e04051b01080708010e04170712021b09190209060d02030121050307030c17040f1706070f0e0109 61
    0x5641c1074a8088101c80507801c100001800e2400342c0564011503862a010740c0210b980119032a0b010b9203180e003000301103010100e83e031420713030030b252828580440c86680421480301c0c4048404010009440840520740c140815400c80d0b0700b60f40780c0102c880400070342100300d280d140358518010700040d0f924040c4000c0108210f9000c25500d4555000307010074000003048903208080b02c5002c1c140b04889401c0190ba03100000e98841c00021160001080b40620ba204403035001480748000001c16900e010f8103a00507081194295103070108414980c450b50b40400c0550340d03a40070304070010683d501c402c00003040460b0083c400d10000300c0c0031102c40c02328030341e641c101c414505005101e01d40325442d500e120740c025002401042e2940450107007036942c0350b0b201c0c4c1c05842c000e94000000c0d498000c1c207030382c201c40e41b80200c58100c9140c1c0c9051803540203155210080c1c8043c06151000c580f4007031802201c007011400000c48014a904148288031001c0d900800c5c4102c2407205051040090000500481d00250b0030303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 915502625 1250 915501375 915501427
    0x4060f03050a1b080103050f01050f0c090a051302130e01060507080702240322120509041d030c01060b31030818030c010e22060503010608031e0c060408 67
    0x4901e4918001e0740041d0304d43e0580303000303400300c405a400c070000c0c1c14201c0d8410b030389421540c0c08450000c0c42150701c0309d001300424100036107400b10150741da0011601d4000d04030a0515030b00d40119007500c001c211040d00b0300042a5218241a4a51416001900c280710385107025000d518002814829911448001e81e00300840c1040076002964081400000d07800583d07004005203031520000b104c410808606500c003c0d04101c007000000c1d2480026142a80303e500507a40242d02c55406030080b00900c0040c0b03004c1001e240c099981c9010440000c1d0848440f600002e181e40400d011440d038038000c00201d080c400580503904080c4a500c980080c2044066904c02400c050700052100f0024618403c8400354280c158101c0e100f0b034010100640303041c00400e5409400c4040e079800140360760701c0442d0048510b0b95003400050413389a03000300342929519000001182e1000917100a084402d00c03510035111112840c26080c4a420034601c1d446100280005d440c4400c0401d410f0001145041a03142031254 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 915503875 1250 915502625 915502661
    0x804120c11030d020303040309060206090d0c05010b130b01030e160e1003060905010c09050315041209030213050103030212031905040602270a050102010c211d0a0b0c04060f03050a 79
    0x3071000b940e07031b4411101100000e0154400040aa00016a45000f840c0e0030024000011001a0888004070141ca040e1003e640b070320320800b010f840d104140c002c201181540418004900000903050b260b9040c00300240b07a0000f05090300c2030001983d0b50043d030307000c04131080858444981c4083c040407281c102500103443c024402041000560080c841603040703443d402c0d00c19aa6204054480e000c2581c1603405c60034003c0010001407038402d0160769800c56040c0803100e10f4680d004280280d0500e4040184a40d48000602c2450b404018045890404100091840c030b07000a0a01d296201800c240045944503004901007001036016205641405415040d00e102d00c1d00c40d80034101568404540078107166980800c42d94418080e110100042d0340342c2509800000c480e60b441c0c194480d070b41726046c942e5518141c21034014144145504900300004041950b014104409141c001030302c0355901c000e040208016150308880c0300da21404090170f001a0560750407000c1f40c003415a41f61041c2d01e140c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 915505125 1250 915503875 915503893
    0x501020703082d030f10050117041407030302031b0a0507170724080c03060a2c0408130b040e010b0a090e100603050604090b04080703090918120804120c1103 69
    0xf0410245101d8843c95400b4455902e440007145050301d05400703460b00040c4c42001301c1e041e40c800e5041e4545c1242c80703056203641000c08208000d04101181d041100140c000280c04405513142c82c0c90203680000c940007a104200160303030340075961070300c9104044200f4144403000c051940d0600c0b202000b00024014465249404448500c0e40310b1400048000326a280020600c07411052003074922a03080506000c1500b0708011082c091500f60520010480004015019103d00900c5a6134016407044a04544801030704c400d504000c01d00b0b4106040d03212040c80200640c46078025140c1c11210402c070480d0751500e076803101b155064030070b802c840c6445851406205000c05842420f0084070314076641000345854090420056840c0329901a000c82d02803004100818683c20045c20755a110707061041c030b49661001070b04241c4004020480b003400f0b2511079103060051031011035020b00307500c0c98080302a180a69802075415541020001045030600c10b81c4200240d507520302d0301c804401001c50395144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 915506375 1250 915505125 915505207
    0xf0d06020c01050106270302150f0f0d06060207080610060807110706080a0b0d1a09101415030604151113290703090b0a03091e1407050102070308 64
    0x504841d401c101b0b03c0b028400710707120340c1080d68181c0c2d065907170041000400352448035805d1700c4d50b002545010303c0b07072400b003250404110201c00181100a0041070101c2c0b00d83c900b50010b42820515400150f00f608120204505a40d46507172080541709a81000704085d241c806049800c00c41403400800c80f8840c10001040c1103821851241c406d0030340c4070b01882541d40100510a01014044c001020501c21802894448075440030140c3d00c00e0b80b080071580d0b07540e2810940c42c15280083c80d01341a0f400392401780503803840c6000c1115407440c800d500801c01801e141d17503401580c003105042d032550790303950320808640e481d80030040700e4800d02e010903030b90a000e849a01e810143d14dd402c0301060100b80c8264040d52402d10102505c4802e17805489030000c0b01d03d400f007090020b9001c04003410030141d90307007070100000d500f01090100d00219003c01d00600b800074a440071000700d83c0b061460003135011090401c0180c2e0f000030035109a030ba10440054a5003900c642d00c548128210241280a500c4484004d001c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 915507625 1250 915506375 915506387
    0x1807080604181e0b07110c040b30070918110109080307030206011509050d06050c0706020406020c100e0a180212010602060415110919030c1e140f0d06020c01050106 72
    0x814043c0c1c0704c03031080c0c1e01d03190f5007982c0e58040740751961481e400c00c6440c00d0040c07034a03a1043d5034901740a480b032040fa103262103558885603141c4c0d10a9060481507013008044036010807820b0044e02130120104980010a01b00f40c20040c0c0e1100e00900600a105a1641513445034550400800100e01280d403120603616010b501d40409014214086048000d0300c0d0120b481009642d04652010f0a80d108215142d1030342c001900c0010700005a849080203e100001c029100510042c1025406841c3c580305502c10017450b910f02003442c80030000080150306a940e0341d141014201c4240c150b180b060ba8091120000182c029400750b1101c80402400018005801080441c070607803140e400101c0b45e80b005110881202d10b80c0b464034526580c00c0c4034a100c10f04054201100603100100d096808541d603a844091401203600001c00d00c142c5481060044a182501c1d00060900c0e17900c1c0f0142c81425102103052030072808070b400d11512071815541c0912400354110388407040c036840240125a110030000c0c0030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 915508875 1250 915507625 915507683
    0x405060a03060213061706060714030717090306181c11070906050a08032a0c13200408061f0f0321020c0f060d020d1a180708060418 58
    0xc0f508002c01d03055070411b8441d4603841030100030145030410702e940d2a40a4800d400118038100b46c40f0130032100000c00d102c4000d007071400c0c00322541b09688804170410302d41400c80c0079000110030030008103403180d03c500101e81d000b0b10910b00500406100000740d0100c4000c1014a0301c048180204100071451070040d030401410380b01d0646204064603640c501c0326640788944c44604400c184144011140700d40a8883c0e0850a0703209011122031001880010b1600d0551000398804079039a240a655440c2d004210502008000110181014507020586860b00402403090b4005100101c4200c100203001341100080c024140109107a141c40c1d1034825820b0038010241b4104100c00520b42c03a12620010b05c111072403201030b06590303c916440080c41007981040d07601c064034540910819911035031a210b4161845da0655950161a60310000d200780c403110b106000c43c222202208100e07645401109903900840e05807000502d5404020540d080d0380b80c6900c0041204a0050a00030030300398084e12144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 915510125 1250 915508875 915508877
    0x606040f1d0903160b1b030f0105030d0c0c03060c141615020424020f031614031e0313021005030405010e010c17101a0c06010501090f050405060a0306021306 69
    0x31868072140c4040e640c0740a041342c4110138120341c84c4000c00090300c100105400c02c10341d0102e105921040d25003503070550001c4820701650b5140310010041031604000c80340b41d040c16403c142c0e4a03440c041d100d00f0220045400301030324490316101c04885052040c1c0403040042051450240c5440000c0d42c9011342c00d0300c1c03100c02d890314405282c205052160368805c841c22030f155a042c0da4107032101c1c003c00e05010340f02042c82100390700600c4901e4040031400e100a15030010300c42c112060107900340c40c0c0b80d1286402101d40c540c280e4014825042e150f0072045808810b2105007400e203483c0e03031310b1250380c440c505890700000b07402c0103a4260303035000f0035084400ba50065109800034010401c1c4c5440f41402c035240b101320321002586962800c0b4a66a000c5852500001840c2489a0441d10340c5400c0b460b41e04400032640c9080700c001011040c0010511103e409400301340b8045079003e02d052a00c4035121150300070584103660341c0c0040f0303050341d540514490085600c40000e6448292440503118842c060b0300c5000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 915511375 1250 915510125 915510179
    0x1804090f0302010f14070c0f15060330050d0b060a0914090906070c11040e0303060108150907120b030d03020c0c03011103070e0a0b0d091101020f150606040f 69
    0x8520a1a5005944001c43c0502c1d038601d85035202441125111f40610b03094070403442950b400c1000c0349080f00440c6014a045401186ca14918540001514001502424090360725981c0003404007102c4034080a1603076510b025500c40b0101c22401d80244110000c00340d10900c00611072807401d0700040341800300c50205030100b00904402042c0400d00c20215151011a0030100004843c24014501c2c0c0d411640103900d0900421107020204040310710714191440541d02c04010040150b1780404400e52001c1e543d0b911450b000740903000b150703015601074061030601c91407202980d9485619031040f010b02c90300404440c40700443c003401500940c841e4013181294003804809896030301b01400307260807401c000783c59281f856071441030866910102803c200da0180c03240e10300050501e40300300070709060300b4503480c00100d20503246490130317130086510343d0203065402c1240052500320010549081102c0100b0256190ba607552001030701074861a0090700784c44640c603001050803000142d403806442d2943c4500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 915512625 1250 915511375 915511391
    0xa1512061b0f090632070203060603150103030c14100609111e0705070e04060b100f05120a0e030d0e0601080102071e03051b030304110609151804090f030201 69
    0x12607001030400342c10404905401c00801c4840d01c91941d814031011900c035541800080652884001c09001038030790008503021440c6425442c00b0b000094001504070001c01c0700011040086075104414400502401181a1541c0520150701c0f003000040c2d010038195412120511502002032506004100340d1a10303059002022166480880b07200e4001502c200c40c0d206c150710010318031350780210300071140e0f409105400140140e600404034011445044082101c0141300b06004540c031209080401304402c503c00d1032070082d0014200e401d0140a01c100701856a210010507015150302100c0c0c80c4075200c0011001e400245a0b4050b240a1481034103964182e6a6542424280c2c040e074203000d8130810301c2000e9040720002692400b80a1803282c1481401c002c910030f0044880000d090715100707640c000008110402c580e42e0000c1980c000c04070b607003030308189074000800c03040c0491039004035422900040220380035024044000d24244002d00c1488001003510300708210411040303045003d0b40c02c040c88 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 915513875 1250 915512625 915512627
    0x606041b230a08090c0301330801230c0a050a0c0302010e0f070303030501240f02150705090310050705030a0c110a03030905060a0203071211070b0c032d0a1512061b 72
    0x45408c03198039942c0d02601c04058805200002484502c40c24404024080000b1114004c0c000c0d50341f240400001d03040b21203c504d41c806a001001003e0082d02c0b181080341c06600340c3c10100fa501d414019280c5040140c03298a000d0b4018030141018801ca44a0505031090b210000103d10307040e030b0300c40c2e5024040359903a80038056080000c2c112100900035141200340400c0c0c4142000401c3c04400c0c4101e45000c120000ca603448041e040e2540c0c13001440c0040c1c0d141950404200c5d040f540072010404104524181c18001d1250001510310904562500c6c1e0f4a540c4900c980110b019450105042e101810b0b8103160203002046568000c5825024180000e0b524103494401e40e03210b00f44039180d0701160562110640001c008411081f00c584805200c4940401c12002d02507109001d20301410b81e59040032080d4003100f4400485a01400d000560403074002100d1941c441e07000301c07011001007038040417000c48022401c00340d00480100c05e180e02441003808080d4110706a80990326052134241802040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 915515125 1250 915513875 915513881
    0x207080c010e010e161a0304212604030215090102090a08010203060f1e21240108010204120615030516030b15061206042405030606041b230a08090c0301 67
    0x3181101c111051101c020f504e40c621b400070365025115120307807903440c680155001520701c584402040001c4010041c011408410320035224218a0601d07a00644e24055500035614056104072030050500e990100f000000250152000014002e017000719140d15803442c50700030340084036114030401c441490002c050508040c00c03280c0e103810b80c0010203215070400070300c0071040d0202c58480716919924481d4201800a000550002500d520035542110818081020000b0180c1016100e644100010000e54142c1c8101c00e8200c2d51200d404607000c0d0440070b4242c41104c2070703030003e0841d0040c20f007800300e41540c407501b840540c2c0c0305031184d0000340c50700303091042d841002c4024150064020481000300780b4540030080d82c054002000410300c20302c0b03100c94040c0b9048900c12903104030b10095040c0714074a018098150f00c0747c8165400c200104000681c00034048241c0030090374030641c1e052030701c21008a22407007880c00c01540c5000da680d00000000404401080703841d03144a000b0740d05214810b18042c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 915516375 1250 915515125 915515129
    0x405040c030506130c090e0c0714030702121c260f0412030b060f07170a12051f050907030603021e12010e0705010e0102070807030b0f0c04030201080a0207080c010e010e16 75
    0x55100d1286e1400d11184a9008001909114003036405020704000189690342c1c0a8040d00844043d680382d444910610280c02079950040310150441d08550300b0b511081c00c7c2014203200307117151010290b12070030600c000c0003001c0b140404424001c3c02c1004901c0001d984003a00803481401c3c0c3c01e40f00a5140021003c588154400b03560040042200807150aa448060310285014168000c240f000b050200f04880c4c0c8001142c00108801400d00305000d600c130710030390340c1c000c04c00300700807421150400204804041c14081e26118103424008a060188658032100140d80d02500c28082c001260949010046000081078400ca541480c0d0b40000300b0107000301d2100c1c81003c030040241d90304010040d26a018a4140281144900d14001500003003c104041c0154003881102c809810904484030507030100400c031640300d5030200010001030340e0000000d540301446110041c1c940c0703030610f0043ca051042080d000019805c0c0b200c5072407007900641c000154907010345c1c01c492242c40b540321403a140f40c10038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 915517625 1250 915516375 915516377
    0xc1e10020c0703081803100e01200912160f09060602011503060f0b04050a0b01020111040303090905071e09090b0409150506150a0806101d10050405040c030506130c 72
    0x2c1c800308005a142e20242040c0c1c07000205042008589601082c50041c85420f00c180c0d86840d8035030701164000070301c903903519200c0c850104c8100c180c0d0300049002c24807132013099502900c0e0211200e95484c0c0103101000000c00d040c103413072240503541c0081c244c2c0030007503000ea801094504100051040e00501c18949002c80000342504102d1660311060003c101c101000107440c1d40341c1407282031569035403007028420445c15000103507150154000908503000119040c1c40743c04200710070700c082500701c407255084803003064000c10311381e07030700b1300204d8050f021a0b5019141d8109440004c003840c1c0c110f0401000e1300c45880f41000850f02480410040d12038000c00900038420140e0150686030301034120300c0e4041d6001d003801505581219044450b94000c080310350020301c2010510005190406030b45800c0030f610700d065010541110200b0166401c5c0c00d26851207060142200905580038009444c0240401802001074401e59400074000c0c1c0400c4075421302c211500318001880e0845446820350413001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 915518875 1250 915517625 915517633
    0x5280311150325180e0a1103010e0a0c030b0a0e04171e0717040e0703060801140a1a0402040f09050115020d0819020d1407080411150c1e10020c 63
    0x180708000040441140507403081000c0d000324502c0190340e6200610042600440c201794902d404055032044501e402d50500108000304010046110600180c03501320140302e40026004e00708450a400501c1500c089075004180c1917400103480d562048124451805401c2c00702022520040038180c0b48030309803502d0b50403424154040b205000400291440c04e11901072001c0c4007401d11004a03081e0040e50001b00410205001c0050b03951f41400fa91004004040003032018416003c0d0701c104206004201001e07283d9100c2841d05407c1e2802c026040001005e4000c540d11622003c01c840140d00d81d000300c624040c1000c4c00014401d030a050b020341a14280d60140c03a2041000385d003100c0d020000b44c164030031340d4100c3c00040c40b00c8c034040c4000d01e01c4090300d1800190340d130681c011750a01d600b40140701c00c0134003e840b010072010030b0910b10345940c0c1203c200c4007052521070b0919280b07842e000b07030401c0380f0b4a8400c030003d110b24168055090812013260b1070441307490003210308000040c0e00c254001c145040d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 915520125 1250 915518875 915518911
    0xb070314040302101a03010f1b08071202071a0c04151806030e0f0709022718130b010306090c0b071709011209050c090c0c07052803111503 61
    0x58982c0c058902005c0150030301400f0031150b4006800e40d26140c995440c04c554940020b007400900c4031448507481081c1c10001e0052601500c01341080c0b0302100c4600b089500001ca50301080b02c1012640c280d44c200c2e00610045040c1a450720040d5006401442400150070495075080c500403070f070084007541c151140b1903000e410054110081c0c1818980842c0368460410401d48c20207040c4070b4240544029100162540f04006400070341c0a1104050b05c40e09040b416030341c80a0300c031040707101c0002103a01c0c60360090313483c0c5490000030844204000b90941110000100411a05801441c1d9090080060510b041d846024a9020340305011008102d1000c07007d800481d2060304c0090900c0d00c105040000411303062902583c19110712220885d110380064074003140501c0e1181c01107070000b201019440c140000d03246c60030b544d03011078000c0d1032003270038101d001c000840c041280c0000004500d00600c0c0300260f0702e140c4cc40d800b01c10a0500792082c1c01e86600d20350240000030030b0768450340c00340d8200041d0076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 915521375 1250 915520125 915520153
    0x807020f0a1511010b010e011b051207050609010c0e0d0b0709121a012c15060c030415020a0201080105090a151205010e0a02010f05180406030b070314040302 69
    0x914000c10964200d00c0356035000030900c00500e840a40e0001c16100d00b50314031110702c0c01a085900d000c0030507040c0140c4020015441e640024504269400c01503c03403444100f5083c043e103403d00c01c0440492034a0009004810044041021360103460510002d10030340d15000c0d01a201d01a1005c4000e4000000c031a104010902a020042d044000390030720400c41902c510449801a04580d000e80d8400030030180845181220340300c4034010203400302491201c0a41c4038280c0400d9401c44207000e211160303900405c4405409042ca070401144c0104415603683e0306900c03058480d04940300764140c480444290600d21800812940303a0594140c1d900c1c0c0c40340c4c1c00d003c100074034013801a0a8510495890031420f49080c00c0c060840d0140200d904091003a101c1d41c0740c10307402d66082c3d404001464020880d0100180d810046040c0b1628540c1801c7d501c9150540e80e400c403c180384070260341d0041c204103001040c816001a00c501904503030340c00b0302c40010580441a000780055800400682c84140c241c4004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 915522625 1250 915521375 915521389
    0x604021f0903081b061b040b09060f0a090302032103130305190207050a0f150818100b0a171b040209090907080d0216060c0c08010f05040b01060903080702 68
    0x660424081c00c50701c9448582054010082d9034039100308000c500b48000a00700a8641d208170440034024080c14110055480d501641c403034013000f2000811002d8070f40d5616825554010001d06003a502c41c00e0001005040c400c507807109a00a00551b0507040d0050307028888000152a642405851130320b89004034000c0100352803080e800c01130f0920600450305c061212018010019500809102d4100401c00461810725408441c0b0222011030070410744440d1a140d11070301c003203030915001d140e8481c10000c0740028100c1c0d006045000d01702403e90140029400703006881c0c001e40c1c3e030401d102d8680740a1000300140505803038440c0c0c4120b141040c1c100301d44003800c0111304040e1015085c800104041250351100f5a03c014154101a03002c3c02540010450351114000c940300030100c07026154903034510303800c00380264003c000021199500b8070140d405d91100a00c03084000700548100f42c1c103200d009102c140c1d01120111880c400000300c9510401030141942e8101045520346901e40d07080041c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 915523875 1250 915522625 915522679
    0xa090b0f0405042c010e0a0b07020313031a0a0c0203120423061b070b1501140c03031005090106051803190302030d0f090b01090504060b04020a0906030e060402 70
    0xc103100402011405407903901031000000407254041140d80d003020904c601101d40600607084c6a813408041c2c0759050700008040c0710303603500041488020b443d4020b0803030039445120707040d41c10f440341a5800810040201410200403c1c1900110381c60b403039810181090700c80d0b49a82e400141c0c001d00c0440b500c00400e107425074100c0d00c56918025000ea003c030800c203103c20a800c0682e0700d600a00e041220780d00d604500c04400a29068456141802a0b904c0d0518080e0251078103075807003883c1c12484040d074060b80c0d00c11002c100350380c2d4540d150100703000ea55560307078030072200d01c1b00404090500141c40d0801c0d5000038140c5e1255150703a4200301102c15145000d410540074558544070f01c0414000f0400a0200411550b0195029541e0741c602e000000741500d40b10605c4800480c030b480b0711540800d0400ca645e90540d080e00402107101d450b00e0030860042e0800d444110303801880001c3c10b1401035000901ca00c102c500d552014002c582002e2062381d20f17008101c401035004500808c1c520f031816040248034034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 915525125 1250 915523875 915523897
    0x11010c0810090c0c061503051501030b04080d39090e0c09010216060801170307050601030f0302030d0606050c120c1023010306200c0a03050901020c031203040b09030a090b 75
    0xd051350407500c0303000136600e80d003c0030f044a1031b81c2441030080c00011300c501101e2070040550b0700710652440e520780b41175020060000e0107420300402c2c1d02d81c3c0c1d0403442d0440001c6914110301302c00d47c040314004503c9100301d0302c200c0303425030070b840c0c4405403900340140901402c40322545042215561f03140318129140e0310400c501811401000c3c0707948000c40410103d60301416003556900155030502e20740b56000d0031503c4100b00c01d54014030044001540018020b81542c2c0d201c40350b41418242481c040c3d2440c010340a0548005041c40004140c40d64800d0103040e03403100742e1003203034104000c14070390400324802d213040c04074150001400c808030364030140c000d03840000381c191603150600c2c90202c82d070440090a03002100d800ea16800400214222240d01040110008904a00c0c242c4c4d00340c103107556603500c0c0500406001e0081511117041e8000d0155070042c0d44040ccc16aa564190804000060b910456085607050111008102044000400d40b8035044883e04d03640006400d24084c00030039086010260 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 915526375 1250 915525125 915525137
    0x180f0803190c4206050108130f020118030602180301110c06040206090a030b2a1c0f0b06070b1621050c09060c1506010f050d0b060d0c11010c0810090c 66
    0x1140000d01c24180c010f9080f07420000790060a0000042104102810b01c013112000071900101241c90011090309082e070900341058890f80c400b03902001c9098a40c80a0b00052020078084114280c00b2501d000c42441100204104090f0b1001c4182d03902414102c503810340d00460000b03005040000c001c000342100148081e02c060755035502d10250341c10855400b411120500c0c07000c1c41c5020f00140100c0c6485141148030304003840b5038a03003030103c0c400512800b00a41c4035006209005100d03400b95003458000307010303a0303611010350030407509290007529a400103e0000d204000901d1081c803400f6451813180342c080c5500d07201d04880901620700941803110000c002c100380450345d42c0e80001400b14000c0c19002e0030340b0004414800d103409000516060500074243d904a001c168400c00700e41c442039649100050803184200440c030b8600449900a01c414a4121075a00007504034041d91700d40c1010900a1050600e000000c4504002c01e448101d900d010224041c800319016401218070001185050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 915527625 1250 915526375 915526463
    0x509030c0406230303071a040303150620060f04170d0c110d020f030901030f090b0a0605120109150b1f05180d050d180f0803190c 57
    0x8080321140c0d401010b01e00542c448441c0b070590804440300f4414021070180d0f040801c541c845600205802c040d4928840e4018005002c00d030090b131022100e165101e04c9148038940310340c405801d0038071900c2c207031500302d00a110700410740c04009416486080c1032070346030f10a5140c40d990b50300300001c900f0482400500500c84545141d5151081600e2416a5900e122070f4a2610000760b00b046950520b400840d000520300c012001700000071110442004c0c0b070001013040c0d89410b141c004050f0504010300d40404201403002088458001c01d042c3e0340b00b11458010050903140070303800c0310040400100010488807804019403941c7d8080e0315405400f8045440d601d089004040d68443d40004070340114902180803540c03001400c4002c00003072000c2d0351100c200c0300103841e40e40d5602d00510440040244d1103502150041d411101980142401c1c00c0c0300f00c4043d140c5c62050740382d1708080e017164080c0b0140ca618500c00ca02c034800c490201c503040300540c0010021300c0c0001801040345030011304800888554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 915528875 1250 915527625 915527629
    0x2f16020a0b030903180f01020604330b10051801050d0f050a14070306080a0f030504080307050a03030f02072f030a1b15050a082205030304022803030509030c 69
    0x4511900c0120003a5a0794064a90000c040d0f03003210105c14052011503103c418541d0700018000d17001038010300e100300c58101d481c064100c1464041c001c070740bd854400240101ca20015000f100380088100c03171a0303100f112140c000b103034680500c01070070710294030420220a4650107a401007840410b105404641c0e40b00041c00307542079070f009450309045a9514003010707000350205c8500d0303600046145000d0280a00d4034010070350701d00901c103010701000c4940018408050241c0111401080360109603078a070103080c10b05584410006030107038082410511898800007a038421500743c00d6000c8100184801e041c01d4503014a81c942d000307080c81c102d402ea45134400c0e9404000c07070701c001032091103400101d801c40805288000b14a0b803120803280d0f900400085c3c0103400c1410340b6219034061800049580e41c03090f8514003588071261918070745171006520014810040001c511403030081c0c8801002c1500c0340445802004910000070048004c0d410510000b80710f0700082010303200080c11140700054240c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 915530125 1250 915528875 915528877
    0x1212030a0b0402040902040803031005101403060a0e09160603150308090d1e020f2e090509040b15030d0207090c1206140a0e070503040b130b09012f16020a0b 69
    0xc6000348d54008000c00003c035108d60290009004181c40a4444808003d8058054822241019110100070001403c00e8641112400040c0020008481c060500003c0d481e01d9040701200e07100c0c0c8039481c01000c0341150081c01a400c502904040b054901403450312842210f400c504100c540c400b05211710134000c40c0e08003d01ca0f2040d2441c41c1d281032101c00300e20412951680c45440b4071300805102c4238000805000020010048624411035558800004000c6440b02c0240d046554042c4468080c00148090b01c64518030880c1c203040300d04ca00c52601c408155035142c8040c0e0307200c01079004010034411111039030031644600245d41484c0c411010168211030a4903a2030700460540d086940300440d85d0314041c11010000c100c41104c041442c141104005c101e80f04c002c101419002c000c0c00401c5158070000c01c80318642d5002400302c082070810114050103014103011400500f05006400d02030718104024001c042ea080504c802c0c03806008800c00c044d0021241001e80c0d20000341d401c00200031202034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 915531375 1250 915530125 915530129
    0xf060307022b02070602060610200a0602090a09140106030f0605041a1903110906130c0804060b01050405061b01060506070308060108131a09011b0207051212030a0b040204090204 78
    0x140b000040b40000b07800003490012107511800455100300244403280d141d00360f0002108042d0302c0c1c0a240d9100044c0e4081c02507820401c00041c43c0309100510b0180146a17014084c030800440d03800718440d6844218006640c0800500b800168829004120b20740c029031020306050182107000c00c409070760f040081c1c100d40d281101d049500c03d80240091192401200b20706110b00380c01c10151215084d515402c0c08403050b100c03007900555441001c5040d0b0354034099507200e0200c0018090254500107500107284140c1642c0c100c640d42d0920581015035030041069038180c9501030403003410f06890008054101c81d00c0a001d117001d560762100860766803608801084428040d445981284c1445d07800100750200c0240034400005140c03012000145502d001c40c0120000303a5410641d503291541d8190040001d01c410b15200c916160800000c036030003051110448204465a00b6180a40000d281c0c0b941004600000f0310001000002c117442502d900207100e848000d44014286a11060008126881a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 915532625 1250 915531375 915531433
    0x80111030105120303190e16061205010902030c0706090f080a1706060304110d02041d0a062304030c0c0305031c0f0903020c010f03020c0105130b090c0f06030702 71
    0x100500c01410040e000743e02881418005620f1403511104206811002c0c0c040785040f66104c0180d10052007080041ca0240790440641d03491940d518100a4886030010f004034841d00d0a000000411003018401c0d64880c11898450510344002070307039801c0003800c03400822540c856030075142101044c0a80090000040103495049030700d5150740c5041c01900000344082d2265108004100004480210b100300801003607409200702c80940c0b0020317014000601e60349880d8030010b50b4012040100142c803000c03003401110f0070450402081044211008080241c9800c01284000b02d000248540101031129010359040015140c0b01d0391080d00755440003004d040a030805000211300744010f8030402d4480c5514000030805000a0354019480c1e242600b1894103004070f5815141c05203020340c048444013650f1000130021303890106d0381e0340c3d040a50a0001d079003843e041e43c0080c5200000281184c01d4400040103030005210a07001c2001a510080c614000c5010b986540540380404980c8071100f0010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 915533875 1250 915532625 915532627
    0x61b040e0109022a070303050a02150a0f151a0309071a0d0c0e0d03080601090b0c1b0109080718090b16020d03061413020c030705030904050f04050c090a06080111 71
    0x4004c4130340900741070000c1c5441d10400d02480800c1213040081c81d034041b251303d03040598540c83d40c43d90582c1882440d03d00c80c0002401ca00420078403003200c1d0302c40002c14042c04001c102c8511485d019100d0303640700b03000702e00c00c0044400b02c0310450404200a9a40140c064040740c06940c1c640c1c2c08402c1c1115041c4019010305004110040c444840e40a0503861001d82e203803604494140500250340024450400381c14400703c18086140d90b44100106400781c015100071503961120241c0690740c41c1102011800d1000385144108800c0d80b2500000b8121400e64005104050800004118804100e9030240310159078842010008105510261283c92000c1c01041c4020000c48080d06040501510504140c6080c2c005e010301d07185031080c3c2100c0700c003c1da50015050100c0740c4038030080c0700e03103c0000941c3c480810b00c0005c100001009104d45841918144140e45407081a01e4078201d0031b80f8003c00e19082112494224100700c5c0020358071803040400401c0065803040b00c0e074210b0796440032054030940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 915535125 1250 915533875 915533887
    0x302040503060106080c090922050f01060b09030d110c12010c080108120a080c0f07080406121107240507030b0405130314210106050714010c02061b040e010902 70
    0x1500380102801410242040c004525291440b070402c7c2c03003503981940c0b00c0c0c0312010100c0d4014a116001c145c80c21a80e4241c10f5aa481504041c0e640740c001c449601241e40c02c0c55004546030400400b900e01c007000180c020640311350003131010342e040054001c0500f49131081144030600c0d0b90399201c03411a80034070070703000294000e424000100b1265058000182c4e50348a90440c26618094500302e6412040b07614003510661124185d54110707208a45c041168140c02203070a4081c0300b094002001101c6540d1070304205451003e00d80400c7d9482c082082482c801d0a115140101c4e003251441044040c00500c440e01034415800c3c2c0808688044d40c420000981d5401014003d050521400350441e824500d02c01103604290350051070510b15400200007030801044980e2058190392101817118510000916607685410006000340c00580060320740990540d903207180d115061007910701804440d8054081c41e90b038441c0321480d1410f50162030f518403504000c00a1700c41082d0716003038043c250070080035036500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 915536375 1250 915535125 915535129
    0x1902041e051f200712060507020c13021308030708040e13030818030c010f06090609050402030604030c020d21120207050c01180801060909031e02150403110607080601090b0a09091503020a0603020405 87
    0x80c0c00500c16400e54ac80041141096542c0722848003680030171410250307841040c0c0d140e07414400315030b5010814606c8045010b204100c0202c000c3c0c070030b90314403c282030700c641d0b00c003058402003040108014020603814400b05001c81c000c1014100761041c21812245854200040c807401c452181c0020400255143c41c1444405400e000c0c0400502c4070110078489802d09800198840c0e030007420013010302407230703282000464030341c61082130866422035812000801d0110054001e81a001c000400041c1c00f0342640c51400e029200341c64195070450000d001e0404804c0c01515100f120130f9603a071085410340f00024450000740903d901816040300049082c0c2c107640b401400160307801e100d4025264032608540c800d60740c00039410500a14070107104885807202d0800780e82040860124000900847c0c0402c603034107810000c1d4600844007030380d48000e000e6943e00c15131058012450394100040442e075081080d5070190f0405a1440088140e01135030030768035070005955212540c0500b002c6500410100614 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 915537625 1250 915536375 915536381
    0x260d090605101a0c1905070602070608040302030a080402060904060b18010e06030406050a0f090623010602070e062b06060905011202091902041e051f20071206 70
    0x200e4090050740341e102c1d050001d00c00d0f000c14403090310351038481d02091030402460704201840328110001402041820181080c41d120300072030080d400548910b040015141c0e215590007886242c065000e036086c4101d80030101d03150b150290080c0c0c0d00000600840e10240d44a10555008040349072030507039902c054100400c0c00540f90b0308030742c2c1840203e100341145a20341e017007101d520641c480e00014440d41c40c0502440201110340700c5c40c0c82a440c0242060802095a1007002d07404500d552102800c40c0e000c500c420003440074000e43c00141c1050204112183d41040e00c80e80001c0c0041211100041c00c1030401f503140c050514840c0c104806607150418008170b4401c0c2009032090380000c1c442c0398140451008a81081000240205e00204c005101200d0280850301980f0403402c066603240d969400660074481000c108003842d84228000140c9460800d4503c00308001241c02c688007207017149010340c1c031080022024503400312001d4000c10502014041b06000c0c1003c580b0080124919003445421 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 915538875 1250 915537625 915537631
    0xa0605060303090901180f0c0f0e0a14040e0319030912022a06070b09030301050a0f050904080a0c0c0f24080c09010e0901030819020703030c260d090605 67
    0x3030b400c2081032007000e80702c0300780c00307415101644084140c04803c00040d000804030701080381c41e1289404890046254020810b940410322540c2d820003a480f580c003000030707441030392040141c4050141010301e02c50a040c3c00900305991030310b00f03890401c8174152029184400001c05400000d9071414260200415a445620a01c0041c401003d01500e00040d202d100d016400303254010030000c214400c1141e40f00801c6410169203c120244507040c40072045560b50028004d240c41040001d20107c2c072541c070b101407042250002040f40956813510780341d00b00203510030b4005108000711f142c05000480c0503600301800425425041c800140d2400100000700701181d100d05032a19241104840c400d40d0000355181c0003880745444944c1c2e580f5210040e540600c0d03129140343c100c00c404d0000410b0011000151400140c02101040d016819040c203d84401c0350f030000402041c01c109540d00400c50000040740465802c041041d84454241c030410001d400c40807060b420f0940b03844ca41420000c0328010150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 915540125 1250 915538875 915538879
    0x30a0b031c05030106200d02060126121620190302090411030f0708071a0a050417012703020c010905210102040f03033203010e04110306090a060506 65
    0x464618820700c0105184018403404c42000000c01d141c1c1c510703082c00f00c0034090940b40c0078215880d500030a00041e4440300300b4032a441a0084d03072015030041c07080f01007950031184100710143c1a443c00c00890424241c0013000924030340c4499000c07050009020954070704494103180700000e21103034400c08001c0420301003102c807079080015680403c0141c40e40001950021b03444104078903c8400400840c0c50201c0350500c1c40e540d813040301c000003802c0e0404240d40e015034441d201c4c140030310403d940c0f8201c15482420302b200c000031820803040155001c032401804220f01808000b013031400750080c1e54005805459502c01c031110582c620001003640400c420840c0301020300f440c510319460310340000c000c50500b0140a404007840405034401030300079412203001d0801d5540d600314042d207038180100503400441e64518400d43d0b000314040481c104204038a04144040007041c5541e0070185058003021001d041102c5d83c1018540c82c840c15030702402858480c01c04075004001c50402030402c2815142d014041b28 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 915541375 1250 915540125 915540163
    0x70e120a0803180a083004150b0613060210020a090501051e03101404060806060d020301020408011d0709050903030114030102070609240501030b040b04031713150c090306180602030a0b03 82
    0x80310700c48655401e42c7c1c41340d00408802c0c140c819081d01c010140800d0ba5015a016100061000c9130b030300e052a10340c0a40c2c00035800c40b200b8050450b0070740300b28400d0740c9404010440c010020041c540c4550001c1a40740307010503000c2500800c64094059580003500c4800b0106a5400d092040560f001074501001e001160144541c0d894605003544404020b00b8890040c170031442520159102501114001e118440003040310b50038504600e1015407881098548a001e6150b00288449aa0203203d01400644004d980745920304a0000c4403c18240d0340c003034255400b406080701041d5a8820414001c0c0070381d00840d0500400e0f804022109142c6400c00c040170315040040c00440c2c3c0a2440b00da105910603035886e60358855060503a038541c1d40180c0107512854240401c070b100b11b907502c5c12a1541e88500c0342c0e104104207601002041c0e40400c13103c0400680c00ba981000440c0a90700881d03c00d02044008107413490a503210403059030310455443e094240c44540c0d132100da003410804c5000ca00c00e080a84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 915542625 1250 915541375 915541447
    0x708041d150a0e2205010501050f01081620060a06091811130b0a140414010602192102150907230f0d0b070e120a0803180a08 55
    0x1448228450142000d680c07042c80000d414602040265802442e0505468143c511a880e100e80603207409d015241c0202412024082c1c55402024540c7c0160b840501c035511003401c403041224039690464144034040d075041c1121170f1143c4241303c01030103025590000300d050740c2442404029604036980c50407041c0400328040c0089465000c02861701d0008403180985880800200c03006080b02108089c0d111040c8140020962841020b513115000709540031b0150750105548201c0044c8240705002c0507170440142016003803e9480c00b0102e00d4400c030b4490240116020b420083c2c501d06a00220150f88031601880480010303104450b80481c903100103041040c2001c412001d005420b808031004009401c0c1c02d05c080d55901100e050380010007510308440100c07075041025052001b5105070001c00c1c0301c4a2545403a0511000382943e2040e80b10040c005071080d42e032400240d0344000c20580c200c80d03541c070300403860010922610144d28001c840d40303a15a80a0b40c50385115855410415400c103002c0201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 915543875 1250 915542625 915542629
    0x306090b0f1504050a0f0c020304090e1209090901090501111215060922050a05040b0907061d01020c0315070f0c050c0f0f041104060e03030325050708041d15 69
    0x20248444060f81e0205244d1101114500508505241c0d03c244ca4100944484020350000c05042200c40001043c044408440c44854540b00301140391580c00c0ca00b00240c4150303042c4418900d070800c0c03001d00006520740032920354508503220354115242030040080c0400341e07072021061044e00245200c211074081c1402c140010054440c0f21001e81c0545a030310540c52007015190b12042ea691306021040c03000d4540fa202c82c400034581120105c80403e4001d01007480c0c08400103102d000c1e548107403180d4100c00034851a8001000c42804c40070704605c50000202d00c192000e0003410340800d01400c01080c0e5080625001e048030400380c2d005810022a0401c800101c0c0c0c00040340c0d07603210307810342d0348001c48141000481d0700c44c04840744860f0854180564000225800c4000300f00b01c1d1402d82d2281103400901c4200768581c0f100795121114102e82c0051550990480b4a00f18403100c1d2909200f458405075035945081c2da00f00764807108000360394100b0304124105000c030055100070019004907484001ea40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 915545125 1250 915543875 915543901
    0x60506031e190c180912030207050601170703141b030a0302060f0c2206080901090c0312030204050910050f09070f0e21060603071d04080901180306090b0f 68
    0x440710365400b40c42c008010500c040a00d8080107020700040c01c40b40d070501031242030050011144111141c0c40721003030a801e01b03480303882600c54480c0e01c007000d000745910b04042c040000c10203006200003030240140000000742e00780070640c628800e11001d0012581034245511403020b840703e5482c0a5001a621030b00001e80c0803a50980c050242044452a925884104003c03409080c504140c00b43d401c07500502d5200503968110b0458502d0750310081d8664600c1c3c8034509803482d508000f402e02840b45806e10000f540b022182d20300b02e409160050033700b982c42e40051141ea00581748036a0442120006020702c0c00d00c100b80320b03d490742c2a9211049401c041d81d00038040d0021007030110810482c00b07600380b4550381d10302d40080900000c3d403012940755607a58165896103016101544a0301c5125030018040c29a662032481c00f000d005145800340d034668446000ca64001d0f404d640c1000b5080c28201302820f0010417820145000c0d0000082a10503840c0030485510003030031046289908600300002e55210030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 915546375 1250 915545125 915545143
    0x1030206030c0d020405040501062705011d061918060c08070b071403190e01090320010f0203180615031b03160602030a140403020d02060a1803060506031e 68
    0x207503503103860245080f002800743d504942c3c1d01c07a091078000a41d4075071049005116000346030005100c9081c403141c4030b074001007038810390b03000c603941042a140b480c5072110516210324010380f91500c0c1404212001c506401051411404075404161000302a2800843d000c06424507081501d0076802d1501c2d061014001c45074000c107060700030000143d0303030b52141c1c0703010030810f101c189d00903124200f41c85404400c003200515400c81c24a80104035505c00814001c4441e4550036840d1403240044400b855038250300300c19505102e943d00c507104030301203002c10303c019849160072150421400313109903c070504244003c2c0680c0c00b101504540c102d45076901042c00d40070880c401c0940b07240380c000100403d041c09130041603140081e03000240001ca6540200051101101c1d581c0c41261858000d592190036000314080690408441c42202006050a80007041c4030265414021010400840700510281b6107810032541d2503165424441e440c2010001203200c0d03400e4181c607022404107140d005580781903a03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 915547625 1250 915546375 915546391
    0x7081501030b061903080c0f01090b0a0510080f010c030b0d0c052106040807171c020d0612200f0d02100509060d0516050403150c021e07050906090103020603 69
    0x1040c04510f480c0d03a05003c02c06103140e0840380d25100c03592414042c02940003580d0103503141c06a100d41a0141e2018407408840682c03000031144591034000b4410001c0400a01310280081054004030b403c0d0001c019400444e0601e40001c502186003820082c2624183da40780c0f0700a8001c4441c640025610101c0311041d03c80a54400a0260170308071020343d0048a07030003055039030280100380020300c2001c00040100074000c003040c81c80d20f914040107944510801d00106814000601c1c41520014070350001d29408101c514041040e41d1280b07a00e040c006500700d4100d0f144580d5820322034590b61100000314407414222413100c2140203c03001310780b0448084a00a02c02c203a06581c0454040c09007007540c13204140501215261140100d03008000c00c0c080c6d8581855801c030341c40d441c56091045044030156070348002c2078841c0c416040002009017100000d16401d41c0560122140c40c0070040c1800352100f001c100041200c2c03031a00d818021400d07006810103018100030401807025817100000c5075080b01380f03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 915548875 1250 915547625 915547643
    0x212805180102071d0105040b01090b0712091d070e0f031902041824181b0b030c04050120030405060a030e060709050f01030507081605040e0a05090708150103 69
    0x1900d40100c1c140700785500460801c44214001d000142c00d401c211034142ca005440800c61008130400558101140e881784040e030f44010082d0030b0000b4208400c1d84903d072280d09107c0105900c4050001c51401c086080d1013107081c0120030011200d070b0001004002900664104000044000100c0c2d203035040405600303d1031880180c00421915185c1c41b42008071a505690b0b40140321929203040d01900a00072909a80640001d201400d101445200c0040120340042c61081403999038440b0a03100d403401c01001040451400200610707a100210322030480050425078079810180054040d48401d00860081d00072065085860000001202c05580b0200c42d6182c50b01c43d5048128041e103880e140d400d96a0140400340041181c000c4143c10580f0700c100d80e00303080190307604011011140121011000036044102254030760b804105000b40c000224641140741c01d485101c1c40141c03410994640702c01694070703003c000305080c050107544041c200b80b40c060144000c1402c04000c400710180009022640 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 915550125 1250 915548875 915548917
    0x30209070c1e08070b0919020f041b1101060e0105031b06040f12020f0409260c030310030539010306090f0603172a212805 54
    0x300b1658028034501e5062055070481d00398580040036070000d4004440a43d00280441c0e10450041500718030103218030b5105862144503020465600c0e00203034130940040e541d507a881e06014070214088800c0c000c40d100d0013031040141c0d2040c1c1c2110201c0c3d200ea005c0d290351500510869a0100305601904d124410022008807040d001a485110b00e07030040b0122000c0d1100000c14108461800311100c0c0200d80c02400c20a1842c01c1c00162401c3d080010304882490224182005410360321000300030b07040c1c50050610300048800391a5500c01e1b00c0c01c60140b00d150b10100708020b410001d00c1d982094110054280c3d58401452038902d4203100f2a55110640c4149400b0f41640700380d10900040642040c00c1c0040030300004110001c02140c0000c2d241c000600d0b0b1207000079190002100c003448812000080d100e404a59107007601414420141100d0103040360040d07018075406400f1070303036210250801c1e50328025112844142250001d990b01c3c4081c40031040d4010310381201c01d0361098001042640a101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 915551375 1250 915550125 915550133
    0x914040c020708070806071205040f02010c110d0501090c1406030f130804060f14090310050415060312030b04140402011115010801091b050901121a0f04110109030209070c 75
    0xb03540d0410f1032144103101c80051004000038120b030103183c95807035042c0f601e004450308070181c41c03040301c020f0b010000d07494260006500c68245600c80354041c9241107a2003413207400044480d0b01508055855a440c2d0340b9403000c0c032661210368402806407605900c180c03c0c1c1d880c080380113070000030300c91001c1c0e20100c0c001403c41482c010509002c81e92004199070358986a00c009054500c00500c000001904000104400e594860131944c1c0c0c01402401850082c612040c40070180c0b0008100300d500c54100051440380c10303040d0103a10055031103980480d03444180058000c08a91425984600c9039040c84007a144000720701c0d401d44c0d006031b020320780400c8c9400c50a45452078a0070004035503280080410001031498010350203584118440d50007540c401000031144403a0030300b14002c095001070070800402100c0c103003082c1010114860a051700e00e0251040714020000011107100d8200c0c2090707810802040803d5503007210040090170a18199400c5801243c5144801440300040c010511201803c0c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 915552625 1250 915551375 915551383
    0x302030705010903170f0712180816030f050f0f0c03090a080f10090804141909020304030306080a0c030b0604020403051902330d181a070914040c02 65
    0x345401c14000d0220114504c1e00030032035015a110f0180302c3d403034900412015062180086d005803140d64a204a081c3da1200c1c01000340307006060b0002c459032490669001407c90000340c280000d8007032010b41d5144c4507003006403070451064001810050100205182180c049068503011039181c6010b40d00c40790008003180c84c0d841500d176519403160302e030f50300022440e0000400d070250101da80b003074440280091500c807094403c030314801400000c003030105100042006c0c6032640d0b081700040682005440c00c01868250304995007142151940000400041c9034060003003c000b4100c4900500740108c15445011054206001c010013010303181c004100c040d50307a90182c0d4003031508541a10f013050700c5204a00d400d581c41c040c00703d0241000d08a0644000a211000245040c42e41440007200a40030014503060f40200140300040c3e43c1d4001c1a600d43d00c410103030040d0340f4030a0b001c0041c55010480000d81c0c41c84000c02c0d10040240d030807070900161003c11115910b8034000c0c0c4000c40c00c40c108040070780c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 915553875 1250 915552625 915552637
    0x30f02060d0f1e0207053703020d021e0a06050a02040b211e01120305040308030f06010e030303070504030b041e0f110406270615120608032104030203 66
    0xc0d182c00c01c6240c1c040c480b519030141c81a80f002d04881022034060503110000d82c02001c6000d880c44c0c008811222071046414003040304419582d01e0401903ca1020202d440e60185d6581a401a80301911110017190108a6036091b5200705901060b0302c80c00704203540e504c00140000405503512900800c00703c1106e901600c02801010b11110b84070800282c850090025002c1c8044500480a011a00000220708a2140505103020783d103043e070b0030007510390a0706907010300840c2017040401001012800410107503000d07030003c0048188d03e0801f0800100311559001c442032180d041042071006d815001070844044a60284105c1d01580d128140070141e504041e9040300e441038110b000e9410001c8a01c9a056581d00c82c96151311141300c00c5c07081c001150454003840c80300c8040200701d88802c02000b08010b071051010742010610946a000300540c810124105074041004060300028141c00c0f4041c0e00701400c12070b00110305040e000c030f804116010034444031002c0c00c04d0a0b0b000c41c041c54401d1003202c075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 915555125 1250 915553875 915553897
    0x71b0320030c0604140f060309030403032010141e071d040207260c03090418020d24051504020a110d0801030b0627070215010b041409090304030f0206 66
    0xd211981c905e06800003104405e03106210b08201c002daa00c05103401350682e07020f10002d4005508150031a501a1561104c0020b80d00d0311400f4130038241d0400c003007080142104003024002103503102c0c4400b005d04d105040542001a55810040d40401020300e064400c0e50080a51810704402c03103200340c0411007040c1c40d80329540c2103400000c054090045004080c80c00d21189078640301c500040a18025080c011320701c000210746c000b00038100c1645016084007600e0204109040d036803080642c002007c00608640496552034130106002b02100032080000c0e9100300180c040c001072a141402d1900c22909125003032007141c1c0401c4201510b4861286107019070304040495458000382d02d000382c5000c80922003210402c84400002c0da480c100303076491400d01007119924904c07090740f41c41c0203e010240101014118415164220064604410340c10f000b4588d00f5250781d642c608045240012030304940c00350340244110014400030920001c101c0b022130350002c1583c40501c2803880054061710500d90400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 915556375 1250 915555125 915555127
    0xe060f010e0a1a03060a0b19051b0307050a05060c1206060a0203040b0406020105100504020f0d1a033a12050405031216080106090513020f0409090503071b0320030c06 73
    0x121605510402117014010071105c1044003940c03050244418404c4080c0032840801d07199405945034001d00c06081c1000d0500c1c14402c900050120051641d08044010380c1c50b07611034840003090000c20712180f23802c2013001c06082c0c0341c103902c80a4102840b030003400072800340f00005281150f5138428010f0310007501c201013a15170b65507640c0c02c2c001d0203400180c030224030310000507000103808c0c5414030894040e8244220380320b0030072410040082c014036560010701440303881c041e80b84c0100c1d5028440c42c0144880150018080f03103150110440d042c00102200c840b403071140012012040c4c01020b0302d48281ea00c03040200e09542c03a46001c2d42103005070040d413412103c01e00244581c051400d043e0000c82c000e01e6843c101d00340c2e070b41c0c6001c40d0300400c00d20074581c00101d00b100401040304035800822030380100d0f0300c409140c50b61b0340c1c0c1010111008400107481980012500b2810400500c012000203100c500e040d4610b58119140d01d4080d50501c28601034040104e03988158a4401340078203110441c4c010302d21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 915557625 1250 915556375 915556409
    0xc0f031306090b0106120203071b0302150901060f1706010e0901020c0a030801054b0303071410051e04060e07060206090f0f0304030204020a092d0e060f010e0a 70
    0x43c900c4081c02031744041180c0501e001c040303440324404c1d40e2141d05555910b9100c1002030010b00c504041041050301103001c1c80c44500d1003410310484031070042842c01e00001e40307603142c040519040e070340907040042c03030f6040216048550b81c00014614151004620503000c0c40c1c0302c0b1144c2c00d00900c0340800c846568080d51080509042e000000c0c181200c2094601c41c2c038083c0780d54401090000402410801c0d25403140c2100c075180c8910100044c00c410b0310400000111a02000030714680001c41e04503500900b40c501030b1290141407280c150302501450b010310207403e140c0d60400440070140340c030104160064002030b0900c241c542003004511048800d075130364507484641c000e4451000301c2e2582ca4610a11041002c505000a05140d041c00300c3d1025505003401c40d400c010207903008030f00c0002000f000035404038810ba07405010010400340c80301d450416131410901e03074080503046e40c0040864105001001080d07245da05c1c2000c0000024079084000280c4240010107502007900001c0791b0040309804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 915558875 1250 915557625 915557633
    0xe1306060b0a0e0f0a15050f0d2a020c1306120302010b0108090f0c12011401090e010c030501050f0f240705010e070303050f0f040306091b050103050c0f03130609 71
    0x180b080d0901a61001c04900d002001d0102c4030328204e03070154100300f94803030400c11040440081503451006181c4180f90036420b94000d1041d40000c40032801042d43c0d0810359006000040303060000b030750040f110000710125800080d40b43c1244054650051303101c11003440480007a58080000b40124680c582e0100c01c06080c005d00804104400b030f408127064201048040d100021001240078101c0000c040070031070803090003010401010000c04940d01c8407600300d05000002c40b40d42c041d14100b9000a007120780111258203481d01100000d0501d03141800602003506c401140c003402603825582c030304026100e0707404281d0480110001d800e8001c0c081c0701c400c0300d40c40102c00a010480c028002032140c0312a030440c4544840b603511008003c10800c00403100d40c84603201c05008810304d0186141d0620355240c4400099480c6400215a10075044204418600304440c01d10041c05003031800300614509801c1c01c614174840d1004000c488100840014013940c0071101007190b03560b0080f400e114030901850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 915560125 1250 915558875 915558877
    0x50f0f0a030f02130302010c081201080d030c180302041802041e1109060a0c05070807090219180b13091416050f120c0d05180f0c03070e1306060b 64
    0x10014000390801004010b0007080740251000744198082c00700407140782d070340150f940400d107141c101c944036010722885402644404250303000344580005003c0380c1d030202c0001803c0354056200c080612800c00e403041640010244900181c0354103940c001903035600108088015842040c001f5840b81c1040000c4507070442400c80d55140b107600d84014030000011150303040c240d00540c0e803001e421a20034441e01141038426000c00105034026016104842e4444900d5401d08100760880c0c600c00c0e400264611100f54440210004d0f01c0d424605480d002e2048450050035044030b2140702c0c041d0101181d510101c60106040c0070083c4550300e010040520b0504030318040e41d008549820a07840307400303540080d190207082100c410540911081c1d00e0001d8025142c600010007805ca0442c04c10140a40c0640c03041030f101c0c990254500703102280c0850f494051042c541145400c44074903c0d04181c1100455072070004080c000c4d100031010304141c2d43d44211119401071801500070700790a09180e8002154242c1c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 915561375 1250 915560125 915560137
    0xf08040311011e1406060d021e030c031008060f0403030c0e03011b021507052a16091805030433051201050603091b030c060a09080d0c0b070f050f0f 65
    0x120050081d40301113540514a82421150607130401070400401c8400201a8000c2a8820349505c2c14a4100449258541305410460b109212041e0000c10301c1020780136803108030300900400c0024035040ca456070301641d0506003e40010b0615454001740900c0f54055600c0c0340000ca800b4008000c02c42c1080d84804603580e00802040250080851080101201c140b003148600540e4560760314106031a007510500c040c480c3e034814090044061042c1c4603107000c2c480c1c02d4507501c1d03103241c050145091200740301c110307a150000c0f94403a50100f1811000110040203031000c4a07040e5185080202c52080030410700300c080400c0c0e2881c11006000c5e4021240c0080c05804c01004403c490f200030382e240c809120700c0c1d02c0140c0d032034009030703020340d080c032408c105241a64490100042d095414041c001c2e00844c00e00d41092040c10082010700b07200348035004003086502180d80582c81d01c1c2c2d81c4c02c4503a45508400e80c0001d00007200b081510350040b51b1030307402a421124900c2440450a039511039180654031316800c61 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 915562625 1250 915561375 915561431
    0x60b100e04050a020406080403140f1602092206020d0b0a0f090605040504080f18040e03040501030e013602090c03090c040908190903050a0c0816060f0804031101 71
    0x1180200e400c1420a01c00c5e070382626030503100d00b000b03070f110381c0c5090b104003c1c03100d038900b00034200708082c030b100d4401d500182406c0c096048414401d81e240b4810801107020061001881c20942010103c0f4101103148820300140c21010059440924400400192482e41c0c010354116244850002da5000c0b216158001c807464004c0800c04e003611202080292081660090110306007407200c2840210080014134140030704666084900d035111b008902903407042100d81e02d00e40c0002c1020002c55070140a44035100c50854001c2241450604180c08920045441e21050014071407500749280440402a07004a07001444259a0319140d14541810742c8215440d00c001d00414038002c030076041c00d0160b101c0080c4d02140725410a084085d002600500f0407a440c0300301b0044030000004540d050100801d42401600f20150460500680030324081200e5140302250742d034108100581640300c505040b04069600e095030a43d01c03141403c86096110203807032415940381c0303000c540c211640c80f03000003800300300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 915563875 1250 915562625 915562631
    0x1202060a05090c090a02090a030809040f02161101021906060501111515210a0c0e130602030a020d1404020f01050a20070816031a04021c060b100e04 65
    0x203038003151054800584907200d09500541c408109442c00c20b200c10b9103c040f00c00b005042845c543c1c0044c5203659640d10030342c0c41c04800204aa0b00d0704042c05514240006a80154a0040d40c07000629600c4c800581c05800c80c109800c881e04981e200340801103c100c01c50318000c070350030014140380000b4034581c401c207408580461f211911580e00401d50401d4011040700401040d5075607800300070301030f40304401d42e139000d02030a21036100b1103445400342055060500082c51600550314104640160304d802210b020002c010405c80c0000c07c0400040c106603110b8405602c23500c0d8540c04001a0282001a0003010300300020f0381e0840d4010442c092103240215080ca141c50603040040d5410b10501410200081002e2482480c0346520010344c0144205031080b0361a0543c4e4000a0342441c442d00d0805079080c645001c1001440842100041c00c0036041d400551181010381c00034034a011410140d80300c0007010501e000921003a03a0011154400140c41d15140c1c4002c843c00611340303070b07440c59100d100d84d00e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 915565125 1250 915563875 915563881
    0x50c0607090f090c05091201111606050106051e07030512011409010509090c150408070e0f090c100e12060a0209120f0a1e0501291008191503120206 65
    0x3c0c02d405507126013550b689840e40341408a50500c80200e440c4c01d00300075199240d100580d04880b0840062080001c2004182c80007601d502e40201a100e069002d0804c21a05100600c1c58505445c1120b1440001da88908c4d070303d0005250070341c0c443c019600e40300b14080458000040f0340b050b4120041c0c80d514100e4000a8513a200c2007041040401641c2250107940b2480c14091b080c00c01d5001690100c81800200b03040554a01440703150a02c0c9802c1484d20b0f80309075080c4031800305d100080d9600a203c00c006094002c0b10760010a1503000c8003119201001000c1854100b5621000d203403040c04150807080d01c0039071504d00c039200060350014521a0091010b081540c07500e24000c90600e100ea215100a40084201030b104c480039461108850710421403d1443c0c41d0025500f4811604a070004408202c400354544003440300a01400d6030031405000705410645c0601e610030300b000d6004c5070107060107200c1350b449181c503070003440000c4000044c444001e0002c024044050840308039695240d00f00c4130256 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 915566375 1250 915565125 915565139
    0x60c070b0619090e01020d0e010902011803050604030e04021603020609250608071103040609050a05040c09090c0905030f0c090c1e0702010c02090f0412090f09020a050c0607090f 78
    0x80c5401c002ca003041107161824055540160006426161020300140c11302d81c0b40f80e40b803012a0350010b001540d581d501c1150f0411560040e81c030300b400b9492700c4800700110b840c5446442d111200148010704000b07507030b0070070351496603940d0544104043d540d841d4446a0880e00c0c029548032002d854550b817070701c00c40c03000c04007100143d09407034400198192418175891411105842081004d81001d0501501503205941d10030104080e000070310035941c1d1601c1441c6044240443c14485400480c021400c141c021405150003120000c100c4001c050009441807180c3c0301129850040d8001540c90701500c0030400502d100080c0c00c00910204840451658484202c654220700c07a4400000703559155009043c2c05036810320140000600606185601c003c80e5070008514080c01c648032400e030140340d006c0c44107020f003c0500d500c0448450820a02d01424001031070301c1500c9504c545840395400240c86c21541e4420300581d00045004c400700c0d202420440b802600010172802402d01149950400040c07003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 915567625 1250 915566375 915566389
    0x30c14070513050a2a0801060309050303070f0203090409061a0d0c030303020319090305030f07020708070b09030a0506100915030803070c0219080102070b091527060c070b06 76
    0x1100001c0026420310b03460b01c071180140400074040000c0e50741d6901a005510540c9120f60b0200c0b1007880308240300c91091380c01405062040c0c105204061070141c8010000b00000116a0001614201907180c0361240100b00d1551040b41c20301a0840c5c105101c5c1c0c010428160492031a928500800c590071000520a01000605c0703440081d04100c4103080030004240242d000356084844d6460443c6080c8541d07007440181c4000000c00ca0014000000f00310044529501c07a44d0815154030141c156185418030055440c401070041031280c03040040d0700c0202d80c0d000c1202d5684298084140e50321407800801c00d40091b095403042e0317015141000392061040314100201e90035aa40400e141e4110b441c0c01c201141c0e94150520100c1e0000462503814880311540225840140740020016940c0e440f5468800031032000540301d1351136030f84410004c00304d02080d902803c0e80b002d81c62000c1d02c00c28580c1450202a000300b0041c41096000314001d00c1081c8000308001c005903805079056018a0b11080180261 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 915568875 1250 915567625 915567629
    0x60c1e210a050403080a050c070b040303020c01080f06060c030705160519081e01020702031507090f0e0408370801273803060903071a06010c0f030c1407 67
    0xb001000103200080031900500640e490610f482814000700400940ca00b0321160401203d0301400714040080680c100480450000203207401011420501030b25010004040c00e42d5100d54404500030700d0701c100070015140c4203504074003100d030900b151389036150a200d500e0288900070269800c0714104020320b0000301c002c86415100801148403201003504140b8014200c032035040d50200490000350f6410401d142040c1d0112034618158245688090400525503120600314200b041c42004944d8400560030741c030603000100310350342e9000446203021803070f5155903080848030041c1c00d541e07547c18400b50749050b48070a500c0e89070003a40c07a4207a5903820040c500082417078503186490110051840d800442d00c0014000080084a46240000703504d8010955801005041d90072026a03502d0108841c540081e025005107160070015280d11001d106102c101028100102002c12300a91003106000c0b0302d1b5402c0700d0848420b08241c80d00400000032482c0c10f03900e00b55208400c03201640003098803c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 915570125 1250 915568875 915568877
    0x8011a0304060b010c140c040506190b031003020913200d11031f0902100c05060a020903070f09150e01050d0f11030d050c0f06060f060c1e210a 63
    0x800d6540d240d4920000d020160802030410013450800400120902a03000b0003030b841c0d20203420000d1401091001f00c400013424144214403100003070810b82c20100c840400e461090138070a07130740c5d62442c001d1040701c00c0a13030009400c00c143d801002a04010011161680d47c0b186240e00c00d40c944d400150541652011742c90340e88940717000042130004035070740140511600060f043c3e400a0702000000c200c03660400358104100c030344580345541140752000c1e98900042c01410304100001554540680d201802042012040d90000320546295000c009003001801303032a040ba820740d0f4076001080c02070001409001030354003407420003007440101d500c0368906075100030300710a00800c01c580b5803011001801e201500e00254036020a40d0a480c180286c11040510380caa280c3c0d1030041441c9507251034022691051b85411203010300c9595507a0841c10070309503008803240d84d11424090300305030906011070b104403130802d42401c801c500f01102040c0c03260403071842c10001d030004d040401010b00345c2c400c0d003100300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 915571375 1250 915570125 915570127
    0x40503031204121806031a040c030e06010b12010e0703060302190513050903031308070204060b04060f020309010c1401020d0f1d0a050606010522030c0e0a0b240f120708011a 76
    0x1001e420f2103940104947c100c407010000c07042c244c1c000400c0c00c50301c13103850341000a0703241d403004088060100807040c0103145103014030380380120501036080b24010600801e820201044007041c905846500b002010355001403005500e8800f82c0034816040d0464401c40c0d000d144015103580d0041514420a8865a1044040c0d4a50780d51078185056a10300c9580c03c0799124401d0007001c0144e100c0303204072409404403495107965181480b001924040c1000c10010440d8000c214042a599200c081d2000c0140e00c05c200000001c0c2c686800d901a0042c00c0005801502e03000c05900700110640224840b8180c20340c0c24078803003081d541d0458481000e0600541680d1100c40400c0c1d9a501c910300602140c840d85d1184882d9021b50b80011306000d54603031007501c030f4400d001e00510168070200b24654000c400004100310a10701ea0000ca120015036800d420b1012604500d0f54034207142e078408581100d01c0704c3c50300903904c40d02031403400340c1e0780c0b02507851100040300e04001240040200704841c010035443d1482d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 915572625 1250 915571375 915571379
    0xf180705091008100509010b0904031b0201031b180b04030308130812010608040c210f06020904020d06030c0b03040215091302030901051803040b0d0509030405030312041218 76
    0x220414640c0600b40c141981c0700c0300c0740091204000e2152180c06240c00d80c002c80c0300c0c20301d11015400e46d0403140b4001c0c8144c69402c1031100080d0400e00c4102e582c40e40c5404c407440150f5500058008200b1081135403506d0302c8e07144030307c00503a40c040f02c00340a245054410104c8542c885450000b070303020742d0100802203803e038400305200c0301502c400e03480712501c18003520341b9143c0c414040140c290403ea120801190501080c8400c00c07200d00142d001800c000c0141c0322504035990820349807403500d02d0b0054443c0d150440980701303001c40d40d01181d0a0150141c025999024a202c4900007400c4910064420441c0440d0108442d08c6010440340219002031000b061603508050082c8680d202018013a401030380b51841c5047c0c2c0d80c240c00654455080180001180d00c0c0c40c085040d40d40e601042c0d04011504208414401e40c0d0b038107c16104104203507100024184d452500d401c2c6180b149030000c55040c403010400040004200c00c05512031481402c002114600001c000d035a4103003154100340c1d005c4040002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 915573875 1250 915572625 915572629
    0x309170f04050d080706020a0c0b1f0902030601021516140a08010611012408010b010c081b07080717160b0703030f0b0d1518050304030b0912040602060f180705 70
    0x4854010b0040690713510303042d2640d9810041f41e1025118102141400d400d1300148820011000d0348295080d10a00682807140c820500c0d0102070300030868442d40c0400880c0d0300c3e910810004100940c808044001c0e1300b04180c0b084c4e02c0000380b000324400a0000d425690603060a181955101800b60b1a143e5035a420a0000d03aa43c1840c03e4101c0c140399aa01410580030802208480440420002c00410300b800d003480d0500b0740b4414078006042c015001c0310703c0005038080003203075240005150142c01c0035604100b42c50a003507881c0c2c000c507014170508001241a038488103000040c40708485c21960320b074000519640e4460f0b620702c5039000b860002e22145000c240a40c0051138039240341040081c1c0201d90600141c50151104029a442d00c1030684e20303030069034144200d0300d0240c4c00f1041c0d81011801d541d070301e5559102d04d000c0141140100710201d8240101080300c8140d030700071820920b40355170315100000d41c1e40c1411145a401004040041040e00001400320b25912220030060000c01e0300700740c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 915575125 1250 915573875 915573889
    0x24011403030d090f020907120e07032006191806031802060c070902031617070c03200a03020a0204050a0b1c0302010603050607121802030d0e011e051818160c0605070309170f0405 78
    0x1404030f03049101045098a95448400c1c0c0301050b098507100c000843f401d802003800885845d40001d8103061801c003101c40e41d11001001c0454803903040700c09030b0f510103c82d980c09042807017079448403032868004000d00c060000c00301d8815041d0103099444040e00710000d2640c604880065400c0c00102c2c0d402501c82d004a40704500d01c50400d52002e020520280c41082958941121300d8000d4005820004001c021440e0a01030641c03c07440d003d4061101580401c0090648070700e66180d00c031a02a1f0301048010035000b03411800041d50010196034180c9405100603000707500388010011454a460088601c04802003c40c000c6150098020106000350b41400d44141403e092058181705240216100c0e00a5042e4481400100382e91225240c181840d0906104008042d0151180b4024020116152818055594482c0e1038075a42501c10a08110a969454400c3d0020b80203a0402041048042d00342e0030191302c0300d104854000341c00400f1003192226005511040304c122400308010002454156 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 915576375 1250 915575125 915575183
    0x90f06030b0c031f030b070201050a020c19051204060c050606061608090f100309060f02072a0e1806070e06030a090302030c24011403030d090f020907120e0703 70
    0x1110485010b00e00110342c0310440c0c130603402120251010400c00c04483d60a01800760484400d900a60501e542600b80ca600d5060b402d900f00f105208044181c0c0901504100d0000050105440c49030b403140c813000020a0f0441e032030000c2e0380340d20a0b040801c07440c0c1004022a03090942004904070080b201e945c2d001c41a910a00700654080e00286541c64581c2d0382136119050301000741c0300041c50007003a1401000f600d0810041d0b89a8a105001392030218107884c1800c444c0780c0d00c2200807d640510f608070311891035096001328850004450800c840c0726032036402d80da110000a41100d1482d511450200c5980d54a111601d07008030b014000b04100c54560381281d150b0500c81d0064a00f8008448220f0346040f07000102c0559a0101c05407204984403400031050140a40389a100684244803012940c5e9200380c2c80c41032240c075518032046e002d000c6600300e000b00541c4d0081c051441c2e81400c00e80109803410707040e55082c00d1440c100101d040910001604801c8a9224002190303010819140780b202c44000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 915577625 1250 915576375 915576391
    0x1080a021507140606040e01051e0711010204090c1403040c0b0f07060e01050402180108061f030f0b01050102100608100b040905190302070504090b060915040c02010204090f06030b0c03 81
    0x9101c02c20008808030440300d141003641c801072803685002410003095030004e220000312a4505000c1c880145400000400340303141e54100c50300780380c80340301080b00e101c44a41c0b40c42c9580c0d4030125020402401035080701d8010318842e0340b010460b00b00c1e921424070a1000743d40041c10810005010843e0380d4015002c0c0401040c001005800c0c9602034075180306484490162020380c1e5075580400c0210b281c200c14002c542c00c0c002c1144551581841c0005079103150142810780f02e00f914002c4890781030b00c040142400b559100318501180c000524050303001980a00034107015008500c460b183c035500600c0359401310313410000101000c14a812860300180301818400d50010349034000c0c240400d204101e10441701070101c0d40880e0b028003a040003410078010307801c0b4a12aa04180b880c20203c0c1d10742e0109504403e084071000065210240904170f00070842d060240c0040c1880c80c07080c600d68040d400740c42114814201400b0b40d10b804010213007226071781e010090400c6000d002050010400102655100b000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 915578875 1250 915577625 915577627
    0x4060509010e0a210507080303090a03080a1d0105040b071b020103020f0f04030c090b0616140a122001091703070c08070c17010e0717030409020c070f0602030301080a0215 75
    0xa03440c000001d40c5000c90b0a261034580304c203000c03040020400520300100415000b07142141842c402c5c0980b550f4003402d000d004c00110b800898004841c540c03000444421034024805003102003084c55000e01021101034516054540005411501681000c103a034010704640e00700441040c1e00544c02500015880e5010803030500404620003d0003004101035801400c01041c003e02c0d1114500c1a584400652406803a085c0181c2260a5150030103910075a84804204895020840b0441c038045111101500c5034040b14040750450340c1000e4103405a501010340002140d8546103140c9c06d03103510110003001214030110b413032140300a150141d03810220314502014940b0350390301d400784207030040c4206071045400300030304101c0e00040140c400881c0100304000d018440c11401d005456030140c1c881c0d140c5c000e005041c6a04505400e104403030103080380c01411034a40f80c000280580d1a0201d010f50250200450070105400f8000005c0d03e040300c07078120081052015590a002c0745008150035401900c00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 915580125 1250 915578875 915578879
    0x100c02070905010609081006060518060921070b03041a060123091c0f02040c0e09160e180703110c19031803030e040b0a1a031b04060509010e0a 63
    0x78990158500030519a40c51050003810f00d5009410018a40704085200d40341c800704214080d04001a22006000c84600c0074940c036181c5c010420500c41c04044561004198100040711900310080403810b46c100e60031036020700c0e210107107110180300c180d0f00502800784042c540b400134a2507403002075001d4070624240d20f2001024001c02c040b1003074001900c0415001007040c041f5400e003d10300c9034801000c50782c4c09007492140d13240d1400801d481007019004d60f8440d2a01c44406001c0c1076596000b10000c1c2080c12145480110f000341503ea800b12040050700e1103039044414905402c005020119080e0101131036207502d517050b402402401024081c0020030b015100e07100605000c0c000114110300c3e10480ca440483c0790040600d00c00074060141d500540c042440404d51182d80da880da80800d440c0010092208400a100d8280c25803001b0101e40c2c13842c148003500c40140b000f03980160012510240c5d2100b40c0d0014255600a03070044400244050028100315880b4540c0f480d10b294000e82180b034a25 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 915581375 1250 915580125 915580139
    0x50f130b0a05040915060f030903140d0905070503030f0301171c0503100b04120b04021305010f08060c04030317190c0203280206010302150d0f0902011808100c0207 72
    0x80c01c290241c0000c5007001c01c042003404483c1c0542c403201480d411801260301d041280140c009a03103080c107102010307900c1400001305401406440400441c204503152a64043c5c02072402500b07005c2002c94140c014480c00064a0500200307446400340d20b451f41c40d0450707090040c504102008460081c2140c8502d0a2180c444220421080c1c1101455500c8950300e24090200d2007280520b5405400701800421040001100c4120405900307a402105c80e82242c4030b0740000343d0900240f0750500c1002e0f00c1e020002881c0d460b54104602100c40c0300e4141d4203195200104403105000b1407001402251050519040000c4e41c10017595100c11514652101c034610034140301c00b15400507000c100982e04c0007685042e112a0f03141c5224421100741c1484a402a144100a4840324103100090141d045405081325070141201600d50704603100d030701082092420109a000b07402900303000da0110f0031030401c0c8600080988840d00c290b4400d08000c00c05826200f9a100091032001c01820460040d008041212 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 915582625 1250 915581375 915581377
    0x902060313080d090c03021e090a020a022d10020301030803010909060e100510052b2a03062708030a0204030b25021609181a16030c050f130b 62
    0x2500400c5c13900c038203c0c1140705202610b81501d00c00186030301c541c0317003060880d5503040c001607002801840260f00ea800d05801039160410015580c0158120f140703180b0070310380b50843d100720a000ca01003201d01c003090340c001c06022440280000342481c013042005204411840e0403200200380715030000140c0d01000708005050800d00101800619200d20503c1090042c0903940b0000d04002c40d17403092000742c0b606042c00c41c0b0492041c02656071880c009045c060107014103000164408014001c01d00140c200380028507100103000403290706240c9040c1c040f10519448641000c012404000c075001904d540318074401d80c1004042c460619000c10000c00060b47c02600c042c001c0b440300850782c0e185210142c2c0c810920810809900c1154040c1d080210450020215442110440c0c0c0f0001900b22601031701d04c46220088038080c1034130910030008410ba00b52842d00c1442003800d503480d0000446040000c0301529543e48a20300010414000c480320300b010000101183c47c4494041c4552503580c2d0314100d41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 915583875 1250 915582625 915582641
    0x19050f0334050717120c0c070b040503031e040f09061502030a0206130f0b0903030403030c091406030a0209100203180d03050a050c070e09030c0708010902060313080d 73
    0x11281e90781e45940607000300e480040d0208000300e04a10640d0041480040050040001c06440c444a411802c881c00c02030404032410300d040144035080302c0c6802c0720720030210380c800d40d602c00c0c0c0c91050780c6c1c00080707112200c02a40c0956030700030040e501d88507541d415070f00da0160400312506c4440007044006041142000054012303c0404d00c049210341c0307021049030141100c40b1801c015500708020b014256a8046040c1b0340c451645151503c3d1038282d8180b2008410030706400400b1189000140030b103000001020b140b04034800c2c0d03018000108807c40490b031915480c81200d44c00c0e102d4010805191500300050359122401d00b50040c2410796400014561110841c420070160704000b61446102c8444001e0411400f815641d07455081010354008103584260241c102c00c100300400c9042c004502880640001d100071a102040d0f800c0c0700d0203c1d032300c0b6071003840407400e02e2180c24000241450107000d41404550000d01440c2142d448030000000c40c00c20b07000c2281c0c50300d0704000e9850141c1291003490b0f6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 915585125 1250 915583875 915583891
    0xe01020a030605010201151202060307110d17072309010201090b0708040c0f03020a090f02090a0315060608010e07050702010210140610051c0b0d0c08151b19050f03 72
    0xa03064500f100282c00c550703082040303580759030b01c1c00c2040c80103a1075402c2e041060b6906039071542d034a13600c54004644640e24503207801c405000c0c450004c0c0f541d40d488840c003e1903c01d1015001d2072501ca6400030744140510707068060f0507100c0a001c01c60280610409030039035043c10300010801803101c0d40c40e280c1120003100c0f04800b10303c1050610081c00f01d2064070304094801d0300c900300002c1e0b043da00010034441c3c1c148541411180c076104a0011132825030152120044040c0410f005142c6924041d00340d1031041121007000c0d07140c8180029140d1260350100d04a03821814191495141c0071000c803641e902c0b00009038158409c0303c0255441c5a45480303414020482a00380382541d0030b185040098a040d41d500d00410000d09200d43d40000b0b0600381c110403004070402000400102400105600c46003421000d05110354081001a4641010510000b60707081ca00c03603145581e8800301110030441c0f0904080000c42c3c0c0611150780260f07000c0d4818281280141400f6040042403546115194421503c1e91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 915586375 1250 915585125 915585131
    0x8040b030a0b0607080319230a0513020108130219080706020c0904080921010207050f010f06180f14090c03060603030405010c0b040602091c0309050904020d0b0a0e01020a03 76
    0x8940c09010b0300c40c0403440d02003260081d1070000300f5100d0341c80501000d010040701d40010b00064400c0c17042039100c40325140881031810004060280340003480a012034103002031134142400039180da0000361a001016034140c642d4110340d280c088810240c1c0c042104201d82001c1e0300e05400e03d821904240d800020700c0d0316401001c1c1242400c00c001c6c140b03000b0392515409415071074140000030741540181d0341074002c140e84c0e8000541408401d176500c0d00110ba8444101d501c0011010280320000c501c1c2240c0c1e0358018000d21020a000c2c00300000c482071881079440c502854a40340c4040389031504507442c94901003401088171400c0c608520401501030300d0151156008480203502ca050034050300b640803000320302031030405203031100207001d58050045c024036403861800050f00700170300395064407000314016100d46032035010001400f014851256040d00810f0501d00e00080b00e24007510340354401c0c0c0d800350011546480546c5c44000c0d6007005443d5801079034072016040350441e800d101410624003156404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 915587625 1250 915586375 915586381
    0x16080415090b0f09010305090a061113080a030e060a0c201e010906030c110102040308040806090c01201c181205032b0603060504110904110909030708040b03 69
    0x2400011080c0c1c040141c4150610040f91041d072100107481800c882070070f020500e941c031400c410342000c040d900010182890480f00000d40300504000d8200c09040707003115007000d6125104150f551400e07460050000d50704d11941501810301002a000d000b00605000c00c41c010180d803841c00908645d0010101c89803690368440161805810f4210f95117040f049d50440c200155000906000c2d141c000d40c400d05440350550700203148101628480780c0030b00c0c0002c40d20303283c49181450b1142c0c400d11540c4001d1241c2d02c04100340000214059200f620141c540310780c3c0c9812070310b0f030204240d0011407901c3c40c1c1c011120781c80d002e805c44822416075100030350398010940300301d18a991684401a0000411509851200c6002801c0001110991021101e181075803c40703d07280a0106000e40e401c0798031150500000004219090f00030034099441510350b080615908001c3c0501c0c0c1004807000b0304004e111b405c0801c013500704171540b180c01509201c140d84c9400700d191a101080e5100e82e212588003c1c0010070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 915588875 1250 915587625 915587627
    0xa0b070e010f0e0105030c1e07020a050109061b020627090106090e0109021e0a03020405010201050618040b04080c0d020a1a04030903140309100309020315160516080415 74
    0x1000034400342420080b5212224020050403101c4614000e81031200001c045112016103c040e18600300e404c0c80d002048211400100b1125048400103c1c0100c4036441c021400350300620054007070310b400b95a80c8107800b644100501602003450b81c01c0c3c0e0080c504000484448002c28800c034a044011654804030100341000d00c085014140e00280411480300340078401d64034241c0546045458000c0050384034810301000e00b25600082d2041140600d00040d0b00c0c103001c0d00368001e04200d4100360020811507842c1024040f5116200d10f2020300d040340708000800040031312101c44e400038001e003516070070310623102c90741440c1c1003c084c00c00380540d00010b035140800c6000c3c035600d000c80340000070402c007031704055030017829413643ca02004140800b041c0781e402041408000351400311100034800c03d44e1306d44008000d80104070010f410b134007a0148260598401100c50100d40c0200480c03244076440c0900c030a01100c803500031680140400b001140908042603191028001400e50156000001c403102c001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 915590125 1250 915588875 915588887
    0x1203040c03021203280f03150e090d08101208070302010f051302210a151e140a09050715030204030f050106060906021b040924060f1a0a0507020a080a0b07 68
    0xf054401a41c48121700c04111030b03011070240c10300d801c3c5043c040f0741011841d012011000c0b40c0d811a407a1081e240c402c0286a080004940140d90b0751601d03600d825031070707545c8030407054000b600410b080029200b44903000a0702d80300007465110301902c000141150150054015108282c071190364092400400200758580250840e03a03050515007409200b901d8012601e40300c1c0da100e20301411701000e4000c01070242550741c00041d039510f1a646084000f1000000040090100000381c0c900501c40e540060101d180e04c0c0315003424a5004401010581d140c03108422210303040400000c205902070000100140300d102a1000b00d86c850400030903070504020008201c038100d544000700b107601000104519115442d503405950308250380218444045090070803c6d41058142d036090020005411030018003d60b0100d8151000d5510721940c4c03583e6000c0620002041840751200900200040400315000d82c1c0140140c070320103442c84031079a0f541d4020504001c00c07444203070fa0b58242d0314100715119500076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 915591375 1250 915590125 915590167
    0x7080106051521060a0905090a0303060602211e030c210c070816080a1101060f08031804090203030403050c041116020d060e0d18080a051203040c03021203 68
    0x2c00150420318180c10b00d181c01da02c0740208003420707810140810300944600c02031a01402c046d81e4140b107a428226280b0396207030441c02d015000240b4005010810038030125004001c1d10b16207419002c2010070b2911001e0961009138075082034a145000ba81104074404007651062090708043c5440b80364600c49074045080d42c0700000c130420162420000c07180e444400b070718222500026810340715a0264086140304480110103025803070081810f0f5421503100c411000180841002845205e903a80d85911103080c0c070b40515142d64005102c0c3c290588280c008640008800800101e200052038001c0317403c40e48503401c03e40d070f40d4000007144211424a80100e40d10b0003000e10800345004058840ca808080140030021b10801b10071192409002c8103800400c403102580040e900003080b13000c005080c02011402c070460400f4184000221014040303115030005810801900498081c490060310740c0e800184101c44034a41000701001503100d04008094080000005555a01400d080100c4102940c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 915592625 1250 915591375 915591409
    0x71713120b0c0f030c09010509130f0b01110d110c09070c0606140612041502040f170a020132030c09090901092006040536010609030b0402010507050708010605 70
    0x41040c208416051804c60354010807114145440f04240c0004032050700c11498440d80c8001c44029628104443d540304405e0840344200403c5099011801034491b0821a001c0802c10b421050080003c1c0d07004030b1907401d10040031000da45885500100103031184800340c03450320018030403003100d40401400c1e106240142c001201040038100c1c1500000d051442540b001c0390001b48850003003000c010403020a0758034510344910541d00c507030700e850030042440381038410295034051034125070aa160000c03402201603030b010384d180350b00765400c1e441d54614034880c10707560407986595842c40b1444d150443c01860080d20203400d046d41e211010310801a5040d4090301501c03650340b60000410002d052151410041c8821721071180c140100d000004026000b65404250803040c54178200c80c1c85403003164940100e600140e18440403c1111072402c07002d80d4240610804152245024404907860ba0700d6294014814500705203488a6940c40c42e0a15440d54440201a9121403044c4000e140040d07804200f4214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 915593875 1250 915592625 915592627
    0x203060a050903030610170420090118020c0f01181101050c061f051503010303091e0306091401020a020105071e1b020301090f03050301031e0503071713120b0c 70
    0x3107000b1030764481c480584001c0c4540401132081c0c4130749000749404858a011445090350f189014142980c000c411086650440a282c898184c0e4500d00031803224169003d03900001780748076002d0100c1000f540100f2000b4114443c403070030728490308024000c418407500b40e4032606d00c124071a89882100302500e055002d05001c2c050001017100c00001901d581c3c010682241c0140000c5103c00c80740d0740d40080d8100580054482051281c2040d00300001d5040b03900c0f0340c5e2444c0d0b5941d5907464850b16115405800c5410130058042080454116006003030314074000e2a6042d006009401d64608a0780905111005070b515074041026040c0c1020108804906280c22440c0c01c00c1003200041c00c41400311a000184001050303400190344095014141181e40030a00b56080f9045080160440c2c00c00d04c01100c5034062140c00c074406000347c03040c0c8030000360b1140040d824011950f81d0809500e618443c0d0407030014050002c00130001482c1e08450017003402103100030381d4403214100b801d04180d00501c4c0300c075041c0c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 915595125 1250 915593875 915593881
    0x1140c03070315170615010309030c060510170a0308241c0605100e01080c0a0909140d030614040204080606011206150f0f030e03090f040b1c0203060a05 67
    0x8010859a0140e070340d1500244124441c07054541e0b401c5240c12618440400d0081c1012084c00018114005c0301c1351003050340580f00c0000110140e480c62035006000412519903280056100e82140da0449801c401c01c00410352159a03184cca020b001c0c080107041c0d800b501600c01403607080f1b015950402004c0ca10304200010a07290142010404a00c1500950003a201840301b18100406840002c0d0310510900c42410702a1010303014179141e00840694200c204000200200002101450300c031014225a01c1149405020300050440440645030702a5030f00c2c3d0005501c0d014401c00303075440c02d030351000603d090074188001e0780d1455032594180a244100700900c160080007504952110302480c005803200003c89600d0040c0c54241d00c03c00301e200502c540105202d4010002044071003d540d10141d402410400440589500c00310018103900204682025810310130780f0203100410181000c41d54186ca5004201c181e08402c61100d06826100d5031401186018005943c0140104100f8840740c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 915596375 1250 915595125 915595141
    0x6050108130c1a0705030d020702031b0114032e060905060f0318100f051503010515010f090e0103060605010305090a0309051c0b1503071d060d1e0809030114 69
    0x81070a0081c100c0030810480d00c03a00d010f540504460003290b00000b582d4541c1c85840010f40a900404000c0340f00c6d000f141c407108100e551000c0d1844c00f0003c141d4807485400345108408106900191011101c140550000010650200e0709450030f0400400c1030003856240180082c03c01009800c03035403041c0703800c0103001c520000e0382e0f0030b8a40101c0b855407100300010951032024036045880003481034290402c0080d100e107440b1980b010f88034400c2c000410b4580d011480400d4221142201c624030422030803a0849003551041c2507004a004082c240740c8807841e1601d58240900c182640119503183e12050180002d50b45800b54035002a442070040405024907a405030070b195060103420301408800c80e091040781c4080b03201032500e503080320145c061410502095040c01d2402944580a44a2024005003542501318846280300c0d90079000403982e01c40e9020822562a0040245c40c1002018032030166091954800d80c6240c0c03103500402d688180340c00515003900c40c1c0541340c3d0410350140c820001c0c49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 915597625 1250 915596375 915596393
    0xc090614031506030a020a0e0403140307052208160f0f03080a0507060b06070b09010b060c1209040e01110a090b0403020f040e0a140a050118020d121e030605010813 72
    0x42c60382100720000542d11800807070314103e80440e0203544624615400280039065103417490055000f03540e1424080110001d20380d542c4416105480000c808021708004410b0740e0340b02e040b03e0203080c50400e6044e6590b00520346404c51814200c3c690050040c0208a030a01307480040008200d0100710204051840d240c2486601803410407106122001071903d04110300f0b0b0b0f01010310b5540c000c04c0729849010038100320014410440d80001c0940ca0106454520300d481e0b01525015200c60b0010441c615403090403035101c1c2c200d840e0040e0000c1c0c031904090310808082c0600c0d40084c2d80005140d0f21419440070051020401c3d030f01003e1000700400040c03002d6100d00140e0f6007070400c291408038501c0800c6954601e4007041413000780181044820940c82103002061110201d401a0300030b0245501c0140070545041d000c540c002c1d403180307a000040e80003c4076104420705400860425160308900e101c900103400d07291450140000e6981c1105014030360700300a94980004501122000d000c05c0e5039a400e0103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 915598875 1250 915597625 915597643
    0x150108060d02010f110a080703090e0a1a010f12050a0506150307050a1419081506040806040b06010225030b012102130b0418020a06050307050a0806120a0c09061403 72
    0x4200a5401c5c9805200d020003800018551104c481550b818440c00c0c0100007104500881c4050b621303c0e00824005220b6005003071505650003215150240f401005480380111a01c48c2400d016280071030225410f1180b1a09100e11400080400c0901d8428108580d49c00c110a401110842c01c1c400c0c41115030788002038412a8800d070070030400400c503040a80c43c80b80248568180c01c1d400801c880c2c0095a0700c6a02ea034000c2d5000640540340d00000b90800125001d5405501ea46a10100020300031540d91010282c101c401030050303c4400324180301d5600100a01c0e8083d5042c0e103001c403810001c0000c89015980140a54119140e0408200d80c0d189415415444040e01c59080903640d00c03200e008981c029a031030103000f40300b00004280407081041e6030990410a82c800c1d100400009043c40c0904100d91050b0983d5403801d00c6c04100315000d403200100034000d19005070103802d09642140e02045802403480c0602d81000542d46000007104c00d5a1307a58220010307030480382c000c4140780d4400154a182d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 915600125 1250 915598875 915598877
    0x32c0d180303031d0307050c03010e0712020402091c031e0318171902060103120305100e0a060b030103060b0301050106140406211e050603030702010801031103010b09150108060d02010f 81
    0x4444a007120752075181160b480070130340313180800a03041c010000002101c0000c4a802d6000b4400c0d4850186929212622403080f00c2e1010112180c1c4001490941e0051110350002445040c0c00c010507001140c841c2016941203000c01e0b05100c5d00703140710403004c589450110365490240200c100c8210801c120000d4120000c04882c14103540b001498020b00070303101020341e40130200d0106e4030351210081d907502c1c080c4016200c0c49045404520010303c80e02800b4403030043d9a5500001d02d280085101b03444c41c0050941d03840550742d0002040300203d40c002140214090300011512141c100d0402d800c4560692124003806030042800000c018400c0960b0201e0300a0f050115006032050078240c8500c01d000300d002e55a920302403c451400403404985480615080020085070303403418249a500e00c2a014041d004c41d000000420010b10707821300052a50a000d000401c10308502c102144030000300356000d5102000964052010396032184503c1e43c002c0c0d0803542070216000741e8001031300ea0100e24038448 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 915601375 1250 915600125 915600131
    0x103020a1712030a200f121806010303030c1d010e10030e06090a030f09060503061002030d0528050f040605091213180c0e10032c0d18030303 62
    0x20110203100b0303005a481184101070f80c3c0e260000d0820001d0052090300304461a20048441d9110314400660304048210044545407c4c980d45200020001c0280b4800c0000381900c80040345000900040c0d009610a03200441c0c1d0b8444010040e180c038202101c13641c0c0b13494020740154400c1e03a002003903900001003503a078441500c000243c210058000c071100388130035224040c14091500300000b03900d01480d010b65102e000003d2004030842e003021540c85080300283c400d0000c00e400380b410000600c104081401100d2a01102003500c0b0182d402c2280c04098003688a05241c0715000070062111020036920801c11180c80e010041350603002c3e000d0405009140e03680c000500c5a0020800b40c100e109100b041c0c640c039003079540c44016441e8414002d010028a2842408004600d0b03401807060b03c142d42e481e546400011003007800345031260801c031a0f04254458440407491907480c1c030114400e0b580b0780c0589030300200c27040032685000003401e150001c02070700c43d90254500c2580f42100e826607a01d45004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 915602625 1250 915601375 915601409
    0x801030201140c1b09060a0e0609070903120207090e03040b040e06030307051e0c0f01050702010809030d0c030905011b081506071416050a081f06090608071d0103020a 73
    0x3611403800b418000018911825880d050700c08440e60010140744d0044030300c59500d9407503401b441211310461184a001c1408000404c14034606031741010342c4290705251600c0d240303560303807a40311401c802c030650040560885c10702889408083e000b0002050400c8000354501440d04c2c0c0a01030300d219610402c05a0b485480108505503020720880d92035a03040400c603440c081c07a21708032882808224503404400c0c810280c240881d4242503d00401d000c00c141c45203828581c03140c00643c0c00c08401403400019020802c10444003201c1440746880e00c89842e03800080f03440c214680a42128601c0b406890401441703082450351503030110803942e201c05002c01c4541000640e10224a0a0140c1c603001803880002d40c1305840c8200002a0009032421600d025580b626a503a05002d9003210700d00a650180d0841c1502c00d05c00c1003424541e101c44401030382c0010b5076981e6600207408556403078109030015008481c08001040c030807114002601c4040c41742031955451039001458501c0385100e80f503110070b021208 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 915603875 1250 915602625 915602657
    0x90512070b0a0206010608160503070818010c05090909010510052403043002060c1303380c070f050a21110a050706030902120a0507050108010b09010801030201 70
    0x580c000420814008075201e5a40050203500c6900034021800024040310004440d0010300340c404000d180903485051550704e4803c421200c02c00d000304043d0035151140350365245103400748690ba550503460368840b911589194100180b20001420800003a810402840010b000214203031089172001c6803c0542948110ba5007048a4101030390603182200200803c0188055406a40d107140ca0b10103d4950b40c2d424001c43c0944140c1d940120310050340a4000280001c8181009105110b448484c0c03000940d0b0b40d40d21243c4000307010110b18245c42d65200072800da200b00c410388001d6410000e002206516103560716038080c0c0506040070301000c1440111405004d4180500e402640d0400c074542d40580130030840044450580014400151fa003880c400c4952002090000f41e269006020302009480c1c100f04038090170f030b100001d9038404600554051411003c10080c10700038401c0029144462403c0000b4200c048164004a03040804004401041e03a0181000381542e0742400c02440da00d8002c58 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 915605125 1250 915603875 915603883
    0x27060f070f080609010e0910020a051306030e0c1909110c1911221a0a0b0f1602060c030d0501050307240f12020f0c0601091103130515150109090c090512 67
    0x1d40704400e948000381107040503903c44010001100c124233550603540e6103100c110101c40c20060100f00f1078010b900c001c0d84c0340ca068460818807441f0811082c01d841d444000003802c43e040310300420694000003e0322a07441a051040001ca420740c0303c1c0c00c01c003526140e15202060091001d840780b0cd00342491000002d2452461060403518040108120000362a00c03041d005051945013148260a00136000903828141000c03200420352006150341030405280c0c68411540c0c07448170881c0d00c440107106500b03ea51080000d4040c4003001d1601082c1c552400e0705160404c1c41c00d4000c083d40c440c41501e6881440c2c00c0d6400031491126600c0d2803110710a03a05400c44046281d0b401c000c02d040e000052002030301c605071000d400414055416074020740d0707071042d0040880311003019070140440700f4000a07080c4246031070403408403030281040e00c02512020a125a403454201e4101e01204105181e201240d40d0000728040a040c0011003044180101c00000d4403050061081600c81d020300746d000441040240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 915606375 1250 915605125 915605143
    0x30d0c17120f0925030f0203030d050c180d030c0b0a060b04120308010b03010312050c07030c0f0905060d0201120b0f041d06090a030827060f070f080609010e09 70
    0x8148603540b4280101e810b81100001c1d50791050a22030034008803400d030240355481c0035420800080c82645482c5039034450050f40400c20aa9160000340012005014107000300d605c181c0d00540c0a9565440741c070445820001c0b5908840d0084d10114447c4001980140300d2405498211112a2040e0741d103c100c00043d220760f4120861144010031b00054044000c170520303c080384242c031741c020b030b0381c1c0c807038038030280b18082448040c0c0181d900d0401a0351080c06403008040d8208075100b074841c083e4480c1c403542c43c507130069408002c852698000070003441d030301413003001d8102d0f008036000924003038540c0008203105001c0703c150082c265104864421a59090a041c01070384000d88140550248542c21024007840c0412031a9140120400100d0f0005c02041041c0d0050f490b8039038928984a4110040c0040f5117105240c140c64881c1030200c001c100104042880340c3c4524002d00c83c3c1c0c0c9000a030041100507100d0241080c4140141400303441e5650714151810756104012940c1d2995481e1003261400c1c80d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 915607625 1250 915606375 915606397
    0x60c0a0503040224190c080a031e0228030c1d0d15020d0b03160902030720010b031216110d020a0f030201020d0f021e2503020f030d0c17 60
    0x3100401c0401c0e128000904003d01c90044845500d40c0d40e14030541d0b03081c0c9286c000800000e010054446454001c6d44400e4000f005080350500c09014424040200d07803048940d130001b840204502d03c036104442440134460008c0c1c0c90180f041c60100240900018030700c205d403011406480c41c1c114151380f500c8210403440c0d90004002d031200c03050b00140c04003c1d804000721600c07880c20009a0326190238000340d82c01d04a420b002e0350300304540c50008010001d4102030081c0c401c2107410000c0c49021000d0224044011503028000188091003104041c83c05903241c0a0200e4400280540140d2107842c610040b075143d0810761440da441200340000302441c0100100030b500c409082c1e404210150402070100a4910030703001c56110f444207400545280e0400841e00e00141d02400d46112507070700340c1c000d42d98041c041000300c40d1140f2194030b802c1000804101c404907196000c400030820740c42e141e0721800441703c00303030003414150209080040081050304070180204003200148882008000c046500007148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 915608875 1250 915607625 915607669
    0x50a090606020d3212060a05060d0c09030b0f0a1d0307080f040302182e0314070803040b0d0501120215070c08030a0e030f06060901062d0c0212060c0a05030402 70
    0x3d2940440d2034001c50300345c2403c01a118000b40e09402c4c0502901e0903140b00900031030500c007008000344040c0c011000c000c0300300059400b00100080000302458050400354442520038940340ca1088201c03004140f80c40c0c840d0b207101c690b042060602008a9038600d801c121543c2d51200b048004030090f104603072000790030145080305454040034601a030750140601c006810341c6404000408101d090000ba0000d01404003a00104000781c00d02081001400c2940c0035524010750301e1416604640095000b956003203030006001540d40d84600c21320f405803504000080700a00150041200c12240382c6021030a548006503141c207101000e644480100001d200b02c03560b403184071000402041000540301d000780b10f081004004501e0116415100b103001904a81e803070b82c44c04204840204004244035903110094164490011600000440804903a01c3e40c10b5080302902c1808400c50500540030501d400c0380d0207000501c00c6072400c5a01e6039030b0074a419520394a0f140002200d480d940e942490030301c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 915610125 1250 915608875 915608957
    0x3020c03011e0f1e1b0c030e0f042003011401170c0a051b07031104091109060d020a14030c0a030309090515120714300c0910050a090606020d 62
    0x1058100c50080742800d0184285000e07a005c09a4803440c01043c005c01045090503a00384900b08074070740b80000240200003058404826000b40c05202001900c0a0103290000061005020381000750070092800e18000d407080b001e0313401e85021850080d040c1249202c0c005200b6924a200301c1c20b0303640350031080d000c207032401000300c8403540e4840b42440f003118408140244003011380740501c52281441d0b00070403040807000b255010040400001800180d00040c00164800980c44030300885000d805030404101000f14008101450324402c127408512030002c00340f05100103030b40715101c01c0c100d40c0104804100e03034641c40340d0540e003114010f80164201c0141244140c10500009507001200e9084c419104070080d06400e120701c09440744250619803145100300000d0545136111042d10552040540369250b881c440001c80200041d5440300340402c50300028081c0d841c02c120401c00400000c1004c00680e4541440a502e07500d0400d603160601c01010150082101e0402800711220303015040000800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 915611375 1250 915610125 915610181
    0x3050f12190c1e03030606030605031e100e0604022407140a1202010c0e0307080a0209060a0803030c0c12040e060d032a030e0604050306130507051c03020c03011e0f 72
    0x1144143c42500083c0c14100002a40f82c081d1142e241aa903018006d0800d00b40289200d001c00343c5070300d003443c4040c4685051059048600c0c45180c0440500360050701c0c550800d401004840840c40002c02c103010460a4940e0f90152401c0454400d55030144042034000c500c03071080c07802d221403050003520044150644e09151030741988110452601510790512199000c014142d840a4501a0480d01e9000300e5000c0d0262424624261303000e00000e00f8020701035110010301e42150001c0c2d821852901010484090711380382030201a6514408445842c203180ca4403000340c60400c0094240d901a40e034400484090510543c03001030302c00c4815000c2c860707101ca04012102813030400b680a800007004094544064500740303084a0444000500800450319400415070310300620705000c42321882035140005441c0c4502c0c200b1041d00640e10790fa91031011103801c019040c694070b1018184207074035044042400d1110711458191200030f001001840d49e141e40511300c014554080841c1000c01901d020391542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 915612625 1250 915611375 915611423
    0xa060e0c0d0507090608190603060f1e090c121a070e030c0a0e0c130e040804060801090902151c051807150909021e030a050103050f12190c 61
    0xe680a25002c104030780c2ea0032421141c5020502465001400c00c801060344489441e0680102c41507020002403c10303900e81d5128126402514104c44241e214a5020030849840603c07001803212114148008001559001c90000560042c2c0c0b040d00701504a02003808541540d8031a0440c10300f8254240f03041c640c0c0041c000d00700c1c2c801043e2003840b0300342e1800217500340381072080111442d0103074004c11511280e00c05200ba800c4140c414491554017a00061440b080307850480c05075000d08015652241851801002800142c2152200300d0070315414a00503104c49a20008400309440e1154079032a41020000701c02d111840c10a181c9401c10b418002100b1100c090707800301710380240403110110b5460043c400700f95100c00d8020301090b8003a03010402c0c0700c000c3d0003d024006103c075600700b68040c0c040344403542c1e070002c0d41c4402d81542e07076000600402c207003003100343c1881040f00c0090001e00035440010340148501c009420b1a100522580c1d0703121401040c205040d25409000a000c0040d040710b04000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 915613875 1250 915612625 915612637
    0x4030504051810060507050c090721020d05011a0d05070509030106060207050906090103050607080a020d050106020609070b0412020d170a05030901141005061b010f02040303260f0a060e0c 82
    0x14111008001401d030700a50444445547c4400075020386282d80c01003100c0460014040028012046090401158080020a041c8184500060325000072884950032140141c0003824a1401d00080b066221002401c0d95041401100301007801c2c6d88e410011a82d0f80124072601b40c0560a01501261254000c00c0c00c3d8283c0750107983c05a025941c030010894010030030702c40940180c004c81c000c10b83c018802d00c0120340c0700707800d210054a4100c00e064440100c403000d03801440103030008800e1202020040c000040188000b003601414603083c080d5404052000d80380c000d100f840c000d0b41d000b041101903804003841340d1302405010703100ca4170303240d02612a60045a00039015440c10991074424803030513000c6409000c4000b1100710f014100010300c40d04d1b500c03c00b00c00e04030568241d11448407400901400c0c2440c0f0b268907000d43c94510b50301d00540001114201e138482c2100d210b900000a010640c4041d5110070310b81e030300b040d05440c0c42914000810050f0049403c41280c1c1d410440c0e9681144002e200d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 915615125 1250 915613875 915613891
    0x100902011403010302060a0c030201141014010c0818040e01051303080109060b0306040c17010b040612050609130c0b0a090e06030a0b2d1f1a0a08040305040518 70
    0x10381c036552000c0200c1144030901009502c40401d1000402d210304c50318a000d0700b1882400001081061180100c540400072144c446103800240018040c1c801c0c1070701ca040142a0070b00b45550280e06607a2550454068084001441048404d00e01e4255907280c01508012200c4402044182081e4641110b230700e01c1c1e07400c1940072039a220000141c011a51044600711215690322904680303807081040090800d10381c07501d08000c02429540d0507644500700302d60007001852040c070303903843c40c10801a091038041158429064500410041d10f0380324001703615403051500082040400061405903103030303545900301e44a1440c010030202040c03508101c0d80c0c4291a884881600075a46180402d9591000158002d011400000200f00c84080d4031003110280c2011f80d0b44c04070301402d4011412503031402140c60141c0c1c46000c418508c19840285203400180c85180b0121070400440144841e040c480c581d92001080844000941418494800d46000e040001c3c46112099180e228085500c041031701d0a403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 915616375 1250 915615125 915615137
    0xc0e10120e030a080709030b0f1302090a0617030a08010b13170a0c090b0d17041d04060c0e030d050307210c020f06101712031801061e140d0510090201 66
    0x54400e4040c031b5000b001c49500407200d00040e9160252502105c0000d0211f681d898800e4182e0001a542c1c590315900c00c1824890000d4182e15055550212141c2c00c01b200005820400892885036400103203103065603290700d1001e541d40205417412203804035a07800022075105009806541c03910200d0102c451901407600c61a40c50f80b506040001c1301c003010712255006104810300400180000303500302054005684140c03c081c0c1e101c4540514a9241144501c080c2d00d84040200f00b124a03c01d0030700c0b0101615046e464864020040390f0394021401c005014800b012002030000e600c40c503e14503071203550a041103a000310703028218024002c4420f0400260107181c0140b0b01509000410a2103145200c260210b0a07150610090078808143e03000c09850145d500b24074205844000254003409800155a817003103c18851030b0300f11101030308448180f402890341d107100d0461240c484c1c07090360340711400e0b2003204040c03600003403001e02010802440d50240d5074080c4184840c0c1d9001100d1039000303803208 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 915617625 1250 915616375 915616381
    0x8040f050607181e090b0409080a0210270201120204031208070225090b01090b070318060806030607050903150907141507080901050d021305130c0e10120e030a08 71
    0x448070100007400c40c0c1d8641c0c1c40300c444c01c000303081081c0c00c01104d01c68017420000d066402d80c0c54203289a4450f610410140e402512021000751081c0703d440c5009400f51640e420102a00110031001e804174217020f410007030701890b0461100001d5044400659000c1a9501c1801e0b00c00c0c80600865412500d8502502403030f5a0598034404040310000031070140146d04948130300348054400103152445440781001146000419920080002044120b01030f44070100c03c60640c080e441c0c0e0300305198010100f041081424010300c1d40300000c24a4102d48075003481a10b502104010a00d0411003c0302c2c50903540203035090100450011800b03000391505050341c1d0a18550700b80038048140320494080f6200c80c001c0202002180e4020007800340084145410fa14080d82092560142d030452044404980d110700410000d0b4505010034480340c000101d810301c606c10450002600b641c901f80011030040000d544d82034403180c40746018140c00030f5002010081803d90701901176990b003146101e1000702c5e00a40c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 915618875 1250 915617625 915617639
    0x3050f0a020306091b120a06030c0b0406050a14070b130b0a0b0609190e01080c090f0c160302011d0307060e060105031b0f04110a0e15040608040f05060718 68
    0x3100e200720f03005080101252600c600c800d514000b080703060300405c0418011403a00c40da40e002032502440c00002e000c0744580c114181019041c1c401d0380211056541088100800b680080c00c1d50482c4045090403440415540c00d403070941e1050b50740040c0a00038400801106c1c5101060041c041c0b4016000001d6941e100140c2b02c0450300350106895116105012504061406540c01c4103522802c03080150000d6599500000848003a004050395400010084403941848511a41d000c105840304071100c1c14004c24034a028031a03101c0c00c91441d44000074181c1810300035000040b5030981106c418095454041046490f50403102c42250f00c0340c00c00050f207003002c0700014818103a0710000c01402170004071504c050302d0304040c40030103500300c20440380500c032036940c47c45101395a00b09030b4280790741d64001440c002c203910250742601e0b1255811168060102c45e0300c10035582560f509040000d55503d0710308218a0240c0c58110040c02d5200d120f040060099200d041c01c0c4044201121800c4269100d00c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 915620125 1250 915618875 915618877
    0x609150b030d12051503060f071106010f03030c0c0f061107090905032208070b0304050f0a03050423090408070b0106030911012d1107091a010503042103050f0a02 71
    0x410b8000141c0308002850100503903078002900081d48080454910f0b51040100781402400c40c1c4215040ca100e100300b15035241c201d02c10142c6580c600300605915814826005420134890001400b003002d00c840b038404000c8201980405403e01684a03211a6507a0000a25641c10801209100c4c0a21800000c11038141e01811020302c1d03124002d1820102a0713080c0e102105d0390406281c840403444240020b06020501a50000d0700d0480c0070141c0d68a041c1c1002e0345000e2010000c44040e600c548860408282e01c04240c3d020b440e0702422001c1150890a0085e900d00d02d452a020340c840d4041c0148410040001d0040c0081403007211500c0040c3c0c1d07074102c1a003c440e00041c3c0a0b05000216400f4030b51f42d8412603151412040e40282d249c1300384101c520b030750188141800100302240015610240f980410411140180903a0381d05111f22007042145210710300139070220313505005001c008a030801008144581c03014404410b440e0780800c110500501a100c1078518030381c0c6241c8100400c0040d92280 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 915621375 1250 915620125 915620143
    0xf05011d040b060f0a240905030607080c0a0302090303180a051507081303050a0b090606190b0912030a0c0204060f0806130201110102040602070f0510080a0c0c0609150b03 75
    0x1110035a00750350340f40e0070710403a00181c0020035445031040360003103003c2003601c41407800e071416903a00720a4050055005040302c4540c1d0010341c401e80c00701c8108880b044d8040303401d0741d000c20381c1d840c40d0751210319050007540070f402980001e80d40b5000224411640d031400580000b94050100c0302c14001c0740c2e42d2000e21003400408600104080f004101c42d0000c10045070041c90f080c41e11507268002e180c0c3c1ca4882504107001d04030100d60880b040b44c00c1c0840d117a0208407064012001300c070301e5080c0095400e20724a01003a04c0c071800c01c0c05040880d00c600140c3d12880c000e28602046003d89a81c4e5076028001003854400f104124421840d02102203a41c03078142240c1025501250010718858682a46002c400c0301c520600301c1c10018a05244000035000b0700241004001c240c009110003814462144190045900f00d1350140c0c104400d480c1c080390380548200d800c024500070010381d90011603011074100b0165100078003082c0c00c000c2d52004124555840d02d141406404080003540040e20815440345115 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 915622625 1250 915621375 915621383
    0x40c030b0102061302010e0a0902090907030507210e0303090304150302040f0513150f03021c030f230f0a030506030f0303010506181c05150402030d140d0f05011d04 72
    0x4400003070884c845020035800428014140a4207441c0ca00c000201e40303006c0340c1c0140510076000700d1030390f983d07060071103410307400c1402801c00307024501c4c0490300184107114007043d1088450000440d0b584407007855000000d003e400c00192541ea24000c2c06065030390340184100c0f03440741d490f0002c1c0c2c1041842842030310103645150256481580c80c0034208400c10383d41c0407d08200940c1d9091a4010440c1928030710001c0203048500e400c00761440c0104000718080610540b900c581d00c628580009a00c014501e6941d002410848040340102002d80400d40340307a5140d80114a000500c07040c0c105440000d410941045d940902c040e6039030105050b145d140c0003210b0545544144014065890b000c0003414008000c501a0040c03240d103a000500488000c0c041007200c0c10b81502c8203010302c44180401e00100d01148405582802c2070b40c04250b41d88003403d407020400624200d203425600c0306d8412240700325240f0b00c0a008640001044800924007841448035640700040d0004d901540501101d1045800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 915623875 1250 915622625 915622633
    0x1002091906032f0904020f0c07091e0510030807030908060406020306040c0c05060c030a150f030b06060f0909220303051909030827030a03020301052d010c150911040c030b0102 77
    0x1844c000d12001c1d400c60440c80c2d0ba0740006014241c200a400c124003c020003005a010070707083d500a50b6281e4846942000904160a1400704000504080c00c1c0c0d170200da41c00913055590300030505045455501d01c0e08004424054942404140240c2d5005140200c40454080000c201d01240507940c214000b00010602c2d00403070001403055460b40b014503440420b114000c5116070074210448860001c1d80c1110303004004105050082c00f00210120b588000140c846900d130200503003115495005643c1c00c03d1248603800c0c0041e11040701ba83c0c9210101360308440311803c0400c6498003034041c0208543d80c590840400803240310b592454000d460200b50951034030107442d202c52514451440780c00051201020745d46400c001c060004000502040308a41d50040c1c4035414001000482d643c544240c0c4848502e2109000078503403910196400480e00b401e00c82c0e09003800d807411004518641d61000402c920f0a081d420510a480c03070300043d000300442d0704000b140d0a030101941112100c2c5070407401644 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 915625125 1250 915623875 915623887
    0x60f15040504050f0a2301110711010918090308221407030804030b0f0a11040b0a0c0203011a030c0a06021e03040803040b0403030e01020f1002091906032f 68
    0x4081e4425030700140180d00b40c07441c12281d48078082c50484006402c546180150098142084020220035420102c140082c88503500e640c80c07089190007901405000c4440002c40c3c2d501680c0030340c200d00020040903042d146002214813444006040240080c3e0100b41c400c00010400f0300103d00c500c00d241c0c010039178003d00c101140c075045c2d122074405502c141e0130712410f03c001c00850040800762000f540b00c2c2d000c5a201c0c0c9408000f280316401d0141800c10100c1c246943c0e900308c1c0d0103505c02d03a410396250320720003031f01c03000030180c203c2d18000030003c06134155180c41a0800988600401040c410509404031034030540b80805010b040809840b1b12001030b0450300850948100e44030880980002550131241403a844500e80c3e403e50b40560f0160301c46210004041040582107070201d0103d003002d00241c00c2e120036010407180c4884400550400e60741e170004550086a898610026140101501400e16542c031580d02070002e100e50503610640308000c1303101c5a10b0400543d807040500d041315000e241040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 915626375 1250 915625125 915625129
    0x7030b2706041e02160b09010c0f0e06040303050c011d0c010e0123160b1f0902130e1008010908030a05090303010b0f091201092a0506072a0902030108060f15 69
    0x90040301c2d49900800d004d814220200e0140080d10740104215400024144074091000e46842b000303400b00c40500035070b010000b0340c59503081b046e2001c582e01030a045969035650340b00d044c01001000b10303a14071a0382c84103100100e00130010b0305004d01c0c0d41c2078941c5000e410880f0015a01d01c3d02c20300307504400110b20003001c00c0c1c0c01d54000191005542c001d1022450100a0350703608446c5400300c80c07200714480c081206115003455501080018400b01c00114504295034401110700c0100b8040c140740c1c4503640003c01c0314120500e19650091101c44020040001f0030310b02600310741e00130307182c800f4910f051202040003400e000c42180d04031030301c24804901d805070201c0d2020b4035405c16440168070002d2801452030741d160a0003401942d034801d01c040c88101000e1101d5645041102406108000444009118a48840c804c80f080150440c2441d10501100c1c054500142c800c11520301f4003019110303001541009a030060341c107882125054a440d9515a0701c1c0030120a021290010f1406019810003564 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 915627625 1250 915626375 915626377
    0x2505060c16171b220207021503070c030806010e040e01051006030212071407020909010905060f100612150b03150420030a1103150f040605060301060807030b2706041e02 74
    0x2140740503041401595144204ca0565011400c03c1003110307800003802421842c2029805280d15807500d41c1c1400d40c1000100204010681740004060224031000310b8040d0780510400303141c00c98010302c288150a500c81c2c00d140a020291802c04001800704000b14826000e4004c3e651400071840c181d188562b1103510482d07903c038010300082174082c0e08103c01005a203c41462300d1080b14410001b04c0d00300001d182080c64202c00401c10150100f80100340080d04284404580888260380303850040f001c0800000d034000e10f140128800c2840d0517541c00503403900240302861044040b400300e9a49800c03000240300076100c0109140c00e600305400c4845210600020166810420714503000500402d105020f04c0035501c1600c0e50a02d442c615486c20b452460f1500c50000c03180806c1c0d4050020515010201d0954001030140200744802540004c3c001d078030950002d003400c6002031850003210101d100001107482055004204549410005000341c2424000e03d14004440d10131090702012881400d002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 915628875 1250 915627625 915627673
    0x80403050a111e0c01090311150d090308061005030c090d030203130f180e1002030903130303090303031a0d080c030409090b10050306092505060c1617 66
    0xc0c440104100b0b502100d04001100112041c08039154116904803011403070800c103411101d04001104c40d06000041881a428070b4080c801c2e141280a203000e6400101c0e140a460f1300c1002003841e000300709040c90b03400a1064050f03141a10380c6007641076001022221031000300c076a5200d07117a080001c030317009007000807003d0205e60003803044e40c0c10800590300700381002c000c0c1c1d0b01020f07040494600c103010a002c4103580441e03181c0c02200401198410764605a11202480b40642810b980440080d038128024402c60742040e04a0a5014903162039190281807260503020680000b441d10300201030301c030b0344066404008640100b20040d13024050760341c2c11541d44003041014840c00180000603024049001e01030700f80d0f224409501d0b8910703002c540c1d02e1030700003642d010b64030a034004402c0c003030518400700340d07064200c3c020f10700400380e400c0c2c000d12060302c0c0345e1170b0740302a030070072070004da4960b0340700d030114460a05241c000c0f002400903030398000746005188031906400c82038014114600d820043e505909071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 915630125 1250 915628875 915628877
    0x6050309010930020a1e1401021c0b0f0f040c0c0209090706020607030207031d040e010f0e0c03010606120b060702090414100501080c0108091203180d020304061d0a05090a020a031b080403050a 84
    0x8900c03030450b607020300ba42c100c11b80100c010b101c901132030201c80c00c2c2070250b00201c41081d1002c6542d00390321000a2003140c1b88818040c099907582700cfd1130204500c1403100c1425560090f0101040b428400788041d61032000740328200060148034080b0b03495610034001c95028540540c1d03078a646038550140c559501481d8140194450359500c04a90619000e002e44d07645c0000c0c0d8440040c040d120399910505140170021100c1c4664940041880b220781c2003400601c2c1500c00e40c00015810f0035420200b030451041d000040d52008404c3d0403c410000d4406032001b09070400310035210701c108120402001d5074001c0c0035140c1207801c1401d81c6006035114a10040d40710f0020011261410040701041c01103500030b03149119107804e486601a802d080c00c1180800c14422840110700c3e0628142000b0310004c10282d815521f03120201c041c8102d65144403800c2d0140000078000109400c1003031441d0b0080d0b200800c910302007428003ca2411098409200ca0300c5411a5121250f0f95511a51304643d10340c0400c034628 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 915631375 1250 915630125 915630143
    0x210f09080d06140a140f130b01020606030f150705160809040b04060f0504021315050a0f1d01030b030c0306010609090b1c0209091c0c150e0706050309010930020a1e 72
    0x1402540c2c6400c0c1f90f01c40000030010010340c05050000083c108000200160f01992261995075420440094081d00004107100c410340039440740c9408480c00c0c440c03030500b100c40c401c483c032019041c01603040007003040306411079003040718550038428081590a07512440d903220070390000422460400360000c0260314804141c2c070340240d44030100341e26625030a040c803800147c40441c40c0300c505d40c5c0001940c11511054105000d4004030010381a04950f81d4107541c504142c0c9980d00003c0c42e481c20410040c01d140024180d490381d40e11844007c1c05803915200c0c2c118218100142d81e0018140340046009442204005081900f00c2d6024004000701c05852900944240c00134014031000d030303002004074401d540d036904458140c2410301e03404041c0529180c01c0c1280c6010ba0300f4801110004940341120010305205440f0741d00d03020050300500c0e000328054940e2a00007914200e0b03440f201e0140009000d9401e40c3d1b0b82081c0781140c2241d5403d00000000e00327000340112010010080301040380104c5115403021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 915632625 1250 915631375 915631399
    0x503060a052e14071a060303130b0714150a06050f0a03061a060d05060406053304090207060f050c0f031308091206160f210f09080d06140a14 62
    0x40746a6841a07100f601c0c490345c0724a021600c60031012105420420450085007080a0054070020034801d91060304055103000840da41004a00220391038140c06400c10703200d801b41d11203a54150b200302241d207a90450303d4004045003038585040726901c0d5990103400c219105055507505401007940341516484406031488140712541c4000c0140b5002c4403920002c41e41c3d082280a10056507000e400c6503104c3c0098111071551100701c0d98546e420009846d00a4000902500d07101c6801d1260380c0003410440e000140c002d041c448250440c1402040e07a220070071656568054100c000d0086061700003170300c80c08001081d07001040742ea00c03440c0c0d60f01420034180391010010004244142d104810840c0ea0812010065a030007500b03461b404009003410041144541c040d001000490340018040036010000301000c007079101d96204d44c440501104041100f1407003802d1240d801d4100804404105013070481c04102c0b200d0301002008900406008241d81506104d28845985401d04407541c1241c110085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 915633875 1250 915632625 915632657
    0x32c011103041208090a120807170702030403150513080c1c0306081b060f0705011d032805070605040201050d1103090c030f0c0d031b030503060a052e 66
    0x254055845500100c604403910940600704e61001004070200380c01c0307010b42802248400b1100901ca0015142c091032544d40c410003640c9505814250f5010802070004100b18036030000014810340307020f03031000c1f581d4504640041c1d0a80b034088070b44500400740741500d07100151984000e040381411031002d44d00700c0c600c01c030080d40200e0b800701010400652101c44c10044c80000f40140110002070718203807881c4141a50205100e4402d0702d902c002f0350180041e850050220030740c010b4409a00009a5103000341c181c1c2c103d0381d03982d00a200a40c0c18507810811440c142100903810b500220003a41f190340c18580280c451034000c042c0100141e051080030008030070000741c1c17407041030b5404161482080c1c1b031b418007440302c030700c3e01c041d5800300c0313000307521003035034040c10000001c0d062a000c041210500001c5200e8542191040b40141d208140070106515045c10540c010010703500c07a0300c00342d80400c00c0560380c00400400c0b00a4100720428140700c400c016941583e124061408000039050080c40600c1001e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 915635125 1250 915633875 915633877
    0xe27071101110a031b0e0609030c060c0105040c0e0f06130e011506110c130b03032101030201081e04060e0705130e160f0b0d0f0c1106010501032c0111 66
    0x1259412909001a903e01980e4242c0308aa60310714403440030840300c1044000103807070b82da04610524420600401c651501d5030b01080303140680307031002d00140d8680b4116200503019280a44d4201ca0b05070710b101e0089288ea10190b14107100300182c4014103115100c1c2000d1101c00f080854540d800a40c540b030141050350003d002e20103415014200008084d0315210000703102e142c082510407420303003201c9054405c9550302c280c2c0c52040e0780022800202c05054030300007407852042c1813081c0385400aa0407041a4001040d4a15040340d000780c07240070344c40c0d484c46034904014052409200c1d0125528001c900401c4003075204100003200718084411a0751144009840343d181015140340e6203803904075069070b0110520176402a60b00310040056140c0c2410040138402c605802141e8202c400411310601156880d00000115642c140c010801880d000c0c1004016560b05001b8002d24403540c000004c455200388a0007144103083c80b0826044042c10240d00003040100c0d6010000d503490311719642c806042e02d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 915636375 1250 915635125 915635141
    0x160309050d240506010210020c03041a071e150e0c19090b0d110d110607110f030a12030c18080f0616140304030c0c0e01060e27071101 59
    0x108681c49034507590305140890040041010060b80c0c10041803084a036000111854100c0c81190050784a9840c00c080f54a107014130342c05288440d04644429840408420040c50f40c58040c1070b540445080f00c00000141c450399450007040e2440038140000c903050b96038400c18500900038180c946030b914840010b00081ca05200301c440786480d00a04002c105058851810303a03182c02da03295602c602007601d46114001140d46038030f001b400e20480c0f500400005c00e4940d05114001000941c41e005c85080c40c401604284074030034018607040d07406134820f280008002c0c01132540415114807c620300e100441c054001d2100300414460450f40381e0b44606501303c1d100c1c0c040c183d094018600201170821451034100003030304460030707409088862040a41e03c0b040d40a12003490340c0155a503510303245000c42e1609001032015140103940c0402080c80560303414818101c8085994540c042100607081211010100c00c0c200b044071045641441d00c040c8a03108a64000e080b410081c44a041c1e41c0011403e40d0094 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 915637625 1250 915636375 915636383
    0x100e03072a03030e030d0c0c0303081906060c1a101e0506030a0e0d1103070b06060f0a020c010f0e060414010c02031c021203010803090f06041203120b03060c160309050d 74
    0x10b051249014201007105c06d1861202d858540c1c6850070540b1072031422130590001a04018607040040e4070811400007005810b000546c040182d0380e40d4041c000d100c1c0c04044000c030340705981c5260394000d203079102000c07a000c0c80f9602018600e41d4a0003101d4000300000001007000400450f20014540d0382e160061031060600c0400420407002c2c11440302d00b41041c0c00240414066a42e040c81600c0c8400010765031a198007a941070420340329180019060701500a0b034014404c40014918255a400300310080765400a032100403000c01c00c80030584560108005081c1c1019007840100403504164a08010342101814900b5020b00d49402090906040c8040f406000240d081070031989541000000d841c9171040e8034090540d410308000e00d84920030307080502c0c41098006190f802694858044030028034001402c404000f40a1501408081d221194144940e00d0002c0429036403c001c16228840d155190b0801d140039003106840540d5502c04500382d04002c581c91000c9116201c030f889080e0182e002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 915638875 1250 915637625 915637637
    0x109080d080411060304030212130b030a0f0e060c0a0305270601060905010816081512070801051f0b0f09060f04181b0f020a0b01060f02100e03072a0303 67
    0x441d0500440c21820300f5680c034000c0c0010420000802da010800081c50350070040d100c1e98850700600e0188207042183c02001d0b84260010038003000049a511080701403641413401d025036000180d51a481d81c4044900f42c000d00020000100030070f02c284d0180da44001050882c1d144440c00342c07001405040503807251800c5030b110200500120ba00408804d00808003444d090081e4a072640001d002e1044a8481c4024420450003040c901c0351a0049110314803006001242d002507901c5c0700a55440142c40f403c0c48551034600412142c42c480211000440c01150030300c05039500c0d101c5034103030315440340b4a81036421100313000240181c4d542200518201e9141c1120a46842c10403500b107905020824460201c0c40c5410b501140036840091088066400c5040100c401020804103a05001850000401002e601c20000c51203a0300502c6c0c080b086035444d8215003042d0807a40113042110b000d85a050280d41c000d000400c002107a000c6d03032101000001c070902110b450505100484040140c03c1240800c007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 915640125 1250 915638875 915638881
    0x3061302091b04090615090806010f1229100f0b0712020f010f0b0405061f030b01050708040801090c0e09030d0506180405070e0c042301031b0216150f030b0109080d08 73
    0x2901c5040d200180c41c0300c40240002b940340641c2c6044070807040c032a0050300c1d40401201c0040c410b800044420200c50034040309000e04213148428020b690440d01340302901144400840c4210200300b44105480550100500e000541d0f280d00e035096241c0600d0404600c40c003104030000340f00a01803284480b103803000218801424004020540e8030080c0110302880000d0354805007204020719008a50b280390500140c6071038102c00481ea0f038859060054000c1c040000c0001e1f240704154806c2d82070f5402013030301d5200341d62103441c050384001c02035500b6802d592047c86a40c050301210b83c402e42c1c000c40018a190424543c90006110a54084606035104d4015100801161030700d4103510317500c201c1801d440c030b14240c1003500c1000810448041d010380444084103d00c5941d020360b01800e01d004201c0401460307011000402540d40b4070503e900307200c038030a00078002a500724216070030701e00e03250326260b41c003101214607000c07001459583c95440c10001e603844002180c900910001d0580600c030b665640300c80c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 915641375 1250 915640125 915640127
    0x20a03030c050105060909030d0f060504091a010515220f140307080106060215150909030712080103030c1119150311070201080f04150f0b03061302091b04090615 71
    0xe20005d20f0a070180000364200014031102008035400c08070b0960000580e040c0300742010004001e5504a140c01a151038000c20500440c02000c031003032000c088030800d0320b84c1c8035418841000184403841e007210310140a246040c0c0000d170f05500048543c102e100c407016560314000c01c6070000a500c80e2141401c00004120300d0b040070700440340078204ca2070090000c00e160000c0256038020015280c4403441e60382d000716030700761089031340105060303001850b44260742081e1401680b80d9000d0300b82103503030b8012103442925035402100801e048a40544070208160700c42d813600b40e14041d606030001c0e40642c0d808081200752071110300800191600005181d010122100c0c007600701d500c49442c619551200307000e4100140c2c2d003d448039500c40401c1c505102207440c1da240c4100303d81074140031002414100016510348200c03640c881c0075485002c404a030140c3d110b45020703d5240407140000394001c464100007940d412041021440405004203203245040d03076658903030040310700701d410090001ca04554200005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 915642625 1250 915641375 915641381
    0x4050306070807081506280815091311090a0501080f281a0703020304030306120b07050c0a0209040c1a040e061306080102070c0305060c072a03020a03030c0501 70
    0x8500182442e00003410314260203410710138024043c801041e540b0306007420540380c0c0010b4800d0348014082e12001111102811069888021054000942043c0006680036120380b250005034402a215841d43e0300d40301c2c0640c1d802d07080180b042d5214490030f40240415203907100c04621612440384001142e5052480d034070705054441c2c00805940c0c0c0140103075041880c02c1241e0114201240281c00000c4110745020742604072920081441c04881d0400c000c08541c240e00254465442640c0c00c00c40d05464100c02c1a15a5400002501d01e02e1001c000417400d40c018001002d50241520403504808847e41c00221505400c1720f0844103900c1c540f070204826908034000c95400700380ba0403001d00741418218104007815005000038402e41901030368a10855039030f8484806000c12400035999800182007101c80201e452004490b6403044200040101484031700f5185e86c15401810f01110345031000342c031644181ca081c400740c98070080b1580040182c1d2400804801035110703403034a00b03a444180c01c2c420b00f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 915643875 1250 915642625 915642631
    0x30b030a051b010e10050d0b06190c1104020a020723180c1e0306130b01020316020a090c020607030b09010e130c05100e030c0f1c050a120504050306 65
    0x195000320a80800500042000c00401a01c1d54015002c80c55880040b0b41e8020450040d80d0080c0c002c0940030b40b4150301c44010050201d1031842032000d4200042889900c1c460b4292010110092041403805544174124040d5042c0c080c0110024007104500014100d9200003a07020160b440710341d04100100c5000150406504841039111458451101042c3c08103808907017443c049101100088450000d00140c0b65500010309406413401c200034103542180c0e009540540c801e00c0740d0003a1f14001d00f1640610100700d0b0301030307000d9030a10101c140102484100200100d9100c0003d080c0402c081c07509100e05460001a0ba005003554100403101600f241d1650903050301030400307c070062061110241c14940c11034000d00c001142c4c0240350400400f941c10b10b401c00c55000c09401201c1d4100ca070300903a150075100044040d40d01180520042004188035a0483c6401494400d0005040348051901290f07941c010010307154181c0035076a07002142c002e50404040824004170b0240a81d080400c20350f98 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 915645125 1250 915643875 915643879
    0x11010e100501120503090108190c0e13050c0f1e1207090909050715120e0f100b09040602090604030501060e01091802030a020609031203040c090c0813030c031407050d030b 75
    0x100b000a581303516803244240981141130140c0703000400c411050b41c1100d90080f01007040c00f00040c3c1040100100000c0b41088a18460228416940b56101c40c0c0d202c1c00d4040c441d01040c8918040c001d048a400c16001003103044503200e000038a005440140d90300408a8480001d100001494400005000c0d8089500024802d0b450f00d04903200040b0001605001c1d500001407150846030000421100ca800c101c114540050400c114070003801000141554003180c020284d405040480e000c1c030003110380005171f16030300c0b01205000c84d0116020747c2c02440320b542d0162a90303140c40c0e100d0f100c40382900c80f281c1c860111030450400400c1000440e03c5148294000d010707410040441503000203545a002c1d14029215500004010801e5a4100400b1004210049941d516881c00e82081d040317000703842c400c48072624180121440300c1c40c419800e07a07100b58806e1504103994a0a61811030315207125110807400d000c1c810a0200d0840c0350070001d0450244104002c20801c0801400281640d210700101c074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 915646375 1250 915645125 915645149
    0x603060b04180911060a030906050606090d080c0708070e04020f121e0c0409060b0a090e07030311070b1b120307142104030908120a0906030c11010e100501 68
    0x480030802c14898400d0320708684101251680042c02d0800850030201e582c1540800c001512607122071f019000100c0450040c042085242d076180c00303000007446500d4034a58000c480780340701c030000b4001c10042c2061b0010041210801c54480040c2d900d000740640200c44032640e0b4104200451405c45100f0740542c4059442d400000341505005a940515405d4100b00e02040340c8603044820003004441170b0740e00001c0080c0001d0010b41080c000a0914010391741c01000d4404002c036507101240100c0204c40510001400041e1942c2c4040f141c40d41240d040715564050f800c000038140c10300d00f015000c3d00c403501c0441486c0065002001d8540a602c2144921001c0b041c0100254141c2206000303041107000e00d0350654030310007941220480c80d00c020310741d004501103400740000d059002401c002a282d014007200e00e4030303e010220a00f0b0303001d80d6811030000303510498240714840c4607400000c882c4c5124200042c0c18002410001d09441c00c44c400c1c038244d80e102c0c0500300062145402410b00500d0345507091 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 915647482 1107 915646375 915646379
    0x13020310021c050402150d0b0d0b06121f0c0c0c0b07020a12120c0618120f090b040308160b090307060c08060d0209090c0612010603060b04 61
    0x21001c1c030725016220000b41c1c0020344074241c00369030000c002080c280d440b101150360aa03c4420a17151491726026084003e84070307961039008441c0b01e108600d185160040c248001c0d03000c0f56055640941c05070204422098510042c0896901c80301404540c414418030b040c3c803000f4481c90020000c80100c880050039500d0a030141481d40c0c403c5030341c2090180e5984802e0094a150a00074180004c0700c56242c0140d4000e00e00710110900c030710004515408813a42e8030345045089941601c0310210200019240751707002c0781c0c060790202d280c1090500390f424003440ca001c43c015800014035581c0c0004540c90b0040e08040b4261103541c1c80080c0e0b14251900b90313065a00d0f80c1002c0d20480300c0c60300380a10501003030301441000e0b02c202c001609500700740e9159001c11490100241001400e8001d102003001c00d603e031407004007000160641d842004c0e5140c000020700f1510320380c0c041c1d601e0880601007 = true := by decide +kernel

theorem cover : BRFrame.Cov 915467625 915647482 := by
  have h0 := BRFrame.cov_init 915467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 915467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 915467625 ≤ n) (h2 : n < 915647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
