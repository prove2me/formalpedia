-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1755
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:33:45.514983+00:00
-- url     : https://prove2.me/submissions/234fe530-d854-4162-82c2-028ff111cece

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 315467625 ≤ n < 315647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 315468875 1250 315467625 315467627
    0x3050403180b040512070816030209390d020a050c01060e0105032a0d0b06040c0315030816080327010c12020c071701021305120a17070c120204050f07 66
    0x3118113440c002c50b031070348000101c450714524184880e009400107015030200c650316042310324416401c0d07a108a5041c0032940d1b81d4000c0042e0040806030316040d030031040100154000c2c2c0c0701103819018211200d080d03d40807035400c505041e40c1c011034002c0c000903c00031f45030305598400e02c1780c1809041040c0380c00e4825450040040d6440c40356a04107140044030b800d403468040e00312110500b0a00c400760001248540b541441068188100c500750b020341d040110000d00240701c0d1242c2e010070006032141031040e908503100e00c8140d4009060030755201482002810109103400c02942c4038a4140803180b903203144540824156801404650f03005030704051030003c41982010000071120742002c00140c03103c03d03404c2201e141034115071001807860860200100180c00640042075105a220520b1000301d0b680c109121043c1c140c030042d414282c01010224000ac0c8299005d40954030101003003d0812050f0f4441c00504040c6c1d82c440c040d840e02c4040d00030218100b60003003c0d40310b103001000568500d00290 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 315470125 1250 315468875 315468877
    0xf040b060621010603020406020d03090302281e0c06020102030613050c0702100801060315150c17030c041410170603070305060906011d01060504031b05040c03050403180b 75
    0x31503108034000300b03200b040c0c0000b1181d01e090102201040200c81c0d60361340000f60095105001310030040c040e200c07a201d0b0360350090141e07010381c56140e03000744204031840300414280c0c4072402d441081e20620260704008a2a038000c000e0402c244c2d401e0640058056141101040d626584081c0c2076900510800042e603484986e6038a68610012000c900390b40c0c1e084070800f19104000d0001c0d4001d40280102c2c0000381d20400303040c142c91803620200818a1344141820700e0300701500c9030b001840d07801944620182c0c070441d03404d8022071003010340c0c2410703480601300018a50402c0b00e00060b851004202003041d108a280382c001c0a100948440412024403070000745030843c0711048408280701d8101003000c80e05c0c05c1152900554201d0300b03884644c2840343c0d03c00c3d1a41c000303116162203d441240d010f040300c002c007500302d81216165280d540c5011316643d1038240c2c540354190110a0344d000782c1000070382612180518440a521756034002014549480d01078810100820205540024942c0038400003903404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 315471375 1250 315470125 315470131
    0xb0109030b130f02090a051503031606150f0e0702060a020705030a030b031614100203040608010e04020607080c06100f05150c01090c0303020601031218031b050301180203060f040b 79
    0x5101c01c42c28203a0030054908205208000e4000e05030f00c0402480001960260340500ba4095040e000305941504040e03407802500b41c21a170380359040075010002481a13009100f588040780301e822215a8a602265101c16a940407126141640e010030900580c1804042d50148000b0000c6041000546805680303020300c82e41501410741d03c0012034542d6a04100e40301c001d0907038115503d8bc1d292aa40f425541107603103826180100c5210814101203400482510b003550040d44d00c20f50980c3c60039046142010000c2d20581c0c0042c0c0030001c040100307011800820604628400408041c1000404059580040c1e403220900562103c0144031a54482d401000f020460301300c40b90b21503030704018041c0100700c3ca4000070701602513418000205500480c006040300e0060304a090400c42650301601e41e40d0a940060032004110303001800003ca0003140200e0b02854442881c1805807240046421105408087da42405100700605c0440c0742c10401d45030f102914103c0c00f40c050500350b584202c050405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 315472625 1250 315471375 315471391
    0x10315050c1b0c0402130807051008130c03020303071101021608060c0732160509042a090608010b030f060c0306060c060c090a1212080c1c0c030b0109030b 68
    0x1c1024242542e808005800001400501c00c40d0388108030700e06081c0081503031080c3c10582c058140002494a0305108014451105032258a165940d00c076009103102141141111010f60400700840561810001b03803003920702c100d100502d01c1541c0000a481c14540748203088120030f011405015600c0040740d502d400485078500d03161110303200e11b4620070340095040c0c0710f82c1600200070450392102a20101c0c01e164065a81a2a817480d40e580c0100620450350140303a07005000034000c00c0008494a4a80c140c0078400100d001008000500000700159190310180c0c07000e4585c8001d020002c030a00c6401c0d1541c4040300103020350f8481181250300e8202c0184920b400000100002d582515210222030703862444005640e41458005c0c10380a40c0c0e003103000c644d07004109000010800c04212144c81c083e942c4c008021640880302c1003000c49031103a0091520045203000d00828580d02000040d000001170003080c00305182c501c031a8000e0881d242c040c125410020081d00800110b888030b5542c2d81c002483d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 315473875 1250 315472625 315472657
    0x1d040c060e010504050409081806130510031b0e091f050f031c0201050a18020310050a0608070b0403120905010f05070c05060a0c1a0105010215092103010315050c 71
    0x10020050b203140c01135501041d0058248035080c02044820340c02059417016003141c0e25407075010002401814003920402450030382080030140460729041070303038030315840544c0f41c0850820352520b100142408c50703140301c0020801041403542d4901d80801d560b030b400090700d210049200e900300700c2c075505c40e0a140314890041250b50711010362a10180980e00b9401c000e8088000c0c2d611000030700a0007441d0484401060a00c0c4c01c4080e030010b509120f14a14541d0024000c0c10548200f003118001407001509086200303075075210000b5152001c1c090b00300280340c40602c054542e491800c0c48218062540d00303090030041a01410311a580e0031a417184071444003481d000b0340390810707450202400102a00a550b0010b0082a540b14883d40032000c1c1038840d220340a00c6003180b249140343c101c0ea070001c1c003840c1c1c050381140341c80c0d200c21022801c4680e44410340e5002c88401c2c80d4508503001e201c008483d0b031020744280000052007803201944011a41e64007080041125246c0f02407102414000c00c1422140355034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 315475125 1250 315473875 315473897
    0x115050a081008010c020706091203140318010e010c081005011b080d0f06140102120a0315120303020a1b02060a050d0f0507110c040612120504030602030708011d040c06 74
    0x20201588402400b443c6000300507145807450040e540b00c10340d2040d0000140001c2c40030881602900109201c0d0f507142d10303540c90042c0c101c0c26510303294000030a000d00b025110303180300100038000d00407001c1085050b1f0002401560000d0010128a0014052603009109160800103070b40e0161030458a2840d880ea840c04452041c604040144034a9950003a00743c01e01900c40003401c140d5011108503021100b01c410300c6040c240040e43c0382c6285000c00d60a04070140102d40c1036500940000150381c0482c0f180e4007440c4d4650350300000080003c1025000240d0105040c180690007030700d4880d071114043c59045030011181d00080461098520110070024042561100444160092418000c0e00d910901251910940c024900d42080542c201140f04411a0102c1da06141c41460700781d50481c000341c841c41160f51140550360001d011500c080240c100800004245e4510103035005882c1c50380c1d001042c0d4505140106118550540084070801071402c8c0300000d00c0c4000f4010440314203051202c4144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 315476375 1250 315475125 315475141
    0x15050912010203040b19150b0a0e0604081501050603010e0406090201030b09130201080a0b030703060b0a08060c0d0f2714150907080a051504020307051305060103050115050a08 77
    0x150042034003030096002005000403c00308500080c41030940200c501c1c1403944850702c92042d0382001c0340544940e0b1580e80700303110107904440104500e24142c01c00249203c2c19601042159005074030060558114914910303006805000140c0100021540d103421941031001c000074041006e07100038691591403401d0743c116402034102584a602c01002c0d4006407070605440f80714240048400ca00187c100c100048019a0b684a411b46440001c1c00030043c4a007160f07100b200038112150b049a112092410001d1044802c10015200350b1a5078500c54071075010140c6801903410701d90b02d1207402d038205a89260041502c4a1101900300385c2c420b000c6000086041401d440a00d51006041e540905039003070540e150142046d50040c21200c0c12a41c80da55070340704585d01d904440000030076a0300206800c01e2207142c502c0450f50428001016215415039400c00103021030510071194444a440310200b01c407035a003620425004114070804080c1455403040010803078881c0c07050075014413601b480400c0d01700f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 315477625 1250 315476375 315476389
    0x1b02030f090a150f0215070e090405030c030a02030c19020607020f120f0d110c060a05030a0b030307140d03050606030619080a0308010510020a02060d05070e032b0801150509 76
    0x1d207901d480540c29660591402062019440149009440307543c100811640c0458600380c03040d121f40e0b82d400440c001d01000c12251600c05403051740c0c580720500a0040c0c0c030700140000c0c140d040145c1c00440d51000030280003410051001d082d02c00245841c1c6030308006d41c03140d004444a260b41120181d1020001d0703c001680d40c800101001101d1055492880f0783c80c500041384004107141e510b4a019000d0408400c9035512a01c00d8072581044040c0203821105004102039074201c0350000700400c0044052000c6403543d08101d50a031030516060707043c5c0040590a0041c40d41d01001c51405108511302200450104e1101170b208500030b03040682e0300ba01c0380b0b10b0b68910300050402e45041c2c0c1c4050f0340c0c6040c02024214203008161003100d02c901041d50090001903600c902503400b4080d907082c401c00f005107900170900185175906029565418001941e0140700039803511034031001e00300c2c0b41003040f2480380d203018035070b0140d50034000110010b11010408104401c00e1080ea0b01d462036a4500540104c1c8d40b0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 315478875 1250 315477625 315477629
    0x60604091a1906090b03030a03091e0507050a0608070f0518030303042a0e060402030406110a020a110114090622080102121e04110a050a090509011b02030f090a 70
    0x8031110010500808052818054240b82c240782014020b1544900d00741c07048600312402c5680c10303071007042200c40c1c4074025002104442d00401000c103822803045070a01e0115000c410842d00d64101c448180a2490304200c440082d05042c80c0c0380245242800001c3c0804d040425040e09114021548a408114203c0b000d45c0564014050301c1c3c0300c0c2050f1401c3d29140034904641e01481c0203101741461140240c0410000f241c51a03003403403141d501c03048107103c000c3d88050006c0d91010b40f1100f05010119102c0c00030440040180c0c000c3c420f1040904282c001c6d104c10000f660304000034000d1824400c150319081e607000ca0b004454442d9944510301000d6108001e00002840c40f04000c0340c00185400c0640c0a0000d000205c686e4007900d907135024030001d60701955164082c4401400c1d000c2000b14030202d4000c14420f002800030a038460b112000900346213155030100354219110b01c04c01034400020b00030256100010825020310821550020b502c0740603282e0433040b400408103054003160350380c10750000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 315480125 1250 315478875 315478913
    0x406021603030509103b01021303110402030403020307061112130209012715090501060203040303170c030411040e030c010903030e0f031b0c041802041401050a060509010201020c060108070e0a090506060409 90
    0x5640c1c024041c3d03c1500340c440d44426103903c01866001d80b4bd03400e003402104d10555040c0d0255140c10600c1d5280e60003403010342da0b803d50714507092100c0400450211a02401980e100900041d14819841000703030070f0740141c20000301c2031402d10b051090411054900030010072807040105800c0c0e91031750200310490b140d0384021005401c040001070346640100080065034020303030700e103034688002e40341d1090810b030141e4221011040030400180812203085000d80385c00401070001c50700c800010402807450308800c0d0007c0c60382e5540d8400500b0035416114408070703010400080d001070f69402107400c2e100c0c05046441011495846840401d4800900c1030480d03110b0020020449410606500003803440300d408101c2c000c0d071030441400440800101a079040b1900104020116820a50203c900c0d402140d2854150364080c006480c0d615410711480d80604020b800410280d4a4803254031388840000d4070b4a00d00a01c0d000b003400100e2004620141d112001b51008a00d071203641c85d01a003411000c11143c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 315481375 1250 315480125 315480127
    0x418090606030305040e070203040510030c020a060507182403091e0312060e0603070b0a0203130311041409060123180a05070513030b0406021603030509103b0102 71
    0x40b08140e0050003074070581c0c0110141d22030690f100f00302030740e0717900c101c1c01903e522a600c44103810b07407a480cd422076941203140e4410b41e030070000290f65001c00e50708181e03517190110b81c4042d000d100124550800d4401040c11140003544401c068218039402e8100481e29403c0585881405041c02035007018020012488000b03500400f4080c1002007800c40c1d4104001c0c0b20a08192000646070a281d00300340c0101401001351108610b41200c1c0080795102c000301c01c040d80003e10000d41291207106c030443c0118003446094070340b0724440040004490804008011805040041c048141c00008056065079803817602d104031980060080c018403000d4503c15603120510760302010b66130401402c0309004514012044c05540c0303c01805440074098080d00b000e40c00b0030301c5410404039a1002034150098000d0100518002c1203a032082003050340904141c1c0070075220400d02080090800c100c2c03107000a4400c00308580c1c081070310340141c1e80304101407080500103480658209207004c001d280e4400182c0030021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 315482625 1250 315481375 315481379
    0x3010f15090b15120402090105120d0f020705060a110601270906110a0201020a0206090609100209042004032a0506091f091a0406141c050f010302041d030418090606 72
    0x1013060180210382c100d0049018a00000d00d50610003400e40c4401402d02c00707000c182000b1a011a0311041407640d0408600c14120000342c940c5071500100111092a655059810040c5000610f0484183d0242c038035481c0010036600b030810705020358004c0c1075803d640840c3d4075906041c01409411641c02d080020407001034248401a0154000c0204d0031158098585590b60070003000d0301c0c0c6d00103c481c1c12442d00940c0c00451440103a9000b814401c500a02c005080070b007004c0a0014445040144607103800e0019041c418070641c0c2070703c201e8a00051700c12100098044000070b140c02031a1158601503540421968001e9440400b020610311104004407101422040018410101c40c410041c42c009003520100001c90b5541c21602030315082e4848140600800c04101900d9102e100308010b550300020f021100341000b40103007401030300010350701400c5504500404c81200c161502c4105038401300141e01c1414640401941c003152255444420582c42c901940405801c10050040c0b0040c905040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 315483875 1250 315482625 315482647
    0x317040e0f04060c0c1223040b04030c15020d0c03020312040605070e18011a0c120307030501080d0903023f0c0a080a1112010c0c0203010f15090b15 65
    0x601da00c12406164140000760860718180e81410241e100074005134000f14005076264011460140818120034060b6078415842c0d003100030581080d04011561440083c003001840582042200648901240700c4c240c1141d200c0b0180d620000200c9020900444141711014540280140c800c421030b0760002c6103041c1307028606000201000c44900700801c0548440e10550704041c00764540c0803480340f0039182103900703004081c02c04024983d21105181d03c1001003002c00d84042c0041812000611050754917802c00130b1001c2c00b941c1d8160801402540512080340c003181d170112008044a40550b07000110705c3c9803068030000b2803403405141020b0210482c01d188220780b280034021503c4054800d9a958a80300d4042041c1c0d0303141131240d081c003684100007401c0420701e010a003069845000b815103010710340303141c0e41500b5280341c0814000031030b1541c030001c41503003802c1c05020040c8940400801c903216101002c46489695401500440c942d1848800da203520740e008808140c0300b038024500c1d16041030b429 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 315485125 1250 315483875 315483901
    0x201031a130c0f2610170328080f0a110414030c010e0915030a0c0603151e06031e020708210f04030807020717160e100317040e 56
    0x500300c800105040301001da104c0c0708250300c0241d1110000910030b000d04641c0e6200103504003500e03801c624500d0480000352030449078031503424441c0c0d581c0619200c01ba1090020403003a0183e81034000c102940c62281c034800c3d8041d032082c0d03001d04110b0301500c45032902e541c0503000b001000a10320349454005008280180d06c40303c4c105400008400322030308503580360300445160032a1000c03690480ea02c070b804961180c2180d9860b4111a6028084070342549442e00c44480303402c007503404403000c20703600d18a0140c0b02801e440d5180140c0780e62490340003c2824240b13181e90910883c8a90020035690340846d41c0102c10540100d416404d80c100250b4031500541894003070b13a8041c49603182d0501c545643d849286850410451103003889260b040c80350b603503a460590704080001e2544003140600040404c11005c0030041d000f42d0301d14a80100100040c4205019881c85030b6005183d0030401d400400c28150000d00706c440c2584e51180c0c0a80610100c8902901580500d401c2440d1180d0340d5001c2224070070340c00c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 315486375 1250 315485125 315485141
    0x1e15090702011b11010f180b09010b09010f030b060301090201081b040302060703030506100c08091516060204050f0f0a0314030c07080d1b170c0a0507030f05010c090605070201031a13 80
    0x1c008001b03d494070701000c0211540c1d0000e2a80c0f41c541d00038014045104640c0f500d5104010350008180300c484c510005019540c260082000400702c401c0501c24400074040c195800001a00200050301e4540c0000e0b0910200a007601c00c0007804071100350750105900241c1e001507901030080c580f9140309203405006044100d4a640c0210080034030f039401c085c41100440c9500e60003006061602c0420b00c20300940c000d010a120140c020100460000140d500e0800141d0b2800f49d034005840b1804c00c81001400401c041910744a440066001c0d05150b40791550002120791080000b0301405000e521a0b003540254200d2032050b000c0c00d40c0c0090340300e2002c504059211041e87e1800b0b2003c808403000588103110210144c041c0c1c941d6001e40d00103041c010000d0101c905c214045441d8003406a44251070300c070303094104440303502242403c4c0003081024001c003110b040d050b0419a084c1810084014414000c03800c000c1d04054079003848154800c606036607000a071802500c95982c51102840d4100034002d44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 315487625 1250 315486375 315486407
    0x80103120903140d080c0319020d0b030a12030c05040305060105040f1b0804050c1503060f0a05040e070311060306030d14040504111902190f06020d02121e15090702011b 74
    0x2000007040e0141503001c90740f042c50a48e0311035508850a50400c0000d4001400500301035a0328074681030180c0c0c00b00200c0da40c082c418211022180740a4600505442001000d40c007801400c0c0300500018002003045415100b0564002905100700d1a2200c094414281c01c0c00306a8401c00e803200740039038407085491145000310125691000300200707000c03601c0c0200f0401200800c2c180f0228000745040020300108060040c40440e4180e00c500001b41292540c00701d618007540030342e10400400c4001c8001320702e00d1104594503400c511349140400c0d00c030718200b0400c80c100708440409200000c00715055030007503e006082040b070101c15481d958030607403240c00045200b007500c1c11a981680e1002905581003440c0312007038020b0f0302107542c805903000c001e030008031011a003d00c21512070000a2018200791070080d44091031500b41662422003d10b80380d5104043c1040500070810440c81c2900411094070f02500d440301c0725078070300718120300402c5544000c245061140c10b241045960184d440d261075062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 315488875 1250 315487625 315487637
    0x3070c0501080f01030f0201022a010e03030f040b07170706020d0b0409331a1003050c18030312011701150503250e0709090f02030403080103120903140d 67
    0xa80340150340b1184100c8041c07803021811401031000400061100c1c1540d0310600494909429032000d04000c80020101e020160120300104a041d6a000c603040c44039403000e401441c44d080d0400f0345440d06205501030381071039500015500701001007664031180740740c0814040340e84940c50381c0b07800e0003e0b5104d2000500040d082050f40c4000d840d16110f1803203030a60002c502d513800d00ca004400d0840081440c642e00070b00d0b400d00b40f04e4081141c14062202d0800148003220182042c510400c41038004a8148000f014506810004030380c81d40ca0460700c8629903074000e4440488401e001904c0c0d4483d0840003005030490380300002da44056024043c2400b224600248612049080b07036400c030440512070207502d507000315030104062540a00d80308044e4074a044900740c031074544c44e0411b40e554040d0b4141c0001460f02604000a0300c4600c2200c8105517103603010340c69401c0985005029540c10300010b04002c0080381c2014902c0c0c02061240300455021110b000b0012410320070b0703500d4103009040a004545 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 315490125 1250 315488875 315488879
    0xa05070b011403060406110d06120c0812030c030c04271b0c06050601030603050610051008070e01030e030c010603061b0e03060a090611040b07060b030c06040b072303070c 75
    0x104504580a10000c00f40c020401d42d9240c3d2214005002000202d0352581420000981203c02c6801040060880c031034004e07080744800e2800c0840083d5683c020701e80ca400902050007244030346000c4a40240000c616940c407a210300034120b185205a5128280b40003501e210401440c002420074901c04020350030411511044044017220040007600400011351078031580b4000401552105070407003410301d00015400d4a076134801e40341010607114902d00c041f10b2042005030386010309071100050700c2c0b0318082d15141040302024090803910300340141490780b142c00c14480340e5410400c3c0d4201118010086c0416540e82c1090f10082c5200000140c4d0071f084500380c0142d807401030b460741d01c441002500800f038980d200c8200310000c0141800807a07400e44c55220381c8058a46800140000e0700802da003042c3ea40225203061001c607200f100e4064002d800290b8045150758511083d102140c0b0580b0b0815582e00d21480d05601803149240b502c9062029100802c5480100101a00f801840360150310105c907 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 315491375 1250 315490125 315490139
    0x509061015020304120614042001020a24090b0a060602160e01062d050910021c0f030b0406080703021005120610051209160b0c030403060507090306020a05070b01 71
    0x807409400400b40e401003008000d0705a100b18440c072803e000345400103250300c500c103000004c900103440907039501480754403a1a40201c5a81c2040303040001340000c10801a132540e80e28081341c107088894406802c0203c600c4900f640170b8000d000410351000c198012032520351609001010030f40600c1e030040c0700e01c1008100005400c0c0c0090700f6100404807000c1280c0ca4100c044450030a01070108049000200c814400300b1030302d8002603000800b070345a007900e43d18142e00748410810b45030044070855001e0000c095925040310740601c1000140e00e45448000ca0140b01a000350120b04401500b0500d49100020414400300303184c0c05491085032035121841044c241100c090150340c1c030700b0400c0741003c5c0c04911240b130900150480101d080c20010b05018110940f408244821114007000c1d82001c00962032090303403218418040c0c040001c40606181e40c0c0c258460f50f078050743c0801444540e8a1010501c224000d640707640046502880940d0b4825071a1001440c1e40c015100846081c0040d0300045505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 315492625 1250 315491375 315491399
    0x7050a03021b091e04031209060c0e0d0f140f070f051002030f030c090a09091b23060c01060b070818010e0618062104170316031a0405090610 62
    0x107041d40031041c15135841c0f04240740740382c5074094821000c0c0085e051440c0080109405145940c602030000028407860003080a410404041d00361403103028407040d95400a803a0350584010b56410003003100340145c40501062401400e44205141440b8101c00040c1000c06110340009440307059034241c90410040c0c6085ea668016400e07007007a0b484e024400030b0541d05040d0003130b040c00000148810040c03560f607074580b03085170b0041509480300c404000c001483da0000050340c800a150301c0b28201303a1940500344803802c1d03590310240700c1c3c8903680001e445107480c0001d41044010340962501c1310f5444c0300d6071070b14031550f44c4030081c0e030400070150b80402500c43d80102c2c0c1c40f0701e0800002c0c1405241080c41c240212004500c29080b5600c80018841d8689420030f800e2213010350025260440c1c1d00c0e0401d0b0400200d00381040214003c1841c9c10000c01804010149203071500b105c440c240810904c0343e025518030030541d09000a0340003031508082020030040000c030f241c0125802c0c01c09103103441c1ca0710416141c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 315493875 1250 315492625 315492631
    0x102041a0429040312020307050f0c1003110408010c020f0606041104090f060e07030e0114040c05130216030e040b010e0303450a0e012907050a03021b09 67
    0xe00c040c07450150031032104008201e0100d042c1c003602185011303180d0343c1d070b0000c01c110324018800680c0041085403c01004119000d11480c5040051000e0804d2100260040c1300c45100e802c10161203d403003140c0b481c00c90050f540030b0905080203001070100c130039000350740343c070208130025040c41900d020400c681010300c191143c0101c1044168076060614413180c0c0984000c208065682d59540c078000780c90308018040e10b008562564002c81c0042004401c5400d40d54225444200140c010007440b00046c0c0c0b11001e04201d0744280c032400e9000c81c3d00d0019500038068520004903524225403180105544881310041502e41103604101c1d4040403001140c01ca8a02d07841e90350568010005440702801443c20810002c1c1d0402501084c0c0c1307030118215009480d40d820702c0070309000c030001a600c0362511120105c0548025810a2030661401c00c0d082590205841e00700c4004840c42402d0101c250b0400448144507041000c03100032880a00d0002c2d80c804114101045c507814004445212380380c0b43d424240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 315495125 1250 315493875 315493889
    0x80102130b0414011b1a0712060b3007030902101d040b0409140a061103041a0703022502030607020312180f0f0d080117030316051b0102041a04 63
    0x5a142c00d50360056401805c81c0c0000381408003184c00d030310300082e00030302d80c5000b0b050b0200e0175141600b05440e010700000201d840702688541094011320040303c0b10307000d40d120342e0b029104003051906000f0b01001c5150900c0740c01001c9842d64030800502c03035019004400c40d90310a481c80740d5041200001220f085801019400c01d03152400010015407410350011144a88014030015001e48942d03201c0414001c01d1249241c00d0300300d021404203005242c4191786200b00859103030740ca0f40c13400755100402c0e01c06044600e450715a003a40442c040b1803003a41912805da1805101150150f0401100d8a652004200483c82841005d0000701c0c002c3c03010090307505003151010380702d841d6103402c5c12450b007040740320491903003038461040014041401002100d804540c00d2001e030a031350000c40c1000700b500405030083c074400340d6200c410790b102d8a80001101d503c141d0b025030707031040002000d81c100c1d09c4d48101c0410a0036445070006010007020f0650007441100c21203640741010203148484802e46000d80d2060309 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 315496375 1250 315495125 315495149
    0xb060c150612030406021b060405010e0919140f0609040b011e0f0305010902030705040204061409060d0908041401050901050a031503141f110301170a06060e01030308090106030b010501030207110901080102130b04 93
    0x1591420081e000e50342011114000201c0140c240c0008420fc403a049910042c1c9442c203000c0c03106411205492642110341522a6086890603490340647d040c0c041c805c004000031180702d11840c0c140d40904800207044001145803000e075403800c0150107040750b90f50581c802d0103003000c0010380385003d100315400c0750070541360700388003186984d00c000203078000856031604018200300d40c0c07040d807a03580304000d2803910401c07402c2e407150b0600400e034101d00c1d900e01005050000401c0312612030b0380c124003030340c0c1c81d06600d290120b181d10a9141001c50382e046984010b05d400410840b01a50b120003150307858800c00140e84041105183c41031800503200108040b0005090810040c00882100e81001542c82924805c8601074119542e508040351915840300c007140f1400001803040641c80080d564000303501000a200e03560941d101e1000003a018401c203418144c0c0007c3d03007001c00410340d24404441c00e00800c0352200307694411714140030b580842041003005150400c045078104004080d60292042403c2c52 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 315497625 1250 315496375 315496397
    0x70206070e04020a050d0c080103050f0606031005060319030f030b0102060606090f0d0c0902040302040e010b03060a18050a12020106060c12142802010b060c150612030406021b06040501 81
    0x2c000250321007030b081401c025080100300c0c0a08040e010b0558031000a40c1c2d499800c1d072640c285641001000c0d40e406000341c000344c040c401740e50b50025403032f030000808950004480d05c5010010340b0b400080f1030241d0f108010382800034145138011112844000712a141030103002403020049803a0344013240ca195001006105942480c1403400103154801d00150806004c003925444601044103141d105d0340c07603036800040030300031820503018003100c4800f00d40080c8004000ea1b40043c1d12810020b01000610343ea07031114000d40101d00707202040c050b030081d0a440102c5441d00300281260701040408000d1f43c00c180300010890f214044022940b500a05090344132a541842120100c07020079903039a00744014000c400e034004184c0d40b0095082d02108000b0388807042c1c0040030b801c3d5040c03e49240d00c40c03602030080300f1206e0000b140a5541c8407914416010b40d55a05000440d041d0f40c1e0000c101e1903100111700401c1c0c20343c0018010043c15102071000f0103035058201000414440da00400b030001d1a55055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 315498875 1250 315497625 315497629
    0x1c050a0b0f0328080903030c01020c010b01050304030c060f021c140c040501020307081e0f0306040506061312080708121e15090a1413140d0c0f03020a050601030b0f070206070e 77
    0x180f1480500c5000703110301d4107070940e0019207540c11007a080780f0300f6540060701d50100c403000d20030015642801e0038400d04500e86520050101003011001a040e1526a07090808548041e8125104101e10111020808980da01014014101000301c01c00c00c031000008074651540d81419074040340c01c164025072800d40145c2e203202d11a04941c5007110000040b020040031103411502504468094041c0c280d01e80c5041c1080009a4502030480c80c0110010082c1c425900440400035090350303004040c000d070900c11440d0141c10343c424a1009000910041101c03000c1000d03410280e03004680c48400e0003001d06803c0e24480451400399230f81c3c80040e41c001004103071790500e5840c4a0703010051030303000510045003e5402600c032900311100451584c0701d09401003004041030815245a002c0002890190045030340901501781000c0003910349806048a1006c05200700982c20544d0380c40380c251619942e580c907016206900030349800e61040103990015002520004016114817283e0751079031210000107003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 315500125 1250 315498875 315498943
    0x1403160f0c08070608041b0f12080d020c0703020102100b0a03111210051b0705030301032d0803070f030903080105090910060e070908071202061c050a0b0f03 69
    0x84982401400001404030010b10003c030042506445110300c51801d031070811160408140c3c14101500411028002155080400380960303400301c1c0040700741c02c0039017405103150040300e003250400c85c00000c140450240214030780045074800c2e0200d070800840c00740c0c91001d0320042000e00783c100e003115900700081f90026003801003508011749102807010a100d03503141000c0c20460881c003025102c00a011600307142e40b086065900d0300601c40c60600545036205500c0e44011710000d880788046e0303a0074411800038247d4070011446040c60000c4101c5242c54100c81c1a0003c44050010030402c581c1c4805460183c0610b2030240e90565505c0e00d030b43c0c200001c000008101420aa060780325200d100c83e40c2040d284103580c05004881c0f00b884151400d85402070000701c05403c083d40d9a00641410004028011159562241e044400e16102c0c0b130010790708140c0c400d41c464404e0040341400c082c046400030a074800030f04030209540c01c0742980645814950340d280c5100c582c0c00001c0c0201c200703040d0404044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 315501375 1250 315500125 315500153
    0x8090607060b0d050a03182304110a08100902030f0403120b06070b0610110303070f02030d110913050709120203030912071d13060903031e0603140316 66
    0xa440020701d09844408608640f41880301100d65500041d21101411b40240c10a40c0060050004648240c2007010b188100400112441c10040458600c404103954130781041103154006850643c6403001005c1c001d1801c03000f91500102010740c00004074400d11f403402120300c201401c40c220b08090721303070703590458402031155102270410b56141c05601031607488100070034040d4042d0000c5045030801e0700405c800c1e100243e6040c020b029520000d03201884000c8203899100c240e60a085202802d142d005274218803600c1c0340035821078a0b00c00a04407e01d410000b6007100d247c1510340103c51819542c000d002c48806031045404151182d80400c02d048038103a00040c06407001c0d090700c0c00d0000c10404516501103c070b41040481d00408014881010111441c1e43d40300790303091491407213050203485400c4a0301800c101400d42929100d003a0f09050094110007884041214500c40441d119a440c50091170140001c13030745030f80c001c05e280b00340c0c040000a803103901c8880700800902c41066960b811050480c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 315502625 1250 315501375 315501383
    0x5130c0e06030a140d09091b18030503070b0f0703140c0a0504080d020102030f0a09020d0305161203150b07050c0d0215070308180105040c170c120a060c05030408090607 74
    0x1203941c10f070000d0121030f45151801d0844006040100c110100505010420b81104407002d107400520f4032043d201850916401c2c82ca410440c03450300184416202c8840d09400140840c40001036490802881142d942d200f14410951a8081d4494007400c5043c2c07100d943d0b0500c050341209021503a0412090000c21050302d141c2070051030103548048560810450301514030150b5070220030402840d03440200c044c0c3c80440240100a0903c40e94005200a14000390141c01c11401040c0c19910700307060400c40c601c0d10b4002c0c4210420310142d14006001c0e00c140b00500300e542000380c000140015194081d00d01b840c3d40035001d00b102a4a0700d080c400160096502680e2058040030061142855440105000c074000d594240c014074210002c02c403400da06062a0010341c0c940309c07c100214180318800f200303440060441550900480034200d141400b4600050b6000f000b0403500110300d2000505c0c0507049100e11024010080da009099900340000c0340e005c3d0800c4410050703014503180420090140d1845 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 315503875 1250 315502625 315502633
    0x12031722030e1201150602280303020912161e0311130b1c0209060d0b070c020301020408070612050c120703091518112d0d020d0309060305130c0e0603 66
    0x200007505404e49102250918150702d03100403e000ea81d505001074823004003101d014007900050309201903040080e5100281c10507034040b424086c0e039680c00d141d0014610240d000c0365a200d07a0b08175240e003a44142c2c801c41410324801d40035150381c8083d000d80d6004898004103091000f048240500450040260f4107501c026684d046481c0f203030791090303403500340d00264032784003803c1004920610005140160555200e810ad0300032400020340108061503108801e80b40c1041c41800e1440480c4c0a1700494022000304e00541e80046800307a0301080c92164550000c5051060341c5031b0f0302043e001441039040c90f000e1004c000e0006600c0a0203600107584141c4600d00c82020200e50040d22070449018030500107a00d0b20f4050031030140814001004040c0904582071540710b016043c072481c04001c90100f039001030314040407a44141c0c0d03d21010700c0a5580240540c0200046840c00030f1001e48a402036102192400300400c140c140f14548a0503100d500100d0003003c2810300001260540c030041183c1e03410301c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 315505125 1250 315503875 315503899
    0x9010e12010c17090c1903140313050604050904120306081c03140702070303050703090b03180c0406260304030807050d081509131b031103010c0810090207030912031722030e 76
    0x414070b0741c84440c48c1d103003c01554594042c013040a444211f81c0d80614442c944c01d201c00c0c0302c01d64810001a070070940c04a015403030280d00b442c041d005040650302002440c0601c0b8006408909616071548804416540c01c0000a1310407a05510f59041542e01c02c3c010703400000c0900010340030701c0007064014001c1c28500b1143e60f40d1416000258411641d800703003a48030790241c1884001c204003d140711942140c0c24071400d42000c066124942103401e0a0400407885020311a200300c0500440d000b0719040200d407a07882d00d250401580e101c80340c5403400009440400041c50702884000c186128070740080190800f921042c03900b50401c41c4a07041a540c2c3c115170105810048000c800100045100c0c040f14990256034204150840f50051480403d0010000800058075500b00b805003d48250780801a2100710509048031040c10b690800003078800309914000c01e054000c2c203085050510540341d030081e5920000854102c03406150000c002280695107000082e002d221100035402000d03010f24100a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 315506375 1250 315505125 315505133
    0x80f010e090a1e03080108010207050c010f0c05060f180604050d0302030712180506010b0c070b0f0909011805100837140c03060408070809010e12010c17090c1903 71
    0x100b0000c041400150420280f14105a044454076006004e10340003181044029198940ca504214a103281007001d021000c0d12a240600f04c1651903a8000089400b04d1601c020100441d500546d0b0701c0017403600160741c05090100c00101580305a50000242030720071618002030300a5000500480b090101042e881458025030388203c01e6170051802450100451500b801414100107800c0302180303640c200f06000352110000b5411040f940240c15482d40c810b000d01f1400b00c140141181c103980801134400004149401001e500202240920f00308001d8840c0e0b114201215a98840c040058104105d210400d090861a21200840e0610210491030700c00078841030600b10344a084405503000c0c00206c2202d10f0411444078008002d8006101c01d041c19220f01c103280c05011402442c0d10f10005025540d640b04610407036003044041d0101d4080140446058040e00c082800e10b40010045580c01d8500041d01000c03038011030310403014040003250380f07042c800300207250000c8506004034000c00000003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 315507625 1250 315506375 315506393
    0xf0503040f0b0906190b030a1b0b1b0c0105130504090c050307060f0e1008010e0a0b0901030602070201180609090b041107140d05040602060a1d2b080f010e090a 70
    0x28803603a10280c00580341202032441c080c0040d03000320013a2461b00c4401e0b10991400620030098075001004030036020713030401c0205c002340701c0d54100c9a00e010010074155000e5203800521820843c65100741c404a4644000450b214007404000316145203d0a03810451070801e584540b0b8001d00540012a03000e454101003441e0640caa842500001c030000001d940c0103500c41010509203100302c8070f03246041c0248100500b111018016041144000e401248034000ea41e4040d20385901d000e010141550f03900c2c18144020741182c501680440c11000c0a90040031926a204007651403548900303100701c0c02c0244c83c90042640c003070f44a81007982e48109c2d81c04815408042c00c81c17184a042c03050f16034401006814180240080c0c0032040c803100340300a10403560003058540d40032003480c3c3d0005040f9140300f1800c9806d40f903403092020070b02421400e102200c40c0d051000194540e800c9400d82c11070240401102e00600403980c0074041401078006016a0303680030b94240d04482c0a0044070186c3c100c0351150010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 315508875 1250 315507625 315507631
    0x70830090609131a3303070c050601080c0108011730070822030b0601050d0b061c0506010903080d09080f0d06030218040b151504080106081c0f0503040f0b 68
    0x1d030001341c400ca82403d00d811441d0b50385140864042850506a4003809820710103268410f070110b02010001402c898411034040381e0194024003211341c01c2d40e545041035240d0f4100a40180002d14400c004185000b4400e1054820710070200100428014008010002450f05c243c189141e40050500c14110140d44054891a130044000381e9407010814020041c101d013190318600f000501c29010030218588284182e80102e082c24003d5445e92108d03600f2004101034403500c4e500610104401d0701109000008525100c40c411b0300b00017607280c0c1e40054605141c144001000d40740b0810407115400071680200050a1107040a517040402d642e80d17610310f0750014809030144955405081003945072000c01400d6003203101820341c903c0c0c05c2545951103540001481040a1010140d02c042d203511020030402000100c0480f580d00c1d5522245042e01a1007140316110003031280c7c00c0815895100e030317048080e004a83d615031002c1c407441403070241d600e500f0050086d105002c41c3c080302d40101d1702621640384 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 315510125 1250 315508875 315508901
    0x1b1309020408010c08090a0b0c0904050c0304031206080d11010e01110c0d0305070507060506150c011415010503071107150504150c050c120a0507083009060913 70
    0x1031180d0409a466007113070b1020508004100541003030160340c510100e82d501d042c85c3c2100c1e078a04175075170398481c40c80c0074400c52416942141c544400c100380200020701550040d0f21035030b80e04082248190040d4181c400d07500032180c146d0451041e0046c11800b0f0022020b461000100105580100842040c2100c4400a12122034400020b0301f112909061004000343e01440c1000c11150400010040071805130705001841c85036242e02069040e9280405240350360191500582c1c2ea80000061902a0101004409e0b4000407500814003035907501143c0f60300e85006a43e90346c115551020101c80c5540d021b41003280034041c030000881c1c007481440c02950b0760101078990556482c54086801140c20491043c4010410600101400540d002c42c0f103c5080104a480525494500c4041c604044405900400600c500c0d100040c40f190085542402121851404600310456164002c600200700c4508040280104103034000740c40c14002815003e180644403800065030418420111080900c0202c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 315511375 1250 315510125 315510127
    0x406050705010f1b091a1806090904140c033c060103080406080601020f0d030506061606090605070518042706050f0604150b07030c05031803060601050c061b130902 72
    0x1a804d6046201e40740240350a209035001d0141c116509a07480c06008582d0a0204110101c2809a501c45090769680c510003403845809040500d0000802c0403281202c01460141111408041c034010a0800c0400c40c0d040c85805000211072490080c0841c2900d03050b000312000c00c4280024000b004844d010b5845a1651641c4a003000405010654000c00480c115405030f001080002c401048900c02500c0303500340441c06840b200e0000300700f4011250214030b0800c07540c02040500030142c000c6407406d4001c56042005071108613007140d40d0b20503038126451142c0080c803041c289080c507030703c15000301ca28180d46004117150300340c0c03510545440c903d064070340c40e03150014003d281c0000c0c00503a8204c20b0840e42003180c2480c0108100d000341309481410442007000c204081858010320901722029403284c2a40c0e560310b1590704041d0b0010380c1460300c5009119050000315030394051000c884e40d11924074020a4030369114a00840684008210303071314080402d00c83c0041e14180d60047e84040d00c4881c0002d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 315512625 1250 315511375 315511421
    0x14070f05070b03090723041d0a05010b04060f05090c0a091203050717090d08031306060e010317070803010b090102010e01020d1e090b06010c03030b03100605130506060406050705010f 80
    0x244d868800185c02c0466400390b0611807404001003a0039104641c1415100803d8814000c80081441404000151038500901d40100c003080b4040d030001801e824111410082c4584450412414101e540526900841c4050101c4c055421800c00741103262500d1603c40425600d0702a01c51a903117051804401144c4081000000c0004089911a180b07080101e11800d000e1a1000244041c1c4118030140c1101d030000007203880d0314082d043e12442260000e400340304042d0340d4111041404824030050318245046012818a00200c0003202e5149411035101e80c1140d0801c20400a15030154003200d0640d0351343e6000004c040001e0014082c140b00550f0005011707014010150460075000a020b41514644010b10001602d0a010560450828078040c184500c06180a50081c92041c1c4916414803a180038110f07140e011360880c40983d042991035a00740000c81c00380000303441040c0d61706548003400f03200c03c0c1700c52841030300641001c0f4010300010400c6043c103170400040342c403141c0c001000301c1801848 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 315513875 1250 315512625 315512641
    0xb0d031119110f04110a18050a0b0c1b06040e090102090405090c030f0109120e01050f040816051c0b0a09020d0f060b09070e0906130e0105220314070f05070b03 70
    0x48540f1000f0f45080c405d29034072100180b424070410900b00c041c000c0b40052004c0701410184018050318018214040c5c144c0c95070b07030300c000d00d4125146141e0103100d4140ca04040d90007002c8000c00c00b100250103142010304291400a0015000740340c40215942440514126601d40c011035014044803000b5000100141e020326040498414070b95009170704104280c0000b80c5d0303e041a4a800400b464803000c0d0680e1f51004844521406021030b000c40c1011030007041020380410540c011445c5440018070302c6603174a0502c81d00d15025920801d40700352081000020590004225512801c0003500040c010401e60020300b8000e2110015034003040031940c0c1e9000c004c07891040010081040300c40e0021403a06a100812a10841c078040d40030703040c1c02d0089501d82e10398141c00741160900b0001406012400003520780280002c642a8007a201c0141d400000c40300c110a1009040e9050340c1c0c1c512181604412203c49948020011101d2401c0040c44d02c011940034420f110103840f034400555a40d00300000c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 315515125 1250 315513875 315513889
    0x7051c090204110708040308070201090e090c03070e071d0301150f03050709052206090807120806010311040603051005031c2a02040f0902100504180b0d03111911 71
    0x4641e20f031218208584400b042c0410260340450b5401104581c2d1001300b0300c0121080c2d98941e0020740107a451100f40b01009038040740ca09620b4405604592103ea1390384050340100206881c03100c0881e50740c5605a6070303210905260155020f0180001c507041d00348140307800e10076076994010003c00039011014000c006060000e10014984003800b4400c90600c50b034680c0080d142008000880b0304000012010460142c1150500035005591540c039070199090080940480400c0301b0300081407640050003d40c06880381d90352000d080c2c0152030819040140a400408016024413001550b00400041c04c0d1303000c0100c01c4c1641d0240c1c4411418010440014065504283c5000d85107130191070340c064882c10348c200c0940c4840c2c048901103044034001d103901c00140b5580e00041d4000d0702c00c64021450300c1e00315009208551000600d0898180160a071208a852040a2035030000f141a50100482c0c850001701180e1219a4141c400143c01002e04620004019401702c0e125016002401130b64600710b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 315516375 1250 315515125 315515141
    0x60a12050108010c171003150f050601140d0b01050712050a300c050903010e070501020f0109020321130807090c030b010c031206030b1f1706060907051c090204 70
    0x100c004e1044180c12140a0305200b0141e40240f42c600c05640019031520704451000015a002111648403a080301c00302805000010702066880d410b02010464951103a1100c945200e48001e2460404c1900c0d00200c003e05030400708a81004400d000030030124400c0c07691030040f502103859040c1d64003000c600160060500140003401e6403514a444e0050700186401340000300a00c000000c2d0a44000f64141c800e03002e4082e031140c044d0701e4041c00300708203000010750000340c038026000c503002201c0d04680c1d1400d039441864001c4d0542c01c10101001502468080c1078050700045c041c541c10b211031401d4950242100c1d40c4041070315404910108640d400703a00c1040d410800910b010302c040704001c070003e806507042c0c51004040005845144803c1c003e80d82c0680003469105010307d0860510008403040740d0400a00e001c03d880f82400c00160304410901503080801c07083e03014107820b80c0c440c820001598030040c90350080c00030400c444d4440e51464050380b1641c60016000198111a03401800120742c142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 315517625 1250 315516375 315516389
    0xc10020918100b1312030807030f02040b0414011e0f142505210301181404080322140615010c08090301020c0d0c060f0204030201080a050403020705060a120501 70
    0x1030300030b1100d04918280742d8400d03035007008451942c5460074000b002c040000e03680810100840035001c0340415600c0f20845001d40c04994081c85040c00086110080340b2903841110031200003000200f000011060541000110504140e024118066010210080603034450800140041c090480c42a04405600b41c60031411600c0d074201172071641ca1844030288290600000d071000060101004002c00188144030b01090007205c20b08041d41c403003583d503002801414204551a490030202410a00c02c201004140e10a200e941f070310341d6241c04403a80c0c009032034085007000413a101038080d1b4650940c448a64860f40e105402d080700009001d0034031101501d440209a00c146a91589a0780034412001040d04000425503c50805002a00900c250813100321b035401032a94580510790080804c145141c043c00c0c051003940340703100040080340310f940402400318245002050b1500c203ea0712803036009102e4012512595203c000003840c03038101842002c0003c504043c0d50810001038007403a4010125 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 315518875 1250 315517625 315517669
    0x512030712020114061c061b08060303070b130602160f06051501020d050c07080706080103030212090904080708070501050a0c0e0a2402100207050706030b01180e0c0c100209 76
    0x700200703011000f5000e00017030302c0765149200848420b09002140340d501544030008021f0700000c4003580d44042006c01c943c0c004103032920000b03501c41c1004012648620b82c00242c1d4603940d81d80d0310b965031101c00300306411b840c1d82e64280004090110701c483c07880c450758000c0d605030365052228a80790055840062815091942c0341a0604031079030005111000c3e403030581042a129422040881d1038041154003524444c420900c0c00206190010b00700c6050300d02036420346580c0b0510b920072036a036204038405680c1060701840020f02040c690f401030b0040c180f0501c0090726185058940701c0c2545c030161000503445680780107403080c0c10707045154000182020348030021030a240c81032000c1d414216010b0041d00400d0302003c5051140b091200703040d8080c081c0411901c41c591390410907610ac40c00d0040401281c0703841e0b2241c290358042c482c5415109a102c0301c40e0017490500e0075050740325001500c1900443d50510200701c60850921044480740a6803200680b00ca01402c100200202600c03181d40110301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 315520125 1250 315518875 315518891
    0x181704050f0f10030e03070206030a0509190803160908100f061703030f25050c070b0c0303060112020c1203061003020a050a0807021f09030807020712150605120307120201 75
    0x94400e041c04002d441c3d42400070380c500c00c01550500714441c81c0e100a510000000030007a18a02540c84540990403050446204003d48000c001074003a4440c1c01520101013403001804061001400c0b4141c400e9500c0d2070007095a4925000c4c2c589480b4a10503160300b40c0700c1448071a41e610510406005000340480c0b000040101c801d201c0d16840040c3c80d04504041c00c400040351079031841100030340c85050b90404200d83c900c0150003845504101605412402444800152403002100780c52214145901451850b00c0721001540e846083c1d42e01041001e80902049168005c14840800d01154032140659245044003c020704e00402c2d06c20b10f41414818001d0114441d0720509446101d042800d1050743d6444019050703107440d00d100f80040301c0f4003000d00003880c054516084040698444c0c0c40749007003a150704506903103407607460080703011159441002c840800d80d600c517101240c1380440e20004015440c0c42c042600c1c0d402040b0704c03000603800060f44004000c148451007501624600c001c0207070740c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 315521375 1250 315520125 315520129
    0xf0d020c0a050f0f18010806060d0b060f0d0501020c010605010e060c0604031d031e0d0306030b0a090c0f030c15090b030103110303190806030f06040b040303181704050f0f 75
    0x11160048038003d0222000e10a00c0740c80b01c50400c204014010510100381e500798104c404120800d004050b414040d43c400328905042405940780ca03143e00c03400c40086596004184203400341d4811055500280300085440800c20a00c010000912541c00100301541040005800700c2c1c0403800050050328204032442203d4400318007640c02a0345840c00b000d199030002110311004200e5104a645030155988840466100d4040c240c1506600000d4510380f529520080e003c07598244409481440d54200003010008150301089206200710088200c4035140c400821055445802c00c5a05d464100014000b002500818101c5a0101d280c80000141014500b0701c083c08103110044c0801e140400803081640c0c18000c0d030305e410511007001d4480300c0503104c001301142e2064451500031b00840701c1083c1c01c3d940c00b103511445140c215034480d056840e00c0d40c08400074070001c0e101280b216000c191300d0000604203604108003054500304036844134280300411501c8120418114031556000617206516 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 315522625 1250 315521375 315521389
    0x6090503060c0d110c010c03020d0b0402070c030b090a0b0408030109051b1804020d0515130c05070f030c021012050105010f020a110102010213120b090109020a0e060f0406080f0d020c 80
    0x80e904403e8007152040c8200d400402e0340c0030300c601e00d151035401c01c0803210802c0d62581c094140b56000020038060b461186062000700e218802005e80403103141d60b024004200507410081d004050542124842030080d03d40030000c502c2501e0840f0071980c000010060340100340215500200c2030000c1220100f074102010032540324038017103058889005843e8059030343d01d69040d134074603810b428010b00c40d41c0f4141c0d9115203020302d100d40003442440340c4042c2c4042c04006105a54121409840e02807915403191590301c02e0184128045007000462204400180c036201d00b001402d11490303c1c0c0e003045450014a0805440e416003103207040084c1c00403031841245c0c4c001140c20415810500001501e055003004034064030403070560810703004d0121800600702411021000d0190f009442524481e1141072185083c1c941c08480a035002d01120700500100802240c4c040d00403800509100c40c54244001003415200e0075444085590020707070303030f401c084441805a880000100d101400b00708813154001448 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 315523875 1250 315522625 315522637
    0x306150d1b09021612030b0303090103050a02040f030b100801110328020f0903060108150c03070306080109030507020f0d0b0a1109040e03030910020408102309010606090503060c 78
    0x48144080c214124080d041d110010150400c44800d555680c1000e8555003c040964821111030501c02150241107200c0d201da800d0452006001d10324002180004601500001d019000c00315801c10000a82d100b0104502d801148030300011049032030405040c40d00da4842e03600210069040070320305100781c420754085903840303140c2e01d00c41d45058029250002d05a07800340e8400e85010702c001441b441c6070b41032001418450340d045003100c040b03a03281d031600ca445165542c0203940070341003000840d050b09422000355500a00b135180c005800c41e50350991030f094540d02003080e00072500014070340040d400d09884007010810309483d460014078aa81c1c47d01040c407070082018580580d103000c11902801510201c2e9205c000003407080c03100108820441d604d0341d1094452003030600c2400c80004103041c0600a0310102c2e140c0b00003819268800c1034441c00900070700c5003442c0c42d00c0380744901084809019410f2a000d0580c41c0000101581050360242180310705400c043c0c8664880c2003044140041a412030354 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 315525125 1250 315523875 315523883
    0x60a06080405010b03011416020313050f0d15140c070f0201030b0103090503190315080c041107061b0201180c0915030b0f0a05060a051e060d020406030b0306150d 71
    0x150594071814010700402041d4011035143d420540241161082d495905016481050114020001520003603131340e8411011030007c50101604108418504034818000320800038199000c59007141e6150020000074005141030a6a1601e214207054042c00c0550b502c4485103414031b203481000d8513005820142d0210003410180c44034400e0003241d20a030080b0114583c080101c0c1d8950701003a14446e0041c089014030b03400207161031a41c42c1c28043d814a000125020700000d130801c1c408040501006d00008000c0340129001003003000d00040e0284200f150b030100d81051024190100f035002420340d508a1120001d040b09108000302140c40d80041e2400c91b114058002012252030a0442750244c540c3d00142901c41c5e01d10800c8804090001c201d071140780c45140c2040940e27100307400c009a14800e03000c3d05070840c1c889480e0b1b06a0041403044200000300040080f13050090100340400ad036401078100b040081d0f1901041041404e0810145070000c0001100f10080c0e4203000201301e81c9603003c18054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 315526375 1250 315525125 315525137
    0x120501031505040602130308030f0f010f0612060e13050f06071704051510080114010312050904150801090b01170d081302060a1e02010e1c1b0303060e010806060a06 72
    0x2000c01075a981120340700046c00e03008a00e1030755641442c1006800c11144418007000c1d040009180660f2145054107842c801c2c04800f07212411f0600403038464420a9080443c0396413200045110400400c1e214400d000a40d49d00346148071740d2806505020749040801110b51000701071101d02a001017003040544400582d901241d81e46040c03042c0392240324400c4a004a50701c00034004204045003269044d101c03414020301040c6075501c514410304009200290031103010126440b50300d4840d00c0103249110004201040015030403020f400502d030b8951041841ea9540c15000301002228074903a401042444000c01c1c0083e45400f0720b1792100c06040d403103810450410006820008810704c8081c0341030300603189984405000101506c0c100c1101703082d2282c0a20381c0c0162054078814003032056914000d002921482c2c481200d0418a1050340d200c40f0b062000b4580945040028440003001080c0240d8010a00c24640708903084407031410b0700200c0081c1c12090400103e40c072071046803011598145031003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 315527625 1250 315526375 315526381
    0x230f0d050f040b0a05030f010e0403050306060d15080102031605190e0a0314010209181e061c08090f0d0818040902060c100f09050c12030f19120501031505 68
    0x191071511071504942c0c0d80c0718011802c2d5801640c4000603600c80e5840416410090342c880028030702150048030020009003003000041d020342003600180844000740c900100b68110300040c0071414a040d0b8029082e50782d8040300308000459001d60400c03100f0f0450401078034000202d00d12003012501d102014050103000c034111000c9803100c01081c401180c2103028401a0303c003141805001c1d40c450221240300ea00c2900004c4c424049042480b40101100340820714818826902d003400041c0040240754010780501c0007501c20b40c0748485010b00d00e40300b0100c9581e9107102d0000c004400b262180310360f009030341803480403000601010440d41e01c044031141c0840490040c4000078060208483c0081d00144c000c2100241c0300b400054650090342c003200240001c40e454507a800c1100c44103c8050034550044e0004c960600700716018038a2010b102085e207103001110429a952070b40000c0d4084540940c0848082820f5030107111089501c4203083c050055500d962103007034070b070b0310301a441421140d6a0004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 315528875 1250 315527625 315527647
    0x1501140d09031103030a06050405010e07120504020109080a0c0302030106080f060415090807120801240507050a081207080a05040305181306060306050910051018050d230f0d05 77
    0x5400e00b910b00f140c1240c2d5245484407404002d04040d1041c1c41c0518240030000c21000c060b424081d200b1351066071070201304040d1560000142502510603814000f06000c046907111052100640d003a000c1c00f012040c0910318410701d401c5662942c46a846c07a003110b0040c0000c41030200d0300300d0b08070360001d007801c2980c80035045410040080350802800c2d09400602c03401000403e015041c030060f8240c0b244180d40e0383c2c51100c42200301e1403036071402000c20940c1003214098001d0002c0c0a40500503800c6074035041a96483c0400d59002000790301000000c0410030211a9100350090740c0310f2180d41082c0440d00b40b907540a080d0b4081e4000c003e01d0b00c40300d505039810640ba920302c00070740028051028002159900f80240051410303004423401895901d00103100221420708030021200b01170162100e84031851002c0300e030021010791a4423038000a40d000649965104d421840850085105d12207540c1076100030300f0b5a4524280308589500901581c0e03080e0a13020603600c44400007410000e981c0c10540035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 315530125 1250 315528875 315528887
    0xf0705010b0910060f020619020f0706022a0307050325051f0609020f040608060607080c0c01032403080a090b030108010207030314010f0b070204060b030702061501140d0903 76
    0x10609812000760010801282c402030f01c900100e07a0941c5484404c030001c1c840407a15600119455241e50701420707850300c0140103d81c020f280e0b000b150300a0310b0500720303640d91f02000d0741e102c100e1891071203a40341c20525101080e0090080782801e60402075203400740659034a40c4a00841003082c029004c050030400004802401c0000784a5100e004da5050203186001c038106001d680c801d9801c014641078020502c440d42d4400c0700c081c0c81d44105561305140c9048030407100400003c4c10542c101ca024094140003500000c050329000840c10083c008c9200008001001ca55417a540c1a03800c1540c42d92400000940000110940703400c14003681d42d8400912b020784944025511481e401d84000000150128040d405081200c0c400c1c2c0d820f003d840c800c03400402144034280074444e00d4a0711040c0c20400c4080c80002000c90390701c050004514140c0d11f0204050a4204560328005a0419000c21943c40281005c5080000c400d007868220b0380100c1c112071202c0d010f40c110702c00d5801d0b61201c3e045c0525004507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 315531375 1250 315530125 315530141
    0x2408070801031536030e01020a05070e07051c140f011202040507030e2a0108010305030f0c0c0a030503130801051608060f03060403050703120209090a020d140c250203030f070501 78
    0x11104400d51346246844210b02d620100150001074986a920071550f20118502e4583c58100000305461410b104402e081e414001e03101c513003840307410015070032003d0f1146c0002c1103185650000140c006000340c1c8c1800c4100004007012290f400c1c2200501c1401ca4601880f000c450701070300c00092503650441d007a0020410020000715a01c42c0e24603082134045a4080540b1244007501e030140d2000f00b100054402c9003003800000c01c0c1c0d07041805007140426994003c0d0103043c501504454a0742e0000000c1982800380f0742090700d20303820000d40f907459510b15404a10041100f038000b0081441c0c041d94012404104019007010015040082503041c0d64881c002e00c02e801d402816102d9608003031a018041e41d200001c1180401e100d011072095440351131003900c454a1014218408954400120784000e41c0401e01c06151a9035030108150702000540180784240180d00100d580e5a00d0016803081c801490340c2800b8201d044001c1520040c0c4011080c1c81c80d081210605548803682407030302d80d02501034a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 315532625 1250 315531375 315531431
    0x603073204080706030f02090607020d05030d0f02040504150302100e01110610080d020303010608070f0c050726031e091c05010213080607020c1924080708010315 71
    0xc034012945990100f2907200300c801c0c60f18100200305901c2c8915080c3d000d000b0740e0552100c03081c062a005401c2c07a2940d613084503c900d0581c1d2610f489010360404448460a1440c002603000c41c0512203400c0610454002182501002c2404da242d0360004915004440e6218100504001d081203113901a1501008030000754091b100145414101c503101c0d014140310301c4440e03109418080e511140088201c9040c2c0da440c0c4c0d500c2c500c0b5902c0d03040c00d4400e0010f0b5120201000030540b5050046803003408010068081030140384d015280c2d0b00a1140b80392550000940035420802c0f60300d0010042010f89a00f04e120400d4181e01c0d440700341d00207180302e149500921251205c0400e42d4040102c103500800c5603017083c00d00102e0301c544800001c0e9440c41e007240d41c00c0141c0e2007120309048030b2410641001c0115031500d000182c00761a28000041103904104030085011160f01003005550003060303403030f4028a00c1c50020f503d5891511200c54400c3c40820b500b040590741e41090f01c8401c0c00c80c2c0c0781c1c40ca6440c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 315533875 1250 315532625 315532627
    0xa150c050912060402010905090408030105060304080910020a05060703020406020319110304030b0406110306030606040f020d0c020709110310030f0303060e0414100219181203090f0506030732 84
    0x107042c0d0081d40320318040340d049001813824000440d003460646400340c00b0380d03081080c81d8103582c02c25050240c2a80041c006544601c81404400080e6484841543c4819072941c0a405500c29070316289140c0750b409085141030500522003480760642c000305a801c15218040003191489011000f504d40d01840100e0760303c00d00001802009200c00075201500541c0b241204010700801d000e41581d5900007070365081d42c150000c101180481c90980c01089900d0380c45a001840d10740e940c4c090b00304586e00e030005003015800008007041464220b1003220680c019031900c0d00e14601c0c001c011001117903410300000702001c0300a00c5000906100382d10581c050403440c0e40f100c0c000d081c54144038801c40c01d101c000c0b0115100305180764444610754003c1d110000c43e109400c090848001409450385180d207400c0b4015403002030000103100d0350780140c0f03810260103920340c001180c0c00e008c103860302d600c4607030401400740341d0030002e01c179050380c1c822140d81095116071404086900300038400000002c13400501040c10350 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 315535125 1250 315533875 315533899
    0x1505063c030604051c0201090305070b04060f0203091b060a020c01081803041202030c0d05030904090501180605100920070302011b020304060f030603020a140312030a091101020a150c0509 82
    0x200040d24411203900030f031034120280c045c00c20490036690303c4103000b40050400e00014001038864140315401910901001c94050064004881260401c44030b0600550143c5008400a5220301c0300040c0040d080e0b03a01e610380307520018065a11142400c50b00e040185e18400291803c00014165036802056401d8a41c1c03a55594043d088000800c40141d01c20701441019901ea840e100400c45c4101d544400a141042415070400c40200b00741c00e030a440342c1d500d9500a0854a01d000c18500c0c100344505800243c2c1c2c100f96480e1041400385420401074a85025540c210324807040016101203e154020a40e5808840c60102d015152641c080760044141000b0000342d5030700400a401643d80740e6680f04413080241ea0110284c0321540700103074200e035024a00703000c105082a981c1155200c09003c6802d04244924503410941c07003101c1050300d0035903135852541044a03d0f50001a11582440204010407051b02c5950b16101c103540100b00f450360340d0721f541031068040c1d02a150100002040d0101351a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 315536375 1250 315535125 315535133
    0x60609070513140a050306070f080703060513050106080921091c0f03020f12071401060e100801140421140a02010204080610030c06050a09050d1505063c030604 70
    0x300040f805032052260300e0000c59a4100001e4052281446a552a2481460780d806945100b0003030981410140c0750340b004907594a80c0aaa285c40505855000449601d800402410071002814000c4541c000210701042c10386500d40c1c5440b1003134a80511980e404410001031118a04116232503810218481301701d0600800000e40da00480c000d40aa9100061130b100040d1900d641d0350b0501d03820134040c403444020503502c51000c07034041480400024001e032034046006418100f200c01242920606605000440080c01101c41ca1040d1001800303003414103981b071340705070710804d8900250b040907084090300d9a0322445072040b03801ea08882440e0b40d003940d600002c1c0030b0340c414081c0036114414440400c01e100d100910b054101e030341121131700d0000d90030f010085601d40d1041486c44100000d4810209556580f040740c1c0301e00c180b21740c000c0400c1589081001050310070040c00284542400b00c45c5880015507201c503407804089603112055521240d401c903500031880d1125858251003a00100030400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 315537625 1250 315536375 315536399
    0x6050a03090f2003010c0c0b1b120403020c1503060d050c0909101514091504050a0b0f150904020c0a0b0a060e010f0f1403010f0c12060504020903060609070513 70
    0x540c2402d4525800c80c0210044c503090f50717003039115013000508001c1040089030245403081c8e007140c96003c00684600700c03003150050341c0c0c11042101c1c3c40180c001051000b010340400051141c5602500c154400305e070340c0c0c180c0e50790070700000b0442c0e07010360034540071b410400100380000c22112070020888503d0b0705225010325074485010b42030950103407509000160300c0c80c40c10283d1040700d070449080754400302c106080c80700c4041c0140c0301e12400f24031078881c2c0e8145c1e6141d024040c440c514500d000610507100500300700343c202c000b550141c02503140d01454000c031030303040702142c4060f04c040e41d0143c0d4034008890103501c0c0c51001c20300a0314030503130300c0180002a52160482e01c12181c11001080035a42c80b808002d514104500c01e01581156000c4200041d81a9046000c1621030040000621800d85414070040c0c035100c20b486000582c400880e81c500041c0c0340325480140409550840c04c3c000b45002003551000d0242146200341c80b00e10010710700900c1401110903014003030880303441560340c4144080d24 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 315538875 1250 315537625 315537653
    0x60c0a0605011701021c1d07030f02100f12180c030b01030204051006020a0209100e070225050a030b0901091e05010507140a0f0e04111c140106050a03090f 68
    0x100c3c80c80c41001094103201402a0f034410b10441c160601c2c2d10b6001700f414801041e140701d040c901000000b004c40900d50003403042c0300007903005c1c140200584074180704220341c50b110081540d00340038548501e41481580a201610b0b01800090700141441503000440c510049608004010400d030140c040700300024070300a54122482035805100680b180001c08524150b18055503005070300054202026203030100c101e80d0080e5000b00e5151246807510b8402004840480f45000036a0211203610340c1c1c010705500515640a02010350071900e0b0800e80090001c250f14070020300b0303994541000c00c1c10002c00b0350011400300d5006088450340500c10701c0051115000b01c0080c2c945500e0000001c2d4401d000d0b0356502d055541010b4260310b0515002015180406000301c00c3d4100900403114504688403403007011407100c0000062501c40d0031031040001501c101d00720100e40d99040c48100840000c070114000c0c10f441480c2042c2d52580042d6004600070060f8800240076100256403103024040f090b00c0000c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315540125 1250 315538875 315538889
    0x40e12070c14090705071a01080c01110706020a081e0406020f01050a05060f1909020a0302070b16091a13030b01050f0a030506060d03110106380301090902060c0a060501 74
    0x1061a611000e42c1400d00d00c4824840c1c102d1010790000b005540b042c0010040039104155543c203110003141c3c00300b40d80c0c000360850300c1c01d82e00070000a8101c0da00071a00340803070440440244092414a9802520341c1c11800c0014104000460081d0b040c070f181102040c50341030070004054840b07640d0103000f96504034850031a18254030700400300c1c0d84a051406a5071040c00068103042442c1c01400030303c07801d240115000c1c008906054004500c02c1d000b40018030003203034540c3d405030329240e00303040c0140d000e000541410815650404481c401035006444201220201c4c0e10040d40d0350318819107848e180c451380c01c02c20141c1651100100401c0303138aa004e46d040e10700940303a00003101070038401c0c03101c003041c2400050000d81c01140010200d01d0281012811103119142c40c64504c01e2440c802400e4400c1608000881c808150514404604001c0d00300d0f000c464081112042d000051320a441612040c0034214130039032130346035103030564031008219030383e00220304102c502c00d945c01c0c24400c00030202801440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315541375 1250 315540125 315540143
    0x2130909112119050c040501090510121505041b0905160201020a02120a090302061206011e050304060903141801080a110319060f09020a0201050c0304050d080402040e1207 75
    0xa480c0502c0c101840308044120801044948802d152a80000e407803414115690310440b61007040e551164042c2c5402042141400314a9080540900da0742401d0741c0c00041c2c4000000c1100c001041050142c00788081c1d0120300029591280c2c105100710009902d095800e80103611030020388420036901640c030900c0c040c581c03015903200da0f0070304900b43d21626022400584c01009445030805042000b032008150b1400c200780c1c500d540b0f9012407801d41004280c001000310840401c6142d503084691a0304001c0307403400f40a41e43d1000207001d03205000c0900042d1806a8540b030704010540100101b803e01986245604c0e11804c05054540e54818903285403400258214081034020219010700c031248156442d02d0360959031031951546400d842c03208005032203602c8000003d8480081c1280501a0580f103001503541d840202c0e01030300b035a0002d402d00490b03000410801010580100c4d20106540035841d1501040d25603000050150a01d504d542d5101e0141980e080300f00c50081d8001d040e054132030a404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315542625 1250 315541375 315541399
    0x14190501051f140903010e0309090604090305040e09031b031e0c030a05032a070c050a0e040209060102100501090c02071a040b03090a120c1509020f01030213090911 72
    0xc004900842d5840001410030307040315001403406501d2485038000326000781c81c00e01c1c041400180c01e548100920701065040000c070b1001d64105040980d44c010030a560038041c05c00156030081c80d0f88914030540c260000c0507400309840d060305004030341518003010702c2c2000c480740b884005912540310342d00060140c60803614080d525042c840c11764006107902000307075041c0f030003056058410341e20061103249000f2680d00c036601c00344c5e102454140b00e0a1001e80340781c0c0300d901d18944420106050f8004034840ca43c1c0800401c0061108141164483c3c0d042c3d81e400041d40318100145d10b46070f0307850340b41003180d41002c0001c1a1030300c1541c1300c101a4989a800c45010710398804034544a00710801401d440c40600300001d11041895000540d000311918003103e041d1a15510f42000c000900d0749400001452442000180840c21040e6250491000f4040101206680c00501d910f65480e040300c2c10b1540120300640021454031059008003624031050100350803a1400b090070740b901c407603114458110310200c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315543875 1250 315542625 315542629
    0xe060306070f0f0201060515030906070c021c03120504080d061a0a14070c0f0e0a020c100c0e1c061514090402060f0a090f06020d080408070203011419050105 69
    0x2a601401c415140c0b20600544081e0440b203158a50500b07409564036644005155110390300c2e18408912081e00058032410030818031390402e0380191001c2c007001101002e0b000540d60702d0040c942c00100c0e816504a185a90345020f4960b090003441815902d8544010441408842e80040c44c1003080ba54041081580720550040e095140a4801c250100d0510090382c0c0e01340134000e000c0c22614481a8035040c80420368801001d0051350b00711602da40305203102000200b0f4902082500700c224607509506040400e20f02995615031a5100c2c0b038243e03150251682d0702801500000380344400034040024480300072300d0b48040e1406107002191094070785a889410b101c01510380700705485a403201041044824010054804805030040c2d910800420091301048030201c01022500b103a900c4010400d440c0000040c03d03140c40c0ea001c01c1c25034000160b41e80d151039218034459400303039000c00d003591030780003034008603005140d6940607a4844100006011106800c0c86141440304448032041c85140e0325001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315545125 1250 315543875 315543883
    0x30b01060c0803011403030909090f070b04081b0111100b0a1a0f090103020f030916080609070e09010908041d0c0702090c0306010c02030106140411040608180705040f05010e0603 78
    0x40901208414401031242d441000300170034540700000c0499040410000018040103810769900c0015030248659400071075052050b01c0c01070411520007070605161084840d140c02003041c20b480c1400c807000d002406d0b603004101c4c140c1b183c200c1c10300319400c10700c0a14421004050201e003261050850000c00900d010101a5491a00c0c8000d040c4034205a90003d15407450340200740d0780c5060540a0003504002c0013502c1c09181710740311038002400030a82d084a8100400080d8000c04180c0d0051010814034400c000344200849803401d9184015550314146540148859040140300c00c50000e4002944200010740540340c4000b9440c40d01c8644842c1003109103882413640081d0407001003800500c00400da21301440c2c0c040c406042c802c80303c1c40f40e90f0000f802c4601e80c0e00b141d0040301590180c4c05003410588540030a0400c54210031740780604210303014080050082009021500480c29100c2e00d140078000c1c0e00043c10302600900194040030b14103000b60200340142c600c103902c8400003070064030f8002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315546375 1250 315545125 315545147
    0xe0601060c11030c01170a02091504060305090a11010c08040503030c06070810060c0f020d120915030203370c050d1b0f030b06070503030f180d02100504031101020a0207030b0106 78
    0x107143e600004104805d1b000c08141e0051003808043e07400d0048083c01d446900100d000340b508070580070755940c10210b02504031400503002c00380c260300c1810042c00003452185501c4c48088242006110700c1100d1400021500c1242c010036050300020480c62491240000d80c4c50207030030240ca405213955201c1211800410311407182e0000601e00b052004041400424201c038040d0014045e11207000407511029107641c002c0c0b040c0c400090802008101e80240000b1790384c03040420786425171031403c00b00c4029120540704d40070040c102c0c80140500e400d46004120707a40054018900520080c0701404000c5c01c1900910a941c03100350500d00003a180b600810500f000c4030001e0b4a4044429207207180c00c4006008010540c1e4221208000c3d54002c00e600f040a18800d07405101c0401c8549405c0b80344007134100311504c00a06551000214086507031300800c0760b041e8810a0400020a0f560303500b81190501510034846105500c00903402104d55400b1a2410569002d0035040082d40d0380d5100407181d4003a00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315547625 1250 315546375 315546377
    0x18090303011509090e0d0906110a11010e0306040b06030705042d020418090212030f181807110f030a020705040905010207050706090f14010e10030e0601060c11030c01 73
    0x4000601c02898002d4101041ca042da20b8a80e0034a0f031141007460489070308100030792a40d80940e5948424a902c08910009045a8504080c941c00301c686500d580720741e4194010305441064661038181c4e48100c5603009040c400908803182c1e402c16040c00c403a03c2d8000d0318598000d014106000c200c9003014021000310b106004c90312100c000307540e064107031181c00100001051540030440041e00203007805c588020118000400140c41100d441005000d2a00a5072011030760014800d10107210050070039100c1e0051f00c4101a80c030f0701a031400055000500d4103002003051000b1082c0703d40558081a001d91219410701110121031510041950b0b81c01022800700060f880618207215034101f6801007010300340300c0c50002d07041802550741ca504064085e00000c0c00244200c41c2001109498a074641c020401e076202180000400400204028072041541b406144c8070308002844c07611a034050040c0755402c10a481c0c0e039507141d000042c241140041e0640d10301c030902803000441e1901180c055089481 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315548875 1250 315547625 315547627
    0x150f010303031a041d061302010203160618080408010e0a021e0a0b040b090307060806030c060319050a0b01030c0809031b0f01091104050906240402040902120105180903 74
    0x185a8085000d0960303080310701c800441d1480290182e132618000e0005000c2c540030310882001c1070701442d510b098401001c2c9039a0035140d03985ca00150b6004401c1310600300190951088071401070030003c1c040c0c034140e189181050b002070500d40c14058402c1c058070a50f181c21000380311110b500140303c0d039184950507000c0c1d4400c2c015000140380042003100150070710310180ca402c6450796207544da1202c03600181d101d04044400064003c0c00d034a820f201070000340c0b2107401c1803820341c02c0c800046542d03a450f440403280a1100080400d10500d2000101c1d004602210300510051900d1072189024000303030030180d40800d08200740440f096000b940d005106142c00703002541800242071400050000d603c041000350301441141802c03200b0280109240c644c06001e09000c04101d003018402115001056119107800480600c54239040303500c030102c02d8584851058078805c800740c3c00600244a1940584c165910014182075803102040d1650304840c0308441004880a80c80207400841c90211421042600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315550125 1250 315548875 315548879
    0x40b0702090c0c150a140a0e070501020706020c010309030e04021801031b080f061c03080405070b030c090f011b0b0604050f0f0f15120105041110050703050d18080705150f01 76
    0x4903242d1059200070311890200c2c0301685890104070014058451f6142980c580b60510f0000c681005500020300b400e20040c140d5078a4190000e49410246d100c003410562204aa0002d041c440c0c0000d10429100510441d55002d1100c0840402d15800d13140501280c01c2170010168030b0100c3c50020b403007400d5912943d04580d03c3c0c00801101e03c50080010340e01c171141c0f9200d40d030941000300342c0000592094641c107a05042c45d08103d803030109264001c910000040003042520100700d001d803505820241c41c0500400181c00040c1d0302c071051010901d442080310081c5800348550500e1a41c00740109840c00c0280e9100c50349000450302040301c203070f041c1142c04404a00c4004100d2040d591060354070341d0340700f281c0e03442400103045222007031a8001c081e0345480c2400305218600c600c521010030116900e0080c1402141d000c0c000307010f2058041c05100000c183c81e64044802c0d008402d02e00445a4207014274207891401c808241c002c910151454803925400c9550801140c41e0103000b886513107200400c580c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315551375 1250 315550125 315550153
    0x1817011d0a08130801112205100507031106070c140303100302091009020a08040b101503020706140901061508071b080702180105010e010804080706020a020f03040b0702090c0c 77
    0xb074026010708441c003101000000b5500000c1c4510381e0700b1b0780d0540c0c40c2070356001200c1c6100258408050b522500303901c1c040081000da07680008512800034075081003600d07228503003001d131005000c070010325645010300010003540581c8038000d0100e482c4124941c140403480150100d550780412103041288001c121010700252401103201584060307180700000c0a9030303e4403503000603600110107280120b0030000c02d100c10011000e00b00396104072141c0911407014640750300708048450301e0144d20706042d4002085014480d95400c81030444040c1c01c071200e140d04040c882d0354000c224034841c0e6000b10421401000700302d8401c0007041d001f0b150599540525132803030f03800121701c0c06204404552a00c810000100140c0341c0a44104042d140a40d54400395890f1100140c101200ca5000380d0401c00d07280c04001c0000c03a81c0040e079486580004006841e6442175406a24144812815142c60310004c070707002030403807030140050903c54802c0d074004200b900e407440d0750011401a20303d08000c0ba040120020840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315552625 1250 315551375 315551377
    0x22805150c060129040b0306010e09060307050906030703060e030d060f0e01030809122407020127140f0d0306050402030106120b01180e090706020c030601090c1817011d0a08 76
    0xc88504c0100c101400380084184050b9802a448103540170008000c102581da000380701c0380e405501c16600c036503240c903001d80040d440b941c40f8061680703c0e000010100d03a441e10308005900145a010000b00301d650100c080d510b560b6045200d20016203424007a02080030312545501404841c00c0808045280c0d00399500c10206801028005800c24070711403155001400400041000c15016503090710405000c3d00286d1a00400620400540e81003a200250484410031107000d135450144442410744054900000d403a1001e0821211340d11a50708014904a0301007080701400304240c50801c00fa41d610380501c41a40001d100c0c00300890281c0043d6115040c0781c1d08540c0309000149000d000007030040c030380302030809030f550441075280610700c04201300010108001c20103041c03580000d24a410000d000a540d4110502402d190b07261960078990b08140210000c2048103406280100340589400d5004070360400021400a558248080c40b0001b41000d1490703288513007483e011304180d0500b6241c0d940c00e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315553875 1250 315552625 315552659
    0x12060f090a0f1113050a0e010b01050310050607060f020304081201080c0a06050c0c03011a0102190c0330050307020d11030a0f020304050406060504030201020d08060a03020d022805150c0601 83
    0x104c40d111100c0c1d01900a140f00710303841103040e002d0000f140c000083d180c50859410a8455061080801c10301161010400e0180300b16501103800656501040c0740401c080e00e59400803021300d60010081c030040082c4d1401802c09408141e61241150780e03181940f039552024402d805400c40342086040c052288113000404246810f803045513510101140032030708442107148140004044682104c00943c0e0512a0b0782c50340f0804880380c011018141c4071074809002a120041c10790150422480003825401d41c000e26a49012107007401c50f0b405908013600d83e602c1240c0c2c000c01802000070342108e040c010031b090360b010b103c500010b6080209144066074503441541d124810740c4420b200014140e038590081002810182e42e94540319483e40c40060b140602c240c0d91001400702c00010840580c54141b401d000b200e4044900d66100007490020420108604424041c01c07003102c9a00c2e00a035480341d0340d4508595090354041c0e42c003080c0c5490f00100c0d000c0c186c0c62012a070400f5004000b0150700c01d20a4407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315555125 1250 315553875 315553879
    0x2a060302071e050d021614010f020f10090b0603010c080403180509010906090b030d02030d110f0304060b15160605040c0b0d0f06090b0d0303150512060f090a0f11 71
    0x516002c10018110b00d50029104603404d0740b003910800042c0358180b024002e0083c5902c2c440070700301c2c100100c2c3c28000080b500e0321030411000c800d1604806208100c0c40b22422494001d54440d05a4900313181c1c040c040345d0070305464020504c0041681410148030302602c6d01d03000c0d0395600081d201d66908694607a414612900200344111000c03034996154404d8074001c0c01c7c8401c000440500d031103070003000d64411610040c441e40018482010760350300482155540030a1081c005201111403010310312034000d4014000501002008000801103a64016503211000711a84440c20080611510340d0340314840040000c5045c0401100c00141c05030821900039100d19072800c841074540c0701500c610f0f000080040d60031501d43c02c5900012200f071240d41d0113010755080c1032014080365801714075000c2191000604041c0d41c2d544100d41d1240c1400c40002400004050032441050f141c11036684480079146120403070141008101200000603282d4a007560040100d0800d442c03544440d07104240d0103501503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315556375 1250 315555125 315555143
    0x16060806120c18060306070c15050901060b0403031d0324040c0302060a09031e020a06050904150f08120909010506070f0203010c030921080c0901050702030f0105042a06030207 77
    0x1003e540c0c0004448002c042c81030303c4200c80c54248105450300b0f0001d4485010710410341c24510219020030002850941011004541502c40f05905801001603a0107030401c80408600401090303400314400513103028178010024011304541c10503494184c0c00c07990071900b449228922600300f0020041c00c1e8450f0013054954511a602c1d00802c036540c0c0583c2c02c8400107518184148100192252071041e0780014107036504c4019025408506190242e015440034800049445802036450b41c0001507900c13600e040e0f090310300d65185802442941503019003c254000e544200300c800e140d070000c1ea42c610900800d001041d0340781409208182e0301c1000e00b959403000c0c010b038900140c0c50034001d503299500943c2d00026280014140440f110f002002c00082120304e51000c068126800440039410012089010ba601e4840e200140d40d14422002e00035098040c0740d0350700100e0300d0103520041c40303130303000e0241d5811022400c281803800c4582c01407400780030708841d0814070110340329901800a480c400d010307078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315557625 1250 315556375 315556393
    0x22d0106050310090b0a021920150106030b01030908090105090604120804090e0604020f120a050a11030c03120f070c05031606020d1701120f0b1003051606080612 71
    0x2083c284600d07801429122519010100c040140220314664812010001103040c00c5072902c2d080c07406500b003400c103001c00068110380511803100040304464a03c07044120360b80c01000036003043e5030100074800c840209250200c44101c950182c065000170341e1b8048066842c110f99040190781300d400c44103c032500424284400314050280400d40860940107009407a1507a1502e0360480a860f07469100114540040c420300c80143c403086d004503640802110200404015510f5051801c010607801521620a000c5e1580a012848180d018410419001d4603e24030804043c9960f40030065004521082c4c1004009841d0115101a18585204440b08030415568070b0010303181c643d01c0f243d480b220b1010390504001d03041c1c04201e5518108a00d00341001500d5a106e03440300d034060140b20320b117940084801c011080011007440b4004665004202c9001c50602e0850550480441e0008444600c6040352106024030300c4143c04045500581e5510750b0f0fa5940c2c800d004da038920b00306504101c0d200d00101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315558875 1250 315557625 315557629
    0x30f06060806011e060311161509030507020f03071805060112020d050708010603060b07290f07091a03060f040f05090c0a1a09061309050c19022d010605 67
    0x15990003880000c0045214400104040001884a0340000305047c036000c0c01c4605003a403207056070400866034208000d4603003a4148428012499980411550329000820040542242c01360a8540c000e607107040420003a40203160307840c26240110300c00030010721120210004144c1116070f003e4410724004608084551700e41d41640c2103d91902c0082d901c40080200c1c5540c000c2540d8014141840c05001080c40c1c604407a02511409401a161020000c00046000002c4042840c061119083c89503076241540007070b910403206a94100001c1c0440d000000d02c107089030110062035180b004d90070719640707174041000700d91803100102c550415103480c0820b032204181c1c41924420703041c03200503011010084e01005030a0400b50401020300c40901010080202c000301a11911402035444940e02d01180000300c5a2080651141000c14245070801c0110320000c0d0241c801248600140301c03200c828403400780c1c0c03590904d1009040c5401c06e00c1d10854528500104010b41d58840e030000a029515000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315560125 1250 315558875 315558883
    0x40305060c0a09180e0c040b0a0b2b020405010206010b1c27030305060f120604030807090902160b070f0804030819050a02130b0f030f061c060906060501090e01030f060608 75
    0x1503160545e59107010b01801c500c240811085910125020054400000002081c414007400b82c41e0b0700003000714103a600c120403070001984084a1000320072416121412840203036019006160050041000001e15280d14005450002c80e00001d0301e0a100890a1314000508a08540340c00c510402052040c1048024445003002d6009690100e46441c000041c0095025038800791030041204ca0110003050b1030100780560803079454034200c6411384525001b04c49030f0810ba000000a0313440090508014101c82501039107152040b00c0c0710a036076448420940380c50034401e501e040404c91000004000900c610b10b60395001c83c0c0054001e0070550005031714002c0700c2c42102e076510047e40c0010b0800c44a0400e01c0410028100041403a1802d900f1281e203050354040a005084402d00c884046480d03503031140c46481c620600700201280e54202400c0101c00780c21064010b640051a200021905e944100541c005485030390091408a929559a030071040d40e0080040d20003540c0c8504c003144c080c0041c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315561375 1250 315560125 315560159
    0x909060d120c02010305060a0602030f0a050c03040801090c0605121503190309080c0901180b010e060309010c08010e060a03030c0204090605010b040609140a0902070c0306021b0f03040305060c0a09 86
    0x96142075410b20584005030854002401d5a4800c2e00c0200c000c000240e4000125450103a4080314283c0f41c0c1602e8206a6450041c1900c15240d4000070501144a0b901540002c074841d004a109520440e40c2e62000c2d1441d20070300031018945030403580021551040e5807600134181c0406003c46210172100308030311843c061180811800034400d99002c00c0070b24010131030341c0e49010003200d496a1070351600c86008058058030707083e650120b8592240c04281e0707005554107044944054451940e0780ba0035404c05008059621035403000c00c44540010802c0c0d1950725695101c0e01e406001c82c50600d045483c05d64070400c20803812680b003034036100603030300191560055600030003108000a44841c203150707010380030314102d4018a40c10002e495840c606590b84c2803541c0b003181c1c208440103036184000d0805591340340d45ca400161005000007254980341001d4120750084085850540b151803941d205100d07101d1003607120103440c950040b0086450526060b008190150741402e000c80459500d18060304407a800d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315562625 1250 315561375 315561377
    0x11b05070e1e0906130222020304121803020a05040f0605120a0201120e1504020d05120d06080106180b21150105030609210d02070501060f0f03080909060d12 69
    0x1541c020710b0100184084540003000000a8004c1d0b140c0855881001075000602a200b031100220401c40034042241d003426444a04806554920303040c03d203400380f0510110032000240d12080e10355044424404c171802502e500500320071449141c07000700009403030041e01d4445959034500f4009a15551130804d243c034404044080d0140649900001d0b0201c08984454200c0900b0076a0103e03200001094407000b070400440d0102040c0c480cbc1c00400c02000790003400030441e1144210a2403c208844060028480743d840140135082e102d04681e800d0303460910400302e04800d0180c03c0350060100e50003142d00c0080242020440030a503803d6192044c07c0c4c4000444a40c11202030b200d402500010240e0142c03100b9001840142002480f44d4ad503846180700c030395103c061100503020011022011a0801c1e20751400a5480c3c8515060180c02450f10307126840b02c091004100080070b03114480c5010403243c120b00d01074103002014081c0500d1201c020422680510303a00c800c2c0300000c2220021800041403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315563875 1250 315562625 315562651
    0x708070302030613050601150e04140f0603150109050406150308041e1214010e070b1c0c0206070e0f041d060601051c0b0a0302120f0d0302030105011b05070e 69
    0x40c60040c903081c040050700a030f80078102c601410010800015103181192462420741071211710700b03902125590354103084940c0c03260820f0700c0d80d804a1140500796000f5042c0c0c2c80d4170215030729058100340e074941c540c40d9800180c62840f40104400155036020f140e000340640300c0811406403403000721400310400c2d0011070358051701003420b0000d0303c14090100c1e9542c00004500181300d0501922074039603605104014208801d5020104a5140a402101c4110043d1044961258842d44d000c202d5410516081d02c4007400c11218017090051801030f00311844440c1c015001d540c803600d80458040d90409245030b0040100080c6c90915204c80c41740340501c5070034400f0000003c0459244034100700700601210704100c400d000c140c05154104001e2016044154400200304100102280403040a503101950042c2c15080e024481a00440c00c2c0c4a941000402c0d03030310f00c0030501c0080d0105d00080c0500707800140245a0315044c5070f04288004200ad01036411104065030b1258004041c0100b10b0300b007022000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315565125 1250 315563875 315563879
    0xc121806100f05040902040e060c1b0102030105010f08071106070e0f041b2111030403020f010e1207060b1f0e060301030b06270a1a030d0f030b03030903070807 70
    0x150a00000390040d00c0740c2403658250b8a01900c0384140c0340c0300c0c003a480c0700707540d1100303041e04542d155805000200008000c0d18407516150518411170303004121480b03105401803407011007020047c42101d040c2e070416140e08448a034130710002c4070381312402088401481462640b2071026281044900d2149036a980d0b280c61400760328051140703032a60041000d0140c2d04003441960206075900d01d010311100349181c980301032208007101c2c8858107801078403001040e18094843c4a4841c0c6003000318800e600a40898090200f00c207211801c171606101030382d04a8000c0c20b0008550003d0000500005000302c81c080380d081c42e01c1000400b4001c0d02405404441c0700d2400e4416242c0e0002c03010400307031008031122404c8d58035548510282c490000c1800d4407130721808000004a17a420b4080d44005d00e5040c0c1d02001c5440c1c440b5031031004028503c0e4488500740402445052031070002030b1609140b00d2543d0341451800b141800f60003a245603041560300d0b0000340441180c6032410094000142007441c000e0003158 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315566375 1250 315565125 315565171
    0xc0303040b16080405070608130f050a020a0b040b0405061606051305162405070c031a060d0807022b0f120906050a11101404050f030901020c090c12 65
    0x200e69003a00180b081c030740c0410005c6000424000c003100c11500381851b0710381d11a00d040541c080070002c0201140f50100145081c0a000120546e185100740d415800c801d843e10480b070034a0260744909454110200014030041c00c20f0005801d50512400d140403507104c5556600080c0c81084541c1e140c00010400b011081c04820001d0075001e4041c01b25031615142444a4408011050a211146140700217090344020784101c0c2110b001e1600040c116907015120720300002160f56010031209110310410110398140f45c42c1d4002c81840ea80a003c46103444220350a000c420710030b00c00c01ca4030440c0e03052541c4140c154180a410782281c403030030421102c00305502d012540070182c0f03502082000305809003842016004001c80c0d844c80b40601384260481054014103251440e0315610100940c1000d025101c01c4480300f0300341e80128030440949072080c65105a00742d41e07014200850b40143d00c842580010b504054036403503040780c1d94007801403418029406141100406a62014001c001071070406244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315567625 1250 315566375 315566401
    0x40203010b0603070f0c0c08070806041202010c0503070e0d0b01090903111531030c021f09090f0e0f03250b0a0b040b040e010e010b0d020a030b0702030c0303040b 71
    0x1600040300c000d800c1d4104081c00401c0d1070301d0a03844900b440b2544071201b06000204003030000034041c5400301d814054985c0d21050310b0340015034046580f06003002e009a1201d0041c0140c0c7e41120403651058210f03036802008880c21310007940242c0c0c1019240c0003541c04110381444841c01303450032070800b144c009031914008054580240d8022000d0b0000c0c0c612142004048114a130022046550300012080400a241c11035a5460000c00706581c008041400c142d0480781c20f205c400e00894802401c1d250140e16800060100381040000440040d414030064410394800300400f0504c50700051100c400080c281e1810081320404410b030f074000f0909410811103040301c48a450b8115a001c034607503085a8a81c17130345040182007036001c0d03a15600c0e01d08641d00d035030384400d81d4180700070000c1c040c10040044041c001c2c44206a080c0580d42001000d404078205a40000d4019602410fa07c902c2d51440e120340203c80030161684085000412a62002c100100040d502540c000c42452406007844809201c40d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315568875 1250 315567625 315567641
    0xf1205040f0506120103110a12050c01080a021206040c0302120c070b0c0f1801030e031909050d0201120506010302040317191b0b0907090603060209030106050a0f0312050f040e04020301 81
    0x3003100c04105058034030131000c581e42d04581d1302008801100b030500c00000c0c4044419004141c00030030755007015040c0b0100003400000c418084e25040e443d6191802c42c64141e21070074000c0c022140702c1d42c01150035070800d130f40a0700401e105450010f06001890103845003c0d401602c4000b141100441c00304140400300c040c1d0742e002408840c0b12850002220324964081c0102080a0030911fa1b02454148590094000ca507170881088140c4c0d640f03480c0c41c015180002c903411300104c0007130420a03002c94035050044203120724540584a8050943c501020340e40030b000b00504543c10035400b4003001002480c941ea25644104617040001c1d1101c05040c090003140000e140b080c410000c10807a6840100380355100c501d0720503007100030141c4580d02c0c0074403545407070980e9005504440c0340290002c1444084d44c054284240200e000b4080709a071402044070403044d82c040d441c0411046801000000e1400012101c042d003541060b9060040043c401e841c01d40040d8403179550456844200000c61400388241700c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315570125 1250 315568875 315568879
    0x9070b04091e0212011208040b0c030c0106060201050606072d080d0b0103090f0b060d0203030313050c0d02010906110f0a0309090b0d110f04110304050a0314040b160f1205040f05 78
    0x410546004130340c0002d01c10603c50084ca07600400308032024001120b0880d8050b11040341065a2181d4003007800e5900d900c0080070703d030b40e2b504e405408101c0520600415024060080110b81007400c43e807180d00d42240e18030032851a24004640c9001d002c0a1940340001c100c0c001c107000f0351148a034041110903241c000c1c410750304041c6072048070720000c0d0584683c45035003a0006501c1e111036903004085141c11061041c065410700c404000c101326060144443c2c1981c070300c510103441244851000b8000301c41082407009010480b681c80c148021031044139040070340c00e2850102e6810320814011503040c100102001e07400103e0051040c8900c00c503500844111240540d07034490f150300d180e141d00c40300c80203551580344507a29051800d000c030b41d00c50700014041d03030300040010b64900303041c0f034850394506042104801249415001c0210340342500c00b81c800311034a503200c803443d041e85540210400c030f001d2541169120051440c074000b09041303100040403c0d00c03a840d895070769428038031140207070120750740494 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315571375 1250 315570125 315570127
    0x3010312020f070303030b1c080309010e1b042f07030305070f0c06020a0509090f0402010e120c04090807060f06050a090e03041a07050a0501020403120c0b060909070b04091e02 77
    0xba040400010300c0c0c41100d4040c5000280141030130005030080b80303400c040c007074400001c84912052229541c010f40c0507980020080011145001032241c44030480d1103e202d040c0051980350103a401c01d60403401d0603004807940742c9051500000c040a88981d136035a03e10031098040341e04001c15805100702c0b90024060309003800300100b0610001c1a413513507060000c1099801040802c01c09005105840b110031000301007801c58500012000070349102120107074002826140880700c642080e10003140c020a10308041c181500284023800b02902c40007604580245040101c00046065485245488500004013141451400c0200003407100c1a8200242e154608003591405000000072a004c0320100c44000c0081015130380810620b004d0250003a01a000c2e00b4000c508201040d4010420389104410800c185005004102c400801d5084002c0c500d40c00c3c5230114020786004c04e2001c0d40040d1900071140c1031911000c0281080e00b0a034440907065407200030b0003c00c86070b450441540f03500c041c0021 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315572625 1250 315571375 315571393
    0x6021f110309030a1d09060d032307061a0607060b0a05060715050708270c1c12030b06040905090f031b060c19230403030c02090a0c1d04150303050301031202 69
    0xc6e00800015262904c80e00307141c0c100034205802042482801507025042030b800140c1c030003209a01d50b0180c5d508648441c40d040c01c08600c03c41345600010400b1001e011581006040c1e40c1c1c01006000540846070700c1801400b000480b5500c40c002418054410644c10410b80f089003140003e80744050703e0780081c0086941040183c1c0c0d900b24084540110161034105203c80c8a05d00a0903e108404000e8105064490b0b003c02d04040984140b0440d1148170a01212428550210200c1d5081d00d4000d41c07286007008100850707401a00855044800c45058480d525044d0400d107165034003080940e6140c8403080c0300700d07041100a11030321b9440700c0e010b8206403400b40d002c03100d03601c84209103c51b00d00380100b42034a68501d901d600300007901c04410803a990354907901c0b800c028240d0008210101d00c26100c9400152150400340280c0b0241c68254417200c8200041401043c07601185131601d0b03400c156070b10200444c000501c0408002103003e62100c5580b5411030030701b07000e00c46a0f07603d00c0c81954801910b03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315573875 1250 315572625 315572629
    0x9030c2c01050906132003010812070305071227080d031802121005190c050c1209010e04090b0103060b030d080c0f0432030706021f110309030a1d 64
    0x10003540401c00b182c43c85008041c042c20391700100100c2c048040f91590600382004040b00f031500442c10307140380c80d0850301c2d402191205615203209114004000600910150300064549000740403061880d0409440c0504c1c90183c020044a4214440c1c2003911044010040d5400a01250099246c40d1800740308c50319007840341b036a00340b05a1100a0041d40e47c0c8103803400b4840d09102c290b0b28110000020700840c1442e0748800101481d041110207002e02d4140c0a00301036001e0303403c0b680f2203680517001d01a04410041d140c52607800a60b40c040c14418003c0303540e2541d940724805c19001d6445901101159415820550101e41c50700814500030b81c08507980640b41078020f0380c00c5074000f02c1030b242d442e03a41078048064816800707940e00c80b1043d00c1d903201c0e000302c0f140414a85501030581e10f20506400f08203940416540d41440e00c02d01002d07802c03c15580d100419103544c100309220180744d022440200780c88101070b403907008451801041e000441c0400410358000c9440507000d50f0100f00503000025400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315575125 1250 315573875 315573889
    0x40207080f0708160807020f060301030f1211030409051504020708040315090602070f1704260c030706080a0e07060e09100312020a0212030c060c0a09030c2c0105 71
    0x19040003000c00c041000b804004001084440e188071801200203000c400d4508541c81c0e07041000b08a1040203900035040c820b06104050f20b0489801c20301401200416480348101000859030b400b04002008100c2c0f02c07040000c0005000a200210000455203821340e0070b440380344125004240310718010003103130340402c0b103e00950701a41e40021000510004c03400c944401040807060040400b800410741c070040c0a400c80c102c0754540c1c0078407101512503030b4091074015944618000c00304103186070300d80b60600030002002d040f41540d0300007c4031500d0007140c0029180c00c100e64060400500c4a100304800d1040d42c0c010405003c107030a00400c3d41d2801c0400c00792122009043e864040e46144001803c2818007615180041d600300751070f012003520501000792640b1a2400a82c0107040554001030b41c21400001c59842d02020400391803240c460340808082940400400c0c403c1282c50080030000c540c0e4113a00d04000c150b0451100d040f01c05810803d1144541448803422140c0d400c4010800f03601c03408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315576375 1250 315575125 315575137
    0x501050f01020309090a0209131a0f01021009030c0204060e2205100b06120405100e030403020906120f07061d01110706080c0408060118200d02030a020c010510050a0504020708 77
    0x2641701c0e4480c1c0d2220804c50090260480403a800241c8503441080b0380301e0359000100d1038901000407a141d841400038001081242e0200b540113074001440012019071591044030420300c01e14118101400d10340000b02038500f5504640c0c40c5042c81810b10501001403140b50201c00d000c00390f40640071341a512040d403902d513840c00451150792030311b00c00a1103548200860f4030380884c1e002007503070300d06050401d941c0e224074034200c050f001840c007540f14808000020540702100e600070040b00c800e80d21403040c06a031595690841c2c1051140d640302003c070440c144803180c090b0526035071701602c92010101d141d21001403502d855050103c003a1020036605800b0070124156070480c1000440794440f910544494441c0360b1000180340a280001b14543c800e003402641e22000c03414007481342201064801895400e00052004211400c000e0840070700402d80185520401c1d02e400181031a10448a250a45000310707039103030f8000a1a581400980303016900e07a405004155404c6040c00f000355075107403043c0b00c2ca03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315577625 1250 315576375 315576379
    0x30702091e2518080a05010902090106090f03060c020f0601060e0f0901080c0d0203030c01060e0109061a040e040618290601050702040f200408010f0c080a05090a081c0501050f01020309 81
    0x14080d4040c42c02d8912084001071a80d0404c80c0e84a403500d046c000d008002d6000c003203201e9180c0f48000281786200f107071000d0036101041c03240c420640c03039a40d40b8001411411034240c10740c0280c81100410400921160b40205481d1329000c4c140c00c480780410007046280500c00c3d1050051340010f020b285000960802402c60a4a11407401c001c640000391541c02180070345004c542c245480400c140c40d110072860304079010403c0a00c07081e41c441c42104254424282d000040c401c0070700c410054040f00c00c54240e00f280c0190000196010702105c0114082511801a0b880000102c0c142d030106c0f094103030082515040c141d00d145941001e20008041e40300d840740c0a40b2540d200c2091045400c2c2e5139002000407003108038900328880001c90301e00320541162007801139552900300901c01d4941c076401b4012100c1038035903403081302c2d0303542d4a102c400405000d05a00042c1c030030f90290700700058190f0010000000c1e444a0240a2a1038485000c15110160020741c020740d1000200d0309540d07000403e4411030101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315578875 1250 315577625 315577637
    0x3030507020f03040b0c06091b13020405100e1008090607120f0f05060a080303060108130f020d03180503070b0a140d2a0c030c02040e030702091e25 65
    0xe000822841c0c86000d903003060302c60100040c0020303640c00710030040819824040540f22a5510b60440c1a1502d038084c20140f51007104504020321444e0583c0301000c03241c0a6080181801e803200c001c03450361025032900c48041400a0284806c40ca410035909107006241c0c0f41100d0640ba242c2030351030f00e842020384814240006180000714500168018500c0c11001840402c0f01d0341001c40c81402910080d204540100407215011822700004001c603482a036040e1619000b81d02c030725529600140d18958281d80c11940320301c118006981d0550202c05160288d90341c103040c5406403000d00320f01146680305034801d0348542804c1240a48110580d10b43c0c41203401e21903140c10010054105520a103070b0b400f81154a040854503040d854110303124240c800056514112000c841c100b501c0a1804140186c0030034070344c0d100b5100529058100741a002d086506a03420070006c0e50215514240c19a0302c4210008030305090f100001c0207504a0798005c0300b040300605200304421544a106400da407a10081000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315580125 1250 315578875 315578881
    0xb1305060c1203240306070f05070f0b040c030b0c07050c19050909060a0c08070516020f03010f0e060c04150305040203150109020706110405031b0f0a120302010f02031003030305 78
    0x100601100004445815025980b40351004c00c9225244115282c0940f050b07030b20b01d121489050001d00c40b485241a602d920034582d1850780223685036000b1803022100043d80c01d07055000103560622084c044c512503502d0009560851a2050388180014542c050b07a8030140062800700cfc0000030111410102a244600c562b2600d03422420340640680043d0b411071201b405001c1c840b100000d545205046644081005140040c81102c580006440a0700012014081d4021407a4450750292a076817000b0411404900388074003082c01d562400c40061082696000f10080c61802800401d84c05803443c0303403540c6020700f4140301440f5181c540308000c08041d07403000040d0440d00c0410840d40000500d040590b01503a54189180c0650f10203042244e0b51801c2050032581000c815080d0780070764500070701402d401661410301c4648030616101c0b0540c44241040b1810040d112500c9090103095034221038170414841e0f08010782515032480c040d4950b54410410000344240788940c0c1401e403070b810702c1c010406031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315581375 1250 315580125 315580147
    0x20c090a020f0412052b0503091501080106031a010e01120c030501020409020702030c040506010912060f020f1e07212f010b010207050a0311150a03050106090b130506 73
    0x8011190000002c01e800540400c6208901c648a50300c58428000c541104100f1401c0004003411414810341e24004002008a810300030340c00355030302901d000226602010360380e2540c0310380b0701c1c01c0e88180303c583d40d249024400c3c0208641e009101030488001d410b104e500d04400759117092014031424451219000c000c40805c080c0310b8550b070045410200a41d140c1d51101980b500135800144128440d1154042c00781c0a0309090040d68822031050710b9601c1d074070b03103003810ba511a403c02c100e04071500c0b60f890180d060f282a003840a0041d140d82d0414032074540140000d0500040312103081c9450000c41800032a000a1300c105001621440c0400007203001c40d0302000c169400d1810302010f4044c5d001c42c250031114841ca5003454038071012410020b0002d8000b0000598485009000700f6402100311107061000c2240c00c10720f201505006000001801400038a01407140c01104802c000241c0b910010000260320a504c24007404005910504e00040b851205d200c40b900f0b441010300408010511030029 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315582625 1250 315581375 315581377
    0xc09060221070c0b07030e0108010819020f0f15090a0b03090c0103020d020f0a0c05060105010c1502180901090203040c0509150409060b0a03050718020a0914031009051c030c020c090a02 81
    0x14050352820319107170140c2d40750242812007228080740c0003c1d0304000010f20f03000c3c00644060509002c402685840c1100d40a11138030340e6044944580103840e040380c1c20016194600615502c01062001a403a400b59008000c0812019409403465170410f0040c072402c40800b1800d40000c90302400c0c0164ac0380031412150300030740188441d288017254040b0b100d03c81590822060fa10303a030320610a03140c10b45e803900015580d020709000090049403010103c94540d44041e40140b104e05c001d4036074032102d80182d2001803030340c6809030800710307504d0340110601c81000b01f8044440007506040f14040c0251900503400c4600c03c0070150f405210303989580d80542400740560010695103009070061082e2134681c02e0079aaa82414850741c1814401643d0400a91203039100b0785813240760303540c1c514001902e4410350001000400c203c09500d401403400c080c590103e14418400748601c1039010b0001004070400c1d0030110010b844600c818503041100500300980c2c0460f0701b0014032011207410051b03880d04c080c10002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315583875 1250 315582625 315582629
    0x330819050d020f2e0e0c0f0a080d031a0307080a051c080403081018020702090a0207030912080408010f1407090509270f0f06070e150307030e0604060c09060221070c 72
    0xa0702e440c05e000600126004602144000c1054403184001e8181744244000e240040c0300d507218a4010322035114545100b038210450f403803440c1034020340c0c0a60042c00031382800c02d80e52101d4102c0c1e2000102c4c008209050010000d40d88124031201d12001e89100090806540240000c04001c0f01c080040c404842c02d800250190035003100d8403050543c24072020009502c0010241e214070403020000d03101e0742c458000c0314000c0d6410341e11030388204d14180345010392003800d050880c0d200300e0600c004100003000748030700700700d6803807050010814083e4880b43c401380c03120140c855000c12449180c28042c5032206005190054854100c41c030102c40d40d03201c020304003100f013940c24070f8501032410400400c082c00a51002d0355903440b819135101791a03e402c1a58200c019510058120907004c241459100d0300724007440e80310580e401c010524448071225a81851402c89080f5860741d80c0768000c4161076440142d21000d0042d5000518005000d4014489c980c9a000790a100c0780e000064100c00f0481c0008072400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315585125 1250 315583875 315583963
    0x803070c050f03040911040510050903070e0c0d2306092e03050c0d050706081b0c0a170702010203120720010608060a330819050d020f 59
    0x2a45044a030442c82c0c5a5100348140811075042c41c20820b01803101c001103400b207940007404000b125510603001e440a030040c030100e6a2500499074002000c0101da451103100d5191090010740d141c07081e00381c1904a500310860001010444140400307000820240301d40c0041048601458951b50181d4502c0a01c018440c070041039004070300c9982c016154400c41c6000d4912440544545c001c4c0d020501158603680e107005080ca80c400c00041000302d00500030396030424482082110700301c8600081d50160b07809090021710300d40c01004140c3c14800803d240010503d85048075a02d80502c5400003542ca026200d400110081d101010460701400b660054900403000d001c01800300c616800010300a01251203140c02e140900390000304016000c3c80f420b03030b0041c4500e907400751040c0e03071911840500d602060341c0003d90300d4003d0003184c03139602000b6807400700e01c2854210034243c0301854020b082c00848900c04007035500c4480d100898000100382011a04944980e2041c2540c07012100115642c80c006903007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315586375 1250 315585125 315585133
    0x60f030216060b030f030c2a0901030f031b0f12180902030c1e13051c03030203060a0515040303020c0a1202060c0c0604090e060f0403210b13140a09030206040803070c05 74
    0x601d0040124141c078404040c41e451601c012340c2c1e600240e5100c0003e0150390782c02075000b40180009848501690103060107450480582034203a120900b40100c00c043c25540202441d5003082000100941144601614540381518040e00d00070700f48031040300d02450313003400d4000c07001440510340c99058400806400d010b9140ea10760848101c08180d0040b2040c3c080da0030b102201250a00b4018803aa200d072280390a00c0c8080d000304e031022002500003030003495000305100e00005c1c0e10744d1840e1404aa4032581c0b044a5592440e52602a00d0040324a50550040c0c02241c070421443c00340382d0701c0c0c0e1909030b01580c040ba600c4426511842c1003a0b1102e0125901c035a01007030200e2007491035404002414a010300700e074515116178500030f440c00c030110b8000380007a01c1040700d1407040e000031b08c55401a40c009140410000c5a05000030380001c0d507648040c0100e550341150402c40f02c1035a00f0b1641210450300100038105203610020f480c0c5800400c003400c003d0000022414191160100d0040c26410400369 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315587625 1250 315586375 315586387
    0x10082a030a0b100605070206030609070c050f0709060905010b0a140f0f041404021207110a0c290406050405041107080c0601170c0108010509041703070306060f030216060b030f03 78
    0x7032041d91040d5000c682d4480c0f0400081007a41c020303002c4500154000706403d055039110420810080307002041c03a0104007145040da1300041d030030040c9190000700c240240100600304090394084a80c0e40e0311520859050900400c42e604401c811240010464509100b90459100100c0400e104000b014491103038001103031150302003040080c209880041c141448000d5421003044141d000707642440940c1c0a441000c07a1646001d1200030054140324016200c08064540341d1400951840c1c0c8804c4011420f60802c1010b03400326164000070384190080703141010b0501d0001040ca008500405010f10ba4510a00c105c2607000e00c1078420003540450206c2d81d503061010010b403540d1080c46800389841c203920b4100540200807818540307421043c0d50302c0280307078030700303010000c2065000d0002c2c0c4010114010985a10404400071440781174039490101e007182c5000d01c02849500d2200c2000c003017610600c403410703581000c9240ea00005412540100c2c88913030380000241080207002c81c1002a100014031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315588875 1250 315587625 315587633
    0x3030c01090303060e0c030604090309080d051801050c07060311040f15030524131b021b190512010605090a0f0b0402040e1b0c01110d0510082a030a 65
    0x1e031050034407950b401e0160558407840f4205620007521209864882880001c10b241441e5210a40341c1c1c2c020b00e00038403810360b10200d4600300711318400281d00203040021502c2e403a240e19001e050602d5004c1ca00f10b4908611003400c0c2d9244c8216000d024100340d151b1496259610070300007500c02401000c00407031580e40c1d4403a003a07610303071410190140c0070904100000d03404c4107588001c3d440c1e0114000400c117210a04000f0805c0d051100f61030750f10705a507100b50507403400310030a10000d8510101d8005110703104003c006070a41e00403010903988110903c401e44203a844011005008403181030350140044c0d04903104035800341140ba0441504104840c080010100b29030700030281259041d8000c006403684c80e4144402da03c194040d0600488107200480c241401805001c00301400060035141031004004104c1d00752548801580c02d5030f034010912800d0a9801d1140c960820310801d2080c0c00c3c245414400c03920382d11500c8042000d0301000a00200301004420188103011009064038009402490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315590125 1250 315588875 315588881
    0x18090f07111f0c1d0a0902070224281713140d0311122e090906050601020a0c05060306011106161710030609020f10020109420b03030c01 60
    0x4103d82c002008003503080303520036040c850741c0342485014003c040b80070b0600350039001030340c44500100c0e0040c510348035449000c0c1514000c00c6c407505080a07030550f150000300c900a01422002c00e0711021700ca00700044078003980c00041c136801610040000e41c0325551410200d8810104142e40503005286d5601480f50007040891000c011044030b4070204030b13980c5102401140c40c0a24407400a003d41e268000c80d03001e82c54050800c00ea511102444a4280c0301501c0c1008420613940c04844c10399120303038044040200c5406280d40c410380030b100a26611807242c5402d04080702921a00f801030b48000302290361a40b01c7c041845801d00c1500c119001400c00382c0380441528014140703000001d682c1030f5440110440441d001d400303502c003500d40700810350461b15a40c0091880b490200c0e030150b01c030300064240742c480d10032218694030340360000242c0c0020b504040b075074034070034000387d1040405031003004034003882d90b440715089140c41e4508040454650300c441001031200a250b154148000b05029102c900150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315591375 1250 315590125 315590141
    0xb100c120c2907090b2d041202030606040902130c050c010603031d01020604240207140309010e0418111c0c1502030f160201020111030c18090f07111f 66
    0x942c0c204025a11200202c0352502240140c65078101e0401c490b2140400100d01c19130000c1e0511462207000849000314021540a94005240952003201170001c4d07160a0081d55400801a54103001240e40c0d540010002c0b50099200c1c0039140d80c0310011840d451152058911040c80c3c44001c118060301d9080250025800c0f10b50510b1075007a0821250480d480498a180201e0f80018481c1c081d2020703070003c50682e80f05150009080f5030a00400021841d03580c001036045a200c0040c5540b0601000010050300d0342110550003281400b180305c22024000039844495a004146c81e140c0e0389040700081d4042d207582101c0e900d090100d0105101740440c0400f81301c00c483c281034010055200c8245c1c140d07108d0095603000155408103001c03041d40603206014440d100c6105100000d0850f120b50744401c95900300b27452142e02d09002003801d20b8071700d440740c80080b00508200c400740d00380e14102c0041c0d01545001045d000070402280741c9820620360800c011110780402e1080501510202c03a04000100401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315592625 1250 315591375 315591443
    0x901060906091401030b09100908030601030c0306080c041503020a060215070e0312160c09050109150e010311130c030b0a050913060e030c0a0c0503010b100c120c 71
    0x80200081c03a4500c500c1003698400031003c070711860341e00c1c6850305011402e006142081c1402441c520f201c483c00584030f207259582c4201a00c54a034244000010101c0741210404824180380100910007882d00080f098001c2d0012034012900d44100070403c200d940381684003c1d0840703012580800c005801203076503071b0503a88945050400c0c0e9600f0000701c401c4482045050f425400030f0041c0075410f0302c0071008001c05031803000c0c402c40d500303410756400150240d10b03401381d080541d456005019110044c01240e0100c1c94560f034140045040c0302004000301d0040c0710080041203c940c203200b803615a070100694a074031012007086841d16601014003d85594861396204d060f400c2c00208580c60540742e668015000d031060304010368815606c4000a0503180c041c0100303880b0900a100020300100003800980b8803840c0704035210340c81c01c0c0c02c0c542581d40342034a803489003d00c6145034200d6640040c00e50300301a00100030107901c2a000b03038140d606c42c460040141c0940300041c4125004051104150f901400d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315593875 1250 315592625 315592631
    0xb160308070903081611090a0614030a08091002010b030a060204050a0b280216120203060c0a05031308090604091b080105010c080c0c06070b010317031009020a120509010609 76
    0x21a0700071540400c85000040030402d040c400990040b5030300001d8410301e881030386400c008068450014507030340350413141c001c03c0301c8c1c0398841842808540ca48650039500c00b0b400400c01d501d0700b45c0d207001d0140910a9024040c6843c4100c00d41d9603032003504545203054001d0b0070f0351002003032400c200001c0d5106002d00d900580400c100054101962800c0719503a042040e401ca03119408031043c01441054030041d281107108006100c002400d803462290010301404c02440c041c00400c0c030505082050040c20340307508540500c183c210054001c82125030151519085400060719450078030a2030050010a40d080040807802240040f042c0d070140c0d2aa1040165006d00a19030320002c0384c0e901000d01411f4000f4201100480010300103074007410580d244102a03415080d6054041400390300040c1e0155180c280c6807004000340080140740340304c2d002c21420dd0900d18501a0501040090700e0b10800c40b4195000400d03882c264810742e240c20f070a5040480a00040c1840030105000c3c100c64080c40500310b207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315595125 1250 315593875 315593881
    0x31911060309150624030a0912030b031606080105060a0201090c0b031807050a0b16050307030302130906031122110a030c03050615070f1a0103031710140303040b160308 74
    0x82d195920001044036800b0000740505e400c155050940c10150010740d102e41c40c0d03011030b4002404074403c8800c0d000ea0760750025141000c402010f240c526901e418254802910700e06000c0341d0b510000301810741c1c0d13040e940d066441d0300882c012030040501540203002d0300c50200e00400d200400c2c5000794014902da42480000424031140d4030348492203841029440290fa0100f080000c10440140484d94440c0c2c640b41010350311070301e8403811030740030800c01c5002a600060002a1840300c00c0d9030303009892455020010f20b800c43d034440c40c41008c2e0030318585c401c0f91a01c0c05100030581804601001d9041148103112094400540b001180c000c0400080800c0c1071481550483c0d20074071500b84200402440700707078079483c00000324406601c0321000340c62080314203005c4404149115508814000340fa81d4a190350b42c51070400074040910b10300b0350b18440c000c440a1000021301c043c0300005845d05036150311130031299100040e2175449598081040310304045101c02140701d000146880e818002c0e00c468210740d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315596375 1250 315595125 315595129
    0x712020408150c18040c200c040e150a02030a0605030a0b0405010609020c03030123090f22030e0f0a121a0a0b13020a0309201206060319110603091506 66
    0x1020340191581e81d00c611001d42c4c038840c5056040101c4141090a16108200302c52031094014000f05106000c1584100d403048002e09061103080b0326046848054030180b19011203501c0766040282500d08159000700204a40d01c8041c0c1c8090002d0070002d04482d694100351a0440319498215001e94a80d441c040001554102c40d0080743d655510900282d8650303801c040d11407404606244403090350b00c0308100700d414640c0310b010300c25008070700c020007510040c6401d040c03503130040303100c0035170042c0041d001d91090b0f0000f070300326a0241a5403000c607140100c0c1e801040228032209216400b921059100302120000c1c4500840c0c000100b05c140440ca51040c0c1d82c01060f075007602c440340070250700019000389075511022150301520f118805443c021500040351303244c00c01700301c0b8031044000101e840079021003a20700e0180004940b480c80017020703190034500b1400103621007060b181501c980303e40400b06181003207030039202c0d1304d105c440041c0126200c0c00e000500c03944d1201c101d01d00c15401c003648004100ca81c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315597625 1250 315596375 315596377
    0x302031005210106060804200109180f050703090303050603010e061819060e1b13091403360306041419150f150501080712020408150c 59
    0x84500880d2095000d00d44410b100318540324a854008041d611480e07001d000b882802520020941c580c0e82460f40d04050400311110303c0c601c08c000b1001e85004e0628001c81e41c00120f0f40c0f04998070308010708002d80000e0300c00e03005404c1c0786a501d11158948410440d1f8a41c0551201018601030384d020841039607908181422074695100d54205c4d60300020019401081510014286019400a50348500616200b0110001c1c4c0e442007115101d8aa0541e201101e804000781d0b00b0030700c0f50400725138a0700950801716500c4404c80418001541e11400c9001c244144000b0000c8094000c1040b03999803c0101c00c3e044010300f0301b0320983c0c803080030030f50325031609030a0040400071104018042c1095454981d203c0c5a07030440c80801003882c4c05244079201d2516154094040d9070750150140d040c19400142450044071403590182c2c001a2401c41500b458001491a4500b0b803603082c00d026000d030321000c0c000e452210342c54101c880003900000d00406d6444011500c40024246070701030b612943c80303840d440c00b03c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315598875 1250 315597625 315597631
    0x10060816080615091f08070e0a0b010801031b080a0c080f0303040803070c1a04060c0801120507030f0c1e05100503041104051b1305030c010207030503070b0c0904020c1507030203 78
    0x540b07800c0e14002a00e140c41d880e002c0e0029003a1804031170450028051036130100f00d55010102507000040b080146101c0c204e9860b03803103261924100000100c0c0030000c1c2500c04103003c0640355001e001d00a8440c03075040038026011349114422603210310f643c0e252081c680c101c0d60040503520b0003122400381031040000140c0740a01d80c00b100b05425603a0321781049030601c0407503606aa240c01072901c103501420829003075a000b1401424040784480401c580a40b05050680c0111300400d8500f040c100450004140034080e29441010b84805034014208a5406800358200c0041c03103218084608a404031030352550101c0d5070039030391410040b4040c04140c0361400300300c602074854032224441c40c0360740c903181d07024a44c4980e141d500c84110b0fa203100101e00c03242d04820000d003001006011b0600a61600700200214100c0034070091a42c1d0381940e5800b902c9004021005090685000200e54aa1712000a94070407044c064000c54030790115807601680d03111010407002d40d000c4100c000c951700c14407038000c40b48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315600125 1250 315598875 315598891
    0xf0501050301110c100b04021e09190501020a03030207080d020a180f05010816031d0309090c0f0a081510080a140108030306010c0816060506090a0c0801090b0102100608160806 77
    0x382c5411485c40c0f0902518003030305003d078050703400c200021181440c0d4400f9009400302068a40d21000c180c428044035031080210061042d560850800c1941c0c1e00107840703100d4544c035140c0913072125010300c0e094001e4064509009402c9001144244020780e0100c100c0000b89018021450110303500c0f80c0004840c0c485000f16130002c0e90b8000090004c608400920249201ea480e00142140c0c1061603240703004d501c491448a0341d00009180865031400640d04c507000664131507054038260401307105500922685e0300d21000d2086070300000d00500b50150303007000303804030281580886074100340b401003080c03400b141c0013408a4540748c08449c400c04c02074401416107035040010b41c5580c03601001510364142000045446010400c03460341d0300048802001e400c01d1141901040e5810444100059541c005117001070040ca4009a245202c3d03010100c00c0c11900d580d1000102e540000004070f09001321003058000d15030070002c0004070000e0002d40c043c5524015804215404c0c1c0360350000e92a1502034a03012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315601375 1250 315600125 315600133
    0x1204030e210c0103020912010f0b180613090f05060c1312020d060b030304180204173702090403021506040b090c030c041205060403020d03050f04150f0f0501050301110c 74
    0x2d495019500511141000506660701b0251b425001400c1d51086440211102e032103000c44d01c4681040d9090701c004c581015000074003458440d022030783c0d180501e5407441d5100d848040b8582030044807a001c031081e9070401c081e40c43c7c628010000c5042680224100610f2035844c1d00002034070300070060f480003080e500808008060b203064403002e0140500d812030903810700040200003003200702540c0e1403036205601c000143e103461420004100740c102d000703c0c40540b40c00c0980c11029011058180305405042020510031200b680c15040000c0401918000c0d00003140c2d0042c0800e15800003100402c0802551000075240d44650501040c1c60114088070381081c440004218000080c01c061a44403000001840c1016035600784d503031900c810300710140c03840d40180003400185603041c01805030341643e9003002d00030380c102401074095545000340050540030611603450820078544d001030241420350001806605030080390b40000300b00030303c90180b09600c0c10541c2c1c920b04503c4401e842c94500d520713010f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315602625 1250 315601375 315601393
    0x6070c02061e0f0d24030c03060f02071e0204051008070e131a07030c170f0702010905010c020115080f0316110603010b0304060f050103081e1204030e21 67
    0x41e10400608000141c501c0401e10008420610100140c0102d980c000000b203074180c0d2014004c11904040c0c0d0500030001c2e2171003018808101c0010750601120b0340b01c0c10018080402600f01c0000340141c0f400280a24075a00ba80d12900c00d034509803604042c02200c0070000f580762000b4011800035144503c00c0d40da004070b00100030020700d5a81c030701c0e84901070b00301c00800c0c604655655502030109160340080140480184020f4039814030071100405120b0a240b0810031240980e00300520001b425003054450860015445900c00c1d00b002000a6202000307101600d0080b4001c1c1c081c288411020149142d001800030361460001402c0c1c4034030f0b038000c001d5803070286c844105000d420308201041d180c80391407040c40c0d03040b41c907004000c0d40204aa03c10740381d01d0707040c1441c0c81420741d0840406c040707219040c240180302290160007161150810a00c0d02d011040740d5041c840c143d80510103a110680720b41c2801c01042c0f58200c1d10680b1141c0b8100c07103030280c1c0e200640f45c0b00c0c5011549007086c0d180c0c0d4405100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315603875 1250 315602625 315602647
    0x1401021f0207050f06070314160c021002010f09050309011403040c031707050307050606010909090b0109150f030606050f06041a130312120f02040513050604090b041406070c0206 78
    0x40c40460300460644026644c00b503006807a218096039400c000950752500d418100c401c075000d044d040003a024100c4038940c0140300c010030100c184c00307001c1d00c6400d4040c07440b58642d00035032000c0340e1050300c1030307042c4006405400c09548030b0b0840e001c001d010500d51034541604c01200d4040f20320840c0e00c0654041d00d241140c4400e000b0344000e108080c004402000490042441000a015171a03c58001000300b4507103500011319442d665130090601c0e604003201d031030006513a01c50060540304110000a4201c80c2e540c1c0d10446010103030f010440c41814090013206001e000d8000009585041d5451101680d180007480050711035445103c034801800003a4440841000d002007002c1d12110f40c107801c80301d0b00d035102d50111084403482000425070130030101b0140211400361361071442e0040021801c01c0d1502c0302003900c030100c044076038039603c2e90303600014503558580e0720070543e5a820442c0044946850b00e41409200c000c41c10400c120712946000940703582c410000e00301071640c050f0000381400c0ca0760203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315605125 1250 315603875 315603877
    0x40e0f100b01171b07050d03060e0106020a030e060904020f04090606050913020c0109060e010504050c060a020d08041e0305040e01050306040f020f01091e0e01080706080115021f061401021f02 84
    0x2444000386260500f2900b1804c94001d001d28a02850240100e058031600180c00c4400341c0d441102020300304001000410b40208944080030b4042c24049460038910001852620941d0f00140c0d01510208881e0804898000600103944003e1303010090f03192158030644040c054091007580c00b01075004000311489194016040c500d0160f000400c07030049a5a81405444440b03ca01c1e032182c7d515000c1006100080282110343c04c070a4800310319140c40c10750000e440b4484905100700b80040c450100b0100900d03480c0b100c01c03184803403007450700003001403a005100398458441c2c804a110510008101d074a00891028001c44d4800c090351186811942440380c025501660705041c4440904005009408444c103400c440d8100c030f035002d60140c2000000070842e58180c0041c54994050079092000300d410810790b078152040040e40305072404003818200c7c0b9040f60f159802808158155881001082c00e8106000f641c0f198880d4006891100303004903590081d02c02c1d0948130100359098140d04540741c0d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315606375 1250 315605125 315605131
    0x10e0a020114070204110711040e060121080f0306030615030304091812121404110f21030a0f03021801050306031501120c05011d130b040e0f100b0117 66
    0x20901a0820315113400182c01c49469094441d81c0120000700e5808206078124070409450084800f008070340501401c0603680c3c80305008202c009041240e4903030901003034946600065912441e840c4d80c40f01000d1604102e60400d5650038000d11500b004181100190000c400011034080c0046040501d032141c00005040c40b500144071200c140020f110200e4000c074183c8200441940b240000b4000b031800100c22100c0d46504054078080c0071042c48000b80b00b992020100ea84104c9032500310f6002600016003410a400c00c51010745241050243c0b0001e002c8040c0a03c09043c0c1c56202014140a10541c01d902c201c800c2c1083c072128032042612250b004e50301454000001404690784007681c3c2003c4100c4030000e8000c03c11041c0f100c184002006426070711600644021721701120f0281c02d5203014000101c4120455200302044082c01d0081c02080d070145040e4070000b002400071810000340d0a84441d15a42094460300a1810300c140f1301c43d1a010300c8803945810b03903a24040b6003c4181030000e01c2409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315607625 1250 315606375 315606407
    0xf0b090609100f23060109050f0303032710060503060c040602031b12070503090901050d0309090218090f0406150f05010309050109022829030907081e060603010e0a0201 74
    0x1c3c8110380d981e0381308501850300b10f4070b4035415207401d030900c0000500f0101c00380d4002d0f80708040c441000e0203a40c4020094070b03085094035030b04824035951150100c0ca00d11512065189900c24403000b5054814180c0008044071001e0b070585400f51152000c440c0588100d005000150380304205003010401ca0087c00208c110840045e03c3c2e241c150400010b0103640b0940065070f096201080c2890781d890891750040c0100b1045900206103603d542e0050806d0713010f0701c50f0400d9240c1c0400c08182c4003004203418003808900803c5485d003881c1c8010f4001189400751010f43d6043e140c120280d0303070a442c141800c41600d5802d440111101d140000442c0a400300c03690866107552641450350060b1a0000309841c48089429000440c4030031600200c51894039501901080010b030100140b91402015a0611220107060582c0d4079541c5012462400296520020341031003441c0410452001a54419291440d80c0b01514600c1c2c441c18109400d88500015088444d0000c44040c0010b60054202800807805 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315608875 1250 315607625 315607631
    0xd02010e0a0807051302090a050108100b07080a081014150408011503030f0801030809041d0d020d090801060f121401020d200720030a0f0f0b090609100f 67
    0x980e8011400c03000300340c0e0007480c19a210007401d014174604902c0103140c04206810031400d0030030000000d18011348a12a0505001080000c0b8146050301074540002d4100c2c2c03d0392a03660001442e0420b2203502c841880000644e240b4007060000340300030044021194031500c5151141c8001c02040f101021400d090503580e4001c10002601074402c2c0070300e8803003c4000c03007030311281407031403d016200050030b40b40e070420498a0401800058407071800c2d00d414000c207840001c3c180300760080d0400b00303181c0001019814031424a940c08005d5002914003448803440c0d9501c6138040d40e070060b413030030380b5038074050809400035500c0d0030300c9422061f019094480340078603502d414180e0086242801c90303000c40d480818413500c0300103c0244940d0500084000384840d4100c1d86424156151141c0c55540d8940074180189440f150041e0396904000d141c25132600940000103484140c9005052a50f061004890000b041000169840c80208100384204000380c09003112582c1c40d00307064018800504202502c0717603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315610125 1250 315608875 315608897
    0xc0f02011d18060312030f011418090714100509040b0a030c03050c0907080c0a0e01030204090f020405031606020a121808100510060e011b02060f0714060402010c020d0201 75
    0x40c076466488000030031814501000e00b00441414200802c160745c1c11031441007002801240e5440900542c1142c900801620072030080c407001452298001c100030b03a400d480d5806000070034002081c6c03102200c400102600c034803100d1070103124120716040a600c01040060080880382c0c2403d0708041c0412a0081400d8203058a9540d83d1010308a81c0e041501c45a0002c1100c0c030f2241001c21086412207000c0c1000c2e00d56103000d0410364183e104d081010404c10400115040850340a901543c01074041c00c1001d2207000c403200d0550009400904c00c55100303201e1a0240001e40c5248260074042e6403007a40034000c40200c075200d50100041c019002d00400406042c1c4c8802c0f04c00078404500940b924001608011541000d200140c0c1e80203060400400281101003000541100799002190020300b40000ca1041c014520b032000c416131900a500401e0014460179503000036001040680c1c49801800c01140e10512115943e080844009000c120840c104030007524200005125070f510500d00030305040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315611375 1250 315610125 315610129
    0x2011509230c070302060708060a03080d09050f0109060f1406010c08120a09020f090709050409170408030a0801060548010c020f06100314030f0f0d0506010c0f02011d 73
    0x107403003240c1000e003503000410302c03404040d0b05229131508407285142c800707210b0800b80c0005408c804103104c01807021000052901802205030052601135802405680040c8801030916010344251001140d400740342014144c8070110512411012000a9008113402d03600c903801958081d00307601080d100d1400600c46402680540c201191044098020124850820b88148941003000c00200c1c2e00c94441141007010183c2d00c0001c400131030b40210703008101803115051503021043c01340210900c01800241c086024240080108000c1c196507544541503030340c503a0304481d18091a003554200101ca082502c088482426111003c0100341200e1004865100002c0360320140d070384400c141c20f035102d000d145070540e01444043e00d1019048060403071031030140402c0340c2c0b1440d0340c00b00900070402e1280e0350041400400c2610210144204400d0340e5800d40030f22038038190002e600c60024981030100040701e0b5481116400c0d41c039a440a4001841542a4015501c4550000846812003a04500c007600340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315612625 1250 315611375 315611441
    0x90702070e131e0b1609080114180d021015080a1401150303020c130b030a06021305040207030f0e031f06030b062b050304180b0f0102011509 62
    0x40007410205080e64400e0b00e80044561410074816055403e22098000424520b0390115440382620003120800d40c034190b0203035500c05890304003940701d41c03815802480030101c05c03c01c2070065120155060181c980145c41a07a54036844503030100682080c1580805064603400480040745800d000c00103050302c0d1202c031860b015401a01f5101c1c0751301a001d0b144c44a900303218140003d05620f031140710003070a40d02c0181d17840081c040d40a00a4030100c0e201c080c0c0301407561003442030000040651307804180908107440a504019041d06060505550000311842c10b0b10031900560381c0740c0ca0340a520b4280a02c00d4580d2100e210204c0e030135005045541040c040a01e81c010004c0000202c002005429070402c0023402e40000c0070035024181084080c00301014409079410b560030f90748000000f0006504d0081d0460007250f0103070703d400c0c0d502d03000c1c220003800d41d401c400540b00c416140d103118580f162004909031070003440b2011a1071a21441032120711040d40058032491091120b031900794060354444164 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315613875 1250 315612625 315612631
    0xa120507150c11032103090709140a050603150402061c061706060406051f0201060306090b04050c01080714090607080403050105010f0605030c090405130501060806180102030114090702070e 83
    0xa00302d00c00307110030040840703400740b1100400d42c010869944864070a05464418000d405410a0301000141302840104512030162a440030180040040010404031000003a600da143c69130400f4005406400e0000b0a01c020ba114030700144502e8446401f0300c6000d40c08185107262036811044500b500401c01d024640007003520841c14907400c004c40e642d590031b25502400c174501c40d03401c082040095075140840c40b031510340c591040302e04401415400360300420a950006003040d007011000d20502901410140c844c50081044d1343c80515100300444090700b003160490b0210f0200c0c000070000c0c54072240a40f500302405000f980c64556141c69012050f00180d20854850b91110018004601c3c822403140082c41c0c5030400d1800e40c18580d440308480e0050f09a42806207569800041204000101c40f007072068005000304110754036040b409072580400c070799030340d038100d10440d00381501ca40510880f8100c905a0207004000502c00d01000b42044002d0001307400c520500c00049106a4121100380c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315615125 1250 315613875 315613877
    0x40b0705070204050907170102090901060f050c24010501080708070e0d0209040b040314071e06110711040506030c03070e06061902100c0905011e0318050109020f0d020a12050715 78
    0x1d506c030b1802404100c0549600c1c51142c569005000703052558640c1070f4454152440307410900d10300c420b105000c580300c1c000c1d0646508144070740e843c40881e1000c5005c4c010710540c0b401c21030008503a220707001034540b81c1c0240c841c0c0e000a01c00c040014061072080710100203200c0d0080a4045207850381d00000c110300d5050310203130350000c6030109020806400c8260040b40107070801445082c0496a128082041928136040c81381d003802500440410100794002c0c00521882c401c400c0c2c03698128108a24240c2052032094041c1d8a0400464071a240c00201c00049440090042009908050007590754500241c0419000700040c02080080e0411044441100032150b0050502448061005042d07404261001c020300c01c11420502013070342c0c440400908034a500510b013040302d0000d282100104009964119035200c00010201001010b411a12295000b02d484040d0204118104584d6055510000f9400300703007003408200107206440d54040c480d00800950b012244d4407075000811320040c0324404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315616375 1250 315615125 315615133
    0x8030403081b01050f042a06111b130209061e0703020c0a06050409240605040602012910140412030818030a0309060603120206010e090a0209040b07050702040509 71
    0x49031008290841c1012110b1502c0240840d09090840e604040009480a4425820004d480014103200000100c00060307020404554642e110802084543e10348410906806410030106d610061168801000c02006102c1c051b480c81c0c450010f0000c1d80541e81c8a07030458810b201e0100d008942c05110080f40e03580111150b43c8501c00c0c60006e090054181403a0300c1610020418004d01c0d5200c0c06031425148440c80c00144416540b24010f07022524448203040c04c04070000126019911902620860741160000d01c1072040209141d44000e03128034804013614034100b9035070712514182140c1c406490382420608401d04d07141591501d80c4e40150403030b44994043c0c0710003800309130b4407a00c01d540c8886096480cc0b0380090750b6a0303040d124441c2649220405840340c1c0000207211b40395003d180150f50014610140848200e8040d40f0741d0303024030428502c000c0303040000e5130070140441c0302e5001c5940180310210710f5689903216407020201604420400205014203001a00c491103054020361482c0014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315617625 1250 315616375 315616387
    0x306050105030f0102031e25211808030705160c05090a05160e0303040b120106030501050a0803071e050102130302190f0e060102010e06070305010503190f02090c040803040308 77
    0x106262810f0301c03c03940003a070710400800058101091290343c0c80c803401c50215080c2d45948059942c203d02c800e00070110f08010000312800320740c00c0740c135460079903183d4500c6c901c2105020041030200c2d4a41744040d02c04240340141c5800007001407005651104180c100305003410700d1076888030300242001c8001c440c1201400b1080c40149003000ca07847c4e0003011810103019528069030101205801001c01c0414070820a00056484d42d0500c10360b0050f083c3d40c2c5500d5100c110607a02540d5506081c440c0002003071402002146ca41800201da000380c801805c01103190400903035480483d000b0410035800340aa029990400140080c002080c81791a4846501d01e030a045004000580301c001c1125903601e00d6031b07201000411341c1e01020701e040b9070450542c0e80f0b060317403400c0050f0b015083e1960346441368040c02040090541d0158001c0d8141c0d441a021901070a4005007010f441c0c00c1c0c592005050301c42d0440700c1100601e014150260302c40c2001003111b04183da211086071540c2c12039002101c04040106203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315618875 1250 315617625 315617629
    0x33f09120905031f15090f0f0225110301020c1606080c030103030e0f041a0103062103030f02090319030905090c0f0a030b06030a020a11010902060f2206050c06093909010306050105 79
    0x2951232809480504520b04005a100002d00303008160009000c100340c1c1d4081d07814020745102c0240a007001400a56a036040c0300c0001e912800c41e6540344030318441c40303140450005e1085031564440c1c0c462110580c51642552070a845c01d0703500e080000c0d0700407107034920703c0c0c0303d81c8270740c080c0c000c10030401200c1c01c408400d0300c070014040d1102030304041c100d160320612001d480504174241c94070302d0b80c250500081041264040b800a480303884003982c0c140c411410091070f24204007401d401c0c214002c0e036500440603141c100300401e5040070b90303880d501d0200030b03c10303c4030b8072200303000519201505080015004c00b6000c00314480b0b80086842d822007640c045070842c2c106800843d000900d40d01c200081081401ca607000900f603000e030ba01100741208001c202810224100f001101b110380c000c401c10800c144c4c0c0d5560040803648121040c845900a02021414a0b507000078003040090300e8400b26010005048507200a180c80c03104411200d00044280a095464038405640a18040e90003c1415030406c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315620125 1250 315618875 315618881
    0x603080a050c19111e040203010e180d021b011e02010c020f01020c060a02090105040b03010902030115080912031e01080601050a080a033f09120905031f15090f 70
    0x81e1880c410f490349000d9001440001c0c03144c503140000c9a401e6014852200308071244802c09110603081803000001007049003c0041c0ba40c13040e1085118180d0340040c030003a003600d8080103403103900560301807046010344a2181d60390001d5000185800e111905107052100280364004035110051713552007a01c007400c0c0d94184002805031900000075440c4c9800046443e40e18040280340b454100d502054030310b156845402220f0007004031420080d140d586501204000f07500a00c122181c0007040c1c0311008405004400c003521604040f000b504203074402a06880c802c2e032000708811001c1c002c104550000c070704c440c140c1c0ca01801c10100202020340c145030074000c143c0825003000c4c81c03650101c0d400d440003035804915112850001d41c905000e01084100d542003000030440714141c0c10b01c035001070309540001a40110503c9010700d0150b00c0c0615901025141280c003405840e8240c1c04c0142c442c0030300040aa03001ca5000d180d031034001507408088200600d040c8803900240c900d5511400c540c0b0740382001d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315621375 1250 315620125 315620143
    0x50403110f040203070815120718020c0d02010608010b09060d030e010e1009080601060503010b04060c210e190803041215113004110a091a1306050603190603080a050c 73
    0x5503600c5225235200985594580c0240700d030f441065080341c0406020a901e405a6110043c00c1c5c0480e80294103800019010b0030407401099901d6180080c102164a04070310102c2c004d00c0c02900800c2d1000301354030202c0710b0310300c2100b05e5414046044840502e83d2070f244016407030516543c0c0c40ca43c1c16414a000c0c5801c025041e4000d034200308090005104015500040301d04840700b5040031803490132107207001480707624044400c91a01040f6a400d01c441a004117841c40c1c40b08003115001840c00300f00b07084c055000401d0142d811268070030700c01440546ea41d00c1c80c03400d1041c0a142219808200c86005500b0758205100d2030103031140100301c04c1180e108840200c50250205508024010720b030006107200040000d00150100080b182e0025054a66941d240060301c00d402c0c0038413440081c40c0d02101c550511845d110b004051080d00300b5030b070340d0062042505568004211524588036205010031010b515460507c03419640c14000000603203034002040c140190751103640e2138141440405003040d0101e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315622625 1250 315621375 315621379
    0x15130509060f0102033a0e0f011a1c0203030a03140c041a070305070c0803091e10080405030c0f1605030a24060f0906031106040303050403110f040203070815 69
    0x42c0d90056a0003005568000102c01c690b580428260502040c1140307251050294078813100d160311070b120f005030708603600e2810040112030b8450034084405081710020010f00507100c0006243c0809484d004040d00c90180e40181079503486800c07a000641154414030802001c0b965860380c400340c845a0310b55803580f04140030001e03030606d4540412524101000e00c1d2000b50101e0016443d003c060142042e0b529080e0040880c20b090f940703580d007065032607203c58030191084a642d041912414002002036100a03805060704585031200f000c1aa01c06101910803a0700e800244860045000c00308580701a0a8062000703040b41e85503049c1c2099452080c0c1c11903400313500070340445008106103081e8598032448003100c040c50b103007038a042c01e402010340390060014980e5240d0b0008000c40c031500301e0019603010710003004010420700304100d4544514070008011a5007808208049501c11800b4080407102800032504801d6480004049a108841a0011403164414000440c3d0b120304200020101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315623875 1250 315622625 315622639
    0x9020405091308180112050907080c060403081902030c030316140a0c0201080a2009040e011e020d0209060d050405120906160c21030806060307050a0e1513050906 71
    0x8140c544034220300c21106040f82800d896000780c3c0c04e6921400c0c40c101040e0000404010310b040003000123489031824414100144603002b420802403520078112000c032030340200d5243c940a00031030080220709081c401c50b010b40c08184507040e098071023800250720544102d88603254900e403c80d4040e150020034942c016000e0014014540e0b07080d048480502960340900301071286a4410300b00c5009001d03851179111a005483d110303003800c2041e80b8098084460704480500c1200c44401c030a500702d890b0542d9410141d502802840d114090590052451011074500589002944008510581d0040d404010f4880d81c4c8c00400040c13010a1100b9090400c000314100d2418840d0b00014405019960b807962001c080c0440300c201b084a030034403d00082c90340c0110b0303110101c41c69041e5080145d45460540c0450281400940b003494a4400c881c07060b246038a0317190601c80d01000450b00001745c03644094011002c00c068400361740d0200007811310100491866850035042000b4131015001c0a03201c5402192 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315625125 1250 315623875 315623911
    0x911040501090303031505120d08060d05060f04050111300610050903071502030a170106020a0605041a0103080a120b090f04022403101d040b06190902040509 69
    0x82e00c005504101c3e605440c0203c3d80420107130484441c41065032200340d0010340301c00c040011160103d04600980d001351103441c460ba03500d40501c4400c42c4040001045900900002001c00c0031614481d90828082c8000150610030307a5001003666010119030890140e941c80040261080c500c1c10050030b0741700c0c4040410a0412801059005403124402000d001020699811075142042285c0080c0520540c000003059091006900ea504c0340d0789000c00540d14448030001c0e405131400090403220340364001c000e051001d84428004043c094002c4404a500d03640a0400e1000004241e000e14011075030907640360b6440b80040c112114001140d451030381008900d000ea640c807c04441d074810301020108000c1e5480b0300c0001d50380c0e00e104020b02c0640640c0700e000f4120904010107188654000d075000c025007032311002038015001141c115043cbc0708081c0c40011700001e45c5046c400380c00c0310740581040714203e842041e01c1903600303c9411070300e840c1e81e021600f00020b180c0421460b402003010240c40e58402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315626375 1250 315625125 315625127
    0x16050102011406040b0d0503041e080f0d03020a0512071709010b03030d0e07031e05160b090d02010201150303050c0c04050c0f13030c12150c020304030212030f03040308010911040501 80
    0x480061086204d9591204207450a0301c2d00c414110300c4540c08070580382d07110b40300c00680b4000c904203c845143c004036540f0229068000191901e600040c020050299100e130410840180d03016201c50f40c00c002c2c081c44640c010100412044d170180c3c0054131120700b034106a25a000300100001d040c40ca150f070400c01c0081150320040700b2154502200380c004186c81130f4244040340713842c040f540000c0030401807030740108140c080034002822041c4100145c442c07080303a900400242403024003500321100000c2022916500e44045541d03e514818000803510841000c3c1c041c49007006640180c0c08210001040d60802070180440184400700312401c0095017410711410b1850301600e4000d4096803000580d0356420300c49a540000216072000d403880d415070305c5040e13442031300c0c00303240d01116401d041d01e40700c0440010500410a1400069000f10b061900e15000c000d80b0000403904504031780002c0001d000e5401000d40103520550007030321045415450f20715101c003120b03071800041301d881a0a000901943e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315627625 1250 315626375 315626411
    0x15060f030312060b040609060215040b06010323070e031005070503040807080903031c0c2307060603060e010b01020f0c060301030818120f0c180a02071e051605010201 73
    0xa0380d0107141c41c81c80324401c000b00c0e01c014411600100303540d440224000039555401544003003a00c040c2d42c00d1340c14140c1810b51179207001506880041c00702c1c207035000013a0594801e9226a40c03d00c524103080c403c1515080c031294200c0002e0350281c1c00100f920004445504040100c850405201c940c00c00141c41c107820000c01c2400b0140c40148080f00c00a510028403400c00296a07800b000182660342d5550c03514404c0c9030a0a400742d241c40703454100352600c21014003940c0e440380070161540d90a4031924140c42030000d59032140500302d90081e520000440480c0540c03048000750040b8100000e0340c1d541c0c0c0d07000a45480c44841400d4043c0c4c1c4420341c800c0345a19124240c0707045907072080c40181c40c0c2683e07288003e040e0900060954109083c0c03002201e100340c00140701c40c0e2950b04d1105a8242c0c2800754140300110000d00001c1e000d103089400410304540c5580d0040c0000d50140b86c1c213080040103040403000c80700c000201034811f54808139180c2851015101d501300208004d0000704540c0c2c00500c4a8031740d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315628875 1250 315627625 315627629
    0x30c100507021c180b09030a0204020c1f060305070b030712020702010c0515010e061c02060901050702060417010b180a0903021626030903070b070804050a1215060f 72
    0x11064559011412140c000c000703404543d241c407080702d884420a0f200060510b10983c0b04a0241003408000007010094842151b84951000d0702612541c6026003d01000c1d501c100c0c2034180511a0b42007543c0c2044040080c5840c01010031030220b040703861410300614211180d008001d00d03110400038030410940088015004428000700581c0750301040c00142c50350401e50801422601035000348254803040c03054050f05803512050704406a843d200c05010b903186522f06004108c030041c003080340c0540345c040c000e40441241490700520384410b5902042c8580c01c1070b8442c0c24601801c071080741c0d45000a01400500c55030962303030380b2885402082c6000300600301a1591041640d5107180d0820b01d8824401c049403522544070004d4007030307515011553314001c0c585400c903201e80a9402c041e5641c802008694003280300070010142d19003000150f02a80d8403080d412524004100300001d425200c3c10340d488000c001c3c2c66100010b1451600f007100c80310141c0e001451074186050001e00000141c800180d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315630125 1250 315628875 315628903
    0x2031306180b030c190311090108042d1e080304060c1718071e170c0409080d050f010b0f0d1404061d0303090607030209010203070f12030e030c 63
    0x1001180c20601828840440d0003002140c0000010400c001000c440104210307684a0300051180a1702441107084a140544415400b5410816001c81f58800c18030290060700900b1a020700140c02140a0403007100080484c3c111100b1046d200c0c00d0000c000810200032544021814211917241e462200303a100050006007046d507034038000c0310102d201c1c0d50a050350015000496200e0709011800c000c0c840320300d2410390040d110718900425090721044c0002500f520681d0241a40e0381455100c031640c00f00e60211000718804ea6032807108130765031070241c11042030103540c195540e00701c9a00000240d4030000c0c0240340c42c0c82000c004001d180030060480340c420180700e081c81c2d11130f400d00d5a04070140c441c42858a00018180040c4010310000da4003098500e044030140d070b140f65028020041d00e03800121809085a00202d0015100f20701030b40080511000500c19640f13401c4441e5100019910104000d55010441010208603107806106204a010580008509100300903120a982e0740c20054102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315631375 1250 315630125 315630137
    0x603030c210503040314220f06030605100509030a05060c18030a0210031107060501031104050f070801060e060d140105010801080304030c030813030b04080702040c050901020c150c010c0216050102031306 89
    0x40c000c81110700a0380c0364403d58034208407511f4005e00d008a091031182c021180400303820b460000300540244152800c80d50003508090039410b0f4042c080d91a500103c46154050107011060000500184603440c400c0d003c46810700d80700c143c0310702d040d4a5031044103c00c600945c802c45200b8003681ea031000c1408d118010b0b1902081c1d086802040107514010540028100d034201400032040100540b801644c10700269000c100564235111187c43d0001d09440300c03008618080010711450703204410ba01041c480c05401c00b80b501008241d220110381079002240c3c2060346182c014081c0d0340c0e100e401140104400001541070500b1074441e4080c249091200501a2100188501d0884500e616010003540c06c805844c82501c0c00b803d1840f40f6030301000c03049108924011b00082518041d0064405440042c4c0c014a410a02c002c1400381e04400458204c00c1c5103000d0000112494007401801d1070420305078007500003221442d4100300c0c482145e400941c1990000d0101031001017009080c60216400f0b45804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315632625 1250 315631375 315631397
    0x703180e0a050a06080a03020c040f021213020a0e070c0302010b03030a02030d0b030705060a171f030b130b01120b16081605220e161407030e03010603030c2105030403 73
    0x900103001603070207400d55015082c4400181b58022402149c1d101c0c0c00d0b10280321320304000086ca41240b00b61159402581c0d10358020400b0f860315000c2c1d48a40da03202900000040e40c45441d011085402203485a0002d01c810025104156084c05403880061060f00114141b4400d02d034045d450380140d20082d0491a40c410a2880540c1c080100b48004c21024084a40c0c0d50311070a03004000318030b030210f400e19104110700403960408038814510211003c42c90300d03101003404d5035601c2e000c1100190110071001000c030b4945010a106c2d072981c3d8001d01c106400aa040025440c20b0143c48200a10b90122581c950600201d020703000107031542d00c8800c114220040c5200d844003510b180c0190700f0700c180350f441445982d484c07003070703924011809a80001000740340c9503640750a4a0f10300840c00d54040006540582d0818100004e5800f074045140b090410320080b070752076000301342100e05a0340203400069100c1c0380f500501c00c0010b5089250302840200d00c0c0140100c0f440500b1511004c0d0004081244006007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315633875 1250 315632625 315632641
    0x141608061f050a06030204060215270a0204110a0f05121302032104050a050316090c110f010f0b0d0f02091b0c0f071d060909030403050307080703180e0a05 68
    0x10000540002003c810300c554031203c1c010000d40040c0181c80141c82198070504804031109500e9120783c0315989217111740d250443e0151481c9001d90f8500516101d826000300059543e80180f008004004190644411250b0401801038050b0340700803040c85803c000f40410b52080007038031940503c08007450420200944086807600c0d44505074569641e41011804041c5401100141300f180c07011112629450303103890405482da2001f510b52080c1c10362200b8100826101e580142d01c1c902203c0c01c010809200400c5904d081120000f0a4090f5942d14050038400000f50b00c9401a049000d031100c00e0014130a41da0031100a00249000c0d1240c0c2910000496011441d41522081c0c801f111005813246085c0303078410f6840d60b03880b01641c44d41c02100004108001c415114542800f24522042542d0f00c58009011240b02c015152070150b0000b080040007085080005022302c1740b1814125588660300e0600a1600380400038039010360071160410440700404180c0c02e9040381080c140000e60703440f03540c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315635125 1250 315633875 315633931
    0x60f090e0c18040b070f0f35060a120f15020d1a0a06021b040b040207080f07150b0105090108090a05070b040e0a02092808070314160806 60
    0x101e1654065201c0c0c051080090980d64050b0140303109804600c15501d600400b55144103104c00d84200050800010f001c16074030440302602200040081241044d401d25005d080c04508205c2280d43c200500f002d100081c24800c0c5464001c0c0b403100000c4007081e03600c0d654159650094400a8140c40ca0301d8100080d079100c0e5411584948004001004910f6088140d540e110710b105242c2c1b0711500d502c0000090351070001c5411045002c0c4004203840c07180c000341c06c100003401c03810f101941140e801d101d510009070914000386a040c514080c0184c030b035003041c941082d8040268034500412401c000d0720b4061640c0100513100d1280c000d0a2482644e0348003c0070620300300c048800546140701c0c00c0400a003408500004105450a1200108032950340e0300600e800c1c0d1080c0340000d81c2005403144498411550300d20881d500e146203000c1d400000340e55004041c0b0f891000d800548001030f06400303500c640e1100300900ea04444800158021355480c02c0051a11a9401080140c0120204403600c4041980b21 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315636375 1250 315635125 315635143
    0x90702011103040c08010e01050f181e0622110f1801030308150603060a030b1008070e0105010915080c0d150b0702120604080304030f05040803190f03060f090e 70
    0x300381c1d50320380c41c00382845080301101e4450703007036030354030348549050341103410700496100d000e4001a20040da261041c401c0c540c4031501c80380d1201070098219562020b404184e070846811003140007041070b0b0400c1850400c000307a908020710075451209000b0704c0080c0600d001040c01e00411181541041075240c042482c90822442807103440e411440044101078028081c140600c42e01c0d0080440e001c010001d000061000350303082d0768403140c403410410000341039041c1e0550094182c4a480e6050707035a50440c914080785d80e0031001c0c00000030401130007696800a4628020007403c44091b040d8003050101510285014003030001410740003458094100082c2c0203c0740400206141c1c502d85980e803c1441d03179540120700101d00c540812401815500700015040740155040081c0528548440e502500e154130350510b0013040c490240000141c0300001d201a0800b04c055581c400e5400c80113034401008950304490001c14145061414030503000806949006d0310724045c000140100340004091401d2018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315637625 1250 315636375 315636401
    0x8010303020a0318260c0d080403200d03030b0f1f080c0c0703030206040b0903030906131505010b070b011a04060309020409050303280212150409080c0304030302060f0c0909070201 79
    0x3030b00c120807144001c48144005620042c3c40c00f001e10350007042407e11800707030040d0950b4024081880842caa4144007034400500350301c100341c0d092000c2d01240c1c01c9840070707100f038000c0390341e80d01441e081c0d04103041c05115103042211504440c501c1e100840410044005156081000d0701e4001040c907451841140c1010110760202d078549a5680b0f0000e6032220700300c2d01211070311500c201242e80c8400020a50b4090710030940a8031255031080b5801c030150031080c2040d00c080003095000f0b1581610380c45070178060181d41c1c401c20340e036a0031414900c100507c107912840076001c3c601c80c00d06401000c0c1050b00c050b40e480d85401315015581d03000050140c004220040e11900000040c00065844281d400c00802010184175002100c0060028228040c41003070a45041c4690002201b500005280c2288494004c00028000c0c1c0180c03130304140d41e0044052612280e00000d818418150100141680714200d00c01400052a0540c5407e0b19401800d09050040c8010004680258003e401c8134a9541c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315638875 1250 315637625 315637649
    0x8010b0604152c0a09060303080103030c080706050103110913050c19031401060f080a050307170c0105070509130603050705190b0d2016080c070e0a02031608010303020a0318 76
    0xe64400034003000c1d40300703d0798450441401c0018041016006110489405071100c032103e81c03035902c0c140ca11506166003100c043c1402c01c19200090400e10406018500a4803008240105241070050450300903143c20303d907403803450070b1200249000654040b00002515244010100c07145541c0c01c3c1c401d1a000105403004000c0701c2c02c881c00341540710808030b07031000c02070850007a0703510b910715140d070303c41e0030f01400541003001403101044d4464801900317683c10010807444d0900d0600520300310f840039508000010000a000b940524081d0304100c00780342c07c803c0c204400381c5140d882c00d0b80c8040030b201d0355000e80784070844a04081400f255001c0141000911181e944040d180752900400420002240680079200c4007005100210f05640d02d83c00280c0075400203c00c1c40e2a00f4042e5040022101f010b031003640400309a40303030242034030360103000c4550000d6200c0c01c01a050350100414049138204100102d40100040fa9000602544454140c10b101400703003c03035503d00100444030f82022601c141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315640125 1250 315638875 315638927
    0xb030c0301090506090706080f060409030909020313020112230403020a0b01060807021c0c0204110d0f02030a14091902010e0d0b0a0e210c010f090b0103050708010b060415 75
    0xb10104d0698800d80c00401500c14550300c9034001d417030311442500c0080b5500c9111000400750306265001841aa0082c00c10010344d035525411182aa030040f608240c0d2495000b0580003156003101148445245d074034400d0001844107420808030785106550740041c00d0091000c14241402801400c880300d810190f03419441d038503140e01038000441590003100600c210300402da9250700200740c5c4100c41d00e040d60340315080d0b4000c0d02007202270002410050a0700c2c2d010000240e42c0c10781e0340f01c0c00c4031459504c94096102c1c034201420364102d43d5504003c041481071203003080000f090102c0c41c003030105241464140007900354001240c1c00132000101d281c2040c07001459005009040903003070301c1074140c1403040c03007118503000900e912011450086441e03280c4041081c114080c68501a084200e0460000108280c0c00640c00060301d1503407001741e405007014001402804005c0c44403201078100d074002804007a40c69070208000b4403840c03144c0900304400340920342d2083d110300120000e030702e01c0100c0c0b614841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 315641375 1250 315640125 315640133
    0x9091e0405071806050d1112030a02010b01030f020909010b031005100507050c0a050102030405100e0616050f030313020d022701050f0a0b030a0b010c052a01051c0b030c030109 77
    0x55554001c520b030b6106483d80c0401d59802601814041c0c3c1d01c003a0817503501080c03644c0c801da10100d90480703440c0e200710720b8a03000000b01410406030910b40a07650002c503006032028000340c221000d00040da100c0c2c031700400c840c41e810f032201d40803541100c8a20201541d00d0341c070b00000c180094159080a64132808030460700e14825488409000d03644d01900a8800d055040750400503020081d104003800b50300244000c012510301940180c404108509203e1700f11200c00c00001c01b26802101440c5540d44909074031002d00404001692a45064800440ca5401d0550840605000c2110003e2140100c0d00c002000c540b246010f200c0c4201c1581745024515201300c6a07410502030901030715016140107030700c503200da2034140d411004450030b001c00c00345551901c803001d10141c01c0340c80000d41401005d080020014404014444031941c6901050550304841c5245a552804001901d030411800b806501e40da1040841403000c0010f80d100d002550254280119007040c450001040d0315504c0d0a030800248 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 315642625 1250 315641375 315641383
    0xb011412030f090a0b0307080420031c080f010f090c0c0605040605040b09030a0c200a060503040302010b0f0f011809060e090d03090308040f0c090906020909010603020a0509091e0405 80
    0x3d1102128008002500d0741d485000c070380800c80d0b0b0200060101004036012800c4850012000c298402c849150089640086490701451112509141d48042c4e0002d003400d5010407026000001005640c07200c1d4900b030f0040c159a20035003c0e000403203030b031000b0303c20102c0d00690040402d03560144081c40589450300b001c6004100032075040c0d03030540c000f800080300700d4000301c22900c42403070603101e012801580b41ca80c810013501c1d5104951403c01042c0c0000c2c42c50b0380b043c1403100140344540e10b5960340e10701480c000342510340380303003150740200c8100301c2c1c510007640d408408542c019000e1034240249a030641c14280158040d92001c540a440c1010100314010080e0301d1a109a05290488100e2003400d54228100c850620010340051034000200340098440540640042e000f101802650b646460705070040302c0c04a1022118140c0c0050310003000e04100c0030703481c01842c207400c1c00c504041c0400c201610500c502a41140314607000e0002410082c10151115411036410440d42c1c6149400e141c0607a031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 315643875 1250 315642625 315642637
    0x30204031e03020f060702030a0c020604050405180c0a0506030112240212060315190209090f0a0e0f100c020703050a140712051c030b0d03031a0306040b011412030f 72
    0x501500c1042085031342d0014003240aa61280d000350700c1d04441d51000c66200180d800d040740c0c031020822001a96580310300940b0f00a210514001c902d151140070004e15024071045114024009403000700318961f40e0303c1c240c3e4110340c900103117080120b40d01d10f401c02240c0c00c40000b0740c02c8040c100b090588043d4282c1d024009d2002c214807610161f846600c1010b0362100700c4650016452b48110001d40c0540314041c880c002c0c800c98201c00350400f648000020b4481d0000c603481c200485a003010403060301e05501420102a030b04c2d02c09000c0703480c040a142134a98191094a0410320745078102e01801d5031081000400450300441580c1080070035250101c0082c01d0914018414891034101050420280303980e0025954040c00404007100c06010b16041802c044010500f80b5503212a00c1f440307600d0f82c88441c2005c43c429540001c800410340704240fa096a8440341c28000d43c4101c04102c0042c0c4071081c46410351b5008101c2c500d441c509840001c42da04503400e84808580808141c2204580341103002e800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 315645125 1250 315643875 315643877
    0x318060d0603111e0303040b0a0903080a050331290a0504050d11150403030b060309010c0f1d0409050f15090d1103070f06020f040e0a050c09090c0901030204031e03 72
    0x40d80141585134401d00c00148407410b606800c1007100300a91409038000f80081c801c10300b0400070181e0f50761035104060b000188490041400001004640d038080c038458034410034111102106d000204111400211100c100140007a4a00001e001550201c1024003c842480184981140b0f840c1c000a00a04410b41d401c54543c81441c2a6002d460f0086090001010040c80201000783c0f51000c041d80c81100a0025424190758000c92841501c913a00211310601e000b000220700760f00c3c2070000a012700308403100c0d00208035002d256000c00d81406940010014000c88000c00c2c030740c040303040481c2130000e600344403081d52103982518a0141d83e802405071050f010001076403002a030941003960781000422a62403240c00c01c10000c400502410615040203000352001400c040c500d90807092540c2c082c1c2c2241c80c0e2158480c0070400c4d9046a401401d5000c00c14069081c10103a200300801d68020b40605042071180021803040c0040e40b00c1d605403002140c004510f003101000f01c040ea20b138060445402a4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 315646375 1250 315645125 315645139
    0x1b0309030c010806100807050d0f02070209090d05092e11010b0d0b0c1b0723040905061b0f0a08061f020304140111060403030605090108010b030318060d060311 70
    0xa0842d0f015000345840780c40050b00e2061251a0350004551303441005003204140601072000180e1b00b00c44c0d124083c4414100000103981d006a070041001025005211141960010400040103580102034900820b42a6441c00d560f2072400c1d411442d41c02c80d01c840120030001d104908607042d034011880b0031010300c610000c101c0303c5412400e000320222400000b130b1001d14004003240803100c42c00001d10301450880086c1a280418551203400c040c030680c020008000c84110010150f9558620880b4803e4100c0c4d04100c0c050701d665a4586499004200740d42c150814040707448042c1c4420102c80142d02d80341041a9541103000c0041d241c110241c903140d0040308280f10f0580d5545006007142184401034005500709440d0481108080d0080c4201a0410020f00d01e0340080607030402240c2c1c060351094801191003810407040c4085488160300c039403200d81c1030609400b40c1e40c401004a9410f1998030440850f6151502c021a282c0e108001030b56403010b00d0010008140200101c559007070140403560a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 315647482 1107 315646375 315646393
    0x60509010507032003031005030a020a09051306020c0106060f08040f0204180b040c150f0503070806210609010f291203040b090109090204060203071104021b030903 72
    0x283d131903001000340113011508071555400b8042c1507001703041711045da80028076000e5080c4030314a41e5030340d9507010501d01c0d0710403032005041a03008031040d075540c05450200c0c3d0080810f482401c00203507501c603041d06451712a4a00c203014980040d0080d401c0e075040c0c2c08220051110f04001005103500d40400d00018940c0202107200d5400381600c0c1e21043c0c5401546444169030800240c10020080c191016154000e0705681d081116850903440c0d69540c2e07000300b80d0304801d8008140c0c05150203003000c14040c10028540d8450000d04009000381705a41c130200090342c20000b4060f0040b0031043c68402414501d10f17021840300310041440c01420f500711500c506685c09a0020040386800003800713100d0b941c001222000411500408618207807800f10300a4481c0120000240500c0720340200440d1a5102c1c2c06490898542c1d4000343d5149040080f95a40da0f4050081d180c024028080c074 = true := by decide +kernel

theorem cover : BRFrame.Cov 315467625 315647482 := by
  have h0 := BRFrame.cov_init 315467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 315467625 ≤ n) (h2 : n < 315647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
