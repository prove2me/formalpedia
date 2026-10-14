-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2565
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:59.130097+00:00
-- url     : https://prove2.me/submissions/21698542-0ec0-461c-8b55-badc21e85860

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 461151079 ≤ n < 461330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 461152329 1250 461151079 461151107
    0x601080106210e060901020307110715050903011503060605040617030403030302090d050d0306050f04090302060105090a02040b04030807030801081b131b080601080a0c0c23031201210f03 82
    0xc03c07031041d52058075251140c1a034004505944c000140149507810800145403520001e01a0450324a4141540708203015a005513061090010f003880244d502988a4a403441ca48140b244115880381402d00c020b1940d4081c103405103190581c0800c0d1652a01d03124001602c0c640d00461406056a4084019410000d4a0b03a0001a54403800e00000c40c10b2014000d4000c46076400244a407408080041d0160403800c2c10340154a024004800320b075000c2404c60541d00c06566006980d00c86510500013882154001036420001140110420441d540203100250191f034400390079980300d48405071102c2160f00c1c9100d0910300d01c0402c4041d401c0c0600881881984048000340302907451350808040c16400c01200005102c40040084030f44e040b54140e900000d00f00e1007003108200d0204007900490300f4a10203032010130303c500c0071600a02d03140d140a400c0001101980c2d10307251849800c1c1c0411b1400c0c041da00d61995403d003c401d410602001b075040482e00300c01d200e0b65000c0c0a031002d41d0008250101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 461153579 1250 461152329 461152331
    0x71703040f1a210a0b06070515070905030d0201020408070603060509010303210203160305070306120b0604150807080d0203030f010e1803030c0c0c030a0c030b0a02040f060e09060108010621 83
    0x10a2103c22420b0401100c1a81c800003501e5003850210310b40e01c125002e000c1620300c10302060168001090340080d0140c0300d1010302c1d0124025440b10f030800c0d50180714075408aa41407107400c40381208168190040c00c100d5000204031000962a4202601507d21074090359800110705401000801e104070b02c0107540a00c150491400c07403402e2881c00c01664030440321458a4500c2c03510700d101090785403045030b510480624040100300c0c01c110302d507032441c04051805030182000e40e002c5031942d5507a50140001c031010b5580080c409941d042e44d29103c44a80c401e90200340208401c08022034004000c80348504e1031042203032001d0f030a10001000c0100c0103440140e003000120002c0142c1802000258021a894070000d500c4040c000700c20f81c03078172546500307403800380c1c0051041000140e002881d03602904e501c80c840f150140e45803150721000380100c1d0310800340d01f13090640006040760000c8015134044070a9407581031a584040064074940340a120742c00c0026503099000420b03006940c1004481003860070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 461154829 1250 461153579 461153587
    0x180d0323090402040b0c10050402100e040b031014011203020312070c020406090b13020f0d02031f06050a0906020303070818070317180d03050a0513030f05071703040f1a 74
    0x10214040b13801c20f4110380007848000454a6007034600b000000e000381c0300c1c01c4040c001c0e0301c0c2581c085130b403201e0000d4000f010300803042c00f902c0e41c582c0c81e03070000407250001030201c54a0419074817041c805000c3ca030450807100384005001060740641c950076a520150590000c500d046140216100d202c0310041005003001000d15481c00140d507035000d0790005001840002c50740c014800308000402c0c48003880c060289204010406600d2103100640e00028a82900182c480d60b074201c0c0b02200c001c0d040c1120b03420284400c804107200b0380080c0500001c2001e41d540401c80d07612020242d0f41c900c41510400045a00700b0000f50003170020707401c141d070458000c0d0300b0b03504215581d80d951502c4500c0d40038a4550b03d4408076001c82e16140d03603042480a920112408650b469240d10b001d8141e201d41030030355041103c0095004010300300c000c0503100459124181b50445021418041d48400d441e0068500d0002200c0c0440e81c182c00010a41d0305450a034106060014505000c841211b040860347c01c81d140e00900c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 461156079 1250 461154829 461154847
    0xf020907090b1306180614091203030412030516171b0c0a1505010b040b0c0a02131b081b070507090c050c0c0a0e0103140709020f180d0323 61
    0x2c0a81140d58550300440d201e24100708001d000da90001c5080300da9941c0b0004204102c5500000f5000c03129811a0201e9665441801088000301c001d40400c40a10002090008101007401d80408440c0d06640810050300c0b8101c8850030105107245440c00610300c003002241c9130000206290b04020340d000c04c0400310070380c0c84900d040da400608550480790419941e080034001801c06045001d0800f00c01080190305011000b041030045004e89100b8010116a8411442040095940c00c0d90000c203551301e0030074012510f1016020600001c007843c441281e0580b82c3d01c3c000d44000c1e0103850340110503491741400b0f240119580d0861041543e00384216100020550b004d4481d12640102603600c2960b03564081c4116458a522107420b24028032039031a0411003218061006415640c0c0700d0740c0000e4065400a0340c0d0f15004182d0481ca262900c006105940d0540d020010035000e1021140c14060903604410000c440226407030140c0400c1141c4c5000c200c80c81030000d50b205083c0c501500700d040114503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 461157329 1250 461156079 461156099
    0x41802031b0a0506040e070c0609020a0b0d1406010206060409021809030406080c120411030102091519020303010506180d0b0703062310030b0604090906050717040f02090709 76
    0xa409200c80740e210440798014142503400001904064032001c3ca040d1a2001784250200000c3c540b100304189038418a04108094203d40b40710b0307030001c10968286880344260f032000c2d44006941c0b00354625068404c01440c01c01030703c1611a0340160068482507440c40c0038171025040e4114200d900c00d40007100c51112803025131740b00340207540c0c0030001e513126030504c5800751031848003410740520060b00340b2066040c1031740d018840d80c0c010380c4101503488800c0302c00d020a003e4001d110748030354006080e0307e902d8200c402000161100c04401c01000503481d0340400b05a0b1240b00a028803074011508000040800704c4811443c3c12903003014240d00e42803121038a07009004003094551400094583e00200b1928946034511049021614244915041c0d640c00051103008004800010b02da29114a0001e03039590030242d40040079000000e01c405283c6207414401080c0481e0700d0804124600d0b0b5003c0c81444203889076110701e6026189402b11002e0b41c0030805c080302c00510142c100914004046411409 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 461158579 1250 461157329 461157343
    0x6090603060204061107150c0f05011a1009050f040e03070b010602150703050601050316090b0d0b190605030c090604090e01020a090503121e0903011811040504080904180203 76
    0x74480180c4983c03c0003001001d800c9401031a424503030000c4420b201111a84c1c0050704120102d007071401001034280f0702201803200012000d009940380c25035402c070b9600024600904154200c40342071001c40c1448081c0c0b0340306258080c160304200c24858803041824150b000003800c841500440b420100c40d41d41c0c000c0f80d82001d8001100580200011403035030020b209100c0c0e085202410103129a10f01040020031a001c01420448861905005080e525015080020281502200b80c0b641c43d150810202c0240a4500307a03140200c400341609071401c0c14200c101e1007034815540d00d8524540740c03240c4888881e04144181540203008010004017400c151081241d201c5c280340c0050380304d111400002d80307154400d074009030194004008020b2114014022207902c541c400d084811601c4100f200c5c240b0900818504a0300b5610300610140c3c4c0790341b00446800440d00c03482c03504170145071400c1440305640c029036004002c040b0511803803495140c0f03a08190141c1c0503040c0c00b8440c03405c42e90006854114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 461159829 1250 461158579 461158583
    0xd0c0f050604150609022812060803040e0c04080613060e070303110129010315050d21020a12030203060d020904060b12060c030612030f0d1a030c0d1506090603 70
    0x6904000b00c3d10210b00e5010701401481006011410944100881d83e507000b6002d0349070607004141000525440c1c081e9541448034100c403002000f180d519020f000340d40381c0c458020b081110800c1d4000030601000203081720245c4010001070f08481d182c9082d0320b205200b038a902101e40644454000700b4000c0d040002070000c502a81d1403541c550846141c5a084540f50272110380c500c0072070b003004040e9a1124298030083c842c00c2c030380016520444034041d41140c0d1039801c03269011525500280c01c0c00101018440b07000b6441d0900c1d01150b40c43c44059940d601e200c0c0300141841c180c2a42030220600a07809507502c440013609142400180340e00244170b40c034048804a0704c0d5070307450901d4480340c2004180c1e50640c4010000410032810440360304d04083c00010903ca2203096a6101380054400034010390764207055041c0c1c01500d400360541ca0b000545400c1400711104117030309040708450b01d00054044200500501901d92803602070300d40c0b90301411a10901200b5a841d6a80095600301d280309640041d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 461161079 1250 461159829 461159843
    0x907060c151109041a0d02011d0409050a0327180e0d0909060b07020105090405060103020702090f01030308060a032012030406020708060708190506041b0807110f0d0c0f050604 77
    0xc0c00c10100011202544c08440172484030320400101512800c20300881d06809092041d0700c0c0c6620088403804801d43d041d5190414100721164040120016080c0030480c8652240e10a142001d03180010040d42c500121501180c86801000300584600c1d6034000f40c0c104040124544110303140661812042ca42c881c00004c00103c0f0810000712a48620303c0076011440c2814034008958000810038011074000901c80c65440c1d0100d500c1307038021b90486d201554060002c03406490840c044500d003000921042c0c0201d401c100008500f4585240246d00760795001041080021940100c089060b091a0603a40c118a0103180e00448113000c002410091116900800446091614403401c140b800b81c002402d00c04c50307200b072112400e40681200301030080040c000490307a440c0d50008010b0514040c14a9090007404c1001c4e00d410744c40f00300320744590441e403625048100707035192803950b078444540c8900c500d4001d4a44242039030b1141641819050013040b41c0e003091030a03a1074450038044141c030210303188 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 461162329 1250 461161079 461161087
    0x20406030f0f0c0605040609051302070605010e04140c060d020306041e060807050f0102030f070609150b03011404030206070c030c120509101103030109020d150b031b030907060c1511 80
    0x2c2030f0010900040c00d00b5191075400c0c1854070b2000750070288207000740361049000004004503408a0b41c192404c942e0001030500465035101c402d240c812600360350135149202c0361000c0e4404048001604540d100016024030300d4018041e815100a4001410842e400b98550180028500030418880440704509200050441c40d0803413080c07501c4800c1c1e000c1c0d03009040400c900d0180ea038001c02a21068600d0224480e5a401d0a241660050805180052822801c1140c59141e036a950b03000d54509001507000300484c201d95209401002c07400c07100200142e2215002540107446070741c03500344251190800d4440241c0039941e002907080030190a000250010601c02c07143e03d0900c062032002441802c1150030501c401d2103540c0c0300d100c14041d465910350001810009400103a00000d10301e20b84018140000c2c0c1c07540d83c180703155032003518094841103048400e03c0311082040b0071207001d024554024004c061810000356200e1521007419070300c03004008541c001c55019409041c5e60842003031a01c50391 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 461163579 1250 461162329 461162333
    0x2061908060a05031219051c151e09020a021002120906010b1e03150d050106090f2c120a021c0c050303281505090c0703020d0c020406030f0f 62
    0x1d0b400301030703010b01d209030b002da8250380072480001c1c111141340c040d41c40183d040001210f81a00d0510900414002200b0b000503081d071902c160354000ca00c10305d4031040d0110600c1e510065060380510f0604052801000c08404000c030404550041c01e0024031b9005490f100304000e4041c0040383c200c240103d031844500c1080105402041c00301c507025005400d04242480d100543c7e1040700c815800d58007114290020210b21040f111004001e5890340c000c1603548c4001c030525041e4083c00061062408090521440e80c80c4406107004103640540c1e2aa4400ca9164982c45a03600b03048a81d4406541801081000480c1d02181d03c01420002d00d03640007032095802c200c1203c11030b110743d50100030420a80744039410010b580481200e400c0550300c9040d1620101e2101c1c10a100020421400400da00e00004507404003100e200d0b02086a0040b22103e503150780700040b070321240c410360070000c00580040781c030801d8050050080c544894005480000d5194403079454102c00070b000780c0151901240c200107002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 461164829 1250 461163579 461163589
    0x30114060f1012090b010f1703030c03071b08070c080f0a06020f040b13060e09040c121502190305011e05090709051008041101090e0105061e030c04051503010501020d0302070206190806 81
    0x2041c1c00340f1403008d850b1070025110307124000546403030b03440c0303200001143c0c11510810f0658160340508440b01c00c451200c0c179082c80540c0c002c40007252058546100007811180225550f20354610002c05001542410742d03500c0c00a500c000c01d101307000b040600c07000c1981d5000d080580111002d0b4121000c8890510001810001011107a50300c1503100508001c009000d020542086038402d0b00015401e0000b8913201031000c0c1441c1a41302d02c1d501c04a0303000e007240480079100180b01000d850030495a600d5081c042d0202a49a00b0303203e115a0b010b0040165090000c81194803032400c0c0341201e95161030380001219040a045100700103110030b0140824044d40b400410300f014005d00300200c10302d240c450b40c4c10b81d113801403040c50320480000c5a80c2500c080f0340922600300c40340c40004c80f0360302d151070044942d150b00140245030042140003121012400c00c80e003141d050ba40e058000b01055050482c0490207948400f4040307810079824031900b44000f81c08940381c01d80b40b90300e86481d0582d00e4031030706000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 461166079 1250 461164829 461164859
    0xe04060e10050106230702090a051b070b0403050906070f05070501080a09021f0e03101a090c0d050709050916080a0b09060906040b03060114030114060f1012090b01 72
    0x781d403040ca444010030a07180c21030640c0b014245506004105801e4400c0f08201ca4010380c040a50080076260400c9a003030840d42c13006104101c9452400c0103416102d80030000d5001d90f0400030314200380c50002c00c0209000f40f000d481d1504000f01010302c0d1100300c5d550a2108013011900720b8459100d8101441030b5a00f01500907403003d600e0b902000400c560382c000441d03510101c1c40300311201a40640c0c0303140c814887c0001d0100390350060201d48a41681c040d04000030b1501da0f40e142c100540c0001d04010b18a040c0d42c0c140d010740340c103d0300c20303090100308aa024001c201c0508404140415138000003007075141c6c00b11140c420b10304140c4c2c017200c0c100d5a5001034000c0344000d0150b20f8451a185910b040341e500c214900d900180c0035540801035a0302c0402007001002201c440941c1446640e00001c1d544030030005100050710b003a4005d128850341c07000e0b034882c0c000041d6881648542c009400d1011418001e240d54a010402d250072a52503014002c10021145411000d40f000c250340320042c040702403610380381 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 461167329 1250 461166079 461166103
    0x80703020313240e280302130e030711010c020a090f0608010209010203040323060f011410140d09060204092003070516170d0c0210090309120c0e04060e 67
    0x2201c403400060079901c21259000c49024800704ca40031142503110585050441c400c109201009407032020103070000d9610b68401240700d0b022030703240229414154080d21200324080703c02175041803250754a80030802800042141000401d1031550096511008801c000f8510980c001400394000140101a1452a0080002c03680100a04100f50340c0c00400c407411290031a408440084404800000409588400b400340e4482c1d0400d1094040f14170708101d04a4003c842d840e11880600414020314000200a040214151404010352856940000c00c0c55103122039001810385402e60343c080032a00940c00154034165503020322000c0f40c1c080d0070f40c1007107401e40050460440c582641e006002d4818036130b070740181c444072855074010480d03103014108400240422058036807542070354490042848490500040c41843c4030307030000050324403035440f69030382540c1d0703000030309043c00c030040044801e0328011188481d8400700001c03801c10041005008034815040800c4070b0b202910258039001c1d01d1481 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 461168579 1250 461167329 461167349
    0x50f0f040804140d05010207050c13110a030e0a1407260c010507030908070306051504021905130302041409071502070302010323040b040507080a0f020904020d080703020313 76
    0x52002045003402030342c003110b03000f010320380008144401056076114980401080c96001090fa0710401201290400c40b034041580c01c0000018200f0184040e60b040220b0102d81d50400c2114111706846030301300440003005e660490790340034410303564a158880c404006110a4002000c10700000500500107010394204900ca64201280b00d400f42d80c5a220201506052050008150302058003442c4040014100402a100700c581e0700d040c464064182180c01681d803207901503103107103646407904c00c0d034410140b1000c44a10103050580144d07603940c000e42d010454000515000001a501c50156401c0c0e005254501c694508ac1545200c2c41d010b078581004200490f80d403010a4030590008445003180c0d02481c0205018000b503c1d08810003000e1449400034410090401c000d011000340900e01482c8105d007169031a0b59286802901e4a42e03510700200305015134040b48000d4034007103500c26080b40c0002c01c100348000c00b613a40c605541d4052481140541c0010442c640f550b40901d200314002c0c580024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 461169829 1250 461168579 461168581
    0x304420c05090409020a030b040302010e06130308070309020f190509090307021f0c0b0c18011d0609030f03031e060108040308040b1015120501290d140703050f0f 71
    0x8005400ea01a49601c1e03030041c1d0343c139072191042d03541d1908100010358002e12241c419003810b0600902078080c40804054611500e40440c60802c0c008840803c010b4242e917684000f5241d16900b01d0203031683c084280e07030004140302c0a1200b5030710000d0410381251701c030420380505480c000a000b10340d900140401c0c0e450300107000100c0503840c1d00072145c5041d0b03188102440040c0c1011420307560103140039406400714070214100030700000c401c40100f0f0116003610818404201c0b09004460f5031100c1c00480741154031207501402c1500b46000a042c0301038008043d41d2501c1100d03105d86245410403207251a21454880314900d4a449810065800075828a080440382c5895200509480405080280552580400100c100a19a4810014100f0000c200410b400014401001111100349074200c41e40380200000b4080301d0016840d100344029480c411149040751424803568201221030403c0d41d40b11174441603101c820600f01441050161400208c0b420410b000f120140310041010585083c050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 461171079 1250 461169829 461169851
    0x30801050f03070b0f1c0b0112060602100b1210150e060d0209151504090c0207120303091b300b0c0306120703050102033702030442 58
    0x114036241075406030306005031340b174100d1002505203104100c02c0d040054405c2d4501c46200080f90001c070780415099a40d07042c40c401c0c4000c11030846501707105070300140e07001010074903581c101908200d824003002040c0c440c1c01d408051400d4103200d001e14007007502035a0b45100010368140e4600010241c180c1c4281007a05142c024041110903001000283c800c088603000100f4998840b62542c3c90a20050044414a65147d002891681040c05a000014180b600401c102c034800592070040f80e09245900440c08819142907000707004400003984e09207240c40711182589105022800104078501d0506505907440c40c2c1c0e2900c4141c0c82d5000039107200ca10f041c010105060b02000f58004500c174001c80d6583e140c443c002422114800100d01e0306000c5c02100106220065015500ca01c05041c81c0044a54030381d1445d4124401c001e5035030741c400f0304a41c42d165401c429070b8061640a440350400c228454803100b00210f60005010075104502d07100c01d880e031220b44180e001c03041a600e145509000d022160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 461172329 1250 461171079 461171083
    0x1050103050c0a1704021f0c060b01020d0c020d02060c1504150b0906120c040c08040b070e0d03050a0504090218041419110415120612031e020c0418030801050f03 71
    0x7114500300310444244c00303e800d40d9140f05400c3e00d5100300c4402d03440c8480300c00d980501266071049054900500e05004c260455001042504e00300d842a44c0b00980c41c4480e82c20000415540c42c400c0e07820040921034442d031503d0070000c5450b0342101c50200c01c2c3d2490940303000c00e404c001210401d03080c039003490008480c03a1608812a90801c0d400c945004529440c1e0095034a0140d011440550082c140050000140c1d0400c42c040d010701d014194002c0e490fa0380d21401c0d1544620a006c080e081b0310540d040f400420b1150000d80105089840c0541c40c0c141c1d1159000d003644c10603a418142c05403161400c203094509482801c944c4c07040031140d500180b412856408106940d0401e40d00311649450076000c04110b042c3c2140c0141c40c0341882440206404880248940c030200061181030b840c00102103541e000d0b54107507444642e40740d0fa0705080c070b4038004281011a0661070100003944900c00901103a507a4030f000380710ba03109a2540040141c0e9281c20b0003011110107034081409440d2500c454480f80c1c0380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 461173579 1250 461172329 461172347
    0x1c06022208150f151005090f04020a0e01051305030d0f0818191b090b12190312150e150a080a02010c03090b03010305060a060905060325180501050103050c0a 69
    0x943c101c0c80da42035035a07035140b80482910741c0060b54000702c0754900d0181c0303d0b0400003030840e011050380c001180283d41000d0100b288540383c8444041155403071100c032076621440060202903282c48070301c040d4030780e10000309160083c1c1900850108a0004280f4100c95020b1641680150702c1c128050342e02c01c0409189868a0716207820004517031802140c2c10a01050b88058024003d4055503007090307503078944145000f019100101c42c460b0012142000460f80e00244000aa04480d207894458511a43c0d00351903000c40c0400c0080555141d64985803504040c0c1d0303000d0010703c0080d0904a0341c2c0f40c88900444012218604c1030b20030fa1100c0c50a001407040080c98000456081c203244001d00000d04007074403203116a5004d42400540040084200300303004c20b040d4001c0e483c0d44400e015141e1561114019107004940780c2d500360780320420120010f11010b06075044520703400c001c404030586a10f9088023044407500e002d040251680d0041209590502ca0654001741640595041c54003142e802001064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 461174829 1250 461173579 461173591
    0xb0c03040f1502120c040303030b0d08120406090501051f150c0609060204081b010305010b07021f11010f050f07050702060415020c06270910051c0602220815 69
    0x50142d032521030741502d5044480700201e1401a0a081c9411107101d613050303210f80000ca000909004c2c6001590038100d1244600545c00700c1d0003400c19a40310400050701d003009006407002500e6443d6400400e90030b02c6a18001c1441c1f0006458100381540102e40c0c029003640054502c4005944208140d42e02041010030326504c400d0110b44a125428200c01900442d0040d0074503010f590b04078101e04411740c119054090302a2024002603a0328100740b080350198030b501a4200d100d1800070210b08003032400124903e0101c1c18112403c21885c04d126003180c10f5601e18010b01c1c0e03525030511900c0003443c00075550060a525207107181c5041a40800d000d40114419511044200c00d9007800340780c021f014460480a02030021078590070b03004030381a420710311100c00212000c01605030704001d040c9242aa4840c40c001a00c080409240605000780d4907115402c0c2141d12414030120030004503580010854056815100e0030100e4840d1101c1d00302101d250302c13010030365004240c80380d81a400c00307010650100e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 461176079 1250 461174829 461174843
    0x20a03050a0b10050105041404060f08030a2601120201020a0506130203010b0f1c170f0406030c020f0c1e060f0a08160e0906060702090a020d06060903020a0306110f040b070b0c03040f 80
    0x5903002e4007250140ad800d03001154404010103020400060001c040c1040c03041c05c0e602c04000784980c5d014015101c40e460070310143c4180140c01072104524000002e00c000f88184101ca01d0742c080380d02c82d14208102a1600702c010214500440306615090007070300a5054100d0310307600b400d0460744c005114140801c107884c0030000e9081304801031140c1d030386198503126131042000780da50904c640c00600642c032038000c0744d0102e80340071941ca0185100160451072504140c0090400c000008101700080e21082e640c0c2c995a403076a0611501c40c0c641c000030300300b10489140602d071100c0c144c100141100c4070040001074250080341c001500c15030b1005100c5161001600c42901c25250000071881354416810040d411820742010302c11441d400394010030b07038089154010001907072141c600b111115224440654485240e01051021a40c907500103008190241600c9151071011800240c8a0f0003035070000c920840c1c04101e2106104420504640c451080c000140c5940307410354900303045100ea12000342c090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 461177329 1250 461176079 461176109
    0x512010909080717030601090e0f0103021e04110403030f021902040902181005030d02030a051e090a0602010608010b01030e0318150d1a03060106090918020a03050a0b1005010504 78
    0x482540003c0b03e00307a942051510f955078400e41c4506400d03a205403a400d001030010300001520746459003400d4020200031440c58202c1e46960200440b5500003002081d00c1408401d91f80040d9442e4464001800300741080189c48520310b0401500034000032841d10b05541042d19440105103035201c04102d003d904841c0042d4909450000c541030350022130420301c3c0340100340c0c14450b00040344d4003003400300d8204078102c50384000140e400320b8680c000c1c002c0e020007042d02445001c00861071000000340d60701c0100c1100d814020010000350300c444450b48168050f075540d04080c0282e20007030041d041c2c1540c0a0801b4040a000789100996070b20170f032024280100201003207402d060ba20302490030400401500d50707903184d441f0381002000402c202140d03a02d10740980d01030b040c1d0740d080c00316055040310512b403210035029207002c0802010340040e91000b107018075000d2041c0d00683c0e4007403206005d1402840181800c2c80d103454452801c00018040b43c4903110603404c00c00281c3e130f00c40100d905942d81200e00040c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 461178579 1250 461177329 461177333
    0x3030209060301060302030f0c0a051c1116031101110a0e0109030b01140a1505040608070c02130b030606010e030705010c0606030c060c1203021306080c0d0c020c100512010909 77
    0x90080c03115403540090004000160300740e050b0041c6001d40d84a28944c000ea490343c600700203a43c454008002c0100b01e0510980220101c07401c01c0307203c001100c49000c07481c00001d0320b80300f40a13840108549244501c1c0348070a01410782c070918400203040b001000b0041c0c0b03905002c0b00b00090043c54000070802242c050701c6081640701e0001c00005607840000c050b2156114070300c1c6c0ca46859044022030103007201d01d400250754400b1038085403902e40c0c941c40d0a4585418824100c0380808003c000c10184040c030000b10005845203811410000c01c8440001040d01e004d90070907003000005492103040150590303800140d940c01103032203000c4400c24205050380003a01c0c1313418005001c10350b00241c4410075410002803207a4105c14030102c46442444240c00300c407241403056040380100000b103940480d800b00c0c1840340b0717400b58002640024905455604201000b0140f038169910081040c0040e0030101040b2000d0604d815402c0000b805c5d42006801c1003034607680d041d4581e030140705680c0c1c030710f13100c01031881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 461179829 1250 461178579 461178581
    0x30f1d120129031506090103060c02031605030d050708071e1817190b04200303130311040603170a0c050a0b0103021c0f061d0a112403010b070303 64
    0x920048901d419030010681078507001401211408543c003c3c020812540e034802030000c0c01d07034403d6000502000f03c1780d003180c075000000c148005030329080d840100a01110031480d0030000d000039100b04011681d0301c0c07600c1c0030002031300c00c05002c01040c441c02400744100e440d04000d80b0341c0703401d040184070440c0d600829412900d214081108400218081c44007207104041d44140050803940c1c00b04640c101c50507240c1040420180000c090070400309213010400103203240000404003548494113002c001c0c0382c1000a41550b000c080042c08125000c0d0007042000060036103075000c120200d074104800303480c5444058100c2e0034000c0610788001d0006000200758000d9a04030380312504a012107071a40014902a200e0b40702c00e0005a00c12107480306880c00c48510b03004604034540e444000414103680350390b1987c0107021840083e0455405e1340d40d180d0003c0c1c9040080074001ea0040e0400800585110280310a40112254106d03210401d09c10b01c04e180d0609008030703070440c0c50044189070384203581d0400310 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461181079 1250 461179829 461179841
    0xa0c030b130b15040905041e021005071106122a07170708270307060509091509190f060302030c12070e070c141b040b0402070606060507030f1d1201 65
    0x242ca0840c04039012580c070b900d0346c0c849031203240f08003000e5040030761b0b0402100700002c900742c0082d489481e000360300c0540c0384594041c0c00b00d2880380344807040d0b0901c544002a416000b405000c061070301b8071401c1041c0310100710b80e110201ca8900012440203500a540601c840c03144c0c40d0050924015010300741940326a0300c040300c1c40b154000500c1c5131248071082001d12806500300c0c50034421842810340d0009443c011818004030740103031319a21303c2c00034542c040c8080920014644c215041c2032680502c00c40c0c807042d8006110341750390400c565130103160003000021070740001d0107110703101e240450a0005032000030350340c032120b4011601d945210784103034000e42c58000316030003031545640900140029903400400e405951441105030701d0150305100009030fa1146054246007112240611864840c203096014492120002d0400761404070191110019100142d0102e800244e0009001d000d156005002c40d44840319858848490300100d080c400800106400b01c42c0f244110282c2c4421018095000e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461182329 1250 461181079 461181109
    0x9060f01140304050706110705010801140301231603110909190c020105160c1101050903010b150d0501080303130b070302091c1709150a090e010308030a0c030b130b 72
    0x642d41c07840d0901d8065140e103801d03c41c02d07000c00c04e819000e00b9010000b0840d101070720410394030021980e181950080841841d8100142c15558a101c40d4000c406c01c21707164004100b03c0880c08015091418052000c1d82024003d2070805107009803101c1c20132000b82c2210f60200c0700b201c1d010311a071101b100750a480c96034000340031920f03481c0c1850300c0801e40d0103412040c03244020416054007200030075030a5400ea80031080c02424001155202c060660055000c1c0a03102005000000c40d4604000864007490180c18801400d1b40c001c10f060484076418025a03014103206009141036081414141ea0241e0341e03250014110060100040c40d8944a41c0c103036201704800500c019002c1c40d504000e011001001082501c2c0800b0314580c03d81020360210172521256409131503400710030801c1c5c405000701e400c05041c040410074240c04c00a01100110803542c0030754042d0402c0c42d92814040d030400100d030b43c0040707070106040c00c101c00d20300740b80d5900b182034098910341140070400e10b2001000810035131401e011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461183579 1250 461182329 461182367
    0x603071412040b011a09090c040503030d02030108100632060a210e07120c030b010602030d15050d110a0e090109050f0a112106250c0209060f01 63
    0x440606a80c10740070940628051014010941d88925042400607005002204040702c1006424860700740003541c03590000003003802c5818107071074000190443e0b00180742c01c581c858000c07005100c02d11040c0300c2061050b01086041002501d4a112010003010f2900901e200f80e048560701c030810350010140c03030900d2074010403066071ba9050400c0540190f103a80840280d044c0800d1603002c8501551080500c12600c54006016403454604029103540107040308a80007200c3e20000000106001d61240c00f0341802d8001c2c50312013000b21590021296080180d440e89001c0b484100090707201c1038a0305c840d003a00305005680061000000c210340c00351507031090203006441000c1041501040d07002c0c81d0014401c03010b0707980f2013a007601465941c12007a80041d0950550102088141c68207900385500858510348092544220385155424400f044941ca1825500081040310b24032006110005400300ca080265515600d81c010610101005001d0b80c005c04d814450317420f0350b0707019003540c001408203164 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461184829 1250 461183579 461183587
    0x30c090d0b07030518371a071e0305070c050604030e1212250c0816170727150503010b061c022503090e06011d06030714 53
    0x542602841402c481260000f0f00c1c040110341c10030260020881d200301c8450090081e481c0c039070034281c1c258407202c800441120480001c1000f00c1c02c298030300182e440c05550444c2008a154140041c0c014005014008208001c0d030300c0002c08220100070940a407d0749070000d10303941c1c0d080d0103498200a15902a10314424403081008141c0d001c0c8280420070026681c480c6110343d40d1008039034503502104800722100f0203210503804a10b894142c992452526125144141e00326100c180325114203802001c02a0882c0c005401503c2407044403100610395100c40a0950b03000064054440c020740c010503848041e50039001c00004d40c03900110080020725101001b00c03407209521000d041803030b03100d42d600075402d1019112007860400d0944210846c5d1003003030756074418030019a800a5004454240c00d42c400d040343c500d05280340408210800f40300e911031044881c1084040c407155000241018100030014101d44203020742d010240398101e8041e1100382e00c039240e889d0142e5a500b21041505001c40c000301d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461186079 1250 461184829 461184833
    0x60c17090103020d1a040c170121140d0e010318020402131707050f0a1202010c1502042301030c0503070e241308071a0f160507060315050a0b03060307030210030f060e040302060c030c090d 82
    0x40303080c1a8ce000203407070b4180c2076100a4019800c0d54441c40c03d5110101d8a20310240260a0a4009100801e42c0e500c0303000c5034a4881c4c01404082d840342501003120361100006026130b0514130320521032014209c0301404000e1501c51114490440b6070700c001d0401c030b908088102007001d001508592090b03940c1065440796240c814003440003804a0320245456040900c02080c0d500910400c00c640210707607200c2e0302d942e8880c0300c2690080d6013424004d0b0058943d14418180041d100d11102c0a0b64180703540caa915000c3c601d21410074030803030f0040c0d070154110000400c1142c0070960010038044010041980700c08141c038824030a40148034a4480840e60400d031b843c1000303404a8403406031581500c0400c148022a42e826a100001d0300a45400c030318006814440013203c00003a5512580060480709626101c4c1d000c12140144500c6071030220b915a0225000351005004880103002e030020044814506510001c0d52510040c0c41e00c40c0c0c1e030b5030000c080781700008070008071a01c0701c001a090043e115000c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461187329 1250 461186079 461186083
    0x1605130f2c070504140f090f0105040b07080a05010803180d020301060f050a09020f0703030e0c030d050c070909114501060c17090103020d1a040c17012114 68
    0x365112201401040800f04a904d000d02c0791940300b00c1c03141001e07189a03440e01d11748000042d000e820380b4910301c03c110b401c0c1500d000c24014107100d07034032500c6045c3c0c55041c103280280c400302000c2e29441400d802c110051200d06800410789900080000d01a1403c2c075100011400003501200040d40650078010301180000386031411000b1550261103c4010903519041c05040b4020300e01100c01c6000200880804240b103a000008d8413510007040d074500b054032000080c5090300c00b548046c08518042035000000d00b06000c008020034043e10142700d0b1843c1c0ba518008032201120105100b900d1070700c520580080e6044a080315040c4402c0c50a00501e08038201580d09a040c400702c00070314902000214109125903c0054000e500070489240551140f2a1609580001d1561030415500b8810b0014a000500400d03014001c0005c803c00104880c50920003030350000501501030042000030101c00524100340603044403c1c0d11102c8120401c00000759403c00104000604944411002407140740c0c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461188579 1250 461187329 461187401
    0x5031b030f040b2415040806240105040f0302061818040b06180a050403030e030a0e040b0303090108040f03120207050d030b0109060c111309141605130f 67
    0x14800600b40b0307a5030400389802d42000501c0c0c0300004c2280340f5621980b800c01d40d441112101584401a051507150004070740b62041c2100c08003688441003d1941103816282c04074500d83c0e800303182091426040100c0c25502c600c079840001e01a050004400c00314100168130b0314103114004007a0b6800390382c100700d40850a0030a1703c0940310345032010007060241c030f807007107a26a100c0d81758104404031307550f4082c0c43c0c0014071004100354141900c40c2030405251006000400c0c0140082e2120040a44040203110442c0c1d0b60f1282c0034000d520400000e80c440c0c1e0012091540154402d501030382d607135407620b01102d064680c0714000113018000300d100000c00c04c012481d09a440c00030b660801402504800450b0400d0061041c8800b0032503009510001c03488050703903042001c030b01030413a0810046550900c022a4442c800c256041c03000d91125548205081c401d0722485410544100c5215040000103864045410040710b80a5560044850304130520b4001d0504441ca0410101454062a0b0f00445c0440307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461189829 1250 461188579 461188583
    0x5030f1305060a0807050309010e010c050d0e030a0503040f0f080f032401120903140a0305040512090310180b1005030d170601030b030715030b09160f05031b030f04 72
    0x19616004207042c109001501c4550030350395121403d0b91204030094a00d80c1c4064480c00e400c0d501c80800f001e2000c001d0080410114035951180d56900d00700203c00c0881e840585103902a401c00c000880700c2c3c81e482815260041d07000704500710201154500200b903200c03503541c0109a54000719800a0110300f400145200c2c0140e1140f900c40041d5103110005001c7c00780740200d000c2060b40310a100c402103640c1c0300030038451090500b444800ca102000d110300e90411012440025158420481004010b01412840c2151001c00302d04248a100c0040c2c2c8070508142a66030040e44c170f40030030032242d15030300c141054140c100e20880301c0c6082904500007200fa03503000d00d6001e441244121103d0754803500000804108280465204d61551001140a800c45124455251143d108003107000c45021281608541050703d0010310001755a0074000e03601402498403080440c01500c800354980c01007140d090811052134030f60356a90718945114481000920010000382002c03041080c0c642807000031a010728 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461191079 1250 461189829 461189857
    0x50a0e0d0f03050306060d18031e0203040312030f0221131505040c0b0d050123060d0b06040b04030c081023220b0618010b041e0305030f 60
    0x41010000d000d4206180d0400400034200201c01002007441080a550025402048280761a10b9490860191610303080024030042e0800760344000c0541009075880894540d14161801d1100b1220180d1640150f01c80030300301c200d201030a11032441c0300b42d08c2031014540c40c050444d240d2440d0286510b5000005c448100d0485080011a000142d402007040c0850b512032500c052000f0354400080141102030005c40d80f00350f800002241c0360741c054015121655007007100250540c50324001444584002000380365482c018000301610342c4815040700c0109060b01c8000c0384001422010070007070710039984114070030b40d0007040103c200030f40145c106003102c940c5002c617aa02e000c1101c0000465101401c8504ca0403c0d0a18229201500340101c95005080c00d0800711010f01400b002c4821018400c03040324003e102d80104685031511241c0055074069911604440350704002c150300301445076010380c0381e400035a1443c3c1c804861885013518040c542c86401c1e03940352015440d807001d150b005080080120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461192329 1250 461191079 461191097
    0xe07110d0203030c0f0c03090d1407050609130e0a0219030302152503140a091e0507050f03030f04080d02060a0207170904020d060320091e060a15050a 66
    0x550710001c1641c0c000c3c860414894030740203c400c10380c0d52544c404001800d580c0002c0c04001030351303550104401d200502038021f02c40c6510382800101d0502c1c5550f0800c034030030030080c058034030240c6410411141d040702c04040080e80d0200907501c1c51400c1c28400c0000d601032441c00070700e04898410881740c030448ec429000c0321400e0038500202e488504003210000135407008412903a8009030a100030003090000b0b42000a00c4842c0c82c0090035564108407840400640c9a0300700104101c0c14051440b4200042d0ba40154100b0300c0c0d030344258030b6036a584242d511841040c1d900a459940500031550903c080a099540d503580c1e902400b5200d0004030035140c00341c040c4400160070712010340210b41030759a00840f10054000c0740c5039a2030260700300e0031362103400c07a13400d00200700241118032030200510b00030720302080c14540ea00d1307514a1030085c84510341d004e412071303006000c0c0925180152144009684940117101e5a900307000c10f0013486544d0242031004102c40b10030704050341140081c10309400680c7d43d5514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461193579 1250 461192329 461192353
    0xf0105040818090105030c0918030301060c120c0201090b0a090518060406060203041a030712022b0902030316020103141608100b0315040204050d0c0e09060618100e0711 74
    0xf46030f40034841e85402d42c0100c12045000d1505c0c286681d41300344404465045043e40300c102a00c0d40d0800d0700204041000014100b060149400070440308207040e1406801c1c07001e441c0e0009103400941d124201e1f4890021640c2d440490181c0c407201d01804014040d012504900c1e0001500d07101d090701c9042c003641ca4000b000c51040e01c040200c070281c882ca01c1030f0301080c40302601490403d6000502007030410000ca40000a02c076180c2c00140801605a000f42401c161140380c5095000176443c5118140c901d803190480040e200401620460000c840c1e10b09000da10600058000c1e1a858031048503403035407001004201e030172610704480d800c103260780c4011050b40c2d6001c8040c141d0003140a29200b04106000148101c0d04814040b141c40c84050005414143d403403000c540c0c2118445407c0700c036401c03442c0c0e0a03c0302190203400284c0c407201c001d0080101d401e0000c045074000034050380c52403005140d1000524140c5200703807440024000781200700c00394900018010b01c080031074080310500c0d00920000d800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461194829 1250 461193579 461193589
    0x3020d05060a080307030e2407031205070905040506041103040804031e08071118150f180121050703030503060f010c021035010515070c0302120f0105040818 69
    0xb09440307040000790f1520100780c40c20b49001e003084070116030080f22520210f08280c05c0804504079103102c0440b05444444038500a071503002880502e01c9840d281c142008042c1d5407100c0420212502950006038a3f1100808600902040314511004150002c1804104903102c0c3c000c0040340e0144500d616441191a00d019060f46119000703441c0d0f50007888070001042183c103546905450040c6600e1002039800c100b0310800104a65100c1d0301403205440301303154100b218558040900c2140c148510440d10401c50800d64810300965140440d41c0c04611040400031040010954102c412685201d40d6881c0041c81035004680d1540104c2c3c030380003001455402501c160120580c000e0802c02040c030550411642010b2540231880a07001c0003181880294042d03004186001d1586c02c400703555814041401960b0380313016135020600504021890225111241400035668100c0c0e240110034280c149480c64613000381c0b200c0003e54070704401d0200300a00d040c000c203120010400a00042450348040003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461196079 1250 461194829 461194849
    0x71202040e18071e0b0307020c090a020c0f06010503060414070b0d05060a060c051209040f0203040f020a05090712112106040501120f060506030f06040c0e01090507231903020d0506 79
    0x602c4c084105006200e120400406036511100c01d204440042079080d00080210314181e88400d4241d500103031a864041c02070005040001112005160b29490304000c01c0d0384980c0208050201402010300c00750700d040038030100e0020140d20a165881b1030b181b90341b00c2c0c0106030075540c03203100d685d80540005256004044001c80d6075006070280014079201492501d031680000307041a0301c10390b03440c8a40001229807010750b00482c00f40d02031a45060080c03051000d504425009144036441d00e204000309030380e10002154141c44440300100d021107000c80440300c58040c1c0203c1c16610b4248510710042d82580b045054442c0404542c14000c41c0d80e40c000c402a1051a01c4001d0070341010342c248100403400075085290422405802c6520082451401d2410544151021619150344120412050300c03030a28441c0941042c0108112600b44000c1c003401c1c400c0400c0c41280a40480420405102c1c507010a54599a641e120200c08200740400b00400a5010f60000601c8515010204109041c2000030f2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461197329 1250 461196079 461196119
    0x601081c0915111908270604030611090a091a0406051503040f0204050106120506011b020d032c130605010207051504051807030c0201090803071202040e1807 69
    0xc2908202d284100c0b000e42000305011403d200c0d030f1000f010440c6181c004e0540c024002d0b125207440702442c2c6100700402e94481e0014040d410900f01d03001c910b0307690000300d5086035886080020a000031b06801d008500501202c0381d4026041c100010320007807150403814042844403030a005050301d045c100b1040700d00a0064070740003d4450405801150004015900309026080d9002c1c480c00300d5001600f40c4800740c020300f00140c1541130103c4130201600a4030380001d002d0904840240c6a101800a044030f0304030068403c440c0e035400e403404d25000700300d034201d010b18612400c5030490803441120394611f2403041142c001c6c200203078080c000c2080d40c8212400c0d00c40c140d0103401c10600e04000c12103c9820500c1c0309400c2242048005410b82d00d418003002400d001030541d19840c901760a0203000c84100f5001ea405690401c44104001840c0100b144d60200070741c10b090140e03c503c41c40d41402400380b50030a41b110202070090140030040e102c50b00203070056a00032151201c0c1c880990210110580300d003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461198579 1250 461197329 461197349
    0x11040f020d1436030403060b0a0902030f04060209011b0b09100204080d0c05071211010e1008060103050702030d11121e0105010c08090613051c020306180f0601081c09 73
    0x1440c0c568981c080c1c0407140702d01008a03c4440c0c00c1c00b050f400b5003194003540c0700b21a11070340c0d1012600542000e000100040014241c1141140b400048000f480080200010103880e40042e80303600c00d0707014040c09000e0f0361a0b80100d4142116030b1800148500c0251100c50136841b44001058a808980c001c55055030b8208001d858814031000050781e505910420480b00c0340242c140201d402007035510090800c6001e0000d481d24242640009080307480c010301001e0003000c0c02500c000115410402a03074000c502071800103420360310b0000c228114040d11091100c5507080149a9090844c20405061014015121040191202c00c1e06d8002c62a005000310000041c003001008607602401c0411510340c042d401040c41c280780e8000007402540800e0001c4400e03403941030b09100e00c0c100f0000185c5103070203041000041d07204540005c0d03568100205036440d00b09200b1044c1c81e200e00d052180b0071b09204032074101da805503103134079410b0303150760314600502d4909d14141d00c0544060302c15051601103d452103d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461199829 1250 461198579 461198611
    0x50c0609130c11060405030301180212040f0602040f0609090e010c0206010b090d0c08010f0b0915130e010c08090105150604090c02070b0406020102250201140711040f020d14 76
    0x301e0303201500b15102104144040d200da00403241400b400f419215600c120080c40d0307250b0400c00340c2e0000314410510740a44620600000c84551340b02c0d40c2d0142c009400c0b208101002069150003c041d05c100e80243d400c0d500160b500141c10ba0300108070b4000e1341c186c9641071041d1050003800386d08a034011030206005a00c640010001d0b6110304005092071035003d40304098031042a151201d06070900d41c44400d0340ea6540030601c2041405200d5900b0000301161410301e0350402c4410040400e06910480c0e10821b2000c50f000146891607201c1d03000404910001e10800142d04d0b4042c000303038800c07940070701c0950070803000a240c40301c0c5041103601d0340c0300204558203040c10304190900600c3c002d1000d109500c076001012800001c0000a04018000740e40090717540c988802170000c00c102d404080025141180801200503a0040c0b9030013920302d801d40c1001e46070744250400964004809161582051601040c0d0070b4900312a0001c004840c0404800c0c004081484d04555079400e04840e209040c0080742 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461201079 1250 461199829 461199859
    0x181e0319060b040204061115040302030f0901120f05040b0108060906010e2a0319020c03041a0d020301060c12050702032a09011d090a050c040b0103021b0a050c0609 72
    0x21058100240101c200103a9030200c40c001c1001c99004d038001c035020a44845c00006a40303010088101d942003d46c000c4581c508155030080c0d502d0040d41e040c400b0601010a04806a134440c401c4042c181404071410f0101041e00c280c40e0000300740c25203080c1c0d0f812000c03000210b80c519000a205000d124100c00405440e881d000041290301001340c18410300e148041c05030446101c2096060172030307003a1303010300550b682400010500c8220000316018800b5005000704814000088142c808403507a01304400c030803151052410f0914419043d640da2010310100011a11a50007074a4414091086655810005c0080c1c8142e409003e80307040294190301c04001002a4043c2030190031042220700c51165030030b01d050001841c1480240c0003602c418604802143c00c940b0894803403a0080103450160519800603150641c03656402420607000e00d45901e0340091340d912035411107501c00310340a00c40604680d2645600e40700c000260080d9080e216020035440c1c20318104048942d0001c00401d0325078402185 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461202329 1250 461201079 461201113
    0x706090605031302060c0105070233040f0507090c0311070f1103031b06160c0201051b0309040606020f0607030c0905150f0a0f0f0e0105040b1e181e03 66
    0x800c58603100901c0d540c2c0301c3c010f84409000e4038581c0649800400c00d440c0940000340780c000003100030000ca428107600100d0144100009e441020780b4507448400555860034910310500d0580d1000380707580b00343c03580056444216484205503400725602400a0514201144890b000d9104080c04015824085000280d402c400034a80d154026090300e0600074910a04400109407039040d514075005034080001c0640303c092002007030880307401c1c440d002c051140c00003080d40c022a120103d5440401e0041400700c07804009407078030a01c00800500c83c4545855000b0b403108118070420016109040201b001e042c082e00130005a088143e40d028852803501c1c081204074880d090702c440708610100070442140c051200101807580c00381c0c032501005428514010442c1c8681d40102c01000f5081440310b85a83c0e0110850b802c0301c1108a00507140c8802c039410300c105120841e4140d09000c00014554682d412140caa60b01c0200200c1d5812403240c852100d803400303070840301e1759075605130021081c00c00380ca001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461203579 1250 461202329 461202331
    0x506161407030e0d0303090501020a050a1205071707121e0e06220206040b03041a010e0121031e030c021e030f1c1e0c02011a040b0f1807030e070609060503 68
    0x9140c0411f5400060725001d089922940b24100012000140160100d40212132004500d441d203c040000d4a00f40e8002015014006020002c1400000c04a032f40d076480740800540d1090008420043d04035680d004154030844e03000705207002420204105a1030320003085140c41001c1602c01a0460b0045545208180c01501c0e03003282c3c0981c0602000c85d0101803400030b14422441801030071400c04660400c5c0380d403003805034800c030618071542c1e00512440d07066890300b0300031b45918500c03c040000303903140039580221004514110b041d52752020280d5540d06410540b8040c2882d000d50740058010361405081c1201a20500c1d6540d004020a108000c0c080009200307501d25881c5105241d00c00421020659040001004850f500c040c624202510781d40314a03240c5000724002000900d0741803142c05107804044904034402c0e580c94107100c0e602e4850501e48400140e00400d8407100144881e017009644c40d00b901c680001a1800d40072001003030000038000140e80c419126a14594a032500c211260f0380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461204829 1250 461203579 461203583
    0x2010e0f0d06050108030408210403200603070206061003060503070e0a1d0d080c0304150b01030f09030503150111030f0c0c0a0e04020f0103020f071401090506161407030e0d 76
    0x16105900482c200c1d2051501810304d41c0e001e5959249080d51403494403542029003201803040020300d01c44100c0d0081180d007107941c401c01001c4600010b42521070010090a0380e1600f11100008003c0880c2e40402c203207120710340480d42031402c0341245104404441c0c890145940542c846001480705d0281240a81c0d0300024048000c9010400c1e1001074501d204c02038050750701c0d41d00c660740c41c015a0b504005000d50102b05051454218582a264040791a055900341050305548030800505039100703030040929811507072414040046a40f0f40201207034021618031082038240c080918880d8410044c0f80e51188000004509220030810410143d5010340c400e1485031080c50340c3c42c160b9468205e18a0002c103e100c25641143c42c0c075006128440c0c601c00c080d41e042601c100030b44440e164803c0d080d41c20311500300d400c204905c55418203a80c010f0070110009015031050a041222901d900c142c03c260040b1103503241500003490948150040c054010002c1c04550b80315459055800c00c004a111014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461206079 1250 461204829 461204839
    0x150905120705040c020307060c05250201020a02030706180b041a160f03050a110a0305041a09180105011101050705070b0c07150518030405030601030b1b04080304140d02010e0f 77
    0x41c1d40340b00160840320407014140c00f41c4c1010070101e01703001c00740c07040c0d40900515080c454684085460801440300c0d46041c0c070621010031070206019079100300f0001e002e00703601400f1102d9142e01c0302c102900001c00824807240341c0f003106102103503000c01d5005440440d8a842084003c000750b045030107216412100350f14a900c43c9940030100820701d010036061800f07000742c0b00c0e07039603030030304088000c00b02c2003001070141d0103074402c80c40100020740c000201c40890305e07c05200d03810150b89101c02c840e28070404007000c0d4080f100d17102c5c0558000c0c00701c001038100c940c01d03250900d8400baa000080d0136941d088504801041043c444200800c022170070b440d6100d655400420301d880229515003440307203ca0148941a02ea4401c100184010030001c0014031014080042d41420b24190000b6034800c4140070007000740400700f001c90002c00340804012107038103078481a01e4666455112043d500c2c0c0040c0300f0b40407045804c521680850600d40a0090402d806941c1c9007084003400303081c880c00d0111030501d15041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461207329 1250 461206079 461206093
    0x902090f09040f060f0f06080f100c050d110c01180812041403030906010509130506011404061a0a03050703020c0a0f21030b090a0c0503070f020a06140a0615090512 72
    0x7442912410103194000304000481b48109004907003141c0c0d081e000702000768855038040d200d0b60f00000d08080d01040300440450183c918200442d21030041c4914041e10380e00f812210b440100854001d402e095149100800511100c0f115540d0000c04458000c1c118030070400a030303480700d1324003410150300a0003100555003100851517200e1942d841100c200c5034580001c3c005200c1c51801802d480d4002203507003405113804880303848040e01c40030188038588801e84041d91540359a1110342210004000002211134009034110000d050703a40080461030000e07107000002a801c4e030080c0b0071f44000002450041805952503a907040d8215050402613444060040c0300c1c50140181d85d845a15488559801141a0b1072000900100030405440a01a542032011420000d544a0203980d0302540618285140c4400b0400a80c00c0400401d0041c0086080004070404201101c0d061400340e600700b8810403006036251521001d8101c0720340e10f41c000405440e070401c041d14010240380c01c45503039001541c81d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461208579 1250 461207329 461207333
    0x11403010623030c0901050f190e090708010b01050301032103060b0301150912050c1903020d030302090f010e28180b010f230c0f010518070902090f09040f 68
    0x1036000c40000b00040070750031070011400c078141804800c25011055a0480c00380d4101000581c0e1240541107a03401510208480c45142030300306a914000d1800100c040c5207810f041102a44803285030149521b00c2d800c00044400b03d510420481c1d04980d00100b103040b0b1030f9071080c0c9640721100200c0c0000209515000041030011065001b07500a01c0581c01c800710300301110001030116002a44001c80d52a2040000340c003250003c100030005036401ca480e486e011a48080b848004e20483e0006508000200001e0f0101501036004000c1700108544404a00780301c1c0c001100c60110011000c0d030005001040301400248540d58048a00003580c806241030340c607411004074000040e204860869101c528900b050350301b09281908500707051412140600350f040c05000f00450902800c0c103890800540c0c5030107150180881c010210b00c1d64000e1000c0d00700080f1203000c00403003001c0c56613140100a0005080089803080b1040d0708005020f240c90a0145000c201e030707404004000799a00700c0f04030302c9440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461209829 1250 461208579 461208599
    0x2090405010f140108130f14030307030f06170703140309181b030c07031b021c020f12060a05040c1d0a050a0501030b0a1a18011503140114030106 64
    0x4042c0400b114440c01d154a0640014000441c20440c0c1e410b214800e0203100c80d005c8072414040585800910702c4501000c14a0000346280e0310f11102603142c0030100502c48409c0e80340d00f000c90000c1020388148921520748161521054038010407600719840b0400400c001180b091245016102c804292070410310f441e00800c00c004450070b09420b90304002410405c4d0003110b60031140d000a10360f0701039401c600c1e01003050541031254180103018002802e030400c1c1018080c001c80014254054090b0a141100e09006a055000058100d1190482c1d00d403d4040781031a0f6000411804100002c0040b5294041e1700700041c400500103880c3c1881041c00494000c1c20000404130400204400c11a17910b003004e03203803040703d4000e4041c020003410400104007241c400240160450b0f5600d1000030700c901002c1520078148801c5211981014401c410107558035030344259075040303a035407000f15008154103103011400c0b205010b202d000c0b00c40d221070051010707444050796000406000707000010520f4a0b035003181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461211079 1250 461209829 461209831
    0x5090906040c11121308010504080d09050a080f0304031101020310030f05160e09010c0c030f0e130e031c061d130605150f01090f061b0c14120d0c08030a02090405 71
    0x4c01d2004000074a0a0400844680c401c020a4540000c100c0c90030160b80e000740600c00d101001e0151500cad43d0111003840024800742c0c0320706510079040c0703603680e8107840524041e0704100c0341540030030f1089019284000c018000c80744121207095240b01001d007181c5e01c001d01d0038101c00c410303180781c1310303482610001e441d94400140c080d00355602a02c0c80381c50b00485030781c250f4082d044203c00304403142c4041000640c10050b2214000124102000008500408074a094112007804001c0d41c0c105480c0e00602400400202000e81c1c10594080403031888000c0241610031510801c0300c80c51030403180b10a421010400247c1082c905540c2220f41041c0d6207445083d550155030f070485603000f505829246180000660802000a0801800d4145401c0709015031605901c505014006103418a01c0c0300c00030107900c3c2222603888401c21034a142c0b6010560044401320a000f40201402d1021002c0301400090101c014801e540c3d40c42c1140d840759a4035015508081c141c0761803240c080c007001d01079913194026030b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461212329 1250 461211079 461211103
    0xb06271003060503190b0403030209010302070f200d0b01030803250206011511120319050a0c14040e06062503080703060b0a0206040206160f0c0f0605090906040c11 72
    0x20a82c80d003040109424200c005803040c28100000141c3c000240c0760700c3c541540107400d03080040c0c5401803d40140c3c007074810300b0401041580c44038506010080003400a210507102c64010080c41c0d500c142c00c1c0149817035500c102070900e0a01c1401000000c001d1001181d20604c4d10310302c03140341e03d801144e40b202e40c140b40340550b015130040c6006000b0741030070034070300c000c01e14091510540001680c010340c1d440f02c01c2c0c0000d0345280a0008001403401030170341d00c1006500e25004042245103030803003180b401020382480e55000110f00d03102500002030700c20160740582d107000b03010640c26100d0324108055981700a2080800f0035180204940d084092110805d0342800703504d40350202d2070680380040c00c64003a5002120072280c148816100d6039400500590306c030354190f40080c0d070f8400f50950340803185d03803802c001490308004e0081d0300d0401c066180717548100e036200d010400a9a403120700940c0c40e802101c600e40e4000c1c480c4000540d2a2415811034080001c4a0410ba00c1e030340c041003901800c00b80c21280c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461213579 1250 461212329 461212331
    0x40e0103111507110d080f070b0f0108030f04121b030609021206100303050f0f0406020708010e070b030703050a0b1002030a09090911120309040906060e0a0b06271003 73
    0x41101c15007400c00c0c000c01640810a6010b10b4182113540d0240302c500b45458190085650703000e01d8007005140c0045032050142c6009071515841180303045040b080c000c0f1442e00844003210000101410000159485450303002881030405091504a1a0816004130150340c00580d00c2e551101040c0390040f1003015602461020403042210700500440148000540903d41c5c441004c02441015421040040d82d5162400700e5496000720702c440080e006150780c0c100000000100001c215030001000000c40c1c08000003401002c0803000156110a140d110301d0030032480130000a4600351003a44555031100c03c001c40021610200703004140006c001d19010005079000041c41400b258100705240024003400340d06001441c69a80e0344183d981c031043c2c2142c00740f600c103c00c04421541c140161034500001910400c40c00c3c01c00d0a00601030030b2140b0854125061300804604e1490f014001c0c60b4503440050a26481c1041640c000c0030140090081e81103200d11030501d07400c03a50f82c3c0b05003900b40c0340d0075030754 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461214829 1250 461213579 461213603
    0x2107061a0118050306190209031e061605090f061b07052b0f0f05150403080108010c0914010302040302090408070501051e042d03020d0e1203041a040e0103 68
    0x1002500c500d080b03541e162811400524100001c0d90001503c40d400f21407100c45c0000103000c500040007074014002020341c14044c0076080d02c80000350411240445070701400700c1d030321900d4180d805d108154a00031040000b41d41004809144d04004400302e000c440054401032500c0c841c4c1c505850110407004034071a094008000800c002c4c5012950919941344030105884c10101e1440024039065010400400071043c10304007000b88205081d401340e20b590408241d60b100161100d0090303440d4012501280450aa0700c00415009014480e44c40c4050040e101c00301070300e08000c40c68003022002d1540714105a0208404001070300c0307003aa1140114030600303c103910b442c1a45030290070b584006109071144181f41c0149146200d40010090b0056000200034078550001900d40004402841d1b942021200310800d0008250327001424290342109940c0e40ca0a15503403008000d8131102540030041c01b54001e00c024004d659600380f0380d6280500d1003040718a031030343c0d0f40c2c6403030064a406d03841600e141a0601c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461216079 1250 461214829 461214881
    0x5120106091b0903060504020402040513021e090f120f100b1f0c030c080409110903010b0a080a1b09090c0602070b0301050d140109020301110904110c210706 69
    0x8001c603085001c82500106402d802000028100030007444083c05881d2250003290554031954121009400c000e080c0c02c0345044c541e0400c00103503000d04100e40465544c4086600049844d00650b40d80203001841102411201c40401400c0741500304584554002ca8003071042c3c1450401141041c100c2c260300201d152202d0700104510740d40f003507142d514208040161041e003590b000c03881101d415403605200d900d80100c0c0c10a00f2071402076800ca107404500d0300c840d0302032820340d0b44c000d404003003021002030084140c2c42d0140650b5100520404003598041c002550008014141d5440e0002c2c42264503804103a07201d051000341c07009208140c503840d040c44001d018080d8140100400f8206d2030402a207994984400300e504002c94440c0030b80480030920b00001e412200790841540c05400030000d20203c00e03035105146144d40300350110361189141c41070202111510000b0b807520403144e28050581101c5200300f03103045043c82090000c40c9207040001e070000800c140b150982030904040d000030340bc1010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461217329 1250 461216079 461216081
    0x124020f03130e010e090303160c0203070603060311031506060702030c15031602010501080d350a1817160c080304030b0a0504020a17070b1c0c0804080307030903090512010609 77
    0x103070000c4942c8412041000401b6100004594100c030401000920118206800711041189004000e500d802908000100700e981500004192401544a002c0a161726401c040d602e0a40b180c0140c5100346100000b44680f0301007002d00050343c0040c0c2501c184445020001d603200d07c5113171004200103804004c3c0400e050103624020140403803400208125410807002d541e580c2030b802400810030034500b0442c402d154400d14041c1035035240e203410b480100181e010100c1c031a101122110201490031900003e4000001e10b440c1180c2c1e040820501a030403c402034055940c01041d420300412000d503000c0c000140070300545c200614401c0c3c050740d00c460551400c00c00d045005060b00c464030b41054240700150751035100b024100ca0029901028040f0b04002c128200310480e802070385011408100d041c081d0712001c0b2482d0090b81c42401c100180164030384240d82d01074090720094600344081c030001c0d4003140203600400d8024000d081451000b0780e031b0b5000400041190049500304e94580030204052055 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461218579 1250 461217329 461217331
    0x4120605160206010e0402010c06050a0c020d180b0d1404050a03020601060f0e040e07080a08070b0106030501030f14010f0203070507050607050c0a0308150d03020d021002030124020f03130e 83
    0x200036070311080380319240c00035560700c01801105094000078001c2030071607009880c1a00340c0340c1d00000500040c60016648001040101030400c0175004008449030a82d10502ca41607074510904100210642441d644034045d40120502101180e0386521450a0700620b50609210f140300701c0c014000b01941d89030003410480180d120005200300a40c03d05540398002c0c10041070b548054074000307988115241e0035850410079a00c49070f19402464540c00500102c4001055028040c1c00c11003102d036070700d040850848000f4840075100340404512540024580c5040030607280c4218008504541543d400c14100d0b402514a080070440c0010b60004009040c0200c1d98804807900344075040c0781a40010310340383d50007014002c040152190025105c1c0580185c2080e242c0c0d4058402880441c06143c0a55550003079814080075110700c8020312100f22890003102d050321900039030340f101d95020340c0b6040210400c210045080d4040c45050000001007040544002c071034410044400c1450f0903600700c1001c0d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461219829 1250 461218579 461218591
    0x120118030315060818071e030614010803071e06020417011b0e120111070302060108100e0a020402090414040804050a050103110a0f0908060405011d03090904151104120605 75
    0x100120040100791303040207020703901c40807a6404841c1c10702409000742c1040c40035041748102c948424080d8000755641580c00090701c1c8920402c105600800d55001d00c40d0303a01340714801e840d0f03000f0031801d400108400b2741c09800d8801e4240540c1c1141c01545c2c2d07142a604243c00151084164400194003c0c40901404080d000c140310310b042070304d1800100509546155020b50f01074a001e0b900035510304d000358030116410061107581500c0d0312031450001e44400083c0b2440b000c0c1d1240312110929041c00c2d20450a41c05d42c0c280040c4088041c03942031201a4025401c1c8550007507071086080c40301200846c005100e02c2c81204c0c190350b01c90a00d0200000105681c00450400d80345c203207031280103c8030760f0460b10200e0780e9051040f0120f61004040b2a015002d41012000e40691800e000c02c02c841508054150f41c441042c140034040b110918650b42e020f807540150b0302580c10000f01d008624013580d150094003001c0f030082843c1102c6188070000e58015840003045650b05903045090002d00c0c4140c0d90810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461221079 1250 461219829 461219861
    0x51902010203100b0712030b03030408010513110901080a0f031b03030c02101104050d1e140106120f0b0a020f0714060c071502030c0d051e091f0b1201180303 69
    0x445c107803280215030101c50400804d042ea1245803002d203550800603280142548402407142c1c0c40c151003064000f001e00342003116003d012202400c2145800b40d54281a10040e400500d0114000e031520328001c2d80c4000b054080c030038010070925148040d01d0808070f085000b0380b80170400844000c1c000313180119a101315030345c251510420314603800c0010304840450328100d4401d06609024103007554222064512600b03480984140a802c0040d0b8039943d40041044800800805a40381c8400080c1400300c030006094402e08081c1100280501c84e8090b0040b44100d0700501340200010115019400341e070096924880d00c8241d03d641d59003c0101a0b0700a44940900e03003858011358940072218403432400101482d1b008000581ca61002405452607200000002e0149082c002c0704000e0f01d076861045000c507010b241000621040c1d000a0b084001c8540707582075081a40707501d411b4401401080380003513122445d070040421aa20900400c11000ba4415624441c10710a260180c1120024110003c0c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461222329 1250 461221079 461221087
    0x100206100e1b0d0b040203010e0411010f050f0706090c27021e0309010902061812010e0d210e0127020603070c11120325051c051902010203100b 63
    0x41c0442e0307411822803005500160b40c40e00d40010301d1202a04800c00c049801c24800300000402c00c20809085e8080c5004811420b1010032880044851445227100c88000c03940801c4803d11001440005044403805500d0001d080d40c150b946100c1c42911a5021162a003d0113400c09101d00f110340d03495651a094090461804450f042e1207215401e50000008910a002c00041c450f9842074000646a0750b00506980e51980c05e0101001841c0000c01c00c540107450580290049030014415040352a00b8800142014210b00c07200711400c000f02005001d0104405143c4c09990305c03140103800c2144100c000216001400492a012030f50520f220305001301014a21400540c40c3e0360100e80d0005468580200098040d04004400301c8613311032680003080108150340c4420080003030075000e1a06245194008822880c90480080150300035040b500102d1080c0c0c45064900c0f070105000d205410720f10700300104c04241c2c2e07000517a401400720240c1d400108020a110070311446401801b1144105814 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461223579 1250 461222329 461222341
    0x80d060509041203090c0f0f0f08032809080f03090f090f0a151809060c090810050912030103110f10080619050a03030e040f0e0307120c02100206100e 66
    0x800090502c03210181aa15217400b02440902c44008019005141212040303540d111030540d11030b80346224083d1000340c4101c0c042003005000c42142c03110300c1c0e2081e464044100302296006c0c40715030f4030b03140c100380304001000080c4402c00340450b0000b007000750055610780c00346400740701800e0318081c40c4a02c144001400c02c0704d4121005001ea070440b44c400d20004c1c483c5140c4410a00a035203640001d486507000b808403107201515a00002c85180c800c81040c400e055880300b081da103800c45802074103104d800c01ca01009d818a07403603004c00c2e40b005500c0704440e0303941c50070b202c0540c0d40e9000b0381081d2041340ca0502154418104401c0ea43e00d40b16041c3d65449032007000071001407014402409091003100000c40f1034a501201c00c60041c003804d801003007501729030350328580a4214002d034a8001c0c0601d080c010310001d04501031081e04840e0040c44040c1d0301d000616a9070304c44d0b558441000406018090442e0300150b150b0103c0d9190400540e0010140c90411506054800c0465032186510084280400c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461224829 1250 461223579 461223593
    0x40c020c101218030c03110106030212060a0e060108070614070f140111130311010c020303040f080105090102070201080402010507030306080102070c1d2205150f0103031412220f080d06050904 84
    0x17040359014604442c0504080003514050011640041e43c4201c01c40644030500c82c0106041e409441f640e4000c00c2a01c4000060325269142445005081c0e0417400c41004031600803205034051030140890145414400e545401c44440c50400a43d543c100001d880340013601d0902c5a41042c00540302d610342040c0c10030030400c1c2c1781802070100a0500790110641086070b40110600740e0f9282d401410baa486543383c4030030354203159251180001303640c20007001c145c1c0c924061007110b100c10f4040c1c2d030310092a0b0707603a00151070941c441c2d40110101542c842e00040c245c0f400788054079507a48658070607444146005249480003100d03040596096a1880601c0180c0d060304c034004006522003d000d0407131002c01c2c240351382008004150051664664810496600c0f4007101e864185d0f03100f501d5070f00503140000d03030400d2580204039403449081e9140300414007011500d62805c4418164200c00c084507405a901c410b103039050a40221290072010400b0032000d68107000d0764002c0c14055400701124646a00c6406c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461226079 1250 461224829 461224847
    0x30c1905040614030d180b0f0c06090c0102070e0103080a0e1518091e010e060d080301030c060f021605090c09030102070308010303080a0e10020f04121a24040c020c10121803 76
    0x890322000110411020583d00c281e8043c842e41c1002c2d201c2c3ca152015165407260340b40c330320b05801805010b00124504003650300080c1031f40c0c0c00200031402c000903581c0c180d170310000103542664080300b14012a080305540b40001d050011000c05480e012519000078401c3d280000340c900caa10920341c02c04600c0f0900031200150440d07404d0780420f640740d1502404103c402143c45005414094000b001000340038600007040d00b210440c0d95007501a9228405c02ca8544826040d200c0c40c0c41c00b042c60400103898004425a0042d101d81c1c003aa1409840d00c0000307003240e1056404802045015004005150304141c2c05680a001e294042c01310605008280e074490749021030780d05490b60b000c00c0c07040c6001400819078000c3e0070300802210b5040361030701780a2401e064860800c40300b0b81c0c00d00c000038030760034880c0310b0807400607001081030a020104004010250400200850861180b801c50180a42d80c812108414814540310003500c0c010350410401139401c2c5030003c12407100e1016400000a40c80001c3c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461227329 1250 461226079 461226089
    0xc030b10050d0b04060b0a0f0f050301020a080117030415110705010f021015080a0b0a0b030102040302010c02010e150d061a2d0403050102030106051c0506030c1905040614030d18 78
    0xa403c0315a034501e002e4005100c080c00180d008108400007003010b944c407207001003d45040d486580c04007940c03003007010b0a078820301400d200040c100320700411410204410402c42844600180da01346a100e1031400e035090707100312100d00080c580e4074822043c8030062220380c0181500f07180052403103c0146029513943c006000c503052140d03440301c0f00d07c1c20038441c0c076842001c2d1003048252401c070305440c14031100002c0d00360392100340e0764504260a56141380500c204c60482c0d5040e142c0c02c00035507141c0c0064640030386a0181d150800e2031500c034442240c0c05100108205445000300041c07141c1411917010782243c1031400c1d0081d0318030401c00b9456440000c12400517000e80010340c00c078100503545070184d6030f0045900061180d8000320001c41d4072500302c400340414010103e04c1c042c4214a030604401541c1068544c16011380081c0c09000090600c9580030104000402c400d81c801c40da144003042c00c88a8070391011512403180e151403180c034901448071000300c0c2c0c050301d8440c40d01045884504211040c034854 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461228579 1250 461227329 461227343
    0x9021305010303030c0807050301170a0512070b010e0411010e010c020d0302010e0d02031e0705120a0207060e100801090b010e0d1401110a0e010302091f030e0105060d03050d0b12030301030c030b10050d 88
    0x214bc0f031101e82001001d0308075500074181d90745848084501915500890700854641017040008100748a030005007504c42ca41108524290090740001552180000d01704c00d030400104010303882c003588546098201083c486d84c0001010324a0144071420701032606081001c5400821400340b00c6401101036082c1c440c0c1c2c030b403009640c1c0c2c07000d440d00e00d2501b42600403202d0721420214507500880c3e0042424000c0f41c14a4548a0326900f2702030401074882484200e401c0441c400600510400e001030b8003a103078524040c10490704014141000507584010030500725010003d011103040701e2602800384d9500d014070b00800328200140c50340041c2c004940411101e04066002c6040d040681c1d902083c80c00c4460300504401c028007032580e008007d000d202c80788400c1982400b000c5000ca00389003a80e070301229055034415040030700802525020708503040005034419070310355010407110f030140001c5000307610460400c1e03481031851418898880d0020040c40201d2012041046552032741e1611054071130380091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461229829 1250 461228579 461228609
    0x50f1005032a1906031b03020c100506060d0204090204080f0f0a030e150412020a050108130605040c0b03090d030e01060b0d0c0212191805011e020109021305010303030c0807050301 79
    0x4501d41000a807030f0b11441d00d0034074100141140e0194000e543c16064445085480d40c0c5c840300686c1030b84901c20078030480b94000302c0f9881c1214595032105421080c002c0c880f91508800310800300c1a0381044e0441c101c5150700040400c114034041080c881c2c00e400b142e011307000000030407040c00e807901180000a8144080c05260b080310340c0e60003503034110003904002c4c459240c980710261f284002c00b500c101240208024040131450b90700820010b44200349814500105c003910340c0d00c80020b080042c00481d544149400701007154040035020714440c005440060031150940d038030080c145c030400380719900f03540d2400304140960054102140c411404051000c10201d6069004901d420301d5154107a182c0b07503000c00c0300008011103520b00110f1a465980d120780c07401c0c0400c1c0c900349030f88191155a0104800020178080e0981d042403115008120b0f000010308070595801241c90350458443c20010300d5521401441015003600c00d088488040c1d240c142c1c014600184043c00700c1c80103018565240741006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461231079 1250 461229829 461229913
    0xd0c05010c06020f030112020f120709110f0a020a0c0f211407080f070614030112030908010906050f250534030305010605070c060f030f050f100503 65
    0x1c0c041300c0c072141c40300b13004580c0c07580c1d00d072500b0f1184141d801c0d003203120700c0981411607071600c1d148144200b250b0224019001091902c0030640090001014a40358548140618000b0903e964042c4c0340a04954024119a4109240c520b04045143e0008000c80c00b2401042c00740603070101d00c10398041c0c00d10f1501e68920f50207007414025004000801006441001da0208400c3c1c008507013010410b40c0c080441d804903072a8081660143ea40040361401c8020600040241c0c000c10402c00790842c3c001d08104500540300e01c009425603000481c03e5441c152660b0500a0146000104540c44900b046510181e41c080000740603070040c175600c40c0000c002f40400d5020862120400c00150340201303090043c10030055800501a0303140595007600460b1800c40005807041c020400c45143c00d5020042108060902c0c6003980c030aa80d001c060001c2640e5041c80f00b0903c0868410140038100a0031182080c3c500015000900541900550f000c1d400c070794408402e0301e104018000381c0d01000b00154134000d05603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461232329 1250 461231079 461231081
    0x602030c0c0a0f14030702030c060901090b0406020714060f0d09150903030902280306020c0106090c030b030d050406140c0118140c100903080c0a15020c06060d0c05010c06 75
    0x400c001c0550180911400410000446aa15041c8900c40c0d02d5441804410036940b24055000003030b4258104c010396070300a2910f10010640f000d01410600c0743c0c0c503101c9006a107143c1080c1c00c018096840031009010a2109003050900000b0440e1000e26007250182c1d0071142d8051801a111f0050300d0320410360820211120f4040303000d4542104014444050900401801141e4002d034002d8042120035142004180c0001c100d540f0440484000c0c98030b035540f44e100940c04640010300555840901082444550042c0c00c910030f10390341d0110750490310404050811151441c80f400b4030008100810a00c1e420041910952045100d0583c41c5e00a01c2809405410000800c0b0501c0800c80b2a4008200c42085841c010f00c64200032207111082d0700040c000c00a80c80c003080c0c40850b0b40c07031504000181000004100c0c2e004410241c90303145100344d613101c0303110b1a100e0b1310034070050300401c1c820f040c400b0070003c296018104482d40300818086440300c542c14000b5008440c10014244400c00c144109 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461233579 1250 461232329 461232337
    0x1303050922020a02070f080a08161104230709060e060c070e040606170f15040204090b01060f020d03050105062d0c0c0f0301150e13050304170f0304120602030c 70
    0x38001055590702c154070343c002e4481280c1d000d0f094040ca00040007080405002038079064580d070290581d0300d0440d001c810030760059540310084658541d0390100c50041e403201c0c0511800b48940346003c2881c0a41603110203124080200150100001c10b04100702c1c103540300c4150110410300740e40aa68444108901c2824000c1c1e0f038001e14501d080070340a010030800f803a8070140890322503511460313400d91140751041d154000c1905141d0710f9481035294000d02c50142c0011500030340b00038800078a44c025580d8008a0100c00d03440348001c00e217480c00080032a42c042c03000d00c4124526141c1008258101000070342107002d50079000f4880e140d00e091003420780b0046a11508403d00004400c0c3e04c03560302d40d01840e902c1d0100b04c1410700070124191994070300e003414003c40000790045150040c40c01c0c10b1540a00c3d110f40000d10702d810081000c501e00c40030038018001000035101600001440b16110340c071003468a10140c10460300c952040000300107044440ea880d00103250700c05400b41c0e0b65241d40c108483c0c40c0c00b0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461234829 1250 461233579 461233639
    0x306050609160813170304032a081803010f090b0601020d21020f1c11071a0603030f0c07050907021c0509060d0c0e09070810031106130e0f13030509 65
    0x95010500d85c2d91589a005035100364420760752501c80403030888610700d520440602c100b5400c3d011449401c00240d4400141840500e01e40040441020400c000380c290344001c0c074142d100343c0e03444540310188116040c410f45d1101d400c0c00280f03141d0510000090400d00000c00c056103900b02a800f5810900030360b0100e030348060001d07035103940b103000c1080f0040ea101c4e05402e00c1940e241c940155003500e10500420381d003119070412a080d0840a100c542c2d401d44070001003501e54503001c01c0001c0c08403d410740c0090318001000100034405c40d8148014045d6400300500b01d0740030b550111011216001c003100304c001c221100307850103640740d0740c840e80884c6603030103000040c044843c148054101c0180c1c1c40492000064011105202c0c1c54503007110030f883e0358400f03666048042d9071020043c00460703da0003030840384440284c2410300e010090205d101900c2030603003246c110035040106100c0064240c882d03498008403000c071840100c0c0d030565009850343c46040c055030f000d200d00d0580b480b1806d02c0600e18224540c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461236079 1250 461234829 461234843
    0xb030910110c061006050d0b0109030503030a09170f0f13180903031802010207050d050717030417010b09130201020307050f030a0906031b0e12070e010306050609160813 74
    0x110701a0700032052a00000d810000074841e840010362a0032082030341300c04440c2c664a03001c2c940304c06100c0d40c1c0050300841090b07a050003c84403001001543c2080118403912550400040c0c0229503d0004920041c0351900440302c45c3c28481d0460a404500c201e501886a401005a86e4010030b80411034000b11175100070042400c402804800700c0194000d02c481e24426076041210b000c0d03100d4000308148043c3c802900590040500740400d0a20003014502383d40264101c50790550354084203c54408184039139107081e08045000c0180d500c8034003001c12410122002403000d40c1440021480d03045005168011440c007008c083d60540e4003d20803150304a4021003600e6910a406140f0380e41c0ba800300d0784100c0041c4600c203000909600c00c1c80b42c1820101c0b40303081a507c2e0a44c45e40100c504002a10003d0303404020002c6100c540041004114020310341c0760701c80b48856256040c5001100c1000b81301da8001c6603104104404428001c41d01a0160554207002a481e110300c0c0d0010b0702610f0780c500042180c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461237329 1250 461236079 461236091
    0x31208060d0b0c120702010c02120309010e0a0f120c110d080702030d020609160305210f130503060705070b13032016090603170a031404110f04060b040b030910 70
    0x542c284002403001000000c00c0c0011354440740c100724202c4100603c2800142c1118940c082030030200302c011034104145900100c2d985228002032420700780100011500c1d82c07120030840c01001002100421a00440c0c240082da880703d40d141c008100c070903070502c180b290302e0340f1002d85c0400000e607060303901594024084070b89107003440f24080d50780c0c4000d413081d88030345c8076002d1030107964008030001509a0341d100c3c000d8070702e40d0002c0056040304110a107a01d10341d83d01c00e021400381c0042c104003420142c0607985900302d08034a064140350078010003510031401c000c0d0401009010540c10391000b5000441240380720780c810b0303840c201101d0111043e44c085260b2542d2071401c583c01c500010b4802030011072140741d034840c0c41c0c0d1100c520040350414800141070395200c41c0c2c13000d562280000a015645594140031400c0c00e030718022480e442100b142c04440080c00080c92070b0742402c1c44400c15a000c4e90070740d420003005080c800148030601441c4200190108000000b50400c2d20512000a607a12480e4040c80a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461238579 1250 461237329 461237341
    0x190315030605040c08010c02100209040e0607360b0a091809060b0609011b24020307020115140613080715110d090608041a0c090415031208060d0b 64
    0x2920080e83d041d5000410031030701081e6964184511088400305400902503016542c0c0860040d4000c40400c50307101e5500d6040f05200b9500340b284610854943e40c450407030007280025281c0802c102c0904141c003861081d5a003901d810342d8030604c01960129012076840b81c03465803040f1a09101604011600003001c0390301050108a5000b41c0d0b00240320701301c240a1150705400b4040c150107440d04850008001009844180c0031022031210014050020b281280c2c6c0a14403c42c007040d00355a41c1200342e9400402c1160440c7e080c450700d00c2c012000c106000a443c50000041d020802c54074a140c4203070400281c060403103070403a1300540144150b109a40d41c0305e945000440c550701509506a01260410030f080c0f0000c900030404042c20401d40e1035031a145420848202e46c0350034010011510b03245121100240d4100362412a4402c0c681da14945076038400d100c0920098406680052480701c031102000c0c00002e0007103865030b50b038080500d444280d9a80c0c03075000414440b010b60f0081c000921050a02c07103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461239829 1250 461238579 461238581
    0x402130b0d0305090a05011d222f070f1227050109051206191d06160906090504050901021210050a1202061e091c060e010b061903150306 60
    0x1440785021201041c08546d24030054601d050130300d0350245c00d031070200c905800c00d281119107a4110b07201e0901140310304d1900500303441210b01c909103008262180c0c00014040303501001c0485040c2c450407001909000c0283d45000380345008080080803580070074141054580b00381a1131190f055007240d5800240c945840c0b02914090350300032140094041080410741c0e080c0107400210b11100900145031642c6c820b238403003000003181c5924024490321503050103117880c03040d081061191050310140c8010b0801d181d0000203980414070040c2440b410050070440319820844100880e1410b54001c0713031641d0307030b07030740590080c45620440405880a1402e03c14100948490801076410907074441595549500d1158400400181c009601c00c0040081d00410800c00d03075590500440c0703e1002d410840c0c00c1c400140600c1941c080c0388511410b0041d1482402030a001d0391070301c8207228008102500d00791004c030700e01d8441c8000d05c025040900110030540c901c6940010341c50604510300519464036450030340c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461241079 1250 461239829 461239837
    0x1c02091003090f0308091f020d0b01080105060f1813050703050a1e051b04080f0c031902010c0c0b0315040b0901080a0201081b040f1d0c030123030604050d170702060402130b0d0305 79
    0x8276091034919a10015406038640c00c0c141e40000300500d0604501f80c80604c802d03402141840c60b1031030301c0582c5480d29110b882c0b0501c1d030315500386004200c42c039204000074111000207090411030743c00c01002140e81025401c40042c501203c031004a034907560303815030b4840d00c1d20100e59a03d0643d4005000140c07420003145440c031480002081da51000052000c0695a111050071840844d000542800040d030054003100f0010303100e14103805420b0341e00c4c08809015042244c14a210900b507241c2610301c0e14061040c4000c081040b254070481d5410a9103640e521003241034001d061040e5440851506890500000b004490b5901880d40d241d81394071800000780c10034840c280d010a2250208481480c4081000d44110f42014050341140c0c40e0542210740d494900d2207060132180341114549007174038288905803255000e5002401e040d055507500821300300021101340c0c03044000c0710502500903408581d070f43c0c0040d011180d0550f500c8103000194000c00c0d44a000980c0f10410030f82c410304041e0080090 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461242329 1250 461241079 461241097
    0x403080c0d08010614030705090d0f060510060314010b2b150e071409040212040803040c080601080c0103110d09050d021018060c02031c02091003090f0308091f02 71
    0x4551642c4c1c0764400d40b40c00005914014810000303000240320340d0320a10242c40411070003054018843d00c0d58450781443c007000602a181251180c0c01c004843d68008203c01c01825039203020446510701101584003c0810b02036681030610000e5a46119138001030300d8a060319508090110442c0c0b2030724094000d1005051110468084d0b581c005030300203204503924031805541e11901040018100c4145071640903080d4954850b90030301c4601181e0a081d112948100c0c851410180e070f070300f00343c03d000e20b61814a034001c0505501c04401400b007000c001c15030005148003802c021030241442ca02c0d411107405000070400d007062404442c4418480005a4941c0b04a481c2c2c0a48000441340d0014806450503104200000c00c02d504c400400104d00354440850b840c036030320590b400c04071a40d0098210745c0302d0f1820104502e0300440e45036034514294000400425641c1010842e40d01d456448139030b18030f4200800390234003090b0b4000030308441c4284030001c2254110311021101000d8140240300a420004035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461243579 1250 461242329 461242337
    0x2060c01021e09060d0504330e070503150a06050d030521010503120c071a07031101062d030c12050105090f06011e08030a030609050a0b1c080403080c0d 67
    0x82c11044408040444203610000303010a03240844841100703010300f4016000700c4034007031950b444a281c400302170021240703000204540040311001103400c000f550b80e82084c140700c541204400300080d50f80000c8101002c40001c090180943c0c402c41d007180140815440b09820404c0d442101c002c141e801030040c01c00d190f0b01071030450390385500e10030403c0f00310003400381e2601540720281404224103110050000021050f04130355540f83c465010212900d01142c01000051000c1203907c00c158001082c9180070411310001c000c55807412104510420750001c3c0121000505207404002040c0001440d001d590840b44804020342d40e441744401c150400e5006a40b44d520f800045001f2410100388100e40c2494407000345116401c0c00100301d501c803000d09a0b81003c20060200103840d0b0018009802010301d6920005a6149002444016207c00900400c1d0107850416010441e07034980c014022601040c1250903030264440c5011016446160009056504007081c1d12411080004002c58807103815a2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461244829 1250 461243579 461243617
    0x13120302060a0504150218100305011d09030901080a02210a060902090607080a09030b01080a200112020f040302060412060b0105030708040803250305090f0f030f070f02060c0102 78
    0x2d0035048441c259802000b91600600c4040c0014154001e4003240202d04001c10740350840704000341009110440039004a44c40c0d500402c16510360290041342c01c0c1044042d0306080c50500c2045803644100c82019040c04407034401b142040c1e41039810b64400300ca1140c51450220b01c112041142c910085850341c04103814040003050380f202500a40b0261180942101d082244640e0340e00581e401c00701440c010000c41d61000400b180511100c14002c182000207000c812500d81002030103542c0c00d4046907001c16582d070a254099034400407881c210100702c5401a1110f5000144403854880d550019502107030208010481048842030140114851681041500300c50740056515000842d8008045248100014007003a10360000b1540180001c480c200320320b4000da540344e0351006500c0d0380c000180d610810071080c0314041059100c803601c0b45004182c0c40d1080c01c01e03240d41e4450310b0081c0706280804680300d42000040203d075040aa40105011b8807002d000300064002d40100f00d0701821802c0040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461246079 1250 461244829 461244841
    0x1c0b0f040b0f060d090506040f05100b011707031b0206060a05040504030203040902090409060c0314091204030311011b05070611070b010b0c1c090e150a030312021312030206 76
    0x22140c05401e000c05800c1c0c12102c41c4074000c10003c0d82002c00c20f040865250901540004c2003844010305c180e00c81c42c0d6018842d00141840c9207098607410f18003400d00d00d004411602c40c0e230003c80050300d40c0b480c01510103a0750703917102c0c044000e480768500c044541e00805803a100d1194010604610a500948803542d28690301c40401094400031b5a010380560000c0105010381202c54006141c10300000d840420540001d50790a012210b00c0300070080001d6031080031700484419440c0c12600030000354002c02c43c040c2101000f400a114620000307007881b800f03021030a100002908100101103074075801501100500c1c2003d8455400010102c1e41d06140100c520307413404000c0146d58469400c0310b1080d020b40c0c20b01e01c40c6032031540070880f500d0251003080740b509040c41e02841c0741c1086060a5440686903450031910340c010341d03009044c110a0f141c10700c02d5850240c403030514940880e5003624144401d01011501c80780244144c01c00070034280c40074600450048958422030340e805109078210b4642c3e540358 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461247329 1250 461246079 461246081
    0x516120908031306060807180b030607080a150306060e061503090d050c0a020901180e0318010e0a0806040c0f09180201030c0504050a17070e070c02040507051c0b0f04 73
    0x120380148000001c1c00410300e001101040000c035240310320340010b400340e1140303042d07890800c540d440710003202c40116030f01e100030b4030364011940c015205034020000c03400c1605018205081c02880407003540e07a00c40c04a54101000c0c0d69200007540c011008120341522181190b400300d4048a196010380305060000509201c0582264031410341040a003810a00d0114101c84035800318143c141c00380724100c00301c009a079810300002d008207040e041e01c00e560507051003040140d80c0013015007102504141320107654000703100c02c1c076940c07441c091800c100c420343d1010006089402641003000c140c860341301004200b060b0703040b00c6019600f400c284184130b141d9075840343c01034454403401c001ca03d1805903032502c0194020303007082d0800030b0907040070b03401c007610782c0007007041d101c2541c0c0241c08208403113281d2010316109225282c0a0280300041c00000d1824607005801200b0b0158024010380e03403240050b440e0b521070410b48510381c4c211140d8140601d0521040c0015006890380580310340d20740300c500c2081c0e00d00303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461248579 1250 461247329 461247341
    0x10e0306040b07051606020a09090623040e03071e0b0f09030702011103040909030518030304061d010903062c0c1e030c030102070b040c0f030f12030f051612 69
    0x30020000b01d0603514194125540d400c0328450b100241c81c91182400014118005040c0c0000c4a54230451803034a0444030302c080e2841c1d41e12189510b100445c0600d804000000c100c444400182e4010801c2061580414518414903101800440000305011540d20142ea0300c41181d60043c0a4a04140c070386945d94a000074080c1c031081210b0344104402401035024000a103e4180910181d178107203992000341409541d41c600c400c50020783e002600032100d04460000b0b1807140000d900440c286810800041c0c07450707888103811000122091741c02910790307225415400c06142e102905000703a041c2800c0781c3e54a019418403440400e17038400f00c1e291401e000003c5110303800d07000502412015241c3e2000070003038000d91070701c83e415000d01c054400903914240001e0070315074030900c0e0040c03880c40e0508141c580c0c1d0080b40c100030013618085a00f000400e10b14078400135000d810402c5041100341c0703610203500904814400351409410700c803c200050015a01540d940c08194072440c80c005a1402c00400300c4030303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461249829 1250 461248579 461248583
    0x30609050c070609050a02100e120708210717070605070806130c0c050601081509030702030c040509150f01050301112502030312190606020a02010e010f120504050705010e030604 78
    0x1005019041c00b01d43d2540090a10740d01403400c0d2601d4949640103d1191100011600d020030300034031840609040040450102c10403a8000d4481c50b41000d54281c0c94a031180c02d03042c00402459030801c841c0e000c032800c6a2003241d0044402410040d00c03199109142c2118005441c0c1a141900040189000c1c004043c4a20030061040056a01007440300005264655261080050001103480014001c024181c06844100010101024080304c080301e250030080141e861504240100701c010380340062806500442100c000c00c40c0d07038569000c076141c410b070407030b004002103032400170310202642292105041e154160300070f1050540c40414060302d4400c450f449840301400f506071030000c0f010a040341700310f81e1000f01502d20741859450325070840329050320614144071311203a400c44404001d108440061996002034600c240c3c2580018050794101d400003410700404400c0403100740d10500d170044051030300c001c0800590410b4100340f55115143d01440380171078480c08080019280015156104079 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461251079 1250 461249829 461249851
    0x5150105030f1b07020406030b060a0f08060708041103030712020c0406030c031518050c030c1f0f05041e05150c030a030218040f09020108060a0b16050304090c020d03060905 76
    0x3440f21000019030306082c00d0b0b42c1404581c04c2c021030005030b4441c0120b4000f180910048007150400d07401b0444000340d00d0340301500078007564101308400035021440c0c40e40407000b82401d14043c0d940d070074200100c00309400140e07454000003850600300641c030f00f920310410945500301c0b501c09400400f400102d0740c0c20701000e010303c00328100401c005502000680303002c846150b030118030142000703401e003010484100c0444190300800b100d03007080e040c100080b04130308030105d0710300c2c6081e400110900303803070442403a0841c1000100c44a03d400580aa0200d40081095032016180365146000b04188000700e809407900c14002c0c41c4002240c8120079058070300740108040514580880480d0940080d88488005821840400c6054840782e803144280f02d5820311078800840d80d01400d100051034450000c140e54801c08102170148032401c55082035400c111003201000d070341c2d029079040a9146003e01e9004198040c00c0818400c0101d034003040142c4001c80d141c60034480d0b81d40707800c1100180c0d40300321a100051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461252329 1250 461251079 461251081
    0x120307091d091203011215180f3003090203330907031703100320011e02190f060509010c20030a050d022206020c01030b0916140a0305150105030f 64
    0x115a0b0035061401d00c026080b00000c1c129040403030b48c400c15403692019141241100551006d000da0703006810012030070714200c168072942d000046400714501c0802401019030b035410110854404000801182010321a0340402d0b0400c0801c1200060500060180302141c20020900f038610026519082e030340e2196030302e4003800f08103c1d84070700340e00028800404852444030002c041042da030011441032400c02006211800c1d940c00141501c40d5900361011500310b00d0f50880405980031680d04501d403021800c91042d6401824001190300d0303001e101030422403030102400302941c4154081114030b82d60340c4503644c1407103101d8940001031042c1107000d41c154104103d0208202e2103400104481403485500500b03103c0d520b005881e0402c8003948800e50360f0180c0340c06101c01074041180e11200c4d80240790910130364103071002194241c1e4001d42148404d6542e44081c2086600604045810b4120718480546a481e407840c02070141400b0b407013240c07000700c005040003442d520842c1140d1140900c40c0c040d03115 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461253579 1250 461252329 461252333
    0x19050c03061210020f04030c060e0d02120c03190b180607140f13030201020c12120304170307030b010e101d0109090204060503040b010503010509120307091d0912030112 74
    0x400b078a107051901801414540f44642207a80301400b103402410840c55111800d510345285c0c1002142c0010051000c03040d14400c081c0d503040d60341113007668161141c207454811029030918200c0e02450040d0301d4001c001503041c00d20716080780600388600511912201d41c0b645081d00ba20300020308110f240603040b86000804682c0102141c2c40c00c440410802480c1a0405050107240e40000c1400104003c2c01001041990307030412024910b0b840456000c000014807805581d40c0d8215413040717402628000c0005001d10090380700d920070641070040610f60303a00d4407a1004008ac461032842c0341c0400c1020014034601d0910303180915000e0990785070840214400c48444845013002d004043c100304401401140340a01400070b4801080e440e1245130710382c14030346001c58034030005070811800307685400c0c2040070a007000240c50f2204102216955683c0d10f8100040702c40d80c3c01c640250ba0407078200d00d44034104070054a010fa1080c042001904c0a030709100c080d00607944020712a800f0100b54410707140300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461254829 1250 461253579 461253589
    0x1909051902010c0c0308130b130302040902030309090f190b010801050f0d14030a0917120a14040b07050c010c02030c013203040210020706120e010b0a0e19050c0306 72
    0x194550050409401e1003c0e290381c0ca00744195076030030480301160041182d000080b034a21000c030190104803896808c043c003407a613802280b0540d102c042e10070360310303110160103540f001d00848404400c00380082c4880e2900315900424850199080b0701c640c40d41b07000e903035210341c4c0b10f200d481c4281605039900e81450346084d0070802044005042940e00400d03841c002c81c00a41098402140350245001441d20350380c0361407015100452a41c000c0c0c1c0d143c0c80001c481400d441c4041144000e000c801403585845505a0388102e070a244a40382c96446500c0000d00810200241405042c1c4240724004590142c00c21f0401141c0d01d420000c8001e402d070b80038003000a22076004801440804070340c1400c0746802e0381c094400c0d440b00310603c401040035240000520044d414140d840503401001030009020961800500410401101445450f841d030344201c040110502900b1403610100700800d4250040e4031040784d40031a10059400c000c4000198402d081c000c0311a010300e030700c2a42c8507202103040d03654640c01c0c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461256079 1250 461254829 461254873
    0xa030909050601110609010c030b0603060a09051b0406020a02040b041e020901210509070e0c0d050c07050d09140a03031b0507030c060915030b030d0e0103020c15190905 74
    0x1505000c00604c1070b200c000c208019007403241d00c0d100004039030283c0c038240140468112550f00c5006080802c00c1140d242c031015505402c0301d0010000040541d079100603c06507510210610702a40030000b000101540c1c0012040d590314022a0200a22003048040100311807640e407540c000e441d91000e007801f0500190f0301405070300f24103040620301d5218881a140030040005e00c0305128a80c1c45c400c0c01481181080b0542c06451007501041280c149056007074054091401d2495003240c4030000144004440c000340c440256000c0220350701d28980100150000301c5074003845a100d41c010b40d8012591401d204901d040b00c0c0c040d101c200491004464000000e10740c1602030380c182c070400c1c2d0700000140c1c0500301d42c1c00410302603451a01d8136007000182086040c0400429040500704948000c10707a42c0401ca003e84000300d41021f049400d80c14005030080d0280546c20b50103801154040c106440c00c2c6410140704062400d0100410341420000d41e08980c801c94002d8283d50162250280055018500c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461257329 1250 461256079 461256091
    0x70c0b04030e06160b0a0902010c1403090a180509070f03030315030506131407032001120608010b03100e03040b030c16231c03020a090b030a09140a03090905 69
    0x300c002c4841030020a8481d03014880d48120644603400308000d0100c00701a054001002c90014411b400054000815000c102500070300105071070480c00511000070421140090b401410081600e680c4245041164202e415040d852034280000650300c00f1010030000207071b800c19540401c01e00d0031034904500402c40980c03040c0c010403c0000110100383c040114a1280301e0802c0c4101114080d450310070300284000100c0e0842d64803211040c0f00080c900405a241120804070504030a62420012900c0079a40740340661030703500d00400461828010342102e40422000e17000c651750304074404200000c89280e80314002590300113100034007074004100011600401e11910050500250040c01c0ca00c0504070070044880390303a0b0034010700310706c451003c483c00340710200c03800340030000341603852500031080e41003100e0304047d4001442404540503412240241600410b180d13141d2030600080e100500c000ca105583d0342208046d480c42030800010b56282666046c2d69020040b4600310300b03800a0000030303001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461258579 1250 461257329 461257337
    0x50c1518040e030c060403120e1b0409201008011406090102031c0213090b0a06082d061203270f03010207060b0f010507020609060309070503060709080d08070c0b0403 73
    0x301c2c021031410405070030495000380c080c000e02e0425180180081a0f20101c0b801c0450070802800d0303c040c00420ac0c800c0d07440740888151041d11004000400505007242c0090004d411203a81c03800c0d41116500d101c50015003503803c42030840c01100c0642e0309120911540c0c105049081458240d418180054001010103004490400c0505a1410ba0904070b1002d0007000e19404105500d401c14070100020080c031080400b00304404800000c0303070f690081800707588240540800800d030b060001103c4c030208005101c0703070340e0a14010602e64519114040c0c60072442004c103241070540c401c0020007201c83e80d074500d00c010064070b400703584900400d6241c00d41c41c50707000c94001c400030844c0d01d0030300061001a100360800501695072504021030a403410b440c00d41000000e220580040c1c40d96000c80312a05000c5902d19140d599100d0b01c50704d00030742c1c0e070012078050240405011002e504910144240c803040801d48807111079025044648041c00c4030100d00040e02e141c0030740040703080524003a411a01a00e4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461259829 1250 461258579 461258591
    0xc020a1202060c0a210e0f090411060f190f0f080415020a0203030603010608010c0c110d06230901051b03070e04061203031a40020304050c151804 64
    0x5903142c14500500001d07641e5000541d148850f030007407080b07140380d03003249414080110300300400030541980d40c0300b120501a0900f0348c085420701650840700310450000030b00b080d03540d0380d0001007044503401000116107030607034940e0700419050082c03407415a50b805603560b8141003000c8540132a0508009001912252605400062441780034001032440103c6a00156070380e042c03000a0500b12841d503484919282d1610031100b1186602035010000f441d04007006200c0103400f54001412a0300014008148601d407105a2000c00345005a07a030180004650b440b02d16650f400515007611011130b601d03c101c190740c5007212150038508001e1600b20407580b900700252221503002c02d00f103e0031034004142c940045441941056032502501010384035402e00030300415460400301f100c101000c0300d400ca51941c50701c800c00e28241b0f802d12080740342901180301030010740c1b0440610b00960044c1d400303550718012551410210700b04074016107540d64042c100d440c9842c200680040e62007262440e01d6038000e8440e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461261079 1250 461259829 461259847
    0x705030c160c03031115070c02180f010f0e010806040204020c01090606081024030f05030c01020a030504060c0503091f15080706030b0a1a09040204170105010303020d0c020a120206 79
    0x10070200644591400d000c058114100500b040700c801d614004140d02c20751000401e2040003080c242c000c4280d042400f120318046c40081c10300145402401c0030700244074104490f00e401034100c1c504079880e2018035544c0d1a200d03050300c28007140900914400790700c2a00800e006003095401844a0f20071500009454041035075030105885066000c8403460f4404200c809843e6110f1290282080590484600f60a07a4004190241059200250010911070b0b40b07030741440001e2045800004402000319030350b42d01444c014000384029903040e502c0342c1c40c05406103030040c0141c0841c2c0c020100031004008498941e0141c132542044040450f6416890350800b0f40460b10509080000d0149000680245400e00d0300082c01c540d81a00c40622030307144050300304410b90041d11194040b001c0304078100e40d11020600420b01900c40d0354050200c800400000c0321150300c040d81302c50305880c800e500740c8406000007039046520580e08040a50721a6064004000801c28035440b0103207144068401800e00e20f210b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461262329 1250 461261079 461261107
    0x20a0e0a0b130e15180616020c01031e0f1e0e060604110a031104050d05010b090108010b1c05011107080d11072d05010c02010614090c030705030c 64
    0x15150489603944940302a201e074a8034a2803405044070503041006003090703420030f150b81ca40c2004000c0042d0003009000ca5200c15016000300c241084241c1215803038103000115400c030fa0003601c0c400006005450380c42141c0d40c824001c20a8241403d5099407810424441c20030040c4000301298640680d01c50f00010519410080544900c0e2010b00021f000704901c03d03d1030809400802c441e00c01e92400010004d80544013054500e4086c152500048508100759245007503c50760300100d41c040f00d946001001c0100c1500190400a000d4a51542590360b510049003658060144283d02403812544c50402221209030002144c0c0520004546001d1503004100706601001c01500c58160016112401590314052484070024007800301d85806101d840300305c80b1141406d61942c94210601080902400740341301d000030203400c50020804025039143c082d0080c28544101200146410303408800d6103800d8007940d116030803448c9003900d50343d51801c08440950005200324414101401012200100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461263579 1250 461262329 461262331
    0x20d120203180610032108070807050d05010e07020d030c09050d020609040903050316020f0607030f14070f020f0a080a080403120609050a0b0618040e0f0a0b0a0b0315070c020a0e 78
    0x500300c01c004c802411410b011406600300105c070b504228a0f8241c203d145584040039079809104d1f442d01c04156201c02004560030701c80d400104080506007000070804422130401c1324020355180e000c6444003c68154140d003500c460b4130b1001c02003105a141040641028440d06d0000d901c004c251520b401c0ca07200000d01200ca0b008400e1340000c50200030450109110049082120070600003006d20400c08000160b544000401c0441019295038111141c600c0e45c0d00a005112103150b4919401c1c43c0c10700f0003d0041a003008114018801c0b0085610301c0c81002c164584070390b4008100340c0c5403030b1250b0000d035440640a071045041000000e242c00d0035050520451025210402d800305840c2003ea011f1402c0c5c0f0300c10114a4070079003007000009042d0a80002e000c00b956001d89010440e41941c0d61014105882040318646c03a0080944010810280440540c072509035850208502010541450350b80d02c400804009106160800b0590260144d80030b840058030040c110b14019844d00410842150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461264829 1250 461263579 461263591
    0x507080c01060815040b1311090906060109060c080910140304050703110a14040b0301023007080f0406110d0c030f11210a020d0204170706020d1202031806 68
    0x503442c01c06000004003801800d51111541686210505241d250710b5045500941600500700401c41d410b01000b0382da01208111244c02030040c00075192100b100346e21440101c1b0050f0000d01440004103c0e94040d69182c407202c0c2d0003003d001d082942e01403d12218110941400301801007900b074010090b140c0e14025445548506e028164180c91490041d1034004201200352144d0000bc8091241c00c0492050401021088401203802e40d0400c0120780203100f000d441d0108101c9072044007020b000300122165041d400c441c8469041e55640008aa80003000d41d00030000c401c000340800d010440d41e403c2000ca060101c1c40446c6400c1c05a08503074112241e5881c80c001083d1104208030540002d0301ca1031464015158042c0d10302a110260204582440c1c001c5115a030300881c08039080c61419819512400c140c25411941c0b04d8540d0780840c501e0115100080d11440f07505000700705248049401c0d1604411611003c0c04041e0941c0100042d420051843d00304200c43c5422020031002000441e000d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461266079 1250 461264829 461264831
    0x50a0609050d02120922060302090c070b0a0605090708220f0b07020a17070602090a1403070603110702090403020c04060e070f022b140708030a0c1b0b070507080c01 72
    0x84400a82800001203210403514004c4c04a148a03486d245405555540b0f81015900b40101040d0380030010415a040650890614010050038100900003484224012000c0000710f94a20b60400140c4645000300d0307802121080102e61214081c602c52174019480c031122140032945181203031540c6440030829170380c9103c00c40700c4400348000c2020240c0c100d00644042c0c402c85460744c850072107d145440309041301d5000040c0240512000340d06a4060031801440410f4a81d594006461002076850825200b0f000d65000051520700a100d22241e04184003000342c2003c41d40e40030040300007030003881030b0194000c51003500000d0b070341d51044802a11810f01543c25a080040005008000c0c0640880641d4003100c10304002e42d10401c100481403a1011b82c1680041601d0412550222000d4918410402c042040303c00c101d111406144500e02100040010412203101100c130400c0708074110200220607201500810601c1e480c440d841003060600c3c0f49010711507a10802160300829114001da = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461267329 1250 461266079 461266093
    0x618060c050a090e2e0f180b01020d080412050405041d1209030a0b0702030f0a0e090c0723010b10090305071a03010b03061c0f060e030408030a0c050a060905 69
    0xb060b000141400a0b0600c18134103004c1d0b151600c01058421444c131041100034241041081e00143d0b14522140a48176a9a00c5450f00303548228182401d020021350111650a02560101c1c0d54030009020a40c00c0850350740c0d041c1a107954a4031340e010801e4000342410030508002c0841c490b1a41c1c054043c0c41240b1252800300c081c1d1204c030321428034000a0910389510401c1101680a5400190f02c000b12500081034080b00d403a03500302641f540c0708080d01c1c00a01c2c0400701d82c11148a42000040c641c000c070617510008542d03aa464086061b108901d001021001c441404212021120b40c256520390701c0e10000040366044407001600c00750105801100182c04405d0038400c104c02401013000030410003042c0750045140c0c1990036018013050240c1c03050042c003c80000c0c103039a5110b50000d490420300401c01001d032032034100413640d804000000ea610505002a03c407054400000700c4013203d0703641000c0c600b040f100400485107a0701c1080251902d03c00c401103c004100350703108590348548544024850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461268579 1250 461267329 461267347
    0x501141e03120a05030f0108060106020a2a060c0c1203201e1b040e0a0b1308030408181f0c060204050306070201020c0d0201053c0930070618060c05 65
    0x1406c4058104c090345030410801000459000128a220994004030f202188030020300c48415800345100e007803541c00e4034228000f580d0341d04000d643e1000ba00880c0207044d1070752a05a204140c02c003140001b000105100101810a842c080d442c034110008141070b1404030030b1241800305041c03140301c221350494020724000413008030362206248640f135058a05100705130130801919140c580d0036201600800d601d17070005442a5040e000092110382c010103003501d0f0f04107403c20b08190707040083c00c5014042e05001107442403401d510000d00c203100ca20640b05000d0f90801080301d0300c0c03000450483c1c03526000e12003c58103a034240302d0070744101a07540c001a00d078161340c428146041c48118001040d6450035003840f50303142e04564500051104200c11450301e03c01d6110300200e00786031071a00b000c407440d500705118941c2008281c41800801d100303031615454950038042110340f010002e0b128421a0200200c0002a81036007000f048103400300414003560210b91540b0050350490303052580059000a81c24032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461269829 1250 461268579 461268601
    0xa0c031d0c0a0801090803280c0201021e0304051b03030d06090e0606180114011b030804020a08072709021c020910080a0f05100606050903010501141e03120a0503 71
    0x620f82440288000c98041d02e8001c0580300242540d1603000d440d9600c80e044011081c0b00401103000b59404000180c00040003c1c000e401403940f80161001201030802c210100c101a04c0c000c5800c1405000241706074440e0b80030341041d16071003d41500051104144a040511a082c000e0402030300129040c280c04910505000340103000d10300c0361469465050b41c4848050003907055641031480200c0f003602010050b03a0740e52007003000b84905915240f90800301a031106100b805030b8400d440b9200b2140d1181505a1100c0785801043d030010f5018050490304c88144c2d4001d80c0d000e40a200000d458501c036008184088060825043e08024000014045003842c18800ba1b010700d90442b40701a081c201500d203501d6003190003001c0e0440c0700184003c1e003030007803d200b072a001c0da810f0b038420030055030395500c050402d8214100c49072180d4030308000004c00202e84469084c00c0304001b4165162040d00580721030040e210541c11980511032801c48005404104000303141c400c11549440ba108c2c94030545900f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461271079 1250 461269829 461269849
    0x15070203030118050a090b180f011e0908040f1706090c0108070c2a050f1207180204091503061a0312090409050601120302060a0b01080a0c031d0c 64
    0x4540c400c0004204a00031491940c0710300e10444004209a02c55040c01d401074481c408000e49500c034040180484a041c000000384903c00c1001581c205100c1c611000d030880d64040c2c4981640000400b20507880800c0358008142c1a20809109041c5625001c1c42d141341451600842440e0795554001e41c0c07a201d0411030154081c050000410150201c500024000701e4054440c100340203010800304200595403500b0440c0e64403520301a000090720580304120702440303209007401804070017a40111030418040381100e20500d0001046c84904d005043d54040c40f640c1400f5500b69824807000c21307441c0c064055202d07041d5282c058561810305504002c0308a48030403420451140107102e20100a44010401203085e00040d40d41c00e854003107240114025012044000305030b402808004a0303103810410842c0c00d514007030f03421a591541e400c5200c2c0d04642021902c45e0200b0380d441c0006044c049150058034481c02c8510b00425403580f0a03042e10a602c012009084070760b04141944031090900314400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461272329 1250 461271079 461271091
    0x906010806011212120c0e0f0402030c090d0311030c0610080d0807080a0f242309152e0905010e040b0103020c07270506090f1005030f15 60
    0x608055490071140f003400030700d07a03c3c0080405081c1041c40610310b014941003101680c0b0a03005020b031402c102c4009140c2d19810080c50f10901c210521500c0700e06052080d20300c80c4084600e15490041343c9401c0010500c0c000d4011000c1141001281c0070142050025005a0000e4001817484d8104040c80619070442600800340d95804001c01c0c0c0d01041e4080a456044461800c0030080b58451070900b0003e0500c000121060320308201c002041041030500202034083c003800580b8000da110128201c3ea0141c80ca1480103003001a0311001d8940303072840b12503401c084602800709021404402103608202d0707075a00d80d007030307420782c103c10f1042d01d003000c0700d0701640c82d04a14000504908140c006040600c045140e54003840c0d40740354404d0240d00a41c116010030306110100c0350000d82d02d0b9407a07002611108407507050380b034004080e00c540c24024010782d40140703c002e000007004c7d620090000d100a5009083d41036041408400044544040c060701c010b9490400c05444441e1180245541c40c903405090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461273579 1250 461272329 461272333
    0x200115121e0201121a060f1806210606130801020901030e030a021908040f0e1918030503061906020a030206010e0c070b0a110a21050c0f0f070f080309060108 69
    0x71000503a4405081c4213160355089001170b0080030103000c00baa105003036003c2600f007080040c00c0c00852425202500180e0f00c0761116542c8a10603e0034404140955140d0542589140b04903ca000346001c040c954410001b909a50809d200f46004042e511101da02011f07582e5030000341042156454040c440758800840c006601d410040381000b0b41e01d003403030001c02e000b481c9962000c1c4100a000700131200202001002d85140b01e440b181e54155032a011340d1032190480401910518440f0b003405249600380c100c101d03c007074500030754400341c400764001840d207035001071900d0b445003100c2464200c44014000a038000c150810a40c0b80103460701c03030180c0040040d0200300c03007003002d2100c400c030071505040e60025200d041522078403028009007004100d00c1044030400301d0580a000d501000034100c10b804c03d1000040e440d51301011004542e025500ca81c00c0542c108103204031400e00c2c900520881c038604800c41c0c506450b1f511643c00308880c02d40d080b14410350000900400c0d44e41007040030301510715440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461274829 1250 461273579 461273633
    0x70b0712230f070306150e03030702040504050c01080117030f070305120103081e0f03040f0f0f05060402011214060f1513080c1e040b1f0c031e20011512 67
    0x5a04441e01d86c042d1011810440c0321041111907032000d0041d44c8041d03034060000e0140303041504e0026240c1281405050000f21603800004a10848802402c201114040070310702d01043c0c548400c8056204240580c10b001d010000c0c40302c402c0d502624240294020060300c0d8582c40c11040c00e198141034680d481075404018808010010070b29401c807030300320b03500c000480112402403424408400013118003610031185924920140100414818802c42c401d82e01e032086000b2650a0714100d50700074400484202140c00083e0080c200a103110301482d00052040e6081540311f81c507014185d0017142d141ca00c0d218604810400d000c000c2000c2000280103c801c07007102824030f030b8220510040030035158032450f1900c032810150380310500b80514902cbc105c0003008144411103c0a00080050a000c50015261000d080072174007041e80d40c81456901a954540c0030f007008652250b911000d5401140c0c255a075030b20843c0c015203028a80b100802c0c12001c09828503005091a9000441d501c10003030043d45001c5c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461276079 1250 461274829 461274839
    0x1110a060e061e0a0203041110090602120408061f080316020a08060601050f03130b070c1101030c1b1719080108030f070803090c1302041406070b0712230f070306 71
    0x10f0401c0b68000707488034005880f0b546030704191180e0102d4140300750300840d80703030141040c855015402d20141c5e0041d1702114039440264030801c50764402e40c490312000e074106e000401d00004148c01003e21501e030900c840b0b0b03440c40d2201e2901d070459100788003051020b9030802040c030071030038003640303034001803e60720042c1c0003502c0c3c514000790617882031680d40c41c50b206d40000040c49100c0c0e42c50020125580112007103405280c1144003070304040042030240d614240c10f4400000c20741c800d02654052100540e2204044510488a10b80900c4400d0085a1010500c1d40488482c10a440035000c40788105425416039030036141c1c00f07010a40306801c04109500104070400b542d04410040341c4030254802c1c0c6407503803965007000260074400c1c1d00340740300e40c400f8403482c03507204a081c0e40c1c0240c8181c411121101003c0e501183c00c000240c07141c100000c20079564840020541c0380105100f4055040007400410320702c4058424100007414101d66a01e410001c0041c45014070305881d039507500c52603605040004a04117 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461277329 1250 461276079 461276131
    0x10031122240323210a0320041a07050a051c050c030301060507050c1915030608060606160b0a0615020a0f02060c1e0105090c100507060b01110a060e06 66
    0x4038103c0404481140070091500d00d0401c400d1801c541001081807080e1240e5141c400c00d0b0f80005441e80000382458000b1003203180851070900281701c100c0700d1134075040c0340407041007603014401c100395062141802a10003261007801419101446030001d0010b0700180c041208280b94001c1111040010502400b549840000101c906644244c00c2031920b4594615000303180c010111820798004d502e403503084044d100310501c1c940c11f503a281800651100010340d070490484400d40b242480d40e501c0000401c441e420518020040045c070600c1c0c00a244495444890b200f45098802000c40c0760303508410803c0c0000350300f08803040d000920282c16a46415221840e00c48040384029214080004a019010100300300c102d401c0ca51080004820400c4022054020002240c2c464943d00034422100240c0c039202c1c2071542c0901254070765500b081c206890350340050401c5070617541440444180349891601c1003082c1d031101803250310003040800400406a040a07000740102d500e1a00e00142515160f01e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461278579 1250 461277329 461277353
    0x80d18050a0813090c0206090f011a04110c0d080f07080114040c020c031b24030a020a05091e0111190b2a0a08070503100311222403 58
    0x742029840d90714400307007140071201c0f42c0e108400c414503252210b28000c0d00401d034180b18403c98400e80c0c850b0390305a00c0090030f80303d50100c0b80c9440d02c2500081002c0340707410f0380030302d00945407441498104448030f60f003079180404034003070000810302502c100310844005442055001d4444e10342207291354075001900c0c5083da54050702901c540c2e02d5181c8904400d202300304000390000000c0445404601c0d03c040d04520300054603035240a6540c21024480c4451054101d034401c020751125180f46546112039000250884001501044010400310050340d80742c00c00b8000000c130b0452071a41d0800c40c000054032501c400e240c04000c642200c0b00200300c0f41a1b840c80442d034650040c0d0511142c0da1040003030034440030400704c0880b1b0481d01c181c8182d01002c0030b5000d051038030020f440d45112034807245000d59140c00b00b1201100c900c000090180b0000e1907400700d1041918002e840d841c140c1d0400a203420688980c62500070110b07644a684094120fa094406c046038610700100c41e4405056440302110101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461279829 1250 461278579 461278583
    0xc0a05010e061807030809090402042409060b13030f0c080d03060801050703090203030a0f030912020604050f0606060717130b0d0b12190305040b03040312050703020c1c09030b04080d18050a 83
    0x2356080020b0b056482d10f40106400c2e001d1840d1007900c1c800c280c4502000d101d601c2c01400c000e01e19042c400304030300d400501156181101070245480391440c540d1901e440007903036030741165007112038640020401800c120240040940da10007007805403c1402d45400c68030010850001c242c01d1a14120243c1c0780402214181d600c18500b400700c034080c0c0101a0098042590000c140c00b024032481c611541c0e0104000d0300030391081c403e4665520304a00920303507404083d03039001d80c4181d04000060001d008109240d003420b0a603521942400041c21141d00e18007070940c0410b900d60310016801c40040c0c99803280e11203403982200e44a50416036425043c0e41d50046192081c580901c44e040740041c18080e00943d4010b0001e0b8400561360314180c5001001390380c0c0030320020042c6040102042da0680170f070095a803c0e9000c4402042d80410042c25450020b42002100c010303c444c0c0329000c404500c0c611195481180140003c81d90f58200d560000b084441c00340181ca11800b0700a6034000183c40031a492920035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 461281079 1250 461279829 461279839
    0x10030b0f01110f0303090c01020c01111c030b0907090905090118080a021c090302090f01060c170d0c030203190509070314100504050a151b050c0a05010e061807030809 73
    0x1560b4a561030410044040c00c194400401007140d68100010100843e070001e9080e10020344202c1e0065691900160650380719402c03003d982c00d440503800c1d6184c0b00040e0300d4503021800c0070130a000300c1c40d617510a480400020f01502014081101e050090540203100c00008001c40b6a445203144400c41c0c40510090101800141024680b882089110825210b0b44070101803042c001802805251541c44100e002e0110f0324001742510146001d4030307048440d19210401d000e000c070b540e02102034820100401c004441449001e0780a51584200650514a5100140c0e00e00309081d0000b901d1304105011503e070342c00d0070100000e0f8000403032442d0840b903206900708161000303080d145003442c10b40401c64014901c0c1100300000d01c140001c6070295540200f200000030581419241d0690390461182c0c80030340c0c1c05130302c0018403502c14001041c4400c0c80d80c082d03540740d0005559040c00c0d40d035a608402e031154804401d0010b001c8880401d414003178184030080c13201d54507540d242e200701c0c01106016880b907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 461282329 1250 461281079 461281097
    0x10020702060708040f09050f06010c030c0c03140f070801020f0a080910050a050a0e0a0c12030e03060106090509010b09090c0906120103051c020a0b0105270703090210030b0f01 77
    0x10344446041e0b442c032035800029151201d469544000500c1c84900c5156820b50900c03001c07842039a040da10460180106030340e5034984840c2034a00381c1d914003000c0340c2100c00c0090494004041460b5150058520504a024100d00c03101800e00c180341000d66006110310f41d2040102d2000e080301d1004803a4465485d0030b2036401d03583d9807401c0606041c500c01c1b031540800e0500c01008200240c03035001d98421001d6600801c4003500c5c0d0010320b5500e802e41c1c0c00040844a0b40352051040e40000702910640364881d1510303001148003203002c6802c101c1e080e8810070210b032580c1d00c103110602c0c002c5401400f512211034401d003030110140004100c0701c40508900400080040c0940558441c001180c8070084151107030142d55a4034a0819134070342c07401c1d0100044e000c100e810b0003140e610100781c8211582e0408180e04461b4280000c0240b0030b4410b50080441d406103685103045201d91207000303803003000c01c2d4400003280f84060040c00207403101204504201403501d120151180e9502000d814401d10a20349a462 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 461283579 1250 461282329 461282333
    0x30c06040603380a060804020a03081308011112060111060a020a0c021905040c0c0c18090b01060806091e0a1d01020c1e0102040302220b0d080c0706050903100207 71
    0x40f84112100a03149041c0080842c03d2900300384080d07208190303041e0343e00000142c4d221812501c5007000e480095015040d850108003248440d4050f104940c1d41e1001c0741b00d11359490000328210348098908010a0b039008c14101800c00d00e00356004da1040f0207081c081c041d9010004029140c02c130040c2070580c0c2507404100180e5084c800c1004000056000d0100c54a001040111210241285c0b0030180700b00c2c203118807a0007051045000c03940656211045404180c2040c101c903034a0002101c402040a5880e1b074541c022909000c0c070300340200026107a04009041ca003090000c000b1000307101042d01c100e09512002c025401070002c41d400483c6001c0001c0d6000038040c3c002c0d00784c000e00c0342c20385103600210764035204110120700552043e0240c03010031001035601154609034051131101a5001d01803c6400c920610700040c0000d00c0d82100e000091019901000603080316003218041c1c6d10188085200b04000e08200301c141c0143c2500d081042c240400d40001030b0b50f0f054501400c0036056000f081c9541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 461284829 1250 461283579 461283611
    0x2030319090e0c030a06080106050609130b041e05070516030806030f01110d050108010603030e130204090c0e0f01180b0906120906160c0b01050103020903100c02010f0b030c06040603 80
    0xc00b4000000014840d8200410704207260780090740e51031030f014544640003448840510449c42114805010b09042041c00e204020103000d082c0f0000010589852092903e81d230f0700d1082c0c514a90304103000703401002d541c0c00c5085c1251350003050380301801800c0040c241111890000542010761600d8080b5003551084042802c04001c00c109455a6003844002085196050702403e0007142e200300070400303681d80355100ca007a0b0b801440064003040d1a61a80a51030074074002d528000c8200c143d02601c3c1036507400d2004200e40e010650100000c074242072040c0e00385881500c01103c00401d117040240b490311680c4800c0c0c2d00304a4031558680701d03000200842240c480b1002d0314200c03809a548181980b4010101e1905c13810103c2e000c0f4100309808050104450156182054480d00601c041225a08000040d0b000394058a2030550506c41c0c1640d0707082c902c00c9801200c010107550360020845600c081c2160b030548813526015803182e0884000745038a40c0302c40c410b980c100c9215240c0450400c204e031413194 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 461286079 1250 461284829 461284847
    0x2907090b1b150a151a0c0a140d030501050d0c050f0409150c080105060309030d0f0b040c0c02090108030f091005190c2306070c060216150c05030402030319 68
    0x1900e60184820540d01030b02031007a110b01c601504807061040c0001000b124514003c1400780c0800340754000c031200c2640d04840301a05280a5201c110f41810403151a80c0783e6600482d044250564482601519034030390501800d801410150f034000c42e5044140d40f2080d03419802d00410740120a19420300f41d240c0d0381d54000300d05c1c0d40d8200a1018400c660340e01100084c0104c84280c601044801c800040c0070f050141c116849031251102441c201040415550081c08003d4115031000380c0318a2404060f0343d803446100402501e80e1101d0884800d284180040004d050f0b0080b0200c0d001071202100201380c1004980203103208844080302d40c54003510039510f0340903454210741002c801c8003151120940141825401034002c0c020040c00350a0ba83c7d510040c48840300b0800407903041840441c40d8030f0f0003609000f0b007443c1703e0708015040c01c0c5220901d520341c886038030050b01c0d1586d580c0c8082e10041041c0c41148024650b030b185c890b2561603d900800d54034840e16900e8540755100307100b41c84500d80318130204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 461287329 1250 461286079 461286127
    0x8031c0609020c03030109241401090312050306090105031b04020304020d170c0c04020702011b021f0509270103080d1103070507050d08220305162907090b 68
    0x2c6449001c02c0362425582d400034001c0901c101c1c64000450341c01540e40c15000502101e1890010810342041c0508000340040c1c0f0700c6505002d50000302100144000d1200031107000c950780c0d40b81c0c4a00d041c004009003c1410390215000750048980301c2816814a460440d55903410b6401591360b413039030b2000c200322058110001c2c0c85000c018035200103030b114a5009251301e03001c0750100c40c82d4a6003601044100c0c81540c030004c0c0408d025100d508400405041540307103150000b80b002c00c00c8030328402407480c41032030a0310272000120001062491860880c40d03032407841b4180080018041441541281010010700000d070441d00c02080079201e40d0903581010810f00c240303200498803404c002e2005001508600c0d0120b606000e00288411003521465506d17201300742d400b241d805c2c42150206001032940140e00c06801300101009040c0c811101440c52500301031145101c08589e100140c20305441e9004460481d004401030780920030429400840082691030407000c2654a0001d0342116110301011101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 461288579 1250 461287329 461287331
    0x303130909170c0303010e040f02030105072007030c0603020912070603060512030304120e030307020d0803041b06231c0506030d03062d170304060e0a08031c0609 71
    0x824880c9a5400c00340c1581c2c4a40031a548046201c18001103d000e8403801d45059070080c00100218542d9520b02900940545000280401c583d0003007030075550212038090100c0c03155500144281c482000140001b04a0009040c0b00c0d41141e4941c80500740074401c04d010184c0200e018406556140400d09421094004460440782d0700c080142c090718152150324400c21400c10200c19003500401200e100d41d6000210b0b501164070b036442610705054255483c2c0c0c00d44030601008005880d5108016007440c02148e40075142e16241c43c00400076021501c00b8131103801182c40c2040150781000c11f5117185800201000051083d00011006c2805009000c0544a06613044501e030101c00b0f600160250303c06a00f50340703000380d5022094094600314450001038180182110b004d41c0201c080b0260001c64829010000964426820054600900d0441155000001c0400070507030040040c2c009200165000d50489143c2910951680141c182180c24268890703030740306a44a80d030b07011402500d50b0241c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 461289829 1250 461288579 461288617
    0x5060f071b1101031a0612040813080304080c0429150315012706030e030f0301080615030111040608040611210901181e0204110702040b010e0108150303 67
    0x501c4414082c2140300140402e2410454500c0c17425001c8441403244e502074101c030310706140c80905480c065030090040d1691101807141c1d045c40720104038414005d040c003200441c2c69908000540c1d04041d083c03004188241e01d011100613590701030f11302e0200d074002000f04c24405ca03008400414400c88001215150b1400d000040011030200024029145082030740c0f03031214502c10750101c4282c1d101e17103002011482002c3c4020800c05220782c2022071070800300d105580c04c0000d810070369800f9410a03089800c80340c020000b045410056820303204c0107264201c00030b20020588401c0c0405911850280d501013010a0000030280300039504082440d0003d40f407020365620103183d82c01d45002210b41400c038424892400b05e544104140510605d800c040b04400142c03441c1a40c2d00e50074800b11b000c0d0701032102508140c1e680942c0d228820030b884a4001c500c903030381d1003e051040100b1943c4690000d4180320142207403041a0740e2269050f81d00a520308900c0031100403680020303142d801400c111259205100b8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 461291079 1250 461289829 461289833
    0xe04260918090c0d0302060123150324010504151b03021e06220203100c180501030903020604120e0a03080c060906160c0c03061a03100905060f071b 65
    0x101d2148110501419908486250010403404030000c48003e80164000740052124030301189520032540400040070700c24940280108102210910b0408040003000c0200240144030440e0208001007485060720a100310b103002800701d0146000c0c004045c0400300c004800d40b0f009030b240154422851440b035503000781d2460000d58402e0450300301d0210100d031075003c0001807400102c1600aa192000c904d0380c003150f440540c1c01e08450300d00180da16204514010155a060f48100b41c1290b240740c4e03d0386040200b83d0b05503900c00c400c0c3d41c001ca04152900c0c00541c0801c0d400708410350017640c4001700c540c1c0c110500c4001c650580c103030203644d1b500c800c81000000c00c2169800060102041c0041500c1003079558148460701c0d09000c031030820515031700400c5120720601c42c8003050f90a5110b8002c24440a499032600c508035451211801ca4000c901c1581c03c1940c41c041041000202c0c524800780100440c550380c40d03446190213020040040804404110079501075100c8009800c0c0d8a036241c0307082c120074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 461292329 1250 461291079 461291119
    0x504080f010f0c05090a1509030803070c02040b0121050c091c0b060d0c090e15040f02041401050114030613050c0307090b09100e0a0b04080706020105010e042609 71
    0x114500c0188500d04208841110f001c0d40c282d03084020010700006d2020301e0700c140c0c070040354115811541000b101074804000600003001450251146031303540b071100102c81c81444201c800907510203051280403c01ca03d10310700780c1d4480310040800001c01050700d4613452800781c0d941c05884010365008200c00140501114113855142c00c00d802520702ca132454607803c081c4070511040c2c40d006802d00050714400d022413a400d400254102e0080c0c800c40d41c483d8258592009a203030b0948080314084420410402989810300910b0154041001c03800e1a551400c40080e006902a82c040c412518001c070004490b60345801888020803d4440c0910583c50078500344d400a43c401c48010000c1a01460082410040c500c00e889454002400038540e000c9040b4007a50020360302d00c00c9950100310204086029201080640020103102006010301400d1080c0607095402c140c009503408540c41e410840030403094a074049102d18181e120700300b0014400c82840b80d51054581300da4102d001d42845070042c10700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 461293579 1250 461292329 461292341
    0x512120f0a1416081305090115120b01020c01030c0c050d2c0f0409060e100f1406030717030f160b06010c0506152701050907091a0304030504080f01 65
    0xc1e0388103000b80403503141503003480c091291050351140e034075421007001400400c01068446004640405d400b6070f104002100300d1400d802a41000d414110543c65068001c041417026410f40e09040c00050b082000003991940d000c00340c9410503841c1d1400c01d842e203019540d80b010f00380d0080c0075502c80000b0788a0140110808581c0004d107510006949a10380f40d4841c209003040000510303c000c0604c0420801000d014941000c0d558030350f40d041c14840d1140e04100042180c0105440424980100e41d8003004442e80406c04404145034413040148540d40030544500b698003001c0c00789621907420a02e945140250069441b65100c0090b036002040c640c00e4003090154412090b4003221340d680c000444003e0f41602008080d60300100114601e2003242500c06001c3d80050309107103038103075900d99211101032130800000c801d01c002170040c40207040c507070300c081e40c410030034100b01884910304440c6030140740140c80000c81c83c0c42c2c0440418109481081280d0040550500300d95403c1452803180c0e0003000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 461294829 1250 461293579 461293597
    0x621060d0c15110a03020a0305090f090702060406050603010b09010b0d0605060f07050c0f0105120601050f0d05090d080112060c2016090b0f120c100f08011e0512120f 73
    0x152a03030503089803030300013200305005074154041c02c1d8982d0070380d50545042d0000c9629030f502a2510034680e85540303880c020341c0c2c466041a402030200d41464107190b011560302820990103641014805c07469501c400c0c841c1030464080c8241142c0d502101800c920041505130041a03100c0f8001401510a81c030090240c8001030196095840700040e000411168080301c16126011690604c01038802d05070b5041c2251380840117042851400c45040c80160155200c0884040340300d6541007400100c2d5002c01180465060f1800d00c2540b030350400c400104001c0040c0401442640c4480c54035521034442c0c00c010500310b456460140407144007121b1161074840e1b0694041c0c684205500000b5401458050108109009401100d0004080040c0600c4200d0400049404d100b2424082000e44403001c0d40505222540d89490340e1400d080c000600c50b02040c3d12181109507100e8442c21018030700ca80034401c070780040302c0e40303294a60752100300c500b0080c43c1a0a01c17000c40340070680386410841d140041090407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 461296079 1250 461294829 461294837
    0x140304030b090607080a060e011824030c05030705060714070b070b0411040b010504060e1c0c08060c070507122f0a050d05060a02030403051306030b0f0621060d0c15 72
    0x9951046d04108459075489002c14a106aa00420800c4446000000101e640c0311011801c030008942a03d92500b204d0042e880e20a0398030420818000300e00f28100107003408801138451903107404002040c038040e59401070990070b20f015491240281c100101c40c01032005900450301c416103420801e500c1242200c00b0343c0c243c414208890030a1510f0b01c103034900301030161035242c106410500c0c2125000114421150880e28222800d5166011a0420410a031094411405550034410001e061440c050808001600c062000000051020443c1810b80320600000c090100b401d041840721107014402e4140082c81c030f00c4a00c00c041e8011000703180e589070709540880d880e40d603502c180504003403036400c01342080c0c1045020600f02d107041d40080d0381003400782c0703051401c1402102c2e0214901e8483c1c1e20440c08070303a4800d842c030800d0405015407482100102c541d2820401b80d100544040b011140a981d0050740450004000340c1e02d00801c9404c40745c1102d01e002410351a030b11030b51000259801c07040085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 461297329 1250 461296079 461296081
    0x60603030e102f011d1623040504060209130f0c090305060a020f0f040605030619050303070605060102030d0207050c1201060b1608070605092406060403140304030b09060708 76
    0x107000d06244032049403a49401405218a8501c01d05a54101c080c84000d1355284e2160070348800c4410540d00d059070528014108075400201d000b10f00d0115030b44560402d410921440d01601000551007524110603107020460f03954501e00380c80248a18048a6030051051021850503a010b500c105884168103004005070201c8090a41d800c1400748401842a803004002581c0c202140e005010b200c2560b40c0d10070b0800043e42006400d03504240c02c4000004d50200c200b10071460022440d1050342e01c10040740d0391160620000c286c40c1d2090341c201408241d01d5401050450744200300300c4218683c4180d00310340f61a0311f4940140c803280072144262040c034007081402003610061207040c003200c0400785400c1c0342c560312032001400315a03d4681618900028440300f40841c55a008a510540064002c1d0159680e103c0c01608076448a4080038000500301081151f03d44554003200d0070b5079040590b4031b44e0180407860a03031a504c40d5401c01003030009440e003881000701001504900030001901c0d95011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 461298579 1250 461297329 461297359
    0x50108030f070213110703020312070804030c021c0c080f0105150907140f03100e0a06060503060f0d120201020a021023060d1a060f12030d1503060603030e 68
    0xd68020700441c0200950300308205001850031201d4182000505800803030b00f140c10344120402034000500507005600005644030000c6561800d40d6400301550800e20b419042075240200040d080c031800901440c810121095840d5503050180f0905501011507490151196446500c400445003400724a40c20040032400031000b1040080b503c01c03024000b1103095032031882c211a04000601002e0b43e15100304545805158003500952040681111058026180600e003c03d0303814001e02d1006460700d408010702540390f000080703a402080440302c484c40c80000380c1c000b9240891451004151407000b0581c0c461054064014004c424503a800341c5248844201c102c100b0f81e51b42071000f1030310502031000108902490311040d504404040e01e00d024060860f074a10041ca10341c0810004003e0707801c03003008003d01d401d02d6406507841040d204c004601444016490790380c02280d0307c04a80315120489800d0142850316290004c540101e000e028280d941d050103800310b030000c002c460003000701d03070b41080c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 461299829 1250 461298579 461298583
    0xc090f050d0f022209030e01170907150e040f060302041401080a080f0c0d020f100c020712050a02030703030e090c0403020f100e04090804090e06010501021e0a0b0a020904050108 78
    0x254072904810403050024940e0700700b00c503100302c00c0c0040b0941100c5a220001d120800d00c15005200e00c02d85480c221544400e00241c8403484c013808030f00c3c4000d01c0340c0811504030740208495003120300813030f1035100842011300c05541103854911684d42162a10480b00784211840d0421000c681c0284d03001c01144524260401c070082c3d0900441d1030f640d11048000c000031f4245402003900e59000c040349030400c0c0030b0b201101c1c02c00b100104041300603070161361151001d5200b07001d40c503840c1c00d10107003c020f50302c1c0041002c0d44903140c9120b05c02c00419600045800c6c80014444002c1d1184d004081d81c521276224038000d011240c1850240340991050400a104040c034001140c003560f07001055000a0780c1040c00300008020180b181e1010003035545200c010310348403401150040c0d0701c070310001a101d41c01c144140080701c40e0045801c09503484a00100701d50b0760003242010030718641142580344c6660b01e0030309520749084903800034641900441084016030065010b8200c00c0000c82e0240410790762860819 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 461301079 1250 461299829 461299849
    0x204090b090403091a0702130b0a0803090d0b04020a05040c02030c0609012a1404091a03072702122508090c010e04090b0f061c0f06020a020309040c090f05 68
    0x24042500d9040900007825007101a910740782c29440176525001050b804182d21701c0d01180110704082e1180722007800e40c5000c0c940000038010764030080d07080100c800e00182c18807212981c00303010205000c001c2020b648030030728140050b0002600070f020790003c5020081d0f4035030102001900900521001c03494001c0103000345941d603014402001491052030046080e016100103104d014096110302c80c4107454400c01c090301c0201890078002a4448a540c0031049000f01c02c808107209810440040c0a80e00344406115803140625200c125103c00c081030b480024882c801c82e0010b10780c1007c1c01c2103d25070b00443d05020302058560240c402507607250342039552000643c0c03024003540180c00941900e5120302c0d110444000e00500100d2103644036180da2041c000d0a0341c16085529114041144608144207103d04129140040c0d59968400ea201d80454002c0007600809581d00090b2a04180c0c1c401c101750f41102c00d000700b0804c01a01e40001c05040c00015200e83d1240b0000b0000000b00351504000345 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 461302329 1250 461301079 461301083
    0x3c0901060c12080703150308031e011503020304031214012111090601180e060f1e060304020a090c020a03090f1a1e030103062403081801031e0204090b0904 68
    0x100080700c1c2c415000d54000c40b00903c40000c01d5501d524010004c1003c0e60324000540c00745210030b603641000100030080c44d0000031419000038800004000010f4a4140210741c141d0b0b500c1c0068076a255490704966400c1c03002c2c0501d92041c10880321810304c4140b13030344090480d14040c0c10203080500401119502a01c41c01c0090700340017055a450005051078100698410380515040740c8109071090b4000450000750400000707162841e08110080c00c001099010305403044034503442e00103040840c0303003801c1076842d081c1d405003201001040c115203480400310003504d0000e41c140441c501205000f50781f98030940d0185c000418191000468520350f98031002a10030740c44030307808006071840507103071560303c01390309a12150a0100c0105d0703d061040301a5010790310401c00455610700c0080400381303950084050882d0405500c07010800148c0794000c031903440704403640b0b25941c072060200583c0281070202403000341a020304601c400701500c507030040081e507003180c804010740440300003440101e20b03080ba80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 461303579 1250 461302329 461302343
    0x60c1e08070e21011b05070f0f0303090609030509010311040807140a08070b0408010b040b2808061305010e06040b0723040909030e09040c053c0901060c 67
    0x10910780303032040c1c8048046040280c450031007881040400c120b0081545540b4070980d5490000b00b115405045540c0340440c4546401e60800c1c0d125201c0c00300100003004010060a800e012100415010b60401ca0402c0c3e080780040100291a003006025548881c41450000745080508140070010100341d805403120703080141280e0b802c00c80140e40052600700965844150700c036001034070740000c10410000d48020308049403203628040315142514180300103188514200604082941c46034107911407403001d600001c03107607080040010700b0841b0003a000300d14107005181c1040480b1845041444c004c40c071484c000c00200380408242a2143c0050701c0c0200001f50680105d5020b51142c646070421175a0420811b8801c5402d01e90204680e0290b400600e0458031490003805054126160381c1d1099416940f00001d45031564640c00c2c40d01c07580c02400d00c00c0c0103400b800c81c41aa070940c1600c000e0501d481d21a8080780002d10341002520144654038401d41e0010000318802c2d00c128a400c0b07100d540a44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 461304829 1250 461303579 461303581
    0x206071d0d050109120e09011a0d0c0c14030a23070209060102150112060f0e10020a05090307030b04120906050a050d111201030c1401121104030f060c1e08 68
    0x20411184018081c0203035500c2d92501d410340c0c0820fa4402903801c10490780d407556500f03000c2440a01c0243d02050b80403031072042d003c880d030b036030792154840407121354200070f50001070381141c031030401d40b11003030302420141c0000001e90340a5004100000100040040c1c1d03141c9450380883d011510800c200345080e0640c1c07400b024814080142800c44500d504500140103440c41c0403101d42141088240c00da101680000c400c0307040006010701441104004100800184000850b1010340b595408504291540d4694002494240c2031f1007841036030450f881c01000d643c02039075641480e034260b00c03087d01d090302c82110381000400c20381c0c040d80e02e01c81240c4039034580764240040c40070141c1d8150040a00b60750034641381d03100f11403440301490051200703a51300208155554158148088001490b03000980d24880b003c20910031a0307000001d45000100d4860302040c005802c024810141c0a254001010480504035500821000e40c0000081441c540e031401c060b004a1440c0d00b4111502002100124400034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 461306079 1250 461304829 461304887
    0x412110f120702120a0b1f0302030c0d0302011e05090f03071703090703020a0303020d1211070206131a1b070b04050d0f0b0c13050d0b07050a210606020607 68
    0x7000e4801540014540e20384202e0200c0702c03500b044202001116910302040070000c41c150401301d00011445806910480b950940d40400d548040400c4454812505459a103003018400d4001302405504250b4001815030300c2101c00e00038007001d46d24545140911800713503807d500e000061715001c070b070418540c40303200c56212820012a4006489c01c402405600c2c0f000c0090303140c010383d01c1d0042d03110754000c0000b4411048000d200d0071046244800e40340c2022000c1c250380600c030046c0d8101c0c0d501107a1244e03546003042c40d81c2211806503031104411400c82c460300140c4240341809030100c640060000088a850204882e0311a0840c1c0120b001e100c80c140003d1200f801c0101034402e6280c41149804561005900d0f1120303c00c50898008a00c001c001645003100721500390000f00601c010380340d6089544441da9550f5255000400c1c0d03800b0044040390601205108a040d20100b03024172100c0400d110080d402c000103403c2074003429001d84900c1011544e21842120102613000804003070300c1d5010100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 461307329 1250 461306079 461306113
    0x806060915090405160b041d01030201080a0f0e0f07150318120203070b10090e0105010b03040605220804060801081f0e03040e0a06060807020a0305091009030501050412110f 76
    0x3d082903a0911420324041a0888038850500240c05c000b8034517034841c0e1412169003840c000d0000148854500100100010303608000f00c26041508408007080007507421000301c0040c1980d84050300103101d90030011850f4100420030380c1c265540c4694209038603842110036400d4450f00344030500710070000407071400400c0c030604124410000c244142e9282052580750030444003010f507001d0180e501d040c5420058011948210310a0221190080c0229803402201c0c82060000500190900781c407000000e4038035428110001d03101c52200100c0034281b025003015020742d00180180c0000c40c030790b480046942c11000502d1105c900c00d611001c00d082c516142c0d48401380c00a400014440e00c8280000708525466502d0140300d40c0000c030000540b180b03481c0c1c0c01044a04042d04060946d08400749100100c1d130320800700d41c0f041e41e0540e503c601e440141d54045a0540056201805551801d41888104102c004500c400e4020941d10317440072040358444552100400150301050b54000c004860b10b00d40030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 461308579 1250 461307329 461307331
    0x1020115150813061401150311070f06060f0311180402030c100201151706070504060504030807020307170307030815031005060a03120f1805060a030504061d07080606091509 76
    0x5080e004144030f0f640f0355107800070799a6195040500d44c0201005008240c01c440070486d00d50301030700d004e024a98880d40241039610032464040e00103000e10364210240112500b04100410120021141280d07583c00c24001d90482140141e00c01d03043d5000c000e2000c0e010511b0740d400b0706d80090292088080900030001001e6231502100255501c544801c0a40c07101c0c446124010300b00311081000c56030b9040007182c2017180041c6180188242800144440c81c4d01005071029a50b000e940c99030703641c07810700009203001c00641c410441641c000d03804403412174010007c0d2504512039128000b0310340350b0901c1d01904e050184002c07500356101000c50b40c445402c1d90007040c1c002c0320160071040915100c4c0c4405080b8030703030801000c001c581d00140701440e0503030003010b645c20248650300a59509007080000380e0284502c140704e00c10552100702082c103000d10b43d070008204085001c500d10b0342c24580003e80761104014030903150103000d07034030000711030742482c0ca0b4441c07044111903d444100b4207004200411224 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 461309829 1250 461308579 461308591
    0x20a06031e0c0c0203010e01020307090303052809082a0402070f0507120b0c0304080703030b04150807170a0c05012006010f150e03100f0b04050a0902010201151508 72
    0x102451800d141c8414440c46001d41080d680b1940710540d50300505080d078041c0c080c2024540c0c410410071070000d40c800c24070b105885d070601d8507035566000500c00b04040d6070049521400c07111a03502e1456010382066800b4120b0303402c9000e0342c401081351500e6502503181c00720f0100220034004510211442c041c1c0c01440314912a0094401c0c0d2480741e1a51071400031940c026000700701d081c40c03641e420310842c0071140394405c2098480d1860351405540789a0f50703008002c0014285030315601d00400607a11030f00100458130010941c1c010960b5600314840e6a5a5079200d502500c001c0144070340e00c941030114a00110f5500803e00e240c1c1145071100440d22641401146d0f00c02c14030303620301301c40840810321005000304912044000303041d0070103c528000d015405000300600540c0354551445440120780903111001000001508a90100600c006022030500c500d51080c1790104201500c005603001021060007a03008001007a0b480d241200c0c40e030301a01030003544001200701c06039018491015164000303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 461311079 1250 461309829 461309861
    0x806042a09200712030506090103051917071101030b010306050105070f03020319050309120304030c110a1809060f05060303030103110105370311040902030c0702090f040c05030109020a0603 83
    0x4020040349000f500b01c004116055540b0b00307a0480303c981e050080310342281c022540e00300300b540b65903a62036507003402d0781841d40d803940050884018406040c80e00c8000010400c11140c1c4d40142d03140407141c0010b0a030b18103020034a001030359011135102e445400d040c3c81040c1c41e8a49007400316141d07600c0c5411116030403811440100103aa44001550003286c003075800b036485003030322030800c01111801c0c159a0482c40200e20b80a208020119500060b00e242e4180c00c80800d4240b464600e0200b03801c02e103141c2280440d1052550302640c068943d0784040e280364041c680400c02e650300b003440042a100305031100780d490b0340b080c00180040348030102044607400050410500c1d0458400c1001401d070001d00422162031003005400110481003580d542503040d03540303400c01001c050b40040c0003060046000320b803850740d4080001000c0200705011a403030a500200034040034503207549241c01080c41110211142004441c00183c203060502803070810641c028140c03a19941481001c50013407890325810102c0c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 461312329 1250 461311079 461311121
    0x1902180f130c08100501030c0c06050a0905030307021f050903040b1606050c030108190213090807020301050901020405031b010507031d041409010b0f1503100801060806042a09 77
    0x1525900c01c1006580140c0c50780c070030300d1500080c1c0c84c409038003076440700f03051505019500401e03590041d01a281c09034056030004507a2a80c105042c010005250010541d100c000140f1443c2c6400252001482d10203a280c0280c186202c6485015034034265040b4440b94014807061200d002000007a1400351a2000f84101400c6240c45020030717031340c080c0e0310b9190103030001005018840c814445010142e0000c0c0d28805040c110b5404145c0700100c8010011106680d58510005c01ca030a10450b4a02078004000388298240b10345164001d41c403a100b154828403e90000c00001001c1410807800c110050f1540e5090030f4550303c040d500c080c2c1d1150b03116030429012112041c40d030f941740b03e03a03002c0703018154502249107001e10b13a840c21502c51381d00da81d1044117038422031240c170759901c84510301c0f810a4884040d16904c0310340040210281d40d8001d54010350a01002003895580003038158404da0140d454041005494501d030982400c5902c004400b81d103a00c4010b000340003541d0449840d0703840c501502040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 461313579 1250 461312329 461312359
    0x8091204030609151406090613020f120601140406030f0b030a030906140c060a09060b0a0e04150207120e0a05100201141006080406090c09090b1902180f 67
    0xa0391054108899480e555008281400100b60a0041e0305130005010400300c0700250b4002c002c920010241442400148005000da480b8035480c5d02d100003140c0070540d2902c48484425109400443c1ea101a00d50100d002071290342c820300003814450500504149058240700d000c80142c1000210307800381c01c0c0c407943c01a625440030000050b0b4140665240d002260402d40010032034111065000b408180c2808407810300040403585581021810000061102151500303602030581764400035032146200704001039a030341d000c00051049100f1800071800031401c07110740041340203408010f040a0181065402d00502034200d48100210003003495011582d034100281c80c9160b0b440301000141d45462410303600880b812181d5801c506922030011059040c8003005102000041003e003040b502d8400020502521503c40c1e4080c100c0318009222450b00340c1003001c20100c5c01c1d252000c0240003408000c1d20000103209035000c00c64603206284050121404000408a103c80307403a80c040140c00070005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 461314829 1250 461313579 461313613
    0x4180c2a110a0b03070908060717092407020601050d0809100905040e030a080a020a080c0714030310030b0907031e03050f0c01060501180b0d05090a0507031119150809 73
    0x3000f00803660200340d9078a440100102041c1095000d460160b003c2402c0c4014590030070406040d4001081040440380d642c00240c42c90b04000c005070039a032004081403401e2017501d02d22464410002c9400721202c03641e0303a000f0b20842c2481140090410101441566110f02e069454100c4941e56031904020342c45c1c44100141c1102e540140c0507a00798030004d0303901403c0f40c11030300321644618200c2085080c2079880001a2990000402440c1c001c0d40008000d410400140d400099000c620300032a512440d1008103041895028082650f900da012000141404070000d901c4054030351142d41c40e2489061072094480c0da03901c0810485c02e006080c400c0410000500c40608400c0c04a400045082d030725140000d0202c1e40c0c4c2c10117030054028014801e2001d035000008541e0400040302001400756038514080d41404079119004145004120001042c03080d45000443c1c40042103846095160141d241403401e00424403601c0c1e07100d00303804082d100311802414140c3d03100d51100155644001030280da20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 461316079 1250 461314829 461314849
    0x30f080313060e01051f03170c1006030609060501171b010201020c060a0603020a240e0103090206030708010e0c041a0306040204030c060809070e070815011404180c2a11 74
    0xa0f900c0d039540c504010004c070b0401c0200c40c3d500360719110b02110034210384501d440208200114030304818006071070200400104064400140400400c00c03010391a0700e40b034009030100342000e80710706050000100e800d483c00c3c40c4081d2402c101c3d2006042d2040b0f80340303074595044a2071400d941036550034030030b00d100c105042c8220b6120328040303640007030042c2c03c620400c5964400d036005220380e03102101103010004000712103108005103c0c00c1460003d0300c003100407400340503e150029046003010092010381d54104802c98182c6410812108859881c001100d620340914030a0b80008494209000400d505820040d90407401c00341000d449d054890f10740001800c4140d202d0300028180000300300050000b0312aa002415000d071028803d41030041d4024404034000e400408100744080325502e1580c082c1c20241000150601c6690b1941e50303c2429010301e54a00315901c46440c1003030002081d49200e4480d2020500d00414404010500a160108260344110049500c0110ba04110045541d080102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 461317329 1250 461316079 461316101
    0x3050a021c0b040507020c0a090e0a12080a0f020a05040504110f07030f020115050a1401180f03020111190b090109060204091d151303050f040627030f08031306 70
    0x440d0b814512070030700040728070007001242150401e0240402130380e6420310380e1040310700a078004034031f20f0445d03140c150034000d40f0a0010485083c1942d501c00403034210840380e105201c0054100b21404008000740c00740d205103090403000507000c1106000d02d180540c0700c081282d840d1b00440d03041c50111b0121030300d5603204203416800704e501c600c0c019844d95424058603400c6600016004035151510700402c400c41807a000b03001c200c06415040074103d03403041201c0280c210a0b034851840480c1d8412142020800c01c1c00140e000440f003405c1018070320341c0003810020404103200c2041d000881030303c40140324040948151025500d81100700c021444600182c40074015040000446121508041d80c0c01c202c0c28203076110740d030054980d1300c10b0000400c41c0d6640c40800360507000d90340c0c1c41d68942243c440c403d521a13340642c0b03012902080071070340310b50101c00d606583c1d007400701291168124281003418610008011811104640f000241958043c50b0451400310b02090b1110603566440e003a6a0401e42d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 461318579 1250 461317329 461317331
    0x20d111207030513090b1f03180303060807060c080406030504030c0b01060905130b030a08030907030f0503040f1d01180e100e0601050d0803061903080f030f0601030204140103050a021c 81
    0x11318200c1039400700b0400281a0700c1c2d400c002100740200891100146006141c47c0200d681d1241d4070164001c4d000f20b281380001c400002020b560307a1401600500440c09800c0091140f1076010902c24090403265a2054003e100c160605142c400308030090000140f0450130407403c01c41d4800080e4a15019a020b00802c0c0c0b00e08585a0a15050018520507104080c048504142141c1213039180414039641040d0070409003075607030303940360181854000c5a5000074215030900043c07a092110100c0500203440e0344400c40700b25503644d9103481100421100c003000762035403403800412140302104034128660603401e038007203120910004124104403c0061200c2140d4549140c8205600107014050141404981b5946000e180b511911501c0c080101002c0c0154005e11100b810741008502c100f008660080c6c019541d85007115400d00280c00694020814541c11408038510750b00038001c0e60180c500002c11030b65001c0303460004401418000e00200c056650130059480003059144405e40e2843e50070320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 461319829 1250 461318579 461318587
    0xe0a0807060f1d09060616060605181e09010f020f090310061202010336030e0906060706090309150314010b1608030406020c03120105091006020d1112070305 69
    0x840540b0481c80c0b00102d404008501000204950024440c20640142942c520215070340b0000403400d207204e80d0076180c081e0300c0d25010103401c00000717400c03d80680700250342c507024450030f04008040c004006c3e102042180095210300140526200c4005c0d072040b55000040f41d48040644e4032412a0301c420344031001c1e5000001e011501f0f0808114018520300d0081e02000b0b42490184807040215900d9402070406844080843c4403030b08960f00d0700354403c504c02402c4100c0744041244012045018030440c0800d8428040c024a49055070007548031381d074090005803401010f0760303500c001040c0c3c1c00811000d000c2d1042c4041007401400c8510610f0018035100020150318011002c402c4200c164000307028a075040101446160b03048061000960b03000501e19166121468401d000c3d000300100c843c03140c071011440000741115a86da460407504160751440b4203840c1c01c0d20800408000380500c00240c2c1c40004003c2c20117110700f80c6101128910001e5550710303902141c0c420595480400c086e400220041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 461321079 1250 461319829 461319839
    0x2040c030902100c110402070c0b04080102070c0801050f0a0c021606020705011706060d0c0527042a110c0306041a07080411090606160f150902060d0c0e0a0807 70
    0xc001c4603c020410b00f4140c0d0101c03810b0340c403000e6281c0500030306406150040f03108000c00508640302c4002d0469040c16030740742ea03202d04056000b03420220080d11034188800c800601a54180318040c041c240004843c80c00750380340030006010781040300e80c030030071803113014140d1290f0580458500d000e0f00195003c4c24450745800d000400003c000440400001e10a00510078180d44480468a4038109040f002c01c0f00e40b2605015a09805090038140e009210b01048240c0c008c0c0325900510510011a0104043e03410740a00d40020341c2201900d024980e54171070425052406035542010b40c04003402100c81d99000b4001103402c001e020340d07084407615040b071607440d040181030184a41c000541d180c007405500e0310340c039a0b401d691101c9070b001d401402e2880206010751641c2c0100c5503080400d40e4071602020041ca0100e20b50981ea0009076801210118240c4003d001e6000300d440058004000c10300700107441540300000c001d50b080000034800603407204c02da01d485101e81c190092443d04081d0403003e1a007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 461322329 1250 461321079 461321089
    0x50a02040218130618020918180f03091305010302031009110d05030d06080c06031906090905030712020303070e1c05010e15060f0d06180204061e0e0114130902040c030902 75
    0x80c007000d40c4e0340c90040c45950328036210179802440700c0c036550346030b00d688d42c0b203550300600c1c01c040340b5281900034006c1c442d00c50308143e0008020144800305640e850b41140d031032270384641228400e02000350b040e0050301610b610410540c10820083e0b004890b0742401c0100e40d00000d54982e10200100c0e41c54001080d000407182880c400da0000703000c90400f07080c090655000080300d610000f00010f904000d901c41e18098000254055800f60030028410000c0f000b03e13040c29a56a08050011180c40e1075401626852504c04425139005441548900003080003404c10490382e243c030a2003030003c6141c1d8061020101c0d1090094003407640035034024041d242c41036944240c41c80d8000345a01d000351b4524072101c40944885812540041d0010800103118491800c80341c040702c2a840040d50060400f440442d4034070b9500401101219640200c12a960b80c0d0507601418007400d00c0345000c00581044981ca040c2071007210a01030791095203001034019076940c0001d003282c01d030358184030000b83c0d54018070b1300314205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 461323579 1250 461322329 461322359
    0x4090917040509161101110702040f0e0303220506010e16020c0102150919050f0f0f07030b061302070c03030e0301052403070b04090225050a020402181306 68
    0x908052070315040c200340c041030301c201002d00116040b00c1c3e50540b900c1c40a00c40c02824920b010f0a00003480100d80e1000f4040b4150042c003130030380c407440c40c10228070030506417481410000079401002e5821a601d0711a03261041c0602c0950f0b080900300c00030074000042003803151502810a2451480240c01e103203034900c41c0180701c00c03441c0c429980701ca49448000e80c0c002a0f1040c120380702da00100000d5441a500600b0800b110170280050004131200d101001008114003100d80c0c40241110748a903d0307401016580d030410700781010180c019160600c081500386031740560144001e01403031a02c8107400305000032644100c40035036a0310b2a080050003016440400030501c100110001c1c0030505050700d035054481c613a0890742109103440507100c9070b2500c0c00c0c4160780c001c0c1b0258148640304c42e82c3c1c0807014040d5020380400b4030181016000d554074410703040d0114180e55004401131510003910303400d00c00250301c101e550107a0701078030582c1c00d000c40d0b465042d0307884c11012954000c902107140109108140788 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 461324829 1250 461323579 461323613
    0x10c020c0603040506014101030b031506060304210c0c0527060102120c010b09090604050a1506050a06120b0a080a150e01090506090d0903110f01030b06040909 70
    0x1002c00500011a100062650642c0c402e405070304480d0143c0c1210f19499110a10440081000720144002240b03040d0b2841d85d9401c030a88060040e4a414420143c6a0140540500c40e51100c0800318590341002d101450380603110b44c41c40e21403075a82c1c03009401001d1034142c8802c0002c01e4608148200a07080d0040401000107076a905800e194503070a4104401c0301e1a80600f500440c1c0001402e60386c400c01449800310301c40d0b030066a03540f40703d1407440d01900e21281424040c40078100443d031203140000310a8412500b00b40504602080e9541c2d42e404000b1401e20784968075100e21001c50a07075504c420710750040c000ca85806200c000040c8200d411f0b10404900c541c89003240030300c1000443e4010595509595001700546c1c1c0c0c00c010307419410010440c401c819141e81d0718000c08101040000034081d80104540d80c11030b1494510407008880d05c900f40e003c000c111200034114444141000595591550014140440c0300c9a04e40007003103094000c1d0b401080d405c0c1c2c44110389414848140c03503088c0911 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 461326079 1250 461324829 461324839
    0x40314031e030c0a030c14030c09090c0a08070c060b0a120b1003080d091a0a0c1205060a09090503090306040507050f040e06040f0807060e010209130209151b0609010c020c 75
    0xc81c0203d0a881c16005a269010500d41c9031400001030500c01d0070b00b203246504080c21542c82c0d040640d4009200d4110307000180c000d03001c581c00b00f081d21401e1001d88052107104d0366049281c1e91480411110301142c840c04498064550b12041819a51400b40d01c000d401e55800d0071507a10214100900d1080d0040c002840044226000340089000c10b030465150312503410f40800e400f406854207031008680c41c1400400c2e90f01c0103051083e250750700e4002e07e20200345079540c1401c1403c500e00786c008582c01503540c00e910040300c5504100350a010b402100415004406036030038400c1d81d802090800d903040307404a80541051800f0304c001e140442c8c0003c2c0d11182660200311405d4031000c42507513200f0190010f000001d400b2445801c2025a40844284ea584148207009403940343d000341d8082e4001c640614440e4030b003109074000c24040c500c00e46440100c005d0041412042c03681d1920140e500c428920480c811005030300610303c81040150134090018080001001207410070028144845000c07003910071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 461327329 1250 461326079 461326081
    0xd02010f05070e18370509070612050c0903010e06070206090312040b0903040f09050106020c01030908070b090c1804050708010e0d1215090b0a081c030f02040314031e03 74
    0x40e01d40c1c0701d2060b220b0100d1141e88002e92203105c0c1100c01c030280701c5540ca1011207403c01d54040f4544042003a00b01340700e190b00a000546900c5112925511540a0280002d84d4401000028161034200e5a0400b00c042c8040d403401c0003840c00b003170940e01100c4d40c00c07000364099010301211550402c40c071ba41c0071440002550410b9540180d0000040d0041c0000c1c1101b4040004036000c81d20500c11600100700b80701070101100e039100b8038040908000d00c1050090300800d00b00c06095402070007104d4159a00422141c44c01e60180d858905080c0c0c040c141015a00c10360155801c0c0b41c03a4401c01440108401a5644603407901e4a45240b51640541154500f80d04100c9503d4400c040010b04011082e8603060590101c5d0f0901c440740000e00300c0360940d074000d240e02d490019580c601c590002060900c11b88400400c1500d402045503288100c813070f01d400171885078202c4800244650300241e1404100c10780503103825500d07194982c481c1c0354605070643c40c1e04005424428044c140f01800c41100314075524030f0035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 461328579 1250 461327329 461327357
    0xf081c2414040902040b0603090a03030e010911010c060b040218031011040e130803040303141b04060e060408030409060e090d0806010f030207170d060b0c120702030f0d02010f0507 79
    0xc041240344001e406107441d010007800710b5032660040a070100300a00485c1e203a1800c25295031761144000c3c0150042460030000b405002418081c083d0565007029888607040c41701da0044854021813002a01c0716070755401c0001d600d9640e40002d01c011560302d204e40f0218007640c41090b0504141500a02d94a03240180d002094508101038904440c00707100710040c20341d80c0100c990726030100e45600601d000c42c008108000c058144e4003801c2c001101462885050b500e519031800c4040112002544070082030100300661881403403d00c40b100c402401e52400c050342e510400e4910b401c240c0021143c10703120b910a000822003105280e5000044600802001d901120050705850014152030304000f480002019410302a4048402c203c0e03212548a10703a030380000584c0c816407c02003160191500303111000940b2400101500c4180c80b609018114501d0943e503a01c2240d07005a10403a058081c0304492094800240715000c241e40c0180c0022820b2040501204100d640041100060015100001c1c7c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 461329829 1250 461328579 461328599
    0x10605090a0b011b0b040c0501051e0c010f0e151030050a060c08130309150c080f030714040b0928140405070306120f081c24 55
    0x14018648440c00900c4100310030040301c044030410516403000b03400c10b00400821171034060a51050307002d180e00549654484004541c036100e1003030301d144140c1941c1c030280782901d952402840c4c0c0300002d4000107482040e505d16202585c4004448841c2c43d04500103810845082020f101e60065518503030780c5090341451301da080c206240704800d14801103c50249a0050498201022001c2c0c1110840e040306105290103070241002c15444000101c16402240100d041c503415400400c1e41920707075101e4a4105030002d40f41100c548444810014059001c1010540c000014591080c003d1031031079032841c007440c01409180783d020b01d40440c454100b20420a107244c2c0002c1d1406000122080340f182418007400300a14070b2a509102080e10000100244000851840d0b9036039080c141c40c14410f03076803588c4090341120750521441081c10f180614460016007040340c05864184250b13103c90401c1c82a607020ba51007101e0300c100d102295914541524203200e070685c000401a86150180a10340c20080b40c1c103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 461330935 1106 461329829 461329831
    0x1401060b1306111002070b011406070c030b04020a0911090f0a060206040f05070f0f05040b030d3c0509011101090503092205040507150201060509 64
    0x5030384140c41041e0307001e2015285507020784074a810380a84014030070b0300e610f09a6001e0003a100d2001c1c01c2d01d101608540380200c03002400c56040100404101c1c06188910b482410107102c5e010000c0d42401d072490079030b5800070b0171040e19111031000c140f00416980100f0600da0402107400a441204000340003000401c85003210310090050611481070114059240141c110a00103004103040780d0030340c01039a01c940100c90050355140050b40c880340f160b0b004401c00d80305015040040f4a05401514030608044000c1c05840944c2031015148420300e0320110a00120828203000302141220181500c0080e84a004400034045100134516400784440c28007103401d03c24a0540804140b044400d913591001c02140f51071700e51001c02c0103500168000e801c3e011400e255480d03810b1340c00c0c05003a000d07901c5000104006403e0541c0403081021803021a411685041802c00c01540d9000030f003 = true := by decide +kernel

theorem cover : BRFrame.Cov 461151079 461330935 := by
  have h0 := BRFrame.cov_init 461151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 461151079 ≤ n) (h2 : n < 461330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
