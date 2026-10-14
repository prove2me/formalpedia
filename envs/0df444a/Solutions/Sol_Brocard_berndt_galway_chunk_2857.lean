-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2857
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:56:42.37909+00:00
-- url     : https://prove2.me/submissions/0da7f255-14a4-4799-a972-adeb1f5c1259

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 513669064 ≤ n < 513848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 513670314 1250 513669064 513669067
    0x4090203010e0912030c0906070203060421031a01080925090606030e06010e091603031e0e09061908011a0406060c0816150e16120507030b10051203 65
    0x40070408140071002a104903083d03882030209130291000c80c011260403c010303520a541d40d612800c00300e280c41c0141c040103035242c01484100310500c151903569451150a0100c0400c500f1215041502181c080c0035005d0005000c41c1201c2d82c055000f03120458000c1041c008448001c4c0044440410041c54034a1020300f80080c00c0701000103050900414010380f942d4141804082203101e44550707a420141b191803000e000c182c022400300710040c010060100d011042088086469080161071074132244241d0701580011109160400c0c4140542540d024005088841c60b441e280100041c030a0100000c49005080c404001a0308200f4850204d08845600f940307509124280d04000c1110324070340c850710a2001041d03c4100140c503003002c0369036801c0c040c0610340094200d4203080e24280031840d07800c1c0b0382526026a41c070842400090792180030003101e10b0411810307100c0c00449940e4a6101c0010f20340d511602040c000a80141045940001841440c5030820b03501d0780000c09c50840f68101d510107400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 513671564 1250 513670314 513670319
    0x30902041e0e0705010215130c0509090102120a020301051014130e1b09010c0f060908070305190201110703030f0b060714010b0a050f01030c030914150a05040c0323030409020301 78
    0x1010f012500040100f400581030b40425040d007110140c070014901c08905202c50361200c05c103c10564200054003000d0b00f44641c0b403070943c02081c002c0d40a20711840010640c480020f02c804080c0c000c0720f0503503001030203100e6036a14090095034100511105580c00718130901100c90541c0d00580300b10000d03e101c00c1c2140344ea050490a01000004880b01400441c10030000c3d06c290303980003185504003d0b030001c500140459203081200007000c46410090502200044003800d040c0e03c24007030b06800301001c4d4005048000850305900f04d54446003404c80001e410300455012900036130042001761400e0401180c02d6025000181d0640d001410444030601c8560440702d101d002482480048182030322030700040b9050034001116010554000c030b0406481d042160100703482900300c5507810317902055072a51044851041900d5002901c9900480c0800030005602500640102801603420002080c00c40c2d0841e21500c0b1044613480000380070070a004042114400d08200920042511800040e203d50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 513672814 1250 513671564 513671591
    0x30c030e0f30030c1203040609060c2d2708100e0d0201050705090907021011040602101422050f060604050106080403022505060409051506031006030902041e 69
    0x20501c00ca03100940c018084e840a108000031019012075a01c9086078580d962494144085c08400400030320a0b03003011149240c0da80c00462040480d000001750000d8040b1303400c82210580018078000c2c000499180021400c00204e046c60420341d80d602d41c0844440d82c8425200f8a42650b000c201c0075920703502ca41c4480103440902a466042e0a18402803203030b802c01d2900100350380504092940f040d44084086100745000308441d844a8150020901801c0707039440c01d01c0e210b5000361158201500595061030f903482c0c2d95201d0009020140d454500068540200210140140c01241c0d404055100d1102c030118404114a0715076103803001c000d0400d46001d130203000030f641040e8051000e0100c82c00030b01c80081d0b004a01011409078404002d1001074181260001010180c1d00c0325400c210005400b058240c60350b04201c1c400c13848002030840550000d0140315880c401101c804801c18109202030090a1198002d21080f900007000460b5818540081013a98001e41c0c08021440f65180e00046025 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 513674064 1250 513672814 513672889
    0x110a120e060720150f04150507140607080106020d081b0403021504140405060306240a0816050307060f03151a13082d100c1218030c030e0f 61
    0x644c8407007030b15081c8425120000304901441c040c903c01010136115202d0307007070b104806031110301e0b0300324014907820760910654944508042e0b58400000700d4403400464502c0c0006040b045004541c1e981c81125910b45003201c000c040c075041320641e43d605c100300000150380c0322402c14010280140002d0303a1180b4142e4920003180c400a11035000d1420442004102d0b603001c94050750040030380168404910279040450195000c0c404090b9008070071300404100b1030b43c0020800301d03035a0380c400f440407599180d004150780c401141c81200001080c04002014482c0b10b43c2145030b0541014005c220100d03154911050151080b81701e500d2006d00206003101ca51a441d0b00134170041c010040a08584c8a1006403941c000e040d42c3d10b85031003400500fa007112070a80400964a5510100340c040000b074051403001407402d4803240c00350404604100c480160590b19662403c00d20b5410b07140e0702120740305607034280d5407100401500743d80981d058021890320384441c510142d003440b10001da100c2d040c8000f004090030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 513675314 1250 513674064 513674089
    0x70c0b180312030403030b0310020d02090906120304151b06091208011827140f370f060e070906180203040816050607110a120e060720 59
    0x203038071410702414100c4800c81104c0e08990940b4002c00c00c00e0b07040380440e01d00718260b803145112a20008503900c0150140c0e001e4000c10200b26404940d80c1c4651040011101d40c07109002191b4004000c03c11480500848141044825007020035003074080c0440318501c2104140b040e0f0780c4e03170348400d0b4040030085030070320340942d042c0281801c0101d0b5042628103940160b07000544024150741d10282d1036648000102444003100c40081c2003400912460080c0b0480007001c801d0f0a40d05c50600f04000649001c502d6150001300303041110407a091014416074440782c1c00182410349601c2c0e0b2600c1d00400c3e900e41c100c4003200d004000106628003d40085450300c4040d81c0264070f000c2c501101404212400303049074004103c1c1c1c030405030300e0b0780310b42c10705480500ca0448020012554052034804120001c19443e01c50300c015110405003803c0521074585a40c40340c04010410f520146011044a0055214407118040a0182ea060519503983c0068015a07802400c0c0c072900845080c0400f880c2003c0107420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 513676564 1250 513675314 513675319
    0x121209083001060903170c0706111207060e0d53040314040807030206070303022206030f0b1f0e030f1e0705030d030515270606090a0b070206070c0b18 66
    0x250108503407007203403103a448c0e02601d410072403c59840c40180e00d040003941900710080f00040d83c0d8112500d03142d402013012621604641c001e030909210243d00446e1141d48904980320851005890032a030200200c14451180402074120302c130510b000c40120014990a40c5004101c1040d0309240c140580681d00c0e9800400103106e0401080c01601e80100e5140308899058400356115040c500d03040c1c01034001c0b00c0808100f1000c503a040c40400d581d045a280c11580b40e92810030044043c5200d030015500c00c2c0c4013030380d000441c02110114505800c40040030002e483d15013024034420140000782840110501c07800554440e04880c103034589281403084042e07a80b040188005481c0801090f12012400d0700d941c14181e0720800900244105003500c1800c034402448580d207480c443d10084580d41480c070141203184a0300c00012050f01308041150f0301c0c035100501c0650418902100d41003180c1c481e0101720781100c014405200002d003d618010050140c0c80002c40c1c4801c284241004a08603552000e403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 513677814 1250 513676564 513676567
    0x3090503060603150405031b15010e0402060304080d0e030a1116080a030819110406030506010801080309130207020603181c0f030203070203130312120908300106090317 74
    0xd00d543d0300007003198003124082e10030300903075566040c400c2c203601500d80d05a10000031820182d00c0d240c1c0c0400c181141d9441c3d4048031a103643c03100210a0b550004a0300250030410405c04180840c7e080c5001d07280841001d50045881e03200101e4160171900701c42d800d0400b00701c030202c20401815003032080541d4484030100d180f00309407410040d1aa030340301120029060100344404615016200903c886284171760b4401844144549080d60b09542c1c400d20400002907d4000840c0c03d035841035012604a030a0344004504041800041007020f07201f008188192541c20482500107850f81c40155114112040b58100c86242c0506518142850344400c0401045010304446955401440507000002e880c03500580301ea40342030041c0d00d54401c051240c603482c0c1d5900c000204002040490f03c0b0811010764031241b000c11096040d105840700c020006100740800d00420310b41c11840c40441804000b5025503102c400c03000019000e410001b03800101c0029003c2609206000c641d000d0442c4554050301d056 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 513679064 1250 513677814 513677821
    0x11032b030e0a0f020d0503030705040e07080403120e1029031609050408072f0109050604030f0f0b0106020f0606010806010e0114040b13030606090b130f0f020a020102070309050306 79
    0x200e4603141c2069008000c00c0d03d0301409015501e82d80b0b109044943d01a003102d80e2820711100240c0150031910500060324440800160402e100d070b10280d0241d81e25450720b40070048a0031080c8064002054043c196101b40314070082282c0d101d00441c3d0710100b004250b4101640201c20610207805041c0c007407030013030b405080007502c003000c080340d010101d4009440005207a2034a2030102c50520507100c01502c5107850303142c5c11042140700c04c100b080b8880075010800319002e14000544400019126050380f010040c0010000b080c41c00386402142441400e01d40c100c40015660761040c001c2c2a0071030030069101e00140300c0300c0f01742000200c1d0002c0e000d08000c185481e1980c00207000c601390900d07450402410142c6c0080030b14011058501515000c00c040d500d490103940ca4103800c030365501c001c0d03648504052000031045060b00c107200c00c441019110400d001800041c3d14090680721010712540b90307440940380c400402030b2001c1c24001c030f01c59001603a03905050800511954a54200d01d05c00c1c5c0084060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 513680314 1250 513679064 513679091
    0x1206181617070504112b020d05060406060807091701020f0406080a0c030207020603160c061a0307091505091012030905040e0708030406031112010303050a11010b091311032b03 77
    0xf5a0525040d2150307607501b03d59116001060380c100c8140585096001180500404010350006407103800180d4081007102d40d10340f000c40300248140c1c0c080002c1284142c0c18841c0400b41584402d07406440c40000d4a09240d48400d90401e0344558820400914010f090082035000e40c01201d031020261724055042c42001c0d00010050b2001030314600818040f028400a1140a030720719126150b0800000c10061050f640c03001c254250000c0000e00c0780c003a1802c0442d1801262080364010030301000741004240c00c00741444000d820203000003140702d441d4400000c01405c080c40c00403c1910968030008118501350500c0151880c1d46020001500401c4040c008000f000066400b01c403110301d07020030740114120548a0794800d5511003c216417900d0700120601d030700180200043e800c01c1e0f959140c520100c0b105282211400d5142c181d000a244011500390350f07216030707030441c00350007034600500800508000903e07109a060010502e000070540484039000418141c942c001c1240c2024020041400e04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 513681564 1250 513680314 513680317
    0x30801080303150603062701090606020609060a0519051f0b070f170c0f010605030d020723210d030c0203070c0e04061e020d050105120618161707050411 67
    0x6490700825021000414aa440c082c500c88081c075141c60020a8010711071f4401d80303004090055510841c286030700041c0040c030001d03055218162242c041c04664442d04141c1028142c00f600c0205140b842c54682103586aa5108140c09071052800c0d581401015040c3d0041c0c0b032410b90700070303d56500107010407004561040c000c40100707680008800c00700c0095089032440c50003003e001b100c4c1407003a0900c1002c000c40540c0941d0a80d0800c5048404451410404a80c0e4109900404164101510580d802041028084d444043c80200308951340002c0c0300a14094070728600550101e580140801076a1326058802e1898883d5103201540c60507400e80c43c0c080900c1d03d00e1140d034140c00d42c0d4130009001d001c13896021550744180c2d0409008c20701441c0c0d908001a41240d00440e144925140001500d854019095001014541c01600079503891031004128107140b083c91036035600400c0d10703114000e450005080301908100750f0b110880e140407085146490140c0d045280150700e01000c810301f000f074050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 513682814 1250 513681564 513681601
    0xc031c11070302100e010e030f070204050a0615110328080f0106091a0405060f04060924030f060806010b040e010f0608181603060515030a0b0a0c090f060507030801080303 75
    0x85010448201c8400317141d004285881100300240800300300510036180d400002d012150080320706012a8a42c01d150800f03c0f0850b11500201549113590503044034002c1d407aa40310380750601d06681c10440c1000084180c904d104242e44e000c800422a5514161b401003c020b40008032420403060960500601402c9018079010703803081020420060002c8650000464000c0d04010703042945420a602c14480560402e01488011909800010030041c644011049005041108402580d0344158043e8018603e1682900103681c82d1440426200070070441c0d94000d02460b02e0a031394546c07904d103010407441c4043c0c00001d42a64488410000d01d80d2200d20035400104110b05900c003102628030035440e001d02100c001070040c2c080341002043c080213610603032240d0702d000d002000741200b47c0101a00d840078088003d20b50b40d8000c012550104050f803101550a200e4100051040d44541c4a03100512a541c4940700080c000920030080681c408546401085d4020082d41035041003513104407202d0045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 513684064 1250 513682814 513682843
    0x3021c030504052101020403140d020a0213111e09100804020d03050a0c05060a0f06060e0a0308090310181b080c061305090403120b0f090105060f0c031c11070302 71
    0xe9040d9041c0c0d02d040b0802c02901c00c0c4c2d070b00131956103542e03207001c8002c44003c2a10020038010300c44120f4909001250f40001594014654046104440c0c4500010700400340c00e210101010301c942502200d02c01c80003e600e4985151254464440b5010000580399180049003080818007d100040e2900303030129070002e07810308115803284000002140c541501d0030300501140304000601081881ca40c4c07100200f0880360000340050358a030202554a40040078203203400000130381d03041020500341000780c2030b2644002d0a131a07585040800030020f41e01c01c2626040c5900110204030204910b0041c00c4131210003c003413000d030441ca01100192100c0c030101500d07004000010740406030203109120100602002003c20700c1504160800030554480490b602645910302a08440e05240c8501400a0780f4070050081c81d16070f00744000d0107500d810201d4100e61260040c130601000b00010300107804d1400000d44a403c6070381070714070300c0c2c400c0e503107002e80c060f41c149000c1181002180d408207900041c0c507000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 513685314 1250 513684064 513684079
    0xb0f0f03031606200f2d0a08100e01061e0302070b0f061203180d05010f0606050d052802030402010c020306010902180a05010207031401061a030103021c03050405 71
    0x200408282103104000c0c54030b09150400d0018002c116850380300b96004005000003001410008401c8946480380d924100c15420f402c0c0315040440c0b03401c081d2401c034405407104071200c1a0540700301c8611500019480c00205014004100c40e103c80b102c4010000e002c50142e44915525005018041c82108504042c4107020b0031201a40c0718040d40440f107001c1c0c1d001c9500300292030b101e803904c2c400e06403c2e1441803107084101001800c04030000191105420f8a865204403a120b40f41080414055042c04546030754903002c00005680251141c0e000a00880d111940d55800340c0c9010411608010560303685e41c0f902041028094400d14030004810f403140d10010ba032038841d40016100f400c000340d07009602d0b00c500000490000b1094010b8400420320381c41c2d00510020032030070040004458060b660060780103180400118210303070000c84d441c0c0000b100000b50551266080701600d0920990880d41b280d002004204501308412450b0b1181c007210800c08041d201503400500c244501d20449205211 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 513686564 1250 513685314 513685339
    0x15030603021f0e03060f061002010e01240602060c0703110f07090e0f060c03060907050d05040302030a0801140a0905070201112a12040b0a0509061215040b0f 69
    0x990105018680042c1600100c44001c00400308141c4400400c00c0011071a01d0040000d080010f019070141e414030f02c00c0011a501c06046c8161100780998440840d900d4142e5400ca400d000e114a41c6902090f51000103d8100c401c010308411406a00c80310465103c0820002400d15602c15107d07503a6061400350089070075010700320700d004500c0b8203090160156074000150024160b11020440c134009040d00c1c0406844807207591290740c1200c002e1150082040090810300e031850390298070000c6800d00714201141c400180d0b04071001150220090f0b400068181ca0070741c0c001440500402c00764810208a00400c400304142400718801e0501040c1c480004c00c0e9114000e40044200f02c015103141c0c1c1d2511403e40180200900348080c160038032001440d002c240043c0031440203200307000d40c9240381c0340c2490040c0f101d2050384140d0b001010040b0601813900140d50306c0b0010100000080078a407140d081800038030120011403e0100d00c2145001c3c012070b1243c448121800307100504440e002d14804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 513687814 1250 513686564 513686567
    0xf0112060906150509060315010e0a0608070e06031501080d0e010509040216170408030703111c1106010e06030a0813091d0105070512010504090f050609010c180e0115 73
    0x9241d035001003506050064800160351028142c0c01101e01c1143d10703100c0c0743c445105050b10740115540c002041c2d51540b00501c5040202404113402c501c1d0890300107a155511400141041d865401510080c405842840031301e140812030361000c0b16a154400d02c03194541080c4940d94034083e00c004051141b02544042168090b00a490070401e01900555484801c98500090352400764000c4503040c2d0807882045a261907201543d00380c8010a000b9031501d09140c41c10307100440d54014036451032282096000c0b0358800c0740070300455a0750686a486110940181082c10417005812410200001100b001746541d40010900c1c042c6402130007040d03907540200071107403407215160844e0103140d00b0408107003412010350040c0e9603d47c00d20700080090b511144411205842a8002d05e501c048683c170060100b440d181e404a035045100703960031a10301d55543e91700c0f0304026049400c0304890f5500c0860344600f682101019525020050803418500c0c10700c08205080e8006004403000f441481100c4c07a48179 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 513689064 1250 513687814 513687821
    0x6060914030f0f160b0a0512130503040e0603010c0c2f06070c1a041802030c0c0a05010605041a0603040602130b0f03040317040b0711030d0e0601060f05030f011206 72
    0x400308800343ca00305001c54070f035155a5444260041c160300d10306070f4001a0f581644041c1c8003110317956540c07907181c000d580900c5100d1840241501401035501101d0304005001080100001c11080c03001994924062007010708490031103130342c03c3c1444aa034039280d0010311314080c040301c40034401c1074145600c10000510070700d1034029040d0542140d000544102408081e1403420111203100c0b1050501d015502d0b05400c05001d01d104134104141c81c0320794040014040c0d0040d6500c00300c5101c1603030400400101007894540c0004080d2542e0355140428481824280505141c1566008070340001c030640e00701088242c03000074409001161b0128000035261840c140703150083c0844003801d61162002e901403110313640142c404801044420f4071034406280c008119074880c81d0003445030726290352000425100043d10810074071082c00104a03440142e815803007080100d40f1524000c000325230415001a0915009034401c1d4144203061080000d5148628103840c10f480d0a42e81c840c0000d0700c1441d10354060b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 513690314 1250 513689064 513689083
    0x402090c0903060108160b0f0d180516030b0105010201140a20071b061407120302040b040b040f050103020c0714010926010c0e060a180510050c0d02010606091403 71
    0x1030140c3c00c000288503a00141c58400705900780800c50340c80b541d600362503d0b144038010b0f581041c01802e100a000d0043e55a008012002124000c01d0f810103c9554550411141d245030b20042c0700309030300c1031080c8243d0042c0d4901400080c0000c000030b2104640103904030a00a000c1441d1a032100d2442c1812101107080410320405025156110403840c500100e40740400745624107900004440040c3c1a845403031500c41d02d00550805500d8800240c46010300000709030741d004241902000002041c0030144000e000820344144600d440701d007071036000032020040d50321460400d8010b00c448107a40802141350012240d011641d081c2e0304256400680c0c0c041a140e0043c02001c841c00007441c8154001641004c250080100800a519403418140c664501940368943c01c0801800030421684c040c01c1071040c14461082d4804100c2d544500062020700c0c1410203030001400801c2000312242e04100983c1c05418500017817110500348000200200003078456002c0294011091030480d4406101d405403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 513691564 1250 513690314 513690319
    0x1008010c050d0b04060b03010e100e0c0d112a070e040606050108090d020318060d020408010b03150c0d0504230105011701020705151e090604060509150402090c09 71
    0x140400018040e60001d0b00c0c641505800d1a81c580100d03d0b1500c10842076400345041c85003140d080054060410800a00b001c1510b440314801090f680111a0213030f20230049140d00c20341d5141481080c0c4241c540500380e01c0008a000d203c803000052400c80c0d0a90442050070358140d8071441001514542011544000c000400a070140820f0004c02d8000c0310a603842030f00e44040320740740c600610399543e541c10394520050b0018401c2a4441005c03084c160380e000b000902c80b90405000030304020032a40650300805440c0e640700b140501c0c03401c0c00d001c04080110f480040180c60303d01010010801d100b15503aa4101c0c90b40c520000d01000420303002d1002d40f80c611800c200203a004180a280241421302803e010300350844452098402c05008036000c10358881301074a0046080345481d000c1400c0034144561b001c06480100341000e00040100348207983c91001000d4600301030a1080450b40c01411107000d5810203005121412658061075030000e5045e0780121a40c1c0d03e1725400c00c014050841c1390b50303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 513692814 1250 513691564 513691571
    0x23f030717040306052a21060a0f08010624170402040204231f05040302190803030403090905070e0132070305090423040f080d021b01060603020301080c09100801 71
    0x200b1004507a00c2076069440100e05422080143c541090f402442c46050400d029017a100740307600d000298031f0381c000038068641615140c50340420310014003143c200c2c42e2240c1d55401d00304103003d0410468102e01c0044142070f00f0060f0960001030900d000700b0311807440a8031020128007151243e604a41c020304460a0905103210014204401807182c030050920641c444820000b11405070021503858464940b200d9161074036560038403c040341b52405014044108a100040d0540140b0045100300d10a541d61030b905c50420308444c0c21a83c01500707600c20400c0e01000780600340d0300004000c042c0c000600e0030100703229900300c0f105080c080d00504100e203800b011821030300309a00311000d0038040c0301c02c4078140403010891000702110044425020681e4100c0340104021078002c10440070503501602096240c4560340340da102c00e0781d02100d000c4411003140e0210030f1049100f81329130000307405541390541c9154540f0b2255a5904c0410000078070841c0404040b50264240527420001002042c0090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 513694064 1250 513692814 513692821
    0x3080910110a030b09011404180501020c030304140d080a05090115060e030601120506072001050f1509150f0d02090c041d13030e03010207023f03071704030605 70
    0x5411500b169400801290400801d00002e261400419060f42c00b00008124088a82c5080102808030b0329048150b18500b1541240410800e00042000d22513140007113590303003402e2601003502204030900340b030140c000c0801003018076840000140c11140080c004203030b60315140d010900416450781d010020051807480010666000b160040541008038242c850f01c1e83d88440c1c101300b02c4c50882006200d6042071000507052030180c402c000e0750780e05200030094502c0c130440c0f4003403c4900981d07012000700504c03410000520800c0f0104942c4d035a0940741101d40d81801000c840d040c5040fa540f00b40300341904000c0841ca9140d40218024883e0021300240d030300d0034400d0b60601c1c030b54014040c40100480c4100026a08070840100b0b500810041e403500c2c0b210807082d1411541d110680307a0f1154155020044580545d07101c000d0031040c1022480340b400743c07108286110030507291100070b207100e12045007202c40390f00c0400f0090b04c031456000504102440e0f965501241144500d07000100040d00d0074090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 513695314 1250 513694064 513694091
    0xe04030f111510080619020f27040c020309030a0204050c071a07090b070b0114010302120907051906080105100201060e010b0d060f050904020d0606080d11060106080702070303080910 80
    0x3030b180281c55002c445070b4110344030a21319444560840741d100000716000010b07400141603600500a205800a80c3c50030240e482c11285d0040301712510044c0c44641503d001105464030740f2500c00141d00303034001503150030143c3d00820340b100700a14001e0301c10765507400000c1140c01c1c80e20880301c030654070841d4011010074000e40d540780079109540c0c4000042150601103601490305040341c0401d50403810301c014070303031030020b000c08e2140000d010941010b07024082e001c0004075008000740140f0480340544025401c000900030009803c10030000d00038034440c810010290440a040e056400030364404542610b400020790140140c1d900a40705a0707140000051622485800f8205409aa0310b00380181503995201d0303041c00c410750080d1540240020040b6006241004024044502c201c5000c608142e480b0502c60800c03040114800205650021404208a00f444198050211750900c4071050401400080d6200294080202400540c10110795100d50401c411001e0480f158004d00440015010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 513696564 1250 513695314 513695353
    0x7110a030201062309010e0615040803210c040902161a040b1e010b2107091701110403140708011104060f2102070f05010c080618010e04030f11 63
    0x2d8441e02c1c11094031541100c0c1c03040c0204e0381070900000c1c1044810303400d014800c043d081c400340c00158003544031400029030301e84c800701a000030901d80002d0340c0c0310076402903403582e0b074880c5984680544200004101048034904240c4007a078110440068941c111000c0c4800d40b00e0100070041d108585016405d4101540c54400c02c0c4101d21985101c14a61620164140305461107191000c1085400340184216500c59014040044004d00c01003442806104040d207062402d075442ca0024003540c13010702800c201b582d08040240c4060008112030301507641d22210a000307c0c00300a00345011141100b20450b030800c4054041c0008400800c0221400c00755502568010b114880108201c0d000301084c0701c1c0110100f00004030410014047e011024091100960003550304481101c8051801340101d20240f180804040094079181020304000c000c0240e54400703d0310000030011524014800110300c0e19039207810540c075051070780400301d20360ba0541300700d00d09801c440d03402d101c0d000740041445292034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 513697814 1250 513696564 513696569
    0x9020a0801151e0608070c02120325080f0304140706120f05091509160f03021c080f031803120a150b040521030a11010c0509130507110a03020106 64
    0x4003010302c550390b50a001c90a480350070340c101c24814040d0708000490080c1c080c164000000d00e8185441000c560001d07040038240b0200c802d10398004138a00e050380c04504282c0244140d030f8000d030421302e03c0e5075a80d588203100700344020741aa400031012400304441181903803421030610382603403070883d207401d0010042d20180c0d0145840504188489a4041a03482000d015084160280c0013941040342403400104002c0d11213806440f83c003080007500c0b09009455409030141035908410f0905c2d600400104240418590145500300a00c010002e2104001c4035500402908580d44a5440f09000409250481a8490b180c0000210001912640b20421b4480ca610b140208884884503000580011041c098081c445000304001e1140703280c0100d5009100c001d0714600c4075803245000e1454255003210500c880490b0b441d150800c8480d0080c06440e1810003d858a1070801c20402c00055500d00d00c038500d100c4407aa10f6012071803681c8110181810003801c10111030000600346402070003403801d403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 513699064 1250 513697814 513697841
    0x1020c0a090f18020f0f0609060417100e0d030c0c020d06020306041d030a050c01060909051e030f191e0e0307050a06020c01121b0309060b300109020a0801 68
    0xe03d82202144608181c414142c01030480032000d03508009002c3c011040c0b841c1594040000c0c459103400c0c2d507a5030004c00242c0b11508a04da41e40403089070451622140c1c0d0217200c0003e003042c01600901c440082e034548402c245140c003240014100b4800d0300d204044581c06500003540400507000e000b029001103000e22801e44080145610007104016a508001c40b14205600100030b1070840c01d1160b000b4014085a0100001c2d01690354240d0900300c0d010b418045615401030301900300a0040c5082c0000550103075801380d8a00340c10484115064031031508200c1c00d400f0001c4441d000305100e241e14110b103614030400480442c4018a014000b0403480ca005442445002c40c08036807070901410003030846025400500d142084d26005455544824804403562591044400398600e21440c1d005a0341c2c025442c00203da800e00c1c02e00d4030a640320450722034004c425000d0206921040340502c44502105041c3d800c00004e0650119400340545400196000c00e00c010041500c10040d1700c049840c8964 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 513700314 1250 513699064 513699071
    0x9050a06030515030d0e0d150c0c0213020c07030f052a03011a180919030e0a05030105090a060c020309091501020f0d051614100b03010b0f031b01020c0a090f 69
    0xb80f408041e51646001d00c0000054400c16120501d824001d80c52904948208000701444208040301422582181318401c001404184e001d419410024603080350100159010741c030700049451030640e9403440c1d110041c02c0c04404000741c0c041c05400e000038007124446046038559030b2038105014448a00d00c1e650140310354030b0007030b40e4015240400b40205001001802d01c00080704051960300014500410745413440c02982e001a101044203140c1d406010b1007034481e900c444032031f10244442d031034140e00424001e038075007000e100441000280a9104651004c000310b84200324450890a5010700c4981c0364000411100303018240c0110082c4404203c420381c01c0b1001d04c0406c0da5080e5a0740415031001010807002c01613112003510950003404451b004d650340b0501490210307566440c0a407204d40c0d081d120707035540e40021210b250031701035003502000448460140907a04400079865408100c035400301c104800d0040f05459009000720000c6942c000c0201141c0e0340d413503a00d240a040076600c000202c524 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 513701564 1250 513700314 513700351
    0x50f120f09100e100203090304080331080c0f0a17030904050906010e13080702090103030810050f0f130e0601150e10140c010b1306061115041209050a060305 69
    0xb96200da0b900c0460b0070340050500400a80d0f400000b03600207048120301d40402c1001044086041005100000020070300e66000800f09a1001d4025000e51103560711181441c03042000c40400103400141c42422160451940c0c038500008a140380d043d40312940d802102d841c4d2020646c40840582920070301510180105d641d5856a6611017200b405030b080d41107a10781c0401d0113200c0b0741521000c014440c456903860a03449400098048009900460000720184c00301300c144000c0709a03550007000161200701001a041000407142d00341400240e010790100800e02d101d420550f040403800302c400206a403101d503119001c2e4940c90311081e160f00b0104203098401805070070070401030083d19110782c0d1001ba6002c8004038000d22070b880564111020340d01c405a00e1a5075541d80c60122220055070740006103649042c4014254035000b04001440350820300d00c1c0030303014000d290910340c800e911100e100030003811000305031003c0340f40d604243d0300404008804074145d90954481d60040c458810024655038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 513702814 1250 513701564 513701593
    0x406150c060e21030403050c010501090506040b04090c05040222031211060708010b1b07171b060906030907092f0c0a060e190609030801060801080c01050f120f09 71
    0x3000345445483c060a00319102400e00c400409990094401d14015207083c03200240725007075071402c4e0080540c6566440510001d80341922582107d460141c2d418403249140e610340e0342c114429413046501407a0002040705888600300404040b0b04550a4480300090326401c00001500403a440200030540b11201c03810413030800074045105103070903504c40d841a03080904501c00364100d4204103411480c0403501e000d10038004c3c010740c00076010070a90041c0e04a00d004941d40ba188820703105100301a0190015881034440408840a106054403155565241d250402e4600559640880c2070f60740740103c1200d900105081112000d46d02480d58030300e1b00d44040b482d0000d88501c00711806ca90b03000d82d00503000101550840101c00c810303001602c00c240040c4001001d802d41d402400c0b85c141d5a1000c40c542019004900e0901500640c07401003003542c103280d40541e458540090035418441c012a106040d80c00b140115410700700440480070250500c01003039441d401060350445540d0265603546038051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 513704064 1250 513702814 513702823
    0x40c0e0105030703091707110d0c06050723060702430b0a1106070504080c01030b010e032b020609030a080903211b0f04030609140a03080a050604290406150c060e 71
    0x41d000083d03c000ac1e0701d03110040e10b082c3d01540c411104c5440c4107110720000c001c582d078540d011804081c09040c0c5803800d814001e013059440c0328001108042454101035a034102c000c260030450b40d070050307803c646000d00e10000480000f60b1010303451a0000070503035010769016a2810010a103441100e4290302c68141c2a01c00340514000c00700190700007024942e0940c42900f00d500e5100040c100000c2c100302036000310f41400d1b16010510f50549540d908120383d420340c0b1880c030301e1086091001d0000c60811001b681d40701c0c81400c3e154010001078401080c1c11100c2030086500c1c001030f0080d140001c0750310507000d58040e50111461054191240040e000542d09101120311001030250711514040c10741d683e40008044042c0c0540ba00c000301520005240020072140c480319000751220202c0f8a00300e815101034074002810300e40198103041c01801001c40c0a41070300c2649107131000040000d0400d2002c5802029180d2240483c1046c6420084290b0b4014008900040c01420f0904c103a40e200b110380c540c0d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 513705314 1250 513704064 513704089
    0xc07080f07150b09150a03020a09090213050f040f06020f03181504230f010c02280b010b090d0609080301140603090d0f0c080a08060f040c0e010503070309170711 71
    0x403408100c00a041d01503880d85c0d0311a070701001081e48421940b01d401103680a11035800c4202130756940c2000b80c0039031a04203400307111030f024a0014011494884195031581c0c4010b40014990503901c0d6464041100a0301070b80c01c1800d007038062039200d00c1c210075410a1320070a4150a5940d0142c404996030701c0c2c100013400c0e449660008481c1724004090321a281d09a40c01d80c41c00c400d1400b90801c41c1310700c96800c0c02840d810b04116801022202c0c0001c80c1201204050f0b0800c2500003161281e00c030020b004101d51383d0442e094a5485600c407412140801c4444100c00070040c115480c2c021384000300401b9401840c10b0724000307200e0803c541290403d000b00c51000f40c40d50725081c1e0010200d209810b21901d12240d0031001842e144401201c0e035940d604068014003000300108008030100302e40b42c00c2605100b00740d1102284c05000350b515004024160410190005042020000005008901a0300407001b09640700b0310100790440000140502608496000c88070b561245004d180303246080d0205140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 513706564 1250 513705314 513705319
    0x150601090602030c0d05091306030f021f080c07031103070605041104110904020c0c06070c091118371721031e070e01030f1808030c07080f07150b 64
    0x3840031113940252201d400440b21f25600400b42c0104240c2515a401200c0c0198402c4845a15040700c62040104050511900080403030a22140d9126030b54440180c6400c008402055030b503030842d60404031903029440d00401200c2c800040c26904001080d8003203441107008460300d8414448603801c01090b201c0c00c0221140c06013080c4100d0440c0c1c0750603802000e4180c84034040710390b40300300c00002c1212604071410540d08050419400c00891b031044c050106240700c05d81d441450050082e01c1e00441e038882001450154810b500f480d80202d00c06020308102142a20140006c02401c1044240f4046540540c109111b0788071400300c80350200080d4031001c401e403201d800102420307013480c00595410040a884422810703400901caa40c8103851000d00800242d0b40364401c0554450014017600c42e242007480c82c02d480c2032198a10b07480302444035040705621500303403540c94640034003100d0180a084405480c051001810010905024004081942c89016054403400003100e503501110700194042d42c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 513707814 1250 513706564 513706573
    0x1804050919020652020a140a050619021203040b011e1a0705060f010323030c070602070303140a050301060c061b0806010909020306060f0307050408150601090602030c 73
    0xc0c0140b800030f0250004580500303a00b41d6001c52011040d0940000224a07038600198821a0382d400d0648401c0100f64660745150080c050155408546040c1d070500c60344000101c2c4130a03000d00e0ba9200940c00c4024030008018503107908515078403078040c1c2d81004107140584584000d840c00c403100301c0292407040d504142907401584c68200c10160154038070380204034501280c0781c0494000b600c00e8201d49100680000b0039107540c011300c0e109160241c054601002c14134101c1c01000050208071340307900d102d840d003070348646441203c000140ca1402107a0b09040d00c0c0c090402d02003240c1c0da00280c041e0460780a42d5500181c000300d40c4000401d441622603580001700204018840b15004041018142d40714060004501205910109007580420005000500c4510900000750790054400014180c5641c00b1403941c1009400518284035081445080750004000282811b014000b03840c001d042c00300907940c4160b00c00c00703a444e80c2070040743d2446c085070307840354007160300c52000040da9529030f194801007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 513709064 1250 513707814 513707863
    0x1090c1e08061807021f09050c150d06090902030d0f05090f0d051024060806091e0414150f1314030d02250201080a0f06090218040509 59
    0x8079500a0001e00840e0400b00040c03015805081d08904544105081d41c041c000a5882110303180812000d64564041c190900c0308000201c0d5000c200c0d4090060b08903071000303001e136100011442031b000303010840041c01d281250000720100e158200b00e218610071411345042c0b220550081d2844803400c040c00000580c1400205800e003442c148040e0080401040d1802e1048980c0e03500b40343c0044001c0d1548910707107508240208005100c0c040d40003801102074030a070349051242c01011901d0041c5514821461000441c1101100200c403010b14a0000091500f515140c01d1500e0100a00c2007565040d2140c18104040c00c03442c1c01c0c01c0d40c0240218001140e6544501c003401c80300c0c000c40c0320140d60004000d221400340032807c000a250b00e114048004d80c81340051070904e6001d50101002c0030210f44290390b00c0c0010703a4130559682d404203550200052041100b0101c1c80101016045040d1982c40040c0004880040d05405031160724211014001a514122415203620108169299011b081d4451 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 513710314 1250 513709064 513709067
    0x309030f0201050d0c030912020c061e04090e03040e06190608070e090106031409010903090e130503070320070b03012c161701050306060d260301090c1e 67
    0x15036060051506505211550300b9100031181402c00703903000309944814035010050f168042d02c00180081c0040c107280c800750703008212036100b0302a150715403141c0e00c2030110882c028541994090130302c485003040795651500b0000c1e62640310340210f41c60711000c000025080d24203080010080200011110b101500e8400e0075a00445e02400b01320034040c080d9a64681c603190081c00c0c074000d02040d50089500c3c0340e44240c02c804940e025021000d540d041c00b860801103900304010400b154001d25000302e4568400204402d22502c620004081c0c1c08000b07030400c241940403c113806c00400c602d0000c44610740c1d903e980c1e42d07980715a00c40c020090100340010402c00c18004690036801107000d01c003c410407040d50a22114100c00c4400e940444012004038405503408854801100d0000a104a2035410324000031b6803050014480ba220700400400326007001082d20702e010b408541004240c005003405c11002c3c3c400d4009001e803091062900010341c0b41035104600d141c010740241000c3c40102d0302007960 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 513711564 1250 513710314 513710333
    0x2030106140703090b0a170c09010f02010509030714070806090303071b03020c1905030102040e010e1806011802070b180111070f080306030f06190c1416140a11030c01030504030903 79
    0x4009050203400320500710300c0b0050b12507d501c01d00d1202d400c03950b5104010005000081003d154a04580c07403d401c0020b2400004212003400f504070500c4201c00824010881c604902508403400070f000e59010b202c0064030001c0954020507480d2102048029120b070040408a4401800750040c1d1004a03054828140040011103240d0800c031070705041500d41002c6801c0e03030300550015149200c150300412600c50002801600610702004217405956410310300742d503c16040c0244080c00403074a0344280c0118180d412544010380c000b1000b2914544660b0400d6070000301c050960565023842140402c804411040380c080c81e9100b9003455000800780c41d581510740000707103c26058402c0103802d41719403004021142c0b0903400c2514203a04155a04a00c006071082d01c110f4905000541560110a00282d800e44a0f0000d1075500640c99280030700300138411008514612000b4010068200140035005400c1001e140044c0c0403244101a074a0044080311400c40e000b900040c7c0720403007440001d62128 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 513712814 1250 513711564 513711577
    0x804031d06040b12160309020d0b0c13080f1509100b03030403050a08340b13061e05150105091201091707050d020f1b0d0c06020102030106140703090b 66
    0x1c04181c1469103c50101015621001d003402d0080c55000811a1040700f418071285017180b14076080c071104405502140d11140b4460004001301c1b21000040c2c070b1060100146c410083c4003130f40002c850b5a4521506449410040021406018824044007004da503403221b24090102c46009000d602c03100d5010340d004220040d2440d505000400c000008900c08000116101e4094040a0b0b82d50b1807520100c0115000b00c0d200c80794417014140c41c6005401c801c0c0c80686042d410a0000a01b9581c4001c0140c14881c8408000d114900d041140b9030711130000190034081c004d21420800280d00d8071045460800b0301c44982070300240e0100180c04160030401c034200c1c1d40c501c4220000ca19041c00f41d550401884040040040308000802c1d1002400810000d030106c0c01c1c03040c00a05011003042c081241c480c2c4980590000f0504103c0c0015125201d03132001251545d000b44185007916182c54000303000c0e600038030400d070001c0c05000c210440040e03a50308031040c2c0c5505494081d016072610740300507280e40010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 513714064 1250 513712814 513712819
    0x6040915030507031406091605090601120908190504050a05121507020610050f03070e15090c070201030509070605071b09020c0106170307080324150304120804031d 72
    0x19000000940100030303c0c40618071441c0d4068554001e510039900d0990000e040601a50103200d0790403004010302580400d07182d00340c40140c69a40d4040060f901102620a2040240e2815100100344102030300501000f581c0c444180c1918941c03014121428056030260cd80c0c0300052810401451500d045010304002c2d2620541d101d0400e0000030089640381101d290340540c1001d010000560798506084000d000119030040308100380d50080b950b6101c580c0144d50002d40c0c0403020580020400070850882c2000a0030b0b54902e01c1d041703c4424241d000080c2c01c9001c00d0030000850804e100100700303102a03510a607111800d00c105a25002070a00c400011548280b0704c5030808540c1d40d503540024030401081f9800802d616240ca000303e80e618401824060203134000740b0502c4001541d94080341e401c2004d920b1030000220420002903541010104010350004004143d14004c001003009940724600a16000c07114010240054800c0181203c00034005094003c0c006042150414503044002c0302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 513715314 1250 513714064 513714101
    0x50c07150c0c080a080103030210020a050a030f0e01110909060301020304150513062408060603100929011404020403030819060e07020114090a020a12031b060207030f0e060409 77
    0x107a443d00d5280d41c1c4180c01007030000724101c006205158040000b0443d00c00320103400c510700305070507000600f03a0244151040c10551561540c9240d0001d54211031580428a4000c208108980d2503c81085d48034500302401510b0000c00280c85103030601c2a40c0c0304c2c035000158200c07003014420f56000203000080801c021a10444d80e80c0b03022442611488a00503031040c000c0e0701c46100f081c91181c0303191196010010a40c058401c012040d00d0216036122400d202c400007091034202c0d442d011179150002469000441c500300d42c91154035041e0405a4101d4614101c61328142d051402800300b83c0c81140030113404181480d002c00c016901102040c5c508030341031000058002e494119081030b40308291440d0005030b440b400c140e01c40045004c0401d07048100c8000030103007600b0f540e0100fa6800101d22801102081700c41c419004d15000750351a011000b0349018080e11000d0910f480f0000b90070860341900090a0921180315560080c00e2180903040010b20031401c09146c89215400b603c141d12488015044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 513716564 1250 513715314 513715337
    0x31305150706140702010b0a0501021e030d050c0a0906030b030a141e1c2610270c0c030905090601030609090c0504050708070f0810180906050c07150c 66
    0xc0b50b01c15420b80075072a0002c0c0703490742010b940003030030764094201c481d100300c40d107a400b040702e682c0014100d1a400310a000300614020030801050440c021660400560b6081c58100071902c21200700508404020b500c402020381e80b142d10031001c076200000c816400d5400302060601003458290480201c0a200c41200c100f50f1400b40d15a08141c2101040c03d829031000e840e9080d80a8070b9511200c240060385420010700e8001024881c4004c01041583c078480d00d04030214001240c101c0da448003a0540352040d00b00314046020061070107040c1040804074603c1c0550002c2602d115044035080303280c1660b5140240c0e0305101c20004500000750000781410f0b074030500028420602d0090301c0c0814000c0540184403442c1005000540d10010910004c0002410400c040150005d8500c1c16001040c43c2c05c50103903480c038850300844083c80d005440036903081080540c098605400441000f44904028809616000c000070594001c100c0700802000c401c81c60701584940a900c58065000d1510b0004164070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 513717814 1250 513716564 513716573
    0x301080607140d0c170108030a050706090f0b07090302090a0e0c010e010e03070b0405030c0102060103020d08030a110d090c080d0c080d141e0f06100818030a030605120313051507 78
    0x401e0344016901048600703640411011541405d940100041d0010354078103003200b01d0080c03984c49080801001c2039a241301c040f0600800b002e40350003040e4070228414003414401c001070100c000a12080b4490100c00000400c420020700a411490f901c210060041c200701c04015211030314509042d9040008104511324180d4081105400030300300e947c0141d5446061400707045c01c144510b083c25056501180c010001a11025030360302c1000d820011440c2c03070703846000058000e0120000400d145510103c2c102c07030100601d600c0213004620a030b017048000c1b0755950455884402d05400f40000c43d402072400c50204200d06d0013801202c1c0150000501c2d403492080d031125401007030b078050b140102d543c00f640c40301c00c50614401c0c0d0003c00141c07280344207242c448001006130f014465010100f040140c04070b8852403131840e000b61440b250109032a100c542c2d48034010001d000501c94548103511940c0900a401c0000c0101d800152719444103840c1c1c0c4c0d041109010900b0f0317445030140203100301045a0720205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 513719064 1250 513717814 513717821
    0x1080304090f1830030207050c0405060123130e07030f0e0c06070303020f0412020102121c0902040231060507021011070f0902070b0c0306030705040e0a0f0c05150301080607140d 78
    0x64441d030305c0042c4c40c1c5c0300c1800c01610f040300c8484454080d034602014000c0c0c681e00514001c02c0240583d90345440300040121402c154001e10b02241c00400401c8008207000b80b00c2c4240d18411509640c0801140500226110a86400a1a1300403e80000a541c4024100030009040c1d10740241030141c1340c039907003d8902249a100d039203c1450318043c1c0d1401011036034144401c15000541c82841428141a00300d0011b52820b0758601941d016954401c5804540301d0360192226041946800f10a0011101e0031075800b8136a0411905020803016021541a0084056400300fa80142194070f08081595017502c1c05054403940e0000e500c0b5851000403103091400700384002c0c110013540561140c0f031600c0e18090000c40070308454403400c01801000a20348000507000c040760300031a4007044450100d5419410b100074070002a1004081007400310a010b80411010105c41041c0e8080d04940304000c03003040036001c01c0c0900c181941004021400040c03184050b814040304d0218000d00c1d0030214000c9034101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 513720314 1250 513719064 513719153
    0x1030507052118060f0114010c05010903090302030105060406060c060b0a2606010b04140f060d020c03040f0503010504020109170c060403060e0c040b06070f080d0501080304090f18 79
    0x6034180c01c0c01c0041070710010943e120300c1000d0100600441c10006a03410901205002d8112104c0d15101d100d203542c1e100307250f1804240d4002000b0403500503a4140108003140b240001c2c0d0003507037020013044260410b4403801c01107421965981e4a004103d540b0704000d0001400c6069000b000d208010504410405200685035000040c0b03500a00c4444170043c01c03c030050340001500e82c2c090002b003020b0341e801114041c0555080710200c0441410b0340001c2d02d0f5000351110714400c0c138404651080740c40340c000000c009980080550000711542c96082509a078004c580003400641800070421030381400703140f000458007203541516203840c5d40b8808940641c00941c000c3ea00141c56500b5020940d40901113489028810f4a003030100d44080c030007182c250b1090800050914220212150611011406440d0020400d480a202d9941e45070161581d942043c01a101442d151034483c0c0d003060717050700c244031b10342d000a4504940303a40c2d903484150109407080c114102c00d40030107086403084031498410a08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 513721564 1250 513720314 513720367
    0x4030b0c0a08060414040f141b0414012403090f0b16230c0a020310090b0106031a09071710150c0b010e04050307050105040602071707110103050705 65
    0x7214003000100906403000541914010792401208980342c40ba04107156905c69041a40e406200e085480d0000340021082070007011406501500d400a88990a880750b180350301304d4040c010302c0c0b100c99605045580030311400c0c101d124051030060811001e480310f0b0100d180700d03080000780c0769155103d111110500c450115021030007802004004940305404404249051405400c2d000300b181c8c007911444040e15065507000008600403e280104000c04c000c50369010302038880c00e00c03c0c02400c40281050708011200d600e00c100003c100326129204445c902044802100d0484a84609114000c0e80c082c4c4410100b250080d03405403401d001781c003e2070203840720800d20706102d89000810038141d02010508400c0204044078200428200981c040c103542c1d040c1c203203187c1900c440ca0060315500c030300680142194204810032041c42410750107000e171540544407000b0311b08141822000035100c2c2c00d01c002c041c400344180d5444654401d501c143d80c01915800d145141204811030484218003d6001c0d07070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 513722814 1250 513721564 513721567
    0x91507060203100f0e04020d03200a05060708160504050f010306051206070f0314010915120302160506040513090c05221b230706020a020615030d12090804030b0c 71
    0x103c210021042c004100e1038541700344c2414940e0003c1c80500744000003400f002200c400082003c40d2016007040014090011207400958610b001512000c0403522103001c5802d04001030b441c45042103100c0d44412055a42e20b16190074107041211240e0701c80700890400d541c803603000c00d0f96210b502d42c02c00c031400600d005000da0300e8003120003850180c9080c0c1501c101801d0940107440310702525800740c1512002040854241c120000c10443c01100d9402101c0c40981ea2400c0d605268000c600382400b00000090358038460f440d031040c41302500c254458030340c00000b040300d54035498610f640004440e9208414481c01c1580e590005070101d502a800006410340021220028030042c1c86800e246000d00714043c0b01d200402d180160100c1c0060090b4008500090854580441e4107022201c0444c2e1141c011500c58508e004001d68525007100c4003000881c0d4400c900d0310350f190008914004a01c99990100c0c40211520504050010389004660001c1c09100c003000046030021110b10407040f210046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 513724064 1250 513722814 513722819
    0x1506030c0706061a070b0a0e010c080106020105060117010e0613060f09050a05220516090b030c010207030b1b0c0307050303190b0102070306110c060f1006050f09150706020310 77
    0xd40c21102e8a6000100c141514446104c1001c0360300255800c0d150441c030b24a91681d5030304c014401808441c3c4108049502c0c3c00c2100208540225110f4103039443c030b90007041240d55000040d0380050640c2c4e0640d0701c941c5110b00400c140c06c41107481c65481a0003030b00f040c0082d641154154107441c2c036500090300c01403d5640c14070034030806110f803560019062000340300901300302180d1288219100c0b43c1c1c10035840303405001401e200b410494a024813040503a000c1025541e4090100149000d415991081c014520950015840082e4a40589400c0515054262620064544032070684da6203218030343e1303080c014280c500000303001405a540c014400380d9601e2a02c203805a2803102e02040340741c0344c0d41c9081c00560644c3d900051075801e42e5400030000901554220b4000c126008451685060748030b00b80030031140035010f022007400382d4031460b9112012502c500096605002e4046503290000092194803220301c1c4c68407817112001d410507040c03403609401d0380300c40c0300381d078803c0320480e103023010480c000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 513725314 1250 513724064 513724073
    0x10030c11061302040b0105041205030403021314070f0e0a03080c0724050901092303100b01210e03121006050a021b03011b082508040303051506030c07 66
    0x40d00c44500030140080c0c1c9442810b030101c2403800b82020340541e54405001803d81d0041d81210050080d202c40c4440000c801d00d0013503030740d40c45408124001c042c10510403140c0c88a601071020000746d40352119040d075640d003004441c4144c9820b8444200100d05d60401680e03200d1250080240d400f500240380d1311440300300d03402c6c5480e00d107520100044455940581e80ea4410500c02c49c036140c01c505c1c1075030f96040000d00481d41d60041d50014240207440800320709101000360000040031000340c0686291814801c7c51030300300c85180c2d81e40d90100e07131401d59010348003890782c141d1300320500e10410024111a446842603c1e6411200d5001030181c400d1003401005113000000360700411403464202d1030640c0140d0b000351034400781c141010880b1481e0219013440e41d002e40140ba080c0c10b102c0c144d1200e4144540300146840001d036a2028071100703800328801c18005105075032480903d207880341d035010f80300c6903402c5000702801488940940d07031903100d040c407643e01d803002540211210030f09030b40c60f821241030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 513726564 1250 513725314 513725327
    0x309150c1603020612100504060e07030609110703260f0907080706171009050c04090b0a030206090108040305130f030b071d0114040503070f15020c03030304060b0102010b10030c 78
    0x901c0e901c98503075604000603136a040071206000040c2c051a13a5a84503100d02c41c500894580010381d2103800e08002085246080780c11911864595509101159845110908550b540204c03190aa0b00401285d00400d000718403484040c6502805018101030501c244018200d0903a040224416001e0a110350508100000c02c0500030040140644a19014024010301c0003c410400c0074120380002450080d04c180000b0b00522501c0800c0c401440e182d00c0e0101107501c9402070312852860503015469600b0440e111340262030340640b42501c1c0107a13800055491880080085081060400084800009000d41000182440d01b031003040e40741149081240408000e1041d000c001c000014041c001c5450491050004000e09025049480c08180b0b03445910581c2c01050305032040080011f1042c24524441003150800340b03850700304105404007207855690011049a1642c81032000c2000708441d40d0010031507407014000020010300c11000b04940b00804c1d90004082540d6002c03488400d9003148 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 513727814 1250 513726564 513726583
    0x608071505120103020f0102030c100b0102070803120a0222060f0818120a02100509060a0e0703120e0402090d03020a05010506030f06190e1b10090b1204050309150c 72
    0x8141d03090012260721118a0441480f01911a20703a19030901c9480c4d0003401112040c1e590382c1c1c1501c8560f031800410300c020740711112900d40181320b8800001000b52000c01a920307031840a100360201501c50b441d8540c083d400c03402200546408214040c00100c000b034120b14001e041c0da403507581d41c00740d1208001d4251080201506085400607241507129035002c01c00d0407180b5440c181a545078182604100d01c1c0590120310500c0c20b03481c000600c540340c500082d150b84142d1041406010249610340350646803007051000509003000303140030850b80c6002e260008a180d001900040c141111540020070354689404180c0c00b41e0404202d0b10309000c004e014030755100030154010411004805902c0da81d810000344034495808500314020b01800784c54214040414401084031a540c40030000e6100e1481c88038441c42c82042c00c6450803031424003030161903040311003218440781010072281040018000c0100115201e000401c6101c040d90340303040700340c9040d0900800b01078851111040c450b2034030840b203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 513729064 1250 513727814 513727817
    0xa05090c0a2d0c0c060f0215190c03050a0e011118030102072a082803090b0a03060302180f06060a14071a06011d121006080715 56
    0x11042104000184003151400c400910b850080c00c0141104203800d518070824841c0b500d001c08118a1425a0003030800100c9402101410192a95200103039940280021010302580150030042e40d4511691440d17907010b0359805540402409160300f4104407240b43c1c141c1c0002ca590f81c001d100d44111184903100561180300001c1000b43c05440a0054074000c100f4903400a188820804203262003c1d01a1501d0f281c4c0b2080010929210f40d2110103e41280001351240c0c00b001500001e61800005100070441003540d55a410074150b1103001c108901640000d40034091107520020b0b001e01b5210080c201c10049940000319a8110f1040042c40c11084004c91510303449501404094004084100c2c2c01c54412101c042e07032400d11001c00d83c0c10140e0300c1d045c0c504620004c69030310180f0070310051201d00314001981401c141e941d0500103550645480e20301c610010071110000071181410312903040070030030f40000c030354003d48005054826585207404c4035032180c000640400c2030f00a070003662074440015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 513730314 1250 513729064 513729079
    0x22090602191403060402090d0503040611060c070b01060c05011b052205181f09140601020607021f02090a03050a020a0f03151503201c0201140901021f05060a05 70
    0x11002c0c21016010180c01c15104590010b041301d0b0690750301c000180d002d030b0b009065a0322907a07a81c402030305030b15044003512074a009000005100c140c0d42421914080e80c440c0c407000640c0d080c54821a28075400300340c1200c0944d81c43c051126041034a81a81d94035540540d10180d450074035258600380844a00d10f2801c03c20b12200040c4542d0381c0d922408031120035580140c0c10150381e400c3c400800c0d00c900c1900210300d115600d8001c601900e19800c04031a00c0f050305280d8115480300401241c4e16002201d602c0c0042c0c0203c09603d1819512151805003440070690140c280307030900740002e02100f9240c3c011034143e0b100d02032100460a120840c1c8000f00030070080e2405035440c640b2040b400080340d241008541d5501c03000f0f000040e800107004005940c20041d854005040e00c00c1091094003480c0710300d84200760340091586e20801e1000300980d1103606a4500702d1f001118030307001c0c80d01e800410180e03056000f0000c0b0600404042c520b100c203100072203900820707181480414404035804903004640038001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 513731564 1250 513730314 513730337
    0x70b0907081b060a180e0105011409010c030e030c04060b0915040e040303090507180209180c09060306180403020303040b0703020f0f07022b050601050f0306062209060219 75
    0x2d034005112070302202a41c2c000e5031251000c0c41101c00d20000390003210442950040441c1d0a440205460b06941083e01e44280c90003030800d4480b8039005115055000844d07611a41000034403507047c80361400f0000e8110340e80107840500040554a140c0c014180324040030440c03e4281c54844c3c9070f29040c140b813412181c03610b03051003001011344400600283c207264440d4540c0e0100841000f41c035004000c140e80e603030038801d06d1060100103035000d0a000c0344075012034010b10b10200303411051140140c0c40c528a4601c0c01190740c00340501900028107441c0c1c40041d0315159150040480030961080d440707a0f000c0c6541c2c0c82c01c0d140a4120007006400c0e01e04051040c4842903454940c0c00071a03070200e80c410745954840171184002407a021020414a022070710111088134990300b02d12519100a210750140ca18603030321001407152160b10341002c154581e202a001c02d425003480d1400140c0c0d800b9000446c213168840c050010103807071a0000c1201c2e6140d0001d10068450480b100c0301101903914980131980c83d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 513732814 1250 513731564 513731593
    0xb060904050c0910030803190e062202060705030d090c1a0301060c11040f06320d050a060903050a0314090d0e0a080a050709060b0f121506070b090708 66
    0x4030341030f02494002001c50210b0440004100095034003400c0c2a82d645030403240406107400d442d0a0510103030030440404207000b030118010f446080c80310503204052002078001c00458115100682c1c0081042145101085050008040c0075010b600b010a1a90703141c503007602180c030a64080d8041000000300256074403007400440e0704590b21440c192100c40740c01e003050303014410300c1e101d850f6026140c090a41455021604118225200b9480b45440c41c02d5111503000c841c0c0c0d00441c05a903c0807404540003075880c01c20341000c0c900380114101c0700d413032800b903a90342c0458041136400d901196000c540115495418065a81400307613011b4800b60340d0910b184120342c2d40d4030032280401440042c80d08007035661202e500440040000b401190340103030007424016120303802401a8804182484008107040c111507003207464010085c8052440d040d00e01e08406500706000d0b01c030754860f00c05101321008984d40d4101510005010b19108c843d10705010803114601000d07075004498075042281801c1040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 513734064 1250 513732814 513732823
    0x60e040f110d050d03051e0709051009081c05070f0c030b06180609220602040e010e10030b0a15090b010e1e04050c090405010303050309010b03151f0e01080a0b06090405 74
    0x5134124100401c00d81c0724000f08103803041400101e40b440040c54402c0200c916440803030501160002e5035101200e03001d14000f107894510034083c0401d070b5809800f40c020000c13860004212442070620b46103080008560f1407107490100041c080c1d40700b11540c5e03001d209016038144103a80040044030b410221411000e072060700203000801140c031070520a80000c00d02c0c0c6440c808028080c5101e074001075808118504040250094050b580c10b404409001040030203072611150f00980d0701401e060039030b40c41c6644003a00104004c0800aa103500c0d4240080300e030034500d00c25005042c0103040403405d000c4040005000b082c00c1a1040d118a81c0a801e032100d031008600c580c414580c081c0c802040c2503440140b00700842c03180041d0b081d0414500300001080c150b00c030000e140541406402400100001800c01da81d8600400c2c0c41e80c60110350101240c000140304040000c509031114200080c99503031404494280400d900090460700300c450704004021080800c1d542c0110304840c8006103050589850303944 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 513735314 1250 513734064 513734083
    0x300901080a09110402031e060409050309060705070b0316020c0922020d0f11120601030b0115120e010209100c050601090207050a06180308070804120e04060e040f110d05 74
    0x4265440440000f480240d0800c031480483c0500107665070704144608400249520001000c4c2c129800080340c800e140074015001c003203812400660a04600200300500c903030000004a49501c1540c200240c8171300342002942c23140481150300e600d100c0207640c0280c00c00a20b650f600e0300c11070114003000503155005001800c50032400c0600380000c800b44c40410001540c0e41c00142403815060150010024080c601800e140029100c411722038030601406a504c0304207000040040c19108018801c86c0f1118468255004052402c0c806031810b903600d50040300d248038030b00c80341650001043c4055007801e800b05268000b080c42d005140c040c0700e45816856000601070785da205a0000b4000003804801c01c6003000d11074120070308000341c01e05985560030345c1808210403004547c101000425071401080c40601c2550455011400b01841c03070fa044401d40040800298000d503140f60204282030a0704115200b2441503405800d20842401c0209955405200b120311402007002c64900150020541581 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 513736564 1250 513735314 513735331
    0xa0c1a0a0f2a080d0606050f07060207020d0b130606060908030904020d0b120604200d0609020102120c03091309020d2d150e0c030703081b30090108 65
    0x1800c1c2d07003100805049200300710490074002c008000360b006001c41c040c01090041c140003810094240d580364141c8003400380b000307402c0c0784070f8017400108040350964004240041c4020650b240c101c10a607103407160b21200743c40004640800411810404c5018490302028000703508012408a01d04402d403030380c0e84035100407140232b1500450aa030130b070942a08000b00114000780420071406961103d155208012074084d03c0703020300d0304c52580003044501d00c84540d00001800341c0700c00800319142c070b402038405a03c8c101d045102c2c041d0350415002c58440a04200225800503603969049401080903e1015225101040c0e1401410030010390381d03403401041c4c2d035500c8801ea1800320403040d0607041d50341d02d00031201340301c04464500c071007002107440e031104100c2d44450007000315002c110303515651800c000f07041981551142d0300a1004c1000b00d40070f8503100401c04a945404110340038041d04180d40c4a000d03022405544000316820804100710309040a01d101000c0d0615002d240024000c04c4090940c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 513737814 1250 513736564 513736577
    0x105090d120b04060602031e09010507060e120f0a110606030723030114370209040b04020c010c0807050a140702040e0a030e0a05040612230a0c1a0a0f 66
    0x200c42091508221102c080041040065a0b5107050180d01d0380e00040341070f0403c44000360b20894886103401070b10b80445041e07484a0034401a070b50303040028201803070001120301c5000d1918030341d072100000500846403105800c5440303201c0210f01400550b000c082811580d00b03c7d6081217511b440006003201200d010742403441c0341c40c648122210b00c060b4400822a055403c1c031030140111200c20007080c1c06190012040c0344642004980c0101d41300c0200d0328005034911404225a401c000d540103031038000002000002d107080c0110000e02283d100b400c040b13006944903417000782810b8101d4102c9174410a503007449403802c03114010040020b00c0f0104010341034413012540d80290340f1168484200d95400e8400c46000c100e003424040e0800c004814894450b52000344c0c00300d81402c05008404c1120200d9a80e5154a00d86e541c0d00800d0022680020458115108072004503a900300104504107000d000300160044c1444011528903101c18030b010200754080101d03880d46a40840500c0c290881c610740721 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 513739064 1250 513737814 513737837
    0x1050f0703020a17040605010e010602030702010903172502100c0c05090c0903010509010e190201230c071d0c04210c091a0f1f1805040e0d110105090d 66
    0x541e0107036041c1303120030b5240b028807040100708081a03000d40e05036100c0340180d807034980c0d032101d04990b68450540004c1c0068640c4c581000014054960030350304c003d25044060501e100c540c101941c0443c00100c142d004905050110154209030b003442681c651140740016000102d40c03135001c68805c42d481650b0284000d6000140107170918800d456075018020001c0c0810700300000b52901030016107000300110300804808a582d1001110300b0441d450b07040e15118001c241e01180100c484c2402c45109050714020042c04180130010301100000d4015070613611132454100c800600008001070001062440801040c003401d60b0000350855080601c014008194030540307401042c1003642d40c41142110708011742c1ca80230b403907141400c602d190010b807031401a403a8808100851001180c40685e885000049003130700780352154500c403d541d0110007a40020643c0e07080414101c52450084407800c0c0c10055980364500d0f8084d442d08480307114640203019500304211955207414480200d5810320403020b590 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 513740314 1250 513739064 513739067
    0x12040201140d0203042a061101060519090501060305010b0f0a020f03030112020906060a1b0c03050706050d05061e0d02121c0f051c0b0105071506090e01050f0703020a 73
    0x41c012485007071591107070405080c600294009550440e03094000450f00c403518080406069106002110030440452403d17209888080180c08a83c50954a03840c1c00324040d10f13400000784440c84480019402117240c041030350200c481c180c0180c420107040000400c21550b20009690b8600c2442131038950b1004006416842c284155103685003030b0101000028032030010000e09841301e8000d6038500a0f070f6507013a0800803d4031a00300c094005c101e0405100305aa07400f101192080b40c800d60117070311119129110207280920a52280d4000359000078000d407000041c1c001e554201405032122450141c0c448520801161031441c014043c42d441036610082d5903c6e03803c007040c21307018481503807102c01c02102d1141924903d0071b0007001040c0d00c0c840050403c4d00c98812210103003c107001c04826400d40300c003000e0260440b4840320333040000500141c0e0110350344100101035884684030000f0581d252248100543d60b401e145001564035001c1000720203800508403992180c01d0740790069445124180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 513741564 1250 513740314 513740327
    0xf020126010f0503010b03031303030309050a1a070f0e13050c040e0a05061c0c03080307030f050a05060a05040917030a1104092301030f0212190303090605010f0b12040201 75
    0x1003240c15503844000007581807182c584002c00e40e041900248004201d02003456640e2140103c485070a025428081000ca84203900c4610b0003071143c0c01340d4000c00c8580d114503070200580b02218032103400d03d00500c10441d0f000540b0003001c0495090800b01c0200010015101c00c100d04400c1c021a501c85000401c0580e00070100c8001c2c0070021041500c40c00d240c05058010101250b03118003c284002c40300f80c00f040b20b0031042e4880c65004080e10140350440d99040e0301d50300003400b98014940c513503048a170070003c14020248240084500081c0300d141000811580205c1580b08a00072460121031802090761502405040310104078000d950751600251080100050078005c0c0c60745801280209a106080e000b911000031140000488401c00e8220600854420b100c02400941280c60100060800e00040a1a69407103002c1d12401c1807100d10380581e6440010088001a582d10704000c01c005036840307668090b0130ba44405682c1241800303000340062190100340a55010701d0380001d004c5a12840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 513742814 1250 513741564 513741617
    0x7030c0e0619050f0d0204030b0a050f040f020114070f0b061009141906120501150f030b030c0907020304030203060907060903021c020406260d0806040b0301150e0f010f030f0201 78
    0x211007a501d07160705d0b044100030b400078081240c042a8500205024105500829002e0000714030f0500254480b90360300c040804d111101241800a1182741050303001088018010240c0950304c0c44410603442d240c581c0440ca8010f03c601e01c11103245100102d11640700c00520207607606041122452101c070390000e03002440352080f10b07402c66218400850140d500258240b50b915540d2024041039072940440c18288842c080e40703500003003000a40141c201e02c0703500141006131000e0203555100d07041c10f0100300582c03c210f840c1c07405613000080400c21400c080041a40c000d6200001d004141d0804800910000741e51101a10565010702207910140e403d070125604245c2c0240100070b840e41d660303050809010085052001500d400011b001d40d00307004540200c02c04d14a60b030300c41c01131351180c003000010900545400d405640e1a4420b684c00f0b101440400d0141007038403007180b800e280c00c80030b800780d1700016008080480d08c0c0610400c00036494a0349006041c0c1d0909001d800c9100c0ca1010b505610f0340b42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 513744064 1250 513742814 513742837
    0x27030105040302030a140f09040c1b12020d08270304090e0c0a05010c0b04140a05070e061f3510090e0a081608090d0b07030c0e061905 59
    0x184030405800000420b0b80241740c2d180c10881c0400b089569149001c1e40c003003aa81d01c1c81c1045040390b18542030b40489103404841c1090082c01c1e950b8001e000350158a00c1040b1074071201400c3d11a01c040e0100640b401600d0742d49014091850020040703d00c00f82014200d501036100f40c00000c010442c14404d65024007440380c1e041000d01c64640505540c0d040310b0b03945c0c2b401400e003008081820351041402c038070f10580180300911282c03120b50360101c10365400e8002d801e00380500c84150000800a001e078400074054444001078a003041c1e070070070621105503410403a5000300d6090542d101e40d008000c81c1c01f6100d0250f00041000b180505141c0184424005c031100300b10401c0070404000030b9007400c43d0950b02507542c100000d9003100d861a03611403403c0780140c03030640c0074031034082d040f804100f05540b00ca20408810b42000f00e01d90214a1b101000181200c00440c0102045204c1e40c1c94411010003d442e0314110215183c03503008140d85200d40518042400d181090800c1c07040d003d001200c000c0c203002c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 513745314 1250 513744064 513744071
    0x2030a080a020a030807090605030f04030207120605060f040c0c15090b0408120108030f1c1116050609010b010c02060c0a120302040f0b0a1704050a06060f05040c080705270301 77
    0x207052009450301c151140441c04120000003107409144a40e000308142c81e2030f91a41d070b00d035031900c4c000240c40f0240144110f085100b0482c2c041496594031095008042c400c03400890a824120208284030180703865160046242108c00e0755490f60006c007148840d50420408620718a45410240151070000005400072118406000c01c06c05410000d1000c000441b858229590720741010b2034491281402042c0c200109000b41d203030ba0021001d200d5580d101d00e800028038082c507280920110703003151484103506964002c2c40d01c24824107009036640003004000230803500802600113058540c8000c2c020b405000c01042c81185010301300400c407000d0360441070301d107403d0201183c001c0c06540540103114070107594000005003004120151448803065449100c03490304a025540c0f450310780104251084d115204030940440d0441c40395001601160148003c4181046d040c4000e5400030b4101008010700780c81004481c07640502036a1b95604100d031003525030720502c40c00d12500030801c81015815481c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 513746564 1250 513745314 513745327
    0x927081218060a1a012006070e0a0b0f0d09050115091a0d020f19090203130606061803110102010f050c0a090b040807151e03060303140906090d02030a08 67
    0x61541c00200c442030030340c04031080d9075144a201400d58a000d844900c0d000c0c0c4034035400f107596010b00141e0801c40c243d8442c211081c4841543c81d85481002e481d0440804c080000b68032050924220103006090b044504900e01310500038402c00c50310420401c0b0300c0c01540e460220080260079006003540c0d6182c50040c480582d1600d186a0013000054010f44240e2018121b00d041414000035042e0400d40080501c2c0d0040c00100910500d40c141d0143e9008582c1d41d040085045030035403000e180500501500c6007014081481c02008032403942d089241801802d44101c0e102806208803401603e6200c0d079a40c50079907541c00141e000d4480505125252402d007010000101081c001071b203c10b14a50751500606695666885502c1c4118024513031240c0000005110740802282d1344161000c0c03074038084800d0603520305c0c41c0350313103140081c0c80200080d296030080050550142c042c01c550000601164074000c42000002e0103441514003450081004e48800f4040d907406112030101f076500a00b08a81c0c80c0c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 513747814 1250 513746564 513746581
    0xf020c1506040f06080a0803070905210105010e0f1f050d141b030d030e0a0f0b04140d0219020604050a0e010906090b010801030201230c03040602010609270812 70
    0xd20464601d8000c918040c03c9140d18a154002d01040720029406450b2034103032501c0341d030001c0d800140440705200450800117903c1d101c01a24861001a011985a61104034505c4909488060740305c420340d941c0020501150102409226030044002001040d201c280c039008070b41e012040380e116680c42401c88166009010b030030a10032103140000c1d42070364a60b400340454007248070340c0c68414540560003079284244e080c1c00b907031007002020404011220146030554036008002810001100c05c602c07690305100c100140a4000492001d20384c028200301c26084038000e64a400c18642c0c6040f050408172100c00b55100c201c1111302500d0013400c1c0e01403d54403204c131130b4001d0000f03110f000c8030945007400004058140788168910340320140d4a480300ac3e4656001101d040040d800e0641e07043e0305801403072182c291070a006240030a02c0f50061525140f5100019003162100d5105502c070740d04200c501b154054184c04c1414031b0725003d02c0c2c13108504140c0c0c1401a0680502c0403c402900120002c1c028502c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 513749064 1250 513747814 513747853
    0xe06091e090f12040f0e092109180903090103021803010f090201110c09010902030903162612011502120a02031305271306150305190b06040f020c 64
    0xc400c00c42c11980401c07800c201548641c481c40c8503000c030a100d00e5000f03111240c405160543c000103004200e8032050b0b65541005121840b08622102800c0e00081100b0703d0700300349090002805602c154081d462a046071240e40328403556070703c1c6040582c00120041072400c0f119000b5800172014008000c00a42070004400030104d080c8140c1c080b5803d02e90b00050350900080808081c24043c3c081e0b203269103071000c2103029400143c65160207000034040c4810003148030b220151001d000311100e68080d8a62602d01904807507004184065001c2000011320b02e601c5029064116084508c0034207003195041000ca050210140c2c100760b446400040225407035900101400340208448854407100740e6401c1007040c0c440000c01c000c030803003408010040f80002006010f40d4800404a260304540b00d2a079503079812100704041051354210220170501c1408000c201d9400310062001d502c0d00701242c00d803508001020014080c0e0b20598481c0320b0b0300032540094050b641d01c0c0312010112071903a008400c012820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 513750314 1250 513749064 513749083
    0xb07050c0106210302120307091208071b14060403050a08090d1403040e0f01050310050601180801150902070b2e0b120702030405100e061312060c08010e06091e09 71
    0x41c41006c60400c4140d07900000c0701e0003040c4907200d212a00785002e442604180c45080c4c03c3c1c2d6030a105102c80e4002c1202d6886040040c02111103104142e401e1012214002c40015080e0b8041d007401d10090000510000301d0300401500a00340a40f80d0340081e0000300d469500c6880100380010080302540075400001c05441a1103003007024801507503d001900d020b0702000d103d190b500d544501281f403010301d01580002c0d0802c03030600d4116202d00d0080c00c0c00010140300d0380a07124582d504d078100b00c24480d002c00010040c156401056141c80825125101296409081500d100c08510115200c010340d82c00c0c0400c61214000f44109040c3e82d03880303a40001e030082d0308400301d400c05240001d802540301100302c409881008107028104c1c00e05480c2164039400c1d00c45600e8108400308403d081407140000050020010007013840f8100c0041c1c44d100c003e489050500c0c1d018012035800500c24042038030507007684028107581d544403965500e44650a59400303485030300705150010b0140019000f0105942d1503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 513751564 1250 513750314 513750317
    0x1209010603050a081908070e090411060310050306010f050d08031e0f071d030601140a1706060a06030504080a030f090b07180b07050c0103020c0703170a080901090b07050c01062103 79
    0x117043c080460305549001080300c0e03940001d440c2c1140c2d26400d1502d8564290001d006541d802c0345d1040380004a08140d00c2600c400d240e06880c11001c01c0140b404001c00c0740504000c0002e5401203142ca40410b4514030000c42c002d00410000c00003a0302c52202168605080343eaa4185015038201040c0039122440d064840e42e0010382000c004043c00c503504901240c0340500600100b1703580c1c0c07074041c10b407400502d500002640405440b0000034205400d401c03103003000c400300c40603149a0031b000040010b245569805001414284810400494103d41c1a81e09031895410041030382c814860b0010000d0002c5ea030700070584803000080c8180150701501d03100700d0b6102500068000d036101e200400c41c500440d42c0c000e2040d030028800030100e51023900584001c0260fa000c62704416101d643c0c50f12180107482c91101c000001003002c115055120400c1d0b40c001881200820060700390792a001d50080c1d00510503000e000700003440b0490a102588184014044d0040110941d840c150110000c0391540304203a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 513752814 1250 513751564 513751597
    0x415170102040b181309032a11010333080c1903060f0612050a03080105031614180c0306150c0a0b15130614010e09150a0906080616020606061209010603050a08 70
    0x515525051501020f0140c0000101c061504270000440103040040200400452046e42d040c1e4045070280c800984514105000c8240c0307400c0c520128903102c5400d10551045003007980d40c40840b0303480c42c50001600d402010104100680c02c3c0900007801c1d86030302190341024801e055500380140814499075072840b80c0e681c80c04503680c490070191365288640c081c0814190001040041032203414504443c82000b40a030303088042c02c80100760540d04200c0b0f00b00d000341c40010402c00b40349003c50800092040e40c0c1e0740c0c5424100d0312070304143d41e4415024014030780c1c01e00901007091a42c00489034200343e00e00801d84246d1106410a07030000e416640b00c0c0b8035860f85900e81c074801d81c0d806181c03840c41d6850050100300050344c0341c801180c800e041c002066a04008610000301d556040340c06001c0103020100f0003403280c3d04103045c14400c8226090005011504018140035450340c511301100d40031300c3e0f201c800030501d444000403a801400580c1c00181603200700e01e40d11003086038070405459403800c1181c030350 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 513754064 1250 513752814 513752867
    0x51c06023901110f0d09140709050606070b07030f09080a0207050103050109050f070c140304060e0f150a0e060f0d05040c080606010806040f02090415170102040b18130903 75
    0xa083c2d40180e20b070841a0354080c4428103d031400b00d00580314107200c001012030041c4c01a07c410345180c1403d80c01404030b4011b00e100740f0500030b150050b99080501541c18030320f00300054a07510307121200509000b04041d12141c04008008030f980003180d9080e006a145a9503d00c4000080e5035940144a500c1c0813900f010b00004500100c3e200d0700748240301694181c06180d40c0c90b007007100d03074010f1004121115110000180c42400e01000680050095901c9400012001d9020098001d8050b64020701c00c402d292070180c041890603050350f403100c8a5082101400d80780c100010000c0c014448020340c0b0081c0410301182c5031206400460103540901c9000e04240e0305c0c1d00341130b5240c4404440150100340401d000c285103003040c1d44043c5140007410702c014248032010000034140d6070420304114024146034400c0c8080302c403880c5510788800364800214585031030007032000342600444076041d100c1ea686205030700d06a15482511001c0300d0101004100b084442d05e409800104860340344e4034448005541c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 513755314 1250 513754064 513754177
    0x220b011710150303080c0f030f06090c090f0f0a170102131a091e030604050a1b081c03020f030901050a06060903080306190f14030c0109051c0602 64
    0x200016600910b00500701142140c805a581c03400c091300c4520500c50410600c4c03c500c0d81c000142d400b03407201d0070203507010707050400400207000e0025040d46101d03502040600ba107980c403041588030f11201511303850407078003944001803400003d9620080c801c02c1c01030344200c0800d106500810140800030300d110032580d10b0f00c3c00b0101d80844d140c8034001b0900b04000c10400781c0f0308505061034060780314400b11800d0102201190400d8070583c0c044605502c0000414200048849800c286c41160190702000c035140c22201a5922040d9400e5101c0030f04c8141c0d607200c0b60380309404580c40210b81d8104183d4078200b6010960080c0011600c1505481c544100403034038074171030b8014a007141e070420705850a517140d100400c4280c00301ca40401c8407c20401d040041c0c5181210308040040114400c51003002940c24245400c0011008615041103403100b01480140d41c0c081d42401c0000c80d6170b03040d0002036030700d1400b0b100078407402c0c06e00c1c3c0103c0062190302001001c000421083c000340c2a40506200707000118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 513756564 1250 513755314 513755321
    0x16061404030c0809040204090c2316020103230916270c0c060c050409150b0307050a05070c0308090325050411300108070608220b011710 60
    0x800400090b00c15010b08042004400504584100148014542983c402d00e141c200c8400d1003c0501040d0410070441500500355821400144030080207460415460b15180b0034908601000381807503a100c0814900c003480d1512003c0d042c2907900410100d040c5800c0ba10707603031181303058a43d042d140d800c1d801003807040030342519500450b500520480041810342c46c1070301038800c0c0700d8010704024072004030300f000c03507154090760720107079166140c096503141807403502c82c16a80c203180c51a192840803402000001ca408041741e5201d0410b280c0203071039808201c82203030a8891010082e0002d0701c1600040144902c0c41c0003800c42010480880b00d4011000080f1034100f05c285c0800403030b02128240401050405030401140c1c1d40c3e20903c01842d05c0411280c212001c0c040c00080b5040e01d014446050f400048910041d001d0014030000308811440c068008010400007000594040d038200303c0780c45141480920802102d5100c4e038075008544c1c44031340d150041b00b0380d009903412a1054100b5422040c09520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 513757814 1250 513756564 513756571
    0x309010203090904020303070209010e062803060903090f0603020307170402030703030f02011e02070c0503060f06060706020403140a05010c17011e0f06020a060b04021602040e12160614 81
    0x30003039401c12102d14104054200000e009030b8150000b0040c40d00181e88544401c0c0c003030300ca00c4a0080c034904001050250303084085050150b0551f0040a0700b03c00c001d02c1c4400e4040761391294020075040010729045407400203d6004c0c020a0642c0d007004225190990055031191010365104881c2100d5000c170090f444200f564040d4050b00864024004a44140086014050140008100b806810703604041c1100104074248040743c2c042020b10400140d8860103000f814100c00901c00380c00e140400548110300500361600c0351400013000020410207805840007150400c0102001400e080d0085850ba6106041110b41d9480d203110058414051426605042805884d084441e030a0110104022410b4807010060f0100030500007011018403c04001071301c078690290010702d0541c034182c130649400c00c131180c0c8140e005218145d1201c3c45014281c0e00c0e241c049502141464410402500705031041109002035040041c0b42c940100030a10851001c0d4440e0804215402480503195140c0c0c82c2503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 513759064 1250 513757814 513757817
    0x316060903080a0624050f0d090c080f03040b0a090306020f030402190b040e0402040209030703050d030507030b01051819330824031027111210060f050a0602030901 72
    0x1d00b0004020700b007121744803c200300341d800c0091a0070083e0382e07900482c1d00107056003040c982e1151416010030036800c0c80314004080d080002c0c0381e16001d1400303c0d030300ea00644c000c00c44608408914494058030890902d002190403001c21903072031a01912002096000b01d0741a80181d04040740070329440b0011800800311030000d04168102410640c0c00c0460070405001603034003940a00c01191142c0e0107110031801140305170000c01054a500d0009420350340000e1404050529180c80c0e1862660460100d41d08401c40c0c041d851030b002c1400c40010b4200440c40d0104070300303003102c407030104501d010100c0d070f0303180c0d0010050f0b142103120a80300e55480160f0074090610000b40f4010118102e01501c88010401c8007560210b09107040c040d9021a10f0f1400e02003212082d2a01c69868000701c140508484c005a040c00c001c03a203896007551034800342408021270050040082c3c2462821080b400d2012411568040f0002c1c170032150b0301d481e82d00094400e40180e6100365040c0400003080f84c00001150440d80c8103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 513760314 1250 513759064 513759089
    0xf0c050309010309020d0c090c021c170603010f05071d0f130209120a0b060112050417030c0c01020c0d090f03150c0c02031c020d050a05030a0e0316060903080a06 71
    0x85074011409843c04020898200f10b00c030998000041b80100d2050292000910024160080c144000e01e060140b0100c3c00002c0b042c00340b40c03459254000c0803294100c0340849c2024260311030b140401d0040c031040200b040f015151400388030030a640070510030010b0180c1500c80d5180c840900800a0b441a0450041c0d44080446210428039030f143c1c0160000000c010500783c8030801c5400c4441c01c14015200449004c0c4e40301701040115030f0026002f0503202c100301b03400c1003103280c960f8941c65801e074008600c0540b9103002c070000f658001003108a40c400045c1c0c1d802507445421041081783d80e41503a600503804600c0010021441d540034102200840c3e4102c800040600c0300141c02900504846035840c00b0010f42c20068030258a04018402c800310126610114008940034001c2c18030b42c08075441c03010002c0410141c0c1966a00a01b540c0d0002810712001070088107100c0c0c4645144115041b0360034014803c460b84081c44800e40c8030010f014000c0e00e8441c4156500c0d07c1c20b9003100c4103400784240c0c9101d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 513761564 1250 513760314 513760327
    0x1b020d05120703140405160e1509041b0803030a05071707030c0306090c180e010b090910051203040e2d06010c02131a04020f0301030b0c0918070f0c0503 67
    0x181d045200d03401c4101d0f4100000c02504030b00d054807001070200d030103485561003142d420f0212115200c20380b000300900441e8907405c2c1041041c1ca11600d0301c05840500c65000c8101140a2069000079a07001c0075088440c502c88079511180c440c0c40b500100c4904207210700d0640040c200350700840034115031a82031030201d021951020303003e90003048505200070030950b543d078000c0340200c0d0b40c1c45100021111522190050720588203900c080c207015402090303205119a0040090300b1600064400190080710343c000e45030307200d048041602190703a00980d0301203090030740040141c00100c004c0c001e940d0b0301c00141c95540e03074044a49120907528904840403904e0f502403c40c100f20b21501890b044401490220301450722900000d50302505070b402c02100c02c1e0740c2c0200303200c00e00d205042c0c4144040142c03070a45c1031101e08084801203000502c80034042d01d0041c4000b901d0014000211180044010000900c00005045c04806400125512008581c0e201170211515000712504240c55503c000210703e03012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 513762814 1250 513761564 513761587
    0xf060905131b050d1415120a0b010603020f07080313030216050306010b0c1606110c0901290c15010608010b16150b0409110a050d0804051c0501020d1b020d05 69
    0x5001c0a420f0b00d10315615134804203200200c03440e26001d014186c500f241d8000c194402c00c502c810120191b00d401d0390040c0c141100051082c0c4083d41115654200180c0301c8200e88000c030880e00c41c40b500100300040010810100412003459100c8180c0030758211500301c0b00d502126010f1300c01b540034580c0d069100d5001000303194801c400600c0200940000d0f0b0704414038800a82d40315501030342003c1701051041e0041d000f1050100484103940c00200c8844803203501d0200e064030b107080c040111101440f980d174000000001100200c0d000c0c104500e04035542c180740c034480b00090020a0082a000442c0e1000000f03d1401c200c1c04d440c0340640305c0003141160081c0395140141205088503805e10b00e9200c2030049241c3c3d4680c130680c040740d80980701201c04030780c5101c02c0180004064018500c10380800960a0100b0700312015071b403d50718281d078080d00154400f69059032000150500030308541c000915424050700716005240714144e0380e0f01300b25800315000401d07a104c00d403c04003100018002e00c00c448548 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 513764064 1250 513762814 513762817
    0xf230709020703090e090c0324010b0a03060b070c080105060105040305032217030d0b09010f1202061c0b13290a0306020705030307091a090d0201090f060905131b05 72
    0x610a040000e913583e0f890000a540076402c40d16a103854111300c01082181c18240031180e04040940846910409003c060300c0c0075180c1801100c402c0000443c0501740f45000e0361200d000343c071241c00c0954540c800c0c0e1070825503000e62409646029400c10020800340e50143d410390f4252544034015500340060709504e0160000705140c001001c1c2000280001d00c0911a01040900340f5484c018540c0c134001c02e1400d5081c1e070302d42101c2078002c4421800410000c000c031041c00007591144000b80c04214040d00010b60140103c020004210980302c41a1050000c42d40c455402400151028642103220101e400120380b2032034030000d940b06061503525002078070318001c5400850000c00c03d410098480d220002280c000300c1c81210305900c00414030240d40d4000303001e200100500d41e45c0b41c3c00150041003104460062601ca01d004148452075442168021040c0d10060140c0344180408681e5450000346107405030720a19000f2004104220310654142c020300340c0c908100c8150340c1c0000740e19003003103c09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 513765314 1250 513764064 513764077
    0x203130b0a060b031503070e0405060c070c090c090306050f010b1b0f03070c0f0e0705190c060c1d0d020603040f080c06040f0b09030c0c010807140301030f23070902 72
    0x1c280c2c0da5a004030712085498080c500500c0310f25013001c0d243c2a040107040c0f40a040c0e4002d0880307103c440080100050b40042c0340caa01c954410030054451100b454001003403642500105079860408102d201e4496216503401e0449020740400e0101da141c1d600c45040c895000c2c09143c07a00f400800603d0b0104001c007a03070040c00408801100c100740142075405085401113001107070012205002003012040c000300440c0a06070310700d00440c5500346410041c1491046050107600006010820580c180c040d0b00c0c18481990002d406004010900c0c2008110b60451941504044020007a0659074185616103071601c95000c0e021030b2840d150f9448404080c44c080740111890b00c010019a590704809109490080d0f108420b540311143d418517101070b00c004001c00928061f80141300c0c0400484000500300e40b1102c082c05d00c046241c4407100201c506508200c5207031b00c003040010002041001102e05604400e01131041080001c400840138024149031503402c0741e00340c0c001e400a01c9950110780c0180740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 513766564 1250 513765314 513765331
    0x705011404051338010c061413140102040506040b220e040506150303030f0606090402040b0c0c0a06050301211a0f070e011709071a0a02010e010203130b 67
    0xe05540c2d00008405008070305001248a840300d080c110298020f0001c0070500e42000c0c0c5099008840500d460f100e1540419500e040101070340d010340a001c0c1e04d1b4050304003c1d4101d08011030502c0c0404000c80d9020b03030500c080310140d040304024580810706100b518107603403008051625080c500004140e0607000f802078040c00f1054010003440d8000d070f051194000700742007003021030300d8513250820500304070005020020b0710b4001451a001130703901004a03a804007201040c0405034032490045440d034040d0700d08030b0742c005100041c08104e480c034401c0074241451140c02140e1060540c40d040c48020400d9210700808070b9014001409038610355500301c4103903200c020300350340b074129161110030312071448091001c0c4004110090003a5034261600c107541c00701031400c2c60320800ca11000000c14204000c0c94218070740c0b803903401183e00d130f42041c081c1100034080803a0340d0201000c07600002c101a40200d0400015600e07011341c1800056040c003da0348942c1c1e01c00c0c4031f51403041311500e4141c0c000794024101007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 513767814 1250 513766564 513766567
    0x361e1203010303020a0309080303010b0304120e190e011d071d040216020f0406032001020f03070c0501110a0c05040c021f0b0f03060402151b0a03020303040606061107050114 76
    0x26819801035402503000e0340c024000500329050103000c00403590004069501b003000180308425907401241c0e00300da4824107000c601400741008840144400300030b10740c01070600c0d442c2d02c072101b06506001e081d2030000d14441c0d103d907620345809a08401d000c2201003400303483d100155000740a40b03245010050141140e540300400c090001d0126030102c2c1c8011a0488494540c40940c100602041001d07001a6020481d50381952a5449090340c0c4a0102c07204026a424010441e403082c0303c64280000d40400700e070344400c4a49400c4490140398042e244c0014001c003840d961110002500000c1c8a411140c012a124142801c0c4809010078807c4d46042d4490520101c00e034401c0c0d40380344007143c4910540010300300700b682c0401610350181d1380360a120f41c0c0404103120150355420400e280d9800044c0c0c1280d65444035076000c035801e480d10815902d207401500451003c0c140c01100862180c0d100340010003010f611110300f501c6106c2c2c10100030a207540501d0040c401940079028800c4c120103010b1095 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 513769064 1250 513767814 513767833
    0x6060e1822022106070f02030a0c080a20061602030304030f0323041a062704020f03031207030b06040324020f0406020102040f060f021f0b0405361e 65
    0x140321801c0040610169840f0400300445c1d668407680c07030004140e0902c043c40c40c1464482000b00409401040942090000124410b030fa9005201b50810f0340b600340c2002e030700d80f0400701071030b0b89801e012a01a0303454000f40c2101181c00344040100c074410382d459259805440751205081700203002541002d440480380b03c54100031b444649002034807580c454138061101030140030700c08a10341405002d56001d0408504036034a07211f0b804040c0d1907007071001800d10141d41d5441c0006011a002d5000141d0180000516070781c003080e070780c04200e1103880c8545040c040c00704080e017032080c50301c25403001801065600301141d0300c90050340344030b0140c40003e40002d0b051842849403002c841d0701541c03100e07016030b60004003044044020656030008150b942003041d034a2000501c040c0d25115410b0507000307030303a810212122a507038140d0300c6200c00d21400740080040785030122002e206503000700900c2140c40c400d0030032815840c60480b268803200e812003015102d0b150300c002c1703000b41000c0c4004070300500340100c843c00b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 513770314 1250 513769064 513769099
    0x60a0f091a13050604111327090c1a03100902031b04080703050c03030708040e0901020f030a06060e0a240203071403121005060421020406060e182202 66
    0x149002d0101e40c0000252070309002d4108000c075031400000c012000c0381441410b1400050341746003003c40d20b81903d4036084000700710880c101307101078002141010b440d041c1c01c2d01c14080000044000d80703003811203500304c1544c000c014540e14041201da10070034508205050001c02d0480e009942c0212101101c1c0345440700706059040f49400c542c0203450260300405080040c80010851a50480001c0c0d000d149411519225100f0610a500903140840c50709408612240c5003581180c504402105aa640700e00b09029201c0c00b5061502c907240000c1c240247c80c00780ca1500b803050004803180e0780c5216054003280c0031070f401400004076444d410341c04244082c1c40403a007950081610300309020041d503610b8501d510101e1078003c02810740002800b80c58000e003c2c90326850101ea003910100e076004241080000c811422642400e18020341190800000103002c0d07400900c6442e441030704903040c240c00300480300005400b42048030121340c54a17549220518001d040101c035002c07c2d0015100899500c54001c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 513771564 1250 513770314 513770329
    0x206070218150108130f02060f041d0a0e1b010509090108060105031513021504090f0507020c01180e0429040506010f06020d2109060e06060a0f091a 65
    0x3040800040501044401881e040600b00604024200b034102802c00c0c0320400d0541440c62130092800301c00d407202605641c1c452060328200541c09001c2c5030340b00e80320402d0902031111040c2c6505080070031800320701c1d05102806545071000800c0014039a2078200c4440c644240c241c2449035060100c00c01c80d43c907240d01d404040034060201600100b0842d49840e013031510b01034071106201d2070854208d0030300601c43c0d0f16a1070b191410b50103c071030382c0702421502001001ca205590100740d5070391a00c42c1c0140400c0580e040548900b5040d000e45541000d0600190340070030803555500c40c0c0d503520380c50502c06059502c02242d0030900401050280b075000d601c20b11000c4071500100b03c000e0400303404001c204101082810302401c40305041e910360b00c2c80c107000a0350322580098141c0a21105200721208009900400e9181c40940700e4240a4518a03081000003010f00000d10b406d28042c1000085c0d281c03c10400d19011688600405400b0700d14015075900101503007440b00b0700301849607800a0050740c5000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 513772814 1250 513771564 513771589
    0x709050301112104050706051c020309011b050f09221107140d050405091905151206060108061e040f05150d0b2205061807080a02030a060902060702 65
    0x25036143d0b440296000c03506049110715400980700c20030604200000b1004541c200803110039050060301e400d01c0801d0030320798100d81500d00c00d03520302c04810011504015045450000341c01c08050f04c02506004046446206a01c030b0711750720f524100152840e40c01c111520700c02d512406d2500300084800104500107660410719640d42e04040030401e0b100b03218680c04e105944520705401080184945000030f4054010703071241501c500840c0c400030b2041c6011440061201028820420061900c40c040481405103c1c40c0135006500a4603030003251400004d41c6400781c403058444801a42e40da20400010034200741d4980c455000d686141841c64403a40211b0407506003510010031140380a02c83c410168007402d600ca4411042041c211001c100c814110a400c000c85141c1c01e4000100007060032180b4004000017004c41c400d240400428180284000541c8015034042c0c500c00c581c1c0340c007030541c2da002c480c00107035050f0030020001d0f000480e107500c80405d0600c003030142400d284068000881b8044c440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 513774064 1250 513772814 513772841
    0xd0210090602100605010f120b0a0801360f03020a0506010b031b36090c030a181203020a03060b16050d0f08040b060d0807050c0306010609030f0b0709050301 69
    0x1090a01c8140d405120300d1920b040b28220401107140341200081010041c09040d1051000400e1a43d00a050741c3c0c104080d21280a0400d0300480d6480c420b650003001b6840440300d02c0901e03099042c2d0640f03511130307980c081c0350f5002007500c50412071a05c500c2000c08403030800702d0542c400c28000e07000068051114074001c00c0c40049140d12031400e46c44d003c911102c90780007100f00e260100b000748041c103140315100e910400d041640102c0c1c14204414488000603140071541d0003145e2404100c2c018070180c0040d40300d130242100038001c906080c01e2a0540582114000f04545130245a06600038841d501400d04603a0510700407808994030a00342c21207501c40c0300c111001c18401c00d012000d0101c1040400c00c640424540f42d602c042074220300400e298009040240000c466802148003580c0d14038504c4081900640300c195911124a4155134400044441034024002c2c0300000a102e409925914100c903041580300d8810401692907084601c401440b440600005080c04101b9840910a140042418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 513775314 1250 513774064 513774077
    0x4140703050f0609010602060703051008120403060b0d0f110307090c020a020307080f1002090409051f230a0f15090c020118111e0409061406030c100e0d0210 69
    0x9219500d0341d880b00201658002d54900c00100019580010001c2e40a000b503d4001130741e49500803280c00701503a80d44a0403080c800c1c203030b440e071101c1c500d00c0041040b01d200b000d04100b039164040901800032483e0780c015055400070303030b60140807498000440c07181110003019108000e403121240c6041742c4401c0b0105005a0200c01c0540c01c5040810201d0f0103060943c004090a03111007210945c1c440c0d00c4030b10000c2868010401402c3c507140d580210320f5107070340306003651400c00d6030b20800025441500800d0080c50b0400044140c50707050300b840c00e8500c00745421075442c12f070355002c0201e010345552512040b00307030b0b0340e044070070004101190b140000c1d0070100d002181c15500303454028251000680e0b801101c031144080c142c0011070003140410811402e564042c420244d002014012520f94880550007078241b101006c1000103c0d4046100c985822003215569110f040606680f40d80b01007103240c008080c01d942c0381403903000300c00c005e10031100284030442c0110643c0c0400d11104c142c2c03031030b000407410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 513776564 1250 513775314 513775321
    0x20c06161a090607030b150901090f090c021e07030b06030f0a050d02100b0a260303040c0303031419110c031b0c01110a080d021b0d08011409010b090414070305 70
    0x900c10b558000713446240c10301c03007140300c00c00003103000c1401c650170007807107000103450405030340a20203140042580720396000c402c1c4d950b9480700c0041c000c6a464100103000d0076008003101100c1000343da44503145a0002c0c41d00340e0079a9140600c990f8050300c1e042c1d151007641c0c20085001010401c11040501c114003400c60070482190181c50030303003c00c2400020508151000185882d44030a070011241600c2e209100022072000103028600004101c1c6030720300000082000748040c000007402220700ca035800b003118000b0b544071241c00b41c00c240c494034018940d012103118440c0054000000c8501d452844038035121040c40401d282d90f0050304006400155000203100225080c0544908000f0078200100d00040d03008031a911024090801000040c2c0420059117000301a4181c5178100e0705580e80ca00c3d94401000c0031070b50f0308904203c0400041180300080f49a034044401486801c00140620b41c00b0703420300040c1519908070207030b10b80d0003c2c0d44222915800d21164000b0b402405070b41c40000c1d0905 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 513777814 1250 513776564 513776581
    0x140d020c010e10020a02090c1902030403032606040903030b1c0203011d0a03180e0c2d0706020c0c04091b05100801050f12031b0c0a06020c06161a 64
    0x340c2585862081080640f9414855004210340000c958101d481101c25903602401581602510700030141c0142041c64089916400100500aa034002d40b070f00b00414140b44050100c0302c00344012043c030b44400e41c01241c01e500f0b05420405165109042c04941c407401940410420944c03042d0020701824a01e000c10f05504080c8203490b5048620000b9000703818420040d203079a440782c4c500080802241020020602030740c1c03581c8001601400c00e0f000118104650050303826002400050348140c0c00192260340d083c505a00010a020340300d04c01400d01a880c0c075100025000541122a03d0250032104c95a80c3e62764415802c01510aa40d071400d10205032803010407181c060f03042a40511944144140002d411248203411503804440d04182c0c0101c00c00894444c0d0032840d2403161611010500d80c6580398040449142c1070800340407103a1540c181d004105071952544034920150300b140d0f4034003a50341804402003001c8a1410b2032924064130503a00d039400052514a0304541c0e445000a02c443c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 513779064 1250 513777814 513777827
    0x1b0c0f16140a050a12060b0a180b0d05061303120f23100b0c010209030a0501020d0b01090b030a05270109020405010915061211040f050909061b07140d020c01 69
    0x45000340d0395516010308200220350400185d00840803d244449400020070280b42c0040142c003038054500c2c5941959800b00348440f6500302d298489881c240004010b83d8105609003c1c0c485400c24020855a11041480404084040801d0b005c00c105081920400c2c0c8181c041d08800003914040040d040130032212092691506066075801038007041e040c4034506405840e034406480550b4101640e500d2040c503118028031442030101d8250048c3c107018018080107601404c01101100c0d828061240143e00444400303882d40603102d0822401d1000c1642008568800ba601401d800e08110054006950a0f00c0540d103003000e44086a4640d0440b50441c100341c003c050041c40080c4040c00410300741e044071070414149003e170100708203080414150101c0f80742c00401f44e1002d0707810074565807038591013141e41c0b450003400f54a00501c0340c4008298103260002e410380c0b06110009140c054480c188018001a40c40988203840c02200c0030340000c0500f4050100200003a00ea400803c5002944000900721 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 513780314 1250 513779064 513779099
    0x13081c080708090a11010302190e030c01030e190302070302060706060f0f050f0132190c020109030f0201050409060603020a02070501110d050310080a14060f1b0c0f16 73
    0x10404120240421008002003403044c159000d541a0f803c06801c900490013400340380c819034050610b1354005051150004d000113190f442c168107407040f00f60300340700540076640c081c2a2040c55500405414024442c021041c1454034400d1041e00c01040c1e41c3d400098060b00300d1070b000d0701c6160b51134008005180301c2c0805600140b0000040410b05460040040c1c1d8584404007603d040c012003801c41800600403100341a601c69040a10f40c016175980c04400200350009900304040c0c1110b207801a12913030040012088543c1d059440148050450341c54030300004040d8001c905100c0c0030312005c0741d471a8071401081d02920540d134006844001d200002461b010341644000d05002142c51407078030044021032407000b00e074114285640d80b0703200c0c50380a540090040d400040c1c1406175180c0310b01000a0400014420817299048071407a03102c003802030340d1302c01c42940c502940007500000066070104142c040c012035903c0e01d041d590501c0b1101061030900c4002d412084402c464002c080c03215040e1420034062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 513781564 1250 513780314 513780317
    0x9030d0b04020f07230a0c060c060605060301060e120a020f1e2106060904022407060903210515090618090c130510050f0a030c0e04152013081c0807 65
    0x241b0964982031900011800f98004101421945c40305010198204d1001007001400384d03662580e40b4203004007107141c4407181c507100d609102010251500c0002e28010120340003490100c501d80c10508001c030011b006948035440c648200c0810071955101070081ca507034a8041d5994800c1860707441820309042006108900c02c18000040c000541c44020100550b014010348034002c00b04500c401c0c00340c5002c0d181300141090b0404102008055201c010241e0503204103943d0702400707440c001404283c0d5000ca41840029000c40021a16440d260703124540202010b425070310407000c0801e840c20807400491700f0041c44e070320075648403000b070506803100018104201c0c800c000c5402d203050ba004850506204491090700303680340c2802c0340c0e618804088000c507402740e4003050460340c90f41143c0494030121000c0d108000301c08020800000b85018041c3c402d040c21044064282c0f1400e0015550341055148007541400d480c004948410b0400c24240a0610104210903144400c00010704500004010300f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 513782814 1250 513781564 513781573
    0x190507030e0405060a030b0c0d060b0406020c1c080d060e0105010e0604090b0307080604060c09050f0d120908012a020d0c080d090c062609030d0b04020f0723 69
    0x140030980c40030307400e02408000ca40c045407540f02c91001500c642d0240d04090300040e0802c06100540d040403006114018100c1c030180412039403466014801e0185104010258110144160452404403087c50300c9104400e00f4a020050300c1e241c40c215900400361109004d0f0341c0d090b0521101101c080e6481c0181402d103009811a801c0d1404107045010f80d1081c00f003215211019040d0381d56080c01440c004d40540400c9514a103000d041c60001740540c0c00090f00403070510350020881d4282403007503038505131001c0d00240803086203954030100303079261100c1c02003000100301002c20701500038060a0214000740820f21104844104c4482185288900c0c450039580690300c0035540702d401010040d021a00b00e07000984404407507020314090a07a000000701100300c003440105403950000c80c111841c81c3c131030504107142c10054142514440003a1007246265100780041c0c00380d581c6d260002c900c40e640241016003800c640040703080c03030380d006180c0c00c42d083e44e2003103d00c0314484440003120002100782c10090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 513784064 1250 513782814 513782827
    0x3020c0f0d060506030a050d05130e1e09010e0f330c03090309041b17070e060a03060e04030c0312060b07060207080c0d0e040e01020414010f0908121905 67
    0x150030708940440108070646070000100d050b5400d019190302250484180c40d06101044002030880e488072004899608640c030001c1803012074007210034442c200c4020030218540c030a400700100020010806505592252035822080301e0a100e41c04464804d040188113000112884001d0b02d080803c1d0b50320600641c01d00f0940712154100304982181e03c0c0c200050f540e07150b9012890852141404041d0400e00b00445038140b0b03415a00102c00d00080c0c1d540e4490f0360503a481d109518440142d8201002540102c1c6040789403900d00020000c0d0f49035400c1c0020625606c044490100001305c4003074001c40c24a6500c6000d040e0000c075600c00c035401d010010401039080c4803a0303c1c420b0280000140c045907001c0350240800c0904000c440074070042e48221450401403800050040c608100031034000c0c1e0500c01211840001402540c056500c41c807240c2e003c080f010001160510f442c4c40c2d0071000c00c5044040041d0200061090b25401140c5075000d035955054506905840110f02d03045030708124081140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 513785314 1250 513784064 513784069
    0xe1005070906140703050703170c030f07020c011e051c02090f0303040305120d0e01050901051f12080309250501021207031d060405040e0a1b0308030a1e020406020a03020c0f 76
    0x4c44040661604009484034101d04040b5500700c0d802c0101e0b0100c0c1407510070b008404954102862003006c1d5035011840545d2500c4040740ca40302c1c0204401d001c42c0046102d11030070b0381c03402c202a070403074807616006042520f04510080070315803907084d003901c0030390010f004d0740281051a280d00050780c007900154902861581c41d65074805903414030b020360440104800000f886113400111200c82002c00a10003070501c0231807c0e0007454140d03200700f000c0e91062090340340c2c0100e10545008441100014a0b4040341a40381c545041d0b10083c01e04c02d65008030304580c101e06400c5400c1c40240f00d01540041c548a043c18000392400491402c1c0f0300d80920240301130b0000942c4901e50070950701110340109403081005020542c02e0040750020f50740319080442c48803541c64009801c8601602a4203540c2c0380c4070f034100350440c211081c1d00014100800130000582d140803141c015070b61a40c094400d50103540840b00740b14080744c102d60019801604a5120038092507410402c035900c0c81011160742c450310185000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 513786564 1250 513785314 513785317
    0xe0c0303030c0c010f0911010f030e03090f0612040b070f09140415170a1e03080402010813060515090a15140609060a09030b0705040513020d0e100507090614 69
    0x56000c400c90010f00c400c03082100303410040c04200810820b00c0b02441510300b8130385081c424007515000864040654040d1f45c03003070041c8226010408081d62818207404140f101c00c01250094903042401007000c80c85000440c3d40051086000e1082e9540500300340c10020b08540720b00b0000020400c0d980e1050240c10080e000e82c081800c4104c41c009040420314402c143d040000b43c0c000c021805104440c3e421b424004034402449c54800e91020000c620300000c00c0b15400c0e0021406000101c4200015005502950b031040c0c00801c080d0710582c00c48007590702c0320144c4808980107403c1101100c14003403507041540140b50807440104041c0b04e20704500c4c0340740764094014810325034544c682e440e12050680703a03007003100d03060746c1c2c0600f03c2d590b00c6100440152a0b20114403080b241440c1070000108103a100c0d200b6501559801001e2981409510008802a40090074400505d0355100d4200c0b140001c03c001054070b40c6090b280104103494004c00150400c040c0c0c0d4864800c1c00040640c2682d884450070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 513787814 1250 513786564 513786571
    0xe1512070c0c350615010207030804032301060906180c0819090606090911061303031409030303180105010f0f03230f030d0b010c030e1003021903020c010e0c030303 72
    0x2803d4071000b401e40241005800207000c42d91240d0000c01c1c40642e80320101244962040c1401c444810980ca80000120f94482c4036100c06803554034203100a1000800c01d0700041c00303011410344520044115803000e2400c4a1856108016081d912035042100d48150300071200720480900d03080000016811025011910044c42c41c140e110401d4246100e40b100d0360300c021320701c41d00312000304a083d4a841030783c4014858090256408410404403101601d8a241201c20000010302c00c455200d16640c0c081d1115106070502500300c41050080d0406500e0070006584240000c91201c403200080d400000d003105c42c1a0480c500340301d4006803c0c070074140080107000841c0c3c0e004000c5400c2c0c291101e0700500300c1440c074180232440d00a9041d1015011400009800180700c0c49104000d1403440300d0041d00d21018500004010402005d944081490003124031090b907641c42c1009440d000000030180c00703213020780c5025000700707038003180012a48001b4881d0509001000005041c40c642050001b0307601d00004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 513789064 1250 513787814 513787829
    0xa0506030403111c0c020a05031204120503070204050705090a05030105060105091e030a1a090610050d0317070314160507021c05070605030118050c04060c030e1512070c0c 75
    0x104100800700c2d040002004102118031003220b000074941c0c0c000c05d203484903081a0310480c06044041250b14001c9003080100302d804e0030030f070f1410b07142a02c02c61000031215016116800180a07403805a1075501485105e41c03825510b81c0d5840101a041059000564200034006e03890b010810031566045000c803410460125a03c05030040c40703200301100e207404404810340500407030142808005540d90a0480c5160500303040d003540d55a100c0150395508226440c0380c8074080407008004d1402c08098040c220ba0191801e107070700c2c48041109a141003003c3e6054800690340b0a40442a1003001c1c480b142c204080c02400b480b440c940000c003c2c514080e0303a1000e4400c01402c0018035000c0c0d4800703000300c07265500c8025200c942d5655400a020340e0024400e0080c4000e038040000d5500c3e2003031107414402d46001c45113030b00f09428580111800010282c0403014416940c40410301961a00d0490307400040c0a14029a01c810a9100d8800500041d000d4001d000d42116420009507940d07902505881e03e4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 513790314 1250 513789064 513789077
    0xb01080a0902040204090c020c120a12080705070b070816030506030d050c19200409121d190906060206012706051e03010b0109080a080f04050613060801050a0506030403 74
    0x142c00010001e100715070010b0012484c1a4403a4500e40d000f0842442409007110314070450780348010410780300c048186005042401d46600b40301c000b4011415140c006d502c0b440e141d824850240d40c1e0680c1e0070f034113440000c00b08034030344100143c03c41a40380b02040004c0350318042c0883d0410101080e942c0c400c0003d014241b00c404600a043d500d030421102d9402c8085003850001100741c0d05029005048410410541c0360a1410203003083c1003501840b2212680300c424030200c2d010441c01294642c50307500700d1b8000d0100100c001d005507600d400128111070505035507040d61034a0034136080126909603106005640040c0c0c01001146c2c054840f048001425065092041006a0342070f8003c00711900200d510028400304481242010443c1c000300c49015402044024000c60064914000501c1014120360010000d817000516002c040c1c5214080c08540a0800d03880e140040c0c2950800e603040f008440d0303000e4041280607400441e040c01841c0c1034034000070290a101c04100e0034070000f400a070501a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 513791564 1250 513790314 513790331
    0x1090f020324011419062c031f1b0909051b03010605160b010b1c1107020d0c051005070606060f1b03120213170102090d1202101d01050a0b01080a 64
    0x3900c1d517000b00002003000c14138158548501000e03007020030000072100a00c6000208601035007009911050703041004004090a0701ca410103401d00f0107215058602d41521904045112825050f440000c4082616400d18181c202421541103600003440640300300003840d080303000d801d03102c000c580c1907403454505160f84840300707005100440c1c0c0340c0c4002000d0703001035070002845491000281100301c44d440e41d103c5a03198903041c12400d442d132450070320907100810441b0b10010700d0b105c8603810325940301d08903607285580e035800000c040655031a2000302240340011007004000780da114005c0900382c1e90a000140c0007410200600180c3d419100528070011450040709140c052182200b1a00701e80405541d12201100011200402c500c1284995940c0c0b00d841a40c00308180250396152001610110b00d524140c1c440e80200c914072a031500942c0940e554681020031507004000b0601c0713200185501d00b0354a10303080e90868500511600c45240b03005a6011941c0c0d00a143c0d582000e100003004c20406c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 513792814 1250 513791564 513791569
    0x4050f04110d06060305070f091a1003150506030a050402031c080610020f100f06050603044101020307110c0d080a14071101032702091801090f0203240114 68
    0x69170005081ba1140c8000020710000c1c00e100d0030140d030b8003807105000c0f84840301645d43c4490545201c0c158001d513000c0381c04006038441c1d0b00c9600051800c140c1d03050010b03610404680d9a0340240d074580c401c00d440e0800c00c410350034100b01d140c94048030021140f000110300d400080c031010010705042e10902804601c803c4852081000030b1030511100e00340c03000003100c00210001088003080040740c080c14988001440e280045c1940d218503000040c10218408020a0b03880d05010320040b040140c0754004011907401515402c0c0030326070b001c4000182d403420300440281021044d00d0f8080c410f90300c00202c2c1c0000f41c60782e400c11120247c3c4240203a4452485160541d101c04501005119480c0c02082020921000e0390541c890200300b07803001c000544010700e081400d000d0328809104880b003010301d5580181000009164400c400e000c25013032261200001d0790940d1001d06080ea86071821043c808203514042c440881c1c07015030041e04040c074401541c0c02c030000c010140300b0410844481041221180c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 513794064 1250 513792814 513792821
    0x290603060a0509150306072a0614010303210905030d0e0c030f1c02030a020d050d021606020d0b09061e03120318010506010c0f021c081804050f04110d06 67
    0x3000d0081c00d00041c2e00d400013011002d0f40501c01e1040c464031a42003c00c1e146030141415a112a0390722110003100303044540c043d4414000360a0072a02141d64511405042a2079040540690312a03a1121480b10540c000301c00b41d400c1c80c00781820300e145450907110025200101300c4007090004000818084c001c04200c1e401c5c450012040e541600410b241c0b809400b0000ca000854542240711000201d6903641040380e0340d009524807a40980c0c013021400040901843c050800c0048812026152a1001d43e480081d414418011984c1c60303000704202c2591002070003100c507003047c01c0d101700c040ca05c3c0140005141c13050310344062542015085055482e61814040008040d0350310414075640e04060110103000c0203203140c12410380d4a0000070800700d40c4184611020503030080c01c03890b001c500700d07000c1180000c5009a4001c0ca4500006141c0006094801400102215810b81c42151520b482400240c480007800c1203440c0b07400004000c001510380a549070180750a69512054458525050006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 513795314 1250 513794064 513794069
    0x32a080912040605090901120f1b12030c020102010f0b090c130e0718060c020a0308160624141e03030c060901051603150605030901090c0801020904290603060a 70
    0x41c07140040d010400079000001814580710685058805030b0343c0e014140410881d18000410720000700080c5404a5001400b8610718100701c0e0078079080c1a0390700c4450000a089640071004540d5071071446080d580c081c40b60808004411100740310490841e0009052554000c0485207860740c0821104022011038451070080c044901c00d200281c10070803009444034080000c68840300b003590901061381031140c40094100d41c0d01a00344400d49095680d41242d581003203110a40c14001650642c001c140076004024540708610989003400580c904618140c48940e000482007014004200105881d00600c103404801104ca4100c40072100100003401c6202d03130107242c0424804c0030f06000b0208410750000340370b0240c46158808290404000750140c4e01c0d030303250703946c103210404004101d0303c3c0c094002158003086440000506002568815242200741d4204040ca40e5011401d04110304042c402ea80004840a05000507072440b22600003482008107042e5011311030200c040b80d201d48954041d07c01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 513796564 1250 513795314 513795343
    0x270d02210702041401080f0a08030a0f0b06070303091b180f02070803101401030b010509040504031b140c040e0a0f020a0f120201020622080304050a0c15032a0809 71
    0x403195050584d401c0c4070081c0605202e902a03c031104009030000600c1140c1507a1010150381155206003000b40101500100303007035000d8640456009a503121002480614800e07100003840ba00d09e410070f010701c44080130507041c003004020428840f0300d91600079420304805c40701002c10f1034012650610301034003031035000400758017000c130070f0000300d444490340501039030380401904032074441603001142504c0c1076540c85400b0503000c00c16240c850400f5045640d0150117810400c00d100070b80c01c030412121407810340036100715154014004007404184034070031203240b04a50a00c40e01d43e289461946a080100005058020700d440391401c64580d0140c800090108013425404269a011480d180c090480c3d401c0740140550700c000368030700900d48061160013010885281030001c85640f011115400540300342d030103200783d008070000140201644c90140a44406c0340c480d0f0041144058240c580d9042c010003c00c0c0701d14480e042118502c0b030f140d2001c001615000200341c071340344152030500303102c240c8904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 513797814 1250 513796564 513796571
    0x9030c0303100905070e09010e0405120d09030908070303080123031606031805100207050109020a06021e0109120503270601050f04140112051005270d0221070204 71
    0x41c0700c2d1184100b2812504424030910582d80d429900f12042082c0300c082e542d11000c9280140300418060a10581c0300388a2405c45142203c9034800b051140c000030382c0300300443c1d01c0324009400c01d9886400d80c0000e0400000905400b8207542e0050b0403946d0500810728604141e2501561841c0e03ca500c141c0030801c041c4c141c07202c1840c0c036080c490070045540188404203050854440d0154420610061705917040400b40c0b5144221a02c40e0300031b903002c075409541940d244c161900143c0d40b01c0410f08001c000c25001480042000d901c000d64801c114200301c5800d915200e051004124400d52040c071061840c0303030440e40c1c0e07550510100342c02c40d1001c641001c4100c2c50005011000400100d50741600d00c11500d151004210001b000103864504556850a190000041004544600301403004910036001c0d030b17030401410611a0116442114881039203060b69440585240c18a20a0210f1368040006000750017001000a591203090f51702407061a480d1503102c45132441c000d026521407590040060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 513799064 1250 513797814 513797821
    0xd08040315050c1602130b12060406050106020a050601060305061809071701060302031002210a200423030f010e010905070603140c0306030a020a09051f080a0b09030c0303 75
    0x1d0400076404101c582030741c2e00c0d00c00882c100c01440d5050780c1d54041c01d2490032102c8003c1750b0921102c0d061200b100f8560640340c04109401d07941780da0014824110000c02050309103400d0502c8415a8410b80c0803009541000c28007201154010a07054103586540c2004580ca40b00e41003c5a5080800c0e45880b1820382e0400a0240686001c2100c01c122988041c054203469115030841d8200c50035032100070362581c0120301d05104c4900580162440640c00740505262050114005658a0701101e0401d8010790321482001c00c0002e5045040e06407209281240c285800c00007000750300b4444c4100070b40510f103070b52440d0b03415503004c001d0090313205282c80080c4040c002b684080c50203000e030003d0480c0c1d10700445001046c403e129100d070051f00d00900203005191b4540342169802076001078070b6660035000302c14001000d42c07149203640d40105921070001a4a00d020202d80f0019051030b000508101211042040b2030070000644001d86070300040011510303103076402598514402c86007110200d00003c801c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 513800314 1250 513799064 513799073
    0x30b07030207031e0c15060504020a020d0f1823030f010902010e190608040503161505060906060405060a030204050406170709050907030f051609051506090d0803060d080403 76
    0xd0300141e0300c0b81d1205825202d8001244460000c80c80c226400035280182d84170219a81c0c1414030001c0d00d4500d000500380d134580011030b041e640010000c402580c446183e20130101d070301007030148022001c1e180559228101d040600024402446001c0e810b0000d04120854907485506c980d40080c4001c046500640700b41500c0c07806080840c00030b1307001c1202c0000503085400c101e4415411070340e4140f0501e8006080000540380d02c20045c00540d0765100074005007403070300c4010401d0080c4d9402941d0310a070701a25038901c4400c6c4e0300b0051191340564410300911081d80c0b9160192020764504a405a45400c442c0d4070840090147e680039a6001c1e00700440060341800100e91450b00c843c0b000166407400703454285140580c1d6060b00c08450643c010401000820080782c1d00111992082066075543e100d0410350034170b000788a42108401c143e4a405000c03c002c01e080c3c411180790402e5600504010203180065209030021602a052000001c0011141c8e43c640487e4494580d0102d0302c0c64540f038407403e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 513801564 1250 513800314 513800317
    0x170c040603150c050711040c020304180f1107050a150f05010b0a180608061507150c090f030507120f02060f030901050a05131205040b040306200405090c070309030b070302 75
    0x240002640343c00740400c40248102d040301e00064020300305282d240c1c00309003800000c01c940b0702d454086010a110119404401907801a9a074030740e60000300d0f40500a40d4590111003542001c0c0001c03540800c20000000d602103030710501c0759008a581d0403056200b550f48005800301040e43c0e24080d1820b40085608100c410140640c180c0d82da80d403c421034145085210041d003240181800711342c0141c0010748516281c0801c03184184400d0442c0d0604149a13030701030b81c000d00c58444280a80d02c031b481da44801640302c0710490060003a520500e044900d9034913041d45840850141456440000c40d5030760038450404010490507901038029640e803a02d584140c1c0168000b628826115400c10001c05c410f6200c07400344a026030100d194480d0a4000c9542c2c80202100181c2c565003801010300c000500d8048103400742009600525011030280c07016416a101d400e26408110800c40e030900c820700050300c401005039409141d40300d0490b80c524203030805940a07000c41d8401403510116004200701d02c2e50580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 513802814 1250 513801564 513801593
    0x312041805010b0304022209060e0a05210a2f03040905060402040b030a15030c060f0201051605040302011409091003050d092d0807030f050f0115170c040603 69
    0x100a142d807285980c3c070292205450195020520f000e100301c0e021a5001c4000c950301c554000050401d41c40e540f41d50603100008041c1146070010300080c01400b10034000115040b140024504101c840480c683c003c900682c22018100070150070290034032410001d550050490702161400060100d20741d09580394414001c40c005942811701050b1541000d0003600c06071028062100d0541d07442a01400c01810507409003924103160800c0040460888001480980710076954100c0035100a40068251040505099401484820041c10341540b040649041e01d60900c3d2200301c419483d0a201141c2c000d4000240e0f008581106000e084900782e080e640c100c902c00d1040e1001d24040c440142c03410980c43c4101c421700b40120f08255a04048100c0150a503070b01416210b0b400c90f00c9400312840c01300c0d43d80044070f052032522141001d001081000c3c0046485000003071012110202c1c4103140700901d48256003a0040705007a011036940e0520041755902000782041003050390b00d090030b003184c08001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 513804064 1250 513802814 513802859
    0x251101050c09010908120a0309020f1003020c0c0108040203070e0702121303020a0e0f182e151206092f2407142104050a050d020d030e031204 62
    0x3213200190040010803580c14a045245005041507850507090b405040030f00c0c2c040f40e00c01e01c0040c0591a17540c0d0000b49800e03001e5142d40050719604004c100e9071402030000e0085060140c43c004000061307400285110542c6d5000410890319160400d090f4900303141244629508600880d0201032450300e2000703d421a03008448040a82d6541d48d080e502c00101583d040185c8000a070008000b516500c180c14441d000420880e041c4480c9599144400f41c00d00d0125566841c804194600030041c0f4098072000031418000114054680440302c5080c1c0b0f82400d0082c50148ca40d11460140201c94041c09181440320104010010401e1030004c2c40f00c240200c01841000f02002250080704c24642c0c10360000d844900750f91030b1054a0b124480a407a0404284007144601c080c0484441c10788840c40171503040311329600340c03100c2c00d100806c0104403c0d0b8202c076000310000846074015940303003142580603c1e01810040c00404140020034104050661140c0000740e00140002d03180600180808003d40c3e007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 513805314 1250 513804064 513804077
    0x1302010909050f13050f070b0301091d0d030b03100518060906010807031b032a060c021e040608060108100f020a0e120102070b0f0717251101050c0901 66
    0x22036041c8800c45070150780d0041c10219040004040700440c101500055001d0390458418106102d001c40c50103800e40c0203c20000d50200040100010901414035030319a44c46c82100840758611540e82d036070050900032420180c440d1610240c548081c40052050310240400f44043e203005c60301c5180d0070030001070451181c401c000028060701d02c0850441c3c16561868060051645152101e80e450310524250a41c5c1941c4080000002000390b19400c0307408030300000d812111100d0f405802ca0303071180d59000f28203009060201030b005136500542c5c4200a01d500280128250001010130f0042001c0e40140349280300d02000410b2906001840e18410100740b001030021292012a060a80c01599000c5020850202009c40c0c240b800a036082541d45594000501380701c4540c4070f4080242d02645e049400d56801001d00407082c0c0d100e0200c03031490751040703110851760502003400b10510725440b40501120a4240405148911400c00d404ac1c88d81d44500a0000c0d0611b600203500301d501496200c0e01007440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 513806564 1250 513805314 513805319
    0x5011706010f261b100203180112020d090605090106050d020a0e04170d06051f2307020306040c0603051008061504020706020c060a050105240a051213020109 69
    0x5001030814107966110400150140c03424100085540c564503103820060343c105900380b1070301820400724165150440382e1385100d5103854144424000d01c88803110071034004008510740c003410000305607034440081c80d10034421051140313103c00034051010343c50300503800c0013011024010f407500624000c501e12802040030655601c1044965110200c0c02500011640001c1018417181f1170a1940b26020340204a03520466040d61000c55004024010b8a140d64120a110900302411560315002d004210b59101c04020324014040c0d01c0901c0c000345440c01000c03c0c004c0340d9a0400305031307a9520b501178104c0390f150405181051200b2518010f03000003d107032100180d20010804e603080200c1c2c1805001d080152682005503500000e1080070903080740d001c0003990300140507840204840888103016100c02d080c40c2d4090029a00706034000c5109030041a0343c940b40f84000042c10203041c442c104226900c01c615602a505030084201d40e46045650108200101c6403c07170311041d805100340d8880a500c1d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 513807814 1250 513806564 513806609
    0x1f090e06010f050a030b130305040e0405030310090209280906060302180108040f030f03090f030c03030e030c0d1b1b080f0303191d0d0e271306020f0a030501 69
    0x38461711000d02102008004982d010003c0c1d02a00281806072a085e40350a071101840e0110712000d803000c507120340c400020400b001150380106009400748400c00e5142030340d01c60004001117600c144a5000058140c064071a2051580829004025180d420b000103942c94601900941040c40841d82c0818001002e002e59072080150902c07030340e40103110a91034002c61300c0c100d404100d0210f80078207150f80e4045036004101c60300e003c103400c00d00c02d541e0814100b03000d18005054070820300c0d0500f003503441800020a0180041b030502d031084154901540140f1907025007500b03040c40200d02500c00310800910300c25520000840c1e500361082203049a840d000e0f0900c14035a40d11044030f0b100c4410005007588419400550820380b81c0e50751011454894990050700c13982444100d22422000c02c18122012215041c0907102c0b010302d034076803030107a40e0440c40c2c000c120203a0034005100032501401038445004102c440c2c2e05a4a50250791200242c840d40c0141d405001000d00303000c1c80e20341d1411b908440d05c440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 513809064 1250 513807814 513807829
    0x40b01060e0321041e080d12020d0501090c0e0109060801050607050c090a091205070f12050d0c030c020f070e15030712061401170c0603070507050118030e010203040605031f090e06010f05 82
    0x4800301d03401007e030640c40010480340008180b690810725a02086101002102401464080e040c40400015082034050002d0b1140404481c41c07418400407602c10030005401c0500281101c0b000d8410f07aa82c0c004600d0702074206141001c601c0c0d8440c3e0380320f00380482c0240325800011440d2140c601c9841d00101e85005a85a004100004040c1e0010040010004018080c40c602c00c50040c00c0480c2072444070b198403000e8540801c040c00000742e48608800d03c1e280c0c1085408072501d00c08000e030050300c1c280b516648010a00030640c91405c140e058882e5401c1e101002510010640000b685008101c0e070700d003800250018409540704d005906001003010301d0011000d4081000c11070080801403600814464107801c0140b41c0d009100080c41501c000c03403020f00501c4484030034090180d401801c1880d002d02420005002d25046600510051000e90f800c0800c403500145c00020000c01c2c00c0356021078104902444e00094941424424000e00400c0c00084190582e2300070019070021503210401d103c1d44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 513810314 1250 513809064 513809069
    0x1b0305071d01230301051504060906030305220e01060305040309050f2d06041d011215090f0f03031a190302011b020a030b011a03040b01060e0321041e 66
    0x15910345100402450183e12a0500045243c0f51040140148000001d084840403124090181c00301d608508040c60300c0e1003003001a00c1903080c104140c50443c1c40084c8907000e900b154403424004e0229005054100511440c000e22850030f0003042c03503840c1d41005000c0c150030340301100070440c4080046101c0c80c0100f0103000d0158040d0104070819841c00700c902ca101c8254170070380280314201150f0100e6459500040000d8030850903010030140c0c3c2100304485101c4142d0043c003203941c100e400703c00001c0034003440802c2d9014075207001c01c500c00d41c1d0030034608400e005600100340c02c040780164001c01da0190010800c0382e40d10316841004107290002c0c8003103170346604216444915900740c14001507025120ba4030001040801c481d40c454507543c0401c10703548141d04140c5452078004010014050303600c4084000032400d8201d1801c509060b907a81824407810300604003030210fa1410003040d80c9080107080303140c806c50074030800101d803402c5da0300010340d00c03d001c0e03122030201e9a85103042598007411181d08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 513811564 1250 513810314 513810359
    0x21b010e090c0a0311190e06030f1906080610150903230a0c0803031b04080a0611121005030d0804051c18080c090f16030e0a1b030507 59
    0xc039a50b8228405031a40f00307601d400d081c5581c501c2c9240c0400e6102014120f858660426102c06494502010341101c42e030954140c81104104100702401c5110401260080880f9060724100081c060708800546840d401150007480f45a041210102400c82071030110380c0b000610b1103c00818041c201ea0030102e601003e00200600c09903c4950b140c01e51130412a002d13118151a038002c41d0b0340d00c04501c00d40702e50050420354404400e01545590841d000c0c48000c00c21106c0600e0325181000320354031803a5051010385699607903c041d90140f1010000c1310303da18521002d848240c6032030107a0708001d911500a0328028814102c00c00034581c01900744a003d1343d0411300801c3c074110120304c1e0101810040080000f04000003603140410400005110040c000d0600a4030904095109014601c1f000503c141c451b90391050034000500e107100c40c1e8200440440ca0081042c0007200111881d01800c1000101007038045903484485044810705002903c2c815420707222115540d80d40c0500d814440d210620 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 513812814 1250 513811564 513811579
    0xf0b090607021203092e0e1f111b0601080c040902010903020f030f1006140f090415020c070303020601150f02070b16140a050c060c070902090d0b0403021b010e 70
    0x80e03481c01d44801840d8844202c2d8121040890071b8803681018a501601159150408851082c580315490140c620004d09a10082c030040081094500205a55941c0420190365809030719250002c0b505c1116502c000e058071080c3e020303140c0d401d80d80e43e5174400d204410040c05420800202890680110844650140e4840d0f41603819602086058804c202140380d00d481222008000e07035805100303d4111410170100041d1488c170b0a920411904c0e10512441c0c80340501030806159075480c3c0c10380540261f0031814030405041c090606000a2181c4070103050340c1e10854500104150f070000b800c0d4107a401102d44180111410a001c1d250107813204a0200560401507081c459139000d14050000f45810011070130340d00f561619842e0b003080030b40c4c01c81c2e01241c012a4442e400d00c81e04201d580502c22094460302e182c01080016035803a001180962a41190009060032195a880345016241d581001c1c4422083c145458040d64917a0b1070b500d80d460980b030052002c90b0301d60149503000301034a070140806 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 513814064 1250 513812814 513812833
    0xd0516090807061218050a03020604050f0d0c112e120e0706140f13030209070c05071a0702060d0506091014090601020a050d02061e01230310090f0b09060702 69
    0x1040603144102d002c03207102c141117008001141c410006181402d00907000342900b805d05003003441c141a0030300030300c1c074581c5c0c40060340300718140c0e00024402c0c03d03e070000c0c0382c154003020782000100c040c1c06039041004001c2c8440d1250024990a803c4000c05515985410b42d4030105804aa401d4072038141c43d40070141c01a0b007040288a0003640f0308503100005950b0300e03240c000390340700080380c98100c80200c1050300e40780032041c021414803402854010300c4a04000c0c8010070580c0c0d07003503582c08030390090780b541c119a01030108510100605940c00c51360b0003440c641d1134803102c07800000200f030112011445441410085280140d1031729062050301c010b103001f042014030101c10b00800c42c6025180c2030440c45504a0300c000b2480612000c461030ac107a501404044c18024000e24120034180c0916900100f0f0100401814a004203682100700500103034a480d124404d001900341003080d4003c245081c105040401000212054842840d10a42c250002501d542314250380d83c81c0110b03429005640140c2d4807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 513815314 1250 513814064 513814097
    0x5090907051504030803010f0911091f05070203071d0112030e01050a1704050a03030c2a0c0815010f0e0603190501020c030d15050301151a0d051609080706 68
    0xb039404035140032890362616542e03680b60f1145a100b680507013501c0c50300c0e0000784114422401002d0003080c4107807c040c109002400000da0090701c4c00c0d0781200c01001c411020690301c0c01038099610b0150010192001241c2d5100c0780190911951081c1c40d01c2052400013066070340000100d4288e454050f80ca92240101010040d2181d60201c0b14403403e200054200d83d441c0c8004414161007540b280020703151902051802806036641280324030240700c40310800390814424030900716011100c40098803045280e6080c4507100750500c0e00099100c2c010071100300c851440300e404040c125140ca15034083d6042d901d800e40240007a05960495140d0011003d105000342c20b6812000200d0140d40014a0117680e00d0140e03103036031b00500c4d007014010384580700d0120542540741440d006000a60003071000d0007400c2002d000036002c0e070040c81c90413884501c42002805c0c6031f205032080443e00c460200403074104a1030483d1203240d28441c0000150140b500403641c0343c004a00001102d0107611018070741f001e030000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 513816564 1250 513815314 513815329
    0x10050a02100c0504240f030b0f040f0207021c0302070b070305040504020903150a090c050301050f010506070c0816080d090605040b070519230712110103151e0509090705 74
    0x1d4034104801444045070a18203030884142140e007a0340c0303130382c45c3c0324404001a103910502071800c2c0a0500d421400d10040c0c6420089241c1e54200b1603000444980f18040c01000340103000d0040d40288010340e59408941c0070a00603104a40030307400f20f40107180d490110248074441c41c0c00c000c00051042c03204100c1428203030080c10514000409031070002e09406000b82c42c900302140c00c0c1207416101e4543c00f090181c803c00c01d4003c1c000c0ad600070302c101e241422030040200d40610845001c0e50f00010041c041c003004480f4103003c2c0821100780c400107090524842140705080c0192401405001084491140600a0801200c180352610b074140340c80c1404081098001400543e42801400817900c1e8a00041c0c0c0d8001e1214032808040c2c03060f9101942031070f1041c840c00400082c07a8459002440743d45400070640310142d0b4803c10040440b0382e104012005408034072020416074450444c0810960543c8075442c00c0b902e09410842c100c44c0d0340720104000c4c444243e4401c0200d07001507000340710b0b50606a4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 513817814 1250 513816564 513816581
    0x1080a11010e03030910020309040c0314131a160f050304020d020112090c0e150a080a15020903101a0102150402150f04030305070614040b132306040210050a0210 71
    0xf0b081d241000100c1001c6094000c100000400582000617042c2103441c013071207034060082062508210409035681c0f4010303000400780c003400810010074001c0341000342607541d0003040e0420080706081401d0100702c0d880301908000d11500482c1d44d108124400d944204192449160010526410300c6500d0b001510701e034030700700c000000c00c44d200d0000c2d202003110b201d4140c2c020620b4140d0b10400c1d281254a40e280805941d003100c2c07144e1743c002d608201f221400110038255540000d80b03080103015030035140000b48151150b1507054094032511741c0e1480c540c0c4d800306042806403030f02c40c40300c02c4490300126264450040c2c0070148410350030115015052a150b06110154544001480c10400000c218850340295204400082d0001040010000d460043c04211160400c0c0c407446c0342400c1c1d0710f8192011000340305110b6600219041d01c1031204040b4054110f646901840601007840304d98a03840d904201e070281d0098595004404d0401d10507400c880803040d490f03020703140c49980408140007030184c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 513819064 1250 513817814 513817819
    0xa02150606070335100506040f090c170703050a1109030d0c0606031707061a0607060c1403100e06030c03120d200d0e070f050f03030d090804050901080a11010e 70
    0x505025036218120f0306000040e0740013071445507082c45e00c180118041c40080d0000c60050f01c0c01e100c2041201e0040302c002080d10248100130440400381d2000302ca069040910401c68008007a003405180760b01a8045401441c124106000300d1804145c0302c07240348203125081d901607105e0000745074a640309640780d00005218540c0030580d25503a4403a440500a4035000b40b8134200005250b030101701aa00c80c1c80b100035040002100464074200004400380034080025001c0b5454603000d078141d034842e000b080e5481200ca009aa240e040c1058030010000302c40c007440717a645005001191040c640058400200c2000400801b580031904200074101c2d002004c54083c030903244c3e03200809580240c40e9008c442514810419121000ea06200f4255207903942d1a00c0150003050050014014800da4a4183c5200b96409111005c00303c002c203196200c0c48060311a581c0c54480d5003420054608000d0084820031176492850b40d0703d13869410388450174064018030800440c8105011540078040c40d64500800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 513820314 1250 513819064 513819107
    0x160510031e0c030c0216080604030f05070605010923090c06090a09020c100506010e090601050f0c071508071805131d010f1109010804080309070810020a021506060703 73
    0x719603903442524181d020795004242c0307502428452660400c14506c11400e54030b0325948079460f00300882e07225000904081c0401001420400d0703a1401001220300166001d00d00300b006682d10349144001740411000d00104040c044902c82d1010803024105000f04c00300c3e0054404143c2e010200300c2141e0005100b03a0700710100b410b00007440d0486101500f0741c0d0109001510040c9042d100f81002c459008100a0601100035007202140e1541107030507900000038205140d0300d1b2401006440c190069019440d4144030382c07032011074006041e44514940c0325030b64a50300c90a80343e041060b602c00700380d14144007046107800c40800c22843c0095040102c00145080028800303544503e85030440311105d59800070341c2d100c010803000521107100b0010701c0c2040104041c144031149000902307610010b00701820f007030004000302d01c80ba17109004030402004000304803007107410603001c10400707500f00c600300d0005406a083c0340c2e8a45501003041c07a100b20002000c0502c1c100e8a5075050b41e440c0c41030300200100090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 513821564 1250 513820314 513820361
    0xa0e0f0d020306101a0304050c010305150307081f110d0c140412110306090d0c05280c0623180909070305070506092d04090c060216051003 61
    0x7003d0081501400354084c4d01401d045c10254542c00303d0751502048001400704004101c0810340209910080c00024a000f140f1500c2c1c0d20613800b82ca401c0c400c40c0c5541401104000600d45078005075041e0b088103411340300c094207811154460704031000c0500503490030008120307964400485030b108940140181c10082d4101601c01071901041e002504403071144200340000d2401c0c0180c603041480880001c0b0028419858071402261300c07200c080b01d00009120b4602282010003000748038814903000c002100103004400c0545000c031807000c50701c1c2503c2c002010840800c288d40f040c4075014281d48050404145071420f0040000c1c55840314500c070003000c010420440d4196034100340d42d4066000c40c00240500c0e07056081c01402c2502c1030303100901c550402c0062100d00e446031509900e06800c01703000d9881e030400307401c59211420a0300c002c2c543d00618004001041280e819401000e64500303a080320030018800d080d1001c010310038007a50354451006002c882241e40319410401e0002103da044481000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 513822814 1250 513821564 513821569
    0xb031e1c03110a210c051c0f0504030806090f010308270901030c0503010c090e06041e09080703030e0c0d0b060a08030408010501030308100e06010e040b09070309050c060a0e0f0d02 79
    0x100103204031070008603100c0e420f03140110090891944540c00315030402170b003907021001400522038840d0740c00142680c131403000050150380c1d00000c0d405840c16020710080c542460010a6103000f110440c1c0b18110003804110706032090040141a240c3c055401407400c40706441030b030490703011031048240042e0007500603003803900c80b5000d0600030752007841001d90703882c04d210406013500e50000c11030041091010302005007044207415582c00c0901514001038603100380704071903640d00101944040b050300b0302c0320000c200b2111a008104140c020741e0708102c0c4040980c080e1351543c0c1d00d00807160b8803502d000207060221394040202034018400516015616955620490a50300300e03a0004031940d5440c1c0040050641041c5403d60103020303441501d00060074610f55816100000e01240d04202c040c8202005a803140c2d8007902c40c084e8010140003c501d840e040040c0902128403040b510388c0286a2113010078244042a0340e9065000d840d45001d1040c59014050b40700c941c1051903600480c80f81d804800740c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 513824064 1250 513822814 513822817
    0x204020c010e06092109060706091a060406090e03030a2c0601090c0c020a140d0204020c0c040f1b080603150c0408070f0b0703230d0b031e1c0311 64
    0x480782c2c00a0036042ca040910380c2e05124510070303c0444840411816581c400a420440f0001c0301c0c11510940c5895071803e2440007400f50b490300411010046440c1022696180c0501c0d02c1440c044800f0302c0940d440300c5801c0705880054144c0c5120383d1040c0080740394130b09190403451200c00e00d00d041c000c8049803800c07011001924810284d070542c12550051041030024064032140d001c0904048081200e154003041c2c1036003c6101e0616842024000b21a5540d10745040d07032040342d0020415525a81449641504c80008940302c0d88a03605e000e803000245200c60080b01210151410883c542e1003070110f054804280040040781d16004030744071030801800d580d00d4980142d8001c02000c1d02e0340e04110510345841441c0c0c1201103809035806041042d107100d001280e003215410b161401d85110b4a5901c841000090f40000205a00105401c14540e507154001c2e000d00d44203d08650f000c55100b0380507281e10080000340550341d004142101407070714151001140240f06440c0c009010540c0c42c100a46a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 513825314 1250 513824064 513824081
    0x406050703020712020307031403090303030703020c0613080d0906020d0c0f08010b0424030b0d050105150103090c0902031e0124111f0b18010f0e04110d0204020c01 72
    0x11400200d04082455410070050b40035020350201158190501d800295a940e40303440018000003040c507200003501c0c41482510742020019040b01e8a80c10510f50280281d004840510740500c1000009220540440f04142c10541c0098403136240085501c0b48001604a5a5060f5a016001c2103020343c110b0691051805030505070f6200440b205907400300a00c0b034103040c0e02035860b18505100520090740380032181d21800c0300042e1065151030318044140d0281002e0209554072241c4200088280320043d040184100c1201003403800080031030005500f00e5140500240c441c01e40d004041c002400705a00031a00207210f100c8150303a01400b41c0b06444039040981141005c800d514030900440c800c0c0205032805101a4144100c503010303038080043c0e0f1164076145040c40061441d59504c03121100f68003a403030010001d090410030742400d011005165030284140d00101480800004155450300c221501503940700340741d05400e01d811400c00803900707403061050780d0082c4e00b0450b0b4901d0040c01d00c82c0804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 513826564 1250 513825314 513825317
    0xb010905060a060801030818040b06191211090d030318051c0c0b060f01180905090c010c05030a080c04051f0806040605032d03030112110301090c03021c02060406 71
    0x14a03207404001e1241054981d404801440059801400016641402d45101885440c0c03031090f815444000107010b8084864099042040041c0800852421542c404a101c020341c450081e0b46010700503140c11104000303031900c41401c062240200e0340c03030103601c2101d22034041e2902240c0e001c206440c503c1400e42c84d613000c6030079921159005038400c5411a00c146c1c03181d0b01d810f01d640240001e807901a120800101124498800c0000d810b803540e01400031a0b000c40403004244c84400e4403004840e005140513110040030344140032600300e041d0700c01d003010042d41d5880300145052400c1040c003030f14004806081296540c80c24040810b864031450340e001000e0444900c014084c1d20b800703030082c200917800780510340a1070038680e007440140c5000404181c0d071007424200041d0000b510006080c00c076056124529280000000001d20540740c800f40e0910a000d5070004190070080740401d4220f45286030010301d041100700e0100050300c1c048014218000210b00351000443c801ea00203616039100350080300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 513827814 1250 513826564 513826571
    0x10c060519180309060804030c06020313061104030203070b161203061a09040c17011211040c110d0203070c12021903060204090b12030f09120703050c130b09040303020904090b0109 79
    0x2d00389688192101d000740701c3c0d402c2c1342081e4103040d10018084412240050f046d140c00001140d03c43c500c52010142241c0c10030401c101703503016407082440c9036100b80f005078030a214051020422030b2451048030703924081a40324454072055a910003480441c56003000701071550f14800000c01060101170305494845c0c50380074640c2c8501e54010081100e210a0b5544104440b24903452100340409240a05403621483c0c517071f501403502d00e414440e8000e508003030794000b0f05113040082020f400001d245a01c40c07601007900c20240c0718090499403409000d0000e42102802c6204208442d44610300e42030b164000f4000e2802c0c4961000e40e0b281002e600d07441154113690001e806c006007100d9104081864208852948040906038012680da004203404502c032201c00003010000740d41c4091008410144803000e031002265030342045511841a014040d0244002180f0b41014824612554a51441c0103081901ca030300c2e191400c50080d08030040080d0030a541c0c43d08040030a49101030f45008200310203010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 513829064 1250 513827814 513827861
    0x11070f0806070f03050601020d0e15040f08060106080702061302060904141602010b0d061116060608060c0a17090102210907120b1f03151b020c010c060519 68
    0x2880640704455150130145464103004682ea400b18250144080030300d400c2c07400822840004018160816800c1c42c1da590002d40040c04080302d00081c0100c904440a40d92680e03618241510542411034160005030455400a01074440050360840c074140041c14041c00c08503644080f800702d80c1011110800c0b1842c81c003c0000c0c0c241300d4006a2a100414402400b01d50111070100b0407480c01420020105034031480392412164a500548460141a20b03000080388241d040410061005004017000c9001303400001d400140c1c484111049600b20380d842103041d03408103600c03101401018002007100e540170051540d41d50802101c1c0610203c1c00c10201800381407141c1c02e246820007a078003607120300542da01c48a0120f45001885a40f000c03884a4000906405040380302c00c900194100808240b044c442d800950344483d80b01703514818015401c07071484000e2030001d07139444100e8400e05001a4807040090000342e05500700e543c1003c419044a011030030110301c1c0d00300f41c3d000c40701241185005c100c100e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 513830314 1250 513829064 513829067
    0x1202030403080c1c1806030b120106030b09161a07050a060204081e060c040b0c0c0a03080a030b22090305160308040309090204080309040e3c07080c0111070f080607 72
    0x801c0c04d100100e060901003c01111390040203900144202000d0641e66104a045900e0702c101c40807110401c0c900030040c06460349803c90392094185e0b18881c15210f00c0455030031040881d00180242c1391407011201400c8140c0c20908419403018608541c2c0340510034038000040c0f204c3c009030024250000c054a0000d008000c0c455040e1044c2c0c01d07140320340d0b00000a0100c2a031a00c801c03641640d851740940c03542d960484079100d00d41001c9600c91034001510005c000709014240001c1c000000740b80d60705200c40190042045142c190101103d40502c8000380111409032495101110461190407c58140102d0094051307200c002c0c10800d13004200420104020168400303580c001500d0100404c500349401c00c00c100342d483c05400f2090f03000b5640d40c900e5064510040200c041c4040b00d001882c00001c0d504608100800d8105000214541c80030103020825000410020140c60001004010440948004540f25074440344604114000e50001040d084072880a43e005000303017800a04403400e21650 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 513831564 1250 513830314 513830353
    0x2031e0a1202090609150c120307030605010f020705060318030304060203010819200a03060c030c020c03030c060a02180904060207021003050c07030315150309020319030c1202030403080c 82
    0x41c45030a4410440001c2650303945068a102500c19944100009030070845029a84598202c408640c420101d1030700c8100e018000540c0302e107034241d42c02e124496031035006450f00d1320321010703d10258000c03042c1032002c0d060a0303020310fa001c0c024014100c0754021074000c01e415a070041c0c9059a17010b8000005100f03560b4100002c0414054102040e801742900380c90360305000c1400d48581c0c02c2400c0c448481d024585d21454140007561b084441080410241c88001e0000d0413902d440e18050701450040c40301c03501d80801603c0e4030301c0c5660041d001503601c0306040341c02588826020580140211070400e11078480b0b000c07051045120380001a66600d40740100100822040950002c0500f8a0104038101911005895410f1382c03504001c120040800003469580c400f5070031001040e018030360b0030391142c1d070703d0b0b080484081d00030380503100c4443d11807034031250192506002a000c25111540390001034004218200c0001c0c41d481641c0c2415140d564012281d401078500503860341c03020b00e144012a06284 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 513832814 1250 513831564 513831587
    0x3030903060b06072d06050114100306080726030c0d030b060a0c02040b120115061d0907050c01020708070821010e160c020907030624090b0a02031e0a 66
    0x83e00f850800005944489800650695003124140398021212035136090201c400e029583c40b010902280d81c4034101340b070743c0040f003da0081c403c4d0030801072001080c0c0240309541c00d0700e41e85000b500105040c503080700940c1c8808075150b02100451192440b032b0f10400d001400e01484000f02405183c02d6020f4014182c072180350f042d6120b101c0c02c0101703d44e69034100d01c00b03030540790f0b06440210f500c0300d00c4400640c80da407019a00081c19403d002d00c04041c8d50926000c0c10075640940c40b0401018902e019050700d02d07260301031300c581200c0f8407404104035078002c1d000f41c0b03001121000050300d8441560341d04101c0ba000040c044a80090200300da025107a03085045180c00e076280140e00580798917100d010804590b002e0301500d03000407201c0261106502c2407000a0040c1e4002d00144510b061440e4018010942441009007000d0071803107400b10701081700c0b02c0111050340d1307a82d8800500d04000d07a142c42e550080050f0015407004011400400400003414040007210f20401500c8010810020b054400c250 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 513834064 1250 513832814 513832819
    0x105120703120f02070b12040204180501051005030f060103050c0609060403080a0903060b04020a02060a1107053f040501081e0a0e0c0402120c0306010306170102040302030114040b16030209040603030903060b 91
    0x6010340080c032447c0c902070940c00303501180e000c512090108c1e01010104614403000c0e21715400e100c00c005415800340c1c0b2940407244240c0072107180c2d191a00c11952220005e0200030256040940480001e03d0100c0280424800c020b0045180a81c0d82c0d8841806a04c016583c40104030011010824045c445c8500c000f000010785056103000d5202034029141d030b1000b049414100e94406440314100e811605550b0420b6000d03084403081d08102055840d07801c80340c0d02c10102c0c0c0407070307801c061402c452400103a0b4540d0f440c1c07922141080c0c00c020065403201402050000740310100180803d0300c20340300e99000d000c0d42058000140c42041159440d04104da11b00145000d80c4c0100300ca10a800d500c403884030707400007050001d43c1c0c403074840c040102c01070080d647c45120446400e907844203060006600900c00c0b24401c80080000c105001701d5900c214004030380150020038407000246681034158100205042d01d86801441d20400000080456031590029800035880301c2c02482000344038484c010720503004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 513835314 1250 513834064 513834067
    0x181b0819020c0c041509020a0c0b010504110d0504030203190806040501080d0c062f0c0601050f010c0b150a080703032007031419060b090714030105120703120f02070b 73
    0x41d1a000c1d070b980c0f402101040e00495694a002160b91000c41030000a0701c2012002e43d61100d52000c000c00460310054155102d40c5041c00004552409125500c1582d04202c00f4900b000c1401810034001c0c82c0c000c00540950000b00103140b0003c00041d02808455015118208507041087c280001c45805801600807540800e0312485041d4005100075100b55202d000401c8041100900c04181c1d046110115203600b00c0300b000b0304555900b40d01a09142e0f60240480b64941c0c1e80f481080b011408203010300e80460200c141d00008a401e004100c0d03130000c004100000d003400c4810125010503e1644000441d8004010030300c02c059000400300d0450300501c221940e039101c1c84840648410140c80000d11101c4c000c01c3c41d00146405100f42c0303000701d1020007241da8400701800d141c0c0c060200301440300c4c0304001200018903018014000c0b0081aa0308105042c1141e0a00080c81021000b001540209108410001000510f43e2119103611040741c0d41d000c40c3d0b4445200c0c080d1410314242c05c0841d042c17a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 513836564 1250 513835314 513835327
    0x9090c080105010917160f03200f150c120a090501080411010c0c08010204090f0b0301050f1621020409050f240d082101050f0901181b081902 62
    0x2030040c10007080e9041703096645280d100c205a0b692600801c1100ca58003410716003000580e5000c0c0c10322040448e402580e0b0900c03041c10b080c20900f0103148210085601c16601501490b8509227450000703030b980b00d61000903181c0204001104d260441070511041d00e80000642001e03029444641b0700010003082c00c1c18400c2c0d0800703030384090324004207031242c504000c201c032816824041019a10001400da0400841d66180c644480300083d0419213401c0d61040d08209400026040512030244150103207004014681c850540003000f545022201328100500d550b02005080442d281141c181101c030840184c2c0d4600d032810200a079000240241c580c080403401f081085421480d60481c40500c00f80f0606107191810005120000c5820014001d0040031600e08004c001c580e1100c0d1684140c103a20a201d41e03030f14020401084110320009400010408c0104050024074640044030700d2000e80115140030074500d0003100558442541c03000a15910501000c44c04070b120040c89001c4e09007045d40b0f000d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 513837814 1250 513836564 513836567
    0x3150306040f02150a0e1e0a120318050d12020f0312041b06080a09031e181403071802040306020c061608070c030807020a060f0c020c121507030e0303010609090c08010501 75
    0x219541c51b0f0f64014010707030b03040b050507604e80c00648805a4004000c0e41300182c542d0b506100c0010010001c4010409104514582040030301c40305040b241d00908641d0210040d5403420401c91048603c0820b40c0315030074842c03c8106061015184007240f10b0321807801850603041c80700313042c940020100e00280391038a013440074550000b603440c4c0c442030f10b400105d0141082c1c40d0440f0082d492003104450f869014000e01d410540c00300700c1c40e000400d0303030a610706640d485400120700000c14401640c1d141c0c0c081c20080140381d0000c00c5041c0c01d0107440304014280350382c03078031004140e81c4411184c3c5d16540020041182c07030b071340d04428564001801c0c909041240750501c00a8000054000080e060020303810000707002610070420b0005056001106208507019001c4010181044032110300241c05a92607442c00b9042c0241e0400d074180c0d0745801000344c5400c041b2045c694040181c40311040580390301e400000d00c0404c10086000b411981d80d00d070b00d40392401002100f00ca80085035002046004001040707140e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 513839064 1250 513837814 513837827
    0x82b09150605090f100305030d050603100c09090f06080105010b1207020c0d0b040816050601080f06090d0302030702031b0d0e06070218070302161b121703150306040f02150a 76
    0x800b1000444d0740e982c48440200002c00001d900082c21880005800000c2c10843d4201c02d020314410f070b00715170103060212403440503608507600c240000796200784100f003081d50720380004e030500141c2e00000424980712081207080d100c00342c0186107070000c0080c0284d0f07041601d0740c0003644103600b44040c2011501440006040c1c050148000d03011142000200341840340320003c0f255001d84668811080c002a4507040388c9803034003442201024001d040000d1402580481c4261103141d080c00900050b5a124505030025040a0015400c5100500c44c2c21140740c01d200c0900d07400410030300189802d4068460080c20301e462002c085028050600021006840e10034400c031030001020f09401d0b40e640c508404400a01600a00000101301e551100c0184015500504040c3c44061001c843d1142c0710307501e03900c14440c50a00140b50056118071882c0c0600000040c5070804000401030134180d19100009140c024190307020303504000420442000c41c9400c9000e0b0000d0004000342c0e80c01d1100d903034800f0f440c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 513840314 1250 513839064 513839071
    0x50a120207031215080106050303090306181e07080c0a08030d09031b0819050c03030a0b01090b1b0d030608030405130e120a030b06090d082b0915060509 67
    0x2595004512402010b00410812071001c0c03142c9001c1119808611a50054020783d00c15141c0c0da51800030081381e03500b80802100c81c0024080c3c020106500e84e80440b681c0707492030041502003802014407a0034400c04c5050388841d000050070042136141d062644640c11300801c4880103101c0c01002104001e00d8401000380c0340f010400c0c203800140d61a103130805403403079101c41c02590600380c07140c02d1030070401c03081c1009456003c981840e5410352074403040b0180c4031072107000e400160302e52091000504080d90703034000348011f0b0301c180b428130710055a408805400307070042101d04440641c0031340365803880741007085030003483d039610302d0184101494210210f45900c5a4001c4500407458031203455503950958209070142604007084460880000d01d06000b075411040441e400617041281c40c40062600c40d050b0341031030100500b0900391080944d5107070015070007a4241412907080805019840c4c0c103000f00c0701c840f000b042c0d5021800aa00d403502659210700f842118030624a01107092040751260b019180c0d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 513841564 1250 513840314 513840347
    0x30b04140402040c1e02030a03050603070b1b03041d0a0b0d02300d050301050310050402090708040204090b01091e0504110d021c0c0e010909020d08030a0609140610050a 74
    0x350402e40c07080c05c58900b9070040d010700c117850807956481d10031540003005100d02c1d440caa5040110381c130380104058840c000742c031541000d03060611603101004985024101507c9a2000f00ca181a80c0c0343da100d4404e141c40000344041c240b8140810007501d5190040c2011002c080754601814a600c0e030004825030300507541000b0302a4100b07000c40c1c0120842c1a03500488695401300e502c03000800310000c000c0da0090013914003d000c3da02502480c0e55083c06120b005650003407108001e40d440c460111049030b0001c006990064030782140c0e00102c3d424590b4240604138404010896400a400501c5a4080100ba00c45060319003420440484d040000000c044101142d2170300c10f014807400041c80ca44140b5030424002017004101408000052108400712030207aa5101450781c3c0c4c904801080311201c06002c0d42001d0000450400501c41c10011980321104460000d070081d1038244107412501c201e4000303401400e030742c0148040ca29005038418658000d51a003189403006922006007081c00000c100788 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 513842814 1250 513841564 513841571
    0xd030209010e0303040b1305010221031b070f020a15091a0918011e0302100806240702090f06010f05071a0c0307090e060d0206070501060909080703030b0414040204 72
    0x40c01a0b01c02c0141603880d020043c00c0761703241d5848210f410056806001c4214082c41c0060000505500100702a034529100e080d44600c00503100e04204126480104020000d2050f1304015a47c800761401a0070510701450030003001a0851051200140d0760340c01004048968074512560203038080d6145013990728204010198240120a003241800754414581e44480701c13540400070035014501980c100d03400c00078041034241d142000480402c0c96400041d400014000054080500a580440e0421409818020700040e0003070858036410048019107080040010a00198607001d00d1054020300210500f0240b800e11100182c203400c05000c0e030900b4030102180e0030003848409040003100c2c6102071580c0e14680340c04a550055a4412501040030403a08080414540328030388482d4032840000d012030501030b101d0b4080214640140201329565034903001c0100300040e250060200c018403604034191500c0c0c80b450f01030240c8005281e032a020b02d203001c100e854485440d06195030019016103000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 513844064 1250 513842814 513842827
    0x51507060e031b1b0d0605060d12030e01060506040e13030309050318011106010303080a2f09011b031d03030c1606021b0901090b010908060c0904050906090d0302 71
    0x1503024003900c0e41595080c0c00007054860800d20003d50280400c02d03940305aaa1515810414010400c04110096044a180010240040e00a505c91600007400418450044030a0341e60b00380a0031000501c100007a4031441e0ba04c004a500340104409410101c40040c00e15051456440072400c1c000e040030301000340326150b0400e140c0241d100003ca00c2e008002c0c0c2e03a81d0700307a0400c0880380c600c180c2042400502d03488980080c4010200d101810382e42e03d0b40d00c403481601c2d555400300291001c001d842c0030b89503240186800313107010403002d180c0f8007048071901034032058208000b44c000f102a04803401c0ca5078603c1d0140c030009600c4500100d5812054096031003001901010071300e0350082e086880d880d8824501c52500c11202d0382c00d41d10844d20b00340d00716480359480b181c155008515403070656400104003030040c000c0d03d02c9034011074040c0506240654125a0f203c00880ca000415100f2102d0008d0000d4101c0d9907090a000e00c5900681070b8004101a00700418401c0e56000d104105034201507001c0f0b41c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 513845314 1250 513844064 513844073
    0xc070305160c0b120601021504120e0307150e0a030b0406020f0906070b0603010f061424030a0e0705010306080d0e040209060c0606040b0d030801060f02160315050c04051507 76
    0x1407804603074024980865198070350102c81c01035030088040301c01c80c540180010300c55610006010b26524074a00c2000c41c07a48503503981d010103003070700842c00040c04040030420f50346480400481c001010030120882c010140f071100038004140e02c01d0340500844c0b40720710500100e401151042d4101b58000300040c0e803404c0320f802d2400e85c5c3c080e03903407103950150002828200344081d10303c40ea03009140450007000780070040700b003e2045540c14803403000c0024014038940d90b00d24111380018100691440d00c0190301417601d1305140c45500440d07207524501d0b0b8909014039103070700800c2820302606027802e08210700fa080c014000e80d00c0044035608020002c40c920420013640352a0190b90300300401400706600d49601481107074640e9402c40e00c40c0d0189180146010f003038546076a80060054258590728420707424454100c98184210300c410042d8898404190361801e00303200080003c5008580442031200440c941500751000a00281d40c4103070144014089076440001d440141c0402c000ca203551454245071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 513846564 1250 513845314 513845347
    0xe010509040f0b130501050a050906030c0607050f1606140307030e07060201091406040309210b01060806120105010f23040c090312110d0807020a052a090c070305 71
    0x1145400c20b0400d42c000b01641a5900105441e0740f00f15002e00c8104001d000500464009206484e130000b01c18804120905007900345542000024013510301c84401000410100d600506e41150141c4c00344240c109103450500041c0a030b45a1071514480180c44c111004050f41c10326005881d000b080000800e08060080c0c1c03282a01024600a4030b0000b5034415000c0d00810040d20141c6206140e02800d1454080205401d440303550300da12100c0b8050b00789140e03a240c1c4501c50300c044c5440e8070740000100100325000d034564000d04256480491514001c000e1044045403441c0d0040c180c1c0c14070700103101034070f02004018280d0710442c051010010081d41c0710402844201040e582041c68042000f0743c4640c06620101a42e000c2c001c1c680c0810a403500c11581d090894500501c590080140482490700c11250030750040024030460300c2c01403440d20b80c0c0e82060080b200c0710300383c4d0b000c10a02d10b2841510945001c0b0013401216490303207620b03260109110b184501e500080401c000015807102211400782d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 513847814 1250 513846564 513846577
    0x8010e090f06100515040b071b030f080717030603061506040306110901020c0d0b070302070c0503031206100905010503040b0403180803070b0109060b070f03030b19090c021c0e0105 79
    0x1400c880c854200f00c00610004900c03400740500030b26000a440c103460f080401150101c405010307509251003d107444080005502071009194008021400030210326104e085907481401584400d58034800d03803a0451f0703c26480c8202004004052042004540d000f14102e07600c658580035030090408000000b4940f84102e400091115103495941442d1554580190140300001e0b000c540a40d1460002c111843c0b00350744000701113620405c000703040b80303110380c0203064418402e045c6d03260200e0725040003c0c02c41c1c000b403040c404604144001c1102d90b1500228003240c01082e82801c800c21801d06000a10070b1200800245c2210702820120301018807e10485001c01b607560406440b842d1610030080e243d51002c2d100740e83c20400c000000c0741220003441542c0441c1c40c3c42d48070a16241e002c1c1d840303c5000e150844c080d024595204418075841d1203006c043d22603d146100320f4601a0b0400740c0c150111250500d11008641c4018911106079202c0c04965600300da003030811640c3e120214004940b02d21846 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 513848920 1106 513847814 513847843
    0x9010615030b0301180303052a04061b020d0524010f06110111040f181b110a0f03080906090a0c14010e0405010b0309150708010e09 58
    0x2540b1240a80030060004a100000e0004044110440e500b06401180d02c502c2040764003a01d0a02e0350064401d03d0402501d106d0500950701401d0040340508801d1092240c503001528155400400403941d004100416100851601a0b1658080c00a2303844207500c50306154640441002101d060b50101140035007410700d0030b541243c2034102021a070350195654003c40d4044800c410080c000741196031450400246800405000000d40303c54141c0051310740309598844da03d681c000036101010a240000702e003820382e1680c81c10902d070038a0003014817050042c0001095004141c90784101e02c02d0068038200c1c0d0701c1e241c031355031540051040100314900340c650512101c00070201c0c41000c13481c11300d07240c1c1400e050784003c2801c4400070b0304284009003021080202d200c0080090000804c08502c8642c49403c3c502006400001d06004020710141c019000440c4404204020040801d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 513669064 513848920 := by
  have h0 := BRFrame.cov_init 513669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 513669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 513669064 ≤ n) (h2 : n < 513848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
