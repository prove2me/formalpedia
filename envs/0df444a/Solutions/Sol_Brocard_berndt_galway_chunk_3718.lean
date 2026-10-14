-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3718
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:31.511777+00:00
-- url     : https://prove2.me/submissions/73058927-3321-4819-840c-577f64711314

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 668525179 ≤ n < 668705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 668526429 1250 668525179 668525189
    0x130201031e0515060a14070c0902070515010509070c0807150e030703020606191701020d051e071103030a020f040f06030506091f03020d0f0c090e161d061306 69
    0x7840d0010045518000200c040400d40140e844c9854000040340c001e1015030310220501400c40e0018000003030201314070f0740074060400003000711340d254002c0c5481c503920000c1e1018040100020b0340005201d14282ca540d911415071034560b0706400540b55522140c6030f01c000002c0325158100c0b01041c03a042442e2281c802000d01d03d6000707580d0f490440c100a881c00e08010034485c464444568107204801080e070b001c004aa12408951101c458803c020502902031072400413070072072404003009921617084080241d54000c1d0170829a690310307140800c0b1400b0800102c015072b2580104041500f0003010b9001300203401200c0a298103141d10f91707804c000b42d541646d10550009032900c4c20300c40c89107000078549400205036040b43c2010f1100c418102e44510746072202a00c82c2e042c41e8588020320840642801440354050344080c5c8481d1200d1005c0010880d0440e8001180301c0c448030b079285619004900016a460042d8400c00307001c0d420118041408000c10594102130700030440c40341b05a85001303c0c0007a00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 668527679 1250 668526429 668526431
    0xa0903050d141e090a060e0708060a050a050901020702030a0b1b030a0f111905090a0b03040605040308010812071704180c0f03020414090a0213080609010e0c09130201031e 75
    0x400c001184100d0f040c5040d541030314040310385080c130080c4000010303c1aa216803007007010414102c0400d2a500780344880c1d114030350390b01401c0c0030010900346a42c0f00c144503c66150003003000f510380c0d03084d641c00c03402040402901680b00034540d10100b018510340035801041e03a03059982030000c9021b0b0002c180c000b910101d8019032609003100c160350b135030300900110504041440d810311440c01da0704002540c190720000c05101000034460042d0b16003502240181044050311903070f034141494030350001c10b4116001d5000a02d10000402c11520124504000c480101c0c00f0b0703030030318103d51944111100000d00064604d60b040000143d5001d02843c40d2903000b46da1b40380000d0000c0344420240c030700c40a1007014020503104100a215110b080390750304210340c009580c03820f182d80d90081c50800038440c0d110060118484d06c140050505400070b00980325142480c006d01400c003a04411658900f01204074036840f90115000581c0410024402d15441d0f005241c04a02120301803d00c00c48a42c2c01c0115240740e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 668528929 1250 668527679 668527681
    0x406020c1e010b120703030f090905090d110c0a05120c0907020618030906040b1806040b04060207240f2604021008040506060d03030f050903041805010e0a0903050d14 73
    0x20150030303c00c2905400007641d03200ca41108404103191502880e000041c24010224800840320340314210b681d0191a40c3d070380c208071070b0416640d2a580c4406803035400000031080d010740001450040f412052483c00600031103035035414002002043c40000f038242e0524030541a4045003582c65182d4580502d945030098022420000c04229945650312900c280301d60040040c04e140ba00c4070b004440883c5c01c00c55000d17494a04001c2001d003035440c1049a26401500801d0100d00030010000a008848190302180d0300703150350300d14410110b6420080c01c00e01d04031502d0b003c56410f009102c42c2d010103045260904d2510640c1c008400b0701c2100c50b61001c15501c1441c00c000031400c1c44d10011408a90500340380e03040340341c0780d680c99a4500d0001c06860080d0303c0b00301da040400d0b00a4102d1910300a12040c18000351600060403070752600140300301d003d1031640c28241b01c01b691b003600c40d03103041e501d80e07400c0d8026640e9070302c01c00c002401c1218004c07400c00c0420002c1080c1c807209486a0040720a460003101c1c11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 668530179 1250 668528929 668528983
    0x1030b041506051e15281d090a0b0d1b0806010302060724090614091501210c03060e0607050403050c010c082109060a0b090f0a1e0b0102101802090406020c 68
    0x3c1b100d1003071811820700503070007000c84603500d0710040e10800e007608540900d0999104d088160141010014564000c01c0208001003086110900001e0600c0e00300c001079101981c0d6a0140d60f070b8042880040e40107807082000c80c000c00c030302d0404440c0424002c401680c022030400144003c54104590555030b143e55001c941ca03101044e840a107800403c0000282140385450510040c6441c045c8a5003101603110b403603100203406003815480b8101d412a90104c0903a981c2c3c2091006013500c0218400c480c0908000a10b0f0305000d10151000d41c2c0d040303002400018004001541e040365581810303074225405200d0700300c0041500501d8024180b04400e032055a042a00c0114230706400a48400c1499041c10302c0020b140c3c031100c043c1c9a01480c080402382c0c10b600c868884a005286020590001038101c40750400d512140340c020343c9121000f80d08039141e0004058846045410048400c00075018103080c080c0540382602031550854080d080061a290440103040c0c50010524460341a0440c41101020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 668531429 1250 668530179 668530237
    0x111212070c090f0903051602010918051f081b0402040b0706140604020f0a030b040902121501061e0e010e1201060302040b061914090901030b041506051e15 68
    0x40c0c1039403e40b0920000c0c2c225a0080c003140162481884040c1403210b024055a01c00c6214a00400f460402c1e0100d4004c5071980300c0103450112a00448041000d02e04940307690a070001340d080380c203214091300b01d08544030700c0441030048501500f9405a024000801c010071a20300508045115200003d11410344202c0404540e070010300207440396205120a22940c4c05001c100c0340c1900d02441d0000d1426036441c0001c0040048440194109804d080449044040004c2e0566011007049142516030f076501000c43d42d8a8501448040442c0803500200b2024001d2600c00360a0320141000900d911013840466020061300d982454180e4440000300158100b5100e0412040c0d01030f1040c0d49001fa078003992032054031400c0580403c002c1c2c004040c042c601244070070354841c5480101003c0c41540e686c01d1540100031309079404d80701c14404c88001c1180380f8807840760408645015000c502d5540210800381c0001d07041c2440a130300405100c5012a121b2034940060080705000b0009444250355a4007401c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 668532679 1250 668531429 668531441
    0xd080d2a021b01050a0e030106091805151306270c06030c020102040b03010b03041e0f02011b0314220e0901060509010e13060f0c080601020c010c111212070c09 70
    0x410300461410004082d981c01000c031805c21000f41824450700e11103001103801000e10b68404000d00d4a404130b902c144541c1c40300d83d422100e00400884140412030440081404002d0700c1e1384c01c010555282c00000240907801484030b06813490392211401d1001200b040c0041d50700882121944040d6005201140d014400c20801d0f02041c0f000f1824181403061180080c131041c0940700d420729010000404210b00b0400780c031981c10401e200d07000c54406902c0c2c45030710100c03003c0049001c00c188510036601c504c0c5003410b80c203d03182c041c2d403424107484184d0003082040c3c2c000c40b0b2a8103058840d21485444849940c4440014540f0082d58070b158641303038440c1400c440e46600094403401101e001008058030b49080540c000c034002c4400041c28480d40f030440002c20715140d002502500b800024401140c11007041445043e00707030280c921605070b513001100d254040781c0d00140502d200c1092074441c0d0510f914020030000184080700c20724610740310f906c101a04200e804583c40d45000400740944a01c40c0620 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 668533929 1250 668532679 668532703
    0x105100f060908150c091210060509160c0314040e15041104060318060c08070917030a0c021c080316031b0e0a05130608070f03020d080d2a02 62
    0x41040c45041031411521030703d034288800d080c0340c1c5020104440c4a40c0303178111458800d0080c2401c3d15034040348110790311441526010b00c103041c0742250018860030701500807442540014480305034101075080990350826821016404c209840d10314040c80300100005102809a2000ca000340d4602242d00f04804020702c1e00e0280500d040440105141c900781040c0c40a49020f0706000c141a0f180318400311040c0600480a8030080c109915120b4081d044040b0300e01441c1ca82d512940b1194440c108407250000c04030007012158410414920790900c03440c200b802c81032000b0100704049103002c880070310003000c1031801d0300c2c40c0318000180a07000624070004581c10b200c9007800e0022000325205c014620304a0b400550078081d400b07a520100d640e685c0c4000000e003100524942c10115840c8510000742180d00810ae00303882450008681016100130200c112136005154080c0c19400ba51007694942001d904491000d4480011143c9035540040342044901040071482096805c00301c000c0c6480441400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 668535179 1250 668533929 668533937
    0x903011109010503180c06130e090a030504060f0c060f020418091e0204020c060a0c030b0a0e0a0e0f06010902120609070917030405060304120f050307090519080105100f06 75
    0x40c1c0d6420b40d820105aa6000c04c03102c10140c540b40044c45420b0400c441d05113032036071104000902640f2580390070b0b2440143c8080500c4880c0c0d9517150b4004503950a182c1d440603000c900140020009184220f0024010545501d031462000c5c0407503442005880d6030400c0c0780703031207900802c0c01e115000030010740d900d4001c400c40302401121107036160b01400e445e244081103400304c1603415200564a840d0100c2d8965a0b0700001c903a86403410141d400c005100fa0541c08000a00b0018503039064038004010f0001c1d00c42c2c0030454005520707400700742c40092160496051032402560f00d004255241445203500078242000b02503960890180316201300c010091038a0b2082480c072061010060340840f003e02584c54a0444180c44450070040603e18026948003ea000c24004108010000380c0e41c5003080e00c0455840d008252012403005460390300085548000044c100380c0c04103d0b5181541c0c00178840380c4048695001275854000381429900219403144000368585c0c001c10812a200c404035000301301c1490 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 668536429 1250 668535179 668535187
    0x31a0f071706010806150a020c0f032107060b0d030503041e080a0c03031b11100e0a15090804090b0a06080105030a020f150406110f010504031704030c060e0309030111 73
    0x114541c824100a00241e04200c014400161541c81d10b18003c1c1908042022258980c44180c3c4002d40d504002d0801a0007600325400308200740c180007a604406052140405c0c4c04044144840c0c105034010a0041d1132542d102c003440c0b100340c2c4500d0000e0041500a5980c180c0c3e9103040e0400c0c06103909114801100c221004c02100003245406007500c41110843c54a2240610682011170140a0807000b03203000c0b40d08000101c85c2c0e180c01500180940c4400c0d819566031030700a04070001181c01c40c02c400e446581080448400083e5032071840310101008402c000340718007198459845903005900511112980c81014642e9403401c1000c4038000c08851401107107560401d408a501ea4810010080c010f02031040303003410aa4034240c82c06080e00c0102413481c0c8079a030702c0c240100064000c8449000c9801007100c50f00741d0341e906008da01c0c4623981607110701c0c00c1c5c0f13101001411180c07040248150200011800740340d0000b45540905071a203d0400e0081d030b00c1b180c44100300340c00c46541881d10550110100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 668537679 1250 668536429 668536457
    0x60a0c020c151e130302030c030712021302040e070e010e030715030902060706022101090603030519030b040f0b0307050405041a0907090504030804140a0c0308090a031a0f07 76
    0x24407444002060102d8203620340c4221418001511003890f0040890480421400709000000c42a201200c0c000c400311409801800103054070390b582409014428644980c690015051003244c1c1084010754850040c07a10340d5440f5880306100d4107980e044c0c0015260741c100303a070541e4016460320042c8011400b40c03022a1030100d00c99241102100d000301819150b0000d80250341d614400d55411940055040d59a020700c01c00084400c0101c5d80d40d0040c0d04078050000c541d0b81421711510702a0713640f40d1103c0c0d251402c108000d00c8a80d01d09148203040580718584405680c449008509070b4041c00c40c0d0220b10304402070205400d10074542c010031300a624000800000c03e80d440011541c0700d0780a050040542c07074070100319040c14401e4000010290a183c01d000400d64406603ca1140e4040c80d45a150350020079211900d444500c4400760100340800014030100d031203c0001c22940e00000d04042c0c0c1c5175030326640c04111102185900c4110582c1d40c0c1000310000700901e44523403064031890030f203104003262 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 668538929 1250 668537679 668537689
    0xf010605011403151003020f0c0303040b0c040602150a0b030114100801140c07050c030706120501050f18070207050d03020a0c05010206040512030901021c0905100e0a1403090a08060a0c020c 83
    0x159413510720469101400002990217681114962070b6032000440d924070710038100c65581d07441640e04840c0385181c0320009103841100c0041d01c0c19904550301811146d25141d014440d10348002d888503815030340d21005010305560074410100b400140034840304030b82c50170304801c6081082650100b83c40d42d041400610400901080780c652040c515a2010345845150030043d10b40340c4420482c540510071241c0104c1e035140c01980d50288158000c0701031110743e80303134810b000c8540c2c20940c40b141c200780d903400c0c0c41184264110000382d0001a500c100c800803039403280040e8100382852400c1c0c6c05070f00040a880d040c80075070001c0902401081c0004c1c0f6850410303070741e207568440f401100c1008202002c4081044040c0a40440340f0751010b1a03071b4a5a0340150800c0345000342040041282c0368030880d03120048100c024068289100002000b40228603050344800c00d1005016801410301c2c0410001545203940e50b00c0c00710b0141043c007009000a2400d0303ca52001c03642e070b99420605550101d00c5044140c0d0720 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668540179 1250 668538929 668538961
    0x60a0c0201270c030b0c0715060e0604022212020a0509010302090c0711031002211033090608010b0301030f380912040b070210110f010605011403 64
    0x60564580c00300700b0b00d0910084010b0141c000800500d21030301441035066400000d0441540101d041c040f2029664808400705c5c0d20912840300a4601500003603440d181c594040c016007507581d03001c95040d9007405a41040e58445402c14200c401042b2421010340c100314603000c024040994400d0010750543c3c000407001c3d440148240d50400c1c002800c0000c220340da040d041040390011b811520f1000716441c003000030750042e8400d05000303203840050000809800c103400e4050894103004c1d218507401c0c660420501e003070240582d01c0c2c00e2241502d105240164214680b205034140c0e840b002030030705100000709001d2040c1e002440d031000c00d200500c0460401d0002488140d8002554100c1c8040f00b042d214001e8441c52014000c42081412640b120705c9800ca001c0c85030700c802050f0303078000c0410a41c861850040d40034010504905100040040c10034010300c04c025030141c20b10001c110b1820b5034013442c2c24a80c0d81c5055007651a02010002541c000c031101042082c80341e1720508514180c0791080034484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668541429 1250 668540179 668540231
    0x30c06090504051b0304020117101503140415110417150702031909170a0b01060f02070302120c0d11010e06030403051e0c030c070f06050a020303010e0c040512060a0c0201 75
    0x130004040b0f0110781c0642588110101d103404d0900461a00046114222416125041180324200d1200c40228820f2064504480c8001a007800c243c4482d100c83c0c00d44c429281501c0881d0b5a607c0003201c1100000000d040100400300d50380c0301c0c0149007808103040408001001d07044848000030b2000c041c0d008001c0d1070440300586007052806203007080488944115620614032104000c0752490344203808684142140c2c0550074441c1c545c1d9903004100c0f40600811000c2c00143c014880034030045c170b040c0c2d010151101c01d6038100d6403020743c0d84001501c00e04500000f201d40e402c40e210755071b4055810203142110b4070b00843d032b080d04515040c4c501030001d10414055a0310b03800e880f82070f235080c0384820051300c034110b060354212501e901003503c2c650307940c001a0007001c1695000081c0060618840d50031103091403213a90147d81035903e440842018120081c0c07694220140510000ca000e40342d490f0b42c04001c416542c001c24142c21b100c4090002c50307000200810440e41003100211802d0000819881445 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668542679 1250 668541429 668541481
    0x305070b0613060311011e090e0a0624030c08060d0b1305160e0903040f0b4617070c060e160e09070f0506030403051201030c0609050405 60
    0x1944a200190401c4880b00d0210001c0d85000404414030144074103c0f1800d9500ba00d0b000c1c0380385171030701005030b00c2c15254280c0d10009602420900190078068105074000c90b044001050454a0ba101d002084000101145038403a080e20456280c55050103201001e500c035080c000a030741003d0300400c100100100000d0950b08081c800710b403c0a0178000004050b9800105403144003078114018501d500d518480c6842c419a0034020444a200100c1250116401c514100526030314008682040b500411004070000601c482080e00544440c2440031495030140007907030f400804056483c4c032248110484001300034000302c18002903158083c41a8108010b0b08240480240718903000e006480703003e6904107a409000100c011200080345c244040c0d6482c03188110719541c0c0c002c0c1071039454007540725003100ca0084140801140c00e0140046401502030325040389060306000c07c214604000f83c0c0f00300c40b2034041e040c04011866004080c00003514040b01c00307000c14141030a003220354428103005807500c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668543929 1250 668542679 668542681
    0x906020703061119050d0e03040b160f170a081f090b0d0f0602091810152609120f030a1d060a0203011a0c19060f1d0f0a0305070b 57
    0x401060001e441d03480720a480e921307050038072402d801800f60300240c032070b030100a00700440111034103404000da40c250386451070718506000c107880c0e00701d006024514003501c800e410310100c0404a0302d1070b98200c06400301e900c1d003103980c3c2000200007048400001c141e07a5400b182901f2840600f81401c4075101242c40b8010003040034050640001c44d003c0310321038000e0074201003a0784181048409e030080c01c081d00d0103e4800030300d802036030004a482103084910368226542064140700030604041503001000c0b151801c4442e48001d00d68044410300d03030011003946288644204500014200840d01c0001000b2031201c1c100948040415020300001d440301001c0c50f110300002c0c044000455100301450b600004a40450400d10341c0b002c0254028000c80703d01d00c04284038501940040c0b07045904507021f0030000c102e401c81c003d2484441c40002e10302110305079191400703074200d56464056031044100742c0a045955820101c1442c0c0b4003851003840000d26000407140c030b80866005001e550303406070402200015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668545179 1250 668543929 668543951
    0x3130b010f0e07440916030b091914071a12061906080a0b0a03020a0510030b21060f04030f050304051c05090111120405040b01020703051504050706090602070306 71
    0x301201842003441312907040740d01a00402c50407105100c00d4004260784008030345480c0015a190b03c1401180b500b96030002c40c080001512040300c1320351081c0620199111040b00c0c5000d492602c081503029036010780092000c01c80301400340f0038280204940c880445042c9031074040e94002e401142c10a4010040010001b00b0503215018440700101c2c80d4134a004101c4d0301d40d800909200025074458048034502540070300d20341040007280081da41c00800c000c1440d854001001501d54184800408054682100c822241c03602d50300c3c81407084200b0003111051007081c1006241c0342005052310409000042800040782e040b030031290003901213241ca20b6aa0741c5d03074144545424164440882070074034100018494940c45409070000c07040c240d94903168040d58031031035a80c0d02940000c48c14189410802000380349001d60082d0f0032480e060060741c0c2d010f966515020304006103141d002500100700400c00c0104203003481020050300380e034200035074131500f0070300001e503200e4203400010b00d240d07039a08820030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668546429 1250 668545179 668545217
    0x109241a1c020909010c09150c060b062a0c030303060918070b04080c04050a090b0a0519050a060311060301030302060c0d0e1c02011503020904021e0603130b010f0e07 73
    0x15902d401402c030342118101641640e000340194035101000698410010490f0040c5442c00d010541450350341c0003c1c2c0b0000d45550700141000d0181940c40b62040000c4418500000c0c814142072a0b003e80d20440741450300c030140c0c101000c81c103c0c0c520a030010000c2108654924400903040f5030303403048410442c94000382c0c2c0e45c5040c3c01c030b400180a0840214000812007000070b001c1010001c2610144215100c1c80020340903520040002031081d0441000641144102d42c040c1383c0c40325441c0c140340c1305000840d1004046500a5850744450b0b070329200103005000d140c01c4211004002503842525561554070000e485e00030107404031036078010000e0201c5101030950001030f604030b07440c001d40d1704000d01c0074040301e003038400055a80050350824401ca6260794507540e0500880350042c0407880341e40d0b0303143c0c00c1045c5114007110700d2203180d6a05840406584a04015601c18140100400440425030a1400111a0590200525042c1d0020921445940c42003407130b04024a4100a500818201c038050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668547679 1250 668546429 668546479
    0x3120507022e0903031e1b0804090b12070902030421030b030c04020a0509062a06040311120703050726120f0606040b16050109241a 58
    0x40d600c026000c0c0e5180d4180d1442c109100b81c40303007203480342c03000103050321054503c0c040611000d4003050b200300542c00159441c90b200748000740c407464080c00e0301c1d680d070f601102481440c2d14255000180414248010320702031250503030030101161070352009039088901c40c1e514501401520384035600840450300300011140c0400140c440c207080100c1c0d10080c640c0040040506c000039510a1152202031142c03818070b4400c54030504103981e43c1da13240100510900c5900da01c14010700b000c1c1110012059030700707442400c070034000c018864060011030810b81401001e1003a0324001c41c4407504102000144031082008844080303605082054603071810b8102100e40102c1c080910103503081d50316125029044a000405c14990740b080d10b54100d84840e8450392003600225011904004100300a000c04401030b00035042c09068140361001d100b035039560b40d40c01d560039442c0c112440c0000d4a03640041c0702220001c0d1021280a01c3c3c104034607000980c02c84801000103c2180c0140410380702c003000707031314114014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668548929 1250 668547679 668547683
    0x4050402030c0319110910090909060b030607050405180628080d05130b070f121e0201020a0e010509031e0607020106170c060a030212090a03020601050a03080403120507 74
    0x464407490700200c0c0e002d01c1d51040f6100c10501d2103140003035465050030702c00c0700380381e00007a0016400c0100300b07014403143e003500840e2601441400c031303000143c02000303002d805032480c454040403400c282c055080c5494946c014200400340103003400140002d8558200b240d084d100b1500094099440e00c101181e4001000300d5412441803581500b460500c83d00445e69084500000840d1001d0b051003004403054054264075000c500c007001001c001c1240540041c00d0403501035010410a60300c19910080c0f00042003c400010407458100700003603000c2c0c0b048c00001d40103140025454100041350040403580b820145905111001c9244183d0340c40400440e182110304900c0001c0300909059880c1d81c0e0901220100010340c2000c501088520406c181d456809500790010051201ca03101001519000a40328104043e402d00c40342d0022617500c80d00e0380c007443c4908042c0031a25045c0c10024200407058200c580141503604007000000c2120b002c580c212500000c0e540180c21141d2400c403594030450b440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668550179 1250 668548929 668548931
    0x1d0d1412060d050d030b09010b040b09130b030708011e0203071e030f0905032503090b030919210504080318060706150f050d2003120406050408060a06080307021203040504 75
    0xa10f060185c150344034a01e0340500325040b6402d82e036140350540b071500c510b01824403281030034400c04105050041400442c2807000304007081c050f00060201e03240c0703083c9601c0605180c1d12207078415082e81c08000c41e4461310310362400661840c5882c1c40040c101c1c044002c05c0d5281e100210640e500e41e00d00c01c0d801281c0c2e2008141c0c0030f211254890520607075079004804100503111044041e107040100a0000f2200594507481e0390302d20b1441d01c42042d4054100404000340b60140c514000c014814031a0103400d07440c8124101120301c5140c146c24184460002900d1085c404e08100c14840c0304000002d0390f13a803000700004240507940d85404075515008881d0300509807410300c0e0150058288103031448040c0c5013241c150118941da076a08102c5005e9040402520820026081410000c0c5255100007000c00250842d02540304101d01161160b0240c0d100c800040c2022405001550050100700e401c5490020203028541c1410160740d00c0b07100c1d50030021312a402e07500f550481c00e041401503d00400000300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668551429 1250 668550179 668550193
    0x60e1f0c110a060525020108040b04110627030a031d0a0e090705011112030c03150d050309041d0c09190f090c12170315041d0d1412060d05 61
    0x25150303800040c00039900c3d241c049070790a010171080802c0d00860f90160340d08040d986a5841d86d1302b46040150081c0d0701d600c2000c0c07414085449010003442070811070601c402541c4289640c0e19003460361070030214465001000c4000101ea48140440214010145654064610000010b960a14a520105000d9514800c101c90780b800428103808540082c0c0700e82d001c22542101c0070362285074900340020024801e2002c125001000e0000d50790000444062810400340000040d44c00c42c10f0201c100c4107035000059007a41c2d81000c0c01520254008594511020100303409600d840303035020044240640c00c1400003540c0d03403060145803000418060b00030401d480c001c41d5454040c10013400203403070f1000552030000c2c01003c5035800001360781d0440c6112040000d1a00c0380041580301034801d0005a5840000b6036083c0d42e40d2082e12540441001400301030340b136440b8000d050540140780d05040c0502034101d068810b00c484100c40758121160000c2500340d8400001481c600d402d0302e005041486545 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668552679 1250 668551429 668551439
    0x6090607060f061a03070f030b0d02090901050103111207050d02010302070b070903020a170a03030b1203120105040b01030207031b050a08030c0c0111030c070b090c060f04060e1f0c110a 81
    0x82d0240040c4d0304c1e00001000c44624542c4120b03e00d21040d03407034100103503c24000800e814404e0340004030114004004c0d600024840e00026039216099030007070b825035580c20040042182004000001c01010ba9030460032030343d480c0d401c41d2205890310075a4040c420140512007160303c40c1c0d04503540325031b02041104003030030400c10040c102620f07400102d004000c40707500818800c11000a19081900381d03c01400c0c001040d80c0c1c224040c05907617075201e40091400b40100c02000d01030029040c0c51201e40403050480d89480c0422003038411313001c91281454410400030011903800030b061508800c15000b0512003403003e1800c94034103100b1141c0585500008002d210319400c100c8001c080c0514420001d1042c0713800d81c42d22020034402919141c01400c81080345c0130001d6106c0c0549a40305003d11309079285041c129020540b1588680700032140340c04002006c0c48101d810505100858206480f4080d002c654421415040812501104207100034442a00200003040b85104410350b0040d0401d50340560320 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668553929 1250 668552679 668552681
    0xa080408160f1205030f070f170a0f060e060d02090907030803161d1309030306080106092f12042603061813170403050a0c030c05091506090607060f 65
    0x20502158020b902c03207410f0546600c1501603a02401034240d441c1001c1d200d200c401d0307036844404140502807001031464031300300e01c0d101480c2d148604d0a180d0081454400c80401004841268100a000ba80000140802038480380d0003101415410341c1d50885684428190510b443c46a42c001040d81c0c0001040000c940308440c858070300794000352581c13200c102ea42090a12038a509070b13449900f20800840041c011107140e0007030700019010341400980d194036094410b007034035800c0c2c2202c00010b441e40e101304001c154505044902408a601010200189104803105445804080103141529001140900180704072003c5041390b030442c40320030300007400c503840142c0e001103e80354450070b0014070304808960562419449005180c10b01c2008100b9903540c080f1040d070003115050102030505c030103c0011004c00c50000f506c0d0141c45010000d501c1d624000402d10000d80116004420390750511002810344c0341c01d042840d0045074800c0d101d071307c9000812100c0c000d85201809a80c1007401000d154061 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668555179 1250 668553929 668553953
    0x50a090e090706090e0f06062a0309180708010909020a09020d0b0301050a0c3e03071b030206120a180f05010c0c080711180411090601090503030a08040816 68
    0x140707446250880f56130f4a41d245c041300c42103035040f48040c21400021300c00d241138001090180c2549440000e0801b160702d070312400c44d081c1081d481030b66200180c1e00030369150003105030043c0c001c1100030341024502614001d1120f07806116016000d40c460410707000311750b01d030040e007400f0f0f04680c0c0c030031034903803902d01c110070064410b0002540c002c0d440d242c0845d2902215001c0e990302d0000a8a81c0c4009500340c0c580b2100404084040343c1d01c03011580c2121203400b010640443c0444820002180c0340c0140382040300346401c0300c0301c40030029000c000c4100300580741c1100751404a80000208103560380c0d0304402c0c40180c11a032580d01c2c0580c140904070300820040880c40207580d801900200405078481c0d2094560104030140580324080501c1300e00c00040711401080c0d030100010300311003900c504201d0214600e40303003958107c4500d10202d05200203030400000441c0d103d03400346171140116103400003280e280c0c410f189903a02004071600014040c04540070450700240320894045c21080d9a60608507500d0b81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668556429 1250 668555179 668555189
    0x3122708161403191805010e030708010525090609030f050c130212061c170c0102030720060c040b090105090a0806070f0e0f01050703122c060115050a090e0907 70
    0x102c0040c0d01302514071480c240c004280740c941039044900d05140c01503680e8138440200303945c14815180041880c4400380141401000000590441d5202030410800070042c0d440c2617108000221100300041507102d80503008072604002440170034081410483e040400042c06640c004841c405000e020f9100390b4018070700548260701003c1d0756124041082182046041410b8a040203681a032002c9154501808041c20a10b0480e611b4243c40c0200c03682603810441e450030100c2e0800c41d0b0440f45000c4032074450440380c0010b026103554a04070500d82028000c40c05081c080c0310011401c00c0c00d603400307081144d0101c1c1c0300134203296456660306e0f00266111000c44242c00021004941c150700300d4020b1003a0182d20800034440e00300d08050100440d0395812041c001d808008c5240407084844089202d142c1c9046080c088505000b05030f0702280070f9202c0020320011940c0c3c407240040101c015128143ca00750240d51a0a039524142c900c1d0446410000740c1062480804800510949000000d50324040726 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668557679 1250 668556429 668556457
    0x3071707170307180b1909080607030b1003140a0b0307030503040b0c0d0c1709011b060b0a15020703020904141501080d0306050310050a1803122708161403 68
    0x454134aa81030b5a0705640d02c10700071252024002c100c030fa0f003155a132003074040c4501d2500862050759101014a0000d0503a00700b0082540d4a50250030782c240361180c29008021814180000d03011840006a05140100103030203076692a12006250307176043c01340400654114080705d894031380392243e41120360702022151145205007200b20780d1050103020325988150f0081d00c61289004c0d203400041e40c0d075000320301542c10000495285115008884d0341c03403544c00c1c01040c1c005031540200060001000751604000340003000f00810703a05143e4006603010589505403180321294440307142000b2100c1100d118500940217040003490350085075a1028100c0381c80c102100c0c24660a901c09030121142e80c0941c2c0c0d015048550b910f80041c20581103da0030080c0b01d2400108801d141040300784404192404400080308208464401d5406021f441189031000192040442000c98002c6e0f0170100e80b00d00802d150004501846590b140f0000d0600c100e4204007185201601b80400a4596001002002c020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668558929 1250 668557679 668557697
    0x30d030908131e0e06180408130603090209070203030114060c010b1f020105150a140a08241f03140c0301060303080f18100e01150b0703090b0c03071707170307 70
    0x1185400c421601070600580203400c908000e0848800d01d03d0007c009940c4030004020002d104540190f0620040c41c89540004400c04188100001c0c40000703801c0a085520500050005c0980c030a170380412200101c030f065940f141c8541c440340c0505005075640b503100c03e0110003654206507071203804a2441e5198000c00c00342e23039124801407010412010182d00003482c1c50042c49002d100900003002e081000300305206190f0394502076840e265040e440c0314ad5a102c1f516415035075049240c006074210762000d42c4003107480403e000d501151b444a00c40600080a540043c0c09210420b201e880c100d060082c000f840031903124100648185c0741614040705401e240d0000a406907900720000e03440c840c81c0d20241014401c035902034009072040c00e803480d0080d50b841665080c2c0b441541c80500040c51340c406200d8135200142406014600680c3c000c0b02080d004100e40e618400b40803007100c4007980d0000c06400c01c5166028560800d01070003400a04c0c80c0140c0c2885c8400900502c00386114001691b120201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668560179 1250 668558929 668558939
    0x60d0e01050708040c0b1801050a27140405010302030a03030c14120717071727010c0201240605030a24090e010b0d171c09050c040b030d030908131e 65
    0x948079060142004000b101590045e9610404c02001401001d140bc1c09421030915038845a135202c03003110140c0d840f0702940c1001000c0c03c11a0000c03600c40101d81c1004698516004070741c4078800200010101651400c0c0f8200c01400703024503000c0940b81c070ba141915110764541102c0d03051020b41d0010301140200b012030641c15140f941e43c501c68616030b07a0305900c9400c0c0440c541078142c0b000e03151442d010940c4040350100c83d1403007060640c60254000118905200f150081d0031240c48150b040c140c03d401c0d0444089546001d1000c100311552898007951700e0783c072252810000d09014000c0e00764124814005040412481180c209881140d2030810020b21240d0071a401c032040c02c800300ba0001c416101040200d002c0c0789942d02051224041c8070300d081c01d5504801924809441d10311906d6641d9160802030160030040b040580d0803d0350100818421100041c1d683e140300142e50080686a035890782c00c0080c00d070142c0703800000c03880712400107588480800044c4241b034100100c0c030812010b80028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668561429 1250 668560179 668560199
    0x40306240b07020109121a070909022215020a08030a09060c210509150402130606020f060702120f090409080301060c110a05061e19120c0905010e060d0e01050708040c 73
    0x2046c0c981c040030070180382c40002e480000683c40140808148904000c000945000d0340c0000c110008039052140402002c13000300c0786101d182500404004000c0080c81114241c0019280080d03503001541243c581e9100e030400e2000d0100490000c0c9014248003d5600761b54104403100e14419245520019078003001010508a5004039000041903000408040341e00788401c1200307030400d0010b000340018000c0803000038155020760380320350010b07132120460101c0c0c00d00c240071080d0441114400381c451400300448220040c001c00e44440d400490001c1d501d2001d42e01c1da407040c0c0c1450750100d8811b80301c2d0f0b51400f014220032280c5c0c1003a901001e45110100316850220104000d0b41c0300108000e041031140003100000d0341e5035025941440030f00300304600c500001038451000d0460706944000030045a5140c0c0c20039684840315480902c00c0d15103051040381c1e0411240c409800041e074445450f00c2900c5400c00c081c00504240035041c4d441d18082c0501c0d00e9000301c05600c81c0e03000719000c01e0720310741e00c0300016 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668562679 1250 668561429 668561459
    0x81005040b13150e12070b062805101233120b040807150c0e06130b1c0e0c010e1008010504051503010e0c010f0903020303040306240b07020109 63
    0x80285032600c1c0f00001d044029403040304c0c104034210481d002240c1d024003c07061030340910300540e85811f1513010491240303403100031480c074031885002c0c0840c80c0c2c0c03034042d013402d038111580105841822000c40030401944075044042c840305a50304284001c1d1485806001c0001301c0c003072003c424041071100109841903070304092040310204428200601c1164840c40c0213140060000c40700e0803020421000869004112003440c0d4800110000359902d400c20b0107170111036115581402080b090110000c0b412030300000342e048501e5080e242d507a4134105070708000740c00300202c525507015180103008900340600040178040710b2000c4c0c9420044440380020094a200154554000204000018400c0c0e05041d0031154001e2101c10f4450340d013292000009003035440643c000350203688501d03002401981d1200c2c5002d0400035904059501c0c074119008251644201d0001800d01a00c40d01030540700b06035403000010441e0641f810310542034660300001e000368845d0106078009070f40c800010800c204442051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668563929 1250 668562679 668562683
    0x801060618090507140408060105040b010801030f0b06043201050105030919022b03120219110a0203120406120216020f12030d020d0e0303061810081005040b13 70
    0x1e40348203441c155040002e0071009181d90704000b007944294003404462800341001c3c2c010800604204e40c1007405010031103032440310660400503120010000300750f00c504d04203c0c594010705490b91581e42c0c0408500600f481c0c101c034a161040005075003084070f604d240b00b07408540c0c0301e040602c01c076640e0343d0046410f8001612041c03025040f07850403190010002e80a004803510140000c0c1e02da40040c01402440028030340b40c10b100031035101c0c0c40d200301540301e21004981811941c00b1810420703001c5c80f6105074040c00c5d827668103103c86445031440742e00082000f4400141d0040447c0d01259550203509803903042489400042824036001503040f05480c000e8030811060380000011040380c0b0740811503081c654442490300310003107005904000400f8001003c81801c0c4480241c1d6071113a101490046604030074850501e0f82040c000d02c80203503940e08090510001e10700444c2180e80300c0b910030285c0920554005107061041c500032000c0c901d141e4000f10300c0340b40203401028071030f80c6641400040003103100700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668565179 1250 668563929 668563967
    0xb0c0f01091a090c09071d030106030308011412010c050c0d0e031f1d0105060f1c02010e060415440709080a050307111e040207110301020304030908010606 68
    0x42c044a842c242d1180e1a4040c40890031159024100000300d2511901912080d0003c0c4200c14007000c42004040081e034026010f50003044250300d542c40042845c0fa06018024211450301410b0400303543c0c24001010041c02c0c04003c1108440c0c524010340b4651260440c1c000500840000448c024050030142c06403803030207000740c289c608034400b524403001c0511400306590740c0d640584094500b44808090140f91441c400054241807500801402448071181c69118203084001c00b440340301c0d100c8800e60203583c2801d00c50181042100010f0b1640a10341140c54a411807882c445600c580c07016002d00303160481007142c800e82003c4d5074000e007074102d180d000c1081200009010814120030300e42ea42d5021040e407514451080c0c0354540b140c140030000f01e0076100c4d40d101003880c2082c001505840400c481049821103080c80c4c20041100305404c001c1101403080341c0c00308408040c4801d021103108a040014000c41d13032480d0600d40600307402042c1c01030114a40c601038010a003140a01c425180312001f000f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668566429 1250 668565179 668565203
    0xf12030806150f0d09050a03020d121a060313120306060806090408070308040c121110110615150d1508010b0f0d110307080a1406040c0302040507180b0c0f0109 70
    0x201d190f5070340c050082002e075240d890303041c140458000e00c0343c01c80c400d02c2035011300301c0d207000c60b80c2c01881c039a00310360020b41541c504036030b00070a03103000c14007650701210039950382e51241d460f00e4205100d40c44c06200540410200004409002e5155008505581c05502d48460f9602d406040c4005802e0403580248203c40c100a40d40200e80103164003a0701c9841034100c02d4001c0c0e100c0085580c20340b5001c400703ca000c09081c02452141c640790314881410603643c40c00c407078600714031159290b941d640a80200c400104926040c0d4460720742c05a1401403103a082c40c0036a4440f03000385010005c0c101c600c205494103a8010020948131810b000700c4040900061046080030740100802030070b44844441100d2503040e14102d558103480078002c61004000c1c40010b4486551281005100803000c0401018240c101c2c0e010000003a4010850405680e010750b40040c40380e856103000d039140b003440f85003c03c990b8005040000c59002c510020301d0440c8200050700c14824104c00f036a426600c0e240c0005040310f88000e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668567679 1250 668566429 668566447
    0x609060912040902090f03030a03061d04021f17010f08161a0c070504050f041e0203030d0218030601091e09020a120c1a071e05120309070f1203080615 66
    0x2402602004400078001c200c020340f0f481c0008e2860340003680140220780c0381d00041090001c507aa00080140c20460302c05070901c0d055001800111200100062840b00706180850540c0700320364100202515001c415500e584589400003103045c58032640240380310719042c0700d070382003014040300085920b265186020070749180250704103a006550075070000e1040880000b4540d5981c0079443c0110b82100540c0c00d28241030a00314080e06002c16080d00f400c00018075040180c500004440c10000d01d0080144c80c1c072494a00c2402120180005680c14410b103800030035028203903400240c640d50310084568640d14260701c0300b420381d070035000301035804000c3d44410802203100ea5445144644199007100312151a002468140022080000f0a04402140f45020850000441d0b0000c11540c1c406403500038807640c030b055840c0348001e490428480044041407401d074080020b900540182c1000300340103078940c0c0403072900a072007540650020300385030007107010307414042c907003050068240c082c00f0b10b44440a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668568929 1250 668567679 668567681
    0x503030c06271009230a0201121b350a0b040212010603060e07140306010f0207080f01050a0c0806010906050a140d0212010603020a02071e0e070206090609120409 71
    0x48030011078902c0ba82d0710a0140318401d0002d4540324414410000e92020740d410304104000c01c079500121404444030f034100c107266000808200080d42440c00504c11040041448003521200c3e59454106108903254a40603030800781401815030046d05141180007070b035565800c0c108c9080c0b111280c0400400c0401d00b4081f0b0798001c080b90304000340c409031505418800c4541d145109034071040000b55108001d0050640c4003000c55002603c515000585080342d5002c41068070020389490f041c0818070b141c200e4214024000c03800240030703007400d0300e5a16103ca00d0050280408481d030507419860403002d030110754024032641d4010b14040c0e54500c03c290402e5002e8039603600141c3d81c0b2081c0011202c0c000c4002039024000c14003010b4105e4090303285da054000c01404040103170005814540144100712400354000f0b41c003021598030355240c2c00c281805880e2541c0420142d0465045401990b0400900c1500054030078054081941101c0503556032102160b140e64108030640c00c103da04000411003500c41d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668570179 1250 668568929 668568961
    0x4061a19031a1225081b01080a02030a0b100c0606210209041104020301120201170106050d0f02190903020114130603050a0f0e0c04060f120204020c1204120c0503030c06 74
    0x71022a40c07022013000c1400300740c0c60b4405000c0405208102e003400580c00601c81103900440301317078454070307032071009070010f0003880d001440605016404000101040019000811620000382c14242110b4203000010b100c4007d0007401e55550b8104076001590720942413140500012044003064a05807690800204000c06402902d031000c941074240c0b40c9680d50b03c0114002c00001c4d030030f003501d0495440050150b038010b440c0401515201d200400586802004440483c1aa184000340a0b803114a4141c001d01400d1348240d509441d8038500e00c040c58200c119801a203000f40c0311031032031400f43e0740b42144c039201d0481c0120414451803020000030f4041e03080143c101d80404d1000c6039244c503a101c640100c4112040c4800c06a0000000d014a42018451341018002c2c0019048581c1d081030681c3e14455143c2400074056503001440c0c0c01001408e008002004014040441da150f981e5090304002c04000030052390501c24a100002e20f5240020854946440800144c512075450460400c0d90b104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668571429 1250 668570179 668570209
    0x18140411073212030709080606030601031214040905041b060e06071e050a060f0b030309060901170408041d04051c050c030c01060806161b0204061a19031a 68
    0x48403070014a00250038441c0440d000c3d01c542c4107030388a150034640204030048503405802c194000d003042c09442d0300c010800c5810b42e50008083c680c5c040b2182d4003114102040d000c503980c906030100b4041608407294026900075030007030b51919008a181070b000ea00320704440c032403440841e20041c13603006541000d0f40500086405501c08800f1031490709104080285030090480d0315400050301e1a04000311071050700026002d05408028948417940031960301d210380c81019100f84000314401d14540e200c0c2b540c486034401c5001003400e05090620307007021150024011100040c00f8050642010300850200c40e2249401c41c00034010340a144000540c00d032046526442081300800030724440d0700d410401000c000030b2120000074039a203032001143c146403003d0800440e824890340c104c50095070102c0002c814030340b81d01401c00c500d10984002402094070794403c80c52100040a21a40c4544070780141c0b04010b207010700d45c14002c0c845002141201c00c00d46810012a030b4003600a0324a052910b42d03004100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668572679 1250 668571429 668571503
    0xd03110703060204060f080a150b1803070303051e0f0d0504060908030c130512120a09031a0f060901030b010b07020312032e0e010504020a1814041107 66
    0x541ca940718801643d00035040b240119451036501920300b03078800c00103903010513011000c200240e01502c54884210340c0740308075403e4035400704020000c1e100401050911007001002c45d500282d607880c01074a5a0460040c00c0310b06180f029440540e503482600302e61041426000031413a08900300d025400030200a002920f9041c1c0d0340e0071131400200700000460081702401030b0941c4030303001000f1250f40f0420329045203000b50441045881620f1000480c41300060980340d0702071319600500303000c0b1086c64066001a15000c10341c91910554108908802e01801d5009030a8400c4d036941000d22030b404200b0b110041100c43c84000422010386600c0141c0f4a4074801000d60700030385001d40070111950025a1064003100b01c0340c1d81c0f80d458003103100d03940310030421404109291034900f544030300b4141c20501c40d01d0700403500011710210940c4919400c24540480e6080c80b58401d45881c5240300c8025410b000d18000c42c5001454452488400d0589020980c480109841c0c0000034a271680c0900342c0090400140e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668573929 1250 668572679 668572693
    0x30601110f0a080d060807081b120307030f030e0303060d12050405130c020105130803040308370c020708120901090e01080c030c01114303020f030102090d0311 70
    0x21007400e00103101403070301031003030030740c07101200c1a01d1002c480d03a603840600140e01c441c0d0304226242012840c07048541c580100b441501780104003003441c078800c00003501c000e80000210401015002000c2c240c240003aa0307010031051440d90300c590f41c0c17484207840140d4001b20304220640003030240054179240401d180340c80c6007400e540e00082038600400800e2001c1068680ca0b0341000b4a509104c4c85038000c001941283d14035150741c54002e41ca100c054009401c001407400003035601c0c0307a55900e2087d048002c0b0112101522404500f81c0d00300402d142c065036140c10100313200d10403440002c401c2c042d11491000790455500b6500b02c0a410f07403002d60400d045c06105400040c86141c41028070b80200354900142000b8001c01080508024001d4034582c140040041189101540080c004400c11118408042542c0c0c030340340029419100c02e8407074804c00c41c0c42c4010301000340c0380048107800c503072095840c0f441e0208000101b500b84e00620350190f801400c510141804244111400344035601c40b1420380d095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668575179 1250 668573929 668573953
    0x70e0609162708120304080f0d0617150702060c0409020d0603062a17180a020a120506130b0c03070c1505150409020a0b09191d0a0203010b03060111 65
    0x4507080c445009400140b140b00070800c61a0a21141c08588030000841d45145401d84d15140c0c640a02070354030109800109001010044981c00040074101e000c0c0c0c0e02c0c2126408400742507461580400110b040c03040d10b004250401d0000070718500072841846c0150800f428104080d00a4002d0804050306680710314000000c20464030501841c0c08468a0101d41e1030302610a100303200340180508400c00c600d060805000b4000c2c4a000398119254a2910098801310ba2900b480d0824280d0040d6002c1080000002d80120030041c3d0000e82d48030310191419999640e14070400c0e40541c100c00340c402c002240c00561004c05280046078025100d04110002d031001f500d07a8948242c0d0b1502819881740d9075018007001038040782100303070381c1a000c440034813007403c07240d01007002002944549101085d020500300c00590b640c1d100110990f0202148036145a0b0310102841245c015819080a50704050081940583c0c240200d81c1640e000a59a03072454460308011525582d20845180c10382c042d1003c0035074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668576429 1250 668575179 668575217
    0x170418091b030b0a0b15040303050c1c09270609050106020c01050c031801200606090606090d0303050c070f08040501080c070c0e070909020a1805190306050c070b040f05070e060916 79
    0x1010794020b40e40d43e5241c0829403102807809841331340c00109100d400e80e5080300d8984c0590240143e4041c403011401002e40245019001d4554000f000c01da10304111000c503047c22281c0c072250417076019500b12440d9030b18000c010340d1107108140002e82150001c1010707500501c810024000c1065061505015918040103050f400d44403038038080307409400200901555242019085030000003c449071031034102044009486180c2c0c60710000d0515448000264440c02003909031501c00d41c00c14014070524015140c41c5009500600606022866510106400c80080015190340541c041c04203a03106040289144407400020703d141c0402c8400c403404610380010340017a1501140540350100c0380d0b814050300189507941600b015009058502090504a0300c00f101c01d001c59030041000a07407500c5080326030082784118a40540141c007200c1c1480100008042d82c0800207000300140c80000e0307100d04940502c10302c141e4400350300001500118501802184403908001c0b06804c00181c5640f082003003403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668577679 1250 668576429 668576437
    0x801090e150a020301060f050301081518030703030509010606080f0403050c0330060111030f0c0a0b07170c070b0f0603010f15031a060607170418091b030b0a0b15 71
    0x42ca8140d00480100311890300241e032403107803001034182103045604102c445641e40481e405c0c8151100c6840000c10b81c100791070f1302500400e40e111026280e80f65901d080280181205075003000d450342c03070410300260b15841205102d0248510354071400c2d190700c0e6602c00301c2d403903003000c4107802d96800104a1500e45c4600c0544400c0e09504101c490b4010080500c4030001c2c85e40020010783c10700c14140490101d03468044121100020301250007074450007003c2e41f05150038081d03000105103011050900c92001c2e081072190340060302001e107000d20b5680305021103143d401407240060500202074085003028007005080c0c1e40c402d8010340001404550f00045c2e80a64000c0c40c40324102d103148020600600901025a00740c40d040307138000c5411030420380d0104075244500840500841000b12243d1351340ca042d40b040b14010000b07000150080c0c40141c0b07030200103050551003114003120310f9817400003588204060404803900709945642c1c1d582c503c48010080c14865400c287d0111410300030b10341d500c0c84074002e8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668578929 1250 668577679 668577691
    0x2040906030519050606040908070606080606100504060507201f030e0102041d06060d1406100e0906040203100504060e15030a0803060402070602041211040f0b010801090e15 76
    0xc1000d62860401c01e040c525034400d030420a00c00142c02201044001980c550010303400da4000589601e5400d000d03c550085c840001c0826082000009880078005a02c500500044410f43e052040313411041d00c0d43e11440c494030003c0740040c00303000049070000d040d1040b605510018080021000000075004200d21107020084c14011010140f145030305200300e01c01c0072034900086141a042c502140154912981202e81d80b0201c500050b03c1529007200303403485206c904006000c100c10034000c020000c4022240e4178006e100d00c880246000d0312a80805440d0303078000c1e14031203c58482c01f050201944c0002c14055040803401d0001400b921180b083d2401040c0c003000c01e5140d428504003106040c5030481c01c3d01d110364000c00811010903c42030840350400011600140e44902c0f03480c0c004043d000d150300410000b609400c80100384000391240d215927480c22242081a00c041c540310608031036142d4130b00c40c001001c45005100803e11584040e12800078941100c51318101d490590726020002c5903c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668580179 1250 668578929 668578931
    0x1203050d0b0316031b0f0509180a1101080a0c0516020a12080d0b0402071a092e05160210180215040f050d03050a03150b0c070611010606090302060705010f020409 71
    0x100140540d42d0700e014418490b0720031207480e0510b1b0070411480c403402c13401550f20508060b4042850307a02030540c101c09000c0304d00c00703984141c0010304049080c014000b5044d0f005c1b8100c68005442101c1911a4003c01541c5848181c18110391030340d00c59455004a0080b84c021a041c4004119030003401d110304040c5111320b0000d07903640c03010403220301618460710846019a006020800002e6243d00034103107040b180c0d0104125039034440d1202031504c1d0460503d000003200a0301c00005a5103074400f070000e1104d0880c01400181c4030480a86150340ca1a0400d80041c0c1040302d9412a02c0a0f0b50480b0100307003800d1501e0400088142c0005e044444141d00016480400007010000e01c031682d910400103080c2140c0c40c41c481c0c42d458030040c0c01449207500840801d0b9551710003403000c689146a10340030b00003403e40152034444c200002c03607480d10035004030740c040380c040c4c590345140c0030b0140100d4040d0f404a0740c482248610759400c0c010f047c0c2200c1d034103c0740b554a40421380c0141240b403001d04010460910 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668581429 1250 668580179 668580223
    0x5031f0e010b0a1211040510210218120c010c02031c02010509071212050c011506020c04060f081507110f07050414040b2a2709011203050d0b03 63
    0x241c83e0781d01c02c0c01c000d44113908009146510000c5102550103c810a03034180d840394014580c111480030307000c01003c02c404170000303007951019103644c0503041c4421343c151b4084c004408201004602e22034801301c1066903012641054840d44a818440450752000d402c4030000000800c000d88114015002d190041c0e54420400c068110300b00107502c01445100418104051651a07480b8a001035903a4102440000521000440c00944c800e085005064115600441c0c80da24001c1d219850086054491410058086104c501d07208250089a00702d030024034009011000d0046420b500410000c2442101034425007554014440e0342d034060840b80141540e00e0a11003084102c480d0003c510030306000b003000300700000c1c1010210942050002030300e01014081d01801d0003090000d1544032460180101c0e03494030802c085011841c40000988650500101c55014401200300c02d104011405a80110701c0001c07c1c0558014446400b89800c04140304030b555012030319142d0910062580123550300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668582679 1250 668581429 668581447
    0x30e041d0f06010608010602100b0d14150c0a0806040506040608070e0f0109060501050702210109110f09060105031f0f081006080607120513020a0e0114010c020105031f0e010b 77
    0x80b0006014200310b0405100c1541411030007544c58007103048180c2c1e400c0c2d4428180d415640c0712001406029407169480c41d803151200c0015448243e02804002003035894008104020000c209844009100e961241403d80d1004104805010003504240e04159650790110f02500c3c103005100290000002100302420420000425460168400d41d081490480c0c1480b05a83c0501103d002e550104c3c2c03100030740c11452542c00d07480303800080c11000641ca002ca0840403c003042c1405103100034112480c1602c40036817400e00141c410102c52140c0004e004000240c2c08860000700c41403240441042c0034101e40d10b034003081e92883e049800c50201c507400300300c400020741e060b8000d041c05050140701804841c204004003600300808001410741c030300c0d20b0b070300000c0811540d010f0b22144a81c000380041e910707a80e2142400c021074400e00a040441d114601240410b50044400da030b4890390607510585565211501d4441044c2c101c101d81e08898000e038400034550403910a410301034400c0504060b500c1c0184 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668583929 1250 668582679 668582683
    0x501020708031605250309080d020c040b060a1b050109020d0602090319020a230a030614090307030c1e050109080918101a130b070201030506040207020904030e041d0f 73
    0x505201c00401c5002c1082c2c42c0f128500d0b10003040030744000749240c6045d403202d24080d074180d0215000304501d4490041b511401c039a00003582c04008509070b0702013145580000920041e4406c180004d00401c2e4103d607224100c0c401c074a00000c03854082e800004440702c0b19070020f8800d071454103045d909980c001c40e00744510f240071b110800035007a0361122002d80d80350907030103d5900030f4641b25042ea0090000e050f107481810203070202030070440040076507410310b403030b46401c80081400e025a01c01f0007640c000040d204400c00011603a40a8058440c0400f41100396180c00e0040b600c0c0381041c035250414000400052024061258220701c103100d0706856100d84410f1040b40c0d80c000c60801c0b021070b41d0405120340203008085c90402d03500000001021000c00c080300380014031400c00344c440d20000a120029074a0f07840d202910401c0e200340d81c06e00440d114072003040203034040c18101a51085004010030002405140c0c00c41703480c000684081254118000b018100741319022010040d5003100e41966410641 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668585179 1250 668583929 668583961
    0xc0d080c160e011d0402011103041e0e0c0c120f37140702040b0a0e07030e120c0c040911040914150f16170106030b0a05030f0c040203060a03050102070803 68
    0x144c2912184c20403558800581d64074009071019060221000e140c0c12503010034021600540700c880710f0200343c1100b20600290440d410b208031000380e20507030302082603c80c07004101c400c502706180040c181c072031a500e80c0c1604c1703078440200309100580410021564034020352180d605140c2c6180603c0012000a03241c20700007616004c1501045402c1911a080d080c04c1d82c19036020795019140000d14080c00004200413072030301e8211000c40c504010400c1200e580c5034100d001c00013540b4042c0d905100f2040894070b103a0058410090300380e00640700301481c03400c2c01da1181c02420b020f08219080d0740c44c46004241125030892043c0c17101c03101c211060b100c1560411100d2407401040b0700c03c101c0340c42c08000050240a01a040807850020515003c0c43e43e0f1042e880c4a071255000303600003180796903688018005000619040c1d015229584001440f441c000c03490422040604002c1c05a0003004403c00009620080544d680b01090380004400b0907400d00c0500401c901c0750780802d0340c80c1408000c2d0010343c08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668586429 1250 668585179 668585189
    0x50a0e0706020106150e0316170f0601050916020106090606170105090403050f0f0405100905090f06060a1b080703081009060b042c07030b1309050c0d080c160e01 71
    0x20410f82c04202c2e00a1700362a400b1158030524090004840040c000b074204003014900c0040e5520120002c1a2485524004c90b0301c030760314904542c24200c1c2e01800d84d40f200780034442d01d50f01c80101000110703a85064940080508034030320001403a60f440314214400c0742c100b60000e500040c4a8495a90004003281d40d1b01d000d003030708035800c8401c6d1600c0d9800404520400101c001040804a1100a11911101170b2005801c00074001d9012494100d80104802c00f030b441a544100320580200b031070b00e004082c480e4000c080150206261400000e015200b04d425000d4001da40207580080401041ca45405400000c2c804e9803030000340d0030403002c506480c011a03003088041d0b03450510300b040780540840868040364a2000d841075401e800401a0402220804900d100c0c2d000340310400a0f11549584030055210003100d28070303000d0361100000003c840c05030100810b554000f6040c40c03c51720b000c11074003c14a200c1d8250b18a02900c40110300e061000550113402142c42c440818001440d4000e14140988 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668587679 1250 668586429 668586431
    0x4230333090607140f030105040b060f04090b0a0605070f02062506050a0606020d0c060c0e0d060b121635010e061e13030e03120c2506050c010906050a0e07060201 71
    0x1c000031700e078040c80b041c4a2184100d565000d050b4007a155141584c42900c458941c3c0350b161692004003002074000001d1041c4648580c200100d0001d0041050300da10720f0b00301c0000c40e0160310a60078007030181e01c03600018111020754048040c082848a204102c454854900821542400303002d4009490541e0004402d5400c0503250441caa60b205d42041b0985130407000c003188407014094282c42d01e610010580ea080200812078009200f402d4121040e960801c0e68030703451440d913940c019512010451081032202640341d0041240e40c040c1019001c1c90543d0400000c40b41d901074040030000b2642001480441c0d444043c0244441814000c0e1035110041741c1c169010480381c130042d803040003002072280a200d000b244049060520800c0214130780c03200035040b166000e4011b0b401c032690b03811010040d2070a00c9041816002e101610f80c529500418400c10b05948500301042a21b140e00000b00c400d0003503580c0c00c444d001244003030044038000c40091030000f482140c5080b03c0c078107080c01600060296 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668588929 1250 668587679 668587687
    0x602100e0a05030316090504020c0f0f010605010e0909010f0207050a03030b0604060822021207090614090f0c070614010303021501240207031203020423033309060714 73
    0x2c200c01008036648103076a9850000f850b20390f050191200c00281e04401d410600c00700d288080c0703610024a131140d0b10518002c4511000d601c0909500b41c81190003498000b03245007000002d00d0030201c1340306401003103200000c02c20003a249480000ca801954040d213003544024514822302d6018170608118810580d03100d407405080c400060f0000d20b000c0c1810410402c10b10080c000c41241c03411021146600070b040b250f090500f1903059640358100d0080210441c078024000070a07584140c00c032580541d02a240c200e1541d110f07261010504401001040400020003110001a607984502803c01d40200000e419035411401e0013850088102c0200c20000303100301c0140402c1081d6105c601c400744000700c03025921a0f1028049082c041280d00082000101d5141b40394100d8160b000380065a0b10300b0390365079540000a04014210700802c2c0c480750982c0000d44040c0c00c0051507040c59005400d43d00307601e10400d030f0110301200c503d03604954050940d0445001c0c001d0203540b0502902d4103906400909080c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668590179 1250 668588929 668588933
    0xf1807050d0807020315010602010e0c01030213090506062808060306070e0f030f070e0a05061e0103020d060509041a130209180f1b040b0d051011090a0602100e0a 71
    0x400401c10801030a81078001c680c80e0210358041101c02280204904e8204855030750b05006406041d205520b14010700800301101c00c554441d100b138a41c081d611419034100180341c0b41920008101c050b04040e009041003000341040041d040c02c403080c0c808509903100c0382507080c0200070585800500080c2c46074001e941442a180d51003118501e030b00e00d089858880c40b030241d4000910f0009090900d483c40c0c0a01c03407000030400c4440302e03d076100d2007003c0000e2046580f02010403140301741c18004283c45140e000d0302c420302544260301400111705d20210014175180c440d40001c550810458040f1440f2800302902c000403d850080710303420040c0d2459000402007250b0024a00c42c070020014101c0e00784420311580400f40800a4a0029620740c1c251000c955502a1001c041030032524030502887c1425090409402d01d0b82c4e034001e030f09800c407002e810346110754042c1001508074003018081c070075414015a036007030703941c5142400200143d800401d803241081040340700780c9112081c02d4085402110722040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668591429 1250 668590179 668590189
    0xf040c0c0b0622090c0b07230c0a09090c0f050d140309040504050706090803032206141504110a090302010c0c081b040f06060207060f090e0f180705 65
    0x342268000e454240c00d03590280400e080e100a00784501c81080600610510408503034441c001c0ca0780151164041c0030b450b140e111003a845400c0009103002c0001c0071890042c854a990034084034003800c25200180c02d80400140002419006aa000c2c0d5541115a04003d000300f40500105451110f405200e86800001000080450405410ba20390800c0000d41047d007801196a142d400820400260070242000c5640310240d000350400304130145030104110301c002054910400514203210413500c0003650102000b0280001110313a0394032082440c4104200715925841002c845441c50b4560b03109008010036100351172003401c440c2c4400c01150034000d910000550035240c0a0900c02c00000d45450484079621f5158410304050190318180008074800001025050320216000c1c0140340c480d41548040324914401e000150340b01a50030481c45004405510031a03c082c10310303041d5140c3d11072400046142c00c4542050401c148010814200c203910b0308460070513140d0000707210071420080422 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668592679 1250 668591429 668591447
    0x618022a0304151412010501120e032704090305180117130309031406010302040c0206070e01201c021e030307030f06030f1a18060a02031b180f040c 65
    0x82400d01800c01c54410345401101691080b09034000680c0c1d40d40039050305d82010003800c4c0180c070300080085c1c0800e0715503126030003004090b44d0703080003840c80c0000c1070484180712580c010100d002001001210a00343c8da036441400c01c82d0327000c0d0700c5243da2585005400303030782c8030030410640f0306103c0034403040301e075000c1d8900324107030b000e05215529078000303080e030030141c4100e400c41c3d100410072900c070fa0120520b8000404c40c981240c8c42954144030a002da0031059031119011500800000e020004070f03102e40d032151395034448001500e09011403091058079203a080c1800389580120029980360120802503041205800039400c1d0303114900d00a1003880e03002e40740c1c480604402c08043d150b451902114200b036000c0c01c020342c0c3c0000051800406803800f0361171820b0314bc000283c00c41c0004000b8400018100450304011100304c0604615582e00c2c400f00b00135017000d841e026448481c00d03070b50484000031b0310040c0701c2c44c03071043c40581c0315580781407c0211444091052034090f508164414040c2a0004c14507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668593929 1250 668592679 668592689
    0xe0c07110315060f01210e0307020a030c03050c0f06030708061c0609150207080307050c1903020604032d031a0301060f03201c1a011403070b04060f120618022a0304 72
    0x406c03140140d02c207280c5527000300100654055584880003042200d0740d44214100c034490003d131004001c2820811a0044203550100d401c04810000101c20601c214031103a4400c000601c00c10040c06943c02c0220100b00311841240c0003030b0303078a0810313041c061400041e81062500030300039407520666a4030000c20f0701000d0090414004082a8111110340c10b214a03241514103084810175803120303040082d510a800e80c3d0a80c00701d244458040d600507a10f4000c3c030103068000c082c408203030903480c0d01180146a07205403486008241d00c2c0c0c00e0f0701039a0a001d110024500042c1203a00c003810341c2001c1c0200819010161814081542034494549070f1022500365281a5814800017030700f07504100d04241d044000048810400c1400031804000c4070101c1e540e8440203400322401161502140c900d1445140501400700d608860142e034014401c0900001e103006d000404a905982c40e844018104402400140e1560700030980e2400c1c07824030307118a41d1000340482141609070b0240e41c40c2c2c2c0c40780701e18026 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668595179 1250 668593929 668593931
    0x10206092b050c060c1b0f0d0e1207090b030d0c03081303032d0c0309050c040b1c06020d0e160501052118010e0303010e0c07110315060f0121 62
    0x103001c15805441500d903590103280680c0c6103403803d010f85c04171070790040342c404c200b8045006024020010008078420b40d40321040c014081d5a40a1500b139551041500045500990710401c00303262200600c00c00004050380c02d000f14a548100d01054100311422a02c0d2007000383d000d0703108000c69440284150403840100b2900e1440c2d55908046001d4814105045443c091081d214142e603a5481c5200505800c050003c120704054000114195510f8070f00190a6506c82c0004000502d400d921070350400100511800f03120300410110f0000c0401d0010558591341c4c04076400e0340e100c10b41c0c01018800d214150240900740c60058140640c11054050300d8100b1202246401540140014940c0c001c034580b81d03491018070f01007100c4026502a61403554041d400d000800840001c00000d4a050792180404050940c0d600d01d00980c01c1c3e0000c030001d031120440947d110106880a004071448900101c0c80c0310700524040701840082d4402d40d501504010405090941e40015002d6010f038010071b90708 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668596429 1250 668595179 668595253
    0x10030807031b030807080603070b030105090a09120206060a0902040501051c06081905150121020109030c030f0224090f12030a0801090b0307030c05040b030a060213030201020609 78
    0x201158841c250b104044040b05040030340070180b64002000521400342d03566200029541c00301499181c4800e0b10502003004024070051041d49043c0e071040c0c0c1c2c01600e541c40068020f520b40c032001e0501013039440d0100560049004d00949051110b075200c00760010402c15487d046c81d01c00028854441c40d0b0402d80040341c001003000b03d03003500390401d00c001c000350700885903602c4050300f004074402c1408008451521405100181c2009d150611604840742c1e03030141c618120304115204d0b0f05020811040b4100440701c0e0000c0001007000e80c0d4003011351300401110800503c03038414000419500005109801100b003540103400745540700312135110205954402442000300081803495400260b5001540800325a00f848242e001031014100c48074214144842c500e03210500d51206500d02000d00b244800e540c060207282843e402c030700c40018000c2c084500c49041501d03820100e8000446210142c160180100199a030410034207401c800380b0b00241004280541c851511206050103c011480c4108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668597679 1250 668596429 668596433
    0x1b0d081909050d030f0e010e19050312250201050103020307290a03021312050303040602031e01060f23040e0615030a0f05070c0203071403010603020310060e0f10030807 74
    0x2820112003242d0240854030083d01c44400a00039090005082d490549004031485600e0414040c49030010301010240c0215910301d104c1a812890011054816110400203100080c042820180c81082d864010300e022004443c9076020410144000c80110381c180401480581d07000305800c0111204c04081014103428007030f520314171103807100100c2901c610101e5081070994064004003110410a0078540c0c809880d1ba40880104c0c0c5180805030041e4014000140050400d41c01142c105840310500380c0301d40c2500201d407000103400d80000b0005030a00d88454181038118032120b10b801162400c83c5201d03c07441521031483c0c0680d00c0380e8000011500003044680e103034194070426005804410580d68600141d591014005d180488002c00c3c0c81d10780024106846000c500d0409607008018091035454040c02c0012500c464900c00d505540c1c0d181d00000607542000742282340580c0500101c2e00a01e0702082d14483c2030020000001c07000706100f0407401c00030240315103003640e901c4000542c58185d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668598929 1250 668597679 668597681
    0x2101a030102070602030f010e041e03050909090f06010f050d0f08070b0a1b140d0b040b100819060506070f0305090406030602070b0105100903110d02090c1b0d0819 72
    0x90542a034065200007280018011a0b0300114401c1040c12494141d40c2d90f1801145000c1c401190b0203006040d188001e44407080282012150315406460a01e0501000200182c0d08090a5488075201d6000d00c030600422801840f41b24014590914442485803401012070103543e0b0040004001c04181c15040e400c0040351030075520901c5c0c21600c04516441c182007004018158220341181c46401c6141b800400c61080361042d04400e44080e0050404403007000e010301612090603010740c030035102d00080c04035894150111060700f089642d0644c403402c00a82d602c45800382c1007803000700c2e9410031754144602c0d11094220b403c1f01e03502051f80242032940b820100e400d400360025950303100e07040c010000203008040e0060314895010b1100a500ca90703803002001075900465155801082c08085d00b0000300d5400f0700b41c0842c4007000b8202038000c4000394000b54040c00119203c0c544ca03200404c5480204580400b80310b01c0c03d8030100200284200880003500f802c1d4020049000682d500c2e181000000341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668600179 1250 668598929 668598971
    0x50c010e010e030a03060f0b04050913060c050703230f1b03161202060105011e05090409080c0f030a080a1e0f05150a0509161103220e070210 62
    0xe240080004003100c0103000e03143c0e4031040c40100040d04000010405a170071140c408200e0324400c0800b450a842c21052103080c0700c004224400614000c440c450200f006c500805503802402c7c0d680582e0b510701443c01402d82454580a4050711045210301c0304040c5030130089034824504a45465210b0012401c220300c00303040301c12601c05030b02011032000080004001c0742c1070721a00c2a440342510080d0311a04076aa084244070f42400600110301003040680c88860b0b102d040d04071032400502e8a402304010800365059110304031010400019449042e58051118189803110580614034144d0754132402042004c1c040c1100c201c195070b0303024241c214001c5810724a400100135100340006515030507000000c0c40c044803883d080302c0307000c1c0e090b018903e0140601e40a44500410240094030b40c2c0070141c2442540c4142c0b0024000f100e06880076a8200300050102c001a0b1500800040c0e8503c101c2c801006581d402401e02020000900000c81e4010840301017100c03110070300180070b20300c212800c10390740c42c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668601429 1250 668600179 668600201
    0x1911011d031e03071202150906060f060f09030304231503060f01090e070207080d0c050a08071a040b010302030705220c0203040b07052802030a1203090204020f0315010e010f050c01 79
    0x82282645c0ba4072030b4000c500d034802e00f80e8803041203034a50785520007070703031515008c6401d0307540800d0505c1c0000340e41c500704002c3d041d41c03c0e0b1444881c0c102007050b03011a2840e80036400152000036805031007028602101219103c00500380c0b1800f000fa50040c410880500015140031702c14400300c82ca0111991046143c5002000555030400382401d04c1c2030080d407034220314001e515050007103004d00e005950058030100120f5910000602ca40700007a15111b9842d0001d0f5070494901030b50840103411141c0741004140618060304007070f031565240d8410186892040e512890141c010b448480c00020f0101d0301d003590704e100400c0045034045a91104a0541c405c7c0c1c0c000e49828003020810030b003032150004216140d403210250165258041c18400044a03800c450000c0d81680004940d00000700c541d000c02503540c28a04011801e0311203036000809a8000c1241f507103000c1c00200c200710000444c0d11044c3d044610070b082000c14641e1150009103160001041e02e010301c03c00094402e9451800d50000d12050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668602679 1250 668601429 668601443
    0x717040e09010e0d090905180303040c080123180120070c0506090d120e031506010e0103092d050109031806020105090c0f031911011d031e0307 63
    0x551988820024400240c1d8140400c0d03282000110f1519400500c203240003604d6112031420390300c6c100d500360141000800218001c0441c080c010000e070f82c02c00145000d01d11400702d089140d41000012421580c005c414110190742d09407407802900c02024070503801c8410384811002161041d41403e014180390200002d2940341191815040707000300300641590f030b1041440f04511039882040002d1070050314211907020701001107400000c1c034a0361080f01d101d00b03e82401e2144070700420001e81020300d20442e00b00300712121020405190b03449400c004c400b0200b400c0c00c204020079600d4460902e008800007500041c5411160340c00e204025064070300c1564030000a004815280c0350040000601441c40000041040004102d85006005062044a840c6c1c0117090015503a0b0403c2454400d8200690305401105848010f40104000b02d00c00d10380110300d00d05c0f402010b81e000406120720007180d07014005546505c0071407030741c002c0341c2032080f000d54400b0140b00e10900c05a00341184201c1d60010015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668603929 1250 668602679 668602687
    0x10110a0203161a04050303030f04020123030a0c0302030403170a0617010e070518060d0809060a0e01140f03010e0705040e13060b120c0118270b011704080717 69
    0x90764542c11440a45003902c892581c090841d080e00800d07070050b4010103615030001d000007055240b60501e100d40c89401450700702080c038100700c201c18440c8141c46003801d154a0000400038441000e0141d8003400f0a28982146545000d80300100138110001a20000ca1224000310b04210b015420280241c48038490404c04148004165030007081d0850303190038180640140018980780001070070030328610b48800801190b4614042110501c081242201c00320024407113400075841e14030140c1956031081e02d07400e003000225000504000601c200d1054010030801240c050032650304103489c110740b4006401d201d1a150107409540c0c50040d5000064000c400c0000c01100040345081400700074000c00381002042001c0c01401480307a0b1420380e00c0103981c403041e2448915481070130702c0103490180c0d10448510b5501d6031103545145045032916000c0c002030030140c0c44256164480c0c04c3d40584242003803840c106810a4414240000a2018001c3c1601141140c00d00c40000481118000780c0400340c1d0b45d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668605179 1250 668603929 668603953
    0xd02010212010f03151806020304030c020f0a0b07030e0a08010c1220120619060309020906030106031205031e010f140a0b0904020d150b03190b10110a0203 68
    0xe4200e418081c001c0700040d4000030f941c08006004038241c80d0040c04018540c2e440e100c010019000700007503504418000030352400403843c42d2001c0d41c000d5110f6904c0200054560041096100c1c011b0500da1041c01c80304010070130384013180102d0b0070056060034403003660841a0002402c44503d940407c1c000d509244003500400e40c030015808890303031540030400000707100d40980340300840b030b0100b0a0b0b5500010420120340e414085203180d4003070402000407642c6030011050314961915a030120307012945910650085182003100164401019802080020703d1602c0d09241c80459201c0d601c18004000003050407414048070801040e1145030031142c1079651929030110b0011070b841800301441c54801050b8151030300c3c82c006c000711000b445080d402c1558483c02c1000941c49051840a11591000c41090307640c0d00c00303001e20041000300390303440d12481c00380000c40044003e2454150403a02d816150341140ea1281d54411014a0703070301c1e004a000741020b129070302d0107400090280d4140710305540948 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668606429 1250 668605179 668605181
    0xb0d0507031a0a1e0906022803180b0403030903022a011103070f1b03060504050309011403070f0806150d090204200d0203090a0816020306010f03020d02120c030d0201 73
    0x4002c00c5901c0600003503603070300c1d401801c6800c445151365110200307180080a0b9101a0070075051940581c80040c0780404400d401038150341c2c806025000d542404200480c041d030103210b4850356022024141c6840c0d2900d036110440e21500810040505a03500c09010905108118030b880c410000112580c00301400a8620b4106641c505540d0000d182a00805c10110022081ea580950f01c002910904c903241d81ea587c80340d0400d9103240c62804000b031400808500c0c68020700740200e004002a41d59001070b240010483e13001c00e1400d281581013003082c1710701654840340c89002038819150071582a290440061003046d40070040d0502e540010406074000341c0564030145001c0c4c422202000380454000c005070f05032140c0c0c2807600203403006101781d110200f0b5503001154008030f1203080d204001090343d600041500709000080e80540c00c00d504c07608500701002454054078400042807800c514560000350501d190b07880090080e00d414400c400a6001007140e90340d0003000070103031180302002c0380c0700034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668607679 1250 668606429 668606453
    0x1707090f0c0806040c113f1e160c0e07090810020a02010b130b0909010c02070605090f0d030503100807030f020607060b0a080307051c0207060c11090f0f07030b130b0d050703 76
    0x21071800540ba447c000341c0308030b00790021034500c108a00706d424198024801d29030ba8407070200d0b602d1824020442c1d03105000d07a0700030700c141440c86160100000790030040090f44881004107080c040c81303183c08061204c1d42001889820314a11203102580c0c6211140040b405400000f44213030f04000180045c0864460325000f8590205080d03e0300c02136544c034004450309803560903902c0800b40c1c02054041c099140b05100504010700c000d00008885890707100810780c0c0b5020b100e019000039070003100307104004400b003080c1c500819000e001070004500b503450741c1840342100040248071308400211102007241030b40023115458402810b07126865902e040154683c1c0c40414100c540d4001e06182c04d102c4050145442540040740c0c2c0101051820036109442200404c4000e440301c150714103c800c4a9514038000f584220410858280035040004401001100240c0704809050904030a0300e455103811a0342342e070f0f11100f244041000e454200119914035038418024000c0e00404030b02006000c030021b100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668608929 1250 668607679 668607733
    0x1305060f0a02100c09170708030408030909090d090506090d0b150f04050f0411010225090c02240c04080a080a0f02060106170406061707090f0c0806040c11 68
    0x3d15424420001030b1822030b01074480300f0000c41c401c15000e1049a5011011103440010031046600c0c031a210303000070b450b64210f940000340c540d00003d1410300034100500b046030402032010052405418100010740200c0351070047c00e0003080d0118950307409940e5446c2001c3c030795401a01b6a14942002040c0741c075024888499140a4031340d0800382241414180704e02c1c0e2060002001c8602d107a122a81c2d1100c80e025421442070461040c1e01100e034841880c000c064000f0780007804602112442c0c072030440d0540d42084888000d54016a0080c25003151605041c040b80042142d19040d60307641a11301840390140b0341125904d44523501c0908100144040140701d41025511102407010400c20202c0c0e44003404d0003150002440c060041d24080d20203014180c04c40c0c800c40300407840c280c4a80c80c01c403c0003452507004000d0741c1b02d46420001003100344a07000d1442c0c000300742881a41c503c101c0142040c0e90141446000c0d96a80700192607851107816455070241c0c00c0c000b41c4d40c205690307000c480d02081d5680c0b50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668610179 1250 668608929 668608933
    0x3030c060c030a0617282003030912010c09060f0509011808010e010204140f100f12091104051b04031704050a030c080607021f05042a0e1303141305060f0a02 69
    0x4504039641b100d895442149900071420444414010fa0540d0084c0c03090203c5030709403205000185955462451f11442d00501100000d000301c0075120007001c54895501480c244250440080e402d0355204007181d0035540b00f070030900c0c0c610001c031224442c89126a4840f08480d4a020114040c000040d0024003c40d032240c2e2805801e01c0b124010444000250b0070500d81c40034218500e040460702560303a401343c22070b481c1031a10342680304c0703203107c82520320000044425074100710021046180500c5403a400003581d0014650350010742c6451201e5114501000d09143c2c08071152400100c0c0c034104075400341001070300050740a6502c0c980740710200041d0107a06100e0040c100000c0049200080c1205141e000078103c003403a1494482034001020041c1058841d00c42e242e0a4003590802850f401010189d00b140c1c0008403440c2a10440006401030711344100c9128031420100400e5001200211040f0403160042c0e5440515000c004a0f01555222941241c404160048202a1000506480031964003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668611429 1250 668610179 668610223
    0xf131505040f0204050306040b0711030a0903350702060408010f090c090207030f141228090b0f190501030303020904050702010902090c09011b0b070e03030c060c030a0617 75
    0x400007607006a0103942d0301b40e07020340000343c0030541c0c024403141c000c45541003020300786401c0810242507900c54140840441d01d0140e00b0005c0040400300410b9145103440d880392600311910607111005c811001c0407134000000714100c01550b580d501201e004140c544020069100c1e0401d0040140140c0c00c01540c075059016000107041105000310b5800700d505682d6401c2c1103220001c1a039428003480003074000d0310700c14003a40c080003910a00d2117005030440c1c001000903a83c1d010001e00107a0148030610041c608080282000603078226a00f500440c9503480c0c0c038a16902c45014a09180300c00502032642410080000185905a0700504940806403000d000903600c0a2086c1d0a0703e6103040021f4029001d0000205801c8001c005031201c0d95052420550008508008070701c214100c10095800b201c0880921000542180545c0085003041d0040c5013004e00301d4840c0342d10f80c40000c1108004480000014540021540c060800b41003c1c2c3d01010015180780c010710b1343c443d081a1001d14644d941c00f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668612679 1250 668611429 668611451
    0x150f10050910180207020913020405180a0b15030a031e080f06010e04020d061e050a180c090302060d0207060f020418090203190f05100b0f0f13150504 66
    0x8100c0c14415480c038160b2544040c542001c0c42e0fa48043d00b9031089440342e0074401c1c0d100590700e036110280070710046000c0030b14481850042200b10307480507004d1000d095120031108651100030030841040750300300750360820300c1d030740d0b550140d0b090180803008030f9250007284a14400c16421400c9880d03c8021140020354410400505030780c4000d040d24100904001040003c00c1c0c1d620034814409540c10240003d03040c900340440607026201660081e0b0311035030459410005002442e2100c03401058111040707102249030180310400303001c5282250a00540b51449034081c2405500c0003401150f015107981c0da5602800341410081d04241c10440d0241d0900d04440d8150f801802640d042d10070070059600c00840b84501c2c10300a0010800482c0c02d4058a075060712030409030618040b8107030040a55440000180c42c1690400e100d90b00c0030340200307181c25510b00c0343d901d403540c507400760150603070751b07400740d8404000007070ba4100703c4200c3d0b41d01c03960511408100d046482081c1404681c0e0690742031180607201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668613929 1250 668612679 668612689
    0x80c0102010c0905120a0b161206030809010c06090b0f06010323070c050c060c01060f1a040510120e01020910080105130c2304062a0b0603150f1005 65
    0x35158000040e140f8031003400766103003010600740c505450404a8524014654500c07000c001c0031552010880d061060400c4065004041030341c9800c60280100300182c21662129403a0040310030b002d042102c400c1e1a41c08022840e400007007016004020005503103040e0b80203080b1407008450382e60003e401d1407490b55110300da50051001742605000d150741c065403032040c100c80041d686a0700f80d0f03c0b44248240c554641c1c230750100a000da032004800124003141000032200a0040691040454800d02000c04d01205101b030243c60a5420884980560307c1c9000c00031a01c1e540200d080d024901c2c5401c40d19070398030304154024101071703005603034074441c40b85a0801039608017424032900c0d410056001d05076000c0c84c526031066007090428244401d0802c0d5445883e02e80001002601803294000102441065081100950f0501b034081f004c852011142d035003c0c81d800d007050001400503aa0308041006690148042c1038038503502c1c0c0e0a101e061030b0080b07064160010564a482c850000241e0100e0b8500340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668615179 1250 668613929 668613941
    0xe10120807140a0210030203151e0a0b04180c17280902060702040513170403151107260d05061201020a051204020319050606010e0609010903110d02040c0504080c010201 74
    0xc5c02c071821050711843c180c01a500050102420728444031030401980e45c0d004035044600440074400001201d10420311080c0d07000c5405c51140140300344410072205205034421000c0e40c0744204041042800d60400303903021003002e100c90350015120340400c01d080c034201d00e5046a13250406d401042d0703d007402102c1412905400310282d00107208002c880c0250400d60442500030a844a40c0d01d42e40c0410b8803600240440343c44200c8051400040400c20f121024003105403841c4031200c100480045030801030362622400740000e10108a44010030b1441e65500320414030000d075516601e590b42003014950004000442d8418416011510a82c001a50510942e10980004e0b00e41900e0501c494480350321030803004008903410b215507800503001d00c000030111702c0d20394455002000b60b8203200001400491407556454000c1c001400f05001c142e0380704406c94200d981112617104040c0b003003000314407038443c03560000e9009402c1680150700340d58090014802c4030609810307514603103841c1004a0030b07184 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668616429 1250 668615179 668615183
    0xd050106021c0503060d0b180a0f060b1f030911030304060504170c06040b0c1c03050411010806241b0708070e040b16031506080912030405070e10120807140a 69
    0x10080314080c000500c0740c000140c2000b1601c0000c4208402200d15030301e00b0031170001c120313032b295155010502040018050401c645004a44100c50403d144544440300c41300911030600b016110780401c424040b1141100c401244042c054a81d5181c50350380c090700b19031151184900a02d8189071511500700c001c05c0c6081d2984005040b1494a8600b40c4603a6190b04014003004050140944440f0b50442012490144141ca40c801090780e190500b00b00040070726841303000e41800364030b030108580c90303540c50381280f68450340c130031441c110001e64942100280586405200000341c0402c0310417100c07800050190884040e0000ca60026840300813500907034200b035900806405424000c56000c5040010701c026800c400d207000110000345001036030a4041950025010508400034401e02c010248141d44546c90145401c51841c10309585055523018644070ba141454a6030002c145641d4040c008000180811812840c4401d4141441010755000d40011151703030002844841c0c90841c01714400464507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668617679 1250 668616429 668616439
    0x30714090103021014070b0a06050f10030e12040b18031c03020304020d020418152703020a080c0105011809030c120e06070f1b15140d050106021c050306 67
    0x80d01c2c550901c43c038000d5070482d010502400c01d414251902524000e004600d0180340700c0003550500452070000c5411941265000715914048030700c5030344680c007040b00d50a4061078000f98010f01002034504040829003443d555100001340011011620030141c1300e16014011840c200700200001c150341c07560460a40508440c80304004c1d030340c09004e0360146070301074000742c445104140c0703e90004040f180704000070341441d445070220100740503c14103c05801394110008200c524080203100165260002c1d00c041680303840c00140003054420f10a008800d81c0c0b01110076101c1e2040300242d40a480c09001d014a4000c13140b420b0300c0c060841d030250f8203140c0d40544540720400c1803600c485c40d24070804007424003030180400c55150a611070900a05c100b40c05055000e000d0503040c94118001c83c090a10031040b500e509209219042e5508803c0300e42000601b841052907003a0002c85543d4050015648165894000001203c9030049a0f591000e020702600200307010445d035040d40d16000a80d0343d1a000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668618929 1250 668617679 668617681
    0x40b0612060705180a03051b091005130b04020c030406020f0703030f0305070306170d12090209060904050a050604030806031005040b0c090105070609081b01020a02030f1c1a03071409 80
    0x140118003c0404013000301c0c18018138509100840c03091081903200322203e520005c40701c0c1d40c0c81c85000c1c1c040090003040b10207032a07901389402c000fa0254620700406200d80c0702c4001004c1c480e03a956000e5071445401800c159141c410307080085890344c10074840c0c0c40160040ba0302c0d2400c984000b24011082d40d0385521000d9040e440284220001c102c0100f182042c150343e00008100034039809030004414a082c1c0040103005020074006000720280c2c101d0303411590a0154a400607500d51101c03692240082d5000078095541d824014030380901c00c8809001d5009820a11081c10b5012100910411068046560003031905546030200c540c1110058170b0603866001145084d03825400501c07601c0c105143c02c40c02c000070303503c074101200c20a403005c546410000900020001460b4502c5c0811350898000b141002c000c040081d49030b1084104c41403c05500159079480310454030110003441180d81000c018018802c041ca501e0040c40c220454864400d101000900d50400c480c920a80c04014081d9005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668620179 1250 668618929 668618941
    0x3170913020306010201180c080c0f0a0902090a33110709110d140a0c0c03050f0a030216050d0e0d05071202060f030703050402190e041b120506040b061206 68
    0xb5000604064119521030f50101101e40c1410743d000301c1503018008505000c2d15141c031540c60803954a21560196503ca0540d4000c0e40c2e90041704d408807091311340b0144c1d44804120024900d11041e41214088030050660100500c1c00e0f51104024540108031402001701a544142c41301c0e500318851b60030f01d0b8807050082c030042403240c00c42c0240f40301506030903040801d2003c031b100c140e60040545036400344c4d0f25002c0001c46500d500802c3c1c80c1c03040b5070030243c01014654400800074071500204404503e0300140146456210ba4105c9240d80c0c071143c00c00c038103005589005501e840b004180000014204400c00803580f402c52454440143e01c40001c02c441440d0010400110150450580e403200b410f001c0d1030401c0b88240011403080560b80da000030b140c41e003072040192000c42c49108945440e4141e406101c2e0b403080882440e0040e0f04400c07180c0c1220194100340522001343c4e0050580d01d154048100d0401c41c000035228025440340440c42c2581e568a0140a900308090000740d03442e070b00840200354 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668621429 1250 668620179 668620181
    0x1101030f02090619030e030f0702100806030318060f04090506190803091c080a17070327050f10140c070203070b0f0712080a050709060e1509150403170913 68
    0x503032040d071708000c0b0f00002d8100c0c800742103821400e07042d03641c9440001d22004524240c0110040d0342d0031810007819030b080100100350741c0d000740030f0a413080041a05103c0e15a644090a90b100c4403140d52040350f603039440e0212070000d040c0540e2128050614124405196103200c50000240c0307544000071410419031004101002a090503e210317520309181d40400440c6800b0014000300c0210f0701c405000000c5000318010f0100018120420145001020300f05900c0d00040300c040020000d800d4010b403009414110300700040c00c6900804c40c400c403400c181c00c0d00e16071b4100c17034808101145040c59542d01c00c0400700c01445402e9009506170001c407400d110882207000500651500100d8030350800080307035602821440f1550151001c02c1030002044498a01402180d41c4406d1031700d44041c03950b14191000d00010140700f01144201c00d07030311190700302c4003018081e5191407400031b10303029081e513910f108207220381d0080c0000d41c0d010078821501d036522440c40041b203241d0740028004400120342c2c151044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668622679 1250 668621429 668621467
    0x31d010f051309180201080f070801050d110306010e01061d0a0608040807060905061b120720190c05010206010305070e13050d031401090c0203190203161101030f020906 74
    0x180c02c85151040416080c0552054191100340301e101c11a5203680ba000141603500c004000700b890348007440c20000441c0d840303209141116426107040c480192180781100701ca41840008075054841d0f80b00000b2081e07010100b0398101d5400791034002d982d89001086203504112aa510390704101c4265040100364800c03068150300034024071599050231080e98a4805880040d1001d44807036000c48244a02c01700040c2405000e9500715034140d2900d10242604010340ca00240b002050103441003508a03240f2203221000610003c4101ba12130005404041020b1644405c40540702401d40d0b50000c1501e5000240060580317030094004c0c013903986000442000c0910042021840000355429070001031410001501c0f64178003034501182e041044400c507220008140c5c00b4158080c184405115015000b00442d0350b41c110114241500c1f4541c034409074551b00c82d05805100c40c10000d8015014090007201c0390a100e05d00b42e81c144180d00d800c0340b02c1c205074020381c251035501c40800c00864140c201044940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668623929 1250 668622679 668622697
    0xc0b09010215270105060907050306100305060316081f1e021608071203141302091012080c10020301150e0a0906090209031612030f030b0a12031d010f05 67
    0x103000b2080703010142071040310144441105170b450b20306204180c50005151070340201d951500034110318040e00002c1880d20303440c1c149011b140c0d80714041070090301c1c28001c110081036107412981a480d650f1483e0340e91041c1d8040b800c040300200d041e990210700850b026116842d01d804c0c641c821040780403c01c0c04000d503c1040030705004031304406a00009000c480203844c041e8003e901070301c140d64108502038241c0c0d2200201400c04806c00c0104507005d00b061003600f0300141c0540ba42e0306d150b80d03104801540d000c21500720b00070000c90320070942e041040000080c86100d4404050384c6108a8003000d06069000a004003001c0c059514228000144074440c000b025203401400c00a14599a01031a412030b0403580215028540000d58010542020405100c082c4240b0041070300d90352420705001e18000d0362500050400c42030418405030244283c0003c00c0c07940009168501440e520840b00a080c00d001c03008901140301c5820311007681c84040301c0761405c0b00040e100c01081c1540c901044866501a10312 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668625179 1250 668623929 668623951
    0x9050f0412020a06110d0510061d1302030f071205071d061c02030108190203100509101811030d0806010311041703070308100f03060b06090306090a0c0b09010215 71
    0x4000c04075603240200b00501740340c2654a81d441036106200f00503110000d10b6034000d0310f90440d007045000d80c0668645006a41510692100c041c8040019407458000c1503900c9500d0000c07003408500c4d02c0078040d145c01007001c0d0301d82450100c0c010410006880040b103410b0b022401c0107003221a1100d041e4072070301000400a00c030324940800c2d605002c4904000c10000c1248039030110051100398020080349040d00e0040c03402401074030b46980003e80d00d51568225800755620303140030801140301005071548a0300b41c24000d01411a816403640c0d800000d03030105070388801d030031545000242401300382803c0b04003242c2d4990001c0e507141c2c0c0040d8040c2c00e144c2105910004100b000141070024542104414074010000e16510310640c100282151005410038850340d0044408102c02d200301d04402c0f0071207900180100b2070000c11400194240920b903032594041c00359070f003044240c0d0300200324040e00d61310482d8160340e01c0c0d85485000c2240d001d0000d80c940541d00020015866811607030030203901101072a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668626429 1250 668625179 668625193
    0x7030f020d050a05010509090325020307050d120306090603080901030509070515030f2203030902030c100e03060135012003010609060201050c0403031b0206180a09050f041202 77
    0x480c11070b082200d1086000b95200018400782c60840c1e00c00e6001440c3e04011800c1c090740b040040c00303a1031100c3e01c1d04215070214047d002152070174000600100401000d448200d4102d003020303440d03c4010100000020324107000881d202403507105400680382c100000c9400c106c0c80c0f10054000304005841c4840b14440c240c0d00184d07956440240e00c104006004006480303080140c0503d4100c00064003e41880c2880c0c0b290407040c0110645040710701e82c26140110b001007a42c008281442410a81c01d900600c0ca07410012019030001211007808030180c0407254a40e0b42c1e0f16000c2211700c000c1401c00104140701005032446803e0b1500785013956401c0000050011100084050140c1508051116640c0c08401000740b290070450b050300a103103600003841766250480440b01c2c1c6206a0200506002c12803540740320030954120303040405c9502808040da540144103401481401400c0450305c596810603020032800742e240078003406403e0080840c6900c0d200c40e60350720300c06204104a00218400d0302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668627679 1250 668626429 668626447
    0x3011215020a050a033c1b09140a0e0604020903030d09140f0c01141809071809020913020f1e030402040b03240a060b0c03030601020d110607030f02 65
    0x1c4001c010304081034480d2580c4501c0390201030b05079103c1104007001142518a6804000720f0000300000782088200e81c000303564a10a950310007024903d0140c2104000404070217003041c0c10141c008203441c0c50740000100a0b4441041081d03120082c01010000c0c44081c01207a61810145c024100104009007a2814a0803c1080c282143d4000c501901d5a02c005081c1031411b910070b220301c04010f01040040e00c0d131000c42d0320000e04021b00a00101c1c186080c0021748503088001456040c4080768024680d0700b850500400090050a4040411502079a000e400240125040c170841d255140c0242c038240034401c614003144000d4000b02540e20070344504103d610700f040d5079258884ea100c035040b413800e520f904060041c801203a6041d62180c0c004e030711411600c004240b00c58540c0402246501451072260b41d81040324015142c90f50003402c01321004942c888010002002a610900080e0b00f104c00940703050b08115030403503a940b003150307840d002940850f0106200343c00911000d4030b1140054a0261a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668628929 1250 668627679 668627681
    0x270f1c050d0e030409050f010b03040f0f050115050406080f07030219050306070c17070b130201210219020601260c09040f0507080607051b10051608100b03011215 71
    0x303141092143d030400502841000342500c5032940207140900c041a0a60400314900414031002d80090192485194040e0810901c500c102c256175500030001d0010502c00600d081241d0102d018140c407a41c00c003100070030f5441000601c03032003400705940204055480d5400740101c038044401244000c941142000c100780c2c400308826806040e5030703540d40c020249982028450041c0f14200c800c03004404002100103d500d24031000e4000c400c42c2e0361f40b8440301c19407005aa01090141c0c604400c1e6410403111100c04c41680d0181c003000004182400806420f070100b281c852200340916660441c1503803501c0781c441c50741c01d00711442d81c134224211501c0282000c00120072050849003191100e070200030b00b10810400b03104034001800c21070020041801c0c000d001401c10701a02c1c05414031060300070000c201c0130800f00400c000c10095100700300840d0034810300f508100300c41400f070304003c0750030031012030424160041300300c0440e80030f518050700f141d0800713110802d003068216055a41030b4260b07044603104856 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668630179 1250 668628929 668628941
    0xa051323070f05130303110f1b010806030601030305030408130902040906140a030b060418060e010501030b07080103030c1e170409110f0d1112270f1c050d 68
    0x451141042480c05890042c00302104003452000c11409001015222a000071403100356a4141000c002e00d000548000f0305e0020840312130342003407044081039003515000708030507054008280d0b5800c4a40e03031f92000341a0b9440e003c0c400140055010000500400d42150150451401080c281035041c0e80e20315408040e1b812540162203902c0d41c0780010009143c8646122079000d0341a50905060f928685504426180082415000f00d0b1592034941c0000d00d00c0c034520510130b9100324200100207401484500810090104685d808000c2011403509401403e210b03049a80c103030b07991a110400f5584104050001341c4014501501400b417400000d1100890340c0e01c001156261503454030311704000d100540f11040c507082c440240400c40010010b000d00d04950000c1c87d0060b011500d003081034544007591056009840c4680f1000c024440b18100c0171144d19600791200c00040c005035192001d1503101c0b90350440e02440d640c0403c540841070040c0c0d1010003c800400d0622a04201c54190b144c819506 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668631429 1250 668630179 668630231
    0x7020607060b060c071e090b0f04020a0507230d09080604110f091f12020f04020f0f071401050f0f0708060a0f14040608030c064b0606090a0513 63
    0x18051400100a1b20f002c8030002c0035000030a200300302030720000c41c41925200d41b20b00e0040da00015031092540c092011101915030102086078041902411108a0780d800700d02200b640c042c0d000342502880c030070000715050312454000382025403500c1e941c81c0c041c060140d03205900000041f5541015540b50001c60303100708203d51040743d168000c0b201c481182d40c0300b03409c004c901805040c89079016849103044a035540005440069130740d1304101b000b1402d03019401c074200c8809400621982080040d440710000c81050800130301c1691190b20700c6000c42982207941600c1c4188080c001410144501303069500102c02a04411400c0c0d1038001d03c4814401d00d800201c40003006180c100c07110304052060000400f0208003444c24110011724190f1625000f4114440d213501c00c0040e000400307115039108441040f40b01c0724840030a031512100500c4403260136190a40d1200c03074000fa000381050070444041d00700051049000c1c600300401c0090540030a00c642410701d55803046451901c094a0f8801030341c070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668632679 1250 668631429 668631449
    0x10c09030305031914014104230415050c07020d060504030908030a030e0601080c030303070f0908191b0f05060711030d0201201207080405030d0507080612010207020607060b060c07 79
    0x1c10fa1a1841f2107082a0420003600e622417a060503659a08009241422104072800b0070301e81080d19070816000340310340401c0407951201c420b010030000502c5c900111a030444200b8021680d8043d043c20143c00742c40c10194000e50400b00b8100000c0440d131080d540301f486820a043d00c19107070031010b4610b812180481d00400c0d601c0301000c980300401c1180900500807030008120b006075510100e900d07804054420b805200000032080515406221418090300c016004c481d145040802442e981c6584134500360f8055001c04155aa4080720f4071074002943c10028903241e10a1902c0103102c426840f940c81542c140f1010800705400d07a03002d00031041c8205030703a230001c07442c1c1182e424206403003c2d100c2140343e05ca410422480b500e001c601400c00c2d03408942410b213359a5076407420315a06500c51b81d02e03c41b901c80c0c41e200030040c5190b0407041140c01400d0654022049404210049080340706940c000f03940700c00e081c40448006070b85a0056490381074060581c40c1041c190030229464a4800e400180b001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668633929 1250 668632679 668632709
    0x2060702060c0703060506030f06011409042103020a030c2d030f14010e061c020d0f0f0506070e0a0b040e040305090901150201180f03110718020309010c0903030503191401 75
    0x5140400c106014004849d001d048554504909000074054140041d4080c03d5000c0005e030900150300303000b840508038200e4050740451b46001c018000d601000007074001c6494040752005c0e85d0b10403848418100201080800061802d18084420a00c801220380415444586010511090340218000c8120800000007a03506000c0514444000102014000c1c01e00010920020080d1001d890703001c0d8069440300c01100441c10201991615520b0107800460b080e5055800c010000603010b00c50355081c0e0f10324400742e950741c0c1005807a024074840c500c18110f05001c180310142e400d203070303143c2c1081c42402c0280c544844500800c814030003d0b844034040e040e01c030741800444e54082c02071003481c90801d0303400181000d00740e99254101159110103410490340c1041604103060401c80440a0070281c54900103024901564001039403044071001041e5081125aa080d41d004540503800d6a903d6140d03241543d651004840000c104204400481c6440d40120800c54508625042c0a0a0348007244485 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668635179 1250 668633929 668633941
    0x204060909050105030c1c0305122a09014d19020a091d1006050a0b040b0a050310050a0b12181c092114030a090302060702060c07030605 60
    0xb1034505a2086000f500034512035042c0d0b03aa0000d9818a44142d09040b05824155050443d001c0c018541c1c25680c000b8140140712000c0c01d0404482c0090700d03c400030010020302c07007960881c1402140c0007240421120341c0740c030b504100a039805140641610a250194000c0000c008410500007903941c80d8044428940030f40c18035040c00b42e6080c06900010030280d40e0803030703408204000354510908034810390750341110590034000803a89149060502c22601010440c8030f0341001031255204403032103446140000242c24100c102554101c8002e8181e45040c058510350680f241c1d480100a0760600640b601c4c00300d941e9482850a10240c401c0d154019155203081c00c1000307545001810340307444401070059040a600c40003c540c01c1401d5140b8600701400104602a40d234810a90000150413a400c620300744451100c144401d00140600e07600c18202c0c0c80e11002a44034072503080400300080110000b03001500300000107016a83c8058241880d21690071922b506110082e0000c864080d100c03014400c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668636429 1250 668635179 668635181
    0x30807020c0105070204020f1e0309150c180a270c1106070e1203180411070b0c03040212011a0301062106050408040302150c16031211100204060909 65
    0x68051014002095a19890350020380140a1100d0080c8903d0300081d032007150002d41010380c0c14640700d008415000350b4084034040c140f034008984080c000e10803500750700e0250510395200b50203806840e0401e86007959187c030030110100c43d03d4800750000b008041c0050408201418004852581c0784441140d158201c050416203950041c000108141c031202d80a10007001304819400c0003580c00d0050010000d00081400590741581416182c08049070103528064103058112641c0030444040100c0000d00404444034000c0d2071000d041107000740006800b070441032005641090008001e50170001c039000d91039003924440340422a2100401c03800c0c09031030509002e80c802405604611031900030420030050700d05804c100002d407080d074070343e03002c94140940c200449007e0340e006800c89660130410000800103071b0150040d03544078420204401c40241c03c001e00c0c001969070095210903402c5c81d801c0100c59181003012500c03024024850a5601d8803a544001c100400d4241c4030400c0e80c0340341c440404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668637679 1250 668636429 668636431
    0x1b14100905011b0807230406080a060605030103051c02010231050a080d031d0d0801031a0403050306060a031d0f06090303070804030f021501090506031009030518180a090308 76
    0x1c080c1035080d903000c06842e400c00303951a4070242c0c2e440e1501250040300c0e0720580707004802c80706c2d04a490b40028041451075005910300c1c07080802d904180511940d5002c03c680c1c51009100203403103a0004240c4103001c1000805012101e24a4400507040c40402070b0803902001d0391300489200a100e4000803c002d031404140340c0000d10b0200c4244000c0382c80d19218940315000700d0a014100f6035604d03181e00600441c00c150500352000300045580b400820b1002501000c020b01040d100750f00901c0d03a88400302c440088032442541d0640d140d40c01c0d034a400c02440601d81017184100103050f200c00031350b0415124a501c201100307070300500070101a46907000311420904090325000c9135410030407c01000301e800c08040b58100f44e140c68001411582d10404a04105010700c04124441c2100000940300320300d90080c13401050102c043d900c400600c1401c0000f2209801307401008150b080c09410036a5070696016055508090100c0c00078544140c40d030440744104035a00e11640741d40d0741c840e5040c035500c50145 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668638929 1250 668637679 668637701
    0x19091a0d140c041203050408060f09071a1206041d0303071d0f01050a0203040801050109020a0906020d0914030307050f01091a0c1c0b09100302030c030d1b1410090501 73
    0x11030705040401481806201e07501540701041c0340c1c0303910b00d02010320502c1110700510101d42551100d0a0a000031425200103940608061043c0d4a001c00c40440380201441c00c031150200040c0307421801d12010002c3e0b0350051141c0d620560b6520108050002e12142405480803200615641c1c9084180a42401c075400e440c00000900e9019031080c1c0c0d20381100b00210b03e8000d00300551036200101c5d08a04e50f1195801c085150b50810300001444041c07900139010300040da13240c04c403405840d042d0480e500d0310100d034082c0010f044e07280b082040440401483c0514a0094140d03842e103800b03521103d180440c1100e11103820380d920603403502405031a0105075149150161001e9180c200121140005d0080f200008109007080a1640c0b4940e000c0d03002e00c02c0803401404142c1c2c00e18080328000160b0f03100d44001e0340203025a65910301c0b5403a000c1058044175000ba2030314903080600000440009203414803c03248410803903031501060383c00304504140c40c000c507500407070390000300e25006081d41c04800d03030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668640179 1250 668638929 668638961
    0x200d050a030212460801060905060a050307080912130f050f1f18170106060f120b0f0d080c0708030909040f02010c1e06050c03040819091a0d 62
    0x300703092104014210103042010f40c1c1072035100d0b0482c1d42c000050381c04144c4601d100712a44544058596007019241d8100e41140d02c1c4e0452281d40d40052001a1098420010005804200092840c3e001c8c503d081e41124851048800701c143c000c91080e080e03885001c00e5040e1103d001401c100c100610031a142c09090300391200007603007840001251503c0552501c480d5842ea00030502031109100d4190303071802201c045066400346941d08040c1d485892a11400000c3e94248000402d503207010304448501aa070702c1d40c9500541841d04081002800f50300b1a6513848101c1c5585052255601c40e181d446443c0103419850342c2c0d10051022920784078940c1d00980c415001030140c0d10b0240d4444111580c840d4003d0a10b180c801030910040320ba14411950040c1540da05a4148010308500c000300e128841c49540104403c2d1134980074407014ac002110300506d149010130003408120310842e402c01540f41e0b03500b031055655131103c00041c6864403402940d09200400304582c4800701a44c000c0301d506006c4214 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 668641429 1250 668640179 668640187
    0x122105040e06150412060905061509060906030c01110307170c0d020708150c19030b18041e031b0302030d14130b060307081605030d0206090a200d050a030212 69
    0x50f24580c5004911030001e9400220341140d05100041d0455501180d00c141520f9151070f091540400c2c0384039401a03203004409140001d50396052a0040d580940070007401407061005802c0110350400c1108401400e03030200b405204000b540d4041206140c0380407038000d9440d00400c64400f0314090040402d401198000c4000300507611001c0346004440d14640c24110850362080768640d8188142400f2026889402808160a139455442440000e20848051468500c8004503085c610300980380901100c0101228042107045031025450540c80390415004401c00403201688110000303030150b015070400103100d0201d80c101d114055540c80740c400803045505104142c420900400e0310f0091410b1248400720b007090f50704201d005c00800e2000d0031a1240f07030301c0e54150685000d00c0c5c07003264001c0c41903031100325a141c00821000c0c41307843c1c0380d8001d12100354903071500d15803003048001c41c044030403010115400c00e03101c1d0a84041224040c030010440100b1925000746050441e000044603140280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 668642679 1250 668641429 668641459
    0xe0f0609120a1d0409020306070f1206030206030f130506010e0916140d061509090b07030c1e030902060a020102030f0601030b0f220e100c02060c04122105040e06 71
    0x1c0e6020484070164085070703d1200300440820b00925a10300c029605204580c1040182d9038001184040c0c580180d440a1005100b4543c03001902c03410300009500400a0000030400515001c403154003408101ca411800c1c1c400e612641c3c1010400e8026002880c0044104001c00f0340410810a2002007189900380700361400948003000d0f2620010284249904120072062007402e400c0503a041c070142c00060701c0c1558449103000103101030f0004440c0e90025000042c0d00c10b0180c4030f0001c600d1000e0304c480c2811000056814110f20f603180401c400c0c555240d5042025803609006804080c01076000182d4034240314100300250b66008210904050404015642546444031103c1205909030703002c02220480040b21650002007144c071804c0c09240c4200348840c01400182180120005103040041c1c44042c0d134100e88581d012100e040044000300020040348003000c1d010f440d5903010780d05007202c80161084400e01112a26801d20004201040500040d95058080340d085001141d41c5d0f00701c48580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 668643929 1250 668642679 668642687
    0x60c0801210201021c031a18130c0306060611100b01020c10030f0e0d0909090209010e15040f0f18020901031403040b0a030c080109021206060a030e0f0609120a 70
    0x1c2660390030795480d988416400c590081003140400203a4264200b403080e8034020040040070000d18000050b0800007030401a801d01c140c4001c1c1d47c90480c42d0354019a030f40ca0754140001b860212044602d0441d8450000c0400c64a04c40e42c0081e00c002d6543c56098440d035148149440318042d41180041e2600c0383d1a442a070300041e00c80c0c100300090351001100115850241d0051031f082050445907814030700b80c0c10951401250301640b0307030f1030f40d144c002e0a21384800c0040c7c112946050025040840e0000501c4490218035100f0740c400d40008e035010740d030303001500802c0030f90340ea20411111558a950b8800141c045900030350146100f0010001c1c041760f0280c00003450b018061201a20f00705030b0031105408100e0500440e03000d81003295002d0381d03c09084c1c82c000d004016202c1d0b0b000000b030f0f10b41d002041d084240d008651118020188002c9180c94440c104012948505804000e160b0340d003000d41e0b0142c40511400800c0841103002c5d160501e03144040f103041c00404000c495000c0300c00c00c0036104080e08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 668645179 1250 668643929 668643959
    0x905030c0a26011e0c0206012106020f1606051b030c0a11070e0f06040504021e04060522050603060402090a090f08030415200901080408040f0602030304060c0801 71
    0x180e401640300d03810000a8420b440791210203070541d4240480c2d05054440c540102e41c8254150108000070300d406a4120f071101c20030f000c0c103c001c05041c1d204002d83d41c015480603102c0c90180300c1c014601104024064042d60040c65441c00c04980000c0c40d1042c0000d9228641c0d202c0f42141000701c0c13000b0103a000c5800303884001d03c02140d885000c541172449501c103081d200e50740a095402c440c0f4040d141c0301c1d900e02e0343d5000c0f01c0c690546010000000c3d501d0400d802482d01131503001d810b64801004900c00042602c4051032110340060ba621000941d9591382d06101a4003100d605503c1c280c034421102050655200800c118020341c0000c041c000140c6528051980c40050180009501c20b040c1ca80242c0ca200801009440306a0110a03c8240424450008071103d2005000c11081c40e500002c4000b0300c5001c0c0120341000e905100c0c01c600c030350003800501d03485881170402a2800d529804040c1050b001c039048030005074070210400c0208001072248000e100303107504111110b903140016404100c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 668646429 1250 668645179 668645189
    0x61403040c0305010905061501170105101715010306050603070806062808070e0a0302100518060c0721110112020903010e0105071209050d0c14030d020a0905030c0a 72
    0x400000040c090001400d00075000d581e000d8004d002e0040c00782046580d4000a403000101e070101820810a2580a0030740700d000b103c003008580da00c9a1806003049a60340e130b889050f109004400d000c1491410101400303d214a031410703201c3c1c0101c04890001002c540f1250403186c0102820014400c03440c3e0001300060b40f00340200c43c0790356500c4801060f040303941c000c11400104031078040c5075102e40a81152519100d510305030348283c05c1c626000c1c2040400035151101a4104031004400e00b507a0340301d07400030155482c2c0300902d18101e11130740d40031408a0380030400b0a0380030741150000307010141c00e0710400b503401d0301c600607054500407242e20303a54480005090090305212089558202e910115010303282d180d04000c2c02000241d0a400d01c40f03000c1d220443c0c03c60300003000010300b104003a142e48100d0a50079085001048184080d807020348044120440603103d041d0741c03041d1004c03000c50420041140908035400503071910540100982030310410740000348a41c11016086006032903030910782040b65 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 668647679 1250 668646429 668646467
    0x180f063304020a12020403030903061112180718060914070909200d090b070f120b01090807140f0d02030c0d0c05030307030e03190302060103080304020411030f100e0106 74
    0x305100c0f05590f052554000ca90758907002050000034076400503000001c03203005035030a20004002d0041c015951183c401681040d10308400420040700f1001c9840031030b0b00300c0d0001c0b26200e5840358880e41210b010f0b221900010350700c2d10404c2c45424071500070012100011000d82500f410003a00260801c18140195584c0300e6407400c480400c040c4181d0654160b941c00f602c6140c0e1942841045805425502e10030386081041e44045280b00c3d00c500c205445050760b075030314022103403410500310014001001c2158100403000601041464040c041c1400404401c01d28601040c44441403090035400d101c1002c0c4240384514240015031000b2600e4401030004171180790195400b842c010302c0e07d070b140380c00560b0144004502c0c5010150012400c4100c91421802c035009403180c402d42d07114807008880000c0068008a004100240c41c5002851f0030510090010a10f000b28110104060b0811140d820307020a450741800040020805100003905105804488640c10214003070280019450310500131 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 668648929 1250 668647679 668647687
    0x106050925021002070501020d201e0409230705090a1401020106031407092412033e0a0503040b07021306030305040501140c0a020108180f06330402 65
    0x81ca2081c006481010003104045403a00098100310b4000d400000742204d41e03e14004941508582186c500c01d40340c211203082c589010445202086445ca0b4032a0b88921100148070224841c40396000b01070380c25000450700040304406103190311008102402d01406d010040003648020f80310301c011201a01c0a8280c04444800d007980103d00408e100e61002d084101d1490620020400128851040f156030100c18000040314418200c90115a41c01207a01400e01d04410032024190303c01380d02c3c0b803c2c00380c00c0404040b04145102d417440564819840d01082c02c0716000300c2241c0c3d0310024100800c402400522001d4190b65030030359a44914080c90111031808100d00045540d03c801201d002e4521a400340700b402d80d42d203806003441d041405003501144810341d501280c0903141050f9094040740d540201031041841d001554100409014982101755034421100c444808002e0186001a05401030081d450310009149004c4850700c1e103990041000403012550021040c146041c80c2000c550060b51 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 668650179 1250 668648929 668649001
    0xa0207020d02090108031308070b1b070b04090207030f080403021b0f06040902090109050105070c060f050c0303070903031e140f040f09090606050d0b181e01090501060509 75
    0x305001d920030081d44441400000302d1048004005009580c00d0004240009502c03007a4446d281c9402d03014004101d0424009040c401d07070f00c40440c04080c2034000c1914022a1290001c0d032850744241c11550400740c00240101c01c050f40071002c00b51050302803400c9811410240d034000c4d00c80014180442206c20070b00e07500c403065580c210008108413801010b0b01d507a40d0f66900904080d401043c3c5150216100c40303000a80c0754003a000311a1007650200c01c02c2d1119042200c161600c2518074840340070401c0034000f01601c010204019030050b07025486a1500c1c62039850010180c00d0300b210381514500302d0b00041800542c01000c5a41c444007045034240e201d00440d8925241400390350b10200303196000c404001400741c86d90780134588490051a05214840c0c44034107100d80481500b0300241150000700000d00803d00c030081903030030207503014155840f45101900c90f25824040a440503481e955546101c01040f03000d00c108002000b0660344d9011600c4c01d080a4900c0e20f06802c078514404c8241d10380c40351 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 668651429 1250 668650179 668650189
    0x80a200d020405091c0305060909160603201804110f12040f050601060c110a06120b13020406051209010b0f060310032111070812090102070302060708031603140a020702 74
    0x117000c200c13411506002c10032413600501502068507898090390044000c070315203a1002c114035040300c4100ca0b61a00d11450704401b00c00401c01c0c0307a844c031a482407000156100d00c3d002e40c0104007101e4624120780d2050b610f2030821045807047c14003044460001c11284020740042400c5e2070521300040d43c1006190354901b8407841102c00c3d90300050044c0105000411080d802002e508a4a40204024441c0c0c14a400a02405900c140500c4020540d00101e01400040c20707000315201c5000500461b1041c4000e0642209076040794218402244001c41c03d44140010000b100740e0084001000f070041e640d61501056013003510000c3c880c02080c0001c001034035a1024928400150f40c0801502440314030001d120a0300074101c80b0704000501c0d821054030f400d5400061075000d44400002400e002003d02280140035070048403854154001d215001016a40d0300000c0c004aa00803042c040d038070719010341c5018000c0070b4504028103240c50160150903040c00e0304641076004c1ca2106005a9500290002031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 668652679 1250 668651429 668651443
    0x7050a02060c0303010f150903020f01110a051c0e06070314071b0e06190e090106030c0906090605061201052e0c0302010510050d0f0c0e01080a200d02040509 69
    0xc0d42001001a072400ca1050010041d8129040ea441141541d0b0301c0d180700c00c4220300030000083c0092a490801c2c001b61501c03038a10008588141041e06408100c610200c2c100b0305401c8040c0d486400c5846080c40344514070303025180000c0e4074a4030b03030410001440091140d00482c031002c0d041298250b250b100d400090811101da0b29009405a0024011402500c000400031300810b0340000d98800480e00c1820b0202c2598000c0c0079219645081c142445a42030311440014510542c40d901c1d020004042000400f404015020343d9001141c0141841c03040070a42d002540100e004070381c2001120a0020284400c6054810071035103001c84116090032520346110f81350300002a1600b4020020240788c11040d9036011078804d070020f000e180c0c0c0d8802c921500c0813551040c141c010003030b0703c1e1050007d00020103407100c483c81409450b0a02e600c681c250010035501742c010b00303500d03481080780100b441480c078010007980c091622441800b88612000c6000b8100c0300d070000307000c1c0351a040880e501c00014880c1e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668653929 1250 668652679 668652683
    0x70b0711030f03010f0b04081b0310020705150f070801060c1b0914060618153a060b0a0f0320090a0906060e090406110310030b0a0603051207050a 64
    0x2a07842c1c8000209000c200d41c001e100b04200c810400c10000303241e8417580d007606d04650b5810041c0101e50f0041c20902c0e00c3e0f100b42540283d050042500408005000b4405440300c00d010700020722828800c000c802d81401d00150894101880c0d46040080050780702621a0541e0000c0c54448103c2d089483c101d00c40f500700360001802040d81c00e00205040c1d81c146e00c8184070100c42003500e829134540b50184001407040c40c421040c000f88081240e80541030511841903000081d52865241c0700c030798868452042401c1207864007008000c242c20b04804122210074608000f100300030801742c0c3c9084190303240d9100f03280109040c064284040da04040c000d920070741139249032034940c140c02c031708a10707812141b5480f00300c0c4580300740d40c031003008546c04c6e6241c465101603501940b80d010345182c0c0a01000300c0000f000700122030890f121140e003101d00e90b0700006580584107107942d070100e980c00d6241ca1256480000d00e40d4100034070740741c8100081440010034a143c0302003000344a81d980c4039400d00030700740200c2a01c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 668655179 1250 668653929 668653933
    0x40f1d15011d09151e031c18060e090c04061b02040f0c02031b01050c0a0e0604241205070c060f0f090c0305070f060905060307050c011a09090a08070b0711 68
    0xc00c9504c9560756099000100100d4030011041002540c5503984160395054a0f05070b846010402c40b8981894051644104141095040d4032064000000c0616241d004a40026284000030a140c00d000f038010790000701d40d181c51b038105801c01c1c070024120200941c5001c4005003051208095440c0c5a000500101a1b02c2040c80170002801e0040e541e80c2c04a010b8850056840380c0c5000124410321520307004442d01042140342c00d106420131202202001500c0341c0c0325004100004141000d118465030a10310850314007503807026618080c0c58040303404d0100503154102001c2081c2d0b03544c014006000194858000680700c00a81500001000c424540b4185549000c1202c2c00b40000000c20104482c0302e00d040300c0a99442d01c5070a81e0100e001c2c42004086030000c00107001c54070340752010b15401083c5150280c00c2107800c84446003544d9008512411041404603528640d080030b40c211541700114400130004070750740e6958043c55109844001c0c1c41c0000d00c1e404503030340c148078025449007009481c00b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 668656429 1250 668655179 668655181
    0x9091506070b0103150608100b03010e0f150f04030e041d0a03080612030f0304060905010f020f0909160c140f03040807090501140a0b070501060506040f1d15011d09 72
    0x19105020502c280426944454040011420241640289001d50340b0034405458803600c0244890301a02c04200c81035031554032101c003040311907802c000d20b087d0102c00c176005001c1120080700152442c0000b50030352841ca04007100f0800480d4104146002808050b0380001e68450070030f508540540e460484840c0500809400308145607001e074506016810442d51003440391000840f0603075a209002060b070a01006000140100700c8a0b841001410b0180d00080b0300c0d03284801c034030f00c103d900c910080540a00086000c45860500c14a080d512440c0c50381c0d1070340640c0609401901014071110000d249070010314406440400601458a101c1880e2085940b1142c9400c4044c2c0c40301014040c1344555450180000f4000c040031441170109040039010701106070403c046006960310601040c2c40035074a0b0309000405440304001000180100000b240d00c0905210302d00c0310601c0d40200070741a160000042c40300b400f03601900284041e80909002012a25000201c0c0290940600b00780d4001c6081e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 668657679 1250 668656429 668656433
    0x406080316031803230109120503041104090c0b131d0f0a09080313050f061503011a09060402090a03120207143010020c0307021908030909150607 64
    0x440101d15a81c442d45421000200d18440041644854400030b000c1100c1815265503800e00c0903900100c2642000002c01c0700d10300c0d500c450302e01050103105880051700c00020482840295800c0d01d41b0020111014400706415880d00c140d1503645e4080d02d4840c1c1e00028203d40041c905051600080080c5600e4a19803090706144044201045510110303032030f240c00c00600c265000e0310409043c2584405100e0454035010740d1401e003000c103030008a0f054440d201543d000c440003082214818581d03100742c3c030030082481c0c00341825264100c0184030300e50400c600d0010b041e6502007415501c2002620016252100880028008041c2d0b50001c1c000300a202440310095038040303001c20603941051030410003c1c007580b0901c000f011a03862f0400610110b070006043c4181c039484140c0880c02c03a07500311404400e1500401c1c080368825405034166034000901c0000f14240243c5503d440f1102408c6401151b1a00c2c00c816100d1242c2d220300d134400d502c072100181d96449a80b482c546414030203001152500b01d54 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 668658929 1250 668657679 668657707
    0x30b071112160c1503180503042328080c0f0f0d021302030a0612080a030c020106180e010c09080d0e011808010b0301050f150411070f050d091d1504060803 68
    0x1184070000003031b081056000c1d4071850394203240100f0350b10074000c0d4545803410f010340001520100c3c0c400081c1da00250f030880d003669454a00b207450301c0781c81d8860403120000c0395496500780659001000540040c81070608a9462120400100200340d5281c1580c01402d000541c0f07241907a00c000b5130000d096100b00c0b0040c0102e50103140b01703da0b22076041004c551140c001c40c10385007034000700500c406020400e030800755110b0b4200d5025507005000102c1e4880d240d100c0d080c07101600c0b0800f0750700795170703509001071201c1424017a03812800013038105845582d0034400c0060321103914001d89800d02101e20002c4225901c981e81e100b2054400502c0042502e1700d514600e0302034180c0e000464400d43c200004103c4003d08a4070590180040c05807007000041100c0502002d00a82c00000589440501a42c0041100c1d48040c248452143c80034001e18207001d031015000350790f80c3c2c10940840008030f030329034403040e401c0d0000d503000007194561200400ca008002006000280c016043d81c1c00301059940e010510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 668660179 1250 668658929 668658959
    0xf2f070b13080601030807020103180c09151508010323010213090f0510090903120507020c010f0c0b0414010e0a080405010e120a0f1a040b01030b071112160c 69
    0x70903502500c0441d0307144440c9554030381c20f02019109690402591006600035441160403c9248000f408801d40d0350f10b55107200f041c0e507032005802c246c541504180d545060782d01040940161280e0b104003000a10008101000500006103202e510348075412540181044c0c02c0e00002506000f03544d50094800040d210980611070b021003a0300b480d0703294110788401d003d101e00c15904844881d0301c0600d002c000c08080c1545040c00d0381408580d02c1e035513100030b02e01e0080704c1c8075940c04e07001484610106e9000511551040c4002000c00200008010010742803030a0150081d4108100328444264502c1160040c64480c1e40f0003000e110f410320b290200300d0500054411103500340c0f20082c40040e084140034418a1000201e0000d40144da50180080d200c0d200c415500382c0904000010810175002c0052417200a072416250121108010000c0042c038400003544a03203149813018000b00c84403102c5a980101c84880122a1804501e040300c401945826124180d0001c2c0c100400315690b5003d21041070f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 668661429 1250 668660179 668660197
    0x201031806091209090209010c020112112101080f1504022b060605121f09080403060e0622030c2f04050c07020105041e12030206060102010c0f2f070b 66
    0x2440d000005d43c0000603c2501d80500d410b0b1190004401c0542c011140600c042e011070480304c1c0d580325110f90307403840d1201408190400756030845015100312800309207494140d000d034140e03a0112011141c44540030a04408600714044020f009450360310000301c0c0700c180d5070700d914010550748025004110703c441440ad10f65010b1501040a641c941044c8a080d40d4038445001c0700b40d001d081c60303240825005240100020440000107030300c80d00c55607035088992261344151540b60325000d4042d8006403d2241d0fa0b04646d120002c071261025001c040f024100d40c3d810701505002483c400041070181607250740300408504403060007090b21242000d600441401a124052b038544000150444020030498175050740503154035041500c5c04070350451000058810b5503031801c440000050350000c007400421518441d070041d00403450000002801c41d103c07200c0f0101007001112195280303c0c0c0200c3c01081000441c0b0403e00320f4144800000c14210840100c4100e42c480c80e00c0c0041c01050903805004000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 668662679 1250 668661429 668661437
    0x5090a150614040506070c0b0304210503011d06040f0518070533130b0306010201050f060906010c020402070203100507081f091d070b0406030b090c0702010318060912 73
    0x1500ca800854100d4010b000320680d410040205100d2441c1c81c0e00505452881480f03000b00458440800c03101c1900b041e0740450315815210b041c842a00f0741c5032000e60b00ca0741c0d035140160031903240841c3c26580d041400c180c0e00124403484046019074803150809040c80c522404203000c02d04140341d0341f00e10511000f5070020136008048010401e4a011500c4294252500204810300780620040030a644007072941111158400c2009903003c51605603030900038901e0121541d100d2401500290075103034024a500c005880403004c01000e6552001b0741a0415820301e054048407416101290003403047d8180654103109031460716007034181c03030b402252040000350b40c3c0d089207884481000400c000341d1030005801005400c030a01c48009654890340780007107070110750121941c9541c50f160509015030400d603407000001074184542901801401c240e040c1c181d50390345885c90080105001400740e440020704060704d82d252000c000e02072140d9418510780000f030402c00701c01c00d45801c030503414180c080c0034041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 668663929 1250 668662679 668662721
    0x15130c23090f0103050c1207020a171206120d050c0102071b051c03120b300f07060c02090429060103110301050d0b071418150405010f030905010605090a 67
    0x281d41309001e200d0081403c1c20790581041e580200450348401c0040c1884118450743c1c402c280807818107210591000001420703030faa100d224403c480c01000f0003c0c5100c1c0691007080d4000c40401c4002000d038002c03d15882c0168941210b030342454064483c50350090b0501b03181300c40042651007403400c40d0b4103d50044900307203607405d00c1c113292030302c580ca0720100640450700010400c0010f201507007100070003100040140a0840b0800010034031034640c82c0410409910071203007040700f00003c0280344401c0d44980000d2070b2107450b1520003070074411281c000a014090305e0011500b00048102d426003503140710f00f54010039002408007400101011185240081c0c1407841c07055010351130740700301d80c1650310141002a4003a4541c0b5040310502000e410072040003100d00103e036100070341c03070701800600071003100c42d240201102080103030380900c011103070301c010004000070007081ea003207103070000401903038100030681c1d4220782081801025190300ca160000e120000b08440c000e040e40c4264207181114101c88a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 668665179 1250 668663929 668663959
    0x210405030114010e0c031509190515030a031211120f2202010e010e210709020424030207060515120604030203030606070c1a0304050615130c2309 64
    0x200002c20303c2a407101d0314880c030114200f460b04000869020350807961100c14111b4200100f00d0b0308004403110317182d5100ca00300c00320b0600814010181c00200026a5a01081002000a40710b200d4014000d040c484c40d05943c0b4141420742d0806043e07491503500098849104141d45140008115803403103003007008100044542c00020f1003109014000c0b0082d01c0300403500c0d4010b40702900c03426031403410301c00f00b11907040701c1ba82d03080f03220024001100441c20809480c0f82c000707403800001d03230800a40a401400180f0144171010008080c180781c00c42501c80e01800f41c4000c1d0002d105842c800b908690800342008003a560742940e044c0c59030b105951955042140c0003140d900c44809440090041c1c004201060003407420501818a61b0b0207010b20003c032942c2d6244071004d540c94203c182c0134100c004001c1009100c810f102480e0701219658610f4820328010f030020300703d0000d050514040380d980d640001c841c1c911a004840400c80b05003007405144c1c28000d0341590940019010031b01c074184041e20848 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 668666429 1250 668665179 668665211
    0x1031406070201110403030302030702031c2f120601090e040614060105090d1203020f07051b01050403030219140d0c060f06050f1516110910060e010c03022104050301 73
    0x18030113042c0b40c1c0742c0d41440e00b960740c11006548050401011844180407072210343c80400021340203e546000001140703091900140c0003551400b0703c0524104403840f02580c1c0211040c100d0b400b00e02c2135107040300c942d40c945005907200e60150704400107810035141040208843d07903016211441400f02d0307005040d601d510044030716200b00342d101a04034070003554520010f518400a810030030b1081c00e0250600400701c280340e442e030300400c0342a1205d0380040c00d06281203510341d00d507580f482020702e881c501e81811034802940d107054031052012009a030f030024a05100840e03003080e9a850510060f20400f0700d0fa80001801d14001e54070540e032103443c00c481042d00c00b00c2845458103c2e40e000e4006801034007260200002940f95441702c0c0c90b4000204600c4101c2100d401e080c10142d4031414400c52701c846010240003541c2e60003080c4904440034104180840340d0030011242e0005030918021704a248145401c0342070203030245c0710350700b6075055000105072004008090000c0c1c45050b0005c02800b0b8004003900c17 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 668667679 1250 668666429 668666441
    0xb120312011403011d0c03070e07050d050601091d0a0609020301240203090a0303021c02030a17040203030d1806050132010e03060723280201060b16060e010b030309042301031406070201 81
    0x11840410050043301840c0d0030203540858141800d8403015580c8690b08100c0c100142c1c0761410310b280008000325480c4a00c50700c8042c1002e22000c5042d0760500a13100300400398401c05c1c2e01400c41075618410914070805c100c9044203805480e000d181d50381d81c94080d6032100240320f9a1030762803100700711255581c40001a907400e511542d03035514800120024041e1801170240060742c05010400c00055038800c1030181e205841c4d14120f207284690400e0401748203d5006030082008015071030400c0840c0c405110000c3c005411850203071560406040c0143c5080e082d94010075014028202000701d02a04110500408080c80840f416182e500707803007407211442801c68180000303807004040012810600342800d240899400002940342c0c4070307020080c0940102544440d24000350b90a141000450b0056000003960301e0000d100706036412002039101e010700c85895014030ba80b40d030000c0b0410400200c100c0844c0001b032141c40300b540c517810540c86d1004103007401c0880f84a5a80403400302d1380705109c0e80c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 668668929 1250 668667679 668667691
    0x406050a0908090f03190308061002010c05030708060f0d0303021903020403050d08062b11010c0c1403070504180b070f0f030903050d0f0b120312011403011d0c03070e 73
    0xf03140648040c100585030380c10303030016501842041c2e00c6420320200340d200014020f010f07842d0000d80d80313050001c201d10031108442c044116410002c007044130a40100c1038a400013010704056203242c3d121004074840c0c091800c149a48250080800818507400d0b9004140b0420303c03441d0001c24000e120741c05d8090344034511000305030f5807280c9000c0580074403c0c0789058100b1001030220000c1018510381002d003010b41c1d411703544240503500303001d8204901d3344800070780c2c0d900a091500c01c1c0402030b00c0c1e000341d01196204011803040c0c8940d04005030340d030078802e800103003600610822500c240105034103440c042158040783d0788440c5030045514280101c54650350051169aa41c843c4c200030281180074066180c01141440b400303002124461005004032014644840c4c0c0000350114400200441015070f807003540600c6c2c00810107241c1101c16a0740650555016406903203010110801003801880d015480310154186460481c04401020078507050894046003200c1d9203903140c07065810210416264 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 668670179 1250 668668929 668668943
    0x20906040b031e030c07061107062607030209060a0c0b0901020f07060905010b041803020714030307240204031a010b160f03020f03040902041706220501020d140406050a09 75
    0xd40d07070f00c050815044964202e12030640c0e04011081241600c2e0400d80e40100b000703e10303038442c0200959800c004100060800e845d2000103d805809402ca02c0c02c0c80305403682e410886540020701d8140030350100d8008810107000c0964912141000600c51500c5140440c0c201020401140c0c0250307050007580e04820743c2d08041460701d080d568440340100010304040301c080d500e4034801009a512480307000b1003454024600d8281404500d40241000d0464010600103420000b4441e12500e00000ba541030f20b50040c43e0074010140860742442c0301c805003441c52109800050044100310745051603234144480c0440388511071f43c8a1800c40c01e28010143c0541e842d00110a1010108036802d0076544254028015219040c01a0070014110b41c0309030090004c1d290001402c10210094210032000074407541d02600c8a0308210384022480c050a0383c0b4040050218591401405070039030445100c0c0d05911802c015070402076510300b0a2010443c0d05035420792038140000c48001240c02442078495004003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 668671429 1250 668670179 668670193
    0x17010f06020717070b13050a1503230112060204030c060309020a080105040203101d070303020303090f060903090415180b0f0420181309050105010b070b1b25020906040b03 75
    0x440e40c15081007400000107084011b0002d259190740540745e016244520281d03060039000c010143c01d031428030304191164a26028101840400107564505446500c0c41d001010109030a100b80a409150070190460b41d44680004000f17130140c0c003182c2400d100f61398800050759200f0080e03003210070444020f901904a4034a0503a130390b080c1c0d0300002076041c000b50440c028000d507413603443c68003040c2c0c0c00c01c40140c0e10000910000107400c020081542e00c10100070300700c915059610356164020f83c86240c0c01203444507442d03030301c0c440500c2411b00070784200c6c03000d80681c11050b5000c02c06083e00c5580d19000c0d107064030b400960f074202401001140c01c078200e0070302d41d80003100314510707440d1f40045140c000b80000007420584659590703e41810048d83d0010109280d88039040140c03c40d601a400002d21240410528000813440401d4907801002149071502e42e42500c0f148034a2445160071600038402c49100b02c501d02c408100000400d0760017500d50035815541c01d0300340070407160954403c0750300d0307480700c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 668672679 1250 668671429 668671439
    0x1f260a080405311e09080f03071b050601060305220201230d021b07060816020a0b011212030c020c0f04090b091507050a090909020117010f0602071707 66
    0x610720f401001e903503201d24025407003c4030881034100d00c8182022205611881102aa10008820f0300c101d0500d02d03d080112044555034401c0030701c650140320701c0e4005e011000034065400b810491119001940700b85490607080d04d0800d860700000d00944000c00d00c1d1401082005a001c0100705e00c8019218002ea503800c0380360019101c1c004c1801c503092026000d1412003a8840c2c4000c06048188140940540c96004008070300440040f00d155103515540015400c125003a4000352064001000d00d49500195800703480403400d21304403441c0903042025030000011900e00ba0b0180c0c4d44601d0080d8030038164801070b5001101625030034000580107900500e200c150034a409002c00002c802c0003400024000c00c42e964600001000711401032464001080028a42c0c0c2038262440d40203a40d8500a40380c001e004502806058503406600c4903130741d641c41c007070045901881040d1110903211a0050701581d44602c1b2080400c014041c500041c01420400103003189804403607145035007060080c080700703800c00e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 668673929 1250 668672679 668672689
    0x1e04030e091009020a090612090206040501080408091c060c090608161110140106050703050d093306050603100311031c08010302010f08060d0b1f260a080405 69
    0x1c0c158a04a03100c802c2d001552010a00c01032a5501294590fa400c80340341030400303449600d804040c01c0000381000a180d006940c0c4c0c00c2118140c0b0170900303102099072907e04104c407282c040c0422042c2c0041d80c81c0d0030803503040c68001214020904c51041070190071217803c0211484036440c81060042401d54001c19018181c0d440f40030105e09023490310b04105401c580446242c1040713008221421036072480240710200700305100a01400c110f040451628060b56401001d510480d0000d03628a6600c421220401c80c461074400d0b081205408481c40c0c1450240c1c0c1402a4510b2130408640240b40500c009010309028080d2072140080080b80c807603451454a408800321050b140095041c05040d0792000c40c0c031600c0703641040440e0a40c2d504809903040d480094004001c1d41c2c48002805028800c201d00ca0751100b18845e80070364030449000c01500d410402006402c0d407058a42e80030101100d010400340c010305441400a045040320844c24001061340f83d480d0703522244041d1500c401008248110b00708 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 668675179 1250 668673929 668673931
    0x1f020703060b0607020901030c06080705030c04120c0b03041103061305060c0702010306050604150f080402030c040f0609090f0b46020708030a0506030c0f011d181e04030e09 76
    0x290010713107012525800030750000402d810803030340910401810b1024a92003444242d2040c2141001850b605000f800c2c40703c2406184200d2199416001c40170003048140c42030200204260700768240c82c0d0400c0c0c42e22240d00180c0103030403402031150800150a0902c0700c0c1d00c40060b950000003400181c1c8551000110315440044164181a00c804001825494010041000b0495110002c08140600c40000c1404003140c0950040207a120f0a0002603507000c640100e103004220343c0001e00e082c1000002c00035205541c051000c0519000c00300c0705200d4680c0c205241c0500c034003107010365640c41040d04100011403150440e00080b28161210348024a181c11082d0b002907081464002c040103104a410b0740d00501007100c070407802100307100070a480c602030f20786c00c101c0403000b40140c45442d1010490150f200311085040150501d0500420360807040b40103a0140c0c09040c1d00741c3d806519450407042031050b910840355449450b07904411400d1030900038052a8103070785401d002403c0f5410850190300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 668676429 1250 668675179 668675201
    0x12c010b010f171302100206091522110a060203040806060a1202100e0d080703020c032a0a03061404120302120c250308091005040b0c07030513030506061f02070306 72
    0x113055640b01c016a45001e0201d040c80c10584c010314407460301042560070a40c516a80c050411598801d01c03140307413405580d4403040c401400840341810418100001160384a00c016030b0000c00301e01c004259a54044000c02c180c0e84000d040fa8281d031180c00078040e14001c184103011071888480e2101c8018500f0b0194050501c03000c0c41c0c0032030a6100800011041e00d0140c408951441c00040e02208068040c001305140220480203441e0654810401301c84500006c030031042585005c01c80c1e00d040c7e42d1013071400300240d80c200c1410400b9078031009610605900540d0181ca02400c41901d020503240b09000320f4000c00f400850920040d211207103403600941280100083e40d4405d403a250300c0f44c088180c455102e15000380d40f40ca1007410300b14019410140301d03986243c0441d0500d4104800700ba4204d24241d0841c07142c0c0140c5543e441c840c201141c46024200000c241804800000400d0000001c0e009014090407a07980c6100c064030030034880a000607105079070241e0040030703040010901c2c84c2c0c03142107050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 668677679 1250 668676429 668676451
    0x11070806060409390602010e0d0806030f15040323071b030b1608180303040f030207080303090106241d011e03050a0c03060323012c010b010f17 63
    0x9580705001e460544e01000807643d051103041001905443c01420300802002c07580000c10042011892039902c800700c11101c0e100307102c103400c040b40040d2000c21044890300b0401043c2c83c080313a50001c5c00c1440004c00d40d816000556108211221303102190a481404021440440d19004059607042c04901c0600c0f18410b4031130f1104c8002010543c58081e9501c030b807480c0c8054460b0707107081e40c0d000b40400b00081c00494501140650350004010b00104880c0c000360048402c40040260f890300303c0c940400f40d0031400b0b140c0000f00500040d06015000b10703040d50041d03074000d4504081d950420420303881484a10f40060501c00904200d11b51f403001a07100d208040c035003a6122001c1c0b4112a24221246812000080d5264204200100c55219031010340d0716508d41030013103918544640c40700d800580000301302400307024074142243c4025400302003040001822030200780e24203d01e20243c410030340c922070410b5080100e80e80742e640c1700d031044a00c00381c1a030f1164036002c50180c4551f1440c1c24002e000008031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 668678929 1250 668677679 668677703
    0xa0507050912151609030f080c1203010e0f0403140a09090c1106010f0b03040816021c050d0c08160501020c010e031c14070302030910061511070806060409 68
    0x944070804151a090641401450340d164220402c50044070001d040d0b1000141308611000d0709a401140c03c0e0407203422010058080f44a0704140d0701034032819000c0c1c002e9101c2e922a8003a0990142c0c003840c100c40021a02c6041d41c5e5078600507a090141c200c1300200081c0090241c200c00704144809000b04400c2403600c00034064450038064205e462144c02500498110780b1000410182000000d0143c22803618090700d032490500340025600015200910003d00411203c044150801c00c100105400424895909aa020300300340c43c000c00c00d005644ca4002d031454110010b000d01e504d24800c0d94030110a0b8034090401c02c070896861500c040880e501c2d5020042080c03d60b1013401003208030048178000c0c6036104d03001d880e2640d03441075141003020341740c0c20300306120203c9007002d0740c1c60b03401a0305080260b075aa590b091001d0400300381a4140107031b507141000200d56104a03050514540c8019101ca01c2c12035805d074130345039403100d90b03106007010340c0d11040009105040a070400000640304010b10f4003e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 668680179 1250 668678929 668678947
    0x150e0c030a03020105240a06030e030f032a03060901050432070e0a03080409020a0c060c1d0a1406070c030c23060a021005060616080912060705030a050705 68
    0x6105081c802600140e441c0c03400d102140f40e0902d005161501c0d081011929001110040b801d8414144030720018035a13559015028140140101c81005d82c0c811601980d0b4a0000f0384000d001400b882010803040d080180d142d80342d908081240c0c013460008106034a00c1e07182c582080050000ca143e4010440c01076045c078041440302c00c00007d081440190f04440a103410103006219203210b41c8031030b01c101d0440c481000440e850303104407020389030a0500903030382c2d05010500f6901e481c1a02c4c00113080c01c3c54101c01d000210352290780840b001800504042c0d01400d503000308000498180140c1c80e0000650044803c0c5103460001019094860195175818654030307211603169540560151403065441580c100210408001051703e5130000c8400750f0400f8075005009540340c4082440540300d80d6074030042240d65070b500b001d4800240100c0c010420080003031510b041513400c0981210300451807504501d0000308040f41c0580f09400759502d490640d960b00b1245c10140034050400814810200070002c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 668681429 1250 668680179 668680183
    0x1e04052503060516050f0c0a30050c0706030f0f02031611120d05040c030b090c0a050405010e04030c1b0f05030607080c2d0301030c21150e0c03 63
    0x30020903584040d215292035400e009040e500d008281601e0302c0355044d00f55050329001800e40c0c024a4070100318a07205c3d10f124203020f181003190300c400740904401a030995401c0c4415030130844690400c00d42c4d401d20f085d00c50070980c1c00d070245561010701c40d0801441444040c1c0719034480c4034448081a03022074400c034401c03d16422030b40240c40f008294201d4048080e11960426a1499142d0800f00106040c07840441041322a004a66000d8402910751001c181882401c02c5018051900400d1002c80b9007490480f0380d6880d10003510340d50245035180400101840c1902c285412075660145c40a290790302d9907421150340c219600100c1c0c0700c0c00c0c1030407000e0100342c06c0d407911006084003290f05d070740300c030306020405180000080903801001908000c2200010302c0d5000e03108002c4030f0510958110b66041003905c031004400082c060030503408400003040c41524180300045401e5000c8012924a054801d6260f00c1420b40001c1e20000389182d003002c100d40107511003003100b40d14030151500a440ca4000038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 668682679 1250 668681429 668681473
    0x61419050433050a080d1e0e040c0302091c050a240f020a030e0c030d0e01030608010f050711030a080606031e040f02190602071a09061902070504051e0405 68
    0xe140801c0d640521513420030383e0a02c2c01034034101004014038004c1203001411492486484213040201094010655000340b08460b4040030092007448221001e0900034002d402003640f1505c103a07080d5500c1407001130381a086204194208014180104042e1240115040207810918154000300c8800910744034038071807034104400200c0302580c0d80c1c0400c040141134994404451485801c010200c030b1141c2c0d00004c1030001507826082072042c030050b031030068008165903072100c2c12550800700e0844090301c09030301640c459251a290800c0051022581c0c568038024160742c00d01040303141e40864a42c1c81c1450246521500d0900074034a01c10078044820300403d0300703079001c980c1c2700800100360045240c050411040c0fa400c40010403081460701400a6841501e4441c041550510361071311220300ca4142d0803a04a000c010300b0700741d40c640e04010000003610480500d10014042c2410108051a00c1d000b4180a950144045181d800501c0a0f0818074100584211840e118050000b01d10b40050140b074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 668683929 1250 668682679 668682761
    0x40b13051c02010b040501051c03030e0313030b1806010b03310c050402130b0714010e030301080105010e1621050a06090b0604030201021218130614190504 68
    0x49020065a94070103400c1d07488404400d03125038200801840140c44000b090041c490b070a901c8103014401a041c02d90042ca80142d0a031424040025080301c040305001c81481103030301c0356890849aa54160150118421112a18506030428801080300e04150350155810020034500c84d192040129072010036821002c07003242ca507500c0d088482062003c040314a1004110540302036140420640526034000c810780202500000701007140c2c401d1200900c614464010302c0720003000b0100300f050f00195079030400d00c1500405d43c02d02c0004101c0c608031540c480c2c01000c0c6040e8446002400300402d5810030914007a440701e113918008450b054900a000311801821b4516000454904005c2444161544000700c5030164104000030401030b640090302c540041078074004980c030340d071224007041211004c4002c00c540c080c0412a1079814810690301403800c13503d291855591803003000040c0400040d0b20041c40710010340d440b10030469404c0c240c0200750589070711044002c14104a80c00f19400740e400d0812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 668685179 1250 668683929 668683963
    0xc030216030b090c0a0e07050d0e01060e0118090308062205010609060f03060f3005011b08090706030510080a0f1106040e01140a2606130308040b1305 66
    0x82c080a00001c2c0704d84030792604141c03028054035040000811a40501504550030058001400510940c007503000e61201c04000000740007140c4d0743c002c4420030742c50a0049450300221030502c00e44240392880f45c03401081e410388958100e650350008110907140c5501c4003c03c21000382d103080c3d60004040c81201d010f00515101e100103141040b9005014100500807a0103140c60101e007403048860891b001800c9440c003004540000003045414000584d0366003603d0f142c601c8202e4082c0801c14107400c802e00c0078030841003213603813240d400308121941503068074903d8441d000048148041442a045141d03c000b05080e402c40351943e5020a40c40d02c0340c2c00740c050303410b000801e4080c01005a4003901040030241141d031541024104400300f000004103124501d160842c6105060581c2ca0300c0703102e00010542484041d900b124900c1c6000321007040e00e20500054011302c0c0000b00b6009003244800d1040d60182c0e0b9048056840d41e44109070200080c21400404840d034106100056041100440204800e80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 668686429 1250 668685179 668685181
    0x1d062101060309050714030313030c140f01080601110c1008100f05100f0e1005120a0c050a050c010608030304050d020c0303160b130b0109090212010507050306010c030216030b 77
    0x4058205041e00030310300705810a03c0201c0410b000082c46003c0e0b0368000031500e038200012002914601c50840c03d02901c40b40c0c80c8000081c06460b210b95030072904c07201b080c0f021100c3c44104028240300c5040d00540803d10560100d4069407142d2442d0a0369900c100480e6500f41014000412814024812b13400141400e4104920380c080c2c0e0304000f00404241000c00702c16400d00000581c01c488201804081051486040c2d00652048214a400c140702a03c803100f18240905c00074190f1388048403005243d204840401c5c103420140c4542104210346035a403a0800c0c600c00f000300c42c0d6501c8907005c04515034a480000c00c1d0071806000950142d84124000c2558104428001c0e0a1660070207a061103a0000d02c4194100c0210008005a040d4014551402544e4903501105003c401d01e00140061a246001080343c26260741f01200a0740212000040072400b9038529085c0c1e03a044541600140007480030070005d50041c0e039115682c2d07109005550405042c081122030011880d4000d56030580c40b04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 668687679 1250 668686429 668686477
    0x303151e0305190b010302060a09091802031506010203090f19090e0f060105030d140c010510050f1c0b060d1407061403070f05090303090d060b0411191d06 68
    0x102c0d03d481c8145251808141602548405400f20b40500c0081d008a2001901c02087c6105c0c414080160040c400c0401ca001b2982660803c08140c10340200e0103071041d042d0780c0e0304922020144034411501640190f1a00d0954800e00005020340044160089410710250043e14041c400c000301070600c066000400c0d00100c1243e07494000d00d5955075600f5001880140701c03c0d240481ca54101140ca4100180f17802c1c03040c512a04c01b40304580c071881c07403035190005009134800182c501008445080715070102600448080050001149045000c4c2401e914106000030f41d0543c030b0b0715481000248a0402011281c9520902c061010404d0a5540010341d06100c0030360404180840c0426445e0b00c64150b241444d00980109080e10a84040c440085031040c0580c0d81041102c08580000d00030301d0031051103103852405418103e1126100c0d900f8400180c0c0c003103445c14161487c0a0031030208030440001601c055406c2610a400400303802c003094100741041c0c4498000b401100f20035001101028031030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 668688929 1250 668687679 668687683
    0x2090f040c2301050315100e01020706030c081302010201090206070f0204050a021c1505032a0103090f0f02040207080c030a030b1e012a0332070303151e0305 69
    0x10350007111500c2c688094002c54144502101e10030501c0a0820300d6881e01c1e82c081c00b0240560202031b00b5070003100780d030000c03421640c0846810b40c184c07400e8084981d8240c880e40241e0980c1c13000c804150000380400005410407220003007050784580180000070344186079070041606030388804020303680d480d100d006203411400c0c04d11615610004400c01182880785202484400ca00340540c1340c5401500d4100c500c00a20070742803e40000c00c0d0040c00c6039080d40d005c09425501c510050481ca40007034003c050601c6e6035001e0b0085828203548250289542d0f40903950b0701c100c4103803001099030003950a007c102c0010b010b030002000d440350711500079a1201241c02c4000c0543d424010310034000c2ea0080301034001ca401e00042c11240045c242050060317440501082c83c11152118001c0c0b50081c0320b090105c0c1490b80014140d5503101030107403401c2032011104201c7d00550002d1011100c0254200224404a48268040341840a0018608105c05e03903030900c41d420070201441c205200008600200200101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 668690179 1250 668688929 668688953
    0x9041a010e191b0804021f02010c110a0b010501110f0304120b09011e02070f020d0303150e041505150310231b21090607120504051c0302040302090f04 66
    0x800c100c03d020740a6003040d10098420888000c50600c41d921000c2811075580361410102c2d007440d50015001c0424450303001340a08007d5400c00080340864444100800c40800c1d904400e0350008582d910503443c000044036410a0700f80407005038055250107000890040c0001e00051000c003804405c842000d003070442c144200580313051503680c0f405400c800e01c2d0020300030308200384100f000c0041e180c1c1014104009010395150009602100030307480341741010703015404100d0828210038840000c0703031a2941115203440070389028080c10085001d65542e0b40840d00542e80c0104d80911600e0000344034400700e4689a004050070b01900d031108000c04101401c80c011101c0082801d5164280741452694000c120160840802002c8000074505030030691465840030400344441006810745450350b48191039400c03d42d02c1d000040d0303030000c0c01c003001c08460150318040d0790014050324103d083c040c400420404a6042401415000d20000000d07030740e0711500600c40d8a440000c00198074007071402c0303109041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 668691429 1250 668690179 668690221
    0x90615180403092606191517120a14090a0b030f0f09030f04090b010522030501060b0702010f0f1107060203040504060902190302072d020415080c09041a010e 69
    0x400c1341c400e040c3d401000800b41d401000c42c0040c004001210711004000e071900d034442d140c140e11b5500000803444542c059944511206400f0380d541181d20000034909442510a90382c00910183d003400b000c41060001400a02c2c00204001451035540500380c585410448400c955a2004010400c2c80d90000c00b80781c1d400104000514039120059005c2c3e10f0381d00550140b07201c510358841000c1600d90060003194400128880301c420060410220909400020b0000301c49550034400c3c0092000000400e40d442c8a13030503154007a1b0242c0c11001203c1520b42c4010943c00c0010300e2052810b100401d003c031101411556024590742c03401c1070180801d58107942d02100da510310411540700102c6c40444640a804903901c4c026035104594242481241443c0200d030018a080c0309006c01c000d035418081b0781c0021700c02e80c1c05000140d8240c0368201001d0b694401c0218541007508000c4940c506480403079803244c81241515004580c5488010003071100360030030359006035510140510000305400810400e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 668692679 1250 668691429 668691479
    0x2070b010801151a0f0c0a0c0608060f040c27030303050903041208030a020405060f1206090108060106110102070c42030b04200a1709061518040309 65
    0x701000ba09625200b4251260903c007a081043c503130422815942266054003004400325116040300c007016440300d03609001181c59404451000654600610340644102c4005050b60440c9400d501880080c1800319140020000c08031240c2d46d01d203c41a800c0c0a0203e5241c000011050071803802030300300c0d01d018021401d00d504c1444108490303000c0c918000c070119445600703d42c980d2640b000300c0001e4052500110b45c88000490b00d100e903140110050502850344046003065034440c2400d20110319028028038803140c220f0303401880b9281c09211031b074640078901d00005291104945420b031200300c05400000c010844c0448140d9000400d061411041c4000b11100c90803100e132040e155140180d86003090306050325110300a02d20381d250752104116054102c100a02813204c17140da00c4445c1e100304a500c01040c4040401030740b030f80c9492040b0f4411f10b020b4005103030030b4a0f040e02403944803010400d481d5004021105c3d0080031811844428003031880390b1184a1528185150741480c4048203031540654 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 668693929 1250 668692679 668692691
    0x30a02210901030c030207020a0e2a032212170a020a0c02061c0204030503070210020d0215060105211909050304030f1b0e241e041b020c040c0e15030a0f06060302070b010801 76
    0x104840c001103981000e1095040030340c100c00d03818071480c040a04dc1c000b034660049035104440d200e401c1829485002d485c1460242c0b5941c44421450407802041d442c400003a0055079450014145040140960507071103072131414041c400e1504900f40ea0241e0011104d035000030650104505000c0201c07081c2c100d8600180040c2003141a00070f54803d40780042c0f020104003040840c8281e40203004985041e400c03c90a5013080b1400c5002c000c02d83d50a459140b0020f407080703084084180c01d4800c070900c0d640d121000d98603091a60f155804410642c0704292441414000c9510203020040503c100a1614101c007884900c2c22929000641150550340d0503500103584a040e5266034101040075207101400c2c9109a99650300040f42c0242524412001c58060b00c0030001081a0001502080b4020444050000c401d03031031402c540611400400640100080781003071600315418014551181860b0400110f680d803582204013a01c8095114002081d40000c81d2000d00003031032840390150400314028410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 668695179 1250 668693929 668694001
    0x9070806090a020a0c020d0318060f02100e070803041706010e13142a091b090d080c070e040b10050a050103020703020a0f05030a02210901030c030207020a0e 69
    0x600710010826160690300054100710180a065000030158028094803d61412850041c10604031086610b442d40c4d1607910009400c0e00c030b808000358942c070580c0540101149001d1120180429209203807984c0030325900801c002c1c00c1007002d4801011084000b03a20140f0000d065402d05d00103030850003840680c0010000319060303800c0e030300c801107074040210610804840792450078411440b4840d030f45002454030500011041022480046004036441055030301d5004e56aa5207540400e4842d64410f82400300c0d022925007025039500c9940202115480c02d40d02d1092542000f0b10758100803078482034041800240400c98040c50ba00007900040f180c80c103410f00001070603070a2644161410141c0024000c1d08062082c05500c1f081c41e07004040074086200ca1801503203a40107403124900600c0f40c0d010081c11038000c0d480e55444040031880342898901d00c01c004402a010b0700720400103064007000458014ac4861100100600c5910858601ca0a040500c080403031a5446220031a0610001c0c0c900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 668696429 1250 668695179 668695189
    0x15021207020616020405090c0f091009051e01060302042111040f09050609030705010e0714360601030b06040303090b130b0c0d02150c030f180d050909070806 69
    0x11140c0440308682c40b00030340040203100d443d00039402500b0609110030310040040c0011801d01e4801c08480c2d09512040800900440074012214800c00280d031a004100e00340e2183e102e617420000101e641d005010002c0400150b500080e0b100300c0000e039000404203c45040c0c400c80001c02c88041010b032107031040680b02c0c81c1c0c00c02e0309450002d11550392003190103446032131980444002607100c8291003040c82e013124056103c0e0000d98081d2400e50034403d00f8401698049503810540c2d480401518810349680240302c43c4081a455588001c11099000b05240b200b685c807400d035004c1e40c00e01e802072502e000c000040590700540f244902468040c00140002138004210000752842214180d0b203c01c840904442200307510303880304200b034000041071401000041a03818641d03019408442d2140142145218840011079030200c80c08818408a035000d0001c041558010326504030340c2000807140009141041401da1910010400006408a01d4245000d032964458041c1c20008020310749580491 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 668697679 1250 668696429 668696437
    0x3190908070f052101241e03050304090b22050402011e120f02070b04050601030c080304030b0f0601030e0105090c27070f030609060f090b040903050a050d091209150212 74
    0x5411200c084a0150710300d402580141c2401611011a0a4041d8821440300c1c281b1142d0085c1c6801200700c184407110380b036122221000702c2c3d5103c0e000354900f40c542b248142c010001760707081c80d60240800200c0a00030940c40700c030a494100050000403a401e0910025040c144410501c0880300805000480301a070009800700a4031440800401c2c002090040d250080c0b1400350024905a41d2200348070a1002c00503849050303911500d070a6205a07140e00d26075542e1b026900c8028480c0c0000c0d40000d51a1104004180e0011418103000c07444075441e148190035620120f50140d031039400320f00341d81030a251191030440c02400c24130039242e04040c65150424280d1004240c00c01307001c005564001c401e482540650000d141e120030802050392101c0021030030801512543c01d14600700000e0a2003440c046c032541c6c05c019850703100d036440c0002110040c2d485400004000f4a117665603000c100101d511904154410f082a6452810f42070501d20314401d10f4400002c03d0086620a950215120301800b04039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 668698929 1250 668697679 668697709
    0x5060405040b0a0905100903030e0f031e09041416030b06163816050c0615030307020303160c1203090608150d030f020d0203090a0b0c03190908070f05 66
    0x884c280c00e050138081d00d0a035091010f0407549242800742001e05034584d00c4103010345444425601800a000555552409944421000b4501c010f1003074182c85113500040103c040081c1c00401c07000306490201c61622030445007000071840803006511030703a500d0303ca1079030307418011a00a400e12a4070200055120007140005051490004000140358180c030b80704c0d043c16803078151486074105003013a9141000c009403210380c003003040c040e400d08425028109039025009802c0042c1003681c0d4156800300100080f244c1c1315090300082229201685040c001010f001c3c51084842209510301d260034070a800b0180c1c80060b600c5c104440c0c101c001399019007000212111882c0a10203900d50800c0c0194801d81600d0195129450080c4003041507040140305080b5441d43c3c003501ea4261501009a80702d116280800d030348440d100105004022004024100261681040f2820b00c0002600c1304095000008a080454600c1c0020085241d00f04000d102500ca0030703508601c01440c1001064101c1c0b03c508079 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 668700179 1250 668698929 668698931
    0x30a0b010c0b04120206010626060112090b18030421031205040f15060810150b040b03010905070318080318160603060503010510031b05130c0305060405040b0a 70
    0x4100260310601d00c060103a60030541100701c0b42824a0002100c5124200040142c05800000200c0500901d5020003450403082d001c0341c40e81c0481000c17420704000901c5141485900f07141441c59200f280f00300d141e524422414030b041404c0581901600b9001003601c407480d0f50041000b403081a81130090036008024000310034a424056140644075450201001e03490302c2d2811081100b80020341e00c4026809000340c500b079510398146510710f8241ca03d81c0c0a02c0e02a0744c802d0107054416010796000110344807081c060107101c9500c80c0254003041c0e000d035101c105403d0010005114166085c4512504120a410b0400014813444800341d1003810002024028003000f20001d5000710305002200e40c5246400142d56240f080c8400304442007665000c2c000001c5d103030940201d40b90070141314460180b6014501444110720b580d5540e542030039160a2640d050210b41800103003a00c84c80389102c1624140c440221702c168980800404562005004030700c607070705050a020100c0c1c05407527101e07006517001c10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 668701429 1250 668700179 668700191
    0x21605012f01020304080318060708190e2e020301030b01140303130905190e0a29070306050907230a030905060c0408060601021c051c0e060f0601050f030a 68
    0x71030700e0680e40707503400341c0c560550000003007004120300080203500c02c031078802200c440700c090109034036a00e0070101c4141e004100d0300c502080d00c85032010b0101060b000012000f0409100380e003a001d04003594a41d1080740d205207010395151100040f580d40c1ca040d5280c0c4001c504640c516211003d41070018800d5280a410b904201b00d142d0b1010300407204050048490f00e40c64954582040000380012189084001540c02c0e4042041c2c2072070040140401c9400e0040c811030740b1a4035070340f28405490030080381805000804003003c04400c6100d034403840651710b00156062030030301400150800240b0610810410a0706800c800300c200700501c0d41e0000d00751000b0744030950240103074020a29514040c100d40700c0c150420022843c103d0081c01543c0c00300c1c1c1034403000d440d610016652005200b401c03042180a182c12285018440c3d0050f03c1c40c02040d40400c080d1603000c00e1190200c608240d007070340040e08040100b00611100156081c0c1020080c40c207649466243d216001c001e02000c1c2449d518942c55031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 668702679 1250 668701429 668701487
    0xa150f0309210206042003060a0c0c021903020420070f0303020405060d020702190e0c030919030f0905030c010e010315031a01080d030506010504091d030c070602160501 74
    0x1c0e290220201c0c48802c0340c80360038154081d50300c3c1c80031141180d0300810784003030494044c0c516640003100075010f4000c1c086520380d198040301800c05800d20004010b0880c905102580d100401426441c250714209032419040d80140415544d00822480349102d2101000c04e43c8a041012154990b80203000401503048500d0124040c0c852684040d502c0390700402d41d01c9040626600408125100302c17044082c2d00c24468000f142441c5c0751003045100341211002405010559004590240d41041580e0361292503101d215030640721003000b0707800140d06260034030f0069081400e2134081c100803402462022100070008054000b154403042c10191a111850441070700a10074501031035105060304000c0006c1d80c40003440040c2441203420610900094450050113441142d00524060351080d2400c1d041c80500005484100380084c58241c142c2055804044144080d000400102015140040c902180285011744240901da00c0d002c010008110503030700114545029882900004030880307040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 668703929 1250 668702679 668702693
    0x23030601090902030703020d060e061513120b06190f0521030a0513090504150902060705011a04150f090507050c12120c0702102102070b01050a150f0309 67
    0x141d0005080b50300200510414503010740207003204907050ba20070001ea0355950090b185001094035000c4e0004860400c030340e031a090b0040284451000010f0003000300780d541e61001541014024195801400b41040c441240341070f01c904010740041e284860030b441c3c2061098180450103209040c40381d52000c284111170321107080c040040054101c25070b034982d60184805051940b15030001c020340843c004c404501740446109a80c000c64200205c0d00c440e4013649225401040031000a03a4000024000e0b05c00142003402458502c9075160503010900d0a2503043c44169148114149590701950000b40a2480340d442c02c0021078040010114007a12400740c01d807018450740c01401c115010b000190110400868018201061107291b032301c01e1660340c408900440d0041071030007540030b40c140e0b4810030120320030707004503030307034442880c0d1710b1500c1d4460042d0f540482e8810743c8103d80c04407080004000750300e442c40180000703184588002001c2150040020309510461014906040e90303180020140816 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 668705035 1106 668703929 668703947
    0x705030108060c0d0209090a0e07120308060927010603030228020d03180905060f06132108031503010c050f0f1b01110a0e0123030601 59
    0x95040c0c43d084642c85203a01e0000315409010701041d940e910705840e405000c4d8020300203021542c1c180b4036402c3c11076a80c814032142c401d08001c0000310f42c001220640c403a00468011145036540500c5c00450003607040ca81421f003a038100c540e0300030801584a082034034081d4084462401002540b00321110141403100d140c2c50111078240010704001607540080c0f03100b403c03e045a415000f40210110300c26074020055551500c007440b4044c02d1510840d00e1624080c0c5040d850a80b516140942058962080401c90b0720780c40c003800740c0b10209910040c0f00d40d50103043c8a0703032820179084026051050b441e02c0c2e4804c0d440d2000c17908450b4040c204880ca051001d00d091810007010003050495600128203400c190f420340780940816007001e1007099541190341040a842c0c100c02080180041d146a01507810b014800c96881045071607020110000c1800141e4940e0380e41da004012218410 = true := by decide +kernel

theorem cover : BRFrame.Cov 668525179 668705035 := by
  have h0 := BRFrame.cov_init 668525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 668525179 ≤ n) (h2 : n < 668705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
